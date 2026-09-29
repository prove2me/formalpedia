-- Prove2me | solution 1 for syracuse_descends_range_119786_123786
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:31.960088+00:00
-- url     : https://prove2.me/submissions/2ea0d482-0bee-4df0-87f9-2fcf839cb0f9

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


theorem B262253 : Blo 119786 262253 := bbase (se 3 (by rfl) ⟨49172, by rfl⟩ : syracuseStep 262253 = 98345) (by norm_num)
theorem B196805 : Blo 119786 196805 := bbase (se 4 (by rfl) ⟨18450, by rfl⟩ : syracuseStep 196805 = 36901) (by norm_num)
theorem B196933 : Blo 119786 196933 := bbase (se 4 (by rfl) ⟨18462, by rfl⟩ : syracuseStep 196933 = 36925) (by norm_num)
theorem B164173 : Blo 119786 164173 := bbase (se 3 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 164173 = 61565) (by norm_num)
theorem B131425 : Blo 119786 131425 := bbase (se 2 (by rfl) ⟨49284, by rfl⟩ : syracuseStep 131425 = 98569) (by norm_num)
theorem B196997 : Blo 119786 196997 := bbase (se 4 (by rfl) ⟨18468, by rfl⟩ : syracuseStep 196997 = 36937) (by norm_num)
theorem B131545 : Blo 119786 131545 := bbase (se 2 (by rfl) ⟨49329, by rfl⟩ : syracuseStep 131545 = 98659) (by norm_num)
theorem B230053 : Blo 119786 230053 := bbase (se 4 (by rfl) ⟨21567, by rfl⟩ : syracuseStep 230053 = 43135) (by norm_num)
theorem B393893 : Blo 119786 393893 := bbase (se 4 (by rfl) ⟨36927, by rfl⟩ : syracuseStep 393893 = 73855) (by norm_num)
theorem B131797 : Blo 119786 131797 := bbase (se 7 (by rfl) ⟨1544, by rfl⟩ : syracuseStep 131797 = 3089) (by norm_num)
theorem B131801 : Blo 119786 131801 := bbase (se 2 (by rfl) ⟨49425, by rfl⟩ : syracuseStep 131801 = 98851) (by norm_num)
theorem B262885 : Blo 119786 262885 := bbase (se 4 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 262885 = 49291) (by norm_num)
theorem B262909 : Blo 119786 262909 := bbase (se 3 (by rfl) ⟨49295, by rfl⟩ : syracuseStep 262909 = 98591) (by norm_num)
theorem B230197 : Blo 119786 230197 := bbase (se 5 (by rfl) ⟨10790, by rfl⟩ : syracuseStep 230197 = 21581) (by norm_num)
theorem B590645 : Blo 119786 590645 := bbase (se 5 (by rfl) ⟨27686, by rfl⟩ : syracuseStep 590645 = 55373) (by norm_num)
theorem B132025 : Blo 119786 132025 := bbase (se 2 (by rfl) ⟨49509, by rfl⟩ : syracuseStep 132025 = 99019) (by norm_num)
theorem B230357 : Blo 119786 230357 := bbase (se 7 (by rfl) ⟨2699, by rfl⟩ : syracuseStep 230357 = 5399) (by norm_num)
theorem B132193 : Blo 119786 132193 := bbase (se 2 (by rfl) ⟨49572, by rfl⟩ : syracuseStep 132193 = 99145) (by norm_num)
theorem B459877 : Blo 119786 459877 := bbase (se 4 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 459877 = 86227) (by norm_num)
theorem B230501 : Blo 119786 230501 := bbase (se 4 (by rfl) ⟨21609, by rfl⟩ : syracuseStep 230501 = 43219) (by norm_num)
theorem B689269 : Blo 119786 689269 := bbase (se 5 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 689269 = 64619) (by norm_num)
theorem B885941 : Blo 119786 885941 := bbase (se 5 (by rfl) ⟨41528, by rfl⟩ : syracuseStep 885941 = 83057) (by norm_num)
theorem B623861 : Blo 119786 623861 := bbase (se 5 (by rfl) ⟨29243, by rfl⟩ : syracuseStep 623861 = 58487) (by norm_num)
theorem B296237 : Blo 119786 296237 := bbase (se 3 (by rfl) ⟨55544, by rfl⟩ : syracuseStep 296237 = 111089) (by norm_num)
theorem B296245 : Blo 119786 296245 := bbase (se 5 (by rfl) ⟨13886, by rfl⟩ : syracuseStep 296245 = 27773) (by norm_num)
theorem B230789 : Blo 119786 230789 := bbase (se 4 (by rfl) ⟨21636, by rfl⟩ : syracuseStep 230789 = 43273) (by norm_num)
theorem B460181 : Blo 119786 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B165341 : Blo 119786 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B230941 : Blo 119786 230941 := bbase (se 3 (by rfl) ⟨43301, by rfl⟩ : syracuseStep 230941 = 86603) (by norm_num)
theorem B263773 : Blo 119786 263773 := bbase (se 3 (by rfl) ⟨49457, by rfl⟩ : syracuseStep 263773 = 98915) (by norm_num)
theorem B362165 : Blo 119786 362165 := bbase (se 5 (by rfl) ⟨16976, by rfl⟩ : syracuseStep 362165 = 33953) (by norm_num)
theorem B263893 : Blo 119786 263893 := bbase (se 7 (by rfl) ⟨3092, by rfl⟩ : syracuseStep 263893 = 6185) (by norm_num)
theorem B231245 : Blo 119786 231245 := bbase (se 3 (by rfl) ⟨43358, by rfl⟩ : syracuseStep 231245 = 86717) (by norm_num)
theorem B755669 : Blo 119786 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B264149 : Blo 119786 264149 := bbase (se 7 (by rfl) ⟨3095, by rfl⟩ : syracuseStep 264149 = 6191) (by norm_num)
theorem B592069 : Blo 119786 592069 := bbase (se 4 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 592069 = 111013) (by norm_num)
theorem B592085 : Blo 119786 592085 := bbase (se 7 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 592085 = 13877) (by norm_num)
theorem B166141 : Blo 119786 166141 := bbase (se 3 (by rfl) ⟨31151, by rfl⟩ : syracuseStep 166141 = 62303) (by norm_num)
theorem B297245 : Blo 119786 297245 := bbase (se 3 (by rfl) ⟨55733, by rfl⟩ : syracuseStep 297245 = 111467) (by norm_num)
theorem B625157 : Blo 119786 625157 := bbase (se 4 (by rfl) ⟨58608, by rfl⟩ : syracuseStep 625157 = 117217) (by norm_num)
theorem B395813 : Blo 119786 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B231997 : Blo 119786 231997 := bbase (se 3 (by rfl) ⟨43499, by rfl⟩ : syracuseStep 231997 = 86999) (by norm_num)
theorem B133817 : Blo 119786 133817 := bbase (se 2 (by rfl) ⟨50181, by rfl⟩ : syracuseStep 133817 = 100363) (by norm_num)
theorem B559813 : Blo 119786 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B232141 : Blo 119786 232141 := bbase (se 3 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 232141 = 87053) (by norm_num)
theorem B232301 : Blo 119786 232301 := bbase (se 3 (by rfl) ⟨43556, by rfl⟩ : syracuseStep 232301 = 87113) (by norm_num)
theorem B330725 : Blo 119786 330725 := bbase (se 4 (by rfl) ⟨31005, by rfl⟩ : syracuseStep 330725 = 62011) (by norm_num)
theorem B658421 : Blo 119786 658421 := bbase (se 5 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 658421 = 61727) (by norm_num)
theorem B232445 : Blo 119786 232445 := bbase (se 3 (by rfl) ⟨43583, by rfl⟩ : syracuseStep 232445 = 87167) (by norm_num)
theorem B691253 : Blo 119786 691253 := bbase (se 5 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 691253 = 64805) (by norm_num)
theorem B593173 : Blo 119786 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B232733 : Blo 119786 232733 := bbase (se 3 (by rfl) ⟨43637, by rfl⟩ : syracuseStep 232733 = 87275) (by norm_num)
theorem B232885 : Blo 119786 232885 := bbase (se 5 (by rfl) ⟨10916, by rfl⟩ : syracuseStep 232885 = 21833) (by norm_num)
theorem B462293 : Blo 119786 462293 := bbase (se 7 (by rfl) ⟨5417, by rfl⟩ : syracuseStep 462293 = 10835) (by norm_num)
theorem B527957 : Blo 119786 527957 := bbase (se 8 (by rfl) ⟨3093, by rfl⟩ : syracuseStep 527957 = 6187) (by norm_num)
theorem B134761 : Blo 119786 134761 := bbase (se 2 (by rfl) ⟨50535, by rfl⟩ : syracuseStep 134761 = 101071) (by norm_num)
theorem B134797 : Blo 119786 134797 := bbase (se 3 (by rfl) ⟨25274, by rfl⟩ : syracuseStep 134797 = 50549) (by norm_num)
theorem B134833 : Blo 119786 134833 := bbase (se 2 (by rfl) ⟨50562, by rfl⟩ : syracuseStep 134833 = 101125) (by norm_num)
theorem B134869 : Blo 119786 134869 := bbase (se 7 (by rfl) ⟨1580, by rfl⟩ : syracuseStep 134869 = 3161) (by norm_num)
theorem B233189 : Blo 119786 233189 := bbase (se 4 (by rfl) ⟨21861, by rfl⟩ : syracuseStep 233189 = 43723) (by norm_num)
theorem B462581 : Blo 119786 462581 := bbase (se 5 (by rfl) ⟨21683, by rfl⟩ : syracuseStep 462581 = 43367) (by norm_num)
theorem B134905 : Blo 119786 134905 := bbase (se 2 (by rfl) ⟨50589, by rfl⟩ : syracuseStep 134905 = 101179) (by norm_num)
theorem B626453 : Blo 119786 626453 := bbase (se 6 (by rfl) ⟨14682, by rfl⟩ : syracuseStep 626453 = 29365) (by norm_num)
theorem B134941 : Blo 119786 134941 := bbase (se 3 (by rfl) ⟨25301, by rfl⟩ : syracuseStep 134941 = 50603) (by norm_num)
theorem B134977 : Blo 119786 134977 := bbase (se 2 (by rfl) ⟨50616, by rfl⟩ : syracuseStep 134977 = 101233) (by norm_num)
theorem B560981 : Blo 119786 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B135013 : Blo 119786 135013 := bbase (se 4 (by rfl) ⟨12657, by rfl⟩ : syracuseStep 135013 = 25315) (by norm_num)
theorem B135049 : Blo 119786 135049 := bbase (se 2 (by rfl) ⟨50643, by rfl⟩ : syracuseStep 135049 = 101287) (by norm_num)
theorem B135085 : Blo 119786 135085 := bbase (se 3 (by rfl) ⟨25328, by rfl⟩ : syracuseStep 135085 = 50657) (by norm_num)
theorem B135121 : Blo 119786 135121 := bbase (se 2 (by rfl) ⟨50670, by rfl⟩ : syracuseStep 135121 = 101341) (by norm_num)
theorem B135157 : Blo 119786 135157 := bbase (se 5 (by rfl) ⟨6335, by rfl⟩ : syracuseStep 135157 = 12671) (by norm_num)
theorem B135193 : Blo 119786 135193 := bbase (se 2 (by rfl) ⟨50697, by rfl⟩ : syracuseStep 135193 = 101395) (by norm_num)
theorem B135229 : Blo 119786 135229 := bbase (se 3 (by rfl) ⟨25355, by rfl⟩ : syracuseStep 135229 = 50711) (by norm_num)
theorem B135265 : Blo 119786 135265 := bbase (se 2 (by rfl) ⟨50724, by rfl⟩ : syracuseStep 135265 = 101449) (by norm_num)
theorem B135301 : Blo 119786 135301 := bbase (se 4 (by rfl) ⟨12684, by rfl⟩ : syracuseStep 135301 = 25369) (by norm_num)
theorem B135337 : Blo 119786 135337 := bbase (se 2 (by rfl) ⟨50751, by rfl⟩ : syracuseStep 135337 = 101503) (by norm_num)
theorem B135373 : Blo 119786 135373 := bbase (se 3 (by rfl) ⟨25382, by rfl⟩ : syracuseStep 135373 = 50765) (by norm_num)
theorem B135409 : Blo 119786 135409 := bbase (se 2 (by rfl) ⟨50778, by rfl⟩ : syracuseStep 135409 = 101557) (by norm_num)
theorem B135445 : Blo 119786 135445 := bbase (se 6 (by rfl) ⟨3174, by rfl⟩ : syracuseStep 135445 = 6349) (by norm_num)
theorem B135481 : Blo 119786 135481 := bbase (se 2 (by rfl) ⟨50805, by rfl⟩ : syracuseStep 135481 = 101611) (by norm_num)
theorem B921941 : Blo 119786 921941 := bbase (se 10 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 921941 = 2701) (by norm_num)
theorem B2003285 : Blo 119786 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B135517 : Blo 119786 135517 := bbase (se 3 (by rfl) ⟨25409, by rfl⟩ : syracuseStep 135517 = 50819) (by norm_num)
theorem B135553 : Blo 119786 135553 := bbase (se 2 (by rfl) ⟨50832, by rfl⟩ : syracuseStep 135553 = 101665) (by norm_num)
theorem B135589 : Blo 119786 135589 := bbase (se 4 (by rfl) ⟨12711, by rfl⟩ : syracuseStep 135589 = 25423) (by norm_num)
theorem B135625 : Blo 119786 135625 := bbase (se 2 (by rfl) ⟨50859, by rfl⟩ : syracuseStep 135625 = 101719) (by norm_num)
theorem B233941 : Blo 119786 233941 := bbase (se 7 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 233941 = 5483) (by norm_num)
theorem B135661 : Blo 119786 135661 := bbase (se 3 (by rfl) ⟨25436, by rfl⟩ : syracuseStep 135661 = 50873) (by norm_num)
theorem B135697 : Blo 119786 135697 := bbase (se 2 (by rfl) ⟨50886, by rfl⟩ : syracuseStep 135697 = 101773) (by norm_num)
theorem B135733 : Blo 119786 135733 := bbase (se 5 (by rfl) ⟨6362, by rfl⟩ : syracuseStep 135733 = 12725) (by norm_num)
theorem B135769 : Blo 119786 135769 := bbase (se 2 (by rfl) ⟨50913, by rfl⟩ : syracuseStep 135769 = 101827) (by norm_num)
theorem B234085 : Blo 119786 234085 := bbase (se 4 (by rfl) ⟨21945, by rfl⟩ : syracuseStep 234085 = 43891) (by norm_num)
theorem B135805 : Blo 119786 135805 := bbase (se 3 (by rfl) ⟨25463, by rfl⟩ : syracuseStep 135805 = 50927) (by norm_num)
theorem B135841 : Blo 119786 135841 := bbase (se 2 (by rfl) ⟨50940, by rfl⟩ : syracuseStep 135841 = 101881) (by norm_num)
theorem B135877 : Blo 119786 135877 := bbase (se 4 (by rfl) ⟨12738, by rfl⟩ : syracuseStep 135877 = 25477) (by norm_num)
theorem B135913 : Blo 119786 135913 := bbase (se 2 (by rfl) ⟨50967, by rfl⟩ : syracuseStep 135913 = 101935) (by norm_num)
theorem B234245 : Blo 119786 234245 := bbase (se 4 (by rfl) ⟨21960, by rfl⟩ : syracuseStep 234245 = 43921) (by norm_num)
theorem B135949 : Blo 119786 135949 := bbase (se 3 (by rfl) ⟨25490, by rfl⟩ : syracuseStep 135949 = 50981) (by norm_num)
theorem B1151765 : Blo 119786 1151765 := bbase (se 6 (by rfl) ⟨26994, by rfl⟩ : syracuseStep 1151765 = 53989) (by norm_num)
theorem B135985 : Blo 119786 135985 := bbase (se 2 (by rfl) ⟨50994, by rfl⟩ : syracuseStep 135985 = 101989) (by norm_num)
theorem B136021 : Blo 119786 136021 := bbase (se 9 (by rfl) ⟨398, by rfl⟩ : syracuseStep 136021 = 797) (by norm_num)
theorem B136057 : Blo 119786 136057 := bbase (se 2 (by rfl) ⟨51021, by rfl⟩ : syracuseStep 136057 = 102043) (by norm_num)
theorem B463765 : Blo 119786 463765 := bbase (se 6 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 463765 = 21739) (by norm_num)
theorem B234389 : Blo 119786 234389 := bbase (se 6 (by rfl) ⟨5493, by rfl⟩ : syracuseStep 234389 = 10987) (by norm_num)
theorem B136093 : Blo 119786 136093 := bbase (se 3 (by rfl) ⟨25517, by rfl⟩ : syracuseStep 136093 = 51035) (by norm_num)
theorem B136129 : Blo 119786 136129 := bbase (se 2 (by rfl) ⟨51048, by rfl⟩ : syracuseStep 136129 = 102097) (by norm_num)
theorem B136165 : Blo 119786 136165 := bbase (se 4 (by rfl) ⟨12765, by rfl⟩ : syracuseStep 136165 = 25531) (by norm_num)
theorem B136201 : Blo 119786 136201 := bbase (se 2 (by rfl) ⟨51075, by rfl⟩ : syracuseStep 136201 = 102151) (by norm_num)
theorem B136237 : Blo 119786 136237 := bbase (se 3 (by rfl) ⟨25544, by rfl⟩ : syracuseStep 136237 = 51089) (by norm_num)
theorem B136273 : Blo 119786 136273 := bbase (se 2 (by rfl) ⟨51102, by rfl⟩ : syracuseStep 136273 = 102205) (by norm_num)
theorem B136309 : Blo 119786 136309 := bbase (se 5 (by rfl) ⟨6389, by rfl⟩ : syracuseStep 136309 = 12779) (by norm_num)
theorem B136345 : Blo 119786 136345 := bbase (se 2 (by rfl) ⟨51129, by rfl⟩ : syracuseStep 136345 = 102259) (by norm_num)
theorem B234677 : Blo 119786 234677 := bbase (se 5 (by rfl) ⟨11000, by rfl⟩ : syracuseStep 234677 = 22001) (by norm_num)
theorem B136381 : Blo 119786 136381 := bbase (se 3 (by rfl) ⟨25571, by rfl⟩ : syracuseStep 136381 = 51143) (by norm_num)
theorem B464069 : Blo 119786 464069 := bbase (se 4 (by rfl) ⟨43506, by rfl⟩ : syracuseStep 464069 = 87013) (by norm_num)
theorem B693461 : Blo 119786 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B136417 : Blo 119786 136417 := bbase (se 2 (by rfl) ⟨51156, by rfl⟩ : syracuseStep 136417 = 102313) (by norm_num)
theorem B627941 : Blo 119786 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B300269 : Blo 119786 300269 := bbase (se 3 (by rfl) ⟨56300, by rfl⟩ : syracuseStep 300269 = 112601) (by norm_num)
theorem B136453 : Blo 119786 136453 := bbase (se 4 (by rfl) ⟨12792, by rfl⟩ : syracuseStep 136453 = 25585) (by norm_num)
theorem B136489 : Blo 119786 136489 := bbase (se 2 (by rfl) ⟨51183, by rfl⟩ : syracuseStep 136489 = 102367) (by norm_num)
theorem B136525 : Blo 119786 136525 := bbase (se 3 (by rfl) ⟨25598, by rfl⟩ : syracuseStep 136525 = 51197) (by norm_num)
theorem B234829 : Blo 119786 234829 := bbase (se 3 (by rfl) ⟨44030, by rfl⟩ : syracuseStep 234829 = 88061) (by norm_num)
theorem B136561 : Blo 119786 136561 := bbase (se 2 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 136561 = 102421) (by norm_num)
theorem B136597 : Blo 119786 136597 := bbase (se 6 (by rfl) ⟨3201, by rfl⟩ : syracuseStep 136597 = 6403) (by norm_num)
theorem B136633 : Blo 119786 136633 := bbase (se 2 (by rfl) ⟨51237, by rfl⟩ : syracuseStep 136633 = 102475) (by norm_num)
theorem B202189 : Blo 119786 202189 := bbase (se 3 (by rfl) ⟨37910, by rfl⟩ : syracuseStep 202189 = 75821) (by norm_num)
theorem B136669 : Blo 119786 136669 := bbase (se 3 (by rfl) ⟨25625, by rfl⟩ : syracuseStep 136669 = 51251) (by norm_num)
theorem B136705 : Blo 119786 136705 := bbase (se 2 (by rfl) ⟨51264, by rfl⟩ : syracuseStep 136705 = 102529) (by norm_num)
theorem B202277 : Blo 119786 202277 := bbase (se 4 (by rfl) ⟨18963, by rfl⟩ : syracuseStep 202277 = 37927) (by norm_num)
theorem B136741 : Blo 119786 136741 := bbase (se 4 (by rfl) ⟨12819, by rfl⟩ : syracuseStep 136741 = 25639) (by norm_num)
theorem B136777 : Blo 119786 136777 := bbase (se 2 (by rfl) ⟨51291, by rfl⟩ : syracuseStep 136777 = 102583) (by norm_num)
theorem B136813 : Blo 119786 136813 := bbase (se 3 (by rfl) ⟨25652, by rfl⟩ : syracuseStep 136813 = 51305) (by norm_num)
theorem B136849 : Blo 119786 136849 := bbase (se 2 (by rfl) ⟨51318, by rfl⟩ : syracuseStep 136849 = 102637) (by norm_num)
theorem B202405 : Blo 119786 202405 := bbase (se 4 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 202405 = 37951) (by norm_num)
theorem B136885 : Blo 119786 136885 := bbase (se 5 (by rfl) ⟨6416, by rfl⟩ : syracuseStep 136885 = 12833) (by norm_num)
theorem B136921 : Blo 119786 136921 := bbase (se 2 (by rfl) ⟨51345, by rfl⟩ : syracuseStep 136921 = 102691) (by norm_num)
theorem B202493 : Blo 119786 202493 := bbase (se 3 (by rfl) ⟨37967, by rfl⟩ : syracuseStep 202493 = 75935) (by norm_num)
theorem B136957 : Blo 119786 136957 := bbase (se 3 (by rfl) ⟨25679, by rfl⟩ : syracuseStep 136957 = 51359) (by norm_num)
theorem B136993 : Blo 119786 136993 := bbase (se 2 (by rfl) ⟨51372, by rfl⟩ : syracuseStep 136993 = 102745) (by norm_num)
theorem B137029 : Blo 119786 137029 := bbase (se 4 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 137029 = 25693) (by norm_num)
theorem B137065 : Blo 119786 137065 := bbase (se 2 (by rfl) ⟨51399, by rfl⟩ : syracuseStep 137065 = 102799) (by norm_num)
theorem B202621 : Blo 119786 202621 := bbase (se 3 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 202621 = 75983) (by norm_num)
theorem B137101 : Blo 119786 137101 := bbase (se 3 (by rfl) ⟨25706, by rfl⟩ : syracuseStep 137101 = 51413) (by norm_num)
theorem B137137 : Blo 119786 137137 := bbase (se 2 (by rfl) ⟨51426, by rfl⟩ : syracuseStep 137137 = 102853) (by norm_num)
theorem B202709 : Blo 119786 202709 := bbase (se 7 (by rfl) ⟨2375, by rfl⟩ : syracuseStep 202709 = 4751) (by norm_num)
theorem B137173 : Blo 119786 137173 := bbase (se 7 (by rfl) ⟨1607, by rfl⟩ : syracuseStep 137173 = 3215) (by norm_num)
theorem B1185749 : Blo 119786 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B137209 : Blo 119786 137209 := bbase (se 2 (by rfl) ⟨51453, by rfl⟩ : syracuseStep 137209 = 102907) (by norm_num)
theorem B137245 : Blo 119786 137245 := bbase (se 3 (by rfl) ⟨25733, by rfl⟩ : syracuseStep 137245 = 51467) (by norm_num)
theorem B137281 : Blo 119786 137281 := bbase (se 2 (by rfl) ⟨51480, by rfl⟩ : syracuseStep 137281 = 102961) (by norm_num)
theorem B202837 : Blo 119786 202837 := bbase (se 8 (by rfl) ⟨1188, by rfl⟩ : syracuseStep 202837 = 2377) (by norm_num)
theorem B137317 : Blo 119786 137317 := bbase (se 4 (by rfl) ⟨12873, by rfl⟩ : syracuseStep 137317 = 25747) (by norm_num)
theorem B137353 : Blo 119786 137353 := bbase (se 2 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 137353 = 103015) (by norm_num)
theorem B202925 : Blo 119786 202925 := bbase (se 3 (by rfl) ⟨38048, by rfl⟩ : syracuseStep 202925 = 76097) (by norm_num)
theorem B137389 : Blo 119786 137389 := bbase (se 3 (by rfl) ⟨25760, by rfl⟩ : syracuseStep 137389 = 51521) (by norm_num)
theorem B137425 : Blo 119786 137425 := bbase (se 2 (by rfl) ⟨51534, by rfl⟩ : syracuseStep 137425 = 103069) (by norm_num)
theorem B432373 : Blo 119786 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B137461 : Blo 119786 137461 := bbase (se 5 (by rfl) ⟨6443, by rfl⟩ : syracuseStep 137461 = 12887) (by norm_num)
theorem B235781 : Blo 119786 235781 := bbase (se 4 (by rfl) ⟨22104, by rfl⟩ : syracuseStep 235781 = 44209) (by norm_num)
theorem B891157 : Blo 119786 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B137497 : Blo 119786 137497 := bbase (se 2 (by rfl) ⟨51561, by rfl⟩ : syracuseStep 137497 = 103123) (by norm_num)
theorem B203053 : Blo 119786 203053 := bbase (se 3 (by rfl) ⟨38072, by rfl⟩ : syracuseStep 203053 = 76145) (by norm_num)
theorem B137533 : Blo 119786 137533 := bbase (se 3 (by rfl) ⟨25787, by rfl⟩ : syracuseStep 137533 = 51575) (by norm_num)
theorem B137569 : Blo 119786 137569 := bbase (se 2 (by rfl) ⟨51588, by rfl⟩ : syracuseStep 137569 = 103177) (by norm_num)
theorem B203141 : Blo 119786 203141 := bbase (se 4 (by rfl) ⟨19044, by rfl⟩ : syracuseStep 203141 = 38089) (by norm_num)
theorem B137605 : Blo 119786 137605 := bbase (se 4 (by rfl) ⟨12900, by rfl⟩ : syracuseStep 137605 = 25801) (by norm_num)
theorem B137641 : Blo 119786 137641 := bbase (se 2 (by rfl) ⟨51615, by rfl⟩ : syracuseStep 137641 = 103231) (by norm_num)
theorem B137677 : Blo 119786 137677 := bbase (se 3 (by rfl) ⟨25814, by rfl⟩ : syracuseStep 137677 = 51629) (by norm_num)
theorem B137713 : Blo 119786 137713 := bbase (se 2 (by rfl) ⟨51642, by rfl⟩ : syracuseStep 137713 = 103285) (by norm_num)
theorem B203269 : Blo 119786 203269 := bbase (se 4 (by rfl) ⟨19056, by rfl⟩ : syracuseStep 203269 = 38113) (by norm_num)
theorem B137749 : Blo 119786 137749 := bbase (se 6 (by rfl) ⟨3228, by rfl⟩ : syracuseStep 137749 = 6457) (by norm_num)
theorem B137785 : Blo 119786 137785 := bbase (se 2 (by rfl) ⟨51669, by rfl⟩ : syracuseStep 137785 = 103339) (by norm_num)
theorem B170581 : Blo 119786 170581 := bbase (se 8 (by rfl) ⟨999, by rfl⟩ : syracuseStep 170581 = 1999) (by norm_num)
theorem B2103893 : Blo 119786 2103893 := bbase (se 8 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 2103893 = 24655) (by norm_num)
theorem B203357 : Blo 119786 203357 := bbase (se 3 (by rfl) ⟨38129, by rfl⟩ : syracuseStep 203357 = 76259) (by norm_num)
theorem B137821 : Blo 119786 137821 := bbase (se 3 (by rfl) ⟨25841, by rfl⟩ : syracuseStep 137821 = 51683) (by norm_num)
theorem B137857 : Blo 119786 137857 := bbase (se 2 (by rfl) ⟨51696, by rfl⟩ : syracuseStep 137857 = 103393) (by norm_num)
theorem B137893 : Blo 119786 137893 := bbase (se 4 (by rfl) ⟨12927, by rfl⟩ : syracuseStep 137893 = 25855) (by norm_num)
theorem B170677 : Blo 119786 170677 := bbase (se 5 (by rfl) ⟨8000, by rfl⟩ : syracuseStep 170677 = 16001) (by norm_num)
theorem B432821 : Blo 119786 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B137929 : Blo 119786 137929 := bbase (se 2 (by rfl) ⟨51723, by rfl⟩ : syracuseStep 137929 = 103447) (by norm_num)
theorem B203485 : Blo 119786 203485 := bbase (se 3 (by rfl) ⟨38153, by rfl⟩ : syracuseStep 203485 = 76307) (by norm_num)
theorem B137965 : Blo 119786 137965 := bbase (se 3 (by rfl) ⟨25868, by rfl⟩ : syracuseStep 137965 = 51737) (by norm_num)
theorem B138001 : Blo 119786 138001 := bbase (se 2 (by rfl) ⟨51750, by rfl⟩ : syracuseStep 138001 = 103501) (by norm_num)
theorem B138029 : Blo 119786 138029 := bbase (se 3 (by rfl) ⟨25880, by rfl⟩ : syracuseStep 138029 = 51761) (by norm_num)
theorem B203573 : Blo 119786 203573 := bbase (se 5 (by rfl) ⟨9542, by rfl⟩ : syracuseStep 203573 = 19085) (by norm_num)
theorem B138037 : Blo 119786 138037 := bbase (se 5 (by rfl) ⟨6470, by rfl⟩ : syracuseStep 138037 = 12941) (by norm_num)
theorem B138073 : Blo 119786 138073 := bbase (se 2 (by rfl) ⟨51777, by rfl⟩ : syracuseStep 138073 = 103555) (by norm_num)
theorem B138109 : Blo 119786 138109 := bbase (se 3 (by rfl) ⟨25895, by rfl⟩ : syracuseStep 138109 = 51791) (by norm_num)
theorem B1579925 : Blo 119786 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B138145 : Blo 119786 138145 := bbase (se 2 (by rfl) ⟨51804, by rfl⟩ : syracuseStep 138145 = 103609) (by norm_num)
theorem B203701 : Blo 119786 203701 := bbase (se 5 (by rfl) ⟨9548, by rfl⟩ : syracuseStep 203701 = 19097) (by norm_num)
theorem B138181 : Blo 119786 138181 := bbase (se 4 (by rfl) ⟨12954, by rfl⟩ : syracuseStep 138181 = 25909) (by norm_num)
theorem B138217 : Blo 119786 138217 := bbase (se 2 (by rfl) ⟨51831, by rfl⟩ : syracuseStep 138217 = 103663) (by norm_num)
theorem B203789 : Blo 119786 203789 := bbase (se 3 (by rfl) ⟨38210, by rfl⟩ : syracuseStep 203789 = 76421) (by norm_num)
theorem B138253 : Blo 119786 138253 := bbase (se 3 (by rfl) ⟨25922, by rfl⟩ : syracuseStep 138253 = 51845) (by norm_num)
theorem B138289 : Blo 119786 138289 := bbase (se 2 (by rfl) ⟨51858, by rfl⟩ : syracuseStep 138289 = 103717) (by norm_num)
theorem B138325 : Blo 119786 138325 := bbase (se 8 (by rfl) ⟨810, by rfl⟩ : syracuseStep 138325 = 1621) (by norm_num)
theorem B138361 : Blo 119786 138361 := bbase (se 2 (by rfl) ⟨51885, by rfl⟩ : syracuseStep 138361 = 103771) (by norm_num)
theorem B203917 : Blo 119786 203917 := bbase (se 3 (by rfl) ⟨38234, by rfl⟩ : syracuseStep 203917 = 76469) (by norm_num)
theorem B138397 : Blo 119786 138397 := bbase (se 3 (by rfl) ⟨25949, by rfl⟩ : syracuseStep 138397 = 51899) (by norm_num)
theorem B171173 : Blo 119786 171173 := bbase (se 4 (by rfl) ⟨16047, by rfl⟩ : syracuseStep 171173 = 32095) (by norm_num)
theorem B138433 : Blo 119786 138433 := bbase (se 2 (by rfl) ⟨51912, by rfl⟩ : syracuseStep 138433 = 103825) (by norm_num)
theorem B204005 : Blo 119786 204005 := bbase (se 4 (by rfl) ⟨19125, by rfl⟩ : syracuseStep 204005 = 38251) (by norm_num)
theorem B138469 : Blo 119786 138469 := bbase (se 4 (by rfl) ⟨12981, by rfl⟩ : syracuseStep 138469 = 25963) (by norm_num)
theorem B269549 : Blo 119786 269549 := bbase (se 3 (by rfl) ⟨50540, by rfl⟩ : syracuseStep 269549 = 101081) (by norm_num)
theorem B466181 : Blo 119786 466181 := bbase (se 4 (by rfl) ⟨43704, by rfl⟩ : syracuseStep 466181 = 87409) (by norm_num)
theorem B138505 : Blo 119786 138505 := bbase (se 2 (by rfl) ⟨51939, by rfl⟩ : syracuseStep 138505 = 103879) (by norm_num)
theorem B138541 : Blo 119786 138541 := bbase (se 3 (by rfl) ⟨25976, by rfl⟩ : syracuseStep 138541 = 51953) (by norm_num)
theorem B269621 : Blo 119786 269621 := bbase (se 5 (by rfl) ⟨12638, by rfl⟩ : syracuseStep 269621 = 25277) (by norm_num)
theorem B138577 : Blo 119786 138577 := bbase (se 2 (by rfl) ⟨51966, by rfl⟩ : syracuseStep 138577 = 103933) (by norm_num)
theorem B204133 : Blo 119786 204133 := bbase (se 4 (by rfl) ⟨19137, by rfl⟩ : syracuseStep 204133 = 38275) (by norm_num)
theorem B138613 : Blo 119786 138613 := bbase (se 5 (by rfl) ⟨6497, by rfl⟩ : syracuseStep 138613 = 12995) (by norm_num)
theorem B269693 : Blo 119786 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B138649 : Blo 119786 138649 := bbase (se 2 (by rfl) ⟨51993, by rfl⟩ : syracuseStep 138649 = 103987) (by norm_num)
theorem B204221 : Blo 119786 204221 := bbase (se 3 (by rfl) ⟨38291, by rfl⟩ : syracuseStep 204221 = 76583) (by norm_num)
theorem B138685 : Blo 119786 138685 := bbase (se 3 (by rfl) ⟨26003, by rfl⟩ : syracuseStep 138685 = 52007) (by norm_num)
theorem B269765 : Blo 119786 269765 := bbase (se 4 (by rfl) ⟨25290, by rfl⟩ : syracuseStep 269765 = 50581) (by norm_num)
theorem B138721 : Blo 119786 138721 := bbase (se 2 (by rfl) ⟨52020, by rfl⟩ : syracuseStep 138721 = 104041) (by norm_num)
theorem B138757 : Blo 119786 138757 := bbase (se 4 (by rfl) ⟨13008, by rfl⟩ : syracuseStep 138757 = 26017) (by norm_num)
theorem B269837 : Blo 119786 269837 := bbase (se 3 (by rfl) ⟨50594, by rfl⟩ : syracuseStep 269837 = 101189) (by norm_num)
theorem B466469 : Blo 119786 466469 := bbase (se 4 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 466469 = 87463) (by norm_num)
theorem B138793 : Blo 119786 138793 := bbase (se 2 (by rfl) ⟨52047, by rfl⟩ : syracuseStep 138793 = 104095) (by norm_num)
theorem B204349 : Blo 119786 204349 := bbase (se 3 (by rfl) ⟨38315, by rfl⟩ : syracuseStep 204349 = 76631) (by norm_num)
theorem B138829 : Blo 119786 138829 := bbase (se 3 (by rfl) ⟨26030, by rfl⟩ : syracuseStep 138829 = 52061) (by norm_num)
theorem B269909 : Blo 119786 269909 := bbase (se 8 (by rfl) ⟨1581, by rfl⟩ : syracuseStep 269909 = 3163) (by norm_num)
theorem B138865 : Blo 119786 138865 := bbase (se 2 (by rfl) ⟨52074, by rfl⟩ : syracuseStep 138865 = 104149) (by norm_num)
theorem B204437 : Blo 119786 204437 := bbase (se 6 (by rfl) ⟨4791, by rfl⟩ : syracuseStep 204437 = 9583) (by norm_num)
theorem B138901 : Blo 119786 138901 := bbase (se 6 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 138901 = 6511) (by norm_num)
theorem B269981 : Blo 119786 269981 := bbase (se 3 (by rfl) ⟨50621, by rfl⟩ : syracuseStep 269981 = 101243) (by norm_num)
theorem B138937 : Blo 119786 138937 := bbase (se 2 (by rfl) ⟨52101, by rfl⟩ : syracuseStep 138937 = 104203) (by norm_num)
theorem B171725 : Blo 119786 171725 := bbase (se 3 (by rfl) ⟨32198, by rfl⟩ : syracuseStep 171725 = 64397) (by norm_num)
theorem B138973 : Blo 119786 138973 := bbase (se 3 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 138973 = 52115) (by norm_num)
theorem B270053 : Blo 119786 270053 := bbase (se 4 (by rfl) ⟨25317, by rfl⟩ : syracuseStep 270053 = 50635) (by norm_num)
theorem B139009 : Blo 119786 139009 := bbase (se 2 (by rfl) ⟨52128, by rfl⟩ : syracuseStep 139009 = 104257) (by norm_num)
theorem B204565 : Blo 119786 204565 := bbase (se 6 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 204565 = 9589) (by norm_num)
theorem B139045 : Blo 119786 139045 := bbase (se 4 (by rfl) ⟨13035, by rfl⟩ : syracuseStep 139045 = 26071) (by norm_num)
theorem B270125 : Blo 119786 270125 := bbase (se 3 (by rfl) ⟨50648, by rfl⟩ : syracuseStep 270125 = 101297) (by norm_num)
theorem B139081 : Blo 119786 139081 := bbase (se 2 (by rfl) ⟨52155, by rfl⟩ : syracuseStep 139081 = 104311) (by norm_num)
theorem B139105 : Blo 119786 139105 := bbase (se 2 (by rfl) ⟨52164, by rfl⟩ : syracuseStep 139105 = 104329) (by norm_num)
theorem B204653 : Blo 119786 204653 := bbase (se 3 (by rfl) ⟨38372, by rfl⟩ : syracuseStep 204653 = 76745) (by norm_num)
theorem B139117 : Blo 119786 139117 := bbase (se 3 (by rfl) ⟨26084, by rfl⟩ : syracuseStep 139117 = 52169) (by norm_num)
theorem B270197 : Blo 119786 270197 := bbase (se 5 (by rfl) ⟨12665, by rfl⟩ : syracuseStep 270197 = 25331) (by norm_num)
theorem B139153 : Blo 119786 139153 := bbase (se 2 (by rfl) ⟨52182, by rfl⟩ : syracuseStep 139153 = 104365) (by norm_num)
theorem B139189 : Blo 119786 139189 := bbase (se 5 (by rfl) ⟨6524, by rfl⟩ : syracuseStep 139189 = 13049) (by norm_num)
theorem B270269 : Blo 119786 270269 := bbase (se 3 (by rfl) ⟨50675, by rfl⟩ : syracuseStep 270269 = 101351) (by norm_num)
theorem B139225 : Blo 119786 139225 := bbase (se 2 (by rfl) ⟨52209, by rfl⟩ : syracuseStep 139225 = 104419) (by norm_num)
theorem B204781 : Blo 119786 204781 := bbase (se 3 (by rfl) ⟨38396, by rfl⟩ : syracuseStep 204781 = 76793) (by norm_num)
theorem B270341 : Blo 119786 270341 := bbase (se 4 (by rfl) ⟨25344, by rfl⟩ : syracuseStep 270341 = 50689) (by norm_num)
theorem B204869 : Blo 119786 204869 := bbase (se 4 (by rfl) ⟨19206, by rfl⟩ : syracuseStep 204869 = 38413) (by norm_num)
theorem B270413 : Blo 119786 270413 := bbase (se 3 (by rfl) ⟨50702, by rfl⟩ : syracuseStep 270413 = 101405) (by norm_num)
theorem B270485 : Blo 119786 270485 := bbase (se 6 (by rfl) ⟨6339, by rfl⟩ : syracuseStep 270485 = 12679) (by norm_num)
theorem B237757 : Blo 119786 237757 := bbase (se 3 (by rfl) ⟨44579, by rfl⟩ : syracuseStep 237757 = 89159) (by norm_num)
theorem B204997 : Blo 119786 204997 := bbase (se 4 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 204997 = 38437) (by norm_num)
theorem B270557 : Blo 119786 270557 := bbase (se 3 (by rfl) ⟨50729, by rfl⟩ : syracuseStep 270557 = 101459) (by norm_num)
theorem B303365 : Blo 119786 303365 := bbase (se 4 (by rfl) ⟨28440, by rfl⟩ : syracuseStep 303365 = 56881) (by norm_num)
theorem B205085 : Blo 119786 205085 := bbase (se 3 (by rfl) ⟨38453, by rfl⟩ : syracuseStep 205085 = 76907) (by norm_num)
theorem B270629 : Blo 119786 270629 := bbase (se 4 (by rfl) ⟨25371, by rfl⟩ : syracuseStep 270629 = 50743) (by norm_num)
theorem B270701 : Blo 119786 270701 := bbase (se 3 (by rfl) ⟨50756, by rfl⟩ : syracuseStep 270701 = 101513) (by norm_num)
theorem B205213 : Blo 119786 205213 := bbase (se 3 (by rfl) ⟨38477, by rfl⟩ : syracuseStep 205213 = 76955) (by norm_num)
theorem B270773 : Blo 119786 270773 := bbase (se 5 (by rfl) ⟨12692, by rfl⟩ : syracuseStep 270773 = 25385) (by norm_num)
theorem B172477 : Blo 119786 172477 := bbase (se 3 (by rfl) ⟨32339, by rfl⟩ : syracuseStep 172477 = 64679) (by norm_num)
theorem B139729 : Blo 119786 139729 := bbase (se 2 (by rfl) ⟨52398, by rfl⟩ : syracuseStep 139729 = 104797) (by norm_num)
theorem B205301 : Blo 119786 205301 := bbase (se 5 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 205301 = 19247) (by norm_num)
theorem B270845 : Blo 119786 270845 := bbase (se 3 (by rfl) ⟨50783, by rfl⟩ : syracuseStep 270845 = 101567) (by norm_num)
theorem B205373 : Blo 119786 205373 := bbase (se 3 (by rfl) ⟨38507, by rfl⟩ : syracuseStep 205373 = 77015) (by norm_num)
theorem B270917 : Blo 119786 270917 := bbase (se 4 (by rfl) ⟨25398, by rfl⟩ : syracuseStep 270917 = 50797) (by norm_num)
theorem B303709 : Blo 119786 303709 := bbase (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) (by norm_num)
theorem B205429 : Blo 119786 205429 := bbase (se 5 (by rfl) ⟨9629, by rfl⟩ : syracuseStep 205429 = 19259) (by norm_num)
theorem B139909 : Blo 119786 139909 := bbase (se 4 (by rfl) ⟨13116, by rfl⟩ : syracuseStep 139909 = 26233) (by norm_num)
theorem B270989 : Blo 119786 270989 := bbase (se 3 (by rfl) ⟨50810, by rfl⟩ : syracuseStep 270989 = 101621) (by norm_num)
theorem B467653 : Blo 119786 467653 := bbase (se 4 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 467653 = 87685) (by norm_num)
theorem B303821 : Blo 119786 303821 := bbase (se 3 (by rfl) ⟨56966, by rfl⟩ : syracuseStep 303821 = 113933) (by norm_num)
theorem B205517 : Blo 119786 205517 := bbase (se 3 (by rfl) ⟨38534, by rfl⟩ : syracuseStep 205517 = 77069) (by norm_num)
theorem B271061 : Blo 119786 271061 := bbase (se 7 (by rfl) ⟨3176, by rfl⟩ : syracuseStep 271061 = 6353) (by norm_num)
theorem B271133 : Blo 119786 271133 := bbase (se 3 (by rfl) ⟨50837, by rfl⟩ : syracuseStep 271133 = 101675) (by norm_num)
theorem B205645 : Blo 119786 205645 := bbase (se 3 (by rfl) ⟨38558, by rfl⟩ : syracuseStep 205645 = 77117) (by norm_num)
theorem B271205 : Blo 119786 271205 := bbase (se 4 (by rfl) ⟨25425, by rfl⟩ : syracuseStep 271205 = 50851) (by norm_num)
theorem B304013 : Blo 119786 304013 := bbase (se 3 (by rfl) ⟨57002, by rfl⟩ : syracuseStep 304013 = 114005) (by norm_num)
theorem B205733 : Blo 119786 205733 := bbase (se 4 (by rfl) ⟨19287, by rfl⟩ : syracuseStep 205733 = 38575) (by norm_num)
theorem B271277 : Blo 119786 271277 := bbase (se 3 (by rfl) ⟨50864, by rfl⟩ : syracuseStep 271277 = 101729) (by norm_num)
theorem B1254325 : Blo 119786 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B271349 : Blo 119786 271349 := bbase (se 5 (by rfl) ⟨12719, by rfl⟩ : syracuseStep 271349 = 25439) (by norm_num)
theorem B467957 : Blo 119786 467957 := bbase (se 5 (by rfl) ⟨21935, by rfl⟩ : syracuseStep 467957 = 43871) (by norm_num)
theorem B205861 : Blo 119786 205861 := bbase (se 4 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 205861 = 38599) (by norm_num)
theorem B271421 : Blo 119786 271421 := bbase (se 3 (by rfl) ⟨50891, by rfl⟩ : syracuseStep 271421 = 101783) (by norm_num)
theorem B140401 : Blo 119786 140401 := bbase (se 2 (by rfl) ⟨52650, by rfl⟩ : syracuseStep 140401 = 105301) (by norm_num)
theorem B205949 : Blo 119786 205949 := bbase (se 3 (by rfl) ⟨38615, by rfl⟩ : syracuseStep 205949 = 77231) (by norm_num)
theorem B271493 : Blo 119786 271493 := bbase (se 4 (by rfl) ⟨25452, by rfl⟩ : syracuseStep 271493 = 50905) (by norm_num)
theorem B271565 : Blo 119786 271565 := bbase (se 3 (by rfl) ⟨50918, by rfl⟩ : syracuseStep 271565 = 101837) (by norm_num)
theorem B173269 : Blo 119786 173269 := bbase (se 7 (by rfl) ⟨2030, by rfl⟩ : syracuseStep 173269 = 4061) (by norm_num)
theorem B304357 : Blo 119786 304357 := bbase (se 4 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 304357 = 57067) (by norm_num)
theorem B206077 : Blo 119786 206077 := bbase (se 3 (by rfl) ⟨38639, by rfl⟩ : syracuseStep 206077 = 77279) (by norm_num)
theorem B271637 : Blo 119786 271637 := bbase (se 6 (by rfl) ⟨6366, by rfl⟩ : syracuseStep 271637 = 12733) (by norm_num)
theorem B992533 : Blo 119786 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B304469 : Blo 119786 304469 := bbase (se 12 (by rfl) ⟨111, by rfl⟩ : syracuseStep 304469 = 223) (by norm_num)
theorem B206165 : Blo 119786 206165 := bbase (se 12 (by rfl) ⟨75, by rfl⟩ : syracuseStep 206165 = 151) (by norm_num)
theorem B271709 : Blo 119786 271709 := bbase (se 3 (by rfl) ⟨50945, by rfl⟩ : syracuseStep 271709 = 101891) (by norm_num)
theorem B664949 : Blo 119786 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B271781 : Blo 119786 271781 := bbase (se 4 (by rfl) ⟨25479, by rfl⟩ : syracuseStep 271781 = 50959) (by norm_num)
theorem B206293 : Blo 119786 206293 := bbase (se 7 (by rfl) ⟨2417, by rfl⟩ : syracuseStep 206293 = 4835) (by norm_num)
theorem B271853 : Blo 119786 271853 := bbase (se 3 (by rfl) ⟨50972, by rfl⟩ : syracuseStep 271853 = 101945) (by norm_num)
theorem B304661 : Blo 119786 304661 := bbase (se 6 (by rfl) ⟨7140, by rfl⟩ : syracuseStep 304661 = 14281) (by norm_num)
theorem B173605 : Blo 119786 173605 := bbase (se 4 (by rfl) ⟨16275, by rfl⟩ : syracuseStep 173605 = 32551) (by norm_num)
theorem B206381 : Blo 119786 206381 := bbase (se 3 (by rfl) ⟨38696, by rfl⟩ : syracuseStep 206381 = 77393) (by norm_num)
theorem B271925 : Blo 119786 271925 := bbase (se 5 (by rfl) ⟨12746, by rfl⟩ : syracuseStep 271925 = 25493) (by norm_num)
theorem B271997 : Blo 119786 271997 := bbase (se 3 (by rfl) ⟨50999, by rfl⟩ : syracuseStep 271997 = 101999) (by norm_num)
theorem B206509 : Blo 119786 206509 := bbase (se 3 (by rfl) ⟨38720, by rfl⟩ : syracuseStep 206509 = 77441) (by norm_num)
theorem B272069 : Blo 119786 272069 := bbase (se 4 (by rfl) ⟨25506, by rfl⟩ : syracuseStep 272069 = 51013) (by norm_num)
theorem B173821 : Blo 119786 173821 := bbase (se 3 (by rfl) ⟨32591, by rfl⟩ : syracuseStep 173821 = 65183) (by norm_num)
theorem B206597 : Blo 119786 206597 := bbase (se 4 (by rfl) ⟨19368, by rfl⟩ : syracuseStep 206597 = 38737) (by norm_num)
theorem B272141 : Blo 119786 272141 := bbase (se 3 (by rfl) ⟨51026, by rfl⟩ : syracuseStep 272141 = 102053) (by norm_num)
theorem B141121 : Blo 119786 141121 := bbase (se 2 (by rfl) ⟨52920, by rfl⟩ : syracuseStep 141121 = 105841) (by norm_num)
theorem B272213 : Blo 119786 272213 := bbase (se 9 (by rfl) ⟨797, by rfl⟩ : syracuseStep 272213 = 1595) (by norm_num)
theorem B141149 : Blo 119786 141149 := bbase (se 3 (by rfl) ⟨26465, by rfl⟩ : syracuseStep 141149 = 52931) (by norm_num)
theorem B305005 : Blo 119786 305005 := bbase (se 3 (by rfl) ⟨57188, by rfl⟩ : syracuseStep 305005 = 114377) (by norm_num)
theorem B206725 : Blo 119786 206725 := bbase (se 4 (by rfl) ⟨19380, by rfl⟩ : syracuseStep 206725 = 38761) (by norm_num)
theorem B272285 : Blo 119786 272285 := bbase (se 3 (by rfl) ⟨51053, by rfl⟩ : syracuseStep 272285 = 102107) (by norm_num)
theorem B206797 : Blo 119786 206797 := bbase (se 3 (by rfl) ⟨38774, by rfl⟩ : syracuseStep 206797 = 77549) (by norm_num)
theorem B305117 : Blo 119786 305117 := bbase (se 3 (by rfl) ⟨57209, by rfl⟩ : syracuseStep 305117 = 114419) (by norm_num)
theorem B206813 : Blo 119786 206813 := bbase (se 3 (by rfl) ⟨38777, by rfl⟩ : syracuseStep 206813 = 77555) (by norm_num)
theorem B272357 : Blo 119786 272357 := bbase (se 4 (by rfl) ⟨25533, by rfl⟩ : syracuseStep 272357 = 51067) (by norm_num)
theorem B272429 : Blo 119786 272429 := bbase (se 3 (by rfl) ⟨51080, by rfl⟩ : syracuseStep 272429 = 102161) (by norm_num)
theorem B206941 : Blo 119786 206941 := bbase (se 3 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 206941 = 77603) (by norm_num)
theorem B272501 : Blo 119786 272501 := bbase (se 5 (by rfl) ⟨12773, by rfl⟩ : syracuseStep 272501 = 25547) (by norm_num)
theorem B174197 : Blo 119786 174197 := bbase (se 5 (by rfl) ⟨8165, by rfl⟩ : syracuseStep 174197 = 16331) (by norm_num)
theorem B305309 : Blo 119786 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B207029 : Blo 119786 207029 := bbase (se 5 (by rfl) ⟨9704, by rfl⟩ : syracuseStep 207029 = 19409) (by norm_num)
theorem B272573 : Blo 119786 272573 := bbase (se 3 (by rfl) ⟨51107, by rfl⟩ : syracuseStep 272573 = 102215) (by norm_num)
theorem B272645 : Blo 119786 272645 := bbase (se 4 (by rfl) ⟨25560, by rfl⟩ : syracuseStep 272645 = 51121) (by norm_num)
theorem B141577 : Blo 119786 141577 := bbase (se 2 (by rfl) ⟨53091, by rfl⟩ : syracuseStep 141577 = 106183) (by norm_num)
theorem B207125 : Blo 119786 207125 := bbase (se 6 (by rfl) ⟨4854, by rfl⟩ : syracuseStep 207125 = 9709) (by norm_num)
theorem B207157 : Blo 119786 207157 := bbase (se 5 (by rfl) ⟨9710, by rfl⟩ : syracuseStep 207157 = 19421) (by norm_num)
theorem B272717 : Blo 119786 272717 := bbase (se 3 (by rfl) ⟨51134, by rfl⟩ : syracuseStep 272717 = 102269) (by norm_num)
theorem B207245 : Blo 119786 207245 := bbase (se 3 (by rfl) ⟨38858, by rfl⟩ : syracuseStep 207245 = 77717) (by norm_num)
theorem B272789 : Blo 119786 272789 := bbase (se 6 (by rfl) ⟨6393, by rfl⟩ : syracuseStep 272789 = 12787) (by norm_num)
theorem B272861 : Blo 119786 272861 := bbase (se 3 (by rfl) ⟨51161, by rfl⟩ : syracuseStep 272861 = 102323) (by norm_num)
theorem B305653 : Blo 119786 305653 := bbase (se 5 (by rfl) ⟨14327, by rfl⟩ : syracuseStep 305653 = 28655) (by norm_num)
theorem B207373 : Blo 119786 207373 := bbase (se 3 (by rfl) ⟨38882, by rfl⟩ : syracuseStep 207373 = 77765) (by norm_num)
theorem B272933 : Blo 119786 272933 := bbase (se 4 (by rfl) ⟨25587, by rfl⟩ : syracuseStep 272933 = 51175) (by norm_num)
theorem B305765 : Blo 119786 305765 := bbase (se 4 (by rfl) ⟨28665, by rfl⟩ : syracuseStep 305765 = 57331) (by norm_num)
theorem B207461 : Blo 119786 207461 := bbase (se 4 (by rfl) ⟨19449, by rfl⟩ : syracuseStep 207461 = 38899) (by norm_num)
theorem B273005 : Blo 119786 273005 := bbase (se 3 (by rfl) ⟨51188, by rfl⟩ : syracuseStep 273005 = 102377) (by norm_num)
theorem B469637 : Blo 119786 469637 := bbase (se 4 (by rfl) ⟨44028, by rfl⟩ : syracuseStep 469637 = 88057) (by norm_num)
theorem B174757 : Blo 119786 174757 := bbase (se 4 (by rfl) ⟨16383, by rfl⟩ : syracuseStep 174757 = 32767) (by norm_num)
theorem B273077 : Blo 119786 273077 := bbase (se 5 (by rfl) ⟨12800, by rfl⟩ : syracuseStep 273077 = 25601) (by norm_num)
theorem B404165 : Blo 119786 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B207589 : Blo 119786 207589 := bbase (se 4 (by rfl) ⟨19461, by rfl⟩ : syracuseStep 207589 = 38923) (by norm_num)
theorem B273149 : Blo 119786 273149 := bbase (se 3 (by rfl) ⟨51215, by rfl⟩ : syracuseStep 273149 = 102431) (by norm_num)
theorem B305957 : Blo 119786 305957 := bbase (se 4 (by rfl) ⟨28683, by rfl⟩ : syracuseStep 305957 = 57367) (by norm_num)
theorem B207677 : Blo 119786 207677 := bbase (se 3 (by rfl) ⟨38939, by rfl⟩ : syracuseStep 207677 = 77879) (by norm_num)
theorem B273221 : Blo 119786 273221 := bbase (se 4 (by rfl) ⟨25614, by rfl⟩ : syracuseStep 273221 = 51229) (by norm_num)
theorem B273293 : Blo 119786 273293 := bbase (se 3 (by rfl) ⟨51242, by rfl⟩ : syracuseStep 273293 = 102485) (by norm_num)
theorem B404405 : Blo 119786 404405 := bbase (se 5 (by rfl) ⟨18956, by rfl⟩ : syracuseStep 404405 = 37913) (by norm_num)
theorem B207805 : Blo 119786 207805 := bbase (se 3 (by rfl) ⟨38963, by rfl⟩ : syracuseStep 207805 = 77927) (by norm_num)
theorem B273365 : Blo 119786 273365 := bbase (se 7 (by rfl) ⟨3203, by rfl⟩ : syracuseStep 273365 = 6407) (by norm_num)
theorem B207893 : Blo 119786 207893 := bbase (se 6 (by rfl) ⟨4872, by rfl⟩ : syracuseStep 207893 = 9745) (by norm_num)
theorem B273437 : Blo 119786 273437 := bbase (se 3 (by rfl) ⟨51269, by rfl⟩ : syracuseStep 273437 = 102539) (by norm_num)
theorem B273509 : Blo 119786 273509 := bbase (se 4 (by rfl) ⟨25641, by rfl⟩ : syracuseStep 273509 = 51283) (by norm_num)
theorem B207973 : Blo 119786 207973 := bbase (se 4 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 207973 = 38995) (by norm_num)
theorem B306301 : Blo 119786 306301 := bbase (se 3 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 306301 = 114863) (by norm_num)
theorem B208021 : Blo 119786 208021 := bbase (se 6 (by rfl) ⟨4875, by rfl⟩ : syracuseStep 208021 = 9751) (by norm_num)
theorem B273581 : Blo 119786 273581 := bbase (se 3 (by rfl) ⟨51296, by rfl⟩ : syracuseStep 273581 = 102593) (by norm_num)
theorem B306413 : Blo 119786 306413 := bbase (se 3 (by rfl) ⟨57452, by rfl⟩ : syracuseStep 306413 = 114905) (by norm_num)
theorem B208109 : Blo 119786 208109 := bbase (se 3 (by rfl) ⟨39020, by rfl⟩ : syracuseStep 208109 = 78041) (by norm_num)
theorem B273653 : Blo 119786 273653 := bbase (se 5 (by rfl) ⟨12827, by rfl⟩ : syracuseStep 273653 = 25655) (by norm_num)
theorem B273725 : Blo 119786 273725 := bbase (se 3 (by rfl) ⟨51323, by rfl⟩ : syracuseStep 273725 = 102647) (by norm_num)
theorem B404837 : Blo 119786 404837 := bbase (se 4 (by rfl) ⟨37953, by rfl⟩ : syracuseStep 404837 = 75907) (by norm_num)
theorem B208237 : Blo 119786 208237 := bbase (se 3 (by rfl) ⟨39044, by rfl⟩ : syracuseStep 208237 = 78089) (by norm_num)
theorem B273797 : Blo 119786 273797 := bbase (se 4 (by rfl) ⟨25668, by rfl⟩ : syracuseStep 273797 = 51337) (by norm_num)
theorem B306605 : Blo 119786 306605 := bbase (se 3 (by rfl) ⟨57488, by rfl⟩ : syracuseStep 306605 = 114977) (by norm_num)
theorem B208325 : Blo 119786 208325 := bbase (se 4 (by rfl) ⟨19530, by rfl⟩ : syracuseStep 208325 = 39061) (by norm_num)
theorem B273869 : Blo 119786 273869 := bbase (se 3 (by rfl) ⟨51350, by rfl⟩ : syracuseStep 273869 = 102701) (by norm_num)
theorem B175621 : Blo 119786 175621 := bbase (se 4 (by rfl) ⟨16464, by rfl⟩ : syracuseStep 175621 = 32929) (by norm_num)
theorem B273941 : Blo 119786 273941 := bbase (se 6 (by rfl) ⟨6420, by rfl⟩ : syracuseStep 273941 = 12841) (by norm_num)
theorem B863797 : Blo 119786 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B208453 : Blo 119786 208453 := bbase (se 4 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 208453 = 39085) (by norm_num)
theorem B536149 : Blo 119786 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B274013 : Blo 119786 274013 := bbase (se 3 (by rfl) ⟨51377, by rfl⟩ : syracuseStep 274013 = 102755) (by norm_num)
theorem B208541 : Blo 119786 208541 := bbase (se 3 (by rfl) ⟨39101, by rfl⟩ : syracuseStep 208541 = 78203) (by norm_num)
theorem B274085 : Blo 119786 274085 := bbase (se 4 (by rfl) ⟨25695, by rfl⟩ : syracuseStep 274085 = 51391) (by norm_num)
theorem B274157 : Blo 119786 274157 := bbase (se 3 (by rfl) ⟨51404, by rfl⟩ : syracuseStep 274157 = 102809) (by norm_num)
theorem B306949 : Blo 119786 306949 := bbase (se 4 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 306949 = 57553) (by norm_num)
theorem B405269 : Blo 119786 405269 := bbase (se 6 (by rfl) ⟨9498, by rfl⟩ : syracuseStep 405269 = 18997) (by norm_num)
theorem B208669 : Blo 119786 208669 := bbase (se 3 (by rfl) ⟨39125, by rfl⟩ : syracuseStep 208669 = 78251) (by norm_num)
theorem B274229 : Blo 119786 274229 := bbase (se 5 (by rfl) ⟨12854, by rfl⟩ : syracuseStep 274229 = 25709) (by norm_num)
theorem B307061 : Blo 119786 307061 := bbase (se 5 (by rfl) ⟨14393, by rfl⟩ : syracuseStep 307061 = 28787) (by norm_num)
theorem B208757 : Blo 119786 208757 := bbase (se 5 (by rfl) ⟨9785, by rfl⟩ : syracuseStep 208757 = 19571) (by norm_num)
theorem B274301 : Blo 119786 274301 := bbase (se 3 (by rfl) ⟨51431, by rfl⟩ : syracuseStep 274301 = 102863) (by norm_num)
theorem B929717 : Blo 119786 929717 := bbase (se 5 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 929717 = 87161) (by norm_num)
theorem B274373 : Blo 119786 274373 := bbase (se 4 (by rfl) ⟨25722, by rfl⟩ : syracuseStep 274373 = 51445) (by norm_num)
theorem B208885 : Blo 119786 208885 := bbase (se 5 (by rfl) ⟨9791, by rfl⟩ : syracuseStep 208885 = 19583) (by norm_num)
theorem B274445 : Blo 119786 274445 := bbase (se 3 (by rfl) ⟨51458, by rfl⟩ : syracuseStep 274445 = 102917) (by norm_num)
theorem B307253 : Blo 119786 307253 := bbase (se 5 (by rfl) ⟨14402, by rfl⟩ : syracuseStep 307253 = 28805) (by norm_num)
theorem B274517 : Blo 119786 274517 := bbase (se 8 (by rfl) ⟨1608, by rfl⟩ : syracuseStep 274517 = 3217) (by norm_num)
theorem B176213 : Blo 119786 176213 := bbase (se 8 (by rfl) ⟨1032, by rfl⟩ : syracuseStep 176213 = 2065) (by norm_num)
theorem B274589 : Blo 119786 274589 := bbase (se 3 (by rfl) ⟨51485, by rfl⟩ : syracuseStep 274589 = 102971) (by norm_num)
theorem B405701 : Blo 119786 405701 := bbase (se 4 (by rfl) ⟨38034, by rfl⟩ : syracuseStep 405701 = 76069) (by norm_num)
theorem B274661 : Blo 119786 274661 := bbase (se 4 (by rfl) ⟨25749, by rfl⟩ : syracuseStep 274661 = 51499) (by norm_num)
theorem B274733 : Blo 119786 274733 := bbase (se 3 (by rfl) ⟨51512, by rfl⟩ : syracuseStep 274733 = 103025) (by norm_num)
theorem B274805 : Blo 119786 274805 := bbase (se 5 (by rfl) ⟨12881, by rfl⟩ : syracuseStep 274805 = 25763) (by norm_num)
theorem B307597 : Blo 119786 307597 := bbase (se 3 (by rfl) ⟨57674, by rfl⟩ : syracuseStep 307597 = 115349) (by norm_num)
theorem B274877 : Blo 119786 274877 := bbase (se 3 (by rfl) ⟨51539, by rfl⟩ : syracuseStep 274877 = 103079) (by norm_num)
theorem B307709 : Blo 119786 307709 := bbase (se 3 (by rfl) ⟨57695, by rfl⟩ : syracuseStep 307709 = 115391) (by norm_num)
theorem B274949 : Blo 119786 274949 := bbase (se 4 (by rfl) ⟨25776, by rfl⟩ : syracuseStep 274949 = 51553) (by norm_num)
theorem B275021 : Blo 119786 275021 := bbase (se 3 (by rfl) ⟨51566, by rfl⟩ : syracuseStep 275021 = 103133) (by norm_num)
theorem B406133 : Blo 119786 406133 := bbase (se 5 (by rfl) ⟨19037, by rfl⟩ : syracuseStep 406133 = 38075) (by norm_num)
theorem B209533 : Blo 119786 209533 := bbase (se 3 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 209533 = 78575) (by norm_num)
theorem B275093 : Blo 119786 275093 := bbase (se 6 (by rfl) ⟨6447, by rfl⟩ : syracuseStep 275093 = 12895) (by norm_num)
theorem B307901 : Blo 119786 307901 := bbase (se 3 (by rfl) ⟨57731, by rfl⟩ : syracuseStep 307901 = 115463) (by norm_num)
theorem B275165 : Blo 119786 275165 := bbase (se 3 (by rfl) ⟨51593, by rfl⟩ : syracuseStep 275165 = 103187) (by norm_num)
theorem B701173 : Blo 119786 701173 := bbase (se 5 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 701173 = 65735) (by norm_num)
theorem B275237 : Blo 119786 275237 := bbase (se 4 (by rfl) ⟨25803, by rfl⟩ : syracuseStep 275237 = 51607) (by norm_num)
theorem B8926037 : Blo 119786 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B275309 : Blo 119786 275309 := bbase (se 3 (by rfl) ⟨51620, by rfl⟩ : syracuseStep 275309 = 103241) (by norm_num)
theorem B471941 : Blo 119786 471941 := bbase (se 4 (by rfl) ⟨44244, by rfl⟩ : syracuseStep 471941 = 88489) (by norm_num)
theorem B275381 : Blo 119786 275381 := bbase (se 5 (by rfl) ⟨12908, by rfl⟩ : syracuseStep 275381 = 25817) (by norm_num)
theorem B275437 : Blo 119786 275437 := bbase (se 3 (by rfl) ⟨51644, by rfl⟩ : syracuseStep 275437 = 103289) (by norm_num)
theorem B275453 : Blo 119786 275453 := bbase (se 3 (by rfl) ⟨51647, by rfl⟩ : syracuseStep 275453 = 103295) (by norm_num)
theorem B308245 : Blo 119786 308245 := bbase (se 6 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 308245 = 14449) (by norm_num)
theorem B406565 : Blo 119786 406565 := bbase (se 4 (by rfl) ⟨38115, by rfl⟩ : syracuseStep 406565 = 76231) (by norm_num)
theorem B275525 : Blo 119786 275525 := bbase (se 4 (by rfl) ⟨25830, by rfl⟩ : syracuseStep 275525 = 51661) (by norm_num)
theorem B144509 : Blo 119786 144509 := bbase (se 3 (by rfl) ⟨27095, by rfl⟩ : syracuseStep 144509 = 54191) (by norm_num)
theorem B308357 : Blo 119786 308357 := bbase (se 4 (by rfl) ⟨28908, by rfl⟩ : syracuseStep 308357 = 57817) (by norm_num)
theorem B275597 : Blo 119786 275597 := bbase (se 3 (by rfl) ⟨51674, by rfl⟩ : syracuseStep 275597 = 103349) (by norm_num)
theorem B210077 : Blo 119786 210077 := bbase (se 3 (by rfl) ⟨39389, by rfl⟩ : syracuseStep 210077 = 78779) (by norm_num)
theorem B275669 : Blo 119786 275669 := bbase (se 7 (by rfl) ⟨3230, by rfl⟩ : syracuseStep 275669 = 6461) (by norm_num)
theorem B275741 : Blo 119786 275741 := bbase (se 3 (by rfl) ⟨51701, by rfl⟩ : syracuseStep 275741 = 103403) (by norm_num)
theorem B308549 : Blo 119786 308549 := bbase (se 4 (by rfl) ⟨28926, by rfl⟩ : syracuseStep 308549 = 57853) (by norm_num)
theorem B275813 : Blo 119786 275813 := bbase (se 4 (by rfl) ⟨25857, by rfl⟩ : syracuseStep 275813 = 51715) (by norm_num)
theorem B275885 : Blo 119786 275885 := bbase (se 3 (by rfl) ⟨51728, by rfl⟩ : syracuseStep 275885 = 103457) (by norm_num)
theorem B406997 : Blo 119786 406997 := bbase (se 7 (by rfl) ⟨4769, by rfl⟩ : syracuseStep 406997 = 9539) (by norm_num)
theorem B275957 : Blo 119786 275957 := bbase (se 5 (by rfl) ⟨12935, by rfl⟩ : syracuseStep 275957 = 25871) (by norm_num)
theorem B276029 : Blo 119786 276029 := bbase (se 3 (by rfl) ⟨51755, by rfl⟩ : syracuseStep 276029 = 103511) (by norm_num)
theorem B276101 : Blo 119786 276101 := bbase (se 4 (by rfl) ⟨25884, by rfl⟩ : syracuseStep 276101 = 51769) (by norm_num)
theorem B308893 : Blo 119786 308893 := bbase (se 3 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 308893 = 115835) (by norm_num)
theorem B276173 : Blo 119786 276173 := bbase (se 3 (by rfl) ⟨51782, by rfl⟩ : syracuseStep 276173 = 103565) (by norm_num)
theorem B341765 : Blo 119786 341765 := bbase (se 4 (by rfl) ⟨32040, by rfl⟩ : syracuseStep 341765 = 64081) (by norm_num)
theorem B309005 : Blo 119786 309005 := bbase (se 3 (by rfl) ⟨57938, by rfl⟩ : syracuseStep 309005 = 115877) (by norm_num)
theorem B276245 : Blo 119786 276245 := bbase (se 6 (by rfl) ⟨6474, by rfl⟩ : syracuseStep 276245 = 12949) (by norm_num)
theorem B145201 : Blo 119786 145201 := bbase (se 2 (by rfl) ⟨54450, by rfl⟩ : syracuseStep 145201 = 108901) (by norm_num)
theorem B1029941 : Blo 119786 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B505685 : Blo 119786 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B276317 : Blo 119786 276317 := bbase (se 3 (by rfl) ⟨51809, by rfl⟩ : syracuseStep 276317 = 103619) (by norm_num)
theorem B407429 : Blo 119786 407429 := bbase (se 4 (by rfl) ⟨38196, by rfl⟩ : syracuseStep 407429 = 76393) (by norm_num)
theorem B145297 : Blo 119786 145297 := bbase (se 2 (by rfl) ⟨54486, by rfl⟩ : syracuseStep 145297 = 108973) (by norm_num)
theorem B276389 : Blo 119786 276389 := bbase (se 4 (by rfl) ⟨25911, by rfl⟩ : syracuseStep 276389 = 51823) (by norm_num)
theorem B309197 : Blo 119786 309197 := bbase (se 3 (by rfl) ⟨57974, by rfl⟩ : syracuseStep 309197 = 115949) (by norm_num)
theorem B276461 : Blo 119786 276461 := bbase (se 3 (by rfl) ⟨51836, by rfl⟩ : syracuseStep 276461 = 103673) (by norm_num)
theorem B276533 : Blo 119786 276533 := bbase (se 5 (by rfl) ⟨12962, by rfl⟩ : syracuseStep 276533 = 25925) (by norm_num)
theorem B276605 : Blo 119786 276605 := bbase (se 3 (by rfl) ⟨51863, by rfl⟩ : syracuseStep 276605 = 103727) (by norm_num)
theorem B276677 : Blo 119786 276677 := bbase (se 4 (by rfl) ⟨25938, by rfl⟩ : syracuseStep 276677 = 51877) (by norm_num)
theorem B276749 : Blo 119786 276749 := bbase (se 3 (by rfl) ⟨51890, by rfl⟩ : syracuseStep 276749 = 103781) (by norm_num)
theorem B833813 : Blo 119786 833813 := bbase (se 6 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 833813 = 39085) (by norm_num)
theorem B178453 : Blo 119786 178453 := bbase (se 6 (by rfl) ⟨4182, by rfl⟩ : syracuseStep 178453 = 8365) (by norm_num)
theorem B309541 : Blo 119786 309541 := bbase (se 4 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 309541 = 58039) (by norm_num)
theorem B407861 : Blo 119786 407861 := bbase (se 5 (by rfl) ⟨19118, by rfl⟩ : syracuseStep 407861 = 38237) (by norm_num)
theorem B276821 : Blo 119786 276821 := bbase (se 10 (by rfl) ⟨405, by rfl⟩ : syracuseStep 276821 = 811) (by norm_num)
theorem B440677 : Blo 119786 440677 := bbase (se 4 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 440677 = 82627) (by norm_num)
theorem B309653 : Blo 119786 309653 := bbase (se 6 (by rfl) ⟨7257, by rfl⟩ : syracuseStep 309653 = 14515) (by norm_num)
theorem B276893 : Blo 119786 276893 := bbase (se 3 (by rfl) ⟨51917, by rfl⟩ : syracuseStep 276893 = 103835) (by norm_num)
theorem B276965 : Blo 119786 276965 := bbase (se 4 (by rfl) ⟨25965, by rfl⟩ : syracuseStep 276965 = 51931) (by norm_num)
theorem B506341 : Blo 119786 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B277037 : Blo 119786 277037 := bbase (se 3 (by rfl) ⟨51944, by rfl⟩ : syracuseStep 277037 = 103889) (by norm_num)
theorem B309845 : Blo 119786 309845 := bbase (se 8 (by rfl) ⟨1815, by rfl⟩ : syracuseStep 309845 = 3631) (by norm_num)
theorem B277109 : Blo 119786 277109 := bbase (se 5 (by rfl) ⟨12989, by rfl⟩ : syracuseStep 277109 = 25979) (by norm_num)
theorem B146081 : Blo 119786 146081 := bbase (se 2 (by rfl) ⟨54780, by rfl⟩ : syracuseStep 146081 = 109561) (by norm_num)
theorem B277181 : Blo 119786 277181 := bbase (se 3 (by rfl) ⟨51971, by rfl⟩ : syracuseStep 277181 = 103943) (by norm_num)
theorem B408293 : Blo 119786 408293 := bbase (se 4 (by rfl) ⟨38277, by rfl⟩ : syracuseStep 408293 = 76555) (by norm_num)
theorem B277253 : Blo 119786 277253 := bbase (se 4 (by rfl) ⟨25992, by rfl⟩ : syracuseStep 277253 = 51985) (by norm_num)
theorem B277325 : Blo 119786 277325 := bbase (se 3 (by rfl) ⟨51998, by rfl⟩ : syracuseStep 277325 = 103997) (by norm_num)
theorem B703349 : Blo 119786 703349 := bbase (se 5 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 703349 = 65939) (by norm_num)
theorem B277397 : Blo 119786 277397 := bbase (se 6 (by rfl) ⟨6501, by rfl⟩ : syracuseStep 277397 = 13003) (by norm_num)
theorem B342949 : Blo 119786 342949 := bbase (se 4 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 342949 = 64303) (by norm_num)
theorem B310189 : Blo 119786 310189 := bbase (se 3 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 310189 = 116321) (by norm_num)
theorem B146389 : Blo 119786 146389 := bbase (se 7 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 146389 = 3431) (by norm_num)
theorem B277469 : Blo 119786 277469 := bbase (se 3 (by rfl) ⟨52025, by rfl⟩ : syracuseStep 277469 = 104051) (by norm_num)
theorem B703477 : Blo 119786 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B310301 : Blo 119786 310301 := bbase (se 3 (by rfl) ⟨58181, by rfl⟩ : syracuseStep 310301 = 116363) (by norm_num)
theorem B277541 : Blo 119786 277541 := bbase (se 4 (by rfl) ⟨26019, by rfl⟩ : syracuseStep 277541 = 52039) (by norm_num)
theorem B343109 : Blo 119786 343109 := bbase (se 4 (by rfl) ⟨32166, by rfl⟩ : syracuseStep 343109 = 64333) (by norm_num)
theorem B277613 : Blo 119786 277613 := bbase (se 3 (by rfl) ⟨52052, by rfl⟩ : syracuseStep 277613 = 104105) (by norm_num)
theorem B408725 : Blo 119786 408725 := bbase (se 6 (by rfl) ⟨9579, by rfl⟩ : syracuseStep 408725 = 19159) (by norm_num)
theorem B277685 : Blo 119786 277685 := bbase (se 5 (by rfl) ⟨13016, by rfl⟩ : syracuseStep 277685 = 26033) (by norm_num)
theorem B310493 : Blo 119786 310493 := bbase (se 3 (by rfl) ⟨58217, by rfl⟩ : syracuseStep 310493 = 116435) (by norm_num)
theorem B277757 : Blo 119786 277757 := bbase (se 3 (by rfl) ⟨52079, by rfl⟩ : syracuseStep 277757 = 104159) (by norm_num)
theorem B343349 : Blo 119786 343349 := bbase (se 5 (by rfl) ⟨16094, by rfl⟩ : syracuseStep 343349 = 32189) (by norm_num)
theorem B277829 : Blo 119786 277829 := bbase (se 4 (by rfl) ⟨26046, by rfl⟩ : syracuseStep 277829 = 52093) (by norm_num)
theorem B146777 : Blo 119786 146777 := bbase (se 2 (by rfl) ⟨55041, by rfl⟩ : syracuseStep 146777 = 110083) (by norm_num)
theorem B277901 : Blo 119786 277901 := bbase (se 3 (by rfl) ⟨52106, by rfl⟩ : syracuseStep 277901 = 104213) (by norm_num)
theorem B245149 : Blo 119786 245149 := bbase (se 3 (by rfl) ⟨45965, by rfl⟩ : syracuseStep 245149 = 91931) (by norm_num)
theorem B277973 : Blo 119786 277973 := bbase (se 7 (by rfl) ⟨3257, by rfl⟩ : syracuseStep 277973 = 6515) (by norm_num)
theorem B179693 : Blo 119786 179693 := bbase (se 3 (by rfl) ⟨33692, by rfl⟩ : syracuseStep 179693 = 67385) (by norm_num)
theorem B343541 : Blo 119786 343541 := bbase (se 5 (by rfl) ⟨16103, by rfl⟩ : syracuseStep 343541 = 32207) (by norm_num)
theorem B179717 : Blo 119786 179717 := bbase (se 4 (by rfl) ⟨16848, by rfl⟩ : syracuseStep 179717 = 33697) (by norm_num)
theorem B179741 : Blo 119786 179741 := bbase (se 3 (by rfl) ⟨33701, by rfl⟩ : syracuseStep 179741 = 67403) (by norm_num)
theorem B278045 : Blo 119786 278045 := bbase (se 3 (by rfl) ⟨52133, by rfl⟩ : syracuseStep 278045 = 104267) (by norm_num)
theorem B179765 : Blo 119786 179765 := bbase (se 5 (by rfl) ⟨8426, by rfl⟩ : syracuseStep 179765 = 16853) (by norm_num)
theorem B310837 : Blo 119786 310837 := bbase (se 5 (by rfl) ⟨14570, by rfl⟩ : syracuseStep 310837 = 29141) (by norm_num)
theorem B409157 : Blo 119786 409157 := bbase (se 4 (by rfl) ⟨38358, by rfl⟩ : syracuseStep 409157 = 76717) (by norm_num)
theorem B179789 : Blo 119786 179789 := bbase (se 3 (by rfl) ⟨33710, by rfl⟩ : syracuseStep 179789 = 67421) (by norm_num)
theorem B179813 : Blo 119786 179813 := bbase (se 4 (by rfl) ⟨16857, by rfl⟩ : syracuseStep 179813 = 33715) (by norm_num)
theorem B278117 : Blo 119786 278117 := bbase (se 4 (by rfl) ⟨26073, by rfl⟩ : syracuseStep 278117 = 52147) (by norm_num)
theorem B179837 : Blo 119786 179837 := bbase (se 3 (by rfl) ⟨33719, by rfl⟩ : syracuseStep 179837 = 67439) (by norm_num)
theorem B179861 : Blo 119786 179861 := bbase (se 6 (by rfl) ⟨4215, by rfl⟩ : syracuseStep 179861 = 8431) (by norm_num)
theorem B310949 : Blo 119786 310949 := bbase (se 4 (by rfl) ⟨29151, by rfl⟩ : syracuseStep 310949 = 58303) (by norm_num)
theorem B179885 : Blo 119786 179885 := bbase (se 3 (by rfl) ⟨33728, by rfl⟩ : syracuseStep 179885 = 67457) (by norm_num)
theorem B278189 : Blo 119786 278189 := bbase (se 3 (by rfl) ⟨52160, by rfl⟩ : syracuseStep 278189 = 104321) (by norm_num)
theorem B147133 : Blo 119786 147133 := bbase (se 3 (by rfl) ⟨27587, by rfl⟩ : syracuseStep 147133 = 55175) (by norm_num)
theorem B179909 : Blo 119786 179909 := bbase (se 4 (by rfl) ⟨16866, by rfl⟩ : syracuseStep 179909 = 33733) (by norm_num)
theorem B179933 : Blo 119786 179933 := bbase (se 3 (by rfl) ⟨33737, by rfl⟩ : syracuseStep 179933 = 67475) (by norm_num)
theorem B179957 : Blo 119786 179957 := bbase (se 5 (by rfl) ⟨8435, by rfl⟩ : syracuseStep 179957 = 16871) (by norm_num)
theorem B278261 : Blo 119786 278261 := bbase (se 5 (by rfl) ⟨13043, by rfl⟩ : syracuseStep 278261 = 26087) (by norm_num)
theorem B179981 : Blo 119786 179981 := bbase (se 3 (by rfl) ⟨33746, by rfl⟩ : syracuseStep 179981 = 67493) (by norm_num)
theorem B180005 : Blo 119786 180005 := bbase (se 4 (by rfl) ⟨16875, by rfl⟩ : syracuseStep 180005 = 33751) (by norm_num)
theorem B180029 : Blo 119786 180029 := bbase (se 3 (by rfl) ⟨33755, by rfl⟩ : syracuseStep 180029 = 67511) (by norm_num)
theorem B278333 : Blo 119786 278333 := bbase (se 3 (by rfl) ⟨52187, by rfl⟩ : syracuseStep 278333 = 104375) (by norm_num)
theorem B180053 : Blo 119786 180053 := bbase (se 9 (by rfl) ⟨527, by rfl⟩ : syracuseStep 180053 = 1055) (by norm_num)
theorem B311141 : Blo 119786 311141 := bbase (se 4 (by rfl) ⟨29169, by rfl⟩ : syracuseStep 311141 = 58339) (by norm_num)
theorem B180077 : Blo 119786 180077 := bbase (se 3 (by rfl) ⟨33764, by rfl⟩ : syracuseStep 180077 = 67529) (by norm_num)
theorem B180101 : Blo 119786 180101 := bbase (se 4 (by rfl) ⟨16884, by rfl⟩ : syracuseStep 180101 = 33769) (by norm_num)
theorem B278405 : Blo 119786 278405 := bbase (se 4 (by rfl) ⟨26100, by rfl⟩ : syracuseStep 278405 = 52201) (by norm_num)
theorem B180125 : Blo 119786 180125 := bbase (se 3 (by rfl) ⟨33773, by rfl⟩ : syracuseStep 180125 = 67547) (by norm_num)
theorem B376741 : Blo 119786 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B180149 : Blo 119786 180149 := bbase (se 5 (by rfl) ⟨8444, by rfl⟩ : syracuseStep 180149 = 16889) (by norm_num)
theorem B245693 : Blo 119786 245693 := bbase (se 3 (by rfl) ⟨46067, by rfl⟩ : syracuseStep 245693 = 92135) (by norm_num)
theorem B180173 : Blo 119786 180173 := bbase (se 3 (by rfl) ⟨33782, by rfl⟩ : syracuseStep 180173 = 67565) (by norm_num)
theorem B278477 : Blo 119786 278477 := bbase (se 3 (by rfl) ⟨52214, by rfl⟩ : syracuseStep 278477 = 104429) (by norm_num)
theorem B180197 : Blo 119786 180197 := bbase (se 4 (by rfl) ⟨16893, by rfl⟩ : syracuseStep 180197 = 33787) (by norm_num)
theorem B409589 : Blo 119786 409589 := bbase (se 5 (by rfl) ⟨19199, by rfl⟩ : syracuseStep 409589 = 38399) (by norm_num)
theorem B180221 : Blo 119786 180221 := bbase (se 3 (by rfl) ⟨33791, by rfl⟩ : syracuseStep 180221 = 67583) (by norm_num)
theorem B147469 : Blo 119786 147469 := bbase (se 3 (by rfl) ⟨27650, by rfl⟩ : syracuseStep 147469 = 55301) (by norm_num)
theorem B180245 : Blo 119786 180245 := bbase (se 6 (by rfl) ⟨4224, by rfl⟩ : syracuseStep 180245 = 8449) (by norm_num)
theorem B180269 : Blo 119786 180269 := bbase (se 3 (by rfl) ⟨33800, by rfl⟩ : syracuseStep 180269 = 67601) (by norm_num)
theorem B180293 : Blo 119786 180293 := bbase (se 4 (by rfl) ⟨16902, by rfl⟩ : syracuseStep 180293 = 33805) (by norm_num)
theorem B180317 : Blo 119786 180317 := bbase (se 3 (by rfl) ⟨33809, by rfl⟩ : syracuseStep 180317 = 67619) (by norm_num)
theorem B180341 : Blo 119786 180341 := bbase (se 5 (by rfl) ⟨8453, by rfl⟩ : syracuseStep 180341 = 16907) (by norm_num)
theorem B180365 : Blo 119786 180365 := bbase (se 3 (by rfl) ⟨33818, by rfl⟩ : syracuseStep 180365 = 67637) (by norm_num)
theorem B180389 : Blo 119786 180389 := bbase (se 4 (by rfl) ⟨16911, by rfl⟩ : syracuseStep 180389 = 33823) (by norm_num)
theorem B180413 : Blo 119786 180413 := bbase (se 3 (by rfl) ⟨33827, by rfl⟩ : syracuseStep 180413 = 67655) (by norm_num)
theorem B311485 : Blo 119786 311485 := bbase (se 3 (by rfl) ⟨58403, by rfl⟩ : syracuseStep 311485 = 116807) (by norm_num)
theorem B180437 : Blo 119786 180437 := bbase (se 7 (by rfl) ⟨2114, by rfl⟩ : syracuseStep 180437 = 4229) (by norm_num)
theorem B180461 : Blo 119786 180461 := bbase (se 3 (by rfl) ⟨33836, by rfl⟩ : syracuseStep 180461 = 67673) (by norm_num)
theorem B180485 : Blo 119786 180485 := bbase (se 4 (by rfl) ⟨16920, by rfl⟩ : syracuseStep 180485 = 33841) (by norm_num)
theorem B180509 : Blo 119786 180509 := bbase (se 3 (by rfl) ⟨33845, by rfl⟩ : syracuseStep 180509 = 67691) (by norm_num)
theorem B311597 : Blo 119786 311597 := bbase (se 3 (by rfl) ⟨58424, by rfl⟩ : syracuseStep 311597 = 116849) (by norm_num)
theorem B180533 : Blo 119786 180533 := bbase (se 5 (by rfl) ⟨8462, by rfl⟩ : syracuseStep 180533 = 16925) (by norm_num)
theorem B180557 : Blo 119786 180557 := bbase (se 3 (by rfl) ⟨33854, by rfl⟩ : syracuseStep 180557 = 67709) (by norm_num)
theorem B1163605 : Blo 119786 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B180581 : Blo 119786 180581 := bbase (se 4 (by rfl) ⟨16929, by rfl⟩ : syracuseStep 180581 = 33859) (by norm_num)
theorem B180605 : Blo 119786 180605 := bbase (se 3 (by rfl) ⟨33863, by rfl⟩ : syracuseStep 180605 = 67727) (by norm_num)
theorem B180629 : Blo 119786 180629 := bbase (se 6 (by rfl) ⟨4233, by rfl⟩ : syracuseStep 180629 = 8467) (by norm_num)
theorem B410021 : Blo 119786 410021 := bbase (se 4 (by rfl) ⟨38439, by rfl⟩ : syracuseStep 410021 = 76879) (by norm_num)
theorem B180653 : Blo 119786 180653 := bbase (se 3 (by rfl) ⟨33872, by rfl⟩ : syracuseStep 180653 = 67745) (by norm_num)
theorem B180677 : Blo 119786 180677 := bbase (se 4 (by rfl) ⟨16938, by rfl⟩ : syracuseStep 180677 = 33877) (by norm_num)
theorem B344533 : Blo 119786 344533 := bbase (se 7 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 344533 = 8075) (by norm_num)
theorem B180701 : Blo 119786 180701 := bbase (se 3 (by rfl) ⟨33881, by rfl⟩ : syracuseStep 180701 = 67763) (by norm_num)
theorem B311789 : Blo 119786 311789 := bbase (se 3 (by rfl) ⟨58460, by rfl⟩ : syracuseStep 311789 = 116921) (by norm_num)
theorem B180725 : Blo 119786 180725 := bbase (se 5 (by rfl) ⟨8471, by rfl⟩ : syracuseStep 180725 = 16943) (by norm_num)
theorem B180749 : Blo 119786 180749 := bbase (se 3 (by rfl) ⟨33890, by rfl⟩ : syracuseStep 180749 = 67781) (by norm_num)
theorem B180773 : Blo 119786 180773 := bbase (se 4 (by rfl) ⟨16947, by rfl⟩ : syracuseStep 180773 = 33895) (by norm_num)
theorem B180797 : Blo 119786 180797 := bbase (se 3 (by rfl) ⟨33899, by rfl⟩ : syracuseStep 180797 = 67799) (by norm_num)
theorem B180821 : Blo 119786 180821 := bbase (se 8 (by rfl) ⟨1059, by rfl⟩ : syracuseStep 180821 = 2119) (by norm_num)
theorem B180845 : Blo 119786 180845 := bbase (se 3 (by rfl) ⟨33908, by rfl⟩ : syracuseStep 180845 = 67817) (by norm_num)
theorem B180869 : Blo 119786 180869 := bbase (se 4 (by rfl) ⟨16956, by rfl⟩ : syracuseStep 180869 = 33913) (by norm_num)
theorem B180893 : Blo 119786 180893 := bbase (se 3 (by rfl) ⟨33917, by rfl⟩ : syracuseStep 180893 = 67835) (by norm_num)
theorem B279197 : Blo 119786 279197 := bbase (se 3 (by rfl) ⟨52349, by rfl⟩ : syracuseStep 279197 = 104699) (by norm_num)
theorem B180917 : Blo 119786 180917 := bbase (se 5 (by rfl) ⟨8480, by rfl⟩ : syracuseStep 180917 = 16961) (by norm_num)
theorem B410309 : Blo 119786 410309 := bbase (se 4 (by rfl) ⟨38466, by rfl⟩ : syracuseStep 410309 = 76933) (by norm_num)
theorem B180941 : Blo 119786 180941 := bbase (se 3 (by rfl) ⟨33926, by rfl⟩ : syracuseStep 180941 = 67853) (by norm_num)
theorem B180965 : Blo 119786 180965 := bbase (se 4 (by rfl) ⟨16965, by rfl⟩ : syracuseStep 180965 = 33931) (by norm_num)
theorem B180989 : Blo 119786 180989 := bbase (se 3 (by rfl) ⟨33935, by rfl⟩ : syracuseStep 180989 = 67871) (by norm_num)
theorem B181013 : Blo 119786 181013 := bbase (se 6 (by rfl) ⟨4242, by rfl⟩ : syracuseStep 181013 = 8485) (by norm_num)
theorem B607013 : Blo 119786 607013 := bbase (se 4 (by rfl) ⟨56907, by rfl⟩ : syracuseStep 607013 = 113815) (by norm_num)
theorem B181037 : Blo 119786 181037 := bbase (se 3 (by rfl) ⟨33944, by rfl⟩ : syracuseStep 181037 = 67889) (by norm_num)
theorem B181061 : Blo 119786 181061 := bbase (se 4 (by rfl) ⟨16974, by rfl⟩ : syracuseStep 181061 = 33949) (by norm_num)
theorem B312133 : Blo 119786 312133 := bbase (se 4 (by rfl) ⟨29262, by rfl⟩ : syracuseStep 312133 = 58525) (by norm_num)
theorem B410453 : Blo 119786 410453 := bbase (se 9 (by rfl) ⟨1202, by rfl⟩ : syracuseStep 410453 = 2405) (by norm_num)
theorem B181085 : Blo 119786 181085 := bbase (se 3 (by rfl) ⟨33953, by rfl⟩ : syracuseStep 181085 = 67907) (by norm_num)
theorem B181109 : Blo 119786 181109 := bbase (se 5 (by rfl) ⟨8489, by rfl⟩ : syracuseStep 181109 = 16979) (by norm_num)
theorem B148349 : Blo 119786 148349 := bbase (se 3 (by rfl) ⟨27815, by rfl⟩ : syracuseStep 148349 = 55631) (by norm_num)
theorem B181133 : Blo 119786 181133 := bbase (se 3 (by rfl) ⟨33962, by rfl⟩ : syracuseStep 181133 = 67925) (by norm_num)
theorem B181157 : Blo 119786 181157 := bbase (se 4 (by rfl) ⟨16983, by rfl⟩ : syracuseStep 181157 = 33967) (by norm_num)
theorem B312245 : Blo 119786 312245 := bbase (se 5 (by rfl) ⟨14636, by rfl⟩ : syracuseStep 312245 = 29273) (by norm_num)
theorem B181181 : Blo 119786 181181 := bbase (se 3 (by rfl) ⟨33971, by rfl⟩ : syracuseStep 181181 = 67943) (by norm_num)
theorem B181205 : Blo 119786 181205 := bbase (se 7 (by rfl) ⟨2123, by rfl⟩ : syracuseStep 181205 = 4247) (by norm_num)
theorem B181229 : Blo 119786 181229 := bbase (se 3 (by rfl) ⟨33980, by rfl⟩ : syracuseStep 181229 = 67961) (by norm_num)
theorem B181253 : Blo 119786 181253 := bbase (se 4 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 181253 = 33985) (by norm_num)
theorem B181277 : Blo 119786 181277 := bbase (se 3 (by rfl) ⟨33989, by rfl⟩ : syracuseStep 181277 = 67979) (by norm_num)
theorem B181301 : Blo 119786 181301 := bbase (se 5 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 181301 = 16997) (by norm_num)
theorem B181325 : Blo 119786 181325 := bbase (se 3 (by rfl) ⟨33998, by rfl⟩ : syracuseStep 181325 = 67997) (by norm_num)
theorem B181349 : Blo 119786 181349 := bbase (se 4 (by rfl) ⟨17001, by rfl⟩ : syracuseStep 181349 = 34003) (by norm_num)
theorem B312437 : Blo 119786 312437 := bbase (se 5 (by rfl) ⟨14645, by rfl⟩ : syracuseStep 312437 = 29291) (by norm_num)
theorem B181373 : Blo 119786 181373 := bbase (se 3 (by rfl) ⟨34007, by rfl⟩ : syracuseStep 181373 = 68015) (by norm_num)
theorem B181397 : Blo 119786 181397 := bbase (se 6 (by rfl) ⟨4251, by rfl⟩ : syracuseStep 181397 = 8503) (by norm_num)
theorem B181421 : Blo 119786 181421 := bbase (se 3 (by rfl) ⟨34016, by rfl⟩ : syracuseStep 181421 = 68033) (by norm_num)
theorem B148657 : Blo 119786 148657 := bbase (se 2 (by rfl) ⟨55746, by rfl⟩ : syracuseStep 148657 = 111493) (by norm_num)
theorem B279733 : Blo 119786 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B181445 : Blo 119786 181445 := bbase (se 4 (by rfl) ⟨17010, by rfl⟩ : syracuseStep 181445 = 34021) (by norm_num)
theorem B181469 : Blo 119786 181469 := bbase (se 3 (by rfl) ⟨34025, by rfl⟩ : syracuseStep 181469 = 68051) (by norm_num)
theorem B181493 : Blo 119786 181493 := bbase (se 5 (by rfl) ⟨8507, by rfl⟩ : syracuseStep 181493 = 17015) (by norm_num)
theorem B410885 : Blo 119786 410885 := bbase (se 4 (by rfl) ⟨38520, by rfl⟩ : syracuseStep 410885 = 77041) (by norm_num)
theorem B181517 : Blo 119786 181517 := bbase (se 3 (by rfl) ⟨34034, by rfl⟩ : syracuseStep 181517 = 68069) (by norm_num)
theorem B181541 : Blo 119786 181541 := bbase (se 4 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 181541 = 34039) (by norm_num)
theorem B181565 : Blo 119786 181565 := bbase (se 3 (by rfl) ⟨34043, by rfl⟩ : syracuseStep 181565 = 68087) (by norm_num)
theorem B181589 : Blo 119786 181589 := bbase (se 12 (by rfl) ⟨66, by rfl⟩ : syracuseStep 181589 = 133) (by norm_num)
theorem B181613 : Blo 119786 181613 := bbase (se 3 (by rfl) ⟨34052, by rfl⟩ : syracuseStep 181613 = 68105) (by norm_num)
theorem B181637 : Blo 119786 181637 := bbase (se 4 (by rfl) ⟨17028, by rfl⟩ : syracuseStep 181637 = 34057) (by norm_num)
theorem B181661 : Blo 119786 181661 := bbase (se 3 (by rfl) ⟨34061, by rfl⟩ : syracuseStep 181661 = 68123) (by norm_num)
theorem B181685 : Blo 119786 181685 := bbase (se 5 (by rfl) ⟨8516, by rfl⟩ : syracuseStep 181685 = 17033) (by norm_num)
theorem B181709 : Blo 119786 181709 := bbase (se 3 (by rfl) ⟨34070, by rfl⟩ : syracuseStep 181709 = 68141) (by norm_num)
theorem B312781 : Blo 119786 312781 := bbase (se 3 (by rfl) ⟨58646, by rfl⟩ : syracuseStep 312781 = 117293) (by norm_num)
theorem B181733 : Blo 119786 181733 := bbase (se 4 (by rfl) ⟨17037, by rfl⟩ : syracuseStep 181733 = 34075) (by norm_num)
theorem B443893 : Blo 119786 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B181757 : Blo 119786 181757 := bbase (se 3 (by rfl) ⟨34079, by rfl⟩ : syracuseStep 181757 = 68159) (by norm_num)
theorem B181781 : Blo 119786 181781 := bbase (se 6 (by rfl) ⟨4260, by rfl⟩ : syracuseStep 181781 = 8521) (by norm_num)
theorem B345637 : Blo 119786 345637 := bbase (se 4 (by rfl) ⟨32403, by rfl⟩ : syracuseStep 345637 = 64807) (by norm_num)
theorem B181805 : Blo 119786 181805 := bbase (se 3 (by rfl) ⟨34088, by rfl⟩ : syracuseStep 181805 = 68177) (by norm_num)
theorem B312893 : Blo 119786 312893 := bbase (se 3 (by rfl) ⟨58667, by rfl⟩ : syracuseStep 312893 = 117335) (by norm_num)
theorem B181829 : Blo 119786 181829 := bbase (se 4 (by rfl) ⟨17046, by rfl⟩ : syracuseStep 181829 = 34093) (by norm_num)
theorem B181853 : Blo 119786 181853 := bbase (se 3 (by rfl) ⟨34097, by rfl⟩ : syracuseStep 181853 = 68195) (by norm_num)
theorem B181877 : Blo 119786 181877 := bbase (se 5 (by rfl) ⟨8525, by rfl⟩ : syracuseStep 181877 = 17051) (by norm_num)
theorem B181901 : Blo 119786 181901 := bbase (se 3 (by rfl) ⟨34106, by rfl⟩ : syracuseStep 181901 = 68213) (by norm_num)
theorem B181925 : Blo 119786 181925 := bbase (se 4 (by rfl) ⟨17055, by rfl⟩ : syracuseStep 181925 = 34111) (by norm_num)
theorem B411317 : Blo 119786 411317 := bbase (se 5 (by rfl) ⟨19280, by rfl⟩ : syracuseStep 411317 = 38561) (by norm_num)
theorem B181949 : Blo 119786 181949 := bbase (se 3 (by rfl) ⟨34115, by rfl⟩ : syracuseStep 181949 = 68231) (by norm_num)
theorem B181973 : Blo 119786 181973 := bbase (se 7 (by rfl) ⟨2132, by rfl⟩ : syracuseStep 181973 = 4265) (by norm_num)
theorem B181997 : Blo 119786 181997 := bbase (se 3 (by rfl) ⟨34124, by rfl⟩ : syracuseStep 181997 = 68249) (by norm_num)
theorem B313085 : Blo 119786 313085 := bbase (se 3 (by rfl) ⟨58703, by rfl⟩ : syracuseStep 313085 = 117407) (by norm_num)
theorem B182021 : Blo 119786 182021 := bbase (se 4 (by rfl) ⟨17064, by rfl⟩ : syracuseStep 182021 = 34129) (by norm_num)
theorem B182045 : Blo 119786 182045 := bbase (se 3 (by rfl) ⟨34133, by rfl⟩ : syracuseStep 182045 = 68267) (by norm_num)
theorem B182069 : Blo 119786 182069 := bbase (se 5 (by rfl) ⟨8534, by rfl⟩ : syracuseStep 182069 = 17069) (by norm_num)
theorem B182093 : Blo 119786 182093 := bbase (se 3 (by rfl) ⟨34142, by rfl⟩ : syracuseStep 182093 = 68285) (by norm_num)
theorem B182117 : Blo 119786 182117 := bbase (se 4 (by rfl) ⟨17073, by rfl⟩ : syracuseStep 182117 = 34147) (by norm_num)
theorem B182141 : Blo 119786 182141 := bbase (se 3 (by rfl) ⟨34151, by rfl⟩ : syracuseStep 182141 = 68303) (by norm_num)
theorem B182165 : Blo 119786 182165 := bbase (se 6 (by rfl) ⟨4269, by rfl⟩ : syracuseStep 182165 = 8539) (by norm_num)
theorem B182189 : Blo 119786 182189 := bbase (se 3 (by rfl) ⟨34160, by rfl⟩ : syracuseStep 182189 = 68321) (by norm_num)
theorem B182213 : Blo 119786 182213 := bbase (se 4 (by rfl) ⟨17082, by rfl⟩ : syracuseStep 182213 = 34165) (by norm_num)
theorem B182237 : Blo 119786 182237 := bbase (se 3 (by rfl) ⟨34169, by rfl⟩ : syracuseStep 182237 = 68339) (by norm_num)
theorem B182261 : Blo 119786 182261 := bbase (se 5 (by rfl) ⟨8543, by rfl⟩ : syracuseStep 182261 = 17087) (by norm_num)
theorem B182285 : Blo 119786 182285 := bbase (se 3 (by rfl) ⟨34178, by rfl⟩ : syracuseStep 182285 = 68357) (by norm_num)
theorem B182309 : Blo 119786 182309 := bbase (se 4 (by rfl) ⟨17091, by rfl⟩ : syracuseStep 182309 = 34183) (by norm_num)
theorem B608309 : Blo 119786 608309 := bbase (se 5 (by rfl) ⟨28514, by rfl⟩ : syracuseStep 608309 = 57029) (by norm_num)
theorem B182333 : Blo 119786 182333 := bbase (se 3 (by rfl) ⟨34187, by rfl⟩ : syracuseStep 182333 = 68375) (by norm_num)
theorem B280637 : Blo 119786 280637 := bbase (se 3 (by rfl) ⟨52619, by rfl⟩ : syracuseStep 280637 = 105239) (by norm_num)
theorem B182357 : Blo 119786 182357 := bbase (se 8 (by rfl) ⟨1068, by rfl⟩ : syracuseStep 182357 = 2137) (by norm_num)
theorem B411749 : Blo 119786 411749 := bbase (se 4 (by rfl) ⟨38601, by rfl⟩ : syracuseStep 411749 = 77203) (by norm_num)
theorem B182381 : Blo 119786 182381 := bbase (se 3 (by rfl) ⟨34196, by rfl⟩ : syracuseStep 182381 = 68393) (by norm_num)
theorem B182405 : Blo 119786 182405 := bbase (se 4 (by rfl) ⟨17100, by rfl⟩ : syracuseStep 182405 = 34201) (by norm_num)
theorem B182429 : Blo 119786 182429 := bbase (se 3 (by rfl) ⟨34205, by rfl⟩ : syracuseStep 182429 = 68411) (by norm_num)
theorem B182453 : Blo 119786 182453 := bbase (se 5 (by rfl) ⟨8552, by rfl⟩ : syracuseStep 182453 = 17105) (by norm_num)
theorem B182477 : Blo 119786 182477 := bbase (se 3 (by rfl) ⟨34214, by rfl⟩ : syracuseStep 182477 = 68429) (by norm_num)
theorem B444629 : Blo 119786 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B182501 : Blo 119786 182501 := bbase (se 4 (by rfl) ⟨17109, by rfl⟩ : syracuseStep 182501 = 34219) (by norm_num)
theorem B182525 : Blo 119786 182525 := bbase (se 3 (by rfl) ⟨34223, by rfl⟩ : syracuseStep 182525 = 68447) (by norm_num)
theorem B182549 : Blo 119786 182549 := bbase (se 6 (by rfl) ⟨4278, by rfl⟩ : syracuseStep 182549 = 8557) (by norm_num)
theorem B182573 : Blo 119786 182573 := bbase (se 3 (by rfl) ⟨34232, by rfl⟩ : syracuseStep 182573 = 68465) (by norm_num)
theorem B182597 : Blo 119786 182597 := bbase (se 4 (by rfl) ⟨17118, by rfl⟩ : syracuseStep 182597 = 34237) (by norm_num)
theorem B248141 : Blo 119786 248141 := bbase (se 3 (by rfl) ⟨46526, by rfl⟩ : syracuseStep 248141 = 93053) (by norm_num)
theorem B182621 : Blo 119786 182621 := bbase (se 3 (by rfl) ⟨34241, by rfl⟩ : syracuseStep 182621 = 68483) (by norm_num)
theorem B182645 : Blo 119786 182645 := bbase (se 5 (by rfl) ⟨8561, by rfl⟩ : syracuseStep 182645 = 17123) (by norm_num)
theorem B182669 : Blo 119786 182669 := bbase (se 3 (by rfl) ⟨34250, by rfl⟩ : syracuseStep 182669 = 68501) (by norm_num)
theorem B182693 : Blo 119786 182693 := bbase (se 4 (by rfl) ⟨17127, by rfl⟩ : syracuseStep 182693 = 34255) (by norm_num)
theorem B182717 : Blo 119786 182717 := bbase (se 3 (by rfl) ⟨34259, by rfl⟩ : syracuseStep 182717 = 68519) (by norm_num)
theorem B182741 : Blo 119786 182741 := bbase (se 7 (by rfl) ⟨2141, by rfl⟩ : syracuseStep 182741 = 4283) (by norm_num)
theorem B182749 : Blo 119786 182749 := bbase (se 3 (by rfl) ⟨34265, by rfl⟩ : syracuseStep 182749 = 68531) (by norm_num)
theorem B182765 : Blo 119786 182765 := bbase (se 3 (by rfl) ⟨34268, by rfl⟩ : syracuseStep 182765 = 68537) (by norm_num)
theorem B182789 : Blo 119786 182789 := bbase (se 4 (by rfl) ⟨17136, by rfl⟩ : syracuseStep 182789 = 34273) (by norm_num)
theorem B412181 : Blo 119786 412181 := bbase (se 6 (by rfl) ⟨9660, by rfl⟩ : syracuseStep 412181 = 19321) (by norm_num)
theorem B182813 : Blo 119786 182813 := bbase (se 3 (by rfl) ⟨34277, by rfl⟩ : syracuseStep 182813 = 68555) (by norm_num)
theorem B182837 : Blo 119786 182837 := bbase (se 5 (by rfl) ⟨8570, by rfl⟩ : syracuseStep 182837 = 17141) (by norm_num)
theorem B182861 : Blo 119786 182861 := bbase (se 3 (by rfl) ⟨34286, by rfl⟩ : syracuseStep 182861 = 68573) (by norm_num)
theorem B182885 : Blo 119786 182885 := bbase (se 4 (by rfl) ⟨17145, by rfl⟩ : syracuseStep 182885 = 34291) (by norm_num)
theorem B182909 : Blo 119786 182909 := bbase (se 3 (by rfl) ⟨34295, by rfl⟩ : syracuseStep 182909 = 68591) (by norm_num)
theorem B182933 : Blo 119786 182933 := bbase (se 6 (by rfl) ⟨4287, by rfl⟩ : syracuseStep 182933 = 8575) (by norm_num)
theorem B182957 : Blo 119786 182957 := bbase (se 3 (by rfl) ⟨34304, by rfl⟩ : syracuseStep 182957 = 68609) (by norm_num)
theorem B182981 : Blo 119786 182981 := bbase (se 4 (by rfl) ⟨17154, by rfl⟩ : syracuseStep 182981 = 34309) (by norm_num)
theorem B183005 : Blo 119786 183005 := bbase (se 3 (by rfl) ⟨34313, by rfl⟩ : syracuseStep 183005 = 68627) (by norm_num)
theorem B576229 : Blo 119786 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B183029 : Blo 119786 183029 := bbase (se 5 (by rfl) ⟨8579, by rfl⟩ : syracuseStep 183029 = 17159) (by norm_num)
theorem B183053 : Blo 119786 183053 := bbase (se 3 (by rfl) ⟨34322, by rfl⟩ : syracuseStep 183053 = 68645) (by norm_num)
theorem B183077 : Blo 119786 183077 := bbase (se 4 (by rfl) ⟨17163, by rfl⟩ : syracuseStep 183077 = 34327) (by norm_num)
theorem B183101 : Blo 119786 183101 := bbase (se 3 (by rfl) ⟨34331, by rfl⟩ : syracuseStep 183101 = 68663) (by norm_num)
theorem B183125 : Blo 119786 183125 := bbase (se 9 (by rfl) ⟨536, by rfl⟩ : syracuseStep 183125 = 1073) (by norm_num)
theorem B183149 : Blo 119786 183149 := bbase (se 3 (by rfl) ⟨34340, by rfl⟩ : syracuseStep 183149 = 68681) (by norm_num)
theorem B183173 : Blo 119786 183173 := bbase (se 4 (by rfl) ⟨17172, by rfl⟩ : syracuseStep 183173 = 34345) (by norm_num)
theorem B183197 : Blo 119786 183197 := bbase (se 3 (by rfl) ⟨34349, by rfl⟩ : syracuseStep 183197 = 68699) (by norm_num)
theorem B183221 : Blo 119786 183221 := bbase (se 5 (by rfl) ⟨8588, by rfl⟩ : syracuseStep 183221 = 17177) (by norm_num)
theorem B412613 : Blo 119786 412613 := bbase (se 4 (by rfl) ⟨38682, by rfl⟩ : syracuseStep 412613 = 77365) (by norm_num)
theorem B183245 : Blo 119786 183245 := bbase (se 3 (by rfl) ⟨34358, by rfl⟩ : syracuseStep 183245 = 68717) (by norm_num)
theorem B183269 : Blo 119786 183269 := bbase (se 4 (by rfl) ⟨17181, by rfl⟩ : syracuseStep 183269 = 34363) (by norm_num)
theorem B183293 : Blo 119786 183293 := bbase (se 3 (by rfl) ⟨34367, by rfl⟩ : syracuseStep 183293 = 68735) (by norm_num)
theorem B347141 : Blo 119786 347141 := bbase (se 4 (by rfl) ⟨32544, by rfl⟩ : syracuseStep 347141 = 65089) (by norm_num)
theorem B1559573 : Blo 119786 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B183317 : Blo 119786 183317 := bbase (se 6 (by rfl) ⟨4296, by rfl⟩ : syracuseStep 183317 = 8593) (by norm_num)
theorem B216101 : Blo 119786 216101 := bbase (se 4 (by rfl) ⟨20259, by rfl⟩ : syracuseStep 216101 = 40519) (by norm_num)
theorem B183341 : Blo 119786 183341 := bbase (se 3 (by rfl) ⟨34376, by rfl⟩ : syracuseStep 183341 = 68753) (by norm_num)
theorem B183365 : Blo 119786 183365 := bbase (se 4 (by rfl) ⟨17190, by rfl⟩ : syracuseStep 183365 = 34381) (by norm_num)
theorem B183389 : Blo 119786 183389 := bbase (se 3 (by rfl) ⟨34385, by rfl⟩ : syracuseStep 183389 = 68771) (by norm_num)
theorem B183413 : Blo 119786 183413 := bbase (se 5 (by rfl) ⟨8597, by rfl⟩ : syracuseStep 183413 = 17195) (by norm_num)
theorem B183437 : Blo 119786 183437 := bbase (se 3 (by rfl) ⟨34394, by rfl⟩ : syracuseStep 183437 = 68789) (by norm_num)
theorem B183461 : Blo 119786 183461 := bbase (se 4 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 183461 = 34399) (by norm_num)
theorem B216245 : Blo 119786 216245 := bbase (se 5 (by rfl) ⟨10136, by rfl⟩ : syracuseStep 216245 = 20273) (by norm_num)
theorem B183485 : Blo 119786 183485 := bbase (se 3 (by rfl) ⟨34403, by rfl⟩ : syracuseStep 183485 = 68807) (by norm_num)
theorem B183509 : Blo 119786 183509 := bbase (se 7 (by rfl) ⟨2150, by rfl⟩ : syracuseStep 183509 = 4301) (by norm_num)
theorem B183533 : Blo 119786 183533 := bbase (se 3 (by rfl) ⟨34412, by rfl⟩ : syracuseStep 183533 = 68825) (by norm_num)
theorem B347381 : Blo 119786 347381 := bbase (se 5 (by rfl) ⟨16283, by rfl⟩ : syracuseStep 347381 = 32567) (by norm_num)
theorem B216317 : Blo 119786 216317 := bbase (se 3 (by rfl) ⟨40559, by rfl⟩ : syracuseStep 216317 = 81119) (by norm_num)
theorem B314621 : Blo 119786 314621 := bbase (se 3 (by rfl) ⟨58991, by rfl⟩ : syracuseStep 314621 = 117983) (by norm_num)
theorem B183557 : Blo 119786 183557 := bbase (se 4 (by rfl) ⟨17208, by rfl⟩ : syracuseStep 183557 = 34417) (by norm_num)
theorem B183581 : Blo 119786 183581 := bbase (se 3 (by rfl) ⟨34421, by rfl⟩ : syracuseStep 183581 = 68843) (by norm_num)
theorem B183605 : Blo 119786 183605 := bbase (se 5 (by rfl) ⟨8606, by rfl⟩ : syracuseStep 183605 = 17213) (by norm_num)
theorem B609605 : Blo 119786 609605 := bbase (se 4 (by rfl) ⟨57150, by rfl⟩ : syracuseStep 609605 = 114301) (by norm_num)
theorem B183629 : Blo 119786 183629 := bbase (se 3 (by rfl) ⟨34430, by rfl⟩ : syracuseStep 183629 = 68861) (by norm_num)
theorem B183653 : Blo 119786 183653 := bbase (se 4 (by rfl) ⟨17217, by rfl⟩ : syracuseStep 183653 = 34435) (by norm_num)
theorem B413045 : Blo 119786 413045 := bbase (se 5 (by rfl) ⟨19361, by rfl⟩ : syracuseStep 413045 = 38723) (by norm_num)
theorem B183677 : Blo 119786 183677 := bbase (se 3 (by rfl) ⟨34439, by rfl⟩ : syracuseStep 183677 = 68879) (by norm_num)
theorem B183701 : Blo 119786 183701 := bbase (se 6 (by rfl) ⟨4305, by rfl⟩ : syracuseStep 183701 = 8611) (by norm_num)
theorem B183725 : Blo 119786 183725 := bbase (se 3 (by rfl) ⟨34448, by rfl⟩ : syracuseStep 183725 = 68897) (by norm_num)
theorem B183749 : Blo 119786 183749 := bbase (se 4 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 183749 = 34453) (by norm_num)
theorem B249293 : Blo 119786 249293 := bbase (se 3 (by rfl) ⟨46742, by rfl⟩ : syracuseStep 249293 = 93485) (by norm_num)
theorem B249301 : Blo 119786 249301 := bbase (se 7 (by rfl) ⟨2921, by rfl⟩ : syracuseStep 249301 = 5843) (by norm_num)
theorem B183773 : Blo 119786 183773 := bbase (se 3 (by rfl) ⟨34457, by rfl⟩ : syracuseStep 183773 = 68915) (by norm_num)
theorem B183797 : Blo 119786 183797 := bbase (se 5 (by rfl) ⟨8615, by rfl⟩ : syracuseStep 183797 = 17231) (by norm_num)
theorem B183821 : Blo 119786 183821 := bbase (se 3 (by rfl) ⟨34466, by rfl⟩ : syracuseStep 183821 = 68933) (by norm_num)
theorem B937493 : Blo 119786 937493 := bbase (se 6 (by rfl) ⟨21972, by rfl⟩ : syracuseStep 937493 = 43945) (by norm_num)
theorem B183845 : Blo 119786 183845 := bbase (se 4 (by rfl) ⟨17235, by rfl⟩ : syracuseStep 183845 = 34471) (by norm_num)
theorem B183869 : Blo 119786 183869 := bbase (se 3 (by rfl) ⟨34475, by rfl⟩ : syracuseStep 183869 = 68951) (by norm_num)
theorem B183893 : Blo 119786 183893 := bbase (se 8 (by rfl) ⟨1077, by rfl⟩ : syracuseStep 183893 = 2155) (by norm_num)
theorem B183917 : Blo 119786 183917 := bbase (se 3 (by rfl) ⟨34484, by rfl⟩ : syracuseStep 183917 = 68969) (by norm_num)
theorem B183941 : Blo 119786 183941 := bbase (se 4 (by rfl) ⟨17244, by rfl⟩ : syracuseStep 183941 = 34489) (by norm_num)
theorem B183965 : Blo 119786 183965 := bbase (se 3 (by rfl) ⟨34493, by rfl⟩ : syracuseStep 183965 = 68987) (by norm_num)
theorem B183989 : Blo 119786 183989 := bbase (se 5 (by rfl) ⟨8624, by rfl⟩ : syracuseStep 183989 = 17249) (by norm_num)
theorem B184013 : Blo 119786 184013 := bbase (se 3 (by rfl) ⟨34502, by rfl⟩ : syracuseStep 184013 = 69005) (by norm_num)
theorem B184037 : Blo 119786 184037 := bbase (se 4 (by rfl) ⟨17253, by rfl⟩ : syracuseStep 184037 = 34507) (by norm_num)
theorem B216821 : Blo 119786 216821 := bbase (se 5 (by rfl) ⟨10163, by rfl⟩ : syracuseStep 216821 = 20327) (by norm_num)
theorem B184061 : Blo 119786 184061 := bbase (se 3 (by rfl) ⟨34511, by rfl⟩ : syracuseStep 184061 = 69023) (by norm_num)
theorem B184085 : Blo 119786 184085 := bbase (se 6 (by rfl) ⟨4314, by rfl⟩ : syracuseStep 184085 = 8629) (by norm_num)
theorem B413477 : Blo 119786 413477 := bbase (se 4 (by rfl) ⟨38763, by rfl⟩ : syracuseStep 413477 = 77527) (by norm_num)
theorem B184109 : Blo 119786 184109 := bbase (se 3 (by rfl) ⟨34520, by rfl⟩ : syracuseStep 184109 = 69041) (by norm_num)
theorem B184133 : Blo 119786 184133 := bbase (se 4 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 184133 = 34525) (by norm_num)
theorem B5820245 : Blo 119786 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B184157 : Blo 119786 184157 := bbase (se 3 (by rfl) ⟨34529, by rfl⟩ : syracuseStep 184157 = 69059) (by norm_num)
theorem B184181 : Blo 119786 184181 := bbase (se 5 (by rfl) ⟨8633, by rfl⟩ : syracuseStep 184181 = 17267) (by norm_num)
theorem B184205 : Blo 119786 184205 := bbase (se 3 (by rfl) ⟨34538, by rfl⟩ : syracuseStep 184205 = 69077) (by norm_num)
theorem B184229 : Blo 119786 184229 := bbase (se 4 (by rfl) ⟨17271, by rfl⟩ : syracuseStep 184229 = 34543) (by norm_num)
theorem B184253 : Blo 119786 184253 := bbase (se 3 (by rfl) ⟨34547, by rfl⟩ : syracuseStep 184253 = 69095) (by norm_num)
theorem B184277 : Blo 119786 184277 := bbase (se 7 (by rfl) ⟨2159, by rfl⟩ : syracuseStep 184277 = 4319) (by norm_num)
theorem B184301 : Blo 119786 184301 := bbase (se 3 (by rfl) ⟨34556, by rfl⟩ : syracuseStep 184301 = 69113) (by norm_num)
theorem B184325 : Blo 119786 184325 := bbase (se 4 (by rfl) ⟨17280, by rfl⟩ : syracuseStep 184325 = 34561) (by norm_num)
theorem B184349 : Blo 119786 184349 := bbase (se 3 (by rfl) ⟨34565, by rfl⟩ : syracuseStep 184349 = 69131) (by norm_num)
theorem B184373 : Blo 119786 184373 := bbase (se 5 (by rfl) ⟨8642, by rfl⟩ : syracuseStep 184373 = 17285) (by norm_num)
theorem B184397 : Blo 119786 184397 := bbase (se 3 (by rfl) ⟨34574, by rfl⟩ : syracuseStep 184397 = 69149) (by norm_num)
theorem B184421 : Blo 119786 184421 := bbase (se 4 (by rfl) ⟨17289, by rfl⟩ : syracuseStep 184421 = 34579) (by norm_num)
theorem B184445 : Blo 119786 184445 := bbase (se 3 (by rfl) ⟨34583, by rfl⟩ : syracuseStep 184445 = 69167) (by norm_num)
theorem B184469 : Blo 119786 184469 := bbase (se 6 (by rfl) ⟨4323, by rfl⟩ : syracuseStep 184469 = 8647) (by norm_num)
theorem B184493 : Blo 119786 184493 := bbase (se 3 (by rfl) ⟨34592, by rfl⟩ : syracuseStep 184493 = 69185) (by norm_num)
theorem B151733 : Blo 119786 151733 := bbase (se 5 (by rfl) ⟨7112, by rfl⟩ : syracuseStep 151733 = 14225) (by norm_num)
theorem B184517 : Blo 119786 184517 := bbase (se 4 (by rfl) ⟨17298, by rfl⟩ : syracuseStep 184517 = 34597) (by norm_num)
theorem B413909 : Blo 119786 413909 := bbase (se 7 (by rfl) ⟨4850, by rfl⟩ : syracuseStep 413909 = 9701) (by norm_num)
theorem B184541 : Blo 119786 184541 := bbase (se 3 (by rfl) ⟨34601, by rfl⟩ : syracuseStep 184541 = 69203) (by norm_num)
theorem B151789 : Blo 119786 151789 := bbase (se 3 (by rfl) ⟨28460, by rfl⟩ : syracuseStep 151789 = 56921) (by norm_num)
theorem B184565 : Blo 119786 184565 := bbase (se 5 (by rfl) ⟨8651, by rfl⟩ : syracuseStep 184565 = 17303) (by norm_num)
theorem B184589 : Blo 119786 184589 := bbase (se 3 (by rfl) ⟨34610, by rfl⟩ : syracuseStep 184589 = 69221) (by norm_num)
theorem B184613 : Blo 119786 184613 := bbase (se 4 (by rfl) ⟨17307, by rfl⟩ : syracuseStep 184613 = 34615) (by norm_num)
theorem B184637 : Blo 119786 184637 := bbase (se 3 (by rfl) ⟨34619, by rfl⟩ : syracuseStep 184637 = 69239) (by norm_num)
theorem B151885 : Blo 119786 151885 := bbase (se 3 (by rfl) ⟨28478, by rfl⟩ : syracuseStep 151885 = 56957) (by norm_num)
theorem B184661 : Blo 119786 184661 := bbase (se 10 (by rfl) ⟨270, by rfl⟩ : syracuseStep 184661 = 541) (by norm_num)
theorem B184685 : Blo 119786 184685 := bbase (se 3 (by rfl) ⟨34628, by rfl⟩ : syracuseStep 184685 = 69257) (by norm_num)
theorem B184709 : Blo 119786 184709 := bbase (se 4 (by rfl) ⟨17316, by rfl⟩ : syracuseStep 184709 = 34633) (by norm_num)
theorem B184733 : Blo 119786 184733 := bbase (se 3 (by rfl) ⟨34637, by rfl⟩ : syracuseStep 184733 = 69275) (by norm_num)
theorem B184757 : Blo 119786 184757 := bbase (se 5 (by rfl) ⟨8660, by rfl⟩ : syracuseStep 184757 = 17321) (by norm_num)
theorem B184781 : Blo 119786 184781 := bbase (se 3 (by rfl) ⟨34646, by rfl⟩ : syracuseStep 184781 = 69293) (by norm_num)
theorem B184805 : Blo 119786 184805 := bbase (se 4 (by rfl) ⟨17325, by rfl⟩ : syracuseStep 184805 = 34651) (by norm_num)
theorem B152057 : Blo 119786 152057 := bbase (se 2 (by rfl) ⟨57021, by rfl⟩ : syracuseStep 152057 = 114043) (by norm_num)
theorem B184829 : Blo 119786 184829 := bbase (se 3 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 184829 = 69311) (by norm_num)
theorem B184853 : Blo 119786 184853 := bbase (se 6 (by rfl) ⟨4332, by rfl⟩ : syracuseStep 184853 = 8665) (by norm_num)
theorem B184877 : Blo 119786 184877 := bbase (se 3 (by rfl) ⟨34664, by rfl⟩ : syracuseStep 184877 = 69329) (by norm_num)
theorem B152113 : Blo 119786 152113 := bbase (se 2 (by rfl) ⟨57042, by rfl⟩ : syracuseStep 152113 = 114085) (by norm_num)
theorem B348725 : Blo 119786 348725 := bbase (se 5 (by rfl) ⟨16346, by rfl⟩ : syracuseStep 348725 = 32693) (by norm_num)
theorem B184901 : Blo 119786 184901 := bbase (se 4 (by rfl) ⟨17334, by rfl⟩ : syracuseStep 184901 = 34669) (by norm_num)
theorem B610901 : Blo 119786 610901 := bbase (se 8 (by rfl) ⟨3579, by rfl⟩ : syracuseStep 610901 = 7159) (by norm_num)
theorem B184925 : Blo 119786 184925 := bbase (se 3 (by rfl) ⟨34673, by rfl⟩ : syracuseStep 184925 = 69347) (by norm_num)
theorem B250469 : Blo 119786 250469 := bbase (se 4 (by rfl) ⟨23481, by rfl⟩ : syracuseStep 250469 = 46963) (by norm_num)
theorem B184949 : Blo 119786 184949 := bbase (se 5 (by rfl) ⟨8669, by rfl⟩ : syracuseStep 184949 = 17339) (by norm_num)
theorem B414341 : Blo 119786 414341 := bbase (se 4 (by rfl) ⟨38844, by rfl⟩ : syracuseStep 414341 = 77689) (by norm_num)
theorem B184973 : Blo 119786 184973 := bbase (se 3 (by rfl) ⟨34682, by rfl⟩ : syracuseStep 184973 = 69365) (by norm_num)
theorem B152209 : Blo 119786 152209 := bbase (se 2 (by rfl) ⟨57078, by rfl⟩ : syracuseStep 152209 = 114157) (by norm_num)
theorem B184997 : Blo 119786 184997 := bbase (se 4 (by rfl) ⟨17343, by rfl⟩ : syracuseStep 184997 = 34687) (by norm_num)
theorem B250541 : Blo 119786 250541 := bbase (se 3 (by rfl) ⟨46976, by rfl⟩ : syracuseStep 250541 = 93953) (by norm_num)
theorem B185021 : Blo 119786 185021 := bbase (se 3 (by rfl) ⟨34691, by rfl⟩ : syracuseStep 185021 = 69383) (by norm_num)
theorem B185045 : Blo 119786 185045 := bbase (se 7 (by rfl) ⟨2168, by rfl⟩ : syracuseStep 185045 = 4337) (by norm_num)
theorem B185069 : Blo 119786 185069 := bbase (se 3 (by rfl) ⟨34700, by rfl⟩ : syracuseStep 185069 = 69401) (by norm_num)
theorem B185093 : Blo 119786 185093 := bbase (se 4 (by rfl) ⟨17352, by rfl⟩ : syracuseStep 185093 = 34705) (by norm_num)
theorem B185117 : Blo 119786 185117 := bbase (se 3 (by rfl) ⟨34709, by rfl⟩ : syracuseStep 185117 = 69419) (by norm_num)
theorem B185141 : Blo 119786 185141 := bbase (se 5 (by rfl) ⟨8678, by rfl⟩ : syracuseStep 185141 = 17357) (by norm_num)
theorem B152381 : Blo 119786 152381 := bbase (se 3 (by rfl) ⟨28571, by rfl⟩ : syracuseStep 152381 = 57143) (by norm_num)
theorem B512837 : Blo 119786 512837 := bbase (se 4 (by rfl) ⟨48078, by rfl⟩ : syracuseStep 512837 = 96157) (by norm_num)
theorem B185165 : Blo 119786 185165 := bbase (se 3 (by rfl) ⟨34718, by rfl⟩ : syracuseStep 185165 = 69437) (by norm_num)
theorem B185189 : Blo 119786 185189 := bbase (se 4 (by rfl) ⟨17361, by rfl⟩ : syracuseStep 185189 = 34723) (by norm_num)
theorem B152437 : Blo 119786 152437 := bbase (se 5 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 152437 = 14291) (by norm_num)
theorem B185213 : Blo 119786 185213 := bbase (se 3 (by rfl) ⟨34727, by rfl⟩ : syracuseStep 185213 = 69455) (by norm_num)
theorem B185237 : Blo 119786 185237 := bbase (se 6 (by rfl) ⟨4341, by rfl⟩ : syracuseStep 185237 = 8683) (by norm_num)
theorem B185261 : Blo 119786 185261 := bbase (se 3 (by rfl) ⟨34736, by rfl⟩ : syracuseStep 185261 = 69473) (by norm_num)
theorem B250805 : Blo 119786 250805 := bbase (se 5 (by rfl) ⟨11756, by rfl⟩ : syracuseStep 250805 = 23513) (by norm_num)
theorem B185285 : Blo 119786 185285 := bbase (se 4 (by rfl) ⟨17370, by rfl⟩ : syracuseStep 185285 = 34741) (by norm_num)
theorem B152533 : Blo 119786 152533 := bbase (se 7 (by rfl) ⟨1787, by rfl⟩ : syracuseStep 152533 = 3575) (by norm_num)
theorem B185309 : Blo 119786 185309 := bbase (se 3 (by rfl) ⟨34745, by rfl⟩ : syracuseStep 185309 = 69491) (by norm_num)
theorem B185333 : Blo 119786 185333 := bbase (se 5 (by rfl) ⟨8687, by rfl⟩ : syracuseStep 185333 = 17375) (by norm_num)
theorem B185357 : Blo 119786 185357 := bbase (se 3 (by rfl) ⟨34754, by rfl⟩ : syracuseStep 185357 = 69509) (by norm_num)
theorem B185381 : Blo 119786 185381 := bbase (se 4 (by rfl) ⟨17379, by rfl⟩ : syracuseStep 185381 = 34759) (by norm_num)
theorem B414773 : Blo 119786 414773 := bbase (se 5 (by rfl) ⟨19442, by rfl⟩ : syracuseStep 414773 = 38885) (by norm_num)
theorem B185405 : Blo 119786 185405 := bbase (se 3 (by rfl) ⟨34763, by rfl⟩ : syracuseStep 185405 = 69527) (by norm_num)
theorem B185429 : Blo 119786 185429 := bbase (se 8 (by rfl) ⟨1086, by rfl⟩ : syracuseStep 185429 = 2173) (by norm_num)
theorem B185437 : Blo 119786 185437 := bbase (se 3 (by rfl) ⟨34769, by rfl⟩ : syracuseStep 185437 = 69539) (by norm_num)
theorem B513125 : Blo 119786 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B185453 : Blo 119786 185453 := bbase (se 3 (by rfl) ⟨34772, by rfl⟩ : syracuseStep 185453 = 69545) (by norm_num)
theorem B152705 : Blo 119786 152705 := bbase (se 2 (by rfl) ⟨57264, by rfl⟩ : syracuseStep 152705 = 114529) (by norm_num)
theorem B185477 : Blo 119786 185477 := bbase (se 4 (by rfl) ⟨17388, by rfl⟩ : syracuseStep 185477 = 34777) (by norm_num)
theorem B185501 : Blo 119786 185501 := bbase (se 3 (by rfl) ⟨34781, by rfl⟩ : syracuseStep 185501 = 69563) (by norm_num)
theorem B185525 : Blo 119786 185525 := bbase (se 5 (by rfl) ⟨8696, by rfl⟩ : syracuseStep 185525 = 17393) (by norm_num)
theorem B152761 : Blo 119786 152761 := bbase (se 2 (by rfl) ⟨57285, by rfl⟩ : syracuseStep 152761 = 114571) (by norm_num)
theorem B185549 : Blo 119786 185549 := bbase (se 3 (by rfl) ⟨34790, by rfl⟩ : syracuseStep 185549 = 69581) (by norm_num)
theorem B349397 : Blo 119786 349397 := bbase (se 7 (by rfl) ⟨4094, by rfl⟩ : syracuseStep 349397 = 8189) (by norm_num)
theorem B185573 : Blo 119786 185573 := bbase (se 4 (by rfl) ⟨17397, by rfl⟩ : syracuseStep 185573 = 34795) (by norm_num)
theorem B185597 : Blo 119786 185597 := bbase (se 3 (by rfl) ⟨34799, by rfl⟩ : syracuseStep 185597 = 69599) (by norm_num)
theorem B185621 : Blo 119786 185621 := bbase (se 6 (by rfl) ⟨4350, by rfl⟩ : syracuseStep 185621 = 8701) (by norm_num)
theorem B152857 : Blo 119786 152857 := bbase (se 2 (by rfl) ⟨57321, by rfl⟩ : syracuseStep 152857 = 114643) (by norm_num)
theorem B185645 : Blo 119786 185645 := bbase (se 3 (by rfl) ⟨34808, by rfl⟩ : syracuseStep 185645 = 69617) (by norm_num)
theorem B185669 : Blo 119786 185669 := bbase (se 4 (by rfl) ⟨17406, by rfl⟩ : syracuseStep 185669 = 34813) (by norm_num)
theorem B284077 : Blo 119786 284077 := bbase (se 3 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 284077 = 106529) (by norm_num)
theorem B153029 : Blo 119786 153029 := bbase (se 4 (by rfl) ⟨14346, by rfl⟩ : syracuseStep 153029 = 28693) (by norm_num)
theorem B415205 : Blo 119786 415205 := bbase (se 4 (by rfl) ⟨38925, by rfl⟩ : syracuseStep 415205 = 77851) (by norm_num)
theorem B153085 : Blo 119786 153085 := bbase (se 3 (by rfl) ⟨28703, by rfl⟩ : syracuseStep 153085 = 57407) (by norm_num)
theorem B153181 : Blo 119786 153181 := bbase (se 3 (by rfl) ⟨28721, by rfl⟩ : syracuseStep 153181 = 57443) (by norm_num)
theorem B349829 : Blo 119786 349829 := bbase (se 4 (by rfl) ⟨32796, by rfl⟩ : syracuseStep 349829 = 65593) (by norm_num)
theorem B1038005 : Blo 119786 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B153353 : Blo 119786 153353 := bbase (se 2 (by rfl) ⟨57507, by rfl⟩ : syracuseStep 153353 = 115015) (by norm_num)
theorem B153409 : Blo 119786 153409 := bbase (se 2 (by rfl) ⟨57528, by rfl⟩ : syracuseStep 153409 = 115057) (by norm_num)
theorem B513877 : Blo 119786 513877 := bbase (se 9 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 513877 = 3011) (by norm_num)
theorem B612197 : Blo 119786 612197 := bbase (se 4 (by rfl) ⟨57393, by rfl⟩ : syracuseStep 612197 = 114787) (by norm_num)
theorem B382837 : Blo 119786 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B415637 : Blo 119786 415637 := bbase (se 6 (by rfl) ⟨9741, by rfl⟩ : syracuseStep 415637 = 19483) (by norm_num)
theorem B153505 : Blo 119786 153505 := bbase (se 2 (by rfl) ⟨57564, by rfl⟩ : syracuseStep 153505 = 115129) (by norm_num)
theorem B186349 : Blo 119786 186349 := bbase (se 3 (by rfl) ⟨34940, by rfl⟩ : syracuseStep 186349 = 69881) (by norm_num)
theorem B153677 : Blo 119786 153677 := bbase (se 3 (by rfl) ⟨28814, by rfl⟩ : syracuseStep 153677 = 57629) (by norm_num)
theorem B252029 : Blo 119786 252029 := bbase (se 3 (by rfl) ⟨47255, by rfl⟩ : syracuseStep 252029 = 94511) (by norm_num)
theorem B153733 : Blo 119786 153733 := bbase (se 4 (by rfl) ⟨14412, by rfl⟩ : syracuseStep 153733 = 28825) (by norm_num)
theorem B153829 : Blo 119786 153829 := bbase (se 4 (by rfl) ⟨14421, by rfl⟩ : syracuseStep 153829 = 28843) (by norm_num)
theorem B416069 : Blo 119786 416069 := bbase (se 4 (by rfl) ⟨39006, by rfl⟩ : syracuseStep 416069 = 78013) (by norm_num)
theorem B350581 : Blo 119786 350581 := bbase (se 5 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 350581 = 32867) (by norm_num)
theorem B154001 : Blo 119786 154001 := bbase (se 2 (by rfl) ⟨57750, by rfl⟩ : syracuseStep 154001 = 115501) (by norm_num)
theorem B154009 : Blo 119786 154009 := bbase (se 2 (by rfl) ⟨57753, by rfl⟩ : syracuseStep 154009 = 115507) (by norm_num)
theorem B154057 : Blo 119786 154057 := bbase (se 2 (by rfl) ⟨57771, by rfl⟩ : syracuseStep 154057 = 115543) (by norm_num)
theorem B1169909 : Blo 119786 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B154153 : Blo 119786 154153 := bbase (se 2 (by rfl) ⟨57807, by rfl⟩ : syracuseStep 154153 = 115615) (by norm_num)
theorem B514613 : Blo 119786 514613 := bbase (se 5 (by rfl) ⟨24122, by rfl⟩ : syracuseStep 514613 = 48245) (by norm_num)
theorem B580229 : Blo 119786 580229 := bbase (se 4 (by rfl) ⟨54396, by rfl⟩ : syracuseStep 580229 = 108793) (by norm_num)
theorem B121537 : Blo 119786 121537 := bbase (se 2 (by rfl) ⟨45576, by rfl⟩ : syracuseStep 121537 = 91153) (by norm_num)
theorem B154325 : Blo 119786 154325 := bbase (se 7 (by rfl) ⟨1808, by rfl⟩ : syracuseStep 154325 = 3617) (by norm_num)
theorem B219877 : Blo 119786 219877 := bbase (se 4 (by rfl) ⟨20613, by rfl⟩ : syracuseStep 219877 = 41227) (by norm_num)
theorem B416501 : Blo 119786 416501 := bbase (se 5 (by rfl) ⟨19523, by rfl⟩ : syracuseStep 416501 = 39047) (by norm_num)
theorem B154381 : Blo 119786 154381 := bbase (se 3 (by rfl) ⟨28946, by rfl⟩ : syracuseStep 154381 = 57893) (by norm_num)
theorem B187181 : Blo 119786 187181 := bbase (se 3 (by rfl) ⟨35096, by rfl⟩ : syracuseStep 187181 = 70193) (by norm_num)
theorem B154477 : Blo 119786 154477 := bbase (se 3 (by rfl) ⟨28964, by rfl⟩ : syracuseStep 154477 = 57929) (by norm_num)
theorem B154649 : Blo 119786 154649 := bbase (se 2 (by rfl) ⟨57993, by rfl⟩ : syracuseStep 154649 = 115987) (by norm_num)
theorem B121897 : Blo 119786 121897 := bbase (se 2 (by rfl) ⟨45711, by rfl⟩ : syracuseStep 121897 = 91423) (by norm_num)
theorem B220205 : Blo 119786 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B154705 : Blo 119786 154705 := bbase (se 2 (by rfl) ⟨58014, by rfl⟩ : syracuseStep 154705 = 116029) (by norm_num)
theorem B613493 : Blo 119786 613493 := bbase (se 5 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 613493 = 57515) (by norm_num)
theorem B187517 : Blo 119786 187517 := bbase (se 3 (by rfl) ⟨35159, by rfl⟩ : syracuseStep 187517 = 70319) (by norm_num)
theorem B416933 : Blo 119786 416933 := bbase (se 4 (by rfl) ⟨39087, by rfl⟩ : syracuseStep 416933 = 78175) (by norm_num)
theorem B220333 : Blo 119786 220333 := bbase (se 3 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 220333 = 82625) (by norm_num)
theorem B154801 : Blo 119786 154801 := bbase (se 2 (by rfl) ⟨58050, by rfl⟩ : syracuseStep 154801 = 116101) (by norm_num)
theorem B154973 : Blo 119786 154973 := bbase (se 3 (by rfl) ⟨29057, by rfl⟩ : syracuseStep 154973 = 58115) (by norm_num)
theorem B155029 : Blo 119786 155029 := bbase (se 6 (by rfl) ⟨3633, by rfl⟩ : syracuseStep 155029 = 7267) (by norm_num)
theorem B2252245 : Blo 119786 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B155125 : Blo 119786 155125 := bbase (se 5 (by rfl) ⟨7271, by rfl⟩ : syracuseStep 155125 = 14543) (by norm_num)
theorem B417365 : Blo 119786 417365 := bbase (se 8 (by rfl) ⟨2445, by rfl⟩ : syracuseStep 417365 = 4891) (by norm_num)
theorem B417413 : Blo 119786 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B155297 : Blo 119786 155297 := bbase (se 2 (by rfl) ⟨58236, by rfl⟩ : syracuseStep 155297 = 116473) (by norm_num)
theorem B155353 : Blo 119786 155353 := bbase (se 2 (by rfl) ⟨58257, by rfl⟩ : syracuseStep 155353 = 116515) (by norm_num)
theorem B155449 : Blo 119786 155449 := bbase (se 2 (by rfl) ⟨58293, by rfl⟩ : syracuseStep 155449 = 116587) (by norm_num)
theorem B155621 : Blo 119786 155621 := bbase (se 4 (by rfl) ⟨14589, by rfl⟩ : syracuseStep 155621 = 29179) (by norm_num)
theorem B155677 : Blo 119786 155677 := bbase (se 3 (by rfl) ⟨29189, by rfl⟩ : syracuseStep 155677 = 58379) (by norm_num)
theorem B155773 : Blo 119786 155773 := bbase (se 3 (by rfl) ⟨29207, by rfl⟩ : syracuseStep 155773 = 58415) (by norm_num)
theorem B1597589 : Blo 119786 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B123049 : Blo 119786 123049 := bbase (se 2 (by rfl) ⟨46143, by rfl⟩ : syracuseStep 123049 = 92287) (by norm_num)
theorem B123077 : Blo 119786 123077 := bbase (se 4 (by rfl) ⟨11538, by rfl⟩ : syracuseStep 123077 = 23077) (by norm_num)
theorem B221429 : Blo 119786 221429 := bbase (se 5 (by rfl) ⟨10379, by rfl⟩ : syracuseStep 221429 = 20759) (by norm_num)
theorem B155945 : Blo 119786 155945 := bbase (se 2 (by rfl) ⟨58479, by rfl⟩ : syracuseStep 155945 = 116959) (by norm_num)
theorem B156001 : Blo 119786 156001 := bbase (se 2 (by rfl) ⟨58500, by rfl⟩ : syracuseStep 156001 = 117001) (by norm_num)
theorem B614789 : Blo 119786 614789 := bbase (se 4 (by rfl) ⟨57636, by rfl⟩ : syracuseStep 614789 = 115273) (by norm_num)
theorem B156097 : Blo 119786 156097 := bbase (se 2 (by rfl) ⟨58536, by rfl⟩ : syracuseStep 156097 = 117073) (by norm_num)
theorem B778709 : Blo 119786 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B221717 : Blo 119786 221717 := bbase (se 6 (by rfl) ⟨5196, by rfl⟩ : syracuseStep 221717 = 10393) (by norm_num)
theorem B549413 : Blo 119786 549413 := bbase (se 4 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 549413 = 103015) (by norm_num)
theorem B156269 : Blo 119786 156269 := bbase (se 3 (by rfl) ⟨29300, by rfl⟩ : syracuseStep 156269 = 58601) (by norm_num)
theorem B156325 : Blo 119786 156325 := bbase (se 4 (by rfl) ⟨14655, by rfl⟩ : syracuseStep 156325 = 29311) (by norm_num)
theorem B156421 : Blo 119786 156421 := bbase (se 4 (by rfl) ⟨14664, by rfl⟩ : syracuseStep 156421 = 29329) (by norm_num)
theorem B1237781 : Blo 119786 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B156593 : Blo 119786 156593 := bbase (se 2 (by rfl) ⟨58722, by rfl⟩ : syracuseStep 156593 = 117445) (by norm_num)
theorem B156649 : Blo 119786 156649 := bbase (se 2 (by rfl) ⟨58743, by rfl⟩ : syracuseStep 156649 = 117487) (by norm_num)
theorem B287981 : Blo 119786 287981 := bbase (se 3 (by rfl) ⟨53996, by rfl⟩ : syracuseStep 287981 = 107993) (by norm_num)
theorem B288269 : Blo 119786 288269 := bbase (se 3 (by rfl) ⟨54050, by rfl⟩ : syracuseStep 288269 = 108101) (by norm_num)
theorem B222869 : Blo 119786 222869 := bbase (se 6 (by rfl) ⟨5223, by rfl⟩ : syracuseStep 222869 = 10447) (by norm_num)
theorem B616085 : Blo 119786 616085 := bbase (se 6 (by rfl) ⟨14439, by rfl⟩ : syracuseStep 616085 = 28879) (by norm_num)
theorem B222949 : Blo 119786 222949 := bbase (se 4 (by rfl) ⟨20901, by rfl⟩ : syracuseStep 222949 = 41803) (by norm_num)
theorem B517909 : Blo 119786 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B255845 : Blo 119786 255845 := bbase (se 4 (by rfl) ⟨23985, by rfl⟩ : syracuseStep 255845 = 47971) (by norm_num)
theorem B124813 : Blo 119786 124813 := bbase (se 3 (by rfl) ⟨23402, by rfl⟩ : syracuseStep 124813 = 46805) (by norm_num)
theorem B583861 : Blo 119786 583861 := bbase (se 5 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 583861 = 54737) (by norm_num)
theorem B256213 : Blo 119786 256213 := bbase (se 7 (by rfl) ⟨3002, by rfl⟩ : syracuseStep 256213 = 6005) (by norm_num)
theorem B158105 : Blo 119786 158105 := bbase (se 2 (by rfl) ⟨59289, by rfl⟩ : syracuseStep 158105 = 118579) (by norm_num)
theorem B387509 : Blo 119786 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B617381 : Blo 119786 617381 := bbase (se 4 (by rfl) ⟨57879, by rfl⟩ : syracuseStep 617381 = 115759) (by norm_num)
theorem B420821 : Blo 119786 420821 := bbase (se 7 (by rfl) ⟨4931, by rfl⟩ : syracuseStep 420821 = 9863) (by norm_num)
theorem B1404053 : Blo 119786 1404053 := bbase (se 6 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 1404053 = 65815) (by norm_num)
theorem B388421 : Blo 119786 388421 := bbase (se 4 (by rfl) ⟨36414, by rfl⟩ : syracuseStep 388421 = 72829) (by norm_num)
theorem B880085 : Blo 119786 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B290317 : Blo 119786 290317 := bbase (se 3 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 290317 = 108869) (by norm_num)
theorem B224869 : Blo 119786 224869 := bbase (se 4 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 224869 = 42163) (by norm_num)
theorem B257717 : Blo 119786 257717 := bbase (se 5 (by rfl) ⟨12080, by rfl⟩ : syracuseStep 257717 = 24161) (by norm_num)
theorem B192269 : Blo 119786 192269 := bbase (se 3 (by rfl) ⟨36050, by rfl⟩ : syracuseStep 192269 = 72101) (by norm_num)
theorem B257861 : Blo 119786 257861 := bbase (se 4 (by rfl) ⟨24174, by rfl⟩ : syracuseStep 257861 = 48349) (by norm_num)
theorem B192397 : Blo 119786 192397 := bbase (se 3 (by rfl) ⟨36074, by rfl⟩ : syracuseStep 192397 = 72149) (by norm_num)
theorem B258221 : Blo 119786 258221 := bbase (se 3 (by rfl) ⟨48416, by rfl⟩ : syracuseStep 258221 = 96833) (by norm_num)
theorem B618677 : Blo 119786 618677 := bbase (se 5 (by rfl) ⟨29000, by rfl⟩ : syracuseStep 618677 = 58001) (by norm_num)
theorem B782581 : Blo 119786 782581 := bbase (se 5 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 782581 = 73367) (by norm_num)
theorem B192781 : Blo 119786 192781 := bbase (se 3 (by rfl) ⟨36146, by rfl⟩ : syracuseStep 192781 = 72293) (by norm_num)
theorem B193037 : Blo 119786 193037 := bbase (se 3 (by rfl) ⟨36194, by rfl⟩ : syracuseStep 193037 = 72389) (by norm_num)
theorem B389765 : Blo 119786 389765 := bbase (se 4 (by rfl) ⟨36540, by rfl⟩ : syracuseStep 389765 = 73081) (by norm_num)
theorem B520901 : Blo 119786 520901 := bbase (se 4 (by rfl) ⟨48834, by rfl⟩ : syracuseStep 520901 = 97669) (by norm_num)
theorem B914165 : Blo 119786 914165 := bbase (se 5 (by rfl) ⟨42851, by rfl⟩ : syracuseStep 914165 = 85703) (by norm_num)
theorem B1504021 : Blo 119786 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B128017 : Blo 119786 128017 := bbase (se 2 (by rfl) ⟨48006, by rfl⟩ : syracuseStep 128017 = 96013) (by norm_num)
theorem B259109 : Blo 119786 259109 := bbase (se 4 (by rfl) ⟨24291, by rfl⟩ : syracuseStep 259109 = 48583) (by norm_num)
theorem B324821 : Blo 119786 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B488693 : Blo 119786 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B259357 : Blo 119786 259357 := bbase (se 3 (by rfl) ⟨48629, by rfl⟩ : syracuseStep 259357 = 97259) (by norm_num)
theorem B455989 : Blo 119786 455989 := bbase (se 5 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 455989 = 42749) (by norm_num)
theorem B193909 : Blo 119786 193909 := bbase (se 5 (by rfl) ⟨9089, by rfl⟩ : syracuseStep 193909 = 18179) (by norm_num)
theorem B619973 : Blo 119786 619973 := bbase (se 4 (by rfl) ⟨58122, by rfl⟩ : syracuseStep 619973 = 116245) (by norm_num)
theorem B128461 : Blo 119786 128461 := bbase (se 3 (by rfl) ⟨24086, by rfl⟩ : syracuseStep 128461 = 48173) (by norm_num)
theorem B194005 : Blo 119786 194005 := bbase (se 7 (by rfl) ⟨2273, by rfl⟩ : syracuseStep 194005 = 4547) (by norm_num)
theorem B128585 : Blo 119786 128585 := bbase (se 2 (by rfl) ⟨48219, by rfl⟩ : syracuseStep 128585 = 96439) (by norm_num)
theorem B456293 : Blo 119786 456293 := bbase (se 4 (by rfl) ⟨42777, by rfl⟩ : syracuseStep 456293 = 85555) (by norm_num)
theorem B194165 : Blo 119786 194165 := bbase (se 5 (by rfl) ⟨9101, by rfl⟩ : syracuseStep 194165 = 18203) (by norm_num)
theorem B521909 : Blo 119786 521909 := bbase (se 5 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 521909 = 48929) (by norm_num)
theorem B980693 : Blo 119786 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B259861 : Blo 119786 259861 := bbase (se 6 (by rfl) ⟨6090, by rfl⟩ : syracuseStep 259861 = 12181) (by norm_num)
theorem B128837 : Blo 119786 128837 := bbase (se 4 (by rfl) ⟨12078, by rfl⟩ : syracuseStep 128837 = 24157) (by norm_num)
theorem B292709 : Blo 119786 292709 := bbase (se 4 (by rfl) ⟨27441, by rfl⟩ : syracuseStep 292709 = 54883) (by norm_num)
theorem B292853 : Blo 119786 292853 := bbase (se 5 (by rfl) ⟨13727, by rfl⟩ : syracuseStep 292853 = 27455) (by norm_num)
theorem B391189 : Blo 119786 391189 := bbase (se 6 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 391189 = 18337) (by norm_num)
theorem B292925 : Blo 119786 292925 := bbase (se 3 (by rfl) ⟨54923, by rfl⟩ : syracuseStep 292925 = 109847) (by norm_num)
theorem B129281 : Blo 119786 129281 := bbase (se 2 (by rfl) ⟨48480, by rfl⟩ : syracuseStep 129281 = 96961) (by norm_num)
theorem B489797 : Blo 119786 489797 := bbase (se 4 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 489797 = 91837) (by norm_num)
theorem B129529 : Blo 119786 129529 := bbase (se 2 (by rfl) ⟨48573, by rfl⟩ : syracuseStep 129529 = 97147) (by norm_num)
theorem B260749 : Blo 119786 260749 := bbase (se 3 (by rfl) ⟨48890, by rfl⟩ : syracuseStep 260749 = 97781) (by norm_num)
theorem B621269 : Blo 119786 621269 := bbase (se 7 (by rfl) ⟨7280, by rfl⟩ : syracuseStep 621269 = 14561) (by norm_num)
theorem B195293 : Blo 119786 195293 := bbase (se 3 (by rfl) ⟨36617, by rfl⟩ : syracuseStep 195293 = 73235) (by norm_num)
theorem B228109 : Blo 119786 228109 := bbase (se 3 (by rfl) ⟨42770, by rfl⟩ : syracuseStep 228109 = 85541) (by norm_num)
theorem B228253 : Blo 119786 228253 := bbase (se 3 (by rfl) ⟨42797, by rfl⟩ : syracuseStep 228253 = 85595) (by norm_num)
theorem B129973 : Blo 119786 129973 := bbase (se 5 (by rfl) ⟨6092, by rfl⟩ : syracuseStep 129973 = 12185) (by norm_num)
theorem B162757 : Blo 119786 162757 := bbase (se 4 (by rfl) ⟨15258, by rfl⟩ : syracuseStep 162757 = 30517) (by norm_num)
theorem B130033 : Blo 119786 130033 := bbase (se 2 (by rfl) ⟨48762, by rfl⟩ : syracuseStep 130033 = 97525) (by norm_num)
theorem B293917 : Blo 119786 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B326693 : Blo 119786 326693 := bbase (se 4 (by rfl) ⟨30627, by rfl⟩ : syracuseStep 326693 = 61255) (by norm_num)
theorem B228413 : Blo 119786 228413 := bbase (se 3 (by rfl) ⟨42827, by rfl⟩ : syracuseStep 228413 = 85655) (by norm_num)
theorem B261245 : Blo 119786 261245 := bbase (se 3 (by rfl) ⟨48983, by rfl⟩ : syracuseStep 261245 = 97967) (by norm_num)
theorem B228557 : Blo 119786 228557 := bbase (se 3 (by rfl) ⟨42854, by rfl⟩ : syracuseStep 228557 = 85709) (by norm_num)
theorem B195805 : Blo 119786 195805 := bbase (se 3 (by rfl) ⟨36713, by rfl⟩ : syracuseStep 195805 = 73427) (by norm_num)
theorem B130349 : Blo 119786 130349 := bbase (se 3 (by rfl) ⟨24440, by rfl⟩ : syracuseStep 130349 = 48881) (by norm_num)
theorem B523685 : Blo 119786 523685 := bbase (se 4 (by rfl) ⟨49095, by rfl⟩ : syracuseStep 523685 = 98191) (by norm_num)
theorem B228845 : Blo 119786 228845 := bbase (se 3 (by rfl) ⟨42908, by rfl⟩ : syracuseStep 228845 = 85817) (by norm_num)
theorem B392789 : Blo 119786 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B228997 : Blo 119786 228997 := bbase (se 4 (by rfl) ⟨21468, by rfl⟩ : syracuseStep 228997 = 42937) (by norm_num)
theorem B458405 : Blo 119786 458405 := bbase (se 4 (by rfl) ⟨42975, by rfl⟩ : syracuseStep 458405 = 85951) (by norm_num)
theorem B491221 : Blo 119786 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B130793 : Blo 119786 130793 := bbase (se 2 (by rfl) ⟨49047, by rfl⟩ : syracuseStep 130793 = 98095) (by norm_num)
theorem B130853 : Blo 119786 130853 := bbase (se 4 (by rfl) ⟨12267, by rfl⟩ : syracuseStep 130853 = 24535) (by norm_num)
theorem B130981 : Blo 119786 130981 := bbase (se 4 (by rfl) ⟨12279, by rfl⟩ : syracuseStep 130981 = 24559) (by norm_num)
theorem B229301 : Blo 119786 229301 := bbase (se 5 (by rfl) ⟨10748, by rfl⟩ : syracuseStep 229301 = 21497) (by norm_num)
theorem B458693 : Blo 119786 458693 := bbase (se 4 (by rfl) ⟨43002, by rfl⟩ : syracuseStep 458693 = 86005) (by norm_num)
theorem B360389 : Blo 119786 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B294853 : Blo 119786 294853 := bbase (se 4 (by rfl) ⟨27642, by rfl⟩ : syracuseStep 294853 = 55285) (by norm_num)
theorem B688085 : Blo 119786 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B622565 : Blo 119786 622565 := bbase (se 4 (by rfl) ⟨58365, by rfl⟩ : syracuseStep 622565 = 116731) (by norm_num)
theorem B262133 : Blo 119786 262133 := bbase (se 5 (by rfl) ⟨12287, by rfl⟩ : syracuseStep 262133 = 24575) (by norm_num)
theorem B196625 : Blo 119786 196625 := bstep (se 2 (by rfl) ⟨73734, by rfl⟩ : syracuseStep 196625 = 147469) B147469
theorem B131203 : Blo 119786 131203 := bstep (se 1 (by rfl) ⟨98402, by rfl⟩ : syracuseStep 131203 = 196805) B196805
theorem B262577 : Blo 119786 262577 := bstep (se 2 (by rfl) ⟨98466, by rfl⟩ : syracuseStep 262577 = 196933) B196933
theorem B262595 : Blo 119786 262595 := bstep (se 1 (by rfl) ⟨196946, by rfl⟩ : syracuseStep 262595 = 393893) B393893
theorem B328205 : Blo 119786 328205 := bstep (se 3 (by rfl) ⟨61538, by rfl⟩ : syracuseStep 328205 = 123077) B123077
theorem B393763 : Blo 119786 393763 := bstep (se 1 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 393763 = 590645) B590645
theorem B229969 : Blo 119786 229969 := bstep (se 2 (by rfl) ⟨86238, by rfl⟩ : syracuseStep 229969 = 172477) B172477
theorem B459377 : Blo 119786 459377 := bstep (se 2 (by rfl) ⟨172266, by rfl⟩ : syracuseStep 459377 = 344533) B344533
theorem B590627 : Blo 119786 590627 := bstep (se 1 (by rfl) ⟨442970, by rfl⟩ : syracuseStep 590627 = 885941) B885941
theorem B197491 : Blo 119786 197491 := bstep (se 1 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 197491 = 296237) B296237
theorem B656261 : Blo 119786 656261 := bstep (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) B123049
theorem B623537 : Blo 119786 623537 := bstep (se 2 (by rfl) ⟨233826, by rfl⟩ : syracuseStep 623537 = 467653) B467653
theorem B525325 : Blo 119786 525325 := bstep (se 3 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 525325 = 196997) B196997
theorem B1672433 : Blo 119786 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B886085 : Blo 119786 886085 := bstep (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) B166141
theorem B755077 : Blo 119786 755077 := bstep (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) B141577
theorem B492941 : Blo 119786 492941 := bstep (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) B184853
theorem B394723 : Blo 119786 394723 := bstep (se 1 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 394723 = 592085) B592085
theorem B296419 : Blo 119786 296419 := bstep (se 1 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 296419 = 444629) B444629
theorem B919025 : Blo 119786 919025 := bstep (se 2 (by rfl) ⟨344634, by rfl⟩ : syracuseStep 919025 = 689269) B689269
theorem B198163 : Blo 119786 198163 := bstep (se 1 (by rfl) ⟨148622, by rfl⟩ : syracuseStep 198163 = 297245) B297245
theorem B198209 : Blo 119786 198209 := bstep (se 2 (by rfl) ⟨74328, by rfl⟩ : syracuseStep 198209 = 148657) B148657
theorem B231025 : Blo 119786 231025 := bstep (se 2 (by rfl) ⟨86634, by rfl⟩ : syracuseStep 231025 = 173269) B173269
theorem B394993 : Blo 119786 394993 := bstep (se 2 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 394993 = 296245) B296245
theorem B591857 : Blo 119786 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B231427 : Blo 119786 231427 := bstep (se 1 (by rfl) ⟨173570, by rfl⟩ : syracuseStep 231427 = 347141) B347141
theorem B460835 : Blo 119786 460835 := bstep (se 1 (by rfl) ⟨345626, by rfl⟩ : syracuseStep 460835 = 691253) B691253
theorem B460849 : Blo 119786 460849 := bstep (se 2 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 460849 = 345637) B345637
theorem B231473 : Blo 119786 231473 := bstep (se 2 (by rfl) ⟨86802, by rfl⟩ : syracuseStep 231473 = 173605) B173605
theorem B821381 : Blo 119786 821381 := bstep (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) B154009
theorem B231587 : Blo 119786 231587 := bstep (se 1 (by rfl) ⟨173690, by rfl⟩ : syracuseStep 231587 = 347381) B347381
theorem B297265 : Blo 119786 297265 := bstep (se 2 (by rfl) ⟨111474, by rfl⟩ : syracuseStep 297265 = 222949) B222949
theorem B166195 : Blo 119786 166195 := bstep (se 1 (by rfl) ⟨124646, by rfl⟩ : syracuseStep 166195 = 249293) B249293
theorem B395597 : Blo 119786 395597 := bstep (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) B148349
theorem B231761 : Blo 119786 231761 := bstep (se 2 (by rfl) ⟨86910, by rfl⟩ : syracuseStep 231761 = 173821) B173821
theorem B624995 : Blo 119786 624995 := bstep (se 1 (by rfl) ⟨468746, by rfl⟩ : syracuseStep 624995 = 937493) B937493
theorem B690545 : Blo 119786 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B166417 : Blo 119786 166417 := bstep (se 2 (by rfl) ⟨62406, by rfl⟩ : syracuseStep 166417 = 124813) B124813
theorem B789425 : Blo 119786 789425 := bstep (se 2 (by rfl) ⟨296034, by rfl⟩ : syracuseStep 789425 = 592069) B592069
theorem B232483 : Blo 119786 232483 := bstep (se 1 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 232483 = 348725) B348725
theorem B166979 : Blo 119786 166979 := bstep (se 1 (by rfl) ⟨125234, by rfl⟩ : syracuseStep 166979 = 250469) B250469
theorem B167027 : Blo 119786 167027 := bstep (se 1 (by rfl) ⟨125270, by rfl⟩ : syracuseStep 167027 = 250541) B250541
theorem B625805 : Blo 119786 625805 := bstep (se 3 (by rfl) ⟨117338, by rfl⟩ : syracuseStep 625805 = 234677) B234677
theorem B167203 : Blo 119786 167203 := bstep (se 1 (by rfl) ⟨125402, by rfl⟩ : syracuseStep 167203 = 250805) B250805
theorem B462307 : Blo 119786 462307 := bstep (se 1 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 462307 = 693461) B693461
theorem B232931 : Blo 119786 232931 := bstep (se 1 (by rfl) ⟨174698, by rfl⟩ : syracuseStep 232931 = 349397) B349397
theorem B200179 : Blo 119786 200179 := bstep (se 1 (by rfl) ⟨150134, by rfl⟩ : syracuseStep 200179 = 300269) B300269
theorem B233009 : Blo 119786 233009 := bstep (se 2 (by rfl) ⟨87378, by rfl⟩ : syracuseStep 233009 = 174757) B174757
theorem B1773197 : Blo 119786 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B134851 : Blo 119786 134851 := bstep (se 1 (by rfl) ⟨101138, by rfl⟩ : syracuseStep 134851 = 202277) B202277
theorem B233219 : Blo 119786 233219 := bstep (se 1 (by rfl) ⟨174914, by rfl⟩ : syracuseStep 233219 = 349829) B349829
theorem B692003 : Blo 119786 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B134995 : Blo 119786 134995 := bstep (se 1 (by rfl) ⟨101246, by rfl⟩ : syracuseStep 134995 = 202493) B202493
theorem B135139 : Blo 119786 135139 := bstep (se 1 (by rfl) ⟨101354, by rfl⟩ : syracuseStep 135139 = 202709) B202709
theorem B790499 : Blo 119786 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B135283 : Blo 119786 135283 := bstep (se 1 (by rfl) ⟨101462, by rfl⟩ : syracuseStep 135283 = 202925) B202925
theorem B135427 : Blo 119786 135427 := bstep (se 1 (by rfl) ⟨101570, by rfl⟩ : syracuseStep 135427 = 203141) B203141
theorem B790897 : Blo 119786 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B594317 : Blo 119786 594317 := bstep (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) B222869
theorem B135571 : Blo 119786 135571 := bstep (se 1 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 135571 = 203357) B203357
theorem B135715 : Blo 119786 135715 := bstep (se 1 (by rfl) ⟨101786, by rfl⟩ : syracuseStep 135715 = 203573) B203573
theorem B1053283 : Blo 119786 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B234161 : Blo 119786 234161 := bstep (se 2 (by rfl) ⟨87810, by rfl⟩ : syracuseStep 234161 = 175621) B175621
theorem B135859 : Blo 119786 135859 := bstep (se 1 (by rfl) ⟨101894, by rfl⟩ : syracuseStep 135859 = 203789) B203789
theorem B1151729 : Blo 119786 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B299825 : Blo 119786 299825 := bstep (se 2 (by rfl) ⟨112434, by rfl⟩ : syracuseStep 299825 = 224869) B224869
theorem B136003 : Blo 119786 136003 := bstep (se 1 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 136003 = 204005) B204005
theorem B136147 : Blo 119786 136147 := bstep (se 1 (by rfl) ⟨102110, by rfl⟩ : syracuseStep 136147 = 204221) B204221
theorem B136291 : Blo 119786 136291 := bstep (se 1 (by rfl) ⟨102218, by rfl⟩ : syracuseStep 136291 = 204437) B204437
theorem B136435 : Blo 119786 136435 := bstep (se 1 (by rfl) ⟨102326, by rfl⟩ : syracuseStep 136435 = 204653) B204653
theorem B136579 : Blo 119786 136579 := bstep (se 1 (by rfl) ⟨102434, by rfl⟩ : syracuseStep 136579 = 204869) B204869
theorem B202243 : Blo 119786 202243 := bstep (se 1 (by rfl) ⟨151682, by rfl⟩ : syracuseStep 202243 = 303365) B303365
theorem B136723 : Blo 119786 136723 := bstep (se 1 (by rfl) ⟨102542, by rfl⟩ : syracuseStep 136723 = 205085) B205085
theorem B464525 : Blo 119786 464525 := bstep (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) B174197
theorem B202385 : Blo 119786 202385 := bstep (se 2 (by rfl) ⟨75894, by rfl⟩ : syracuseStep 202385 = 151789) B151789
theorem B136867 : Blo 119786 136867 := bstep (se 1 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 136867 = 205301) B205301
theorem B366275 : Blo 119786 366275 := bstep (se 1 (by rfl) ⟨274706, by rfl⟩ : syracuseStep 366275 = 549413) B549413
theorem B202513 : Blo 119786 202513 := bstep (se 2 (by rfl) ⟨75942, by rfl⟩ : syracuseStep 202513 = 151885) B151885
theorem B202547 : Blo 119786 202547 := bstep (se 1 (by rfl) ⟨151910, by rfl⟩ : syracuseStep 202547 = 303821) B303821
theorem B137011 : Blo 119786 137011 := bstep (se 1 (by rfl) ⟨102758, by rfl⟩ : syracuseStep 137011 = 205517) B205517
theorem B202675 : Blo 119786 202675 := bstep (se 1 (by rfl) ⟨152006, by rfl⟩ : syracuseStep 202675 = 304013) B304013
theorem B137155 : Blo 119786 137155 := bstep (se 1 (by rfl) ⟨102866, by rfl⟩ : syracuseStep 137155 = 205733) B205733
theorem B202817 : Blo 119786 202817 := bstep (se 2 (by rfl) ⟨76056, by rfl⟩ : syracuseStep 202817 = 152113) B152113
theorem B137299 : Blo 119786 137299 := bstep (se 1 (by rfl) ⟨102974, by rfl⟩ : syracuseStep 137299 = 205949) B205949
theorem B202945 : Blo 119786 202945 := bstep (se 2 (by rfl) ⟨76104, by rfl⟩ : syracuseStep 202945 = 152209) B152209
theorem B661709 : Blo 119786 661709 := bstep (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) B248141
theorem B202979 : Blo 119786 202979 := bstep (se 1 (by rfl) ⟨152234, by rfl⟩ : syracuseStep 202979 = 304469) B304469
theorem B137443 : Blo 119786 137443 := bstep (se 1 (by rfl) ⟨103082, by rfl⟩ : syracuseStep 137443 = 206165) B206165
theorem B203107 : Blo 119786 203107 := bstep (se 1 (by rfl) ⟨152330, by rfl⟩ : syracuseStep 203107 = 304661) B304661
theorem B2005361 : Blo 119786 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B137587 : Blo 119786 137587 := bstep (se 1 (by rfl) ⟨103190, by rfl⟩ : syracuseStep 137587 = 206381) B206381
theorem B203249 : Blo 119786 203249 := bstep (se 2 (by rfl) ⟨76218, by rfl⟩ : syracuseStep 203249 = 152437) B152437
theorem B137731 : Blo 119786 137731 := bstep (se 1 (by rfl) ⟨103298, by rfl⟩ : syracuseStep 137731 = 206597) B206597
theorem B203377 : Blo 119786 203377 := bstep (se 2 (by rfl) ⟨76266, by rfl⟩ : syracuseStep 203377 = 152533) B152533
theorem B367249 : Blo 119786 367249 := bstep (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) B275437
theorem B203411 : Blo 119786 203411 := bstep (se 1 (by rfl) ⟨152558, by rfl⟩ : syracuseStep 203411 = 305117) B305117
theorem B137875 : Blo 119786 137875 := bstep (se 1 (by rfl) ⟨103406, by rfl⟩ : syracuseStep 137875 = 206813) B206813
theorem B170689 : Blo 119786 170689 := bstep (se 2 (by rfl) ⟨64008, by rfl⟩ : syracuseStep 170689 = 128017) B128017
theorem B1055501 : Blo 119786 1055501 := bstep (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) B395813
theorem B203539 : Blo 119786 203539 := bstep (se 1 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 203539 = 305309) B305309
theorem B138019 : Blo 119786 138019 := bstep (se 1 (by rfl) ⟨103514, by rfl⟩ : syracuseStep 138019 = 207029) B207029
theorem B138083 : Blo 119786 138083 := bstep (se 1 (by rfl) ⟨103562, by rfl⟩ : syracuseStep 138083 = 207125) B207125
theorem B203681 : Blo 119786 203681 := bstep (se 2 (by rfl) ⟨76380, by rfl⟩ : syracuseStep 203681 = 152761) B152761
theorem B138163 : Blo 119786 138163 := bstep (se 1 (by rfl) ⟨103622, by rfl⟩ : syracuseStep 138163 = 207245) B207245
theorem B203809 : Blo 119786 203809 := bstep (se 2 (by rfl) ⟨76428, by rfl⟩ : syracuseStep 203809 = 152857) B152857
theorem B203843 : Blo 119786 203843 := bstep (se 1 (by rfl) ⟨152882, by rfl⟩ : syracuseStep 203843 = 305765) B305765
theorem B138307 : Blo 119786 138307 := bstep (se 1 (by rfl) ⟨103730, by rfl⟩ : syracuseStep 138307 = 207461) B207461
theorem B269443 : Blo 119786 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B1154189 : Blo 119786 1154189 := bstep (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) B432821
theorem B203971 : Blo 119786 203971 := bstep (se 1 (by rfl) ⟨152978, by rfl⟩ : syracuseStep 203971 = 305957) B305957
theorem B138451 : Blo 119786 138451 := bstep (se 1 (by rfl) ⟨103838, by rfl⟩ : syracuseStep 138451 = 207677) B207677
theorem B269585 : Blo 119786 269585 := bstep (se 2 (by rfl) ⟨101094, by rfl⟩ : syracuseStep 269585 = 202189) B202189
theorem B171281 : Blo 119786 171281 := bstep (se 2 (by rfl) ⟨64230, by rfl⟩ : syracuseStep 171281 = 128461) B128461
theorem B269603 : Blo 119786 269603 := bstep (se 1 (by rfl) ⟨202202, by rfl⟩ : syracuseStep 269603 = 404405) B404405
theorem B204113 : Blo 119786 204113 := bstep (se 2 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 204113 = 153085) B153085
theorem B138595 : Blo 119786 138595 := bstep (se 1 (by rfl) ⟨103946, by rfl⟩ : syracuseStep 138595 = 207893) B207893
theorem B368077 : Blo 119786 368077 := bstep (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) B138029
theorem B204241 : Blo 119786 204241 := bstep (se 2 (by rfl) ⟨76590, by rfl⟩ : syracuseStep 204241 = 153181) B153181
theorem B204275 : Blo 119786 204275 := bstep (se 1 (by rfl) ⟨153206, by rfl⟩ : syracuseStep 204275 = 306413) B306413
theorem B138739 : Blo 119786 138739 := bstep (se 1 (by rfl) ⟨104054, by rfl⟩ : syracuseStep 138739 = 208109) B208109
theorem B269873 : Blo 119786 269873 := bstep (se 2 (by rfl) ⟨101202, by rfl⟩ : syracuseStep 269873 = 202405) B202405
theorem B269891 : Blo 119786 269891 := bstep (se 1 (by rfl) ⟨202418, by rfl⟩ : syracuseStep 269891 = 404837) B404837
theorem B204403 : Blo 119786 204403 := bstep (se 1 (by rfl) ⟨153302, by rfl⟩ : syracuseStep 204403 = 306605) B306605
theorem B138883 : Blo 119786 138883 := bstep (se 1 (by rfl) ⟨104162, by rfl⟩ : syracuseStep 138883 = 208325) B208325
theorem B204545 : Blo 119786 204545 := bstep (se 2 (by rfl) ⟨76704, by rfl⟩ : syracuseStep 204545 = 153409) B153409
theorem B139027 : Blo 119786 139027 := bstep (se 1 (by rfl) ⟨104270, by rfl⟩ : syracuseStep 139027 = 208541) B208541
theorem B171811 : Blo 119786 171811 := bstep (se 1 (by rfl) ⟨128858, by rfl⟩ : syracuseStep 171811 = 257717) B257717
theorem B270161 : Blo 119786 270161 := bstep (se 2 (by rfl) ⟨101310, by rfl⟩ : syracuseStep 270161 = 202621) B202621
theorem B270179 : Blo 119786 270179 := bstep (se 1 (by rfl) ⟨202634, by rfl⟩ : syracuseStep 270179 = 405269) B405269
theorem B204673 : Blo 119786 204673 := bstep (se 2 (by rfl) ⟨76752, by rfl⟩ : syracuseStep 204673 = 153505) B153505
theorem B204707 : Blo 119786 204707 := bstep (se 1 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 204707 = 307061) B307061
theorem B139171 : Blo 119786 139171 := bstep (se 1 (by rfl) ⟨104378, by rfl⟩ : syracuseStep 139171 = 208757) B208757
theorem B204835 : Blo 119786 204835 := bstep (se 1 (by rfl) ⟨153626, by rfl⟩ : syracuseStep 204835 = 307253) B307253
theorem B270449 : Blo 119786 270449 := bstep (se 2 (by rfl) ⟨101418, by rfl⟩ : syracuseStep 270449 = 202837) B202837
theorem B172147 : Blo 119786 172147 := bstep (se 1 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 172147 = 258221) B258221
theorem B270467 : Blo 119786 270467 := bstep (se 1 (by rfl) ⟨202850, by rfl⟩ : syracuseStep 270467 = 405701) B405701
theorem B204977 : Blo 119786 204977 := bstep (se 2 (by rfl) ⟨76866, by rfl⟩ : syracuseStep 204977 = 153733) B153733
theorem B205105 : Blo 119786 205105 := bstep (se 2 (by rfl) ⟨76914, by rfl⟩ : syracuseStep 205105 = 153829) B153829
theorem B205139 : Blo 119786 205139 := bstep (se 1 (by rfl) ⟨153854, by rfl⟩ : syracuseStep 205139 = 307709) B307709
theorem B1188209 : Blo 119786 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B237937 : Blo 119786 237937 := bstep (se 2 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 237937 = 178453) B178453
theorem B270737 : Blo 119786 270737 := bstep (se 2 (by rfl) ⟨101526, by rfl⟩ : syracuseStep 270737 = 203053) B203053
theorem B270755 : Blo 119786 270755 := bstep (se 1 (by rfl) ⟨203066, by rfl⟩ : syracuseStep 270755 = 406133) B406133
theorem B205267 : Blo 119786 205267 := bstep (se 1 (by rfl) ⟨153950, by rfl⟩ : syracuseStep 205267 = 307901) B307901
theorem B467441 : Blo 119786 467441 := bstep (se 2 (by rfl) ⟨175290, by rfl⟩ : syracuseStep 467441 = 350581) B350581
theorem B205409 : Blo 119786 205409 := bstep (se 2 (by rfl) ⟨77028, by rfl⟩ : syracuseStep 205409 = 154057) B154057
theorem B172705 : Blo 119786 172705 := bstep (se 2 (by rfl) ⟨64764, by rfl⟩ : syracuseStep 172705 = 129529) B129529
theorem B271025 : Blo 119786 271025 := bstep (se 2 (by rfl) ⟨101634, by rfl⟩ : syracuseStep 271025 = 203269) B203269
theorem B271043 : Blo 119786 271043 := bstep (se 1 (by rfl) ⟨203282, by rfl⟩ : syracuseStep 271043 = 406565) B406565
theorem B172739 : Blo 119786 172739 := bstep (se 1 (by rfl) ⟨129554, by rfl⟩ : syracuseStep 172739 = 259109) B259109
theorem B205537 : Blo 119786 205537 := bstep (se 2 (by rfl) ⟨77076, by rfl⟩ : syracuseStep 205537 = 154153) B154153
theorem B205571 : Blo 119786 205571 := bstep (se 1 (by rfl) ⟨154178, by rfl⟩ : syracuseStep 205571 = 308357) B308357
theorem B140051 : Blo 119786 140051 := bstep (se 1 (by rfl) ⟨105038, by rfl⟩ : syracuseStep 140051 = 210077) B210077
theorem B205699 : Blo 119786 205699 := bstep (se 1 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 205699 = 308549) B308549
theorem B271313 : Blo 119786 271313 := bstep (se 2 (by rfl) ⟨101742, by rfl⟩ : syracuseStep 271313 = 203485) B203485
theorem B271331 : Blo 119786 271331 := bstep (se 1 (by rfl) ⟨203498, by rfl⟩ : syracuseStep 271331 = 406997) B406997
theorem B304145 : Blo 119786 304145 := bstep (se 2 (by rfl) ⟨114054, by rfl⟩ : syracuseStep 304145 = 228109) B228109
theorem B205841 : Blo 119786 205841 := bstep (se 2 (by rfl) ⟨77190, by rfl⟩ : syracuseStep 205841 = 154381) B154381
theorem B304195 : Blo 119786 304195 := bstep (se 1 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 304195 = 456293) B456293
theorem B205969 : Blo 119786 205969 := bstep (se 2 (by rfl) ⟨77238, by rfl⟩ : syracuseStep 205969 = 154477) B154477
theorem B206003 : Blo 119786 206003 := bstep (se 1 (by rfl) ⟨154502, by rfl⟩ : syracuseStep 206003 = 309005) B309005
theorem B304337 : Blo 119786 304337 := bstep (se 2 (by rfl) ⟨114126, by rfl⟩ : syracuseStep 304337 = 228253) B228253
theorem B337123 : Blo 119786 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B271601 : Blo 119786 271601 := bstep (se 2 (by rfl) ⟨101850, by rfl⟩ : syracuseStep 271601 = 203701) B203701
theorem B173297 : Blo 119786 173297 := bstep (se 2 (by rfl) ⟨64986, by rfl⟩ : syracuseStep 173297 = 129973) B129973
theorem B271619 : Blo 119786 271619 := bstep (se 1 (by rfl) ⟨203714, by rfl⟩ : syracuseStep 271619 = 407429) B407429
theorem B206131 : Blo 119786 206131 := bstep (se 1 (by rfl) ⟨154598, by rfl⟩ : syracuseStep 206131 = 309197) B309197
theorem B173377 : Blo 119786 173377 := bstep (se 2 (by rfl) ⟨65016, by rfl⟩ : syracuseStep 173377 = 130033) B130033
theorem B206273 : Blo 119786 206273 := bstep (se 2 (by rfl) ⟨77352, by rfl⟩ : syracuseStep 206273 = 154705) B154705
theorem B271889 : Blo 119786 271889 := bstep (se 2 (by rfl) ⟨101958, by rfl⟩ : syracuseStep 271889 = 203917) B203917
theorem B271907 : Blo 119786 271907 := bstep (se 1 (by rfl) ⟨203930, by rfl⟩ : syracuseStep 271907 = 407861) B407861
theorem B206401 : Blo 119786 206401 := bstep (se 2 (by rfl) ⟨77400, by rfl⟩ : syracuseStep 206401 = 154801) B154801
theorem B206435 : Blo 119786 206435 := bstep (se 1 (by rfl) ⟨154826, by rfl⟩ : syracuseStep 206435 = 309653) B309653
theorem B206563 : Blo 119786 206563 := bstep (se 1 (by rfl) ⟨154922, by rfl⟩ : syracuseStep 206563 = 309845) B309845
theorem B272177 : Blo 119786 272177 := bstep (se 2 (by rfl) ⟨102066, by rfl⟩ : syracuseStep 272177 = 204133) B204133
theorem B272195 : Blo 119786 272195 := bstep (se 1 (by rfl) ⟨204146, by rfl⟩ : syracuseStep 272195 = 408293) B408293
theorem B206705 : Blo 119786 206705 := bstep (se 2 (by rfl) ⟨77514, by rfl⟩ : syracuseStep 206705 = 155029) B155029
theorem B468899 : Blo 119786 468899 := bstep (se 1 (by rfl) ⟨351674, by rfl⟩ : syracuseStep 468899 = 703349) B703349
theorem B206833 : Blo 119786 206833 := bstep (se 2 (by rfl) ⟨77562, by rfl⟩ : syracuseStep 206833 = 155125) B155125
theorem B206867 : Blo 119786 206867 := bstep (se 1 (by rfl) ⟨155150, by rfl⟩ : syracuseStep 206867 = 310301) B310301
theorem B272465 : Blo 119786 272465 := bstep (se 2 (by rfl) ⟨102174, by rfl⟩ : syracuseStep 272465 = 204349) B204349
theorem B174163 : Blo 119786 174163 := bstep (se 1 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 174163 = 261245) B261245
theorem B272483 : Blo 119786 272483 := bstep (se 1 (by rfl) ⟨204362, by rfl⟩ : syracuseStep 272483 = 408725) B408725
theorem B206995 : Blo 119786 206995 := bstep (se 1 (by rfl) ⟨155246, by rfl⟩ : syracuseStep 206995 = 310493) B310493
theorem B305329 : Blo 119786 305329 := bstep (se 2 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 305329 = 228997) B228997
theorem B2009285 : Blo 119786 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B207137 : Blo 119786 207137 := bstep (se 2 (by rfl) ⟨77676, by rfl⟩ : syracuseStep 207137 = 155353) B155353
theorem B272753 : Blo 119786 272753 := bstep (se 2 (by rfl) ⟨102282, by rfl⟩ : syracuseStep 272753 = 204565) B204565
theorem B272771 : Blo 119786 272771 := bstep (se 1 (by rfl) ⟨204578, by rfl⟩ : syracuseStep 272771 = 409157) B409157
theorem B207265 : Blo 119786 207265 := bstep (se 2 (by rfl) ⟨77724, by rfl⟩ : syracuseStep 207265 = 155449) B155449
theorem B305603 : Blo 119786 305603 := bstep (se 1 (by rfl) ⟨229202, by rfl⟩ : syracuseStep 305603 = 458405) B458405
theorem B207299 : Blo 119786 207299 := bstep (se 1 (by rfl) ⟨155474, by rfl⟩ : syracuseStep 207299 = 310949) B310949
theorem B174641 : Blo 119786 174641 := bstep (se 2 (by rfl) ⟨65490, by rfl⟩ : syracuseStep 174641 = 130981) B130981
theorem B207427 : Blo 119786 207427 := bstep (se 1 (by rfl) ⟨155570, by rfl⟩ : syracuseStep 207427 = 311141) B311141
theorem B305795 : Blo 119786 305795 := bstep (se 1 (by rfl) ⟨229346, by rfl⟩ : syracuseStep 305795 = 458693) B458693
theorem B240259 : Blo 119786 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B273041 : Blo 119786 273041 := bstep (se 2 (by rfl) ⟨102390, by rfl⟩ : syracuseStep 273041 = 204781) B204781
theorem B273059 : Blo 119786 273059 := bstep (se 1 (by rfl) ⟨204794, by rfl⟩ : syracuseStep 273059 = 409589) B409589
theorem B174755 : Blo 119786 174755 := bstep (se 1 (by rfl) ⟨131066, by rfl⟩ : syracuseStep 174755 = 262133) B262133
theorem B207569 : Blo 119786 207569 := bstep (se 2 (by rfl) ⟨77838, by rfl⟩ : syracuseStep 207569 = 155677) B155677
theorem B174835 : Blo 119786 174835 := bstep (se 1 (by rfl) ⟨131126, by rfl⟩ : syracuseStep 174835 = 262253) B262253
theorem B207697 : Blo 119786 207697 := bstep (se 2 (by rfl) ⟨77886, by rfl⟩ : syracuseStep 207697 = 155773) B155773
theorem B207731 : Blo 119786 207731 := bstep (se 1 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 207731 = 311597) B311597
theorem B469901 : Blo 119786 469901 := bstep (se 3 (by rfl) ⟨88106, by rfl⟩ : syracuseStep 469901 = 176213) B176213
theorem B273329 : Blo 119786 273329 := bstep (se 2 (by rfl) ⟨102498, by rfl⟩ : syracuseStep 273329 = 204997) B204997
theorem B273347 : Blo 119786 273347 := bstep (se 1 (by rfl) ⟨205010, by rfl⟩ : syracuseStep 273347 = 410021) B410021
theorem B207859 : Blo 119786 207859 := bstep (se 1 (by rfl) ⟨155894, by rfl⟩ : syracuseStep 207859 = 311789) B311789
theorem B1551473 : Blo 119786 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B208001 : Blo 119786 208001 := bstep (se 2 (by rfl) ⟨78000, by rfl⟩ : syracuseStep 208001 = 156001) B156001
theorem B273539 : Blo 119786 273539 := bstep (se 1 (by rfl) ⟨205154, by rfl⟩ : syracuseStep 273539 = 410309) B410309
theorem B404621 : Blo 119786 404621 := bstep (se 3 (by rfl) ⟨75866, by rfl⟩ : syracuseStep 404621 = 151733) B151733
theorem B404675 : Blo 119786 404675 := bstep (se 1 (by rfl) ⟨303506, by rfl⟩ : syracuseStep 404675 = 607013) B607013
theorem B273617 : Blo 119786 273617 := bstep (se 2 (by rfl) ⟨102606, by rfl⟩ : syracuseStep 273617 = 205213) B205213
theorem B273635 : Blo 119786 273635 := bstep (se 1 (by rfl) ⟨205226, by rfl⟩ : syracuseStep 273635 = 410453) B410453
theorem B208129 : Blo 119786 208129 := bstep (se 2 (by rfl) ⟨78048, by rfl⟩ : syracuseStep 208129 = 156097) B156097
theorem B175393 : Blo 119786 175393 := bstep (se 2 (by rfl) ⟨65772, by rfl⟩ : syracuseStep 175393 = 131545) B131545
theorem B208163 : Blo 119786 208163 := bstep (se 1 (by rfl) ⟨156122, by rfl⟩ : syracuseStep 208163 = 312245) B312245
theorem B208291 : Blo 119786 208291 := bstep (se 1 (by rfl) ⟨156218, by rfl⟩ : syracuseStep 208291 = 312437) B312437
theorem B404945 : Blo 119786 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B273905 : Blo 119786 273905 := bstep (se 2 (by rfl) ⟨102714, by rfl⟩ : syracuseStep 273905 = 205429) B205429
theorem B273923 : Blo 119786 273923 := bstep (se 1 (by rfl) ⟨205442, by rfl⟩ : syracuseStep 273923 = 410885) B410885
theorem B306737 : Blo 119786 306737 := bstep (se 2 (by rfl) ⟨115026, by rfl⟩ : syracuseStep 306737 = 230053) B230053
theorem B208433 : Blo 119786 208433 := bstep (se 2 (by rfl) ⟨78162, by rfl⟩ : syracuseStep 208433 = 156325) B156325
theorem B306787 : Blo 119786 306787 := bstep (se 1 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 306787 = 460181) B460181
theorem B208561 : Blo 119786 208561 := bstep (se 2 (by rfl) ⟨78210, by rfl⟩ : syracuseStep 208561 = 156421) B156421
theorem B208595 : Blo 119786 208595 := bstep (se 1 (by rfl) ⟨156446, by rfl⟩ : syracuseStep 208595 = 312893) B312893
theorem B306929 : Blo 119786 306929 := bstep (se 2 (by rfl) ⟨115098, by rfl⟩ : syracuseStep 306929 = 230197) B230197
theorem B274193 : Blo 119786 274193 := bstep (se 2 (by rfl) ⟨102822, by rfl⟩ : syracuseStep 274193 = 205645) B205645
theorem B274211 : Blo 119786 274211 := bstep (se 1 (by rfl) ⟨205658, by rfl⟩ : syracuseStep 274211 = 411317) B411317
theorem B208723 : Blo 119786 208723 := bstep (se 1 (by rfl) ⟨156542, by rfl⟩ : syracuseStep 208723 = 313085) B313085
theorem B176033 : Blo 119786 176033 := bstep (se 2 (by rfl) ⟨66012, by rfl⟩ : syracuseStep 176033 = 132025) B132025
theorem B208865 : Blo 119786 208865 := bstep (se 2 (by rfl) ⟨78324, by rfl⟩ : syracuseStep 208865 = 156649) B156649
theorem B176099 : Blo 119786 176099 := bstep (se 1 (by rfl) ⟨132074, by rfl⟩ : syracuseStep 176099 = 264149) B264149
theorem B405485 : Blo 119786 405485 := bstep (se 3 (by rfl) ⟨76028, by rfl⟩ : syracuseStep 405485 = 152057) B152057
theorem B405539 : Blo 119786 405539 := bstep (se 1 (by rfl) ⟨304154, by rfl⟩ : syracuseStep 405539 = 608309) B608309
theorem B274481 : Blo 119786 274481 := bstep (se 2 (by rfl) ⟨102930, by rfl⟩ : syracuseStep 274481 = 205861) B205861
theorem B274499 : Blo 119786 274499 := bstep (se 1 (by rfl) ⟨205874, by rfl⟩ : syracuseStep 274499 = 411749) B411749
theorem B176257 : Blo 119786 176257 := bstep (se 2 (by rfl) ⟨66096, by rfl⟩ : syracuseStep 176257 = 132193) B132193
theorem B372977 : Blo 119786 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B405809 : Blo 119786 405809 := bstep (se 2 (by rfl) ⟨152178, by rfl⟩ : syracuseStep 405809 = 304357) B304357
theorem B274769 : Blo 119786 274769 := bstep (se 2 (by rfl) ⟨103038, by rfl⟩ : syracuseStep 274769 = 206077) B206077
theorem B274787 : Blo 119786 274787 := bstep (se 1 (by rfl) ⟨206090, by rfl⟩ : syracuseStep 274787 = 412181) B412181
theorem B1323377 : Blo 119786 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B700933 : Blo 119786 700933 := bstep (se 4 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 700933 = 131425) B131425
theorem B275057 : Blo 119786 275057 := bstep (se 2 (by rfl) ⟨103146, by rfl⟩ : syracuseStep 275057 = 206293) B206293
theorem B275075 : Blo 119786 275075 := bstep (se 1 (by rfl) ⟨206306, by rfl⟩ : syracuseStep 275075 = 412613) B412613
theorem B438947 : Blo 119786 438947 := bstep (se 1 (by rfl) ⟨329210, by rfl⟩ : syracuseStep 438947 = 658421) B658421
theorem B144067 : Blo 119786 144067 := bstep (se 1 (by rfl) ⟨108050, by rfl⟩ : syracuseStep 144067 = 216101) B216101
theorem B307921 : Blo 119786 307921 := bstep (se 2 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 307921 = 230941) B230941
theorem B144163 : Blo 119786 144163 := bstep (se 1 (by rfl) ⟨108122, by rfl⟩ : syracuseStep 144163 = 216245) B216245
theorem B406349 : Blo 119786 406349 := bstep (se 3 (by rfl) ⟨76190, by rfl⟩ : syracuseStep 406349 = 152381) B152381
theorem B209747 : Blo 119786 209747 := bstep (se 1 (by rfl) ⟨157310, by rfl⟩ : syracuseStep 209747 = 314621) B314621
theorem B406403 : Blo 119786 406403 := bstep (se 1 (by rfl) ⟨304802, by rfl⟩ : syracuseStep 406403 = 609605) B609605
theorem B275345 : Blo 119786 275345 := bstep (se 2 (by rfl) ⟨103254, by rfl⟩ : syracuseStep 275345 = 206509) B206509
theorem B275363 : Blo 119786 275363 := bstep (se 1 (by rfl) ⟨206522, by rfl⟩ : syracuseStep 275363 = 413045) B413045
theorem B308195 : Blo 119786 308195 := bstep (se 1 (by rfl) ⟨231146, by rfl⟩ : syracuseStep 308195 = 462293) B462293
theorem B406673 : Blo 119786 406673 := bstep (se 2 (by rfl) ⟨152502, by rfl⟩ : syracuseStep 406673 = 305005) B305005
theorem B144547 : Blo 119786 144547 := bstep (se 1 (by rfl) ⟨108410, by rfl⟩ : syracuseStep 144547 = 216821) B216821
theorem B308387 : Blo 119786 308387 := bstep (se 1 (by rfl) ⟨231290, by rfl⟩ : syracuseStep 308387 = 462581) B462581
theorem B275633 : Blo 119786 275633 := bstep (se 2 (by rfl) ⟨103362, by rfl⟩ : syracuseStep 275633 = 206725) B206725
theorem B275651 : Blo 119786 275651 := bstep (se 1 (by rfl) ⟨206738, by rfl⟩ : syracuseStep 275651 = 413477) B413477
theorem B2700485 : Blo 119786 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B373987 : Blo 119786 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B3880163 : Blo 119786 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B275729 : Blo 119786 275729 := bstep (se 2 (by rfl) ⟨103398, by rfl⟩ : syracuseStep 275729 = 206797) B206797
theorem B275921 : Blo 119786 275921 := bstep (se 2 (by rfl) ⟨103470, by rfl⟩ : syracuseStep 275921 = 206941) B206941
theorem B275939 : Blo 119786 275939 := bstep (se 1 (by rfl) ⟨206954, by rfl⟩ : syracuseStep 275939 = 413909) B413909
theorem B341617 : Blo 119786 341617 := bstep (se 2 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 341617 = 256213) B256213
theorem B407213 : Blo 119786 407213 := bstep (se 3 (by rfl) ⟨76352, by rfl⟩ : syracuseStep 407213 = 152705) B152705
theorem B407267 : Blo 119786 407267 := bstep (se 1 (by rfl) ⟨305450, by rfl⟩ : syracuseStep 407267 = 610901) B610901
theorem B276209 : Blo 119786 276209 := bstep (se 2 (by rfl) ⟨103578, by rfl⟩ : syracuseStep 276209 = 207157) B207157
theorem B276227 : Blo 119786 276227 := bstep (se 1 (by rfl) ⟨207170, by rfl⟩ : syracuseStep 276227 = 414341) B414341
theorem B767843 : Blo 119786 767843 := bstep (se 1 (by rfl) ⟨575882, by rfl⟩ : syracuseStep 767843 = 1151765) B1151765
theorem B341891 : Blo 119786 341891 := bstep (se 1 (by rfl) ⟨256418, by rfl⟩ : syracuseStep 341891 = 512837) B512837
theorem B866189 : Blo 119786 866189 := bstep (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) B324821
theorem B243665 : Blo 119786 243665 := bstep (se 2 (by rfl) ⟨91374, by rfl⟩ : syracuseStep 243665 = 182749) B182749
theorem B407537 : Blo 119786 407537 := bstep (se 2 (by rfl) ⟨152826, by rfl⟩ : syracuseStep 407537 = 305653) B305653
theorem B276497 : Blo 119786 276497 := bstep (se 2 (by rfl) ⟨103686, by rfl⟩ : syracuseStep 276497 = 207373) B207373
theorem B276515 : Blo 119786 276515 := bstep (se 1 (by rfl) ⟨207386, by rfl⟩ : syracuseStep 276515 = 414773) B414773
theorem B342083 : Blo 119786 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B309329 : Blo 119786 309329 := bstep (se 2 (by rfl) ⟨115998, by rfl⟩ : syracuseStep 309329 = 231997) B231997
theorem B309379 : Blo 119786 309379 := bstep (se 1 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 309379 = 464069) B464069
theorem B309521 : Blo 119786 309521 := bstep (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) B232141
theorem B768305 : Blo 119786 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B276785 : Blo 119786 276785 := bstep (se 2 (by rfl) ⟨103794, by rfl⟩ : syracuseStep 276785 = 207589) B207589
theorem B276803 : Blo 119786 276803 := bstep (se 1 (by rfl) ⟨207602, by rfl⟩ : syracuseStep 276803 = 415205) B415205
theorem B702917 : Blo 119786 702917 := bstep (se 4 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 702917 = 131797) B131797
theorem B408077 : Blo 119786 408077 := bstep (se 3 (by rfl) ⟨76514, by rfl⟩ : syracuseStep 408077 = 153029) B153029
theorem B408131 : Blo 119786 408131 := bstep (se 1 (by rfl) ⟨306098, by rfl⟩ : syracuseStep 408131 = 612197) B612197
theorem B440909 : Blo 119786 440909 := bstep (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) B165341
theorem B277073 : Blo 119786 277073 := bstep (se 2 (by rfl) ⟨103902, by rfl⟩ : syracuseStep 277073 = 207805) B207805
theorem B277091 : Blo 119786 277091 := bstep (se 1 (by rfl) ⟨207818, by rfl⟩ : syracuseStep 277091 = 415637) B415637
theorem B408401 : Blo 119786 408401 := bstep (se 2 (by rfl) ⟨153150, by rfl⟩ : syracuseStep 408401 = 306301) B306301
theorem B342893 : Blo 119786 342893 := bstep (se 3 (by rfl) ⟨64292, by rfl⟩ : syracuseStep 342893 = 128585) B128585
theorem B277361 : Blo 119786 277361 := bstep (se 2 (by rfl) ⟨104010, by rfl⟩ : syracuseStep 277361 = 208021) B208021
theorem B277379 : Blo 119786 277379 := bstep (se 1 (by rfl) ⟨208034, by rfl⟩ : syracuseStep 277379 = 416069) B416069
theorem B343075 : Blo 119786 343075 := bstep (se 1 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 343075 = 514613) B514613
theorem B965773 : Blo 119786 965773 := bstep (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) B362165
theorem B277649 : Blo 119786 277649 := bstep (se 2 (by rfl) ⟨104118, by rfl⟩ : syracuseStep 277649 = 208237) B208237
theorem B277667 : Blo 119786 277667 := bstep (se 1 (by rfl) ⟨208250, by rfl⟩ : syracuseStep 277667 = 416501) B416501
theorem B310513 : Blo 119786 310513 := bstep (se 2 (by rfl) ⟨116442, by rfl⟩ : syracuseStep 310513 = 232885) B232885
theorem B408941 : Blo 119786 408941 := bstep (se 3 (by rfl) ⟨76676, by rfl⟩ : syracuseStep 408941 = 153353) B153353
theorem B408995 : Blo 119786 408995 := bstep (se 1 (by rfl) ⟨306746, by rfl⟩ : syracuseStep 408995 = 613493) B613493
theorem B277937 : Blo 119786 277937 := bstep (se 2 (by rfl) ⟨104226, by rfl⟩ : syracuseStep 277937 = 208453) B208453
theorem B277955 : Blo 119786 277955 := bstep (se 1 (by rfl) ⟨208466, by rfl⟩ : syracuseStep 277955 = 416933) B416933
theorem B179681 : Blo 119786 179681 := bstep (se 2 (by rfl) ⟨67380, by rfl⟩ : syracuseStep 179681 = 134761) B134761
theorem B179699 : Blo 119786 179699 := bstep (se 1 (by rfl) ⟨134774, by rfl⟩ : syracuseStep 179699 = 269549) B269549
theorem B310787 : Blo 119786 310787 := bstep (se 1 (by rfl) ⟨233090, by rfl⟩ : syracuseStep 310787 = 466181) B466181
theorem B343565 : Blo 119786 343565 := bstep (se 3 (by rfl) ⟨64418, by rfl⟩ : syracuseStep 343565 = 128837) B128837
theorem B179729 : Blo 119786 179729 := bstep (se 2 (by rfl) ⟨67398, by rfl⟩ : syracuseStep 179729 = 134797) B134797
theorem B179747 : Blo 119786 179747 := bstep (se 1 (by rfl) ⟨134810, by rfl⟩ : syracuseStep 179747 = 269621) B269621
theorem B179777 : Blo 119786 179777 := bstep (se 2 (by rfl) ⟨67416, by rfl⟩ : syracuseStep 179777 = 134833) B134833
theorem B376397 : Blo 119786 376397 := bstep (se 3 (by rfl) ⟨70574, by rfl⟩ : syracuseStep 376397 = 141149) B141149
theorem B179795 : Blo 119786 179795 := bstep (se 1 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 179795 = 269693) B269693
theorem B179825 : Blo 119786 179825 := bstep (se 2 (by rfl) ⟨67434, by rfl⟩ : syracuseStep 179825 = 134869) B134869
theorem B179843 : Blo 119786 179843 := bstep (se 1 (by rfl) ⟨134882, by rfl⟩ : syracuseStep 179843 = 269765) B269765
theorem B179873 : Blo 119786 179873 := bstep (se 2 (by rfl) ⟨67452, by rfl⟩ : syracuseStep 179873 = 134905) B134905
theorem B409265 : Blo 119786 409265 := bstep (se 2 (by rfl) ⟨153474, by rfl⟩ : syracuseStep 409265 = 306949) B306949
theorem B179891 : Blo 119786 179891 := bstep (se 1 (by rfl) ⟨134918, by rfl⟩ : syracuseStep 179891 = 269837) B269837
theorem B310979 : Blo 119786 310979 := bstep (se 1 (by rfl) ⟨233234, by rfl⟩ : syracuseStep 310979 = 466469) B466469
theorem B179921 : Blo 119786 179921 := bstep (se 2 (by rfl) ⟨67470, by rfl⟩ : syracuseStep 179921 = 134941) B134941
theorem B278225 : Blo 119786 278225 := bstep (se 2 (by rfl) ⟨104334, by rfl⟩ : syracuseStep 278225 = 208669) B208669
theorem B179939 : Blo 119786 179939 := bstep (se 1 (by rfl) ⟨134954, by rfl⟩ : syracuseStep 179939 = 269909) B269909
theorem B278243 : Blo 119786 278243 := bstep (se 1 (by rfl) ⟨208682, by rfl⟩ : syracuseStep 278243 = 417365) B417365
theorem B179969 : Blo 119786 179969 := bstep (se 2 (by rfl) ⟨67488, by rfl⟩ : syracuseStep 179969 = 134977) B134977
theorem B179987 : Blo 119786 179987 := bstep (se 1 (by rfl) ⟨134990, by rfl⟩ : syracuseStep 179987 = 269981) B269981
theorem B180017 : Blo 119786 180017 := bstep (se 2 (by rfl) ⟨67506, by rfl⟩ : syracuseStep 180017 = 135013) B135013
theorem B180035 : Blo 119786 180035 := bstep (se 1 (by rfl) ⟨135026, by rfl⟩ : syracuseStep 180035 = 270053) B270053
theorem B180065 : Blo 119786 180065 := bstep (se 2 (by rfl) ⟨67524, by rfl⟩ : syracuseStep 180065 = 135049) B135049
theorem B180083 : Blo 119786 180083 := bstep (se 1 (by rfl) ⟨135062, by rfl⟩ : syracuseStep 180083 = 270125) B270125
theorem B2015117 : Blo 119786 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B180113 : Blo 119786 180113 := bstep (se 2 (by rfl) ⟨67542, by rfl⟩ : syracuseStep 180113 = 135085) B135085
theorem B180131 : Blo 119786 180131 := bstep (se 1 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 180131 = 270197) B270197
theorem B180161 : Blo 119786 180161 := bstep (se 2 (by rfl) ⟨67560, by rfl⟩ : syracuseStep 180161 = 135121) B135121
theorem B180179 : Blo 119786 180179 := bstep (se 1 (by rfl) ⟨135134, by rfl⟩ : syracuseStep 180179 = 270269) B270269
theorem B180209 : Blo 119786 180209 := bstep (se 2 (by rfl) ⟨67578, by rfl⟩ : syracuseStep 180209 = 135157) B135157
theorem B278513 : Blo 119786 278513 := bstep (se 2 (by rfl) ⟨104442, by rfl⟩ : syracuseStep 278513 = 208885) B208885
theorem B180227 : Blo 119786 180227 := bstep (se 1 (by rfl) ⟨135170, by rfl⟩ : syracuseStep 180227 = 270341) B270341
theorem B180257 : Blo 119786 180257 := bstep (se 2 (by rfl) ⟨67596, by rfl⟩ : syracuseStep 180257 = 135193) B135193
theorem B180275 : Blo 119786 180275 := bstep (se 1 (by rfl) ⟨135206, by rfl⟩ : syracuseStep 180275 = 270413) B270413
theorem B180305 : Blo 119786 180305 := bstep (se 2 (by rfl) ⟨67614, by rfl⟩ : syracuseStep 180305 = 135229) B135229
theorem B180323 : Blo 119786 180323 := bstep (se 1 (by rfl) ⟨135242, by rfl⟩ : syracuseStep 180323 = 270485) B270485
theorem B1065059 : Blo 119786 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B180353 : Blo 119786 180353 := bstep (se 2 (by rfl) ⟨67632, by rfl⟩ : syracuseStep 180353 = 135265) B135265
theorem B180371 : Blo 119786 180371 := bstep (se 1 (by rfl) ⟨135278, by rfl⟩ : syracuseStep 180371 = 270557) B270557
theorem B147619 : Blo 119786 147619 := bstep (se 1 (by rfl) ⟨110714, by rfl⟩ : syracuseStep 147619 = 221429) B221429
theorem B180401 : Blo 119786 180401 := bstep (se 2 (by rfl) ⟨67650, by rfl⟩ : syracuseStep 180401 = 135301) B135301
theorem B180419 : Blo 119786 180419 := bstep (se 1 (by rfl) ⟨135314, by rfl⟩ : syracuseStep 180419 = 270629) B270629
theorem B409805 : Blo 119786 409805 := bstep (se 3 (by rfl) ⟨76838, by rfl⟩ : syracuseStep 409805 = 153677) B153677
theorem B180449 : Blo 119786 180449 := bstep (se 2 (by rfl) ⟨67668, by rfl⟩ : syracuseStep 180449 = 135337) B135337
theorem B180467 : Blo 119786 180467 := bstep (se 1 (by rfl) ⟨135350, by rfl⟩ : syracuseStep 180467 = 270701) B270701
theorem B409859 : Blo 119786 409859 := bstep (se 1 (by rfl) ⟨307394, by rfl⟩ : syracuseStep 409859 = 614789) B614789
theorem B180497 : Blo 119786 180497 := bstep (se 2 (by rfl) ⟨67686, by rfl⟩ : syracuseStep 180497 = 135373) B135373
theorem B180515 : Blo 119786 180515 := bstep (se 1 (by rfl) ⟨135386, by rfl⟩ : syracuseStep 180515 = 270773) B270773
theorem B180545 : Blo 119786 180545 := bstep (se 2 (by rfl) ⟨67704, by rfl⟩ : syracuseStep 180545 = 135409) B135409
theorem B672077 : Blo 119786 672077 := bstep (se 3 (by rfl) ⟨126014, by rfl⟩ : syracuseStep 672077 = 252029) B252029
theorem B180563 : Blo 119786 180563 := bstep (se 1 (by rfl) ⟨135422, by rfl⟩ : syracuseStep 180563 = 270845) B270845
theorem B147811 : Blo 119786 147811 := bstep (se 1 (by rfl) ⟨110858, by rfl⟩ : syracuseStep 147811 = 221717) B221717
theorem B180593 : Blo 119786 180593 := bstep (se 2 (by rfl) ⟨67722, by rfl⟩ : syracuseStep 180593 = 135445) B135445
theorem B180611 : Blo 119786 180611 := bstep (se 1 (by rfl) ⟨135458, by rfl⟩ : syracuseStep 180611 = 270917) B270917
theorem B180641 : Blo 119786 180641 := bstep (se 2 (by rfl) ⟨67740, by rfl⟩ : syracuseStep 180641 = 135481) B135481
theorem B180659 : Blo 119786 180659 := bstep (se 1 (by rfl) ⟨135494, by rfl⟩ : syracuseStep 180659 = 270989) B270989
theorem B180689 : Blo 119786 180689 := bstep (se 2 (by rfl) ⟨67758, by rfl⟩ : syracuseStep 180689 = 135517) B135517
theorem B180707 : Blo 119786 180707 := bstep (se 1 (by rfl) ⟨135530, by rfl⟩ : syracuseStep 180707 = 271061) B271061
theorem B180737 : Blo 119786 180737 := bstep (se 2 (by rfl) ⟨67776, by rfl⟩ : syracuseStep 180737 = 135553) B135553
theorem B410129 : Blo 119786 410129 := bstep (se 2 (by rfl) ⟨153798, by rfl⟩ : syracuseStep 410129 = 307597) B307597
theorem B180755 : Blo 119786 180755 := bstep (se 1 (by rfl) ⟨135566, by rfl⟩ : syracuseStep 180755 = 271133) B271133
theorem B180785 : Blo 119786 180785 := bstep (se 2 (by rfl) ⟨67794, by rfl⟩ : syracuseStep 180785 = 135589) B135589
theorem B180803 : Blo 119786 180803 := bstep (se 1 (by rfl) ⟨135602, by rfl⟩ : syracuseStep 180803 = 271205) B271205
theorem B180833 : Blo 119786 180833 := bstep (se 2 (by rfl) ⟨67812, by rfl⟩ : syracuseStep 180833 = 135625) B135625
theorem B311921 : Blo 119786 311921 := bstep (se 2 (by rfl) ⟨116970, by rfl⟩ : syracuseStep 311921 = 233941) B233941
theorem B180851 : Blo 119786 180851 := bstep (se 1 (by rfl) ⟨135638, by rfl⟩ : syracuseStep 180851 = 271277) B271277
theorem B180881 : Blo 119786 180881 := bstep (se 2 (by rfl) ⟨67830, by rfl⟩ : syracuseStep 180881 = 135661) B135661
theorem B180899 : Blo 119786 180899 := bstep (se 1 (by rfl) ⟨135674, by rfl⟩ : syracuseStep 180899 = 271349) B271349
theorem B311971 : Blo 119786 311971 := bstep (se 1 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 311971 = 467957) B467957
theorem B344749 : Blo 119786 344749 := bstep (se 3 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 344749 = 129281) B129281
theorem B180929 : Blo 119786 180929 := bstep (se 2 (by rfl) ⟨67848, by rfl⟩ : syracuseStep 180929 = 135697) B135697
theorem B180947 : Blo 119786 180947 := bstep (se 1 (by rfl) ⟨135710, by rfl⟩ : syracuseStep 180947 = 271421) B271421
theorem B180977 : Blo 119786 180977 := bstep (se 2 (by rfl) ⟨67866, by rfl⟩ : syracuseStep 180977 = 135733) B135733
theorem B180995 : Blo 119786 180995 := bstep (se 1 (by rfl) ⟨135746, by rfl⟩ : syracuseStep 180995 = 271493) B271493
theorem B181025 : Blo 119786 181025 := bstep (se 2 (by rfl) ⟨67884, by rfl⟩ : syracuseStep 181025 = 135769) B135769
theorem B312113 : Blo 119786 312113 := bstep (se 2 (by rfl) ⟨117042, by rfl⟩ : syracuseStep 312113 = 234085) B234085
theorem B181043 : Blo 119786 181043 := bstep (se 1 (by rfl) ⟨135782, by rfl⟩ : syracuseStep 181043 = 271565) B271565
theorem B181073 : Blo 119786 181073 := bstep (se 2 (by rfl) ⟨67902, by rfl⟩ : syracuseStep 181073 = 135805) B135805
theorem B279377 : Blo 119786 279377 := bstep (se 2 (by rfl) ⟨104766, by rfl⟩ : syracuseStep 279377 = 209533) B209533
theorem B181091 : Blo 119786 181091 := bstep (se 1 (by rfl) ⟨135818, by rfl⟩ : syracuseStep 181091 = 271637) B271637
theorem B181121 : Blo 119786 181121 := bstep (se 2 (by rfl) ⟨67920, by rfl⟩ : syracuseStep 181121 = 135841) B135841
theorem B181139 : Blo 119786 181139 := bstep (se 1 (by rfl) ⟨135854, by rfl⟩ : syracuseStep 181139 = 271709) B271709
theorem B181169 : Blo 119786 181169 := bstep (se 2 (by rfl) ⟨67938, by rfl⟩ : syracuseStep 181169 = 135877) B135877
theorem B181187 : Blo 119786 181187 := bstep (se 1 (by rfl) ⟨135890, by rfl⟩ : syracuseStep 181187 = 271781) B271781
theorem B181217 : Blo 119786 181217 := bstep (se 2 (by rfl) ⟨67956, by rfl⟩ : syracuseStep 181217 = 135913) B135913
theorem B934897 : Blo 119786 934897 := bstep (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) B701173
theorem B181235 : Blo 119786 181235 := bstep (se 1 (by rfl) ⟨135926, by rfl⟩ : syracuseStep 181235 = 271853) B271853
theorem B181265 : Blo 119786 181265 := bstep (se 2 (by rfl) ⟨67974, by rfl⟩ : syracuseStep 181265 = 135949) B135949
theorem B181283 : Blo 119786 181283 := bstep (se 1 (by rfl) ⟨135962, by rfl⟩ : syracuseStep 181283 = 271925) B271925
theorem B410669 : Blo 119786 410669 := bstep (se 3 (by rfl) ⟨77000, by rfl⟩ : syracuseStep 410669 = 154001) B154001
theorem B181313 : Blo 119786 181313 := bstep (se 2 (by rfl) ⟨67992, by rfl⟩ : syracuseStep 181313 = 135985) B135985
theorem B181331 : Blo 119786 181331 := bstep (se 1 (by rfl) ⟨135998, by rfl⟩ : syracuseStep 181331 = 271997) B271997
theorem B410723 : Blo 119786 410723 := bstep (se 1 (by rfl) ⟨308042, by rfl⟩ : syracuseStep 410723 = 616085) B616085
theorem B181361 : Blo 119786 181361 := bstep (se 2 (by rfl) ⟨68010, by rfl⟩ : syracuseStep 181361 = 136021) B136021
theorem B181379 : Blo 119786 181379 := bstep (se 1 (by rfl) ⟨136034, by rfl⟩ : syracuseStep 181379 = 272069) B272069
theorem B1033357 : Blo 119786 1033357 := bstep (se 3 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 1033357 = 387509) B387509
theorem B181409 : Blo 119786 181409 := bstep (se 2 (by rfl) ⟨68028, by rfl⟩ : syracuseStep 181409 = 136057) B136057
theorem B181427 : Blo 119786 181427 := bstep (se 1 (by rfl) ⟨136070, by rfl⟩ : syracuseStep 181427 = 272141) B272141
theorem B181457 : Blo 119786 181457 := bstep (se 2 (by rfl) ⟨68046, by rfl⟩ : syracuseStep 181457 = 136093) B136093
theorem B181475 : Blo 119786 181475 := bstep (se 1 (by rfl) ⟨136106, by rfl⟩ : syracuseStep 181475 = 272213) B272213
theorem B181505 : Blo 119786 181505 := bstep (se 2 (by rfl) ⟨68064, by rfl⟩ : syracuseStep 181505 = 136129) B136129
theorem B181523 : Blo 119786 181523 := bstep (se 1 (by rfl) ⟨136142, by rfl⟩ : syracuseStep 181523 = 272285) B272285
theorem B181553 : Blo 119786 181553 := bstep (se 2 (by rfl) ⟨68082, by rfl⟩ : syracuseStep 181553 = 136165) B136165
theorem B181571 : Blo 119786 181571 := bstep (se 1 (by rfl) ⟨136178, by rfl⟩ : syracuseStep 181571 = 272357) B272357
theorem B181601 : Blo 119786 181601 := bstep (se 2 (by rfl) ⟨68100, by rfl⟩ : syracuseStep 181601 = 136201) B136201
theorem B410993 : Blo 119786 410993 := bstep (se 2 (by rfl) ⟨154122, by rfl⟩ : syracuseStep 410993 = 308245) B308245
theorem B181619 : Blo 119786 181619 := bstep (se 1 (by rfl) ⟨136214, by rfl⟩ : syracuseStep 181619 = 272429) B272429
theorem B181649 : Blo 119786 181649 := bstep (se 2 (by rfl) ⟨68118, by rfl⟩ : syracuseStep 181649 = 136237) B136237
theorem B181667 : Blo 119786 181667 := bstep (se 1 (by rfl) ⟨136250, by rfl⟩ : syracuseStep 181667 = 272501) B272501
theorem B181697 : Blo 119786 181697 := bstep (se 2 (by rfl) ⟨68136, by rfl⟩ : syracuseStep 181697 = 136273) B136273
theorem B247249 : Blo 119786 247249 := bstep (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) B185437
theorem B181715 : Blo 119786 181715 := bstep (se 1 (by rfl) ⟨136286, by rfl⟩ : syracuseStep 181715 = 272573) B272573
theorem B181745 : Blo 119786 181745 := bstep (se 2 (by rfl) ⟨68154, by rfl⟩ : syracuseStep 181745 = 136309) B136309
theorem B181763 : Blo 119786 181763 := bstep (se 1 (by rfl) ⟨136322, by rfl⟩ : syracuseStep 181763 = 272645) B272645
theorem B181793 : Blo 119786 181793 := bstep (se 2 (by rfl) ⟨68172, by rfl⟩ : syracuseStep 181793 = 136345) B136345
theorem B181811 : Blo 119786 181811 := bstep (se 1 (by rfl) ⟨136358, by rfl⟩ : syracuseStep 181811 = 272717) B272717
theorem B181841 : Blo 119786 181841 := bstep (se 2 (by rfl) ⟨68190, by rfl⟩ : syracuseStep 181841 = 136381) B136381
theorem B181859 : Blo 119786 181859 := bstep (se 1 (by rfl) ⟨136394, by rfl⟩ : syracuseStep 181859 = 272789) B272789
theorem B181889 : Blo 119786 181889 := bstep (se 2 (by rfl) ⟨68208, by rfl⟩ : syracuseStep 181889 = 136417) B136417
theorem B181907 : Blo 119786 181907 := bstep (se 1 (by rfl) ⟨136430, by rfl⟩ : syracuseStep 181907 = 272861) B272861
theorem B181937 : Blo 119786 181937 := bstep (se 2 (by rfl) ⟨68226, by rfl⟩ : syracuseStep 181937 = 136453) B136453
theorem B181955 : Blo 119786 181955 := bstep (se 1 (by rfl) ⟨136466, by rfl⟩ : syracuseStep 181955 = 272933) B272933
theorem B345809 : Blo 119786 345809 := bstep (se 2 (by rfl) ⟨129678, by rfl⟩ : syracuseStep 345809 = 259357) B259357
theorem B181985 : Blo 119786 181985 := bstep (se 2 (by rfl) ⟨68244, by rfl⟩ : syracuseStep 181985 = 136489) B136489
theorem B607985 : Blo 119786 607985 := bstep (se 2 (by rfl) ⟨227994, by rfl⟩ : syracuseStep 607985 = 455989) B455989
theorem B182003 : Blo 119786 182003 := bstep (se 1 (by rfl) ⟨136502, by rfl⟩ : syracuseStep 182003 = 273005) B273005
theorem B313091 : Blo 119786 313091 := bstep (se 1 (by rfl) ⟨234818, by rfl⟩ : syracuseStep 313091 = 469637) B469637
theorem B182033 : Blo 119786 182033 := bstep (se 2 (by rfl) ⟨68262, by rfl⟩ : syracuseStep 182033 = 136525) B136525
theorem B313105 : Blo 119786 313105 := bstep (se 2 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 313105 = 234829) B234829
theorem B182051 : Blo 119786 182051 := bstep (se 1 (by rfl) ⟨136538, by rfl⟩ : syracuseStep 182051 = 273077) B273077
theorem B182081 : Blo 119786 182081 := bstep (se 2 (by rfl) ⟨68280, by rfl⟩ : syracuseStep 182081 = 136561) B136561
theorem B182099 : Blo 119786 182099 := bstep (se 1 (by rfl) ⟨136574, by rfl⟩ : syracuseStep 182099 = 273149) B273149
theorem B182129 : Blo 119786 182129 := bstep (se 2 (by rfl) ⟨68298, by rfl⟩ : syracuseStep 182129 = 136597) B136597
theorem B182147 : Blo 119786 182147 := bstep (se 1 (by rfl) ⟨136610, by rfl⟩ : syracuseStep 182147 = 273221) B273221
theorem B411533 : Blo 119786 411533 := bstep (se 3 (by rfl) ⟨77162, by rfl⟩ : syracuseStep 411533 = 154325) B154325
theorem B378769 : Blo 119786 378769 := bstep (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) B284077
theorem B182177 : Blo 119786 182177 := bstep (se 2 (by rfl) ⟨68316, by rfl⟩ : syracuseStep 182177 = 136633) B136633
theorem B182195 : Blo 119786 182195 := bstep (se 1 (by rfl) ⟨136646, by rfl⟩ : syracuseStep 182195 = 273293) B273293
theorem B1427381 : Blo 119786 1427381 := bstep (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) B133817
theorem B411587 : Blo 119786 411587 := bstep (se 1 (by rfl) ⟨308690, by rfl⟩ : syracuseStep 411587 = 617381) B617381
theorem B182225 : Blo 119786 182225 := bstep (se 2 (by rfl) ⟨68334, by rfl⟩ : syracuseStep 182225 = 136669) B136669
theorem B182243 : Blo 119786 182243 := bstep (se 1 (by rfl) ⟨136682, by rfl⟩ : syracuseStep 182243 = 273365) B273365
theorem B280547 : Blo 119786 280547 := bstep (se 1 (by rfl) ⟨210410, by rfl⟩ : syracuseStep 280547 = 420821) B420821
theorem B182273 : Blo 119786 182273 := bstep (se 2 (by rfl) ⟨68352, by rfl⟩ : syracuseStep 182273 = 136705) B136705
theorem B182291 : Blo 119786 182291 := bstep (se 1 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 182291 = 273437) B273437
theorem B182321 : Blo 119786 182321 := bstep (se 2 (by rfl) ⟨68370, by rfl⟩ : syracuseStep 182321 = 136741) B136741
theorem B182339 : Blo 119786 182339 := bstep (se 1 (by rfl) ⟨136754, by rfl⟩ : syracuseStep 182339 = 273509) B273509
theorem B182369 : Blo 119786 182369 := bstep (se 2 (by rfl) ⟨68388, by rfl⟩ : syracuseStep 182369 = 136777) B136777
theorem B936035 : Blo 119786 936035 := bstep (se 1 (by rfl) ⟨702026, by rfl⟩ : syracuseStep 936035 = 1404053) B1404053
theorem B182387 : Blo 119786 182387 := bstep (se 1 (by rfl) ⟨136790, by rfl⟩ : syracuseStep 182387 = 273581) B273581
theorem B182417 : Blo 119786 182417 := bstep (se 2 (by rfl) ⟨68406, by rfl⟩ : syracuseStep 182417 = 136813) B136813
theorem B182435 : Blo 119786 182435 := bstep (se 1 (by rfl) ⟨136826, by rfl⟩ : syracuseStep 182435 = 273653) B273653
theorem B182465 : Blo 119786 182465 := bstep (se 2 (by rfl) ⟨68424, by rfl⟩ : syracuseStep 182465 = 136849) B136849
theorem B411857 : Blo 119786 411857 := bstep (se 2 (by rfl) ⟨154446, by rfl⟩ : syracuseStep 411857 = 308893) B308893
theorem B182483 : Blo 119786 182483 := bstep (se 1 (by rfl) ⟨136862, by rfl⟩ : syracuseStep 182483 = 273725) B273725
theorem B182513 : Blo 119786 182513 := bstep (se 2 (by rfl) ⟨68442, by rfl⟩ : syracuseStep 182513 = 136885) B136885
theorem B182531 : Blo 119786 182531 := bstep (se 1 (by rfl) ⟨136898, by rfl⟩ : syracuseStep 182531 = 273797) B273797
theorem B182561 : Blo 119786 182561 := bstep (se 2 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 182561 = 136921) B136921
theorem B182579 : Blo 119786 182579 := bstep (se 1 (by rfl) ⟨136934, by rfl⟩ : syracuseStep 182579 = 273869) B273869
theorem B182609 : Blo 119786 182609 := bstep (se 2 (by rfl) ⟨68478, by rfl⟩ : syracuseStep 182609 = 136957) B136957
theorem B182627 : Blo 119786 182627 := bstep (se 1 (by rfl) ⟨136970, by rfl⟩ : syracuseStep 182627 = 273941) B273941
theorem B346481 : Blo 119786 346481 := bstep (se 2 (by rfl) ⟨129930, by rfl⟩ : syracuseStep 346481 = 259861) B259861
theorem B182657 : Blo 119786 182657 := bstep (se 2 (by rfl) ⟨68496, by rfl⟩ : syracuseStep 182657 = 136993) B136993
theorem B182675 : Blo 119786 182675 := bstep (se 1 (by rfl) ⟨137006, by rfl⟩ : syracuseStep 182675 = 274013) B274013
theorem B182705 : Blo 119786 182705 := bstep (se 2 (by rfl) ⟨68514, by rfl⟩ : syracuseStep 182705 = 137029) B137029
theorem B182723 : Blo 119786 182723 := bstep (se 1 (by rfl) ⟨137042, by rfl⟩ : syracuseStep 182723 = 274085) B274085
theorem B1034693 : Blo 119786 1034693 := bstep (se 4 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 1034693 = 194005) B194005
theorem B1329605 : Blo 119786 1329605 := bstep (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) B249301
theorem B182753 : Blo 119786 182753 := bstep (se 2 (by rfl) ⟨68532, by rfl⟩ : syracuseStep 182753 = 137065) B137065
theorem B510449 : Blo 119786 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B182771 : Blo 119786 182771 := bstep (se 1 (by rfl) ⟨137078, by rfl⟩ : syracuseStep 182771 = 274157) B274157
theorem B182801 : Blo 119786 182801 := bstep (se 2 (by rfl) ⟨68550, by rfl⟩ : syracuseStep 182801 = 137101) B137101
theorem B182819 : Blo 119786 182819 := bstep (se 1 (by rfl) ⟨137114, by rfl⟩ : syracuseStep 182819 = 274229) B274229
theorem B182849 : Blo 119786 182849 := bstep (se 2 (by rfl) ⟨68568, by rfl⟩ : syracuseStep 182849 = 137137) B137137
theorem B182867 : Blo 119786 182867 := bstep (se 1 (by rfl) ⟨137150, by rfl⟩ : syracuseStep 182867 = 274301) B274301
theorem B182897 : Blo 119786 182897 := bstep (se 2 (by rfl) ⟨68586, by rfl⟩ : syracuseStep 182897 = 137173) B137173
theorem B182915 : Blo 119786 182915 := bstep (se 1 (by rfl) ⟨137186, by rfl⟩ : syracuseStep 182915 = 274373) B274373
theorem B248465 : Blo 119786 248465 := bstep (se 2 (by rfl) ⟨93174, by rfl⟩ : syracuseStep 248465 = 186349) B186349
theorem B182945 : Blo 119786 182945 := bstep (se 2 (by rfl) ⟨68604, by rfl⟩ : syracuseStep 182945 = 137209) B137209
theorem B182963 : Blo 119786 182963 := bstep (se 1 (by rfl) ⟨137222, by rfl⟩ : syracuseStep 182963 = 274445) B274445
theorem B182993 : Blo 119786 182993 := bstep (se 2 (by rfl) ⟨68622, by rfl⟩ : syracuseStep 182993 = 137245) B137245
theorem B183011 : Blo 119786 183011 := bstep (se 1 (by rfl) ⟨137258, by rfl⟩ : syracuseStep 183011 = 274517) B274517
theorem B412397 : Blo 119786 412397 := bstep (se 3 (by rfl) ⟨77324, by rfl⟩ : syracuseStep 412397 = 154649) B154649
theorem B183041 : Blo 119786 183041 := bstep (se 2 (by rfl) ⟨68640, by rfl⟩ : syracuseStep 183041 = 137281) B137281
theorem B183059 : Blo 119786 183059 := bstep (se 1 (by rfl) ⟨137294, by rfl⟩ : syracuseStep 183059 = 274589) B274589
theorem B412451 : Blo 119786 412451 := bstep (se 1 (by rfl) ⟨309338, by rfl⟩ : syracuseStep 412451 = 618677) B618677
theorem B183089 : Blo 119786 183089 := bstep (se 2 (by rfl) ⟨68658, by rfl⟩ : syracuseStep 183089 = 137317) B137317
theorem B183107 : Blo 119786 183107 := bstep (se 1 (by rfl) ⟨137330, by rfl⟩ : syracuseStep 183107 = 274661) B274661
theorem B183137 : Blo 119786 183137 := bstep (se 2 (by rfl) ⟨68676, by rfl⟩ : syracuseStep 183137 = 137353) B137353
theorem B183155 : Blo 119786 183155 := bstep (se 1 (by rfl) ⟨137366, by rfl⟩ : syracuseStep 183155 = 274733) B274733
theorem B183185 : Blo 119786 183185 := bstep (se 2 (by rfl) ⟨68694, by rfl⟩ : syracuseStep 183185 = 137389) B137389
theorem B183203 : Blo 119786 183203 := bstep (se 1 (by rfl) ⟨137402, by rfl⟩ : syracuseStep 183203 = 274805) B274805
theorem B183233 : Blo 119786 183233 := bstep (se 2 (by rfl) ⟨68712, by rfl⟩ : syracuseStep 183233 = 137425) B137425
theorem B183251 : Blo 119786 183251 := bstep (se 1 (by rfl) ⟨137438, by rfl⟩ : syracuseStep 183251 = 274877) B274877
theorem B576497 : Blo 119786 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B183281 : Blo 119786 183281 := bstep (se 2 (by rfl) ⟨68730, by rfl⟩ : syracuseStep 183281 = 137461) B137461
theorem B183299 : Blo 119786 183299 := bstep (se 1 (by rfl) ⟨137474, by rfl⟩ : syracuseStep 183299 = 274949) B274949
theorem B183329 : Blo 119786 183329 := bstep (se 2 (by rfl) ⟨68748, by rfl⟩ : syracuseStep 183329 = 137497) B137497
theorem B412721 : Blo 119786 412721 := bstep (se 2 (by rfl) ⟨154770, by rfl⟩ : syracuseStep 412721 = 309541) B309541
theorem B183347 : Blo 119786 183347 := bstep (se 1 (by rfl) ⟨137510, by rfl⟩ : syracuseStep 183347 = 275021) B275021
theorem B183377 : Blo 119786 183377 := bstep (se 2 (by rfl) ⟨68766, by rfl⟩ : syracuseStep 183377 = 137533) B137533
theorem B183395 : Blo 119786 183395 := bstep (se 1 (by rfl) ⟨137546, by rfl⟩ : syracuseStep 183395 = 275093) B275093
theorem B183425 : Blo 119786 183425 := bstep (se 2 (by rfl) ⟨68784, by rfl⟩ : syracuseStep 183425 = 137569) B137569
theorem B347267 : Blo 119786 347267 := bstep (se 1 (by rfl) ⟨260450, by rfl⟩ : syracuseStep 347267 = 520901) B520901
theorem B183443 : Blo 119786 183443 := bstep (se 1 (by rfl) ⟨137582, by rfl⟩ : syracuseStep 183443 = 275165) B275165
theorem B609443 : Blo 119786 609443 := bstep (se 1 (by rfl) ⟨457082, by rfl⟩ : syracuseStep 609443 = 914165) B914165
theorem B183473 : Blo 119786 183473 := bstep (se 2 (by rfl) ⟨68802, by rfl⟩ : syracuseStep 183473 = 137605) B137605
theorem B183491 : Blo 119786 183491 := bstep (se 1 (by rfl) ⟨137618, by rfl⟩ : syracuseStep 183491 = 275237) B275237
theorem B183521 : Blo 119786 183521 := bstep (se 2 (by rfl) ⟨68820, by rfl⟩ : syracuseStep 183521 = 137641) B137641
theorem B5950691 : Blo 119786 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B183539 : Blo 119786 183539 := bstep (se 1 (by rfl) ⟨137654, by rfl⟩ : syracuseStep 183539 = 275309) B275309
theorem B314627 : Blo 119786 314627 := bstep (se 1 (by rfl) ⟨235970, by rfl⟩ : syracuseStep 314627 = 471941) B471941
theorem B183569 : Blo 119786 183569 := bstep (se 2 (by rfl) ⟨68838, by rfl⟩ : syracuseStep 183569 = 137677) B137677
theorem B183587 : Blo 119786 183587 := bstep (se 1 (by rfl) ⟨137690, by rfl⟩ : syracuseStep 183587 = 275381) B275381
theorem B183617 : Blo 119786 183617 := bstep (se 2 (by rfl) ⟨68856, by rfl⟩ : syracuseStep 183617 = 137713) B137713
theorem B576845 : Blo 119786 576845 := bstep (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) B216317
theorem B183635 : Blo 119786 183635 := bstep (se 1 (by rfl) ⟨137726, by rfl⟩ : syracuseStep 183635 = 275453) B275453
theorem B183665 : Blo 119786 183665 := bstep (se 2 (by rfl) ⟨68874, by rfl⟩ : syracuseStep 183665 = 137749) B137749
theorem B183683 : Blo 119786 183683 := bstep (se 1 (by rfl) ⟨137762, by rfl⟩ : syracuseStep 183683 = 275525) B275525
theorem B183713 : Blo 119786 183713 := bstep (se 2 (by rfl) ⟨68892, by rfl⟩ : syracuseStep 183713 = 137785) B137785
theorem B183731 : Blo 119786 183731 := bstep (se 1 (by rfl) ⟨137798, by rfl⟩ : syracuseStep 183731 = 275597) B275597
theorem B347597 : Blo 119786 347597 := bstep (se 3 (by rfl) ⟨65174, by rfl⟩ : syracuseStep 347597 = 130349) B130349
theorem B183761 : Blo 119786 183761 := bstep (se 2 (by rfl) ⟨68910, by rfl⟩ : syracuseStep 183761 = 137821) B137821
theorem B183779 : Blo 119786 183779 := bstep (se 1 (by rfl) ⟨137834, by rfl⟩ : syracuseStep 183779 = 275669) B275669
theorem B183809 : Blo 119786 183809 := bstep (se 2 (by rfl) ⟨68928, by rfl⟩ : syracuseStep 183809 = 137857) B137857
theorem B347665 : Blo 119786 347665 := bstep (se 2 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 347665 = 260749) B260749
theorem B183827 : Blo 119786 183827 := bstep (se 1 (by rfl) ⟨137870, by rfl⟩ : syracuseStep 183827 = 275741) B275741
theorem B183857 : Blo 119786 183857 := bstep (se 2 (by rfl) ⟨68946, by rfl⟩ : syracuseStep 183857 = 137893) B137893
theorem B183875 : Blo 119786 183875 := bstep (se 1 (by rfl) ⟨137906, by rfl⟩ : syracuseStep 183875 = 275813) B275813
theorem B413261 : Blo 119786 413261 := bstep (se 3 (by rfl) ⟨77486, by rfl⟩ : syracuseStep 413261 = 154973) B154973
theorem B183905 : Blo 119786 183905 := bstep (se 2 (by rfl) ⟨68964, by rfl⟩ : syracuseStep 183905 = 137929) B137929
theorem B183923 : Blo 119786 183923 := bstep (se 1 (by rfl) ⟨137942, by rfl⟩ : syracuseStep 183923 = 275885) B275885
theorem B413315 : Blo 119786 413315 := bstep (se 1 (by rfl) ⟨309986, by rfl⟩ : syracuseStep 413315 = 619973) B619973
theorem B183953 : Blo 119786 183953 := bstep (se 2 (by rfl) ⟨68982, by rfl⟩ : syracuseStep 183953 = 137965) B137965
theorem B183971 : Blo 119786 183971 := bstep (se 1 (by rfl) ⟨137978, by rfl⟩ : syracuseStep 183971 = 275957) B275957
theorem B184001 : Blo 119786 184001 := bstep (se 2 (by rfl) ⟨69000, by rfl⟩ : syracuseStep 184001 = 138001) B138001
theorem B184019 : Blo 119786 184019 := bstep (se 1 (by rfl) ⟨138014, by rfl⟩ : syracuseStep 184019 = 276029) B276029
theorem B184049 : Blo 119786 184049 := bstep (se 2 (by rfl) ⟨69018, by rfl⟩ : syracuseStep 184049 = 138037) B138037
theorem B184067 : Blo 119786 184067 := bstep (se 1 (by rfl) ⟨138050, by rfl⟩ : syracuseStep 184067 = 276101) B276101
theorem B184097 : Blo 119786 184097 := bstep (se 2 (by rfl) ⟨69036, by rfl⟩ : syracuseStep 184097 = 138073) B138073
theorem B347939 : Blo 119786 347939 := bstep (se 1 (by rfl) ⟨260954, by rfl⟩ : syracuseStep 347939 = 521909) B521909
theorem B184115 : Blo 119786 184115 := bstep (se 1 (by rfl) ⟨138086, by rfl⟩ : syracuseStep 184115 = 276173) B276173
theorem B184145 : Blo 119786 184145 := bstep (se 2 (by rfl) ⟨69054, by rfl⟩ : syracuseStep 184145 = 138109) B138109
theorem B184163 : Blo 119786 184163 := bstep (se 1 (by rfl) ⟨138122, by rfl⟩ : syracuseStep 184163 = 276245) B276245
theorem B184193 : Blo 119786 184193 := bstep (se 2 (by rfl) ⟨69072, by rfl⟩ : syracuseStep 184193 = 138145) B138145
theorem B2346893 : Blo 119786 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B413585 : Blo 119786 413585 := bstep (se 2 (by rfl) ⟨155094, by rfl⟩ : syracuseStep 413585 = 310189) B310189
theorem B184211 : Blo 119786 184211 := bstep (se 1 (by rfl) ⟨138158, by rfl⟩ : syracuseStep 184211 = 276317) B276317
theorem B217009 : Blo 119786 217009 := bstep (se 2 (by rfl) ⟨81378, by rfl⟩ : syracuseStep 217009 = 162757) B162757
theorem B184241 : Blo 119786 184241 := bstep (se 2 (by rfl) ⟨69090, by rfl⟩ : syracuseStep 184241 = 138181) B138181
theorem B184259 : Blo 119786 184259 := bstep (se 1 (by rfl) ⟨138194, by rfl⟩ : syracuseStep 184259 = 276389) B276389
theorem B610253 : Blo 119786 610253 := bstep (se 3 (by rfl) ⟨114422, by rfl⟩ : syracuseStep 610253 = 228845) B228845
theorem B184289 : Blo 119786 184289 := bstep (se 2 (by rfl) ⟨69108, by rfl⟩ : syracuseStep 184289 = 138217) B138217
theorem B937969 : Blo 119786 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B184307 : Blo 119786 184307 := bstep (se 1 (by rfl) ⟨138230, by rfl⟩ : syracuseStep 184307 = 276461) B276461
theorem B184337 : Blo 119786 184337 := bstep (se 2 (by rfl) ⟨69126, by rfl⟩ : syracuseStep 184337 = 138253) B138253
theorem B184355 : Blo 119786 184355 := bstep (se 1 (by rfl) ⟨138266, by rfl⟩ : syracuseStep 184355 = 276533) B276533
theorem B184385 : Blo 119786 184385 := bstep (se 2 (by rfl) ⟨69144, by rfl⟩ : syracuseStep 184385 = 138289) B138289
theorem B184403 : Blo 119786 184403 := bstep (se 1 (by rfl) ⟨138302, by rfl⟩ : syracuseStep 184403 = 276605) B276605
theorem B184433 : Blo 119786 184433 := bstep (se 2 (by rfl) ⟨69162, by rfl⟩ : syracuseStep 184433 = 138325) B138325
theorem B184451 : Blo 119786 184451 := bstep (se 1 (by rfl) ⟨138338, by rfl⟩ : syracuseStep 184451 = 276677) B276677
theorem B184481 : Blo 119786 184481 := bstep (se 2 (by rfl) ⟨69180, by rfl⟩ : syracuseStep 184481 = 138361) B138361
theorem B184499 : Blo 119786 184499 := bstep (se 1 (by rfl) ⟨138374, by rfl⟩ : syracuseStep 184499 = 276749) B276749
theorem B184529 : Blo 119786 184529 := bstep (se 2 (by rfl) ⟨69198, by rfl⟩ : syracuseStep 184529 = 138397) B138397
theorem B184547 : Blo 119786 184547 := bstep (se 1 (by rfl) ⟨138410, by rfl⟩ : syracuseStep 184547 = 276821) B276821
theorem B184577 : Blo 119786 184577 := bstep (se 2 (by rfl) ⟨69216, by rfl⟩ : syracuseStep 184577 = 138433) B138433
theorem B184595 : Blo 119786 184595 := bstep (se 1 (by rfl) ⟨138446, by rfl⟩ : syracuseStep 184595 = 276893) B276893
theorem B184625 : Blo 119786 184625 := bstep (se 2 (by rfl) ⟨69234, by rfl⟩ : syracuseStep 184625 = 138469) B138469
theorem B184643 : Blo 119786 184643 := bstep (se 1 (by rfl) ⟨138482, by rfl⟩ : syracuseStep 184643 = 276965) B276965
theorem B184673 : Blo 119786 184673 := bstep (se 2 (by rfl) ⟨69252, by rfl⟩ : syracuseStep 184673 = 138505) B138505
theorem B184691 : Blo 119786 184691 := bstep (se 1 (by rfl) ⟨138518, by rfl⟩ : syracuseStep 184691 = 277037) B277037
theorem B184721 : Blo 119786 184721 := bstep (se 2 (by rfl) ⟨69270, by rfl⟩ : syracuseStep 184721 = 138541) B138541
theorem B184739 : Blo 119786 184739 := bstep (se 1 (by rfl) ⟨138554, by rfl⟩ : syracuseStep 184739 = 277109) B277109
theorem B414125 : Blo 119786 414125 := bstep (se 3 (by rfl) ⟨77648, by rfl⟩ : syracuseStep 414125 = 155297) B155297
theorem B184769 : Blo 119786 184769 := bstep (se 2 (by rfl) ⟨69288, by rfl⟩ : syracuseStep 184769 = 138577) B138577
theorem B184787 : Blo 119786 184787 := bstep (se 1 (by rfl) ⟨138590, by rfl⟩ : syracuseStep 184787 = 277181) B277181
theorem B414179 : Blo 119786 414179 := bstep (se 1 (by rfl) ⟨310634, by rfl⟩ : syracuseStep 414179 = 621269) B621269
theorem B184817 : Blo 119786 184817 := bstep (se 2 (by rfl) ⟨69306, by rfl⟩ : syracuseStep 184817 = 138613) B138613
theorem B184835 : Blo 119786 184835 := bstep (se 1 (by rfl) ⟨138626, by rfl⟩ : syracuseStep 184835 = 277253) B277253
theorem B184865 : Blo 119786 184865 := bstep (se 2 (by rfl) ⟨69324, by rfl⟩ : syracuseStep 184865 = 138649) B138649
theorem B184883 : Blo 119786 184883 := bstep (se 1 (by rfl) ⟨138662, by rfl⟩ : syracuseStep 184883 = 277325) B277325
theorem B184913 : Blo 119786 184913 := bstep (se 2 (by rfl) ⟨69342, by rfl⟩ : syracuseStep 184913 = 138685) B138685
theorem B184931 : Blo 119786 184931 := bstep (se 1 (by rfl) ⟨138698, by rfl⟩ : syracuseStep 184931 = 277397) B277397
theorem B348781 : Blo 119786 348781 := bstep (se 3 (by rfl) ⟨65396, by rfl⟩ : syracuseStep 348781 = 130793) B130793
theorem B3002993 : Blo 119786 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B184961 : Blo 119786 184961 := bstep (se 2 (by rfl) ⟨69360, by rfl⟩ : syracuseStep 184961 = 138721) B138721
theorem B184979 : Blo 119786 184979 := bstep (se 1 (by rfl) ⟨138734, by rfl⟩ : syracuseStep 184979 = 277469) B277469
theorem B185009 : Blo 119786 185009 := bstep (se 2 (by rfl) ⟨69378, by rfl⟩ : syracuseStep 185009 = 138757) B138757
theorem B217795 : Blo 119786 217795 := bstep (se 1 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 217795 = 326693) B326693
theorem B185027 : Blo 119786 185027 := bstep (se 1 (by rfl) ⟨138770, by rfl⟩ : syracuseStep 185027 = 277541) B277541
theorem B152275 : Blo 119786 152275 := bstep (se 1 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 152275 = 228413) B228413
theorem B185057 : Blo 119786 185057 := bstep (se 2 (by rfl) ⟨69396, by rfl⟩ : syracuseStep 185057 = 138793) B138793
theorem B414449 : Blo 119786 414449 := bstep (se 2 (by rfl) ⟨155418, by rfl⟩ : syracuseStep 414449 = 310837) B310837
theorem B185075 : Blo 119786 185075 := bstep (se 1 (by rfl) ⟨138806, by rfl⟩ : syracuseStep 185075 = 277613) B277613
theorem B774917 : Blo 119786 774917 := bstep (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) B145297
theorem B348941 : Blo 119786 348941 := bstep (se 3 (by rfl) ⟨65426, by rfl⟩ : syracuseStep 348941 = 130853) B130853
theorem B185105 : Blo 119786 185105 := bstep (se 2 (by rfl) ⟨69414, by rfl⟩ : syracuseStep 185105 = 138829) B138829
theorem B185123 : Blo 119786 185123 := bstep (se 1 (by rfl) ⟨138842, by rfl⟩ : syracuseStep 185123 = 277685) B277685
theorem B152371 : Blo 119786 152371 := bstep (se 1 (by rfl) ⟨114278, by rfl⟩ : syracuseStep 152371 = 228557) B228557
theorem B185153 : Blo 119786 185153 := bstep (se 2 (by rfl) ⟨69432, by rfl⟩ : syracuseStep 185153 = 138865) B138865
theorem B185171 : Blo 119786 185171 := bstep (se 1 (by rfl) ⟨138878, by rfl⟩ : syracuseStep 185171 = 277757) B277757
theorem B185201 : Blo 119786 185201 := bstep (se 2 (by rfl) ⟨69450, by rfl⟩ : syracuseStep 185201 = 138901) B138901
theorem B185219 : Blo 119786 185219 := bstep (se 1 (by rfl) ⟨138914, by rfl⟩ : syracuseStep 185219 = 277829) B277829
theorem B185249 : Blo 119786 185249 := bstep (se 2 (by rfl) ⟨69468, by rfl⟩ : syracuseStep 185249 = 138937) B138937
theorem B185267 : Blo 119786 185267 := bstep (se 1 (by rfl) ⟨138950, by rfl⟩ : syracuseStep 185267 = 277901) B277901
theorem B349123 : Blo 119786 349123 := bstep (se 1 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 349123 = 523685) B523685
theorem B185297 : Blo 119786 185297 := bstep (se 2 (by rfl) ⟨69486, by rfl⟩ : syracuseStep 185297 = 138973) B138973
theorem B185315 : Blo 119786 185315 := bstep (se 1 (by rfl) ⟨138986, by rfl⟩ : syracuseStep 185315 = 277973) B277973
theorem B119795 : Blo 119786 119795 := bstep (se 1 (by rfl) ⟨89846, by rfl⟩ : syracuseStep 119795 = 179693) B179693
theorem B185345 : Blo 119786 185345 := bstep (se 2 (by rfl) ⟨69504, by rfl⟩ : syracuseStep 185345 = 139009) B139009
theorem B119811 : Blo 119786 119811 := bstep (se 1 (by rfl) ⟨89858, by rfl⟩ : syracuseStep 119811 = 179717) B179717
theorem B119827 : Blo 119786 119827 := bstep (se 1 (by rfl) ⟨89870, by rfl⟩ : syracuseStep 119827 = 179741) B179741
theorem B185363 : Blo 119786 185363 := bstep (se 1 (by rfl) ⟨139022, by rfl⟩ : syracuseStep 185363 = 278045) B278045
theorem B119843 : Blo 119786 119843 := bstep (se 1 (by rfl) ⟨89882, by rfl⟩ : syracuseStep 119843 = 179765) B179765
theorem B185393 : Blo 119786 185393 := bstep (se 2 (by rfl) ⟨69522, by rfl⟩ : syracuseStep 185393 = 139045) B139045
theorem B119859 : Blo 119786 119859 := bstep (se 1 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 119859 = 179789) B179789
theorem B119875 : Blo 119786 119875 := bstep (se 1 (by rfl) ⟨89906, by rfl⟩ : syracuseStep 119875 = 179813) B179813
theorem B185411 : Blo 119786 185411 := bstep (se 1 (by rfl) ⟨139058, by rfl⟩ : syracuseStep 185411 = 278117) B278117
theorem B119891 : Blo 119786 119891 := bstep (se 1 (by rfl) ⟨89918, by rfl⟩ : syracuseStep 119891 = 179837) B179837
theorem B185441 : Blo 119786 185441 := bstep (se 2 (by rfl) ⟨69540, by rfl⟩ : syracuseStep 185441 = 139081) B139081
theorem B119907 : Blo 119786 119907 := bstep (se 1 (by rfl) ⟨89930, by rfl⟩ : syracuseStep 119907 = 179861) B179861
theorem B119923 : Blo 119786 119923 := bstep (se 1 (by rfl) ⟨89942, by rfl⟩ : syracuseStep 119923 = 179885) B179885
theorem B185459 : Blo 119786 185459 := bstep (se 1 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 185459 = 278189) B278189
theorem B185473 : Blo 119786 185473 := bstep (se 2 (by rfl) ⟨69552, by rfl⟩ : syracuseStep 185473 = 139105) B139105
theorem B119939 : Blo 119786 119939 := bstep (se 1 (by rfl) ⟨89954, by rfl⟩ : syracuseStep 119939 = 179909) B179909
theorem B185489 : Blo 119786 185489 := bstep (se 2 (by rfl) ⟨69558, by rfl⟩ : syracuseStep 185489 = 139117) B139117
theorem B119955 : Blo 119786 119955 := bstep (se 1 (by rfl) ⟨89966, by rfl⟩ : syracuseStep 119955 = 179933) B179933
theorem B119971 : Blo 119786 119971 := bstep (se 1 (by rfl) ⟨89978, by rfl⟩ : syracuseStep 119971 = 179957) B179957
theorem B185507 : Blo 119786 185507 := bstep (se 1 (by rfl) ⟨139130, by rfl⟩ : syracuseStep 185507 = 278261) B278261
theorem B119987 : Blo 119786 119987 := bstep (se 1 (by rfl) ⟨89990, by rfl⟩ : syracuseStep 119987 = 179981) B179981
theorem B185537 : Blo 119786 185537 := bstep (se 2 (by rfl) ⟨69576, by rfl⟩ : syracuseStep 185537 = 139153) B139153
theorem B120003 : Blo 119786 120003 := bstep (se 1 (by rfl) ⟨90002, by rfl⟩ : syracuseStep 120003 = 180005) B180005
theorem B120019 : Blo 119786 120019 := bstep (se 1 (by rfl) ⟨90014, by rfl⟩ : syracuseStep 120019 = 180029) B180029
theorem B185555 : Blo 119786 185555 := bstep (se 1 (by rfl) ⟨139166, by rfl⟩ : syracuseStep 185555 = 278333) B278333
theorem B120035 : Blo 119786 120035 := bstep (se 1 (by rfl) ⟨90026, by rfl⟩ : syracuseStep 120035 = 180053) B180053
theorem B185585 : Blo 119786 185585 := bstep (se 2 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 185585 = 139189) B139189
theorem B120051 : Blo 119786 120051 := bstep (se 1 (by rfl) ⟨90038, by rfl⟩ : syracuseStep 120051 = 180077) B180077
theorem B120067 : Blo 119786 120067 := bstep (se 1 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 120067 = 180101) B180101
theorem B185603 : Blo 119786 185603 := bstep (se 1 (by rfl) ⟨139202, by rfl⟩ : syracuseStep 185603 = 278405) B278405
theorem B414989 : Blo 119786 414989 := bstep (se 3 (by rfl) ⟨77810, by rfl⟩ : syracuseStep 414989 = 155621) B155621
theorem B120083 : Blo 119786 120083 := bstep (se 1 (by rfl) ⟨90062, by rfl⟩ : syracuseStep 120083 = 180125) B180125
theorem B185633 : Blo 119786 185633 := bstep (se 2 (by rfl) ⟨69612, by rfl⟩ : syracuseStep 185633 = 139225) B139225
theorem B120099 : Blo 119786 120099 := bstep (se 1 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 120099 = 180149) B180149
theorem B152867 : Blo 119786 152867 := bstep (se 1 (by rfl) ⟨114650, by rfl⟩ : syracuseStep 152867 = 229301) B229301
theorem B120115 : Blo 119786 120115 := bstep (se 1 (by rfl) ⟨90086, by rfl⟩ : syracuseStep 120115 = 180173) B180173
theorem B185651 : Blo 119786 185651 := bstep (se 1 (by rfl) ⟨139238, by rfl⟩ : syracuseStep 185651 = 278477) B278477
theorem B120131 : Blo 119786 120131 := bstep (se 1 (by rfl) ⟨90098, by rfl⟩ : syracuseStep 120131 = 180197) B180197
theorem B415043 : Blo 119786 415043 := bstep (se 1 (by rfl) ⟨311282, by rfl⟩ : syracuseStep 415043 = 622565) B622565
theorem B120147 : Blo 119786 120147 := bstep (se 1 (by rfl) ⟨90110, by rfl⟩ : syracuseStep 120147 = 180221) B180221
theorem B120163 : Blo 119786 120163 := bstep (se 1 (by rfl) ⟨90122, by rfl⟩ : syracuseStep 120163 = 180245) B180245
theorem B120179 : Blo 119786 120179 := bstep (se 1 (by rfl) ⟨90134, by rfl⟩ : syracuseStep 120179 = 180269) B180269
theorem B120195 : Blo 119786 120195 := bstep (se 1 (by rfl) ⟨90146, by rfl⟩ : syracuseStep 120195 = 180293) B180293
theorem B120211 : Blo 119786 120211 := bstep (se 1 (by rfl) ⟨90158, by rfl⟩ : syracuseStep 120211 = 180317) B180317
theorem B120227 : Blo 119786 120227 := bstep (se 1 (by rfl) ⟨90170, by rfl⟩ : syracuseStep 120227 = 180341) B180341
theorem B120243 : Blo 119786 120243 := bstep (se 1 (by rfl) ⟨90182, by rfl⟩ : syracuseStep 120243 = 180365) B180365
theorem B120259 : Blo 119786 120259 := bstep (se 1 (by rfl) ⟨90194, by rfl⟩ : syracuseStep 120259 = 180389) B180389
theorem B120275 : Blo 119786 120275 := bstep (se 1 (by rfl) ⟨90206, by rfl⟩ : syracuseStep 120275 = 180413) B180413
theorem B120291 : Blo 119786 120291 := bstep (se 1 (by rfl) ⟨90218, by rfl⟩ : syracuseStep 120291 = 180437) B180437
theorem B120307 : Blo 119786 120307 := bstep (se 1 (by rfl) ⟨90230, by rfl⟩ : syracuseStep 120307 = 180461) B180461
theorem B120323 : Blo 119786 120323 := bstep (se 1 (by rfl) ⟨90242, by rfl⟩ : syracuseStep 120323 = 180485) B180485
theorem B120339 : Blo 119786 120339 := bstep (se 1 (by rfl) ⟨90254, by rfl⟩ : syracuseStep 120339 = 180509) B180509
theorem B120355 : Blo 119786 120355 := bstep (se 1 (by rfl) ⟨90266, by rfl⟩ : syracuseStep 120355 = 180533) B180533
theorem B120371 : Blo 119786 120371 := bstep (se 1 (by rfl) ⟨90278, by rfl⟩ : syracuseStep 120371 = 180557) B180557
theorem B120387 : Blo 119786 120387 := bstep (se 1 (by rfl) ⟨90290, by rfl⟩ : syracuseStep 120387 = 180581) B180581
theorem B317009 : Blo 119786 317009 := bstep (se 2 (by rfl) ⟨118878, by rfl⟩ : syracuseStep 317009 = 237757) B237757
theorem B120403 : Blo 119786 120403 := bstep (se 1 (by rfl) ⟨90302, by rfl⟩ : syracuseStep 120403 = 180605) B180605
theorem B415313 : Blo 119786 415313 := bstep (se 2 (by rfl) ⟨155742, by rfl⟩ : syracuseStep 415313 = 311485) B311485
theorem B120419 : Blo 119786 120419 := bstep (se 1 (by rfl) ⟨90314, by rfl⟩ : syracuseStep 120419 = 180629) B180629
theorem B120435 : Blo 119786 120435 := bstep (se 1 (by rfl) ⟨90326, by rfl⟩ : syracuseStep 120435 = 180653) B180653
theorem B120451 : Blo 119786 120451 := bstep (se 1 (by rfl) ⟨90338, by rfl⟩ : syracuseStep 120451 = 180677) B180677
theorem B120467 : Blo 119786 120467 := bstep (se 1 (by rfl) ⟨90350, by rfl⟩ : syracuseStep 120467 = 180701) B180701
theorem B120483 : Blo 119786 120483 := bstep (se 1 (by rfl) ⟨90362, by rfl⟩ : syracuseStep 120483 = 180725) B180725
theorem B120499 : Blo 119786 120499 := bstep (se 1 (by rfl) ⟨90374, by rfl⟩ : syracuseStep 120499 = 180749) B180749
theorem B120515 : Blo 119786 120515 := bstep (se 1 (by rfl) ⟨90386, by rfl⟩ : syracuseStep 120515 = 180773) B180773
theorem B120531 : Blo 119786 120531 := bstep (se 1 (by rfl) ⟨90398, by rfl⟩ : syracuseStep 120531 = 180797) B180797
theorem B120547 : Blo 119786 120547 := bstep (se 1 (by rfl) ⟨90410, by rfl⟩ : syracuseStep 120547 = 180821) B180821
theorem B120563 : Blo 119786 120563 := bstep (se 1 (by rfl) ⟨90422, by rfl⟩ : syracuseStep 120563 = 180845) B180845
theorem B120579 : Blo 119786 120579 := bstep (se 1 (by rfl) ⟨90434, by rfl⟩ : syracuseStep 120579 = 180869) B180869
theorem B218897 : Blo 119786 218897 := bstep (se 2 (by rfl) ⟨82086, by rfl⟩ : syracuseStep 218897 = 164173) B164173
theorem B186131 : Blo 119786 186131 := bstep (se 1 (by rfl) ⟨139598, by rfl⟩ : syracuseStep 186131 = 279197) B279197
theorem B120595 : Blo 119786 120595 := bstep (se 1 (by rfl) ⟨90446, by rfl⟩ : syracuseStep 120595 = 180893) B180893
theorem B120611 : Blo 119786 120611 := bstep (se 1 (by rfl) ⟨90458, by rfl⟩ : syracuseStep 120611 = 180917) B180917
theorem B120627 : Blo 119786 120627 := bstep (se 1 (by rfl) ⟨90470, by rfl⟩ : syracuseStep 120627 = 180941) B180941
theorem B120643 : Blo 119786 120643 := bstep (se 1 (by rfl) ⟨90482, by rfl⟩ : syracuseStep 120643 = 180965) B180965
theorem B120659 : Blo 119786 120659 := bstep (se 1 (by rfl) ⟨90494, by rfl⟩ : syracuseStep 120659 = 180989) B180989
theorem B120675 : Blo 119786 120675 := bstep (se 1 (by rfl) ⟨90506, by rfl⟩ : syracuseStep 120675 = 181013) B181013
theorem B120691 : Blo 119786 120691 := bstep (se 1 (by rfl) ⟨90518, by rfl⟩ : syracuseStep 120691 = 181037) B181037
theorem B120707 : Blo 119786 120707 := bstep (se 1 (by rfl) ⟨90530, by rfl⟩ : syracuseStep 120707 = 181061) B181061
theorem B120723 : Blo 119786 120723 := bstep (se 1 (by rfl) ⟨90542, by rfl⟩ : syracuseStep 120723 = 181085) B181085
theorem B120739 : Blo 119786 120739 := bstep (se 1 (by rfl) ⟨90554, by rfl⟩ : syracuseStep 120739 = 181109) B181109
theorem B120755 : Blo 119786 120755 := bstep (se 1 (by rfl) ⟨90566, by rfl⟩ : syracuseStep 120755 = 181133) B181133
theorem B186305 : Blo 119786 186305 := bstep (se 2 (by rfl) ⟨69864, by rfl⟩ : syracuseStep 186305 = 139729) B139729
theorem B120771 : Blo 119786 120771 := bstep (se 1 (by rfl) ⟨90578, by rfl⟩ : syracuseStep 120771 = 181157) B181157
theorem B120787 : Blo 119786 120787 := bstep (se 1 (by rfl) ⟨90590, by rfl⟩ : syracuseStep 120787 = 181181) B181181
theorem B120803 : Blo 119786 120803 := bstep (se 1 (by rfl) ⟨90602, by rfl⟩ : syracuseStep 120803 = 181205) B181205
theorem B153571 : Blo 119786 153571 := bstep (se 1 (by rfl) ⟨115178, by rfl⟩ : syracuseStep 153571 = 230357) B230357
theorem B120819 : Blo 119786 120819 := bstep (se 1 (by rfl) ⟨90614, by rfl⟩ : syracuseStep 120819 = 181229) B181229
theorem B120835 : Blo 119786 120835 := bstep (se 1 (by rfl) ⟨90626, by rfl⟩ : syracuseStep 120835 = 181253) B181253
theorem B120851 : Blo 119786 120851 := bstep (se 1 (by rfl) ⟨90638, by rfl⟩ : syracuseStep 120851 = 181277) B181277
theorem B120867 : Blo 119786 120867 := bstep (se 1 (by rfl) ⟨90650, by rfl⟩ : syracuseStep 120867 = 181301) B181301
theorem B120883 : Blo 119786 120883 := bstep (se 1 (by rfl) ⟨90662, by rfl⟩ : syracuseStep 120883 = 181325) B181325
theorem B120899 : Blo 119786 120899 := bstep (se 1 (by rfl) ⟨90674, by rfl⟩ : syracuseStep 120899 = 181349) B181349
theorem B153667 : Blo 119786 153667 := bstep (se 1 (by rfl) ⟨115250, by rfl⟩ : syracuseStep 153667 = 230501) B230501
theorem B120915 : Blo 119786 120915 := bstep (se 1 (by rfl) ⟨90686, by rfl⟩ : syracuseStep 120915 = 181373) B181373
theorem B120931 : Blo 119786 120931 := bstep (se 1 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 120931 = 181397) B181397
theorem B415853 : Blo 119786 415853 := bstep (se 3 (by rfl) ⟨77972, by rfl⟩ : syracuseStep 415853 = 155945) B155945
theorem B120947 : Blo 119786 120947 := bstep (se 1 (by rfl) ⟨90710, by rfl⟩ : syracuseStep 120947 = 181421) B181421
theorem B120963 : Blo 119786 120963 := bstep (se 1 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 120963 = 181445) B181445
theorem B120979 : Blo 119786 120979 := bstep (se 1 (by rfl) ⟨90734, by rfl⟩ : syracuseStep 120979 = 181469) B181469
theorem B120995 : Blo 119786 120995 := bstep (se 1 (by rfl) ⟨90746, by rfl⟩ : syracuseStep 120995 = 181493) B181493
theorem B415907 : Blo 119786 415907 := bstep (se 1 (by rfl) ⟨311930, by rfl⟩ : syracuseStep 415907 = 623861) B623861
theorem B186545 : Blo 119786 186545 := bstep (se 2 (by rfl) ⟨69954, by rfl⟩ : syracuseStep 186545 = 139909) B139909
theorem B121011 : Blo 119786 121011 := bstep (se 1 (by rfl) ⟨90758, by rfl⟩ : syracuseStep 121011 = 181517) B181517
theorem B121027 : Blo 119786 121027 := bstep (se 1 (by rfl) ⟨90770, by rfl⟩ : syracuseStep 121027 = 181541) B181541
theorem B121043 : Blo 119786 121043 := bstep (se 1 (by rfl) ⟨90782, by rfl⟩ : syracuseStep 121043 = 181565) B181565
theorem B121059 : Blo 119786 121059 := bstep (se 1 (by rfl) ⟨90794, by rfl⟩ : syracuseStep 121059 = 181589) B181589
theorem B121075 : Blo 119786 121075 := bstep (se 1 (by rfl) ⟨90806, by rfl⟩ : syracuseStep 121075 = 181613) B181613
theorem B121091 : Blo 119786 121091 := bstep (se 1 (by rfl) ⟨90818, by rfl⟩ : syracuseStep 121091 = 181637) B181637
theorem B121107 : Blo 119786 121107 := bstep (se 1 (by rfl) ⟨90830, by rfl⟩ : syracuseStep 121107 = 181661) B181661
theorem B121123 : Blo 119786 121123 := bstep (se 1 (by rfl) ⟨90842, by rfl⟩ : syracuseStep 121123 = 181685) B181685
theorem B350513 : Blo 119786 350513 := bstep (se 2 (by rfl) ⟨131442, by rfl⟩ : syracuseStep 350513 = 262885) B262885
theorem B121139 : Blo 119786 121139 := bstep (se 1 (by rfl) ⟨90854, by rfl⟩ : syracuseStep 121139 = 181709) B181709
theorem B121155 : Blo 119786 121155 := bstep (se 1 (by rfl) ⟨90866, by rfl⟩ : syracuseStep 121155 = 181733) B181733
theorem B121171 : Blo 119786 121171 := bstep (se 1 (by rfl) ⟨90878, by rfl⟩ : syracuseStep 121171 = 181757) B181757
theorem B121187 : Blo 119786 121187 := bstep (se 1 (by rfl) ⟨90890, by rfl⟩ : syracuseStep 121187 = 181781) B181781
theorem B121203 : Blo 119786 121203 := bstep (se 1 (by rfl) ⟨90902, by rfl⟩ : syracuseStep 121203 = 181805) B181805
theorem B121219 : Blo 119786 121219 := bstep (se 1 (by rfl) ⟨90914, by rfl⟩ : syracuseStep 121219 = 181829) B181829
theorem B121235 : Blo 119786 121235 := bstep (se 1 (by rfl) ⟨90926, by rfl⟩ : syracuseStep 121235 = 181853) B181853
theorem B121251 : Blo 119786 121251 := bstep (se 1 (by rfl) ⟨90938, by rfl⟩ : syracuseStep 121251 = 181877) B181877
theorem B416177 : Blo 119786 416177 := bstep (se 2 (by rfl) ⟨156066, by rfl⟩ : syracuseStep 416177 = 312133) B312133
theorem B121267 : Blo 119786 121267 := bstep (se 1 (by rfl) ⟨90950, by rfl⟩ : syracuseStep 121267 = 181901) B181901
theorem B121283 : Blo 119786 121283 := bstep (se 1 (by rfl) ⟨90962, by rfl⟩ : syracuseStep 121283 = 181925) B181925
theorem B121299 : Blo 119786 121299 := bstep (se 1 (by rfl) ⟨90974, by rfl⟩ : syracuseStep 121299 = 181949) B181949
theorem B121315 : Blo 119786 121315 := bstep (se 1 (by rfl) ⟨90986, by rfl⟩ : syracuseStep 121315 = 181973) B181973
theorem B121331 : Blo 119786 121331 := bstep (se 1 (by rfl) ⟨90998, by rfl⟩ : syracuseStep 121331 = 181997) B181997
theorem B121347 : Blo 119786 121347 := bstep (se 1 (by rfl) ⟨91010, by rfl⟩ : syracuseStep 121347 = 182021) B182021
theorem B121363 : Blo 119786 121363 := bstep (se 1 (by rfl) ⟨91022, by rfl⟩ : syracuseStep 121363 = 182045) B182045
theorem B121379 : Blo 119786 121379 := bstep (se 1 (by rfl) ⟨91034, by rfl⟩ : syracuseStep 121379 = 182069) B182069
theorem B121395 : Blo 119786 121395 := bstep (se 1 (by rfl) ⟨91046, by rfl⟩ : syracuseStep 121395 = 182093) B182093
theorem B154163 : Blo 119786 154163 := bstep (se 1 (by rfl) ⟨115622, by rfl⟩ : syracuseStep 154163 = 231245) B231245
theorem B121411 : Blo 119786 121411 := bstep (se 1 (by rfl) ⟨91058, by rfl⟩ : syracuseStep 121411 = 182117) B182117
theorem B121427 : Blo 119786 121427 := bstep (se 1 (by rfl) ⟨91070, by rfl⟩ : syracuseStep 121427 = 182141) B182141
theorem B121443 : Blo 119786 121443 := bstep (se 1 (by rfl) ⟨91082, by rfl⟩ : syracuseStep 121443 = 182165) B182165
theorem B121459 : Blo 119786 121459 := bstep (se 1 (by rfl) ⟨91094, by rfl⟩ : syracuseStep 121459 = 182189) B182189
theorem B121475 : Blo 119786 121475 := bstep (se 1 (by rfl) ⟨91106, by rfl⟩ : syracuseStep 121475 = 182213) B182213
theorem B121491 : Blo 119786 121491 := bstep (se 1 (by rfl) ⟨91118, by rfl⟩ : syracuseStep 121491 = 182237) B182237
theorem B121507 : Blo 119786 121507 := bstep (se 1 (by rfl) ⟨91130, by rfl⟩ : syracuseStep 121507 = 182261) B182261
theorem B121523 : Blo 119786 121523 := bstep (se 1 (by rfl) ⟨91142, by rfl⟩ : syracuseStep 121523 = 182285) B182285
theorem B121539 : Blo 119786 121539 := bstep (se 1 (by rfl) ⟨91154, by rfl⟩ : syracuseStep 121539 = 182309) B182309
theorem B514765 : Blo 119786 514765 := bstep (se 3 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 514765 = 193037) B193037
theorem B121555 : Blo 119786 121555 := bstep (se 1 (by rfl) ⟨91166, by rfl⟩ : syracuseStep 121555 = 182333) B182333
theorem B187091 : Blo 119786 187091 := bstep (se 1 (by rfl) ⟨140318, by rfl⟩ : syracuseStep 187091 = 280637) B280637
theorem B121571 : Blo 119786 121571 := bstep (se 1 (by rfl) ⟨91178, by rfl⟩ : syracuseStep 121571 = 182357) B182357
theorem B121587 : Blo 119786 121587 := bstep (se 1 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 121587 = 182381) B182381
theorem B121603 : Blo 119786 121603 := bstep (se 1 (by rfl) ⟨91202, by rfl⟩ : syracuseStep 121603 = 182405) B182405
theorem B121619 : Blo 119786 121619 := bstep (se 1 (by rfl) ⟨91214, by rfl⟩ : syracuseStep 121619 = 182429) B182429
theorem B121635 : Blo 119786 121635 := bstep (se 1 (by rfl) ⟨91226, by rfl⟩ : syracuseStep 121635 = 182453) B182453
theorem B613169 : Blo 119786 613169 := bstep (se 2 (by rfl) ⟨229938, by rfl⟩ : syracuseStep 613169 = 459877) B459877
theorem B121651 : Blo 119786 121651 := bstep (se 1 (by rfl) ⟨91238, by rfl⟩ : syracuseStep 121651 = 182477) B182477
theorem B187201 : Blo 119786 187201 := bstep (se 2 (by rfl) ⟨70200, by rfl⟩ : syracuseStep 187201 = 140401) B140401
theorem B121667 : Blo 119786 121667 := bstep (se 1 (by rfl) ⟨91250, by rfl⟩ : syracuseStep 121667 = 182501) B182501
theorem B547661 : Blo 119786 547661 := bstep (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) B205373
theorem B121683 : Blo 119786 121683 := bstep (se 1 (by rfl) ⟨91262, by rfl⟩ : syracuseStep 121683 = 182525) B182525
theorem B121699 : Blo 119786 121699 := bstep (se 1 (by rfl) ⟨91274, by rfl⟩ : syracuseStep 121699 = 182549) B182549
theorem B121715 : Blo 119786 121715 := bstep (se 1 (by rfl) ⟨91286, by rfl⟩ : syracuseStep 121715 = 182573) B182573
theorem B121731 : Blo 119786 121731 := bstep (se 1 (by rfl) ⟨91298, by rfl⟩ : syracuseStep 121731 = 182597) B182597
theorem B121747 : Blo 119786 121747 := bstep (se 1 (by rfl) ⟨91310, by rfl⟩ : syracuseStep 121747 = 182621) B182621
theorem B121763 : Blo 119786 121763 := bstep (se 1 (by rfl) ⟨91322, by rfl⟩ : syracuseStep 121763 = 182645) B182645
theorem B121779 : Blo 119786 121779 := bstep (se 1 (by rfl) ⟨91334, by rfl⟩ : syracuseStep 121779 = 182669) B182669
theorem B121795 : Blo 119786 121795 := bstep (se 1 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 121795 = 182693) B182693
theorem B416717 : Blo 119786 416717 := bstep (se 3 (by rfl) ⟨78134, by rfl⟩ : syracuseStep 416717 = 156269) B156269
theorem B121811 : Blo 119786 121811 := bstep (se 1 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 121811 = 182717) B182717
theorem B121827 : Blo 119786 121827 := bstep (se 1 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 121827 = 182741) B182741
theorem B121843 : Blo 119786 121843 := bstep (se 1 (by rfl) ⟨91382, by rfl⟩ : syracuseStep 121843 = 182765) B182765
theorem B121859 : Blo 119786 121859 := bstep (se 1 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 121859 = 182789) B182789
theorem B416771 : Blo 119786 416771 := bstep (se 1 (by rfl) ⟨312578, by rfl⟩ : syracuseStep 416771 = 625157) B625157
theorem B121875 : Blo 119786 121875 := bstep (se 1 (by rfl) ⟨91406, by rfl⟩ : syracuseStep 121875 = 182813) B182813
theorem B121891 : Blo 119786 121891 := bstep (se 1 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 121891 = 182837) B182837
theorem B121907 : Blo 119786 121907 := bstep (se 1 (by rfl) ⟨91430, by rfl⟩ : syracuseStep 121907 = 182861) B182861
theorem B121923 : Blo 119786 121923 := bstep (se 1 (by rfl) ⟨91442, by rfl⟩ : syracuseStep 121923 = 182885) B182885
theorem B121939 : Blo 119786 121939 := bstep (se 1 (by rfl) ⟨91454, by rfl⟩ : syracuseStep 121939 = 182909) B182909
theorem B121955 : Blo 119786 121955 := bstep (se 1 (by rfl) ⟨91466, by rfl⟩ : syracuseStep 121955 = 182933) B182933
theorem B121971 : Blo 119786 121971 := bstep (se 1 (by rfl) ⟨91478, by rfl⟩ : syracuseStep 121971 = 182957) B182957
theorem B121987 : Blo 119786 121987 := bstep (se 1 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 121987 = 182981) B182981
theorem B122003 : Blo 119786 122003 := bstep (se 1 (by rfl) ⟨91502, by rfl⟩ : syracuseStep 122003 = 183005) B183005
theorem B122019 : Blo 119786 122019 := bstep (se 1 (by rfl) ⟨91514, by rfl⟩ : syracuseStep 122019 = 183029) B183029
theorem B122035 : Blo 119786 122035 := bstep (se 1 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 122035 = 183053) B183053
theorem B122051 : Blo 119786 122051 := bstep (se 1 (by rfl) ⟨91538, by rfl⟩ : syracuseStep 122051 = 183077) B183077
theorem B122067 : Blo 119786 122067 := bstep (se 1 (by rfl) ⟨91550, by rfl⟩ : syracuseStep 122067 = 183101) B183101
theorem B122083 : Blo 119786 122083 := bstep (se 1 (by rfl) ⟨91562, by rfl⟩ : syracuseStep 122083 = 183125) B183125
theorem B351469 : Blo 119786 351469 := bstep (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) B131801
theorem B122099 : Blo 119786 122099 := bstep (se 1 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 122099 = 183149) B183149
theorem B154867 : Blo 119786 154867 := bstep (se 1 (by rfl) ⟨116150, by rfl⟩ : syracuseStep 154867 = 232301) B232301
theorem B122115 : Blo 119786 122115 := bstep (se 1 (by rfl) ⟨91586, by rfl⟩ : syracuseStep 122115 = 183173) B183173
theorem B417041 : Blo 119786 417041 := bstep (se 2 (by rfl) ⟨156390, by rfl⟩ : syracuseStep 417041 = 312781) B312781
theorem B122131 : Blo 119786 122131 := bstep (se 1 (by rfl) ⟨91598, by rfl⟩ : syracuseStep 122131 = 183197) B183197
theorem B122147 : Blo 119786 122147 := bstep (se 1 (by rfl) ⟨91610, by rfl⟩ : syracuseStep 122147 = 183221) B183221
theorem B122163 : Blo 119786 122163 := bstep (se 1 (by rfl) ⟨91622, by rfl⟩ : syracuseStep 122163 = 183245) B183245
theorem B220483 : Blo 119786 220483 := bstep (se 1 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 220483 = 330725) B330725
theorem B122179 : Blo 119786 122179 := bstep (se 1 (by rfl) ⟨91634, by rfl⟩ : syracuseStep 122179 = 183269) B183269
theorem B122195 : Blo 119786 122195 := bstep (se 1 (by rfl) ⟨91646, by rfl⟩ : syracuseStep 122195 = 183293) B183293
theorem B154963 : Blo 119786 154963 := bstep (se 1 (by rfl) ⟨116222, by rfl⟩ : syracuseStep 154963 = 232445) B232445
theorem B1039715 : Blo 119786 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B122211 : Blo 119786 122211 := bstep (se 1 (by rfl) ⟨91658, by rfl⟩ : syracuseStep 122211 = 183317) B183317
theorem B122227 : Blo 119786 122227 := bstep (se 1 (by rfl) ⟨91670, by rfl⟩ : syracuseStep 122227 = 183341) B183341
theorem B122243 : Blo 119786 122243 := bstep (se 1 (by rfl) ⟨91682, by rfl⟩ : syracuseStep 122243 = 183365) B183365
theorem B3300749 : Blo 119786 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B122259 : Blo 119786 122259 := bstep (se 1 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 122259 = 183389) B183389
theorem B122275 : Blo 119786 122275 := bstep (se 1 (by rfl) ⟨91706, by rfl⟩ : syracuseStep 122275 = 183413) B183413
theorem B122291 : Blo 119786 122291 := bstep (se 1 (by rfl) ⟨91718, by rfl⟩ : syracuseStep 122291 = 183437) B183437
theorem B122307 : Blo 119786 122307 := bstep (se 1 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 122307 = 183461) B183461
theorem B351697 : Blo 119786 351697 := bstep (se 2 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 351697 = 263773) B263773
theorem B122323 : Blo 119786 122323 := bstep (se 1 (by rfl) ⟨91742, by rfl⟩ : syracuseStep 122323 = 183485) B183485
theorem B122339 : Blo 119786 122339 := bstep (se 1 (by rfl) ⟨91754, by rfl⟩ : syracuseStep 122339 = 183509) B183509
theorem B122355 : Blo 119786 122355 := bstep (se 1 (by rfl) ⟨91766, by rfl⟩ : syracuseStep 122355 = 183533) B183533
theorem B122371 : Blo 119786 122371 := bstep (se 1 (by rfl) ⟨91778, by rfl⟩ : syracuseStep 122371 = 183557) B183557
theorem B122387 : Blo 119786 122387 := bstep (se 1 (by rfl) ⟨91790, by rfl⟩ : syracuseStep 122387 = 183581) B183581
theorem B122403 : Blo 119786 122403 := bstep (se 1 (by rfl) ⟨91802, by rfl⟩ : syracuseStep 122403 = 183605) B183605
theorem B122419 : Blo 119786 122419 := bstep (se 1 (by rfl) ⟨91814, by rfl⟩ : syracuseStep 122419 = 183629) B183629
theorem B122435 : Blo 119786 122435 := bstep (se 1 (by rfl) ⟨91826, by rfl⟩ : syracuseStep 122435 = 183653) B183653
theorem B122451 : Blo 119786 122451 := bstep (se 1 (by rfl) ⟨91838, by rfl⟩ : syracuseStep 122451 = 183677) B183677
theorem B122467 : Blo 119786 122467 := bstep (se 1 (by rfl) ⟨91850, by rfl⟩ : syracuseStep 122467 = 183701) B183701
theorem B351857 : Blo 119786 351857 := bstep (se 2 (by rfl) ⟨131946, by rfl⟩ : syracuseStep 351857 = 263893) B263893
theorem B122483 : Blo 119786 122483 := bstep (se 1 (by rfl) ⟨91862, by rfl⟩ : syracuseStep 122483 = 183725) B183725
theorem B122499 : Blo 119786 122499 := bstep (se 1 (by rfl) ⟨91874, by rfl⟩ : syracuseStep 122499 = 183749) B183749
theorem B122515 : Blo 119786 122515 := bstep (se 1 (by rfl) ⟨91886, by rfl⟩ : syracuseStep 122515 = 183773) B183773
theorem B122531 : Blo 119786 122531 := bstep (se 1 (by rfl) ⟨91898, by rfl⟩ : syracuseStep 122531 = 183797) B183797
theorem B122547 : Blo 119786 122547 := bstep (se 1 (by rfl) ⟨91910, by rfl⟩ : syracuseStep 122547 = 183821) B183821
theorem B122563 : Blo 119786 122563 := bstep (se 1 (by rfl) ⟨91922, by rfl⟩ : syracuseStep 122563 = 183845) B183845
theorem B122579 : Blo 119786 122579 := bstep (se 1 (by rfl) ⟨91934, by rfl⟩ : syracuseStep 122579 = 183869) B183869
theorem B122595 : Blo 119786 122595 := bstep (se 1 (by rfl) ⟨91946, by rfl⟩ : syracuseStep 122595 = 183893) B183893
theorem B351971 : Blo 119786 351971 := bstep (se 1 (by rfl) ⟨263978, by rfl⟩ : syracuseStep 351971 = 527957) B527957
theorem B122611 : Blo 119786 122611 := bstep (se 1 (by rfl) ⟨91958, by rfl⟩ : syracuseStep 122611 = 183917) B183917
theorem B122627 : Blo 119786 122627 := bstep (se 1 (by rfl) ⟨91970, by rfl⟩ : syracuseStep 122627 = 183941) B183941
theorem B122643 : Blo 119786 122643 := bstep (se 1 (by rfl) ⟨91982, by rfl⟩ : syracuseStep 122643 = 183965) B183965
theorem B122659 : Blo 119786 122659 := bstep (se 1 (by rfl) ⟨91994, by rfl⟩ : syracuseStep 122659 = 183989) B183989
theorem B417581 : Blo 119786 417581 := bstep (se 3 (by rfl) ⟨78296, by rfl⟩ : syracuseStep 417581 = 156593) B156593
theorem B122675 : Blo 119786 122675 := bstep (se 1 (by rfl) ⟨92006, by rfl⟩ : syracuseStep 122675 = 184013) B184013
theorem B122691 : Blo 119786 122691 := bstep (se 1 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 122691 = 184037) B184037
theorem B155459 : Blo 119786 155459 := bstep (se 1 (by rfl) ⟨116594, by rfl⟩ : syracuseStep 155459 = 233189) B233189
theorem B122707 : Blo 119786 122707 := bstep (se 1 (by rfl) ⟨92030, by rfl⟩ : syracuseStep 122707 = 184061) B184061
theorem B122723 : Blo 119786 122723 := bstep (se 1 (by rfl) ⟨92042, by rfl⟩ : syracuseStep 122723 = 184085) B184085
theorem B417635 : Blo 119786 417635 := bstep (se 1 (by rfl) ⟨313226, by rfl⟩ : syracuseStep 417635 = 626453) B626453
theorem B122739 : Blo 119786 122739 := bstep (se 1 (by rfl) ⟨92054, by rfl⟩ : syracuseStep 122739 = 184109) B184109
theorem B122755 : Blo 119786 122755 := bstep (se 1 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 122755 = 184133) B184133
theorem B122771 : Blo 119786 122771 := bstep (se 1 (by rfl) ⟨92078, by rfl⟩ : syracuseStep 122771 = 184157) B184157
theorem B122787 : Blo 119786 122787 := bstep (se 1 (by rfl) ⟨92090, by rfl⟩ : syracuseStep 122787 = 184181) B184181
theorem B122803 : Blo 119786 122803 := bstep (se 1 (by rfl) ⟨92102, by rfl⟩ : syracuseStep 122803 = 184205) B184205
theorem B122819 : Blo 119786 122819 := bstep (se 1 (by rfl) ⟨92114, by rfl⟩ : syracuseStep 122819 = 184229) B184229
theorem B122835 : Blo 119786 122835 := bstep (se 1 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 122835 = 184253) B184253
theorem B122851 : Blo 119786 122851 := bstep (se 1 (by rfl) ⟨92138, by rfl⟩ : syracuseStep 122851 = 184277) B184277
theorem B122867 : Blo 119786 122867 := bstep (se 1 (by rfl) ⟨92150, by rfl⟩ : syracuseStep 122867 = 184301) B184301
theorem B122883 : Blo 119786 122883 := bstep (se 1 (by rfl) ⟨92162, by rfl⟩ : syracuseStep 122883 = 184325) B184325
theorem B122899 : Blo 119786 122899 := bstep (se 1 (by rfl) ⟨92174, by rfl⟩ : syracuseStep 122899 = 184349) B184349
theorem B122915 : Blo 119786 122915 := bstep (se 1 (by rfl) ⟨92186, by rfl⟩ : syracuseStep 122915 = 184373) B184373
theorem B122931 : Blo 119786 122931 := bstep (se 1 (by rfl) ⟨92198, by rfl⟩ : syracuseStep 122931 = 184397) B184397
theorem B122947 : Blo 119786 122947 := bstep (se 1 (by rfl) ⟨92210, by rfl⟩ : syracuseStep 122947 = 184421) B184421
theorem B122963 : Blo 119786 122963 := bstep (se 1 (by rfl) ⟨92222, by rfl⟩ : syracuseStep 122963 = 184445) B184445
theorem B122979 : Blo 119786 122979 := bstep (se 1 (by rfl) ⟨92234, by rfl⟩ : syracuseStep 122979 = 184469) B184469
theorem B122995 : Blo 119786 122995 := bstep (se 1 (by rfl) ⟨92246, by rfl⟩ : syracuseStep 122995 = 184493) B184493
theorem B123011 : Blo 119786 123011 := bstep (se 1 (by rfl) ⟨92258, by rfl⟩ : syracuseStep 123011 = 184517) B184517
theorem B123027 : Blo 119786 123027 := bstep (se 1 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 123027 = 184541) B184541
theorem B123043 : Blo 119786 123043 := bstep (se 1 (by rfl) ⟨92282, by rfl⟩ : syracuseStep 123043 = 184565) B184565
theorem B123059 : Blo 119786 123059 := bstep (se 1 (by rfl) ⟨92294, by rfl⟩ : syracuseStep 123059 = 184589) B184589
theorem B123075 : Blo 119786 123075 := bstep (se 1 (by rfl) ⟨92306, by rfl⟩ : syracuseStep 123075 = 184613) B184613
theorem B123091 : Blo 119786 123091 := bstep (se 1 (by rfl) ⟨92318, by rfl⟩ : syracuseStep 123091 = 184637) B184637
theorem B614627 : Blo 119786 614627 := bstep (se 1 (by rfl) ⟨460970, by rfl⟩ : syracuseStep 614627 = 921941) B921941
theorem B123107 : Blo 119786 123107 := bstep (se 1 (by rfl) ⟨92330, by rfl⟩ : syracuseStep 123107 = 184661) B184661
theorem B1335523 : Blo 119786 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B778481 : Blo 119786 778481 := bstep (se 2 (by rfl) ⟨291930, by rfl⟩ : syracuseStep 778481 = 583861) B583861
theorem B123123 : Blo 119786 123123 := bstep (se 1 (by rfl) ⟨92342, by rfl⟩ : syracuseStep 123123 = 184685) B184685
theorem B123139 : Blo 119786 123139 := bstep (se 1 (by rfl) ⟨92354, by rfl⟩ : syracuseStep 123139 = 184709) B184709
theorem B123155 : Blo 119786 123155 := bstep (se 1 (by rfl) ⟨92366, by rfl⟩ : syracuseStep 123155 = 184733) B184733
theorem B123171 : Blo 119786 123171 := bstep (se 1 (by rfl) ⟨92378, by rfl⟩ : syracuseStep 123171 = 184757) B184757
theorem B123187 : Blo 119786 123187 := bstep (se 1 (by rfl) ⟨92390, by rfl⟩ : syracuseStep 123187 = 184781) B184781
theorem B123203 : Blo 119786 123203 := bstep (se 1 (by rfl) ⟨92402, by rfl⟩ : syracuseStep 123203 = 184805) B184805
theorem B385357 : Blo 119786 385357 := bstep (se 3 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 385357 = 144509) B144509
theorem B123219 : Blo 119786 123219 := bstep (se 1 (by rfl) ⟨92414, by rfl⟩ : syracuseStep 123219 = 184829) B184829
theorem B123235 : Blo 119786 123235 := bstep (se 1 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 123235 = 184853) B184853
theorem B123251 : Blo 119786 123251 := bstep (se 1 (by rfl) ⟨92438, by rfl⟩ : syracuseStep 123251 = 184877) B184877
theorem B123267 : Blo 119786 123267 := bstep (se 1 (by rfl) ⟨92450, by rfl⟩ : syracuseStep 123267 = 184901) B184901
theorem B123283 : Blo 119786 123283 := bstep (se 1 (by rfl) ⟨92462, by rfl⟩ : syracuseStep 123283 = 184925) B184925
theorem B123299 : Blo 119786 123299 := bstep (se 1 (by rfl) ⟨92474, by rfl⟩ : syracuseStep 123299 = 184949) B184949
theorem B123315 : Blo 119786 123315 := bstep (se 1 (by rfl) ⟨92486, by rfl⟩ : syracuseStep 123315 = 184973) B184973
theorem B123331 : Blo 119786 123331 := bstep (se 1 (by rfl) ⟨92498, by rfl⟩ : syracuseStep 123331 = 184997) B184997
theorem B123347 : Blo 119786 123347 := bstep (se 1 (by rfl) ⟨92510, by rfl⟩ : syracuseStep 123347 = 185021) B185021
theorem B123363 : Blo 119786 123363 := bstep (se 1 (by rfl) ⟨92522, by rfl⟩ : syracuseStep 123363 = 185045) B185045
theorem B123379 : Blo 119786 123379 := bstep (se 1 (by rfl) ⟨92534, by rfl⟩ : syracuseStep 123379 = 185069) B185069
theorem B156163 : Blo 119786 156163 := bstep (se 1 (by rfl) ⟨117122, by rfl⟩ : syracuseStep 156163 = 234245) B234245
theorem B123395 : Blo 119786 123395 := bstep (se 1 (by rfl) ⟨92546, by rfl⟩ : syracuseStep 123395 = 185093) B185093
theorem B123411 : Blo 119786 123411 := bstep (se 1 (by rfl) ⟨92558, by rfl⟩ : syracuseStep 123411 = 185117) B185117
theorem B123427 : Blo 119786 123427 := bstep (se 1 (by rfl) ⟨92570, by rfl⟩ : syracuseStep 123427 = 185141) B185141
theorem B123443 : Blo 119786 123443 := bstep (se 1 (by rfl) ⟨92582, by rfl⟩ : syracuseStep 123443 = 185165) B185165
theorem B123459 : Blo 119786 123459 := bstep (se 1 (by rfl) ⟨92594, by rfl⟩ : syracuseStep 123459 = 185189) B185189
theorem B123475 : Blo 119786 123475 := bstep (se 1 (by rfl) ⟨92606, by rfl⟩ : syracuseStep 123475 = 185213) B185213
theorem B156259 : Blo 119786 156259 := bstep (se 1 (by rfl) ⟨117194, by rfl⟩ : syracuseStep 156259 = 234389) B234389
theorem B123491 : Blo 119786 123491 := bstep (se 1 (by rfl) ⟨92618, by rfl⟩ : syracuseStep 123491 = 185237) B185237
theorem B123507 : Blo 119786 123507 := bstep (se 1 (by rfl) ⟨92630, by rfl⟩ : syracuseStep 123507 = 185261) B185261
theorem B123523 : Blo 119786 123523 := bstep (se 1 (by rfl) ⟨92642, by rfl⟩ : syracuseStep 123523 = 185285) B185285
theorem B123539 : Blo 119786 123539 := bstep (se 1 (by rfl) ⟨92654, by rfl⟩ : syracuseStep 123539 = 185309) B185309
theorem B123555 : Blo 119786 123555 := bstep (se 1 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 123555 = 185333) B185333
theorem B123571 : Blo 119786 123571 := bstep (se 1 (by rfl) ⟨92678, by rfl⟩ : syracuseStep 123571 = 185357) B185357
theorem B123587 : Blo 119786 123587 := bstep (se 1 (by rfl) ⟨92690, by rfl⟩ : syracuseStep 123587 = 185381) B185381
theorem B123603 : Blo 119786 123603 := bstep (se 1 (by rfl) ⟨92702, by rfl⟩ : syracuseStep 123603 = 185405) B185405
theorem B123619 : Blo 119786 123619 := bstep (se 1 (by rfl) ⟨92714, by rfl⟩ : syracuseStep 123619 = 185429) B185429
theorem B123635 : Blo 119786 123635 := bstep (se 1 (by rfl) ⟨92726, by rfl⟩ : syracuseStep 123635 = 185453) B185453
theorem B123651 : Blo 119786 123651 := bstep (se 1 (by rfl) ⟨92738, by rfl⟩ : syracuseStep 123651 = 185477) B185477
theorem B123667 : Blo 119786 123667 := bstep (se 1 (by rfl) ⟨92750, by rfl⟩ : syracuseStep 123667 = 185501) B185501
theorem B123683 : Blo 119786 123683 := bstep (se 1 (by rfl) ⟨92762, by rfl⟩ : syracuseStep 123683 = 185525) B185525
theorem B123699 : Blo 119786 123699 := bstep (se 1 (by rfl) ⟨92774, by rfl⟩ : syracuseStep 123699 = 185549) B185549
theorem B418627 : Blo 119786 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B123715 : Blo 119786 123715 := bstep (se 1 (by rfl) ⟨92786, by rfl⟩ : syracuseStep 123715 = 185573) B185573
theorem B123731 : Blo 119786 123731 := bstep (se 1 (by rfl) ⟨92798, by rfl⟩ : syracuseStep 123731 = 185597) B185597
theorem B123747 : Blo 119786 123747 := bstep (se 1 (by rfl) ⟨92810, by rfl⟩ : syracuseStep 123747 = 185621) B185621
theorem B123763 : Blo 119786 123763 := bstep (se 1 (by rfl) ⟨92822, by rfl⟩ : syracuseStep 123763 = 185645) B185645
theorem B123779 : Blo 119786 123779 := bstep (se 1 (by rfl) ⟨92834, by rfl⟩ : syracuseStep 123779 = 185669) B185669
theorem B746417 : Blo 119786 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B910277 : Blo 119786 910277 := bstep (se 4 (by rfl) ⟨85338, by rfl⟩ : syracuseStep 910277 = 170677) B170677
theorem B615437 : Blo 119786 615437 := bstep (se 3 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 615437 = 230789) B230789
theorem B1172677 : Blo 119786 1172677 := bstep (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) B219877
theorem B1402181 : Blo 119786 1402181 := bstep (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) B262909
theorem B157187 : Blo 119786 157187 := bstep (se 1 (by rfl) ⟨117890, by rfl⟩ : syracuseStep 157187 = 235781) B235781
theorem B779939 : Blo 119786 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B1402595 : Blo 119786 1402595 := bstep (se 1 (by rfl) ⟨1051946, by rfl⟩ : syracuseStep 1402595 = 2103893) B2103893
theorem B386819 : Blo 119786 386819 := bstep (se 1 (by rfl) ⟨290114, by rfl⟩ : syracuseStep 386819 = 580229) B580229
theorem B124787 : Blo 119786 124787 := bstep (se 1 (by rfl) ⟨93590, by rfl⟩ : syracuseStep 124787 = 187181) B187181
theorem B387089 : Blo 119786 387089 := bstep (se 2 (by rfl) ⟨145158, by rfl⟩ : syracuseStep 387089 = 290317) B290317
theorem B125011 : Blo 119786 125011 := bstep (se 1 (by rfl) ⟨93758, by rfl⟩ : syracuseStep 125011 = 187517) B187517
theorem B714865 : Blo 119786 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B682253 : Blo 119786 682253 := bstep (se 3 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 682253 = 255845) B255845
theorem B256529 : Blo 119786 256529 := bstep (se 2 (by rfl) ⟨96198, by rfl⟩ : syracuseStep 256529 = 192397) B192397
theorem B780941 : Blo 119786 780941 := bstep (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) B292853
theorem B519139 : Blo 119786 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B1043441 : Blo 119786 1043441 := bstep (se 2 (by rfl) ⟨391290, by rfl⟩ : syracuseStep 1043441 = 782581) B782581
theorem B257041 : Blo 119786 257041 := bstep (se 2 (by rfl) ⟨96390, by rfl⟩ : syracuseStep 257041 = 192781) B192781
theorem B1109189 : Blo 119786 1109189 := bstep (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) B207973
theorem B191987 : Blo 119786 191987 := bstep (se 1 (by rfl) ⟨143990, by rfl⟩ : syracuseStep 191987 = 287981) B287981
theorem B192179 : Blo 119786 192179 := bstep (se 1 (by rfl) ⟨144134, by rfl⟩ : syracuseStep 192179 = 288269) B288269
theorem B421613 : Blo 119786 421613 := bstep (se 3 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 421613 = 158105) B158105
theorem B618353 : Blo 119786 618353 := bstep (se 2 (by rfl) ⟨231882, by rfl⟩ : syracuseStep 618353 = 463765) B463765
theorem B389549 : Blo 119786 389549 := bstep (se 3 (by rfl) ⟨73040, by rfl⟩ : syracuseStep 389549 = 146081) B146081
theorem B258545 : Blo 119786 258545 := bstep (se 2 (by rfl) ⟨96954, by rfl⟩ : syracuseStep 258545 = 193909) B193909
theorem B1307461 : Blo 119786 1307461 := bstep (se 4 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 1307461 = 245149) B245149
theorem B258947 : Blo 119786 258947 := bstep (se 1 (by rfl) ⟨194210, by rfl⟩ : syracuseStep 258947 = 388421) B388421
theorem B193601 : Blo 119786 193601 := bstep (se 2 (by rfl) ⟨72600, by rfl⟩ : syracuseStep 193601 = 145201) B145201
theorem B685169 : Blo 119786 685169 := bstep (se 2 (by rfl) ⟨256938, by rfl⟩ : syracuseStep 685169 = 513877) B513877
theorem B128179 : Blo 119786 128179 := bstep (se 1 (by rfl) ⟨96134, by rfl⟩ : syracuseStep 128179 = 192269) B192269
theorem B619811 : Blo 119786 619811 := bstep (se 1 (by rfl) ⟨464858, by rfl⟩ : syracuseStep 619811 = 929717) B929717
theorem B521585 : Blo 119786 521585 := bstep (se 2 (by rfl) ⟨195594, by rfl⟩ : syracuseStep 521585 = 391189) B391189
theorem B587213 : Blo 119786 587213 := bstep (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) B220205
theorem B259843 : Blo 119786 259843 := bstep (se 1 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 259843 = 389765) B389765
theorem B456461 : Blo 119786 456461 := bstep (se 3 (by rfl) ⟨85586, by rfl⟩ : syracuseStep 456461 = 171173) B171173
theorem B587569 : Blo 119786 587569 := bstep (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) B440677
theorem B620621 : Blo 119786 620621 := bstep (se 3 (by rfl) ⟨116366, by rfl⟩ : syracuseStep 620621 = 232733) B232733
theorem B227441 : Blo 119786 227441 := bstep (se 2 (by rfl) ⟨85290, by rfl⟩ : syracuseStep 227441 = 170581) B170581
theorem B325795 : Blo 119786 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B391405 : Blo 119786 391405 := bstep (se 3 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 391405 = 146777) B146777
theorem B162049 : Blo 119786 162049 := bstep (se 2 (by rfl) ⟨60768, by rfl⟩ : syracuseStep 162049 = 121537) B121537
theorem B129443 : Blo 119786 129443 := bstep (se 1 (by rfl) ⟨97082, by rfl⟩ : syracuseStep 129443 = 194165) B194165
theorem B653795 : Blo 119786 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B227843 : Blo 119786 227843 := bstep (se 1 (by rfl) ⟨170882, by rfl⟩ : syracuseStep 227843 = 341765) B341765
theorem B686627 : Blo 119786 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B457265 : Blo 119786 457265 := bstep (se 2 (by rfl) ⟨171474, by rfl⟩ : syracuseStep 457265 = 342949) B342949
theorem B195139 : Blo 119786 195139 := bstep (se 1 (by rfl) ⟨146354, by rfl⟩ : syracuseStep 195139 = 292709) B292709
theorem B195185 : Blo 119786 195185 := bstep (se 2 (by rfl) ⟨73194, by rfl⟩ : syracuseStep 195185 = 146389) B146389
theorem B916109 : Blo 119786 916109 := bstep (se 3 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 916109 = 343541) B343541
theorem B391889 : Blo 119786 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B195283 : Blo 119786 195283 := bstep (se 1 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 195283 = 292925) B292925
theorem B162529 : Blo 119786 162529 := bstep (se 2 (by rfl) ⟨60948, by rfl⟩ : syracuseStep 162529 = 121897) B121897
theorem B555875 : Blo 119786 555875 := bstep (se 1 (by rfl) ⟨416906, by rfl⟩ : syracuseStep 555875 = 833813) B833813
theorem B326531 : Blo 119786 326531 := bstep (se 1 (by rfl) ⟨244898, by rfl⟩ : syracuseStep 326531 = 489797) B489797
theorem B1047437 : Blo 119786 1047437 := bstep (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) B392789
theorem B293777 : Blo 119786 293777 := bstep (se 2 (by rfl) ⟨110166, by rfl⟩ : syracuseStep 293777 = 220333) B220333
theorem B261073 : Blo 119786 261073 := bstep (se 2 (by rfl) ⟨97902, by rfl⟩ : syracuseStep 261073 = 195805) B195805
theorem B752645 : Blo 119786 752645 := bstep (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) B141121
theorem B1113101 : Blo 119786 1113101 := bstep (se 3 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 1113101 = 417413) B417413
theorem B130195 : Blo 119786 130195 := bstep (se 1 (by rfl) ⟨97646, by rfl⟩ : syracuseStep 130195 = 195293) B195293
theorem B457933 : Blo 119786 457933 := bstep (se 3 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 457933 = 171725) B171725
theorem B228739 : Blo 119786 228739 := bstep (se 1 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 228739 = 343109) B343109
theorem B687629 : Blo 119786 687629 := bstep (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) B257861
theorem B228899 : Blo 119786 228899 := bstep (se 1 (by rfl) ⟨171674, by rfl⟩ : syracuseStep 228899 = 343349) B343349
theorem B196177 : Blo 119786 196177 := bstep (se 2 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 196177 = 147133) B147133
theorem B654961 : Blo 119786 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B393137 : Blo 119786 393137 := bstep (se 2 (by rfl) ⟨147426, by rfl⟩ : syracuseStep 393137 = 294853) B294853
theorem B163795 : Blo 119786 163795 := bstep (se 1 (by rfl) ⟨122846, by rfl⟩ : syracuseStep 163795 = 245693) B245693
theorem B458723 : Blo 119786 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B524333 : Blo 119786 524333 := bstep (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) B196625
theorem B229529 : Blo 119786 229529 := bstep (se 2 (by rfl) ⟨86073, by rfl⟩ : syracuseStep 229529 = 172147) B172147
theorem B196825 : Blo 119786 196825 := bstep (se 2 (by rfl) ⟨73809, by rfl⟩ : syracuseStep 196825 = 147619) B147619
theorem B197081 : Blo 119786 197081 := bstep (se 2 (by rfl) ⟨73905, by rfl⟩ : syracuseStep 197081 = 147811) B147811
theorem B393751 : Blo 119786 393751 := bstep (se 1 (by rfl) ⟨295313, by rfl⟩ : syracuseStep 393751 = 590627) B590627
theorem B525017 : Blo 119786 525017 := bstep (se 2 (by rfl) ⟨196881, by rfl⟩ : syracuseStep 525017 = 393763) B393763
theorem B1114955 : Blo 119786 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B230273 : Blo 119786 230273 := bstep (se 2 (by rfl) ⟨86352, by rfl⟩ : syracuseStep 230273 = 172705) B172705
theorem B590723 : Blo 119786 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B459665 : Blo 119786 459665 := bstep (se 2 (by rfl) ⟨172374, by rfl⟩ : syracuseStep 459665 = 344749) B344749
theorem B328627 : Blo 119786 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B132139 : Blo 119786 132139 := bstep (se 1 (by rfl) ⟨99104, by rfl⟩ : syracuseStep 132139 = 198209) B198209
theorem B230539 : Blo 119786 230539 := bstep (se 1 (by rfl) ⟨172904, by rfl⟩ : syracuseStep 230539 = 345809) B345809
theorem B263321 : Blo 119786 263321 := bstep (se 2 (by rfl) ⟨98745, by rfl⟩ : syracuseStep 263321 = 197491) B197491
theorem B951587 : Blo 119786 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B1246529 : Blo 119786 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B394571 : Blo 119786 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B624023 : Blo 119786 624023 := bstep (se 1 (by rfl) ⟨468017, by rfl⟩ : syracuseStep 624023 = 936035) B936035
theorem B1377809 : Blo 119786 1377809 := bstep (se 2 (by rfl) ⟨516678, by rfl⟩ : syracuseStep 1377809 = 1033357) B1033357
theorem B263731 : Blo 119786 263731 := bstep (se 1 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 263731 = 395597) B395597
theorem B460363 : Blo 119786 460363 := bstep (se 1 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 460363 = 690545) B690545
theorem B230987 : Blo 119786 230987 := bstep (se 1 (by rfl) ⟨173240, by rfl⟩ : syracuseStep 230987 = 346481) B346481
theorem B886373 : Blo 119786 886373 := bstep (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) B166195
theorem B689795 : Blo 119786 689795 := bstep (se 1 (by rfl) ⟨517346, by rfl⟩ : syracuseStep 689795 = 1034693) B1034693
theorem B886403 : Blo 119786 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B231169 : Blo 119786 231169 := bstep (se 2 (by rfl) ⟨86688, by rfl⟩ : syracuseStep 231169 = 173377) B173377
theorem B460637 : Blo 119786 460637 := bstep (se 3 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 460637 = 172739) B172739
theorem B329665 : Blo 119786 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B526283 : Blo 119786 526283 := bstep (se 1 (by rfl) ⟨394712, by rfl⟩ : syracuseStep 526283 = 789425) B789425
theorem B526297 : Blo 119786 526297 := bstep (se 2 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 526297 = 394723) B394723
theorem B395225 : Blo 119786 395225 := bstep (se 2 (by rfl) ⟨148209, by rfl⟩ : syracuseStep 395225 = 296419) B296419
theorem B264217 : Blo 119786 264217 := bstep (se 2 (by rfl) ⟨99081, by rfl⟩ : syracuseStep 264217 = 198163) B198163
theorem B231511 : Blo 119786 231511 := bstep (se 1 (by rfl) ⟨173633, by rfl⟩ : syracuseStep 231511 = 347267) B347267
theorem B3967127 : Blo 119786 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B559325 : Blo 119786 559325 := bstep (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) B209747
theorem B231731 : Blo 119786 231731 := bstep (se 1 (by rfl) ⟨173798, by rfl⟩ : syracuseStep 231731 = 347597) B347597
theorem B526657 : Blo 119786 526657 := bstep (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) B394993
theorem B1182131 : Blo 119786 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B461335 : Blo 119786 461335 := bstep (se 1 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 461335 = 692003) B692003
theorem B231959 : Blo 119786 231959 := bstep (se 1 (by rfl) ⟨173969, by rfl⟩ : syracuseStep 231959 = 347939) B347939
theorem B526999 : Blo 119786 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B887557 : Blo 119786 887557 := bstep (se 4 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 887557 = 166417) B166417
theorem B232217 : Blo 119786 232217 := bstep (se 2 (by rfl) ⟨87081, by rfl⟩ : syracuseStep 232217 = 174163) B174163
theorem B166681 : Blo 119786 166681 := bstep (se 2 (by rfl) ⟨62505, by rfl⟩ : syracuseStep 166681 = 125011) B125011
theorem B953153 : Blo 119786 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B396353 : Blo 119786 396353 := bstep (se 2 (by rfl) ⟨148632, by rfl⟩ : syracuseStep 396353 = 297265) B297265
theorem B2001995 : Blo 119786 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B232627 : Blo 119786 232627 := bstep (se 1 (by rfl) ⟨174470, by rfl⟩ : syracuseStep 232627 = 348941) B348941
theorem B199883 : Blo 119786 199883 := bstep (se 1 (by rfl) ⟨149912, by rfl⟩ : syracuseStep 199883 = 299825) B299825
theorem B462125 : Blo 119786 462125 := bstep (se 3 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 462125 = 173297) B173297
theorem B3083669 : Blo 119786 3083669 := bstep (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) B144547
theorem B233113 : Blo 119786 233113 := bstep (se 2 (by rfl) ⟨87417, by rfl⟩ : syracuseStep 233113 = 174835) B174835
theorem B134923 : Blo 119786 134923 := bstep (se 1 (by rfl) ⟨101192, by rfl⟩ : syracuseStep 134923 = 202385) B202385
theorem B135031 : Blo 119786 135031 := bstep (se 1 (by rfl) ⟨101273, by rfl⟩ : syracuseStep 135031 = 202547) B202547
theorem B692185 : Blo 119786 692185 := bstep (se 2 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 692185 = 519139) B519139
theorem B135211 : Blo 119786 135211 := bstep (se 1 (by rfl) ⟨101408, by rfl⟩ : syracuseStep 135211 = 202817) B202817
theorem B135319 : Blo 119786 135319 := bstep (se 1 (by rfl) ⟨101489, by rfl⟩ : syracuseStep 135319 = 202979) B202979
theorem B233675 : Blo 119786 233675 := bstep (se 1 (by rfl) ⟨175256, by rfl⟩ : syracuseStep 233675 = 350513) B350513
theorem B135499 : Blo 119786 135499 := bstep (se 1 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 135499 = 203249) B203249
theorem B2232677 : Blo 119786 2232677 := bstep (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) B418627
theorem B1380725 : Blo 119786 1380725 := bstep (se 5 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 1380725 = 129443) B129443
theorem B233857 : Blo 119786 233857 := bstep (se 2 (by rfl) ⟨87696, by rfl⟩ : syracuseStep 233857 = 175393) B175393
theorem B135607 : Blo 119786 135607 := bstep (se 1 (by rfl) ⟨101705, by rfl⟩ : syracuseStep 135607 = 203411) B203411
theorem B135787 : Blo 119786 135787 := bstep (se 1 (by rfl) ⟨101840, by rfl⟩ : syracuseStep 135787 = 203681) B203681
theorem B266905 : Blo 119786 266905 := bstep (se 2 (by rfl) ⟨100089, by rfl⟩ : syracuseStep 266905 = 200179) B200179
theorem B463553 : Blo 119786 463553 := bstep (se 2 (by rfl) ⟨173832, by rfl⟩ : syracuseStep 463553 = 347665) B347665
theorem B135895 : Blo 119786 135895 := bstep (se 1 (by rfl) ⟨101921, by rfl⟩ : syracuseStep 135895 = 203843) B203843
theorem B136075 : Blo 119786 136075 := bstep (se 1 (by rfl) ⟨102056, by rfl⟩ : syracuseStep 136075 = 204113) B204113
theorem B693143 : Blo 119786 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B2200499 : Blo 119786 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B332765 : Blo 119786 332765 := bstep (se 3 (by rfl) ⟨62393, by rfl⟩ : syracuseStep 332765 = 124787) B124787
theorem B136183 : Blo 119786 136183 := bstep (se 1 (by rfl) ⟨102137, by rfl⟩ : syracuseStep 136183 = 204275) B204275
theorem B234571 : Blo 119786 234571 := bstep (se 1 (by rfl) ⟨175928, by rfl⟩ : syracuseStep 234571 = 351857) B351857
theorem B234647 : Blo 119786 234647 := bstep (se 1 (by rfl) ⟨175985, by rfl⟩ : syracuseStep 234647 = 351971) B351971
theorem B136363 : Blo 119786 136363 := bstep (se 1 (by rfl) ⟨102272, by rfl⟩ : syracuseStep 136363 = 204545) B204545
theorem B496813 : Blo 119786 496813 := bstep (se 3 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 496813 = 186305) B186305
theorem B136471 : Blo 119786 136471 := bstep (se 1 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 136471 = 204707) B204707
theorem B136651 : Blo 119786 136651 := bstep (se 1 (by rfl) ⟨102488, by rfl⟩ : syracuseStep 136651 = 204977) B204977
theorem B235009 : Blo 119786 235009 := bstep (se 2 (by rfl) ⟨88128, by rfl⟩ : syracuseStep 235009 = 176257) B176257
theorem B136759 : Blo 119786 136759 := bstep (se 1 (by rfl) ⟨102569, by rfl⟩ : syracuseStep 136759 = 205139) B205139
theorem B792139 : Blo 119786 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B136939 : Blo 119786 136939 := bstep (se 1 (by rfl) ⟨102704, by rfl⟩ : syracuseStep 136939 = 205409) B205409
theorem B1054529 : Blo 119786 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B137047 : Blo 119786 137047 := bstep (se 1 (by rfl) ⟨102785, by rfl⟩ : syracuseStep 137047 = 205571) B205571
theorem B497611 : Blo 119786 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B202763 : Blo 119786 202763 := bstep (se 1 (by rfl) ⟨152072, by rfl⟩ : syracuseStep 202763 = 304145) B304145
theorem B137227 : Blo 119786 137227 := bstep (se 1 (by rfl) ⟨102920, by rfl⟩ : syracuseStep 137227 = 205841) B205841
theorem B5150789 : Blo 119786 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B137335 : Blo 119786 137335 := bstep (se 1 (by rfl) ⟨103001, by rfl⟩ : syracuseStep 137335 = 206003) B206003
theorem B202891 : Blo 119786 202891 := bstep (se 1 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 202891 = 304337) B304337
theorem B465041 : Blo 119786 465041 := bstep (se 2 (by rfl) ⟨174390, by rfl⟩ : syracuseStep 465041 = 348781) B348781
theorem B203033 : Blo 119786 203033 := bstep (se 2 (by rfl) ⟨76137, by rfl⟩ : syracuseStep 203033 = 152275) B152275
theorem B137515 : Blo 119786 137515 := bstep (se 1 (by rfl) ⟨103136, by rfl⟩ : syracuseStep 137515 = 206273) B206273
theorem B137623 : Blo 119786 137623 := bstep (se 1 (by rfl) ⟨103217, by rfl⟩ : syracuseStep 137623 = 206435) B206435
theorem B203161 : Blo 119786 203161 := bstep (se 2 (by rfl) ⟨76185, by rfl⟩ : syracuseStep 203161 = 152371) B152371
theorem B1743281 : Blo 119786 1743281 := bstep (se 2 (by rfl) ⟨653730, by rfl⟩ : syracuseStep 1743281 = 1307461) B1307461
theorem B137803 : Blo 119786 137803 := bstep (se 1 (by rfl) ⟨103352, by rfl⟩ : syracuseStep 137803 = 206705) B206705
theorem B465497 : Blo 119786 465497 := bstep (se 2 (by rfl) ⟨174561, by rfl⟩ : syracuseStep 465497 = 349123) B349123
theorem B137911 : Blo 119786 137911 := bstep (se 1 (by rfl) ⟨103433, by rfl⟩ : syracuseStep 137911 = 206867) B206867
theorem B465709 : Blo 119786 465709 := bstep (se 3 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 465709 = 174641) B174641
theorem B891749 : Blo 119786 891749 := bstep (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) B167203
theorem B138091 : Blo 119786 138091 := bstep (se 1 (by rfl) ⟨103568, by rfl⟩ : syracuseStep 138091 = 207137) B207137
theorem B170905 : Blo 119786 170905 := bstep (se 2 (by rfl) ⟨64089, by rfl⟩ : syracuseStep 170905 = 128179) B128179
theorem B203735 : Blo 119786 203735 := bstep (se 1 (by rfl) ⟨152801, by rfl⟩ : syracuseStep 203735 = 305603) B305603
theorem B498649 : Blo 119786 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B138199 : Blo 119786 138199 := bstep (se 1 (by rfl) ⟨103649, by rfl⟩ : syracuseStep 138199 = 207299) B207299
theorem B171019 : Blo 119786 171019 := bstep (se 1 (by rfl) ⟨128264, by rfl⟩ : syracuseStep 171019 = 256529) B256529
theorem B662573 : Blo 119786 662573 := bstep (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) B248465
theorem B203863 : Blo 119786 203863 := bstep (se 1 (by rfl) ⟨152897, by rfl⟩ : syracuseStep 203863 = 305795) B305795
theorem B466013 : Blo 119786 466013 := bstep (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) B174755
theorem B138379 : Blo 119786 138379 := bstep (se 1 (by rfl) ⟨103784, by rfl⟩ : syracuseStep 138379 = 207569) B207569
theorem B138487 : Blo 119786 138487 := bstep (se 1 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 138487 = 207731) B207731
theorem B695627 : Blo 119786 695627 := bstep (se 1 (by rfl) ⟨521720, by rfl⟩ : syracuseStep 695627 = 1043441) B1043441
theorem B269657 : Blo 119786 269657 := bstep (se 2 (by rfl) ⟨101121, by rfl⟩ : syracuseStep 269657 = 202243) B202243
theorem B138667 : Blo 119786 138667 := bstep (se 1 (by rfl) ⟨104000, by rfl⟩ : syracuseStep 138667 = 208001) B208001
theorem B269747 : Blo 119786 269747 := bstep (se 1 (by rfl) ⟨202310, by rfl⟩ : syracuseStep 269747 = 404621) B404621
theorem B269783 : Blo 119786 269783 := bstep (se 1 (by rfl) ⟨202337, by rfl⟩ : syracuseStep 269783 = 404675) B404675
theorem B138775 : Blo 119786 138775 := bstep (se 1 (by rfl) ⟨104081, by rfl⟩ : syracuseStep 138775 = 208163) B208163
theorem B368221 : Blo 119786 368221 := bstep (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) B138083
theorem B269963 : Blo 119786 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B270017 : Blo 119786 270017 := bstep (se 2 (by rfl) ⟨101256, by rfl⟩ : syracuseStep 270017 = 202513) B202513
theorem B204491 : Blo 119786 204491 := bstep (se 1 (by rfl) ⟨153368, by rfl⟩ : syracuseStep 204491 = 306737) B306737
theorem B138955 : Blo 119786 138955 := bstep (se 1 (by rfl) ⟨104216, by rfl⟩ : syracuseStep 138955 = 208433) B208433
theorem B139063 : Blo 119786 139063 := bstep (se 1 (by rfl) ⟨104297, by rfl⟩ : syracuseStep 139063 = 208595) B208595
theorem B204619 : Blo 119786 204619 := bstep (se 1 (by rfl) ⟨153464, by rfl⟩ : syracuseStep 204619 = 306929) B306929
theorem B270233 : Blo 119786 270233 := bstep (se 2 (by rfl) ⟨101337, by rfl⟩ : syracuseStep 270233 = 202675) B202675
theorem B204761 : Blo 119786 204761 := bstep (se 2 (by rfl) ⟨76785, by rfl⟩ : syracuseStep 204761 = 153571) B153571
theorem B139243 : Blo 119786 139243 := bstep (se 1 (by rfl) ⟨104432, by rfl⟩ : syracuseStep 139243 = 208865) B208865
theorem B270323 : Blo 119786 270323 := bstep (se 1 (by rfl) ⟨202742, by rfl⟩ : syracuseStep 270323 = 405485) B405485
theorem B270359 : Blo 119786 270359 := bstep (se 1 (by rfl) ⟨202769, by rfl⟩ : syracuseStep 270359 = 405539) B405539
theorem B204889 : Blo 119786 204889 := bstep (se 2 (by rfl) ⟨76833, by rfl⟩ : syracuseStep 204889 = 153667) B153667
theorem B270539 : Blo 119786 270539 := bstep (se 1 (by rfl) ⟨202904, by rfl⟩ : syracuseStep 270539 = 405809) B405809
theorem B434393 : Blo 119786 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B270593 : Blo 119786 270593 := bstep (se 2 (by rfl) ⟨101472, by rfl⟩ : syracuseStep 270593 = 202945) B202945
theorem B172363 : Blo 119786 172363 := bstep (se 1 (by rfl) ⟨129272, by rfl⟩ : syracuseStep 172363 = 258545) B258545
theorem B270809 : Blo 119786 270809 := bstep (se 2 (by rfl) ⟨101553, by rfl⟩ : syracuseStep 270809 = 203107) B203107
theorem B270899 : Blo 119786 270899 := bstep (se 1 (by rfl) ⟨203174, by rfl⟩ : syracuseStep 270899 = 406349) B406349
theorem B270935 : Blo 119786 270935 := bstep (se 1 (by rfl) ⟨203201, by rfl⟩ : syracuseStep 270935 = 406403) B406403
theorem B172631 : Blo 119786 172631 := bstep (se 1 (by rfl) ⟨129473, by rfl⟩ : syracuseStep 172631 = 258947) B258947
theorem B205463 : Blo 119786 205463 := bstep (se 1 (by rfl) ⟨154097, by rfl⟩ : syracuseStep 205463 = 308195) B308195
theorem B271115 : Blo 119786 271115 := bstep (se 1 (by rfl) ⟨203336, by rfl⟩ : syracuseStep 271115 = 406673) B406673
theorem B205591 : Blo 119786 205591 := bstep (se 1 (by rfl) ⟨154193, by rfl⟩ : syracuseStep 205591 = 308387) B308387
theorem B271169 : Blo 119786 271169 := bstep (se 2 (by rfl) ⟨101688, by rfl⟩ : syracuseStep 271169 = 203377) B203377
theorem B271385 : Blo 119786 271385 := bstep (se 2 (by rfl) ⟨101769, by rfl⟩ : syracuseStep 271385 = 203539) B203539
theorem B271475 : Blo 119786 271475 := bstep (se 1 (by rfl) ⟨203606, by rfl⟩ : syracuseStep 271475 = 407213) B407213
theorem B271511 : Blo 119786 271511 := bstep (se 1 (by rfl) ⟨203633, by rfl⟩ : syracuseStep 271511 = 407267) B407267
theorem B304307 : Blo 119786 304307 := bstep (se 1 (by rfl) ⟨228230, by rfl⟩ : syracuseStep 304307 = 456461) B456461
theorem B271691 : Blo 119786 271691 := bstep (se 1 (by rfl) ⟨203768, by rfl⟩ : syracuseStep 271691 = 407537) B407537
theorem B271745 : Blo 119786 271745 := bstep (se 2 (by rfl) ⟨101904, by rfl⟩ : syracuseStep 271745 = 203809) B203809
theorem B206219 : Blo 119786 206219 := bstep (se 1 (by rfl) ⟨154664, by rfl⟩ : syracuseStep 206219 = 309329) B309329
theorem B206347 : Blo 119786 206347 := bstep (se 1 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 206347 = 309521) B309521
theorem B173593 : Blo 119786 173593 := bstep (se 2 (by rfl) ⟨65097, by rfl⟩ : syracuseStep 173593 = 130195) B130195
theorem B271961 : Blo 119786 271961 := bstep (se 2 (by rfl) ⟨101985, by rfl⟩ : syracuseStep 271961 = 203971) B203971
theorem B468611 : Blo 119786 468611 := bstep (se 1 (by rfl) ⟨351458, by rfl⟩ : syracuseStep 468611 = 702917) B702917
theorem B468625 : Blo 119786 468625 := bstep (se 2 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 468625 = 351469) B351469
theorem B435863 : Blo 119786 435863 := bstep (se 1 (by rfl) ⟨326897, by rfl⟩ : syracuseStep 435863 = 653795) B653795
theorem B206489 : Blo 119786 206489 := bstep (se 2 (by rfl) ⟨77433, by rfl⟩ : syracuseStep 206489 = 154867) B154867
theorem B272051 : Blo 119786 272051 := bstep (se 1 (by rfl) ⟨204038, by rfl⟩ : syracuseStep 272051 = 408077) B408077
theorem B304843 : Blo 119786 304843 := bstep (se 1 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 304843 = 457265) B457265
theorem B272087 : Blo 119786 272087 := bstep (se 1 (by rfl) ⟨204065, by rfl⟩ : syracuseStep 272087 = 408131) B408131
theorem B206617 : Blo 119786 206617 := bstep (se 2 (by rfl) ⟨77481, by rfl⟩ : syracuseStep 206617 = 154963) B154963
theorem B304985 : Blo 119786 304985 := bstep (se 2 (by rfl) ⟨114369, by rfl⟩ : syracuseStep 304985 = 228739) B228739
theorem B272267 : Blo 119786 272267 := bstep (se 1 (by rfl) ⟨204200, by rfl⟩ : syracuseStep 272267 = 408401) B408401
theorem B370583 : Blo 119786 370583 := bstep (se 1 (by rfl) ⟨277937, by rfl⟩ : syracuseStep 370583 = 555875) B555875
theorem B698291 : Blo 119786 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B272321 : Blo 119786 272321 := bstep (se 2 (by rfl) ⟨102120, by rfl⟩ : syracuseStep 272321 = 204241) B204241
theorem B468929 : Blo 119786 468929 := bstep (se 2 (by rfl) ⟨175848, by rfl⟩ : syracuseStep 468929 = 351697) B351697
theorem B501763 : Blo 119786 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B272537 : Blo 119786 272537 := bstep (se 2 (by rfl) ⟨102201, by rfl⟩ : syracuseStep 272537 = 204403) B204403
theorem B272627 : Blo 119786 272627 := bstep (se 1 (by rfl) ⟨204470, by rfl⟩ : syracuseStep 272627 = 408941) B408941
theorem B272663 : Blo 119786 272663 := bstep (se 1 (by rfl) ⟨204497, by rfl⟩ : syracuseStep 272663 = 408995) B408995
theorem B207191 : Blo 119786 207191 := bstep (se 1 (by rfl) ⟨155393, by rfl⟩ : syracuseStep 207191 = 310787) B310787
theorem B469421 : Blo 119786 469421 := bstep (se 3 (by rfl) ⟨88016, by rfl⟩ : syracuseStep 469421 = 176033) B176033
theorem B272843 : Blo 119786 272843 := bstep (se 1 (by rfl) ⟨204632, by rfl⟩ : syracuseStep 272843 = 409265) B409265
theorem B207319 : Blo 119786 207319 := bstep (se 1 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 207319 = 310979) B310979
theorem B272897 : Blo 119786 272897 := bstep (se 2 (by rfl) ⟨102336, by rfl⟩ : syracuseStep 272897 = 204673) B204673
theorem B469597 : Blo 119786 469597 := bstep (se 3 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 469597 = 176099) B176099
theorem B305815 : Blo 119786 305815 := bstep (se 1 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 305815 = 458723) B458723
theorem B273113 : Blo 119786 273113 := bstep (se 2 (by rfl) ⟨102417, by rfl⟩ : syracuseStep 273113 = 204835) B204835
theorem B273203 : Blo 119786 273203 := bstep (se 1 (by rfl) ⟨204902, by rfl⟩ : syracuseStep 273203 = 409805) B409805
theorem B273239 : Blo 119786 273239 := bstep (se 1 (by rfl) ⟨204929, by rfl⟩ : syracuseStep 273239 = 409859) B409859
theorem B175051 : Blo 119786 175051 := bstep (se 1 (by rfl) ⟨131288, by rfl⟩ : syracuseStep 175051 = 262577) B262577
theorem B175063 : Blo 119786 175063 := bstep (se 1 (by rfl) ⟨131297, by rfl⟩ : syracuseStep 175063 = 262595) B262595
theorem B1780697 : Blo 119786 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B273419 : Blo 119786 273419 := bstep (se 1 (by rfl) ⟨205064, by rfl⟩ : syracuseStep 273419 = 410129) B410129
theorem B273473 : Blo 119786 273473 := bstep (se 2 (by rfl) ⟨102552, by rfl⟩ : syracuseStep 273473 = 205105) B205105
theorem B306251 : Blo 119786 306251 := bstep (se 1 (by rfl) ⟨229688, by rfl⟩ : syracuseStep 306251 = 459377) B459377
theorem B207947 : Blo 119786 207947 := bstep (se 1 (by rfl) ⟨155960, by rfl⟩ : syracuseStep 207947 = 311921) B311921
theorem B208075 : Blo 119786 208075 := bstep (se 1 (by rfl) ⟨156056, by rfl⟩ : syracuseStep 208075 = 312113) B312113
theorem B437507 : Blo 119786 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B273689 : Blo 119786 273689 := bstep (se 2 (by rfl) ⟨102633, by rfl⟩ : syracuseStep 273689 = 205267) B205267
theorem B208217 : Blo 119786 208217 := bstep (se 2 (by rfl) ⟨78081, by rfl⟩ : syracuseStep 208217 = 156163) B156163
theorem B699749 : Blo 119786 699749 := bstep (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) B131203
theorem B273779 : Blo 119786 273779 := bstep (se 1 (by rfl) ⟨205334, by rfl⟩ : syracuseStep 273779 = 410669) B410669
theorem B273815 : Blo 119786 273815 := bstep (se 1 (by rfl) ⟨205361, by rfl⟩ : syracuseStep 273815 = 410723) B410723
theorem B306625 : Blo 119786 306625 := bstep (se 2 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 306625 = 229969) B229969
theorem B208345 : Blo 119786 208345 := bstep (se 2 (by rfl) ⟨78129, by rfl⟩ : syracuseStep 208345 = 156259) B156259
theorem B273995 : Blo 119786 273995 := bstep (se 1 (by rfl) ⟨205496, by rfl⟩ : syracuseStep 273995 = 410993) B410993
theorem B274049 : Blo 119786 274049 := bstep (se 2 (by rfl) ⟨102768, by rfl⟩ : syracuseStep 274049 = 205537) B205537
theorem B1584845 : Blo 119786 1584845 := bstep (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) B594317
theorem B405323 : Blo 119786 405323 := bstep (se 1 (by rfl) ⟨303992, by rfl⟩ : syracuseStep 405323 = 607985) B607985
theorem B208727 : Blo 119786 208727 := bstep (se 1 (by rfl) ⟨156545, by rfl⟩ : syracuseStep 208727 = 313091) B313091
theorem B274265 : Blo 119786 274265 := bstep (se 2 (by rfl) ⟨102849, by rfl⟩ : syracuseStep 274265 = 205699) B205699
theorem B1781621 : Blo 119786 1781621 := bstep (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) B167027
theorem B274355 : Blo 119786 274355 := bstep (se 1 (by rfl) ⟨205766, by rfl⟩ : syracuseStep 274355 = 411533) B411533
theorem B274391 : Blo 119786 274391 := bstep (se 1 (by rfl) ⟨205793, by rfl⟩ : syracuseStep 274391 = 411587) B411587
theorem B700433 : Blo 119786 700433 := bstep (se 2 (by rfl) ⟨262662, by rfl⟩ : syracuseStep 700433 = 525325) B525325
theorem B307223 : Blo 119786 307223 := bstep (se 1 (by rfl) ⟨230417, by rfl⟩ : syracuseStep 307223 = 460835) B460835
theorem B405593 : Blo 119786 405593 := bstep (se 2 (by rfl) ⟨152097, by rfl⟩ : syracuseStep 405593 = 304195) B304195
theorem B274571 : Blo 119786 274571 := bstep (se 1 (by rfl) ⟨205928, by rfl⟩ : syracuseStep 274571 = 411857) B411857
theorem B274625 : Blo 119786 274625 := bstep (se 2 (by rfl) ⟨102984, by rfl⟩ : syracuseStep 274625 = 205969) B205969
theorem B274841 : Blo 119786 274841 := bstep (se 2 (by rfl) ⟨103065, by rfl⟩ : syracuseStep 274841 = 206131) B206131
theorem B274931 : Blo 119786 274931 := bstep (se 1 (by rfl) ⟨206198, by rfl⟩ : syracuseStep 274931 = 412397) B412397
theorem B274967 : Blo 119786 274967 := bstep (se 1 (by rfl) ⟨206225, by rfl⟩ : syracuseStep 274967 = 412451) B412451
theorem B275147 : Blo 119786 275147 := bstep (se 1 (by rfl) ⟨206360, by rfl⟩ : syracuseStep 275147 = 412721) B412721
theorem B373469 : Blo 119786 373469 := bstep (se 3 (by rfl) ⟨70025, by rfl⟩ : syracuseStep 373469 = 140051) B140051
theorem B275201 : Blo 119786 275201 := bstep (se 2 (by rfl) ⟨103200, by rfl⟩ : syracuseStep 275201 = 206401) B206401
theorem B406295 : Blo 119786 406295 := bstep (se 1 (by rfl) ⟨304721, by rfl⟩ : syracuseStep 406295 = 609443) B609443
theorem B308033 : Blo 119786 308033 := bstep (se 2 (by rfl) ⟨115512, by rfl⟩ : syracuseStep 308033 = 231025) B231025
theorem B275417 : Blo 119786 275417 := bstep (se 2 (by rfl) ⟨103281, by rfl⟩ : syracuseStep 275417 = 206563) B206563
theorem B275507 : Blo 119786 275507 := bstep (se 1 (by rfl) ⟨206630, by rfl⟩ : syracuseStep 275507 = 413261) B413261
theorem B275543 : Blo 119786 275543 := bstep (se 1 (by rfl) ⟨206657, by rfl⟩ : syracuseStep 275543 = 413315) B413315
theorem B505025 : Blo 119786 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B275723 : Blo 119786 275723 := bstep (se 1 (by rfl) ⟨206792, by rfl⟩ : syracuseStep 275723 = 413585) B413585
theorem B406835 : Blo 119786 406835 := bstep (se 1 (by rfl) ⟨305126, by rfl⟩ : syracuseStep 406835 = 610253) B610253
theorem B275777 : Blo 119786 275777 := bstep (se 2 (by rfl) ⟨103416, by rfl⟩ : syracuseStep 275777 = 206833) B206833
theorem B308569 : Blo 119786 308569 := bstep (se 2 (by rfl) ⟨115713, by rfl⟩ : syracuseStep 308569 = 231427) B231427
theorem B275993 : Blo 119786 275993 := bstep (se 2 (by rfl) ⟨103497, by rfl⟩ : syracuseStep 275993 = 206995) B206995
theorem B407105 : Blo 119786 407105 := bstep (se 2 (by rfl) ⟨152664, by rfl⟩ : syracuseStep 407105 = 305329) B305329
theorem B276083 : Blo 119786 276083 := bstep (se 1 (by rfl) ⟨207062, by rfl⟩ : syracuseStep 276083 = 414125) B414125
theorem B276119 : Blo 119786 276119 := bstep (se 1 (by rfl) ⟨207089, by rfl⟩ : syracuseStep 276119 = 414179) B414179
theorem B767819 : Blo 119786 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B276299 : Blo 119786 276299 := bstep (se 1 (by rfl) ⟨207224, by rfl⟩ : syracuseStep 276299 = 414449) B414449
theorem B276353 : Blo 119786 276353 := bstep (se 2 (by rfl) ⟨103632, by rfl⟩ : syracuseStep 276353 = 207265) B207265
theorem B735277 : Blo 119786 735277 := bstep (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) B275729
theorem B14956597 : Blo 119786 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B276569 : Blo 119786 276569 := bstep (se 2 (by rfl) ⟨103713, by rfl⟩ : syracuseStep 276569 = 207427) B207427
theorem B407645 : Blo 119786 407645 := bstep (se 3 (by rfl) ⟨76433, by rfl⟩ : syracuseStep 407645 = 152867) B152867
theorem B276659 : Blo 119786 276659 := bstep (se 1 (by rfl) ⟨207494, by rfl⟩ : syracuseStep 276659 = 414989) B414989
theorem B276695 : Blo 119786 276695 := bstep (se 1 (by rfl) ⟨207521, by rfl⟩ : syracuseStep 276695 = 415043) B415043
theorem B211339 : Blo 119786 211339 := bstep (se 1 (by rfl) ⟨158504, by rfl⟩ : syracuseStep 211339 = 317009) B317009
theorem B276875 : Blo 119786 276875 := bstep (se 1 (by rfl) ⟨207656, by rfl⟩ : syracuseStep 276875 = 415313) B415313
theorem B309683 : Blo 119786 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B276929 : Blo 119786 276929 := bstep (se 2 (by rfl) ⟨103848, by rfl⟩ : syracuseStep 276929 = 207697) B207697
theorem B244183 : Blo 119786 244183 := bstep (se 1 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 244183 = 366275) B366275
theorem B145931 : Blo 119786 145931 := bstep (se 1 (by rfl) ⟨109448, by rfl⟩ : syracuseStep 145931 = 218897) B218897
theorem B277145 : Blo 119786 277145 := bstep (se 2 (by rfl) ⟨103929, by rfl⟩ : syracuseStep 277145 = 207859) B207859
theorem B342721 : Blo 119786 342721 := bstep (se 2 (by rfl) ⟨128520, by rfl⟩ : syracuseStep 342721 = 257041) B257041
theorem B309977 : Blo 119786 309977 := bstep (se 2 (by rfl) ⟨116241, by rfl⟩ : syracuseStep 309977 = 232483) B232483
theorem B277235 : Blo 119786 277235 := bstep (se 1 (by rfl) ⟨207926, by rfl⟩ : syracuseStep 277235 = 415853) B415853
theorem B277271 : Blo 119786 277271 := bstep (se 1 (by rfl) ⟨207953, by rfl⟩ : syracuseStep 277271 = 415907) B415907
theorem B441139 : Blo 119786 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B277451 : Blo 119786 277451 := bstep (se 1 (by rfl) ⟨208088, by rfl⟩ : syracuseStep 277451 = 416177) B416177
theorem B277505 : Blo 119786 277505 := bstep (se 2 (by rfl) ⟨104064, by rfl⟩ : syracuseStep 277505 = 208129) B208129
theorem B703667 : Blo 119786 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B408779 : Blo 119786 408779 := bstep (se 1 (by rfl) ⟨306584, by rfl⟩ : syracuseStep 408779 = 613169) B613169
theorem B277721 : Blo 119786 277721 := bstep (se 2 (by rfl) ⟨104145, by rfl⟩ : syracuseStep 277721 = 208291) B208291
theorem B277811 : Blo 119786 277811 := bstep (se 1 (by rfl) ⟨208358, by rfl⟩ : syracuseStep 277811 = 416717) B416717
theorem B277847 : Blo 119786 277847 := bstep (se 1 (by rfl) ⟨208385, by rfl⟩ : syracuseStep 277847 = 416771) B416771
theorem B769459 : Blo 119786 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B409049 : Blo 119786 409049 := bstep (se 2 (by rfl) ⟨153393, by rfl⟩ : syracuseStep 409049 = 306787) B306787
theorem B179723 : Blo 119786 179723 := bstep (se 1 (by rfl) ⟨134792, by rfl⟩ : syracuseStep 179723 = 269585) B269585
theorem B278027 : Blo 119786 278027 := bstep (se 1 (by rfl) ⟨208520, by rfl⟩ : syracuseStep 278027 = 417041) B417041
theorem B179735 : Blo 119786 179735 := bstep (se 1 (by rfl) ⟨134801, by rfl⟩ : syracuseStep 179735 = 269603) B269603
theorem B278081 : Blo 119786 278081 := bstep (se 2 (by rfl) ⟨104280, by rfl⟩ : syracuseStep 278081 = 208561) B208561
theorem B179801 : Blo 119786 179801 := bstep (se 2 (by rfl) ⟨67425, by rfl⟩ : syracuseStep 179801 = 134851) B134851
theorem B179915 : Blo 119786 179915 := bstep (se 1 (by rfl) ⟨134936, by rfl⟩ : syracuseStep 179915 = 269873) B269873
theorem B179927 : Blo 119786 179927 := bstep (se 1 (by rfl) ⟨134945, by rfl⟩ : syracuseStep 179927 = 269891) B269891
theorem B1392389 : Blo 119786 1392389 := bstep (se 4 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 1392389 = 261073) B261073
theorem B179993 : Blo 119786 179993 := bstep (se 2 (by rfl) ⟨67497, by rfl⟩ : syracuseStep 179993 = 134995) B134995
theorem B278297 : Blo 119786 278297 := bstep (se 2 (by rfl) ⟨104361, by rfl⟩ : syracuseStep 278297 = 208723) B208723
theorem B278387 : Blo 119786 278387 := bstep (se 1 (by rfl) ⟨208790, by rfl⟩ : syracuseStep 278387 = 417581) B417581
theorem B180107 : Blo 119786 180107 := bstep (se 1 (by rfl) ⟨135080, by rfl⟩ : syracuseStep 180107 = 270161) B270161
theorem B180119 : Blo 119786 180119 := bstep (se 1 (by rfl) ⟨135089, by rfl⟩ : syracuseStep 180119 = 270179) B270179
theorem B278423 : Blo 119786 278423 := bstep (se 1 (by rfl) ⟨208817, by rfl⟩ : syracuseStep 278423 = 417635) B417635
theorem B180185 : Blo 119786 180185 := bstep (se 2 (by rfl) ⟨67569, by rfl⟩ : syracuseStep 180185 = 135139) B135139
theorem B180299 : Blo 119786 180299 := bstep (se 1 (by rfl) ⟨135224, by rfl⟩ : syracuseStep 180299 = 270449) B270449
theorem B180311 : Blo 119786 180311 := bstep (se 1 (by rfl) ⟨135233, by rfl⟩ : syracuseStep 180311 = 270467) B270467
theorem B409751 : Blo 119786 409751 := bstep (se 1 (by rfl) ⟨307313, by rfl⟩ : syracuseStep 409751 = 614627) B614627
theorem B180377 : Blo 119786 180377 := bstep (se 2 (by rfl) ⟨67641, by rfl⟩ : syracuseStep 180377 = 135283) B135283
theorem B180491 : Blo 119786 180491 := bstep (se 1 (by rfl) ⟨135368, by rfl⟩ : syracuseStep 180491 = 270737) B270737
theorem B180503 : Blo 119786 180503 := bstep (se 1 (by rfl) ⟨135377, by rfl⟩ : syracuseStep 180503 = 270755) B270755
theorem B311627 : Blo 119786 311627 := bstep (se 1 (by rfl) ⟨233720, by rfl⟩ : syracuseStep 311627 = 467441) B467441
theorem B180569 : Blo 119786 180569 := bstep (se 2 (by rfl) ⟨67713, by rfl⟩ : syracuseStep 180569 = 135427) B135427
theorem B180683 : Blo 119786 180683 := bstep (se 1 (by rfl) ⟨135512, by rfl⟩ : syracuseStep 180683 = 271025) B271025
theorem B180695 : Blo 119786 180695 := bstep (se 1 (by rfl) ⟨135521, by rfl⟩ : syracuseStep 180695 = 271043) B271043
theorem B180761 : Blo 119786 180761 := bstep (se 2 (by rfl) ⟨67785, by rfl⟩ : syracuseStep 180761 = 135571) B135571
theorem B606851 : Blo 119786 606851 := bstep (se 1 (by rfl) ⟨455138, by rfl⟩ : syracuseStep 606851 = 910277) B910277
theorem B180875 : Blo 119786 180875 := bstep (se 1 (by rfl) ⟨135656, by rfl⟩ : syracuseStep 180875 = 271313) B271313
theorem B180887 : Blo 119786 180887 := bstep (se 1 (by rfl) ⟨135665, by rfl⟩ : syracuseStep 180887 = 271331) B271331
theorem B934577 : Blo 119786 934577 := bstep (se 2 (by rfl) ⟨350466, by rfl⟩ : syracuseStep 934577 = 700933) B700933
theorem B410291 : Blo 119786 410291 := bstep (se 1 (by rfl) ⟨307718, by rfl⟩ : syracuseStep 410291 = 615437) B615437
theorem B180953 : Blo 119786 180953 := bstep (se 2 (by rfl) ⟨67857, by rfl⟩ : syracuseStep 180953 = 135715) B135715
theorem B181067 : Blo 119786 181067 := bstep (se 1 (by rfl) ⟨135800, by rfl⟩ : syracuseStep 181067 = 271601) B271601
theorem B181079 : Blo 119786 181079 := bstep (se 1 (by rfl) ⟨135809, by rfl⟩ : syracuseStep 181079 = 271619) B271619
theorem B181145 : Blo 119786 181145 := bstep (se 2 (by rfl) ⟨67929, by rfl⟩ : syracuseStep 181145 = 135859) B135859
theorem B410561 : Blo 119786 410561 := bstep (se 2 (by rfl) ⟨153960, by rfl⟩ : syracuseStep 410561 = 307921) B307921
theorem B181259 : Blo 119786 181259 := bstep (se 1 (by rfl) ⟨135944, by rfl⟩ : syracuseStep 181259 = 271889) B271889
theorem B181271 : Blo 119786 181271 := bstep (se 1 (by rfl) ⟨135953, by rfl⟩ : syracuseStep 181271 = 271907) B271907
theorem B181337 : Blo 119786 181337 := bstep (se 2 (by rfl) ⟨68001, by rfl⟩ : syracuseStep 181337 = 136003) B136003
theorem B935063 : Blo 119786 935063 := bstep (se 1 (by rfl) ⟨701297, by rfl⟩ : syracuseStep 935063 = 1402595) B1402595
theorem B181451 : Blo 119786 181451 := bstep (se 1 (by rfl) ⟨136088, by rfl⟩ : syracuseStep 181451 = 272177) B272177
theorem B181463 : Blo 119786 181463 := bstep (se 1 (by rfl) ⟨136097, by rfl⟩ : syracuseStep 181463 = 272195) B272195
theorem B312599 : Blo 119786 312599 := bstep (se 1 (by rfl) ⟨234449, by rfl⟩ : syracuseStep 312599 = 468899) B468899
theorem B181529 : Blo 119786 181529 := bstep (se 2 (by rfl) ⟨68073, by rfl⟩ : syracuseStep 181529 = 136147) B136147
theorem B1361197 : Blo 119786 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B181643 : Blo 119786 181643 := bstep (se 1 (by rfl) ⟨136232, by rfl⟩ : syracuseStep 181643 = 272465) B272465
theorem B181655 : Blo 119786 181655 := bstep (se 1 (by rfl) ⟨136241, by rfl⟩ : syracuseStep 181655 = 272483) B272483
theorem B181721 : Blo 119786 181721 := bstep (se 2 (by rfl) ⟨68145, by rfl⟩ : syracuseStep 181721 = 136291) B136291
theorem B411101 : Blo 119786 411101 := bstep (se 3 (by rfl) ⟨77081, by rfl⟩ : syracuseStep 411101 = 154163) B154163
theorem B247297 : Blo 119786 247297 := bstep (se 2 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 247297 = 185473) B185473
theorem B181835 : Blo 119786 181835 := bstep (se 1 (by rfl) ⟨136376, by rfl⟩ : syracuseStep 181835 = 272753) B272753
theorem B181847 : Blo 119786 181847 := bstep (se 1 (by rfl) ⟨136385, by rfl⟩ : syracuseStep 181847 = 272771) B272771
theorem B181913 : Blo 119786 181913 := bstep (se 2 (by rfl) ⟨68217, by rfl⟩ : syracuseStep 181913 = 136435) B136435
theorem B182027 : Blo 119786 182027 := bstep (se 1 (by rfl) ⟨136520, by rfl⟩ : syracuseStep 182027 = 273041) B273041
theorem B182039 : Blo 119786 182039 := bstep (se 1 (by rfl) ⟨136529, by rfl⟩ : syracuseStep 182039 = 273059) B273059
theorem B182105 : Blo 119786 182105 := bstep (se 2 (by rfl) ⟨68289, by rfl⟩ : syracuseStep 182105 = 136579) B136579
theorem B313267 : Blo 119786 313267 := bstep (se 1 (by rfl) ⟨234950, by rfl⟩ : syracuseStep 313267 = 469901) B469901
theorem B182219 : Blo 119786 182219 := bstep (se 1 (by rfl) ⟨136664, by rfl⟩ : syracuseStep 182219 = 273329) B273329
theorem B182231 : Blo 119786 182231 := bstep (se 1 (by rfl) ⟨136673, by rfl⟩ : syracuseStep 182231 = 273347) B273347
theorem B182297 : Blo 119786 182297 := bstep (se 2 (by rfl) ⟨68361, by rfl⟩ : syracuseStep 182297 = 136723) B136723
theorem B1034315 : Blo 119786 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B182359 : Blo 119786 182359 := bstep (se 1 (by rfl) ⟨136769, by rfl⟩ : syracuseStep 182359 = 273539) B273539
theorem B739459 : Blo 119786 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B182411 : Blo 119786 182411 := bstep (se 1 (by rfl) ⟨136808, by rfl⟩ : syracuseStep 182411 = 273617) B273617
theorem B182423 : Blo 119786 182423 := bstep (se 1 (by rfl) ⟨136817, by rfl⟩ : syracuseStep 182423 = 273635) B273635
theorem B1460429 : Blo 119786 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B182489 : Blo 119786 182489 := bstep (se 2 (by rfl) ⟨68433, by rfl⟩ : syracuseStep 182489 = 136867) B136867
theorem B182603 : Blo 119786 182603 := bstep (se 1 (by rfl) ⟨136952, by rfl⟩ : syracuseStep 182603 = 273905) B273905
theorem B182615 : Blo 119786 182615 := bstep (se 1 (by rfl) ⟨136961, by rfl⟩ : syracuseStep 182615 = 273923) B273923
theorem B346457 : Blo 119786 346457 := bstep (se 2 (by rfl) ⟨129921, by rfl⟩ : syracuseStep 346457 = 259843) B259843
theorem B182681 : Blo 119786 182681 := bstep (se 2 (by rfl) ⟨68505, by rfl⟩ : syracuseStep 182681 = 137011) B137011
theorem B281075 : Blo 119786 281075 := bstep (se 1 (by rfl) ⟨210806, by rfl⟩ : syracuseStep 281075 = 421613) B421613
theorem B182795 : Blo 119786 182795 := bstep (se 1 (by rfl) ⟨137096, by rfl⟩ : syracuseStep 182795 = 274193) B274193
theorem B182807 : Blo 119786 182807 := bstep (se 1 (by rfl) ⟨137105, by rfl⟩ : syracuseStep 182807 = 274211) B274211
theorem B412235 : Blo 119786 412235 := bstep (se 1 (by rfl) ⟨309176, by rfl⟩ : syracuseStep 412235 = 618353) B618353
theorem B182873 : Blo 119786 182873 := bstep (se 2 (by rfl) ⟨68577, by rfl⟩ : syracuseStep 182873 = 137155) B137155
theorem B182987 : Blo 119786 182987 := bstep (se 1 (by rfl) ⟨137240, by rfl⟩ : syracuseStep 182987 = 274481) B274481
theorem B182999 : Blo 119786 182999 := bstep (se 1 (by rfl) ⟨137249, by rfl⟩ : syracuseStep 182999 = 274499) B274499
theorem B183065 : Blo 119786 183065 := bstep (se 2 (by rfl) ⟨68649, by rfl⟩ : syracuseStep 183065 = 137299) B137299
theorem B248651 : Blo 119786 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B412505 : Blo 119786 412505 := bstep (se 2 (by rfl) ⟨154689, by rfl⟩ : syracuseStep 412505 = 309379) B309379
theorem B445277 : Blo 119786 445277 := bstep (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) B166979
theorem B183179 : Blo 119786 183179 := bstep (se 1 (by rfl) ⟨137384, by rfl⟩ : syracuseStep 183179 = 274769) B274769
theorem B183191 : Blo 119786 183191 := bstep (se 1 (by rfl) ⟨137393, by rfl⟩ : syracuseStep 183191 = 274787) B274787
theorem B183257 : Blo 119786 183257 := bstep (se 2 (by rfl) ⟨68721, by rfl⟩ : syracuseStep 183257 = 137443) B137443
theorem B216065 : Blo 119786 216065 := bstep (se 2 (by rfl) ⟨81024, by rfl⟩ : syracuseStep 216065 = 162049) B162049
theorem B183371 : Blo 119786 183371 := bstep (se 1 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 183371 = 275057) B275057
theorem B183383 : Blo 119786 183383 := bstep (se 1 (by rfl) ⟨137537, by rfl⟩ : syracuseStep 183383 = 275075) B275075
theorem B183449 : Blo 119786 183449 := bstep (se 2 (by rfl) ⟨68793, by rfl⟩ : syracuseStep 183449 = 137587) B137587
theorem B183563 : Blo 119786 183563 := bstep (se 1 (by rfl) ⟨137672, by rfl⟩ : syracuseStep 183563 = 275345) B275345
theorem B183575 : Blo 119786 183575 := bstep (se 1 (by rfl) ⟨137681, by rfl⟩ : syracuseStep 183575 = 275363) B275363
theorem B183641 : Blo 119786 183641 := bstep (se 2 (by rfl) ⟨68865, by rfl⟩ : syracuseStep 183641 = 137731) B137731
theorem B839005 : Blo 119786 839005 := bstep (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) B314627
theorem B183755 : Blo 119786 183755 := bstep (se 1 (by rfl) ⟨137816, by rfl⟩ : syracuseStep 183755 = 275633) B275633
theorem B183767 : Blo 119786 183767 := bstep (se 1 (by rfl) ⟨137825, by rfl⟩ : syracuseStep 183767 = 275651) B275651
theorem B413207 : Blo 119786 413207 := bstep (se 1 (by rfl) ⟨309905, by rfl⟩ : syracuseStep 413207 = 619811) B619811
theorem B183833 : Blo 119786 183833 := bstep (se 2 (by rfl) ⟨68937, by rfl⟩ : syracuseStep 183833 = 137875) B137875
theorem B347723 : Blo 119786 347723 := bstep (se 1 (by rfl) ⟨260792, by rfl⟩ : syracuseStep 347723 = 521585) B521585
theorem B183947 : Blo 119786 183947 := bstep (se 1 (by rfl) ⟨137960, by rfl⟩ : syracuseStep 183947 = 275921) B275921
theorem B183959 : Blo 119786 183959 := bstep (se 1 (by rfl) ⟨137969, by rfl⟩ : syracuseStep 183959 = 275939) B275939
theorem B184025 : Blo 119786 184025 := bstep (se 2 (by rfl) ⟨69009, by rfl⟩ : syracuseStep 184025 = 138019) B138019
theorem B249601 : Blo 119786 249601 := bstep (se 2 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 249601 = 187201) B187201
theorem B184139 : Blo 119786 184139 := bstep (se 1 (by rfl) ⟨138104, by rfl⟩ : syracuseStep 184139 = 276209) B276209
theorem B184151 : Blo 119786 184151 := bstep (se 1 (by rfl) ⟨138113, by rfl⟩ : syracuseStep 184151 = 276227) B276227
theorem B511895 : Blo 119786 511895 := bstep (se 1 (by rfl) ⟨383921, by rfl⟩ : syracuseStep 511895 = 767843) B767843
theorem B184217 : Blo 119786 184217 := bstep (se 2 (by rfl) ⟨69081, by rfl⟩ : syracuseStep 184217 = 138163) B138163
theorem B577459 : Blo 119786 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B184331 : Blo 119786 184331 := bstep (se 1 (by rfl) ⟨138248, by rfl⟩ : syracuseStep 184331 = 276497) B276497
theorem B184343 : Blo 119786 184343 := bstep (se 1 (by rfl) ⟨138257, by rfl⟩ : syracuseStep 184343 = 276515) B276515
theorem B413747 : Blo 119786 413747 := bstep (se 1 (by rfl) ⟨310310, by rfl⟩ : syracuseStep 413747 = 620621) B620621
theorem B151627 : Blo 119786 151627 := bstep (se 1 (by rfl) ⟨113720, by rfl⟩ : syracuseStep 151627 = 227441) B227441
theorem B184409 : Blo 119786 184409 := bstep (se 2 (by rfl) ⟨69153, by rfl⟩ : syracuseStep 184409 = 138307) B138307
theorem B512203 : Blo 119786 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B184523 : Blo 119786 184523 := bstep (se 1 (by rfl) ⟨138392, by rfl⟩ : syracuseStep 184523 = 276785) B276785
theorem B184535 : Blo 119786 184535 := bstep (se 1 (by rfl) ⟨138401, by rfl⟩ : syracuseStep 184535 = 276803) B276803
theorem B610577 : Blo 119786 610577 := bstep (se 2 (by rfl) ⟨228966, by rfl⟩ : syracuseStep 610577 = 457933) B457933
theorem B184601 : Blo 119786 184601 := bstep (se 2 (by rfl) ⟨69225, by rfl⟩ : syracuseStep 184601 = 138451) B138451
theorem B414017 : Blo 119786 414017 := bstep (se 2 (by rfl) ⟨155256, by rfl⟩ : syracuseStep 414017 = 310513) B310513
theorem B151895 : Blo 119786 151895 := bstep (se 1 (by rfl) ⟨113921, by rfl⟩ : syracuseStep 151895 = 227843) B227843
theorem B184715 : Blo 119786 184715 := bstep (se 1 (by rfl) ⟨138536, by rfl⟩ : syracuseStep 184715 = 277073) B277073
theorem B184727 : Blo 119786 184727 := bstep (se 1 (by rfl) ⟨138545, by rfl⟩ : syracuseStep 184727 = 277091) B277091
theorem B610739 : Blo 119786 610739 := bstep (se 1 (by rfl) ⟨458054, by rfl⟩ : syracuseStep 610739 = 916109) B916109
theorem B184793 : Blo 119786 184793 := bstep (se 2 (by rfl) ⟨69297, by rfl⟩ : syracuseStep 184793 = 138595) B138595
theorem B512477 : Blo 119786 512477 := bstep (se 3 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 512477 = 192179) B192179
theorem B184907 : Blo 119786 184907 := bstep (se 1 (by rfl) ⟨138680, by rfl⟩ : syracuseStep 184907 = 277361) B277361
theorem B217687 : Blo 119786 217687 := bstep (se 1 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 217687 = 326531) B326531
theorem B184919 : Blo 119786 184919 := bstep (se 1 (by rfl) ⟨138689, by rfl⟩ : syracuseStep 184919 = 277379) B277379
theorem B184985 : Blo 119786 184985 := bstep (se 2 (by rfl) ⟨69369, by rfl⟩ : syracuseStep 184985 = 138739) B138739
theorem B742067 : Blo 119786 742067 := bstep (se 1 (by rfl) ⟨556550, by rfl⟩ : syracuseStep 742067 = 1113101) B1113101
theorem B185099 : Blo 119786 185099 := bstep (se 1 (by rfl) ⟨138824, by rfl⟩ : syracuseStep 185099 = 277649) B277649
theorem B185111 : Blo 119786 185111 := bstep (se 1 (by rfl) ⟨138833, by rfl⟩ : syracuseStep 185111 = 277667) B277667
theorem B873281 : Blo 119786 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B185177 : Blo 119786 185177 := bstep (se 2 (by rfl) ⟨69441, by rfl⟩ : syracuseStep 185177 = 138883) B138883
theorem B414557 : Blo 119786 414557 := bstep (se 3 (by rfl) ⟨77729, by rfl⟩ : syracuseStep 414557 = 155459) B155459
theorem B185291 : Blo 119786 185291 := bstep (se 1 (by rfl) ⟨138968, by rfl⟩ : syracuseStep 185291 = 277937) B277937
theorem B185303 : Blo 119786 185303 := bstep (se 1 (by rfl) ⟨138977, by rfl⟩ : syracuseStep 185303 = 277955) B277955
theorem B119787 : Blo 119786 119787 := bstep (se 1 (by rfl) ⟨89840, by rfl⟩ : syracuseStep 119787 = 179681) B179681
theorem B119799 : Blo 119786 119799 := bstep (se 1 (by rfl) ⟨89849, by rfl⟩ : syracuseStep 119799 = 179699) B179699
theorem B119819 : Blo 119786 119819 := bstep (se 1 (by rfl) ⟨89864, by rfl⟩ : syracuseStep 119819 = 179729) B179729
theorem B119831 : Blo 119786 119831 := bstep (se 1 (by rfl) ⟨89873, by rfl⟩ : syracuseStep 119831 = 179747) B179747
theorem B152599 : Blo 119786 152599 := bstep (se 1 (by rfl) ⟨114449, by rfl⟩ : syracuseStep 152599 = 228899) B228899
theorem B185369 : Blo 119786 185369 := bstep (se 2 (by rfl) ⟨69513, by rfl⟩ : syracuseStep 185369 = 139027) B139027
theorem B119851 : Blo 119786 119851 := bstep (se 1 (by rfl) ⟨89888, by rfl⟩ : syracuseStep 119851 = 179777) B179777
theorem B250931 : Blo 119786 250931 := bstep (se 1 (by rfl) ⟨188198, by rfl⟩ : syracuseStep 250931 = 376397) B376397
theorem B119863 : Blo 119786 119863 := bstep (se 1 (by rfl) ⟨89897, by rfl⟩ : syracuseStep 119863 = 179795) B179795
theorem B119883 : Blo 119786 119883 := bstep (se 1 (by rfl) ⟨89912, by rfl⟩ : syracuseStep 119883 = 179825) B179825
theorem B119895 : Blo 119786 119895 := bstep (se 1 (by rfl) ⟨89921, by rfl⟩ : syracuseStep 119895 = 179843) B179843
theorem B119915 : Blo 119786 119915 := bstep (se 1 (by rfl) ⟨89936, by rfl⟩ : syracuseStep 119915 = 179873) B179873
theorem B119927 : Blo 119786 119927 := bstep (se 1 (by rfl) ⟨89945, by rfl⟩ : syracuseStep 119927 = 179891) B179891
theorem B119947 : Blo 119786 119947 := bstep (se 1 (by rfl) ⟨89960, by rfl⟩ : syracuseStep 119947 = 179921) B179921
theorem B185483 : Blo 119786 185483 := bstep (se 1 (by rfl) ⟨139112, by rfl⟩ : syracuseStep 185483 = 278225) B278225
theorem B119959 : Blo 119786 119959 := bstep (se 1 (by rfl) ⟨89969, by rfl⟩ : syracuseStep 119959 = 179939) B179939
theorem B185495 : Blo 119786 185495 := bstep (se 1 (by rfl) ⟨139121, by rfl⟩ : syracuseStep 185495 = 278243) B278243
theorem B119979 : Blo 119786 119979 := bstep (se 1 (by rfl) ⟨89984, by rfl⟩ : syracuseStep 119979 = 179969) B179969
theorem B119991 : Blo 119786 119991 := bstep (se 1 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 119991 = 179987) B179987
theorem B120011 : Blo 119786 120011 := bstep (se 1 (by rfl) ⟨90008, by rfl⟩ : syracuseStep 120011 = 180017) B180017
theorem B120023 : Blo 119786 120023 := bstep (se 1 (by rfl) ⟨90017, by rfl⟩ : syracuseStep 120023 = 180035) B180035
theorem B185561 : Blo 119786 185561 := bstep (se 2 (by rfl) ⟨69585, by rfl⟩ : syracuseStep 185561 = 139171) B139171
theorem B120043 : Blo 119786 120043 := bstep (se 1 (by rfl) ⟨90032, by rfl⟩ : syracuseStep 120043 = 180065) B180065
theorem B120055 : Blo 119786 120055 := bstep (se 1 (by rfl) ⟨90041, by rfl⟩ : syracuseStep 120055 = 180083) B180083
theorem B5002501 : Blo 119786 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B120075 : Blo 119786 120075 := bstep (se 1 (by rfl) ⟨90056, by rfl⟩ : syracuseStep 120075 = 180113) B180113
theorem B120087 : Blo 119786 120087 := bstep (se 1 (by rfl) ⟨90065, by rfl⟩ : syracuseStep 120087 = 180131) B180131
theorem B218393 : Blo 119786 218393 := bstep (se 2 (by rfl) ⟨81897, by rfl⟩ : syracuseStep 218393 = 163795) B163795
theorem B120107 : Blo 119786 120107 := bstep (se 1 (by rfl) ⟨90080, by rfl⟩ : syracuseStep 120107 = 180161) B180161
theorem B120119 : Blo 119786 120119 := bstep (se 1 (by rfl) ⟨90089, by rfl⟩ : syracuseStep 120119 = 180179) B180179
theorem B120139 : Blo 119786 120139 := bstep (se 1 (by rfl) ⟨90104, by rfl⟩ : syracuseStep 120139 = 180209) B180209
theorem B185675 : Blo 119786 185675 := bstep (se 1 (by rfl) ⟨139256, by rfl⟩ : syracuseStep 185675 = 278513) B278513
theorem B120151 : Blo 119786 120151 := bstep (se 1 (by rfl) ⟨90113, by rfl⟩ : syracuseStep 120151 = 180227) B180227
theorem B120171 : Blo 119786 120171 := bstep (se 1 (by rfl) ⟨90128, by rfl⟩ : syracuseStep 120171 = 180257) B180257
theorem B120183 : Blo 119786 120183 := bstep (se 1 (by rfl) ⟨90137, by rfl⟩ : syracuseStep 120183 = 180275) B180275
theorem B120203 : Blo 119786 120203 := bstep (se 1 (by rfl) ⟨90152, by rfl⟩ : syracuseStep 120203 = 180305) B180305
theorem B120215 : Blo 119786 120215 := bstep (se 1 (by rfl) ⟨90161, by rfl⟩ : syracuseStep 120215 = 180323) B180323
theorem B710039 : Blo 119786 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B120235 : Blo 119786 120235 := bstep (se 1 (by rfl) ⟨90176, by rfl⟩ : syracuseStep 120235 = 180353) B180353
theorem B120247 : Blo 119786 120247 := bstep (se 1 (by rfl) ⟨90185, by rfl⟩ : syracuseStep 120247 = 180371) B180371
theorem B120267 : Blo 119786 120267 := bstep (se 1 (by rfl) ⟨90200, by rfl⟩ : syracuseStep 120267 = 180401) B180401
theorem B120279 : Blo 119786 120279 := bstep (se 1 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 120279 = 180419) B180419
theorem B120299 : Blo 119786 120299 := bstep (se 1 (by rfl) ⟨90224, by rfl⟩ : syracuseStep 120299 = 180449) B180449
theorem B120311 : Blo 119786 120311 := bstep (se 1 (by rfl) ⟨90233, by rfl⟩ : syracuseStep 120311 = 180467) B180467
theorem B120331 : Blo 119786 120331 := bstep (se 1 (by rfl) ⟨90248, by rfl⟩ : syracuseStep 120331 = 180497) B180497
theorem B120343 : Blo 119786 120343 := bstep (se 1 (by rfl) ⟨90257, by rfl⟩ : syracuseStep 120343 = 180515) B180515
theorem B120363 : Blo 119786 120363 := bstep (se 1 (by rfl) ⟨90272, by rfl⟩ : syracuseStep 120363 = 180545) B180545
theorem B448051 : Blo 119786 448051 := bstep (se 1 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 448051 = 672077) B672077
theorem B120375 : Blo 119786 120375 := bstep (se 1 (by rfl) ⟨90281, by rfl⟩ : syracuseStep 120375 = 180563) B180563
theorem B120395 : Blo 119786 120395 := bstep (se 1 (by rfl) ⟨90296, by rfl⟩ : syracuseStep 120395 = 180593) B180593
theorem B120407 : Blo 119786 120407 := bstep (se 1 (by rfl) ⟨90305, by rfl⟩ : syracuseStep 120407 = 180611) B180611
theorem B120427 : Blo 119786 120427 := bstep (se 1 (by rfl) ⟨90320, by rfl⟩ : syracuseStep 120427 = 180641) B180641
theorem B120439 : Blo 119786 120439 := bstep (se 1 (by rfl) ⟨90329, by rfl⟩ : syracuseStep 120439 = 180659) B180659
theorem B120459 : Blo 119786 120459 := bstep (se 1 (by rfl) ⟨90344, by rfl⟩ : syracuseStep 120459 = 180689) B180689
theorem B120471 : Blo 119786 120471 := bstep (se 1 (by rfl) ⟨90353, by rfl⟩ : syracuseStep 120471 = 180707) B180707
theorem B120491 : Blo 119786 120491 := bstep (se 1 (by rfl) ⟨90368, by rfl⟩ : syracuseStep 120491 = 180737) B180737
theorem B218803 : Blo 119786 218803 := bstep (se 1 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 218803 = 328205) B328205
theorem B120503 : Blo 119786 120503 := bstep (se 1 (by rfl) ⟨90377, by rfl⟩ : syracuseStep 120503 = 180755) B180755
theorem B120523 : Blo 119786 120523 := bstep (se 1 (by rfl) ⟨90392, by rfl⟩ : syracuseStep 120523 = 180785) B180785
theorem B120535 : Blo 119786 120535 := bstep (se 1 (by rfl) ⟨90401, by rfl⟩ : syracuseStep 120535 = 180803) B180803
theorem B120555 : Blo 119786 120555 := bstep (se 1 (by rfl) ⟨90416, by rfl⟩ : syracuseStep 120555 = 180833) B180833
theorem B120567 : Blo 119786 120567 := bstep (se 1 (by rfl) ⟨90425, by rfl⟩ : syracuseStep 120567 = 180851) B180851
theorem B120587 : Blo 119786 120587 := bstep (se 1 (by rfl) ⟨90440, by rfl⟩ : syracuseStep 120587 = 180881) B180881
theorem B513809 : Blo 119786 513809 := bstep (se 2 (by rfl) ⟨192678, by rfl⟩ : syracuseStep 513809 = 385357) B385357
theorem B120599 : Blo 119786 120599 := bstep (se 1 (by rfl) ⟨90449, by rfl⟩ : syracuseStep 120599 = 180899) B180899
theorem B120619 : Blo 119786 120619 := bstep (se 1 (by rfl) ⟨90464, by rfl⟩ : syracuseStep 120619 = 180929) B180929
theorem B120631 : Blo 119786 120631 := bstep (se 1 (by rfl) ⟨90473, by rfl⟩ : syracuseStep 120631 = 180947) B180947
theorem B317249 : Blo 119786 317249 := bstep (se 2 (by rfl) ⟨118968, by rfl⟩ : syracuseStep 317249 = 237937) B237937
theorem B120651 : Blo 119786 120651 := bstep (se 1 (by rfl) ⟨90488, by rfl⟩ : syracuseStep 120651 = 180977) B180977
theorem B120663 : Blo 119786 120663 := bstep (se 1 (by rfl) ⟨90497, by rfl⟩ : syracuseStep 120663 = 180995) B180995
theorem B120683 : Blo 119786 120683 := bstep (se 1 (by rfl) ⟨90512, by rfl⟩ : syracuseStep 120683 = 181025) B181025
theorem B120695 : Blo 119786 120695 := bstep (se 1 (by rfl) ⟨90521, by rfl⟩ : syracuseStep 120695 = 181043) B181043
theorem B120715 : Blo 119786 120715 := bstep (se 1 (by rfl) ⟨90536, by rfl⟩ : syracuseStep 120715 = 181073) B181073
theorem B186251 : Blo 119786 186251 := bstep (se 1 (by rfl) ⟨139688, by rfl⟩ : syracuseStep 186251 = 279377) B279377
theorem B120727 : Blo 119786 120727 := bstep (se 1 (by rfl) ⟨90545, by rfl⟩ : syracuseStep 120727 = 181091) B181091
theorem B120747 : Blo 119786 120747 := bstep (se 1 (by rfl) ⟨90560, by rfl⟩ : syracuseStep 120747 = 181121) B181121
theorem B120759 : Blo 119786 120759 := bstep (se 1 (by rfl) ⟨90569, by rfl⟩ : syracuseStep 120759 = 181139) B181139
theorem B120779 : Blo 119786 120779 := bstep (se 1 (by rfl) ⟨90584, by rfl⟩ : syracuseStep 120779 = 181169) B181169
theorem B415691 : Blo 119786 415691 := bstep (se 1 (by rfl) ⟨311768, by rfl⟩ : syracuseStep 415691 = 623537) B623537
theorem B120791 : Blo 119786 120791 := bstep (se 1 (by rfl) ⟨90593, by rfl⟩ : syracuseStep 120791 = 181187) B181187
theorem B120811 : Blo 119786 120811 := bstep (se 1 (by rfl) ⟨90608, by rfl⟩ : syracuseStep 120811 = 181217) B181217
theorem B120823 : Blo 119786 120823 := bstep (se 1 (by rfl) ⟨90617, by rfl⟩ : syracuseStep 120823 = 181235) B181235
theorem B120843 : Blo 119786 120843 := bstep (se 1 (by rfl) ⟨90632, by rfl⟩ : syracuseStep 120843 = 181265) B181265
theorem B120855 : Blo 119786 120855 := bstep (se 1 (by rfl) ⟨90641, by rfl⟩ : syracuseStep 120855 = 181283) B181283
theorem B120875 : Blo 119786 120875 := bstep (se 1 (by rfl) ⟨90656, by rfl⟩ : syracuseStep 120875 = 181313) B181313
theorem B120887 : Blo 119786 120887 := bstep (se 1 (by rfl) ⟨90665, by rfl⟩ : syracuseStep 120887 = 181331) B181331
theorem B120907 : Blo 119786 120907 := bstep (se 1 (by rfl) ⟨90680, by rfl⟩ : syracuseStep 120907 = 181361) B181361
theorem B120919 : Blo 119786 120919 := bstep (se 1 (by rfl) ⟨90689, by rfl⟩ : syracuseStep 120919 = 181379) B181379
theorem B120939 : Blo 119786 120939 := bstep (se 1 (by rfl) ⟨90704, by rfl⟩ : syracuseStep 120939 = 181409) B181409
theorem B120951 : Blo 119786 120951 := bstep (se 1 (by rfl) ⟨90713, by rfl⟩ : syracuseStep 120951 = 181427) B181427
theorem B120971 : Blo 119786 120971 := bstep (se 1 (by rfl) ⟨90728, by rfl⟩ : syracuseStep 120971 = 181457) B181457
theorem B120983 : Blo 119786 120983 := bstep (se 1 (by rfl) ⟨90737, by rfl⟩ : syracuseStep 120983 = 181475) B181475
theorem B121003 : Blo 119786 121003 := bstep (se 1 (by rfl) ⟨90752, by rfl⟩ : syracuseStep 121003 = 181505) B181505
theorem B121015 : Blo 119786 121015 := bstep (se 1 (by rfl) ⟨90761, by rfl⟩ : syracuseStep 121015 = 181523) B181523
theorem B121035 : Blo 119786 121035 := bstep (se 1 (by rfl) ⟨90776, by rfl⟩ : syracuseStep 121035 = 181553) B181553
theorem B121047 : Blo 119786 121047 := bstep (se 1 (by rfl) ⟨90785, by rfl⟩ : syracuseStep 121047 = 181571) B181571
theorem B415961 : Blo 119786 415961 := bstep (se 2 (by rfl) ⟨155985, by rfl⟩ : syracuseStep 415961 = 311971) B311971
theorem B121067 : Blo 119786 121067 := bstep (se 1 (by rfl) ⟨90800, by rfl⟩ : syracuseStep 121067 = 181601) B181601
theorem B121079 : Blo 119786 121079 := bstep (se 1 (by rfl) ⟨90809, by rfl⟩ : syracuseStep 121079 = 181619) B181619
theorem B121099 : Blo 119786 121099 := bstep (se 1 (by rfl) ⟨90824, by rfl⟩ : syracuseStep 121099 = 181649) B181649
theorem B121111 : Blo 119786 121111 := bstep (se 1 (by rfl) ⟨90833, by rfl⟩ : syracuseStep 121111 = 181667) B181667
theorem B121131 : Blo 119786 121131 := bstep (se 1 (by rfl) ⟨90848, by rfl⟩ : syracuseStep 121131 = 181697) B181697
theorem B121143 : Blo 119786 121143 := bstep (se 1 (by rfl) ⟨90857, by rfl⟩ : syracuseStep 121143 = 181715) B181715
theorem B612683 : Blo 119786 612683 := bstep (se 1 (by rfl) ⟨459512, by rfl⟩ : syracuseStep 612683 = 919025) B919025
theorem B121163 : Blo 119786 121163 := bstep (se 1 (by rfl) ⟨90872, by rfl⟩ : syracuseStep 121163 = 181745) B181745
theorem B121175 : Blo 119786 121175 := bstep (se 1 (by rfl) ⟨90881, by rfl⟩ : syracuseStep 121175 = 181763) B181763
theorem B121195 : Blo 119786 121195 := bstep (se 1 (by rfl) ⟨90896, by rfl⟩ : syracuseStep 121195 = 181793) B181793
theorem B121207 : Blo 119786 121207 := bstep (se 1 (by rfl) ⟨90905, by rfl⟩ : syracuseStep 121207 = 181811) B181811
theorem B121227 : Blo 119786 121227 := bstep (se 1 (by rfl) ⟨90920, by rfl⟩ : syracuseStep 121227 = 181841) B181841
theorem B121239 : Blo 119786 121239 := bstep (se 1 (by rfl) ⟨90929, by rfl⟩ : syracuseStep 121239 = 181859) B181859
theorem B121259 : Blo 119786 121259 := bstep (se 1 (by rfl) ⟨90944, by rfl⟩ : syracuseStep 121259 = 181889) B181889
theorem B121271 : Blo 119786 121271 := bstep (se 1 (by rfl) ⟨90953, by rfl⟩ : syracuseStep 121271 = 181907) B181907
theorem B121291 : Blo 119786 121291 := bstep (se 1 (by rfl) ⟨90968, by rfl⟩ : syracuseStep 121291 = 181937) B181937
theorem B121303 : Blo 119786 121303 := bstep (se 1 (by rfl) ⟨90977, by rfl⟩ : syracuseStep 121303 = 181955) B181955
theorem B121323 : Blo 119786 121323 := bstep (se 1 (by rfl) ⟨90992, by rfl⟩ : syracuseStep 121323 = 181985) B181985
theorem B121335 : Blo 119786 121335 := bstep (se 1 (by rfl) ⟨91001, by rfl⟩ : syracuseStep 121335 = 182003) B182003
theorem B121355 : Blo 119786 121355 := bstep (se 1 (by rfl) ⟨91016, by rfl⟩ : syracuseStep 121355 = 182033) B182033
theorem B121367 : Blo 119786 121367 := bstep (se 1 (by rfl) ⟨91025, by rfl⟩ : syracuseStep 121367 = 182051) B182051
theorem B121387 : Blo 119786 121387 := bstep (se 1 (by rfl) ⟨91040, by rfl⟩ : syracuseStep 121387 = 182081) B182081
theorem B121399 : Blo 119786 121399 := bstep (se 1 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 121399 = 182099) B182099
theorem B121419 : Blo 119786 121419 := bstep (se 1 (by rfl) ⟨91064, by rfl⟩ : syracuseStep 121419 = 182129) B182129
theorem B121431 : Blo 119786 121431 := bstep (se 1 (by rfl) ⟨91073, by rfl⟩ : syracuseStep 121431 = 182147) B182147
theorem B121451 : Blo 119786 121451 := bstep (se 1 (by rfl) ⟨91088, by rfl⟩ : syracuseStep 121451 = 182177) B182177
theorem B121463 : Blo 119786 121463 := bstep (se 1 (by rfl) ⟨91097, by rfl⟩ : syracuseStep 121463 = 182195) B182195
theorem B121483 : Blo 119786 121483 := bstep (se 1 (by rfl) ⟨91112, by rfl⟩ : syracuseStep 121483 = 182225) B182225
theorem B121495 : Blo 119786 121495 := bstep (se 1 (by rfl) ⟨91121, by rfl⟩ : syracuseStep 121495 = 182243) B182243
theorem B187031 : Blo 119786 187031 := bstep (se 1 (by rfl) ⟨140273, by rfl⟩ : syracuseStep 187031 = 280547) B280547
theorem B121515 : Blo 119786 121515 := bstep (se 1 (by rfl) ⟨91136, by rfl⟩ : syracuseStep 121515 = 182273) B182273
theorem B121527 : Blo 119786 121527 := bstep (se 1 (by rfl) ⟨91145, by rfl⟩ : syracuseStep 121527 = 182291) B182291
theorem B121547 : Blo 119786 121547 := bstep (se 1 (by rfl) ⟨91160, by rfl⟩ : syracuseStep 121547 = 182321) B182321
theorem B154315 : Blo 119786 154315 := bstep (se 1 (by rfl) ⟨115736, by rfl⟩ : syracuseStep 154315 = 231473) B231473
theorem B121559 : Blo 119786 121559 := bstep (se 1 (by rfl) ⟨91169, by rfl⟩ : syracuseStep 121559 = 182339) B182339
theorem B121579 : Blo 119786 121579 := bstep (se 1 (by rfl) ⟨91184, by rfl⟩ : syracuseStep 121579 = 182369) B182369
theorem B121591 : Blo 119786 121591 := bstep (se 1 (by rfl) ⟨91193, by rfl⟩ : syracuseStep 121591 = 182387) B182387
theorem B121611 : Blo 119786 121611 := bstep (se 1 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 121611 = 182417) B182417
theorem B121623 : Blo 119786 121623 := bstep (se 1 (by rfl) ⟨91217, by rfl⟩ : syracuseStep 121623 = 182435) B182435
theorem B154391 : Blo 119786 154391 := bstep (se 1 (by rfl) ⟨115793, by rfl⟩ : syracuseStep 154391 = 231587) B231587
theorem B121643 : Blo 119786 121643 := bstep (se 1 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 121643 = 182465) B182465
theorem B121655 : Blo 119786 121655 := bstep (se 1 (by rfl) ⟨91241, by rfl⟩ : syracuseStep 121655 = 182483) B182483
theorem B121675 : Blo 119786 121675 := bstep (se 1 (by rfl) ⟨91256, by rfl⟩ : syracuseStep 121675 = 182513) B182513
theorem B121687 : Blo 119786 121687 := bstep (se 1 (by rfl) ⟨91265, by rfl⟩ : syracuseStep 121687 = 182531) B182531
theorem B121707 : Blo 119786 121707 := bstep (se 1 (by rfl) ⟨91280, by rfl⟩ : syracuseStep 121707 = 182561) B182561
theorem B121719 : Blo 119786 121719 := bstep (se 1 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 121719 = 182579) B182579
theorem B121739 : Blo 119786 121739 := bstep (se 1 (by rfl) ⟨91304, by rfl⟩ : syracuseStep 121739 = 182609) B182609
theorem B121751 : Blo 119786 121751 := bstep (se 1 (by rfl) ⟨91313, by rfl⟩ : syracuseStep 121751 = 182627) B182627
theorem B416663 : Blo 119786 416663 := bstep (se 1 (by rfl) ⟨312497, by rfl⟩ : syracuseStep 416663 = 624995) B624995
theorem B121771 : Blo 119786 121771 := bstep (se 1 (by rfl) ⟨91328, by rfl⟩ : syracuseStep 121771 = 182657) B182657
theorem B1563569 : Blo 119786 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B121783 : Blo 119786 121783 := bstep (se 1 (by rfl) ⟨91337, by rfl⟩ : syracuseStep 121783 = 182675) B182675
theorem B121803 : Blo 119786 121803 := bstep (se 1 (by rfl) ⟨91352, by rfl⟩ : syracuseStep 121803 = 182705) B182705
theorem B121815 : Blo 119786 121815 := bstep (se 1 (by rfl) ⟨91361, by rfl⟩ : syracuseStep 121815 = 182723) B182723
theorem B449497 : Blo 119786 449497 := bstep (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) B337123
theorem B121835 : Blo 119786 121835 := bstep (se 1 (by rfl) ⟨91376, by rfl⟩ : syracuseStep 121835 = 182753) B182753
theorem B121847 : Blo 119786 121847 := bstep (se 1 (by rfl) ⟨91385, by rfl⟩ : syracuseStep 121847 = 182771) B182771
theorem B121867 : Blo 119786 121867 := bstep (se 1 (by rfl) ⟨91400, by rfl⟩ : syracuseStep 121867 = 182801) B182801
theorem B121879 : Blo 119786 121879 := bstep (se 1 (by rfl) ⟨91409, by rfl⟩ : syracuseStep 121879 = 182819) B182819
theorem B121899 : Blo 119786 121899 := bstep (se 1 (by rfl) ⟨91424, by rfl⟩ : syracuseStep 121899 = 182849) B182849
theorem B121911 : Blo 119786 121911 := bstep (se 1 (by rfl) ⟨91433, by rfl⟩ : syracuseStep 121911 = 182867) B182867
theorem B121931 : Blo 119786 121931 := bstep (se 1 (by rfl) ⟨91448, by rfl⟩ : syracuseStep 121931 = 182897) B182897
theorem B121943 : Blo 119786 121943 := bstep (se 1 (by rfl) ⟨91457, by rfl⟩ : syracuseStep 121943 = 182915) B182915
theorem B121963 : Blo 119786 121963 := bstep (se 1 (by rfl) ⟨91472, by rfl⟩ : syracuseStep 121963 = 182945) B182945
theorem B121975 : Blo 119786 121975 := bstep (se 1 (by rfl) ⟨91481, by rfl⟩ : syracuseStep 121975 = 182963) B182963
theorem B121995 : Blo 119786 121995 := bstep (se 1 (by rfl) ⟨91496, by rfl⟩ : syracuseStep 121995 = 182993) B182993
theorem B122007 : Blo 119786 122007 := bstep (se 1 (by rfl) ⟨91505, by rfl⟩ : syracuseStep 122007 = 183011) B183011
theorem B122027 : Blo 119786 122027 := bstep (se 1 (by rfl) ⟨91520, by rfl⟩ : syracuseStep 122027 = 183041) B183041
theorem B1006769 : Blo 119786 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B122039 : Blo 119786 122039 := bstep (se 1 (by rfl) ⟨91529, by rfl⟩ : syracuseStep 122039 = 183059) B183059
theorem B122059 : Blo 119786 122059 := bstep (se 1 (by rfl) ⟨91544, by rfl⟩ : syracuseStep 122059 = 183089) B183089
theorem B122071 : Blo 119786 122071 := bstep (se 1 (by rfl) ⟨91553, by rfl⟩ : syracuseStep 122071 = 183107) B183107
theorem B122091 : Blo 119786 122091 := bstep (se 1 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 122091 = 183137) B183137
theorem B122103 : Blo 119786 122103 := bstep (se 1 (by rfl) ⟨91577, by rfl⟩ : syracuseStep 122103 = 183155) B183155
theorem B122123 : Blo 119786 122123 := bstep (se 1 (by rfl) ⟨91592, by rfl⟩ : syracuseStep 122123 = 183185) B183185
theorem B122135 : Blo 119786 122135 := bstep (se 1 (by rfl) ⟨91601, by rfl⟩ : syracuseStep 122135 = 183203) B183203
theorem B122155 : Blo 119786 122155 := bstep (se 1 (by rfl) ⟨91616, by rfl⟩ : syracuseStep 122155 = 183233) B183233
theorem B122167 : Blo 119786 122167 := bstep (se 1 (by rfl) ⟨91625, by rfl⟩ : syracuseStep 122167 = 183251) B183251
theorem B122187 : Blo 119786 122187 := bstep (se 1 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 122187 = 183281) B183281
theorem B122199 : Blo 119786 122199 := bstep (se 1 (by rfl) ⟨91649, by rfl⟩ : syracuseStep 122199 = 183299) B183299
theorem B122219 : Blo 119786 122219 := bstep (se 1 (by rfl) ⟨91664, by rfl⟩ : syracuseStep 122219 = 183329) B183329
theorem B122231 : Blo 119786 122231 := bstep (se 1 (by rfl) ⟨91673, by rfl⟩ : syracuseStep 122231 = 183347) B183347
theorem B122251 : Blo 119786 122251 := bstep (se 1 (by rfl) ⟨91688, by rfl⟩ : syracuseStep 122251 = 183377) B183377
theorem B122263 : Blo 119786 122263 := bstep (se 1 (by rfl) ⟨91697, by rfl⟩ : syracuseStep 122263 = 183395) B183395
theorem B122283 : Blo 119786 122283 := bstep (se 1 (by rfl) ⟨91712, by rfl⟩ : syracuseStep 122283 = 183425) B183425
theorem B417203 : Blo 119786 417203 := bstep (se 1 (by rfl) ⟨312902, by rfl⟩ : syracuseStep 417203 = 625805) B625805
theorem B122295 : Blo 119786 122295 := bstep (se 1 (by rfl) ⟨91721, by rfl⟩ : syracuseStep 122295 = 183443) B183443
theorem B122315 : Blo 119786 122315 := bstep (se 1 (by rfl) ⟨91736, by rfl⟩ : syracuseStep 122315 = 183473) B183473
theorem B122327 : Blo 119786 122327 := bstep (se 1 (by rfl) ⟨91745, by rfl⟩ : syracuseStep 122327 = 183491) B183491
theorem B122347 : Blo 119786 122347 := bstep (se 1 (by rfl) ⟨91760, by rfl⟩ : syracuseStep 122347 = 183521) B183521
theorem B122359 : Blo 119786 122359 := bstep (se 1 (by rfl) ⟨91769, by rfl⟩ : syracuseStep 122359 = 183539) B183539
theorem B122379 : Blo 119786 122379 := bstep (se 1 (by rfl) ⟨91784, by rfl⟩ : syracuseStep 122379 = 183569) B183569
theorem B122391 : Blo 119786 122391 := bstep (se 1 (by rfl) ⟨91793, by rfl⟩ : syracuseStep 122391 = 183587) B183587
theorem B122411 : Blo 119786 122411 := bstep (se 1 (by rfl) ⟨91808, by rfl⟩ : syracuseStep 122411 = 183617) B183617
theorem B384563 : Blo 119786 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B122423 : Blo 119786 122423 := bstep (se 1 (by rfl) ⟨91817, by rfl⟩ : syracuseStep 122423 = 183635) B183635
theorem B122443 : Blo 119786 122443 := bstep (se 1 (by rfl) ⟨91832, by rfl⟩ : syracuseStep 122443 = 183665) B183665
theorem B122455 : Blo 119786 122455 := bstep (se 1 (by rfl) ⟨91841, by rfl⟩ : syracuseStep 122455 = 183683) B183683
theorem B122475 : Blo 119786 122475 := bstep (se 1 (by rfl) ⟨91856, by rfl⟩ : syracuseStep 122475 = 183713) B183713
theorem B122487 : Blo 119786 122487 := bstep (se 1 (by rfl) ⟨91865, by rfl⟩ : syracuseStep 122487 = 183731) B183731
theorem B122507 : Blo 119786 122507 := bstep (se 1 (by rfl) ⟨91880, by rfl⟩ : syracuseStep 122507 = 183761) B183761
theorem B122519 : Blo 119786 122519 := bstep (se 1 (by rfl) ⟨91889, by rfl⟩ : syracuseStep 122519 = 183779) B183779
theorem B155287 : Blo 119786 155287 := bstep (se 1 (by rfl) ⟨116465, by rfl⟩ : syracuseStep 155287 = 232931) B232931
theorem B122539 : Blo 119786 122539 := bstep (se 1 (by rfl) ⟨91904, by rfl⟩ : syracuseStep 122539 = 183809) B183809
theorem B122551 : Blo 119786 122551 := bstep (se 1 (by rfl) ⟨91913, by rfl⟩ : syracuseStep 122551 = 183827) B183827
theorem B417473 : Blo 119786 417473 := bstep (se 2 (by rfl) ⟨156552, by rfl⟩ : syracuseStep 417473 = 313105) B313105
theorem B155339 : Blo 119786 155339 := bstep (se 1 (by rfl) ⟨116504, by rfl⟩ : syracuseStep 155339 = 233009) B233009
theorem B122571 : Blo 119786 122571 := bstep (se 1 (by rfl) ⟨91928, by rfl⟩ : syracuseStep 122571 = 183857) B183857
theorem B122583 : Blo 119786 122583 := bstep (se 1 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 122583 = 183875) B183875
theorem B122603 : Blo 119786 122603 := bstep (se 1 (by rfl) ⟨91952, by rfl⟩ : syracuseStep 122603 = 183905) B183905
theorem B122615 : Blo 119786 122615 := bstep (se 1 (by rfl) ⟨91961, by rfl⟩ : syracuseStep 122615 = 183923) B183923
theorem B122635 : Blo 119786 122635 := bstep (se 1 (by rfl) ⟨91976, by rfl⟩ : syracuseStep 122635 = 183953) B183953
theorem B122647 : Blo 119786 122647 := bstep (se 1 (by rfl) ⟨91985, by rfl⟩ : syracuseStep 122647 = 183971) B183971
theorem B122667 : Blo 119786 122667 := bstep (se 1 (by rfl) ⟨92000, by rfl⟩ : syracuseStep 122667 = 184001) B184001
theorem B122679 : Blo 119786 122679 := bstep (se 1 (by rfl) ⟨92009, by rfl⟩ : syracuseStep 122679 = 184019) B184019
theorem B122699 : Blo 119786 122699 := bstep (se 1 (by rfl) ⟨92024, by rfl⟩ : syracuseStep 122699 = 184049) B184049
theorem B122711 : Blo 119786 122711 := bstep (se 1 (by rfl) ⟨92033, by rfl⟩ : syracuseStep 122711 = 184067) B184067
theorem B122731 : Blo 119786 122731 := bstep (se 1 (by rfl) ⟨92048, by rfl⟩ : syracuseStep 122731 = 184097) B184097
theorem B122743 : Blo 119786 122743 := bstep (se 1 (by rfl) ⟨92057, by rfl⟩ : syracuseStep 122743 = 184115) B184115
theorem B122763 : Blo 119786 122763 := bstep (se 1 (by rfl) ⟨92072, by rfl⟩ : syracuseStep 122763 = 184145) B184145
theorem B122775 : Blo 119786 122775 := bstep (se 1 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 122775 = 184163) B184163
theorem B122795 : Blo 119786 122795 := bstep (se 1 (by rfl) ⟨92096, by rfl⟩ : syracuseStep 122795 = 184193) B184193
theorem B1564595 : Blo 119786 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B122807 : Blo 119786 122807 := bstep (se 1 (by rfl) ⟨92105, by rfl⟩ : syracuseStep 122807 = 184211) B184211
theorem B122827 : Blo 119786 122827 := bstep (se 1 (by rfl) ⟨92120, by rfl⟩ : syracuseStep 122827 = 184241) B184241
theorem B122839 : Blo 119786 122839 := bstep (se 1 (by rfl) ⟨92129, by rfl⟩ : syracuseStep 122839 = 184259) B184259
theorem B122859 : Blo 119786 122859 := bstep (se 1 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 122859 = 184289) B184289
theorem B122871 : Blo 119786 122871 := bstep (se 1 (by rfl) ⟨92153, by rfl⟩ : syracuseStep 122871 = 184307) B184307
theorem B122891 : Blo 119786 122891 := bstep (se 1 (by rfl) ⟨92168, by rfl⟩ : syracuseStep 122891 = 184337) B184337
theorem B122903 : Blo 119786 122903 := bstep (se 1 (by rfl) ⟨92177, by rfl⟩ : syracuseStep 122903 = 184355) B184355
theorem B122923 : Blo 119786 122923 := bstep (se 1 (by rfl) ⟨92192, by rfl⟩ : syracuseStep 122923 = 184385) B184385
theorem B122935 : Blo 119786 122935 := bstep (se 1 (by rfl) ⟨92201, by rfl⟩ : syracuseStep 122935 = 184403) B184403
theorem B614465 : Blo 119786 614465 := bstep (se 2 (by rfl) ⟨230424, by rfl⟩ : syracuseStep 614465 = 460849) B460849
theorem B122955 : Blo 119786 122955 := bstep (se 1 (by rfl) ⟨92216, by rfl⟩ : syracuseStep 122955 = 184433) B184433
theorem B122967 : Blo 119786 122967 := bstep (se 1 (by rfl) ⟨92225, by rfl⟩ : syracuseStep 122967 = 184451) B184451
theorem B122987 : Blo 119786 122987 := bstep (se 1 (by rfl) ⟨92240, by rfl⟩ : syracuseStep 122987 = 184481) B184481
theorem B122999 : Blo 119786 122999 := bstep (se 1 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 122999 = 184499) B184499
theorem B123019 : Blo 119786 123019 := bstep (se 1 (by rfl) ⟨92264, by rfl⟩ : syracuseStep 123019 = 184529) B184529
theorem B123031 : Blo 119786 123031 := bstep (se 1 (by rfl) ⟨92273, by rfl⟩ : syracuseStep 123031 = 184547) B184547
theorem B123051 : Blo 119786 123051 := bstep (se 1 (by rfl) ⟨92288, by rfl⟩ : syracuseStep 123051 = 184577) B184577
theorem B516269 : Blo 119786 516269 := bstep (se 3 (by rfl) ⟨96800, by rfl⟩ : syracuseStep 516269 = 193601) B193601
theorem B123063 : Blo 119786 123063 := bstep (se 1 (by rfl) ⟨92297, by rfl⟩ : syracuseStep 123063 = 184595) B184595
theorem B123083 : Blo 119786 123083 := bstep (se 1 (by rfl) ⟨92312, by rfl⟩ : syracuseStep 123083 = 184625) B184625
theorem B123095 : Blo 119786 123095 := bstep (se 1 (by rfl) ⟨92321, by rfl⟩ : syracuseStep 123095 = 184643) B184643
theorem B123115 : Blo 119786 123115 := bstep (se 1 (by rfl) ⟨92336, by rfl⟩ : syracuseStep 123115 = 184673) B184673
theorem B123127 : Blo 119786 123127 := bstep (se 1 (by rfl) ⟨92345, by rfl⟩ : syracuseStep 123127 = 184691) B184691
theorem B123147 : Blo 119786 123147 := bstep (se 1 (by rfl) ⟨92360, by rfl⟩ : syracuseStep 123147 = 184721) B184721
theorem B123159 : Blo 119786 123159 := bstep (se 1 (by rfl) ⟨92369, by rfl⟩ : syracuseStep 123159 = 184739) B184739
theorem B123179 : Blo 119786 123179 := bstep (se 1 (by rfl) ⟨92384, by rfl⟩ : syracuseStep 123179 = 184769) B184769
theorem B123191 : Blo 119786 123191 := bstep (se 1 (by rfl) ⟨92393, by rfl⟩ : syracuseStep 123191 = 184787) B184787
theorem B123211 : Blo 119786 123211 := bstep (se 1 (by rfl) ⟨92408, by rfl⟩ : syracuseStep 123211 = 184817) B184817
theorem B123223 : Blo 119786 123223 := bstep (se 1 (by rfl) ⟨92417, by rfl⟩ : syracuseStep 123223 = 184835) B184835
theorem B123243 : Blo 119786 123243 := bstep (se 1 (by rfl) ⟨92432, by rfl⟩ : syracuseStep 123243 = 184865) B184865
theorem B123255 : Blo 119786 123255 := bstep (se 1 (by rfl) ⟨92441, by rfl⟩ : syracuseStep 123255 = 184883) B184883
theorem B123275 : Blo 119786 123275 := bstep (se 1 (by rfl) ⟨92456, by rfl⟩ : syracuseStep 123275 = 184913) B184913
theorem B123287 : Blo 119786 123287 := bstep (se 1 (by rfl) ⟨92465, by rfl⟩ : syracuseStep 123287 = 184931) B184931
theorem B123307 : Blo 119786 123307 := bstep (se 1 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 123307 = 184961) B184961
theorem B123319 : Blo 119786 123319 := bstep (se 1 (by rfl) ⟨92489, by rfl⟩ : syracuseStep 123319 = 184979) B184979
theorem B123339 : Blo 119786 123339 := bstep (se 1 (by rfl) ⟨92504, by rfl⟩ : syracuseStep 123339 = 185009) B185009
theorem B156107 : Blo 119786 156107 := bstep (se 1 (by rfl) ⟨117080, by rfl⟩ : syracuseStep 156107 = 234161) B234161
theorem B123351 : Blo 119786 123351 := bstep (se 1 (by rfl) ⟨92513, by rfl⟩ : syracuseStep 123351 = 185027) B185027
theorem B123371 : Blo 119786 123371 := bstep (se 1 (by rfl) ⟨92528, by rfl⟩ : syracuseStep 123371 = 185057) B185057
theorem B123383 : Blo 119786 123383 := bstep (se 1 (by rfl) ⟨92537, by rfl⟩ : syracuseStep 123383 = 185075) B185075
theorem B516611 : Blo 119786 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B123403 : Blo 119786 123403 := bstep (se 1 (by rfl) ⟨92552, by rfl⟩ : syracuseStep 123403 = 185105) B185105
theorem B123415 : Blo 119786 123415 := bstep (se 1 (by rfl) ⟨92561, by rfl⟩ : syracuseStep 123415 = 185123) B185123
theorem B123435 : Blo 119786 123435 := bstep (se 1 (by rfl) ⟨92576, by rfl⟩ : syracuseStep 123435 = 185153) B185153
theorem B123447 : Blo 119786 123447 := bstep (se 1 (by rfl) ⟨92585, by rfl⟩ : syracuseStep 123447 = 185171) B185171
theorem B123467 : Blo 119786 123467 := bstep (se 1 (by rfl) ⟨92600, by rfl⟩ : syracuseStep 123467 = 185201) B185201
theorem B123479 : Blo 119786 123479 := bstep (se 1 (by rfl) ⟨92609, by rfl⟩ : syracuseStep 123479 = 185219) B185219
theorem B123499 : Blo 119786 123499 := bstep (se 1 (by rfl) ⟨92624, by rfl⟩ : syracuseStep 123499 = 185249) B185249
theorem B123511 : Blo 119786 123511 := bstep (se 1 (by rfl) ⟨92633, by rfl⟩ : syracuseStep 123511 = 185267) B185267
theorem B123531 : Blo 119786 123531 := bstep (se 1 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 123531 = 185297) B185297
theorem B123543 : Blo 119786 123543 := bstep (se 1 (by rfl) ⟨92657, by rfl⟩ : syracuseStep 123543 = 185315) B185315
theorem B123563 : Blo 119786 123563 := bstep (se 1 (by rfl) ⟨92672, by rfl⟩ : syracuseStep 123563 = 185345) B185345
theorem B123575 : Blo 119786 123575 := bstep (se 1 (by rfl) ⟨92681, by rfl⟩ : syracuseStep 123575 = 185363) B185363
theorem B123595 : Blo 119786 123595 := bstep (se 1 (by rfl) ⟨92696, by rfl⟩ : syracuseStep 123595 = 185393) B185393
theorem B123607 : Blo 119786 123607 := bstep (se 1 (by rfl) ⟨92705, by rfl⟩ : syracuseStep 123607 = 185411) B185411
theorem B123627 : Blo 119786 123627 := bstep (se 1 (by rfl) ⟨92720, by rfl⟩ : syracuseStep 123627 = 185441) B185441
theorem B123639 : Blo 119786 123639 := bstep (se 1 (by rfl) ⟨92729, by rfl⟩ : syracuseStep 123639 = 185459) B185459
theorem B123659 : Blo 119786 123659 := bstep (se 1 (by rfl) ⟨92744, by rfl⟩ : syracuseStep 123659 = 185489) B185489
theorem B123671 : Blo 119786 123671 := bstep (se 1 (by rfl) ⟨92753, by rfl⟩ : syracuseStep 123671 = 185507) B185507
theorem B123691 : Blo 119786 123691 := bstep (se 1 (by rfl) ⟨92768, by rfl⟩ : syracuseStep 123691 = 185537) B185537
theorem B123703 : Blo 119786 123703 := bstep (se 1 (by rfl) ⟨92777, by rfl⟩ : syracuseStep 123703 = 185555) B185555
theorem B123723 : Blo 119786 123723 := bstep (se 1 (by rfl) ⟨92792, by rfl⟩ : syracuseStep 123723 = 185585) B185585
theorem B123735 : Blo 119786 123735 := bstep (se 1 (by rfl) ⟨92801, by rfl⟩ : syracuseStep 123735 = 185603) B185603
theorem B320345 : Blo 119786 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B123755 : Blo 119786 123755 := bstep (se 1 (by rfl) ⟨92816, by rfl⟩ : syracuseStep 123755 = 185633) B185633
theorem B123767 : Blo 119786 123767 := bstep (se 1 (by rfl) ⟨92825, by rfl⟩ : syracuseStep 123767 = 185651) B185651
theorem B124087 : Blo 119786 124087 := bstep (se 1 (by rfl) ⟨93065, by rfl⟩ : syracuseStep 124087 = 186131) B186131
theorem B419165 : Blo 119786 419165 := bstep (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) B157187
theorem B124363 : Blo 119786 124363 := bstep (se 1 (by rfl) ⟨93272, by rfl⟩ : syracuseStep 124363 = 186545) B186545
theorem B1336907 : Blo 119786 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B616409 : Blo 119786 616409 := bstep (se 2 (by rfl) ⟨231153, by rfl⟩ : syracuseStep 616409 = 462307) B462307
theorem B3467285 : Blo 119786 3467285 := bstep (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) B162529
theorem B289345 : Blo 119786 289345 := bstep (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) B217009
theorem B518987 : Blo 119786 518987 := bstep (se 1 (by rfl) ⟨389240, by rfl⟩ : syracuseStep 518987 = 778481) B778481
theorem B912221 : Blo 119786 912221 := bstep (se 3 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 912221 = 342083) B342083
theorem B2190349 : Blo 119786 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B1404377 : Blo 119786 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B618029 : Blo 119786 618029 := bstep (se 3 (by rfl) ⟨115880, by rfl⟩ : syracuseStep 618029 = 231761) B231761
theorem B192089 : Blo 119786 192089 := bstep (se 2 (by rfl) ⟨72033, by rfl⟩ : syracuseStep 192089 = 144067) B144067
theorem B290393 : Blo 119786 290393 := bstep (se 2 (by rfl) ⟨108897, by rfl⟩ : syracuseStep 290393 = 217795) B217795
theorem B192217 : Blo 119786 192217 := bstep (se 2 (by rfl) ⟨72081, by rfl⟩ : syracuseStep 192217 = 144163) B144163
theorem B519959 : Blo 119786 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B257879 : Blo 119786 257879 := bstep (se 1 (by rfl) ⟨193409, by rfl⟩ : syracuseStep 257879 = 386819) B386819
theorem B258059 : Blo 119786 258059 := bstep (se 1 (by rfl) ⟨193544, by rfl⟩ : syracuseStep 258059 = 387089) B387089
theorem B1339523 : Blo 119786 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B454835 : Blo 119786 454835 := bstep (se 1 (by rfl) ⟨341126, by rfl⟩ : syracuseStep 454835 = 682253) B682253
theorem B520627 : Blo 119786 520627 := bstep (se 1 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 520627 = 780941) B780941
theorem B1045037 : Blo 119786 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B455489 : Blo 119786 455489 := bstep (se 2 (by rfl) ⟨170808, by rfl⟩ : syracuseStep 455489 = 341617) B341617
theorem B1995637 : Blo 119786 1995637 := bstep (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) B187091
theorem B127991 : Blo 119786 127991 := bstep (se 1 (by rfl) ⟨95993, by rfl⟩ : syracuseStep 127991 = 191987) B191987
theorem B783425 : Blo 119786 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B1537325 : Blo 119786 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B882251 : Blo 119786 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B259699 : Blo 119786 259699 := bstep (se 1 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 259699 = 389549) B389549
theorem B521873 : Blo 119786 521873 := bstep (se 2 (by rfl) ⟨195702, by rfl⟩ : syracuseStep 521873 = 391405) B391405
theorem B292631 : Blo 119786 292631 := bstep (se 1 (by rfl) ⟨219473, by rfl⟩ : syracuseStep 292631 = 438947) B438947
theorem B456749 : Blo 119786 456749 := bstep (se 3 (by rfl) ⟨85640, by rfl⟩ : syracuseStep 456749 = 171281) B171281
theorem B456779 : Blo 119786 456779 := bstep (se 1 (by rfl) ⟨342584, by rfl⟩ : syracuseStep 456779 = 685169) B685169
theorem B260185 : Blo 119786 260185 := bstep (se 2 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 260185 = 195139) B195139
theorem B1800323 : Blo 119786 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B2586775 : Blo 119786 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B489665 : Blo 119786 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B227585 : Blo 119786 227585 := bstep (se 2 (by rfl) ⟨85344, by rfl⟩ : syracuseStep 227585 = 170689) B170689
theorem B686353 : Blo 119786 686353 := bstep (se 2 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 686353 = 514765) B514765
theorem B260377 : Blo 119786 260377 := bstep (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) B195283
theorem B391475 : Blo 119786 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B227927 : Blo 119786 227927 := bstep (se 1 (by rfl) ⟨170945, by rfl⟩ : syracuseStep 227927 = 341891) B341891
theorem B162443 : Blo 119786 162443 := bstep (se 1 (by rfl) ⟨121832, by rfl⟩ : syracuseStep 162443 = 243665) B243665
theorem B457433 : Blo 119786 457433 := bstep (se 2 (by rfl) ⟨171537, by rfl⟩ : syracuseStep 457433 = 343075) B343075
theorem B359257 : Blo 119786 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B457751 : Blo 119786 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B293939 : Blo 119786 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B130123 : Blo 119786 130123 := bstep (se 1 (by rfl) ⟨97592, by rfl⟩ : syracuseStep 130123 = 195185) B195185
theorem B293977 : Blo 119786 293977 := bstep (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) B220483
theorem B228595 : Blo 119786 228595 := bstep (se 1 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 228595 = 342893) B342893
theorem B195851 : Blo 119786 195851 := bstep (se 1 (by rfl) ⟨146888, by rfl⟩ : syracuseStep 195851 = 293777) B293777
theorem B490769 : Blo 119786 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B621917 : Blo 119786 621917 := bstep (se 3 (by rfl) ⟨116609, by rfl⟩ : syracuseStep 621917 = 233219) B233219
theorem B261569 : Blo 119786 261569 := bstep (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) B196177
theorem B229043 : Blo 119786 229043 := bstep (se 1 (by rfl) ⟨171782, by rfl⟩ : syracuseStep 229043 = 343565) B343565
theorem B458419 : Blo 119786 458419 := bstep (se 1 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 458419 = 687629) B687629
theorem B229081 : Blo 119786 229081 := bstep (se 2 (by rfl) ⟨85905, by rfl⟩ : syracuseStep 229081 = 171811) B171811
theorem B1343411 : Blo 119786 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B262091 : Blo 119786 262091 := bstep (se 1 (by rfl) ⟨196568, by rfl⟩ : syracuseStep 262091 = 393137) B393137
theorem B163913 : Blo 119786 163913 := bstep (se 2 (by rfl) ⟨61467, by rfl⟩ : syracuseStep 163913 = 122935) B122935
theorem B262433 : Blo 119786 262433 := bstep (se 2 (by rfl) ⟨98412, by rfl⟩ : syracuseStep 262433 = 196825) B196825
theorem B131387 : Blo 119786 131387 := bstep (se 1 (by rfl) ⟨98540, by rfl⟩ : syracuseStep 131387 = 197081) B197081
theorem B229817 : Blo 119786 229817 := bstep (se 2 (by rfl) ⟨86181, by rfl⟩ : syracuseStep 229817 = 172363) B172363
theorem B623051 : Blo 119786 623051 := bstep (se 1 (by rfl) ⟨467288, by rfl⟩ : syracuseStep 623051 = 934577) B934577
theorem B393815 : Blo 119786 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B525001 : Blo 119786 525001 := bstep (se 2 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 525001 = 393751) B393751
theorem B623375 : Blo 119786 623375 := bstep (se 1 (by rfl) ⟨467531, by rfl⟩ : syracuseStep 623375 = 935063) B935063
theorem B918539 : Blo 119786 918539 := bstep (se 1 (by rfl) ⟨688904, by rfl⟩ : syracuseStep 918539 = 1377809) B1377809
theorem B590915 : Blo 119786 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B459863 : Blo 119786 459863 := bstep (se 1 (by rfl) ⟨344897, by rfl⟩ : syracuseStep 459863 = 689795) B689795
theorem B590935 : Blo 119786 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B263483 : Blo 119786 263483 := bstep (se 1 (by rfl) ⟨197612, by rfl⟩ : syracuseStep 263483 = 395225) B395225
theorem B689543 : Blo 119786 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B460349 : Blo 119786 460349 := bstep (se 3 (by rfl) ⟨86315, by rfl⟩ : syracuseStep 460349 = 172631) B172631
theorem B165449 : Blo 119786 165449 := bstep (se 2 (by rfl) ⟨62043, by rfl⟩ : syracuseStep 165449 = 124087) B124087
theorem B788087 : Blo 119786 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B165817 : Blo 119786 165817 := bstep (se 2 (by rfl) ⟨62181, by rfl⟩ : syracuseStep 165817 = 124363) B124363
theorem B329729 : Blo 119786 329729 := bstep (se 2 (by rfl) ⟨123648, by rfl⟩ : syracuseStep 329729 = 247297) B247297
theorem B264235 : Blo 119786 264235 := bstep (se 1 (by rfl) ⟨198176, by rfl⟩ : syracuseStep 264235 = 396353) B396353
theorem B133255 : Blo 119786 133255 := bstep (se 1 (by rfl) ⟨99941, by rfl⟩ : syracuseStep 133255 = 199883) B199883
theorem B624833 : Blo 119786 624833 := bstep (se 2 (by rfl) ⟨234312, by rfl⟩ : syracuseStep 624833 = 468625) B468625
theorem B231815 : Blo 119786 231815 := bstep (se 1 (by rfl) ⟨173861, by rfl⟩ : syracuseStep 231815 = 347723) B347723
theorem B985945 : Blo 119786 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B920483 : Blo 119786 920483 := bstep (se 1 (by rfl) ⟨690362, by rfl⟩ : syracuseStep 920483 = 1380725) B1380725
theorem B494711 : Blo 119786 494711 := bstep (se 1 (by rfl) ⟨371033, by rfl⟩ : syracuseStep 494711 = 742067) B742067
theorem B462095 : Blo 119786 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B167287 : Blo 119786 167287 := bstep (se 1 (by rfl) ⟨125465, by rfl⟩ : syracuseStep 167287 = 250931) B250931
theorem B626129 : Blo 119786 626129 := bstep (se 2 (by rfl) ⟨234798, by rfl⟩ : syracuseStep 626129 = 469597) B469597
theorem B1052189 : Blo 119786 1052189 := bstep (se 3 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 1052189 = 394571) B394571
theorem B1183409 : Blo 119786 1183409 := bstep (se 2 (by rfl) ⟨443778, by rfl⟩ : syracuseStep 1183409 = 887557) B887557
theorem B233417 : Blo 119786 233417 := bstep (se 2 (by rfl) ⟨87531, by rfl⟩ : syracuseStep 233417 = 175063) B175063
theorem B135175 : Blo 119786 135175 := bstep (se 1 (by rfl) ⟨101381, by rfl⟩ : syracuseStep 135175 = 202763) B202763
theorem B2920465 : Blo 119786 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B888965 : Blo 119786 888965 := bstep (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) B166681
theorem B135355 : Blo 119786 135355 := bstep (se 1 (by rfl) ⟨101516, by rfl⟩ : syracuseStep 135355 = 203033) B203033
theorem B135823 : Blo 119786 135823 := bstep (se 1 (by rfl) ⟨101867, by rfl⟩ : syracuseStep 135823 = 203735) B203735
theorem B463751 : Blo 119786 463751 := bstep (se 1 (by rfl) ⟨347813, by rfl⟩ : syracuseStep 463751 = 695627) B695627
theorem B332801 : Blo 119786 332801 := bstep (se 2 (by rfl) ⟨124800, by rfl⟩ : syracuseStep 332801 = 249601) B249601
theorem B136327 : Blo 119786 136327 := bstep (se 1 (by rfl) ⟨102245, by rfl⟩ : syracuseStep 136327 = 204491) B204491
theorem B922913 : Blo 119786 922913 := bstep (se 2 (by rfl) ⟨346092, by rfl⟩ : syracuseStep 922913 = 692185) B692185
theorem B136507 : Blo 119786 136507 := bstep (se 1 (by rfl) ⟨102380, by rfl⟩ : syracuseStep 136507 = 204761) B204761
theorem B202169 : Blo 119786 202169 := bstep (se 2 (by rfl) ⟨75813, by rfl⟩ : syracuseStep 202169 = 151627) B151627
theorem B136975 : Blo 119786 136975 := bstep (se 1 (by rfl) ⟨102731, by rfl⟩ : syracuseStep 136975 = 205463) B205463
theorem B694169 : Blo 119786 694169 := bstep (se 2 (by rfl) ⟨260313, by rfl⟩ : syracuseStep 694169 = 520627) B520627
theorem B202871 : Blo 119786 202871 := bstep (se 1 (by rfl) ⟨152153, by rfl⟩ : syracuseStep 202871 = 304307) B304307
theorem B923885 : Blo 119786 923885 := bstep (se 3 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 923885 = 346457) B346457
theorem B137479 : Blo 119786 137479 := bstep (se 1 (by rfl) ⟨103109, by rfl⟩ : syracuseStep 137479 = 206219) B206219
theorem B891271 : Blo 119786 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B137659 : Blo 119786 137659 := bstep (se 1 (by rfl) ⟨103244, by rfl⟩ : syracuseStep 137659 = 206489) B206489
theorem B2660849 : Blo 119786 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B203323 : Blo 119786 203323 := bstep (se 1 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 203323 = 304985) B304985
theorem B465527 : Blo 119786 465527 := bstep (se 1 (by rfl) ⟨349145, by rfl⟩ : syracuseStep 465527 = 698291) B698291
theorem B203465 : Blo 119786 203465 := bstep (se 2 (by rfl) ⟨76299, by rfl⟩ : syracuseStep 203465 = 152599) B152599
theorem B138127 : Blo 119786 138127 := bstep (se 1 (by rfl) ⟨103595, by rfl⟩ : syracuseStep 138127 = 207191) B207191
theorem B662417 : Blo 119786 662417 := bstep (se 2 (by rfl) ⟨248406, by rfl⟩ : syracuseStep 662417 = 496813) B496813
theorem B433181 : Blo 119786 433181 := bstep (se 3 (by rfl) ⟨81221, by rfl⟩ : syracuseStep 433181 = 162443) B162443
theorem B1187131 : Blo 119786 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B204167 : Blo 119786 204167 := bstep (se 1 (by rfl) ⟨153125, by rfl⟩ : syracuseStep 204167 = 306251) B306251
theorem B138631 : Blo 119786 138631 := bstep (se 1 (by rfl) ⟨103973, by rfl⟩ : syracuseStep 138631 = 207947) B207947
theorem B597401 : Blo 119786 597401 := bstep (se 2 (by rfl) ⟨224025, by rfl⟩ : syracuseStep 597401 = 448051) B448051
theorem B1056185 : Blo 119786 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B138811 : Blo 119786 138811 := bstep (se 1 (by rfl) ⟨104108, by rfl⟩ : syracuseStep 138811 = 208217) B208217
theorem B466499 : Blo 119786 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B1187405 : Blo 119786 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B1056563 : Blo 119786 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B270215 : Blo 119786 270215 := bstep (se 1 (by rfl) ⟨202661, by rfl⟩ : syracuseStep 270215 = 405323) B405323
theorem B171919 : Blo 119786 171919 := bstep (se 1 (by rfl) ⟨128939, by rfl⟩ : syracuseStep 171919 = 257879) B257879
theorem B139151 : Blo 119786 139151 := bstep (se 1 (by rfl) ⟨104363, by rfl⟩ : syracuseStep 139151 = 208727) B208727
theorem B1187747 : Blo 119786 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B663481 : Blo 119786 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B172039 : Blo 119786 172039 := bstep (se 1 (by rfl) ⟨129029, by rfl⟩ : syracuseStep 172039 = 258059) B258059
theorem B466955 : Blo 119786 466955 := bstep (se 1 (by rfl) ⟨350216, by rfl⟩ : syracuseStep 466955 = 700433) B700433
theorem B204815 : Blo 119786 204815 := bstep (se 1 (by rfl) ⟨153611, by rfl⟩ : syracuseStep 204815 = 307223) B307223
theorem B270395 : Blo 119786 270395 := bstep (se 1 (by rfl) ⟨202796, by rfl⟩ : syracuseStep 270395 = 405593) B405593
theorem B893015 : Blo 119786 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B303223 : Blo 119786 303223 := bstep (se 1 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 303223 = 454835) B454835
theorem B925829 : Blo 119786 925829 := bstep (se 4 (by rfl) ⟨86796, by rfl⟩ : syracuseStep 925829 = 173593) B173593
theorem B270521 : Blo 119786 270521 := bstep (se 2 (by rfl) ⟨101445, by rfl⟩ : syracuseStep 270521 = 202891) B202891
theorem B3449033 : Blo 119786 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B1646837 : Blo 119786 1646837 := bstep (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) B154391
theorem B696691 : Blo 119786 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B270863 : Blo 119786 270863 := bstep (se 1 (by rfl) ⟨203147, by rfl⟩ : syracuseStep 270863 = 406295) B406295
theorem B270881 : Blo 119786 270881 := bstep (se 2 (by rfl) ⟨101580, by rfl⟩ : syracuseStep 270881 = 203161) B203161
theorem B303659 : Blo 119786 303659 := bstep (se 1 (by rfl) ⟨227744, by rfl⟩ : syracuseStep 303659 = 455489) B455489
theorem B205355 : Blo 119786 205355 := bstep (se 1 (by rfl) ⟨154016, by rfl⟩ : syracuseStep 205355 = 308033) B308033
theorem B336683 : Blo 119786 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B1024883 : Blo 119786 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B271223 : Blo 119786 271223 := bstep (se 1 (by rfl) ⟨203417, by rfl⟩ : syracuseStep 271223 = 406835) B406835
theorem B205753 : Blo 119786 205753 := bstep (se 2 (by rfl) ⟨77157, by rfl⟩ : syracuseStep 205753 = 154315) B154315
theorem B271403 : Blo 119786 271403 := bstep (se 1 (by rfl) ⟨203552, by rfl⟩ : syracuseStep 271403 = 407105) B407105
theorem B697517 : Blo 119786 697517 := bstep (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) B261569
theorem B664865 : Blo 119786 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B599329 : Blo 119786 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B304499 : Blo 119786 304499 := bstep (se 1 (by rfl) ⟨228374, by rfl⟩ : syracuseStep 304499 = 456749) B456749
theorem B304519 : Blo 119786 304519 := bstep (se 1 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 304519 = 456779) B456779
theorem B271763 : Blo 119786 271763 := bstep (se 1 (by rfl) ⟨203822, by rfl⟩ : syracuseStep 271763 = 407645) B407645
theorem B173497 : Blo 119786 173497 := bstep (se 2 (by rfl) ⟨65061, by rfl⟩ : syracuseStep 173497 = 130123) B130123
theorem B271817 : Blo 119786 271817 := bstep (se 2 (by rfl) ⟨101931, by rfl⟩ : syracuseStep 271817 = 203863) B203863
theorem B206455 : Blo 119786 206455 := bstep (se 1 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 206455 = 309683) B309683
theorem B304793 : Blo 119786 304793 := bstep (se 2 (by rfl) ⟨114297, by rfl⟩ : syracuseStep 304793 = 228595) B228595
theorem B304955 : Blo 119786 304955 := bstep (se 1 (by rfl) ⟨228716, by rfl⟩ : syracuseStep 304955 = 457433) B457433
theorem B206651 : Blo 119786 206651 := bstep (se 1 (by rfl) ⟨154988, by rfl⟩ : syracuseStep 206651 = 309977) B309977
theorem B1025945 : Blo 119786 1025945 := bstep (se 2 (by rfl) ⟨384729, by rfl⟩ : syracuseStep 1025945 = 769459) B769459
theorem B305167 : Blo 119786 305167 := bstep (se 1 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 305167 = 457751) B457751
theorem B1386557 : Blo 119786 1386557 := bstep (se 3 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 1386557 = 519959) B519959
theorem B469111 : Blo 119786 469111 := bstep (se 1 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 469111 = 703667) B703667
theorem B272519 : Blo 119786 272519 := bstep (se 1 (by rfl) ⟨204389, by rfl⟩ : syracuseStep 272519 = 408779) B408779
theorem B207049 : Blo 119786 207049 := bstep (se 2 (by rfl) ⟨77643, by rfl⟩ : syracuseStep 207049 = 155287) B155287
theorem B305441 : Blo 119786 305441 := bstep (se 2 (by rfl) ⟨114540, by rfl⟩ : syracuseStep 305441 = 229081) B229081
theorem B272699 : Blo 119786 272699 := bstep (se 1 (by rfl) ⟨204524, by rfl⟩ : syracuseStep 272699 = 409049) B409049
theorem B272825 : Blo 119786 272825 := bstep (se 2 (by rfl) ⟨102309, by rfl⟩ : syracuseStep 272825 = 204619) B204619
theorem B928259 : Blo 119786 928259 := bstep (se 1 (by rfl) ⟨696194, by rfl⟩ : syracuseStep 928259 = 1392389) B1392389
theorem B895607 : Blo 119786 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B174727 : Blo 119786 174727 := bstep (se 1 (by rfl) ⟨131045, by rfl⟩ : syracuseStep 174727 = 262091) B262091
theorem B273167 : Blo 119786 273167 := bstep (se 1 (by rfl) ⟨204875, by rfl⟩ : syracuseStep 273167 = 409751) B409751
theorem B273185 : Blo 119786 273185 := bstep (se 2 (by rfl) ⟨102444, by rfl⟩ : syracuseStep 273185 = 204889) B204889
theorem B207751 : Blo 119786 207751 := bstep (se 1 (by rfl) ⟨155813, by rfl⟩ : syracuseStep 207751 = 311627) B311627
theorem B404567 : Blo 119786 404567 := bstep (se 1 (by rfl) ⟨303425, by rfl⟩ : syracuseStep 404567 = 606851) B606851
theorem B273527 : Blo 119786 273527 := bstep (se 1 (by rfl) ⟨205145, by rfl⟩ : syracuseStep 273527 = 410291) B410291
theorem B306443 : Blo 119786 306443 := bstep (se 1 (by rfl) ⟨229832, by rfl⟩ : syracuseStep 306443 = 459665) B459665
theorem B273707 : Blo 119786 273707 := bstep (se 1 (by rfl) ⟨205280, by rfl⟩ : syracuseStep 273707 = 410561) B410561
theorem B175547 : Blo 119786 175547 := bstep (se 1 (by rfl) ⟨131660, by rfl⟩ : syracuseStep 175547 = 263321) B263321
theorem B208399 : Blo 119786 208399 := bstep (se 1 (by rfl) ⟨156299, by rfl⟩ : syracuseStep 208399 = 312599) B312599
theorem B634391 : Blo 119786 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B831019 : Blo 119786 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B405053 : Blo 119786 405053 := bstep (se 3 (by rfl) ⟨75947, by rfl⟩ : syracuseStep 405053 = 151895) B151895
theorem B274067 : Blo 119786 274067 := bstep (se 1 (by rfl) ⟨205550, by rfl⟩ : syracuseStep 274067 = 411101) B411101
theorem B274121 : Blo 119786 274121 := bstep (se 2 (by rfl) ⟨102795, by rfl⟩ : syracuseStep 274121 = 205591) B205591
theorem B307091 : Blo 119786 307091 := bstep (se 1 (by rfl) ⟨230318, by rfl⟩ : syracuseStep 307091 = 460637) B460637
theorem B176185 : Blo 119786 176185 := bstep (se 2 (by rfl) ⟨66069, by rfl⟩ : syracuseStep 176185 = 132139) B132139
theorem B1388677 : Blo 119786 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B307385 : Blo 119786 307385 := bstep (se 2 (by rfl) ⟨115269, by rfl⟩ : syracuseStep 307385 = 230539) B230539
theorem B274823 : Blo 119786 274823 := bstep (se 1 (by rfl) ⟨206117, by rfl⟩ : syracuseStep 274823 = 412235) B412235
theorem B1814929 : Blo 119786 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B635435 : Blo 119786 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B275003 : Blo 119786 275003 := bstep (se 1 (by rfl) ⟨206252, by rfl⟩ : syracuseStep 275003 = 412505) B412505
theorem B995917 : Blo 119786 995917 := bstep (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) B373469
theorem B275129 : Blo 119786 275129 := bstep (se 2 (by rfl) ⟨103173, by rfl⟩ : syracuseStep 275129 = 206347) B206347
theorem B1127141 : Blo 119786 1127141 := bstep (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) B211339
theorem B308083 : Blo 119786 308083 := bstep (se 1 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 308083 = 462125) B462125
theorem B406457 : Blo 119786 406457 := bstep (se 2 (by rfl) ⟨152421, by rfl⟩ : syracuseStep 406457 = 304843) B304843
theorem B308225 : Blo 119786 308225 := bstep (se 2 (by rfl) ⟨115584, by rfl⟩ : syracuseStep 308225 = 231169) B231169
theorem B275471 : Blo 119786 275471 := bstep (se 1 (by rfl) ⟨206603, by rfl⟩ : syracuseStep 275471 = 413207) B413207
theorem B275489 : Blo 119786 275489 := bstep (se 2 (by rfl) ⟨103308, by rfl⟩ : syracuseStep 275489 = 206617) B206617
theorem B439553 : Blo 119786 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B341263 : Blo 119786 341263 := bstep (se 1 (by rfl) ⟨255947, by rfl⟩ : syracuseStep 341263 = 511895) B511895
theorem B701729 : Blo 119786 701729 := bstep (se 2 (by rfl) ⟨263148, by rfl⟩ : syracuseStep 701729 = 526297) B526297
theorem B341309 : Blo 119786 341309 := bstep (se 3 (by rfl) ⟨63995, by rfl⟩ : syracuseStep 341309 = 127991) B127991
theorem B669017 : Blo 119786 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B275831 : Blo 119786 275831 := bstep (se 1 (by rfl) ⟨206873, by rfl⟩ : syracuseStep 275831 = 413747) B413747
theorem B243145 : Blo 119786 243145 := bstep (se 2 (by rfl) ⟨91179, by rfl⟩ : syracuseStep 243145 = 182359) B182359
theorem B308681 : Blo 119786 308681 := bstep (se 2 (by rfl) ⟨115755, by rfl⟩ : syracuseStep 308681 = 231511) B231511
theorem B407051 : Blo 119786 407051 := bstep (se 1 (by rfl) ⟨305288, by rfl⟩ : syracuseStep 407051 = 610577) B610577
theorem B276011 : Blo 119786 276011 := bstep (se 1 (by rfl) ⟨207008, by rfl⟩ : syracuseStep 276011 = 414017) B414017
theorem B1488451 : Blo 119786 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B407159 : Blo 119786 407159 := bstep (se 1 (by rfl) ⟨305369, by rfl⟩ : syracuseStep 407159 = 610739) B610739
theorem B341651 : Blo 119786 341651 := bstep (se 1 (by rfl) ⟨256238, by rfl⟩ : syracuseStep 341651 = 512477) B512477
theorem B702209 : Blo 119786 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B309035 : Blo 119786 309035 := bstep (se 1 (by rfl) ⟨231776, by rfl⟩ : syracuseStep 309035 = 463553) B463553
theorem B276371 : Blo 119786 276371 := bstep (se 1 (by rfl) ⟨207278, by rfl⟩ : syracuseStep 276371 = 414557) B414557
theorem B276425 : Blo 119786 276425 := bstep (se 2 (by rfl) ⟨103659, by rfl⟩ : syracuseStep 276425 = 207319) B207319
theorem B1423493 : Blo 119786 1423493 := bstep (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) B266905
theorem B145595 : Blo 119786 145595 := bstep (se 1 (by rfl) ⟨109196, by rfl⟩ : syracuseStep 145595 = 218393) B218393
theorem B407753 : Blo 119786 407753 := bstep (se 2 (by rfl) ⟨152907, by rfl⟩ : syracuseStep 407753 = 305815) B305815
theorem B702665 : Blo 119786 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B473359 : Blo 119786 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B342539 : Blo 119786 342539 := bstep (se 1 (by rfl) ⟨256904, by rfl⟩ : syracuseStep 342539 = 513809) B513809
theorem B703019 : Blo 119786 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B211499 : Blo 119786 211499 := bstep (se 1 (by rfl) ⟨158624, by rfl⟩ : syracuseStep 211499 = 317249) B317249
theorem B277127 : Blo 119786 277127 := bstep (se 1 (by rfl) ⟨207845, by rfl⟩ : syracuseStep 277127 = 415691) B415691
theorem B310027 : Blo 119786 310027 := bstep (se 1 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 310027 = 465041) B465041
theorem B277307 : Blo 119786 277307 := bstep (se 1 (by rfl) ⟨207980, by rfl⟩ : syracuseStep 277307 = 415961) B415961
theorem B408455 : Blo 119786 408455 := bstep (se 1 (by rfl) ⟨306341, by rfl⟩ : syracuseStep 408455 = 612683) B612683
theorem B310169 : Blo 119786 310169 := bstep (se 2 (by rfl) ⟨116313, by rfl⟩ : syracuseStep 310169 = 232627) B232627
theorem B277433 : Blo 119786 277433 := bstep (se 2 (by rfl) ⟨104037, by rfl⟩ : syracuseStep 277433 = 208075) B208075
theorem B1162187 : Blo 119786 1162187 := bstep (se 1 (by rfl) ⟨871640, by rfl⟩ : syracuseStep 1162187 = 1743281) B1743281
theorem B310331 : Blo 119786 310331 := bstep (se 1 (by rfl) ⟨232748, by rfl⟩ : syracuseStep 310331 = 465497) B465497
theorem B408833 : Blo 119786 408833 := bstep (se 2 (by rfl) ⟨153312, by rfl⟩ : syracuseStep 408833 = 306625) B306625
theorem B277775 : Blo 119786 277775 := bstep (se 1 (by rfl) ⟨208331, by rfl⟩ : syracuseStep 277775 = 416663) B416663
theorem B277793 : Blo 119786 277793 := bstep (se 2 (by rfl) ⟨104172, by rfl⟩ : syracuseStep 277793 = 208345) B208345
theorem B441715 : Blo 119786 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B310675 : Blo 119786 310675 := bstep (se 1 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 310675 = 466013) B466013
theorem B671179 : Blo 119786 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B310817 : Blo 119786 310817 := bstep (se 2 (by rfl) ⟨116556, by rfl⟩ : syracuseStep 310817 = 233113) B233113
theorem B179771 : Blo 119786 179771 := bstep (se 1 (by rfl) ⟨134828, by rfl⟩ : syracuseStep 179771 = 269657) B269657
theorem B1752677 : Blo 119786 1752677 := bstep (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) B328627
theorem B179831 : Blo 119786 179831 := bstep (se 1 (by rfl) ⟨134873, by rfl⟩ : syracuseStep 179831 = 269747) B269747
theorem B278135 : Blo 119786 278135 := bstep (se 1 (by rfl) ⟨208601, by rfl⟩ : syracuseStep 278135 = 417203) B417203
theorem B179855 : Blo 119786 179855 := bstep (se 1 (by rfl) ⟨134891, by rfl⟩ : syracuseStep 179855 = 269783) B269783
theorem B179897 : Blo 119786 179897 := bstep (se 2 (by rfl) ⟨67461, by rfl⟩ : syracuseStep 179897 = 134923) B134923
theorem B933605 : Blo 119786 933605 := bstep (se 4 (by rfl) ⟨87525, by rfl⟩ : syracuseStep 933605 = 175051) B175051
theorem B179975 : Blo 119786 179975 := bstep (se 1 (by rfl) ⟨134981, by rfl⟩ : syracuseStep 179975 = 269963) B269963
theorem B180011 : Blo 119786 180011 := bstep (se 1 (by rfl) ⟨135008, by rfl⟩ : syracuseStep 180011 = 270017) B270017
theorem B278315 : Blo 119786 278315 := bstep (se 1 (by rfl) ⟨208736, by rfl⟩ : syracuseStep 278315 = 417473) B417473
theorem B180041 : Blo 119786 180041 := bstep (se 2 (by rfl) ⟨67515, by rfl⟩ : syracuseStep 180041 = 135031) B135031
theorem B769945 : Blo 119786 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B180155 : Blo 119786 180155 := bstep (se 1 (by rfl) ⟨135116, by rfl⟩ : syracuseStep 180155 = 270233) B270233
theorem B180215 : Blo 119786 180215 := bstep (se 1 (by rfl) ⟨135161, by rfl⟩ : syracuseStep 180215 = 270323) B270323
theorem B180239 : Blo 119786 180239 := bstep (se 1 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 180239 = 270359) B270359
theorem B409643 : Blo 119786 409643 := bstep (se 1 (by rfl) ⟨307232, by rfl⟩ : syracuseStep 409643 = 614465) B614465
theorem B180281 : Blo 119786 180281 := bstep (se 2 (by rfl) ⟨67605, by rfl⟩ : syracuseStep 180281 = 135211) B135211
theorem B344179 : Blo 119786 344179 := bstep (se 1 (by rfl) ⟨258134, by rfl⟩ : syracuseStep 344179 = 516269) B516269
theorem B1556597 : Blo 119786 1556597 := bstep (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) B145931
theorem B180359 : Blo 119786 180359 := bstep (se 1 (by rfl) ⟨135269, by rfl⟩ : syracuseStep 180359 = 270539) B270539
theorem B180395 : Blo 119786 180395 := bstep (se 1 (by rfl) ⟨135296, by rfl⟩ : syracuseStep 180395 = 270593) B270593
theorem B180425 : Blo 119786 180425 := bstep (se 2 (by rfl) ⟨67659, by rfl⟩ : syracuseStep 180425 = 135319) B135319
theorem B180539 : Blo 119786 180539 := bstep (se 1 (by rfl) ⟨135404, by rfl⟩ : syracuseStep 180539 = 270809) B270809
theorem B344407 : Blo 119786 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B180599 : Blo 119786 180599 := bstep (se 1 (by rfl) ⟨135449, by rfl⟩ : syracuseStep 180599 = 270899) B270899
theorem B180623 : Blo 119786 180623 := bstep (se 1 (by rfl) ⟨135467, by rfl⟩ : syracuseStep 180623 = 270935) B270935
theorem B180665 : Blo 119786 180665 := bstep (se 2 (by rfl) ⟨67749, by rfl⟩ : syracuseStep 180665 = 135499) B135499
theorem B311809 : Blo 119786 311809 := bstep (se 2 (by rfl) ⟨116928, by rfl⟩ : syracuseStep 311809 = 233857) B233857
theorem B180743 : Blo 119786 180743 := bstep (se 1 (by rfl) ⟨135557, by rfl⟩ : syracuseStep 180743 = 271115) B271115
theorem B180779 : Blo 119786 180779 := bstep (se 1 (by rfl) ⟨135584, by rfl⟩ : syracuseStep 180779 = 271169) B271169
theorem B213563 : Blo 119786 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B180809 : Blo 119786 180809 := bstep (se 2 (by rfl) ⟨67803, by rfl⟩ : syracuseStep 180809 = 135607) B135607
theorem B1491533 : Blo 119786 1491533 := bstep (se 3 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 1491533 = 559325) B559325
theorem B180923 : Blo 119786 180923 := bstep (se 1 (by rfl) ⟨135692, by rfl⟩ : syracuseStep 180923 = 271385) B271385
theorem B180983 : Blo 119786 180983 := bstep (se 1 (by rfl) ⟨135737, by rfl⟩ : syracuseStep 180983 = 271475) B271475
theorem B181007 : Blo 119786 181007 := bstep (se 1 (by rfl) ⟨135755, by rfl⟩ : syracuseStep 181007 = 271511) B271511
theorem B181049 : Blo 119786 181049 := bstep (se 2 (by rfl) ⟨67893, by rfl⟩ : syracuseStep 181049 = 135787) B135787
theorem B181127 : Blo 119786 181127 := bstep (se 1 (by rfl) ⟨135845, by rfl⟩ : syracuseStep 181127 = 271691) B271691
theorem B279443 : Blo 119786 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B181163 : Blo 119786 181163 := bstep (se 1 (by rfl) ⟨135872, by rfl⟩ : syracuseStep 181163 = 271745) B271745
theorem B181193 : Blo 119786 181193 := bstep (se 2 (by rfl) ⟨67947, by rfl⟩ : syracuseStep 181193 = 135895) B135895
theorem B181307 : Blo 119786 181307 := bstep (se 1 (by rfl) ⟨135980, by rfl⟩ : syracuseStep 181307 = 271961) B271961
theorem B312407 : Blo 119786 312407 := bstep (se 1 (by rfl) ⟨234305, by rfl⟩ : syracuseStep 312407 = 468611) B468611
theorem B181367 : Blo 119786 181367 := bstep (se 1 (by rfl) ⟨136025, by rfl⟩ : syracuseStep 181367 = 272051) B272051
theorem B181391 : Blo 119786 181391 := bstep (se 1 (by rfl) ⟨136043, by rfl⟩ : syracuseStep 181391 = 272087) B272087
theorem B181433 : Blo 119786 181433 := bstep (se 2 (by rfl) ⟨68037, by rfl⟩ : syracuseStep 181433 = 136075) B136075
theorem B181511 : Blo 119786 181511 := bstep (se 1 (by rfl) ⟨136133, by rfl⟩ : syracuseStep 181511 = 272267) B272267
theorem B247055 : Blo 119786 247055 := bstep (se 1 (by rfl) ⟨185291, by rfl⟩ : syracuseStep 247055 = 370583) B370583
theorem B181547 : Blo 119786 181547 := bstep (se 1 (by rfl) ⟨136160, by rfl⟩ : syracuseStep 181547 = 272321) B272321
theorem B312619 : Blo 119786 312619 := bstep (se 1 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 312619 = 468929) B468929
theorem B410939 : Blo 119786 410939 := bstep (se 1 (by rfl) ⟨308204, by rfl⟩ : syracuseStep 410939 = 616409) B616409
theorem B181577 : Blo 119786 181577 := bstep (se 2 (by rfl) ⟨68091, by rfl⟩ : syracuseStep 181577 = 136183) B136183
theorem B2311523 : Blo 119786 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B312761 : Blo 119786 312761 := bstep (se 2 (by rfl) ⟨117285, by rfl⟩ : syracuseStep 312761 = 234571) B234571
theorem B181691 : Blo 119786 181691 := bstep (se 1 (by rfl) ⟨136268, by rfl⟩ : syracuseStep 181691 = 272537) B272537
theorem B181751 : Blo 119786 181751 := bstep (se 1 (by rfl) ⟨136313, by rfl⟩ : syracuseStep 181751 = 272627) B272627
theorem B181775 : Blo 119786 181775 := bstep (se 1 (by rfl) ⟨136331, by rfl⟩ : syracuseStep 181775 = 272663) B272663
theorem B181817 : Blo 119786 181817 := bstep (se 2 (by rfl) ⟨68181, by rfl⟩ : syracuseStep 181817 = 136363) B136363
theorem B312947 : Blo 119786 312947 := bstep (se 1 (by rfl) ⟨234710, by rfl⟩ : syracuseStep 312947 = 469421) B469421
theorem B181895 : Blo 119786 181895 := bstep (se 1 (by rfl) ⟨136421, by rfl⟩ : syracuseStep 181895 = 272843) B272843
theorem B181931 : Blo 119786 181931 := bstep (se 1 (by rfl) ⟨136448, by rfl⟩ : syracuseStep 181931 = 272897) B272897
theorem B6670001 : Blo 119786 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B181961 : Blo 119786 181961 := bstep (se 2 (by rfl) ⟨68235, by rfl⟩ : syracuseStep 181961 = 136471) B136471
theorem B411425 : Blo 119786 411425 := bstep (se 2 (by rfl) ⟨154284, by rfl⟩ : syracuseStep 411425 = 308569) B308569
theorem B182075 : Blo 119786 182075 := bstep (se 1 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 182075 = 273113) B273113
theorem B4474693 : Blo 119786 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B182135 : Blo 119786 182135 := bstep (se 1 (by rfl) ⟨136601, by rfl⟩ : syracuseStep 182135 = 273203) B273203
theorem B345991 : Blo 119786 345991 := bstep (se 1 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 345991 = 518987) B518987
theorem B182159 : Blo 119786 182159 := bstep (se 1 (by rfl) ⟨136619, by rfl⟩ : syracuseStep 182159 = 273239) B273239
theorem B608147 : Blo 119786 608147 := bstep (se 1 (by rfl) ⟨456110, by rfl⟩ : syracuseStep 608147 = 912221) B912221
theorem B182201 : Blo 119786 182201 := bstep (se 2 (by rfl) ⟨68325, by rfl⟩ : syracuseStep 182201 = 136651) B136651
theorem B313345 : Blo 119786 313345 := bstep (se 2 (by rfl) ⟨117504, by rfl⟩ : syracuseStep 313345 = 235009) B235009
theorem B182279 : Blo 119786 182279 := bstep (se 1 (by rfl) ⟨136709, by rfl⟩ : syracuseStep 182279 = 273419) B273419
theorem B182315 : Blo 119786 182315 := bstep (se 1 (by rfl) ⟨136736, by rfl⟩ : syracuseStep 182315 = 273473) B273473
theorem B182345 : Blo 119786 182345 := bstep (se 2 (by rfl) ⟨68379, by rfl⟩ : syracuseStep 182345 = 136759) B136759
theorem B1656949 : Blo 119786 1656949 := bstep (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) B155339
theorem B346265 : Blo 119786 346265 := bstep (se 2 (by rfl) ⟨129849, by rfl⟩ : syracuseStep 346265 = 259699) B259699
theorem B182459 : Blo 119786 182459 := bstep (se 1 (by rfl) ⟨136844, by rfl⟩ : syracuseStep 182459 = 273689) B273689
theorem B182519 : Blo 119786 182519 := bstep (se 1 (by rfl) ⟨136889, by rfl⟩ : syracuseStep 182519 = 273779) B273779
theorem B2377997 : Blo 119786 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B182543 : Blo 119786 182543 := bstep (se 1 (by rfl) ⟨136907, by rfl⟩ : syracuseStep 182543 = 273815) B273815
theorem B182585 : Blo 119786 182585 := bstep (se 2 (by rfl) ⟨68469, by rfl⟩ : syracuseStep 182585 = 136939) B136939
theorem B936251 : Blo 119786 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B412019 : Blo 119786 412019 := bstep (se 1 (by rfl) ⟨309014, by rfl⟩ : syracuseStep 412019 = 618029) B618029
theorem B182663 : Blo 119786 182663 := bstep (se 1 (by rfl) ⟨136997, by rfl⟩ : syracuseStep 182663 = 273995) B273995
theorem B182699 : Blo 119786 182699 := bstep (se 1 (by rfl) ⟨137024, by rfl⟩ : syracuseStep 182699 = 274049) B274049
theorem B182729 : Blo 119786 182729 := bstep (se 2 (by rfl) ⟨68523, by rfl⟩ : syracuseStep 182729 = 137047) B137047
theorem B182843 : Blo 119786 182843 := bstep (se 1 (by rfl) ⟨137132, by rfl⟩ : syracuseStep 182843 = 274265) B274265
theorem B182903 : Blo 119786 182903 := bstep (se 1 (by rfl) ⟨137177, by rfl⟩ : syracuseStep 182903 = 274355) B274355
theorem B182927 : Blo 119786 182927 := bstep (se 1 (by rfl) ⟨137195, by rfl⟩ : syracuseStep 182927 = 274391) B274391
theorem B576173 : Blo 119786 576173 := bstep (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) B216065
theorem B182969 : Blo 119786 182969 := bstep (se 2 (by rfl) ⟨68613, by rfl⟩ : syracuseStep 182969 = 137227) B137227
theorem B19942129 : Blo 119786 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B183047 : Blo 119786 183047 := bstep (se 1 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 183047 = 274571) B274571
theorem B346913 : Blo 119786 346913 := bstep (se 2 (by rfl) ⟨130092, by rfl⟩ : syracuseStep 346913 = 260185) B260185
theorem B183083 : Blo 119786 183083 := bstep (se 1 (by rfl) ⟨137312, by rfl⟩ : syracuseStep 183083 = 274625) B274625
theorem B183113 : Blo 119786 183113 := bstep (se 2 (by rfl) ⟨68667, by rfl⟩ : syracuseStep 183113 = 137335) B137335
theorem B183227 : Blo 119786 183227 := bstep (se 1 (by rfl) ⟨137420, by rfl⟩ : syracuseStep 183227 = 274841) B274841
theorem B183287 : Blo 119786 183287 := bstep (se 1 (by rfl) ⟨137465, by rfl⟩ : syracuseStep 183287 = 274931) B274931
theorem B183311 : Blo 119786 183311 := bstep (se 1 (by rfl) ⟨137483, by rfl⟩ : syracuseStep 183311 = 274967) B274967
theorem B183353 : Blo 119786 183353 := bstep (se 2 (by rfl) ⟨68757, by rfl⟩ : syracuseStep 183353 = 137515) B137515
theorem B183431 : Blo 119786 183431 := bstep (se 1 (by rfl) ⟨137573, by rfl⟩ : syracuseStep 183431 = 275147) B275147
theorem B183467 : Blo 119786 183467 := bstep (se 1 (by rfl) ⟨137600, by rfl⟩ : syracuseStep 183467 = 275201) B275201
theorem B183497 : Blo 119786 183497 := bstep (se 2 (by rfl) ⟨68811, by rfl⟩ : syracuseStep 183497 = 137623) B137623
theorem B183611 : Blo 119786 183611 := bstep (se 1 (by rfl) ⟨137708, by rfl⟩ : syracuseStep 183611 = 275417) B275417
theorem B183671 : Blo 119786 183671 := bstep (se 1 (by rfl) ⟨137753, by rfl⟩ : syracuseStep 183671 = 275507) B275507
theorem B183695 : Blo 119786 183695 := bstep (se 1 (by rfl) ⟨137771, by rfl⟩ : syracuseStep 183695 = 275543) B275543
theorem B183737 : Blo 119786 183737 := bstep (se 2 (by rfl) ⟨68901, by rfl⟩ : syracuseStep 183737 = 137803) B137803
theorem B183815 : Blo 119786 183815 := bstep (se 1 (by rfl) ⟨137861, by rfl⟩ : syracuseStep 183815 = 275723) B275723
theorem B183851 : Blo 119786 183851 := bstep (se 1 (by rfl) ⟨137888, by rfl⟩ : syracuseStep 183851 = 275777) B275777
theorem B183881 : Blo 119786 183881 := bstep (se 2 (by rfl) ⟨68955, by rfl⟩ : syracuseStep 183881 = 137911) B137911
theorem B183995 : Blo 119786 183995 := bstep (se 1 (by rfl) ⟨137996, by rfl⟩ : syracuseStep 183995 = 275993) B275993
theorem B184055 : Blo 119786 184055 := bstep (se 1 (by rfl) ⟨138041, by rfl⟩ : syracuseStep 184055 = 276083) B276083
theorem B347915 : Blo 119786 347915 := bstep (se 1 (by rfl) ⟨260936, by rfl⟩ : syracuseStep 347915 = 521873) B521873
theorem B184079 : Blo 119786 184079 := bstep (se 1 (by rfl) ⟨138059, by rfl⟩ : syracuseStep 184079 = 276119) B276119
theorem B479009 : Blo 119786 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B184121 : Blo 119786 184121 := bstep (se 2 (by rfl) ⟨69045, by rfl⟩ : syracuseStep 184121 = 138091) B138091
theorem B511879 : Blo 119786 511879 := bstep (se 1 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 511879 = 767819) B767819
theorem B184199 : Blo 119786 184199 := bstep (se 1 (by rfl) ⟨138149, by rfl⟩ : syracuseStep 184199 = 276299) B276299
theorem B184235 : Blo 119786 184235 := bstep (se 1 (by rfl) ⟨138176, by rfl⟩ : syracuseStep 184235 = 276353) B276353
theorem B184265 : Blo 119786 184265 := bstep (se 2 (by rfl) ⟨69099, by rfl⟩ : syracuseStep 184265 = 138199) B138199
theorem B184379 : Blo 119786 184379 := bstep (se 1 (by rfl) ⟨138284, by rfl⟩ : syracuseStep 184379 = 276569) B276569
theorem B1200215 : Blo 119786 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B1986677 : Blo 119786 1986677 := bstep (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) B186251
theorem B184439 : Blo 119786 184439 := bstep (se 1 (by rfl) ⟨138329, by rfl⟩ : syracuseStep 184439 = 276659) B276659
theorem B184463 : Blo 119786 184463 := bstep (se 1 (by rfl) ⟨138347, by rfl⟩ : syracuseStep 184463 = 276695) B276695
theorem B151723 : Blo 119786 151723 := bstep (se 1 (by rfl) ⟨113792, by rfl⟩ : syracuseStep 151723 = 227585) B227585
theorem B184505 : Blo 119786 184505 := bstep (se 2 (by rfl) ⟨69189, by rfl⟩ : syracuseStep 184505 = 138379) B138379
theorem B512237 : Blo 119786 512237 := bstep (se 3 (by rfl) ⟨96044, by rfl⟩ : syracuseStep 512237 = 192089) B192089
theorem B184583 : Blo 119786 184583 := bstep (se 1 (by rfl) ⟨138437, by rfl⟩ : syracuseStep 184583 = 276875) B276875
theorem B184619 : Blo 119786 184619 := bstep (se 1 (by rfl) ⟨138464, by rfl⟩ : syracuseStep 184619 = 276929) B276929
theorem B184649 : Blo 119786 184649 := bstep (se 2 (by rfl) ⟨69243, by rfl⟩ : syracuseStep 184649 = 138487) B138487
theorem B151951 : Blo 119786 151951 := bstep (se 1 (by rfl) ⟨113963, by rfl⟩ : syracuseStep 151951 = 227927) B227927
theorem B184763 : Blo 119786 184763 := bstep (se 1 (by rfl) ⟨138572, by rfl⟩ : syracuseStep 184763 = 277145) B277145
theorem B184823 : Blo 119786 184823 := bstep (se 1 (by rfl) ⟨138617, by rfl⟩ : syracuseStep 184823 = 277235) B277235
theorem B184847 : Blo 119786 184847 := bstep (se 1 (by rfl) ⟨138635, by rfl⟩ : syracuseStep 184847 = 277271) B277271
theorem B184889 : Blo 119786 184889 := bstep (se 2 (by rfl) ⟨69333, by rfl⟩ : syracuseStep 184889 = 138667) B138667
theorem B184967 : Blo 119786 184967 := bstep (se 1 (by rfl) ⟨138725, by rfl⟩ : syracuseStep 184967 = 277451) B277451
theorem B185003 : Blo 119786 185003 := bstep (se 1 (by rfl) ⟨138752, by rfl⟩ : syracuseStep 185003 = 277505) B277505
theorem B185033 : Blo 119786 185033 := bstep (se 2 (by rfl) ⟨69387, by rfl⟩ : syracuseStep 185033 = 138775) B138775
theorem B185147 : Blo 119786 185147 := bstep (se 1 (by rfl) ⟨138860, by rfl⟩ : syracuseStep 185147 = 277721) B277721
theorem B185207 : Blo 119786 185207 := bstep (se 1 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 185207 = 277811) B277811
theorem B185231 : Blo 119786 185231 := bstep (se 1 (by rfl) ⟨138923, by rfl⟩ : syracuseStep 185231 = 277847) B277847
theorem B414611 : Blo 119786 414611 := bstep (se 1 (by rfl) ⟨310958, by rfl⟩ : syracuseStep 414611 = 621917) B621917
theorem B611225 : Blo 119786 611225 := bstep (se 2 (by rfl) ⟨229209, by rfl⟩ : syracuseStep 611225 = 458419) B458419
theorem B185273 : Blo 119786 185273 := bstep (se 2 (by rfl) ⟨69477, by rfl⟩ : syracuseStep 185273 = 138955) B138955
theorem B119815 : Blo 119786 119815 := bstep (se 1 (by rfl) ⟨89861, by rfl⟩ : syracuseStep 119815 = 179723) B179723
theorem B185351 : Blo 119786 185351 := bstep (se 1 (by rfl) ⟨139013, by rfl⟩ : syracuseStep 185351 = 278027) B278027
theorem B119823 : Blo 119786 119823 := bstep (se 1 (by rfl) ⟨89867, by rfl⟩ : syracuseStep 119823 = 179735) B179735
theorem B185387 : Blo 119786 185387 := bstep (se 1 (by rfl) ⟨139040, by rfl⟩ : syracuseStep 185387 = 278081) B278081
theorem B119867 : Blo 119786 119867 := bstep (se 1 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 119867 = 179801) B179801
theorem B185417 : Blo 119786 185417 := bstep (se 2 (by rfl) ⟨69531, by rfl⟩ : syracuseStep 185417 = 139063) B139063
theorem B152695 : Blo 119786 152695 := bstep (se 1 (by rfl) ⟨114521, by rfl⟩ : syracuseStep 152695 = 229043) B229043
theorem B119943 : Blo 119786 119943 := bstep (se 1 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 119943 = 179915) B179915
theorem B119951 : Blo 119786 119951 := bstep (se 1 (by rfl) ⟨89963, by rfl⟩ : syracuseStep 119951 = 179927) B179927
theorem B119995 : Blo 119786 119995 := bstep (se 1 (by rfl) ⟨89996, by rfl⟩ : syracuseStep 119995 = 179993) B179993
theorem B185531 : Blo 119786 185531 := bstep (se 1 (by rfl) ⟨139148, by rfl⟩ : syracuseStep 185531 = 278297) B278297
theorem B185591 : Blo 119786 185591 := bstep (se 1 (by rfl) ⟨139193, by rfl⟩ : syracuseStep 185591 = 278387) B278387
theorem B120071 : Blo 119786 120071 := bstep (se 1 (by rfl) ⟨90053, by rfl⟩ : syracuseStep 120071 = 180107) B180107
theorem B120079 : Blo 119786 120079 := bstep (se 1 (by rfl) ⟨90059, by rfl⟩ : syracuseStep 120079 = 180119) B180119
theorem B185615 : Blo 119786 185615 := bstep (se 1 (by rfl) ⟨139211, by rfl⟩ : syracuseStep 185615 = 278423) B278423
theorem B185657 : Blo 119786 185657 := bstep (se 2 (by rfl) ⟨69621, by rfl⟩ : syracuseStep 185657 = 139243) B139243
theorem B120123 : Blo 119786 120123 := bstep (se 1 (by rfl) ⟨90092, by rfl⟩ : syracuseStep 120123 = 180185) B180185
theorem B120199 : Blo 119786 120199 := bstep (se 1 (by rfl) ⟨90149, by rfl⟩ : syracuseStep 120199 = 180299) B180299
theorem B120207 : Blo 119786 120207 := bstep (se 1 (by rfl) ⟨90155, by rfl⟩ : syracuseStep 120207 = 180311) B180311
theorem B120251 : Blo 119786 120251 := bstep (se 1 (by rfl) ⟨90188, by rfl⟩ : syracuseStep 120251 = 180377) B180377
theorem B153019 : Blo 119786 153019 := bstep (se 1 (by rfl) ⟨114764, by rfl⟩ : syracuseStep 153019 = 229529) B229529
theorem B1398221 : Blo 119786 1398221 := bstep (se 3 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 1398221 = 524333) B524333
theorem B120327 : Blo 119786 120327 := bstep (se 1 (by rfl) ⟨90245, by rfl⟩ : syracuseStep 120327 = 180491) B180491
theorem B120335 : Blo 119786 120335 := bstep (se 1 (by rfl) ⟨90251, by rfl⟩ : syracuseStep 120335 = 180503) B180503
theorem B120379 : Blo 119786 120379 := bstep (se 1 (by rfl) ⟨90284, by rfl⟩ : syracuseStep 120379 = 180569) B180569
theorem B120455 : Blo 119786 120455 := bstep (se 1 (by rfl) ⟨90341, by rfl⟩ : syracuseStep 120455 = 180683) B180683
theorem B120463 : Blo 119786 120463 := bstep (se 1 (by rfl) ⟨90347, by rfl⟩ : syracuseStep 120463 = 180695) B180695
theorem B120507 : Blo 119786 120507 := bstep (se 1 (by rfl) ⟨90380, by rfl⟩ : syracuseStep 120507 = 180761) B180761
theorem B120583 : Blo 119786 120583 := bstep (se 1 (by rfl) ⟨90437, by rfl⟩ : syracuseStep 120583 = 180875) B180875
theorem B120591 : Blo 119786 120591 := bstep (se 1 (by rfl) ⟨90443, by rfl⟩ : syracuseStep 120591 = 180887) B180887
theorem B120635 : Blo 119786 120635 := bstep (se 1 (by rfl) ⟨90476, by rfl⟩ : syracuseStep 120635 = 180953) B180953
theorem B350011 : Blo 119786 350011 := bstep (se 1 (by rfl) ⟨262508, by rfl⟩ : syracuseStep 350011 = 525017) B525017
theorem B120711 : Blo 119786 120711 := bstep (se 1 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 120711 = 181067) B181067
theorem B743303 : Blo 119786 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B120719 : Blo 119786 120719 := bstep (se 1 (by rfl) ⟨90539, by rfl⟩ : syracuseStep 120719 = 181079) B181079
theorem B153515 : Blo 119786 153515 := bstep (se 1 (by rfl) ⟨115136, by rfl⟩ : syracuseStep 153515 = 230273) B230273
theorem B120763 : Blo 119786 120763 := bstep (se 1 (by rfl) ⟨90572, by rfl⟩ : syracuseStep 120763 = 181145) B181145
theorem B120839 : Blo 119786 120839 := bstep (se 1 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 120839 = 181259) B181259
theorem B120847 : Blo 119786 120847 := bstep (se 1 (by rfl) ⟨90635, by rfl⟩ : syracuseStep 120847 = 181271) B181271
theorem B120891 : Blo 119786 120891 := bstep (se 1 (by rfl) ⟨90668, by rfl⟩ : syracuseStep 120891 = 181337) B181337
theorem B120967 : Blo 119786 120967 := bstep (se 1 (by rfl) ⟨90725, by rfl⟩ : syracuseStep 120967 = 181451) B181451
theorem B120975 : Blo 119786 120975 := bstep (se 1 (by rfl) ⟨90731, by rfl⟩ : syracuseStep 120975 = 181463) B181463
theorem B121019 : Blo 119786 121019 := bstep (se 1 (by rfl) ⟨90764, by rfl⟩ : syracuseStep 121019 = 181529) B181529
theorem B121095 : Blo 119786 121095 := bstep (se 1 (by rfl) ⟨90821, by rfl⟩ : syracuseStep 121095 = 181643) B181643
theorem B121103 : Blo 119786 121103 := bstep (se 1 (by rfl) ⟨90827, by rfl⟩ : syracuseStep 121103 = 181655) B181655
theorem B416015 : Blo 119786 416015 := bstep (se 1 (by rfl) ⟨312011, by rfl⟩ : syracuseStep 416015 = 624023) B624023
theorem B121147 : Blo 119786 121147 := bstep (se 1 (by rfl) ⟨90860, by rfl⟩ : syracuseStep 121147 = 181721) B181721
theorem B121223 : Blo 119786 121223 := bstep (se 1 (by rfl) ⟨90917, by rfl⟩ : syracuseStep 121223 = 181835) B181835
theorem B153991 : Blo 119786 153991 := bstep (se 1 (by rfl) ⟨115493, by rfl⟩ : syracuseStep 153991 = 230987) B230987
theorem B121231 : Blo 119786 121231 := bstep (se 1 (by rfl) ⟨90923, by rfl⟩ : syracuseStep 121231 = 181847) B181847
theorem B121275 : Blo 119786 121275 := bstep (se 1 (by rfl) ⟨90956, by rfl⟩ : syracuseStep 121275 = 181913) B181913
theorem B121351 : Blo 119786 121351 := bstep (se 1 (by rfl) ⟨91013, by rfl⟩ : syracuseStep 121351 = 182027) B182027
theorem B121359 : Blo 119786 121359 := bstep (se 1 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 121359 = 182039) B182039
theorem B416285 : Blo 119786 416285 := bstep (se 3 (by rfl) ⟨78053, by rfl⟩ : syracuseStep 416285 = 156107) B156107
theorem B121403 : Blo 119786 121403 := bstep (se 1 (by rfl) ⟨91052, by rfl⟩ : syracuseStep 121403 = 182105) B182105
theorem B121479 : Blo 119786 121479 := bstep (se 1 (by rfl) ⟨91109, by rfl⟩ : syracuseStep 121479 = 182219) B182219
theorem B350855 : Blo 119786 350855 := bstep (se 1 (by rfl) ⟨263141, by rfl⟩ : syracuseStep 350855 = 526283) B526283
theorem B121487 : Blo 119786 121487 := bstep (se 1 (by rfl) ⟨91115, by rfl⟩ : syracuseStep 121487 = 182231) B182231
theorem B121531 : Blo 119786 121531 := bstep (se 1 (by rfl) ⟨91148, by rfl⟩ : syracuseStep 121531 = 182297) B182297
theorem B121607 : Blo 119786 121607 := bstep (se 1 (by rfl) ⟨91205, by rfl⟩ : syracuseStep 121607 = 182411) B182411
theorem B121615 : Blo 119786 121615 := bstep (se 1 (by rfl) ⟨91211, by rfl⟩ : syracuseStep 121615 = 182423) B182423
theorem B2644751 : Blo 119786 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B973619 : Blo 119786 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B121659 : Blo 119786 121659 := bstep (se 1 (by rfl) ⟨91244, by rfl⟩ : syracuseStep 121659 = 182489) B182489
theorem B154487 : Blo 119786 154487 := bstep (se 1 (by rfl) ⟨115865, by rfl⟩ : syracuseStep 154487 = 231731) B231731
theorem B121735 : Blo 119786 121735 := bstep (se 1 (by rfl) ⟨91301, by rfl⟩ : syracuseStep 121735 = 182603) B182603
theorem B121743 : Blo 119786 121743 := bstep (se 1 (by rfl) ⟨91307, by rfl⟩ : syracuseStep 121743 = 182615) B182615
theorem B121787 : Blo 119786 121787 := bstep (se 1 (by rfl) ⟨91340, by rfl⟩ : syracuseStep 121787 = 182681) B182681
theorem B121863 : Blo 119786 121863 := bstep (se 1 (by rfl) ⟨91397, by rfl⟩ : syracuseStep 121863 = 182795) B182795
theorem B121871 : Blo 119786 121871 := bstep (se 1 (by rfl) ⟨91403, by rfl⟩ : syracuseStep 121871 = 182807) B182807
theorem B154639 : Blo 119786 154639 := bstep (se 1 (by rfl) ⟨115979, by rfl⟩ : syracuseStep 154639 = 231959) B231959
theorem B121915 : Blo 119786 121915 := bstep (se 1 (by rfl) ⟨91436, by rfl⟩ : syracuseStep 121915 = 182873) B182873
theorem B121991 : Blo 119786 121991 := bstep (se 1 (by rfl) ⟨91493, by rfl⟩ : syracuseStep 121991 = 182987) B182987
theorem B121999 : Blo 119786 121999 := bstep (se 1 (by rfl) ⟨91499, by rfl⟩ : syracuseStep 121999 = 182999) B182999
theorem B122043 : Blo 119786 122043 := bstep (se 1 (by rfl) ⟨91532, by rfl⟩ : syracuseStep 122043 = 183065) B183065
theorem B154811 : Blo 119786 154811 := bstep (se 1 (by rfl) ⟨116108, by rfl⟩ : syracuseStep 154811 = 232217) B232217
theorem B122119 : Blo 119786 122119 := bstep (se 1 (by rfl) ⟨91589, by rfl⟩ : syracuseStep 122119 = 183179) B183179
theorem B122127 : Blo 119786 122127 := bstep (se 1 (by rfl) ⟨91595, by rfl⟩ : syracuseStep 122127 = 183191) B183191
theorem B122171 : Blo 119786 122171 := bstep (se 1 (by rfl) ⟨91628, by rfl⟩ : syracuseStep 122171 = 183257) B183257
theorem B122247 : Blo 119786 122247 := bstep (se 1 (by rfl) ⟨91685, by rfl⟩ : syracuseStep 122247 = 183371) B183371
theorem B1334663 : Blo 119786 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B122255 : Blo 119786 122255 := bstep (se 1 (by rfl) ⟨91691, by rfl⟩ : syracuseStep 122255 = 183383) B183383
theorem B351641 : Blo 119786 351641 := bstep (se 2 (by rfl) ⟨131865, by rfl⟩ : syracuseStep 351641 = 263731) B263731
theorem B613817 : Blo 119786 613817 := bstep (se 2 (by rfl) ⟨230181, by rfl⟩ : syracuseStep 613817 = 460363) B460363
theorem B122299 : Blo 119786 122299 := bstep (se 1 (by rfl) ⟨91724, by rfl⟩ : syracuseStep 122299 = 183449) B183449
theorem B122375 : Blo 119786 122375 := bstep (se 1 (by rfl) ⟨91781, by rfl⟩ : syracuseStep 122375 = 183563) B183563
theorem B122383 : Blo 119786 122383 := bstep (se 1 (by rfl) ⟨91787, by rfl⟩ : syracuseStep 122383 = 183575) B183575
theorem B122427 : Blo 119786 122427 := bstep (se 1 (by rfl) ⟨91820, by rfl⟩ : syracuseStep 122427 = 183641) B183641
theorem B2055779 : Blo 119786 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B122503 : Blo 119786 122503 := bstep (se 1 (by rfl) ⟨91877, by rfl⟩ : syracuseStep 122503 = 183755) B183755
theorem B122511 : Blo 119786 122511 := bstep (se 1 (by rfl) ⟨91883, by rfl⟩ : syracuseStep 122511 = 183767) B183767
theorem B122555 : Blo 119786 122555 := bstep (se 1 (by rfl) ⟨91916, by rfl⟩ : syracuseStep 122555 = 183833) B183833
theorem B122631 : Blo 119786 122631 := bstep (se 1 (by rfl) ⟨91973, by rfl⟩ : syracuseStep 122631 = 183947) B183947
theorem B122639 : Blo 119786 122639 := bstep (se 1 (by rfl) ⟨91979, by rfl⟩ : syracuseStep 122639 = 183959) B183959
theorem B122683 : Blo 119786 122683 := bstep (se 1 (by rfl) ⟨92012, by rfl⟩ : syracuseStep 122683 = 184025) B184025
theorem B122759 : Blo 119786 122759 := bstep (se 1 (by rfl) ⟨92069, by rfl⟩ : syracuseStep 122759 = 184139) B184139
theorem B122767 : Blo 119786 122767 := bstep (se 1 (by rfl) ⟨92075, by rfl⟩ : syracuseStep 122767 = 184151) B184151
theorem B417689 : Blo 119786 417689 := bstep (se 2 (by rfl) ⟨156633, by rfl⟩ : syracuseStep 417689 = 313267) B313267
theorem B122811 : Blo 119786 122811 := bstep (se 1 (by rfl) ⟨92108, by rfl⟩ : syracuseStep 122811 = 184217) B184217
theorem B122887 : Blo 119786 122887 := bstep (se 1 (by rfl) ⟨92165, by rfl⟩ : syracuseStep 122887 = 184331) B184331
theorem B122895 : Blo 119786 122895 := bstep (se 1 (by rfl) ⟨92171, by rfl⟩ : syracuseStep 122895 = 184343) B184343
theorem B352289 : Blo 119786 352289 := bstep (se 2 (by rfl) ⟨132108, by rfl⟩ : syracuseStep 352289 = 264217) B264217
theorem B122939 : Blo 119786 122939 := bstep (se 1 (by rfl) ⟨92204, by rfl⟩ : syracuseStep 122939 = 184409) B184409
theorem B123015 : Blo 119786 123015 := bstep (se 1 (by rfl) ⟨92261, by rfl⟩ : syracuseStep 123015 = 184523) B184523
theorem B155783 : Blo 119786 155783 := bstep (se 1 (by rfl) ⟨116837, by rfl⟩ : syracuseStep 155783 = 233675) B233675
theorem B123023 : Blo 119786 123023 := bstep (se 1 (by rfl) ⟨92267, by rfl⟩ : syracuseStep 123023 = 184535) B184535
theorem B123067 : Blo 119786 123067 := bstep (se 1 (by rfl) ⟨92300, by rfl⟩ : syracuseStep 123067 = 184601) B184601
theorem B123143 : Blo 119786 123143 := bstep (se 1 (by rfl) ⟨92357, by rfl⟩ : syracuseStep 123143 = 184715) B184715
theorem B123151 : Blo 119786 123151 := bstep (se 1 (by rfl) ⟨92363, by rfl⟩ : syracuseStep 123151 = 184727) B184727
theorem B123195 : Blo 119786 123195 := bstep (se 1 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 123195 = 184793) B184793
theorem B123271 : Blo 119786 123271 := bstep (se 1 (by rfl) ⟨92453, by rfl⟩ : syracuseStep 123271 = 184907) B184907
theorem B123279 : Blo 119786 123279 := bstep (se 1 (by rfl) ⟨92459, by rfl⟩ : syracuseStep 123279 = 184919) B184919
theorem B123323 : Blo 119786 123323 := bstep (se 1 (by rfl) ⟨92492, by rfl⟩ : syracuseStep 123323 = 184985) B184985
theorem B123399 : Blo 119786 123399 := bstep (se 1 (by rfl) ⟨92549, by rfl⟩ : syracuseStep 123399 = 185099) B185099
theorem B123407 : Blo 119786 123407 := bstep (se 1 (by rfl) ⟨92555, by rfl⟩ : syracuseStep 123407 = 185111) B185111
theorem B582187 : Blo 119786 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B123451 : Blo 119786 123451 := bstep (se 1 (by rfl) ⟨92588, by rfl⟩ : syracuseStep 123451 = 185177) B185177
theorem B1466999 : Blo 119786 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B123527 : Blo 119786 123527 := bstep (se 1 (by rfl) ⟨92645, by rfl⟩ : syracuseStep 123527 = 185291) B185291
theorem B123535 : Blo 119786 123535 := bstep (se 1 (by rfl) ⟨92651, by rfl⟩ : syracuseStep 123535 = 185303) B185303
theorem B221843 : Blo 119786 221843 := bstep (se 1 (by rfl) ⟨166382, by rfl⟩ : syracuseStep 221843 = 332765) B332765
theorem B123579 : Blo 119786 123579 := bstep (se 1 (by rfl) ⟨92684, by rfl⟩ : syracuseStep 123579 = 185369) B185369
theorem B615113 : Blo 119786 615113 := bstep (se 2 (by rfl) ⟨230667, by rfl⟩ : syracuseStep 615113 = 461335) B461335
theorem B385793 : Blo 119786 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B123655 : Blo 119786 123655 := bstep (se 1 (by rfl) ⟨92741, by rfl⟩ : syracuseStep 123655 = 185483) B185483
theorem B156431 : Blo 119786 156431 := bstep (se 1 (by rfl) ⟨117323, by rfl⟩ : syracuseStep 156431 = 234647) B234647
theorem B123663 : Blo 119786 123663 := bstep (se 1 (by rfl) ⟨92747, by rfl⟩ : syracuseStep 123663 = 185495) B185495
theorem B123707 : Blo 119786 123707 := bstep (se 1 (by rfl) ⟨92780, by rfl⟩ : syracuseStep 123707 = 185561) B185561
theorem B123783 : Blo 119786 123783 := bstep (se 1 (by rfl) ⟨92837, by rfl⟩ : syracuseStep 123783 = 185675) B185675
theorem B3433859 : Blo 119786 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B124687 : Blo 119786 124687 := bstep (se 1 (by rfl) ⟨93515, by rfl⟩ : syracuseStep 124687 = 187031) B187031
theorem B1042379 : Blo 119786 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B780349 : Blo 119786 780349 := bstep (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) B292631
theorem B256289 : Blo 119786 256289 := bstep (se 2 (by rfl) ⟨96108, by rfl⟩ : syracuseStep 256289 = 192217) B192217
theorem B256375 : Blo 119786 256375 := bstep (se 1 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 256375 = 384563) B384563
theorem B1043063 : Blo 119786 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B289595 : Blo 119786 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B682937 : Blo 119786 682937 := bstep (se 2 (by rfl) ⟨256101, by rfl⟩ : syracuseStep 682937 = 512203) B512203
theorem B290249 : Blo 119786 290249 := bstep (se 2 (by rfl) ⟨108843, by rfl⟩ : syracuseStep 290249 = 217687) B217687
theorem B290575 : Blo 119786 290575 := bstep (se 1 (by rfl) ⟨217931, by rfl⟩ : syracuseStep 290575 = 435863) B435863
theorem B749533 : Blo 119786 749533 := bstep (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) B281075
theorem B291671 : Blo 119786 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B291737 : Blo 119786 291737 := bstep (se 2 (by rfl) ⟨109401, by rfl⟩ : syracuseStep 291737 = 218803) B218803
theorem B193595 : Blo 119786 193595 := bstep (se 1 (by rfl) ⟨145196, by rfl⟩ : syracuseStep 193595 = 290393) B290393
theorem B980369 : Blo 119786 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B915137 : Blo 119786 915137 := bstep (se 2 (by rfl) ⟨343176, by rfl⟩ : syracuseStep 915137 = 686353) B686353
theorem B325577 : Blo 119786 325577 := bstep (se 2 (by rfl) ⟨122091, by rfl⟩ : syracuseStep 325577 = 244183) B244183
theorem B522283 : Blo 119786 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B2652277 : Blo 119786 2652277 := bstep (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) B248651
theorem B456961 : Blo 119786 456961 := bstep (se 2 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 456961 = 342721) B342721
theorem B588167 : Blo 119786 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B620945 : Blo 119786 620945 := bstep (se 2 (by rfl) ⟨232854, by rfl⟩ : syracuseStep 620945 = 465709) B465709
theorem B588185 : Blo 119786 588185 := bstep (se 2 (by rfl) ⟨220569, by rfl⟩ : syracuseStep 588185 = 441139) B441139
theorem B227873 : Blo 119786 227873 := bstep (se 2 (by rfl) ⟨85452, by rfl⟩ : syracuseStep 227873 = 170905) B170905
theorem B228025 : Blo 119786 228025 := bstep (se 2 (by rfl) ⟨85509, by rfl⟩ : syracuseStep 228025 = 171019) B171019
theorem B391969 : Blo 119786 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B326443 : Blo 119786 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B260983 : Blo 119786 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B195959 : Blo 119786 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B490961 : Blo 119786 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B130567 : Blo 119786 130567 := bstep (se 1 (by rfl) ⟨97925, by rfl⟩ : syracuseStep 130567 = 195851) B195851
theorem B327179 : Blo 119786 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B229385 : Blo 119786 229385 := bstep (se 2 (by rfl) ⟨86019, by rfl⟩ : syracuseStep 229385 = 172039) B172039
theorem B458905 : Blo 119786 458905 := bstep (se 2 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 458905 = 344179) B344179
theorem B262543 : Blo 119786 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B459209 : Blo 119786 459209 := bstep (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) B344407
theorem B393943 : Blo 119786 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B1541015 : Blo 119786 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B459695 : Blo 119786 459695 := bstep (se 1 (by rfl) ⟨344771, by rfl⟩ : syracuseStep 459695 = 689543) B689543
theorem B230843 : Blo 119786 230843 := bstep (se 1 (by rfl) ⟨173132, by rfl⟩ : syracuseStep 230843 = 346265) B346265
theorem B787913 : Blo 119786 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B493037 : Blo 119786 493037 := bstep (se 3 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 493037 = 184889) B184889
theorem B624167 : Blo 119786 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B231275 : Blo 119786 231275 := bstep (se 1 (by rfl) ⟨173456, by rfl⟩ : syracuseStep 231275 = 346913) B346913
theorem B231329 : Blo 119786 231329 := bstep (se 2 (by rfl) ⟨86748, by rfl⟩ : syracuseStep 231329 = 173497) B173497
theorem B329807 : Blo 119786 329807 := bstep (se 1 (by rfl) ⟨247355, by rfl⟩ : syracuseStep 329807 = 494711) B494711
theorem B166249 : Blo 119786 166249 := bstep (se 2 (by rfl) ⟨62343, by rfl⟩ : syracuseStep 166249 = 124687) B124687
theorem B5966257 : Blo 119786 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B788939 : Blo 119786 788939 := bstep (se 1 (by rfl) ⟨591704, by rfl⟩ : syracuseStep 788939 = 1183409) B1183409
theorem B461321 : Blo 119786 461321 := bstep (se 2 (by rfl) ⟨172995, by rfl⟩ : syracuseStep 461321 = 345991) B345991
theorem B592643 : Blo 119786 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B625481 : Blo 119786 625481 := bstep (se 2 (by rfl) ⟨234555, by rfl⟩ : syracuseStep 625481 = 469111) B469111
theorem B232969 : Blo 119786 232969 := bstep (se 2 (by rfl) ⟨87363, by rfl⟩ : syracuseStep 232969 = 174727) B174727
theorem B134779 : Blo 119786 134779 := bstep (se 1 (by rfl) ⟨101084, by rfl⟩ : syracuseStep 134779 = 202169) B202169
theorem B1314593 : Blo 119786 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B462779 : Blo 119786 462779 := bstep (se 1 (by rfl) ⟨347084, by rfl⟩ : syracuseStep 462779 = 694169) B694169
theorem B135247 : Blo 119786 135247 := bstep (se 1 (by rfl) ⟨101435, by rfl⟩ : syracuseStep 135247 = 202871) B202871
theorem B2101565 : Blo 119786 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B1773899 : Blo 119786 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B233903 : Blo 119786 233903 := bstep (se 1 (by rfl) ⟨175427, by rfl⟩ : syracuseStep 233903 = 350855) B350855
theorem B135643 : Blo 119786 135643 := bstep (se 1 (by rfl) ⟨101732, by rfl⟩ : syracuseStep 135643 = 203465) B203465
theorem B136111 : Blo 119786 136111 := bstep (se 1 (by rfl) ⟨102083, by rfl⟩ : syracuseStep 136111 = 204167) B204167
theorem B889775 : Blo 119786 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B398267 : Blo 119786 398267 := bstep (se 1 (by rfl) ⟨298700, by rfl⟩ : syracuseStep 398267 = 597401) B597401
theorem B234427 : Blo 119786 234427 := bstep (se 1 (by rfl) ⟨175820, by rfl⟩ : syracuseStep 234427 = 351641) B351641
theorem B791603 : Blo 119786 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B791831 : Blo 119786 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B136543 : Blo 119786 136543 := bstep (se 1 (by rfl) ⟨102407, by rfl⟩ : syracuseStep 136543 = 204815) B204815
theorem B595343 : Blo 119786 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B234913 : Blo 119786 234913 := bstep (se 2 (by rfl) ⟨88092, by rfl⟩ : syracuseStep 234913 = 176185) B176185
theorem B2299355 : Blo 119786 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B202297 : Blo 119786 202297 := bstep (se 2 (by rfl) ⟨75861, by rfl⟩ : syracuseStep 202297 = 151723) B151723
theorem B202439 : Blo 119786 202439 := bstep (se 1 (by rfl) ⟨151829, by rfl⟩ : syracuseStep 202439 = 303659) B303659
theorem B136903 : Blo 119786 136903 := bstep (se 1 (by rfl) ⟨102677, by rfl⟩ : syracuseStep 136903 = 205355) B205355
theorem B202601 : Blo 119786 202601 := bstep (se 2 (by rfl) ⟨75975, by rfl⟩ : syracuseStep 202601 = 151951) B151951
theorem B465011 : Blo 119786 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B202999 : Blo 119786 202999 := bstep (se 1 (by rfl) ⟨152249, by rfl⟩ : syracuseStep 202999 = 304499) B304499
theorem B203195 : Blo 119786 203195 := bstep (se 1 (by rfl) ⟨152396, by rfl⟩ : syracuseStep 203195 = 304793) B304793
theorem B203303 : Blo 119786 203303 := bstep (se 1 (by rfl) ⟨152477, by rfl⟩ : syracuseStep 203303 = 304955) B304955
theorem B137767 : Blo 119786 137767 := bstep (se 1 (by rfl) ⟨103325, by rfl⟩ : syracuseStep 137767 = 206651) B206651
theorem B694919 : Blo 119786 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B924371 : Blo 119786 924371 := bstep (se 1 (by rfl) ⟨693278, by rfl⟩ : syracuseStep 924371 = 1386557) B1386557
theorem B203593 : Blo 119786 203593 := bstep (se 2 (by rfl) ⟨76347, by rfl⟩ : syracuseStep 203593 = 152695) B152695
theorem B203627 : Blo 119786 203627 := bstep (se 1 (by rfl) ⟨152720, by rfl⟩ : syracuseStep 203627 = 305441) B305441
theorem B695375 : Blo 119786 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B597071 : Blo 119786 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B204025 : Blo 119786 204025 := bstep (se 2 (by rfl) ⟨76509, by rfl⟩ : syracuseStep 204025 = 153019) B153019
theorem B269711 : Blo 119786 269711 := bstep (se 1 (by rfl) ⟨202283, by rfl⟩ : syracuseStep 269711 = 404567) B404567
theorem B204295 : Blo 119786 204295 := bstep (se 1 (by rfl) ⟨153221, by rfl⟩ : syracuseStep 204295 = 306443) B306443
theorem B270035 : Blo 119786 270035 := bstep (se 1 (by rfl) ⟨202526, by rfl⟩ : syracuseStep 270035 = 405053) B405053
theorem B466681 : Blo 119786 466681 := bstep (se 2 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 466681 = 350011) B350011
theorem B204727 : Blo 119786 204727 := bstep (se 1 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 204727 = 307091) B307091
theorem B696377 : Blo 119786 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B204923 : Blo 119786 204923 := bstep (se 1 (by rfl) ⟨153692, by rfl⟩ : syracuseStep 204923 = 307385) B307385
theorem B631145 : Blo 119786 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B205321 : Blo 119786 205321 := bstep (se 2 (by rfl) ⟨76995, by rfl⟩ : syracuseStep 205321 = 153991) B153991
theorem B1188361 : Blo 119786 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B270971 : Blo 119786 270971 := bstep (se 1 (by rfl) ⟨203228, by rfl⟩ : syracuseStep 270971 = 406457) B406457
theorem B205483 : Blo 119786 205483 := bstep (se 1 (by rfl) ⟨154112, by rfl⟩ : syracuseStep 205483 = 308225) B308225
theorem B271097 : Blo 119786 271097 := bstep (se 2 (by rfl) ⟨101661, by rfl⟩ : syracuseStep 271097 = 203323) B203323
theorem B467819 : Blo 119786 467819 := bstep (se 1 (by rfl) ⟨350864, by rfl⟩ : syracuseStep 467819 = 701729) B701729
theorem B304033 : Blo 119786 304033 := bstep (se 2 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 304033 = 228025) B228025
theorem B205787 : Blo 119786 205787 := bstep (se 1 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 205787 = 308681) B308681
theorem B271367 : Blo 119786 271367 := bstep (se 1 (by rfl) ⟨203525, by rfl⟩ : syracuseStep 271367 = 407051) B407051
theorem B435257 : Blo 119786 435257 := bstep (se 2 (by rfl) ⟨163221, by rfl⟩ : syracuseStep 435257 = 326443) B326443
theorem B271439 : Blo 119786 271439 := bstep (se 1 (by rfl) ⟨203579, by rfl⟩ : syracuseStep 271439 = 407159) B407159
theorem B468125 : Blo 119786 468125 := bstep (se 3 (by rfl) ⟨87773, by rfl⟩ : syracuseStep 468125 = 175547) B175547
theorem B468139 : Blo 119786 468139 := bstep (se 1 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 468139 = 702209) B702209
theorem B206023 : Blo 119786 206023 := bstep (se 1 (by rfl) ⟨154517, by rfl⟩ : syracuseStep 206023 = 309035) B309035
theorem B206185 : Blo 119786 206185 := bstep (se 2 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 206185 = 154639) B154639
theorem B271835 : Blo 119786 271835 := bstep (se 1 (by rfl) ⟨203876, by rfl⟩ : syracuseStep 271835 = 407753) B407753
theorem B468443 : Blo 119786 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B468679 : Blo 119786 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B140999 : Blo 119786 140999 := bstep (se 1 (by rfl) ⟨105749, by rfl⟩ : syracuseStep 140999 = 211499) B211499
theorem B1582841 : Blo 119786 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B272303 : Blo 119786 272303 := bstep (se 1 (by rfl) ⟨204227, by rfl⟩ : syracuseStep 272303 = 408455) B408455
theorem B894905 : Blo 119786 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B206779 : Blo 119786 206779 := bstep (se 1 (by rfl) ⟨155084, by rfl⟩ : syracuseStep 206779 = 310169) B310169
theorem B174089 : Blo 119786 174089 := bstep (se 2 (by rfl) ⟨65283, by rfl⟩ : syracuseStep 174089 = 130567) B130567
theorem B927773 : Blo 119786 927773 := bstep (se 3 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 927773 = 347915) B347915
theorem B206887 : Blo 119786 206887 := bstep (se 1 (by rfl) ⟨155165, by rfl⟩ : syracuseStep 206887 = 310331) B310331
theorem B272555 : Blo 119786 272555 := bstep (se 1 (by rfl) ⟨204416, by rfl⟩ : syracuseStep 272555 = 408833) B408833
theorem B207211 : Blo 119786 207211 := bstep (se 1 (by rfl) ⟨155408, by rfl⟩ : syracuseStep 207211 = 310817) B310817
theorem B371069 : Blo 119786 371069 := bstep (se 3 (by rfl) ⟨69575, by rfl⟩ : syracuseStep 371069 = 139151) B139151
theorem B1026593 : Blo 119786 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B273095 : Blo 119786 273095 := bstep (se 1 (by rfl) ⟨204821, by rfl⟩ : syracuseStep 273095 = 409643) B409643
theorem B404297 : Blo 119786 404297 := bstep (se 2 (by rfl) ⟨151611, by rfl⟩ : syracuseStep 404297 = 303223) B303223
theorem B174955 : Blo 119786 174955 := bstep (se 1 (by rfl) ⟨131216, by rfl⟩ : syracuseStep 174955 = 262433) B262433
theorem B994355 : Blo 119786 994355 := bstep (se 1 (by rfl) ⟨745766, by rfl⟩ : syracuseStep 994355 = 1491533) B1491533
theorem B928921 : Blo 119786 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B306575 : Blo 119786 306575 := bstep (se 1 (by rfl) ⟨229931, by rfl⟩ : syracuseStep 306575 = 459863) B459863
theorem B208271 : Blo 119786 208271 := bstep (se 1 (by rfl) ⟨156203, by rfl⟩ : syracuseStep 208271 = 312407) B312407
theorem B1748405 : Blo 119786 1748405 := bstep (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) B163913
theorem B273959 : Blo 119786 273959 := bstep (se 1 (by rfl) ⟨205469, by rfl⟩ : syracuseStep 273959 = 410939) B410939
theorem B175655 : Blo 119786 175655 := bstep (se 1 (by rfl) ⟨131741, by rfl⟩ : syracuseStep 175655 = 263483) B263483
theorem B700001 : Blo 119786 700001 := bstep (se 2 (by rfl) ⟨262500, by rfl⟩ : syracuseStep 700001 = 525001) B525001
theorem B208507 : Blo 119786 208507 := bstep (se 1 (by rfl) ⟨156380, by rfl⟩ : syracuseStep 208507 = 312761) B312761
theorem B306899 : Blo 119786 306899 := bstep (se 1 (by rfl) ⟨230174, by rfl⟩ : syracuseStep 306899 = 460349) B460349
theorem B208631 : Blo 119786 208631 := bstep (se 1 (by rfl) ⟨156473, by rfl⟩ : syracuseStep 208631 = 312947) B312947
theorem B274283 : Blo 119786 274283 := bstep (se 1 (by rfl) ⟨205712, by rfl⟩ : syracuseStep 274283 = 411425) B411425
theorem B274337 : Blo 119786 274337 := bstep (se 2 (by rfl) ⟨102876, by rfl⟩ : syracuseStep 274337 = 205753) B205753
theorem B405431 : Blo 119786 405431 := bstep (se 1 (by rfl) ⟨304073, by rfl⟩ : syracuseStep 405431 = 608147) B608147
theorem B569501 : Blo 119786 569501 := bstep (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) B213563
theorem B1585331 : Blo 119786 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B274679 : Blo 119786 274679 := bstep (se 1 (by rfl) ⟨206009, by rfl⟩ : syracuseStep 274679 = 412019) B412019
theorem B799105 : Blo 119786 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B406025 : Blo 119786 406025 := bstep (se 2 (by rfl) ⟨152259, by rfl⟩ : syracuseStep 406025 = 304519) B304519
theorem B9679621 : Blo 119786 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B897821 : Blo 119786 897821 := bstep (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) B336683
theorem B275273 : Blo 119786 275273 := bstep (se 2 (by rfl) ⟨103227, by rfl⟩ : syracuseStep 275273 = 206455) B206455
theorem B308063 : Blo 119786 308063 := bstep (se 1 (by rfl) ⟨231047, by rfl⟩ : syracuseStep 308063 = 462095) B462095
theorem B701459 : Blo 119786 701459 := bstep (se 1 (by rfl) ⟨526094, by rfl⟩ : syracuseStep 701459 = 1052189) B1052189
theorem B406889 : Blo 119786 406889 := bstep (se 2 (by rfl) ⟨152583, by rfl⟩ : syracuseStep 406889 = 305167) B305167
theorem B1324451 : Blo 119786 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B2209265 : Blo 119786 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B341491 : Blo 119786 341491 := bstep (se 1 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 341491 = 512237) B512237
theorem B2635253 : Blo 119786 2635253 := bstep (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) B247055
theorem B276065 : Blo 119786 276065 := bstep (se 2 (by rfl) ⟨103524, by rfl⟩ : syracuseStep 276065 = 207049) B207049
theorem B341833 : Blo 119786 341833 := bstep (se 2 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 341833 = 256375) B256375
theorem B309167 : Blo 119786 309167 := bstep (se 1 (by rfl) ⟨231875, by rfl⟩ : syracuseStep 309167 = 463751) B463751
theorem B276407 : Blo 119786 276407 := bstep (se 1 (by rfl) ⟨207305, by rfl⟩ : syracuseStep 276407 = 414611) B414611
theorem B407483 : Blo 119786 407483 := bstep (se 1 (by rfl) ⟨305612, by rfl⟩ : syracuseStep 407483 = 611225) B611225
theorem B1784045 : Blo 119786 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B932147 : Blo 119786 932147 := bstep (se 1 (by rfl) ⟨699110, by rfl⟩ : syracuseStep 932147 = 1398221) B1398221
theorem B26589505 : Blo 119786 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B277001 : Blo 119786 277001 := bstep (se 2 (by rfl) ⟨103875, by rfl⟩ : syracuseStep 277001 = 207751) B207751
theorem B277343 : Blo 119786 277343 := bstep (se 1 (by rfl) ⟨208007, by rfl⟩ : syracuseStep 277343 = 416015) B416015
theorem B441197 : Blo 119786 441197 := bstep (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) B165449
theorem B277523 : Blo 119786 277523 := bstep (se 1 (by rfl) ⟨208142, by rfl⟩ : syracuseStep 277523 = 416285) B416285
theorem B310351 : Blo 119786 310351 := bstep (se 1 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 310351 = 465527) B465527
theorem B441611 : Blo 119786 441611 := bstep (se 1 (by rfl) ⟨331208, by rfl⟩ : syracuseStep 441611 = 662417) B662417
theorem B277865 : Blo 119786 277865 := bstep (se 2 (by rfl) ⟨104199, by rfl⟩ : syracuseStep 277865 = 208399) B208399
theorem B409211 : Blo 119786 409211 := bstep (se 1 (by rfl) ⟨306908, by rfl⟩ : syracuseStep 409211 = 613817) B613817
theorem B704123 : Blo 119786 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B1982141 : Blo 119786 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B310999 : Blo 119786 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B409373 : Blo 119786 409373 := bstep (se 3 (by rfl) ⟨76757, by rfl⟩ : syracuseStep 409373 = 153515) B153515
theorem B868205 : Blo 119786 868205 := bstep (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) B325577
theorem B704375 : Blo 119786 704375 := bstep (se 1 (by rfl) ⟨528281, by rfl⟩ : syracuseStep 704375 = 1056563) B1056563
theorem B180143 : Blo 119786 180143 := bstep (se 1 (by rfl) ⟨135107, by rfl⟩ : syracuseStep 180143 = 270215) B270215
theorem B278459 : Blo 119786 278459 := bstep (se 1 (by rfl) ⟨208844, by rfl⟩ : syracuseStep 278459 = 417689) B417689
theorem B999377 : Blo 119786 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B311303 : Blo 119786 311303 := bstep (se 1 (by rfl) ⟨233477, by rfl⟩ : syracuseStep 311303 = 466955) B466955
theorem B180233 : Blo 119786 180233 := bstep (se 2 (by rfl) ⟨67587, by rfl⟩ : syracuseStep 180233 = 135175) B135175
theorem B180263 : Blo 119786 180263 := bstep (se 1 (by rfl) ⟨135197, by rfl⟩ : syracuseStep 180263 = 270395) B270395
theorem B180347 : Blo 119786 180347 := bstep (se 1 (by rfl) ⟨135260, by rfl⟩ : syracuseStep 180347 = 270521) B270521
theorem B1097891 : Blo 119786 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B1851569 : Blo 119786 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B180473 : Blo 119786 180473 := bstep (se 2 (by rfl) ⟨67677, by rfl⟩ : syracuseStep 180473 = 135355) B135355
theorem B180575 : Blo 119786 180575 := bstep (se 1 (by rfl) ⟨135431, by rfl⟩ : syracuseStep 180575 = 270863) B270863
theorem B180587 : Blo 119786 180587 := bstep (se 1 (by rfl) ⟨135440, by rfl⟩ : syracuseStep 180587 = 270881) B270881
theorem B147895 : Blo 119786 147895 := bstep (se 1 (by rfl) ⟨110921, by rfl⟩ : syracuseStep 147895 = 221843) B221843
theorem B410075 : Blo 119786 410075 := bstep (se 1 (by rfl) ⟨307556, by rfl⟩ : syracuseStep 410075 = 615113) B615113
theorem B180815 : Blo 119786 180815 := bstep (se 1 (by rfl) ⟨135611, by rfl⟩ : syracuseStep 180815 = 271223) B271223
theorem B180935 : Blo 119786 180935 := bstep (se 1 (by rfl) ⟨135701, by rfl⟩ : syracuseStep 180935 = 271403) B271403
theorem B1327889 : Blo 119786 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B181097 : Blo 119786 181097 := bstep (se 2 (by rfl) ⟨67911, by rfl⟩ : syracuseStep 181097 = 135823) B135823
theorem B443243 : Blo 119786 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B181175 : Blo 119786 181175 := bstep (se 1 (by rfl) ⟨135881, by rfl⟩ : syracuseStep 181175 = 271763) B271763
theorem B181211 : Blo 119786 181211 := bstep (se 1 (by rfl) ⟨135908, by rfl⟩ : syracuseStep 181211 = 271817) B271817
theorem B410777 : Blo 119786 410777 := bstep (se 2 (by rfl) ⟨154041, by rfl⟩ : syracuseStep 410777 = 308083) B308083
theorem B607661 : Blo 119786 607661 := bstep (se 3 (by rfl) ⟨113936, by rfl⟩ : syracuseStep 607661 = 227873) B227873
theorem B181679 : Blo 119786 181679 := bstep (se 1 (by rfl) ⟨136259, by rfl⟩ : syracuseStep 181679 = 272519) B272519
theorem B181769 : Blo 119786 181769 := bstep (se 2 (by rfl) ⟨68163, by rfl⟩ : syracuseStep 181769 = 136327) B136327
theorem B181799 : Blo 119786 181799 := bstep (se 1 (by rfl) ⟨136349, by rfl⟩ : syracuseStep 181799 = 272699) B272699
theorem B181883 : Blo 119786 181883 := bstep (se 1 (by rfl) ⟨136412, by rfl⟩ : syracuseStep 181883 = 272825) B272825
theorem B182009 : Blo 119786 182009 := bstep (se 2 (by rfl) ⟨68253, by rfl⟩ : syracuseStep 182009 = 136507) B136507
theorem B182111 : Blo 119786 182111 := bstep (se 1 (by rfl) ⟨136583, by rfl⟩ : syracuseStep 182111 = 273167) B273167
theorem B182123 : Blo 119786 182123 := bstep (se 1 (by rfl) ⟨136592, by rfl⟩ : syracuseStep 182123 = 273185) B273185
theorem B182351 : Blo 119786 182351 := bstep (se 1 (by rfl) ⟨136763, by rfl⟩ : syracuseStep 182351 = 273527) B273527
theorem B1984601 : Blo 119786 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B772253 : Blo 119786 772253 := bstep (se 3 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 772253 = 289595) B289595
theorem B182471 : Blo 119786 182471 := bstep (se 1 (by rfl) ⟨136853, by rfl⟩ : syracuseStep 182471 = 273707) B273707
theorem B411965 : Blo 119786 411965 := bstep (se 3 (by rfl) ⟨77243, by rfl⟩ : syracuseStep 411965 = 154487) B154487
theorem B182633 : Blo 119786 182633 := bstep (se 2 (by rfl) ⟨68487, by rfl⟩ : syracuseStep 182633 = 136975) B136975
theorem B1296773 : Blo 119786 1296773 := bstep (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) B243145
theorem B182711 : Blo 119786 182711 := bstep (se 1 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 182711 = 274067) B274067
theorem B182747 : Blo 119786 182747 := bstep (se 1 (by rfl) ⟨137060, by rfl⟩ : syracuseStep 182747 = 274121) B274121
theorem B183215 : Blo 119786 183215 := bstep (se 1 (by rfl) ⟨137411, by rfl⟩ : syracuseStep 183215 = 274823) B274823
theorem B609281 : Blo 119786 609281 := bstep (se 2 (by rfl) ⟨228480, by rfl⟩ : syracuseStep 609281 = 456961) B456961
theorem B183305 : Blo 119786 183305 := bstep (se 2 (by rfl) ⟨68739, by rfl⟩ : syracuseStep 183305 = 137479) B137479
theorem B183335 : Blo 119786 183335 := bstep (se 1 (by rfl) ⟨137501, by rfl⟩ : syracuseStep 183335 = 275003) B275003
theorem B183419 : Blo 119786 183419 := bstep (se 1 (by rfl) ⟨137564, by rfl⟩ : syracuseStep 183419 = 275129) B275129
theorem B412829 : Blo 119786 412829 := bstep (se 3 (by rfl) ⟨77405, by rfl⟩ : syracuseStep 412829 = 154811) B154811
theorem B183545 : Blo 119786 183545 := bstep (se 2 (by rfl) ⟨68829, by rfl⟩ : syracuseStep 183545 = 137659) B137659
theorem B183647 : Blo 119786 183647 := bstep (se 1 (by rfl) ⟨137735, by rfl⟩ : syracuseStep 183647 = 275471) B275471
theorem B183659 : Blo 119786 183659 := bstep (se 1 (by rfl) ⟨137744, by rfl⟩ : syracuseStep 183659 = 275489) B275489
theorem B183887 : Blo 119786 183887 := bstep (se 1 (by rfl) ⟨137915, by rfl⟩ : syracuseStep 183887 = 275831) B275831
theorem B413369 : Blo 119786 413369 := bstep (se 2 (by rfl) ⟨155013, by rfl⟩ : syracuseStep 413369 = 310027) B310027
theorem B184007 : Blo 119786 184007 := bstep (se 1 (by rfl) ⟨138005, by rfl⟩ : syracuseStep 184007 = 276011) B276011
theorem B610091 : Blo 119786 610091 := bstep (se 1 (by rfl) ⟨457568, by rfl⟩ : syracuseStep 610091 = 915137) B915137
theorem B347977 : Blo 119786 347977 := bstep (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) B260983
theorem B184169 : Blo 119786 184169 := bstep (se 2 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 184169 = 138127) B138127
theorem B184247 : Blo 119786 184247 := bstep (se 1 (by rfl) ⟨138185, by rfl⟩ : syracuseStep 184247 = 276371) B276371
theorem B184283 : Blo 119786 184283 := bstep (se 1 (by rfl) ⟨138212, by rfl⟩ : syracuseStep 184283 = 276425) B276425
theorem B872477 : Blo 119786 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B413963 : Blo 119786 413963 := bstep (se 1 (by rfl) ⟨310472, by rfl⟩ : syracuseStep 413963 = 620945) B620945
theorem B184751 : Blo 119786 184751 := bstep (se 1 (by rfl) ⟨138563, by rfl⟩ : syracuseStep 184751 = 277127) B277127
theorem B184841 : Blo 119786 184841 := bstep (se 2 (by rfl) ⟨69315, by rfl⟩ : syracuseStep 184841 = 138631) B138631
theorem B414233 : Blo 119786 414233 := bstep (se 2 (by rfl) ⟨155337, by rfl⟩ : syracuseStep 414233 = 310675) B310675
theorem B184871 : Blo 119786 184871 := bstep (se 1 (by rfl) ⟨138653, by rfl⟩ : syracuseStep 184871 = 277307) B277307
theorem B184955 : Blo 119786 184955 := bstep (se 1 (by rfl) ⟨138716, by rfl⟩ : syracuseStep 184955 = 277433) B277433
theorem B774791 : Blo 119786 774791 := bstep (se 1 (by rfl) ⟨581093, by rfl⟩ : syracuseStep 774791 = 1162187) B1162187
theorem B185081 : Blo 119786 185081 := bstep (se 2 (by rfl) ⟨69405, by rfl⟩ : syracuseStep 185081 = 138811) B138811
theorem B185183 : Blo 119786 185183 := bstep (se 1 (by rfl) ⟨138887, by rfl⟩ : syracuseStep 185183 = 277775) B277775
theorem B185195 : Blo 119786 185195 := bstep (se 1 (by rfl) ⟨138896, by rfl⟩ : syracuseStep 185195 = 277793) B277793
theorem B119847 : Blo 119786 119847 := bstep (se 1 (by rfl) ⟨89885, by rfl⟩ : syracuseStep 119847 = 179771) B179771
theorem B1168451 : Blo 119786 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B119887 : Blo 119786 119887 := bstep (se 1 (by rfl) ⟨89915, by rfl⟩ : syracuseStep 119887 = 179831) B179831
theorem B185423 : Blo 119786 185423 := bstep (se 1 (by rfl) ⟨139067, by rfl⟩ : syracuseStep 185423 = 278135) B278135
theorem B119903 : Blo 119786 119903 := bstep (se 1 (by rfl) ⟨89927, by rfl⟩ : syracuseStep 119903 = 179855) B179855
theorem B119931 : Blo 119786 119931 := bstep (se 1 (by rfl) ⟨89948, by rfl⟩ : syracuseStep 119931 = 179897) B179897
theorem B119983 : Blo 119786 119983 := bstep (se 1 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 119983 = 179975) B179975
theorem B120007 : Blo 119786 120007 := bstep (se 1 (by rfl) ⟨90005, by rfl⟩ : syracuseStep 120007 = 180011) B180011
theorem B185543 : Blo 119786 185543 := bstep (se 1 (by rfl) ⟨139157, by rfl⟩ : syracuseStep 185543 = 278315) B278315
theorem B120027 : Blo 119786 120027 := bstep (se 1 (by rfl) ⟨90020, by rfl⟩ : syracuseStep 120027 = 180041) B180041
theorem B120103 : Blo 119786 120103 := bstep (se 1 (by rfl) ⟨90077, by rfl⟩ : syracuseStep 120103 = 180155) B180155
theorem B120143 : Blo 119786 120143 := bstep (se 1 (by rfl) ⟨90107, by rfl⟩ : syracuseStep 120143 = 180215) B180215
theorem B120159 : Blo 119786 120159 := bstep (se 1 (by rfl) ⟨90119, by rfl⟩ : syracuseStep 120159 = 180239) B180239
theorem B120187 : Blo 119786 120187 := bstep (se 1 (by rfl) ⟨90140, by rfl⟩ : syracuseStep 120187 = 180281) B180281
theorem B1037731 : Blo 119786 1037731 := bstep (se 1 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 1037731 = 1556597) B1556597
theorem B939437 : Blo 119786 939437 := bstep (se 3 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 939437 = 352289) B352289
theorem B120239 : Blo 119786 120239 := bstep (se 1 (by rfl) ⟨90179, by rfl⟩ : syracuseStep 120239 = 180359) B180359
theorem B120263 : Blo 119786 120263 := bstep (se 1 (by rfl) ⟨90197, by rfl⟩ : syracuseStep 120263 = 180395) B180395
theorem B120283 : Blo 119786 120283 := bstep (se 1 (by rfl) ⟨90212, by rfl⟩ : syracuseStep 120283 = 180425) B180425
theorem B120359 : Blo 119786 120359 := bstep (se 1 (by rfl) ⟨90269, by rfl⟩ : syracuseStep 120359 = 180539) B180539
theorem B3200573 : Blo 119786 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B120399 : Blo 119786 120399 := bstep (se 1 (by rfl) ⟨90299, by rfl⟩ : syracuseStep 120399 = 180599) B180599
theorem B120415 : Blo 119786 120415 := bstep (se 1 (by rfl) ⟨90311, by rfl⟩ : syracuseStep 120415 = 180623) B180623
theorem B120443 : Blo 119786 120443 := bstep (se 1 (by rfl) ⟨90332, by rfl⟩ : syracuseStep 120443 = 180665) B180665
theorem B415367 : Blo 119786 415367 := bstep (se 1 (by rfl) ⟨311525, by rfl⟩ : syracuseStep 415367 = 623051) B623051
theorem B120495 : Blo 119786 120495 := bstep (se 1 (by rfl) ⟨90371, by rfl⟩ : syracuseStep 120495 = 180743) B180743
theorem B415421 : Blo 119786 415421 := bstep (se 3 (by rfl) ⟨77891, by rfl⟩ : syracuseStep 415421 = 155783) B155783
theorem B120519 : Blo 119786 120519 := bstep (se 1 (by rfl) ⟨90389, by rfl⟩ : syracuseStep 120519 = 180779) B180779
theorem B120539 : Blo 119786 120539 := bstep (se 1 (by rfl) ⟨90404, by rfl⟩ : syracuseStep 120539 = 180809) B180809
theorem B120615 : Blo 119786 120615 := bstep (se 1 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 120615 = 180923) B180923
theorem B120655 : Blo 119786 120655 := bstep (se 1 (by rfl) ⟨90491, by rfl⟩ : syracuseStep 120655 = 180983) B180983
theorem B120671 : Blo 119786 120671 := bstep (se 1 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 120671 = 181007) B181007
theorem B415583 : Blo 119786 415583 := bstep (se 1 (by rfl) ⟨311687, by rfl⟩ : syracuseStep 415583 = 623375) B623375
theorem B120699 : Blo 119786 120699 := bstep (se 1 (by rfl) ⟨90524, by rfl⟩ : syracuseStep 120699 = 181049) B181049
theorem B120751 : Blo 119786 120751 := bstep (se 1 (by rfl) ⟨90563, by rfl⟩ : syracuseStep 120751 = 181127) B181127
theorem B186295 : Blo 119786 186295 := bstep (se 1 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 186295 = 279443) B279443
theorem B120775 : Blo 119786 120775 := bstep (se 1 (by rfl) ⟨90581, by rfl⟩ : syracuseStep 120775 = 181163) B181163
theorem B120795 : Blo 119786 120795 := bstep (se 1 (by rfl) ⟨90596, by rfl⟩ : syracuseStep 120795 = 181193) B181193
theorem B415745 : Blo 119786 415745 := bstep (se 2 (by rfl) ⟨155904, by rfl⟩ : syracuseStep 415745 = 311809) B311809
theorem B612359 : Blo 119786 612359 := bstep (se 1 (by rfl) ⟨459269, by rfl⟩ : syracuseStep 612359 = 918539) B918539
theorem B710693 : Blo 119786 710693 := bstep (se 4 (by rfl) ⟨66627, by rfl⟩ : syracuseStep 710693 = 133255) B133255
theorem B120871 : Blo 119786 120871 := bstep (se 1 (by rfl) ⟨90653, by rfl⟩ : syracuseStep 120871 = 181307) B181307
theorem B776249 : Blo 119786 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B120911 : Blo 119786 120911 := bstep (se 1 (by rfl) ⟨90683, by rfl⟩ : syracuseStep 120911 = 181367) B181367
theorem B120927 : Blo 119786 120927 := bstep (se 1 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 120927 = 181391) B181391
theorem B120955 : Blo 119786 120955 := bstep (se 1 (by rfl) ⟨90716, by rfl⟩ : syracuseStep 120955 = 181433) B181433
theorem B350365 : Blo 119786 350365 := bstep (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) B131387
theorem B121007 : Blo 119786 121007 := bstep (se 1 (by rfl) ⟨90755, by rfl⟩ : syracuseStep 121007 = 181511) B181511
theorem B121031 : Blo 119786 121031 := bstep (se 1 (by rfl) ⟨90773, by rfl⟩ : syracuseStep 121031 = 181547) B181547
theorem B121051 : Blo 119786 121051 := bstep (se 1 (by rfl) ⟨90788, by rfl⟩ : syracuseStep 121051 = 181577) B181577
theorem B121127 : Blo 119786 121127 := bstep (se 1 (by rfl) ⟨90845, by rfl⟩ : syracuseStep 121127 = 181691) B181691
theorem B121167 : Blo 119786 121167 := bstep (se 1 (by rfl) ⟨90875, by rfl⟩ : syracuseStep 121167 = 181751) B181751
theorem B121183 : Blo 119786 121183 := bstep (se 1 (by rfl) ⟨90887, by rfl⟩ : syracuseStep 121183 = 181775) B181775
theorem B121211 : Blo 119786 121211 := bstep (se 1 (by rfl) ⟨90908, by rfl⟩ : syracuseStep 121211 = 181817) B181817
theorem B121263 : Blo 119786 121263 := bstep (se 1 (by rfl) ⟨90947, by rfl⟩ : syracuseStep 121263 = 181895) B181895
theorem B121287 : Blo 119786 121287 := bstep (se 1 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 121287 = 181931) B181931
theorem B4446667 : Blo 119786 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B121307 : Blo 119786 121307 := bstep (se 1 (by rfl) ⟨90980, by rfl⟩ : syracuseStep 121307 = 181961) B181961
theorem B612845 : Blo 119786 612845 := bstep (se 3 (by rfl) ⟨114908, by rfl⟩ : syracuseStep 612845 = 229817) B229817
theorem B121383 : Blo 119786 121383 := bstep (se 1 (by rfl) ⟨91037, by rfl⟩ : syracuseStep 121383 = 182075) B182075
theorem B121423 : Blo 119786 121423 := bstep (se 1 (by rfl) ⟨91067, by rfl⟩ : syracuseStep 121423 = 182135) B182135
theorem B121439 : Blo 119786 121439 := bstep (se 1 (by rfl) ⟨91079, by rfl⟩ : syracuseStep 121439 = 182159) B182159
theorem B121467 : Blo 119786 121467 := bstep (se 1 (by rfl) ⟨91100, by rfl⟩ : syracuseStep 121467 = 182201) B182201
theorem B121519 : Blo 119786 121519 := bstep (se 1 (by rfl) ⟨91139, by rfl⟩ : syracuseStep 121519 = 182279) B182279
theorem B121543 : Blo 119786 121543 := bstep (se 1 (by rfl) ⟨91157, by rfl⟩ : syracuseStep 121543 = 182315) B182315
theorem B121563 : Blo 119786 121563 := bstep (se 1 (by rfl) ⟨91172, by rfl⟩ : syracuseStep 121563 = 182345) B182345
theorem B121639 : Blo 119786 121639 := bstep (se 1 (by rfl) ⟨91229, by rfl⟩ : syracuseStep 121639 = 182459) B182459
theorem B416555 : Blo 119786 416555 := bstep (se 1 (by rfl) ⟨312416, by rfl⟩ : syracuseStep 416555 = 624833) B624833
theorem B121679 : Blo 119786 121679 := bstep (se 1 (by rfl) ⟨91259, by rfl⟩ : syracuseStep 121679 = 182519) B182519
theorem B121695 : Blo 119786 121695 := bstep (se 1 (by rfl) ⟨91271, by rfl⟩ : syracuseStep 121695 = 182543) B182543
theorem B121723 : Blo 119786 121723 := bstep (se 1 (by rfl) ⟨91292, by rfl⟩ : syracuseStep 121723 = 182585) B182585
theorem B121775 : Blo 119786 121775 := bstep (se 1 (by rfl) ⟨91331, by rfl⟩ : syracuseStep 121775 = 182663) B182663
theorem B154543 : Blo 119786 154543 := bstep (se 1 (by rfl) ⟨115907, by rfl⟩ : syracuseStep 154543 = 231815) B231815
theorem B121799 : Blo 119786 121799 := bstep (se 1 (by rfl) ⟨91349, by rfl⟩ : syracuseStep 121799 = 182699) B182699
theorem B121819 : Blo 119786 121819 := bstep (se 1 (by rfl) ⟨91364, by rfl⟩ : syracuseStep 121819 = 182729) B182729
theorem B121895 : Blo 119786 121895 := bstep (se 1 (by rfl) ⟨91421, by rfl⟩ : syracuseStep 121895 = 182843) B182843
theorem B416825 : Blo 119786 416825 := bstep (se 2 (by rfl) ⟨156309, by rfl⟩ : syracuseStep 416825 = 312619) B312619
theorem B121935 : Blo 119786 121935 := bstep (se 1 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 121935 = 182903) B182903
theorem B121951 : Blo 119786 121951 := bstep (se 1 (by rfl) ⟨91463, by rfl⟩ : syracuseStep 121951 = 182927) B182927
theorem B384115 : Blo 119786 384115 := bstep (se 1 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 384115 = 576173) B576173
theorem B121979 : Blo 119786 121979 := bstep (se 1 (by rfl) ⟨91484, by rfl⟩ : syracuseStep 121979 = 182969) B182969
theorem B122031 : Blo 119786 122031 := bstep (se 1 (by rfl) ⟨91523, by rfl⟩ : syracuseStep 122031 = 183047) B183047
theorem B122055 : Blo 119786 122055 := bstep (se 1 (by rfl) ⟨91541, by rfl⟩ : syracuseStep 122055 = 183083) B183083
theorem B122075 : Blo 119786 122075 := bstep (se 1 (by rfl) ⟨91556, by rfl⟩ : syracuseStep 122075 = 183113) B183113
theorem B613655 : Blo 119786 613655 := bstep (se 1 (by rfl) ⟨460241, by rfl⟩ : syracuseStep 613655 = 920483) B920483
theorem B122151 : Blo 119786 122151 := bstep (se 1 (by rfl) ⟨91613, by rfl⟩ : syracuseStep 122151 = 183227) B183227
theorem B122191 : Blo 119786 122191 := bstep (se 1 (by rfl) ⟨91643, by rfl⟩ : syracuseStep 122191 = 183287) B183287
theorem B122207 : Blo 119786 122207 := bstep (se 1 (by rfl) ⟨91655, by rfl⟩ : syracuseStep 122207 = 183311) B183311
theorem B122235 : Blo 119786 122235 := bstep (se 1 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 122235 = 183353) B183353
theorem B417149 : Blo 119786 417149 := bstep (se 3 (by rfl) ⟨78215, by rfl⟩ : syracuseStep 417149 = 156431) B156431
theorem B122287 : Blo 119786 122287 := bstep (se 1 (by rfl) ⟨91715, by rfl⟩ : syracuseStep 122287 = 183431) B183431
theorem B122311 : Blo 119786 122311 := bstep (se 1 (by rfl) ⟨91733, by rfl⟩ : syracuseStep 122311 = 183467) B183467
theorem B122331 : Blo 119786 122331 := bstep (se 1 (by rfl) ⟨91748, by rfl⟩ : syracuseStep 122331 = 183497) B183497
theorem B122407 : Blo 119786 122407 := bstep (se 1 (by rfl) ⟨91805, by rfl⟩ : syracuseStep 122407 = 183611) B183611
theorem B122447 : Blo 119786 122447 := bstep (se 1 (by rfl) ⟨91835, by rfl⟩ : syracuseStep 122447 = 183671) B183671
theorem B122463 : Blo 119786 122463 := bstep (se 1 (by rfl) ⟨91847, by rfl⟩ : syracuseStep 122463 = 183695) B183695
theorem B122491 : Blo 119786 122491 := bstep (se 1 (by rfl) ⟨91868, by rfl⟩ : syracuseStep 122491 = 183737) B183737
theorem B417419 : Blo 119786 417419 := bstep (se 1 (by rfl) ⟨313064, by rfl⟩ : syracuseStep 417419 = 626129) B626129
theorem B122543 : Blo 119786 122543 := bstep (se 1 (by rfl) ⟨91907, by rfl⟩ : syracuseStep 122543 = 183815) B183815
theorem B122567 : Blo 119786 122567 := bstep (se 1 (by rfl) ⟨91925, by rfl⟩ : syracuseStep 122567 = 183851) B183851
theorem B122587 : Blo 119786 122587 := bstep (se 1 (by rfl) ⟨91940, by rfl⟩ : syracuseStep 122587 = 183881) B183881
theorem B122663 : Blo 119786 122663 := bstep (se 1 (by rfl) ⟨91997, by rfl⟩ : syracuseStep 122663 = 183995) B183995
theorem B122703 : Blo 119786 122703 := bstep (se 1 (by rfl) ⟨92027, by rfl⟩ : syracuseStep 122703 = 184055) B184055
theorem B122719 : Blo 119786 122719 := bstep (se 1 (by rfl) ⟨92039, by rfl⟩ : syracuseStep 122719 = 184079) B184079
theorem B319339 : Blo 119786 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B122747 : Blo 119786 122747 := bstep (se 1 (by rfl) ⟨92060, by rfl⟩ : syracuseStep 122747 = 184121) B184121
theorem B221089 : Blo 119786 221089 := bstep (se 2 (by rfl) ⟨82908, by rfl⟩ : syracuseStep 221089 = 165817) B165817
theorem B122799 : Blo 119786 122799 := bstep (se 1 (by rfl) ⟨92099, by rfl⟩ : syracuseStep 122799 = 184199) B184199
theorem B122823 : Blo 119786 122823 := bstep (se 1 (by rfl) ⟨92117, by rfl⟩ : syracuseStep 122823 = 184235) B184235
theorem B122843 : Blo 119786 122843 := bstep (se 1 (by rfl) ⟨92132, by rfl⟩ : syracuseStep 122843 = 184265) B184265
theorem B155611 : Blo 119786 155611 := bstep (se 1 (by rfl) ⟨116708, by rfl⟩ : syracuseStep 155611 = 233417) B233417
theorem B417793 : Blo 119786 417793 := bstep (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) B313345
theorem B122919 : Blo 119786 122919 := bstep (se 1 (by rfl) ⟨92189, by rfl⟩ : syracuseStep 122919 = 184379) B184379
theorem B352313 : Blo 119786 352313 := bstep (se 2 (by rfl) ⟨132117, by rfl⟩ : syracuseStep 352313 = 264235) B264235
theorem B122959 : Blo 119786 122959 := bstep (se 1 (by rfl) ⟨92219, by rfl⟩ : syracuseStep 122959 = 184439) B184439
theorem B1040465 : Blo 119786 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B122975 : Blo 119786 122975 := bstep (se 1 (by rfl) ⟨92231, by rfl⟩ : syracuseStep 122975 = 184463) B184463
theorem B123003 : Blo 119786 123003 := bstep (se 1 (by rfl) ⟨92252, by rfl⟩ : syracuseStep 123003 = 184505) B184505
theorem B516253 : Blo 119786 516253 := bstep (se 3 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 516253 = 193595) B193595
theorem B123055 : Blo 119786 123055 := bstep (se 1 (by rfl) ⟨92291, by rfl⟩ : syracuseStep 123055 = 184583) B184583
theorem B123079 : Blo 119786 123079 := bstep (se 1 (by rfl) ⟨92309, by rfl⟩ : syracuseStep 123079 = 184619) B184619
theorem B123099 : Blo 119786 123099 := bstep (se 1 (by rfl) ⟨92324, by rfl⟩ : syracuseStep 123099 = 184649) B184649
theorem B123175 : Blo 119786 123175 := bstep (se 1 (by rfl) ⟨92381, by rfl⟩ : syracuseStep 123175 = 184763) B184763
theorem B123215 : Blo 119786 123215 := bstep (se 1 (by rfl) ⟨92411, by rfl⟩ : syracuseStep 123215 = 184823) B184823
theorem B123231 : Blo 119786 123231 := bstep (se 1 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 123231 = 184847) B184847
theorem B123259 : Blo 119786 123259 := bstep (se 1 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 123259 = 184889) B184889
theorem B123311 : Blo 119786 123311 := bstep (se 1 (by rfl) ⟨92483, by rfl⟩ : syracuseStep 123311 = 184967) B184967
theorem B123335 : Blo 119786 123335 := bstep (se 1 (by rfl) ⟨92501, by rfl⟩ : syracuseStep 123335 = 185003) B185003
theorem B123355 : Blo 119786 123355 := bstep (se 1 (by rfl) ⟨92516, by rfl⟩ : syracuseStep 123355 = 185033) B185033
theorem B123431 : Blo 119786 123431 := bstep (se 1 (by rfl) ⟨92573, by rfl⟩ : syracuseStep 123431 = 185147) B185147
theorem B123471 : Blo 119786 123471 := bstep (se 1 (by rfl) ⟨92603, by rfl⟩ : syracuseStep 123471 = 185207) B185207
theorem B123487 : Blo 119786 123487 := bstep (se 1 (by rfl) ⟨92615, by rfl⟩ : syracuseStep 123487 = 185231) B185231
theorem B123515 : Blo 119786 123515 := bstep (se 1 (by rfl) ⟨92636, by rfl⟩ : syracuseStep 123515 = 185273) B185273
theorem B221867 : Blo 119786 221867 := bstep (se 1 (by rfl) ⟨166400, by rfl⟩ : syracuseStep 221867 = 332801) B332801
theorem B1172141 : Blo 119786 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B123567 : Blo 119786 123567 := bstep (se 1 (by rfl) ⟨92675, by rfl⟩ : syracuseStep 123567 = 185351) B185351
theorem B123591 : Blo 119786 123591 := bstep (se 1 (by rfl) ⟨92693, by rfl⟩ : syracuseStep 123591 = 185387) B185387
theorem B123611 : Blo 119786 123611 := bstep (se 1 (by rfl) ⟨92708, by rfl⟩ : syracuseStep 123611 = 185417) B185417
theorem B123687 : Blo 119786 123687 := bstep (se 1 (by rfl) ⟨92765, by rfl⟩ : syracuseStep 123687 = 185531) B185531
theorem B123727 : Blo 119786 123727 := bstep (se 1 (by rfl) ⟨92795, by rfl⟩ : syracuseStep 123727 = 185591) B185591
theorem B123743 : Blo 119786 123743 := bstep (se 1 (by rfl) ⟨92807, by rfl⟩ : syracuseStep 123743 = 185615) B185615
theorem B615275 : Blo 119786 615275 := bstep (se 1 (by rfl) ⟨461456, by rfl⟩ : syracuseStep 615275 = 922913) B922913
theorem B123771 : Blo 119786 123771 := bstep (se 1 (by rfl) ⟨92828, by rfl⟩ : syracuseStep 123771 = 185657) B185657
theorem B615923 : Blo 119786 615923 := bstep (se 1 (by rfl) ⟨461942, by rfl⟩ : syracuseStep 615923 = 923885) B923885
theorem B223049 : Blo 119786 223049 := bstep (se 2 (by rfl) ⟨83643, by rfl⟩ : syracuseStep 223049 = 167287) B167287
theorem B1763167 : Blo 119786 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B649079 : Blo 119786 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B288787 : Blo 119786 288787 := bstep (se 1 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 288787 = 433181) B433181
theorem B1108025 : Blo 119786 1108025 := bstep (se 2 (by rfl) ⟨415509, by rfl⟩ : syracuseStep 1108025 = 831019) B831019
theorem B387433 : Blo 119786 387433 := bstep (se 2 (by rfl) ⟨145287, by rfl⟩ : syracuseStep 387433 = 290575) B290575
theorem B1370519 : Blo 119786 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B682505 : Blo 119786 682505 := bstep (se 2 (by rfl) ⟨255939, by rfl⟩ : syracuseStep 682505 = 511879) B511879
theorem B879277 : Blo 119786 879277 := bstep (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) B329729
theorem B3893953 : Blo 119786 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B617219 : Blo 119786 617219 := bstep (se 1 (by rfl) ⟨462914, by rfl⟩ : syracuseStep 617219 = 925829) B925829
theorem B977999 : Blo 119786 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B388253 : Blo 119786 388253 := bstep (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) B145595
theorem B257195 : Blo 119786 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B683255 : Blo 119786 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B683437 : Blo 119786 683437 := bstep (se 3 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 683437 = 256289) B256289
theorem B2289239 : Blo 119786 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B683963 : Blo 119786 683963 := bstep (se 1 (by rfl) ⟨512972, by rfl⟩ : syracuseStep 683963 = 1025945) B1025945
theorem B618839 : Blo 119786 618839 := bstep (se 1 (by rfl) ⟨464129, by rfl⟩ : syracuseStep 618839 = 928259) B928259
theorem B455017 : Blo 119786 455017 := bstep (se 2 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 455017 = 341263) B341263
theorem B455291 : Blo 119786 455291 := bstep (se 1 (by rfl) ⟨341468, by rfl⟩ : syracuseStep 455291 = 682937) B682937
theorem B193499 : Blo 119786 193499 := bstep (se 1 (by rfl) ⟨145124, by rfl⟩ : syracuseStep 193499 = 290249) B290249
theorem B422927 : Blo 119786 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B3536369 : Blo 119786 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B325309 : Blo 119786 325309 := bstep (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) B121991
theorem B423623 : Blo 119786 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B751427 : Blo 119786 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B194447 : Blo 119786 194447 := bstep (se 1 (by rfl) ⟨145835, by rfl⟩ : syracuseStep 194447 = 291671) B291671
theorem B194491 : Blo 119786 194491 := bstep (se 1 (by rfl) ⟨145868, by rfl⟩ : syracuseStep 194491 = 291737) B291737
theorem B227539 : Blo 119786 227539 := bstep (se 1 (by rfl) ⟨170654, by rfl⟩ : syracuseStep 227539 = 341309) B341309
theorem B653579 : Blo 119786 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B522557 : Blo 119786 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B522625 : Blo 119786 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B227767 : Blo 119786 227767 := bstep (se 1 (by rfl) ⟨170825, by rfl⟩ : syracuseStep 227767 = 341651) B341651
theorem B1309229 : Blo 119786 1309229 := bstep (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) B490961
theorem B948995 : Blo 119786 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B392111 : Blo 119786 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B392123 : Blo 119786 392123 := bstep (se 1 (by rfl) ⟨294092, by rfl⟩ : syracuseStep 392123 = 588185) B588185
theorem B228359 : Blo 119786 228359 := bstep (se 1 (by rfl) ⟨171269, by rfl⟩ : syracuseStep 228359 = 342539) B342539
theorem B588953 : Blo 119786 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B3538565 : Blo 119786 3538565 := bstep (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) B663481
theorem B622403 : Blo 119786 622403 := bstep (se 1 (by rfl) ⟨466802, by rfl⟩ : syracuseStep 622403 = 933605) B933605
theorem B229225 : Blo 119786 229225 := bstep (se 2 (by rfl) ⟨85959, by rfl⟩ : syracuseStep 229225 = 171919) B171919
theorem B557057 : Blo 119786 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B688337 : Blo 119786 688337 := bstep (se 2 (by rfl) ⟨258126, by rfl⟩ : syracuseStep 688337 = 516253) B516253
theorem B885259 : Blo 119786 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B295495 : Blo 119786 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B5604173 : Blo 119786 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B525257 : Blo 119786 525257 := bstep (se 2 (by rfl) ⟨196971, by rfl⟩ : syracuseStep 525257 = 393943) B393943
theorem B525275 : Blo 119786 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B328691 : Blo 119786 328691 := bstep (se 1 (by rfl) ⟨246518, by rfl⟩ : syracuseStep 328691 = 493037) B493037
theorem B624185 : Blo 119786 624185 := bstep (se 2 (by rfl) ⟨234069, by rfl⟩ : syracuseStep 624185 = 468139) B468139
theorem B525959 : Blo 119786 525959 := bstep (se 1 (by rfl) ⟨394469, by rfl⟩ : syracuseStep 525959 = 788939) B788939
theorem B624905 : Blo 119786 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B788773 : Blo 119786 788773 := bstep (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) B147895
theorem B1182599 : Blo 119786 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B593183 : Blo 119786 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B265511 : Blo 119786 265511 := bstep (se 1 (by rfl) ⟨199133, by rfl⟩ : syracuseStep 265511 = 398267) B398267
theorem B527735 : Blo 119786 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B527887 : Blo 119786 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B396895 : Blo 119786 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B626291 : Blo 119786 626291 := bstep (se 1 (by rfl) ⟨469718, by rfl⟩ : syracuseStep 626291 = 939437) B939437
theorem B2133715 : Blo 119786 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B134959 : Blo 119786 134959 := bstep (se 1 (by rfl) ⟨101219, by rfl⟩ : syracuseStep 134959 = 202439) B202439
theorem B233273 : Blo 119786 233273 := bstep (se 2 (by rfl) ⟨87477, by rfl⟩ : syracuseStep 233273 = 174955) B174955
theorem B135067 : Blo 119786 135067 := bstep (se 1 (by rfl) ⟨101300, by rfl⟩ : syracuseStep 135067 = 202601) B202601
theorem B135463 : Blo 119786 135463 := bstep (se 1 (by rfl) ⟨101597, by rfl⟩ : syracuseStep 135463 = 203195) B203195
theorem B135535 : Blo 119786 135535 := bstep (se 1 (by rfl) ⟨101651, by rfl⟩ : syracuseStep 135535 = 203303) B203303
theorem B463279 : Blo 119786 463279 := bstep (se 1 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 463279 = 694919) B694919
theorem B135751 : Blo 119786 135751 := bstep (se 1 (by rfl) ⟨101813, by rfl⟩ : syracuseStep 135751 = 203627) B203627
theorem B463583 : Blo 119786 463583 := bstep (se 1 (by rfl) ⟨347687, by rfl⟩ : syracuseStep 463583 = 695375) B695375
theorem B398047 : Blo 119786 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B463969 : Blo 119786 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B464237 : Blo 119786 464237 := bstep (se 3 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 464237 = 174089) B174089
theorem B464251 : Blo 119786 464251 := bstep (se 1 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 464251 = 696377) B696377
theorem B234875 : Blo 119786 234875 := bstep (se 1 (by rfl) ⟨176156, by rfl⟩ : syracuseStep 234875 = 352313) B352313
theorem B693643 : Blo 119786 693643 := bstep (se 1 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 693643 = 1040465) B1040465
theorem B136615 : Blo 119786 136615 := bstep (se 1 (by rfl) ⟨102461, by rfl⟩ : syracuseStep 136615 = 204923) B204923
theorem B137191 : Blo 119786 137191 := bstep (se 1 (by rfl) ⟨102893, by rfl⟩ : syracuseStep 137191 = 205787) B205787
theorem B1055227 : Blo 119786 1055227 := bstep (se 1 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 1055227 = 1582841) B1582841
theorem B432719 : Blo 119786 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B596603 : Blo 119786 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B1383641 : Blo 119786 1383641 := bstep (se 2 (by rfl) ⟨518865, by rfl⟩ : syracuseStep 1383641 = 1037731) B1037731
theorem B269531 : Blo 119786 269531 := bstep (se 1 (by rfl) ⟨202148, by rfl⟩ : syracuseStep 269531 = 404297) B404297
theorem B1580381 : Blo 119786 1580381 := bstep (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) B592643
theorem B662903 : Blo 119786 662903 := bstep (se 1 (by rfl) ⟨497177, by rfl⟩ : syracuseStep 662903 = 994355) B994355
theorem B269729 : Blo 119786 269729 := bstep (se 2 (by rfl) ⟨101148, by rfl⟩ : syracuseStep 269729 = 202297) B202297
theorem B433745 : Blo 119786 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B204383 : Blo 119786 204383 := bstep (se 1 (by rfl) ⟨153287, by rfl⟩ : syracuseStep 204383 = 306575) B306575
theorem B138847 : Blo 119786 138847 := bstep (se 1 (by rfl) ⟨104135, by rfl⟩ : syracuseStep 138847 = 208271) B208271
theorem B466667 : Blo 119786 466667 := bstep (se 1 (by rfl) ⟨350000, by rfl⟩ : syracuseStep 466667 = 700001) B700001
theorem B204599 : Blo 119786 204599 := bstep (se 1 (by rfl) ⟨153449, by rfl⟩ : syracuseStep 204599 = 306899) B306899
theorem B139087 : Blo 119786 139087 := bstep (se 1 (by rfl) ⟨104315, by rfl⟩ : syracuseStep 139087 = 208631) B208631
theorem B270287 : Blo 119786 270287 := bstep (se 1 (by rfl) ⟨202715, by rfl⟩ : syracuseStep 270287 = 405431) B405431
theorem B1056887 : Blo 119786 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B467153 : Blo 119786 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B303385 : Blo 119786 303385 := bstep (se 2 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 303385 = 227539) B227539
theorem B270665 : Blo 119786 270665 := bstep (se 2 (by rfl) ⟨101499, by rfl⟩ : syracuseStep 270665 = 202999) B202999
theorem B270683 : Blo 119786 270683 := bstep (se 1 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 270683 = 406025) B406025
theorem B303527 : Blo 119786 303527 := bstep (se 1 (by rfl) ⟨227645, by rfl⟩ : syracuseStep 303527 = 455291) B455291
theorem B696833 : Blo 119786 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B598547 : Blo 119786 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B205375 : Blo 119786 205375 := bstep (se 1 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 205375 = 308063) B308063
theorem B303689 : Blo 119786 303689 := bstep (se 2 (by rfl) ⟨113883, by rfl⟩ : syracuseStep 303689 = 227767) B227767
theorem B467639 : Blo 119786 467639 := bstep (se 1 (by rfl) ⟨350729, by rfl⟩ : syracuseStep 467639 = 701459) B701459
theorem B271259 : Blo 119786 271259 := bstep (se 1 (by rfl) ⟨203444, by rfl⟩ : syracuseStep 271259 = 406889) B406889
theorem B271457 : Blo 119786 271457 := bstep (se 2 (by rfl) ⟨101796, by rfl⟩ : syracuseStep 271457 = 203593) B203593
theorem B500951 : Blo 119786 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B206057 : Blo 119786 206057 := bstep (se 2 (by rfl) ⟨77271, by rfl⟩ : syracuseStep 206057 = 154543) B154543
theorem B206111 : Blo 119786 206111 := bstep (se 1 (by rfl) ⟨154583, by rfl⟩ : syracuseStep 206111 = 309167) B309167
theorem B271655 : Blo 119786 271655 := bstep (se 1 (by rfl) ⟨203741, by rfl⟩ : syracuseStep 271655 = 407483) B407483
theorem B468413 : Blo 119786 468413 := bstep (se 3 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 468413 = 175655) B175655
theorem B1189363 : Blo 119786 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B435719 : Blo 119786 435719 := bstep (se 1 (by rfl) ⟨326789, by rfl⟩ : syracuseStep 435719 = 653579) B653579
theorem B272033 : Blo 119786 272033 := bstep (se 2 (by rfl) ⟨102012, by rfl⟩ : syracuseStep 272033 = 204025) B204025
theorem B632663 : Blo 119786 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B272393 : Blo 119786 272393 := bstep (se 2 (by rfl) ⟨102147, by rfl⟩ : syracuseStep 272393 = 204295) B204295
theorem B272807 : Blo 119786 272807 := bstep (se 1 (by rfl) ⟨204605, by rfl⟩ : syracuseStep 272807 = 409211) B409211
theorem B469415 : Blo 119786 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B1321427 : Blo 119786 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B305633 : Blo 119786 305633 := bstep (se 2 (by rfl) ⟨114612, by rfl⟩ : syracuseStep 305633 = 229225) B229225
theorem B272915 : Blo 119786 272915 := bstep (se 1 (by rfl) ⟨204686, by rfl⟩ : syracuseStep 272915 = 409373) B409373
theorem B272969 : Blo 119786 272969 := bstep (se 2 (by rfl) ⟨102363, by rfl⟩ : syracuseStep 272969 = 204727) B204727
theorem B469583 : Blo 119786 469583 := bstep (se 1 (by rfl) ⟨352187, by rfl⟩ : syracuseStep 469583 = 704375) B704375
theorem B207481 : Blo 119786 207481 := bstep (se 2 (by rfl) ⟨77805, by rfl⟩ : syracuseStep 207481 = 155611) B155611
theorem B666251 : Blo 119786 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B207535 : Blo 119786 207535 := bstep (se 1 (by rfl) ⟨155651, by rfl⟩ : syracuseStep 207535 = 311303) B311303
theorem B731927 : Blo 119786 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B306139 : Blo 119786 306139 := bstep (se 1 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 306139 = 459209) B459209
theorem B273383 : Blo 119786 273383 := bstep (se 1 (by rfl) ⟨205037, by rfl⟩ : syracuseStep 273383 = 410075) B410075
theorem B1027343 : Blo 119786 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B306463 : Blo 119786 306463 := bstep (se 1 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 306463 = 459695) B459695
theorem B273761 : Blo 119786 273761 := bstep (se 2 (by rfl) ⟨102660, by rfl⟩ : syracuseStep 273761 = 205321) B205321
theorem B1584481 : Blo 119786 1584481 := bstep (se 2 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 1584481 = 1188361) B1188361
theorem B273851 : Blo 119786 273851 := bstep (se 1 (by rfl) ⟨205388, by rfl⟩ : syracuseStep 273851 = 410777) B410777
theorem B273977 : Blo 119786 273977 := bstep (se 2 (by rfl) ⟨102741, by rfl⟩ : syracuseStep 273977 = 205483) B205483
theorem B405107 : Blo 119786 405107 := bstep (se 1 (by rfl) ⟨303830, by rfl⟩ : syracuseStep 405107 = 607661) B607661
theorem B405377 : Blo 119786 405377 := bstep (se 2 (by rfl) ⟨152016, by rfl⟩ : syracuseStep 405377 = 304033) B304033
theorem B1323067 : Blo 119786 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B274643 : Blo 119786 274643 := bstep (se 1 (by rfl) ⟨205982, by rfl⟩ : syracuseStep 274643 = 411965) B411965
theorem B864515 : Blo 119786 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B274697 : Blo 119786 274697 := bstep (se 2 (by rfl) ⟨103011, by rfl⟩ : syracuseStep 274697 = 206023) B206023
theorem B307547 : Blo 119786 307547 := bstep (se 1 (by rfl) ⟨230660, by rfl⟩ : syracuseStep 307547 = 461321) B461321
theorem B274913 : Blo 119786 274913 := bstep (se 2 (by rfl) ⟨103092, by rfl⟩ : syracuseStep 274913 = 206185) B206185
theorem B406187 : Blo 119786 406187 := bstep (se 1 (by rfl) ⟨304640, by rfl⟩ : syracuseStep 406187 = 609281) B609281
theorem B275219 : Blo 119786 275219 := bstep (se 1 (by rfl) ⟨206414, by rfl⟩ : syracuseStep 275219 = 412829) B412829
theorem B275579 : Blo 119786 275579 := bstep (se 1 (by rfl) ⟨206684, by rfl⟩ : syracuseStep 275579 = 413369) B413369
theorem B406727 : Blo 119786 406727 := bstep (se 1 (by rfl) ⟨305045, by rfl⟩ : syracuseStep 406727 = 610091) B610091
theorem B275705 : Blo 119786 275705 := bstep (se 2 (by rfl) ⟨103389, by rfl⟩ : syracuseStep 275705 = 206779) B206779
theorem B308519 : Blo 119786 308519 := bstep (se 1 (by rfl) ⟨231389, by rfl⟩ : syracuseStep 308519 = 462779) B462779
theorem B275849 : Blo 119786 275849 := bstep (se 2 (by rfl) ⟨103443, by rfl⟩ : syracuseStep 275849 = 206887) B206887
theorem B275975 : Blo 119786 275975 := bstep (se 1 (by rfl) ⟨206981, by rfl⟩ : syracuseStep 275975 = 413963) B413963
theorem B276155 : Blo 119786 276155 := bstep (se 1 (by rfl) ⟨207116, by rfl⟩ : syracuseStep 276155 = 414233) B414233
theorem B276281 : Blo 119786 276281 := bstep (se 2 (by rfl) ⟨103605, by rfl⟩ : syracuseStep 276281 = 207211) B207211
theorem B5191937 : Blo 119786 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B276911 : Blo 119786 276911 := bstep (se 1 (by rfl) ⟨207683, by rfl⟩ : syracuseStep 276911 = 415367) B415367
theorem B276947 : Blo 119786 276947 := bstep (se 1 (by rfl) ⟨207710, by rfl⟩ : syracuseStep 276947 = 415421) B415421
theorem B277055 : Blo 119786 277055 := bstep (se 1 (by rfl) ⟨207791, by rfl⟩ : syracuseStep 277055 = 415583) B415583
theorem B277163 : Blo 119786 277163 := bstep (se 1 (by rfl) ⟨207872, by rfl⟩ : syracuseStep 277163 = 415745) B415745
theorem B408239 : Blo 119786 408239 := bstep (se 1 (by rfl) ⟨306179, by rfl⟩ : syracuseStep 408239 = 612359) B612359
theorem B473795 : Blo 119786 473795 := bstep (se 1 (by rfl) ⟨355346, by rfl⟩ : syracuseStep 473795 = 710693) B710693
theorem B310007 : Blo 119786 310007 := bstep (se 1 (by rfl) ⟨232505, by rfl⟩ : syracuseStep 310007 = 465011) B465011
theorem B408563 : Blo 119786 408563 := bstep (se 1 (by rfl) ⟨306422, by rfl⟩ : syracuseStep 408563 = 612845) B612845
theorem B375997 : Blo 119786 375997 := bstep (se 3 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 375997 = 140999) B140999
theorem B277703 : Blo 119786 277703 := bstep (se 1 (by rfl) ⟨208277, by rfl⟩ : syracuseStep 277703 = 416555) B416555
theorem B310625 : Blo 119786 310625 := bstep (se 2 (by rfl) ⟨116484, by rfl⟩ : syracuseStep 310625 = 232969) B232969
theorem B277883 : Blo 119786 277883 := bstep (se 1 (by rfl) ⟨208412, by rfl⟩ : syracuseStep 277883 = 416825) B416825
theorem B179705 : Blo 119786 179705 := bstep (se 2 (by rfl) ⟨67389, by rfl⟩ : syracuseStep 179705 = 134779) B134779
theorem B278009 : Blo 119786 278009 := bstep (se 2 (by rfl) ⟨104253, by rfl⟩ : syracuseStep 278009 = 208507) B208507
theorem B409103 : Blo 119786 409103 := bstep (se 1 (by rfl) ⟨306827, by rfl⟩ : syracuseStep 409103 = 613655) B613655
theorem B278099 : Blo 119786 278099 := bstep (se 1 (by rfl) ⟨208574, by rfl⟩ : syracuseStep 278099 = 417149) B417149
theorem B179807 : Blo 119786 179807 := bstep (se 1 (by rfl) ⟨134855, by rfl⟩ : syracuseStep 179807 = 269711) B269711
theorem B278279 : Blo 119786 278279 := bstep (se 1 (by rfl) ⟨208709, by rfl⟩ : syracuseStep 278279 = 417419) B417419
theorem B180023 : Blo 119786 180023 := bstep (se 1 (by rfl) ⟨135017, by rfl⟩ : syracuseStep 180023 = 270035) B270035
theorem B180329 : Blo 119786 180329 := bstep (se 2 (by rfl) ⟨67623, by rfl⟩ : syracuseStep 180329 = 135247) B135247
theorem B180647 : Blo 119786 180647 := bstep (se 1 (by rfl) ⟨135485, by rfl⟩ : syracuseStep 180647 = 270971) B270971
theorem B147911 : Blo 119786 147911 := bstep (se 1 (by rfl) ⟨110933, by rfl⟩ : syracuseStep 147911 = 221867) B221867
theorem B606689 : Blo 119786 606689 := bstep (se 2 (by rfl) ⟨227508, by rfl⟩ : syracuseStep 606689 = 455017) B455017
theorem B180731 : Blo 119786 180731 := bstep (se 1 (by rfl) ⟨135548, by rfl⟩ : syracuseStep 180731 = 271097) B271097
theorem B1065473 : Blo 119786 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B410183 : Blo 119786 410183 := bstep (se 1 (by rfl) ⟨307637, by rfl⟩ : syracuseStep 410183 = 615275) B615275
theorem B311879 : Blo 119786 311879 := bstep (se 1 (by rfl) ⟨233909, by rfl⟩ : syracuseStep 311879 = 467819) B467819
theorem B180857 : Blo 119786 180857 := bstep (se 2 (by rfl) ⟨67821, by rfl⟩ : syracuseStep 180857 = 135643) B135643
theorem B180911 : Blo 119786 180911 := bstep (se 1 (by rfl) ⟨135683, by rfl⟩ : syracuseStep 180911 = 271367) B271367
theorem B180959 : Blo 119786 180959 := bstep (se 1 (by rfl) ⟨135719, by rfl⟩ : syracuseStep 180959 = 271439) B271439
theorem B312083 : Blo 119786 312083 := bstep (se 1 (by rfl) ⟨234062, by rfl⟩ : syracuseStep 312083 = 468125) B468125
theorem B181223 : Blo 119786 181223 := bstep (se 1 (by rfl) ⟨135917, by rfl⟩ : syracuseStep 181223 = 271835) B271835
theorem B312295 : Blo 119786 312295 := bstep (se 1 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 312295 = 468443) B468443
theorem B410615 : Blo 119786 410615 := bstep (se 1 (by rfl) ⟨307961, by rfl⟩ : syracuseStep 410615 = 615923) B615923
theorem B148699 : Blo 119786 148699 := bstep (se 1 (by rfl) ⟨111524, by rfl⟩ : syracuseStep 148699 = 223049) B223049
theorem B181481 : Blo 119786 181481 := bstep (se 2 (by rfl) ⟨68055, by rfl⟩ : syracuseStep 181481 = 136111) B136111
theorem B312569 : Blo 119786 312569 := bstep (se 2 (by rfl) ⟨117213, by rfl⟩ : syracuseStep 312569 = 234427) B234427
theorem B181535 : Blo 119786 181535 := bstep (se 1 (by rfl) ⟨136151, by rfl⟩ : syracuseStep 181535 = 272303) B272303
theorem B738683 : Blo 119786 738683 := bstep (se 1 (by rfl) ⟨554012, by rfl⟩ : syracuseStep 738683 = 1108025) B1108025
theorem B181703 : Blo 119786 181703 := bstep (se 1 (by rfl) ⟨136277, by rfl⟩ : syracuseStep 181703 = 272555) B272555
theorem B247379 : Blo 119786 247379 := bstep (se 1 (by rfl) ⟨185534, by rfl⟩ : syracuseStep 247379 = 371069) B371069
theorem B182057 : Blo 119786 182057 := bstep (se 2 (by rfl) ⟨68271, by rfl⟩ : syracuseStep 182057 = 136543) B136543
theorem B182063 : Blo 119786 182063 := bstep (se 1 (by rfl) ⟨136547, by rfl⟩ : syracuseStep 182063 = 273095) B273095
theorem B411479 : Blo 119786 411479 := bstep (se 1 (by rfl) ⟨308609, by rfl⟩ : syracuseStep 411479 = 617219) B617219
theorem B313217 : Blo 119786 313217 := bstep (se 2 (by rfl) ⟨117456, by rfl⟩ : syracuseStep 313217 = 234913) B234913
theorem B182537 : Blo 119786 182537 := bstep (se 2 (by rfl) ⟨68451, by rfl⟩ : syracuseStep 182537 = 136903) B136903
theorem B1165603 : Blo 119786 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B182639 : Blo 119786 182639 := bstep (se 1 (by rfl) ⟨136979, by rfl⟩ : syracuseStep 182639 = 273959) B273959
theorem B1526159 : Blo 119786 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B182855 : Blo 119786 182855 := bstep (se 1 (by rfl) ⟨137141, by rfl⟩ : syracuseStep 182855 = 274283) B274283
theorem B248393 : Blo 119786 248393 := bstep (se 2 (by rfl) ⟨93147, by rfl⟩ : syracuseStep 248393 = 186295) B186295
theorem B182891 : Blo 119786 182891 := bstep (se 1 (by rfl) ⟨137168, by rfl⟩ : syracuseStep 182891 = 274337) B274337
theorem B608957 : Blo 119786 608957 := bstep (se 3 (by rfl) ⟨114179, by rfl⟩ : syracuseStep 608957 = 228359) B228359
theorem B379667 : Blo 119786 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B183119 : Blo 119786 183119 := bstep (se 1 (by rfl) ⟨137339, by rfl⟩ : syracuseStep 183119 = 274679) B274679
theorem B2607997 : Blo 119786 2607997 := bstep (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) B977999
theorem B412559 : Blo 119786 412559 := bstep (se 1 (by rfl) ⟨309419, by rfl⟩ : syracuseStep 412559 = 618839) B618839
theorem B1035341 : Blo 119786 1035341 := bstep (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) B388253
theorem B183515 : Blo 119786 183515 := bstep (se 1 (by rfl) ⟨137636, by rfl⟩ : syracuseStep 183515 = 275273) B275273
theorem B281951 : Blo 119786 281951 := bstep (se 1 (by rfl) ⟨211463, by rfl⟩ : syracuseStep 281951 = 422927) B422927
theorem B183689 : Blo 119786 183689 := bstep (se 2 (by rfl) ⟨68883, by rfl⟩ : syracuseStep 183689 = 137767) B137767
theorem B1756835 : Blo 119786 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B184043 : Blo 119786 184043 := bstep (se 1 (by rfl) ⟨138032, by rfl⟩ : syracuseStep 184043 = 276065) B276065
theorem B282415 : Blo 119786 282415 := bstep (se 1 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 282415 = 423623) B423623
theorem B184271 : Blo 119786 184271 := bstep (se 1 (by rfl) ⟨138203, by rfl⟩ : syracuseStep 184271 = 276407) B276407
theorem B413801 : Blo 119786 413801 := bstep (se 2 (by rfl) ⟨155175, by rfl⟩ : syracuseStep 413801 = 310351) B310351
theorem B512153 : Blo 119786 512153 := bstep (se 2 (by rfl) ⟨192057, by rfl⟩ : syracuseStep 512153 = 384115) B384115
theorem B348371 : Blo 119786 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B184667 : Blo 119786 184667 := bstep (se 1 (by rfl) ⟨138500, by rfl⟩ : syracuseStep 184667 = 277001) B277001
theorem B872819 : Blo 119786 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B184895 : Blo 119786 184895 := bstep (se 1 (by rfl) ⟨138671, by rfl⟩ : syracuseStep 184895 = 277343) B277343
theorem B185015 : Blo 119786 185015 := bstep (se 1 (by rfl) ⟨138761, by rfl⟩ : syracuseStep 185015 = 277523) B277523
theorem B185243 : Blo 119786 185243 := bstep (se 1 (by rfl) ⟨138932, by rfl⟩ : syracuseStep 185243 = 277865) B277865
theorem B414665 : Blo 119786 414665 := bstep (se 2 (by rfl) ⟨155499, by rfl⟩ : syracuseStep 414665 = 310999) B310999
theorem B2315213 : Blo 119786 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B414935 : Blo 119786 414935 := bstep (se 1 (by rfl) ⟨311201, by rfl⟩ : syracuseStep 414935 = 622403) B622403
theorem B120095 : Blo 119786 120095 := bstep (se 1 (by rfl) ⟨90071, by rfl⟩ : syracuseStep 120095 = 180143) B180143
theorem B185639 : Blo 119786 185639 := bstep (se 1 (by rfl) ⟨139229, by rfl⟩ : syracuseStep 185639 = 278459) B278459
theorem B120155 : Blo 119786 120155 := bstep (se 1 (by rfl) ⟨90116, by rfl⟩ : syracuseStep 120155 = 180233) B180233
theorem B152923 : Blo 119786 152923 := bstep (se 1 (by rfl) ⟨114692, by rfl⟩ : syracuseStep 152923 = 229385) B229385
theorem B120175 : Blo 119786 120175 := bstep (se 1 (by rfl) ⟨90131, by rfl⟩ : syracuseStep 120175 = 180263) B180263
theorem B120231 : Blo 119786 120231 := bstep (se 1 (by rfl) ⟨90173, by rfl⟩ : syracuseStep 120231 = 180347) B180347
theorem B1234379 : Blo 119786 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B120315 : Blo 119786 120315 := bstep (se 1 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 120315 = 180473) B180473
theorem B611873 : Blo 119786 611873 := bstep (se 2 (by rfl) ⟨229452, by rfl⟩ : syracuseStep 611873 = 458905) B458905
theorem B120383 : Blo 119786 120383 := bstep (se 1 (by rfl) ⟨90287, by rfl⟩ : syracuseStep 120383 = 180575) B180575
theorem B120391 : Blo 119786 120391 := bstep (se 1 (by rfl) ⟨90293, by rfl⟩ : syracuseStep 120391 = 180587) B180587
theorem B120543 : Blo 119786 120543 := bstep (se 1 (by rfl) ⟨90407, by rfl⟩ : syracuseStep 120543 = 180815) B180815
theorem B120623 : Blo 119786 120623 := bstep (se 1 (by rfl) ⟨90467, by rfl⟩ : syracuseStep 120623 = 180935) B180935
theorem B350057 : Blo 119786 350057 := bstep (se 2 (by rfl) ⟨131271, by rfl⟩ : syracuseStep 350057 = 262543) B262543
theorem B120731 : Blo 119786 120731 := bstep (se 1 (by rfl) ⟨90548, by rfl⟩ : syracuseStep 120731 = 181097) B181097
theorem B120783 : Blo 119786 120783 := bstep (se 1 (by rfl) ⟨90587, by rfl⟩ : syracuseStep 120783 = 181175) B181175
theorem B120807 : Blo 119786 120807 := bstep (se 1 (by rfl) ⟨90605, by rfl⟩ : syracuseStep 120807 = 181211) B181211
theorem B481261 : Blo 119786 481261 := bstep (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) B180473
theorem B121119 : Blo 119786 121119 := bstep (se 1 (by rfl) ⟨90839, by rfl⟩ : syracuseStep 121119 = 181679) B181679
theorem B153895 : Blo 119786 153895 := bstep (se 1 (by rfl) ⟨115421, by rfl⟩ : syracuseStep 153895 = 230843) B230843
theorem B121179 : Blo 119786 121179 := bstep (se 1 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 121179 = 181769) B181769
theorem B121199 : Blo 119786 121199 := bstep (se 1 (by rfl) ⟨90899, by rfl⟩ : syracuseStep 121199 = 181799) B181799
theorem B416111 : Blo 119786 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B121255 : Blo 119786 121255 := bstep (se 1 (by rfl) ⟨90941, by rfl⟩ : syracuseStep 121255 = 181883) B181883
theorem B121339 : Blo 119786 121339 := bstep (se 1 (by rfl) ⟨91004, by rfl⟩ : syracuseStep 121339 = 182009) B182009
theorem B121407 : Blo 119786 121407 := bstep (se 1 (by rfl) ⟨91055, by rfl⟩ : syracuseStep 121407 = 182111) B182111
theorem B121415 : Blo 119786 121415 := bstep (se 1 (by rfl) ⟨91061, by rfl⟩ : syracuseStep 121415 = 182123) B182123
theorem B154219 : Blo 119786 154219 := bstep (se 1 (by rfl) ⟨115664, by rfl⟩ : syracuseStep 154219 = 231329) B231329
theorem B121567 : Blo 119786 121567 := bstep (se 1 (by rfl) ⟨91175, by rfl⟩ : syracuseStep 121567 = 182351) B182351
theorem B219871 : Blo 119786 219871 := bstep (se 1 (by rfl) ⟨164903, by rfl⟩ : syracuseStep 219871 = 329807) B329807
theorem B514835 : Blo 119786 514835 := bstep (se 1 (by rfl) ⟨386126, by rfl⟩ : syracuseStep 514835 = 772253) B772253
theorem B121647 : Blo 119786 121647 := bstep (se 1 (by rfl) ⟨91235, by rfl⟩ : syracuseStep 121647 = 182471) B182471
theorem B121755 : Blo 119786 121755 := bstep (se 1 (by rfl) ⟨91316, by rfl⟩ : syracuseStep 121755 = 182633) B182633
theorem B121807 : Blo 119786 121807 := bstep (se 1 (by rfl) ⟨91355, by rfl⟩ : syracuseStep 121807 = 182711) B182711
theorem B121831 : Blo 119786 121831 := bstep (se 1 (by rfl) ⟨91373, by rfl⟩ : syracuseStep 121831 = 182747) B182747
theorem B416987 : Blo 119786 416987 := bstep (se 1 (by rfl) ⟨312740, by rfl⟩ : syracuseStep 416987 = 625481) B625481
theorem B122143 : Blo 119786 122143 := bstep (se 1 (by rfl) ⟨91607, by rfl⟩ : syracuseStep 122143 = 183215) B183215
theorem B122203 : Blo 119786 122203 := bstep (se 1 (by rfl) ⟨91652, by rfl⟩ : syracuseStep 122203 = 183305) B183305
theorem B122223 : Blo 119786 122223 := bstep (se 1 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 122223 = 183335) B183335
theorem B122279 : Blo 119786 122279 := bstep (se 1 (by rfl) ⟨91709, by rfl⟩ : syracuseStep 122279 = 183419) B183419
theorem B122363 : Blo 119786 122363 := bstep (se 1 (by rfl) ⟨91772, by rfl⟩ : syracuseStep 122363 = 183545) B183545
theorem B122431 : Blo 119786 122431 := bstep (se 1 (by rfl) ⟨91823, by rfl⟩ : syracuseStep 122431 = 183647) B183647
theorem B122439 : Blo 119786 122439 := bstep (se 1 (by rfl) ⟨91829, by rfl⟩ : syracuseStep 122439 = 183659) B183659
theorem B122591 : Blo 119786 122591 := bstep (se 1 (by rfl) ⟨91943, by rfl⟩ : syracuseStep 122591 = 183887) B183887
theorem B2350889 : Blo 119786 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B122671 : Blo 119786 122671 := bstep (se 1 (by rfl) ⟨92003, by rfl⟩ : syracuseStep 122671 = 184007) B184007
theorem B876395 : Blo 119786 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B122779 : Blo 119786 122779 := bstep (se 1 (by rfl) ⟨92084, by rfl⟩ : syracuseStep 122779 = 184169) B184169
theorem B122831 : Blo 119786 122831 := bstep (se 1 (by rfl) ⟨92123, by rfl⟩ : syracuseStep 122831 = 184247) B184247
theorem B122855 : Blo 119786 122855 := bstep (se 1 (by rfl) ⟨92141, by rfl⟩ : syracuseStep 122855 = 184283) B184283
theorem B581651 : Blo 119786 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B385049 : Blo 119786 385049 := bstep (se 2 (by rfl) ⟨144393, by rfl⟩ : syracuseStep 385049 = 288787) B288787
theorem B123167 : Blo 119786 123167 := bstep (se 1 (by rfl) ⟨92375, by rfl⟩ : syracuseStep 123167 = 184751) B184751
theorem B155935 : Blo 119786 155935 := bstep (se 1 (by rfl) ⟨116951, by rfl⟩ : syracuseStep 155935 = 233903) B233903
theorem B123227 : Blo 119786 123227 := bstep (se 1 (by rfl) ⟨92420, by rfl⟩ : syracuseStep 123227 = 184841) B184841
theorem B123247 : Blo 119786 123247 := bstep (se 1 (by rfl) ⟨92435, by rfl⟩ : syracuseStep 123247 = 184871) B184871
theorem B123303 : Blo 119786 123303 := bstep (se 1 (by rfl) ⟨92477, by rfl⟩ : syracuseStep 123303 = 184955) B184955
theorem B516527 : Blo 119786 516527 := bstep (se 1 (by rfl) ⟨387395, by rfl⟩ : syracuseStep 516527 = 774791) B774791
theorem B516577 : Blo 119786 516577 := bstep (se 2 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 516577 = 387433) B387433
theorem B221665 : Blo 119786 221665 := bstep (se 2 (by rfl) ⟨83124, by rfl⟩ : syracuseStep 221665 = 166249) B166249
theorem B123387 : Blo 119786 123387 := bstep (se 1 (by rfl) ⟨92540, by rfl⟩ : syracuseStep 123387 = 185081) B185081
theorem B123455 : Blo 119786 123455 := bstep (se 1 (by rfl) ⟨92591, by rfl⟩ : syracuseStep 123455 = 185183) B185183
theorem B7955009 : Blo 119786 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B123463 : Blo 119786 123463 := bstep (se 1 (by rfl) ⟨92597, by rfl⟩ : syracuseStep 123463 = 185195) B185195
theorem B778967 : Blo 119786 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B123615 : Blo 119786 123615 := bstep (se 1 (by rfl) ⟨92711, by rfl⟩ : syracuseStep 123615 = 185423) B185423
theorem B123695 : Blo 119786 123695 := bstep (se 1 (by rfl) ⟨92771, by rfl⟩ : syracuseStep 123695 = 185543) B185543
theorem B1172369 : Blo 119786 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B1532903 : Blo 119786 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B3531869 : Blo 119786 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B517499 : Blo 119786 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B1238561 : Blo 119786 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B616247 : Blo 119786 616247 := bstep (se 1 (by rfl) ⟨462185, by rfl⟩ : syracuseStep 616247 = 924371) B924371
theorem B911249 : Blo 119786 911249 := bstep (se 2 (by rfl) ⟨341718, by rfl⟩ : syracuseStep 911249 = 683437) B683437
theorem B616733 : Blo 119786 616733 := bstep (se 3 (by rfl) ⟨115637, by rfl⟩ : syracuseStep 616733 = 231275) B231275
theorem B518525 : Blo 119786 518525 := bstep (se 3 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 518525 = 194447) B194447
theorem B420763 : Blo 119786 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B781427 : Blo 119786 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B290171 : Blo 119786 290171 := bstep (se 1 (by rfl) ⟨217628, by rfl⟩ : syracuseStep 290171 = 435257) B435257
theorem B12906161 : Blo 119786 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B618515 : Blo 119786 618515 := bstep (se 1 (by rfl) ⟨463886, by rfl⟩ : syracuseStep 618515 = 927773) B927773
theorem B913679 : Blo 119786 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B455003 : Blo 119786 455003 := bstep (se 1 (by rfl) ⟨341252, by rfl⟩ : syracuseStep 455003 = 682505) B682505
theorem B684395 : Blo 119786 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B455321 : Blo 119786 455321 := bstep (se 2 (by rfl) ⟨170745, by rfl⟩ : syracuseStep 455321 = 341491) B341491
theorem B455503 : Blo 119786 455503 := bstep (se 1 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 455503 = 683255) B683255
theorem B455777 : Blo 119786 455777 := bstep (se 2 (by rfl) ⟨170916, by rfl⟩ : syracuseStep 455777 = 341833) B341833
theorem B259321 : Blo 119786 259321 := bstep (se 2 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 259321 = 194491) B194491
theorem B455975 : Blo 119786 455975 := bstep (se 1 (by rfl) ⟨341981, by rfl⟩ : syracuseStep 455975 = 683963) B683963
theorem B35452673 : Blo 119786 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B685853 : Blo 119786 685853 := bstep (se 3 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 685853 = 257195) B257195
theorem B5928889 : Blo 119786 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B128999 : Blo 119786 128999 := bstep (se 1 (by rfl) ⟨96749, by rfl⟩ : syracuseStep 128999 = 193499) B193499
theorem B2357579 : Blo 119786 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B1472843 : Blo 119786 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B621431 : Blo 119786 621431 := bstep (se 1 (by rfl) ⟨466073, by rfl⟩ : syracuseStep 621431 = 932147) B932147
theorem B294131 : Blo 119786 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B261407 : Blo 119786 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B261415 : Blo 119786 261415 := bstep (se 1 (by rfl) ⟨196061, by rfl⟩ : syracuseStep 261415 = 392123) B392123
theorem B392635 : Blo 119786 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B294407 : Blo 119786 294407 := bstep (se 1 (by rfl) ⟨220805, by rfl⟩ : syracuseStep 294407 = 441611) B441611
theorem B622241 : Blo 119786 622241 := bstep (se 2 (by rfl) ⟨233340, by rfl⟩ : syracuseStep 622241 = 466681) B466681
theorem B2359043 : Blo 119786 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B425785 : Blo 119786 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B294785 : Blo 119786 294785 := bstep (se 2 (by rfl) ⟨110544, by rfl⟩ : syracuseStep 294785 = 221089) B221089
theorem B458891 : Blo 119786 458891 := bstep (se 1 (by rfl) ⟨344168, by rfl⟩ : syracuseStep 458891 = 688337) B688337
theorem B3736115 : Blo 119786 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B688769 : Blo 119786 688769 := bstep (se 2 (by rfl) ⟨258288, by rfl⟩ : syracuseStep 688769 = 516577) B516577
theorem B295553 : Blo 119786 295553 := bstep (se 2 (by rfl) ⟨110832, by rfl⟩ : syracuseStep 295553 = 221665) B221665
theorem B1180345 : Blo 119786 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B492455 : Blo 119786 492455 := bstep (se 1 (by rfl) ⟨369341, by rfl⟩ : syracuseStep 492455 = 738683) B738683
theorem B788399 : Blo 119786 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B690227 : Blo 119786 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B395455 : Blo 119786 395455 := bstep (se 1 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 395455 = 593183) B593183
theorem B232247 : Blo 119786 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B1575973 : Blo 119786 1575973 := bstep (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) B295495
theorem B1051697 : Blo 119786 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B1543475 : Blo 119786 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B3477329 : Blo 119786 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B561017 : Blo 119786 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B233371 : Blo 119786 233371 := bstep (se 1 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 233371 = 350057) B350057
theorem B659677 : Blo 119786 659677 := bstep (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) B247379
theorem B397735 : Blo 119786 397735 := bstep (se 1 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 397735 = 596603) B596603
theorem B1577717 : Blo 119786 1577717 := bstep (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) B147911
theorem B529193 : Blo 119786 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B922427 : Blo 119786 922427 := bstep (se 1 (by rfl) ⟨691820, by rfl⟩ : syracuseStep 922427 = 1383641) B1383641
theorem B1053587 : Blo 119786 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B136255 : Blo 119786 136255 := bstep (se 1 (by rfl) ⟨102191, by rfl⟩ : syracuseStep 136255 = 204383) B204383
theorem B136399 : Blo 119786 136399 := bstep (se 1 (by rfl) ⟨102299, by rfl⟩ : syracuseStep 136399 = 204599) B204599
theorem B202351 : Blo 119786 202351 := bstep (se 1 (by rfl) ⟨151763, by rfl⟩ : syracuseStep 202351 = 303527) B303527
theorem B464555 : Blo 119786 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B202459 : Blo 119786 202459 := bstep (se 1 (by rfl) ⟨151844, by rfl⟩ : syracuseStep 202459 = 303689) B303689
theorem B137371 : Blo 119786 137371 := bstep (se 1 (by rfl) ⟨103028, by rfl⟩ : syracuseStep 137371 = 206057) B206057
theorem B137407 : Blo 119786 137407 := bstep (se 1 (by rfl) ⟨103055, by rfl⟩ : syracuseStep 137407 = 206111) B206111
theorem B530729 : Blo 119786 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B825707 : Blo 119786 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B4069757 : Blo 119786 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B793061 : Blo 119786 793061 := bstep (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) B148699
theorem B662381 : Blo 119786 662381 := bstep (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) B248393
theorem B203755 : Blo 119786 203755 := bstep (se 1 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 203755 = 305633) B305633
theorem B203897 : Blo 119786 203897 := bstep (se 2 (by rfl) ⟨76461, by rfl⟩ : syracuseStep 203897 = 152923) B152923
theorem B924857 : Blo 119786 924857 := bstep (se 2 (by rfl) ⟨346821, by rfl⟩ : syracuseStep 924857 = 693643) B693643
theorem B270071 : Blo 119786 270071 := bstep (se 1 (by rfl) ⟨202553, by rfl⟩ : syracuseStep 270071 = 405107) B405107
theorem B7905185 : Blo 119786 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B270251 : Blo 119786 270251 := bstep (se 1 (by rfl) ⟨202688, by rfl⟩ : syracuseStep 270251 = 405377) B405377
theorem B303335 : Blo 119786 303335 := bstep (se 1 (by rfl) ⟨227501, by rfl⟩ : syracuseStep 303335 = 455003) B455003
theorem B205031 : Blo 119786 205031 := bstep (se 1 (by rfl) ⟨153773, by rfl⟩ : syracuseStep 205031 = 307547) B307547
theorem B205193 : Blo 119786 205193 := bstep (se 2 (by rfl) ⟨76947, by rfl⟩ : syracuseStep 205193 = 153895) B153895
theorem B303547 : Blo 119786 303547 := bstep (se 1 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 303547 = 455321) B455321
theorem B270791 : Blo 119786 270791 := bstep (se 1 (by rfl) ⟨203093, by rfl⟩ : syracuseStep 270791 = 406187) B406187
theorem B303851 : Blo 119786 303851 := bstep (se 1 (by rfl) ⟨227888, by rfl⟩ : syracuseStep 303851 = 455777) B455777
theorem B697085 : Blo 119786 697085 := bstep (se 3 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 697085 = 261407) B261407
theorem B271151 : Blo 119786 271151 := bstep (se 1 (by rfl) ⟨203363, by rfl⟩ : syracuseStep 271151 = 406727) B406727
theorem B205625 : Blo 119786 205625 := bstep (se 2 (by rfl) ⟨77109, by rfl⟩ : syracuseStep 205625 = 154219) B154219
theorem B303983 : Blo 119786 303983 := bstep (se 1 (by rfl) ⟨227987, by rfl⟩ : syracuseStep 303983 = 455975) B455975
theorem B205679 : Blo 119786 205679 := bstep (se 1 (by rfl) ⟨154259, by rfl⟩ : syracuseStep 205679 = 308519) B308519
theorem B23635115 : Blo 119786 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B501329 : Blo 119786 501329 := bstep (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) B375997
theorem B272159 : Blo 119786 272159 := bstep (se 1 (by rfl) ⟨204119, by rfl⟩ : syracuseStep 272159 = 408239) B408239
theorem B206671 : Blo 119786 206671 := bstep (se 1 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 206671 = 310007) B310007
theorem B272375 : Blo 119786 272375 := bstep (se 1 (by rfl) ⟨204281, by rfl⟩ : syracuseStep 272375 = 408563) B408563
theorem B207083 : Blo 119786 207083 := bstep (se 1 (by rfl) ⟨155312, by rfl⟩ : syracuseStep 207083 = 310625) B310625
theorem B272735 : Blo 119786 272735 := bstep (se 1 (by rfl) ⟨204551, by rfl⟩ : syracuseStep 272735 = 409103) B409103
theorem B567713 : Blo 119786 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B1485485 : Blo 119786 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B404459 : Blo 119786 404459 := bstep (se 1 (by rfl) ⟨303344, by rfl⟩ : syracuseStep 404459 = 606689) B606689
theorem B404513 : Blo 119786 404513 := bstep (se 2 (by rfl) ⟨151692, by rfl⟩ : syracuseStep 404513 = 303385) B303385
theorem B207913 : Blo 119786 207913 := bstep (se 2 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 207913 = 155935) B155935
theorem B273455 : Blo 119786 273455 := bstep (se 1 (by rfl) ⟨205091, by rfl⟩ : syracuseStep 273455 = 410183) B410183
theorem B207919 : Blo 119786 207919 := bstep (se 1 (by rfl) ⟨155939, by rfl⟩ : syracuseStep 207919 = 311879) B311879
theorem B208055 : Blo 119786 208055 := bstep (se 1 (by rfl) ⟨156041, by rfl⟩ : syracuseStep 208055 = 312083) B312083
theorem B273743 : Blo 119786 273743 := bstep (se 1 (by rfl) ⟨205307, by rfl⟩ : syracuseStep 273743 = 410615) B410615
theorem B273833 : Blo 119786 273833 := bstep (se 2 (by rfl) ⟨102687, by rfl⟩ : syracuseStep 273833 = 205375) B205375
theorem B208379 : Blo 119786 208379 := bstep (se 1 (by rfl) ⟨156284, by rfl⟩ : syracuseStep 208379 = 312569) B312569
theorem B274319 : Blo 119786 274319 := bstep (se 1 (by rfl) ⟨205739, by rfl⟩ : syracuseStep 274319 = 411479) B411479
theorem B208811 : Blo 119786 208811 := bstep (se 1 (by rfl) ⟨156608, by rfl⟩ : syracuseStep 208811 = 313217) B313217
theorem B405971 : Blo 119786 405971 := bstep (se 1 (by rfl) ⟨304478, by rfl⟩ : syracuseStep 405971 = 608957) B608957
theorem B275039 : Blo 119786 275039 := bstep (se 1 (by rfl) ⟨206279, by rfl⟩ : syracuseStep 275039 = 412559) B412559
theorem B1585817 : Blo 119786 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B177007 : Blo 119786 177007 := bstep (se 1 (by rfl) ⟨132755, by rfl⟩ : syracuseStep 177007 = 265511) B265511
theorem B275867 : Blo 119786 275867 := bstep (se 1 (by rfl) ⟨206900, by rfl⟩ : syracuseStep 275867 = 413801) B413801
theorem B341435 : Blo 119786 341435 := bstep (se 1 (by rfl) ⟨256076, by rfl⟩ : syracuseStep 341435 = 512153) B512153
theorem B1554137 : Blo 119786 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B309055 : Blo 119786 309055 := bstep (se 1 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 309055 = 463583) B463583
theorem B276443 : Blo 119786 276443 := bstep (se 1 (by rfl) ⟨207332, by rfl⟩ : syracuseStep 276443 = 414665) B414665
theorem B276623 : Blo 119786 276623 := bstep (se 1 (by rfl) ⟨207467, by rfl⟩ : syracuseStep 276623 = 414935) B414935
theorem B276641 : Blo 119786 276641 := bstep (se 2 (by rfl) ⟨103740, by rfl⟩ : syracuseStep 276641 = 207481) B207481
theorem B276713 : Blo 119786 276713 := bstep (se 2 (by rfl) ⟨103767, by rfl⟩ : syracuseStep 276713 = 207535) B207535
theorem B309491 : Blo 119786 309491 := bstep (se 1 (by rfl) ⟨232118, by rfl⟩ : syracuseStep 309491 = 464237) B464237
theorem B407915 : Blo 119786 407915 := bstep (se 1 (by rfl) ⟨305936, by rfl⟩ : syracuseStep 407915 = 611873) B611873
theorem B3291677 : Blo 119786 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B408185 : Blo 119786 408185 := bstep (se 2 (by rfl) ⟨153069, by rfl⟩ : syracuseStep 408185 = 306139) B306139
theorem B408617 : Blo 119786 408617 := bstep (se 2 (by rfl) ⟨153231, by rfl⟩ : syracuseStep 408617 = 306463) B306463
theorem B2112641 : Blo 119786 2112641 := bstep (se 2 (by rfl) ⟨792240, by rfl⟩ : syracuseStep 2112641 = 1584481) B1584481
theorem B343223 : Blo 119786 343223 := bstep (se 1 (by rfl) ⟨257417, by rfl⟩ : syracuseStep 343223 = 514835) B514835
theorem B703849 : Blo 119786 703849 := bstep (se 2 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 703849 = 527887) B527887
theorem B179687 : Blo 119786 179687 := bstep (se 1 (by rfl) ⟨134765, by rfl⟩ : syracuseStep 179687 = 269531) B269531
theorem B277991 : Blo 119786 277991 := bstep (se 1 (by rfl) ⟨208493, by rfl⟩ : syracuseStep 277991 = 416987) B416987
theorem B441935 : Blo 119786 441935 := bstep (se 1 (by rfl) ⟨331451, by rfl⟩ : syracuseStep 441935 = 662903) B662903
theorem B179819 : Blo 119786 179819 := bstep (se 1 (by rfl) ⟨134864, by rfl⟩ : syracuseStep 179819 = 269729) B269729
theorem B179945 : Blo 119786 179945 := bstep (se 2 (by rfl) ⟨67479, by rfl⟩ : syracuseStep 179945 = 134959) B134959
theorem B376553 : Blo 119786 376553 := bstep (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) B282415
theorem B311111 : Blo 119786 311111 := bstep (se 1 (by rfl) ⟨233333, by rfl⟩ : syracuseStep 311111 = 466667) B466667
theorem B180089 : Blo 119786 180089 := bstep (se 2 (by rfl) ⟨67533, by rfl⟩ : syracuseStep 180089 = 135067) B135067
theorem B343997 : Blo 119786 343997 := bstep (se 3 (by rfl) ⟨64499, by rfl⟩ : syracuseStep 343997 = 128999) B128999
theorem B180191 : Blo 119786 180191 := bstep (se 1 (by rfl) ⟨135143, by rfl⟩ : syracuseStep 180191 = 270287) B270287
theorem B704591 : Blo 119786 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B311435 : Blo 119786 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B180443 : Blo 119786 180443 := bstep (se 1 (by rfl) ⟨135332, by rfl⟩ : syracuseStep 180443 = 270665) B270665
theorem B180455 : Blo 119786 180455 := bstep (se 1 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 180455 = 270683) B270683
theorem B344351 : Blo 119786 344351 := bstep (se 1 (by rfl) ⟨258263, by rfl⟩ : syracuseStep 344351 = 516527) B516527
theorem B180617 : Blo 119786 180617 := bstep (se 2 (by rfl) ⟨67731, by rfl⟩ : syracuseStep 180617 = 135463) B135463
theorem B311759 : Blo 119786 311759 := bstep (se 1 (by rfl) ⟨233819, by rfl⟩ : syracuseStep 311759 = 467639) B467639
theorem B180713 : Blo 119786 180713 := bstep (se 2 (by rfl) ⟨67767, by rfl⟩ : syracuseStep 180713 = 135535) B135535
theorem B180839 : Blo 119786 180839 := bstep (se 1 (by rfl) ⟨135629, by rfl⟩ : syracuseStep 180839 = 271259) B271259
theorem B180971 : Blo 119786 180971 := bstep (se 1 (by rfl) ⟨135728, by rfl⟩ : syracuseStep 180971 = 271457) B271457
theorem B181001 : Blo 119786 181001 := bstep (se 2 (by rfl) ⟨67875, by rfl⟩ : syracuseStep 181001 = 135751) B135751
theorem B181103 : Blo 119786 181103 := bstep (se 1 (by rfl) ⟨135827, by rfl⟩ : syracuseStep 181103 = 271655) B271655
theorem B344999 : Blo 119786 344999 := bstep (se 1 (by rfl) ⟨258749, by rfl⟩ : syracuseStep 344999 = 517499) B517499
theorem B312275 : Blo 119786 312275 := bstep (se 1 (by rfl) ⟨234206, by rfl⟩ : syracuseStep 312275 = 468413) B468413
theorem B607337 : Blo 119786 607337 := bstep (se 2 (by rfl) ⟨227751, by rfl⟩ : syracuseStep 607337 = 455503) B455503
theorem B181355 : Blo 119786 181355 := bstep (se 1 (by rfl) ⟨136016, by rfl⟩ : syracuseStep 181355 = 272033) B272033
theorem B410831 : Blo 119786 410831 := bstep (se 1 (by rfl) ⟨308123, by rfl⟩ : syracuseStep 410831 = 616247) B616247
theorem B607499 : Blo 119786 607499 := bstep (se 1 (by rfl) ⟨455624, by rfl⟩ : syracuseStep 607499 = 911249) B911249
theorem B181595 : Blo 119786 181595 := bstep (se 1 (by rfl) ⟨136196, by rfl⟩ : syracuseStep 181595 = 272393) B272393
theorem B411155 : Blo 119786 411155 := bstep (se 1 (by rfl) ⟨308366, by rfl⟩ : syracuseStep 411155 = 616733) B616733
theorem B345683 : Blo 119786 345683 := bstep (se 1 (by rfl) ⟨259262, by rfl⟩ : syracuseStep 345683 = 518525) B518525
theorem B181871 : Blo 119786 181871 := bstep (se 1 (by rfl) ⟨136403, by rfl⟩ : syracuseStep 181871 = 272807) B272807
theorem B312943 : Blo 119786 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B345761 : Blo 119786 345761 := bstep (se 2 (by rfl) ⟨129660, by rfl⟩ : syracuseStep 345761 = 259321) B259321
theorem B181943 : Blo 119786 181943 := bstep (se 1 (by rfl) ⟨136457, by rfl⟩ : syracuseStep 181943 = 272915) B272915
theorem B181979 : Blo 119786 181979 := bstep (se 1 (by rfl) ⟨136484, by rfl⟩ : syracuseStep 181979 = 272969) B272969
theorem B313055 : Blo 119786 313055 := bstep (se 1 (by rfl) ⟨234791, by rfl⟩ : syracuseStep 313055 = 469583) B469583
theorem B444167 : Blo 119786 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B182153 : Blo 119786 182153 := bstep (se 2 (by rfl) ⟨68307, by rfl⟩ : syracuseStep 182153 = 136615) B136615
theorem B182255 : Blo 119786 182255 := bstep (se 1 (by rfl) ⟨136691, by rfl⟩ : syracuseStep 182255 = 273383) B273383
theorem B182507 : Blo 119786 182507 := bstep (se 1 (by rfl) ⟨136880, by rfl⟩ : syracuseStep 182507 = 273761) B273761
theorem B182567 : Blo 119786 182567 := bstep (se 1 (by rfl) ⟨136925, by rfl⟩ : syracuseStep 182567 = 273851) B273851
theorem B182651 : Blo 119786 182651 := bstep (se 1 (by rfl) ⟨136988, by rfl⟩ : syracuseStep 182651 = 273977) B273977
theorem B8604107 : Blo 119786 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B182921 : Blo 119786 182921 := bstep (se 2 (by rfl) ⟨68595, by rfl⟩ : syracuseStep 182921 = 137191) B137191
theorem B641681 : Blo 119786 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B412343 : Blo 119786 412343 := bstep (se 1 (by rfl) ⟨309257, by rfl⟩ : syracuseStep 412343 = 618515) B618515
theorem B183095 : Blo 119786 183095 := bstep (se 1 (by rfl) ⟨137321, by rfl⟩ : syracuseStep 183095 = 274643) B274643
theorem B576343 : Blo 119786 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B183131 : Blo 119786 183131 := bstep (se 1 (by rfl) ⟨137348, by rfl⟩ : syracuseStep 183131 = 274697) B274697
theorem B609119 : Blo 119786 609119 := bstep (se 1 (by rfl) ⟨456839, by rfl⟩ : syracuseStep 609119 = 913679) B913679
theorem B183275 : Blo 119786 183275 := bstep (se 1 (by rfl) ⟨137456, by rfl⟩ : syracuseStep 183275 = 274913) B274913
theorem B183479 : Blo 119786 183479 := bstep (se 1 (by rfl) ⟨137609, by rfl⟩ : syracuseStep 183479 = 275219) B275219
theorem B183719 : Blo 119786 183719 := bstep (se 1 (by rfl) ⟨137789, by rfl⟩ : syracuseStep 183719 = 275579) B275579
theorem B183803 : Blo 119786 183803 := bstep (se 1 (by rfl) ⟨137852, by rfl⟩ : syracuseStep 183803 = 275705) B275705
theorem B183899 : Blo 119786 183899 := bstep (se 1 (by rfl) ⟨137924, by rfl⟩ : syracuseStep 183899 = 275849) B275849
theorem B183983 : Blo 119786 183983 := bstep (se 1 (by rfl) ⟨137987, by rfl⟩ : syracuseStep 183983 = 275975) B275975
theorem B184103 : Blo 119786 184103 := bstep (se 1 (by rfl) ⟨138077, by rfl⟩ : syracuseStep 184103 = 276155) B276155
theorem B184187 : Blo 119786 184187 := bstep (se 1 (by rfl) ⟨138140, by rfl⟩ : syracuseStep 184187 = 276281) B276281
theorem B3461291 : Blo 119786 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B184607 : Blo 119786 184607 := bstep (se 1 (by rfl) ⟨138455, by rfl⟩ : syracuseStep 184607 = 276911) B276911
theorem B184631 : Blo 119786 184631 := bstep (se 1 (by rfl) ⟨138473, by rfl⟩ : syracuseStep 184631 = 276947) B276947
theorem B184703 : Blo 119786 184703 := bstep (se 1 (by rfl) ⟨138527, by rfl⟩ : syracuseStep 184703 = 277055) B277055
theorem B348553 : Blo 119786 348553 := bstep (se 2 (by rfl) ⟨130707, by rfl⟩ : syracuseStep 348553 = 261415) B261415
theorem B741797 : Blo 119786 741797 := bstep (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) B139087
theorem B184775 : Blo 119786 184775 := bstep (se 1 (by rfl) ⟨138581, by rfl⟩ : syracuseStep 184775 = 277163) B277163
theorem B315863 : Blo 119786 315863 := bstep (se 1 (by rfl) ⟨236897, by rfl⟩ : syracuseStep 315863 = 473795) B473795
theorem B414287 : Blo 119786 414287 := bstep (se 1 (by rfl) ⟨310715, by rfl⟩ : syracuseStep 414287 = 621431) B621431
theorem B185129 : Blo 119786 185129 := bstep (se 2 (by rfl) ⟨69423, by rfl⟩ : syracuseStep 185129 = 138847) B138847
theorem B185135 : Blo 119786 185135 := bstep (se 1 (by rfl) ⟨138851, by rfl⟩ : syracuseStep 185135 = 277703) B277703
theorem B185255 : Blo 119786 185255 := bstep (se 1 (by rfl) ⟨138941, by rfl⟩ : syracuseStep 185255 = 277883) B277883
theorem B119803 : Blo 119786 119803 := bstep (se 1 (by rfl) ⟨89852, by rfl⟩ : syracuseStep 119803 = 179705) B179705
theorem B185339 : Blo 119786 185339 := bstep (se 1 (by rfl) ⟨139004, by rfl⟩ : syracuseStep 185339 = 278009) B278009
theorem B185399 : Blo 119786 185399 := bstep (se 1 (by rfl) ⟨139049, by rfl⟩ : syracuseStep 185399 = 278099) B278099
theorem B119871 : Blo 119786 119871 := bstep (se 1 (by rfl) ⟨89903, by rfl⟩ : syracuseStep 119871 = 179807) B179807
theorem B414827 : Blo 119786 414827 := bstep (se 1 (by rfl) ⟨311120, by rfl⟩ : syracuseStep 414827 = 622241) B622241
theorem B185519 : Blo 119786 185519 := bstep (se 1 (by rfl) ⟨139139, by rfl⟩ : syracuseStep 185519 = 278279) B278279
theorem B120015 : Blo 119786 120015 := bstep (se 1 (by rfl) ⟨90011, by rfl⟩ : syracuseStep 120015 = 180023) B180023
theorem B120219 : Blo 119786 120219 := bstep (se 1 (by rfl) ⟨90164, by rfl⟩ : syracuseStep 120219 = 180329) B180329
theorem B120431 : Blo 119786 120431 := bstep (se 1 (by rfl) ⟨90323, by rfl⟩ : syracuseStep 120431 = 180647) B180647
theorem B120487 : Blo 119786 120487 := bstep (se 1 (by rfl) ⟨90365, by rfl⟩ : syracuseStep 120487 = 180731) B180731
theorem B710315 : Blo 119786 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B120571 : Blo 119786 120571 := bstep (se 1 (by rfl) ⟨90428, by rfl⟩ : syracuseStep 120571 = 180857) B180857
theorem B120607 : Blo 119786 120607 := bstep (se 1 (by rfl) ⟨90455, by rfl⟩ : syracuseStep 120607 = 180911) B180911
theorem B120639 : Blo 119786 120639 := bstep (se 1 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 120639 = 180959) B180959
theorem B350171 : Blo 119786 350171 := bstep (se 1 (by rfl) ⟨262628, by rfl⟩ : syracuseStep 350171 = 525257) B525257
theorem B350183 : Blo 119786 350183 := bstep (se 1 (by rfl) ⟨262637, by rfl⟩ : syracuseStep 350183 = 525275) B525275
theorem B120815 : Blo 119786 120815 := bstep (se 1 (by rfl) ⟨90611, by rfl⟩ : syracuseStep 120815 = 181223) B181223
theorem B120987 : Blo 119786 120987 := bstep (se 1 (by rfl) ⟨90740, by rfl⟩ : syracuseStep 120987 = 181481) B181481
theorem B121023 : Blo 119786 121023 := bstep (se 1 (by rfl) ⟨90767, by rfl⟩ : syracuseStep 121023 = 181535) B181535
theorem B121135 : Blo 119786 121135 := bstep (se 1 (by rfl) ⟨90851, by rfl⟩ : syracuseStep 121135 = 181703) B181703
theorem B416123 : Blo 119786 416123 := bstep (se 1 (by rfl) ⟨312092, by rfl⟩ : syracuseStep 416123 = 624185) B624185
theorem B350639 : Blo 119786 350639 := bstep (se 1 (by rfl) ⟨262979, by rfl⟩ : syracuseStep 350639 = 525959) B525959
theorem B121371 : Blo 119786 121371 := bstep (se 1 (by rfl) ⟨91028, by rfl⟩ : syracuseStep 121371 = 182057) B182057
theorem B121375 : Blo 119786 121375 := bstep (se 1 (by rfl) ⟨91031, by rfl⟩ : syracuseStep 121375 = 182063) B182063
theorem B416393 : Blo 119786 416393 := bstep (se 2 (by rfl) ⟨156147, by rfl⟩ : syracuseStep 416393 = 312295) B312295
theorem B1596125 : Blo 119786 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B416603 : Blo 119786 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B121691 : Blo 119786 121691 := bstep (se 1 (by rfl) ⟨91268, by rfl⟩ : syracuseStep 121691 = 182537) B182537
theorem B121759 : Blo 119786 121759 := bstep (se 1 (by rfl) ⟨91319, by rfl⟩ : syracuseStep 121759 = 182639) B182639
theorem B121903 : Blo 119786 121903 := bstep (se 1 (by rfl) ⟨91427, by rfl⟩ : syracuseStep 121903 = 182855) B182855
theorem B121927 : Blo 119786 121927 := bstep (se 1 (by rfl) ⟨91445, by rfl⟩ : syracuseStep 121927 = 182891) B182891
theorem B122079 : Blo 119786 122079 := bstep (se 1 (by rfl) ⟨91559, by rfl⟩ : syracuseStep 122079 = 183119) B183119
theorem B122343 : Blo 119786 122343 := bstep (se 1 (by rfl) ⟨91757, by rfl⟩ : syracuseStep 122343 = 183515) B183515
theorem B187967 : Blo 119786 187967 := bstep (se 1 (by rfl) ⟨140975, by rfl⟩ : syracuseStep 187967 = 281951) B281951
theorem B351823 : Blo 119786 351823 := bstep (se 1 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 351823 = 527735) B527735
theorem B122459 : Blo 119786 122459 := bstep (se 1 (by rfl) ⟨91844, by rfl⟩ : syracuseStep 122459 = 183689) B183689
theorem B417527 : Blo 119786 417527 := bstep (se 1 (by rfl) ⟨313145, by rfl⟩ : syracuseStep 417527 = 626291) B626291
theorem B1171223 : Blo 119786 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B122695 : Blo 119786 122695 := bstep (se 1 (by rfl) ⟨92021, by rfl⟩ : syracuseStep 122695 = 184043) B184043
theorem B155515 : Blo 119786 155515 := bstep (se 1 (by rfl) ⟨116636, by rfl⟩ : syracuseStep 155515 = 233273) B233273
theorem B4087741 : Blo 119786 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B876509 : Blo 119786 876509 := bstep (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) B328691
theorem B122847 : Blo 119786 122847 := bstep (se 1 (by rfl) ⟨92135, by rfl⟩ : syracuseStep 122847 = 184271) B184271
theorem B123111 : Blo 119786 123111 := bstep (se 1 (by rfl) ⟨92333, by rfl⟩ : syracuseStep 123111 = 184667) B184667
theorem B581879 : Blo 119786 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B123263 : Blo 119786 123263 := bstep (se 1 (by rfl) ⟨92447, by rfl⟩ : syracuseStep 123263 = 184895) B184895
theorem B123343 : Blo 119786 123343 := bstep (se 1 (by rfl) ⟨92507, by rfl⟩ : syracuseStep 123343 = 185015) B185015
theorem B1335869 : Blo 119786 1335869 := bstep (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) B500951
theorem B123495 : Blo 119786 123495 := bstep (se 1 (by rfl) ⟨92621, by rfl⟩ : syracuseStep 123495 = 185243) B185243
theorem B123759 : Blo 119786 123759 := bstep (se 1 (by rfl) ⟨92819, by rfl⟩ : syracuseStep 123759 = 185639) B185639
theorem B156583 : Blo 119786 156583 := bstep (se 1 (by rfl) ⟨117437, by rfl⟩ : syracuseStep 156583 = 234875) B234875
theorem B288479 : Blo 119786 288479 := bstep (se 1 (by rfl) ⟨216359, by rfl⟩ : syracuseStep 288479 = 432719) B432719
theorem B2844953 : Blo 119786 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B289163 : Blo 119786 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B1567259 : Blo 119786 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B584263 : Blo 119786 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B387767 : Blo 119786 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B256699 : Blo 119786 256699 := bstep (se 1 (by rfl) ⟨192524, by rfl⟩ : syracuseStep 256699 = 385049) B385049
theorem B1764089 : Blo 119786 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B5303339 : Blo 119786 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B519311 : Blo 119786 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B617705 : Blo 119786 617705 := bstep (se 2 (by rfl) ⟨231639, by rfl⟩ : syracuseStep 617705 = 463279) B463279
theorem B781579 : Blo 119786 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B2354579 : Blo 119786 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B1109629 : Blo 119786 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B290479 : Blo 119786 290479 := bstep (se 1 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 290479 = 435719) B435719
theorem B421775 : Blo 119786 421775 := bstep (se 1 (by rfl) ⟨316331, by rfl⟩ : syracuseStep 421775 = 632663) B632663
theorem B618625 : Blo 119786 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B880951 : Blo 119786 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B619001 : Blo 119786 619001 := bstep (se 2 (by rfl) ⟨232125, by rfl⟩ : syracuseStep 619001 = 464251) B464251
theorem B487951 : Blo 119786 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B1012445 : Blo 119786 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B520951 : Blo 119786 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B684895 : Blo 119786 684895 := bstep (se 1 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 684895 = 1027343) B1027343
theorem B193447 : Blo 119786 193447 := bstep (se 1 (by rfl) ⟨145085, by rfl⟩ : syracuseStep 193447 = 290171) B290171
theorem B456263 : Blo 119786 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B784349 : Blo 119786 784349 := bstep (se 3 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 784349 = 294131) B294131
theorem B1406969 : Blo 119786 1406969 := bstep (se 2 (by rfl) ⟨527613, by rfl⟩ : syracuseStep 1406969 = 1055227) B1055227
theorem B293161 : Blo 119786 293161 := bstep (se 2 (by rfl) ⟨109935, by rfl⟩ : syracuseStep 293161 = 219871) B219871
theorem B457235 : Blo 119786 457235 := bstep (se 1 (by rfl) ⟨342926, by rfl⟩ : syracuseStep 457235 = 685853) B685853
theorem B1571719 : Blo 119786 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B981895 : Blo 119786 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B523513 : Blo 119786 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B196271 : Blo 119786 196271 := bstep (se 1 (by rfl) ⟨147203, by rfl⟩ : syracuseStep 196271 = 294407) B294407
theorem B1572695 : Blo 119786 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B196523 : Blo 119786 196523 := bstep (se 1 (by rfl) ⟨147392, by rfl⟩ : syracuseStep 196523 = 294785) B294785
theorem B229567 : Blo 119786 229567 := bstep (se 1 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 229567 = 344351) B344351
theorem B2490743 : Blo 119786 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B459179 : Blo 119786 459179 := bstep (se 1 (by rfl) ⟨344384, by rfl⟩ : syracuseStep 459179 = 688769) B688769
theorem B197035 : Blo 119786 197035 := bstep (se 1 (by rfl) ⟨147776, by rfl⟩ : syracuseStep 197035 = 295553) B295553
theorem B328303 : Blo 119786 328303 := bstep (se 1 (by rfl) ⟨246227, by rfl⟩ : syracuseStep 328303 = 492455) B492455
theorem B1573793 : Blo 119786 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B230455 : Blo 119786 230455 := bstep (se 1 (by rfl) ⟨172841, by rfl⟩ : syracuseStep 230455 = 345683) B345683
theorem B230507 : Blo 119786 230507 := bstep (se 1 (by rfl) ⟨172880, by rfl⟩ : syracuseStep 230507 = 345761) B345761
theorem B296111 : Blo 119786 296111 := bstep (se 1 (by rfl) ⟨222083, by rfl⟩ : syracuseStep 296111 = 444167) B444167
theorem B525599 : Blo 119786 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B460151 : Blo 119786 460151 := bstep (se 1 (by rfl) ⟨345113, by rfl⟩ : syracuseStep 460151 = 690227) B690227
theorem B5736071 : Blo 119786 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B427787 : Blo 119786 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B1411181 : Blo 119786 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B919997 : Blo 119786 919997 := bstep (se 3 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 919997 = 344999) B344999
theorem B527273 : Blo 119786 527273 := bstep (se 2 (by rfl) ⟨197727, by rfl⟩ : syracuseStep 527273 = 395455) B395455
theorem B494531 : Blo 119786 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B1051811 : Blo 119786 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B233447 : Blo 119786 233447 := bstep (se 1 (by rfl) ⟨175085, by rfl⟩ : syracuseStep 233447 = 350171) B350171
theorem B233455 : Blo 119786 233455 := bstep (se 1 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 233455 = 350183) B350183
theorem B2101297 : Blo 119786 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B233759 : Blo 119786 233759 := bstep (se 1 (by rfl) ⟨175319, by rfl⟩ : syracuseStep 233759 = 350639) B350639
theorem B528707 : Blo 119786 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B135931 : Blo 119786 135931 := bstep (se 1 (by rfl) ⟨101948, by rfl⟩ : syracuseStep 135931 = 203897) B203897
theorem B1479505 : Blo 119786 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B202223 : Blo 119786 202223 := bstep (se 1 (by rfl) ⟨151667, by rfl⟩ : syracuseStep 202223 = 303335) B303335
theorem B136687 : Blo 119786 136687 := bstep (se 1 (by rfl) ⟨102515, by rfl⟩ : syracuseStep 136687 = 205031) B205031
theorem B824833 : Blo 119786 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B136795 : Blo 119786 136795 := bstep (se 1 (by rfl) ⟨102596, by rfl⟩ : syracuseStep 136795 = 205193) B205193
theorem B890579 : Blo 119786 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B202567 : Blo 119786 202567 := bstep (se 1 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 202567 = 303851) B303851
theorem B464723 : Blo 119786 464723 := bstep (se 1 (by rfl) ⟨348542, by rfl⟩ : syracuseStep 464723 = 697085) B697085
theorem B464737 : Blo 119786 464737 := bstep (se 2 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 464737 = 348553) B348553
theorem B137083 : Blo 119786 137083 := bstep (se 1 (by rfl) ⟨102812, by rfl⟩ : syracuseStep 137083 = 205625) B205625
theorem B202655 : Blo 119786 202655 := bstep (se 1 (by rfl) ⟨151991, by rfl⟩ : syracuseStep 202655 = 303983) B303983
theorem B137119 : Blo 119786 137119 := bstep (se 1 (by rfl) ⟨102839, by rfl⟩ : syracuseStep 137119 = 205679) B205679
theorem B694601 : Blo 119786 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B334219 : Blo 119786 334219 := bstep (se 1 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 334219 = 501329) B501329
theorem B236009 : Blo 119786 236009 := bstep (se 2 (by rfl) ⟨88503, by rfl⟩ : syracuseStep 236009 = 177007) B177007
theorem B138055 : Blo 119786 138055 := bstep (se 1 (by rfl) ⟨103541, by rfl⟩ : syracuseStep 138055 = 207083) B207083
theorem B990323 : Blo 119786 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B269639 : Blo 119786 269639 := bstep (se 1 (by rfl) ⟨202229, by rfl⟩ : syracuseStep 269639 = 404459) B404459
theorem B269675 : Blo 119786 269675 := bstep (se 1 (by rfl) ⟨202256, by rfl⟩ : syracuseStep 269675 = 404513) B404513
theorem B138703 : Blo 119786 138703 := bstep (se 1 (by rfl) ⟨104027, by rfl⟩ : syracuseStep 138703 = 208055) B208055
theorem B269801 : Blo 119786 269801 := bstep (se 2 (by rfl) ⟨101175, by rfl⟩ : syracuseStep 269801 = 202351) B202351
theorem B269945 : Blo 119786 269945 := bstep (se 2 (by rfl) ⟨101229, by rfl⟩ : syracuseStep 269945 = 202459) B202459
theorem B138919 : Blo 119786 138919 := bstep (se 1 (by rfl) ⟨104189, by rfl⟩ : syracuseStep 138919 = 208379) B208379
theorem B139207 : Blo 119786 139207 := bstep (se 1 (by rfl) ⟨104405, by rfl⟩ : syracuseStep 139207 = 208811) B208811
theorem B270647 : Blo 119786 270647 := bstep (se 1 (by rfl) ⟨202985, by rfl⟩ : syracuseStep 270647 = 405971) B405971
theorem B1057211 : Blo 119786 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B304175 : Blo 119786 304175 := bstep (se 1 (by rfl) ⟨228131, by rfl⟩ : syracuseStep 304175 = 456263) B456263
theorem B271673 : Blo 119786 271673 := bstep (se 2 (by rfl) ⟨101877, by rfl⟩ : syracuseStep 271673 = 203755) B203755
theorem B206327 : Blo 119786 206327 := bstep (se 1 (by rfl) ⟨154745, by rfl⟩ : syracuseStep 206327 = 309491) B309491
theorem B501245 : Blo 119786 501245 := bstep (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) B187967
theorem B271943 : Blo 119786 271943 := bstep (se 1 (by rfl) ⟨203957, by rfl⟩ : syracuseStep 271943 = 407915) B407915
theorem B698017 : Blo 119786 698017 := bstep (se 2 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 698017 = 523513) B523513
theorem B304823 : Blo 119786 304823 := bstep (se 1 (by rfl) ⟨228617, by rfl⟩ : syracuseStep 304823 = 457235) B457235
theorem B272123 : Blo 119786 272123 := bstep (se 1 (by rfl) ⟨204092, by rfl⟩ : syracuseStep 272123 = 408185) B408185
theorem B272411 : Blo 119786 272411 := bstep (se 1 (by rfl) ⟨204308, by rfl⟩ : syracuseStep 272411 = 408617) B408617
theorem B469097 : Blo 119786 469097 := bstep (se 2 (by rfl) ⟨175911, by rfl⟩ : syracuseStep 469097 = 351823) B351823
theorem B207353 : Blo 119786 207353 := bstep (se 2 (by rfl) ⟨77757, by rfl⟩ : syracuseStep 207353 = 155515) B155515
theorem B207407 : Blo 119786 207407 := bstep (se 1 (by rfl) ⟨155555, by rfl⟩ : syracuseStep 207407 = 311111) B311111
theorem B5450321 : Blo 119786 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B469727 : Blo 119786 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B305927 : Blo 119786 305927 := bstep (se 1 (by rfl) ⟨229445, by rfl⟩ : syracuseStep 305927 = 458891) B458891
theorem B207623 : Blo 119786 207623 := bstep (se 1 (by rfl) ⟨155717, by rfl⟩ : syracuseStep 207623 = 311435) B311435
theorem B207839 : Blo 119786 207839 := bstep (se 1 (by rfl) ⟨155879, by rfl⟩ : syracuseStep 207839 = 311759) B311759
theorem B404729 : Blo 119786 404729 := bstep (se 2 (by rfl) ⟨151773, by rfl⟩ : syracuseStep 404729 = 303547) B303547
theorem B208183 : Blo 119786 208183 := bstep (se 1 (by rfl) ⟨156137, by rfl⟩ : syracuseStep 208183 = 312275) B312275
theorem B404891 : Blo 119786 404891 := bstep (se 1 (by rfl) ⟨303668, by rfl⟩ : syracuseStep 404891 = 607337) B607337
theorem B273887 : Blo 119786 273887 := bstep (se 1 (by rfl) ⟨205415, by rfl⟩ : syracuseStep 273887 = 410831) B410831
theorem B404999 : Blo 119786 404999 := bstep (se 1 (by rfl) ⟨303749, by rfl⟩ : syracuseStep 404999 = 607499) B607499
theorem B274103 : Blo 119786 274103 := bstep (se 1 (by rfl) ⟨205577, by rfl⟩ : syracuseStep 274103 = 411155) B411155
theorem B208703 : Blo 119786 208703 := bstep (se 1 (by rfl) ⟨156527, by rfl⟩ : syracuseStep 208703 = 313055) B313055
theorem B208777 : Blo 119786 208777 := bstep (se 2 (by rfl) ⟨78291, by rfl⟩ : syracuseStep 208777 = 156583) B156583
theorem B274895 : Blo 119786 274895 := bstep (se 1 (by rfl) ⟨206171, by rfl⟩ : syracuseStep 274895 = 412343) B412343
theorem B406079 : Blo 119786 406079 := bstep (se 1 (by rfl) ⟨304559, by rfl⟩ : syracuseStep 406079 = 609119) B609119
theorem B701131 : Blo 119786 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B1028983 : Blo 119786 1028983 := bstep (se 1 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 1028983 = 1543475) B1543475
theorem B275561 : Blo 119786 275561 := bstep (se 2 (by rfl) ⟨103335, by rfl⟩ : syracuseStep 275561 = 206671) B206671
theorem B2602405 : Blo 119786 2602405 := bstep (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) B487951
theorem B2307527 : Blo 119786 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B210575 : Blo 119786 210575 := bstep (se 1 (by rfl) ⟨157931, by rfl⟩ : syracuseStep 210575 = 315863) B315863
theorem B276191 : Blo 119786 276191 := bstep (se 1 (by rfl) ⟨207143, by rfl⟩ : syracuseStep 276191 = 414287) B414287
theorem B702391 : Blo 119786 702391 := bstep (se 1 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 702391 = 1053587) B1053587
theorem B276551 : Blo 119786 276551 := bstep (se 1 (by rfl) ⟨207413, by rfl⟩ : syracuseStep 276551 = 414827) B414827
theorem B309703 : Blo 119786 309703 := bstep (se 1 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 309703 = 464555) B464555
theorem B473543 : Blo 119786 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B768457 : Blo 119786 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B277217 : Blo 119786 277217 := bstep (se 2 (by rfl) ⟨103956, by rfl⟩ : syracuseStep 277217 = 207913) B207913
theorem B277225 : Blo 119786 277225 := bstep (se 2 (by rfl) ⟨103959, by rfl⟩ : syracuseStep 277225 = 207919) B207919
theorem B277415 : Blo 119786 277415 := bstep (se 1 (by rfl) ⟨208061, by rfl⟩ : syracuseStep 277415 = 416123) B416123
theorem B277595 : Blo 119786 277595 := bstep (se 1 (by rfl) ⟨208196, by rfl⟩ : syracuseStep 277595 = 416393) B416393
theorem B1064083 : Blo 119786 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B441587 : Blo 119786 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B769277 : Blo 119786 769277 := bstep (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) B288479
theorem B1031717 : Blo 119786 1031717 := bstep (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) B193447
theorem B180047 : Blo 119786 180047 := bstep (se 1 (by rfl) ⟨135035, by rfl⟩ : syracuseStep 180047 = 270071) B270071
theorem B278351 : Blo 119786 278351 := bstep (se 1 (by rfl) ⟨208763, by rfl⟩ : syracuseStep 278351 = 417527) B417527
theorem B311161 : Blo 119786 311161 := bstep (se 2 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 311161 = 233371) B233371
theorem B180167 : Blo 119786 180167 := bstep (se 1 (by rfl) ⟨135125, by rfl⟩ : syracuseStep 180167 = 270251) B270251
theorem B180527 : Blo 119786 180527 := bstep (se 1 (by rfl) ⟨135395, by rfl⟩ : syracuseStep 180527 = 270791) B270791
theorem B180767 : Blo 119786 180767 := bstep (se 1 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 180767 = 271151) B271151
theorem B181439 : Blo 119786 181439 := bstep (se 1 (by rfl) ⟨136079, by rfl⟩ : syracuseStep 181439 = 272159) B272159
theorem B181583 : Blo 119786 181583 := bstep (se 1 (by rfl) ⟨136187, by rfl⟩ : syracuseStep 181583 = 272375) B272375
theorem B181673 : Blo 119786 181673 := bstep (se 2 (by rfl) ⟨68127, by rfl⟩ : syracuseStep 181673 = 136255) B136255
theorem B181823 : Blo 119786 181823 := bstep (se 1 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 181823 = 272735) B272735
theorem B181865 : Blo 119786 181865 := bstep (se 2 (by rfl) ⟨68199, by rfl⟩ : syracuseStep 181865 = 136399) B136399
theorem B378475 : Blo 119786 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B182303 : Blo 119786 182303 := bstep (se 1 (by rfl) ⟨136727, by rfl⟩ : syracuseStep 182303 = 273455) B273455
theorem B346207 : Blo 119786 346207 := bstep (se 1 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 346207 = 519311) B519311
theorem B411803 : Blo 119786 411803 := bstep (se 1 (by rfl) ⟨308852, by rfl⟩ : syracuseStep 411803 = 617705) B617705
theorem B182495 : Blo 119786 182495 := bstep (se 1 (by rfl) ⟨136871, by rfl⟩ : syracuseStep 182495 = 273743) B273743
theorem B182555 : Blo 119786 182555 := bstep (se 1 (by rfl) ⟨136916, by rfl⟩ : syracuseStep 182555 = 273833) B273833
theorem B412073 : Blo 119786 412073 := bstep (se 2 (by rfl) ⟨154527, by rfl⟩ : syracuseStep 412073 = 309055) B309055
theorem B281183 : Blo 119786 281183 := bstep (se 1 (by rfl) ⟨210887, by rfl⟩ : syracuseStep 281183 = 421775) B421775
theorem B182879 : Blo 119786 182879 := bstep (se 1 (by rfl) ⟨137159, by rfl⟩ : syracuseStep 182879 = 274319) B274319
theorem B183161 : Blo 119786 183161 := bstep (se 2 (by rfl) ⟨68685, by rfl⟩ : syracuseStep 183161 = 137371) B137371
theorem B183209 : Blo 119786 183209 := bstep (se 2 (by rfl) ⟨68703, by rfl⟩ : syracuseStep 183209 = 137407) B137407
theorem B412667 : Blo 119786 412667 := bstep (se 1 (by rfl) ⟨309500, by rfl⟩ : syracuseStep 412667 = 619001) B619001
theorem B183359 : Blo 119786 183359 := bstep (se 1 (by rfl) ⟨137519, by rfl⟩ : syracuseStep 183359 = 275039) B275039
theorem B674963 : Blo 119786 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B183911 : Blo 119786 183911 := bstep (se 1 (by rfl) ⟨137933, by rfl⟩ : syracuseStep 183911 = 275867) B275867
theorem B1036091 : Blo 119786 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B184295 : Blo 119786 184295 := bstep (se 1 (by rfl) ⟨138221, by rfl⟩ : syracuseStep 184295 = 276443) B276443
theorem B937979 : Blo 119786 937979 := bstep (se 1 (by rfl) ⟨703484, by rfl⟩ : syracuseStep 937979 = 1406969) B1406969
theorem B184415 : Blo 119786 184415 := bstep (se 1 (by rfl) ⟨138311, by rfl⟩ : syracuseStep 184415 = 276623) B276623
theorem B184427 : Blo 119786 184427 := bstep (se 1 (by rfl) ⟨138320, by rfl⟩ : syracuseStep 184427 = 276641) B276641
theorem B184475 : Blo 119786 184475 := bstep (se 1 (by rfl) ⟨138356, by rfl⟩ : syracuseStep 184475 = 276713) B276713
theorem B938465 : Blo 119786 938465 := bstep (se 2 (by rfl) ⟨351924, by rfl⟩ : syracuseStep 938465 = 703849) B703849
theorem B1004141 : Blo 119786 1004141 := bstep (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) B376553
theorem B1496045 : Blo 119786 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B119791 : Blo 119786 119791 := bstep (se 1 (by rfl) ⟨89843, by rfl⟩ : syracuseStep 119791 = 179687) B179687
theorem B185327 : Blo 119786 185327 := bstep (se 1 (by rfl) ⟨138995, by rfl⟩ : syracuseStep 185327 = 277991) B277991
theorem B119879 : Blo 119786 119879 := bstep (se 1 (by rfl) ⟨89909, by rfl⟩ : syracuseStep 119879 = 179819) B179819
theorem B119963 : Blo 119786 119963 := bstep (se 1 (by rfl) ⟨89972, by rfl⟩ : syracuseStep 119963 = 179945) B179945
theorem B120059 : Blo 119786 120059 := bstep (se 1 (by rfl) ⟨90044, by rfl⟩ : syracuseStep 120059 = 180089) B180089
theorem B120127 : Blo 119786 120127 := bstep (se 1 (by rfl) ⟨90095, by rfl⟩ : syracuseStep 120127 = 180191) B180191
theorem B120295 : Blo 119786 120295 := bstep (se 1 (by rfl) ⟨90221, by rfl⟩ : syracuseStep 120295 = 180443) B180443
theorem B120303 : Blo 119786 120303 := bstep (se 1 (by rfl) ⟨90227, by rfl⟩ : syracuseStep 120303 = 180455) B180455
theorem B120411 : Blo 119786 120411 := bstep (se 1 (by rfl) ⟨90308, by rfl⟩ : syracuseStep 120411 = 180617) B180617
theorem B120475 : Blo 119786 120475 := bstep (se 1 (by rfl) ⟨90356, by rfl⟩ : syracuseStep 120475 = 180713) B180713
theorem B120559 : Blo 119786 120559 := bstep (se 1 (by rfl) ⟨90419, by rfl⟩ : syracuseStep 120559 = 180839) B180839
theorem B120647 : Blo 119786 120647 := bstep (se 1 (by rfl) ⟨90485, by rfl⟩ : syracuseStep 120647 = 180971) B180971
theorem B120667 : Blo 119786 120667 := bstep (se 1 (by rfl) ⟨90500, by rfl⟩ : syracuseStep 120667 = 181001) B181001
theorem B120735 : Blo 119786 120735 := bstep (se 1 (by rfl) ⟨90551, by rfl⟩ : syracuseStep 120735 = 181103) B181103
theorem B120903 : Blo 119786 120903 := bstep (se 1 (by rfl) ⟨90677, by rfl⟩ : syracuseStep 120903 = 181355) B181355
theorem B121063 : Blo 119786 121063 := bstep (se 1 (by rfl) ⟨90797, by rfl⟩ : syracuseStep 121063 = 181595) B181595
theorem B121247 : Blo 119786 121247 := bstep (se 1 (by rfl) ⟨90935, by rfl⟩ : syracuseStep 121247 = 181871) B181871
theorem B121295 : Blo 119786 121295 := bstep (se 1 (by rfl) ⟨90971, by rfl⟩ : syracuseStep 121295 = 181943) B181943
theorem B121319 : Blo 119786 121319 := bstep (se 1 (by rfl) ⟨90989, by rfl⟩ : syracuseStep 121319 = 181979) B181979
theorem B121435 : Blo 119786 121435 := bstep (se 1 (by rfl) ⟨91076, by rfl⟩ : syracuseStep 121435 = 182153) B182153
theorem B121503 : Blo 119786 121503 := bstep (se 1 (by rfl) ⟨91127, by rfl⟩ : syracuseStep 121503 = 182255) B182255
theorem B121671 : Blo 119786 121671 := bstep (se 1 (by rfl) ⟨91253, by rfl⟩ : syracuseStep 121671 = 182507) B182507
theorem B121711 : Blo 119786 121711 := bstep (se 1 (by rfl) ⟨91283, by rfl⟩ : syracuseStep 121711 = 182567) B182567
theorem B121767 : Blo 119786 121767 := bstep (se 1 (by rfl) ⟨91325, by rfl⟩ : syracuseStep 121767 = 182651) B182651
theorem B121947 : Blo 119786 121947 := bstep (se 1 (by rfl) ⟨91460, by rfl⟩ : syracuseStep 121947 = 182921) B182921
theorem B122063 : Blo 119786 122063 := bstep (se 1 (by rfl) ⟨91547, by rfl⟩ : syracuseStep 122063 = 183095) B183095
theorem B122087 : Blo 119786 122087 := bstep (se 1 (by rfl) ⟨91565, by rfl⟩ : syracuseStep 122087 = 183131) B183131
theorem B122183 : Blo 119786 122183 := bstep (se 1 (by rfl) ⟨91637, by rfl⟩ : syracuseStep 122183 = 183275) B183275
theorem B122319 : Blo 119786 122319 := bstep (se 1 (by rfl) ⟨91739, by rfl⟩ : syracuseStep 122319 = 183479) B183479
theorem B417257 : Blo 119786 417257 := bstep (se 2 (by rfl) ⟨156471, by rfl⟩ : syracuseStep 417257 = 312943) B312943
theorem B122479 : Blo 119786 122479 := bstep (se 1 (by rfl) ⟨91859, by rfl⟩ : syracuseStep 122479 = 183719) B183719
theorem B122535 : Blo 119786 122535 := bstep (se 1 (by rfl) ⟨91901, by rfl⟩ : syracuseStep 122535 = 183803) B183803
theorem B122599 : Blo 119786 122599 := bstep (se 1 (by rfl) ⟨91949, by rfl⟩ : syracuseStep 122599 = 183899) B183899
theorem B122655 : Blo 119786 122655 := bstep (se 1 (by rfl) ⟨91991, by rfl⟩ : syracuseStep 122655 = 183983) B183983
theorem B122735 : Blo 119786 122735 := bstep (se 1 (by rfl) ⟨92051, by rfl⟩ : syracuseStep 122735 = 184103) B184103
theorem B2318219 : Blo 119786 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B122791 : Blo 119786 122791 := bstep (se 1 (by rfl) ⟨92093, by rfl⟩ : syracuseStep 122791 = 184187) B184187
theorem B123071 : Blo 119786 123071 := bstep (se 1 (by rfl) ⟨92303, by rfl⟩ : syracuseStep 123071 = 184607) B184607
theorem B123087 : Blo 119786 123087 := bstep (se 1 (by rfl) ⟨92315, by rfl⟩ : syracuseStep 123087 = 184631) B184631
theorem B123135 : Blo 119786 123135 := bstep (se 1 (by rfl) ⟨92351, by rfl⟩ : syracuseStep 123135 = 184703) B184703
theorem B123183 : Blo 119786 123183 := bstep (se 1 (by rfl) ⟨92387, by rfl⟩ : syracuseStep 123183 = 184775) B184775
theorem B123419 : Blo 119786 123419 := bstep (se 1 (by rfl) ⟨92564, by rfl⟩ : syracuseStep 123419 = 185129) B185129
theorem B123423 : Blo 119786 123423 := bstep (se 1 (by rfl) ⟨92567, by rfl⟩ : syracuseStep 123423 = 185135) B185135
theorem B614951 : Blo 119786 614951 := bstep (se 1 (by rfl) ⟨461213, by rfl⟩ : syracuseStep 614951 = 922427) B922427
theorem B123503 : Blo 119786 123503 := bstep (se 1 (by rfl) ⟨92627, by rfl⟩ : syracuseStep 123503 = 185255) B185255
theorem B123559 : Blo 119786 123559 := bstep (se 1 (by rfl) ⟨92669, by rfl⟩ : syracuseStep 123559 = 185339) B185339
theorem B123599 : Blo 119786 123599 := bstep (se 1 (by rfl) ⟨92699, by rfl⟩ : syracuseStep 123599 = 185399) B185399
theorem B779017 : Blo 119786 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B123679 : Blo 119786 123679 := bstep (se 1 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 123679 = 185519) B185519
theorem B1369061 : Blo 119786 1369061 := bstep (se 4 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 1369061 = 256699) B256699
theorem B353819 : Blo 119786 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B550471 : Blo 119786 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B2713171 : Blo 119786 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B1042105 : Blo 119786 1042105 := bstep (se 2 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 1042105 = 781579) B781579
theorem B1238813 : Blo 119786 1238813 := bstep (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) B464555
theorem B616571 : Blo 119786 616571 := bstep (se 1 (by rfl) ⟨462428, by rfl⟩ : syracuseStep 616571 = 924857) B924857
theorem B387305 : Blo 119786 387305 := bstep (se 2 (by rfl) ⟨145239, by rfl⟩ : syracuseStep 387305 = 290479) B290479
theorem B780815 : Blo 119786 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B5270123 : Blo 119786 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B584339 : Blo 119786 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B387919 : Blo 119786 387919 := bstep (se 1 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 387919 = 581879) B581879
theorem B879569 : Blo 119786 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B1174601 : Blo 119786 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B15756743 : Blo 119786 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B913193 : Blo 119786 913193 := bstep (se 2 (by rfl) ⟨342447, by rfl⟩ : syracuseStep 913193 = 684895) B684895
theorem B1896635 : Blo 119786 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B192775 : Blo 119786 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B1044839 : Blo 119786 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B258511 : Blo 119786 258511 := bstep (se 1 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 258511 = 387767) B387767
theorem B1176059 : Blo 119786 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B3535559 : Blo 119786 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B619325 : Blo 119786 619325 := bstep (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) B232247
theorem B1110941 : Blo 119786 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B1569719 : Blo 119786 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B390881 : Blo 119786 390881 := bstep (se 2 (by rfl) ⟨146580, by rfl⟩ : syracuseStep 390881 = 293161) B293161
theorem B8485013 : Blo 119786 8485013 := bstep (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) B397735
theorem B227623 : Blo 119786 227623 := bstep (se 1 (by rfl) ⟨170717, by rfl⟩ : syracuseStep 227623 = 341435) B341435
theorem B2095625 : Blo 119786 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B1309193 : Blo 119786 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B522899 : Blo 119786 522899 := bstep (se 1 (by rfl) ⟨392174, by rfl⟩ : syracuseStep 522899 = 784349) B784349
theorem B2194451 : Blo 119786 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B1408427 : Blo 119786 1408427 := bstep (se 1 (by rfl) ⟨1056320, by rfl⟩ : syracuseStep 1408427 = 2112641) B2112641
theorem B228815 : Blo 119786 228815 := bstep (se 1 (by rfl) ⟨171611, by rfl⟩ : syracuseStep 228815 = 343223) B343223
theorem B294623 : Blo 119786 294623 := bstep (se 1 (by rfl) ⟨220967, by rfl⟩ : syracuseStep 294623 = 441935) B441935
theorem B130847 : Blo 119786 130847 := bstep (se 1 (by rfl) ⟨98135, by rfl⟩ : syracuseStep 130847 = 196271) B196271
theorem B1048463 : Blo 119786 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B131015 : Blo 119786 131015 := bstep (se 1 (by rfl) ⟨98261, by rfl⟩ : syracuseStep 131015 = 196523) B196523
theorem B229331 : Blo 119786 229331 := bstep (se 1 (by rfl) ⟨171998, by rfl⟩ : syracuseStep 229331 = 343997) B343997
theorem B1049195 : Blo 119786 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B197407 : Blo 119786 197407 := bstep (se 1 (by rfl) ⟨148055, by rfl⟩ : syracuseStep 197407 = 296111) B296111
theorem B1409885 : Blo 119786 1409885 := bstep (se 3 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 1409885 = 528707) B528707
theorem B329341 : Blo 119786 329341 := bstep (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) B123503
theorem B329687 : Blo 119786 329687 := bstep (se 1 (by rfl) ⟨247265, by rfl⟩ : syracuseStep 329687 = 494531) B494531
theorem B1050853 : Blo 119786 1050853 := bstep (se 4 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 1050853 = 197035) B197035
theorem B690727 : Blo 119786 690727 := bstep (se 1 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 690727 = 1036091) B1036091
theorem B625319 : Blo 119786 625319 := bstep (se 1 (by rfl) ⟨468989, by rfl⟩ : syracuseStep 625319 = 937979) B937979
theorem B461609 : Blo 119786 461609 := bstep (se 2 (by rfl) ⟨173103, by rfl⟩ : syracuseStep 461609 = 346207) B346207
theorem B625643 : Blo 119786 625643 := bstep (se 1 (by rfl) ⟨469232, by rfl⟩ : syracuseStep 625643 = 938465) B938465
theorem B134815 : Blo 119786 134815 := bstep (se 1 (by rfl) ⟨101111, by rfl⟩ : syracuseStep 134815 = 202223) B202223
theorem B1478533 : Blo 119786 1478533 := bstep (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) B277225
theorem B135103 : Blo 119786 135103 := bstep (se 1 (by rfl) ⟨101327, by rfl⟩ : syracuseStep 135103 = 202655) B202655
theorem B463067 : Blo 119786 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B2068901 : Blo 119786 2068901 := bstep (se 4 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 2068901 = 387919) B387919
theorem B660215 : Blo 119786 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B1545479 : Blo 119786 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B202783 : Blo 119786 202783 := bstep (se 1 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 202783 = 304175) B304175
theorem B137551 : Blo 119786 137551 := bstep (se 1 (by rfl) ⟨103163, by rfl⟩ : syracuseStep 137551 = 206327) B206327
theorem B334163 : Blo 119786 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B235879 : Blo 119786 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B1972673 : Blo 119786 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B203215 : Blo 119786 203215 := bstep (se 1 (by rfl) ⟨152411, by rfl⟩ : syracuseStep 203215 = 304823) B304823
theorem B825875 : Blo 119786 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B138235 : Blo 119786 138235 := bstep (se 1 (by rfl) ⟨103676, by rfl⟩ : syracuseStep 138235 = 207353) B207353
theorem B138271 : Blo 119786 138271 := bstep (se 1 (by rfl) ⟨103703, by rfl⟩ : syracuseStep 138271 = 207407) B207407
theorem B3513415 : Blo 119786 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B203951 : Blo 119786 203951 := bstep (se 1 (by rfl) ⟨152963, by rfl⟩ : syracuseStep 203951 = 305927) B305927
theorem B138415 : Blo 119786 138415 := bstep (se 1 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 138415 = 207623) B207623
theorem B138559 : Blo 119786 138559 := bstep (se 1 (by rfl) ⟨103919, by rfl⟩ : syracuseStep 138559 = 207839) B207839
theorem B269819 : Blo 119786 269819 := bstep (se 1 (by rfl) ⟨202364, by rfl⟩ : syracuseStep 269819 = 404729) B404729
theorem B269927 : Blo 119786 269927 := bstep (se 1 (by rfl) ⟨202445, by rfl⟩ : syracuseStep 269927 = 404891) B404891
theorem B269999 : Blo 119786 269999 := bstep (se 1 (by rfl) ⟨202499, by rfl⟩ : syracuseStep 269999 = 404999) B404999
theorem B270089 : Blo 119786 270089 := bstep (se 2 (by rfl) ⟨101283, by rfl⟩ : syracuseStep 270089 = 202567) B202567
theorem B139135 : Blo 119786 139135 := bstep (se 1 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 139135 = 208703) B208703
theorem B696559 : Blo 119786 696559 := bstep (se 1 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 696559 = 1044839) B1044839
theorem B270719 : Blo 119786 270719 := bstep (se 1 (by rfl) ⟨203039, by rfl⟩ : syracuseStep 270719 = 406079) B406079
theorem B303497 : Blo 119786 303497 := bstep (se 2 (by rfl) ⟨113811, by rfl⟩ : syracuseStep 303497 = 227623) B227623
theorem B1024609 : Blo 119786 1024609 := bstep (se 2 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 1024609 = 768457) B768457
theorem B140383 : Blo 119786 140383 := bstep (se 1 (by rfl) ⟨105287, by rfl⟩ : syracuseStep 140383 = 210575) B210575
theorem B1418777 : Blo 119786 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B698975 : Blo 119786 698975 := bstep (se 1 (by rfl) ⟨524231, by rfl⟩ : syracuseStep 698975 = 1048463) B1048463
theorem B306089 : Blo 119786 306089 := bstep (se 2 (by rfl) ⟨114783, by rfl⟩ : syracuseStep 306089 = 229567) B229567
theorem B306119 : Blo 119786 306119 := bstep (se 1 (by rfl) ⟨229589, by rfl⟩ : syracuseStep 306119 = 459179) B459179
theorem B437737 : Blo 119786 437737 := bstep (se 2 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 437737 = 328303) B328303
theorem B306767 : Blo 119786 306767 := bstep (se 1 (by rfl) ⟨230075, by rfl⟩ : syracuseStep 306767 = 460151) B460151
theorem B307273 : Blo 119786 307273 := bstep (se 2 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 307273 = 230455) B230455
theorem B274535 : Blo 119786 274535 := bstep (se 1 (by rfl) ⟨205901, by rfl⟩ : syracuseStep 274535 = 411803) B411803
theorem B274715 : Blo 119786 274715 := bstep (se 1 (by rfl) ⟨206036, by rfl⟩ : syracuseStep 274715 = 412073) B412073
theorem B275111 : Blo 119786 275111 := bstep (se 1 (by rfl) ⟨206333, by rfl⟩ : syracuseStep 275111 = 412667) B412667
theorem B733961 : Blo 119786 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B701207 : Blo 119786 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B3617561 : Blo 119786 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B930689 : Blo 119786 930689 := bstep (se 2 (by rfl) ⟨349008, by rfl⟩ : syracuseStep 930689 = 698017) B698017
theorem B1389473 : Blo 119786 1389473 := bstep (se 2 (by rfl) ⟨521052, by rfl⟩ : syracuseStep 1389473 = 1042105) B1042105
theorem B669427 : Blo 119786 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B997363 : Blo 119786 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B309815 : Blo 119786 309815 := bstep (se 1 (by rfl) ⟨232361, by rfl⟩ : syracuseStep 309815 = 464723) B464723
theorem B277577 : Blo 119786 277577 := bstep (se 2 (by rfl) ⟨104091, by rfl⟩ : syracuseStep 277577 = 208183) B208183
theorem B2374877 : Blo 119786 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B179759 : Blo 119786 179759 := bstep (se 1 (by rfl) ⟨134819, by rfl⟩ : syracuseStep 179759 = 269639) B269639
theorem B179783 : Blo 119786 179783 := bstep (se 1 (by rfl) ⟨134837, by rfl⟩ : syracuseStep 179783 = 269675) B269675
theorem B179867 : Blo 119786 179867 := bstep (se 1 (by rfl) ⟨134900, by rfl⟩ : syracuseStep 179867 = 269801) B269801
theorem B278171 : Blo 119786 278171 := bstep (se 1 (by rfl) ⟨208628, by rfl⟩ : syracuseStep 278171 = 417257) B417257
theorem B179963 : Blo 119786 179963 := bstep (se 1 (by rfl) ⟨134972, by rfl⟩ : syracuseStep 179963 = 269945) B269945
theorem B278369 : Blo 119786 278369 := bstep (se 2 (by rfl) ⟨104388, by rfl⟩ : syracuseStep 278369 = 208777) B208777
theorem B311273 : Blo 119786 311273 := bstep (se 2 (by rfl) ⟨116727, by rfl⟩ : syracuseStep 311273 = 233455) B233455
theorem B2801729 : Blo 119786 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B180431 : Blo 119786 180431 := bstep (se 1 (by rfl) ⟨135323, by rfl⟩ : syracuseStep 180431 = 270647) B270647
theorem B704807 : Blo 119786 704807 := bstep (se 1 (by rfl) ⟨528605, by rfl⟩ : syracuseStep 704807 = 1057211) B1057211
theorem B409967 : Blo 119786 409967 := bstep (se 1 (by rfl) ⟨307475, by rfl⟩ : syracuseStep 409967 = 614951) B614951
theorem B344681 : Blo 119786 344681 := bstep (se 2 (by rfl) ⟨129255, by rfl⟩ : syracuseStep 344681 = 258511) B258511
theorem B181115 : Blo 119786 181115 := bstep (se 1 (by rfl) ⟨135836, by rfl⟩ : syracuseStep 181115 = 271673) B271673
theorem B934841 : Blo 119786 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B181241 : Blo 119786 181241 := bstep (se 2 (by rfl) ⟨67965, by rfl⟩ : syracuseStep 181241 = 135931) B135931
theorem B181295 : Blo 119786 181295 := bstep (se 1 (by rfl) ⟨135971, by rfl⟩ : syracuseStep 181295 = 271943) B271943
theorem B181415 : Blo 119786 181415 := bstep (se 1 (by rfl) ⟨136061, by rfl⟩ : syracuseStep 181415 = 272123) B272123
theorem B181607 : Blo 119786 181607 := bstep (se 1 (by rfl) ⟨136205, by rfl⟩ : syracuseStep 181607 = 272411) B272411
theorem B312731 : Blo 119786 312731 := bstep (se 1 (by rfl) ⟨234548, by rfl⟩ : syracuseStep 312731 = 469097) B469097
theorem B411047 : Blo 119786 411047 := bstep (se 1 (by rfl) ⟨308285, by rfl⟩ : syracuseStep 411047 = 616571) B616571
theorem B1558237 : Blo 119786 1558237 := bstep (se 3 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 1558237 = 584339) B584339
theorem B313151 : Blo 119786 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B182249 : Blo 119786 182249 := bstep (se 2 (by rfl) ⟨68343, by rfl⟩ : syracuseStep 182249 = 136687) B136687
theorem B1099777 : Blo 119786 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B182393 : Blo 119786 182393 := bstep (se 2 (by rfl) ⟨68397, by rfl⟩ : syracuseStep 182393 = 136795) B136795
theorem B10504495 : Blo 119786 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B182591 : Blo 119786 182591 := bstep (se 1 (by rfl) ⟨136943, by rfl⟩ : syracuseStep 182591 = 273887) B273887
theorem B182735 : Blo 119786 182735 := bstep (se 1 (by rfl) ⟨137051, by rfl⟩ : syracuseStep 182735 = 274103) B274103
theorem B182777 : Blo 119786 182777 := bstep (se 2 (by rfl) ⟨68541, by rfl⟩ : syracuseStep 182777 = 137083) B137083
theorem B608795 : Blo 119786 608795 := bstep (se 1 (by rfl) ⟨456596, by rfl⟩ : syracuseStep 608795 = 913193) B913193
theorem B182825 : Blo 119786 182825 := bstep (se 2 (by rfl) ⟨68559, by rfl⟩ : syracuseStep 182825 = 137119) B137119
theorem B936521 : Blo 119786 936521 := bstep (se 2 (by rfl) ⟨351195, by rfl⟩ : syracuseStep 936521 = 702391) B702391
theorem B1264423 : Blo 119786 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B183263 : Blo 119786 183263 := bstep (se 1 (by rfl) ⟨137447, by rfl⟩ : syracuseStep 183263 = 274895) B274895
theorem B1395701 : Blo 119786 1395701 := bstep (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) B130847
theorem B445625 : Blo 119786 445625 := bstep (se 2 (by rfl) ⟨167109, by rfl⟩ : syracuseStep 445625 = 334219) B334219
theorem B412883 : Blo 119786 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B2018533 : Blo 119786 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B412937 : Blo 119786 412937 := bstep (se 2 (by rfl) ⟨154851, by rfl⟩ : syracuseStep 412937 = 309703) B309703
theorem B740627 : Blo 119786 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B2051405 : Blo 119786 2051405 := bstep (se 3 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 2051405 = 769277) B769277
theorem B183707 : Blo 119786 183707 := bstep (se 1 (by rfl) ⟨137780, by rfl⟩ : syracuseStep 183707 = 275561) B275561
theorem B184073 : Blo 119786 184073 := bstep (se 2 (by rfl) ⟨69027, by rfl⟩ : syracuseStep 184073 = 138055) B138055
theorem B184127 : Blo 119786 184127 := bstep (se 1 (by rfl) ⟨138095, by rfl⟩ : syracuseStep 184127 = 276191) B276191
theorem B184367 : Blo 119786 184367 := bstep (se 1 (by rfl) ⟨138275, by rfl⟩ : syracuseStep 184367 = 276551) B276551
theorem B5656675 : Blo 119786 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B315695 : Blo 119786 315695 := bstep (se 1 (by rfl) ⟨236771, by rfl⟩ : syracuseStep 315695 = 473543) B473543
theorem B1397083 : Blo 119786 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B872795 : Blo 119786 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B348599 : Blo 119786 348599 := bstep (se 1 (by rfl) ⟨261449, by rfl⟩ : syracuseStep 348599 = 522899) B522899
theorem B184811 : Blo 119786 184811 := bstep (se 1 (by rfl) ⟨138608, by rfl⟩ : syracuseStep 184811 = 277217) B277217
theorem B184937 : Blo 119786 184937 := bstep (se 2 (by rfl) ⟨69351, by rfl⟩ : syracuseStep 184937 = 138703) B138703
theorem B184943 : Blo 119786 184943 := bstep (se 1 (by rfl) ⟨138707, by rfl⟩ : syracuseStep 184943 = 277415) B277415
theorem B1462967 : Blo 119786 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B185063 : Blo 119786 185063 := bstep (se 1 (by rfl) ⟨138797, by rfl⟩ : syracuseStep 185063 = 277595) B277595
theorem B185225 : Blo 119786 185225 := bstep (se 2 (by rfl) ⟨69459, by rfl⟩ : syracuseStep 185225 = 138919) B138919
theorem B938951 : Blo 119786 938951 := bstep (se 1 (by rfl) ⟨704213, by rfl⟩ : syracuseStep 938951 = 1408427) B1408427
theorem B152543 : Blo 119786 152543 := bstep (se 1 (by rfl) ⟨114407, by rfl⟩ : syracuseStep 152543 = 228815) B228815
theorem B414881 : Blo 119786 414881 := bstep (se 2 (by rfl) ⟨155580, by rfl⟩ : syracuseStep 414881 = 311161) B311161
theorem B349373 : Blo 119786 349373 := bstep (se 3 (by rfl) ⟨65507, by rfl⟩ : syracuseStep 349373 = 131015) B131015
theorem B611549 : Blo 119786 611549 := bstep (se 3 (by rfl) ⟨114665, by rfl⟩ : syracuseStep 611549 = 229331) B229331
theorem B120031 : Blo 119786 120031 := bstep (se 1 (by rfl) ⟨90023, by rfl⟩ : syracuseStep 120031 = 180047) B180047
theorem B185567 : Blo 119786 185567 := bstep (se 1 (by rfl) ⟨139175, by rfl⟩ : syracuseStep 185567 = 278351) B278351
theorem B185609 : Blo 119786 185609 := bstep (se 2 (by rfl) ⟨69603, by rfl⟩ : syracuseStep 185609 = 139207) B139207
theorem B120111 : Blo 119786 120111 := bstep (se 1 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 120111 = 180167) B180167
theorem B120351 : Blo 119786 120351 := bstep (se 1 (by rfl) ⟨90263, by rfl⟩ : syracuseStep 120351 = 180527) B180527
theorem B1660495 : Blo 119786 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B120511 : Blo 119786 120511 := bstep (se 1 (by rfl) ⟨90383, by rfl⟩ : syracuseStep 120511 = 180767) B180767
theorem B153671 : Blo 119786 153671 := bstep (se 1 (by rfl) ⟨115253, by rfl⟩ : syracuseStep 153671 = 230507) B230507
theorem B120959 : Blo 119786 120959 := bstep (se 1 (by rfl) ⟨90719, by rfl⟩ : syracuseStep 120959 = 181439) B181439
theorem B350399 : Blo 119786 350399 := bstep (se 1 (by rfl) ⟨262799, by rfl⟩ : syracuseStep 350399 = 525599) B525599
theorem B121055 : Blo 119786 121055 := bstep (se 1 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 121055 = 181583) B181583
theorem B121115 : Blo 119786 121115 := bstep (se 1 (by rfl) ⟨90836, by rfl⟩ : syracuseStep 121115 = 181673) B181673
theorem B1038689 : Blo 119786 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B121215 : Blo 119786 121215 := bstep (se 1 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 121215 = 181823) B181823
theorem B121243 : Blo 119786 121243 := bstep (se 1 (by rfl) ⟨90932, by rfl⟩ : syracuseStep 121243 = 181865) B181865
theorem B3824047 : Blo 119786 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B285191 : Blo 119786 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B3136157 : Blo 119786 3136157 := bstep (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) B1176059
theorem B121535 : Blo 119786 121535 := bstep (se 1 (by rfl) ⟨91151, by rfl⟩ : syracuseStep 121535 = 182303) B182303
theorem B940787 : Blo 119786 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B121663 : Blo 119786 121663 := bstep (se 1 (by rfl) ⟨91247, by rfl⟩ : syracuseStep 121663 = 182495) B182495
theorem B121703 : Blo 119786 121703 := bstep (se 1 (by rfl) ⟨91277, by rfl⟩ : syracuseStep 121703 = 182555) B182555
theorem B613331 : Blo 119786 613331 := bstep (se 1 (by rfl) ⟨459998, by rfl⟩ : syracuseStep 613331 = 919997) B919997
theorem B121919 : Blo 119786 121919 := bstep (se 1 (by rfl) ⟨91439, by rfl⟩ : syracuseStep 121919 = 182879) B182879
theorem B122107 : Blo 119786 122107 := bstep (se 1 (by rfl) ⟨91580, by rfl⟩ : syracuseStep 122107 = 183161) B183161
theorem B122139 : Blo 119786 122139 := bstep (se 1 (by rfl) ⟨91604, by rfl⟩ : syracuseStep 122139 = 183209) B183209
theorem B351515 : Blo 119786 351515 := bstep (se 1 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 351515 = 527273) B527273
theorem B122239 : Blo 119786 122239 := bstep (se 1 (by rfl) ⟨91679, by rfl⟩ : syracuseStep 122239 = 183359) B183359
theorem B449975 : Blo 119786 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B122607 : Blo 119786 122607 := bstep (se 1 (by rfl) ⟨91955, by rfl⟩ : syracuseStep 122607 = 183911) B183911
theorem B122863 : Blo 119786 122863 := bstep (se 1 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 122863 = 184295) B184295
theorem B122943 : Blo 119786 122943 := bstep (se 1 (by rfl) ⟨92207, by rfl⟩ : syracuseStep 122943 = 184415) B184415
theorem B122951 : Blo 119786 122951 := bstep (se 1 (by rfl) ⟨92213, by rfl⟩ : syracuseStep 122951 = 184427) B184427
theorem B122983 : Blo 119786 122983 := bstep (se 1 (by rfl) ⟨92237, by rfl⟩ : syracuseStep 122983 = 184475) B184475
theorem B155839 : Blo 119786 155839 := bstep (se 1 (by rfl) ⟨116879, by rfl⟩ : syracuseStep 155839 = 233759) B233759
theorem B123551 : Blo 119786 123551 := bstep (se 1 (by rfl) ⟨92663, by rfl⟩ : syracuseStep 123551 = 185327) B185327
theorem B157339 : Blo 119786 157339 := bstep (se 1 (by rfl) ⟨118004, by rfl⟩ : syracuseStep 157339 = 236009) B236009
theorem B257033 : Blo 119786 257033 := bstep (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) B192775
theorem B912707 : Blo 119786 912707 := bstep (se 1 (by rfl) ⟨684530, by rfl⟩ : syracuseStep 912707 = 1369061) B1369061
theorem B1371977 : Blo 119786 1371977 := bstep (se 2 (by rfl) ⟨514491, by rfl⟩ : syracuseStep 1371977 = 1028983) B1028983
theorem B258203 : Blo 119786 258203 := bstep (se 1 (by rfl) ⟨193652, by rfl⟩ : syracuseStep 258203 = 387305) B387305
theorem B749821 : Blo 119786 749821 := bstep (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) B281183
theorem B520543 : Blo 119786 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B3633547 : Blo 119786 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B3469873 : Blo 119786 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B586379 : Blo 119786 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B783067 : Blo 119786 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B619649 : Blo 119786 619649 := bstep (se 2 (by rfl) ⟨232368, by rfl⟩ : syracuseStep 619649 = 464737) B464737
theorem B2357039 : Blo 119786 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B1046479 : Blo 119786 1046479 := bstep (se 1 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 1046479 = 1569719) B1569719
theorem B1538351 : Blo 119786 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B260587 : Blo 119786 260587 := bstep (se 1 (by rfl) ⟨195440, by rfl⟩ : syracuseStep 260587 = 390881) B390881
theorem B294391 : Blo 119786 294391 := bstep (se 1 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 294391 = 441587) B441587
theorem B556541 : Blo 119786 556541 := bstep (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) B208703
theorem B687811 : Blo 119786 687811 := bstep (se 1 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 687811 = 1031717) B1031717
theorem B196415 : Blo 119786 196415 := bstep (se 1 (by rfl) ⟨147311, by rfl⟩ : syracuseStep 196415 = 294623) B294623
theorem B622525 : Blo 119786 622525 := bstep (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) B233447
theorem B1867819 : Blo 119786 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B229787 : Blo 119786 229787 := bstep (se 1 (by rfl) ⟨172340, by rfl⟩ : syracuseStep 229787 = 344681) B344681
theorem B623227 : Blo 119786 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B624347 : Blo 119786 624347 := bstep (se 1 (by rfl) ⟨468260, by rfl⟩ : syracuseStep 624347 = 936521) B936521
theorem B297083 : Blo 119786 297083 := bstep (se 1 (by rfl) ⟨222812, by rfl⟩ : syracuseStep 297083 = 445625) B445625
theorem B493751 : Blo 119786 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B1379267 : Blo 119786 1379267 := bstep (se 1 (by rfl) ⟨1034450, by rfl⟩ : syracuseStep 1379267 = 2068901) B2068901
theorem B232399 : Blo 119786 232399 := bstep (se 1 (by rfl) ⟨174299, by rfl⟩ : syracuseStep 232399 = 348599) B348599
theorem B625967 : Blo 119786 625967 := bstep (se 1 (by rfl) ⟨469475, by rfl⟩ : syracuseStep 625967 = 938951) B938951
theorem B920969 : Blo 119786 920969 := bstep (se 2 (by rfl) ⟨345363, by rfl⟩ : syracuseStep 920969 = 690727) B690727
theorem B233599 : Blo 119786 233599 := bstep (se 1 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 233599 = 350399) B350399
theorem B1052837 : Blo 119786 1052837 := bstep (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) B197407
theorem B692459 : Blo 119786 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B1315115 : Blo 119786 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B2691377 : Blo 119786 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B627191 : Blo 119786 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B135967 : Blo 119786 135967 := bstep (se 1 (by rfl) ⟨101975, by rfl⟩ : syracuseStep 135967 = 203951) B203951
theorem B234343 : Blo 119786 234343 := bstep (se 1 (by rfl) ⟨175757, by rfl⟩ : syracuseStep 234343 = 351515) B351515
theorem B1971377 : Blo 119786 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B7542233 : Blo 119786 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B202331 : Blo 119786 202331 := bstep (se 1 (by rfl) ⟨151748, by rfl⟩ : syracuseStep 202331 = 303497) B303497
theorem B694057 : Blo 119786 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B4626497 : Blo 119786 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B891101 : Blo 119786 891101 := bstep (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) B334163
theorem B465983 : Blo 119786 465983 := bstep (se 1 (by rfl) ⟨349487, by rfl⟩ : syracuseStep 465983 = 698975) B698975
theorem B204059 : Blo 119786 204059 := bstep (se 1 (by rfl) ⟨153044, by rfl⟩ : syracuseStep 204059 = 306089) B306089
theorem B204079 : Blo 119786 204079 := bstep (se 1 (by rfl) ⟨153059, by rfl⟩ : syracuseStep 204079 = 306119) B306119
theorem B204511 : Blo 119786 204511 := bstep (se 1 (by rfl) ⟨153383, by rfl⟩ : syracuseStep 204511 = 306767) B306767
theorem B270377 : Blo 119786 270377 := bstep (se 2 (by rfl) ⟨101391, by rfl⟩ : syracuseStep 270377 = 202783) B202783
theorem B172135 : Blo 119786 172135 := bstep (se 1 (by rfl) ⟨129101, by rfl⟩ : syracuseStep 172135 = 258203) B258203
theorem B467471 : Blo 119786 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B6333005 : Blo 119786 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B270953 : Blo 119786 270953 := bstep (se 2 (by rfl) ⟨101607, by rfl⟩ : syracuseStep 270953 = 203215) B203215
theorem B926315 : Blo 119786 926315 := bstep (se 1 (by rfl) ⟨694736, by rfl⟩ : syracuseStep 926315 = 1389473) B1389473
theorem B1025567 : Blo 119786 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B206543 : Blo 119786 206543 := bstep (se 1 (by rfl) ⟨154907, by rfl⟩ : syracuseStep 206543 = 309815) B309815
theorem B371027 : Blo 119786 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B830033 : Blo 119786 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B207515 : Blo 119786 207515 := bstep (se 1 (by rfl) ⟨155636, by rfl⟩ : syracuseStep 207515 = 311273) B311273
theorem B469871 : Blo 119786 469871 := bstep (se 1 (by rfl) ⟨352403, by rfl⟩ : syracuseStep 469871 = 704807) B704807
theorem B273311 : Blo 119786 273311 := bstep (se 1 (by rfl) ⟨204983, by rfl⟩ : syracuseStep 273311 = 409967) B409967
theorem B207785 : Blo 119786 207785 := bstep (se 2 (by rfl) ⟨77919, by rfl⟩ : syracuseStep 207785 = 155839) B155839
theorem B928745 : Blo 119786 928745 := bstep (se 2 (by rfl) ⟨348279, by rfl⟩ : syracuseStep 928745 = 696559) B696559
theorem B699463 : Blo 119786 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B208487 : Blo 119786 208487 := bstep (se 1 (by rfl) ⟨156365, by rfl⟩ : syracuseStep 208487 = 312731) B312731
theorem B274031 : Blo 119786 274031 := bstep (se 1 (by rfl) ⟨205523, by rfl⟩ : syracuseStep 274031 = 411047) B411047
theorem B405863 : Blo 119786 405863 := bstep (se 1 (by rfl) ⟨304397, by rfl⟩ : syracuseStep 405863 = 608795) B608795
theorem B307739 : Blo 119786 307739 := bstep (se 1 (by rfl) ⟨230804, by rfl⟩ : syracuseStep 307739 = 461609) B461609
theorem B1258021 : Blo 119786 1258021 := bstep (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) B235879
theorem B930467 : Blo 119786 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B275255 : Blo 119786 275255 := bstep (se 1 (by rfl) ⟨206441, by rfl⟩ : syracuseStep 275255 = 412883) B412883
theorem B439121 : Blo 119786 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B275291 : Blo 119786 275291 := bstep (se 1 (by rfl) ⟨206468, by rfl⟩ : syracuseStep 275291 = 412937) B412937
theorem B209785 : Blo 119786 209785 := bstep (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) B157339
theorem B2077649 : Blo 119786 2077649 := bstep (se 2 (by rfl) ⟨779118, by rfl⟩ : syracuseStep 2077649 = 1558237) B1558237
theorem B406781 : Blo 119786 406781 := bstep (se 3 (by rfl) ⟨76271, by rfl⟩ : syracuseStep 406781 = 152543) B152543
theorem B308711 : Blo 119786 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B14005993 : Blo 119786 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B931661 : Blo 119786 931661 := bstep (se 3 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 931661 = 349373) B349373
theorem B440143 : Blo 119786 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B276587 : Blo 119786 276587 := bstep (se 1 (by rfl) ⟨207440, by rfl⟩ : syracuseStep 276587 = 414881) B414881
theorem B407699 : Blo 119786 407699 := bstep (se 1 (by rfl) ⟨305774, by rfl⟩ : syracuseStep 407699 = 611549) B611549
theorem B1030319 : Blo 119786 1030319 := bstep (se 1 (by rfl) ⟨772739, by rfl⟩ : syracuseStep 1030319 = 1545479) B1545479
theorem B1685897 : Blo 119786 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B408887 : Blo 119786 408887 := bstep (se 1 (by rfl) ⟨306665, by rfl⟩ : syracuseStep 408887 = 613331) B613331
theorem B835069 : Blo 119786 835069 := bstep (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) B313151
theorem B179753 : Blo 119786 179753 := bstep (se 2 (by rfl) ⟨67407, by rfl⟩ : syracuseStep 179753 = 134815) B134815
theorem B179879 : Blo 119786 179879 := bstep (se 1 (by rfl) ⟨134909, by rfl⟩ : syracuseStep 179879 = 269819) B269819
theorem B179951 : Blo 119786 179951 := bstep (se 1 (by rfl) ⟨134963, by rfl⟩ : syracuseStep 179951 = 269927) B269927
theorem B179999 : Blo 119786 179999 := bstep (se 1 (by rfl) ⟨134999, by rfl⟩ : syracuseStep 179999 = 269999) B269999
theorem B180059 : Blo 119786 180059 := bstep (se 1 (by rfl) ⟨135044, by rfl⟩ : syracuseStep 180059 = 270089) B270089
theorem B180137 : Blo 119786 180137 := bstep (se 2 (by rfl) ⟨67551, by rfl⟩ : syracuseStep 180137 = 135103) B135103
theorem B409697 : Blo 119786 409697 := bstep (se 2 (by rfl) ⟨153636, by rfl⟩ : syracuseStep 409697 = 307273) B307273
theorem B409789 : Blo 119786 409789 := bstep (se 3 (by rfl) ⟨76835, by rfl⟩ : syracuseStep 409789 = 153671) B153671
theorem B180479 : Blo 119786 180479 := bstep (se 1 (by rfl) ⟨135359, by rfl⟩ : syracuseStep 180479 = 270719) B270719
theorem B999761 : Blo 119786 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B2213993 : Blo 119786 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B608471 : Blo 119786 608471 := bstep (se 1 (by rfl) ⟨456353, by rfl⟩ : syracuseStep 608471 = 912707) B912707
theorem B1395305 : Blo 119786 1395305 := bstep (se 2 (by rfl) ⟨523239, by rfl⟩ : syracuseStep 1395305 = 1046479) B1046479
theorem B1329817 : Blo 119786 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B183023 : Blo 119786 183023 := bstep (se 1 (by rfl) ⟨137267, by rfl⟩ : syracuseStep 183023 = 274535) B274535
theorem B183143 : Blo 119786 183143 := bstep (se 1 (by rfl) ⟨137357, by rfl⟩ : syracuseStep 183143 = 274715) B274715
theorem B183401 : Blo 119786 183401 := bstep (se 2 (by rfl) ⟨68775, by rfl⟩ : syracuseStep 183401 = 137551) B137551
theorem B183407 : Blo 119786 183407 := bstep (se 1 (by rfl) ⟨137555, by rfl⟩ : syracuseStep 183407 = 275111) B275111
theorem B2411707 : Blo 119786 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B5098729 : Blo 119786 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B347449 : Blo 119786 347449 := bstep (se 2 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 347449 = 260587) B260587
theorem B413099 : Blo 119786 413099 := bstep (se 1 (by rfl) ⟨309824, by rfl⟩ : syracuseStep 413099 = 619649) B619649
theorem B1199933 : Blo 119786 1199933 := bstep (se 3 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 1199933 = 449975) B449975
theorem B184313 : Blo 119786 184313 := bstep (se 2 (by rfl) ⟨69117, by rfl⟩ : syracuseStep 184313 = 138235) B138235
theorem B184361 : Blo 119786 184361 := bstep (se 2 (by rfl) ⟨69135, by rfl⟩ : syracuseStep 184361 = 138271) B138271
theorem B184553 : Blo 119786 184553 := bstep (se 2 (by rfl) ⟨69207, by rfl⟩ : syracuseStep 184553 = 138415) B138415
theorem B184745 : Blo 119786 184745 := bstep (se 2 (by rfl) ⟨69279, by rfl⟩ : syracuseStep 184745 = 138559) B138559
theorem B185051 : Blo 119786 185051 := bstep (se 1 (by rfl) ⟨138788, by rfl⟩ : syracuseStep 185051 = 277577) B277577
theorem B119839 : Blo 119786 119839 := bstep (se 1 (by rfl) ⟨89879, by rfl⟩ : syracuseStep 119839 = 179759) B179759
theorem B119855 : Blo 119786 119855 := bstep (se 1 (by rfl) ⟨89891, by rfl⟩ : syracuseStep 119855 = 179783) B179783
theorem B119911 : Blo 119786 119911 := bstep (se 1 (by rfl) ⟨89933, by rfl⟩ : syracuseStep 119911 = 179867) B179867
theorem B185447 : Blo 119786 185447 := bstep (se 1 (by rfl) ⟨139085, by rfl⟩ : syracuseStep 185447 = 278171) B278171
theorem B119975 : Blo 119786 119975 := bstep (se 1 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 119975 = 179963) B179963
theorem B185513 : Blo 119786 185513 := bstep (se 2 (by rfl) ⟨69567, by rfl⟩ : syracuseStep 185513 = 139135) B139135
theorem B185579 : Blo 119786 185579 := bstep (se 1 (by rfl) ⟨139184, by rfl⟩ : syracuseStep 185579 = 278369) B278369
theorem B120287 : Blo 119786 120287 := bstep (se 1 (by rfl) ⟨90215, by rfl⟩ : syracuseStep 120287 = 180431) B180431
theorem B939923 : Blo 119786 939923 := bstep (se 1 (by rfl) ⟨704942, by rfl⟩ : syracuseStep 939923 = 1409885) B1409885
theorem B120743 : Blo 119786 120743 := bstep (se 1 (by rfl) ⟨90557, by rfl⟩ : syracuseStep 120743 = 181115) B181115
theorem B120827 : Blo 119786 120827 := bstep (se 1 (by rfl) ⟨90620, by rfl⟩ : syracuseStep 120827 = 181241) B181241
theorem B120863 : Blo 119786 120863 := bstep (se 1 (by rfl) ⟨90647, by rfl⟩ : syracuseStep 120863 = 181295) B181295
theorem B120943 : Blo 119786 120943 := bstep (se 1 (by rfl) ⟨90707, by rfl⟩ : syracuseStep 120943 = 181415) B181415
theorem B841853 : Blo 119786 841853 := bstep (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) B315695
theorem B1366145 : Blo 119786 1366145 := bstep (se 2 (by rfl) ⟨512304, by rfl⟩ : syracuseStep 1366145 = 1024609) B1024609
theorem B121071 : Blo 119786 121071 := bstep (se 1 (by rfl) ⟨90803, by rfl⟩ : syracuseStep 121071 = 181607) B181607
theorem B219791 : Blo 119786 219791 := bstep (se 1 (by rfl) ⟨164843, by rfl⟩ : syracuseStep 219791 = 329687) B329687
theorem B121499 : Blo 119786 121499 := bstep (se 1 (by rfl) ⟨91124, by rfl⟩ : syracuseStep 121499 = 182249) B182249
theorem B121595 : Blo 119786 121595 := bstep (se 1 (by rfl) ⟨91196, by rfl⟩ : syracuseStep 121595 = 182393) B182393
theorem B187177 : Blo 119786 187177 := bstep (se 2 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 187177 = 140383) B140383
theorem B121727 : Blo 119786 121727 := bstep (se 1 (by rfl) ⟨91295, by rfl⟩ : syracuseStep 121727 = 182591) B182591
theorem B121823 : Blo 119786 121823 := bstep (se 1 (by rfl) ⟨91367, by rfl⟩ : syracuseStep 121823 = 182735) B182735
theorem B121851 : Blo 119786 121851 := bstep (se 1 (by rfl) ⟨91388, by rfl⟩ : syracuseStep 121851 = 182777) B182777
theorem B121883 : Blo 119786 121883 := bstep (se 1 (by rfl) ⟨91412, by rfl⟩ : syracuseStep 121883 = 182825) B182825
theorem B416879 : Blo 119786 416879 := bstep (se 1 (by rfl) ⟨312659, by rfl⟩ : syracuseStep 416879 = 625319) B625319
theorem B122175 : Blo 119786 122175 := bstep (se 1 (by rfl) ⟨91631, by rfl⟩ : syracuseStep 122175 = 183263) B183263
theorem B417095 : Blo 119786 417095 := bstep (se 1 (by rfl) ⟨312821, by rfl⟩ : syracuseStep 417095 = 625643) B625643
theorem B1957229 : Blo 119786 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B1367603 : Blo 119786 1367603 := bstep (se 1 (by rfl) ⟨1025702, by rfl⟩ : syracuseStep 1367603 = 2051405) B2051405
theorem B122471 : Blo 119786 122471 := bstep (se 1 (by rfl) ⟨91853, by rfl⟩ : syracuseStep 122471 = 183707) B183707
theorem B122715 : Blo 119786 122715 := bstep (se 1 (by rfl) ⟨92036, by rfl⟩ : syracuseStep 122715 = 184073) B184073
theorem B122751 : Blo 119786 122751 := bstep (se 1 (by rfl) ⟨92063, by rfl⟩ : syracuseStep 122751 = 184127) B184127
theorem B1466369 : Blo 119786 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B122911 : Blo 119786 122911 := bstep (se 1 (by rfl) ⟨92183, by rfl⟩ : syracuseStep 122911 = 184367) B184367
theorem B581863 : Blo 119786 581863 := bstep (se 1 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 581863 = 872795) B872795
theorem B1401137 : Blo 119786 1401137 := bstep (se 2 (by rfl) ⟨525426, by rfl⟩ : syracuseStep 1401137 = 1050853) B1050853
theorem B123207 : Blo 119786 123207 := bstep (se 1 (by rfl) ⟨92405, by rfl⟩ : syracuseStep 123207 = 184811) B184811
theorem B123291 : Blo 119786 123291 := bstep (se 1 (by rfl) ⟨92468, by rfl⟩ : syracuseStep 123291 = 184937) B184937
theorem B123295 : Blo 119786 123295 := bstep (se 1 (by rfl) ⟨92471, by rfl⟩ : syracuseStep 123295 = 184943) B184943
theorem B975311 : Blo 119786 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B123375 : Blo 119786 123375 := bstep (se 1 (by rfl) ⟨92531, by rfl⟩ : syracuseStep 123375 = 185063) B185063
theorem B123483 : Blo 119786 123483 := bstep (se 1 (by rfl) ⟨92612, by rfl⟩ : syracuseStep 123483 = 185225) B185225
theorem B123711 : Blo 119786 123711 := bstep (se 1 (by rfl) ⟨92783, by rfl⟩ : syracuseStep 123711 = 185567) B185567
theorem B123739 : Blo 119786 123739 := bstep (se 1 (by rfl) ⟨92804, by rfl⟩ : syracuseStep 123739 = 185609) B185609
theorem B190127 : Blo 119786 190127 := bstep (se 1 (by rfl) ⟨142595, by rfl⟩ : syracuseStep 190127 = 285191) B285191
theorem B550583 : Blo 119786 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B2090771 : Blo 119786 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B583649 : Blo 119786 583649 := bstep (se 2 (by rfl) ⟨218868, by rfl⟩ : syracuseStep 583649 = 437737) B437737
theorem B1862777 : Blo 119786 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B4844729 : Blo 119786 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B1044089 : Blo 119786 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B945851 : Blo 119786 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B914651 : Blo 119786 914651 := bstep (se 1 (by rfl) ⟨685988, by rfl⟩ : syracuseStep 914651 = 1371977) B1371977
theorem B685421 : Blo 119786 685421 := bstep (se 3 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 685421 = 257033) B257033
theorem B390919 : Blo 119786 390919 := bstep (se 1 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 390919 = 586379) B586379
theorem B620459 : Blo 119786 620459 := bstep (se 1 (by rfl) ⟨465344, by rfl⟩ : syracuseStep 620459 = 930689) B930689
theorem B1571359 : Blo 119786 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B3570277 : Blo 119786 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B4684553 : Blo 119786 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B392521 : Blo 119786 392521 := bstep (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) B294391
theorem B917081 : Blo 119786 917081 := bstep (se 2 (by rfl) ⟨343905, by rfl⟩ : syracuseStep 917081 = 687811) B687811
theorem B130943 : Blo 119786 130943 := bstep (se 1 (by rfl) ⟨98207, by rfl⟩ : syracuseStep 130943 = 196415) B196415
theorem B2490425 : Blo 119786 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B918053 : Blo 119786 918053 := bstep (se 4 (by rfl) ⟨86067, by rfl⟩ : syracuseStep 918053 = 172135) B172135
theorem B1475995 : Blo 119786 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B198055 : Blo 119786 198055 := bstep (se 1 (by rfl) ⟨148541, by rfl⟩ : syracuseStep 198055 = 297083) B297083
theorem B329167 : Blo 119786 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B919511 : Blo 119786 919511 := bstep (se 1 (by rfl) ⟨689633, by rfl⟩ : syracuseStep 919511 = 1379267) B1379267
theorem B461639 : Blo 119786 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B1314251 : Blo 119786 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B1773089 : Blo 119786 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B134887 : Blo 119786 134887 := bstep (se 1 (by rfl) ⟨101165, by rfl⟩ : syracuseStep 134887 = 202331) B202331
theorem B626615 : Blo 119786 626615 := bstep (se 1 (by rfl) ⟨469961, by rfl⟩ : syracuseStep 626615 = 939923) B939923
theorem B3084331 : Blo 119786 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B594067 : Blo 119786 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B3215609 : Blo 119786 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B463265 : Blo 119786 463265 := bstep (se 2 (by rfl) ⟨173724, by rfl⟩ : syracuseStep 463265 = 347449) B347449
theorem B136039 : Blo 119786 136039 := bstep (se 1 (by rfl) ⟨102029, by rfl⟩ : syracuseStep 136039 = 204059) B204059
theorem B1677361 : Blo 119786 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B367055 : Blo 119786 367055 := bstep (se 1 (by rfl) ⟨275291, by rfl⟩ : syracuseStep 367055 = 550583) B550583
theorem B137695 : Blo 119786 137695 := bstep (se 1 (by rfl) ⟨103271, by rfl⟩ : syracuseStep 137695 = 206543) B206543
theorem B138343 : Blo 119786 138343 := bstep (se 1 (by rfl) ⟨103757, by rfl⟩ : syracuseStep 138343 = 207515) B207515
theorem B138523 : Blo 119786 138523 := bstep (se 1 (by rfl) ⟨103892, by rfl⟩ : syracuseStep 138523 = 207785) B207785
theorem B925409 : Blo 119786 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B138991 : Blo 119786 138991 := bstep (se 1 (by rfl) ⟨104243, by rfl⟩ : syracuseStep 138991 = 208487) B208487
theorem B696059 : Blo 119786 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B270575 : Blo 119786 270575 := bstep (se 1 (by rfl) ⟨202931, by rfl⟩ : syracuseStep 270575 = 405863) B405863
theorem B205159 : Blo 119786 205159 := bstep (se 1 (by rfl) ⟨153869, by rfl⟩ : syracuseStep 205159 = 307739) B307739
theorem B12919277 : Blo 119786 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B1385099 : Blo 119786 1385099 := bstep (se 1 (by rfl) ⟨1038824, by rfl⟩ : syracuseStep 1385099 = 2077649) B2077649
theorem B4760369 : Blo 119786 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B271187 : Blo 119786 271187 := bstep (se 1 (by rfl) ⟨203390, by rfl⟩ : syracuseStep 271187 = 406781) B406781
theorem B205807 : Blo 119786 205807 := bstep (se 1 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 205807 = 308711) B308711
theorem B271799 : Blo 119786 271799 := bstep (se 1 (by rfl) ⟨203849, by rfl⟩ : syracuseStep 271799 = 407699) B407699
theorem B1123931 : Blo 119786 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B272105 : Blo 119786 272105 := bstep (se 2 (by rfl) ⟨102039, by rfl⟩ : syracuseStep 272105 = 204079) B204079
theorem B3123035 : Blo 119786 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B272591 : Blo 119786 272591 := bstep (se 1 (by rfl) ⟨204443, by rfl⟩ : syracuseStep 272591 = 408887) B408887
theorem B272681 : Blo 119786 272681 := bstep (se 2 (by rfl) ⟨102255, by rfl⟩ : syracuseStep 272681 = 204511) B204511
theorem B273131 : Blo 119786 273131 := bstep (se 1 (by rfl) ⟨204848, by rfl⟩ : syracuseStep 273131 = 409697) B409697
theorem B830969 : Blo 119786 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B2666029 : Blo 119786 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B405647 : Blo 119786 405647 := bstep (se 1 (by rfl) ⟨304235, by rfl⟩ : syracuseStep 405647 = 608471) B608471
theorem B930203 : Blo 119786 930203 := bstep (se 1 (by rfl) ⟨697652, by rfl⟩ : syracuseStep 930203 = 1395305) B1395305
theorem B275399 : Blo 119786 275399 := bstep (se 1 (by rfl) ⟨206549, by rfl⟩ : syracuseStep 275399 = 413099) B413099
theorem B799955 : Blo 119786 799955 := bstep (se 1 (by rfl) ⟨599966, by rfl⟩ : syracuseStep 799955 = 1199933) B1199933
theorem B701891 : Blo 119786 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B5028155 : Blo 119786 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B309865 : Blo 119786 309865 := bstep (se 2 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 309865 = 232399) B232399
theorem B932617 : Blo 119786 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B6798305 : Blo 119786 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B507005 : Blo 119786 507005 := bstep (se 3 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 507005 = 190127) B190127
theorem B310655 : Blo 119786 310655 := bstep (se 1 (by rfl) ⟨232991, by rfl⟩ : syracuseStep 310655 = 465983) B465983
theorem B277919 : Blo 119786 277919 := bstep (se 1 (by rfl) ⟨208439, by rfl⟩ : syracuseStep 277919 = 416879) B416879
theorem B278063 : Blo 119786 278063 := bstep (se 1 (by rfl) ⟨208547, by rfl⟩ : syracuseStep 278063 = 417095) B417095
theorem B180251 : Blo 119786 180251 := bstep (se 1 (by rfl) ⟨135188, by rfl⟩ : syracuseStep 180251 = 270377) B270377
theorem B311465 : Blo 119786 311465 := bstep (se 2 (by rfl) ⟨116799, by rfl⟩ : syracuseStep 311465 = 233599) B233599
theorem B934091 : Blo 119786 934091 := bstep (se 1 (by rfl) ⟨700568, by rfl⟩ : syracuseStep 934091 = 1401137) B1401137
theorem B2244941 : Blo 119786 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B311647 : Blo 119786 311647 := bstep (se 1 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 311647 = 467471) B467471
theorem B180635 : Blo 119786 180635 := bstep (se 1 (by rfl) ⟨135476, by rfl⟩ : syracuseStep 180635 = 270953) B270953
theorem B181289 : Blo 119786 181289 := bstep (se 2 (by rfl) ⟨67983, by rfl⟩ : syracuseStep 181289 = 135967) B135967
theorem B312457 : Blo 119786 312457 := bstep (se 2 (by rfl) ⟨117171, by rfl⟩ : syracuseStep 312457 = 234343) B234343
theorem B279713 : Blo 119786 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B1393847 : Blo 119786 1393847 := bstep (se 1 (by rfl) ⟨1045385, by rfl⟩ : syracuseStep 1393847 = 2090771) B2090771
theorem B247351 : Blo 119786 247351 := bstep (se 1 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 247351 = 371027) B371027
theorem B313247 : Blo 119786 313247 := bstep (se 1 (by rfl) ⟨234935, by rfl⟩ : syracuseStep 313247 = 469871) B469871
theorem B182207 : Blo 119786 182207 := bstep (se 1 (by rfl) ⟨136655, by rfl⟩ : syracuseStep 182207 = 273311) B273311
theorem B182687 : Blo 119786 182687 := bstep (se 1 (by rfl) ⟨137015, by rfl⟩ : syracuseStep 182687 = 274031) B274031
theorem B183503 : Blo 119786 183503 := bstep (se 1 (by rfl) ⟨137627, by rfl⟩ : syracuseStep 183503 = 275255) B275255
theorem B183527 : Blo 119786 183527 := bstep (se 1 (by rfl) ⟨137645, by rfl⟩ : syracuseStep 183527 = 275291) B275291
theorem B609767 : Blo 119786 609767 := bstep (se 1 (by rfl) ⟨457325, by rfl⟩ : syracuseStep 609767 = 914651) B914651
theorem B249569 : Blo 119786 249569 := bstep (se 2 (by rfl) ⟨93588, by rfl⟩ : syracuseStep 249569 = 187177) B187177
theorem B413639 : Blo 119786 413639 := bstep (se 1 (by rfl) ⟨310229, by rfl⟩ : syracuseStep 413639 = 620459) B620459
theorem B184391 : Blo 119786 184391 := bstep (se 1 (by rfl) ⟨138293, by rfl⟩ : syracuseStep 184391 = 276587) B276587
theorem B2347429 : Blo 119786 2347429 := bstep (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) B440143
theorem B349181 : Blo 119786 349181 := bstep (se 3 (by rfl) ⟨65471, by rfl⟩ : syracuseStep 349181 = 130943) B130943
theorem B119835 : Blo 119786 119835 := bstep (se 1 (by rfl) ⟨89876, by rfl⟩ : syracuseStep 119835 = 179753) B179753
theorem B611387 : Blo 119786 611387 := bstep (se 1 (by rfl) ⟨458540, by rfl⟩ : syracuseStep 611387 = 917081) B917081
theorem B119919 : Blo 119786 119919 := bstep (se 1 (by rfl) ⟨89939, by rfl⟩ : syracuseStep 119919 = 179879) B179879
theorem B119967 : Blo 119786 119967 := bstep (se 1 (by rfl) ⟨89975, by rfl⟩ : syracuseStep 119967 = 179951) B179951
theorem B119999 : Blo 119786 119999 := bstep (se 1 (by rfl) ⟨89999, by rfl⟩ : syracuseStep 119999 = 179999) B179999
theorem B120039 : Blo 119786 120039 := bstep (se 1 (by rfl) ⟨90029, by rfl⟩ : syracuseStep 120039 = 180059) B180059
theorem B120091 : Blo 119786 120091 := bstep (se 1 (by rfl) ⟨90068, by rfl⟩ : syracuseStep 120091 = 180137) B180137
theorem B120319 : Blo 119786 120319 := bstep (se 1 (by rfl) ⟨90239, by rfl⟩ : syracuseStep 120319 = 180479) B180479
theorem B546385 : Blo 119786 546385 := bstep (se 2 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 546385 = 409789) B409789
theorem B153191 : Blo 119786 153191 := bstep (se 1 (by rfl) ⟨114893, by rfl⟩ : syracuseStep 153191 = 229787) B229787
theorem B775817 : Blo 119786 775817 := bstep (se 2 (by rfl) ⟨290931, by rfl⟩ : syracuseStep 775817 = 581863) B581863
theorem B416231 : Blo 119786 416231 := bstep (se 1 (by rfl) ⟨312173, by rfl⟩ : syracuseStep 416231 = 624347) B624347
theorem B122015 : Blo 119786 122015 := bstep (se 1 (by rfl) ⟨91511, by rfl⟩ : syracuseStep 122015 = 183023) B183023
theorem B122095 : Blo 119786 122095 := bstep (se 1 (by rfl) ⟨91571, by rfl⟩ : syracuseStep 122095 = 183143) B183143
theorem B122267 : Blo 119786 122267 := bstep (se 1 (by rfl) ⟨91700, by rfl⟩ : syracuseStep 122267 = 183401) B183401
theorem B122271 : Blo 119786 122271 := bstep (se 1 (by rfl) ⟨91703, by rfl⟩ : syracuseStep 122271 = 183407) B183407
theorem B417311 : Blo 119786 417311 := bstep (se 1 (by rfl) ⟨312983, by rfl⟩ : syracuseStep 417311 = 625967) B625967
theorem B613979 : Blo 119786 613979 := bstep (se 1 (by rfl) ⟨460484, by rfl⟩ : syracuseStep 613979 = 920969) B920969
theorem B122875 : Blo 119786 122875 := bstep (se 1 (by rfl) ⟨92156, by rfl⟩ : syracuseStep 122875 = 184313) B184313
theorem B122907 : Blo 119786 122907 := bstep (se 1 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 122907 = 184361) B184361
theorem B123035 : Blo 119786 123035 := bstep (se 1 (by rfl) ⟨92276, by rfl⟩ : syracuseStep 123035 = 184553) B184553
theorem B876743 : Blo 119786 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B1794251 : Blo 119786 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B123163 : Blo 119786 123163 := bstep (se 1 (by rfl) ⟨92372, by rfl⟩ : syracuseStep 123163 = 184745) B184745
theorem B418127 : Blo 119786 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B123367 : Blo 119786 123367 := bstep (se 1 (by rfl) ⟨92525, by rfl⟩ : syracuseStep 123367 = 185051) B185051
theorem B123631 : Blo 119786 123631 := bstep (se 1 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 123631 = 185447) B185447
theorem B123675 : Blo 119786 123675 := bstep (se 1 (by rfl) ⟨92756, by rfl⟩ : syracuseStep 123675 = 185513) B185513
theorem B123719 : Blo 119786 123719 := bstep (se 1 (by rfl) ⟨92789, by rfl⟩ : syracuseStep 123719 = 185579) B185579
theorem B910763 : Blo 119786 910763 := bstep (se 1 (by rfl) ⟨683072, by rfl⟩ : syracuseStep 910763 = 1366145) B1366145
theorem B1304819 : Blo 119786 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B911735 : Blo 119786 911735 := bstep (se 1 (by rfl) ⟨683801, by rfl⟩ : syracuseStep 911735 = 1367603) B1367603
theorem B977579 : Blo 119786 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B650207 : Blo 119786 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B4222003 : Blo 119786 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B617543 : Blo 119786 617543 := bstep (se 1 (by rfl) ⟨463157, by rfl⟩ : syracuseStep 617543 = 926315) B926315
theorem B683711 : Blo 119786 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B389099 : Blo 119786 389099 := bstep (se 1 (by rfl) ⟨291824, by rfl⟩ : syracuseStep 389099 = 583649) B583649
theorem B586109 : Blo 119786 586109 := bstep (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) B219791
theorem B553355 : Blo 119786 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B619163 : Blo 119786 619163 := bstep (se 1 (by rfl) ⟨464372, by rfl⟩ : syracuseStep 619163 = 928745) B928745
theorem B1241851 : Blo 119786 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B18674657 : Blo 119786 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B521225 : Blo 119786 521225 := bstep (se 2 (by rfl) ⟨195459, by rfl⟩ : syracuseStep 521225 = 390919) B390919
theorem B620311 : Blo 119786 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B292747 : Blo 119786 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B2095145 : Blo 119786 2095145 := bstep (se 2 (by rfl) ⟨785679, by rfl⟩ : syracuseStep 2095145 = 1571359) B1571359
theorem B456947 : Blo 119786 456947 := bstep (se 1 (by rfl) ⟨342710, by rfl⟩ : syracuseStep 456947 = 685421) B685421
theorem B621107 : Blo 119786 621107 := bstep (se 1 (by rfl) ⟨465830, by rfl⟩ : syracuseStep 621107 = 931661) B931661
theorem B686879 : Blo 119786 686879 := bstep (se 1 (by rfl) ⟨515159, by rfl⟩ : syracuseStep 686879 = 1030319) B1030319
theorem B523361 : Blo 119786 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B2522269 : Blo 119786 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B1113425 : Blo 119786 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B622727 : Blo 119786 622727 := bstep (se 1 (by rfl) ⟨467045, by rfl⟩ : syracuseStep 622727 = 934091) B934091
theorem B1115005 : Blo 119786 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B5276821 : Blo 119786 5276821 := bstep (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) B247351
theorem B1967993 : Blo 119786 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B264073 : Blo 119786 264073 := bstep (se 2 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 264073 = 198055) B198055
theorem B1182059 : Blo 119786 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B166379 : Blo 119786 166379 := bstep (se 1 (by rfl) ⟨124784, by rfl⟩ : syracuseStep 166379 = 249569) B249569
theorem B232787 : Blo 119786 232787 := bstep (se 1 (by rfl) ⟨174590, by rfl⟩ : syracuseStep 232787 = 349181) B349181
theorem B464039 : Blo 119786 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B792089 : Blo 119786 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B923399 : Blo 119786 923399 := bstep (se 1 (by rfl) ⟨692549, by rfl⟩ : syracuseStep 923399 = 1385099) B1385099
theorem B433471 : Blo 119786 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B728513 : Blo 119786 728513 := bstep (se 2 (by rfl) ⟨273192, by rfl⟩ : syracuseStep 728513 = 546385) B546385
theorem B827081 : Blo 119786 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B2236481 : Blo 119786 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B270431 : Blo 119786 270431 := bstep (se 1 (by rfl) ⟨202823, by rfl⟩ : syracuseStep 270431 = 405647) B405647
theorem B368903 : Blo 119786 368903 := bstep (se 1 (by rfl) ⟨276677, by rfl⟩ : syracuseStep 368903 = 553355) B553355
theorem B533303 : Blo 119786 533303 := bstep (se 1 (by rfl) ⟨399977, by rfl⟩ : syracuseStep 533303 = 799955) B799955
theorem B467927 : Blo 119786 467927 := bstep (se 1 (by rfl) ⟨350945, by rfl⟩ : syracuseStep 467927 = 701891) B701891
theorem B304631 : Blo 119786 304631 := bstep (se 1 (by rfl) ⟨228473, by rfl⟩ : syracuseStep 304631 = 456947) B456947
theorem B3352103 : Blo 119786 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B4532203 : Blo 119786 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B338003 : Blo 119786 338003 := bstep (se 1 (by rfl) ⟨253502, by rfl⟩ : syracuseStep 338003 = 507005) B507005
theorem B207103 : Blo 119786 207103 := bstep (se 1 (by rfl) ⟨155327, by rfl⟩ : syracuseStep 207103 = 310655) B310655
theorem B207643 : Blo 119786 207643 := bstep (se 1 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 207643 = 311465) B311465
theorem B273545 : Blo 119786 273545 := bstep (se 2 (by rfl) ⟨102579, by rfl⟩ : syracuseStep 273545 = 205159) B205159
theorem B929231 : Blo 119786 929231 := bstep (se 1 (by rfl) ⟨696923, by rfl⟩ : syracuseStep 929231 = 1393847) B1393847
theorem B208831 : Blo 119786 208831 := bstep (se 1 (by rfl) ⟨156623, by rfl⟩ : syracuseStep 208831 = 313247) B313247
theorem B274409 : Blo 119786 274409 := bstep (se 2 (by rfl) ⟨102903, by rfl⟩ : syracuseStep 274409 = 205807) B205807
theorem B307759 : Blo 119786 307759 := bstep (se 1 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 307759 = 461639) B461639
theorem B438889 : Blo 119786 438889 := bstep (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) B329167
theorem B406511 : Blo 119786 406511 := bstep (se 1 (by rfl) ⟨304883, by rfl⟩ : syracuseStep 406511 = 609767) B609767
theorem B275759 : Blo 119786 275759 := bstep (se 1 (by rfl) ⟨206819, by rfl⟩ : syracuseStep 275759 = 413639) B413639
theorem B2143739 : Blo 119786 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B308843 : Blo 119786 308843 := bstep (se 1 (by rfl) ⟨231632, by rfl⟩ : syracuseStep 308843 = 463265) B463265
theorem B407591 : Blo 119786 407591 := bstep (se 1 (by rfl) ⟨305693, by rfl⟩ : syracuseStep 407591 = 611387) B611387
theorem B408509 : Blo 119786 408509 := bstep (se 3 (by rfl) ⟨76595, by rfl⟩ : syracuseStep 408509 = 153191) B153191
theorem B244703 : Blo 119786 244703 := bstep (se 1 (by rfl) ⟨183527, by rfl⟩ : syracuseStep 244703 = 367055) B367055
theorem B277487 : Blo 119786 277487 := bstep (se 1 (by rfl) ⟨208115, by rfl⟩ : syracuseStep 277487 = 416231) B416231
theorem B3554705 : Blo 119786 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B179849 : Blo 119786 179849 := bstep (se 2 (by rfl) ⟨67443, by rfl⟩ : syracuseStep 179849 = 134887) B134887
theorem B278207 : Blo 119786 278207 := bstep (se 1 (by rfl) ⟨208655, by rfl⟩ : syracuseStep 278207 = 417311) B417311
theorem B409319 : Blo 119786 409319 := bstep (se 1 (by rfl) ⟨306989, by rfl⟩ : syracuseStep 409319 = 613979) B613979
theorem B4112441 : Blo 119786 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B1196167 : Blo 119786 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B180383 : Blo 119786 180383 := bstep (se 1 (by rfl) ⟨135287, by rfl⟩ : syracuseStep 180383 = 270575) B270575
theorem B3129905 : Blo 119786 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B180791 : Blo 119786 180791 := bstep (se 1 (by rfl) ⟨135593, by rfl⟩ : syracuseStep 180791 = 271187) B271187
theorem B13452101 : Blo 119786 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B607175 : Blo 119786 607175 := bstep (se 1 (by rfl) ⟨455381, by rfl⟩ : syracuseStep 607175 = 910763) B910763
theorem B181199 : Blo 119786 181199 := bstep (se 1 (by rfl) ⟨135899, by rfl⟩ : syracuseStep 181199 = 271799) B271799
theorem B1655801 : Blo 119786 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B181385 : Blo 119786 181385 := bstep (se 2 (by rfl) ⟨68019, by rfl⟩ : syracuseStep 181385 = 136039) B136039
theorem B181403 : Blo 119786 181403 := bstep (se 1 (by rfl) ⟨136052, by rfl⟩ : syracuseStep 181403 = 272105) B272105
theorem B2082023 : Blo 119786 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B181727 : Blo 119786 181727 := bstep (se 1 (by rfl) ⟨136295, by rfl⟩ : syracuseStep 181727 = 272591) B272591
theorem B869879 : Blo 119786 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B181787 : Blo 119786 181787 := bstep (se 1 (by rfl) ⟨136340, by rfl⟩ : syracuseStep 181787 = 272681) B272681
theorem B607823 : Blo 119786 607823 := bstep (se 1 (by rfl) ⟨455867, by rfl⟩ : syracuseStep 607823 = 911735) B911735
theorem B182087 : Blo 119786 182087 := bstep (se 1 (by rfl) ⟨136565, by rfl⟩ : syracuseStep 182087 = 273131) B273131
theorem B411695 : Blo 119786 411695 := bstep (se 1 (by rfl) ⟨308771, by rfl⟩ : syracuseStep 411695 = 617543) B617543
theorem B412775 : Blo 119786 412775 := bstep (se 1 (by rfl) ⟨309581, by rfl⟩ : syracuseStep 412775 = 619163) B619163
theorem B183593 : Blo 119786 183593 := bstep (se 2 (by rfl) ⟨68847, by rfl⟩ : syracuseStep 183593 = 137695) B137695
theorem B183599 : Blo 119786 183599 := bstep (se 1 (by rfl) ⟨137699, by rfl⟩ : syracuseStep 183599 = 275399) B275399
theorem B347483 : Blo 119786 347483 := bstep (se 1 (by rfl) ⟨260612, by rfl⟩ : syracuseStep 347483 = 521225) B521225
theorem B413153 : Blo 119786 413153 := bstep (se 2 (by rfl) ⟨154932, by rfl⟩ : syracuseStep 413153 = 309865) B309865
theorem B1396763 : Blo 119786 1396763 := bstep (se 1 (by rfl) ⟨1047572, by rfl⟩ : syracuseStep 1396763 = 2095145) B2095145
theorem B184457 : Blo 119786 184457 := bstep (se 2 (by rfl) ⟨69171, by rfl⟩ : syracuseStep 184457 = 138343) B138343
theorem B414071 : Blo 119786 414071 := bstep (se 1 (by rfl) ⟨310553, by rfl⟩ : syracuseStep 414071 = 621107) B621107
theorem B184697 : Blo 119786 184697 := bstep (se 2 (by rfl) ⟨69261, by rfl⟩ : syracuseStep 184697 = 138523) B138523
theorem B348907 : Blo 119786 348907 := bstep (se 1 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 348907 = 523361) B523361
theorem B742283 : Blo 119786 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B185279 : Blo 119786 185279 := bstep (se 1 (by rfl) ⟨138959, by rfl⟩ : syracuseStep 185279 = 277919) B277919
theorem B185321 : Blo 119786 185321 := bstep (se 2 (by rfl) ⟨69495, by rfl⟩ : syracuseStep 185321 = 138991) B138991
theorem B185375 : Blo 119786 185375 := bstep (se 1 (by rfl) ⟨139031, by rfl⟩ : syracuseStep 185375 = 278063) B278063
theorem B120167 : Blo 119786 120167 := bstep (se 1 (by rfl) ⟨90125, by rfl⟩ : syracuseStep 120167 = 180251) B180251
theorem B1660283 : Blo 119786 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B1496627 : Blo 119786 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B120423 : Blo 119786 120423 := bstep (se 1 (by rfl) ⟨90317, by rfl⟩ : syracuseStep 120423 = 180635) B180635
theorem B612035 : Blo 119786 612035 := bstep (se 1 (by rfl) ⟨459026, by rfl⟩ : syracuseStep 612035 = 918053) B918053
theorem B415529 : Blo 119786 415529 := bstep (se 2 (by rfl) ⟨155823, by rfl⟩ : syracuseStep 415529 = 311647) B311647
theorem B120859 : Blo 119786 120859 := bstep (se 1 (by rfl) ⟨90644, by rfl⟩ : syracuseStep 120859 = 181289) B181289
theorem B186475 : Blo 119786 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B121471 : Blo 119786 121471 := bstep (se 1 (by rfl) ⟨91103, by rfl⟩ : syracuseStep 121471 = 182207) B182207
theorem B613007 : Blo 119786 613007 := bstep (se 1 (by rfl) ⟨459755, by rfl⟩ : syracuseStep 613007 = 919511) B919511
theorem B416609 : Blo 119786 416609 := bstep (se 2 (by rfl) ⟨156228, by rfl⟩ : syracuseStep 416609 = 312457) B312457
theorem B121791 : Blo 119786 121791 := bstep (se 1 (by rfl) ⟨91343, by rfl⟩ : syracuseStep 121791 = 182687) B182687
theorem B122335 : Blo 119786 122335 := bstep (se 1 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 122335 = 183503) B183503
theorem B122351 : Blo 119786 122351 := bstep (se 1 (by rfl) ⟨91763, by rfl⟩ : syracuseStep 122351 = 183527) B183527
theorem B876167 : Blo 119786 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B417743 : Blo 119786 417743 := bstep (se 1 (by rfl) ⟨313307, by rfl⟩ : syracuseStep 417743 = 626615) B626615
theorem B122927 : Blo 119786 122927 := bstep (se 1 (by rfl) ⟨92195, by rfl⟩ : syracuseStep 122927 = 184391) B184391
theorem B517211 : Blo 119786 517211 := bstep (se 1 (by rfl) ⟨387908, by rfl⟩ : syracuseStep 517211 = 775817) B775817
theorem B4973957 : Blo 119786 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B5629337 : Blo 119786 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B616939 : Blo 119786 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B584495 : Blo 119786 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B8612851 : Blo 119786 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B3173579 : Blo 119786 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B749287 : Blo 119786 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B651719 : Blo 119786 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B553979 : Blo 119786 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B455807 : Blo 119786 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B390329 : Blo 119786 390329 := bstep (se 2 (by rfl) ⟨146373, by rfl⟩ : syracuseStep 390329 = 292747) B292747
theorem B259399 : Blo 119786 259399 := bstep (se 1 (by rfl) ⟨194549, by rfl⟩ : syracuseStep 259399 = 389099) B389099
theorem B390739 : Blo 119786 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B620135 : Blo 119786 620135 := bstep (se 1 (by rfl) ⟨465101, by rfl⟩ : syracuseStep 620135 = 930203) B930203
theorem B489341 : Blo 119786 489341 := bstep (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) B183503
theorem B12449771 : Blo 119786 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B457919 : Blo 119786 457919 := bstep (se 1 (by rfl) ⟨343439, by rfl⟩ : syracuseStep 457919 = 686879) B686879
theorem B1311995 : Blo 119786 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B788039 : Blo 119786 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B231655 : Blo 119786 231655 := bstep (se 1 (by rfl) ⟨173741, by rfl⟩ : syracuseStep 231655 = 347483) B347483
theorem B494855 : Blo 119786 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B528059 : Blo 119786 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B3315971 : Blo 119786 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B465209 : Blo 119786 465209 := bstep (se 2 (by rfl) ⟨174453, by rfl⟩ : syracuseStep 465209 = 348907) B348907
theorem B203087 : Blo 119786 203087 := bstep (se 1 (by rfl) ⟨152315, by rfl⟩ : syracuseStep 203087 = 304631) B304631
theorem B2234735 : Blo 119786 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B434479 : Blo 119786 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B271007 : Blo 119786 271007 := bstep (se 1 (by rfl) ⟨203255, by rfl⟩ : syracuseStep 271007 = 406511) B406511
theorem B369319 : Blo 119786 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B303871 : Blo 119786 303871 := bstep (se 1 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 303871 = 455807) B455807
theorem B205895 : Blo 119786 205895 := bstep (se 1 (by rfl) ⟨154421, by rfl⟩ : syracuseStep 205895 = 308843) B308843
theorem B8299847 : Blo 119786 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B271727 : Blo 119786 271727 := bstep (se 1 (by rfl) ⟨203795, by rfl⟩ : syracuseStep 271727 = 407591) B407591
theorem B272339 : Blo 119786 272339 := bstep (se 1 (by rfl) ⟨204254, by rfl⟩ : syracuseStep 272339 = 408509) B408509
theorem B305279 : Blo 119786 305279 := bstep (se 1 (by rfl) ⟨228959, by rfl⟩ : syracuseStep 305279 = 457919) B457919
theorem B2369803 : Blo 119786 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B272879 : Blo 119786 272879 := bstep (se 1 (by rfl) ⟨204659, by rfl⟩ : syracuseStep 272879 = 409319) B409319
theorem B404783 : Blo 119786 404783 := bstep (se 1 (by rfl) ⟨303587, by rfl⟩ : syracuseStep 404783 = 607175) B607175
theorem B1388015 : Blo 119786 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B405215 : Blo 119786 405215 := bstep (se 1 (by rfl) ⟨303911, by rfl⟩ : syracuseStep 405215 = 607823) B607823
theorem B1486673 : Blo 119786 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B274463 : Blo 119786 274463 := bstep (se 1 (by rfl) ⟨205847, by rfl⟩ : syracuseStep 274463 = 411695) B411695
theorem B275183 : Blo 119786 275183 := bstep (se 1 (by rfl) ⟨206387, by rfl⟩ : syracuseStep 275183 = 412775) B412775
theorem B275435 : Blo 119786 275435 := bstep (se 1 (by rfl) ⟨206576, by rfl⟩ : syracuseStep 275435 = 413153) B413153
theorem B6042937 : Blo 119786 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B931175 : Blo 119786 931175 := bstep (se 1 (by rfl) ⟨698381, by rfl⟩ : syracuseStep 931175 = 1396763) B1396763
theorem B276047 : Blo 119786 276047 := bstep (se 1 (by rfl) ⟨207035, by rfl⟩ : syracuseStep 276047 = 414071) B414071
theorem B276137 : Blo 119786 276137 := bstep (se 2 (by rfl) ⟨103551, by rfl⟩ : syracuseStep 276137 = 207103) B207103
theorem B309359 : Blo 119786 309359 := bstep (se 1 (by rfl) ⟨232019, by rfl⟩ : syracuseStep 309359 = 464039) B464039
theorem B997751 : Blo 119786 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B276857 : Blo 119786 276857 := bstep (se 2 (by rfl) ⟨103821, by rfl⟩ : syracuseStep 276857 = 207643) B207643
theorem B408023 : Blo 119786 408023 := bstep (se 1 (by rfl) ⟨306017, by rfl⟩ : syracuseStep 408023 = 612035) B612035
theorem B277019 : Blo 119786 277019 := bstep (se 1 (by rfl) ⟨207764, by rfl⟩ : syracuseStep 277019 = 415529) B415529
theorem B11483801 : Blo 119786 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B408671 : Blo 119786 408671 := bstep (se 1 (by rfl) ⟨306503, by rfl⟩ : syracuseStep 408671 = 613007) B613007
theorem B277739 : Blo 119786 277739 := bstep (se 1 (by rfl) ⟨208304, by rfl⟩ : syracuseStep 277739 = 416609) B416609
theorem B999049 : Blo 119786 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B278441 : Blo 119786 278441 := bstep (se 2 (by rfl) ⟨104415, by rfl⟩ : syracuseStep 278441 = 208831) B208831
theorem B278495 : Blo 119786 278495 := bstep (se 1 (by rfl) ⟨208871, by rfl⟩ : syracuseStep 278495 = 417743) B417743
theorem B1490987 : Blo 119786 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B180287 : Blo 119786 180287 := bstep (se 1 (by rfl) ⟨135215, by rfl⟩ : syracuseStep 180287 = 270431) B270431
theorem B245935 : Blo 119786 245935 := bstep (se 1 (by rfl) ⟨184451, by rfl⟩ : syracuseStep 245935 = 368903) B368903
theorem B311951 : Blo 119786 311951 := bstep (se 1 (by rfl) ⟨233963, by rfl⟩ : syracuseStep 311951 = 467927) B467927
theorem B344807 : Blo 119786 344807 := bstep (se 1 (by rfl) ⟨258605, by rfl⟩ : syracuseStep 344807 = 517211) B517211
theorem B410345 : Blo 119786 410345 := bstep (se 2 (by rfl) ⟨153879, by rfl⟩ : syracuseStep 410345 = 307759) B307759
theorem B3752891 : Blo 119786 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B443677 : Blo 119786 443677 := bstep (se 3 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 443677 = 166379) B166379
theorem B345865 : Blo 119786 345865 := bstep (se 2 (by rfl) ⟨129699, by rfl⟩ : syracuseStep 345865 = 259399) B259399
theorem B182363 : Blo 119786 182363 := bstep (se 1 (by rfl) ⟨136772, by rfl⟩ : syracuseStep 182363 = 273545) B273545
theorem B2115719 : Blo 119786 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B182939 : Blo 119786 182939 := bstep (se 1 (by rfl) ⟨137204, by rfl⟩ : syracuseStep 182939 = 274409) B274409
theorem B248633 : Blo 119786 248633 := bstep (se 2 (by rfl) ⟨93237, by rfl⟩ : syracuseStep 248633 = 186475) B186475
theorem B183839 : Blo 119786 183839 := bstep (se 1 (by rfl) ⟨137879, by rfl⟩ : syracuseStep 183839 = 275759) B275759
theorem B1429159 : Blo 119786 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B413423 : Blo 119786 413423 := bstep (se 1 (by rfl) ⟨310067, by rfl⟩ : syracuseStep 413423 = 620135) B620135
theorem B577961 : Blo 119786 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B184991 : Blo 119786 184991 := bstep (se 1 (by rfl) ⟨138743, by rfl⟩ : syracuseStep 184991 = 277487) B277487
theorem B13161365 : Blo 119786 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B119899 : Blo 119786 119899 := bstep (se 1 (by rfl) ⟨89924, by rfl⟩ : syracuseStep 119899 = 179849) B179849
theorem B185471 : Blo 119786 185471 := bstep (se 1 (by rfl) ⟨139103, by rfl⟩ : syracuseStep 185471 = 278207) B278207
theorem B2741627 : Blo 119786 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B415151 : Blo 119786 415151 := bstep (se 1 (by rfl) ⟨311363, by rfl⟩ : syracuseStep 415151 = 622727) B622727
theorem B120255 : Blo 119786 120255 := bstep (se 1 (by rfl) ⟨90191, by rfl⟩ : syracuseStep 120255 = 180383) B180383
theorem B1594889 : Blo 119786 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B2086603 : Blo 119786 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B120527 : Blo 119786 120527 := bstep (se 1 (by rfl) ⟨90395, by rfl⟩ : syracuseStep 120527 = 180791) B180791
theorem B8968067 : Blo 119786 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B120799 : Blo 119786 120799 := bstep (se 1 (by rfl) ⟨90599, by rfl⟩ : syracuseStep 120799 = 181199) B181199
theorem B1103867 : Blo 119786 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B120923 : Blo 119786 120923 := bstep (se 1 (by rfl) ⟨90692, by rfl⟩ : syracuseStep 120923 = 181385) B181385
theorem B120935 : Blo 119786 120935 := bstep (se 1 (by rfl) ⟨90701, by rfl⟩ : syracuseStep 120935 = 181403) B181403
theorem B121151 : Blo 119786 121151 := bstep (se 1 (by rfl) ⟨90863, by rfl⟩ : syracuseStep 121151 = 181727) B181727
theorem B121191 : Blo 119786 121191 := bstep (se 1 (by rfl) ⟨90893, by rfl⟩ : syracuseStep 121191 = 181787) B181787
theorem B121391 : Blo 119786 121391 := bstep (se 1 (by rfl) ⟨91043, by rfl⟩ : syracuseStep 121391 = 182087) B182087
theorem B7035761 : Blo 119786 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B122395 : Blo 119786 122395 := bstep (se 1 (by rfl) ⟨91796, by rfl⟩ : syracuseStep 122395 = 183593) B183593
theorem B122399 : Blo 119786 122399 := bstep (se 1 (by rfl) ⟨91799, by rfl⟩ : syracuseStep 122399 = 183599) B183599
theorem B155191 : Blo 119786 155191 := bstep (se 1 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 155191 = 232787) B232787
theorem B352097 : Blo 119786 352097 := bstep (se 2 (by rfl) ⟨132036, by rfl⟩ : syracuseStep 352097 = 264073) B264073
theorem B122971 : Blo 119786 122971 := bstep (se 1 (by rfl) ⟨92228, by rfl⟩ : syracuseStep 122971 = 184457) B184457
theorem B123131 : Blo 119786 123131 := bstep (se 1 (by rfl) ⟨92348, by rfl⟩ : syracuseStep 123131 = 184697) B184697
theorem B123519 : Blo 119786 123519 := bstep (se 1 (by rfl) ⟨92639, by rfl⟩ : syracuseStep 123519 = 185279) B185279
theorem B123547 : Blo 119786 123547 := bstep (se 1 (by rfl) ⟨92660, by rfl⟩ : syracuseStep 123547 = 185321) B185321
theorem B123583 : Blo 119786 123583 := bstep (se 1 (by rfl) ⟨92687, by rfl⟩ : syracuseStep 123583 = 185375) B185375
theorem B1106855 : Blo 119786 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B615599 : Blo 119786 615599 := bstep (se 1 (by rfl) ⟨461699, by rfl⟩ : syracuseStep 615599 = 923399) B923399
theorem B2319677 : Blo 119786 2319677 := bstep (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) B869879
theorem B485675 : Blo 119786 485675 := bstep (se 1 (by rfl) ⟨364256, by rfl⟩ : syracuseStep 485675 = 728513) B728513
theorem B1304909 : Blo 119786 1304909 := bstep (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) B489341
theorem B584111 : Blo 119786 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B551387 : Blo 119786 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B355535 : Blo 119786 355535 := bstep (se 1 (by rfl) ⟨266651, by rfl⟩ : syracuseStep 355535 = 533303) B533303
theorem B585185 : Blo 119786 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B225335 : Blo 119786 225335 := bstep (se 1 (by rfl) ⟨169001, by rfl⟩ : syracuseStep 225335 = 338003) B338003
theorem B389663 : Blo 119786 389663 := bstep (se 1 (by rfl) ⟨292247, by rfl⟩ : syracuseStep 389663 = 584495) B584495
theorem B520985 : Blo 119786 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B619487 : Blo 119786 619487 := bstep (se 1 (by rfl) ⟨464615, by rfl⟩ : syracuseStep 619487 = 929231) B929231
theorem B260219 : Blo 119786 260219 := bstep (se 1 (by rfl) ⟨195164, by rfl⟩ : syracuseStep 260219 = 390329) B390329
theorem B163135 : Blo 119786 163135 := bstep (se 1 (by rfl) ⟨122351, by rfl⟩ : syracuseStep 163135 = 244703) B244703
theorem B229871 : Blo 119786 229871 := bstep (se 1 (by rfl) ⟨172403, by rfl⟩ : syracuseStep 229871 = 344807) B344807
theorem B492425 : Blo 119786 492425 := bstep (se 2 (by rfl) ⟨184659, by rfl⟩ : syracuseStep 492425 = 369319) B369319
theorem B1311653 : Blo 119786 1311653 := bstep (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) B245935
theorem B525359 : Blo 119786 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B1410479 : Blo 119786 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B591569 : Blo 119786 591569 := bstep (se 2 (by rfl) ⟨221838, by rfl⟩ : syracuseStep 591569 = 443677) B443677
theorem B165755 : Blo 119786 165755 := bstep (se 1 (by rfl) ⟨124316, by rfl⟩ : syracuseStep 165755 = 248633) B248633
theorem B329903 : Blo 119786 329903 := bstep (se 1 (by rfl) ⟨247427, by rfl⟩ : syracuseStep 329903 = 494855) B494855
theorem B461153 : Blo 119786 461153 := bstep (se 2 (by rfl) ⟨172932, by rfl⟩ : syracuseStep 461153 = 345865) B345865
theorem B7311005 : Blo 119786 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B135391 : Blo 119786 135391 := bstep (se 1 (by rfl) ⟨101543, by rfl⟩ : syracuseStep 135391 = 203087) B203087
theorem B4690507 : Blo 119786 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B1905545 : Blo 119786 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B234731 : Blo 119786 234731 := bstep (se 1 (by rfl) ⟨176048, by rfl⟩ : syracuseStep 234731 = 352097) B352097
theorem B693917 : Blo 119786 693917 := bstep (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) B260219
theorem B137263 : Blo 119786 137263 := bstep (se 1 (by rfl) ⟨102947, by rfl⟩ : syracuseStep 137263 = 205895) B205895
theorem B1546451 : Blo 119786 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B203519 : Blo 119786 203519 := bstep (se 1 (by rfl) ⟨152639, by rfl⟩ : syracuseStep 203519 = 305279) B305279
theorem B367591 : Blo 119786 367591 := bstep (se 1 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 367591 = 551387) B551387
theorem B237023 : Blo 119786 237023 := bstep (se 1 (by rfl) ⟨177767, by rfl⟩ : syracuseStep 237023 = 355535) B355535
theorem B269855 : Blo 119786 269855 := bstep (se 1 (by rfl) ⟨202391, by rfl⟩ : syracuseStep 269855 = 404783) B404783
theorem B925343 : Blo 119786 925343 := bstep (se 1 (by rfl) ⟨694007, by rfl⟩ : syracuseStep 925343 = 1388015) B1388015
theorem B270143 : Blo 119786 270143 := bstep (se 1 (by rfl) ⟨202607, by rfl⟩ : syracuseStep 270143 = 405215) B405215
theorem B991115 : Blo 119786 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B206239 : Blo 119786 206239 := bstep (se 1 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 206239 = 309359) B309359
theorem B665167 : Blo 119786 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B272015 : Blo 119786 272015 := bstep (se 1 (by rfl) ⟨204011, by rfl⟩ : syracuseStep 272015 = 408023) B408023
theorem B272447 : Blo 119786 272447 := bstep (se 1 (by rfl) ⟨204335, by rfl⟩ : syracuseStep 272447 = 408671) B408671
theorem B206921 : Blo 119786 206921 := bstep (se 2 (by rfl) ⟨77595, by rfl⟩ : syracuseStep 206921 = 155191) B155191
theorem B3975965 : Blo 119786 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B207967 : Blo 119786 207967 := bstep (se 1 (by rfl) ⟨155975, by rfl⟩ : syracuseStep 207967 = 311951) B311951
theorem B273563 : Blo 119786 273563 := bstep (se 1 (by rfl) ⟨205172, by rfl⟩ : syracuseStep 273563 = 410345) B410345
theorem B2501927 : Blo 119786 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B405161 : Blo 119786 405161 := bstep (se 2 (by rfl) ⟨151935, by rfl⟩ : syracuseStep 405161 = 303871) B303871
theorem B275615 : Blo 119786 275615 := bstep (se 1 (by rfl) ⟨206711, by rfl⟩ : syracuseStep 275615 = 413423) B413423
theorem B308873 : Blo 119786 308873 := bstep (se 2 (by rfl) ⟨115827, by rfl⟩ : syracuseStep 308873 = 231655) B231655
theorem B3159737 : Blo 119786 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B276767 : Blo 119786 276767 := bstep (se 1 (by rfl) ⟨207575, by rfl⟩ : syracuseStep 276767 = 415151) B415151
theorem B1063259 : Blo 119786 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B5978711 : Blo 119786 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B735911 : Blo 119786 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B2210647 : Blo 119786 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B310139 : Blo 119786 310139 := bstep (se 1 (by rfl) ⟨232604, by rfl⟩ : syracuseStep 310139 = 465209) B465209
theorem B1489823 : Blo 119786 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B180671 : Blo 119786 180671 := bstep (se 1 (by rfl) ⟨135503, by rfl⟩ : syracuseStep 180671 = 271007) B271007
theorem B737903 : Blo 119786 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B410399 : Blo 119786 410399 := bstep (se 1 (by rfl) ⟨307799, by rfl⟩ : syracuseStep 410399 = 615599) B615599
theorem B181151 : Blo 119786 181151 := bstep (se 1 (by rfl) ⟨135863, by rfl⟩ : syracuseStep 181151 = 271727) B271727
theorem B181559 : Blo 119786 181559 := bstep (se 1 (by rfl) ⟨136169, by rfl⟩ : syracuseStep 181559 = 272339) B272339
theorem B869939 : Blo 119786 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B181919 : Blo 119786 181919 := bstep (se 1 (by rfl) ⟨136439, by rfl⟩ : syracuseStep 181919 = 272879) B272879
theorem B182975 : Blo 119786 182975 := bstep (se 1 (by rfl) ⟨137231, by rfl⟩ : syracuseStep 182975 = 274463) B274463
theorem B150223 : Blo 119786 150223 := bstep (se 1 (by rfl) ⟨112667, by rfl⟩ : syracuseStep 150223 = 225335) B225335
theorem B183455 : Blo 119786 183455 := bstep (se 1 (by rfl) ⟨137591, by rfl⟩ : syracuseStep 183455 = 275183) B275183
theorem B347323 : Blo 119786 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B412991 : Blo 119786 412991 := bstep (se 1 (by rfl) ⟨309743, by rfl⟩ : syracuseStep 412991 = 619487) B619487
theorem B183623 : Blo 119786 183623 := bstep (se 1 (by rfl) ⟨137717, by rfl⟩ : syracuseStep 183623 = 275435) B275435
theorem B184031 : Blo 119786 184031 := bstep (se 1 (by rfl) ⟨138023, by rfl⟩ : syracuseStep 184031 = 276047) B276047
theorem B11128549 : Blo 119786 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B184091 : Blo 119786 184091 := bstep (se 1 (by rfl) ⟨138068, by rfl⟩ : syracuseStep 184091 = 276137) B276137
theorem B1560493 : Blo 119786 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B184571 : Blo 119786 184571 := bstep (se 1 (by rfl) ⟨138428, by rfl⟩ : syracuseStep 184571 = 276857) B276857
theorem B184679 : Blo 119786 184679 := bstep (se 1 (by rfl) ⟨138509, by rfl⟩ : syracuseStep 184679 = 277019) B277019
theorem B217513 : Blo 119786 217513 := bstep (se 2 (by rfl) ⟨81567, by rfl⟩ : syracuseStep 217513 = 163135) B163135
theorem B7655867 : Blo 119786 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B185159 : Blo 119786 185159 := bstep (se 1 (by rfl) ⟨138869, by rfl⟩ : syracuseStep 185159 = 277739) B277739
theorem B1332065 : Blo 119786 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B185627 : Blo 119786 185627 := bstep (se 1 (by rfl) ⟨139220, by rfl⟩ : syracuseStep 185627 = 278441) B278441
theorem B185663 : Blo 119786 185663 := bstep (se 1 (by rfl) ⟨139247, by rfl⟩ : syracuseStep 185663 = 278495) B278495
theorem B120191 : Blo 119786 120191 := bstep (se 1 (by rfl) ⟨90143, by rfl⟩ : syracuseStep 120191 = 180287) B180287
theorem B579305 : Blo 119786 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B121575 : Blo 119786 121575 := bstep (se 1 (by rfl) ⟨91181, by rfl⟩ : syracuseStep 121575 = 182363) B182363
theorem B121959 : Blo 119786 121959 := bstep (se 1 (by rfl) ⟨91469, by rfl⟩ : syracuseStep 121959 = 182939) B182939
theorem B122559 : Blo 119786 122559 := bstep (se 1 (by rfl) ⟨91919, by rfl⟩ : syracuseStep 122559 = 183839) B183839
theorem B352039 : Blo 119786 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B385307 : Blo 119786 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B123327 : Blo 119786 123327 := bstep (se 1 (by rfl) ⟨92495, by rfl⟩ : syracuseStep 123327 = 184991) B184991
theorem B8774243 : Blo 119786 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B3498653 : Blo 119786 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B123647 : Blo 119786 123647 := bstep (se 1 (by rfl) ⟨92735, by rfl⟩ : syracuseStep 123647 = 185471) B185471
theorem B5533231 : Blo 119786 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B323783 : Blo 119786 323783 := bstep (se 1 (by rfl) ⟨242837, by rfl⟩ : syracuseStep 323783 = 485675) B485675
theorem B389407 : Blo 119786 389407 := bstep (se 1 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 389407 = 584111) B584111
theorem B8057249 : Blo 119786 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B259775 : Blo 119786 259775 := bstep (se 1 (by rfl) ⟨194831, by rfl⟩ : syracuseStep 259775 = 389663) B389663
theorem B620783 : Blo 119786 620783 := bstep (se 1 (by rfl) ⟨465587, by rfl⟩ : syracuseStep 620783 = 931175) B931175
theorem B491935 : Blo 119786 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B328283 : Blo 119786 328283 := bstep (se 1 (by rfl) ⟨246212, by rfl⟩ : syracuseStep 328283 = 492425) B492425
theorem B394379 : Blo 119786 394379 := bstep (se 1 (by rfl) ⟨295784, by rfl⟩ : syracuseStep 394379 = 591569) B591569
theorem B886889 : Blo 119786 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B888043 : Blo 119786 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B200297 : Blo 119786 200297 := bstep (se 2 (by rfl) ⟨75111, by rfl⟩ : syracuseStep 200297 = 150223) B150223
theorem B462611 : Blo 119786 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B463097 : Blo 119786 463097 := bstep (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) B347323
theorem B135679 : Blo 119786 135679 := bstep (se 1 (by rfl) ⟨101759, by rfl⟩ : syracuseStep 135679 = 203519) B203519
theorem B7377641 : Blo 119786 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B660743 : Blo 119786 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B2332435 : Blo 119786 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B137947 : Blo 119786 137947 := bstep (se 1 (by rfl) ⟨103460, by rfl⟩ : syracuseStep 137947 = 206921) B206921
theorem B270107 : Blo 119786 270107 := bstep (se 1 (by rfl) ⟨202580, by rfl⟩ : syracuseStep 270107 = 405161) B405161
theorem B205915 : Blo 119786 205915 := bstep (se 1 (by rfl) ⟨154436, by rfl⟩ : syracuseStep 205915 = 308873) B308873
theorem B2106491 : Blo 119786 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B173183 : Blo 119786 173183 := bstep (se 1 (by rfl) ⟨129887, by rfl⟩ : syracuseStep 173183 = 259775) B259775
theorem B206759 : Blo 119786 206759 := bstep (se 1 (by rfl) ⟨155069, by rfl⟩ : syracuseStep 206759 = 310139) B310139
theorem B993215 : Blo 119786 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B469385 : Blo 119786 469385 := bstep (se 2 (by rfl) ⟨176019, by rfl⟩ : syracuseStep 469385 = 352039) B352039
theorem B273599 : Blo 119786 273599 := bstep (se 1 (by rfl) ⟨205199, by rfl⟩ : syracuseStep 273599 = 410399) B410399
theorem B307435 : Blo 119786 307435 := bstep (se 1 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 307435 = 461153) B461153
theorem B274985 : Blo 119786 274985 := bstep (se 2 (by rfl) ⟨103119, by rfl⟩ : syracuseStep 274985 = 206239) B206239
theorem B275327 : Blo 119786 275327 := bstep (se 1 (by rfl) ⟨206495, by rfl⟩ : syracuseStep 275327 = 412991) B412991
theorem B277289 : Blo 119786 277289 := bstep (se 2 (by rfl) ⟨103983, by rfl⟩ : syracuseStep 277289 = 207967) B207967
theorem B1030967 : Blo 119786 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B442013 : Blo 119786 442013 := bstep (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) B165755
theorem B179903 : Blo 119786 179903 := bstep (se 1 (by rfl) ⟨134927, by rfl⟩ : syracuseStep 179903 = 269855) B269855
theorem B180095 : Blo 119786 180095 := bstep (se 1 (by rfl) ⟨135071, by rfl⟩ : syracuseStep 180095 = 270143) B270143
theorem B2080657 : Blo 119786 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B180521 : Blo 119786 180521 := bstep (se 2 (by rfl) ⟨67695, by rfl⟩ : syracuseStep 180521 = 135391) B135391
theorem B5849495 : Blo 119786 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B181343 : Blo 119786 181343 := bstep (se 1 (by rfl) ⟨136007, by rfl⟩ : syracuseStep 181343 = 272015) B272015
theorem B181631 : Blo 119786 181631 := bstep (se 1 (by rfl) ⟨136223, by rfl⟩ : syracuseStep 181631 = 272447) B272447
theorem B15943229 : Blo 119786 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B182375 : Blo 119786 182375 := bstep (se 1 (by rfl) ⟨136781, by rfl⟩ : syracuseStep 182375 = 273563) B273563
theorem B183017 : Blo 119786 183017 := bstep (se 2 (by rfl) ⟨68631, by rfl⟩ : syracuseStep 183017 = 137263) B137263
theorem B215855 : Blo 119786 215855 := bstep (se 1 (by rfl) ⟨161891, by rfl⟩ : syracuseStep 215855 = 323783) B323783
theorem B183743 : Blo 119786 183743 := bstep (se 1 (by rfl) ⟨137807, by rfl⟩ : syracuseStep 183743 = 275615) B275615
theorem B413855 : Blo 119786 413855 := bstep (se 1 (by rfl) ⟨310391, by rfl⟩ : syracuseStep 413855 = 620783) B620783
theorem B184511 : Blo 119786 184511 := bstep (se 1 (by rfl) ⟨138383, by rfl⟩ : syracuseStep 184511 = 276767) B276767
theorem B708839 : Blo 119786 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B120447 : Blo 119786 120447 := bstep (se 1 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 120447 = 180671) B180671
theorem B153247 : Blo 119786 153247 := bstep (se 1 (by rfl) ⟨114935, by rfl⟩ : syracuseStep 153247 = 229871) B229871
theorem B120767 : Blo 119786 120767 := bstep (se 1 (by rfl) ⟨90575, by rfl⟩ : syracuseStep 120767 = 181151) B181151
theorem B874435 : Blo 119786 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B350239 : Blo 119786 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B121039 : Blo 119786 121039 := bstep (se 1 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 121039 = 181559) B181559
theorem B940319 : Blo 119786 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B579959 : Blo 119786 579959 := bstep (se 1 (by rfl) ⟨434969, by rfl⟩ : syracuseStep 579959 = 869939) B869939
theorem B121279 : Blo 119786 121279 := bstep (se 1 (by rfl) ⟨90959, by rfl⟩ : syracuseStep 121279 = 181919) B181919
theorem B219935 : Blo 119786 219935 := bstep (se 1 (by rfl) ⟨164951, by rfl⟩ : syracuseStep 219935 = 329903) B329903
theorem B121983 : Blo 119786 121983 := bstep (se 1 (by rfl) ⟨91487, by rfl⟩ : syracuseStep 121983 = 182975) B182975
theorem B122303 : Blo 119786 122303 := bstep (se 1 (by rfl) ⟨91727, by rfl⟩ : syracuseStep 122303 = 183455) B183455
theorem B122415 : Blo 119786 122415 := bstep (se 1 (by rfl) ⟨91811, by rfl⟩ : syracuseStep 122415 = 183623) B183623
theorem B4874003 : Blo 119786 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B122687 : Blo 119786 122687 := bstep (se 1 (by rfl) ⟨92015, by rfl⟩ : syracuseStep 122687 = 184031) B184031
theorem B122727 : Blo 119786 122727 := bstep (se 1 (by rfl) ⟨92045, by rfl⟩ : syracuseStep 122727 = 184091) B184091
theorem B123047 : Blo 119786 123047 := bstep (se 1 (by rfl) ⟨92285, by rfl⟩ : syracuseStep 123047 = 184571) B184571
theorem B123119 : Blo 119786 123119 := bstep (se 1 (by rfl) ⟨92339, by rfl⟩ : syracuseStep 123119 = 184679) B184679
theorem B5103911 : Blo 119786 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B123439 : Blo 119786 123439 := bstep (se 1 (by rfl) ⟨92579, by rfl⟩ : syracuseStep 123439 = 185159) B185159
theorem B1270363 : Blo 119786 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B156487 : Blo 119786 156487 := bstep (se 1 (by rfl) ⟨117365, by rfl⟩ : syracuseStep 156487 = 234731) B234731
theorem B123751 : Blo 119786 123751 := bstep (se 1 (by rfl) ⟨92813, by rfl⟩ : syracuseStep 123751 = 185627) B185627
theorem B123775 : Blo 119786 123775 := bstep (se 1 (by rfl) ⟨92831, by rfl⟩ : syracuseStep 123775 = 185663) B185663
theorem B386203 : Blo 119786 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B14838065 : Blo 119786 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B158015 : Blo 119786 158015 := bstep (se 1 (by rfl) ⟨118511, by rfl⟩ : syracuseStep 158015 = 237023) B237023
theorem B616895 : Blo 119786 616895 := bstep (se 1 (by rfl) ⟨462671, by rfl⟩ : syracuseStep 616895 = 925343) B925343
theorem B256871 : Blo 119786 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B519209 : Blo 119786 519209 := bstep (se 2 (by rfl) ⟨194703, by rfl⟩ : syracuseStep 519209 = 389407) B389407
theorem B290017 : Blo 119786 290017 := bstep (se 2 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 290017 = 217513) B217513
theorem B6254009 : Blo 119786 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B2650643 : Blo 119786 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B1667951 : Blo 119786 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B5371499 : Blo 119786 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B2947529 : Blo 119786 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B490121 : Blo 119786 490121 := bstep (se 2 (by rfl) ⟨183795, by rfl⟩ : syracuseStep 490121 = 367591) B367591
theorem B490607 : Blo 119786 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B3899663 : Blo 119786 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B655913 : Blo 119786 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B262919 : Blo 119786 262919 := bstep (se 1 (by rfl) ⟨197189, by rfl⟩ : syracuseStep 262919 = 394379) B394379
theorem B133531 : Blo 119786 133531 := bstep (se 1 (by rfl) ⟨100148, by rfl⟩ : syracuseStep 133531 = 200297) B200297
theorem B461821 : Blo 119786 461821 := bstep (se 3 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 461821 = 173183) B173183
theorem B4918427 : Blo 119786 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B626879 : Blo 119786 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B1184057 : Blo 119786 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B3249335 : Blo 119786 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B2365037 : Blo 119786 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B137839 : Blo 119786 137839 := bstep (se 1 (by rfl) ⟨103379, by rfl⟩ : syracuseStep 137839 = 206759) B206759
theorem B662143 : Blo 119786 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B171247 : Blo 119786 171247 := bstep (se 1 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 171247 = 256871) B256871
theorem B204329 : Blo 119786 204329 := bstep (se 2 (by rfl) ⟨76623, by rfl⟩ : syracuseStep 204329 = 153247) B153247
theorem B4169339 : Blo 119786 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B466985 : Blo 119786 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B3580999 : Blo 119786 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B10628819 : Blo 119786 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B208649 : Blo 119786 208649 := bstep (se 2 (by rfl) ⟨78243, by rfl⟩ : syracuseStep 208649 = 156487) B156487
theorem B274553 : Blo 119786 274553 := bstep (se 2 (by rfl) ⟨102957, by rfl⟩ : syracuseStep 274553 = 205915) B205915
theorem B143903 : Blo 119786 143903 := bstep (se 1 (by rfl) ⟨107927, by rfl⟩ : syracuseStep 143903 = 215855) B215855
theorem B308407 : Blo 119786 308407 := bstep (se 1 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 308407 = 462611) B462611
theorem B275903 : Blo 119786 275903 := bstep (se 1 (by rfl) ⟨206927, by rfl⟩ : syracuseStep 275903 = 413855) B413855
theorem B472559 : Blo 119786 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B308731 : Blo 119786 308731 := bstep (se 1 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 308731 = 463097) B463097
theorem B5617309 : Blo 119786 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B440495 : Blo 119786 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B180071 : Blo 119786 180071 := bstep (se 1 (by rfl) ⟨135053, by rfl⟩ : syracuseStep 180071 = 270107) B270107
theorem B409913 : Blo 119786 409913 := bstep (se 2 (by rfl) ⟨153717, by rfl⟩ : syracuseStep 409913 = 307435) B307435
theorem B180905 : Blo 119786 180905 := bstep (se 2 (by rfl) ⟨67839, by rfl⟩ : syracuseStep 180905 = 135679) B135679
theorem B312923 : Blo 119786 312923 := bstep (se 1 (by rfl) ⟨234692, by rfl⟩ : syracuseStep 312923 = 469385) B469385
theorem B411263 : Blo 119786 411263 := bstep (se 1 (by rfl) ⟨308447, by rfl⟩ : syracuseStep 411263 = 616895) B616895
theorem B346139 : Blo 119786 346139 := bstep (se 1 (by rfl) ⟨259604, by rfl⟩ : syracuseStep 346139 = 519209) B519209
theorem B182399 : Blo 119786 182399 := bstep (se 1 (by rfl) ⟨136799, by rfl⟩ : syracuseStep 182399 = 273599) B273599
theorem B1165913 : Blo 119786 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B183323 : Blo 119786 183323 := bstep (se 1 (by rfl) ⟨137492, by rfl⟩ : syracuseStep 183323 = 274985) B274985
theorem B183551 : Blo 119786 183551 := bstep (se 1 (by rfl) ⟨137663, by rfl⟩ : syracuseStep 183551 = 275327) B275327
theorem B183929 : Blo 119786 183929 := bstep (se 2 (by rfl) ⟨68973, by rfl⟩ : syracuseStep 183929 = 137947) B137947
theorem B184859 : Blo 119786 184859 := bstep (se 1 (by rfl) ⟨138644, by rfl⟩ : syracuseStep 184859 = 277289) B277289
theorem B11096837 : Blo 119786 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B119935 : Blo 119786 119935 := bstep (se 1 (by rfl) ⟨89951, by rfl⟩ : syracuseStep 119935 = 179903) B179903
theorem B120063 : Blo 119786 120063 := bstep (se 1 (by rfl) ⟨90047, by rfl⟩ : syracuseStep 120063 = 180095) B180095
theorem B120347 : Blo 119786 120347 := bstep (se 1 (by rfl) ⟨90260, by rfl⟩ : syracuseStep 120347 = 180521) B180521
theorem B218855 : Blo 119786 218855 := bstep (se 1 (by rfl) ⟨164141, by rfl⟩ : syracuseStep 218855 = 328283) B328283
theorem B120895 : Blo 119786 120895 := bstep (se 1 (by rfl) ⟨90671, by rfl⟩ : syracuseStep 120895 = 181343) B181343
theorem B1693817 : Blo 119786 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B121087 : Blo 119786 121087 := bstep (se 1 (by rfl) ⟨90815, by rfl⟩ : syracuseStep 121087 = 181631) B181631
theorem B121583 : Blo 119786 121583 := bstep (se 1 (by rfl) ⟨91187, by rfl⟩ : syracuseStep 121583 = 182375) B182375
theorem B514937 : Blo 119786 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B122011 : Blo 119786 122011 := bstep (se 1 (by rfl) ⟨91508, by rfl⟩ : syracuseStep 122011 = 183017) B183017
theorem B122495 : Blo 119786 122495 := bstep (se 1 (by rfl) ⟨91871, by rfl⟩ : syracuseStep 122495 = 183743) B183743
theorem B123007 : Blo 119786 123007 := bstep (se 1 (by rfl) ⟨92255, by rfl⟩ : syracuseStep 123007 = 184511) B184511
theorem B386639 : Blo 119786 386639 := bstep (se 1 (by rfl) ⟨289979, by rfl⟩ : syracuseStep 386639 = 579959) B579959
theorem B386689 : Blo 119786 386689 := bstep (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) B290017
theorem B3402607 : Blo 119786 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B421373 : Blo 119786 421373 := bstep (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) B158015
theorem B9892043 : Blo 119786 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B4714805 : Blo 119786 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B586493 : Blo 119786 586493 := bstep (se 3 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 586493 = 219935) B219935
theorem B3109913 : Blo 119786 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B1767095 : Blo 119786 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B1111967 : Blo 119786 1111967 := bstep (se 1 (by rfl) ⟨833975, by rfl⟩ : syracuseStep 1111967 = 1667951) B1667951
theorem B1965019 : Blo 119786 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B326747 : Blo 119786 326747 := bstep (se 1 (by rfl) ⟨245060, by rfl⟩ : syracuseStep 326747 = 490121) B490121
theorem B687311 : Blo 119786 687311 := bstep (se 1 (by rfl) ⟨515483, by rfl⟩ : syracuseStep 687311 = 1030967) B1030967
theorem B327071 : Blo 119786 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B230759 : Blo 119786 230759 := bstep (se 1 (by rfl) ⟨173069, by rfl⟩ : syracuseStep 230759 = 346139) B346139
theorem B3278951 : Blo 119786 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B789371 : Blo 119786 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B2166223 : Blo 119786 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B1576691 : Blo 119786 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B136219 : Blo 119786 136219 := bstep (se 1 (by rfl) ⟨102164, by rfl⟩ : syracuseStep 136219 = 204329) B204329
theorem B7085879 : Blo 119786 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B139099 : Blo 119786 139099 := bstep (se 1 (by rfl) ⟨104324, by rfl⟩ : syracuseStep 139099 = 208649) B208649
theorem B6594695 : Blo 119786 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B2073275 : Blo 119786 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B1123661 : Blo 119786 1123661 := bstep (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) B421373
theorem B2599775 : Blo 119786 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B273275 : Blo 119786 273275 := bstep (se 1 (by rfl) ⟨204956, by rfl⟩ : syracuseStep 273275 = 409913) B409913
theorem B437275 : Blo 119786 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B175279 : Blo 119786 175279 := bstep (se 1 (by rfl) ⟨131459, by rfl⟩ : syracuseStep 175279 = 262919) B262919
theorem B208615 : Blo 119786 208615 := bstep (se 1 (by rfl) ⟨156461, by rfl⟩ : syracuseStep 208615 = 312923) B312923
theorem B274175 : Blo 119786 274175 := bstep (se 1 (by rfl) ⟨205631, by rfl⟩ : syracuseStep 274175 = 411263) B411263
theorem B4536809 : Blo 119786 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B145903 : Blo 119786 145903 := bstep (se 1 (by rfl) ⟨109427, by rfl⟩ : syracuseStep 145903 = 218855) B218855
theorem B1260157 : Blo 119786 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B1129211 : Blo 119786 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B343291 : Blo 119786 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B311323 : Blo 119786 311323 := bstep (se 1 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 311323 = 466985) B466985
theorem B411209 : Blo 119786 411209 := bstep (se 2 (by rfl) ⟨154203, by rfl⟩ : syracuseStep 411209 = 308407) B308407
theorem B411641 : Blo 119786 411641 := bstep (se 2 (by rfl) ⟨154365, by rfl⟩ : syracuseStep 411641 = 308731) B308731
theorem B7489745 : Blo 119786 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B183035 : Blo 119786 183035 := bstep (se 1 (by rfl) ⟨137276, by rfl⟩ : syracuseStep 183035 = 274553) B274553
theorem B183785 : Blo 119786 183785 := bstep (se 2 (by rfl) ⟨68919, by rfl⟩ : syracuseStep 183785 = 137839) B137839
theorem B183935 : Blo 119786 183935 := bstep (se 1 (by rfl) ⟨137951, by rfl⟩ : syracuseStep 183935 = 275903) B275903
theorem B741311 : Blo 119786 741311 := bstep (se 1 (by rfl) ⟨555983, by rfl⟩ : syracuseStep 741311 = 1111967) B1111967
theorem B217831 : Blo 119786 217831 := bstep (se 1 (by rfl) ⟨163373, by rfl⟩ : syracuseStep 217831 = 326747) B326747
theorem B218047 : Blo 119786 218047 := bstep (se 1 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 218047 = 327071) B327071
theorem B120047 : Blo 119786 120047 := bstep (se 1 (by rfl) ⟨90035, by rfl⟩ : syracuseStep 120047 = 180071) B180071
theorem B120603 : Blo 119786 120603 := bstep (se 1 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 120603 = 180905) B180905
theorem B12572813 : Blo 119786 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B383741 : Blo 119786 383741 := bstep (se 3 (by rfl) ⟨71951, by rfl⟩ : syracuseStep 383741 = 143903) B143903
theorem B121599 : Blo 119786 121599 := bstep (se 1 (by rfl) ⟨91199, by rfl⟩ : syracuseStep 121599 = 182399) B182399
theorem B777275 : Blo 119786 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B122215 : Blo 119786 122215 := bstep (se 1 (by rfl) ⟨91661, by rfl⟩ : syracuseStep 122215 = 183323) B183323
theorem B712165 : Blo 119786 712165 := bstep (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) B133531
theorem B122367 : Blo 119786 122367 := bstep (se 1 (by rfl) ⟨91775, by rfl⟩ : syracuseStep 122367 = 183551) B183551
theorem B515585 : Blo 119786 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B122619 : Blo 119786 122619 := bstep (se 1 (by rfl) ⟨91964, by rfl⟩ : syracuseStep 122619 = 183929) B183929
theorem B417919 : Blo 119786 417919 := bstep (se 1 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 417919 = 626879) B626879
theorem B123239 : Blo 119786 123239 := bstep (se 1 (by rfl) ⟨92429, by rfl⟩ : syracuseStep 123239 = 184859) B184859
theorem B7397891 : Blo 119786 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B615761 : Blo 119786 615761 := bstep (se 2 (by rfl) ⟨230910, by rfl⟩ : syracuseStep 615761 = 461821) B461821
theorem B2779559 : Blo 119786 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B19098661 : Blo 119786 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B257759 : Blo 119786 257759 := bstep (se 1 (by rfl) ⟨193319, by rfl⟩ : syracuseStep 257759 = 386639) B386639
theorem B390995 : Blo 119786 390995 := bstep (se 1 (by rfl) ⟨293246, by rfl⟩ : syracuseStep 390995 = 586493) B586493
theorem B882857 : Blo 119786 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B1178063 : Blo 119786 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B2620025 : Blo 119786 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B293663 : Blo 119786 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B228329 : Blo 119786 228329 := bstep (se 2 (by rfl) ⟨85623, by rfl⟩ : syracuseStep 228329 = 171247) B171247
theorem B458207 : Blo 119786 458207 := bstep (se 1 (by rfl) ⟨343655, by rfl⟩ : syracuseStep 458207 = 687311) B687311
theorem B557225 : Blo 119786 557225 := bstep (se 2 (by rfl) ⟨208959, by rfl⟩ : syracuseStep 557225 = 417919) B417919
theorem B526247 : Blo 119786 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B1051127 : Blo 119786 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B494207 : Blo 119786 494207 := bstep (se 1 (by rfl) ⟨370655, by rfl⟩ : syracuseStep 494207 = 741311) B741311
theorem B25464881 : Blo 119786 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B233705 : Blo 119786 233705 := bstep (se 2 (by rfl) ⟨87639, by rfl⟩ : syracuseStep 233705 = 175279) B175279
theorem B2888297 : Blo 119786 2888297 := bstep (se 2 (by rfl) ⟨1083111, by rfl⟩ : syracuseStep 2888297 = 2166223) B2166223
theorem B4723919 : Blo 119786 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B4396463 : Blo 119786 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B1382183 : Blo 119786 1382183 := bstep (se 1 (by rfl) ⟨1036637, by rfl⟩ : syracuseStep 1382183 = 2073275) B2073275
theorem B171839 : Blo 119786 171839 := bstep (se 1 (by rfl) ⟨128879, by rfl⟩ : syracuseStep 171839 = 257759) B257759
theorem B1680209 : Blo 119786 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B3024539 : Blo 119786 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B1746683 : Blo 119786 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B305471 : Blo 119786 305471 := bstep (se 1 (by rfl) ⟨229103, by rfl⟩ : syracuseStep 305471 = 458207) B458207
theorem B274139 : Blo 119786 274139 := bstep (se 1 (by rfl) ⟨205604, by rfl⟩ : syracuseStep 274139 = 411209) B411209
theorem B274427 : Blo 119786 274427 := bstep (se 1 (by rfl) ⟨205820, by rfl⟩ : syracuseStep 274427 = 411641) B411641
theorem B4993163 : Blo 119786 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B278153 : Blo 119786 278153 := bstep (se 2 (by rfl) ⟨104307, by rfl⟩ : syracuseStep 278153 = 208615) B208615
theorem B4931927 : Blo 119786 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B410507 : Blo 119786 410507 := bstep (se 1 (by rfl) ⟨307880, by rfl⟩ : syracuseStep 410507 = 615761) B615761
theorem B181625 : Blo 119786 181625 := bstep (se 2 (by rfl) ⟨68109, by rfl⟩ : syracuseStep 181625 = 136219) B136219
theorem B1853039 : Blo 119786 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B182183 : Blo 119786 182183 := bstep (se 1 (by rfl) ⟨136637, by rfl⟩ : syracuseStep 182183 = 273275) B273275
theorem B182783 : Blo 119786 182783 := bstep (se 1 (by rfl) ⟨137087, by rfl⟩ : syracuseStep 182783 = 274175) B274175
theorem B152219 : Blo 119786 152219 := bstep (se 1 (by rfl) ⟨114164, by rfl⟩ : syracuseStep 152219 = 228329) B228329
theorem B185465 : Blo 119786 185465 := bstep (se 2 (by rfl) ⟨69549, by rfl⟩ : syracuseStep 185465 = 139099) B139099
theorem B415097 : Blo 119786 415097 := bstep (se 2 (by rfl) ⟨155661, by rfl⟩ : syracuseStep 415097 = 311323) B311323
theorem B153839 : Blo 119786 153839 := bstep (se 1 (by rfl) ⟨115379, by rfl⟩ : syracuseStep 153839 = 230759) B230759
theorem B2185967 : Blo 119786 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B122023 : Blo 119786 122023 := bstep (se 1 (by rfl) ⟨91517, by rfl⟩ : syracuseStep 122023 = 183035) B183035
theorem B122523 : Blo 119786 122523 := bstep (se 1 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 122523 = 183785) B183785
theorem B122623 : Blo 119786 122623 := bstep (se 1 (by rfl) ⟨91967, by rfl⟩ : syracuseStep 122623 = 183935) B183935
theorem B583033 : Blo 119786 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B8381875 : Blo 119786 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B255827 : Blo 119786 255827 := bstep (se 1 (by rfl) ⟨191870, by rfl⟩ : syracuseStep 255827 = 383741) B383741
theorem B518183 : Blo 119786 518183 := bstep (se 1 (by rfl) ⟨388637, by rfl⟩ : syracuseStep 518183 = 777275) B777275
theorem B2354285 : Blo 119786 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B749107 : Blo 119786 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B290441 : Blo 119786 290441 := bstep (se 2 (by rfl) ⟨108915, by rfl⟩ : syracuseStep 290441 = 217831) B217831
theorem B290729 : Blo 119786 290729 := bstep (se 2 (by rfl) ⟨109023, by rfl⟩ : syracuseStep 290729 = 218047) B218047
theorem B1733183 : Blo 119786 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B783101 : Blo 119786 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B194537 : Blo 119786 194537 := bstep (se 2 (by rfl) ⟨72951, by rfl⟩ : syracuseStep 194537 = 145903) B145903
theorem B260663 : Blo 119786 260663 := bstep (se 1 (by rfl) ⟨195497, by rfl⟩ : syracuseStep 260663 = 390995) B390995
theorem B1374893 : Blo 119786 1374893 := bstep (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) B515585
theorem B785375 : Blo 119786 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B457721 : Blo 119786 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B752807 : Blo 119786 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B949553 : Blo 119786 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B623213 : Blo 119786 623213 := bstep (se 3 (by rfl) ⟨116852, by rfl⟩ : syracuseStep 623213 = 233705) B233705
theorem B329471 : Blo 119786 329471 := bstep (se 1 (by rfl) ⟨247103, by rfl⟩ : syracuseStep 329471 = 494207) B494207
theorem B11175833 : Blo 119786 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B16976587 : Blo 119786 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B3149279 : Blo 119786 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B921455 : Blo 119786 921455 := bstep (se 1 (by rfl) ⟨691091, by rfl⟩ : syracuseStep 921455 = 1382183) B1382183
theorem B1120139 : Blo 119786 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B170551 : Blo 119786 170551 := bstep (se 1 (by rfl) ⟨127913, by rfl⟩ : syracuseStep 170551 = 255827) B255827
theorem B695101 : Blo 119786 695101 := bstep (se 3 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 695101 = 260663) B260663
theorem B203647 : Blo 119786 203647 := bstep (se 1 (by rfl) ⟨152735, by rfl⟩ : syracuseStep 203647 = 305471) B305471
theorem B1155455 : Blo 119786 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B305147 : Blo 119786 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B501871 : Blo 119786 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B633035 : Blo 119786 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B371483 : Blo 119786 371483 := bstep (se 1 (by rfl) ⟨278612, by rfl⟩ : syracuseStep 371483 = 557225) B557225
theorem B3287951 : Blo 119786 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B273671 : Blo 119786 273671 := bstep (se 1 (by rfl) ⟨205253, by rfl⟩ : syracuseStep 273671 = 410507) B410507
theorem B700751 : Blo 119786 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B405917 : Blo 119786 405917 := bstep (se 3 (by rfl) ⟨76109, by rfl⟩ : syracuseStep 405917 = 152219) B152219
theorem B276731 : Blo 119786 276731 := bstep (se 1 (by rfl) ⟨207548, by rfl⟩ : syracuseStep 276731 = 415097) B415097
theorem B2930975 : Blo 119786 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B410237 : Blo 119786 410237 := bstep (se 3 (by rfl) ⟨76919, by rfl⟩ : syracuseStep 410237 = 153839) B153839
theorem B2016359 : Blo 119786 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B1164455 : Blo 119786 1164455 := bstep (se 1 (by rfl) ⟨873341, by rfl⟩ : syracuseStep 1164455 = 1746683) B1746683
theorem B345455 : Blo 119786 345455 := bstep (se 1 (by rfl) ⟨259091, by rfl⟩ : syracuseStep 345455 = 518183) B518183
theorem B182759 : Blo 119786 182759 := bstep (se 1 (by rfl) ⟨137069, by rfl⟩ : syracuseStep 182759 = 274139) B274139
theorem B182951 : Blo 119786 182951 := bstep (se 1 (by rfl) ⟨137213, by rfl⟩ : syracuseStep 182951 = 274427) B274427
theorem B3328775 : Blo 119786 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B6278093 : Blo 119786 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B185435 : Blo 119786 185435 := bstep (se 1 (by rfl) ⟨139076, by rfl⟩ : syracuseStep 185435 = 278153) B278153
theorem B775277 : Blo 119786 775277 := bstep (se 3 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 775277 = 290729) B290729
theorem B121083 : Blo 119786 121083 := bstep (se 1 (by rfl) ⟨90812, by rfl⟩ : syracuseStep 121083 = 181625) B181625
theorem B1235359 : Blo 119786 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B121455 : Blo 119786 121455 := bstep (se 1 (by rfl) ⟨91091, by rfl⟩ : syracuseStep 121455 = 182183) B182183
theorem B350831 : Blo 119786 350831 := bstep (se 1 (by rfl) ⟨263123, by rfl⟩ : syracuseStep 350831 = 526247) B526247
theorem B121855 : Blo 119786 121855 := bstep (se 1 (by rfl) ⟨91391, by rfl⟩ : syracuseStep 121855 = 182783) B182783
theorem B777377 : Blo 119786 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B1925531 : Blo 119786 1925531 := bstep (se 1 (by rfl) ⟨1444148, by rfl⟩ : syracuseStep 1925531 = 2888297) B2888297
theorem B123643 : Blo 119786 123643 := bstep (se 1 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 123643 = 185465) B185465
theorem B5829245 : Blo 119786 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B193627 : Blo 119786 193627 := bstep (se 1 (by rfl) ⟨145220, by rfl⟩ : syracuseStep 193627 = 290441) B290441
theorem B3995237 : Blo 119786 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B522067 : Blo 119786 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B129691 : Blo 119786 129691 := bstep (se 1 (by rfl) ⟨97268, by rfl⟩ : syracuseStep 129691 = 194537) B194537
theorem B916595 : Blo 119786 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B523583 : Blo 119786 523583 := bstep (se 1 (by rfl) ⟨392687, by rfl⟩ : syracuseStep 523583 = 785375) B785375
theorem B458237 : Blo 119786 458237 := bstep (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) B171839
theorem B1344239 : Blo 119786 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B230303 : Blo 119786 230303 := bstep (se 1 (by rfl) ⟨172727, by rfl⟩ : syracuseStep 230303 = 345455) B345455
theorem B2099519 : Blo 119786 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B691685 : Blo 119786 691685 := bstep (se 4 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 691685 = 129691) B129691
theorem B1283687 : Blo 119786 1283687 := bstep (se 1 (by rfl) ⟨962765, by rfl⟩ : syracuseStep 1283687 = 1925531) B1925531
theorem B203431 : Blo 119786 203431 := bstep (se 1 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 203431 = 305147) B305147
theorem B696089 : Blo 119786 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B467167 : Blo 119786 467167 := bstep (se 1 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 467167 = 700751) B700751
theorem B270611 : Blo 119786 270611 := bstep (se 1 (by rfl) ⟨202958, by rfl⟩ : syracuseStep 270611 = 405917) B405917
theorem B1647145 : Blo 119786 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B2663491 : Blo 119786 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B926801 : Blo 119786 926801 := bstep (se 2 (by rfl) ⟨347550, by rfl⟩ : syracuseStep 926801 = 695101) B695101
theorem B271529 : Blo 119786 271529 := bstep (se 2 (by rfl) ⟨101823, by rfl⟩ : syracuseStep 271529 = 203647) B203647
theorem B305491 : Blo 119786 305491 := bstep (se 1 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 305491 = 458237) B458237
theorem B273491 : Blo 119786 273491 := bstep (se 1 (by rfl) ⟨205118, by rfl⟩ : syracuseStep 273491 = 410237) B410237
theorem B7450555 : Blo 119786 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B669161 : Blo 119786 669161 := bstep (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) B501871
theorem B770303 : Blo 119786 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B935549 : Blo 119786 935549 := bstep (se 3 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 935549 = 350831) B350831
theorem B247655 : Blo 119786 247655 := bstep (se 1 (by rfl) ⟨185741, by rfl⟩ : syracuseStep 247655 = 371483) B371483
theorem B182447 : Blo 119786 182447 := bstep (se 1 (by rfl) ⟨136835, by rfl⟩ : syracuseStep 182447 = 273671) B273671
theorem B3886163 : Blo 119786 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B184487 : Blo 119786 184487 := bstep (se 1 (by rfl) ⟨138365, by rfl⟩ : syracuseStep 184487 = 276731) B276731
theorem B1953983 : Blo 119786 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B611063 : Blo 119786 611063 := bstep (se 1 (by rfl) ⟨458297, by rfl⟩ : syracuseStep 611063 = 916595) B916595
theorem B349055 : Blo 119786 349055 := bstep (se 1 (by rfl) ⟨261791, by rfl⟩ : syracuseStep 349055 = 523583) B523583
theorem B415475 : Blo 119786 415475 := bstep (se 1 (by rfl) ⟨311606, by rfl⟩ : syracuseStep 415475 = 623213) B623213
theorem B776303 : Blo 119786 776303 := bstep (se 1 (by rfl) ⟨582227, by rfl⟩ : syracuseStep 776303 = 1164455) B1164455
theorem B219647 : Blo 119786 219647 := bstep (se 1 (by rfl) ⟨164735, by rfl⟩ : syracuseStep 219647 = 329471) B329471
theorem B121839 : Blo 119786 121839 := bstep (se 1 (by rfl) ⟨91379, by rfl⟩ : syracuseStep 121839 = 182759) B182759
theorem B121967 : Blo 119786 121967 := bstep (se 1 (by rfl) ⟨91475, by rfl⟩ : syracuseStep 121967 = 182951) B182951
theorem B2219183 : Blo 119786 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B4185395 : Blo 119786 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B614303 : Blo 119786 614303 := bstep (se 1 (by rfl) ⟨460727, by rfl⟩ : syracuseStep 614303 = 921455) B921455
theorem B909605 : Blo 119786 909605 := bstep (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) B170551
theorem B123623 : Blo 119786 123623 := bstep (se 1 (by rfl) ⟨92717, by rfl⟩ : syracuseStep 123623 = 185435) B185435
theorem B516851 : Blo 119786 516851 := bstep (se 1 (by rfl) ⟨387638, by rfl⟩ : syracuseStep 516851 = 775277) B775277
theorem B22635449 : Blo 119786 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B746759 : Blo 119786 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B518251 : Blo 119786 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B258169 : Blo 119786 258169 := bstep (se 2 (by rfl) ⟨96813, by rfl⟩ : syracuseStep 258169 = 193627) B193627
theorem B422023 : Blo 119786 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B2191967 : Blo 119786 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B622889 : Blo 119786 622889 := bstep (se 2 (by rfl) ⟨233583, by rfl⟩ : syracuseStep 622889 = 467167) B467167
theorem B2196193 : Blo 119786 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B623699 : Blo 119786 623699 := bstep (se 1 (by rfl) ⟨467774, by rfl⟩ : syracuseStep 623699 = 935549) B935549
theorem B2590775 : Blo 119786 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B461123 : Blo 119786 461123 := bstep (se 1 (by rfl) ⟨345842, by rfl⟩ : syracuseStep 461123 = 691685) B691685
theorem B691001 : Blo 119786 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B232703 : Blo 119786 232703 := bstep (se 1 (by rfl) ⟨174527, by rfl⟩ : syracuseStep 232703 = 349055) B349055
theorem B855791 : Blo 119786 855791 := bstep (se 1 (by rfl) ⟨641843, by rfl⟩ : syracuseStep 855791 = 1283687) B1283687
theorem B1479455 : Blo 119786 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B2790263 : Blo 119786 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B660413 : Blo 119786 660413 := bstep (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) B247655
theorem B464059 : Blo 119786 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B9934073 : Blo 119786 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B562697 : Blo 119786 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B497839 : Blo 119786 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B271241 : Blo 119786 271241 := bstep (se 2 (by rfl) ⟨101715, by rfl⟩ : syracuseStep 271241 = 203431) B203431
theorem B896159 : Blo 119786 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B3551321 : Blo 119786 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B407321 : Blo 119786 407321 := bstep (se 2 (by rfl) ⟨152745, by rfl⟩ : syracuseStep 407321 = 305491) B305491
theorem B407375 : Blo 119786 407375 := bstep (se 1 (by rfl) ⟨305531, by rfl⟩ : syracuseStep 407375 = 611063) B611063
theorem B276983 : Blo 119786 276983 := bstep (se 1 (by rfl) ⟨207737, by rfl⟩ : syracuseStep 276983 = 415475) B415475
theorem B146431 : Blo 119786 146431 := bstep (se 1 (by rfl) ⟨109823, by rfl⟩ : syracuseStep 146431 = 219647) B219647
theorem B409535 : Blo 119786 409535 := bstep (se 1 (by rfl) ⟨307151, by rfl⟩ : syracuseStep 409535 = 614303) B614303
theorem B344225 : Blo 119786 344225 := bstep (se 2 (by rfl) ⟨129084, by rfl⟩ : syracuseStep 344225 = 258169) B258169
theorem B180407 : Blo 119786 180407 := bstep (se 1 (by rfl) ⟨135305, by rfl⟩ : syracuseStep 180407 = 270611) B270611
theorem B606403 : Blo 119786 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B344567 : Blo 119786 344567 := bstep (se 1 (by rfl) ⟨258425, by rfl⟩ : syracuseStep 344567 = 516851) B516851
theorem B15090299 : Blo 119786 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B181019 : Blo 119786 181019 := bstep (se 1 (by rfl) ⟨135764, by rfl⟩ : syracuseStep 181019 = 271529) B271529
theorem B182327 : Blo 119786 182327 := bstep (se 1 (by rfl) ⟨136745, by rfl⟩ : syracuseStep 182327 = 273491) B273491
theorem B1461311 : Blo 119786 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B446107 : Blo 119786 446107 := bstep (se 1 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 446107 = 669161) B669161
theorem B513535 : Blo 119786 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B121631 : Blo 119786 121631 := bstep (se 1 (by rfl) ⟨91223, by rfl⟩ : syracuseStep 121631 = 182447) B182447
theorem B1399679 : Blo 119786 1399679 := bstep (se 1 (by rfl) ⟨1049759, by rfl⟩ : syracuseStep 1399679 = 2099519) B2099519
theorem B614141 : Blo 119786 614141 := bstep (se 3 (by rfl) ⟨115151, by rfl⟩ : syracuseStep 614141 = 230303) B230303
theorem B122991 : Blo 119786 122991 := bstep (se 1 (by rfl) ⟨92243, by rfl⟩ : syracuseStep 122991 = 184487) B184487
theorem B1302655 : Blo 119786 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B517535 : Blo 119786 517535 := bstep (se 1 (by rfl) ⟨388151, by rfl⟩ : syracuseStep 517535 = 776303) B776303
theorem B617867 : Blo 119786 617867 := bstep (se 1 (by rfl) ⟨463400, by rfl⟩ : syracuseStep 617867 = 926801) B926801
theorem B229483 : Blo 119786 229483 := bstep (se 1 (by rfl) ⟨172112, by rfl⟩ : syracuseStep 229483 = 344225) B344225
theorem B1736873 : Blo 119786 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B9470189 : Blo 119786 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B229711 : Blo 119786 229711 := bstep (se 1 (by rfl) ⟨172283, by rfl⟩ : syracuseStep 229711 = 344567) B344567
theorem B10060199 : Blo 119786 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B460667 : Blo 119786 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B986303 : Blo 119786 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B6622715 : Blo 119786 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B594809 : Blo 119786 594809 := bstep (se 2 (by rfl) ⟨223053, by rfl⟩ : syracuseStep 594809 = 446107) B446107
theorem B597439 : Blo 119786 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B663785 : Blo 119786 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B271547 : Blo 119786 271547 := bstep (se 1 (by rfl) ⟨203660, by rfl⟩ : syracuseStep 271547 = 407321) B407321
theorem B271583 : Blo 119786 271583 := bstep (se 1 (by rfl) ⟨203687, by rfl⟩ : syracuseStep 271583 = 407375) B407375
theorem B273023 : Blo 119786 273023 := bstep (se 1 (by rfl) ⟨204767, by rfl⟩ : syracuseStep 273023 = 409535) B409535
theorem B2928257 : Blo 119786 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B307415 : Blo 119786 307415 := bstep (se 1 (by rfl) ⟨230561, by rfl⟩ : syracuseStep 307415 = 461123) B461123
theorem B570527 : Blo 119786 570527 := bstep (se 1 (by rfl) ⟨427895, by rfl⟩ : syracuseStep 570527 = 855791) B855791
theorem B440275 : Blo 119786 440275 := bstep (se 1 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 440275 = 660413) B660413
theorem B375131 : Blo 119786 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B933119 : Blo 119786 933119 := bstep (se 1 (by rfl) ⟨699839, by rfl⟩ : syracuseStep 933119 = 1399679) B1399679
theorem B409427 : Blo 119786 409427 := bstep (se 1 (by rfl) ⟨307070, by rfl⟩ : syracuseStep 409427 = 614141) B614141
theorem B180827 : Blo 119786 180827 := bstep (se 1 (by rfl) ⟨135620, by rfl⟩ : syracuseStep 180827 = 271241) B271241
theorem B345023 : Blo 119786 345023 := bstep (se 1 (by rfl) ⟨258767, by rfl⟩ : syracuseStep 345023 = 517535) B517535
theorem B411911 : Blo 119786 411911 := bstep (se 1 (by rfl) ⟨308933, by rfl⟩ : syracuseStep 411911 = 617867) B617867
theorem B184655 : Blo 119786 184655 := bstep (se 1 (by rfl) ⟨138491, by rfl⟩ : syracuseStep 184655 = 276983) B276983
theorem B120271 : Blo 119786 120271 := bstep (se 1 (by rfl) ⟨90203, by rfl⟩ : syracuseStep 120271 = 180407) B180407
theorem B415259 : Blo 119786 415259 := bstep (se 1 (by rfl) ⟨311444, by rfl⟩ : syracuseStep 415259 = 622889) B622889
theorem B808537 : Blo 119786 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B120679 : Blo 119786 120679 := bstep (se 1 (by rfl) ⟨90509, by rfl⟩ : syracuseStep 120679 = 181019) B181019
theorem B415799 : Blo 119786 415799 := bstep (se 1 (by rfl) ⟨311849, by rfl⟩ : syracuseStep 415799 = 623699) B623699
theorem B1727183 : Blo 119786 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B121551 : Blo 119786 121551 := bstep (se 1 (by rfl) ⟨91163, by rfl⟩ : syracuseStep 121551 = 182327) B182327
theorem B974207 : Blo 119786 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B155135 : Blo 119786 155135 := bstep (se 1 (by rfl) ⟨116351, by rfl⟩ : syracuseStep 155135 = 232703) B232703
theorem B1860175 : Blo 119786 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B780965 : Blo 119786 780965 := bstep (se 4 (by rfl) ⟨73215, by rfl⟩ : syracuseStep 780965 = 146431) B146431
theorem B618745 : Blo 119786 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B684713 : Blo 119786 684713 := bstep (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) B513535
theorem B230015 : Blo 119786 230015 := bstep (se 1 (by rfl) ⟨172511, by rfl⟩ : syracuseStep 230015 = 345023) B345023
theorem B396539 : Blo 119786 396539 := bstep (se 1 (by rfl) ⟨297404, by rfl⟩ : syracuseStep 396539 = 594809) B594809
theorem B824993 : Blo 119786 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B3186341 : Blo 119786 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B204943 : Blo 119786 204943 := bstep (se 1 (by rfl) ⟨153707, by rfl⟩ : syracuseStep 204943 = 307415) B307415
theorem B2630141 : Blo 119786 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B272951 : Blo 119786 272951 := bstep (se 1 (by rfl) ⟨204713, by rfl⟩ : syracuseStep 272951 = 409427) B409427
theorem B1157915 : Blo 119786 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B305977 : Blo 119786 305977 := bstep (se 2 (by rfl) ⟨114741, by rfl⟩ : syracuseStep 305977 = 229483) B229483
theorem B306281 : Blo 119786 306281 := bstep (se 2 (by rfl) ⟨114855, by rfl⟩ : syracuseStep 306281 = 229711) B229711
theorem B307111 : Blo 119786 307111 := bstep (se 1 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 307111 = 460667) B460667
theorem B274607 : Blo 119786 274607 := bstep (se 1 (by rfl) ⟨205955, by rfl⟩ : syracuseStep 274607 = 411911) B411911
theorem B276839 : Blo 119786 276839 := bstep (se 1 (by rfl) ⟨207629, by rfl⟩ : syracuseStep 276839 = 415259) B415259
theorem B277199 : Blo 119786 277199 := bstep (se 1 (by rfl) ⟨207899, by rfl⟩ : syracuseStep 277199 = 415799) B415799
theorem B442523 : Blo 119786 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B181031 : Blo 119786 181031 := bstep (se 1 (by rfl) ⟨135773, by rfl⟩ : syracuseStep 181031 = 271547) B271547
theorem B181055 : Blo 119786 181055 := bstep (se 1 (by rfl) ⟨135791, by rfl⟩ : syracuseStep 181055 = 271583) B271583
theorem B1000349 : Blo 119786 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B182015 : Blo 119786 182015 := bstep (se 1 (by rfl) ⟨136511, by rfl⟩ : syracuseStep 182015 = 273023) B273023
theorem B4605821 : Blo 119786 4605821 := bstep (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) B1727183
theorem B1952171 : Blo 119786 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B380351 : Blo 119786 380351 := bstep (se 1 (by rfl) ⟨285263, by rfl⟩ : syracuseStep 380351 = 570527) B570527
theorem B413693 : Blo 119786 413693 := bstep (se 3 (by rfl) ⟨77567, by rfl⟩ : syracuseStep 413693 = 155135) B155135
theorem B6313459 : Blo 119786 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B6706799 : Blo 119786 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B120551 : Blo 119786 120551 := bstep (se 1 (by rfl) ⟨90413, by rfl⟩ : syracuseStep 120551 = 180827) B180827
theorem B2480233 : Blo 119786 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B4415143 : Blo 119786 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B123103 : Blo 119786 123103 := bstep (se 1 (by rfl) ⟨92327, by rfl⟩ : syracuseStep 123103 = 184655) B184655
theorem B649471 : Blo 119786 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B520643 : Blo 119786 520643 := bstep (se 1 (by rfl) ⟨390482, by rfl⟩ : syracuseStep 520643 = 780965) B780965
theorem B1078049 : Blo 119786 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B587033 : Blo 119786 587033 := bstep (se 2 (by rfl) ⟨220137, by rfl⟩ : syracuseStep 587033 = 440275) B440275
theorem B456475 : Blo 119786 456475 := bstep (se 1 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 456475 = 684713) B684713
theorem B622079 : Blo 119786 622079 := bstep (se 1 (by rfl) ⟨466559, by rfl⟩ : syracuseStep 622079 = 933119) B933119
theorem B295015 : Blo 119786 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B264359 : Blo 119786 264359 := bstep (se 1 (by rfl) ⟨198269, by rfl⟩ : syracuseStep 264359 = 396539) B396539
theorem B204187 : Blo 119786 204187 := bstep (se 1 (by rfl) ⟨153140, by rfl⟩ : syracuseStep 204187 = 306281) B306281
theorem B273257 : Blo 119786 273257 := bstep (se 2 (by rfl) ⟨102471, by rfl⟩ : syracuseStep 273257 = 204943) B204943
theorem B666899 : Blo 119786 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B275795 : Blo 119786 275795 := bstep (se 1 (by rfl) ⟨206846, by rfl⟩ : syracuseStep 275795 = 413693) B413693
theorem B865961 : Blo 119786 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B4471199 : Blo 119786 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B407969 : Blo 119786 407969 := bstep (se 2 (by rfl) ⟨152988, by rfl⟩ : syracuseStep 407969 = 305977) B305977
theorem B409481 : Blo 119786 409481 := bstep (se 2 (by rfl) ⟨153555, by rfl⟩ : syracuseStep 409481 = 307111) B307111
theorem B1753427 : Blo 119786 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B181967 : Blo 119786 181967 := bstep (se 1 (by rfl) ⟨136475, by rfl⟩ : syracuseStep 181967 = 272951) B272951
theorem B771943 : Blo 119786 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B608633 : Blo 119786 608633 := bstep (se 2 (by rfl) ⟨228237, by rfl⟩ : syracuseStep 608633 = 456475) B456475
theorem B183071 : Blo 119786 183071 := bstep (se 1 (by rfl) ⟨137303, by rfl⟩ : syracuseStep 183071 = 274607) B274607
theorem B347095 : Blo 119786 347095 := bstep (se 1 (by rfl) ⟨260321, by rfl⟩ : syracuseStep 347095 = 520643) B520643
theorem B184559 : Blo 119786 184559 := bstep (se 1 (by rfl) ⟨138419, by rfl⟩ : syracuseStep 184559 = 276839) B276839
theorem B184799 : Blo 119786 184799 := bstep (se 1 (by rfl) ⟨138599, by rfl⟩ : syracuseStep 184799 = 277199) B277199
theorem B5886857 : Blo 119786 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B414719 : Blo 119786 414719 := bstep (se 1 (by rfl) ⟨311039, by rfl⟩ : syracuseStep 414719 = 622079) B622079
theorem B153343 : Blo 119786 153343 := bstep (se 1 (by rfl) ⟨115007, by rfl⟩ : syracuseStep 153343 = 230015) B230015
theorem B120687 : Blo 119786 120687 := bstep (se 1 (by rfl) ⟨90515, by rfl⟩ : syracuseStep 120687 = 181031) B181031
theorem B120703 : Blo 119786 120703 := bstep (se 1 (by rfl) ⟨90527, by rfl⟩ : syracuseStep 120703 = 181055) B181055
theorem B121343 : Blo 119786 121343 := bstep (se 1 (by rfl) ⟨91007, by rfl⟩ : syracuseStep 121343 = 182015) B182015
theorem B3070547 : Blo 119786 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B1301447 : Blo 119786 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B2874797 : Blo 119786 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B253567 : Blo 119786 253567 := bstep (se 1 (by rfl) ⟨190175, by rfl⟩ : syracuseStep 253567 = 380351) B380351
theorem B549995 : Blo 119786 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B2124227 : Blo 119786 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B8417945 : Blo 119786 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B3306977 : Blo 119786 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B391355 : Blo 119786 391355 := bstep (se 1 (by rfl) ⟨293516, by rfl⟩ : syracuseStep 391355 = 587033) B587033
theorem B393353 : Blo 119786 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B5866613 : Blo 119786 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B462793 : Blo 119786 462793 := bstep (se 2 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 462793 = 347095) B347095
theorem B1416151 : Blo 119786 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B204457 : Blo 119786 204457 := bstep (se 2 (by rfl) ⟨76671, by rfl⟩ : syracuseStep 204457 = 153343) B153343
theorem B5611963 : Blo 119786 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B2204651 : Blo 119786 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B271979 : Blo 119786 271979 := bstep (se 1 (by rfl) ⟨203984, by rfl⟩ : syracuseStep 271979 = 407969) B407969
theorem B272249 : Blo 119786 272249 := bstep (se 2 (by rfl) ⟨102093, by rfl⟩ : syracuseStep 272249 = 204187) B204187
theorem B338089 : Blo 119786 338089 := bstep (se 2 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 338089 = 253567) B253567
theorem B272987 : Blo 119786 272987 := bstep (se 1 (by rfl) ⟨204740, by rfl⟩ : syracuseStep 272987 = 409481) B409481
theorem B176239 : Blo 119786 176239 := bstep (se 1 (by rfl) ⟨132179, by rfl⟩ : syracuseStep 176239 = 264359) B264359
theorem B405755 : Blo 119786 405755 := bstep (se 1 (by rfl) ⟨304316, by rfl⟩ : syracuseStep 405755 = 608633) B608633
theorem B1029257 : Blo 119786 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B276479 : Blo 119786 276479 := bstep (se 1 (by rfl) ⟨207359, by rfl⟩ : syracuseStep 276479 = 414719) B414719
theorem B2047031 : Blo 119786 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B867631 : Blo 119786 867631 := bstep (se 1 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 867631 = 1301447) B1301447
theorem B1916531 : Blo 119786 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B182171 : Blo 119786 182171 := bstep (se 1 (by rfl) ⟨136628, by rfl⟩ : syracuseStep 182171 = 273257) B273257
theorem B444599 : Blo 119786 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B183863 : Blo 119786 183863 := bstep (se 1 (by rfl) ⟨137897, by rfl⟩ : syracuseStep 183863 = 275795) B275795
theorem B577307 : Blo 119786 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B1168951 : Blo 119786 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B121311 : Blo 119786 121311 := bstep (se 1 (by rfl) ⟨90983, by rfl⟩ : syracuseStep 121311 = 181967) B181967
theorem B122047 : Blo 119786 122047 := bstep (se 1 (by rfl) ⟨91535, by rfl⟩ : syracuseStep 122047 = 183071) B183071
theorem B123039 : Blo 119786 123039 := bstep (se 1 (by rfl) ⟨92279, by rfl⟩ : syracuseStep 123039 = 184559) B184559
theorem B123199 : Blo 119786 123199 := bstep (se 1 (by rfl) ⟨92399, by rfl⟩ : syracuseStep 123199 = 184799) B184799
theorem B3924571 : Blo 119786 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B260903 : Blo 119786 260903 := bstep (se 1 (by rfl) ⟨195677, by rfl⟩ : syracuseStep 260903 = 391355) B391355
theorem B2980799 : Blo 119786 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B262235 : Blo 119786 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B296399 : Blo 119786 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B270503 : Blo 119786 270503 := bstep (se 1 (by rfl) ⟨202877, by rfl⟩ : syracuseStep 270503 = 405755) B405755
theorem B1156841 : Blo 119786 1156841 := bstep (se 2 (by rfl) ⟨433815, by rfl⟩ : syracuseStep 1156841 = 867631) B867631
theorem B173935 : Blo 119786 173935 := bstep (se 1 (by rfl) ⟨130451, by rfl⟩ : syracuseStep 173935 = 260903) B260903
theorem B272609 : Blo 119786 272609 := bstep (se 2 (by rfl) ⟨102228, by rfl⟩ : syracuseStep 272609 = 204457) B204457
theorem B7482617 : Blo 119786 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B3911075 : Blo 119786 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B181319 : Blo 119786 181319 := bstep (se 1 (by rfl) ⟨135989, by rfl⟩ : syracuseStep 181319 = 271979) B271979
theorem B181499 : Blo 119786 181499 := bstep (se 1 (by rfl) ⟨136124, by rfl⟩ : syracuseStep 181499 = 272249) B272249
theorem B181991 : Blo 119786 181991 := bstep (se 1 (by rfl) ⟨136493, by rfl⟩ : syracuseStep 181991 = 272987) B272987
theorem B1558601 : Blo 119786 1558601 := bstep (se 2 (by rfl) ⟨584475, by rfl⟩ : syracuseStep 1558601 = 1168951) B1168951
theorem B1888201 : Blo 119786 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B184319 : Blo 119786 184319 := bstep (se 1 (by rfl) ⟨138239, by rfl⟩ : syracuseStep 184319 = 276479) B276479
theorem B1987199 : Blo 119786 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B1364687 : Blo 119786 1364687 := bstep (se 1 (by rfl) ⟨1023515, by rfl⟩ : syracuseStep 1364687 = 2047031) B2047031
theorem B939941 : Blo 119786 939941 := bstep (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) B176239
theorem B5232761 : Blo 119786 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B121447 : Blo 119786 121447 := bstep (se 1 (by rfl) ⟨91085, by rfl⟩ : syracuseStep 121447 = 182171) B182171
theorem B122575 : Blo 119786 122575 := bstep (se 1 (by rfl) ⟨91931, by rfl⟩ : syracuseStep 122575 = 183863) B183863
theorem B384871 : Blo 119786 384871 := bstep (se 1 (by rfl) ⟨288653, by rfl⟩ : syracuseStep 384871 = 577307) B577307
theorem B450785 : Blo 119786 450785 := bstep (se 2 (by rfl) ⟨169044, by rfl⟩ : syracuseStep 450785 = 338089) B338089
theorem B617057 : Blo 119786 617057 := bstep (se 2 (by rfl) ⟨231396, by rfl⟩ : syracuseStep 617057 = 462793) B462793
theorem B1469767 : Blo 119786 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B686171 : Blo 119786 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B1277687 : Blo 119786 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B231913 : Blo 119786 231913 := bstep (se 2 (by rfl) ⟨86967, by rfl⟩ : syracuseStep 231913 = 173935) B173935
theorem B790397 : Blo 119786 790397 := bstep (se 3 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 790397 = 296399) B296399
theorem B626627 : Blo 119786 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B300523 : Blo 119786 300523 := bstep (se 1 (by rfl) ⟨225392, by rfl⟩ : syracuseStep 300523 = 450785) B450785
theorem B4988411 : Blo 119786 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B699293 : Blo 119786 699293 := bstep (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) B262235
theorem B1324799 : Blo 119786 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B3488507 : Blo 119786 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B180335 : Blo 119786 180335 := bstep (se 1 (by rfl) ⟨135251, by rfl⟩ : syracuseStep 180335 = 270503) B270503
theorem B771227 : Blo 119786 771227 := bstep (se 1 (by rfl) ⟨578420, by rfl⟩ : syracuseStep 771227 = 1156841) B1156841
theorem B181739 : Blo 119786 181739 := bstep (se 1 (by rfl) ⟨136304, by rfl⟩ : syracuseStep 181739 = 272609) B272609
theorem B411371 : Blo 119786 411371 := bstep (se 1 (by rfl) ⟨308528, by rfl⟩ : syracuseStep 411371 = 617057) B617057
theorem B2607383 : Blo 119786 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B513161 : Blo 119786 513161 := bstep (se 2 (by rfl) ⟨192435, by rfl⟩ : syracuseStep 513161 = 384871) B384871
theorem B120879 : Blo 119786 120879 := bstep (se 1 (by rfl) ⟨90659, by rfl⟩ : syracuseStep 120879 = 181319) B181319
theorem B120999 : Blo 119786 120999 := bstep (se 1 (by rfl) ⟨90749, by rfl⟩ : syracuseStep 120999 = 181499) B181499
theorem B121327 : Blo 119786 121327 := bstep (se 1 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 121327 = 181991) B181991
theorem B1039067 : Blo 119786 1039067 := bstep (se 1 (by rfl) ⟨779300, by rfl⟩ : syracuseStep 1039067 = 1558601) B1558601
theorem B122879 : Blo 119786 122879 := bstep (se 1 (by rfl) ⟨92159, by rfl⟩ : syracuseStep 122879 = 184319) B184319
theorem B909791 : Blo 119786 909791 := bstep (se 1 (by rfl) ⟨682343, by rfl⟩ : syracuseStep 909791 = 1364687) B1364687
theorem B1959689 : Blo 119786 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B2517601 : Blo 119786 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B457447 : Blo 119786 457447 := bstep (se 1 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 457447 = 686171) B686171
theorem B851791 : Blo 119786 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B1738255 : Blo 119786 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B526931 : Blo 119786 526931 := bstep (se 1 (by rfl) ⟨395198, by rfl⟩ : syracuseStep 526931 = 790397) B790397
theorem B692711 : Blo 119786 692711 := bstep (se 1 (by rfl) ⟨519533, by rfl⟩ : syracuseStep 692711 = 1039067) B1039067
theorem B466195 : Blo 119786 466195 := bstep (se 1 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 466195 = 699293) B699293
theorem B400697 : Blo 119786 400697 := bstep (se 2 (by rfl) ⟨150261, by rfl⟩ : syracuseStep 400697 = 300523) B300523
theorem B274247 : Blo 119786 274247 := bstep (se 1 (by rfl) ⟨205685, by rfl⟩ : syracuseStep 274247 = 411371) B411371
theorem B309217 : Blo 119786 309217 := bstep (se 2 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 309217 = 231913) B231913
theorem B342107 : Blo 119786 342107 := bstep (se 1 (by rfl) ⟨256580, by rfl⟩ : syracuseStep 342107 = 513161) B513161
theorem B3356801 : Blo 119786 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B3325607 : Blo 119786 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B606527 : Blo 119786 606527 := bstep (se 1 (by rfl) ⟨454895, by rfl⟩ : syracuseStep 606527 = 909791) B909791
theorem B609929 : Blo 119786 609929 := bstep (se 2 (by rfl) ⟨228723, by rfl⟩ : syracuseStep 609929 = 457447) B457447
theorem B1135721 : Blo 119786 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B120223 : Blo 119786 120223 := bstep (se 1 (by rfl) ⟨90167, by rfl⟩ : syracuseStep 120223 = 180335) B180335
theorem B514151 : Blo 119786 514151 := bstep (se 1 (by rfl) ⟨385613, by rfl⟩ : syracuseStep 514151 = 771227) B771227
theorem B121159 : Blo 119786 121159 := bstep (se 1 (by rfl) ⟨90869, by rfl⟩ : syracuseStep 121159 = 181739) B181739
theorem B1306459 : Blo 119786 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B883199 : Blo 119786 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B2325671 : Blo 119786 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B1671005 : Blo 119786 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B461807 : Blo 119786 461807 := bstep (se 1 (by rfl) ⟨346355, by rfl⟩ : syracuseStep 461807 = 692711) B692711
theorem B757147 : Blo 119786 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B267131 : Blo 119786 267131 := bstep (se 1 (by rfl) ⟨200348, by rfl⟩ : syracuseStep 267131 = 400697) B400697
theorem B2237867 : Blo 119786 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B1550447 : Blo 119786 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B404351 : Blo 119786 404351 := bstep (se 1 (by rfl) ⟨303263, by rfl⟩ : syracuseStep 404351 = 606527) B606527
theorem B406619 : Blo 119786 406619 := bstep (se 1 (by rfl) ⟨304964, by rfl⟩ : syracuseStep 406619 = 609929) B609929
theorem B342767 : Blo 119786 342767 := bstep (se 1 (by rfl) ⟨257075, by rfl⟩ : syracuseStep 342767 = 514151) B514151
theorem B182831 : Blo 119786 182831 := bstep (se 1 (by rfl) ⟨137123, by rfl⟩ : syracuseStep 182831 = 274247) B274247
theorem B412289 : Blo 119786 412289 := bstep (se 2 (by rfl) ⟨154608, by rfl⟩ : syracuseStep 412289 = 309217) B309217
theorem B6967781 : Blo 119786 6967781 := bstep (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) B1306459
theorem B2217071 : Blo 119786 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B351287 : Blo 119786 351287 := bstep (se 1 (by rfl) ⟨263465, by rfl⟩ : syracuseStep 351287 = 526931) B526931
theorem B2317673 : Blo 119786 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B228071 : Blo 119786 228071 := bstep (se 1 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 228071 = 342107) B342107
theorem B588799 : Blo 119786 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B621593 : Blo 119786 621593 := bstep (se 2 (by rfl) ⟨233097, by rfl⟩ : syracuseStep 621593 = 466195) B466195
theorem B1114003 : Blo 119786 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B1478047 : Blo 119786 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B234191 : Blo 119786 234191 := bstep (se 1 (by rfl) ⟨175643, by rfl⟩ : syracuseStep 234191 = 351287) B351287
theorem B1545115 : Blo 119786 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B269567 : Blo 119786 269567 := bstep (se 1 (by rfl) ⟨202175, by rfl⟩ : syracuseStep 269567 = 404351) B404351
theorem B271079 : Blo 119786 271079 := bstep (se 1 (by rfl) ⟨203309, by rfl⟩ : syracuseStep 271079 = 406619) B406619
theorem B5941349 : Blo 119786 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B274859 : Blo 119786 274859 := bstep (se 1 (by rfl) ⟨206144, by rfl⟩ : syracuseStep 274859 = 412289) B412289
theorem B307871 : Blo 119786 307871 := bstep (se 1 (by rfl) ⟨230903, by rfl⟩ : syracuseStep 307871 = 461807) B461807
theorem B178087 : Blo 119786 178087 := bstep (se 1 (by rfl) ⟨133565, by rfl⟩ : syracuseStep 178087 = 267131) B267131
theorem B1491911 : Blo 119786 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B1033631 : Blo 119786 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B152047 : Blo 119786 152047 := bstep (se 1 (by rfl) ⟨114035, by rfl⟩ : syracuseStep 152047 = 228071) B228071
theorem B414395 : Blo 119786 414395 := bstep (se 1 (by rfl) ⟨310796, by rfl⟩ : syracuseStep 414395 = 621593) B621593
theorem B121887 : Blo 119786 121887 := bstep (se 1 (by rfl) ⟨91415, by rfl⟩ : syracuseStep 121887 = 182831) B182831
theorem B4645187 : Blo 119786 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B1009529 : Blo 119786 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B785065 : Blo 119786 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B228511 : Blo 119786 228511 := bstep (se 1 (by rfl) ⟨171383, by rfl⟩ : syracuseStep 228511 = 342767) B342767
theorem B689087 : Blo 119786 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B624509 : Blo 119786 624509 := bstep (se 3 (by rfl) ⟨117095, by rfl⟩ : syracuseStep 624509 = 234191) B234191
theorem B1970729 : Blo 119786 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B202729 : Blo 119786 202729 := bstep (se 2 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 202729 = 152047) B152047
theorem B237449 : Blo 119786 237449 := bstep (se 2 (by rfl) ⟨89043, by rfl⟩ : syracuseStep 237449 = 178087) B178087
theorem B205247 : Blo 119786 205247 := bstep (se 1 (by rfl) ⟨153935, by rfl⟩ : syracuseStep 205247 = 307871) B307871
theorem B304681 : Blo 119786 304681 := bstep (se 2 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 304681 = 228511) B228511
theorem B994607 : Blo 119786 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B276263 : Blo 119786 276263 := bstep (se 1 (by rfl) ⟨207197, by rfl⟩ : syracuseStep 276263 = 414395) B414395
theorem B179711 : Blo 119786 179711 := bstep (se 1 (by rfl) ⟨134783, by rfl⟩ : syracuseStep 179711 = 269567) B269567
theorem B3096791 : Blo 119786 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B180719 : Blo 119786 180719 := bstep (se 1 (by rfl) ⟨135539, by rfl⟩ : syracuseStep 180719 = 271079) B271079
theorem B673019 : Blo 119786 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B183239 : Blo 119786 183239 := bstep (se 1 (by rfl) ⟨137429, by rfl⟩ : syracuseStep 183239 = 274859) B274859
theorem B2060153 : Blo 119786 2060153 := bstep (se 2 (by rfl) ⟨772557, by rfl⟩ : syracuseStep 2060153 = 1545115) B1545115
theorem B3960899 : Blo 119786 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B1046753 : Blo 119786 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B2064527 : Blo 119786 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B459391 : Blo 119786 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B1313819 : Blo 119786 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B136831 : Blo 119786 136831 := bstep (se 1 (by rfl) ⟨102623, by rfl⟩ : syracuseStep 136831 = 205247) B205247
theorem B663071 : Blo 119786 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B270305 : Blo 119786 270305 := bstep (se 2 (by rfl) ⟨101364, by rfl⟩ : syracuseStep 270305 = 202729) B202729
theorem B697835 : Blo 119786 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B633197 : Blo 119786 633197 := bstep (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) B237449
theorem B406241 : Blo 119786 406241 := bstep (se 2 (by rfl) ⟨152340, by rfl⟩ : syracuseStep 406241 = 304681) B304681
theorem B2640599 : Blo 119786 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B184175 : Blo 119786 184175 := bstep (se 1 (by rfl) ⟨138131, by rfl⟩ : syracuseStep 184175 = 276263) B276263
theorem B119807 : Blo 119786 119807 := bstep (se 1 (by rfl) ⟨89855, by rfl⟩ : syracuseStep 119807 = 179711) B179711
theorem B120479 : Blo 119786 120479 := bstep (se 1 (by rfl) ⟨90359, by rfl⟩ : syracuseStep 120479 = 180719) B180719
theorem B448679 : Blo 119786 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B416339 : Blo 119786 416339 := bstep (se 1 (by rfl) ⟨312254, by rfl⟩ : syracuseStep 416339 = 624509) B624509
theorem B122159 : Blo 119786 122159 := bstep (se 1 (by rfl) ⟨91619, by rfl⟩ : syracuseStep 122159 = 183239) B183239
theorem B1373435 : Blo 119786 1373435 := bstep (se 1 (by rfl) ⟨1030076, by rfl⟩ : syracuseStep 1373435 = 2060153) B2060153
theorem B1376351 : Blo 119786 1376351 := bstep (se 1 (by rfl) ⟨1032263, by rfl⟩ : syracuseStep 1376351 = 2064527) B2064527
theorem B299119 : Blo 119786 299119 := bstep (se 1 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 299119 = 448679) B448679
theorem B465223 : Blo 119786 465223 := bstep (se 1 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 465223 = 697835) B697835
theorem B270827 : Blo 119786 270827 := bstep (se 1 (by rfl) ⟨203120, by rfl⟩ : syracuseStep 270827 = 406241) B406241
theorem B277559 : Blo 119786 277559 := bstep (se 1 (by rfl) ⟨208169, by rfl⟩ : syracuseStep 277559 = 416339) B416339
theorem B180203 : Blo 119786 180203 := bstep (se 1 (by rfl) ⟨135152, by rfl⟩ : syracuseStep 180203 = 270305) B270305
theorem B182441 : Blo 119786 182441 := bstep (se 2 (by rfl) ⟨68415, by rfl⟩ : syracuseStep 182441 = 136831) B136831
theorem B612521 : Blo 119786 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B1760399 : Blo 119786 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B875879 : Blo 119786 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B122783 : Blo 119786 122783 := bstep (se 1 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 122783 = 184175) B184175
theorem B422131 : Blo 119786 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B915623 : Blo 119786 915623 := bstep (se 1 (by rfl) ⟨686717, by rfl⟩ : syracuseStep 915623 = 1373435) B1373435
theorem B1768189 : Blo 119786 1768189 := bstep (se 3 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 1768189 = 663071) B663071
theorem B917567 : Blo 119786 917567 := bstep (se 1 (by rfl) ⟨688175, by rfl⟩ : syracuseStep 917567 = 1376351) B1376351
theorem B398825 : Blo 119786 398825 := bstep (se 2 (by rfl) ⟨149559, by rfl⟩ : syracuseStep 398825 = 299119) B299119
theorem B562841 : Blo 119786 562841 := bstep (se 2 (by rfl) ⟨211065, by rfl⟩ : syracuseStep 562841 = 422131) B422131
theorem B408347 : Blo 119786 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B180551 : Blo 119786 180551 := bstep (se 1 (by rfl) ⟨135413, by rfl⟩ : syracuseStep 180551 = 270827) B270827
theorem B610415 : Blo 119786 610415 := bstep (se 1 (by rfl) ⟨457811, by rfl⟩ : syracuseStep 610415 = 915623) B915623
theorem B185039 : Blo 119786 185039 := bstep (se 1 (by rfl) ⟨138779, by rfl⟩ : syracuseStep 185039 = 277559) B277559
theorem B120135 : Blo 119786 120135 := bstep (se 1 (by rfl) ⟨90101, by rfl⟩ : syracuseStep 120135 = 180203) B180203
theorem B121627 : Blo 119786 121627 := bstep (se 1 (by rfl) ⟨91220, by rfl⟩ : syracuseStep 121627 = 182441) B182441
theorem B1173599 : Blo 119786 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B583919 : Blo 119786 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B620297 : Blo 119786 620297 := bstep (se 2 (by rfl) ⟨232611, by rfl⟩ : syracuseStep 620297 = 465223) B465223
theorem B2357585 : Blo 119786 2357585 := bstep (se 2 (by rfl) ⟨884094, by rfl⟩ : syracuseStep 2357585 = 1768189) B1768189
theorem B265883 : Blo 119786 265883 := bstep (se 1 (by rfl) ⟨199412, by rfl⟩ : syracuseStep 265883 = 398825) B398825
theorem B272231 : Blo 119786 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B406943 : Blo 119786 406943 := bstep (se 1 (by rfl) ⟨305207, by rfl⟩ : syracuseStep 406943 = 610415) B610415
theorem B375227 : Blo 119786 375227 := bstep (se 1 (by rfl) ⟨281420, by rfl⟩ : syracuseStep 375227 = 562841) B562841
theorem B413531 : Blo 119786 413531 := bstep (se 1 (by rfl) ⟨310148, by rfl⟩ : syracuseStep 413531 = 620297) B620297
theorem B611711 : Blo 119786 611711 := bstep (se 1 (by rfl) ⟨458783, by rfl⟩ : syracuseStep 611711 = 917567) B917567
theorem B120367 : Blo 119786 120367 := bstep (se 1 (by rfl) ⟨90275, by rfl⟩ : syracuseStep 120367 = 180551) B180551
theorem B123359 : Blo 119786 123359 := bstep (se 1 (by rfl) ⟨92519, by rfl⟩ : syracuseStep 123359 = 185039) B185039
theorem B782399 : Blo 119786 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B389279 : Blo 119786 389279 := bstep (se 1 (by rfl) ⟨291959, by rfl⟩ : syracuseStep 389279 = 583919) B583919
theorem B1571723 : Blo 119786 1571723 := bstep (se 1 (by rfl) ⟨1178792, by rfl⟩ : syracuseStep 1571723 = 2357585) B2357585
theorem B271295 : Blo 119786 271295 := bstep (se 1 (by rfl) ⟨203471, by rfl⟩ : syracuseStep 271295 = 406943) B406943
theorem B275687 : Blo 119786 275687 := bstep (se 1 (by rfl) ⟨206765, by rfl⟩ : syracuseStep 275687 = 413531) B413531
theorem B407807 : Blo 119786 407807 := bstep (se 1 (by rfl) ⟨305855, by rfl⟩ : syracuseStep 407807 = 611711) B611711
theorem B181487 : Blo 119786 181487 := bstep (se 1 (by rfl) ⟨136115, by rfl⟩ : syracuseStep 181487 = 272231) B272231
theorem B250151 : Blo 119786 250151 := bstep (se 1 (by rfl) ⟨187613, by rfl⟩ : syracuseStep 250151 = 375227) B375227
theorem B709021 : Blo 119786 709021 := bstep (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) B265883
theorem B2086397 : Blo 119786 2086397 := bstep (se 3 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 2086397 = 782399) B782399
theorem B259519 : Blo 119786 259519 := bstep (se 1 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 259519 = 389279) B389279
theorem B1047815 : Blo 119786 1047815 := bstep (se 1 (by rfl) ⟨785861, by rfl⟩ : syracuseStep 1047815 = 1571723) B1571723
theorem B271871 : Blo 119786 271871 := bstep (se 1 (by rfl) ⟨203903, by rfl⟩ : syracuseStep 271871 = 407807) B407807
theorem B698543 : Blo 119786 698543 := bstep (se 1 (by rfl) ⟨523907, by rfl⟩ : syracuseStep 698543 = 1047815) B1047815
theorem B2668277 : Blo 119786 2668277 := bstep (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) B250151
theorem B1390931 : Blo 119786 1390931 := bstep (se 1 (by rfl) ⟨1043198, by rfl⟩ : syracuseStep 1390931 = 2086397) B2086397
theorem B180863 : Blo 119786 180863 := bstep (se 1 (by rfl) ⟨135647, by rfl⟩ : syracuseStep 180863 = 271295) B271295
theorem B346025 : Blo 119786 346025 := bstep (se 2 (by rfl) ⟨129759, by rfl⟩ : syracuseStep 346025 = 259519) B259519
theorem B183791 : Blo 119786 183791 := bstep (se 1 (by rfl) ⟨137843, by rfl⟩ : syracuseStep 183791 = 275687) B275687
theorem B120991 : Blo 119786 120991 := bstep (se 1 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 120991 = 181487) B181487
theorem B945361 : Blo 119786 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B230683 : Blo 119786 230683 := bstep (se 1 (by rfl) ⟨173012, by rfl⟩ : syracuseStep 230683 = 346025) B346025
theorem B465695 : Blo 119786 465695 := bstep (se 1 (by rfl) ⟨349271, by rfl⟩ : syracuseStep 465695 = 698543) B698543
theorem B1778851 : Blo 119786 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B927287 : Blo 119786 927287 := bstep (se 1 (by rfl) ⟨695465, by rfl⟩ : syracuseStep 927287 = 1390931) B1390931
theorem B181247 : Blo 119786 181247 := bstep (se 1 (by rfl) ⟨135935, by rfl⟩ : syracuseStep 181247 = 271871) B271871
theorem B120575 : Blo 119786 120575 := bstep (se 1 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 120575 = 180863) B180863
theorem B122527 : Blo 119786 122527 := bstep (se 1 (by rfl) ⟨91895, by rfl⟩ : syracuseStep 122527 = 183791) B183791
theorem B5041925 : Blo 119786 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B2371801 : Blo 119786 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B307577 : Blo 119786 307577 := bstep (se 2 (by rfl) ⟨115341, by rfl⟩ : syracuseStep 307577 = 230683) B230683
theorem B310463 : Blo 119786 310463 := bstep (se 1 (by rfl) ⟨232847, by rfl⟩ : syracuseStep 310463 = 465695) B465695
theorem B3361283 : Blo 119786 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B120831 : Blo 119786 120831 := bstep (se 1 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 120831 = 181247) B181247
theorem B618191 : Blo 119786 618191 := bstep (se 1 (by rfl) ⟨463643, by rfl⟩ : syracuseStep 618191 = 927287) B927287
theorem B205051 : Blo 119786 205051 := bstep (se 1 (by rfl) ⟨153788, by rfl⟩ : syracuseStep 205051 = 307577) B307577
theorem B206975 : Blo 119786 206975 := bstep (se 1 (by rfl) ⟨155231, by rfl⟩ : syracuseStep 206975 = 310463) B310463
theorem B2240855 : Blo 119786 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B3162401 : Blo 119786 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B412127 : Blo 119786 412127 := bstep (se 1 (by rfl) ⟨309095, by rfl⟩ : syracuseStep 412127 = 618191) B618191
theorem B137983 : Blo 119786 137983 := bstep (se 1 (by rfl) ⟨103487, by rfl⟩ : syracuseStep 137983 = 206975) B206975
theorem B2108267 : Blo 119786 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B273401 : Blo 119786 273401 := bstep (se 2 (by rfl) ⟨102525, by rfl⟩ : syracuseStep 273401 = 205051) B205051
theorem B274751 : Blo 119786 274751 := bstep (se 1 (by rfl) ⟨206063, by rfl⟩ : syracuseStep 274751 = 412127) B412127
theorem B1493903 : Blo 119786 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B995935 : Blo 119786 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B182267 : Blo 119786 182267 := bstep (se 1 (by rfl) ⟨136700, by rfl⟩ : syracuseStep 182267 = 273401) B273401
theorem B183167 : Blo 119786 183167 := bstep (se 1 (by rfl) ⟨137375, by rfl⟩ : syracuseStep 183167 = 274751) B274751
theorem B183977 : Blo 119786 183977 := bstep (se 2 (by rfl) ⟨68991, by rfl⟩ : syracuseStep 183977 = 137983) B137983
theorem B1405511 : Blo 119786 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B1327913 : Blo 119786 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B937007 : Blo 119786 937007 := bstep (se 1 (by rfl) ⟨702755, by rfl⟩ : syracuseStep 937007 = 1405511) B1405511
theorem B121511 : Blo 119786 121511 := bstep (se 1 (by rfl) ⟨91133, by rfl⟩ : syracuseStep 121511 = 182267) B182267
theorem B122111 : Blo 119786 122111 := bstep (se 1 (by rfl) ⟨91583, by rfl⟩ : syracuseStep 122111 = 183167) B183167
theorem B122651 : Blo 119786 122651 := bstep (se 1 (by rfl) ⟨91988, by rfl⟩ : syracuseStep 122651 = 183977) B183977
theorem B885275 : Blo 119786 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B624671 : Blo 119786 624671 := bstep (se 1 (by rfl) ⟨468503, by rfl⟩ : syracuseStep 624671 = 937007) B937007
theorem B590183 : Blo 119786 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B416447 : Blo 119786 416447 := bstep (se 1 (by rfl) ⟨312335, by rfl⟩ : syracuseStep 416447 = 624671) B624671
theorem B393455 : Blo 119786 393455 := bstep (se 1 (by rfl) ⟨295091, by rfl⟩ : syracuseStep 393455 = 590183) B590183
theorem B277631 : Blo 119786 277631 := bstep (se 1 (by rfl) ⟨208223, by rfl⟩ : syracuseStep 277631 = 416447) B416447
theorem B1049213 : Blo 119786 1049213 := bstep (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) B393455
theorem B185087 : Blo 119786 185087 := bstep (se 1 (by rfl) ⟨138815, by rfl⟩ : syracuseStep 185087 = 277631) B277631
theorem B699475 : Blo 119786 699475 := bstep (se 1 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 699475 = 1049213) B1049213
theorem B123391 : Blo 119786 123391 := bstep (se 1 (by rfl) ⟨92543, by rfl⟩ : syracuseStep 123391 = 185087) B185087
theorem B932633 : Blo 119786 932633 := bstep (se 2 (by rfl) ⟨349737, by rfl⟩ : syracuseStep 932633 = 699475) B699475
theorem B621755 : Blo 119786 621755 := bstep (se 1 (by rfl) ⟨466316, by rfl⟩ : syracuseStep 621755 = 932633) B932633
theorem B414503 : Blo 119786 414503 := bstep (se 1 (by rfl) ⟨310877, by rfl⟩ : syracuseStep 414503 = 621755) B621755
theorem B276335 : Blo 119786 276335 := bstep (se 1 (by rfl) ⟨207251, by rfl⟩ : syracuseStep 276335 = 414503) B414503
theorem B184223 : Blo 119786 184223 := bstep (se 1 (by rfl) ⟨138167, by rfl⟩ : syracuseStep 184223 = 276335) B276335
theorem B122815 : Blo 119786 122815 := bstep (se 1 (by rfl) ⟨92111, by rfl⟩ : syracuseStep 122815 = 184223) B184223

theorem C0 (j : ℕ) (h1 : 29946 ≤ j) (h2 : j ≤ 30645) : Blo 119786 (4 * j + 3) := by
  interval_cases j
  · exact B119787
  · exact B119791
  · exact B119795
  · exact B119799
  · exact B119803
  · exact B119807
  · exact B119811
  · exact B119815
  · exact B119819
  · exact B119823
  · exact B119827
  · exact B119831
  · exact B119835
  · exact B119839
  · exact B119843
  · exact B119847
  · exact B119851
  · exact B119855
  · exact B119859
  · exact B119863
  · exact B119867
  · exact B119871
  · exact B119875
  · exact B119879
  · exact B119883
  · exact B119887
  · exact B119891
  · exact B119895
  · exact B119899
  · exact B119903
  · exact B119907
  · exact B119911
  · exact B119915
  · exact B119919
  · exact B119923
  · exact B119927
  · exact B119931
  · exact B119935
  · exact B119939
  · exact B119943
  · exact B119947
  · exact B119951
  · exact B119955
  · exact B119959
  · exact B119963
  · exact B119967
  · exact B119971
  · exact B119975
  · exact B119979
  · exact B119983
  · exact B119987
  · exact B119991
  · exact B119995
  · exact B119999
  · exact B120003
  · exact B120007
  · exact B120011
  · exact B120015
  · exact B120019
  · exact B120023
  · exact B120027
  · exact B120031
  · exact B120035
  · exact B120039
  · exact B120043
  · exact B120047
  · exact B120051
  · exact B120055
  · exact B120059
  · exact B120063
  · exact B120067
  · exact B120071
  · exact B120075
  · exact B120079
  · exact B120083
  · exact B120087
  · exact B120091
  · exact B120095
  · exact B120099
  · exact B120103
  · exact B120107
  · exact B120111
  · exact B120115
  · exact B120119
  · exact B120123
  · exact B120127
  · exact B120131
  · exact B120135
  · exact B120139
  · exact B120143
  · exact B120147
  · exact B120151
  · exact B120155
  · exact B120159
  · exact B120163
  · exact B120167
  · exact B120171
  · exact B120175
  · exact B120179
  · exact B120183
  · exact B120187
  · exact B120191
  · exact B120195
  · exact B120199
  · exact B120203
  · exact B120207
  · exact B120211
  · exact B120215
  · exact B120219
  · exact B120223
  · exact B120227
  · exact B120231
  · exact B120235
  · exact B120239
  · exact B120243
  · exact B120247
  · exact B120251
  · exact B120255
  · exact B120259
  · exact B120263
  · exact B120267
  · exact B120271
  · exact B120275
  · exact B120279
  · exact B120283
  · exact B120287
  · exact B120291
  · exact B120295
  · exact B120299
  · exact B120303
  · exact B120307
  · exact B120311
  · exact B120315
  · exact B120319
  · exact B120323
  · exact B120327
  · exact B120331
  · exact B120335
  · exact B120339
  · exact B120343
  · exact B120347
  · exact B120351
  · exact B120355
  · exact B120359
  · exact B120363
  · exact B120367
  · exact B120371
  · exact B120375
  · exact B120379
  · exact B120383
  · exact B120387
  · exact B120391
  · exact B120395
  · exact B120399
  · exact B120403
  · exact B120407
  · exact B120411
  · exact B120415
  · exact B120419
  · exact B120423
  · exact B120427
  · exact B120431
  · exact B120435
  · exact B120439
  · exact B120443
  · exact B120447
  · exact B120451
  · exact B120455
  · exact B120459
  · exact B120463
  · exact B120467
  · exact B120471
  · exact B120475
  · exact B120479
  · exact B120483
  · exact B120487
  · exact B120491
  · exact B120495
  · exact B120499
  · exact B120503
  · exact B120507
  · exact B120511
  · exact B120515
  · exact B120519
  · exact B120523
  · exact B120527
  · exact B120531
  · exact B120535
  · exact B120539
  · exact B120543
  · exact B120547
  · exact B120551
  · exact B120555
  · exact B120559
  · exact B120563
  · exact B120567
  · exact B120571
  · exact B120575
  · exact B120579
  · exact B120583
  · exact B120587
  · exact B120591
  · exact B120595
  · exact B120599
  · exact B120603
  · exact B120607
  · exact B120611
  · exact B120615
  · exact B120619
  · exact B120623
  · exact B120627
  · exact B120631
  · exact B120635
  · exact B120639
  · exact B120643
  · exact B120647
  · exact B120651
  · exact B120655
  · exact B120659
  · exact B120663
  · exact B120667
  · exact B120671
  · exact B120675
  · exact B120679
  · exact B120683
  · exact B120687
  · exact B120691
  · exact B120695
  · exact B120699
  · exact B120703
  · exact B120707
  · exact B120711
  · exact B120715
  · exact B120719
  · exact B120723
  · exact B120727
  · exact B120731
  · exact B120735
  · exact B120739
  · exact B120743
  · exact B120747
  · exact B120751
  · exact B120755
  · exact B120759
  · exact B120763
  · exact B120767
  · exact B120771
  · exact B120775
  · exact B120779
  · exact B120783
  · exact B120787
  · exact B120791
  · exact B120795
  · exact B120799
  · exact B120803
  · exact B120807
  · exact B120811
  · exact B120815
  · exact B120819
  · exact B120823
  · exact B120827
  · exact B120831
  · exact B120835
  · exact B120839
  · exact B120843
  · exact B120847
  · exact B120851
  · exact B120855
  · exact B120859
  · exact B120863
  · exact B120867
  · exact B120871
  · exact B120875
  · exact B120879
  · exact B120883
  · exact B120887
  · exact B120891
  · exact B120895
  · exact B120899
  · exact B120903
  · exact B120907
  · exact B120911
  · exact B120915
  · exact B120919
  · exact B120923
  · exact B120927
  · exact B120931
  · exact B120935
  · exact B120939
  · exact B120943
  · exact B120947
  · exact B120951
  · exact B120955
  · exact B120959
  · exact B120963
  · exact B120967
  · exact B120971
  · exact B120975
  · exact B120979
  · exact B120983
  · exact B120987
  · exact B120991
  · exact B120995
  · exact B120999
  · exact B121003
  · exact B121007
  · exact B121011
  · exact B121015
  · exact B121019
  · exact B121023
  · exact B121027
  · exact B121031
  · exact B121035
  · exact B121039
  · exact B121043
  · exact B121047
  · exact B121051
  · exact B121055
  · exact B121059
  · exact B121063
  · exact B121067
  · exact B121071
  · exact B121075
  · exact B121079
  · exact B121083
  · exact B121087
  · exact B121091
  · exact B121095
  · exact B121099
  · exact B121103
  · exact B121107
  · exact B121111
  · exact B121115
  · exact B121119
  · exact B121123
  · exact B121127
  · exact B121131
  · exact B121135
  · exact B121139
  · exact B121143
  · exact B121147
  · exact B121151
  · exact B121155
  · exact B121159
  · exact B121163
  · exact B121167
  · exact B121171
  · exact B121175
  · exact B121179
  · exact B121183
  · exact B121187
  · exact B121191
  · exact B121195
  · exact B121199
  · exact B121203
  · exact B121207
  · exact B121211
  · exact B121215
  · exact B121219
  · exact B121223
  · exact B121227
  · exact B121231
  · exact B121235
  · exact B121239
  · exact B121243
  · exact B121247
  · exact B121251
  · exact B121255
  · exact B121259
  · exact B121263
  · exact B121267
  · exact B121271
  · exact B121275
  · exact B121279
  · exact B121283
  · exact B121287
  · exact B121291
  · exact B121295
  · exact B121299
  · exact B121303
  · exact B121307
  · exact B121311
  · exact B121315
  · exact B121319
  · exact B121323
  · exact B121327
  · exact B121331
  · exact B121335
  · exact B121339
  · exact B121343
  · exact B121347
  · exact B121351
  · exact B121355
  · exact B121359
  · exact B121363
  · exact B121367
  · exact B121371
  · exact B121375
  · exact B121379
  · exact B121383
  · exact B121387
  · exact B121391
  · exact B121395
  · exact B121399
  · exact B121403
  · exact B121407
  · exact B121411
  · exact B121415
  · exact B121419
  · exact B121423
  · exact B121427
  · exact B121431
  · exact B121435
  · exact B121439
  · exact B121443
  · exact B121447
  · exact B121451
  · exact B121455
  · exact B121459
  · exact B121463
  · exact B121467
  · exact B121471
  · exact B121475
  · exact B121479
  · exact B121483
  · exact B121487
  · exact B121491
  · exact B121495
  · exact B121499
  · exact B121503
  · exact B121507
  · exact B121511
  · exact B121515
  · exact B121519
  · exact B121523
  · exact B121527
  · exact B121531
  · exact B121535
  · exact B121539
  · exact B121543
  · exact B121547
  · exact B121551
  · exact B121555
  · exact B121559
  · exact B121563
  · exact B121567
  · exact B121571
  · exact B121575
  · exact B121579
  · exact B121583
  · exact B121587
  · exact B121591
  · exact B121595
  · exact B121599
  · exact B121603
  · exact B121607
  · exact B121611
  · exact B121615
  · exact B121619
  · exact B121623
  · exact B121627
  · exact B121631
  · exact B121635
  · exact B121639
  · exact B121643
  · exact B121647
  · exact B121651
  · exact B121655
  · exact B121659
  · exact B121663
  · exact B121667
  · exact B121671
  · exact B121675
  · exact B121679
  · exact B121683
  · exact B121687
  · exact B121691
  · exact B121695
  · exact B121699
  · exact B121703
  · exact B121707
  · exact B121711
  · exact B121715
  · exact B121719
  · exact B121723
  · exact B121727
  · exact B121731
  · exact B121735
  · exact B121739
  · exact B121743
  · exact B121747
  · exact B121751
  · exact B121755
  · exact B121759
  · exact B121763
  · exact B121767
  · exact B121771
  · exact B121775
  · exact B121779
  · exact B121783
  · exact B121787
  · exact B121791
  · exact B121795
  · exact B121799
  · exact B121803
  · exact B121807
  · exact B121811
  · exact B121815
  · exact B121819
  · exact B121823
  · exact B121827
  · exact B121831
  · exact B121835
  · exact B121839
  · exact B121843
  · exact B121847
  · exact B121851
  · exact B121855
  · exact B121859
  · exact B121863
  · exact B121867
  · exact B121871
  · exact B121875
  · exact B121879
  · exact B121883
  · exact B121887
  · exact B121891
  · exact B121895
  · exact B121899
  · exact B121903
  · exact B121907
  · exact B121911
  · exact B121915
  · exact B121919
  · exact B121923
  · exact B121927
  · exact B121931
  · exact B121935
  · exact B121939
  · exact B121943
  · exact B121947
  · exact B121951
  · exact B121955
  · exact B121959
  · exact B121963
  · exact B121967
  · exact B121971
  · exact B121975
  · exact B121979
  · exact B121983
  · exact B121987
  · exact B121991
  · exact B121995
  · exact B121999
  · exact B122003
  · exact B122007
  · exact B122011
  · exact B122015
  · exact B122019
  · exact B122023
  · exact B122027
  · exact B122031
  · exact B122035
  · exact B122039
  · exact B122043
  · exact B122047
  · exact B122051
  · exact B122055
  · exact B122059
  · exact B122063
  · exact B122067
  · exact B122071
  · exact B122075
  · exact B122079
  · exact B122083
  · exact B122087
  · exact B122091
  · exact B122095
  · exact B122099
  · exact B122103
  · exact B122107
  · exact B122111
  · exact B122115
  · exact B122119
  · exact B122123
  · exact B122127
  · exact B122131
  · exact B122135
  · exact B122139
  · exact B122143
  · exact B122147
  · exact B122151
  · exact B122155
  · exact B122159
  · exact B122163
  · exact B122167
  · exact B122171
  · exact B122175
  · exact B122179
  · exact B122183
  · exact B122187
  · exact B122191
  · exact B122195
  · exact B122199
  · exact B122203
  · exact B122207
  · exact B122211
  · exact B122215
  · exact B122219
  · exact B122223
  · exact B122227
  · exact B122231
  · exact B122235
  · exact B122239
  · exact B122243
  · exact B122247
  · exact B122251
  · exact B122255
  · exact B122259
  · exact B122263
  · exact B122267
  · exact B122271
  · exact B122275
  · exact B122279
  · exact B122283
  · exact B122287
  · exact B122291
  · exact B122295
  · exact B122299
  · exact B122303
  · exact B122307
  · exact B122311
  · exact B122315
  · exact B122319
  · exact B122323
  · exact B122327
  · exact B122331
  · exact B122335
  · exact B122339
  · exact B122343
  · exact B122347
  · exact B122351
  · exact B122355
  · exact B122359
  · exact B122363
  · exact B122367
  · exact B122371
  · exact B122375
  · exact B122379
  · exact B122383
  · exact B122387
  · exact B122391
  · exact B122395
  · exact B122399
  · exact B122403
  · exact B122407
  · exact B122411
  · exact B122415
  · exact B122419
  · exact B122423
  · exact B122427
  · exact B122431
  · exact B122435
  · exact B122439
  · exact B122443
  · exact B122447
  · exact B122451
  · exact B122455
  · exact B122459
  · exact B122463
  · exact B122467
  · exact B122471
  · exact B122475
  · exact B122479
  · exact B122483
  · exact B122487
  · exact B122491
  · exact B122495
  · exact B122499
  · exact B122503
  · exact B122507
  · exact B122511
  · exact B122515
  · exact B122519
  · exact B122523
  · exact B122527
  · exact B122531
  · exact B122535
  · exact B122539
  · exact B122543
  · exact B122547
  · exact B122551
  · exact B122555
  · exact B122559
  · exact B122563
  · exact B122567
  · exact B122571
  · exact B122575
  · exact B122579
  · exact B122583

theorem C1 (j : ℕ) (h1 : 30646 ≤ j) (h2 : j ≤ 30945) : Blo 119786 (4 * j + 3) := by
  interval_cases j
  · exact B122587
  · exact B122591
  · exact B122595
  · exact B122599
  · exact B122603
  · exact B122607
  · exact B122611
  · exact B122615
  · exact B122619
  · exact B122623
  · exact B122627
  · exact B122631
  · exact B122635
  · exact B122639
  · exact B122643
  · exact B122647
  · exact B122651
  · exact B122655
  · exact B122659
  · exact B122663
  · exact B122667
  · exact B122671
  · exact B122675
  · exact B122679
  · exact B122683
  · exact B122687
  · exact B122691
  · exact B122695
  · exact B122699
  · exact B122703
  · exact B122707
  · exact B122711
  · exact B122715
  · exact B122719
  · exact B122723
  · exact B122727
  · exact B122731
  · exact B122735
  · exact B122739
  · exact B122743
  · exact B122747
  · exact B122751
  · exact B122755
  · exact B122759
  · exact B122763
  · exact B122767
  · exact B122771
  · exact B122775
  · exact B122779
  · exact B122783
  · exact B122787
  · exact B122791
  · exact B122795
  · exact B122799
  · exact B122803
  · exact B122807
  · exact B122811
  · exact B122815
  · exact B122819
  · exact B122823
  · exact B122827
  · exact B122831
  · exact B122835
  · exact B122839
  · exact B122843
  · exact B122847
  · exact B122851
  · exact B122855
  · exact B122859
  · exact B122863
  · exact B122867
  · exact B122871
  · exact B122875
  · exact B122879
  · exact B122883
  · exact B122887
  · exact B122891
  · exact B122895
  · exact B122899
  · exact B122903
  · exact B122907
  · exact B122911
  · exact B122915
  · exact B122919
  · exact B122923
  · exact B122927
  · exact B122931
  · exact B122935
  · exact B122939
  · exact B122943
  · exact B122947
  · exact B122951
  · exact B122955
  · exact B122959
  · exact B122963
  · exact B122967
  · exact B122971
  · exact B122975
  · exact B122979
  · exact B122983
  · exact B122987
  · exact B122991
  · exact B122995
  · exact B122999
  · exact B123003
  · exact B123007
  · exact B123011
  · exact B123015
  · exact B123019
  · exact B123023
  · exact B123027
  · exact B123031
  · exact B123035
  · exact B123039
  · exact B123043
  · exact B123047
  · exact B123051
  · exact B123055
  · exact B123059
  · exact B123063
  · exact B123067
  · exact B123071
  · exact B123075
  · exact B123079
  · exact B123083
  · exact B123087
  · exact B123091
  · exact B123095
  · exact B123099
  · exact B123103
  · exact B123107
  · exact B123111
  · exact B123115
  · exact B123119
  · exact B123123
  · exact B123127
  · exact B123131
  · exact B123135
  · exact B123139
  · exact B123143
  · exact B123147
  · exact B123151
  · exact B123155
  · exact B123159
  · exact B123163
  · exact B123167
  · exact B123171
  · exact B123175
  · exact B123179
  · exact B123183
  · exact B123187
  · exact B123191
  · exact B123195
  · exact B123199
  · exact B123203
  · exact B123207
  · exact B123211
  · exact B123215
  · exact B123219
  · exact B123223
  · exact B123227
  · exact B123231
  · exact B123235
  · exact B123239
  · exact B123243
  · exact B123247
  · exact B123251
  · exact B123255
  · exact B123259
  · exact B123263
  · exact B123267
  · exact B123271
  · exact B123275
  · exact B123279
  · exact B123283
  · exact B123287
  · exact B123291
  · exact B123295
  · exact B123299
  · exact B123303
  · exact B123307
  · exact B123311
  · exact B123315
  · exact B123319
  · exact B123323
  · exact B123327
  · exact B123331
  · exact B123335
  · exact B123339
  · exact B123343
  · exact B123347
  · exact B123351
  · exact B123355
  · exact B123359
  · exact B123363
  · exact B123367
  · exact B123371
  · exact B123375
  · exact B123379
  · exact B123383
  · exact B123387
  · exact B123391
  · exact B123395
  · exact B123399
  · exact B123403
  · exact B123407
  · exact B123411
  · exact B123415
  · exact B123419
  · exact B123423
  · exact B123427
  · exact B123431
  · exact B123435
  · exact B123439
  · exact B123443
  · exact B123447
  · exact B123451
  · exact B123455
  · exact B123459
  · exact B123463
  · exact B123467
  · exact B123471
  · exact B123475
  · exact B123479
  · exact B123483
  · exact B123487
  · exact B123491
  · exact B123495
  · exact B123499
  · exact B123503
  · exact B123507
  · exact B123511
  · exact B123515
  · exact B123519
  · exact B123523
  · exact B123527
  · exact B123531
  · exact B123535
  · exact B123539
  · exact B123543
  · exact B123547
  · exact B123551
  · exact B123555
  · exact B123559
  · exact B123563
  · exact B123567
  · exact B123571
  · exact B123575
  · exact B123579
  · exact B123583
  · exact B123587
  · exact B123591
  · exact B123595
  · exact B123599
  · exact B123603
  · exact B123607
  · exact B123611
  · exact B123615
  · exact B123619
  · exact B123623
  · exact B123627
  · exact B123631
  · exact B123635
  · exact B123639
  · exact B123643
  · exact B123647
  · exact B123651
  · exact B123655
  · exact B123659
  · exact B123663
  · exact B123667
  · exact B123671
  · exact B123675
  · exact B123679
  · exact B123683
  · exact B123687
  · exact B123691
  · exact B123695
  · exact B123699
  · exact B123703
  · exact B123707
  · exact B123711
  · exact B123715
  · exact B123719
  · exact B123723
  · exact B123727
  · exact B123731
  · exact B123735
  · exact B123739
  · exact B123743
  · exact B123747
  · exact B123751
  · exact B123755
  · exact B123759
  · exact B123763
  · exact B123767
  · exact B123771
  · exact B123775
  · exact B123779
  · exact B123783

theorem solution (m : ℕ) (hlo : 119786 ≤ m) (hhi : m ≤ 123786) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 29946 ≤ j := by omega
    have hj2 : j ≤ 30945 := by omega
    have hb : Blo 119786 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 30646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
