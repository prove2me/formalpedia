-- Prove2me | solution 1 for syracuse_descends_range_319836_323836
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:24.499982+00:00
-- url     : https://prove2.me/submissions/56cae386-6bc4-4df0-9e9f-4b07e21514b4

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


theorem B1081349 : Blo 319836 1081349 := bbase (se 4 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 1081349 = 202753) (by norm_num)
theorem B720917 : Blo 319836 720917 := bbase (se 6 (by rfl) ⟨16896, by rfl⟩ : syracuseStep 720917 = 33793) (by norm_num)
theorem B589853 : Blo 319836 589853 := bbase (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) (by norm_num)
theorem B360481 : Blo 319836 360481 := bbase (se 2 (by rfl) ⟨135180, by rfl⟩ : syracuseStep 360481 = 270361) (by norm_num)
theorem B2064437 : Blo 319836 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B360517 : Blo 319836 360517 := bbase (se 4 (by rfl) ⟨33798, by rfl⟩ : syracuseStep 360517 = 67597) (by norm_num)
theorem B720989 : Blo 319836 720989 := bbase (se 3 (by rfl) ⟨135185, by rfl⟩ : syracuseStep 720989 = 270371) (by norm_num)
theorem B327773 : Blo 319836 327773 := bbase (se 3 (by rfl) ⟨61457, by rfl⟩ : syracuseStep 327773 = 122915) (by norm_num)
theorem B360553 : Blo 319836 360553 := bbase (se 2 (by rfl) ⟨135207, by rfl⟩ : syracuseStep 360553 = 270415) (by norm_num)
theorem B360589 : Blo 319836 360589 := bbase (se 3 (by rfl) ⟨67610, by rfl⟩ : syracuseStep 360589 = 135221) (by norm_num)
theorem B721061 : Blo 319836 721061 := bbase (se 4 (by rfl) ⟨67599, by rfl⟩ : syracuseStep 721061 = 135199) (by norm_num)
theorem B360625 : Blo 319836 360625 := bbase (se 2 (by rfl) ⟨135234, by rfl⟩ : syracuseStep 360625 = 270469) (by norm_num)
theorem B557237 : Blo 319836 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B524485 : Blo 319836 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B1474757 : Blo 319836 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B360661 : Blo 319836 360661 := bbase (se 7 (by rfl) ⟨4226, by rfl⟩ : syracuseStep 360661 = 8453) (by norm_num)
theorem B1638629 : Blo 319836 1638629 := bbase (se 4 (by rfl) ⟨153621, by rfl⟩ : syracuseStep 1638629 = 307243) (by norm_num)
theorem B721133 : Blo 319836 721133 := bbase (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) (by norm_num)
theorem B360697 : Blo 319836 360697 := bbase (se 2 (by rfl) ⟨135261, by rfl⟩ : syracuseStep 360697 = 270523) (by norm_num)
theorem B360733 : Blo 319836 360733 := bbase (se 3 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 360733 = 135275) (by norm_num)
theorem B459037 : Blo 319836 459037 := bbase (se 3 (by rfl) ⟨86069, by rfl⟩ : syracuseStep 459037 = 172139) (by norm_num)
theorem B721205 : Blo 319836 721205 := bbase (se 5 (by rfl) ⟨33806, by rfl⟩ : syracuseStep 721205 = 67613) (by norm_num)
theorem B819517 : Blo 319836 819517 := bbase (se 3 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 819517 = 307319) (by norm_num)
theorem B360769 : Blo 319836 360769 := bbase (se 2 (by rfl) ⟨135288, by rfl⟩ : syracuseStep 360769 = 270577) (by norm_num)
theorem B360805 : Blo 319836 360805 := bbase (se 4 (by rfl) ⟨33825, by rfl⟩ : syracuseStep 360805 = 67651) (by norm_num)
theorem B721277 : Blo 319836 721277 := bbase (se 3 (by rfl) ⟨135239, by rfl⟩ : syracuseStep 721277 = 270479) (by norm_num)
theorem B360841 : Blo 319836 360841 := bbase (se 2 (by rfl) ⟨135315, by rfl⟩ : syracuseStep 360841 = 270631) (by norm_num)
theorem B360877 : Blo 319836 360877 := bbase (se 3 (by rfl) ⟨67664, by rfl⟩ : syracuseStep 360877 = 135329) (by norm_num)
theorem B819629 : Blo 319836 819629 := bbase (se 3 (by rfl) ⟨153680, by rfl⟩ : syracuseStep 819629 = 307361) (by norm_num)
theorem B1081781 : Blo 319836 1081781 := bbase (se 5 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 1081781 = 101417) (by norm_num)
theorem B721349 : Blo 319836 721349 := bbase (se 4 (by rfl) ⟨67626, by rfl⟩ : syracuseStep 721349 = 135253) (by norm_num)
theorem B360913 : Blo 319836 360913 := bbase (se 2 (by rfl) ⟨135342, by rfl⟩ : syracuseStep 360913 = 270685) (by norm_num)
theorem B360949 : Blo 319836 360949 := bbase (se 5 (by rfl) ⟨16919, by rfl⟩ : syracuseStep 360949 = 33839) (by norm_num)
theorem B721421 : Blo 319836 721421 := bbase (se 3 (by rfl) ⟨135266, by rfl⟩ : syracuseStep 721421 = 270533) (by norm_num)
theorem B360985 : Blo 319836 360985 := bbase (se 2 (by rfl) ⟨135369, by rfl⟩ : syracuseStep 360985 = 270739) (by norm_num)
theorem B590365 : Blo 319836 590365 := bbase (se 3 (by rfl) ⟨110693, by rfl⟩ : syracuseStep 590365 = 221387) (by norm_num)
theorem B361021 : Blo 319836 361021 := bbase (se 3 (by rfl) ⟨67691, by rfl⟩ : syracuseStep 361021 = 135383) (by norm_num)
theorem B721493 : Blo 319836 721493 := bbase (se 8 (by rfl) ⟨4227, by rfl⟩ : syracuseStep 721493 = 8455) (by norm_num)
theorem B361057 : Blo 319836 361057 := bbase (se 2 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 361057 = 270793) (by norm_num)
theorem B459373 : Blo 319836 459373 := bbase (se 3 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 459373 = 172265) (by norm_num)
theorem B361093 : Blo 319836 361093 := bbase (se 4 (by rfl) ⟨33852, by rfl⟩ : syracuseStep 361093 = 67705) (by norm_num)
theorem B721565 : Blo 319836 721565 := bbase (se 3 (by rfl) ⟨135293, by rfl⟩ : syracuseStep 721565 = 270587) (by norm_num)
theorem B361129 : Blo 319836 361129 := bbase (se 2 (by rfl) ⟨135423, by rfl⟩ : syracuseStep 361129 = 270847) (by norm_num)
theorem B688837 : Blo 319836 688837 := bbase (se 4 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 688837 = 129157) (by norm_num)
theorem B361165 : Blo 319836 361165 := bbase (se 3 (by rfl) ⟨67718, by rfl⟩ : syracuseStep 361165 = 135437) (by norm_num)
theorem B721637 : Blo 319836 721637 := bbase (se 4 (by rfl) ⟨67653, by rfl⟩ : syracuseStep 721637 = 135307) (by norm_num)
theorem B361201 : Blo 319836 361201 := bbase (se 2 (by rfl) ⟨135450, by rfl⟩ : syracuseStep 361201 = 270901) (by norm_num)
theorem B361237 : Blo 319836 361237 := bbase (se 6 (by rfl) ⟨8466, by rfl⟩ : syracuseStep 361237 = 16933) (by norm_num)
theorem B721709 : Blo 319836 721709 := bbase (se 3 (by rfl) ⟨135320, by rfl⟩ : syracuseStep 721709 = 270641) (by norm_num)
theorem B361273 : Blo 319836 361273 := bbase (se 2 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 361273 = 270955) (by norm_num)
theorem B459589 : Blo 319836 459589 := bbase (se 4 (by rfl) ⟨43086, by rfl⟩ : syracuseStep 459589 = 86173) (by norm_num)
theorem B361309 : Blo 319836 361309 := bbase (se 3 (by rfl) ⟨67745, by rfl⟩ : syracuseStep 361309 = 135491) (by norm_num)
theorem B1082213 : Blo 319836 1082213 := bbase (se 4 (by rfl) ⟨101457, by rfl⟩ : syracuseStep 1082213 = 202915) (by norm_num)
theorem B721781 : Blo 319836 721781 := bbase (se 5 (by rfl) ⟨33833, by rfl⟩ : syracuseStep 721781 = 67667) (by norm_num)
theorem B361345 : Blo 319836 361345 := bbase (se 2 (by rfl) ⟨135504, by rfl⟩ : syracuseStep 361345 = 271009) (by norm_num)
theorem B361381 : Blo 319836 361381 := bbase (se 4 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 361381 = 67759) (by norm_num)
theorem B721853 : Blo 319836 721853 := bbase (se 3 (by rfl) ⟨135347, by rfl⟩ : syracuseStep 721853 = 270695) (by norm_num)
theorem B590789 : Blo 319836 590789 := bbase (se 4 (by rfl) ⟨55386, by rfl⟩ : syracuseStep 590789 = 110773) (by norm_num)
theorem B361417 : Blo 319836 361417 := bbase (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) (by norm_num)
theorem B361453 : Blo 319836 361453 := bbase (se 3 (by rfl) ⟨67772, by rfl⟩ : syracuseStep 361453 = 135545) (by norm_num)
theorem B721925 : Blo 319836 721925 := bbase (se 4 (by rfl) ⟨67680, by rfl⟩ : syracuseStep 721925 = 135361) (by norm_num)
theorem B361489 : Blo 319836 361489 := bbase (se 2 (by rfl) ⟨135558, by rfl⟩ : syracuseStep 361489 = 271117) (by norm_num)
theorem B361525 : Blo 319836 361525 := bbase (se 5 (by rfl) ⟨16946, by rfl⟩ : syracuseStep 361525 = 33893) (by norm_num)
theorem B721997 : Blo 319836 721997 := bbase (se 3 (by rfl) ⟨135374, by rfl⟩ : syracuseStep 721997 = 270749) (by norm_num)
theorem B361561 : Blo 319836 361561 := bbase (se 2 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 361561 = 271171) (by norm_num)
theorem B361597 : Blo 319836 361597 := bbase (se 3 (by rfl) ⟨67799, by rfl⟩ : syracuseStep 361597 = 135599) (by norm_num)
theorem B722069 : Blo 319836 722069 := bbase (se 6 (by rfl) ⟨16923, by rfl⟩ : syracuseStep 722069 = 33847) (by norm_num)
theorem B918677 : Blo 319836 918677 := bbase (se 6 (by rfl) ⟨21531, by rfl⟩ : syracuseStep 918677 = 43063) (by norm_num)
theorem B361633 : Blo 319836 361633 := bbase (se 2 (by rfl) ⟨135612, by rfl⟩ : syracuseStep 361633 = 271225) (by norm_num)
theorem B459965 : Blo 319836 459965 := bbase (se 3 (by rfl) ⟨86243, by rfl⟩ : syracuseStep 459965 = 172487) (by norm_num)
theorem B361669 : Blo 319836 361669 := bbase (se 4 (by rfl) ⟨33906, by rfl⟩ : syracuseStep 361669 = 67813) (by norm_num)
theorem B722141 : Blo 319836 722141 := bbase (se 3 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 722141 = 270803) (by norm_num)
theorem B361705 : Blo 319836 361705 := bbase (se 2 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 361705 = 271279) (by norm_num)
theorem B361741 : Blo 319836 361741 := bbase (se 3 (by rfl) ⟨67826, by rfl⟩ : syracuseStep 361741 = 135653) (by norm_num)
theorem B1082645 : Blo 319836 1082645 := bbase (se 6 (by rfl) ⟨25374, by rfl⟩ : syracuseStep 1082645 = 50749) (by norm_num)
theorem B722213 : Blo 319836 722213 := bbase (se 4 (by rfl) ⟨67707, by rfl⟩ : syracuseStep 722213 = 135415) (by norm_num)
theorem B361777 : Blo 319836 361777 := bbase (se 2 (by rfl) ⟨135666, by rfl⟩ : syracuseStep 361777 = 271333) (by norm_num)
theorem B361813 : Blo 319836 361813 := bbase (se 12 (by rfl) ⟨132, by rfl⟩ : syracuseStep 361813 = 265) (by norm_num)
theorem B722285 : Blo 319836 722285 := bbase (se 3 (by rfl) ⟨135428, by rfl⟩ : syracuseStep 722285 = 270857) (by norm_num)
theorem B361849 : Blo 319836 361849 := bbase (se 2 (by rfl) ⟨135693, by rfl⟩ : syracuseStep 361849 = 271387) (by norm_num)
theorem B361885 : Blo 319836 361885 := bbase (se 3 (by rfl) ⟨67853, by rfl⟩ : syracuseStep 361885 = 135707) (by norm_num)
theorem B722357 : Blo 319836 722357 := bbase (se 5 (by rfl) ⟨33860, by rfl⟩ : syracuseStep 722357 = 67721) (by norm_num)
theorem B361921 : Blo 319836 361921 := bbase (se 2 (by rfl) ⟨135720, by rfl⟩ : syracuseStep 361921 = 271441) (by norm_num)
theorem B361957 : Blo 319836 361957 := bbase (se 4 (by rfl) ⟨33933, by rfl⟩ : syracuseStep 361957 = 67867) (by norm_num)
theorem B1836533 : Blo 319836 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B722429 : Blo 319836 722429 := bbase (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) (by norm_num)
theorem B361993 : Blo 319836 361993 := bbase (se 2 (by rfl) ⟨135747, by rfl⟩ : syracuseStep 361993 = 271495) (by norm_num)
theorem B362029 : Blo 319836 362029 := bbase (se 3 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 362029 = 135761) (by norm_num)
theorem B689725 : Blo 319836 689725 := bbase (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) (by norm_num)
theorem B722501 : Blo 319836 722501 := bbase (se 4 (by rfl) ⟨67734, by rfl⟩ : syracuseStep 722501 = 135469) (by norm_num)
theorem B362065 : Blo 319836 362065 := bbase (se 2 (by rfl) ⟨135774, by rfl⟩ : syracuseStep 362065 = 271549) (by norm_num)
theorem B362101 : Blo 319836 362101 := bbase (se 5 (by rfl) ⟨16973, by rfl⟩ : syracuseStep 362101 = 33947) (by norm_num)
theorem B722573 : Blo 319836 722573 := bbase (se 3 (by rfl) ⟨135482, by rfl⟩ : syracuseStep 722573 = 270965) (by norm_num)
theorem B362137 : Blo 319836 362137 := bbase (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) (by norm_num)
theorem B362173 : Blo 319836 362173 := bbase (se 3 (by rfl) ⟨67907, by rfl⟩ : syracuseStep 362173 = 135815) (by norm_num)
theorem B1083077 : Blo 319836 1083077 := bbase (se 4 (by rfl) ⟨101538, by rfl⟩ : syracuseStep 1083077 = 203077) (by norm_num)
theorem B722645 : Blo 319836 722645 := bbase (se 7 (by rfl) ⟨8468, by rfl⟩ : syracuseStep 722645 = 16937) (by norm_num)
theorem B362209 : Blo 319836 362209 := bbase (se 2 (by rfl) ⟨135828, by rfl⟩ : syracuseStep 362209 = 271657) (by norm_num)
theorem B362245 : Blo 319836 362245 := bbase (se 4 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 362245 = 67921) (by norm_num)
theorem B722717 : Blo 319836 722717 := bbase (se 3 (by rfl) ⟨135509, by rfl⟩ : syracuseStep 722717 = 271019) (by norm_num)
theorem B362281 : Blo 319836 362281 := bbase (se 2 (by rfl) ⟨135855, by rfl⟩ : syracuseStep 362281 = 271711) (by norm_num)
theorem B362317 : Blo 319836 362317 := bbase (se 3 (by rfl) ⟨67934, by rfl⟩ : syracuseStep 362317 = 135869) (by norm_num)
theorem B722789 : Blo 319836 722789 := bbase (se 4 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 722789 = 135523) (by norm_num)
theorem B362353 : Blo 319836 362353 := bbase (se 2 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 362353 = 271765) (by norm_num)
theorem B362389 : Blo 319836 362389 := bbase (se 6 (by rfl) ⟨8493, by rfl⟩ : syracuseStep 362389 = 16987) (by norm_num)
theorem B722861 : Blo 319836 722861 := bbase (se 3 (by rfl) ⟨135536, by rfl⟩ : syracuseStep 722861 = 271073) (by norm_num)
theorem B362425 : Blo 319836 362425 := bbase (se 2 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 362425 = 271819) (by norm_num)
theorem B362461 : Blo 319836 362461 := bbase (se 3 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 362461 = 135923) (by norm_num)
theorem B1214453 : Blo 319836 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B722933 : Blo 319836 722933 := bbase (se 5 (by rfl) ⟨33887, by rfl⟩ : syracuseStep 722933 = 67775) (by norm_num)
theorem B362497 : Blo 319836 362497 := bbase (se 2 (by rfl) ⟨135936, by rfl⟩ : syracuseStep 362497 = 271873) (by norm_num)
theorem B362533 : Blo 319836 362533 := bbase (se 4 (by rfl) ⟨33987, by rfl⟩ : syracuseStep 362533 = 67975) (by norm_num)
theorem B690221 : Blo 319836 690221 := bbase (se 3 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 690221 = 258833) (by norm_num)
theorem B723005 : Blo 319836 723005 := bbase (se 3 (by rfl) ⟨135563, by rfl⟩ : syracuseStep 723005 = 271127) (by norm_num)
theorem B362569 : Blo 319836 362569 := bbase (se 2 (by rfl) ⟨135963, by rfl⟩ : syracuseStep 362569 = 271927) (by norm_num)
theorem B362605 : Blo 319836 362605 := bbase (se 3 (by rfl) ⟨67988, by rfl⟩ : syracuseStep 362605 = 135977) (by norm_num)
theorem B1083509 : Blo 319836 1083509 := bbase (se 5 (by rfl) ⟨50789, by rfl⟩ : syracuseStep 1083509 = 101579) (by norm_num)
theorem B1476725 : Blo 319836 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B723077 : Blo 319836 723077 := bbase (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) (by norm_num)
theorem B362641 : Blo 319836 362641 := bbase (se 2 (by rfl) ⟨135990, by rfl⟩ : syracuseStep 362641 = 271981) (by norm_num)
theorem B362677 : Blo 319836 362677 := bbase (se 5 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 362677 = 34001) (by norm_num)
theorem B723149 : Blo 319836 723149 := bbase (se 3 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 723149 = 271181) (by norm_num)
theorem B362713 : Blo 319836 362713 := bbase (se 2 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 362713 = 272035) (by norm_num)
theorem B362749 : Blo 319836 362749 := bbase (se 3 (by rfl) ⟨68015, by rfl⟩ : syracuseStep 362749 = 136031) (by norm_num)
theorem B723221 : Blo 319836 723221 := bbase (se 6 (by rfl) ⟨16950, by rfl⟩ : syracuseStep 723221 = 33901) (by norm_num)
theorem B2492693 : Blo 319836 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B362785 : Blo 319836 362785 := bbase (se 2 (by rfl) ⟨136044, by rfl⟩ : syracuseStep 362785 = 272089) (by norm_num)
theorem B1968437 : Blo 319836 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B362821 : Blo 319836 362821 := bbase (se 4 (by rfl) ⟨34014, by rfl⟩ : syracuseStep 362821 = 68029) (by norm_num)
theorem B723293 : Blo 319836 723293 := bbase (se 3 (by rfl) ⟨135617, by rfl⟩ : syracuseStep 723293 = 271235) (by norm_num)
theorem B362857 : Blo 319836 362857 := bbase (se 2 (by rfl) ⟨136071, by rfl⟩ : syracuseStep 362857 = 272143) (by norm_num)
theorem B362893 : Blo 319836 362893 := bbase (se 3 (by rfl) ⟨68042, by rfl⟩ : syracuseStep 362893 = 136085) (by norm_num)
theorem B723365 : Blo 319836 723365 := bbase (se 4 (by rfl) ⟨67815, by rfl⟩ : syracuseStep 723365 = 135631) (by norm_num)
theorem B362929 : Blo 319836 362929 := bbase (se 2 (by rfl) ⟨136098, by rfl⟩ : syracuseStep 362929 = 272197) (by norm_num)
theorem B362965 : Blo 319836 362965 := bbase (se 7 (by rfl) ⟨4253, by rfl⟩ : syracuseStep 362965 = 8507) (by norm_num)
theorem B723437 : Blo 319836 723437 := bbase (se 3 (by rfl) ⟨135644, by rfl⟩ : syracuseStep 723437 = 271289) (by norm_num)
theorem B363001 : Blo 319836 363001 := bbase (se 2 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 363001 = 272251) (by norm_num)
theorem B363037 : Blo 319836 363037 := bbase (se 3 (by rfl) ⟨68069, by rfl⟩ : syracuseStep 363037 = 136139) (by norm_num)
theorem B1083941 : Blo 319836 1083941 := bbase (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) (by norm_num)
theorem B723509 : Blo 319836 723509 := bbase (se 5 (by rfl) ⟨33914, by rfl⟩ : syracuseStep 723509 = 67829) (by norm_num)
theorem B363073 : Blo 319836 363073 := bbase (se 2 (by rfl) ⟨136152, by rfl⟩ : syracuseStep 363073 = 272305) (by norm_num)
theorem B363109 : Blo 319836 363109 := bbase (se 4 (by rfl) ⟨34041, by rfl⟩ : syracuseStep 363109 = 68083) (by norm_num)
theorem B723581 : Blo 319836 723581 := bbase (se 3 (by rfl) ⟨135671, by rfl⟩ : syracuseStep 723581 = 271343) (by norm_num)
theorem B363145 : Blo 319836 363145 := bbase (se 2 (by rfl) ⟨136179, by rfl⟩ : syracuseStep 363145 = 272359) (by norm_num)
theorem B363181 : Blo 319836 363181 := bbase (se 3 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 363181 = 136193) (by norm_num)
theorem B723653 : Blo 319836 723653 := bbase (se 4 (by rfl) ⟨67842, by rfl⟩ : syracuseStep 723653 = 135685) (by norm_num)
theorem B920261 : Blo 319836 920261 := bbase (se 4 (by rfl) ⟨86274, by rfl⟩ : syracuseStep 920261 = 172549) (by norm_num)
theorem B363217 : Blo 319836 363217 := bbase (se 2 (by rfl) ⟨136206, by rfl⟩ : syracuseStep 363217 = 272413) (by norm_num)
theorem B363253 : Blo 319836 363253 := bbase (se 5 (by rfl) ⟨17027, by rfl⟩ : syracuseStep 363253 = 34055) (by norm_num)
theorem B723725 : Blo 319836 723725 := bbase (se 3 (by rfl) ⟨135698, by rfl⟩ : syracuseStep 723725 = 271397) (by norm_num)
theorem B363289 : Blo 319836 363289 := bbase (se 2 (by rfl) ⟨136233, by rfl⟩ : syracuseStep 363289 = 272467) (by norm_num)
theorem B363325 : Blo 319836 363325 := bbase (se 3 (by rfl) ⟨68123, by rfl⟩ : syracuseStep 363325 = 136247) (by norm_num)
theorem B723797 : Blo 319836 723797 := bbase (se 9 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 723797 = 4241) (by norm_num)
theorem B363361 : Blo 319836 363361 := bbase (se 2 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 363361 = 272521) (by norm_num)
theorem B363397 : Blo 319836 363397 := bbase (se 4 (by rfl) ⟨34068, by rfl⟩ : syracuseStep 363397 = 68137) (by norm_num)
theorem B691085 : Blo 319836 691085 := bbase (se 3 (by rfl) ⟨129578, by rfl⟩ : syracuseStep 691085 = 259157) (by norm_num)
theorem B723869 : Blo 319836 723869 := bbase (se 3 (by rfl) ⟨135725, by rfl⟩ : syracuseStep 723869 = 271451) (by norm_num)
theorem B363433 : Blo 319836 363433 := bbase (se 2 (by rfl) ⟨136287, by rfl⟩ : syracuseStep 363433 = 272575) (by norm_num)
theorem B363469 : Blo 319836 363469 := bbase (se 3 (by rfl) ⟨68150, by rfl⟩ : syracuseStep 363469 = 136301) (by norm_num)
theorem B1084373 : Blo 319836 1084373 := bbase (se 7 (by rfl) ⟨12707, by rfl⟩ : syracuseStep 1084373 = 25415) (by norm_num)
theorem B723941 : Blo 319836 723941 := bbase (se 4 (by rfl) ⟨67869, by rfl⟩ : syracuseStep 723941 = 135739) (by norm_num)
theorem B363505 : Blo 319836 363505 := bbase (se 2 (by rfl) ⟨136314, by rfl⟩ : syracuseStep 363505 = 272629) (by norm_num)
theorem B1543157 : Blo 319836 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B363541 : Blo 319836 363541 := bbase (se 6 (by rfl) ⟨8520, by rfl⟩ : syracuseStep 363541 = 17041) (by norm_num)
theorem B691229 : Blo 319836 691229 := bbase (se 3 (by rfl) ⟨129605, by rfl⟩ : syracuseStep 691229 = 259211) (by norm_num)
theorem B724013 : Blo 319836 724013 := bbase (se 3 (by rfl) ⟨135752, by rfl⟩ : syracuseStep 724013 = 271505) (by norm_num)
theorem B363577 : Blo 319836 363577 := bbase (se 2 (by rfl) ⟨136341, by rfl⟩ : syracuseStep 363577 = 272683) (by norm_num)
theorem B363613 : Blo 319836 363613 := bbase (se 3 (by rfl) ⟨68177, by rfl⟩ : syracuseStep 363613 = 136355) (by norm_num)
theorem B724085 : Blo 319836 724085 := bbase (se 5 (by rfl) ⟨33941, by rfl⟩ : syracuseStep 724085 = 67883) (by norm_num)
theorem B494717 : Blo 319836 494717 := bbase (se 3 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 494717 = 185519) (by norm_num)
theorem B363649 : Blo 319836 363649 := bbase (se 2 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 363649 = 272737) (by norm_num)
theorem B363685 : Blo 319836 363685 := bbase (se 4 (by rfl) ⟨34095, by rfl⟩ : syracuseStep 363685 = 68191) (by norm_num)
theorem B724157 : Blo 319836 724157 := bbase (se 3 (by rfl) ⟨135779, by rfl⟩ : syracuseStep 724157 = 271559) (by norm_num)
theorem B363721 : Blo 319836 363721 := bbase (se 2 (by rfl) ⟨136395, by rfl⟩ : syracuseStep 363721 = 272791) (by norm_num)
theorem B363757 : Blo 319836 363757 := bbase (se 3 (by rfl) ⟨68204, by rfl⟩ : syracuseStep 363757 = 136409) (by norm_num)
theorem B724229 : Blo 319836 724229 := bbase (se 4 (by rfl) ⟨67896, by rfl⟩ : syracuseStep 724229 = 135793) (by norm_num)
theorem B363793 : Blo 319836 363793 := bbase (se 2 (by rfl) ⟨136422, by rfl⟩ : syracuseStep 363793 = 272845) (by norm_num)
theorem B363829 : Blo 319836 363829 := bbase (se 5 (by rfl) ⟨17054, by rfl⟩ : syracuseStep 363829 = 34109) (by norm_num)
theorem B724301 : Blo 319836 724301 := bbase (se 3 (by rfl) ⟨135806, by rfl⟩ : syracuseStep 724301 = 271613) (by norm_num)
theorem B363865 : Blo 319836 363865 := bbase (se 2 (by rfl) ⟨136449, by rfl⟩ : syracuseStep 363865 = 272899) (by norm_num)
theorem B920933 : Blo 319836 920933 := bbase (se 4 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 920933 = 172675) (by norm_num)
theorem B363901 : Blo 319836 363901 := bbase (se 3 (by rfl) ⟨68231, by rfl⟩ : syracuseStep 363901 = 136463) (by norm_num)
theorem B1084805 : Blo 319836 1084805 := bbase (se 4 (by rfl) ⟨101700, by rfl⟩ : syracuseStep 1084805 = 203401) (by norm_num)
theorem B724373 : Blo 319836 724373 := bbase (se 6 (by rfl) ⟨16977, by rfl⟩ : syracuseStep 724373 = 33955) (by norm_num)
theorem B363937 : Blo 319836 363937 := bbase (se 2 (by rfl) ⟨136476, by rfl⟩ : syracuseStep 363937 = 272953) (by norm_num)
theorem B363973 : Blo 319836 363973 := bbase (se 4 (by rfl) ⟨34122, by rfl⟩ : syracuseStep 363973 = 68245) (by norm_num)
theorem B724445 : Blo 319836 724445 := bbase (se 3 (by rfl) ⟨135833, by rfl⟩ : syracuseStep 724445 = 271667) (by norm_num)
theorem B364009 : Blo 319836 364009 := bbase (se 2 (by rfl) ⟨136503, by rfl⟩ : syracuseStep 364009 = 273007) (by norm_num)
theorem B364045 : Blo 319836 364045 := bbase (se 3 (by rfl) ⟨68258, by rfl⟩ : syracuseStep 364045 = 136517) (by norm_num)
theorem B1379861 : Blo 319836 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B724517 : Blo 319836 724517 := bbase (se 4 (by rfl) ⟨67923, by rfl⟩ : syracuseStep 724517 = 135847) (by norm_num)
theorem B364081 : Blo 319836 364081 := bbase (se 2 (by rfl) ⟨136530, by rfl⟩ : syracuseStep 364081 = 273061) (by norm_num)
theorem B462397 : Blo 319836 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B364117 : Blo 319836 364117 := bbase (se 8 (by rfl) ⟨2133, by rfl⟩ : syracuseStep 364117 = 4267) (by norm_num)
theorem B724589 : Blo 319836 724589 := bbase (se 3 (by rfl) ⟨135860, by rfl⟩ : syracuseStep 724589 = 271721) (by norm_num)
theorem B364153 : Blo 319836 364153 := bbase (se 2 (by rfl) ⟨136557, by rfl⟩ : syracuseStep 364153 = 273115) (by norm_num)
theorem B364189 : Blo 319836 364189 := bbase (se 3 (by rfl) ⟨68285, by rfl⟩ : syracuseStep 364189 = 136571) (by norm_num)
theorem B724661 : Blo 319836 724661 := bbase (se 5 (by rfl) ⟨33968, by rfl⟩ : syracuseStep 724661 = 67937) (by norm_num)
theorem B364225 : Blo 319836 364225 := bbase (se 2 (by rfl) ⟨136584, by rfl⟩ : syracuseStep 364225 = 273169) (by norm_num)
theorem B364261 : Blo 319836 364261 := bbase (se 4 (by rfl) ⟨34149, by rfl⟩ : syracuseStep 364261 = 68299) (by norm_num)
theorem B724733 : Blo 319836 724733 := bbase (se 3 (by rfl) ⟨135887, by rfl⟩ : syracuseStep 724733 = 271775) (by norm_num)
theorem B364297 : Blo 319836 364297 := bbase (se 2 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 364297 = 273223) (by norm_num)
theorem B921365 : Blo 319836 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B1085237 : Blo 319836 1085237 := bbase (se 5 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 1085237 = 101741) (by norm_num)
theorem B724805 : Blo 319836 724805 := bbase (se 4 (by rfl) ⟨67950, by rfl⟩ : syracuseStep 724805 = 135901) (by norm_num)
theorem B757621 : Blo 319836 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B724877 : Blo 319836 724877 := bbase (se 3 (by rfl) ⟨135914, by rfl⟩ : syracuseStep 724877 = 271829) (by norm_num)
theorem B724949 : Blo 319836 724949 := bbase (se 7 (by rfl) ⟨8495, by rfl⟩ : syracuseStep 724949 = 16991) (by norm_num)
theorem B725021 : Blo 319836 725021 := bbase (se 3 (by rfl) ⟨135941, by rfl⟩ : syracuseStep 725021 = 271883) (by norm_num)
theorem B1216565 : Blo 319836 1216565 := bbase (se 5 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 1216565 = 114053) (by norm_num)
theorem B725093 : Blo 319836 725093 := bbase (se 4 (by rfl) ⟨67977, by rfl⟩ : syracuseStep 725093 = 135955) (by norm_num)
theorem B725165 : Blo 319836 725165 := bbase (se 3 (by rfl) ⟨135968, by rfl⟩ : syracuseStep 725165 = 271937) (by norm_num)
theorem B1085669 : Blo 319836 1085669 := bbase (se 4 (by rfl) ⟨101781, by rfl⟩ : syracuseStep 1085669 = 203563) (by norm_num)
theorem B725237 : Blo 319836 725237 := bbase (se 5 (by rfl) ⟨33995, by rfl⟩ : syracuseStep 725237 = 67991) (by norm_num)
theorem B1544501 : Blo 319836 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B725309 : Blo 319836 725309 := bbase (se 3 (by rfl) ⟨135995, by rfl⟩ : syracuseStep 725309 = 271991) (by norm_num)
theorem B1216853 : Blo 319836 1216853 := bbase (se 10 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 1216853 = 3565) (by norm_num)
theorem B725381 : Blo 319836 725381 := bbase (se 4 (by rfl) ⟨68004, by rfl⟩ : syracuseStep 725381 = 136009) (by norm_num)
theorem B725453 : Blo 319836 725453 := bbase (se 3 (by rfl) ⟨136022, by rfl⟩ : syracuseStep 725453 = 272045) (by norm_num)
theorem B922117 : Blo 319836 922117 := bbase (se 4 (by rfl) ⟨86448, by rfl⟩ : syracuseStep 922117 = 172897) (by norm_num)
theorem B725525 : Blo 319836 725525 := bbase (se 6 (by rfl) ⟨17004, by rfl⟩ : syracuseStep 725525 = 34009) (by norm_num)
theorem B725597 : Blo 319836 725597 := bbase (se 3 (by rfl) ⟨136049, by rfl⟩ : syracuseStep 725597 = 272099) (by norm_num)
theorem B692869 : Blo 319836 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B1086101 : Blo 319836 1086101 := bbase (se 6 (by rfl) ⟨25455, by rfl⟩ : syracuseStep 1086101 = 50911) (by norm_num)
theorem B725669 : Blo 319836 725669 := bbase (se 4 (by rfl) ⟨68031, by rfl⟩ : syracuseStep 725669 = 136063) (by norm_num)
theorem B725741 : Blo 319836 725741 := bbase (se 3 (by rfl) ⟨136076, by rfl⟩ : syracuseStep 725741 = 272153) (by norm_num)
theorem B725813 : Blo 319836 725813 := bbase (se 5 (by rfl) ⟨34022, by rfl⟩ : syracuseStep 725813 = 68045) (by norm_num)
theorem B725885 : Blo 319836 725885 := bbase (se 3 (by rfl) ⟨136103, by rfl⟩ : syracuseStep 725885 = 272207) (by norm_num)
theorem B725957 : Blo 319836 725957 := bbase (se 4 (by rfl) ⟨68058, by rfl⟩ : syracuseStep 725957 = 136117) (by norm_num)
theorem B726029 : Blo 319836 726029 := bbase (se 3 (by rfl) ⟨136130, by rfl⟩ : syracuseStep 726029 = 272261) (by norm_num)
theorem B693317 : Blo 319836 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B1086533 : Blo 319836 1086533 := bbase (se 4 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 1086533 = 203725) (by norm_num)
theorem B726101 : Blo 319836 726101 := bbase (se 8 (by rfl) ⟨4254, by rfl⟩ : syracuseStep 726101 = 8509) (by norm_num)
theorem B726173 : Blo 319836 726173 := bbase (se 3 (by rfl) ⟨136157, by rfl⟩ : syracuseStep 726173 = 272315) (by norm_num)
theorem B726245 : Blo 319836 726245 := bbase (se 4 (by rfl) ⟨68085, by rfl⟩ : syracuseStep 726245 = 136171) (by norm_num)
theorem B1381637 : Blo 319836 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B726317 : Blo 319836 726317 := bbase (se 3 (by rfl) ⟨136184, by rfl⟩ : syracuseStep 726317 = 272369) (by norm_num)
theorem B464221 : Blo 319836 464221 := bbase (se 3 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 464221 = 174083) (by norm_num)
theorem B726389 : Blo 319836 726389 := bbase (se 5 (by rfl) ⟨34049, by rfl⟩ : syracuseStep 726389 = 68099) (by norm_num)
theorem B726461 : Blo 319836 726461 := bbase (se 3 (by rfl) ⟨136211, by rfl⟩ : syracuseStep 726461 = 272423) (by norm_num)
theorem B1218037 : Blo 319836 1218037 := bbase (se 5 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 1218037 = 114191) (by norm_num)
theorem B1086965 : Blo 319836 1086965 := bbase (se 5 (by rfl) ⟨50951, by rfl⟩ : syracuseStep 1086965 = 101903) (by norm_num)
theorem B726533 : Blo 319836 726533 := bbase (se 4 (by rfl) ⟨68112, by rfl⟩ : syracuseStep 726533 = 136225) (by norm_num)
theorem B2430485 : Blo 319836 2430485 := bbase (se 6 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 2430485 = 113929) (by norm_num)
theorem B661069 : Blo 319836 661069 := bbase (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) (by norm_num)
theorem B726605 : Blo 319836 726605 := bbase (se 3 (by rfl) ⟨136238, by rfl⟩ : syracuseStep 726605 = 272477) (by norm_num)
theorem B726677 : Blo 319836 726677 := bbase (se 6 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 726677 = 34063) (by norm_num)
theorem B1545925 : Blo 319836 1545925 := bbase (se 4 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 1545925 = 289861) (by norm_num)
theorem B726749 : Blo 319836 726749 := bbase (se 3 (by rfl) ⟨136265, by rfl⟩ : syracuseStep 726749 = 272531) (by norm_num)
theorem B1218341 : Blo 319836 1218341 := bbase (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) (by norm_num)
theorem B726821 : Blo 319836 726821 := bbase (se 4 (by rfl) ⟨68139, by rfl⟩ : syracuseStep 726821 = 136279) (by norm_num)
theorem B726893 : Blo 319836 726893 := bbase (se 3 (by rfl) ⟨136292, by rfl⟩ : syracuseStep 726893 = 272585) (by norm_num)
theorem B1087397 : Blo 319836 1087397 := bbase (se 4 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 1087397 = 203887) (by norm_num)
theorem B726965 : Blo 319836 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B727037 : Blo 319836 727037 := bbase (se 3 (by rfl) ⟨136319, by rfl⟩ : syracuseStep 727037 = 272639) (by norm_num)
theorem B727109 : Blo 319836 727109 := bbase (se 4 (by rfl) ⟨68166, by rfl⟩ : syracuseStep 727109 = 136333) (by norm_num)
theorem B2922581 : Blo 319836 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B727181 : Blo 319836 727181 := bbase (se 3 (by rfl) ⟨136346, by rfl⟩ : syracuseStep 727181 = 272693) (by norm_num)
theorem B3643541 : Blo 319836 3643541 := bbase (se 6 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 3643541 = 170791) (by norm_num)
theorem B727253 : Blo 319836 727253 := bbase (se 7 (by rfl) ⟨8522, by rfl⟩ : syracuseStep 727253 = 17045) (by norm_num)
theorem B1382629 : Blo 319836 1382629 := bbase (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) (by norm_num)
theorem B465133 : Blo 319836 465133 := bbase (se 3 (by rfl) ⟨87212, by rfl⟩ : syracuseStep 465133 = 174425) (by norm_num)
theorem B727325 : Blo 319836 727325 := bbase (se 3 (by rfl) ⟨136373, by rfl⟩ : syracuseStep 727325 = 272747) (by norm_num)
theorem B1087829 : Blo 319836 1087829 := bbase (se 10 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 1087829 = 3187) (by norm_num)
theorem B727397 : Blo 319836 727397 := bbase (se 4 (by rfl) ⟨68193, by rfl⟩ : syracuseStep 727397 = 136387) (by norm_num)
theorem B727469 : Blo 319836 727469 := bbase (se 3 (by rfl) ⟨136400, by rfl⟩ : syracuseStep 727469 = 272801) (by norm_num)
theorem B727541 : Blo 319836 727541 := bbase (se 5 (by rfl) ⟨34103, by rfl⟩ : syracuseStep 727541 = 68207) (by norm_num)
theorem B727613 : Blo 319836 727613 := bbase (se 3 (by rfl) ⟨136427, by rfl⟩ : syracuseStep 727613 = 272855) (by norm_num)
theorem B727685 : Blo 319836 727685 := bbase (se 4 (by rfl) ⟨68220, by rfl⟩ : syracuseStep 727685 = 136441) (by norm_num)
theorem B498317 : Blo 319836 498317 := bbase (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) (by norm_num)
theorem B727757 : Blo 319836 727757 := bbase (se 3 (by rfl) ⟨136454, by rfl⟩ : syracuseStep 727757 = 272909) (by norm_num)
theorem B1088261 : Blo 319836 1088261 := bbase (se 4 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 1088261 = 204049) (by norm_num)
theorem B727829 : Blo 319836 727829 := bbase (se 6 (by rfl) ⟨17058, by rfl⟩ : syracuseStep 727829 = 34117) (by norm_num)
theorem B727901 : Blo 319836 727901 := bbase (se 3 (by rfl) ⟨136481, by rfl⟩ : syracuseStep 727901 = 272963) (by norm_num)
theorem B2923381 : Blo 319836 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B727973 : Blo 319836 727973 := bbase (se 4 (by rfl) ⟨68247, by rfl⟩ : syracuseStep 727973 = 136495) (by norm_num)
theorem B728045 : Blo 319836 728045 := bbase (se 3 (by rfl) ⟨136508, by rfl⟩ : syracuseStep 728045 = 273017) (by norm_num)
theorem B662581 : Blo 319836 662581 := bbase (se 5 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 662581 = 62117) (by norm_num)
theorem B728117 : Blo 319836 728117 := bbase (se 5 (by rfl) ⟨34130, by rfl⟩ : syracuseStep 728117 = 68261) (by norm_num)
theorem B728189 : Blo 319836 728189 := bbase (se 3 (by rfl) ⟨136535, by rfl⟩ : syracuseStep 728189 = 273071) (by norm_num)
theorem B1154213 : Blo 319836 1154213 := bbase (se 4 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 1154213 = 216415) (by norm_num)
theorem B2202805 : Blo 319836 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1088693 : Blo 319836 1088693 := bbase (se 5 (by rfl) ⟨51032, by rfl⟩ : syracuseStep 1088693 = 102065) (by norm_num)
theorem B728261 : Blo 319836 728261 := bbase (se 4 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 728261 = 136549) (by norm_num)
theorem B1252565 : Blo 319836 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1023205 : Blo 319836 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B728333 : Blo 319836 728333 := bbase (se 3 (by rfl) ⟨136562, by rfl⟩ : syracuseStep 728333 = 273125) (by norm_num)
theorem B728405 : Blo 319836 728405 := bbase (se 11 (by rfl) ⟨533, by rfl⟩ : syracuseStep 728405 = 1067) (by norm_num)
theorem B728477 : Blo 319836 728477 := bbase (se 3 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 728477 = 273179) (by norm_num)
theorem B433613 : Blo 319836 433613 := bbase (se 3 (by rfl) ⟨81302, by rfl⟩ : syracuseStep 433613 = 162605) (by norm_num)
theorem B728549 : Blo 319836 728549 := bbase (se 4 (by rfl) ⟨68301, by rfl⟩ : syracuseStep 728549 = 136603) (by norm_num)
theorem B368105 : Blo 319836 368105 := bbase (se 2 (by rfl) ⟨138039, by rfl⟩ : syracuseStep 368105 = 276079) (by norm_num)
theorem B4562453 : Blo 319836 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B728621 : Blo 319836 728621 := bbase (se 3 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 728621 = 273233) (by norm_num)
theorem B1089125 : Blo 319836 1089125 := bbase (se 4 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 1089125 = 204211) (by norm_num)
theorem B1220453 : Blo 319836 1220453 := bbase (se 4 (by rfl) ⟨114417, by rfl⟩ : syracuseStep 1220453 = 228835) (by norm_num)
theorem B434197 : Blo 319836 434197 := bbase (se 6 (by rfl) ⟨10176, by rfl⟩ : syracuseStep 434197 = 20353) (by norm_num)
theorem B1089557 : Blo 319836 1089557 := bbase (se 6 (by rfl) ⟨25536, by rfl⟩ : syracuseStep 1089557 = 51073) (by norm_num)
theorem B1220741 : Blo 319836 1220741 := bbase (se 4 (by rfl) ⟨114444, by rfl⟩ : syracuseStep 1220741 = 228889) (by norm_num)
theorem B434317 : Blo 319836 434317 := bbase (se 3 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 434317 = 162869) (by norm_num)
theorem B631181 : Blo 319836 631181 := bbase (se 3 (by rfl) ⟨118346, by rfl⟩ : syracuseStep 631181 = 236693) (by norm_num)
theorem B1647029 : Blo 319836 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B1089989 : Blo 319836 1089989 := bbase (se 4 (by rfl) ⟨102186, by rfl⟩ : syracuseStep 1089989 = 204373) (by norm_num)
theorem B631405 : Blo 319836 631405 := bbase (se 3 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 631405 = 236777) (by norm_num)
theorem B992101 : Blo 319836 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B1090421 : Blo 319836 1090421 := bbase (se 5 (by rfl) ⟨51113, by rfl⟩ : syracuseStep 1090421 = 102227) (by norm_num)
theorem B1156069 : Blo 319836 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B730181 : Blo 319836 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B1221925 : Blo 319836 1221925 := bbase (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) (by norm_num)
theorem B1090853 : Blo 319836 1090853 := bbase (se 4 (by rfl) ⟨102267, by rfl⟩ : syracuseStep 1090853 = 204535) (by norm_num)
theorem B1648181 : Blo 319836 1648181 := bbase (se 5 (by rfl) ⟨77258, by rfl⟩ : syracuseStep 1648181 = 154517) (by norm_num)
theorem B1222229 : Blo 319836 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B370273 : Blo 319836 370273 := bbase (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) (by norm_num)
theorem B1025669 : Blo 319836 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B1091285 : Blo 319836 1091285 := bbase (se 7 (by rfl) ⟨12788, by rfl⟩ : syracuseStep 1091285 = 25577) (by norm_num)
theorem B796709 : Blo 319836 796709 := bbase (se 4 (by rfl) ⟨74691, by rfl⟩ : syracuseStep 796709 = 149383) (by norm_num)
theorem B1091717 : Blo 319836 1091717 := bbase (se 4 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 1091717 = 204697) (by norm_num)
theorem B1550789 : Blo 319836 1550789 := bbase (se 4 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 1550789 = 290773) (by norm_num)
theorem B1092149 : Blo 319836 1092149 := bbase (se 5 (by rfl) ⟨51194, by rfl⟩ : syracuseStep 1092149 = 102389) (by norm_num)
theorem B338713 : Blo 319836 338713 := bbase (se 2 (by rfl) ⟨127017, by rfl⟩ : syracuseStep 338713 = 254035) (by norm_num)
theorem B1682309 : Blo 319836 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B732053 : Blo 319836 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B666557 : Blo 319836 666557 := bbase (se 3 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 666557 = 249959) (by norm_num)
theorem B1092581 : Blo 319836 1092581 := bbase (se 4 (by rfl) ⟨102429, by rfl⟩ : syracuseStep 1092581 = 204859) (by norm_num)
theorem B1027093 : Blo 319836 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B404833 : Blo 319836 404833 := bbase (se 2 (by rfl) ⟨151812, by rfl⟩ : syracuseStep 404833 = 303625) (by norm_num)
theorem B699781 : Blo 319836 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B404929 : Blo 319836 404929 := bbase (se 2 (by rfl) ⟨151848, by rfl⟩ : syracuseStep 404929 = 303697) (by norm_num)
theorem B1027541 : Blo 319836 1027541 := bbase (se 7 (by rfl) ⟨12041, by rfl⟩ : syracuseStep 1027541 = 24083) (by norm_num)
theorem B405101 : Blo 319836 405101 := bbase (se 3 (by rfl) ⟨75956, by rfl⟩ : syracuseStep 405101 = 151913) (by norm_num)
theorem B1224341 : Blo 319836 1224341 := bbase (se 6 (by rfl) ⟨28695, by rfl⟩ : syracuseStep 1224341 = 57391) (by norm_num)
theorem B405157 : Blo 319836 405157 := bbase (se 4 (by rfl) ⟨37983, by rfl⟩ : syracuseStep 405157 = 75967) (by norm_num)
theorem B405253 : Blo 319836 405253 := bbase (se 4 (by rfl) ⟨37992, by rfl⟩ : syracuseStep 405253 = 75985) (by norm_num)
theorem B405425 : Blo 319836 405425 := bbase (se 2 (by rfl) ⟨152034, by rfl⟩ : syracuseStep 405425 = 304069) (by norm_num)
theorem B1224629 : Blo 319836 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B405481 : Blo 319836 405481 := bbase (se 2 (by rfl) ⟨152055, by rfl⟩ : syracuseStep 405481 = 304111) (by norm_num)
theorem B1552421 : Blo 319836 1552421 := bbase (se 4 (by rfl) ⟨145539, by rfl⟩ : syracuseStep 1552421 = 291079) (by norm_num)
theorem B405577 : Blo 319836 405577 := bbase (se 2 (by rfl) ⟨152091, by rfl⟩ : syracuseStep 405577 = 304183) (by norm_num)
theorem B405749 : Blo 319836 405749 := bbase (se 5 (by rfl) ⟨19019, by rfl⟩ : syracuseStep 405749 = 38039) (by norm_num)
theorem B405805 : Blo 319836 405805 := bbase (se 3 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 405805 = 152177) (by norm_num)
theorem B405901 : Blo 319836 405901 := bbase (se 3 (by rfl) ⟨76106, by rfl⟩ : syracuseStep 405901 = 152213) (by norm_num)
theorem B1159589 : Blo 319836 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B406073 : Blo 319836 406073 := bbase (se 2 (by rfl) ⟨152277, by rfl⟩ : syracuseStep 406073 = 304555) (by norm_num)
theorem B406129 : Blo 319836 406129 := bbase (se 2 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 406129 = 304597) (by norm_num)
theorem B2765461 : Blo 319836 2765461 := bbase (se 6 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 2765461 = 129631) (by norm_num)
theorem B406225 : Blo 319836 406225 := bbase (se 2 (by rfl) ⟨152334, by rfl⟩ : syracuseStep 406225 = 304669) (by norm_num)
theorem B1160021 : Blo 319836 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B406397 : Blo 319836 406397 := bbase (se 3 (by rfl) ⟨76199, by rfl⟩ : syracuseStep 406397 = 152399) (by norm_num)
theorem B406453 : Blo 319836 406453 := bbase (se 5 (by rfl) ⟨19052, by rfl⟩ : syracuseStep 406453 = 38105) (by norm_num)
theorem B406549 : Blo 319836 406549 := bbase (se 6 (by rfl) ⟨9528, by rfl⟩ : syracuseStep 406549 = 19057) (by norm_num)
theorem B1225813 : Blo 319836 1225813 := bbase (se 8 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 1225813 = 14365) (by norm_num)
theorem B2438261 : Blo 319836 2438261 := bbase (se 5 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 2438261 = 228587) (by norm_num)
theorem B406721 : Blo 319836 406721 := bbase (se 2 (by rfl) ⟨152520, by rfl⟩ : syracuseStep 406721 = 305041) (by norm_num)
theorem B1619189 : Blo 319836 1619189 := bbase (se 5 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 1619189 = 151799) (by norm_num)
theorem B406777 : Blo 319836 406777 := bbase (se 2 (by rfl) ⟨152541, by rfl⟩ : syracuseStep 406777 = 305083) (by norm_num)
theorem B406873 : Blo 319836 406873 := bbase (se 2 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 406873 = 305155) (by norm_num)
theorem B1226117 : Blo 319836 1226117 := bbase (se 4 (by rfl) ⟨114948, by rfl⟩ : syracuseStep 1226117 = 229897) (by norm_num)
theorem B407045 : Blo 319836 407045 := bbase (se 4 (by rfl) ⟨38160, by rfl⟩ : syracuseStep 407045 = 76321) (by norm_num)
theorem B407101 : Blo 319836 407101 := bbase (se 3 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 407101 = 152663) (by norm_num)
theorem B407197 : Blo 319836 407197 := bbase (se 3 (by rfl) ⟨76349, by rfl⟩ : syracuseStep 407197 = 152699) (by norm_num)
theorem B1029797 : Blo 319836 1029797 := bbase (se 4 (by rfl) ⟨96543, by rfl⟩ : syracuseStep 1029797 = 193087) (by norm_num)
theorem B734933 : Blo 319836 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B341749 : Blo 319836 341749 := bbase (se 5 (by rfl) ⟨16019, by rfl⟩ : syracuseStep 341749 = 32039) (by norm_num)
theorem B341753 : Blo 319836 341753 := bbase (se 2 (by rfl) ⟨128157, by rfl⟩ : syracuseStep 341753 = 256315) (by norm_num)
theorem B407369 : Blo 319836 407369 := bbase (se 2 (by rfl) ⟨152763, by rfl⟩ : syracuseStep 407369 = 305527) (by norm_num)
theorem B407425 : Blo 319836 407425 := bbase (se 2 (by rfl) ⟨152784, by rfl⟩ : syracuseStep 407425 = 305569) (by norm_num)
theorem B407521 : Blo 319836 407521 := bbase (se 2 (by rfl) ⟨152820, by rfl⟩ : syracuseStep 407521 = 305641) (by norm_num)
theorem B407693 : Blo 319836 407693 := bbase (se 3 (by rfl) ⟨76442, by rfl⟩ : syracuseStep 407693 = 152885) (by norm_num)
theorem B2308277 : Blo 319836 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B407749 : Blo 319836 407749 := bbase (se 4 (by rfl) ⟨38226, by rfl⟩ : syracuseStep 407749 = 76453) (by norm_num)
theorem B735517 : Blo 319836 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B407845 : Blo 319836 407845 := bbase (se 4 (by rfl) ⟨38235, by rfl⟩ : syracuseStep 407845 = 76471) (by norm_num)
theorem B342317 : Blo 319836 342317 := bbase (se 3 (by rfl) ⟨64184, by rfl⟩ : syracuseStep 342317 = 128369) (by norm_num)
theorem B1161605 : Blo 319836 1161605 := bbase (se 4 (by rfl) ⟨108900, by rfl⟩ : syracuseStep 1161605 = 217801) (by norm_num)
theorem B408017 : Blo 319836 408017 := bbase (se 2 (by rfl) ⟨153006, by rfl⟩ : syracuseStep 408017 = 306013) (by norm_num)
theorem B342505 : Blo 319836 342505 := bbase (se 2 (by rfl) ⟨128439, by rfl⟩ : syracuseStep 342505 = 256879) (by norm_num)
theorem B1620485 : Blo 319836 1620485 := bbase (se 4 (by rfl) ⟨151920, by rfl⟩ : syracuseStep 1620485 = 303841) (by norm_num)
theorem B408073 : Blo 319836 408073 := bbase (se 2 (by rfl) ⟨153027, by rfl⟩ : syracuseStep 408073 = 306055) (by norm_num)
theorem B408169 : Blo 319836 408169 := bbase (se 2 (by rfl) ⟨153063, by rfl⟩ : syracuseStep 408169 = 306127) (by norm_num)
theorem B768629 : Blo 319836 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B768637 : Blo 319836 768637 := bbase (se 3 (by rfl) ⟨144119, by rfl⟩ : syracuseStep 768637 = 288239) (by norm_num)
theorem B408341 : Blo 319836 408341 := bbase (se 6 (by rfl) ⟨9570, by rfl⟩ : syracuseStep 408341 = 19141) (by norm_num)
theorem B408397 : Blo 319836 408397 := bbase (se 3 (by rfl) ⟨76574, by rfl⟩ : syracuseStep 408397 = 153149) (by norm_num)
theorem B1096597 : Blo 319836 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B408493 : Blo 319836 408493 := bbase (se 3 (by rfl) ⟨76592, by rfl⟩ : syracuseStep 408493 = 153185) (by norm_num)
theorem B408665 : Blo 319836 408665 := bbase (se 2 (by rfl) ⟨153249, by rfl⟩ : syracuseStep 408665 = 306499) (by norm_num)
theorem B408721 : Blo 319836 408721 := bbase (se 2 (by rfl) ⟨153270, by rfl⟩ : syracuseStep 408721 = 306541) (by norm_num)
theorem B539797 : Blo 319836 539797 := bbase (se 6 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 539797 = 25303) (by norm_num)
theorem B539885 : Blo 319836 539885 := bbase (se 3 (by rfl) ⟨101228, by rfl⟩ : syracuseStep 539885 = 202457) (by norm_num)
theorem B408817 : Blo 319836 408817 := bbase (se 2 (by rfl) ⟨153306, by rfl⟩ : syracuseStep 408817 = 306613) (by norm_num)
theorem B343325 : Blo 319836 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B540013 : Blo 319836 540013 := bbase (se 3 (by rfl) ⟨101252, by rfl⟩ : syracuseStep 540013 = 202505) (by norm_num)
theorem B408989 : Blo 319836 408989 := bbase (se 3 (by rfl) ⟨76685, by rfl⟩ : syracuseStep 408989 = 153371) (by norm_num)
theorem B736685 : Blo 319836 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B540101 : Blo 319836 540101 := bbase (se 4 (by rfl) ⟨50634, by rfl⟩ : syracuseStep 540101 = 101269) (by norm_num)
theorem B1228229 : Blo 319836 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B409045 : Blo 319836 409045 := bbase (se 7 (by rfl) ⟨4793, by rfl⟩ : syracuseStep 409045 = 9587) (by norm_num)
theorem B4439573 : Blo 319836 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B409141 : Blo 319836 409141 := bbase (se 5 (by rfl) ⟨19178, by rfl⟩ : syracuseStep 409141 = 38357) (by norm_num)
theorem B540229 : Blo 319836 540229 := bbase (se 4 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 540229 = 101293) (by norm_num)
theorem B769637 : Blo 319836 769637 := bbase (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) (by norm_num)
theorem B540317 : Blo 319836 540317 := bbase (se 3 (by rfl) ⟨101309, by rfl⟩ : syracuseStep 540317 = 202619) (by norm_num)
theorem B343769 : Blo 319836 343769 := bbase (se 2 (by rfl) ⟨128913, by rfl⟩ : syracuseStep 343769 = 257827) (by norm_num)
theorem B409313 : Blo 319836 409313 := bbase (se 2 (by rfl) ⟨153492, by rfl⟩ : syracuseStep 409313 = 306985) (by norm_num)
theorem B1228517 : Blo 319836 1228517 := bbase (se 4 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 1228517 = 230347) (by norm_num)
theorem B1621781 : Blo 319836 1621781 := bbase (se 6 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 1621781 = 76021) (by norm_num)
theorem B409369 : Blo 319836 409369 := bbase (se 2 (by rfl) ⟨153513, by rfl⟩ : syracuseStep 409369 = 307027) (by norm_num)
theorem B540445 : Blo 319836 540445 := bbase (se 3 (by rfl) ⟨101333, by rfl⟩ : syracuseStep 540445 = 202667) (by norm_num)
theorem B540533 : Blo 319836 540533 := bbase (se 5 (by rfl) ⟨25337, by rfl⟩ : syracuseStep 540533 = 50675) (by norm_num)
theorem B409465 : Blo 319836 409465 := bbase (se 2 (by rfl) ⟨153549, by rfl⟩ : syracuseStep 409465 = 307099) (by norm_num)
theorem B344017 : Blo 319836 344017 := bbase (se 2 (by rfl) ⟨129006, by rfl⟩ : syracuseStep 344017 = 258013) (by norm_num)
theorem B540661 : Blo 319836 540661 := bbase (se 5 (by rfl) ⟨25343, by rfl⟩ : syracuseStep 540661 = 50687) (by norm_num)
theorem B868373 : Blo 319836 868373 := bbase (se 6 (by rfl) ⟨20352, by rfl⟩ : syracuseStep 868373 = 40705) (by norm_num)
theorem B409637 : Blo 319836 409637 := bbase (se 4 (by rfl) ⟨38403, by rfl⟩ : syracuseStep 409637 = 76807) (by norm_num)
theorem B540749 : Blo 319836 540749 := bbase (se 3 (by rfl) ⟨101390, by rfl⟩ : syracuseStep 540749 = 202781) (by norm_num)
theorem B409693 : Blo 319836 409693 := bbase (se 3 (by rfl) ⟨76817, by rfl⟩ : syracuseStep 409693 = 153635) (by norm_num)
theorem B409789 : Blo 319836 409789 := bbase (se 3 (by rfl) ⟨76835, by rfl⟩ : syracuseStep 409789 = 153671) (by norm_num)
theorem B540877 : Blo 319836 540877 := bbase (se 3 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 540877 = 202829) (by norm_num)
theorem B540965 : Blo 319836 540965 := bbase (se 4 (by rfl) ⟨50715, by rfl⟩ : syracuseStep 540965 = 101431) (by norm_num)
theorem B770405 : Blo 319836 770405 := bbase (se 4 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 770405 = 144451) (by norm_num)
theorem B344449 : Blo 319836 344449 := bbase (se 2 (by rfl) ⟨129168, by rfl⟩ : syracuseStep 344449 = 258337) (by norm_num)
theorem B541093 : Blo 319836 541093 := bbase (se 4 (by rfl) ⟨50727, by rfl⟩ : syracuseStep 541093 = 101455) (by norm_num)
theorem B442813 : Blo 319836 442813 := bbase (se 3 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 442813 = 166055) (by norm_num)
theorem B344521 : Blo 319836 344521 := bbase (se 2 (by rfl) ⟨129195, by rfl⟩ : syracuseStep 344521 = 258391) (by norm_num)
theorem B541181 : Blo 319836 541181 := bbase (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) (by norm_num)
theorem B541309 : Blo 319836 541309 := bbase (se 3 (by rfl) ⟨101495, by rfl⟩ : syracuseStep 541309 = 202991) (by norm_num)
theorem B541397 : Blo 319836 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B344893 : Blo 319836 344893 := bbase (se 3 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 344893 = 129335) (by norm_num)
theorem B738109 : Blo 319836 738109 := bbase (se 3 (by rfl) ⟨138395, by rfl⟩ : syracuseStep 738109 = 276791) (by norm_num)
theorem B541525 : Blo 319836 541525 := bbase (se 9 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 541525 = 3173) (by norm_num)
theorem B541613 : Blo 319836 541613 := bbase (se 3 (by rfl) ⟨101552, by rfl⟩ : syracuseStep 541613 = 203105) (by norm_num)
theorem B1098677 : Blo 319836 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B1623077 : Blo 319836 1623077 := bbase (se 4 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 1623077 = 304327) (by norm_num)
theorem B967717 : Blo 319836 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B541741 : Blo 319836 541741 := bbase (se 3 (by rfl) ⟨101576, by rfl⟩ : syracuseStep 541741 = 203153) (by norm_num)
theorem B607333 : Blo 319836 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B541829 : Blo 319836 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B410773 : Blo 319836 410773 := bbase (se 6 (by rfl) ⟨9627, by rfl⟩ : syracuseStep 410773 = 19255) (by norm_num)
theorem B345269 : Blo 319836 345269 := bbase (se 5 (by rfl) ⟨16184, by rfl⟩ : syracuseStep 345269 = 32369) (by norm_num)
theorem B345341 : Blo 319836 345341 := bbase (se 3 (by rfl) ⟨64751, by rfl⟩ : syracuseStep 345341 = 129503) (by norm_num)
theorem B607493 : Blo 319836 607493 := bbase (se 4 (by rfl) ⟨56952, by rfl⟩ : syracuseStep 607493 = 113905) (by norm_num)
theorem B541957 : Blo 319836 541957 := bbase (se 4 (by rfl) ⟨50808, by rfl⟩ : syracuseStep 541957 = 101617) (by norm_num)
theorem B542045 : Blo 319836 542045 := bbase (se 3 (by rfl) ⟨101633, by rfl⟩ : syracuseStep 542045 = 203267) (by norm_num)
theorem B607637 : Blo 319836 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B345529 : Blo 319836 345529 := bbase (se 2 (by rfl) ⟨129573, by rfl⟩ : syracuseStep 345529 = 259147) (by norm_num)
theorem B1394117 : Blo 319836 1394117 := bbase (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) (by norm_num)
theorem B542173 : Blo 319836 542173 := bbase (se 3 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 542173 = 203315) (by norm_num)
theorem B1033717 : Blo 319836 1033717 := bbase (se 5 (by rfl) ⟨48455, by rfl⟩ : syracuseStep 1033717 = 96911) (by norm_num)
theorem B542261 : Blo 319836 542261 := bbase (se 5 (by rfl) ⟨25418, by rfl⟩ : syracuseStep 542261 = 50837) (by norm_num)
theorem B345713 : Blo 319836 345713 := bbase (se 2 (by rfl) ⟨129642, by rfl⟩ : syracuseStep 345713 = 259285) (by norm_num)
theorem B607925 : Blo 319836 607925 := bbase (se 5 (by rfl) ⟨28496, by rfl⟩ : syracuseStep 607925 = 56993) (by norm_num)
theorem B542389 : Blo 319836 542389 := bbase (se 5 (by rfl) ⟨25424, by rfl⟩ : syracuseStep 542389 = 50849) (by norm_num)
theorem B1033973 : Blo 319836 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B542477 : Blo 319836 542477 := bbase (se 3 (by rfl) ⟨101714, by rfl⟩ : syracuseStep 542477 = 203429) (by norm_num)
theorem B608077 : Blo 319836 608077 := bbase (se 3 (by rfl) ⟨114014, by rfl⟩ : syracuseStep 608077 = 228029) (by norm_num)
theorem B542605 : Blo 319836 542605 := bbase (se 3 (by rfl) ⟨101738, by rfl⟩ : syracuseStep 542605 = 203477) (by norm_num)
theorem B542693 : Blo 319836 542693 := bbase (se 4 (by rfl) ⟨50877, by rfl⟩ : syracuseStep 542693 = 101755) (by norm_num)
theorem B4769813 : Blo 319836 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B542821 : Blo 319836 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B772213 : Blo 319836 772213 := bbase (se 5 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 772213 = 72395) (by norm_num)
theorem B608381 : Blo 319836 608381 := bbase (se 3 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 608381 = 228143) (by norm_num)
theorem B1230997 : Blo 319836 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B542909 : Blo 319836 542909 := bbase (se 3 (by rfl) ⟨101795, by rfl⟩ : syracuseStep 542909 = 203591) (by norm_num)
theorem B1624373 : Blo 319836 1624373 := bbase (se 5 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 1624373 = 152285) (by norm_num)
theorem B543037 : Blo 319836 543037 := bbase (se 3 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 543037 = 203639) (by norm_num)
theorem B543125 : Blo 319836 543125 := bbase (se 6 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 543125 = 25459) (by norm_num)
theorem B1100213 : Blo 319836 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B543253 : Blo 319836 543253 := bbase (se 6 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 543253 = 25465) (by norm_num)
theorem B543341 : Blo 319836 543341 := bbase (se 3 (by rfl) ⟨101876, by rfl⟩ : syracuseStep 543341 = 203753) (by norm_num)
theorem B772733 : Blo 319836 772733 := bbase (se 3 (by rfl) ⟨144887, by rfl⟩ : syracuseStep 772733 = 289775) (by norm_num)
theorem B543469 : Blo 319836 543469 := bbase (se 3 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 543469 = 203801) (by norm_num)
theorem B1297205 : Blo 319836 1297205 := bbase (se 5 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 1297205 = 121613) (by norm_num)
theorem B543557 : Blo 319836 543557 := bbase (se 4 (by rfl) ⟨50958, by rfl⟩ : syracuseStep 543557 = 101917) (by norm_num)
theorem B609133 : Blo 319836 609133 := bbase (se 3 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 609133 = 228425) (by norm_num)
theorem B543685 : Blo 319836 543685 := bbase (se 4 (by rfl) ⟨50970, by rfl⟩ : syracuseStep 543685 = 101941) (by norm_num)
theorem B2870261 : Blo 319836 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B609277 : Blo 319836 609277 := bbase (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) (by norm_num)
theorem B773117 : Blo 319836 773117 := bbase (se 3 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 773117 = 289919) (by norm_num)
theorem B543773 : Blo 319836 543773 := bbase (se 3 (by rfl) ⟨101957, by rfl⟩ : syracuseStep 543773 = 203915) (by norm_num)
theorem B773165 : Blo 319836 773165 := bbase (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) (by norm_num)
theorem B773173 : Blo 319836 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B609437 : Blo 319836 609437 := bbase (se 3 (by rfl) ⟨114269, by rfl⟩ : syracuseStep 609437 = 228539) (by norm_num)
theorem B543901 : Blo 319836 543901 := bbase (se 3 (by rfl) ⟨101981, by rfl⟩ : syracuseStep 543901 = 203963) (by norm_num)
theorem B543989 : Blo 319836 543989 := bbase (se 5 (by rfl) ⟨25499, by rfl⟩ : syracuseStep 543989 = 50999) (by norm_num)
theorem B609581 : Blo 319836 609581 := bbase (se 3 (by rfl) ⟨114296, by rfl⟩ : syracuseStep 609581 = 228593) (by norm_num)
theorem B544117 : Blo 319836 544117 := bbase (se 5 (by rfl) ⟨25505, by rfl⟩ : syracuseStep 544117 = 51011) (by norm_num)
theorem B544205 : Blo 319836 544205 := bbase (se 3 (by rfl) ⟨102038, by rfl⟩ : syracuseStep 544205 = 204077) (by norm_num)
theorem B871973 : Blo 319836 871973 := bbase (se 4 (by rfl) ⟨81747, by rfl⟩ : syracuseStep 871973 = 163495) (by norm_num)
theorem B1625669 : Blo 319836 1625669 := bbase (se 4 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 1625669 = 304813) (by norm_num)
theorem B609869 : Blo 319836 609869 := bbase (se 3 (by rfl) ⟨114350, by rfl⟩ : syracuseStep 609869 = 228701) (by norm_num)
theorem B544333 : Blo 319836 544333 := bbase (se 3 (by rfl) ⟨102062, by rfl⟩ : syracuseStep 544333 = 204125) (by norm_num)
theorem B413273 : Blo 319836 413273 := bbase (se 2 (by rfl) ⟨154977, by rfl⟩ : syracuseStep 413273 = 309955) (by norm_num)
theorem B544421 : Blo 319836 544421 := bbase (se 4 (by rfl) ⟨51039, by rfl⟩ : syracuseStep 544421 = 102079) (by norm_num)
theorem B2215637 : Blo 319836 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B610021 : Blo 319836 610021 := bbase (se 4 (by rfl) ⟨57189, by rfl⟩ : syracuseStep 610021 = 114379) (by norm_num)
theorem B544549 : Blo 319836 544549 := bbase (se 4 (by rfl) ⟨51051, by rfl⟩ : syracuseStep 544549 = 102103) (by norm_num)
theorem B544637 : Blo 319836 544637 := bbase (se 3 (by rfl) ⟨102119, by rfl⟩ : syracuseStep 544637 = 204239) (by norm_num)
theorem B544765 : Blo 319836 544765 := bbase (se 3 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 544765 = 204287) (by norm_num)
theorem B610325 : Blo 319836 610325 := bbase (se 6 (by rfl) ⟨14304, by rfl⟩ : syracuseStep 610325 = 28609) (by norm_num)
theorem B774173 : Blo 319836 774173 := bbase (se 3 (by rfl) ⟨145157, by rfl⟩ : syracuseStep 774173 = 290315) (by norm_num)
theorem B577573 : Blo 319836 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B544853 : Blo 319836 544853 := bbase (se 8 (by rfl) ⟨3192, by rfl⟩ : syracuseStep 544853 = 6385) (by norm_num)
theorem B544981 : Blo 319836 544981 := bbase (se 7 (by rfl) ⟨6386, by rfl⟩ : syracuseStep 544981 = 12773) (by norm_num)
theorem B774365 : Blo 319836 774365 := bbase (se 3 (by rfl) ⟨145193, by rfl⟩ : syracuseStep 774365 = 290387) (by norm_num)
theorem B545069 : Blo 319836 545069 := bbase (se 3 (by rfl) ⟨102200, by rfl⟩ : syracuseStep 545069 = 204401) (by norm_num)
theorem B1823093 : Blo 319836 1823093 := bbase (se 5 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 1823093 = 170915) (by norm_num)
theorem B545197 : Blo 319836 545197 := bbase (se 3 (by rfl) ⟨102224, by rfl⟩ : syracuseStep 545197 = 204449) (by norm_num)
theorem B1036741 : Blo 319836 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B578029 : Blo 319836 578029 := bbase (se 3 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 578029 = 216761) (by norm_num)
theorem B545285 : Blo 319836 545285 := bbase (se 4 (by rfl) ⟨51120, by rfl⟩ : syracuseStep 545285 = 102241) (by norm_num)
theorem B479765 : Blo 319836 479765 := bbase (se 6 (by rfl) ⟨11244, by rfl⟩ : syracuseStep 479765 = 22489) (by norm_num)
theorem B479789 : Blo 319836 479789 := bbase (se 3 (by rfl) ⟨89960, by rfl⟩ : syracuseStep 479789 = 179921) (by norm_num)
theorem B479813 : Blo 319836 479813 := bbase (se 4 (by rfl) ⟨44982, by rfl⟩ : syracuseStep 479813 = 89965) (by norm_num)
theorem B479837 : Blo 319836 479837 := bbase (se 3 (by rfl) ⟨89969, by rfl⟩ : syracuseStep 479837 = 179939) (by norm_num)
theorem B479861 : Blo 319836 479861 := bbase (se 5 (by rfl) ⟨22493, by rfl⟩ : syracuseStep 479861 = 44987) (by norm_num)
theorem B545413 : Blo 319836 545413 := bbase (se 4 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 545413 = 102265) (by norm_num)
theorem B479885 : Blo 319836 479885 := bbase (se 3 (by rfl) ⟨89978, by rfl⟩ : syracuseStep 479885 = 179957) (by norm_num)
theorem B479909 : Blo 319836 479909 := bbase (se 4 (by rfl) ⟨44991, by rfl⟩ : syracuseStep 479909 = 89983) (by norm_num)
theorem B479933 : Blo 319836 479933 := bbase (se 3 (by rfl) ⟨89987, by rfl⟩ : syracuseStep 479933 = 179975) (by norm_num)
theorem B479957 : Blo 319836 479957 := bbase (se 7 (by rfl) ⟨5624, by rfl⟩ : syracuseStep 479957 = 11249) (by norm_num)
theorem B2446037 : Blo 319836 2446037 := bbase (se 7 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 2446037 = 57329) (by norm_num)
theorem B545501 : Blo 319836 545501 := bbase (se 3 (by rfl) ⟨102281, by rfl⟩ : syracuseStep 545501 = 204563) (by norm_num)
theorem B479981 : Blo 319836 479981 := bbase (se 3 (by rfl) ⟨89996, by rfl⟩ : syracuseStep 479981 = 179993) (by norm_num)
theorem B480005 : Blo 319836 480005 := bbase (se 4 (by rfl) ⟨45000, by rfl⟩ : syracuseStep 480005 = 90001) (by norm_num)
theorem B611077 : Blo 319836 611077 := bbase (se 4 (by rfl) ⟨57288, by rfl⟩ : syracuseStep 611077 = 114577) (by norm_num)
theorem B480029 : Blo 319836 480029 := bbase (se 3 (by rfl) ⟨90005, by rfl⟩ : syracuseStep 480029 = 180011) (by norm_num)
theorem B480053 : Blo 319836 480053 := bbase (se 5 (by rfl) ⟨22502, by rfl⟩ : syracuseStep 480053 = 45005) (by norm_num)
theorem B480077 : Blo 319836 480077 := bbase (se 3 (by rfl) ⟨90014, by rfl⟩ : syracuseStep 480077 = 180029) (by norm_num)
theorem B1626965 : Blo 319836 1626965 := bbase (se 9 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 1626965 = 9533) (by norm_num)
theorem B545629 : Blo 319836 545629 := bbase (se 3 (by rfl) ⟨102305, by rfl⟩ : syracuseStep 545629 = 204611) (by norm_num)
theorem B480101 : Blo 319836 480101 := bbase (se 4 (by rfl) ⟨45009, by rfl⟩ : syracuseStep 480101 = 90019) (by norm_num)
theorem B480125 : Blo 319836 480125 := bbase (se 3 (by rfl) ⟨90023, by rfl⟩ : syracuseStep 480125 = 180047) (by norm_num)
theorem B480149 : Blo 319836 480149 := bbase (se 6 (by rfl) ⟨11253, by rfl⟩ : syracuseStep 480149 = 22507) (by norm_num)
theorem B611221 : Blo 319836 611221 := bbase (se 6 (by rfl) ⟨14325, by rfl⟩ : syracuseStep 611221 = 28651) (by norm_num)
theorem B480173 : Blo 319836 480173 := bbase (se 3 (by rfl) ⟨90032, by rfl⟩ : syracuseStep 480173 = 180065) (by norm_num)
theorem B545717 : Blo 319836 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B480197 : Blo 319836 480197 := bbase (se 4 (by rfl) ⟨45018, by rfl⟩ : syracuseStep 480197 = 90037) (by norm_num)
theorem B480221 : Blo 319836 480221 := bbase (se 3 (by rfl) ⟨90041, by rfl⟩ : syracuseStep 480221 = 180083) (by norm_num)
theorem B480245 : Blo 319836 480245 := bbase (se 5 (by rfl) ⟨22511, by rfl⟩ : syracuseStep 480245 = 45023) (by norm_num)
theorem B480269 : Blo 319836 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B480293 : Blo 319836 480293 := bbase (se 4 (by rfl) ⟨45027, by rfl⟩ : syracuseStep 480293 = 90055) (by norm_num)
theorem B611381 : Blo 319836 611381 := bbase (se 5 (by rfl) ⟨28658, by rfl⟩ : syracuseStep 611381 = 57317) (by norm_num)
theorem B545845 : Blo 319836 545845 := bbase (se 5 (by rfl) ⟨25586, by rfl⟩ : syracuseStep 545845 = 51173) (by norm_num)
theorem B480317 : Blo 319836 480317 := bbase (se 3 (by rfl) ⟨90059, by rfl⟩ : syracuseStep 480317 = 180119) (by norm_num)
theorem B480341 : Blo 319836 480341 := bbase (se 8 (by rfl) ⟨2814, by rfl⟩ : syracuseStep 480341 = 5629) (by norm_num)
theorem B480365 : Blo 319836 480365 := bbase (se 3 (by rfl) ⟨90068, by rfl⟩ : syracuseStep 480365 = 180137) (by norm_num)
theorem B480389 : Blo 319836 480389 := bbase (se 4 (by rfl) ⟨45036, by rfl⟩ : syracuseStep 480389 = 90073) (by norm_num)
theorem B545933 : Blo 319836 545933 := bbase (se 3 (by rfl) ⟨102362, by rfl⟩ : syracuseStep 545933 = 204725) (by norm_num)
theorem B480413 : Blo 319836 480413 := bbase (se 3 (by rfl) ⟨90077, by rfl⟩ : syracuseStep 480413 = 180155) (by norm_num)
theorem B480437 : Blo 319836 480437 := bbase (se 5 (by rfl) ⟨22520, by rfl⟩ : syracuseStep 480437 = 45041) (by norm_num)
theorem B611525 : Blo 319836 611525 := bbase (se 4 (by rfl) ⟨57330, by rfl⟩ : syracuseStep 611525 = 114661) (by norm_num)
theorem B480461 : Blo 319836 480461 := bbase (se 3 (by rfl) ⟨90086, by rfl⟩ : syracuseStep 480461 = 180173) (by norm_num)
theorem B513245 : Blo 319836 513245 := bbase (se 3 (by rfl) ⟨96233, by rfl⟩ : syracuseStep 513245 = 192467) (by norm_num)
theorem B480485 : Blo 319836 480485 := bbase (se 4 (by rfl) ⟨45045, by rfl⟩ : syracuseStep 480485 = 90091) (by norm_num)
theorem B480509 : Blo 319836 480509 := bbase (se 3 (by rfl) ⟨90095, by rfl⟩ : syracuseStep 480509 = 180191) (by norm_num)
theorem B546061 : Blo 319836 546061 := bbase (se 3 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 546061 = 204773) (by norm_num)
theorem B480533 : Blo 319836 480533 := bbase (se 6 (by rfl) ⟨11262, by rfl⟩ : syracuseStep 480533 = 22525) (by norm_num)
theorem B480557 : Blo 319836 480557 := bbase (se 3 (by rfl) ⟨90104, by rfl⟩ : syracuseStep 480557 = 180209) (by norm_num)
theorem B480581 : Blo 319836 480581 := bbase (se 4 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 480581 = 90109) (by norm_num)
theorem B480605 : Blo 319836 480605 := bbase (se 3 (by rfl) ⟨90113, by rfl⟩ : syracuseStep 480605 = 180227) (by norm_num)
theorem B513373 : Blo 319836 513373 := bbase (se 3 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 513373 = 192515) (by norm_num)
theorem B546149 : Blo 319836 546149 := bbase (se 4 (by rfl) ⟨51201, by rfl⟩ : syracuseStep 546149 = 102403) (by norm_num)
theorem B480629 : Blo 319836 480629 := bbase (se 5 (by rfl) ⟨22529, by rfl⟩ : syracuseStep 480629 = 45059) (by norm_num)
theorem B480653 : Blo 319836 480653 := bbase (se 3 (by rfl) ⟨90122, by rfl⟩ : syracuseStep 480653 = 180245) (by norm_num)
theorem B578957 : Blo 319836 578957 := bbase (se 3 (by rfl) ⟨108554, by rfl⟩ : syracuseStep 578957 = 217109) (by norm_num)
theorem B480677 : Blo 319836 480677 := bbase (se 4 (by rfl) ⟨45063, by rfl⟩ : syracuseStep 480677 = 90127) (by norm_num)
theorem B480701 : Blo 319836 480701 := bbase (se 3 (by rfl) ⟨90131, by rfl⟩ : syracuseStep 480701 = 180263) (by norm_num)
theorem B480725 : Blo 319836 480725 := bbase (se 7 (by rfl) ⟨5633, by rfl⟩ : syracuseStep 480725 = 11267) (by norm_num)
theorem B611813 : Blo 319836 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B546277 : Blo 319836 546277 := bbase (se 4 (by rfl) ⟨51213, by rfl⟩ : syracuseStep 546277 = 102427) (by norm_num)
theorem B480749 : Blo 319836 480749 := bbase (se 3 (by rfl) ⟨90140, by rfl⟩ : syracuseStep 480749 = 180281) (by norm_num)
theorem B480773 : Blo 319836 480773 := bbase (se 4 (by rfl) ⟨45072, by rfl⟩ : syracuseStep 480773 = 90145) (by norm_num)
theorem B480797 : Blo 319836 480797 := bbase (se 3 (by rfl) ⟨90149, by rfl⟩ : syracuseStep 480797 = 180299) (by norm_num)
theorem B480821 : Blo 319836 480821 := bbase (se 5 (by rfl) ⟨22538, by rfl⟩ : syracuseStep 480821 = 45077) (by norm_num)
theorem B579125 : Blo 319836 579125 := bbase (se 5 (by rfl) ⟨27146, by rfl⟩ : syracuseStep 579125 = 54293) (by norm_num)
theorem B546365 : Blo 319836 546365 := bbase (se 3 (by rfl) ⟨102443, by rfl⟩ : syracuseStep 546365 = 204887) (by norm_num)
theorem B480845 : Blo 319836 480845 := bbase (se 3 (by rfl) ⟨90158, by rfl⟩ : syracuseStep 480845 = 180317) (by norm_num)
theorem B480869 : Blo 319836 480869 := bbase (se 4 (by rfl) ⟨45081, by rfl⟩ : syracuseStep 480869 = 90163) (by norm_num)
theorem B480893 : Blo 319836 480893 := bbase (se 3 (by rfl) ⟨90167, by rfl⟩ : syracuseStep 480893 = 180335) (by norm_num)
theorem B611965 : Blo 319836 611965 := bbase (se 3 (by rfl) ⟨114743, by rfl⟩ : syracuseStep 611965 = 229487) (by norm_num)
theorem B480917 : Blo 319836 480917 := bbase (se 6 (by rfl) ⟨11271, by rfl⟩ : syracuseStep 480917 = 22543) (by norm_num)
theorem B480941 : Blo 319836 480941 := bbase (se 3 (by rfl) ⟨90176, by rfl⟩ : syracuseStep 480941 = 180353) (by norm_num)
theorem B480965 : Blo 319836 480965 := bbase (se 4 (by rfl) ⟨45090, by rfl⟩ : syracuseStep 480965 = 90181) (by norm_num)
theorem B480989 : Blo 319836 480989 := bbase (se 3 (by rfl) ⟨90185, by rfl⟩ : syracuseStep 480989 = 180371) (by norm_num)
theorem B481013 : Blo 319836 481013 := bbase (se 5 (by rfl) ⟨22547, by rfl⟩ : syracuseStep 481013 = 45095) (by norm_num)
theorem B481037 : Blo 319836 481037 := bbase (se 3 (by rfl) ⟨90194, by rfl⟩ : syracuseStep 481037 = 180389) (by norm_num)
theorem B481061 : Blo 319836 481061 := bbase (se 4 (by rfl) ⟨45099, by rfl⟩ : syracuseStep 481061 = 90199) (by norm_num)
theorem B874277 : Blo 319836 874277 := bbase (se 4 (by rfl) ⟨81963, by rfl⟩ : syracuseStep 874277 = 163927) (by norm_num)
theorem B481085 : Blo 319836 481085 := bbase (se 3 (by rfl) ⟨90203, by rfl⟩ : syracuseStep 481085 = 180407) (by norm_num)
theorem B481109 : Blo 319836 481109 := bbase (se 9 (by rfl) ⟨1409, by rfl⟩ : syracuseStep 481109 = 2819) (by norm_num)
theorem B579413 : Blo 319836 579413 := bbase (se 9 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 579413 = 3395) (by norm_num)
theorem B481133 : Blo 319836 481133 := bbase (se 3 (by rfl) ⟨90212, by rfl⟩ : syracuseStep 481133 = 180425) (by norm_num)
theorem B481157 : Blo 319836 481157 := bbase (se 4 (by rfl) ⟨45108, by rfl⟩ : syracuseStep 481157 = 90217) (by norm_num)
theorem B481181 : Blo 319836 481181 := bbase (se 3 (by rfl) ⟨90221, by rfl⟩ : syracuseStep 481181 = 180443) (by norm_num)
theorem B874405 : Blo 319836 874405 := bbase (se 4 (by rfl) ⟨81975, by rfl⟩ : syracuseStep 874405 = 163951) (by norm_num)
theorem B612269 : Blo 319836 612269 := bbase (se 3 (by rfl) ⟨114800, by rfl⟩ : syracuseStep 612269 = 229601) (by norm_num)
theorem B481205 : Blo 319836 481205 := bbase (se 5 (by rfl) ⟨22556, by rfl⟩ : syracuseStep 481205 = 45113) (by norm_num)
theorem B1103813 : Blo 319836 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B481229 : Blo 319836 481229 := bbase (se 3 (by rfl) ⟨90230, by rfl⟩ : syracuseStep 481229 = 180461) (by norm_num)
theorem B481253 : Blo 319836 481253 := bbase (se 4 (by rfl) ⟨45117, by rfl⟩ : syracuseStep 481253 = 90235) (by norm_num)
theorem B481277 : Blo 319836 481277 := bbase (se 3 (by rfl) ⟨90239, by rfl⟩ : syracuseStep 481277 = 180479) (by norm_num)
theorem B481301 : Blo 319836 481301 := bbase (se 6 (by rfl) ⟨11280, by rfl⟩ : syracuseStep 481301 = 22561) (by norm_num)
theorem B481325 : Blo 319836 481325 := bbase (se 3 (by rfl) ⟨90248, by rfl⟩ : syracuseStep 481325 = 180497) (by norm_num)
theorem B481349 : Blo 319836 481349 := bbase (se 4 (by rfl) ⟨45126, by rfl⟩ : syracuseStep 481349 = 90253) (by norm_num)
theorem B481373 : Blo 319836 481373 := bbase (se 3 (by rfl) ⟨90257, by rfl⟩ : syracuseStep 481373 = 180515) (by norm_num)
theorem B1628261 : Blo 319836 1628261 := bbase (se 4 (by rfl) ⟨152649, by rfl⟩ : syracuseStep 1628261 = 305299) (by norm_num)
theorem B2054261 : Blo 319836 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B481397 : Blo 319836 481397 := bbase (se 5 (by rfl) ⟨22565, by rfl⟩ : syracuseStep 481397 = 45131) (by norm_num)
theorem B776317 : Blo 319836 776317 := bbase (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) (by norm_num)
theorem B514181 : Blo 319836 514181 := bbase (se 4 (by rfl) ⟨48204, by rfl⟩ : syracuseStep 514181 = 96409) (by norm_num)
theorem B481421 : Blo 319836 481421 := bbase (se 3 (by rfl) ⟨90266, by rfl⟩ : syracuseStep 481421 = 180533) (by norm_num)
theorem B481445 : Blo 319836 481445 := bbase (se 4 (by rfl) ⟨45135, by rfl⟩ : syracuseStep 481445 = 90271) (by norm_num)
theorem B481469 : Blo 319836 481469 := bbase (se 3 (by rfl) ⟨90275, by rfl⟩ : syracuseStep 481469 = 180551) (by norm_num)
theorem B1300693 : Blo 319836 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B481493 : Blo 319836 481493 := bbase (se 7 (by rfl) ⟨5642, by rfl⟩ : syracuseStep 481493 = 11285) (by norm_num)
theorem B481517 : Blo 319836 481517 := bbase (se 3 (by rfl) ⟨90284, by rfl⟩ : syracuseStep 481517 = 180569) (by norm_num)
theorem B874741 : Blo 319836 874741 := bbase (se 5 (by rfl) ⟨41003, by rfl⟩ : syracuseStep 874741 = 82007) (by norm_num)
theorem B481541 : Blo 319836 481541 := bbase (se 4 (by rfl) ⟨45144, by rfl⟩ : syracuseStep 481541 = 90289) (by norm_num)
theorem B481565 : Blo 319836 481565 := bbase (se 3 (by rfl) ⟨90293, by rfl⟩ : syracuseStep 481565 = 180587) (by norm_num)
theorem B481589 : Blo 319836 481589 := bbase (se 5 (by rfl) ⟨22574, by rfl⟩ : syracuseStep 481589 = 45149) (by norm_num)
theorem B481613 : Blo 319836 481613 := bbase (se 3 (by rfl) ⟨90302, by rfl⟩ : syracuseStep 481613 = 180605) (by norm_num)
theorem B481637 : Blo 319836 481637 := bbase (se 4 (by rfl) ⟨45153, by rfl⟩ : syracuseStep 481637 = 90307) (by norm_num)
theorem B481661 : Blo 319836 481661 := bbase (se 3 (by rfl) ⟨90311, by rfl⟩ : syracuseStep 481661 = 180623) (by norm_num)
theorem B481685 : Blo 319836 481685 := bbase (se 6 (by rfl) ⟨11289, by rfl⟩ : syracuseStep 481685 = 22579) (by norm_num)
theorem B514469 : Blo 319836 514469 := bbase (se 4 (by rfl) ⟨48231, by rfl⟩ : syracuseStep 514469 = 96463) (by norm_num)
theorem B481709 : Blo 319836 481709 := bbase (se 3 (by rfl) ⟨90320, by rfl⟩ : syracuseStep 481709 = 180641) (by norm_num)
theorem B481733 : Blo 319836 481733 := bbase (se 4 (by rfl) ⟨45162, by rfl⟩ : syracuseStep 481733 = 90325) (by norm_num)
theorem B481757 : Blo 319836 481757 := bbase (se 3 (by rfl) ⟨90329, by rfl⟩ : syracuseStep 481757 = 180659) (by norm_num)
theorem B481781 : Blo 319836 481781 := bbase (se 5 (by rfl) ⟨22583, by rfl⟩ : syracuseStep 481781 = 45167) (by norm_num)
theorem B481805 : Blo 319836 481805 := bbase (se 3 (by rfl) ⟨90338, by rfl⟩ : syracuseStep 481805 = 180677) (by norm_num)
theorem B481829 : Blo 319836 481829 := bbase (se 4 (by rfl) ⟨45171, by rfl⟩ : syracuseStep 481829 = 90343) (by norm_num)
theorem B481853 : Blo 319836 481853 := bbase (se 3 (by rfl) ⟨90347, by rfl⟩ : syracuseStep 481853 = 180695) (by norm_num)
theorem B481877 : Blo 319836 481877 := bbase (se 8 (by rfl) ⟨2823, by rfl⟩ : syracuseStep 481877 = 5647) (by norm_num)
theorem B481901 : Blo 319836 481901 := bbase (se 3 (by rfl) ⟨90356, by rfl⟩ : syracuseStep 481901 = 180713) (by norm_num)
theorem B481925 : Blo 319836 481925 := bbase (se 4 (by rfl) ⟨45180, by rfl⟩ : syracuseStep 481925 = 90361) (by norm_num)
theorem B481949 : Blo 319836 481949 := bbase (se 3 (by rfl) ⟨90365, by rfl⟩ : syracuseStep 481949 = 180731) (by norm_num)
theorem B613021 : Blo 319836 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B481973 : Blo 319836 481973 := bbase (se 5 (by rfl) ⟨22592, by rfl⟩ : syracuseStep 481973 = 45185) (by norm_num)
theorem B481997 : Blo 319836 481997 := bbase (se 3 (by rfl) ⟨90374, by rfl⟩ : syracuseStep 481997 = 180749) (by norm_num)
theorem B482021 : Blo 319836 482021 := bbase (se 4 (by rfl) ⟨45189, by rfl⟩ : syracuseStep 482021 = 90379) (by norm_num)
theorem B482045 : Blo 319836 482045 := bbase (se 3 (by rfl) ⟨90383, by rfl⟩ : syracuseStep 482045 = 180767) (by norm_num)
theorem B482069 : Blo 319836 482069 := bbase (se 6 (by rfl) ⟨11298, by rfl⟩ : syracuseStep 482069 = 22597) (by norm_num)
theorem B482093 : Blo 319836 482093 := bbase (se 3 (by rfl) ⟨90392, by rfl⟩ : syracuseStep 482093 = 180785) (by norm_num)
theorem B613165 : Blo 319836 613165 := bbase (se 3 (by rfl) ⟨114968, by rfl⟩ : syracuseStep 613165 = 229937) (by norm_num)
theorem B809797 : Blo 319836 809797 := bbase (se 4 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 809797 = 151837) (by norm_num)
theorem B482117 : Blo 319836 482117 := bbase (se 4 (by rfl) ⟨45198, by rfl⟩ : syracuseStep 482117 = 90397) (by norm_num)
theorem B514885 : Blo 319836 514885 := bbase (se 4 (by rfl) ⟨48270, by rfl⟩ : syracuseStep 514885 = 96541) (by norm_num)
theorem B482141 : Blo 319836 482141 := bbase (se 3 (by rfl) ⟨90401, by rfl⟩ : syracuseStep 482141 = 180803) (by norm_num)
theorem B482165 : Blo 319836 482165 := bbase (se 5 (by rfl) ⟨22601, by rfl⟩ : syracuseStep 482165 = 45203) (by norm_num)
theorem B482189 : Blo 319836 482189 := bbase (se 3 (by rfl) ⟨90410, by rfl⟩ : syracuseStep 482189 = 180821) (by norm_num)
theorem B482213 : Blo 319836 482213 := bbase (se 4 (by rfl) ⟨45207, by rfl⟩ : syracuseStep 482213 = 90415) (by norm_num)
theorem B809909 : Blo 319836 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B482237 : Blo 319836 482237 := bbase (se 3 (by rfl) ⟨90419, by rfl⟩ : syracuseStep 482237 = 180839) (by norm_num)
theorem B613325 : Blo 319836 613325 := bbase (se 3 (by rfl) ⟨114998, by rfl⟩ : syracuseStep 613325 = 229997) (by norm_num)
theorem B482261 : Blo 319836 482261 := bbase (se 7 (by rfl) ⟨5651, by rfl⟩ : syracuseStep 482261 = 11303) (by norm_num)
theorem B482285 : Blo 319836 482285 := bbase (se 3 (by rfl) ⟨90428, by rfl⟩ : syracuseStep 482285 = 180857) (by norm_num)
theorem B973829 : Blo 319836 973829 := bbase (se 4 (by rfl) ⟨91296, by rfl⟩ : syracuseStep 973829 = 182593) (by norm_num)
theorem B482309 : Blo 319836 482309 := bbase (se 4 (by rfl) ⟨45216, by rfl⟩ : syracuseStep 482309 = 90433) (by norm_num)
theorem B482333 : Blo 319836 482333 := bbase (se 3 (by rfl) ⟨90437, by rfl⟩ : syracuseStep 482333 = 180875) (by norm_num)
theorem B580645 : Blo 319836 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B482357 : Blo 319836 482357 := bbase (se 5 (by rfl) ⟨22610, by rfl⟩ : syracuseStep 482357 = 45221) (by norm_num)
theorem B777269 : Blo 319836 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B482381 : Blo 319836 482381 := bbase (se 3 (by rfl) ⟨90446, by rfl⟩ : syracuseStep 482381 = 180893) (by norm_num)
theorem B613469 : Blo 319836 613469 := bbase (se 3 (by rfl) ⟨115025, by rfl⟩ : syracuseStep 613469 = 230051) (by norm_num)
theorem B482405 : Blo 319836 482405 := bbase (se 4 (by rfl) ⟨45225, by rfl⟩ : syracuseStep 482405 = 90451) (by norm_num)
theorem B580717 : Blo 319836 580717 := bbase (se 3 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 580717 = 217769) (by norm_num)
theorem B777325 : Blo 319836 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B810101 : Blo 319836 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B482429 : Blo 319836 482429 := bbase (se 3 (by rfl) ⟨90455, by rfl⟩ : syracuseStep 482429 = 180911) (by norm_num)
theorem B482453 : Blo 319836 482453 := bbase (se 6 (by rfl) ⟨11307, by rfl⟩ : syracuseStep 482453 = 22615) (by norm_num)
theorem B482477 : Blo 319836 482477 := bbase (se 3 (by rfl) ⟨90464, by rfl⟩ : syracuseStep 482477 = 180929) (by norm_num)
theorem B482501 : Blo 319836 482501 := bbase (se 4 (by rfl) ⟨45234, by rfl⟩ : syracuseStep 482501 = 90469) (by norm_num)
theorem B482525 : Blo 319836 482525 := bbase (se 3 (by rfl) ⟨90473, by rfl⟩ : syracuseStep 482525 = 180947) (by norm_num)
theorem B482549 : Blo 319836 482549 := bbase (se 5 (by rfl) ⟨22619, by rfl⟩ : syracuseStep 482549 = 45239) (by norm_num)
theorem B580861 : Blo 319836 580861 := bbase (se 3 (by rfl) ⟨108911, by rfl⟩ : syracuseStep 580861 = 217823) (by norm_num)
theorem B482573 : Blo 319836 482573 := bbase (se 3 (by rfl) ⟨90482, by rfl⟩ : syracuseStep 482573 = 180965) (by norm_num)
theorem B482597 : Blo 319836 482597 := bbase (se 4 (by rfl) ⟨45243, by rfl⟩ : syracuseStep 482597 = 90487) (by norm_num)
theorem B482621 : Blo 319836 482621 := bbase (se 3 (by rfl) ⟨90491, by rfl⟩ : syracuseStep 482621 = 180983) (by norm_num)
theorem B482645 : Blo 319836 482645 := bbase (se 11 (by rfl) ⟨353, by rfl⟩ : syracuseStep 482645 = 707) (by norm_num)
theorem B482669 : Blo 319836 482669 := bbase (se 3 (by rfl) ⟨90500, by rfl⟩ : syracuseStep 482669 = 181001) (by norm_num)
theorem B1629557 : Blo 319836 1629557 := bbase (se 5 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 1629557 = 152771) (by norm_num)
theorem B613757 : Blo 319836 613757 := bbase (se 3 (by rfl) ⟨115079, by rfl⟩ : syracuseStep 613757 = 230159) (by norm_num)
theorem B482693 : Blo 319836 482693 := bbase (se 4 (by rfl) ⟨45252, by rfl⟩ : syracuseStep 482693 = 90505) (by norm_num)
theorem B482717 : Blo 319836 482717 := bbase (se 3 (by rfl) ⟨90509, by rfl⟩ : syracuseStep 482717 = 181019) (by norm_num)
theorem B482741 : Blo 319836 482741 := bbase (se 5 (by rfl) ⟨22628, by rfl⟩ : syracuseStep 482741 = 45257) (by norm_num)
theorem B810445 : Blo 319836 810445 := bbase (se 3 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 810445 = 303917) (by norm_num)
theorem B482765 : Blo 319836 482765 := bbase (se 3 (by rfl) ⟨90518, by rfl⟩ : syracuseStep 482765 = 181037) (by norm_num)
theorem B482789 : Blo 319836 482789 := bbase (se 4 (by rfl) ⟨45261, by rfl⟩ : syracuseStep 482789 = 90523) (by norm_num)
theorem B777701 : Blo 319836 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B482813 : Blo 319836 482813 := bbase (se 3 (by rfl) ⟨90527, by rfl⟩ : syracuseStep 482813 = 181055) (by norm_num)
theorem B482837 : Blo 319836 482837 := bbase (se 6 (by rfl) ⟨11316, by rfl⟩ : syracuseStep 482837 = 22633) (by norm_num)
theorem B613909 : Blo 319836 613909 := bbase (se 6 (by rfl) ⟨14388, by rfl⟩ : syracuseStep 613909 = 28777) (by norm_num)
theorem B384545 : Blo 319836 384545 := bbase (se 2 (by rfl) ⟨144204, by rfl⟩ : syracuseStep 384545 = 288409) (by norm_num)
theorem B482861 : Blo 319836 482861 := bbase (se 3 (by rfl) ⟨90536, by rfl⟩ : syracuseStep 482861 = 181073) (by norm_num)
theorem B810557 : Blo 319836 810557 := bbase (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) (by norm_num)
theorem B482885 : Blo 319836 482885 := bbase (se 4 (by rfl) ⟨45270, by rfl⟩ : syracuseStep 482885 = 90541) (by norm_num)
theorem B482909 : Blo 319836 482909 := bbase (se 3 (by rfl) ⟨90545, by rfl⟩ : syracuseStep 482909 = 181091) (by norm_num)
theorem B482933 : Blo 319836 482933 := bbase (se 5 (by rfl) ⟨22637, by rfl⟩ : syracuseStep 482933 = 45275) (by norm_num)
theorem B482957 : Blo 319836 482957 := bbase (se 3 (by rfl) ⟨90554, by rfl⟩ : syracuseStep 482957 = 181109) (by norm_num)
theorem B482981 : Blo 319836 482981 := bbase (se 4 (by rfl) ⟨45279, by rfl⟩ : syracuseStep 482981 = 90559) (by norm_num)
theorem B483005 : Blo 319836 483005 := bbase (se 3 (by rfl) ⟨90563, by rfl⟩ : syracuseStep 483005 = 181127) (by norm_num)
theorem B1367765 : Blo 319836 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B483029 : Blo 319836 483029 := bbase (se 7 (by rfl) ⟨5660, by rfl⟩ : syracuseStep 483029 = 11321) (by norm_num)
theorem B777941 : Blo 319836 777941 := bbase (se 7 (by rfl) ⟨9116, by rfl⟩ : syracuseStep 777941 = 18233) (by norm_num)
theorem B515821 : Blo 319836 515821 := bbase (se 3 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 515821 = 193433) (by norm_num)
theorem B483053 : Blo 319836 483053 := bbase (se 3 (by rfl) ⟨90572, by rfl⟩ : syracuseStep 483053 = 181145) (by norm_num)
theorem B810749 : Blo 319836 810749 := bbase (se 3 (by rfl) ⟨152015, by rfl⟩ : syracuseStep 810749 = 304031) (by norm_num)
theorem B483077 : Blo 319836 483077 := bbase (se 4 (by rfl) ⟨45288, by rfl⟩ : syracuseStep 483077 = 90577) (by norm_num)
theorem B483101 : Blo 319836 483101 := bbase (se 3 (by rfl) ⟨90581, by rfl⟩ : syracuseStep 483101 = 181163) (by norm_num)
theorem B483125 : Blo 319836 483125 := bbase (se 5 (by rfl) ⟨22646, by rfl⟩ : syracuseStep 483125 = 45293) (by norm_num)
theorem B614213 : Blo 319836 614213 := bbase (se 4 (by rfl) ⟨57582, by rfl⟩ : syracuseStep 614213 = 115165) (by norm_num)
theorem B483149 : Blo 319836 483149 := bbase (se 3 (by rfl) ⟨90590, by rfl⟩ : syracuseStep 483149 = 181181) (by norm_num)
theorem B384853 : Blo 319836 384853 := bbase (se 9 (by rfl) ⟨1127, by rfl⟩ : syracuseStep 384853 = 2255) (by norm_num)
theorem B483173 : Blo 319836 483173 := bbase (se 4 (by rfl) ⟨45297, by rfl⟩ : syracuseStep 483173 = 90595) (by norm_num)
theorem B483197 : Blo 319836 483197 := bbase (se 3 (by rfl) ⟨90599, by rfl⟩ : syracuseStep 483197 = 181199) (by norm_num)
theorem B483221 : Blo 319836 483221 := bbase (se 6 (by rfl) ⟨11325, by rfl⟩ : syracuseStep 483221 = 22651) (by norm_num)
theorem B483245 : Blo 319836 483245 := bbase (se 3 (by rfl) ⟨90608, by rfl⟩ : syracuseStep 483245 = 181217) (by norm_num)
theorem B483269 : Blo 319836 483269 := bbase (se 4 (by rfl) ⟨45306, by rfl⟩ : syracuseStep 483269 = 90613) (by norm_num)
theorem B483293 : Blo 319836 483293 := bbase (se 3 (by rfl) ⟨90617, by rfl⟩ : syracuseStep 483293 = 181235) (by norm_num)
theorem B483317 : Blo 319836 483317 := bbase (se 5 (by rfl) ⟨22655, by rfl⟩ : syracuseStep 483317 = 45311) (by norm_num)
theorem B483341 : Blo 319836 483341 := bbase (se 3 (by rfl) ⟨90626, by rfl⟩ : syracuseStep 483341 = 181253) (by norm_num)
theorem B483365 : Blo 319836 483365 := bbase (se 4 (by rfl) ⟨45315, by rfl⟩ : syracuseStep 483365 = 90631) (by norm_num)
theorem B483389 : Blo 319836 483389 := bbase (se 3 (by rfl) ⟨90635, by rfl⟩ : syracuseStep 483389 = 181271) (by norm_num)
theorem B811093 : Blo 319836 811093 := bbase (se 8 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 811093 = 9505) (by norm_num)
theorem B483413 : Blo 319836 483413 := bbase (se 8 (by rfl) ⟨2832, by rfl⟩ : syracuseStep 483413 = 5665) (by norm_num)
theorem B548957 : Blo 319836 548957 := bbase (se 3 (by rfl) ⟨102929, by rfl⟩ : syracuseStep 548957 = 205859) (by norm_num)
theorem B581725 : Blo 319836 581725 := bbase (se 3 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 581725 = 218147) (by norm_num)
theorem B483437 : Blo 319836 483437 := bbase (se 3 (by rfl) ⟨90644, by rfl⟩ : syracuseStep 483437 = 181289) (by norm_num)
theorem B483461 : Blo 319836 483461 := bbase (se 4 (by rfl) ⟨45324, by rfl⟩ : syracuseStep 483461 = 90649) (by norm_num)
theorem B483485 : Blo 319836 483485 := bbase (se 3 (by rfl) ⟨90653, by rfl⟩ : syracuseStep 483485 = 181307) (by norm_num)
theorem B483509 : Blo 319836 483509 := bbase (se 5 (by rfl) ⟨22664, by rfl⟩ : syracuseStep 483509 = 45329) (by norm_num)
theorem B581813 : Blo 319836 581813 := bbase (se 5 (by rfl) ⟨27272, by rfl⟩ : syracuseStep 581813 = 54545) (by norm_num)
theorem B811205 : Blo 319836 811205 := bbase (se 4 (by rfl) ⟨76050, by rfl⟩ : syracuseStep 811205 = 152101) (by norm_num)
theorem B483533 : Blo 319836 483533 := bbase (se 3 (by rfl) ⟨90662, by rfl⟩ : syracuseStep 483533 = 181325) (by norm_num)
theorem B385237 : Blo 319836 385237 := bbase (se 7 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 385237 = 9029) (by norm_num)
theorem B385241 : Blo 319836 385241 := bbase (se 2 (by rfl) ⟨144465, by rfl⟩ : syracuseStep 385241 = 288931) (by norm_num)
theorem B483557 : Blo 319836 483557 := bbase (se 4 (by rfl) ⟨45333, by rfl⟩ : syracuseStep 483557 = 90667) (by norm_num)
theorem B483581 : Blo 319836 483581 := bbase (se 3 (by rfl) ⟨90671, by rfl⟩ : syracuseStep 483581 = 181343) (by norm_num)
theorem B483605 : Blo 319836 483605 := bbase (se 6 (by rfl) ⟨11334, by rfl⟩ : syracuseStep 483605 = 22669) (by norm_num)
theorem B483629 : Blo 319836 483629 := bbase (se 3 (by rfl) ⟨90680, by rfl⟩ : syracuseStep 483629 = 181361) (by norm_num)
theorem B483653 : Blo 319836 483653 := bbase (se 4 (by rfl) ⟨45342, by rfl⟩ : syracuseStep 483653 = 90685) (by norm_num)
theorem B483677 : Blo 319836 483677 := bbase (se 3 (by rfl) ⟨90689, by rfl⟩ : syracuseStep 483677 = 181379) (by norm_num)
theorem B483701 : Blo 319836 483701 := bbase (se 5 (by rfl) ⟨22673, by rfl⟩ : syracuseStep 483701 = 45347) (by norm_num)
theorem B811397 : Blo 319836 811397 := bbase (se 4 (by rfl) ⟨76068, by rfl⟩ : syracuseStep 811397 = 152137) (by norm_num)
theorem B483725 : Blo 319836 483725 := bbase (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) (by norm_num)
theorem B483749 : Blo 319836 483749 := bbase (se 4 (by rfl) ⟨45351, by rfl⟩ : syracuseStep 483749 = 90703) (by norm_num)
theorem B483773 : Blo 319836 483773 := bbase (se 3 (by rfl) ⟨90707, by rfl⟩ : syracuseStep 483773 = 181415) (by norm_num)
theorem B483797 : Blo 319836 483797 := bbase (se 7 (by rfl) ⟨5669, by rfl⟩ : syracuseStep 483797 = 11339) (by norm_num)
theorem B483821 : Blo 319836 483821 := bbase (se 3 (by rfl) ⟨90716, by rfl⟩ : syracuseStep 483821 = 181433) (by norm_num)
theorem B483845 : Blo 319836 483845 := bbase (se 4 (by rfl) ⟨45360, by rfl⟩ : syracuseStep 483845 = 90721) (by norm_num)
theorem B352793 : Blo 319836 352793 := bbase (se 2 (by rfl) ⟨132297, by rfl⟩ : syracuseStep 352793 = 264595) (by norm_num)
theorem B483869 : Blo 319836 483869 := bbase (se 3 (by rfl) ⟨90725, by rfl⟩ : syracuseStep 483869 = 181451) (by norm_num)
theorem B2482741 : Blo 319836 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B483893 : Blo 319836 483893 := bbase (se 5 (by rfl) ⟨22682, by rfl⟩ : syracuseStep 483893 = 45365) (by norm_num)
theorem B483917 : Blo 319836 483917 := bbase (se 3 (by rfl) ⟨90734, by rfl⟩ : syracuseStep 483917 = 181469) (by norm_num)
theorem B483941 : Blo 319836 483941 := bbase (se 4 (by rfl) ⟨45369, by rfl⟩ : syracuseStep 483941 = 90739) (by norm_num)
theorem B582245 : Blo 319836 582245 := bbase (se 4 (by rfl) ⟨54585, by rfl⟩ : syracuseStep 582245 = 109171) (by norm_num)
theorem B385645 : Blo 319836 385645 := bbase (se 3 (by rfl) ⟨72308, by rfl⟩ : syracuseStep 385645 = 144617) (by norm_num)
theorem B483965 : Blo 319836 483965 := bbase (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) (by norm_num)
theorem B1630853 : Blo 319836 1630853 := bbase (se 4 (by rfl) ⟨152892, by rfl⟩ : syracuseStep 1630853 = 305785) (by norm_num)
theorem B483989 : Blo 319836 483989 := bbase (se 6 (by rfl) ⟨11343, by rfl⟩ : syracuseStep 483989 = 22687) (by norm_num)
theorem B484013 : Blo 319836 484013 := bbase (se 3 (by rfl) ⟨90752, by rfl⟩ : syracuseStep 484013 = 181505) (by norm_num)
theorem B484037 : Blo 319836 484037 := bbase (se 4 (by rfl) ⟨45378, by rfl⟩ : syracuseStep 484037 = 90757) (by norm_num)
theorem B811741 : Blo 319836 811741 := bbase (se 3 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 811741 = 304403) (by norm_num)
theorem B484061 : Blo 319836 484061 := bbase (se 3 (by rfl) ⟨90761, by rfl⟩ : syracuseStep 484061 = 181523) (by norm_num)
theorem B484085 : Blo 319836 484085 := bbase (se 5 (by rfl) ⟨22691, by rfl⟩ : syracuseStep 484085 = 45383) (by norm_num)
theorem B484109 : Blo 319836 484109 := bbase (se 3 (by rfl) ⟨90770, by rfl⟩ : syracuseStep 484109 = 181541) (by norm_num)
theorem B484133 : Blo 319836 484133 := bbase (se 4 (by rfl) ⟨45387, by rfl⟩ : syracuseStep 484133 = 90775) (by norm_num)
theorem B484157 : Blo 319836 484157 := bbase (se 3 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 484157 = 181559) (by norm_num)
theorem B811853 : Blo 319836 811853 := bbase (se 3 (by rfl) ⟨152222, by rfl⟩ : syracuseStep 811853 = 304445) (by norm_num)
theorem B484181 : Blo 319836 484181 := bbase (se 9 (by rfl) ⟨1418, by rfl⟩ : syracuseStep 484181 = 2837) (by norm_num)
theorem B484205 : Blo 319836 484205 := bbase (se 3 (by rfl) ⟨90788, by rfl⟩ : syracuseStep 484205 = 181577) (by norm_num)
theorem B2614133 : Blo 319836 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B484229 : Blo 319836 484229 := bbase (se 4 (by rfl) ⟨45396, by rfl⟩ : syracuseStep 484229 = 90793) (by norm_num)
theorem B582533 : Blo 319836 582533 := bbase (se 4 (by rfl) ⟨54612, by rfl⟩ : syracuseStep 582533 = 109225) (by norm_num)
theorem B517013 : Blo 319836 517013 := bbase (se 6 (by rfl) ⟨12117, by rfl⟩ : syracuseStep 517013 = 24235) (by norm_num)
theorem B484253 : Blo 319836 484253 := bbase (se 3 (by rfl) ⟨90797, by rfl⟩ : syracuseStep 484253 = 181595) (by norm_num)
theorem B484277 : Blo 319836 484277 := bbase (se 5 (by rfl) ⟨22700, by rfl⟩ : syracuseStep 484277 = 45401) (by norm_num)
theorem B484301 : Blo 319836 484301 := bbase (se 3 (by rfl) ⟨90806, by rfl⟩ : syracuseStep 484301 = 181613) (by norm_num)
theorem B484325 : Blo 319836 484325 := bbase (se 4 (by rfl) ⟨45405, by rfl⟩ : syracuseStep 484325 = 90811) (by norm_num)
theorem B484349 : Blo 319836 484349 := bbase (se 3 (by rfl) ⟨90815, by rfl⟩ : syracuseStep 484349 = 181631) (by norm_num)
theorem B812045 : Blo 319836 812045 := bbase (se 3 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 812045 = 304517) (by norm_num)
theorem B484373 : Blo 319836 484373 := bbase (se 6 (by rfl) ⟨11352, by rfl⟩ : syracuseStep 484373 = 22705) (by norm_num)
theorem B484397 : Blo 319836 484397 := bbase (se 3 (by rfl) ⟨90824, by rfl⟩ : syracuseStep 484397 = 181649) (by norm_num)
theorem B484421 : Blo 319836 484421 := bbase (se 4 (by rfl) ⟨45414, by rfl⟩ : syracuseStep 484421 = 90829) (by norm_num)
theorem B517205 : Blo 319836 517205 := bbase (se 8 (by rfl) ⟨3030, by rfl⟩ : syracuseStep 517205 = 6061) (by norm_num)
theorem B484445 : Blo 319836 484445 := bbase (se 3 (by rfl) ⟨90833, by rfl⟩ : syracuseStep 484445 = 181667) (by norm_num)
theorem B484469 : Blo 319836 484469 := bbase (se 5 (by rfl) ⟨22709, by rfl⟩ : syracuseStep 484469 = 45419) (by norm_num)
theorem B484493 : Blo 319836 484493 := bbase (se 3 (by rfl) ⟨90842, by rfl⟩ : syracuseStep 484493 = 181685) (by norm_num)
theorem B484517 : Blo 319836 484517 := bbase (se 4 (by rfl) ⟨45423, by rfl⟩ : syracuseStep 484517 = 90847) (by norm_num)
theorem B484541 : Blo 319836 484541 := bbase (se 3 (by rfl) ⟨90851, by rfl⟩ : syracuseStep 484541 = 181703) (by norm_num)
theorem B484565 : Blo 319836 484565 := bbase (se 7 (by rfl) ⟨5678, by rfl⟩ : syracuseStep 484565 = 11357) (by norm_num)
theorem B484589 : Blo 319836 484589 := bbase (se 3 (by rfl) ⟨90860, by rfl⟩ : syracuseStep 484589 = 181721) (by norm_num)
theorem B1729781 : Blo 319836 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B484613 : Blo 319836 484613 := bbase (se 4 (by rfl) ⟨45432, by rfl⟩ : syracuseStep 484613 = 90865) (by norm_num)
theorem B484637 : Blo 319836 484637 := bbase (se 3 (by rfl) ⟨90869, by rfl⟩ : syracuseStep 484637 = 181739) (by norm_num)
theorem B484661 : Blo 319836 484661 := bbase (se 5 (by rfl) ⟨22718, by rfl⟩ : syracuseStep 484661 = 45437) (by norm_num)
theorem B484685 : Blo 319836 484685 := bbase (se 3 (by rfl) ⟨90878, by rfl⟩ : syracuseStep 484685 = 181757) (by norm_num)
theorem B419161 : Blo 319836 419161 := bbase (se 2 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 419161 = 314371) (by norm_num)
theorem B812389 : Blo 319836 812389 := bbase (se 4 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 812389 = 152323) (by norm_num)
theorem B1467749 : Blo 319836 1467749 := bbase (se 4 (by rfl) ⟨137601, by rfl⟩ : syracuseStep 1467749 = 275203) (by norm_num)
theorem B484709 : Blo 319836 484709 := bbase (se 4 (by rfl) ⟨45441, by rfl⟩ : syracuseStep 484709 = 90883) (by norm_num)
theorem B484733 : Blo 319836 484733 := bbase (se 3 (by rfl) ⟨90887, by rfl⟩ : syracuseStep 484733 = 181775) (by norm_num)
theorem B484757 : Blo 319836 484757 := bbase (se 6 (by rfl) ⟨11361, by rfl⟩ : syracuseStep 484757 = 22723) (by norm_num)
theorem B484781 : Blo 319836 484781 := bbase (se 3 (by rfl) ⟨90896, by rfl⟩ : syracuseStep 484781 = 181793) (by norm_num)
theorem B1369541 : Blo 319836 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B484805 : Blo 319836 484805 := bbase (se 4 (by rfl) ⟨45450, by rfl⟩ : syracuseStep 484805 = 90901) (by norm_num)
theorem B812501 : Blo 319836 812501 := bbase (se 7 (by rfl) ⟨9521, by rfl⟩ : syracuseStep 812501 = 19043) (by norm_num)
theorem B484829 : Blo 319836 484829 := bbase (se 3 (by rfl) ⟨90905, by rfl⟩ : syracuseStep 484829 = 181811) (by norm_num)
theorem B648685 : Blo 319836 648685 := bbase (se 3 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 648685 = 243257) (by norm_num)
theorem B484853 : Blo 319836 484853 := bbase (se 5 (by rfl) ⟨22727, by rfl⟩ : syracuseStep 484853 = 45455) (by norm_num)
theorem B484877 : Blo 319836 484877 := bbase (se 3 (by rfl) ⟨90914, by rfl⟩ : syracuseStep 484877 = 181829) (by norm_num)
theorem B484901 : Blo 319836 484901 := bbase (se 4 (by rfl) ⟨45459, by rfl⟩ : syracuseStep 484901 = 90919) (by norm_num)
theorem B484925 : Blo 319836 484925 := bbase (se 3 (by rfl) ⟨90923, by rfl⟩ : syracuseStep 484925 = 181847) (by norm_num)
theorem B484949 : Blo 319836 484949 := bbase (se 8 (by rfl) ⟨2841, by rfl⟩ : syracuseStep 484949 = 5683) (by norm_num)
theorem B484973 : Blo 319836 484973 := bbase (se 3 (by rfl) ⟨90932, by rfl⟩ : syracuseStep 484973 = 181865) (by norm_num)
theorem B484997 : Blo 319836 484997 := bbase (se 4 (by rfl) ⟨45468, by rfl⟩ : syracuseStep 484997 = 90937) (by norm_num)
theorem B812693 : Blo 319836 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B485021 : Blo 319836 485021 := bbase (se 3 (by rfl) ⟨90941, by rfl⟩ : syracuseStep 485021 = 181883) (by norm_num)
theorem B1369781 : Blo 319836 1369781 := bbase (se 5 (by rfl) ⟨64208, by rfl⟩ : syracuseStep 1369781 = 128417) (by norm_num)
theorem B485045 : Blo 319836 485045 := bbase (se 5 (by rfl) ⟨22736, by rfl⟩ : syracuseStep 485045 = 45473) (by norm_num)
theorem B485069 : Blo 319836 485069 := bbase (se 3 (by rfl) ⟨90950, by rfl⟩ : syracuseStep 485069 = 181901) (by norm_num)
theorem B4187861 : Blo 319836 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B485093 : Blo 319836 485093 := bbase (se 4 (by rfl) ⟨45477, by rfl⟩ : syracuseStep 485093 = 90955) (by norm_num)
theorem B485117 : Blo 319836 485117 := bbase (se 3 (by rfl) ⟨90959, by rfl⟩ : syracuseStep 485117 = 181919) (by norm_num)
theorem B485141 : Blo 319836 485141 := bbase (se 6 (by rfl) ⟨11370, by rfl⟩ : syracuseStep 485141 = 22741) (by norm_num)
theorem B485165 : Blo 319836 485165 := bbase (se 3 (by rfl) ⟨90968, by rfl⟩ : syracuseStep 485165 = 181937) (by norm_num)
theorem B550709 : Blo 319836 550709 := bbase (se 5 (by rfl) ⟨25814, by rfl⟩ : syracuseStep 550709 = 51629) (by norm_num)
theorem B485189 : Blo 319836 485189 := bbase (se 4 (by rfl) ⟨45486, by rfl⟩ : syracuseStep 485189 = 90973) (by norm_num)
theorem B485213 : Blo 319836 485213 := bbase (se 3 (by rfl) ⟨90977, by rfl⟩ : syracuseStep 485213 = 181955) (by norm_num)
theorem B485237 : Blo 319836 485237 := bbase (se 5 (by rfl) ⟨22745, by rfl⟩ : syracuseStep 485237 = 45491) (by norm_num)
theorem B485261 : Blo 319836 485261 := bbase (se 3 (by rfl) ⟨90986, by rfl⟩ : syracuseStep 485261 = 181973) (by norm_num)
theorem B1632149 : Blo 319836 1632149 := bbase (se 6 (by rfl) ⟨38253, by rfl⟩ : syracuseStep 1632149 = 76507) (by norm_num)
theorem B485285 : Blo 319836 485285 := bbase (se 4 (by rfl) ⟨45495, by rfl⟩ : syracuseStep 485285 = 90991) (by norm_num)
theorem B485309 : Blo 319836 485309 := bbase (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) (by norm_num)
theorem B2746325 : Blo 319836 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B387029 : Blo 319836 387029 := bbase (se 7 (by rfl) ⟨4535, by rfl⟩ : syracuseStep 387029 = 9071) (by norm_num)
theorem B485333 : Blo 319836 485333 := bbase (se 7 (by rfl) ⟨5687, by rfl⟩ : syracuseStep 485333 = 11375) (by norm_num)
theorem B813037 : Blo 319836 813037 := bbase (se 3 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 813037 = 304889) (by norm_num)
theorem B485357 : Blo 319836 485357 := bbase (se 3 (by rfl) ⟨91004, by rfl⟩ : syracuseStep 485357 = 182009) (by norm_num)
theorem B485381 : Blo 319836 485381 := bbase (se 4 (by rfl) ⟨45504, by rfl⟩ : syracuseStep 485381 = 91009) (by norm_num)
theorem B485405 : Blo 319836 485405 := bbase (se 3 (by rfl) ⟨91013, by rfl⟩ : syracuseStep 485405 = 182027) (by norm_num)
theorem B1173541 : Blo 319836 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B485429 : Blo 319836 485429 := bbase (se 5 (by rfl) ⟨22754, by rfl⟩ : syracuseStep 485429 = 45509) (by norm_num)
theorem B485453 : Blo 319836 485453 := bbase (se 3 (by rfl) ⟨91022, by rfl⟩ : syracuseStep 485453 = 182045) (by norm_num)
theorem B649309 : Blo 319836 649309 := bbase (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) (by norm_num)
theorem B813149 : Blo 319836 813149 := bbase (se 3 (by rfl) ⟨152465, by rfl⟩ : syracuseStep 813149 = 304931) (by norm_num)
theorem B485477 : Blo 319836 485477 := bbase (se 4 (by rfl) ⟨45513, by rfl⟩ : syracuseStep 485477 = 91027) (by norm_num)
theorem B485501 : Blo 319836 485501 := bbase (se 3 (by rfl) ⟨91031, by rfl⟩ : syracuseStep 485501 = 182063) (by norm_num)
theorem B485525 : Blo 319836 485525 := bbase (se 6 (by rfl) ⟨11379, by rfl⟩ : syracuseStep 485525 = 22759) (by norm_num)
theorem B485549 : Blo 319836 485549 := bbase (se 3 (by rfl) ⟨91040, by rfl⟩ : syracuseStep 485549 = 182081) (by norm_num)
theorem B3106997 : Blo 319836 3106997 := bbase (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) (by norm_num)
theorem B485573 : Blo 319836 485573 := bbase (se 4 (by rfl) ⟨45522, by rfl⟩ : syracuseStep 485573 = 91045) (by norm_num)
theorem B387289 : Blo 319836 387289 := bbase (se 2 (by rfl) ⟨145233, by rfl⟩ : syracuseStep 387289 = 290467) (by norm_num)
theorem B485597 : Blo 319836 485597 := bbase (se 3 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 485597 = 182099) (by norm_num)
theorem B485621 : Blo 319836 485621 := bbase (se 5 (by rfl) ⟨22763, by rfl⟩ : syracuseStep 485621 = 45527) (by norm_num)
theorem B387337 : Blo 319836 387337 := bbase (se 2 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 387337 = 290503) (by norm_num)
theorem B485645 : Blo 319836 485645 := bbase (se 3 (by rfl) ⟨91058, by rfl⟩ : syracuseStep 485645 = 182117) (by norm_num)
theorem B813341 : Blo 319836 813341 := bbase (se 3 (by rfl) ⟨152501, by rfl⟩ : syracuseStep 813341 = 305003) (by norm_num)
theorem B485669 : Blo 319836 485669 := bbase (se 4 (by rfl) ⟨45531, by rfl⟩ : syracuseStep 485669 = 91063) (by norm_num)
theorem B485693 : Blo 319836 485693 := bbase (se 3 (by rfl) ⟨91067, by rfl⟩ : syracuseStep 485693 = 182135) (by norm_num)
theorem B485717 : Blo 319836 485717 := bbase (se 10 (by rfl) ⟨711, by rfl⟩ : syracuseStep 485717 = 1423) (by norm_num)
theorem B485741 : Blo 319836 485741 := bbase (se 3 (by rfl) ⟨91076, by rfl⟩ : syracuseStep 485741 = 182153) (by norm_num)
theorem B616829 : Blo 319836 616829 := bbase (se 3 (by rfl) ⟨115655, by rfl⟩ : syracuseStep 616829 = 231311) (by norm_num)
theorem B518653 : Blo 319836 518653 := bbase (se 3 (by rfl) ⟨97247, by rfl⟩ : syracuseStep 518653 = 194495) (by norm_num)
theorem B813685 : Blo 319836 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B813797 : Blo 319836 813797 := bbase (se 4 (by rfl) ⟨76293, by rfl⟩ : syracuseStep 813797 = 152587) (by norm_num)
theorem B617237 : Blo 319836 617237 := bbase (se 6 (by rfl) ⟨14466, by rfl⟩ : syracuseStep 617237 = 28933) (by norm_num)
theorem B813989 : Blo 319836 813989 := bbase (se 4 (by rfl) ⟨76311, by rfl⟩ : syracuseStep 813989 = 152623) (by norm_num)
theorem B388009 : Blo 319836 388009 := bbase (se 2 (by rfl) ⟨145503, by rfl⟩ : syracuseStep 388009 = 291007) (by norm_num)
theorem B1633445 : Blo 319836 1633445 := bbase (se 4 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 1633445 = 306271) (by norm_num)
theorem B2616533 : Blo 319836 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B3075317 : Blo 319836 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B814333 : Blo 319836 814333 := bbase (se 3 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 814333 = 305375) (by norm_num)
theorem B650501 : Blo 319836 650501 := bbase (se 4 (by rfl) ⟨60984, by rfl⟩ : syracuseStep 650501 = 121969) (by norm_num)
theorem B650549 : Blo 319836 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B814445 : Blo 319836 814445 := bbase (se 3 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 814445 = 305417) (by norm_num)
theorem B2616725 : Blo 319836 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B945605 : Blo 319836 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B814637 : Blo 319836 814637 := bbase (se 3 (by rfl) ⟨152744, by rfl⟩ : syracuseStep 814637 = 305489) (by norm_num)
theorem B2780725 : Blo 319836 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B683677 : Blo 319836 683677 := bbase (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) (by norm_num)
theorem B683797 : Blo 319836 683797 := bbase (se 6 (by rfl) ⟨16026, by rfl⟩ : syracuseStep 683797 = 32053) (by norm_num)
theorem B814981 : Blo 319836 814981 := bbase (se 4 (by rfl) ⟨76404, by rfl⟩ : syracuseStep 814981 = 152809) (by norm_num)
theorem B389009 : Blo 319836 389009 := bbase (se 2 (by rfl) ⟨145878, by rfl⟩ : syracuseStep 389009 = 291757) (by norm_num)
theorem B913301 : Blo 319836 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B1372069 : Blo 319836 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B815093 : Blo 319836 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B684053 : Blo 319836 684053 := bbase (se 6 (by rfl) ⟨16032, by rfl⟩ : syracuseStep 684053 = 32065) (by norm_num)
theorem B553109 : Blo 319836 553109 := bbase (se 6 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 553109 = 25927) (by norm_num)
theorem B815285 : Blo 319836 815285 := bbase (se 5 (by rfl) ⟨38216, by rfl⟩ : syracuseStep 815285 = 76433) (by norm_num)
theorem B1831157 : Blo 319836 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B2453813 : Blo 319836 2453813 := bbase (se 5 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 2453813 = 230045) (by norm_num)
theorem B1634741 : Blo 319836 1634741 := bbase (se 5 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 1634741 = 153257) (by norm_num)
theorem B1667557 : Blo 319836 1667557 := bbase (se 4 (by rfl) ⟨156333, by rfl⟩ : syracuseStep 1667557 = 312667) (by norm_num)
theorem B815629 : Blo 319836 815629 := bbase (se 3 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 815629 = 305861) (by norm_num)
theorem B815741 : Blo 319836 815741 := bbase (se 3 (by rfl) ⟨152951, by rfl⟩ : syracuseStep 815741 = 305903) (by norm_num)
theorem B1766165 : Blo 319836 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B815933 : Blo 319836 815933 := bbase (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) (by norm_num)
theorem B5665621 : Blo 319836 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B2749301 : Blo 319836 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B455557 : Blo 319836 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B684941 : Blo 319836 684941 := bbase (se 3 (by rfl) ⟨128426, by rfl⟩ : syracuseStep 684941 = 256853) (by norm_num)
theorem B914485 : Blo 319836 914485 := bbase (se 5 (by rfl) ⟨42866, by rfl⟩ : syracuseStep 914485 = 85733) (by norm_num)
theorem B685181 : Blo 319836 685181 := bbase (se 3 (by rfl) ⟨128471, by rfl⟩ : syracuseStep 685181 = 256943) (by norm_num)
theorem B816277 : Blo 319836 816277 := bbase (se 6 (by rfl) ⟨19131, by rfl⟩ : syracuseStep 816277 = 38263) (by norm_num)
theorem B914645 : Blo 319836 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B324853 : Blo 319836 324853 := bbase (se 5 (by rfl) ⟨15227, by rfl⟩ : syracuseStep 324853 = 30455) (by norm_num)
theorem B816389 : Blo 319836 816389 := bbase (se 4 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 816389 = 153073) (by norm_num)
theorem B1373557 : Blo 319836 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B1373573 : Blo 319836 1373573 := bbase (se 4 (by rfl) ⟨128772, by rfl⟩ : syracuseStep 1373573 = 257545) (by norm_num)
theorem B1832341 : Blo 319836 1832341 := bbase (se 6 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 1832341 = 85891) (by norm_num)
theorem B914885 : Blo 319836 914885 := bbase (se 4 (by rfl) ⟨85770, by rfl⟩ : syracuseStep 914885 = 171541) (by norm_num)
theorem B816581 : Blo 319836 816581 := bbase (se 4 (by rfl) ⟨76554, by rfl⟩ : syracuseStep 816581 = 153109) (by norm_num)
theorem B456149 : Blo 319836 456149 := bbase (se 7 (by rfl) ⟨5345, by rfl⟩ : syracuseStep 456149 = 10691) (by norm_num)
theorem B652789 : Blo 319836 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B456229 : Blo 319836 456229 := bbase (se 4 (by rfl) ⟨42771, by rfl⟩ : syracuseStep 456229 = 85543) (by norm_num)
theorem B652853 : Blo 319836 652853 := bbase (se 5 (by rfl) ⟨30602, by rfl⟩ : syracuseStep 652853 = 61205) (by norm_num)
theorem B685685 : Blo 319836 685685 := bbase (se 5 (by rfl) ⟨32141, by rfl⟩ : syracuseStep 685685 = 64283) (by norm_num)
theorem B685693 : Blo 319836 685693 := bbase (se 3 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 685693 = 257135) (by norm_num)
theorem B915077 : Blo 319836 915077 := bbase (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) (by norm_num)
theorem B456349 : Blo 319836 456349 := bbase (se 3 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 456349 = 171131) (by norm_num)
theorem B1636037 : Blo 319836 1636037 := bbase (se 4 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 1636037 = 306757) (by norm_num)
theorem B882389 : Blo 319836 882389 := bbase (se 7 (by rfl) ⟨10340, by rfl⟩ : syracuseStep 882389 = 20681) (by norm_num)
theorem B456445 : Blo 319836 456445 := bbase (se 3 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 456445 = 171167) (by norm_num)
theorem B816925 : Blo 319836 816925 := bbase (se 3 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 816925 = 306347) (by norm_num)
theorem B817037 : Blo 319836 817037 := bbase (se 3 (by rfl) ⟨153194, by rfl⟩ : syracuseStep 817037 = 306389) (by norm_num)
theorem B817229 : Blo 319836 817229 := bbase (se 3 (by rfl) ⟨153230, by rfl⟩ : syracuseStep 817229 = 306461) (by norm_num)
theorem B1308869 : Blo 319836 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B456941 : Blo 319836 456941 := bbase (se 3 (by rfl) ⟨85676, by rfl⟩ : syracuseStep 456941 = 171353) (by norm_num)
theorem B1079621 : Blo 319836 1079621 := bbase (se 4 (by rfl) ⟨101214, by rfl⟩ : syracuseStep 1079621 = 202429) (by norm_num)
theorem B1308997 : Blo 319836 1308997 := bbase (se 4 (by rfl) ⟨122718, by rfl⟩ : syracuseStep 1308997 = 245437) (by norm_num)
theorem B326017 : Blo 319836 326017 := bbase (se 2 (by rfl) ⟨122256, by rfl⟩ : syracuseStep 326017 = 244513) (by norm_num)
theorem B326029 : Blo 319836 326029 := bbase (se 3 (by rfl) ⟨61130, by rfl⟩ : syracuseStep 326029 = 122261) (by norm_num)
theorem B326053 : Blo 319836 326053 := bbase (se 4 (by rfl) ⟨30567, by rfl⟩ : syracuseStep 326053 = 61135) (by norm_num)
theorem B817573 : Blo 319836 817573 := bbase (se 4 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 817573 = 153295) (by norm_num)
theorem B4946453 : Blo 319836 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B817685 : Blo 319836 817685 := bbase (se 6 (by rfl) ⟨19164, by rfl⟩ : syracuseStep 817685 = 38329) (by norm_num)
theorem B916069 : Blo 319836 916069 := bbase (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) (by norm_num)
theorem B817877 : Blo 319836 817877 := bbase (se 7 (by rfl) ⟨9584, by rfl⟩ : syracuseStep 817877 = 19169) (by norm_num)
theorem B686821 : Blo 319836 686821 := bbase (se 4 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 686821 = 128779) (by norm_num)
theorem B1080053 : Blo 319836 1080053 := bbase (se 5 (by rfl) ⟨50627, by rfl⟩ : syracuseStep 1080053 = 101255) (by norm_num)
theorem B457493 : Blo 319836 457493 := bbase (se 6 (by rfl) ⟨10722, by rfl⟩ : syracuseStep 457493 = 21445) (by norm_num)
theorem B1178389 : Blo 319836 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B719693 : Blo 319836 719693 := bbase (se 3 (by rfl) ⟨134942, by rfl⟩ : syracuseStep 719693 = 269885) (by norm_num)
theorem B719765 : Blo 319836 719765 := bbase (se 6 (by rfl) ⟨16869, by rfl⟩ : syracuseStep 719765 = 33739) (by norm_num)
theorem B1637333 : Blo 319836 1637333 := bbase (se 7 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 1637333 = 38375) (by norm_num)
theorem B719837 : Blo 319836 719837 := bbase (se 3 (by rfl) ⟨134969, by rfl⟩ : syracuseStep 719837 = 269939) (by norm_num)
theorem B719909 : Blo 319836 719909 := bbase (se 4 (by rfl) ⟨67491, by rfl⟩ : syracuseStep 719909 = 134983) (by norm_num)
theorem B818221 : Blo 319836 818221 := bbase (se 3 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 818221 = 306833) (by norm_num)
theorem B687197 : Blo 319836 687197 := bbase (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) (by norm_num)
theorem B719981 : Blo 319836 719981 := bbase (se 3 (by rfl) ⟨134996, by rfl⟩ : syracuseStep 719981 = 269993) (by norm_num)
theorem B392329 : Blo 319836 392329 := bbase (se 2 (by rfl) ⟨147123, by rfl⟩ : syracuseStep 392329 = 294247) (by norm_num)
theorem B818333 : Blo 319836 818333 := bbase (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) (by norm_num)
theorem B1080485 : Blo 319836 1080485 := bbase (se 4 (by rfl) ⟨101295, by rfl⟩ : syracuseStep 1080485 = 202591) (by norm_num)
theorem B720053 : Blo 319836 720053 := bbase (se 5 (by rfl) ⟨33752, by rfl⟩ : syracuseStep 720053 = 67505) (by norm_num)
theorem B326873 : Blo 319836 326873 := bbase (se 2 (by rfl) ⟨122577, by rfl⟩ : syracuseStep 326873 = 245155) (by norm_num)
theorem B720125 : Blo 319836 720125 := bbase (se 3 (by rfl) ⟨135023, by rfl⟩ : syracuseStep 720125 = 270047) (by norm_num)
theorem B720197 : Blo 319836 720197 := bbase (se 4 (by rfl) ⟨67518, by rfl⟩ : syracuseStep 720197 = 135037) (by norm_num)
theorem B1834325 : Blo 319836 1834325 := bbase (se 11 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 1834325 = 2687) (by norm_num)
theorem B818525 : Blo 319836 818525 := bbase (se 3 (by rfl) ⟨153473, by rfl⟩ : syracuseStep 818525 = 306947) (by norm_num)
theorem B720269 : Blo 319836 720269 := bbase (se 3 (by rfl) ⟨135050, by rfl⟩ : syracuseStep 720269 = 270101) (by norm_num)
theorem B359833 : Blo 319836 359833 := bbase (se 2 (by rfl) ⟨134937, by rfl⟩ : syracuseStep 359833 = 269875) (by norm_num)
theorem B359869 : Blo 319836 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B720341 : Blo 319836 720341 := bbase (se 7 (by rfl) ⟨8441, by rfl⟩ : syracuseStep 720341 = 16883) (by norm_num)
theorem B359905 : Blo 319836 359905 := bbase (se 2 (by rfl) ⟨134964, by rfl⟩ : syracuseStep 359905 = 269929) (by norm_num)
theorem B359941 : Blo 319836 359941 := bbase (se 4 (by rfl) ⟨33744, by rfl⟩ : syracuseStep 359941 = 67489) (by norm_num)
theorem B458245 : Blo 319836 458245 := bbase (se 4 (by rfl) ⟨42960, by rfl⟩ : syracuseStep 458245 = 85921) (by norm_num)
theorem B720413 : Blo 319836 720413 := bbase (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) (by norm_num)
theorem B327197 : Blo 319836 327197 := bbase (se 3 (by rfl) ⟨61349, by rfl⟩ : syracuseStep 327197 = 122699) (by norm_num)
theorem B359977 : Blo 319836 359977 := bbase (se 2 (by rfl) ⟨134991, by rfl⟩ : syracuseStep 359977 = 269983) (by norm_num)
theorem B360013 : Blo 319836 360013 := bbase (se 3 (by rfl) ⟨67502, by rfl⟩ : syracuseStep 360013 = 135005) (by norm_num)
theorem B1080917 : Blo 319836 1080917 := bbase (se 8 (by rfl) ⟨6333, by rfl⟩ : syracuseStep 1080917 = 12667) (by norm_num)
theorem B1375829 : Blo 319836 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B720485 : Blo 319836 720485 := bbase (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) (by norm_num)
theorem B360049 : Blo 319836 360049 := bbase (se 2 (by rfl) ⟨135018, by rfl⟩ : syracuseStep 360049 = 270037) (by norm_num)
theorem B1638005 : Blo 319836 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B360085 : Blo 319836 360085 := bbase (se 6 (by rfl) ⟨8439, by rfl⟩ : syracuseStep 360085 = 16879) (by norm_num)
theorem B720557 : Blo 319836 720557 := bbase (se 3 (by rfl) ⟨135104, by rfl⟩ : syracuseStep 720557 = 270209) (by norm_num)
theorem B917173 : Blo 319836 917173 := bbase (se 5 (by rfl) ⟨42992, by rfl⟩ : syracuseStep 917173 = 85985) (by norm_num)
theorem B818869 : Blo 319836 818869 := bbase (se 5 (by rfl) ⟨38384, by rfl⟩ : syracuseStep 818869 = 76769) (by norm_num)
theorem B360121 : Blo 319836 360121 := bbase (se 2 (by rfl) ⟨135045, by rfl⟩ : syracuseStep 360121 = 270091) (by norm_num)
theorem B360157 : Blo 319836 360157 := bbase (se 3 (by rfl) ⟨67529, by rfl⟩ : syracuseStep 360157 = 135059) (by norm_num)
theorem B720629 : Blo 319836 720629 := bbase (se 5 (by rfl) ⟨33779, by rfl⟩ : syracuseStep 720629 = 67559) (by norm_num)
theorem B360193 : Blo 319836 360193 := bbase (se 2 (by rfl) ⟨135072, by rfl⟩ : syracuseStep 360193 = 270145) (by norm_num)
theorem B360229 : Blo 319836 360229 := bbase (se 4 (by rfl) ⟨33771, by rfl⟩ : syracuseStep 360229 = 67543) (by norm_num)
theorem B818981 : Blo 319836 818981 := bbase (se 4 (by rfl) ⟨76779, by rfl⟩ : syracuseStep 818981 = 153559) (by norm_num)
theorem B2817845 : Blo 319836 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B720701 : Blo 319836 720701 := bbase (se 3 (by rfl) ⟨135131, by rfl⟩ : syracuseStep 720701 = 270263) (by norm_num)
theorem B360265 : Blo 319836 360265 := bbase (se 2 (by rfl) ⟨135099, by rfl⟩ : syracuseStep 360265 = 270199) (by norm_num)
theorem B327529 : Blo 319836 327529 := bbase (se 2 (by rfl) ⟨122823, by rfl⟩ : syracuseStep 327529 = 245647) (by norm_num)
theorem B360301 : Blo 319836 360301 := bbase (se 3 (by rfl) ⟨67556, by rfl⟩ : syracuseStep 360301 = 135113) (by norm_num)
theorem B720773 : Blo 319836 720773 := bbase (se 4 (by rfl) ⟨67572, by rfl⟩ : syracuseStep 720773 = 135145) (by norm_num)
theorem B360337 : Blo 319836 360337 := bbase (se 2 (by rfl) ⟨135126, by rfl⟩ : syracuseStep 360337 = 270253) (by norm_num)
theorem B360373 : Blo 319836 360373 := bbase (se 5 (by rfl) ⟨16892, by rfl⟩ : syracuseStep 360373 = 33785) (by norm_num)
theorem B655285 : Blo 319836 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B720845 : Blo 319836 720845 := bbase (se 3 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 720845 = 270317) (by norm_num)
theorem B360409 : Blo 319836 360409 := bbase (se 2 (by rfl) ⟨135153, by rfl⟩ : syracuseStep 360409 = 270307) (by norm_num)
theorem B819173 : Blo 319836 819173 := bbase (se 4 (by rfl) ⟨76797, by rfl⟩ : syracuseStep 819173 = 153595) (by norm_num)
theorem B360445 : Blo 319836 360445 := bbase (se 3 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 360445 = 135167) (by norm_num)
theorem B720899 : Blo 319836 720899 := bstep (se 1 (by rfl) ⟨540674, by rfl⟩ : syracuseStep 720899 = 1081349) B1081349
theorem B1376291 : Blo 319836 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B360499 : Blo 319836 360499 := bstep (se 1 (by rfl) ⟨270374, by rfl⟩ : syracuseStep 360499 = 540749) B540749
theorem B1572941 : Blo 319836 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B1081457 : Blo 319836 1081457 := bstep (se 2 (by rfl) ⟨405546, by rfl⟩ : syracuseStep 1081457 = 811093) B811093
theorem B983171 : Blo 319836 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B360643 : Blo 319836 360643 := bstep (se 1 (by rfl) ⟨270482, by rfl⟩ : syracuseStep 360643 = 540965) B540965
theorem B721169 : Blo 319836 721169 := bstep (se 2 (by rfl) ⟨270438, by rfl⟩ : syracuseStep 721169 = 540877) B540877
theorem B721187 : Blo 319836 721187 := bstep (se 1 (by rfl) ⟨540890, by rfl⟩ : syracuseStep 721187 = 1081781) B1081781
theorem B360787 : Blo 319836 360787 := bstep (se 1 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 360787 = 541181) B541181
theorem B1474957 : Blo 319836 1474957 := bstep (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) B553109
theorem B360931 : Blo 319836 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B459265 : Blo 319836 459265 := bstep (se 2 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 459265 = 344449) B344449
theorem B721457 : Blo 319836 721457 := bstep (se 2 (by rfl) ⟨270546, by rfl⟩ : syracuseStep 721457 = 541093) B541093
theorem B721475 : Blo 319836 721475 := bstep (se 1 (by rfl) ⟨541106, by rfl⟩ : syracuseStep 721475 = 1082213) B1082213
theorem B2064973 : Blo 319836 2064973 := bstep (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) B774365
theorem B590417 : Blo 319836 590417 := bstep (se 2 (by rfl) ⟨221406, by rfl⟩ : syracuseStep 590417 = 442813) B442813
theorem B459361 : Blo 319836 459361 := bstep (se 2 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 459361 = 344521) B344521
theorem B361075 : Blo 319836 361075 := bstep (se 1 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 361075 = 541613) B541613
theorem B393859 : Blo 319836 393859 := bstep (se 1 (by rfl) ⟨295394, by rfl⟩ : syracuseStep 393859 = 590789) B590789
theorem B1081997 : Blo 319836 1081997 := bstep (se 3 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 1081997 = 405749) B405749
theorem B1082051 : Blo 319836 1082051 := bstep (se 1 (by rfl) ⟨811538, by rfl⟩ : syracuseStep 1082051 = 1623077) B1623077
theorem B787153 : Blo 319836 787153 := bstep (se 2 (by rfl) ⟨295182, by rfl⟩ : syracuseStep 787153 = 590365) B590365
theorem B3310321 : Blo 319836 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B361219 : Blo 319836 361219 := bstep (se 1 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 361219 = 541829) B541829
theorem B12321557 : Blo 319836 12321557 := bstep (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) B577573
theorem B721745 : Blo 319836 721745 := bstep (se 2 (by rfl) ⟨270654, by rfl⟩ : syracuseStep 721745 = 541309) B541309
theorem B721763 : Blo 319836 721763 := bstep (se 1 (by rfl) ⟨541322, by rfl⟩ : syracuseStep 721763 = 1082645) B1082645
theorem B361363 : Blo 319836 361363 := bstep (se 1 (by rfl) ⟨271022, by rfl⟩ : syracuseStep 361363 = 542045) B542045
theorem B918449 : Blo 319836 918449 := bstep (se 2 (by rfl) ⟨344418, by rfl⟩ : syracuseStep 918449 = 688837) B688837
theorem B1082321 : Blo 319836 1082321 := bstep (se 2 (by rfl) ⟨405870, by rfl⟩ : syracuseStep 1082321 = 811741) B811741
theorem B361507 : Blo 319836 361507 := bstep (se 1 (by rfl) ⟨271130, by rfl⟩ : syracuseStep 361507 = 542261) B542261
theorem B459857 : Blo 319836 459857 := bstep (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) B344893
theorem B984145 : Blo 319836 984145 := bstep (se 2 (by rfl) ⟨369054, by rfl⟩ : syracuseStep 984145 = 738109) B738109
theorem B722033 : Blo 319836 722033 := bstep (se 2 (by rfl) ⟨270762, by rfl⟩ : syracuseStep 722033 = 541525) B541525
theorem B722051 : Blo 319836 722051 := bstep (se 1 (by rfl) ⟨541538, by rfl⟩ : syracuseStep 722051 = 1083077) B1083077
theorem B4392077 : Blo 319836 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B689315 : Blo 319836 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B361651 : Blo 319836 361651 := bstep (se 1 (by rfl) ⟨271238, by rfl⟩ : syracuseStep 361651 = 542477) B542477
theorem B1541425 : Blo 319836 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B5276981 : Blo 319836 5276981 := bstep (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) B494717
theorem B361795 : Blo 319836 361795 := bstep (se 1 (by rfl) ⟨271346, by rfl⟩ : syracuseStep 361795 = 542693) B542693
theorem B722321 : Blo 319836 722321 := bstep (se 2 (by rfl) ⟨270870, by rfl⟩ : syracuseStep 722321 = 541741) B541741
theorem B722339 : Blo 319836 722339 := bstep (se 1 (by rfl) ⟨541754, by rfl⟩ : syracuseStep 722339 = 1083509) B1083509
theorem B361939 : Blo 319836 361939 := bstep (se 1 (by rfl) ⟨271454, by rfl⟩ : syracuseStep 361939 = 542909) B542909
theorem B1082861 : Blo 319836 1082861 := bstep (se 3 (by rfl) ⟨203036, by rfl⟩ : syracuseStep 1082861 = 406073) B406073
theorem B1082915 : Blo 319836 1082915 := bstep (se 1 (by rfl) ⟨812186, by rfl⟩ : syracuseStep 1082915 = 1624373) B1624373
theorem B1312291 : Blo 319836 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B362083 : Blo 319836 362083 := bstep (se 1 (by rfl) ⟨271562, by rfl⟩ : syracuseStep 362083 = 543125) B543125
theorem B722609 : Blo 319836 722609 := bstep (se 2 (by rfl) ⟨270978, by rfl⟩ : syracuseStep 722609 = 541957) B541957
theorem B722627 : Blo 319836 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B362227 : Blo 319836 362227 := bstep (se 1 (by rfl) ⟨271670, by rfl⟩ : syracuseStep 362227 = 543341) B543341
theorem B558881 : Blo 319836 558881 := bstep (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) B419161
theorem B1083185 : Blo 319836 1083185 := bstep (se 2 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 1083185 = 812389) B812389
theorem B362371 : Blo 319836 362371 := bstep (se 1 (by rfl) ⟨271778, by rfl⟩ : syracuseStep 362371 = 543557) B543557
theorem B460723 : Blo 319836 460723 := bstep (se 1 (by rfl) ⟨345542, by rfl⟩ : syracuseStep 460723 = 691085) B691085
theorem B722897 : Blo 319836 722897 := bstep (se 2 (by rfl) ⟨271086, by rfl⟩ : syracuseStep 722897 = 542173) B542173
theorem B722915 : Blo 319836 722915 := bstep (se 1 (by rfl) ⟨542186, by rfl⟩ : syracuseStep 722915 = 1084373) B1084373
theorem B1378289 : Blo 319836 1378289 := bstep (se 2 (by rfl) ⟨516858, by rfl⟩ : syracuseStep 1378289 = 1033717) B1033717
theorem B362515 : Blo 319836 362515 := bstep (se 1 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 362515 = 543773) B543773
theorem B460819 : Blo 319836 460819 := bstep (se 1 (by rfl) ⟨345614, by rfl⟩ : syracuseStep 460819 = 691229) B691229
theorem B493697 : Blo 319836 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B362659 : Blo 319836 362659 := bstep (se 1 (by rfl) ⟨271994, by rfl⟩ : syracuseStep 362659 = 543989) B543989
theorem B723185 : Blo 319836 723185 := bstep (se 2 (by rfl) ⟨271194, by rfl⟩ : syracuseStep 723185 = 542389) B542389
theorem B723203 : Blo 319836 723203 := bstep (se 1 (by rfl) ⟨542402, by rfl⟩ : syracuseStep 723203 = 1084805) B1084805
theorem B362803 : Blo 319836 362803 := bstep (se 1 (by rfl) ⟨272102, by rfl⟩ : syracuseStep 362803 = 544205) B544205
theorem B1083725 : Blo 319836 1083725 := bstep (se 3 (by rfl) ⟨203198, by rfl⟩ : syracuseStep 1083725 = 406397) B406397
theorem B919907 : Blo 319836 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B1083779 : Blo 319836 1083779 := bstep (se 1 (by rfl) ⟨812834, by rfl⟩ : syracuseStep 1083779 = 1625669) B1625669
theorem B362947 : Blo 319836 362947 := bstep (se 1 (by rfl) ⟨272210, by rfl⟩ : syracuseStep 362947 = 544421) B544421
theorem B1477091 : Blo 319836 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B723473 : Blo 319836 723473 := bstep (se 2 (by rfl) ⟨271302, by rfl⟩ : syracuseStep 723473 = 542605) B542605
theorem B723491 : Blo 319836 723491 := bstep (se 1 (by rfl) ⟨542618, by rfl⟩ : syracuseStep 723491 = 1085237) B1085237
theorem B363091 : Blo 319836 363091 := bstep (se 1 (by rfl) ⟨272318, by rfl⟩ : syracuseStep 363091 = 544637) B544637
theorem B1084049 : Blo 319836 1084049 := bstep (se 2 (by rfl) ⟨406518, by rfl⟩ : syracuseStep 1084049 = 813037) B813037
theorem B363235 : Blo 319836 363235 := bstep (se 1 (by rfl) ⟨272426, by rfl⟩ : syracuseStep 363235 = 544853) B544853
theorem B723761 : Blo 319836 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B723779 : Blo 319836 723779 := bstep (se 1 (by rfl) ⟨542834, by rfl⟩ : syracuseStep 723779 = 1085669) B1085669
theorem B1641329 : Blo 319836 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B363379 : Blo 319836 363379 := bstep (se 1 (by rfl) ⟨272534, by rfl⟩ : syracuseStep 363379 = 545069) B545069
theorem B1379213 : Blo 319836 1379213 := bstep (se 3 (by rfl) ⟨258602, by rfl⟩ : syracuseStep 1379213 = 517205) B517205
theorem B1215395 : Blo 319836 1215395 := bstep (se 1 (by rfl) ⟨911546, by rfl⟩ : syracuseStep 1215395 = 1823093) B1823093
theorem B363523 : Blo 319836 363523 := bstep (se 1 (by rfl) ⟨272642, by rfl⟩ : syracuseStep 363523 = 545285) B545285
theorem B724049 : Blo 319836 724049 := bstep (se 2 (by rfl) ⟨271518, by rfl⟩ : syracuseStep 724049 = 543037) B543037
theorem B724067 : Blo 319836 724067 := bstep (se 1 (by rfl) ⟨543050, by rfl⟩ : syracuseStep 724067 = 1086101) B1086101
theorem B920717 : Blo 319836 920717 := bstep (se 3 (by rfl) ⟨172634, by rfl⟩ : syracuseStep 920717 = 345269) B345269
theorem B363667 : Blo 319836 363667 := bstep (se 1 (by rfl) ⟨272750, by rfl⟩ : syracuseStep 363667 = 545501) B545501
theorem B1084589 : Blo 319836 1084589 := bstep (se 3 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 1084589 = 406721) B406721
theorem B1084643 : Blo 319836 1084643 := bstep (se 1 (by rfl) ⟨813482, by rfl⟩ : syracuseStep 1084643 = 1626965) B1626965
theorem B363811 : Blo 319836 363811 := bstep (se 1 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 363811 = 545717) B545717
theorem B920909 : Blo 319836 920909 := bstep (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) B345341
theorem B691537 : Blo 319836 691537 := bstep (se 2 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 691537 = 518653) B518653
theorem B724337 : Blo 319836 724337 := bstep (se 2 (by rfl) ⟨271626, by rfl⟩ : syracuseStep 724337 = 543253) B543253
theorem B724355 : Blo 319836 724355 := bstep (se 1 (by rfl) ⟨543266, by rfl⟩ : syracuseStep 724355 = 1086533) B1086533
theorem B363955 : Blo 319836 363955 := bstep (se 1 (by rfl) ⟨272966, by rfl⟩ : syracuseStep 363955 = 545933) B545933
theorem B1084913 : Blo 319836 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B364099 : Blo 319836 364099 := bstep (se 1 (by rfl) ⟨273074, by rfl⟩ : syracuseStep 364099 = 546149) B546149
theorem B724625 : Blo 319836 724625 := bstep (se 2 (by rfl) ⟨271734, by rfl⟩ : syracuseStep 724625 = 543469) B543469
theorem B724643 : Blo 319836 724643 := bstep (se 1 (by rfl) ⟨543482, by rfl⟩ : syracuseStep 724643 = 1086965) B1086965
theorem B364243 : Blo 319836 364243 := bstep (se 1 (by rfl) ⟨273182, by rfl⟩ : syracuseStep 364243 = 546365) B546365
theorem B1216397 : Blo 319836 1216397 := bstep (se 3 (by rfl) ⟨228074, by rfl⟩ : syracuseStep 1216397 = 456149) B456149
theorem B724913 : Blo 319836 724913 := bstep (se 2 (by rfl) ⟨271842, by rfl⟩ : syracuseStep 724913 = 543685) B543685
theorem B724931 : Blo 319836 724931 := bstep (se 1 (by rfl) ⟨543698, by rfl⟩ : syracuseStep 724931 = 1087397) B1087397
theorem B1085453 : Blo 319836 1085453 := bstep (se 3 (by rfl) ⟨203522, by rfl⟩ : syracuseStep 1085453 = 407045) B407045
theorem B1085507 : Blo 319836 1085507 := bstep (se 1 (by rfl) ⟨814130, by rfl⟩ : syracuseStep 1085507 = 1628261) B1628261
theorem B2429027 : Blo 319836 2429027 := bstep (se 1 (by rfl) ⟨1821770, by rfl⟩ : syracuseStep 2429027 = 3643541) B3643541
theorem B725201 : Blo 319836 725201 := bstep (se 2 (by rfl) ⟨271950, by rfl⟩ : syracuseStep 725201 = 543901) B543901
theorem B725219 : Blo 319836 725219 := bstep (se 1 (by rfl) ⟨543914, by rfl⟩ : syracuseStep 725219 = 1087829) B1087829
theorem B921901 : Blo 319836 921901 := bstep (se 3 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 921901 = 345713) B345713
theorem B1085777 : Blo 319836 1085777 := bstep (se 2 (by rfl) ⟨407166, by rfl⟩ : syracuseStep 1085777 = 814333) B814333
theorem B725489 : Blo 319836 725489 := bstep (se 2 (by rfl) ⟨272058, by rfl⟩ : syracuseStep 725489 = 544117) B544117
theorem B725507 : Blo 319836 725507 := bstep (se 1 (by rfl) ⟨544130, by rfl⟩ : syracuseStep 725507 = 1088261) B1088261
theorem B3707633 : Blo 319836 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B725777 : Blo 319836 725777 := bstep (se 2 (by rfl) ⟨272166, by rfl⟩ : syracuseStep 725777 = 544333) B544333
theorem B725795 : Blo 319836 725795 := bstep (se 1 (by rfl) ⟨544346, by rfl⟩ : syracuseStep 725795 = 1088693) B1088693
theorem B1086317 : Blo 319836 1086317 := bstep (se 3 (by rfl) ⟨203684, by rfl⟩ : syracuseStep 1086317 = 407369) B407369
theorem B2069381 : Blo 319836 2069381 := bstep (se 4 (by rfl) ⟨194004, by rfl⟩ : syracuseStep 2069381 = 388009) B388009
theorem B1545101 : Blo 319836 1545101 := bstep (se 3 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 1545101 = 579413) B579413
theorem B1086371 : Blo 319836 1086371 := bstep (se 1 (by rfl) ⟨814778, by rfl⟩ : syracuseStep 1086371 = 1629557) B1629557
theorem B726065 : Blo 319836 726065 := bstep (se 2 (by rfl) ⟨272274, by rfl⟩ : syracuseStep 726065 = 544549) B544549
theorem B726083 : Blo 319836 726083 := bstep (se 1 (by rfl) ⟨544562, by rfl⟩ : syracuseStep 726083 = 1089125) B1089125
theorem B1086641 : Blo 319836 1086641 := bstep (se 2 (by rfl) ⟨407490, by rfl⟩ : syracuseStep 1086641 = 814981) B814981
theorem B726353 : Blo 319836 726353 := bstep (se 2 (by rfl) ⟨272382, by rfl⟩ : syracuseStep 726353 = 544765) B544765
theorem B726371 : Blo 319836 726371 := bstep (se 1 (by rfl) ⟨544778, by rfl⟩ : syracuseStep 726371 = 1089557) B1089557
theorem B12719501 : Blo 319836 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B365971 : Blo 319836 365971 := bstep (se 1 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 365971 = 548957) B548957
theorem B1840589 : Blo 319836 1840589 := bstep (se 3 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 1840589 = 690221) B690221
theorem B726641 : Blo 319836 726641 := bstep (se 2 (by rfl) ⟨272490, by rfl⟩ : syracuseStep 726641 = 544981) B544981
theorem B726659 : Blo 319836 726659 := bstep (se 1 (by rfl) ⟨544994, by rfl⟩ : syracuseStep 726659 = 1089989) B1089989
theorem B3937933 : Blo 319836 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B1087181 : Blo 319836 1087181 := bstep (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) B407693
theorem B1087235 : Blo 319836 1087235 := bstep (se 1 (by rfl) ⟨815426, by rfl⟩ : syracuseStep 1087235 = 1630853) B1630853
theorem B726929 : Blo 319836 726929 := bstep (se 2 (by rfl) ⟨272598, by rfl⟩ : syracuseStep 726929 = 545197) B545197
theorem B1742755 : Blo 319836 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B726947 : Blo 319836 726947 := bstep (se 1 (by rfl) ⟨545210, by rfl⟩ : syracuseStep 726947 = 1090421) B1090421
theorem B1382321 : Blo 319836 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B1218509 : Blo 319836 1218509 := bstep (se 3 (by rfl) ⟨228470, by rfl⟩ : syracuseStep 1218509 = 456941) B456941
theorem B1087505 : Blo 319836 1087505 := bstep (se 2 (by rfl) ⟨407814, by rfl⟩ : syracuseStep 1087505 = 815629) B815629
theorem B1153187 : Blo 319836 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B923825 : Blo 319836 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B727217 : Blo 319836 727217 := bstep (se 2 (by rfl) ⟨272706, by rfl⟩ : syracuseStep 727217 = 545413) B545413
theorem B727235 : Blo 319836 727235 := bstep (se 1 (by rfl) ⟨545426, by rfl⟩ : syracuseStep 727235 = 1090853) B1090853
theorem B1644877 : Blo 319836 1644877 := bstep (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) B616829
theorem B727505 : Blo 319836 727505 := bstep (se 2 (by rfl) ⟨272814, by rfl⟩ : syracuseStep 727505 = 545629) B545629
theorem B2791907 : Blo 319836 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B727523 : Blo 319836 727523 := bstep (se 1 (by rfl) ⟨545642, by rfl⟩ : syracuseStep 727523 = 1091285) B1091285
theorem B367139 : Blo 319836 367139 := bstep (se 1 (by rfl) ⟨275354, by rfl⟩ : syracuseStep 367139 = 550709) B550709
theorem B1088045 : Blo 319836 1088045 := bstep (se 3 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 1088045 = 408017) B408017
theorem B1088099 : Blo 319836 1088099 := bstep (se 1 (by rfl) ⟨816074, by rfl⟩ : syracuseStep 1088099 = 1632149) B1632149
theorem B531139 : Blo 319836 531139 := bstep (se 1 (by rfl) ⟨398354, by rfl⟩ : syracuseStep 531139 = 796709) B796709
theorem B1219313 : Blo 319836 1219313 := bstep (se 2 (by rfl) ⟨457242, by rfl⟩ : syracuseStep 1219313 = 914485) B914485
theorem B727793 : Blo 319836 727793 := bstep (se 2 (by rfl) ⟨272922, by rfl⟩ : syracuseStep 727793 = 545845) B545845
theorem B727811 : Blo 319836 727811 := bstep (se 1 (by rfl) ⟨545858, by rfl⟩ : syracuseStep 727811 = 1091717) B1091717
theorem B2071331 : Blo 319836 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B5315381 : Blo 319836 5315381 := bstep (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) B498317
theorem B1088369 : Blo 319836 1088369 := bstep (se 2 (by rfl) ⟨408138, by rfl⟩ : syracuseStep 1088369 = 816277) B816277
theorem B728081 : Blo 319836 728081 := bstep (se 2 (by rfl) ⟨273030, by rfl⟩ : syracuseStep 728081 = 546061) B546061
theorem B728099 : Blo 319836 728099 := bstep (se 1 (by rfl) ⟨546074, by rfl⟩ : syracuseStep 728099 = 1092149) B1092149
theorem B1121539 : Blo 319836 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B728369 : Blo 319836 728369 := bstep (se 2 (by rfl) ⟨273138, by rfl⟩ : syracuseStep 728369 = 546277) B546277
theorem B728387 : Blo 319836 728387 := bstep (se 1 (by rfl) ⟨546290, by rfl⟩ : syracuseStep 728387 = 1092581) B1092581
theorem B1219981 : Blo 319836 1219981 := bstep (se 3 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 1219981 = 457493) B457493
theorem B1088909 : Blo 319836 1088909 := bstep (se 3 (by rfl) ⟨204170, by rfl⟩ : syracuseStep 1088909 = 408341) B408341
theorem B1088963 : Blo 319836 1088963 := bstep (se 1 (by rfl) ⟨816722, by rfl⟩ : syracuseStep 1088963 = 1633445) B1633445
theorem B1744355 : Blo 319836 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B433667 : Blo 319836 433667 := bstep (se 1 (by rfl) ⟨325250, by rfl⟩ : syracuseStep 433667 = 650501) B650501
theorem B1842821 : Blo 319836 1842821 := bstep (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) B345529
theorem B1089233 : Blo 319836 1089233 := bstep (se 2 (by rfl) ⟨408462, by rfl⟩ : syracuseStep 1089233 = 816925) B816925
theorem B1220771 : Blo 319836 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B1089773 : Blo 319836 1089773 := bstep (se 3 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 1089773 = 408665) B408665
theorem B1089827 : Blo 319836 1089827 := bstep (se 1 (by rfl) ⟨817370, by rfl⟩ : syracuseStep 1089827 = 1634741) B1634741
theorem B1843505 : Blo 319836 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B3678533 : Blo 319836 3678533 := bstep (se 4 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 3678533 = 689725) B689725
theorem B1745329 : Blo 319836 1745329 := bstep (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) B1308997
theorem B434689 : Blo 319836 434689 := bstep (se 2 (by rfl) ⟨163008, by rfl⟩ : syracuseStep 434689 = 326017) B326017
theorem B434705 : Blo 319836 434705 := bstep (se 2 (by rfl) ⟨163014, by rfl⟩ : syracuseStep 434705 = 326029) B326029
theorem B434737 : Blo 319836 434737 := bstep (se 2 (by rfl) ⟨163026, by rfl⟩ : syracuseStep 434737 = 326053) B326053
theorem B1090097 : Blo 319836 1090097 := bstep (se 2 (by rfl) ⟨408786, by rfl⟩ : syracuseStep 1090097 = 817573) B817573
theorem B1221425 : Blo 319836 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B1024849 : Blo 319836 1024849 := bstep (se 2 (by rfl) ⟨384318, by rfl⟩ : syracuseStep 1024849 = 768637) B768637
theorem B435235 : Blo 319836 435235 := bstep (se 1 (by rfl) ⟨326426, by rfl⟩ : syracuseStep 435235 = 652853) B652853
theorem B1090637 : Blo 319836 1090637 := bstep (se 3 (by rfl) ⟨204494, by rfl⟩ : syracuseStep 1090637 = 408989) B408989
theorem B1090691 : Blo 319836 1090691 := bstep (se 1 (by rfl) ⟨818018, by rfl⟩ : syracuseStep 1090691 = 1636037) B1636037
theorem B1156301 : Blo 319836 1156301 := bstep (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) B433613
theorem B2073869 : Blo 319836 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B2434373 : Blo 319836 2434373 := bstep (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) B456445
theorem B12166541 : Blo 319836 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B1090961 : Blo 319836 1090961 := bstep (se 2 (by rfl) ⟨409110, by rfl⟩ : syracuseStep 1090961 = 818221) B818221
theorem B1025453 : Blo 319836 1025453 := bstep (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) B384545
theorem B4368013 : Blo 319836 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B1746821 : Blo 319836 1746821 := bstep (se 4 (by rfl) ⟨163764, by rfl⟩ : syracuseStep 1746821 = 327529) B327529
theorem B1091501 : Blo 319836 1091501 := bstep (se 3 (by rfl) ⟨204656, by rfl⟩ : syracuseStep 1091501 = 409313) B409313
theorem B1091555 : Blo 319836 1091555 := bstep (se 1 (by rfl) ⟨818666, by rfl⟩ : syracuseStep 1091555 = 1637333) B1637333
theorem B1222883 : Blo 319836 1222883 := bstep (se 1 (by rfl) ⟨917162, by rfl⟩ : syracuseStep 1222883 = 1834325) B1834325
theorem B1222897 : Blo 319836 1222897 := bstep (se 2 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 1222897 = 917173) B917173
theorem B1091825 : Blo 319836 1091825 := bstep (se 2 (by rfl) ⟨409434, by rfl⟩ : syracuseStep 1091825 = 818869) B818869
theorem B2959715 : Blo 319836 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B1878563 : Blo 319836 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1092365 : Blo 319836 1092365 := bstep (se 3 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 1092365 = 409637) B409637
theorem B371491 : Blo 319836 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B1092419 : Blo 319836 1092419 := bstep (se 1 (by rfl) ⟨819314, by rfl⟩ : syracuseStep 1092419 = 1638629) B1638629
theorem B699313 : Blo 319836 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B1092689 : Blo 319836 1092689 := bstep (se 2 (by rfl) ⟨409758, by rfl⟩ : syracuseStep 1092689 = 819517) B819517
theorem B732451 : Blo 319836 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B404995 : Blo 319836 404995 := bstep (se 1 (by rfl) ⟨303746, by rfl⟩ : syracuseStep 404995 = 607493) B607493
theorem B405091 : Blo 319836 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B929411 : Blo 319836 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B1224355 : Blo 319836 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B1683149 : Blo 319836 1683149 := bstep (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) B631181
theorem B1322801 : Blo 319836 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B1290289 : Blo 319836 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B405587 : Blo 319836 405587 := bstep (se 1 (by rfl) ⟨304190, by rfl⟩ : syracuseStep 405587 = 608381) B608381
theorem B733475 : Blo 319836 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B864803 : Blo 319836 864803 := bstep (se 1 (by rfl) ⟨648602, by rfl⟩ : syracuseStep 864803 = 1297205) B1297205
theorem B864913 : Blo 319836 864913 := bstep (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) B648685
theorem B1028771 : Blo 319836 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B1913507 : Blo 319836 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B406291 : Blo 319836 406291 := bstep (se 1 (by rfl) ⟨304718, by rfl⟩ : syracuseStep 406291 = 609437) B609437
theorem B406387 : Blo 319836 406387 := bstep (se 1 (by rfl) ⟨304790, by rfl⟩ : syracuseStep 406387 = 609581) B609581
theorem B3093389 : Blo 319836 3093389 := bstep (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) B1160021
theorem B4109237 : Blo 319836 4109237 := bstep (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) B385241
theorem B406883 : Blo 319836 406883 := bstep (se 1 (by rfl) ⟨305162, by rfl⟩ : syracuseStep 406883 = 610325) B610325
theorem B865745 : Blo 319836 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B1029617 : Blo 319836 1029617 := bstep (se 2 (by rfl) ⟨386106, by rfl⟩ : syracuseStep 1029617 = 772213) B772213
theorem B1947149 : Blo 319836 1947149 := bstep (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) B730181
theorem B1848845 : Blo 319836 1848845 := bstep (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) B693317
theorem B1029667 : Blo 319836 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B1226573 : Blo 319836 1226573 := bstep (se 3 (by rfl) ⟨229982, by rfl⟩ : syracuseStep 1226573 = 459965) B459965
theorem B3684365 : Blo 319836 3684365 := bstep (se 3 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 3684365 = 1381637) B1381637
theorem B407587 : Blo 319836 407587 := bstep (se 1 (by rfl) ⟨305690, by rfl⟩ : syracuseStep 407587 = 611381) B611381
theorem B407683 : Blo 319836 407683 := bstep (se 1 (by rfl) ⟨305762, by rfl⟩ : syracuseStep 407683 = 611525) B611525
theorem B342163 : Blo 319836 342163 := bstep (se 1 (by rfl) ⟨256622, by rfl⟩ : syracuseStep 342163 = 513245) B513245
theorem B1620323 : Blo 319836 1620323 := bstep (se 1 (by rfl) ⟨1215242, by rfl⟩ : syracuseStep 1620323 = 2430485) B2430485
theorem B408179 : Blo 319836 408179 := bstep (se 1 (by rfl) ⟨306134, by rfl⟩ : syracuseStep 408179 = 612269) B612269
theorem B735875 : Blo 319836 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B1948387 : Blo 319836 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B1030897 : Blo 319836 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B342787 : Blo 319836 342787 := bstep (se 1 (by rfl) ⟨257090, by rfl⟩ : syracuseStep 342787 = 514181) B514181
theorem B6175541 : Blo 319836 6175541 := bstep (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) B578957
theorem B2735117 : Blo 319836 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B2440205 : Blo 319836 2440205 := bstep (se 3 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 2440205 = 915077) B915077
theorem B539777 : Blo 319836 539777 := bstep (se 2 (by rfl) ⟨202416, by rfl⟩ : syracuseStep 539777 = 404833) B404833
theorem B1621133 : Blo 319836 1621133 := bstep (se 3 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 1621133 = 607925) B607925
theorem B933041 : Blo 319836 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B539905 : Blo 319836 539905 := bstep (se 2 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 539905 = 404929) B404929
theorem B539939 : Blo 319836 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B408883 : Blo 319836 408883 := bstep (se 1 (by rfl) ⟨306662, by rfl⟩ : syracuseStep 408883 = 613325) B613325
theorem B408979 : Blo 319836 408979 := bstep (se 1 (by rfl) ⟨306734, by rfl⟩ : syracuseStep 408979 = 613469) B613469
theorem B540067 : Blo 319836 540067 := bstep (se 1 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 540067 = 810101) B810101
theorem B769475 : Blo 319836 769475 := bstep (se 1 (by rfl) ⟨577106, by rfl⟩ : syracuseStep 769475 = 1154213) B1154213
theorem B5848517 : Blo 319836 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B835043 : Blo 319836 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B540209 : Blo 319836 540209 := bstep (se 2 (by rfl) ⟨202578, by rfl⟩ : syracuseStep 540209 = 405157) B405157
theorem B540337 : Blo 319836 540337 := bstep (se 2 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 540337 = 405253) B405253
theorem B540371 : Blo 319836 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B540499 : Blo 319836 540499 := bstep (se 1 (by rfl) ⟨405374, by rfl⟩ : syracuseStep 540499 = 810749) B810749
theorem B409475 : Blo 319836 409475 := bstep (se 1 (by rfl) ⟨307106, by rfl⟩ : syracuseStep 409475 = 614213) B614213
theorem B1032077 : Blo 319836 1032077 := bstep (se 3 (by rfl) ⟨193514, by rfl⟩ : syracuseStep 1032077 = 387029) B387029
theorem B540641 : Blo 319836 540641 := bstep (se 2 (by rfl) ⟨202740, by rfl⟩ : syracuseStep 540641 = 405481) B405481
theorem B540769 : Blo 319836 540769 := bstep (se 2 (by rfl) ⟨202788, by rfl⟩ : syracuseStep 540769 = 405577) B405577
theorem B540803 : Blo 319836 540803 := bstep (se 1 (by rfl) ⟨405602, by rfl⟩ : syracuseStep 540803 = 811205) B811205
theorem B540931 : Blo 319836 540931 := bstep (se 1 (by rfl) ⟨405698, by rfl⟩ : syracuseStep 540931 = 811397) B811397
theorem B541073 : Blo 319836 541073 := bstep (se 2 (by rfl) ⟨202902, by rfl⟩ : syracuseStep 541073 = 405805) B405805
theorem B541201 : Blo 319836 541201 := bstep (se 2 (by rfl) ⟨202950, by rfl⟩ : syracuseStep 541201 = 405901) B405901
theorem B7225877 : Blo 319836 7225877 := bstep (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) B338713
theorem B541235 : Blo 319836 541235 := bstep (se 1 (by rfl) ⟨405926, by rfl⟩ : syracuseStep 541235 = 811853) B811853
theorem B344675 : Blo 319836 344675 := bstep (se 1 (by rfl) ⟨258506, by rfl⟩ : syracuseStep 344675 = 517013) B517013
theorem B770705 : Blo 319836 770705 := bstep (se 2 (by rfl) ⟨289014, by rfl⟩ : syracuseStep 770705 = 578029) B578029
theorem B1229489 : Blo 319836 1229489 := bstep (se 2 (by rfl) ⟨461058, by rfl⟩ : syracuseStep 1229489 = 922117) B922117
theorem B541363 : Blo 319836 541363 := bstep (se 1 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 541363 = 812045) B812045
theorem B541505 : Blo 319836 541505 := bstep (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) B406129
theorem B3687281 : Blo 319836 3687281 := bstep (se 2 (by rfl) ⟨1382730, by rfl⟩ : syracuseStep 3687281 = 2765461) B2765461
theorem B541633 : Blo 319836 541633 := bstep (se 2 (by rfl) ⟨203112, by rfl⟩ : syracuseStep 541633 = 406225) B406225
theorem B541667 : Blo 319836 541667 := bstep (se 1 (by rfl) ⟨406250, by rfl⟩ : syracuseStep 541667 = 812501) B812501
theorem B1098787 : Blo 319836 1098787 := bstep (se 1 (by rfl) ⟨824090, by rfl⟩ : syracuseStep 1098787 = 1648181) B1648181
theorem B541795 : Blo 319836 541795 := bstep (se 1 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 541795 = 812693) B812693
theorem B7554161 : Blo 319836 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B607409 : Blo 319836 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B541937 : Blo 319836 541937 := bstep (se 2 (by rfl) ⟨203226, by rfl⟩ : syracuseStep 541937 = 406453) B406453
theorem B542065 : Blo 319836 542065 := bstep (se 2 (by rfl) ⟨203274, by rfl⟩ : syracuseStep 542065 = 406549) B406549
theorem B542099 : Blo 319836 542099 := bstep (se 1 (by rfl) ⟨406574, by rfl⟩ : syracuseStep 542099 = 813149) B813149
theorem B542227 : Blo 319836 542227 := bstep (se 1 (by rfl) ⟨406670, by rfl⟩ : syracuseStep 542227 = 813341) B813341
theorem B1033859 : Blo 319836 1033859 := bstep (se 1 (by rfl) ⟨775394, by rfl⟩ : syracuseStep 1033859 = 1550789) B1550789
theorem B542369 : Blo 319836 542369 := bstep (se 2 (by rfl) ⟨203388, by rfl⟩ : syracuseStep 542369 = 406777) B406777
theorem B542497 : Blo 319836 542497 := bstep (se 2 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 542497 = 406873) B406873
theorem B542531 : Blo 319836 542531 := bstep (se 1 (by rfl) ⟨406898, by rfl⟩ : syracuseStep 542531 = 813797) B813797
theorem B2475845 : Blo 319836 2475845 := bstep (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) B464221
theorem B411491 : Blo 319836 411491 := bstep (se 1 (by rfl) ⟨308618, by rfl⟩ : syracuseStep 411491 = 617237) B617237
theorem B2443121 : Blo 319836 2443121 := bstep (se 2 (by rfl) ⟨916170, by rfl⟩ : syracuseStep 2443121 = 1832341) B1832341
theorem B542659 : Blo 319836 542659 := bstep (se 1 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 542659 = 813989) B813989
theorem B444371 : Blo 319836 444371 := bstep (se 1 (by rfl) ⟨333278, by rfl⟩ : syracuseStep 444371 = 666557) B666557
theorem B1624049 : Blo 319836 1624049 := bstep (se 2 (by rfl) ⟨609018, by rfl⟩ : syracuseStep 1624049 = 1218037) B1218037
theorem B870385 : Blo 319836 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B608305 : Blo 319836 608305 := bstep (se 2 (by rfl) ⟨228114, by rfl⟩ : syracuseStep 608305 = 456229) B456229
theorem B542801 : Blo 319836 542801 := bstep (se 2 (by rfl) ⟨203550, by rfl⟩ : syracuseStep 542801 = 407101) B407101
theorem B2050211 : Blo 319836 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B608465 : Blo 319836 608465 := bstep (se 2 (by rfl) ⟨228174, by rfl⟩ : syracuseStep 608465 = 456349) B456349
theorem B542929 : Blo 319836 542929 := bstep (se 2 (by rfl) ⟨203598, by rfl⟩ : syracuseStep 542929 = 407197) B407197
theorem B542963 : Blo 319836 542963 := bstep (se 1 (by rfl) ⟨407222, by rfl⟩ : syracuseStep 542963 = 814445) B814445
theorem B543091 : Blo 319836 543091 := bstep (se 1 (by rfl) ⟨407318, by rfl⟩ : syracuseStep 543091 = 814637) B814637
theorem B543233 : Blo 319836 543233 := bstep (se 2 (by rfl) ⟨203712, by rfl⟩ : syracuseStep 543233 = 407425) B407425
theorem B1165873 : Blo 319836 1165873 := bstep (se 2 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 1165873 = 874405) B874405
theorem B608867 : Blo 319836 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B543361 : Blo 319836 543361 := bstep (se 2 (by rfl) ⟨203760, by rfl⟩ : syracuseStep 543361 = 407521) B407521
theorem B543395 : Blo 319836 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B1034947 : Blo 319836 1034947 := bstep (se 1 (by rfl) ⟨776210, by rfl⟩ : syracuseStep 1034947 = 1552421) B1552421
theorem B543523 : Blo 319836 543523 := bstep (se 1 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 543523 = 815285) B815285
theorem B1035089 : Blo 319836 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B543665 : Blo 319836 543665 := bstep (se 2 (by rfl) ⟨203874, by rfl⟩ : syracuseStep 543665 = 407749) B407749
theorem B773059 : Blo 319836 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B1166321 : Blo 319836 1166321 := bstep (se 2 (by rfl) ⟨437370, by rfl⟩ : syracuseStep 1166321 = 874741) B874741
theorem B543793 : Blo 319836 543793 := bstep (se 2 (by rfl) ⟨203922, by rfl⟩ : syracuseStep 543793 = 407845) B407845
theorem B543827 : Blo 319836 543827 := bstep (se 1 (by rfl) ⟨407870, by rfl⟩ : syracuseStep 543827 = 815741) B815741
theorem B543955 : Blo 319836 543955 := bstep (se 1 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 543955 = 815933) B815933
theorem B871661 : Blo 319836 871661 := bstep (se 3 (by rfl) ⟨163436, by rfl⟩ : syracuseStep 871661 = 326873) B326873
theorem B544097 : Blo 319836 544097 := bstep (se 2 (by rfl) ⟨204036, by rfl⟩ : syracuseStep 544097 = 408073) B408073
theorem B1625507 : Blo 319836 1625507 := bstep (se 1 (by rfl) ⟨1219130, by rfl⟩ : syracuseStep 1625507 = 2438261) B2438261
theorem B544225 : Blo 319836 544225 := bstep (se 2 (by rfl) ⟨204084, by rfl⟩ : syracuseStep 544225 = 408169) B408169
theorem B609763 : Blo 319836 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B544259 : Blo 319836 544259 := bstep (se 1 (by rfl) ⟨408194, by rfl⟩ : syracuseStep 544259 = 816389) B816389
theorem B609923 : Blo 319836 609923 := bstep (se 1 (by rfl) ⟨457442, by rfl⟩ : syracuseStep 609923 = 914885) B914885
theorem B544387 : Blo 319836 544387 := bstep (se 1 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 544387 = 816581) B816581
theorem B544529 : Blo 319836 544529 := bstep (se 2 (by rfl) ⟨204198, by rfl⟩ : syracuseStep 544529 = 408397) B408397
theorem B544657 : Blo 319836 544657 := bstep (se 2 (by rfl) ⟨204246, by rfl⟩ : syracuseStep 544657 = 408493) B408493
theorem B544691 : Blo 319836 544691 := bstep (se 1 (by rfl) ⟨408518, by rfl⟩ : syracuseStep 544691 = 817037) B817037
theorem B1822661 : Blo 319836 1822661 := bstep (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) B341749
theorem B774193 : Blo 319836 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B544819 : Blo 319836 544819 := bstep (se 1 (by rfl) ⟨408614, by rfl⟩ : syracuseStep 544819 = 817229) B817229
theorem B872525 : Blo 319836 872525 := bstep (se 3 (by rfl) ⟨163598, by rfl⟩ : syracuseStep 872525 = 327197) B327197
theorem B872579 : Blo 319836 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B774289 : Blo 319836 774289 := bstep (se 2 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 774289 = 580717) B580717
theorem B1036433 : Blo 319836 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B544961 : Blo 319836 544961 := bstep (se 2 (by rfl) ⟨204360, by rfl⟩ : syracuseStep 544961 = 408721) B408721
theorem B1626317 : Blo 319836 1626317 := bstep (se 3 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 1626317 = 609869) B609869
theorem B1102061 : Blo 319836 1102061 := bstep (se 3 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 1102061 = 413273) B413273
theorem B2937073 : Blo 319836 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B774403 : Blo 319836 774403 := bstep (se 1 (by rfl) ⟨580802, by rfl⟩ : syracuseStep 774403 = 1161605) B1161605
theorem B1364273 : Blo 319836 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B545089 : Blo 319836 545089 := bstep (se 2 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 545089 = 408817) B408817
theorem B774481 : Blo 319836 774481 := bstep (se 2 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 774481 = 580861) B580861
theorem B3297635 : Blo 319836 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B545123 : Blo 319836 545123 := bstep (se 1 (by rfl) ⟨408842, by rfl⟩ : syracuseStep 545123 = 817685) B817685
theorem B512419 : Blo 319836 512419 := bstep (se 1 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 512419 = 768629) B768629
theorem B545251 : Blo 319836 545251 := bstep (se 1 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 545251 = 817877) B817877
theorem B479777 : Blo 319836 479777 := bstep (se 2 (by rfl) ⟨179916, by rfl⟩ : syracuseStep 479777 = 359833) B359833
theorem B479795 : Blo 319836 479795 := bstep (se 1 (by rfl) ⟨359846, by rfl⟩ : syracuseStep 479795 = 719693) B719693
theorem B479825 : Blo 319836 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B479843 : Blo 319836 479843 := bstep (se 1 (by rfl) ⟨359882, by rfl⟩ : syracuseStep 479843 = 719765) B719765
theorem B545393 : Blo 319836 545393 := bstep (se 2 (by rfl) ⟨204522, by rfl⟩ : syracuseStep 545393 = 409045) B409045
theorem B479873 : Blo 319836 479873 := bstep (se 2 (by rfl) ⟨179952, by rfl⟩ : syracuseStep 479873 = 359905) B359905
theorem B479891 : Blo 319836 479891 := bstep (se 1 (by rfl) ⟨359918, by rfl⟩ : syracuseStep 479891 = 719837) B719837
theorem B479921 : Blo 319836 479921 := bstep (se 2 (by rfl) ⟨179970, by rfl⟩ : syracuseStep 479921 = 359941) B359941
theorem B610993 : Blo 319836 610993 := bstep (se 2 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 610993 = 458245) B458245
theorem B479939 : Blo 319836 479939 := bstep (se 1 (by rfl) ⟨359954, by rfl⟩ : syracuseStep 479939 = 719909) B719909
theorem B479969 : Blo 319836 479969 := bstep (se 2 (by rfl) ⟨179988, by rfl⟩ : syracuseStep 479969 = 359977) B359977
theorem B545521 : Blo 319836 545521 := bstep (se 2 (by rfl) ⟨204570, by rfl⟩ : syracuseStep 545521 = 409141) B409141
theorem B479987 : Blo 319836 479987 := bstep (se 1 (by rfl) ⟨359990, by rfl⟩ : syracuseStep 479987 = 719981) B719981
theorem B480017 : Blo 319836 480017 := bstep (se 2 (by rfl) ⟨180006, by rfl⟩ : syracuseStep 480017 = 360013) B360013
theorem B545555 : Blo 319836 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B480035 : Blo 319836 480035 := bstep (se 1 (by rfl) ⟨360026, by rfl⟩ : syracuseStep 480035 = 720053) B720053
theorem B480065 : Blo 319836 480065 := bstep (se 2 (by rfl) ⟨180024, by rfl⟩ : syracuseStep 480065 = 360049) B360049
theorem B480083 : Blo 319836 480083 := bstep (se 1 (by rfl) ⟨360062, by rfl⟩ : syracuseStep 480083 = 720125) B720125
theorem B480113 : Blo 319836 480113 := bstep (se 2 (by rfl) ⟨180042, by rfl⟩ : syracuseStep 480113 = 360085) B360085
theorem B480131 : Blo 319836 480131 := bstep (se 1 (by rfl) ⟨360098, by rfl⟩ : syracuseStep 480131 = 720197) B720197
theorem B545683 : Blo 319836 545683 := bstep (se 1 (by rfl) ⟨409262, by rfl⟩ : syracuseStep 545683 = 818525) B818525
theorem B480161 : Blo 319836 480161 := bstep (se 2 (by rfl) ⟨180060, by rfl⟩ : syracuseStep 480161 = 360121) B360121
theorem B480179 : Blo 319836 480179 := bstep (se 1 (by rfl) ⟨360134, by rfl⟩ : syracuseStep 480179 = 720269) B720269
theorem B480209 : Blo 319836 480209 := bstep (se 2 (by rfl) ⟨180078, by rfl⟩ : syracuseStep 480209 = 360157) B360157
theorem B480227 : Blo 319836 480227 := bstep (se 1 (by rfl) ⟨360170, by rfl⟩ : syracuseStep 480227 = 720341) B720341
theorem B480257 : Blo 319836 480257 := bstep (se 2 (by rfl) ⟨180096, by rfl⟩ : syracuseStep 480257 = 360193) B360193
theorem B480275 : Blo 319836 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B545825 : Blo 319836 545825 := bstep (se 2 (by rfl) ⟨204684, by rfl⟩ : syracuseStep 545825 = 409369) B409369
theorem B1037357 : Blo 319836 1037357 := bstep (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) B389009
theorem B480305 : Blo 319836 480305 := bstep (se 2 (by rfl) ⟨180114, by rfl⟩ : syracuseStep 480305 = 360229) B360229
theorem B480323 : Blo 319836 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B513091 : Blo 319836 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B480353 : Blo 319836 480353 := bstep (se 2 (by rfl) ⟨180132, by rfl⟩ : syracuseStep 480353 = 360265) B360265
theorem B513137 : Blo 319836 513137 := bstep (se 2 (by rfl) ⟨192426, by rfl⟩ : syracuseStep 513137 = 384853) B384853
theorem B480371 : Blo 319836 480371 := bstep (se 1 (by rfl) ⟨360278, by rfl⟩ : syracuseStep 480371 = 720557) B720557
theorem B480401 : Blo 319836 480401 := bstep (se 2 (by rfl) ⟨180150, by rfl⟩ : syracuseStep 480401 = 360301) B360301
theorem B545953 : Blo 319836 545953 := bstep (se 2 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 545953 = 409465) B409465
theorem B480419 : Blo 319836 480419 := bstep (se 1 (by rfl) ⟨360314, by rfl⟩ : syracuseStep 480419 = 720629) B720629
theorem B480449 : Blo 319836 480449 := bstep (se 2 (by rfl) ⟨180168, by rfl⟩ : syracuseStep 480449 = 360337) B360337
theorem B545987 : Blo 319836 545987 := bstep (se 1 (by rfl) ⟨409490, by rfl⟩ : syracuseStep 545987 = 818981) B818981
theorem B480467 : Blo 319836 480467 := bstep (se 1 (by rfl) ⟨360350, by rfl⟩ : syracuseStep 480467 = 720701) B720701
theorem B480497 : Blo 319836 480497 := bstep (se 2 (by rfl) ⟨180186, by rfl⟩ : syracuseStep 480497 = 360373) B360373
theorem B873713 : Blo 319836 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B480515 : Blo 319836 480515 := bstep (se 1 (by rfl) ⟨360386, by rfl⟩ : syracuseStep 480515 = 720773) B720773
theorem B480545 : Blo 319836 480545 := bstep (se 2 (by rfl) ⟨180204, by rfl⟩ : syracuseStep 480545 = 360409) B360409
theorem B480563 : Blo 319836 480563 := bstep (se 1 (by rfl) ⟨360422, by rfl⟩ : syracuseStep 480563 = 720845) B720845
theorem B546115 : Blo 319836 546115 := bstep (se 1 (by rfl) ⟨409586, by rfl⟩ : syracuseStep 546115 = 819173) B819173
theorem B480593 : Blo 319836 480593 := bstep (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) B360445
theorem B480611 : Blo 319836 480611 := bstep (se 1 (by rfl) ⟨360458, by rfl⟩ : syracuseStep 480611 = 720917) B720917
theorem B578915 : Blo 319836 578915 := bstep (se 1 (by rfl) ⟨434186, by rfl⟩ : syracuseStep 578915 = 868373) B868373
theorem B578929 : Blo 319836 578929 := bstep (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) B434197
theorem B480641 : Blo 319836 480641 := bstep (se 2 (by rfl) ⟨180240, by rfl⟩ : syracuseStep 480641 = 360481) B360481
theorem B480659 : Blo 319836 480659 := bstep (se 1 (by rfl) ⟨360494, by rfl⟩ : syracuseStep 480659 = 720989) B720989
theorem B480689 : Blo 319836 480689 := bstep (se 2 (by rfl) ⟨180258, by rfl⟩ : syracuseStep 480689 = 360517) B360517
theorem B480707 : Blo 319836 480707 := bstep (se 1 (by rfl) ⟨360530, by rfl⟩ : syracuseStep 480707 = 721061) B721061
theorem B546257 : Blo 319836 546257 := bstep (se 2 (by rfl) ⟨204846, by rfl⟩ : syracuseStep 546257 = 409693) B409693
theorem B480737 : Blo 319836 480737 := bstep (se 2 (by rfl) ⟨180276, by rfl⟩ : syracuseStep 480737 = 360553) B360553
theorem B480755 : Blo 319836 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B480785 : Blo 319836 480785 := bstep (se 2 (by rfl) ⟨180294, by rfl⟩ : syracuseStep 480785 = 360589) B360589
theorem B579089 : Blo 319836 579089 := bstep (se 2 (by rfl) ⟨217158, by rfl⟩ : syracuseStep 579089 = 434317) B434317
theorem B480803 : Blo 319836 480803 := bstep (se 1 (by rfl) ⟨360602, by rfl⟩ : syracuseStep 480803 = 721205) B721205
theorem B480833 : Blo 319836 480833 := bstep (se 2 (by rfl) ⟨180312, by rfl⟩ : syracuseStep 480833 = 360625) B360625
theorem B874061 : Blo 319836 874061 := bstep (se 3 (by rfl) ⟨163886, by rfl⟩ : syracuseStep 874061 = 327773) B327773
theorem B546385 : Blo 319836 546385 := bstep (se 2 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 546385 = 409789) B409789
theorem B480851 : Blo 319836 480851 := bstep (se 1 (by rfl) ⟨360638, by rfl⟩ : syracuseStep 480851 = 721277) B721277
theorem B480881 : Blo 319836 480881 := bstep (se 2 (by rfl) ⟨180330, by rfl⟩ : syracuseStep 480881 = 360661) B360661
theorem B513649 : Blo 319836 513649 := bstep (se 2 (by rfl) ⟨192618, by rfl⟩ : syracuseStep 513649 = 385237) B385237
theorem B546419 : Blo 319836 546419 := bstep (se 1 (by rfl) ⟨409814, by rfl⟩ : syracuseStep 546419 = 819629) B819629
theorem B480899 : Blo 319836 480899 := bstep (se 1 (by rfl) ⟨360674, by rfl⟩ : syracuseStep 480899 = 721349) B721349
theorem B480929 : Blo 319836 480929 := bstep (se 2 (by rfl) ⟨180348, by rfl⟩ : syracuseStep 480929 = 360697) B360697
theorem B480947 : Blo 319836 480947 := bstep (se 1 (by rfl) ⟨360710, by rfl⟩ : syracuseStep 480947 = 721421) B721421
theorem B480977 : Blo 319836 480977 := bstep (se 2 (by rfl) ⟨180366, by rfl⟩ : syracuseStep 480977 = 360733) B360733
theorem B612049 : Blo 319836 612049 := bstep (se 2 (by rfl) ⟨229518, by rfl⟩ : syracuseStep 612049 = 459037) B459037
theorem B480995 : Blo 319836 480995 := bstep (se 1 (by rfl) ⟨360746, by rfl⟩ : syracuseStep 480995 = 721493) B721493
theorem B481025 : Blo 319836 481025 := bstep (se 2 (by rfl) ⟨180384, by rfl⟩ : syracuseStep 481025 = 360769) B360769
theorem B481043 : Blo 319836 481043 := bstep (se 1 (by rfl) ⟨360782, by rfl⟩ : syracuseStep 481043 = 721565) B721565
theorem B481073 : Blo 319836 481073 := bstep (se 2 (by rfl) ⟨180402, by rfl⟩ : syracuseStep 481073 = 360805) B360805
theorem B481091 : Blo 319836 481091 := bstep (se 1 (by rfl) ⟨360818, by rfl⟩ : syracuseStep 481091 = 721637) B721637
theorem B3102533 : Blo 319836 3102533 := bstep (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) B581725
theorem B481121 : Blo 319836 481121 := bstep (se 2 (by rfl) ⟨180420, by rfl⟩ : syracuseStep 481121 = 360841) B360841
theorem B481139 : Blo 319836 481139 := bstep (se 1 (by rfl) ⟨360854, by rfl⟩ : syracuseStep 481139 = 721709) B721709
theorem B481169 : Blo 319836 481169 := bstep (se 2 (by rfl) ⟨180438, by rfl⟩ : syracuseStep 481169 = 360877) B360877
theorem B481187 : Blo 319836 481187 := bstep (se 1 (by rfl) ⟨360890, by rfl⟩ : syracuseStep 481187 = 721781) B721781
theorem B481217 : Blo 319836 481217 := bstep (se 2 (by rfl) ⟨180456, by rfl⟩ : syracuseStep 481217 = 360913) B360913
theorem B481235 : Blo 319836 481235 := bstep (se 1 (by rfl) ⟨360926, by rfl⟩ : syracuseStep 481235 = 721853) B721853
theorem B481265 : Blo 319836 481265 := bstep (se 2 (by rfl) ⟨180474, by rfl⟩ : syracuseStep 481265 = 360949) B360949
theorem B481283 : Blo 319836 481283 := bstep (se 1 (by rfl) ⟨360962, by rfl⟩ : syracuseStep 481283 = 721925) B721925
theorem B481313 : Blo 319836 481313 := bstep (se 2 (by rfl) ⟨180492, by rfl⟩ : syracuseStep 481313 = 360985) B360985
theorem B481331 : Blo 319836 481331 := bstep (se 1 (by rfl) ⟨360998, by rfl⟩ : syracuseStep 481331 = 721997) B721997
theorem B481361 : Blo 319836 481361 := bstep (se 2 (by rfl) ⟨180510, by rfl⟩ : syracuseStep 481361 = 361021) B361021
theorem B481379 : Blo 319836 481379 := bstep (se 1 (by rfl) ⟨361034, by rfl⟩ : syracuseStep 481379 = 722069) B722069
theorem B612451 : Blo 319836 612451 := bstep (se 1 (by rfl) ⟨459338, by rfl⟩ : syracuseStep 612451 = 918677) B918677
theorem B481409 : Blo 319836 481409 := bstep (se 2 (by rfl) ⟨180528, by rfl⟩ : syracuseStep 481409 = 361057) B361057
theorem B514193 : Blo 319836 514193 := bstep (se 2 (by rfl) ⟨192822, by rfl⟩ : syracuseStep 514193 = 385645) B385645
theorem B612497 : Blo 319836 612497 := bstep (se 2 (by rfl) ⟨229686, by rfl⟩ : syracuseStep 612497 = 459373) B459373
theorem B481427 : Blo 319836 481427 := bstep (se 1 (by rfl) ⟨361070, by rfl⟩ : syracuseStep 481427 = 722141) B722141
theorem B841873 : Blo 319836 841873 := bstep (se 2 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 841873 = 631405) B631405
theorem B481457 : Blo 319836 481457 := bstep (se 2 (by rfl) ⟨180546, by rfl⟩ : syracuseStep 481457 = 361093) B361093
theorem B481475 : Blo 319836 481475 := bstep (se 1 (by rfl) ⟨361106, by rfl⟩ : syracuseStep 481475 = 722213) B722213
theorem B481505 : Blo 319836 481505 := bstep (se 2 (by rfl) ⟨180564, by rfl⟩ : syracuseStep 481505 = 361129) B361129
theorem B481523 : Blo 319836 481523 := bstep (se 1 (by rfl) ⟨361142, by rfl⟩ : syracuseStep 481523 = 722285) B722285
theorem B2054413 : Blo 319836 2054413 := bstep (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) B770405
theorem B481553 : Blo 319836 481553 := bstep (se 2 (by rfl) ⟨180582, by rfl⟩ : syracuseStep 481553 = 361165) B361165
theorem B481571 : Blo 319836 481571 := bstep (se 1 (by rfl) ⟨361178, by rfl⟩ : syracuseStep 481571 = 722357) B722357
theorem B481601 : Blo 319836 481601 := bstep (se 2 (by rfl) ⟨180600, by rfl⟩ : syracuseStep 481601 = 361201) B361201
theorem B481619 : Blo 319836 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B481649 : Blo 319836 481649 := bstep (se 2 (by rfl) ⟨180618, by rfl⟩ : syracuseStep 481649 = 361237) B361237
theorem B481667 : Blo 319836 481667 := bstep (se 1 (by rfl) ⟨361250, by rfl⟩ : syracuseStep 481667 = 722501) B722501
theorem B481697 : Blo 319836 481697 := bstep (se 2 (by rfl) ⟨180636, by rfl⟩ : syracuseStep 481697 = 361273) B361273
theorem B612785 : Blo 319836 612785 := bstep (se 2 (by rfl) ⟨229794, by rfl⟩ : syracuseStep 612785 = 459589) B459589
theorem B481715 : Blo 319836 481715 := bstep (se 1 (by rfl) ⟨361286, by rfl⟩ : syracuseStep 481715 = 722573) B722573
theorem B481745 : Blo 319836 481745 := bstep (se 2 (by rfl) ⟨180654, by rfl⟩ : syracuseStep 481745 = 361309) B361309
theorem B481763 : Blo 319836 481763 := bstep (se 1 (by rfl) ⟨361322, by rfl⟩ : syracuseStep 481763 = 722645) B722645
theorem B481793 : Blo 319836 481793 := bstep (se 2 (by rfl) ⟨180672, by rfl⟩ : syracuseStep 481793 = 361345) B361345
theorem B481811 : Blo 319836 481811 := bstep (se 1 (by rfl) ⟨361358, by rfl⟩ : syracuseStep 481811 = 722717) B722717
theorem B481841 : Blo 319836 481841 := bstep (se 2 (by rfl) ⟨180690, by rfl⟩ : syracuseStep 481841 = 361381) B361381
theorem B481859 : Blo 319836 481859 := bstep (se 1 (by rfl) ⟨361394, by rfl⟩ : syracuseStep 481859 = 722789) B722789
theorem B481889 : Blo 319836 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B481907 : Blo 319836 481907 := bstep (se 1 (by rfl) ⟨361430, by rfl⟩ : syracuseStep 481907 = 722861) B722861
theorem B481937 : Blo 319836 481937 := bstep (se 2 (by rfl) ⟨180726, by rfl⟩ : syracuseStep 481937 = 361453) B361453
theorem B809635 : Blo 319836 809635 := bstep (se 1 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 809635 = 1214453) B1214453
theorem B481955 : Blo 319836 481955 := bstep (se 1 (by rfl) ⟨361466, by rfl⟩ : syracuseStep 481955 = 722933) B722933
theorem B481985 : Blo 319836 481985 := bstep (se 2 (by rfl) ⟨180744, by rfl⟩ : syracuseStep 481985 = 361489) B361489
theorem B482003 : Blo 319836 482003 := bstep (se 1 (by rfl) ⟨361502, by rfl⟩ : syracuseStep 482003 = 723005) B723005
theorem B940781 : Blo 319836 940781 := bstep (se 3 (by rfl) ⟨176396, by rfl⟩ : syracuseStep 940781 = 352793) B352793
theorem B482033 : Blo 319836 482033 := bstep (se 2 (by rfl) ⟨180762, by rfl⟩ : syracuseStep 482033 = 361525) B361525
theorem B482051 : Blo 319836 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B482081 : Blo 319836 482081 := bstep (se 2 (by rfl) ⟨180780, by rfl⟩ : syracuseStep 482081 = 361561) B361561
theorem B809777 : Blo 319836 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B482099 : Blo 319836 482099 := bstep (se 1 (by rfl) ⟨361574, by rfl⟩ : syracuseStep 482099 = 723149) B723149
theorem B482129 : Blo 319836 482129 := bstep (se 2 (by rfl) ⟨180798, by rfl⟩ : syracuseStep 482129 = 361597) B361597
theorem B482147 : Blo 319836 482147 := bstep (se 1 (by rfl) ⟨361610, by rfl⟩ : syracuseStep 482147 = 723221) B723221
theorem B1661795 : Blo 319836 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B547697 : Blo 319836 547697 := bstep (se 2 (by rfl) ⟨205386, by rfl⟩ : syracuseStep 547697 = 410773) B410773
theorem B482177 : Blo 319836 482177 := bstep (se 2 (by rfl) ⟨180816, by rfl⟩ : syracuseStep 482177 = 361633) B361633
theorem B482195 : Blo 319836 482195 := bstep (se 1 (by rfl) ⟨361646, by rfl⟩ : syracuseStep 482195 = 723293) B723293
theorem B482225 : Blo 319836 482225 := bstep (se 2 (by rfl) ⟨180834, by rfl⟩ : syracuseStep 482225 = 361669) B361669
theorem B482243 : Blo 319836 482243 := bstep (se 1 (by rfl) ⟨361682, by rfl⟩ : syracuseStep 482243 = 723365) B723365
theorem B482273 : Blo 319836 482273 := bstep (se 2 (by rfl) ⟨180852, by rfl⟩ : syracuseStep 482273 = 361705) B361705
theorem B482291 : Blo 319836 482291 := bstep (se 1 (by rfl) ⟨361718, by rfl⟩ : syracuseStep 482291 = 723437) B723437
theorem B482321 : Blo 319836 482321 := bstep (se 2 (by rfl) ⟨180870, by rfl⟩ : syracuseStep 482321 = 361741) B361741
theorem B482339 : Blo 319836 482339 := bstep (se 1 (by rfl) ⟨361754, by rfl⟩ : syracuseStep 482339 = 723509) B723509
theorem B1629233 : Blo 319836 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B482369 : Blo 319836 482369 := bstep (se 2 (by rfl) ⟨180888, by rfl⟩ : syracuseStep 482369 = 361777) B361777
theorem B482387 : Blo 319836 482387 := bstep (se 1 (by rfl) ⟨361790, by rfl⟩ : syracuseStep 482387 = 723581) B723581
theorem B515155 : Blo 319836 515155 := bstep (se 1 (by rfl) ⟨386366, by rfl⟩ : syracuseStep 515155 = 772733) B772733
theorem B482417 : Blo 319836 482417 := bstep (se 2 (by rfl) ⟨180906, by rfl⟩ : syracuseStep 482417 = 361813) B361813
theorem B482435 : Blo 319836 482435 := bstep (se 1 (by rfl) ⟨361826, by rfl⟩ : syracuseStep 482435 = 723653) B723653
theorem B613507 : Blo 319836 613507 := bstep (se 1 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 613507 = 920261) B920261
theorem B482465 : Blo 319836 482465 := bstep (se 2 (by rfl) ⟨180924, by rfl⟩ : syracuseStep 482465 = 361849) B361849
theorem B482483 : Blo 319836 482483 := bstep (se 1 (by rfl) ⟨361862, by rfl⟩ : syracuseStep 482483 = 723725) B723725
theorem B482513 : Blo 319836 482513 := bstep (se 2 (by rfl) ⟨180942, by rfl⟩ : syracuseStep 482513 = 361885) B361885
theorem B482531 : Blo 319836 482531 := bstep (se 1 (by rfl) ⟨361898, by rfl⟩ : syracuseStep 482531 = 723797) B723797
theorem B482561 : Blo 319836 482561 := bstep (se 2 (by rfl) ⟨180960, by rfl⟩ : syracuseStep 482561 = 361921) B361921
theorem B482579 : Blo 319836 482579 := bstep (se 1 (by rfl) ⟨361934, by rfl⟩ : syracuseStep 482579 = 723869) B723869
theorem B482609 : Blo 319836 482609 := bstep (se 2 (by rfl) ⟨180978, by rfl⟩ : syracuseStep 482609 = 361957) B361957
theorem B482627 : Blo 319836 482627 := bstep (se 1 (by rfl) ⟨361970, by rfl⟩ : syracuseStep 482627 = 723941) B723941
theorem B515411 : Blo 319836 515411 := bstep (se 1 (by rfl) ⟨386558, by rfl⟩ : syracuseStep 515411 = 773117) B773117
theorem B482657 : Blo 319836 482657 := bstep (se 2 (by rfl) ⟨180996, by rfl⟩ : syracuseStep 482657 = 361993) B361993
theorem B482675 : Blo 319836 482675 := bstep (se 1 (by rfl) ⟨362006, by rfl⟩ : syracuseStep 482675 = 724013) B724013
theorem B4709773 : Blo 319836 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B482705 : Blo 319836 482705 := bstep (se 2 (by rfl) ⟨181014, by rfl⟩ : syracuseStep 482705 = 362029) B362029
theorem B482723 : Blo 319836 482723 := bstep (se 1 (by rfl) ⟨362042, by rfl⟩ : syracuseStep 482723 = 724085) B724085
theorem B482753 : Blo 319836 482753 := bstep (se 2 (by rfl) ⟨181032, by rfl⟩ : syracuseStep 482753 = 362065) B362065
theorem B482771 : Blo 319836 482771 := bstep (se 1 (by rfl) ⟨362078, by rfl⟩ : syracuseStep 482771 = 724157) B724157
theorem B482801 : Blo 319836 482801 := bstep (se 2 (by rfl) ⟨181050, by rfl⟩ : syracuseStep 482801 = 362101) B362101
theorem B482819 : Blo 319836 482819 := bstep (se 1 (by rfl) ⟨362114, by rfl⟩ : syracuseStep 482819 = 724229) B724229
theorem B482849 : Blo 319836 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B482867 : Blo 319836 482867 := bstep (se 1 (by rfl) ⟨362150, by rfl⟩ : syracuseStep 482867 = 724301) B724301
theorem B613955 : Blo 319836 613955 := bstep (se 1 (by rfl) ⟨460466, by rfl⟩ : syracuseStep 613955 = 920933) B920933
theorem B482897 : Blo 319836 482897 := bstep (se 2 (by rfl) ⟨181086, by rfl⟩ : syracuseStep 482897 = 362173) B362173
theorem B482915 : Blo 319836 482915 := bstep (se 1 (by rfl) ⟨362186, by rfl⟩ : syracuseStep 482915 = 724373) B724373
theorem B482945 : Blo 319836 482945 := bstep (se 2 (by rfl) ⟨181104, by rfl⟩ : syracuseStep 482945 = 362209) B362209
theorem B482963 : Blo 319836 482963 := bstep (se 1 (by rfl) ⟨362222, by rfl⟩ : syracuseStep 482963 = 724445) B724445
theorem B482993 : Blo 319836 482993 := bstep (se 2 (by rfl) ⟨181122, by rfl⟩ : syracuseStep 482993 = 362245) B362245
theorem B483011 : Blo 319836 483011 := bstep (se 1 (by rfl) ⟨362258, by rfl⟩ : syracuseStep 483011 = 724517) B724517
theorem B581315 : Blo 319836 581315 := bstep (se 1 (by rfl) ⟨435986, by rfl⟩ : syracuseStep 581315 = 871973) B871973
theorem B1826509 : Blo 319836 1826509 := bstep (se 3 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 1826509 = 684941) B684941
theorem B483041 : Blo 319836 483041 := bstep (se 2 (by rfl) ⟨181140, by rfl⟩ : syracuseStep 483041 = 362281) B362281
theorem B483059 : Blo 319836 483059 := bstep (se 1 (by rfl) ⟨362294, by rfl⟩ : syracuseStep 483059 = 724589) B724589
theorem B810769 : Blo 319836 810769 := bstep (se 2 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 810769 = 608077) B608077
theorem B483089 : Blo 319836 483089 := bstep (se 2 (by rfl) ⟨181158, by rfl⟩ : syracuseStep 483089 = 362317) B362317
theorem B483107 : Blo 319836 483107 := bstep (se 1 (by rfl) ⟨362330, by rfl⟩ : syracuseStep 483107 = 724661) B724661
theorem B483137 : Blo 319836 483137 := bstep (se 2 (by rfl) ⟨181176, by rfl⟩ : syracuseStep 483137 = 362353) B362353
theorem B483155 : Blo 319836 483155 := bstep (se 1 (by rfl) ⟨362366, by rfl⟩ : syracuseStep 483155 = 724733) B724733
theorem B614243 : Blo 319836 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B483185 : Blo 319836 483185 := bstep (se 2 (by rfl) ⟨181194, by rfl⟩ : syracuseStep 483185 = 362389) B362389
theorem B483203 : Blo 319836 483203 := bstep (se 1 (by rfl) ⟨362402, by rfl⟩ : syracuseStep 483203 = 724805) B724805
theorem B483233 : Blo 319836 483233 := bstep (se 2 (by rfl) ⟨181212, by rfl⟩ : syracuseStep 483233 = 362425) B362425
theorem B483251 : Blo 319836 483251 := bstep (se 1 (by rfl) ⟨362438, by rfl⟩ : syracuseStep 483251 = 724877) B724877
theorem B483281 : Blo 319836 483281 := bstep (se 2 (by rfl) ⟨181230, by rfl⟩ : syracuseStep 483281 = 362461) B362461
theorem B483299 : Blo 319836 483299 := bstep (se 1 (by rfl) ⟨362474, by rfl⟩ : syracuseStep 483299 = 724949) B724949
theorem B483329 : Blo 319836 483329 := bstep (se 2 (by rfl) ⟨181248, by rfl⟩ : syracuseStep 483329 = 362497) B362497
theorem B516115 : Blo 319836 516115 := bstep (se 1 (by rfl) ⟨387086, by rfl⟩ : syracuseStep 516115 = 774173) B774173
theorem B483347 : Blo 319836 483347 := bstep (se 1 (by rfl) ⟨362510, by rfl⟩ : syracuseStep 483347 = 725021) B725021
theorem B811043 : Blo 319836 811043 := bstep (se 1 (by rfl) ⟨608282, by rfl⟩ : syracuseStep 811043 = 1216565) B1216565
theorem B1564721 : Blo 319836 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B483377 : Blo 319836 483377 := bstep (se 2 (by rfl) ⟨181266, by rfl⟩ : syracuseStep 483377 = 362533) B362533
theorem B483395 : Blo 319836 483395 := bstep (se 1 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 483395 = 725093) B725093
theorem B483425 : Blo 319836 483425 := bstep (se 2 (by rfl) ⟨181284, by rfl⟩ : syracuseStep 483425 = 362569) B362569
theorem B483443 : Blo 319836 483443 := bstep (se 1 (by rfl) ⟨362582, by rfl⟩ : syracuseStep 483443 = 725165) B725165
theorem B483473 : Blo 319836 483473 := bstep (se 2 (by rfl) ⟨181302, by rfl⟩ : syracuseStep 483473 = 362605) B362605
theorem B483491 : Blo 319836 483491 := bstep (se 1 (by rfl) ⟨362618, by rfl⟩ : syracuseStep 483491 = 725237) B725237
theorem B483521 : Blo 319836 483521 := bstep (se 2 (by rfl) ⟨181320, by rfl⟩ : syracuseStep 483521 = 362641) B362641
theorem B483539 : Blo 319836 483539 := bstep (se 1 (by rfl) ⟨362654, by rfl⟩ : syracuseStep 483539 = 725309) B725309
theorem B811235 : Blo 319836 811235 := bstep (se 1 (by rfl) ⟨608426, by rfl⟩ : syracuseStep 811235 = 1216853) B1216853
theorem B483569 : Blo 319836 483569 := bstep (se 2 (by rfl) ⟨181338, by rfl⟩ : syracuseStep 483569 = 362677) B362677
theorem B483587 : Blo 319836 483587 := bstep (se 1 (by rfl) ⟨362690, by rfl⟩ : syracuseStep 483587 = 725381) B725381
theorem B516385 : Blo 319836 516385 := bstep (se 2 (by rfl) ⟨193644, by rfl⟩ : syracuseStep 516385 = 387289) B387289
theorem B483617 : Blo 319836 483617 := bstep (se 2 (by rfl) ⟨181356, by rfl⟩ : syracuseStep 483617 = 362713) B362713
theorem B483635 : Blo 319836 483635 := bstep (se 1 (by rfl) ⟨362726, by rfl⟩ : syracuseStep 483635 = 725453) B725453
theorem B483665 : Blo 319836 483665 := bstep (se 2 (by rfl) ⟨181374, by rfl⟩ : syracuseStep 483665 = 362749) B362749
theorem B516449 : Blo 319836 516449 := bstep (se 2 (by rfl) ⟨193668, by rfl⟩ : syracuseStep 516449 = 387337) B387337
theorem B319843 : Blo 319836 319843 := bstep (se 1 (by rfl) ⟨239882, by rfl⟩ : syracuseStep 319843 = 479765) B479765
theorem B483683 : Blo 319836 483683 := bstep (se 1 (by rfl) ⟨362762, by rfl⟩ : syracuseStep 483683 = 725525) B725525
theorem B319859 : Blo 319836 319859 := bstep (se 1 (by rfl) ⟨239894, by rfl⟩ : syracuseStep 319859 = 479789) B479789
theorem B483713 : Blo 319836 483713 := bstep (se 2 (by rfl) ⟨181392, by rfl⟩ : syracuseStep 483713 = 362785) B362785
theorem B319875 : Blo 319836 319875 := bstep (se 1 (by rfl) ⟨239906, by rfl⟩ : syracuseStep 319875 = 479813) B479813
theorem B319891 : Blo 319836 319891 := bstep (se 1 (by rfl) ⟨239918, by rfl⟩ : syracuseStep 319891 = 479837) B479837
theorem B483731 : Blo 319836 483731 := bstep (se 1 (by rfl) ⟨362798, by rfl⟩ : syracuseStep 483731 = 725597) B725597
theorem B319907 : Blo 319836 319907 := bstep (se 1 (by rfl) ⟨239930, by rfl⟩ : syracuseStep 319907 = 479861) B479861
theorem B483761 : Blo 319836 483761 := bstep (se 2 (by rfl) ⟨181410, by rfl⟩ : syracuseStep 483761 = 362821) B362821
theorem B319923 : Blo 319836 319923 := bstep (se 1 (by rfl) ⟨239942, by rfl⟩ : syracuseStep 319923 = 479885) B479885
theorem B319939 : Blo 319836 319939 := bstep (se 1 (by rfl) ⟨239954, by rfl⟩ : syracuseStep 319939 = 479909) B479909
theorem B483779 : Blo 319836 483779 := bstep (se 1 (by rfl) ⟨362834, by rfl⟩ : syracuseStep 483779 = 725669) B725669
theorem B319955 : Blo 319836 319955 := bstep (se 1 (by rfl) ⟨239966, by rfl⟩ : syracuseStep 319955 = 479933) B479933
theorem B483809 : Blo 319836 483809 := bstep (se 2 (by rfl) ⟨181428, by rfl⟩ : syracuseStep 483809 = 362857) B362857
theorem B319971 : Blo 319836 319971 := bstep (se 1 (by rfl) ⟨239978, by rfl⟩ : syracuseStep 319971 = 479957) B479957
theorem B1630691 : Blo 319836 1630691 := bstep (se 1 (by rfl) ⟨1223018, by rfl⟩ : syracuseStep 1630691 = 2446037) B2446037
theorem B319987 : Blo 319836 319987 := bstep (se 1 (by rfl) ⟨239990, by rfl⟩ : syracuseStep 319987 = 479981) B479981
theorem B483827 : Blo 319836 483827 := bstep (se 1 (by rfl) ⟨362870, by rfl⟩ : syracuseStep 483827 = 725741) B725741
theorem B320003 : Blo 319836 320003 := bstep (se 1 (by rfl) ⟨240002, by rfl⟩ : syracuseStep 320003 = 480005) B480005
theorem B483857 : Blo 319836 483857 := bstep (se 2 (by rfl) ⟨181446, by rfl⟩ : syracuseStep 483857 = 362893) B362893
theorem B320019 : Blo 319836 320019 := bstep (se 1 (by rfl) ⟨240014, by rfl⟩ : syracuseStep 320019 = 480029) B480029
theorem B320035 : Blo 319836 320035 := bstep (se 1 (by rfl) ⟨240026, by rfl⟩ : syracuseStep 320035 = 480053) B480053
theorem B483875 : Blo 319836 483875 := bstep (se 1 (by rfl) ⟨362906, by rfl⟩ : syracuseStep 483875 = 725813) B725813
theorem B320051 : Blo 319836 320051 := bstep (se 1 (by rfl) ⟨240038, by rfl⟩ : syracuseStep 320051 = 480077) B480077
theorem B483905 : Blo 319836 483905 := bstep (se 2 (by rfl) ⟨181464, by rfl⟩ : syracuseStep 483905 = 362929) B362929
theorem B320067 : Blo 319836 320067 := bstep (se 1 (by rfl) ⟨240050, by rfl⟩ : syracuseStep 320067 = 480101) B480101
theorem B320083 : Blo 319836 320083 := bstep (se 1 (by rfl) ⟨240062, by rfl⟩ : syracuseStep 320083 = 480125) B480125
theorem B483923 : Blo 319836 483923 := bstep (se 1 (by rfl) ⟨362942, by rfl⟩ : syracuseStep 483923 = 725885) B725885
theorem B320099 : Blo 319836 320099 := bstep (se 1 (by rfl) ⟨240074, by rfl⟩ : syracuseStep 320099 = 480149) B480149
theorem B483953 : Blo 319836 483953 := bstep (se 2 (by rfl) ⟨181482, by rfl⟩ : syracuseStep 483953 = 362965) B362965
theorem B320115 : Blo 319836 320115 := bstep (se 1 (by rfl) ⟨240086, by rfl⟩ : syracuseStep 320115 = 480173) B480173
theorem B320131 : Blo 319836 320131 := bstep (se 1 (by rfl) ⟨240098, by rfl⟩ : syracuseStep 320131 = 480197) B480197
theorem B483971 : Blo 319836 483971 := bstep (se 1 (by rfl) ⟨362978, by rfl⟩ : syracuseStep 483971 = 725957) B725957
theorem B320147 : Blo 319836 320147 := bstep (se 1 (by rfl) ⟨240110, by rfl⟩ : syracuseStep 320147 = 480221) B480221
theorem B484001 : Blo 319836 484001 := bstep (se 2 (by rfl) ⟨181500, by rfl⟩ : syracuseStep 484001 = 363001) B363001
theorem B320163 : Blo 319836 320163 := bstep (se 1 (by rfl) ⟨240122, by rfl⟩ : syracuseStep 320163 = 480245) B480245
theorem B320179 : Blo 319836 320179 := bstep (se 1 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 320179 = 480269) B480269
theorem B484019 : Blo 319836 484019 := bstep (se 1 (by rfl) ⟨363014, by rfl⟩ : syracuseStep 484019 = 726029) B726029
theorem B320195 : Blo 319836 320195 := bstep (se 1 (by rfl) ⟨240146, by rfl⟩ : syracuseStep 320195 = 480293) B480293
theorem B484049 : Blo 319836 484049 := bstep (se 2 (by rfl) ⟨181518, by rfl⟩ : syracuseStep 484049 = 363037) B363037
theorem B320211 : Blo 319836 320211 := bstep (se 1 (by rfl) ⟨240158, by rfl⟩ : syracuseStep 320211 = 480317) B480317
theorem B320227 : Blo 319836 320227 := bstep (se 1 (by rfl) ⟨240170, by rfl⟩ : syracuseStep 320227 = 480341) B480341
theorem B484067 : Blo 319836 484067 := bstep (se 1 (by rfl) ⟨363050, by rfl⟩ : syracuseStep 484067 = 726101) B726101
theorem B320243 : Blo 319836 320243 := bstep (se 1 (by rfl) ⟨240182, by rfl⟩ : syracuseStep 320243 = 480365) B480365
theorem B484097 : Blo 319836 484097 := bstep (se 2 (by rfl) ⟨181536, by rfl⟩ : syracuseStep 484097 = 363073) B363073
theorem B320259 : Blo 319836 320259 := bstep (se 1 (by rfl) ⟨240194, by rfl⟩ : syracuseStep 320259 = 480389) B480389
theorem B320275 : Blo 319836 320275 := bstep (se 1 (by rfl) ⟨240206, by rfl⟩ : syracuseStep 320275 = 480413) B480413
theorem B484115 : Blo 319836 484115 := bstep (se 1 (by rfl) ⟨363086, by rfl⟩ : syracuseStep 484115 = 726173) B726173
theorem B320291 : Blo 319836 320291 := bstep (se 1 (by rfl) ⟨240218, by rfl⟩ : syracuseStep 320291 = 480437) B480437
theorem B484145 : Blo 319836 484145 := bstep (se 2 (by rfl) ⟨181554, by rfl⟩ : syracuseStep 484145 = 363109) B363109
theorem B320307 : Blo 319836 320307 := bstep (se 1 (by rfl) ⟨240230, by rfl⟩ : syracuseStep 320307 = 480461) B480461
theorem B320323 : Blo 319836 320323 := bstep (se 1 (by rfl) ⟨240242, by rfl⟩ : syracuseStep 320323 = 480485) B480485
theorem B484163 : Blo 319836 484163 := bstep (se 1 (by rfl) ⟨363122, by rfl⟩ : syracuseStep 484163 = 726245) B726245
theorem B320339 : Blo 319836 320339 := bstep (se 1 (by rfl) ⟨240254, by rfl⟩ : syracuseStep 320339 = 480509) B480509
theorem B484193 : Blo 319836 484193 := bstep (se 2 (by rfl) ⟨181572, by rfl⟩ : syracuseStep 484193 = 363145) B363145
theorem B320355 : Blo 319836 320355 := bstep (se 1 (by rfl) ⟨240266, by rfl⟩ : syracuseStep 320355 = 480533) B480533
theorem B320371 : Blo 319836 320371 := bstep (se 1 (by rfl) ⟨240278, by rfl⟩ : syracuseStep 320371 = 480557) B480557
theorem B484211 : Blo 319836 484211 := bstep (se 1 (by rfl) ⟨363158, by rfl⟩ : syracuseStep 484211 = 726317) B726317
theorem B320387 : Blo 319836 320387 := bstep (se 1 (by rfl) ⟨240290, by rfl⟩ : syracuseStep 320387 = 480581) B480581
theorem B484241 : Blo 319836 484241 := bstep (se 2 (by rfl) ⟨181590, by rfl⟩ : syracuseStep 484241 = 363181) B363181
theorem B320403 : Blo 319836 320403 := bstep (se 1 (by rfl) ⟨240302, by rfl⟩ : syracuseStep 320403 = 480605) B480605
theorem B320419 : Blo 319836 320419 := bstep (se 1 (by rfl) ⟨240314, by rfl⟩ : syracuseStep 320419 = 480629) B480629
theorem B484259 : Blo 319836 484259 := bstep (se 1 (by rfl) ⟨363194, by rfl⟩ : syracuseStep 484259 = 726389) B726389
theorem B320435 : Blo 319836 320435 := bstep (se 1 (by rfl) ⟨240326, by rfl⟩ : syracuseStep 320435 = 480653) B480653
theorem B484289 : Blo 319836 484289 := bstep (se 2 (by rfl) ⟨181608, by rfl⟩ : syracuseStep 484289 = 363217) B363217
theorem B320451 : Blo 319836 320451 := bstep (se 1 (by rfl) ⟨240338, by rfl⟩ : syracuseStep 320451 = 480677) B480677
theorem B320467 : Blo 319836 320467 := bstep (se 1 (by rfl) ⟨240350, by rfl⟩ : syracuseStep 320467 = 480701) B480701
theorem B484307 : Blo 319836 484307 := bstep (se 1 (by rfl) ⟨363230, by rfl⟩ : syracuseStep 484307 = 726461) B726461
theorem B320483 : Blo 319836 320483 := bstep (se 1 (by rfl) ⟨240362, by rfl⟩ : syracuseStep 320483 = 480725) B480725
theorem B484337 : Blo 319836 484337 := bstep (se 2 (by rfl) ⟨181626, by rfl⟩ : syracuseStep 484337 = 363253) B363253
theorem B320499 : Blo 319836 320499 := bstep (se 1 (by rfl) ⟨240374, by rfl⟩ : syracuseStep 320499 = 480749) B480749
theorem B320515 : Blo 319836 320515 := bstep (se 1 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 320515 = 480773) B480773
theorem B484355 : Blo 319836 484355 := bstep (se 1 (by rfl) ⟨363266, by rfl⟩ : syracuseStep 484355 = 726533) B726533
theorem B320531 : Blo 319836 320531 := bstep (se 1 (by rfl) ⟨240398, by rfl⟩ : syracuseStep 320531 = 480797) B480797
theorem B484385 : Blo 319836 484385 := bstep (se 2 (by rfl) ⟨181644, by rfl⟩ : syracuseStep 484385 = 363289) B363289
theorem B320547 : Blo 319836 320547 := bstep (se 1 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 320547 = 480821) B480821
theorem B386083 : Blo 319836 386083 := bstep (se 1 (by rfl) ⟨289562, by rfl⟩ : syracuseStep 386083 = 579125) B579125
theorem B320563 : Blo 319836 320563 := bstep (se 1 (by rfl) ⟨240422, by rfl⟩ : syracuseStep 320563 = 480845) B480845
theorem B484403 : Blo 319836 484403 := bstep (se 1 (by rfl) ⟨363302, by rfl⟩ : syracuseStep 484403 = 726605) B726605
theorem B320579 : Blo 319836 320579 := bstep (se 1 (by rfl) ⟨240434, by rfl⟩ : syracuseStep 320579 = 480869) B480869
theorem B484433 : Blo 319836 484433 := bstep (se 2 (by rfl) ⟨181662, by rfl⟩ : syracuseStep 484433 = 363325) B363325
theorem B320595 : Blo 319836 320595 := bstep (se 1 (by rfl) ⟨240446, by rfl⟩ : syracuseStep 320595 = 480893) B480893
theorem B320611 : Blo 319836 320611 := bstep (se 1 (by rfl) ⟨240458, by rfl⟩ : syracuseStep 320611 = 480917) B480917
theorem B484451 : Blo 319836 484451 := bstep (se 1 (by rfl) ⟨363338, by rfl⟩ : syracuseStep 484451 = 726677) B726677
theorem B320627 : Blo 319836 320627 := bstep (se 1 (by rfl) ⟨240470, by rfl⟩ : syracuseStep 320627 = 480941) B480941
theorem B484481 : Blo 319836 484481 := bstep (se 2 (by rfl) ⟨181680, by rfl⟩ : syracuseStep 484481 = 363361) B363361
theorem B320643 : Blo 319836 320643 := bstep (se 1 (by rfl) ⟨240482, by rfl⟩ : syracuseStep 320643 = 480965) B480965
theorem B812177 : Blo 319836 812177 := bstep (se 2 (by rfl) ⟨304566, by rfl⟩ : syracuseStep 812177 = 609133) B609133
theorem B320659 : Blo 319836 320659 := bstep (se 1 (by rfl) ⟨240494, by rfl⟩ : syracuseStep 320659 = 480989) B480989
theorem B484499 : Blo 319836 484499 := bstep (se 1 (by rfl) ⟨363374, by rfl⟩ : syracuseStep 484499 = 726749) B726749
theorem B320675 : Blo 319836 320675 := bstep (se 1 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 320675 = 481013) B481013
theorem B484529 : Blo 319836 484529 := bstep (se 2 (by rfl) ⟨181698, by rfl⟩ : syracuseStep 484529 = 363397) B363397
theorem B320691 : Blo 319836 320691 := bstep (se 1 (by rfl) ⟨240518, by rfl⟩ : syracuseStep 320691 = 481037) B481037
theorem B320707 : Blo 319836 320707 := bstep (se 1 (by rfl) ⟨240530, by rfl⟩ : syracuseStep 320707 = 481061) B481061
theorem B812227 : Blo 319836 812227 := bstep (se 1 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 812227 = 1218341) B1218341
theorem B484547 : Blo 319836 484547 := bstep (se 1 (by rfl) ⟨363410, by rfl⟩ : syracuseStep 484547 = 726821) B726821
theorem B582851 : Blo 319836 582851 := bstep (se 1 (by rfl) ⟨437138, by rfl⟩ : syracuseStep 582851 = 874277) B874277
theorem B320723 : Blo 319836 320723 := bstep (se 1 (by rfl) ⟨240542, by rfl⟩ : syracuseStep 320723 = 481085) B481085
theorem B484577 : Blo 319836 484577 := bstep (se 2 (by rfl) ⟨181716, by rfl⟩ : syracuseStep 484577 = 363433) B363433
theorem B320739 : Blo 319836 320739 := bstep (se 1 (by rfl) ⟨240554, by rfl⟩ : syracuseStep 320739 = 481109) B481109
theorem B320755 : Blo 319836 320755 := bstep (se 1 (by rfl) ⟨240566, by rfl⟩ : syracuseStep 320755 = 481133) B481133
theorem B484595 : Blo 319836 484595 := bstep (se 1 (by rfl) ⟨363446, by rfl⟩ : syracuseStep 484595 = 726893) B726893
theorem B320771 : Blo 319836 320771 := bstep (se 1 (by rfl) ⟨240578, by rfl⟩ : syracuseStep 320771 = 481157) B481157
theorem B1631501 : Blo 319836 1631501 := bstep (se 3 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 1631501 = 611813) B611813
theorem B484625 : Blo 319836 484625 := bstep (se 2 (by rfl) ⟨181734, by rfl⟩ : syracuseStep 484625 = 363469) B363469
theorem B320787 : Blo 319836 320787 := bstep (se 1 (by rfl) ⟨240590, by rfl⟩ : syracuseStep 320787 = 481181) B481181
theorem B320803 : Blo 319836 320803 := bstep (se 1 (by rfl) ⟨240602, by rfl⟩ : syracuseStep 320803 = 481205) B481205
theorem B484643 : Blo 319836 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B320819 : Blo 319836 320819 := bstep (se 1 (by rfl) ⟨240614, by rfl⟩ : syracuseStep 320819 = 481229) B481229
theorem B484673 : Blo 319836 484673 := bstep (se 2 (by rfl) ⟨181752, by rfl⟩ : syracuseStep 484673 = 363505) B363505
theorem B320835 : Blo 319836 320835 := bstep (se 1 (by rfl) ⟨240626, by rfl⟩ : syracuseStep 320835 = 481253) B481253
theorem B812369 : Blo 319836 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B320851 : Blo 319836 320851 := bstep (se 1 (by rfl) ⟨240638, by rfl⟩ : syracuseStep 320851 = 481277) B481277
theorem B484691 : Blo 319836 484691 := bstep (se 1 (by rfl) ⟨363518, by rfl⟩ : syracuseStep 484691 = 727037) B727037
theorem B320867 : Blo 319836 320867 := bstep (se 1 (by rfl) ⟨240650, by rfl⟩ : syracuseStep 320867 = 481301) B481301
theorem B1369457 : Blo 319836 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B484721 : Blo 319836 484721 := bstep (se 2 (by rfl) ⟨181770, by rfl⟩ : syracuseStep 484721 = 363541) B363541
theorem B320883 : Blo 319836 320883 := bstep (se 1 (by rfl) ⟨240662, by rfl⟩ : syracuseStep 320883 = 481325) B481325
theorem B320899 : Blo 319836 320899 := bstep (se 1 (by rfl) ⟨240674, by rfl⟩ : syracuseStep 320899 = 481349) B481349
theorem B484739 : Blo 319836 484739 := bstep (se 1 (by rfl) ⟨363554, by rfl⟩ : syracuseStep 484739 = 727109) B727109
theorem B320915 : Blo 319836 320915 := bstep (se 1 (by rfl) ⟨240686, by rfl⟩ : syracuseStep 320915 = 481373) B481373
theorem B484769 : Blo 319836 484769 := bstep (se 2 (by rfl) ⟨181788, by rfl⟩ : syracuseStep 484769 = 363577) B363577
theorem B1369507 : Blo 319836 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B320931 : Blo 319836 320931 := bstep (se 1 (by rfl) ⟨240698, by rfl⟩ : syracuseStep 320931 = 481397) B481397
theorem B320947 : Blo 319836 320947 := bstep (se 1 (by rfl) ⟨240710, by rfl⟩ : syracuseStep 320947 = 481421) B481421
theorem B484787 : Blo 319836 484787 := bstep (se 1 (by rfl) ⟨363590, by rfl⟩ : syracuseStep 484787 = 727181) B727181
theorem B320963 : Blo 319836 320963 := bstep (se 1 (by rfl) ⟨240722, by rfl⟩ : syracuseStep 320963 = 481445) B481445
theorem B484817 : Blo 319836 484817 := bstep (se 2 (by rfl) ⟨181806, by rfl⟩ : syracuseStep 484817 = 363613) B363613
theorem B320979 : Blo 319836 320979 := bstep (se 1 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 320979 = 481469) B481469
theorem B320995 : Blo 319836 320995 := bstep (se 1 (by rfl) ⟨240746, by rfl⟩ : syracuseStep 320995 = 481493) B481493
theorem B484835 : Blo 319836 484835 := bstep (se 1 (by rfl) ⟨363626, by rfl⟩ : syracuseStep 484835 = 727253) B727253
theorem B321011 : Blo 319836 321011 := bstep (se 1 (by rfl) ⟨240758, by rfl⟩ : syracuseStep 321011 = 481517) B481517
theorem B484865 : Blo 319836 484865 := bstep (se 2 (by rfl) ⟨181824, by rfl⟩ : syracuseStep 484865 = 363649) B363649
theorem B321027 : Blo 319836 321027 := bstep (se 1 (by rfl) ⟨240770, by rfl⟩ : syracuseStep 321027 = 481541) B481541
theorem B321043 : Blo 319836 321043 := bstep (se 1 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 321043 = 481565) B481565
theorem B484883 : Blo 319836 484883 := bstep (se 1 (by rfl) ⟨363662, by rfl⟩ : syracuseStep 484883 = 727325) B727325
theorem B321059 : Blo 319836 321059 := bstep (se 1 (by rfl) ⟨240794, by rfl⟩ : syracuseStep 321059 = 481589) B481589
theorem B484913 : Blo 319836 484913 := bstep (se 2 (by rfl) ⟨181842, by rfl⟩ : syracuseStep 484913 = 363685) B363685
theorem B321075 : Blo 319836 321075 := bstep (se 1 (by rfl) ⟨240806, by rfl⟩ : syracuseStep 321075 = 481613) B481613
theorem B321091 : Blo 319836 321091 := bstep (se 1 (by rfl) ⟨240818, by rfl⟩ : syracuseStep 321091 = 481637) B481637
theorem B484931 : Blo 319836 484931 := bstep (se 1 (by rfl) ⟨363698, by rfl⟩ : syracuseStep 484931 = 727397) B727397
theorem B321107 : Blo 319836 321107 := bstep (se 1 (by rfl) ⟨240830, by rfl⟩ : syracuseStep 321107 = 481661) B481661
theorem B484961 : Blo 319836 484961 := bstep (se 2 (by rfl) ⟨181860, by rfl⟩ : syracuseStep 484961 = 363721) B363721
theorem B321123 : Blo 319836 321123 := bstep (se 1 (by rfl) ⟨240842, by rfl⟩ : syracuseStep 321123 = 481685) B481685
theorem B321139 : Blo 319836 321139 := bstep (se 1 (by rfl) ⟨240854, by rfl⟩ : syracuseStep 321139 = 481709) B481709
theorem B484979 : Blo 319836 484979 := bstep (se 1 (by rfl) ⟨363734, by rfl⟩ : syracuseStep 484979 = 727469) B727469
theorem B321155 : Blo 319836 321155 := bstep (se 1 (by rfl) ⟨240866, by rfl⟩ : syracuseStep 321155 = 481733) B481733
theorem B1828493 : Blo 319836 1828493 := bstep (se 3 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 1828493 = 685685) B685685
theorem B485009 : Blo 319836 485009 := bstep (se 2 (by rfl) ⟨181878, by rfl⟩ : syracuseStep 485009 = 363757) B363757
theorem B321171 : Blo 319836 321171 := bstep (se 1 (by rfl) ⟨240878, by rfl⟩ : syracuseStep 321171 = 481757) B481757
theorem B321187 : Blo 319836 321187 := bstep (se 1 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 321187 = 481781) B481781
theorem B485027 : Blo 319836 485027 := bstep (se 1 (by rfl) ⟨363770, by rfl⟩ : syracuseStep 485027 = 727541) B727541
theorem B321203 : Blo 319836 321203 := bstep (se 1 (by rfl) ⟨240902, by rfl⟩ : syracuseStep 321203 = 481805) B481805
theorem B485057 : Blo 319836 485057 := bstep (se 2 (by rfl) ⟨181896, by rfl⟩ : syracuseStep 485057 = 363793) B363793
theorem B321219 : Blo 319836 321219 := bstep (se 1 (by rfl) ⟨240914, by rfl⟩ : syracuseStep 321219 = 481829) B481829
theorem B321235 : Blo 319836 321235 := bstep (se 1 (by rfl) ⟨240926, by rfl⟩ : syracuseStep 321235 = 481853) B481853
theorem B485075 : Blo 319836 485075 := bstep (se 1 (by rfl) ⟨363806, by rfl⟩ : syracuseStep 485075 = 727613) B727613
theorem B321251 : Blo 319836 321251 := bstep (se 1 (by rfl) ⟨240938, by rfl⟩ : syracuseStep 321251 = 481877) B481877
theorem B485105 : Blo 319836 485105 := bstep (se 2 (by rfl) ⟨181914, by rfl⟩ : syracuseStep 485105 = 363829) B363829
theorem B321267 : Blo 319836 321267 := bstep (se 1 (by rfl) ⟨240950, by rfl⟩ : syracuseStep 321267 = 481901) B481901
theorem B321283 : Blo 319836 321283 := bstep (se 1 (by rfl) ⟨240962, by rfl⟩ : syracuseStep 321283 = 481925) B481925
theorem B485123 : Blo 319836 485123 := bstep (se 1 (by rfl) ⟨363842, by rfl⟩ : syracuseStep 485123 = 727685) B727685
theorem B321299 : Blo 319836 321299 := bstep (se 1 (by rfl) ⟨240974, by rfl⟩ : syracuseStep 321299 = 481949) B481949
theorem B485153 : Blo 319836 485153 := bstep (se 2 (by rfl) ⟨181932, by rfl⟩ : syracuseStep 485153 = 363865) B363865
theorem B321315 : Blo 319836 321315 := bstep (se 1 (by rfl) ⟨240986, by rfl⟩ : syracuseStep 321315 = 481973) B481973
theorem B321331 : Blo 319836 321331 := bstep (se 1 (by rfl) ⟨240998, by rfl⟩ : syracuseStep 321331 = 481997) B481997
theorem B485171 : Blo 319836 485171 := bstep (se 1 (by rfl) ⟨363878, by rfl⟩ : syracuseStep 485171 = 727757) B727757
theorem B321347 : Blo 319836 321347 := bstep (se 1 (by rfl) ⟨241010, by rfl⟩ : syracuseStep 321347 = 482021) B482021
theorem B485201 : Blo 319836 485201 := bstep (se 2 (by rfl) ⟨181950, by rfl⟩ : syracuseStep 485201 = 363901) B363901
theorem B321363 : Blo 319836 321363 := bstep (se 1 (by rfl) ⟨241022, by rfl⟩ : syracuseStep 321363 = 482045) B482045
theorem B321379 : Blo 319836 321379 := bstep (se 1 (by rfl) ⟨241034, by rfl⟩ : syracuseStep 321379 = 482069) B482069
theorem B485219 : Blo 319836 485219 := bstep (se 1 (by rfl) ⟨363914, by rfl⟩ : syracuseStep 485219 = 727829) B727829
theorem B321395 : Blo 319836 321395 := bstep (se 1 (by rfl) ⟨241046, by rfl⟩ : syracuseStep 321395 = 482093) B482093
theorem B485249 : Blo 319836 485249 := bstep (se 2 (by rfl) ⟨181968, by rfl⟩ : syracuseStep 485249 = 363937) B363937
theorem B321411 : Blo 319836 321411 := bstep (se 1 (by rfl) ⟨241058, by rfl⟩ : syracuseStep 321411 = 482117) B482117
theorem B1959821 : Blo 319836 1959821 := bstep (se 3 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 1959821 = 734933) B734933
theorem B321427 : Blo 319836 321427 := bstep (se 1 (by rfl) ⟨241070, by rfl⟩ : syracuseStep 321427 = 482141) B482141
theorem B485267 : Blo 319836 485267 := bstep (se 1 (by rfl) ⟨363950, by rfl⟩ : syracuseStep 485267 = 727901) B727901
theorem B321443 : Blo 319836 321443 := bstep (se 1 (by rfl) ⟨241082, by rfl⟩ : syracuseStep 321443 = 482165) B482165
theorem B485297 : Blo 319836 485297 := bstep (se 2 (by rfl) ⟨181986, by rfl⟩ : syracuseStep 485297 = 363973) B363973
theorem B321459 : Blo 319836 321459 := bstep (se 1 (by rfl) ⟨241094, by rfl⟩ : syracuseStep 321459 = 482189) B482189
theorem B321475 : Blo 319836 321475 := bstep (se 1 (by rfl) ⟨241106, by rfl⟩ : syracuseStep 321475 = 482213) B482213
theorem B485315 : Blo 319836 485315 := bstep (se 1 (by rfl) ⟨363986, by rfl⟩ : syracuseStep 485315 = 727973) B727973
theorem B15591365 : Blo 319836 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B321491 : Blo 319836 321491 := bstep (se 1 (by rfl) ⟨241118, by rfl⟩ : syracuseStep 321491 = 482237) B482237
theorem B485345 : Blo 319836 485345 := bstep (se 2 (by rfl) ⟨182004, by rfl⟩ : syracuseStep 485345 = 364009) B364009
theorem B321507 : Blo 319836 321507 := bstep (se 1 (by rfl) ⟨241130, by rfl⟩ : syracuseStep 321507 = 482261) B482261
theorem B911341 : Blo 319836 911341 := bstep (se 3 (by rfl) ⟨170876, by rfl⟩ : syracuseStep 911341 = 341753) B341753
theorem B321523 : Blo 319836 321523 := bstep (se 1 (by rfl) ⟨241142, by rfl⟩ : syracuseStep 321523 = 482285) B482285
theorem B485363 : Blo 319836 485363 := bstep (se 1 (by rfl) ⟨364022, by rfl⟩ : syracuseStep 485363 = 728045) B728045
theorem B649219 : Blo 319836 649219 := bstep (se 1 (by rfl) ⟨486914, by rfl⟩ : syracuseStep 649219 = 973829) B973829
theorem B321539 : Blo 319836 321539 := bstep (se 1 (by rfl) ⟨241154, by rfl⟩ : syracuseStep 321539 = 482309) B482309
theorem B485393 : Blo 319836 485393 := bstep (se 2 (by rfl) ⟨182022, by rfl⟩ : syracuseStep 485393 = 364045) B364045
theorem B321555 : Blo 319836 321555 := bstep (se 1 (by rfl) ⟨241166, by rfl⟩ : syracuseStep 321555 = 482333) B482333
theorem B321571 : Blo 319836 321571 := bstep (se 1 (by rfl) ⟨241178, by rfl⟩ : syracuseStep 321571 = 482357) B482357
theorem B518179 : Blo 319836 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B485411 : Blo 319836 485411 := bstep (se 1 (by rfl) ⟨364058, by rfl⟩ : syracuseStep 485411 = 728117) B728117
theorem B321587 : Blo 319836 321587 := bstep (se 1 (by rfl) ⟨241190, by rfl⟩ : syracuseStep 321587 = 482381) B482381
theorem B485441 : Blo 319836 485441 := bstep (se 2 (by rfl) ⟨182040, by rfl⟩ : syracuseStep 485441 = 364081) B364081
theorem B321603 : Blo 319836 321603 := bstep (se 1 (by rfl) ⟨241202, by rfl⟩ : syracuseStep 321603 = 482405) B482405
theorem B616529 : Blo 319836 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B321619 : Blo 319836 321619 := bstep (se 1 (by rfl) ⟨241214, by rfl⟩ : syracuseStep 321619 = 482429) B482429
theorem B485459 : Blo 319836 485459 := bstep (se 1 (by rfl) ⟨364094, by rfl⟩ : syracuseStep 485459 = 728189) B728189
theorem B321635 : Blo 319836 321635 := bstep (se 1 (by rfl) ⟨241226, by rfl⟩ : syracuseStep 321635 = 482453) B482453
theorem B485489 : Blo 319836 485489 := bstep (se 2 (by rfl) ⟨182058, by rfl⟩ : syracuseStep 485489 = 364117) B364117
theorem B321651 : Blo 319836 321651 := bstep (se 1 (by rfl) ⟨241238, by rfl⟩ : syracuseStep 321651 = 482477) B482477
theorem B321667 : Blo 319836 321667 := bstep (se 1 (by rfl) ⟨241250, by rfl⟩ : syracuseStep 321667 = 482501) B482501
theorem B485507 : Blo 319836 485507 := bstep (se 1 (by rfl) ⟨364130, by rfl⟩ : syracuseStep 485507 = 728261) B728261
theorem B321683 : Blo 319836 321683 := bstep (se 1 (by rfl) ⟨241262, by rfl⟩ : syracuseStep 321683 = 482525) B482525
theorem B485537 : Blo 319836 485537 := bstep (se 2 (by rfl) ⟨182076, by rfl⟩ : syracuseStep 485537 = 364153) B364153
theorem B321699 : Blo 319836 321699 := bstep (se 1 (by rfl) ⟨241274, by rfl⟩ : syracuseStep 321699 = 482549) B482549
theorem B321715 : Blo 319836 321715 := bstep (se 1 (by rfl) ⟨241286, by rfl⟩ : syracuseStep 321715 = 482573) B482573
theorem B485555 : Blo 319836 485555 := bstep (se 1 (by rfl) ⟨364166, by rfl⟩ : syracuseStep 485555 = 728333) B728333
theorem B321731 : Blo 319836 321731 := bstep (se 1 (by rfl) ⟨241298, by rfl⟩ : syracuseStep 321731 = 482597) B482597
theorem B911569 : Blo 319836 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B485585 : Blo 319836 485585 := bstep (se 2 (by rfl) ⟨182094, by rfl⟩ : syracuseStep 485585 = 364189) B364189
theorem B321747 : Blo 319836 321747 := bstep (se 1 (by rfl) ⟨241310, by rfl⟩ : syracuseStep 321747 = 482621) B482621
theorem B321763 : Blo 319836 321763 := bstep (se 1 (by rfl) ⟨241322, by rfl⟩ : syracuseStep 321763 = 482645) B482645
theorem B485603 : Blo 319836 485603 := bstep (se 1 (by rfl) ⟨364202, by rfl⟩ : syracuseStep 485603 = 728405) B728405
theorem B321779 : Blo 319836 321779 := bstep (se 1 (by rfl) ⟨241334, by rfl⟩ : syracuseStep 321779 = 482669) B482669
theorem B485633 : Blo 319836 485633 := bstep (se 2 (by rfl) ⟨182112, by rfl⟩ : syracuseStep 485633 = 364225) B364225
theorem B321795 : Blo 319836 321795 := bstep (se 1 (by rfl) ⟨241346, by rfl⟩ : syracuseStep 321795 = 482693) B482693
theorem B321811 : Blo 319836 321811 := bstep (se 1 (by rfl) ⟨241358, by rfl⟩ : syracuseStep 321811 = 482717) B482717
theorem B485651 : Blo 319836 485651 := bstep (se 1 (by rfl) ⟨364238, by rfl⟩ : syracuseStep 485651 = 728477) B728477
theorem B321827 : Blo 319836 321827 := bstep (se 1 (by rfl) ⟨241370, by rfl⟩ : syracuseStep 321827 = 482741) B482741
theorem B813361 : Blo 319836 813361 := bstep (se 2 (by rfl) ⟨305010, by rfl⟩ : syracuseStep 813361 = 610021) B610021
theorem B485681 : Blo 319836 485681 := bstep (se 2 (by rfl) ⟨182130, by rfl⟩ : syracuseStep 485681 = 364261) B364261
theorem B321843 : Blo 319836 321843 := bstep (se 1 (by rfl) ⟨241382, by rfl⟩ : syracuseStep 321843 = 482765) B482765
theorem B321859 : Blo 319836 321859 := bstep (se 1 (by rfl) ⟨241394, by rfl⟩ : syracuseStep 321859 = 482789) B482789
theorem B485699 : Blo 319836 485699 := bstep (se 1 (by rfl) ⟨364274, by rfl⟩ : syracuseStep 485699 = 728549) B728549
theorem B321875 : Blo 319836 321875 := bstep (se 1 (by rfl) ⟨241406, by rfl⟩ : syracuseStep 321875 = 482813) B482813
theorem B485729 : Blo 319836 485729 := bstep (se 2 (by rfl) ⟨182148, by rfl⟩ : syracuseStep 485729 = 364297) B364297
theorem B321891 : Blo 319836 321891 := bstep (se 1 (by rfl) ⟨241418, by rfl⟩ : syracuseStep 321891 = 482837) B482837
theorem B911729 : Blo 319836 911729 := bstep (se 2 (by rfl) ⟨341898, by rfl⟩ : syracuseStep 911729 = 683797) B683797
theorem B321907 : Blo 319836 321907 := bstep (se 1 (by rfl) ⟨241430, by rfl⟩ : syracuseStep 321907 = 482861) B482861
theorem B485747 : Blo 319836 485747 := bstep (se 1 (by rfl) ⟨364310, by rfl⟩ : syracuseStep 485747 = 728621) B728621
theorem B321923 : Blo 319836 321923 := bstep (se 1 (by rfl) ⟨241442, by rfl⟩ : syracuseStep 321923 = 482885) B482885
theorem B321939 : Blo 319836 321939 := bstep (se 1 (by rfl) ⟨241454, by rfl⟩ : syracuseStep 321939 = 482909) B482909
theorem B321955 : Blo 319836 321955 := bstep (se 1 (by rfl) ⟨241466, by rfl⟩ : syracuseStep 321955 = 482933) B482933
theorem B321971 : Blo 319836 321971 := bstep (se 1 (by rfl) ⟨241478, by rfl⟩ : syracuseStep 321971 = 482957) B482957
theorem B321987 : Blo 319836 321987 := bstep (se 1 (by rfl) ⟨241490, by rfl⟩ : syracuseStep 321987 = 482981) B482981
theorem B322003 : Blo 319836 322003 := bstep (se 1 (by rfl) ⟨241502, by rfl⟩ : syracuseStep 322003 = 483005) B483005
theorem B911843 : Blo 319836 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B322019 : Blo 319836 322019 := bstep (se 1 (by rfl) ⟨241514, by rfl⟩ : syracuseStep 322019 = 483029) B483029
theorem B518627 : Blo 319836 518627 := bstep (se 1 (by rfl) ⟨388970, by rfl⟩ : syracuseStep 518627 = 777941) B777941
theorem B1010161 : Blo 319836 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B322035 : Blo 319836 322035 := bstep (se 1 (by rfl) ⟨241526, by rfl⟩ : syracuseStep 322035 = 483053) B483053
theorem B322051 : Blo 319836 322051 := bstep (se 1 (by rfl) ⟨241538, by rfl⟩ : syracuseStep 322051 = 483077) B483077
theorem B322067 : Blo 319836 322067 := bstep (se 1 (by rfl) ⟨241550, by rfl⟩ : syracuseStep 322067 = 483101) B483101
theorem B322083 : Blo 319836 322083 := bstep (se 1 (by rfl) ⟨241562, by rfl⟩ : syracuseStep 322083 = 483125) B483125
theorem B1829425 : Blo 319836 1829425 := bstep (se 2 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 1829425 = 1372069) B1372069
theorem B322099 : Blo 319836 322099 := bstep (se 1 (by rfl) ⟨241574, by rfl⟩ : syracuseStep 322099 = 483149) B483149
theorem B813635 : Blo 319836 813635 := bstep (se 1 (by rfl) ⟨610226, by rfl⟩ : syracuseStep 813635 = 1220453) B1220453
theorem B322115 : Blo 319836 322115 := bstep (se 1 (by rfl) ⟨241586, by rfl⟩ : syracuseStep 322115 = 483173) B483173
theorem B322131 : Blo 319836 322131 := bstep (se 1 (by rfl) ⟨241598, by rfl⟩ : syracuseStep 322131 = 483197) B483197
theorem B322147 : Blo 319836 322147 := bstep (se 1 (by rfl) ⟨241610, by rfl⟩ : syracuseStep 322147 = 483221) B483221
theorem B322163 : Blo 319836 322163 := bstep (se 1 (by rfl) ⟨241622, by rfl⟩ : syracuseStep 322163 = 483245) B483245
theorem B322179 : Blo 319836 322179 := bstep (se 1 (by rfl) ⟨241634, by rfl⟩ : syracuseStep 322179 = 483269) B483269
theorem B322195 : Blo 319836 322195 := bstep (se 1 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 322195 = 483293) B483293
theorem B322211 : Blo 319836 322211 := bstep (se 1 (by rfl) ⟨241658, by rfl⟩ : syracuseStep 322211 = 483317) B483317
theorem B322227 : Blo 319836 322227 := bstep (se 1 (by rfl) ⟨241670, by rfl⟩ : syracuseStep 322227 = 483341) B483341
theorem B322243 : Blo 319836 322243 := bstep (se 1 (by rfl) ⟨241682, by rfl⟩ : syracuseStep 322243 = 483365) B483365
theorem B322259 : Blo 319836 322259 := bstep (se 1 (by rfl) ⟨241694, by rfl⟩ : syracuseStep 322259 = 483389) B483389
theorem B322275 : Blo 319836 322275 := bstep (se 1 (by rfl) ⟨241706, by rfl⟩ : syracuseStep 322275 = 483413) B483413
theorem B322291 : Blo 319836 322291 := bstep (se 1 (by rfl) ⟨241718, by rfl⟩ : syracuseStep 322291 = 483437) B483437
theorem B813827 : Blo 319836 813827 := bstep (se 1 (by rfl) ⟨610370, by rfl⟩ : syracuseStep 813827 = 1220741) B1220741
theorem B322307 : Blo 319836 322307 := bstep (se 1 (by rfl) ⟨241730, by rfl⟩ : syracuseStep 322307 = 483461) B483461
theorem B322323 : Blo 319836 322323 := bstep (se 1 (by rfl) ⟨241742, by rfl⟩ : syracuseStep 322323 = 483485) B483485
theorem B322339 : Blo 319836 322339 := bstep (se 1 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 322339 = 483509) B483509
theorem B387875 : Blo 319836 387875 := bstep (se 1 (by rfl) ⟨290906, by rfl⟩ : syracuseStep 387875 = 581813) B581813
theorem B322355 : Blo 319836 322355 := bstep (se 1 (by rfl) ⟨241766, by rfl⟩ : syracuseStep 322355 = 483533) B483533
theorem B322371 : Blo 319836 322371 := bstep (se 1 (by rfl) ⟨241778, by rfl⟩ : syracuseStep 322371 = 483557) B483557
theorem B322387 : Blo 319836 322387 := bstep (se 1 (by rfl) ⟨241790, by rfl⟩ : syracuseStep 322387 = 483581) B483581
theorem B322403 : Blo 319836 322403 := bstep (se 1 (by rfl) ⟨241802, by rfl⟩ : syracuseStep 322403 = 483605) B483605
theorem B322419 : Blo 319836 322419 := bstep (se 1 (by rfl) ⟨241814, by rfl⟩ : syracuseStep 322419 = 483629) B483629
theorem B322435 : Blo 319836 322435 := bstep (se 1 (by rfl) ⟨241826, by rfl⟩ : syracuseStep 322435 = 483653) B483653
theorem B322451 : Blo 319836 322451 := bstep (se 1 (by rfl) ⟨241838, by rfl⟩ : syracuseStep 322451 = 483677) B483677
theorem B322467 : Blo 319836 322467 := bstep (se 1 (by rfl) ⟨241850, by rfl⟩ : syracuseStep 322467 = 483701) B483701
theorem B322483 : Blo 319836 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B322499 : Blo 319836 322499 := bstep (se 1 (by rfl) ⟨241874, by rfl⟩ : syracuseStep 322499 = 483749) B483749
theorem B3533765 : Blo 319836 3533765 := bstep (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) B662581
theorem B322515 : Blo 319836 322515 := bstep (se 1 (by rfl) ⟨241886, by rfl⟩ : syracuseStep 322515 = 483773) B483773
theorem B322531 : Blo 319836 322531 := bstep (se 1 (by rfl) ⟨241898, by rfl⟩ : syracuseStep 322531 = 483797) B483797
theorem B322547 : Blo 319836 322547 := bstep (se 1 (by rfl) ⟨241910, by rfl⟩ : syracuseStep 322547 = 483821) B483821
theorem B322563 : Blo 319836 322563 := bstep (se 1 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 322563 = 483845) B483845
theorem B322579 : Blo 319836 322579 := bstep (se 1 (by rfl) ⟨241934, by rfl⟩ : syracuseStep 322579 = 483869) B483869
theorem B322595 : Blo 319836 322595 := bstep (se 1 (by rfl) ⟨241946, by rfl⟩ : syracuseStep 322595 = 483893) B483893
theorem B322611 : Blo 319836 322611 := bstep (se 1 (by rfl) ⟨241958, by rfl⟩ : syracuseStep 322611 = 483917) B483917
theorem B322627 : Blo 319836 322627 := bstep (se 1 (by rfl) ⟨241970, by rfl⟩ : syracuseStep 322627 = 483941) B483941
theorem B388163 : Blo 319836 388163 := bstep (se 1 (by rfl) ⟨291122, by rfl⟩ : syracuseStep 388163 = 582245) B582245
theorem B322643 : Blo 319836 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B322659 : Blo 319836 322659 := bstep (se 1 (by rfl) ⟨241994, by rfl⟩ : syracuseStep 322659 = 483989) B483989
theorem B322675 : Blo 319836 322675 := bstep (se 1 (by rfl) ⟨242006, by rfl⟩ : syracuseStep 322675 = 484013) B484013
theorem B322691 : Blo 319836 322691 := bstep (se 1 (by rfl) ⟨242018, by rfl⟩ : syracuseStep 322691 = 484037) B484037
theorem B322707 : Blo 319836 322707 := bstep (se 1 (by rfl) ⟨242030, by rfl⟩ : syracuseStep 322707 = 484061) B484061
theorem B322723 : Blo 319836 322723 := bstep (se 1 (by rfl) ⟨242042, by rfl⟩ : syracuseStep 322723 = 484085) B484085
theorem B322739 : Blo 319836 322739 := bstep (se 1 (by rfl) ⟨242054, by rfl⟩ : syracuseStep 322739 = 484109) B484109
theorem B322755 : Blo 319836 322755 := bstep (se 1 (by rfl) ⟨242066, by rfl⟩ : syracuseStep 322755 = 484133) B484133
theorem B322771 : Blo 319836 322771 := bstep (se 1 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 322771 = 484157) B484157
theorem B322787 : Blo 319836 322787 := bstep (se 1 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 322787 = 484181) B484181
theorem B322803 : Blo 319836 322803 := bstep (se 1 (by rfl) ⟨242102, by rfl⟩ : syracuseStep 322803 = 484205) B484205
theorem B322819 : Blo 319836 322819 := bstep (se 1 (by rfl) ⟨242114, by rfl⟩ : syracuseStep 322819 = 484229) B484229
theorem B388355 : Blo 319836 388355 := bstep (se 1 (by rfl) ⟨291266, by rfl⟩ : syracuseStep 388355 = 582533) B582533
theorem B322835 : Blo 319836 322835 := bstep (se 1 (by rfl) ⟨242126, by rfl⟩ : syracuseStep 322835 = 484253) B484253
theorem B322851 : Blo 319836 322851 := bstep (se 1 (by rfl) ⟨242138, by rfl⟩ : syracuseStep 322851 = 484277) B484277
theorem B2223409 : Blo 319836 2223409 := bstep (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) B1667557
theorem B322867 : Blo 319836 322867 := bstep (se 1 (by rfl) ⟨242150, by rfl⟩ : syracuseStep 322867 = 484301) B484301
theorem B322883 : Blo 319836 322883 := bstep (se 1 (by rfl) ⟨242162, by rfl⟩ : syracuseStep 322883 = 484325) B484325
theorem B322899 : Blo 319836 322899 := bstep (se 1 (by rfl) ⟨242174, by rfl⟩ : syracuseStep 322899 = 484349) B484349
theorem B322915 : Blo 319836 322915 := bstep (se 1 (by rfl) ⟨242186, by rfl⟩ : syracuseStep 322915 = 484373) B484373
theorem B322931 : Blo 319836 322931 := bstep (se 1 (by rfl) ⟨242198, by rfl⟩ : syracuseStep 322931 = 484397) B484397
theorem B322947 : Blo 319836 322947 := bstep (se 1 (by rfl) ⟨242210, by rfl⟩ : syracuseStep 322947 = 484421) B484421
theorem B322963 : Blo 319836 322963 := bstep (se 1 (by rfl) ⟨242222, by rfl⟩ : syracuseStep 322963 = 484445) B484445
theorem B322979 : Blo 319836 322979 := bstep (se 1 (by rfl) ⟨242234, by rfl⟩ : syracuseStep 322979 = 484469) B484469
theorem B322995 : Blo 319836 322995 := bstep (se 1 (by rfl) ⟨242246, by rfl⟩ : syracuseStep 322995 = 484493) B484493
theorem B323011 : Blo 319836 323011 := bstep (se 1 (by rfl) ⟨242258, by rfl⟩ : syracuseStep 323011 = 484517) B484517
theorem B912845 : Blo 319836 912845 := bstep (se 3 (by rfl) ⟨171158, by rfl⟩ : syracuseStep 912845 = 342317) B342317
theorem B323027 : Blo 319836 323027 := bstep (se 1 (by rfl) ⟨242270, by rfl⟩ : syracuseStep 323027 = 484541) B484541
theorem B323043 : Blo 319836 323043 := bstep (se 1 (by rfl) ⟨242282, by rfl⟩ : syracuseStep 323043 = 484565) B484565
theorem B323059 : Blo 319836 323059 := bstep (se 1 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 323059 = 484589) B484589
theorem B323075 : Blo 319836 323075 := bstep (se 1 (by rfl) ⟨242306, by rfl⟩ : syracuseStep 323075 = 484613) B484613
theorem B323091 : Blo 319836 323091 := bstep (se 1 (by rfl) ⟨242318, by rfl⟩ : syracuseStep 323091 = 484637) B484637
theorem B323107 : Blo 319836 323107 := bstep (se 1 (by rfl) ⟨242330, by rfl⟩ : syracuseStep 323107 = 484661) B484661
theorem B323123 : Blo 319836 323123 := bstep (se 1 (by rfl) ⟨242342, by rfl⟩ : syracuseStep 323123 = 484685) B484685
theorem B978499 : Blo 319836 978499 := bstep (se 1 (by rfl) ⟨733874, by rfl⟩ : syracuseStep 978499 = 1467749) B1467749
theorem B323139 : Blo 319836 323139 := bstep (se 1 (by rfl) ⟨242354, by rfl⟩ : syracuseStep 323139 = 484709) B484709
theorem B323155 : Blo 319836 323155 := bstep (se 1 (by rfl) ⟨242366, by rfl⟩ : syracuseStep 323155 = 484733) B484733
theorem B323171 : Blo 319836 323171 := bstep (se 1 (by rfl) ⟨242378, by rfl⟩ : syracuseStep 323171 = 484757) B484757
theorem B323187 : Blo 319836 323187 := bstep (se 1 (by rfl) ⟨242390, by rfl⟩ : syracuseStep 323187 = 484781) B484781
theorem B913027 : Blo 319836 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B323203 : Blo 319836 323203 := bstep (se 1 (by rfl) ⟨242402, by rfl⟩ : syracuseStep 323203 = 484805) B484805
theorem B323219 : Blo 319836 323219 := bstep (se 1 (by rfl) ⟨242414, by rfl⟩ : syracuseStep 323219 = 484829) B484829
theorem B323235 : Blo 319836 323235 := bstep (se 1 (by rfl) ⟨242426, by rfl⟩ : syracuseStep 323235 = 484853) B484853
theorem B814769 : Blo 319836 814769 := bstep (se 2 (by rfl) ⟨305538, by rfl⟩ : syracuseStep 814769 = 611077) B611077
theorem B323251 : Blo 319836 323251 := bstep (se 1 (by rfl) ⟨242438, by rfl⟩ : syracuseStep 323251 = 484877) B484877
theorem B323267 : Blo 319836 323267 := bstep (se 1 (by rfl) ⟨242450, by rfl⟩ : syracuseStep 323267 = 484901) B484901
theorem B323283 : Blo 319836 323283 := bstep (se 1 (by rfl) ⟨242462, by rfl⟩ : syracuseStep 323283 = 484925) B484925
theorem B814819 : Blo 319836 814819 := bstep (se 1 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 814819 = 1222229) B1222229
theorem B323299 : Blo 319836 323299 := bstep (se 1 (by rfl) ⟨242474, by rfl⟩ : syracuseStep 323299 = 484949) B484949
theorem B323315 : Blo 319836 323315 := bstep (se 1 (by rfl) ⟨242486, by rfl⟩ : syracuseStep 323315 = 484973) B484973
theorem B323331 : Blo 319836 323331 := bstep (se 1 (by rfl) ⟨242498, by rfl⟩ : syracuseStep 323331 = 484997) B484997
theorem B1371917 : Blo 319836 1371917 := bstep (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) B514469
theorem B323347 : Blo 319836 323347 := bstep (se 1 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 323347 = 485021) B485021
theorem B913187 : Blo 319836 913187 := bstep (se 1 (by rfl) ⟨684890, by rfl⟩ : syracuseStep 913187 = 1369781) B1369781
theorem B323363 : Blo 319836 323363 := bstep (se 1 (by rfl) ⟨242522, by rfl⟩ : syracuseStep 323363 = 485045) B485045
theorem B323379 : Blo 319836 323379 := bstep (se 1 (by rfl) ⟨242534, by rfl⟩ : syracuseStep 323379 = 485069) B485069
theorem B323395 : Blo 319836 323395 := bstep (se 1 (by rfl) ⟨242546, by rfl⟩ : syracuseStep 323395 = 485093) B485093
theorem B323411 : Blo 319836 323411 := bstep (se 1 (by rfl) ⟨242558, by rfl⟩ : syracuseStep 323411 = 485117) B485117
theorem B323427 : Blo 319836 323427 := bstep (se 1 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 323427 = 485141) B485141
theorem B814961 : Blo 319836 814961 := bstep (se 2 (by rfl) ⟨305610, by rfl⟩ : syracuseStep 814961 = 611221) B611221
theorem B323443 : Blo 319836 323443 := bstep (se 1 (by rfl) ⟨242582, by rfl⟩ : syracuseStep 323443 = 485165) B485165
theorem B323459 : Blo 319836 323459 := bstep (se 1 (by rfl) ⟨242594, by rfl⟩ : syracuseStep 323459 = 485189) B485189
theorem B323475 : Blo 319836 323475 := bstep (se 1 (by rfl) ⟨242606, by rfl⟩ : syracuseStep 323475 = 485213) B485213
theorem B323491 : Blo 319836 323491 := bstep (se 1 (by rfl) ⟨242618, by rfl⟩ : syracuseStep 323491 = 485237) B485237
theorem B323507 : Blo 319836 323507 := bstep (se 1 (by rfl) ⟨242630, by rfl⟩ : syracuseStep 323507 = 485261) B485261
theorem B323523 : Blo 319836 323523 := bstep (se 1 (by rfl) ⟨242642, by rfl⟩ : syracuseStep 323523 = 485285) B485285
theorem B1732549 : Blo 319836 1732549 := bstep (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) B324853
theorem B323539 : Blo 319836 323539 := bstep (se 1 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 323539 = 485309) B485309
theorem B1830883 : Blo 319836 1830883 := bstep (se 1 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 1830883 = 2746325) B2746325
theorem B323555 : Blo 319836 323555 := bstep (se 1 (by rfl) ⟨242666, by rfl⟩ : syracuseStep 323555 = 485333) B485333
theorem B323571 : Blo 319836 323571 := bstep (se 1 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 323571 = 485357) B485357
theorem B323587 : Blo 319836 323587 := bstep (se 1 (by rfl) ⟨242690, by rfl⟩ : syracuseStep 323587 = 485381) B485381
theorem B323603 : Blo 319836 323603 := bstep (se 1 (by rfl) ⟨242702, by rfl⟩ : syracuseStep 323603 = 485405) B485405
theorem B323619 : Blo 319836 323619 := bstep (se 1 (by rfl) ⟨242714, by rfl⟩ : syracuseStep 323619 = 485429) B485429
theorem B323635 : Blo 319836 323635 := bstep (se 1 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 323635 = 485453) B485453
theorem B323651 : Blo 319836 323651 := bstep (se 1 (by rfl) ⟨242738, by rfl⟩ : syracuseStep 323651 = 485477) B485477
theorem B323667 : Blo 319836 323667 := bstep (se 1 (by rfl) ⟨242750, by rfl⟩ : syracuseStep 323667 = 485501) B485501
theorem B323683 : Blo 319836 323683 := bstep (se 1 (by rfl) ⟨242762, by rfl⟩ : syracuseStep 323683 = 485525) B485525
theorem B1634417 : Blo 319836 1634417 := bstep (se 2 (by rfl) ⟨612906, by rfl⟩ : syracuseStep 1634417 = 1225813) B1225813
theorem B323699 : Blo 319836 323699 := bstep (se 1 (by rfl) ⟨242774, by rfl⟩ : syracuseStep 323699 = 485549) B485549
theorem B323715 : Blo 319836 323715 := bstep (se 1 (by rfl) ⟨242786, by rfl⟩ : syracuseStep 323715 = 485573) B485573
theorem B323731 : Blo 319836 323731 := bstep (se 1 (by rfl) ⟨242798, by rfl⟩ : syracuseStep 323731 = 485597) B485597
theorem B323747 : Blo 319836 323747 := bstep (se 1 (by rfl) ⟨242810, by rfl⟩ : syracuseStep 323747 = 485621) B485621
theorem B323763 : Blo 319836 323763 := bstep (se 1 (by rfl) ⟨242822, by rfl⟩ : syracuseStep 323763 = 485645) B485645
theorem B323779 : Blo 319836 323779 := bstep (se 1 (by rfl) ⟨242834, by rfl⟩ : syracuseStep 323779 = 485669) B485669
theorem B323795 : Blo 319836 323795 := bstep (se 1 (by rfl) ⟨242846, by rfl⟩ : syracuseStep 323795 = 485693) B485693
theorem B323811 : Blo 319836 323811 := bstep (se 1 (by rfl) ⟨242858, by rfl⟩ : syracuseStep 323811 = 485717) B485717
theorem B323827 : Blo 319836 323827 := bstep (se 1 (by rfl) ⟨242870, by rfl⟩ : syracuseStep 323827 = 485741) B485741
theorem B684497 : Blo 319836 684497 := bstep (se 2 (by rfl) ⟨256686, by rfl⟩ : syracuseStep 684497 = 513373) B513373
theorem B1831409 : Blo 319836 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B488035 : Blo 319836 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B881425 : Blo 319836 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B914257 : Blo 319836 914257 := bstep (se 2 (by rfl) ⟨342846, by rfl⟩ : syracuseStep 914257 = 685693) B685693
theorem B815953 : Blo 319836 815953 := bstep (se 2 (by rfl) ⟨305982, by rfl⟩ : syracuseStep 815953 = 611965) B611965
theorem B2061233 : Blo 319836 2061233 := bstep (se 2 (by rfl) ⟨772962, by rfl⟩ : syracuseStep 2061233 = 1545925) B1545925
theorem B3666869 : Blo 319836 3666869 := bstep (se 5 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 3666869 = 343769) B343769
theorem B685027 : Blo 319836 685027 := bstep (se 1 (by rfl) ⟨513770, by rfl⟩ : syracuseStep 685027 = 1027541) B1027541
theorem B816227 : Blo 319836 816227 := bstep (se 1 (by rfl) ⟨612170, by rfl⟩ : syracuseStep 816227 = 1224341) B1224341
theorem B816419 : Blo 319836 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B456035 : Blo 319836 456035 := bstep (se 1 (by rfl) ⟨342026, by rfl⟩ : syracuseStep 456035 = 684053) B684053
theorem B2061773 : Blo 319836 2061773 := bstep (se 3 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 2061773 = 773165) B773165
theorem B1635875 : Blo 319836 1635875 := bstep (se 1 (by rfl) ⟨1226906, by rfl⟩ : syracuseStep 1635875 = 2453813) B2453813
theorem B1734257 : Blo 319836 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B620177 : Blo 319836 620177 := bstep (se 2 (by rfl) ⟨232566, by rfl⟩ : syracuseStep 620177 = 465133) B465133
theorem B980689 : Blo 319836 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B1832867 : Blo 319836 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B456673 : Blo 319836 456673 := bstep (se 2 (by rfl) ⟨171252, by rfl⟩ : syracuseStep 456673 = 342505) B342505
theorem B915533 : Blo 319836 915533 := bstep (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) B343325
theorem B456787 : Blo 319836 456787 := bstep (se 1 (by rfl) ⟨342590, by rfl⟩ : syracuseStep 456787 = 685181) B685181
theorem B1734797 : Blo 319836 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B1079459 : Blo 319836 1079459 := bstep (se 1 (by rfl) ⟨809594, by rfl⟩ : syracuseStep 1079459 = 1619189) B1619189
theorem B817361 : Blo 319836 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B915715 : Blo 319836 915715 := bstep (se 1 (by rfl) ⟨686786, by rfl⟩ : syracuseStep 915715 = 1373573) B1373573
theorem B817411 : Blo 319836 817411 := bstep (se 1 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 817411 = 1226117) B1226117
theorem B915761 : Blo 319836 915761 := bstep (se 2 (by rfl) ⟨343410, by rfl⟩ : syracuseStep 915761 = 686821) B686821
theorem B1636685 : Blo 319836 1636685 := bstep (se 3 (by rfl) ⟨306878, by rfl⟩ : syracuseStep 1636685 = 613757) B613757
theorem B1571185 : Blo 319836 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B6977933 : Blo 319836 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B817553 : Blo 319836 817553 := bstep (se 2 (by rfl) ⟨306582, by rfl⟩ : syracuseStep 817553 = 613165) B613165
theorem B1079729 : Blo 319836 1079729 := bstep (se 2 (by rfl) ⟨404898, by rfl⟩ : syracuseStep 1079729 = 809797) B809797
theorem B686513 : Blo 319836 686513 := bstep (se 2 (by rfl) ⟨257442, by rfl⟩ : syracuseStep 686513 = 514885) B514885
theorem B686531 : Blo 319836 686531 := bstep (se 1 (by rfl) ⟨514898, by rfl⟩ : syracuseStep 686531 = 1029797) B1029797
theorem B588259 : Blo 319836 588259 := bstep (se 1 (by rfl) ⟨441194, by rfl⟩ : syracuseStep 588259 = 882389) B882389
theorem B2521613 : Blo 319836 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B981613 : Blo 319836 981613 := bstep (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) B368105
theorem B1538851 : Blo 319836 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B523105 : Blo 319836 523105 := bstep (se 2 (by rfl) ⟨196164, by rfl⟩ : syracuseStep 523105 = 392329) B392329
theorem B719729 : Blo 319836 719729 := bstep (se 2 (by rfl) ⟨269898, by rfl⟩ : syracuseStep 719729 = 539797) B539797
theorem B719747 : Blo 319836 719747 := bstep (se 1 (by rfl) ⟨539810, by rfl⟩ : syracuseStep 719747 = 1079621) B1079621
theorem B1080269 : Blo 319836 1080269 := bstep (se 3 (by rfl) ⟨202550, by rfl⟩ : syracuseStep 1080269 = 405101) B405101
theorem B1080323 : Blo 319836 1080323 := bstep (se 1 (by rfl) ⟨810242, by rfl⟩ : syracuseStep 1080323 = 1620485) B1620485
theorem B720017 : Blo 319836 720017 := bstep (se 2 (by rfl) ⟨270006, by rfl⟩ : syracuseStep 720017 = 540013) B540013
theorem B720035 : Blo 319836 720035 := bstep (se 1 (by rfl) ⟨540026, by rfl⟩ : syracuseStep 720035 = 1080053) B1080053
theorem B1080593 : Blo 319836 1080593 := bstep (se 2 (by rfl) ⟨405222, by rfl⟩ : syracuseStep 1080593 = 810445) B810445
theorem B818545 : Blo 319836 818545 := bstep (se 2 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 818545 = 613909) B613909
theorem B458131 : Blo 319836 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B720305 : Blo 319836 720305 := bstep (se 2 (by rfl) ⟨270114, by rfl⟩ : syracuseStep 720305 = 540229) B540229
theorem B720323 : Blo 319836 720323 := bstep (se 1 (by rfl) ⟨540242, by rfl⟩ : syracuseStep 720323 = 1080485) B1080485
theorem B359923 : Blo 319836 359923 := bstep (se 1 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 359923 = 539885) B539885
theorem B491123 : Blo 319836 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B360067 : Blo 319836 360067 := bstep (se 1 (by rfl) ⟨270050, by rfl⟩ : syracuseStep 360067 = 540101) B540101
theorem B818819 : Blo 319836 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B687761 : Blo 319836 687761 := bstep (se 2 (by rfl) ⟨257910, by rfl⟩ : syracuseStep 687761 = 515821) B515821
theorem B720593 : Blo 319836 720593 := bstep (se 2 (by rfl) ⟨270222, by rfl⟩ : syracuseStep 720593 = 540445) B540445
theorem B720611 : Blo 319836 720611 := bstep (se 1 (by rfl) ⟨540458, by rfl⟩ : syracuseStep 720611 = 1080917) B1080917
theorem B917219 : Blo 319836 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B1834757 : Blo 319836 1834757 := bstep (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) B344017
theorem B360211 : Blo 319836 360211 := bstep (se 1 (by rfl) ⟨270158, by rfl⟩ : syracuseStep 360211 = 540317) B540317
theorem B1081133 : Blo 319836 1081133 := bstep (se 3 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 1081133 = 405425) B405425
theorem B819011 : Blo 319836 819011 := bstep (se 1 (by rfl) ⟨614258, by rfl⟩ : syracuseStep 819011 = 1228517) B1228517
theorem B1081187 : Blo 319836 1081187 := bstep (se 1 (by rfl) ⟨810890, by rfl⟩ : syracuseStep 1081187 = 1621781) B1621781
theorem B360355 : Blo 319836 360355 := bstep (se 1 (by rfl) ⟨270266, by rfl⟩ : syracuseStep 360355 = 540533) B540533
theorem B720881 : Blo 319836 720881 := bstep (se 2 (by rfl) ⟨270330, by rfl⟩ : syracuseStep 720881 = 540661) B540661
theorem B917527 : Blo 319836 917527 := bstep (se 1 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 917527 = 1376291) B1376291
theorem B1048627 : Blo 319836 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B720971 : Blo 319836 720971 := bstep (se 1 (by rfl) ⟨540728, by rfl⟩ : syracuseStep 720971 = 1081457) B1081457
theorem B360535 : Blo 319836 360535 := bstep (se 1 (by rfl) ⟨270401, by rfl⟩ : syracuseStep 360535 = 540803) B540803
theorem B655447 : Blo 319836 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B2752613 : Blo 319836 2752613 := bstep (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) B516115
theorem B2457701 : Blo 319836 2457701 := bstep (se 4 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 2457701 = 460819) B460819
theorem B721025 : Blo 319836 721025 := bstep (se 2 (by rfl) ⟨270384, by rfl⟩ : syracuseStep 721025 = 540769) B540769
theorem B1081565 : Blo 319836 1081565 := bstep (se 3 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 1081565 = 405587) B405587
theorem B360715 : Blo 319836 360715 := bstep (se 1 (by rfl) ⟨270536, by rfl⟩ : syracuseStep 360715 = 541073) B541073
theorem B721241 : Blo 319836 721241 := bstep (se 2 (by rfl) ⟨270465, by rfl⟩ : syracuseStep 721241 = 540931) B540931
theorem B2326877 : Blo 319836 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B4817251 : Blo 319836 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B360823 : Blo 319836 360823 := bstep (se 1 (by rfl) ⟨270617, by rfl⟩ : syracuseStep 360823 = 541235) B541235
theorem B688513 : Blo 319836 688513 := bstep (se 2 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 688513 = 516385) B516385
theorem B393611 : Blo 319836 393611 := bstep (se 1 (by rfl) ⟨295208, by rfl⟩ : syracuseStep 393611 = 590417) B590417
theorem B721331 : Blo 319836 721331 := bstep (se 1 (by rfl) ⟨540998, by rfl⟩ : syracuseStep 721331 = 1081997) B1081997
theorem B819659 : Blo 319836 819659 := bstep (se 1 (by rfl) ⟨614744, by rfl⟩ : syracuseStep 819659 = 1229489) B1229489
theorem B721367 : Blo 319836 721367 := bstep (se 1 (by rfl) ⟨541025, by rfl⟩ : syracuseStep 721367 = 1082051) B1082051
theorem B1966609 : Blo 319836 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B361003 : Blo 319836 361003 := bstep (se 1 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 361003 = 541505) B541505
theorem B2327105 : Blo 319836 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B2458187 : Blo 319836 2458187 := bstep (se 1 (by rfl) ⟨1843640, by rfl⟩ : syracuseStep 2458187 = 3687281) B3687281
theorem B721547 : Blo 319836 721547 := bstep (se 1 (by rfl) ⟨541160, by rfl⟩ : syracuseStep 721547 = 1082321) B1082321
theorem B361111 : Blo 319836 361111 := bstep (se 1 (by rfl) ⟨270833, by rfl⟩ : syracuseStep 361111 = 541667) B541667
theorem B721601 : Blo 319836 721601 := bstep (se 2 (by rfl) ⟨270600, by rfl⟩ : syracuseStep 721601 = 541201) B541201
theorem B2753297 : Blo 319836 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B361291 : Blo 319836 361291 := bstep (se 1 (by rfl) ⟨270968, by rfl⟩ : syracuseStep 361291 = 541937) B541937
theorem B525145 : Blo 319836 525145 := bstep (se 2 (by rfl) ⟨196929, by rfl⟩ : syracuseStep 525145 = 393859) B393859
theorem B721817 : Blo 319836 721817 := bstep (se 2 (by rfl) ⟨270681, by rfl⟩ : syracuseStep 721817 = 541363) B541363
theorem B361399 : Blo 319836 361399 := bstep (se 1 (by rfl) ⟨271049, by rfl⟩ : syracuseStep 361399 = 542099) B542099
theorem B1049537 : Blo 319836 1049537 := bstep (se 2 (by rfl) ⟨393576, by rfl⟩ : syracuseStep 1049537 = 787153) B787153
theorem B721907 : Blo 319836 721907 := bstep (se 1 (by rfl) ⟨541430, by rfl⟩ : syracuseStep 721907 = 1082861) B1082861
theorem B721943 : Blo 319836 721943 := bstep (se 1 (by rfl) ⟨541457, by rfl⟩ : syracuseStep 721943 = 1082915) B1082915
theorem B689239 : Blo 319836 689239 := bstep (se 1 (by rfl) ⟨516929, by rfl⟩ : syracuseStep 689239 = 1033859) B1033859
theorem B361579 : Blo 319836 361579 := bstep (se 1 (by rfl) ⟨271184, by rfl⟩ : syracuseStep 361579 = 542369) B542369
theorem B722123 : Blo 319836 722123 := bstep (se 1 (by rfl) ⟨541592, by rfl⟩ : syracuseStep 722123 = 1083185) B1083185
theorem B361687 : Blo 319836 361687 := bstep (se 1 (by rfl) ⟨271265, by rfl⟩ : syracuseStep 361687 = 542531) B542531
theorem B722177 : Blo 319836 722177 := bstep (se 2 (by rfl) ⟨270816, by rfl⟩ : syracuseStep 722177 = 541633) B541633
theorem B1082699 : Blo 319836 1082699 := bstep (se 1 (by rfl) ⟨812024, by rfl⟩ : syracuseStep 1082699 = 1624049) B1624049
theorem B918859 : Blo 319836 918859 := bstep (se 1 (by rfl) ⟨689144, by rfl⟩ : syracuseStep 918859 = 1378289) B1378289
theorem B4130149 : Blo 319836 4130149 := bstep (se 4 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 4130149 = 774403) B774403
theorem B361867 : Blo 319836 361867 := bstep (se 1 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 361867 = 542801) B542801
theorem B329131 : Blo 319836 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B1312193 : Blo 319836 1312193 := bstep (se 2 (by rfl) ⟨492072, by rfl⟩ : syracuseStep 1312193 = 984145) B984145
theorem B722393 : Blo 319836 722393 := bstep (se 2 (by rfl) ⟨270897, by rfl⟩ : syracuseStep 722393 = 541795) B541795
theorem B361975 : Blo 319836 361975 := bstep (se 1 (by rfl) ⟨271481, by rfl⟩ : syracuseStep 361975 = 542963) B542963
theorem B722483 : Blo 319836 722483 := bstep (se 1 (by rfl) ⟨541862, by rfl⟩ : syracuseStep 722483 = 1083725) B1083725
theorem B722519 : Blo 319836 722519 := bstep (se 1 (by rfl) ⟨541889, by rfl⟩ : syracuseStep 722519 = 1083779) B1083779
theorem B1082969 : Blo 319836 1082969 := bstep (se 2 (by rfl) ⟨406113, by rfl⟩ : syracuseStep 1082969 = 812227) B812227
theorem B919133 : Blo 319836 919133 := bstep (se 3 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 919133 = 344675) B344675
theorem B984727 : Blo 319836 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B362155 : Blo 319836 362155 := bstep (se 1 (by rfl) ⟨271616, by rfl⟩ : syracuseStep 362155 = 543233) B543233
theorem B722699 : Blo 319836 722699 := bstep (se 1 (by rfl) ⟨542024, by rfl⟩ : syracuseStep 722699 = 1084049) B1084049
theorem B362263 : Blo 319836 362263 := bstep (se 1 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 362263 = 543395) B543395
theorem B722753 : Blo 319836 722753 := bstep (se 2 (by rfl) ⟨271032, by rfl⟩ : syracuseStep 722753 = 542065) B542065
theorem B690059 : Blo 319836 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B919475 : Blo 319836 919475 := bstep (se 1 (by rfl) ⟨689606, by rfl⟩ : syracuseStep 919475 = 1379213) B1379213
theorem B362443 : Blo 319836 362443 := bstep (se 1 (by rfl) ⟨271832, by rfl⟩ : syracuseStep 362443 = 543665) B543665
theorem B722969 : Blo 319836 722969 := bstep (se 2 (by rfl) ⟨271113, by rfl⟩ : syracuseStep 722969 = 542227) B542227
theorem B362551 : Blo 319836 362551 := bstep (se 1 (by rfl) ⟨271913, by rfl⟩ : syracuseStep 362551 = 543827) B543827
theorem B723059 : Blo 319836 723059 := bstep (se 1 (by rfl) ⟨542294, by rfl⟩ : syracuseStep 723059 = 1084589) B1084589
theorem B723095 : Blo 319836 723095 := bstep (se 1 (by rfl) ⟨542321, by rfl⟩ : syracuseStep 723095 = 1084643) B1084643
theorem B362731 : Blo 319836 362731 := bstep (se 1 (by rfl) ⟨272048, by rfl⟩ : syracuseStep 362731 = 544097) B544097
theorem B1083671 : Blo 319836 1083671 := bstep (se 1 (by rfl) ⟨812753, by rfl⟩ : syracuseStep 1083671 = 1625507) B1625507
theorem B723275 : Blo 319836 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B362839 : Blo 319836 362839 := bstep (se 1 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 362839 = 544259) B544259
theorem B723329 : Blo 319836 723329 := bstep (se 2 (by rfl) ⟨271248, by rfl⟩ : syracuseStep 723329 = 542497) B542497
theorem B363019 : Blo 319836 363019 := bstep (se 1 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 363019 = 544529) B544529
theorem B723545 : Blo 319836 723545 := bstep (se 2 (by rfl) ⟨271329, by rfl⟩ : syracuseStep 723545 = 542659) B542659
theorem B363127 : Blo 319836 363127 := bstep (se 1 (by rfl) ⟨272345, by rfl⟩ : syracuseStep 363127 = 544691) B544691
theorem B1215107 : Blo 319836 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B1215121 : Blo 319836 1215121 := bstep (se 2 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 1215121 = 911341) B911341
theorem B723635 : Blo 319836 723635 := bstep (se 1 (by rfl) ⟨542726, by rfl⟩ : syracuseStep 723635 = 1085453) B1085453
theorem B723671 : Blo 319836 723671 := bstep (se 1 (by rfl) ⟨542753, by rfl⟩ : syracuseStep 723671 = 1085507) B1085507
theorem B690905 : Blo 319836 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B363307 : Blo 319836 363307 := bstep (se 1 (by rfl) ⟨272480, by rfl⟩ : syracuseStep 363307 = 544961) B544961
theorem B1084211 : Blo 319836 1084211 := bstep (se 1 (by rfl) ⟨813158, by rfl⟩ : syracuseStep 1084211 = 1626317) B1626317
theorem B723851 : Blo 319836 723851 := bstep (se 1 (by rfl) ⟨542888, by rfl⟩ : syracuseStep 723851 = 1085777) B1085777
theorem B2198423 : Blo 319836 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B363415 : Blo 319836 363415 := bstep (se 1 (by rfl) ⟨272561, by rfl⟩ : syracuseStep 363415 = 545123) B545123
theorem B1215425 : Blo 319836 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B723905 : Blo 319836 723905 := bstep (se 2 (by rfl) ⟨271464, by rfl⟩ : syracuseStep 723905 = 542929) B542929
theorem B1084481 : Blo 319836 1084481 := bstep (se 2 (by rfl) ⟨406680, by rfl⟩ : syracuseStep 1084481 = 813361) B813361
theorem B363595 : Blo 319836 363595 := bstep (se 1 (by rfl) ⟨272696, by rfl⟩ : syracuseStep 363595 = 545393) B545393
theorem B1838173 : Blo 319836 1838173 := bstep (se 3 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 1838173 = 689315) B689315
theorem B724121 : Blo 319836 724121 := bstep (se 2 (by rfl) ⟨271545, by rfl⟩ : syracuseStep 724121 = 543091) B543091
theorem B363703 : Blo 319836 363703 := bstep (se 1 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 363703 = 545555) B545555
theorem B724211 : Blo 319836 724211 := bstep (se 1 (by rfl) ⟨543158, by rfl⟩ : syracuseStep 724211 = 1086317) B1086317
theorem B1379587 : Blo 319836 1379587 := bstep (se 1 (by rfl) ⟨1034690, by rfl⟩ : syracuseStep 1379587 = 2069381) B2069381
theorem B724247 : Blo 319836 724247 := bstep (se 1 (by rfl) ⟨543185, by rfl⟩ : syracuseStep 724247 = 1086371) B1086371
theorem B1346881 : Blo 319836 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B363883 : Blo 319836 363883 := bstep (se 1 (by rfl) ⟨272912, by rfl⟩ : syracuseStep 363883 = 545825) B545825
theorem B691571 : Blo 319836 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B724427 : Blo 319836 724427 := bstep (se 1 (by rfl) ⟨543320, by rfl⟩ : syracuseStep 724427 = 1086641) B1086641
theorem B363991 : Blo 319836 363991 := bstep (se 1 (by rfl) ⟨272993, by rfl⟩ : syracuseStep 363991 = 545987) B545987
theorem B724481 : Blo 319836 724481 := bstep (se 2 (by rfl) ⟨271680, by rfl⟩ : syracuseStep 724481 = 543361) B543361
theorem B1379929 : Blo 319836 1379929 := bstep (se 2 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 1379929 = 1034947) B1034947
theorem B1216093 : Blo 319836 1216093 := bstep (se 3 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 1216093 = 456035) B456035
theorem B1085021 : Blo 319836 1085021 := bstep (se 3 (by rfl) ⟨203441, by rfl⟩ : syracuseStep 1085021 = 406883) B406883
theorem B364171 : Blo 319836 364171 := bstep (se 1 (by rfl) ⟨273128, by rfl⟩ : syracuseStep 364171 = 546257) B546257
theorem B724697 : Blo 319836 724697 := bstep (se 2 (by rfl) ⟨271761, by rfl⟩ : syracuseStep 724697 = 543523) B543523
theorem B364279 : Blo 319836 364279 := bstep (se 1 (by rfl) ⟨273209, by rfl⟩ : syracuseStep 364279 = 546419) B546419
theorem B724787 : Blo 319836 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B724823 : Blo 319836 724823 := bstep (se 1 (by rfl) ⟨543617, by rfl⟩ : syracuseStep 724823 = 1087235) B1087235
theorem B2068355 : Blo 319836 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B921547 : Blo 319836 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B725003 : Blo 319836 725003 := bstep (se 1 (by rfl) ⟨543752, by rfl⟩ : syracuseStep 725003 = 1087505) B1087505
theorem B725057 : Blo 319836 725057 := bstep (se 2 (by rfl) ⟨271896, by rfl⟩ : syracuseStep 725057 = 543793) B543793
theorem B725273 : Blo 319836 725273 := bstep (se 2 (by rfl) ⟨271977, by rfl⟩ : syracuseStep 725273 = 543955) B543955
theorem B4624685 : Blo 319836 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B725363 : Blo 319836 725363 := bstep (se 1 (by rfl) ⟨544022, by rfl⟩ : syracuseStep 725363 = 1088045) B1088045
theorem B725399 : Blo 319836 725399 := bstep (se 1 (by rfl) ⟨544049, by rfl⟩ : syracuseStep 725399 = 1088099) B1088099
theorem B922049 : Blo 319836 922049 := bstep (se 2 (by rfl) ⟨345768, by rfl⟩ : syracuseStep 922049 = 691537) B691537
theorem B627187 : Blo 319836 627187 := bstep (se 1 (by rfl) ⟨470390, by rfl⟩ : syracuseStep 627187 = 940781) B940781
theorem B2789893 : Blo 319836 2789893 := bstep (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) B523105
theorem B1380887 : Blo 319836 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B3543587 : Blo 319836 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B365131 : Blo 319836 365131 := bstep (se 1 (by rfl) ⟨273848, by rfl⟩ : syracuseStep 365131 = 547697) B547697
theorem B725579 : Blo 319836 725579 := bstep (se 1 (by rfl) ⟨544184, by rfl⟩ : syracuseStep 725579 = 1088369) B1088369
theorem B725633 : Blo 319836 725633 := bstep (se 2 (by rfl) ⟨272112, by rfl⟩ : syracuseStep 725633 = 544225) B544225
theorem B1086155 : Blo 319836 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B1217369 : Blo 319836 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B725849 : Blo 319836 725849 := bstep (se 2 (by rfl) ⟨272193, by rfl⟩ : syracuseStep 725849 = 544387) B544387
theorem B725939 : Blo 319836 725939 := bstep (se 1 (by rfl) ⟨544454, by rfl⟩ : syracuseStep 725939 = 1088909) B1088909
theorem B725975 : Blo 319836 725975 := bstep (se 1 (by rfl) ⟨544481, by rfl⟩ : syracuseStep 725975 = 1088963) B1088963
theorem B1086425 : Blo 319836 1086425 := bstep (se 2 (by rfl) ⟨407409, by rfl⟩ : syracuseStep 1086425 = 814819) B814819
theorem B726155 : Blo 319836 726155 := bstep (se 1 (by rfl) ⟨544616, by rfl⟩ : syracuseStep 726155 = 1089233) B1089233
theorem B726209 : Blo 319836 726209 := bstep (se 2 (by rfl) ⟨272328, by rfl⟩ : syracuseStep 726209 = 544657) B544657
theorem B726425 : Blo 319836 726425 := bstep (se 2 (by rfl) ⟨272409, by rfl⟩ : syracuseStep 726425 = 544819) B544819
theorem B726515 : Blo 319836 726515 := bstep (se 1 (by rfl) ⟨544886, by rfl⟩ : syracuseStep 726515 = 1089773) B1089773
theorem B726551 : Blo 319836 726551 := bstep (se 1 (by rfl) ⟨544913, by rfl⟩ : syracuseStep 726551 = 1089827) B1089827
theorem B1644077 : Blo 319836 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B1087127 : Blo 319836 1087127 := bstep (se 1 (by rfl) ⟨815345, by rfl⟩ : syracuseStep 1087127 = 1630691) B1630691
theorem B726731 : Blo 319836 726731 := bstep (se 1 (by rfl) ⟨545048, by rfl⟩ : syracuseStep 726731 = 1090097) B1090097
theorem B726785 : Blo 319836 726785 := bstep (se 2 (by rfl) ⟨272544, by rfl⟩ : syracuseStep 726785 = 545089) B545089
theorem B727001 : Blo 319836 727001 := bstep (se 2 (by rfl) ⟨272625, by rfl⟩ : syracuseStep 727001 = 545251) B545251
theorem B727091 : Blo 319836 727091 := bstep (se 1 (by rfl) ⟨545318, by rfl⟩ : syracuseStep 727091 = 1090637) B1090637
theorem B727127 : Blo 319836 727127 := bstep (se 1 (by rfl) ⟨545345, by rfl⟩ : syracuseStep 727127 = 1090691) B1090691
theorem B1087667 : Blo 319836 1087667 := bstep (se 1 (by rfl) ⟨815750, by rfl⟩ : syracuseStep 1087667 = 1631501) B1631501
theorem B1382579 : Blo 319836 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B1153217 : Blo 319836 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B727307 : Blo 319836 727307 := bstep (se 1 (by rfl) ⟨545480, by rfl⟩ : syracuseStep 727307 = 1090961) B1090961
theorem B727361 : Blo 319836 727361 := bstep (se 2 (by rfl) ⟨272760, by rfl⟩ : syracuseStep 727361 = 545521) B545521
theorem B1218995 : Blo 319836 1218995 := bstep (se 1 (by rfl) ⟨914246, by rfl⟩ : syracuseStep 1218995 = 1828493) B1828493
theorem B1219009 : Blo 319836 1219009 := bstep (se 2 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 1219009 = 914257) B914257
theorem B1087937 : Blo 319836 1087937 := bstep (se 2 (by rfl) ⟨407976, by rfl⟩ : syracuseStep 1087937 = 815953) B815953
theorem B727577 : Blo 319836 727577 := bstep (se 2 (by rfl) ⟨272841, by rfl⟩ : syracuseStep 727577 = 545683) B545683
theorem B727667 : Blo 319836 727667 := bstep (se 1 (by rfl) ⟨545750, by rfl⟩ : syracuseStep 727667 = 1091501) B1091501
theorem B10394243 : Blo 319836 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B727703 : Blo 319836 727703 := bstep (se 1 (by rfl) ⟨545777, by rfl⟩ : syracuseStep 727703 = 1091555) B1091555
theorem B727883 : Blo 319836 727883 := bstep (se 1 (by rfl) ⟨545912, by rfl⟩ : syracuseStep 727883 = 1091825) B1091825
theorem B727937 : Blo 319836 727937 := bstep (se 2 (by rfl) ⟨272976, by rfl⟩ : syracuseStep 727937 = 545953) B545953
theorem B1973143 : Blo 319836 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B1088477 : Blo 319836 1088477 := bstep (se 3 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 1088477 = 408179) B408179
theorem B728153 : Blo 319836 728153 := bstep (se 2 (by rfl) ⟨273057, by rfl⟩ : syracuseStep 728153 = 546115) B546115
theorem B728243 : Blo 319836 728243 := bstep (se 1 (by rfl) ⟨546182, by rfl⟩ : syracuseStep 728243 = 1092365) B1092365
theorem B728279 : Blo 319836 728279 := bstep (se 1 (by rfl) ⟨546209, by rfl⟩ : syracuseStep 728279 = 1092419) B1092419
theorem B728459 : Blo 319836 728459 := bstep (se 1 (by rfl) ⟨546344, by rfl⟩ : syracuseStep 728459 = 1092689) B1092689
theorem B728513 : Blo 319836 728513 := bstep (se 2 (by rfl) ⟨273192, by rfl⟩ : syracuseStep 728513 = 546385) B546385
theorem B5250577 : Blo 319836 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B1089611 : Blo 319836 1089611 := bstep (se 1 (by rfl) ⟨817208, by rfl⟩ : syracuseStep 1089611 = 1634417) B1634417
theorem B1122497 : Blo 319836 1122497 := bstep (se 2 (by rfl) ⟨420936, by rfl⟩ : syracuseStep 1122497 = 841873) B841873
theorem B1220939 : Blo 319836 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B1220953 : Blo 319836 1220953 := bstep (se 2 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 1220953 = 915715) B915715
theorem B1089881 : Blo 319836 1089881 := bstep (se 2 (by rfl) ⟨408705, by rfl⟩ : syracuseStep 1089881 = 817411) B817411
theorem B5218661 : Blo 319836 5218661 := bstep (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) B978499
theorem B2597849 : Blo 319836 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B1090583 : Blo 319836 1090583 := bstep (se 1 (by rfl) ⟨817937, by rfl⟩ : syracuseStep 1090583 = 1635875) B1635875
theorem B1221911 : Blo 319836 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B1156445 : Blo 319836 1156445 := bstep (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) B433667
theorem B1156531 : Blo 319836 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B1091123 : Blo 319836 1091123 := bstep (se 1 (by rfl) ⟨818342, by rfl⟩ : syracuseStep 1091123 = 1636685) B1636685
theorem B1681075 : Blo 319836 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B1091393 : Blo 319836 1091393 := bstep (se 2 (by rfl) ⟨409272, by rfl⟩ : syracuseStep 1091393 = 818545) B818545
theorem B1550173 : Blo 319836 1550173 := bstep (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) B581315
theorem B2435345 : Blo 319836 2435345 := bstep (se 2 (by rfl) ⟨913254, by rfl⟩ : syracuseStep 2435345 = 1826509) B1826509
theorem B1091933 : Blo 319836 1091933 := bstep (se 3 (by rfl) ⟨204737, by rfl⟩ : syracuseStep 1091933 = 409475) B409475
theorem B1223171 : Blo 319836 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B2763821 : Blo 319836 2763821 := bstep (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) B1036433
theorem B404939 : Blo 319836 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B3517987 : Blo 319836 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B1650563 : Blo 319836 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B1159213 : Blo 319836 1159213 := bstep (se 3 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 1159213 = 434705) B434705
theorem B2306141 : Blo 319836 2306141 := bstep (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) B864803
theorem B405643 : Blo 319836 405643 := bstep (se 1 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 405643 = 608465) B608465
theorem B405911 : Blo 319836 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B1094219 : Blo 319836 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B1749721 : Blo 319836 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B406615 : Blo 319836 406615 := bstep (se 1 (by rfl) ⟨304961, by rfl⟩ : syracuseStep 406615 = 609923) B609923
theorem B1160513 : Blo 319836 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B865625 : Blo 319836 865625 := bstep (se 2 (by rfl) ⟨324609, by rfl⟩ : syracuseStep 865625 = 649219) B649219
theorem B1619351 : Blo 319836 1619351 := bstep (se 1 (by rfl) ⟨1214513, by rfl⟩ : syracuseStep 1619351 = 2429027) B2429027
theorem B734707 : Blo 319836 734707 := bstep (se 1 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 734707 = 1102061) B1102061
theorem B1226285 : Blo 319836 1226285 := bstep (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) B459857
theorem B11712205 : Blo 319836 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B2471755 : Blo 319836 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B1030067 : Blo 319836 1030067 := bstep (se 1 (by rfl) ⟨772550, by rfl⟩ : syracuseStep 1030067 = 1545101) B1545101
theorem B2439233 : Blo 319836 2439233 := bstep (se 2 (by rfl) ⟨914712, by rfl⟩ : syracuseStep 2439233 = 1829425) B1829425
theorem B1554497 : Blo 319836 1554497 := bstep (se 2 (by rfl) ⟨582936, by rfl⟩ : syracuseStep 1554497 = 1165873) B1165873
theorem B342091 : Blo 319836 342091 := bstep (se 1 (by rfl) ⟨256568, by rfl⟩ : syracuseStep 342091 = 513137) B513137
theorem B1227059 : Blo 319836 1227059 := bstep (se 1 (by rfl) ⟨920294, by rfl⟩ : syracuseStep 1227059 = 1840589) B1840589
theorem B932417 : Blo 319836 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B1030745 : Blo 319836 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B408331 : Blo 319836 408331 := bstep (se 1 (by rfl) ⟨306248, by rfl⟩ : syracuseStep 408331 = 612497) B612497
theorem B768791 : Blo 319836 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B1653805 : Blo 319836 1653805 := bstep (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) B620177
theorem B2964545 : Blo 319836 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B539851 : Blo 319836 539851 := bstep (se 1 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 539851 = 809777) B809777
theorem B539993 : Blo 319836 539993 := bstep (se 2 (by rfl) ⟨202497, by rfl⟩ : syracuseStep 539993 = 404995) B404995
theorem B540121 : Blo 319836 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B343607 : Blo 319836 343607 := bstep (se 1 (by rfl) ⟨257705, by rfl⟩ : syracuseStep 343607 = 515411) B515411
theorem B1097309 : Blo 319836 1097309 := bstep (se 3 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 1097309 = 411491) B411491
theorem B409303 : Blo 319836 409303 := bstep (se 1 (by rfl) ⟨306977, by rfl⟩ : syracuseStep 409303 = 613955) B613955
theorem B1228547 : Blo 319836 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B2310065 : Blo 319836 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B2441177 : Blo 319836 2441177 := bstep (se 2 (by rfl) ⟨915441, by rfl⟩ : syracuseStep 2441177 = 1830883) B1830883
theorem B540695 : Blo 319836 540695 := bstep (se 1 (by rfl) ⟨405521, by rfl⟩ : syracuseStep 540695 = 811043) B811043
theorem B1720385 : Blo 319836 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B1032257 : Blo 319836 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B540823 : Blo 319836 540823 := bstep (se 1 (by rfl) ⟨405617, by rfl⟩ : syracuseStep 540823 = 811235) B811235
theorem B1032385 : Blo 319836 1032385 := bstep (se 2 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 1032385 = 774289) B774289
theorem B1229003 : Blo 319836 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B344299 : Blo 319836 344299 := bstep (se 1 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 344299 = 516449) B516449
theorem B3916097 : Blo 319836 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B1229201 : Blo 319836 1229201 := bstep (se 2 (by rfl) ⟨460950, by rfl⟩ : syracuseStep 1229201 = 921901) B921901
theorem B1032641 : Blo 319836 1032641 := bstep (se 2 (by rfl) ⟨387240, by rfl⟩ : syracuseStep 1032641 = 774481) B774481
theorem B541451 : Blo 319836 541451 := bstep (se 1 (by rfl) ⟨406088, by rfl⟩ : syracuseStep 541451 = 812177) B812177
theorem B770867 : Blo 319836 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B1622915 : Blo 319836 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B541579 : Blo 319836 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B8111027 : Blo 319836 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B541721 : Blo 319836 541721 := bstep (se 2 (by rfl) ⟨203145, by rfl⟩ : syracuseStep 541721 = 406291) B406291
theorem B541849 : Blo 319836 541849 := bstep (se 2 (by rfl) ⟨203193, by rfl⟩ : syracuseStep 541849 = 406387) B406387
theorem B1164547 : Blo 319836 1164547 := bstep (se 1 (by rfl) ⟨873410, by rfl⟩ : syracuseStep 1164547 = 1746821) B1746821
theorem B607819 : Blo 319836 607819 := bstep (se 1 (by rfl) ⟨455864, by rfl⟩ : syracuseStep 607819 = 911729) B911729
theorem B607895 : Blo 319836 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B345751 : Blo 319836 345751 := bstep (se 1 (by rfl) ⟨259313, by rfl⟩ : syracuseStep 345751 = 518627) B518627
theorem B542423 : Blo 319836 542423 := bstep (se 1 (by rfl) ⟨406817, by rfl⟩ : syracuseStep 542423 = 813635) B813635
theorem B771905 : Blo 319836 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B542551 : Blo 319836 542551 := bstep (se 1 (by rfl) ⟨406913, by rfl⟩ : syracuseStep 542551 = 813827) B813827
theorem B1034333 : Blo 319836 1034333 := bstep (se 3 (by rfl) ⟨193937, by rfl⟩ : syracuseStep 1034333 = 387875) B387875
theorem B608563 : Blo 319836 608563 := bstep (se 1 (by rfl) ⟨456422, by rfl⟩ : syracuseStep 608563 = 912845) B912845
theorem B543179 : Blo 319836 543179 := bstep (se 1 (by rfl) ⟨407384, by rfl⟩ : syracuseStep 543179 = 814769) B814769
theorem B9423373 : Blo 319836 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B608791 : Blo 319836 608791 := bstep (se 1 (by rfl) ⟨456593, by rfl⟩ : syracuseStep 608791 = 913187) B913187
theorem B543307 : Blo 319836 543307 := bstep (se 1 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 543307 = 814961) B814961
theorem B608897 : Blo 319836 608897 := bstep (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) B456673
theorem B543449 : Blo 319836 543449 := bstep (se 2 (by rfl) ⟨203793, by rfl⟩ : syracuseStep 543449 = 407587) B407587
theorem B609049 : Blo 319836 609049 := bstep (se 2 (by rfl) ⟨228393, by rfl⟩ : syracuseStep 609049 = 456787) B456787
theorem B543577 : Blo 319836 543577 := bstep (se 2 (by rfl) ⟨203841, by rfl⟩ : syracuseStep 543577 = 407683) B407683
theorem B1035101 : Blo 319836 1035101 := bstep (se 3 (by rfl) ⟨194081, by rfl⟩ : syracuseStep 1035101 = 388163) B388163
theorem B2739217 : Blo 319836 2739217 := bstep (se 2 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 2739217 = 2054413) B2054413
theorem B2739491 : Blo 319836 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B2444579 : Blo 319836 2444579 := bstep (se 1 (by rfl) ⟨1833434, by rfl⟩ : syracuseStep 2444579 = 3666869) B3666869
theorem B1035613 : Blo 319836 1035613 := bstep (se 3 (by rfl) ⟨194177, by rfl⟩ : syracuseStep 1035613 = 388355) B388355
theorem B544151 : Blo 319836 544151 := bstep (se 1 (by rfl) ⟨408113, by rfl⟩ : syracuseStep 544151 = 816227) B816227
theorem B544279 : Blo 319836 544279 := bstep (se 1 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 544279 = 816419) B816419
theorem B708185 : Blo 319836 708185 := bstep (se 2 (by rfl) ⟨265569, by rfl⟩ : syracuseStep 708185 = 531139) B531139
theorem B577163 : Blo 319836 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B1298099 : Blo 319836 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B1232563 : Blo 319836 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B2051801 : Blo 319836 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B610355 : Blo 319836 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B544907 : Blo 319836 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B610507 : Blo 319836 610507 := bstep (se 1 (by rfl) ⟨457880, by rfl⟩ : syracuseStep 610507 = 915761) B915761
theorem B545035 : Blo 319836 545035 := bstep (se 1 (by rfl) ⟨408776, by rfl⟩ : syracuseStep 545035 = 817553) B817553
theorem B1495385 : Blo 319836 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B545177 : Blo 319836 545177 := bstep (se 2 (by rfl) ⟨204441, by rfl⟩ : syracuseStep 545177 = 408883) B408883
theorem B1626641 : Blo 319836 1626641 := bstep (se 2 (by rfl) ⟨609990, by rfl⟩ : syracuseStep 1626641 = 1219981) B1219981
theorem B6279697 : Blo 319836 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B610841 : Blo 319836 610841 := bstep (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) B458131
theorem B545305 : Blo 319836 545305 := bstep (se 2 (by rfl) ⟨204489, by rfl⟩ : syracuseStep 545305 = 408979) B408979
theorem B4117027 : Blo 319836 4117027 := bstep (se 1 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 4117027 = 6175541) B6175541
theorem B479819 : Blo 319836 479819 := bstep (se 1 (by rfl) ⟨359864, by rfl⟩ : syracuseStep 479819 = 719729) B719729
theorem B479831 : Blo 319836 479831 := bstep (se 1 (by rfl) ⟨359873, by rfl⟩ : syracuseStep 479831 = 719747) B719747
theorem B479897 : Blo 319836 479897 := bstep (se 2 (by rfl) ⟨179961, by rfl⟩ : syracuseStep 479897 = 359923) B359923
theorem B1823411 : Blo 319836 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1626803 : Blo 319836 1626803 := bstep (se 1 (by rfl) ⟨1220102, by rfl⟩ : syracuseStep 1626803 = 2440205) B2440205
theorem B480011 : Blo 319836 480011 := bstep (se 1 (by rfl) ⟨360008, by rfl⟩ : syracuseStep 480011 = 720017) B720017
theorem B480023 : Blo 319836 480023 := bstep (se 1 (by rfl) ⟨360017, by rfl⟩ : syracuseStep 480023 = 720035) B720035
theorem B480089 : Blo 319836 480089 := bstep (se 2 (by rfl) ⟨180033, by rfl⟩ : syracuseStep 480089 = 360067) B360067
theorem B4739957 : Blo 319836 4739957 := bstep (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) B444371
theorem B480203 : Blo 319836 480203 := bstep (se 1 (by rfl) ⟨360152, by rfl⟩ : syracuseStep 480203 = 720305) B720305
theorem B480215 : Blo 319836 480215 := bstep (se 1 (by rfl) ⟨360161, by rfl⟩ : syracuseStep 480215 = 720323) B720323
theorem B512983 : Blo 319836 512983 := bstep (se 1 (by rfl) ⟨384737, by rfl⟩ : syracuseStep 512983 = 769475) B769475
theorem B480281 : Blo 319836 480281 := bstep (se 2 (by rfl) ⟨180105, by rfl⟩ : syracuseStep 480281 = 360211) B360211
theorem B545879 : Blo 319836 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B480395 : Blo 319836 480395 := bstep (se 1 (by rfl) ⟨360296, by rfl⟩ : syracuseStep 480395 = 720593) B720593
theorem B480407 : Blo 319836 480407 := bstep (se 1 (by rfl) ⟨360305, by rfl⟩ : syracuseStep 480407 = 720611) B720611
theorem B611479 : Blo 319836 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B546007 : Blo 319836 546007 := bstep (se 1 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 546007 = 819011) B819011
theorem B480473 : Blo 319836 480473 := bstep (se 2 (by rfl) ⟨180177, by rfl⟩ : syracuseStep 480473 = 360355) B360355
theorem B480587 : Blo 319836 480587 := bstep (se 1 (by rfl) ⟨360440, by rfl⟩ : syracuseStep 480587 = 720881) B720881
theorem B480599 : Blo 319836 480599 := bstep (se 1 (by rfl) ⟨360449, by rfl⟩ : syracuseStep 480599 = 720899) B720899
theorem B480665 : Blo 319836 480665 := bstep (se 2 (by rfl) ⟨180249, by rfl⟩ : syracuseStep 480665 = 360499) B360499
theorem B480779 : Blo 319836 480779 := bstep (se 1 (by rfl) ⟨360584, by rfl⟩ : syracuseStep 480779 = 721169) B721169
theorem B480791 : Blo 319836 480791 := bstep (se 1 (by rfl) ⟨360593, by rfl⟩ : syracuseStep 480791 = 721187) B721187
theorem B480857 : Blo 319836 480857 := bstep (se 2 (by rfl) ⟨180321, by rfl⟩ : syracuseStep 480857 = 360643) B360643
theorem B480971 : Blo 319836 480971 := bstep (se 1 (by rfl) ⟨360728, by rfl⟩ : syracuseStep 480971 = 721457) B721457
theorem B480983 : Blo 319836 480983 := bstep (se 1 (by rfl) ⟨360737, by rfl⟩ : syracuseStep 480983 = 721475) B721475
theorem B513803 : Blo 319836 513803 := bstep (se 1 (by rfl) ⟨385352, by rfl⟩ : syracuseStep 513803 = 770705) B770705
theorem B481049 : Blo 319836 481049 := bstep (se 2 (by rfl) ⟨180393, by rfl⟩ : syracuseStep 481049 = 360787) B360787
theorem B8214371 : Blo 319836 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B481163 : Blo 319836 481163 := bstep (se 1 (by rfl) ⟨360872, by rfl⟩ : syracuseStep 481163 = 721745) B721745
theorem B481175 : Blo 319836 481175 := bstep (se 1 (by rfl) ⟨360881, by rfl⟩ : syracuseStep 481175 = 721763) B721763
theorem B612299 : Blo 319836 612299 := bstep (se 1 (by rfl) ⟨459224, by rfl⟩ : syracuseStep 612299 = 918449) B918449
theorem B481241 : Blo 319836 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B612353 : Blo 319836 612353 := bstep (se 2 (by rfl) ⟨229632, by rfl⟩ : syracuseStep 612353 = 459265) B459265
theorem B481355 : Blo 319836 481355 := bstep (se 1 (by rfl) ⟨361016, by rfl⟩ : syracuseStep 481355 = 722033) B722033
theorem B5036107 : Blo 319836 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B481367 : Blo 319836 481367 := bstep (se 1 (by rfl) ⟨361025, by rfl⟩ : syracuseStep 481367 = 722051) B722051
theorem B1824869 : Blo 319836 1824869 := bstep (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) B342163
theorem B481433 : Blo 319836 481433 := bstep (se 2 (by rfl) ⟨180537, by rfl⟩ : syracuseStep 481433 = 361075) B361075
theorem B481547 : Blo 319836 481547 := bstep (se 1 (by rfl) ⟨361160, by rfl⟩ : syracuseStep 481547 = 722321) B722321
theorem B481559 : Blo 319836 481559 := bstep (se 1 (by rfl) ⟨361169, by rfl⟩ : syracuseStep 481559 = 722339) B722339
theorem B4413761 : Blo 319836 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B481625 : Blo 319836 481625 := bstep (se 2 (by rfl) ⟨180609, by rfl⟩ : syracuseStep 481625 = 361219) B361219
theorem B1366465 : Blo 319836 1366465 := bstep (se 2 (by rfl) ⟨512424, by rfl⟩ : syracuseStep 1366465 = 1024849) B1024849
theorem B481739 : Blo 319836 481739 := bstep (se 1 (by rfl) ⟨361304, by rfl⟩ : syracuseStep 481739 = 722609) B722609
theorem B481751 : Blo 319836 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B481817 : Blo 319836 481817 := bstep (se 2 (by rfl) ⟨180681, by rfl⟩ : syracuseStep 481817 = 361363) B361363
theorem B1825325 : Blo 319836 1825325 := bstep (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) B684497
theorem B1628747 : Blo 319836 1628747 := bstep (se 1 (by rfl) ⟨1221560, by rfl⟩ : syracuseStep 1628747 = 2443121) B2443121
theorem B481931 : Blo 319836 481931 := bstep (se 1 (by rfl) ⟨361448, by rfl⟩ : syracuseStep 481931 = 722897) B722897
theorem B481943 : Blo 319836 481943 := bstep (se 1 (by rfl) ⟨361457, by rfl⟩ : syracuseStep 481943 = 722915) B722915
theorem B1465049 : Blo 319836 1465049 := bstep (se 2 (by rfl) ⟨549393, by rfl⟩ : syracuseStep 1465049 = 1098787) B1098787
theorem B482009 : Blo 319836 482009 := bstep (se 2 (by rfl) ⟨180753, by rfl⟩ : syracuseStep 482009 = 361507) B361507
theorem B514777 : Blo 319836 514777 := bstep (se 2 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 514777 = 386083) B386083
theorem B580313 : Blo 319836 580313 := bstep (se 2 (by rfl) ⟨217617, by rfl⟩ : syracuseStep 580313 = 435235) B435235
theorem B1366807 : Blo 319836 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B482123 : Blo 319836 482123 := bstep (se 1 (by rfl) ⟨361592, by rfl⟩ : syracuseStep 482123 = 723185) B723185
theorem B482135 : Blo 319836 482135 := bstep (se 1 (by rfl) ⟨361601, by rfl⟩ : syracuseStep 482135 = 723203) B723203
theorem B613271 : Blo 319836 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B482201 : Blo 319836 482201 := bstep (se 2 (by rfl) ⟨180825, by rfl⟩ : syracuseStep 482201 = 361651) B361651
theorem B482315 : Blo 319836 482315 := bstep (se 1 (by rfl) ⟨361736, by rfl⟩ : syracuseStep 482315 = 723473) B723473
theorem B482327 : Blo 319836 482327 := bstep (se 1 (by rfl) ⟨361745, by rfl⟩ : syracuseStep 482327 = 723491) B723491
theorem B2055233 : Blo 319836 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B482393 : Blo 319836 482393 := bstep (se 2 (by rfl) ⟨180897, by rfl⟩ : syracuseStep 482393 = 361795) B361795
theorem B482507 : Blo 319836 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B482519 : Blo 319836 482519 := bstep (se 1 (by rfl) ⟨361889, by rfl⟩ : syracuseStep 482519 = 723779) B723779
theorem B1826009 : Blo 319836 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B810263 : Blo 319836 810263 := bstep (se 1 (by rfl) ⟨607697, by rfl⟩ : syracuseStep 810263 = 1215395) B1215395
theorem B482585 : Blo 319836 482585 := bstep (se 2 (by rfl) ⟨180969, by rfl⟩ : syracuseStep 482585 = 361939) B361939
theorem B777547 : Blo 319836 777547 := bstep (se 1 (by rfl) ⟨583160, by rfl⟩ : syracuseStep 777547 = 1166321) B1166321
theorem B482699 : Blo 319836 482699 := bstep (se 1 (by rfl) ⟨362024, by rfl⟩ : syracuseStep 482699 = 724049) B724049
theorem B482711 : Blo 319836 482711 := bstep (se 1 (by rfl) ⟨362033, by rfl⟩ : syracuseStep 482711 = 724067) B724067
theorem B613811 : Blo 319836 613811 := bstep (se 1 (by rfl) ⟨460358, by rfl⟩ : syracuseStep 613811 = 920717) B920717
theorem B482777 : Blo 319836 482777 := bstep (se 2 (by rfl) ⟨181041, by rfl⟩ : syracuseStep 482777 = 362083) B362083
theorem B581107 : Blo 319836 581107 := bstep (se 1 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 581107 = 871661) B871661
theorem B482891 : Blo 319836 482891 := bstep (se 1 (by rfl) ⟨362168, by rfl⟩ : syracuseStep 482891 = 724337) B724337
theorem B482903 : Blo 319836 482903 := bstep (se 1 (by rfl) ⟨362177, by rfl⟩ : syracuseStep 482903 = 724355) B724355
theorem B482969 : Blo 319836 482969 := bstep (se 2 (by rfl) ⟨181113, by rfl⟩ : syracuseStep 482969 = 362227) B362227
theorem B483083 : Blo 319836 483083 := bstep (se 1 (by rfl) ⟨362312, by rfl⟩ : syracuseStep 483083 = 724625) B724625
theorem B483095 : Blo 319836 483095 := bstep (se 1 (by rfl) ⟨362321, by rfl⟩ : syracuseStep 483095 = 724643) B724643
theorem B483161 : Blo 319836 483161 := bstep (se 2 (by rfl) ⟨181185, by rfl⟩ : syracuseStep 483161 = 362371) B362371
theorem B3137381 : Blo 319836 3137381 := bstep (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) B588259
theorem B614297 : Blo 319836 614297 := bstep (se 2 (by rfl) ⟨230361, by rfl⟩ : syracuseStep 614297 = 460723) B460723
theorem B810931 : Blo 319836 810931 := bstep (se 1 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 810931 = 1216397) B1216397
theorem B483275 : Blo 319836 483275 := bstep (se 1 (by rfl) ⟨362456, by rfl⟩ : syracuseStep 483275 = 724913) B724913
theorem B483287 : Blo 319836 483287 := bstep (se 1 (by rfl) ⟨362465, by rfl⟩ : syracuseStep 483287 = 724931) B724931
theorem B2318341 : Blo 319836 2318341 := bstep (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) B434689
theorem B483353 : Blo 319836 483353 := bstep (se 2 (by rfl) ⟨181257, by rfl⟩ : syracuseStep 483353 = 362515) B362515
theorem B581683 : Blo 319836 581683 := bstep (se 1 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 581683 = 872525) B872525
theorem B811073 : Blo 319836 811073 := bstep (se 2 (by rfl) ⟨304152, by rfl⟩ : syracuseStep 811073 = 608305) B608305
theorem B483467 : Blo 319836 483467 := bstep (se 1 (by rfl) ⟨362600, by rfl⟩ : syracuseStep 483467 = 725201) B725201
theorem B483479 : Blo 319836 483479 := bstep (se 1 (by rfl) ⟨362609, by rfl⟩ : syracuseStep 483479 = 725219) B725219
theorem B909515 : Blo 319836 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B483545 : Blo 319836 483545 := bstep (se 2 (by rfl) ⟨181329, by rfl⟩ : syracuseStep 483545 = 362659) B362659
theorem B2318597 : Blo 319836 2318597 := bstep (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) B434737
theorem B93184277 : Blo 319836 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B1630529 : Blo 319836 1630529 := bstep (se 2 (by rfl) ⟨611448, by rfl⟩ : syracuseStep 1630529 = 1222897) B1222897
theorem B483659 : Blo 319836 483659 := bstep (se 1 (by rfl) ⟨362744, by rfl⟩ : syracuseStep 483659 = 725489) B725489
theorem B483671 : Blo 319836 483671 := bstep (se 1 (by rfl) ⟨362753, by rfl⟩ : syracuseStep 483671 = 725507) B725507
theorem B319851 : Blo 319836 319851 := bstep (se 1 (by rfl) ⟨239888, by rfl⟩ : syracuseStep 319851 = 479777) B479777
theorem B319863 : Blo 319836 319863 := bstep (se 1 (by rfl) ⟨239897, by rfl⟩ : syracuseStep 319863 = 479795) B479795
theorem B319883 : Blo 319836 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B319895 : Blo 319836 319895 := bstep (se 1 (by rfl) ⟨239921, by rfl⟩ : syracuseStep 319895 = 479843) B479843
theorem B483737 : Blo 319836 483737 := bstep (se 2 (by rfl) ⟨181401, by rfl⟩ : syracuseStep 483737 = 362803) B362803
theorem B319915 : Blo 319836 319915 := bstep (se 1 (by rfl) ⟨239936, by rfl⟩ : syracuseStep 319915 = 479873) B479873
theorem B319927 : Blo 319836 319927 := bstep (se 1 (by rfl) ⟨239945, by rfl⟩ : syracuseStep 319927 = 479891) B479891
theorem B319947 : Blo 319836 319947 := bstep (se 1 (by rfl) ⟨239960, by rfl⟩ : syracuseStep 319947 = 479921) B479921
theorem B319959 : Blo 319836 319959 := bstep (se 1 (by rfl) ⟨239969, by rfl⟩ : syracuseStep 319959 = 479939) B479939
theorem B319979 : Blo 319836 319979 := bstep (se 1 (by rfl) ⟨239984, by rfl⟩ : syracuseStep 319979 = 479969) B479969
theorem B319991 : Blo 319836 319991 := bstep (se 1 (by rfl) ⟨239993, by rfl⟩ : syracuseStep 319991 = 479987) B479987
theorem B2449925 : Blo 319836 2449925 := bstep (se 4 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 2449925 = 459361) B459361
theorem B320011 : Blo 319836 320011 := bstep (se 1 (by rfl) ⟨240008, by rfl⟩ : syracuseStep 320011 = 480017) B480017
theorem B483851 : Blo 319836 483851 := bstep (se 1 (by rfl) ⟨362888, by rfl⟩ : syracuseStep 483851 = 725777) B725777
theorem B320023 : Blo 319836 320023 := bstep (se 1 (by rfl) ⟨240017, by rfl⟩ : syracuseStep 320023 = 480035) B480035
theorem B483863 : Blo 319836 483863 := bstep (se 1 (by rfl) ⟨362897, by rfl⟩ : syracuseStep 483863 = 725795) B725795
theorem B320043 : Blo 319836 320043 := bstep (se 1 (by rfl) ⟨240032, by rfl⟩ : syracuseStep 320043 = 480065) B480065
theorem B320055 : Blo 319836 320055 := bstep (se 1 (by rfl) ⟨240041, by rfl⟩ : syracuseStep 320055 = 480083) B480083
theorem B320075 : Blo 319836 320075 := bstep (se 1 (by rfl) ⟨240056, by rfl⟩ : syracuseStep 320075 = 480113) B480113
theorem B320087 : Blo 319836 320087 := bstep (se 1 (by rfl) ⟨240065, by rfl⟩ : syracuseStep 320087 = 480131) B480131
theorem B483929 : Blo 319836 483929 := bstep (se 2 (by rfl) ⟨181473, by rfl⟩ : syracuseStep 483929 = 362947) B362947
theorem B320107 : Blo 319836 320107 := bstep (se 1 (by rfl) ⟨240080, by rfl⟩ : syracuseStep 320107 = 480161) B480161
theorem B320119 : Blo 319836 320119 := bstep (se 1 (by rfl) ⟨240089, by rfl⟩ : syracuseStep 320119 = 480179) B480179
theorem B320139 : Blo 319836 320139 := bstep (se 1 (by rfl) ⟨240104, by rfl⟩ : syracuseStep 320139 = 480209) B480209
theorem B320151 : Blo 319836 320151 := bstep (se 1 (by rfl) ⟨240113, by rfl⟩ : syracuseStep 320151 = 480227) B480227
theorem B320171 : Blo 319836 320171 := bstep (se 1 (by rfl) ⟨240128, by rfl⟩ : syracuseStep 320171 = 480257) B480257
theorem B320183 : Blo 319836 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B320203 : Blo 319836 320203 := bstep (se 1 (by rfl) ⟨240152, by rfl⟩ : syracuseStep 320203 = 480305) B480305
theorem B484043 : Blo 319836 484043 := bstep (se 1 (by rfl) ⟨363032, by rfl⟩ : syracuseStep 484043 = 726065) B726065
theorem B320215 : Blo 319836 320215 := bstep (se 1 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 320215 = 480323) B480323
theorem B484055 : Blo 319836 484055 := bstep (se 1 (by rfl) ⟨363041, by rfl⟩ : syracuseStep 484055 = 726083) B726083
theorem B320235 : Blo 319836 320235 := bstep (se 1 (by rfl) ⟨240176, by rfl⟩ : syracuseStep 320235 = 480353) B480353
theorem B320247 : Blo 319836 320247 := bstep (se 1 (by rfl) ⟨240185, by rfl⟩ : syracuseStep 320247 = 480371) B480371
theorem B320267 : Blo 319836 320267 := bstep (se 1 (by rfl) ⟨240200, by rfl⟩ : syracuseStep 320267 = 480401) B480401
theorem B320279 : Blo 319836 320279 := bstep (se 1 (by rfl) ⟨240209, by rfl⟩ : syracuseStep 320279 = 480419) B480419
theorem B484121 : Blo 319836 484121 := bstep (se 2 (by rfl) ⟨181545, by rfl⟩ : syracuseStep 484121 = 363091) B363091
theorem B320299 : Blo 319836 320299 := bstep (se 1 (by rfl) ⟨240224, by rfl⟩ : syracuseStep 320299 = 480449) B480449
theorem B320311 : Blo 319836 320311 := bstep (se 1 (by rfl) ⟨240233, by rfl⟩ : syracuseStep 320311 = 480467) B480467
theorem B320331 : Blo 319836 320331 := bstep (se 1 (by rfl) ⟨240248, by rfl⟩ : syracuseStep 320331 = 480497) B480497
theorem B582475 : Blo 319836 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B320343 : Blo 319836 320343 := bstep (se 1 (by rfl) ⟨240257, by rfl⟩ : syracuseStep 320343 = 480515) B480515
theorem B320363 : Blo 319836 320363 := bstep (se 1 (by rfl) ⟨240272, by rfl⟩ : syracuseStep 320363 = 480545) B480545
theorem B320375 : Blo 319836 320375 := bstep (se 1 (by rfl) ⟨240281, by rfl⟩ : syracuseStep 320375 = 480563) B480563
theorem B320395 : Blo 319836 320395 := bstep (se 1 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 320395 = 480593) B480593
theorem B484235 : Blo 319836 484235 := bstep (se 1 (by rfl) ⟨363176, by rfl⟩ : syracuseStep 484235 = 726353) B726353
theorem B320407 : Blo 319836 320407 := bstep (se 1 (by rfl) ⟨240305, by rfl⟩ : syracuseStep 320407 = 480611) B480611
theorem B385943 : Blo 319836 385943 := bstep (se 1 (by rfl) ⟨289457, by rfl⟩ : syracuseStep 385943 = 578915) B578915
theorem B484247 : Blo 319836 484247 := bstep (se 1 (by rfl) ⟨363185, by rfl⟩ : syracuseStep 484247 = 726371) B726371
theorem B320427 : Blo 319836 320427 := bstep (se 1 (by rfl) ⟨240320, by rfl⟩ : syracuseStep 320427 = 480641) B480641
theorem B8479667 : Blo 319836 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B320439 : Blo 319836 320439 := bstep (se 1 (by rfl) ⟨240329, by rfl⟩ : syracuseStep 320439 = 480659) B480659
theorem B320459 : Blo 319836 320459 := bstep (se 1 (by rfl) ⟨240344, by rfl⟩ : syracuseStep 320459 = 480689) B480689
theorem B320471 : Blo 319836 320471 := bstep (se 1 (by rfl) ⟨240353, by rfl⟩ : syracuseStep 320471 = 480707) B480707
theorem B484313 : Blo 319836 484313 := bstep (se 2 (by rfl) ⟨181617, by rfl⟩ : syracuseStep 484313 = 363235) B363235
theorem B320491 : Blo 319836 320491 := bstep (se 1 (by rfl) ⟨240368, by rfl⟩ : syracuseStep 320491 = 480737) B480737
theorem B320503 : Blo 319836 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B320523 : Blo 319836 320523 := bstep (se 1 (by rfl) ⟨240392, by rfl⟩ : syracuseStep 320523 = 480785) B480785
theorem B386059 : Blo 319836 386059 := bstep (se 1 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 386059 = 579089) B579089
theorem B320535 : Blo 319836 320535 := bstep (se 1 (by rfl) ⟨240401, by rfl⟩ : syracuseStep 320535 = 480803) B480803
theorem B320555 : Blo 319836 320555 := bstep (se 1 (by rfl) ⟨240416, by rfl⟩ : syracuseStep 320555 = 480833) B480833
theorem B582707 : Blo 319836 582707 := bstep (se 1 (by rfl) ⟨437030, by rfl⟩ : syracuseStep 582707 = 874061) B874061
theorem B320567 : Blo 319836 320567 := bstep (se 1 (by rfl) ⟨240425, by rfl⟩ : syracuseStep 320567 = 480851) B480851
theorem B320587 : Blo 319836 320587 := bstep (se 1 (by rfl) ⟨240440, by rfl⟩ : syracuseStep 320587 = 480881) B480881
theorem B484427 : Blo 319836 484427 := bstep (se 1 (by rfl) ⟨363320, by rfl⟩ : syracuseStep 484427 = 726641) B726641
theorem B320599 : Blo 319836 320599 := bstep (se 1 (by rfl) ⟨240449, by rfl⟩ : syracuseStep 320599 = 480899) B480899
theorem B484439 : Blo 319836 484439 := bstep (se 1 (by rfl) ⟨363329, by rfl⟩ : syracuseStep 484439 = 726659) B726659
theorem B320619 : Blo 319836 320619 := bstep (se 1 (by rfl) ⟨240464, by rfl⟩ : syracuseStep 320619 = 480929) B480929
theorem B320631 : Blo 319836 320631 := bstep (se 1 (by rfl) ⟨240473, by rfl⟩ : syracuseStep 320631 = 480947) B480947
theorem B320651 : Blo 319836 320651 := bstep (se 1 (by rfl) ⟨240488, by rfl⟩ : syracuseStep 320651 = 480977) B480977
theorem B320663 : Blo 319836 320663 := bstep (se 1 (by rfl) ⟨240497, by rfl⟩ : syracuseStep 320663 = 480995) B480995
theorem B484505 : Blo 319836 484505 := bstep (se 2 (by rfl) ⟨181689, by rfl⟩ : syracuseStep 484505 = 363379) B363379
theorem B320683 : Blo 319836 320683 := bstep (se 1 (by rfl) ⟨240512, by rfl⟩ : syracuseStep 320683 = 481025) B481025
theorem B320695 : Blo 319836 320695 := bstep (se 1 (by rfl) ⟨240521, by rfl⟩ : syracuseStep 320695 = 481043) B481043
theorem B320715 : Blo 319836 320715 := bstep (se 1 (by rfl) ⟨240536, by rfl⟩ : syracuseStep 320715 = 481073) B481073
theorem B320727 : Blo 319836 320727 := bstep (se 1 (by rfl) ⟨240545, by rfl⟩ : syracuseStep 320727 = 481091) B481091
theorem B320747 : Blo 319836 320747 := bstep (se 1 (by rfl) ⟨240560, by rfl⟩ : syracuseStep 320747 = 481121) B481121
theorem B320759 : Blo 319836 320759 := bstep (se 1 (by rfl) ⟨240569, by rfl⟩ : syracuseStep 320759 = 481139) B481139
theorem B5498117 : Blo 319836 5498117 := bstep (se 4 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 5498117 = 1030897) B1030897
theorem B320779 : Blo 319836 320779 := bstep (se 1 (by rfl) ⟨240584, by rfl⟩ : syracuseStep 320779 = 481169) B481169
theorem B484619 : Blo 319836 484619 := bstep (se 1 (by rfl) ⟨363464, by rfl⟩ : syracuseStep 484619 = 726929) B726929
theorem B320791 : Blo 319836 320791 := bstep (se 1 (by rfl) ⟨240593, by rfl⟩ : syracuseStep 320791 = 481187) B481187
theorem B484631 : Blo 319836 484631 := bstep (se 1 (by rfl) ⟨363473, by rfl⟩ : syracuseStep 484631 = 726947) B726947
theorem B320811 : Blo 319836 320811 := bstep (se 1 (by rfl) ⟨240608, by rfl⟩ : syracuseStep 320811 = 481217) B481217
theorem B812339 : Blo 319836 812339 := bstep (se 1 (by rfl) ⟨609254, by rfl⟩ : syracuseStep 812339 = 1218509) B1218509
theorem B320823 : Blo 319836 320823 := bstep (se 1 (by rfl) ⟨240617, by rfl⟩ : syracuseStep 320823 = 481235) B481235
theorem B320843 : Blo 319836 320843 := bstep (se 1 (by rfl) ⟨240632, by rfl⟩ : syracuseStep 320843 = 481265) B481265
theorem B320855 : Blo 319836 320855 := bstep (se 1 (by rfl) ⟨240641, by rfl⟩ : syracuseStep 320855 = 481283) B481283
theorem B484697 : Blo 319836 484697 := bstep (se 2 (by rfl) ⟨181761, by rfl⟩ : syracuseStep 484697 = 363523) B363523
theorem B320875 : Blo 319836 320875 := bstep (se 1 (by rfl) ⟨240656, by rfl⟩ : syracuseStep 320875 = 481313) B481313
theorem B320887 : Blo 319836 320887 := bstep (se 1 (by rfl) ⟨240665, by rfl⟩ : syracuseStep 320887 = 481331) B481331
theorem B320907 : Blo 319836 320907 := bstep (se 1 (by rfl) ⟨240680, by rfl⟩ : syracuseStep 320907 = 481361) B481361
theorem B320919 : Blo 319836 320919 := bstep (se 1 (by rfl) ⟨240689, by rfl⟩ : syracuseStep 320919 = 481379) B481379
theorem B320939 : Blo 319836 320939 := bstep (se 1 (by rfl) ⟨240704, by rfl⟩ : syracuseStep 320939 = 481409) B481409
theorem B320951 : Blo 319836 320951 := bstep (se 1 (by rfl) ⟨240713, by rfl⟩ : syracuseStep 320951 = 481427) B481427
theorem B615883 : Blo 319836 615883 := bstep (se 1 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 615883 = 923825) B923825
theorem B320971 : Blo 319836 320971 := bstep (se 1 (by rfl) ⟨240728, by rfl⟩ : syracuseStep 320971 = 481457) B481457
theorem B484811 : Blo 319836 484811 := bstep (se 1 (by rfl) ⟨363608, by rfl⟩ : syracuseStep 484811 = 727217) B727217
theorem B320983 : Blo 319836 320983 := bstep (se 1 (by rfl) ⟨240737, by rfl⟩ : syracuseStep 320983 = 481475) B481475
theorem B484823 : Blo 319836 484823 := bstep (se 1 (by rfl) ⟨363617, by rfl⟩ : syracuseStep 484823 = 727235) B727235
theorem B321003 : Blo 319836 321003 := bstep (se 1 (by rfl) ⟨240752, by rfl⟩ : syracuseStep 321003 = 481505) B481505
theorem B321015 : Blo 319836 321015 := bstep (se 1 (by rfl) ⟨240761, by rfl⟩ : syracuseStep 321015 = 481523) B481523
theorem B321035 : Blo 319836 321035 := bstep (se 1 (by rfl) ⟨240776, by rfl⟩ : syracuseStep 321035 = 481553) B481553
theorem B321047 : Blo 319836 321047 := bstep (se 1 (by rfl) ⟨240785, by rfl⟩ : syracuseStep 321047 = 481571) B481571
theorem B484889 : Blo 319836 484889 := bstep (se 2 (by rfl) ⟨181833, by rfl⟩ : syracuseStep 484889 = 363667) B363667
theorem B321067 : Blo 319836 321067 := bstep (se 1 (by rfl) ⟨240800, by rfl⟩ : syracuseStep 321067 = 481601) B481601
theorem B321079 : Blo 319836 321079 := bstep (se 1 (by rfl) ⟨240809, by rfl⟩ : syracuseStep 321079 = 481619) B481619
theorem B321099 : Blo 319836 321099 := bstep (se 1 (by rfl) ⟨240824, by rfl⟩ : syracuseStep 321099 = 481649) B481649
theorem B321111 : Blo 319836 321111 := bstep (se 1 (by rfl) ⟨240833, by rfl⟩ : syracuseStep 321111 = 481667) B481667
theorem B321131 : Blo 319836 321131 := bstep (se 1 (by rfl) ⟨240848, by rfl⟩ : syracuseStep 321131 = 481697) B481697
theorem B321143 : Blo 319836 321143 := bstep (se 1 (by rfl) ⟨240857, by rfl⟩ : syracuseStep 321143 = 481715) B481715
theorem B321163 : Blo 319836 321163 := bstep (se 1 (by rfl) ⟨240872, by rfl⟩ : syracuseStep 321163 = 481745) B481745
theorem B485003 : Blo 319836 485003 := bstep (se 1 (by rfl) ⟨363752, by rfl⟩ : syracuseStep 485003 = 727505) B727505
theorem B321175 : Blo 319836 321175 := bstep (se 1 (by rfl) ⟨240881, by rfl⟩ : syracuseStep 321175 = 481763) B481763
theorem B1861271 : Blo 319836 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B485015 : Blo 319836 485015 := bstep (se 1 (by rfl) ⟨363761, by rfl⟩ : syracuseStep 485015 = 727523) B727523
theorem B321195 : Blo 319836 321195 := bstep (se 1 (by rfl) ⟨240896, by rfl⟩ : syracuseStep 321195 = 481793) B481793
theorem B321207 : Blo 319836 321207 := bstep (se 1 (by rfl) ⟨240905, by rfl⟩ : syracuseStep 321207 = 481811) B481811
theorem B321227 : Blo 319836 321227 := bstep (se 1 (by rfl) ⟨240920, by rfl⟩ : syracuseStep 321227 = 481841) B481841
theorem B321239 : Blo 319836 321239 := bstep (se 1 (by rfl) ⟨240929, by rfl⟩ : syracuseStep 321239 = 481859) B481859
theorem B976601 : Blo 319836 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B485081 : Blo 319836 485081 := bstep (se 2 (by rfl) ⟨181905, by rfl⟩ : syracuseStep 485081 = 363811) B363811
theorem B321259 : Blo 319836 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B321271 : Blo 319836 321271 := bstep (se 1 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 321271 = 481907) B481907
theorem B321291 : Blo 319836 321291 := bstep (se 1 (by rfl) ⟨240968, by rfl⟩ : syracuseStep 321291 = 481937) B481937
theorem B321303 : Blo 319836 321303 := bstep (se 1 (by rfl) ⟨240977, by rfl⟩ : syracuseStep 321303 = 481955) B481955
theorem B321323 : Blo 319836 321323 := bstep (se 1 (by rfl) ⟨240992, by rfl⟩ : syracuseStep 321323 = 481985) B481985
theorem B321335 : Blo 319836 321335 := bstep (se 1 (by rfl) ⟨241001, by rfl⟩ : syracuseStep 321335 = 482003) B482003
theorem B812875 : Blo 319836 812875 := bstep (se 1 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 812875 = 1219313) B1219313
theorem B321355 : Blo 319836 321355 := bstep (se 1 (by rfl) ⟨241016, by rfl⟩ : syracuseStep 321355 = 482033) B482033
theorem B485195 : Blo 319836 485195 := bstep (se 1 (by rfl) ⟨363896, by rfl⟩ : syracuseStep 485195 = 727793) B727793
theorem B321367 : Blo 319836 321367 := bstep (se 1 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 321367 = 482051) B482051
theorem B485207 : Blo 319836 485207 := bstep (se 1 (by rfl) ⟨363905, by rfl⟩ : syracuseStep 485207 = 727811) B727811
theorem B321387 : Blo 319836 321387 := bstep (se 1 (by rfl) ⟨241040, by rfl⟩ : syracuseStep 321387 = 482081) B482081
theorem B321399 : Blo 319836 321399 := bstep (se 1 (by rfl) ⟨241049, by rfl⟩ : syracuseStep 321399 = 482099) B482099
theorem B321419 : Blo 319836 321419 := bstep (se 1 (by rfl) ⟨241064, by rfl⟩ : syracuseStep 321419 = 482129) B482129
theorem B321431 : Blo 319836 321431 := bstep (se 1 (by rfl) ⟨241073, by rfl⟩ : syracuseStep 321431 = 482147) B482147
theorem B1107863 : Blo 319836 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B485273 : Blo 319836 485273 := bstep (se 2 (by rfl) ⟨181977, by rfl⟩ : syracuseStep 485273 = 363955) B363955
theorem B321451 : Blo 319836 321451 := bstep (se 1 (by rfl) ⟨241088, by rfl⟩ : syracuseStep 321451 = 482177) B482177
theorem B321463 : Blo 319836 321463 := bstep (se 1 (by rfl) ⟨241097, by rfl⟩ : syracuseStep 321463 = 482195) B482195
theorem B321483 : Blo 319836 321483 := bstep (se 1 (by rfl) ⟨241112, by rfl⟩ : syracuseStep 321483 = 482225) B482225
theorem B321495 : Blo 319836 321495 := bstep (se 1 (by rfl) ⟨241121, by rfl⟩ : syracuseStep 321495 = 482243) B482243
theorem B813017 : Blo 319836 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B321515 : Blo 319836 321515 := bstep (se 1 (by rfl) ⟨241136, by rfl⟩ : syracuseStep 321515 = 482273) B482273
theorem B321527 : Blo 319836 321527 := bstep (se 1 (by rfl) ⟨241145, by rfl⟩ : syracuseStep 321527 = 482291) B482291
theorem B321547 : Blo 319836 321547 := bstep (se 1 (by rfl) ⟨241160, by rfl⟩ : syracuseStep 321547 = 482321) B482321
theorem B485387 : Blo 319836 485387 := bstep (se 1 (by rfl) ⟨364040, by rfl⟩ : syracuseStep 485387 = 728081) B728081
theorem B321559 : Blo 319836 321559 := bstep (se 1 (by rfl) ⟨241169, by rfl⟩ : syracuseStep 321559 = 482339) B482339
theorem B485399 : Blo 319836 485399 := bstep (se 1 (by rfl) ⟨364049, by rfl⟩ : syracuseStep 485399 = 728099) B728099
theorem B321579 : Blo 319836 321579 := bstep (se 1 (by rfl) ⟨241184, by rfl⟩ : syracuseStep 321579 = 482369) B482369
theorem B321591 : Blo 319836 321591 := bstep (se 1 (by rfl) ⟨241193, by rfl⟩ : syracuseStep 321591 = 482387) B482387
theorem B321611 : Blo 319836 321611 := bstep (se 1 (by rfl) ⟨241208, by rfl⟩ : syracuseStep 321611 = 482417) B482417
theorem B321623 : Blo 319836 321623 := bstep (se 1 (by rfl) ⟨241217, by rfl⟩ : syracuseStep 321623 = 482435) B482435
theorem B485465 : Blo 319836 485465 := bstep (se 2 (by rfl) ⟨182049, by rfl⟩ : syracuseStep 485465 = 364099) B364099
theorem B321643 : Blo 319836 321643 := bstep (se 1 (by rfl) ⟨241232, by rfl⟩ : syracuseStep 321643 = 482465) B482465
theorem B321655 : Blo 319836 321655 := bstep (se 1 (by rfl) ⟨241241, by rfl⟩ : syracuseStep 321655 = 482483) B482483
theorem B321675 : Blo 319836 321675 := bstep (se 1 (by rfl) ⟨241256, by rfl⟩ : syracuseStep 321675 = 482513) B482513
theorem B321687 : Blo 319836 321687 := bstep (se 1 (by rfl) ⟨241265, by rfl⟩ : syracuseStep 321687 = 482531) B482531
theorem B321707 : Blo 319836 321707 := bstep (se 1 (by rfl) ⟨241280, by rfl⟩ : syracuseStep 321707 = 482561) B482561
theorem B321719 : Blo 319836 321719 := bstep (se 1 (by rfl) ⟨241289, by rfl⟩ : syracuseStep 321719 = 482579) B482579
theorem B321739 : Blo 319836 321739 := bstep (se 1 (by rfl) ⟨241304, by rfl⟩ : syracuseStep 321739 = 482609) B482609
theorem B485579 : Blo 319836 485579 := bstep (se 1 (by rfl) ⟨364184, by rfl⟩ : syracuseStep 485579 = 728369) B728369
theorem B321751 : Blo 319836 321751 := bstep (se 1 (by rfl) ⟨241313, by rfl⟩ : syracuseStep 321751 = 482627) B482627
theorem B485591 : Blo 319836 485591 := bstep (se 1 (by rfl) ⟨364193, by rfl⟩ : syracuseStep 485591 = 728387) B728387
theorem B1632473 : Blo 319836 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B321771 : Blo 319836 321771 := bstep (se 1 (by rfl) ⟨241328, by rfl⟩ : syracuseStep 321771 = 482657) B482657
theorem B321783 : Blo 319836 321783 := bstep (se 1 (by rfl) ⟨241337, by rfl⟩ : syracuseStep 321783 = 482675) B482675
theorem B321803 : Blo 319836 321803 := bstep (se 1 (by rfl) ⟨241352, by rfl⟩ : syracuseStep 321803 = 482705) B482705
theorem B321815 : Blo 319836 321815 := bstep (se 1 (by rfl) ⟨241361, by rfl⟩ : syracuseStep 321815 = 482723) B482723
theorem B485657 : Blo 319836 485657 := bstep (se 2 (by rfl) ⟨182121, by rfl⟩ : syracuseStep 485657 = 364243) B364243
theorem B321835 : Blo 319836 321835 := bstep (se 1 (by rfl) ⟨241376, by rfl⟩ : syracuseStep 321835 = 482753) B482753
theorem B321847 : Blo 319836 321847 := bstep (se 1 (by rfl) ⟨241385, by rfl⟩ : syracuseStep 321847 = 482771) B482771
theorem B321867 : Blo 319836 321867 := bstep (se 1 (by rfl) ⟨241400, by rfl⟩ : syracuseStep 321867 = 482801) B482801
theorem B321879 : Blo 319836 321879 := bstep (se 1 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 321879 = 482819) B482819
theorem B321899 : Blo 319836 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B321911 : Blo 319836 321911 := bstep (se 1 (by rfl) ⟨241433, by rfl⟩ : syracuseStep 321911 = 482867) B482867
theorem B321931 : Blo 319836 321931 := bstep (se 1 (by rfl) ⟨241448, by rfl⟩ : syracuseStep 321931 = 482897) B482897
theorem B321943 : Blo 319836 321943 := bstep (se 1 (by rfl) ⟨241457, by rfl⟩ : syracuseStep 321943 = 482915) B482915
theorem B321963 : Blo 319836 321963 := bstep (se 1 (by rfl) ⟨241472, by rfl⟩ : syracuseStep 321963 = 482945) B482945
theorem B321975 : Blo 319836 321975 := bstep (se 1 (by rfl) ⟨241481, by rfl⟩ : syracuseStep 321975 = 482963) B482963
theorem B321995 : Blo 319836 321995 := bstep (se 1 (by rfl) ⟨241496, by rfl⟩ : syracuseStep 321995 = 482993) B482993
theorem B322007 : Blo 319836 322007 := bstep (se 1 (by rfl) ⟨241505, by rfl⟩ : syracuseStep 322007 = 483011) B483011
theorem B322027 : Blo 319836 322027 := bstep (se 1 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 322027 = 483041) B483041
theorem B322039 : Blo 319836 322039 := bstep (se 1 (by rfl) ⟨241529, by rfl⟩ : syracuseStep 322039 = 483059) B483059
theorem B322059 : Blo 319836 322059 := bstep (se 1 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 322059 = 483089) B483089
theorem B322071 : Blo 319836 322071 := bstep (se 1 (by rfl) ⟨241553, by rfl⟩ : syracuseStep 322071 = 483107) B483107
theorem B322091 : Blo 319836 322091 := bstep (se 1 (by rfl) ⟨241568, by rfl⟩ : syracuseStep 322091 = 483137) B483137
theorem B322103 : Blo 319836 322103 := bstep (se 1 (by rfl) ⟨241577, by rfl⟩ : syracuseStep 322103 = 483155) B483155
theorem B322123 : Blo 319836 322123 := bstep (se 1 (by rfl) ⟨241592, by rfl⟩ : syracuseStep 322123 = 483185) B483185
theorem B322135 : Blo 319836 322135 := bstep (se 1 (by rfl) ⟨241601, by rfl⟩ : syracuseStep 322135 = 483203) B483203
theorem B322155 : Blo 319836 322155 := bstep (se 1 (by rfl) ⟨241616, by rfl⟩ : syracuseStep 322155 = 483233) B483233
theorem B322167 : Blo 319836 322167 := bstep (se 1 (by rfl) ⟨241625, by rfl⟩ : syracuseStep 322167 = 483251) B483251
theorem B322187 : Blo 319836 322187 := bstep (se 1 (by rfl) ⟨241640, by rfl⟩ : syracuseStep 322187 = 483281) B483281
theorem B322199 : Blo 319836 322199 := bstep (se 1 (by rfl) ⟨241649, by rfl⟩ : syracuseStep 322199 = 483299) B483299
theorem B322219 : Blo 319836 322219 := bstep (se 1 (by rfl) ⟨241664, by rfl⟩ : syracuseStep 322219 = 483329) B483329
theorem B322231 : Blo 319836 322231 := bstep (se 1 (by rfl) ⟨241673, by rfl⟩ : syracuseStep 322231 = 483347) B483347
theorem B1043147 : Blo 319836 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B322251 : Blo 319836 322251 := bstep (se 1 (by rfl) ⟨241688, by rfl⟩ : syracuseStep 322251 = 483377) B483377
theorem B322263 : Blo 319836 322263 := bstep (se 1 (by rfl) ⟨241697, by rfl⟩ : syracuseStep 322263 = 483395) B483395
theorem B322283 : Blo 319836 322283 := bstep (se 1 (by rfl) ⟨241712, by rfl⟩ : syracuseStep 322283 = 483425) B483425
theorem B322295 : Blo 319836 322295 := bstep (se 1 (by rfl) ⟨241721, by rfl⟩ : syracuseStep 322295 = 483443) B483443
theorem B322315 : Blo 319836 322315 := bstep (se 1 (by rfl) ⟨241736, by rfl⟩ : syracuseStep 322315 = 483473) B483473
theorem B813847 : Blo 319836 813847 := bstep (se 1 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 813847 = 1220771) B1220771
theorem B322327 : Blo 319836 322327 := bstep (se 1 (by rfl) ⟨241745, by rfl⟩ : syracuseStep 322327 = 483491) B483491
theorem B322347 : Blo 319836 322347 := bstep (se 1 (by rfl) ⟨241760, by rfl⟩ : syracuseStep 322347 = 483521) B483521
theorem B322359 : Blo 319836 322359 := bstep (se 1 (by rfl) ⟨241769, by rfl⟩ : syracuseStep 322359 = 483539) B483539
theorem B322379 : Blo 319836 322379 := bstep (se 1 (by rfl) ⟨241784, by rfl⟩ : syracuseStep 322379 = 483569) B483569
theorem B322391 : Blo 319836 322391 := bstep (se 1 (by rfl) ⟨241793, by rfl⟩ : syracuseStep 322391 = 483587) B483587
theorem B322411 : Blo 319836 322411 := bstep (se 1 (by rfl) ⟨241808, by rfl⟩ : syracuseStep 322411 = 483617) B483617
theorem B322423 : Blo 319836 322423 := bstep (se 1 (by rfl) ⟨241817, by rfl⟩ : syracuseStep 322423 = 483635) B483635
theorem B2452355 : Blo 319836 2452355 := bstep (se 1 (by rfl) ⟨1839266, by rfl⟩ : syracuseStep 2452355 = 3678533) B3678533
theorem B322443 : Blo 319836 322443 := bstep (se 1 (by rfl) ⟨241832, by rfl⟩ : syracuseStep 322443 = 483665) B483665
theorem B322455 : Blo 319836 322455 := bstep (se 1 (by rfl) ⟨241841, by rfl⟩ : syracuseStep 322455 = 483683) B483683
theorem B322475 : Blo 319836 322475 := bstep (se 1 (by rfl) ⟨241856, by rfl⟩ : syracuseStep 322475 = 483713) B483713
theorem B322487 : Blo 319836 322487 := bstep (se 1 (by rfl) ⟨241865, by rfl⟩ : syracuseStep 322487 = 483731) B483731
theorem B322507 : Blo 319836 322507 := bstep (se 1 (by rfl) ⟨241880, by rfl⟩ : syracuseStep 322507 = 483761) B483761
theorem B322519 : Blo 319836 322519 := bstep (se 1 (by rfl) ⟨241889, by rfl⟩ : syracuseStep 322519 = 483779) B483779
theorem B322539 : Blo 319836 322539 := bstep (se 1 (by rfl) ⟨241904, by rfl⟩ : syracuseStep 322539 = 483809) B483809
theorem B322551 : Blo 319836 322551 := bstep (se 1 (by rfl) ⟨241913, by rfl⟩ : syracuseStep 322551 = 483827) B483827
theorem B322571 : Blo 319836 322571 := bstep (se 1 (by rfl) ⟨241928, by rfl⟩ : syracuseStep 322571 = 483857) B483857
theorem B322583 : Blo 319836 322583 := bstep (se 1 (by rfl) ⟨241937, by rfl⟩ : syracuseStep 322583 = 483875) B483875
theorem B322603 : Blo 319836 322603 := bstep (se 1 (by rfl) ⟨241952, by rfl⟩ : syracuseStep 322603 = 483905) B483905
theorem B1371181 : Blo 319836 1371181 := bstep (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) B514193
theorem B322615 : Blo 319836 322615 := bstep (se 1 (by rfl) ⟨241961, by rfl⟩ : syracuseStep 322615 = 483923) B483923
theorem B322635 : Blo 319836 322635 := bstep (se 1 (by rfl) ⟨241976, by rfl⟩ : syracuseStep 322635 = 483953) B483953
theorem B322647 : Blo 319836 322647 := bstep (se 1 (by rfl) ⟨241985, by rfl⟩ : syracuseStep 322647 = 483971) B483971
theorem B322667 : Blo 319836 322667 := bstep (se 1 (by rfl) ⟨242000, by rfl⟩ : syracuseStep 322667 = 484001) B484001
theorem B322679 : Blo 319836 322679 := bstep (se 1 (by rfl) ⟨242009, by rfl⟩ : syracuseStep 322679 = 484019) B484019
theorem B322699 : Blo 319836 322699 := bstep (se 1 (by rfl) ⟨242024, by rfl⟩ : syracuseStep 322699 = 484049) B484049
theorem B322711 : Blo 319836 322711 := bstep (se 1 (by rfl) ⟨242033, by rfl⟩ : syracuseStep 322711 = 484067) B484067
theorem B322731 : Blo 319836 322731 := bstep (se 1 (by rfl) ⟨242048, by rfl⟩ : syracuseStep 322731 = 484097) B484097
theorem B322743 : Blo 319836 322743 := bstep (se 1 (by rfl) ⟨242057, by rfl⟩ : syracuseStep 322743 = 484115) B484115
theorem B814283 : Blo 319836 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B322763 : Blo 319836 322763 := bstep (se 1 (by rfl) ⟨242072, by rfl⟩ : syracuseStep 322763 = 484145) B484145
theorem B322775 : Blo 319836 322775 := bstep (se 1 (by rfl) ⟨242081, by rfl⟩ : syracuseStep 322775 = 484163) B484163
theorem B683225 : Blo 319836 683225 := bstep (se 2 (by rfl) ⟨256209, by rfl⟩ : syracuseStep 683225 = 512419) B512419
theorem B322795 : Blo 319836 322795 := bstep (se 1 (by rfl) ⟨242096, by rfl⟩ : syracuseStep 322795 = 484193) B484193
theorem B322807 : Blo 319836 322807 := bstep (se 1 (by rfl) ⟨242105, by rfl⟩ : syracuseStep 322807 = 484211) B484211
theorem B322827 : Blo 319836 322827 := bstep (se 1 (by rfl) ⟨242120, by rfl⟩ : syracuseStep 322827 = 484241) B484241
theorem B322839 : Blo 319836 322839 := bstep (se 1 (by rfl) ⟨242129, by rfl⟩ : syracuseStep 322839 = 484259) B484259
theorem B322859 : Blo 319836 322859 := bstep (se 1 (by rfl) ⟨242144, by rfl⟩ : syracuseStep 322859 = 484289) B484289
theorem B322871 : Blo 319836 322871 := bstep (se 1 (by rfl) ⟨242153, by rfl⟩ : syracuseStep 322871 = 484307) B484307
theorem B322891 : Blo 319836 322891 := bstep (se 1 (by rfl) ⟨242168, by rfl⟩ : syracuseStep 322891 = 484337) B484337
theorem B322903 : Blo 319836 322903 := bstep (se 1 (by rfl) ⟨242177, by rfl⟩ : syracuseStep 322903 = 484355) B484355
theorem B322923 : Blo 319836 322923 := bstep (se 1 (by rfl) ⟨242192, by rfl⟩ : syracuseStep 322923 = 484385) B484385
theorem B322935 : Blo 319836 322935 := bstep (se 1 (by rfl) ⟨242201, by rfl⟩ : syracuseStep 322935 = 484403) B484403
theorem B322955 : Blo 319836 322955 := bstep (se 1 (by rfl) ⟨242216, by rfl⟩ : syracuseStep 322955 = 484433) B484433
theorem B7925141 : Blo 319836 7925141 := bstep (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) B371491
theorem B322967 : Blo 319836 322967 := bstep (se 1 (by rfl) ⟨242225, by rfl⟩ : syracuseStep 322967 = 484451) B484451
theorem B322987 : Blo 319836 322987 := bstep (se 1 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 322987 = 484481) B484481
theorem B322999 : Blo 319836 322999 := bstep (se 1 (by rfl) ⟨242249, by rfl⟩ : syracuseStep 322999 = 484499) B484499
theorem B323019 : Blo 319836 323019 := bstep (se 1 (by rfl) ⟨242264, by rfl⟩ : syracuseStep 323019 = 484529) B484529
theorem B323031 : Blo 319836 323031 := bstep (se 1 (by rfl) ⟨242273, by rfl⟩ : syracuseStep 323031 = 484547) B484547
theorem B388567 : Blo 319836 388567 := bstep (se 1 (by rfl) ⟨291425, by rfl⟩ : syracuseStep 388567 = 582851) B582851
theorem B650713 : Blo 319836 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B323051 : Blo 319836 323051 := bstep (se 1 (by rfl) ⟨242288, by rfl⟩ : syracuseStep 323051 = 484577) B484577
theorem B323063 : Blo 319836 323063 := bstep (se 1 (by rfl) ⟨242297, by rfl⟩ : syracuseStep 323063 = 484595) B484595
theorem B323083 : Blo 319836 323083 := bstep (se 1 (by rfl) ⟨242312, by rfl⟩ : syracuseStep 323083 = 484625) B484625
theorem B323095 : Blo 319836 323095 := bstep (se 1 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 323095 = 484643) B484643
theorem B323115 : Blo 319836 323115 := bstep (se 1 (by rfl) ⟨242336, by rfl⟩ : syracuseStep 323115 = 484673) B484673
theorem B323127 : Blo 319836 323127 := bstep (se 1 (by rfl) ⟨242345, by rfl⟩ : syracuseStep 323127 = 484691) B484691
theorem B814657 : Blo 319836 814657 := bstep (se 2 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 814657 = 610993) B610993
theorem B912971 : Blo 319836 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B323147 : Blo 319836 323147 := bstep (se 1 (by rfl) ⟨242360, by rfl⟩ : syracuseStep 323147 = 484721) B484721
theorem B323159 : Blo 319836 323159 := bstep (se 1 (by rfl) ⟨242369, by rfl⟩ : syracuseStep 323159 = 484739) B484739
theorem B323179 : Blo 319836 323179 := bstep (se 1 (by rfl) ⟨242384, by rfl⟩ : syracuseStep 323179 = 484769) B484769
theorem B683635 : Blo 319836 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B323191 : Blo 319836 323191 := bstep (se 1 (by rfl) ⟨242393, by rfl⟩ : syracuseStep 323191 = 484787) B484787
theorem B323211 : Blo 319836 323211 := bstep (se 1 (by rfl) ⟨242408, by rfl⟩ : syracuseStep 323211 = 484817) B484817
theorem B323223 : Blo 319836 323223 := bstep (se 1 (by rfl) ⟨242417, by rfl⟩ : syracuseStep 323223 = 484835) B484835
theorem B323243 : Blo 319836 323243 := bstep (se 1 (by rfl) ⟨242432, by rfl⟩ : syracuseStep 323243 = 484865) B484865
theorem B323255 : Blo 319836 323255 := bstep (se 1 (by rfl) ⟨242441, by rfl⟩ : syracuseStep 323255 = 484883) B484883
theorem B1175233 : Blo 319836 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B323275 : Blo 319836 323275 := bstep (se 1 (by rfl) ⟨242456, by rfl⟩ : syracuseStep 323275 = 484913) B484913
theorem B323287 : Blo 319836 323287 := bstep (se 1 (by rfl) ⟨242465, by rfl⟩ : syracuseStep 323287 = 484931) B484931
theorem B323307 : Blo 319836 323307 := bstep (se 1 (by rfl) ⟨242480, by rfl⟩ : syracuseStep 323307 = 484961) B484961
theorem B323319 : Blo 319836 323319 := bstep (se 1 (by rfl) ⟨242489, by rfl⟩ : syracuseStep 323319 = 484979) B484979
theorem B323339 : Blo 319836 323339 := bstep (se 1 (by rfl) ⟨242504, by rfl⟩ : syracuseStep 323339 = 485009) B485009
theorem B323351 : Blo 319836 323351 := bstep (se 1 (by rfl) ⟨242513, by rfl⟩ : syracuseStep 323351 = 485027) B485027
theorem B323371 : Blo 319836 323371 := bstep (se 1 (by rfl) ⟨242528, by rfl⟩ : syracuseStep 323371 = 485057) B485057
theorem B1830701 : Blo 319836 1830701 := bstep (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) B686513
theorem B1634093 : Blo 319836 1634093 := bstep (se 3 (by rfl) ⟨306392, by rfl⟩ : syracuseStep 1634093 = 612785) B612785
theorem B323383 : Blo 319836 323383 := bstep (se 1 (by rfl) ⟨242537, by rfl⟩ : syracuseStep 323383 = 485075) B485075
theorem B323403 : Blo 319836 323403 := bstep (se 1 (by rfl) ⟨242552, by rfl⟩ : syracuseStep 323403 = 485105) B485105
theorem B323415 : Blo 319836 323415 := bstep (se 1 (by rfl) ⟨242561, by rfl⟩ : syracuseStep 323415 = 485123) B485123
theorem B323435 : Blo 319836 323435 := bstep (se 1 (by rfl) ⟨242576, by rfl⟩ : syracuseStep 323435 = 485153) B485153
theorem B323447 : Blo 319836 323447 := bstep (se 1 (by rfl) ⟨242585, by rfl⟩ : syracuseStep 323447 = 485171) B485171
theorem B323467 : Blo 319836 323467 := bstep (se 1 (by rfl) ⟨242600, by rfl⟩ : syracuseStep 323467 = 485201) B485201
theorem B323479 : Blo 319836 323479 := bstep (se 1 (by rfl) ⟨242609, by rfl⟩ : syracuseStep 323479 = 485219) B485219
theorem B323499 : Blo 319836 323499 := bstep (se 1 (by rfl) ⟨242624, by rfl⟩ : syracuseStep 323499 = 485249) B485249
theorem B1306547 : Blo 319836 1306547 := bstep (se 1 (by rfl) ⟨979910, by rfl⟩ : syracuseStep 1306547 = 1959821) B1959821
theorem B323511 : Blo 319836 323511 := bstep (se 1 (by rfl) ⟨242633, by rfl⟩ : syracuseStep 323511 = 485267) B485267
theorem B323531 : Blo 319836 323531 := bstep (se 1 (by rfl) ⟨242648, by rfl⟩ : syracuseStep 323531 = 485297) B485297
theorem B323543 : Blo 319836 323543 := bstep (se 1 (by rfl) ⟨242657, by rfl⟩ : syracuseStep 323543 = 485315) B485315
theorem B913369 : Blo 319836 913369 := bstep (se 2 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 913369 = 685027) B685027
theorem B323563 : Blo 319836 323563 := bstep (se 1 (by rfl) ⟨242672, by rfl⟩ : syracuseStep 323563 = 485345) B485345
theorem B323575 : Blo 319836 323575 := bstep (se 1 (by rfl) ⟨242681, by rfl⟩ : syracuseStep 323575 = 485363) B485363
theorem B323595 : Blo 319836 323595 := bstep (se 1 (by rfl) ⟨242696, by rfl⟩ : syracuseStep 323595 = 485393) B485393
theorem B323607 : Blo 319836 323607 := bstep (se 1 (by rfl) ⟨242705, by rfl⟩ : syracuseStep 323607 = 485411) B485411
theorem B323627 : Blo 319836 323627 := bstep (se 1 (by rfl) ⟨242720, by rfl⟩ : syracuseStep 323627 = 485441) B485441
theorem B323639 : Blo 319836 323639 := bstep (se 1 (by rfl) ⟨242729, by rfl⟩ : syracuseStep 323639 = 485459) B485459
theorem B323659 : Blo 319836 323659 := bstep (se 1 (by rfl) ⟨242744, by rfl⟩ : syracuseStep 323659 = 485489) B485489
theorem B323671 : Blo 319836 323671 := bstep (se 1 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 323671 = 485507) B485507
theorem B684121 : Blo 319836 684121 := bstep (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) B513091
theorem B5009501 : Blo 319836 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B979037 : Blo 319836 979037 := bstep (se 3 (by rfl) ⟨183569, by rfl⟩ : syracuseStep 979037 = 367139) B367139
theorem B323691 : Blo 319836 323691 := bstep (se 1 (by rfl) ⟨242768, by rfl⟩ : syracuseStep 323691 = 485537) B485537
theorem B323703 : Blo 319836 323703 := bstep (se 1 (by rfl) ⟨242777, by rfl⟩ : syracuseStep 323703 = 485555) B485555
theorem B323723 : Blo 319836 323723 := bstep (se 1 (by rfl) ⟨242792, by rfl⟩ : syracuseStep 323723 = 485585) B485585
theorem B815255 : Blo 319836 815255 := bstep (se 1 (by rfl) ⟨611441, by rfl⟩ : syracuseStep 815255 = 1222883) B1222883
theorem B323735 : Blo 319836 323735 := bstep (se 1 (by rfl) ⟨242801, by rfl⟩ : syracuseStep 323735 = 485603) B485603
theorem B323755 : Blo 319836 323755 := bstep (se 1 (by rfl) ⟨242816, by rfl⟩ : syracuseStep 323755 = 485633) B485633
theorem B323767 : Blo 319836 323767 := bstep (se 1 (by rfl) ⟨242825, by rfl⟩ : syracuseStep 323767 = 485651) B485651
theorem B323787 : Blo 319836 323787 := bstep (se 1 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 323787 = 485681) B485681
theorem B323799 : Blo 319836 323799 := bstep (se 1 (by rfl) ⟨242849, by rfl⟩ : syracuseStep 323799 = 485699) B485699
theorem B323819 : Blo 319836 323819 := bstep (se 1 (by rfl) ⟨242864, by rfl⟩ : syracuseStep 323819 = 485729) B485729
theorem B323831 : Blo 319836 323831 := bstep (se 1 (by rfl) ⟨242873, by rfl⟩ : syracuseStep 323831 = 485747) B485747
theorem B487961 : Blo 319836 487961 := bstep (se 2 (by rfl) ⟨182985, by rfl⟩ : syracuseStep 487961 = 365971) B365971
theorem B1372889 : Blo 319836 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B17953589 : Blo 319836 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B684865 : Blo 319836 684865 := bstep (se 2 (by rfl) ⟨256824, by rfl⟩ : syracuseStep 684865 = 513649) B513649
theorem B816065 : Blo 319836 816065 := bstep (se 2 (by rfl) ⟨306024, by rfl⟩ : syracuseStep 816065 = 612049) B612049
theorem B1307585 : Blo 319836 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B619607 : Blo 319836 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B914611 : Blo 319836 914611 := bstep (se 1 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 914611 = 1371917) B1371917
theorem B881867 : Blo 319836 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B2323673 : Blo 319836 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B816601 : Blo 319836 816601 := bstep (se 2 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 816601 = 612451) B612451
theorem B488983 : Blo 319836 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B5961397 : Blo 319836 5961397 := bstep (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) B558881
theorem B2193169 : Blo 319836 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B685847 : Blo 319836 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B1275671 : Blo 319836 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B2094913 : Blo 319836 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B2062259 : Blo 319836 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B1374155 : Blo 319836 1374155 := bstep (se 1 (by rfl) ⟨1030616, by rfl⟩ : syracuseStep 1374155 = 2061233) B2061233
theorem B1308817 : Blo 319836 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B2455757 : Blo 319836 2455757 := bstep (se 3 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 2455757 = 920909) B920909
theorem B1079513 : Blo 319836 1079513 := bstep (se 2 (by rfl) ⟨404817, by rfl⟩ : syracuseStep 1079513 = 809635) B809635
theorem B1374515 : Blo 319836 1374515 := bstep (se 1 (by rfl) ⟨1030886, by rfl⟩ : syracuseStep 1374515 = 2061773) B2061773
theorem B686411 : Blo 319836 686411 := bstep (se 1 (by rfl) ⟨514808, by rfl⟩ : syracuseStep 686411 = 1029617) B1029617
theorem B457049 : Blo 319836 457049 := bstep (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) B342787
theorem B817715 : Blo 319836 817715 := bstep (se 1 (by rfl) ⟨613286, by rfl⟩ : syracuseStep 817715 = 1226573) B1226573
theorem B2226781 : Blo 319836 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B4651613 : Blo 319836 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B2456243 : Blo 319836 2456243 := bstep (se 1 (by rfl) ⟨1842182, by rfl⟩ : syracuseStep 2456243 = 3684365) B3684365
theorem B719639 : Blo 319836 719639 := bstep (se 1 (by rfl) ⟨539729, by rfl⟩ : syracuseStep 719639 = 1079459) B1079459
theorem B686873 : Blo 319836 686873 := bstep (se 2 (by rfl) ⟨257577, by rfl⟩ : syracuseStep 686873 = 515155) B515155
theorem B818009 : Blo 319836 818009 := bstep (se 2 (by rfl) ⟨306753, by rfl⟩ : syracuseStep 818009 = 613507) B613507
theorem B1080215 : Blo 319836 1080215 := bstep (se 1 (by rfl) ⟨810161, by rfl⟩ : syracuseStep 1080215 = 1620323) B1620323
theorem B4651955 : Blo 319836 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B719819 : Blo 319836 719819 := bstep (se 1 (by rfl) ⟨539864, by rfl⟩ : syracuseStep 719819 = 1079729) B1079729
theorem B457687 : Blo 319836 457687 := bstep (se 1 (by rfl) ⟨343265, by rfl⟩ : syracuseStep 457687 = 686531) B686531
theorem B1309661 : Blo 319836 1309661 := bstep (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) B491123
theorem B719873 : Blo 319836 719873 := bstep (se 2 (by rfl) ⟨269952, by rfl⟩ : syracuseStep 719873 = 539905) B539905
theorem B490583 : Blo 319836 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B720089 : Blo 319836 720089 := bstep (se 2 (by rfl) ⟨270033, by rfl⟩ : syracuseStep 720089 = 540067) B540067
theorem B720179 : Blo 319836 720179 := bstep (se 1 (by rfl) ⟨540134, by rfl⟩ : syracuseStep 720179 = 1080269) B1080269
theorem B720215 : Blo 319836 720215 := bstep (se 1 (by rfl) ⟨540161, by rfl⟩ : syracuseStep 720215 = 1080323) B1080323
theorem B359851 : Blo 319836 359851 := bstep (se 1 (by rfl) ⟨269888, by rfl⟩ : syracuseStep 359851 = 539777) B539777
theorem B1080755 : Blo 319836 1080755 := bstep (se 1 (by rfl) ⟨810566, by rfl⟩ : syracuseStep 1080755 = 1621133) B1621133
theorem B622027 : Blo 319836 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B720395 : Blo 319836 720395 := bstep (se 1 (by rfl) ⟨540296, by rfl⟩ : syracuseStep 720395 = 1080593) B1080593
theorem B359959 : Blo 319836 359959 := bstep (se 1 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 359959 = 539939) B539939
theorem B720449 : Blo 319836 720449 := bstep (se 2 (by rfl) ⟨270168, by rfl⟩ : syracuseStep 720449 = 540337) B540337
theorem B1637981 : Blo 319836 1637981 := bstep (se 3 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 1637981 = 614243) B614243
theorem B3899011 : Blo 319836 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B1081025 : Blo 319836 1081025 := bstep (se 2 (by rfl) ⟨405384, by rfl⟩ : syracuseStep 1081025 = 810769) B810769
theorem B360139 : Blo 319836 360139 := bstep (se 1 (by rfl) ⟨270104, by rfl⟩ : syracuseStep 360139 = 540209) B540209
theorem B458507 : Blo 319836 458507 := bstep (se 1 (by rfl) ⟨343880, by rfl⟩ : syracuseStep 458507 = 687761) B687761
theorem B720665 : Blo 319836 720665 := bstep (se 2 (by rfl) ⟨270249, by rfl⟩ : syracuseStep 720665 = 540499) B540499
theorem B360247 : Blo 319836 360247 := bstep (se 1 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 360247 = 540371) B540371
theorem B720755 : Blo 319836 720755 := bstep (se 1 (by rfl) ⟨540566, by rfl⟩ : syracuseStep 720755 = 1081133) B1081133
theorem B720791 : Blo 319836 720791 := bstep (se 1 (by rfl) ⟨540593, by rfl⟩ : syracuseStep 720791 = 1081187) B1081187
theorem B688051 : Blo 319836 688051 := bstep (se 1 (by rfl) ⟨516038, by rfl⟩ : syracuseStep 688051 = 1032077) B1032077
theorem B360427 : Blo 319836 360427 := bstep (se 1 (by rfl) ⟨270320, by rfl⟩ : syracuseStep 360427 = 540641) B540641
theorem B360463 : Blo 319836 360463 := bstep (se 1 (by rfl) ⟨270347, by rfl⟩ : syracuseStep 360463 = 540695) B540695
theorem B1146923 : Blo 319836 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B688171 : Blo 319836 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B1835075 : Blo 319836 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B1638467 : Blo 319836 1638467 := bstep (se 1 (by rfl) ⟨1228850, by rfl⟩ : syracuseStep 1638467 = 2457701) B2457701
theorem B819335 : Blo 319836 819335 := bstep (se 1 (by rfl) ⟨614501, by rfl⟩ : syracuseStep 819335 = 1229003) B1229003
theorem B721043 : Blo 319836 721043 := bstep (se 1 (by rfl) ⟨540782, by rfl⟩ : syracuseStep 721043 = 1081565) B1081565
theorem B721097 : Blo 319836 721097 := bstep (se 2 (by rfl) ⟨270411, by rfl⟩ : syracuseStep 721097 = 540823) B540823
theorem B1376513 : Blo 319836 1376513 := bstep (se 2 (by rfl) ⟨516192, by rfl⟩ : syracuseStep 1376513 = 1032385) B1032385
theorem B819467 : Blo 319836 819467 := bstep (se 1 (by rfl) ⟨614600, by rfl⟩ : syracuseStep 819467 = 1229201) B1229201
theorem B688427 : Blo 319836 688427 := bstep (se 1 (by rfl) ⟨516320, by rfl⟩ : syracuseStep 688427 = 1032641) B1032641
theorem B459065 : Blo 319836 459065 := bstep (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) B344299
theorem B1638791 : Blo 319836 1638791 := bstep (se 1 (by rfl) ⟨1229093, by rfl⟩ : syracuseStep 1638791 = 2458187) B2458187
theorem B918017 : Blo 319836 918017 := bstep (se 2 (by rfl) ⟨344256, by rfl⟩ : syracuseStep 918017 = 688513) B688513
theorem B360967 : Blo 319836 360967 := bstep (se 1 (by rfl) ⟨270725, by rfl⟩ : syracuseStep 360967 = 541451) B541451
theorem B1835531 : Blo 319836 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B2425373 : Blo 319836 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B1081943 : Blo 319836 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B361147 : Blo 319836 361147 := bstep (se 1 (by rfl) ⟨270860, by rfl⟩ : syracuseStep 361147 = 541721) B541721
theorem B2622145 : Blo 319836 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B6980357 : Blo 319836 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B721799 : Blo 319836 721799 := bstep (se 1 (by rfl) ⟨541349, by rfl⟩ : syracuseStep 721799 = 1082699) B1082699
theorem B721979 : Blo 319836 721979 := bstep (se 1 (by rfl) ⟨541484, by rfl⟩ : syracuseStep 721979 = 1082969) B1082969
theorem B1082429 : Blo 319836 1082429 := bstep (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) B405911
theorem B361615 : Blo 319836 361615 := bstep (se 1 (by rfl) ⟨271211, by rfl⟩ : syracuseStep 361615 = 542423) B542423
theorem B722105 : Blo 319836 722105 := bstep (se 2 (by rfl) ⟨270789, by rfl⟩ : syracuseStep 722105 = 541579) B541579
theorem B689555 : Blo 319836 689555 := bstep (se 1 (by rfl) ⟨517166, by rfl⟩ : syracuseStep 689555 = 1034333) B1034333
theorem B918985 : Blo 319836 918985 := bstep (se 2 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 918985 = 689239) B689239
theorem B722447 : Blo 319836 722447 := bstep (se 1 (by rfl) ⟨541835, by rfl⟩ : syracuseStep 722447 = 1083671) B1083671
theorem B722465 : Blo 319836 722465 := bstep (se 2 (by rfl) ⟨270924, by rfl⟩ : syracuseStep 722465 = 541849) B541849
theorem B362119 : Blo 319836 362119 := bstep (se 1 (by rfl) ⟨271589, by rfl⟩ : syracuseStep 362119 = 543179) B543179
theorem B5506865 : Blo 319836 5506865 := bstep (se 2 (by rfl) ⟨2065074, by rfl⟩ : syracuseStep 5506865 = 4130149) B4130149
theorem B362299 : Blo 319836 362299 := bstep (se 1 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 362299 = 543449) B543449
theorem B460603 : Blo 319836 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B25692005 : Blo 319836 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B722807 : Blo 319836 722807 := bstep (se 1 (by rfl) ⟨542105, by rfl⟩ : syracuseStep 722807 = 1084211) B1084211
theorem B690067 : Blo 319836 690067 := bstep (se 1 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 690067 = 1035101) B1035101
theorem B1542041 : Blo 319836 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B821177 : Blo 319836 821177 := bstep (se 2 (by rfl) ⟨307941, by rfl⟩ : syracuseStep 821177 = 615883) B615883
theorem B722987 : Blo 319836 722987 := bstep (se 1 (by rfl) ⟨542240, by rfl⟩ : syracuseStep 722987 = 1084481) B1084481
theorem B461047 : Blo 319836 461047 := bstep (se 1 (by rfl) ⟨345785, by rfl⟩ : syracuseStep 461047 = 691571) B691571
theorem B362767 : Blo 319836 362767 := bstep (se 1 (by rfl) ⟨272075, by rfl⟩ : syracuseStep 362767 = 544151) B544151
theorem B723347 : Blo 319836 723347 := bstep (se 1 (by rfl) ⟨542510, by rfl⟩ : syracuseStep 723347 = 1085021) B1085021
theorem B1083833 : Blo 319836 1083833 := bstep (se 2 (by rfl) ⟨406437, by rfl⟩ : syracuseStep 1083833 = 812875) B812875
theorem B723401 : Blo 319836 723401 := bstep (se 2 (by rfl) ⟨271275, by rfl⟩ : syracuseStep 723401 = 542551) B542551
theorem B2066897 : Blo 319836 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B21629405 : Blo 319836 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B363271 : Blo 319836 363271 := bstep (se 1 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 363271 = 544907) B544907
theorem B3083123 : Blo 319836 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B363451 : Blo 319836 363451 := bstep (se 1 (by rfl) ⟨272588, by rfl⟩ : syracuseStep 363451 = 545177) B545177
theorem B1084427 : Blo 319836 1084427 := bstep (se 1 (by rfl) ⟨813320, by rfl⟩ : syracuseStep 1084427 = 1626641) B1626641
theorem B920591 : Blo 319836 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B2362391 : Blo 319836 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B1215607 : Blo 319836 1215607 := bstep (se 1 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 1215607 = 1823411) B1823411
theorem B1084535 : Blo 319836 1084535 := bstep (se 1 (by rfl) ⟨813401, by rfl⟩ : syracuseStep 1084535 = 1626803) B1626803
theorem B724103 : Blo 319836 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B724283 : Blo 319836 724283 := bstep (se 1 (by rfl) ⟨543212, by rfl⟩ : syracuseStep 724283 = 1086425) B1086425
theorem B363919 : Blo 319836 363919 := bstep (se 1 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 363919 = 545879) B545879
theorem B724409 : Blo 319836 724409 := bstep (se 2 (by rfl) ⟨271653, by rfl⟩ : syracuseStep 724409 = 543307) B543307
theorem B1085129 : Blo 319836 1085129 := bstep (se 2 (by rfl) ⟨406923, by rfl⟩ : syracuseStep 1085129 = 813847) B813847
theorem B724751 : Blo 319836 724751 := bstep (se 1 (by rfl) ⟨543563, by rfl⟩ : syracuseStep 724751 = 1087127) B1087127
theorem B724769 : Blo 319836 724769 := bstep (se 2 (by rfl) ⟨271788, by rfl⟩ : syracuseStep 724769 = 543577) B543577
theorem B5476247 : Blo 319836 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B1216579 : Blo 319836 1216579 := bstep (se 1 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 1216579 = 1824869) B1824869
theorem B4198517 : Blo 319836 4198517 := bstep (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) B393611
theorem B725111 : Blo 319836 725111 := bstep (se 1 (by rfl) ⟨543833, by rfl⟩ : syracuseStep 725111 = 1087667) B1087667
theorem B921719 : Blo 319836 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B725291 : Blo 319836 725291 := bstep (se 1 (by rfl) ⟨543968, by rfl⟩ : syracuseStep 725291 = 1087937) B1087937
theorem B1839449 : Blo 319836 1839449 := bstep (se 2 (by rfl) ⟨689793, by rfl⟩ : syracuseStep 1839449 = 1379587) B1379587
theorem B1216883 : Blo 319836 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B1085831 : Blo 319836 1085831 := bstep (se 1 (by rfl) ⟨814373, by rfl⟩ : syracuseStep 1085831 = 1628747) B1628747
theorem B1380817 : Blo 319836 1380817 := bstep (se 2 (by rfl) ⟨517806, by rfl⟩ : syracuseStep 1380817 = 1035613) B1035613
theorem B725651 : Blo 319836 725651 := bstep (se 1 (by rfl) ⟨544238, by rfl⟩ : syracuseStep 725651 = 1088477) B1088477
theorem B725705 : Blo 319836 725705 := bstep (se 2 (by rfl) ⟨272139, by rfl⟩ : syracuseStep 725705 = 544279) B544279
theorem B4690649 : Blo 319836 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B1086209 : Blo 319836 1086209 := bstep (se 2 (by rfl) ⟨407328, by rfl⟩ : syracuseStep 1086209 = 814657) B814657
theorem B1839905 : Blo 319836 1839905 := bstep (se 2 (by rfl) ⟨689964, by rfl⟩ : syracuseStep 1839905 = 1379929) B1379929
theorem B10523429 : Blo 319836 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B1217339 : Blo 319836 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B1643417 : Blo 319836 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B1840157 : Blo 319836 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B1217825 : Blo 319836 1217825 := bstep (se 2 (by rfl) ⟨456684, by rfl⟩ : syracuseStep 1217825 = 913369) B913369
theorem B726407 : Blo 319836 726407 := bstep (se 1 (by rfl) ⟨544805, by rfl⟩ : syracuseStep 726407 = 1089611) B1089611
theorem B1545617 : Blo 319836 1545617 := bstep (se 2 (by rfl) ⟨579606, by rfl⟩ : syracuseStep 1545617 = 1159213) B1159213
theorem B1545731 : Blo 319836 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B1087019 : Blo 319836 1087019 := bstep (se 1 (by rfl) ⟨815264, by rfl⟩ : syracuseStep 1087019 = 1630529) B1630529
theorem B726587 : Blo 319836 726587 := bstep (se 1 (by rfl) ⟨544940, by rfl⟩ : syracuseStep 726587 = 1089881) B1089881
theorem B3479107 : Blo 319836 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B726713 : Blo 319836 726713 := bstep (se 2 (by rfl) ⟨272517, by rfl⟩ : syracuseStep 726713 = 545035) B545035
theorem B727055 : Blo 319836 727055 := bstep (se 1 (by rfl) ⟨545291, by rfl⟩ : syracuseStep 727055 = 1090583) B1090583
theorem B727073 : Blo 319836 727073 := bstep (se 2 (by rfl) ⟨272652, by rfl⟩ : syracuseStep 727073 = 545305) B545305
theorem B1218797 : Blo 319836 1218797 := bstep (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) B457049
theorem B2332961 : Blo 319836 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B727415 : Blo 319836 727415 := bstep (se 1 (by rfl) ⟨545561, by rfl⟩ : syracuseStep 727415 = 1091123) B1091123
theorem B727595 : Blo 319836 727595 := bstep (se 1 (by rfl) ⟨545696, by rfl⟩ : syracuseStep 727595 = 1091393) B1091393
theorem B1088315 : Blo 319836 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B727955 : Blo 319836 727955 := bstep (se 1 (by rfl) ⟨545966, by rfl⟩ : syracuseStep 727955 = 1091933) B1091933
theorem B1219481 : Blo 319836 1219481 := bstep (se 2 (by rfl) ⟨457305, by rfl⟩ : syracuseStep 1219481 = 914611) B914611
theorem B728009 : Blo 319836 728009 := bstep (se 2 (by rfl) ⟨273003, by rfl⟩ : syracuseStep 728009 = 546007) B546007
theorem B695431 : Blo 319836 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B1088801 : Blo 319836 1088801 := bstep (se 2 (by rfl) ⟨408300, by rfl⟩ : syracuseStep 1088801 = 816601) B816601
theorem B1842547 : Blo 319836 1842547 := bstep (se 1 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 1842547 = 2763821) B2763821
theorem B5283427 : Blo 319836 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B2924225 : Blo 319836 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B2793217 : Blo 319836 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1220467 : Blo 319836 1220467 := bstep (se 1 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 1220467 = 1830701) B1830701
theorem B1089395 : Blo 319836 1089395 := bstep (se 1 (by rfl) ⟨817046, by rfl⟩ : syracuseStep 1089395 = 1634093) B1634093
theorem B5480621 : Blo 319836 5480621 := bstep (se 3 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 5480621 = 2055233) B2055233
theorem B729479 : Blo 319836 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B11969059 : Blo 319836 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B1844005 : Blo 319836 1844005 := bstep (se 4 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 1844005 = 345751) B345751
theorem B5251877 : Blo 319836 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B1549115 : Blo 319836 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B2205073 : Blo 319836 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B829369 : Blo 319836 829369 := bstep (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) B622027
theorem B1222685 : Blo 319836 1222685 := bstep (se 3 (by rfl) ⟨229253, by rfl⟩ : syracuseStep 1222685 = 458507) B458507
theorem B1976363 : Blo 319836 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B5515613 : Blo 319836 5515613 := bstep (se 3 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 5515613 = 2068355) B2068355
theorem B731539 : Blo 319836 731539 := bstep (se 1 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 731539 = 1097309) B1097309
theorem B1091987 : Blo 319836 1091987 := bstep (se 1 (by rfl) ⟨818990, by rfl⟩ : syracuseStep 1091987 = 1637981) B1637981
theorem B3091121 : Blo 319836 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B1223369 : Blo 319836 1223369 := bstep (se 2 (by rfl) ⟨458763, by rfl⟩ : syracuseStep 1223369 = 917527) B917527
theorem B1551251 : Blo 319836 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1551403 : Blo 319836 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B699691 : Blo 319836 699691 := bstep (se 1 (by rfl) ⟨524768, by rfl⟩ : syracuseStep 699691 = 1049537) B1049537
theorem B248491405 : Blo 319836 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B405263 : Blo 319836 405263 := bstep (se 1 (by rfl) ⟨303947, by rfl⟩ : syracuseStep 405263 = 607895) B607895
theorem B700193 : Blo 319836 700193 := bstep (se 2 (by rfl) ⟨262572, by rfl⟩ : syracuseStep 700193 = 525145) B525145
theorem B1552729 : Blo 319836 1552729 := bstep (se 2 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 1552729 = 1164547) B1164547
theorem B1225145 : Blo 319836 1225145 := bstep (se 2 (by rfl) ⟨459429, by rfl⟩ : syracuseStep 1225145 = 918859) B918859
theorem B438841 : Blo 319836 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B2241433 : Blo 319836 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B472123 : Blo 319836 472123 := bstep (se 1 (by rfl) ⟨354092, by rfl⟩ : syracuseStep 472123 = 708185) B708185
theorem B1029181 : Blo 319836 1029181 := bstep (se 3 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 1029181 = 385943) B385943
theorem B865399 : Blo 319836 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B996923 : Blo 319836 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B1652285 : Blo 319836 1652285 := bstep (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) B619607
theorem B1947365 : Blo 319836 1947365 := bstep (se 4 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 1947365 = 365131) B365131
theorem B3159971 : Blo 319836 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B12564497 : Blo 319836 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B1620161 : Blo 319836 1620161 := bstep (se 2 (by rfl) ⟨607560, by rfl⟩ : syracuseStep 1620161 = 1215121) B1215121
theorem B2308333 : Blo 319836 2308333 := bstep (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) B865625
theorem B408235 : Blo 319836 408235 := bstep (se 1 (by rfl) ⟨306176, by rfl⟩ : syracuseStep 408235 = 612353) B612353
theorem B3652289 : Blo 319836 3652289 := bstep (se 2 (by rfl) ⟨1369608, by rfl⟩ : syracuseStep 3652289 = 2739217) B2739217
theorem B768811 : Blo 319836 768811 := bstep (se 1 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 768811 = 1153217) B1153217
theorem B6929495 : Blo 319836 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B2604269 : Blo 319836 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B867617 : Blo 319836 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B1621457 : Blo 319836 1621457 := bstep (se 2 (by rfl) ⟨608046, by rfl⟩ : syracuseStep 1621457 = 1216093) B1216093
theorem B540175 : Blo 319836 540175 := bstep (se 1 (by rfl) ⟨405131, by rfl⟩ : syracuseStep 540175 = 810263) B810263
theorem B409207 : Blo 319836 409207 := bstep (se 1 (by rfl) ⟨306905, by rfl⟩ : syracuseStep 409207 = 613811) B613811
theorem B1228729 : Blo 319836 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B409531 : Blo 319836 409531 := bstep (se 1 (by rfl) ⟨307148, by rfl⟩ : syracuseStep 409531 = 614297) B614297
theorem B540715 : Blo 319836 540715 := bstep (se 1 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 540715 = 811073) B811073
theorem B540857 : Blo 319836 540857 := bstep (se 2 (by rfl) ⟨202821, by rfl⟩ : syracuseStep 540857 = 405643) B405643
theorem B5653111 : Blo 319836 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B836249 : Blo 319836 836249 := bstep (se 2 (by rfl) ⟨313593, by rfl⟩ : syracuseStep 836249 = 627187) B627187
theorem B3719857 : Blo 319836 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B8372929 : Blo 319836 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B5489369 : Blo 319836 5489369 := bstep (se 2 (by rfl) ⟨2058513, by rfl⟩ : syracuseStep 5489369 = 4117027) B4117027
theorem B541559 : Blo 319836 541559 := bstep (se 1 (by rfl) ⟨406169, by rfl⟩ : syracuseStep 541559 = 812339) B812339
theorem B770963 : Blo 319836 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B738575 : Blo 319836 738575 := bstep (se 1 (by rfl) ⟨553931, by rfl⟩ : syracuseStep 738575 = 1107863) B1107863
theorem B542011 : Blo 319836 542011 := bstep (se 1 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 542011 = 813017) B813017
theorem B542153 : Blo 319836 542153 := bstep (se 2 (by rfl) ⟨203307, by rfl⟩ : syracuseStep 542153 = 406615) B406615
theorem B1623563 : Blo 319836 1623563 := bstep (se 1 (by rfl) ⟨1217672, by rfl⟩ : syracuseStep 1623563 = 2435345) B2435345
theorem B1623725 : Blo 319836 1623725 := bstep (se 3 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 1623725 = 608897) B608897
theorem B2050109 : Blo 319836 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B542855 : Blo 319836 542855 := bstep (se 1 (by rfl) ⟨407141, by rfl⟩ : syracuseStep 542855 = 814283) B814283
theorem B7948529 : Blo 319836 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B15616273 : Blo 319836 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B608647 : Blo 319836 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B3295673 : Blo 319836 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B1100375 : Blo 319836 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B871031 : Blo 319836 871031 := bstep (se 1 (by rfl) ⟨653273, by rfl⟩ : syracuseStep 871031 = 1306547) B1306547
theorem B543503 : Blo 319836 543503 := bstep (se 1 (by rfl) ⟨407627, by rfl⟩ : syracuseStep 543503 = 815255) B815255
theorem B1821953 : Blo 319836 1821953 := bstep (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) B1366465
theorem B1625345 : Blo 319836 1625345 := bstep (se 2 (by rfl) ⟨609504, by rfl⟩ : syracuseStep 1625345 = 1219009) B1219009
theorem B544043 : Blo 319836 544043 := bstep (se 1 (by rfl) ⟨408032, by rfl⟩ : syracuseStep 544043 = 816065) B816065
theorem B871723 : Blo 319836 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B2969041 : Blo 319836 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B773675 : Blo 319836 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B544441 : Blo 319836 544441 := bstep (se 2 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 544441 = 408331) B408331
theorem B1822409 : Blo 319836 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B610249 : Blo 319836 610249 := bstep (se 2 (by rfl) ⟨228843, by rfl⟩ : syracuseStep 610249 = 457687) B457687
theorem B1626155 : Blo 319836 1626155 := bstep (se 1 (by rfl) ⟨1219616, by rfl⟩ : syracuseStep 1626155 = 2439233) B2439233
theorem B1036331 : Blo 319836 1036331 := bstep (se 1 (by rfl) ⟨777248, by rfl⟩ : syracuseStep 1036331 = 1554497) B1554497
theorem B545143 : Blo 319836 545143 := bstep (se 1 (by rfl) ⟨408857, by rfl⟩ : syracuseStep 545143 = 817715) B817715
theorem B3101075 : Blo 319836 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B1036729 : Blo 319836 1036729 := bstep (se 2 (by rfl) ⟨388773, by rfl⟩ : syracuseStep 1036729 = 777547) B777547
theorem B479759 : Blo 319836 479759 := bstep (se 1 (by rfl) ⟨359819, by rfl⟩ : syracuseStep 479759 = 719639) B719639
theorem B479801 : Blo 319836 479801 := bstep (se 2 (by rfl) ⟨179925, by rfl⟩ : syracuseStep 479801 = 359851) B359851
theorem B545339 : Blo 319836 545339 := bstep (se 1 (by rfl) ⟨409004, by rfl⟩ : syracuseStep 545339 = 818009) B818009
theorem B3101303 : Blo 319836 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B479879 : Blo 319836 479879 := bstep (se 1 (by rfl) ⟨359909, by rfl⟩ : syracuseStep 479879 = 719819) B719819
theorem B873107 : Blo 319836 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B774809 : Blo 319836 774809 := bstep (se 2 (by rfl) ⟨290553, by rfl⟩ : syracuseStep 774809 = 581107) B581107
theorem B479915 : Blo 319836 479915 := bstep (se 1 (by rfl) ⟨359936, by rfl⟩ : syracuseStep 479915 = 719873) B719873
theorem B7000769 : Blo 319836 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B479945 : Blo 319836 479945 := bstep (se 2 (by rfl) ⟨179979, by rfl⟩ : syracuseStep 479945 = 359959) B359959
theorem B480059 : Blo 319836 480059 := bstep (se 1 (by rfl) ⟨360044, by rfl⟩ : syracuseStep 480059 = 720089) B720089
theorem B5198681 : Blo 319836 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B480119 : Blo 319836 480119 := bstep (se 1 (by rfl) ⟨360089, by rfl⟩ : syracuseStep 480119 = 720179) B720179
theorem B480143 : Blo 319836 480143 := bstep (se 1 (by rfl) ⟨360107, by rfl⟩ : syracuseStep 480143 = 720215) B720215
theorem B480185 : Blo 319836 480185 := bstep (se 2 (by rfl) ⟨180069, by rfl⟩ : syracuseStep 480185 = 360139) B360139
theorem B545737 : Blo 319836 545737 := bstep (se 2 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 545737 = 409303) B409303
theorem B480263 : Blo 319836 480263 := bstep (se 1 (by rfl) ⟨360197, by rfl⟩ : syracuseStep 480263 = 720395) B720395
theorem B480299 : Blo 319836 480299 := bstep (se 1 (by rfl) ⟨360224, by rfl⟩ : syracuseStep 480299 = 720449) B720449
theorem B480329 : Blo 319836 480329 := bstep (se 2 (by rfl) ⟨180123, by rfl⟩ : syracuseStep 480329 = 360247) B360247
theorem B480443 : Blo 319836 480443 := bstep (se 1 (by rfl) ⟨360332, by rfl⟩ : syracuseStep 480443 = 720665) B720665
theorem B480503 : Blo 319836 480503 := bstep (se 1 (by rfl) ⟨360377, by rfl⟩ : syracuseStep 480503 = 720755) B720755
theorem B480527 : Blo 319836 480527 := bstep (se 1 (by rfl) ⟨360395, by rfl⟩ : syracuseStep 480527 = 720791) B720791
theorem B480569 : Blo 319836 480569 := bstep (se 2 (by rfl) ⟨180213, by rfl⟩ : syracuseStep 480569 = 360427) B360427
theorem B1627451 : Blo 319836 1627451 := bstep (se 1 (by rfl) ⟨1220588, by rfl⟩ : syracuseStep 1627451 = 2441177) B2441177
theorem B480647 : Blo 319836 480647 := bstep (se 1 (by rfl) ⟨360485, by rfl⟩ : syracuseStep 480647 = 720971) B720971
theorem B775577 : Blo 319836 775577 := bstep (se 2 (by rfl) ⟨290841, by rfl⟩ : syracuseStep 775577 = 581683) B581683
theorem B1398169 : Blo 319836 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B480683 : Blo 319836 480683 := bstep (se 1 (by rfl) ⟨360512, by rfl⟩ : syracuseStep 480683 = 721025) B721025
theorem B480713 : Blo 319836 480713 := bstep (se 2 (by rfl) ⟨180267, by rfl⟩ : syracuseStep 480713 = 360535) B360535
theorem B873929 : Blo 319836 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B1627613 : Blo 319836 1627613 := bstep (se 3 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 1627613 = 610355) B610355
theorem B2610731 : Blo 319836 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B480827 : Blo 319836 480827 := bstep (se 1 (by rfl) ⟨360620, by rfl⟩ : syracuseStep 480827 = 721241) B721241
theorem B480887 : Blo 319836 480887 := bstep (se 1 (by rfl) ⟨360665, by rfl⟩ : syracuseStep 480887 = 721331) B721331
theorem B546439 : Blo 319836 546439 := bstep (se 1 (by rfl) ⟨409829, by rfl⟩ : syracuseStep 546439 = 819659) B819659
theorem B480911 : Blo 319836 480911 := bstep (se 1 (by rfl) ⟨360683, by rfl⟩ : syracuseStep 480911 = 721367) B721367
theorem B480953 : Blo 319836 480953 := bstep (se 2 (by rfl) ⟨180357, by rfl⟩ : syracuseStep 480953 = 360715) B360715
theorem B481031 : Blo 319836 481031 := bstep (se 1 (by rfl) ⟨360773, by rfl⟩ : syracuseStep 481031 = 721547) B721547
theorem B1627937 : Blo 319836 1627937 := bstep (se 2 (by rfl) ⟨610476, by rfl⟩ : syracuseStep 1627937 = 1220953) B1220953
theorem B481067 : Blo 319836 481067 := bstep (se 1 (by rfl) ⟨360800, by rfl⟩ : syracuseStep 481067 = 721601) B721601
theorem B481097 : Blo 319836 481097 := bstep (se 2 (by rfl) ⟨180411, by rfl⟩ : syracuseStep 481097 = 360823) B360823
theorem B513911 : Blo 319836 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B481211 : Blo 319836 481211 := bstep (se 1 (by rfl) ⟨360908, by rfl⟩ : syracuseStep 481211 = 721817) B721817
theorem B481271 : Blo 319836 481271 := bstep (se 1 (by rfl) ⟨360953, by rfl⟩ : syracuseStep 481271 = 721907) B721907
theorem B481295 : Blo 319836 481295 := bstep (se 1 (by rfl) ⟨360971, by rfl⟩ : syracuseStep 481295 = 721943) B721943
theorem B481337 : Blo 319836 481337 := bstep (se 2 (by rfl) ⟨180501, by rfl⟩ : syracuseStep 481337 = 361003) B361003
theorem B481415 : Blo 319836 481415 := bstep (se 1 (by rfl) ⟨361061, by rfl⟩ : syracuseStep 481415 = 722123) B722123
theorem B481451 : Blo 319836 481451 := bstep (se 1 (by rfl) ⟨361088, by rfl⟩ : syracuseStep 481451 = 722177) B722177
theorem B481481 : Blo 319836 481481 := bstep (se 2 (by rfl) ⟨180555, by rfl⟩ : syracuseStep 481481 = 361111) B361111
theorem B874795 : Blo 319836 874795 := bstep (se 1 (by rfl) ⟨656096, by rfl⟩ : syracuseStep 874795 = 1312193) B1312193
theorem B481595 : Blo 319836 481595 := bstep (se 1 (by rfl) ⟨361196, by rfl⟩ : syracuseStep 481595 = 722393) B722393
theorem B481655 : Blo 319836 481655 := bstep (se 1 (by rfl) ⟨361241, by rfl⟩ : syracuseStep 481655 = 722483) B722483
theorem B481679 : Blo 319836 481679 := bstep (se 1 (by rfl) ⟨361259, by rfl⟩ : syracuseStep 481679 = 722519) B722519
theorem B612755 : Blo 319836 612755 := bstep (se 1 (by rfl) ⟨459566, by rfl⟩ : syracuseStep 612755 = 919133) B919133
theorem B481721 : Blo 319836 481721 := bstep (se 2 (by rfl) ⟨180645, by rfl⟩ : syracuseStep 481721 = 361291) B361291
theorem B776633 : Blo 319836 776633 := bstep (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) B582475
theorem B481799 : Blo 319836 481799 := bstep (se 1 (by rfl) ⟨361349, by rfl⟩ : syracuseStep 481799 = 722699) B722699
theorem B481835 : Blo 319836 481835 := bstep (se 1 (by rfl) ⟨361376, by rfl⟩ : syracuseStep 481835 = 722753) B722753
theorem B514603 : Blo 319836 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B481865 : Blo 319836 481865 := bstep (se 2 (by rfl) ⟨180699, by rfl⟩ : syracuseStep 481865 = 361399) B361399
theorem B612983 : Blo 319836 612983 := bstep (se 1 (by rfl) ⟨459737, by rfl⟩ : syracuseStep 612983 = 919475) B919475
theorem B514745 : Blo 319836 514745 := bstep (se 2 (by rfl) ⟨193029, by rfl⟩ : syracuseStep 514745 = 386059) B386059
theorem B481979 : Blo 319836 481979 := bstep (se 1 (by rfl) ⟨361484, by rfl⟩ : syracuseStep 481979 = 722969) B722969
theorem B1628909 : Blo 319836 1628909 := bstep (se 3 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 1628909 = 610841) B610841
theorem B482039 : Blo 319836 482039 := bstep (se 1 (by rfl) ⟨361529, by rfl⟩ : syracuseStep 482039 = 723059) B723059
theorem B482063 : Blo 319836 482063 := bstep (se 1 (by rfl) ⟨361547, by rfl⟩ : syracuseStep 482063 = 723095) B723095
theorem B482105 : Blo 319836 482105 := bstep (se 2 (by rfl) ⟨180789, by rfl⟩ : syracuseStep 482105 = 361579) B361579
theorem B482183 : Blo 319836 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B482219 : Blo 319836 482219 := bstep (se 1 (by rfl) ⟨361664, by rfl⟩ : syracuseStep 482219 = 723329) B723329
theorem B482249 : Blo 319836 482249 := bstep (se 2 (by rfl) ⟨180843, by rfl⟩ : syracuseStep 482249 = 361687) B361687
theorem B482363 : Blo 319836 482363 := bstep (se 1 (by rfl) ⟨361772, by rfl⟩ : syracuseStep 482363 = 723545) B723545
theorem B810071 : Blo 319836 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B482423 : Blo 319836 482423 := bstep (se 1 (by rfl) ⟨361817, by rfl⟩ : syracuseStep 482423 = 723635) B723635
theorem B482447 : Blo 319836 482447 := bstep (se 1 (by rfl) ⟨361835, by rfl⟩ : syracuseStep 482447 = 723671) B723671
theorem B482489 : Blo 319836 482489 := bstep (se 2 (by rfl) ⟨180933, by rfl⟩ : syracuseStep 482489 = 361867) B361867
theorem B3661037 : Blo 319836 3661037 := bstep (se 3 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 3661037 = 1372889) B1372889
theorem B482567 : Blo 319836 482567 := bstep (se 1 (by rfl) ⟨361925, by rfl⟩ : syracuseStep 482567 = 723851) B723851
theorem B1465615 : Blo 319836 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B810283 : Blo 319836 810283 := bstep (se 1 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 810283 = 1215425) B1215425
theorem B482603 : Blo 319836 482603 := bstep (se 1 (by rfl) ⟨361952, by rfl⟩ : syracuseStep 482603 = 723905) B723905
theorem B482633 : Blo 319836 482633 := bstep (se 2 (by rfl) ⟨180987, by rfl⟩ : syracuseStep 482633 = 361975) B361975
theorem B810425 : Blo 319836 810425 := bstep (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) B607819
theorem B482747 : Blo 319836 482747 := bstep (se 1 (by rfl) ⟨362060, by rfl⟩ : syracuseStep 482747 = 724121) B724121
theorem B482807 : Blo 319836 482807 := bstep (se 1 (by rfl) ⟨362105, by rfl⟩ : syracuseStep 482807 = 724211) B724211
theorem B482831 : Blo 319836 482831 := bstep (se 1 (by rfl) ⟨362123, by rfl⟩ : syracuseStep 482831 = 724247) B724247
theorem B1826327 : Blo 319836 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B1629719 : Blo 319836 1629719 := bstep (se 1 (by rfl) ⟨1222289, by rfl⟩ : syracuseStep 1629719 = 2444579) B2444579
theorem B482873 : Blo 319836 482873 := bstep (se 2 (by rfl) ⟨181077, by rfl⟩ : syracuseStep 482873 = 362155) B362155
theorem B482951 : Blo 319836 482951 := bstep (se 1 (by rfl) ⟨362213, by rfl⟩ : syracuseStep 482951 = 724427) B724427
theorem B482987 : Blo 319836 482987 := bstep (se 1 (by rfl) ⟨362240, by rfl⟩ : syracuseStep 482987 = 724481) B724481
theorem B483017 : Blo 319836 483017 := bstep (se 2 (by rfl) ⟨181131, by rfl⟩ : syracuseStep 483017 = 362263) B362263
theorem B1367867 : Blo 319836 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B483131 : Blo 319836 483131 := bstep (se 1 (by rfl) ⟨362348, by rfl⟩ : syracuseStep 483131 = 724697) B724697
theorem B483191 : Blo 319836 483191 := bstep (se 1 (by rfl) ⟨362393, by rfl⟩ : syracuseStep 483191 = 724787) B724787
theorem B483215 : Blo 319836 483215 := bstep (se 1 (by rfl) ⟨362411, by rfl⟩ : syracuseStep 483215 = 724823) B724823
theorem B483257 : Blo 319836 483257 := bstep (se 2 (by rfl) ⟨181221, by rfl⟩ : syracuseStep 483257 = 362443) B362443
theorem B483335 : Blo 319836 483335 := bstep (se 1 (by rfl) ⟨362501, by rfl⟩ : syracuseStep 483335 = 725003) B725003
theorem B483371 : Blo 319836 483371 := bstep (se 1 (by rfl) ⟨362528, by rfl⟩ : syracuseStep 483371 = 725057) B725057
theorem B483401 : Blo 319836 483401 := bstep (se 2 (by rfl) ⟨181275, by rfl⟩ : syracuseStep 483401 = 362551) B362551
theorem B483515 : Blo 319836 483515 := bstep (se 1 (by rfl) ⟨362636, by rfl⟩ : syracuseStep 483515 = 725273) B725273
theorem B483575 : Blo 319836 483575 := bstep (se 1 (by rfl) ⟨362681, by rfl⟩ : syracuseStep 483575 = 725363) B725363
theorem B483599 : Blo 319836 483599 := bstep (se 1 (by rfl) ⟨362699, by rfl⟩ : syracuseStep 483599 = 725399) B725399
theorem B614699 : Blo 319836 614699 := bstep (se 1 (by rfl) ⟨461024, by rfl⟩ : syracuseStep 614699 = 922049) B922049
theorem B483641 : Blo 319836 483641 := bstep (se 2 (by rfl) ⟨181365, by rfl⟩ : syracuseStep 483641 = 362731) B362731
theorem B319879 : Blo 319836 319879 := bstep (se 1 (by rfl) ⟨239909, by rfl⟩ : syracuseStep 319879 = 479819) B479819
theorem B483719 : Blo 319836 483719 := bstep (se 1 (by rfl) ⟨362789, by rfl⟩ : syracuseStep 483719 = 725579) B725579
theorem B319887 : Blo 319836 319887 := bstep (se 1 (by rfl) ⟨239915, by rfl⟩ : syracuseStep 319887 = 479831) B479831
theorem B811417 : Blo 319836 811417 := bstep (se 2 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 811417 = 608563) B608563
theorem B483755 : Blo 319836 483755 := bstep (se 1 (by rfl) ⟨362816, by rfl⟩ : syracuseStep 483755 = 725633) B725633
theorem B319931 : Blo 319836 319931 := bstep (se 1 (by rfl) ⟨239948, by rfl⟩ : syracuseStep 319931 = 479897) B479897
theorem B483785 : Blo 319836 483785 := bstep (se 2 (by rfl) ⟨181419, by rfl⟩ : syracuseStep 483785 = 362839) B362839
theorem B320007 : Blo 319836 320007 := bstep (se 1 (by rfl) ⟨240005, by rfl⟩ : syracuseStep 320007 = 480011) B480011
theorem B320015 : Blo 319836 320015 := bstep (se 1 (by rfl) ⟨240011, by rfl⟩ : syracuseStep 320015 = 480023) B480023
theorem B320059 : Blo 319836 320059 := bstep (se 1 (by rfl) ⟨240044, by rfl⟩ : syracuseStep 320059 = 480089) B480089
theorem B811579 : Blo 319836 811579 := bstep (se 1 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 811579 = 1217369) B1217369
theorem B483899 : Blo 319836 483899 := bstep (se 1 (by rfl) ⟨362924, by rfl⟩ : syracuseStep 483899 = 725849) B725849
theorem B483959 : Blo 319836 483959 := bstep (se 1 (by rfl) ⟨362969, by rfl⟩ : syracuseStep 483959 = 725939) B725939
theorem B320135 : Blo 319836 320135 := bstep (se 1 (by rfl) ⟨240101, by rfl⟩ : syracuseStep 320135 = 480203) B480203
theorem B320143 : Blo 319836 320143 := bstep (se 1 (by rfl) ⟨240107, by rfl⟩ : syracuseStep 320143 = 480215) B480215
theorem B483983 : Blo 319836 483983 := bstep (se 1 (by rfl) ⟨362987, by rfl⟩ : syracuseStep 483983 = 725975) B725975
theorem B484025 : Blo 319836 484025 := bstep (se 2 (by rfl) ⟨181509, by rfl⟩ : syracuseStep 484025 = 363019) B363019
theorem B320187 : Blo 319836 320187 := bstep (se 1 (by rfl) ⟨240140, by rfl⟩ : syracuseStep 320187 = 480281) B480281
theorem B811721 : Blo 319836 811721 := bstep (se 2 (by rfl) ⟨304395, by rfl⟩ : syracuseStep 811721 = 608791) B608791
theorem B320263 : Blo 319836 320263 := bstep (se 1 (by rfl) ⟨240197, by rfl⟩ : syracuseStep 320263 = 480395) B480395
theorem B484103 : Blo 319836 484103 := bstep (se 1 (by rfl) ⟨363077, by rfl⟩ : syracuseStep 484103 = 726155) B726155
theorem B320271 : Blo 319836 320271 := bstep (se 1 (by rfl) ⟨240203, by rfl⟩ : syracuseStep 320271 = 480407) B480407
theorem B484139 : Blo 319836 484139 := bstep (se 1 (by rfl) ⟨363104, by rfl⟩ : syracuseStep 484139 = 726209) B726209
theorem B320315 : Blo 319836 320315 := bstep (se 1 (by rfl) ⟨240236, by rfl⟩ : syracuseStep 320315 = 480473) B480473
theorem B484169 : Blo 319836 484169 := bstep (se 2 (by rfl) ⟨181563, by rfl⟩ : syracuseStep 484169 = 363127) B363127
theorem B320391 : Blo 319836 320391 := bstep (se 1 (by rfl) ⟨240293, by rfl⟩ : syracuseStep 320391 = 480587) B480587
theorem B320399 : Blo 319836 320399 := bstep (se 1 (by rfl) ⟨240299, by rfl⟩ : syracuseStep 320399 = 480599) B480599
theorem B320443 : Blo 319836 320443 := bstep (se 1 (by rfl) ⟨240332, by rfl⟩ : syracuseStep 320443 = 480665) B480665
theorem B484283 : Blo 319836 484283 := bstep (se 1 (by rfl) ⟨363212, by rfl⟩ : syracuseStep 484283 = 726425) B726425
theorem B484343 : Blo 319836 484343 := bstep (se 1 (by rfl) ⟨363257, by rfl⟩ : syracuseStep 484343 = 726515) B726515
theorem B320519 : Blo 319836 320519 := bstep (se 1 (by rfl) ⟨240389, by rfl⟩ : syracuseStep 320519 = 480779) B480779
theorem B320527 : Blo 319836 320527 := bstep (se 1 (by rfl) ⟨240395, by rfl⟩ : syracuseStep 320527 = 480791) B480791
theorem B484367 : Blo 319836 484367 := bstep (se 1 (by rfl) ⟨363275, by rfl⟩ : syracuseStep 484367 = 726551) B726551
theorem B812065 : Blo 319836 812065 := bstep (se 2 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 812065 = 609049) B609049
theorem B484409 : Blo 319836 484409 := bstep (se 2 (by rfl) ⟨181653, by rfl⟩ : syracuseStep 484409 = 363307) B363307
theorem B320571 : Blo 319836 320571 := bstep (se 1 (by rfl) ⟨240428, by rfl⟩ : syracuseStep 320571 = 480857) B480857
theorem B320647 : Blo 319836 320647 := bstep (se 1 (by rfl) ⟨240485, by rfl⟩ : syracuseStep 320647 = 480971) B480971
theorem B484487 : Blo 319836 484487 := bstep (se 1 (by rfl) ⟨363365, by rfl⟩ : syracuseStep 484487 = 726731) B726731
theorem B320655 : Blo 319836 320655 := bstep (se 1 (by rfl) ⟨240491, by rfl⟩ : syracuseStep 320655 = 480983) B480983
theorem B484523 : Blo 319836 484523 := bstep (se 1 (by rfl) ⟨363392, by rfl⟩ : syracuseStep 484523 = 726785) B726785
theorem B320699 : Blo 319836 320699 := bstep (se 1 (by rfl) ⟨240524, by rfl⟩ : syracuseStep 320699 = 481049) B481049
theorem B484553 : Blo 319836 484553 := bstep (se 2 (by rfl) ⟨181707, by rfl⟩ : syracuseStep 484553 = 363415) B363415
theorem B320775 : Blo 319836 320775 := bstep (se 1 (by rfl) ⟨240581, by rfl⟩ : syracuseStep 320775 = 481163) B481163
theorem B320783 : Blo 319836 320783 := bstep (se 1 (by rfl) ⟨240587, by rfl⟩ : syracuseStep 320783 = 481175) B481175
theorem B320827 : Blo 319836 320827 := bstep (se 1 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 320827 = 481241) B481241
theorem B484667 : Blo 319836 484667 := bstep (se 1 (by rfl) ⟨363500, by rfl⟩ : syracuseStep 484667 = 727001) B727001
theorem B484727 : Blo 319836 484727 := bstep (se 1 (by rfl) ⟨363545, by rfl⟩ : syracuseStep 484727 = 727091) B727091
theorem B320903 : Blo 319836 320903 := bstep (se 1 (by rfl) ⟨240677, by rfl⟩ : syracuseStep 320903 = 481355) B481355
theorem B320911 : Blo 319836 320911 := bstep (se 1 (by rfl) ⟨240683, by rfl⟩ : syracuseStep 320911 = 481367) B481367
theorem B484751 : Blo 319836 484751 := bstep (se 1 (by rfl) ⟨363563, by rfl⟩ : syracuseStep 484751 = 727127) B727127
theorem B1828241 : Blo 319836 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B484793 : Blo 319836 484793 := bstep (se 2 (by rfl) ⟨181797, by rfl⟩ : syracuseStep 484793 = 363595) B363595
theorem B320955 : Blo 319836 320955 := bstep (se 1 (by rfl) ⟨240716, by rfl⟩ : syracuseStep 320955 = 481433) B481433
theorem B4384205 : Blo 319836 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B2450897 : Blo 319836 2450897 := bstep (se 2 (by rfl) ⟨919086, by rfl⟩ : syracuseStep 2450897 = 1838173) B1838173
theorem B321031 : Blo 319836 321031 := bstep (se 1 (by rfl) ⟨240773, by rfl⟩ : syracuseStep 321031 = 481547) B481547
theorem B484871 : Blo 319836 484871 := bstep (se 1 (by rfl) ⟨363653, by rfl⟩ : syracuseStep 484871 = 727307) B727307
theorem B321039 : Blo 319836 321039 := bstep (se 1 (by rfl) ⟨240779, by rfl⟩ : syracuseStep 321039 = 481559) B481559
theorem B2942507 : Blo 319836 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B484907 : Blo 319836 484907 := bstep (se 1 (by rfl) ⟨363680, by rfl⟩ : syracuseStep 484907 = 727361) B727361
theorem B321083 : Blo 319836 321083 := bstep (se 1 (by rfl) ⟨240812, by rfl⟩ : syracuseStep 321083 = 481625) B481625
theorem B484937 : Blo 319836 484937 := bstep (se 2 (by rfl) ⟨181851, by rfl⟩ : syracuseStep 484937 = 363703) B363703
theorem B812663 : Blo 319836 812663 := bstep (se 1 (by rfl) ⟨609497, by rfl⟩ : syracuseStep 812663 = 1218995) B1218995
theorem B321159 : Blo 319836 321159 := bstep (se 1 (by rfl) ⟨240869, by rfl⟩ : syracuseStep 321159 = 481739) B481739
theorem B321167 : Blo 319836 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B321211 : Blo 319836 321211 := bstep (se 1 (by rfl) ⟨240908, by rfl⟩ : syracuseStep 321211 = 481817) B481817
theorem B485051 : Blo 319836 485051 := bstep (se 1 (by rfl) ⟨363788, by rfl⟩ : syracuseStep 485051 = 727577) B727577
theorem B485111 : Blo 319836 485111 := bstep (se 1 (by rfl) ⟨363833, by rfl⟩ : syracuseStep 485111 = 727667) B727667
theorem B1795841 : Blo 319836 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B321287 : Blo 319836 321287 := bstep (se 1 (by rfl) ⟨240965, by rfl⟩ : syracuseStep 321287 = 481931) B481931
theorem B321295 : Blo 319836 321295 := bstep (se 1 (by rfl) ⟨240971, by rfl⟩ : syracuseStep 321295 = 481943) B481943
theorem B485135 : Blo 319836 485135 := bstep (se 1 (by rfl) ⟨363851, by rfl⟩ : syracuseStep 485135 = 727703) B727703
theorem B485177 : Blo 319836 485177 := bstep (se 2 (by rfl) ⟨181941, by rfl⟩ : syracuseStep 485177 = 363883) B363883
theorem B976699 : Blo 319836 976699 := bstep (se 1 (by rfl) ⟨732524, by rfl⟩ : syracuseStep 976699 = 1465049) B1465049
theorem B321339 : Blo 319836 321339 := bstep (se 1 (by rfl) ⟨241004, by rfl⟩ : syracuseStep 321339 = 482009) B482009
theorem B386875 : Blo 319836 386875 := bstep (se 1 (by rfl) ⟨290156, by rfl⟩ : syracuseStep 386875 = 580313) B580313
theorem B321415 : Blo 319836 321415 := bstep (se 1 (by rfl) ⟨241061, by rfl⟩ : syracuseStep 321415 = 482123) B482123
theorem B485255 : Blo 319836 485255 := bstep (se 1 (by rfl) ⟨363941, by rfl⟩ : syracuseStep 485255 = 727883) B727883
theorem B321423 : Blo 319836 321423 := bstep (se 1 (by rfl) ⟨241067, by rfl⟩ : syracuseStep 321423 = 482135) B482135
theorem B485291 : Blo 319836 485291 := bstep (se 1 (by rfl) ⟨363968, by rfl⟩ : syracuseStep 485291 = 727937) B727937
theorem B321467 : Blo 319836 321467 := bstep (se 1 (by rfl) ⟨241100, by rfl⟩ : syracuseStep 321467 = 482201) B482201
theorem B518089 : Blo 319836 518089 := bstep (se 2 (by rfl) ⟨194283, by rfl⟩ : syracuseStep 518089 = 388567) B388567
theorem B485321 : Blo 319836 485321 := bstep (se 2 (by rfl) ⟨181995, by rfl⟩ : syracuseStep 485321 = 363991) B363991
theorem B321543 : Blo 319836 321543 := bstep (se 1 (by rfl) ⟨241157, by rfl⟩ : syracuseStep 321543 = 482315) B482315
theorem B321551 : Blo 319836 321551 := bstep (se 1 (by rfl) ⟨241163, by rfl⟩ : syracuseStep 321551 = 482327) B482327
theorem B1370141 : Blo 319836 1370141 := bstep (se 3 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 1370141 = 513803) B513803
theorem B321595 : Blo 319836 321595 := bstep (se 1 (by rfl) ⟨241196, by rfl⟩ : syracuseStep 321595 = 482393) B482393
theorem B485435 : Blo 319836 485435 := bstep (se 1 (by rfl) ⟨364076, by rfl⟩ : syracuseStep 485435 = 728153) B728153
theorem B1828925 : Blo 319836 1828925 := bstep (se 3 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 1828925 = 685847) B685847
theorem B485495 : Blo 319836 485495 := bstep (se 1 (by rfl) ⟨364121, by rfl⟩ : syracuseStep 485495 = 728243) B728243
theorem B321671 : Blo 319836 321671 := bstep (se 1 (by rfl) ⟨241253, by rfl⟩ : syracuseStep 321671 = 482507) B482507
theorem B321679 : Blo 319836 321679 := bstep (se 1 (by rfl) ⟨241259, by rfl⟩ : syracuseStep 321679 = 482519) B482519
theorem B485519 : Blo 319836 485519 := bstep (se 1 (by rfl) ⟨364139, by rfl⟩ : syracuseStep 485519 = 728279) B728279
theorem B911513 : Blo 319836 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B485561 : Blo 319836 485561 := bstep (se 2 (by rfl) ⟨182085, by rfl⟩ : syracuseStep 485561 = 364171) B364171
theorem B321723 : Blo 319836 321723 := bstep (se 1 (by rfl) ⟨241292, by rfl⟩ : syracuseStep 321723 = 482585) B482585
theorem B1566977 : Blo 319836 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B321799 : Blo 319836 321799 := bstep (se 1 (by rfl) ⟨241349, by rfl⟩ : syracuseStep 321799 = 482699) B482699
theorem B485639 : Blo 319836 485639 := bstep (se 1 (by rfl) ⟨364229, by rfl⟩ : syracuseStep 485639 = 728459) B728459
theorem B321807 : Blo 319836 321807 := bstep (se 1 (by rfl) ⟨241355, by rfl⟩ : syracuseStep 321807 = 482711) B482711
theorem B485675 : Blo 319836 485675 := bstep (se 1 (by rfl) ⟨364256, by rfl⟩ : syracuseStep 485675 = 728513) B728513
theorem B321851 : Blo 319836 321851 := bstep (se 1 (by rfl) ⟨241388, by rfl⟩ : syracuseStep 321851 = 482777) B482777
theorem B485705 : Blo 319836 485705 := bstep (se 2 (by rfl) ⟨182139, by rfl⟩ : syracuseStep 485705 = 364279) B364279
theorem B321927 : Blo 319836 321927 := bstep (se 1 (by rfl) ⟨241445, by rfl⟩ : syracuseStep 321927 = 482891) B482891
theorem B321935 : Blo 319836 321935 := bstep (se 1 (by rfl) ⟨241451, by rfl⟩ : syracuseStep 321935 = 482903) B482903
theorem B321979 : Blo 319836 321979 := bstep (se 1 (by rfl) ⟨241484, by rfl⟩ : syracuseStep 321979 = 482969) B482969
theorem B322055 : Blo 319836 322055 := bstep (se 1 (by rfl) ⟨241541, by rfl⟩ : syracuseStep 322055 = 483083) B483083
theorem B322063 : Blo 319836 322063 := bstep (se 1 (by rfl) ⟨241547, by rfl⟩ : syracuseStep 322063 = 483095) B483095
theorem B1632797 : Blo 319836 1632797 := bstep (se 3 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 1632797 = 612299) B612299
theorem B322107 : Blo 319836 322107 := bstep (se 1 (by rfl) ⟨241580, by rfl⟩ : syracuseStep 322107 = 483161) B483161
theorem B2091587 : Blo 319836 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B322183 : Blo 319836 322183 := bstep (se 1 (by rfl) ⟨241637, by rfl⟩ : syracuseStep 322183 = 483275) B483275
theorem B322191 : Blo 319836 322191 := bstep (se 1 (by rfl) ⟨241643, by rfl⟩ : syracuseStep 322191 = 483287) B483287
theorem B322235 : Blo 319836 322235 := bstep (se 1 (by rfl) ⟨241676, by rfl⟩ : syracuseStep 322235 = 483353) B483353
theorem B322311 : Blo 319836 322311 := bstep (se 1 (by rfl) ⟨241733, by rfl⟩ : syracuseStep 322311 = 483467) B483467
theorem B322319 : Blo 319836 322319 := bstep (se 1 (by rfl) ⟨241739, by rfl⟩ : syracuseStep 322319 = 483479) B483479
theorem B912161 : Blo 319836 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B748331 : Blo 319836 748331 := bstep (se 1 (by rfl) ⟨561248, by rfl⟩ : syracuseStep 748331 = 1122497) B1122497
theorem B322363 : Blo 319836 322363 := bstep (se 1 (by rfl) ⟨241772, by rfl⟩ : syracuseStep 322363 = 483545) B483545
theorem B813959 : Blo 319836 813959 := bstep (se 1 (by rfl) ⟨610469, by rfl⟩ : syracuseStep 813959 = 1220939) B1220939
theorem B322439 : Blo 319836 322439 := bstep (se 1 (by rfl) ⟨241829, by rfl⟩ : syracuseStep 322439 = 483659) B483659
theorem B322447 : Blo 319836 322447 := bstep (se 1 (by rfl) ⟨241835, by rfl⟩ : syracuseStep 322447 = 483671) B483671
theorem B814009 : Blo 319836 814009 := bstep (se 2 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 814009 = 610507) B610507
theorem B322491 : Blo 319836 322491 := bstep (se 1 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 322491 = 483737) B483737
theorem B1633283 : Blo 319836 1633283 := bstep (se 1 (by rfl) ⟨1224962, by rfl⟩ : syracuseStep 1633283 = 2449925) B2449925
theorem B322567 : Blo 319836 322567 := bstep (se 1 (by rfl) ⟨241925, by rfl⟩ : syracuseStep 322567 = 483851) B483851
theorem B322575 : Blo 319836 322575 := bstep (se 1 (by rfl) ⟨241931, by rfl⟩ : syracuseStep 322575 = 483863) B483863
theorem B322619 : Blo 319836 322619 := bstep (se 1 (by rfl) ⟨241964, by rfl⟩ : syracuseStep 322619 = 483929) B483929
theorem B322695 : Blo 319836 322695 := bstep (se 1 (by rfl) ⟨242021, by rfl⟩ : syracuseStep 322695 = 484043) B484043
theorem B322703 : Blo 319836 322703 := bstep (se 1 (by rfl) ⟨242027, by rfl⟩ : syracuseStep 322703 = 484055) B484055
theorem B322747 : Blo 319836 322747 := bstep (se 1 (by rfl) ⟨242060, by rfl⟩ : syracuseStep 322747 = 484121) B484121
theorem B322823 : Blo 319836 322823 := bstep (se 1 (by rfl) ⟨242117, by rfl⟩ : syracuseStep 322823 = 484235) B484235
theorem B322831 : Blo 319836 322831 := bstep (se 1 (by rfl) ⟨242123, by rfl⟩ : syracuseStep 322831 = 484247) B484247
theorem B1731899 : Blo 319836 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B322875 : Blo 319836 322875 := bstep (se 1 (by rfl) ⟨242156, by rfl⟩ : syracuseStep 322875 = 484313) B484313
theorem B388471 : Blo 319836 388471 := bstep (se 1 (by rfl) ⟨291353, by rfl⟩ : syracuseStep 388471 = 582707) B582707
theorem B322951 : Blo 319836 322951 := bstep (se 1 (by rfl) ⟨242213, by rfl⟩ : syracuseStep 322951 = 484427) B484427
theorem B322959 : Blo 319836 322959 := bstep (se 1 (by rfl) ⟨242219, by rfl⟩ : syracuseStep 322959 = 484439) B484439
theorem B323003 : Blo 319836 323003 := bstep (se 1 (by rfl) ⟨242252, by rfl⟩ : syracuseStep 323003 = 484505) B484505
theorem B3665411 : Blo 319836 3665411 := bstep (se 1 (by rfl) ⟨2749058, by rfl⟩ : syracuseStep 3665411 = 5498117) B5498117
theorem B323079 : Blo 319836 323079 := bstep (se 1 (by rfl) ⟨242309, by rfl⟩ : syracuseStep 323079 = 484619) B484619
theorem B814607 : Blo 319836 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B323087 : Blo 319836 323087 := bstep (se 1 (by rfl) ⟨242315, by rfl⟩ : syracuseStep 323087 = 484631) B484631
theorem B323131 : Blo 319836 323131 := bstep (se 1 (by rfl) ⟨242348, by rfl⟩ : syracuseStep 323131 = 484697) B484697
theorem B323207 : Blo 319836 323207 := bstep (se 1 (by rfl) ⟨242405, by rfl⟩ : syracuseStep 323207 = 484811) B484811
theorem B323215 : Blo 319836 323215 := bstep (se 1 (by rfl) ⟨242411, by rfl⟩ : syracuseStep 323215 = 484823) B484823
theorem B323259 : Blo 319836 323259 := bstep (se 1 (by rfl) ⟨242444, by rfl⟩ : syracuseStep 323259 = 484889) B484889
theorem B913153 : Blo 319836 913153 := bstep (se 2 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 913153 = 684865) B684865
theorem B323335 : Blo 319836 323335 := bstep (se 1 (by rfl) ⟨242501, by rfl⟩ : syracuseStep 323335 = 485003) B485003
theorem B1240847 : Blo 319836 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B323343 : Blo 319836 323343 := bstep (se 1 (by rfl) ⟨242507, by rfl⟩ : syracuseStep 323343 = 485015) B485015
theorem B323387 : Blo 319836 323387 := bstep (se 1 (by rfl) ⟨242540, by rfl⟩ : syracuseStep 323387 = 485081) B485081
theorem B323463 : Blo 319836 323463 := bstep (se 1 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 323463 = 485195) B485195
theorem B323471 : Blo 319836 323471 := bstep (se 1 (by rfl) ⟨242603, by rfl⟩ : syracuseStep 323471 = 485207) B485207
theorem B323515 : Blo 319836 323515 := bstep (se 1 (by rfl) ⟨242636, by rfl⟩ : syracuseStep 323515 = 485273) B485273
theorem B683977 : Blo 319836 683977 := bstep (se 2 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 683977 = 512983) B512983
theorem B323591 : Blo 319836 323591 := bstep (se 1 (by rfl) ⟨242693, by rfl⟩ : syracuseStep 323591 = 485387) B485387
theorem B323599 : Blo 319836 323599 := bstep (se 1 (by rfl) ⟨242699, by rfl⟩ : syracuseStep 323599 = 485399) B485399
theorem B323643 : Blo 319836 323643 := bstep (se 1 (by rfl) ⟨242732, by rfl⟩ : syracuseStep 323643 = 485465) B485465
theorem B323719 : Blo 319836 323719 := bstep (se 1 (by rfl) ⟨242789, by rfl⟩ : syracuseStep 323719 = 485579) B485579
theorem B323727 : Blo 319836 323727 := bstep (se 1 (by rfl) ⟨242795, by rfl⟩ : syracuseStep 323727 = 485591) B485591
theorem B323771 : Blo 319836 323771 := bstep (se 1 (by rfl) ⟨242828, by rfl⟩ : syracuseStep 323771 = 485657) B485657
theorem B815305 : Blo 319836 815305 := bstep (se 2 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 815305 = 611479) B611479
theorem B815447 : Blo 319836 815447 := bstep (se 1 (by rfl) ⟨611585, by rfl⟩ : syracuseStep 815447 = 1223171) B1223171
theorem B1634903 : Blo 319836 1634903 := bstep (se 1 (by rfl) ⟨1226177, by rfl⟩ : syracuseStep 1634903 = 2452355) B2452355
theorem B979609 : Blo 319836 979609 := bstep (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) B734707
theorem B651977 : Blo 319836 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B455483 : Blo 319836 455483 := bstep (se 1 (by rfl) ⟨341612, by rfl⟩ : syracuseStep 455483 = 683225) B683225
theorem B1635389 : Blo 319836 1635389 := bstep (se 3 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 1635389 = 613271) B613271
theorem B1537427 : Blo 319836 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B3339667 : Blo 319836 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B652691 : Blo 319836 652691 := bstep (se 1 (by rfl) ⟨489518, by rfl⟩ : syracuseStep 652691 = 979037) B979037
theorem B456121 : Blo 319836 456121 := bstep (se 2 (by rfl) ⟨171045, by rfl⟩ : syracuseStep 456121 = 342091) B342091
theorem B6714809 : Blo 319836 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B1308221 : Blo 319836 1308221 := bstep (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) B490583
theorem B325307 : Blo 319836 325307 := bstep (se 1 (by rfl) ⟨243980, by rfl⟩ : syracuseStep 325307 = 487961) B487961
theorem B587911 : Blo 319836 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B1079567 : Blo 319836 1079567 := bstep (se 1 (by rfl) ⟨809675, by rfl⟩ : syracuseStep 1079567 = 1619351) B1619351
theorem B686369 : Blo 319836 686369 := bstep (se 2 (by rfl) ⟨257388, by rfl⟩ : syracuseStep 686369 = 514777) B514777
theorem B817523 : Blo 319836 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B850447 : Blo 319836 850447 := bstep (se 1 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 850447 = 1275671) B1275671
theorem B1079837 : Blo 319836 1079837 := bstep (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) B404939
theorem B686711 : Blo 319836 686711 := bstep (se 1 (by rfl) ⟨515033, by rfl⟩ : syracuseStep 686711 = 1030067) B1030067
theorem B1374839 : Blo 319836 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B916103 : Blo 319836 916103 := bstep (se 1 (by rfl) ⟨687077, by rfl⟩ : syracuseStep 916103 = 1374155) B1374155
theorem B1637171 : Blo 319836 1637171 := bstep (se 1 (by rfl) ⟨1227878, by rfl⟩ : syracuseStep 1637171 = 2455757) B2455757
theorem B719675 : Blo 319836 719675 := bstep (se 1 (by rfl) ⟨539756, by rfl⟩ : syracuseStep 719675 = 1079513) B1079513
theorem B916285 : Blo 319836 916285 := bstep (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) B343607
theorem B916343 : Blo 319836 916343 := bstep (se 1 (by rfl) ⟨687257, by rfl⟩ : syracuseStep 916343 = 1374515) B1374515
theorem B818039 : Blo 319836 818039 := bstep (se 1 (by rfl) ⟨613529, by rfl⟩ : syracuseStep 818039 = 1227059) B1227059
theorem B457607 : Blo 319836 457607 := bstep (se 1 (by rfl) ⟨343205, by rfl⟩ : syracuseStep 457607 = 686411) B686411
theorem B719801 : Blo 319836 719801 := bstep (se 2 (by rfl) ⟨269925, by rfl⟩ : syracuseStep 719801 = 539851) B539851
theorem B1539101 : Blo 319836 1539101 := bstep (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) B577163
theorem B621611 : Blo 319836 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B687163 : Blo 319836 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B1637495 : Blo 319836 1637495 := bstep (se 1 (by rfl) ⟨1228121, by rfl⟩ : syracuseStep 1637495 = 2456243) B2456243
theorem B457915 : Blo 319836 457915 := bstep (se 1 (by rfl) ⟨343436, by rfl⟩ : syracuseStep 457915 = 686873) B686873
theorem B720143 : Blo 319836 720143 := bstep (se 1 (by rfl) ⟨540107, by rfl⟩ : syracuseStep 720143 = 1080215) B1080215
theorem B720161 : Blo 319836 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B359995 : Blo 319836 359995 := bstep (se 1 (by rfl) ⟨269996, by rfl⟩ : syracuseStep 359995 = 539993) B539993
theorem B720503 : Blo 319836 720503 := bstep (se 1 (by rfl) ⟨540377, by rfl⟩ : syracuseStep 720503 = 1080755) B1080755
theorem B720683 : Blo 319836 720683 := bstep (se 1 (by rfl) ⟨540512, by rfl⟩ : syracuseStep 720683 = 1081025) B1081025
theorem B819031 : Blo 319836 819031 := bstep (se 1 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 819031 = 1228547) B1228547
theorem B1081241 : Blo 319836 1081241 := bstep (se 2 (by rfl) ⟨405465, by rfl⟩ : syracuseStep 1081241 = 810931) B810931
theorem B917401 : Blo 319836 917401 := bstep (se 2 (by rfl) ⟨344025, by rfl⟩ : syracuseStep 917401 = 688051) B688051
theorem B1540043 : Blo 319836 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B720953 : Blo 319836 720953 := bstep (se 2 (by rfl) ⟨270357, by rfl⟩ : syracuseStep 720953 = 540715) B540715
theorem B917561 : Blo 319836 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B360571 : Blo 319836 360571 := bstep (se 1 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 360571 = 540857) B540857
theorem B917675 : Blo 319836 917675 := bstep (se 1 (by rfl) ⟨688256, by rfl⟩ : syracuseStep 917675 = 1376513) B1376513
theorem B458951 : Blo 319836 458951 := bstep (se 1 (by rfl) ⟨344213, by rfl⟩ : syracuseStep 458951 = 688427) B688427
theorem B721295 : Blo 319836 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B4653571 : Blo 319836 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B1081889 : Blo 319836 1081889 := bstep (se 2 (by rfl) ⟨405708, by rfl⟩ : syracuseStep 1081889 = 811417) B811417
theorem B361039 : Blo 319836 361039 := bstep (se 1 (by rfl) ⟨270779, by rfl⟩ : syracuseStep 361039 = 541559) B541559
theorem B721619 : Blo 319836 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B15958745 : Blo 319836 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B1082105 : Blo 319836 1082105 := bstep (se 2 (by rfl) ⟨405789, by rfl⟩ : syracuseStep 1082105 = 811579) B811579
theorem B7537481 : Blo 319836 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B492383 : Blo 319836 492383 := bstep (se 1 (by rfl) ⟨369287, by rfl⟩ : syracuseStep 492383 = 738575) B738575
theorem B459703 : Blo 319836 459703 := bstep (se 1 (by rfl) ⟨344777, by rfl⟩ : syracuseStep 459703 = 689555) B689555
theorem B361435 : Blo 319836 361435 := bstep (se 1 (by rfl) ⟨271076, by rfl⟩ : syracuseStep 361435 = 542153) B542153
theorem B1082375 : Blo 319836 1082375 := bstep (se 1 (by rfl) ⟨811781, by rfl⟩ : syracuseStep 1082375 = 1623563) B1623563
theorem B2458673 : Blo 319836 2458673 := bstep (se 2 (by rfl) ⟨922002, by rfl⟩ : syracuseStep 2458673 = 1844005) B1844005
theorem B1082483 : Blo 319836 1082483 := bstep (se 1 (by rfl) ⟨811862, by rfl⟩ : syracuseStep 1082483 = 1623725) B1623725
theorem B3671243 : Blo 319836 3671243 := bstep (se 1 (by rfl) ⟨2753432, by rfl⟩ : syracuseStep 3671243 = 5506865) B5506865
theorem B1082753 : Blo 319836 1082753 := bstep (se 2 (by rfl) ⟨406032, by rfl⟩ : syracuseStep 1082753 = 812065) B812065
theorem B361903 : Blo 319836 361903 := bstep (se 1 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 361903 = 542855) B542855
theorem B2197115 : Blo 319836 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B722555 : Blo 319836 722555 := bstep (se 1 (by rfl) ⟨541916, by rfl⟩ : syracuseStep 722555 = 1083833) B1083833
theorem B1377931 : Blo 319836 1377931 := bstep (se 1 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 1377931 = 2066897) B2066897
theorem B14419603 : Blo 319836 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B722681 : Blo 319836 722681 := bstep (se 2 (by rfl) ⟨271005, by rfl⟩ : syracuseStep 722681 = 542011) B542011
theorem B362335 : Blo 319836 362335 := bstep (se 1 (by rfl) ⟨271751, by rfl⟩ : syracuseStep 362335 = 543503) B543503
theorem B722951 : Blo 319836 722951 := bstep (se 1 (by rfl) ⟨542213, by rfl⟩ : syracuseStep 722951 = 1084427) B1084427
theorem B1574927 : Blo 319836 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B723023 : Blo 319836 723023 := bstep (se 1 (by rfl) ⟨542267, by rfl⟩ : syracuseStep 723023 = 1084535) B1084535
theorem B1214621 : Blo 319836 1214621 := bstep (se 3 (by rfl) ⟨227741, by rfl⟩ : syracuseStep 1214621 = 455483) B455483
theorem B1214635 : Blo 319836 1214635 := bstep (se 1 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 1214635 = 1821953) B1821953
theorem B1083563 : Blo 319836 1083563 := bstep (se 1 (by rfl) ⟨812672, by rfl⟩ : syracuseStep 1083563 = 1625345) B1625345
theorem B362695 : Blo 319836 362695 := bstep (se 1 (by rfl) ⟨272021, by rfl⟩ : syracuseStep 362695 = 544043) B544043
theorem B1214939 : Blo 319836 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B723419 : Blo 319836 723419 := bstep (se 1 (by rfl) ⟨542564, by rfl⟩ : syracuseStep 723419 = 1085129) B1085129
theorem B920089 : Blo 319836 920089 := bstep (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) B690067
theorem B690785 : Blo 319836 690785 := bstep (se 2 (by rfl) ⟨259044, by rfl⟩ : syracuseStep 690785 = 518089) B518089
theorem B16714421 : Blo 319836 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1084103 : Blo 319836 1084103 := bstep (se 1 (by rfl) ⟨813077, by rfl⟩ : syracuseStep 1084103 = 1626155) B1626155
theorem B690887 : Blo 319836 690887 := bstep (se 1 (by rfl) ⟨518165, by rfl⟩ : syracuseStep 690887 = 1036331) B1036331
theorem B723887 : Blo 319836 723887 := bstep (se 1 (by rfl) ⟨542915, by rfl⟩ : syracuseStep 723887 = 1085831) B1085831
theorem B2067383 : Blo 319836 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B363559 : Blo 319836 363559 := bstep (se 1 (by rfl) ⟨272669, by rfl⟩ : syracuseStep 363559 = 545339) B545339
theorem B2067535 : Blo 319836 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B724139 : Blo 319836 724139 := bstep (se 1 (by rfl) ⟨543104, by rfl⟩ : syracuseStep 724139 = 1086209) B1086209
theorem B7015619 : Blo 319836 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B1084967 : Blo 319836 1084967 := bstep (se 1 (by rfl) ⟨813725, by rfl⟩ : syracuseStep 1084967 = 1627451) B1627451
theorem B1085075 : Blo 319836 1085075 := bstep (se 1 (by rfl) ⟨813806, by rfl⟩ : syracuseStep 1085075 = 1627613) B1627613
theorem B1740487 : Blo 319836 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B724679 : Blo 319836 724679 := bstep (se 1 (by rfl) ⟨543509, by rfl⟩ : syracuseStep 724679 = 1087019) B1087019
theorem B4099805 : Blo 319836 4099805 := bstep (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) B1537427
theorem B1085291 : Blo 319836 1085291 := bstep (se 1 (by rfl) ⟨813968, by rfl⟩ : syracuseStep 1085291 = 1627937) B1627937
theorem B2330477 : Blo 319836 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B1085345 : Blo 319836 1085345 := bstep (se 2 (by rfl) ⟨407004, by rfl⟩ : syracuseStep 1085345 = 814009) B814009
theorem B2068537 : Blo 319836 2068537 := bstep (se 2 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 2068537 = 1551403) B1551403
theorem B1085939 : Blo 319836 1085939 := bstep (se 1 (by rfl) ⟨814454, by rfl⟩ : syracuseStep 1085939 = 1628909) B1628909
theorem B331321873 : Blo 319836 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B725543 : Blo 319836 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B725867 : Blo 319836 725867 := bstep (se 1 (by rfl) ⟨544400, by rfl⟩ : syracuseStep 725867 = 1088801) B1088801
theorem B725921 : Blo 319836 725921 := bstep (se 2 (by rfl) ⟨272220, by rfl⟩ : syracuseStep 725921 = 544441) B544441
theorem B1217537 : Blo 319836 1217537 := bstep (se 2 (by rfl) ⟨456576, by rfl⟩ : syracuseStep 1217537 = 913153) B913153
theorem B1217551 : Blo 319836 1217551 := bstep (se 1 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 1217551 = 1826327) B1826327
theorem B1086479 : Blo 319836 1086479 := bstep (se 1 (by rfl) ⟨814859, by rfl⟩ : syracuseStep 1086479 = 1629719) B1629719
theorem B726263 : Blo 319836 726263 := bstep (se 1 (by rfl) ⟨544697, by rfl⟩ : syracuseStep 726263 = 1089395) B1089395
theorem B1087073 : Blo 319836 1087073 := bstep (se 2 (by rfl) ⟨407652, by rfl⟩ : syracuseStep 1087073 = 815305) B815305
theorem B2070305 : Blo 319836 2070305 := bstep (se 2 (by rfl) ⟨776364, by rfl⟩ : syracuseStep 2070305 = 1552729) B1552729
theorem B726857 : Blo 319836 726857 := bstep (se 2 (by rfl) ⟨272571, by rfl⟩ : syracuseStep 726857 = 545143) B545143
theorem B1382305 : Blo 319836 1382305 := bstep (se 2 (by rfl) ⟨518364, by rfl⟩ : syracuseStep 1382305 = 1036729) B1036729
theorem B1841089 : Blo 319836 1841089 := bstep (se 2 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 1841089 = 1380817) B1380817
theorem B3708965 : Blo 319836 3708965 := bstep (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) B695431
theorem B1218827 : Blo 319836 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B2922803 : Blo 319836 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B2071021 : Blo 319836 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B727649 : Blo 319836 727649 := bstep (se 2 (by rfl) ⟨272868, by rfl⟩ : syracuseStep 727649 = 545737) B545737
theorem B1317575 : Blo 319836 1317575 := bstep (se 1 (by rfl) ⟨988181, by rfl⟩ : syracuseStep 1317575 = 1976363) B1976363
theorem B1219283 : Blo 319836 1219283 := bstep (se 1 (by rfl) ⟨914462, by rfl⟩ : syracuseStep 1219283 = 1828925) B1828925
theorem B629497 : Blo 319836 629497 := bstep (se 2 (by rfl) ⟨236061, by rfl⟩ : syracuseStep 629497 = 472123) B472123
theorem B1153865 : Blo 319836 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B3677075 : Blo 319836 3677075 := bstep (se 1 (by rfl) ⟨2757806, by rfl⟩ : syracuseStep 3677075 = 5515613) B5515613
theorem B8919989 : Blo 319836 8919989 := bstep (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) B836249
theorem B727991 : Blo 319836 727991 := bstep (se 1 (by rfl) ⟨545993, by rfl⟩ : syracuseStep 727991 = 1091987) B1091987
theorem B1088531 : Blo 319836 1088531 := bstep (se 1 (by rfl) ⟨816398, by rfl⟩ : syracuseStep 1088531 = 1632797) B1632797
theorem B498887 : Blo 319836 498887 := bstep (se 1 (by rfl) ⟨374165, by rfl⟩ : syracuseStep 498887 = 748331) B748331
theorem B1088855 : Blo 319836 1088855 := bstep (se 1 (by rfl) ⟨816641, by rfl⟩ : syracuseStep 1088855 = 1633283) B1633283
theorem B2432429 : Blo 319836 2432429 := bstep (se 3 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 2432429 = 912161) B912161
theorem B728585 : Blo 319836 728585 := bstep (se 2 (by rfl) ⟨273219, by rfl⟩ : syracuseStep 728585 = 546439) B546439
theorem B1220285 : Blo 319836 1220285 := bstep (se 3 (by rfl) ⟨228803, by rfl⟩ : syracuseStep 1220285 = 457607) B457607
theorem B827231 : Blo 319836 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B466795 : Blo 319836 466795 := bstep (se 1 (by rfl) ⟨350096, by rfl⟩ : syracuseStep 466795 = 700193) B700193
theorem B4104269 : Blo 319836 4104269 := bstep (se 3 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 4104269 = 1539101) B1539101
theorem B1089935 : Blo 319836 1089935 := bstep (se 1 (by rfl) ⟨817451, by rfl⟩ : syracuseStep 1089935 = 1634903) B1634903
theorem B434651 : Blo 319836 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B1090259 : Blo 319836 1090259 := bstep (se 1 (by rfl) ⟨817694, by rfl⟩ : syracuseStep 1090259 = 1635389) B1635389
theorem B435127 : Blo 319836 435127 := bstep (se 1 (by rfl) ⟨326345, by rfl⟩ : syracuseStep 435127 = 652691) B652691
theorem B664615 : Blo 319836 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B1025081 : Blo 319836 1025081 := bstep (se 2 (by rfl) ⟨384405, by rfl⟩ : syracuseStep 1025081 = 768811) B768811
theorem B1221713 : Blo 319836 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B2106647 : Blo 319836 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B2434859 : Blo 319836 2434859 := bstep (se 1 (by rfl) ⟨1826144, by rfl⟩ : syracuseStep 2434859 = 3652289) B3652289
theorem B1091447 : Blo 319836 1091447 := bstep (se 1 (by rfl) ⟨818585, by rfl⟩ : syracuseStep 1091447 = 1637171) B1637171
theorem B1091663 : Blo 319836 1091663 := bstep (se 1 (by rfl) ⟨818747, by rfl⟩ : syracuseStep 1091663 = 1637495) B1637495
theorem B1092041 : Blo 319836 1092041 := bstep (se 2 (by rfl) ⟨409515, by rfl⟩ : syracuseStep 1092041 = 819031) B819031
theorem B1223201 : Blo 319836 1223201 := bstep (se 2 (by rfl) ⟨458700, by rfl⟩ : syracuseStep 1223201 = 917401) B917401
theorem B1026695 : Blo 319836 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B764615 : Blo 319836 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B1223383 : Blo 319836 1223383 := bstep (se 1 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 1223383 = 1835075) B1835075
theorem B1092311 : Blo 319836 1092311 := bstep (se 1 (by rfl) ⟨819233, by rfl⟩ : syracuseStep 1092311 = 1638467) B1638467
theorem B1092527 : Blo 319836 1092527 := bstep (se 1 (by rfl) ⟨819395, by rfl⟩ : syracuseStep 1092527 = 1638791) B1638791
theorem B1223687 : Blo 319836 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B1616915 : Blo 319836 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1224173 : Blo 319836 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B4959809 : Blo 319836 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B1028027 : Blo 319836 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B733583 : Blo 319836 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B1225313 : Blo 319836 1225313 := bstep (se 2 (by rfl) ⟨459492, by rfl⟩ : syracuseStep 1225313 = 918985) B918985
theorem B3650831 : Blo 319836 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B2799011 : Blo 319836 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B1226299 : Blo 319836 1226299 := bstep (se 1 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 1226299 = 1839449) B1839449
theorem B2340485 : Blo 319836 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B20821697 : Blo 319836 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B4667179 : Blo 319836 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B3127099 : Blo 319836 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B1226603 : Blo 319836 1226603 := bstep (se 1 (by rfl) ⟨919952, by rfl⟩ : syracuseStep 1226603 = 1839905) B1839905
theorem B1095611 : Blo 319836 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B1226771 : Blo 319836 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1030411 : Blo 319836 1030411 := bstep (se 1 (by rfl) ⟨772808, by rfl⟩ : syracuseStep 1030411 = 1545617) B1545617
theorem B1030487 : Blo 319836 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B1620809 : Blo 319836 1620809 := bstep (se 2 (by rfl) ⟨607803, by rfl⟩ : syracuseStep 1620809 = 1215607) B1215607
theorem B1555307 : Blo 319836 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B408503 : Blo 319836 408503 := bstep (se 1 (by rfl) ⟨306377, by rfl⟩ : syracuseStep 408503 = 612755) B612755
theorem B1162297 : Blo 319836 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B932921 : Blo 319836 932921 := bstep (se 2 (by rfl) ⟨349845, by rfl⟩ : syracuseStep 932921 = 699691) B699691
theorem B408655 : Blo 319836 408655 := bstep (se 1 (by rfl) ⟨306491, by rfl⟩ : syracuseStep 408655 = 612983) B612983
theorem B343163 : Blo 319836 343163 := bstep (se 1 (by rfl) ⟨257372, by rfl⟩ : syracuseStep 343163 = 514745) B514745
theorem B867485 : Blo 319836 867485 := bstep (se 3 (by rfl) ⟨162653, by rfl⟩ : syracuseStep 867485 = 325307) B325307
theorem B540047 : Blo 319836 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B2440691 : Blo 319836 2440691 := bstep (se 1 (by rfl) ⟨1830518, by rfl⟩ : syracuseStep 2440691 = 3661037) B3661037
theorem B540283 : Blo 319836 540283 := bstep (se 1 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 540283 = 810425) B810425
theorem B1949483 : Blo 319836 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B1622105 : Blo 319836 1622105 := bstep (se 2 (by rfl) ⟨608289, by rfl⟩ : syracuseStep 1622105 = 1216579) B1216579
theorem B3653747 : Blo 319836 3653747 := bstep (se 1 (by rfl) ⟨2740310, by rfl⟩ : syracuseStep 3653747 = 5480621) B5480621
theorem B409799 : Blo 319836 409799 := bstep (se 1 (by rfl) ⟨307349, by rfl⟩ : syracuseStep 409799 = 614699) B614699
theorem B541147 : Blo 319836 541147 := bstep (se 1 (by rfl) ⟨405860, by rfl⟩ : syracuseStep 541147 = 811721) B811721
theorem B1032743 : Blo 319836 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B541775 : Blo 319836 541775 := bstep (se 1 (by rfl) ⟨406331, by rfl⟩ : syracuseStep 541775 = 812663) B812663
theorem B1197227 : Blo 319836 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B607675 : Blo 319836 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B608161 : Blo 319836 608161 := bstep (se 2 (by rfl) ⟨228060, by rfl⟩ : syracuseStep 608161 = 456121) B456121
theorem B542639 : Blo 319836 542639 := bstep (se 1 (by rfl) ⟨406979, by rfl⟩ : syracuseStep 542639 = 813959) B813959
theorem B1034167 : Blo 319836 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B4638809 : Blo 319836 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B2443607 : Blo 319836 2443607 := bstep (se 1 (by rfl) ⟨1832705, by rfl⟩ : syracuseStep 2443607 = 3665411) B3665411
theorem B543071 : Blo 319836 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B543631 : Blo 319836 543631 := bstep (se 1 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 543631 = 815447) B815447
theorem B1166393 : Blo 319836 1166393 := bstep (se 2 (by rfl) ⟨437397, by rfl⟩ : syracuseStep 1166393 = 874795) B874795
theorem B1133929 : Blo 319836 1133929 := bstep (se 2 (by rfl) ⟨425223, by rfl⟩ : syracuseStep 1133929 = 850447) B850447
theorem B544313 : Blo 319836 544313 := bstep (se 2 (by rfl) ⟨204117, by rfl⟩ : syracuseStep 544313 = 408235) B408235
theorem B4476539 : Blo 319836 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B1101523 : Blo 319836 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B872147 : Blo 319836 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B1298243 : Blo 319836 1298243 := bstep (se 1 (by rfl) ⟨973682, by rfl⟩ : syracuseStep 1298243 = 1947365) B1947365
theorem B8376331 : Blo 319836 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B545015 : Blo 319836 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B610553 : Blo 319836 610553 := bstep (se 2 (by rfl) ⟨228957, by rfl⟩ : syracuseStep 610553 = 457915) B457915
theorem B1954153 : Blo 319836 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B610735 : Blo 319836 610735 := bstep (se 1 (by rfl) ⟨458051, by rfl⟩ : syracuseStep 610735 = 916103) B916103
theorem B479783 : Blo 319836 479783 := bstep (se 1 (by rfl) ⟨359837, by rfl⟩ : syracuseStep 479783 = 719675) B719675
theorem B610895 : Blo 319836 610895 := bstep (se 1 (by rfl) ⟨458171, by rfl⟩ : syracuseStep 610895 = 916343) B916343
theorem B545359 : Blo 319836 545359 := bstep (se 1 (by rfl) ⟨409019, by rfl⟩ : syracuseStep 545359 = 818039) B818039
theorem B479867 : Blo 319836 479867 := bstep (se 1 (by rfl) ⟨359900, by rfl⟩ : syracuseStep 479867 = 719801) B719801
theorem B414407 : Blo 319836 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B479993 : Blo 319836 479993 := bstep (se 2 (by rfl) ⟨179997, by rfl⟩ : syracuseStep 479993 = 359995) B359995
theorem B545609 : Blo 319836 545609 := bstep (se 2 (by rfl) ⟨204603, by rfl⟩ : syracuseStep 545609 = 409207) B409207
theorem B480095 : Blo 319836 480095 := bstep (se 1 (by rfl) ⟨360071, by rfl⟩ : syracuseStep 480095 = 720143) B720143
theorem B480107 : Blo 319836 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B578411 : Blo 319836 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B3724289 : Blo 319836 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B480335 : Blo 319836 480335 := bstep (se 1 (by rfl) ⟨360251, by rfl⟩ : syracuseStep 480335 = 720503) B720503
theorem B1627289 : Blo 319836 1627289 := bstep (se 2 (by rfl) ⟨610233, by rfl⟩ : syracuseStep 1627289 = 1220467) B1220467
theorem B480455 : Blo 319836 480455 := bstep (se 1 (by rfl) ⟨360341, by rfl⟩ : syracuseStep 480455 = 720683) B720683
theorem B546041 : Blo 319836 546041 := bstep (se 2 (by rfl) ⟨204765, by rfl⟩ : syracuseStep 546041 = 409531) B409531
theorem B480617 : Blo 319836 480617 := bstep (se 2 (by rfl) ⟨180231, by rfl⟩ : syracuseStep 480617 = 360463) B360463
theorem B546223 : Blo 319836 546223 := bstep (se 1 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 546223 = 819335) B819335
theorem B480695 : Blo 319836 480695 := bstep (se 1 (by rfl) ⟨360521, by rfl⟩ : syracuseStep 480695 = 721043) B721043
theorem B480731 : Blo 319836 480731 := bstep (se 1 (by rfl) ⟨360548, by rfl⟩ : syracuseStep 480731 = 721097) B721097
theorem B546311 : Blo 319836 546311 := bstep (se 1 (by rfl) ⟨409733, by rfl⟩ : syracuseStep 546311 = 819467) B819467
theorem B612011 : Blo 319836 612011 := bstep (se 1 (by rfl) ⟨459008, by rfl⟩ : syracuseStep 612011 = 918017) B918017
theorem B3659579 : Blo 319836 3659579 := bstep (se 1 (by rfl) ⟨2744684, by rfl⟩ : syracuseStep 3659579 = 5489369) B5489369
theorem B481199 : Blo 319836 481199 := bstep (se 1 (by rfl) ⟨360899, by rfl⟩ : syracuseStep 481199 = 721799) B721799
theorem B481289 : Blo 319836 481289 := bstep (se 2 (by rfl) ⟨180483, by rfl⟩ : syracuseStep 481289 = 360967) B360967
theorem B481319 : Blo 319836 481319 := bstep (se 1 (by rfl) ⟨360989, by rfl⟩ : syracuseStep 481319 = 721979) B721979
theorem B481403 : Blo 319836 481403 := bstep (se 1 (by rfl) ⟨361052, by rfl⟩ : syracuseStep 481403 = 722105) B722105
theorem B481529 : Blo 319836 481529 := bstep (se 2 (by rfl) ⟨180573, by rfl⟩ : syracuseStep 481529 = 361147) B361147
theorem B11163905 : Blo 319836 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B3496193 : Blo 319836 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B481631 : Blo 319836 481631 := bstep (se 1 (by rfl) ⟨361223, by rfl⟩ : syracuseStep 481631 = 722447) B722447
theorem B481643 : Blo 319836 481643 := bstep (se 1 (by rfl) ⟨361232, by rfl⟩ : syracuseStep 481643 = 722465) B722465
theorem B481871 : Blo 319836 481871 := bstep (se 1 (by rfl) ⟨361403, by rfl⟩ : syracuseStep 481871 = 722807) B722807
theorem B547451 : Blo 319836 547451 := bstep (se 1 (by rfl) ⟨410588, by rfl⟩ : syracuseStep 547451 = 821177) B821177
theorem B481991 : Blo 319836 481991 := bstep (se 1 (by rfl) ⟨361493, by rfl⟩ : syracuseStep 481991 = 722987) B722987
theorem B1366739 : Blo 319836 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B5299019 : Blo 319836 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B482153 : Blo 319836 482153 := bstep (se 2 (by rfl) ⟨180807, by rfl⟩ : syracuseStep 482153 = 361615) B361615
theorem B482231 : Blo 319836 482231 := bstep (se 1 (by rfl) ⟨361673, by rfl⟩ : syracuseStep 482231 = 723347) B723347
theorem B482267 : Blo 319836 482267 := bstep (se 1 (by rfl) ⟨361700, by rfl⟩ : syracuseStep 482267 = 723401) B723401
theorem B2055415 : Blo 319836 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B613727 : Blo 319836 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B482735 : Blo 319836 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B482825 : Blo 319836 482825 := bstep (se 2 (by rfl) ⟨181059, by rfl⟩ : syracuseStep 482825 = 362119) B362119
theorem B482855 : Blo 319836 482855 := bstep (se 1 (by rfl) ⟨362141, by rfl⟩ : syracuseStep 482855 = 724283) B724283
theorem B482939 : Blo 319836 482939 := bstep (se 1 (by rfl) ⟨362204, by rfl⟩ : syracuseStep 482939 = 724409) B724409
theorem B515783 : Blo 319836 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B2055901 : Blo 319836 2055901 := bstep (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) B770963
theorem B1302265 : Blo 319836 1302265 := bstep (se 2 (by rfl) ⟨488349, by rfl⟩ : syracuseStep 1302265 = 976699) B976699
theorem B483065 : Blo 319836 483065 := bstep (se 2 (by rfl) ⟨181149, by rfl⟩ : syracuseStep 483065 = 362299) B362299
theorem B614137 : Blo 319836 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B483167 : Blo 319836 483167 := bstep (se 1 (by rfl) ⟨362375, by rfl⟩ : syracuseStep 483167 = 724751) B724751
theorem B483179 : Blo 319836 483179 := bstep (se 1 (by rfl) ⟨362384, by rfl⟩ : syracuseStep 483179 = 724769) B724769
theorem B1105825 : Blo 319836 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B483407 : Blo 319836 483407 := bstep (se 1 (by rfl) ⟨362555, by rfl⟩ : syracuseStep 483407 = 725111) B725111
theorem B614479 : Blo 319836 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B483527 : Blo 319836 483527 := bstep (se 1 (by rfl) ⟨362645, by rfl⟩ : syracuseStep 483527 = 725291) B725291
theorem B2744549 : Blo 319836 2744549 := bstep (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) B514603
theorem B811255 : Blo 319836 811255 := bstep (se 1 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 811255 = 1216883) B1216883
theorem B614729 : Blo 319836 614729 := bstep (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) B461047
theorem B319839 : Blo 319836 319839 := bstep (se 1 (by rfl) ⟨239879, by rfl⟩ : syracuseStep 319839 = 479759) B479759
theorem B483689 : Blo 319836 483689 := bstep (se 2 (by rfl) ⟨181383, by rfl⟩ : syracuseStep 483689 = 362767) B362767
theorem B319867 : Blo 319836 319867 := bstep (se 1 (by rfl) ⟨239900, by rfl⟩ : syracuseStep 319867 = 479801) B479801
theorem B319919 : Blo 319836 319919 := bstep (se 1 (by rfl) ⟨239939, by rfl⟩ : syracuseStep 319919 = 479879) B479879
theorem B483767 : Blo 319836 483767 := bstep (se 1 (by rfl) ⟨362825, by rfl⟩ : syracuseStep 483767 = 725651) B725651
theorem B582071 : Blo 319836 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B516539 : Blo 319836 516539 := bstep (se 1 (by rfl) ⟨387404, by rfl⟩ : syracuseStep 516539 = 774809) B774809
theorem B319943 : Blo 319836 319943 := bstep (se 1 (by rfl) ⟨239957, by rfl⟩ : syracuseStep 319943 = 479915) B479915
theorem B319963 : Blo 319836 319963 := bstep (se 1 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 319963 = 479945) B479945
theorem B483803 : Blo 319836 483803 := bstep (se 1 (by rfl) ⟨362852, by rfl⟩ : syracuseStep 483803 = 725705) B725705
theorem B811529 : Blo 319836 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B975385 : Blo 319836 975385 := bstep (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) B731539
theorem B320039 : Blo 319836 320039 := bstep (se 1 (by rfl) ⟨240029, by rfl⟩ : syracuseStep 320039 = 480059) B480059
theorem B811559 : Blo 319836 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B3465787 : Blo 319836 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B320079 : Blo 319836 320079 := bstep (se 1 (by rfl) ⟨240059, by rfl⟩ : syracuseStep 320079 = 480119) B480119
theorem B320095 : Blo 319836 320095 := bstep (se 1 (by rfl) ⟨240071, by rfl⟩ : syracuseStep 320095 = 480143) B480143
theorem B320123 : Blo 319836 320123 := bstep (se 1 (by rfl) ⟨240092, by rfl⟩ : syracuseStep 320123 = 480185) B480185
theorem B320175 : Blo 319836 320175 := bstep (se 1 (by rfl) ⟨240131, by rfl⟩ : syracuseStep 320175 = 480263) B480263
theorem B320199 : Blo 319836 320199 := bstep (se 1 (by rfl) ⟨240149, by rfl⟩ : syracuseStep 320199 = 480299) B480299
theorem B320219 : Blo 319836 320219 := bstep (se 1 (by rfl) ⟨240164, by rfl⟩ : syracuseStep 320219 = 480329) B480329
theorem B320295 : Blo 319836 320295 := bstep (se 1 (by rfl) ⟨240221, by rfl⟩ : syracuseStep 320295 = 480443) B480443
theorem B320335 : Blo 319836 320335 := bstep (se 1 (by rfl) ⟨240251, by rfl⟩ : syracuseStep 320335 = 480503) B480503
theorem B320351 : Blo 319836 320351 := bstep (se 1 (by rfl) ⟨240263, by rfl⟩ : syracuseStep 320351 = 480527) B480527
theorem B811883 : Blo 319836 811883 := bstep (se 1 (by rfl) ⟨608912, by rfl⟩ : syracuseStep 811883 = 1217825) B1217825
theorem B320379 : Blo 319836 320379 := bstep (se 1 (by rfl) ⟨240284, by rfl⟩ : syracuseStep 320379 = 480569) B480569
theorem B320431 : Blo 319836 320431 := bstep (se 1 (by rfl) ⟨240323, by rfl⟩ : syracuseStep 320431 = 480647) B480647
theorem B484271 : Blo 319836 484271 := bstep (se 1 (by rfl) ⟨363203, by rfl⟩ : syracuseStep 484271 = 726407) B726407
theorem B517051 : Blo 319836 517051 := bstep (se 1 (by rfl) ⟨387788, by rfl⟩ : syracuseStep 517051 = 775577) B775577
theorem B320455 : Blo 319836 320455 := bstep (se 1 (by rfl) ⟨240341, by rfl⟩ : syracuseStep 320455 = 480683) B480683
theorem B320475 : Blo 319836 320475 := bstep (se 1 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 320475 = 480713) B480713
theorem B484361 : Blo 319836 484361 := bstep (se 2 (by rfl) ⟨181635, by rfl⟩ : syracuseStep 484361 = 363271) B363271
theorem B320551 : Blo 319836 320551 := bstep (se 1 (by rfl) ⟨240413, by rfl⟩ : syracuseStep 320551 = 480827) B480827
theorem B484391 : Blo 319836 484391 := bstep (se 1 (by rfl) ⟨363293, by rfl⟩ : syracuseStep 484391 = 726587) B726587
theorem B320591 : Blo 319836 320591 := bstep (se 1 (by rfl) ⟨240443, by rfl⟩ : syracuseStep 320591 = 480887) B480887
theorem B320607 : Blo 319836 320607 := bstep (se 1 (by rfl) ⟨240455, by rfl⟩ : syracuseStep 320607 = 480911) B480911
theorem B320635 : Blo 319836 320635 := bstep (se 1 (by rfl) ⟨240476, by rfl⟩ : syracuseStep 320635 = 480953) B480953
theorem B484475 : Blo 319836 484475 := bstep (se 1 (by rfl) ⟨363356, by rfl⟩ : syracuseStep 484475 = 726713) B726713
theorem B320687 : Blo 319836 320687 := bstep (se 1 (by rfl) ⟨240515, by rfl⟩ : syracuseStep 320687 = 481031) B481031
theorem B320711 : Blo 319836 320711 := bstep (se 1 (by rfl) ⟨240533, by rfl⟩ : syracuseStep 320711 = 481067) B481067
theorem B320731 : Blo 319836 320731 := bstep (se 1 (by rfl) ⟨240548, by rfl⟩ : syracuseStep 320731 = 481097) B481097
theorem B484601 : Blo 319836 484601 := bstep (se 2 (by rfl) ⟨181725, by rfl⟩ : syracuseStep 484601 = 363451) B363451
theorem B320807 : Blo 319836 320807 := bstep (se 1 (by rfl) ⟨240605, by rfl⟩ : syracuseStep 320807 = 481211) B481211
theorem B320847 : Blo 319836 320847 := bstep (se 1 (by rfl) ⟨240635, by rfl⟩ : syracuseStep 320847 = 481271) B481271
theorem B320863 : Blo 319836 320863 := bstep (se 1 (by rfl) ⟨240647, by rfl⟩ : syracuseStep 320863 = 481295) B481295
theorem B484703 : Blo 319836 484703 := bstep (se 1 (by rfl) ⟨363527, by rfl⟩ : syracuseStep 484703 = 727055) B727055
theorem B484715 : Blo 319836 484715 := bstep (se 1 (by rfl) ⟨363536, by rfl⟩ : syracuseStep 484715 = 727073) B727073
theorem B320891 : Blo 319836 320891 := bstep (se 1 (by rfl) ⟨240668, by rfl⟩ : syracuseStep 320891 = 481337) B481337
theorem B320943 : Blo 319836 320943 := bstep (se 1 (by rfl) ⟨240707, by rfl⟩ : syracuseStep 320943 = 481415) B481415
theorem B320967 : Blo 319836 320967 := bstep (se 1 (by rfl) ⟨240725, by rfl⟩ : syracuseStep 320967 = 481451) B481451
theorem B320987 : Blo 319836 320987 := bstep (se 1 (by rfl) ⟨240740, by rfl⟩ : syracuseStep 320987 = 481481) B481481
theorem B812531 : Blo 319836 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B321063 : Blo 319836 321063 := bstep (se 1 (by rfl) ⟨240797, by rfl⟩ : syracuseStep 321063 = 481595) B481595
theorem B321103 : Blo 319836 321103 := bstep (se 1 (by rfl) ⟨240827, by rfl⟩ : syracuseStep 321103 = 481655) B481655
theorem B484943 : Blo 319836 484943 := bstep (se 1 (by rfl) ⟨363707, by rfl⟩ : syracuseStep 484943 = 727415) B727415
theorem B321119 : Blo 319836 321119 := bstep (se 1 (by rfl) ⟨240839, by rfl⟩ : syracuseStep 321119 = 481679) B481679
theorem B321147 : Blo 319836 321147 := bstep (se 1 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 321147 = 481721) B481721
theorem B321199 : Blo 319836 321199 := bstep (se 1 (by rfl) ⟨240899, by rfl⟩ : syracuseStep 321199 = 481799) B481799
theorem B321223 : Blo 319836 321223 := bstep (se 1 (by rfl) ⟨240917, by rfl⟩ : syracuseStep 321223 = 481835) B481835
theorem B485063 : Blo 319836 485063 := bstep (se 1 (by rfl) ⟨363797, by rfl⟩ : syracuseStep 485063 = 727595) B727595
theorem B321243 : Blo 319836 321243 := bstep (se 1 (by rfl) ⟨240932, by rfl⟩ : syracuseStep 321243 = 481865) B481865
theorem B321319 : Blo 319836 321319 := bstep (se 1 (by rfl) ⟨240989, by rfl⟩ : syracuseStep 321319 = 481979) B481979
theorem B517961 : Blo 319836 517961 := bstep (se 2 (by rfl) ⟨194235, by rfl⟩ : syracuseStep 517961 = 388471) B388471
theorem B321359 : Blo 319836 321359 := bstep (se 1 (by rfl) ⟨241019, by rfl⟩ : syracuseStep 321359 = 482039) B482039
theorem B321375 : Blo 319836 321375 := bstep (se 1 (by rfl) ⟨241031, by rfl⟩ : syracuseStep 321375 = 482063) B482063
theorem B485225 : Blo 319836 485225 := bstep (se 2 (by rfl) ⟨181959, by rfl⟩ : syracuseStep 485225 = 363919) B363919
theorem B321403 : Blo 319836 321403 := bstep (se 1 (by rfl) ⟨241052, by rfl⟩ : syracuseStep 321403 = 482105) B482105
theorem B321455 : Blo 319836 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B485303 : Blo 319836 485303 := bstep (se 1 (by rfl) ⟨363977, by rfl⟩ : syracuseStep 485303 = 727955) B727955
theorem B812987 : Blo 319836 812987 := bstep (se 1 (by rfl) ⟨609740, by rfl⟩ : syracuseStep 812987 = 1219481) B1219481
theorem B3958721 : Blo 319836 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B321479 : Blo 319836 321479 := bstep (se 1 (by rfl) ⟨241109, by rfl⟩ : syracuseStep 321479 = 482219) B482219
theorem B321499 : Blo 319836 321499 := bstep (se 1 (by rfl) ⟨241124, by rfl⟩ : syracuseStep 321499 = 482249) B482249
theorem B485339 : Blo 319836 485339 := bstep (se 1 (by rfl) ⟨364004, by rfl⟩ : syracuseStep 485339 = 728009) B728009
theorem B321575 : Blo 319836 321575 := bstep (se 1 (by rfl) ⟨241181, by rfl⟩ : syracuseStep 321575 = 482363) B482363
theorem B321615 : Blo 319836 321615 := bstep (se 1 (by rfl) ⟨241211, by rfl⟩ : syracuseStep 321615 = 482423) B482423
theorem B321631 : Blo 319836 321631 := bstep (se 1 (by rfl) ⟨241223, by rfl⟩ : syracuseStep 321631 = 482447) B482447
theorem B321659 : Blo 319836 321659 := bstep (se 1 (by rfl) ⟨241244, by rfl⟩ : syracuseStep 321659 = 482489) B482489
theorem B11954309 : Blo 319836 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B321711 : Blo 319836 321711 := bstep (se 1 (by rfl) ⟨241283, by rfl⟩ : syracuseStep 321711 = 482567) B482567
theorem B321735 : Blo 319836 321735 := bstep (se 1 (by rfl) ⟨241301, by rfl⟩ : syracuseStep 321735 = 482603) B482603
theorem B321755 : Blo 319836 321755 := bstep (se 1 (by rfl) ⟨241316, by rfl⟩ : syracuseStep 321755 = 482633) B482633
theorem B68512013 : Blo 319836 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B321831 : Blo 319836 321831 := bstep (se 1 (by rfl) ⟨241373, by rfl⟩ : syracuseStep 321831 = 482747) B482747
theorem B1370429 : Blo 319836 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B321871 : Blo 319836 321871 := bstep (se 1 (by rfl) ⟨241403, by rfl⟩ : syracuseStep 321871 = 482807) B482807
theorem B321887 : Blo 319836 321887 := bstep (se 1 (by rfl) ⟨241415, by rfl⟩ : syracuseStep 321887 = 482831) B482831
theorem B321915 : Blo 319836 321915 := bstep (se 1 (by rfl) ⟨241436, by rfl⟩ : syracuseStep 321915 = 482873) B482873
theorem B321967 : Blo 319836 321967 := bstep (se 1 (by rfl) ⟨241475, by rfl⟩ : syracuseStep 321967 = 482951) B482951
theorem B321991 : Blo 319836 321991 := bstep (se 1 (by rfl) ⟨241493, by rfl⟩ : syracuseStep 321991 = 482987) B482987
theorem B322011 : Blo 319836 322011 := bstep (se 1 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 322011 = 483017) B483017
theorem B911911 : Blo 319836 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B322087 : Blo 319836 322087 := bstep (se 1 (by rfl) ⟨241565, by rfl⟩ : syracuseStep 322087 = 483131) B483131
theorem B322127 : Blo 319836 322127 := bstep (se 1 (by rfl) ⟨241595, by rfl⟩ : syracuseStep 322127 = 483191) B483191
theorem B322143 : Blo 319836 322143 := bstep (se 1 (by rfl) ⟨241607, by rfl⟩ : syracuseStep 322143 = 483215) B483215
theorem B911969 : Blo 319836 911969 := bstep (se 2 (by rfl) ⟨341988, by rfl⟩ : syracuseStep 911969 = 683977) B683977
theorem B813665 : Blo 319836 813665 := bstep (se 2 (by rfl) ⟨305124, by rfl⟩ : syracuseStep 813665 = 610249) B610249
theorem B322171 : Blo 319836 322171 := bstep (se 1 (by rfl) ⟨241628, by rfl⟩ : syracuseStep 322171 = 483257) B483257
theorem B322223 : Blo 319836 322223 := bstep (se 1 (by rfl) ⟨241667, by rfl⟩ : syracuseStep 322223 = 483335) B483335
theorem B322247 : Blo 319836 322247 := bstep (se 1 (by rfl) ⟨241685, by rfl⟩ : syracuseStep 322247 = 483371) B483371
theorem B322267 : Blo 319836 322267 := bstep (se 1 (by rfl) ⟨241700, by rfl⟩ : syracuseStep 322267 = 483401) B483401
theorem B322343 : Blo 319836 322343 := bstep (se 1 (by rfl) ⟨241757, by rfl⟩ : syracuseStep 322343 = 483515) B483515
theorem B322383 : Blo 319836 322383 := bstep (se 1 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 322383 = 483575) B483575
theorem B322399 : Blo 319836 322399 := bstep (se 1 (by rfl) ⟨241799, by rfl⟩ : syracuseStep 322399 = 483599) B483599
theorem B322427 : Blo 319836 322427 := bstep (se 1 (by rfl) ⟨241820, by rfl⟩ : syracuseStep 322427 = 483641) B483641
theorem B486319 : Blo 319836 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B322479 : Blo 319836 322479 := bstep (se 1 (by rfl) ⟨241859, by rfl⟩ : syracuseStep 322479 = 483719) B483719
theorem B322503 : Blo 319836 322503 := bstep (se 1 (by rfl) ⟨241877, by rfl⟩ : syracuseStep 322503 = 483755) B483755
theorem B322523 : Blo 319836 322523 := bstep (se 1 (by rfl) ⟨241892, by rfl⟩ : syracuseStep 322523 = 483785) B483785
theorem B322599 : Blo 319836 322599 := bstep (se 1 (by rfl) ⟨241949, by rfl⟩ : syracuseStep 322599 = 483899) B483899
theorem B322639 : Blo 319836 322639 := bstep (se 1 (by rfl) ⟨241979, by rfl⟩ : syracuseStep 322639 = 483959) B483959
theorem B322655 : Blo 319836 322655 := bstep (se 1 (by rfl) ⟨241991, by rfl⟩ : syracuseStep 322655 = 483983) B483983
theorem B322683 : Blo 319836 322683 := bstep (se 1 (by rfl) ⟨242012, by rfl⟩ : syracuseStep 322683 = 484025) B484025
theorem B322735 : Blo 319836 322735 := bstep (se 1 (by rfl) ⟨242051, by rfl⟩ : syracuseStep 322735 = 484103) B484103
theorem B3501251 : Blo 319836 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B322759 : Blo 319836 322759 := bstep (se 1 (by rfl) ⟨242069, by rfl⟩ : syracuseStep 322759 = 484139) B484139
theorem B322779 : Blo 319836 322779 := bstep (se 1 (by rfl) ⟨242084, by rfl⟩ : syracuseStep 322779 = 484169) B484169
theorem B322855 : Blo 319836 322855 := bstep (se 1 (by rfl) ⟨242141, by rfl⟩ : syracuseStep 322855 = 484283) B484283
theorem B322895 : Blo 319836 322895 := bstep (se 1 (by rfl) ⟨242171, by rfl⟩ : syracuseStep 322895 = 484343) B484343
theorem B322911 : Blo 319836 322911 := bstep (se 1 (by rfl) ⟨242183, by rfl⟩ : syracuseStep 322911 = 484367) B484367
theorem B22310261 : Blo 319836 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B322939 : Blo 319836 322939 := bstep (se 1 (by rfl) ⟨242204, by rfl⟩ : syracuseStep 322939 = 484409) B484409
theorem B322991 : Blo 319836 322991 := bstep (se 1 (by rfl) ⟨242243, by rfl⟩ : syracuseStep 322991 = 484487) B484487
theorem B323015 : Blo 319836 323015 := bstep (se 1 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 323015 = 484523) B484523
theorem B323035 : Blo 319836 323035 := bstep (se 1 (by rfl) ⟨242276, by rfl⟩ : syracuseStep 323035 = 484553) B484553
theorem B1306145 : Blo 319836 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B323111 : Blo 319836 323111 := bstep (se 1 (by rfl) ⟨242333, by rfl⟩ : syracuseStep 323111 = 484667) B484667
theorem B323151 : Blo 319836 323151 := bstep (se 1 (by rfl) ⟨242363, by rfl⟩ : syracuseStep 323151 = 484727) B484727
theorem B323167 : Blo 319836 323167 := bstep (se 1 (by rfl) ⟨242375, by rfl⟩ : syracuseStep 323167 = 484751) B484751
theorem B323195 : Blo 319836 323195 := bstep (se 1 (by rfl) ⟨242396, by rfl⟩ : syracuseStep 323195 = 484793) B484793
theorem B1633931 : Blo 319836 1633931 := bstep (se 1 (by rfl) ⟨1225448, by rfl⟩ : syracuseStep 1633931 = 2450897) B2450897
theorem B323247 : Blo 319836 323247 := bstep (se 1 (by rfl) ⟨242435, by rfl⟩ : syracuseStep 323247 = 484871) B484871
theorem B1961671 : Blo 319836 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B323271 : Blo 319836 323271 := bstep (se 1 (by rfl) ⟨242453, by rfl⟩ : syracuseStep 323271 = 484907) B484907
theorem B323291 : Blo 319836 323291 := bstep (se 1 (by rfl) ⟨242468, by rfl⟩ : syracuseStep 323291 = 484937) B484937
theorem B323367 : Blo 319836 323367 := bstep (se 1 (by rfl) ⟨242525, by rfl⟩ : syracuseStep 323367 = 485051) B485051
theorem B323407 : Blo 319836 323407 := bstep (se 1 (by rfl) ⟨242555, by rfl⟩ : syracuseStep 323407 = 485111) B485111
theorem B323423 : Blo 319836 323423 := bstep (se 1 (by rfl) ⟨242567, by rfl⟩ : syracuseStep 323423 = 485135) B485135
theorem B323451 : Blo 319836 323451 := bstep (se 1 (by rfl) ⟨242588, by rfl⟩ : syracuseStep 323451 = 485177) B485177
theorem B323503 : Blo 319836 323503 := bstep (se 1 (by rfl) ⟨242627, by rfl⟩ : syracuseStep 323503 = 485255) B485255
theorem B323527 : Blo 319836 323527 := bstep (se 1 (by rfl) ⟨242645, by rfl⟩ : syracuseStep 323527 = 485291) B485291
theorem B323547 : Blo 319836 323547 := bstep (se 1 (by rfl) ⟨242660, by rfl⟩ : syracuseStep 323547 = 485321) B485321
theorem B913427 : Blo 319836 913427 := bstep (se 1 (by rfl) ⟨685070, by rfl⟩ : syracuseStep 913427 = 1370141) B1370141
theorem B815123 : Blo 319836 815123 := bstep (se 1 (by rfl) ⟨611342, by rfl⟩ : syracuseStep 815123 = 1222685) B1222685
theorem B323623 : Blo 319836 323623 := bstep (se 1 (by rfl) ⟨242717, by rfl⟩ : syracuseStep 323623 = 485435) B485435
theorem B323663 : Blo 319836 323663 := bstep (se 1 (by rfl) ⟨242747, by rfl⟩ : syracuseStep 323663 = 485495) B485495
theorem B1372241 : Blo 319836 1372241 := bstep (se 2 (by rfl) ⟨514590, by rfl⟩ : syracuseStep 1372241 = 1029181) B1029181
theorem B323679 : Blo 319836 323679 := bstep (se 1 (by rfl) ⟨242759, by rfl⟩ : syracuseStep 323679 = 485519) B485519
theorem B323707 : Blo 319836 323707 := bstep (se 1 (by rfl) ⟨242780, by rfl⟩ : syracuseStep 323707 = 485561) B485561
theorem B323759 : Blo 319836 323759 := bstep (se 1 (by rfl) ⟨242819, by rfl⟩ : syracuseStep 323759 = 485639) B485639
theorem B323783 : Blo 319836 323783 := bstep (se 1 (by rfl) ⟨242837, by rfl⟩ : syracuseStep 323783 = 485675) B485675
theorem B323803 : Blo 319836 323803 := bstep (se 1 (by rfl) ⟨242852, by rfl⟩ : syracuseStep 323803 = 485705) B485705
theorem B2322749 : Blo 319836 2322749 := bstep (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) B871031
theorem B2060747 : Blo 319836 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B815579 : Blo 319836 815579 := bstep (se 1 (by rfl) ⟨611684, by rfl⟩ : syracuseStep 815579 = 1223369) B1223369
theorem B4452889 : Blo 319836 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B1864225 : Blo 319836 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B11760389 : Blo 319836 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B783881 : Blo 319836 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B816763 : Blo 319836 816763 := bstep (se 1 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 816763 = 1225145) B1225145
theorem B3077777 : Blo 319836 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B6944717 : Blo 319836 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B4618397 : Blo 319836 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B916217 : Blo 319836 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B1080107 : Blo 319836 1080107 := bstep (se 1 (by rfl) ⟨810080, by rfl⟩ : syracuseStep 1080107 = 1620161) B1620161
theorem B719711 : Blo 319836 719711 := bstep (se 1 (by rfl) ⟨539783, by rfl⟩ : syracuseStep 719711 = 1079567) B1079567
theorem B457579 : Blo 319836 457579 := bstep (se 1 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 457579 = 686369) B686369
theorem B2063333 : Blo 319836 2063333 := bstep (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) B386875
theorem B719891 : Blo 319836 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B1080377 : Blo 319836 1080377 := bstep (se 2 (by rfl) ⟨405141, by rfl⟩ : syracuseStep 1080377 = 810283) B810283
theorem B457807 : Blo 319836 457807 := bstep (se 1 (by rfl) ⟨343355, by rfl⟩ : syracuseStep 457807 = 686711) B686711
theorem B916559 : Blo 319836 916559 := bstep (se 1 (by rfl) ⟨687419, by rfl⟩ : syracuseStep 916559 = 1374839) B1374839
theorem B2456729 : Blo 319836 2456729 := bstep (se 2 (by rfl) ⟨921273, by rfl⟩ : syracuseStep 2456729 = 1842547) B1842547
theorem B720233 : Blo 319836 720233 := bstep (se 2 (by rfl) ⟨270087, by rfl⟩ : syracuseStep 720233 = 540175) B540175
theorem B1080701 : Blo 319836 1080701 := bstep (se 3 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 1080701 = 405263) B405263
theorem B4619663 : Blo 319836 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B7044569 : Blo 319836 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B1080971 : Blo 319836 1080971 := bstep (se 1 (by rfl) ⟨810728, by rfl⟩ : syracuseStep 1080971 = 1621457) B1621457
theorem B1638305 : Blo 319836 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B720827 : Blo 319836 720827 := bstep (se 1 (by rfl) ⟨540620, by rfl⟩ : syracuseStep 720827 = 1081241) B1081241
theorem B1081403 : Blo 319836 1081403 := bstep (se 1 (by rfl) ⟨811052, by rfl⟩ : syracuseStep 1081403 = 1622105) B1622105
theorem B819305 : Blo 319836 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B1081673 : Blo 319836 1081673 := bstep (se 2 (by rfl) ⟨405627, by rfl⟩ : syracuseStep 1081673 = 811255) B811255
theorem B721259 : Blo 319836 721259 := bstep (se 1 (by rfl) ⟨540944, by rfl⟩ : syracuseStep 721259 = 1081889) B1081889
theorem B688495 : Blo 319836 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B721403 : Blo 319836 721403 := bstep (se 1 (by rfl) ⟨541052, by rfl⟩ : syracuseStep 721403 = 1082105) B1082105
theorem B328255 : Blo 319836 328255 := bstep (se 1 (by rfl) ⟨246191, by rfl⟩ : syracuseStep 328255 = 492383) B492383
theorem B721529 : Blo 319836 721529 := bstep (se 2 (by rfl) ⟨270573, by rfl⟩ : syracuseStep 721529 = 541147) B541147
theorem B721583 : Blo 319836 721583 := bstep (se 1 (by rfl) ⟨541187, by rfl⟩ : syracuseStep 721583 = 1082375) B1082375
theorem B1639115 : Blo 319836 1639115 := bstep (se 1 (by rfl) ⟨1229336, by rfl⟩ : syracuseStep 1639115 = 2458673) B2458673
theorem B361183 : Blo 319836 361183 := bstep (se 1 (by rfl) ⟨270887, by rfl⟩ : syracuseStep 361183 = 541775) B541775
theorem B721655 : Blo 319836 721655 := bstep (se 1 (by rfl) ⟨541241, by rfl⟩ : syracuseStep 721655 = 1082483) B1082483
theorem B4621049 : Blo 319836 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B1639277 : Blo 319836 1639277 := bstep (se 3 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 1639277 = 614729) B614729
theorem B721835 : Blo 319836 721835 := bstep (se 1 (by rfl) ⟨541376, by rfl⟩ : syracuseStep 721835 = 1082753) B1082753
theorem B689401 : Blo 319836 689401 := bstep (se 2 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 689401 = 517051) B517051
theorem B361759 : Blo 319836 361759 := bstep (se 1 (by rfl) ⟨271319, by rfl⟩ : syracuseStep 361759 = 542639) B542639
theorem B1049951 : Blo 319836 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B886153 : Blo 319836 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B722375 : Blo 319836 722375 := bstep (se 1 (by rfl) ⟨541781, by rfl⟩ : syracuseStep 722375 = 1083563) B1083563
theorem B362047 : Blo 319836 362047 := bstep (se 1 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 362047 = 543071) B543071
theorem B460523 : Blo 319836 460523 := bstep (se 1 (by rfl) ⟨345392, by rfl⟩ : syracuseStep 460523 = 690785) B690785
theorem B11142947 : Blo 319836 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B722735 : Blo 319836 722735 := bstep (se 1 (by rfl) ⟨542051, by rfl⟩ : syracuseStep 722735 = 1084103) B1084103
theorem B1378255 : Blo 319836 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B1837241 : Blo 319836 1837241 := bstep (se 2 (by rfl) ⟨688965, by rfl⟩ : syracuseStep 1837241 = 1377931) B1377931
theorem B723311 : Blo 319836 723311 := bstep (se 1 (by rfl) ⟨542483, by rfl⟩ : syracuseStep 723311 = 1084967) B1084967
theorem B362875 : Blo 319836 362875 := bstep (se 1 (by rfl) ⟨272156, by rfl⟩ : syracuseStep 362875 = 544313) B544313
theorem B2984359 : Blo 319836 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B723383 : Blo 319836 723383 := bstep (se 1 (by rfl) ⟨542537, by rfl⟩ : syracuseStep 723383 = 1085075) B1085075
theorem B723527 : Blo 319836 723527 := bstep (se 1 (by rfl) ⟨542645, by rfl⟩ : syracuseStep 723527 = 1085291) B1085291
theorem B1378889 : Blo 319836 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B723563 : Blo 319836 723563 := bstep (se 1 (by rfl) ⟨542672, by rfl⟩ : syracuseStep 723563 = 1085345) B1085345
theorem B363343 : Blo 319836 363343 := bstep (se 1 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 363343 = 545015) B545015
theorem B723959 : Blo 319836 723959 := bstep (se 1 (by rfl) ⟨542969, by rfl⟩ : syracuseStep 723959 = 1085939) B1085939
theorem B363739 : Blo 319836 363739 := bstep (se 1 (by rfl) ⟨272804, by rfl⟩ : syracuseStep 363739 = 545609) B545609
theorem B724319 : Blo 319836 724319 := bstep (se 1 (by rfl) ⟨543239, by rfl⟩ : syracuseStep 724319 = 1086479) B1086479
theorem B1215881 : Blo 319836 1215881 := bstep (se 2 (by rfl) ⟨455955, by rfl⟩ : syracuseStep 1215881 = 911911) B911911
theorem B1084859 : Blo 319836 1084859 := bstep (se 1 (by rfl) ⟨813644, by rfl⟩ : syracuseStep 1084859 = 1627289) B1627289
theorem B364027 : Blo 319836 364027 := bstep (se 1 (by rfl) ⟨273020, by rfl⟩ : syracuseStep 364027 = 546041) B546041
theorem B364207 : Blo 319836 364207 := bstep (se 1 (by rfl) ⟨273155, by rfl⟩ : syracuseStep 364207 = 546311) B546311
theorem B724715 : Blo 319836 724715 := bstep (se 1 (by rfl) ⟨543536, by rfl⟩ : syracuseStep 724715 = 1087073) B1087073
theorem B724841 : Blo 319836 724841 := bstep (se 2 (by rfl) ⟨271815, by rfl⟩ : syracuseStep 724841 = 543631) B543631
theorem B1380203 : Blo 319836 1380203 := bstep (se 1 (by rfl) ⟨1035152, by rfl⟩ : syracuseStep 1380203 = 2070305) B2070305
theorem B2756713 : Blo 319836 2756713 := bstep (se 2 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 2756713 = 2067535) B2067535
theorem B7442603 : Blo 319836 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B2330795 : Blo 319836 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B364967 : Blo 319836 364967 := bstep (se 1 (by rfl) ⟨273725, by rfl⟩ : syracuseStep 364967 = 547451) B547451
theorem B1511905 : Blo 319836 1511905 := bstep (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) B1133929
theorem B725687 : Blo 319836 725687 := bstep (se 1 (by rfl) ⟨544265, by rfl⟩ : syracuseStep 725687 = 1088531) B1088531
theorem B332591 : Blo 319836 332591 := bstep (se 1 (by rfl) ⟨249443, by rfl⟩ : syracuseStep 332591 = 498887) B498887
theorem B725903 : Blo 319836 725903 := bstep (se 1 (by rfl) ⟨544427, by rfl⟩ : syracuseStep 725903 = 1088855) B1088855
theorem B2758049 : Blo 319836 2758049 := bstep (se 2 (by rfl) ⟨1034268, by rfl⟩ : syracuseStep 2758049 = 2068537) B2068537
theorem B726623 : Blo 319836 726623 := bstep (se 1 (by rfl) ⟨544967, by rfl⟩ : syracuseStep 726623 = 1089935) B1089935
theorem B726839 : Blo 319836 726839 := bstep (se 1 (by rfl) ⟨545129, by rfl⟩ : syracuseStep 726839 = 1090259) B1090259
theorem B5937185 : Blo 319836 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B727145 : Blo 319836 727145 := bstep (se 2 (by rfl) ⟨272679, by rfl⟩ : syracuseStep 727145 = 545359) B545359
theorem B727631 : Blo 319836 727631 := bstep (se 1 (by rfl) ⟨545723, by rfl⟩ : syracuseStep 727631 = 1091447) B1091447
theorem B727775 : Blo 319836 727775 := bstep (se 1 (by rfl) ⟨545831, by rfl⟩ : syracuseStep 727775 = 1091663) B1091663
theorem B728027 : Blo 319836 728027 := bstep (se 1 (by rfl) ⟨546020, by rfl⟩ : syracuseStep 728027 = 1092041) B1092041
theorem B728207 : Blo 319836 728207 := bstep (se 1 (by rfl) ⟨546155, by rfl⟩ : syracuseStep 728207 = 1092311) B1092311
theorem B1842365 : Blo 319836 1842365 := bstep (se 3 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 1842365 = 690887) B690887
theorem B728297 : Blo 319836 728297 := bstep (se 2 (by rfl) ⟨273111, by rfl⟩ : syracuseStep 728297 = 546223) B546223
theorem B728351 : Blo 319836 728351 := bstep (se 1 (by rfl) ⟨546263, by rfl⟩ : syracuseStep 728351 = 1092527) B1092527
theorem B2334167 : Blo 319836 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B1089017 : Blo 319836 1089017 := bstep (se 2 (by rfl) ⟨408381, by rfl⟩ : syracuseStep 1089017 = 816763) B816763
theorem B4169465 : Blo 319836 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B1089287 : Blo 319836 1089287 := bstep (se 1 (by rfl) ⟨816965, by rfl⟩ : syracuseStep 1089287 = 1633931) B1633931
theorem B1089341 : Blo 319836 1089341 := bstep (se 3 (by rfl) ⟨204251, by rfl⟩ : syracuseStep 1089341 = 408503) B408503
theorem B1843073 : Blo 319836 1843073 := bstep (se 2 (by rfl) ⟨691152, by rfl⟩ : syracuseStep 1843073 = 1382305) B1382305
theorem B1548499 : Blo 319836 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B7840259 : Blo 319836 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B2761361 : Blo 319836 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B2433887 : Blo 319836 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B4629811 : Blo 319836 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B1549729 : Blo 319836 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B2205949 : Blo 319836 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B4696379 : Blo 319836 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B1092203 : Blo 319836 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B2435831 : Blo 319836 2435831 := bstep (se 1 (by rfl) ⟨1826873, by rfl⟩ : syracuseStep 2435831 = 3653747) B3653747
theorem B1223869 : Blo 319836 1223869 := bstep (se 3 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 1223869 = 458951) B458951
theorem B1092797 : Blo 319836 1092797 := bstep (se 3 (by rfl) ⟨204899, by rfl⟩ : syracuseStep 1092797 = 409799) B409799
theorem B5024987 : Blo 319836 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B6204761 : Blo 319836 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B1159069 : Blo 319836 1159069 := bstep (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) B434651
theorem B3092539 : Blo 319836 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B2733203 : Blo 319836 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B865495 : Blo 319836 865495 := bstep (se 1 (by rfl) ⟨649121, by rfl⟩ : syracuseStep 865495 = 1298243) B1298243
theorem B1553651 : Blo 319836 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B407035 : Blo 319836 407035 := bstep (se 1 (by rfl) ⟨305276, by rfl⟩ : syracuseStep 407035 = 610553) B610553
theorem B1619513 : Blo 319836 1619513 := bstep (se 2 (by rfl) ⟨607317, by rfl⟩ : syracuseStep 1619513 = 1214635) B1214635
theorem B407263 : Blo 319836 407263 := bstep (se 1 (by rfl) ⟨305447, by rfl⟩ : syracuseStep 407263 = 610895) B610895
theorem B3192605 : Blo 319836 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B1226785 : Blo 319836 1226785 := bstep (se 2 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 1226785 = 920089) B920089
theorem B408007 : Blo 319836 408007 := bstep (se 1 (by rfl) ⟨306005, by rfl⟩ : syracuseStep 408007 = 612011) B612011
theorem B2439719 : Blo 319836 2439719 := bstep (se 1 (by rfl) ⟨1829789, by rfl⟩ : syracuseStep 2439719 = 3659579) B3659579
theorem B3357317 : Blo 319836 3357317 := bstep (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) B629497
theorem B2472643 : Blo 319836 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B1948535 : Blo 319836 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B6208757 : Blo 319836 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B5946659 : Blo 319836 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B409151 : Blo 319836 409151 := bstep (se 1 (by rfl) ⟨306863, by rfl⟩ : syracuseStep 409151 = 613727) B613727
theorem B1621619 : Blo 319836 1621619 := bstep (se 1 (by rfl) ⟨1216214, by rfl⟩ : syracuseStep 1621619 = 2432429) B2432429
theorem B343855 : Blo 319836 343855 := bstep (se 1 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 343855 = 515783) B515783
theorem B2736179 : Blo 319836 2736179 := bstep (se 1 (by rfl) ⟨2052134, by rfl⟩ : syracuseStep 2736179 = 4104269) B4104269
theorem B344359 : Blo 319836 344359 := bstep (se 1 (by rfl) ⟨258269, by rfl⟩ : syracuseStep 344359 = 516539) B516539
theorem B541019 : Blo 319836 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B541039 : Blo 319836 541039 := bstep (se 1 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 541039 = 811559) B811559
theorem B2605537 : Blo 319836 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B541255 : Blo 319836 541255 := bstep (se 1 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 541255 = 811883) B811883
theorem B441762497 : Blo 319836 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B541687 : Blo 319836 541687 := bstep (se 1 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 541687 = 812531) B812531
theorem B1623239 : Blo 319836 1623239 := bstep (se 1 (by rfl) ⟨1217429, by rfl⟩ : syracuseStep 1623239 = 2434859) B2434859
theorem B345307 : Blo 319836 345307 := bstep (se 1 (by rfl) ⟨258980, by rfl⟩ : syracuseStep 345307 = 517961) B517961
theorem B541991 : Blo 319836 541991 := bstep (se 1 (by rfl) ⟨406493, by rfl⟩ : syracuseStep 541991 = 812987) B812987
theorem B2639147 : Blo 319836 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B1623401 : Blo 319836 1623401 := bstep (se 2 (by rfl) ⟨608775, by rfl⟩ : syracuseStep 1623401 = 1217551) B1217551
theorem B607979 : Blo 319836 607979 := bstep (se 1 (by rfl) ⟨455984, by rfl⟩ : syracuseStep 607979 = 911969) B911969
theorem B542443 : Blo 319836 542443 := bstep (se 1 (by rfl) ⟨406832, by rfl⟩ : syracuseStep 542443 = 813665) B813665
theorem B509743 : Blo 319836 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B870763 : Blo 319836 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B608951 : Blo 319836 608951 := bstep (se 1 (by rfl) ⟨456713, by rfl⟩ : syracuseStep 608951 = 913427) B913427
theorem B543415 : Blo 319836 543415 := bstep (se 1 (by rfl) ⟨407561, by rfl⟩ : syracuseStep 543415 = 815123) B815123
theorem B543719 : Blo 319836 543719 := bstep (se 1 (by rfl) ⟨407789, by rfl⟩ : syracuseStep 543719 = 815579) B815579
theorem B1560323 : Blo 319836 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B2051851 : Blo 319836 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B13881131 : Blo 319836 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B610105 : Blo 319836 610105 := bstep (se 2 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 610105 = 457579) B457579
theorem B610409 : Blo 319836 610409 := bstep (se 2 (by rfl) ⟨228903, by rfl⟩ : syracuseStep 610409 = 457807) B457807
theorem B544873 : Blo 319836 544873 := bstep (se 2 (by rfl) ⟨204327, by rfl⟩ : syracuseStep 544873 = 408655) B408655
theorem B2740553 : Blo 319836 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B610811 : Blo 319836 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B479807 : Blo 319836 479807 := bstep (se 1 (by rfl) ⟨359855, by rfl⟩ : syracuseStep 479807 = 719711) B719711
theorem B1036871 : Blo 319836 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B11686517 : Blo 319836 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B479927 : Blo 319836 479927 := bstep (se 1 (by rfl) ⟨359945, by rfl⟩ : syracuseStep 479927 = 719891) B719891
theorem B611039 : Blo 319836 611039 := bstep (se 1 (by rfl) ⟨458279, by rfl⟩ : syracuseStep 611039 = 916559) B916559
theorem B578323 : Blo 319836 578323 := bstep (se 1 (by rfl) ⟨433742, by rfl⟩ : syracuseStep 578323 = 867485) B867485
theorem B480155 : Blo 319836 480155 := bstep (se 1 (by rfl) ⟨360116, by rfl⟩ : syracuseStep 480155 = 720233) B720233
theorem B2741201 : Blo 319836 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B1627127 : Blo 319836 1627127 := bstep (se 1 (by rfl) ⟨1220345, by rfl⟩ : syracuseStep 1627127 = 2440691) B2440691
theorem B1299655 : Blo 319836 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B480551 : Blo 319836 480551 := bstep (se 1 (by rfl) ⟨360413, by rfl⟩ : syracuseStep 480551 = 720827) B720827
theorem B480635 : Blo 319836 480635 := bstep (se 1 (by rfl) ⟨360476, by rfl⟩ : syracuseStep 480635 = 720953) B720953
theorem B611707 : Blo 319836 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B611783 : Blo 319836 611783 := bstep (se 1 (by rfl) ⟨458837, by rfl⟩ : syracuseStep 611783 = 917675) B917675
theorem B480761 : Blo 319836 480761 := bstep (se 2 (by rfl) ⟨180285, by rfl⟩ : syracuseStep 480761 = 360571) B360571
theorem B480863 : Blo 319836 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B481079 : Blo 319836 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B10639163 : Blo 319836 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B481385 : Blo 319836 481385 := bstep (se 2 (by rfl) ⟨180519, by rfl⟩ : syracuseStep 481385 = 361039) B361039
theorem B2447495 : Blo 319836 2447495 := bstep (se 1 (by rfl) ⟨1835621, by rfl⟩ : syracuseStep 2447495 = 3671243) B3671243
theorem B1956221 : Blo 319836 1956221 := bstep (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) B733583
theorem B1464743 : Blo 319836 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B481703 : Blo 319836 481703 := bstep (se 1 (by rfl) ⟨361277, by rfl⟩ : syracuseStep 481703 = 722555) B722555
theorem B481787 : Blo 319836 481787 := bstep (se 1 (by rfl) ⟨361340, by rfl⟩ : syracuseStep 481787 = 722681) B722681
theorem B580169 : Blo 319836 580169 := bstep (se 2 (by rfl) ⟨217563, by rfl⟩ : syracuseStep 580169 = 435127) B435127
theorem B612937 : Blo 319836 612937 := bstep (se 2 (by rfl) ⟨229851, by rfl⟩ : syracuseStep 612937 = 459703) B459703
theorem B481913 : Blo 319836 481913 := bstep (se 2 (by rfl) ⟨180717, by rfl⟩ : syracuseStep 481913 = 361435) B361435
theorem B481967 : Blo 319836 481967 := bstep (se 1 (by rfl) ⟨361475, by rfl⟩ : syracuseStep 481967 = 722951) B722951
theorem B482015 : Blo 319836 482015 := bstep (se 1 (by rfl) ⟨361511, by rfl⟩ : syracuseStep 482015 = 723023) B723023
theorem B809747 : Blo 319836 809747 := bstep (se 1 (by rfl) ⟨607310, by rfl⟩ : syracuseStep 809747 = 1214621) B1214621
theorem B1629071 : Blo 319836 1629071 := bstep (se 1 (by rfl) ⟨1221803, by rfl⟩ : syracuseStep 1629071 = 2443607) B2443607
theorem B809959 : Blo 319836 809959 := bstep (se 1 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 809959 = 1214939) B1214939
theorem B482279 : Blo 319836 482279 := bstep (se 1 (by rfl) ⟨361709, by rfl⟩ : syracuseStep 482279 = 723419) B723419
theorem B1105085 : Blo 319836 1105085 := bstep (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) B414407
theorem B482537 : Blo 319836 482537 := bstep (se 2 (by rfl) ⟨180951, by rfl⟩ : syracuseStep 482537 = 361903) B361903
theorem B810233 : Blo 319836 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B482591 : Blo 319836 482591 := bstep (se 1 (by rfl) ⟨361943, by rfl⟩ : syracuseStep 482591 = 723887) B723887
theorem B777595 : Blo 319836 777595 := bstep (se 1 (by rfl) ⟨583196, by rfl⟩ : syracuseStep 777595 = 1166393) B1166393
theorem B482759 : Blo 319836 482759 := bstep (se 1 (by rfl) ⟨362069, by rfl⟩ : syracuseStep 482759 = 724139) B724139
theorem B483113 : Blo 319836 483113 := bstep (se 2 (by rfl) ⟨181167, by rfl⟩ : syracuseStep 483113 = 362335) B362335
theorem B483119 : Blo 319836 483119 := bstep (se 1 (by rfl) ⟨362339, by rfl⟩ : syracuseStep 483119 = 724679) B724679
theorem B581431 : Blo 319836 581431 := bstep (se 1 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 581431 = 872147) B872147
theorem B810881 : Blo 319836 810881 := bstep (se 2 (by rfl) ⟨304080, by rfl⟩ : syracuseStep 810881 = 608161) B608161
theorem B5202053 : Blo 319836 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B483593 : Blo 319836 483593 := bstep (se 2 (by rfl) ⟨181347, by rfl⟩ : syracuseStep 483593 = 362695) B362695
theorem B319855 : Blo 319836 319855 := bstep (se 1 (by rfl) ⟨239891, by rfl⟩ : syracuseStep 319855 = 479783) B479783
theorem B483695 : Blo 319836 483695 := bstep (se 1 (by rfl) ⟨362771, by rfl⟩ : syracuseStep 483695 = 725543) B725543
theorem B319911 : Blo 319836 319911 := bstep (se 1 (by rfl) ⟨239933, by rfl⟩ : syracuseStep 319911 = 479867) B479867
theorem B319995 : Blo 319836 319995 := bstep (se 1 (by rfl) ⟨239996, by rfl⟩ : syracuseStep 319995 = 479993) B479993
theorem B320063 : Blo 319836 320063 := bstep (se 1 (by rfl) ⟨240047, by rfl⟩ : syracuseStep 320063 = 480095) B480095
theorem B320071 : Blo 319836 320071 := bstep (se 1 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 320071 = 480107) B480107
theorem B385607 : Blo 319836 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B483911 : Blo 319836 483911 := bstep (se 1 (by rfl) ⟨362933, by rfl⟩ : syracuseStep 483911 = 725867) B725867
theorem B483947 : Blo 319836 483947 := bstep (se 1 (by rfl) ⟨362960, by rfl⟩ : syracuseStep 483947 = 725921) B725921
theorem B811691 : Blo 319836 811691 := bstep (se 1 (by rfl) ⟨608768, by rfl⟩ : syracuseStep 811691 = 1217537) B1217537
theorem B2482859 : Blo 319836 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B320223 : Blo 319836 320223 := bstep (se 1 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 320223 = 480335) B480335
theorem B320303 : Blo 319836 320303 := bstep (se 1 (by rfl) ⟨240227, by rfl⟩ : syracuseStep 320303 = 480455) B480455
theorem B484175 : Blo 319836 484175 := bstep (se 1 (by rfl) ⟨363131, by rfl⟩ : syracuseStep 484175 = 726263) B726263
theorem B320411 : Blo 319836 320411 := bstep (se 1 (by rfl) ⟨240308, by rfl⟩ : syracuseStep 320411 = 480617) B480617
theorem B1631177 : Blo 319836 1631177 := bstep (se 2 (by rfl) ⟨611691, by rfl⟩ : syracuseStep 1631177 = 1223383) B1223383
theorem B320463 : Blo 319836 320463 := bstep (se 1 (by rfl) ⟨240347, by rfl⟩ : syracuseStep 320463 = 480695) B480695
theorem B320487 : Blo 319836 320487 := bstep (se 1 (by rfl) ⟨240365, by rfl⟩ : syracuseStep 320487 = 480731) B480731
theorem B484571 : Blo 319836 484571 := bstep (se 1 (by rfl) ⟨363428, by rfl⟩ : syracuseStep 484571 = 726857) B726857
theorem B648425 : Blo 319836 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B320799 : Blo 319836 320799 := bstep (se 1 (by rfl) ⟨240599, by rfl⟩ : syracuseStep 320799 = 481199) B481199
theorem B320859 : Blo 319836 320859 := bstep (se 1 (by rfl) ⟨240644, by rfl⟩ : syracuseStep 320859 = 481289) B481289
theorem B320879 : Blo 319836 320879 := bstep (se 1 (by rfl) ⟨240659, by rfl⟩ : syracuseStep 320879 = 481319) B481319
theorem B484745 : Blo 319836 484745 := bstep (se 2 (by rfl) ⟨181779, by rfl⟩ : syracuseStep 484745 = 363559) B363559
theorem B320935 : Blo 319836 320935 := bstep (se 1 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 320935 = 481403) B481403
theorem B321019 : Blo 319836 321019 := bstep (se 1 (by rfl) ⟨240764, by rfl⟩ : syracuseStep 321019 = 481529) B481529
theorem B812551 : Blo 319836 812551 := bstep (se 1 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 812551 = 1218827) B1218827
theorem B321087 : Blo 319836 321087 := bstep (se 1 (by rfl) ⟨240815, by rfl⟩ : syracuseStep 321087 = 481631) B481631
theorem B321095 : Blo 319836 321095 := bstep (se 1 (by rfl) ⟨240821, by rfl⟩ : syracuseStep 321095 = 481643) B481643
theorem B321247 : Blo 319836 321247 := bstep (se 1 (by rfl) ⟨240935, by rfl⟩ : syracuseStep 321247 = 481871) B481871
theorem B485099 : Blo 319836 485099 := bstep (se 1 (by rfl) ⟨363824, by rfl⟩ : syracuseStep 485099 = 727649) B727649
theorem B878383 : Blo 319836 878383 := bstep (se 1 (by rfl) ⟨658787, by rfl⟩ : syracuseStep 878383 = 1317575) B1317575
theorem B321327 : Blo 319836 321327 := bstep (se 1 (by rfl) ⟨240995, by rfl⟩ : syracuseStep 321327 = 481991) B481991
theorem B911159 : Blo 319836 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B812855 : Blo 319836 812855 := bstep (se 1 (by rfl) ⟨609641, by rfl⟩ : syracuseStep 812855 = 1219283) B1219283
theorem B3532679 : Blo 319836 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B321435 : Blo 319836 321435 := bstep (se 1 (by rfl) ⟨241076, by rfl⟩ : syracuseStep 321435 = 482153) B482153
theorem B2451383 : Blo 319836 2451383 := bstep (se 1 (by rfl) ⟨1838537, by rfl⟩ : syracuseStep 2451383 = 3677075) B3677075
theorem B321487 : Blo 319836 321487 := bstep (se 1 (by rfl) ⟨241115, by rfl⟩ : syracuseStep 321487 = 482231) B482231
theorem B485327 : Blo 319836 485327 := bstep (se 1 (by rfl) ⟨363995, by rfl⟩ : syracuseStep 485327 = 727991) B727991
theorem B321511 : Blo 319836 321511 := bstep (se 1 (by rfl) ⟨241133, by rfl⟩ : syracuseStep 321511 = 482267) B482267
theorem B2320649 : Blo 319836 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B2615561 : Blo 319836 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B1468697 : Blo 319836 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B321823 : Blo 319836 321823 := bstep (se 1 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 321823 = 482735) B482735
theorem B321883 : Blo 319836 321883 := bstep (se 1 (by rfl) ⟨241412, by rfl⟩ : syracuseStep 321883 = 482825) B482825
theorem B485723 : Blo 319836 485723 := bstep (se 1 (by rfl) ⟨364292, by rfl⟩ : syracuseStep 485723 = 728585) B728585
theorem B321903 : Blo 319836 321903 := bstep (se 1 (by rfl) ⟨241427, by rfl⟩ : syracuseStep 321903 = 482855) B482855
theorem B321959 : Blo 319836 321959 := bstep (se 1 (by rfl) ⟨241469, by rfl⟩ : syracuseStep 321959 = 482939) B482939
theorem B813523 : Blo 319836 813523 := bstep (se 1 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 813523 = 1220285) B1220285
theorem B322043 : Blo 319836 322043 := bstep (se 1 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 322043 = 483065) B483065
theorem B322111 : Blo 319836 322111 := bstep (se 1 (by rfl) ⟨241583, by rfl⟩ : syracuseStep 322111 = 483167) B483167
theorem B322119 : Blo 319836 322119 := bstep (se 1 (by rfl) ⟨241589, by rfl⟩ : syracuseStep 322119 = 483179) B483179
theorem B11168441 : Blo 319836 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B322271 : Blo 319836 322271 := bstep (se 1 (by rfl) ⟨241703, by rfl⟩ : syracuseStep 322271 = 483407) B483407
theorem B322351 : Blo 319836 322351 := bstep (se 1 (by rfl) ⟨241763, by rfl⟩ : syracuseStep 322351 = 483527) B483527
theorem B1829699 : Blo 319836 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B322459 : Blo 319836 322459 := bstep (se 1 (by rfl) ⟨241844, by rfl⟩ : syracuseStep 322459 = 483689) B483689
theorem B322511 : Blo 319836 322511 := bstep (se 1 (by rfl) ⟨241883, by rfl⟩ : syracuseStep 322511 = 483767) B483767
theorem B322535 : Blo 319836 322535 := bstep (se 1 (by rfl) ⟨241901, by rfl⟩ : syracuseStep 322535 = 483803) B483803
theorem B31878157 : Blo 319836 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B814313 : Blo 319836 814313 := bstep (se 2 (by rfl) ⟨305367, by rfl⟩ : syracuseStep 814313 = 610735) B610735
theorem B322847 : Blo 319836 322847 := bstep (se 1 (by rfl) ⟨242135, by rfl⟩ : syracuseStep 322847 = 484271) B484271
theorem B322907 : Blo 319836 322907 := bstep (se 1 (by rfl) ⟨242180, by rfl⟩ : syracuseStep 322907 = 484361) B484361
theorem B322927 : Blo 319836 322927 := bstep (se 1 (by rfl) ⟨242195, by rfl⟩ : syracuseStep 322927 = 484391) B484391
theorem B683387 : Blo 319836 683387 := bstep (se 1 (by rfl) ⟨512540, by rfl⟩ : syracuseStep 683387 = 1025081) B1025081
theorem B2485633 : Blo 319836 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B814475 : Blo 319836 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B322983 : Blo 319836 322983 := bstep (se 1 (by rfl) ⟨242237, by rfl⟩ : syracuseStep 322983 = 484475) B484475
theorem B323067 : Blo 319836 323067 := bstep (se 1 (by rfl) ⟨242300, by rfl⟩ : syracuseStep 323067 = 484601) B484601
theorem B1404431 : Blo 319836 1404431 := bstep (se 1 (by rfl) ⟨1053323, by rfl⟩ : syracuseStep 1404431 = 2106647) B2106647
theorem B2747965 : Blo 319836 2747965 := bstep (se 3 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 2747965 = 1030487) B1030487
theorem B323135 : Blo 319836 323135 := bstep (se 1 (by rfl) ⟨242351, by rfl⟩ : syracuseStep 323135 = 484703) B484703
theorem B323143 : Blo 319836 323143 := bstep (se 1 (by rfl) ⟨242357, by rfl⟩ : syracuseStep 323143 = 484715) B484715
theorem B323295 : Blo 319836 323295 := bstep (se 1 (by rfl) ⟨242471, by rfl⟩ : syracuseStep 323295 = 484943) B484943
theorem B323375 : Blo 319836 323375 := bstep (se 1 (by rfl) ⟨242531, by rfl⟩ : syracuseStep 323375 = 485063) B485063
theorem B323483 : Blo 319836 323483 := bstep (se 1 (by rfl) ⟨242612, by rfl⟩ : syracuseStep 323483 = 485225) B485225
theorem B323535 : Blo 319836 323535 := bstep (se 1 (by rfl) ⟨242651, by rfl⟩ : syracuseStep 323535 = 485303) B485303
theorem B323559 : Blo 319836 323559 := bstep (se 1 (by rfl) ⟨242669, by rfl⟩ : syracuseStep 323559 = 485339) B485339
theorem B45674675 : Blo 319836 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B913619 : Blo 319836 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B815467 : Blo 319836 815467 := bstep (se 1 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 815467 = 1223201) B1223201
theorem B684463 : Blo 319836 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B815791 : Blo 319836 815791 := bstep (se 1 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 815791 = 1223687) B1223687
theorem B1077943 : Blo 319836 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B1635065 : Blo 319836 1635065 := bstep (se 2 (by rfl) ⟨613149, by rfl⟩ : syracuseStep 1635065 = 1226299) B1226299
theorem B3076973 : Blo 319836 3076973 := bstep (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) B1153865
theorem B14873507 : Blo 319836 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B816115 : Blo 319836 816115 := bstep (se 1 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 816115 = 1224173) B1224173
theorem B3306539 : Blo 319836 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B6222905 : Blo 319836 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B2454785 : Blo 319836 2454785 := bstep (se 2 (by rfl) ⟨920544, by rfl⟩ : syracuseStep 2454785 = 1841089) B1841089
theorem B685351 : Blo 319836 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B914827 : Blo 319836 914827 := bstep (se 1 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 914827 = 1372241) B1372241
theorem B1373831 : Blo 319836 1373831 := bstep (se 1 (by rfl) ⟨1030373, by rfl⟩ : syracuseStep 1373831 = 2060747) B2060747
theorem B915101 : Blo 319836 915101 := bstep (se 3 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 915101 = 343163) B343163
theorem B1373881 : Blo 319836 1373881 := bstep (se 2 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 1373881 = 1030411) B1030411
theorem B816875 : Blo 319836 816875 := bstep (se 1 (by rfl) ⟨612656, by rfl⟩ : syracuseStep 816875 = 1225313) B1225313
theorem B18708317 : Blo 319836 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B76904549 : Blo 319836 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B1866007 : Blo 319836 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B522587 : Blo 319836 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B817735 : Blo 319836 817735 := bstep (se 1 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 817735 = 1226603) B1226603
theorem B817847 : Blo 319836 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B3078931 : Blo 319836 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B720071 : Blo 319836 720071 := bstep (se 1 (by rfl) ⟨540053, by rfl⟩ : syracuseStep 720071 = 1080107) B1080107
theorem B1080539 : Blo 319836 1080539 := bstep (se 1 (by rfl) ⟨810404, by rfl⟩ : syracuseStep 1080539 = 1620809) B1620809
theorem B2489573 : Blo 319836 2489573 := bstep (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) B466795
theorem B1375555 : Blo 319836 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B720251 : Blo 319836 720251 := bstep (se 1 (by rfl) ⟨540188, by rfl⟩ : syracuseStep 720251 = 1080377) B1080377
theorem B621947 : Blo 319836 621947 := bstep (se 1 (by rfl) ⟨466460, by rfl⟩ : syracuseStep 621947 = 932921) B932921
theorem B1637819 : Blo 319836 1637819 := bstep (se 1 (by rfl) ⟨1228364, by rfl⟩ : syracuseStep 1637819 = 2456729) B2456729
theorem B720377 : Blo 319836 720377 := bstep (se 2 (by rfl) ⟨270141, by rfl⟩ : syracuseStep 720377 = 540283) B540283
theorem B720467 : Blo 319836 720467 := bstep (se 1 (by rfl) ⟨540350, by rfl⟩ : syracuseStep 720467 = 1080701) B1080701
theorem B360031 : Blo 319836 360031 := bstep (se 1 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 360031 = 540047) B540047
theorem B3079775 : Blo 319836 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B1736353 : Blo 319836 1736353 := bstep (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) B1302265
theorem B818849 : Blo 319836 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B720647 : Blo 319836 720647 := bstep (se 1 (by rfl) ⟨540485, by rfl⟩ : syracuseStep 720647 = 1080971) B1080971
theorem B1474433 : Blo 319836 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B720935 : Blo 319836 720935 := bstep (se 1 (by rfl) ⟨540701, by rfl⟩ : syracuseStep 720935 = 1081403) B1081403
theorem B721115 : Blo 319836 721115 := bstep (se 1 (by rfl) ⟨540836, by rfl⟩ : syracuseStep 721115 = 1081673) B1081673
theorem B360679 : Blo 319836 360679 := bstep (se 1 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 360679 = 541019) B541019
theorem B2064665 : Blo 319836 2064665 := bstep (se 2 (by rfl) ⟨774249, by rfl⟩ : syracuseStep 2064665 = 1548499) B1548499
theorem B459145 : Blo 319836 459145 := bstep (se 2 (by rfl) ⟨172179, by rfl⟩ : syracuseStep 459145 = 344359) B344359
theorem B721385 : Blo 319836 721385 := bstep (se 2 (by rfl) ⟨270519, by rfl⟩ : syracuseStep 721385 = 541039) B541039
theorem B917993 : Blo 319836 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B3080699 : Blo 319836 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B721673 : Blo 319836 721673 := bstep (se 2 (by rfl) ⟨270627, by rfl⟩ : syracuseStep 721673 = 541255) B541255
theorem B1082159 : Blo 319836 1082159 := bstep (se 1 (by rfl) ⟨811619, by rfl⟩ : syracuseStep 1082159 = 1623239) B1623239
theorem B361327 : Blo 319836 361327 := bstep (se 1 (by rfl) ⟨270995, by rfl⟩ : syracuseStep 361327 = 541991) B541991
theorem B1082267 : Blo 319836 1082267 := bstep (se 1 (by rfl) ⟨811700, by rfl⟩ : syracuseStep 1082267 = 1623401) B1623401
theorem B722249 : Blo 319836 722249 := bstep (se 2 (by rfl) ⟨270843, by rfl⟩ : syracuseStep 722249 = 541687) B541687
theorem B460409 : Blo 319836 460409 := bstep (se 2 (by rfl) ⟨172653, by rfl⟩ : syracuseStep 460409 = 345307) B345307
theorem B919201 : Blo 319836 919201 := bstep (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) B689401
theorem B919259 : Blo 319836 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B6620957 : Blo 319836 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B1181537 : Blo 319836 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B2066305 : Blo 319836 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B362479 : Blo 319836 362479 := bstep (se 1 (by rfl) ⟨271859, by rfl⟩ : syracuseStep 362479 = 543719) B543719
theorem B1083401 : Blo 319836 1083401 := bstep (se 2 (by rfl) ⟨406275, by rfl⟩ : syracuseStep 1083401 = 812551) B812551
theorem B886909 : Blo 319836 886909 := bstep (se 3 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 886909 = 332591) B332591
theorem B723239 : Blo 319836 723239 := bstep (se 1 (by rfl) ⟨542429, by rfl⟩ : syracuseStep 723239 = 1084859) B1084859
theorem B723257 : Blo 319836 723257 := bstep (se 2 (by rfl) ⟨271221, by rfl⟩ : syracuseStep 723257 = 542443) B542443
theorem B13896197 : Blo 319836 13896197 := bstep (se 4 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 13896197 = 2605537) B2605537
theorem B920135 : Blo 319836 920135 := bstep (se 1 (by rfl) ⟨690101, by rfl⟩ : syracuseStep 920135 = 1380203) B1380203
theorem B1837673 : Blo 319836 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B8817437 : Blo 319836 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B691247 : Blo 319836 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B1084697 : Blo 319836 1084697 := bstep (se 2 (by rfl) ⟨406761, by rfl⟩ : syracuseStep 1084697 = 813523) B813523
theorem B1084751 : Blo 319836 1084751 := bstep (se 1 (by rfl) ⟨813563, by rfl⟩ : syracuseStep 1084751 = 1627127) B1627127
theorem B724553 : Blo 319836 724553 := bstep (se 2 (by rfl) ⟨271707, by rfl⟩ : syracuseStep 724553 = 543415) B543415
theorem B1838699 : Blo 319836 1838699 := bstep (se 1 (by rfl) ⟨1379024, by rfl⟩ : syracuseStep 1838699 = 2758049) B2758049
theorem B42504209 : Blo 319836 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B3084389 : Blo 319836 3084389 := bstep (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) B578323
theorem B3314177 : Blo 319836 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B1086047 : Blo 319836 1086047 := bstep (se 1 (by rfl) ⟨814535, by rfl⟩ : syracuseStep 1086047 = 1629071) B1629071
theorem B726011 : Blo 319836 726011 := bstep (se 1 (by rfl) ⟨544508, by rfl⟩ : syracuseStep 726011 = 1089017) B1089017
theorem B726191 : Blo 319836 726191 := bstep (se 1 (by rfl) ⟨544643, by rfl⟩ : syracuseStep 726191 = 1089287) B1089287
theorem B1545425 : Blo 319836 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B726227 : Blo 319836 726227 := bstep (se 1 (by rfl) ⟨544670, by rfl⟩ : syracuseStep 726227 = 1089341) B1089341
theorem B15832493 : Blo 319836 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B3675617 : Blo 319836 3675617 := bstep (se 2 (by rfl) ⟨1378356, by rfl⟩ : syracuseStep 3675617 = 2756713) B2756713
theorem B726497 : Blo 319836 726497 := bstep (se 2 (by rfl) ⟨272436, by rfl⟩ : syracuseStep 726497 = 544873) B544873
theorem B1840907 : Blo 319836 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B1087289 : Blo 319836 1087289 := bstep (se 2 (by rfl) ⟨407733, by rfl⟩ : syracuseStep 1087289 = 815467) B815467
theorem B1087451 : Blo 319836 1087451 := bstep (se 1 (by rfl) ⟨815588, by rfl⟩ : syracuseStep 1087451 = 1631177) B1631177
theorem B1087721 : Blo 319836 1087721 := bstep (se 2 (by rfl) ⟨407895, by rfl⟩ : syracuseStep 1087721 = 815791) B815791
theorem B3905981 : Blo 319836 3905981 := bstep (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) B1464743
theorem B1088153 : Blo 319836 1088153 := bstep (se 2 (by rfl) ⟨408057, by rfl⟩ : syracuseStep 1088153 = 816115) B816115
theorem B1547099 : Blo 319836 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B1743707 : Blo 319836 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B728135 : Blo 319836 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B7445627 : Blo 319836 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B1219769 : Blo 319836 1219769 := bstep (se 2 (by rfl) ⟨457413, by rfl⟩ : syracuseStep 1219769 = 914827) B914827
theorem B1219799 : Blo 319836 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B728531 : Blo 319836 728531 := bstep (se 1 (by rfl) ⟨546398, by rfl⟩ : syracuseStep 728531 = 1092797) B1092797
theorem B3349991 : Blo 319836 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B4136507 : Blo 319836 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B30449783 : Blo 319836 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B1090043 : Blo 319836 1090043 := bstep (se 1 (by rfl) ⟨817532, by rfl⟩ : syracuseStep 1090043 = 1635065) B1635065
theorem B1090313 : Blo 319836 1090313 := bstep (se 2 (by rfl) ⟨408867, by rfl⟩ : syracuseStep 1090313 = 817735) B817735
theorem B4105241 : Blo 319836 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B1091069 : Blo 319836 1091069 := bstep (se 3 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 1091069 = 409151) B409151
theorem B2238211 : Blo 319836 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B4139171 : Blo 319836 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B1091879 : Blo 319836 1091879 := bstep (se 1 (by rfl) ⟨818909, by rfl⟩ : syracuseStep 1091879 = 1637819) B1637819
theorem B1092743 : Blo 319836 1092743 := bstep (se 1 (by rfl) ⟨819557, by rfl⟩ : syracuseStep 1092743 = 1639115) B1639115
theorem B2436317 : Blo 319836 2436317 := bstep (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) B913619
theorem B1092851 : Blo 319836 1092851 := bstep (se 1 (by rfl) ⟨819638, by rfl⟩ : syracuseStep 1092851 = 1639277) B1639277
theorem B699967 : Blo 319836 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B405319 : Blo 319836 405319 := bstep (se 1 (by rfl) ⟨303989, by rfl⟩ : syracuseStep 405319 = 607979) B607979
theorem B1224827 : Blo 319836 1224827 := bstep (se 1 (by rfl) ⟨918620, by rfl⟩ : syracuseStep 1224827 = 1837241) B1837241
theorem B1028285 : Blo 319836 1028285 := bstep (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) B385607
theorem B6173081 : Blo 319836 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B405967 : Blo 319836 405967 := bstep (se 1 (by rfl) ⟨304475, by rfl⟩ : syracuseStep 405967 = 608951) B608951
theorem B9254087 : Blo 319836 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B406939 : Blo 319836 406939 := bstep (se 1 (by rfl) ⟨305204, by rfl⟩ : syracuseStep 406939 = 610409) B610409
theorem B4961735 : Blo 319836 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B407207 : Blo 319836 407207 := bstep (se 1 (by rfl) ⟨305405, by rfl⟩ : syracuseStep 407207 = 610811) B610811
theorem B1161017 : Blo 319836 1161017 := bstep (se 2 (by rfl) ⟨435381, by rfl⟩ : syracuseStep 1161017 = 870763) B870763
theorem B407359 : Blo 319836 407359 := bstep (se 1 (by rfl) ⟨305519, by rfl⟩ : syracuseStep 407359 = 611039) B611039
theorem B3979145 : Blo 319836 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B407855 : Blo 319836 407855 := bstep (se 1 (by rfl) ⟨305891, by rfl⟩ : syracuseStep 407855 = 611783) B611783
theorem B7092775 : Blo 319836 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B539831 : Blo 319836 539831 := bstep (se 1 (by rfl) ⟨404873, by rfl⟩ : syracuseStep 539831 = 809747) B809747
theorem B1228061 : Blo 319836 1228061 := bstep (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) B460523
theorem B736723 : Blo 319836 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B1228243 : Blo 319836 1228243 := bstep (se 1 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 1228243 = 1842365) B1842365
theorem B540155 : Blo 319836 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B1556111 : Blo 319836 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B2735801 : Blo 319836 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B540587 : Blo 319836 540587 := bstep (se 1 (by rfl) ⟨405440, by rfl⟩ : syracuseStep 540587 = 810881) B810881
theorem B1228715 : Blo 319836 1228715 := bstep (se 1 (by rfl) ⟨921536, by rfl⟩ : syracuseStep 1228715 = 1843073) B1843073
theorem B5226839 : Blo 319836 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B541127 : Blo 319836 541127 := bstep (se 1 (by rfl) ⟨405845, by rfl⟩ : syracuseStep 541127 = 811691) B811691
theorem B1622591 : Blo 319836 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B2015873 : Blo 319836 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B3916525 : Blo 319836 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B6931493 : Blo 319836 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B607439 : Blo 319836 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B541903 : Blo 319836 541903 := bstep (se 1 (by rfl) ⟨406427, by rfl⟩ : syracuseStep 541903 = 812855) B812855
theorem B3655205 : Blo 319836 3655205 := bstep (se 4 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 3655205 = 685351) B685351
theorem B3130919 : Blo 319836 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B1623887 : Blo 319836 1623887 := bstep (se 1 (by rfl) ⟨1217915, by rfl⟩ : syracuseStep 1623887 = 2435831) B2435831
theorem B542713 : Blo 319836 542713 := bstep (se 2 (by rfl) ⟨203517, by rfl⟩ : syracuseStep 542713 = 407035) B407035
theorem B542875 : Blo 319836 542875 := bstep (se 1 (by rfl) ⟨407156, by rfl⟩ : syracuseStep 542875 = 814313) B814313
theorem B542983 : Blo 319836 542983 := bstep (se 1 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 542983 = 814475) B814475
theorem B543017 : Blo 319836 543017 := bstep (se 2 (by rfl) ⟨203631, by rfl⟩ : syracuseStep 543017 = 407263) B407263
theorem B936287 : Blo 319836 936287 := bstep (se 1 (by rfl) ⟨702215, by rfl⟩ : syracuseStep 936287 = 1404431) B1404431
theorem B2051315 : Blo 319836 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B544009 : Blo 319836 544009 := bstep (se 2 (by rfl) ⟨204003, by rfl⟩ : syracuseStep 544009 = 408007) B408007
theorem B6638861 : Blo 319836 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B9915671 : Blo 319836 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B4148603 : Blo 319836 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B1822135 : Blo 319836 1822135 := bstep (se 1 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 1822135 = 2733203) B2733203
theorem B1035767 : Blo 319836 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B3296857 : Blo 319836 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B610067 : Blo 319836 610067 := bstep (se 1 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 610067 = 915101) B915101
theorem B544583 : Blo 319836 544583 := bstep (se 1 (by rfl) ⟨408437, by rfl⟩ : syracuseStep 544583 = 816875) B816875
theorem B12472211 : Blo 319836 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B51269699 : Blo 319836 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B348391 : Blo 319836 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B1626479 : Blo 319836 1626479 := bstep (se 1 (by rfl) ⟨1219859, by rfl⟩ : syracuseStep 1626479 = 2439719) B2439719
theorem B545231 : Blo 319836 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B1036793 : Blo 319836 1036793 := bstep (se 2 (by rfl) ⟨388797, by rfl⟩ : syracuseStep 1036793 = 777595) B777595
theorem B1299023 : Blo 319836 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B480041 : Blo 319836 480041 := bstep (se 2 (by rfl) ⟨180015, by rfl⟩ : syracuseStep 480041 = 360031) B360031
theorem B480047 : Blo 319836 480047 := bstep (se 1 (by rfl) ⟨360035, by rfl⟩ : syracuseStep 480047 = 720071) B720071
theorem B2315137 : Blo 319836 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B480167 : Blo 319836 480167 := bstep (se 1 (by rfl) ⟨360125, by rfl⟩ : syracuseStep 480167 = 720251) B720251
theorem B414631 : Blo 319836 414631 := bstep (se 1 (by rfl) ⟨310973, by rfl⟩ : syracuseStep 414631 = 621947) B621947
theorem B480251 : Blo 319836 480251 := bstep (se 1 (by rfl) ⟨360188, by rfl⟩ : syracuseStep 480251 = 720377) B720377
theorem B480311 : Blo 319836 480311 := bstep (se 1 (by rfl) ⟨360233, by rfl⟩ : syracuseStep 480311 = 720467) B720467
theorem B2053183 : Blo 319836 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B775241 : Blo 319836 775241 := bstep (se 2 (by rfl) ⟨290715, by rfl⟩ : syracuseStep 775241 = 581431) B581431
theorem B545899 : Blo 319836 545899 := bstep (se 1 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 545899 = 818849) B818849
theorem B480431 : Blo 319836 480431 := bstep (se 1 (by rfl) ⟨360323, by rfl⟩ : syracuseStep 480431 = 720647) B720647
theorem B1824119 : Blo 319836 1824119 := bstep (se 1 (by rfl) ⟨1368089, by rfl⟩ : syracuseStep 1824119 = 2736179) B2736179
theorem B546203 : Blo 319836 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B480839 : Blo 319836 480839 := bstep (se 1 (by rfl) ⟨360629, by rfl⟩ : syracuseStep 480839 = 721259) B721259
theorem B480935 : Blo 319836 480935 := bstep (se 1 (by rfl) ⟨360701, by rfl⟩ : syracuseStep 480935 = 721403) B721403
theorem B481019 : Blo 319836 481019 := bstep (se 1 (by rfl) ⟨360764, by rfl⟩ : syracuseStep 481019 = 721529) B721529
theorem B6215453 : Blo 319836 6215453 := bstep (se 3 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 6215453 = 2330795) B2330795
theorem B481055 : Blo 319836 481055 := bstep (se 1 (by rfl) ⟨360791, by rfl⟩ : syracuseStep 481055 = 721583) B721583
theorem B294508331 : Blo 319836 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B481103 : Blo 319836 481103 := bstep (se 1 (by rfl) ⟨360827, by rfl⟩ : syracuseStep 481103 = 721655) B721655
theorem B481223 : Blo 319836 481223 := bstep (se 1 (by rfl) ⟨360917, by rfl⟩ : syracuseStep 481223 = 721835) B721835
theorem B481577 : Blo 319836 481577 := bstep (se 2 (by rfl) ⟨180591, by rfl⟩ : syracuseStep 481577 = 361183) B361183
theorem B481583 : Blo 319836 481583 := bstep (se 1 (by rfl) ⟨361187, by rfl⟩ : syracuseStep 481583 = 722375) B722375
theorem B7428631 : Blo 319836 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B481823 : Blo 319836 481823 := bstep (se 1 (by rfl) ⟨361367, by rfl⟩ : syracuseStep 481823 = 722735) B722735
theorem B7002773 : Blo 319836 7002773 := bstep (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) B328255
theorem B482207 : Blo 319836 482207 := bstep (se 1 (by rfl) ⟨361655, by rfl⟩ : syracuseStep 482207 = 723311) B723311
theorem B482255 : Blo 319836 482255 := bstep (se 1 (by rfl) ⟨361691, by rfl⟩ : syracuseStep 482255 = 723383) B723383
theorem B482345 : Blo 319836 482345 := bstep (se 2 (by rfl) ⟨180879, by rfl⟩ : syracuseStep 482345 = 361759) B361759
theorem B482351 : Blo 319836 482351 := bstep (se 1 (by rfl) ⟨361763, by rfl⟩ : syracuseStep 482351 = 723527) B723527
theorem B482375 : Blo 319836 482375 := bstep (se 1 (by rfl) ⟨361781, by rfl⟩ : syracuseStep 482375 = 723563) B723563
theorem B482639 : Blo 319836 482639 := bstep (se 1 (by rfl) ⟨361979, by rfl⟩ : syracuseStep 482639 = 723959) B723959
theorem B482729 : Blo 319836 482729 := bstep (se 2 (by rfl) ⟨181023, by rfl⟩ : syracuseStep 482729 = 362047) B362047
theorem B482879 : Blo 319836 482879 := bstep (se 1 (by rfl) ⟨362159, by rfl⟩ : syracuseStep 482879 = 724319) B724319
theorem B810587 : Blo 319836 810587 := bstep (se 1 (by rfl) ⟨607940, by rfl⟩ : syracuseStep 810587 = 1215881) B1215881
theorem B679657 : Blo 319836 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B483143 : Blo 319836 483143 := bstep (se 1 (by rfl) ⟨362357, by rfl⟩ : syracuseStep 483143 = 724715) B724715
theorem B1040215 : Blo 319836 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B483227 : Blo 319836 483227 := bstep (se 1 (by rfl) ⟨362420, by rfl⟩ : syracuseStep 483227 = 724841) B724841
theorem B1827035 : Blo 319836 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B2941265 : Blo 319836 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B319871 : Blo 319836 319871 := bstep (se 1 (by rfl) ⟨239903, by rfl⟩ : syracuseStep 319871 = 479807) B479807
theorem B7791011 : Blo 319836 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B319951 : Blo 319836 319951 := bstep (se 1 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 319951 = 479927) B479927
theorem B483791 : Blo 319836 483791 := bstep (se 1 (by rfl) ⟨362843, by rfl⟩ : syracuseStep 483791 = 725687) B725687
theorem B483833 : Blo 319836 483833 := bstep (se 2 (by rfl) ⟨181437, by rfl⟩ : syracuseStep 483833 = 362875) B362875
theorem B483935 : Blo 319836 483935 := bstep (se 1 (by rfl) ⟨362951, by rfl⟩ : syracuseStep 483935 = 725903) B725903
theorem B320103 : Blo 319836 320103 := bstep (se 1 (by rfl) ⟨240077, by rfl⟩ : syracuseStep 320103 = 480155) B480155
theorem B1729133 : Blo 319836 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B1827467 : Blo 319836 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B7037725 : Blo 319836 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B320367 : Blo 319836 320367 := bstep (se 1 (by rfl) ⟨240275, by rfl⟩ : syracuseStep 320367 = 480551) B480551
theorem B320423 : Blo 319836 320423 := bstep (se 1 (by rfl) ⟨240317, by rfl⟩ : syracuseStep 320423 = 480635) B480635
theorem B320507 : Blo 319836 320507 := bstep (se 1 (by rfl) ⟨240380, by rfl⟩ : syracuseStep 320507 = 480761) B480761
theorem B320575 : Blo 319836 320575 := bstep (se 1 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 320575 = 480863) B480863
theorem B484415 : Blo 319836 484415 := bstep (se 1 (by rfl) ⟨363311, by rfl⟩ : syracuseStep 484415 = 726623) B726623
theorem B484457 : Blo 319836 484457 := bstep (se 2 (by rfl) ⟨181671, by rfl⟩ : syracuseStep 484457 = 363343) B363343
theorem B320719 : Blo 319836 320719 := bstep (se 1 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 320719 = 481079) B481079
theorem B484559 : Blo 319836 484559 := bstep (se 1 (by rfl) ⟨363419, by rfl⟩ : syracuseStep 484559 = 726839) B726839
theorem B320923 : Blo 319836 320923 := bstep (se 1 (by rfl) ⟨240692, by rfl⟩ : syracuseStep 320923 = 481385) B481385
theorem B484763 : Blo 319836 484763 := bstep (se 1 (by rfl) ⟨363572, by rfl⟩ : syracuseStep 484763 = 727145) B727145
theorem B1631663 : Blo 319836 1631663 := bstep (se 1 (by rfl) ⟨1223747, by rfl⟩ : syracuseStep 1631663 = 2447495) B2447495
theorem B1631825 : Blo 319836 1631825 := bstep (se 2 (by rfl) ⟨611934, by rfl⟩ : syracuseStep 1631825 = 1223869) B1223869
theorem B1304147 : Blo 319836 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B321135 : Blo 319836 321135 := bstep (se 1 (by rfl) ⟨240851, by rfl⟩ : syracuseStep 321135 = 481703) B481703
theorem B484985 : Blo 319836 484985 := bstep (se 2 (by rfl) ⟨181869, by rfl⟩ : syracuseStep 484985 = 363739) B363739
theorem B321191 : Blo 319836 321191 := bstep (se 1 (by rfl) ⟨240893, by rfl⟩ : syracuseStep 321191 = 481787) B481787
theorem B386779 : Blo 319836 386779 := bstep (se 1 (by rfl) ⟨290084, by rfl⟩ : syracuseStep 386779 = 580169) B580169
theorem B485087 : Blo 319836 485087 := bstep (se 1 (by rfl) ⟨363815, by rfl⟩ : syracuseStep 485087 = 727631) B727631
theorem B3892981 : Blo 319836 3892981 := bstep (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) B364967
theorem B321275 : Blo 319836 321275 := bstep (se 1 (by rfl) ⟨240956, by rfl⟩ : syracuseStep 321275 = 481913) B481913
theorem B321311 : Blo 319836 321311 := bstep (se 1 (by rfl) ⟨240983, by rfl⟩ : syracuseStep 321311 = 481967) B481967
theorem B321343 : Blo 319836 321343 := bstep (se 1 (by rfl) ⟨241007, by rfl⟩ : syracuseStep 321343 = 482015) B482015
theorem B485183 : Blo 319836 485183 := bstep (se 1 (by rfl) ⟨363887, by rfl⟩ : syracuseStep 485183 = 727775) B727775
theorem B485351 : Blo 319836 485351 := bstep (se 1 (by rfl) ⟨364013, by rfl⟩ : syracuseStep 485351 = 728027) B728027
theorem B321519 : Blo 319836 321519 := bstep (se 1 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 321519 = 482279) B482279
theorem B485369 : Blo 319836 485369 := bstep (se 2 (by rfl) ⟨182013, by rfl⟩ : syracuseStep 485369 = 364027) B364027
theorem B3663953 : Blo 319836 3663953 := bstep (se 2 (by rfl) ⟨1373982, by rfl⟩ : syracuseStep 3663953 = 2747965) B2747965
theorem B485471 : Blo 319836 485471 := bstep (se 1 (by rfl) ⟨364103, by rfl⟩ : syracuseStep 485471 = 728207) B728207
theorem B321691 : Blo 319836 321691 := bstep (se 1 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 321691 = 482537) B482537
theorem B485531 : Blo 319836 485531 := bstep (se 1 (by rfl) ⟨364148, by rfl⟩ : syracuseStep 485531 = 728297) B728297
theorem B321727 : Blo 319836 321727 := bstep (se 1 (by rfl) ⟨241295, by rfl⟩ : syracuseStep 321727 = 482591) B482591
theorem B485567 : Blo 319836 485567 := bstep (se 1 (by rfl) ⟨364175, by rfl⟩ : syracuseStep 485567 = 728351) B728351
theorem B485609 : Blo 319836 485609 := bstep (se 2 (by rfl) ⟨182103, by rfl⟩ : syracuseStep 485609 = 364207) B364207
theorem B321839 : Blo 319836 321839 := bstep (se 1 (by rfl) ⟨241379, by rfl⟩ : syracuseStep 321839 = 482759) B482759
theorem B813473 : Blo 319836 813473 := bstep (se 2 (by rfl) ⟨305052, by rfl⟩ : syracuseStep 813473 = 610105) B610105
theorem B2779643 : Blo 319836 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B322075 : Blo 319836 322075 := bstep (se 1 (by rfl) ⟨241556, by rfl⟩ : syracuseStep 322075 = 483113) B483113
theorem B322079 : Blo 319836 322079 := bstep (se 1 (by rfl) ⟨241559, by rfl⟩ : syracuseStep 322079 = 483119) B483119
theorem B4123385 : Blo 319836 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B3468035 : Blo 319836 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B322395 : Blo 319836 322395 := bstep (se 1 (by rfl) ⟨241796, by rfl⟩ : syracuseStep 322395 = 483593) B483593
theorem B322463 : Blo 319836 322463 := bstep (se 1 (by rfl) ⟨241847, by rfl⟩ : syracuseStep 322463 = 483695) B483695
theorem B322607 : Blo 319836 322607 := bstep (se 1 (by rfl) ⟨241955, by rfl⟩ : syracuseStep 322607 = 483911) B483911
theorem B322631 : Blo 319836 322631 := bstep (se 1 (by rfl) ⟨241973, by rfl⟩ : syracuseStep 322631 = 483947) B483947
theorem B322783 : Blo 319836 322783 := bstep (se 1 (by rfl) ⟨242087, by rfl⟩ : syracuseStep 322783 = 484175) B484175
theorem B912617 : Blo 319836 912617 := bstep (se 2 (by rfl) ⟨342231, by rfl⟩ : syracuseStep 912617 = 684463) B684463
theorem B323047 : Blo 319836 323047 := bstep (se 1 (by rfl) ⟨242285, by rfl⟩ : syracuseStep 323047 = 484571) B484571
theorem B1437257 : Blo 319836 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B323163 : Blo 319836 323163 := bstep (se 1 (by rfl) ⟨242372, by rfl⟩ : syracuseStep 323163 = 484745) B484745
theorem B4615973 : Blo 319836 4615973 := bstep (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) B865495
theorem B323399 : Blo 319836 323399 := bstep (se 1 (by rfl) ⟨242549, by rfl⟩ : syracuseStep 323399 = 485099) B485099
theorem B2355119 : Blo 319836 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B1634255 : Blo 319836 1634255 := bstep (se 1 (by rfl) ⟨1225691, by rfl⟩ : syracuseStep 1634255 = 2451383) B2451383
theorem B323551 : Blo 319836 323551 := bstep (se 1 (by rfl) ⟨242663, by rfl⟩ : syracuseStep 323551 = 485327) B485327
theorem B323815 : Blo 319836 323815 := bstep (se 1 (by rfl) ⟨242861, by rfl⟩ : syracuseStep 323815 = 485723) B485723
theorem B815609 : Blo 319836 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B1831841 : Blo 319836 1831841 := bstep (se 2 (by rfl) ⟨686940, by rfl⟩ : syracuseStep 1831841 = 1373881) B1373881
theorem B455591 : Blo 319836 455591 := bstep (se 1 (by rfl) ⟨341693, by rfl⟩ : syracuseStep 455591 = 683387) B683387
theorem B1635713 : Blo 319836 1635713 := bstep (se 2 (by rfl) ⟨613392, by rfl⟩ : syracuseStep 1635713 = 1226785) B1226785
theorem B2488009 : Blo 319836 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B817249 : Blo 319836 817249 := bstep (se 2 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 817249 = 612937) B612937
theorem B1636523 : Blo 319836 1636523 := bstep (se 1 (by rfl) ⟨1227392, by rfl⟩ : syracuseStep 1636523 = 2454785) B2454785
theorem B1079675 : Blo 319836 1079675 := bstep (se 1 (by rfl) ⟨809756, by rfl⟩ : syracuseStep 1079675 = 1619513) B1619513
theorem B915887 : Blo 319836 915887 := bstep (se 1 (by rfl) ⟨686915, by rfl⟩ : syracuseStep 915887 = 1373831) B1373831
theorem B2128403 : Blo 319836 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B1079945 : Blo 319836 1079945 := bstep (se 2 (by rfl) ⟨404979, by rfl⟩ : syracuseStep 1079945 = 809959) B809959
theorem B4684709 : Blo 319836 4684709 := bstep (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) B878383
theorem B1834073 : Blo 319836 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B720359 : Blo 319836 720359 := bstep (se 1 (by rfl) ⟨540269, by rfl⟩ : syracuseStep 720359 = 1080539) B1080539
theorem B3964439 : Blo 319836 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B458473 : Blo 319836 458473 := bstep (se 2 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 458473 = 343855) B343855
theorem B1081079 : Blo 319836 1081079 := bstep (se 1 (by rfl) ⟨810809, by rfl⟩ : syracuseStep 1081079 = 1621619) B1621619
theorem B982955 : Blo 319836 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B1376443 : Blo 319836 1376443 := bstep (se 1 (by rfl) ⟨1032332, by rfl⟩ : syracuseStep 1376443 = 2064665) B2064665
theorem B360751 : Blo 319836 360751 := bstep (se 1 (by rfl) ⟨270563, by rfl⟩ : syracuseStep 360751 = 541127) B541127
theorem B1081727 : Blo 319836 1081727 := bstep (se 1 (by rfl) ⟨811295, by rfl⟩ : syracuseStep 1081727 = 1622591) B1622591
theorem B1343915 : Blo 319836 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B721439 : Blo 319836 721439 := bstep (se 1 (by rfl) ⟨541079, by rfl⟩ : syracuseStep 721439 = 1082159) B1082159
theorem B721511 : Blo 319836 721511 := bstep (se 1 (by rfl) ⟨541133, by rfl⟩ : syracuseStep 721511 = 1082267) B1082267
theorem B4620995 : Blo 319836 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B1082591 : Blo 319836 1082591 := bstep (se 1 (by rfl) ⟨811943, by rfl⟩ : syracuseStep 1082591 = 1623887) B1623887
theorem B787691 : Blo 319836 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B722267 : Blo 319836 722267 := bstep (se 1 (by rfl) ⟨541700, by rfl⟩ : syracuseStep 722267 = 1083401) B1083401
theorem B362011 : Blo 319836 362011 := bstep (se 1 (by rfl) ⟨271508, by rfl⟩ : syracuseStep 362011 = 543017) B543017
theorem B624191 : Blo 319836 624191 := bstep (se 1 (by rfl) ⟨468143, by rfl⟩ : syracuseStep 624191 = 936287) B936287
theorem B722537 : Blo 319836 722537 := bstep (se 2 (by rfl) ⟨270951, by rfl⟩ : syracuseStep 722537 = 541903) B541903
theorem B460831 : Blo 319836 460831 := bstep (se 1 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 460831 = 691247) B691247
theorem B723131 : Blo 319836 723131 := bstep (se 1 (by rfl) ⟨542348, by rfl⟩ : syracuseStep 723131 = 1084697) B1084697
theorem B723167 : Blo 319836 723167 := bstep (se 1 (by rfl) ⟨542375, by rfl⟩ : syracuseStep 723167 = 1084751) B1084751
theorem B1214909 : Blo 319836 1214909 := bstep (se 3 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 1214909 = 455591) B455591
theorem B2755073 : Blo 319836 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B363055 : Blo 319836 363055 := bstep (se 1 (by rfl) ⟨272291, by rfl⟩ : syracuseStep 363055 = 544583) B544583
theorem B723617 : Blo 319836 723617 := bstep (se 2 (by rfl) ⟨271356, by rfl⟩ : syracuseStep 723617 = 542713) B542713
theorem B1182545 : Blo 319836 1182545 := bstep (se 2 (by rfl) ⟨443454, by rfl⟩ : syracuseStep 1182545 = 886909) B886909
theorem B723833 : Blo 319836 723833 := bstep (se 2 (by rfl) ⟨271437, by rfl⟩ : syracuseStep 723833 = 542875) B542875
theorem B1084319 : Blo 319836 1084319 := bstep (se 1 (by rfl) ⟨813239, by rfl⟩ : syracuseStep 1084319 = 1626479) B1626479
theorem B363487 : Blo 319836 363487 := bstep (se 1 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 363487 = 545231) B545231
theorem B691195 : Blo 319836 691195 := bstep (se 1 (by rfl) ⟨518396, by rfl⟩ : syracuseStep 691195 = 1036793) B1036793
theorem B723977 : Blo 319836 723977 := bstep (se 2 (by rfl) ⟨271491, by rfl⟩ : syracuseStep 723977 = 542983) B542983
theorem B724031 : Blo 319836 724031 := bstep (se 1 (by rfl) ⟨543023, by rfl⟩ : syracuseStep 724031 = 1086047) B1086047
theorem B1216079 : Blo 319836 1216079 := bstep (se 1 (by rfl) ⟨912059, by rfl⟩ : syracuseStep 1216079 = 1824119) B1824119
theorem B364135 : Blo 319836 364135 := bstep (se 1 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 364135 = 546203) B546203
theorem B10554995 : Blo 319836 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B724859 : Blo 319836 724859 := bstep (se 1 (by rfl) ⟨543644, by rfl⟩ : syracuseStep 724859 = 1087289) B1087289
theorem B724967 : Blo 319836 724967 := bstep (se 1 (by rfl) ⟨543725, by rfl⟩ : syracuseStep 724967 = 1087451) B1087451
theorem B725147 : Blo 319836 725147 := bstep (se 1 (by rfl) ⟨543860, by rfl⟩ : syracuseStep 725147 = 1087721) B1087721
theorem B3477725 : Blo 319836 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B725345 : Blo 319836 725345 := bstep (se 2 (by rfl) ⟨272004, by rfl⟩ : syracuseStep 725345 = 544009) B544009
theorem B725435 : Blo 319836 725435 := bstep (se 1 (by rfl) ⟨544076, by rfl⟩ : syracuseStep 725435 = 1088153) B1088153
theorem B1085885 : Blo 319836 1085885 := bstep (se 3 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 1085885 = 407207) B407207
theorem B2429513 : Blo 319836 2429513 := bstep (se 2 (by rfl) ⟨911067, by rfl⟩ : syracuseStep 2429513 = 1822135) B1822135
theorem B4395809 : Blo 319836 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B2233327 : Blo 319836 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2757671 : Blo 319836 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B1218023 : Blo 319836 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B726695 : Blo 319836 726695 := bstep (se 1 (by rfl) ⟨545021, by rfl⟩ : syracuseStep 726695 = 1090043) B1090043
theorem B1152755 : Blo 319836 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B1218311 : Blo 319836 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B726875 : Blo 319836 726875 := bstep (se 1 (by rfl) ⟨545156, by rfl⟩ : syracuseStep 726875 = 1090313) B1090313
theorem B1087613 : Blo 319836 1087613 := bstep (se 3 (by rfl) ⟨203927, by rfl⟩ : syracuseStep 1087613 = 407855) B407855
theorem B1087775 : Blo 319836 1087775 := bstep (se 1 (by rfl) ⟨815831, by rfl⟩ : syracuseStep 1087775 = 1631663) B1631663
theorem B727379 : Blo 319836 727379 := bstep (se 1 (by rfl) ⟨545534, by rfl⟩ : syracuseStep 727379 = 1091069) B1091069
theorem B1087883 : Blo 319836 1087883 := bstep (se 1 (by rfl) ⟨815912, by rfl⟩ : syracuseStep 1087883 = 1631825) B1631825
theorem B3086849 : Blo 319836 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B7412381 : Blo 319836 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B5675741 : Blo 319836 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B2759447 : Blo 319836 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B727865 : Blo 319836 727865 := bstep (se 2 (by rfl) ⟨272949, by rfl⟩ : syracuseStep 727865 = 545899) B545899
theorem B727919 : Blo 319836 727919 := bstep (se 1 (by rfl) ⟨545939, by rfl⟩ : syracuseStep 727919 = 1091879) B1091879
theorem B9248093 : Blo 319836 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B728495 : Blo 319836 728495 := bstep (se 1 (by rfl) ⟨546371, by rfl⟩ : syracuseStep 728495 = 1092743) B1092743
theorem B728567 : Blo 319836 728567 := bstep (se 1 (by rfl) ⟨546425, by rfl⟩ : syracuseStep 728567 = 1092851) B1092851
theorem B3317345 : Blo 319836 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B958171 : Blo 319836 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B1089503 : Blo 319836 1089503 := bstep (se 1 (by rfl) ⟨817127, by rfl⟩ : syracuseStep 1089503 = 1634255) B1634255
theorem B1089665 : Blo 319836 1089665 := bstep (se 2 (by rfl) ⟨408624, by rfl⟩ : syracuseStep 1089665 = 817249) B817249
theorem B1221227 : Blo 319836 1221227 := bstep (se 1 (by rfl) ⟨915920, by rfl⟩ : syracuseStep 1221227 = 1831841) B1831841
theorem B9904841 : Blo 319836 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B17703629 : Blo 319836 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B6169391 : Blo 319836 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B1090475 : Blo 319836 1090475 := bstep (se 1 (by rfl) ⟨817856, by rfl⟩ : syracuseStep 1090475 = 1635713) B1635713
theorem B2762045 : Blo 319836 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B11937125 : Blo 319836 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B1091015 : Blo 319836 1091015 := bstep (se 1 (by rfl) ⟨818261, by rfl⟩ : syracuseStep 1091015 = 1636523) B1636523
theorem B3123139 : Blo 319836 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B1222715 : Blo 319836 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B1386953 : Blo 319836 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B136719197 : Blo 319836 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B3484559 : Blo 319836 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B5222033 : Blo 319836 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B2436803 : Blo 319836 2436803 := bstep (se 1 (by rfl) ⟨1827602, by rfl⟩ : syracuseStep 2436803 = 3655205) B3655205
theorem B9383633 : Blo 319836 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B1225115 : Blo 319836 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B5878291 : Blo 319836 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B1225601 : Blo 319836 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B2765735 : Blo 319836 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B5190641 : Blo 319836 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B1225799 : Blo 319836 1225799 := bstep (se 1 (by rfl) ⟨919349, by rfl⟩ : syracuseStep 1225799 = 1838699) B1838699
theorem B406711 : Blo 319836 406711 := bstep (se 1 (by rfl) ⟨305033, by rfl⟩ : syracuseStep 406711 = 610067) B610067
theorem B2209451 : Blo 319836 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B866015 : Blo 319836 866015 := bstep (se 1 (by rfl) ⟨649511, by rfl⟩ : syracuseStep 866015 = 1299023) B1299023
theorem B1619837 : Blo 319836 1619837 := bstep (se 3 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 1619837 = 607439) B607439
theorem B1030283 : Blo 319836 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B1227271 : Blo 319836 1227271 := bstep (se 1 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 1227271 = 1840907) B1840907
theorem B4143635 : Blo 319836 4143635 := bstep (se 1 (by rfl) ⟨3107726, by rfl⟩ : syracuseStep 4143635 = 6215453) B6215453
theorem B2603987 : Blo 319836 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B1227757 : Blo 319836 1227757 := bstep (se 3 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 1227757 = 460409) B460409
theorem B4668515 : Blo 319836 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B1031399 : Blo 319836 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B1162471 : Blo 319836 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B4963751 : Blo 319836 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B933289 : Blo 319836 933289 := bstep (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) B699967
theorem B2211365 : Blo 319836 2211365 := bstep (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) B414631
theorem B540391 : Blo 319836 540391 := bstep (se 1 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 540391 = 810587) B810587
theorem B540425 : Blo 319836 540425 := bstep (se 2 (by rfl) ⟨202659, by rfl⟩ : syracuseStep 540425 = 405319) B405319
theorem B20299855 : Blo 319836 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B5194007 : Blo 319836 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B541289 : Blo 319836 541289 := bstep (se 2 (by rfl) ⟨202983, by rfl⟩ : syracuseStep 541289 = 405967) B405967
theorem B2736827 : Blo 319836 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B2442635 : Blo 319836 2442635 := bstep (se 1 (by rfl) ⟨1831976, by rfl⟩ : syracuseStep 2442635 = 3663953) B3663953
theorem B2737577 : Blo 319836 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B542315 : Blo 319836 542315 := bstep (se 1 (by rfl) ⟨406736, by rfl⟩ : syracuseStep 542315 = 813473) B813473
theorem B542585 : Blo 319836 542585 := bstep (se 2 (by rfl) ⟨203469, by rfl⟩ : syracuseStep 542585 = 406939) B406939
theorem B1624211 : Blo 319836 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B608411 : Blo 319836 608411 := bstep (se 1 (by rfl) ⟨456308, by rfl⟩ : syracuseStep 608411 = 912617) B912617
theorem B543145 : Blo 319836 543145 := bstep (se 2 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 543145 = 407359) B407359
theorem B4115387 : Blo 319836 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B543739 : Blo 319836 543739 := bstep (se 1 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 543739 = 815609) B815609
theorem B9457033 : Blo 319836 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B774011 : Blo 319836 774011 := bstep (se 1 (by rfl) ⟨580508, by rfl⟩ : syracuseStep 774011 = 1161017) B1161017
theorem B610591 : Blo 319836 610591 := bstep (se 1 (by rfl) ⟨457943, by rfl⟩ : syracuseStep 610591 = 915887) B915887
theorem B4149629 : Blo 319836 4149629 := bstep (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) B1556111
theorem B906209 : Blo 319836 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B611297 : Blo 319836 611297 := bstep (se 2 (by rfl) ⟨229236, by rfl⟩ : syracuseStep 611297 = 458473) B458473
theorem B480239 : Blo 319836 480239 := bstep (se 1 (by rfl) ⟨360179, by rfl⟩ : syracuseStep 480239 = 720359) B720359
theorem B2642959 : Blo 319836 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B1823867 : Blo 319836 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B480623 : Blo 319836 480623 := bstep (se 1 (by rfl) ⟨360467, by rfl⟩ : syracuseStep 480623 = 720935) B720935
theorem B480743 : Blo 319836 480743 := bstep (se 1 (by rfl) ⟨360557, by rfl⟩ : syracuseStep 480743 = 721115) B721115
theorem B480905 : Blo 319836 480905 := bstep (se 2 (by rfl) ⟨180339, by rfl⟩ : syracuseStep 480905 = 360679) B360679
theorem B480923 : Blo 319836 480923 := bstep (se 1 (by rfl) ⟨360692, by rfl⟩ : syracuseStep 480923 = 721385) B721385
theorem B2053799 : Blo 319836 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B481115 : Blo 319836 481115 := bstep (se 1 (by rfl) ⟨360836, by rfl⟩ : syracuseStep 481115 = 721673) B721673
theorem B612193 : Blo 319836 612193 := bstep (se 2 (by rfl) ⟨229572, by rfl⟩ : syracuseStep 612193 = 459145) B459145
theorem B481499 : Blo 319836 481499 := bstep (se 1 (by rfl) ⟨361124, by rfl⟩ : syracuseStep 481499 = 722249) B722249
theorem B2087279 : Blo 319836 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B612839 : Blo 319836 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B481769 : Blo 319836 481769 := bstep (se 2 (by rfl) ⟨180663, by rfl⟩ : syracuseStep 481769 = 361327) B361327
theorem B4413971 : Blo 319836 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B1858085 : Blo 319836 1858085 := bstep (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) B348391
theorem B2447981 : Blo 319836 2447981 := bstep (se 3 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 2447981 = 917993) B917993
theorem B482159 : Blo 319836 482159 := bstep (se 1 (by rfl) ⟨361619, by rfl⟩ : syracuseStep 482159 = 723239) B723239
theorem B482171 : Blo 319836 482171 := bstep (se 1 (by rfl) ⟨361628, by rfl⟩ : syracuseStep 482171 = 723257) B723257
theorem B9264131 : Blo 319836 9264131 := bstep (se 1 (by rfl) ⟨6948098, by rfl⟩ : syracuseStep 9264131 = 13896197) B13896197
theorem B613423 : Blo 319836 613423 := bstep (se 1 (by rfl) ⟨460067, by rfl⟩ : syracuseStep 613423 = 920135) B920135
theorem B1367543 : Blo 319836 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B6610447 : Blo 319836 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B515705 : Blo 319836 515705 := bstep (se 2 (by rfl) ⟨193389, by rfl⟩ : syracuseStep 515705 = 386779) B386779
theorem B483035 : Blo 319836 483035 := bstep (se 1 (by rfl) ⟨362276, by rfl⟩ : syracuseStep 483035 = 724553) B724553
theorem B8314807 : Blo 319836 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B483305 : Blo 319836 483305 := bstep (se 2 (by rfl) ⟨181239, by rfl⟩ : syracuseStep 483305 = 362479) B362479
theorem B28336139 : Blo 319836 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B2056259 : Blo 319836 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B320027 : Blo 319836 320027 := bstep (se 1 (by rfl) ⟨240020, by rfl⟩ : syracuseStep 320027 = 480041) B480041
theorem B320031 : Blo 319836 320031 := bstep (se 1 (by rfl) ⟨240023, by rfl⟩ : syracuseStep 320031 = 480047) B480047
theorem B320111 : Blo 319836 320111 := bstep (se 1 (by rfl) ⟨240083, by rfl⟩ : syracuseStep 320111 = 480167) B480167
theorem B320167 : Blo 319836 320167 := bstep (se 1 (by rfl) ⟨240125, by rfl⟩ : syracuseStep 320167 = 480251) B480251
theorem B484007 : Blo 319836 484007 := bstep (se 1 (by rfl) ⟨363005, by rfl⟩ : syracuseStep 484007 = 726011) B726011
theorem B320207 : Blo 319836 320207 := bstep (se 1 (by rfl) ⟨240155, by rfl⟩ : syracuseStep 320207 = 480311) B480311
theorem B516827 : Blo 319836 516827 := bstep (se 1 (by rfl) ⟨387620, by rfl⟩ : syracuseStep 516827 = 775241) B775241
theorem B320287 : Blo 319836 320287 := bstep (se 1 (by rfl) ⟨240215, by rfl⟩ : syracuseStep 320287 = 480431) B480431
theorem B484127 : Blo 319836 484127 := bstep (se 1 (by rfl) ⟨363095, by rfl⟩ : syracuseStep 484127 = 726191) B726191
theorem B484151 : Blo 319836 484151 := bstep (se 1 (by rfl) ⟨363113, by rfl⟩ : syracuseStep 484151 = 726227) B726227
theorem B2450411 : Blo 319836 2450411 := bstep (se 1 (by rfl) ⟨1837808, by rfl⟩ : syracuseStep 2450411 = 3675617) B3675617
theorem B484331 : Blo 319836 484331 := bstep (se 1 (by rfl) ⟨363248, by rfl⟩ : syracuseStep 484331 = 726497) B726497
theorem B320559 : Blo 319836 320559 := bstep (se 1 (by rfl) ⟨240419, by rfl⟩ : syracuseStep 320559 = 480839) B480839
theorem B320623 : Blo 319836 320623 := bstep (se 1 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 320623 = 480935) B480935
theorem B320679 : Blo 319836 320679 := bstep (se 1 (by rfl) ⟨240509, by rfl⟩ : syracuseStep 320679 = 481019) B481019
theorem B320703 : Blo 319836 320703 := bstep (se 1 (by rfl) ⟨240527, by rfl⟩ : syracuseStep 320703 = 481055) B481055
theorem B196338887 : Blo 319836 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B320735 : Blo 319836 320735 := bstep (se 1 (by rfl) ⟨240551, by rfl⟩ : syracuseStep 320735 = 481103) B481103
theorem B320815 : Blo 319836 320815 := bstep (se 1 (by rfl) ⟨240611, by rfl⟩ : syracuseStep 320815 = 481223) B481223
theorem B321051 : Blo 319836 321051 := bstep (se 1 (by rfl) ⟨240788, by rfl⟩ : syracuseStep 321051 = 481577) B481577
theorem B321055 : Blo 319836 321055 := bstep (se 1 (by rfl) ⟨240791, by rfl⟩ : syracuseStep 321055 = 481583) B481583
theorem B321215 : Blo 319836 321215 := bstep (se 1 (by rfl) ⟨240911, by rfl⟩ : syracuseStep 321215 = 481823) B481823
theorem B321471 : Blo 319836 321471 := bstep (se 1 (by rfl) ⟨241103, by rfl⟩ : syracuseStep 321471 = 482207) B482207
theorem B321503 : Blo 319836 321503 := bstep (se 1 (by rfl) ⟨241127, by rfl⟩ : syracuseStep 321503 = 482255) B482255
theorem B321563 : Blo 319836 321563 := bstep (se 1 (by rfl) ⟨241172, by rfl⟩ : syracuseStep 321563 = 482345) B482345
theorem B321567 : Blo 319836 321567 := bstep (se 1 (by rfl) ⟨241175, by rfl⟩ : syracuseStep 321567 = 482351) B482351
theorem B321583 : Blo 319836 321583 := bstep (se 1 (by rfl) ⟨241187, by rfl⟩ : syracuseStep 321583 = 482375) B482375
theorem B485423 : Blo 319836 485423 := bstep (se 1 (by rfl) ⟨364067, by rfl⟩ : syracuseStep 485423 = 728135) B728135
theorem B813179 : Blo 319836 813179 := bstep (se 1 (by rfl) ⟨609884, by rfl⟩ : syracuseStep 813179 = 1219769) B1219769
theorem B813199 : Blo 319836 813199 := bstep (se 1 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 813199 = 1219799) B1219799
theorem B321759 : Blo 319836 321759 := bstep (se 1 (by rfl) ⟨241319, by rfl⟩ : syracuseStep 321759 = 482639) B482639
theorem B321819 : Blo 319836 321819 := bstep (se 1 (by rfl) ⟨241364, by rfl⟩ : syracuseStep 321819 = 482729) B482729
theorem B485687 : Blo 319836 485687 := bstep (se 1 (by rfl) ⟨364265, by rfl⟩ : syracuseStep 485687 = 728531) B728531
theorem B321919 : Blo 319836 321919 := bstep (se 1 (by rfl) ⟨241439, by rfl⟩ : syracuseStep 321919 = 482879) B482879
theorem B322095 : Blo 319836 322095 := bstep (se 1 (by rfl) ⟨241571, by rfl⟩ : syracuseStep 322095 = 483143) B483143
theorem B322151 : Blo 319836 322151 := bstep (se 1 (by rfl) ⟨241613, by rfl⟩ : syracuseStep 322151 = 483227) B483227
theorem B1960843 : Blo 319836 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B322527 : Blo 319836 322527 := bstep (se 1 (by rfl) ⟨241895, by rfl⟩ : syracuseStep 322527 = 483791) B483791
theorem B322555 : Blo 319836 322555 := bstep (se 1 (by rfl) ⟨241916, by rfl⟩ : syracuseStep 322555 = 483833) B483833
theorem B322623 : Blo 319836 322623 := bstep (se 1 (by rfl) ⟨241967, by rfl⟩ : syracuseStep 322623 = 483935) B483935
theorem B322943 : Blo 319836 322943 := bstep (se 1 (by rfl) ⟨242207, by rfl⟩ : syracuseStep 322943 = 484415) B484415
theorem B322971 : Blo 319836 322971 := bstep (se 1 (by rfl) ⟨242228, by rfl⟩ : syracuseStep 322971 = 484457) B484457
theorem B323039 : Blo 319836 323039 := bstep (se 1 (by rfl) ⟨242279, by rfl⟩ : syracuseStep 323039 = 484559) B484559
theorem B323175 : Blo 319836 323175 := bstep (se 1 (by rfl) ⟨242381, by rfl⟩ : syracuseStep 323175 = 484763) B484763
theorem B323323 : Blo 319836 323323 := bstep (se 1 (by rfl) ⟨242492, by rfl⟩ : syracuseStep 323323 = 484985) B484985
theorem B323391 : Blo 319836 323391 := bstep (se 1 (by rfl) ⟨242543, by rfl⟩ : syracuseStep 323391 = 485087) B485087
theorem B323455 : Blo 319836 323455 := bstep (se 1 (by rfl) ⟨242591, by rfl⟩ : syracuseStep 323455 = 485183) B485183
theorem B323567 : Blo 319836 323567 := bstep (se 1 (by rfl) ⟨242675, by rfl⟩ : syracuseStep 323567 = 485351) B485351
theorem B323579 : Blo 319836 323579 := bstep (se 1 (by rfl) ⟨242684, by rfl⟩ : syracuseStep 323579 = 485369) B485369
theorem B323647 : Blo 319836 323647 := bstep (se 1 (by rfl) ⟨242735, by rfl⟩ : syracuseStep 323647 = 485471) B485471
theorem B323687 : Blo 319836 323687 := bstep (se 1 (by rfl) ⟨242765, by rfl⟩ : syracuseStep 323687 = 485531) B485531
theorem B323711 : Blo 319836 323711 := bstep (se 1 (by rfl) ⟨242783, by rfl⟩ : syracuseStep 323711 = 485567) B485567
theorem B323739 : Blo 319836 323739 := bstep (se 1 (by rfl) ⟨242804, by rfl⟩ : syracuseStep 323739 = 485609) B485609
theorem B2748923 : Blo 319836 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B3077315 : Blo 319836 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B1570079 : Blo 319836 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B816551 : Blo 319836 816551 := bstep (se 1 (by rfl) ⟨612413, by rfl⟩ : syracuseStep 816551 = 1224827) B1224827
theorem B685523 : Blo 319836 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B3307823 : Blo 319836 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B2652763 : Blo 319836 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B719783 : Blo 319836 719783 := bstep (se 1 (by rfl) ⟨539837, by rfl⟩ : syracuseStep 719783 = 1079675) B1079675
theorem B719963 : Blo 319836 719963 := bstep (se 1 (by rfl) ⟨539972, by rfl⟩ : syracuseStep 719963 = 1079945) B1079945
theorem B982297 : Blo 319836 982297 := bstep (se 2 (by rfl) ⟨368361, by rfl⟩ : syracuseStep 982297 = 736723) B736723
theorem B1637657 : Blo 319836 1637657 := bstep (se 2 (by rfl) ⟨614121, by rfl⟩ : syracuseStep 1637657 = 1228243) B1228243
theorem B359887 : Blo 319836 359887 := bstep (se 1 (by rfl) ⟨269915, by rfl⟩ : syracuseStep 359887 = 539831) B539831
theorem B818707 : Blo 319836 818707 := bstep (se 1 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 818707 = 1228061) B1228061
theorem B360103 : Blo 319836 360103 := bstep (se 1 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 360103 = 540155) B540155
theorem B720719 : Blo 319836 720719 := bstep (se 1 (by rfl) ⟨540539, by rfl⟩ : syracuseStep 720719 = 1081079) B1081079
theorem B360391 : Blo 319836 360391 := bstep (se 1 (by rfl) ⟨270293, by rfl⟩ : syracuseStep 360391 = 540587) B540587
theorem B655303 : Blo 319836 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B819143 : Blo 319836 819143 := bstep (se 1 (by rfl) ⟨614357, by rfl⟩ : syracuseStep 819143 = 1228715) B1228715
theorem B27066473 : Blo 319836 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B1835257 : Blo 319836 1835257 := bstep (se 2 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 1835257 = 1376443) B1376443
theorem B721151 : Blo 319836 721151 := bstep (se 1 (by rfl) ⟨540863, by rfl⟩ : syracuseStep 721151 = 1081727) B1081727
theorem B360859 : Blo 319836 360859 := bstep (se 1 (by rfl) ⟨270644, by rfl⟩ : syracuseStep 360859 = 541289) B541289
theorem B3080663 : Blo 319836 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B721727 : Blo 319836 721727 := bstep (se 1 (by rfl) ⟨541295, by rfl⟩ : syracuseStep 721727 = 1082591) B1082591
theorem B525127 : Blo 319836 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B361543 : Blo 319836 361543 := bstep (se 1 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 361543 = 542315) B542315
theorem B361723 : Blo 319836 361723 := bstep (se 1 (by rfl) ⟨271292, by rfl⟩ : syracuseStep 361723 = 542585) B542585
theorem B1082807 : Blo 319836 1082807 := bstep (se 1 (by rfl) ⟨812105, by rfl⟩ : syracuseStep 1082807 = 1624211) B1624211
theorem B1836715 : Blo 319836 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B788363 : Blo 319836 788363 := bstep (se 1 (by rfl) ⟨591272, by rfl⟩ : syracuseStep 788363 = 1182545) B1182545
theorem B1378205 : Blo 319836 1378205 := bstep (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) B516827
theorem B722879 : Blo 319836 722879 := bstep (se 1 (by rfl) ⟨542159, by rfl⟩ : syracuseStep 722879 = 1084319) B1084319
theorem B4164185 : Blo 319836 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B1084265 : Blo 319836 1084265 := bstep (se 2 (by rfl) ⟨406599, by rfl⟩ : syracuseStep 1084265 = 813199) B813199
theorem B723923 : Blo 319836 723923 := bstep (se 1 (by rfl) ⟨542942, by rfl⟩ : syracuseStep 723923 = 1085885) B1085885
theorem B724193 : Blo 319836 724193 := bstep (se 2 (by rfl) ⟨271572, by rfl⟩ : syracuseStep 724193 = 543145) B543145
theorem B1838447 : Blo 319836 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B1215911 : Blo 319836 1215911 := bstep (se 1 (by rfl) ⟨911933, by rfl⟩ : syracuseStep 1215911 = 1823867) B1823867
theorem B724985 : Blo 319836 724985 := bstep (se 2 (by rfl) ⟨271869, by rfl⟩ : syracuseStep 724985 = 543739) B543739
theorem B921593 : Blo 319836 921593 := bstep (se 2 (by rfl) ⟨345597, by rfl⟩ : syracuseStep 921593 = 691195) B691195
theorem B725075 : Blo 319836 725075 := bstep (se 1 (by rfl) ⟨543806, by rfl⟩ : syracuseStep 725075 = 1087613) B1087613
theorem B725183 : Blo 319836 725183 := bstep (se 1 (by rfl) ⟨543887, by rfl⟩ : syracuseStep 725183 = 1087775) B1087775
theorem B725255 : Blo 319836 725255 := bstep (se 1 (by rfl) ⟨543941, by rfl⟩ : syracuseStep 725255 = 1087883) B1087883
theorem B1839631 : Blo 319836 1839631 := bstep (se 1 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 1839631 = 2759447) B2759447
theorem B6165395 : Blo 319836 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B726335 : Blo 319836 726335 := bstep (se 1 (by rfl) ⟨544751, by rfl⟩ : syracuseStep 726335 = 1089503) B1089503
theorem B726443 : Blo 319836 726443 := bstep (se 1 (by rfl) ⟨544832, by rfl⟩ : syracuseStep 726443 = 1089665) B1089665
theorem B11802419 : Blo 319836 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B726983 : Blo 319836 726983 := bstep (se 1 (by rfl) ⟨545237, by rfl⟩ : syracuseStep 726983 = 1090475) B1090475
theorem B7837721 : Blo 319836 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B1841363 : Blo 319836 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B727343 : Blo 319836 727343 := bstep (se 1 (by rfl) ⟨545507, by rfl⟩ : syracuseStep 727343 = 1091015) B1091015
theorem B11770589 : Blo 319836 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B924635 : Blo 319836 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B3481355 : Blo 319836 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1843823 : Blo 319836 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B2205215 : Blo 319836 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B1549961 : Blo 319836 1549961 := bstep (se 2 (by rfl) ⟨581235, by rfl⟩ : syracuseStep 1549961 = 1162471) B1162471
theorem B2762423 : Blo 319836 2762423 := bstep (se 1 (by rfl) ⟨2071817, by rfl⟩ : syracuseStep 2762423 = 4143635) B4143635
theorem B1091609 : Blo 319836 1091609 := bstep (se 2 (by rfl) ⟨409353, by rfl⟩ : syracuseStep 1091609 = 818707) B818707
theorem B1091771 : Blo 319836 1091771 := bstep (se 1 (by rfl) ⟨818828, by rfl⟩ : syracuseStep 1091771 = 1637657) B1637657
theorem B11086409 : Blo 319836 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B895943 : Blo 319836 895943 := bstep (se 1 (by rfl) ⟨671957, by rfl⟩ : syracuseStep 895943 = 1343915) B1343915
theorem B2766419 : Blo 319836 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B1619675 : Blo 319836 1619675 := bstep (se 1 (by rfl) ⟨1214756, by rfl⟩ : syracuseStep 1619675 = 2429513) B2429513
theorem B2930539 : Blo 319836 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B604139 : Blo 319836 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B407531 : Blo 319836 407531 := bstep (se 1 (by rfl) ⟨305648, by rfl⟩ : syracuseStep 407531 = 611297) B611297
theorem B768503 : Blo 319836 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B1391519 : Blo 319836 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B408559 : Blo 319836 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B3783827 : Blo 319836 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B6176087 : Blo 319836 6176087 := bstep (se 1 (by rfl) ⟨4632065, by rfl⟩ : syracuseStep 6176087 = 9264131) B9264131
theorem B2211563 : Blo 319836 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B18890759 : Blo 319836 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B1622429 : Blo 319836 1622429 := bstep (se 3 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 1622429 = 608411) B608411
theorem B6603227 : Blo 319836 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B4112927 : Blo 319836 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B130892591 : Blo 319836 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B3523945 : Blo 319836 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B542119 : Blo 319836 542119 := bstep (se 1 (by rfl) ⟨406589, by rfl⟩ : syracuseStep 542119 = 813179) B813179
theorem B542281 : Blo 319836 542281 := bstep (se 2 (by rfl) ⟨203355, by rfl⟩ : syracuseStep 542281 = 406711) B406711
theorem B91146131 : Blo 319836 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B1624535 : Blo 319836 1624535 := bstep (se 1 (by rfl) ⟨1218401, by rfl⟩ : syracuseStep 1624535 = 2436803) B2436803
theorem B3460427 : Blo 319836 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B2051543 : Blo 319836 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B544367 : Blo 319836 544367 := bstep (se 1 (by rfl) ⟨408275, by rfl⟩ : syracuseStep 544367 = 816551) B816551
theorem B577343 : Blo 319836 577343 := bstep (se 1 (by rfl) ⟨433007, by rfl⟩ : syracuseStep 577343 = 866015) B866015
theorem B479849 : Blo 319836 479849 := bstep (se 2 (by rfl) ⟨179943, by rfl⟩ : syracuseStep 479849 = 359887) B359887
theorem B479855 : Blo 319836 479855 := bstep (se 1 (by rfl) ⟨359891, by rfl⟩ : syracuseStep 479855 = 719783) B719783
theorem B479975 : Blo 319836 479975 := bstep (se 1 (by rfl) ⟨359981, by rfl⟩ : syracuseStep 479975 = 719963) B719963
theorem B480137 : Blo 319836 480137 := bstep (se 2 (by rfl) ⟨180051, by rfl⟩ : syracuseStep 480137 = 360103) B360103
theorem B480479 : Blo 319836 480479 := bstep (se 1 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 480479 = 720719) B720719
theorem B480521 : Blo 319836 480521 := bstep (se 2 (by rfl) ⟨180195, by rfl⟩ : syracuseStep 480521 = 360391) B360391
theorem B873737 : Blo 319836 873737 := bstep (se 2 (by rfl) ⟨327651, by rfl⟩ : syracuseStep 873737 = 655303) B655303
theorem B546095 : Blo 319836 546095 := bstep (se 1 (by rfl) ⟨409571, by rfl⟩ : syracuseStep 546095 = 819143) B819143
theorem B3462671 : Blo 319836 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B480959 : Blo 319836 480959 := bstep (se 1 (by rfl) ⟨360719, by rfl⟩ : syracuseStep 480959 = 721439) B721439
theorem B481001 : Blo 319836 481001 := bstep (se 2 (by rfl) ⟨180375, by rfl⟩ : syracuseStep 481001 = 360751) B360751
theorem B481007 : Blo 319836 481007 := bstep (se 1 (by rfl) ⟨360755, by rfl⟩ : syracuseStep 481007 = 721511) B721511
theorem B1824551 : Blo 319836 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B481511 : Blo 319836 481511 := bstep (se 1 (by rfl) ⟨361133, by rfl⟩ : syracuseStep 481511 = 722267) B722267
theorem B1628423 : Blo 319836 1628423 := bstep (se 1 (by rfl) ⟨1221317, by rfl⟩ : syracuseStep 1628423 = 2442635) B2442635
theorem B1825051 : Blo 319836 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B481691 : Blo 319836 481691 := bstep (se 1 (by rfl) ⟨361268, by rfl⟩ : syracuseStep 481691 = 722537) B722537
theorem B482087 : Blo 319836 482087 := bstep (se 1 (by rfl) ⟨361565, by rfl⟩ : syracuseStep 482087 = 723131) B723131
theorem B482111 : Blo 319836 482111 := bstep (se 1 (by rfl) ⟨361583, by rfl⟩ : syracuseStep 482111 = 723167) B723167
theorem B809939 : Blo 319836 809939 := bstep (se 1 (by rfl) ⟨607454, by rfl⟩ : syracuseStep 809939 = 1214909) B1214909
theorem B482411 : Blo 319836 482411 := bstep (se 1 (by rfl) ⟨361808, by rfl⟩ : syracuseStep 482411 = 723617) B723617
theorem B482555 : Blo 319836 482555 := bstep (se 1 (by rfl) ⟨361916, by rfl⟩ : syracuseStep 482555 = 723833) B723833
theorem B2743591 : Blo 319836 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B482651 : Blo 319836 482651 := bstep (se 1 (by rfl) ⟨361988, by rfl⟩ : syracuseStep 482651 = 723977) B723977
theorem B482681 : Blo 319836 482681 := bstep (se 2 (by rfl) ⟨181005, by rfl⟩ : syracuseStep 482681 = 362011) B362011
theorem B482687 : Blo 319836 482687 := bstep (se 1 (by rfl) ⟨362015, by rfl⟩ : syracuseStep 482687 = 724031) B724031
theorem B810719 : Blo 319836 810719 := bstep (se 1 (by rfl) ⟨608039, by rfl⟩ : syracuseStep 810719 = 1216079) B1216079
theorem B516007 : Blo 319836 516007 := bstep (se 1 (by rfl) ⟨387005, by rfl⟩ : syracuseStep 516007 = 774011) B774011
theorem B483239 : Blo 319836 483239 := bstep (se 1 (by rfl) ⟨362429, by rfl⟩ : syracuseStep 483239 = 724859) B724859
theorem B483311 : Blo 319836 483311 := bstep (se 1 (by rfl) ⟨362483, by rfl⟩ : syracuseStep 483311 = 724967) B724967
theorem B614441 : Blo 319836 614441 := bstep (se 2 (by rfl) ⟨230415, by rfl⟩ : syracuseStep 614441 = 460831) B460831
theorem B483431 : Blo 319836 483431 := bstep (se 1 (by rfl) ⟨362573, by rfl⟩ : syracuseStep 483431 = 725147) B725147
theorem B2318483 : Blo 319836 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B483563 : Blo 319836 483563 := bstep (se 1 (by rfl) ⟨362672, by rfl⟩ : syracuseStep 483563 = 725345) B725345
theorem B483623 : Blo 319836 483623 := bstep (se 1 (by rfl) ⟨362717, by rfl⟩ : syracuseStep 483623 = 725435) B725435
theorem B320159 : Blo 319836 320159 := bstep (se 1 (by rfl) ⟨240119, by rfl⟩ : syracuseStep 320159 = 480239) B480239
theorem B484073 : Blo 319836 484073 := bstep (se 2 (by rfl) ⟨181527, by rfl⟩ : syracuseStep 484073 = 363055) B363055
theorem B320415 : Blo 319836 320415 := bstep (se 1 (by rfl) ⟨240311, by rfl⟩ : syracuseStep 320415 = 480623) B480623
theorem B320495 : Blo 319836 320495 := bstep (se 1 (by rfl) ⟨240371, by rfl⟩ : syracuseStep 320495 = 480743) B480743
theorem B812015 : Blo 319836 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B320603 : Blo 319836 320603 := bstep (se 1 (by rfl) ⟨240452, by rfl⟩ : syracuseStep 320603 = 480905) B480905
theorem B320615 : Blo 319836 320615 := bstep (se 1 (by rfl) ⟨240461, by rfl⟩ : syracuseStep 320615 = 480923) B480923
theorem B1369199 : Blo 319836 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B484463 : Blo 319836 484463 := bstep (se 1 (by rfl) ⟨363347, by rfl⟩ : syracuseStep 484463 = 726695) B726695
theorem B812207 : Blo 319836 812207 := bstep (se 1 (by rfl) ⟨609155, by rfl⟩ : syracuseStep 812207 = 1218311) B1218311
theorem B2614457 : Blo 319836 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B320743 : Blo 319836 320743 := bstep (se 1 (by rfl) ⟨240557, by rfl⟩ : syracuseStep 320743 = 481115) B481115
theorem B484583 : Blo 319836 484583 := bstep (se 1 (by rfl) ⟨363437, by rfl⟩ : syracuseStep 484583 = 726875) B726875
theorem B484649 : Blo 319836 484649 := bstep (se 2 (by rfl) ⟨181743, by rfl⟩ : syracuseStep 484649 = 363487) B363487
theorem B320999 : Blo 319836 320999 := bstep (se 1 (by rfl) ⟨240749, by rfl⟩ : syracuseStep 320999 = 481499) B481499
theorem B1664509 : Blo 319836 1664509 := bstep (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) B624191
theorem B484919 : Blo 319836 484919 := bstep (se 1 (by rfl) ⟨363689, by rfl⟩ : syracuseStep 484919 = 727379) B727379
theorem B321179 : Blo 319836 321179 := bstep (se 1 (by rfl) ⟨240884, by rfl⟩ : syracuseStep 321179 = 481769) B481769
theorem B2057899 : Blo 319836 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B1238723 : Blo 319836 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B1631987 : Blo 319836 1631987 := bstep (se 1 (by rfl) ⟨1223990, by rfl⟩ : syracuseStep 1631987 = 2447981) B2447981
theorem B4941587 : Blo 319836 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B5891869 : Blo 319836 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B12609377 : Blo 319836 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B485243 : Blo 319836 485243 := bstep (se 1 (by rfl) ⟨363932, by rfl⟩ : syracuseStep 485243 = 727865) B727865
theorem B321439 : Blo 319836 321439 := bstep (se 1 (by rfl) ⟨241079, by rfl⟩ : syracuseStep 321439 = 482159) B482159
theorem B485279 : Blo 319836 485279 := bstep (se 1 (by rfl) ⟨363959, by rfl⟩ : syracuseStep 485279 = 727919) B727919
theorem B321447 : Blo 319836 321447 := bstep (se 1 (by rfl) ⟨241085, by rfl⟩ : syracuseStep 321447 = 482171) B482171
theorem B485513 : Blo 319836 485513 := bstep (se 2 (by rfl) ⟨182067, by rfl⟩ : syracuseStep 485513 = 364135) B364135
theorem B485663 : Blo 319836 485663 := bstep (se 1 (by rfl) ⟨364247, by rfl⟩ : syracuseStep 485663 = 728495) B728495
theorem B911695 : Blo 319836 911695 := bstep (se 1 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 911695 = 1367543) B1367543
theorem B485711 : Blo 319836 485711 := bstep (se 1 (by rfl) ⟨364283, by rfl⟩ : syracuseStep 485711 = 728567) B728567
theorem B322023 : Blo 319836 322023 := bstep (se 1 (by rfl) ⟨241517, by rfl⟩ : syracuseStep 322023 = 483035) B483035
theorem B322203 : Blo 319836 322203 := bstep (se 1 (by rfl) ⟨241652, by rfl⟩ : syracuseStep 322203 = 483305) B483305
theorem B1370839 : Blo 319836 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B814121 : Blo 319836 814121 := bstep (se 2 (by rfl) ⟨305295, by rfl⟩ : syracuseStep 814121 = 610591) B610591
theorem B814151 : Blo 319836 814151 := bstep (se 1 (by rfl) ⟨610613, by rfl⟩ : syracuseStep 814151 = 1221227) B1221227
theorem B322671 : Blo 319836 322671 := bstep (se 1 (by rfl) ⟨242003, by rfl⟩ : syracuseStep 322671 = 484007) B484007
theorem B322751 : Blo 319836 322751 := bstep (se 1 (by rfl) ⟨242063, by rfl⟩ : syracuseStep 322751 = 484127) B484127
theorem B322767 : Blo 319836 322767 := bstep (se 1 (by rfl) ⟨242075, by rfl⟩ : syracuseStep 322767 = 484151) B484151
theorem B1633607 : Blo 319836 1633607 := bstep (se 1 (by rfl) ⟨1225205, by rfl⟩ : syracuseStep 1633607 = 2450411) B2450411
theorem B322887 : Blo 319836 322887 := bstep (se 1 (by rfl) ⟨242165, by rfl⟩ : syracuseStep 322887 = 484331) B484331
theorem B7958083 : Blo 319836 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B2977769 : Blo 319836 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B323615 : Blo 319836 323615 := bstep (se 1 (by rfl) ⟨242711, by rfl⟩ : syracuseStep 323615 = 485423) B485423
theorem B815143 : Blo 319836 815143 := bstep (se 1 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 815143 = 1222715) B1222715
theorem B323791 : Blo 319836 323791 := bstep (se 1 (by rfl) ⟨242843, by rfl⟩ : syracuseStep 323791 = 485687) B485687
theorem B2323039 : Blo 319836 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B4977541 : Blo 319836 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B816257 : Blo 319836 816257 := bstep (se 2 (by rfl) ⟨306096, by rfl⟩ : syracuseStep 816257 = 612193) B612193
theorem B6255755 : Blo 319836 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B816743 : Blo 319836 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1832615 : Blo 319836 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B817067 : Blo 319836 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B1636361 : Blo 319836 1636361 := bstep (se 2 (by rfl) ⟨613635, by rfl⟩ : syracuseStep 1636361 = 1227271) B1227271
theorem B817199 : Blo 319836 817199 := bstep (se 1 (by rfl) ⟨612899, by rfl⟩ : syracuseStep 817199 = 1225799) B1225799
theorem B3537017 : Blo 319836 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1046719 : Blo 319836 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B457015 : Blo 319836 457015 := bstep (se 1 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 457015 = 685523) B685523
theorem B1079891 : Blo 319836 1079891 := bstep (se 1 (by rfl) ⟨809918, by rfl⟩ : syracuseStep 1079891 = 1619837) B1619837
theorem B1637009 : Blo 319836 1637009 := bstep (se 2 (by rfl) ⟨613878, by rfl⟩ : syracuseStep 1637009 = 1227757) B1227757
theorem B817897 : Blo 319836 817897 := bstep (se 2 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 817897 = 613423) B613423
theorem B686855 : Blo 319836 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B28146653 : Blo 319836 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B1375213 : Blo 319836 1375213 := bstep (se 3 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 1375213 = 515705) B515705
theorem B1309729 : Blo 319836 1309729 := bstep (se 2 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 1309729 = 982297) B982297
theorem B1735991 : Blo 319836 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B8813929 : Blo 319836 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B3112343 : Blo 319836 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B687599 : Blo 319836 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B3309167 : Blo 319836 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B1277561 : Blo 319836 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B720521 : Blo 319836 720521 := bstep (se 2 (by rfl) ⟨270195, by rfl⟩ : syracuseStep 720521 = 540391) B540391
theorem B1474243 : Blo 319836 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B360283 : Blo 319836 360283 := bstep (se 1 (by rfl) ⟨270212, by rfl⟩ : syracuseStep 360283 = 540425) B540425
theorem B1081619 : Blo 319836 1081619 := bstep (se 1 (by rfl) ⟨811214, by rfl⟩ : syracuseStep 1081619 = 1622429) B1622429
theorem B721871 : Blo 319836 721871 := bstep (se 1 (by rfl) ⟨541403, by rfl⟩ : syracuseStep 721871 = 1082807) B1082807
theorem B525575 : Blo 319836 525575 := bstep (se 1 (by rfl) ⟨394181, by rfl⟩ : syracuseStep 525575 = 788363) B788363
theorem B918803 : Blo 319836 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B1083023 : Blo 319836 1083023 := bstep (se 1 (by rfl) ⟨812267, by rfl⟩ : syracuseStep 1083023 = 1624535) B1624535
theorem B722825 : Blo 319836 722825 := bstep (se 2 (by rfl) ⟨271059, by rfl⟩ : syracuseStep 722825 = 542119) B542119
theorem B722843 : Blo 319836 722843 := bstep (se 1 (by rfl) ⟨542132, by rfl⟩ : syracuseStep 722843 = 1084265) B1084265
theorem B723041 : Blo 319836 723041 := bstep (se 2 (by rfl) ⟨271140, by rfl⟩ : syracuseStep 723041 = 542281) B542281
theorem B349046909 : Blo 319836 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B362911 : Blo 319836 362911 := bstep (se 1 (by rfl) ⟨272183, by rfl⟩ : syracuseStep 362911 = 544367) B544367
theorem B1215593 : Blo 319836 1215593 := bstep (se 2 (by rfl) ⟨455847, by rfl⟩ : syracuseStep 1215593 = 911695) B911695
theorem B364063 : Blo 319836 364063 := bstep (se 1 (by rfl) ⟨273047, by rfl⟩ : syracuseStep 364063 = 546095) B546095
theorem B1216367 : Blo 319836 1216367 := bstep (se 1 (by rfl) ⟨912275, by rfl⟩ : syracuseStep 1216367 = 1824551) B1824551
theorem B7868279 : Blo 319836 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B1085615 : Blo 319836 1085615 := bstep (se 1 (by rfl) ⟨814211, by rfl⟩ : syracuseStep 1085615 = 1628423) B1628423
theorem B26546885 : Blo 319836 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B13177565 : Blo 319836 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B1611037 : Blo 319836 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B1086749 : Blo 319836 1086749 := bstep (se 3 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 1086749 = 407531) B407531
theorem B1086857 : Blo 319836 1086857 := bstep (se 2 (by rfl) ⟨407571, by rfl⟩ : syracuseStep 1086857 = 815143) B815143
theorem B1545655 : Blo 319836 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B1742971 : Blo 319836 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B1841615 : Blo 319836 1841615 := bstep (se 1 (by rfl) ⟨1381211, by rfl⟩ : syracuseStep 1841615 = 2762423) B2762423
theorem B825815 : Blo 319836 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B1087991 : Blo 319836 1087991 := bstep (se 1 (by rfl) ⟨815993, by rfl⟩ : syracuseStep 1087991 = 1631987) B1631987
theorem B727739 : Blo 319836 727739 := bstep (se 1 (by rfl) ⟨545804, by rfl⟩ : syracuseStep 727739 = 1091609) B1091609
theorem B727847 : Blo 319836 727847 := bstep (se 1 (by rfl) ⟨545885, by rfl⟩ : syracuseStep 727847 = 1091771) B1091771
theorem B597295 : Blo 319836 597295 := bstep (se 1 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 597295 = 895943) B895943
theorem B1089071 : Blo 319836 1089071 := bstep (se 1 (by rfl) ⟨816803, by rfl⟩ : syracuseStep 1089071 = 1633607) B1633607
theorem B3907385 : Blo 319836 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B2433401 : Blo 319836 2433401 := bstep (se 2 (by rfl) ⟨912525, by rfl⟩ : syracuseStep 2433401 = 1825051) B1825051
theorem B4170503 : Blo 319836 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B1090529 : Blo 319836 1090529 := bstep (se 2 (by rfl) ⟨408948, by rfl⟩ : syracuseStep 1090529 = 817897) B817897
theorem B1844279 : Blo 319836 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B1221743 : Blo 319836 1221743 := bstep (se 1 (by rfl) ⟨916307, by rfl⟩ : syracuseStep 1221743 = 1832615) B1832615
theorem B1090907 : Blo 319836 1090907 := bstep (se 1 (by rfl) ⟨818180, by rfl⟩ : syracuseStep 1090907 = 1636361) B1636361
theorem B1746305 : Blo 319836 1746305 := bstep (se 2 (by rfl) ⟨654864, by rfl⟩ : syracuseStep 1746305 = 1309729) B1309729
theorem B1091339 : Blo 319836 1091339 := bstep (se 1 (by rfl) ⟨818504, by rfl⟩ : syracuseStep 1091339 = 1637009) B1637009
theorem B927679 : Blo 319836 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B1157327 : Blo 319836 1157327 := bstep (se 1 (by rfl) ⟨867995, by rfl⟩ : syracuseStep 1157327 = 1735991) B1735991
theorem B2074895 : Blo 319836 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B2206111 : Blo 319836 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B7940717 : Blo 319836 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B12593839 : Blo 319836 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B4402151 : Blo 319836 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B700169 : Blo 319836 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B60764087 : Blo 319836 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B4698593 : Blo 319836 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B2306951 : Blo 319836 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B1225631 : Blo 319836 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B4110263 : Blo 319836 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B2308447 : Blo 319836 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B5225147 : Blo 319836 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B1227575 : Blo 319836 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B7847059 : Blo 319836 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B539959 : Blo 319836 539959 := bstep (se 1 (by rfl) ⟨404969, by rfl⟩ : syracuseStep 539959 = 809939) B809939
theorem B540479 : Blo 319836 540479 := bstep (se 1 (by rfl) ⟨405359, by rfl⟩ : syracuseStep 540479 = 810719) B810719
theorem B409627 : Blo 319836 409627 := bstep (se 1 (by rfl) ⟨307220, by rfl⟩ : syracuseStep 409627 = 614441) B614441
theorem B1229215 : Blo 319836 1229215 := bstep (se 1 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 1229215 = 1843823) B1843823
theorem B541343 : Blo 319836 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B541471 : Blo 319836 541471 := bstep (se 1 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 541471 = 812207) B812207
theorem B3097385 : Blo 319836 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B1033307 : Blo 319836 1033307 := bstep (se 1 (by rfl) ⟨774980, by rfl⟩ : syracuseStep 1033307 = 1549961) B1549961
theorem B8406251 : Blo 319836 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B7390939 : Blo 319836 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B542747 : Blo 319836 542747 := bstep (se 1 (by rfl) ⟨407060, by rfl⟩ : syracuseStep 542747 = 814121) B814121
theorem B542767 : Blo 319836 542767 := bstep (se 1 (by rfl) ⟨407075, by rfl⟩ : syracuseStep 542767 = 814151) B814151
theorem B1395625 : Blo 319836 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B609353 : Blo 319836 609353 := bstep (se 2 (by rfl) ⟨228507, by rfl⟩ : syracuseStep 609353 = 457015) B457015
theorem B544171 : Blo 319836 544171 := bstep (se 1 (by rfl) ⟨408128, by rfl⟩ : syracuseStep 544171 = 816257) B816257
theorem B544495 : Blo 319836 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B544711 : Blo 319836 544711 := bstep (se 1 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 544711 = 817067) B817067
theorem B544745 : Blo 319836 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B544799 : Blo 319836 544799 := bstep (se 1 (by rfl) ⟨408599, by rfl⟩ : syracuseStep 544799 = 817199) B817199
theorem B512335 : Blo 319836 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B3658121 : Blo 319836 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B11751905 : Blo 319836 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B18764435 : Blo 319836 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B4117391 : Blo 319836 4117391 := bstep (se 1 (by rfl) ⟨3088043, by rfl⟩ : syracuseStep 4117391 = 6176087) B6176087
theorem B480347 : Blo 319836 480347 := bstep (se 1 (by rfl) ⟨360260, by rfl⟩ : syracuseStep 480347 = 720521) B720521
theorem B480377 : Blo 319836 480377 := bstep (se 2 (by rfl) ⟨180141, by rfl⟩ : syracuseStep 480377 = 360283) B360283
theorem B18044315 : Blo 319836 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B480767 : Blo 319836 480767 := bstep (se 1 (by rfl) ⟨360575, by rfl⟩ : syracuseStep 480767 = 721151) B721151
theorem B2053775 : Blo 319836 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B2447009 : Blo 319836 2447009 := bstep (se 2 (by rfl) ⟨917628, by rfl⟩ : syracuseStep 2447009 = 1835257) B1835257
theorem B2741951 : Blo 319836 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B481145 : Blo 319836 481145 := bstep (se 2 (by rfl) ⟨180429, by rfl⟩ : syracuseStep 481145 = 360859) B360859
theorem B481151 : Blo 319836 481151 := bstep (se 1 (by rfl) ⟨360863, by rfl⟩ : syracuseStep 481151 = 721727) B721727
theorem B481919 : Blo 319836 481919 := bstep (se 1 (by rfl) ⟨361439, by rfl⟩ : syracuseStep 481919 = 722879) B722879
theorem B482057 : Blo 319836 482057 := bstep (se 2 (by rfl) ⟨180771, by rfl⟩ : syracuseStep 482057 = 361543) B361543
theorem B482297 : Blo 319836 482297 := bstep (se 2 (by rfl) ⟨180861, by rfl⟩ : syracuseStep 482297 = 361723) B361723
theorem B2776123 : Blo 319836 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B482615 : Blo 319836 482615 := bstep (se 1 (by rfl) ⟨361961, by rfl⟩ : syracuseStep 482615 = 723923) B723923
theorem B2219345 : Blo 319836 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B482795 : Blo 319836 482795 := bstep (se 1 (by rfl) ⟨362096, by rfl⟩ : syracuseStep 482795 = 724193) B724193
theorem B2743865 : Blo 319836 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B2448953 : Blo 319836 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B810607 : Blo 319836 810607 := bstep (se 1 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 810607 = 1215911) B1215911
theorem B1367695 : Blo 319836 1367695 := bstep (se 1 (by rfl) ⟨1025771, by rfl⟩ : syracuseStep 1367695 = 2051543) B2051543
theorem B7855825 : Blo 319836 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B384895 : Blo 319836 384895 := bstep (se 1 (by rfl) ⟨288671, by rfl⟩ : syracuseStep 384895 = 577343) B577343
theorem B483323 : Blo 319836 483323 := bstep (se 1 (by rfl) ⟨362492, by rfl⟩ : syracuseStep 483323 = 724985) B724985
theorem B614395 : Blo 319836 614395 := bstep (se 1 (by rfl) ⟨460796, by rfl⟩ : syracuseStep 614395 = 921593) B921593
theorem B483383 : Blo 319836 483383 := bstep (se 1 (by rfl) ⟨362537, by rfl⟩ : syracuseStep 483383 = 725075) B725075
theorem B483455 : Blo 319836 483455 := bstep (se 1 (by rfl) ⟨362591, by rfl⟩ : syracuseStep 483455 = 725183) B725183
theorem B483503 : Blo 319836 483503 := bstep (se 1 (by rfl) ⟨362627, by rfl⟩ : syracuseStep 483503 = 725255) B725255
theorem B319899 : Blo 319836 319899 := bstep (se 1 (by rfl) ⟨239924, by rfl⟩ : syracuseStep 319899 = 479849) B479849
theorem B319903 : Blo 319836 319903 := bstep (se 1 (by rfl) ⟨239927, by rfl⟩ : syracuseStep 319903 = 479855) B479855
theorem B319983 : Blo 319836 319983 := bstep (se 1 (by rfl) ⟨239987, by rfl⟩ : syracuseStep 319983 = 479975) B479975
theorem B320091 : Blo 319836 320091 := bstep (se 1 (by rfl) ⟨240068, by rfl⟩ : syracuseStep 320091 = 480137) B480137
theorem B320319 : Blo 319836 320319 := bstep (se 1 (by rfl) ⟨240239, by rfl⟩ : syracuseStep 320319 = 480479) B480479
theorem B320347 : Blo 319836 320347 := bstep (se 1 (by rfl) ⟨240260, by rfl⟩ : syracuseStep 320347 = 480521) B480521
theorem B582491 : Blo 319836 582491 := bstep (se 1 (by rfl) ⟨436868, by rfl⟩ : syracuseStep 582491 = 873737) B873737
theorem B484223 : Blo 319836 484223 := bstep (se 1 (by rfl) ⟨363167, by rfl⟩ : syracuseStep 484223 = 726335) B726335
theorem B484295 : Blo 319836 484295 := bstep (se 1 (by rfl) ⟨363221, by rfl⟩ : syracuseStep 484295 = 726443) B726443
theorem B1827785 : Blo 319836 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B320639 : Blo 319836 320639 := bstep (se 1 (by rfl) ⟨240479, by rfl⟩ : syracuseStep 320639 = 480959) B480959
theorem B320667 : Blo 319836 320667 := bstep (se 1 (by rfl) ⟨240500, by rfl⟩ : syracuseStep 320667 = 481001) B481001
theorem B320671 : Blo 319836 320671 := bstep (se 1 (by rfl) ⟨240503, by rfl⟩ : syracuseStep 320671 = 481007) B481007
theorem B484655 : Blo 319836 484655 := bstep (se 1 (by rfl) ⟨363491, by rfl⟩ : syracuseStep 484655 = 726983) B726983
theorem B31450517 : Blo 319836 31450517 := bstep (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) B1474243
theorem B321007 : Blo 319836 321007 := bstep (se 1 (by rfl) ⟨240755, by rfl⟩ : syracuseStep 321007 = 481511) B481511
theorem B484895 : Blo 319836 484895 := bstep (se 1 (by rfl) ⟨363671, by rfl⟩ : syracuseStep 484895 = 727343) B727343
theorem B321127 : Blo 319836 321127 := bstep (se 1 (by rfl) ⟨240845, by rfl⟩ : syracuseStep 321127 = 481691) B481691
theorem B321391 : Blo 319836 321391 := bstep (se 1 (by rfl) ⟨241043, by rfl⟩ : syracuseStep 321391 = 482087) B482087
theorem B321407 : Blo 319836 321407 := bstep (se 1 (by rfl) ⟨241055, by rfl⟩ : syracuseStep 321407 = 482111) B482111
theorem B616423 : Blo 319836 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B321607 : Blo 319836 321607 := bstep (se 1 (by rfl) ⟨241205, by rfl⟩ : syracuseStep 321607 = 482411) B482411
theorem B10610777 : Blo 319836 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B321703 : Blo 319836 321703 := bstep (se 1 (by rfl) ⟨241277, by rfl⟩ : syracuseStep 321703 = 482555) B482555
theorem B321767 : Blo 319836 321767 := bstep (se 1 (by rfl) ⟨241325, by rfl⟩ : syracuseStep 321767 = 482651) B482651
theorem B321787 : Blo 319836 321787 := bstep (se 1 (by rfl) ⟨241340, by rfl⟩ : syracuseStep 321787 = 482681) B482681
theorem B321791 : Blo 319836 321791 := bstep (se 1 (by rfl) ⟨241343, by rfl⟩ : syracuseStep 321791 = 482687) B482687
theorem B2320903 : Blo 319836 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B322159 : Blo 319836 322159 := bstep (se 1 (by rfl) ⟨241619, by rfl⟩ : syracuseStep 322159 = 483239) B483239
theorem B322207 : Blo 319836 322207 := bstep (se 1 (by rfl) ⟨241655, by rfl⟩ : syracuseStep 322207 = 483311) B483311
theorem B322287 : Blo 319836 322287 := bstep (se 1 (by rfl) ⟨241715, by rfl⟩ : syracuseStep 322287 = 483431) B483431
theorem B322375 : Blo 319836 322375 := bstep (se 1 (by rfl) ⟨241781, by rfl⟩ : syracuseStep 322375 = 483563) B483563
theorem B322415 : Blo 319836 322415 := bstep (se 1 (by rfl) ⟨241811, by rfl⟩ : syracuseStep 322415 = 483623) B483623
theorem B322715 : Blo 319836 322715 := bstep (se 1 (by rfl) ⟨242036, by rfl⟩ : syracuseStep 322715 = 484073) B484073
theorem B2452841 : Blo 319836 2452841 := bstep (se 2 (by rfl) ⟨919815, by rfl⟩ : syracuseStep 2452841 = 1839631) B1839631
theorem B912799 : Blo 319836 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B322975 : Blo 319836 322975 := bstep (se 1 (by rfl) ⟨242231, by rfl⟩ : syracuseStep 322975 = 484463) B484463
theorem B323055 : Blo 319836 323055 := bstep (se 1 (by rfl) ⟨242291, by rfl⟩ : syracuseStep 323055 = 484583) B484583
theorem B323099 : Blo 319836 323099 := bstep (se 1 (by rfl) ⟨242324, by rfl⟩ : syracuseStep 323099 = 484649) B484649
theorem B1470143 : Blo 319836 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B323279 : Blo 319836 323279 := bstep (se 1 (by rfl) ⟨242459, by rfl⟩ : syracuseStep 323279 = 484919) B484919
theorem B323495 : Blo 319836 323495 := bstep (se 1 (by rfl) ⟨242621, by rfl⟩ : syracuseStep 323495 = 485243) B485243
theorem B323519 : Blo 319836 323519 := bstep (se 1 (by rfl) ⟨242639, by rfl⟩ : syracuseStep 323519 = 485279) B485279
theorem B323675 : Blo 319836 323675 := bstep (se 1 (by rfl) ⟨242756, by rfl⟩ : syracuseStep 323675 = 485513) B485513
theorem B323775 : Blo 319836 323775 := bstep (se 1 (by rfl) ⟨242831, by rfl⟩ : syracuseStep 323775 = 485663) B485663
theorem B323807 : Blo 319836 323807 := bstep (se 1 (by rfl) ⟨242855, by rfl⟩ : syracuseStep 323807 = 485711) B485711
theorem B1079783 : Blo 319836 1079783 := bstep (se 1 (by rfl) ⟨809837, by rfl⟩ : syracuseStep 1079783 = 1619675) B1619675
theorem B1833617 : Blo 319836 1833617 := bstep (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) B1375213
theorem B2358011 : Blo 319836 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B719927 : Blo 319836 719927 := bstep (se 1 (by rfl) ⟨539945, by rfl⟩ : syracuseStep 719927 = 1079891) B1079891
theorem B457903 : Blo 319836 457903 := bstep (se 1 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 457903 = 686855) B686855
theorem B2522551 : Blo 319836 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B458399 : Blo 319836 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B851707 : Blo 319836 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B1474375 : Blo 319836 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B688009 : Blo 319836 688009 := bstep (se 2 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 688009 = 516007) B516007
theorem B721079 : Blo 319836 721079 := bstep (se 1 (by rfl) ⟨540809, by rfl⟩ : syracuseStep 721079 = 1081619) B1081619
theorem B360895 : Blo 319836 360895 := bstep (se 1 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 360895 = 541343) B541343
theorem B2064923 : Blo 319836 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B1638953 : Blo 319836 1638953 := bstep (se 2 (by rfl) ⟨614607, by rfl⟩ : syracuseStep 1638953 = 1229215) B1229215
theorem B688871 : Blo 319836 688871 := bstep (se 1 (by rfl) ⟨516653, by rfl⟩ : syracuseStep 688871 = 1033307) B1033307
theorem B5604167 : Blo 319836 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B721961 : Blo 319836 721961 := bstep (se 2 (by rfl) ⟨270735, by rfl⟩ : syracuseStep 721961 = 541471) B541471
theorem B722015 : Blo 319836 722015 := bstep (se 1 (by rfl) ⟨541511, by rfl⟩ : syracuseStep 722015 = 1083023) B1083023
theorem B361831 : Blo 319836 361831 := bstep (se 1 (by rfl) ⟨271373, by rfl⟩ : syracuseStep 361831 = 542747) B542747
theorem B821897 : Blo 319836 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B363163 : Blo 319836 363163 := bstep (se 1 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 363163 = 544745) B544745
theorem B363199 : Blo 319836 363199 := bstep (se 1 (by rfl) ⟨272399, by rfl⟩ : syracuseStep 363199 = 544799) B544799
theorem B723689 : Blo 319836 723689 := bstep (se 2 (by rfl) ⟨271383, by rfl⟩ : syracuseStep 723689 = 542767) B542767
theorem B723743 : Blo 319836 723743 := bstep (se 1 (by rfl) ⟨542807, by rfl⟩ : syracuseStep 723743 = 1085615) B1085615
theorem B17697923 : Blo 319836 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B8785043 : Blo 319836 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B724499 : Blo 319836 724499 := bstep (se 1 (by rfl) ⟨543374, by rfl⟩ : syracuseStep 724499 = 1086749) B1086749
theorem B724571 : Blo 319836 724571 := bstep (se 1 (by rfl) ⟨543428, by rfl⟩ : syracuseStep 724571 = 1086857) B1086857
theorem B12029543 : Blo 319836 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B725327 : Blo 319836 725327 := bstep (se 1 (by rfl) ⟨543995, by rfl⟩ : syracuseStep 725327 = 1087991) B1087991
theorem B1217065 : Blo 319836 1217065 := bstep (se 2 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 1217065 = 912799) B912799
theorem B725561 : Blo 319836 725561 := bstep (se 2 (by rfl) ⟨272085, by rfl⟩ : syracuseStep 725561 = 544171) B544171
theorem B1479563 : Blo 319836 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B725993 : Blo 319836 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B726047 : Blo 319836 726047 := bstep (se 1 (by rfl) ⟨544535, by rfl⟩ : syracuseStep 726047 = 1089071) B1089071
theorem B726281 : Blo 319836 726281 := bstep (se 2 (by rfl) ⟨272355, by rfl⟩ : syracuseStep 726281 = 544711) B544711
theorem B1218523 : Blo 319836 1218523 := bstep (se 1 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 1218523 = 1827785) B1827785
theorem B727019 : Blo 319836 727019 := bstep (se 1 (by rfl) ⟨545264, by rfl⟩ : syracuseStep 727019 = 1090529) B1090529
theorem B727271 : Blo 319836 727271 := bstep (se 1 (by rfl) ⟨545453, by rfl⟩ : syracuseStep 727271 = 1090907) B1090907
theorem B727559 : Blo 319836 727559 := bstep (se 1 (by rfl) ⟨545669, by rfl⟩ : syracuseStep 727559 = 1091339) B1091339
theorem B2202173 : Blo 319836 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1383263 : Blo 319836 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B40509391 : Blo 319836 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B10462745 : Blo 319836 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B796393 : Blo 319836 796393 := bstep (se 2 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 796393 = 597295) B597295
theorem B1222397 : Blo 319836 1222397 := bstep (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) B458399
theorem B1222411 : Blo 319836 1222411 := bstep (se 1 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 1222411 = 1833617) B1833617
theorem B3483431 : Blo 319836 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B20982077 : Blo 319836 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B31338413 : Blo 319836 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B232697939 : Blo 319836 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B2732453 : Blo 319836 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B406235 : Blo 319836 406235 := bstep (se 1 (by rfl) ⟨304676, by rfl⟩ : syracuseStep 406235 = 609353) B609353
theorem B2438747 : Blo 319836 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B3094537 : Blo 319836 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B16791785 : Blo 319836 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B1227743 : Blo 319836 1227743 := bstep (se 1 (by rfl) ⟨920807, by rfl⟩ : syracuseStep 1227743 = 1841615) B1841615
theorem B2604923 : Blo 319836 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B1622267 : Blo 319836 1622267 := bstep (se 1 (by rfl) ⟨1216700, by rfl⟩ : syracuseStep 1622267 = 2433401) B2433401
theorem B1229519 : Blo 319836 1229519 := bstep (se 1 (by rfl) ⟨922139, by rfl⟩ : syracuseStep 1229519 = 1844279) B1844279
theorem B2442149 : Blo 319836 2442149 := bstep (se 4 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 2442149 = 457903) B457903
theorem B1164203 : Blo 319836 1164203 := bstep (se 1 (by rfl) ⟨873152, by rfl⟩ : syracuseStep 1164203 = 1746305) B1746305
theorem B771551 : Blo 319836 771551 := bstep (se 1 (by rfl) ⟨578663, by rfl⟩ : syracuseStep 771551 = 1157327) B1157327
theorem B2148049 : Blo 319836 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B5293811 : Blo 319836 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2934767 : Blo 319836 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B3132395 : Blo 319836 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B2740175 : Blo 319836 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B4542437 : Blo 319836 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B3363401 : Blo 319836 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B2052773 : Blo 319836 2052773 := bstep (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) B384895
theorem B479951 : Blo 319836 479951 := bstep (se 1 (by rfl) ⟨359963, by rfl⟩ : syracuseStep 479951 = 719927) B719927
theorem B1823593 : Blo 319836 1823593 := bstep (se 2 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 1823593 = 1367695) B1367695
theorem B10474433 : Blo 319836 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B546169 : Blo 319836 546169 := bstep (se 2 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 546169 = 409627) B409627
theorem B481247 : Blo 319836 481247 := bstep (se 1 (by rfl) ⟨360935, by rfl⟩ : syracuseStep 481247 = 721871) B721871
theorem B612535 : Blo 319836 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B481883 : Blo 319836 481883 := bstep (se 1 (by rfl) ⟨361412, by rfl⟩ : syracuseStep 481883 = 722825) B722825
theorem B481895 : Blo 319836 481895 := bstep (se 1 (by rfl) ⟨361421, by rfl⟩ : syracuseStep 481895 = 722843) B722843
theorem B482027 : Blo 319836 482027 := bstep (se 1 (by rfl) ⟨361520, by rfl⟩ : syracuseStep 482027 = 723041) B723041
theorem B810395 : Blo 319836 810395 := bstep (se 1 (by rfl) ⟨607796, by rfl⟩ : syracuseStep 810395 = 1215593) B1215593
theorem B9854585 : Blo 319836 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B810911 : Blo 319836 810911 := bstep (se 1 (by rfl) ⟨608183, by rfl⟩ : syracuseStep 810911 = 1216367) B1216367
theorem B1236905 : Blo 319836 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B12509623 : Blo 319836 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B2941481 : Blo 319836 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B483881 : Blo 319836 483881 := bstep (se 2 (by rfl) ⟨181455, by rfl⟩ : syracuseStep 483881 = 362911) B362911
theorem B2744927 : Blo 319836 2744927 := bstep (se 1 (by rfl) ⟨2058695, by rfl⟩ : syracuseStep 2744927 = 4117391) B4117391
theorem B1401533 : Blo 319836 1401533 := bstep (se 3 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 1401533 = 525575) B525575
theorem B320231 : Blo 319836 320231 := bstep (se 1 (by rfl) ⟨240173, by rfl⟩ : syracuseStep 320231 = 480347) B480347
theorem B320251 : Blo 319836 320251 := bstep (se 1 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 320251 = 480377) B480377
theorem B320511 : Blo 319836 320511 := bstep (se 1 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 320511 = 480767) B480767
theorem B1369183 : Blo 319836 1369183 := bstep (se 1 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 1369183 = 2053775) B2053775
theorem B1631339 : Blo 319836 1631339 := bstep (se 1 (by rfl) ⟨1223504, by rfl⟩ : syracuseStep 1631339 = 2447009) B2447009
theorem B1827967 : Blo 319836 1827967 := bstep (se 1 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 1827967 = 2741951) B2741951
theorem B1860833 : Blo 319836 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B320763 : Blo 319836 320763 := bstep (se 1 (by rfl) ⟨240572, by rfl⟩ : syracuseStep 320763 = 481145) B481145
theorem B320767 : Blo 319836 320767 := bstep (se 1 (by rfl) ⟨240575, by rfl⟩ : syracuseStep 320767 = 481151) B481151
theorem B321279 : Blo 319836 321279 := bstep (se 1 (by rfl) ⟨240959, by rfl⟩ : syracuseStep 321279 = 481919) B481919
theorem B485159 : Blo 319836 485159 := bstep (se 1 (by rfl) ⟨363869, by rfl⟩ : syracuseStep 485159 = 727739) B727739
theorem B321371 : Blo 319836 321371 := bstep (se 1 (by rfl) ⟨241028, by rfl⟩ : syracuseStep 321371 = 482057) B482057
theorem B485231 : Blo 319836 485231 := bstep (se 1 (by rfl) ⟨363923, by rfl⟩ : syracuseStep 485231 = 727847) B727847
theorem B321531 : Blo 319836 321531 := bstep (se 1 (by rfl) ⟨241148, by rfl⟩ : syracuseStep 321531 = 482297) B482297
theorem B485417 : Blo 319836 485417 := bstep (se 2 (by rfl) ⟨182031, by rfl⟩ : syracuseStep 485417 = 364063) B364063
theorem B321743 : Blo 319836 321743 := bstep (se 1 (by rfl) ⟨241307, by rfl⟩ : syracuseStep 321743 = 482615) B482615
theorem B321863 : Blo 319836 321863 := bstep (se 1 (by rfl) ⟨241397, by rfl⟩ : syracuseStep 321863 = 482795) B482795
theorem B1829243 : Blo 319836 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B1632635 : Blo 319836 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B322215 : Blo 319836 322215 := bstep (se 1 (by rfl) ⟨241661, by rfl⟩ : syracuseStep 322215 = 483323) B483323
theorem B322255 : Blo 319836 322255 := bstep (se 1 (by rfl) ⟨241691, by rfl⟩ : syracuseStep 322255 = 483383) B483383
theorem B322303 : Blo 319836 322303 := bstep (se 1 (by rfl) ⟨241727, by rfl⟩ : syracuseStep 322303 = 483455) B483455
theorem B322335 : Blo 319836 322335 := bstep (se 1 (by rfl) ⟨241751, by rfl⟩ : syracuseStep 322335 = 483503) B483503
theorem B2780335 : Blo 319836 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B388327 : Blo 319836 388327 := bstep (se 1 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 388327 = 582491) B582491
theorem B322815 : Blo 319836 322815 := bstep (se 1 (by rfl) ⟨242111, by rfl⟩ : syracuseStep 322815 = 484223) B484223
theorem B322863 : Blo 319836 322863 := bstep (se 1 (by rfl) ⟨242147, by rfl⟩ : syracuseStep 322863 = 484295) B484295
theorem B814495 : Blo 319836 814495 := bstep (se 1 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 814495 = 1221743) B1221743
theorem B323103 : Blo 319836 323103 := bstep (se 1 (by rfl) ⟨242327, by rfl⟩ : syracuseStep 323103 = 484655) B484655
theorem B20967011 : Blo 319836 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B323263 : Blo 319836 323263 := bstep (se 1 (by rfl) ⟨242447, by rfl⟩ : syracuseStep 323263 = 484895) B484895
theorem B7073851 : Blo 319836 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B2060873 : Blo 319836 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B6288029 : Blo 319836 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1635227 : Blo 319836 1635227 := bstep (se 1 (by rfl) ⟨1226420, by rfl⟩ : syracuseStep 1635227 = 2452841) B2452841
theorem B980095 : Blo 319836 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B7468469 : Blo 319836 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B2323961 : Blo 319836 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B3077929 : Blo 319836 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B1537967 : Blo 319836 1537967 := bstep (se 1 (by rfl) ⟨1153475, by rfl⟩ : syracuseStep 1537967 = 2306951) B2306951
theorem B817087 : Blo 319836 817087 := bstep (se 1 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 817087 = 1225631) B1225631
theorem B3701497 : Blo 319836 3701497 := bstep (se 2 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 3701497 = 2776123) B2776123
theorem B719855 : Blo 319836 719855 := bstep (se 1 (by rfl) ⟨539891, by rfl⟩ : syracuseStep 719855 = 1079783) B1079783
theorem B719945 : Blo 319836 719945 := bstep (se 2 (by rfl) ⟨269979, by rfl⟩ : syracuseStep 719945 = 539959) B539959
theorem B818383 : Blo 319836 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B1080809 : Blo 319836 1080809 := bstep (se 2 (by rfl) ⟨405303, by rfl⟩ : syracuseStep 1080809 = 810607) B810607
theorem B1965833 : Blo 319836 1965833 := bstep (se 2 (by rfl) ⟨737187, by rfl⟩ : syracuseStep 1965833 = 1474375) B1474375
theorem B917345 : Blo 319836 917345 := bstep (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) B688009
theorem B360319 : Blo 319836 360319 := bstep (se 1 (by rfl) ⟨270239, by rfl⟩ : syracuseStep 360319 = 540479) B540479
theorem B819193 : Blo 319836 819193 := bstep (se 2 (by rfl) ⟨307197, by rfl⟩ : syracuseStep 819193 = 614395) B614395
theorem B1081511 : Blo 319836 1081511 := bstep (se 1 (by rfl) ⟨811133, by rfl⟩ : syracuseStep 1081511 = 1622267) B1622267
theorem B620527837 : Blo 319836 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B1376615 : Blo 319836 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B819679 : Blo 319836 819679 := bstep (se 1 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 819679 = 1229519) B1229519
theorem B3736111 : Blo 319836 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B1083293 : Blo 319836 1083293 := bstep (se 3 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 1083293 = 406235) B406235
theorem B1836989 : Blo 319836 1836989 := bstep (se 3 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 1836989 = 688871) B688871
theorem B11798615 : Blo 319836 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B66717989 : Blo 319836 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B986375 : Blo 319836 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B6982955 : Blo 319836 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B1085993 : Blo 319836 1085993 := bstep (se 2 (by rfl) ⟨407247, by rfl⟩ : syracuseStep 1085993 = 814495) B814495
theorem B922175 : Blo 319836 922175 := bstep (se 1 (by rfl) ⟨691631, by rfl⟩ : syracuseStep 922175 = 1383263) B1383263
theorem B824603 : Blo 319836 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B1087559 : Blo 319836 1087559 := bstep (se 1 (by rfl) ⟨815669, by rfl⟩ : syracuseStep 1087559 = 1631339) B1631339
theorem B2431457 : Blo 319836 2431457 := bstep (se 2 (by rfl) ⟨911796, by rfl⟩ : syracuseStep 2431457 = 1823593) B1823593
theorem B1219495 : Blo 319836 1219495 := bstep (se 1 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 1219495 = 1829243) B1829243
theorem B1088423 : Blo 319836 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B728225 : Blo 319836 728225 := bstep (se 2 (by rfl) ⟨273084, by rfl⟩ : syracuseStep 728225 = 546169) B546169
theorem B4103905 : Blo 319836 4103905 := bstep (se 2 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 4103905 = 3077929) B3077929
theorem B1089449 : Blo 319836 1089449 := bstep (se 2 (by rfl) ⟨408543, by rfl⟩ : syracuseStep 1089449 = 817087) B817087
theorem B1090151 : Blo 319836 1090151 := bstep (se 1 (by rfl) ⟨817613, by rfl⟩ : syracuseStep 1090151 = 1635227) B1635227
theorem B1549307 : Blo 319836 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B1025311 : Blo 319836 1025311 := bstep (se 1 (by rfl) ⟨768983, by rfl⟩ : syracuseStep 1025311 = 1537967) B1537967
theorem B1091177 : Blo 319836 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B54012521 : Blo 319836 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B1092257 : Blo 319836 1092257 := bstep (se 2 (by rfl) ⟨409596, by rfl⟩ : syracuseStep 1092257 = 819193) B819193
theorem B1092635 : Blo 319836 1092635 := bstep (se 1 (by rfl) ⟨819476, by rfl⟩ : syracuseStep 1092635 = 1638953) B1638953
theorem B7843949 : Blo 319836 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B2437289 : Blo 319836 2437289 := bstep (se 2 (by rfl) ⟨913983, by rfl⟩ : syracuseStep 2437289 = 1827967) B1827967
theorem B2864065 : Blo 319836 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1061857 : Blo 319836 1061857 := bstep (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) B796393
theorem B3028291 : Blo 319836 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B4962221 : Blo 319836 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B540263 : Blo 319836 540263 := bstep (se 1 (by rfl) ⟨405197, by rfl⟩ : syracuseStep 540263 = 810395) B810395
theorem B6569723 : Blo 319836 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B540607 : Blo 319836 540607 := bstep (se 1 (by rfl) ⟨405455, by rfl⟩ : syracuseStep 540607 = 810911) B810911
theorem B934355 : Blo 319836 934355 := bstep (se 1 (by rfl) ⟨700766, by rfl⟩ : syracuseStep 934355 = 1401533) B1401533
theorem B1622753 : Blo 319836 1622753 := bstep (se 2 (by rfl) ⟨608532, by rfl⟩ : syracuseStep 1622753 = 1217065) B1217065
theorem B14828453 : Blo 319836 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B13978007 : Blo 319836 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B20892275 : Blo 319836 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B1624697 : Blo 319836 1624697 := bstep (se 2 (by rfl) ⟨609261, by rfl⟩ : syracuseStep 1624697 = 1218523) B1218523
theorem B1821635 : Blo 319836 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B4935329 : Blo 319836 4935329 := bstep (se 2 (by rfl) ⟨1850748, by rfl⟩ : syracuseStep 4935329 = 3701497) B3701497
theorem B1625831 : Blo 319836 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B11194523 : Blo 319836 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B479903 : Blo 319836 479903 := bstep (se 1 (by rfl) ⟨359927, by rfl⟩ : syracuseStep 479903 = 719855) B719855
theorem B479963 : Blo 319836 479963 := bstep (se 1 (by rfl) ⟨359972, by rfl⟩ : syracuseStep 479963 = 719945) B719945
theorem B480425 : Blo 319836 480425 := bstep (se 2 (by rfl) ⟨180159, by rfl⟩ : syracuseStep 480425 = 360319) B360319
theorem B611563 : Blo 319836 611563 := bstep (se 1 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 611563 = 917345) B917345
theorem B480719 : Blo 319836 480719 := bstep (se 1 (by rfl) ⟨360539, by rfl⟩ : syracuseStep 480719 = 721079) B721079
theorem B481193 : Blo 319836 481193 := bstep (se 2 (by rfl) ⟨180447, by rfl⟩ : syracuseStep 481193 = 360895) B360895
theorem B1628099 : Blo 319836 1628099 := bstep (se 1 (by rfl) ⟨1221074, by rfl⟩ : syracuseStep 1628099 = 2442149) B2442149
theorem B776135 : Blo 319836 776135 := bstep (se 1 (by rfl) ⟨582101, by rfl⟩ : syracuseStep 776135 = 1164203) B1164203
theorem B481307 : Blo 319836 481307 := bstep (se 1 (by rfl) ⟨360980, by rfl⟩ : syracuseStep 481307 = 721961) B721961
theorem B481343 : Blo 319836 481343 := bstep (se 1 (by rfl) ⟨361007, by rfl⟩ : syracuseStep 481343 = 722015) B722015
theorem B514367 : Blo 319836 514367 := bstep (se 1 (by rfl) ⟨385775, by rfl⟩ : syracuseStep 514367 = 771551) B771551
theorem B3529207 : Blo 319836 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B1956511 : Blo 319836 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B1825577 : Blo 319836 1825577 := bstep (se 2 (by rfl) ⟨684591, by rfl⟩ : syracuseStep 1825577 = 1369183) B1369183
theorem B8969069 : Blo 319836 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B547931 : Blo 319836 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B482441 : Blo 319836 482441 := bstep (se 2 (by rfl) ⟨180915, by rfl⟩ : syracuseStep 482441 = 361831) B361831
theorem B482459 : Blo 319836 482459 := bstep (se 1 (by rfl) ⟨361844, by rfl⟩ : syracuseStep 482459 = 723689) B723689
theorem B482495 : Blo 319836 482495 := bstep (se 1 (by rfl) ⟨361871, by rfl⟩ : syracuseStep 482495 = 723743) B723743
theorem B2088263 : Blo 319836 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B5856695 : Blo 319836 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B482999 : Blo 319836 482999 := bstep (se 1 (by rfl) ⟨362249, by rfl⟩ : syracuseStep 482999 = 724499) B724499
theorem B1629881 : Blo 319836 1629881 := bstep (se 2 (by rfl) ⟨611205, by rfl⟩ : syracuseStep 1629881 = 1222411) B1222411
theorem B483047 : Blo 319836 483047 := bstep (se 1 (by rfl) ⟨362285, by rfl⟩ : syracuseStep 483047 = 724571) B724571
theorem B8019695 : Blo 319836 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B1826783 : Blo 319836 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B483551 : Blo 319836 483551 := bstep (se 1 (by rfl) ⟨362663, by rfl⟩ : syracuseStep 483551 = 725327) B725327
theorem B483707 : Blo 319836 483707 := bstep (se 1 (by rfl) ⟨362780, by rfl⟩ : syracuseStep 483707 = 725561) B725561
theorem B1368515 : Blo 319836 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B319967 : Blo 319836 319967 := bstep (se 1 (by rfl) ⟨239975, by rfl⟩ : syracuseStep 319967 = 479951) B479951
theorem B483995 : Blo 319836 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B484031 : Blo 319836 484031 := bstep (se 1 (by rfl) ⟨363023, by rfl⟩ : syracuseStep 484031 = 726047) B726047
theorem B484187 : Blo 319836 484187 := bstep (se 1 (by rfl) ⟨363140, by rfl⟩ : syracuseStep 484187 = 726281) B726281
theorem B484217 : Blo 319836 484217 := bstep (se 2 (by rfl) ⟨181581, by rfl⟩ : syracuseStep 484217 = 363163) B363163
theorem B484265 : Blo 319836 484265 := bstep (se 2 (by rfl) ⟨181599, by rfl⟩ : syracuseStep 484265 = 363199) B363199
theorem B320831 : Blo 319836 320831 := bstep (se 1 (by rfl) ⟨240623, by rfl⟩ : syracuseStep 320831 = 481247) B481247
theorem B484679 : Blo 319836 484679 := bstep (se 1 (by rfl) ⟨363509, by rfl⟩ : syracuseStep 484679 = 727019) B727019
theorem B484847 : Blo 319836 484847 := bstep (se 1 (by rfl) ⟨363635, by rfl⟩ : syracuseStep 484847 = 727271) B727271
theorem B517769 : Blo 319836 517769 := bstep (se 2 (by rfl) ⟨194163, by rfl⟩ : syracuseStep 517769 = 388327) B388327
theorem B485039 : Blo 319836 485039 := bstep (se 1 (by rfl) ⟨363779, by rfl⟩ : syracuseStep 485039 = 727559) B727559
theorem B1468115 : Blo 319836 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B321255 : Blo 319836 321255 := bstep (se 1 (by rfl) ⟨240941, by rfl⟩ : syracuseStep 321255 = 481883) B481883
theorem B321263 : Blo 319836 321263 := bstep (se 1 (by rfl) ⟨240947, by rfl⟩ : syracuseStep 321263 = 481895) B481895
theorem B321351 : Blo 319836 321351 := bstep (se 1 (by rfl) ⟨241013, by rfl⟩ : syracuseStep 321351 = 482027) B482027
theorem B9431801 : Blo 319836 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B322587 : Blo 319836 322587 := bstep (se 1 (by rfl) ⟨241940, by rfl⟩ : syracuseStep 322587 = 483881) B483881
theorem B1829951 : Blo 319836 1829951 := bstep (se 1 (by rfl) ⟨1372463, by rfl⟩ : syracuseStep 1829951 = 2744927) B2744927
theorem B6975163 : Blo 319836 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B814931 : Blo 319836 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B2322287 : Blo 319836 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B323439 : Blo 319836 323439 := bstep (se 1 (by rfl) ⟨242579, by rfl⟩ : syracuseStep 323439 = 485159) B485159
theorem B323487 : Blo 319836 323487 := bstep (se 1 (by rfl) ⟨242615, by rfl⟩ : syracuseStep 323487 = 485231) B485231
theorem B323611 : Blo 319836 323611 := bstep (se 1 (by rfl) ⟨242708, by rfl⟩ : syracuseStep 323611 = 485417) B485417
theorem B1306793 : Blo 319836 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B13988051 : Blo 319836 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B4126049 : Blo 319836 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B816713 : Blo 319836 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B1373915 : Blo 319836 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B4192019 : Blo 319836 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B4978979 : Blo 319836 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B818495 : Blo 319836 818495 := bstep (se 1 (by rfl) ⟨613871, by rfl⟩ : syracuseStep 818495 = 1227743) B1227743
theorem B720539 : Blo 319836 720539 := bstep (se 1 (by rfl) ⟨540404, by rfl⟩ : syracuseStep 720539 = 1080809) B1080809
theorem B1310555 : Blo 319836 1310555 := bstep (se 1 (by rfl) ⟨982916, by rfl⟩ : syracuseStep 1310555 = 1965833) B1965833
theorem B1736615 : Blo 319836 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B721007 : Blo 319836 721007 := bstep (se 1 (by rfl) ⟨540755, by rfl⟩ : syracuseStep 721007 = 1081511) B1081511
theorem B917743 : Blo 319836 917743 := bstep (se 1 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 917743 = 1376615) B1376615
theorem B622903 : Blo 319836 622903 := bstep (se 1 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 622903 = 934355) B934355
theorem B1081835 : Blo 319836 1081835 := bstep (se 1 (by rfl) ⟨811376, by rfl⟩ : syracuseStep 1081835 = 1622753) B1622753
theorem B4981481 : Blo 319836 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B722195 : Blo 319836 722195 := bstep (se 1 (by rfl) ⟨541646, by rfl⟩ : syracuseStep 722195 = 1083293) B1083293
theorem B7865743 : Blo 319836 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B13928183 : Blo 319836 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B1083131 : Blo 319836 1083131 := bstep (se 1 (by rfl) ⟨812348, by rfl⟩ : syracuseStep 1083131 = 1624697) B1624697
theorem B1214423 : Blo 319836 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B4655303 : Blo 319836 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B1083887 : Blo 319836 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B4131485 : Blo 319836 4131485 := bstep (se 3 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 4131485 = 1549307) B1549307
theorem B723995 : Blo 319836 723995 := bstep (se 1 (by rfl) ⟨542996, by rfl⟩ : syracuseStep 723995 = 1085993) B1085993
theorem B1085399 : Blo 319836 1085399 := bstep (se 1 (by rfl) ⟨814049, by rfl⟩ : syracuseStep 1085399 = 1628099) B1628099
theorem B725039 : Blo 319836 725039 := bstep (se 1 (by rfl) ⟨543779, by rfl⟩ : syracuseStep 725039 = 1087559) B1087559
theorem B1217051 : Blo 319836 1217051 := bstep (se 1 (by rfl) ⟨912788, by rfl⟩ : syracuseStep 1217051 = 1825577) B1825577
theorem B725615 : Blo 319836 725615 := bstep (se 1 (by rfl) ⟨544211, by rfl⟩ : syracuseStep 725615 = 1088423) B1088423
theorem B3904463 : Blo 319836 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B1086587 : Blo 319836 1086587 := bstep (se 1 (by rfl) ⟨814940, by rfl⟩ : syracuseStep 1086587 = 1629881) B1629881
theorem B726299 : Blo 319836 726299 := bstep (se 1 (by rfl) ⟨544724, by rfl⟩ : syracuseStep 726299 = 1089449) B1089449
theorem B1217855 : Blo 319836 1217855 := bstep (se 1 (by rfl) ⟨913391, by rfl⟩ : syracuseStep 1217855 = 1826783) B1826783
theorem B726767 : Blo 319836 726767 := bstep (se 1 (by rfl) ⟨545075, by rfl⟩ : syracuseStep 726767 = 1090151) B1090151
theorem B727451 : Blo 319836 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B1415809 : Blo 319836 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B728171 : Blo 319836 728171 := bstep (se 1 (by rfl) ⟨546128, by rfl⟩ : syracuseStep 728171 = 1092257) B1092257
theorem B728423 : Blo 319836 728423 := bstep (se 1 (by rfl) ⟨546317, by rfl⟩ : syracuseStep 728423 = 1092635) B1092635
theorem B1219967 : Blo 319836 1219967 := bstep (se 1 (by rfl) ⟨914975, by rfl⟩ : syracuseStep 1219967 = 1829951) B1829951
theorem B1548191 : Blo 319836 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B2630333 : Blo 319836 2630333 := bstep (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) B986375
theorem B2794679 : Blo 319836 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B3319319 : Blo 319836 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B1157743 : Blo 319836 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B827370449 : Blo 319836 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B3484781 : Blo 319836 3484781 := bstep (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) B1306793
theorem B1092905 : Blo 319836 1092905 := bstep (se 2 (by rfl) ⟨409839, by rfl⟩ : syracuseStep 1092905 = 819679) B819679
theorem B3649373 : Blo 319836 3649373 := bstep (se 3 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 3649373 = 1368515) B1368515
theorem B1224659 : Blo 319836 1224659 := bstep (se 1 (by rfl) ⟨918494, by rfl⟩ : syracuseStep 1224659 = 1836989) B1836989
theorem B44478659 : Blo 319836 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B9318671 : Blo 319836 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B3290219 : Blo 319836 3290219 := bstep (se 1 (by rfl) ⟨2467664, by rfl⟩ : syracuseStep 3290219 = 4935329) B4935329
theorem B8795765 : Blo 319836 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B342911 : Blo 319836 342911 := bstep (se 1 (by rfl) ⟨257183, by rfl⟩ : syracuseStep 342911 = 514367) B514367
theorem B1620971 : Blo 319836 1620971 := bstep (se 1 (by rfl) ⟨1215728, by rfl⟩ : syracuseStep 1620971 = 2431457) B2431457
theorem B5979379 : Blo 319836 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B1392175 : Blo 319836 1392175 := bstep (se 1 (by rfl) ⟨1044131, by rfl⟩ : syracuseStep 1392175 = 2088263) B2088263
theorem B345179 : Blo 319836 345179 := bstep (se 1 (by rfl) ⟨258884, by rfl⟩ : syracuseStep 345179 = 517769) B517769
theorem B3818753 : Blo 319836 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B64603541 : Blo 319836 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B543287 : Blo 319836 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B5229299 : Blo 319836 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B1624859 : Blo 319836 1624859 := bstep (se 1 (by rfl) ⟨1218644, by rfl⟩ : syracuseStep 1624859 = 2437289) B2437289
theorem B9325367 : Blo 319836 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B1461149 : Blo 319836 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B4705609 : Blo 319836 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B2608681 : Blo 319836 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B544475 : Blo 319836 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B1625993 : Blo 319836 1625993 := bstep (se 2 (by rfl) ⟨609747, by rfl⟩ : syracuseStep 1625993 = 1219495) B1219495
theorem B21385853 : Blo 319836 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B545663 : Blo 319836 545663 := bstep (se 1 (by rfl) ⟨409247, by rfl⟩ : syracuseStep 545663 = 818495) B818495
theorem B480359 : Blo 319836 480359 := bstep (se 1 (by rfl) ⟨360269, by rfl⟩ : syracuseStep 480359 = 720539) B720539
theorem B4379815 : Blo 319836 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B873703 : Blo 319836 873703 := bstep (se 1 (by rfl) ⟨655277, by rfl⟩ : syracuseStep 873703 = 1310555) B1310555
theorem B9885635 : Blo 319836 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B1367081 : Blo 319836 1367081 := bstep (se 2 (by rfl) ⟨512655, by rfl⟩ : syracuseStep 1367081 = 1025311) B1025311
theorem B7463015 : Blo 319836 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B614783 : Blo 319836 614783 := bstep (se 1 (by rfl) ⟨461087, by rfl⟩ : syracuseStep 614783 = 922175) B922175
theorem B319935 : Blo 319836 319935 := bstep (se 1 (by rfl) ⟨239951, by rfl⟩ : syracuseStep 319935 = 479903) B479903
theorem B319975 : Blo 319836 319975 := bstep (se 1 (by rfl) ⟨239981, by rfl⟩ : syracuseStep 319975 = 479963) B479963
theorem B320283 : Blo 319836 320283 := bstep (se 1 (by rfl) ⟨240212, by rfl⟩ : syracuseStep 320283 = 480425) B480425
theorem B320479 : Blo 319836 320479 := bstep (se 1 (by rfl) ⟨240359, by rfl⟩ : syracuseStep 320479 = 480719) B480719
theorem B320795 : Blo 319836 320795 := bstep (se 1 (by rfl) ⟨240596, by rfl⟩ : syracuseStep 320795 = 481193) B481193
theorem B517423 : Blo 319836 517423 := bstep (se 1 (by rfl) ⟨388067, by rfl⟩ : syracuseStep 517423 = 776135) B776135
theorem B320871 : Blo 319836 320871 := bstep (se 1 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 320871 = 481307) B481307
theorem B320895 : Blo 319836 320895 := bstep (se 1 (by rfl) ⟨240671, by rfl⟩ : syracuseStep 320895 = 481343) B481343
theorem B321627 : Blo 319836 321627 := bstep (se 1 (by rfl) ⟨241220, by rfl⟩ : syracuseStep 321627 = 482441) B482441
theorem B321639 : Blo 319836 321639 := bstep (se 1 (by rfl) ⟨241229, by rfl⟩ : syracuseStep 321639 = 482459) B482459
theorem B485483 : Blo 319836 485483 := bstep (se 1 (by rfl) ⟨364112, by rfl⟩ : syracuseStep 485483 = 728225) B728225
theorem B321663 : Blo 319836 321663 := bstep (se 1 (by rfl) ⟨241247, by rfl⟩ : syracuseStep 321663 = 482495) B482495
theorem B9300217 : Blo 319836 9300217 := bstep (se 2 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 9300217 = 6975163) B6975163
theorem B321999 : Blo 319836 321999 := bstep (se 1 (by rfl) ⟨241499, by rfl⟩ : syracuseStep 321999 = 482999) B482999
theorem B322031 : Blo 319836 322031 := bstep (se 1 (by rfl) ⟨241523, by rfl⟩ : syracuseStep 322031 = 483047) B483047
theorem B322367 : Blo 319836 322367 := bstep (se 1 (by rfl) ⟨241775, by rfl⟩ : syracuseStep 322367 = 483551) B483551
theorem B322471 : Blo 319836 322471 := bstep (se 1 (by rfl) ⟨241853, by rfl⟩ : syracuseStep 322471 = 483707) B483707
theorem B322663 : Blo 319836 322663 := bstep (se 1 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 322663 = 483995) B483995
theorem B322687 : Blo 319836 322687 := bstep (se 1 (by rfl) ⟨242015, by rfl⟩ : syracuseStep 322687 = 484031) B484031
theorem B322791 : Blo 319836 322791 := bstep (se 1 (by rfl) ⟨242093, by rfl⟩ : syracuseStep 322791 = 484187) B484187
theorem B322811 : Blo 319836 322811 := bstep (se 1 (by rfl) ⟨242108, by rfl⟩ : syracuseStep 322811 = 484217) B484217
theorem B322843 : Blo 319836 322843 := bstep (se 1 (by rfl) ⟨242132, by rfl⟩ : syracuseStep 322843 = 484265) B484265
theorem B323119 : Blo 319836 323119 := bstep (se 1 (by rfl) ⟨242339, by rfl⟩ : syracuseStep 323119 = 484679) B484679
theorem B323231 : Blo 319836 323231 := bstep (se 1 (by rfl) ⟨242423, by rfl⟩ : syracuseStep 323231 = 484847) B484847
theorem B323359 : Blo 319836 323359 := bstep (se 1 (by rfl) ⟨242519, by rfl⟩ : syracuseStep 323359 = 485039) B485039
theorem B978743 : Blo 319836 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B815417 : Blo 319836 815417 := bstep (se 2 (by rfl) ⟨305781, by rfl⟩ : syracuseStep 815417 = 611563) B611563
theorem B36008347 : Blo 319836 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B6287867 : Blo 319836 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B2750699 : Blo 319836 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B915943 : Blo 319836 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B3308147 : Blo 319836 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B5471873 : Blo 319836 5471873 := bstep (se 2 (by rfl) ⟨2051952, by rfl⟩ : syracuseStep 5471873 = 4103905) B4103905
theorem B360175 : Blo 319836 360175 := bstep (se 1 (by rfl) ⟨270131, by rfl⟩ : syracuseStep 360175 = 540263) B540263
theorem B720809 : Blo 319836 720809 := bstep (se 2 (by rfl) ⟨270303, by rfl⟩ : syracuseStep 720809 = 540607) B540607
theorem B721223 : Blo 319836 721223 := bstep (se 1 (by rfl) ⟨540917, by rfl⟩ : syracuseStep 721223 = 1081835) B1081835
theorem B722087 : Blo 319836 722087 := bstep (se 1 (by rfl) ⟨541565, by rfl⟩ : syracuseStep 722087 = 1083131) B1083131
theorem B722591 : Blo 319836 722591 := bstep (se 1 (by rfl) ⟨541943, by rfl⟩ : syracuseStep 722591 = 1083887) B1083887
theorem B362191 : Blo 319836 362191 := bstep (se 1 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 362191 = 543287) B543287
theorem B689897 : Blo 319836 689897 := bstep (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) B517423
theorem B2754323 : Blo 319836 2754323 := bstep (se 1 (by rfl) ⟨2065742, by rfl⟩ : syracuseStep 2754323 = 4131485) B4131485
theorem B1083239 : Blo 319836 1083239 := bstep (se 1 (by rfl) ⟨812429, by rfl⟩ : syracuseStep 1083239 = 1624859) B1624859
theorem B10487657 : Blo 319836 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B362983 : Blo 319836 362983 := bstep (se 1 (by rfl) ⟨272237, by rfl⟩ : syracuseStep 362983 = 544475) B544475
theorem B1083995 : Blo 319836 1083995 := bstep (se 1 (by rfl) ⟨812996, by rfl⟩ : syracuseStep 1083995 = 1625993) B1625993
theorem B723599 : Blo 319836 723599 := bstep (se 1 (by rfl) ⟨542699, by rfl⟩ : syracuseStep 723599 = 1085399) B1085399
theorem B920477 : Blo 319836 920477 := bstep (se 3 (by rfl) ⟨172589, by rfl⟩ : syracuseStep 920477 = 345179) B345179
theorem B14257235 : Blo 319836 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B363775 : Blo 319836 363775 := bstep (se 1 (by rfl) ⟨272831, by rfl⟩ : syracuseStep 363775 = 545663) B545663
theorem B724391 : Blo 319836 724391 := bstep (se 1 (by rfl) ⟨543293, by rfl⟩ : syracuseStep 724391 = 1086587) B1086587
theorem B1543657 : Blo 319836 1543657 := bstep (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) B1157743
theorem B6590423 : Blo 319836 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B3478241 : Blo 319836 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B48011129 : Blo 319836 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B728603 : Blo 319836 728603 := bstep (se 1 (by rfl) ⟨546452, by rfl⟩ : syracuseStep 728603 = 1092905) B1092905
theorem B2432915 : Blo 319836 2432915 := bstep (se 1 (by rfl) ⟨1824686, by rfl⟩ : syracuseStep 2432915 = 3649373) B3649373
theorem B1221257 : Blo 319836 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B7972505 : Blo 319836 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B2205431 : Blo 319836 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B3647915 : Blo 319836 3647915 := bstep (se 1 (by rfl) ⟨2735936, by rfl⟩ : syracuseStep 3647915 = 5471873) B5471873
theorem B1223657 : Blo 319836 1223657 := bstep (se 2 (by rfl) ⟨458871, by rfl⟩ : syracuseStep 1223657 = 917743) B917743
theorem B830537 : Blo 319836 830537 := bstep (se 2 (by rfl) ⟨311451, by rfl⟩ : syracuseStep 830537 = 622903) B622903
theorem B43069027 : Blo 319836 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B9285455 : Blo 319836 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B3486199 : Blo 319836 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B12400289 : Blo 319836 12400289 := bstep (se 2 (by rfl) ⟨4650108, by rfl⟩ : syracuseStep 12400289 = 9300217) B9300217
theorem B2602975 : Blo 319836 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B6274145 : Blo 319836 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B409855 : Blo 319836 409855 := bstep (se 1 (by rfl) ⟨307391, by rfl⟩ : syracuseStep 409855 = 614783) B614783
theorem B1753555 : Blo 319836 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B2212879 : Blo 319836 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B1164937 : Blo 319836 1164937 := bstep (se 2 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 1164937 = 873703) B873703
theorem B53135797 : Blo 319836 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B6212447 : Blo 319836 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B543611 : Blo 319836 543611 := bstep (se 1 (by rfl) ⟨407708, by rfl⟩ : syracuseStep 543611 = 815417) B815417
theorem B1887745 : Blo 319836 1887745 := bstep (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) B1415809
theorem B1856233 : Blo 319836 1856233 := bstep (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) B1392175
theorem B2609981 : Blo 319836 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B480233 : Blo 319836 480233 := bstep (se 2 (by rfl) ⟨180087, by rfl⟩ : syracuseStep 480233 = 360175) B360175
theorem B480539 : Blo 319836 480539 := bstep (se 1 (by rfl) ⟨360404, by rfl⟩ : syracuseStep 480539 = 720809) B720809
theorem B480671 : Blo 319836 480671 := bstep (se 1 (by rfl) ⟨360503, by rfl⟩ : syracuseStep 480671 = 721007) B721007
theorem B2545835 : Blo 319836 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B481463 : Blo 319836 481463 := bstep (se 1 (by rfl) ⟨361097, by rfl⟩ : syracuseStep 481463 = 722195) B722195
theorem B809615 : Blo 319836 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B3103535 : Blo 319836 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B6216911 : Blo 319836 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B974099 : Blo 319836 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B482663 : Blo 319836 482663 := bstep (se 1 (by rfl) ⟨361997, by rfl⟩ : syracuseStep 482663 = 723995) B723995
theorem B483359 : Blo 319836 483359 := bstep (se 1 (by rfl) ⟨362519, by rfl⟩ : syracuseStep 483359 = 725039) B725039
theorem B811367 : Blo 319836 811367 := bstep (se 1 (by rfl) ⟨608525, by rfl⟩ : syracuseStep 811367 = 1217051) B1217051
theorem B483743 : Blo 319836 483743 := bstep (se 1 (by rfl) ⟨362807, by rfl⟩ : syracuseStep 483743 = 725615) B725615
theorem B320239 : Blo 319836 320239 := bstep (se 1 (by rfl) ⟨240179, by rfl⟩ : syracuseStep 320239 = 480359) B480359
theorem B484199 : Blo 319836 484199 := bstep (se 1 (by rfl) ⟨363149, by rfl⟩ : syracuseStep 484199 = 726299) B726299
theorem B811903 : Blo 319836 811903 := bstep (se 1 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 811903 = 1217855) B1217855
theorem B484511 : Blo 319836 484511 := bstep (se 1 (by rfl) ⟨363383, by rfl⟩ : syracuseStep 484511 = 726767) B726767
theorem B484967 : Blo 319836 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B911387 : Blo 319836 911387 := bstep (se 1 (by rfl) ⟨683540, by rfl⟩ : syracuseStep 911387 = 1367081) B1367081
theorem B485447 : Blo 319836 485447 := bstep (se 1 (by rfl) ⟨364085, by rfl⟩ : syracuseStep 485447 = 728171) B728171
theorem B485615 : Blo 319836 485615 := bstep (se 1 (by rfl) ⟨364211, by rfl⟩ : syracuseStep 485615 = 728423) B728423
theorem B813311 : Blo 319836 813311 := bstep (se 1 (by rfl) ⟨609983, by rfl⟩ : syracuseStep 813311 = 1219967) B1219967
theorem B4975343 : Blo 319836 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B1863119 : Blo 319836 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B23359013 : Blo 319836 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B323655 : Blo 319836 323655 := bstep (se 1 (by rfl) ⟨242741, by rfl⟩ : syracuseStep 323655 = 485483) B485483
theorem B551580299 : Blo 319836 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B2323187 : Blo 319836 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B914429 : Blo 319836 914429 := bstep (se 3 (by rfl) ⟨171455, by rfl⟩ : syracuseStep 914429 = 342911) B342911
theorem B816439 : Blo 319836 816439 := bstep (se 1 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 816439 = 1224659) B1224659
theorem B29652439 : Blo 319836 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B4191911 : Blo 319836 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B2193479 : Blo 319836 2193479 := bstep (se 1 (by rfl) ⟨1645109, by rfl⟩ : syracuseStep 2193479 = 3290219) B3290219
theorem B5863843 : Blo 319836 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B1833799 : Blo 319836 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B1080647 : Blo 319836 1080647 := bstep (se 1 (by rfl) ⟨810485, by rfl⟩ : syracuseStep 1080647 = 1620971) B1620971
theorem B4128509 : Blo 319836 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B459931 : Blo 319836 459931 := bstep (se 1 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 459931 = 689897) B689897
theorem B1082537 : Blo 319836 1082537 := bstep (se 2 (by rfl) ⟨405951, by rfl⟩ : syracuseStep 1082537 = 811903) B811903
theorem B1836215 : Blo 319836 1836215 := bstep (se 1 (by rfl) ⟨1377161, by rfl⟩ : syracuseStep 1836215 = 2754323) B2754323
theorem B722159 : Blo 319836 722159 := bstep (se 1 (by rfl) ⟨541619, by rfl⟩ : syracuseStep 722159 = 1083239) B1083239
theorem B2950505 : Blo 319836 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B722663 : Blo 319836 722663 := bstep (se 1 (by rfl) ⟨541997, by rfl⟩ : syracuseStep 722663 = 1083995) B1083995
theorem B362407 : Blo 319836 362407 := bstep (se 1 (by rfl) ⟨271805, by rfl⟩ : syracuseStep 362407 = 543611) B543611
theorem B9275309 : Blo 319836 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B9504823 : Blo 319836 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B4393615 : Blo 319836 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B1739987 : Blo 319836 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B70847729 : Blo 319836 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B2069023 : Blo 319836 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B6788893 : Blo 319836 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B5315003 : Blo 319836 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B2431943 : Blo 319836 2431943 := bstep (se 1 (by rfl) ⟨1823957, by rfl⟩ : syracuseStep 2431943 = 3647915) B3647915
theorem B1088585 : Blo 319836 1088585 := bstep (se 2 (by rfl) ⟨408219, by rfl⟩ : syracuseStep 1088585 = 816439) B816439
theorem B3316895 : Blo 319836 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B15572675 : Blo 319836 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B1548791 : Blo 319836 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B8266859 : Blo 319836 8266859 := bstep (se 1 (by rfl) ⟨6200144, by rfl⟩ : syracuseStep 8266859 = 12400289) B12400289
theorem B2794607 : Blo 319836 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B2338073 : Blo 319836 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B6991771 : Blo 319836 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B4141631 : Blo 319836 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B1553249 : Blo 319836 1553249 := bstep (se 2 (by rfl) ⟨582468, by rfl⟩ : syracuseStep 1553249 = 1164937) B1164937
theorem B539743 : Blo 319836 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B57425369 : Blo 319836 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B4144607 : Blo 319836 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B1621943 : Blo 319836 1621943 := bstep (se 1 (by rfl) ⟨1216457, by rfl⟩ : syracuseStep 1621943 = 2432915) B2432915
theorem B540911 : Blo 319836 540911 := bstep (se 1 (by rfl) ⟨405683, by rfl⟩ : syracuseStep 540911 = 811367) B811367
theorem B2474977 : Blo 319836 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B607591 : Blo 319836 607591 := bstep (se 1 (by rfl) ⟨455693, by rfl⟩ : syracuseStep 607591 = 911387) B911387
theorem B542207 : Blo 319836 542207 := bstep (se 1 (by rfl) ⟨406655, by rfl⟩ : syracuseStep 542207 = 813311) B813311
theorem B39536585 : Blo 319836 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B7818457 : Blo 319836 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B609619 : Blo 319836 609619 := bstep (se 1 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 609619 = 914429) B914429
theorem B2445065 : Blo 319836 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B4968317 : Blo 319836 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B1462319 : Blo 319836 1462319 := bstep (se 1 (by rfl) ⟨1096739, by rfl⟩ : syracuseStep 1462319 = 2193479) B2193479
theorem B4182763 : Blo 319836 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B480815 : Blo 319836 480815 := bstep (se 1 (by rfl) ⟨360611, by rfl⟩ : syracuseStep 480815 = 721223) B721223
theorem B546473 : Blo 319836 546473 := bstep (se 2 (by rfl) ⟨204927, by rfl⟩ : syracuseStep 546473 = 409855) B409855
theorem B481391 : Blo 319836 481391 := bstep (se 1 (by rfl) ⟨361043, by rfl⟩ : syracuseStep 481391 = 722087) B722087
theorem B481727 : Blo 319836 481727 := bstep (se 1 (by rfl) ⟨361295, by rfl⟩ : syracuseStep 481727 = 722591) B722591
theorem B482399 : Blo 319836 482399 := bstep (se 1 (by rfl) ⟨361799, by rfl⟩ : syracuseStep 482399 = 723599) B723599
theorem B613651 : Blo 319836 613651 := bstep (se 1 (by rfl) ⟨460238, by rfl⟩ : syracuseStep 613651 = 920477) B920477
theorem B482921 : Blo 319836 482921 := bstep (se 2 (by rfl) ⟨181095, by rfl⟩ : syracuseStep 482921 = 362191) B362191
theorem B482927 : Blo 319836 482927 := bstep (se 1 (by rfl) ⟨362195, by rfl⟩ : syracuseStep 482927 = 724391) B724391
theorem B483977 : Blo 319836 483977 := bstep (se 2 (by rfl) ⟨181491, by rfl⟩ : syracuseStep 483977 = 362983) B362983
theorem B320155 : Blo 319836 320155 := bstep (se 1 (by rfl) ⟨240116, by rfl⟩ : syracuseStep 320155 = 480233) B480233
theorem B320359 : Blo 319836 320359 := bstep (se 1 (by rfl) ⟨240269, by rfl⟩ : syracuseStep 320359 = 480539) B480539
theorem B320447 : Blo 319836 320447 := bstep (se 1 (by rfl) ⟨240335, by rfl⟩ : syracuseStep 320447 = 480671) B480671
theorem B32007419 : Blo 319836 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B320975 : Blo 319836 320975 := bstep (se 1 (by rfl) ⟨240731, by rfl⟩ : syracuseStep 320975 = 481463) B481463
theorem B485033 : Blo 319836 485033 := bstep (se 2 (by rfl) ⟨181887, by rfl⟩ : syracuseStep 485033 = 363775) B363775
theorem B2058209 : Blo 319836 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B2516993 : Blo 319836 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B649399 : Blo 319836 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B321775 : Blo 319836 321775 := bstep (se 1 (by rfl) ⟨241331, by rfl⟩ : syracuseStep 321775 = 482663) B482663
theorem B485735 : Blo 319836 485735 := bstep (se 1 (by rfl) ⟨364301, by rfl⟩ : syracuseStep 485735 = 728603) B728603
theorem B322239 : Blo 319836 322239 := bstep (se 1 (by rfl) ⟨241679, by rfl⟩ : syracuseStep 322239 = 483359) B483359
theorem B322495 : Blo 319836 322495 := bstep (se 1 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 322495 = 483743) B483743
theorem B814171 : Blo 319836 814171 := bstep (se 1 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 814171 = 1221257) B1221257
theorem B322799 : Blo 319836 322799 := bstep (se 1 (by rfl) ⟨242099, by rfl⟩ : syracuseStep 322799 = 484199) B484199
theorem B4648265 : Blo 319836 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B323007 : Blo 319836 323007 := bstep (se 1 (by rfl) ⟨242255, by rfl⟩ : syracuseStep 323007 = 484511) B484511
theorem B323311 : Blo 319836 323311 := bstep (se 1 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 323311 = 484967) B484967
theorem B1470287 : Blo 319836 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B323631 : Blo 319836 323631 := bstep (se 1 (by rfl) ⟨242723, by rfl⟩ : syracuseStep 323631 = 485447) B485447
theorem B323743 : Blo 319836 323743 := bstep (se 1 (by rfl) ⟨242807, by rfl⟩ : syracuseStep 323743 = 485615) B485615
theorem B815771 : Blo 319836 815771 := bstep (se 1 (by rfl) ⟨611828, by rfl⟩ : syracuseStep 815771 = 1223657) B1223657
theorem B553691 : Blo 319836 553691 := bstep (se 1 (by rfl) ⟨415268, by rfl⟩ : syracuseStep 553691 = 830537) B830537
theorem B6190303 : Blo 319836 6190303 := bstep (se 1 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 6190303 = 9285455) B9285455
theorem B3470633 : Blo 319836 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B367720199 : Blo 319836 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B720431 : Blo 319836 720431 := bstep (se 1 (by rfl) ⟨540323, by rfl⟩ : syracuseStep 720431 = 1080647) B1080647
theorem B2752339 : Blo 319836 2752339 := bstep (se 1 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 2752339 = 4128509) B4128509
theorem B360607 : Blo 319836 360607 := bstep (se 1 (by rfl) ⟨270455, by rfl⟩ : syracuseStep 360607 = 540911) B540911
theorem B721691 : Blo 319836 721691 := bstep (se 1 (by rfl) ⟨541268, by rfl⟩ : syracuseStep 721691 = 1082537) B1082537
theorem B1967003 : Blo 319836 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B361471 : Blo 319836 361471 := bstep (se 1 (by rfl) ⟨271103, by rfl⟩ : syracuseStep 361471 = 542207) B542207
theorem B364315 : Blo 319836 364315 := bstep (se 1 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 364315 = 546473) B546473
theorem B1085561 : Blo 319836 1085561 := bstep (se 2 (by rfl) ⟨407085, by rfl⟩ : syracuseStep 1085561 = 814171) B814171
theorem B10424609 : Blo 319836 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B3543335 : Blo 319836 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B725723 : Blo 319836 725723 := bstep (se 1 (by rfl) ⟨544292, by rfl⟩ : syracuseStep 725723 = 1088585) B1088585
theorem B2758697 : Blo 319836 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B5511239 : Blo 319836 5511239 := bstep (se 1 (by rfl) ⟨4133429, by rfl⟩ : syracuseStep 5511239 = 8266859) B8266859
theorem B21338279 : Blo 319836 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B5577017 : Blo 319836 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1677995 : Blo 319836 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B9051857 : Blo 319836 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B2761087 : Blo 319836 2761087 := bstep (se 1 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 2761087 = 4141631) B4141631
theorem B369127 : Blo 319836 369127 := bstep (se 1 (by rfl) ⟨276845, by rfl⟩ : syracuseStep 369127 = 553691) B553691
theorem B245146799 : Blo 319836 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B153134317 : Blo 319836 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B41527133 : Blo 319836 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B2763071 : Blo 319836 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B13248845 : Blo 319836 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B1224143 : Blo 319836 1224143 := bstep (se 1 (by rfl) ⟨918107, by rfl⟩ : syracuseStep 1224143 = 1836215) B1836215
theorem B26357723 : Blo 319836 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B1159991 : Blo 319836 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B47231819 : Blo 319836 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B865865 : Blo 319836 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B1621295 : Blo 319836 1621295 := bstep (se 1 (by rfl) ⟨1215971, by rfl⟩ : syracuseStep 1621295 = 2431943) B2431943
theorem B2211263 : Blo 319836 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B9322361 : Blo 319836 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B1032527 : Blo 319836 1032527 := bstep (se 1 (by rfl) ⟨774395, by rfl⟩ : syracuseStep 1032527 = 1548791) B1548791
theorem B1558715 : Blo 319836 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B3098843 : Blo 319836 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B543847 : Blo 319836 543847 := bstep (se 1 (by rfl) ⟨407885, by rfl⟩ : syracuseStep 543847 = 815771) B815771
theorem B1035499 : Blo 319836 1035499 := bstep (se 1 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 1035499 = 1553249) B1553249
theorem B2313755 : Blo 319836 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B480287 : Blo 319836 480287 := bstep (se 1 (by rfl) ⟨360215, by rfl⟩ : syracuseStep 480287 = 720431) B720431
theorem B481439 : Blo 319836 481439 := bstep (se 1 (by rfl) ⟨361079, by rfl⟩ : syracuseStep 481439 = 722159) B722159
theorem B481775 : Blo 319836 481775 := bstep (se 1 (by rfl) ⟨361331, by rfl⟩ : syracuseStep 481775 = 722663) B722663
theorem B6183539 : Blo 319836 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B3299969 : Blo 319836 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B613241 : Blo 319836 613241 := bstep (se 2 (by rfl) ⟨229965, by rfl⟩ : syracuseStep 613241 = 459931) B459931
theorem B810121 : Blo 319836 810121 := bstep (se 2 (by rfl) ⟨303795, by rfl⟩ : syracuseStep 810121 = 607591) B607591
theorem B1630043 : Blo 319836 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B483209 : Blo 319836 483209 := bstep (se 2 (by rfl) ⟨181203, by rfl⟩ : syracuseStep 483209 = 362407) B362407
theorem B974879 : Blo 319836 974879 := bstep (se 1 (by rfl) ⟨731159, by rfl⟩ : syracuseStep 974879 = 1462319) B1462319
theorem B12673097 : Blo 319836 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B5858153 : Blo 319836 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B320543 : Blo 319836 320543 := bstep (se 1 (by rfl) ⟨240407, by rfl⟩ : syracuseStep 320543 = 480815) B480815
theorem B320927 : Blo 319836 320927 := bstep (se 1 (by rfl) ⟨240695, by rfl⟩ : syracuseStep 320927 = 481391) B481391
theorem B321151 : Blo 319836 321151 := bstep (se 1 (by rfl) ⟨240863, by rfl⟩ : syracuseStep 321151 = 481727) B481727
theorem B812825 : Blo 319836 812825 := bstep (se 2 (by rfl) ⟨304809, by rfl⟩ : syracuseStep 812825 = 609619) B609619
theorem B321599 : Blo 319836 321599 := bstep (se 1 (by rfl) ⟨241199, by rfl⟩ : syracuseStep 321599 = 482399) B482399
theorem B321947 : Blo 319836 321947 := bstep (se 1 (by rfl) ⟨241460, by rfl⟩ : syracuseStep 321947 = 482921) B482921
theorem B321951 : Blo 319836 321951 := bstep (se 1 (by rfl) ⟨241463, by rfl⟩ : syracuseStep 321951 = 482927) B482927
theorem B322651 : Blo 319836 322651 := bstep (se 1 (by rfl) ⟨241988, by rfl⟩ : syracuseStep 322651 = 483977) B483977
theorem B1863071 : Blo 319836 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B323355 : Blo 319836 323355 := bstep (se 1 (by rfl) ⟨242516, by rfl⟩ : syracuseStep 323355 = 485033) B485033
theorem B1372139 : Blo 319836 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B323823 : Blo 319836 323823 := bstep (se 1 (by rfl) ⟨242867, by rfl⟩ : syracuseStep 323823 = 485735) B485735
theorem B8253737 : Blo 319836 8253737 := bstep (se 2 (by rfl) ⟨3095151, by rfl⟩ : syracuseStep 8253737 = 6190303) B6190303
theorem B980191 : Blo 319836 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B719657 : Blo 319836 719657 := bstep (se 2 (by rfl) ⟨269871, by rfl⟩ : syracuseStep 719657 = 539743) B539743
theorem B818201 : Blo 319836 818201 := bstep (se 2 (by rfl) ⟨306825, by rfl⟩ : syracuseStep 818201 = 613651) B613651
theorem B3669785 : Blo 319836 3669785 := bstep (se 2 (by rfl) ⟨1376169, by rfl⟩ : syracuseStep 3669785 = 2752339) B2752339
theorem B1081295 : Blo 319836 1081295 := bstep (se 1 (by rfl) ⟨810971, by rfl⟩ : syracuseStep 1081295 = 1621943) B1621943
theorem B688351 : Blo 319836 688351 := bstep (se 1 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 688351 = 1032527) B1032527
theorem B1311335 : Blo 319836 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B2065895 : Blo 319836 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B1542503 : Blo 319836 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B1968677 : Blo 319836 1968677 := bstep (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) B369127
theorem B723707 : Blo 319836 723707 := bstep (se 1 (by rfl) ⟨542780, by rfl⟩ : syracuseStep 723707 = 1085561) B1085561
theorem B6949739 : Blo 319836 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B2362223 : Blo 319836 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B1839131 : Blo 319836 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B3674159 : Blo 319836 3674159 := bstep (se 1 (by rfl) ⟨2755619, by rfl⟩ : syracuseStep 3674159 = 5511239) B5511239
theorem B14225519 : Blo 319836 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B725129 : Blo 319836 725129 := bstep (se 2 (by rfl) ⟨271923, by rfl⟩ : syracuseStep 725129 = 543847) B543847
theorem B1380665 : Blo 319836 1380665 := bstep (se 2 (by rfl) ⟨517749, by rfl⟩ : syracuseStep 1380665 = 1035499) B1035499
theorem B2199979 : Blo 319836 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B1118663 : Blo 319836 1118663 := bstep (se 1 (by rfl) ⟨838997, by rfl⟩ : syracuseStep 1118663 = 1677995) B1677995
theorem B6034571 : Blo 319836 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B1086695 : Blo 319836 1086695 := bstep (se 1 (by rfl) ⟨815021, by rfl⟩ : syracuseStep 1086695 = 1630043) B1630043
theorem B3905435 : Blo 319836 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B816716357 : Blo 319836 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B1842047 : Blo 319836 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B17571815 : Blo 319836 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B3681449 : Blo 319836 3681449 := bstep (se 2 (by rfl) ⟨1380543, by rfl⟩ : syracuseStep 3681449 = 2761087) B2761087
theorem B16626293 : Blo 319836 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B408827 : Blo 319836 408827 := bstep (se 1 (by rfl) ⟨306620, by rfl⟩ : syracuseStep 408827 = 613241) B613241
theorem B163431199 : Blo 319836 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B541883 : Blo 319836 541883 := bstep (se 1 (by rfl) ⟨406412, by rfl⟩ : syracuseStep 541883 = 812825) B812825
theorem B8832563 : Blo 319836 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B773327 : Blo 319836 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B577243 : Blo 319836 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B479771 : Blo 319836 479771 := bstep (se 1 (by rfl) ⟨359828, by rfl⟩ : syracuseStep 479771 = 719657) B719657
theorem B545467 : Blo 319836 545467 := bstep (se 1 (by rfl) ⟨409100, by rfl⟩ : syracuseStep 545467 = 818201) B818201
theorem B2446523 : Blo 319836 2446523 := bstep (se 1 (by rfl) ⟨1834892, by rfl⟩ : syracuseStep 2446523 = 3669785) B3669785
theorem B6214907 : Blo 319836 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B480809 : Blo 319836 480809 := bstep (se 2 (by rfl) ⟨180303, by rfl⟩ : syracuseStep 480809 = 360607) B360607
theorem B481127 : Blo 319836 481127 := bstep (se 1 (by rfl) ⟨360845, by rfl⟩ : syracuseStep 481127 = 721691) B721691
theorem B481961 : Blo 319836 481961 := bstep (se 2 (by rfl) ⟨180735, by rfl⟩ : syracuseStep 481961 = 361471) B361471
theorem B483815 : Blo 319836 483815 := bstep (se 1 (by rfl) ⟨362861, by rfl⟩ : syracuseStep 483815 = 725723) B725723
theorem B320191 : Blo 319836 320191 := bstep (se 1 (by rfl) ⟨240143, by rfl⟩ : syracuseStep 320191 = 480287) B480287
theorem B320959 : Blo 319836 320959 := bstep (se 1 (by rfl) ⟨240719, by rfl⟩ : syracuseStep 320959 = 481439) B481439
theorem B321183 : Blo 319836 321183 := bstep (se 1 (by rfl) ⟨240887, by rfl⟩ : syracuseStep 321183 = 481775) B481775
theorem B4122359 : Blo 319836 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B485753 : Blo 319836 485753 := bstep (se 2 (by rfl) ⟨182157, by rfl⟩ : syracuseStep 485753 = 364315) B364315
theorem B322139 : Blo 319836 322139 := bstep (se 1 (by rfl) ⟨241604, by rfl⟩ : syracuseStep 322139 = 483209) B483209
theorem B649919 : Blo 319836 649919 := bstep (se 1 (by rfl) ⟨487439, by rfl⟩ : syracuseStep 649919 = 974879) B974879
theorem B8448731 : Blo 319836 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B14872045 : Blo 319836 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B27684755 : Blo 319836 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B1306921 : Blo 319836 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B1242047 : Blo 319836 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B816095 : Blo 319836 816095 := bstep (se 1 (by rfl) ⟨612071, by rfl⟩ : syracuseStep 816095 = 1224143) B1224143
theorem B914759 : Blo 319836 914759 := bstep (se 1 (by rfl) ⟨686069, by rfl⟩ : syracuseStep 914759 = 1372139) B1372139
theorem B5502491 : Blo 319836 5502491 := bstep (se 1 (by rfl) ⟨4126868, by rfl⟩ : syracuseStep 5502491 = 8253737) B8253737
theorem B31487879 : Blo 319836 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B1080161 : Blo 319836 1080161 := bstep (se 2 (by rfl) ⟨405060, by rfl⟩ : syracuseStep 1080161 = 810121) B810121
theorem B1080863 : Blo 319836 1080863 := bstep (se 1 (by rfl) ⟨810647, by rfl⟩ : syracuseStep 1080863 = 1621295) B1621295
theorem B1474175 : Blo 319836 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B720863 : Blo 319836 720863 := bstep (se 1 (by rfl) ⟨540647, by rfl⟩ : syracuseStep 720863 = 1081295) B1081295
theorem B917801 : Blo 319836 917801 := bstep (se 2 (by rfl) ⟨344175, by rfl⟩ : syracuseStep 917801 = 688351) B688351
theorem B361255 : Blo 319836 361255 := bstep (se 1 (by rfl) ⟨270941, by rfl⟩ : syracuseStep 361255 = 541883) B541883
theorem B1377263 : Blo 319836 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B217908265 : Blo 319836 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1312451 : Blo 319836 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B1574815 : Blo 319836 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B11733221 : Blo 319836 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B920443 : Blo 319836 920443 := bstep (se 1 (by rfl) ⟨690332, by rfl⟩ : syracuseStep 920443 = 1380665) B1380665
theorem B724463 : Blo 319836 724463 := bstep (se 1 (by rfl) ⟨543347, by rfl⟩ : syracuseStep 724463 = 1086695) B1086695
theorem B544477571 : Blo 319836 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B19829393 : Blo 319836 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B1742561 : Blo 319836 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B727289 : Blo 319836 727289 := bstep (se 2 (by rfl) ⟨272733, by rfl⟩ : syracuseStep 727289 = 545467) B545467
theorem B433279 : Blo 319836 433279 := bstep (se 1 (by rfl) ⟨324959, by rfl⟩ : syracuseStep 433279 = 649919) B649919
theorem B18456503 : Blo 319836 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B11084195 : Blo 319836 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B828031 : Blo 319836 828031 := bstep (se 1 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 828031 = 1242047) B1242047
theorem B1090205 : Blo 319836 1090205 := bstep (se 3 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 1090205 = 408827) B408827
theorem B1028335 : Blo 319836 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B4633159 : Blo 319836 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B1226087 : Blo 319836 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B9483679 : Blo 319836 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B4143271 : Blo 319836 4143271 := bstep (se 1 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 4143271 = 6214907) B6214907
theorem B1228031 : Blo 319836 1228031 := bstep (se 1 (by rfl) ⟨921023, by rfl⟩ : syracuseStep 1228031 = 1842047) B1842047
theorem B769657 : Blo 319836 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B11714543 : Blo 319836 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B544063 : Blo 319836 544063 := bstep (se 1 (by rfl) ⟨408047, by rfl⟩ : syracuseStep 544063 = 816095) B816095
theorem B609839 : Blo 319836 609839 := bstep (se 1 (by rfl) ⟨457379, by rfl⟩ : syracuseStep 609839 = 914759) B914759
theorem B20991919 : Blo 319836 20991919 := bstep (se 1 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 20991919 = 31487879) B31487879
theorem B480575 : Blo 319836 480575 := bstep (se 1 (by rfl) ⟨360431, by rfl⟩ : syracuseStep 480575 = 720863) B720863
theorem B874223 : Blo 319836 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B5888375 : Blo 319836 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B482471 : Blo 319836 482471 := bstep (se 1 (by rfl) ⟨361853, by rfl⟩ : syracuseStep 482471 = 723707) B723707
theorem B2449439 : Blo 319836 2449439 := bstep (se 1 (by rfl) ⟨1837079, by rfl⟩ : syracuseStep 2449439 = 3674159) B3674159
theorem B483419 : Blo 319836 483419 := bstep (se 1 (by rfl) ⟨362564, by rfl⟩ : syracuseStep 483419 = 725129) B725129
theorem B745775 : Blo 319836 745775 := bstep (se 1 (by rfl) ⟨559331, by rfl⟩ : syracuseStep 745775 = 1118663) B1118663
theorem B319847 : Blo 319836 319847 := bstep (se 1 (by rfl) ⟨239885, by rfl⟩ : syracuseStep 319847 = 479771) B479771
theorem B4023047 : Blo 319836 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B1631015 : Blo 319836 1631015 := bstep (se 1 (by rfl) ⟨1223261, by rfl⟩ : syracuseStep 1631015 = 2446523) B2446523
theorem B320539 : Blo 319836 320539 := bstep (se 1 (by rfl) ⟨240404, by rfl⟩ : syracuseStep 320539 = 480809) B480809
theorem B320751 : Blo 319836 320751 := bstep (se 1 (by rfl) ⟨240563, by rfl⟩ : syracuseStep 320751 = 481127) B481127
theorem B321307 : Blo 319836 321307 := bstep (se 1 (by rfl) ⟨240980, by rfl⟩ : syracuseStep 321307 = 481961) B481961
theorem B10414493 : Blo 319836 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B322543 : Blo 319836 322543 := bstep (se 1 (by rfl) ⟨241907, by rfl⟩ : syracuseStep 322543 = 483815) B483815
theorem B2748239 : Blo 319836 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B323835 : Blo 319836 323835 := bstep (se 1 (by rfl) ⟨242876, by rfl⟩ : syracuseStep 323835 = 485753) B485753
theorem B5632487 : Blo 319836 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B2454299 : Blo 319836 2454299 := bstep (se 1 (by rfl) ⟨1840724, by rfl⟩ : syracuseStep 2454299 = 3681449) B3681449
theorem B2062205 : Blo 319836 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B3668327 : Blo 319836 3668327 := bstep (se 1 (by rfl) ⟨2751245, by rfl⟩ : syracuseStep 3668327 = 5502491) B5502491
theorem B720107 : Blo 319836 720107 := bstep (se 1 (by rfl) ⟨540080, by rfl⟩ : syracuseStep 720107 = 1080161) B1080161
theorem B720575 : Blo 319836 720575 := bstep (se 1 (by rfl) ⟨540431, by rfl⟩ : syracuseStep 720575 = 1080863) B1080863
theorem B982783 : Blo 319836 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B2099753 : Blo 319836 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B3672701 : Blo 319836 3672701 := bstep (se 3 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 3672701 = 1377263) B1377263
theorem B725417 : Blo 319836 725417 := bstep (se 2 (by rfl) ⟨272031, by rfl⟩ : syracuseStep 725417 = 544063) B544063
theorem B27989225 : Blo 319836 27989225 := bstep (se 2 (by rfl) ⟨10495959, by rfl⟩ : syracuseStep 27989225 = 20991919) B20991919
theorem B497183 : Blo 319836 497183 := bstep (se 1 (by rfl) ⟨372887, by rfl⟩ : syracuseStep 497183 = 745775) B745775
theorem B726803 : Blo 319836 726803 := bstep (se 1 (by rfl) ⟨545102, by rfl⟩ : syracuseStep 726803 = 1090205) B1090205
theorem B1087343 : Blo 319836 1087343 := bstep (se 1 (by rfl) ⟨815507, by rfl⟩ : syracuseStep 1087343 = 1631015) B1631015
theorem B1026209 : Blo 319836 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B7809695 : Blo 319836 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B10728125 : Blo 319836 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B406559 : Blo 319836 406559 := bstep (se 1 (by rfl) ⟨304919, by rfl⟩ : syracuseStep 406559 = 609839) B609839
theorem B362985047 : Blo 319836 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B13219595 : Blo 319836 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B1161707 : Blo 319836 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B1227257 : Blo 319836 1227257 := bstep (se 2 (by rfl) ⟨460221, by rfl⟩ : syracuseStep 1227257 = 920443) B920443
theorem B7389463 : Blo 319836 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B6177545 : Blo 319836 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B50579621 : Blo 319836 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B5524361 : Blo 319836 5524361 := bstep (se 2 (by rfl) ⟨2071635, by rfl⟩ : syracuseStep 5524361 = 4143271) B4143271
theorem B3754991 : Blo 319836 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B577705 : Blo 319836 577705 := bstep (se 2 (by rfl) ⟨216639, by rfl⟩ : syracuseStep 577705 = 433279) B433279
theorem B2445551 : Blo 319836 2445551 := bstep (se 1 (by rfl) ⟨1834163, by rfl⟩ : syracuseStep 2445551 = 3668327) B3668327
theorem B480071 : Blo 319836 480071 := bstep (se 1 (by rfl) ⟨360053, by rfl⟩ : syracuseStep 480071 = 720107) B720107
theorem B480383 : Blo 319836 480383 := bstep (se 1 (by rfl) ⟨360287, by rfl⟩ : syracuseStep 480383 = 720575) B720575
theorem B611867 : Blo 319836 611867 := bstep (se 1 (by rfl) ⟨458900, by rfl⟩ : syracuseStep 611867 = 917801) B917801
theorem B1104041 : Blo 319836 1104041 := bstep (se 2 (by rfl) ⟨414015, by rfl⟩ : syracuseStep 1104041 = 828031) B828031
theorem B481673 : Blo 319836 481673 := bstep (se 2 (by rfl) ⟨180627, by rfl⟩ : syracuseStep 481673 = 361255) B361255
theorem B874967 : Blo 319836 874967 := bstep (se 1 (by rfl) ⟨656225, by rfl⟩ : syracuseStep 874967 = 1312451) B1312451
theorem B290544353 : Blo 319836 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B482975 : Blo 319836 482975 := bstep (se 1 (by rfl) ⟨362231, by rfl⟩ : syracuseStep 482975 = 724463) B724463
theorem B320383 : Blo 319836 320383 := bstep (se 1 (by rfl) ⟨240287, by rfl⟩ : syracuseStep 320383 = 480575) B480575
theorem B582815 : Blo 319836 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B484859 : Blo 319836 484859 := bstep (se 1 (by rfl) ⟨363644, by rfl⟩ : syracuseStep 484859 = 727289) B727289
theorem B3925583 : Blo 319836 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B321647 : Blo 319836 321647 := bstep (se 1 (by rfl) ⟨241235, by rfl⟩ : syracuseStep 321647 = 482471) B482471
theorem B1632959 : Blo 319836 1632959 := bstep (se 1 (by rfl) ⟨1224719, by rfl⟩ : syracuseStep 1632959 = 2449439) B2449439
theorem B322279 : Blo 319836 322279 := bstep (se 1 (by rfl) ⟨241709, by rfl⟩ : syracuseStep 322279 = 483419) B483419
theorem B1371113 : Blo 319836 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B31288589 : Blo 319836 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B6942995 : Blo 319836 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B1832159 : Blo 319836 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B1636199 : Blo 319836 1636199 := bstep (se 1 (by rfl) ⟨1227149, by rfl⟩ : syracuseStep 1636199 = 2454299) B2454299
theorem B817391 : Blo 319836 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B1374803 : Blo 319836 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B818687 : Blo 319836 818687 := bstep (se 1 (by rfl) ⟨614015, by rfl⟩ : syracuseStep 818687 = 1228031) B1228031
theorem B1310377 : Blo 319836 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B49217341 : Blo 319836 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B33719747 : Blo 319836 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B1084157 : Blo 319836 1084157 := bstep (se 3 (by rfl) ⟨203279, by rfl⟩ : syracuseStep 1084157 = 406559) B406559
theorem B724895 : Blo 319836 724895 := bstep (se 1 (by rfl) ⟨543671, by rfl⟩ : syracuseStep 724895 = 1087343) B1087343
theorem B193696235 : Blo 319836 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B2333245 : Blo 319836 2333245 := bstep (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) B874967
theorem B1088639 : Blo 319836 1088639 := bstep (se 1 (by rfl) ⟨816479, by rfl⟩ : syracuseStep 1088639 = 1632959) B1632959
theorem B4628663 : Blo 319836 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B7152083 : Blo 319836 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B1221439 : Blo 319836 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B1090799 : Blo 319836 1090799 := bstep (se 1 (by rfl) ⟨818099, by rfl⟩ : syracuseStep 1090799 = 1636199) B1636199
theorem B1747169 : Blo 319836 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B3682907 : Blo 319836 3682907 := bstep (se 1 (by rfl) ⟨2762180, by rfl⟩ : syracuseStep 3682907 = 5524361) B5524361
theorem B2503327 : Blo 319836 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B1554173 : Blo 319836 1554173 := bstep (se 3 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 1554173 = 582815) B582815
theorem B18659483 : Blo 319836 18659483 := bstep (se 1 (by rfl) ⟨13994612, by rfl⟩ : syracuseStep 18659483 = 27989225) B27989225
theorem B407911 : Blo 319836 407911 := bstep (se 1 (by rfl) ⟨305933, by rfl⟩ : syracuseStep 407911 = 611867) B611867
theorem B1325821 : Blo 319836 1325821 := bstep (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) B497183
theorem B770273 : Blo 319836 770273 := bstep (se 2 (by rfl) ⟨288852, by rfl⟩ : syracuseStep 770273 = 577705) B577705
theorem B3097885 : Blo 319836 3097885 := bstep (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) B1161707
theorem B20859059 : Blo 319836 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B544927 : Blo 319836 544927 := bstep (se 1 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 544927 = 817391) B817391
theorem B545791 : Blo 319836 545791 := bstep (se 1 (by rfl) ⟨409343, by rfl⟩ : syracuseStep 545791 = 818687) B818687
theorem B65623121 : Blo 319836 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B9852617 : Blo 319836 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B4118363 : Blo 319836 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B1399835 : Blo 319836 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B2448467 : Blo 319836 2448467 := bstep (se 1 (by rfl) ⟨1836350, by rfl⟩ : syracuseStep 2448467 = 3672701) B3672701
theorem B1630367 : Blo 319836 1630367 := bstep (se 1 (by rfl) ⟨1222775, by rfl⟩ : syracuseStep 1630367 = 2445551) B2445551
theorem B483611 : Blo 319836 483611 := bstep (se 1 (by rfl) ⟨362708, by rfl⟩ : syracuseStep 483611 = 725417) B725417
theorem B320047 : Blo 319836 320047 := bstep (se 1 (by rfl) ⟨240035, by rfl⟩ : syracuseStep 320047 = 480071) B480071
theorem B320255 : Blo 319836 320255 := bstep (se 1 (by rfl) ⟨240191, by rfl⟩ : syracuseStep 320255 = 480383) B480383
theorem B484535 : Blo 319836 484535 := bstep (se 1 (by rfl) ⟨363401, by rfl⟩ : syracuseStep 484535 = 726803) B726803
theorem B321115 : Blo 319836 321115 := bstep (se 1 (by rfl) ⟨240836, by rfl⟩ : syracuseStep 321115 = 481673) B481673
theorem B321983 : Blo 319836 321983 := bstep (se 1 (by rfl) ⟨241487, by rfl⟩ : syracuseStep 321983 = 482975) B482975
theorem B2944109 : Blo 319836 2944109 := bstep (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) B1104041
theorem B323239 : Blo 319836 323239 := bstep (se 1 (by rfl) ⟨242429, by rfl⟩ : syracuseStep 323239 = 484859) B484859
theorem B2617055 : Blo 319836 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B684139 : Blo 319836 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B5206463 : Blo 319836 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B914075 : Blo 319836 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B241990031 : Blo 319836 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B8813063 : Blo 319836 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B818171 : Blo 319836 818171 := bstep (se 1 (by rfl) ⟨613628, by rfl⟩ : syracuseStep 818171 = 1227257) B1227257
theorem B916535 : Blo 319836 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B4130513 : Blo 319836 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B722771 : Blo 319836 722771 := bstep (se 1 (by rfl) ⟨542078, by rfl⟩ : syracuseStep 722771 = 1084157) B1084157
theorem B43748747 : Blo 319836 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B89919325 : Blo 319836 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B725759 : Blo 319836 725759 := bstep (se 1 (by rfl) ⟨544319, by rfl⟩ : syracuseStep 725759 = 1088639) B1088639
theorem B1086911 : Blo 319836 1086911 := bstep (se 1 (by rfl) ⟨815183, by rfl⟩ : syracuseStep 1086911 = 1630367) B1630367
theorem B3085775 : Blo 319836 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B726569 : Blo 319836 726569 := bstep (se 2 (by rfl) ⟨272463, by rfl⟩ : syracuseStep 726569 = 544927) B544927
theorem B727199 : Blo 319836 727199 := bstep (se 1 (by rfl) ⟨545399, by rfl⟩ : syracuseStep 727199 = 1090799) B1090799
theorem B727721 : Blo 319836 727721 := bstep (se 2 (by rfl) ⟨272895, by rfl⟩ : syracuseStep 727721 = 545791) B545791
theorem B23501501 : Blo 319836 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B1744703 : Blo 319836 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B161326687 : Blo 319836 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B13906039 : Blo 319836 13906039 := bstep (se 1 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 13906039 = 20859059) B20859059
theorem B6568411 : Blo 319836 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B933223 : Blo 319836 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B4768055 : Blo 319836 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B1164779 : Blo 319836 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B2444093 : Blo 319836 2444093 := bstep (se 3 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 2444093 = 916535) B916535
theorem B609383 : Blo 319836 609383 := bstep (se 1 (by rfl) ⟨457037, by rfl⟩ : syracuseStep 609383 = 914075) B914075
theorem B543881 : Blo 319836 543881 := bstep (se 2 (by rfl) ⟨203955, by rfl⟩ : syracuseStep 543881 = 407911) B407911
theorem B1036115 : Blo 319836 1036115 := bstep (se 1 (by rfl) ⟨777086, by rfl⟩ : syracuseStep 1036115 = 1554173) B1554173
theorem B12439655 : Blo 319836 12439655 := bstep (se 1 (by rfl) ⟨9329741, by rfl⟩ : syracuseStep 12439655 = 18659483) B18659483
theorem B545447 : Blo 319836 545447 := bstep (se 1 (by rfl) ⟨409085, by rfl⟩ : syracuseStep 545447 = 818171) B818171
theorem B513515 : Blo 319836 513515 := bstep (se 1 (by rfl) ⟨385136, by rfl⟩ : syracuseStep 513515 = 770273) B770273
theorem B1628585 : Blo 319836 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B483263 : Blo 319836 483263 := bstep (se 1 (by rfl) ⟨362447, by rfl⟩ : syracuseStep 483263 = 724895) B724895
theorem B129130823 : Blo 319836 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B2745575 : Blo 319836 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B1632311 : Blo 319836 1632311 := bstep (se 1 (by rfl) ⟨1224233, by rfl⟩ : syracuseStep 1632311 = 2448467) B2448467
theorem B912185 : Blo 319836 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B322407 : Blo 319836 322407 := bstep (se 1 (by rfl) ⟨241805, by rfl⟩ : syracuseStep 322407 = 483611) B483611
theorem B323023 : Blo 319836 323023 := bstep (se 1 (by rfl) ⟨242267, by rfl⟩ : syracuseStep 323023 = 484535) B484535
theorem B3337769 : Blo 319836 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B1962739 : Blo 319836 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B3470975 : Blo 319836 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B2455271 : Blo 319836 2455271 := bstep (se 1 (by rfl) ⟨1841453, by rfl⟩ : syracuseStep 2455271 = 3682907) B3682907
theorem B3110993 : Blo 319836 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B1767761 : Blo 319836 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B3178703 : Blo 319836 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B2753675 : Blo 319836 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B362587 : Blo 319836 362587 := bstep (se 1 (by rfl) ⟨271940, by rfl⟩ : syracuseStep 362587 = 543881) B543881
theorem B29165831 : Blo 319836 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B690743 : Blo 319836 690743 := bstep (se 1 (by rfl) ⟨518057, by rfl⟩ : syracuseStep 690743 = 1036115) B1036115
theorem B8293103 : Blo 319836 8293103 := bstep (se 1 (by rfl) ⟨6219827, by rfl⟩ : syracuseStep 8293103 = 12439655) B12439655
theorem B363631 : Blo 319836 363631 := bstep (se 1 (by rfl) ⟨272723, by rfl⟩ : syracuseStep 363631 = 545447) B545447
theorem B724607 : Blo 319836 724607 := bstep (se 1 (by rfl) ⟨543455, by rfl⟩ : syracuseStep 724607 = 1086911) B1086911
theorem B1085723 : Blo 319836 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B15667667 : Blo 319836 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B86087215 : Blo 319836 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B1088207 : Blo 319836 1088207 := bstep (se 1 (by rfl) ⟨816155, by rfl⟩ : syracuseStep 1088207 = 1632311) B1632311
theorem B8757881 : Blo 319836 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B2073995 : Blo 319836 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B479569733 : Blo 319836 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B215102249 : Blo 319836 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B342343 : Blo 319836 342343 := bstep (se 1 (by rfl) ⟨256757, by rfl⟩ : syracuseStep 342343 = 513515) B513515
theorem B1163135 : Blo 319836 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B608123 : Blo 319836 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B1625021 : Blo 319836 1625021 := bstep (se 3 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 1625021 = 609383) B609383
theorem B2313983 : Blo 319836 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B776519 : Blo 319836 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B481847 : Blo 319836 481847 := bstep (se 1 (by rfl) ⟨361385, by rfl⟩ : syracuseStep 481847 = 722771) B722771
theorem B1629395 : Blo 319836 1629395 := bstep (se 1 (by rfl) ⟨1222046, by rfl⟩ : syracuseStep 1629395 = 2444093) B2444093
theorem B483839 : Blo 319836 483839 := bstep (se 1 (by rfl) ⟨362879, by rfl⟩ : syracuseStep 483839 = 725759) B725759
theorem B2057183 : Blo 319836 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B484379 : Blo 319836 484379 := bstep (se 1 (by rfl) ⟨363284, by rfl⟩ : syracuseStep 484379 = 726569) B726569
theorem B484799 : Blo 319836 484799 := bstep (se 1 (by rfl) ⟨363599, by rfl⟩ : syracuseStep 484799 = 727199) B727199
theorem B485147 : Blo 319836 485147 := bstep (se 1 (by rfl) ⟨363860, by rfl⟩ : syracuseStep 485147 = 727721) B727721
theorem B322175 : Blo 319836 322175 := bstep (se 1 (by rfl) ⟨241631, by rfl⟩ : syracuseStep 322175 = 483263) B483263
theorem B18541385 : Blo 319836 18541385 := bstep (se 2 (by rfl) ⟨6953019, by rfl⟩ : syracuseStep 18541385 = 13906039) B13906039
theorem B1830383 : Blo 319836 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B2616985 : Blo 319836 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B2225179 : Blo 319836 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B1636847 : Blo 319836 1636847 := bstep (se 1 (by rfl) ⟨1227635, by rfl⟩ : syracuseStep 1636847 = 2455271) B2455271
theorem B1178507 : Blo 319836 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B1244297 : Blo 319836 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B1835783 : Blo 319836 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B460495 : Blo 319836 460495 := bstep (se 1 (by rfl) ⟨345371, by rfl⟩ : syracuseStep 460495 = 690743) B690743
theorem B1083347 : Blo 319836 1083347 := bstep (se 1 (by rfl) ⟨812510, by rfl⟩ : syracuseStep 1083347 = 1625021) B1625021
theorem B1542655 : Blo 319836 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B723815 : Blo 319836 723815 := bstep (se 1 (by rfl) ⟨542861, by rfl⟩ : syracuseStep 723815 = 1085723) B1085723
theorem B725471 : Blo 319836 725471 := bstep (se 1 (by rfl) ⟨544103, by rfl⟩ : syracuseStep 725471 = 1088207) B1088207
theorem B1086263 : Blo 319836 1086263 := bstep (se 1 (by rfl) ⟨814697, by rfl⟩ : syracuseStep 1086263 = 1629395) B1629395
theorem B5838587 : Blo 319836 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B1382663 : Blo 319836 1382663 := bstep (se 1 (by rfl) ⟨1036997, by rfl⟩ : syracuseStep 1382663 = 2073995) B2073995
theorem B12360923 : Blo 319836 12360923 := bstep (se 1 (by rfl) ⟨9270692, by rfl⟩ : syracuseStep 12360923 = 18541385) B18541385
theorem B1220255 : Blo 319836 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B143401499 : Blo 319836 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B1091231 : Blo 319836 1091231 := bstep (se 1 (by rfl) ⟨818423, by rfl⟩ : syracuseStep 1091231 = 1636847) B1636847
theorem B829531 : Blo 319836 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B405415 : Blo 319836 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B19443887 : Blo 319836 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B3489313 : Blo 319836 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B2966905 : Blo 319836 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B775423 : Blo 319836 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B2119135 : Blo 319836 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B5528735 : Blo 319836 5528735 := bstep (se 1 (by rfl) ⟨4146551, by rfl⟩ : syracuseStep 5528735 = 8293103) B8293103
theorem B483071 : Blo 319836 483071 := bstep (se 1 (by rfl) ⟨362303, by rfl⟩ : syracuseStep 483071 = 724607) B724607
theorem B483449 : Blo 319836 483449 := bstep (se 2 (by rfl) ⟨181293, by rfl⟩ : syracuseStep 483449 = 362587) B362587
theorem B10445111 : Blo 319836 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B484841 : Blo 319836 484841 := bstep (se 2 (by rfl) ⟨181815, by rfl⟩ : syracuseStep 484841 = 363631) B363631
theorem B517679 : Blo 319836 517679 := bstep (se 1 (by rfl) ⟨388259, by rfl⟩ : syracuseStep 517679 = 776519) B776519
theorem B321231 : Blo 319836 321231 := bstep (se 1 (by rfl) ⟨240923, by rfl⟩ : syracuseStep 321231 = 481847) B481847
theorem B322559 : Blo 319836 322559 := bstep (se 1 (by rfl) ⟨241919, by rfl⟩ : syracuseStep 322559 = 483839) B483839
theorem B1371455 : Blo 319836 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B322919 : Blo 319836 322919 := bstep (se 1 (by rfl) ⟨242189, by rfl⟩ : syracuseStep 322919 = 484379) B484379
theorem B323199 : Blo 319836 323199 := bstep (se 1 (by rfl) ⟨242399, by rfl⟩ : syracuseStep 323199 = 484799) B484799
theorem B323431 : Blo 319836 323431 := bstep (se 1 (by rfl) ⟨242573, by rfl⟩ : syracuseStep 323431 = 485147) B485147
theorem B319713155 : Blo 319836 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B114782953 : Blo 319836 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B3142685 : Blo 319836 3142685 := bstep (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) B1178507
theorem B456457 : Blo 319836 456457 := bstep (se 2 (by rfl) ⟨171171, by rfl⟩ : syracuseStep 456457 = 342343) B342343
theorem B4424165 : Blo 319836 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B722231 : Blo 319836 722231 := bstep (se 1 (by rfl) ⟨541673, by rfl⟩ : syracuseStep 722231 = 1083347) B1083347
theorem B8227493 : Blo 319836 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B724175 : Blo 319836 724175 := bstep (se 1 (by rfl) ⟨543131, by rfl⟩ : syracuseStep 724175 = 1086263) B1086263
theorem B921775 : Blo 319836 921775 := bstep (se 1 (by rfl) ⟨691331, by rfl⟩ : syracuseStep 921775 = 1382663) B1382663
theorem B727487 : Blo 319836 727487 := bstep (se 1 (by rfl) ⟨545615, by rfl⟩ : syracuseStep 727487 = 1091231) B1091231
theorem B2825513 : Blo 319836 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B1223855 : Blo 319836 1223855 := bstep (se 1 (by rfl) ⟨917891, by rfl⟩ : syracuseStep 1223855 = 1835783) B1835783
theorem B3685823 : Blo 319836 3685823 := bstep (se 1 (by rfl) ⟨2764367, by rfl⟩ : syracuseStep 3685823 = 5528735) B5528735
theorem B8240615 : Blo 319836 8240615 := bstep (se 1 (by rfl) ⟨6180461, by rfl⟩ : syracuseStep 8240615 = 12360923) B12360923
theorem B540553 : Blo 319836 540553 := bstep (se 2 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 540553 = 405415) B405415
theorem B6963407 : Blo 319836 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B95600999 : Blo 319836 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B153043937 : Blo 319836 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B345119 : Blo 319836 345119 := bstep (se 1 (by rfl) ⟨258839, by rfl⟩ : syracuseStep 345119 = 517679) B517679
theorem B1033897 : Blo 319836 1033897 := bstep (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) B775423
theorem B608609 : Blo 319836 608609 := bstep (se 2 (by rfl) ⟨228228, by rfl⟩ : syracuseStep 608609 = 456457) B456457
theorem B213142103 : Blo 319836 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B12962591 : Blo 319836 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B3955873 : Blo 319836 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B482543 : Blo 319836 482543 := bstep (se 1 (by rfl) ⟨361907, by rfl⟩ : syracuseStep 482543 = 723815) B723815
theorem B613993 : Blo 319836 613993 := bstep (se 2 (by rfl) ⟨230247, by rfl⟩ : syracuseStep 613993 = 460495) B460495
theorem B8380493 : Blo 319836 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B483647 : Blo 319836 483647 := bstep (se 1 (by rfl) ⟨362735, by rfl⟩ : syracuseStep 483647 = 725471) B725471
theorem B3892391 : Blo 319836 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B813503 : Blo 319836 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B322047 : Blo 319836 322047 := bstep (se 1 (by rfl) ⟨241535, by rfl⟩ : syracuseStep 322047 = 483071) B483071
theorem B322299 : Blo 319836 322299 := bstep (se 1 (by rfl) ⟨241724, by rfl⟩ : syracuseStep 322299 = 483449) B483449
theorem B323227 : Blo 319836 323227 := bstep (se 1 (by rfl) ⟨242420, by rfl⟩ : syracuseStep 323227 = 484841) B484841
theorem B914303 : Blo 319836 914303 := bstep (se 1 (by rfl) ⟨685727, by rfl⟩ : syracuseStep 914303 = 1371455) B1371455
theorem B4652417 : Blo 319836 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B63733999 : Blo 319836 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B2949443 : Blo 319836 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B1378529 : Blo 319836 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B920317 : Blo 319836 920317 := bstep (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) B345119
theorem B2594927 : Blo 319836 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B405739 : Blo 319836 405739 := bstep (se 1 (by rfl) ⟨304304, by rfl⟩ : syracuseStep 405739 = 608609) B608609
theorem B142094735 : Blo 319836 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B5484995 : Blo 319836 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B1883675 : Blo 319836 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B5586995 : Blo 319836 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B1229033 : Blo 319836 1229033 := bstep (se 2 (by rfl) ⟨460887, by rfl⟩ : syracuseStep 1229033 = 921775) B921775
theorem B542335 : Blo 319836 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B609535 : Blo 319836 609535 := bstep (se 1 (by rfl) ⟨457151, by rfl⟩ : syracuseStep 609535 = 914303) B914303
theorem B3101611 : Blo 319836 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B5493743 : Blo 319836 5493743 := bstep (se 1 (by rfl) ⟨4120307, by rfl⟩ : syracuseStep 5493743 = 8240615) B8240615
theorem B4642271 : Blo 319836 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B102029291 : Blo 319836 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B481487 : Blo 319836 481487 := bstep (se 1 (by rfl) ⟨361115, by rfl⟩ : syracuseStep 481487 = 722231) B722231
theorem B8641727 : Blo 319836 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B482783 : Blo 319836 482783 := bstep (se 1 (by rfl) ⟨362087, by rfl⟩ : syracuseStep 482783 = 724175) B724175
theorem B484991 : Blo 319836 484991 := bstep (se 1 (by rfl) ⟨363743, by rfl⟩ : syracuseStep 484991 = 727487) B727487
theorem B321695 : Blo 319836 321695 := bstep (se 1 (by rfl) ⟨241271, by rfl⟩ : syracuseStep 321695 = 482543) B482543
theorem B322431 : Blo 319836 322431 := bstep (se 1 (by rfl) ⟨241823, by rfl⟩ : syracuseStep 322431 = 483647) B483647
theorem B815903 : Blo 319836 815903 := bstep (se 1 (by rfl) ⟨611927, by rfl⟩ : syracuseStep 815903 = 1223855) B1223855
theorem B5274497 : Blo 319836 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B818657 : Blo 319836 818657 := bstep (se 2 (by rfl) ⟨306996, by rfl⟩ : syracuseStep 818657 = 613993) B613993
theorem B2457215 : Blo 319836 2457215 := bstep (se 1 (by rfl) ⟨1842911, by rfl⟩ : syracuseStep 2457215 = 3685823) B3685823
theorem B720737 : Blo 319836 720737 := bstep (se 2 (by rfl) ⟨270276, by rfl⟩ : syracuseStep 720737 = 540553) B540553
theorem B819355 : Blo 319836 819355 := bstep (se 1 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 819355 = 1229033) B1229033
theorem B1966295 : Blo 319836 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B919019 : Blo 319836 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B723113 : Blo 319836 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B6919805 : Blo 319836 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B4135481 : Blo 319836 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B3516331 : Blo 319836 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B1255783 : Blo 319836 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B84978665 : Blo 319836 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B3094847 : Blo 319836 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B1227089 : Blo 319836 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B540985 : Blo 319836 540985 := bstep (se 2 (by rfl) ⟨202869, by rfl⟩ : syracuseStep 540985 = 405739) B405739
theorem B3656663 : Blo 319836 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B543935 : Blo 319836 543935 := bstep (se 1 (by rfl) ⟨407951, by rfl⟩ : syracuseStep 543935 = 815903) B815903
theorem B545771 : Blo 319836 545771 := bstep (se 1 (by rfl) ⟨409328, by rfl⟩ : syracuseStep 545771 = 818657) B818657
theorem B480491 : Blo 319836 480491 := bstep (se 1 (by rfl) ⟨360368, by rfl⟩ : syracuseStep 480491 = 720737) B720737
theorem B3724663 : Blo 319836 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B3662495 : Blo 319836 3662495 := bstep (se 1 (by rfl) ⟨2746871, by rfl⟩ : syracuseStep 3662495 = 5493743) B5493743
theorem B68019527 : Blo 319836 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B320991 : Blo 319836 320991 := bstep (se 1 (by rfl) ⟨240743, by rfl⟩ : syracuseStep 320991 = 481487) B481487
theorem B812713 : Blo 319836 812713 := bstep (se 2 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 812713 = 609535) B609535
theorem B5761151 : Blo 319836 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B321855 : Blo 319836 321855 := bstep (se 1 (by rfl) ⟨241391, by rfl⟩ : syracuseStep 321855 = 482783) B482783
theorem B323327 : Blo 319836 323327 := bstep (se 1 (by rfl) ⟨242495, by rfl⟩ : syracuseStep 323327 = 484991) B484991
theorem B94729823 : Blo 319836 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B1638143 : Blo 319836 1638143 := bstep (se 1 (by rfl) ⟨1228607, by rfl⟩ : syracuseStep 1638143 = 2457215) B2457215
theorem B1310863 : Blo 319836 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B721313 : Blo 319836 721313 := bstep (se 2 (by rfl) ⟨270492, by rfl⟩ : syracuseStep 721313 = 540985) B540985
theorem B362623 : Blo 319836 362623 := bstep (se 1 (by rfl) ⟨271967, by rfl⟩ : syracuseStep 362623 = 543935) B543935
theorem B1083617 : Blo 319836 1083617 := bstep (se 2 (by rfl) ⟨406356, by rfl⟩ : syracuseStep 1083617 = 812713) B812713
theorem B4688441 : Blo 319836 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B1674377 : Blo 319836 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B363847 : Blo 319836 363847 := bstep (se 1 (by rfl) ⟨272885, by rfl⟩ : syracuseStep 363847 = 545771) B545771
theorem B2756987 : Blo 319836 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B3840767 : Blo 319836 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B63153215 : Blo 319836 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B1092095 : Blo 319836 1092095 := bstep (se 1 (by rfl) ⟨819071, by rfl⟩ : syracuseStep 1092095 = 1638143) B1638143
theorem B1092473 : Blo 319836 1092473 := bstep (se 2 (by rfl) ⟨409677, by rfl⟩ : syracuseStep 1092473 = 819355) B819355
theorem B2437775 : Blo 319836 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B2441663 : Blo 319836 2441663 := bstep (se 1 (by rfl) ⟨1831247, by rfl⟩ : syracuseStep 2441663 = 3662495) B3662495
theorem B4966217 : Blo 319836 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B612679 : Blo 319836 612679 := bstep (se 1 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 612679 = 919019) B919019
theorem B482075 : Blo 319836 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B320327 : Blo 319836 320327 := bstep (se 1 (by rfl) ⟨240245, by rfl⟩ : syracuseStep 320327 = 480491) B480491
theorem B4613203 : Blo 319836 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B45346351 : Blo 319836 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B56652443 : Blo 319836 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B2063231 : Blo 319836 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B818059 : Blo 319836 818059 := bstep (se 1 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 818059 = 1227089) B1227089
theorem B3310811 : Blo 319836 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B722411 : Blo 319836 722411 := bstep (se 1 (by rfl) ⟨541808, by rfl⟩ : syracuseStep 722411 = 1083617) B1083617
theorem B1116251 : Blo 319836 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B1837991 : Blo 319836 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B2560511 : Blo 319836 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B60461801 : Blo 319836 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B728063 : Blo 319836 728063 := bstep (se 1 (by rfl) ⟨546047, by rfl⟩ : syracuseStep 728063 = 1092095) B1092095
theorem B728315 : Blo 319836 728315 := bstep (se 1 (by rfl) ⟨546236, by rfl⟩ : syracuseStep 728315 = 1092473) B1092473
theorem B1090745 : Blo 319836 1090745 := bstep (se 2 (by rfl) ⟨409029, by rfl⟩ : syracuseStep 1090745 = 818059) B818059
theorem B1747817 : Blo 319836 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B3125627 : Blo 319836 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B1625183 : Blo 319836 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B37768295 : Blo 319836 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B480875 : Blo 319836 480875 := bstep (se 1 (by rfl) ⟨360656, by rfl⟩ : syracuseStep 480875 = 721313) B721313
theorem B1627775 : Blo 319836 1627775 := bstep (se 1 (by rfl) ⟨1220831, by rfl⟩ : syracuseStep 1627775 = 2441663) B2441663
theorem B6150937 : Blo 319836 6150937 := bstep (se 2 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 6150937 = 4613203) B4613203
theorem B483497 : Blo 319836 483497 := bstep (se 2 (by rfl) ⟨181311, by rfl⟩ : syracuseStep 483497 = 362623) B362623
theorem B485129 : Blo 319836 485129 := bstep (se 2 (by rfl) ⟨181923, by rfl⟩ : syracuseStep 485129 = 363847) B363847
theorem B321383 : Blo 319836 321383 := bstep (se 1 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 321383 = 482075) B482075
theorem B42102143 : Blo 319836 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B816905 : Blo 319836 816905 := bstep (se 2 (by rfl) ⟨306339, by rfl⟩ : syracuseStep 816905 = 612679) B612679
theorem B1375487 : Blo 319836 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B1083455 : Blo 319836 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B1707007 : Blo 319836 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B40307867 : Blo 319836 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B1085183 : Blo 319836 1085183 := bstep (se 1 (by rfl) ⟨813887, by rfl⟩ : syracuseStep 1085183 = 1627775) B1627775
theorem B727163 : Blo 319836 727163 := bstep (se 1 (by rfl) ⟨545372, by rfl⟩ : syracuseStep 727163 = 1090745) B1090745
theorem B8201249 : Blo 319836 8201249 := bstep (se 2 (by rfl) ⟨3075468, by rfl⟩ : syracuseStep 8201249 = 6150937) B6150937
theorem B2207207 : Blo 319836 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B1225327 : Blo 319836 1225327 := bstep (se 1 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 1225327 = 1837991) B1837991
theorem B25178863 : Blo 319836 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B1165211 : Blo 319836 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B28068095 : Blo 319836 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B2083751 : Blo 319836 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B544603 : Blo 319836 544603 := bstep (se 1 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 544603 = 816905) B816905
theorem B481607 : Blo 319836 481607 := bstep (se 1 (by rfl) ⟨361205, by rfl⟩ : syracuseStep 481607 = 722411) B722411
theorem B744167 : Blo 319836 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B320583 : Blo 319836 320583 := bstep (se 1 (by rfl) ⟨240437, by rfl⟩ : syracuseStep 320583 = 480875) B480875
theorem B485375 : Blo 319836 485375 := bstep (se 1 (by rfl) ⟨364031, by rfl⟩ : syracuseStep 485375 = 728063) B728063
theorem B485543 : Blo 319836 485543 := bstep (se 1 (by rfl) ⟨364157, by rfl⟩ : syracuseStep 485543 = 728315) B728315
theorem B322331 : Blo 319836 322331 := bstep (se 1 (by rfl) ⟨241748, by rfl⟩ : syracuseStep 322331 = 483497) B483497
theorem B323419 : Blo 319836 323419 := bstep (se 1 (by rfl) ⟨242564, by rfl⟩ : syracuseStep 323419 = 485129) B485129
theorem B916991 : Blo 319836 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B722303 : Blo 319836 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B18712063 : Blo 319836 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B26871911 : Blo 319836 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B723455 : Blo 319836 723455 := bstep (se 1 (by rfl) ⟨542591, by rfl⟩ : syracuseStep 723455 = 1085183) B1085183
theorem B726137 : Blo 319836 726137 := bstep (se 2 (by rfl) ⟨272301, by rfl⟩ : syracuseStep 726137 = 544603) B544603
theorem B1389167 : Blo 319836 1389167 := bstep (se 1 (by rfl) ⟨1041875, by rfl⟩ : syracuseStep 1389167 = 2083751) B2083751
theorem B2276009 : Blo 319836 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B33571817 : Blo 319836 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B1984445 : Blo 319836 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B5885885 : Blo 319836 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B611327 : Blo 319836 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B776807 : Blo 319836 776807 := bstep (se 1 (by rfl) ⟨582605, by rfl⟩ : syracuseStep 776807 = 1165211) B1165211
theorem B484775 : Blo 319836 484775 := bstep (se 1 (by rfl) ⟨363581, by rfl⟩ : syracuseStep 484775 = 727163) B727163
theorem B321071 : Blo 319836 321071 := bstep (se 1 (by rfl) ⟨240803, by rfl⟩ : syracuseStep 321071 = 481607) B481607
theorem B5467499 : Blo 319836 5467499 := bstep (se 1 (by rfl) ⟨4100624, by rfl⟩ : syracuseStep 5467499 = 8201249) B8201249
theorem B1633769 : Blo 319836 1633769 := bstep (se 2 (by rfl) ⟨612663, by rfl⟩ : syracuseStep 1633769 = 1225327) B1225327
theorem B323583 : Blo 319836 323583 := bstep (se 1 (by rfl) ⟨242687, by rfl⟩ : syracuseStep 323583 = 485375) B485375
theorem B323695 : Blo 319836 323695 := bstep (se 1 (by rfl) ⟨242771, by rfl⟩ : syracuseStep 323695 = 485543) B485543
theorem B22381211 : Blo 319836 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B3644999 : Blo 319836 3644999 := bstep (se 1 (by rfl) ⟨2733749, by rfl⟩ : syracuseStep 3644999 = 5467499) B5467499
theorem B1089179 : Blo 319836 1089179 := bstep (se 1 (by rfl) ⟨816884, by rfl⟩ : syracuseStep 1089179 = 1633769) B1633769
theorem B926111 : Blo 319836 926111 := bstep (se 1 (by rfl) ⟨694583, by rfl⟩ : syracuseStep 926111 = 1389167) B1389167
theorem B1517339 : Blo 319836 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B1322963 : Blo 319836 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B24949417 : Blo 319836 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B481535 : Blo 319836 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B17914607 : Blo 319836 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B482303 : Blo 319836 482303 := bstep (se 1 (by rfl) ⟨361727, by rfl⟩ : syracuseStep 482303 = 723455) B723455
theorem B3923923 : Blo 319836 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B1630205 : Blo 319836 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B484091 : Blo 319836 484091 := bstep (se 1 (by rfl) ⟨363068, by rfl⟩ : syracuseStep 484091 = 726137) B726137
theorem B517871 : Blo 319836 517871 := bstep (se 1 (by rfl) ⟨388403, by rfl⟩ : syracuseStep 517871 = 776807) B776807
theorem B323183 : Blo 319836 323183 := bstep (se 1 (by rfl) ⟨242387, by rfl⟩ : syracuseStep 323183 = 484775) B484775
theorem B1380989 : Blo 319836 1380989 := bstep (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) B517871
theorem B2429999 : Blo 319836 2429999 := bstep (se 1 (by rfl) ⟨1822499, by rfl⟩ : syracuseStep 2429999 = 3644999) B3644999
theorem B726119 : Blo 319836 726119 := bstep (se 1 (by rfl) ⟨544589, by rfl⟩ : syracuseStep 726119 = 1089179) B1089179
theorem B1086803 : Blo 319836 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B33265889 : Blo 319836 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B14920807 : Blo 319836 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B2469629 : Blo 319836 2469629 := bstep (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) B926111
theorem B11943071 : Blo 319836 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B5231897 : Blo 319836 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B321023 : Blo 319836 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B321535 : Blo 319836 321535 := bstep (se 1 (by rfl) ⟨241151, by rfl⟩ : syracuseStep 321535 = 482303) B482303
theorem B322727 : Blo 319836 322727 := bstep (se 1 (by rfl) ⟨242045, by rfl⟩ : syracuseStep 322727 = 484091) B484091
theorem B1011559 : Blo 319836 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B881975 : Blo 319836 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B920659 : Blo 319836 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B724535 : Blo 319836 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B19894409 : Blo 319836 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B1348745 : Blo 319836 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B1646419 : Blo 319836 1646419 := bstep (se 1 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 1646419 = 2469629) B2469629
theorem B1619999 : Blo 319836 1619999 := bstep (se 1 (by rfl) ⟨1214999, by rfl⟩ : syracuseStep 1619999 = 2429999) B2429999
theorem B3487931 : Blo 319836 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B484079 : Blo 319836 484079 := bstep (se 1 (by rfl) ⟨363059, by rfl⟩ : syracuseStep 484079 = 726119) B726119
theorem B22177259 : Blo 319836 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B587983 : Blo 319836 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B7962047 : Blo 319836 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B14784839 : Blo 319836 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B1227545 : Blo 319836 1227545 := bstep (se 2 (by rfl) ⟨460329, by rfl⟩ : syracuseStep 1227545 = 920659) B920659
theorem B483023 : Blo 319836 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B13262939 : Blo 319836 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B3596653 : Blo 319836 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B322719 : Blo 319836 322719 := bstep (se 1 (by rfl) ⟨242039, by rfl⟩ : syracuseStep 322719 = 484079) B484079
theorem B783977 : Blo 319836 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B1079999 : Blo 319836 1079999 := bstep (se 1 (by rfl) ⟨809999, by rfl⟩ : syracuseStep 1079999 = 1619999) B1619999
theorem B2325287 : Blo 319836 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B5308031 : Blo 319836 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B2195225 : Blo 319836 2195225 := bstep (se 2 (by rfl) ⟨823209, by rfl⟩ : syracuseStep 2195225 = 1646419) B1646419
theorem B1550191 : Blo 319836 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B4795537 : Blo 319836 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B1463483 : Blo 319836 1463483 := bstep (se 1 (by rfl) ⟨1097612, by rfl⟩ : syracuseStep 1463483 = 2195225) B2195225
theorem B9856559 : Blo 319836 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B2090605 : Blo 319836 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B322015 : Blo 319836 322015 := bstep (se 1 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 322015 = 483023) B483023
theorem B8841959 : Blo 319836 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B719999 : Blo 319836 719999 := bstep (se 1 (by rfl) ⟨539999, by rfl⟩ : syracuseStep 719999 = 1079999) B1079999
theorem B818363 : Blo 319836 818363 := bstep (se 1 (by rfl) ⟨613772, by rfl⟩ : syracuseStep 818363 = 1227545) B1227545
theorem B3538687 : Blo 319836 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B2787473 : Blo 319836 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B2066921 : Blo 319836 2066921 := bstep (se 2 (by rfl) ⟨775095, by rfl⟩ : syracuseStep 2066921 = 1550191) B1550191
theorem B6394049 : Blo 319836 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B6571039 : Blo 319836 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B479999 : Blo 319836 479999 := bstep (se 1 (by rfl) ⟨359999, by rfl⟩ : syracuseStep 479999 = 719999) B719999
theorem B545575 : Blo 319836 545575 := bstep (se 1 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 545575 = 818363) B818363
theorem B975655 : Blo 319836 975655 := bstep (se 1 (by rfl) ⟨731741, by rfl⟩ : syracuseStep 975655 = 1463483) B1463483
theorem B5894639 : Blo 319836 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B4718249 : Blo 319836 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B1377947 : Blo 319836 1377947 := bstep (se 1 (by rfl) ⟨1033460, by rfl⟩ : syracuseStep 1377947 = 2066921) B2066921
theorem B4262699 : Blo 319836 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B727433 : Blo 319836 727433 := bstep (se 2 (by rfl) ⟨272787, by rfl⟩ : syracuseStep 727433 = 545575) B545575
theorem B8761385 : Blo 319836 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B1300873 : Blo 319836 1300873 := bstep (se 2 (by rfl) ⟨487827, by rfl⟩ : syracuseStep 1300873 = 975655) B975655
theorem B1858315 : Blo 319836 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B319999 : Blo 319836 319999 := bstep (se 1 (by rfl) ⟨239999, by rfl⟩ : syracuseStep 319999 = 479999) B479999
theorem B3929759 : Blo 319836 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B3145499 : Blo 319836 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B918631 : Blo 319836 918631 := bstep (se 1 (by rfl) ⟨688973, by rfl⟩ : syracuseStep 918631 = 1377947) B1377947
theorem B5840923 : Blo 319836 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B2477753 : Blo 319836 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B2841799 : Blo 319836 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B484955 : Blo 319836 484955 := bstep (se 1 (by rfl) ⟨363716, by rfl⟩ : syracuseStep 484955 = 727433) B727433
theorem B1734497 : Blo 319836 1734497 := bstep (se 2 (by rfl) ⟨650436, by rfl⟩ : syracuseStep 1734497 = 1300873) B1300873
theorem B2619839 : Blo 319836 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B2096999 : Blo 319836 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B1156331 : Blo 319836 1156331 := bstep (se 1 (by rfl) ⟨867248, by rfl⟩ : syracuseStep 1156331 = 1734497) B1734497
theorem B1746559 : Blo 319836 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B1224841 : Blo 319836 1224841 := bstep (se 2 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 1224841 = 918631) B918631
theorem B1651835 : Blo 319836 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B3789065 : Blo 319836 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B1397999 : Blo 319836 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B7787897 : Blo 319836 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B323303 : Blo 319836 323303 := bstep (se 1 (by rfl) ⟨242477, by rfl⟩ : syracuseStep 323303 = 484955) B484955
theorem B2328745 : Blo 319836 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B10104173 : Blo 319836 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B931999 : Blo 319836 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B5191931 : Blo 319836 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B770887 : Blo 319836 770887 := bstep (se 1 (by rfl) ⟨578165, by rfl⟩ : syracuseStep 770887 = 1156331) B1156331
theorem B1101223 : Blo 319836 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B1633121 : Blo 319836 1633121 := bstep (se 2 (by rfl) ⟨612420, by rfl⟩ : syracuseStep 1633121 = 1224841) B1224841
theorem B1088747 : Blo 319836 1088747 := bstep (se 1 (by rfl) ⟨816560, by rfl⟩ : syracuseStep 1088747 = 1633121) B1633121
theorem B1027849 : Blo 319836 1027849 := bstep (se 2 (by rfl) ⟨385443, by rfl⟩ : syracuseStep 1027849 = 770887) B770887
theorem B6736115 : Blo 319836 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B3461287 : Blo 319836 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B3104993 : Blo 319836 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B1468297 : Blo 319836 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B1242665 : Blo 319836 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B4490743 : Blo 319836 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B725831 : Blo 319836 725831 := bstep (se 1 (by rfl) ⟨544373, by rfl⟩ : syracuseStep 725831 = 1088747) B1088747
theorem B828443 : Blo 319836 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B8279981 : Blo 319836 8279981 := bstep (se 3 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 8279981 = 3104993) B3104993
theorem B1370465 : Blo 319836 1370465 := bstep (se 2 (by rfl) ⟨513924, by rfl⟩ : syracuseStep 1370465 = 1027849) B1027849
theorem B4615049 : Blo 319836 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B7830917 : Blo 319836 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B5220611 : Blo 319836 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B5519987 : Blo 319836 5519987 := bstep (se 1 (by rfl) ⟨4139990, by rfl⟩ : syracuseStep 5519987 = 8279981) B8279981
theorem B5987657 : Blo 319836 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B483887 : Blo 319836 483887 := bstep (se 1 (by rfl) ⟨362915, by rfl⟩ : syracuseStep 483887 = 725831) B725831
theorem B552295 : Blo 319836 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B913643 : Blo 319836 913643 := bstep (se 1 (by rfl) ⟨685232, by rfl⟩ : syracuseStep 913643 = 1370465) B1370465
theorem B3076699 : Blo 319836 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B4102265 : Blo 319836 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B3480407 : Blo 319836 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B3679991 : Blo 319836 3679991 := bstep (se 1 (by rfl) ⟨2759993, by rfl⟩ : syracuseStep 3679991 = 5519987) B5519987
theorem B736393 : Blo 319836 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B609095 : Blo 319836 609095 := bstep (se 1 (by rfl) ⟨456821, by rfl⟩ : syracuseStep 609095 = 913643) B913643
theorem B3991771 : Blo 319836 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B322591 : Blo 319836 322591 := bstep (se 1 (by rfl) ⟨241943, by rfl⟩ : syracuseStep 322591 = 483887) B483887
theorem B406063 : Blo 319836 406063 := bstep (se 1 (by rfl) ⟨304547, by rfl⟩ : syracuseStep 406063 = 609095) B609095
theorem B5322361 : Blo 319836 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B2734843 : Blo 319836 2734843 := bstep (se 1 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 2734843 = 4102265) B4102265
theorem B2320271 : Blo 319836 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B2453327 : Blo 319836 2453327 := bstep (se 1 (by rfl) ⟨1839995, by rfl⟩ : syracuseStep 2453327 = 3679991) B3679991
theorem B981857 : Blo 319836 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B1546847 : Blo 319836 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B3646457 : Blo 319836 3646457 := bstep (se 2 (by rfl) ⟨1367421, by rfl⟩ : syracuseStep 3646457 = 2734843) B2734843
theorem B541417 : Blo 319836 541417 := bstep (se 2 (by rfl) ⟨203031, by rfl⟩ : syracuseStep 541417 = 406063) B406063
theorem B7096481 : Blo 319836 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B1635551 : Blo 319836 1635551 := bstep (se 1 (by rfl) ⟨1226663, by rfl⟩ : syracuseStep 1635551 = 2453327) B2453327
theorem B654571 : Blo 319836 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B721889 : Blo 319836 721889 := bstep (se 2 (by rfl) ⟨270708, by rfl⟩ : syracuseStep 721889 = 541417) B541417
theorem B2430971 : Blo 319836 2430971 := bstep (se 1 (by rfl) ⟨1823228, by rfl⟩ : syracuseStep 2430971 = 3646457) B3646457
theorem B1090367 : Blo 319836 1090367 := bstep (se 1 (by rfl) ⟨817775, by rfl⟩ : syracuseStep 1090367 = 1635551) B1635551
theorem B4730987 : Blo 319836 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B1031231 : Blo 319836 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B3491045 : Blo 319836 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B2327363 : Blo 319836 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B726911 : Blo 319836 726911 := bstep (se 1 (by rfl) ⟨545183, by rfl⟩ : syracuseStep 726911 = 1090367) B1090367
theorem B3153991 : Blo 319836 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B1620647 : Blo 319836 1620647 := bstep (se 1 (by rfl) ⟨1215485, by rfl⟩ : syracuseStep 1620647 = 2430971) B2430971
theorem B481259 : Blo 319836 481259 := bstep (se 1 (by rfl) ⟨360944, by rfl⟩ : syracuseStep 481259 = 721889) B721889
theorem B2749949 : Blo 319836 2749949 := bstep (se 3 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 2749949 = 1031231) B1031231
theorem B4205321 : Blo 319836 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B1551575 : Blo 319836 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B484607 : Blo 319836 484607 := bstep (se 1 (by rfl) ⟨363455, by rfl⟩ : syracuseStep 484607 = 726911) B726911
theorem B320839 : Blo 319836 320839 := bstep (se 1 (by rfl) ⟨240629, by rfl⟩ : syracuseStep 320839 = 481259) B481259
theorem B1833299 : Blo 319836 1833299 := bstep (se 1 (by rfl) ⟨1374974, by rfl⟩ : syracuseStep 1833299 = 2749949) B2749949
theorem B1080431 : Blo 319836 1080431 := bstep (se 1 (by rfl) ⟨810323, by rfl⟩ : syracuseStep 1080431 = 1620647) B1620647
theorem B1222199 : Blo 319836 1222199 := bstep (se 1 (by rfl) ⟨916649, by rfl⟩ : syracuseStep 1222199 = 1833299) B1833299
theorem B2803547 : Blo 319836 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B1034383 : Blo 319836 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B323071 : Blo 319836 323071 := bstep (se 1 (by rfl) ⟨242303, by rfl⟩ : syracuseStep 323071 = 484607) B484607
theorem B720287 : Blo 319836 720287 := bstep (se 1 (by rfl) ⟨540215, by rfl⟩ : syracuseStep 720287 = 1080431) B1080431
theorem B1869031 : Blo 319836 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B1379177 : Blo 319836 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B480191 : Blo 319836 480191 := bstep (se 1 (by rfl) ⟨360143, by rfl⟩ : syracuseStep 480191 = 720287) B720287
theorem B814799 : Blo 319836 814799 := bstep (se 1 (by rfl) ⟨611099, by rfl⟩ : syracuseStep 814799 = 1222199) B1222199
theorem B2492041 : Blo 319836 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B919451 : Blo 319836 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B543199 : Blo 319836 543199 := bstep (se 1 (by rfl) ⟨407399, by rfl⟩ : syracuseStep 543199 = 814799) B814799
theorem B320127 : Blo 319836 320127 := bstep (se 1 (by rfl) ⟨240095, by rfl⟩ : syracuseStep 320127 = 480191) B480191
theorem B724265 : Blo 319836 724265 := bstep (se 2 (by rfl) ⟨271599, by rfl⟩ : syracuseStep 724265 = 543199) B543199
theorem B3322721 : Blo 319836 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2451869 : Blo 319836 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B2215147 : Blo 319836 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B482843 : Blo 319836 482843 := bstep (se 1 (by rfl) ⟨362132, by rfl⟩ : syracuseStep 482843 = 724265) B724265
theorem B1634579 : Blo 319836 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B2953529 : Blo 319836 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B1089719 : Blo 319836 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B321895 : Blo 319836 321895 := bstep (se 1 (by rfl) ⟨241421, by rfl⟩ : syracuseStep 321895 = 482843) B482843
theorem B1969019 : Blo 319836 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B726479 : Blo 319836 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B1312679 : Blo 319836 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B484319 : Blo 319836 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B875119 : Blo 319836 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B322879 : Blo 319836 322879 := bstep (se 1 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 322879 = 484319) B484319
theorem B1166825 : Blo 319836 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B3111533 : Blo 319836 3111533 := bstep (se 3 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 3111533 = 1166825) B1166825
theorem B2074355 : Blo 319836 2074355 := bstep (se 1 (by rfl) ⟨1555766, by rfl⟩ : syracuseStep 2074355 = 3111533) B3111533
theorem B1382903 : Blo 319836 1382903 := bstep (se 1 (by rfl) ⟨1037177, by rfl⟩ : syracuseStep 1382903 = 2074355) B2074355
theorem B921935 : Blo 319836 921935 := bstep (se 1 (by rfl) ⟨691451, by rfl⟩ : syracuseStep 921935 = 1382903) B1382903
theorem B614623 : Blo 319836 614623 := bstep (se 1 (by rfl) ⟨460967, by rfl⟩ : syracuseStep 614623 = 921935) B921935
theorem B819497 : Blo 319836 819497 := bstep (se 2 (by rfl) ⟨307311, by rfl⟩ : syracuseStep 819497 = 614623) B614623
theorem B546331 : Blo 319836 546331 := bstep (se 1 (by rfl) ⟨409748, by rfl⟩ : syracuseStep 546331 = 819497) B819497
theorem B728441 : Blo 319836 728441 := bstep (se 2 (by rfl) ⟨273165, by rfl⟩ : syracuseStep 728441 = 546331) B546331
theorem B485627 : Blo 319836 485627 := bstep (se 1 (by rfl) ⟨364220, by rfl⟩ : syracuseStep 485627 = 728441) B728441
theorem B323751 : Blo 319836 323751 := bstep (se 1 (by rfl) ⟨242813, by rfl⟩ : syracuseStep 323751 = 485627) B485627

theorem C0 (j : ℕ) (h1 : 79959 ≤ j) (h2 : j ≤ 80658) : Blo 319836 (4 * j + 3) := by
  interval_cases j
  · exact B319839
  · exact B319843
  · exact B319847
  · exact B319851
  · exact B319855
  · exact B319859
  · exact B319863
  · exact B319867
  · exact B319871
  · exact B319875
  · exact B319879
  · exact B319883
  · exact B319887
  · exact B319891
  · exact B319895
  · exact B319899
  · exact B319903
  · exact B319907
  · exact B319911
  · exact B319915
  · exact B319919
  · exact B319923
  · exact B319927
  · exact B319931
  · exact B319935
  · exact B319939
  · exact B319943
  · exact B319947
  · exact B319951
  · exact B319955
  · exact B319959
  · exact B319963
  · exact B319967
  · exact B319971
  · exact B319975
  · exact B319979
  · exact B319983
  · exact B319987
  · exact B319991
  · exact B319995
  · exact B319999
  · exact B320003
  · exact B320007
  · exact B320011
  · exact B320015
  · exact B320019
  · exact B320023
  · exact B320027
  · exact B320031
  · exact B320035
  · exact B320039
  · exact B320043
  · exact B320047
  · exact B320051
  · exact B320055
  · exact B320059
  · exact B320063
  · exact B320067
  · exact B320071
  · exact B320075
  · exact B320079
  · exact B320083
  · exact B320087
  · exact B320091
  · exact B320095
  · exact B320099
  · exact B320103
  · exact B320107
  · exact B320111
  · exact B320115
  · exact B320119
  · exact B320123
  · exact B320127
  · exact B320131
  · exact B320135
  · exact B320139
  · exact B320143
  · exact B320147
  · exact B320151
  · exact B320155
  · exact B320159
  · exact B320163
  · exact B320167
  · exact B320171
  · exact B320175
  · exact B320179
  · exact B320183
  · exact B320187
  · exact B320191
  · exact B320195
  · exact B320199
  · exact B320203
  · exact B320207
  · exact B320211
  · exact B320215
  · exact B320219
  · exact B320223
  · exact B320227
  · exact B320231
  · exact B320235
  · exact B320239
  · exact B320243
  · exact B320247
  · exact B320251
  · exact B320255
  · exact B320259
  · exact B320263
  · exact B320267
  · exact B320271
  · exact B320275
  · exact B320279
  · exact B320283
  · exact B320287
  · exact B320291
  · exact B320295
  · exact B320299
  · exact B320303
  · exact B320307
  · exact B320311
  · exact B320315
  · exact B320319
  · exact B320323
  · exact B320327
  · exact B320331
  · exact B320335
  · exact B320339
  · exact B320343
  · exact B320347
  · exact B320351
  · exact B320355
  · exact B320359
  · exact B320363
  · exact B320367
  · exact B320371
  · exact B320375
  · exact B320379
  · exact B320383
  · exact B320387
  · exact B320391
  · exact B320395
  · exact B320399
  · exact B320403
  · exact B320407
  · exact B320411
  · exact B320415
  · exact B320419
  · exact B320423
  · exact B320427
  · exact B320431
  · exact B320435
  · exact B320439
  · exact B320443
  · exact B320447
  · exact B320451
  · exact B320455
  · exact B320459
  · exact B320463
  · exact B320467
  · exact B320471
  · exact B320475
  · exact B320479
  · exact B320483
  · exact B320487
  · exact B320491
  · exact B320495
  · exact B320499
  · exact B320503
  · exact B320507
  · exact B320511
  · exact B320515
  · exact B320519
  · exact B320523
  · exact B320527
  · exact B320531
  · exact B320535
  · exact B320539
  · exact B320543
  · exact B320547
  · exact B320551
  · exact B320555
  · exact B320559
  · exact B320563
  · exact B320567
  · exact B320571
  · exact B320575
  · exact B320579
  · exact B320583
  · exact B320587
  · exact B320591
  · exact B320595
  · exact B320599
  · exact B320603
  · exact B320607
  · exact B320611
  · exact B320615
  · exact B320619
  · exact B320623
  · exact B320627
  · exact B320631
  · exact B320635
  · exact B320639
  · exact B320643
  · exact B320647
  · exact B320651
  · exact B320655
  · exact B320659
  · exact B320663
  · exact B320667
  · exact B320671
  · exact B320675
  · exact B320679
  · exact B320683
  · exact B320687
  · exact B320691
  · exact B320695
  · exact B320699
  · exact B320703
  · exact B320707
  · exact B320711
  · exact B320715
  · exact B320719
  · exact B320723
  · exact B320727
  · exact B320731
  · exact B320735
  · exact B320739
  · exact B320743
  · exact B320747
  · exact B320751
  · exact B320755
  · exact B320759
  · exact B320763
  · exact B320767
  · exact B320771
  · exact B320775
  · exact B320779
  · exact B320783
  · exact B320787
  · exact B320791
  · exact B320795
  · exact B320799
  · exact B320803
  · exact B320807
  · exact B320811
  · exact B320815
  · exact B320819
  · exact B320823
  · exact B320827
  · exact B320831
  · exact B320835
  · exact B320839
  · exact B320843
  · exact B320847
  · exact B320851
  · exact B320855
  · exact B320859
  · exact B320863
  · exact B320867
  · exact B320871
  · exact B320875
  · exact B320879
  · exact B320883
  · exact B320887
  · exact B320891
  · exact B320895
  · exact B320899
  · exact B320903
  · exact B320907
  · exact B320911
  · exact B320915
  · exact B320919
  · exact B320923
  · exact B320927
  · exact B320931
  · exact B320935
  · exact B320939
  · exact B320943
  · exact B320947
  · exact B320951
  · exact B320955
  · exact B320959
  · exact B320963
  · exact B320967
  · exact B320971
  · exact B320975
  · exact B320979
  · exact B320983
  · exact B320987
  · exact B320991
  · exact B320995
  · exact B320999
  · exact B321003
  · exact B321007
  · exact B321011
  · exact B321015
  · exact B321019
  · exact B321023
  · exact B321027
  · exact B321031
  · exact B321035
  · exact B321039
  · exact B321043
  · exact B321047
  · exact B321051
  · exact B321055
  · exact B321059
  · exact B321063
  · exact B321067
  · exact B321071
  · exact B321075
  · exact B321079
  · exact B321083
  · exact B321087
  · exact B321091
  · exact B321095
  · exact B321099
  · exact B321103
  · exact B321107
  · exact B321111
  · exact B321115
  · exact B321119
  · exact B321123
  · exact B321127
  · exact B321131
  · exact B321135
  · exact B321139
  · exact B321143
  · exact B321147
  · exact B321151
  · exact B321155
  · exact B321159
  · exact B321163
  · exact B321167
  · exact B321171
  · exact B321175
  · exact B321179
  · exact B321183
  · exact B321187
  · exact B321191
  · exact B321195
  · exact B321199
  · exact B321203
  · exact B321207
  · exact B321211
  · exact B321215
  · exact B321219
  · exact B321223
  · exact B321227
  · exact B321231
  · exact B321235
  · exact B321239
  · exact B321243
  · exact B321247
  · exact B321251
  · exact B321255
  · exact B321259
  · exact B321263
  · exact B321267
  · exact B321271
  · exact B321275
  · exact B321279
  · exact B321283
  · exact B321287
  · exact B321291
  · exact B321295
  · exact B321299
  · exact B321303
  · exact B321307
  · exact B321311
  · exact B321315
  · exact B321319
  · exact B321323
  · exact B321327
  · exact B321331
  · exact B321335
  · exact B321339
  · exact B321343
  · exact B321347
  · exact B321351
  · exact B321355
  · exact B321359
  · exact B321363
  · exact B321367
  · exact B321371
  · exact B321375
  · exact B321379
  · exact B321383
  · exact B321387
  · exact B321391
  · exact B321395
  · exact B321399
  · exact B321403
  · exact B321407
  · exact B321411
  · exact B321415
  · exact B321419
  · exact B321423
  · exact B321427
  · exact B321431
  · exact B321435
  · exact B321439
  · exact B321443
  · exact B321447
  · exact B321451
  · exact B321455
  · exact B321459
  · exact B321463
  · exact B321467
  · exact B321471
  · exact B321475
  · exact B321479
  · exact B321483
  · exact B321487
  · exact B321491
  · exact B321495
  · exact B321499
  · exact B321503
  · exact B321507
  · exact B321511
  · exact B321515
  · exact B321519
  · exact B321523
  · exact B321527
  · exact B321531
  · exact B321535
  · exact B321539
  · exact B321543
  · exact B321547
  · exact B321551
  · exact B321555
  · exact B321559
  · exact B321563
  · exact B321567
  · exact B321571
  · exact B321575
  · exact B321579
  · exact B321583
  · exact B321587
  · exact B321591
  · exact B321595
  · exact B321599
  · exact B321603
  · exact B321607
  · exact B321611
  · exact B321615
  · exact B321619
  · exact B321623
  · exact B321627
  · exact B321631
  · exact B321635
  · exact B321639
  · exact B321643
  · exact B321647
  · exact B321651
  · exact B321655
  · exact B321659
  · exact B321663
  · exact B321667
  · exact B321671
  · exact B321675
  · exact B321679
  · exact B321683
  · exact B321687
  · exact B321691
  · exact B321695
  · exact B321699
  · exact B321703
  · exact B321707
  · exact B321711
  · exact B321715
  · exact B321719
  · exact B321723
  · exact B321727
  · exact B321731
  · exact B321735
  · exact B321739
  · exact B321743
  · exact B321747
  · exact B321751
  · exact B321755
  · exact B321759
  · exact B321763
  · exact B321767
  · exact B321771
  · exact B321775
  · exact B321779
  · exact B321783
  · exact B321787
  · exact B321791
  · exact B321795
  · exact B321799
  · exact B321803
  · exact B321807
  · exact B321811
  · exact B321815
  · exact B321819
  · exact B321823
  · exact B321827
  · exact B321831
  · exact B321835
  · exact B321839
  · exact B321843
  · exact B321847
  · exact B321851
  · exact B321855
  · exact B321859
  · exact B321863
  · exact B321867
  · exact B321871
  · exact B321875
  · exact B321879
  · exact B321883
  · exact B321887
  · exact B321891
  · exact B321895
  · exact B321899
  · exact B321903
  · exact B321907
  · exact B321911
  · exact B321915
  · exact B321919
  · exact B321923
  · exact B321927
  · exact B321931
  · exact B321935
  · exact B321939
  · exact B321943
  · exact B321947
  · exact B321951
  · exact B321955
  · exact B321959
  · exact B321963
  · exact B321967
  · exact B321971
  · exact B321975
  · exact B321979
  · exact B321983
  · exact B321987
  · exact B321991
  · exact B321995
  · exact B321999
  · exact B322003
  · exact B322007
  · exact B322011
  · exact B322015
  · exact B322019
  · exact B322023
  · exact B322027
  · exact B322031
  · exact B322035
  · exact B322039
  · exact B322043
  · exact B322047
  · exact B322051
  · exact B322055
  · exact B322059
  · exact B322063
  · exact B322067
  · exact B322071
  · exact B322075
  · exact B322079
  · exact B322083
  · exact B322087
  · exact B322091
  · exact B322095
  · exact B322099
  · exact B322103
  · exact B322107
  · exact B322111
  · exact B322115
  · exact B322119
  · exact B322123
  · exact B322127
  · exact B322131
  · exact B322135
  · exact B322139
  · exact B322143
  · exact B322147
  · exact B322151
  · exact B322155
  · exact B322159
  · exact B322163
  · exact B322167
  · exact B322171
  · exact B322175
  · exact B322179
  · exact B322183
  · exact B322187
  · exact B322191
  · exact B322195
  · exact B322199
  · exact B322203
  · exact B322207
  · exact B322211
  · exact B322215
  · exact B322219
  · exact B322223
  · exact B322227
  · exact B322231
  · exact B322235
  · exact B322239
  · exact B322243
  · exact B322247
  · exact B322251
  · exact B322255
  · exact B322259
  · exact B322263
  · exact B322267
  · exact B322271
  · exact B322275
  · exact B322279
  · exact B322283
  · exact B322287
  · exact B322291
  · exact B322295
  · exact B322299
  · exact B322303
  · exact B322307
  · exact B322311
  · exact B322315
  · exact B322319
  · exact B322323
  · exact B322327
  · exact B322331
  · exact B322335
  · exact B322339
  · exact B322343
  · exact B322347
  · exact B322351
  · exact B322355
  · exact B322359
  · exact B322363
  · exact B322367
  · exact B322371
  · exact B322375
  · exact B322379
  · exact B322383
  · exact B322387
  · exact B322391
  · exact B322395
  · exact B322399
  · exact B322403
  · exact B322407
  · exact B322411
  · exact B322415
  · exact B322419
  · exact B322423
  · exact B322427
  · exact B322431
  · exact B322435
  · exact B322439
  · exact B322443
  · exact B322447
  · exact B322451
  · exact B322455
  · exact B322459
  · exact B322463
  · exact B322467
  · exact B322471
  · exact B322475
  · exact B322479
  · exact B322483
  · exact B322487
  · exact B322491
  · exact B322495
  · exact B322499
  · exact B322503
  · exact B322507
  · exact B322511
  · exact B322515
  · exact B322519
  · exact B322523
  · exact B322527
  · exact B322531
  · exact B322535
  · exact B322539
  · exact B322543
  · exact B322547
  · exact B322551
  · exact B322555
  · exact B322559
  · exact B322563
  · exact B322567
  · exact B322571
  · exact B322575
  · exact B322579
  · exact B322583
  · exact B322587
  · exact B322591
  · exact B322595
  · exact B322599
  · exact B322603
  · exact B322607
  · exact B322611
  · exact B322615
  · exact B322619
  · exact B322623
  · exact B322627
  · exact B322631
  · exact B322635

theorem C1 (j : ℕ) (h1 : 80659 ≤ j) (h2 : j ≤ 80958) : Blo 319836 (4 * j + 3) := by
  interval_cases j
  · exact B322639
  · exact B322643
  · exact B322647
  · exact B322651
  · exact B322655
  · exact B322659
  · exact B322663
  · exact B322667
  · exact B322671
  · exact B322675
  · exact B322679
  · exact B322683
  · exact B322687
  · exact B322691
  · exact B322695
  · exact B322699
  · exact B322703
  · exact B322707
  · exact B322711
  · exact B322715
  · exact B322719
  · exact B322723
  · exact B322727
  · exact B322731
  · exact B322735
  · exact B322739
  · exact B322743
  · exact B322747
  · exact B322751
  · exact B322755
  · exact B322759
  · exact B322763
  · exact B322767
  · exact B322771
  · exact B322775
  · exact B322779
  · exact B322783
  · exact B322787
  · exact B322791
  · exact B322795
  · exact B322799
  · exact B322803
  · exact B322807
  · exact B322811
  · exact B322815
  · exact B322819
  · exact B322823
  · exact B322827
  · exact B322831
  · exact B322835
  · exact B322839
  · exact B322843
  · exact B322847
  · exact B322851
  · exact B322855
  · exact B322859
  · exact B322863
  · exact B322867
  · exact B322871
  · exact B322875
  · exact B322879
  · exact B322883
  · exact B322887
  · exact B322891
  · exact B322895
  · exact B322899
  · exact B322903
  · exact B322907
  · exact B322911
  · exact B322915
  · exact B322919
  · exact B322923
  · exact B322927
  · exact B322931
  · exact B322935
  · exact B322939
  · exact B322943
  · exact B322947
  · exact B322951
  · exact B322955
  · exact B322959
  · exact B322963
  · exact B322967
  · exact B322971
  · exact B322975
  · exact B322979
  · exact B322983
  · exact B322987
  · exact B322991
  · exact B322995
  · exact B322999
  · exact B323003
  · exact B323007
  · exact B323011
  · exact B323015
  · exact B323019
  · exact B323023
  · exact B323027
  · exact B323031
  · exact B323035
  · exact B323039
  · exact B323043
  · exact B323047
  · exact B323051
  · exact B323055
  · exact B323059
  · exact B323063
  · exact B323067
  · exact B323071
  · exact B323075
  · exact B323079
  · exact B323083
  · exact B323087
  · exact B323091
  · exact B323095
  · exact B323099
  · exact B323103
  · exact B323107
  · exact B323111
  · exact B323115
  · exact B323119
  · exact B323123
  · exact B323127
  · exact B323131
  · exact B323135
  · exact B323139
  · exact B323143
  · exact B323147
  · exact B323151
  · exact B323155
  · exact B323159
  · exact B323163
  · exact B323167
  · exact B323171
  · exact B323175
  · exact B323179
  · exact B323183
  · exact B323187
  · exact B323191
  · exact B323195
  · exact B323199
  · exact B323203
  · exact B323207
  · exact B323211
  · exact B323215
  · exact B323219
  · exact B323223
  · exact B323227
  · exact B323231
  · exact B323235
  · exact B323239
  · exact B323243
  · exact B323247
  · exact B323251
  · exact B323255
  · exact B323259
  · exact B323263
  · exact B323267
  · exact B323271
  · exact B323275
  · exact B323279
  · exact B323283
  · exact B323287
  · exact B323291
  · exact B323295
  · exact B323299
  · exact B323303
  · exact B323307
  · exact B323311
  · exact B323315
  · exact B323319
  · exact B323323
  · exact B323327
  · exact B323331
  · exact B323335
  · exact B323339
  · exact B323343
  · exact B323347
  · exact B323351
  · exact B323355
  · exact B323359
  · exact B323363
  · exact B323367
  · exact B323371
  · exact B323375
  · exact B323379
  · exact B323383
  · exact B323387
  · exact B323391
  · exact B323395
  · exact B323399
  · exact B323403
  · exact B323407
  · exact B323411
  · exact B323415
  · exact B323419
  · exact B323423
  · exact B323427
  · exact B323431
  · exact B323435
  · exact B323439
  · exact B323443
  · exact B323447
  · exact B323451
  · exact B323455
  · exact B323459
  · exact B323463
  · exact B323467
  · exact B323471
  · exact B323475
  · exact B323479
  · exact B323483
  · exact B323487
  · exact B323491
  · exact B323495
  · exact B323499
  · exact B323503
  · exact B323507
  · exact B323511
  · exact B323515
  · exact B323519
  · exact B323523
  · exact B323527
  · exact B323531
  · exact B323535
  · exact B323539
  · exact B323543
  · exact B323547
  · exact B323551
  · exact B323555
  · exact B323559
  · exact B323563
  · exact B323567
  · exact B323571
  · exact B323575
  · exact B323579
  · exact B323583
  · exact B323587
  · exact B323591
  · exact B323595
  · exact B323599
  · exact B323603
  · exact B323607
  · exact B323611
  · exact B323615
  · exact B323619
  · exact B323623
  · exact B323627
  · exact B323631
  · exact B323635
  · exact B323639
  · exact B323643
  · exact B323647
  · exact B323651
  · exact B323655
  · exact B323659
  · exact B323663
  · exact B323667
  · exact B323671
  · exact B323675
  · exact B323679
  · exact B323683
  · exact B323687
  · exact B323691
  · exact B323695
  · exact B323699
  · exact B323703
  · exact B323707
  · exact B323711
  · exact B323715
  · exact B323719
  · exact B323723
  · exact B323727
  · exact B323731
  · exact B323735
  · exact B323739
  · exact B323743
  · exact B323747
  · exact B323751
  · exact B323755
  · exact B323759
  · exact B323763
  · exact B323767
  · exact B323771
  · exact B323775
  · exact B323779
  · exact B323783
  · exact B323787
  · exact B323791
  · exact B323795
  · exact B323799
  · exact B323803
  · exact B323807
  · exact B323811
  · exact B323815
  · exact B323819
  · exact B323823
  · exact B323827
  · exact B323831
  · exact B323835

theorem solution (m : ℕ) (hlo : 319836 ≤ m) (hhi : m ≤ 323836) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 79959 ≤ j := by omega
    have hj2 : j ≤ 80958 := by omega
    have hb : Blo 319836 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 80659 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
