-- Prove2me | solution 1 for syracuse_descends_range_479788_483788
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:06.266396+00:00
-- url     : https://prove2.me/submissions/e47a9fd8-9d4f-45ed-a64a-9df4b67720dd

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


theorem B1081349 : Blo 479788 1081349 := bbase (se 4 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 1081349 = 202753) (by norm_num)
theorem B1376261 : Blo 479788 1376261 := bbase (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) (by norm_num)
theorem B720917 : Blo 479788 720917 := bbase (se 6 (by rfl) ⟨16896, by rfl⟩ : syracuseStep 720917 = 33793) (by norm_num)
theorem B1835045 : Blo 479788 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B720941 : Blo 479788 720941 := bbase (se 3 (by rfl) ⟨135176, by rfl⟩ : syracuseStep 720941 = 270353) (by norm_num)
theorem B720965 : Blo 479788 720965 := bbase (se 4 (by rfl) ⟨67590, by rfl⟩ : syracuseStep 720965 = 135181) (by norm_num)
theorem B1081421 : Blo 479788 1081421 := bbase (se 3 (by rfl) ⟨202766, by rfl⟩ : syracuseStep 1081421 = 405533) (by norm_num)
theorem B720989 : Blo 479788 720989 := bbase (se 3 (by rfl) ⟨135185, by rfl⟩ : syracuseStep 720989 = 270371) (by norm_num)
theorem B721013 : Blo 479788 721013 := bbase (se 5 (by rfl) ⟨33797, by rfl⟩ : syracuseStep 721013 = 67595) (by norm_num)
theorem B721037 : Blo 479788 721037 := bbase (se 3 (by rfl) ⟨135194, by rfl⟩ : syracuseStep 721037 = 270389) (by norm_num)
theorem B1081493 : Blo 479788 1081493 := bbase (se 6 (by rfl) ⟨25347, by rfl⟩ : syracuseStep 1081493 = 50695) (by norm_num)
theorem B721061 : Blo 479788 721061 := bbase (se 4 (by rfl) ⟨67599, by rfl⟩ : syracuseStep 721061 = 135199) (by norm_num)
theorem B721085 : Blo 479788 721085 := bbase (se 3 (by rfl) ⟨135203, by rfl⟩ : syracuseStep 721085 = 270407) (by norm_num)
theorem B721109 : Blo 479788 721109 := bbase (se 7 (by rfl) ⟨8450, by rfl⟩ : syracuseStep 721109 = 16901) (by norm_num)
theorem B1081565 : Blo 479788 1081565 := bbase (se 3 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 1081565 = 405587) (by norm_num)
theorem B721133 : Blo 479788 721133 := bbase (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) (by norm_num)
theorem B721157 : Blo 479788 721157 := bbase (se 4 (by rfl) ⟨67608, by rfl⟩ : syracuseStep 721157 = 135217) (by norm_num)
theorem B721181 : Blo 479788 721181 := bbase (se 3 (by rfl) ⟨135221, by rfl⟩ : syracuseStep 721181 = 270443) (by norm_num)
theorem B1081637 : Blo 479788 1081637 := bbase (se 4 (by rfl) ⟨101403, by rfl⟩ : syracuseStep 1081637 = 202807) (by norm_num)
theorem B721205 : Blo 479788 721205 := bbase (se 5 (by rfl) ⟨33806, by rfl⟩ : syracuseStep 721205 = 67613) (by norm_num)
theorem B721229 : Blo 479788 721229 := bbase (se 3 (by rfl) ⟨135230, by rfl⟩ : syracuseStep 721229 = 270461) (by norm_num)
theorem B721253 : Blo 479788 721253 := bbase (se 4 (by rfl) ⟨67617, by rfl⟩ : syracuseStep 721253 = 135235) (by norm_num)
theorem B1081709 : Blo 479788 1081709 := bbase (se 3 (by rfl) ⟨202820, by rfl⟩ : syracuseStep 1081709 = 405641) (by norm_num)
theorem B721277 : Blo 479788 721277 := bbase (se 3 (by rfl) ⟨135239, by rfl⟩ : syracuseStep 721277 = 270479) (by norm_num)
theorem B721301 : Blo 479788 721301 := bbase (se 6 (by rfl) ⟨16905, by rfl⟩ : syracuseStep 721301 = 33811) (by norm_num)
theorem B721325 : Blo 479788 721325 := bbase (se 3 (by rfl) ⟨135248, by rfl⟩ : syracuseStep 721325 = 270497) (by norm_num)
theorem B1081781 : Blo 479788 1081781 := bbase (se 5 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 1081781 = 101417) (by norm_num)
theorem B721349 : Blo 479788 721349 := bbase (se 4 (by rfl) ⟨67626, by rfl⟩ : syracuseStep 721349 = 135253) (by norm_num)
theorem B721373 : Blo 479788 721373 := bbase (se 3 (by rfl) ⟨135257, by rfl⟩ : syracuseStep 721373 = 270515) (by norm_num)
theorem B721397 : Blo 479788 721397 := bbase (se 5 (by rfl) ⟨33815, by rfl⟩ : syracuseStep 721397 = 67631) (by norm_num)
theorem B1081853 : Blo 479788 1081853 := bbase (se 3 (by rfl) ⟨202847, by rfl⟩ : syracuseStep 1081853 = 405695) (by norm_num)
theorem B721421 : Blo 479788 721421 := bbase (se 3 (by rfl) ⟨135266, by rfl⟩ : syracuseStep 721421 = 270533) (by norm_num)
theorem B721445 : Blo 479788 721445 := bbase (se 4 (by rfl) ⟨67635, by rfl⟩ : syracuseStep 721445 = 135271) (by norm_num)
theorem B721469 : Blo 479788 721469 := bbase (se 3 (by rfl) ⟨135275, by rfl⟩ : syracuseStep 721469 = 270551) (by norm_num)
theorem B1081925 : Blo 479788 1081925 := bbase (se 4 (by rfl) ⟨101430, by rfl⟩ : syracuseStep 1081925 = 202861) (by norm_num)
theorem B721493 : Blo 479788 721493 := bbase (se 8 (by rfl) ⟨4227, by rfl⟩ : syracuseStep 721493 = 8455) (by norm_num)
theorem B721517 : Blo 479788 721517 := bbase (se 3 (by rfl) ⟨135284, by rfl⟩ : syracuseStep 721517 = 270569) (by norm_num)
theorem B721541 : Blo 479788 721541 := bbase (se 4 (by rfl) ⟨67644, by rfl⟩ : syracuseStep 721541 = 135289) (by norm_num)
theorem B1081997 : Blo 479788 1081997 := bbase (se 3 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 1081997 = 405749) (by norm_num)
theorem B721565 : Blo 479788 721565 := bbase (se 3 (by rfl) ⟨135293, by rfl⟩ : syracuseStep 721565 = 270587) (by norm_num)
theorem B721589 : Blo 479788 721589 := bbase (se 5 (by rfl) ⟨33824, by rfl⟩ : syracuseStep 721589 = 67649) (by norm_num)
theorem B721613 : Blo 479788 721613 := bbase (se 3 (by rfl) ⟨135302, by rfl⟩ : syracuseStep 721613 = 270605) (by norm_num)
theorem B1082069 : Blo 479788 1082069 := bbase (se 7 (by rfl) ⟨12680, by rfl⟩ : syracuseStep 1082069 = 25361) (by norm_num)
theorem B918229 : Blo 479788 918229 := bbase (se 7 (by rfl) ⟨10760, by rfl⟩ : syracuseStep 918229 = 21521) (by norm_num)
theorem B721637 : Blo 479788 721637 := bbase (se 4 (by rfl) ⟨67653, by rfl⟩ : syracuseStep 721637 = 135307) (by norm_num)
theorem B1377013 : Blo 479788 1377013 := bbase (se 5 (by rfl) ⟨64547, by rfl⟩ : syracuseStep 1377013 = 129095) (by norm_num)
theorem B721661 : Blo 479788 721661 := bbase (se 3 (by rfl) ⟨135311, by rfl⟩ : syracuseStep 721661 = 270623) (by norm_num)
theorem B721685 : Blo 479788 721685 := bbase (se 6 (by rfl) ⟨16914, by rfl⟩ : syracuseStep 721685 = 33829) (by norm_num)
theorem B1082141 : Blo 479788 1082141 := bbase (se 3 (by rfl) ⟨202901, by rfl⟩ : syracuseStep 1082141 = 405803) (by norm_num)
theorem B721709 : Blo 479788 721709 := bbase (se 3 (by rfl) ⟨135320, by rfl⟩ : syracuseStep 721709 = 270641) (by norm_num)
theorem B721733 : Blo 479788 721733 := bbase (se 4 (by rfl) ⟨67662, by rfl⟩ : syracuseStep 721733 = 135325) (by norm_num)
theorem B721757 : Blo 479788 721757 := bbase (se 3 (by rfl) ⟨135329, by rfl⟩ : syracuseStep 721757 = 270659) (by norm_num)
theorem B1082213 : Blo 479788 1082213 := bbase (se 4 (by rfl) ⟨101457, by rfl⟩ : syracuseStep 1082213 = 202915) (by norm_num)
theorem B918373 : Blo 479788 918373 := bbase (se 4 (by rfl) ⟨86097, by rfl⟩ : syracuseStep 918373 = 172195) (by norm_num)
theorem B721781 : Blo 479788 721781 := bbase (se 5 (by rfl) ⟨33833, by rfl⟩ : syracuseStep 721781 = 67667) (by norm_num)
theorem B721805 : Blo 479788 721805 := bbase (se 3 (by rfl) ⟨135338, by rfl⟩ : syracuseStep 721805 = 270677) (by norm_num)
theorem B721829 : Blo 479788 721829 := bbase (se 4 (by rfl) ⟨67671, by rfl⟩ : syracuseStep 721829 = 135343) (by norm_num)
theorem B1082285 : Blo 479788 1082285 := bbase (se 3 (by rfl) ⟨202928, by rfl⟩ : syracuseStep 1082285 = 405857) (by norm_num)
theorem B721853 : Blo 479788 721853 := bbase (se 3 (by rfl) ⟨135347, by rfl⟩ : syracuseStep 721853 = 270695) (by norm_num)
theorem B721877 : Blo 479788 721877 := bbase (se 7 (by rfl) ⟨8459, by rfl⟩ : syracuseStep 721877 = 16919) (by norm_num)
theorem B721901 : Blo 479788 721901 := bbase (se 3 (by rfl) ⟨135356, by rfl⟩ : syracuseStep 721901 = 270713) (by norm_num)
theorem B1082357 : Blo 479788 1082357 := bbase (se 5 (by rfl) ⟨50735, by rfl⟩ : syracuseStep 1082357 = 101471) (by norm_num)
theorem B721925 : Blo 479788 721925 := bbase (se 4 (by rfl) ⟨67680, by rfl⟩ : syracuseStep 721925 = 135361) (by norm_num)
theorem B721949 : Blo 479788 721949 := bbase (se 3 (by rfl) ⟨135365, by rfl⟩ : syracuseStep 721949 = 270731) (by norm_num)
theorem B721973 : Blo 479788 721973 := bbase (se 5 (by rfl) ⟨33842, by rfl⟩ : syracuseStep 721973 = 67685) (by norm_num)
theorem B1082429 : Blo 479788 1082429 := bbase (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) (by norm_num)
theorem B721997 : Blo 479788 721997 := bbase (se 3 (by rfl) ⟨135374, by rfl⟩ : syracuseStep 721997 = 270749) (by norm_num)
theorem B722021 : Blo 479788 722021 := bbase (se 4 (by rfl) ⟨67689, by rfl⟩ : syracuseStep 722021 = 135379) (by norm_num)
theorem B722045 : Blo 479788 722045 := bbase (se 3 (by rfl) ⟨135383, by rfl⟩ : syracuseStep 722045 = 270767) (by norm_num)
theorem B1082501 : Blo 479788 1082501 := bbase (se 4 (by rfl) ⟨101484, by rfl⟩ : syracuseStep 1082501 = 202969) (by norm_num)
theorem B722069 : Blo 479788 722069 := bbase (se 6 (by rfl) ⟨16923, by rfl⟩ : syracuseStep 722069 = 33847) (by norm_num)
theorem B722093 : Blo 479788 722093 := bbase (se 3 (by rfl) ⟨135392, by rfl⟩ : syracuseStep 722093 = 270785) (by norm_num)
theorem B722117 : Blo 479788 722117 := bbase (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) (by norm_num)
theorem B1836229 : Blo 479788 1836229 := bbase (se 4 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 1836229 = 344293) (by norm_num)
theorem B1082573 : Blo 479788 1082573 := bbase (se 3 (by rfl) ⟨202982, by rfl⟩ : syracuseStep 1082573 = 405965) (by norm_num)
theorem B722141 : Blo 479788 722141 := bbase (se 3 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 722141 = 270803) (by norm_num)
theorem B722165 : Blo 479788 722165 := bbase (se 5 (by rfl) ⟨33851, by rfl⟩ : syracuseStep 722165 = 67703) (by norm_num)
theorem B722189 : Blo 479788 722189 := bbase (se 3 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 722189 = 270821) (by norm_num)
theorem B1082645 : Blo 479788 1082645 := bbase (se 6 (by rfl) ⟨25374, by rfl⟩ : syracuseStep 1082645 = 50749) (by norm_num)
theorem B722213 : Blo 479788 722213 := bbase (se 4 (by rfl) ⟨67707, by rfl⟩ : syracuseStep 722213 = 135415) (by norm_num)
theorem B722237 : Blo 479788 722237 := bbase (se 3 (by rfl) ⟨135419, by rfl⟩ : syracuseStep 722237 = 270839) (by norm_num)
theorem B722261 : Blo 479788 722261 := bbase (se 12 (by rfl) ⟨264, by rfl⟩ : syracuseStep 722261 = 529) (by norm_num)
theorem B1082717 : Blo 479788 1082717 := bbase (se 3 (by rfl) ⟨203009, by rfl⟩ : syracuseStep 1082717 = 406019) (by norm_num)
theorem B722285 : Blo 479788 722285 := bbase (se 3 (by rfl) ⟨135428, by rfl⟩ : syracuseStep 722285 = 270857) (by norm_num)
theorem B722309 : Blo 479788 722309 := bbase (se 4 (by rfl) ⟨67716, by rfl⟩ : syracuseStep 722309 = 135433) (by norm_num)
theorem B722333 : Blo 479788 722333 := bbase (se 3 (by rfl) ⟨135437, by rfl⟩ : syracuseStep 722333 = 270875) (by norm_num)
theorem B1082789 : Blo 479788 1082789 := bbase (se 4 (by rfl) ⟨101511, by rfl⟩ : syracuseStep 1082789 = 203023) (by norm_num)
theorem B722357 : Blo 479788 722357 := bbase (se 5 (by rfl) ⟨33860, by rfl⟩ : syracuseStep 722357 = 67721) (by norm_num)
theorem B722381 : Blo 479788 722381 := bbase (se 3 (by rfl) ⟨135446, by rfl⟩ : syracuseStep 722381 = 270893) (by norm_num)
theorem B722405 : Blo 479788 722405 := bbase (se 4 (by rfl) ⟨67725, by rfl⟩ : syracuseStep 722405 = 135451) (by norm_num)
theorem B624109 : Blo 479788 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B1082861 : Blo 479788 1082861 := bbase (se 3 (by rfl) ⟨203036, by rfl⟩ : syracuseStep 1082861 = 406073) (by norm_num)
theorem B1836533 : Blo 479788 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B722429 : Blo 479788 722429 := bbase (se 3 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 722429 = 270911) (by norm_num)
theorem B722453 : Blo 479788 722453 := bbase (se 6 (by rfl) ⟨16932, by rfl⟩ : syracuseStep 722453 = 33865) (by norm_num)
theorem B722477 : Blo 479788 722477 := bbase (se 3 (by rfl) ⟨135464, by rfl⟩ : syracuseStep 722477 = 270929) (by norm_num)
theorem B1082933 : Blo 479788 1082933 := bbase (se 5 (by rfl) ⟨50762, by rfl⟩ : syracuseStep 1082933 = 101525) (by norm_num)
theorem B722501 : Blo 479788 722501 := bbase (se 4 (by rfl) ⟨67734, by rfl⟩ : syracuseStep 722501 = 135469) (by norm_num)
theorem B722525 : Blo 479788 722525 := bbase (se 3 (by rfl) ⟨135473, by rfl⟩ : syracuseStep 722525 = 270947) (by norm_num)
theorem B722549 : Blo 479788 722549 := bbase (se 5 (by rfl) ⟨33869, by rfl⟩ : syracuseStep 722549 = 67739) (by norm_num)
theorem B1083005 : Blo 479788 1083005 := bbase (se 3 (by rfl) ⟨203063, by rfl⟩ : syracuseStep 1083005 = 406127) (by norm_num)
theorem B722573 : Blo 479788 722573 := bbase (se 3 (by rfl) ⟨135482, by rfl⟩ : syracuseStep 722573 = 270965) (by norm_num)
theorem B722597 : Blo 479788 722597 := bbase (se 4 (by rfl) ⟨67743, by rfl⟩ : syracuseStep 722597 = 135487) (by norm_num)
theorem B722621 : Blo 479788 722621 := bbase (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) (by norm_num)
theorem B1083077 : Blo 479788 1083077 := bbase (se 4 (by rfl) ⟨101538, by rfl⟩ : syracuseStep 1083077 = 203077) (by norm_num)
theorem B722645 : Blo 479788 722645 := bbase (se 7 (by rfl) ⟨8468, by rfl⟩ : syracuseStep 722645 = 16937) (by norm_num)
theorem B722669 : Blo 479788 722669 := bbase (se 3 (by rfl) ⟨135500, by rfl⟩ : syracuseStep 722669 = 271001) (by norm_num)
theorem B722693 : Blo 479788 722693 := bbase (se 4 (by rfl) ⟨67752, by rfl⟩ : syracuseStep 722693 = 135505) (by norm_num)
theorem B1083149 : Blo 479788 1083149 := bbase (se 3 (by rfl) ⟨203090, by rfl⟩ : syracuseStep 1083149 = 406181) (by norm_num)
theorem B722717 : Blo 479788 722717 := bbase (se 3 (by rfl) ⟨135509, by rfl⟩ : syracuseStep 722717 = 271019) (by norm_num)
theorem B722741 : Blo 479788 722741 := bbase (se 5 (by rfl) ⟨33878, by rfl⟩ : syracuseStep 722741 = 67757) (by norm_num)
theorem B722765 : Blo 479788 722765 := bbase (se 3 (by rfl) ⟨135518, by rfl⟩ : syracuseStep 722765 = 271037) (by norm_num)
theorem B1083221 : Blo 479788 1083221 := bbase (se 9 (by rfl) ⟨3173, by rfl⟩ : syracuseStep 1083221 = 6347) (by norm_num)
theorem B722789 : Blo 479788 722789 := bbase (se 4 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 722789 = 135523) (by norm_num)
theorem B722813 : Blo 479788 722813 := bbase (se 3 (by rfl) ⟨135527, by rfl⟩ : syracuseStep 722813 = 271055) (by norm_num)
theorem B722837 : Blo 479788 722837 := bbase (se 6 (by rfl) ⟨16941, by rfl⟩ : syracuseStep 722837 = 33883) (by norm_num)
theorem B1083293 : Blo 479788 1083293 := bbase (se 3 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 1083293 = 406235) (by norm_num)
theorem B722861 : Blo 479788 722861 := bbase (se 3 (by rfl) ⟨135536, by rfl⟩ : syracuseStep 722861 = 271073) (by norm_num)
theorem B722885 : Blo 479788 722885 := bbase (se 4 (by rfl) ⟨67770, by rfl⟩ : syracuseStep 722885 = 135541) (by norm_num)
theorem B722909 : Blo 479788 722909 := bbase (se 3 (by rfl) ⟨135545, by rfl⟩ : syracuseStep 722909 = 271091) (by norm_num)
theorem B1083365 : Blo 479788 1083365 := bbase (se 4 (by rfl) ⟨101565, by rfl⟩ : syracuseStep 1083365 = 203131) (by norm_num)
theorem B722933 : Blo 479788 722933 := bbase (se 5 (by rfl) ⟨33887, by rfl⟩ : syracuseStep 722933 = 67775) (by norm_num)
theorem B722957 : Blo 479788 722957 := bbase (se 3 (by rfl) ⟨135554, by rfl⟩ : syracuseStep 722957 = 271109) (by norm_num)
theorem B722981 : Blo 479788 722981 := bbase (se 4 (by rfl) ⟨67779, by rfl⟩ : syracuseStep 722981 = 135559) (by norm_num)
theorem B1083437 : Blo 479788 1083437 := bbase (se 3 (by rfl) ⟨203144, by rfl⟩ : syracuseStep 1083437 = 406289) (by norm_num)
theorem B723005 : Blo 479788 723005 := bbase (se 3 (by rfl) ⟨135563, by rfl⟩ : syracuseStep 723005 = 271127) (by norm_num)
theorem B723029 : Blo 479788 723029 := bbase (se 8 (by rfl) ⟨4236, by rfl⟩ : syracuseStep 723029 = 8473) (by norm_num)
theorem B1542245 : Blo 479788 1542245 := bbase (se 4 (by rfl) ⟨144585, by rfl⟩ : syracuseStep 1542245 = 289171) (by norm_num)
theorem B723053 : Blo 479788 723053 := bbase (se 3 (by rfl) ⟨135572, by rfl⟩ : syracuseStep 723053 = 271145) (by norm_num)
theorem B1083509 : Blo 479788 1083509 := bbase (se 5 (by rfl) ⟨50789, by rfl⟩ : syracuseStep 1083509 = 101579) (by norm_num)
theorem B493697 : Blo 479788 493697 := bbase (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) (by norm_num)
theorem B723077 : Blo 479788 723077 := bbase (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) (by norm_num)
theorem B723101 : Blo 479788 723101 := bbase (se 3 (by rfl) ⟨135581, by rfl⟩ : syracuseStep 723101 = 271163) (by norm_num)
theorem B723125 : Blo 479788 723125 := bbase (se 5 (by rfl) ⟨33896, by rfl⟩ : syracuseStep 723125 = 67793) (by norm_num)
theorem B1083581 : Blo 479788 1083581 := bbase (se 3 (by rfl) ⟨203171, by rfl⟩ : syracuseStep 1083581 = 406343) (by norm_num)
theorem B723149 : Blo 479788 723149 := bbase (se 3 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 723149 = 271181) (by norm_num)
theorem B723173 : Blo 479788 723173 := bbase (se 4 (by rfl) ⟨67797, by rfl⟩ : syracuseStep 723173 = 135595) (by norm_num)
theorem B723197 : Blo 479788 723197 := bbase (se 3 (by rfl) ⟨135599, by rfl⟩ : syracuseStep 723197 = 271199) (by norm_num)
theorem B1083653 : Blo 479788 1083653 := bbase (se 4 (by rfl) ⟨101592, by rfl⟩ : syracuseStep 1083653 = 203185) (by norm_num)
theorem B723221 : Blo 479788 723221 := bbase (se 6 (by rfl) ⟨16950, by rfl⟩ : syracuseStep 723221 = 33901) (by norm_num)
theorem B723245 : Blo 479788 723245 := bbase (se 3 (by rfl) ⟨135608, by rfl⟩ : syracuseStep 723245 = 271217) (by norm_num)
theorem B723269 : Blo 479788 723269 := bbase (se 4 (by rfl) ⟨67806, by rfl⟩ : syracuseStep 723269 = 135613) (by norm_num)
theorem B1214797 : Blo 479788 1214797 := bbase (se 3 (by rfl) ⟨227774, by rfl⟩ : syracuseStep 1214797 = 455549) (by norm_num)
theorem B1083725 : Blo 479788 1083725 := bbase (se 3 (by rfl) ⟨203198, by rfl⟩ : syracuseStep 1083725 = 406397) (by norm_num)
theorem B723293 : Blo 479788 723293 := bbase (se 3 (by rfl) ⟨135617, by rfl⟩ : syracuseStep 723293 = 271235) (by norm_num)
theorem B723317 : Blo 479788 723317 := bbase (se 5 (by rfl) ⟨33905, by rfl⟩ : syracuseStep 723317 = 67811) (by norm_num)
theorem B723341 : Blo 479788 723341 := bbase (se 3 (by rfl) ⟨135626, by rfl⟩ : syracuseStep 723341 = 271253) (by norm_num)
theorem B1083797 : Blo 479788 1083797 := bbase (se 6 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 1083797 = 50803) (by norm_num)
theorem B723365 : Blo 479788 723365 := bbase (se 4 (by rfl) ⟨67815, by rfl⟩ : syracuseStep 723365 = 135631) (by norm_num)
theorem B1214909 : Blo 479788 1214909 := bbase (se 3 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 1214909 = 455591) (by norm_num)
theorem B723389 : Blo 479788 723389 := bbase (se 3 (by rfl) ⟨135635, by rfl⟩ : syracuseStep 723389 = 271271) (by norm_num)
theorem B723413 : Blo 479788 723413 := bbase (se 7 (by rfl) ⟨8477, by rfl⟩ : syracuseStep 723413 = 16955) (by norm_num)
theorem B1083869 : Blo 479788 1083869 := bbase (se 3 (by rfl) ⟨203225, by rfl⟩ : syracuseStep 1083869 = 406451) (by norm_num)
theorem B723437 : Blo 479788 723437 := bbase (se 3 (by rfl) ⟨135644, by rfl⟩ : syracuseStep 723437 = 271289) (by norm_num)
theorem B723461 : Blo 479788 723461 := bbase (se 4 (by rfl) ⟨67824, by rfl⟩ : syracuseStep 723461 = 135649) (by norm_num)
theorem B723485 : Blo 479788 723485 := bbase (se 3 (by rfl) ⟨135653, by rfl⟩ : syracuseStep 723485 = 271307) (by norm_num)
theorem B1083941 : Blo 479788 1083941 := bbase (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) (by norm_num)
theorem B723509 : Blo 479788 723509 := bbase (se 5 (by rfl) ⟨33914, by rfl⟩ : syracuseStep 723509 = 67829) (by norm_num)
theorem B723533 : Blo 479788 723533 := bbase (se 3 (by rfl) ⟨135662, by rfl⟩ : syracuseStep 723533 = 271325) (by norm_num)
theorem B723557 : Blo 479788 723557 := bbase (se 4 (by rfl) ⟨67833, by rfl⟩ : syracuseStep 723557 = 135667) (by norm_num)
theorem B1084013 : Blo 479788 1084013 := bbase (se 3 (by rfl) ⟨203252, by rfl⟩ : syracuseStep 1084013 = 406505) (by norm_num)
theorem B1215101 : Blo 479788 1215101 := bbase (se 3 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 1215101 = 455663) (by norm_num)
theorem B723581 : Blo 479788 723581 := bbase (se 3 (by rfl) ⟨135671, by rfl⟩ : syracuseStep 723581 = 271343) (by norm_num)
theorem B723605 : Blo 479788 723605 := bbase (se 6 (by rfl) ⟨16959, by rfl⟩ : syracuseStep 723605 = 33919) (by norm_num)
theorem B723629 : Blo 479788 723629 := bbase (se 3 (by rfl) ⟨135680, by rfl⟩ : syracuseStep 723629 = 271361) (by norm_num)
theorem B1084085 : Blo 479788 1084085 := bbase (se 5 (by rfl) ⟨50816, by rfl⟩ : syracuseStep 1084085 = 101633) (by norm_num)
theorem B723653 : Blo 479788 723653 := bbase (se 4 (by rfl) ⟨67842, by rfl⟩ : syracuseStep 723653 = 135685) (by norm_num)
theorem B625357 : Blo 479788 625357 := bbase (se 3 (by rfl) ⟨117254, by rfl⟩ : syracuseStep 625357 = 234509) (by norm_num)
theorem B723677 : Blo 479788 723677 := bbase (se 3 (by rfl) ⟨135689, by rfl⟩ : syracuseStep 723677 = 271379) (by norm_num)
theorem B723701 : Blo 479788 723701 := bbase (se 5 (by rfl) ⟨33923, by rfl⟩ : syracuseStep 723701 = 67847) (by norm_num)
theorem B1084157 : Blo 479788 1084157 := bbase (se 3 (by rfl) ⟨203279, by rfl⟩ : syracuseStep 1084157 = 406559) (by norm_num)
theorem B723725 : Blo 479788 723725 := bbase (se 3 (by rfl) ⟨135698, by rfl⟩ : syracuseStep 723725 = 271397) (by norm_num)
theorem B723749 : Blo 479788 723749 := bbase (se 4 (by rfl) ⟨67851, by rfl⟩ : syracuseStep 723749 = 135703) (by norm_num)
theorem B723773 : Blo 479788 723773 := bbase (se 3 (by rfl) ⟨135707, by rfl⟩ : syracuseStep 723773 = 271415) (by norm_num)
theorem B1084229 : Blo 479788 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B723797 : Blo 479788 723797 := bbase (se 9 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 723797 = 4241) (by norm_num)
theorem B723821 : Blo 479788 723821 := bbase (se 3 (by rfl) ⟨135716, by rfl⟩ : syracuseStep 723821 = 271433) (by norm_num)
theorem B723845 : Blo 479788 723845 := bbase (se 4 (by rfl) ⟨67860, by rfl⟩ : syracuseStep 723845 = 135721) (by norm_num)
theorem B1084301 : Blo 479788 1084301 := bbase (se 3 (by rfl) ⟨203306, by rfl⟩ : syracuseStep 1084301 = 406613) (by norm_num)
theorem B723869 : Blo 479788 723869 := bbase (se 3 (by rfl) ⟨135725, by rfl⟩ : syracuseStep 723869 = 271451) (by norm_num)
theorem B723893 : Blo 479788 723893 := bbase (se 5 (by rfl) ⟨33932, by rfl⟩ : syracuseStep 723893 = 67865) (by norm_num)
theorem B723917 : Blo 479788 723917 := bbase (se 3 (by rfl) ⟨135734, by rfl⟩ : syracuseStep 723917 = 271469) (by norm_num)
theorem B1215445 : Blo 479788 1215445 := bbase (se 7 (by rfl) ⟨14243, by rfl⟩ : syracuseStep 1215445 = 28487) (by norm_num)
theorem B1084373 : Blo 479788 1084373 := bbase (se 7 (by rfl) ⟨12707, by rfl⟩ : syracuseStep 1084373 = 25415) (by norm_num)
theorem B723941 : Blo 479788 723941 := bbase (se 4 (by rfl) ⟨67869, by rfl⟩ : syracuseStep 723941 = 135739) (by norm_num)
theorem B1543157 : Blo 479788 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B723965 : Blo 479788 723965 := bbase (se 3 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 723965 = 271487) (by norm_num)
theorem B723989 : Blo 479788 723989 := bbase (se 6 (by rfl) ⟨16968, by rfl⟩ : syracuseStep 723989 = 33937) (by norm_num)
theorem B1084445 : Blo 479788 1084445 := bbase (se 3 (by rfl) ⟨203333, by rfl⟩ : syracuseStep 1084445 = 406667) (by norm_num)
theorem B724013 : Blo 479788 724013 := bbase (se 3 (by rfl) ⟨135752, by rfl⟩ : syracuseStep 724013 = 271505) (by norm_num)
theorem B1215557 : Blo 479788 1215557 := bbase (se 4 (by rfl) ⟨113958, by rfl⟩ : syracuseStep 1215557 = 227917) (by norm_num)
theorem B724037 : Blo 479788 724037 := bbase (se 4 (by rfl) ⟨67878, by rfl⟩ : syracuseStep 724037 = 135757) (by norm_num)
theorem B724061 : Blo 479788 724061 := bbase (se 3 (by rfl) ⟨135761, by rfl⟩ : syracuseStep 724061 = 271523) (by norm_num)
theorem B1084517 : Blo 479788 1084517 := bbase (se 4 (by rfl) ⟨101673, by rfl⟩ : syracuseStep 1084517 = 203347) (by norm_num)
theorem B724085 : Blo 479788 724085 := bbase (se 5 (by rfl) ⟨33941, by rfl⟩ : syracuseStep 724085 = 67883) (by norm_num)
theorem B494717 : Blo 479788 494717 := bbase (se 3 (by rfl) ⟨92759, by rfl⟩ : syracuseStep 494717 = 185519) (by norm_num)
theorem B724109 : Blo 479788 724109 := bbase (se 3 (by rfl) ⟨135770, by rfl⟩ : syracuseStep 724109 = 271541) (by norm_num)
theorem B724133 : Blo 479788 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B1084589 : Blo 479788 1084589 := bbase (se 3 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 1084589 = 406721) (by norm_num)
theorem B724157 : Blo 479788 724157 := bbase (se 3 (by rfl) ⟨135779, by rfl⟩ : syracuseStep 724157 = 271559) (by norm_num)
theorem B724181 : Blo 479788 724181 := bbase (se 7 (by rfl) ⟨8486, by rfl⟩ : syracuseStep 724181 = 16973) (by norm_num)
theorem B724205 : Blo 479788 724205 := bbase (se 3 (by rfl) ⟨135788, by rfl⟩ : syracuseStep 724205 = 271577) (by norm_num)
theorem B1084661 : Blo 479788 1084661 := bbase (se 5 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 1084661 = 101687) (by norm_num)
theorem B1215749 : Blo 479788 1215749 := bbase (se 4 (by rfl) ⟨113976, by rfl⟩ : syracuseStep 1215749 = 227953) (by norm_num)
theorem B724229 : Blo 479788 724229 := bbase (se 4 (by rfl) ⟨67896, by rfl⟩ : syracuseStep 724229 = 135793) (by norm_num)
theorem B724253 : Blo 479788 724253 := bbase (se 3 (by rfl) ⟨135797, by rfl⟩ : syracuseStep 724253 = 271595) (by norm_num)
theorem B724277 : Blo 479788 724277 := bbase (se 5 (by rfl) ⟨33950, by rfl⟩ : syracuseStep 724277 = 67901) (by norm_num)
theorem B1084733 : Blo 479788 1084733 := bbase (se 3 (by rfl) ⟨203387, by rfl⟩ : syracuseStep 1084733 = 406775) (by norm_num)
theorem B724301 : Blo 479788 724301 := bbase (se 3 (by rfl) ⟨135806, by rfl⟩ : syracuseStep 724301 = 271613) (by norm_num)
theorem B724325 : Blo 479788 724325 := bbase (se 4 (by rfl) ⟨67905, by rfl⟩ : syracuseStep 724325 = 135811) (by norm_num)
theorem B724349 : Blo 479788 724349 := bbase (se 3 (by rfl) ⟨135815, by rfl⟩ : syracuseStep 724349 = 271631) (by norm_num)
theorem B1084805 : Blo 479788 1084805 := bbase (se 4 (by rfl) ⟨101700, by rfl⟩ : syracuseStep 1084805 = 203401) (by norm_num)
theorem B724373 : Blo 479788 724373 := bbase (se 6 (by rfl) ⟨16977, by rfl⟩ : syracuseStep 724373 = 33955) (by norm_num)
theorem B724397 : Blo 479788 724397 := bbase (se 3 (by rfl) ⟨135824, by rfl⟩ : syracuseStep 724397 = 271649) (by norm_num)
theorem B724421 : Blo 479788 724421 := bbase (se 4 (by rfl) ⟨67914, by rfl⟩ : syracuseStep 724421 = 135829) (by norm_num)
theorem B1084877 : Blo 479788 1084877 := bbase (se 3 (by rfl) ⟨203414, by rfl⟩ : syracuseStep 1084877 = 406829) (by norm_num)
theorem B724445 : Blo 479788 724445 := bbase (se 3 (by rfl) ⟨135833, by rfl⟩ : syracuseStep 724445 = 271667) (by norm_num)
theorem B724469 : Blo 479788 724469 := bbase (se 5 (by rfl) ⟨33959, by rfl⟩ : syracuseStep 724469 = 67919) (by norm_num)
theorem B724493 : Blo 479788 724493 := bbase (se 3 (by rfl) ⟨135842, by rfl⟩ : syracuseStep 724493 = 271685) (by norm_num)
theorem B1084949 : Blo 479788 1084949 := bbase (se 6 (by rfl) ⟨25428, by rfl⟩ : syracuseStep 1084949 = 50857) (by norm_num)
theorem B724517 : Blo 479788 724517 := bbase (se 4 (by rfl) ⟨67923, by rfl⟩ : syracuseStep 724517 = 135847) (by norm_num)
theorem B724541 : Blo 479788 724541 := bbase (se 3 (by rfl) ⟨135851, by rfl⟩ : syracuseStep 724541 = 271703) (by norm_num)
theorem B724565 : Blo 479788 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B1216093 : Blo 479788 1216093 := bbase (se 3 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 1216093 = 456035) (by norm_num)
theorem B1085021 : Blo 479788 1085021 := bbase (se 3 (by rfl) ⟨203441, by rfl⟩ : syracuseStep 1085021 = 406883) (by norm_num)
theorem B724589 : Blo 479788 724589 := bbase (se 3 (by rfl) ⟨135860, by rfl⟩ : syracuseStep 724589 = 271721) (by norm_num)
theorem B724613 : Blo 479788 724613 := bbase (se 4 (by rfl) ⟨67932, by rfl⟩ : syracuseStep 724613 = 135865) (by norm_num)
theorem B724637 : Blo 479788 724637 := bbase (se 3 (by rfl) ⟨135869, by rfl⟩ : syracuseStep 724637 = 271739) (by norm_num)
theorem B1085093 : Blo 479788 1085093 := bbase (se 4 (by rfl) ⟨101727, by rfl⟩ : syracuseStep 1085093 = 203455) (by norm_num)
theorem B724661 : Blo 479788 724661 := bbase (se 5 (by rfl) ⟨33968, by rfl⟩ : syracuseStep 724661 = 67937) (by norm_num)
theorem B1216205 : Blo 479788 1216205 := bbase (se 3 (by rfl) ⟨228038, by rfl⟩ : syracuseStep 1216205 = 456077) (by norm_num)
theorem B724685 : Blo 479788 724685 := bbase (se 3 (by rfl) ⟨135878, by rfl⟩ : syracuseStep 724685 = 271757) (by norm_num)
theorem B724709 : Blo 479788 724709 := bbase (se 4 (by rfl) ⟨67941, by rfl⟩ : syracuseStep 724709 = 135883) (by norm_num)
theorem B1085165 : Blo 479788 1085165 := bbase (se 3 (by rfl) ⟨203468, by rfl⟩ : syracuseStep 1085165 = 406937) (by norm_num)
theorem B724733 : Blo 479788 724733 := bbase (se 3 (by rfl) ⟨135887, by rfl⟩ : syracuseStep 724733 = 271775) (by norm_num)
theorem B724757 : Blo 479788 724757 := bbase (se 6 (by rfl) ⟨16986, by rfl⟩ : syracuseStep 724757 = 33973) (by norm_num)
theorem B724781 : Blo 479788 724781 := bbase (se 3 (by rfl) ⟨135896, by rfl⟩ : syracuseStep 724781 = 271793) (by norm_num)
theorem B1085237 : Blo 479788 1085237 := bbase (se 5 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 1085237 = 101741) (by norm_num)
theorem B724805 : Blo 479788 724805 := bbase (se 4 (by rfl) ⟨67950, by rfl⟩ : syracuseStep 724805 = 135901) (by norm_num)
theorem B724829 : Blo 479788 724829 := bbase (se 3 (by rfl) ⟨135905, by rfl⟩ : syracuseStep 724829 = 271811) (by norm_num)
theorem B724853 : Blo 479788 724853 := bbase (se 5 (by rfl) ⟨33977, by rfl⟩ : syracuseStep 724853 = 67955) (by norm_num)
theorem B1085309 : Blo 479788 1085309 := bbase (se 3 (by rfl) ⟨203495, by rfl⟩ : syracuseStep 1085309 = 406991) (by norm_num)
theorem B1216397 : Blo 479788 1216397 := bbase (se 3 (by rfl) ⟨228074, by rfl⟩ : syracuseStep 1216397 = 456149) (by norm_num)
theorem B724877 : Blo 479788 724877 := bbase (se 3 (by rfl) ⟨135914, by rfl⟩ : syracuseStep 724877 = 271829) (by norm_num)
theorem B724901 : Blo 479788 724901 := bbase (se 4 (by rfl) ⟨67959, by rfl⟩ : syracuseStep 724901 = 135919) (by norm_num)
theorem B724925 : Blo 479788 724925 := bbase (se 3 (by rfl) ⟨135923, by rfl⟩ : syracuseStep 724925 = 271847) (by norm_num)
theorem B1085381 : Blo 479788 1085381 := bbase (se 4 (by rfl) ⟨101754, by rfl⟩ : syracuseStep 1085381 = 203509) (by norm_num)
theorem B724949 : Blo 479788 724949 := bbase (se 7 (by rfl) ⟨8495, by rfl⟩ : syracuseStep 724949 = 16991) (by norm_num)
theorem B724973 : Blo 479788 724973 := bbase (se 3 (by rfl) ⟨135932, by rfl⟩ : syracuseStep 724973 = 271865) (by norm_num)
theorem B724997 : Blo 479788 724997 := bbase (se 4 (by rfl) ⟨67968, by rfl⟩ : syracuseStep 724997 = 135937) (by norm_num)
theorem B1085453 : Blo 479788 1085453 := bbase (se 3 (by rfl) ⟨203522, by rfl⟩ : syracuseStep 1085453 = 407045) (by norm_num)
theorem B725021 : Blo 479788 725021 := bbase (se 3 (by rfl) ⟨135941, by rfl⟩ : syracuseStep 725021 = 271883) (by norm_num)
theorem B725045 : Blo 479788 725045 := bbase (se 5 (by rfl) ⟨33986, by rfl⟩ : syracuseStep 725045 = 67973) (by norm_num)
theorem B725069 : Blo 479788 725069 := bbase (se 3 (by rfl) ⟨135950, by rfl⟩ : syracuseStep 725069 = 271901) (by norm_num)
theorem B1085525 : Blo 479788 1085525 := bbase (se 8 (by rfl) ⟨6360, by rfl⟩ : syracuseStep 1085525 = 12721) (by norm_num)
theorem B725093 : Blo 479788 725093 := bbase (se 4 (by rfl) ⟨67977, by rfl⟩ : syracuseStep 725093 = 135955) (by norm_num)
theorem B823421 : Blo 479788 823421 := bbase (se 3 (by rfl) ⟨154391, by rfl⟩ : syracuseStep 823421 = 308783) (by norm_num)
theorem B725117 : Blo 479788 725117 := bbase (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) (by norm_num)
theorem B725141 : Blo 479788 725141 := bbase (se 6 (by rfl) ⟨16995, by rfl⟩ : syracuseStep 725141 = 33991) (by norm_num)
theorem B1085597 : Blo 479788 1085597 := bbase (se 3 (by rfl) ⟨203549, by rfl⟩ : syracuseStep 1085597 = 407099) (by norm_num)
theorem B725165 : Blo 479788 725165 := bbase (se 3 (by rfl) ⟨135968, by rfl⟩ : syracuseStep 725165 = 271937) (by norm_num)
theorem B725189 : Blo 479788 725189 := bbase (se 4 (by rfl) ⟨67986, by rfl⟩ : syracuseStep 725189 = 135973) (by norm_num)
theorem B1741013 : Blo 479788 1741013 := bbase (se 7 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 1741013 = 40805) (by norm_num)
theorem B725213 : Blo 479788 725213 := bbase (se 3 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 725213 = 271955) (by norm_num)
theorem B1216741 : Blo 479788 1216741 := bbase (se 4 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 1216741 = 228139) (by norm_num)
theorem B1085669 : Blo 479788 1085669 := bbase (se 4 (by rfl) ⟨101781, by rfl⟩ : syracuseStep 1085669 = 203563) (by norm_num)
theorem B725237 : Blo 479788 725237 := bbase (se 5 (by rfl) ⟨33995, by rfl⟩ : syracuseStep 725237 = 67991) (by norm_num)
theorem B2429189 : Blo 479788 2429189 := bbase (se 4 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 2429189 = 455473) (by norm_num)
theorem B725261 : Blo 479788 725261 := bbase (se 3 (by rfl) ⟨135986, by rfl⟩ : syracuseStep 725261 = 271973) (by norm_num)
theorem B725285 : Blo 479788 725285 := bbase (se 4 (by rfl) ⟨67995, by rfl⟩ : syracuseStep 725285 = 135991) (by norm_num)
theorem B1085741 : Blo 479788 1085741 := bbase (se 3 (by rfl) ⟨203576, by rfl⟩ : syracuseStep 1085741 = 407153) (by norm_num)
theorem B1544501 : Blo 479788 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B725309 : Blo 479788 725309 := bbase (se 3 (by rfl) ⟨135995, by rfl⟩ : syracuseStep 725309 = 271991) (by norm_num)
theorem B1216853 : Blo 479788 1216853 := bbase (se 10 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 1216853 = 3565) (by norm_num)
theorem B725333 : Blo 479788 725333 := bbase (se 10 (by rfl) ⟨1062, by rfl⟩ : syracuseStep 725333 = 2125) (by norm_num)
theorem B725357 : Blo 479788 725357 := bbase (se 3 (by rfl) ⟨136004, by rfl⟩ : syracuseStep 725357 = 272009) (by norm_num)
theorem B1085813 : Blo 479788 1085813 := bbase (se 5 (by rfl) ⟨50897, by rfl⟩ : syracuseStep 1085813 = 101795) (by norm_num)
theorem B725381 : Blo 479788 725381 := bbase (se 4 (by rfl) ⟨68004, by rfl⟩ : syracuseStep 725381 = 136009) (by norm_num)
theorem B725405 : Blo 479788 725405 := bbase (se 3 (by rfl) ⟨136013, by rfl⟩ : syracuseStep 725405 = 272027) (by norm_num)
theorem B725429 : Blo 479788 725429 := bbase (se 5 (by rfl) ⟨34004, by rfl⟩ : syracuseStep 725429 = 68009) (by norm_num)
theorem B1085885 : Blo 479788 1085885 := bbase (se 3 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 1085885 = 407207) (by norm_num)
theorem B725453 : Blo 479788 725453 := bbase (se 3 (by rfl) ⟨136022, by rfl⟩ : syracuseStep 725453 = 272045) (by norm_num)
theorem B725477 : Blo 479788 725477 := bbase (se 4 (by rfl) ⟨68013, by rfl⟩ : syracuseStep 725477 = 136027) (by norm_num)
theorem B725501 : Blo 479788 725501 := bbase (se 3 (by rfl) ⟨136031, by rfl⟩ : syracuseStep 725501 = 272063) (by norm_num)
theorem B1085957 : Blo 479788 1085957 := bbase (se 4 (by rfl) ⟨101808, by rfl⟩ : syracuseStep 1085957 = 203617) (by norm_num)
theorem B1217045 : Blo 479788 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B725525 : Blo 479788 725525 := bbase (se 6 (by rfl) ⟨17004, by rfl⟩ : syracuseStep 725525 = 34009) (by norm_num)
theorem B725549 : Blo 479788 725549 := bbase (se 3 (by rfl) ⟨136040, by rfl⟩ : syracuseStep 725549 = 272081) (by norm_num)
theorem B725573 : Blo 479788 725573 := bbase (se 4 (by rfl) ⟨68022, by rfl⟩ : syracuseStep 725573 = 136045) (by norm_num)
theorem B1086029 : Blo 479788 1086029 := bbase (se 3 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 1086029 = 407261) (by norm_num)
theorem B725597 : Blo 479788 725597 := bbase (se 3 (by rfl) ⟨136049, by rfl⟩ : syracuseStep 725597 = 272099) (by norm_num)
theorem B725621 : Blo 479788 725621 := bbase (se 5 (by rfl) ⟨34013, by rfl⟩ : syracuseStep 725621 = 68027) (by norm_num)
theorem B725645 : Blo 479788 725645 := bbase (se 3 (by rfl) ⟨136058, by rfl⟩ : syracuseStep 725645 = 272117) (by norm_num)
theorem B1086101 : Blo 479788 1086101 := bbase (se 6 (by rfl) ⟨25455, by rfl⟩ : syracuseStep 1086101 = 50911) (by norm_num)
theorem B5509781 : Blo 479788 5509781 := bbase (se 6 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 5509781 = 258271) (by norm_num)
theorem B725669 : Blo 479788 725669 := bbase (se 4 (by rfl) ⟨68031, by rfl⟩ : syracuseStep 725669 = 136063) (by norm_num)
theorem B1086173 : Blo 479788 1086173 := bbase (se 3 (by rfl) ⟨203657, by rfl⟩ : syracuseStep 1086173 = 407315) (by norm_num)
theorem B2462501 : Blo 479788 2462501 := bbase (se 4 (by rfl) ⟨230859, by rfl⟩ : syracuseStep 2462501 = 461719) (by norm_num)
theorem B1086245 : Blo 479788 1086245 := bbase (se 4 (by rfl) ⟨101835, by rfl⟩ : syracuseStep 1086245 = 203671) (by norm_num)
theorem B627521 : Blo 479788 627521 := bbase (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) (by norm_num)
theorem B8262485 : Blo 479788 8262485 := bbase (se 9 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 8262485 = 48413) (by norm_num)
theorem B1217389 : Blo 479788 1217389 := bbase (se 3 (by rfl) ⟨228260, by rfl⟩ : syracuseStep 1217389 = 456521) (by norm_num)
theorem B1086317 : Blo 479788 1086317 := bbase (se 3 (by rfl) ⟨203684, by rfl⟩ : syracuseStep 1086317 = 407369) (by norm_num)
theorem B1086389 : Blo 479788 1086389 := bbase (se 5 (by rfl) ⟨50924, by rfl⟩ : syracuseStep 1086389 = 101849) (by norm_num)
theorem B1217501 : Blo 479788 1217501 := bbase (se 3 (by rfl) ⟨228281, by rfl⟩ : syracuseStep 1217501 = 456563) (by norm_num)
theorem B1086461 : Blo 479788 1086461 := bbase (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) (by norm_num)
theorem B693317 : Blo 479788 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B1086533 : Blo 479788 1086533 := bbase (se 4 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 1086533 = 203725) (by norm_num)
theorem B1086605 : Blo 479788 1086605 := bbase (se 3 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 1086605 = 407477) (by norm_num)
theorem B1217693 : Blo 479788 1217693 := bbase (se 3 (by rfl) ⟨228317, by rfl⟩ : syracuseStep 1217693 = 456635) (by norm_num)
theorem B1086677 : Blo 479788 1086677 := bbase (se 7 (by rfl) ⟨12734, by rfl⟩ : syracuseStep 1086677 = 25469) (by norm_num)
theorem B1086749 : Blo 479788 1086749 := bbase (se 3 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 1086749 = 407531) (by norm_num)
theorem B25335125 : Blo 479788 25335125 := bbase (se 14 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 25335125 = 4639) (by norm_num)
theorem B1086821 : Blo 479788 1086821 := bbase (se 4 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 1086821 = 203779) (by norm_num)
theorem B1086893 : Blo 479788 1086893 := bbase (se 3 (by rfl) ⟨203792, by rfl⟩ : syracuseStep 1086893 = 407585) (by norm_num)
theorem B1218037 : Blo 479788 1218037 := bbase (se 5 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 1218037 = 114191) (by norm_num)
theorem B1086965 : Blo 479788 1086965 := bbase (se 5 (by rfl) ⟨50951, by rfl⟩ : syracuseStep 1086965 = 101903) (by norm_num)
theorem B2430485 : Blo 479788 2430485 := bbase (se 6 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 2430485 = 113929) (by norm_num)
theorem B1087037 : Blo 479788 1087037 := bbase (se 3 (by rfl) ⟨203819, by rfl⟩ : syracuseStep 1087037 = 407639) (by norm_num)
theorem B661069 : Blo 479788 661069 := bbase (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) (by norm_num)
theorem B1218149 : Blo 479788 1218149 := bbase (se 4 (by rfl) ⟨114201, by rfl⟩ : syracuseStep 1218149 = 228403) (by norm_num)
theorem B1087109 : Blo 479788 1087109 := bbase (se 4 (by rfl) ⟨101916, by rfl⟩ : syracuseStep 1087109 = 203833) (by norm_num)
theorem B1545925 : Blo 479788 1545925 := bbase (se 4 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 1545925 = 289861) (by norm_num)
theorem B1087181 : Blo 479788 1087181 := bbase (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) (by norm_num)
theorem B1087253 : Blo 479788 1087253 := bbase (se 6 (by rfl) ⟨25482, by rfl⟩ : syracuseStep 1087253 = 50965) (by norm_num)
theorem B1218341 : Blo 479788 1218341 := bbase (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) (by norm_num)
theorem B1087325 : Blo 479788 1087325 := bbase (se 3 (by rfl) ⟨203873, by rfl⟩ : syracuseStep 1087325 = 407747) (by norm_num)
theorem B1087397 : Blo 479788 1087397 := bbase (se 4 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 1087397 = 203887) (by norm_num)
theorem B1087469 : Blo 479788 1087469 := bbase (se 3 (by rfl) ⟨203900, by rfl⟩ : syracuseStep 1087469 = 407801) (by norm_num)
theorem B923653 : Blo 479788 923653 := bbase (se 4 (by rfl) ⟨86592, by rfl⟩ : syracuseStep 923653 = 173185) (by norm_num)
theorem B1087541 : Blo 479788 1087541 := bbase (se 5 (by rfl) ⟨50978, by rfl⟩ : syracuseStep 1087541 = 101957) (by norm_num)
theorem B2922581 : Blo 479788 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B4954229 : Blo 479788 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B1218685 : Blo 479788 1218685 := bbase (se 3 (by rfl) ⟨228503, by rfl⟩ : syracuseStep 1218685 = 457007) (by norm_num)
theorem B1087613 : Blo 479788 1087613 := bbase (se 3 (by rfl) ⟨203927, by rfl⟩ : syracuseStep 1087613 = 407855) (by norm_num)
theorem B3643541 : Blo 479788 3643541 := bbase (se 6 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 3643541 = 170791) (by norm_num)
theorem B1087685 : Blo 479788 1087685 := bbase (se 4 (by rfl) ⟨101970, by rfl⟩ : syracuseStep 1087685 = 203941) (by norm_num)
theorem B1218797 : Blo 479788 1218797 := bbase (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) (by norm_num)
theorem B1087757 : Blo 479788 1087757 := bbase (se 3 (by rfl) ⟨203954, by rfl⟩ : syracuseStep 1087757 = 407909) (by norm_num)
theorem B989525 : Blo 479788 989525 := bbase (se 10 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 989525 = 2899) (by norm_num)
theorem B1087829 : Blo 479788 1087829 := bbase (se 10 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 1087829 = 3187) (by norm_num)
theorem B1087901 : Blo 479788 1087901 := bbase (se 3 (by rfl) ⟨203981, by rfl⟩ : syracuseStep 1087901 = 407963) (by norm_num)
theorem B1218989 : Blo 479788 1218989 := bbase (se 3 (by rfl) ⟨228560, by rfl⟩ : syracuseStep 1218989 = 457121) (by norm_num)
theorem B1087973 : Blo 479788 1087973 := bbase (se 4 (by rfl) ⟨101997, by rfl⟩ : syracuseStep 1087973 = 203995) (by norm_num)
theorem B825869 : Blo 479788 825869 := bbase (se 3 (by rfl) ⟨154850, by rfl⟩ : syracuseStep 825869 = 309701) (by norm_num)
theorem B1088045 : Blo 479788 1088045 := bbase (se 3 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 1088045 = 408017) (by norm_num)
theorem B1088117 : Blo 479788 1088117 := bbase (se 5 (by rfl) ⟨51005, by rfl⟩ : syracuseStep 1088117 = 102011) (by norm_num)
theorem B1088189 : Blo 479788 1088189 := bbase (se 3 (by rfl) ⟨204035, by rfl⟩ : syracuseStep 1088189 = 408071) (by norm_num)
theorem B1219333 : Blo 479788 1219333 := bbase (se 4 (by rfl) ⟨114312, by rfl⟩ : syracuseStep 1219333 = 228625) (by norm_num)
theorem B1088261 : Blo 479788 1088261 := bbase (se 4 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 1088261 = 204049) (by norm_num)
theorem B2431781 : Blo 479788 2431781 := bbase (se 4 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 2431781 = 455959) (by norm_num)
theorem B1088333 : Blo 479788 1088333 := bbase (se 3 (by rfl) ⟨204062, by rfl⟩ : syracuseStep 1088333 = 408125) (by norm_num)
theorem B2923381 : Blo 479788 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B1219445 : Blo 479788 1219445 := bbase (se 5 (by rfl) ⟨57161, by rfl⟩ : syracuseStep 1219445 = 114323) (by norm_num)
theorem B1088405 : Blo 479788 1088405 := bbase (se 6 (by rfl) ⟨25509, by rfl⟩ : syracuseStep 1088405 = 51019) (by norm_num)
theorem B1088477 : Blo 479788 1088477 := bbase (se 3 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 1088477 = 408179) (by norm_num)
theorem B1219637 : Blo 479788 1219637 := bbase (se 5 (by rfl) ⟨57170, by rfl⟩ : syracuseStep 1219637 = 114341) (by norm_num)
theorem B662581 : Blo 479788 662581 := bbase (se 5 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 662581 = 62117) (by norm_num)
theorem B1252565 : Blo 479788 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1547525 : Blo 479788 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B38083925 : Blo 479788 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B1219981 : Blo 479788 1219981 := bbase (se 3 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 1219981 = 457493) (by norm_num)
theorem B1220093 : Blo 479788 1220093 := bbase (se 3 (by rfl) ⟨228767, by rfl⟩ : syracuseStep 1220093 = 457535) (by norm_num)
theorem B4562453 : Blo 479788 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B1220285 : Blo 479788 1220285 := bbase (se 3 (by rfl) ⟨228803, by rfl⟩ : syracuseStep 1220285 = 457607) (by norm_num)
theorem B3088181 : Blo 479788 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B1220629 : Blo 479788 1220629 := bbase (se 6 (by rfl) ⟨28608, by rfl⟩ : syracuseStep 1220629 = 57217) (by norm_num)
theorem B2433077 : Blo 479788 2433077 := bbase (se 5 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 2433077 = 228101) (by norm_num)
theorem B7610453 : Blo 479788 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1220741 : Blo 479788 1220741 := bbase (se 4 (by rfl) ⟨114444, by rfl⟩ : syracuseStep 1220741 = 228889) (by norm_num)
theorem B1155397 : Blo 479788 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B1220933 : Blo 479788 1220933 := bbase (se 4 (by rfl) ⟨114462, by rfl⟩ : syracuseStep 1220933 = 228925) (by norm_num)
theorem B1548629 : Blo 479788 1548629 := bbase (se 10 (by rfl) ⟨2268, by rfl⟩ : syracuseStep 1548629 = 4537) (by norm_num)
theorem B1647029 : Blo 479788 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B4956821 : Blo 479788 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B1221277 : Blo 479788 1221277 := bbase (se 3 (by rfl) ⟨228989, by rfl⟩ : syracuseStep 1221277 = 457979) (by norm_num)
theorem B1221389 : Blo 479788 1221389 := bbase (se 3 (by rfl) ⟨229010, by rfl⟩ : syracuseStep 1221389 = 458021) (by norm_num)
theorem B1221581 : Blo 479788 1221581 := bbase (se 3 (by rfl) ⟨229046, by rfl⟩ : syracuseStep 1221581 = 458093) (by norm_num)
theorem B1156069 : Blo 479788 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B1025149 : Blo 479788 1025149 := bbase (se 3 (by rfl) ⟨192215, by rfl⟩ : syracuseStep 1025149 = 384431) (by norm_num)
theorem B1156301 : Blo 479788 1156301 := bbase (se 3 (by rfl) ⟨216806, by rfl⟩ : syracuseStep 1156301 = 433613) (by norm_num)
theorem B1025293 : Blo 479788 1025293 := bbase (se 3 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 1025293 = 384485) (by norm_num)
theorem B1221925 : Blo 479788 1221925 := bbase (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) (by norm_num)
theorem B2434373 : Blo 479788 2434373 := bbase (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) (by norm_num)
theorem B1156445 : Blo 479788 1156445 := bbase (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) (by norm_num)
theorem B1156493 : Blo 479788 1156493 := bbase (se 3 (by rfl) ⟨216842, by rfl⟩ : syracuseStep 1156493 = 433685) (by norm_num)
theorem B1222037 : Blo 479788 1222037 := bbase (se 6 (by rfl) ⟨28641, by rfl⟩ : syracuseStep 1222037 = 57283) (by norm_num)
theorem B2860469 : Blo 479788 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B2598389 : Blo 479788 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B1648181 : Blo 479788 1648181 := bbase (se 5 (by rfl) ⟨77258, by rfl⟩ : syracuseStep 1648181 = 154517) (by norm_num)
theorem B1222229 : Blo 479788 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B1025669 : Blo 479788 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B1156781 : Blo 479788 1156781 := bbase (se 3 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 1156781 = 433793) (by norm_num)
theorem B6596437 : Blo 479788 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B1222573 : Blo 479788 1222573 := bbase (se 3 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 1222573 = 458465) (by norm_num)
theorem B1026037 : Blo 479788 1026037 := bbase (se 5 (by rfl) ⟨48095, by rfl⟩ : syracuseStep 1026037 = 96191) (by norm_num)
theorem B1222685 : Blo 479788 1222685 := bbase (se 3 (by rfl) ⟨229253, by rfl⟩ : syracuseStep 1222685 = 458507) (by norm_num)
theorem B1222877 : Blo 479788 1222877 := bbase (se 3 (by rfl) ⟨229289, by rfl⟩ : syracuseStep 1222877 = 458579) (by norm_num)
theorem B2107765 : Blo 479788 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B1321397 : Blo 479788 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B1223221 : Blo 479788 1223221 := bbase (se 5 (by rfl) ⟨57338, by rfl⟩ : syracuseStep 1223221 = 114677) (by norm_num)
theorem B2435669 : Blo 479788 2435669 := bbase (se 8 (by rfl) ⟨14271, by rfl⟩ : syracuseStep 2435669 = 28543) (by norm_num)
theorem B1223333 : Blo 479788 1223333 := bbase (se 4 (by rfl) ⟨114687, by rfl⟩ : syracuseStep 1223333 = 229375) (by norm_num)
theorem B3517141 : Blo 479788 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B1223525 : Blo 479788 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B1223869 : Blo 479788 1223869 := bbase (se 3 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 1223869 = 458951) (by norm_num)
theorem B1223981 : Blo 479788 1223981 := bbase (se 3 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 1223981 = 458993) (by norm_num)
theorem B3485045 : Blo 479788 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B1027541 : Blo 479788 1027541 := bbase (se 7 (by rfl) ⟨12041, by rfl⟩ : syracuseStep 1027541 = 24083) (by norm_num)
theorem B1224173 : Blo 479788 1224173 := bbase (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) (by norm_num)
theorem B3092053 : Blo 479788 3092053 := bbase (se 8 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 3092053 = 36235) (by norm_num)
theorem B1027685 : Blo 479788 1027685 := bbase (se 4 (by rfl) ⟨96345, by rfl⟩ : syracuseStep 1027685 = 192691) (by norm_num)
theorem B1224517 : Blo 479788 1224517 := bbase (se 4 (by rfl) ⟨114798, by rfl⟩ : syracuseStep 1224517 = 229597) (by norm_num)
theorem B2436965 : Blo 479788 2436965 := bbase (se 4 (by rfl) ⟨228465, by rfl⟩ : syracuseStep 2436965 = 456931) (by norm_num)
theorem B1028045 : Blo 479788 1028045 := bbase (se 3 (by rfl) ⟨192758, by rfl⟩ : syracuseStep 1028045 = 385517) (by norm_num)
theorem B733133 : Blo 479788 733133 := bbase (se 3 (by rfl) ⟨137462, by rfl⟩ : syracuseStep 733133 = 274925) (by norm_num)
theorem B1159213 : Blo 479788 1159213 := bbase (se 3 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 1159213 = 434705) (by norm_num)
theorem B831973 : Blo 479788 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B1159829 : Blo 479788 1159829 := bbase (se 6 (by rfl) ⟨27183, by rfl⟩ : syracuseStep 1159829 = 54367) (by norm_num)
theorem B1389221 : Blo 479788 1389221 := bbase (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) (by norm_num)
theorem B1028933 : Blo 479788 1028933 := bbase (se 4 (by rfl) ⟨96462, by rfl⟩ : syracuseStep 1028933 = 192925) (by norm_num)
theorem B2732885 : Blo 479788 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B1160029 : Blo 479788 1160029 := bbase (se 3 (by rfl) ⟨217505, by rfl⟩ : syracuseStep 1160029 = 435011) (by norm_num)
theorem B4109237 : Blo 479788 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B1029181 : Blo 479788 1029181 := bbase (se 3 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 1029181 = 385943) (by norm_num)
theorem B2438261 : Blo 479788 2438261 := bbase (se 5 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 2438261 = 228587) (by norm_num)
theorem B865525 : Blo 479788 865525 := bbase (se 5 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 865525 = 81143) (by norm_num)
theorem B1095029 : Blo 479788 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B734653 : Blo 479788 734653 := bbase (se 3 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 734653 = 275495) (by norm_num)
theorem B865741 : Blo 479788 865741 := bbase (se 3 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 865741 = 324653) (by norm_num)
theorem B1029685 : Blo 479788 1029685 := bbase (se 5 (by rfl) ⟨48266, by rfl⟩ : syracuseStep 1029685 = 96533) (by norm_num)
theorem B1160837 : Blo 479788 1160837 := bbase (se 4 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 1160837 = 217657) (by norm_num)
theorem B1619621 : Blo 479788 1619621 := bbase (se 4 (by rfl) ⟨151839, by rfl⟩ : syracuseStep 1619621 = 303679) (by norm_num)
theorem B1947349 : Blo 479788 1947349 := bbase (se 7 (by rfl) ⟨22820, by rfl⟩ : syracuseStep 1947349 = 45641) (by norm_num)
theorem B734933 : Blo 479788 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B1947365 : Blo 479788 1947365 := bbase (se 4 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 1947365 = 365131) (by norm_num)
theorem B3651317 : Blo 479788 3651317 := bbase (se 5 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 3651317 = 342311) (by norm_num)
theorem B1620053 : Blo 479788 1620053 := bbase (se 8 (by rfl) ⟨9492, by rfl⟩ : syracuseStep 1620053 = 18985) (by norm_num)
theorem B2308277 : Blo 479788 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B735517 : Blo 479788 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B735565 : Blo 479788 735565 := bbase (se 3 (by rfl) ⟨137918, by rfl⟩ : syracuseStep 735565 = 275837) (by norm_num)
theorem B4405589 : Blo 479788 4405589 := bbase (se 10 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 4405589 = 12907) (by norm_num)
theorem B2439557 : Blo 479788 2439557 := bbase (se 4 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 2439557 = 457417) (by norm_num)
theorem B1161605 : Blo 479788 1161605 := bbase (se 4 (by rfl) ⟨108900, by rfl⟩ : syracuseStep 1161605 = 217801) (by norm_num)
theorem B1030573 : Blo 479788 1030573 := bbase (se 3 (by rfl) ⟨193232, by rfl⟩ : syracuseStep 1030573 = 386465) (by norm_num)
theorem B1096141 : Blo 479788 1096141 := bbase (se 3 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 1096141 = 411053) (by norm_num)
theorem B1620485 : Blo 479788 1620485 := bbase (se 4 (by rfl) ⟨151920, by rfl⟩ : syracuseStep 1620485 = 303841) (by norm_num)
theorem B768637 : Blo 479788 768637 := bbase (se 3 (by rfl) ⟨144119, by rfl⟩ : syracuseStep 768637 = 288239) (by norm_num)
theorem B1784533 : Blo 479788 1784533 := bbase (se 7 (by rfl) ⟨20912, by rfl⟩ : syracuseStep 1784533 = 41825) (by norm_num)
theorem B867125 : Blo 479788 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B2308949 : Blo 479788 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B1096597 : Blo 479788 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B1031069 : Blo 479788 1031069 := bbase (se 3 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 1031069 = 386651) (by norm_num)
theorem B1620917 : Blo 479788 1620917 := bbase (se 5 (by rfl) ⟨75980, by rfl⟩ : syracuseStep 1620917 = 151961) (by norm_num)
theorem B867277 : Blo 479788 867277 := bbase (se 3 (by rfl) ⟨162614, by rfl⟩ : syracuseStep 867277 = 325229) (by norm_num)
theorem B867341 : Blo 479788 867341 := bbase (se 3 (by rfl) ⟨162626, by rfl⟩ : syracuseStep 867341 = 325253) (by norm_num)
theorem B539797 : Blo 479788 539797 := bbase (se 6 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 539797 = 25303) (by norm_num)
theorem B867485 : Blo 479788 867485 := bbase (se 3 (by rfl) ⟨162653, by rfl⟩ : syracuseStep 867485 = 325307) (by norm_num)
theorem B539833 : Blo 479788 539833 := bbase (se 2 (by rfl) ⟨202437, by rfl⟩ : syracuseStep 539833 = 404875) (by norm_num)
theorem B539869 : Blo 479788 539869 := bbase (se 3 (by rfl) ⟨101225, by rfl⟩ : syracuseStep 539869 = 202451) (by norm_num)
theorem B539905 : Blo 479788 539905 := bbase (se 2 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 539905 = 404929) (by norm_num)
theorem B539941 : Blo 479788 539941 := bbase (se 4 (by rfl) ⟨50619, by rfl⟩ : syracuseStep 539941 = 101239) (by norm_num)
theorem B539977 : Blo 479788 539977 := bbase (se 2 (by rfl) ⟨202491, by rfl⟩ : syracuseStep 539977 = 404983) (by norm_num)
theorem B1621349 : Blo 479788 1621349 := bbase (se 4 (by rfl) ⟨152001, by rfl⟩ : syracuseStep 1621349 = 304003) (by norm_num)
theorem B540013 : Blo 479788 540013 := bbase (se 3 (by rfl) ⟨101252, by rfl⟩ : syracuseStep 540013 = 202505) (by norm_num)
theorem B540049 : Blo 479788 540049 := bbase (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) (by norm_num)
theorem B540085 : Blo 479788 540085 := bbase (se 5 (by rfl) ⟨25316, by rfl⟩ : syracuseStep 540085 = 50633) (by norm_num)
theorem B540121 : Blo 479788 540121 := bbase (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) (by norm_num)
theorem B540157 : Blo 479788 540157 := bbase (se 3 (by rfl) ⟨101279, by rfl⟩ : syracuseStep 540157 = 202559) (by norm_num)
theorem B540193 : Blo 479788 540193 := bbase (se 2 (by rfl) ⟨202572, by rfl⟩ : syracuseStep 540193 = 405145) (by norm_num)
theorem B540229 : Blo 479788 540229 := bbase (se 4 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 540229 = 101293) (by norm_num)
theorem B1097309 : Blo 479788 1097309 := bbase (se 3 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 1097309 = 411491) (by norm_num)
theorem B769637 : Blo 479788 769637 := bbase (se 4 (by rfl) ⟨72153, by rfl⟩ : syracuseStep 769637 = 144307) (by norm_num)
theorem B540265 : Blo 479788 540265 := bbase (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) (by norm_num)
theorem B540301 : Blo 479788 540301 := bbase (se 3 (by rfl) ⟨101306, by rfl⟩ : syracuseStep 540301 = 202613) (by norm_num)
theorem B2440853 : Blo 479788 2440853 := bbase (se 6 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 2440853 = 114415) (by norm_num)
theorem B540337 : Blo 479788 540337 := bbase (se 2 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 540337 = 405253) (by norm_num)
theorem B540373 : Blo 479788 540373 := bbase (se 7 (by rfl) ⟨6332, by rfl⟩ : syracuseStep 540373 = 12665) (by norm_num)
theorem B769765 : Blo 479788 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B540409 : Blo 479788 540409 := bbase (se 2 (by rfl) ⟨202653, by rfl⟩ : syracuseStep 540409 = 405307) (by norm_num)
theorem B1621781 : Blo 479788 1621781 := bbase (se 6 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 1621781 = 76021) (by norm_num)
theorem B1031957 : Blo 479788 1031957 := bbase (se 6 (by rfl) ⟨24186, by rfl⟩ : syracuseStep 1031957 = 48373) (by norm_num)
theorem B540445 : Blo 479788 540445 := bbase (se 3 (by rfl) ⟨101333, by rfl⟩ : syracuseStep 540445 = 202667) (by norm_num)
theorem B540481 : Blo 479788 540481 := bbase (se 2 (by rfl) ⟨202680, by rfl⟩ : syracuseStep 540481 = 405361) (by norm_num)
theorem B540517 : Blo 479788 540517 := bbase (se 4 (by rfl) ⟨50673, by rfl⟩ : syracuseStep 540517 = 101347) (by norm_num)
theorem B540553 : Blo 479788 540553 := bbase (se 2 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 540553 = 405415) (by norm_num)
theorem B1032077 : Blo 479788 1032077 := bbase (se 3 (by rfl) ⟨193514, by rfl⟩ : syracuseStep 1032077 = 387029) (by norm_num)
theorem B540589 : Blo 479788 540589 := bbase (se 3 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 540589 = 202721) (by norm_num)
theorem B540625 : Blo 479788 540625 := bbase (se 2 (by rfl) ⟨202734, by rfl⟩ : syracuseStep 540625 = 405469) (by norm_num)
theorem B540661 : Blo 479788 540661 := bbase (se 5 (by rfl) ⟨25343, by rfl⟩ : syracuseStep 540661 = 50687) (by norm_num)
theorem B540697 : Blo 479788 540697 := bbase (se 2 (by rfl) ⟨202761, by rfl⟩ : syracuseStep 540697 = 405523) (by norm_num)
theorem B540733 : Blo 479788 540733 := bbase (se 3 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 540733 = 202775) (by norm_num)
theorem B540769 : Blo 479788 540769 := bbase (se 2 (by rfl) ⟨202788, by rfl⟩ : syracuseStep 540769 = 405577) (by norm_num)
theorem B770149 : Blo 479788 770149 := bbase (se 4 (by rfl) ⟨72201, by rfl⟩ : syracuseStep 770149 = 144403) (by norm_num)
theorem B540805 : Blo 479788 540805 := bbase (se 4 (by rfl) ⟨50700, by rfl⟩ : syracuseStep 540805 = 101401) (by norm_num)
theorem B540841 : Blo 479788 540841 := bbase (se 2 (by rfl) ⟨202815, by rfl⟩ : syracuseStep 540841 = 405631) (by norm_num)
theorem B1622213 : Blo 479788 1622213 := bbase (se 4 (by rfl) ⟨152082, by rfl⟩ : syracuseStep 1622213 = 304165) (by norm_num)
theorem B540877 : Blo 479788 540877 := bbase (se 3 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 540877 = 202829) (by norm_num)
theorem B4636885 : Blo 479788 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B540913 : Blo 479788 540913 := bbase (se 2 (by rfl) ⟨202842, by rfl⟩ : syracuseStep 540913 = 405685) (by norm_num)
theorem B540949 : Blo 479788 540949 := bbase (se 6 (by rfl) ⟨12678, by rfl⟩ : syracuseStep 540949 = 25357) (by norm_num)
theorem B868661 : Blo 479788 868661 := bbase (se 5 (by rfl) ⟨40718, by rfl⟩ : syracuseStep 868661 = 81437) (by norm_num)
theorem B540985 : Blo 479788 540985 := bbase (se 2 (by rfl) ⟨202869, by rfl⟩ : syracuseStep 540985 = 405739) (by norm_num)
theorem B541021 : Blo 479788 541021 := bbase (se 3 (by rfl) ⟨101441, by rfl⟩ : syracuseStep 541021 = 202883) (by norm_num)
theorem B770405 : Blo 479788 770405 := bbase (se 4 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 770405 = 144451) (by norm_num)
theorem B541057 : Blo 479788 541057 := bbase (se 2 (by rfl) ⟨202896, by rfl⟩ : syracuseStep 541057 = 405793) (by norm_num)
theorem B541093 : Blo 479788 541093 := bbase (se 4 (by rfl) ⟨50727, by rfl⟩ : syracuseStep 541093 = 101455) (by norm_num)
theorem B541129 : Blo 479788 541129 := bbase (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) (by norm_num)
theorem B541165 : Blo 479788 541165 := bbase (se 3 (by rfl) ⟨101468, by rfl⟩ : syracuseStep 541165 = 202937) (by norm_num)
theorem B1032709 : Blo 479788 1032709 := bbase (se 4 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 1032709 = 193633) (by norm_num)
theorem B541201 : Blo 479788 541201 := bbase (se 2 (by rfl) ⟨202950, by rfl⟩ : syracuseStep 541201 = 405901) (by norm_num)
theorem B541237 : Blo 479788 541237 := bbase (se 5 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 541237 = 50741) (by norm_num)
theorem B541273 : Blo 479788 541273 := bbase (se 2 (by rfl) ⟨202977, by rfl⟩ : syracuseStep 541273 = 405955) (by norm_num)
theorem B1622645 : Blo 479788 1622645 := bbase (se 5 (by rfl) ⟨76061, by rfl⟩ : syracuseStep 1622645 = 152123) (by norm_num)
theorem B541309 : Blo 479788 541309 := bbase (se 3 (by rfl) ⟨101495, by rfl⟩ : syracuseStep 541309 = 202991) (by norm_num)
theorem B541345 : Blo 479788 541345 := bbase (se 2 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 541345 = 406009) (by norm_num)
theorem B541381 : Blo 479788 541381 := bbase (se 4 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 541381 = 101509) (by norm_num)
theorem B541417 : Blo 479788 541417 := bbase (se 2 (by rfl) ⟨203031, by rfl⟩ : syracuseStep 541417 = 406063) (by norm_num)
theorem B541453 : Blo 479788 541453 := bbase (se 3 (by rfl) ⟨101522, by rfl⟩ : syracuseStep 541453 = 203045) (by norm_num)
theorem B541489 : Blo 479788 541489 := bbase (se 2 (by rfl) ⟨203058, by rfl⟩ : syracuseStep 541489 = 406117) (by norm_num)
theorem B541525 : Blo 479788 541525 := bbase (se 9 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 541525 = 3173) (by norm_num)
theorem B541561 : Blo 479788 541561 := bbase (se 2 (by rfl) ⟨203085, by rfl⟩ : syracuseStep 541561 = 406171) (by norm_num)
theorem B541597 : Blo 479788 541597 := bbase (se 3 (by rfl) ⟨101549, by rfl⟩ : syracuseStep 541597 = 203099) (by norm_num)
theorem B2442149 : Blo 479788 2442149 := bbase (se 4 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 2442149 = 457903) (by norm_num)
theorem B1098677 : Blo 479788 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B541633 : Blo 479788 541633 := bbase (se 2 (by rfl) ⟨203112, by rfl⟩ : syracuseStep 541633 = 406225) (by norm_num)
theorem B541669 : Blo 479788 541669 := bbase (se 4 (by rfl) ⟨50781, by rfl⟩ : syracuseStep 541669 = 101563) (by norm_num)
theorem B541705 : Blo 479788 541705 := bbase (se 2 (by rfl) ⟨203139, by rfl⟩ : syracuseStep 541705 = 406279) (by norm_num)
theorem B1623077 : Blo 479788 1623077 := bbase (se 4 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 1623077 = 304327) (by norm_num)
theorem B967717 : Blo 479788 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B607277 : Blo 479788 607277 := bbase (se 3 (by rfl) ⟨113864, by rfl⟩ : syracuseStep 607277 = 227729) (by norm_num)
theorem B541741 : Blo 479788 541741 := bbase (se 3 (by rfl) ⟨101576, by rfl⟩ : syracuseStep 541741 = 203153) (by norm_num)
theorem B541777 : Blo 479788 541777 := bbase (se 2 (by rfl) ⟨203166, by rfl⟩ : syracuseStep 541777 = 406333) (by norm_num)
theorem B607333 : Blo 479788 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B541813 : Blo 479788 541813 := bbase (se 5 (by rfl) ⟨25397, by rfl⟩ : syracuseStep 541813 = 50795) (by norm_num)
theorem B541849 : Blo 479788 541849 := bbase (se 2 (by rfl) ⟨203193, by rfl⟩ : syracuseStep 541849 = 406387) (by norm_num)
theorem B2933941 : Blo 479788 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B541885 : Blo 479788 541885 := bbase (se 3 (by rfl) ⟨101603, by rfl⟩ : syracuseStep 541885 = 203207) (by norm_num)
theorem B607429 : Blo 479788 607429 := bbase (se 4 (by rfl) ⟨56946, by rfl⟩ : syracuseStep 607429 = 113893) (by norm_num)
theorem B771277 : Blo 479788 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B541921 : Blo 479788 541921 := bbase (se 2 (by rfl) ⟨203220, by rfl⟩ : syracuseStep 541921 = 406441) (by norm_num)
theorem B541957 : Blo 479788 541957 := bbase (se 4 (by rfl) ⟨50808, by rfl⟩ : syracuseStep 541957 = 101617) (by norm_num)
theorem B6964501 : Blo 479788 6964501 := bbase (se 6 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 6964501 = 326461) (by norm_num)
theorem B541993 : Blo 479788 541993 := bbase (se 2 (by rfl) ⟨203247, by rfl⟩ : syracuseStep 541993 = 406495) (by norm_num)
theorem B771373 : Blo 479788 771373 := bbase (se 3 (by rfl) ⟨144632, by rfl⟩ : syracuseStep 771373 = 289265) (by norm_num)
theorem B542029 : Blo 479788 542029 := bbase (se 3 (by rfl) ⟨101630, by rfl⟩ : syracuseStep 542029 = 203261) (by norm_num)
theorem B607601 : Blo 479788 607601 := bbase (se 2 (by rfl) ⟨227850, by rfl⟩ : syracuseStep 607601 = 455701) (by norm_num)
theorem B542065 : Blo 479788 542065 := bbase (se 2 (by rfl) ⟨203274, by rfl⟩ : syracuseStep 542065 = 406549) (by norm_num)
theorem B542101 : Blo 479788 542101 := bbase (se 6 (by rfl) ⟨12705, by rfl⟩ : syracuseStep 542101 = 25411) (by norm_num)
theorem B607657 : Blo 479788 607657 := bbase (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) (by norm_num)
theorem B542137 : Blo 479788 542137 := bbase (se 2 (by rfl) ⟨203301, by rfl⟩ : syracuseStep 542137 = 406603) (by norm_num)
theorem B1394117 : Blo 479788 1394117 := bbase (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) (by norm_num)
theorem B771533 : Blo 479788 771533 := bbase (se 3 (by rfl) ⟨144662, by rfl⟩ : syracuseStep 771533 = 289325) (by norm_num)
theorem B1623509 : Blo 479788 1623509 := bbase (se 7 (by rfl) ⟨19025, by rfl⟩ : syracuseStep 1623509 = 38051) (by norm_num)
theorem B542173 : Blo 479788 542173 := bbase (se 3 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 542173 = 203315) (by norm_num)
theorem B542209 : Blo 479788 542209 := bbase (se 2 (by rfl) ⟨203328, by rfl⟩ : syracuseStep 542209 = 406657) (by norm_num)
theorem B607753 : Blo 479788 607753 := bbase (se 2 (by rfl) ⟨227907, by rfl⟩ : syracuseStep 607753 = 455815) (by norm_num)
theorem B3720725 : Blo 479788 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B542245 : Blo 479788 542245 := bbase (se 4 (by rfl) ⟨50835, by rfl⟩ : syracuseStep 542245 = 101671) (by norm_num)
theorem B542281 : Blo 479788 542281 := bbase (se 2 (by rfl) ⟨203355, by rfl⟩ : syracuseStep 542281 = 406711) (by norm_num)
theorem B542317 : Blo 479788 542317 := bbase (se 3 (by rfl) ⟨101684, by rfl⟩ : syracuseStep 542317 = 203369) (by norm_num)
theorem B542353 : Blo 479788 542353 := bbase (se 2 (by rfl) ⟨203382, by rfl⟩ : syracuseStep 542353 = 406765) (by norm_num)
theorem B607925 : Blo 479788 607925 := bbase (se 5 (by rfl) ⟨28496, by rfl⟩ : syracuseStep 607925 = 56993) (by norm_num)
theorem B542389 : Blo 479788 542389 := bbase (se 5 (by rfl) ⟨25424, by rfl⟩ : syracuseStep 542389 = 50849) (by norm_num)
theorem B6178517 : Blo 479788 6178517 := bbase (se 7 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 6178517 = 144809) (by norm_num)
theorem B542425 : Blo 479788 542425 := bbase (se 2 (by rfl) ⟨203409, by rfl⟩ : syracuseStep 542425 = 406819) (by norm_num)
theorem B607981 : Blo 479788 607981 := bbase (se 3 (by rfl) ⟨113996, by rfl⟩ : syracuseStep 607981 = 227993) (by norm_num)
theorem B542461 : Blo 479788 542461 := bbase (se 3 (by rfl) ⟨101711, by rfl⟩ : syracuseStep 542461 = 203423) (by norm_num)
theorem B542497 : Blo 479788 542497 := bbase (se 2 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 542497 = 406873) (by norm_num)
theorem B542533 : Blo 479788 542533 := bbase (se 4 (by rfl) ⟨50862, by rfl⟩ : syracuseStep 542533 = 101725) (by norm_num)
theorem B2475845 : Blo 479788 2475845 := bbase (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) (by norm_num)
theorem B608077 : Blo 479788 608077 := bbase (se 3 (by rfl) ⟨114014, by rfl⟩ : syracuseStep 608077 = 228029) (by norm_num)
theorem B542569 : Blo 479788 542569 := bbase (se 2 (by rfl) ⟨203463, by rfl⟩ : syracuseStep 542569 = 406927) (by norm_num)
theorem B1623941 : Blo 479788 1623941 := bbase (se 4 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 1623941 = 304489) (by norm_num)
theorem B542605 : Blo 479788 542605 := bbase (se 3 (by rfl) ⟨101738, by rfl⟩ : syracuseStep 542605 = 203477) (by norm_num)
theorem B542641 : Blo 479788 542641 := bbase (se 2 (by rfl) ⟨203490, by rfl⟩ : syracuseStep 542641 = 406981) (by norm_num)
theorem B542677 : Blo 479788 542677 := bbase (se 7 (by rfl) ⟨6359, by rfl⟩ : syracuseStep 542677 = 12719) (by norm_num)
theorem B608249 : Blo 479788 608249 := bbase (se 2 (by rfl) ⟨228093, by rfl⟩ : syracuseStep 608249 = 456187) (by norm_num)
theorem B542713 : Blo 479788 542713 := bbase (se 2 (by rfl) ⟨203517, by rfl⟩ : syracuseStep 542713 = 407035) (by norm_num)
theorem B4769813 : Blo 479788 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B542749 : Blo 479788 542749 := bbase (se 3 (by rfl) ⟨101765, by rfl⟩ : syracuseStep 542749 = 203531) (by norm_num)
theorem B608305 : Blo 479788 608305 := bbase (se 2 (by rfl) ⟨228114, by rfl⟩ : syracuseStep 608305 = 456229) (by norm_num)
theorem B542785 : Blo 479788 542785 := bbase (se 2 (by rfl) ⟨203544, by rfl⟩ : syracuseStep 542785 = 407089) (by norm_num)
theorem B542821 : Blo 479788 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B542857 : Blo 479788 542857 := bbase (se 2 (by rfl) ⟨203571, by rfl⟩ : syracuseStep 542857 = 407143) (by norm_num)
theorem B608401 : Blo 479788 608401 := bbase (se 2 (by rfl) ⟨228150, by rfl⟩ : syracuseStep 608401 = 456301) (by norm_num)
theorem B542893 : Blo 479788 542893 := bbase (se 3 (by rfl) ⟨101792, by rfl⟩ : syracuseStep 542893 = 203585) (by norm_num)
theorem B2443445 : Blo 479788 2443445 := bbase (se 5 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 2443445 = 229073) (by norm_num)
theorem B542929 : Blo 479788 542929 := bbase (se 2 (by rfl) ⟨203598, by rfl⟩ : syracuseStep 542929 = 407197) (by norm_num)
theorem B542965 : Blo 479788 542965 := bbase (se 5 (by rfl) ⟨25451, by rfl⟩ : syracuseStep 542965 = 50903) (by norm_num)
theorem B543001 : Blo 479788 543001 := bbase (se 2 (by rfl) ⟨203625, by rfl⟩ : syracuseStep 543001 = 407251) (by norm_num)
theorem B1624373 : Blo 479788 1624373 := bbase (se 5 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 1624373 = 152285) (by norm_num)
theorem B608573 : Blo 479788 608573 := bbase (se 3 (by rfl) ⟨114107, by rfl⟩ : syracuseStep 608573 = 228215) (by norm_num)
theorem B543037 : Blo 479788 543037 := bbase (se 3 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 543037 = 203639) (by norm_num)
theorem B543073 : Blo 479788 543073 := bbase (se 2 (by rfl) ⟨203652, by rfl⟩ : syracuseStep 543073 = 407305) (by norm_num)
theorem B608629 : Blo 479788 608629 := bbase (se 5 (by rfl) ⟨28529, by rfl⟩ : syracuseStep 608629 = 57059) (by norm_num)
theorem B543109 : Blo 479788 543109 := bbase (se 4 (by rfl) ⟨50916, by rfl⟩ : syracuseStep 543109 = 101833) (by norm_num)
theorem B543145 : Blo 479788 543145 := bbase (se 2 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 543145 = 407359) (by norm_num)
theorem B2574773 : Blo 479788 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B4180405 : Blo 479788 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B543181 : Blo 479788 543181 := bbase (se 3 (by rfl) ⟨101846, by rfl⟩ : syracuseStep 543181 = 203693) (by norm_num)
theorem B608725 : Blo 479788 608725 := bbase (se 7 (by rfl) ⟨7133, by rfl⟩ : syracuseStep 608725 = 14267) (by norm_num)
theorem B543217 : Blo 479788 543217 := bbase (se 2 (by rfl) ⟨203706, by rfl⟩ : syracuseStep 543217 = 407413) (by norm_num)
theorem B543253 : Blo 479788 543253 := bbase (se 6 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 543253 = 25465) (by norm_num)
theorem B772661 : Blo 479788 772661 := bbase (se 5 (by rfl) ⟨36218, by rfl⟩ : syracuseStep 772661 = 72437) (by norm_num)
theorem B543289 : Blo 479788 543289 := bbase (se 2 (by rfl) ⟨203733, by rfl⟩ : syracuseStep 543289 = 407467) (by norm_num)
theorem B543325 : Blo 479788 543325 := bbase (se 3 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 543325 = 203747) (by norm_num)
theorem B608897 : Blo 479788 608897 := bbase (se 2 (by rfl) ⟨228336, by rfl⟩ : syracuseStep 608897 = 456673) (by norm_num)
theorem B543361 : Blo 479788 543361 := bbase (se 2 (by rfl) ⟨203760, by rfl⟩ : syracuseStep 543361 = 407521) (by norm_num)
theorem B543397 : Blo 479788 543397 := bbase (se 4 (by rfl) ⟨50943, by rfl⟩ : syracuseStep 543397 = 101887) (by norm_num)
theorem B608953 : Blo 479788 608953 := bbase (se 2 (by rfl) ⟨228357, by rfl⟩ : syracuseStep 608953 = 456715) (by norm_num)
theorem B543433 : Blo 479788 543433 := bbase (se 2 (by rfl) ⟨203787, by rfl⟩ : syracuseStep 543433 = 407575) (by norm_num)
theorem B1624805 : Blo 479788 1624805 := bbase (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) (by norm_num)
theorem B543469 : Blo 479788 543469 := bbase (se 3 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 543469 = 203801) (by norm_num)
theorem B543505 : Blo 479788 543505 := bbase (se 2 (by rfl) ⟨203814, by rfl⟩ : syracuseStep 543505 = 407629) (by norm_num)
theorem B609049 : Blo 479788 609049 := bbase (se 2 (by rfl) ⟨228393, by rfl⟩ : syracuseStep 609049 = 456787) (by norm_num)
theorem B1297205 : Blo 479788 1297205 := bbase (se 5 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 1297205 = 121613) (by norm_num)
theorem B543541 : Blo 479788 543541 := bbase (se 5 (by rfl) ⟨25478, by rfl⟩ : syracuseStep 543541 = 50957) (by norm_num)
theorem B543577 : Blo 479788 543577 := bbase (se 2 (by rfl) ⟨203841, by rfl⟩ : syracuseStep 543577 = 407683) (by norm_num)
theorem B543613 : Blo 479788 543613 := bbase (se 3 (by rfl) ⟨101927, by rfl⟩ : syracuseStep 543613 = 203855) (by norm_num)
theorem B576401 : Blo 479788 576401 := bbase (se 2 (by rfl) ⟨216150, by rfl⟩ : syracuseStep 576401 = 432301) (by norm_num)
theorem B543649 : Blo 479788 543649 := bbase (se 2 (by rfl) ⟨203868, by rfl⟩ : syracuseStep 543649 = 407737) (by norm_num)
theorem B609221 : Blo 479788 609221 := bbase (se 4 (by rfl) ⟨57114, by rfl⟩ : syracuseStep 609221 = 114229) (by norm_num)
theorem B543685 : Blo 479788 543685 := bbase (se 4 (by rfl) ⟨50970, by rfl⟩ : syracuseStep 543685 = 101941) (by norm_num)
theorem B4410325 : Blo 479788 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B543721 : Blo 479788 543721 := bbase (se 2 (by rfl) ⟨203895, by rfl⟩ : syracuseStep 543721 = 407791) (by norm_num)
theorem B609277 : Blo 479788 609277 := bbase (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) (by norm_num)
theorem B543757 : Blo 479788 543757 := bbase (se 3 (by rfl) ⟨101954, by rfl⟩ : syracuseStep 543757 = 203909) (by norm_num)
theorem B543793 : Blo 479788 543793 := bbase (se 2 (by rfl) ⟨203922, by rfl⟩ : syracuseStep 543793 = 407845) (by norm_num)
theorem B773173 : Blo 479788 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B543829 : Blo 479788 543829 := bbase (se 8 (by rfl) ⟨3186, by rfl⟩ : syracuseStep 543829 = 6373) (by norm_num)
theorem B609373 : Blo 479788 609373 := bbase (se 3 (by rfl) ⟨114257, by rfl⟩ : syracuseStep 609373 = 228515) (by norm_num)
theorem B543865 : Blo 479788 543865 := bbase (se 2 (by rfl) ⟨203949, by rfl⟩ : syracuseStep 543865 = 407899) (by norm_num)
theorem B1297541 : Blo 479788 1297541 := bbase (se 4 (by rfl) ⟨121644, by rfl⟩ : syracuseStep 1297541 = 243289) (by norm_num)
theorem B871565 : Blo 479788 871565 := bbase (se 3 (by rfl) ⟨163418, by rfl⟩ : syracuseStep 871565 = 326837) (by norm_num)
theorem B1625237 : Blo 479788 1625237 := bbase (se 6 (by rfl) ⟨38091, by rfl⟩ : syracuseStep 1625237 = 76183) (by norm_num)
theorem B543901 : Blo 479788 543901 := bbase (se 3 (by rfl) ⟨101981, by rfl⟩ : syracuseStep 543901 = 203963) (by norm_num)
theorem B543937 : Blo 479788 543937 := bbase (se 2 (by rfl) ⟨203976, by rfl⟩ : syracuseStep 543937 = 407953) (by norm_num)
theorem B543973 : Blo 479788 543973 := bbase (se 4 (by rfl) ⟨50997, by rfl⟩ : syracuseStep 543973 = 101995) (by norm_num)
theorem B609545 : Blo 479788 609545 := bbase (se 2 (by rfl) ⟨228579, by rfl⟩ : syracuseStep 609545 = 457159) (by norm_num)
theorem B544009 : Blo 479788 544009 := bbase (se 2 (by rfl) ⟨204003, by rfl⟩ : syracuseStep 544009 = 408007) (by norm_num)
theorem B642325 : Blo 479788 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B871717 : Blo 479788 871717 := bbase (se 4 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 871717 = 163447) (by norm_num)
theorem B544045 : Blo 479788 544045 := bbase (se 3 (by rfl) ⟨102008, by rfl⟩ : syracuseStep 544045 = 204017) (by norm_num)
theorem B609601 : Blo 479788 609601 := bbase (se 2 (by rfl) ⟨228600, by rfl⟩ : syracuseStep 609601 = 457201) (by norm_num)
theorem B544081 : Blo 479788 544081 := bbase (se 2 (by rfl) ⟨204030, by rfl⟩ : syracuseStep 544081 = 408061) (by norm_num)
theorem B544117 : Blo 479788 544117 := bbase (se 5 (by rfl) ⟨25505, by rfl⟩ : syracuseStep 544117 = 51011) (by norm_num)
theorem B544153 : Blo 479788 544153 := bbase (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) (by norm_num)
theorem B609697 : Blo 479788 609697 := bbase (se 2 (by rfl) ⟨228636, by rfl⟩ : syracuseStep 609697 = 457273) (by norm_num)
theorem B544189 : Blo 479788 544189 := bbase (se 3 (by rfl) ⟨102035, by rfl⟩ : syracuseStep 544189 = 204071) (by norm_num)
theorem B2444741 : Blo 479788 2444741 := bbase (se 4 (by rfl) ⟨229194, by rfl⟩ : syracuseStep 2444741 = 458389) (by norm_num)
theorem B1101269 : Blo 479788 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B544225 : Blo 479788 544225 := bbase (se 2 (by rfl) ⟨204084, by rfl⟩ : syracuseStep 544225 = 408169) (by norm_num)
theorem B544261 : Blo 479788 544261 := bbase (se 4 (by rfl) ⟨51024, by rfl⟩ : syracuseStep 544261 = 102049) (by norm_num)
theorem B577093 : Blo 479788 577093 := bbase (se 4 (by rfl) ⟨54102, by rfl⟩ : syracuseStep 577093 = 108205) (by norm_num)
theorem B1625669 : Blo 479788 1625669 := bbase (se 4 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 1625669 = 304813) (by norm_num)
theorem B609869 : Blo 479788 609869 := bbase (se 3 (by rfl) ⟨114350, by rfl⟩ : syracuseStep 609869 = 228701) (by norm_num)
theorem B609925 : Blo 479788 609925 := bbase (se 4 (by rfl) ⟨57180, by rfl⟩ : syracuseStep 609925 = 114361) (by norm_num)
theorem B577189 : Blo 479788 577189 := bbase (se 4 (by rfl) ⟨54111, by rfl⟩ : syracuseStep 577189 = 108223) (by norm_num)
theorem B1953461 : Blo 479788 1953461 := bbase (se 5 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 1953461 = 183137) (by norm_num)
theorem B1855157 : Blo 479788 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B610021 : Blo 479788 610021 := bbase (se 4 (by rfl) ⟨57189, by rfl⟩ : syracuseStep 610021 = 114379) (by norm_num)
theorem B610193 : Blo 479788 610193 := bbase (se 2 (by rfl) ⟨228822, by rfl⟩ : syracuseStep 610193 = 457645) (by norm_num)
theorem B610249 : Blo 479788 610249 := bbase (se 2 (by rfl) ⟨228843, by rfl⟩ : syracuseStep 610249 = 457687) (by norm_num)
theorem B1626101 : Blo 479788 1626101 := bbase (se 5 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 1626101 = 152447) (by norm_num)
theorem B774173 : Blo 479788 774173 := bbase (se 3 (by rfl) ⟨145157, by rfl⟩ : syracuseStep 774173 = 290315) (by norm_num)
theorem B577573 : Blo 479788 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B610345 : Blo 479788 610345 := bbase (se 2 (by rfl) ⟨228879, by rfl⟩ : syracuseStep 610345 = 457759) (by norm_num)
theorem B774301 : Blo 479788 774301 := bbase (se 3 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 774301 = 290363) (by norm_num)
theorem B1462469 : Blo 479788 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B610517 : Blo 479788 610517 := bbase (se 7 (by rfl) ⟨7154, by rfl⟩ : syracuseStep 610517 = 14309) (by norm_num)
theorem B774365 : Blo 479788 774365 := bbase (se 3 (by rfl) ⟨145193, by rfl⟩ : syracuseStep 774365 = 290387) (by norm_num)
theorem B610573 : Blo 479788 610573 := bbase (se 3 (by rfl) ⟨114482, by rfl⟩ : syracuseStep 610573 = 228965) (by norm_num)
theorem B610669 : Blo 479788 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B1823093 : Blo 479788 1823093 := bbase (se 5 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 1823093 = 170915) (by norm_num)
theorem B2052485 : Blo 479788 2052485 := bbase (se 4 (by rfl) ⟨192420, by rfl⟩ : syracuseStep 2052485 = 384841) (by norm_num)
theorem B1626533 : Blo 479788 1626533 := bbase (se 4 (by rfl) ⟨152487, by rfl⟩ : syracuseStep 1626533 = 304975) (by norm_num)
theorem B1102325 : Blo 479788 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B610841 : Blo 479788 610841 := bbase (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) (by norm_num)
theorem B610897 : Blo 479788 610897 := bbase (se 2 (by rfl) ⟨229086, by rfl⟩ : syracuseStep 610897 = 458173) (by norm_num)
theorem B1823381 : Blo 479788 1823381 := bbase (se 6 (by rfl) ⟨42735, by rfl⟩ : syracuseStep 1823381 = 85471) (by norm_num)
theorem B512677 : Blo 479788 512677 := bbase (se 4 (by rfl) ⟨48063, by rfl⟩ : syracuseStep 512677 = 96127) (by norm_num)
theorem B2052773 : Blo 479788 2052773 := bbase (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) (by norm_num)
theorem B610993 : Blo 479788 610993 := bbase (se 2 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 610993 = 458245) (by norm_num)
theorem B2740949 : Blo 479788 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B2446037 : Blo 479788 2446037 := bbase (se 7 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 2446037 = 57329) (by norm_num)
theorem B512749 : Blo 479788 512749 := bbase (se 3 (by rfl) ⟨96140, by rfl⟩ : syracuseStep 512749 = 192281) (by norm_num)
theorem B4117301 : Blo 479788 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B1626965 : Blo 479788 1626965 := bbase (se 9 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 1626965 = 9533) (by norm_num)
theorem B611165 : Blo 479788 611165 := bbase (se 3 (by rfl) ⟨114593, by rfl⟩ : syracuseStep 611165 = 229187) (by norm_num)
theorem B4739957 : Blo 479788 4739957 := bbase (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) (by norm_num)
theorem B611221 : Blo 479788 611221 := bbase (se 6 (by rfl) ⟨14325, by rfl⟩ : syracuseStep 611221 = 28651) (by norm_num)
theorem B512929 : Blo 479788 512929 := bbase (se 2 (by rfl) ⟨192348, by rfl⟩ : syracuseStep 512929 = 384697) (by norm_num)
theorem B611317 : Blo 479788 611317 := bbase (se 5 (by rfl) ⟨28655, by rfl⟩ : syracuseStep 611317 = 57311) (by norm_num)
theorem B578621 : Blo 479788 578621 := bbase (se 3 (by rfl) ⟨108491, by rfl⟩ : syracuseStep 578621 = 216983) (by norm_num)
theorem B611489 : Blo 479788 611489 := bbase (se 2 (by rfl) ⟨229308, by rfl⟩ : syracuseStep 611489 = 458617) (by norm_num)
theorem B611545 : Blo 479788 611545 := bbase (se 2 (by rfl) ⟨229329, by rfl⟩ : syracuseStep 611545 = 458659) (by norm_num)
theorem B1627397 : Blo 479788 1627397 := bbase (se 4 (by rfl) ⟨152568, by rfl⟩ : syracuseStep 1627397 = 305137) (by norm_num)
theorem B611641 : Blo 479788 611641 := bbase (se 2 (by rfl) ⟨229365, by rfl⟩ : syracuseStep 611641 = 458731) (by norm_num)
theorem B3659093 : Blo 479788 3659093 := bbase (se 15 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3659093 = 335) (by norm_num)
theorem B513373 : Blo 479788 513373 := bbase (se 3 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 513373 = 192515) (by norm_num)
theorem B578929 : Blo 479788 578929 := bbase (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) (by norm_num)
theorem B578957 : Blo 479788 578957 := bbase (se 3 (by rfl) ⟨108554, by rfl⟩ : syracuseStep 578957 = 217109) (by norm_num)
theorem B2053525 : Blo 479788 2053525 := bbase (se 6 (by rfl) ⟨48129, by rfl⟩ : syracuseStep 2053525 = 96259) (by norm_num)
theorem B513497 : Blo 479788 513497 := bbase (se 2 (by rfl) ⟨192561, by rfl⟩ : syracuseStep 513497 = 385123) (by norm_num)
theorem B611813 : Blo 479788 611813 := bbase (se 4 (by rfl) ⟨57357, by rfl⟩ : syracuseStep 611813 = 114715) (by norm_num)
theorem B611869 : Blo 479788 611869 := bbase (se 3 (by rfl) ⟨114725, by rfl⟩ : syracuseStep 611869 = 229451) (by norm_num)
theorem B611965 : Blo 479788 611965 := bbase (se 3 (by rfl) ⟨114743, by rfl⟩ : syracuseStep 611965 = 229487) (by norm_num)
theorem B1627829 : Blo 479788 1627829 := bbase (se 5 (by rfl) ⟨76304, by rfl⟩ : syracuseStep 1627829 = 152609) (by norm_num)
theorem B513749 : Blo 479788 513749 := bbase (se 7 (by rfl) ⟨6020, by rfl⟩ : syracuseStep 513749 = 12041) (by norm_num)
theorem B612137 : Blo 479788 612137 := bbase (se 2 (by rfl) ⟨229551, by rfl⟩ : syracuseStep 612137 = 459103) (by norm_num)
theorem B1824565 : Blo 479788 1824565 := bbase (se 5 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 1824565 = 171053) (by norm_num)
theorem B612193 : Blo 479788 612193 := bbase (se 2 (by rfl) ⟨229572, by rfl⟩ : syracuseStep 612193 = 459145) (by norm_num)
theorem B2742133 : Blo 479788 2742133 := bbase (se 5 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 2742133 = 257075) (by norm_num)
theorem B579457 : Blo 479788 579457 := bbase (se 2 (by rfl) ⟨217296, by rfl⟩ : syracuseStep 579457 = 434593) (by norm_num)
theorem B612289 : Blo 479788 612289 := bbase (se 2 (by rfl) ⟨229608, by rfl⟩ : syracuseStep 612289 = 459217) (by norm_num)
theorem B2447333 : Blo 479788 2447333 := bbase (se 4 (by rfl) ⟨229437, by rfl⟩ : syracuseStep 2447333 = 458875) (by norm_num)
theorem B720893 : Blo 479788 720893 := bbase (se 3 (by rfl) ⟨135167, by rfl⟩ : syracuseStep 720893 = 270335) (by norm_num)
theorem B1824869 : Blo 479788 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B1628261 : Blo 479788 1628261 := bbase (se 4 (by rfl) ⟨152649, by rfl⟩ : syracuseStep 1628261 = 305299) (by norm_num)
theorem B2054261 : Blo 479788 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B514193 : Blo 479788 514193 := bbase (se 2 (by rfl) ⟨192822, by rfl⟩ : syracuseStep 514193 = 385645) (by norm_num)
theorem B10377557 : Blo 479788 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B514441 : Blo 479788 514441 := bbase (se 2 (by rfl) ⟨192915, by rfl⟩ : syracuseStep 514441 = 385831) (by norm_num)
theorem B4708853 : Blo 479788 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B1628693 : Blo 479788 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B1858085 : Blo 479788 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B809669 : Blo 479788 809669 := bbase (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) (by norm_num)
theorem B940781 : Blo 479788 940781 := bbase (se 3 (by rfl) ⟨176396, by rfl⟩ : syracuseStep 940781 = 352793) (by norm_num)
theorem B809797 : Blo 479788 809797 := bbase (se 4 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 809797 = 151837) (by norm_num)
theorem B514885 : Blo 479788 514885 := bbase (se 4 (by rfl) ⟨48270, by rfl⟩ : syracuseStep 514885 = 96541) (by norm_num)
theorem B514945 : Blo 479788 514945 := bbase (se 2 (by rfl) ⟨193104, by rfl⟩ : syracuseStep 514945 = 386209) (by norm_num)
theorem B809885 : Blo 479788 809885 := bbase (se 3 (by rfl) ⟨151853, by rfl⟩ : syracuseStep 809885 = 303707) (by norm_num)
theorem B1956773 : Blo 479788 1956773 := bbase (se 4 (by rfl) ⟨183447, by rfl⟩ : syracuseStep 1956773 = 366895) (by norm_num)
theorem B3464117 : Blo 479788 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B1629125 : Blo 479788 1629125 := bbase (se 4 (by rfl) ⟨152730, by rfl⟩ : syracuseStep 1629125 = 305461) (by norm_num)
theorem B973829 : Blo 479788 973829 := bbase (se 4 (by rfl) ⟨91296, by rfl⟩ : syracuseStep 973829 = 182593) (by norm_num)
theorem B810013 : Blo 479788 810013 := bbase (se 3 (by rfl) ⟨151877, by rfl⟩ : syracuseStep 810013 = 303755) (by norm_num)
theorem B580645 : Blo 479788 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B1301573 : Blo 479788 1301573 := bbase (se 4 (by rfl) ⟨122022, by rfl⟩ : syracuseStep 1301573 = 244045) (by norm_num)
theorem B810101 : Blo 479788 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B515261 : Blo 479788 515261 := bbase (se 3 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 515261 = 193223) (by norm_num)
theorem B1465573 : Blo 479788 1465573 := bbase (se 4 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 1465573 = 274795) (by norm_num)
theorem B580837 : Blo 479788 580837 := bbase (se 4 (by rfl) ⟨54453, by rfl⟩ : syracuseStep 580837 = 108907) (by norm_num)
theorem B810229 : Blo 479788 810229 := bbase (se 5 (by rfl) ⟨37979, by rfl⟩ : syracuseStep 810229 = 75959) (by norm_num)
theorem B2448629 : Blo 479788 2448629 := bbase (se 5 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 2448629 = 229559) (by norm_num)
theorem B580937 : Blo 479788 580937 := bbase (se 2 (by rfl) ⟨217851, by rfl⟩ : syracuseStep 580937 = 435703) (by norm_num)
theorem B810317 : Blo 479788 810317 := bbase (se 3 (by rfl) ⟨151934, by rfl⟩ : syracuseStep 810317 = 303869) (by norm_num)
theorem B1629557 : Blo 479788 1629557 := bbase (se 5 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 1629557 = 152771) (by norm_num)
theorem B810445 : Blo 479788 810445 := bbase (se 3 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 810445 = 303917) (by norm_num)
theorem B810533 : Blo 479788 810533 := bbase (se 4 (by rfl) ⟨75987, by rfl⟩ : syracuseStep 810533 = 151975) (by norm_num)
theorem B515705 : Blo 479788 515705 := bbase (se 2 (by rfl) ⟨193389, by rfl⟩ : syracuseStep 515705 = 386779) (by norm_num)
theorem B810661 : Blo 479788 810661 := bbase (se 4 (by rfl) ⟨75999, by rfl⟩ : syracuseStep 810661 = 151999) (by norm_num)
theorem B1040045 : Blo 479788 1040045 := bbase (se 3 (by rfl) ⟨195008, by rfl⟩ : syracuseStep 1040045 = 390017) (by norm_num)
theorem B515765 : Blo 479788 515765 := bbase (se 5 (by rfl) ⟨24176, by rfl⟩ : syracuseStep 515765 = 48353) (by norm_num)
theorem B974525 : Blo 479788 974525 := bbase (se 3 (by rfl) ⟨182723, by rfl⟩ : syracuseStep 974525 = 365447) (by norm_num)
theorem B810749 : Blo 479788 810749 := bbase (se 3 (by rfl) ⟨152015, by rfl⟩ : syracuseStep 810749 = 304031) (by norm_num)
theorem B1629989 : Blo 479788 1629989 := bbase (se 4 (by rfl) ⟨152811, by rfl⟩ : syracuseStep 1629989 = 305623) (by norm_num)
theorem B2744117 : Blo 479788 2744117 := bbase (se 5 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 2744117 = 257261) (by norm_num)
theorem B515893 : Blo 479788 515893 := bbase (se 5 (by rfl) ⟨24182, by rfl⟩ : syracuseStep 515893 = 48365) (by norm_num)
theorem B810877 : Blo 479788 810877 := bbase (se 3 (by rfl) ⟨152039, by rfl⟩ : syracuseStep 810877 = 304079) (by norm_num)
theorem B2318213 : Blo 479788 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B810965 : Blo 479788 810965 := bbase (se 7 (by rfl) ⟨9503, by rfl⟩ : syracuseStep 810965 = 19007) (by norm_num)
theorem B811093 : Blo 479788 811093 := bbase (se 8 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 811093 = 9505) (by norm_num)
theorem B1368197 : Blo 479788 1368197 := bbase (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) (by norm_num)
theorem B1826981 : Blo 479788 1826981 := bbase (se 4 (by rfl) ⟨171279, by rfl⟩ : syracuseStep 1826981 = 342559) (by norm_num)
theorem B811181 : Blo 479788 811181 := bbase (se 3 (by rfl) ⟨152096, by rfl⟩ : syracuseStep 811181 = 304193) (by norm_num)
theorem B1630421 : Blo 479788 1630421 := bbase (se 7 (by rfl) ⟨19106, by rfl⟩ : syracuseStep 1630421 = 38213) (by norm_num)
theorem B516337 : Blo 479788 516337 := bbase (se 2 (by rfl) ⟨193626, by rfl⟩ : syracuseStep 516337 = 387253) (by norm_num)
theorem B2318597 : Blo 479788 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B811309 : Blo 479788 811309 := bbase (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) (by norm_num)
theorem B549193 : Blo 479788 549193 := bbase (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) (by norm_num)
theorem B516457 : Blo 479788 516457 := bbase (se 2 (by rfl) ⟨193671, by rfl⟩ : syracuseStep 516457 = 387343) (by norm_num)
theorem B1466741 : Blo 479788 1466741 := bbase (se 5 (by rfl) ⟨68753, by rfl⟩ : syracuseStep 1466741 = 137507) (by norm_num)
theorem B811397 : Blo 479788 811397 := bbase (se 4 (by rfl) ⟨76068, by rfl⟩ : syracuseStep 811397 = 152137) (by norm_num)
theorem B1827269 : Blo 479788 1827269 := bbase (se 4 (by rfl) ⟨171306, by rfl⟩ : syracuseStep 1827269 = 342613) (by norm_num)
theorem B811525 : Blo 479788 811525 := bbase (se 4 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 811525 = 152161) (by norm_num)
theorem B811613 : Blo 479788 811613 := bbase (se 3 (by rfl) ⟨152177, by rfl⟩ : syracuseStep 811613 = 304355) (by norm_num)
theorem B1630853 : Blo 479788 1630853 := bbase (se 4 (by rfl) ⟨152892, by rfl⟩ : syracuseStep 1630853 = 305785) (by norm_num)
theorem B811741 : Blo 479788 811741 := bbase (se 3 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 811741 = 304403) (by norm_num)
theorem B549649 : Blo 479788 549649 := bbase (se 2 (by rfl) ⟨206118, by rfl⟩ : syracuseStep 549649 = 412237) (by norm_num)
theorem B811829 : Blo 479788 811829 := bbase (se 5 (by rfl) ⟨38054, by rfl⟩ : syracuseStep 811829 = 76109) (by norm_num)
theorem B549685 : Blo 479788 549685 := bbase (se 5 (by rfl) ⟨25766, by rfl⟩ : syracuseStep 549685 = 51533) (by norm_num)
theorem B2614133 : Blo 479788 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B811957 : Blo 479788 811957 := bbase (se 5 (by rfl) ⟨38060, by rfl⟩ : syracuseStep 811957 = 76121) (by norm_num)
theorem B812045 : Blo 479788 812045 := bbase (se 3 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 812045 = 304517) (by norm_num)
theorem B1631285 : Blo 479788 1631285 := bbase (se 5 (by rfl) ⟨76466, by rfl⟩ : syracuseStep 1631285 = 152933) (by norm_num)
theorem B1729637 : Blo 479788 1729637 := bbase (se 4 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 1729637 = 324307) (by norm_num)
theorem B1959029 : Blo 479788 1959029 := bbase (se 5 (by rfl) ⟨91829, by rfl⟩ : syracuseStep 1959029 = 183659) (by norm_num)
theorem B1303685 : Blo 479788 1303685 := bbase (se 4 (by rfl) ⟨122220, by rfl⟩ : syracuseStep 1303685 = 244441) (by norm_num)
theorem B812173 : Blo 479788 812173 := bbase (se 3 (by rfl) ⟨152282, by rfl⟩ : syracuseStep 812173 = 304565) (by norm_num)
theorem B812261 : Blo 479788 812261 := bbase (se 4 (by rfl) ⟨76149, by rfl⟩ : syracuseStep 812261 = 152299) (by norm_num)
theorem B1729781 : Blo 479788 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B550141 : Blo 479788 550141 := bbase (se 3 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 550141 = 206303) (by norm_num)
theorem B1959173 : Blo 479788 1959173 := bbase (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) (by norm_num)
theorem B1369381 : Blo 479788 1369381 := bbase (se 4 (by rfl) ⟨128379, by rfl⟩ : syracuseStep 1369381 = 256759) (by norm_num)
theorem B2057557 : Blo 479788 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B812389 : Blo 479788 812389 := bbase (se 4 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 812389 = 152323) (by norm_num)
theorem B1467749 : Blo 479788 1467749 := bbase (se 4 (by rfl) ⟨137601, by rfl⟩ : syracuseStep 1467749 = 275203) (by norm_num)
theorem B812477 : Blo 479788 812477 := bbase (se 3 (by rfl) ⟨152339, by rfl⟩ : syracuseStep 812477 = 304679) (by norm_num)
theorem B1369541 : Blo 479788 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B550361 : Blo 479788 550361 := bbase (se 2 (by rfl) ⟨206385, by rfl⟩ : syracuseStep 550361 = 412771) (by norm_num)
theorem B1631717 : Blo 479788 1631717 := bbase (se 4 (by rfl) ⟨152973, by rfl⟩ : syracuseStep 1631717 = 305947) (by norm_num)
theorem B1730069 : Blo 479788 1730069 := bbase (se 6 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 1730069 = 81097) (by norm_num)
theorem B910901 : Blo 479788 910901 := bbase (se 5 (by rfl) ⟨42698, by rfl⟩ : syracuseStep 910901 = 85397) (by norm_num)
theorem B812605 : Blo 479788 812605 := bbase (se 3 (by rfl) ⟨152363, by rfl⟩ : syracuseStep 812605 = 304727) (by norm_num)
theorem B1828453 : Blo 479788 1828453 := bbase (se 4 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 1828453 = 342835) (by norm_num)
theorem B812693 : Blo 479788 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B1369781 : Blo 479788 1369781 := bbase (se 5 (by rfl) ⟨64208, by rfl⟩ : syracuseStep 1369781 = 128417) (by norm_num)
theorem B4187861 : Blo 479788 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B3892981 : Blo 479788 3892981 := bbase (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) (by norm_num)
theorem B812821 : Blo 479788 812821 := bbase (se 6 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 812821 = 38101) (by norm_num)
theorem B911189 : Blo 479788 911189 := bbase (se 9 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 911189 = 5339) (by norm_num)
theorem B812909 : Blo 479788 812909 := bbase (se 3 (by rfl) ⟨152420, by rfl⟩ : syracuseStep 812909 = 304841) (by norm_num)
theorem B1369973 : Blo 479788 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B1828757 : Blo 479788 1828757 := bbase (se 6 (by rfl) ⟨42861, by rfl⟩ : syracuseStep 1828757 = 85723) (by norm_num)
theorem B1468309 : Blo 479788 1468309 := bbase (se 6 (by rfl) ⟨34413, by rfl⟩ : syracuseStep 1468309 = 68827) (by norm_num)
theorem B1632149 : Blo 479788 1632149 := bbase (se 6 (by rfl) ⟨38253, by rfl⟩ : syracuseStep 1632149 = 76507) (by norm_num)
theorem B2746325 : Blo 479788 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B911341 : Blo 479788 911341 := bbase (se 3 (by rfl) ⟨170876, by rfl⟩ : syracuseStep 911341 = 341753) (by norm_num)
theorem B813037 : Blo 479788 813037 := bbase (se 3 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 813037 = 304889) (by norm_num)
theorem B3893237 : Blo 479788 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B8775701 : Blo 479788 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B813125 : Blo 479788 813125 := bbase (se 4 (by rfl) ⟨76230, by rfl⟩ : syracuseStep 813125 = 152461) (by norm_num)
theorem B813253 : Blo 479788 813253 := bbase (se 4 (by rfl) ⟨76242, by rfl⟩ : syracuseStep 813253 = 152485) (by norm_num)
theorem B911645 : Blo 479788 911645 := bbase (se 3 (by rfl) ⟨170933, by rfl⟩ : syracuseStep 911645 = 341867) (by norm_num)
theorem B813341 : Blo 479788 813341 := bbase (se 3 (by rfl) ⟨152501, by rfl⟩ : syracuseStep 813341 = 305003) (by norm_num)
theorem B1632581 : Blo 479788 1632581 := bbase (se 4 (by rfl) ⟨153054, by rfl⟩ : syracuseStep 1632581 = 306109) (by norm_num)
theorem B780653 : Blo 479788 780653 := bbase (se 3 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 780653 = 292745) (by norm_num)
theorem B813469 : Blo 479788 813469 := bbase (se 3 (by rfl) ⟨152525, by rfl⟩ : syracuseStep 813469 = 305051) (by norm_num)
theorem B813557 : Blo 479788 813557 := bbase (se 5 (by rfl) ⟨38135, by rfl⟩ : syracuseStep 813557 = 76271) (by norm_num)
theorem B813685 : Blo 479788 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B813773 : Blo 479788 813773 := bbase (se 3 (by rfl) ⟨152582, by rfl⟩ : syracuseStep 813773 = 305165) (by norm_num)
theorem B813901 : Blo 479788 813901 := bbase (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) (by norm_num)
theorem B1370965 : Blo 479788 1370965 := bbase (se 9 (by rfl) ⟨4016, by rfl⟩ : syracuseStep 1370965 = 8033) (by norm_num)
theorem B813989 : Blo 479788 813989 := bbase (se 4 (by rfl) ⟨76311, by rfl⟩ : syracuseStep 813989 = 152623) (by norm_num)
theorem B1043389 : Blo 479788 1043389 := bbase (se 3 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 1043389 = 391271) (by norm_num)
theorem B912397 : Blo 479788 912397 := bbase (se 3 (by rfl) ⟨171074, by rfl⟩ : syracuseStep 912397 = 342149) (by norm_num)
theorem B814117 : Blo 479788 814117 := bbase (se 4 (by rfl) ⟨76323, by rfl⟩ : syracuseStep 814117 = 152647) (by norm_num)
theorem B1469477 : Blo 479788 1469477 := bbase (se 4 (by rfl) ⟨137763, by rfl⟩ : syracuseStep 1469477 = 275527) (by norm_num)
theorem B814205 : Blo 479788 814205 := bbase (se 3 (by rfl) ⟨152663, by rfl⟩ : syracuseStep 814205 = 305327) (by norm_num)
theorem B912541 : Blo 479788 912541 := bbase (se 3 (by rfl) ⟨171101, by rfl⟩ : syracuseStep 912541 = 342203) (by norm_num)
theorem B1731797 : Blo 479788 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B3075317 : Blo 479788 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B814333 : Blo 479788 814333 := bbase (se 3 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 814333 = 305375) (by norm_num)
theorem B650549 : Blo 479788 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B912701 : Blo 479788 912701 := bbase (se 3 (by rfl) ⟨171131, by rfl⟩ : syracuseStep 912701 = 342263) (by norm_num)
theorem B814421 : Blo 479788 814421 := bbase (se 11 (by rfl) ⟨596, by rfl⟩ : syracuseStep 814421 = 1193) (by norm_num)
theorem B7925141 : Blo 479788 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B912845 : Blo 479788 912845 := bbase (se 3 (by rfl) ⟨171158, by rfl⟩ : syracuseStep 912845 = 342317) (by norm_num)
theorem B814549 : Blo 479788 814549 := bbase (se 7 (by rfl) ⟨9545, by rfl⟩ : syracuseStep 814549 = 19091) (by norm_num)
theorem B880141 : Blo 479788 880141 := bbase (se 3 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 880141 = 330053) (by norm_num)
theorem B814637 : Blo 479788 814637 := bbase (se 3 (by rfl) ⟨152744, by rfl⟩ : syracuseStep 814637 = 305489) (by norm_num)
theorem B683597 : Blo 479788 683597 := bbase (se 3 (by rfl) ⟨128174, by rfl⟩ : syracuseStep 683597 = 256349) (by norm_num)
theorem B683677 : Blo 479788 683677 := bbase (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) (by norm_num)
theorem B814765 : Blo 479788 814765 := bbase (se 3 (by rfl) ⟨152768, by rfl⟩ : syracuseStep 814765 = 305537) (by norm_num)
theorem B913133 : Blo 479788 913133 := bbase (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) (by norm_num)
theorem B814853 : Blo 479788 814853 := bbase (se 4 (by rfl) ⟨76392, by rfl⟩ : syracuseStep 814853 = 152785) (by norm_num)
theorem B683797 : Blo 479788 683797 := bbase (se 6 (by rfl) ⟨16026, by rfl⟩ : syracuseStep 683797 = 32053) (by norm_num)
theorem B683893 : Blo 479788 683893 := bbase (se 5 (by rfl) ⟨32057, by rfl⟩ : syracuseStep 683893 = 64115) (by norm_num)
theorem B913285 : Blo 479788 913285 := bbase (se 4 (by rfl) ⟨85620, by rfl⟩ : syracuseStep 913285 = 171241) (by norm_num)
theorem B814981 : Blo 479788 814981 := bbase (se 4 (by rfl) ⟨76404, by rfl⟩ : syracuseStep 814981 = 152809) (by norm_num)
theorem B1372069 : Blo 479788 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B1732549 : Blo 479788 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B1830869 : Blo 479788 1830869 := bbase (se 7 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 1830869 = 42911) (by norm_num)
theorem B815069 : Blo 479788 815069 := bbase (se 3 (by rfl) ⟨152825, by rfl⟩ : syracuseStep 815069 = 305651) (by norm_num)
theorem B815197 : Blo 479788 815197 := bbase (se 3 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 815197 = 305699) (by norm_num)
theorem B913589 : Blo 479788 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B815285 : Blo 479788 815285 := bbase (se 5 (by rfl) ⟨38216, by rfl⟩ : syracuseStep 815285 = 76433) (by norm_num)
theorem B618725 : Blo 479788 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B1831157 : Blo 479788 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B2060549 : Blo 479788 2060549 := bbase (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) (by norm_num)
theorem B815413 : Blo 479788 815413 := bbase (se 5 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 815413 = 76445) (by norm_num)
theorem B684389 : Blo 479788 684389 := bbase (se 4 (by rfl) ⟨64161, by rfl⟩ : syracuseStep 684389 = 128323) (by norm_num)
theorem B815501 : Blo 479788 815501 := bbase (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) (by norm_num)
theorem B815629 : Blo 479788 815629 := bbase (se 3 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 815629 = 305861) (by norm_num)
theorem B815717 : Blo 479788 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B815845 : Blo 479788 815845 := bbase (se 4 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 815845 = 152971) (by norm_num)
theorem B1176365 : Blo 479788 1176365 := bbase (se 3 (by rfl) ⟨220568, by rfl⟩ : syracuseStep 1176365 = 441137) (by norm_num)
theorem B815933 : Blo 479788 815933 := bbase (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) (by norm_num)
theorem B684941 : Blo 479788 684941 := bbase (se 3 (by rfl) ⟨128426, by rfl⟩ : syracuseStep 684941 = 256853) (by norm_num)
theorem B914341 : Blo 479788 914341 := bbase (se 4 (by rfl) ⟨85719, by rfl⟩ : syracuseStep 914341 = 171439) (by norm_num)
theorem B1733557 : Blo 479788 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B3666869 : Blo 479788 3666869 := bbase (se 5 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 3666869 = 343769) (by norm_num)
theorem B816061 : Blo 479788 816061 := bbase (se 3 (by rfl) ⟨153011, by rfl⟩ : syracuseStep 816061 = 306023) (by norm_num)
theorem B816149 : Blo 479788 816149 := bbase (se 6 (by rfl) ⟨19128, by rfl⟩ : syracuseStep 816149 = 38257) (by norm_num)
theorem B914485 : Blo 479788 914485 := bbase (se 5 (by rfl) ⟨42866, by rfl⟩ : syracuseStep 914485 = 85733) (by norm_num)
theorem B816277 : Blo 479788 816277 := bbase (se 6 (by rfl) ⟨19131, by rfl⟩ : syracuseStep 816277 = 38263) (by norm_num)
theorem B914645 : Blo 479788 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B816365 : Blo 479788 816365 := bbase (se 3 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 816365 = 306137) (by norm_num)
theorem B2061557 : Blo 479788 2061557 := bbase (se 5 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 2061557 = 193271) (by norm_num)
theorem B914789 : Blo 479788 914789 := bbase (se 4 (by rfl) ⟨85761, by rfl⟩ : syracuseStep 914789 = 171523) (by norm_num)
theorem B1373573 : Blo 479788 1373573 := bbase (se 4 (by rfl) ⟨128772, by rfl⟩ : syracuseStep 1373573 = 257545) (by norm_num)
theorem B980357 : Blo 479788 980357 := bbase (se 4 (by rfl) ⟨91908, by rfl⟩ : syracuseStep 980357 = 183817) (by norm_num)
theorem B1832341 : Blo 479788 1832341 := bbase (se 6 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 1832341 = 85891) (by norm_num)
theorem B685693 : Blo 479788 685693 := bbase (se 3 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 685693 = 257135) (by norm_num)
theorem B915077 : Blo 479788 915077 := bbase (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) (by norm_num)
theorem B620177 : Blo 479788 620177 := bbase (se 2 (by rfl) ⟨232566, by rfl⟩ : syracuseStep 620177 = 465133) (by norm_num)
theorem B1832645 : Blo 479788 1832645 := bbase (se 4 (by rfl) ⟨171810, by rfl⟩ : syracuseStep 1832645 = 343621) (by norm_num)
theorem B882389 : Blo 479788 882389 := bbase (se 7 (by rfl) ⟨10340, by rfl⟩ : syracuseStep 882389 = 20681) (by norm_num)
theorem B915229 : Blo 479788 915229 := bbase (se 3 (by rfl) ⟨171605, by rfl⟩ : syracuseStep 915229 = 343211) (by norm_num)
theorem B489533 : Blo 479788 489533 := bbase (se 3 (by rfl) ⟨91787, by rfl⟩ : syracuseStep 489533 = 183575) (by norm_num)
theorem B915533 : Blo 479788 915533 := bbase (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) (by norm_num)
theorem B1079549 : Blo 479788 1079549 := bbase (se 3 (by rfl) ⟨202415, by rfl⟩ : syracuseStep 1079549 = 404831) (by norm_num)
theorem B1079621 : Blo 479788 1079621 := bbase (se 4 (by rfl) ⟨101214, by rfl⟩ : syracuseStep 1079621 = 202429) (by norm_num)
theorem B1079693 : Blo 479788 1079693 := bbase (se 3 (by rfl) ⟨202442, by rfl⟩ : syracuseStep 1079693 = 404885) (by norm_num)
theorem B1538453 : Blo 479788 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B686485 : Blo 479788 686485 := bbase (se 6 (by rfl) ⟨16089, by rfl⟩ : syracuseStep 686485 = 32179) (by norm_num)
theorem B653717 : Blo 479788 653717 := bbase (se 6 (by rfl) ⟨15321, by rfl⟩ : syracuseStep 653717 = 30643) (by norm_num)
theorem B1079765 : Blo 479788 1079765 := bbase (se 7 (by rfl) ⟨12653, by rfl⟩ : syracuseStep 1079765 = 25307) (by norm_num)
theorem B1079837 : Blo 479788 1079837 := bbase (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) (by norm_num)
theorem B1079909 : Blo 479788 1079909 := bbase (se 4 (by rfl) ⟨101241, by rfl⟩ : syracuseStep 1079909 = 202483) (by norm_num)
theorem B490093 : Blo 479788 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B1079981 : Blo 479788 1079981 := bbase (se 3 (by rfl) ⟨202496, by rfl⟩ : syracuseStep 1079981 = 404993) (by norm_num)
theorem B686821 : Blo 479788 686821 := bbase (se 4 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 686821 = 128779) (by norm_num)
theorem B1080053 : Blo 479788 1080053 := bbase (se 5 (by rfl) ⟨50627, by rfl⟩ : syracuseStep 1080053 = 101255) (by norm_num)
theorem B1080125 : Blo 479788 1080125 := bbase (se 3 (by rfl) ⟨202523, by rfl⟩ : syracuseStep 1080125 = 405047) (by norm_num)
theorem B916285 : Blo 479788 916285 := bbase (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) (by norm_num)
theorem B719693 : Blo 479788 719693 := bbase (se 3 (by rfl) ⟨134942, by rfl⟩ : syracuseStep 719693 = 269885) (by norm_num)
theorem B523105 : Blo 479788 523105 := bbase (se 2 (by rfl) ⟨196164, by rfl⟩ : syracuseStep 523105 = 392329) (by norm_num)
theorem B719717 : Blo 479788 719717 := bbase (se 4 (by rfl) ⟨67473, by rfl⟩ : syracuseStep 719717 = 134947) (by norm_num)
theorem B719741 : Blo 479788 719741 := bbase (se 3 (by rfl) ⟨134951, by rfl⟩ : syracuseStep 719741 = 269903) (by norm_num)
theorem B1080197 : Blo 479788 1080197 := bbase (se 4 (by rfl) ⟨101268, by rfl⟩ : syracuseStep 1080197 = 202537) (by norm_num)
theorem B719765 : Blo 479788 719765 := bbase (se 6 (by rfl) ⟨16869, by rfl⟩ : syracuseStep 719765 = 33739) (by norm_num)
theorem B719789 : Blo 479788 719789 := bbase (se 3 (by rfl) ⟨134960, by rfl⟩ : syracuseStep 719789 = 269921) (by norm_num)
theorem B1375157 : Blo 479788 1375157 := bbase (se 5 (by rfl) ⟨64460, by rfl⟩ : syracuseStep 1375157 = 128921) (by norm_num)
theorem B687037 : Blo 479788 687037 := bbase (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) (by norm_num)
theorem B719813 : Blo 479788 719813 := bbase (se 4 (by rfl) ⟨67482, by rfl⟩ : syracuseStep 719813 = 134965) (by norm_num)
theorem B1080269 : Blo 479788 1080269 := bbase (se 3 (by rfl) ⟨202550, by rfl⟩ : syracuseStep 1080269 = 405101) (by norm_num)
theorem B916429 : Blo 479788 916429 := bbase (se 3 (by rfl) ⟨171830, by rfl⟩ : syracuseStep 916429 = 343661) (by norm_num)
theorem B719837 : Blo 479788 719837 := bbase (se 3 (by rfl) ⟨134969, by rfl⟩ : syracuseStep 719837 = 269939) (by norm_num)
theorem B2063333 : Blo 479788 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B719861 : Blo 479788 719861 := bbase (se 5 (by rfl) ⟨33743, by rfl⟩ : syracuseStep 719861 = 67487) (by norm_num)
theorem B1407989 : Blo 479788 1407989 := bbase (se 5 (by rfl) ⟨65999, by rfl⟩ : syracuseStep 1407989 = 131999) (by norm_num)
theorem B719885 : Blo 479788 719885 := bbase (se 3 (by rfl) ⟨134978, by rfl⟩ : syracuseStep 719885 = 269957) (by norm_num)
theorem B1080341 : Blo 479788 1080341 := bbase (se 6 (by rfl) ⟨25320, by rfl⟩ : syracuseStep 1080341 = 50641) (by norm_num)
theorem B719909 : Blo 479788 719909 := bbase (se 4 (by rfl) ⟨67491, by rfl⟩ : syracuseStep 719909 = 134983) (by norm_num)
theorem B719933 : Blo 479788 719933 := bbase (se 3 (by rfl) ⟨134987, by rfl⟩ : syracuseStep 719933 = 269975) (by norm_num)
theorem B719957 : Blo 479788 719957 := bbase (se 8 (by rfl) ⟨4218, by rfl⟩ : syracuseStep 719957 = 8437) (by norm_num)
theorem B1080413 : Blo 479788 1080413 := bbase (se 3 (by rfl) ⟨202577, by rfl⟩ : syracuseStep 1080413 = 405155) (by norm_num)
theorem B719981 : Blo 479788 719981 := bbase (se 3 (by rfl) ⟨134996, by rfl⟩ : syracuseStep 719981 = 269993) (by norm_num)
theorem B916589 : Blo 479788 916589 := bbase (se 3 (by rfl) ⟨171860, by rfl⟩ : syracuseStep 916589 = 343721) (by norm_num)
theorem B720005 : Blo 479788 720005 := bbase (se 4 (by rfl) ⟨67500, by rfl⟩ : syracuseStep 720005 = 135001) (by norm_num)
theorem B720029 : Blo 479788 720029 := bbase (se 3 (by rfl) ⟨135005, by rfl⟩ : syracuseStep 720029 = 270011) (by norm_num)
theorem B1080485 : Blo 479788 1080485 := bbase (se 4 (by rfl) ⟨101295, by rfl⟩ : syracuseStep 1080485 = 202591) (by norm_num)
theorem B720053 : Blo 479788 720053 := bbase (se 5 (by rfl) ⟨33752, by rfl⟩ : syracuseStep 720053 = 67505) (by norm_num)
theorem B720077 : Blo 479788 720077 := bbase (se 3 (by rfl) ⟨135014, by rfl⟩ : syracuseStep 720077 = 270029) (by norm_num)
theorem B720101 : Blo 479788 720101 := bbase (se 4 (by rfl) ⟨67509, by rfl⟩ : syracuseStep 720101 = 135019) (by norm_num)
theorem B1080557 : Blo 479788 1080557 := bbase (se 3 (by rfl) ⟨202604, by rfl⟩ : syracuseStep 1080557 = 405209) (by norm_num)
theorem B720125 : Blo 479788 720125 := bbase (se 3 (by rfl) ⟨135023, by rfl⟩ : syracuseStep 720125 = 270047) (by norm_num)
theorem B916733 : Blo 479788 916733 := bbase (se 3 (by rfl) ⟨171887, by rfl⟩ : syracuseStep 916733 = 343775) (by norm_num)
theorem B720149 : Blo 479788 720149 := bbase (se 6 (by rfl) ⟨16878, by rfl⟩ : syracuseStep 720149 = 33757) (by norm_num)
theorem B720173 : Blo 479788 720173 := bbase (se 3 (by rfl) ⟨135032, by rfl⟩ : syracuseStep 720173 = 270065) (by norm_num)
theorem B1080629 : Blo 479788 1080629 := bbase (se 5 (by rfl) ⟨50654, by rfl⟩ : syracuseStep 1080629 = 101309) (by norm_num)
theorem B687413 : Blo 479788 687413 := bbase (se 5 (by rfl) ⟨32222, by rfl⟩ : syracuseStep 687413 = 64445) (by norm_num)
theorem B720197 : Blo 479788 720197 := bbase (se 4 (by rfl) ⟨67518, by rfl⟩ : syracuseStep 720197 = 135037) (by norm_num)
theorem B720221 : Blo 479788 720221 := bbase (se 3 (by rfl) ⟨135041, by rfl⟩ : syracuseStep 720221 = 270083) (by norm_num)
theorem B720245 : Blo 479788 720245 := bbase (se 5 (by rfl) ⟨33761, by rfl⟩ : syracuseStep 720245 = 67523) (by norm_num)
theorem B1080701 : Blo 479788 1080701 := bbase (se 3 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 1080701 = 405263) (by norm_num)
theorem B720269 : Blo 479788 720269 := bbase (se 3 (by rfl) ⟨135050, by rfl⟩ : syracuseStep 720269 = 270101) (by norm_num)
theorem B720293 : Blo 479788 720293 := bbase (se 4 (by rfl) ⟨67527, by rfl⟩ : syracuseStep 720293 = 135055) (by norm_num)
theorem B720317 : Blo 479788 720317 := bbase (se 3 (by rfl) ⟨135059, by rfl⟩ : syracuseStep 720317 = 270119) (by norm_num)
theorem B1080773 : Blo 479788 1080773 := bbase (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) (by norm_num)
theorem B720341 : Blo 479788 720341 := bbase (se 7 (by rfl) ⟨8441, by rfl⟩ : syracuseStep 720341 = 16883) (by norm_num)
theorem B720365 : Blo 479788 720365 := bbase (se 3 (by rfl) ⟨135068, by rfl⟩ : syracuseStep 720365 = 270137) (by norm_num)
theorem B720389 : Blo 479788 720389 := bbase (se 4 (by rfl) ⟨67536, by rfl⟩ : syracuseStep 720389 = 135073) (by norm_num)
theorem B1080845 : Blo 479788 1080845 := bbase (se 3 (by rfl) ⟨202658, by rfl⟩ : syracuseStep 1080845 = 405317) (by norm_num)
theorem B917021 : Blo 479788 917021 := bbase (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) (by norm_num)
theorem B720413 : Blo 479788 720413 := bbase (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) (by norm_num)
theorem B720437 : Blo 479788 720437 := bbase (se 5 (by rfl) ⟨33770, by rfl⟩ : syracuseStep 720437 = 67541) (by norm_num)
theorem B720461 : Blo 479788 720461 := bbase (se 3 (by rfl) ⟨135086, by rfl⟩ : syracuseStep 720461 = 270173) (by norm_num)
theorem B1080917 : Blo 479788 1080917 := bbase (se 8 (by rfl) ⟨6333, by rfl⟩ : syracuseStep 1080917 = 12667) (by norm_num)
theorem B1375829 : Blo 479788 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B720485 : Blo 479788 720485 := bbase (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) (by norm_num)
theorem B720509 : Blo 479788 720509 := bbase (se 3 (by rfl) ⟨135095, by rfl⟩ : syracuseStep 720509 = 270191) (by norm_num)
theorem B720533 : Blo 479788 720533 := bbase (se 6 (by rfl) ⟨16887, by rfl⟩ : syracuseStep 720533 = 33775) (by norm_num)
theorem B1080989 : Blo 479788 1080989 := bbase (se 3 (by rfl) ⟨202685, by rfl⟩ : syracuseStep 1080989 = 405371) (by norm_num)
theorem B720557 : Blo 479788 720557 := bbase (se 3 (by rfl) ⟨135104, by rfl⟩ : syracuseStep 720557 = 270209) (by norm_num)
theorem B917173 : Blo 479788 917173 := bbase (se 5 (by rfl) ⟨42992, by rfl⟩ : syracuseStep 917173 = 85985) (by norm_num)
theorem B720581 : Blo 479788 720581 := bbase (se 4 (by rfl) ⟨67554, by rfl⟩ : syracuseStep 720581 = 135109) (by norm_num)
theorem B720605 : Blo 479788 720605 := bbase (se 3 (by rfl) ⟨135113, by rfl⟩ : syracuseStep 720605 = 270227) (by norm_num)
theorem B1081061 : Blo 479788 1081061 := bbase (se 4 (by rfl) ⟨101349, by rfl⟩ : syracuseStep 1081061 = 202699) (by norm_num)
theorem B720629 : Blo 479788 720629 := bbase (se 5 (by rfl) ⟨33779, by rfl⟩ : syracuseStep 720629 = 67559) (by norm_num)
theorem B1834757 : Blo 479788 1834757 := bbase (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) (by norm_num)
theorem B720653 : Blo 479788 720653 := bbase (se 3 (by rfl) ⟨135122, by rfl⟩ : syracuseStep 720653 = 270245) (by norm_num)
theorem B720677 : Blo 479788 720677 := bbase (se 4 (by rfl) ⟨67563, by rfl⟩ : syracuseStep 720677 = 135127) (by norm_num)
theorem B1081133 : Blo 479788 1081133 := bbase (se 3 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 1081133 = 405425) (by norm_num)
theorem B2817845 : Blo 479788 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B720701 : Blo 479788 720701 := bbase (se 3 (by rfl) ⟨135131, by rfl⟩ : syracuseStep 720701 = 270263) (by norm_num)
theorem B720725 : Blo 479788 720725 := bbase (se 9 (by rfl) ⟨2111, by rfl⟩ : syracuseStep 720725 = 4223) (by norm_num)
theorem B3702613 : Blo 479788 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B720749 : Blo 479788 720749 := bbase (se 3 (by rfl) ⟨135140, by rfl⟩ : syracuseStep 720749 = 270281) (by norm_num)
theorem B1081205 : Blo 479788 1081205 := bbase (se 5 (by rfl) ⟨50681, by rfl⟩ : syracuseStep 1081205 = 101363) (by norm_num)
theorem B720773 : Blo 479788 720773 := bbase (se 4 (by rfl) ⟨67572, by rfl⟩ : syracuseStep 720773 = 135145) (by norm_num)
theorem B720797 : Blo 479788 720797 := bbase (se 3 (by rfl) ⟨135149, by rfl⟩ : syracuseStep 720797 = 270299) (by norm_num)
theorem B720821 : Blo 479788 720821 := bbase (se 5 (by rfl) ⟨33788, by rfl⟩ : syracuseStep 720821 = 67577) (by norm_num)
theorem B1081277 : Blo 479788 1081277 := bbase (se 3 (by rfl) ⟨202739, by rfl⟩ : syracuseStep 1081277 = 405479) (by norm_num)
theorem B720845 : Blo 479788 720845 := bbase (se 3 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 720845 = 270317) (by norm_num)
theorem B720869 : Blo 479788 720869 := bbase (se 4 (by rfl) ⟨67581, by rfl⟩ : syracuseStep 720869 = 135163) (by norm_num)
theorem B917477 : Blo 479788 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B720899 : Blo 479788 720899 := bstep (se 1 (by rfl) ⟨540674, by rfl⟩ : syracuseStep 720899 = 1081349) B1081349
theorem B917507 : Blo 479788 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B720929 : Blo 479788 720929 := bstep (se 2 (by rfl) ⟨270348, by rfl⟩ : syracuseStep 720929 = 540697) B540697
theorem B720947 : Blo 479788 720947 := bstep (se 1 (by rfl) ⟨540710, by rfl⟩ : syracuseStep 720947 = 1081421) B1081421
theorem B720977 : Blo 479788 720977 := bstep (se 2 (by rfl) ⟨270366, by rfl⟩ : syracuseStep 720977 = 540733) B540733
theorem B720995 : Blo 479788 720995 := bstep (se 1 (by rfl) ⟨540746, by rfl⟩ : syracuseStep 720995 = 1081493) B1081493
theorem B1081457 : Blo 479788 1081457 := bstep (se 2 (by rfl) ⟨405546, by rfl⟩ : syracuseStep 1081457 = 811093) B811093
theorem B721025 : Blo 479788 721025 := bstep (se 2 (by rfl) ⟨270384, by rfl⟩ : syracuseStep 721025 = 540769) B540769
theorem B1081475 : Blo 479788 1081475 := bstep (se 1 (by rfl) ⟨811106, by rfl⟩ : syracuseStep 1081475 = 1622213) B1622213
theorem B721043 : Blo 479788 721043 := bstep (se 1 (by rfl) ⟨540782, by rfl⟩ : syracuseStep 721043 = 1081565) B1081565
theorem B721073 : Blo 479788 721073 := bstep (se 2 (by rfl) ⟨270402, by rfl⟩ : syracuseStep 721073 = 540805) B540805
theorem B721091 : Blo 479788 721091 := bstep (se 1 (by rfl) ⟨540818, by rfl⟩ : syracuseStep 721091 = 1081637) B1081637
theorem B721121 : Blo 479788 721121 := bstep (se 2 (by rfl) ⟨270420, by rfl⟩ : syracuseStep 721121 = 540841) B540841
theorem B721139 : Blo 479788 721139 := bstep (se 1 (by rfl) ⟨540854, by rfl⟩ : syracuseStep 721139 = 1081709) B1081709
theorem B721169 : Blo 479788 721169 := bstep (se 2 (by rfl) ⟨270438, by rfl⟩ : syracuseStep 721169 = 540877) B540877
theorem B721187 : Blo 479788 721187 := bstep (se 1 (by rfl) ⟨540890, by rfl⟩ : syracuseStep 721187 = 1081781) B1081781
theorem B721217 : Blo 479788 721217 := bstep (se 2 (by rfl) ⟨270456, by rfl⟩ : syracuseStep 721217 = 540913) B540913
theorem B721235 : Blo 479788 721235 := bstep (se 1 (by rfl) ⟨540926, by rfl⟩ : syracuseStep 721235 = 1081853) B1081853
theorem B721265 : Blo 479788 721265 := bstep (se 2 (by rfl) ⟨270474, by rfl⟩ : syracuseStep 721265 = 540949) B540949
theorem B721283 : Blo 479788 721283 := bstep (se 1 (by rfl) ⟨540962, by rfl⟩ : syracuseStep 721283 = 1081925) B1081925
theorem B1081745 : Blo 479788 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B721313 : Blo 479788 721313 := bstep (se 2 (by rfl) ⟨270492, by rfl⟩ : syracuseStep 721313 = 540985) B540985
theorem B1081763 : Blo 479788 1081763 := bstep (se 1 (by rfl) ⟨811322, by rfl⟩ : syracuseStep 1081763 = 1622645) B1622645
theorem B1540529 : Blo 479788 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B721331 : Blo 479788 721331 := bstep (se 1 (by rfl) ⟨540998, by rfl⟩ : syracuseStep 721331 = 1081997) B1081997
theorem B721361 : Blo 479788 721361 := bstep (se 2 (by rfl) ⟨270510, by rfl⟩ : syracuseStep 721361 = 541021) B541021
theorem B688609 : Blo 479788 688609 := bstep (se 2 (by rfl) ⟨258228, by rfl⟩ : syracuseStep 688609 = 516457) B516457
theorem B721379 : Blo 479788 721379 := bstep (se 1 (by rfl) ⟨541034, by rfl⟩ : syracuseStep 721379 = 1082069) B1082069
theorem B721409 : Blo 479788 721409 := bstep (se 2 (by rfl) ⟨270528, by rfl⟩ : syracuseStep 721409 = 541057) B541057
theorem B3899917 : Blo 479788 3899917 := bstep (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) B1462469
theorem B721427 : Blo 479788 721427 := bstep (se 1 (by rfl) ⟨541070, by rfl⟩ : syracuseStep 721427 = 1082141) B1082141
theorem B721457 : Blo 479788 721457 := bstep (se 2 (by rfl) ⟨270546, by rfl⟩ : syracuseStep 721457 = 541093) B541093
theorem B721475 : Blo 479788 721475 := bstep (se 1 (by rfl) ⟨541106, by rfl⟩ : syracuseStep 721475 = 1082213) B1082213
theorem B2064973 : Blo 479788 2064973 := bstep (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) B774365
theorem B721505 : Blo 479788 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B721523 : Blo 479788 721523 := bstep (se 1 (by rfl) ⟨541142, by rfl⟩ : syracuseStep 721523 = 1082285) B1082285
theorem B721553 : Blo 479788 721553 := bstep (se 2 (by rfl) ⟨270582, by rfl⟩ : syracuseStep 721553 = 541165) B541165
theorem B721571 : Blo 479788 721571 := bstep (se 1 (by rfl) ⟨541178, by rfl⟩ : syracuseStep 721571 = 1082357) B1082357
theorem B1082033 : Blo 479788 1082033 := bstep (se 2 (by rfl) ⟨405762, by rfl⟩ : syracuseStep 1082033 = 811525) B811525
theorem B1376945 : Blo 479788 1376945 := bstep (se 2 (by rfl) ⟨516354, by rfl⟩ : syracuseStep 1376945 = 1032709) B1032709
theorem B721601 : Blo 479788 721601 := bstep (se 2 (by rfl) ⟨270600, by rfl⟩ : syracuseStep 721601 = 541201) B541201
theorem B1082051 : Blo 479788 1082051 := bstep (se 1 (by rfl) ⟨811538, by rfl⟩ : syracuseStep 1082051 = 1623077) B1623077
theorem B721619 : Blo 479788 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B721649 : Blo 479788 721649 := bstep (se 2 (by rfl) ⟨270618, by rfl⟩ : syracuseStep 721649 = 541237) B541237
theorem B721667 : Blo 479788 721667 := bstep (se 1 (by rfl) ⟨541250, by rfl⟩ : syracuseStep 721667 = 1082501) B1082501
theorem B12321557 : Blo 479788 12321557 := bstep (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) B577573
theorem B721697 : Blo 479788 721697 := bstep (se 2 (by rfl) ⟨270636, by rfl⟩ : syracuseStep 721697 = 541273) B541273
theorem B721715 : Blo 479788 721715 := bstep (se 1 (by rfl) ⟨541286, by rfl⟩ : syracuseStep 721715 = 1082573) B1082573
theorem B721745 : Blo 479788 721745 := bstep (se 2 (by rfl) ⟨270654, by rfl⟩ : syracuseStep 721745 = 541309) B541309
theorem B721763 : Blo 479788 721763 := bstep (se 1 (by rfl) ⟨541322, by rfl⟩ : syracuseStep 721763 = 1082645) B1082645
theorem B721793 : Blo 479788 721793 := bstep (se 2 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 721793 = 541345) B541345
theorem B721811 : Blo 479788 721811 := bstep (se 1 (by rfl) ⟨541358, by rfl⟩ : syracuseStep 721811 = 1082717) B1082717
theorem B721841 : Blo 479788 721841 := bstep (se 2 (by rfl) ⟨270690, by rfl⟩ : syracuseStep 721841 = 541381) B541381
theorem B721859 : Blo 479788 721859 := bstep (se 1 (by rfl) ⟨541394, by rfl⟩ : syracuseStep 721859 = 1082789) B1082789
theorem B1082321 : Blo 479788 1082321 := bstep (se 2 (by rfl) ⟨405870, by rfl⟩ : syracuseStep 1082321 = 811741) B811741
theorem B721889 : Blo 479788 721889 := bstep (se 2 (by rfl) ⟨270708, by rfl⟩ : syracuseStep 721889 = 541417) B541417
theorem B1082339 : Blo 479788 1082339 := bstep (se 1 (by rfl) ⟨811754, by rfl⟩ : syracuseStep 1082339 = 1623509) B1623509
theorem B1836017 : Blo 479788 1836017 := bstep (se 2 (by rfl) ⟨688506, by rfl⟩ : syracuseStep 1836017 = 1377013) B1377013
theorem B721907 : Blo 479788 721907 := bstep (se 1 (by rfl) ⟨541430, by rfl⟩ : syracuseStep 721907 = 1082861) B1082861
theorem B721937 : Blo 479788 721937 := bstep (se 2 (by rfl) ⟨270726, by rfl⟩ : syracuseStep 721937 = 541453) B541453
theorem B721955 : Blo 479788 721955 := bstep (se 1 (by rfl) ⟨541466, by rfl⟩ : syracuseStep 721955 = 1082933) B1082933
theorem B721985 : Blo 479788 721985 := bstep (se 2 (by rfl) ⟨270744, by rfl⟩ : syracuseStep 721985 = 541489) B541489
theorem B722003 : Blo 479788 722003 := bstep (se 1 (by rfl) ⟨541502, by rfl⟩ : syracuseStep 722003 = 1083005) B1083005
theorem B722033 : Blo 479788 722033 := bstep (se 2 (by rfl) ⟨270762, by rfl⟩ : syracuseStep 722033 = 541525) B541525
theorem B722051 : Blo 479788 722051 := bstep (se 1 (by rfl) ⟨541538, by rfl⟩ : syracuseStep 722051 = 1083077) B1083077
theorem B4392077 : Blo 479788 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B722081 : Blo 479788 722081 := bstep (se 2 (by rfl) ⟨270780, by rfl⟩ : syracuseStep 722081 = 541561) B541561
theorem B722099 : Blo 479788 722099 := bstep (se 1 (by rfl) ⟨541574, by rfl⟩ : syracuseStep 722099 = 1083149) B1083149
theorem B722129 : Blo 479788 722129 := bstep (se 2 (by rfl) ⟨270798, by rfl⟩ : syracuseStep 722129 = 541597) B541597
theorem B722147 : Blo 479788 722147 := bstep (se 1 (by rfl) ⟨541610, by rfl⟩ : syracuseStep 722147 = 1083221) B1083221
theorem B1082609 : Blo 479788 1082609 := bstep (se 2 (by rfl) ⟨405978, by rfl⟩ : syracuseStep 1082609 = 811957) B811957
theorem B722177 : Blo 479788 722177 := bstep (se 2 (by rfl) ⟨270816, by rfl⟩ : syracuseStep 722177 = 541633) B541633
theorem B1082627 : Blo 479788 1082627 := bstep (se 1 (by rfl) ⟨811970, by rfl⟩ : syracuseStep 1082627 = 1623941) B1623941
theorem B2753797 : Blo 479788 2753797 := bstep (se 4 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 2753797 = 516337) B516337
theorem B722195 : Blo 479788 722195 := bstep (se 1 (by rfl) ⟨541646, by rfl⟩ : syracuseStep 722195 = 1083293) B1083293
theorem B1541425 : Blo 479788 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B722225 : Blo 479788 722225 := bstep (se 2 (by rfl) ⟨270834, by rfl⟩ : syracuseStep 722225 = 541669) B541669
theorem B5276981 : Blo 479788 5276981 := bstep (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) B494717
theorem B722243 : Blo 479788 722243 := bstep (se 1 (by rfl) ⟨541682, by rfl⟩ : syracuseStep 722243 = 1083365) B1083365
theorem B722273 : Blo 479788 722273 := bstep (se 2 (by rfl) ⟨270852, by rfl⟩ : syracuseStep 722273 = 541705) B541705
theorem B722291 : Blo 479788 722291 := bstep (se 1 (by rfl) ⟨541718, by rfl⟩ : syracuseStep 722291 = 1083437) B1083437
theorem B722321 : Blo 479788 722321 := bstep (se 2 (by rfl) ⟨270870, by rfl⟩ : syracuseStep 722321 = 541741) B541741
theorem B722339 : Blo 479788 722339 := bstep (se 1 (by rfl) ⟨541754, by rfl⟩ : syracuseStep 722339 = 1083509) B1083509
theorem B722369 : Blo 479788 722369 := bstep (se 2 (by rfl) ⟨270888, by rfl⟩ : syracuseStep 722369 = 541777) B541777
theorem B722387 : Blo 479788 722387 := bstep (se 1 (by rfl) ⟨541790, by rfl⟩ : syracuseStep 722387 = 1083581) B1083581
theorem B722417 : Blo 479788 722417 := bstep (se 2 (by rfl) ⟨270906, by rfl⟩ : syracuseStep 722417 = 541813) B541813
theorem B722435 : Blo 479788 722435 := bstep (se 1 (by rfl) ⟨541826, by rfl⟩ : syracuseStep 722435 = 1083653) B1083653
theorem B1082897 : Blo 479788 1082897 := bstep (se 2 (by rfl) ⟨406086, by rfl⟩ : syracuseStep 1082897 = 812173) B812173
theorem B722465 : Blo 479788 722465 := bstep (se 2 (by rfl) ⟨270924, by rfl⟩ : syracuseStep 722465 = 541849) B541849
theorem B1082915 : Blo 479788 1082915 := bstep (se 1 (by rfl) ⟨812186, by rfl⟩ : syracuseStep 1082915 = 1624373) B1624373
theorem B722483 : Blo 479788 722483 := bstep (se 1 (by rfl) ⟨541862, by rfl⟩ : syracuseStep 722483 = 1083725) B1083725
theorem B722513 : Blo 479788 722513 := bstep (se 2 (by rfl) ⟨270942, by rfl⟩ : syracuseStep 722513 = 541885) B541885
theorem B722531 : Blo 479788 722531 := bstep (se 1 (by rfl) ⟨541898, by rfl⟩ : syracuseStep 722531 = 1083797) B1083797
theorem B722561 : Blo 479788 722561 := bstep (se 2 (by rfl) ⟨270960, by rfl⟩ : syracuseStep 722561 = 541921) B541921
theorem B722579 : Blo 479788 722579 := bstep (se 1 (by rfl) ⟨541934, by rfl⟩ : syracuseStep 722579 = 1083869) B1083869
theorem B722609 : Blo 479788 722609 := bstep (se 2 (by rfl) ⟨270978, by rfl⟩ : syracuseStep 722609 = 541957) B541957
theorem B722627 : Blo 479788 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B722657 : Blo 479788 722657 := bstep (se 2 (by rfl) ⟨270996, by rfl⟩ : syracuseStep 722657 = 541993) B541993
theorem B722675 : Blo 479788 722675 := bstep (se 1 (by rfl) ⟨542006, by rfl⟩ : syracuseStep 722675 = 1084013) B1084013
theorem B722705 : Blo 479788 722705 := bstep (se 2 (by rfl) ⟨271014, by rfl⟩ : syracuseStep 722705 = 542029) B542029
theorem B722723 : Blo 479788 722723 := bstep (se 1 (by rfl) ⟨542042, by rfl⟩ : syracuseStep 722723 = 1084085) B1084085
theorem B1083185 : Blo 479788 1083185 := bstep (se 2 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 1083185 = 812389) B812389
theorem B722753 : Blo 479788 722753 := bstep (se 2 (by rfl) ⟨271032, by rfl⟩ : syracuseStep 722753 = 542065) B542065
theorem B1083203 : Blo 479788 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B722771 : Blo 479788 722771 := bstep (se 1 (by rfl) ⟨542078, by rfl⟩ : syracuseStep 722771 = 1084157) B1084157
theorem B722801 : Blo 479788 722801 := bstep (se 2 (by rfl) ⟨271050, by rfl⟩ : syracuseStep 722801 = 542101) B542101
theorem B722819 : Blo 479788 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B722849 : Blo 479788 722849 := bstep (se 2 (by rfl) ⟨271068, by rfl⟩ : syracuseStep 722849 = 542137) B542137
theorem B722867 : Blo 479788 722867 := bstep (se 1 (by rfl) ⟨542150, by rfl⟩ : syracuseStep 722867 = 1084301) B1084301
theorem B11241413 : Blo 479788 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B722897 : Blo 479788 722897 := bstep (se 2 (by rfl) ⟨271086, by rfl⟩ : syracuseStep 722897 = 542173) B542173
theorem B722915 : Blo 479788 722915 := bstep (se 1 (by rfl) ⟨542186, by rfl⟩ : syracuseStep 722915 = 1084373) B1084373
theorem B722945 : Blo 479788 722945 := bstep (se 2 (by rfl) ⟨271104, by rfl⟩ : syracuseStep 722945 = 542209) B542209
theorem B722963 : Blo 479788 722963 := bstep (se 1 (by rfl) ⟨542222, by rfl⟩ : syracuseStep 722963 = 1084445) B1084445
theorem B722993 : Blo 479788 722993 := bstep (se 2 (by rfl) ⟨271122, by rfl⟩ : syracuseStep 722993 = 542245) B542245
theorem B723011 : Blo 479788 723011 := bstep (se 1 (by rfl) ⟨542258, by rfl⟩ : syracuseStep 723011 = 1084517) B1084517
theorem B1083473 : Blo 479788 1083473 := bstep (se 2 (by rfl) ⟨406302, by rfl⟩ : syracuseStep 1083473 = 812605) B812605
theorem B723041 : Blo 479788 723041 := bstep (se 2 (by rfl) ⟨271140, by rfl⟩ : syracuseStep 723041 = 542281) B542281
theorem B1083491 : Blo 479788 1083491 := bstep (se 1 (by rfl) ⟨812618, by rfl⟩ : syracuseStep 1083491 = 1625237) B1625237
theorem B723059 : Blo 479788 723059 := bstep (se 1 (by rfl) ⟨542294, by rfl⟩ : syracuseStep 723059 = 1084589) B1084589
theorem B723089 : Blo 479788 723089 := bstep (se 2 (by rfl) ⟨271158, by rfl⟩ : syracuseStep 723089 = 542317) B542317
theorem B723107 : Blo 479788 723107 := bstep (se 1 (by rfl) ⟨542330, by rfl⟩ : syracuseStep 723107 = 1084661) B1084661
theorem B1673389 : Blo 479788 1673389 := bstep (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) B627521
theorem B723137 : Blo 479788 723137 := bstep (se 2 (by rfl) ⟨271176, by rfl⟩ : syracuseStep 723137 = 542353) B542353
theorem B723155 : Blo 479788 723155 := bstep (se 1 (by rfl) ⟨542366, by rfl⟩ : syracuseStep 723155 = 1084733) B1084733
theorem B723185 : Blo 479788 723185 := bstep (se 2 (by rfl) ⟨271194, by rfl⟩ : syracuseStep 723185 = 542389) B542389
theorem B723203 : Blo 479788 723203 := bstep (se 1 (by rfl) ⟨542402, by rfl⟩ : syracuseStep 723203 = 1084805) B1084805
theorem B10455317 : Blo 479788 10455317 := bstep (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) B490093
theorem B723233 : Blo 479788 723233 := bstep (se 2 (by rfl) ⟨271212, by rfl⟩ : syracuseStep 723233 = 542425) B542425
theorem B723251 : Blo 479788 723251 := bstep (se 1 (by rfl) ⟨542438, by rfl⟩ : syracuseStep 723251 = 1084877) B1084877
theorem B723281 : Blo 479788 723281 := bstep (se 2 (by rfl) ⟨271230, by rfl⟩ : syracuseStep 723281 = 542461) B542461
theorem B723299 : Blo 479788 723299 := bstep (se 1 (by rfl) ⟨542474, by rfl⟩ : syracuseStep 723299 = 1084949) B1084949
theorem B1083761 : Blo 479788 1083761 := bstep (se 2 (by rfl) ⟨406410, by rfl⟩ : syracuseStep 1083761 = 812821) B812821
theorem B723329 : Blo 479788 723329 := bstep (se 2 (by rfl) ⟨271248, by rfl⟩ : syracuseStep 723329 = 542497) B542497
theorem B1083779 : Blo 479788 1083779 := bstep (se 1 (by rfl) ⟨812834, by rfl⟩ : syracuseStep 1083779 = 1625669) B1625669
theorem B723347 : Blo 479788 723347 := bstep (se 1 (by rfl) ⟨542510, by rfl⟩ : syracuseStep 723347 = 1085021) B1085021
theorem B723377 : Blo 479788 723377 := bstep (se 2 (by rfl) ⟨271266, by rfl⟩ : syracuseStep 723377 = 542533) B542533
theorem B723395 : Blo 479788 723395 := bstep (se 1 (by rfl) ⟨542546, by rfl⟩ : syracuseStep 723395 = 1085093) B1085093
theorem B723425 : Blo 479788 723425 := bstep (se 2 (by rfl) ⟨271284, by rfl⟩ : syracuseStep 723425 = 542569) B542569
theorem B723443 : Blo 479788 723443 := bstep (se 1 (by rfl) ⟨542582, by rfl⟩ : syracuseStep 723443 = 1085165) B1085165
theorem B723473 : Blo 479788 723473 := bstep (se 2 (by rfl) ⟨271302, by rfl⟩ : syracuseStep 723473 = 542605) B542605
theorem B723491 : Blo 479788 723491 := bstep (se 1 (by rfl) ⟨542618, by rfl⟩ : syracuseStep 723491 = 1085237) B1085237
theorem B723521 : Blo 479788 723521 := bstep (se 2 (by rfl) ⟨271320, by rfl⟩ : syracuseStep 723521 = 542641) B542641
theorem B723539 : Blo 479788 723539 := bstep (se 1 (by rfl) ⟨542654, by rfl⟩ : syracuseStep 723539 = 1085309) B1085309
theorem B723569 : Blo 479788 723569 := bstep (se 2 (by rfl) ⟨271338, by rfl⟩ : syracuseStep 723569 = 542677) B542677
theorem B723587 : Blo 479788 723587 := bstep (se 1 (by rfl) ⟨542690, by rfl⟩ : syracuseStep 723587 = 1085381) B1085381
theorem B1215121 : Blo 479788 1215121 := bstep (se 2 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 1215121 = 911341) B911341
theorem B1084049 : Blo 479788 1084049 := bstep (se 2 (by rfl) ⟨406518, by rfl⟩ : syracuseStep 1084049 = 813037) B813037
theorem B723617 : Blo 479788 723617 := bstep (se 2 (by rfl) ⟨271356, by rfl⟩ : syracuseStep 723617 = 542713) B542713
theorem B1084067 : Blo 479788 1084067 := bstep (se 1 (by rfl) ⟨813050, by rfl⟩ : syracuseStep 1084067 = 1626101) B1626101
theorem B723635 : Blo 479788 723635 := bstep (se 1 (by rfl) ⟨542726, by rfl⟩ : syracuseStep 723635 = 1085453) B1085453
theorem B723665 : Blo 479788 723665 := bstep (se 2 (by rfl) ⟨271374, by rfl⟩ : syracuseStep 723665 = 542749) B542749
theorem B723683 : Blo 479788 723683 := bstep (se 1 (by rfl) ⟨542762, by rfl⟩ : syracuseStep 723683 = 1085525) B1085525
theorem B723713 : Blo 479788 723713 := bstep (se 2 (by rfl) ⟨271392, by rfl⟩ : syracuseStep 723713 = 542785) B542785
theorem B723731 : Blo 479788 723731 := bstep (se 1 (by rfl) ⟨542798, by rfl⟩ : syracuseStep 723731 = 1085597) B1085597
theorem B723761 : Blo 479788 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B723779 : Blo 479788 723779 := bstep (se 1 (by rfl) ⟨542834, by rfl⟩ : syracuseStep 723779 = 1085669) B1085669
theorem B1542989 : Blo 479788 1542989 := bstep (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) B578621
theorem B723809 : Blo 479788 723809 := bstep (se 2 (by rfl) ⟨271428, by rfl⟩ : syracuseStep 723809 = 542857) B542857
theorem B723827 : Blo 479788 723827 := bstep (se 1 (by rfl) ⟨542870, by rfl⟩ : syracuseStep 723827 = 1085741) B1085741
theorem B723857 : Blo 479788 723857 := bstep (se 2 (by rfl) ⟨271446, by rfl⟩ : syracuseStep 723857 = 542893) B542893
theorem B1215395 : Blo 479788 1215395 := bstep (se 1 (by rfl) ⟨911546, by rfl⟩ : syracuseStep 1215395 = 1823093) B1823093
theorem B723875 : Blo 479788 723875 := bstep (se 1 (by rfl) ⟨542906, by rfl⟩ : syracuseStep 723875 = 1085813) B1085813
theorem B1084337 : Blo 479788 1084337 := bstep (se 2 (by rfl) ⟨406626, by rfl⟩ : syracuseStep 1084337 = 813253) B813253
theorem B723905 : Blo 479788 723905 := bstep (se 2 (by rfl) ⟨271464, by rfl⟩ : syracuseStep 723905 = 542929) B542929
theorem B1084355 : Blo 479788 1084355 := bstep (se 1 (by rfl) ⟨813266, by rfl⟩ : syracuseStep 1084355 = 1626533) B1626533
theorem B723923 : Blo 479788 723923 := bstep (se 1 (by rfl) ⟨542942, by rfl⟩ : syracuseStep 723923 = 1085885) B1085885
theorem B723953 : Blo 479788 723953 := bstep (se 2 (by rfl) ⟨271482, by rfl⟩ : syracuseStep 723953 = 542965) B542965
theorem B723971 : Blo 479788 723971 := bstep (se 1 (by rfl) ⟨542978, by rfl⟩ : syracuseStep 723971 = 1085957) B1085957
theorem B724001 : Blo 479788 724001 := bstep (se 2 (by rfl) ⟨271500, by rfl⟩ : syracuseStep 724001 = 543001) B543001
theorem B724019 : Blo 479788 724019 := bstep (se 1 (by rfl) ⟨543014, by rfl⟩ : syracuseStep 724019 = 1086029) B1086029
theorem B724049 : Blo 479788 724049 := bstep (se 2 (by rfl) ⟨271518, by rfl⟩ : syracuseStep 724049 = 543037) B543037
theorem B1215587 : Blo 479788 1215587 := bstep (se 1 (by rfl) ⟨911690, by rfl⟩ : syracuseStep 1215587 = 1823381) B1823381
theorem B724067 : Blo 479788 724067 := bstep (se 1 (by rfl) ⟨543050, by rfl⟩ : syracuseStep 724067 = 1086101) B1086101
theorem B3673187 : Blo 479788 3673187 := bstep (se 1 (by rfl) ⟨2754890, by rfl⟩ : syracuseStep 3673187 = 5509781) B5509781
theorem B724097 : Blo 479788 724097 := bstep (se 2 (by rfl) ⟨271536, by rfl⟩ : syracuseStep 724097 = 543073) B543073
theorem B724115 : Blo 479788 724115 := bstep (se 1 (by rfl) ⟨543086, by rfl⟩ : syracuseStep 724115 = 1086173) B1086173
theorem B724145 : Blo 479788 724145 := bstep (se 2 (by rfl) ⟨271554, by rfl⟩ : syracuseStep 724145 = 543109) B543109
theorem B1641667 : Blo 479788 1641667 := bstep (se 1 (by rfl) ⟨1231250, by rfl⟩ : syracuseStep 1641667 = 2462501) B2462501
theorem B724163 : Blo 479788 724163 := bstep (se 1 (by rfl) ⟨543122, by rfl⟩ : syracuseStep 724163 = 1086245) B1086245
theorem B1084625 : Blo 479788 1084625 := bstep (se 2 (by rfl) ⟨406734, by rfl⟩ : syracuseStep 1084625 = 813469) B813469
theorem B724193 : Blo 479788 724193 := bstep (se 2 (by rfl) ⟨271572, by rfl⟩ : syracuseStep 724193 = 543145) B543145
theorem B1084643 : Blo 479788 1084643 := bstep (se 1 (by rfl) ⟨813482, by rfl⟩ : syracuseStep 1084643 = 1626965) B1626965
theorem B5508323 : Blo 479788 5508323 := bstep (se 1 (by rfl) ⟨4131242, by rfl⟩ : syracuseStep 5508323 = 8262485) B8262485
theorem B5573873 : Blo 479788 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B724211 : Blo 479788 724211 := bstep (se 1 (by rfl) ⟨543158, by rfl⟩ : syracuseStep 724211 = 1086317) B1086317
theorem B724241 : Blo 479788 724241 := bstep (se 2 (by rfl) ⟨271590, by rfl⟩ : syracuseStep 724241 = 543181) B543181
theorem B724259 : Blo 479788 724259 := bstep (se 1 (by rfl) ⟨543194, by rfl⟩ : syracuseStep 724259 = 1086389) B1086389
theorem B724289 : Blo 479788 724289 := bstep (se 2 (by rfl) ⟨271608, by rfl⟩ : syracuseStep 724289 = 543217) B543217
theorem B724307 : Blo 479788 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B724337 : Blo 479788 724337 := bstep (se 2 (by rfl) ⟨271626, by rfl⟩ : syracuseStep 724337 = 543253) B543253
theorem B724355 : Blo 479788 724355 := bstep (se 1 (by rfl) ⟨543266, by rfl⟩ : syracuseStep 724355 = 1086533) B1086533
theorem B724385 : Blo 479788 724385 := bstep (se 2 (by rfl) ⟨271644, by rfl⟩ : syracuseStep 724385 = 543289) B543289
theorem B724403 : Blo 479788 724403 := bstep (se 1 (by rfl) ⟨543302, by rfl⟩ : syracuseStep 724403 = 1086605) B1086605
theorem B6196661 : Blo 479788 6196661 := bstep (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) B580937
theorem B724433 : Blo 479788 724433 := bstep (se 2 (by rfl) ⟨271662, by rfl⟩ : syracuseStep 724433 = 543325) B543325
theorem B724451 : Blo 479788 724451 := bstep (se 1 (by rfl) ⟨543338, by rfl⟩ : syracuseStep 724451 = 1086677) B1086677
theorem B1084913 : Blo 479788 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B724481 : Blo 479788 724481 := bstep (se 2 (by rfl) ⟨271680, by rfl⟩ : syracuseStep 724481 = 543361) B543361
theorem B1084931 : Blo 479788 1084931 := bstep (se 1 (by rfl) ⟨813698, by rfl⟩ : syracuseStep 1084931 = 1627397) B1627397
theorem B724499 : Blo 479788 724499 := bstep (se 1 (by rfl) ⟨543374, by rfl⟩ : syracuseStep 724499 = 1086749) B1086749
theorem B724529 : Blo 479788 724529 := bstep (se 2 (by rfl) ⟨271698, by rfl⟩ : syracuseStep 724529 = 543397) B543397
theorem B724547 : Blo 479788 724547 := bstep (se 1 (by rfl) ⟨543410, by rfl⟩ : syracuseStep 724547 = 1086821) B1086821
theorem B724577 : Blo 479788 724577 := bstep (se 2 (by rfl) ⟨271716, by rfl⟩ : syracuseStep 724577 = 543433) B543433
theorem B4689521 : Blo 479788 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B724595 : Blo 479788 724595 := bstep (se 1 (by rfl) ⟨543446, by rfl⟩ : syracuseStep 724595 = 1086893) B1086893
theorem B724625 : Blo 479788 724625 := bstep (se 2 (by rfl) ⟨271734, by rfl⟩ : syracuseStep 724625 = 543469) B543469
theorem B724643 : Blo 479788 724643 := bstep (se 1 (by rfl) ⟨543482, by rfl⟩ : syracuseStep 724643 = 1086965) B1086965
theorem B724673 : Blo 479788 724673 := bstep (se 2 (by rfl) ⟨271752, by rfl⟩ : syracuseStep 724673 = 543505) B543505
theorem B724691 : Blo 479788 724691 := bstep (se 1 (by rfl) ⟨543518, by rfl⟩ : syracuseStep 724691 = 1087037) B1087037
theorem B724721 : Blo 479788 724721 := bstep (se 2 (by rfl) ⟨271770, by rfl⟩ : syracuseStep 724721 = 543541) B543541
theorem B724739 : Blo 479788 724739 := bstep (se 1 (by rfl) ⟨543554, by rfl⟩ : syracuseStep 724739 = 1087109) B1087109
theorem B1085201 : Blo 479788 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B724769 : Blo 479788 724769 := bstep (se 2 (by rfl) ⟨271788, by rfl⟩ : syracuseStep 724769 = 543577) B543577
theorem B1085219 : Blo 479788 1085219 := bstep (se 1 (by rfl) ⟨813914, by rfl⟩ : syracuseStep 1085219 = 1627829) B1627829
theorem B724787 : Blo 479788 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B724817 : Blo 479788 724817 := bstep (se 2 (by rfl) ⟨271806, by rfl⟩ : syracuseStep 724817 = 543613) B543613
theorem B724835 : Blo 479788 724835 := bstep (se 1 (by rfl) ⟨543626, by rfl⟩ : syracuseStep 724835 = 1087253) B1087253
theorem B724865 : Blo 479788 724865 := bstep (se 2 (by rfl) ⟨271824, by rfl⟩ : syracuseStep 724865 = 543649) B543649
theorem B724883 : Blo 479788 724883 := bstep (se 1 (by rfl) ⟨543662, by rfl⟩ : syracuseStep 724883 = 1087325) B1087325
theorem B724913 : Blo 479788 724913 := bstep (se 2 (by rfl) ⟨271842, by rfl⟩ : syracuseStep 724913 = 543685) B543685
theorem B724931 : Blo 479788 724931 := bstep (se 1 (by rfl) ⟨543698, by rfl⟩ : syracuseStep 724931 = 1087397) B1087397
theorem B724961 : Blo 479788 724961 := bstep (se 2 (by rfl) ⟨271860, by rfl⟩ : syracuseStep 724961 = 543721) B543721
theorem B724979 : Blo 479788 724979 := bstep (se 1 (by rfl) ⟨543734, by rfl⟩ : syracuseStep 724979 = 1087469) B1087469
theorem B1216529 : Blo 479788 1216529 := bstep (se 2 (by rfl) ⟨456198, by rfl⟩ : syracuseStep 1216529 = 912397) B912397
theorem B725009 : Blo 479788 725009 := bstep (se 2 (by rfl) ⟨271878, by rfl⟩ : syracuseStep 725009 = 543757) B543757
theorem B725027 : Blo 479788 725027 := bstep (se 1 (by rfl) ⟨543770, by rfl⟩ : syracuseStep 725027 = 1087541) B1087541
theorem B1085489 : Blo 479788 1085489 := bstep (se 2 (by rfl) ⟨407058, by rfl⟩ : syracuseStep 1085489 = 814117) B814117
theorem B725057 : Blo 479788 725057 := bstep (se 2 (by rfl) ⟨271896, by rfl⟩ : syracuseStep 725057 = 543793) B543793
theorem B1216579 : Blo 479788 1216579 := bstep (se 1 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 1216579 = 1824869) B1824869
theorem B1085507 : Blo 479788 1085507 := bstep (se 1 (by rfl) ⟨814130, by rfl⟩ : syracuseStep 1085507 = 1628261) B1628261
theorem B725075 : Blo 479788 725075 := bstep (se 1 (by rfl) ⟨543806, by rfl⟩ : syracuseStep 725075 = 1087613) B1087613
theorem B2429027 : Blo 479788 2429027 := bstep (se 1 (by rfl) ⟨1821770, by rfl⟩ : syracuseStep 2429027 = 3643541) B3643541
theorem B725105 : Blo 479788 725105 := bstep (se 2 (by rfl) ⟨271914, by rfl⟩ : syracuseStep 725105 = 543829) B543829
theorem B725123 : Blo 479788 725123 := bstep (se 1 (by rfl) ⟨543842, by rfl⟩ : syracuseStep 725123 = 1087685) B1087685
theorem B725153 : Blo 479788 725153 := bstep (se 2 (by rfl) ⟨271932, by rfl⟩ : syracuseStep 725153 = 543865) B543865
theorem B725171 : Blo 479788 725171 := bstep (se 1 (by rfl) ⟨543878, by rfl⟩ : syracuseStep 725171 = 1087757) B1087757
theorem B1216721 : Blo 479788 1216721 := bstep (se 2 (by rfl) ⟨456270, by rfl⟩ : syracuseStep 1216721 = 912541) B912541
theorem B725201 : Blo 479788 725201 := bstep (se 2 (by rfl) ⟨271950, by rfl⟩ : syracuseStep 725201 = 543901) B543901
theorem B6918371 : Blo 479788 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B659683 : Blo 479788 659683 := bstep (se 1 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 659683 = 989525) B989525
theorem B725219 : Blo 479788 725219 := bstep (se 1 (by rfl) ⟨543914, by rfl⟩ : syracuseStep 725219 = 1087829) B1087829
theorem B725249 : Blo 479788 725249 := bstep (se 2 (by rfl) ⟨271968, by rfl⟩ : syracuseStep 725249 = 543937) B543937
theorem B725267 : Blo 479788 725267 := bstep (se 1 (by rfl) ⟨543950, by rfl⟩ : syracuseStep 725267 = 1087901) B1087901
theorem B725297 : Blo 479788 725297 := bstep (se 2 (by rfl) ⟨271986, by rfl⟩ : syracuseStep 725297 = 543973) B543973
theorem B725315 : Blo 479788 725315 := bstep (se 1 (by rfl) ⟨543986, by rfl⟩ : syracuseStep 725315 = 1087973) B1087973
theorem B1085777 : Blo 479788 1085777 := bstep (se 2 (by rfl) ⟨407166, by rfl⟩ : syracuseStep 1085777 = 814333) B814333
theorem B725345 : Blo 479788 725345 := bstep (se 2 (by rfl) ⟨272004, by rfl⟩ : syracuseStep 725345 = 544009) B544009
theorem B1085795 : Blo 479788 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B856433 : Blo 479788 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B725363 : Blo 479788 725363 := bstep (se 1 (by rfl) ⟨544022, by rfl⟩ : syracuseStep 725363 = 1088045) B1088045
theorem B725393 : Blo 479788 725393 := bstep (se 2 (by rfl) ⟨272022, by rfl⟩ : syracuseStep 725393 = 544045) B544045
theorem B725411 : Blo 479788 725411 := bstep (se 1 (by rfl) ⟨544058, by rfl⟩ : syracuseStep 725411 = 1088117) B1088117
theorem B725441 : Blo 479788 725441 := bstep (se 2 (by rfl) ⟨272040, by rfl⟩ : syracuseStep 725441 = 544081) B544081
theorem B3084749 : Blo 479788 3084749 := bstep (se 3 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 3084749 = 1156781) B1156781
theorem B725459 : Blo 479788 725459 := bstep (se 1 (by rfl) ⟨544094, by rfl⟩ : syracuseStep 725459 = 1088189) B1088189
theorem B725489 : Blo 479788 725489 := bstep (se 2 (by rfl) ⟨272058, by rfl⟩ : syracuseStep 725489 = 544117) B544117
theorem B627187 : Blo 479788 627187 := bstep (se 1 (by rfl) ⟨470390, by rfl⟩ : syracuseStep 627187 = 940781) B940781
theorem B725507 : Blo 479788 725507 := bstep (se 1 (by rfl) ⟨544130, by rfl⟩ : syracuseStep 725507 = 1088261) B1088261
theorem B2789893 : Blo 479788 2789893 := bstep (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) B523105
theorem B725537 : Blo 479788 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B725555 : Blo 479788 725555 := bstep (se 1 (by rfl) ⟨544166, by rfl⟩ : syracuseStep 725555 = 1088333) B1088333
theorem B30511669 : Blo 479788 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B725585 : Blo 479788 725585 := bstep (se 2 (by rfl) ⟨272094, by rfl⟩ : syracuseStep 725585 = 544189) B544189
theorem B725603 : Blo 479788 725603 := bstep (se 1 (by rfl) ⟨544202, by rfl⟩ : syracuseStep 725603 = 1088405) B1088405
theorem B1086065 : Blo 479788 1086065 := bstep (se 2 (by rfl) ⟨407274, by rfl⟩ : syracuseStep 1086065 = 814549) B814549
theorem B725633 : Blo 479788 725633 := bstep (se 2 (by rfl) ⟨272112, by rfl⟩ : syracuseStep 725633 = 544225) B544225
theorem B1086083 : Blo 479788 1086083 := bstep (se 1 (by rfl) ⟨814562, by rfl⟩ : syracuseStep 1086083 = 1629125) B1629125
theorem B725651 : Blo 479788 725651 := bstep (se 1 (by rfl) ⟨544238, by rfl⟩ : syracuseStep 725651 = 1088477) B1088477
theorem B725681 : Blo 479788 725681 := bstep (se 2 (by rfl) ⟨272130, by rfl⟩ : syracuseStep 725681 = 544261) B544261
theorem B2429837 : Blo 479788 2429837 := bstep (se 3 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 2429837 = 911189) B911189
theorem B1086353 : Blo 479788 1086353 := bstep (se 2 (by rfl) ⟨407382, by rfl⟩ : syracuseStep 1086353 = 814765) B814765
theorem B1086371 : Blo 479788 1086371 := bstep (se 1 (by rfl) ⟨814778, by rfl⟩ : syracuseStep 1086371 = 1629557) B1629557
theorem B1217713 : Blo 479788 1217713 := bstep (se 2 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 1217713 = 913285) B913285
theorem B1086641 : Blo 479788 1086641 := bstep (se 2 (by rfl) ⟨407490, by rfl⟩ : syracuseStep 1086641 = 814981) B814981
theorem B1086659 : Blo 479788 1086659 := bstep (se 1 (by rfl) ⟨814994, by rfl⟩ : syracuseStep 1086659 = 1629989) B1629989
theorem B1545475 : Blo 479788 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B12719501 : Blo 479788 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1545617 : Blo 479788 1545617 := bstep (se 2 (by rfl) ⟨579606, by rfl⟩ : syracuseStep 1545617 = 1159213) B1159213
theorem B1217987 : Blo 479788 1217987 := bstep (se 1 (by rfl) ⟨913490, by rfl⟩ : syracuseStep 1217987 = 1826981) B1826981
theorem B1086929 : Blo 479788 1086929 := bstep (se 2 (by rfl) ⟨407598, by rfl⟩ : syracuseStep 1086929 = 815197) B815197
theorem B1086947 : Blo 479788 1086947 := bstep (se 1 (by rfl) ⟨815210, by rfl⟩ : syracuseStep 1086947 = 1630421) B1630421
theorem B1545731 : Blo 479788 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B1218179 : Blo 479788 1218179 := bstep (se 1 (by rfl) ⟨913634, by rfl⟩ : syracuseStep 1218179 = 1827269) B1827269
theorem B1316525 : Blo 479788 1316525 := bstep (se 3 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 1316525 = 493697) B493697
theorem B1087217 : Blo 479788 1087217 := bstep (se 2 (by rfl) ⟨407706, by rfl⟩ : syracuseStep 1087217 = 815413) B815413
theorem B1087235 : Blo 479788 1087235 := bstep (se 1 (by rfl) ⟨815426, by rfl⟩ : syracuseStep 1087235 = 1630853) B1630853
theorem B1742755 : Blo 479788 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B1087505 : Blo 479788 1087505 := bstep (se 2 (by rfl) ⟨407814, by rfl⟩ : syracuseStep 1087505 = 815629) B815629
theorem B1087523 : Blo 479788 1087523 := bstep (se 1 (by rfl) ⟨815642, by rfl⟩ : syracuseStep 1087523 = 1631285) B1631285
theorem B1153091 : Blo 479788 1153091 := bstep (se 1 (by rfl) ⟨864818, by rfl⟩ : syracuseStep 1153091 = 1729637) B1729637
theorem B1153187 : Blo 479788 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B1087793 : Blo 479788 1087793 := bstep (se 2 (by rfl) ⟨407922, by rfl⟩ : syracuseStep 1087793 = 815845) B815845
theorem B1087811 : Blo 479788 1087811 := bstep (se 1 (by rfl) ⟨815858, by rfl⟩ : syracuseStep 1087811 = 1631717) B1631717
theorem B1153379 : Blo 479788 1153379 := bstep (se 1 (by rfl) ⟨865034, by rfl⟩ : syracuseStep 1153379 = 1730069) B1730069
theorem B1743245 : Blo 479788 1743245 := bstep (se 3 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 1743245 = 653717) B653717
theorem B1546705 : Blo 479788 1546705 := bstep (se 2 (by rfl) ⟨580014, by rfl⟩ : syracuseStep 1546705 = 1160029) B1160029
theorem B2791907 : Blo 479788 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B1219121 : Blo 479788 1219121 := bstep (se 2 (by rfl) ⟨457170, by rfl⟩ : syracuseStep 1219121 = 914341) B914341
theorem B1088081 : Blo 479788 1088081 := bstep (se 2 (by rfl) ⟨408030, by rfl⟩ : syracuseStep 1088081 = 816061) B816061
theorem B1219171 : Blo 479788 1219171 := bstep (se 1 (by rfl) ⟨914378, by rfl⟩ : syracuseStep 1219171 = 1828757) B1828757
theorem B1088099 : Blo 479788 1088099 := bstep (se 1 (by rfl) ⟨816074, by rfl⟩ : syracuseStep 1088099 = 1632149) B1632149
theorem B2595491 : Blo 479788 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B1219313 : Blo 479788 1219313 := bstep (se 2 (by rfl) ⟨457242, by rfl⟩ : syracuseStep 1219313 = 914485) B914485
theorem B1088369 : Blo 479788 1088369 := bstep (se 2 (by rfl) ⟨408138, by rfl⟩ : syracuseStep 1088369 = 816277) B816277
theorem B1088387 : Blo 479788 1088387 := bstep (se 1 (by rfl) ⟨816290, by rfl⟩ : syracuseStep 1088387 = 1632581) B1632581
theorem B1154033 : Blo 479788 1154033 := bstep (se 2 (by rfl) ⟨432762, by rfl⟩ : syracuseStep 1154033 = 865525) B865525
theorem B1154321 : Blo 479788 1154321 := bstep (se 2 (by rfl) ⟨432870, by rfl⟩ : syracuseStep 1154321 = 865741) B865741
theorem B1154531 : Blo 479788 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B5283427 : Blo 479788 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B2596465 : Blo 479788 2596465 := bstep (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) B1947349
theorem B1220305 : Blo 479788 1220305 := bstep (se 2 (by rfl) ⟨457614, by rfl⟩ : syracuseStep 1220305 = 915229) B915229
theorem B2432753 : Blo 479788 2432753 := bstep (se 2 (by rfl) ⟨912282, by rfl⟩ : syracuseStep 2432753 = 1824565) B1824565
theorem B1220579 : Blo 479788 1220579 := bstep (se 1 (by rfl) ⟨915434, by rfl⟩ : syracuseStep 1220579 = 1830869) B1830869
theorem B1220771 : Blo 479788 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B926147 : Blo 479788 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B1024849 : Blo 479788 1024849 := bstep (se 2 (by rfl) ⟨384318, by rfl⟩ : syracuseStep 1024849 = 768637) B768637
theorem B730019 : Blo 479788 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B1221713 : Blo 479788 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B1221763 : Blo 479788 1221763 := bstep (se 1 (by rfl) ⟨916322, by rfl⟩ : syracuseStep 1221763 = 1832645) B1832645
theorem B2434211 : Blo 479788 2434211 := bstep (se 1 (by rfl) ⟨1825658, by rfl⟩ : syracuseStep 2434211 = 3651317) B3651317
theorem B1156369 : Blo 479788 1156369 := bstep (se 2 (by rfl) ⟨433638, by rfl⟩ : syracuseStep 1156369 = 867277) B867277
theorem B1221905 : Blo 479788 1221905 := bstep (se 2 (by rfl) ⟨458214, by rfl⟩ : syracuseStep 1221905 = 916429) B916429
theorem B12166541 : Blo 479788 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B1025635 : Blo 479788 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B2598733 : Blo 479788 2598733 := bstep (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) B974525
theorem B3647429 : Blo 479788 3647429 := bstep (se 4 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 3647429 = 683893) B683893
theorem B2435021 : Blo 479788 2435021 := bstep (se 3 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 2435021 = 913133) B913133
theorem B3090437 : Blo 479788 3090437 := bstep (se 4 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 3090437 = 579457) B579457
theorem B1222897 : Blo 479788 1222897 := bstep (se 2 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 1222897 = 917173) B917173
theorem B1026353 : Blo 479788 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B731539 : Blo 479788 731539 := bstep (se 1 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 731539 = 1097309) B1097309
theorem B1223171 : Blo 479788 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B1878563 : Blo 479788 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1223363 : Blo 479788 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B1026865 : Blo 479788 1026865 := bstep (se 2 (by rfl) ⟨385074, by rfl⟩ : syracuseStep 1026865 = 770149) B770149
theorem B732257 : Blo 479788 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B1649933 : Blo 479788 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B732451 : Blo 479788 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B5221685 : Blo 479788 5221685 := bstep (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) B489533
theorem B1224305 : Blo 479788 1224305 := bstep (se 2 (by rfl) ⟨459114, by rfl⟩ : syracuseStep 1224305 = 918229) B918229
theorem B929411 : Blo 479788 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B1224355 : Blo 479788 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B1224497 : Blo 479788 1224497 := bstep (se 2 (by rfl) ⟨459186, by rfl⟩ : syracuseStep 1224497 = 918373) B918373
theorem B1650563 : Blo 479788 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B1290289 : Blo 479788 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B3911921 : Blo 479788 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B1028369 : Blo 479788 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B1716515 : Blo 479788 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B9286001 : Blo 479788 9286001 := bstep (se 2 (by rfl) ⟨3482250, by rfl⟩ : syracuseStep 9286001 = 6964501) B6964501
theorem B864803 : Blo 479788 864803 := bstep (se 1 (by rfl) ⟨648602, by rfl⟩ : syracuseStep 864803 = 1297205) B1297205
theorem B832145 : Blo 479788 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B1028771 : Blo 479788 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B865027 : Blo 479788 865027 := bstep (se 1 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 865027 = 1297541) B1297541
theorem B2437937 : Blo 479788 2437937 := bstep (se 2 (by rfl) ⟨914226, by rfl⟩ : syracuseStep 2437937 = 1828453) B1828453
theorem B734179 : Blo 479788 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B5190641 : Blo 479788 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B8795249 : Blo 479788 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B1619405 : Blo 479788 1619405 := bstep (se 3 (by rfl) ⟨303638, by rfl⟩ : syracuseStep 1619405 = 607277) B607277
theorem B1160675 : Blo 479788 1160675 := bstep (se 1 (by rfl) ⟨870506, by rfl⟩ : syracuseStep 1160675 = 1741013) B1741013
theorem B1619459 : Blo 479788 1619459 := bstep (se 1 (by rfl) ⟨1214594, by rfl⟩ : syracuseStep 1619459 = 2429189) B2429189
theorem B1848845 : Blo 479788 1848845 := bstep (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) B693317
theorem B1029667 : Blo 479788 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B1619729 : Blo 479788 1619729 := bstep (se 2 (by rfl) ⟨607398, by rfl⟩ : syracuseStep 1619729 = 1214797) B1214797
theorem B3159971 : Blo 479788 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B16890083 : Blo 479788 16890083 := bstep (se 1 (by rfl) ⟨12667562, by rfl⟩ : syracuseStep 16890083 = 25335125) B25335125
theorem B2439395 : Blo 479788 2439395 := bstep (se 1 (by rfl) ⟨1829546, by rfl⟩ : syracuseStep 2439395 = 3659093) B3659093
theorem B833809 : Blo 479788 833809 := bstep (se 2 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 833809 = 625357) B625357
theorem B1620269 : Blo 479788 1620269 := bstep (se 3 (by rfl) ⟨303800, by rfl⟩ : syracuseStep 1620269 = 607601) B607601
theorem B1620323 : Blo 479788 1620323 := bstep (se 1 (by rfl) ⟨1215242, by rfl⟩ : syracuseStep 1620323 = 2430485) B2430485
theorem B2734661 : Blo 479788 2734661 := bstep (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) B512749
theorem B1391185 : Blo 479788 1391185 := bstep (se 2 (by rfl) ⟨521694, by rfl⟩ : syracuseStep 1391185 = 1043389) B1043389
theorem B1620593 : Blo 479788 1620593 := bstep (se 2 (by rfl) ⟨607722, by rfl⟩ : syracuseStep 1620593 = 1215445) B1215445
theorem B5880433 : Blo 479788 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B1948387 : Blo 479788 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B1030897 : Blo 479788 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B2931461 : Blo 479788 2931461 := bstep (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) B549649
theorem B6175541 : Blo 479788 6175541 := bstep (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) B578957
theorem B2931653 : Blo 479788 2931653 := bstep (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) B549685
theorem B2735117 : Blo 479788 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B2440205 : Blo 479788 2440205 := bstep (se 3 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 2440205 = 915077) B915077
theorem B1653805 : Blo 479788 1653805 := bstep (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) B620177
theorem B1162289 : Blo 479788 1162289 := bstep (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) B871717
theorem B539779 : Blo 479788 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B1621133 : Blo 479788 1621133 := bstep (se 3 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 1621133 = 607925) B607925
theorem B1621187 : Blo 479788 1621187 := bstep (se 1 (by rfl) ⟨1215890, by rfl⟩ : syracuseStep 1621187 = 2431781) B2431781
theorem B539923 : Blo 479788 539923 := bstep (se 1 (by rfl) ⟨404942, by rfl⟩ : syracuseStep 539923 = 809885) B809885
theorem B2309411 : Blo 479788 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B867715 : Blo 479788 867715 := bstep (se 1 (by rfl) ⟨650786, by rfl⟩ : syracuseStep 867715 = 1301573) B1301573
theorem B540067 : Blo 479788 540067 := bstep (se 1 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 540067 = 810101) B810101
theorem B769457 : Blo 479788 769457 := bstep (se 2 (by rfl) ⟨288546, by rfl⟩ : syracuseStep 769457 = 577093) B577093
theorem B5848517 : Blo 479788 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B1621457 : Blo 479788 1621457 := bstep (se 2 (by rfl) ⟨608046, by rfl⟩ : syracuseStep 1621457 = 1216093) B1216093
theorem B835043 : Blo 479788 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B769585 : Blo 479788 769585 := bstep (se 2 (by rfl) ⟨288594, by rfl⟩ : syracuseStep 769585 = 577189) B577189
theorem B540211 : Blo 479788 540211 := bstep (se 1 (by rfl) ⟨405158, by rfl⟩ : syracuseStep 540211 = 810317) B810317
theorem B3653261 : Blo 479788 3653261 := bstep (se 3 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 3653261 = 1369973) B1369973
theorem B540355 : Blo 479788 540355 := bstep (se 1 (by rfl) ⟨405266, by rfl⟩ : syracuseStep 540355 = 810533) B810533
theorem B540499 : Blo 479788 540499 := bstep (se 1 (by rfl) ⟨405374, by rfl⟩ : syracuseStep 540499 = 810749) B810749
theorem B2310065 : Blo 479788 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B540643 : Blo 479788 540643 := bstep (se 1 (by rfl) ⟨405482, by rfl⟩ : syracuseStep 540643 = 810965) B810965
theorem B1621997 : Blo 479788 1621997 := bstep (se 3 (by rfl) ⟨304124, by rfl⟩ : syracuseStep 1621997 = 608249) B608249
theorem B1622051 : Blo 479788 1622051 := bstep (se 1 (by rfl) ⟨1216538, by rfl⟩ : syracuseStep 1622051 = 2433077) B2433077
theorem B540787 : Blo 479788 540787 := bstep (se 1 (by rfl) ⟨405590, by rfl⟩ : syracuseStep 540787 = 811181) B811181
theorem B1032401 : Blo 479788 1032401 := bstep (se 2 (by rfl) ⟨387150, by rfl⟩ : syracuseStep 1032401 = 774301) B774301
theorem B1032419 : Blo 479788 1032419 := bstep (se 1 (by rfl) ⟨774314, by rfl⟩ : syracuseStep 1032419 = 1548629) B1548629
theorem B540931 : Blo 479788 540931 := bstep (se 1 (by rfl) ⟨405698, by rfl⟩ : syracuseStep 540931 = 811397) B811397
theorem B4112653 : Blo 479788 4112653 := bstep (se 3 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 4112653 = 1542245) B1542245
theorem B1622321 : Blo 479788 1622321 := bstep (se 2 (by rfl) ⟨608370, by rfl⟩ : syracuseStep 1622321 = 1216741) B1216741
theorem B541075 : Blo 479788 541075 := bstep (se 1 (by rfl) ⟨405806, by rfl⟩ : syracuseStep 541075 = 811613) B811613
theorem B541219 : Blo 479788 541219 := bstep (se 1 (by rfl) ⟨405914, by rfl⟩ : syracuseStep 541219 = 811829) B811829
theorem B541363 : Blo 479788 541363 := bstep (se 1 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 541363 = 812045) B812045
theorem B869123 : Blo 479788 869123 := bstep (se 1 (by rfl) ⟨651842, by rfl⟩ : syracuseStep 869123 = 1303685) B1303685
theorem B770867 : Blo 479788 770867 := bstep (se 1 (by rfl) ⟨578150, by rfl⟩ : syracuseStep 770867 = 1156301) B1156301
theorem B541507 : Blo 479788 541507 := bstep (se 1 (by rfl) ⟨406130, by rfl⟩ : syracuseStep 541507 = 812261) B812261
theorem B1622861 : Blo 479788 1622861 := bstep (se 3 (by rfl) ⟨304286, by rfl⟩ : syracuseStep 1622861 = 608573) B608573
theorem B1622915 : Blo 479788 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B770963 : Blo 479788 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B770995 : Blo 479788 770995 := bstep (se 1 (by rfl) ⟨578246, by rfl⟩ : syracuseStep 770995 = 1156493) B1156493
theorem B541651 : Blo 479788 541651 := bstep (se 1 (by rfl) ⟨406238, by rfl⟩ : syracuseStep 541651 = 812477) B812477
theorem B607267 : Blo 479788 607267 := bstep (se 1 (by rfl) ⟨455450, by rfl⟩ : syracuseStep 607267 = 910901) B910901
theorem B1098787 : Blo 479788 1098787 := bstep (se 1 (by rfl) ⟨824090, by rfl⟩ : syracuseStep 1098787 = 1648181) B1648181
theorem B541795 : Blo 479788 541795 := bstep (se 1 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 541795 = 812693) B812693
theorem B1623185 : Blo 479788 1623185 := bstep (se 2 (by rfl) ⟨608694, by rfl⟩ : syracuseStep 1623185 = 1217389) B1217389
theorem B2311409 : Blo 479788 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B541939 : Blo 479788 541939 := bstep (se 1 (by rfl) ⟨406454, by rfl⟩ : syracuseStep 541939 = 812909) B812909
theorem B2934085 : Blo 479788 2934085 := bstep (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) B550141
theorem B5850467 : Blo 479788 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B542083 : Blo 479788 542083 := bstep (se 1 (by rfl) ⟨406562, by rfl⟩ : syracuseStep 542083 = 813125) B813125
theorem B607763 : Blo 479788 607763 := bstep (se 1 (by rfl) ⟨455822, by rfl⟩ : syracuseStep 607763 = 911645) B911645
theorem B542227 : Blo 479788 542227 := bstep (se 1 (by rfl) ⟨406670, by rfl⟩ : syracuseStep 542227 = 813341) B813341
theorem B4113989 : Blo 479788 4113989 := bstep (se 4 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 4113989 = 771373) B771373
theorem B542371 : Blo 479788 542371 := bstep (se 1 (by rfl) ⟨406778, by rfl⟩ : syracuseStep 542371 = 813557) B813557
theorem B1623725 : Blo 479788 1623725 := bstep (se 3 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 1623725 = 608897) B608897
theorem B1623779 : Blo 479788 1623779 := bstep (se 1 (by rfl) ⟨1217834, by rfl⟩ : syracuseStep 1623779 = 2435669) B2435669
theorem B542515 : Blo 479788 542515 := bstep (se 1 (by rfl) ⟨406886, by rfl⟩ : syracuseStep 542515 = 813773) B813773
theorem B771905 : Blo 479788 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B2738033 : Blo 479788 2738033 := bstep (se 2 (by rfl) ⟨1026762, by rfl⟩ : syracuseStep 2738033 = 2053525) B2053525
theorem B2443121 : Blo 479788 2443121 := bstep (se 2 (by rfl) ⟨916170, by rfl⟩ : syracuseStep 2443121 = 1832341) B1832341
theorem B542659 : Blo 479788 542659 := bstep (se 1 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 542659 = 813989) B813989
theorem B1624049 : Blo 479788 1624049 := bstep (se 2 (by rfl) ⟨609018, by rfl⟩ : syracuseStep 1624049 = 1218037) B1218037
theorem B542803 : Blo 479788 542803 := bstep (se 1 (by rfl) ⟨407102, by rfl⟩ : syracuseStep 542803 = 814205) B814205
theorem B2312333 : Blo 479788 2312333 := bstep (se 3 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 2312333 = 867125) B867125
theorem B2050211 : Blo 479788 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B608467 : Blo 479788 608467 := bstep (se 1 (by rfl) ⟨456350, by rfl⟩ : syracuseStep 608467 = 912701) B912701
theorem B542947 : Blo 479788 542947 := bstep (se 1 (by rfl) ⟨407210, by rfl⟩ : syracuseStep 542947 = 814421) B814421
theorem B608563 : Blo 479788 608563 := bstep (se 1 (by rfl) ⟨456422, by rfl⟩ : syracuseStep 608563 = 912845) B912845
theorem B543091 : Blo 479788 543091 := bstep (se 1 (by rfl) ⟨407318, by rfl⟩ : syracuseStep 543091 = 814637) B814637
theorem B3656177 : Blo 479788 3656177 := bstep (se 2 (by rfl) ⟨1371066, by rfl⟩ : syracuseStep 3656177 = 2742133) B2742133
theorem B543235 : Blo 479788 543235 := bstep (se 1 (by rfl) ⟨407426, by rfl⟩ : syracuseStep 543235 = 814853) B814853
theorem B1624589 : Blo 479788 1624589 := bstep (se 3 (by rfl) ⟨304610, by rfl⟩ : syracuseStep 1624589 = 609221) B609221
theorem B1624643 : Blo 479788 1624643 := bstep (se 1 (by rfl) ⟨1218482, by rfl⟩ : syracuseStep 1624643 = 2436965) B2436965
theorem B543379 : Blo 479788 543379 := bstep (se 1 (by rfl) ⟨407534, by rfl⟩ : syracuseStep 543379 = 815069) B815069
theorem B1231537 : Blo 479788 1231537 := bstep (se 2 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 1231537 = 923653) B923653
theorem B609059 : Blo 479788 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B543523 : Blo 479788 543523 := bstep (se 1 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 543523 = 815285) B815285
theorem B1624913 : Blo 479788 1624913 := bstep (se 2 (by rfl) ⟨609342, by rfl⟩ : syracuseStep 1624913 = 1218685) B1218685
theorem B543667 : Blo 479788 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B543811 : Blo 479788 543811 := bstep (se 1 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 543811 = 815717) B815717
theorem B773219 : Blo 479788 773219 := bstep (se 1 (by rfl) ⟨579914, by rfl⟩ : syracuseStep 773219 = 1159829) B1159829
theorem B543955 : Blo 479788 543955 := bstep (se 1 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 543955 = 815933) B815933
theorem B1821923 : Blo 479788 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B1461521 : Blo 479788 1461521 := bstep (se 2 (by rfl) ⟨548070, by rfl⟩ : syracuseStep 1461521 = 1096141) B1096141
theorem B2739491 : Blo 479788 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B2444579 : Blo 479788 2444579 := bstep (se 1 (by rfl) ⟨1833434, by rfl⟩ : syracuseStep 2444579 = 3666869) B3666869
theorem B544099 : Blo 479788 544099 := bstep (se 1 (by rfl) ⟨408074, by rfl⟩ : syracuseStep 544099 = 816149) B816149
theorem B1625453 : Blo 479788 1625453 := bstep (se 3 (by rfl) ⟨304772, by rfl⟩ : syracuseStep 1625453 = 609545) B609545
theorem B1625507 : Blo 479788 1625507 := bstep (se 1 (by rfl) ⟨1219130, by rfl⟩ : syracuseStep 1625507 = 2438261) B2438261
theorem B609763 : Blo 479788 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B544243 : Blo 479788 544243 := bstep (se 1 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 544243 = 816365) B816365
theorem B609859 : Blo 479788 609859 := bstep (se 1 (by rfl) ⟨457394, by rfl⟩ : syracuseStep 609859 = 914789) B914789
theorem B2379377 : Blo 479788 2379377 := bstep (se 2 (by rfl) ⟨892266, by rfl⟩ : syracuseStep 2379377 = 1784533) B1784533
theorem B9293453 : Blo 479788 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B1625777 : Blo 479788 1625777 := bstep (se 2 (by rfl) ⟨609666, by rfl⟩ : syracuseStep 1625777 = 1219333) B1219333
theorem B773891 : Blo 479788 773891 := bstep (se 1 (by rfl) ⟨580418, by rfl⟩ : syracuseStep 773891 = 1160837) B1160837
theorem B1298243 : Blo 479788 1298243 := bstep (se 1 (by rfl) ⟨973682, by rfl⟩ : syracuseStep 1298243 = 1947365) B1947365
theorem B774193 : Blo 479788 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B610355 : Blo 479788 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B2445389 : Blo 479788 2445389 := bstep (se 3 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 2445389 = 917021) B917021
theorem B1822925 : Blo 479788 1822925 := bstep (se 3 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 1822925 = 683597) B683597
theorem B1626317 : Blo 479788 1626317 := bstep (se 3 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 1626317 = 609869) B609869
theorem B2937059 : Blo 479788 2937059 := bstep (se 1 (by rfl) ⟨2202794, by rfl⟩ : syracuseStep 2937059 = 4405589) B4405589
theorem B1626371 : Blo 479788 1626371 := bstep (se 1 (by rfl) ⟨1219778, by rfl⟩ : syracuseStep 1626371 = 2439557) B2439557
theorem B774403 : Blo 479788 774403 := bstep (se 1 (by rfl) ⟨580802, by rfl⟩ : syracuseStep 774403 = 1161605) B1161605
theorem B2740493 : Blo 479788 2740493 := bstep (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) B1027685
theorem B1954097 : Blo 479788 1954097 := bstep (se 2 (by rfl) ⟨732786, by rfl⟩ : syracuseStep 1954097 = 1465573) B1465573
theorem B774449 : Blo 479788 774449 := bstep (se 2 (by rfl) ⟨290418, by rfl⟩ : syracuseStep 774449 = 580837) B580837
theorem B2773453 : Blo 479788 2773453 := bstep (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) B1040045
theorem B1626641 : Blo 479788 1626641 := bstep (se 2 (by rfl) ⟨609990, by rfl⟩ : syracuseStep 1626641 = 1219981) B1219981
theorem B479795 : Blo 479788 479795 := bstep (se 1 (by rfl) ⟨359846, by rfl⟩ : syracuseStep 479795 = 719693) B719693
theorem B479811 : Blo 479788 479811 := bstep (se 1 (by rfl) ⟨359858, by rfl⟩ : syracuseStep 479811 = 719717) B719717
theorem B479827 : Blo 479788 479827 := bstep (se 1 (by rfl) ⟨359870, by rfl⟩ : syracuseStep 479827 = 719741) B719741
theorem B479843 : Blo 479788 479843 := bstep (se 1 (by rfl) ⟨359882, by rfl⟩ : syracuseStep 479843 = 719765) B719765
theorem B479859 : Blo 479788 479859 := bstep (se 1 (by rfl) ⟨359894, by rfl⟩ : syracuseStep 479859 = 719789) B719789
theorem B479875 : Blo 479788 479875 := bstep (se 1 (by rfl) ⟨359906, by rfl⟩ : syracuseStep 479875 = 719813) B719813
theorem B479891 : Blo 479788 479891 := bstep (se 1 (by rfl) ⟨359918, by rfl⟩ : syracuseStep 479891 = 719837) B719837
theorem B479907 : Blo 479788 479907 := bstep (se 1 (by rfl) ⟨359930, by rfl⟩ : syracuseStep 479907 = 719861) B719861
theorem B938659 : Blo 479788 938659 := bstep (se 1 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 938659 = 1407989) B1407989
theorem B479923 : Blo 479788 479923 := bstep (se 1 (by rfl) ⟨359942, by rfl⟩ : syracuseStep 479923 = 719885) B719885
theorem B578227 : Blo 479788 578227 := bstep (se 1 (by rfl) ⟨433670, by rfl⟩ : syracuseStep 578227 = 867341) B867341
theorem B479939 : Blo 479788 479939 := bstep (se 1 (by rfl) ⟨359954, by rfl⟩ : syracuseStep 479939 = 719909) B719909
theorem B479955 : Blo 479788 479955 := bstep (se 1 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 479955 = 719933) B719933
theorem B479971 : Blo 479788 479971 := bstep (se 1 (by rfl) ⟨359978, by rfl⟩ : syracuseStep 479971 = 719957) B719957
theorem B479987 : Blo 479788 479987 := bstep (se 1 (by rfl) ⟨359990, by rfl⟩ : syracuseStep 479987 = 719981) B719981
theorem B611059 : Blo 479788 611059 := bstep (se 1 (by rfl) ⟨458294, by rfl⟩ : syracuseStep 611059 = 916589) B916589
theorem B480003 : Blo 479788 480003 := bstep (se 1 (by rfl) ⟨360002, by rfl⟩ : syracuseStep 480003 = 720005) B720005
theorem B480019 : Blo 479788 480019 := bstep (se 1 (by rfl) ⟨360014, by rfl⟩ : syracuseStep 480019 = 720029) B720029
theorem B578323 : Blo 479788 578323 := bstep (se 1 (by rfl) ⟨433742, by rfl⟩ : syracuseStep 578323 = 867485) B867485
theorem B480035 : Blo 479788 480035 := bstep (se 1 (by rfl) ⟨360026, by rfl⟩ : syracuseStep 480035 = 720053) B720053
theorem B480051 : Blo 479788 480051 := bstep (se 1 (by rfl) ⟨360038, by rfl⟩ : syracuseStep 480051 = 720077) B720077
theorem B480067 : Blo 479788 480067 := bstep (se 1 (by rfl) ⟨360050, by rfl⟩ : syracuseStep 480067 = 720101) B720101
theorem B480083 : Blo 479788 480083 := bstep (se 1 (by rfl) ⟨360062, by rfl⟩ : syracuseStep 480083 = 720125) B720125
theorem B611155 : Blo 479788 611155 := bstep (se 1 (by rfl) ⟨458366, by rfl⟩ : syracuseStep 611155 = 916733) B916733
theorem B480099 : Blo 479788 480099 := bstep (se 1 (by rfl) ⟨360074, by rfl⟩ : syracuseStep 480099 = 720149) B720149
theorem B480115 : Blo 479788 480115 := bstep (se 1 (by rfl) ⟨360086, by rfl⟩ : syracuseStep 480115 = 720173) B720173
theorem B480131 : Blo 479788 480131 := bstep (se 1 (by rfl) ⟨360098, by rfl⟩ : syracuseStep 480131 = 720197) B720197
theorem B480147 : Blo 479788 480147 := bstep (se 1 (by rfl) ⟨360110, by rfl⟩ : syracuseStep 480147 = 720221) B720221
theorem B480163 : Blo 479788 480163 := bstep (se 1 (by rfl) ⟨360122, by rfl⟩ : syracuseStep 480163 = 720245) B720245
theorem B480179 : Blo 479788 480179 := bstep (se 1 (by rfl) ⟨360134, by rfl⟩ : syracuseStep 480179 = 720269) B720269
theorem B480195 : Blo 479788 480195 := bstep (se 1 (by rfl) ⟨360146, by rfl⟩ : syracuseStep 480195 = 720293) B720293
theorem B480211 : Blo 479788 480211 := bstep (se 1 (by rfl) ⟨360158, by rfl⟩ : syracuseStep 480211 = 720317) B720317
theorem B480227 : Blo 479788 480227 := bstep (se 1 (by rfl) ⟨360170, by rfl⟩ : syracuseStep 480227 = 720341) B720341
theorem B480243 : Blo 479788 480243 := bstep (se 1 (by rfl) ⟨360182, by rfl⟩ : syracuseStep 480243 = 720365) B720365
theorem B480259 : Blo 479788 480259 := bstep (se 1 (by rfl) ⟨360194, by rfl⟩ : syracuseStep 480259 = 720389) B720389
theorem B480275 : Blo 479788 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B480291 : Blo 479788 480291 := bstep (se 1 (by rfl) ⟨360218, by rfl⟩ : syracuseStep 480291 = 720437) B720437
theorem B1627181 : Blo 479788 1627181 := bstep (se 3 (by rfl) ⟨305096, by rfl⟩ : syracuseStep 1627181 = 610193) B610193
theorem B480307 : Blo 479788 480307 := bstep (se 1 (by rfl) ⟨360230, by rfl⟩ : syracuseStep 480307 = 720461) B720461
theorem B480323 : Blo 479788 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B513091 : Blo 479788 513091 := bstep (se 1 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 513091 = 769637) B769637
theorem B480339 : Blo 479788 480339 := bstep (se 1 (by rfl) ⟨360254, by rfl⟩ : syracuseStep 480339 = 720509) B720509
theorem B480355 : Blo 479788 480355 := bstep (se 1 (by rfl) ⟨360266, by rfl⟩ : syracuseStep 480355 = 720533) B720533
theorem B1627235 : Blo 479788 1627235 := bstep (se 1 (by rfl) ⟨1220426, by rfl⟩ : syracuseStep 1627235 = 2440853) B2440853
theorem B4936817 : Blo 479788 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B480371 : Blo 479788 480371 := bstep (se 1 (by rfl) ⟨360278, by rfl⟩ : syracuseStep 480371 = 720557) B720557
theorem B480387 : Blo 479788 480387 := bstep (se 1 (by rfl) ⟨360290, by rfl⟩ : syracuseStep 480387 = 720581) B720581
theorem B480403 : Blo 479788 480403 := bstep (se 1 (by rfl) ⟨360302, by rfl⟩ : syracuseStep 480403 = 720605) B720605
theorem B480419 : Blo 479788 480419 := bstep (se 1 (by rfl) ⟨360314, by rfl⟩ : syracuseStep 480419 = 720629) B720629
theorem B480435 : Blo 479788 480435 := bstep (se 1 (by rfl) ⟨360326, by rfl⟩ : syracuseStep 480435 = 720653) B720653
theorem B480451 : Blo 479788 480451 := bstep (se 1 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 480451 = 720677) B720677
theorem B480467 : Blo 479788 480467 := bstep (se 1 (by rfl) ⟨360350, by rfl⟩ : syracuseStep 480467 = 720701) B720701
theorem B480483 : Blo 479788 480483 := bstep (se 1 (by rfl) ⟨360362, by rfl⟩ : syracuseStep 480483 = 720725) B720725
theorem B480499 : Blo 479788 480499 := bstep (se 1 (by rfl) ⟨360374, by rfl⟩ : syracuseStep 480499 = 720749) B720749
theorem B480515 : Blo 479788 480515 := bstep (se 1 (by rfl) ⟨360386, by rfl⟩ : syracuseStep 480515 = 720773) B720773
theorem B480531 : Blo 479788 480531 := bstep (se 1 (by rfl) ⟨360398, by rfl⟩ : syracuseStep 480531 = 720797) B720797
theorem B480547 : Blo 479788 480547 := bstep (se 1 (by rfl) ⟨360410, by rfl⟩ : syracuseStep 480547 = 720821) B720821
theorem B480563 : Blo 479788 480563 := bstep (se 1 (by rfl) ⟨360422, by rfl⟩ : syracuseStep 480563 = 720845) B720845
theorem B480579 : Blo 479788 480579 := bstep (se 1 (by rfl) ⟨360434, by rfl⟩ : syracuseStep 480579 = 720869) B720869
theorem B611651 : Blo 479788 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B480595 : Blo 479788 480595 := bstep (se 1 (by rfl) ⟨360446, by rfl⟩ : syracuseStep 480595 = 720893) B720893
theorem B480611 : Blo 479788 480611 := bstep (se 1 (by rfl) ⟨360458, by rfl⟩ : syracuseStep 480611 = 720917) B720917
theorem B1627505 : Blo 479788 1627505 := bstep (se 2 (by rfl) ⟨610314, by rfl⟩ : syracuseStep 1627505 = 1220629) B1220629
theorem B480627 : Blo 479788 480627 := bstep (se 1 (by rfl) ⟨360470, by rfl⟩ : syracuseStep 480627 = 720941) B720941
theorem B480643 : Blo 479788 480643 := bstep (se 1 (by rfl) ⟨360482, by rfl⟩ : syracuseStep 480643 = 720965) B720965
theorem B480659 : Blo 479788 480659 := bstep (se 1 (by rfl) ⟨360494, by rfl⟩ : syracuseStep 480659 = 720989) B720989
theorem B480675 : Blo 479788 480675 := bstep (se 1 (by rfl) ⟨360506, by rfl⟩ : syracuseStep 480675 = 721013) B721013
theorem B480691 : Blo 479788 480691 := bstep (se 1 (by rfl) ⟨360518, by rfl⟩ : syracuseStep 480691 = 721037) B721037
theorem B480707 : Blo 479788 480707 := bstep (se 1 (by rfl) ⟨360530, by rfl⟩ : syracuseStep 480707 = 721061) B721061
theorem B480723 : Blo 479788 480723 := bstep (se 1 (by rfl) ⟨360542, by rfl⟩ : syracuseStep 480723 = 721085) B721085
theorem B480739 : Blo 479788 480739 := bstep (se 1 (by rfl) ⟨360554, by rfl⟩ : syracuseStep 480739 = 721109) B721109
theorem B480755 : Blo 479788 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B480771 : Blo 479788 480771 := bstep (se 1 (by rfl) ⟨360578, by rfl⟩ : syracuseStep 480771 = 721157) B721157
theorem B480787 : Blo 479788 480787 := bstep (se 1 (by rfl) ⟨360590, by rfl⟩ : syracuseStep 480787 = 721181) B721181
theorem B480803 : Blo 479788 480803 := bstep (se 1 (by rfl) ⟨360602, by rfl⟩ : syracuseStep 480803 = 721205) B721205
theorem B579107 : Blo 479788 579107 := bstep (se 1 (by rfl) ⟨434330, by rfl⟩ : syracuseStep 579107 = 868661) B868661
theorem B480819 : Blo 479788 480819 := bstep (se 1 (by rfl) ⟨360614, by rfl⟩ : syracuseStep 480819 = 721229) B721229
theorem B480835 : Blo 479788 480835 := bstep (se 1 (by rfl) ⟨360626, by rfl⟩ : syracuseStep 480835 = 721253) B721253
theorem B480851 : Blo 479788 480851 := bstep (se 1 (by rfl) ⟨360638, by rfl⟩ : syracuseStep 480851 = 721277) B721277
theorem B480867 : Blo 479788 480867 := bstep (se 1 (by rfl) ⟨360650, by rfl⟩ : syracuseStep 480867 = 721301) B721301
theorem B6182513 : Blo 479788 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B480883 : Blo 479788 480883 := bstep (se 1 (by rfl) ⟨360662, by rfl⟩ : syracuseStep 480883 = 721325) B721325
theorem B480899 : Blo 479788 480899 := bstep (se 1 (by rfl) ⟨360674, by rfl⟩ : syracuseStep 480899 = 721349) B721349
theorem B480915 : Blo 479788 480915 := bstep (se 1 (by rfl) ⟨360686, by rfl⟩ : syracuseStep 480915 = 721373) B721373
theorem B480931 : Blo 479788 480931 := bstep (se 1 (by rfl) ⟨360698, by rfl⟩ : syracuseStep 480931 = 721397) B721397
theorem B480947 : Blo 479788 480947 := bstep (se 1 (by rfl) ⟨360710, by rfl⟩ : syracuseStep 480947 = 721421) B721421
theorem B480963 : Blo 479788 480963 := bstep (se 1 (by rfl) ⟨360722, by rfl⟩ : syracuseStep 480963 = 721445) B721445
theorem B480979 : Blo 479788 480979 := bstep (se 1 (by rfl) ⟨360734, by rfl⟩ : syracuseStep 480979 = 721469) B721469
theorem B480995 : Blo 479788 480995 := bstep (se 1 (by rfl) ⟨360746, by rfl⟩ : syracuseStep 480995 = 721493) B721493
theorem B481011 : Blo 479788 481011 := bstep (se 1 (by rfl) ⟨360758, by rfl⟩ : syracuseStep 481011 = 721517) B721517
theorem B481027 : Blo 479788 481027 := bstep (se 1 (by rfl) ⟨360770, by rfl⟩ : syracuseStep 481027 = 721541) B721541
theorem B481043 : Blo 479788 481043 := bstep (se 1 (by rfl) ⟨360782, by rfl⟩ : syracuseStep 481043 = 721565) B721565
theorem B481059 : Blo 479788 481059 := bstep (se 1 (by rfl) ⟨360794, by rfl⟩ : syracuseStep 481059 = 721589) B721589
theorem B481075 : Blo 479788 481075 := bstep (se 1 (by rfl) ⟨360806, by rfl⟩ : syracuseStep 481075 = 721613) B721613
theorem B481091 : Blo 479788 481091 := bstep (se 1 (by rfl) ⟨360818, by rfl⟩ : syracuseStep 481091 = 721637) B721637
theorem B481107 : Blo 479788 481107 := bstep (se 1 (by rfl) ⟨360830, by rfl⟩ : syracuseStep 481107 = 721661) B721661
theorem B481123 : Blo 479788 481123 := bstep (se 1 (by rfl) ⟨360842, by rfl⟩ : syracuseStep 481123 = 721685) B721685
theorem B481139 : Blo 479788 481139 := bstep (se 1 (by rfl) ⟨360854, by rfl⟩ : syracuseStep 481139 = 721709) B721709
theorem B481155 : Blo 479788 481155 := bstep (se 1 (by rfl) ⟨360866, by rfl⟩ : syracuseStep 481155 = 721733) B721733
theorem B1628045 : Blo 479788 1628045 := bstep (se 3 (by rfl) ⟨305258, by rfl⟩ : syracuseStep 1628045 = 610517) B610517
theorem B481171 : Blo 479788 481171 := bstep (se 1 (by rfl) ⟨360878, by rfl⟩ : syracuseStep 481171 = 721757) B721757
theorem B481187 : Blo 479788 481187 := bstep (se 1 (by rfl) ⟨360890, by rfl⟩ : syracuseStep 481187 = 721781) B721781
theorem B481203 : Blo 479788 481203 := bstep (se 1 (by rfl) ⟨360902, by rfl⟩ : syracuseStep 481203 = 721805) B721805
theorem B481219 : Blo 479788 481219 := bstep (se 1 (by rfl) ⟨360914, by rfl⟩ : syracuseStep 481219 = 721829) B721829
theorem B1628099 : Blo 479788 1628099 := bstep (se 1 (by rfl) ⟨1221074, by rfl⟩ : syracuseStep 1628099 = 2442149) B2442149
theorem B481235 : Blo 479788 481235 := bstep (se 1 (by rfl) ⟨360926, by rfl⟩ : syracuseStep 481235 = 721853) B721853
theorem B481251 : Blo 479788 481251 := bstep (se 1 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 481251 = 721877) B721877
theorem B481267 : Blo 479788 481267 := bstep (se 1 (by rfl) ⟨360950, by rfl⟩ : syracuseStep 481267 = 721901) B721901
theorem B481283 : Blo 479788 481283 := bstep (se 1 (by rfl) ⟨360962, by rfl⟩ : syracuseStep 481283 = 721925) B721925
theorem B481299 : Blo 479788 481299 := bstep (se 1 (by rfl) ⟨360974, by rfl⟩ : syracuseStep 481299 = 721949) B721949
theorem B481315 : Blo 479788 481315 := bstep (se 1 (by rfl) ⟨360986, by rfl⟩ : syracuseStep 481315 = 721973) B721973
theorem B481331 : Blo 479788 481331 := bstep (se 1 (by rfl) ⟨360998, by rfl⟩ : syracuseStep 481331 = 721997) B721997
theorem B481347 : Blo 479788 481347 := bstep (se 1 (by rfl) ⟨361010, by rfl⟩ : syracuseStep 481347 = 722021) B722021
theorem B481363 : Blo 479788 481363 := bstep (se 1 (by rfl) ⟨361022, by rfl⟩ : syracuseStep 481363 = 722045) B722045
theorem B481379 : Blo 479788 481379 := bstep (se 1 (by rfl) ⟨361034, by rfl⟩ : syracuseStep 481379 = 722069) B722069
theorem B481395 : Blo 479788 481395 := bstep (se 1 (by rfl) ⟨361046, by rfl⟩ : syracuseStep 481395 = 722093) B722093
theorem B481411 : Blo 479788 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B481427 : Blo 479788 481427 := bstep (se 1 (by rfl) ⟨361070, by rfl⟩ : syracuseStep 481427 = 722141) B722141
theorem B481443 : Blo 479788 481443 := bstep (se 1 (by rfl) ⟨361082, by rfl⟩ : syracuseStep 481443 = 722165) B722165
theorem B481459 : Blo 479788 481459 := bstep (se 1 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 481459 = 722189) B722189
theorem B481475 : Blo 479788 481475 := bstep (se 1 (by rfl) ⟨361106, by rfl⟩ : syracuseStep 481475 = 722213) B722213
theorem B1628369 : Blo 479788 1628369 := bstep (se 2 (by rfl) ⟨610638, by rfl⟩ : syracuseStep 1628369 = 1221277) B1221277
theorem B481491 : Blo 479788 481491 := bstep (se 1 (by rfl) ⟨361118, by rfl⟩ : syracuseStep 481491 = 722237) B722237
theorem B481507 : Blo 479788 481507 := bstep (se 1 (by rfl) ⟨361130, by rfl⟩ : syracuseStep 481507 = 722261) B722261
theorem B481523 : Blo 479788 481523 := bstep (se 1 (by rfl) ⟨361142, by rfl⟩ : syracuseStep 481523 = 722285) B722285
theorem B481539 : Blo 479788 481539 := bstep (se 1 (by rfl) ⟨361154, by rfl⟩ : syracuseStep 481539 = 722309) B722309
theorem B1825037 : Blo 479788 1825037 := bstep (se 3 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 1825037 = 684389) B684389
theorem B2054413 : Blo 479788 2054413 := bstep (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) B770405
theorem B481555 : Blo 479788 481555 := bstep (se 1 (by rfl) ⟨361166, by rfl⟩ : syracuseStep 481555 = 722333) B722333
theorem B481571 : Blo 479788 481571 := bstep (se 1 (by rfl) ⟨361178, by rfl⟩ : syracuseStep 481571 = 722357) B722357
theorem B481587 : Blo 479788 481587 := bstep (se 1 (by rfl) ⟨361190, by rfl⟩ : syracuseStep 481587 = 722381) B722381
theorem B514355 : Blo 479788 514355 := bstep (se 1 (by rfl) ⟨385766, by rfl⟩ : syracuseStep 514355 = 771533) B771533
theorem B481603 : Blo 479788 481603 := bstep (se 1 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 481603 = 722405) B722405
theorem B481619 : Blo 479788 481619 := bstep (se 1 (by rfl) ⟨361214, by rfl⟩ : syracuseStep 481619 = 722429) B722429
theorem B481635 : Blo 479788 481635 := bstep (se 1 (by rfl) ⟨361226, by rfl⟩ : syracuseStep 481635 = 722453) B722453
theorem B2480483 : Blo 479788 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B481651 : Blo 479788 481651 := bstep (se 1 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 481651 = 722477) B722477
theorem B481667 : Blo 479788 481667 := bstep (se 1 (by rfl) ⟨361250, by rfl⟩ : syracuseStep 481667 = 722501) B722501
theorem B481683 : Blo 479788 481683 := bstep (se 1 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 481683 = 722525) B722525
theorem B481699 : Blo 479788 481699 := bstep (se 1 (by rfl) ⟨361274, by rfl⟩ : syracuseStep 481699 = 722549) B722549
theorem B481715 : Blo 479788 481715 := bstep (se 1 (by rfl) ⟨361286, by rfl⟩ : syracuseStep 481715 = 722573) B722573
theorem B481731 : Blo 479788 481731 := bstep (se 1 (by rfl) ⟨361298, by rfl⟩ : syracuseStep 481731 = 722597) B722597
theorem B481747 : Blo 479788 481747 := bstep (se 1 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 481747 = 722621) B722621
theorem B481763 : Blo 479788 481763 := bstep (se 1 (by rfl) ⟨361322, by rfl⟩ : syracuseStep 481763 = 722645) B722645
theorem B4119011 : Blo 479788 4119011 := bstep (se 1 (by rfl) ⟨3089258, by rfl⟩ : syracuseStep 4119011 = 6178517) B6178517
theorem B481779 : Blo 479788 481779 := bstep (se 1 (by rfl) ⟨361334, by rfl⟩ : syracuseStep 481779 = 722669) B722669
theorem B481795 : Blo 479788 481795 := bstep (se 1 (by rfl) ⟨361346, by rfl⟩ : syracuseStep 481795 = 722693) B722693
theorem B481811 : Blo 479788 481811 := bstep (se 1 (by rfl) ⟨361358, by rfl⟩ : syracuseStep 481811 = 722717) B722717
theorem B481827 : Blo 479788 481827 := bstep (se 1 (by rfl) ⟨361370, by rfl⟩ : syracuseStep 481827 = 722741) B722741
theorem B481843 : Blo 479788 481843 := bstep (se 1 (by rfl) ⟨361382, by rfl⟩ : syracuseStep 481843 = 722765) B722765
theorem B481859 : Blo 479788 481859 := bstep (se 1 (by rfl) ⟨361394, by rfl⟩ : syracuseStep 481859 = 722789) B722789
theorem B481875 : Blo 479788 481875 := bstep (se 1 (by rfl) ⟨361406, by rfl⟩ : syracuseStep 481875 = 722813) B722813
theorem B481891 : Blo 479788 481891 := bstep (se 1 (by rfl) ⟨361418, by rfl⟩ : syracuseStep 481891 = 722837) B722837
theorem B481907 : Blo 479788 481907 := bstep (se 1 (by rfl) ⟨361430, by rfl⟩ : syracuseStep 481907 = 722861) B722861
theorem B481923 : Blo 479788 481923 := bstep (se 1 (by rfl) ⟨361442, by rfl⟩ : syracuseStep 481923 = 722885) B722885
theorem B2939533 : Blo 479788 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B481939 : Blo 479788 481939 := bstep (se 1 (by rfl) ⟨361454, by rfl⟩ : syracuseStep 481939 = 722909) B722909
theorem B481955 : Blo 479788 481955 := bstep (se 1 (by rfl) ⟨361466, by rfl⟩ : syracuseStep 481955 = 722933) B722933
theorem B481971 : Blo 479788 481971 := bstep (se 1 (by rfl) ⟨361478, by rfl⟩ : syracuseStep 481971 = 722957) B722957
theorem B481987 : Blo 479788 481987 := bstep (se 1 (by rfl) ⟨361490, by rfl⟩ : syracuseStep 481987 = 722981) B722981
theorem B482003 : Blo 479788 482003 := bstep (se 1 (by rfl) ⟨361502, by rfl⟩ : syracuseStep 482003 = 723005) B723005
theorem B482019 : Blo 479788 482019 := bstep (se 1 (by rfl) ⟨361514, by rfl⟩ : syracuseStep 482019 = 723029) B723029
theorem B1628909 : Blo 479788 1628909 := bstep (se 3 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 1628909 = 610841) B610841
theorem B482035 : Blo 479788 482035 := bstep (se 1 (by rfl) ⟨361526, by rfl⟩ : syracuseStep 482035 = 723053) B723053
theorem B482051 : Blo 479788 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B482067 : Blo 479788 482067 := bstep (se 1 (by rfl) ⟨361550, by rfl⟩ : syracuseStep 482067 = 723101) B723101
theorem B482083 : Blo 479788 482083 := bstep (se 1 (by rfl) ⟨361562, by rfl⟩ : syracuseStep 482083 = 723125) B723125
theorem B1628963 : Blo 479788 1628963 := bstep (se 1 (by rfl) ⟨1221722, by rfl⟩ : syracuseStep 1628963 = 2443445) B2443445
theorem B809777 : Blo 479788 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B482099 : Blo 479788 482099 := bstep (se 1 (by rfl) ⟨361574, by rfl⟩ : syracuseStep 482099 = 723149) B723149
theorem B482115 : Blo 479788 482115 := bstep (se 1 (by rfl) ⟨361586, by rfl⟩ : syracuseStep 482115 = 723173) B723173
theorem B1366865 : Blo 479788 1366865 := bstep (se 2 (by rfl) ⟨512574, by rfl⟩ : syracuseStep 1366865 = 1025149) B1025149
theorem B482131 : Blo 479788 482131 := bstep (se 1 (by rfl) ⟨361598, by rfl⟩ : syracuseStep 482131 = 723197) B723197
theorem B482147 : Blo 479788 482147 := bstep (se 1 (by rfl) ⟨361610, by rfl⟩ : syracuseStep 482147 = 723221) B723221
theorem B482163 : Blo 479788 482163 := bstep (se 1 (by rfl) ⟨361622, by rfl⟩ : syracuseStep 482163 = 723245) B723245
theorem B482179 : Blo 479788 482179 := bstep (se 1 (by rfl) ⟨361634, by rfl⟩ : syracuseStep 482179 = 723269) B723269
theorem B482195 : Blo 479788 482195 := bstep (se 1 (by rfl) ⟨361646, by rfl⟩ : syracuseStep 482195 = 723293) B723293
theorem B482211 : Blo 479788 482211 := bstep (se 1 (by rfl) ⟨361658, by rfl⟩ : syracuseStep 482211 = 723317) B723317
theorem B809905 : Blo 479788 809905 := bstep (se 2 (by rfl) ⟨303714, by rfl⟩ : syracuseStep 809905 = 607429) B607429
theorem B2448305 : Blo 479788 2448305 := bstep (se 2 (by rfl) ⟨918114, by rfl⟩ : syracuseStep 2448305 = 1836229) B1836229
theorem B482227 : Blo 479788 482227 := bstep (se 1 (by rfl) ⟨361670, by rfl⟩ : syracuseStep 482227 = 723341) B723341
theorem B482243 : Blo 479788 482243 := bstep (se 1 (by rfl) ⟨361682, by rfl⟩ : syracuseStep 482243 = 723365) B723365
theorem B809939 : Blo 479788 809939 := bstep (se 1 (by rfl) ⟨607454, by rfl⟩ : syracuseStep 809939 = 1214909) B1214909
theorem B482259 : Blo 479788 482259 := bstep (se 1 (by rfl) ⟨361694, by rfl⟩ : syracuseStep 482259 = 723389) B723389
theorem B482275 : Blo 479788 482275 := bstep (se 1 (by rfl) ⟨361706, by rfl⟩ : syracuseStep 482275 = 723413) B723413
theorem B482291 : Blo 479788 482291 := bstep (se 1 (by rfl) ⟨361718, by rfl⟩ : syracuseStep 482291 = 723437) B723437
theorem B482307 : Blo 479788 482307 := bstep (se 1 (by rfl) ⟨361730, by rfl⟩ : syracuseStep 482307 = 723461) B723461
theorem B1367057 : Blo 479788 1367057 := bstep (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) B1025293
theorem B482323 : Blo 479788 482323 := bstep (se 1 (by rfl) ⟨361742, by rfl⟩ : syracuseStep 482323 = 723485) B723485
theorem B482339 : Blo 479788 482339 := bstep (se 1 (by rfl) ⟨361754, by rfl⟩ : syracuseStep 482339 = 723509) B723509
theorem B515107 : Blo 479788 515107 := bstep (se 1 (by rfl) ⟨386330, by rfl⟩ : syracuseStep 515107 = 772661) B772661
theorem B1825841 : Blo 479788 1825841 := bstep (se 2 (by rfl) ⟨684690, by rfl⟩ : syracuseStep 1825841 = 1369381) B1369381
theorem B1629233 : Blo 479788 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B482355 : Blo 479788 482355 := bstep (se 1 (by rfl) ⟨361766, by rfl⟩ : syracuseStep 482355 = 723533) B723533
theorem B482371 : Blo 479788 482371 := bstep (se 1 (by rfl) ⟨361778, by rfl⟩ : syracuseStep 482371 = 723557) B723557
theorem B810067 : Blo 479788 810067 := bstep (se 1 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 810067 = 1215101) B1215101
theorem B482387 : Blo 479788 482387 := bstep (se 1 (by rfl) ⟨361790, by rfl⟩ : syracuseStep 482387 = 723581) B723581
theorem B482403 : Blo 479788 482403 := bstep (se 1 (by rfl) ⟨361802, by rfl⟩ : syracuseStep 482403 = 723605) B723605
theorem B2743409 : Blo 479788 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B482419 : Blo 479788 482419 := bstep (se 1 (by rfl) ⟨361814, by rfl⟩ : syracuseStep 482419 = 723629) B723629
theorem B482435 : Blo 479788 482435 := bstep (se 1 (by rfl) ⟨361826, by rfl⟩ : syracuseStep 482435 = 723653) B723653
theorem B482451 : Blo 479788 482451 := bstep (se 1 (by rfl) ⟨361838, by rfl⟩ : syracuseStep 482451 = 723677) B723677
theorem B482467 : Blo 479788 482467 := bstep (se 1 (by rfl) ⟨361850, by rfl⟩ : syracuseStep 482467 = 723701) B723701
theorem B482483 : Blo 479788 482483 := bstep (se 1 (by rfl) ⟨361862, by rfl⟩ : syracuseStep 482483 = 723725) B723725
theorem B482499 : Blo 479788 482499 := bstep (se 1 (by rfl) ⟨361874, by rfl⟩ : syracuseStep 482499 = 723749) B723749
theorem B482515 : Blo 479788 482515 := bstep (se 1 (by rfl) ⟨361886, by rfl⟩ : syracuseStep 482515 = 723773) B723773
theorem B810209 : Blo 479788 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B482531 : Blo 479788 482531 := bstep (se 1 (by rfl) ⟨361898, by rfl⟩ : syracuseStep 482531 = 723797) B723797
theorem B482547 : Blo 479788 482547 := bstep (se 1 (by rfl) ⟨361910, by rfl⟩ : syracuseStep 482547 = 723821) B723821
theorem B482563 : Blo 479788 482563 := bstep (se 1 (by rfl) ⟨361922, by rfl⟩ : syracuseStep 482563 = 723845) B723845
theorem B482579 : Blo 479788 482579 := bstep (se 1 (by rfl) ⟨361934, by rfl⟩ : syracuseStep 482579 = 723869) B723869
theorem B482595 : Blo 479788 482595 := bstep (se 1 (by rfl) ⟨361946, by rfl⟩ : syracuseStep 482595 = 723893) B723893
theorem B482611 : Blo 479788 482611 := bstep (se 1 (by rfl) ⟨361958, by rfl⟩ : syracuseStep 482611 = 723917) B723917
theorem B482627 : Blo 479788 482627 := bstep (se 1 (by rfl) ⟨361970, by rfl⟩ : syracuseStep 482627 = 723941) B723941
theorem B482643 : Blo 479788 482643 := bstep (se 1 (by rfl) ⟨361982, by rfl⟩ : syracuseStep 482643 = 723965) B723965
theorem B810337 : Blo 479788 810337 := bstep (se 2 (by rfl) ⟨303876, by rfl⟩ : syracuseStep 810337 = 607753) B607753
theorem B482659 : Blo 479788 482659 := bstep (se 1 (by rfl) ⟨361994, by rfl⟩ : syracuseStep 482659 = 723989) B723989
theorem B482675 : Blo 479788 482675 := bstep (se 1 (by rfl) ⟨362006, by rfl⟩ : syracuseStep 482675 = 724013) B724013
theorem B810371 : Blo 479788 810371 := bstep (se 1 (by rfl) ⟨607778, by rfl⟩ : syracuseStep 810371 = 1215557) B1215557
theorem B482691 : Blo 479788 482691 := bstep (se 1 (by rfl) ⟨362018, by rfl⟩ : syracuseStep 482691 = 724037) B724037
theorem B482707 : Blo 479788 482707 := bstep (se 1 (by rfl) ⟨362030, by rfl⟩ : syracuseStep 482707 = 724061) B724061
theorem B482723 : Blo 479788 482723 := bstep (se 1 (by rfl) ⟨362042, by rfl⟩ : syracuseStep 482723 = 724085) B724085
theorem B482739 : Blo 479788 482739 := bstep (se 1 (by rfl) ⟨362054, by rfl⟩ : syracuseStep 482739 = 724109) B724109
theorem B482755 : Blo 479788 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B482771 : Blo 479788 482771 := bstep (se 1 (by rfl) ⟨362078, by rfl⟩ : syracuseStep 482771 = 724157) B724157
theorem B482787 : Blo 479788 482787 := bstep (se 1 (by rfl) ⟨362090, by rfl⟩ : syracuseStep 482787 = 724181) B724181
theorem B482803 : Blo 479788 482803 := bstep (se 1 (by rfl) ⟨362102, by rfl⟩ : syracuseStep 482803 = 724205) B724205
theorem B810499 : Blo 479788 810499 := bstep (se 1 (by rfl) ⟨607874, by rfl⟩ : syracuseStep 810499 = 1215749) B1215749
theorem B482819 : Blo 479788 482819 := bstep (se 1 (by rfl) ⟨362114, by rfl⟩ : syracuseStep 482819 = 724229) B724229
theorem B482835 : Blo 479788 482835 := bstep (se 1 (by rfl) ⟨362126, by rfl⟩ : syracuseStep 482835 = 724253) B724253
theorem B482851 : Blo 479788 482851 := bstep (se 1 (by rfl) ⟨362138, by rfl⟩ : syracuseStep 482851 = 724277) B724277
theorem B482867 : Blo 479788 482867 := bstep (se 1 (by rfl) ⟨362150, by rfl⟩ : syracuseStep 482867 = 724301) B724301
theorem B482883 : Blo 479788 482883 := bstep (se 1 (by rfl) ⟨362162, by rfl⟩ : syracuseStep 482883 = 724325) B724325
theorem B1629773 : Blo 479788 1629773 := bstep (se 3 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 1629773 = 611165) B611165
theorem B482899 : Blo 479788 482899 := bstep (se 1 (by rfl) ⟨362174, by rfl⟩ : syracuseStep 482899 = 724349) B724349
theorem B482915 : Blo 479788 482915 := bstep (se 1 (by rfl) ⟨362186, by rfl⟩ : syracuseStep 482915 = 724373) B724373
theorem B482931 : Blo 479788 482931 := bstep (se 1 (by rfl) ⟨362198, by rfl⟩ : syracuseStep 482931 = 724397) B724397
theorem B1629827 : Blo 479788 1629827 := bstep (se 1 (by rfl) ⟨1222370, by rfl⟩ : syracuseStep 1629827 = 2444741) B2444741
theorem B482947 : Blo 479788 482947 := bstep (se 1 (by rfl) ⟨362210, by rfl⟩ : syracuseStep 482947 = 724421) B724421
theorem B810641 : Blo 479788 810641 := bstep (se 2 (by rfl) ⟨303990, by rfl⟩ : syracuseStep 810641 = 607981) B607981
theorem B482963 : Blo 479788 482963 := bstep (se 1 (by rfl) ⟨362222, by rfl⟩ : syracuseStep 482963 = 724445) B724445
theorem B482979 : Blo 479788 482979 := bstep (se 1 (by rfl) ⟨362234, by rfl⟩ : syracuseStep 482979 = 724469) B724469
theorem B482995 : Blo 479788 482995 := bstep (se 1 (by rfl) ⟨362246, by rfl⟩ : syracuseStep 482995 = 724493) B724493
theorem B483011 : Blo 479788 483011 := bstep (se 1 (by rfl) ⟨362258, by rfl⟩ : syracuseStep 483011 = 724517) B724517
theorem B1826509 : Blo 479788 1826509 := bstep (se 3 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 1826509 = 684941) B684941
theorem B483027 : Blo 479788 483027 := bstep (se 1 (by rfl) ⟨362270, by rfl⟩ : syracuseStep 483027 = 724541) B724541
theorem B483043 : Blo 479788 483043 := bstep (se 1 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 483043 = 724565) B724565
theorem B483059 : Blo 479788 483059 := bstep (se 1 (by rfl) ⟨362294, by rfl⟩ : syracuseStep 483059 = 724589) B724589
theorem B483075 : Blo 479788 483075 := bstep (se 1 (by rfl) ⟨362306, by rfl⟩ : syracuseStep 483075 = 724613) B724613
theorem B810769 : Blo 479788 810769 := bstep (se 2 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 810769 = 608077) B608077
theorem B483091 : Blo 479788 483091 := bstep (se 1 (by rfl) ⟨362318, by rfl⟩ : syracuseStep 483091 = 724637) B724637
theorem B483107 : Blo 479788 483107 := bstep (se 1 (by rfl) ⟨362330, by rfl⟩ : syracuseStep 483107 = 724661) B724661
theorem B810803 : Blo 479788 810803 := bstep (se 1 (by rfl) ⟨608102, by rfl⟩ : syracuseStep 810803 = 1216205) B1216205
theorem B483123 : Blo 479788 483123 := bstep (se 1 (by rfl) ⟨362342, by rfl⟩ : syracuseStep 483123 = 724685) B724685
theorem B483139 : Blo 479788 483139 := bstep (se 1 (by rfl) ⟨362354, by rfl⟩ : syracuseStep 483139 = 724709) B724709
theorem B483155 : Blo 479788 483155 := bstep (se 1 (by rfl) ⟨362366, by rfl⟩ : syracuseStep 483155 = 724733) B724733
theorem B483171 : Blo 479788 483171 := bstep (se 1 (by rfl) ⟨362378, by rfl⟩ : syracuseStep 483171 = 724757) B724757
theorem B1957745 : Blo 479788 1957745 := bstep (se 2 (by rfl) ⟨734154, by rfl⟩ : syracuseStep 1957745 = 1468309) B1468309
theorem B483187 : Blo 479788 483187 := bstep (se 1 (by rfl) ⟨362390, by rfl⟩ : syracuseStep 483187 = 724781) B724781
theorem B483203 : Blo 479788 483203 := bstep (se 1 (by rfl) ⟨362402, by rfl⟩ : syracuseStep 483203 = 724805) B724805
theorem B1630097 : Blo 479788 1630097 := bstep (se 2 (by rfl) ⟨611286, by rfl⟩ : syracuseStep 1630097 = 1222573) B1222573
theorem B483219 : Blo 479788 483219 := bstep (se 1 (by rfl) ⟨362414, by rfl⟩ : syracuseStep 483219 = 724829) B724829
theorem B483235 : Blo 479788 483235 := bstep (se 1 (by rfl) ⟨362426, by rfl⟩ : syracuseStep 483235 = 724853) B724853
theorem B810931 : Blo 479788 810931 := bstep (se 1 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 810931 = 1216397) B1216397
theorem B483251 : Blo 479788 483251 := bstep (se 1 (by rfl) ⟨362438, by rfl⟩ : syracuseStep 483251 = 724877) B724877
theorem B483267 : Blo 479788 483267 := bstep (se 1 (by rfl) ⟨362450, by rfl⟩ : syracuseStep 483267 = 724901) B724901
theorem B483283 : Blo 479788 483283 := bstep (se 1 (by rfl) ⟨362462, by rfl⟩ : syracuseStep 483283 = 724925) B724925
theorem B483299 : Blo 479788 483299 := bstep (se 1 (by rfl) ⟨362474, by rfl⟩ : syracuseStep 483299 = 724949) B724949
theorem B1368049 : Blo 479788 1368049 := bstep (se 2 (by rfl) ⟨513018, by rfl⟩ : syracuseStep 1368049 = 1026037) B1026037
theorem B483315 : Blo 479788 483315 := bstep (se 1 (by rfl) ⟨362486, by rfl⟩ : syracuseStep 483315 = 724973) B724973
theorem B483331 : Blo 479788 483331 := bstep (se 1 (by rfl) ⟨362498, by rfl⟩ : syracuseStep 483331 = 724997) B724997
theorem B516115 : Blo 479788 516115 := bstep (se 1 (by rfl) ⟨387086, by rfl⟩ : syracuseStep 516115 = 774173) B774173
theorem B483347 : Blo 479788 483347 := bstep (se 1 (by rfl) ⟨362510, by rfl⟩ : syracuseStep 483347 = 725021) B725021
theorem B483363 : Blo 479788 483363 := bstep (se 1 (by rfl) ⟨362522, by rfl⟩ : syracuseStep 483363 = 725045) B725045
theorem B483379 : Blo 479788 483379 := bstep (se 1 (by rfl) ⟨362534, by rfl⟩ : syracuseStep 483379 = 725069) B725069
theorem B811073 : Blo 479788 811073 := bstep (se 2 (by rfl) ⟨304152, by rfl⟩ : syracuseStep 811073 = 608305) B608305
theorem B483395 : Blo 479788 483395 := bstep (se 1 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 483395 = 725093) B725093
theorem B548947 : Blo 479788 548947 := bstep (se 1 (by rfl) ⟨411710, by rfl⟩ : syracuseStep 548947 = 823421) B823421
theorem B483411 : Blo 479788 483411 := bstep (se 1 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 483411 = 725117) B725117
theorem B483427 : Blo 479788 483427 := bstep (se 1 (by rfl) ⟨362570, by rfl⟩ : syracuseStep 483427 = 725141) B725141
theorem B483443 : Blo 479788 483443 := bstep (se 1 (by rfl) ⟨362582, by rfl⟩ : syracuseStep 483443 = 725165) B725165
theorem B483459 : Blo 479788 483459 := bstep (se 1 (by rfl) ⟨362594, by rfl⟩ : syracuseStep 483459 = 725189) B725189
theorem B483475 : Blo 479788 483475 := bstep (se 1 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 483475 = 725213) B725213
theorem B483491 : Blo 479788 483491 := bstep (se 1 (by rfl) ⟨362618, by rfl⟩ : syracuseStep 483491 = 725237) B725237
theorem B483507 : Blo 479788 483507 := bstep (se 1 (by rfl) ⟨362630, by rfl⟩ : syracuseStep 483507 = 725261) B725261
theorem B811201 : Blo 479788 811201 := bstep (se 2 (by rfl) ⟨304200, by rfl⟩ : syracuseStep 811201 = 608401) B608401
theorem B483523 : Blo 479788 483523 := bstep (se 1 (by rfl) ⟨362642, by rfl⟩ : syracuseStep 483523 = 725285) B725285
theorem B483539 : Blo 479788 483539 := bstep (se 1 (by rfl) ⟨362654, by rfl⟩ : syracuseStep 483539 = 725309) B725309
theorem B811235 : Blo 479788 811235 := bstep (se 1 (by rfl) ⟨608426, by rfl⟩ : syracuseStep 811235 = 1216853) B1216853
theorem B483555 : Blo 479788 483555 := bstep (se 1 (by rfl) ⟨362666, by rfl⟩ : syracuseStep 483555 = 725333) B725333
theorem B483571 : Blo 479788 483571 := bstep (se 1 (by rfl) ⟨362678, by rfl⟩ : syracuseStep 483571 = 725357) B725357
theorem B1368323 : Blo 479788 1368323 := bstep (se 1 (by rfl) ⟨1026242, by rfl⟩ : syracuseStep 1368323 = 2052485) B2052485
theorem B483587 : Blo 479788 483587 := bstep (se 1 (by rfl) ⟨362690, by rfl⟩ : syracuseStep 483587 = 725381) B725381
theorem B483603 : Blo 479788 483603 := bstep (se 1 (by rfl) ⟨362702, by rfl⟩ : syracuseStep 483603 = 725405) B725405
theorem B483619 : Blo 479788 483619 := bstep (se 1 (by rfl) ⟨362714, by rfl⟩ : syracuseStep 483619 = 725429) B725429
theorem B483635 : Blo 479788 483635 := bstep (se 1 (by rfl) ⟨362726, by rfl⟩ : syracuseStep 483635 = 725453) B725453
theorem B483651 : Blo 479788 483651 := bstep (se 1 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 483651 = 725477) B725477
theorem B483667 : Blo 479788 483667 := bstep (se 1 (by rfl) ⟨362750, by rfl⟩ : syracuseStep 483667 = 725501) B725501
theorem B811363 : Blo 479788 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B483683 : Blo 479788 483683 := bstep (se 1 (by rfl) ⟨362762, by rfl⟩ : syracuseStep 483683 = 725525) B725525
theorem B483699 : Blo 479788 483699 := bstep (se 1 (by rfl) ⟨362774, by rfl⟩ : syracuseStep 483699 = 725549) B725549
theorem B483715 : Blo 479788 483715 := bstep (se 1 (by rfl) ⟨362786, by rfl⟩ : syracuseStep 483715 = 725573) B725573
theorem B483731 : Blo 479788 483731 := bstep (se 1 (by rfl) ⟨362798, by rfl⟩ : syracuseStep 483731 = 725597) B725597
theorem B483747 : Blo 479788 483747 := bstep (se 1 (by rfl) ⟨362810, by rfl⟩ : syracuseStep 483747 = 725621) B725621
theorem B1630637 : Blo 479788 1630637 := bstep (se 3 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 1630637 = 611489) B611489
theorem B483763 : Blo 479788 483763 := bstep (se 1 (by rfl) ⟨362822, by rfl⟩ : syracuseStep 483763 = 725645) B725645
theorem B1368515 : Blo 479788 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B483779 : Blo 479788 483779 := bstep (se 1 (by rfl) ⟨362834, by rfl⟩ : syracuseStep 483779 = 725669) B725669
theorem B1827299 : Blo 479788 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B1630691 : Blo 479788 1630691 := bstep (se 1 (by rfl) ⟨1223018, by rfl⟩ : syracuseStep 1630691 = 2446037) B2446037
theorem B811505 : Blo 479788 811505 := bstep (se 2 (by rfl) ⟨304314, by rfl⟩ : syracuseStep 811505 = 608629) B608629
theorem B2744867 : Blo 479788 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B811633 : Blo 479788 811633 := bstep (se 2 (by rfl) ⟨304362, by rfl⟩ : syracuseStep 811633 = 608725) B608725
theorem B811667 : Blo 479788 811667 := bstep (se 1 (by rfl) ⟨608750, by rfl⟩ : syracuseStep 811667 = 1217501) B1217501
theorem B1630961 : Blo 479788 1630961 := bstep (se 2 (by rfl) ⟨611610, by rfl⟩ : syracuseStep 1630961 = 1223221) B1223221
theorem B811795 : Blo 479788 811795 := bstep (se 1 (by rfl) ⟨608846, by rfl⟩ : syracuseStep 811795 = 1217693) B1217693
theorem B811937 : Blo 479788 811937 := bstep (se 2 (by rfl) ⟨304476, by rfl⟩ : syracuseStep 811937 = 608953) B608953
theorem B2614285 : Blo 479788 2614285 := bstep (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) B980357
theorem B812065 : Blo 479788 812065 := bstep (se 2 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 812065 = 609049) B609049
theorem B812099 : Blo 479788 812099 := bstep (se 1 (by rfl) ⟨609074, by rfl⟩ : syracuseStep 812099 = 1218149) B1218149
theorem B1827953 : Blo 479788 1827953 := bstep (se 2 (by rfl) ⟨685482, by rfl⟩ : syracuseStep 1827953 = 1370965) B1370965
theorem B812227 : Blo 479788 812227 := bstep (se 1 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 812227 = 1218341) B1218341
theorem B1369325 : Blo 479788 1369325 := bstep (se 3 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 1369325 = 513497) B513497
theorem B1467629 : Blo 479788 1467629 := bstep (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) B550361
theorem B1631501 : Blo 479788 1631501 := bstep (se 3 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 1631501 = 611813) B611813
theorem B1631555 : Blo 479788 1631555 := bstep (se 1 (by rfl) ⟨1223666, by rfl⟩ : syracuseStep 1631555 = 2447333) B2447333
theorem B812369 : Blo 479788 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B1369507 : Blo 479788 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B3302819 : Blo 479788 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B812497 : Blo 479788 812497 := bstep (se 2 (by rfl) ⟨304686, by rfl⟩ : syracuseStep 812497 = 609373) B609373
theorem B812531 : Blo 479788 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B1631825 : Blo 479788 1631825 := bstep (se 2 (by rfl) ⟨611934, by rfl⟩ : syracuseStep 1631825 = 1223869) B1223869
theorem B812659 : Blo 479788 812659 := bstep (se 1 (by rfl) ⟨609494, by rfl⟩ : syracuseStep 812659 = 1218989) B1218989
theorem B3139235 : Blo 479788 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B550579 : Blo 479788 550579 := bstep (se 1 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 550579 = 825869) B825869
theorem B1238723 : Blo 479788 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B812801 : Blo 479788 812801 := bstep (se 2 (by rfl) ⟨304800, by rfl⟩ : syracuseStep 812801 = 609601) B609601
theorem B812929 : Blo 479788 812929 := bstep (se 2 (by rfl) ⟨304848, by rfl⟩ : syracuseStep 812929 = 609697) B609697
theorem B1369997 : Blo 479788 1369997 := bstep (se 3 (by rfl) ⟨256874, by rfl⟩ : syracuseStep 1369997 = 513749) B513749
theorem B1959821 : Blo 479788 1959821 := bstep (se 3 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 1959821 = 734933) B734933
theorem B812963 : Blo 479788 812963 := bstep (se 1 (by rfl) ⟨609722, by rfl⟩ : syracuseStep 812963 = 1219445) B1219445
theorem B1304515 : Blo 479788 1304515 := bstep (se 1 (by rfl) ⟨978386, by rfl⟩ : syracuseStep 1304515 = 1956773) B1956773
theorem B15591365 : Blo 479788 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B649219 : Blo 479788 649219 := bstep (se 1 (by rfl) ⟨486914, by rfl⟩ : syracuseStep 649219 = 973829) B973829
theorem B1173521 : Blo 479788 1173521 := bstep (se 2 (by rfl) ⟨440070, by rfl⟩ : syracuseStep 1173521 = 880141) B880141
theorem B813091 : Blo 479788 813091 := bstep (se 1 (by rfl) ⟨609818, by rfl⟩ : syracuseStep 813091 = 1219637) B1219637
theorem B1632365 : Blo 479788 1632365 := bstep (se 3 (by rfl) ⟨306068, by rfl⟩ : syracuseStep 1632365 = 612137) B612137
theorem B4122737 : Blo 479788 4122737 := bstep (se 2 (by rfl) ⟨1546026, by rfl⟩ : syracuseStep 4122737 = 3092053) B3092053
theorem B1632419 : Blo 479788 1632419 := bstep (se 1 (by rfl) ⟨1224314, by rfl⟩ : syracuseStep 1632419 = 2448629) B2448629
theorem B813233 : Blo 479788 813233 := bstep (se 2 (by rfl) ⟨304962, by rfl⟩ : syracuseStep 813233 = 609925) B609925
theorem B911569 : Blo 479788 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B25389283 : Blo 479788 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B813361 : Blo 479788 813361 := bstep (se 2 (by rfl) ⟨305010, by rfl⟩ : syracuseStep 813361 = 610021) B610021
theorem B813395 : Blo 479788 813395 := bstep (se 1 (by rfl) ⟨610046, by rfl⟩ : syracuseStep 813395 = 1220093) B1220093
theorem B911729 : Blo 479788 911729 := bstep (se 2 (by rfl) ⟨341898, by rfl⟩ : syracuseStep 911729 = 683797) B683797
theorem B1632689 : Blo 479788 1632689 := bstep (se 2 (by rfl) ⟨612258, by rfl⟩ : syracuseStep 1632689 = 1224517) B1224517
theorem B813523 : Blo 479788 813523 := bstep (se 1 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 813523 = 1220285) B1220285
theorem B1829411 : Blo 479788 1829411 := bstep (se 1 (by rfl) ⟨1372058, by rfl⟩ : syracuseStep 1829411 = 2744117) B2744117
theorem B2058787 : Blo 479788 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B1829425 : Blo 479788 1829425 := bstep (se 2 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 1829425 = 1372069) B1372069
theorem B813665 : Blo 479788 813665 := bstep (se 2 (by rfl) ⟨305124, by rfl⟩ : syracuseStep 813665 = 610249) B610249
theorem B813793 : Blo 479788 813793 := bstep (se 2 (by rfl) ⟨305172, by rfl⟩ : syracuseStep 813793 = 610345) B610345
theorem B5073635 : Blo 479788 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B912131 : Blo 479788 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B813827 : Blo 479788 813827 := bstep (se 1 (by rfl) ⟨610370, by rfl⟩ : syracuseStep 813827 = 1220741) B1220741
theorem B813955 : Blo 479788 813955 := bstep (se 1 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 813955 = 1220933) B1220933
theorem B977827 : Blo 479788 977827 := bstep (se 1 (by rfl) ⟨733370, by rfl⟩ : syracuseStep 977827 = 1466741) B1466741
theorem B3533765 : Blo 479788 3533765 := bstep (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) B662581
theorem B814097 : Blo 479788 814097 := bstep (se 2 (by rfl) ⟨305286, by rfl⟩ : syracuseStep 814097 = 610573) B610573
theorem B1371181 : Blo 479788 1371181 := bstep (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) B514193
theorem B3304547 : Blo 479788 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B814225 : Blo 479788 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B814259 : Blo 479788 814259 := bstep (se 1 (by rfl) ⟨610694, by rfl⟩ : syracuseStep 814259 = 1221389) B1221389
theorem B1109297 : Blo 479788 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B814387 : Blo 479788 814387 := bstep (se 1 (by rfl) ⟨610790, by rfl⟩ : syracuseStep 814387 = 1221581) B1221581
theorem B1306019 : Blo 479788 1306019 := bstep (se 1 (by rfl) ⟨979514, by rfl⟩ : syracuseStep 1306019 = 1959029) B1959029
theorem B814529 : Blo 479788 814529 := bstep (se 2 (by rfl) ⟨305448, by rfl⟩ : syracuseStep 814529 = 610897) B610897
theorem B1306115 : Blo 479788 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B683569 : Blo 479788 683569 := bstep (se 2 (by rfl) ⟨256338, by rfl⟩ : syracuseStep 683569 = 512677) B512677
theorem B814657 : Blo 479788 814657 := bstep (se 2 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 814657 = 610993) B610993
theorem B978499 : Blo 479788 978499 := bstep (se 1 (by rfl) ⟨733874, by rfl⟩ : syracuseStep 978499 = 1467749) B1467749
theorem B814691 : Blo 479788 814691 := bstep (se 1 (by rfl) ⟨611018, by rfl⟩ : syracuseStep 814691 = 1222037) B1222037
theorem B913027 : Blo 479788 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B1732259 : Blo 479788 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B814819 : Blo 479788 814819 := bstep (se 1 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 814819 = 1222229) B1222229
theorem B913187 : Blo 479788 913187 := bstep (se 1 (by rfl) ⟨684890, by rfl⟩ : syracuseStep 913187 = 1369781) B1369781
theorem B814961 : Blo 479788 814961 := bstep (se 2 (by rfl) ⟨305610, by rfl⟩ : syracuseStep 814961 = 611221) B611221
theorem B683905 : Blo 479788 683905 := bstep (se 2 (by rfl) ⟨256464, by rfl⟩ : syracuseStep 683905 = 512929) B512929
theorem B1830883 : Blo 479788 1830883 := bstep (se 1 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 1830883 = 2746325) B2746325
theorem B815089 : Blo 479788 815089 := bstep (se 2 (by rfl) ⟨305658, by rfl⟩ : syracuseStep 815089 = 611317) B611317
theorem B815123 : Blo 479788 815123 := bstep (se 1 (by rfl) ⟨611342, by rfl⟩ : syracuseStep 815123 = 1222685) B1222685
theorem B1372241 : Blo 479788 1372241 := bstep (se 2 (by rfl) ⟨514590, by rfl⟩ : syracuseStep 1372241 = 1029181) B1029181
theorem B815251 : Blo 479788 815251 := bstep (se 1 (by rfl) ⟨611438, by rfl⟩ : syracuseStep 815251 = 1222877) B1222877
theorem B520435 : Blo 479788 520435 := bstep (se 1 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 520435 = 780653) B780653
theorem B815393 : Blo 479788 815393 := bstep (se 2 (by rfl) ⟨305772, by rfl⟩ : syracuseStep 815393 = 611545) B611545
theorem B880931 : Blo 479788 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B815521 : Blo 479788 815521 := bstep (se 2 (by rfl) ⟨305820, by rfl⟩ : syracuseStep 815521 = 611641) B611641
theorem B815555 : Blo 479788 815555 := bstep (se 1 (by rfl) ⟨611666, by rfl⟩ : syracuseStep 815555 = 1223333) B1223333
theorem B684497 : Blo 479788 684497 := bstep (se 2 (by rfl) ⟨256686, by rfl⟩ : syracuseStep 684497 = 513373) B513373
theorem B815683 : Blo 479788 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B979537 : Blo 479788 979537 := bstep (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) B734653
theorem B979651 : Blo 479788 979651 := bstep (se 1 (by rfl) ⟨734738, by rfl⟩ : syracuseStep 979651 = 1469477) B1469477
theorem B815825 : Blo 479788 815825 := bstep (se 2 (by rfl) ⟨305934, by rfl⟩ : syracuseStep 815825 = 611869) B611869
theorem B1372913 : Blo 479788 1372913 := bstep (se 2 (by rfl) ⟨514842, by rfl⟩ : syracuseStep 1372913 = 1029685) B1029685
theorem B881425 : Blo 479788 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B914257 : Blo 479788 914257 := bstep (se 2 (by rfl) ⟨342846, by rfl⟩ : syracuseStep 914257 = 685693) B685693
theorem B815953 : Blo 479788 815953 := bstep (se 2 (by rfl) ⟨305982, by rfl⟩ : syracuseStep 815953 = 611965) B611965
theorem B815987 : Blo 479788 815987 := bstep (se 1 (by rfl) ⟨611990, by rfl⟩ : syracuseStep 815987 = 1223981) B1223981
theorem B2061233 : Blo 479788 2061233 := bstep (se 2 (by rfl) ⟨772962, by rfl⟩ : syracuseStep 2061233 = 1545925) B1545925
theorem B685027 : Blo 479788 685027 := bstep (se 1 (by rfl) ⟨513770, by rfl⟩ : syracuseStep 685027 = 1027541) B1027541
theorem B816115 : Blo 479788 816115 := bstep (se 1 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 816115 = 1224173) B1224173
theorem B1537069 : Blo 479788 1537069 := bstep (se 3 (by rfl) ⟨288200, by rfl⟩ : syracuseStep 1537069 = 576401) B576401
theorem B816257 : Blo 479788 816257 := bstep (se 2 (by rfl) ⟨306096, by rfl⟩ : syracuseStep 816257 = 612193) B612193
theorem B816385 : Blo 479788 816385 := bstep (se 2 (by rfl) ⟨306144, by rfl⟩ : syracuseStep 816385 = 612289) B612289
theorem B685363 : Blo 479788 685363 := bstep (se 1 (by rfl) ⟨514022, by rfl⟩ : syracuseStep 685363 = 1028045) B1028045
theorem B488755 : Blo 479788 488755 := bstep (se 1 (by rfl) ⟨366566, by rfl⟩ : syracuseStep 488755 = 733133) B733133
theorem B1373699 : Blo 479788 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B2324173 : Blo 479788 2324173 := bstep (se 3 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 2324173 = 871565) B871565
theorem B980689 : Blo 479788 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B980753 : Blo 479788 980753 := bstep (se 2 (by rfl) ⟨367782, by rfl⟩ : syracuseStep 980753 = 735565) B735565
theorem B1374029 : Blo 479788 1374029 := bstep (se 3 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 1374029 = 515261) B515261
theorem B685921 : Blo 479788 685921 := bstep (se 2 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 685921 = 514441) B514441
theorem B915313 : Blo 479788 915313 := bstep (se 2 (by rfl) ⟨343242, by rfl⟩ : syracuseStep 915313 = 686485) B686485
theorem B784243 : Blo 479788 784243 := bstep (se 1 (by rfl) ⟨588182, by rfl⟩ : syracuseStep 784243 = 1176365) B1176365
theorem B685955 : Blo 479788 685955 := bstep (se 1 (by rfl) ⟨514466, by rfl⟩ : syracuseStep 685955 = 1028933) B1028933
theorem B1374097 : Blo 479788 1374097 := bstep (se 2 (by rfl) ⟨515286, by rfl⟩ : syracuseStep 1374097 = 1030573) B1030573
theorem B4126733 : Blo 479788 4126733 := bstep (se 3 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 4126733 = 1547525) B1547525
theorem B1734797 : Blo 479788 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B1833101 : Blo 479788 1833101 := bstep (se 3 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 1833101 = 687413) B687413
theorem B1374371 : Blo 479788 1374371 := bstep (se 1 (by rfl) ⟨1030778, by rfl⟩ : syracuseStep 1374371 = 2061557) B2061557
theorem B915715 : Blo 479788 915715 := bstep (se 1 (by rfl) ⟨686786, by rfl⟩ : syracuseStep 915715 = 1373573) B1373573
theorem B915761 : Blo 479788 915761 := bstep (se 2 (by rfl) ⟨343410, by rfl⟩ : syracuseStep 915761 = 686821) B686821
theorem B1079729 : Blo 479788 1079729 := bstep (se 2 (by rfl) ⟨404898, by rfl⟩ : syracuseStep 1079729 = 809797) B809797
theorem B686513 : Blo 479788 686513 := bstep (se 2 (by rfl) ⟨257442, by rfl⟩ : syracuseStep 686513 = 514885) B514885
theorem B1079747 : Blo 479788 1079747 := bstep (se 1 (by rfl) ⟨809810, by rfl⟩ : syracuseStep 1079747 = 1619621) B1619621
theorem B588259 : Blo 479788 588259 := bstep (se 1 (by rfl) ⟨441194, by rfl⟩ : syracuseStep 588259 = 882389) B882389
theorem B686593 : Blo 479788 686593 := bstep (se 2 (by rfl) ⟨257472, by rfl⟩ : syracuseStep 686593 = 514945) B514945
theorem B916049 : Blo 479788 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B1080017 : Blo 479788 1080017 := bstep (se 2 (by rfl) ⟨405006, by rfl⟩ : syracuseStep 1080017 = 810013) B810013
theorem B1080035 : Blo 479788 1080035 := bstep (se 1 (by rfl) ⟨810026, by rfl⟩ : syracuseStep 1080035 = 1620053) B1620053
theorem B1538851 : Blo 479788 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B719699 : Blo 479788 719699 := bstep (se 1 (by rfl) ⟨539774, by rfl⟩ : syracuseStep 719699 = 1079549) B1079549
theorem B719729 : Blo 479788 719729 := bstep (se 2 (by rfl) ⟨269898, by rfl⟩ : syracuseStep 719729 = 539797) B539797
theorem B719747 : Blo 479788 719747 := bstep (se 1 (by rfl) ⟨539810, by rfl⟩ : syracuseStep 719747 = 1079621) B1079621
theorem B719777 : Blo 479788 719777 := bstep (se 2 (by rfl) ⟨269916, by rfl⟩ : syracuseStep 719777 = 539833) B539833
theorem B719795 : Blo 479788 719795 := bstep (se 1 (by rfl) ⟨539846, by rfl⟩ : syracuseStep 719795 = 1079693) B1079693
theorem B719825 : Blo 479788 719825 := bstep (se 2 (by rfl) ⟨269934, by rfl⟩ : syracuseStep 719825 = 539869) B539869
theorem B719843 : Blo 479788 719843 := bstep (se 1 (by rfl) ⟨539882, by rfl⟩ : syracuseStep 719843 = 1079765) B1079765
theorem B1375213 : Blo 479788 1375213 := bstep (se 3 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 1375213 = 515705) B515705
theorem B1080305 : Blo 479788 1080305 := bstep (se 2 (by rfl) ⟨405114, by rfl⟩ : syracuseStep 1080305 = 810229) B810229
theorem B719873 : Blo 479788 719873 := bstep (se 2 (by rfl) ⟨269952, by rfl⟩ : syracuseStep 719873 = 539905) B539905
theorem B1080323 : Blo 479788 1080323 := bstep (se 1 (by rfl) ⟨810242, by rfl⟩ : syracuseStep 1080323 = 1620485) B1620485
theorem B719891 : Blo 479788 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B719921 : Blo 479788 719921 := bstep (se 2 (by rfl) ⟨269970, by rfl⟩ : syracuseStep 719921 = 539941) B539941
theorem B719939 : Blo 479788 719939 := bstep (se 1 (by rfl) ⟨539954, by rfl⟩ : syracuseStep 719939 = 1079909) B1079909
theorem B719969 : Blo 479788 719969 := bstep (se 2 (by rfl) ⟨269988, by rfl⟩ : syracuseStep 719969 = 539977) B539977
theorem B719987 : Blo 479788 719987 := bstep (se 1 (by rfl) ⟨539990, by rfl⟩ : syracuseStep 719987 = 1079981) B1079981
theorem B5209229 : Blo 479788 5209229 := bstep (se 3 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 5209229 = 1953461) B1953461
theorem B4947085 : Blo 479788 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B1375373 : Blo 479788 1375373 := bstep (se 3 (by rfl) ⟨257882, by rfl⟩ : syracuseStep 1375373 = 515765) B515765
theorem B720017 : Blo 479788 720017 := bstep (se 2 (by rfl) ⟨270006, by rfl⟩ : syracuseStep 720017 = 540013) B540013
theorem B720035 : Blo 479788 720035 := bstep (se 1 (by rfl) ⟨540026, by rfl⟩ : syracuseStep 720035 = 1080053) B1080053
theorem B720065 : Blo 479788 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B720083 : Blo 479788 720083 := bstep (se 1 (by rfl) ⟨540062, by rfl⟩ : syracuseStep 720083 = 1080125) B1080125
theorem B1539299 : Blo 479788 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B720113 : Blo 479788 720113 := bstep (se 2 (by rfl) ⟨270042, by rfl⟩ : syracuseStep 720113 = 540085) B540085
theorem B720131 : Blo 479788 720131 := bstep (se 1 (by rfl) ⟨540098, by rfl⟩ : syracuseStep 720131 = 1080197) B1080197
theorem B1080593 : Blo 479788 1080593 := bstep (se 2 (by rfl) ⟨405222, by rfl⟩ : syracuseStep 1080593 = 810445) B810445
theorem B687379 : Blo 479788 687379 := bstep (se 1 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 687379 = 1031069) B1031069
theorem B720161 : Blo 479788 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B916771 : Blo 479788 916771 := bstep (se 1 (by rfl) ⟨687578, by rfl⟩ : syracuseStep 916771 = 1375157) B1375157
theorem B1080611 : Blo 479788 1080611 := bstep (se 1 (by rfl) ⟨810458, by rfl⟩ : syracuseStep 1080611 = 1620917) B1620917
theorem B720179 : Blo 479788 720179 := bstep (se 1 (by rfl) ⟨540134, by rfl⟩ : syracuseStep 720179 = 1080269) B1080269
theorem B1375555 : Blo 479788 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B720209 : Blo 479788 720209 := bstep (se 2 (by rfl) ⟨270078, by rfl⟩ : syracuseStep 720209 = 540157) B540157
theorem B720227 : Blo 479788 720227 := bstep (se 1 (by rfl) ⟨540170, by rfl⟩ : syracuseStep 720227 = 1080341) B1080341
theorem B720257 : Blo 479788 720257 := bstep (se 2 (by rfl) ⟨270096, by rfl⟩ : syracuseStep 720257 = 540193) B540193
theorem B720275 : Blo 479788 720275 := bstep (se 1 (by rfl) ⟨540206, by rfl⟩ : syracuseStep 720275 = 1080413) B1080413
theorem B720305 : Blo 479788 720305 := bstep (se 2 (by rfl) ⟨270114, by rfl⟩ : syracuseStep 720305 = 540229) B540229
theorem B720323 : Blo 479788 720323 := bstep (se 1 (by rfl) ⟨540242, by rfl⟩ : syracuseStep 720323 = 1080485) B1080485
theorem B720353 : Blo 479788 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B720371 : Blo 479788 720371 := bstep (se 1 (by rfl) ⟨540278, by rfl⟩ : syracuseStep 720371 = 1080557) B1080557
theorem B720401 : Blo 479788 720401 := bstep (se 2 (by rfl) ⟨270150, by rfl⟩ : syracuseStep 720401 = 540301) B540301
theorem B720419 : Blo 479788 720419 := bstep (se 1 (by rfl) ⟨540314, by rfl⟩ : syracuseStep 720419 = 1080629) B1080629
theorem B1080881 : Blo 479788 1080881 := bstep (se 2 (by rfl) ⟨405330, by rfl⟩ : syracuseStep 1080881 = 810661) B810661
theorem B720449 : Blo 479788 720449 := bstep (se 2 (by rfl) ⟨270168, by rfl⟩ : syracuseStep 720449 = 540337) B540337
theorem B1080899 : Blo 479788 1080899 := bstep (se 1 (by rfl) ⟨810674, by rfl⟩ : syracuseStep 1080899 = 1621349) B1621349
theorem B720467 : Blo 479788 720467 := bstep (se 1 (by rfl) ⟨540350, by rfl⟩ : syracuseStep 720467 = 1080701) B1080701
theorem B720497 : Blo 479788 720497 := bstep (se 2 (by rfl) ⟨270186, by rfl⟩ : syracuseStep 720497 = 540373) B540373
theorem B720515 : Blo 479788 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B720545 : Blo 479788 720545 := bstep (se 2 (by rfl) ⟨270204, by rfl⟩ : syracuseStep 720545 = 540409) B540409
theorem B720563 : Blo 479788 720563 := bstep (se 1 (by rfl) ⟨540422, by rfl⟩ : syracuseStep 720563 = 1080845) B1080845
theorem B720593 : Blo 479788 720593 := bstep (se 2 (by rfl) ⟨270222, by rfl⟩ : syracuseStep 720593 = 540445) B540445
theorem B720611 : Blo 479788 720611 := bstep (se 1 (by rfl) ⟨540458, by rfl⟩ : syracuseStep 720611 = 1080917) B1080917
theorem B917219 : Blo 479788 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B687857 : Blo 479788 687857 := bstep (se 2 (by rfl) ⟨257946, by rfl⟩ : syracuseStep 687857 = 515893) B515893
theorem B720641 : Blo 479788 720641 := bstep (se 2 (by rfl) ⟨270240, by rfl⟩ : syracuseStep 720641 = 540481) B540481
theorem B720659 : Blo 479788 720659 := bstep (se 1 (by rfl) ⟨540494, by rfl⟩ : syracuseStep 720659 = 1080989) B1080989
theorem B720689 : Blo 479788 720689 := bstep (se 2 (by rfl) ⟨270258, by rfl⟩ : syracuseStep 720689 = 540517) B540517
theorem B720707 : Blo 479788 720707 := bstep (se 1 (by rfl) ⟨540530, by rfl⟩ : syracuseStep 720707 = 1081061) B1081061
theorem B1081169 : Blo 479788 1081169 := bstep (se 2 (by rfl) ⟨405438, by rfl⟩ : syracuseStep 1081169 = 810877) B810877
theorem B720737 : Blo 479788 720737 := bstep (se 2 (by rfl) ⟨270276, by rfl⟩ : syracuseStep 720737 = 540553) B540553
theorem B1081187 : Blo 479788 1081187 := bstep (se 1 (by rfl) ⟨810890, by rfl⟩ : syracuseStep 1081187 = 1621781) B1621781
theorem B687971 : Blo 479788 687971 := bstep (se 1 (by rfl) ⟨515978, by rfl⟩ : syracuseStep 687971 = 1031957) B1031957
theorem B720755 : Blo 479788 720755 := bstep (se 1 (by rfl) ⟨540566, by rfl⟩ : syracuseStep 720755 = 1081133) B1081133
theorem B720785 : Blo 479788 720785 := bstep (se 2 (by rfl) ⟨270294, by rfl⟩ : syracuseStep 720785 = 540589) B540589
theorem B720803 : Blo 479788 720803 := bstep (se 1 (by rfl) ⟨540602, by rfl⟩ : syracuseStep 720803 = 1081205) B1081205
theorem B688051 : Blo 479788 688051 := bstep (se 1 (by rfl) ⟨516038, by rfl⟩ : syracuseStep 688051 = 1032077) B1032077
theorem B720833 : Blo 479788 720833 := bstep (se 2 (by rfl) ⟨270312, by rfl⟩ : syracuseStep 720833 = 540625) B540625
theorem B720851 : Blo 479788 720851 := bstep (se 1 (by rfl) ⟨540638, by rfl⟩ : syracuseStep 720851 = 1081277) B1081277
theorem B720881 : Blo 479788 720881 := bstep (se 2 (by rfl) ⟨270330, by rfl⟩ : syracuseStep 720881 = 540661) B540661
theorem B1081367 : Blo 479788 1081367 := bstep (se 1 (by rfl) ⟨811025, by rfl⟩ : syracuseStep 1081367 = 1622051) B1622051
theorem B720971 : Blo 479788 720971 := bstep (se 1 (by rfl) ⟨540728, by rfl⟩ : syracuseStep 720971 = 1081457) B1081457
theorem B720983 : Blo 479788 720983 := bstep (se 1 (by rfl) ⟨540737, by rfl⟩ : syracuseStep 720983 = 1081475) B1081475
theorem B2752613 : Blo 479788 2752613 := bstep (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) B516115
theorem B688267 : Blo 479788 688267 := bstep (se 1 (by rfl) ⟨516200, by rfl⟩ : syracuseStep 688267 = 1032401) B1032401
theorem B688279 : Blo 479788 688279 := bstep (se 1 (by rfl) ⟨516209, by rfl⟩ : syracuseStep 688279 = 1032419) B1032419
theorem B721049 : Blo 479788 721049 := bstep (se 2 (by rfl) ⟨270393, by rfl⟩ : syracuseStep 721049 = 540787) B540787
theorem B1081547 : Blo 479788 1081547 := bstep (se 1 (by rfl) ⟨811160, by rfl⟩ : syracuseStep 1081547 = 1622321) B1622321
theorem B1081601 : Blo 479788 1081601 := bstep (se 2 (by rfl) ⟨405600, by rfl⟩ : syracuseStep 1081601 = 811201) B811201
theorem B721163 : Blo 479788 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B721175 : Blo 479788 721175 := bstep (se 1 (by rfl) ⟨540881, by rfl⟩ : syracuseStep 721175 = 1081763) B1081763
theorem B721241 : Blo 479788 721241 := bstep (se 2 (by rfl) ⟨270465, by rfl⟩ : syracuseStep 721241 = 540931) B540931
theorem B721355 : Blo 479788 721355 := bstep (se 1 (by rfl) ⟨541016, by rfl⟩ : syracuseStep 721355 = 1082033) B1082033
theorem B917963 : Blo 479788 917963 := bstep (se 1 (by rfl) ⟨688472, by rfl⟩ : syracuseStep 917963 = 1376945) B1376945
theorem B721367 : Blo 479788 721367 := bstep (se 1 (by rfl) ⟨541025, by rfl⟩ : syracuseStep 721367 = 1082051) B1082051
theorem B1081817 : Blo 479788 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B721433 : Blo 479788 721433 := bstep (se 2 (by rfl) ⟨270537, by rfl⟩ : syracuseStep 721433 = 541075) B541075
theorem B1081907 : Blo 479788 1081907 := bstep (se 1 (by rfl) ⟨811430, by rfl⟩ : syracuseStep 1081907 = 1622861) B1622861
theorem B1081943 : Blo 479788 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B918145 : Blo 479788 918145 := bstep (se 2 (by rfl) ⟨344304, by rfl⟩ : syracuseStep 918145 = 688609) B688609
theorem B721547 : Blo 479788 721547 := bstep (se 1 (by rfl) ⟨541160, by rfl⟩ : syracuseStep 721547 = 1082321) B1082321
theorem B721559 : Blo 479788 721559 := bstep (se 1 (by rfl) ⟨541169, by rfl⟩ : syracuseStep 721559 = 1082339) B1082339
theorem B721625 : Blo 479788 721625 := bstep (se 2 (by rfl) ⟨270609, by rfl⟩ : syracuseStep 721625 = 541219) B541219
theorem B1082123 : Blo 479788 1082123 := bstep (se 1 (by rfl) ⟨811592, by rfl⟩ : syracuseStep 1082123 = 1623185) B1623185
theorem B2753297 : Blo 479788 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B1082177 : Blo 479788 1082177 := bstep (se 2 (by rfl) ⟨405816, by rfl⟩ : syracuseStep 1082177 = 811633) B811633
theorem B1540939 : Blo 479788 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B721739 : Blo 479788 721739 := bstep (se 1 (by rfl) ⟨541304, by rfl⟩ : syracuseStep 721739 = 1082609) B1082609
theorem B721751 : Blo 479788 721751 := bstep (se 1 (by rfl) ⟨541313, by rfl⟩ : syracuseStep 721751 = 1082627) B1082627
theorem B3900311 : Blo 479788 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B721817 : Blo 479788 721817 := bstep (se 2 (by rfl) ⟨270681, by rfl⟩ : syracuseStep 721817 = 541363) B541363
theorem B721931 : Blo 479788 721931 := bstep (se 1 (by rfl) ⟨541448, by rfl⟩ : syracuseStep 721931 = 1082897) B1082897
theorem B721943 : Blo 479788 721943 := bstep (se 1 (by rfl) ⟨541457, by rfl⟩ : syracuseStep 721943 = 1082915) B1082915
theorem B1082393 : Blo 479788 1082393 := bstep (se 2 (by rfl) ⟨405897, by rfl⟩ : syracuseStep 1082393 = 811795) B811795
theorem B722009 : Blo 479788 722009 := bstep (se 2 (by rfl) ⟨270753, by rfl⟩ : syracuseStep 722009 = 541507) B541507
theorem B1082483 : Blo 479788 1082483 := bstep (se 1 (by rfl) ⟨811862, by rfl⟩ : syracuseStep 1082483 = 1623725) B1623725
theorem B1082519 : Blo 479788 1082519 := bstep (se 1 (by rfl) ⟨811889, by rfl⟩ : syracuseStep 1082519 = 1623779) B1623779
theorem B722123 : Blo 479788 722123 := bstep (se 1 (by rfl) ⟨541592, by rfl⟩ : syracuseStep 722123 = 1083185) B1083185
theorem B722135 : Blo 479788 722135 := bstep (se 1 (by rfl) ⟨541601, by rfl⟩ : syracuseStep 722135 = 1083203) B1083203
theorem B722201 : Blo 479788 722201 := bstep (se 2 (by rfl) ⟨270825, by rfl⟩ : syracuseStep 722201 = 541651) B541651
theorem B1082699 : Blo 479788 1082699 := bstep (se 1 (by rfl) ⟨812024, by rfl⟩ : syracuseStep 1082699 = 1624049) B1624049
theorem B4130149 : Blo 479788 4130149 := bstep (se 4 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 4130149 = 774403) B774403
theorem B1082753 : Blo 479788 1082753 := bstep (se 2 (by rfl) ⟨406032, by rfl⟩ : syracuseStep 1082753 = 812065) B812065
theorem B722315 : Blo 479788 722315 := bstep (se 1 (by rfl) ⟨541736, by rfl⟩ : syracuseStep 722315 = 1083473) B1083473
theorem B722327 : Blo 479788 722327 := bstep (se 1 (by rfl) ⟨541745, by rfl⟩ : syracuseStep 722327 = 1083491) B1083491
theorem B1541555 : Blo 479788 1541555 := bstep (se 1 (by rfl) ⟨1156166, by rfl⟩ : syracuseStep 1541555 = 2312333) B2312333
theorem B722393 : Blo 479788 722393 := bstep (se 2 (by rfl) ⟨270897, by rfl⟩ : syracuseStep 722393 = 541795) B541795
theorem B722507 : Blo 479788 722507 := bstep (se 1 (by rfl) ⟨541880, by rfl⟩ : syracuseStep 722507 = 1083761) B1083761
theorem B722519 : Blo 479788 722519 := bstep (se 1 (by rfl) ⟨541889, by rfl⟩ : syracuseStep 722519 = 1083779) B1083779
theorem B1082969 : Blo 479788 1082969 := bstep (se 2 (by rfl) ⟨406113, by rfl⟩ : syracuseStep 1082969 = 812227) B812227
theorem B722585 : Blo 479788 722585 := bstep (se 2 (by rfl) ⟨270969, by rfl⟩ : syracuseStep 722585 = 541939) B541939
theorem B3671729 : Blo 479788 3671729 := bstep (se 2 (by rfl) ⟨1376898, by rfl⟩ : syracuseStep 3671729 = 2753797) B2753797
theorem B1083059 : Blo 479788 1083059 := bstep (se 1 (by rfl) ⟨812294, by rfl⟩ : syracuseStep 1083059 = 1624589) B1624589
theorem B1541825 : Blo 479788 1541825 := bstep (se 2 (by rfl) ⟨578184, by rfl⟩ : syracuseStep 1541825 = 1156369) B1156369
theorem B1083095 : Blo 479788 1083095 := bstep (se 1 (by rfl) ⟨812321, by rfl⟩ : syracuseStep 1083095 = 1624643) B1624643
theorem B722699 : Blo 479788 722699 := bstep (se 1 (by rfl) ⟨542024, by rfl⟩ : syracuseStep 722699 = 1084049) B1084049
theorem B722711 : Blo 479788 722711 := bstep (se 1 (by rfl) ⟨542033, by rfl⟩ : syracuseStep 722711 = 1084067) B1084067
theorem B722777 : Blo 479788 722777 := bstep (se 2 (by rfl) ⟨271041, by rfl⟩ : syracuseStep 722777 = 542083) B542083
theorem B1083275 : Blo 479788 1083275 := bstep (se 1 (by rfl) ⟨812456, by rfl⟩ : syracuseStep 1083275 = 1624913) B1624913
theorem B1083329 : Blo 479788 1083329 := bstep (se 2 (by rfl) ⟨406248, by rfl⟩ : syracuseStep 1083329 = 812497) B812497
theorem B722891 : Blo 479788 722891 := bstep (se 1 (by rfl) ⟨542168, by rfl⟩ : syracuseStep 722891 = 1084337) B1084337
theorem B722903 : Blo 479788 722903 := bstep (se 1 (by rfl) ⟨542177, by rfl⟩ : syracuseStep 722903 = 1084355) B1084355
theorem B722969 : Blo 479788 722969 := bstep (se 2 (by rfl) ⟨271113, by rfl⟩ : syracuseStep 722969 = 542227) B542227
theorem B723083 : Blo 479788 723083 := bstep (se 1 (by rfl) ⟨542312, by rfl⟩ : syracuseStep 723083 = 1084625) B1084625
theorem B1214615 : Blo 479788 1214615 := bstep (se 1 (by rfl) ⟨910961, by rfl⟩ : syracuseStep 1214615 = 1821923) B1821923
theorem B723095 : Blo 479788 723095 := bstep (se 1 (by rfl) ⟨542321, by rfl⟩ : syracuseStep 723095 = 1084643) B1084643
theorem B1083545 : Blo 479788 1083545 := bstep (se 2 (by rfl) ⟨406329, by rfl⟩ : syracuseStep 1083545 = 812659) B812659
theorem B3672215 : Blo 479788 3672215 := bstep (se 1 (by rfl) ⟨2754161, by rfl⟩ : syracuseStep 3672215 = 5508323) B5508323
theorem B723161 : Blo 479788 723161 := bstep (se 2 (by rfl) ⟨271185, by rfl⟩ : syracuseStep 723161 = 542371) B542371
theorem B1083635 : Blo 479788 1083635 := bstep (se 1 (by rfl) ⟨812726, by rfl⟩ : syracuseStep 1083635 = 1625453) B1625453
theorem B1083671 : Blo 479788 1083671 := bstep (se 1 (by rfl) ⟨812753, by rfl⟩ : syracuseStep 1083671 = 1625507) B1625507
theorem B4131107 : Blo 479788 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B723275 : Blo 479788 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B723287 : Blo 479788 723287 := bstep (se 1 (by rfl) ⟨542465, by rfl⟩ : syracuseStep 723287 = 1084931) B1084931
theorem B723353 : Blo 479788 723353 := bstep (se 2 (by rfl) ⟨271257, by rfl⟩ : syracuseStep 723353 = 542515) B542515
theorem B6195635 : Blo 479788 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B1083851 : Blo 479788 1083851 := bstep (se 1 (by rfl) ⟨812888, by rfl⟩ : syracuseStep 1083851 = 1625777) B1625777
theorem B1083905 : Blo 479788 1083905 := bstep (se 2 (by rfl) ⟨406464, by rfl⟩ : syracuseStep 1083905 = 812929) B812929
theorem B723467 : Blo 479788 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B723479 : Blo 479788 723479 := bstep (se 1 (by rfl) ⟨542609, by rfl⟩ : syracuseStep 723479 = 1085219) B1085219
theorem B723545 : Blo 479788 723545 := bstep (se 2 (by rfl) ⟨271329, by rfl⟩ : syracuseStep 723545 = 542659) B542659
theorem B1739353 : Blo 479788 1739353 := bstep (se 2 (by rfl) ⟨652257, by rfl⟩ : syracuseStep 1739353 = 1304515) B1304515
theorem B723659 : Blo 479788 723659 := bstep (se 1 (by rfl) ⟨542744, by rfl⟩ : syracuseStep 723659 = 1085489) B1085489
theorem B723671 : Blo 479788 723671 := bstep (se 1 (by rfl) ⟨542753, by rfl⟩ : syracuseStep 723671 = 1085507) B1085507
theorem B1084121 : Blo 479788 1084121 := bstep (se 2 (by rfl) ⟨406545, by rfl⟩ : syracuseStep 1084121 = 813091) B813091
theorem B723737 : Blo 479788 723737 := bstep (se 2 (by rfl) ⟨271401, by rfl⟩ : syracuseStep 723737 = 542803) B542803
theorem B1215283 : Blo 479788 1215283 := bstep (se 1 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 1215283 = 1822925) B1822925
theorem B1084211 : Blo 479788 1084211 := bstep (se 1 (by rfl) ⟨813158, by rfl⟩ : syracuseStep 1084211 = 1626317) B1626317
theorem B1084247 : Blo 479788 1084247 := bstep (se 1 (by rfl) ⟨813185, by rfl⟩ : syracuseStep 1084247 = 1626371) B1626371
theorem B723851 : Blo 479788 723851 := bstep (se 1 (by rfl) ⟨542888, by rfl⟩ : syracuseStep 723851 = 1085777) B1085777
theorem B2231185 : Blo 479788 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B723863 : Blo 479788 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B1215425 : Blo 479788 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B33852377 : Blo 479788 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B723929 : Blo 479788 723929 := bstep (se 2 (by rfl) ⟨271473, by rfl⟩ : syracuseStep 723929 = 542947) B542947
theorem B1084427 : Blo 479788 1084427 := bstep (se 1 (by rfl) ⟨813320, by rfl⟩ : syracuseStep 1084427 = 1626641) B1626641
theorem B1084481 : Blo 479788 1084481 := bstep (se 2 (by rfl) ⟨406680, by rfl⟩ : syracuseStep 1084481 = 813361) B813361
theorem B724043 : Blo 479788 724043 := bstep (se 1 (by rfl) ⟨543032, by rfl⟩ : syracuseStep 724043 = 1086065) B1086065
theorem B724055 : Blo 479788 724055 := bstep (se 1 (by rfl) ⟨543041, by rfl⟩ : syracuseStep 724055 = 1086083) B1086083
theorem B724121 : Blo 479788 724121 := bstep (se 2 (by rfl) ⟨271545, by rfl⟩ : syracuseStep 724121 = 543091) B543091
theorem B724235 : Blo 479788 724235 := bstep (se 1 (by rfl) ⟨543176, by rfl⟩ : syracuseStep 724235 = 1086353) B1086353
theorem B724247 : Blo 479788 724247 := bstep (se 1 (by rfl) ⟨543185, by rfl⟩ : syracuseStep 724247 = 1086371) B1086371
theorem B1084697 : Blo 479788 1084697 := bstep (se 2 (by rfl) ⟨406761, by rfl⟩ : syracuseStep 1084697 = 813523) B813523
theorem B724313 : Blo 479788 724313 := bstep (se 2 (by rfl) ⟨271617, by rfl⟩ : syracuseStep 724313 = 543235) B543235
theorem B1084787 : Blo 479788 1084787 := bstep (se 1 (by rfl) ⟨813590, by rfl⟩ : syracuseStep 1084787 = 1627181) B1627181
theorem B1084823 : Blo 479788 1084823 := bstep (se 1 (by rfl) ⟨813617, by rfl⟩ : syracuseStep 1084823 = 1627235) B1627235
theorem B724427 : Blo 479788 724427 := bstep (se 1 (by rfl) ⟨543320, by rfl⟩ : syracuseStep 724427 = 1086641) B1086641
theorem B724439 : Blo 479788 724439 := bstep (se 1 (by rfl) ⟨543329, by rfl⟩ : syracuseStep 724439 = 1086659) B1086659
theorem B724505 : Blo 479788 724505 := bstep (se 2 (by rfl) ⟨271689, by rfl⟩ : syracuseStep 724505 = 543379) B543379
theorem B1642049 : Blo 479788 1642049 := bstep (se 2 (by rfl) ⟨615768, by rfl⟩ : syracuseStep 1642049 = 1231537) B1231537
theorem B1085003 : Blo 479788 1085003 := bstep (se 1 (by rfl) ⟨813752, by rfl⟩ : syracuseStep 1085003 = 1627505) B1627505
theorem B1085057 : Blo 479788 1085057 := bstep (se 2 (by rfl) ⟨406896, by rfl⟩ : syracuseStep 1085057 = 813793) B813793
theorem B724619 : Blo 479788 724619 := bstep (se 1 (by rfl) ⟨543464, by rfl⟩ : syracuseStep 724619 = 1086929) B1086929
theorem B724631 : Blo 479788 724631 := bstep (se 1 (by rfl) ⟨543473, by rfl⟩ : syracuseStep 724631 = 1086947) B1086947
theorem B724697 : Blo 479788 724697 := bstep (se 2 (by rfl) ⟨271761, by rfl⟩ : syracuseStep 724697 = 543523) B543523
theorem B724811 : Blo 479788 724811 := bstep (se 1 (by rfl) ⟨543608, by rfl⟩ : syracuseStep 724811 = 1087217) B1087217
theorem B724823 : Blo 479788 724823 := bstep (se 1 (by rfl) ⟨543617, by rfl⟩ : syracuseStep 724823 = 1087235) B1087235
theorem B1085273 : Blo 479788 1085273 := bstep (se 2 (by rfl) ⟨406977, by rfl⟩ : syracuseStep 1085273 = 813955) B813955
theorem B724889 : Blo 479788 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B1085363 : Blo 479788 1085363 := bstep (se 1 (by rfl) ⟨814022, by rfl⟩ : syracuseStep 1085363 = 1628045) B1628045
theorem B1085399 : Blo 479788 1085399 := bstep (se 1 (by rfl) ⟨814049, by rfl⟩ : syracuseStep 1085399 = 1628099) B1628099
theorem B725003 : Blo 479788 725003 := bstep (se 1 (by rfl) ⟨543752, by rfl⟩ : syracuseStep 725003 = 1087505) B1087505
theorem B725015 : Blo 479788 725015 := bstep (se 1 (by rfl) ⟨543761, by rfl⟩ : syracuseStep 725015 = 1087523) B1087523
theorem B725081 : Blo 479788 725081 := bstep (se 2 (by rfl) ⟨271905, by rfl⟩ : syracuseStep 725081 = 543811) B543811
theorem B1544285 : Blo 479788 1544285 := bstep (se 3 (by rfl) ⟨289553, by rfl⟩ : syracuseStep 1544285 = 579107) B579107
theorem B3084389 : Blo 479788 3084389 := bstep (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) B578323
theorem B1085579 : Blo 479788 1085579 := bstep (se 1 (by rfl) ⟨814184, by rfl⟩ : syracuseStep 1085579 = 1628369) B1628369
theorem B1216691 : Blo 479788 1216691 := bstep (se 1 (by rfl) ⟨912518, by rfl⟩ : syracuseStep 1216691 = 1825037) B1825037
theorem B1085633 : Blo 479788 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B725195 : Blo 479788 725195 := bstep (se 1 (by rfl) ⟨543896, by rfl⟩ : syracuseStep 725195 = 1087793) B1087793
theorem B725207 : Blo 479788 725207 := bstep (se 1 (by rfl) ⟨543905, by rfl⟩ : syracuseStep 725207 = 1087811) B1087811
theorem B725273 : Blo 479788 725273 := bstep (se 2 (by rfl) ⟨271977, by rfl⟩ : syracuseStep 725273 = 543955) B543955
theorem B725387 : Blo 479788 725387 := bstep (se 1 (by rfl) ⟨544040, by rfl⟩ : syracuseStep 725387 = 1088081) B1088081
theorem B725399 : Blo 479788 725399 := bstep (se 1 (by rfl) ⟨544049, by rfl⟩ : syracuseStep 725399 = 1088099) B1088099
theorem B1085849 : Blo 479788 1085849 := bstep (se 2 (by rfl) ⟨407193, by rfl⟩ : syracuseStep 1085849 = 814387) B814387
theorem B725465 : Blo 479788 725465 := bstep (se 2 (by rfl) ⟨272049, by rfl⟩ : syracuseStep 725465 = 544099) B544099
theorem B1085939 : Blo 479788 1085939 := bstep (se 1 (by rfl) ⟨814454, by rfl⟩ : syracuseStep 1085939 = 1628909) B1628909
theorem B1085975 : Blo 479788 1085975 := bstep (se 1 (by rfl) ⟨814481, by rfl⟩ : syracuseStep 1085975 = 1628963) B1628963
theorem B725579 : Blo 479788 725579 := bstep (se 1 (by rfl) ⟨544184, by rfl⟩ : syracuseStep 725579 = 1088369) B1088369
theorem B725591 : Blo 479788 725591 := bstep (se 1 (by rfl) ⟨544193, by rfl⟩ : syracuseStep 725591 = 1088387) B1088387
theorem B725657 : Blo 479788 725657 := bstep (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) B544243
theorem B1217227 : Blo 479788 1217227 := bstep (se 1 (by rfl) ⟨912920, by rfl⟩ : syracuseStep 1217227 = 1825841) B1825841
theorem B1086155 : Blo 479788 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B1086209 : Blo 479788 1086209 := bstep (se 2 (by rfl) ⟨407328, by rfl⟩ : syracuseStep 1086209 = 814657) B814657
theorem B1217369 : Blo 479788 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B1086425 : Blo 479788 1086425 := bstep (se 2 (by rfl) ⟨407409, by rfl⟩ : syracuseStep 1086425 = 814819) B814819
theorem B1086515 : Blo 479788 1086515 := bstep (se 1 (by rfl) ⟨814886, by rfl⟩ : syracuseStep 1086515 = 1629773) B1629773
theorem B1086551 : Blo 479788 1086551 := bstep (se 1 (by rfl) ⟨814913, by rfl⟩ : syracuseStep 1086551 = 1629827) B1629827
theorem B1086731 : Blo 479788 1086731 := bstep (se 1 (by rfl) ⟨815048, by rfl⟩ : syracuseStep 1086731 = 1630097) B1630097
theorem B1086785 : Blo 479788 1086785 := bstep (se 2 (by rfl) ⟨407544, by rfl⟩ : syracuseStep 1086785 = 815089) B815089
theorem B1087001 : Blo 479788 1087001 := bstep (se 2 (by rfl) ⟨407625, by rfl⟩ : syracuseStep 1087001 = 815251) B815251
theorem B1087091 : Blo 479788 1087091 := bstep (se 1 (by rfl) ⟨815318, by rfl⟩ : syracuseStep 1087091 = 1630637) B1630637
theorem B1218199 : Blo 479788 1218199 := bstep (se 1 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 1218199 = 1827299) B1827299
theorem B1087127 : Blo 479788 1087127 := bstep (se 1 (by rfl) ⟨815345, by rfl⟩ : syracuseStep 1087127 = 1630691) B1630691
theorem B1087307 : Blo 479788 1087307 := bstep (se 1 (by rfl) ⟨815480, by rfl⟩ : syracuseStep 1087307 = 1630961) B1630961
theorem B1087361 : Blo 479788 1087361 := bstep (se 2 (by rfl) ⟨407760, by rfl⟩ : syracuseStep 1087361 = 815521) B815521
theorem B1218635 : Blo 479788 1218635 := bstep (se 1 (by rfl) ⟨913976, by rfl⟩ : syracuseStep 1218635 = 1827953) B1827953
theorem B1087577 : Blo 479788 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B1087667 : Blo 479788 1087667 := bstep (se 1 (by rfl) ⟨815750, by rfl⟩ : syracuseStep 1087667 = 1631501) B1631501
theorem B1087703 : Blo 479788 1087703 := bstep (se 1 (by rfl) ⟨815777, by rfl⟩ : syracuseStep 1087703 = 1631555) B1631555
theorem B1251545 : Blo 479788 1251545 := bstep (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) B938659
theorem B2201879 : Blo 479788 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1153369 : Blo 479788 1153369 := bstep (se 2 (by rfl) ⟨432513, by rfl⟩ : syracuseStep 1153369 = 865027) B865027
theorem B1087883 : Blo 479788 1087883 := bstep (se 1 (by rfl) ⟨815912, by rfl⟩ : syracuseStep 1087883 = 1631825) B1631825
theorem B1219009 : Blo 479788 1219009 := bstep (se 2 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 1219009 = 914257) B914257
theorem B1087937 : Blo 479788 1087937 := bstep (se 2 (by rfl) ⟨407976, by rfl⟩ : syracuseStep 1087937 = 815953) B815953
theorem B825815 : Blo 479788 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B2431619 : Blo 479788 2431619 := bstep (se 1 (by rfl) ⟨1823714, by rfl⟩ : syracuseStep 2431619 = 3647429) B3647429
theorem B10394243 : Blo 479788 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B1088153 : Blo 479788 1088153 := bstep (se 2 (by rfl) ⟨408057, by rfl⟩ : syracuseStep 1088153 = 816115) B816115
theorem B1088243 : Blo 479788 1088243 := bstep (se 1 (by rfl) ⟨816182, by rfl⟩ : syracuseStep 1088243 = 1632365) B1632365
theorem B1088279 : Blo 479788 1088279 := bstep (se 1 (by rfl) ⟨816209, by rfl⟩ : syracuseStep 1088279 = 1632419) B1632419
theorem B1088459 : Blo 479788 1088459 := bstep (se 1 (by rfl) ⟨816344, by rfl⟩ : syracuseStep 1088459 = 1632689) B1632689
theorem B1088513 : Blo 479788 1088513 := bstep (se 2 (by rfl) ⟨408192, by rfl⟩ : syracuseStep 1088513 = 816385) B816385
theorem B1219607 : Blo 479788 1219607 := bstep (se 1 (by rfl) ⟨914705, by rfl⟩ : syracuseStep 1219607 = 1829411) B1829411
theorem B4627813 : Blo 479788 4627813 := bstep (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) B867715
theorem B2203031 : Blo 479788 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B1154839 : Blo 479788 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B1220417 : Blo 479788 1220417 := bstep (se 2 (by rfl) ⟨457656, by rfl⟩ : syracuseStep 1220417 = 915313) B915313
theorem B3645485 : Blo 479788 3645485 := bstep (se 3 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 3645485 = 1367057) B1367057
theorem B1220953 : Blo 479788 1220953 := bstep (se 2 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 1220953 = 915715) B915715
theorem B5218661 : Blo 479788 5218661 := bstep (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) B978499
theorem B7840577 : Blo 479788 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B2597849 : Blo 479788 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B2106647 : Blo 479788 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B2205073 : Blo 479788 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B1156531 : Blo 479788 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B1222067 : Blo 479788 1222067 := bstep (se 1 (by rfl) ⟨916550, by rfl⟩ : syracuseStep 1222067 = 1833101) B1833101
theorem B6596113 : Blo 479788 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B1222361 : Blo 479788 1222361 := bstep (se 2 (by rfl) ⟨458385, by rfl⟩ : syracuseStep 1222361 = 916771) B916771
theorem B1026113 : Blo 479788 1026113 := bstep (se 2 (by rfl) ⟨384792, by rfl⟩ : syracuseStep 1026113 = 769585) B769585
theorem B1026199 : Blo 479788 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B2435345 : Blo 479788 2435345 := bstep (se 2 (by rfl) ⟨913254, by rfl⟩ : syracuseStep 2435345 = 1826509) B1826509
theorem B2435507 : Blo 479788 2435507 := bstep (se 1 (by rfl) ⟨1826630, by rfl⟩ : syracuseStep 2435507 = 3653261) B3653261
theorem B731929 : Blo 479788 731929 := bstep (se 2 (by rfl) ⟨274473, by rfl⟩ : syracuseStep 731929 = 548947) B548947
theorem B1027019 : Blo 479788 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B5483537 : Blo 479788 5483537 := bstep (se 2 (by rfl) ⟨2056326, by rfl⟩ : syracuseStep 5483537 = 4112653) B4112653
theorem B1224011 : Blo 479788 1224011 := bstep (se 1 (by rfl) ⟨918008, by rfl⟩ : syracuseStep 1224011 = 1836017) B1836017
theorem B3517987 : Blo 479788 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B3649373 : Blo 479788 3649373 := bstep (se 3 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 3649373 = 1368515) B1368515
theorem B3518309 : Blo 479788 3518309 := bstep (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) B659683
theorem B1027993 : Blo 479788 1027993 := bstep (se 2 (by rfl) ⟨385497, by rfl⟩ : syracuseStep 1027993 = 770995) B770995
theorem B3485713 : Blo 479788 3485713 := bstep (se 2 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 3485713 = 2614285) B2614285
theorem B2306141 : Blo 479788 2306141 := bstep (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) B864803
theorem B2437451 : Blo 479788 2437451 := bstep (se 1 (by rfl) ⟨1828088, by rfl⟩ : syracuseStep 2437451 = 3656177) B3656177
theorem B3912113 : Blo 479788 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B3715915 : Blo 479788 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B734105 : Blo 479788 734105 := bstep (se 2 (by rfl) ⟨275289, by rfl⟩ : syracuseStep 734105 = 550579) B550579
theorem B3126347 : Blo 479788 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B1586251 : Blo 479788 1586251 := bstep (se 1 (by rfl) ⟨1189688, by rfl⟩ : syracuseStep 1586251 = 2379377) B2379377
theorem B865495 : Blo 479788 865495 := bstep (se 1 (by rfl) ⟨649121, by rfl⟩ : syracuseStep 865495 = 1298243) B1298243
theorem B865625 : Blo 479788 865625 := bstep (se 2 (by rfl) ⟨324609, by rfl⟩ : syracuseStep 865625 = 649219) B649219
theorem B1619351 : Blo 479788 1619351 := bstep (se 1 (by rfl) ⟨1214513, by rfl⟩ : syracuseStep 1619351 = 2429027) B2429027
theorem B11712205 : Blo 479788 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B5486453 : Blo 479788 5486453 := bstep (se 5 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 5486453 = 514355) B514355
theorem B1619891 : Blo 479788 1619891 := bstep (se 1 (by rfl) ⟨1214918, by rfl⟩ : syracuseStep 1619891 = 2429837) B2429837
theorem B2439233 : Blo 479788 2439233 := bstep (se 2 (by rfl) ⟨914712, by rfl⟩ : syracuseStep 2439233 = 1829425) B1829425
theorem B3291211 : Blo 479788 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B1620161 : Blo 479788 1620161 := bstep (se 2 (by rfl) ⟨607560, by rfl⟩ : syracuseStep 1620161 = 1215121) B1215121
theorem B1030411 : Blo 479788 1030411 := bstep (se 1 (by rfl) ⟨772808, by rfl⟩ : syracuseStep 1030411 = 1545617) B1545617
theorem B1030487 : Blo 479788 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B768727 : Blo 479788 768727 := bstep (se 1 (by rfl) ⟨576545, by rfl⟩ : syracuseStep 768727 = 1153091) B1153091
theorem B1620701 : Blo 479788 1620701 := bstep (se 3 (by rfl) ⟨303881, by rfl⟩ : syracuseStep 1620701 = 607763) B607763
theorem B768791 : Blo 479788 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B768919 : Blo 479788 768919 := bstep (se 1 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 768919 = 1153379) B1153379
theorem B1653655 : Blo 479788 1653655 := bstep (se 1 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 1653655 = 2480483) B2480483
theorem B1162163 : Blo 479788 1162163 := bstep (se 1 (by rfl) ⟨871622, by rfl⟩ : syracuseStep 1162163 = 1743245) B1743245
theorem B539851 : Blo 479788 539851 := bstep (se 1 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 539851 = 809777) B809777
theorem B539959 : Blo 479788 539959 := bstep (se 1 (by rfl) ⟨404969, by rfl⟩ : syracuseStep 539959 = 809939) B809939
theorem B769355 : Blo 479788 769355 := bstep (se 1 (by rfl) ⟨577016, by rfl⟩ : syracuseStep 769355 = 1154033) B1154033
theorem B540139 : Blo 479788 540139 := bstep (se 1 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 540139 = 810209) B810209
theorem B769547 : Blo 479788 769547 := bstep (se 1 (by rfl) ⟨577160, by rfl⟩ : syracuseStep 769547 = 1154321) B1154321
theorem B540247 : Blo 479788 540247 := bstep (se 1 (by rfl) ⟨405185, by rfl⟩ : syracuseStep 540247 = 810371) B810371
theorem B540427 : Blo 479788 540427 := bstep (se 1 (by rfl) ⟨405320, by rfl⟩ : syracuseStep 540427 = 810641) B810641
theorem B1621835 : Blo 479788 1621835 := bstep (se 1 (by rfl) ⟨1216376, by rfl⟩ : syracuseStep 1621835 = 2432753) B2432753
theorem B540535 : Blo 479788 540535 := bstep (se 1 (by rfl) ⟨405401, by rfl⟩ : syracuseStep 540535 = 810803) B810803
theorem B2441177 : Blo 479788 2441177 := bstep (se 2 (by rfl) ⟨915441, by rfl⟩ : syracuseStep 2441177 = 1830883) B1830883
theorem B540715 : Blo 479788 540715 := bstep (se 1 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 540715 = 811073) B811073
theorem B1720385 : Blo 479788 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B1032257 : Blo 479788 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B1622105 : Blo 479788 1622105 := bstep (se 2 (by rfl) ⟨608289, by rfl⟩ : syracuseStep 1622105 = 1216579) B1216579
theorem B540823 : Blo 479788 540823 := bstep (se 1 (by rfl) ⟨405617, by rfl⟩ : syracuseStep 540823 = 811235) B811235
theorem B541003 : Blo 479788 541003 := bstep (se 1 (by rfl) ⟨405752, by rfl⟩ : syracuseStep 541003 = 811505) B811505
theorem B541111 : Blo 479788 541111 := bstep (se 1 (by rfl) ⟨405833, by rfl⟩ : syracuseStep 541111 = 811667) B811667
theorem B541291 : Blo 479788 541291 := bstep (se 1 (by rfl) ⟨405968, by rfl⟩ : syracuseStep 541291 = 811937) B811937
theorem B836249 : Blo 479788 836249 := bstep (se 2 (by rfl) ⟨313593, by rfl⟩ : syracuseStep 836249 = 627187) B627187
theorem B3719857 : Blo 479788 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B541399 : Blo 479788 541399 := bstep (se 1 (by rfl) ⟨406049, by rfl⟩ : syracuseStep 541399 = 812099) B812099
theorem B40682225 : Blo 479788 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B1622807 : Blo 479788 1622807 := bstep (se 1 (by rfl) ⟨1217105, by rfl⟩ : syracuseStep 1622807 = 2434211) B2434211
theorem B541579 : Blo 479788 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B770969 : Blo 479788 770969 := bstep (se 2 (by rfl) ⟨289113, by rfl⟩ : syracuseStep 770969 = 578227) B578227
theorem B8111027 : Blo 479788 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B541687 : Blo 479788 541687 := bstep (se 1 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 541687 = 812531) B812531
theorem B541867 : Blo 479788 541867 := bstep (se 1 (by rfl) ⟨406400, by rfl⟩ : syracuseStep 541867 = 812801) B812801
theorem B541975 : Blo 479788 541975 := bstep (se 1 (by rfl) ⟨406481, by rfl⟩ : syracuseStep 541975 = 812963) B812963
theorem B1623347 : Blo 479788 1623347 := bstep (se 1 (by rfl) ⟨1217510, by rfl⟩ : syracuseStep 1623347 = 2435021) B2435021
theorem B2049425 : Blo 479788 2049425 := bstep (se 2 (by rfl) ⟨768534, by rfl⟩ : syracuseStep 2049425 = 1537069) B1537069
theorem B542155 : Blo 479788 542155 := bstep (se 1 (by rfl) ⟨406616, by rfl⟩ : syracuseStep 542155 = 813233) B813233
theorem B2442797 : Blo 479788 2442797 := bstep (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) B916049
theorem B542263 : Blo 479788 542263 := bstep (se 1 (by rfl) ⟨406697, by rfl⟩ : syracuseStep 542263 = 813395) B813395
theorem B1623617 : Blo 479788 1623617 := bstep (se 2 (by rfl) ⟨608856, by rfl⟩ : syracuseStep 1623617 = 1217713) B1217713
theorem B607819 : Blo 479788 607819 := bstep (se 1 (by rfl) ⟨455864, by rfl⟩ : syracuseStep 607819 = 911729) B911729
theorem B542443 : Blo 479788 542443 := bstep (se 1 (by rfl) ⟨406832, by rfl⟩ : syracuseStep 542443 = 813665) B813665
theorem B14042933 : Blo 479788 14042933 := bstep (se 5 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 14042933 = 1316525) B1316525
theorem B608087 : Blo 479788 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B542551 : Blo 479788 542551 := bstep (se 1 (by rfl) ⟨406913, by rfl⟩ : syracuseStep 542551 = 813827) B813827
theorem B542731 : Blo 479788 542731 := bstep (se 1 (by rfl) ⟨407048, by rfl⟩ : syracuseStep 542731 = 814097) B814097
theorem B1624157 : Blo 479788 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B542839 : Blo 479788 542839 := bstep (se 1 (by rfl) ⟨407129, by rfl⟩ : syracuseStep 542839 = 814259) B814259
theorem B1099955 : Blo 479788 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B739531 : Blo 479788 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B4114637 : Blo 479788 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B3098897 : Blo 479788 3098897 := bstep (se 2 (by rfl) ⟨1162086, by rfl⟩ : syracuseStep 3098897 = 2324173) B2324173
theorem B870679 : Blo 479788 870679 := bstep (se 1 (by rfl) ⟨653009, by rfl⟩ : syracuseStep 870679 = 1306019) B1306019
theorem B543019 : Blo 479788 543019 := bstep (se 1 (by rfl) ⟨407264, by rfl⟩ : syracuseStep 543019 = 814529) B814529
theorem B870743 : Blo 479788 870743 := bstep (se 1 (by rfl) ⟨653057, by rfl⟩ : syracuseStep 870743 = 1306115) B1306115
theorem B543127 : Blo 479788 543127 := bstep (se 1 (by rfl) ⟨407345, by rfl⟩ : syracuseStep 543127 = 814691) B814691
theorem B7817741 : Blo 479788 7817741 := bstep (se 3 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 7817741 = 2931653) B2931653
theorem B9423373 : Blo 479788 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B608791 : Blo 479788 608791 := bstep (se 1 (by rfl) ⟨456593, by rfl⟩ : syracuseStep 608791 = 913187) B913187
theorem B543307 : Blo 479788 543307 := bstep (se 1 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 543307 = 814961) B814961
theorem B1100375 : Blo 479788 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B543415 : Blo 479788 543415 := bstep (se 1 (by rfl) ⟨407561, by rfl⟩ : syracuseStep 543415 = 815123) B815123
theorem B2607947 : Blo 479788 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B543595 : Blo 479788 543595 := bstep (se 1 (by rfl) ⟨407696, by rfl⟩ : syracuseStep 543595 = 815393) B815393
theorem B543703 : Blo 479788 543703 := bstep (se 1 (by rfl) ⟨407777, by rfl⟩ : syracuseStep 543703 = 815555) B815555
theorem B2739217 : Blo 479788 2739217 := bstep (se 2 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 2739217 = 2054413) B2054413
theorem B543883 : Blo 479788 543883 := bstep (se 1 (by rfl) ⟨407912, by rfl⟩ : syracuseStep 543883 = 815825) B815825
theorem B1625291 : Blo 479788 1625291 := bstep (se 1 (by rfl) ⟨1218968, by rfl⟩ : syracuseStep 1625291 = 2437937) B2437937
theorem B543991 : Blo 479788 543991 := bstep (se 1 (by rfl) ⟨407993, by rfl⟩ : syracuseStep 543991 = 815987) B815987
theorem B3460427 : Blo 479788 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B544171 : Blo 479788 544171 := bstep (se 1 (by rfl) ⟨408128, by rfl⟩ : syracuseStep 544171 = 816257) B816257
theorem B1854913 : Blo 479788 1854913 := bstep (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) B1391185
theorem B1625561 : Blo 479788 1625561 := bstep (se 2 (by rfl) ⟨609585, by rfl⟩ : syracuseStep 1625561 = 1219171) B1219171
theorem B773783 : Blo 479788 773783 := bstep (se 1 (by rfl) ⟨580337, by rfl⟩ : syracuseStep 773783 = 1160675) B1160675
theorem B1232563 : Blo 479788 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B2051801 : Blo 479788 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B2051885 : Blo 479788 2051885 := bstep (se 3 (by rfl) ⟨384728, by rfl⟩ : syracuseStep 2051885 = 769457) B769457
theorem B11260055 : Blo 479788 11260055 := bstep (se 1 (by rfl) ⟨8445041, by rfl⟩ : syracuseStep 11260055 = 16890083) B16890083
theorem B1626263 : Blo 479788 1626263 := bstep (se 1 (by rfl) ⟨1219697, by rfl⟩ : syracuseStep 1626263 = 2439395) B2439395
theorem B610507 : Blo 479788 610507 := bstep (se 1 (by rfl) ⟨457880, by rfl⟩ : syracuseStep 610507 = 915761) B915761
theorem B1823107 : Blo 479788 1823107 := bstep (se 1 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 1823107 = 2734661) B2734661
theorem B1954307 : Blo 479788 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B4117027 : Blo 479788 4117027 := bstep (se 1 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 4117027 = 6175541) B6175541
theorem B479799 : Blo 479788 479799 := bstep (se 1 (by rfl) ⟨359849, by rfl⟩ : syracuseStep 479799 = 719699) B719699
theorem B479819 : Blo 479788 479819 := bstep (se 1 (by rfl) ⟨359864, by rfl⟩ : syracuseStep 479819 = 719729) B719729
theorem B479831 : Blo 479788 479831 := bstep (se 1 (by rfl) ⟨359873, by rfl⟩ : syracuseStep 479831 = 719747) B719747
theorem B479851 : Blo 479788 479851 := bstep (se 1 (by rfl) ⟨359888, by rfl⟩ : syracuseStep 479851 = 719777) B719777
theorem B479863 : Blo 479788 479863 := bstep (se 1 (by rfl) ⟨359897, by rfl⟩ : syracuseStep 479863 = 719795) B719795
theorem B479883 : Blo 479788 479883 := bstep (se 1 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 479883 = 719825) B719825
theorem B479895 : Blo 479788 479895 := bstep (se 1 (by rfl) ⟨359921, by rfl⟩ : syracuseStep 479895 = 719843) B719843
theorem B479915 : Blo 479788 479915 := bstep (se 1 (by rfl) ⟨359936, by rfl⟩ : syracuseStep 479915 = 719873) B719873
theorem B1823411 : Blo 479788 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1626803 : Blo 479788 1626803 := bstep (se 1 (by rfl) ⟨1220102, by rfl⟩ : syracuseStep 1626803 = 2440205) B2440205
theorem B479927 : Blo 479788 479927 := bstep (se 1 (by rfl) ⟨359945, by rfl⟩ : syracuseStep 479927 = 719891) B719891
theorem B479947 : Blo 479788 479947 := bstep (se 1 (by rfl) ⟨359960, by rfl⟩ : syracuseStep 479947 = 719921) B719921
theorem B774859 : Blo 479788 774859 := bstep (se 1 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 774859 = 1162289) B1162289
theorem B479959 : Blo 479788 479959 := bstep (se 1 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 479959 = 719939) B719939
theorem B479979 : Blo 479788 479979 := bstep (se 1 (by rfl) ⟨359984, by rfl⟩ : syracuseStep 479979 = 719969) B719969
theorem B479991 : Blo 479788 479991 := bstep (se 1 (by rfl) ⟨359993, by rfl⟩ : syracuseStep 479991 = 719987) B719987
theorem B480011 : Blo 479788 480011 := bstep (se 1 (by rfl) ⟨360008, by rfl⟩ : syracuseStep 480011 = 720017) B720017
theorem B480023 : Blo 479788 480023 := bstep (se 1 (by rfl) ⟨360017, by rfl⟩ : syracuseStep 480023 = 720035) B720035
theorem B480043 : Blo 479788 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B480055 : Blo 479788 480055 := bstep (se 1 (by rfl) ⟨360041, by rfl⟩ : syracuseStep 480055 = 720083) B720083
theorem B3461953 : Blo 479788 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B480075 : Blo 479788 480075 := bstep (se 1 (by rfl) ⟨360056, by rfl⟩ : syracuseStep 480075 = 720113) B720113
theorem B480087 : Blo 479788 480087 := bstep (se 1 (by rfl) ⟨360065, by rfl⟩ : syracuseStep 480087 = 720131) B720131
theorem B480107 : Blo 479788 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B480119 : Blo 479788 480119 := bstep (se 1 (by rfl) ⟨360089, by rfl⟩ : syracuseStep 480119 = 720179) B720179
theorem B480139 : Blo 479788 480139 := bstep (se 1 (by rfl) ⟨360104, by rfl⟩ : syracuseStep 480139 = 720209) B720209
theorem B480151 : Blo 479788 480151 := bstep (se 1 (by rfl) ⟨360113, by rfl⟩ : syracuseStep 480151 = 720227) B720227
theorem B480171 : Blo 479788 480171 := bstep (se 1 (by rfl) ⟨360128, by rfl⟩ : syracuseStep 480171 = 720257) B720257
theorem B480183 : Blo 479788 480183 := bstep (se 1 (by rfl) ⟨360137, by rfl⟩ : syracuseStep 480183 = 720275) B720275
theorem B1627073 : Blo 479788 1627073 := bstep (se 2 (by rfl) ⟨610152, by rfl⟩ : syracuseStep 1627073 = 1220305) B1220305
theorem B480203 : Blo 479788 480203 := bstep (se 1 (by rfl) ⟨360152, by rfl⟩ : syracuseStep 480203 = 720305) B720305
theorem B480215 : Blo 479788 480215 := bstep (se 1 (by rfl) ⟨360161, by rfl⟩ : syracuseStep 480215 = 720323) B720323
theorem B480235 : Blo 479788 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B480247 : Blo 479788 480247 := bstep (se 1 (by rfl) ⟨360185, by rfl⟩ : syracuseStep 480247 = 720371) B720371
theorem B480267 : Blo 479788 480267 := bstep (se 1 (by rfl) ⟨360200, by rfl⟩ : syracuseStep 480267 = 720401) B720401
theorem B480279 : Blo 479788 480279 := bstep (se 1 (by rfl) ⟨360209, by rfl⟩ : syracuseStep 480279 = 720419) B720419
theorem B480299 : Blo 479788 480299 := bstep (se 1 (by rfl) ⟨360224, by rfl⟩ : syracuseStep 480299 = 720449) B720449
theorem B480311 : Blo 479788 480311 := bstep (se 1 (by rfl) ⟨360233, by rfl⟩ : syracuseStep 480311 = 720467) B720467
theorem B480331 : Blo 479788 480331 := bstep (se 1 (by rfl) ⟨360248, by rfl⟩ : syracuseStep 480331 = 720497) B720497
theorem B480343 : Blo 479788 480343 := bstep (se 1 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 480343 = 720515) B720515
theorem B480363 : Blo 479788 480363 := bstep (se 1 (by rfl) ⟨360272, by rfl⟩ : syracuseStep 480363 = 720545) B720545
theorem B480375 : Blo 479788 480375 := bstep (se 1 (by rfl) ⟨360281, by rfl⟩ : syracuseStep 480375 = 720563) B720563
theorem B480395 : Blo 479788 480395 := bstep (se 1 (by rfl) ⟨360296, by rfl⟩ : syracuseStep 480395 = 720593) B720593
theorem B480407 : Blo 479788 480407 := bstep (se 1 (by rfl) ⟨360305, by rfl⟩ : syracuseStep 480407 = 720611) B720611
theorem B611479 : Blo 479788 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B480427 : Blo 479788 480427 := bstep (se 1 (by rfl) ⟨360320, by rfl⟩ : syracuseStep 480427 = 720641) B720641
theorem B480439 : Blo 479788 480439 := bstep (se 1 (by rfl) ⟨360329, by rfl⟩ : syracuseStep 480439 = 720659) B720659
theorem B480459 : Blo 479788 480459 := bstep (se 1 (by rfl) ⟨360344, by rfl⟩ : syracuseStep 480459 = 720689) B720689
theorem B480471 : Blo 479788 480471 := bstep (se 1 (by rfl) ⟨360353, by rfl⟩ : syracuseStep 480471 = 720707) B720707
theorem B480491 : Blo 479788 480491 := bstep (se 1 (by rfl) ⟨360368, by rfl⟩ : syracuseStep 480491 = 720737) B720737
theorem B480503 : Blo 479788 480503 := bstep (se 1 (by rfl) ⟨360377, by rfl⟩ : syracuseStep 480503 = 720755) B720755
theorem B480523 : Blo 479788 480523 := bstep (se 1 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 480523 = 720785) B720785
theorem B480535 : Blo 479788 480535 := bstep (se 1 (by rfl) ⟨360401, by rfl⟩ : syracuseStep 480535 = 720803) B720803
theorem B480555 : Blo 479788 480555 := bstep (se 1 (by rfl) ⟨360416, by rfl⟩ : syracuseStep 480555 = 720833) B720833
theorem B480567 : Blo 479788 480567 := bstep (se 1 (by rfl) ⟨360425, by rfl⟩ : syracuseStep 480567 = 720851) B720851
theorem B1824065 : Blo 479788 1824065 := bstep (se 2 (by rfl) ⟨684024, by rfl⟩ : syracuseStep 1824065 = 1368049) B1368049
theorem B480587 : Blo 479788 480587 := bstep (se 1 (by rfl) ⟨360440, by rfl⟩ : syracuseStep 480587 = 720881) B720881
theorem B480599 : Blo 479788 480599 := bstep (se 1 (by rfl) ⟨360449, by rfl⟩ : syracuseStep 480599 = 720899) B720899
theorem B2446685 : Blo 479788 2446685 := bstep (se 3 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 2446685 = 917507) B917507
theorem B480619 : Blo 479788 480619 := bstep (se 1 (by rfl) ⟨360464, by rfl⟩ : syracuseStep 480619 = 720929) B720929
theorem B480631 : Blo 479788 480631 := bstep (se 1 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 480631 = 720947) B720947
theorem B480651 : Blo 479788 480651 := bstep (se 1 (by rfl) ⟨360488, by rfl⟩ : syracuseStep 480651 = 720977) B720977
theorem B480663 : Blo 479788 480663 := bstep (se 1 (by rfl) ⟨360497, by rfl⟩ : syracuseStep 480663 = 720995) B720995
theorem B480683 : Blo 479788 480683 := bstep (se 1 (by rfl) ⟨360512, by rfl⟩ : syracuseStep 480683 = 721025) B721025
theorem B480695 : Blo 479788 480695 := bstep (se 1 (by rfl) ⟨360521, by rfl⟩ : syracuseStep 480695 = 721043) B721043
theorem B480715 : Blo 479788 480715 := bstep (se 1 (by rfl) ⟨360536, by rfl⟩ : syracuseStep 480715 = 721073) B721073
theorem B480727 : Blo 479788 480727 := bstep (se 1 (by rfl) ⟨360545, by rfl⟩ : syracuseStep 480727 = 721091) B721091
theorem B1627613 : Blo 479788 1627613 := bstep (se 3 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 1627613 = 610355) B610355
theorem B480747 : Blo 479788 480747 := bstep (se 1 (by rfl) ⟨360560, by rfl⟩ : syracuseStep 480747 = 721121) B721121
theorem B480759 : Blo 479788 480759 := bstep (se 1 (by rfl) ⟨360569, by rfl⟩ : syracuseStep 480759 = 721139) B721139
theorem B480779 : Blo 479788 480779 := bstep (se 1 (by rfl) ⟨360584, by rfl⟩ : syracuseStep 480779 = 721169) B721169
theorem B480791 : Blo 479788 480791 := bstep (se 1 (by rfl) ⟨360593, by rfl⟩ : syracuseStep 480791 = 721187) B721187
theorem B480811 : Blo 479788 480811 := bstep (se 1 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 480811 = 721217) B721217
theorem B480823 : Blo 479788 480823 := bstep (se 1 (by rfl) ⟨360617, by rfl⟩ : syracuseStep 480823 = 721235) B721235
theorem B480843 : Blo 479788 480843 := bstep (se 1 (by rfl) ⟨360632, by rfl⟩ : syracuseStep 480843 = 721265) B721265
theorem B480855 : Blo 479788 480855 := bstep (se 1 (by rfl) ⟨360641, by rfl⟩ : syracuseStep 480855 = 721283) B721283
theorem B480875 : Blo 479788 480875 := bstep (se 1 (by rfl) ⟨360656, by rfl⟩ : syracuseStep 480875 = 721313) B721313
theorem B480887 : Blo 479788 480887 := bstep (se 1 (by rfl) ⟨360665, by rfl⟩ : syracuseStep 480887 = 721331) B721331
theorem B480907 : Blo 479788 480907 := bstep (se 1 (by rfl) ⟨360680, by rfl⟩ : syracuseStep 480907 = 721361) B721361
theorem B480919 : Blo 479788 480919 := bstep (se 1 (by rfl) ⟨360689, by rfl⟩ : syracuseStep 480919 = 721379) B721379
theorem B480939 : Blo 479788 480939 := bstep (se 1 (by rfl) ⟨360704, by rfl⟩ : syracuseStep 480939 = 721409) B721409
theorem B480951 : Blo 479788 480951 := bstep (se 1 (by rfl) ⟨360713, by rfl⟩ : syracuseStep 480951 = 721427) B721427
theorem B480971 : Blo 479788 480971 := bstep (se 1 (by rfl) ⟨360728, by rfl⟩ : syracuseStep 480971 = 721457) B721457
theorem B480983 : Blo 479788 480983 := bstep (se 1 (by rfl) ⟨360737, by rfl⟩ : syracuseStep 480983 = 721475) B721475
theorem B481003 : Blo 479788 481003 := bstep (se 1 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 481003 = 721505) B721505
theorem B481015 : Blo 479788 481015 := bstep (se 1 (by rfl) ⟨360761, by rfl⟩ : syracuseStep 481015 = 721523) B721523
theorem B481035 : Blo 479788 481035 := bstep (se 1 (by rfl) ⟨360776, by rfl⟩ : syracuseStep 481035 = 721553) B721553
theorem B481047 : Blo 479788 481047 := bstep (se 1 (by rfl) ⟨360785, by rfl⟩ : syracuseStep 481047 = 721571) B721571
theorem B481067 : Blo 479788 481067 := bstep (se 1 (by rfl) ⟨360800, by rfl⟩ : syracuseStep 481067 = 721601) B721601
theorem B481079 : Blo 479788 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B481099 : Blo 479788 481099 := bstep (se 1 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 481099 = 721649) B721649
theorem B481111 : Blo 479788 481111 := bstep (se 1 (by rfl) ⟨360833, by rfl⟩ : syracuseStep 481111 = 721667) B721667
theorem B579415 : Blo 479788 579415 := bstep (se 1 (by rfl) ⟨434561, by rfl⟩ : syracuseStep 579415 = 869123) B869123
theorem B8214371 : Blo 479788 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B481131 : Blo 479788 481131 := bstep (se 1 (by rfl) ⟨360848, by rfl⟩ : syracuseStep 481131 = 721697) B721697
theorem B481143 : Blo 479788 481143 := bstep (se 1 (by rfl) ⟨360857, by rfl⟩ : syracuseStep 481143 = 721715) B721715
theorem B513911 : Blo 479788 513911 := bstep (se 1 (by rfl) ⟨385433, by rfl⟩ : syracuseStep 513911 = 770867) B770867
theorem B481163 : Blo 479788 481163 := bstep (se 1 (by rfl) ⟨360872, by rfl⟩ : syracuseStep 481163 = 721745) B721745
theorem B481175 : Blo 479788 481175 := bstep (se 1 (by rfl) ⟨360881, by rfl⟩ : syracuseStep 481175 = 721763) B721763
theorem B481195 : Blo 479788 481195 := bstep (se 1 (by rfl) ⟨360896, by rfl⟩ : syracuseStep 481195 = 721793) B721793
theorem B481207 : Blo 479788 481207 := bstep (se 1 (by rfl) ⟨360905, by rfl⟩ : syracuseStep 481207 = 721811) B721811
theorem B481227 : Blo 479788 481227 := bstep (se 1 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 481227 = 721841) B721841
theorem B481239 : Blo 479788 481239 := bstep (se 1 (by rfl) ⟨360929, by rfl⟩ : syracuseStep 481239 = 721859) B721859
theorem B481259 : Blo 479788 481259 := bstep (se 1 (by rfl) ⟨360944, by rfl⟩ : syracuseStep 481259 = 721889) B721889
theorem B481271 : Blo 479788 481271 := bstep (se 1 (by rfl) ⟨360953, by rfl⟩ : syracuseStep 481271 = 721907) B721907
theorem B481291 : Blo 479788 481291 := bstep (se 1 (by rfl) ⟨360968, by rfl⟩ : syracuseStep 481291 = 721937) B721937
theorem B5199889 : Blo 479788 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B481303 : Blo 479788 481303 := bstep (se 1 (by rfl) ⟨360977, by rfl⟩ : syracuseStep 481303 = 721955) B721955
theorem B481323 : Blo 479788 481323 := bstep (se 1 (by rfl) ⟨360992, by rfl⟩ : syracuseStep 481323 = 721985) B721985
theorem B481335 : Blo 479788 481335 := bstep (se 1 (by rfl) ⟨361001, by rfl⟩ : syracuseStep 481335 = 722003) B722003
theorem B481355 : Blo 479788 481355 := bstep (se 1 (by rfl) ⟨361016, by rfl⟩ : syracuseStep 481355 = 722033) B722033
theorem B481367 : Blo 479788 481367 := bstep (se 1 (by rfl) ⟨361025, by rfl⟩ : syracuseStep 481367 = 722051) B722051
theorem B481387 : Blo 479788 481387 := bstep (se 1 (by rfl) ⟨361040, by rfl⟩ : syracuseStep 481387 = 722081) B722081
theorem B481399 : Blo 479788 481399 := bstep (se 1 (by rfl) ⟨361049, by rfl⟩ : syracuseStep 481399 = 722099) B722099
theorem B481419 : Blo 479788 481419 := bstep (se 1 (by rfl) ⟨361064, by rfl⟩ : syracuseStep 481419 = 722129) B722129
theorem B481431 : Blo 479788 481431 := bstep (se 1 (by rfl) ⟨361073, by rfl⟩ : syracuseStep 481431 = 722147) B722147
theorem B481451 : Blo 479788 481451 := bstep (se 1 (by rfl) ⟨361088, by rfl⟩ : syracuseStep 481451 = 722177) B722177
theorem B481463 : Blo 479788 481463 := bstep (se 1 (by rfl) ⟨361097, by rfl⟩ : syracuseStep 481463 = 722195) B722195
theorem B481483 : Blo 479788 481483 := bstep (se 1 (by rfl) ⟨361112, by rfl⟩ : syracuseStep 481483 = 722225) B722225
theorem B481495 : Blo 479788 481495 := bstep (se 1 (by rfl) ⟨361121, by rfl⟩ : syracuseStep 481495 = 722243) B722243
theorem B481515 : Blo 479788 481515 := bstep (se 1 (by rfl) ⟨361136, by rfl⟩ : syracuseStep 481515 = 722273) B722273
theorem B481527 : Blo 479788 481527 := bstep (se 1 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 481527 = 722291) B722291
theorem B481547 : Blo 479788 481547 := bstep (se 1 (by rfl) ⟨361160, by rfl⟩ : syracuseStep 481547 = 722321) B722321
theorem B481559 : Blo 479788 481559 := bstep (se 1 (by rfl) ⟨361169, by rfl⟩ : syracuseStep 481559 = 722339) B722339
theorem B481579 : Blo 479788 481579 := bstep (se 1 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 481579 = 722369) B722369
theorem B2283821 : Blo 479788 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B481591 : Blo 479788 481591 := bstep (se 1 (by rfl) ⟨361193, by rfl⟩ : syracuseStep 481591 = 722387) B722387
theorem B481611 : Blo 479788 481611 := bstep (se 1 (by rfl) ⟨361208, by rfl⟩ : syracuseStep 481611 = 722417) B722417
theorem B481623 : Blo 479788 481623 := bstep (se 1 (by rfl) ⟨361217, by rfl⟩ : syracuseStep 481623 = 722435) B722435
theorem B481643 : Blo 479788 481643 := bstep (se 1 (by rfl) ⟨361232, by rfl⟩ : syracuseStep 481643 = 722465) B722465
theorem B481655 : Blo 479788 481655 := bstep (se 1 (by rfl) ⟨361241, by rfl⟩ : syracuseStep 481655 = 722483) B722483
theorem B2742659 : Blo 479788 2742659 := bstep (se 1 (by rfl) ⟨2056994, by rfl⟩ : syracuseStep 2742659 = 4113989) B4113989
theorem B481675 : Blo 479788 481675 := bstep (se 1 (by rfl) ⟨361256, by rfl⟩ : syracuseStep 481675 = 722513) B722513
theorem B481687 : Blo 479788 481687 := bstep (se 1 (by rfl) ⟨361265, by rfl⟩ : syracuseStep 481687 = 722531) B722531
theorem B481707 : Blo 479788 481707 := bstep (se 1 (by rfl) ⟨361280, by rfl⟩ : syracuseStep 481707 = 722561) B722561
theorem B481719 : Blo 479788 481719 := bstep (se 1 (by rfl) ⟨361289, by rfl⟩ : syracuseStep 481719 = 722579) B722579
theorem B1366465 : Blo 479788 1366465 := bstep (se 2 (by rfl) ⟨512424, by rfl⟩ : syracuseStep 1366465 = 1024849) B1024849
theorem B481739 : Blo 479788 481739 := bstep (se 1 (by rfl) ⟨361304, by rfl⟩ : syracuseStep 481739 = 722609) B722609
theorem B481751 : Blo 479788 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B481771 : Blo 479788 481771 := bstep (se 1 (by rfl) ⟨361328, by rfl⟩ : syracuseStep 481771 = 722657) B722657
theorem B481783 : Blo 479788 481783 := bstep (se 1 (by rfl) ⟨361337, by rfl⟩ : syracuseStep 481783 = 722675) B722675
theorem B481803 : Blo 479788 481803 := bstep (se 1 (by rfl) ⟨361352, by rfl⟩ : syracuseStep 481803 = 722705) B722705
theorem B481815 : Blo 479788 481815 := bstep (se 1 (by rfl) ⟨361361, by rfl⟩ : syracuseStep 481815 = 722723) B722723
theorem B481835 : Blo 479788 481835 := bstep (se 1 (by rfl) ⟨361376, by rfl⟩ : syracuseStep 481835 = 722753) B722753
theorem B514603 : Blo 479788 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B1825325 : Blo 479788 1825325 := bstep (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) B684497
theorem B481847 : Blo 479788 481847 := bstep (se 1 (by rfl) ⟨361385, by rfl⟩ : syracuseStep 481847 = 722771) B722771
theorem B1825355 : Blo 479788 1825355 := bstep (se 1 (by rfl) ⟨1369016, by rfl⟩ : syracuseStep 1825355 = 2738033) B2738033
theorem B481867 : Blo 479788 481867 := bstep (se 1 (by rfl) ⟨361400, by rfl⟩ : syracuseStep 481867 = 722801) B722801
theorem B1628747 : Blo 479788 1628747 := bstep (se 1 (by rfl) ⟨1221560, by rfl⟩ : syracuseStep 1628747 = 2443121) B2443121
theorem B481879 : Blo 479788 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B2775653 : Blo 479788 2775653 := bstep (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) B520435
theorem B481899 : Blo 479788 481899 := bstep (se 1 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 481899 = 722849) B722849
theorem B481911 : Blo 479788 481911 := bstep (se 1 (by rfl) ⟨361433, by rfl⟩ : syracuseStep 481911 = 722867) B722867
theorem B7494275 : Blo 479788 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B481931 : Blo 479788 481931 := bstep (se 1 (by rfl) ⟨361448, by rfl⟩ : syracuseStep 481931 = 722897) B722897
theorem B481943 : Blo 479788 481943 := bstep (se 1 (by rfl) ⟨361457, by rfl⟩ : syracuseStep 481943 = 722915) B722915
theorem B481963 : Blo 479788 481963 := bstep (se 1 (by rfl) ⟨361472, by rfl⟩ : syracuseStep 481963 = 722945) B722945
theorem B481975 : Blo 479788 481975 := bstep (se 1 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 481975 = 722963) B722963
theorem B481995 : Blo 479788 481995 := bstep (se 1 (by rfl) ⟨361496, by rfl⟩ : syracuseStep 481995 = 722993) B722993
theorem B482007 : Blo 479788 482007 := bstep (se 1 (by rfl) ⟨361505, by rfl⟩ : syracuseStep 482007 = 723011) B723011
theorem B809689 : Blo 479788 809689 := bstep (se 2 (by rfl) ⟨303633, by rfl⟩ : syracuseStep 809689 = 607267) B607267
theorem B1465049 : Blo 479788 1465049 := bstep (se 2 (by rfl) ⟨549393, by rfl⟩ : syracuseStep 1465049 = 1098787) B1098787
theorem B482027 : Blo 479788 482027 := bstep (se 1 (by rfl) ⟨361520, by rfl⟩ : syracuseStep 482027 = 723041) B723041
theorem B482039 : Blo 479788 482039 := bstep (se 1 (by rfl) ⟨361529, by rfl⟩ : syracuseStep 482039 = 723059) B723059
theorem B482059 : Blo 479788 482059 := bstep (se 1 (by rfl) ⟨361544, by rfl⟩ : syracuseStep 482059 = 723089) B723089
theorem B1366807 : Blo 479788 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B482071 : Blo 479788 482071 := bstep (se 1 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 482071 = 723107) B723107
theorem B482091 : Blo 479788 482091 := bstep (se 1 (by rfl) ⟨361568, by rfl⟩ : syracuseStep 482091 = 723137) B723137
theorem B482103 : Blo 479788 482103 := bstep (se 1 (by rfl) ⟨361577, by rfl⟩ : syracuseStep 482103 = 723155) B723155
theorem B482123 : Blo 479788 482123 := bstep (se 1 (by rfl) ⟨361592, by rfl⟩ : syracuseStep 482123 = 723185) B723185
theorem B482135 : Blo 479788 482135 := bstep (se 1 (by rfl) ⟨361601, by rfl⟩ : syracuseStep 482135 = 723203) B723203
theorem B1629017 : Blo 479788 1629017 := bstep (se 2 (by rfl) ⟨610881, by rfl⟩ : syracuseStep 1629017 = 1221763) B1221763
theorem B6970211 : Blo 479788 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B482155 : Blo 479788 482155 := bstep (se 1 (by rfl) ⟨361616, by rfl⟩ : syracuseStep 482155 = 723233) B723233
theorem B482167 : Blo 479788 482167 := bstep (se 1 (by rfl) ⟨361625, by rfl⟩ : syracuseStep 482167 = 723251) B723251
theorem B482187 : Blo 479788 482187 := bstep (se 1 (by rfl) ⟨361640, by rfl⟩ : syracuseStep 482187 = 723281) B723281
theorem B482199 : Blo 479788 482199 := bstep (se 1 (by rfl) ⟨361649, by rfl⟩ : syracuseStep 482199 = 723299) B723299
theorem B482219 : Blo 479788 482219 := bstep (se 1 (by rfl) ⟨361664, by rfl⟩ : syracuseStep 482219 = 723329) B723329
theorem B482231 : Blo 479788 482231 := bstep (se 1 (by rfl) ⟨361673, by rfl⟩ : syracuseStep 482231 = 723347) B723347
theorem B482251 : Blo 479788 482251 := bstep (se 1 (by rfl) ⟨361688, by rfl⟩ : syracuseStep 482251 = 723377) B723377
theorem B482263 : Blo 479788 482263 := bstep (se 1 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 482263 = 723395) B723395
theorem B482283 : Blo 479788 482283 := bstep (se 1 (by rfl) ⟨361712, by rfl⟩ : syracuseStep 482283 = 723425) B723425
theorem B482295 : Blo 479788 482295 := bstep (se 1 (by rfl) ⟨361721, by rfl⟩ : syracuseStep 482295 = 723443) B723443
theorem B482315 : Blo 479788 482315 := bstep (se 1 (by rfl) ⟨361736, by rfl⟩ : syracuseStep 482315 = 723473) B723473
theorem B482327 : Blo 479788 482327 := bstep (se 1 (by rfl) ⟨361745, by rfl⟩ : syracuseStep 482327 = 723491) B723491
theorem B482347 : Blo 479788 482347 := bstep (se 1 (by rfl) ⟨361760, by rfl⟩ : syracuseStep 482347 = 723521) B723521
theorem B482359 : Blo 479788 482359 := bstep (se 1 (by rfl) ⟨361769, by rfl⟩ : syracuseStep 482359 = 723539) B723539
theorem B2055233 : Blo 479788 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B482379 : Blo 479788 482379 := bstep (se 1 (by rfl) ⟨361784, by rfl⟩ : syracuseStep 482379 = 723569) B723569
theorem B482391 : Blo 479788 482391 := bstep (se 1 (by rfl) ⟨361793, by rfl⟩ : syracuseStep 482391 = 723587) B723587
theorem B482411 : Blo 479788 482411 := bstep (se 1 (by rfl) ⟨361808, by rfl⟩ : syracuseStep 482411 = 723617) B723617
theorem B482423 : Blo 479788 482423 := bstep (se 1 (by rfl) ⟨361817, by rfl⟩ : syracuseStep 482423 = 723635) B723635
theorem B482443 : Blo 479788 482443 := bstep (se 1 (by rfl) ⟨361832, by rfl⟩ : syracuseStep 482443 = 723665) B723665
theorem B482455 : Blo 479788 482455 := bstep (se 1 (by rfl) ⟨361841, by rfl⟩ : syracuseStep 482455 = 723683) B723683
theorem B482475 : Blo 479788 482475 := bstep (se 1 (by rfl) ⟨361856, by rfl⟩ : syracuseStep 482475 = 723713) B723713
theorem B482487 : Blo 479788 482487 := bstep (se 1 (by rfl) ⟨361865, by rfl⟩ : syracuseStep 482487 = 723731) B723731
theorem B482507 : Blo 479788 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B482519 : Blo 479788 482519 := bstep (se 1 (by rfl) ⟨361889, by rfl⟩ : syracuseStep 482519 = 723779) B723779
theorem B1826009 : Blo 479788 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B482539 : Blo 479788 482539 := bstep (se 1 (by rfl) ⟨361904, by rfl⟩ : syracuseStep 482539 = 723809) B723809
theorem B482551 : Blo 479788 482551 := bstep (se 1 (by rfl) ⟨361913, by rfl⟩ : syracuseStep 482551 = 723827) B723827
theorem B482571 : Blo 479788 482571 := bstep (se 1 (by rfl) ⟨361928, by rfl⟩ : syracuseStep 482571 = 723857) B723857
theorem B810263 : Blo 479788 810263 := bstep (se 1 (by rfl) ⟨607697, by rfl⟩ : syracuseStep 810263 = 1215395) B1215395
theorem B482583 : Blo 479788 482583 := bstep (se 1 (by rfl) ⟨361937, by rfl⟩ : syracuseStep 482583 = 723875) B723875
theorem B482603 : Blo 479788 482603 := bstep (se 1 (by rfl) ⟨361952, by rfl⟩ : syracuseStep 482603 = 723905) B723905
theorem B482615 : Blo 479788 482615 := bstep (se 1 (by rfl) ⟨361961, by rfl⟩ : syracuseStep 482615 = 723923) B723923
theorem B482635 : Blo 479788 482635 := bstep (se 1 (by rfl) ⟨361976, by rfl⟩ : syracuseStep 482635 = 723953) B723953
theorem B482647 : Blo 479788 482647 := bstep (se 1 (by rfl) ⟨361985, by rfl⟩ : syracuseStep 482647 = 723971) B723971
theorem B482667 : Blo 479788 482667 := bstep (se 1 (by rfl) ⟨362000, by rfl⟩ : syracuseStep 482667 = 724001) B724001
theorem B482679 : Blo 479788 482679 := bstep (se 1 (by rfl) ⟨362009, by rfl⟩ : syracuseStep 482679 = 724019) B724019
theorem B482699 : Blo 479788 482699 := bstep (se 1 (by rfl) ⟨362024, by rfl⟩ : syracuseStep 482699 = 724049) B724049
theorem B810391 : Blo 479788 810391 := bstep (se 1 (by rfl) ⟨607793, by rfl⟩ : syracuseStep 810391 = 1215587) B1215587
theorem B482711 : Blo 479788 482711 := bstep (se 1 (by rfl) ⟨362033, by rfl⟩ : syracuseStep 482711 = 724067) B724067
theorem B515479 : Blo 479788 515479 := bstep (se 1 (by rfl) ⟨386609, by rfl⟩ : syracuseStep 515479 = 773219) B773219
theorem B2448791 : Blo 479788 2448791 := bstep (se 1 (by rfl) ⟨1836593, by rfl⟩ : syracuseStep 2448791 = 3673187) B3673187
theorem B482731 : Blo 479788 482731 := bstep (se 1 (by rfl) ⟨362048, by rfl⟩ : syracuseStep 482731 = 724097) B724097
theorem B482743 : Blo 479788 482743 := bstep (se 1 (by rfl) ⟨362057, by rfl⟩ : syracuseStep 482743 = 724115) B724115
theorem B482763 : Blo 479788 482763 := bstep (se 1 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 482763 = 724145) B724145
theorem B482775 : Blo 479788 482775 := bstep (se 1 (by rfl) ⟨362081, by rfl⟩ : syracuseStep 482775 = 724163) B724163
theorem B1367513 : Blo 479788 1367513 := bstep (se 2 (by rfl) ⟨512817, by rfl⟩ : syracuseStep 1367513 = 1025635) B1025635
theorem B482795 : Blo 479788 482795 := bstep (se 1 (by rfl) ⟨362096, by rfl⟩ : syracuseStep 482795 = 724193) B724193
theorem B482807 : Blo 479788 482807 := bstep (se 1 (by rfl) ⟨362105, by rfl⟩ : syracuseStep 482807 = 724211) B724211
theorem B482827 : Blo 479788 482827 := bstep (se 1 (by rfl) ⟨362120, by rfl⟩ : syracuseStep 482827 = 724241) B724241
theorem B1629719 : Blo 479788 1629719 := bstep (se 1 (by rfl) ⟨1222289, by rfl⟩ : syracuseStep 1629719 = 2444579) B2444579
theorem B1826327 : Blo 479788 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B482839 : Blo 479788 482839 := bstep (se 1 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 482839 = 724259) B724259
theorem B482859 : Blo 479788 482859 := bstep (se 1 (by rfl) ⟨362144, by rfl⟩ : syracuseStep 482859 = 724289) B724289
theorem B482871 : Blo 479788 482871 := bstep (se 1 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 482871 = 724307) B724307
theorem B482891 : Blo 479788 482891 := bstep (se 1 (by rfl) ⟨362168, by rfl⟩ : syracuseStep 482891 = 724337) B724337
theorem B482903 : Blo 479788 482903 := bstep (se 1 (by rfl) ⟨362177, by rfl⟩ : syracuseStep 482903 = 724355) B724355
theorem B482923 : Blo 479788 482923 := bstep (se 1 (by rfl) ⟨362192, by rfl⟩ : syracuseStep 482923 = 724385) B724385
theorem B482935 : Blo 479788 482935 := bstep (se 1 (by rfl) ⟨362201, by rfl⟩ : syracuseStep 482935 = 724403) B724403
theorem B482955 : Blo 479788 482955 := bstep (se 1 (by rfl) ⟨362216, by rfl⟩ : syracuseStep 482955 = 724433) B724433
theorem B482967 : Blo 479788 482967 := bstep (se 1 (by rfl) ⟨362225, by rfl⟩ : syracuseStep 482967 = 724451) B724451
theorem B482987 : Blo 479788 482987 := bstep (se 1 (by rfl) ⟨362240, by rfl⟩ : syracuseStep 482987 = 724481) B724481
theorem B482999 : Blo 479788 482999 := bstep (se 1 (by rfl) ⟨362249, by rfl⟩ : syracuseStep 482999 = 724499) B724499
theorem B483019 : Blo 479788 483019 := bstep (se 1 (by rfl) ⟨362264, by rfl⟩ : syracuseStep 483019 = 724529) B724529
theorem B483031 : Blo 479788 483031 := bstep (se 1 (by rfl) ⟨362273, by rfl⟩ : syracuseStep 483031 = 724547) B724547
theorem B2055901 : Blo 479788 2055901 := bstep (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) B770963
theorem B483051 : Blo 479788 483051 := bstep (se 1 (by rfl) ⟨362288, by rfl⟩ : syracuseStep 483051 = 724577) B724577
theorem B483063 : Blo 479788 483063 := bstep (se 1 (by rfl) ⟨362297, by rfl⟩ : syracuseStep 483063 = 724595) B724595
theorem B483083 : Blo 479788 483083 := bstep (se 1 (by rfl) ⟨362312, by rfl⟩ : syracuseStep 483083 = 724625) B724625
theorem B483095 : Blo 479788 483095 := bstep (se 1 (by rfl) ⟨362321, by rfl⟩ : syracuseStep 483095 = 724643) B724643
theorem B483115 : Blo 479788 483115 := bstep (se 1 (by rfl) ⟨362336, by rfl⟩ : syracuseStep 483115 = 724673) B724673
theorem B483127 : Blo 479788 483127 := bstep (se 1 (by rfl) ⟨362345, by rfl⟩ : syracuseStep 483127 = 724691) B724691
theorem B483147 : Blo 479788 483147 := bstep (se 1 (by rfl) ⟨362360, by rfl⟩ : syracuseStep 483147 = 724721) B724721
theorem B515927 : Blo 479788 515927 := bstep (se 1 (by rfl) ⟨386945, by rfl⟩ : syracuseStep 515927 = 773891) B773891
theorem B483159 : Blo 479788 483159 := bstep (se 1 (by rfl) ⟨362369, by rfl⟩ : syracuseStep 483159 = 724739) B724739
theorem B3137381 : Blo 479788 3137381 := bstep (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) B588259
theorem B483179 : Blo 479788 483179 := bstep (se 1 (by rfl) ⟨362384, by rfl⟩ : syracuseStep 483179 = 724769) B724769
theorem B483191 : Blo 479788 483191 := bstep (se 1 (by rfl) ⟨362393, by rfl⟩ : syracuseStep 483191 = 724787) B724787
theorem B483211 : Blo 479788 483211 := bstep (se 1 (by rfl) ⟨362408, by rfl⟩ : syracuseStep 483211 = 724817) B724817
theorem B483223 : Blo 479788 483223 := bstep (se 1 (by rfl) ⟨362417, by rfl⟩ : syracuseStep 483223 = 724835) B724835
theorem B483243 : Blo 479788 483243 := bstep (se 1 (by rfl) ⟨362432, by rfl⟩ : syracuseStep 483243 = 724865) B724865
theorem B483255 : Blo 479788 483255 := bstep (se 1 (by rfl) ⟨362441, by rfl⟩ : syracuseStep 483255 = 724883) B724883
theorem B483275 : Blo 479788 483275 := bstep (se 1 (by rfl) ⟨362456, by rfl⟩ : syracuseStep 483275 = 724913) B724913
theorem B483287 : Blo 479788 483287 := bstep (se 1 (by rfl) ⟨362465, by rfl⟩ : syracuseStep 483287 = 724931) B724931
theorem B483307 : Blo 479788 483307 := bstep (se 1 (by rfl) ⟨362480, by rfl⟩ : syracuseStep 483307 = 724961) B724961
theorem B483319 : Blo 479788 483319 := bstep (se 1 (by rfl) ⟨362489, by rfl⟩ : syracuseStep 483319 = 724979) B724979
theorem B811019 : Blo 479788 811019 := bstep (se 1 (by rfl) ⟨608264, by rfl⟩ : syracuseStep 811019 = 1216529) B1216529
theorem B483339 : Blo 479788 483339 := bstep (se 1 (by rfl) ⟨362504, by rfl⟩ : syracuseStep 483339 = 725009) B725009
theorem B483351 : Blo 479788 483351 := bstep (se 1 (by rfl) ⟨362513, by rfl⟩ : syracuseStep 483351 = 725027) B725027
theorem B483371 : Blo 479788 483371 := bstep (se 1 (by rfl) ⟨362528, by rfl⟩ : syracuseStep 483371 = 725057) B725057
theorem B1630259 : Blo 479788 1630259 := bstep (se 1 (by rfl) ⟨1222694, by rfl⟩ : syracuseStep 1630259 = 2445389) B2445389
theorem B483383 : Blo 479788 483383 := bstep (se 1 (by rfl) ⟨362537, by rfl⟩ : syracuseStep 483383 = 725075) B725075
theorem B483403 : Blo 479788 483403 := bstep (se 1 (by rfl) ⟨362552, by rfl⟩ : syracuseStep 483403 = 725105) B725105
theorem B483415 : Blo 479788 483415 := bstep (se 1 (by rfl) ⟨362561, by rfl⟩ : syracuseStep 483415 = 725123) B725123
theorem B483435 : Blo 479788 483435 := bstep (se 1 (by rfl) ⟨362576, by rfl⟩ : syracuseStep 483435 = 725153) B725153
theorem B483447 : Blo 479788 483447 := bstep (se 1 (by rfl) ⟨362585, by rfl⟩ : syracuseStep 483447 = 725171) B725171
theorem B811147 : Blo 479788 811147 := bstep (se 1 (by rfl) ⟨608360, by rfl⟩ : syracuseStep 811147 = 1216721) B1216721
theorem B483467 : Blo 479788 483467 := bstep (se 1 (by rfl) ⟨362600, by rfl⟩ : syracuseStep 483467 = 725201) B725201
theorem B4612247 : Blo 479788 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B1958039 : Blo 479788 1958039 := bstep (se 1 (by rfl) ⟨1468529, by rfl⟩ : syracuseStep 1958039 = 2937059) B2937059
theorem B483479 : Blo 479788 483479 := bstep (se 1 (by rfl) ⟨362609, by rfl⟩ : syracuseStep 483479 = 725219) B725219
theorem B483499 : Blo 479788 483499 := bstep (se 1 (by rfl) ⟨362624, by rfl⟩ : syracuseStep 483499 = 725249) B725249
theorem B1826995 : Blo 479788 1826995 := bstep (se 1 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 1826995 = 2740493) B2740493
theorem B483511 : Blo 479788 483511 := bstep (se 1 (by rfl) ⟨362633, by rfl⟩ : syracuseStep 483511 = 725267) B725267
theorem B1302731 : Blo 479788 1302731 := bstep (se 1 (by rfl) ⟨977048, by rfl⟩ : syracuseStep 1302731 = 1954097) B1954097
theorem B516299 : Blo 479788 516299 := bstep (se 1 (by rfl) ⟨387224, by rfl⟩ : syracuseStep 516299 = 774449) B774449
theorem B483531 : Blo 479788 483531 := bstep (se 1 (by rfl) ⟨362648, by rfl⟩ : syracuseStep 483531 = 725297) B725297
theorem B483543 : Blo 479788 483543 := bstep (se 1 (by rfl) ⟨362657, by rfl⟩ : syracuseStep 483543 = 725315) B725315
theorem B483563 : Blo 479788 483563 := bstep (se 1 (by rfl) ⟨362672, by rfl⟩ : syracuseStep 483563 = 725345) B725345
theorem B483575 : Blo 479788 483575 := bstep (se 1 (by rfl) ⟨362681, by rfl⟩ : syracuseStep 483575 = 725363) B725363
theorem B483595 : Blo 479788 483595 := bstep (se 1 (by rfl) ⟨362696, by rfl⟩ : syracuseStep 483595 = 725393) B725393
theorem B62710037 : Blo 479788 62710037 := bstep (se 6 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 62710037 = 2939533) B2939533
theorem B483607 : Blo 479788 483607 := bstep (se 1 (by rfl) ⟨362705, by rfl⟩ : syracuseStep 483607 = 725411) B725411
theorem B811289 : Blo 479788 811289 := bstep (se 2 (by rfl) ⟨304233, by rfl⟩ : syracuseStep 811289 = 608467) B608467
theorem B483627 : Blo 479788 483627 := bstep (se 1 (by rfl) ⟨362720, by rfl⟩ : syracuseStep 483627 = 725441) B725441
theorem B2056499 : Blo 479788 2056499 := bstep (se 1 (by rfl) ⟨1542374, by rfl⟩ : syracuseStep 2056499 = 3084749) B3084749
theorem B483639 : Blo 479788 483639 := bstep (se 1 (by rfl) ⟨362729, by rfl⟩ : syracuseStep 483639 = 725459) B725459
theorem B1630529 : Blo 479788 1630529 := bstep (se 2 (by rfl) ⟨611448, by rfl⟩ : syracuseStep 1630529 = 1222897) B1222897
theorem B483659 : Blo 479788 483659 := bstep (se 1 (by rfl) ⟨362744, by rfl⟩ : syracuseStep 483659 = 725489) B725489
theorem B483671 : Blo 479788 483671 := bstep (se 1 (by rfl) ⟨362753, by rfl⟩ : syracuseStep 483671 = 725507) B725507
theorem B483691 : Blo 479788 483691 := bstep (se 1 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 483691 = 725537) B725537
theorem B483703 : Blo 479788 483703 := bstep (se 1 (by rfl) ⟨362777, by rfl⟩ : syracuseStep 483703 = 725555) B725555
theorem B483723 : Blo 479788 483723 := bstep (se 1 (by rfl) ⟨362792, by rfl⟩ : syracuseStep 483723 = 725585) B725585
theorem B483735 : Blo 479788 483735 := bstep (se 1 (by rfl) ⟨362801, by rfl⟩ : syracuseStep 483735 = 725603) B725603
theorem B811417 : Blo 479788 811417 := bstep (se 2 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 811417 = 608563) B608563
theorem B483755 : Blo 479788 483755 := bstep (se 1 (by rfl) ⟨362816, by rfl⟩ : syracuseStep 483755 = 725633) B725633
theorem B483767 : Blo 479788 483767 := bstep (se 1 (by rfl) ⟨362825, by rfl⟩ : syracuseStep 483767 = 725651) B725651
theorem B483787 : Blo 479788 483787 := bstep (se 1 (by rfl) ⟨362840, by rfl⟩ : syracuseStep 483787 = 725681) B725681
theorem B975385 : Blo 479788 975385 := bstep (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) B731539
theorem B2745049 : Blo 479788 2745049 := bstep (se 2 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 2745049 = 2058787) B2058787
theorem B1631069 : Blo 479788 1631069 := bstep (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) B611651
theorem B8479667 : Blo 479788 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B811991 : Blo 479788 811991 := bstep (se 1 (by rfl) ⟨608993, by rfl⟩ : syracuseStep 811991 = 1217987) B1217987
theorem B1369153 : Blo 479788 1369153 := bstep (se 2 (by rfl) ⟨513432, by rfl⟩ : syracuseStep 1369153 = 1026865) B1026865
theorem B4121675 : Blo 479788 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B812119 : Blo 479788 812119 := bstep (se 1 (by rfl) ⟨609089, by rfl⟩ : syracuseStep 812119 = 1218179) B1218179
theorem B1303769 : Blo 479788 1303769 := bstep (se 2 (by rfl) ⟨488913, by rfl⟩ : syracuseStep 1303769 = 977827) B977827
theorem B5498117 : Blo 479788 5498117 := bstep (se 4 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 5498117 = 1030897) B1030897
theorem B1828241 : Blo 479788 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B2188889 : Blo 479788 2188889 := bstep (se 2 (by rfl) ⟨820833, by rfl⟩ : syracuseStep 2188889 = 1641667) B1641667
theorem B2746007 : Blo 479788 2746007 := bstep (se 1 (by rfl) ⟨2059505, by rfl⟩ : syracuseStep 2746007 = 4119011) B4119011
theorem B1861271 : Blo 479788 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B812747 : Blo 479788 812747 := bstep (se 1 (by rfl) ⟨609560, by rfl⟩ : syracuseStep 812747 = 1219121) B1219121
theorem B976601 : Blo 479788 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B1730327 : Blo 479788 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B812875 : Blo 479788 812875 := bstep (se 1 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 812875 = 1219313) B1219313
theorem B911243 : Blo 479788 911243 := bstep (se 1 (by rfl) ⟨683432, by rfl⟩ : syracuseStep 911243 = 1366865) B1366865
theorem B1632203 : Blo 479788 1632203 := bstep (se 1 (by rfl) ⟨1224152, by rfl⟩ : syracuseStep 1632203 = 2448305) B2448305
theorem B813017 : Blo 479788 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B2615341 : Blo 479788 2615341 := bstep (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) B980753
theorem B911425 : Blo 479788 911425 := bstep (se 2 (by rfl) ⟨341784, by rfl⟩ : syracuseStep 911425 = 683569) B683569
theorem B1828939 : Blo 479788 1828939 := bstep (se 1 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 1828939 = 2743409) B2743409
theorem B813145 : Blo 479788 813145 := bstep (se 2 (by rfl) ⟨304929, by rfl⟩ : syracuseStep 813145 = 609859) B609859
theorem B1632473 : Blo 479788 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B1829213 : Blo 479788 1829213 := bstep (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) B685955
theorem B911873 : Blo 479788 911873 := bstep (se 2 (by rfl) ⟨341952, by rfl⟩ : syracuseStep 911873 = 683905) B683905
theorem B1305163 : Blo 479788 1305163 := bstep (se 1 (by rfl) ⟨978872, by rfl⟩ : syracuseStep 1305163 = 1957745) B1957745
theorem B813719 : Blo 479788 813719 := bstep (se 1 (by rfl) ⟨610289, by rfl⟩ : syracuseStep 813719 = 1220579) B1220579
theorem B813847 : Blo 479788 813847 := bstep (se 1 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 813847 = 1220771) B1220771
theorem B912215 : Blo 479788 912215 := bstep (se 1 (by rfl) ⟨684161, by rfl⟩ : syracuseStep 912215 = 1368323) B1368323
theorem B617431 : Blo 479788 617431 := bstep (se 1 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 617431 = 926147) B926147
theorem B1829911 : Blo 479788 1829911 := bstep (se 1 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 1829911 = 2744867) B2744867
theorem B3697937 : Blo 479788 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B486679 : Blo 479788 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B814475 : Blo 479788 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B1306049 : Blo 479788 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B912883 : Blo 479788 912883 := bstep (se 1 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 912883 = 1369325) B1369325
theorem B978419 : Blo 479788 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B814603 : Blo 479788 814603 := bstep (se 1 (by rfl) ⟨610952, by rfl⟩ : syracuseStep 814603 = 1221905) B1221905
theorem B1306201 : Blo 479788 1306201 := bstep (se 2 (by rfl) ⟨489825, by rfl⟩ : syracuseStep 1306201 = 979651) B979651
theorem B814745 : Blo 479788 814745 := bstep (se 2 (by rfl) ⟨305529, by rfl⟩ : syracuseStep 814745 = 611059) B611059
theorem B1175233 : Blo 479788 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B2092823 : Blo 479788 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B814873 : Blo 479788 814873 := bstep (se 2 (by rfl) ⟨305577, by rfl⟩ : syracuseStep 814873 = 611155) B611155
theorem B1830701 : Blo 479788 1830701 := bstep (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) B686513
theorem B913331 : Blo 479788 913331 := bstep (se 1 (by rfl) ⟨684998, by rfl⟩ : syracuseStep 913331 = 1369997) B1369997
theorem B1306547 : Blo 479788 1306547 := bstep (se 1 (by rfl) ⟨979910, by rfl⟩ : syracuseStep 1306547 = 1959821) B1959821
theorem B913369 : Blo 479788 913369 := bstep (se 2 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 913369 = 685027) B685027
theorem B978905 : Blo 479788 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B2060291 : Blo 479788 2060291 := bstep (se 1 (by rfl) ⟨1545218, by rfl⟩ : syracuseStep 2060291 = 3090437) B3090437
theorem B782347 : Blo 479788 782347 := bstep (se 1 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 782347 = 1173521) B1173521
theorem B2748491 : Blo 479788 2748491 := bstep (se 1 (by rfl) ⟨2061368, by rfl⟩ : syracuseStep 2748491 = 4122737) B4122737
theorem B684121 : Blo 479788 684121 := bstep (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) B513091
theorem B5009501 : Blo 479788 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B8876213 : Blo 479788 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B684235 : Blo 479788 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B815447 : Blo 479788 815447 := bstep (se 1 (by rfl) ⟨611585, by rfl⟩ : syracuseStep 815447 = 1223171) B1223171
theorem B2060633 : Blo 479788 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B913817 : Blo 479788 913817 := bstep (se 2 (by rfl) ⟨342681, by rfl⟩ : syracuseStep 913817 = 685363) B685363
theorem B651673 : Blo 479788 651673 := bstep (se 2 (by rfl) ⟨244377, by rfl⟩ : syracuseStep 651673 = 488755) B488755
theorem B815575 : Blo 479788 815575 := bstep (se 1 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 815575 = 1223363) B1223363
theorem B13529693 : Blo 479788 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B1372889 : Blo 479788 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B488171 : Blo 479788 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B1307585 : Blo 479788 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B816203 : Blo 479788 816203 := bstep (se 1 (by rfl) ⟨612152, by rfl⟩ : syracuseStep 816203 = 1224305) B1224305
theorem B619607 : Blo 479788 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B914561 : Blo 479788 914561 := bstep (se 2 (by rfl) ⟨342960, by rfl⟩ : syracuseStep 914561 = 685921) B685921
theorem B1045657 : Blo 479788 1045657 := bstep (se 2 (by rfl) ⟨392121, by rfl⟩ : syracuseStep 1045657 = 784243) B784243
theorem B1832129 : Blo 479788 1832129 := bstep (se 2 (by rfl) ⟨687048, by rfl⟩ : syracuseStep 1832129 = 1374097) B1374097
theorem B816331 : Blo 479788 816331 := bstep (se 1 (by rfl) ⟨612248, by rfl⟩ : syracuseStep 816331 = 1224497) B1224497
theorem B2323673 : Blo 479788 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B914827 : Blo 479788 914827 := bstep (se 1 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 914827 = 1372241) B1372241
theorem B685579 : Blo 479788 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1144343 : Blo 479788 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B587287 : Blo 479788 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B6190667 : Blo 479788 6190667 := bstep (se 1 (by rfl) ⟨4643000, by rfl⟩ : syracuseStep 6190667 = 9286001) B9286001
theorem B1111745 : Blo 479788 1111745 := bstep (se 2 (by rfl) ⟨416904, by rfl⟩ : syracuseStep 1111745 = 833809) B833809
theorem B13891277 : Blo 479788 13891277 := bstep (se 3 (by rfl) ⟨2604614, by rfl⟩ : syracuseStep 13891277 = 5209229) B5209229
theorem B685847 : Blo 479788 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B915275 : Blo 479788 915275 := bstep (se 1 (by rfl) ⟨686456, by rfl⟩ : syracuseStep 915275 = 1372913) B1372913
theorem B2062273 : Blo 479788 2062273 := bstep (se 2 (by rfl) ⟨773352, by rfl⟩ : syracuseStep 2062273 = 1546705) B1546705
theorem B1374155 : Blo 479788 1374155 := bstep (se 1 (by rfl) ⟨1030616, by rfl⟩ : syracuseStep 1374155 = 2061233) B2061233
theorem B915457 : Blo 479788 915457 := bstep (se 2 (by rfl) ⟨343296, by rfl⟩ : syracuseStep 915457 = 686593) B686593
theorem B3897389 : Blo 479788 3897389 := bstep (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) B1461521
theorem B5863499 : Blo 479788 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B13924493 : Blo 479788 13924493 := bstep (se 3 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 13924493 = 5221685) B5221685
theorem B1079603 : Blo 479788 1079603 := bstep (se 1 (by rfl) ⟨809702, by rfl⟩ : syracuseStep 1079603 = 1619405) B1619405
theorem B1079639 : Blo 479788 1079639 := bstep (se 1 (by rfl) ⟨809729, by rfl⟩ : syracuseStep 1079639 = 1619459) B1619459
theorem B915799 : Blo 479788 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B1079819 : Blo 479788 1079819 := bstep (se 1 (by rfl) ⟨809864, by rfl⟩ : syracuseStep 1079819 = 1619729) B1619729
theorem B916019 : Blo 479788 916019 := bstep (se 1 (by rfl) ⟨687014, by rfl⟩ : syracuseStep 916019 = 1374029) B1374029
theorem B1079873 : Blo 479788 1079873 := bstep (se 2 (by rfl) ⟨404952, by rfl⟩ : syracuseStep 1079873 = 809905) B809905
theorem B3078749 : Blo 479788 3078749 := bstep (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) B1154531
theorem B2226781 : Blo 479788 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B1833617 : Blo 479788 1833617 := bstep (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) B1375213
theorem B2751155 : Blo 479788 2751155 := bstep (se 1 (by rfl) ⟨2063366, by rfl⟩ : syracuseStep 2751155 = 4126733) B4126733
theorem B686809 : Blo 479788 686809 := bstep (se 2 (by rfl) ⟨257553, by rfl⟩ : syracuseStep 686809 = 515107) B515107
theorem B916247 : Blo 479788 916247 := bstep (se 1 (by rfl) ⟨687185, by rfl⟩ : syracuseStep 916247 = 1374371) B1374371
theorem B1080089 : Blo 479788 1080089 := bstep (se 2 (by rfl) ⟨405033, by rfl⟩ : syracuseStep 1080089 = 810067) B810067
theorem B719705 : Blo 479788 719705 := bstep (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) B539779
theorem B1080179 : Blo 479788 1080179 := bstep (se 1 (by rfl) ⟨810134, by rfl⟩ : syracuseStep 1080179 = 1620269) B1620269
theorem B1080215 : Blo 479788 1080215 := bstep (se 1 (by rfl) ⟨810161, by rfl⟩ : syracuseStep 1080215 = 1620323) B1620323
theorem B719819 : Blo 479788 719819 := bstep (se 1 (by rfl) ⟨539864, by rfl⟩ : syracuseStep 719819 = 1079729) B1079729
theorem B719831 : Blo 479788 719831 := bstep (se 1 (by rfl) ⟨539873, by rfl⟩ : syracuseStep 719831 = 1079747) B1079747
theorem B719897 : Blo 479788 719897 := bstep (se 2 (by rfl) ⟨269961, by rfl⟩ : syracuseStep 719897 = 539923) B539923
theorem B916505 : Blo 479788 916505 := bstep (se 2 (by rfl) ⟨343689, by rfl⟩ : syracuseStep 916505 = 687379) B687379
theorem B13859909 : Blo 479788 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B1080395 : Blo 479788 1080395 := bstep (se 1 (by rfl) ⟨810296, by rfl⟩ : syracuseStep 1080395 = 1620593) B1620593
theorem B1834073 : Blo 479788 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B1080449 : Blo 479788 1080449 := bstep (se 2 (by rfl) ⟨405168, by rfl⟩ : syracuseStep 1080449 = 810337) B810337
theorem B720011 : Blo 479788 720011 := bstep (se 1 (by rfl) ⟨540008, by rfl⟩ : syracuseStep 720011 = 1080017) B1080017
theorem B720023 : Blo 479788 720023 := bstep (se 1 (by rfl) ⟨540017, by rfl⟩ : syracuseStep 720023 = 1080035) B1080035
theorem B720089 : Blo 479788 720089 := bstep (se 2 (by rfl) ⟨270033, by rfl⟩ : syracuseStep 720089 = 540067) B540067
theorem B1834285 : Blo 479788 1834285 := bstep (se 3 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 1834285 = 687857) B687857
theorem B720203 : Blo 479788 720203 := bstep (se 1 (by rfl) ⟨540152, by rfl⟩ : syracuseStep 720203 = 1080305) B1080305
theorem B720215 : Blo 479788 720215 := bstep (se 1 (by rfl) ⟨540161, by rfl⟩ : syracuseStep 720215 = 1080323) B1080323
theorem B1080665 : Blo 479788 1080665 := bstep (se 2 (by rfl) ⟨405249, by rfl⟩ : syracuseStep 1080665 = 810499) B810499
theorem B720281 : Blo 479788 720281 := bstep (se 2 (by rfl) ⟨270105, by rfl⟩ : syracuseStep 720281 = 540211) B540211
theorem B1080755 : Blo 479788 1080755 := bstep (se 1 (by rfl) ⟨810566, by rfl⟩ : syracuseStep 1080755 = 1621133) B1621133
theorem B916915 : Blo 479788 916915 := bstep (se 1 (by rfl) ⟨687686, by rfl⟩ : syracuseStep 916915 = 1375373) B1375373
theorem B1080791 : Blo 479788 1080791 := bstep (se 1 (by rfl) ⟨810593, by rfl⟩ : syracuseStep 1080791 = 1621187) B1621187
theorem B7044569 : Blo 479788 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B720395 : Blo 479788 720395 := bstep (se 1 (by rfl) ⟨540296, by rfl⟩ : syracuseStep 720395 = 1080593) B1080593
theorem B720407 : Blo 479788 720407 := bstep (se 1 (by rfl) ⟨540305, by rfl⟩ : syracuseStep 720407 = 1080611) B1080611
theorem B1539607 : Blo 479788 1539607 := bstep (se 1 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 1539607 = 2309411) B2309411
theorem B720473 : Blo 479788 720473 := bstep (se 2 (by rfl) ⟨270177, by rfl⟩ : syracuseStep 720473 = 540355) B540355
theorem B1834589 : Blo 479788 1834589 := bstep (se 3 (by rfl) ⟨343985, by rfl⟩ : syracuseStep 1834589 = 687971) B687971
theorem B3899011 : Blo 479788 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B1080971 : Blo 479788 1080971 := bstep (se 1 (by rfl) ⟨810728, by rfl⟩ : syracuseStep 1080971 = 1621457) B1621457
theorem B1081025 : Blo 479788 1081025 := bstep (se 2 (by rfl) ⟨405384, by rfl⟩ : syracuseStep 1081025 = 810769) B810769
theorem B720587 : Blo 479788 720587 := bstep (se 1 (by rfl) ⟨540440, by rfl⟩ : syracuseStep 720587 = 1080881) B1080881
theorem B720599 : Blo 479788 720599 := bstep (se 1 (by rfl) ⟨540449, by rfl⟩ : syracuseStep 720599 = 1080899) B1080899
theorem B720665 : Blo 479788 720665 := bstep (se 2 (by rfl) ⟨270249, by rfl⟩ : syracuseStep 720665 = 540499) B540499
theorem B720779 : Blo 479788 720779 := bstep (se 1 (by rfl) ⟨540584, by rfl⟩ : syracuseStep 720779 = 1081169) B1081169
theorem B720791 : Blo 479788 720791 := bstep (se 1 (by rfl) ⟨540593, by rfl⟩ : syracuseStep 720791 = 1081187) B1081187
theorem B1081241 : Blo 479788 1081241 := bstep (se 2 (by rfl) ⟨405465, by rfl⟩ : syracuseStep 1081241 = 810931) B810931
theorem B917401 : Blo 479788 917401 := bstep (se 2 (by rfl) ⟨344025, by rfl⟩ : syracuseStep 917401 = 688051) B688051
theorem B1540043 : Blo 479788 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B720857 : Blo 479788 720857 := bstep (se 2 (by rfl) ⟨270321, by rfl⟩ : syracuseStep 720857 = 540643) B540643
theorem B1081331 : Blo 479788 1081331 := bstep (se 1 (by rfl) ⟨810998, by rfl⟩ : syracuseStep 1081331 = 1621997) B1621997
theorem B720911 : Blo 479788 720911 := bstep (se 1 (by rfl) ⟨540683, by rfl⟩ : syracuseStep 720911 = 1081367) B1081367
theorem B1146923 : Blo 479788 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B688171 : Blo 479788 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B720953 : Blo 479788 720953 := bstep (se 2 (by rfl) ⟨270357, by rfl⟩ : syracuseStep 720953 = 540715) B540715
theorem B1081403 : Blo 479788 1081403 := bstep (se 1 (by rfl) ⟨811052, by rfl⟩ : syracuseStep 1081403 = 1622105) B1622105
theorem B1835075 : Blo 479788 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B721031 : Blo 479788 721031 := bstep (se 1 (by rfl) ⟨540773, by rfl⟩ : syracuseStep 721031 = 1081547) B1081547
theorem B721067 : Blo 479788 721067 := bstep (se 1 (by rfl) ⟨540800, by rfl⟩ : syracuseStep 721067 = 1081601) B1081601
theorem B1081529 : Blo 479788 1081529 := bstep (se 2 (by rfl) ⟨405573, by rfl⟩ : syracuseStep 1081529 = 811147) B811147
theorem B721097 : Blo 479788 721097 := bstep (se 2 (by rfl) ⟨270411, by rfl⟩ : syracuseStep 721097 = 540823) B540823
theorem B917705 : Blo 479788 917705 := bstep (se 2 (by rfl) ⟨344139, by rfl⟩ : syracuseStep 917705 = 688279) B688279
theorem B721211 : Blo 479788 721211 := bstep (se 1 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 721211 = 1081817) B1081817
theorem B721271 : Blo 479788 721271 := bstep (se 1 (by rfl) ⟨540953, by rfl⟩ : syracuseStep 721271 = 1081907) B1081907
theorem B721295 : Blo 479788 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B721337 : Blo 479788 721337 := bstep (se 2 (by rfl) ⟨270501, by rfl⟩ : syracuseStep 721337 = 541003) B541003
theorem B721415 : Blo 479788 721415 := bstep (se 1 (by rfl) ⟨541061, by rfl⟩ : syracuseStep 721415 = 1082123) B1082123
theorem B1835531 : Blo 479788 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B1081871 : Blo 479788 1081871 := bstep (se 1 (by rfl) ⟨811403, by rfl⟩ : syracuseStep 1081871 = 1622807) B1622807
theorem B1376797 : Blo 479788 1376797 := bstep (se 3 (by rfl) ⟨258149, by rfl⟩ : syracuseStep 1376797 = 516299) B516299
theorem B1081889 : Blo 479788 1081889 := bstep (se 2 (by rfl) ⟨405708, by rfl⟩ : syracuseStep 1081889 = 811417) B811417
theorem B721451 : Blo 479788 721451 := bstep (se 1 (by rfl) ⟨541088, by rfl⟩ : syracuseStep 721451 = 1082177) B1082177
theorem B721481 : Blo 479788 721481 := bstep (se 2 (by rfl) ⟨270555, by rfl⟩ : syracuseStep 721481 = 541111) B541111
theorem B721595 : Blo 479788 721595 := bstep (se 1 (by rfl) ⟨541196, by rfl⟩ : syracuseStep 721595 = 1082393) B1082393
theorem B3670757 : Blo 479788 3670757 := bstep (se 4 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 3670757 = 688267) B688267
theorem B721655 : Blo 479788 721655 := bstep (se 1 (by rfl) ⟨541241, by rfl⟩ : syracuseStep 721655 = 1082483) B1082483
theorem B721679 : Blo 479788 721679 := bstep (se 1 (by rfl) ⟨541259, by rfl⟩ : syracuseStep 721679 = 1082519) B1082519
theorem B721721 : Blo 479788 721721 := bstep (se 2 (by rfl) ⟨270645, by rfl⟩ : syracuseStep 721721 = 541291) B541291
theorem B1082231 : Blo 479788 1082231 := bstep (se 1 (by rfl) ⟨811673, by rfl⟩ : syracuseStep 1082231 = 1623347) B1623347
theorem B721799 : Blo 479788 721799 := bstep (se 1 (by rfl) ⟨541349, by rfl⟩ : syracuseStep 721799 = 1082699) B1082699
theorem B721835 : Blo 479788 721835 := bstep (se 1 (by rfl) ⟨541376, by rfl⟩ : syracuseStep 721835 = 1082753) B1082753
theorem B721865 : Blo 479788 721865 := bstep (se 2 (by rfl) ⟨270699, by rfl⟩ : syracuseStep 721865 = 541399) B541399
theorem B1082411 : Blo 479788 1082411 := bstep (se 1 (by rfl) ⟨811808, by rfl⟩ : syracuseStep 1082411 = 1623617) B1623617
theorem B721979 : Blo 479788 721979 := bstep (se 1 (by rfl) ⟨541484, by rfl⟩ : syracuseStep 721979 = 1082969) B1082969
theorem B722039 : Blo 479788 722039 := bstep (se 1 (by rfl) ⟨541529, by rfl⟩ : syracuseStep 722039 = 1083059) B1083059
theorem B722063 : Blo 479788 722063 := bstep (se 1 (by rfl) ⟨541547, by rfl⟩ : syracuseStep 722063 = 1083095) B1083095
theorem B722105 : Blo 479788 722105 := bstep (se 2 (by rfl) ⟨270789, by rfl⟩ : syracuseStep 722105 = 541579) B541579
theorem B722183 : Blo 479788 722183 := bstep (se 1 (by rfl) ⟨541637, by rfl⟩ : syracuseStep 722183 = 1083275) B1083275
theorem B722219 : Blo 479788 722219 := bstep (se 1 (by rfl) ⟨541664, by rfl⟩ : syracuseStep 722219 = 1083329) B1083329
theorem B722249 : Blo 479788 722249 := bstep (se 2 (by rfl) ⟨270843, by rfl⟩ : syracuseStep 722249 = 541687) B541687
theorem B5211485 : Blo 479788 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B1082771 : Blo 479788 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B722363 : Blo 479788 722363 := bstep (se 1 (by rfl) ⟨541772, by rfl⟩ : syracuseStep 722363 = 1083545) B1083545
theorem B1082825 : Blo 479788 1082825 := bstep (se 2 (by rfl) ⟨406059, by rfl⟩ : syracuseStep 1082825 = 812119) B812119
theorem B722423 : Blo 479788 722423 := bstep (se 1 (by rfl) ⟨541817, by rfl⟩ : syracuseStep 722423 = 1083635) B1083635
theorem B2065931 : Blo 479788 2065931 := bstep (se 1 (by rfl) ⟨1549448, by rfl⟩ : syracuseStep 2065931 = 3098897) B3098897
theorem B722447 : Blo 479788 722447 := bstep (se 1 (by rfl) ⟨541835, by rfl⟩ : syracuseStep 722447 = 1083671) B1083671
theorem B2754071 : Blo 479788 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B722489 : Blo 479788 722489 := bstep (se 2 (by rfl) ⟨270933, by rfl⟩ : syracuseStep 722489 = 541867) B541867
theorem B36079181 : Blo 479788 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B4130423 : Blo 479788 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B722567 : Blo 479788 722567 := bstep (se 1 (by rfl) ⟨541925, by rfl⟩ : syracuseStep 722567 = 1083851) B1083851
theorem B722603 : Blo 479788 722603 := bstep (se 1 (by rfl) ⟨541952, by rfl⟩ : syracuseStep 722603 = 1083905) B1083905
theorem B5211827 : Blo 479788 5211827 := bstep (se 1 (by rfl) ⟨3908870, by rfl⟩ : syracuseStep 5211827 = 7817741) B7817741
theorem B722633 : Blo 479788 722633 := bstep (se 2 (by rfl) ⟨270987, by rfl⟩ : syracuseStep 722633 = 541975) B541975
theorem B5506865 : Blo 479788 5506865 := bstep (se 2 (by rfl) ⟨2065074, by rfl⟩ : syracuseStep 5506865 = 4130149) B4130149
theorem B722747 : Blo 479788 722747 := bstep (se 1 (by rfl) ⟨542060, by rfl⟩ : syracuseStep 722747 = 1084121) B1084121
theorem B722807 : Blo 479788 722807 := bstep (se 1 (by rfl) ⟨542105, by rfl⟩ : syracuseStep 722807 = 1084211) B1084211
theorem B1738631 : Blo 479788 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B722831 : Blo 479788 722831 := bstep (se 1 (by rfl) ⟨542123, by rfl⟩ : syracuseStep 722831 = 1084247) B1084247
theorem B1542041 : Blo 479788 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B722873 : Blo 479788 722873 := bstep (se 2 (by rfl) ⟨271077, by rfl⟩ : syracuseStep 722873 = 542155) B542155
theorem B722951 : Blo 479788 722951 := bstep (se 1 (by rfl) ⟨542213, by rfl⟩ : syracuseStep 722951 = 1084427) B1084427
theorem B722987 : Blo 479788 722987 := bstep (se 1 (by rfl) ⟨542240, by rfl⟩ : syracuseStep 722987 = 1084481) B1084481
theorem B723017 : Blo 479788 723017 := bstep (se 2 (by rfl) ⟨271131, by rfl⟩ : syracuseStep 723017 = 542263) B542263
theorem B1083527 : Blo 479788 1083527 := bstep (se 1 (by rfl) ⟨812645, by rfl⟩ : syracuseStep 1083527 = 1625291) B1625291
theorem B723131 : Blo 479788 723131 := bstep (se 1 (by rfl) ⟨542348, by rfl⟩ : syracuseStep 723131 = 1084697) B1084697
theorem B723191 : Blo 479788 723191 := bstep (se 1 (by rfl) ⟨542393, by rfl⟩ : syracuseStep 723191 = 1084787) B1084787
theorem B723215 : Blo 479788 723215 := bstep (se 1 (by rfl) ⟨542411, by rfl⟩ : syracuseStep 723215 = 1084823) B1084823
theorem B723257 : Blo 479788 723257 := bstep (se 2 (by rfl) ⟨271221, by rfl⟩ : syracuseStep 723257 = 542443) B542443
theorem B1083707 : Blo 479788 1083707 := bstep (se 1 (by rfl) ⟨812780, by rfl⟩ : syracuseStep 1083707 = 1625561) B1625561
theorem B723335 : Blo 479788 723335 := bstep (se 1 (by rfl) ⟨542501, by rfl⟩ : syracuseStep 723335 = 1085003) B1085003
theorem B723371 : Blo 479788 723371 := bstep (se 1 (by rfl) ⟨542528, by rfl⟩ : syracuseStep 723371 = 1085057) B1085057
theorem B1083833 : Blo 479788 1083833 := bstep (se 2 (by rfl) ⟨406437, by rfl⟩ : syracuseStep 1083833 = 812875) B812875
theorem B723401 : Blo 479788 723401 := bstep (se 2 (by rfl) ⟨271275, by rfl⟩ : syracuseStep 723401 = 542551) B542551
theorem B21629405 : Blo 479788 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B723515 : Blo 479788 723515 := bstep (se 1 (by rfl) ⟨542636, by rfl⟩ : syracuseStep 723515 = 1085273) B1085273
theorem B723575 : Blo 479788 723575 := bstep (se 1 (by rfl) ⟨542681, by rfl⟩ : syracuseStep 723575 = 1085363) B1085363
theorem B723599 : Blo 479788 723599 := bstep (se 1 (by rfl) ⟨542699, by rfl⟩ : syracuseStep 723599 = 1085399) B1085399
theorem B723641 : Blo 479788 723641 := bstep (se 2 (by rfl) ⟨271365, by rfl⟩ : syracuseStep 723641 = 542731) B542731
theorem B1215233 : Blo 479788 1215233 := bstep (se 2 (by rfl) ⟨455712, by rfl⟩ : syracuseStep 1215233 = 911425) B911425
theorem B723719 : Blo 479788 723719 := bstep (se 1 (by rfl) ⟨542789, by rfl⟩ : syracuseStep 723719 = 1085579) B1085579
theorem B7506703 : Blo 479788 7506703 := bstep (se 1 (by rfl) ⟨5630027, by rfl⟩ : syracuseStep 7506703 = 11260055) B11260055
theorem B1084175 : Blo 479788 1084175 := bstep (se 1 (by rfl) ⟨813131, by rfl⟩ : syracuseStep 1084175 = 1626263) B1626263
theorem B1084193 : Blo 479788 1084193 := bstep (se 2 (by rfl) ⟨406572, by rfl⟩ : syracuseStep 1084193 = 813145) B813145
theorem B723755 : Blo 479788 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B723785 : Blo 479788 723785 := bstep (se 2 (by rfl) ⟨271419, by rfl⟩ : syracuseStep 723785 = 542839) B542839
theorem B986041 : Blo 479788 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B723899 : Blo 479788 723899 := bstep (se 1 (by rfl) ⟨542924, by rfl⟩ : syracuseStep 723899 = 1085849) B1085849
theorem B723959 : Blo 479788 723959 := bstep (se 1 (by rfl) ⟨542969, by rfl⟩ : syracuseStep 723959 = 1085939) B1085939
theorem B723983 : Blo 479788 723983 := bstep (se 1 (by rfl) ⟨542987, by rfl⟩ : syracuseStep 723983 = 1085975) B1085975
theorem B724025 : Blo 479788 724025 := bstep (se 2 (by rfl) ⟨271509, by rfl⟩ : syracuseStep 724025 = 543019) B543019
theorem B1215607 : Blo 479788 1215607 := bstep (se 1 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 1215607 = 1823411) B1823411
theorem B1084535 : Blo 479788 1084535 := bstep (se 1 (by rfl) ⟨813401, by rfl⟩ : syracuseStep 1084535 = 1626803) B1626803
theorem B724103 : Blo 479788 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B724139 : Blo 479788 724139 := bstep (se 1 (by rfl) ⟨543104, by rfl⟩ : syracuseStep 724139 = 1086209) B1086209
theorem B724169 : Blo 479788 724169 := bstep (se 2 (by rfl) ⟨271563, by rfl⟩ : syracuseStep 724169 = 543127) B543127
theorem B1084715 : Blo 479788 1084715 := bstep (se 1 (by rfl) ⟨813536, by rfl⟩ : syracuseStep 1084715 = 1627073) B1627073
theorem B724283 : Blo 479788 724283 := bstep (se 1 (by rfl) ⟨543212, by rfl⟩ : syracuseStep 724283 = 1086425) B1086425
theorem B724343 : Blo 479788 724343 := bstep (se 1 (by rfl) ⟨543257, by rfl⟩ : syracuseStep 724343 = 1086515) B1086515
theorem B724367 : Blo 479788 724367 := bstep (se 1 (by rfl) ⟨543275, by rfl⟩ : syracuseStep 724367 = 1086551) B1086551
theorem B1740217 : Blo 479788 1740217 := bstep (se 2 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 1740217 = 1305163) B1305163
theorem B724409 : Blo 479788 724409 := bstep (se 2 (by rfl) ⟨271653, by rfl⟩ : syracuseStep 724409 = 543307) B543307
theorem B724487 : Blo 479788 724487 := bstep (se 1 (by rfl) ⟨543365, by rfl⟩ : syracuseStep 724487 = 1086731) B1086731
theorem B1216043 : Blo 479788 1216043 := bstep (se 1 (by rfl) ⟨912032, by rfl⟩ : syracuseStep 1216043 = 1824065) B1824065
theorem B724523 : Blo 479788 724523 := bstep (se 1 (by rfl) ⟨543392, by rfl⟩ : syracuseStep 724523 = 1086785) B1086785
theorem B724553 : Blo 479788 724553 := bstep (se 2 (by rfl) ⟨271707, by rfl⟩ : syracuseStep 724553 = 543415) B543415
theorem B1085075 : Blo 479788 1085075 := bstep (se 1 (by rfl) ⟨813806, by rfl⟩ : syracuseStep 1085075 = 1627613) B1627613
theorem B724667 : Blo 479788 724667 := bstep (se 1 (by rfl) ⟨543500, by rfl⟩ : syracuseStep 724667 = 1087001) B1087001
theorem B1085129 : Blo 479788 1085129 := bstep (se 2 (by rfl) ⟨406923, by rfl⟩ : syracuseStep 1085129 = 813847) B813847
theorem B724727 : Blo 479788 724727 := bstep (se 1 (by rfl) ⟨543545, by rfl⟩ : syracuseStep 724727 = 1087091) B1087091
theorem B724751 : Blo 479788 724751 := bstep (se 1 (by rfl) ⟨543563, by rfl⟩ : syracuseStep 724751 = 1087127) B1087127
theorem B724793 : Blo 479788 724793 := bstep (se 2 (by rfl) ⟨271797, by rfl⟩ : syracuseStep 724793 = 543595) B543595
theorem B724871 : Blo 479788 724871 := bstep (se 1 (by rfl) ⟨543653, by rfl⟩ : syracuseStep 724871 = 1087307) B1087307
theorem B5476247 : Blo 479788 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B724907 : Blo 479788 724907 := bstep (se 1 (by rfl) ⟨543680, by rfl⟩ : syracuseStep 724907 = 1087361) B1087361
theorem B823241 : Blo 479788 823241 := bstep (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) B617431
theorem B724937 : Blo 479788 724937 := bstep (se 2 (by rfl) ⟨271851, by rfl⟩ : syracuseStep 724937 = 543703) B543703
theorem B725051 : Blo 479788 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B725111 : Blo 479788 725111 := bstep (se 1 (by rfl) ⟨543833, by rfl⟩ : syracuseStep 725111 = 1087667) B1087667
theorem B725135 : Blo 479788 725135 := bstep (se 1 (by rfl) ⟨543851, by rfl⟩ : syracuseStep 725135 = 1087703) B1087703
theorem B725177 : Blo 479788 725177 := bstep (se 2 (by rfl) ⟨271941, by rfl⟩ : syracuseStep 725177 = 543883) B543883
theorem B725255 : Blo 479788 725255 := bstep (se 1 (by rfl) ⟨543941, by rfl⟩ : syracuseStep 725255 = 1087883) B1087883
theorem B725291 : Blo 479788 725291 := bstep (se 1 (by rfl) ⟨543968, by rfl⟩ : syracuseStep 725291 = 1087937) B1087937
theorem B725321 : Blo 479788 725321 := bstep (se 2 (by rfl) ⟨271995, by rfl⟩ : syracuseStep 725321 = 543991) B543991
theorem B1216883 : Blo 479788 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B1216903 : Blo 479788 1216903 := bstep (se 1 (by rfl) ⟨912677, by rfl⟩ : syracuseStep 1216903 = 1825355) B1825355
theorem B1085831 : Blo 479788 1085831 := bstep (se 1 (by rfl) ⟨814373, by rfl⟩ : syracuseStep 1085831 = 1628747) B1628747
theorem B725435 : Blo 479788 725435 := bstep (se 1 (by rfl) ⟨544076, by rfl⟩ : syracuseStep 725435 = 1088153) B1088153
theorem B725495 : Blo 479788 725495 := bstep (se 1 (by rfl) ⟨544121, by rfl⟩ : syracuseStep 725495 = 1088243) B1088243
theorem B725519 : Blo 479788 725519 := bstep (se 1 (by rfl) ⟨544139, by rfl⟩ : syracuseStep 725519 = 1088279) B1088279
theorem B725561 : Blo 479788 725561 := bstep (se 2 (by rfl) ⟨272085, by rfl⟩ : syracuseStep 725561 = 544171) B544171
theorem B1086011 : Blo 479788 1086011 := bstep (se 1 (by rfl) ⟨814508, by rfl⟩ : syracuseStep 1086011 = 1629017) B1629017
theorem B725639 : Blo 479788 725639 := bstep (se 1 (by rfl) ⟨544229, by rfl⟩ : syracuseStep 725639 = 1088459) B1088459
theorem B1217177 : Blo 479788 1217177 := bstep (se 2 (by rfl) ⟨456441, by rfl⟩ : syracuseStep 1217177 = 912883) B912883
theorem B725675 : Blo 479788 725675 := bstep (se 1 (by rfl) ⟨544256, by rfl⟩ : syracuseStep 725675 = 1088513) B1088513
theorem B13931189 : Blo 479788 13931189 := bstep (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) B1306049
theorem B1086137 : Blo 479788 1086137 := bstep (se 2 (by rfl) ⟨407301, by rfl⟩ : syracuseStep 1086137 = 814603) B814603
theorem B4690649 : Blo 479788 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B1741601 : Blo 479788 1741601 := bstep (se 2 (by rfl) ⟨653100, by rfl⟩ : syracuseStep 1741601 = 1306201) B1306201
theorem B1217339 : Blo 479788 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B1643417 : Blo 479788 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B1217551 : Blo 479788 1217551 := bstep (se 1 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 1217551 = 1826327) B1826327
theorem B1086479 : Blo 479788 1086479 := bstep (se 1 (by rfl) ⟨814859, by rfl⟩ : syracuseStep 1086479 = 1629719) B1629719
theorem B1086497 : Blo 479788 1086497 := bstep (se 2 (by rfl) ⟨407436, by rfl⟩ : syracuseStep 1086497 = 814873) B814873
theorem B1217825 : Blo 479788 1217825 := bstep (se 2 (by rfl) ⟨456684, by rfl⟩ : syracuseStep 1217825 = 913369) B913369
theorem B2430323 : Blo 479788 2430323 := bstep (se 1 (by rfl) ⟨1822742, by rfl⟩ : syracuseStep 2430323 = 3645485) B3645485
theorem B1086839 : Blo 479788 1086839 := bstep (se 1 (by rfl) ⟨815129, by rfl⟩ : syracuseStep 1086839 = 1630259) B1630259
theorem B1087019 : Blo 479788 1087019 := bstep (se 1 (by rfl) ⟨815264, by rfl⟩ : syracuseStep 1087019 = 1630529) B1630529
theorem B3479107 : Blo 479788 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B2430809 : Blo 479788 2430809 := bstep (se 2 (by rfl) ⟨911553, by rfl⟩ : syracuseStep 2430809 = 1823107) B1823107
theorem B1087379 : Blo 479788 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B1087433 : Blo 479788 1087433 := bstep (se 2 (by rfl) ⟨407787, by rfl⟩ : syracuseStep 1087433 = 815575) B815575
theorem B1218827 : Blo 479788 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B4954553 : Blo 479788 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B2202173 : Blo 479788 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1088135 : Blo 479788 1088135 := bstep (se 1 (by rfl) ⟨816101, by rfl⟩ : syracuseStep 1088135 = 1632203) B1632203
theorem B1088315 : Blo 479788 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B1219475 : Blo 479788 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B8919989 : Blo 479788 8919989 := bstep (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) B836249
theorem B1088441 : Blo 479788 1088441 := bstep (se 2 (by rfl) ⟨408165, by rfl⟩ : syracuseStep 1088441 = 816331) B816331
theorem B1219769 : Blo 479788 1219769 := bstep (se 2 (by rfl) ⟨457413, by rfl⟩ : syracuseStep 1219769 = 914827) B914827
theorem B2465291 : Blo 479788 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B1220467 : Blo 479788 1220467 := bstep (se 1 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 1220467 = 1830701) B1830701
theorem B2432915 : Blo 479788 2432915 := bstep (se 1 (by rfl) ⟨1824686, by rfl⟩ : syracuseStep 2432915 = 3649373) B3649373
theorem B1220609 : Blo 479788 1220609 := bstep (se 2 (by rfl) ⟨457728, by rfl⟩ : syracuseStep 1220609 = 915457) B915457
theorem B5480621 : Blo 479788 5480621 := bstep (se 3 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 5480621 = 2055233) B2055233
theorem B1221065 : Blo 479788 1221065 := bstep (se 2 (by rfl) ⟨457899, by rfl⟩ : syracuseStep 1221065 = 915799) B915799
theorem B1221419 : Blo 479788 1221419 := bstep (se 1 (by rfl) ⟨916064, by rfl⟩ : syracuseStep 1221419 = 1832129) B1832129
theorem B1549115 : Blo 479788 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B1024969 : Blo 479788 1024969 := bstep (se 2 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 1024969 = 768727) B768727
theorem B762895 : Blo 479788 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B1025225 : Blo 479788 1025225 := bstep (se 2 (by rfl) ⟨384459, by rfl⟩ : syracuseStep 1025225 = 768919) B768919
theorem B2204873 : Blo 479788 2204873 := bstep (se 2 (by rfl) ⟨826827, by rfl⟩ : syracuseStep 2204873 = 1653655) B1653655
theorem B2598259 : Blo 479788 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B3908999 : Blo 479788 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B9282995 : Blo 479788 9282995 := bstep (se 1 (by rfl) ⟨6962246, by rfl⟩ : syracuseStep 9282995 = 13924493) B13924493
theorem B1222411 : Blo 479788 1222411 := bstep (se 1 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 1222411 = 1833617) B1833617
theorem B6170417 : Blo 479788 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B1222553 : Blo 479788 1222553 := bstep (se 2 (by rfl) ⟨458457, by rfl⟩ : syracuseStep 1222553 = 916915) B916915
theorem B1222715 : Blo 479788 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B4696379 : Blo 479788 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B1223059 : Blo 479788 1223059 := bstep (se 1 (by rfl) ⟨917294, by rfl⟩ : syracuseStep 1223059 = 1834589) B1834589
theorem B1223201 : Blo 479788 1223201 := bstep (se 2 (by rfl) ⟨458700, by rfl⟩ : syracuseStep 1223201 = 917401) B917401
theorem B1026695 : Blo 479788 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B2435993 : Blo 479788 2435993 := bstep (se 2 (by rfl) ⟨913497, by rfl⟩ : syracuseStep 2435993 = 1826995) B1826995
theorem B2600207 : Blo 479788 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B1224193 : Blo 479788 1224193 := bstep (se 2 (by rfl) ⟨459072, by rfl⟩ : syracuseStep 1224193 = 918145) B918145
theorem B4959809 : Blo 479788 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B1027703 : Blo 479788 1027703 := bstep (se 1 (by rfl) ⟨770777, by rfl⟩ : syracuseStep 1027703 = 1541555) B1541555
theorem B1027883 : Blo 479788 1027883 := bstep (se 1 (by rfl) ⟨770912, by rfl⟩ : syracuseStep 1027883 = 1541825) B1541825
theorem B733303 : Blo 479788 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B733583 : Blo 479788 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B8794817 : Blo 479788 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B2306951 : Blo 479788 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B1094699 : Blo 479788 1094699 := bstep (se 1 (by rfl) ⟨821024, by rfl⟩ : syracuseStep 1094699 = 1642049) B1642049
theorem B3487121 : Blo 479788 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B1029523 : Blo 479788 1029523 := bstep (se 1 (by rfl) ⟨772142, by rfl⟩ : syracuseStep 1029523 = 1544285) B1544285
theorem B2438585 : Blo 479788 2438585 := bstep (se 2 (by rfl) ⟨914469, by rfl⟩ : syracuseStep 2438585 = 1828939) B1828939
theorem B1652285 : Blo 479788 1652285 := bstep (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) B619607
theorem B1160905 : Blo 479788 1160905 := bstep (se 2 (by rfl) ⟨435339, by rfl⟩ : syracuseStep 1160905 = 870679) B870679
theorem B12564497 : Blo 479788 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B2308333 : Blo 479788 2308333 := bstep (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) B865625
theorem B1620377 : Blo 479788 1620377 := bstep (se 2 (by rfl) ⟨607641, by rfl⟩ : syracuseStep 1620377 = 1215283) B1215283
theorem B3652289 : Blo 479788 3652289 := bstep (se 2 (by rfl) ⟨1369608, by rfl⟩ : syracuseStep 3652289 = 2739217) B2739217
theorem B2439881 : Blo 479788 2439881 := bstep (se 2 (by rfl) ⟨914955, by rfl⟩ : syracuseStep 2439881 = 1829911) B1829911
theorem B1522547 : Blo 479788 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B1850435 : Blo 479788 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B4996183 : Blo 479788 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B1621079 : Blo 479788 1621079 := bstep (se 1 (by rfl) ⟨1215809, by rfl⟩ : syracuseStep 1621079 = 2431619) B2431619
theorem B6929495 : Blo 479788 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B2604269 : Blo 479788 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B2473217 : Blo 479788 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B540175 : Blo 479788 540175 := bstep (se 1 (by rfl) ⟨405131, by rfl⟩ : syracuseStep 540175 = 810263) B810263
theorem B1621565 : Blo 479788 1621565 := bstep (se 3 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 1621565 = 608087) B608087
theorem B540679 : Blo 479788 540679 := bstep (se 1 (by rfl) ⟨405509, by rfl⟩ : syracuseStep 540679 = 811019) B811019
theorem B868487 : Blo 479788 868487 := bstep (se 1 (by rfl) ⟨651365, by rfl⟩ : syracuseStep 868487 = 1302731) B1302731
theorem B2736301 : Blo 479788 2736301 := bstep (se 3 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 2736301 = 1026113) B1026113
theorem B540859 : Blo 479788 540859 := bstep (se 1 (by rfl) ⟨405644, by rfl⟩ : syracuseStep 540859 = 811289) B811289
theorem B868897 : Blo 479788 868897 := bstep (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) B651673
theorem B5227051 : Blo 479788 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B5653111 : Blo 479788 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B541327 : Blo 479788 541327 := bstep (se 1 (by rfl) ⟨405995, by rfl⟩ : syracuseStep 541327 = 811991) B811991
theorem B5489369 : Blo 479788 5489369 := bstep (se 2 (by rfl) ⟨2058513, by rfl⟩ : syracuseStep 5489369 = 4117027) B4117027
theorem B869179 : Blo 479788 869179 := bstep (se 1 (by rfl) ⟨651884, by rfl⟩ : syracuseStep 869179 = 1303769) B1303769
theorem B1622969 : Blo 479788 1622969 := bstep (se 2 (by rfl) ⟨608613, by rfl⟩ : syracuseStep 1622969 = 1217227) B1217227
theorem B1033145 : Blo 479788 1033145 := bstep (se 2 (by rfl) ⟨387429, by rfl⟩ : syracuseStep 1033145 = 774859) B774859
theorem B1459259 : Blo 479788 1459259 := bstep (se 1 (by rfl) ⟨1094444, by rfl⟩ : syracuseStep 1459259 = 2188889) B2188889
theorem B541831 : Blo 479788 541831 := bstep (se 1 (by rfl) ⟨406373, by rfl⟩ : syracuseStep 541831 = 812747) B812747
theorem B607495 : Blo 479788 607495 := bstep (se 1 (by rfl) ⟨455621, by rfl⟩ : syracuseStep 607495 = 911243) B911243
theorem B542011 : Blo 479788 542011 := bstep (se 1 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 542011 = 813017) B813017
theorem B2115001 : Blo 479788 2115001 := bstep (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) B1586251
theorem B1623563 : Blo 479788 1623563 := bstep (se 1 (by rfl) ⟨1217672, by rfl⟩ : syracuseStep 1623563 = 2435345) B2435345
theorem B1394209 : Blo 479788 1394209 := bstep (se 2 (by rfl) ⟨522828, by rfl⟩ : syracuseStep 1394209 = 1045657) B1045657
theorem B8209997 : Blo 479788 8209997 := bstep (se 3 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 8209997 = 3078749) B3078749
theorem B1623671 : Blo 479788 1623671 := bstep (se 1 (by rfl) ⟨1217753, by rfl⟩ : syracuseStep 1623671 = 2435507) B2435507
theorem B607915 : Blo 479788 607915 := bstep (se 1 (by rfl) ⟨455936, by rfl⟩ : syracuseStep 607915 = 911873) B911873
theorem B542479 : Blo 479788 542479 := bstep (se 1 (by rfl) ⟨406859, by rfl⟩ : syracuseStep 542479 = 813719) B813719
theorem B608143 : Blo 479788 608143 := bstep (se 1 (by rfl) ⟨456107, by rfl⟩ : syracuseStep 608143 = 912215) B912215
theorem B3655691 : Blo 479788 3655691 := bstep (se 1 (by rfl) ⟨2741768, by rfl⟩ : syracuseStep 3655691 = 5483537) B5483537
theorem B2050109 : Blo 479788 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B1624265 : Blo 479788 1624265 := bstep (se 2 (by rfl) ⟨609099, by rfl⟩ : syracuseStep 1624265 = 1218199) B1218199
theorem B542983 : Blo 479788 542983 := bstep (se 1 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 542983 = 814475) B814475
theorem B15616273 : Blo 479788 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B543163 : Blo 479788 543163 := bstep (se 1 (by rfl) ⟨407372, by rfl⟩ : syracuseStep 543163 = 814745) B814745
theorem B772553 : Blo 479788 772553 := bstep (se 2 (by rfl) ⟨289707, by rfl⟩ : syracuseStep 772553 = 579415) B579415
theorem B1395215 : Blo 479788 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B2738717 : Blo 479788 2738717 := bstep (se 3 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 2738717 = 1027019) B1027019
theorem B2345539 : Blo 479788 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B608887 : Blo 479788 608887 := bstep (se 1 (by rfl) ⟨456665, by rfl⟩ : syracuseStep 608887 = 913331) B913331
theorem B871031 : Blo 479788 871031 := bstep (se 1 (by rfl) ⟨653273, by rfl⟩ : syracuseStep 871031 = 1306547) B1306547
theorem B6933185 : Blo 479788 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B5917475 : Blo 479788 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B1624967 : Blo 479788 1624967 := bstep (se 1 (by rfl) ⟨1218725, by rfl⟩ : syracuseStep 1624967 = 2437451) B2437451
theorem B543631 : Blo 479788 543631 := bstep (se 1 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 543631 = 815447) B815447
theorem B609211 : Blo 479788 609211 := bstep (se 1 (by rfl) ⟨456908, by rfl⟩ : syracuseStep 609211 = 913817) B913817
theorem B2608075 : Blo 479788 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B1821953 : Blo 479788 1821953 := bstep (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) B1366465
theorem B1625345 : Blo 479788 1625345 := bstep (se 2 (by rfl) ⟨609504, by rfl⟩ : syracuseStep 1625345 = 1219009) B1219009
theorem B871723 : Blo 479788 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B2084231 : Blo 479788 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B544135 : Blo 479788 544135 := bstep (se 1 (by rfl) ⟨408101, by rfl⟩ : syracuseStep 544135 = 816203) B816203
theorem B609707 : Blo 479788 609707 := bstep (se 1 (by rfl) ⟨457280, by rfl⟩ : syracuseStep 609707 = 914561) B914561
theorem B2969041 : Blo 479788 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B1822409 : Blo 479788 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B741163 : Blo 479788 741163 := bstep (se 1 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 741163 = 1111745) B1111745
theorem B9260851 : Blo 479788 9260851 := bstep (se 1 (by rfl) ⟨6945638, by rfl⟩ : syracuseStep 9260851 = 13891277) B13891277
theorem B610183 : Blo 479788 610183 := bstep (se 1 (by rfl) ⟨457637, by rfl⟩ : syracuseStep 610183 = 915275) B915275
theorem B3657635 : Blo 479788 3657635 := bstep (se 1 (by rfl) ⟨2743226, by rfl⟩ : syracuseStep 3657635 = 5486453) B5486453
theorem B2052125 : Blo 479788 2052125 := bstep (se 3 (by rfl) ⟨384773, by rfl⟩ : syracuseStep 2052125 = 769547) B769547
theorem B1626155 : Blo 479788 1626155 := bstep (se 1 (by rfl) ⟨1219616, by rfl⟩ : syracuseStep 1626155 = 2439233) B2439233
theorem B610679 : Blo 479788 610679 := bstep (se 1 (by rfl) ⟨458009, by rfl⟩ : syracuseStep 610679 = 916019) B916019
theorem B2445713 : Blo 479788 2445713 := bstep (se 2 (by rfl) ⟨917142, by rfl⟩ : syracuseStep 2445713 = 1834285) B1834285
theorem B610831 : Blo 479788 610831 := bstep (se 1 (by rfl) ⟨458123, by rfl⟩ : syracuseStep 610831 = 916247) B916247
theorem B479803 : Blo 479788 479803 := bstep (se 1 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 479803 = 719705) B719705
theorem B774775 : Blo 479788 774775 := bstep (se 1 (by rfl) ⟨581081, by rfl⟩ : syracuseStep 774775 = 1162163) B1162163
theorem B479879 : Blo 479788 479879 := bstep (se 1 (by rfl) ⟨359909, by rfl⟩ : syracuseStep 479879 = 719819) B719819
theorem B479887 : Blo 479788 479887 := bstep (se 1 (by rfl) ⟨359915, by rfl⟩ : syracuseStep 479887 = 719831) B719831
theorem B479931 : Blo 479788 479931 := bstep (se 1 (by rfl) ⟨359948, by rfl⟩ : syracuseStep 479931 = 719897) B719897
theorem B611003 : Blo 479788 611003 := bstep (se 1 (by rfl) ⟨458252, by rfl⟩ : syracuseStep 611003 = 916505) B916505
theorem B2052809 : Blo 479788 2052809 := bstep (se 2 (by rfl) ⟨769803, by rfl⟩ : syracuseStep 2052809 = 1539607) B1539607
theorem B480007 : Blo 479788 480007 := bstep (se 1 (by rfl) ⟨360005, by rfl⟩ : syracuseStep 480007 = 720011) B720011
theorem B480015 : Blo 479788 480015 := bstep (se 1 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 480015 = 720023) B720023
theorem B480059 : Blo 479788 480059 := bstep (se 1 (by rfl) ⟨360044, by rfl⟩ : syracuseStep 480059 = 720089) B720089
theorem B5198681 : Blo 479788 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B512903 : Blo 479788 512903 := bstep (se 1 (by rfl) ⟨384677, by rfl⟩ : syracuseStep 512903 = 769355) B769355
theorem B480135 : Blo 479788 480135 := bstep (se 1 (by rfl) ⟨360101, by rfl⟩ : syracuseStep 480135 = 720203) B720203
theorem B480143 : Blo 479788 480143 := bstep (se 1 (by rfl) ⟨360107, by rfl⟩ : syracuseStep 480143 = 720215) B720215
theorem B480187 : Blo 479788 480187 := bstep (se 1 (by rfl) ⟨360140, by rfl⟩ : syracuseStep 480187 = 720281) B720281
theorem B2741201 : Blo 479788 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B480263 : Blo 479788 480263 := bstep (se 1 (by rfl) ⟨360197, by rfl⟩ : syracuseStep 480263 = 720395) B720395
theorem B480271 : Blo 479788 480271 := bstep (se 1 (by rfl) ⟨360203, by rfl⟩ : syracuseStep 480271 = 720407) B720407
theorem B480315 : Blo 479788 480315 := bstep (se 1 (by rfl) ⟨360236, by rfl⟩ : syracuseStep 480315 = 720473) B720473
theorem B480391 : Blo 479788 480391 := bstep (se 1 (by rfl) ⟨360293, by rfl⟩ : syracuseStep 480391 = 720587) B720587
theorem B480399 : Blo 479788 480399 := bstep (se 1 (by rfl) ⟨360299, by rfl⟩ : syracuseStep 480399 = 720599) B720599
theorem B480443 : Blo 479788 480443 := bstep (se 1 (by rfl) ⟨360332, by rfl⟩ : syracuseStep 480443 = 720665) B720665
theorem B2610413 : Blo 479788 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B480519 : Blo 479788 480519 := bstep (se 1 (by rfl) ⟨360389, by rfl⟩ : syracuseStep 480519 = 720779) B720779
theorem B480527 : Blo 479788 480527 := bstep (se 1 (by rfl) ⟨360395, by rfl⟩ : syracuseStep 480527 = 720791) B720791
theorem B480571 : Blo 479788 480571 := bstep (se 1 (by rfl) ⟨360428, by rfl⟩ : syracuseStep 480571 = 720857) B720857
theorem B1627451 : Blo 479788 1627451 := bstep (se 1 (by rfl) ⟨1220588, by rfl⟩ : syracuseStep 1627451 = 2441177) B2441177
theorem B480647 : Blo 479788 480647 := bstep (se 1 (by rfl) ⟨360485, by rfl⟩ : syracuseStep 480647 = 720971) B720971
theorem B480655 : Blo 479788 480655 := bstep (se 1 (by rfl) ⟨360491, by rfl⟩ : syracuseStep 480655 = 720983) B720983
theorem B480699 : Blo 479788 480699 := bstep (se 1 (by rfl) ⟨360524, by rfl⟩ : syracuseStep 480699 = 721049) B721049
theorem B480775 : Blo 479788 480775 := bstep (se 1 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 480775 = 721163) B721163
theorem B480783 : Blo 479788 480783 := bstep (se 1 (by rfl) ⟨360587, by rfl⟩ : syracuseStep 480783 = 721175) B721175
theorem B480827 : Blo 479788 480827 := bstep (se 1 (by rfl) ⟨360620, by rfl⟩ : syracuseStep 480827 = 721241) B721241
theorem B480903 : Blo 479788 480903 := bstep (se 1 (by rfl) ⟨360677, by rfl⟩ : syracuseStep 480903 = 721355) B721355
theorem B611975 : Blo 479788 611975 := bstep (se 1 (by rfl) ⟨458981, by rfl⟩ : syracuseStep 611975 = 917963) B917963
theorem B480911 : Blo 479788 480911 := bstep (se 1 (by rfl) ⟨360683, by rfl⟩ : syracuseStep 480911 = 721367) B721367
theorem B480955 : Blo 479788 480955 := bstep (se 1 (by rfl) ⟨360716, by rfl⟩ : syracuseStep 480955 = 721433) B721433
theorem B17553125 : Blo 479788 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B481031 : Blo 479788 481031 := bstep (se 1 (by rfl) ⟨360773, by rfl⟩ : syracuseStep 481031 = 721547) B721547
theorem B481039 : Blo 479788 481039 := bstep (se 1 (by rfl) ⟨360779, by rfl⟩ : syracuseStep 481039 = 721559) B721559
theorem B1627937 : Blo 479788 1627937 := bstep (se 2 (by rfl) ⟨610476, by rfl⟩ : syracuseStep 1627937 = 1220953) B1220953
theorem B481083 : Blo 479788 481083 := bstep (se 1 (by rfl) ⟨360812, by rfl⟩ : syracuseStep 481083 = 721625) B721625
theorem B27121483 : Blo 479788 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B481159 : Blo 479788 481159 := bstep (se 1 (by rfl) ⟨360869, by rfl⟩ : syracuseStep 481159 = 721739) B721739
theorem B481167 : Blo 479788 481167 := bstep (se 1 (by rfl) ⟨360875, by rfl⟩ : syracuseStep 481167 = 721751) B721751
theorem B481211 : Blo 479788 481211 := bstep (se 1 (by rfl) ⟨360908, by rfl⟩ : syracuseStep 481211 = 721817) B721817
theorem B481287 : Blo 479788 481287 := bstep (se 1 (by rfl) ⟨360965, by rfl⟩ : syracuseStep 481287 = 721931) B721931
theorem B481295 : Blo 479788 481295 := bstep (se 1 (by rfl) ⟨360971, by rfl⟩ : syracuseStep 481295 = 721943) B721943
theorem B481339 : Blo 479788 481339 := bstep (se 1 (by rfl) ⟨361004, by rfl⟩ : syracuseStep 481339 = 722009) B722009
theorem B481415 : Blo 479788 481415 := bstep (se 1 (by rfl) ⟨361061, by rfl⟩ : syracuseStep 481415 = 722123) B722123
theorem B481423 : Blo 479788 481423 := bstep (se 1 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 481423 = 722135) B722135
theorem B481467 : Blo 479788 481467 := bstep (se 1 (by rfl) ⟨361100, by rfl⟩ : syracuseStep 481467 = 722201) B722201
theorem B481543 : Blo 479788 481543 := bstep (se 1 (by rfl) ⟨361157, by rfl⟩ : syracuseStep 481543 = 722315) B722315
theorem B1366283 : Blo 479788 1366283 := bstep (se 1 (by rfl) ⟨1024712, by rfl⟩ : syracuseStep 1366283 = 2049425) B2049425
theorem B481551 : Blo 479788 481551 := bstep (se 1 (by rfl) ⟨361163, by rfl⟩ : syracuseStep 481551 = 722327) B722327
theorem B3660065 : Blo 479788 3660065 := bstep (se 2 (by rfl) ⟨1372524, by rfl⟩ : syracuseStep 3660065 = 2745049) B2745049
theorem B481595 : Blo 479788 481595 := bstep (se 1 (by rfl) ⟨361196, by rfl⟩ : syracuseStep 481595 = 722393) B722393
theorem B1628531 : Blo 479788 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B481671 : Blo 479788 481671 := bstep (se 1 (by rfl) ⟨361253, by rfl⟩ : syracuseStep 481671 = 722507) B722507
theorem B481679 : Blo 479788 481679 := bstep (se 1 (by rfl) ⟨361259, by rfl⟩ : syracuseStep 481679 = 722519) B722519
theorem B2054585 : Blo 479788 2054585 := bstep (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) B1540939
theorem B481723 : Blo 479788 481723 := bstep (se 1 (by rfl) ⟨361292, by rfl⟩ : syracuseStep 481723 = 722585) B722585
theorem B2447819 : Blo 479788 2447819 := bstep (se 1 (by rfl) ⟨1835864, by rfl⟩ : syracuseStep 2447819 = 3671729) B3671729
theorem B481799 : Blo 479788 481799 := bstep (se 1 (by rfl) ⟨361349, by rfl⟩ : syracuseStep 481799 = 722699) B722699
theorem B481807 : Blo 479788 481807 := bstep (se 1 (by rfl) ⟨361355, by rfl⟩ : syracuseStep 481807 = 722711) B722711
theorem B9361955 : Blo 479788 9361955 := bstep (se 1 (by rfl) ⟨7021466, by rfl⟩ : syracuseStep 9361955 = 14042933) B14042933
theorem B481851 : Blo 479788 481851 := bstep (se 1 (by rfl) ⟨361388, by rfl⟩ : syracuseStep 481851 = 722777) B722777
theorem B481927 : Blo 479788 481927 := bstep (se 1 (by rfl) ⟨361445, by rfl⟩ : syracuseStep 481927 = 722891) B722891
theorem B481935 : Blo 479788 481935 := bstep (se 1 (by rfl) ⟨361451, by rfl⟩ : syracuseStep 481935 = 722903) B722903
theorem B481979 : Blo 479788 481979 := bstep (se 1 (by rfl) ⟨361484, by rfl⟩ : syracuseStep 481979 = 722969) B722969
theorem B1825537 : Blo 479788 1825537 := bstep (se 2 (by rfl) ⟨684576, by rfl⟩ : syracuseStep 1825537 = 1369153) B1369153
theorem B482055 : Blo 479788 482055 := bstep (se 1 (by rfl) ⟨361541, by rfl⟩ : syracuseStep 482055 = 723083) B723083
theorem B809743 : Blo 479788 809743 := bstep (se 1 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 809743 = 1214615) B1214615
theorem B482063 : Blo 479788 482063 := bstep (se 1 (by rfl) ⟨361547, by rfl⟩ : syracuseStep 482063 = 723095) B723095
theorem B2448143 : Blo 479788 2448143 := bstep (se 1 (by rfl) ⟨1836107, by rfl⟩ : syracuseStep 2448143 = 3672215) B3672215
theorem B2743091 : Blo 479788 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B482107 : Blo 479788 482107 := bstep (se 1 (by rfl) ⟨361580, by rfl⟩ : syracuseStep 482107 = 723161) B723161
theorem B482183 : Blo 479788 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B482191 : Blo 479788 482191 := bstep (se 1 (by rfl) ⟨361643, by rfl⟩ : syracuseStep 482191 = 723287) B723287
theorem B580495 : Blo 479788 580495 := bstep (se 1 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 580495 = 870743) B870743
theorem B482235 : Blo 479788 482235 := bstep (se 1 (by rfl) ⟨361676, by rfl⟩ : syracuseStep 482235 = 723353) B723353
theorem B482311 : Blo 479788 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B482319 : Blo 479788 482319 := bstep (se 1 (by rfl) ⟨361739, by rfl⟩ : syracuseStep 482319 = 723479) B723479
theorem B482363 : Blo 479788 482363 := bstep (se 1 (by rfl) ⟨361772, by rfl⟩ : syracuseStep 482363 = 723545) B723545
theorem B6151301 : Blo 479788 6151301 := bstep (se 4 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 6151301 = 1153369) B1153369
theorem B482439 : Blo 479788 482439 := bstep (se 1 (by rfl) ⟨361829, by rfl⟩ : syracuseStep 482439 = 723659) B723659
theorem B482447 : Blo 479788 482447 := bstep (se 1 (by rfl) ⟨361835, by rfl⟩ : syracuseStep 482447 = 723671) B723671
theorem B482491 : Blo 479788 482491 := bstep (se 1 (by rfl) ⟨361868, by rfl⟩ : syracuseStep 482491 = 723737) B723737
theorem B3661037 : Blo 479788 3661037 := bstep (se 3 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 3661037 = 1372889) B1372889
theorem B482567 : Blo 479788 482567 := bstep (se 1 (by rfl) ⟨361925, by rfl⟩ : syracuseStep 482567 = 723851) B723851
theorem B482575 : Blo 479788 482575 := bstep (se 1 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 482575 = 723863) B723863
theorem B1301789 : Blo 479788 1301789 := bstep (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) B488171
theorem B810283 : Blo 479788 810283 := bstep (se 1 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 810283 = 1215425) B1215425
theorem B482619 : Blo 479788 482619 := bstep (se 1 (by rfl) ⟨361964, by rfl⟩ : syracuseStep 482619 = 723929) B723929
theorem B482695 : Blo 479788 482695 := bstep (se 1 (by rfl) ⟨362021, by rfl⟩ : syracuseStep 482695 = 724043) B724043
theorem B482703 : Blo 479788 482703 := bstep (se 1 (by rfl) ⟨362027, by rfl⟩ : syracuseStep 482703 = 724055) B724055
theorem B810425 : Blo 479788 810425 := bstep (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) B607819
theorem B482747 : Blo 479788 482747 := bstep (se 1 (by rfl) ⟨362060, by rfl⟩ : syracuseStep 482747 = 724121) B724121
theorem B482823 : Blo 479788 482823 := bstep (se 1 (by rfl) ⟨362117, by rfl⟩ : syracuseStep 482823 = 724235) B724235
theorem B482831 : Blo 479788 482831 := bstep (se 1 (by rfl) ⟨362123, by rfl⟩ : syracuseStep 482831 = 724247) B724247
theorem B482875 : Blo 479788 482875 := bstep (se 1 (by rfl) ⟨362156, by rfl⟩ : syracuseStep 482875 = 724313) B724313
theorem B482951 : Blo 479788 482951 := bstep (se 1 (by rfl) ⟨362213, by rfl⟩ : syracuseStep 482951 = 724427) B724427
theorem B482959 : Blo 479788 482959 := bstep (se 1 (by rfl) ⟨362219, by rfl⟩ : syracuseStep 482959 = 724439) B724439
theorem B483003 : Blo 479788 483003 := bstep (se 1 (by rfl) ⟨362252, by rfl⟩ : syracuseStep 483003 = 724505) B724505
theorem B2055917 : Blo 479788 2055917 := bstep (se 3 (by rfl) ⟨385484, by rfl⟩ : syracuseStep 2055917 = 770969) B770969
theorem B1957613 : Blo 479788 1957613 := bstep (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) B734105
theorem B483079 : Blo 479788 483079 := bstep (se 1 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 483079 = 724619) B724619
theorem B515855 : Blo 479788 515855 := bstep (se 1 (by rfl) ⟨386891, by rfl⟩ : syracuseStep 515855 = 773783) B773783
theorem B483087 : Blo 479788 483087 := bstep (se 1 (by rfl) ⟨362315, by rfl⟩ : syracuseStep 483087 = 724631) B724631
theorem B1367867 : Blo 479788 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B483131 : Blo 479788 483131 := bstep (se 1 (by rfl) ⟨362348, by rfl⟩ : syracuseStep 483131 = 724697) B724697
theorem B1367923 : Blo 479788 1367923 := bstep (se 1 (by rfl) ⟨1025942, by rfl⟩ : syracuseStep 1367923 = 2051885) B2051885
theorem B483207 : Blo 479788 483207 := bstep (se 1 (by rfl) ⟨362405, by rfl⟩ : syracuseStep 483207 = 724811) B724811
theorem B483215 : Blo 479788 483215 := bstep (se 1 (by rfl) ⟨362411, by rfl⟩ : syracuseStep 483215 = 724823) B724823
theorem B483259 : Blo 479788 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B483335 : Blo 479788 483335 := bstep (se 1 (by rfl) ⟨362501, by rfl⟩ : syracuseStep 483335 = 725003) B725003
theorem B483343 : Blo 479788 483343 := bstep (se 1 (by rfl) ⟨362507, by rfl⟩ : syracuseStep 483343 = 725015) B725015
theorem B483387 : Blo 479788 483387 := bstep (se 1 (by rfl) ⟨362540, by rfl⟩ : syracuseStep 483387 = 725081) B725081
theorem B2056259 : Blo 479788 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B811127 : Blo 479788 811127 := bstep (se 1 (by rfl) ⟨608345, by rfl⟩ : syracuseStep 811127 = 1216691) B1216691
theorem B5202053 : Blo 479788 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B483463 : Blo 479788 483463 := bstep (se 1 (by rfl) ⟨362597, by rfl⟩ : syracuseStep 483463 = 725195) B725195
theorem B483471 : Blo 479788 483471 := bstep (se 1 (by rfl) ⟨362603, by rfl⟩ : syracuseStep 483471 = 725207) B725207
theorem B483515 : Blo 479788 483515 := bstep (se 1 (by rfl) ⟨362636, by rfl⟩ : syracuseStep 483515 = 725273) B725273
theorem B1368265 : Blo 479788 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B2744549 : Blo 479788 2744549 := bstep (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) B514603
theorem B483591 : Blo 479788 483591 := bstep (se 1 (by rfl) ⟨362693, by rfl⟩ : syracuseStep 483591 = 725387) B725387
theorem B483599 : Blo 479788 483599 := bstep (se 1 (by rfl) ⟨362699, by rfl⟩ : syracuseStep 483599 = 725399) B725399
theorem B483643 : Blo 479788 483643 := bstep (se 1 (by rfl) ⟨362732, by rfl⟩ : syracuseStep 483643 = 725465) B725465
theorem B483719 : Blo 479788 483719 := bstep (se 1 (by rfl) ⟨362789, by rfl⟩ : syracuseStep 483719 = 725579) B725579
theorem B483727 : Blo 479788 483727 := bstep (se 1 (by rfl) ⟨362795, by rfl⟩ : syracuseStep 483727 = 725591) B725591
theorem B483771 : Blo 479788 483771 := bstep (se 1 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 483771 = 725657) B725657
theorem B811579 : Blo 479788 811579 := bstep (se 1 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 811579 = 1217369) B1217369
theorem B811721 : Blo 479788 811721 := bstep (se 2 (by rfl) ⟨304395, by rfl⟩ : syracuseStep 811721 = 608791) B608791
theorem B2319137 : Blo 479788 2319137 := bstep (se 2 (by rfl) ⟨869676, by rfl⟩ : syracuseStep 2319137 = 1739353) B1739353
theorem B1631123 : Blo 479788 1631123 := bstep (se 1 (by rfl) ⟨1223342, by rfl⟩ : syracuseStep 1631123 = 2446685) B2446685
theorem B975905 : Blo 479788 975905 := bstep (se 2 (by rfl) ⟨365964, by rfl⟩ : syracuseStep 975905 = 731929) B731929
theorem B3662981 : Blo 479788 3662981 := bstep (se 4 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 3662981 = 686809) B686809
theorem B2974913 : Blo 479788 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B812423 : Blo 479788 812423 := bstep (se 1 (by rfl) ⟨609317, by rfl⟩ : syracuseStep 812423 = 1218635) B1218635
theorem B1467919 : Blo 479788 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B1828439 : Blo 479788 1828439 := bstep (se 1 (by rfl) ⟨1371329, by rfl⟩ : syracuseStep 1828439 = 2742659) B2742659
theorem B648905 : Blo 479788 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B976699 : Blo 479788 976699 := bstep (se 1 (by rfl) ⟨732524, by rfl⟩ : syracuseStep 976699 = 1465049) B1465049
theorem B4646807 : Blo 479788 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B813071 : Blo 479788 813071 := bstep (se 1 (by rfl) ⟨609803, by rfl⟩ : syracuseStep 813071 = 1219607) B1219607
theorem B4614205 : Blo 479788 4614205 := bstep (se 3 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 4614205 = 1730327) B1730327
theorem B1828925 : Blo 479788 1828925 := bstep (se 3 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 1828925 = 685847) B685847
theorem B1566977 : Blo 479788 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1468687 : Blo 479788 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B1632527 : Blo 479788 1632527 := bstep (se 1 (by rfl) ⟨1224395, by rfl⟩ : syracuseStep 1632527 = 2448791) B2448791
theorem B911675 : Blo 479788 911675 := bstep (se 1 (by rfl) ⟨683756, by rfl⟩ : syracuseStep 911675 = 1367513) B1367513
theorem B1370429 : Blo 479788 1370429 := bstep (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) B513911
theorem B1370657 : Blo 479788 1370657 := bstep (se 2 (by rfl) ⟨513996, by rfl⟩ : syracuseStep 1370657 = 1027993) B1027993
theorem B813611 : Blo 479788 813611 := bstep (se 1 (by rfl) ⟨610208, by rfl⟩ : syracuseStep 813611 = 1220417) B1220417
theorem B2091587 : Blo 479788 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B1043129 : Blo 479788 1043129 := bstep (se 2 (by rfl) ⟨391173, by rfl⟩ : syracuseStep 1043129 = 782347) B782347
theorem B4647617 : Blo 479788 4647617 := bstep (se 2 (by rfl) ⟨1742856, by rfl⟩ : syracuseStep 4647617 = 3485713) B3485713
theorem B3074831 : Blo 479788 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B1305359 : Blo 479788 1305359 := bstep (se 1 (by rfl) ⟨979019, by rfl⟩ : syracuseStep 1305359 = 1958039) B1958039
theorem B912161 : Blo 479788 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B41806691 : Blo 479788 41806691 := bstep (se 1 (by rfl) ⟨31355018, by rfl⟩ : syracuseStep 41806691 = 62710037) B62710037
theorem B1370999 : Blo 479788 1370999 := bstep (se 1 (by rfl) ⟨1028249, by rfl⟩ : syracuseStep 1370999 = 2056499) B2056499
theorem B912313 : Blo 479788 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B814009 : Blo 479788 814009 := bstep (se 2 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 814009 = 610507) B610507
theorem B3337453 : Blo 479788 3337453 := bstep (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) B1251545
theorem B1731899 : Blo 479788 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B2747783 : Blo 479788 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B3665411 : Blo 479788 3665411 := bstep (se 1 (by rfl) ⟨2749058, by rfl⟩ : syracuseStep 3665411 = 5498117) B5498117
theorem B1404431 : Blo 479788 1404431 := bstep (se 1 (by rfl) ⟨1053323, by rfl⟩ : syracuseStep 1404431 = 2106647) B2106647
theorem B2747965 : Blo 479788 2747965 := bstep (se 3 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 2747965 = 1030487) B1030487
theorem B814711 : Blo 479788 814711 := bstep (se 1 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 814711 = 1222067) B1222067
theorem B4615937 : Blo 479788 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B1830671 : Blo 479788 1830671 := bstep (se 1 (by rfl) ⟨1373003, by rfl⟩ : syracuseStep 1830671 = 2746007) B2746007
theorem B1240847 : Blo 479788 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B4615973 : Blo 479788 4615973 := bstep (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) B865495
theorem B814907 : Blo 479788 814907 := bstep (se 1 (by rfl) ⟨611180, by rfl⟩ : syracuseStep 814907 = 1222361) B1222361
theorem B815305 : Blo 479788 815305 := bstep (se 2 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 815305 = 611479) B611479
theorem B914105 : Blo 479788 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B783049 : Blo 479788 783049 := bstep (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) B587287
theorem B11760389 : Blo 479788 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B816007 : Blo 479788 816007 := bstep (se 1 (by rfl) ⟨612005, by rfl⟩ : syracuseStep 816007 = 1224011) B1224011
theorem B652279 : Blo 479788 652279 := bstep (se 1 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 652279 = 978419) B978419
theorem B90273005 : Blo 479788 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B2749697 : Blo 479788 2749697 := bstep (se 2 (by rfl) ⟨1031136, by rfl⟩ : syracuseStep 2749697 = 2062273) B2062273
theorem B1373527 : Blo 479788 1373527 := bstep (se 1 (by rfl) ⟨1030145, by rfl⟩ : syracuseStep 1373527 = 2060291) B2060291
theorem B1832327 : Blo 479788 1832327 := bstep (se 1 (by rfl) ⟨1374245, by rfl⟩ : syracuseStep 1832327 = 2748491) B2748491
theorem B1537427 : Blo 479788 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B3339667 : Blo 479788 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B1373755 : Blo 479788 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B1373881 : Blo 479788 1373881 := bstep (se 2 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 1373881 = 1030411) B1030411
theorem B1079567 : Blo 479788 1079567 := bstep (se 1 (by rfl) ⟨809675, by rfl⟩ : syracuseStep 1079567 = 1619351) B1619351
theorem B1079585 : Blo 479788 1079585 := bstep (se 2 (by rfl) ⟨404844, by rfl⟩ : syracuseStep 1079585 = 809689) B809689
theorem B4127111 : Blo 479788 4127111 := bstep (se 1 (by rfl) ⟨3095333, by rfl⟩ : syracuseStep 4127111 = 6190667) B6190667
theorem B1079927 : Blo 479788 1079927 := bstep (se 1 (by rfl) ⟨809945, by rfl⟩ : syracuseStep 1079927 = 1619891) B1619891
theorem B916103 : Blo 479788 916103 := bstep (se 1 (by rfl) ⟨687077, by rfl⟩ : syracuseStep 916103 = 1374155) B1374155
theorem B1080107 : Blo 479788 1080107 := bstep (se 1 (by rfl) ⟨810080, by rfl⟩ : syracuseStep 1080107 = 1620161) B1620161
theorem B719735 : Blo 479788 719735 := bstep (se 1 (by rfl) ⟨539801, by rfl⟩ : syracuseStep 719735 = 1079603) B1079603
theorem B719759 : Blo 479788 719759 := bstep (se 1 (by rfl) ⟨539819, by rfl⟩ : syracuseStep 719759 = 1079639) B1079639
theorem B719801 : Blo 479788 719801 := bstep (se 2 (by rfl) ⟨269925, by rfl⟩ : syracuseStep 719801 = 539851) B539851
theorem B719879 : Blo 479788 719879 := bstep (se 1 (by rfl) ⟨539909, by rfl⟩ : syracuseStep 719879 = 1079819) B1079819
theorem B719915 : Blo 479788 719915 := bstep (se 1 (by rfl) ⟨539936, by rfl⟩ : syracuseStep 719915 = 1079873) B1079873
theorem B719945 : Blo 479788 719945 := bstep (se 2 (by rfl) ⟨269979, by rfl⟩ : syracuseStep 719945 = 539959) B539959
theorem B1834103 : Blo 479788 1834103 := bstep (se 1 (by rfl) ⟨1375577, by rfl⟩ : syracuseStep 1834103 = 2751155) B2751155
theorem B1080467 : Blo 479788 1080467 := bstep (se 1 (by rfl) ⟨810350, by rfl⟩ : syracuseStep 1080467 = 1620701) B1620701
theorem B720059 : Blo 479788 720059 := bstep (se 1 (by rfl) ⟨540044, by rfl⟩ : syracuseStep 720059 = 1080089) B1080089
theorem B1080521 : Blo 479788 1080521 := bstep (se 2 (by rfl) ⟨405195, by rfl⟩ : syracuseStep 1080521 = 810391) B810391
theorem B687305 : Blo 479788 687305 := bstep (se 2 (by rfl) ⟨257739, by rfl⟩ : syracuseStep 687305 = 515479) B515479
theorem B720119 : Blo 479788 720119 := bstep (se 1 (by rfl) ⟨540089, by rfl⟩ : syracuseStep 720119 = 1080179) B1080179
theorem B720143 : Blo 479788 720143 := bstep (se 1 (by rfl) ⟨540107, by rfl⟩ : syracuseStep 720143 = 1080215) B1080215
theorem B720185 : Blo 479788 720185 := bstep (se 2 (by rfl) ⟨270069, by rfl⟩ : syracuseStep 720185 = 540139) B540139
theorem B9239939 : Blo 479788 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B720263 : Blo 479788 720263 := bstep (se 1 (by rfl) ⟨540197, by rfl⟩ : syracuseStep 720263 = 1080395) B1080395
theorem B720299 : Blo 479788 720299 := bstep (se 1 (by rfl) ⟨540224, by rfl⟩ : syracuseStep 720299 = 1080449) B1080449
theorem B720329 : Blo 479788 720329 := bstep (se 2 (by rfl) ⟨270123, by rfl⟩ : syracuseStep 720329 = 540247) B540247
theorem B720443 : Blo 479788 720443 := bstep (se 1 (by rfl) ⟨540332, by rfl⟩ : syracuseStep 720443 = 1080665) B1080665
theorem B1375805 : Blo 479788 1375805 := bstep (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) B515927
theorem B720503 : Blo 479788 720503 := bstep (se 1 (by rfl) ⟨540377, by rfl⟩ : syracuseStep 720503 = 1080755) B1080755
theorem B720527 : Blo 479788 720527 := bstep (se 1 (by rfl) ⟨540395, by rfl⟩ : syracuseStep 720527 = 1080791) B1080791
theorem B720569 : Blo 479788 720569 := bstep (se 2 (by rfl) ⟨270213, by rfl⟩ : syracuseStep 720569 = 540427) B540427
theorem B1539785 : Blo 479788 1539785 := bstep (se 2 (by rfl) ⟨577419, by rfl⟩ : syracuseStep 1539785 = 1154839) B1154839
theorem B720647 : Blo 479788 720647 := bstep (se 1 (by rfl) ⟨540485, by rfl⟩ : syracuseStep 720647 = 1080971) B1080971
theorem B720683 : Blo 479788 720683 := bstep (se 1 (by rfl) ⟨540512, by rfl⟩ : syracuseStep 720683 = 1081025) B1081025
theorem B720713 : Blo 479788 720713 := bstep (se 2 (by rfl) ⟨270267, by rfl⟩ : syracuseStep 720713 = 540535) B540535
theorem B1081223 : Blo 479788 1081223 := bstep (se 1 (by rfl) ⟨810917, by rfl⟩ : syracuseStep 1081223 = 1621835) B1621835
theorem B720827 : Blo 479788 720827 := bstep (se 1 (by rfl) ⟨540620, by rfl⟩ : syracuseStep 720827 = 1081241) B1081241
theorem B720887 : Blo 479788 720887 := bstep (se 1 (by rfl) ⟨540665, by rfl⟩ : syracuseStep 720887 = 1081331) B1081331
theorem B720905 : Blo 479788 720905 := bstep (se 2 (by rfl) ⟨270339, by rfl⟩ : syracuseStep 720905 = 540679) B540679
theorem B720935 : Blo 479788 720935 := bstep (se 1 (by rfl) ⟨540701, by rfl⟩ : syracuseStep 720935 = 1081403) B1081403
theorem B917561 : Blo 479788 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B721019 : Blo 479788 721019 := bstep (se 1 (by rfl) ⟨540764, by rfl⟩ : syracuseStep 721019 = 1081529) B1081529
theorem B721145 : Blo 479788 721145 := bstep (se 2 (by rfl) ⟨270429, by rfl⟩ : syracuseStep 721145 = 540859) B540859
theorem B721247 : Blo 479788 721247 := bstep (se 1 (by rfl) ⟨540935, by rfl⟩ : syracuseStep 721247 = 1081871) B1081871
theorem B721259 : Blo 479788 721259 := bstep (se 1 (by rfl) ⟨540944, by rfl⟩ : syracuseStep 721259 = 1081889) B1081889
theorem B721487 : Blo 479788 721487 := bstep (se 1 (by rfl) ⟨541115, by rfl⟩ : syracuseStep 721487 = 1082231) B1082231
theorem B1081979 : Blo 479788 1081979 := bstep (se 1 (by rfl) ⟨811484, by rfl⟩ : syracuseStep 1081979 = 1622969) B1622969
theorem B688763 : Blo 479788 688763 := bstep (se 1 (by rfl) ⟨516572, by rfl⟩ : syracuseStep 688763 = 1033145) B1033145
theorem B721607 : Blo 479788 721607 := bstep (se 1 (by rfl) ⟨541205, by rfl⟩ : syracuseStep 721607 = 1082411) B1082411
theorem B1835729 : Blo 479788 1835729 := bstep (se 2 (by rfl) ⟨688398, by rfl⟩ : syracuseStep 1835729 = 1376797) B1376797
theorem B1082105 : Blo 479788 1082105 := bstep (se 2 (by rfl) ⟨405789, by rfl⟩ : syracuseStep 1082105 = 811579) B811579
theorem B7537481 : Blo 479788 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B721769 : Blo 479788 721769 := bstep (se 2 (by rfl) ⟨270663, by rfl⟩ : syracuseStep 721769 = 541327) B541327
theorem B3474323 : Blo 479788 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B721847 : Blo 479788 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B721883 : Blo 479788 721883 := bstep (se 1 (by rfl) ⟨541412, by rfl⟩ : syracuseStep 721883 = 1082825) B1082825
theorem B1082375 : Blo 479788 1082375 := bstep (se 1 (by rfl) ⟨811781, by rfl⟩ : syracuseStep 1082375 = 1623563) B1623563
theorem B1377287 : Blo 479788 1377287 := bstep (se 1 (by rfl) ⟨1032965, by rfl⟩ : syracuseStep 1377287 = 2065931) B2065931
theorem B1836047 : Blo 479788 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B5473331 : Blo 479788 5473331 := bstep (se 1 (by rfl) ⟨4104998, by rfl⟩ : syracuseStep 5473331 = 8209997) B8209997
theorem B24052787 : Blo 479788 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B1082447 : Blo 479788 1082447 := bstep (se 1 (by rfl) ⟨811835, by rfl⟩ : syracuseStep 1082447 = 1623671) B1623671
theorem B2753615 : Blo 479788 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B3474551 : Blo 479788 3474551 := bstep (se 1 (by rfl) ⟨2605913, by rfl⟩ : syracuseStep 3474551 = 5211827) B5211827
theorem B3671243 : Blo 479788 3671243 := bstep (se 1 (by rfl) ⟨2753432, by rfl⟩ : syracuseStep 3671243 = 5506865) B5506865
theorem B1017193 : Blo 479788 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B722351 : Blo 479788 722351 := bstep (se 1 (by rfl) ⟨541763, by rfl⟩ : syracuseStep 722351 = 1083527) B1083527
theorem B1082843 : Blo 479788 1082843 := bstep (se 1 (by rfl) ⟨812132, by rfl⟩ : syracuseStep 1082843 = 1624265) B1624265
theorem B722441 : Blo 479788 722441 := bstep (se 2 (by rfl) ⟨270915, by rfl⟩ : syracuseStep 722441 = 541831) B541831
theorem B722471 : Blo 479788 722471 := bstep (se 1 (by rfl) ⟨541853, by rfl⟩ : syracuseStep 722471 = 1083707) B1083707
theorem B722555 : Blo 479788 722555 := bstep (se 1 (by rfl) ⟨541916, by rfl⟩ : syracuseStep 722555 = 1083833) B1083833
theorem B14419603 : Blo 479788 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B722681 : Blo 479788 722681 := bstep (se 2 (by rfl) ⟨271005, by rfl⟩ : syracuseStep 722681 = 542011) B542011
theorem B4622123 : Blo 479788 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B722783 : Blo 479788 722783 := bstep (se 1 (by rfl) ⟨542087, by rfl⟩ : syracuseStep 722783 = 1084175) B1084175
theorem B722795 : Blo 479788 722795 := bstep (se 1 (by rfl) ⟨542096, by rfl⟩ : syracuseStep 722795 = 1084193) B1084193
theorem B1083311 : Blo 479788 1083311 := bstep (se 1 (by rfl) ⟨812483, by rfl⟩ : syracuseStep 1083311 = 1624967) B1624967
theorem B723023 : Blo 479788 723023 := bstep (se 1 (by rfl) ⟨542267, by rfl⟩ : syracuseStep 723023 = 1084535) B1084535
theorem B1214635 : Blo 479788 1214635 := bstep (se 1 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 1214635 = 1821953) B1821953
theorem B1083563 : Blo 479788 1083563 := bstep (se 1 (by rfl) ⟨812672, by rfl⟩ : syracuseStep 1083563 = 1625345) B1625345
theorem B723143 : Blo 479788 723143 := bstep (se 1 (by rfl) ⟨542357, by rfl⟩ : syracuseStep 723143 = 1084715) B1084715
theorem B723305 : Blo 479788 723305 := bstep (se 2 (by rfl) ⟨271239, by rfl⟩ : syracuseStep 723305 = 542479) B542479
theorem B723383 : Blo 479788 723383 := bstep (se 1 (by rfl) ⟨542537, by rfl⟩ : syracuseStep 723383 = 1085075) B1085075
theorem B1214939 : Blo 479788 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B723419 : Blo 479788 723419 := bstep (se 1 (by rfl) ⟨542564, by rfl⟩ : syracuseStep 723419 = 1085129) B1085129
theorem B16714421 : Blo 479788 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1084103 : Blo 479788 1084103 := bstep (se 1 (by rfl) ⟨813077, by rfl⟩ : syracuseStep 1084103 = 1626155) B1626155
theorem B2919197 : Blo 479788 2919197 := bstep (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) B1094699
theorem B723887 : Blo 479788 723887 := bstep (se 1 (by rfl) ⟨542915, by rfl⟩ : syracuseStep 723887 = 1085831) B1085831
theorem B723977 : Blo 479788 723977 := bstep (se 2 (by rfl) ⟨271491, by rfl⟩ : syracuseStep 723977 = 542983) B542983
theorem B724007 : Blo 479788 724007 := bstep (se 1 (by rfl) ⟨543005, by rfl⟩ : syracuseStep 724007 = 1086011) B1086011
theorem B724091 : Blo 479788 724091 := bstep (se 1 (by rfl) ⟨543068, by rfl⟩ : syracuseStep 724091 = 1086137) B1086137
theorem B724217 : Blo 479788 724217 := bstep (se 2 (by rfl) ⟨271581, by rfl⟩ : syracuseStep 724217 = 543163) B543163
theorem B4132133 : Blo 479788 4132133 := bstep (se 4 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 4132133 = 774775) B774775
theorem B724319 : Blo 479788 724319 := bstep (se 1 (by rfl) ⟨543239, by rfl⟩ : syracuseStep 724319 = 1086479) B1086479
theorem B724331 : Blo 479788 724331 := bstep (se 1 (by rfl) ⟨543248, by rfl⟩ : syracuseStep 724331 = 1086497) B1086497
theorem B1740275 : Blo 479788 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B1084967 : Blo 479788 1084967 := bstep (se 1 (by rfl) ⟨813725, by rfl⟩ : syracuseStep 1084967 = 1627451) B1627451
theorem B724559 : Blo 479788 724559 := bstep (se 1 (by rfl) ⟨543419, by rfl⟩ : syracuseStep 724559 = 1086839) B1086839
theorem B724679 : Blo 479788 724679 := bstep (se 1 (by rfl) ⟨543509, by rfl⟩ : syracuseStep 724679 = 1087019) B1087019
theorem B4099805 : Blo 479788 4099805 := bstep (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) B1537427
theorem B11702083 : Blo 479788 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B724841 : Blo 479788 724841 := bstep (se 2 (by rfl) ⟨271815, by rfl⟩ : syracuseStep 724841 = 543631) B543631
theorem B1085291 : Blo 479788 1085291 := bstep (se 1 (by rfl) ⟨813968, by rfl⟩ : syracuseStep 1085291 = 1627937) B1627937
theorem B1314721 : Blo 479788 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B1216417 : Blo 479788 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B1085345 : Blo 479788 1085345 := bstep (se 2 (by rfl) ⟨407004, by rfl⟩ : syracuseStep 1085345 = 814009) B814009
theorem B724919 : Blo 479788 724919 := bstep (se 1 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 724919 = 1087379) B1087379
theorem B3477433 : Blo 479788 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B724955 : Blo 479788 724955 := bstep (se 1 (by rfl) ⟨543716, by rfl⟩ : syracuseStep 724955 = 1087433) B1087433
theorem B1085687 : Blo 479788 1085687 := bstep (se 1 (by rfl) ⟨814265, by rfl⟩ : syracuseStep 1085687 = 1628531) B1628531
theorem B725423 : Blo 479788 725423 := bstep (se 1 (by rfl) ⟨544067, by rfl⟩ : syracuseStep 725423 = 1088135) B1088135
theorem B725513 : Blo 479788 725513 := bstep (se 2 (by rfl) ⟨272067, by rfl⟩ : syracuseStep 725513 = 544135) B544135
theorem B725543 : Blo 479788 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B725627 : Blo 479788 725627 := bstep (se 1 (by rfl) ⟨544220, by rfl⟩ : syracuseStep 725627 = 1088441) B1088441
theorem B4100867 : Blo 479788 4100867 := bstep (se 1 (by rfl) ⟨3075650, by rfl⟩ : syracuseStep 4100867 = 6151301) B6151301
theorem B1086281 : Blo 479788 1086281 := bstep (se 2 (by rfl) ⟨407355, by rfl⟩ : syracuseStep 1086281 = 814711) B814711
theorem B1643527 : Blo 479788 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B988217 : Blo 479788 988217 := bstep (se 2 (by rfl) ⟨370581, by rfl⟩ : syracuseStep 988217 = 741163) B741163
theorem B1087073 : Blo 479788 1087073 := bstep (se 2 (by rfl) ⟨407652, by rfl⟩ : syracuseStep 1087073 = 815305) B815305
theorem B1546091 : Blo 479788 1546091 := bstep (se 1 (by rfl) ⟨1159568, by rfl⟩ : syracuseStep 1546091 = 2319137) B2319137
theorem B1087415 : Blo 479788 1087415 := bstep (se 1 (by rfl) ⟨815561, by rfl⟩ : syracuseStep 1087415 = 1631123) B1631123
theorem B2431133 : Blo 479788 2431133 := bstep (se 3 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 2431133 = 911675) B911675
theorem B1218959 : Blo 479788 1218959 := bstep (se 1 (by rfl) ⟨914219, by rfl⟩ : syracuseStep 1218959 = 1828439) B1828439
theorem B1088009 : Blo 479788 1088009 := bstep (se 2 (by rfl) ⟨408003, by rfl⟩ : syracuseStep 1088009 = 816007) B816007
theorem B1219283 : Blo 479788 1219283 := bstep (se 1 (by rfl) ⟨914462, by rfl⟩ : syracuseStep 1219283 = 1828925) B1828925
theorem B1088351 : Blo 479788 1088351 := bstep (se 1 (by rfl) ⟨816263, by rfl⟩ : syracuseStep 1088351 = 1632527) B1632527
theorem B2432429 : Blo 479788 2432429 := bstep (se 3 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 2432429 = 912161) B912161
theorem B1547873 : Blo 479788 1547873 := bstep (se 2 (by rfl) ⟨580452, by rfl⟩ : syracuseStep 1547873 = 1160905) B1160905
theorem B11280005 : Blo 479788 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B1220447 : Blo 479788 1220447 := bstep (se 1 (by rfl) ⟨915335, by rfl⟩ : syracuseStep 1220447 = 1830671) B1830671
theorem B827231 : Blo 479788 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B7840259 : Blo 479788 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B1221551 : Blo 479788 1221551 := bstep (se 1 (by rfl) ⟨916163, by rfl⟩ : syracuseStep 1221551 = 1832327) B1832327
theorem B2434049 : Blo 479788 2434049 := bstep (se 2 (by rfl) ⟨912768, by rfl⟩ : syracuseStep 2434049 = 1825537) B1825537
theorem B6661577 : Blo 479788 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B2434859 : Blo 479788 2434859 := bstep (se 1 (by rfl) ⟨1826144, by rfl⟩ : syracuseStep 2434859 = 3652289) B3652289
theorem B5220301 : Blo 479788 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B1222735 : Blo 479788 1222735 := bstep (se 1 (by rfl) ⟨917051, by rfl⟩ : syracuseStep 1222735 = 1834103) B1834103
theorem B1648811 : Blo 479788 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B1026523 : Blo 479788 1026523 := bstep (se 1 (by rfl) ⟨769892, by rfl⟩ : syracuseStep 1026523 = 1539785) B1539785
theorem B764615 : Blo 479788 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B1223383 : Blo 479788 1223383 := bstep (se 1 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 1223383 = 1835075) B1835075
theorem B3648401 : Blo 479788 3648401 := bstep (se 2 (by rfl) ⟨1368150, by rfl⟩ : syracuseStep 3648401 = 2736301) B2736301
theorem B1223687 : Blo 479788 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B3910949 : Blo 479788 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B1158905 : Blo 479788 1158905 := bstep (se 2 (by rfl) ⟨434589, by rfl⟩ : syracuseStep 1158905 = 869179) B869179
theorem B1028027 : Blo 479788 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B2437127 : Blo 479788 2437127 := bstep (se 1 (by rfl) ⟨1827845, by rfl⟩ : syracuseStep 2437127 = 3655691) B3655691
theorem B930143 : Blo 479788 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B2437613 : Blo 479788 2437613 := bstep (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) B914105
theorem B3944983 : Blo 479788 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B1389487 : Blo 479788 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B3650831 : Blo 479788 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B2438423 : Blo 479788 2438423 := bstep (se 1 (by rfl) ⟨1828817, by rfl⟩ : syracuseStep 2438423 = 3657635) B3657635
theorem B4634117 : Blo 479788 4634117 := bstep (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) B868897
theorem B20821697 : Blo 479788 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B9287459 : Blo 479788 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B3127099 : Blo 479788 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B1161067 : Blo 479788 1161067 := bstep (se 1 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 1161067 = 1741601) B1741601
theorem B1095611 : Blo 479788 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B3127385 : Blo 479788 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B1620215 : Blo 479788 1620215 := bstep (se 1 (by rfl) ⟨1215161, by rfl⟩ : syracuseStep 1620215 = 2430323) B2430323
theorem B10008937 : Blo 479788 10008937 := bstep (se 2 (by rfl) ⟨3753351, by rfl⟩ : syracuseStep 10008937 = 7506703) B7506703
theorem B1620539 : Blo 479788 1620539 := bstep (se 1 (by rfl) ⟨1215404, by rfl⟩ : syracuseStep 1620539 = 2430809) B2430809
theorem B1620809 : Blo 479788 1620809 := bstep (se 2 (by rfl) ⟨607803, by rfl⟩ : syracuseStep 1620809 = 1215607) B1215607
theorem B2440043 : Blo 479788 2440043 := bstep (se 1 (by rfl) ⟨1830032, by rfl⟩ : syracuseStep 2440043 = 3660065) B3660065
theorem B6241303 : Blo 479788 6241303 := bstep (se 1 (by rfl) ⟨4680977, by rfl⟩ : syracuseStep 6241303 = 9361955) B9361955
theorem B1162297 : Blo 479788 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B5946659 : Blo 479788 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B2440691 : Blo 479788 2440691 := bstep (se 1 (by rfl) ⟨1830518, by rfl⟩ : syracuseStep 2440691 = 3661037) B3661037
theorem B540283 : Blo 479788 540283 := bstep (se 1 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 540283 = 810425) B810425
theorem B4636349 : Blo 479788 4636349 := bstep (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) B1738631
theorem B1621943 : Blo 479788 1621943 := bstep (se 1 (by rfl) ⟨1216457, by rfl⟩ : syracuseStep 1621943 = 2432915) B2432915
theorem B540751 : Blo 479788 540751 := bstep (se 1 (by rfl) ⟨405563, by rfl⟩ : syracuseStep 540751 = 811127) B811127
theorem B3653747 : Blo 479788 3653747 := bstep (se 1 (by rfl) ⟨2740310, by rfl⟩ : syracuseStep 3653747 = 5480621) B5480621
theorem B541147 : Blo 479788 541147 := bstep (se 1 (by rfl) ⟨405860, by rfl⟩ : syracuseStep 541147 = 811721) B811721
theorem B1622537 : Blo 479788 1622537 := bstep (se 2 (by rfl) ⟨608451, by rfl⟩ : syracuseStep 1622537 = 1216903) B1216903
theorem B1032743 : Blo 479788 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B2441987 : Blo 479788 2441987 := bstep (se 1 (by rfl) ⟨1831490, by rfl⟩ : syracuseStep 2441987 = 3662981) B3662981
theorem B1983275 : Blo 479788 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B541615 : Blo 479788 541615 := bstep (se 1 (by rfl) ⟨406211, by rfl⟩ : syracuseStep 541615 = 812423) B812423
theorem B2605999 : Blo 479788 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B4113611 : Blo 479788 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B3097871 : Blo 479788 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B869705 : Blo 479788 869705 := bstep (se 2 (by rfl) ⟨326139, by rfl⟩ : syracuseStep 869705 = 652279) B652279
theorem B542047 : Blo 479788 542047 := bstep (se 1 (by rfl) ⟨406535, by rfl⟩ : syracuseStep 542047 = 813071) B813071
theorem B1623401 : Blo 479788 1623401 := bstep (se 2 (by rfl) ⟨608775, by rfl⟩ : syracuseStep 1623401 = 1217551) B1217551
theorem B3130919 : Blo 479788 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B542407 : Blo 479788 542407 := bstep (se 1 (by rfl) ⟨406805, by rfl⟩ : syracuseStep 542407 = 813611) B813611
theorem B3098411 : Blo 479788 3098411 := bstep (se 1 (by rfl) ⟨2323808, by rfl⟩ : syracuseStep 3098411 = 4647617) B4647617
theorem B2049887 : Blo 479788 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B870239 : Blo 479788 870239 := bstep (se 1 (by rfl) ⟨652679, by rfl⟩ : syracuseStep 870239 = 1305359) B1305359
theorem B27871127 : Blo 479788 27871127 := bstep (se 1 (by rfl) ⟨20903345, by rfl⟩ : syracuseStep 27871127 = 41806691) B41806691
theorem B1623995 : Blo 479788 1623995 := bstep (se 1 (by rfl) ⟨1217996, by rfl⟩ : syracuseStep 1623995 = 2435993) B2435993
theorem B4638809 : Blo 479788 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B2443607 : Blo 479788 2443607 := bstep (se 1 (by rfl) ⟨1832705, by rfl⟩ : syracuseStep 2443607 = 3665411) B3665411
theorem B936287 : Blo 479788 936287 := bstep (se 1 (by rfl) ⟨702215, by rfl⟩ : syracuseStep 936287 = 1404431) B1404431
theorem B36161977 : Blo 479788 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B543271 : Blo 479788 543271 := bstep (se 1 (by rfl) ⟨407453, by rfl⟩ : syracuseStep 543271 = 814907) B814907
theorem B60182003 : Blo 479788 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B1625723 : Blo 479788 1625723 := bstep (se 1 (by rfl) ⟨1219292, by rfl⟩ : syracuseStep 1625723 = 2438585) B2438585
theorem B1101523 : Blo 479788 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B1625885 : Blo 479788 1625885 := bstep (se 3 (by rfl) ⟨304853, by rfl⟩ : syracuseStep 1625885 = 609707) B609707
theorem B773993 : Blo 479788 773993 := bstep (se 2 (by rfl) ⟨290247, by rfl⟩ : syracuseStep 773993 = 580495) B580495
theorem B8376331 : Blo 479788 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B610735 : Blo 479788 610735 := bstep (se 1 (by rfl) ⟨458051, by rfl⟩ : syracuseStep 610735 = 916103) B916103
theorem B1626587 : Blo 479788 1626587 := bstep (se 1 (by rfl) ⟨1219940, by rfl⟩ : syracuseStep 1626587 = 2439881) B2439881
theorem B479823 : Blo 479788 479823 := bstep (se 1 (by rfl) ⟨359867, by rfl⟩ : syracuseStep 479823 = 719735) B719735
theorem B479839 : Blo 479788 479839 := bstep (se 1 (by rfl) ⟨359879, by rfl⟩ : syracuseStep 479839 = 719759) B719759
theorem B479867 : Blo 479788 479867 := bstep (se 1 (by rfl) ⟨359900, by rfl⟩ : syracuseStep 479867 = 719801) B719801
theorem B479919 : Blo 479788 479919 := bstep (se 1 (by rfl) ⟨359939, by rfl⟩ : syracuseStep 479919 = 719879) B719879
theorem B479943 : Blo 479788 479943 := bstep (se 1 (by rfl) ⟨359957, by rfl⟩ : syracuseStep 479943 = 719915) B719915
theorem B1233623 : Blo 479788 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B479963 : Blo 479788 479963 := bstep (se 1 (by rfl) ⟨359972, by rfl⟩ : syracuseStep 479963 = 719945) B719945
theorem B480039 : Blo 479788 480039 := bstep (se 1 (by rfl) ⟨360029, by rfl⟩ : syracuseStep 480039 = 720059) B720059
theorem B480079 : Blo 479788 480079 := bstep (se 1 (by rfl) ⟨360059, by rfl⟩ : syracuseStep 480079 = 720119) B720119
theorem B480095 : Blo 479788 480095 := bstep (se 1 (by rfl) ⟨360071, by rfl⟩ : syracuseStep 480095 = 720143) B720143
theorem B480123 : Blo 479788 480123 := bstep (se 1 (by rfl) ⟨360092, by rfl⟩ : syracuseStep 480123 = 720185) B720185
theorem B480175 : Blo 479788 480175 := bstep (se 1 (by rfl) ⟨360131, by rfl⟩ : syracuseStep 480175 = 720263) B720263
theorem B480199 : Blo 479788 480199 := bstep (se 1 (by rfl) ⟨360149, by rfl⟩ : syracuseStep 480199 = 720299) B720299
theorem B480219 : Blo 479788 480219 := bstep (se 1 (by rfl) ⟨360164, by rfl⟩ : syracuseStep 480219 = 720329) B720329
theorem B480295 : Blo 479788 480295 := bstep (se 1 (by rfl) ⟨360221, by rfl⟩ : syracuseStep 480295 = 720443) B720443
theorem B480335 : Blo 479788 480335 := bstep (se 1 (by rfl) ⟨360251, by rfl⟩ : syracuseStep 480335 = 720503) B720503
theorem B480351 : Blo 479788 480351 := bstep (se 1 (by rfl) ⟨360263, by rfl⟩ : syracuseStep 480351 = 720527) B720527
theorem B480379 : Blo 479788 480379 := bstep (se 1 (by rfl) ⟨360284, by rfl⟩ : syracuseStep 480379 = 720569) B720569
theorem B1823897 : Blo 479788 1823897 := bstep (se 2 (by rfl) ⟨683961, by rfl⟩ : syracuseStep 1823897 = 1367923) B1367923
theorem B1627289 : Blo 479788 1627289 := bstep (se 2 (by rfl) ⟨610233, by rfl⟩ : syracuseStep 1627289 = 1220467) B1220467
theorem B480431 : Blo 479788 480431 := bstep (se 1 (by rfl) ⟨360323, by rfl⟩ : syracuseStep 480431 = 720647) B720647
theorem B480455 : Blo 479788 480455 := bstep (se 1 (by rfl) ⟨360341, by rfl⟩ : syracuseStep 480455 = 720683) B720683
theorem B480475 : Blo 479788 480475 := bstep (se 1 (by rfl) ⟨360356, by rfl⟩ : syracuseStep 480475 = 720713) B720713
theorem B480551 : Blo 479788 480551 := bstep (se 1 (by rfl) ⟨360413, by rfl⟩ : syracuseStep 480551 = 720827) B720827
theorem B480591 : Blo 479788 480591 := bstep (se 1 (by rfl) ⟨360443, by rfl⟩ : syracuseStep 480591 = 720887) B720887
theorem B480607 : Blo 479788 480607 := bstep (se 1 (by rfl) ⟨360455, by rfl⟩ : syracuseStep 480607 = 720911) B720911
theorem B480635 : Blo 479788 480635 := bstep (se 1 (by rfl) ⟨360476, by rfl⟩ : syracuseStep 480635 = 720953) B720953
theorem B480687 : Blo 479788 480687 := bstep (se 1 (by rfl) ⟨360515, by rfl⟩ : syracuseStep 480687 = 721031) B721031
theorem B480711 : Blo 479788 480711 := bstep (se 1 (by rfl) ⟨360533, by rfl⟩ : syracuseStep 480711 = 721067) B721067
theorem B480731 : Blo 479788 480731 := bstep (se 1 (by rfl) ⟨360548, by rfl⟩ : syracuseStep 480731 = 721097) B721097
theorem B611803 : Blo 479788 611803 := bstep (se 1 (by rfl) ⟨458852, by rfl⟩ : syracuseStep 611803 = 917705) B917705
theorem B480807 : Blo 479788 480807 := bstep (se 1 (by rfl) ⟨360605, by rfl⟩ : syracuseStep 480807 = 721211) B721211
theorem B480847 : Blo 479788 480847 := bstep (se 1 (by rfl) ⟨360635, by rfl⟩ : syracuseStep 480847 = 721271) B721271
theorem B480863 : Blo 479788 480863 := bstep (se 1 (by rfl) ⟨360647, by rfl⟩ : syracuseStep 480863 = 721295) B721295
theorem B1824353 : Blo 479788 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B480891 : Blo 479788 480891 := bstep (se 1 (by rfl) ⟨360668, by rfl⟩ : syracuseStep 480891 = 721337) B721337
theorem B480943 : Blo 479788 480943 := bstep (se 1 (by rfl) ⟨360707, by rfl⟩ : syracuseStep 480943 = 721415) B721415
theorem B2315965 : Blo 479788 2315965 := bstep (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) B868487
theorem B480967 : Blo 479788 480967 := bstep (se 1 (by rfl) ⟨360725, by rfl⟩ : syracuseStep 480967 = 721451) B721451
theorem B480987 : Blo 479788 480987 := bstep (se 1 (by rfl) ⟨360740, by rfl⟩ : syracuseStep 480987 = 721481) B721481
theorem B481063 : Blo 479788 481063 := bstep (se 1 (by rfl) ⟨360797, by rfl⟩ : syracuseStep 481063 = 721595) B721595
theorem B3659579 : Blo 479788 3659579 := bstep (se 1 (by rfl) ⟨2744684, by rfl⟩ : syracuseStep 3659579 = 5489369) B5489369
theorem B2447171 : Blo 479788 2447171 := bstep (se 1 (by rfl) ⟨1835378, by rfl⟩ : syracuseStep 2447171 = 3670757) B3670757
theorem B481103 : Blo 479788 481103 := bstep (se 1 (by rfl) ⟨360827, by rfl⟩ : syracuseStep 481103 = 721655) B721655
theorem B481119 : Blo 479788 481119 := bstep (se 1 (by rfl) ⟨360839, by rfl⟩ : syracuseStep 481119 = 721679) B721679
theorem B481147 : Blo 479788 481147 := bstep (se 1 (by rfl) ⟨360860, by rfl⟩ : syracuseStep 481147 = 721721) B721721
theorem B481199 : Blo 479788 481199 := bstep (se 1 (by rfl) ⟨360899, by rfl⟩ : syracuseStep 481199 = 721799) B721799
theorem B481223 : Blo 479788 481223 := bstep (se 1 (by rfl) ⟨360917, by rfl⟩ : syracuseStep 481223 = 721835) B721835
theorem B481243 : Blo 479788 481243 := bstep (se 1 (by rfl) ⟨360932, by rfl⟩ : syracuseStep 481243 = 721865) B721865
theorem B972839 : Blo 479788 972839 := bstep (se 1 (by rfl) ⟨729629, by rfl⟩ : syracuseStep 972839 = 1459259) B1459259
theorem B481319 : Blo 479788 481319 := bstep (se 1 (by rfl) ⟨360989, by rfl⟩ : syracuseStep 481319 = 721979) B721979
theorem B6969401 : Blo 479788 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B481359 : Blo 479788 481359 := bstep (se 1 (by rfl) ⟨361019, by rfl⟩ : syracuseStep 481359 = 722039) B722039
theorem B481375 : Blo 479788 481375 := bstep (se 1 (by rfl) ⟨361031, by rfl⟩ : syracuseStep 481375 = 722063) B722063
theorem B481403 : Blo 479788 481403 := bstep (se 1 (by rfl) ⟨361052, by rfl⟩ : syracuseStep 481403 = 722105) B722105
theorem B481455 : Blo 479788 481455 := bstep (se 1 (by rfl) ⟨361091, by rfl⟩ : syracuseStep 481455 = 722183) B722183
theorem B481479 : Blo 479788 481479 := bstep (se 1 (by rfl) ⟨361109, by rfl⟩ : syracuseStep 481479 = 722219) B722219
theorem B481499 : Blo 479788 481499 := bstep (se 1 (by rfl) ⟨361124, by rfl⟩ : syracuseStep 481499 = 722249) B722249
theorem B481575 : Blo 479788 481575 := bstep (se 1 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 481575 = 722363) B722363
theorem B1628477 : Blo 479788 1628477 := bstep (se 3 (by rfl) ⟨305339, by rfl⟩ : syracuseStep 1628477 = 610679) B610679
theorem B481615 : Blo 479788 481615 := bstep (se 1 (by rfl) ⟨361211, by rfl⟩ : syracuseStep 481615 = 722423) B722423
theorem B481631 : Blo 479788 481631 := bstep (se 1 (by rfl) ⟨361223, by rfl⟩ : syracuseStep 481631 = 722447) B722447
theorem B481659 : Blo 479788 481659 := bstep (se 1 (by rfl) ⟨361244, by rfl⟩ : syracuseStep 481659 = 722489) B722489
theorem B1956221 : Blo 479788 1956221 := bstep (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) B733583
theorem B481711 : Blo 479788 481711 := bstep (se 1 (by rfl) ⟨361283, by rfl⟩ : syracuseStep 481711 = 722567) B722567
theorem B481735 : Blo 479788 481735 := bstep (se 1 (by rfl) ⟨361301, by rfl⟩ : syracuseStep 481735 = 722603) B722603
theorem B481755 : Blo 479788 481755 := bstep (se 1 (by rfl) ⟨361316, by rfl⟩ : syracuseStep 481755 = 722633) B722633
theorem B481831 : Blo 479788 481831 := bstep (se 1 (by rfl) ⟨361373, by rfl⟩ : syracuseStep 481831 = 722747) B722747
theorem B481871 : Blo 479788 481871 := bstep (se 1 (by rfl) ⟨361403, by rfl⟩ : syracuseStep 481871 = 722807) B722807
theorem B481887 : Blo 479788 481887 := bstep (se 1 (by rfl) ⟨361415, by rfl⟩ : syracuseStep 481887 = 722831) B722831
theorem B1366625 : Blo 479788 1366625 := bstep (se 2 (by rfl) ⟨512484, by rfl⟩ : syracuseStep 1366625 = 1024969) B1024969
theorem B481915 : Blo 479788 481915 := bstep (se 1 (by rfl) ⟨361436, by rfl⟩ : syracuseStep 481915 = 722873) B722873
theorem B481967 : Blo 479788 481967 := bstep (se 1 (by rfl) ⟨361475, by rfl⟩ : syracuseStep 481967 = 722951) B722951
theorem B481991 : Blo 479788 481991 := bstep (se 1 (by rfl) ⟨361493, by rfl⟩ : syracuseStep 481991 = 722987) B722987
theorem B1366739 : Blo 479788 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B482011 : Blo 479788 482011 := bstep (se 1 (by rfl) ⟨361508, by rfl⟩ : syracuseStep 482011 = 723017) B723017
theorem B482087 : Blo 479788 482087 := bstep (se 1 (by rfl) ⟨361565, by rfl⟩ : syracuseStep 482087 = 723131) B723131
theorem B482127 : Blo 479788 482127 := bstep (se 1 (by rfl) ⟨361595, by rfl⟩ : syracuseStep 482127 = 723191) B723191
theorem B482143 : Blo 479788 482143 := bstep (se 1 (by rfl) ⟨361607, by rfl⟩ : syracuseStep 482143 = 723215) B723215
theorem B482171 : Blo 479788 482171 := bstep (se 1 (by rfl) ⟨361628, by rfl⟩ : syracuseStep 482171 = 723257) B723257
theorem B482223 : Blo 479788 482223 := bstep (se 1 (by rfl) ⟨361667, by rfl⟩ : syracuseStep 482223 = 723335) B723335
theorem B482247 : Blo 479788 482247 := bstep (se 1 (by rfl) ⟨361685, by rfl⟩ : syracuseStep 482247 = 723371) B723371
theorem B482267 : Blo 479788 482267 := bstep (se 1 (by rfl) ⟨361700, by rfl⟩ : syracuseStep 482267 = 723401) B723401
theorem B515035 : Blo 479788 515035 := bstep (se 1 (by rfl) ⟨386276, by rfl⟩ : syracuseStep 515035 = 772553) B772553
theorem B809993 : Blo 479788 809993 := bstep (se 2 (by rfl) ⟨303747, by rfl⟩ : syracuseStep 809993 = 607495) B607495
theorem B1825811 : Blo 479788 1825811 := bstep (se 1 (by rfl) ⟨1369358, by rfl⟩ : syracuseStep 1825811 = 2738717) B2738717
theorem B482343 : Blo 479788 482343 := bstep (se 1 (by rfl) ⟨361757, by rfl⟩ : syracuseStep 482343 = 723515) B723515
theorem B482383 : Blo 479788 482383 := bstep (se 1 (by rfl) ⟨361787, by rfl⟩ : syracuseStep 482383 = 723575) B723575
theorem B482399 : Blo 479788 482399 := bstep (se 1 (by rfl) ⟨361799, by rfl⟩ : syracuseStep 482399 = 723599) B723599
theorem B482427 : Blo 479788 482427 := bstep (se 1 (by rfl) ⟨361820, by rfl⟩ : syracuseStep 482427 = 723641) B723641
theorem B3464345 : Blo 479788 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B1629341 : Blo 479788 1629341 := bstep (se 3 (by rfl) ⟨305501, by rfl⟩ : syracuseStep 1629341 = 611003) B611003
theorem B810155 : Blo 479788 810155 := bstep (se 1 (by rfl) ⟨607616, by rfl⟩ : syracuseStep 810155 = 1215233) B1215233
theorem B482479 : Blo 479788 482479 := bstep (se 1 (by rfl) ⟨361859, by rfl⟩ : syracuseStep 482479 = 723719) B723719
theorem B482503 : Blo 479788 482503 := bstep (se 1 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 482503 = 723755) B723755
theorem B482523 : Blo 479788 482523 := bstep (se 1 (by rfl) ⟨361892, by rfl⟩ : syracuseStep 482523 = 723785) B723785
theorem B482599 : Blo 479788 482599 := bstep (se 1 (by rfl) ⟨361949, by rfl⟩ : syracuseStep 482599 = 723899) B723899
theorem B482639 : Blo 479788 482639 := bstep (se 1 (by rfl) ⟨361979, by rfl⟩ : syracuseStep 482639 = 723959) B723959
theorem B482655 : Blo 479788 482655 := bstep (se 1 (by rfl) ⟨361991, by rfl⟩ : syracuseStep 482655 = 723983) B723983
theorem B1957225 : Blo 479788 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B482683 : Blo 479788 482683 := bstep (se 1 (by rfl) ⟨362012, by rfl⟩ : syracuseStep 482683 = 724025) B724025
theorem B1858945 : Blo 479788 1858945 := bstep (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) B1394209
theorem B482735 : Blo 479788 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B482759 : Blo 479788 482759 := bstep (se 1 (by rfl) ⟨362069, by rfl⟩ : syracuseStep 482759 = 724139) B724139
theorem B482779 : Blo 479788 482779 := bstep (se 1 (by rfl) ⟨362084, by rfl⟩ : syracuseStep 482779 = 724169) B724169
theorem B482855 : Blo 479788 482855 := bstep (se 1 (by rfl) ⟨362141, by rfl⟩ : syracuseStep 482855 = 724283) B724283
theorem B810553 : Blo 479788 810553 := bstep (se 2 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 810553 = 607915) B607915
theorem B482895 : Blo 479788 482895 := bstep (se 1 (by rfl) ⟨362171, by rfl⟩ : syracuseStep 482895 = 724343) B724343
theorem B482911 : Blo 479788 482911 := bstep (se 1 (by rfl) ⟨362183, by rfl⟩ : syracuseStep 482911 = 724367) B724367
theorem B482939 : Blo 479788 482939 := bstep (se 1 (by rfl) ⟨362204, by rfl⟩ : syracuseStep 482939 = 724409) B724409
theorem B482991 : Blo 479788 482991 := bstep (se 1 (by rfl) ⟨362243, by rfl⟩ : syracuseStep 482991 = 724487) B724487
theorem B1629881 : Blo 479788 1629881 := bstep (se 2 (by rfl) ⟨611205, by rfl⟩ : syracuseStep 1629881 = 1222411) B1222411
theorem B1367741 : Blo 479788 1367741 := bstep (se 3 (by rfl) ⟨256451, by rfl⟩ : syracuseStep 1367741 = 512903) B512903
theorem B810695 : Blo 479788 810695 := bstep (se 1 (by rfl) ⟨608021, by rfl⟩ : syracuseStep 810695 = 1216043) B1216043
theorem B483015 : Blo 479788 483015 := bstep (se 1 (by rfl) ⟨362261, by rfl⟩ : syracuseStep 483015 = 724523) B724523
theorem B483035 : Blo 479788 483035 := bstep (se 1 (by rfl) ⟨362276, by rfl⟩ : syracuseStep 483035 = 724553) B724553
theorem B1302265 : Blo 479788 1302265 := bstep (se 2 (by rfl) ⟨488349, by rfl⟩ : syracuseStep 1302265 = 976699) B976699
theorem B483111 : Blo 479788 483111 := bstep (se 1 (by rfl) ⟨362333, by rfl⟩ : syracuseStep 483111 = 724667) B724667
theorem B483151 : Blo 479788 483151 := bstep (se 1 (by rfl) ⟨362363, by rfl⟩ : syracuseStep 483151 = 724727) B724727
theorem B483167 : Blo 479788 483167 := bstep (se 1 (by rfl) ⟨362375, by rfl⟩ : syracuseStep 483167 = 724751) B724751
theorem B810857 : Blo 479788 810857 := bstep (se 2 (by rfl) ⟨304071, by rfl⟩ : syracuseStep 810857 = 608143) B608143
theorem B483195 : Blo 479788 483195 := bstep (se 1 (by rfl) ⟨362396, by rfl⟩ : syracuseStep 483195 = 724793) B724793
theorem B483247 : Blo 479788 483247 := bstep (se 1 (by rfl) ⟨362435, by rfl⟩ : syracuseStep 483247 = 724871) B724871
theorem B483271 : Blo 479788 483271 := bstep (se 1 (by rfl) ⟨362453, by rfl⟩ : syracuseStep 483271 = 724907) B724907
theorem B483291 : Blo 479788 483291 := bstep (se 1 (by rfl) ⟨362468, by rfl⟩ : syracuseStep 483291 = 724937) B724937
theorem B1368083 : Blo 479788 1368083 := bstep (se 1 (by rfl) ⟨1026062, by rfl⟩ : syracuseStep 1368083 = 2052125) B2052125
theorem B483367 : Blo 479788 483367 := bstep (se 1 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 483367 = 725051) B725051
theorem B483407 : Blo 479788 483407 := bstep (se 1 (by rfl) ⟨362555, by rfl⟩ : syracuseStep 483407 = 725111) B725111
theorem B6152273 : Blo 479788 6152273 := bstep (se 2 (by rfl) ⟨2307102, by rfl⟩ : syracuseStep 6152273 = 4614205) B4614205
theorem B483423 : Blo 479788 483423 := bstep (se 1 (by rfl) ⟨362567, by rfl⟩ : syracuseStep 483423 = 725135) B725135
theorem B483451 : Blo 479788 483451 := bstep (se 1 (by rfl) ⟨362588, by rfl⟩ : syracuseStep 483451 = 725177) B725177
theorem B483503 : Blo 479788 483503 := bstep (se 1 (by rfl) ⟨362627, by rfl⟩ : syracuseStep 483503 = 725255) B725255
theorem B483527 : Blo 479788 483527 := bstep (se 1 (by rfl) ⟨362645, by rfl⟩ : syracuseStep 483527 = 725291) B725291
theorem B483547 : Blo 479788 483547 := bstep (se 1 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 483547 = 725321) B725321
theorem B811255 : Blo 479788 811255 := bstep (se 1 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 811255 = 1216883) B1216883
theorem B1630475 : Blo 479788 1630475 := bstep (se 1 (by rfl) ⟨1222856, by rfl⟩ : syracuseStep 1630475 = 2445713) B2445713
theorem B483623 : Blo 479788 483623 := bstep (se 1 (by rfl) ⟨362717, by rfl⟩ : syracuseStep 483623 = 725435) B725435
theorem B483663 : Blo 479788 483663 := bstep (se 1 (by rfl) ⟨362747, by rfl⟩ : syracuseStep 483663 = 725495) B725495
theorem B483679 : Blo 479788 483679 := bstep (se 1 (by rfl) ⟨362759, by rfl⟩ : syracuseStep 483679 = 725519) B725519
theorem B1958249 : Blo 479788 1958249 := bstep (se 2 (by rfl) ⟨734343, by rfl⟩ : syracuseStep 1958249 = 1468687) B1468687
theorem B483707 : Blo 479788 483707 := bstep (se 1 (by rfl) ⟨362780, by rfl⟩ : syracuseStep 483707 = 725561) B725561
theorem B483759 : Blo 479788 483759 := bstep (se 1 (by rfl) ⟨362819, by rfl⟩ : syracuseStep 483759 = 725639) B725639
theorem B811451 : Blo 479788 811451 := bstep (se 1 (by rfl) ⟨608588, by rfl⟩ : syracuseStep 811451 = 1217177) B1217177
theorem B483783 : Blo 479788 483783 := bstep (se 1 (by rfl) ⟨362837, by rfl⟩ : syracuseStep 483783 = 725675) B725675
theorem B1368539 : Blo 479788 1368539 := bstep (se 1 (by rfl) ⟨1026404, by rfl⟩ : syracuseStep 1368539 = 2052809) B2052809
theorem B1630745 : Blo 479788 1630745 := bstep (se 2 (by rfl) ⟨611529, by rfl⟩ : syracuseStep 1630745 = 1223059) B1223059
theorem B811559 : Blo 479788 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B3465787 : Blo 479788 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B1827467 : Blo 479788 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B811849 : Blo 479788 811849 := bstep (se 2 (by rfl) ⟨304443, by rfl⟩ : syracuseStep 811849 = 608887) B608887
theorem B811883 : Blo 479788 811883 := bstep (se 1 (by rfl) ⟨608912, by rfl⟩ : syracuseStep 811883 = 1217825) B1217825
theorem B812281 : Blo 479788 812281 := bstep (se 2 (by rfl) ⟨304605, by rfl⟩ : syracuseStep 812281 = 609211) B609211
theorem B910855 : Blo 479788 910855 := bstep (se 1 (by rfl) ⟨683141, by rfl⟩ : syracuseStep 910855 = 1366283) B1366283
theorem B812551 : Blo 479788 812551 := bstep (se 1 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 812551 = 1218827) B1218827
theorem B1369723 : Blo 479788 1369723 := bstep (se 1 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 1369723 = 2054585) B2054585
theorem B3303035 : Blo 479788 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B1631879 : Blo 479788 1631879 := bstep (se 1 (by rfl) ⟨1223909, by rfl⟩ : syracuseStep 1631879 = 2447819) B2447819
theorem B4449937 : Blo 479788 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B1631933 : Blo 479788 1631933 := bstep (se 3 (by rfl) ⟨305987, by rfl⟩ : syracuseStep 1631933 = 611975) B611975
theorem B1468115 : Blo 479788 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B1632095 : Blo 479788 1632095 := bstep (se 1 (by rfl) ⟨1224071, by rfl⟩ : syracuseStep 1632095 = 2448143) B2448143
theorem B1730413 : Blo 479788 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B1828727 : Blo 479788 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B2320289 : Blo 479788 2320289 := bstep (se 2 (by rfl) ⟨870108, by rfl⟩ : syracuseStep 2320289 = 1740217) B1740217
theorem B812983 : Blo 479788 812983 := bstep (se 1 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 812983 = 1219475) B1219475
theorem B3958721 : Blo 479788 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1632257 : Blo 479788 1632257 := bstep (se 2 (by rfl) ⟨612096, by rfl⟩ : syracuseStep 1632257 = 1224193) B1224193
theorem B3663953 : Blo 479788 3663953 := bstep (se 2 (by rfl) ⟨1373982, by rfl⟩ : syracuseStep 3663953 = 2747965) B2747965
theorem B813179 : Blo 479788 813179 := bstep (se 1 (by rfl) ⟨609884, by rfl⟩ : syracuseStep 813179 = 1219769) B1219769
theorem B12347801 : Blo 479788 12347801 := bstep (se 2 (by rfl) ⟨4630425, by rfl⟩ : syracuseStep 12347801 = 9260851) B9260851
theorem B1370611 : Blo 479788 1370611 := bstep (se 1 (by rfl) ⟨1027958, by rfl⟩ : syracuseStep 1370611 = 2055917) B2055917
theorem B813577 : Blo 479788 813577 := bstep (se 2 (by rfl) ⟨305091, by rfl⟩ : syracuseStep 813577 = 610183) B610183
theorem B911911 : Blo 479788 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B813739 : Blo 479788 813739 := bstep (se 1 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 813739 = 1220609) B1220609
theorem B1370839 : Blo 479788 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B3468035 : Blo 479788 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B1829699 : Blo 479788 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B814043 : Blo 479788 814043 := bstep (se 1 (by rfl) ⟨610532, by rfl⟩ : syracuseStep 814043 = 1221065) B1221065
theorem B814279 : Blo 479788 814279 := bstep (se 1 (by rfl) ⟨610709, by rfl⟩ : syracuseStep 814279 = 1221419) B1221419
theorem B814441 : Blo 479788 814441 := bstep (se 2 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 814441 = 610831) B610831
theorem B650603 : Blo 479788 650603 := bstep (se 1 (by rfl) ⟨487952, by rfl⟩ : syracuseStep 650603 = 975905) B975905
theorem B22310261 : Blo 479788 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B683483 : Blo 479788 683483 := bstep (se 1 (by rfl) ⟨512612, by rfl⟩ : syracuseStep 683483 = 1025225) B1025225
theorem B1469915 : Blo 479788 1469915 := bstep (se 1 (by rfl) ⟨1102436, by rfl⟩ : syracuseStep 1469915 = 2204873) B2204873
theorem B1044065 : Blo 479788 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B6188663 : Blo 479788 6188663 := bstep (se 1 (by rfl) ⟨4641497, by rfl⟩ : syracuseStep 6188663 = 9282995) B9282995
theorem B815035 : Blo 479788 815035 := bstep (se 1 (by rfl) ⟨611276, by rfl⟩ : syracuseStep 815035 = 1222553) B1222553
theorem B815143 : Blo 479788 815143 := bstep (se 1 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 815143 = 1222715) B1222715
theorem B913619 : Blo 479788 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B2322749 : Blo 479788 2322749 := bstep (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) B871031
theorem B913771 : Blo 479788 913771 := bstep (se 1 (by rfl) ⟨685328, by rfl⟩ : syracuseStep 913771 = 1370657) B1370657
theorem B815467 : Blo 479788 815467 := bstep (se 1 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 815467 = 1223201) B1223201
theorem B684463 : Blo 479788 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B1831369 : Blo 479788 1831369 := bstep (se 2 (by rfl) ⟨686763, by rfl⟩ : syracuseStep 1831369 = 1373527) B1373527
theorem B2781677 : Blo 479788 2781677 := bstep (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) B1043129
theorem B4452889 : Blo 479788 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B1372697 : Blo 479788 1372697 := bstep (se 2 (by rfl) ⟨514761, by rfl⟩ : syracuseStep 1372697 = 1029523) B1029523
theorem B913999 : Blo 479788 913999 := bstep (se 1 (by rfl) ⟨685499, by rfl⟩ : syracuseStep 913999 = 1370999) B1370999
theorem B1831673 : Blo 479788 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B1733471 : Blo 479788 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B1831841 : Blo 479788 1831841 := bstep (se 2 (by rfl) ⟨686940, by rfl⟩ : syracuseStep 1831841 = 1373881) B1373881
theorem B1831855 : Blo 479788 1831855 := bstep (se 1 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 1831855 = 2747783) B2747783
theorem B3306539 : Blo 479788 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B685135 : Blo 479788 685135 := bstep (se 1 (by rfl) ⟨513851, by rfl⟩ : syracuseStep 685135 = 1027703) B1027703
theorem B3077291 : Blo 479788 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B3077315 : Blo 479788 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B685255 : Blo 479788 685255 := bstep (se 1 (by rfl) ⟨513941, by rfl⟩ : syracuseStep 685255 = 1027883) B1027883
theorem B3077777 : Blo 479788 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B5863211 : Blo 479788 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B1832813 : Blo 479788 1832813 := bstep (se 3 (by rfl) ⟨343652, by rfl⟩ : syracuseStep 1832813 = 687305) B687305
theorem B1537967 : Blo 479788 1537967 := bstep (se 1 (by rfl) ⟨1153475, by rfl⟩ : syracuseStep 1537967 = 2306951) B2306951
theorem B6944717 : Blo 479788 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B3471437 : Blo 479788 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B4618397 : Blo 479788 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B1833131 : Blo 479788 1833131 := bstep (se 1 (by rfl) ⟨1374848, by rfl⟩ : syracuseStep 1833131 = 2749697) B2749697
theorem B2324747 : Blo 479788 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B1079657 : Blo 479788 1079657 := bstep (se 2 (by rfl) ⟨404871, by rfl⟩ : syracuseStep 1079657 = 809743) B809743
theorem B3668813 : Blo 479788 3668813 := bstep (se 3 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 3668813 = 1375805) B1375805
theorem B719711 : Blo 479788 719711 := bstep (se 1 (by rfl) ⟨539783, by rfl⟩ : syracuseStep 719711 = 1079567) B1079567
theorem B719723 : Blo 479788 719723 := bstep (se 1 (by rfl) ⟨539792, by rfl⟩ : syracuseStep 719723 = 1079585) B1079585
theorem B2751407 : Blo 479788 2751407 := bstep (se 1 (by rfl) ⟨2063555, by rfl⟩ : syracuseStep 2751407 = 4127111) B4127111
theorem B1080251 : Blo 479788 1080251 := bstep (se 1 (by rfl) ⟨810188, by rfl⟩ : syracuseStep 1080251 = 1620377) B1620377
theorem B1080377 : Blo 479788 1080377 := bstep (se 2 (by rfl) ⟨405141, by rfl⟩ : syracuseStep 1080377 = 810283) B810283
theorem B719951 : Blo 479788 719951 := bstep (se 1 (by rfl) ⟨539963, by rfl⟩ : syracuseStep 719951 = 1079927) B1079927
theorem B720071 : Blo 479788 720071 := bstep (se 1 (by rfl) ⟨540053, by rfl⟩ : syracuseStep 720071 = 1080107) B1080107
theorem B1015031 : Blo 479788 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B720233 : Blo 479788 720233 := bstep (se 2 (by rfl) ⟨270087, by rfl⟩ : syracuseStep 720233 = 540175) B540175
theorem B1375613 : Blo 479788 1375613 := bstep (se 3 (by rfl) ⟨257927, by rfl⟩ : syracuseStep 1375613 = 515855) B515855
theorem B1080719 : Blo 479788 1080719 := bstep (se 1 (by rfl) ⟨810539, by rfl⟩ : syracuseStep 1080719 = 1621079) B1621079
theorem B4619663 : Blo 479788 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B720311 : Blo 479788 720311 := bstep (se 1 (by rfl) ⟨540233, by rfl⟩ : syracuseStep 720311 = 1080467) B1080467
theorem B720347 : Blo 479788 720347 := bstep (se 1 (by rfl) ⟨540260, by rfl⟩ : syracuseStep 720347 = 1080521) B1080521
theorem B6159959 : Blo 479788 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B1081043 : Blo 479788 1081043 := bstep (se 1 (by rfl) ⟨810782, by rfl⟩ : syracuseStep 1081043 = 1621565) B1621565
theorem B2195309 : Blo 479788 2195309 := bstep (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) B823241
theorem B720815 : Blo 479788 720815 := bstep (se 1 (by rfl) ⟨540611, by rfl⟩ : syracuseStep 720815 = 1081223) B1081223
theorem B721001 : Blo 479788 721001 := bstep (se 2 (by rfl) ⟨270375, by rfl⟩ : syracuseStep 721001 = 540751) B540751
theorem B1081673 : Blo 479788 1081673 := bstep (se 2 (by rfl) ⟨405627, by rfl⟩ : syracuseStep 1081673 = 811255) B811255
theorem B1081691 : Blo 479788 1081691 := bstep (se 1 (by rfl) ⟨811268, by rfl⟩ : syracuseStep 1081691 = 1622537) B1622537
theorem B688495 : Blo 479788 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B721319 : Blo 479788 721319 := bstep (se 1 (by rfl) ⟨540989, by rfl⟩ : syracuseStep 721319 = 1081979) B1081979
theorem B721403 : Blo 479788 721403 := bstep (se 1 (by rfl) ⟨541052, by rfl⟩ : syracuseStep 721403 = 1082105) B1082105
theorem B721529 : Blo 479788 721529 := bstep (se 2 (by rfl) ⟨270573, by rfl⟩ : syracuseStep 721529 = 541147) B541147
theorem B721583 : Blo 479788 721583 := bstep (se 1 (by rfl) ⟨541187, by rfl⟩ : syracuseStep 721583 = 1082375) B1082375
theorem B918191 : Blo 479788 918191 := bstep (se 1 (by rfl) ⟨688643, by rfl⟩ : syracuseStep 918191 = 1377287) B1377287
theorem B721631 : Blo 479788 721631 := bstep (se 1 (by rfl) ⟨541223, by rfl⟩ : syracuseStep 721631 = 1082447) B1082447
theorem B1835743 : Blo 479788 1835743 := bstep (se 1 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 1835743 = 2753615) B2753615
theorem B4621049 : Blo 479788 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B2065247 : Blo 479788 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1082267 : Blo 479788 1082267 := bstep (se 1 (by rfl) ⟨811700, by rfl⟩ : syracuseStep 1082267 = 1623401) B1623401
theorem B721895 : Blo 479788 721895 := bstep (se 1 (by rfl) ⟨541421, by rfl⟩ : syracuseStep 721895 = 1082843) B1082843
theorem B1082465 : Blo 479788 1082465 := bstep (se 2 (by rfl) ⟨405924, by rfl⟩ : syracuseStep 1082465 = 811849) B811849
theorem B3081415 : Blo 479788 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B2065607 : Blo 479788 2065607 := bstep (se 1 (by rfl) ⟨1549205, by rfl⟩ : syracuseStep 2065607 = 3098411) B3098411
theorem B722153 : Blo 479788 722153 := bstep (se 2 (by rfl) ⟨270807, by rfl⟩ : syracuseStep 722153 = 541615) B541615
theorem B3474665 : Blo 479788 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B18580751 : Blo 479788 18580751 := bstep (se 1 (by rfl) ⟨13935563, by rfl⟩ : syracuseStep 18580751 = 27871127) B27871127
theorem B722207 : Blo 479788 722207 := bstep (se 1 (by rfl) ⟨541655, by rfl⟩ : syracuseStep 722207 = 1083311) B1083311
theorem B1082663 : Blo 479788 1082663 := bstep (se 1 (by rfl) ⟨811997, by rfl⟩ : syracuseStep 1082663 = 1623995) B1623995
theorem B722375 : Blo 479788 722375 := bstep (se 1 (by rfl) ⟨541781, by rfl⟩ : syracuseStep 722375 = 1083563) B1083563
theorem B624191 : Blo 479788 624191 := bstep (se 1 (by rfl) ⟨468143, by rfl⟩ : syracuseStep 624191 = 936287) B936287
theorem B1836701 : Blo 479788 1836701 := bstep (se 3 (by rfl) ⟨344381, by rfl⟩ : syracuseStep 1836701 = 688763) B688763
theorem B1083041 : Blo 479788 1083041 := bstep (se 2 (by rfl) ⟨406140, by rfl⟩ : syracuseStep 1083041 = 812281) B812281
theorem B11142947 : Blo 479788 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B722729 : Blo 479788 722729 := bstep (se 2 (by rfl) ⟨271023, by rfl⟩ : syracuseStep 722729 = 542047) B542047
theorem B722735 : Blo 479788 722735 := bstep (se 1 (by rfl) ⟨542051, by rfl⟩ : syracuseStep 722735 = 1084103) B1084103
theorem B1214473 : Blo 479788 1214473 := bstep (se 2 (by rfl) ⟨455427, by rfl⟩ : syracuseStep 1214473 = 910855) B910855
theorem B1083401 : Blo 479788 1083401 := bstep (se 2 (by rfl) ⟨406275, by rfl⟩ : syracuseStep 1083401 = 812551) B812551
theorem B5933249 : Blo 479788 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B2754755 : Blo 479788 2754755 := bstep (se 1 (by rfl) ⟨2066066, by rfl⟩ : syracuseStep 2754755 = 4132133) B4132133
theorem B723209 : Blo 479788 723209 := bstep (se 2 (by rfl) ⟨271203, by rfl⟩ : syracuseStep 723209 = 542407) B542407
theorem B723311 : Blo 479788 723311 := bstep (se 1 (by rfl) ⟨542483, by rfl⟩ : syracuseStep 723311 = 1084967) B1084967
theorem B1083815 : Blo 479788 1083815 := bstep (se 1 (by rfl) ⟨812861, by rfl⟩ : syracuseStep 1083815 = 1625723) B1625723
theorem B5474789 : Blo 479788 5474789 := bstep (se 4 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 5474789 = 1026523) B1026523
theorem B1083923 : Blo 479788 1083923 := bstep (se 1 (by rfl) ⟨812942, by rfl⟩ : syracuseStep 1083923 = 1625885) B1625885
theorem B723527 : Blo 479788 723527 := bstep (se 1 (by rfl) ⟨542645, by rfl⟩ : syracuseStep 723527 = 1085291) B1085291
theorem B1083977 : Blo 479788 1083977 := bstep (se 2 (by rfl) ⟨406491, by rfl⟩ : syracuseStep 1083977 = 812983) B812983
theorem B723563 : Blo 479788 723563 := bstep (se 1 (by rfl) ⟨542672, by rfl⟩ : syracuseStep 723563 = 1085345) B1085345
theorem B8817437 : Blo 479788 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B723791 : Blo 479788 723791 := bstep (se 1 (by rfl) ⟨542843, by rfl⟩ : syracuseStep 723791 = 1085687) B1085687
theorem B1084391 : Blo 479788 1084391 := bstep (se 1 (by rfl) ⟨813293, by rfl⟩ : syracuseStep 1084391 = 1626587) B1626587
theorem B822415 : Blo 479788 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B724187 : Blo 479788 724187 := bstep (se 1 (by rfl) ⟨543140, by rfl⟩ : syracuseStep 724187 = 1086281) B1086281
theorem B1084769 : Blo 479788 1084769 := bstep (se 2 (by rfl) ⟨406788, by rfl⟩ : syracuseStep 1084769 = 813577) B813577
theorem B658811 : Blo 479788 658811 := bstep (se 1 (by rfl) ⟨494108, by rfl⟩ : syracuseStep 658811 = 988217) B988217
theorem B1215881 : Blo 479788 1215881 := bstep (se 2 (by rfl) ⟨455955, by rfl⟩ : syracuseStep 1215881 = 911911) B911911
theorem B724361 : Blo 479788 724361 := bstep (se 2 (by rfl) ⟨271635, by rfl⟩ : syracuseStep 724361 = 543271) B543271
theorem B1215931 : Blo 479788 1215931 := bstep (se 1 (by rfl) ⟨911948, by rfl⟩ : syracuseStep 1215931 = 1823897) B1823897
theorem B1084859 : Blo 479788 1084859 := bstep (se 1 (by rfl) ⟨813644, by rfl⟩ : syracuseStep 1084859 = 1627289) B1627289
theorem B1084985 : Blo 479788 1084985 := bstep (se 2 (by rfl) ⟨406869, by rfl⟩ : syracuseStep 1084985 = 813739) B813739
theorem B1216235 : Blo 479788 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B724715 : Blo 479788 724715 := bstep (se 1 (by rfl) ⟨543536, by rfl⟩ : syracuseStep 724715 = 1087073) B1087073
theorem B724943 : Blo 479788 724943 := bstep (se 1 (by rfl) ⟨543707, by rfl⟩ : syracuseStep 724943 = 1087415) B1087415
theorem B1085651 : Blo 479788 1085651 := bstep (se 1 (by rfl) ⟨814238, by rfl⟩ : syracuseStep 1085651 = 1628477) B1628477
theorem B1085705 : Blo 479788 1085705 := bstep (se 2 (by rfl) ⟨407139, by rfl⟩ : syracuseStep 1085705 = 814279) B814279
theorem B725339 : Blo 479788 725339 := bstep (se 1 (by rfl) ⟨544004, by rfl⟩ : syracuseStep 725339 = 1088009) B1088009
theorem B1085921 : Blo 479788 1085921 := bstep (se 2 (by rfl) ⟨407220, by rfl⟩ : syracuseStep 1085921 = 814441) B814441
theorem B725567 : Blo 479788 725567 := bstep (se 1 (by rfl) ⟨544175, by rfl⟩ : syracuseStep 725567 = 1088351) B1088351
theorem B1217207 : Blo 479788 1217207 := bstep (se 1 (by rfl) ⟨912905, by rfl⟩ : syracuseStep 1217207 = 1825811) B1825811
theorem B1086227 : Blo 479788 1086227 := bstep (se 1 (by rfl) ⟨814670, by rfl⟩ : syracuseStep 1086227 = 1629341) B1629341
theorem B15602777 : Blo 479788 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B1086587 : Blo 479788 1086587 := bstep (se 1 (by rfl) ⟨814940, by rfl⟩ : syracuseStep 1086587 = 1629881) B1629881
theorem B1086713 : Blo 479788 1086713 := bstep (se 2 (by rfl) ⟨407517, by rfl⟩ : syracuseStep 1086713 = 815035) B815035
theorem B1086857 : Blo 479788 1086857 := bstep (se 2 (by rfl) ⟨407571, by rfl⟩ : syracuseStep 1086857 = 815143) B815143
theorem B4101515 : Blo 479788 4101515 := bstep (se 1 (by rfl) ⟨3076136, by rfl⟩ : syracuseStep 4101515 = 6152273) B6152273
theorem B1086983 : Blo 479788 1086983 := bstep (se 1 (by rfl) ⟨815237, by rfl⟩ : syracuseStep 1086983 = 1630475) B1630475
theorem B1087163 : Blo 479788 1087163 := bstep (se 1 (by rfl) ⟨815372, by rfl⟩ : syracuseStep 1087163 = 1630745) B1630745
theorem B1218311 : Blo 479788 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B1218361 : Blo 479788 1218361 := bstep (se 2 (by rfl) ⟨456885, by rfl⟩ : syracuseStep 1218361 = 913771) B913771
theorem B1087289 : Blo 479788 1087289 := bstep (se 2 (by rfl) ⟨407733, by rfl⟩ : syracuseStep 1087289 = 815467) B815467
theorem B6199325 : Blo 479788 6199325 := bstep (se 3 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 6199325 = 2324747) B2324747
theorem B5937185 : Blo 479788 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B1218665 : Blo 479788 1218665 := bstep (se 2 (by rfl) ⟨456999, by rfl⟩ : syracuseStep 1218665 = 913999) B913999
theorem B2202023 : Blo 479788 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B1087919 : Blo 479788 1087919 := bstep (se 1 (by rfl) ⟨815939, by rfl⟩ : syracuseStep 1087919 = 1631879) B1631879
theorem B1087955 : Blo 479788 1087955 := bstep (se 1 (by rfl) ⟨815966, by rfl⟩ : syracuseStep 1087955 = 1631933) B1631933
theorem B1088063 : Blo 479788 1088063 := bstep (se 1 (by rfl) ⟨816047, by rfl⟩ : syracuseStep 1088063 = 1632095) B1632095
theorem B1219151 : Blo 479788 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B1546859 : Blo 479788 1546859 := bstep (se 1 (by rfl) ⟨1160144, by rfl⟩ : syracuseStep 1546859 = 2320289) B2320289
theorem B1088171 : Blo 479788 1088171 := bstep (se 1 (by rfl) ⟨816128, by rfl⟩ : syracuseStep 1088171 = 1632257) B1632257
theorem B8231867 : Blo 479788 8231867 := bstep (se 1 (by rfl) ⟨6173900, by rfl⟩ : syracuseStep 8231867 = 12347801) B12347801
theorem B1219799 : Blo 479788 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B2432267 : Blo 479788 2432267 := bstep (se 1 (by rfl) ⟨1824200, by rfl⟩ : syracuseStep 2432267 = 3648401) B3648401
theorem B9248093 : Blo 479788 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B3087953 : Blo 479788 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B696043 : Blo 479788 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B4169465 : Blo 479788 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B1548089 : Blo 479788 1548089 := bstep (se 2 (by rfl) ⟨580533, by rfl⟩ : syracuseStep 1548089 = 1161067) B1161067
theorem B1548499 : Blo 479788 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B13345249 : Blo 479788 13345249 := bstep (se 2 (by rfl) ⟨5004468, by rfl⟩ : syracuseStep 13345249 = 10008937) B10008937
theorem B1221115 : Blo 479788 1221115 := bstep (se 1 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 1221115 = 1831673) B1831673
theorem B1155647 : Blo 479788 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B1221227 : Blo 479788 1221227 := bstep (se 1 (by rfl) ⟨915920, by rfl⟩ : syracuseStep 1221227 = 1831841) B1831841
theorem B2433887 : Blo 479788 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B3089411 : Blo 479788 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B3908807 : Blo 479788 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B1221875 : Blo 479788 1221875 := bstep (se 1 (by rfl) ⟨916406, by rfl⟩ : syracuseStep 1221875 = 1832813) B1832813
theorem B1025311 : Blo 479788 1025311 := bstep (se 1 (by rfl) ⟨768983, by rfl⟩ : syracuseStep 1025311 = 1537967) B1537967
theorem B4629811 : Blo 479788 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B1549729 : Blo 479788 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B1222087 : Blo 479788 1222087 := bstep (se 1 (by rfl) ⟨916565, by rfl⟩ : syracuseStep 1222087 = 1833131) B1833131
theorem B3090413 : Blo 479788 3090413 := bstep (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) B1158905
theorem B2205949 : Blo 479788 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B4106639 : Blo 479788 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B3090899 : Blo 479788 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B2435831 : Blo 479788 2435831 := bstep (se 1 (by rfl) ⟨1826873, by rfl⟩ : syracuseStep 2435831 = 3653747) B3653747
theorem B1223819 : Blo 479788 1223819 := bstep (se 1 (by rfl) ⟨917864, by rfl⟩ : syracuseStep 1223819 = 1835729) B1835729
theorem B1322183 : Blo 479788 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B5024987 : Blo 479788 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B2436317 : Blo 479788 2436317 := bstep (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) B913619
theorem B1224031 : Blo 479788 1224031 := bstep (se 1 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 1224031 = 1836047) B1836047
theorem B3648887 : Blo 479788 3648887 := bstep (se 1 (by rfl) ⟨2736665, by rfl⟩ : syracuseStep 3648887 = 5473331) B5473331
theorem B16035191 : Blo 479788 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B3092539 : Blo 479788 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B1356257 : Blo 479788 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B40121335 : Blo 479788 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B1160183 : Blo 479788 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B2307217 : Blo 479788 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B2733203 : Blo 479788 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B6960401 : Blo 479788 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B1619513 : Blo 479788 1619513 := bstep (se 2 (by rfl) ⟨607317, by rfl⟩ : syracuseStep 1619513 = 1214635) B1214635
theorem B2733911 : Blo 479788 2733911 := bstep (se 1 (by rfl) ⟨2050433, by rfl⟩ : syracuseStep 2733911 = 4100867) B4100867
theorem B48215969 : Blo 479788 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B2439719 : Blo 479788 2439719 := bstep (se 1 (by rfl) ⟨1829789, by rfl⟩ : syracuseStep 2439719 = 3659579) B3659579
theorem B1030727 : Blo 479788 1030727 := bstep (se 1 (by rfl) ⟨773045, by rfl⟩ : syracuseStep 1030727 = 1546091) B1546091
theorem B1620755 : Blo 479788 1620755 := bstep (se 1 (by rfl) ⟨1215566, by rfl⟩ : syracuseStep 1620755 = 2431133) B2431133
theorem B539995 : Blo 479788 539995 := bstep (se 1 (by rfl) ⟨404996, by rfl⟩ : syracuseStep 539995 = 809993) B809993
theorem B2309563 : Blo 479788 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B540103 : Blo 479788 540103 := bstep (se 1 (by rfl) ⟨405077, by rfl⟩ : syracuseStep 540103 = 810155) B810155
theorem B1621619 : Blo 479788 1621619 := bstep (se 1 (by rfl) ⟨1216214, by rfl⟩ : syracuseStep 1621619 = 2432429) B2432429
theorem B1031915 : Blo 479788 1031915 := bstep (se 1 (by rfl) ⟨773936, by rfl⟩ : syracuseStep 1031915 = 1547873) B1547873
theorem B7520003 : Blo 479788 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B540463 : Blo 479788 540463 := bstep (se 1 (by rfl) ⟨405347, by rfl⟩ : syracuseStep 540463 = 810695) B810695
theorem B1752961 : Blo 479788 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B1621889 : Blo 479788 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B540571 : Blo 479788 540571 := bstep (se 1 (by rfl) ⟨405428, by rfl⟩ : syracuseStep 540571 = 810857) B810857
theorem B4636577 : Blo 479788 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B540967 : Blo 479788 540967 := bstep (se 1 (by rfl) ⟨405725, by rfl⟩ : syracuseStep 540967 = 811451) B811451
theorem B5226839 : Blo 479788 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B541039 : Blo 479788 541039 := bstep (se 1 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 541039 = 811559) B811559
theorem B541255 : Blo 479788 541255 := bstep (se 1 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 541255 = 811883) B811883
theorem B2441825 : Blo 479788 2441825 := bstep (se 2 (by rfl) ⟨915684, by rfl⟩ : syracuseStep 2441825 = 1831369) B1831369
theorem B1622699 : Blo 479788 1622699 := bstep (se 1 (by rfl) ⟨1217024, by rfl⟩ : syracuseStep 1622699 = 2434049) B2434049
theorem B5259977 : Blo 479788 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B4441051 : Blo 479788 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B1623239 : Blo 479788 1623239 := bstep (se 1 (by rfl) ⟨1217429, by rfl⟩ : syracuseStep 1623239 = 2434859) B2434859
theorem B1852649 : Blo 479788 1852649 := bstep (se 2 (by rfl) ⟨694743, by rfl⟩ : syracuseStep 1852649 = 1389487) B1389487
theorem B2442473 : Blo 479788 2442473 := bstep (se 2 (by rfl) ⟨915927, by rfl⟩ : syracuseStep 2442473 = 1831855) B1831855
theorem B2639147 : Blo 479788 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B2442635 : Blo 479788 2442635 := bstep (se 1 (by rfl) ⟨1831976, by rfl⟩ : syracuseStep 2442635 = 3663953) B3663953
theorem B542119 : Blo 479788 542119 := bstep (se 1 (by rfl) ⟨406589, by rfl⟩ : syracuseStep 542119 = 813179) B813179
theorem B1099207 : Blo 479788 1099207 := bstep (se 1 (by rfl) ⟨824405, by rfl⟩ : syracuseStep 1099207 = 1648811) B1648811
theorem B509743 : Blo 479788 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B542695 : Blo 479788 542695 := bstep (se 1 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 542695 = 814043) B814043
theorem B7784525 : Blo 479788 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B2607299 : Blo 479788 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B1624751 : Blo 479788 1624751 := bstep (se 1 (by rfl) ⟨1218563, by rfl⟩ : syracuseStep 1624751 = 2437127) B2437127
theorem B1625075 : Blo 479788 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B1854451 : Blo 479788 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B2051527 : Blo 479788 2051527 := bstep (se 1 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 2051527 = 3077291) B3077291
theorem B2051543 : Blo 479788 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B1625615 : Blo 479788 1625615 := bstep (se 1 (by rfl) ⟨1219211, by rfl⟩ : syracuseStep 1625615 = 2438423) B2438423
theorem B2051851 : Blo 479788 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B13881131 : Blo 479788 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B1822621 : Blo 479788 1822621 := bstep (se 3 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 1822621 = 683483) B683483
theorem B2314291 : Blo 479788 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B2084923 : Blo 479788 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B2609633 : Blo 479788 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B2478593 : Blo 479788 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B2445875 : Blo 479788 2445875 := bstep (se 1 (by rfl) ⟨1834406, by rfl⟩ : syracuseStep 2445875 = 3668813) B3668813
theorem B479807 : Blo 479788 479807 := bstep (se 1 (by rfl) ⟨359855, by rfl⟩ : syracuseStep 479807 = 719711) B719711
theorem B479815 : Blo 479788 479815 := bstep (se 1 (by rfl) ⟨359861, by rfl⟩ : syracuseStep 479815 = 719723) B719723
theorem B1626695 : Blo 479788 1626695 := bstep (se 1 (by rfl) ⟨1220021, by rfl⟩ : syracuseStep 1626695 = 2440043) B2440043
theorem B11686517 : Blo 479788 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B479967 : Blo 479788 479967 := bstep (se 1 (by rfl) ⟨359975, by rfl⟩ : syracuseStep 479967 = 719951) B719951
theorem B480047 : Blo 479788 480047 := bstep (se 1 (by rfl) ⟨360035, by rfl⟩ : syracuseStep 480047 = 720071) B720071
theorem B676687 : Blo 479788 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B480155 : Blo 479788 480155 := bstep (se 1 (by rfl) ⟨360116, by rfl⟩ : syracuseStep 480155 = 720233) B720233
theorem B480207 : Blo 479788 480207 := bstep (se 1 (by rfl) ⟨360155, by rfl⟩ : syracuseStep 480207 = 720311) B720311
theorem B480231 : Blo 479788 480231 := bstep (se 1 (by rfl) ⟨360173, by rfl⟩ : syracuseStep 480231 = 720347) B720347
theorem B1627127 : Blo 479788 1627127 := bstep (se 1 (by rfl) ⟨1220345, by rfl⟩ : syracuseStep 1627127 = 2440691) B2440691
theorem B1463539 : Blo 479788 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B480543 : Blo 479788 480543 := bstep (se 1 (by rfl) ⟨360407, by rfl⟩ : syracuseStep 480543 = 720815) B720815
theorem B480603 : Blo 479788 480603 := bstep (se 1 (by rfl) ⟨360452, by rfl⟩ : syracuseStep 480603 = 720905) B720905
theorem B480623 : Blo 479788 480623 := bstep (se 1 (by rfl) ⟨360467, by rfl⟩ : syracuseStep 480623 = 720935) B720935
theorem B611707 : Blo 479788 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B480679 : Blo 479788 480679 := bstep (se 1 (by rfl) ⟨360509, by rfl⟩ : syracuseStep 480679 = 721019) B721019
theorem B480763 : Blo 479788 480763 := bstep (se 1 (by rfl) ⟨360572, by rfl⟩ : syracuseStep 480763 = 721145) B721145
theorem B480831 : Blo 479788 480831 := bstep (se 1 (by rfl) ⟨360623, by rfl⟩ : syracuseStep 480831 = 721247) B721247
theorem B480839 : Blo 479788 480839 := bstep (se 1 (by rfl) ⟨360629, by rfl⟩ : syracuseStep 480839 = 721259) B721259
theorem B480991 : Blo 479788 480991 := bstep (se 1 (by rfl) ⟨360743, by rfl⟩ : syracuseStep 480991 = 721487) B721487
theorem B481071 : Blo 479788 481071 := bstep (se 1 (by rfl) ⟨360803, by rfl⟩ : syracuseStep 481071 = 721607) B721607
theorem B1627991 : Blo 479788 1627991 := bstep (se 1 (by rfl) ⟨1220993, by rfl⟩ : syracuseStep 1627991 = 2441987) B2441987
theorem B481179 : Blo 479788 481179 := bstep (se 1 (by rfl) ⟨360884, by rfl⟩ : syracuseStep 481179 = 721769) B721769
theorem B2316215 : Blo 479788 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B481231 : Blo 479788 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B481255 : Blo 479788 481255 := bstep (se 1 (by rfl) ⟨360941, by rfl⟩ : syracuseStep 481255 = 721883) B721883
theorem B2316367 : Blo 479788 2316367 := bstep (se 1 (by rfl) ⟨1737275, by rfl⟩ : syracuseStep 2316367 = 3474551) B3474551
theorem B2742407 : Blo 479788 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B2447495 : Blo 479788 2447495 := bstep (se 1 (by rfl) ⟨1835621, by rfl⟩ : syracuseStep 2447495 = 3671243) B3671243
theorem B579803 : Blo 479788 579803 := bstep (se 1 (by rfl) ⟨434852, by rfl⟩ : syracuseStep 579803 = 869705) B869705
theorem B2480381 : Blo 479788 2480381 := bstep (se 3 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 2480381 = 930143) B930143
theorem B481567 : Blo 479788 481567 := bstep (se 1 (by rfl) ⟨361175, by rfl⟩ : syracuseStep 481567 = 722351) B722351
theorem B481627 : Blo 479788 481627 := bstep (se 1 (by rfl) ⟨361220, by rfl⟩ : syracuseStep 481627 = 722441) B722441
theorem B481647 : Blo 479788 481647 := bstep (se 1 (by rfl) ⟨361235, by rfl⟩ : syracuseStep 481647 = 722471) B722471
theorem B2087279 : Blo 479788 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B481703 : Blo 479788 481703 := bstep (se 1 (by rfl) ⟨361277, by rfl⟩ : syracuseStep 481703 = 722555) B722555
theorem B481787 : Blo 479788 481787 := bstep (se 1 (by rfl) ⟨361340, by rfl⟩ : syracuseStep 481787 = 722681) B722681
theorem B1366591 : Blo 479788 1366591 := bstep (se 1 (by rfl) ⟨1024943, by rfl⟩ : syracuseStep 1366591 = 2049887) B2049887
theorem B481855 : Blo 479788 481855 := bstep (se 1 (by rfl) ⟨361391, by rfl⟩ : syracuseStep 481855 = 722783) B722783
theorem B580159 : Blo 479788 580159 := bstep (se 1 (by rfl) ⟨435119, by rfl⟩ : syracuseStep 580159 = 870239) B870239
theorem B481863 : Blo 479788 481863 := bstep (se 1 (by rfl) ⟨361397, by rfl⟩ : syracuseStep 481863 = 722795) B722795
theorem B482015 : Blo 479788 482015 := bstep (se 1 (by rfl) ⟨361511, by rfl⟩ : syracuseStep 482015 = 723023) B723023
theorem B482095 : Blo 479788 482095 := bstep (se 1 (by rfl) ⟨361571, by rfl⟩ : syracuseStep 482095 = 723143) B723143
theorem B1629071 : Blo 479788 1629071 := bstep (se 1 (by rfl) ⟨1221803, by rfl⟩ : syracuseStep 1629071 = 2443607) B2443607
theorem B482203 : Blo 479788 482203 := bstep (se 1 (by rfl) ⟨361652, by rfl⟩ : syracuseStep 482203 = 723305) B723305
theorem B482255 : Blo 479788 482255 := bstep (se 1 (by rfl) ⟨361691, by rfl⟩ : syracuseStep 482255 = 723383) B723383
theorem B809959 : Blo 479788 809959 := bstep (se 1 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 809959 = 1214939) B1214939
theorem B482279 : Blo 479788 482279 := bstep (se 1 (by rfl) ⟨361709, by rfl⟩ : syracuseStep 482279 = 723419) B723419
theorem B482591 : Blo 479788 482591 := bstep (se 1 (by rfl) ⟨361943, by rfl⟩ : syracuseStep 482591 = 723887) B723887
theorem B482651 : Blo 479788 482651 := bstep (se 1 (by rfl) ⟨361988, by rfl⟩ : syracuseStep 482651 = 723977) B723977
theorem B482671 : Blo 479788 482671 := bstep (se 1 (by rfl) ⟨362003, by rfl⟩ : syracuseStep 482671 = 724007) B724007
theorem B482727 : Blo 479788 482727 := bstep (se 1 (by rfl) ⟨362045, by rfl⟩ : syracuseStep 482727 = 724091) B724091
theorem B1826297 : Blo 479788 1826297 := bstep (se 2 (by rfl) ⟨684861, by rfl⟩ : syracuseStep 1826297 = 1369723) B1369723
theorem B482811 : Blo 479788 482811 := bstep (se 1 (by rfl) ⟨362108, by rfl⟩ : syracuseStep 482811 = 724217) B724217
theorem B482879 : Blo 479788 482879 := bstep (se 1 (by rfl) ⟨362159, by rfl⟩ : syracuseStep 482879 = 724319) B724319
theorem B482887 : Blo 479788 482887 := bstep (se 1 (by rfl) ⟨362165, by rfl⟩ : syracuseStep 482887 = 724331) B724331
theorem B483039 : Blo 479788 483039 := bstep (se 1 (by rfl) ⟨362279, by rfl⟩ : syracuseStep 483039 = 724559) B724559
theorem B483119 : Blo 479788 483119 := bstep (se 1 (by rfl) ⟨362339, by rfl⟩ : syracuseStep 483119 = 724679) B724679
theorem B483227 : Blo 479788 483227 := bstep (se 1 (by rfl) ⟨362420, by rfl⟩ : syracuseStep 483227 = 724841) B724841
theorem B483279 : Blo 479788 483279 := bstep (se 1 (by rfl) ⟨362459, by rfl⟩ : syracuseStep 483279 = 724919) B724919
theorem B483303 : Blo 479788 483303 := bstep (se 1 (by rfl) ⟨362477, by rfl⟩ : syracuseStep 483303 = 724955) B724955
theorem B1630313 : Blo 479788 1630313 := bstep (se 2 (by rfl) ⟨611367, by rfl⟩ : syracuseStep 1630313 = 1222735) B1222735
theorem B483615 : Blo 479788 483615 := bstep (se 1 (by rfl) ⟨362711, by rfl⟩ : syracuseStep 483615 = 725423) B725423
theorem B483675 : Blo 479788 483675 := bstep (se 1 (by rfl) ⟨362756, by rfl⟩ : syracuseStep 483675 = 725513) B725513
theorem B483695 : Blo 479788 483695 := bstep (se 1 (by rfl) ⟨362771, by rfl⟩ : syracuseStep 483695 = 725543) B725543
theorem B483751 : Blo 479788 483751 := bstep (se 1 (by rfl) ⟨362813, by rfl⟩ : syracuseStep 483751 = 725627) B725627
theorem B1827481 : Blo 479788 1827481 := bstep (se 2 (by rfl) ⟨685305, by rfl⟩ : syracuseStep 1827481 = 1370611) B1370611
theorem B1827785 : Blo 479788 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B1631177 : Blo 479788 1631177 := bstep (se 2 (by rfl) ⟨611691, by rfl⟩ : syracuseStep 1631177 = 1223383) B1223383
theorem B1631447 : Blo 479788 1631447 := bstep (se 1 (by rfl) ⟨1223585, by rfl⟩ : syracuseStep 1631447 = 2447171) B2447171
theorem B648559 : Blo 479788 648559 := bstep (se 1 (by rfl) ⟨486419, by rfl⟩ : syracuseStep 648559 = 972839) B972839
theorem B4646267 : Blo 479788 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B1304147 : Blo 479788 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B812639 : Blo 479788 812639 := bstep (se 1 (by rfl) ⟨609479, by rfl⟩ : syracuseStep 812639 = 1218959) B1218959
theorem B911083 : Blo 479788 911083 := bstep (se 1 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 911083 = 1366625) B1366625
theorem B911159 : Blo 479788 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B812855 : Blo 479788 812855 := bstep (se 1 (by rfl) ⟨609641, by rfl⟩ : syracuseStep 812855 = 1219283) B1219283
theorem B1468697 : Blo 479788 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B911827 : Blo 479788 911827 := bstep (se 1 (by rfl) ⟨683870, by rfl⟩ : syracuseStep 911827 = 1367741) B1367741
theorem B813631 : Blo 479788 813631 := bstep (se 1 (by rfl) ⟨610223, by rfl⟩ : syracuseStep 813631 = 1220447) B1220447
theorem B912055 : Blo 479788 912055 := bstep (se 1 (by rfl) ⟨684041, by rfl⟩ : syracuseStep 912055 = 1368083) B1368083
theorem B11168441 : Blo 479788 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B1305499 : Blo 479788 1305499 := bstep (se 1 (by rfl) ⟨979124, by rfl⟩ : syracuseStep 1305499 = 1958249) B1958249
theorem B912359 : Blo 479788 912359 := bstep (se 1 (by rfl) ⟨684269, by rfl⟩ : syracuseStep 912359 = 1368539) B1368539
theorem B912617 : Blo 479788 912617 := bstep (se 2 (by rfl) ⟨342231, by rfl⟩ : syracuseStep 912617 = 684463) B684463
theorem B814313 : Blo 479788 814313 := bstep (se 2 (by rfl) ⟨305367, by rfl⟩ : syracuseStep 814313 = 610735) B610735
theorem B814367 : Blo 479788 814367 := bstep (se 1 (by rfl) ⟨610775, by rfl⟩ : syracuseStep 814367 = 1221551) B1221551
theorem B978743 : Blo 479788 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B2191369 : Blo 479788 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B913513 : Blo 479788 913513 := bstep (se 2 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 913513 = 685135) B685135
theorem B913673 : Blo 479788 913673 := bstep (se 2 (by rfl) ⟨342627, by rfl⟩ : syracuseStep 913673 = 685255) B685255
theorem B815737 : Blo 479788 815737 := bstep (se 2 (by rfl) ⟨305901, by rfl⟩ : syracuseStep 815737 = 611803) B611803
theorem B815791 : Blo 479788 815791 := bstep (se 1 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 815791 = 1223687) B1223687
theorem B14873507 : Blo 479788 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B979943 : Blo 479788 979943 := bstep (se 1 (by rfl) ⟨734957, by rfl⟩ : syracuseStep 979943 = 1469915) B1469915
theorem B4125775 : Blo 479788 4125775 := bstep (se 1 (by rfl) ⟨3094331, by rfl⟩ : syracuseStep 4125775 = 6188663) B6188663
theorem B685351 : Blo 479788 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B915131 : Blo 479788 915131 := bstep (se 1 (by rfl) ⟨686348, by rfl⟩ : syracuseStep 915131 = 1372697) B1372697
theorem B76904549 : Blo 479788 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B1734941 : Blo 479788 1734941 := bstep (se 3 (by rfl) ⟨325301, by rfl⟩ : syracuseStep 1734941 = 650603) B650603
theorem B6191639 : Blo 479788 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B686713 : Blo 479788 686713 := bstep (se 2 (by rfl) ⟨257517, by rfl⟩ : syracuseStep 686713 = 515035) B515035
theorem B8321737 : Blo 479788 8321737 := bstep (se 2 (by rfl) ⟨3120651, by rfl⟩ : syracuseStep 8321737 = 6241303) B6241303
theorem B3078931 : Blo 479788 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B1080143 : Blo 479788 1080143 := bstep (se 1 (by rfl) ⟨810107, by rfl⟩ : syracuseStep 1080143 = 1620215) B1620215
theorem B719771 : Blo 479788 719771 := bstep (se 1 (by rfl) ⟨539828, by rfl⟩ : syracuseStep 719771 = 1079657) B1079657
theorem B1080359 : Blo 479788 1080359 := bstep (se 1 (by rfl) ⟨810269, by rfl⟩ : syracuseStep 1080359 = 1620539) B1620539
theorem B1080539 : Blo 479788 1080539 := bstep (se 1 (by rfl) ⟨810404, by rfl⟩ : syracuseStep 1080539 = 1620809) B1620809
theorem B1834271 : Blo 479788 1834271 := bstep (se 1 (by rfl) ⟨1375703, by rfl⟩ : syracuseStep 1834271 = 2751407) B2751407
theorem B720167 : Blo 479788 720167 := bstep (se 1 (by rfl) ⟨540125, by rfl⟩ : syracuseStep 720167 = 1080251) B1080251
theorem B720251 : Blo 479788 720251 := bstep (se 1 (by rfl) ⟨540188, by rfl⟩ : syracuseStep 720251 = 1080377) B1080377
theorem B1080737 : Blo 479788 1080737 := bstep (se 2 (by rfl) ⟨405276, by rfl⟩ : syracuseStep 1080737 = 810553) B810553
theorem B720377 : Blo 479788 720377 := bstep (se 2 (by rfl) ⟨270141, by rfl⟩ : syracuseStep 720377 = 540283) B540283
theorem B3964439 : Blo 479788 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B917075 : Blo 479788 917075 := bstep (se 1 (by rfl) ⟨687806, by rfl⟩ : syracuseStep 917075 = 1375613) B1375613
theorem B720479 : Blo 479788 720479 := bstep (se 1 (by rfl) ⟨540359, by rfl⟩ : syracuseStep 720479 = 1080719) B1080719
theorem B3079775 : Blo 479788 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B2063981 : Blo 479788 2063981 := bstep (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) B773993
theorem B1736353 : Blo 479788 1736353 := bstep (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) B1302265
theorem B720695 : Blo 479788 720695 := bstep (se 1 (by rfl) ⟨540521, by rfl⟩ : syracuseStep 720695 = 1081043) B1081043
theorem B1081295 : Blo 479788 1081295 := bstep (se 1 (by rfl) ⟨810971, by rfl⟩ : syracuseStep 1081295 = 1621943) B1621943
theorem B721115 : Blo 479788 721115 := bstep (se 1 (by rfl) ⟨540836, by rfl⟩ : syracuseStep 721115 = 1081673) B1081673
theorem B721127 : Blo 479788 721127 := bstep (se 1 (by rfl) ⟨540845, by rfl⟩ : syracuseStep 721127 = 1081691) B1081691
theorem B2064665 : Blo 479788 2064665 := bstep (se 2 (by rfl) ⟨774249, by rfl⟩ : syracuseStep 2064665 = 1548499) B1548499
theorem B721289 : Blo 479788 721289 := bstep (se 2 (by rfl) ⟨270483, by rfl⟩ : syracuseStep 721289 = 540967) B540967
theorem B1081799 : Blo 479788 1081799 := bstep (se 1 (by rfl) ⟨811349, by rfl⟩ : syracuseStep 1081799 = 1622699) B1622699
theorem B3506651 : Blo 479788 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B721385 : Blo 479788 721385 := bstep (se 2 (by rfl) ⟨270519, by rfl⟩ : syracuseStep 721385 = 541039) B541039
theorem B917993 : Blo 479788 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B3080699 : Blo 479788 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B1376831 : Blo 479788 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B721511 : Blo 479788 721511 := bstep (se 1 (by rfl) ⟨541133, by rfl⟩ : syracuseStep 721511 = 1082267) B1082267
theorem B17793665 : Blo 479788 17793665 := bstep (se 2 (by rfl) ⟨6672624, by rfl⟩ : syracuseStep 17793665 = 13345249) B13345249
theorem B721643 : Blo 479788 721643 := bstep (se 1 (by rfl) ⟨541232, by rfl⟩ : syracuseStep 721643 = 1082465) B1082465
theorem B721673 : Blo 479788 721673 := bstep (se 2 (by rfl) ⟨270627, by rfl⟩ : syracuseStep 721673 = 541255) B541255
theorem B1082159 : Blo 479788 1082159 := bstep (se 1 (by rfl) ⟨811619, by rfl⟩ : syracuseStep 1082159 = 1623239) B1623239
theorem B1377071 : Blo 479788 1377071 := bstep (se 1 (by rfl) ⟨1032803, by rfl⟩ : syracuseStep 1377071 = 2065607) B2065607
theorem B12387167 : Blo 479788 12387167 := bstep (se 1 (by rfl) ⟨9290375, by rfl⟩ : syracuseStep 12387167 = 18580751) B18580751
theorem B721775 : Blo 479788 721775 := bstep (se 1 (by rfl) ⟨541331, by rfl⟩ : syracuseStep 721775 = 1082663) B1082663
theorem B722027 : Blo 479788 722027 := bstep (se 1 (by rfl) ⟨541520, by rfl⟩ : syracuseStep 722027 = 1083041) B1083041
theorem B722267 : Blo 479788 722267 := bstep (se 1 (by rfl) ⟨541700, by rfl⟩ : syracuseStep 722267 = 1083401) B1083401
theorem B1738199 : Blo 479788 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B1836503 : Blo 479788 1836503 := bstep (se 1 (by rfl) ⟨1377377, by rfl⟩ : syracuseStep 1836503 = 2754755) B2754755
theorem B3081725 : Blo 479788 3081725 := bstep (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) B1155647
theorem B722543 : Blo 479788 722543 := bstep (se 1 (by rfl) ⟨541907, by rfl⟩ : syracuseStep 722543 = 1083815) B1083815
theorem B722615 : Blo 479788 722615 := bstep (se 1 (by rfl) ⟨541961, by rfl⟩ : syracuseStep 722615 = 1083923) B1083923
theorem B722651 : Blo 479788 722651 := bstep (se 1 (by rfl) ⟨541988, by rfl⟩ : syracuseStep 722651 = 1083977) B1083977
theorem B1083167 : Blo 479788 1083167 := bstep (se 1 (by rfl) ⟨812375, by rfl⟩ : syracuseStep 1083167 = 1624751) B1624751
theorem B2066305 : Blo 479788 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B722825 : Blo 479788 722825 := bstep (se 2 (by rfl) ⟨271059, by rfl⟩ : syracuseStep 722825 = 542119) B542119
theorem B722927 : Blo 479788 722927 := bstep (se 1 (by rfl) ⟨542195, by rfl⟩ : syracuseStep 722927 = 1084391) B1084391
theorem B1083383 : Blo 479788 1083383 := bstep (se 1 (by rfl) ⟨812537, by rfl⟩ : syracuseStep 1083383 = 1625075) B1625075
theorem B723179 : Blo 479788 723179 := bstep (se 1 (by rfl) ⟨542384, by rfl⟩ : syracuseStep 723179 = 1084769) B1084769
theorem B723239 : Blo 479788 723239 := bstep (se 1 (by rfl) ⟨542429, by rfl⟩ : syracuseStep 723239 = 1084859) B1084859
theorem B1214777 : Blo 479788 1214777 := bstep (se 2 (by rfl) ⟨455541, by rfl⟩ : syracuseStep 1214777 = 911083) B911083
theorem B1083743 : Blo 479788 1083743 := bstep (se 1 (by rfl) ⟨812807, by rfl⟩ : syracuseStep 1083743 = 1625615) B1625615
theorem B723323 : Blo 479788 723323 := bstep (se 1 (by rfl) ⟨542492, by rfl⟩ : syracuseStep 723323 = 1084985) B1084985
theorem B723593 : Blo 479788 723593 := bstep (se 2 (by rfl) ⟨271347, by rfl⟩ : syracuseStep 723593 = 542695) B542695
theorem B723767 : Blo 479788 723767 := bstep (se 1 (by rfl) ⟨542825, by rfl⟩ : syracuseStep 723767 = 1085651) B1085651
theorem B723803 : Blo 479788 723803 := bstep (se 1 (by rfl) ⟨542852, by rfl⟩ : syracuseStep 723803 = 1085705) B1085705
theorem B723947 : Blo 479788 723947 := bstep (se 1 (by rfl) ⟨542960, by rfl⟩ : syracuseStep 723947 = 1085921) B1085921
theorem B1739755 : Blo 479788 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B1084463 : Blo 479788 1084463 := bstep (se 1 (by rfl) ⟨813347, by rfl⟩ : syracuseStep 1084463 = 1626695) B1626695
theorem B724151 : Blo 479788 724151 := bstep (se 1 (by rfl) ⟨543113, by rfl⟩ : syracuseStep 724151 = 1086227) B1086227
theorem B1215769 : Blo 479788 1215769 := bstep (se 2 (by rfl) ⟨455913, by rfl⟩ : syracuseStep 1215769 = 911827) B911827
theorem B1084751 : Blo 479788 1084751 := bstep (se 1 (by rfl) ⟨813563, by rfl⟩ : syracuseStep 1084751 = 1627127) B1627127
theorem B724391 : Blo 479788 724391 := bstep (se 1 (by rfl) ⟨543293, by rfl⟩ : syracuseStep 724391 = 1086587) B1086587
theorem B1084841 : Blo 479788 1084841 := bstep (se 2 (by rfl) ⟨406815, by rfl⟩ : syracuseStep 1084841 = 813631) B813631
theorem B724475 : Blo 479788 724475 := bstep (se 1 (by rfl) ⟨543356, by rfl⟩ : syracuseStep 724475 = 1086713) B1086713
theorem B1216073 : Blo 479788 1216073 := bstep (se 2 (by rfl) ⟨456027, by rfl⟩ : syracuseStep 1216073 = 912055) B912055
theorem B724571 : Blo 479788 724571 := bstep (se 1 (by rfl) ⟨543428, by rfl⟩ : syracuseStep 724571 = 1086857) B1086857
theorem B724655 : Blo 479788 724655 := bstep (se 1 (by rfl) ⟨543491, by rfl⟩ : syracuseStep 724655 = 1086983) B1086983
theorem B724775 : Blo 479788 724775 := bstep (se 1 (by rfl) ⟨543581, by rfl⟩ : syracuseStep 724775 = 1087163) B1087163
theorem B1740665 : Blo 479788 1740665 := bstep (se 2 (by rfl) ⟨652749, by rfl⟩ : syracuseStep 1740665 = 1305499) B1305499
theorem B724859 : Blo 479788 724859 := bstep (se 1 (by rfl) ⟨543644, by rfl⟩ : syracuseStep 724859 = 1087289) B1087289
theorem B1085327 : Blo 479788 1085327 := bstep (se 1 (by rfl) ⟨813995, by rfl⟩ : syracuseStep 1085327 = 1627991) B1627991
theorem B1544143 : Blo 479788 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B4132883 : Blo 479788 4132883 := bstep (se 1 (by rfl) ⟨3099662, by rfl⟩ : syracuseStep 4132883 = 6199325) B6199325
theorem B3477725 : Blo 479788 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B725279 : Blo 479788 725279 := bstep (se 1 (by rfl) ⟨543959, by rfl⟩ : syracuseStep 725279 = 1087919) B1087919
theorem B725303 : Blo 479788 725303 := bstep (se 1 (by rfl) ⟨543977, by rfl⟩ : syracuseStep 725303 = 1087955) B1087955
theorem B725375 : Blo 479788 725375 := bstep (se 1 (by rfl) ⟨544031, by rfl⟩ : syracuseStep 725375 = 1088063) B1088063
theorem B725447 : Blo 479788 725447 := bstep (se 1 (by rfl) ⟨544085, by rfl⟩ : syracuseStep 725447 = 1088171) B1088171
theorem B1086047 : Blo 479788 1086047 := bstep (se 1 (by rfl) ⟨814535, by rfl⟩ : syracuseStep 1086047 = 1629071) B1629071
theorem B6165395 : Blo 479788 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B1217531 : Blo 479788 1217531 := bstep (se 1 (by rfl) ⟨913148, by rfl⟩ : syracuseStep 1217531 = 1826297) B1826297
theorem B2430161 : Blo 479788 2430161 := bstep (se 2 (by rfl) ⟨911310, by rfl⟩ : syracuseStep 2430161 = 1822621) B1822621
theorem B2921825 : Blo 479788 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B3085721 : Blo 479788 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B1086875 : Blo 479788 1086875 := bstep (se 1 (by rfl) ⟨815156, by rfl⟩ : syracuseStep 1086875 = 1630313) B1630313
theorem B15832493 : Blo 479788 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B1218017 : Blo 479788 1218017 := bstep (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) B913513
theorem B1546141 : Blo 479788 1546141 := bstep (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) B579803
theorem B1218523 : Blo 479788 1218523 := bstep (se 1 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 1218523 = 1827785) B1827785
theorem B1087451 : Blo 479788 1087451 := bstep (se 1 (by rfl) ⟨815588, by rfl⟩ : syracuseStep 1087451 = 1631177) B1631177
theorem B1087631 : Blo 479788 1087631 := bstep (se 1 (by rfl) ⟨815723, by rfl⟩ : syracuseStep 1087631 = 1631447) B1631447
theorem B1087649 : Blo 479788 1087649 := bstep (se 2 (by rfl) ⟨407868, by rfl⟩ : syracuseStep 1087649 = 815737) B815737
theorem B1087721 : Blo 479788 1087721 := bstep (se 2 (by rfl) ⟨407895, by rfl⟩ : syracuseStep 1087721 = 815791) B815791
theorem B5872061 : Blo 479788 5872061 := bstep (se 3 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 5872061 = 2202023) B2202023
theorem B7445627 : Blo 479788 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B3349991 : Blo 479788 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B2432591 : Blo 479788 2432591 := bstep (se 1 (by rfl) ⟨1824443, by rfl⟩ : syracuseStep 2432591 = 3648887) B3648887
theorem B10690127 : Blo 479788 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B3088489 : Blo 479788 3088489 := bstep (se 2 (by rfl) ⟨1158183, by rfl⟩ : syracuseStep 3088489 = 2316367) B2316367
theorem B4105241 : Blo 479788 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B3712229 : Blo 479788 3712229 := bstep (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) B696043
theorem B1156627 : Blo 479788 1156627 := bstep (se 1 (by rfl) ⟨867470, by rfl⟩ : syracuseStep 1156627 = 1734941) B1734941
theorem B1222847 : Blo 479788 1222847 := bstep (se 1 (by rfl) ⟨917135, by rfl⟩ : syracuseStep 1222847 = 1834271) B1834271
theorem B2337281 : Blo 479788 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B3091051 : Blo 479788 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B3484559 : Blo 479788 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B11119589 : Blo 479788 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B2436641 : Blo 479788 2436641 := bstep (se 2 (by rfl) ⟨913740, by rfl⟩ : syracuseStep 2436641 = 1827481) B1827481
theorem B1224467 : Blo 479788 1224467 := bstep (se 1 (by rfl) ⟨918350, by rfl⟩ : syracuseStep 1224467 = 1836701) B1836701
theorem B5189683 : Blo 479788 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B4108553 : Blo 479788 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B3649859 : Blo 479788 3649859 := bstep (se 1 (by rfl) ⟨2737394, by rfl⟩ : syracuseStep 3649859 = 5474789) B5474789
theorem B6173081 : Blo 479788 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B864745 : Blo 479788 864745 := bstep (se 2 (by rfl) ⟨324279, by rfl⟩ : syracuseStep 864745 = 648559) B648559
theorem B5878291 : Blo 479788 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B9254087 : Blo 479788 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B3093821 : Blo 479788 3093821 := bstep (se 3 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 3093821 = 1160183) B1160183
theorem B1619297 : Blo 479788 1619297 := bstep (se 2 (by rfl) ⟨607236, by rfl⟩ : syracuseStep 1619297 = 1214473) B1214473
theorem B1652395 : Blo 479788 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B10401851 : Blo 479788 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B2734343 : Blo 479788 2734343 := bstep (se 1 (by rfl) ⟨2050757, by rfl⟩ : syracuseStep 2734343 = 4101515) B4101515
theorem B2472601 : Blo 479788 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B1653587 : Blo 479788 1653587 := bstep (se 1 (by rfl) ⟨1240190, by rfl⟩ : syracuseStep 1653587 = 2480381) B2480381
theorem B1096553 : Blo 479788 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B1391519 : Blo 479788 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B1031239 : Blo 479788 1031239 := bstep (se 1 (by rfl) ⟨773429, by rfl⟩ : syracuseStep 1031239 = 1546859) B1546859
theorem B1621241 : Blo 479788 1621241 := bstep (se 2 (by rfl) ⟨607965, by rfl⟩ : syracuseStep 1621241 = 1215931) B1215931
theorem B2735369 : Blo 479788 2735369 := bstep (se 2 (by rfl) ⟨1025763, by rfl⟩ : syracuseStep 2735369 = 2051527) B2051527
theorem B5487911 : Blo 479788 5487911 := bstep (se 1 (by rfl) ⟨4115933, by rfl⟩ : syracuseStep 5487911 = 8231867) B8231867
theorem B1621511 : Blo 479788 1621511 := bstep (se 1 (by rfl) ⟨1216133, by rfl⟩ : syracuseStep 1621511 = 2432267) B2432267
theorem B2735801 : Blo 479788 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B1032059 : Blo 479788 1032059 := bstep (se 1 (by rfl) ⟨774044, by rfl⟩ : syracuseStep 1032059 = 1548089) B1548089
theorem B1622591 : Blo 479788 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B3916525 : Blo 479788 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B2605871 : Blo 479788 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B3097511 : Blo 479788 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B541759 : Blo 479788 541759 := bstep (se 1 (by rfl) ⟨406319, by rfl⟩ : syracuseStep 541759 = 812639) B812639
theorem B902249 : Blo 479788 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B607439 : Blo 479788 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B541903 : Blo 479788 541903 := bstep (se 1 (by rfl) ⟨406427, by rfl⟩ : syracuseStep 541903 = 812855) B812855
theorem B53495113 : Blo 479788 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B3655205 : Blo 479788 3655205 := bstep (se 4 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 3655205 = 685351) B685351
theorem B2737759 : Blo 479788 2737759 := bstep (se 1 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 2737759 = 4106639) B4106639
theorem B1951385 : Blo 479788 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B1623887 : Blo 479788 1623887 := bstep (se 1 (by rfl) ⟨1217915, by rfl⟩ : syracuseStep 1623887 = 2435831) B2435831
theorem B608239 : Blo 479788 608239 := bstep (se 1 (by rfl) ⟨456179, by rfl⟩ : syracuseStep 608239 = 912359) B912359
theorem B1624211 : Blo 479788 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B608411 : Blo 479788 608411 := bstep (se 1 (by rfl) ⟨456308, by rfl⟩ : syracuseStep 608411 = 912617) B912617
theorem B542875 : Blo 479788 542875 := bstep (se 1 (by rfl) ⟨407156, by rfl⟩ : syracuseStep 542875 = 814313) B814313
theorem B542911 : Blo 479788 542911 := bstep (se 1 (by rfl) ⟨407183, by rfl⟩ : syracuseStep 542911 = 814367) B814367
theorem B1624481 : Blo 479788 1624481 := bstep (se 2 (by rfl) ⟨609180, by rfl⟩ : syracuseStep 1624481 = 1218361) B1218361
theorem B609115 : Blo 479788 609115 := bstep (se 1 (by rfl) ⟨456836, by rfl⟩ : syracuseStep 609115 = 913673) B913673
theorem B904171 : Blo 479788 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B9915671 : Blo 479788 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B1822121 : Blo 479788 1822121 := bstep (se 2 (by rfl) ⟨683295, by rfl⟩ : syracuseStep 1822121 = 1366591) B1366591
theorem B773545 : Blo 479788 773545 := bstep (se 2 (by rfl) ⟨290079, by rfl⟩ : syracuseStep 773545 = 580159) B580159
theorem B1822135 : Blo 479788 1822135 := bstep (se 1 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 1822135 = 2733203) B2733203
theorem B4640267 : Blo 479788 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B11095649 : Blo 479788 11095649 := bstep (se 2 (by rfl) ⟨4160868, by rfl⟩ : syracuseStep 11095649 = 8321737) B8321737
theorem B1756829 : Blo 479788 1756829 := bstep (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) B658811
theorem B610087 : Blo 479788 610087 := bstep (se 1 (by rfl) ⟨457565, by rfl⟩ : syracuseStep 610087 = 915131) B915131
theorem B1822607 : Blo 479788 1822607 := bstep (se 1 (by rfl) ⟨1366955, by rfl⟩ : syracuseStep 1822607 = 2733911) B2733911
theorem B51269699 : Blo 479788 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B1626479 : Blo 479788 1626479 := bstep (se 1 (by rfl) ⟨1219859, by rfl⟩ : syracuseStep 1626479 = 2439719) B2439719
theorem B479847 : Blo 479788 479847 := bstep (se 1 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 479847 = 719771) B719771
theorem B2609981 : Blo 479788 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B480111 : Blo 479788 480111 := bstep (se 1 (by rfl) ⟨360083, by rfl⟩ : syracuseStep 480111 = 720167) B720167
theorem B2315137 : Blo 479788 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B480167 : Blo 479788 480167 := bstep (se 1 (by rfl) ⟨360125, by rfl⟩ : syracuseStep 480167 = 720251) B720251
theorem B480251 : Blo 479788 480251 := bstep (se 1 (by rfl) ⟨360188, by rfl⟩ : syracuseStep 480251 = 720377) B720377
theorem B2642959 : Blo 479788 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B611383 : Blo 479788 611383 := bstep (se 1 (by rfl) ⟨458537, by rfl⟩ : syracuseStep 611383 = 917075) B917075
theorem B480319 : Blo 479788 480319 := bstep (se 1 (by rfl) ⟨360239, by rfl⟩ : syracuseStep 480319 = 720479) B720479
theorem B2053183 : Blo 479788 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B480463 : Blo 479788 480463 := bstep (se 1 (by rfl) ⟨360347, by rfl⟩ : syracuseStep 480463 = 720695) B720695
theorem B480667 : Blo 479788 480667 := bstep (se 1 (by rfl) ⟨360500, by rfl⟩ : syracuseStep 480667 = 721001) B721001
theorem B480879 : Blo 479788 480879 := bstep (se 1 (by rfl) ⟨360659, by rfl⟩ : syracuseStep 480879 = 721319) B721319
theorem B480935 : Blo 479788 480935 := bstep (se 1 (by rfl) ⟨360701, by rfl⟩ : syracuseStep 480935 = 721403) B721403
theorem B1627883 : Blo 479788 1627883 := bstep (se 1 (by rfl) ⟨1220912, by rfl⟩ : syracuseStep 1627883 = 2441825) B2441825
theorem B481019 : Blo 479788 481019 := bstep (se 1 (by rfl) ⟨360764, by rfl⟩ : syracuseStep 481019 = 721529) B721529
theorem B481055 : Blo 479788 481055 := bstep (se 1 (by rfl) ⟨360791, by rfl⟩ : syracuseStep 481055 = 721583) B721583
theorem B612127 : Blo 479788 612127 := bstep (se 1 (by rfl) ⟨459095, by rfl⟩ : syracuseStep 612127 = 918191) B918191
theorem B481087 : Blo 479788 481087 := bstep (se 1 (by rfl) ⟨360815, by rfl⟩ : syracuseStep 481087 = 721631) B721631
theorem B481263 : Blo 479788 481263 := bstep (se 1 (by rfl) ⟨360947, by rfl⟩ : syracuseStep 481263 = 721895) B721895
theorem B1628153 : Blo 479788 1628153 := bstep (se 2 (by rfl) ⟨610557, by rfl⟩ : syracuseStep 1628153 = 1221115) B1221115
theorem B1235099 : Blo 479788 1235099 := bstep (se 1 (by rfl) ⟨926324, by rfl⟩ : syracuseStep 1235099 = 1852649) B1852649
theorem B481435 : Blo 479788 481435 := bstep (se 1 (by rfl) ⟨361076, by rfl⟩ : syracuseStep 481435 = 722153) B722153
theorem B2316443 : Blo 479788 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B1628315 : Blo 479788 1628315 := bstep (se 1 (by rfl) ⟨1221236, by rfl⟩ : syracuseStep 1628315 = 2442473) B2442473
theorem B481471 : Blo 479788 481471 := bstep (se 1 (by rfl) ⟨361103, by rfl⟩ : syracuseStep 481471 = 722207) B722207
theorem B1628423 : Blo 479788 1628423 := bstep (se 1 (by rfl) ⟨1221317, by rfl⟩ : syracuseStep 1628423 = 2442635) B2442635
theorem B2447657 : Blo 479788 2447657 := bstep (se 2 (by rfl) ⟨917871, by rfl⟩ : syracuseStep 2447657 = 1835743) B1835743
theorem B481583 : Blo 479788 481583 := bstep (se 1 (by rfl) ⟨361187, by rfl⟩ : syracuseStep 481583 = 722375) B722375
theorem B7428631 : Blo 479788 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B481819 : Blo 479788 481819 := bstep (se 1 (by rfl) ⟨361364, by rfl⟩ : syracuseStep 481819 = 722729) B722729
theorem B481823 : Blo 479788 481823 := bstep (se 1 (by rfl) ⟨361367, by rfl⟩ : syracuseStep 481823 = 722735) B722735
theorem B3955499 : Blo 479788 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B482139 : Blo 479788 482139 := bstep (se 1 (by rfl) ⟨361604, by rfl⟩ : syracuseStep 482139 = 723209) B723209
theorem B482207 : Blo 479788 482207 := bstep (se 1 (by rfl) ⟨361655, by rfl⟩ : syracuseStep 482207 = 723311) B723311
theorem B1367081 : Blo 479788 1367081 := bstep (se 2 (by rfl) ⟨512655, by rfl⟩ : syracuseStep 1367081 = 1025311) B1025311
theorem B482351 : Blo 479788 482351 := bstep (se 1 (by rfl) ⟨361763, by rfl⟩ : syracuseStep 482351 = 723527) B723527
theorem B482375 : Blo 479788 482375 := bstep (se 1 (by rfl) ⟨361781, by rfl⟩ : syracuseStep 482375 = 723563) B723563
theorem B482527 : Blo 479788 482527 := bstep (se 1 (by rfl) ⟨361895, by rfl⟩ : syracuseStep 482527 = 723791) B723791
theorem B1465609 : Blo 479788 1465609 := bstep (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) B1099207
theorem B1629449 : Blo 479788 1629449 := bstep (se 2 (by rfl) ⟨611043, by rfl⟩ : syracuseStep 1629449 = 1222087) B1222087
theorem B482791 : Blo 479788 482791 := bstep (se 1 (by rfl) ⟨362093, by rfl⟩ : syracuseStep 482791 = 724187) B724187
theorem B810587 : Blo 479788 810587 := bstep (se 1 (by rfl) ⟨607940, by rfl⟩ : syracuseStep 810587 = 1215881) B1215881
theorem B482907 : Blo 479788 482907 := bstep (se 1 (by rfl) ⟨362180, by rfl⟩ : syracuseStep 482907 = 724361) B724361
theorem B1367695 : Blo 479788 1367695 := bstep (se 1 (by rfl) ⟨1025771, by rfl⟩ : syracuseStep 1367695 = 2051543) B2051543
theorem B679657 : Blo 479788 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B810823 : Blo 479788 810823 := bstep (se 1 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 810823 = 1216235) B1216235
theorem B483143 : Blo 479788 483143 := bstep (se 1 (by rfl) ⟨362357, by rfl⟩ : syracuseStep 483143 = 724715) B724715
theorem B2613181 : Blo 479788 2613181 := bstep (se 3 (by rfl) ⟨489971, by rfl⟩ : syracuseStep 2613181 = 979943) B979943
theorem B483295 : Blo 479788 483295 := bstep (se 1 (by rfl) ⟨362471, by rfl⟩ : syracuseStep 483295 = 724943) B724943
theorem B483559 : Blo 479788 483559 := bstep (se 1 (by rfl) ⟨362669, by rfl⟩ : syracuseStep 483559 = 725339) B725339
theorem B2941265 : Blo 479788 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B1630583 : Blo 479788 1630583 := bstep (se 1 (by rfl) ⟨1222937, by rfl⟩ : syracuseStep 1630583 = 2445875) B2445875
theorem B483711 : Blo 479788 483711 := bstep (se 1 (by rfl) ⟨362783, by rfl⟩ : syracuseStep 483711 = 725567) B725567
theorem B7791011 : Blo 479788 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B811471 : Blo 479788 811471 := bstep (se 1 (by rfl) ⟨608603, by rfl⟩ : syracuseStep 811471 = 1217207) B1217207
theorem B7037725 : Blo 479788 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B812207 : Blo 479788 812207 := bstep (se 1 (by rfl) ⟨609155, by rfl⟩ : syracuseStep 812207 = 1218311) B1218311
theorem B812443 : Blo 479788 812443 := bstep (se 1 (by rfl) ⟨609332, by rfl⟩ : syracuseStep 812443 = 1218665) B1218665
theorem B1828271 : Blo 479788 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B1631663 : Blo 479788 1631663 := bstep (se 1 (by rfl) ⟨1223747, by rfl⟩ : syracuseStep 1631663 = 2447495) B2447495
theorem B1664509 : Blo 479788 1664509 := bstep (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) B624191
theorem B812767 : Blo 479788 812767 := bstep (se 1 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 812767 = 1219151) B1219151
theorem B1632041 : Blo 479788 1632041 := bstep (se 2 (by rfl) ⟨612015, by rfl⟩ : syracuseStep 1632041 = 1224031) B1224031
theorem B813199 : Blo 479788 813199 := bstep (se 1 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 813199 = 1219799) B1219799
theorem B2058635 : Blo 479788 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B23685605 : Blo 479788 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B2779643 : Blo 479788 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B4123385 : Blo 479788 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B814151 : Blo 479788 814151 := bstep (se 1 (by rfl) ⟨610613, by rfl⟩ : syracuseStep 814151 = 1221227) B1221227
theorem B2059607 : Blo 479788 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B814583 : Blo 479788 814583 := bstep (se 1 (by rfl) ⟨610937, by rfl⟩ : syracuseStep 814583 = 1221875) B1221875
theorem B2060275 : Blo 479788 2060275 := bstep (se 1 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 2060275 = 3090413) B3090413
theorem B5501033 : Blo 479788 5501033 := bstep (se 2 (by rfl) ⟨2062887, by rfl⟩ : syracuseStep 5501033 = 4125775) B4125775
theorem B3076289 : Blo 479788 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B2060599 : Blo 479788 2060599 := bstep (se 1 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 2060599 = 3090899) B3090899
theorem B815609 : Blo 479788 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B815879 : Blo 479788 815879 := bstep (se 1 (by rfl) ⟨611909, by rfl⟩ : syracuseStep 815879 = 1223819) B1223819
theorem B881455 : Blo 479788 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B915617 : Blo 479788 915617 := bstep (se 2 (by rfl) ⟨343356, by rfl⟩ : syracuseStep 915617 = 686713) B686713
theorem B1079675 : Blo 479788 1079675 := bstep (se 1 (by rfl) ⟨809756, by rfl⟩ : syracuseStep 1079675 = 1619513) B1619513
theorem B32143979 : Blo 479788 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B1079945 : Blo 479788 1079945 := bstep (se 2 (by rfl) ⟨404979, by rfl⟩ : syracuseStep 1079945 = 809959) B809959
theorem B5503949 : Blo 479788 5503949 := bstep (se 3 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 5503949 = 2063981) B2063981
theorem B4127759 : Blo 479788 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B687151 : Blo 479788 687151 := bstep (se 1 (by rfl) ⟨515363, by rfl⟩ : syracuseStep 687151 = 1030727) B1030727
theorem B719993 : Blo 479788 719993 := bstep (se 2 (by rfl) ⟨269997, by rfl⟩ : syracuseStep 719993 = 539995) B539995
theorem B1080503 : Blo 479788 1080503 := bstep (se 1 (by rfl) ⟨810377, by rfl⟩ : syracuseStep 1080503 = 1620755) B1620755
theorem B720095 : Blo 479788 720095 := bstep (se 1 (by rfl) ⟨540071, by rfl⟩ : syracuseStep 720095 = 1080143) B1080143
theorem B3079417 : Blo 479788 3079417 := bstep (se 2 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 3079417 = 2309563) B2309563
theorem B720137 : Blo 479788 720137 := bstep (se 2 (by rfl) ⟨270051, by rfl⟩ : syracuseStep 720137 = 540103) B540103
theorem B720239 : Blo 479788 720239 := bstep (se 1 (by rfl) ⟨540179, by rfl⟩ : syracuseStep 720239 = 1080359) B1080359
theorem B720359 : Blo 479788 720359 := bstep (se 1 (by rfl) ⟨540269, by rfl⟩ : syracuseStep 720359 = 1080539) B1080539
theorem B720491 : Blo 479788 720491 := bstep (se 1 (by rfl) ⟨540368, by rfl⟩ : syracuseStep 720491 = 1080737) B1080737
theorem B720617 : Blo 479788 720617 := bstep (se 2 (by rfl) ⟨270231, by rfl⟩ : syracuseStep 720617 = 540463) B540463
theorem B1081079 : Blo 479788 1081079 := bstep (se 1 (by rfl) ⟨810809, by rfl⟩ : syracuseStep 1081079 = 1621619) B1621619
theorem B687943 : Blo 479788 687943 := bstep (se 1 (by rfl) ⟨515957, by rfl⟩ : syracuseStep 687943 = 1031915) B1031915
theorem B5013335 : Blo 479788 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B720761 : Blo 479788 720761 := bstep (se 2 (by rfl) ⟨270285, by rfl⟩ : syracuseStep 720761 = 540571) B540571
theorem B1081259 : Blo 479788 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B720863 : Blo 479788 720863 := bstep (se 1 (by rfl) ⟨540647, by rfl⟩ : syracuseStep 720863 = 1081295) B1081295
theorem B1376443 : Blo 479788 1376443 := bstep (se 1 (by rfl) ⟨1032332, by rfl⟩ : syracuseStep 1376443 = 2064665) B2064665
theorem B721199 : Blo 479788 721199 := bstep (se 1 (by rfl) ⟨540899, by rfl⟩ : syracuseStep 721199 = 1081799) B1081799
theorem B1081727 : Blo 479788 1081727 := bstep (se 1 (by rfl) ⟨811295, by rfl⟩ : syracuseStep 1081727 = 1622591) B1622591
theorem B917887 : Blo 479788 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B11862443 : Blo 479788 11862443 := bstep (se 1 (by rfl) ⟨8896832, by rfl⟩ : syracuseStep 11862443 = 17793665) B17793665
theorem B721439 : Blo 479788 721439 := bstep (se 1 (by rfl) ⟨541079, by rfl⟩ : syracuseStep 721439 = 1082159) B1082159
theorem B918047 : Blo 479788 918047 := bstep (se 1 (by rfl) ⟨688535, by rfl⟩ : syracuseStep 918047 = 1377071) B1377071
theorem B8258111 : Blo 479788 8258111 := bstep (se 1 (by rfl) ⟨6193583, by rfl⟩ : syracuseStep 8258111 = 12387167) B12387167
theorem B1081961 : Blo 479788 1081961 := bstep (se 2 (by rfl) ⟨405735, by rfl⟩ : syracuseStep 1081961 = 811471) B811471
theorem B2065007 : Blo 479788 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B722111 : Blo 479788 722111 := bstep (se 1 (by rfl) ⟨541583, by rfl⟩ : syracuseStep 722111 = 1083167) B1083167
theorem B1082591 : Blo 479788 1082591 := bstep (se 1 (by rfl) ⟨811943, by rfl⟩ : syracuseStep 1082591 = 1623887) B1623887
theorem B722255 : Blo 479788 722255 := bstep (se 1 (by rfl) ⟨541691, by rfl⟩ : syracuseStep 722255 = 1083383) B1083383
theorem B722345 : Blo 479788 722345 := bstep (se 2 (by rfl) ⟨270879, by rfl⟩ : syracuseStep 722345 = 541759) B541759
theorem B1082807 : Blo 479788 1082807 := bstep (se 1 (by rfl) ⟨812105, by rfl⟩ : syracuseStep 1082807 = 1624211) B1624211
theorem B722495 : Blo 479788 722495 := bstep (se 1 (by rfl) ⟨541871, by rfl⟩ : syracuseStep 722495 = 1083743) B1083743
theorem B722537 : Blo 479788 722537 := bstep (se 2 (by rfl) ⟨270951, by rfl⟩ : syracuseStep 722537 = 541903) B541903
theorem B1082987 : Blo 479788 1082987 := bstep (se 1 (by rfl) ⟨812240, by rfl⟩ : syracuseStep 1082987 = 1624481) B1624481
theorem B1083257 : Blo 479788 1083257 := bstep (se 2 (by rfl) ⟨406221, by rfl⟩ : syracuseStep 1083257 = 812443) B812443
theorem B1542169 : Blo 479788 1542169 := bstep (se 2 (by rfl) ⟨578313, by rfl⟩ : syracuseStep 1542169 = 1156627) B1156627
theorem B722975 : Blo 479788 722975 := bstep (se 1 (by rfl) ⟨542231, by rfl⟩ : syracuseStep 722975 = 1084463) B1084463
theorem B6948989 : Blo 479788 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B723167 : Blo 479788 723167 := bstep (se 1 (by rfl) ⟨542375, by rfl⟩ : syracuseStep 723167 = 1084751) B1084751
theorem B1214747 : Blo 479788 1214747 := bstep (se 1 (by rfl) ⟨911060, by rfl⟩ : syracuseStep 1214747 = 1822121) B1822121
theorem B723227 : Blo 479788 723227 := bstep (se 1 (by rfl) ⟨542420, by rfl⟩ : syracuseStep 723227 = 1084841) B1084841
theorem B1083689 : Blo 479788 1083689 := bstep (se 2 (by rfl) ⟨406383, by rfl⟩ : syracuseStep 1083689 = 812767) B812767
theorem B2755073 : Blo 479788 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B1215071 : Blo 479788 1215071 := bstep (se 1 (by rfl) ⟨911303, by rfl⟩ : syracuseStep 1215071 = 1822607) B1822607
theorem B723551 : Blo 479788 723551 := bstep (se 1 (by rfl) ⟨542663, by rfl⟩ : syracuseStep 723551 = 1085327) B1085327
theorem B2755255 : Blo 479788 2755255 := bstep (se 1 (by rfl) ⟨2066441, by rfl⟩ : syracuseStep 2755255 = 4132883) B4132883
theorem B1084265 : Blo 479788 1084265 := bstep (se 2 (by rfl) ⟨406599, by rfl⟩ : syracuseStep 1084265 = 813199) B813199
theorem B723833 : Blo 479788 723833 := bstep (se 2 (by rfl) ⟨271437, by rfl⟩ : syracuseStep 723833 = 542875) B542875
theorem B1084319 : Blo 479788 1084319 := bstep (se 1 (by rfl) ⟨813239, by rfl⟩ : syracuseStep 1084319 = 1626479) B1626479
theorem B723881 : Blo 479788 723881 := bstep (se 2 (by rfl) ⟨271455, by rfl⟩ : syracuseStep 723881 = 542911) B542911
theorem B724031 : Blo 479788 724031 := bstep (se 1 (by rfl) ⟨543023, by rfl⟩ : syracuseStep 724031 = 1086047) B1086047
theorem B1739987 : Blo 479788 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B724583 : Blo 479788 724583 := bstep (se 1 (by rfl) ⟨543437, by rfl⟩ : syracuseStep 724583 = 1086875) B1086875
theorem B10554995 : Blo 479788 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B1085255 : Blo 479788 1085255 := bstep (se 1 (by rfl) ⟨813941, by rfl⟩ : syracuseStep 1085255 = 1627883) B1627883
theorem B724967 : Blo 479788 724967 := bstep (se 1 (by rfl) ⟨543725, by rfl⟩ : syracuseStep 724967 = 1087451) B1087451
theorem B1085435 : Blo 479788 1085435 := bstep (se 1 (by rfl) ⟨814076, by rfl⟩ : syracuseStep 1085435 = 1628153) B1628153
theorem B725087 : Blo 479788 725087 := bstep (se 1 (by rfl) ⟨543815, by rfl⟩ : syracuseStep 725087 = 1087631) B1087631
theorem B1085543 : Blo 479788 1085543 := bstep (se 1 (by rfl) ⟨814157, by rfl⟩ : syracuseStep 1085543 = 1628315) B1628315
theorem B725099 : Blo 479788 725099 := bstep (se 1 (by rfl) ⟨543824, by rfl⟩ : syracuseStep 725099 = 1087649) B1087649
theorem B725147 : Blo 479788 725147 := bstep (se 1 (by rfl) ⟨543860, by rfl⟩ : syracuseStep 725147 = 1087721) B1087721
theorem B1085615 : Blo 479788 1085615 := bstep (se 1 (by rfl) ⟨814211, by rfl⟩ : syracuseStep 1085615 = 1628423) B1628423
theorem B2429513 : Blo 479788 2429513 := bstep (se 2 (by rfl) ⟨911067, by rfl⟩ : syracuseStep 2429513 = 1822135) B1822135
theorem B1086299 : Blo 479788 1086299 := bstep (se 1 (by rfl) ⟨814724, by rfl⟩ : syracuseStep 1086299 = 1629449) B1629449
theorem B2233327 : Blo 479788 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B6919577 : Blo 479788 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B1087055 : Blo 479788 1087055 := bstep (se 1 (by rfl) ⟨815291, by rfl⟩ : syracuseStep 1087055 = 1630583) B1630583
theorem B7837721 : Blo 479788 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B1218847 : Blo 479788 1218847 := bstep (se 1 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 1218847 = 1828271) B1828271
theorem B1087775 : Blo 479788 1087775 := bstep (se 1 (by rfl) ⟨815831, by rfl⟩ : syracuseStep 1087775 = 1631663) B1631663
theorem B3086849 : Blo 479788 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B1088027 : Blo 479788 1088027 := bstep (se 1 (by rfl) ⟨816020, by rfl⟩ : syracuseStep 1088027 = 1632041) B1632041
theorem B7412381 : Blo 479788 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B7413059 : Blo 479788 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B2203193 : Blo 479788 2203193 := bstep (se 2 (by rfl) ⟨826197, by rfl⟩ : syracuseStep 2203193 = 1652395) B1652395
theorem B2433239 : Blo 479788 2433239 := bstep (se 1 (by rfl) ⟨1824929, by rfl⟩ : syracuseStep 2433239 = 3649859) B3649859
theorem B9904841 : Blo 479788 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B6169391 : Blo 479788 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B4105889 : Blo 479788 4105889 := bstep (se 2 (by rfl) ⟨1539708, by rfl⟩ : syracuseStep 4105889 = 3079417) B3079417
theorem B731035 : Blo 479788 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B927679 : Blo 479788 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B3484241 : Blo 479788 3484241 := bstep (se 2 (by rfl) ⟨1306590, by rfl⟩ : syracuseStep 3484241 = 2613181) B2613181
theorem B136719197 : Blo 479788 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B2337767 : Blo 479788 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B601499 : Blo 479788 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B1158799 : Blo 479788 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B1224335 : Blo 479788 1224335 := bstep (se 1 (by rfl) ⟨918251, by rfl⟩ : syracuseStep 1224335 = 1836503) B1836503
theorem B5222033 : Blo 479788 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B2436803 : Blo 479788 2436803 := bstep (se 1 (by rfl) ⟨1827602, by rfl⟩ : syracuseStep 2436803 = 3655205) B3655205
theorem B9383633 : Blo 479788 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B3650345 : Blo 479788 3650345 := bstep (se 2 (by rfl) ⟨1368879, by rfl⟩ : syracuseStep 3650345 = 2737759) B2737759
theorem B1160443 : Blo 479788 1160443 := bstep (se 1 (by rfl) ⟨870332, by rfl⟩ : syracuseStep 1160443 = 1740665) B1740665
theorem B1619837 : Blo 479788 1619837 := bstep (se 3 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 1619837 = 607439) B607439
theorem B4110263 : Blo 479788 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B1620107 : Blo 479788 1620107 := bstep (se 1 (by rfl) ⟨1215080, by rfl⟩ : syracuseStep 1620107 = 2430161) B2430161
theorem B1947883 : Blo 479788 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B1621025 : Blo 479788 1621025 := bstep (se 2 (by rfl) ⟨607884, by rfl⟩ : syracuseStep 1621025 = 1215769) B1215769
theorem B2636999 : Blo 479788 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B1031393 : Blo 479788 1031393 := bstep (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) B773545
theorem B4963751 : Blo 479788 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B1621727 : Blo 479788 1621727 := bstep (se 1 (by rfl) ⟨1216295, by rfl⟩ : syracuseStep 1621727 = 2432591) B2432591
theorem B7126751 : Blo 479788 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B540391 : Blo 479788 540391 := bstep (se 1 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 540391 = 810587) B810587
theorem B5194007 : Blo 479788 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B1622429 : Blo 479788 1622429 := bstep (se 3 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 1622429 = 608411) B608411
theorem B3293597 : Blo 479788 3293597 := bstep (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) B1235099
theorem B6177181 : Blo 479788 6177181 := bstep (se 3 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 6177181 = 2316443) B2316443
theorem B2736827 : Blo 479788 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B541471 : Blo 479788 541471 := bstep (se 1 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 541471 = 812207) B812207
theorem B2474819 : Blo 479788 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B3523945 : Blo 479788 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B2737577 : Blo 479788 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B1558187 : Blo 479788 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B542767 : Blo 479788 542767 := bstep (se 1 (by rfl) ⟨407075, by rfl⟩ : syracuseStep 542767 = 814151) B814151
theorem B543055 : Blo 479788 543055 := bstep (se 1 (by rfl) ⟨407291, by rfl⟩ : syracuseStep 543055 = 814583) B814583
theorem B1624427 : Blo 479788 1624427 := bstep (se 1 (by rfl) ⟨1218320, by rfl⟩ : syracuseStep 1624427 = 2436641) B2436641
theorem B1624697 : Blo 479788 1624697 := bstep (se 2 (by rfl) ⟨609261, by rfl⟩ : syracuseStep 1624697 = 1218523) B1218523
theorem B2050859 : Blo 479788 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B2739035 : Blo 479788 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B4115387 : Blo 479788 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B543739 : Blo 479788 543739 := bstep (se 1 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 543739 = 815609) B815609
theorem B543919 : Blo 479788 543919 := bstep (se 1 (by rfl) ⟨407939, by rfl⟩ : syracuseStep 543919 = 815879) B815879
theorem B3296801 : Blo 479788 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B5492285 : Blo 479788 5492285 := bstep (se 3 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 5492285 = 2059607) B2059607
theorem B12374045 : Blo 479788 12374045 := bstep (se 3 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 12374045 = 4640267) B4640267
theorem B6934567 : Blo 479788 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B610411 : Blo 479788 610411 := bstep (se 1 (by rfl) ⟨457808, by rfl⟩ : syracuseStep 610411 = 915617) B915617
theorem B1822895 : Blo 479788 1822895 := bstep (se 1 (by rfl) ⟨1367171, by rfl⟩ : syracuseStep 1822895 = 2734343) B2734343
theorem B1954145 : Blo 479788 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B1102391 : Blo 479788 1102391 := bstep (se 1 (by rfl) ⟨826793, by rfl⟩ : syracuseStep 1102391 = 1653587) B1653587
theorem B479995 : Blo 479788 479995 := bstep (se 1 (by rfl) ⟨359996, by rfl⟩ : syracuseStep 479995 = 719993) B719993
theorem B480063 : Blo 479788 480063 := bstep (se 1 (by rfl) ⟨360047, by rfl⟩ : syracuseStep 480063 = 720095) B720095
theorem B480091 : Blo 479788 480091 := bstep (se 1 (by rfl) ⟨360068, by rfl⟩ : syracuseStep 480091 = 720137) B720137
theorem B1823579 : Blo 479788 1823579 := bstep (se 1 (by rfl) ⟨1367684, by rfl⟩ : syracuseStep 1823579 = 2735369) B2735369
theorem B1823593 : Blo 479788 1823593 := bstep (se 2 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 1823593 = 1367695) B1367695
theorem B3658607 : Blo 479788 3658607 := bstep (se 1 (by rfl) ⟨2743955, by rfl⟩ : syracuseStep 3658607 = 5487911) B5487911
theorem B480159 : Blo 479788 480159 := bstep (se 1 (by rfl) ⟨360119, by rfl⟩ : syracuseStep 480159 = 720239) B720239
theorem B906209 : Blo 479788 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B480239 : Blo 479788 480239 := bstep (se 1 (by rfl) ⟨360179, by rfl⟩ : syracuseStep 480239 = 720359) B720359
theorem B480327 : Blo 479788 480327 := bstep (se 1 (by rfl) ⟨360245, by rfl⟩ : syracuseStep 480327 = 720491) B720491
theorem B1823867 : Blo 479788 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B480411 : Blo 479788 480411 := bstep (se 1 (by rfl) ⟨360308, by rfl⟩ : syracuseStep 480411 = 720617) B720617
theorem B480507 : Blo 479788 480507 := bstep (se 1 (by rfl) ⟨360380, by rfl⟩ : syracuseStep 480507 = 720761) B720761
theorem B480575 : Blo 479788 480575 := bstep (se 1 (by rfl) ⟨360431, by rfl⟩ : syracuseStep 480575 = 720863) B720863
theorem B4117985 : Blo 479788 4117985 := bstep (se 2 (by rfl) ⟨1544244, by rfl⟩ : syracuseStep 4117985 = 3088489) B3088489
theorem B480743 : Blo 479788 480743 := bstep (se 1 (by rfl) ⟨360557, by rfl⟩ : syracuseStep 480743 = 721115) B721115
theorem B480751 : Blo 479788 480751 := bstep (se 1 (by rfl) ⟨360563, by rfl⟩ : syracuseStep 480751 = 721127) B721127
theorem B480859 : Blo 479788 480859 := bstep (se 1 (by rfl) ⟨360644, by rfl⟩ : syracuseStep 480859 = 721289) B721289
theorem B480923 : Blo 479788 480923 := bstep (se 1 (by rfl) ⟨360692, by rfl⟩ : syracuseStep 480923 = 721385) B721385
theorem B2053799 : Blo 479788 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B481007 : Blo 479788 481007 := bstep (se 1 (by rfl) ⟨360755, by rfl⟩ : syracuseStep 481007 = 721511) B721511
theorem B481095 : Blo 479788 481095 := bstep (se 1 (by rfl) ⟨360821, by rfl⟩ : syracuseStep 481095 = 721643) B721643
theorem B481115 : Blo 479788 481115 := bstep (se 1 (by rfl) ⟨360836, by rfl⟩ : syracuseStep 481115 = 721673) B721673
theorem B481183 : Blo 479788 481183 := bstep (se 1 (by rfl) ⟨360887, by rfl⟩ : syracuseStep 481183 = 721775) B721775
theorem B481351 : Blo 479788 481351 := bstep (se 1 (by rfl) ⟨361013, by rfl⟩ : syracuseStep 481351 = 722027) B722027
theorem B481511 : Blo 479788 481511 := bstep (se 1 (by rfl) ⟨361133, by rfl⟩ : syracuseStep 481511 = 722267) B722267
theorem B2054483 : Blo 479788 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B481695 : Blo 479788 481695 := bstep (se 1 (by rfl) ⟨361271, by rfl⟩ : syracuseStep 481695 = 722543) B722543
theorem B481743 : Blo 479788 481743 := bstep (se 1 (by rfl) ⟨361307, by rfl⟩ : syracuseStep 481743 = 722615) B722615
theorem B481767 : Blo 479788 481767 := bstep (se 1 (by rfl) ⟨361325, by rfl⟩ : syracuseStep 481767 = 722651) B722651
theorem B481883 : Blo 479788 481883 := bstep (se 1 (by rfl) ⟨361412, by rfl⟩ : syracuseStep 481883 = 722825) B722825
theorem B2447981 : Blo 479788 2447981 := bstep (se 3 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 2447981 = 917993) B917993
theorem B481951 : Blo 479788 481951 := bstep (se 1 (by rfl) ⟨361463, by rfl⟩ : syracuseStep 481951 = 722927) B722927
theorem B482119 : Blo 479788 482119 := bstep (se 1 (by rfl) ⟨361589, by rfl⟩ : syracuseStep 482119 = 723179) B723179
theorem B482159 : Blo 479788 482159 := bstep (se 1 (by rfl) ⟨361619, by rfl⟩ : syracuseStep 482159 = 723239) B723239
theorem B809851 : Blo 479788 809851 := bstep (se 1 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 809851 = 1214777) B1214777
theorem B482215 : Blo 479788 482215 := bstep (se 1 (by rfl) ⟨361661, by rfl⟩ : syracuseStep 482215 = 723323) B723323
theorem B482395 : Blo 479788 482395 := bstep (se 1 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 482395 = 723593) B723593
theorem B71326817 : Blo 479788 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B482511 : Blo 479788 482511 := bstep (se 1 (by rfl) ⟨361883, by rfl⟩ : syracuseStep 482511 = 723767) B723767
theorem B482535 : Blo 479788 482535 := bstep (se 1 (by rfl) ⟨361901, by rfl⟩ : syracuseStep 482535 = 723803) B723803
theorem B482631 : Blo 479788 482631 := bstep (se 1 (by rfl) ⟨361973, by rfl⟩ : syracuseStep 482631 = 723947) B723947
theorem B2219345 : Blo 479788 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B482767 : Blo 479788 482767 := bstep (se 1 (by rfl) ⟨362075, by rfl⟩ : syracuseStep 482767 = 724151) B724151
theorem B6610447 : Blo 479788 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B482927 : Blo 479788 482927 := bstep (se 1 (by rfl) ⟨362195, by rfl⟩ : syracuseStep 482927 = 724391) B724391
theorem B482983 : Blo 479788 482983 := bstep (se 1 (by rfl) ⟨362237, by rfl⟩ : syracuseStep 482983 = 724475) B724475
theorem B810715 : Blo 479788 810715 := bstep (se 1 (by rfl) ⟨608036, by rfl⟩ : syracuseStep 810715 = 1216073) B1216073
theorem B483047 : Blo 479788 483047 := bstep (se 1 (by rfl) ⟨362285, by rfl⟩ : syracuseStep 483047 = 724571) B724571
theorem B7397099 : Blo 479788 7397099 := bstep (se 1 (by rfl) ⟨5547824, by rfl⟩ : syracuseStep 7397099 = 11095649) B11095649
theorem B483103 : Blo 479788 483103 := bstep (se 1 (by rfl) ⟨362327, by rfl⟩ : syracuseStep 483103 = 724655) B724655
theorem B483183 : Blo 479788 483183 := bstep (se 1 (by rfl) ⟨362387, by rfl⟩ : syracuseStep 483183 = 724775) B724775
theorem B4611973 : Blo 479788 4611973 := bstep (se 4 (by rfl) ⟨432372, by rfl⟩ : syracuseStep 4611973 = 864745) B864745
theorem B483239 : Blo 479788 483239 := bstep (se 1 (by rfl) ⟨362429, by rfl⟩ : syracuseStep 483239 = 724859) B724859
theorem B810985 : Blo 479788 810985 := bstep (se 2 (by rfl) ⟨304119, by rfl⟩ : syracuseStep 810985 = 608239) B608239
theorem B2318483 : Blo 479788 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B483519 : Blo 479788 483519 := bstep (se 1 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 483519 = 725279) B725279
theorem B483535 : Blo 479788 483535 := bstep (se 1 (by rfl) ⟨362651, by rfl⟩ : syracuseStep 483535 = 725303) B725303
theorem B483583 : Blo 479788 483583 := bstep (se 1 (by rfl) ⟨362687, by rfl⟩ : syracuseStep 483583 = 725375) B725375
theorem B483631 : Blo 479788 483631 := bstep (se 1 (by rfl) ⟨362723, by rfl⟩ : syracuseStep 483631 = 725447) B725447
theorem B811687 : Blo 479788 811687 := bstep (se 1 (by rfl) ⟨608765, by rfl⟩ : syracuseStep 811687 = 1217531) B1217531
theorem B4121401 : Blo 479788 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B2057147 : Blo 479788 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B812011 : Blo 479788 812011 := bstep (se 1 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 812011 = 1218017) B1218017
theorem B812153 : Blo 479788 812153 := bstep (se 2 (by rfl) ⟨304557, by rfl⟩ : syracuseStep 812153 = 609115) B609115
theorem B1205561 : Blo 479788 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B2319673 : Blo 479788 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B1631771 : Blo 479788 1631771 := bstep (se 1 (by rfl) ⟨1223828, by rfl⟩ : syracuseStep 1631771 = 2447657) B2447657
theorem B5203693 : Blo 479788 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B911387 : Blo 479788 911387 := bstep (se 1 (by rfl) ⟨683540, by rfl⟩ : syracuseStep 911387 = 1367081) B1367081
theorem B813449 : Blo 479788 813449 := bstep (se 2 (by rfl) ⟨305043, by rfl⟩ : syracuseStep 813449 = 610087) B610087
theorem B2058857 : Blo 479788 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B2747033 : Blo 479788 2747033 := bstep (se 2 (by rfl) ⟨1030137, by rfl⟩ : syracuseStep 2747033 = 2060275) B2060275
theorem B1960843 : Blo 479788 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B2747465 : Blo 479788 2747465 := bstep (se 2 (by rfl) ⟨1030299, by rfl⟩ : syracuseStep 2747465 = 2060599) B2060599
theorem B1175273 : Blo 479788 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B15658829 : Blo 479788 15658829 := bstep (se 3 (by rfl) ⟨2936030, by rfl⟩ : syracuseStep 15658829 = 5872061) B5872061
theorem B815177 : Blo 479788 815177 := bstep (se 2 (by rfl) ⟨305691, by rfl⟩ : syracuseStep 815177 = 611383) B611383
theorem B815231 : Blo 479788 815231 := bstep (se 1 (by rfl) ⟨611423, by rfl⟩ : syracuseStep 815231 = 1222847) B1222847
theorem B1372423 : Blo 479788 1372423 := bstep (se 1 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 1372423 = 2058635) B2058635
theorem B15790403 : Blo 479788 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B2748923 : Blo 479788 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B2323039 : Blo 479788 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B816169 : Blo 479788 816169 := bstep (se 2 (by rfl) ⟨306063, by rfl⟩ : syracuseStep 816169 = 612127) B612127
theorem B816311 : Blo 479788 816311 := bstep (se 1 (by rfl) ⟨612233, by rfl⟩ : syracuseStep 816311 = 1224467) B1224467
theorem B2061521 : Blo 479788 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B3667355 : Blo 479788 3667355 := bstep (se 1 (by rfl) ⟨2750516, by rfl⟩ : syracuseStep 3667355 = 5501033) B5501033
theorem B2062547 : Blo 479788 2062547 := bstep (se 1 (by rfl) ⟨1546910, by rfl⟩ : syracuseStep 2062547 = 3093821) B3093821
theorem B1079531 : Blo 479788 1079531 := bstep (se 1 (by rfl) ⟨809648, by rfl⟩ : syracuseStep 1079531 = 1619297) B1619297
theorem B916201 : Blo 479788 916201 := bstep (se 2 (by rfl) ⟨343575, by rfl⟩ : syracuseStep 916201 = 687151) B687151
theorem B1374985 : Blo 479788 1374985 := bstep (se 2 (by rfl) ⟨515619, by rfl⟩ : syracuseStep 1374985 = 1031239) B1031239
theorem B719783 : Blo 479788 719783 := bstep (se 1 (by rfl) ⟨539837, by rfl⟩ : syracuseStep 719783 = 1079675) B1079675
theorem B21429319 : Blo 479788 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B4684877 : Blo 479788 4684877 := bstep (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) B1756829
theorem B719963 : Blo 479788 719963 := bstep (se 1 (by rfl) ⟨539972, by rfl⟩ : syracuseStep 719963 = 1079945) B1079945
theorem B3669299 : Blo 479788 3669299 := bstep (se 1 (by rfl) ⟨2751974, by rfl⟩ : syracuseStep 3669299 = 5503949) B5503949
theorem B2751839 : Blo 479788 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B720335 : Blo 479788 720335 := bstep (se 1 (by rfl) ⟨540251, by rfl⟩ : syracuseStep 720335 = 1080503) B1080503
theorem B1080827 : Blo 479788 1080827 := bstep (se 1 (by rfl) ⟨810620, by rfl⟩ : syracuseStep 1080827 = 1621241) B1621241
theorem B2752157 : Blo 479788 2752157 := bstep (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) B1032059
theorem B1081007 : Blo 479788 1081007 := bstep (se 1 (by rfl) ⟨810755, by rfl⟩ : syracuseStep 1081007 = 1621511) B1621511
theorem B1081097 : Blo 479788 1081097 := bstep (se 2 (by rfl) ⟨405411, by rfl⟩ : syracuseStep 1081097 = 810823) B810823
theorem B917257 : Blo 479788 917257 := bstep (se 2 (by rfl) ⟨343971, by rfl⟩ : syracuseStep 917257 = 687943) B687943
theorem B720719 : Blo 479788 720719 := bstep (se 1 (by rfl) ⟨540539, by rfl⟩ : syracuseStep 720719 = 1081079) B1081079
theorem B3342223 : Blo 479788 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B720839 : Blo 479788 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B1835257 : Blo 479788 1835257 := bstep (se 2 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 1835257 = 1376443) B1376443
theorem B721151 : Blo 479788 721151 := bstep (se 1 (by rfl) ⟨540863, by rfl⟩ : syracuseStep 721151 = 1081727) B1081727
theorem B1081619 : Blo 479788 1081619 := bstep (se 1 (by rfl) ⟨811214, by rfl⟩ : syracuseStep 1081619 = 1622429) B1622429
theorem B2195731 : Blo 479788 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B5505407 : Blo 479788 5505407 := bstep (se 1 (by rfl) ⟨4129055, by rfl⟩ : syracuseStep 5505407 = 8258111) B8258111
theorem B721307 : Blo 479788 721307 := bstep (se 1 (by rfl) ⟨540980, by rfl⟩ : syracuseStep 721307 = 1081961) B1081961
theorem B1376671 : Blo 479788 1376671 := bstep (se 1 (by rfl) ⟨1032503, by rfl⟩ : syracuseStep 1376671 = 2065007) B2065007
theorem B721727 : Blo 479788 721727 := bstep (se 1 (by rfl) ⟨541295, by rfl⟩ : syracuseStep 721727 = 1082591) B1082591
theorem B1082249 : Blo 479788 1082249 := bstep (se 2 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 1082249 = 811687) B811687
theorem B5211053 : Blo 479788 5211053 := bstep (se 3 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 5211053 = 1954145) B1954145
theorem B721871 : Blo 479788 721871 := bstep (se 1 (by rfl) ⟨541403, by rfl⟩ : syracuseStep 721871 = 1082807) B1082807
theorem B721961 : Blo 479788 721961 := bstep (se 2 (by rfl) ⟨270735, by rfl⟩ : syracuseStep 721961 = 541471) B541471
theorem B721991 : Blo 479788 721991 := bstep (se 1 (by rfl) ⟨541493, by rfl⟩ : syracuseStep 721991 = 1082987) B1082987
theorem B722171 : Blo 479788 722171 := bstep (se 1 (by rfl) ⟨541628, by rfl⟩ : syracuseStep 722171 = 1083257) B1083257
theorem B1082681 : Blo 479788 1082681 := bstep (se 2 (by rfl) ⟨406005, by rfl⟩ : syracuseStep 1082681 = 812011) B812011
theorem B722459 : Blo 479788 722459 := bstep (se 1 (by rfl) ⟨541844, by rfl⟩ : syracuseStep 722459 = 1083689) B1083689
theorem B1082951 : Blo 479788 1082951 := bstep (se 1 (by rfl) ⟨812213, by rfl⟩ : syracuseStep 1082951 = 1624427) B1624427
theorem B1836715 : Blo 479788 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B1083131 : Blo 479788 1083131 := bstep (se 1 (by rfl) ⟨812348, by rfl⟩ : syracuseStep 1083131 = 1624697) B1624697
theorem B722843 : Blo 479788 722843 := bstep (se 1 (by rfl) ⟨542132, by rfl⟩ : syracuseStep 722843 = 1084265) B1084265
theorem B722879 : Blo 479788 722879 := bstep (se 1 (by rfl) ⟨542159, by rfl⟩ : syracuseStep 722879 = 1084319) B1084319
theorem B2197867 : Blo 479788 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B723503 : Blo 479788 723503 := bstep (se 1 (by rfl) ⟨542627, by rfl⟩ : syracuseStep 723503 = 1085255) B1085255
theorem B723623 : Blo 479788 723623 := bstep (se 1 (by rfl) ⟨542717, by rfl⟩ : syracuseStep 723623 = 1085435) B1085435
theorem B723689 : Blo 479788 723689 := bstep (se 2 (by rfl) ⟨271383, by rfl⟩ : syracuseStep 723689 = 542767) B542767
theorem B723695 : Blo 479788 723695 := bstep (se 1 (by rfl) ⟨542771, by rfl⟩ : syracuseStep 723695 = 1085543) B1085543
theorem B1215263 : Blo 479788 1215263 := bstep (se 1 (by rfl) ⟨911447, by rfl⟩ : syracuseStep 1215263 = 1822895) B1822895
theorem B723743 : Blo 479788 723743 := bstep (se 1 (by rfl) ⟨542807, by rfl⟩ : syracuseStep 723743 = 1085615) B1085615
theorem B724073 : Blo 479788 724073 := bstep (se 2 (by rfl) ⟨271527, by rfl⟩ : syracuseStep 724073 = 543055) B543055
theorem B1215719 : Blo 479788 1215719 := bstep (se 1 (by rfl) ⟨911789, by rfl⟩ : syracuseStep 1215719 = 1823579) B1823579
theorem B724199 : Blo 479788 724199 := bstep (se 1 (by rfl) ⟨543149, by rfl⟩ : syracuseStep 724199 = 1086299) B1086299
theorem B1215911 : Blo 479788 1215911 := bstep (se 1 (by rfl) ⟨911933, by rfl⟩ : syracuseStep 1215911 = 1823867) B1823867
theorem B3214829 : Blo 479788 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B3673673 : Blo 479788 3673673 := bstep (se 2 (by rfl) ⟨1377627, by rfl⟩ : syracuseStep 3673673 = 2755255) B2755255
theorem B724703 : Blo 479788 724703 := bstep (se 1 (by rfl) ⟨543527, by rfl⟩ : syracuseStep 724703 = 1087055) B1087055
theorem B724985 : Blo 479788 724985 := bstep (se 2 (by rfl) ⟨271869, by rfl⟩ : syracuseStep 724985 = 543739) B543739
theorem B725183 : Blo 479788 725183 := bstep (se 1 (by rfl) ⟨543887, by rfl⟩ : syracuseStep 725183 = 1087775) B1087775
theorem B725225 : Blo 479788 725225 := bstep (se 2 (by rfl) ⟨271959, by rfl⟩ : syracuseStep 725225 = 543919) B543919
theorem B725351 : Blo 479788 725351 := bstep (se 1 (by rfl) ⟨544013, by rfl⟩ : syracuseStep 725351 = 1088027) B1088027
theorem B47551211 : Blo 479788 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B1545065 : Blo 479788 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B1479563 : Blo 479788 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B9246089 : Blo 479788 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B1545655 : Blo 479788 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B1087847 : Blo 479788 1087847 := bstep (se 1 (by rfl) ⟨815885, by rfl⟩ : syracuseStep 1087847 = 1631771) B1631771
theorem B2431457 : Blo 479788 2431457 := bstep (se 2 (by rfl) ⟨911796, by rfl⟩ : syracuseStep 2431457 = 1823593) B1823593
theorem B1088225 : Blo 479788 1088225 := bstep (se 2 (by rfl) ⟨408084, by rfl⟩ : syracuseStep 1088225 = 816169) B816169
theorem B1547257 : Blo 479788 1547257 := bstep (se 2 (by rfl) ⟨580221, by rfl⟩ : syracuseStep 1547257 = 1160443) B1160443
theorem B3481355 : Blo 479788 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B10526935 : Blo 479788 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B2597177 : Blo 479788 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B2433563 : Blo 479788 2433563 := bstep (se 1 (by rfl) ⟨1825172, by rfl⟩ : syracuseStep 2433563 = 3650345) B3650345
theorem B19768157 : Blo 479788 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B1221601 : Blo 479788 1221601 := bstep (se 2 (by rfl) ⟨458100, by rfl⟩ : syracuseStep 1221601 = 916201) B916201
theorem B3123251 : Blo 479788 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B1223009 : Blo 479788 1223009 := bstep (se 2 (by rfl) ⟨458628, by rfl⟩ : syracuseStep 1223009 = 917257) B917257
theorem B7908295 : Blo 479788 7908295 := bstep (se 1 (by rfl) ⟨5931221, by rfl⟩ : syracuseStep 7908295 = 11862443) B11862443
theorem B1223849 : Blo 479788 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B8236241 : Blo 479788 8236241 := bstep (se 2 (by rfl) ⟨3088590, by rfl⟩ : syracuseStep 8236241 = 6177181) B6177181
theorem B1649879 : Blo 479788 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B4632659 : Blo 479788 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B3092897 : Blo 479788 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B4698593 : Blo 479788 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B1159991 : Blo 479788 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B734927 : Blo 479788 734927 := bstep (se 1 (by rfl) ⟨551195, by rfl⟩ : syracuseStep 734927 = 1102391) B1102391
theorem B1619675 : Blo 479788 1619675 := bstep (se 1 (by rfl) ⟨1214756, by rfl⟩ : syracuseStep 1619675 = 2429513) B2429513
theorem B2439071 : Blo 479788 2439071 := bstep (se 1 (by rfl) ⟨1829303, by rfl⟩ : syracuseStep 2439071 = 3658607) B3658607
theorem B604139 : Blo 479788 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B5225147 : Blo 479788 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B4931399 : Blo 479788 4931399 := bstep (se 1 (by rfl) ⟨3698549, by rfl⟩ : syracuseStep 4931399 = 7397099) B7397099
theorem B1622159 : Blo 479788 1622159 := bstep (se 1 (by rfl) ⟨1216619, by rfl⟩ : syracuseStep 1622159 = 2433239) B2433239
theorem B6603227 : Blo 479788 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B4112927 : Blo 479788 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B541435 : Blo 479788 541435 := bstep (se 1 (by rfl) ⟨406076, by rfl⟩ : syracuseStep 541435 = 812153) B812153
theorem B3097385 : Blo 479788 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B2737259 : Blo 479788 2737259 := bstep (se 1 (by rfl) ⟨2052944, by rfl⟩ : syracuseStep 2737259 = 4105889) B4105889
theorem B607591 : Blo 479788 607591 := bstep (se 1 (by rfl) ⟨455693, by rfl⟩ : syracuseStep 607591 = 911387) B911387
theorem B542299 : Blo 479788 542299 := bstep (se 1 (by rfl) ⟨406724, by rfl⟩ : syracuseStep 542299 = 813449) B813449
theorem B91146131 : Blo 479788 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B1558511 : Blo 479788 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B1624535 : Blo 479788 1624535 := bstep (se 1 (by rfl) ⟨1218401, by rfl⟩ : syracuseStep 1624535 = 2436803) B2436803
theorem B10439219 : Blo 479788 10439219 := bstep (se 1 (by rfl) ⟨7829414, by rfl⟩ : syracuseStep 10439219 = 15658829) B15658829
theorem B543451 : Blo 479788 543451 := bstep (se 1 (by rfl) ⟨407588, by rfl⟩ : syracuseStep 543451 = 815177) B815177
theorem B543487 : Blo 479788 543487 := bstep (se 1 (by rfl) ⟨407615, by rfl⟩ : syracuseStep 543487 = 815231) B815231
theorem B1625129 : Blo 479788 1625129 := bstep (se 2 (by rfl) ⟨609423, by rfl⟩ : syracuseStep 1625129 = 1218847) B1218847
theorem B544207 : Blo 479788 544207 := bstep (se 1 (by rfl) ⟨408155, by rfl⟩ : syracuseStep 544207 = 816311) B816311
theorem B2444903 : Blo 479788 2444903 := bstep (se 1 (by rfl) ⟨1833677, by rfl⟩ : syracuseStep 2444903 = 3667355) B3667355
theorem B2740175 : Blo 479788 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B479855 : Blo 479788 479855 := bstep (se 1 (by rfl) ⟨359891, by rfl⟩ : syracuseStep 479855 = 719783) B719783
theorem B479975 : Blo 479788 479975 := bstep (se 1 (by rfl) ⟨359981, by rfl⟩ : syracuseStep 479975 = 719963) B719963
theorem B1757999 : Blo 479788 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B2446199 : Blo 479788 2446199 := bstep (se 1 (by rfl) ⟨1834649, by rfl⟩ : syracuseStep 2446199 = 3669299) B3669299
theorem B480223 : Blo 479788 480223 := bstep (se 1 (by rfl) ⟨360167, by rfl⟩ : syracuseStep 480223 = 720335) B720335
theorem B6149297 : Blo 479788 6149297 := bstep (se 2 (by rfl) ⟨2305986, by rfl⟩ : syracuseStep 6149297 = 4611973) B4611973
theorem B480479 : Blo 479788 480479 := bstep (se 1 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 480479 = 720719) B720719
theorem B480559 : Blo 479788 480559 := bstep (se 1 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 480559 = 720839) B720839
theorem B3462671 : Blo 479788 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B480799 : Blo 479788 480799 := bstep (se 1 (by rfl) ⟨360599, by rfl⟩ : syracuseStep 480799 = 721199) B721199
theorem B480959 : Blo 479788 480959 := bstep (se 1 (by rfl) ⟨360719, by rfl⟩ : syracuseStep 480959 = 721439) B721439
theorem B612031 : Blo 479788 612031 := bstep (se 1 (by rfl) ⟨459023, by rfl⟩ : syracuseStep 612031 = 918047) B918047
theorem B1824551 : Blo 479788 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B481407 : Blo 479788 481407 := bstep (se 1 (by rfl) ⟨361055, by rfl⟩ : syracuseStep 481407 = 722111) B722111
theorem B481503 : Blo 479788 481503 := bstep (se 1 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 481503 = 722255) B722255
theorem B1825051 : Blo 479788 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B481563 : Blo 479788 481563 := bstep (se 1 (by rfl) ⟨361172, by rfl⟩ : syracuseStep 481563 = 722345) B722345
theorem B481663 : Blo 479788 481663 := bstep (se 1 (by rfl) ⟨361247, by rfl⟩ : syracuseStep 481663 = 722495) B722495
theorem B481691 : Blo 479788 481691 := bstep (se 1 (by rfl) ⟨361268, by rfl⟩ : syracuseStep 481691 = 722537) B722537
theorem B5495201 : Blo 479788 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B1038791 : Blo 479788 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B481983 : Blo 479788 481983 := bstep (se 1 (by rfl) ⟨361487, by rfl⟩ : syracuseStep 481983 = 722975) B722975
theorem B482111 : Blo 479788 482111 := bstep (se 1 (by rfl) ⟨361583, by rfl⟩ : syracuseStep 482111 = 723167) B723167
theorem B809831 : Blo 479788 809831 := bstep (se 1 (by rfl) ⟨607373, by rfl⟩ : syracuseStep 809831 = 1214747) B1214747
theorem B482151 : Blo 479788 482151 := bstep (se 1 (by rfl) ⟨361613, by rfl⟩ : syracuseStep 482151 = 723227) B723227
theorem B810047 : Blo 479788 810047 := bstep (se 1 (by rfl) ⟨607535, by rfl⟩ : syracuseStep 810047 = 1215071) B1215071
theorem B482367 : Blo 479788 482367 := bstep (se 1 (by rfl) ⟨361775, by rfl⟩ : syracuseStep 482367 = 723551) B723551
theorem B1826023 : Blo 479788 1826023 := bstep (se 1 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 1826023 = 2739035) B2739035
theorem B482555 : Blo 479788 482555 := bstep (se 1 (by rfl) ⟨361916, by rfl⟩ : syracuseStep 482555 = 723833) B723833
theorem B482587 : Blo 479788 482587 := bstep (se 1 (by rfl) ⟨361940, by rfl⟩ : syracuseStep 482587 = 723881) B723881
theorem B2743591 : Blo 479788 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B482687 : Blo 479788 482687 := bstep (se 1 (by rfl) ⟨362015, by rfl⟩ : syracuseStep 482687 = 724031) B724031
theorem B3661523 : Blo 479788 3661523 := bstep (se 1 (by rfl) ⟨2746142, by rfl⟩ : syracuseStep 3661523 = 5492285) B5492285
theorem B483055 : Blo 479788 483055 := bstep (se 1 (by rfl) ⟨362291, by rfl⟩ : syracuseStep 483055 = 724583) B724583
theorem B1236905 : Blo 479788 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B483311 : Blo 479788 483311 := bstep (se 1 (by rfl) ⟨362483, by rfl⟩ : syracuseStep 483311 = 724967) B724967
theorem B8249363 : Blo 479788 8249363 := bstep (se 1 (by rfl) ⟨6187022, by rfl⟩ : syracuseStep 8249363 = 12374045) B12374045
theorem B2056225 : Blo 479788 2056225 := bstep (se 2 (by rfl) ⟨771084, by rfl⟩ : syracuseStep 2056225 = 1542169) B1542169
theorem B483391 : Blo 479788 483391 := bstep (se 1 (by rfl) ⟨362543, by rfl⟩ : syracuseStep 483391 = 725087) B725087
theorem B483399 : Blo 479788 483399 := bstep (se 1 (by rfl) ⟨362549, by rfl⟩ : syracuseStep 483399 = 725099) B725099
theorem B483431 : Blo 479788 483431 := bstep (se 1 (by rfl) ⟨362573, by rfl⟩ : syracuseStep 483431 = 725147) B725147
theorem B4613051 : Blo 479788 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B2745323 : Blo 479788 2745323 := bstep (se 1 (by rfl) ⟨2058992, by rfl⟩ : syracuseStep 2745323 = 4117985) B4117985
theorem B1369199 : Blo 479788 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B2614457 : Blo 479788 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B1369655 : Blo 479788 1369655 := bstep (se 1 (by rfl) ⟨1027241, by rfl⟩ : syracuseStep 1369655 = 2054483) B2054483
theorem B2057899 : Blo 479788 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B1631987 : Blo 479788 1631987 := bstep (se 1 (by rfl) ⟨1223990, by rfl⟩ : syracuseStep 1631987 = 2447981) B2447981
theorem B4941587 : Blo 479788 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B1468795 : Blo 479788 1468795 := bstep (se 1 (by rfl) ⟨1101596, by rfl⟩ : syracuseStep 1468795 = 2203193) B2203193
theorem B813881 : Blo 479788 813881 := bstep (se 2 (by rfl) ⟨305205, by rfl⟩ : syracuseStep 813881 = 610411) B610411
theorem B1829897 : Blo 479788 1829897 := bstep (se 2 (by rfl) ⟨686211, by rfl⟩ : syracuseStep 1829897 = 1372423) B1372423
theorem B1371431 : Blo 479788 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B2977769 : Blo 479788 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B2322827 : Blo 479788 2322827 := bstep (se 1 (by rfl) ⟨1742120, by rfl⟩ : syracuseStep 2322827 = 3484241) B3484241
theorem B1372571 : Blo 479788 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B1831355 : Blo 479788 1831355 := bstep (se 1 (by rfl) ⟨1373516, by rfl⟩ : syracuseStep 1831355 = 2747033) B2747033
theorem B1831643 : Blo 479788 1831643 := bstep (se 1 (by rfl) ⟨1373732, by rfl⟩ : syracuseStep 1831643 = 2747465) B2747465
theorem B5468957 : Blo 479788 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B816223 : Blo 479788 816223 := bstep (se 1 (by rfl) ⟨612167, by rfl⟩ : syracuseStep 816223 = 1224335) B1224335
theorem B6255755 : Blo 479788 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B783515 : Blo 479788 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B1832615 : Blo 479788 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B2750381 : Blo 479788 2750381 := bstep (se 3 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 2750381 = 1031393) B1031393
theorem B1374347 : Blo 479788 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B1833313 : Blo 479788 1833313 := bstep (se 2 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 1833313 = 1374985) B1374985
theorem B1603997 : Blo 479788 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B1079801 : Blo 479788 1079801 := bstep (se 2 (by rfl) ⟨404925, by rfl⟩ : syracuseStep 1079801 = 809851) B809851
theorem B27753029 : Blo 479788 27753029 := bstep (se 4 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 27753029 = 5203693) B5203693
theorem B1079891 : Blo 479788 1079891 := bstep (se 1 (by rfl) ⟨809918, by rfl⟩ : syracuseStep 1079891 = 1619837) B1619837
theorem B1080071 : Blo 479788 1080071 := bstep (se 1 (by rfl) ⟨810053, by rfl⟩ : syracuseStep 1080071 = 1620107) B1620107
theorem B28572425 : Blo 479788 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B1375031 : Blo 479788 1375031 := bstep (se 1 (by rfl) ⟨1031273, by rfl⟩ : syracuseStep 1375031 = 2062547) B2062547
theorem B719687 : Blo 479788 719687 := bstep (se 1 (by rfl) ⟨539765, by rfl⟩ : syracuseStep 719687 = 1079531) B1079531
theorem B28146653 : Blo 479788 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B19004669 : Blo 479788 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B8813929 : Blo 479788 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B1080683 : Blo 479788 1080683 := bstep (se 1 (by rfl) ⟨810512, by rfl⟩ : syracuseStep 1080683 = 1621025) B1621025
theorem B3898853 : Blo 479788 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B1834559 : Blo 479788 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B3309167 : Blo 479788 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B1080953 : Blo 479788 1080953 := bstep (se 2 (by rfl) ⟨405357, by rfl⟩ : syracuseStep 1080953 = 810715) B810715
theorem B720521 : Blo 479788 720521 := bstep (se 2 (by rfl) ⟨270195, by rfl⟩ : syracuseStep 720521 = 540391) B540391
theorem B720551 : Blo 479788 720551 := bstep (se 1 (by rfl) ⟨540413, by rfl⟩ : syracuseStep 720551 = 1080827) B1080827
theorem B1834771 : Blo 479788 1834771 := bstep (se 1 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 1834771 = 2752157) B2752157
theorem B720671 : Blo 479788 720671 := bstep (se 1 (by rfl) ⟨540503, by rfl⟩ : syracuseStep 720671 = 1081007) B1081007
theorem B1081151 : Blo 479788 1081151 := bstep (se 1 (by rfl) ⟨810863, by rfl⟩ : syracuseStep 1081151 = 1621727) B1621727
theorem B720731 : Blo 479788 720731 := bstep (se 1 (by rfl) ⟨540548, by rfl⟩ : syracuseStep 720731 = 1081097) B1081097
theorem B4456297 : Blo 479788 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B1081313 : Blo 479788 1081313 := bstep (se 2 (by rfl) ⟨405492, by rfl⟩ : syracuseStep 1081313 = 810985) B810985
theorem B1081439 : Blo 479788 1081439 := bstep (se 1 (by rfl) ⟨811079, by rfl⟩ : syracuseStep 1081439 = 1622159) B1622159
theorem B721079 : Blo 479788 721079 := bstep (se 1 (by rfl) ⟨540809, by rfl⟩ : syracuseStep 721079 = 1081619) B1081619
theorem B3670271 : Blo 479788 3670271 := bstep (se 1 (by rfl) ⟨2752703, by rfl⟩ : syracuseStep 3670271 = 5505407) B5505407
theorem B2064923 : Blo 479788 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B1835561 : Blo 479788 1835561 := bstep (se 2 (by rfl) ⟨688335, by rfl⟩ : syracuseStep 1835561 = 1376671) B1376671
theorem B721499 : Blo 479788 721499 := bstep (se 1 (by rfl) ⟨541124, by rfl⟩ : syracuseStep 721499 = 1082249) B1082249
theorem B3474035 : Blo 479788 3474035 := bstep (se 1 (by rfl) ⟨2605526, by rfl⟩ : syracuseStep 3474035 = 5211053) B5211053
theorem B721787 : Blo 479788 721787 := bstep (se 1 (by rfl) ⟨541340, by rfl⟩ : syracuseStep 721787 = 1082681) B1082681
theorem B721913 : Blo 479788 721913 := bstep (se 2 (by rfl) ⟨270717, by rfl⟩ : syracuseStep 721913 = 541435) B541435
theorem B721967 : Blo 479788 721967 := bstep (se 1 (by rfl) ⟨541475, by rfl⟩ : syracuseStep 721967 = 1082951) B1082951
theorem B722087 : Blo 479788 722087 := bstep (se 1 (by rfl) ⟨541565, by rfl⟩ : syracuseStep 722087 = 1083131) B1083131
theorem B1083023 : Blo 479788 1083023 := bstep (se 1 (by rfl) ⟨812267, by rfl⟩ : syracuseStep 1083023 = 1624535) B1624535
theorem B1083419 : Blo 479788 1083419 := bstep (se 1 (by rfl) ⟨812564, by rfl⟩ : syracuseStep 1083419 = 1625129) B1625129
theorem B723065 : Blo 479788 723065 := bstep (se 2 (by rfl) ⟨271149, by rfl⟩ : syracuseStep 723065 = 542299) B542299
theorem B986375 : Blo 479788 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B4099531 : Blo 479788 4099531 := bstep (se 1 (by rfl) ⟨3074648, by rfl⟩ : syracuseStep 4099531 = 6149297) B6149297
theorem B6164059 : Blo 479788 6164059 := bstep (se 1 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 6164059 = 9246089) B9246089
theorem B724601 : Blo 479788 724601 := bstep (se 2 (by rfl) ⟨271725, by rfl⟩ : syracuseStep 724601 = 543451) B543451
theorem B724649 : Blo 479788 724649 := bstep (se 2 (by rfl) ⟨271743, by rfl⟩ : syracuseStep 724649 = 543487) B543487
theorem B1216367 : Blo 479788 1216367 := bstep (se 1 (by rfl) ⟨912275, by rfl⟩ : syracuseStep 1216367 = 1824551) B1824551
theorem B725231 : Blo 479788 725231 := bstep (se 1 (by rfl) ⟨543923, by rfl⟩ : syracuseStep 725231 = 1087847) B1087847
theorem B725483 : Blo 479788 725483 := bstep (se 1 (by rfl) ⟨544112, by rfl⟩ : syracuseStep 725483 = 1088225) B1088225
theorem B725609 : Blo 479788 725609 := bstep (se 2 (by rfl) ⟨272103, by rfl⟩ : syracuseStep 725609 = 544207) B544207
theorem B13177565 : Blo 479788 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B824603 : Blo 479788 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B1611037 : Blo 479788 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B13178771 : Blo 479788 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B1742971 : Blo 479788 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B1087991 : Blo 479788 1087991 := bstep (se 1 (by rfl) ⟨815993, by rfl⟩ : syracuseStep 1087991 = 1631987) B1631987
theorem B1088297 : Blo 479788 1088297 := bstep (se 2 (by rfl) ⟨408111, by rfl⟩ : syracuseStep 1088297 = 816223) B816223
theorem B1219931 : Blo 479788 1219931 := bstep (se 1 (by rfl) ⟨914948, by rfl⟩ : syracuseStep 1219931 = 1829897) B1829897
theorem B3088439 : Blo 479788 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B1548551 : Blo 479788 1548551 := bstep (se 1 (by rfl) ⟨1161413, by rfl⟩ : syracuseStep 1548551 = 2322827) B2322827
theorem B1220903 : Blo 479788 1220903 := bstep (se 1 (by rfl) ⟨915677, by rfl⟩ : syracuseStep 1220903 = 1831355) B1831355
theorem B2433401 : Blo 479788 2433401 := bstep (se 2 (by rfl) ⟨912525, by rfl⟩ : syracuseStep 2433401 = 1825051) B1825051
theorem B1221095 : Blo 479788 1221095 := bstep (se 1 (by rfl) ⟨915821, by rfl⟩ : syracuseStep 1221095 = 1831643) B1831643
theorem B3645971 : Blo 479788 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B4170503 : Blo 479788 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B1221743 : Blo 479788 1221743 := bstep (se 1 (by rfl) ⟨916307, by rfl⟩ : syracuseStep 1221743 = 1832615) B1832615
theorem B2434697 : Blo 479788 2434697 := bstep (se 2 (by rfl) ⟨913011, by rfl⟩ : syracuseStep 2434697 = 1826023) B1826023
theorem B3483431 : Blo 479788 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B19048283 : Blo 479788 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B13150397 : Blo 479788 13150397 := bstep (se 3 (by rfl) ⟨2465699, by rfl⟩ : syracuseStep 13150397 = 4931399) B4931399
theorem B2599235 : Blo 479788 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B1223039 : Blo 479788 1223039 := bstep (se 1 (by rfl) ⟨917279, by rfl⟩ : syracuseStep 1223039 = 1834559) B1834559
theorem B2206111 : Blo 479788 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B5941729 : Blo 479788 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B7940717 : Blo 479788 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B14035913 : Blo 479788 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B4402151 : Blo 479788 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B60764087 : Blo 479788 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B11710565 : Blo 479788 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B6959479 : Blo 479788 6959479 := bstep (se 1 (by rfl) ⟨5219609, by rfl⟩ : syracuseStep 6959479 = 10439219) B10439219
theorem B2143219 : Blo 479788 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B2930489 : Blo 479788 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B31700807 : Blo 479788 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B1030043 : Blo 479788 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B2308447 : Blo 479788 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B1620971 : Blo 479788 1620971 := bstep (se 1 (by rfl) ⟨1215728, by rfl⟩ : syracuseStep 1620971 = 2431457) B2431457
theorem B539887 : Blo 479788 539887 := bstep (se 1 (by rfl) ⟨404915, by rfl⟩ : syracuseStep 539887 = 809831) B809831
theorem B540031 : Blo 479788 540031 := bstep (se 1 (by rfl) ⟨405023, by rfl⟩ : syracuseStep 540031 = 810047) B810047
theorem B2441015 : Blo 479788 2441015 := bstep (se 1 (by rfl) ⟨1830761, by rfl⟩ : syracuseStep 2441015 = 3661523) B3661523
theorem B1622375 : Blo 479788 1622375 := bstep (se 1 (by rfl) ⟨1216781, by rfl⟩ : syracuseStep 1622375 = 2433563) B2433563
theorem B2770109 : Blo 479788 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B2082167 : Blo 479788 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B542587 : Blo 479788 542587 := bstep (se 1 (by rfl) ⟨406940, by rfl⟩ : syracuseStep 542587 = 813881) B813881
theorem B5490827 : Blo 479788 5490827 := bstep (se 1 (by rfl) ⟨4118120, by rfl⟩ : syracuseStep 5490827 = 8236241) B8236241
theorem B1099919 : Blo 479788 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B3132395 : Blo 479788 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B2444417 : Blo 479788 2444417 := bstep (se 2 (by rfl) ⟨916656, by rfl⟩ : syracuseStep 2444417 = 1833313) B1833313
theorem B773327 : Blo 479788 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B3657149 : Blo 479788 3657149 := bstep (se 3 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 3657149 = 1371431) B1371431
theorem B1626047 : Blo 479788 1626047 := bstep (se 1 (by rfl) ⟨1219535, by rfl⟩ : syracuseStep 1626047 = 2439071) B2439071
theorem B1069331 : Blo 479788 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B18502019 : Blo 479788 18502019 := bstep (se 1 (by rfl) ⟨13876514, by rfl⟩ : syracuseStep 18502019 = 27753029) B27753029
theorem B3658121 : Blo 479788 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B11751905 : Blo 479788 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B479791 : Blo 479788 479791 := bstep (se 1 (by rfl) ⟨359843, by rfl⟩ : syracuseStep 479791 = 719687) B719687
theorem B18764435 : Blo 479788 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B12669779 : Blo 479788 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B2446361 : Blo 479788 2446361 := bstep (se 2 (by rfl) ⟨917385, by rfl⟩ : syracuseStep 2446361 = 1834771) B1834771
theorem B480347 : Blo 479788 480347 := bstep (se 1 (by rfl) ⟨360260, by rfl⟩ : syracuseStep 480347 = 720521) B720521
theorem B480367 : Blo 479788 480367 := bstep (se 1 (by rfl) ⟨360275, by rfl⟩ : syracuseStep 480367 = 720551) B720551
theorem B480447 : Blo 479788 480447 := bstep (se 1 (by rfl) ⟨360335, by rfl⟩ : syracuseStep 480447 = 720671) B720671
theorem B480487 : Blo 479788 480487 := bstep (se 1 (by rfl) ⟨360365, by rfl⟩ : syracuseStep 480487 = 720731) B720731
theorem B2741633 : Blo 479788 2741633 := bstep (se 2 (by rfl) ⟨1028112, by rfl⟩ : syracuseStep 2741633 = 2056225) B2056225
theorem B480767 : Blo 479788 480767 := bstep (se 1 (by rfl) ⟨360575, by rfl⟩ : syracuseStep 480767 = 721151) B721151
theorem B480871 : Blo 479788 480871 := bstep (se 1 (by rfl) ⟨360653, by rfl⟩ : syracuseStep 480871 = 721307) B721307
theorem B2447009 : Blo 479788 2447009 := bstep (se 2 (by rfl) ⟨917628, by rfl⟩ : syracuseStep 2447009 = 1835257) B1835257
theorem B2741951 : Blo 479788 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B481151 : Blo 479788 481151 := bstep (se 1 (by rfl) ⟨360863, by rfl⟩ : syracuseStep 481151 = 721727) B721727
theorem B481247 : Blo 479788 481247 := bstep (se 1 (by rfl) ⟨360935, by rfl⟩ : syracuseStep 481247 = 721871) B721871
theorem B481307 : Blo 479788 481307 := bstep (se 1 (by rfl) ⟨360980, by rfl⟩ : syracuseStep 481307 = 721961) B721961
theorem B481327 : Blo 479788 481327 := bstep (se 1 (by rfl) ⟨360995, by rfl⟩ : syracuseStep 481327 = 721991) B721991
theorem B1824839 : Blo 479788 1824839 := bstep (se 1 (by rfl) ⟨1368629, by rfl⟩ : syracuseStep 1824839 = 2737259) B2737259
theorem B481447 : Blo 479788 481447 := bstep (se 1 (by rfl) ⟨361085, by rfl⟩ : syracuseStep 481447 = 722171) B722171
theorem B481639 : Blo 479788 481639 := bstep (se 1 (by rfl) ⟨361229, by rfl⟩ : syracuseStep 481639 = 722459) B722459
theorem B481895 : Blo 479788 481895 := bstep (se 1 (by rfl) ⟨361421, by rfl⟩ : syracuseStep 481895 = 722843) B722843
theorem B481919 : Blo 479788 481919 := bstep (se 1 (by rfl) ⟨361439, by rfl⟩ : syracuseStep 481919 = 722879) B722879
theorem B1628801 : Blo 479788 1628801 := bstep (se 2 (by rfl) ⟨610800, by rfl⟩ : syracuseStep 1628801 = 1221601) B1221601
theorem B1039007 : Blo 479788 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B482335 : Blo 479788 482335 := bstep (se 1 (by rfl) ⟨361751, by rfl⟩ : syracuseStep 482335 = 723503) B723503
theorem B482415 : Blo 479788 482415 := bstep (se 1 (by rfl) ⟨361811, by rfl⟩ : syracuseStep 482415 = 723623) B723623
theorem B810121 : Blo 479788 810121 := bstep (se 2 (by rfl) ⟨303795, by rfl⟩ : syracuseStep 810121 = 607591) B607591
theorem B482459 : Blo 479788 482459 := bstep (se 1 (by rfl) ⟨361844, by rfl⟩ : syracuseStep 482459 = 723689) B723689
theorem B482463 : Blo 479788 482463 := bstep (se 1 (by rfl) ⟨361847, by rfl⟩ : syracuseStep 482463 = 723695) B723695
theorem B810175 : Blo 479788 810175 := bstep (se 1 (by rfl) ⟨607631, by rfl⟩ : syracuseStep 810175 = 1215263) B1215263
theorem B482495 : Blo 479788 482495 := bstep (se 1 (by rfl) ⟨361871, by rfl⟩ : syracuseStep 482495 = 723743) B723743
theorem B482715 : Blo 479788 482715 := bstep (se 1 (by rfl) ⟨362036, by rfl⟩ : syracuseStep 482715 = 724073) B724073
theorem B810479 : Blo 479788 810479 := bstep (se 1 (by rfl) ⟨607859, by rfl⟩ : syracuseStep 810479 = 1215719) B1215719
theorem B482799 : Blo 479788 482799 := bstep (se 1 (by rfl) ⟨362099, by rfl⟩ : syracuseStep 482799 = 724199) B724199
theorem B2743865 : Blo 479788 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B2448953 : Blo 479788 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B810607 : Blo 479788 810607 := bstep (se 1 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 810607 = 1215911) B1215911
theorem B2449115 : Blo 479788 2449115 := bstep (se 1 (by rfl) ⟨1836836, by rfl⟩ : syracuseStep 2449115 = 3673673) B3673673
theorem B1629935 : Blo 479788 1629935 := bstep (se 1 (by rfl) ⟨1222451, by rfl⟩ : syracuseStep 1629935 = 2444903) B2444903
theorem B483135 : Blo 479788 483135 := bstep (se 1 (by rfl) ⟨362351, by rfl⟩ : syracuseStep 483135 = 724703) B724703
theorem B1826783 : Blo 479788 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B483323 : Blo 479788 483323 := bstep (se 1 (by rfl) ⟨362492, by rfl⟩ : syracuseStep 483323 = 724985) B724985
theorem B483455 : Blo 479788 483455 := bstep (se 1 (by rfl) ⟨362591, by rfl⟩ : syracuseStep 483455 = 725183) B725183
theorem B483483 : Blo 479788 483483 := bstep (se 1 (by rfl) ⟨362612, by rfl⟩ : syracuseStep 483483 = 725225) B725225
theorem B483567 : Blo 479788 483567 := bstep (se 1 (by rfl) ⟨362675, by rfl⟩ : syracuseStep 483567 = 725351) B725351
theorem B1958393 : Blo 479788 1958393 := bstep (se 2 (by rfl) ⟨734397, by rfl⟩ : syracuseStep 1958393 = 1468795) B1468795
theorem B1171999 : Blo 479788 1171999 := bstep (se 1 (by rfl) ⟨878999, by rfl⟩ : syracuseStep 1171999 = 1757999) B1757999
theorem B1630799 : Blo 479788 1630799 := bstep (se 1 (by rfl) ⟨1223099, by rfl⟩ : syracuseStep 1630799 = 2446199) B2446199
theorem B10544393 : Blo 479788 10544393 := bstep (se 2 (by rfl) ⟨3954147, by rfl⟩ : syracuseStep 10544393 = 7908295) B7908295
theorem B3663467 : Blo 479788 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B1959805 : Blo 479788 1959805 := bstep (se 3 (by rfl) ⟨367463, by rfl⟩ : syracuseStep 1959805 = 734927) B734927
theorem B2320903 : Blo 479788 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B5499575 : Blo 479788 5499575 := bstep (se 1 (by rfl) ⟨4124681, by rfl⟩ : syracuseStep 5499575 = 8249363) B8249363
theorem B1731451 : Blo 479788 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B3664925 : Blo 479788 3664925 := bstep (se 3 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 3664925 = 1374347) B1374347
theorem B3075367 : Blo 479788 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B1830215 : Blo 479788 1830215 := bstep (se 1 (by rfl) ⟨1372661, by rfl⟩ : syracuseStep 1830215 = 2745323) B2745323
theorem B912799 : Blo 479788 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B913103 : Blo 479788 913103 := bstep (se 1 (by rfl) ⟨684827, by rfl⟩ : syracuseStep 913103 = 1369655) B1369655
theorem B815339 : Blo 479788 815339 := bstep (se 1 (by rfl) ⟨611504, by rfl⟩ : syracuseStep 815339 = 1223009) B1223009
theorem B2060873 : Blo 479788 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B815899 : Blo 479788 815899 := bstep (se 1 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 815899 = 1223849) B1223849
theorem B816041 : Blo 479788 816041 := bstep (se 2 (by rfl) ⟨306015, by rfl⟩ : syracuseStep 816041 = 612031) B612031
theorem B915047 : Blo 479788 915047 := bstep (se 1 (by rfl) ⟨686285, by rfl⟩ : syracuseStep 915047 = 1372571) B1372571
theorem B2061931 : Blo 479788 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B522343 : Blo 479788 522343 := bstep (se 1 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 522343 = 783515) B783515
theorem B1079783 : Blo 479788 1079783 := bstep (se 1 (by rfl) ⟨809837, by rfl⟩ : syracuseStep 1079783 = 1619675) B1619675
theorem B1833587 : Blo 479788 1833587 := bstep (se 1 (by rfl) ⟨1375190, by rfl⟩ : syracuseStep 1833587 = 2750381) B2750381
theorem B2063009 : Blo 479788 2063009 := bstep (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) B1547257
theorem B719867 : Blo 479788 719867 := bstep (se 1 (by rfl) ⟨539900, by rfl⟩ : syracuseStep 719867 = 1079801) B1079801
theorem B719927 : Blo 479788 719927 := bstep (se 1 (by rfl) ⟨539945, by rfl⟩ : syracuseStep 719927 = 1079891) B1079891
theorem B720047 : Blo 479788 720047 := bstep (se 1 (by rfl) ⟨540035, by rfl⟩ : syracuseStep 720047 = 1080071) B1080071
theorem B916687 : Blo 479788 916687 := bstep (se 1 (by rfl) ⟨687515, by rfl⟩ : syracuseStep 916687 = 1375031) B1375031
theorem B720455 : Blo 479788 720455 := bstep (se 1 (by rfl) ⟨540341, by rfl⟩ : syracuseStep 720455 = 1080683) B1080683
theorem B720635 : Blo 479788 720635 := bstep (se 1 (by rfl) ⟨540476, by rfl⟩ : syracuseStep 720635 = 1080953) B1080953
theorem B720767 : Blo 479788 720767 := bstep (se 1 (by rfl) ⟨540575, by rfl⟩ : syracuseStep 720767 = 1081151) B1081151
theorem B720875 : Blo 479788 720875 := bstep (se 1 (by rfl) ⟨540656, by rfl⟩ : syracuseStep 720875 = 1081313) B1081313
theorem B720959 : Blo 479788 720959 := bstep (se 1 (by rfl) ⟨540719, by rfl⟩ : syracuseStep 720959 = 1081439) B1081439
theorem B1081583 : Blo 479788 1081583 := bstep (se 1 (by rfl) ⟨811187, by rfl⟩ : syracuseStep 1081583 = 1622375) B1622375
theorem B1376615 : Blo 479788 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B2851549 : Blo 479788 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B722015 : Blo 479788 722015 := bstep (se 1 (by rfl) ⟨541511, by rfl⟩ : syracuseStep 722015 = 1083023) B1083023
theorem B722279 : Blo 479788 722279 := bstep (se 1 (by rfl) ⟨541709, by rfl⟩ : syracuseStep 722279 = 1083419) B1083419
theorem B723449 : Blo 479788 723449 := bstep (se 2 (by rfl) ⟨271293, by rfl⟩ : syracuseStep 723449 = 542587) B542587
theorem B1084031 : Blo 479788 1084031 := bstep (se 1 (by rfl) ⟨813023, by rfl⟩ : syracuseStep 1084031 = 1626047) B1626047
theorem B8785043 : Blo 479788 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B8785847 : Blo 479788 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B1216559 : Blo 479788 1216559 := bstep (se 1 (by rfl) ⟨912419, by rfl⟩ : syracuseStep 1216559 = 1824839) B1824839
theorem B725327 : Blo 479788 725327 := bstep (se 1 (by rfl) ⟨543995, by rfl⟩ : syracuseStep 725327 = 1087991) B1087991
theorem B4100489 : Blo 479788 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B1085867 : Blo 479788 1085867 := bstep (se 1 (by rfl) ⟨814400, by rfl⟩ : syracuseStep 1085867 = 1628801) B1628801
theorem B725531 : Blo 479788 725531 := bstep (se 1 (by rfl) ⟨544148, by rfl⟩ : syracuseStep 725531 = 1088297) B1088297
theorem B1217065 : Blo 479788 1217065 := bstep (se 2 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 1217065 = 912799) B912799
theorem B1086623 : Blo 479788 1086623 := bstep (se 1 (by rfl) ⟨814967, by rfl⟩ : syracuseStep 1086623 = 1629935) B1629935
theorem B1217855 : Blo 479788 1217855 := bstep (se 1 (by rfl) ⟨913391, by rfl⟩ : syracuseStep 1217855 = 1826783) B1826783
theorem B2430647 : Blo 479788 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B1087199 : Blo 479788 1087199 := bstep (se 1 (by rfl) ⟨815399, by rfl⟩ : syracuseStep 1087199 = 1630799) B1630799
theorem B9279305 : Blo 479788 9279305 := bstep (se 2 (by rfl) ⟨3479739, by rfl⟩ : syracuseStep 9279305 = 6959479) B6959479
theorem B35067725 : Blo 479788 35067725 := bstep (se 3 (by rfl) ⟨6575198, by rfl⟩ : syracuseStep 35067725 = 13150397) B13150397
theorem B1087865 : Blo 479788 1087865 := bstep (se 2 (by rfl) ⟨407949, by rfl⟩ : syracuseStep 1087865 = 815899) B815899
theorem B2857625 : Blo 479788 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B1220143 : Blo 479788 1220143 := bstep (se 1 (by rfl) ⟨915107, by rfl⟩ : syracuseStep 1220143 = 1830215) B1830215
theorem B40509391 : Blo 479788 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B7807043 : Blo 479788 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B696457 : Blo 479788 696457 := bstep (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) B522343
theorem B2630333 : Blo 479788 2630333 := bstep (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) B986375
theorem B1222249 : Blo 479788 1222249 := bstep (se 2 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 1222249 = 916687) B916687
theorem B1222391 : Blo 479788 1222391 := bstep (se 1 (by rfl) ⟨916793, by rfl⟩ : syracuseStep 1222391 = 1833587) B1833587
theorem B1223707 : Blo 479788 1223707 := bstep (se 1 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 1223707 = 1835561) B1835561
theorem B1846739 : Blo 479788 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B1388111 : Blo 479788 1388111 := bstep (se 1 (by rfl) ⟨1041083, by rfl⟩ : syracuseStep 1388111 = 2082167) B2082167
theorem B31338413 : Blo 479788 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B2438099 : Blo 479788 2438099 := bstep (se 1 (by rfl) ⟨1828574, by rfl⟩ : syracuseStep 2438099 = 3657149) B3657149
theorem B12334679 : Blo 479788 12334679 := bstep (se 1 (by rfl) ⟨9251009, by rfl⟩ : syracuseStep 12334679 = 18502019) B18502019
theorem B2438747 : Blo 479788 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B8795765 : Blo 479788 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B3094537 : Blo 479788 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B2308601 : Blo 479788 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B540319 : Blo 479788 540319 := bstep (se 1 (by rfl) ⟨405239, by rfl⟩ : syracuseStep 540319 = 810479) B810479
theorem B1032367 : Blo 479788 1032367 := bstep (se 1 (by rfl) ⟨774275, by rfl⟩ : syracuseStep 1032367 = 1548551) B1548551
theorem B1622267 : Blo 479788 1622267 := bstep (se 1 (by rfl) ⟨1216700, by rfl⟩ : syracuseStep 1622267 = 2433401) B2433401
theorem B2933117 : Blo 479788 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B7029595 : Blo 479788 7029595 := bstep (se 1 (by rfl) ⟨5272196, by rfl⟩ : syracuseStep 7029595 = 10544393) B10544393
theorem B2442311 : Blo 479788 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B1623131 : Blo 479788 1623131 := bstep (se 1 (by rfl) ⟨1217348, by rfl⟩ : syracuseStep 1623131 = 2434697) B2434697
theorem B12698855 : Blo 479788 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B2148049 : Blo 479788 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B5293811 : Blo 479788 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2770685 : Blo 479788 2770685 := bstep (se 3 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 2770685 = 1039007) B1039007
theorem B9357275 : Blo 479788 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B2934767 : Blo 479788 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B2443283 : Blo 479788 2443283 := bstep (se 1 (by rfl) ⟨1832462, by rfl⟩ : syracuseStep 2443283 = 3664925) B3664925
theorem B608735 : Blo 479788 608735 := bstep (se 1 (by rfl) ⟨456551, by rfl⟩ : syracuseStep 608735 = 913103) B913103
theorem B543559 : Blo 479788 543559 := bstep (se 1 (by rfl) ⟨407669, by rfl⟩ : syracuseStep 543559 = 815339) B815339
theorem B544027 : Blo 479788 544027 := bstep (se 1 (by rfl) ⟨408020, by rfl⟩ : syracuseStep 544027 = 816041) B816041
theorem B610031 : Blo 479788 610031 := bstep (se 1 (by rfl) ⟨457523, by rfl⟩ : syracuseStep 610031 = 915047) B915047
theorem B1953659 : Blo 479788 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B479911 : Blo 479788 479911 := bstep (se 1 (by rfl) ⟨359933, by rfl⟩ : syracuseStep 479911 = 719867) B719867
theorem B479951 : Blo 479788 479951 := bstep (se 1 (by rfl) ⟨359963, by rfl⟩ : syracuseStep 479951 = 719927) B719927
theorem B480031 : Blo 479788 480031 := bstep (se 1 (by rfl) ⟨360023, by rfl⟩ : syracuseStep 480031 = 720047) B720047
theorem B480303 : Blo 479788 480303 := bstep (se 1 (by rfl) ⟨360227, by rfl⟩ : syracuseStep 480303 = 720455) B720455
theorem B480423 : Blo 479788 480423 := bstep (se 1 (by rfl) ⟨360317, by rfl⟩ : syracuseStep 480423 = 720635) B720635
theorem B1627343 : Blo 479788 1627343 := bstep (se 1 (by rfl) ⟨1220507, by rfl⟩ : syracuseStep 1627343 = 2441015) B2441015
theorem B480511 : Blo 479788 480511 := bstep (se 1 (by rfl) ⟨360383, by rfl⟩ : syracuseStep 480511 = 720767) B720767
theorem B480583 : Blo 479788 480583 := bstep (se 1 (by rfl) ⟨360437, by rfl⟩ : syracuseStep 480583 = 720875) B720875
theorem B480719 : Blo 479788 480719 := bstep (se 1 (by rfl) ⟨360539, by rfl⟩ : syracuseStep 480719 = 721079) B721079
theorem B2446847 : Blo 479788 2446847 := bstep (se 1 (by rfl) ⟨1835135, by rfl⟩ : syracuseStep 2446847 = 3670271) B3670271
theorem B480999 : Blo 479788 480999 := bstep (se 1 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 480999 = 721499) B721499
theorem B2316023 : Blo 479788 2316023 := bstep (se 1 (by rfl) ⟨1737017, by rfl⟩ : syracuseStep 2316023 = 3474035) B3474035
theorem B481191 : Blo 479788 481191 := bstep (se 1 (by rfl) ⟨360893, by rfl⟩ : syracuseStep 481191 = 721787) B721787
theorem B481275 : Blo 479788 481275 := bstep (se 1 (by rfl) ⟨360956, by rfl⟩ : syracuseStep 481275 = 721913) B721913
theorem B481311 : Blo 479788 481311 := bstep (se 1 (by rfl) ⟨360983, by rfl⟩ : syracuseStep 481311 = 721967) B721967
theorem B481391 : Blo 479788 481391 := bstep (se 1 (by rfl) ⟨361043, by rfl⟩ : syracuseStep 481391 = 722087) B722087
theorem B482043 : Blo 479788 482043 := bstep (se 1 (by rfl) ⟨361532, by rfl⟩ : syracuseStep 482043 = 723065) B723065
theorem B3660551 : Blo 479788 3660551 := bstep (se 1 (by rfl) ⟨2745413, by rfl⟩ : syracuseStep 3660551 = 5490827) B5490827
theorem B2088263 : Blo 479788 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B1629611 : Blo 479788 1629611 := bstep (se 1 (by rfl) ⟨1222208, by rfl⟩ : syracuseStep 1629611 = 2444417) B2444417
theorem B483067 : Blo 479788 483067 := bstep (se 1 (by rfl) ⟨362300, by rfl⟩ : syracuseStep 483067 = 724601) B724601
theorem B483099 : Blo 479788 483099 := bstep (se 1 (by rfl) ⟨362324, by rfl⟩ : syracuseStep 483099 = 724649) B724649
theorem B2613073 : Blo 479788 2613073 := bstep (se 2 (by rfl) ⟨979902, by rfl⟩ : syracuseStep 2613073 = 1959805) B1959805
theorem B810911 : Blo 479788 810911 := bstep (se 1 (by rfl) ⟨608183, by rfl⟩ : syracuseStep 810911 = 1216367) B1216367
theorem B483487 : Blo 479788 483487 := bstep (se 1 (by rfl) ⟨362615, by rfl⟩ : syracuseStep 483487 = 725231) B725231
theorem B6250661 : Blo 479788 6250661 := bstep (se 4 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 6250661 = 1171999) B1171999
theorem B483655 : Blo 479788 483655 := bstep (se 1 (by rfl) ⟨362741, by rfl⟩ : syracuseStep 483655 = 725483) B725483
theorem B483739 : Blo 479788 483739 := bstep (se 1 (by rfl) ⟨362804, by rfl⟩ : syracuseStep 483739 = 725609) B725609
theorem B12509623 : Blo 479788 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B2941481 : Blo 479788 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B8446519 : Blo 479788 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B7922305 : Blo 479788 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B1630907 : Blo 479788 1630907 := bstep (se 1 (by rfl) ⟨1223180, by rfl⟩ : syracuseStep 1630907 = 2446361) B2446361
theorem B1827755 : Blo 479788 1827755 := bstep (se 1 (by rfl) ⟨1370816, by rfl⟩ : syracuseStep 1827755 = 2741633) B2741633
theorem B1631339 : Blo 479788 1631339 := bstep (se 1 (by rfl) ⟨1223504, by rfl⟩ : syracuseStep 1631339 = 2447009) B2447009
theorem B1827967 : Blo 479788 1827967 := bstep (se 1 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 1827967 = 2741951) B2741951
theorem B5466041 : Blo 479788 5466041 := bstep (se 2 (by rfl) ⟨2049765, by rfl⟩ : syracuseStep 5466041 = 4099531) B4099531
theorem B8218745 : Blo 479788 8218745 := bstep (se 2 (by rfl) ⟨3082029, by rfl⟩ : syracuseStep 8218745 = 6164059) B6164059
theorem B813287 : Blo 479788 813287 := bstep (se 1 (by rfl) ⟨609965, by rfl⟩ : syracuseStep 813287 = 1219931) B1219931
theorem B1829243 : Blo 479788 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B1632635 : Blo 479788 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B2746781 : Blo 479788 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B1632743 : Blo 479788 1632743 := bstep (se 1 (by rfl) ⟨1224557, by rfl⟩ : syracuseStep 1632743 = 2449115) B2449115
theorem B2058959 : Blo 479788 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B813935 : Blo 479788 813935 := bstep (se 1 (by rfl) ⟨610451, by rfl⟩ : syracuseStep 813935 = 1220903) B1220903
theorem B814063 : Blo 479788 814063 := bstep (se 1 (by rfl) ⟨610547, by rfl⟩ : syracuseStep 814063 = 1221095) B1221095
theorem B1305595 : Blo 479788 1305595 := bstep (se 1 (by rfl) ⟨979196, by rfl⟩ : syracuseStep 1305595 = 1958393) B1958393
theorem B2780335 : Blo 479788 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B814495 : Blo 479788 814495 := bstep (se 1 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 814495 = 1221743) B1221743
theorem B2322287 : Blo 479788 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B1732823 : Blo 479788 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B815359 : Blo 479788 815359 := bstep (se 1 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 815359 = 1223039) B1223039
theorem B3666383 : Blo 479788 3666383 := bstep (se 1 (by rfl) ⟨2749787, by rfl⟩ : syracuseStep 3666383 = 5499575) B5499575
theorem B2749241 : Blo 479788 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B2323961 : Blo 479788 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B1373915 : Blo 479788 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B3077929 : Blo 479788 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B2062205 : Blo 479788 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B21133871 : Blo 479788 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B1080161 : Blo 479788 1080161 := bstep (se 2 (by rfl) ⟨405060, by rfl⟩ : syracuseStep 1080161 = 810121) B810121
theorem B1080233 : Blo 479788 1080233 := bstep (se 2 (by rfl) ⟨405087, by rfl⟩ : syracuseStep 1080233 = 810175) B810175
theorem B719849 : Blo 479788 719849 := bstep (se 2 (by rfl) ⟨269943, by rfl⟩ : syracuseStep 719849 = 539887) B539887
theorem B719855 : Blo 479788 719855 := bstep (se 1 (by rfl) ⟨539891, by rfl⟩ : syracuseStep 719855 = 1079783) B1079783
theorem B1375339 : Blo 479788 1375339 := bstep (se 1 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 1375339 = 2063009) B2063009
theorem B720041 : Blo 479788 720041 := bstep (se 2 (by rfl) ⟨270015, by rfl⟩ : syracuseStep 720041 = 540031) B540031
theorem B1080647 : Blo 479788 1080647 := bstep (se 1 (by rfl) ⟨810485, by rfl⟩ : syracuseStep 1080647 = 1620971) B1620971
theorem B1080809 : Blo 479788 1080809 := bstep (se 2 (by rfl) ⟨405303, by rfl⟩ : syracuseStep 1080809 = 810607) B810607
theorem B721055 : Blo 479788 721055 := bstep (se 1 (by rfl) ⟨540791, by rfl⟩ : syracuseStep 721055 = 1081583) B1081583
theorem B1081511 : Blo 479788 1081511 := bstep (se 1 (by rfl) ⟨811133, by rfl⟩ : syracuseStep 1081511 = 1622267) B1622267
theorem B1376489 : Blo 479788 1376489 := bstep (se 2 (by rfl) ⟨516183, by rfl⟩ : syracuseStep 1376489 = 1032367) B1032367
theorem B917743 : Blo 479788 917743 := bstep (se 1 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 917743 = 1376615) B1376615
theorem B1082087 : Blo 479788 1082087 := bstep (se 1 (by rfl) ⟨811565, by rfl⟩ : syracuseStep 1082087 = 1623131) B1623131
theorem B722687 : Blo 479788 722687 := bstep (se 1 (by rfl) ⟨542015, by rfl⟩ : syracuseStep 722687 = 1084031) B1084031
theorem B66717989 : Blo 479788 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B723911 : Blo 479788 723911 := bstep (se 1 (by rfl) ⟨542933, by rfl⟩ : syracuseStep 723911 = 1085867) B1085867
theorem B724415 : Blo 479788 724415 := bstep (se 1 (by rfl) ⟨543311, by rfl⟩ : syracuseStep 724415 = 1086623) B1086623
theorem B1084895 : Blo 479788 1084895 := bstep (se 1 (by rfl) ⟨813671, by rfl⟩ : syracuseStep 1084895 = 1627343) B1627343
theorem B724745 : Blo 479788 724745 := bstep (se 2 (by rfl) ⟨271779, by rfl⟩ : syracuseStep 724745 = 543559) B543559
theorem B724799 : Blo 479788 724799 := bstep (se 1 (by rfl) ⟨543599, by rfl⟩ : syracuseStep 724799 = 1087199) B1087199
theorem B1544015 : Blo 479788 1544015 := bstep (se 1 (by rfl) ⟨1158011, by rfl⟩ : syracuseStep 1544015 = 2316023) B2316023
theorem B1085417 : Blo 479788 1085417 := bstep (se 2 (by rfl) ⟨407031, by rfl⟩ : syracuseStep 1085417 = 814063) B814063
theorem B1740793 : Blo 479788 1740793 := bstep (se 2 (by rfl) ⟨652797, by rfl⟩ : syracuseStep 1740793 = 1305595) B1305595
theorem B725243 : Blo 479788 725243 := bstep (se 1 (by rfl) ⟨543932, by rfl⟩ : syracuseStep 725243 = 1087865) B1087865
theorem B725369 : Blo 479788 725369 := bstep (se 2 (by rfl) ⟨272013, by rfl⟩ : syracuseStep 725369 = 544027) B544027
theorem B1905083 : Blo 479788 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B37491173 : Blo 479788 37491173 := bstep (se 4 (by rfl) ⟨3514797, by rfl⟩ : syracuseStep 37491173 = 7029595) B7029595
theorem B1085993 : Blo 479788 1085993 := bstep (se 2 (by rfl) ⟨407247, by rfl⟩ : syracuseStep 1085993 = 814495) B814495
theorem B1086407 : Blo 479788 1086407 := bstep (se 1 (by rfl) ⟨814805, by rfl⟩ : syracuseStep 1086407 = 1629611) B1629611
theorem B4167107 : Blo 479788 4167107 := bstep (se 1 (by rfl) ⟨3125330, by rfl⟩ : syracuseStep 4167107 = 6250661) B6250661
theorem B1087145 : Blo 479788 1087145 := bstep (se 2 (by rfl) ⟨407679, by rfl⟩ : syracuseStep 1087145 = 815359) B815359
theorem B1087271 : Blo 479788 1087271 := bstep (se 1 (by rfl) ⟨815453, by rfl⟩ : syracuseStep 1087271 = 1630907) B1630907
theorem B1218503 : Blo 479788 1218503 := bstep (se 1 (by rfl) ⟨913877, by rfl⟩ : syracuseStep 1218503 = 1827755) B1827755
theorem B1087559 : Blo 479788 1087559 := bstep (se 1 (by rfl) ⟨815669, by rfl⟩ : syracuseStep 1087559 = 1631339) B1631339
theorem B3644027 : Blo 479788 3644027 := bstep (se 1 (by rfl) ⟨2733020, by rfl⟩ : syracuseStep 3644027 = 5466041) B5466041
theorem B5479163 : Blo 479788 5479163 := bstep (se 1 (by rfl) ⟨4109372, by rfl⟩ : syracuseStep 5479163 = 8218745) B8218745
theorem B1219495 : Blo 479788 1219495 := bstep (se 1 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 1219495 = 1829243) B1829243
theorem B1088423 : Blo 479788 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B1088495 : Blo 479788 1088495 := bstep (se 1 (by rfl) ⟨816371, by rfl⟩ : syracuseStep 1088495 = 1632743) B1632743
theorem B4103905 : Blo 479788 4103905 := bstep (se 2 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 4103905 = 3077929) B3077929
theorem B1548191 : Blo 479788 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B1155215 : Blo 479788 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B1549307 : Blo 479788 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B4924637 : Blo 479788 4924637 := bstep (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) B1846739
theorem B3484097 : Blo 479788 3484097 := bstep (se 2 (by rfl) ⟨1306536, by rfl⟩ : syracuseStep 3484097 = 2613073) B2613073
theorem B54012521 : Blo 479788 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B928609 : Blo 479788 928609 := bstep (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) B696457
theorem B8465903 : Blo 479788 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B1847123 : Blo 479788 1847123 := bstep (se 1 (by rfl) ⟨1385342, by rfl⟩ : syracuseStep 1847123 = 2770685) B2770685
theorem B6238183 : Blo 479788 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B7843949 : Blo 479788 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B2437289 : Blo 479788 2437289 := bstep (se 2 (by rfl) ⟨913983, by rfl⟩ : syracuseStep 2437289 = 1827967) B1827967
theorem B2864065 : Blo 479788 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B2733659 : Blo 479788 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B42252293 : Blo 479788 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B1620431 : Blo 479788 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B23378483 : Blo 479788 23378483 := bstep (se 1 (by rfl) ⟨17533862, by rfl⟩ : syracuseStep 23378483 = 35067725) B35067725
theorem B2440367 : Blo 479788 2440367 := bstep (se 1 (by rfl) ⟨1830275, by rfl⟩ : syracuseStep 2440367 = 3660551) B3660551
theorem B60833045 : Blo 479788 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1392175 : Blo 479788 1392175 := bstep (se 1 (by rfl) ⟨1044131, by rfl⟩ : syracuseStep 1392175 = 2088263) B2088263
theorem B540607 : Blo 479788 540607 := bstep (se 1 (by rfl) ⟨405455, by rfl⟩ : syracuseStep 540607 = 810911) B810911
theorem B1753555 : Blo 479788 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B1622753 : Blo 479788 1622753 := bstep (se 2 (by rfl) ⟨608532, by rfl⟩ : syracuseStep 1622753 = 1217065) B1217065
theorem B14828453 : Blo 479788 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B1623293 : Blo 479788 1623293 := bstep (se 3 (by rfl) ⟨304367, by rfl⟩ : syracuseStep 1623293 = 608735) B608735
theorem B542191 : Blo 479788 542191 := bstep (se 1 (by rfl) ⟨406643, by rfl⟩ : syracuseStep 542191 = 813287) B813287
theorem B542623 : Blo 479788 542623 := bstep (se 1 (by rfl) ⟨406967, by rfl⟩ : syracuseStep 542623 = 813935) B813935
theorem B20892275 : Blo 479788 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B2444255 : Blo 479788 2444255 := bstep (se 1 (by rfl) ⟨1833191, by rfl⟩ : syracuseStep 2444255 = 3666383) B3666383
theorem B1625399 : Blo 479788 1625399 := bstep (se 1 (by rfl) ⟨1219049, by rfl⟩ : syracuseStep 1625399 = 2438099) B2438099
theorem B1625831 : Blo 479788 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B1626749 : Blo 479788 1626749 := bstep (se 3 (by rfl) ⟨305015, by rfl⟩ : syracuseStep 1626749 = 610031) B610031
theorem B479899 : Blo 479788 479899 := bstep (se 1 (by rfl) ⟨359924, by rfl⟩ : syracuseStep 479899 = 719849) B719849
theorem B479903 : Blo 479788 479903 := bstep (se 1 (by rfl) ⟨359927, by rfl⟩ : syracuseStep 479903 = 719855) B719855
theorem B1626857 : Blo 479788 1626857 := bstep (se 2 (by rfl) ⟨610071, by rfl⟩ : syracuseStep 1626857 = 1220143) B1220143
theorem B480027 : Blo 479788 480027 := bstep (se 1 (by rfl) ⟨360020, by rfl⟩ : syracuseStep 480027 = 720041) B720041
theorem B480639 : Blo 479788 480639 := bstep (se 1 (by rfl) ⟨360479, by rfl⟩ : syracuseStep 480639 = 720959) B720959
theorem B1955411 : Blo 479788 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B1628207 : Blo 479788 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B481343 : Blo 479788 481343 := bstep (se 1 (by rfl) ⟨361007, by rfl⟩ : syracuseStep 481343 = 722015) B722015
theorem B11262025 : Blo 479788 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B481519 : Blo 479788 481519 := bstep (se 1 (by rfl) ⟨361139, by rfl⟩ : syracuseStep 481519 = 722279) B722279
theorem B3529207 : Blo 479788 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B1956511 : Blo 479788 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B1628855 : Blo 479788 1628855 := bstep (se 1 (by rfl) ⟨1221641, by rfl⟩ : syracuseStep 1628855 = 2443283) B2443283
theorem B482299 : Blo 479788 482299 := bstep (se 1 (by rfl) ⟨361724, by rfl⟩ : syracuseStep 482299 = 723449) B723449
theorem B5856695 : Blo 479788 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B1629665 : Blo 479788 1629665 := bstep (se 2 (by rfl) ⟨611124, by rfl⟩ : syracuseStep 1629665 = 1222249) B1222249
theorem B1302439 : Blo 479788 1302439 := bstep (se 1 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 1302439 = 1953659) B1953659
theorem B5857231 : Blo 479788 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B811039 : Blo 479788 811039 := bstep (se 1 (by rfl) ⟨608279, by rfl⟩ : syracuseStep 811039 = 1216559) B1216559
theorem B483551 : Blo 479788 483551 := bstep (se 1 (by rfl) ⟨362663, by rfl⟩ : syracuseStep 483551 = 725327) B725327
theorem B483687 : Blo 479788 483687 := bstep (se 1 (by rfl) ⟨362765, by rfl⟩ : syracuseStep 483687 = 725531) B725531
theorem B811903 : Blo 479788 811903 := bstep (se 1 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 811903 = 1217855) B1217855
theorem B1631231 : Blo 479788 1631231 := bstep (se 1 (by rfl) ⟨1223423, by rfl⟩ : syracuseStep 1631231 = 2446847) B2446847
theorem B6186203 : Blo 479788 6186203 := bstep (se 1 (by rfl) ⟨4639652, by rfl⟩ : syracuseStep 6186203 = 9279305) B9279305
theorem B1631609 : Blo 479788 1631609 := bstep (se 2 (by rfl) ⟨611853, by rfl⟩ : syracuseStep 1631609 = 1223707) B1223707
theorem B5204695 : Blo 479788 5204695 := bstep (se 1 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 5204695 = 7807043) B7807043
theorem B814927 : Blo 479788 814927 := bstep (se 1 (by rfl) ⟨611195, by rfl⟩ : syracuseStep 814927 = 1222391) B1222391
theorem B6156269 : Blo 479788 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B1831187 : Blo 479788 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B1372639 : Blo 479788 1372639 := bstep (se 1 (by rfl) ⟨1029479, by rfl⟩ : syracuseStep 1372639 = 2058959) B2058959
theorem B4126049 : Blo 479788 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B1832827 : Blo 479788 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B8223119 : Blo 479788 8223119 := bstep (se 1 (by rfl) ⟨6167339, by rfl⟩ : syracuseStep 8223119 = 12334679) B12334679
theorem B5863843 : Blo 479788 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B915943 : Blo 479788 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B1374803 : Blo 479788 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B1833785 : Blo 479788 1833785 := bstep (se 2 (by rfl) ⟨687669, by rfl⟩ : syracuseStep 1833785 = 1375339) B1375339
theorem B3701629 : Blo 479788 3701629 := bstep (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) B1388111
theorem B14089247 : Blo 479788 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B720107 : Blo 479788 720107 := bstep (se 1 (by rfl) ⟨540080, by rfl⟩ : syracuseStep 720107 = 1080161) B1080161
theorem B720155 : Blo 479788 720155 := bstep (se 1 (by rfl) ⟨540116, by rfl⟩ : syracuseStep 720155 = 1080233) B1080233
theorem B720425 : Blo 479788 720425 := bstep (se 2 (by rfl) ⟨270159, by rfl⟩ : syracuseStep 720425 = 540319) B540319
theorem B720431 : Blo 479788 720431 := bstep (se 1 (by rfl) ⟨540323, by rfl⟩ : syracuseStep 720431 = 1080647) B1080647
theorem B720539 : Blo 479788 720539 := bstep (se 1 (by rfl) ⟨540404, by rfl⟩ : syracuseStep 720539 = 1080809) B1080809
theorem B1081385 : Blo 479788 1081385 := bstep (se 2 (by rfl) ⟨405519, by rfl⟩ : syracuseStep 1081385 = 811039) B811039
theorem B721007 : Blo 479788 721007 := bstep (se 1 (by rfl) ⟨540755, by rfl⟩ : syracuseStep 721007 = 1081511) B1081511
theorem B917659 : Blo 479788 917659 := bstep (se 1 (by rfl) ⟨688244, by rfl⟩ : syracuseStep 917659 = 1376489) B1376489
theorem B1081835 : Blo 479788 1081835 := bstep (se 1 (by rfl) ⟨811376, by rfl⟩ : syracuseStep 1081835 = 1622753) B1622753
theorem B721391 : Blo 479788 721391 := bstep (se 1 (by rfl) ⟨541043, by rfl⟩ : syracuseStep 721391 = 1082087) B1082087
theorem B1082195 : Blo 479788 1082195 := bstep (se 1 (by rfl) ⟨811646, by rfl⟩ : syracuseStep 1082195 = 1623293) B1623293
theorem B1082537 : Blo 479788 1082537 := bstep (se 2 (by rfl) ⟨405951, by rfl⟩ : syracuseStep 1082537 = 811903) B811903
theorem B13928183 : Blo 479788 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B722921 : Blo 479788 722921 := bstep (se 2 (by rfl) ⟨271095, by rfl⟩ : syracuseStep 722921 = 542191) B542191
theorem B1083599 : Blo 479788 1083599 := bstep (se 1 (by rfl) ⟨812699, by rfl⟩ : syracuseStep 1083599 = 1625399) B1625399
theorem B723263 : Blo 479788 723263 := bstep (se 1 (by rfl) ⟨542447, by rfl⟩ : syracuseStep 723263 = 1084895) B1084895
theorem B1083887 : Blo 479788 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B723497 : Blo 479788 723497 := bstep (se 2 (by rfl) ⟨271311, by rfl⟩ : syracuseStep 723497 = 542623) B542623
theorem B723611 : Blo 479788 723611 := bstep (se 1 (by rfl) ⟨542708, by rfl⟩ : syracuseStep 723611 = 1085417) B1085417
theorem B4131485 : Blo 479788 4131485 := bstep (se 3 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 4131485 = 1549307) B1549307
theorem B723995 : Blo 479788 723995 := bstep (se 1 (by rfl) ⟨542996, by rfl⟩ : syracuseStep 723995 = 1085993) B1085993
theorem B1084499 : Blo 479788 1084499 := bstep (se 1 (by rfl) ⟨813374, by rfl⟩ : syracuseStep 1084499 = 1626749) B1626749
theorem B1084571 : Blo 479788 1084571 := bstep (se 1 (by rfl) ⟨813428, by rfl⟩ : syracuseStep 1084571 = 1626857) B1626857
theorem B724271 : Blo 479788 724271 := bstep (se 1 (by rfl) ⟨543203, by rfl⟩ : syracuseStep 724271 = 1086407) B1086407
theorem B724763 : Blo 479788 724763 := bstep (se 1 (by rfl) ⟨543572, by rfl⟩ : syracuseStep 724763 = 1087145) B1087145
theorem B724847 : Blo 479788 724847 := bstep (se 1 (by rfl) ⟨543635, by rfl⟩ : syracuseStep 724847 = 1087271) B1087271
theorem B1085471 : Blo 479788 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B725039 : Blo 479788 725039 := bstep (se 1 (by rfl) ⟨543779, by rfl⟩ : syracuseStep 725039 = 1087559) B1087559
theorem B2429351 : Blo 479788 2429351 := bstep (se 1 (by rfl) ⟨1822013, by rfl⟩ : syracuseStep 2429351 = 3644027) B3644027
theorem B1085903 : Blo 479788 1085903 := bstep (se 1 (by rfl) ⟨814427, by rfl⟩ : syracuseStep 1085903 = 1628855) B1628855
theorem B725615 : Blo 479788 725615 := bstep (se 1 (by rfl) ⟨544211, by rfl⟩ : syracuseStep 725615 = 1088423) B1088423
theorem B725663 : Blo 479788 725663 := bstep (se 1 (by rfl) ⟨544247, by rfl⟩ : syracuseStep 725663 = 1088495) B1088495
theorem B3904463 : Blo 479788 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B1086443 : Blo 479788 1086443 := bstep (se 1 (by rfl) ⟨814832, by rfl⟩ : syracuseStep 1086443 = 1629665) B1629665
theorem B1086569 : Blo 479788 1086569 := bstep (se 2 (by rfl) ⟨407463, by rfl⟩ : syracuseStep 1086569 = 814927) B814927
theorem B1087487 : Blo 479788 1087487 := bstep (se 1 (by rfl) ⟨815615, by rfl⟩ : syracuseStep 1087487 = 1631231) B1631231
theorem B3283091 : Blo 479788 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B1087739 : Blo 479788 1087739 := bstep (se 1 (by rfl) ⟨815804, by rfl⟩ : syracuseStep 1087739 = 1631609) B1631609
theorem B5643935 : Blo 479788 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B4104179 : Blo 479788 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B15016033 : Blo 479788 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B1220791 : Blo 479788 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B1221257 : Blo 479788 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B5482079 : Blo 479788 5482079 := bstep (se 1 (by rfl) ⟨4111559, by rfl⟩ : syracuseStep 5482079 = 8223119) B8223119
theorem B1222523 : Blo 479788 1222523 := bstep (se 1 (by rfl) ⟨916892, by rfl⟩ : syracuseStep 1222523 = 1833785) B1833785
theorem B7809641 : Blo 479788 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B1223657 : Blo 479788 1223657 := bstep (se 2 (by rfl) ⟨458871, by rfl⟩ : syracuseStep 1223657 = 917743) B917743
theorem B2338073 : Blo 479788 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B44478659 : Blo 479788 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B1029343 : Blo 479788 1029343 := bstep (se 1 (by rfl) ⟨772007, by rfl⟩ : syracuseStep 1029343 = 1544015) B1544015
theorem B3652775 : Blo 479788 3652775 := bstep (se 1 (by rfl) ⟨2739581, by rfl⟩ : syracuseStep 3652775 = 5479163) B5479163
theorem B770143 : Blo 479788 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B3818753 : Blo 479788 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B19810325 : Blo 479788 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B2443769 : Blo 479788 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B1231415 : Blo 479788 1231415 := bstep (se 1 (by rfl) ⟨923561, by rfl⟩ : syracuseStep 1231415 = 1847123) B1847123
theorem B5229299 : Blo 479788 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B1624859 : Blo 479788 1624859 := bstep (se 1 (by rfl) ⟨1218644, by rfl⟩ : syracuseStep 1624859 = 2437289) B2437289
theorem B7818457 : Blo 479788 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B4705609 : Blo 479788 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B2608681 : Blo 479788 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B1822439 : Blo 479788 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B4935505 : Blo 479788 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B1625993 : Blo 479788 1625993 := bstep (se 2 (by rfl) ⟨609747, by rfl⟩ : syracuseStep 1625993 = 1219495) B1219495
theorem B28168195 : Blo 479788 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B15585655 : Blo 479788 15585655 := bstep (se 1 (by rfl) ⟨11689241, by rfl⟩ : syracuseStep 15585655 = 23378483) B23378483
theorem B9392831 : Blo 479788 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B1856233 : Blo 479788 1856233 := bstep (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) B1392175
theorem B1626911 : Blo 479788 1626911 := bstep (se 1 (by rfl) ⟨1220183, by rfl⟩ : syracuseStep 1626911 = 2440367) B2440367
theorem B480071 : Blo 479788 480071 := bstep (se 1 (by rfl) ⟨360053, by rfl⟩ : syracuseStep 480071 = 720107) B720107
theorem B40555363 : Blo 479788 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B480103 : Blo 479788 480103 := bstep (se 1 (by rfl) ⟨360077, by rfl⟩ : syracuseStep 480103 = 720155) B720155
theorem B480283 : Blo 479788 480283 := bstep (se 1 (by rfl) ⟨360212, by rfl⟩ : syracuseStep 480283 = 720425) B720425
theorem B480287 : Blo 479788 480287 := bstep (se 1 (by rfl) ⟨360215, by rfl⟩ : syracuseStep 480287 = 720431) B720431
theorem B480359 : Blo 479788 480359 := bstep (se 1 (by rfl) ⟨360269, by rfl⟩ : syracuseStep 480359 = 720539) B720539
theorem B480703 : Blo 479788 480703 := bstep (se 1 (by rfl) ⟨360527, by rfl⟩ : syracuseStep 480703 = 721055) B721055
theorem B9885635 : Blo 479788 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B481791 : Blo 479788 481791 := bstep (se 1 (by rfl) ⟨361343, by rfl⟩ : syracuseStep 481791 = 722687) B722687
theorem B482607 : Blo 479788 482607 := bstep (se 1 (by rfl) ⟨361955, by rfl⟩ : syracuseStep 482607 = 723911) B723911
theorem B1629503 : Blo 479788 1629503 := bstep (se 1 (by rfl) ⟨1222127, by rfl⟩ : syracuseStep 1629503 = 2444255) B2444255
theorem B482943 : Blo 479788 482943 := bstep (se 1 (by rfl) ⟨362207, by rfl⟩ : syracuseStep 482943 = 724415) B724415
theorem B483163 : Blo 479788 483163 := bstep (se 1 (by rfl) ⟨362372, by rfl⟩ : syracuseStep 483163 = 724745) B724745
theorem B483199 : Blo 479788 483199 := bstep (se 1 (by rfl) ⟨362399, by rfl⟩ : syracuseStep 483199 = 724799) B724799
theorem B483495 : Blo 479788 483495 := bstep (se 1 (by rfl) ⟨362621, by rfl⟩ : syracuseStep 483495 = 725243) B725243
theorem B483579 : Blo 479788 483579 := bstep (se 1 (by rfl) ⟨362684, by rfl⟩ : syracuseStep 483579 = 725369) B725369
theorem B1270055 : Blo 479788 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B24994115 : Blo 479788 24994115 := bstep (se 1 (by rfl) ⟨18745586, by rfl⟩ : syracuseStep 24994115 = 37491173) B37491173
theorem B6939593 : Blo 479788 6939593 := bstep (se 2 (by rfl) ⟨2602347, by rfl⟩ : syracuseStep 6939593 = 5204695) B5204695
theorem B2778071 : Blo 479788 2778071 := bstep (se 1 (by rfl) ⟨2083553, by rfl⟩ : syracuseStep 2778071 = 4167107) B4167107
theorem B1303607 : Blo 479788 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B812335 : Blo 479788 812335 := bstep (se 1 (by rfl) ⟨609251, by rfl⟩ : syracuseStep 812335 = 1218503) B1218503
theorem B8317577 : Blo 479788 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B2321057 : Blo 479788 2321057 := bstep (se 2 (by rfl) ⟨870396, by rfl⟩ : syracuseStep 2321057 = 1740793) B1740793
theorem B1830185 : Blo 479788 1830185 := bstep (se 2 (by rfl) ⟨686319, by rfl⟩ : syracuseStep 1830185 = 1372639) B1372639
theorem B4124135 : Blo 479788 4124135 := bstep (se 1 (by rfl) ⟨3093101, by rfl⟩ : syracuseStep 4124135 = 6186203) B6186203
theorem B2322731 : Blo 479788 2322731 := bstep (se 1 (by rfl) ⟨1742048, by rfl⟩ : syracuseStep 2322731 = 3484097) B3484097
theorem B36008347 : Blo 479788 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B2750699 : Blo 479788 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B1080287 : Blo 479788 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B916535 : Blo 479788 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B5471873 : Blo 479788 5471873 := bstep (se 2 (by rfl) ⟨2051952, by rfl⟩ : syracuseStep 5471873 = 4103905) B4103905
theorem B4128509 : Blo 479788 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B1736585 : Blo 479788 1736585 := bstep (se 2 (by rfl) ⟨651219, by rfl⟩ : syracuseStep 1736585 = 1302439) B1302439
theorem B720809 : Blo 479788 720809 := bstep (se 2 (by rfl) ⟨270303, by rfl⟩ : syracuseStep 720809 = 540607) B540607
theorem B720923 : Blo 479788 720923 := bstep (se 1 (by rfl) ⟨540692, by rfl⟩ : syracuseStep 720923 = 1081385) B1081385
theorem B20021377 : Blo 479788 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B721223 : Blo 479788 721223 := bstep (se 1 (by rfl) ⟨540917, by rfl⟩ : syracuseStep 721223 = 1081835) B1081835
theorem B721463 : Blo 479788 721463 := bstep (se 1 (by rfl) ⟨541097, by rfl⟩ : syracuseStep 721463 = 1082195) B1082195
theorem B721691 : Blo 479788 721691 := bstep (se 1 (by rfl) ⟨541268, by rfl⟩ : syracuseStep 721691 = 1082537) B1082537
theorem B13206883 : Blo 479788 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B722399 : Blo 479788 722399 := bstep (se 1 (by rfl) ⟨541799, by rfl⟩ : syracuseStep 722399 = 1083599) B1083599
theorem B722591 : Blo 479788 722591 := bstep (se 1 (by rfl) ⟨541943, by rfl⟩ : syracuseStep 722591 = 1083887) B1083887
theorem B820943 : Blo 479788 820943 := bstep (se 1 (by rfl) ⟨615707, by rfl⟩ : syracuseStep 820943 = 1231415) B1231415
theorem B1083113 : Blo 479788 1083113 := bstep (se 2 (by rfl) ⟨406167, by rfl⟩ : syracuseStep 1083113 = 812335) B812335
theorem B2754323 : Blo 479788 2754323 := bstep (se 1 (by rfl) ⟨2065742, by rfl⟩ : syracuseStep 2754323 = 4131485) B4131485
theorem B1083239 : Blo 479788 1083239 := bstep (se 1 (by rfl) ⟨812429, by rfl⟩ : syracuseStep 1083239 = 1624859) B1624859
theorem B722999 : Blo 479788 722999 := bstep (se 1 (by rfl) ⟨542249, by rfl⟩ : syracuseStep 722999 = 1084499) B1084499
theorem B723047 : Blo 479788 723047 := bstep (se 1 (by rfl) ⟨542285, by rfl⟩ : syracuseStep 723047 = 1084571) B1084571
theorem B1214959 : Blo 479788 1214959 := bstep (se 1 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 1214959 = 1822439) B1822439
theorem B7408189 : Blo 479788 7408189 := bstep (se 3 (by rfl) ⟨1389035, by rfl⟩ : syracuseStep 7408189 = 2778071) B2778071
theorem B1083995 : Blo 479788 1083995 := bstep (se 1 (by rfl) ⟨812996, by rfl⟩ : syracuseStep 1083995 = 1625993) B1625993
theorem B723647 : Blo 479788 723647 := bstep (se 1 (by rfl) ⟨542735, by rfl⟩ : syracuseStep 723647 = 1085471) B1085471
theorem B723935 : Blo 479788 723935 := bstep (se 1 (by rfl) ⟨542951, by rfl⟩ : syracuseStep 723935 = 1085903) B1085903
theorem B6261887 : Blo 479788 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B1084607 : Blo 479788 1084607 := bstep (se 1 (by rfl) ⟨813455, by rfl⟩ : syracuseStep 1084607 = 1626911) B1626911
theorem B724295 : Blo 479788 724295 := bstep (se 1 (by rfl) ⟨543221, by rfl⟩ : syracuseStep 724295 = 1086443) B1086443
theorem B724379 : Blo 479788 724379 := bstep (se 1 (by rfl) ⟨543284, by rfl⟩ : syracuseStep 724379 = 1086569) B1086569
theorem B6590423 : Blo 479788 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B724991 : Blo 479788 724991 := bstep (se 1 (by rfl) ⟨543743, by rfl⟩ : syracuseStep 724991 = 1087487) B1087487
theorem B725159 : Blo 479788 725159 := bstep (se 1 (by rfl) ⟨543869, by rfl⟩ : syracuseStep 725159 = 1087739) B1087739
theorem B10424609 : Blo 479788 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B3478241 : Blo 479788 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B1086335 : Blo 479788 1086335 := bstep (se 1 (by rfl) ⟨814751, by rfl⟩ : syracuseStep 1086335 = 1629503) B1629503
theorem B37557593 : Blo 479788 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B20780873 : Blo 479788 20780873 := bstep (se 2 (by rfl) ⟨7792827, by rfl⟩ : syracuseStep 20780873 = 15585655) B15585655
theorem B48011129 : Blo 479788 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B4626395 : Blo 479788 4626395 := bstep (se 1 (by rfl) ⟨3469796, by rfl⟩ : syracuseStep 4626395 = 6939593) B6939593
theorem B54073817 : Blo 479788 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1547371 : Blo 479788 1547371 := bstep (se 1 (by rfl) ⟨1160528, by rfl⟩ : syracuseStep 1547371 = 2321057) B2321057
theorem B1220123 : Blo 479788 1220123 := bstep (se 1 (by rfl) ⟨915092, by rfl⟩ : syracuseStep 1220123 = 1830185) B1830185
theorem B1548487 : Blo 479788 1548487 := bstep (se 1 (by rfl) ⟨1161365, by rfl⟩ : syracuseStep 1548487 = 2322731) B2322731
theorem B2435183 : Blo 479788 2435183 := bstep (se 1 (by rfl) ⟨1826387, by rfl⟩ : syracuseStep 2435183 = 3652775) B3652775
theorem B3647915 : Blo 479788 3647915 := bstep (se 1 (by rfl) ⟨2735936, by rfl⟩ : syracuseStep 3647915 = 5471873) B5471873
theorem B1157723 : Blo 479788 1157723 := bstep (se 1 (by rfl) ⟨868292, by rfl⟩ : syracuseStep 1157723 = 1736585) B1736585
theorem B1026857 : Blo 479788 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B1223545 : Blo 479788 1223545 := bstep (se 2 (by rfl) ⟨458829, by rfl⟩ : syracuseStep 1223545 = 917659) B917659
theorem B9285455 : Blo 479788 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B3486199 : Blo 479788 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B1619567 : Blo 479788 1619567 := bstep (se 1 (by rfl) ⟨1214675, by rfl⟩ : syracuseStep 1619567 = 2429351) B2429351
theorem B2602975 : Blo 479788 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B6274145 : Blo 479788 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B2736119 : Blo 479788 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B16662743 : Blo 479788 16662743 := bstep (se 1 (by rfl) ⟨12497057, by rfl⟩ : syracuseStep 16662743 = 24994115) B24994115
theorem B869071 : Blo 479788 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B2474977 : Blo 479788 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B3654719 : Blo 479788 3654719 := bstep (se 1 (by rfl) ⟨2741039, by rfl⟩ : syracuseStep 3654719 = 5482079) B5482079
theorem B1558715 : Blo 479788 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B2444093 : Blo 479788 2444093 := bstep (se 3 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 2444093 = 916535) B916535
theorem B480539 : Blo 479788 480539 := bstep (se 1 (by rfl) ⟨360404, by rfl⟩ : syracuseStep 480539 = 720809) B720809
theorem B480671 : Blo 479788 480671 := bstep (se 1 (by rfl) ⟨360503, by rfl⟩ : syracuseStep 480671 = 721007) B721007
theorem B1627721 : Blo 479788 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B480927 : Blo 479788 480927 := bstep (se 1 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 480927 = 721391) B721391
theorem B2545835 : Blo 479788 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B481947 : Blo 479788 481947 := bstep (se 1 (by rfl) ⟨361460, by rfl⟩ : syracuseStep 481947 = 722921) B722921
theorem B482175 : Blo 479788 482175 := bstep (se 1 (by rfl) ⟨361631, by rfl⟩ : syracuseStep 482175 = 723263) B723263
theorem B1629179 : Blo 479788 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B482331 : Blo 479788 482331 := bstep (se 1 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 482331 = 723497) B723497
theorem B482407 : Blo 479788 482407 := bstep (se 1 (by rfl) ⟨361805, by rfl⟩ : syracuseStep 482407 = 723611) B723611
theorem B482663 : Blo 479788 482663 := bstep (se 1 (by rfl) ⟨361997, by rfl⟩ : syracuseStep 482663 = 723995) B723995
theorem B482847 : Blo 479788 482847 := bstep (se 1 (by rfl) ⟨362135, by rfl⟩ : syracuseStep 482847 = 724271) B724271
theorem B483175 : Blo 479788 483175 := bstep (se 1 (by rfl) ⟨362381, by rfl⟩ : syracuseStep 483175 = 724763) B724763
theorem B483231 : Blo 479788 483231 := bstep (se 1 (by rfl) ⟨362423, by rfl⟩ : syracuseStep 483231 = 724847) B724847
theorem B483359 : Blo 479788 483359 := bstep (se 1 (by rfl) ⟨362519, by rfl⟩ : syracuseStep 483359 = 725039) B725039
theorem B483743 : Blo 479788 483743 := bstep (se 1 (by rfl) ⟨362807, by rfl⟩ : syracuseStep 483743 = 725615) B725615
theorem B483775 : Blo 479788 483775 := bstep (se 1 (by rfl) ⟨362831, by rfl⟩ : syracuseStep 483775 = 725663) B725663
theorem B2188727 : Blo 479788 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B3762623 : Blo 479788 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B6580673 : Blo 479788 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B846703 : Blo 479788 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B814171 : Blo 479788 814171 := bstep (se 1 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 814171 = 1221257) B1221257
theorem B815015 : Blo 479788 815015 := bstep (se 1 (by rfl) ⟨611261, by rfl⟩ : syracuseStep 815015 = 1222523) B1222523
theorem B1372457 : Blo 479788 1372457 := bstep (se 2 (by rfl) ⟨514671, by rfl⟩ : syracuseStep 1372457 = 1029343) B1029343
theorem B22180205 : Blo 479788 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B5206427 : Blo 479788 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B815771 : Blo 479788 815771 := bstep (se 1 (by rfl) ⟨611828, by rfl⟩ : syracuseStep 815771 = 1223657) B1223657
theorem B2749423 : Blo 479788 2749423 := bstep (se 1 (by rfl) ⟨2062067, by rfl⟩ : syracuseStep 2749423 = 4124135) B4124135
theorem B29652439 : Blo 479788 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B1833799 : Blo 479788 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B720191 : Blo 479788 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B2752339 : Blo 479788 2752339 := bstep (se 1 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 2752339 = 4128509) B4128509
theorem B11108495 : Blo 479788 11108495 := bstep (se 1 (by rfl) ⟨8331371, by rfl⟩ : syracuseStep 11108495 = 16662743) B16662743
theorem B2064649 : Blo 479788 2064649 := bstep (se 2 (by rfl) ⟨774243, by rfl⟩ : syracuseStep 2064649 = 1548487) B1548487
theorem B722075 : Blo 479788 722075 := bstep (se 1 (by rfl) ⟨541556, by rfl⟩ : syracuseStep 722075 = 1083113) B1083113
theorem B1836215 : Blo 479788 1836215 := bstep (se 1 (by rfl) ⟨1377161, by rfl⟩ : syracuseStep 1836215 = 2754323) B2754323
theorem B722159 : Blo 479788 722159 := bstep (se 1 (by rfl) ⟨541619, by rfl⟩ : syracuseStep 722159 = 1083239) B1083239
theorem B722663 : Blo 479788 722663 := bstep (se 1 (by rfl) ⟨541997, by rfl⟩ : syracuseStep 722663 = 1083995) B1083995
theorem B9275309 : Blo 479788 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B723071 : Blo 479788 723071 := bstep (se 1 (by rfl) ⟨542303, by rfl⟩ : syracuseStep 723071 = 1084607) B1084607
theorem B4393615 : Blo 479788 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B6949739 : Blo 479788 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B724223 : Blo 479788 724223 := bstep (se 1 (by rfl) ⟨543167, by rfl⟩ : syracuseStep 724223 = 1086335) B1086335
theorem B25038395 : Blo 479788 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B1085147 : Blo 479788 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B3084263 : Blo 479788 3084263 := bstep (se 1 (by rfl) ⟨2313197, by rfl⟩ : syracuseStep 3084263 = 4626395) B4626395
theorem B1085561 : Blo 479788 1085561 := bstep (se 2 (by rfl) ⟨407085, by rfl⟩ : syracuseStep 1085561 = 814171) B814171
theorem B36049211 : Blo 479788 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1086119 : Blo 479788 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B6788893 : Blo 479788 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B2431943 : Blo 479788 2431943 := bstep (se 1 (by rfl) ⟨1823957, by rfl⟩ : syracuseStep 2431943 = 3647915) B3647915
theorem B14786803 : Blo 479788 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B2436479 : Blo 479788 2436479 := bstep (se 1 (by rfl) ⟨1827359, by rfl⟩ : syracuseStep 2436479 = 3654719) B3654719
theorem B1158761 : Blo 479788 1158761 := bstep (se 2 (by rfl) ⟨434535, by rfl⟩ : syracuseStep 1158761 = 869071) B869071
theorem B17609177 : Blo 479788 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B16626293 : Blo 479788 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B4174591 : Blo 479788 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1619945 : Blo 479788 1619945 := bstep (se 2 (by rfl) ⟨607479, by rfl⟩ : syracuseStep 1619945 = 1214959) B1214959
theorem B9877585 : Blo 479788 9877585 := bstep (se 2 (by rfl) ⟨3704094, by rfl⟩ : syracuseStep 9877585 = 7408189) B7408189
theorem B1459151 : Blo 479788 1459151 := bstep (se 1 (by rfl) ⟨1094363, by rfl⟩ : syracuseStep 1459151 = 2188727) B2188727
theorem B1623455 : Blo 479788 1623455 := bstep (se 1 (by rfl) ⟨1217591, by rfl⟩ : syracuseStep 1623455 = 2435183) B2435183
theorem B2508415 : Blo 479788 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B771815 : Blo 479788 771815 := bstep (se 1 (by rfl) ⟨578861, by rfl⟩ : syracuseStep 771815 = 1157723) B1157723
theorem B39536585 : Blo 479788 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B2738285 : Blo 479788 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B543343 : Blo 479788 543343 := bstep (se 1 (by rfl) ⟨407507, by rfl⟩ : syracuseStep 543343 = 815015) B815015
theorem B543847 : Blo 479788 543847 := bstep (se 1 (by rfl) ⟨407885, by rfl⟩ : syracuseStep 543847 = 815771) B815771
theorem B2445065 : Blo 479788 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B4182763 : Blo 479788 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B480127 : Blo 479788 480127 := bstep (se 1 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 480127 = 720191) B720191
theorem B1824079 : Blo 479788 1824079 := bstep (se 1 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 1824079 = 2736119) B2736119
theorem B480615 : Blo 479788 480615 := bstep (se 1 (by rfl) ⟨360461, by rfl⟩ : syracuseStep 480615 = 720923) B720923
theorem B26695169 : Blo 479788 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B480815 : Blo 479788 480815 := bstep (se 1 (by rfl) ⟨360611, by rfl⟩ : syracuseStep 480815 = 721223) B721223
theorem B480975 : Blo 479788 480975 := bstep (se 1 (by rfl) ⟨360731, by rfl⟩ : syracuseStep 480975 = 721463) B721463
theorem B481127 : Blo 479788 481127 := bstep (se 1 (by rfl) ⟨360845, by rfl⟩ : syracuseStep 481127 = 721691) B721691
theorem B481599 : Blo 479788 481599 := bstep (se 1 (by rfl) ⟨361199, by rfl⟩ : syracuseStep 481599 = 722399) B722399
theorem B481727 : Blo 479788 481727 := bstep (se 1 (by rfl) ⟨361295, by rfl⟩ : syracuseStep 481727 = 722591) B722591
theorem B547295 : Blo 479788 547295 := bstep (se 1 (by rfl) ⟨410471, by rfl⟩ : syracuseStep 547295 = 820943) B820943
theorem B3299969 : Blo 479788 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B481999 : Blo 479788 481999 := bstep (se 1 (by rfl) ⟨361499, by rfl⟩ : syracuseStep 481999 = 722999) B722999
theorem B482031 : Blo 479788 482031 := bstep (se 1 (by rfl) ⟨361523, by rfl⟩ : syracuseStep 482031 = 723047) B723047
theorem B482431 : Blo 479788 482431 := bstep (se 1 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 482431 = 723647) B723647
theorem B1629395 : Blo 479788 1629395 := bstep (se 1 (by rfl) ⟨1222046, by rfl⟩ : syracuseStep 1629395 = 2444093) B2444093
theorem B482623 : Blo 479788 482623 := bstep (se 1 (by rfl) ⟨361967, by rfl⟩ : syracuseStep 482623 = 723935) B723935
theorem B482863 : Blo 479788 482863 := bstep (se 1 (by rfl) ⟨362147, by rfl⟩ : syracuseStep 482863 = 724295) B724295
theorem B482919 : Blo 479788 482919 := bstep (se 1 (by rfl) ⟨362189, by rfl⟩ : syracuseStep 482919 = 724379) B724379
theorem B483327 : Blo 479788 483327 := bstep (se 1 (by rfl) ⟨362495, by rfl⟩ : syracuseStep 483327 = 724991) B724991
theorem B483439 : Blo 479788 483439 := bstep (se 1 (by rfl) ⟨362579, by rfl⟩ : syracuseStep 483439 = 725159) B725159
theorem B1631393 : Blo 479788 1631393 := bstep (se 2 (by rfl) ⟨611772, by rfl⟩ : syracuseStep 1631393 = 1223545) B1223545
theorem B13853915 : Blo 479788 13853915 := bstep (se 1 (by rfl) ⟨10390436, by rfl⟩ : syracuseStep 13853915 = 20780873) B20780873
theorem B32007419 : Blo 479788 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B4515749 : Blo 479788 4515749 := bstep (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) B846703
theorem B813415 : Blo 479788 813415 := bstep (se 1 (by rfl) ⟨610061, by rfl⟩ : syracuseStep 813415 = 1220123) B1220123
theorem B4648265 : Blo 479788 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B3665897 : Blo 479788 3665897 := bstep (se 2 (by rfl) ⟨1374711, by rfl⟩ : syracuseStep 3665897 = 2749423) B2749423
theorem B4387115 : Blo 479788 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B6190303 : Blo 479788 6190303 := bstep (se 1 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 6190303 = 9285455) B9285455
theorem B3470633 : Blo 479788 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B914971 : Blo 479788 914971 := bstep (se 1 (by rfl) ⟨686228, by rfl⟩ : syracuseStep 914971 = 1372457) B1372457
theorem B3470951 : Blo 479788 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B1079711 : Blo 479788 1079711 := bstep (se 1 (by rfl) ⟨809783, by rfl⟩ : syracuseStep 1079711 = 1619567) B1619567
theorem B2063161 : Blo 479788 2063161 := bstep (se 2 (by rfl) ⟨773685, by rfl⟩ : syracuseStep 2063161 = 1547371) B1547371
theorem B3669785 : Blo 479788 3669785 := bstep (se 2 (by rfl) ⟨1376169, by rfl⟩ : syracuseStep 3669785 = 2752339) B2752339
theorem B7405663 : Blo 479788 7405663 := bstep (se 1 (by rfl) ⟨5554247, by rfl⟩ : syracuseStep 7405663 = 11108495) B11108495
theorem B2752865 : Blo 479788 2752865 := bstep (se 2 (by rfl) ⟨1032324, by rfl⟩ : syracuseStep 2752865 = 2064649) B2064649
theorem B1082303 : Blo 479788 1082303 := bstep (se 1 (by rfl) ⟨811727, by rfl⟩ : syracuseStep 1082303 = 1623455) B1623455
theorem B723431 : Blo 479788 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B723707 : Blo 479788 723707 := bstep (se 1 (by rfl) ⟨542780, by rfl⟩ : syracuseStep 723707 = 1085561) B1085561
theorem B724079 : Blo 479788 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B1084553 : Blo 479788 1084553 := bstep (se 2 (by rfl) ⟨406707, by rfl⟩ : syracuseStep 1084553 = 813415) B813415
theorem B724457 : Blo 479788 724457 := bstep (se 2 (by rfl) ⟨271671, by rfl⟩ : syracuseStep 724457 = 543343) B543343
theorem B17796779 : Blo 479788 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B725129 : Blo 479788 725129 := bstep (se 2 (by rfl) ⟨271923, by rfl⟩ : syracuseStep 725129 = 543847) B543847
theorem B2199979 : Blo 479788 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B1086263 : Blo 479788 1086263 := bstep (se 1 (by rfl) ⟨814697, by rfl⟩ : syracuseStep 1086263 = 1629395) B1629395
theorem B1087595 : Blo 479788 1087595 := bstep (se 1 (by rfl) ⟨815696, by rfl⟩ : syracuseStep 1087595 = 1631393) B1631393
theorem B21338279 : Blo 479788 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B5577017 : Blo 479788 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B2432105 : Blo 479788 2432105 := bstep (se 2 (by rfl) ⟨912039, by rfl⟩ : syracuseStep 2432105 = 1824079) B1824079
theorem B1219961 : Blo 479788 1219961 := bstep (se 2 (by rfl) ⟨457485, by rfl⟩ : syracuseStep 1219961 = 914971) B914971
theorem B9051857 : Blo 479788 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B2924743 : Blo 479788 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B11739451 : Blo 479788 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B11084195 : Blo 479788 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B13378213 : Blo 479788 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B1224143 : Blo 479788 1224143 := bstep (se 1 (by rfl) ⟨918107, by rfl⟩ : syracuseStep 1224143 = 1836215) B1836215
theorem B26357723 : Blo 479788 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B4633159 : Blo 479788 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B16692263 : Blo 479788 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B24032807 : Blo 479788 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B1621295 : Blo 479788 1621295 := bstep (se 1 (by rfl) ⟨1215971, by rfl⟩ : syracuseStep 1621295 = 2431943) B2431943
theorem B1459453 : Blo 479788 1459453 := bstep (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) B547295
theorem B3098843 : Blo 479788 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B1624319 : Blo 479788 1624319 := bstep (se 1 (by rfl) ⟨1218239, by rfl⟩ : syracuseStep 1624319 = 2436479) B2436479
theorem B772507 : Blo 479788 772507 := bstep (se 1 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 772507 = 1158761) B1158761
theorem B2443931 : Blo 479788 2443931 := bstep (se 1 (by rfl) ⟨1832948, by rfl⟩ : syracuseStep 2443931 = 3665897) B3665897
theorem B2313755 : Blo 479788 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B2313967 : Blo 479788 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B2446523 : Blo 479788 2446523 := bstep (se 1 (by rfl) ⟨1834892, by rfl⟩ : syracuseStep 2446523 = 3669785) B3669785
theorem B19715737 : Blo 479788 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B972767 : Blo 479788 972767 := bstep (se 1 (by rfl) ⟨729575, by rfl⟩ : syracuseStep 972767 = 1459151) B1459151
theorem B481383 : Blo 479788 481383 := bstep (se 1 (by rfl) ⟨361037, by rfl⟩ : syracuseStep 481383 = 722075) B722075
theorem B481439 : Blo 479788 481439 := bstep (se 1 (by rfl) ⟨361079, by rfl⟩ : syracuseStep 481439 = 722159) B722159
theorem B481775 : Blo 479788 481775 := bstep (se 1 (by rfl) ⟨361331, by rfl⟩ : syracuseStep 481775 = 722663) B722663
theorem B6183539 : Blo 479788 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B1825523 : Blo 479788 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B482047 : Blo 479788 482047 := bstep (se 1 (by rfl) ⟨361535, by rfl⟩ : syracuseStep 482047 = 723071) B723071
theorem B482815 : Blo 479788 482815 := bstep (se 1 (by rfl) ⟨362111, by rfl⟩ : syracuseStep 482815 = 724223) B724223
theorem B1630043 : Blo 479788 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B2056175 : Blo 479788 2056175 := bstep (se 1 (by rfl) ⟨1542131, by rfl⟩ : syracuseStep 2056175 = 3084263) B3084263
theorem B5858153 : Blo 479788 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B2058173 : Blo 479788 2058173 := bstep (se 3 (by rfl) ⟨385907, by rfl⟩ : syracuseStep 2058173 = 771815) B771815
theorem B9235943 : Blo 479788 9235943 := bstep (se 1 (by rfl) ⟨6926957, by rfl⟩ : syracuseStep 9235943 = 13853915) B13853915
theorem B5566121 : Blo 479788 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B3010499 : Blo 479788 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B8253737 : Blo 479788 8253737 := bstep (se 2 (by rfl) ⟨3095151, by rfl⟩ : syracuseStep 8253737 = 6190303) B6190303
theorem B13170113 : Blo 479788 13170113 := bstep (se 2 (by rfl) ⟨4938792, by rfl⟩ : syracuseStep 13170113 = 9877585) B9877585
theorem B2750881 : Blo 479788 2750881 := bstep (se 2 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 2750881 = 2063161) B2063161
theorem B1079963 : Blo 479788 1079963 := bstep (se 1 (by rfl) ⟨809972, by rfl⟩ : syracuseStep 1079963 = 1619945) B1619945
theorem B719807 : Blo 479788 719807 := bstep (se 1 (by rfl) ⟨539855, by rfl⟩ : syracuseStep 719807 = 1079711) B1079711
theorem B1835243 : Blo 479788 1835243 := bstep (se 1 (by rfl) ⟨1376432, by rfl⟩ : syracuseStep 1835243 = 2752865) B2752865
theorem B3899657 : Blo 479788 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B721535 : Blo 479788 721535 := bstep (se 1 (by rfl) ⟨541151, by rfl⟩ : syracuseStep 721535 = 1082303) B1082303
theorem B2065895 : Blo 479788 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B1082879 : Blo 479788 1082879 := bstep (se 1 (by rfl) ⟨812159, by rfl⟩ : syracuseStep 1082879 = 1624319) B1624319
theorem B723035 : Blo 479788 723035 := bstep (se 1 (by rfl) ⟨542276, by rfl⟩ : syracuseStep 723035 = 1084553) B1084553
theorem B11733221 : Blo 479788 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B1542503 : Blo 479788 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B11864519 : Blo 479788 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B724175 : Blo 479788 724175 := bstep (se 1 (by rfl) ⟨543131, by rfl⟩ : syracuseStep 724175 = 1086263) B1086263
theorem B725063 : Blo 479788 725063 := bstep (se 1 (by rfl) ⟨543797, by rfl⟩ : syracuseStep 725063 = 1087595) B1087595
theorem B14225519 : Blo 479788 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B1217015 : Blo 479788 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B3085289 : Blo 479788 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B6034571 : Blo 479788 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B1086695 : Blo 479788 1086695 := bstep (se 1 (by rfl) ⟨815021, by rfl⟩ : syracuseStep 1086695 = 1630043) B1630043
theorem B2594045 : Blo 479788 2594045 := bstep (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) B972767
theorem B3905435 : Blo 479788 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B26287649 : Blo 479788 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B3710747 : Blo 479788 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B2006999 : Blo 479788 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B17571815 : Blo 479788 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B9874217 : Blo 479788 9874217 := bstep (se 2 (by rfl) ⟨3702831, by rfl⟩ : syracuseStep 9874217 = 7405663) B7405663
theorem B17837617 : Blo 479788 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B1945937 : Blo 479788 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B1030009 : Blo 479788 1030009 := bstep (se 2 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 1030009 = 772507) B772507
theorem B1621403 : Blo 479788 1621403 := bstep (se 1 (by rfl) ⟨1216052, by rfl⟩ : syracuseStep 1621403 = 2432105) B2432105
theorem B7389463 : Blo 479788 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B6177545 : Blo 479788 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B11128175 : Blo 479788 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B479871 : Blo 479788 479871 := bstep (se 1 (by rfl) ⟨359903, by rfl⟩ : syracuseStep 479871 = 719807) B719807
theorem B15652601 : Blo 479788 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B482287 : Blo 479788 482287 := bstep (se 1 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 482287 = 723431) B723431
theorem B1629287 : Blo 479788 1629287 := bstep (se 1 (by rfl) ⟨1221965, by rfl⟩ : syracuseStep 1629287 = 2443931) B2443931
theorem B482471 : Blo 479788 482471 := bstep (se 1 (by rfl) ⟨361853, by rfl⟩ : syracuseStep 482471 = 723707) B723707
theorem B482719 : Blo 479788 482719 := bstep (se 1 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 482719 = 724079) B724079
theorem B482971 : Blo 479788 482971 := bstep (se 1 (by rfl) ⟨362228, by rfl⟩ : syracuseStep 482971 = 724457) B724457
theorem B483419 : Blo 479788 483419 := bstep (se 1 (by rfl) ⟨362564, by rfl⟩ : syracuseStep 483419 = 725129) B725129
theorem B1631015 : Blo 479788 1631015 := bstep (se 1 (by rfl) ⟨1223261, by rfl⟩ : syracuseStep 1631015 = 2446523) B2446523
theorem B4122359 : Blo 479788 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B813307 : Blo 479788 813307 := bstep (se 1 (by rfl) ⟨609980, by rfl⟩ : syracuseStep 813307 = 1219961) B1219961
theorem B1370783 : Blo 479788 1370783 := bstep (se 1 (by rfl) ⟨1028087, by rfl⟩ : syracuseStep 1370783 = 2056175) B2056175
theorem B14872045 : Blo 479788 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B1372115 : Blo 479788 1372115 := bstep (se 1 (by rfl) ⟨1029086, by rfl⟩ : syracuseStep 1372115 = 2058173) B2058173
theorem B816095 : Blo 479788 816095 := bstep (se 1 (by rfl) ⟨612071, by rfl⟩ : syracuseStep 816095 = 1224143) B1224143
theorem B6157295 : Blo 479788 6157295 := bstep (se 1 (by rfl) ⟨4617971, by rfl⟩ : syracuseStep 6157295 = 9235943) B9235943
theorem B5502491 : Blo 479788 5502491 := bstep (se 1 (by rfl) ⟨4126868, by rfl⟩ : syracuseStep 5502491 = 8253737) B8253737
theorem B3667841 : Blo 479788 3667841 := bstep (se 2 (by rfl) ⟨1375440, by rfl⟩ : syracuseStep 3667841 = 2750881) B2750881
theorem B8780075 : Blo 479788 8780075 := bstep (se 1 (by rfl) ⟨6585056, by rfl⟩ : syracuseStep 8780075 = 13170113) B13170113
theorem B16021871 : Blo 479788 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B719975 : Blo 479788 719975 := bstep (se 1 (by rfl) ⟨539981, by rfl⟩ : syracuseStep 719975 = 1079963) B1079963
theorem B1080863 : Blo 479788 1080863 := bstep (se 1 (by rfl) ⟨810647, by rfl⟩ : syracuseStep 1080863 = 1621295) B1621295
theorem B1377263 : Blo 479788 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B721919 : Blo 479788 721919 := bstep (se 1 (by rfl) ⟨541439, by rfl⟩ : syracuseStep 721919 = 1082879) B1082879
theorem B1084409 : Blo 479788 1084409 := bstep (se 2 (by rfl) ⟨406653, by rfl⟩ : syracuseStep 1084409 = 813307) B813307
theorem B724463 : Blo 479788 724463 := bstep (se 1 (by rfl) ⟨543347, by rfl⟩ : syracuseStep 724463 = 1086695) B1086695
theorem B19829393 : Blo 479788 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B1086191 : Blo 479788 1086191 := bstep (se 1 (by rfl) ⟨814643, by rfl⟩ : syracuseStep 1086191 = 1629287) B1629287
theorem B1087343 : Blo 479788 1087343 := bstep (se 1 (by rfl) ⟨815507, by rfl⟩ : syracuseStep 1087343 = 1631015) B1631015
theorem B4104863 : Blo 479788 4104863 := bstep (se 1 (by rfl) ⟨3078647, by rfl⟩ : syracuseStep 4104863 = 6157295) B6157295
theorem B1223495 : Blo 479788 1223495 := bstep (se 1 (by rfl) ⟨917621, by rfl⟩ : syracuseStep 1223495 = 1835243) B1835243
theorem B2599771 : Blo 479788 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B1028335 : Blo 479788 1028335 := bstep (se 1 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 1028335 = 1542503) B1542503
theorem B7909679 : Blo 479788 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B7418783 : Blo 479788 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B9483679 : Blo 479788 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B10435067 : Blo 479788 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B2473831 : Blo 479788 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B11714543 : Blo 479788 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B1297291 : Blo 479788 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B544063 : Blo 479788 544063 := bstep (se 1 (by rfl) ⟨408047, by rfl⟩ : syracuseStep 544063 = 816095) B816095
theorem B2445227 : Blo 479788 2445227 := bstep (se 1 (by rfl) ⟨1833920, by rfl⟩ : syracuseStep 2445227 = 3667841) B3667841
theorem B5853383 : Blo 479788 5853383 := bstep (se 1 (by rfl) ⟨4390037, by rfl⟩ : syracuseStep 5853383 = 8780075) B8780075
theorem B479983 : Blo 479788 479983 := bstep (se 1 (by rfl) ⟨359987, by rfl⟩ : syracuseStep 479983 = 719975) B719975
theorem B9852617 : Blo 479788 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B481023 : Blo 479788 481023 := bstep (se 1 (by rfl) ⟨360767, by rfl⟩ : syracuseStep 481023 = 721535) B721535
theorem B4118363 : Blo 479788 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B482023 : Blo 479788 482023 := bstep (se 1 (by rfl) ⟨361517, by rfl⟩ : syracuseStep 482023 = 723035) B723035
theorem B482783 : Blo 479788 482783 := bstep (se 1 (by rfl) ⟨362087, by rfl⟩ : syracuseStep 482783 = 724175) B724175
theorem B483375 : Blo 479788 483375 := bstep (se 1 (by rfl) ⟨362531, by rfl⟩ : syracuseStep 483375 = 725063) B725063
theorem B811343 : Blo 479788 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B2056859 : Blo 479788 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B4023047 : Blo 479788 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B1729363 : Blo 479788 1729363 := bstep (se 1 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 1729363 = 2594045) B2594045
theorem B23783489 : Blo 479788 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B17525099 : Blo 479788 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B10414493 : Blo 479788 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B1337999 : Blo 479788 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B31288589 : Blo 479788 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B2748239 : Blo 479788 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B913855 : Blo 479788 913855 := bstep (se 1 (by rfl) ⟨685391, by rfl⟩ : syracuseStep 913855 = 1370783) B1370783
theorem B6582811 : Blo 479788 6582811 := bstep (se 1 (by rfl) ⟨4937108, by rfl⟩ : syracuseStep 6582811 = 9874217) B9874217
theorem B1373345 : Blo 479788 1373345 := bstep (se 2 (by rfl) ⟨515004, by rfl⟩ : syracuseStep 1373345 = 1030009) B1030009
theorem B914743 : Blo 479788 914743 := bstep (se 1 (by rfl) ⟨686057, by rfl⟩ : syracuseStep 914743 = 1372115) B1372115
theorem B3668327 : Blo 479788 3668327 := bstep (se 1 (by rfl) ⟨2751245, by rfl⟩ : syracuseStep 3668327 = 5502491) B5502491
theorem B10681247 : Blo 479788 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B1080935 : Blo 479788 1080935 := bstep (se 1 (by rfl) ⟨810701, by rfl⟩ : syracuseStep 1080935 = 1621403) B1621403
theorem B720575 : Blo 479788 720575 := bstep (se 1 (by rfl) ⟨540431, by rfl⟩ : syracuseStep 720575 = 1080863) B1080863
theorem B722939 : Blo 479788 722939 := bstep (se 1 (by rfl) ⟨542204, by rfl⟩ : syracuseStep 722939 = 1084409) B1084409
theorem B3672701 : Blo 479788 3672701 := bstep (se 3 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 3672701 = 1377263) B1377263
theorem B3902255 : Blo 479788 3902255 := bstep (se 1 (by rfl) ⟨2926691, by rfl⟩ : syracuseStep 3902255 = 5853383) B5853383
theorem B724127 : Blo 479788 724127 := bstep (se 1 (by rfl) ⟨543095, by rfl⟩ : syracuseStep 724127 = 1086191) B1086191
theorem B724895 : Blo 479788 724895 := bstep (se 1 (by rfl) ⟨543671, by rfl⟩ : syracuseStep 724895 = 1087343) B1087343
theorem B725417 : Blo 479788 725417 := bstep (se 2 (by rfl) ⟨272031, by rfl⟩ : syracuseStep 725417 = 544063) B544063
theorem B1218473 : Blo 479788 1218473 := bstep (se 2 (by rfl) ⟨456927, by rfl⟩ : syracuseStep 1218473 = 913855) B913855
theorem B1219657 : Blo 479788 1219657 := bstep (se 2 (by rfl) ⟨457371, by rfl⟩ : syracuseStep 1219657 = 914743) B914743
theorem B6956711 : Blo 479788 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B7120831 : Blo 479788 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B7809695 : Blo 479788 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B2305817 : Blo 479788 2305817 := bstep (se 2 (by rfl) ⟨864681, by rfl⟩ : syracuseStep 2305817 = 1729363) B1729363
theorem B10728125 : Blo 479788 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B13219595 : Blo 479788 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B6568411 : Blo 479788 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B540895 : Blo 479788 540895 := bstep (se 1 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 540895 = 811343) B811343
theorem B2736575 : Blo 479788 2736575 := bstep (se 1 (by rfl) ⟨2052431, by rfl⟩ : syracuseStep 2736575 = 4104863) B4104863
theorem B11683399 : Blo 479788 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B50579621 : Blo 479788 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B20859059 : Blo 479788 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B2445551 : Blo 479788 2445551 := bstep (se 1 (by rfl) ⟨1834163, by rfl⟩ : syracuseStep 2445551 = 3668327) B3668327
theorem B480383 : Blo 479788 480383 := bstep (se 1 (by rfl) ⟨360287, by rfl⟩ : syracuseStep 480383 = 720575) B720575
theorem B3298441 : Blo 479788 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B481279 : Blo 479788 481279 := bstep (se 1 (by rfl) ⟨360959, by rfl⟩ : syracuseStep 481279 = 721919) B721919
theorem B482975 : Blo 479788 482975 := bstep (se 1 (by rfl) ⟨362231, by rfl⟩ : syracuseStep 482975 = 724463) B724463
theorem B1630151 : Blo 479788 1630151 := bstep (se 1 (by rfl) ⟨1222613, by rfl⟩ : syracuseStep 1630151 = 2445227) B2445227
theorem B3466361 : Blo 479788 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B1729721 : Blo 479788 1729721 := bstep (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) B1297291
theorem B2745575 : Blo 479788 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B1371113 : Blo 479788 1371113 := bstep (se 2 (by rfl) ⟨514167, by rfl⟩ : syracuseStep 1371113 = 1028335) B1028335
theorem B1371239 : Blo 479788 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B8777081 : Blo 479788 8777081 := bstep (se 2 (by rfl) ⟨3291405, by rfl⟩ : syracuseStep 8777081 = 6582811) B6582811
theorem B15855659 : Blo 479788 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B6942995 : Blo 479788 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B3567997 : Blo 479788 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B815663 : Blo 479788 815663 := bstep (se 1 (by rfl) ⟨611747, by rfl⟩ : syracuseStep 815663 = 1223495) B1223495
theorem B1832159 : Blo 479788 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B5273119 : Blo 479788 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B4945855 : Blo 479788 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B915563 : Blo 479788 915563 := bstep (se 1 (by rfl) ⟨686672, by rfl⟩ : syracuseStep 915563 = 1373345) B1373345
theorem B720623 : Blo 479788 720623 := bstep (se 1 (by rfl) ⟨540467, by rfl⟩ : syracuseStep 720623 = 1080935) B1080935
theorem B721193 : Blo 479788 721193 := bstep (se 2 (by rfl) ⟨270447, by rfl⟩ : syracuseStep 721193 = 540895) B540895
theorem B33719747 : Blo 479788 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B9243629 : Blo 479788 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B1086767 : Blo 479788 1086767 := bstep (se 1 (by rfl) ⟨815075, by rfl⟩ : syracuseStep 1086767 = 1630151) B1630151
theorem B4757329 : Blo 479788 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B4397921 : Blo 479788 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B6594473 : Blo 479788 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B28123301 : Blo 479788 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B4628663 : Blo 479788 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B7152083 : Blo 479788 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B8757881 : Blo 479788 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B1221439 : Blo 479788 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B13906039 : Blo 479788 13906039 := bstep (se 1 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 13906039 = 20859059) B20859059
theorem B2601503 : Blo 479788 2601503 := bstep (se 1 (by rfl) ⟨1951127, by rfl⟩ : syracuseStep 2601503 = 3902255) B3902255
theorem B15577865 : Blo 479788 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B2441501 : Blo 479788 2441501 := bstep (se 3 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 2441501 = 915563) B915563
theorem B4637807 : Blo 479788 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B5851387 : Blo 479788 5851387 := bstep (se 1 (by rfl) ⟨4388540, by rfl⟩ : syracuseStep 5851387 = 8777081) B8777081
theorem B10570439 : Blo 479788 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B543775 : Blo 479788 543775 := bstep (se 1 (by rfl) ⟨407831, by rfl⟩ : syracuseStep 543775 = 815663) B815663
theorem B1626209 : Blo 479788 1626209 := bstep (se 2 (by rfl) ⟨609828, by rfl⟩ : syracuseStep 1626209 = 1219657) B1219657
theorem B480415 : Blo 479788 480415 := bstep (se 1 (by rfl) ⟨360311, by rfl⟩ : syracuseStep 480415 = 720623) B720623
theorem B1824383 : Blo 479788 1824383 := bstep (se 1 (by rfl) ⟨1368287, by rfl⟩ : syracuseStep 1824383 = 2736575) B2736575
theorem B481959 : Blo 479788 481959 := bstep (se 1 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 481959 = 722939) B722939
theorem B2448467 : Blo 479788 2448467 := bstep (se 1 (by rfl) ⟨1836350, by rfl⟩ : syracuseStep 2448467 = 3672701) B3672701
theorem B482751 : Blo 479788 482751 := bstep (se 1 (by rfl) ⟨362063, by rfl⟩ : syracuseStep 482751 = 724127) B724127
theorem B9494441 : Blo 479788 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B483263 : Blo 479788 483263 := bstep (se 1 (by rfl) ⟨362447, by rfl⟩ : syracuseStep 483263 = 724895) B724895
theorem B1630367 : Blo 479788 1630367 := bstep (se 1 (by rfl) ⟨1222775, by rfl⟩ : syracuseStep 1630367 = 2445551) B2445551
theorem B483611 : Blo 479788 483611 := bstep (se 1 (by rfl) ⟨362708, by rfl⟩ : syracuseStep 483611 = 725417) B725417
theorem B4612589 : Blo 479788 4612589 := bstep (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) B1729721
theorem B812315 : Blo 479788 812315 := bstep (se 1 (by rfl) ⟨609236, by rfl⟩ : syracuseStep 812315 = 1218473) B1218473
theorem B1830383 : Blo 479788 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B5206463 : Blo 479788 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B914075 : Blo 479788 914075 := bstep (se 1 (by rfl) ⟨685556, by rfl⟩ : syracuseStep 914075 = 1371113) B1371113
theorem B914159 : Blo 479788 914159 := bstep (se 1 (by rfl) ⟨685619, by rfl⟩ : syracuseStep 914159 = 1371239) B1371239
theorem B1537211 : Blo 479788 1537211 := bstep (se 1 (by rfl) ⟨1152908, by rfl⟩ : syracuseStep 1537211 = 2305817) B2305817
theorem B8813063 : Blo 479788 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B7046959 : Blo 479788 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B6162419 : Blo 479788 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B1084139 : Blo 479788 1084139 := bstep (se 1 (by rfl) ⟨813104, by rfl⟩ : syracuseStep 1084139 = 1626209) B1626209
theorem B7801849 : Blo 479788 7801849 := bstep (se 2 (by rfl) ⟨2925693, by rfl⟩ : syracuseStep 7801849 = 5851387) B5851387
theorem B724511 : Blo 479788 724511 := bstep (se 1 (by rfl) ⟨543383, by rfl⟩ : syracuseStep 724511 = 1086767) B1086767
theorem B1216255 : Blo 479788 1216255 := bstep (se 1 (by rfl) ⟨912191, by rfl⟩ : syracuseStep 1216255 = 1824383) B1824383
theorem B89919325 : Blo 479788 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B725033 : Blo 479788 725033 := bstep (se 2 (by rfl) ⟨271887, by rfl⟩ : syracuseStep 725033 = 543775) B543775
theorem B6329627 : Blo 479788 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B4396315 : Blo 479788 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B1086911 : Blo 479788 1086911 := bstep (se 1 (by rfl) ⟨815183, by rfl⟩ : syracuseStep 1086911 = 1630367) B1630367
theorem B18748867 : Blo 479788 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B3085775 : Blo 479788 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B5838587 : Blo 479788 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B23501501 : Blo 479788 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B1220255 : Blo 479788 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B1024807 : Blo 479788 1024807 := bstep (se 1 (by rfl) ⟨768605, by rfl⟩ : syracuseStep 1024807 = 1537211) B1537211
theorem B3091871 : Blo 479788 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B2931947 : Blo 479788 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B4768055 : Blo 479788 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B541543 : Blo 479788 541543 := bstep (se 1 (by rfl) ⟨406157, by rfl⟩ : syracuseStep 541543 = 812315) B812315
theorem B6343105 : Blo 479788 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B609383 : Blo 479788 609383 := bstep (se 1 (by rfl) ⟨457037, by rfl⟩ : syracuseStep 609383 = 914075) B914075
theorem B609439 : Blo 479788 609439 := bstep (se 1 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 609439 = 914159) B914159
theorem B1627667 : Blo 479788 1627667 := bstep (se 1 (by rfl) ⟨1220750, by rfl⟩ : syracuseStep 1627667 = 2441501) B2441501
theorem B480795 : Blo 479788 480795 := bstep (se 1 (by rfl) ⟨360596, by rfl⟩ : syracuseStep 480795 = 721193) B721193
theorem B1628585 : Blo 479788 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B1632311 : Blo 479788 1632311 := bstep (se 1 (by rfl) ⟨1224233, by rfl⟩ : syracuseStep 1632311 = 2448467) B2448467
theorem B18541385 : Blo 479788 18541385 := bstep (se 2 (by rfl) ⟨6953019, by rfl⟩ : syracuseStep 18541385 = 13906039) B13906039
theorem B3075059 : Blo 479788 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B3470975 : Blo 479788 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B1734335 : Blo 479788 1734335 := bstep (se 1 (by rfl) ⟨1300751, by rfl⟩ : syracuseStep 1734335 = 2601503) B2601503
theorem B10385243 : Blo 479788 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B3178703 : Blo 479788 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B722057 : Blo 479788 722057 := bstep (se 2 (by rfl) ⟨270771, by rfl⟩ : syracuseStep 722057 = 541543) B541543
theorem B722759 : Blo 479788 722759 := bstep (se 1 (by rfl) ⟨542069, by rfl⟩ : syracuseStep 722759 = 1084139) B1084139
theorem B8457473 : Blo 479788 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B724607 : Blo 479788 724607 := bstep (se 1 (by rfl) ⟨543455, by rfl⟩ : syracuseStep 724607 = 1086911) B1086911
theorem B1085111 : Blo 479788 1085111 := bstep (se 1 (by rfl) ⟨813833, by rfl⟩ : syracuseStep 1085111 = 1627667) B1627667
theorem B1085723 : Blo 479788 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B15667667 : Blo 479788 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B1088207 : Blo 479788 1088207 := bstep (se 1 (by rfl) ⟨816155, by rfl⟩ : syracuseStep 1088207 = 1632311) B1632311
theorem B12360923 : Blo 479788 12360923 := bstep (se 1 (by rfl) ⟨9270692, by rfl⟩ : syracuseStep 12360923 = 18541385) B18541385
theorem B1156223 : Blo 479788 1156223 := bstep (se 1 (by rfl) ⟨867167, by rfl⟩ : syracuseStep 1156223 = 1734335) B1734335
theorem B6923495 : Blo 479788 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B479569733 : Blo 479788 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B4108279 : Blo 479788 4108279 := bstep (se 1 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 4108279 = 6162419) B6162419
theorem B10402465 : Blo 479788 10402465 := bstep (se 2 (by rfl) ⟨3900924, by rfl⟩ : syracuseStep 10402465 = 7801849) B7801849
theorem B1621673 : Blo 479788 1621673 := bstep (se 2 (by rfl) ⟨608127, by rfl⟩ : syracuseStep 1621673 = 1216255) B1216255
theorem B2050039 : Blo 479788 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B1625021 : Blo 479788 1625021 := bstep (se 3 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 1625021 = 609383) B609383
theorem B8244989 : Blo 479788 8244989 := bstep (se 3 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 8244989 = 3091871) B3091871
theorem B2313983 : Blo 479788 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B1954631 : Blo 479788 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B1366409 : Blo 479788 1366409 := bstep (se 2 (by rfl) ⟨512403, by rfl⟩ : syracuseStep 1366409 = 1024807) B1024807
theorem B483007 : Blo 479788 483007 := bstep (se 1 (by rfl) ⟨362255, by rfl⟩ : syracuseStep 483007 = 724511) B724511
theorem B9395945 : Blo 479788 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B483355 : Blo 479788 483355 := bstep (se 1 (by rfl) ⟨362516, by rfl⟩ : syracuseStep 483355 = 725033) B725033
theorem B4219751 : Blo 479788 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B2057183 : Blo 479788 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B3892391 : Blo 479788 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B812585 : Blo 479788 812585 := bstep (se 2 (by rfl) ⟨304719, by rfl⟩ : syracuseStep 812585 = 609439) B609439
theorem B813503 : Blo 479788 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B5861753 : Blo 479788 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B24998489 : Blo 479788 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B1083347 : Blo 479788 1083347 := bstep (se 1 (by rfl) ⟨812510, by rfl⟩ : syracuseStep 1083347 = 1625021) B1625021
theorem B5212349 : Blo 479788 5212349 := bstep (se 3 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 5212349 = 1954631) B1954631
theorem B723407 : Blo 479788 723407 := bstep (se 1 (by rfl) ⟨542555, by rfl⟩ : syracuseStep 723407 = 1085111) B1085111
theorem B1542655 : Blo 479788 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B723815 : Blo 479788 723815 := bstep (se 1 (by rfl) ⟨542861, by rfl⟩ : syracuseStep 723815 = 1085723) B1085723
theorem B725471 : Blo 479788 725471 := bstep (se 1 (by rfl) ⟨544103, by rfl⟩ : syracuseStep 725471 = 1088207) B1088207
theorem B6263963 : Blo 479788 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B5477705 : Blo 479788 5477705 := bstep (se 2 (by rfl) ⟨2054139, by rfl⟩ : syracuseStep 5477705 = 4108279) B4108279
theorem B2594927 : Blo 479788 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B3907835 : Blo 479788 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B22553261 : Blo 479788 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B13869953 : Blo 479788 13869953 := bstep (se 2 (by rfl) ⟨5201232, by rfl⟩ : syracuseStep 13869953 = 10402465) B10402465
theorem B2733385 : Blo 479788 2733385 := bstep (se 2 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 2733385 = 2050039) B2050039
theorem B18462653 : Blo 479788 18462653 := bstep (se 3 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 18462653 = 6923495) B6923495
theorem B180042709 : Blo 479788 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B8240615 : Blo 479788 8240615 := bstep (se 1 (by rfl) ⟨6180461, by rfl⟩ : syracuseStep 8240615 = 12360923) B12360923
theorem B770815 : Blo 479788 770815 := bstep (se 1 (by rfl) ⟨578111, by rfl⟩ : syracuseStep 770815 = 1156223) B1156223
theorem B541723 : Blo 479788 541723 := bstep (se 1 (by rfl) ⟨406292, by rfl⟩ : syracuseStep 541723 = 812585) B812585
theorem B542335 : Blo 479788 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B16665659 : Blo 479788 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B2119135 : Blo 479788 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B481371 : Blo 479788 481371 := bstep (se 1 (by rfl) ⟨361028, by rfl⟩ : syracuseStep 481371 = 722057) B722057
theorem B481839 : Blo 479788 481839 := bstep (se 1 (by rfl) ⟨361379, by rfl⟩ : syracuseStep 481839 = 722759) B722759
theorem B483071 : Blo 479788 483071 := bstep (se 1 (by rfl) ⟨362303, by rfl⟩ : syracuseStep 483071 = 724607) B724607
theorem B5496659 : Blo 479788 5496659 := bstep (se 1 (by rfl) ⟨4122494, by rfl⟩ : syracuseStep 5496659 = 8244989) B8244989
theorem B10445111 : Blo 479788 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B910939 : Blo 479788 910939 := bstep (se 1 (by rfl) ⟨683204, by rfl⟩ : syracuseStep 910939 = 1366409) B1366409
theorem B1371455 : Blo 479788 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B319713155 : Blo 479788 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B1081115 : Blo 479788 1081115 := bstep (se 1 (by rfl) ⟨810836, by rfl⟩ : syracuseStep 1081115 = 1621673) B1621673
theorem B722231 : Blo 479788 722231 := bstep (se 1 (by rfl) ⟨541673, by rfl⟩ : syracuseStep 722231 = 1083347) B1083347
theorem B722297 : Blo 479788 722297 := bstep (se 2 (by rfl) ⟨270861, by rfl⟩ : syracuseStep 722297 = 541723) B541723
theorem B3474899 : Blo 479788 3474899 := bstep (se 1 (by rfl) ⟨2606174, by rfl⟩ : syracuseStep 3474899 = 5212349) B5212349
theorem B11110439 : Blo 479788 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B1214585 : Blo 479788 1214585 := bstep (se 2 (by rfl) ⟨455469, by rfl⟩ : syracuseStep 1214585 = 910939) B910939
theorem B723113 : Blo 479788 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B8227493 : Blo 479788 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B6919805 : Blo 479788 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B9246635 : Blo 479788 9246635 := bstep (se 1 (by rfl) ⟨6934976, by rfl⟩ : syracuseStep 9246635 = 13869953) B13869953
theorem B3644513 : Blo 479788 3644513 := bstep (se 2 (by rfl) ⟨1366692, by rfl⟩ : syracuseStep 3644513 = 2733385) B2733385
theorem B2825513 : Blo 479788 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B4175975 : Blo 479788 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B3651803 : Blo 479788 3651803 := bstep (se 1 (by rfl) ⟨2738852, by rfl⟩ : syracuseStep 3651803 = 5477705) B5477705
theorem B4111013 : Blo 479788 4111013 := bstep (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) B770815
theorem B2605223 : Blo 479788 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B6963407 : Blo 479788 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B213142103 : Blo 479788 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B12308435 : Blo 479788 12308435 := bstep (se 1 (by rfl) ⟨9231326, by rfl⟩ : syracuseStep 12308435 = 18462653) B18462653
theorem B5493743 : Blo 479788 5493743 := bstep (se 1 (by rfl) ⟨4120307, by rfl⟩ : syracuseStep 5493743 = 8240615) B8240615
theorem B482271 : Blo 479788 482271 := bstep (se 1 (by rfl) ⟨361703, by rfl⟩ : syracuseStep 482271 = 723407) B723407
theorem B482543 : Blo 479788 482543 := bstep (se 1 (by rfl) ⟨361907, by rfl⟩ : syracuseStep 482543 = 723815) B723815
theorem B483647 : Blo 479788 483647 := bstep (se 1 (by rfl) ⟨362735, by rfl⟩ : syracuseStep 483647 = 725471) B725471
theorem B3664439 : Blo 479788 3664439 := bstep (se 1 (by rfl) ⟨2748329, by rfl⟩ : syracuseStep 3664439 = 5496659) B5496659
theorem B15035507 : Blo 479788 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B914303 : Blo 479788 914303 := bstep (se 1 (by rfl) ⟨685727, by rfl⟩ : syracuseStep 914303 = 1371455) B1371455
theorem B240056945 : Blo 479788 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B720743 : Blo 479788 720743 := bstep (se 1 (by rfl) ⟨540557, by rfl⟩ : syracuseStep 720743 = 1081115) B1081115
theorem B1736815 : Blo 479788 1736815 := bstep (se 1 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 1736815 = 2605223) B2605223
theorem B7406959 : Blo 479788 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B6164423 : Blo 479788 6164423 := bstep (se 1 (by rfl) ⟨4623317, by rfl⟩ : syracuseStep 6164423 = 9246635) B9246635
theorem B2429675 : Blo 479788 2429675 := bstep (se 1 (by rfl) ⟨1822256, by rfl⟩ : syracuseStep 2429675 = 3644513) B3644513
theorem B2434535 : Blo 479788 2434535 := bstep (se 1 (by rfl) ⟨1825901, by rfl⟩ : syracuseStep 2434535 = 3651803) B3651803
theorem B142094735 : Blo 479788 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B5484995 : Blo 479788 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B8205623 : Blo 479788 8205623 := bstep (se 1 (by rfl) ⟨6154217, by rfl⟩ : syracuseStep 8205623 = 12308435) B12308435
theorem B1883675 : Blo 479788 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B2442959 : Blo 479788 2442959 := bstep (se 1 (by rfl) ⟨1832219, by rfl⟩ : syracuseStep 2442959 = 3664439) B3664439
theorem B609535 : Blo 479788 609535 := bstep (se 1 (by rfl) ⟨457151, by rfl⟩ : syracuseStep 609535 = 914303) B914303
theorem B2740675 : Blo 479788 2740675 := bstep (se 1 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 2740675 = 4111013) B4111013
theorem B480495 : Blo 479788 480495 := bstep (se 1 (by rfl) ⟨360371, by rfl⟩ : syracuseStep 480495 = 720743) B720743
theorem B4642271 : Blo 479788 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B481487 : Blo 479788 481487 := bstep (se 1 (by rfl) ⟨361115, by rfl⟩ : syracuseStep 481487 = 722231) B722231
theorem B481531 : Blo 479788 481531 := bstep (se 1 (by rfl) ⟨361148, by rfl⟩ : syracuseStep 481531 = 722297) B722297
theorem B2316599 : Blo 479788 2316599 := bstep (se 1 (by rfl) ⟨1737449, by rfl⟩ : syracuseStep 2316599 = 3474899) B3474899
theorem B809723 : Blo 479788 809723 := bstep (se 1 (by rfl) ⟨607292, by rfl⟩ : syracuseStep 809723 = 1214585) B1214585
theorem B482075 : Blo 479788 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B3662495 : Blo 479788 3662495 := bstep (se 1 (by rfl) ⟨2746871, by rfl⟩ : syracuseStep 3662495 = 5493743) B5493743
theorem B4613203 : Blo 479788 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B10023671 : Blo 479788 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B2783983 : Blo 479788 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B160037963 : Blo 479788 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B1544399 : Blo 479788 1544399 := bstep (se 1 (by rfl) ⟨1158299, by rfl⟩ : syracuseStep 1544399 = 2316599) B2316599
theorem B3711977 : Blo 479788 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B1255783 : Blo 479788 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B9875945 : Blo 479788 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B4109615 : Blo 479788 4109615 := bstep (se 1 (by rfl) ⟨3082211, by rfl⟩ : syracuseStep 4109615 = 6164423) B6164423
theorem B1619783 : Blo 479788 1619783 := bstep (se 1 (by rfl) ⟨1214837, by rfl⟩ : syracuseStep 1619783 = 2429675) B2429675
theorem B3094847 : Blo 479788 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B539815 : Blo 479788 539815 := bstep (se 1 (by rfl) ⟨404861, by rfl⟩ : syracuseStep 539815 = 809723) B809723
theorem B2441663 : Blo 479788 2441663 := bstep (se 1 (by rfl) ⟨1831247, by rfl⟩ : syracuseStep 2441663 = 3662495) B3662495
theorem B3654233 : Blo 479788 3654233 := bstep (se 2 (by rfl) ⟨1370337, by rfl⟩ : syracuseStep 3654233 = 2740675) B2740675
theorem B1623023 : Blo 479788 1623023 := bstep (se 1 (by rfl) ⟨1217267, by rfl⟩ : syracuseStep 1623023 = 2434535) B2434535
theorem B3656663 : Blo 479788 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B2315753 : Blo 479788 2315753 := bstep (se 2 (by rfl) ⟨868407, by rfl⟩ : syracuseStep 2315753 = 1736815) B1736815
theorem B1628639 : Blo 479788 1628639 := bstep (se 1 (by rfl) ⟨1221479, by rfl⟩ : syracuseStep 1628639 = 2442959) B2442959
theorem B6150937 : Blo 479788 6150937 := bstep (se 2 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 6150937 = 4613203) B4613203
theorem B812713 : Blo 479788 812713 := bstep (se 2 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 812713 = 609535) B609535
theorem B94729823 : Blo 479788 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B6682447 : Blo 479788 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B5470415 : Blo 479788 5470415 := bstep (se 1 (by rfl) ⟨4102811, by rfl⟩ : syracuseStep 5470415 = 8205623) B8205623
theorem B106691975 : Blo 479788 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B1082015 : Blo 479788 1082015 := bstep (se 1 (by rfl) ⟨811511, by rfl⟩ : syracuseStep 1082015 = 1623023) B1623023
theorem B1083617 : Blo 479788 1083617 := bstep (se 2 (by rfl) ⟨406356, by rfl⟩ : syracuseStep 1083617 = 812713) B812713
theorem B1674377 : Blo 479788 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B1543835 : Blo 479788 1543835 := bstep (se 1 (by rfl) ⟨1157876, by rfl⟩ : syracuseStep 1543835 = 2315753) B2315753
theorem B1085759 : Blo 479788 1085759 := bstep (se 1 (by rfl) ⟨814319, by rfl⟩ : syracuseStep 1085759 = 1628639) B1628639
theorem B8201249 : Blo 479788 8201249 := bstep (se 2 (by rfl) ⟨3075468, by rfl⟩ : syracuseStep 8201249 = 6150937) B6150937
theorem B63153215 : Blo 479788 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B3646943 : Blo 479788 3646943 := bstep (se 1 (by rfl) ⟨2735207, by rfl⟩ : syracuseStep 3646943 = 5470415) B5470415
theorem B2436155 : Blo 479788 2436155 := bstep (se 1 (by rfl) ⟨1827116, by rfl⟩ : syracuseStep 2436155 = 3654233) B3654233
theorem B2437775 : Blo 479788 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B1029599 : Blo 479788 1029599 := bstep (se 1 (by rfl) ⟨772199, by rfl⟩ : syracuseStep 1029599 = 1544399) B1544399
theorem B2474651 : Blo 479788 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B2739743 : Blo 479788 2739743 := bstep (se 1 (by rfl) ⟨2054807, by rfl⟩ : syracuseStep 2739743 = 4109615) B4109615
theorem B71127983 : Blo 479788 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B1627775 : Blo 479788 1627775 := bstep (se 1 (by rfl) ⟨1220831, by rfl⟩ : syracuseStep 1627775 = 2441663) B2441663
theorem B26335853 : Blo 479788 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B8909929 : Blo 479788 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B1079855 : Blo 479788 1079855 := bstep (se 1 (by rfl) ⟨809891, by rfl⟩ : syracuseStep 1079855 = 1619783) B1619783
theorem B2063231 : Blo 479788 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B719753 : Blo 479788 719753 := bstep (se 2 (by rfl) ⟨269907, by rfl⟩ : syracuseStep 719753 = 539815) B539815
theorem B721343 : Blo 479788 721343 := bstep (se 1 (by rfl) ⟨541007, by rfl⟩ : syracuseStep 721343 = 1082015) B1082015
theorem B722411 : Blo 479788 722411 := bstep (se 1 (by rfl) ⟨541808, by rfl⟩ : syracuseStep 722411 = 1083617) B1083617
theorem B1116251 : Blo 479788 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B723839 : Blo 479788 723839 := bstep (se 1 (by rfl) ⟨542879, by rfl⟩ : syracuseStep 723839 = 1085759) B1085759
theorem B47418655 : Blo 479788 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B1085183 : Blo 479788 1085183 := bstep (se 1 (by rfl) ⟨813887, by rfl⟩ : syracuseStep 1085183 = 1627775) B1627775
theorem B2431295 : Blo 479788 2431295 := bstep (se 1 (by rfl) ⟨1823471, by rfl⟩ : syracuseStep 2431295 = 3646943) B3646943
theorem B6599069 : Blo 479788 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B1029223 : Blo 479788 1029223 := bstep (se 1 (by rfl) ⟨771917, by rfl⟩ : syracuseStep 1029223 = 1543835) B1543835
theorem B11879905 : Blo 479788 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B1624103 : Blo 479788 1624103 := bstep (se 1 (by rfl) ⟨1218077, by rfl⟩ : syracuseStep 1624103 = 2436155) B2436155
theorem B1625183 : Blo 479788 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B479835 : Blo 479788 479835 := bstep (se 1 (by rfl) ⟨359876, by rfl⟩ : syracuseStep 479835 = 719753) B719753
theorem B1826495 : Blo 479788 1826495 := bstep (se 1 (by rfl) ⟨1369871, by rfl⟩ : syracuseStep 1826495 = 2739743) B2739743
theorem B17557235 : Blo 479788 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B5467499 : Blo 479788 5467499 := bstep (se 1 (by rfl) ⟨4100624, by rfl⟩ : syracuseStep 5467499 = 8201249) B8201249
theorem B42102143 : Blo 479788 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B686399 : Blo 479788 686399 := bstep (se 1 (by rfl) ⟨514799, by rfl⟩ : syracuseStep 686399 = 1029599) B1029599
theorem B719903 : Blo 479788 719903 := bstep (se 1 (by rfl) ⟨539927, by rfl⟩ : syracuseStep 719903 = 1079855) B1079855
theorem B1375487 : Blo 479788 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B1082735 : Blo 479788 1082735 := bstep (se 1 (by rfl) ⟨812051, by rfl⟩ : syracuseStep 1082735 = 1624103) B1624103
theorem B1083455 : Blo 479788 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B723455 : Blo 479788 723455 := bstep (se 1 (by rfl) ⟨542591, by rfl⟩ : syracuseStep 723455 = 1085183) B1085183
theorem B1217663 : Blo 479788 1217663 := bstep (se 1 (by rfl) ⟨913247, by rfl⟩ : syracuseStep 1217663 = 1826495) B1826495
theorem B11704823 : Blo 479788 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B3644999 : Blo 479788 3644999 := bstep (se 1 (by rfl) ⟨2733749, by rfl⟩ : syracuseStep 3644999 = 5467499) B5467499
theorem B4399379 : Blo 479788 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B15839873 : Blo 479788 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B1620863 : Blo 479788 1620863 := bstep (se 1 (by rfl) ⟨1215647, by rfl⟩ : syracuseStep 1620863 = 2431295) B2431295
theorem B63224873 : Blo 479788 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B28068095 : Blo 479788 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B479935 : Blo 479788 479935 := bstep (se 1 (by rfl) ⟨359951, by rfl⟩ : syracuseStep 479935 = 719903) B719903
theorem B480895 : Blo 479788 480895 := bstep (se 1 (by rfl) ⟨360671, by rfl⟩ : syracuseStep 480895 = 721343) B721343
theorem B481607 : Blo 479788 481607 := bstep (se 1 (by rfl) ⟨361205, by rfl⟩ : syracuseStep 481607 = 722411) B722411
theorem B744167 : Blo 479788 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B482559 : Blo 479788 482559 := bstep (se 1 (by rfl) ⟨361919, by rfl⟩ : syracuseStep 482559 = 723839) B723839
theorem B1830397 : Blo 479788 1830397 := bstep (se 3 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 1830397 = 686399) B686399
theorem B1372297 : Blo 479788 1372297 := bstep (se 2 (by rfl) ⟨514611, by rfl⟩ : syracuseStep 1372297 = 1029223) B1029223
theorem B916991 : Blo 479788 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B721823 : Blo 479788 721823 := bstep (se 1 (by rfl) ⟨541367, by rfl⟩ : syracuseStep 721823 = 1082735) B1082735
theorem B722303 : Blo 479788 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B18712063 : Blo 479788 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B7803215 : Blo 479788 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B2429999 : Blo 479788 2429999 := bstep (se 1 (by rfl) ⟨1822499, by rfl⟩ : syracuseStep 2429999 = 3644999) B3644999
theorem B10559915 : Blo 479788 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B42149915 : Blo 479788 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B2440529 : Blo 479788 2440529 := bstep (se 2 (by rfl) ⟨915198, by rfl⟩ : syracuseStep 2440529 = 1830397) B1830397
theorem B2932919 : Blo 479788 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B1984445 : Blo 479788 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B611327 : Blo 479788 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B482303 : Blo 479788 482303 := bstep (se 1 (by rfl) ⟨361727, by rfl⟩ : syracuseStep 482303 = 723455) B723455
theorem B811775 : Blo 479788 811775 := bstep (se 1 (by rfl) ⟨608831, by rfl⟩ : syracuseStep 811775 = 1217663) B1217663
theorem B1829729 : Blo 479788 1829729 := bstep (se 2 (by rfl) ⟨686148, by rfl⟩ : syracuseStep 1829729 = 1372297) B1372297
theorem B1080575 : Blo 479788 1080575 := bstep (se 1 (by rfl) ⟨810431, by rfl⟩ : syracuseStep 1080575 = 1620863) B1620863
theorem B1219819 : Blo 479788 1219819 := bstep (se 1 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 1219819 = 1829729) B1829729
theorem B1322963 : Blo 479788 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B24949417 : Blo 479788 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B1619999 : Blo 479788 1619999 := bstep (se 1 (by rfl) ⟨1214999, by rfl⟩ : syracuseStep 1619999 = 2429999) B2429999
theorem B541183 : Blo 479788 541183 := bstep (se 1 (by rfl) ⟨405887, by rfl⟩ : syracuseStep 541183 = 811775) B811775
theorem B28099943 : Blo 479788 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B1627019 : Blo 479788 1627019 := bstep (se 1 (by rfl) ⟨1220264, by rfl⟩ : syracuseStep 1627019 = 2440529) B2440529
theorem B1955279 : Blo 479788 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B481215 : Blo 479788 481215 := bstep (se 1 (by rfl) ⟨360911, by rfl⟩ : syracuseStep 481215 = 721823) B721823
theorem B481535 : Blo 479788 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B1630205 : Blo 479788 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B5202143 : Blo 479788 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B7039943 : Blo 479788 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B720383 : Blo 479788 720383 := bstep (se 1 (by rfl) ⟨540287, by rfl⟩ : syracuseStep 720383 = 1080575) B1080575
theorem B721577 : Blo 479788 721577 := bstep (se 2 (by rfl) ⟨270591, by rfl⟩ : syracuseStep 721577 = 541183) B541183
theorem B1084679 : Blo 479788 1084679 := bstep (se 1 (by rfl) ⟨813509, by rfl⟩ : syracuseStep 1084679 = 1627019) B1627019
theorem B1086803 : Blo 479788 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B33265889 : Blo 479788 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B4693295 : Blo 479788 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B1626425 : Blo 479788 1626425 := bstep (se 2 (by rfl) ⟨609909, by rfl⟩ : syracuseStep 1626425 = 1219819) B1219819
theorem B480255 : Blo 479788 480255 := bstep (se 1 (by rfl) ⟨360191, by rfl⟩ : syracuseStep 480255 = 720383) B720383
theorem B18733295 : Blo 479788 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B1303519 : Blo 479788 1303519 := bstep (se 1 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 1303519 = 1955279) B1955279
theorem B3468095 : Blo 479788 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B881975 : Blo 479788 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B1079999 : Blo 479788 1079999 := bstep (se 1 (by rfl) ⟨809999, by rfl⟩ : syracuseStep 1079999 = 1619999) B1619999
theorem B1738025 : Blo 479788 1738025 := bstep (se 2 (by rfl) ⟨651759, by rfl⟩ : syracuseStep 1738025 = 1303519) B1303519
theorem B723119 : Blo 479788 723119 := bstep (se 1 (by rfl) ⟨542339, by rfl⟩ : syracuseStep 723119 = 1084679) B1084679
theorem B1084283 : Blo 479788 1084283 := bstep (se 1 (by rfl) ⟨813212, by rfl⟩ : syracuseStep 1084283 = 1626425) B1626425
theorem B724535 : Blo 479788 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B3128863 : Blo 479788 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B49955453 : Blo 479788 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B2312063 : Blo 479788 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B481051 : Blo 479788 481051 := bstep (se 1 (by rfl) ⟨360788, by rfl⟩ : syracuseStep 481051 = 721577) B721577
theorem B22177259 : Blo 479788 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B587983 : Blo 479788 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B719999 : Blo 479788 719999 := bstep (se 1 (by rfl) ⟨539999, by rfl⟩ : syracuseStep 719999 = 1079999) B1079999
theorem B1541375 : Blo 479788 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B722855 : Blo 479788 722855 := bstep (se 1 (by rfl) ⟨542141, by rfl⟩ : syracuseStep 722855 = 1084283) B1084283
theorem B14784839 : Blo 479788 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B4171817 : Blo 479788 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B33303635 : Blo 479788 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B1158683 : Blo 479788 1158683 := bstep (se 1 (by rfl) ⟨869012, by rfl⟩ : syracuseStep 1158683 = 1738025) B1738025
theorem B479999 : Blo 479788 479999 := bstep (se 1 (by rfl) ⟨359999, by rfl⟩ : syracuseStep 479999 = 719999) B719999
theorem B482079 : Blo 479788 482079 := bstep (se 1 (by rfl) ⟨361559, by rfl⟩ : syracuseStep 482079 = 723119) B723119
theorem B483023 : Blo 479788 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B783977 : Blo 479788 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B3089821 : Blo 479788 3089821 := bstep (se 3 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 3089821 = 1158683) B1158683
theorem B1027583 : Blo 479788 1027583 := bstep (se 1 (by rfl) ⟨770687, by rfl⟩ : syracuseStep 1027583 = 1541375) B1541375
theorem B22202423 : Blo 479788 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B481903 : Blo 479788 481903 := bstep (se 1 (by rfl) ⟨361427, by rfl⟩ : syracuseStep 481903 = 722855) B722855
theorem B9856559 : Blo 479788 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B2090605 : Blo 479788 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B2781211 : Blo 479788 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B2787473 : Blo 479788 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B3708281 : Blo 479788 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B6571039 : Blo 479788 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B14801615 : Blo 479788 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B4119761 : Blo 479788 4119761 := bstep (se 2 (by rfl) ⟨1544910, by rfl⟩ : syracuseStep 4119761 = 3089821) B3089821
theorem B685055 : Blo 479788 685055 := bstep (se 1 (by rfl) ⟨513791, by rfl⟩ : syracuseStep 685055 = 1027583) B1027583
theorem B9867743 : Blo 479788 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B8761385 : Blo 479788 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B1858315 : Blo 479788 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B1826813 : Blo 479788 1826813 := bstep (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) B685055
theorem B9888749 : Blo 479788 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B2746507 : Blo 479788 2746507 := bstep (se 1 (by rfl) ⟨2059880, by rfl⟩ : syracuseStep 2746507 = 4119761) B4119761
theorem B1217875 : Blo 479788 1217875 := bstep (se 1 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 1217875 = 1826813) B1826813
theorem B6592499 : Blo 479788 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B5840923 : Blo 479788 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B2477753 : Blo 479788 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B3662009 : Blo 479788 3662009 := bstep (se 2 (by rfl) ⟨1373253, by rfl⟩ : syracuseStep 3662009 = 2746507) B2746507
theorem B6578495 : Blo 479788 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B4394999 : Blo 479788 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B1651835 : Blo 479788 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B2441339 : Blo 479788 2441339 := bstep (se 1 (by rfl) ⟨1831004, by rfl⟩ : syracuseStep 2441339 = 3662009) B3662009
theorem B1623833 : Blo 479788 1623833 := bstep (se 2 (by rfl) ⟨608937, by rfl⟩ : syracuseStep 1623833 = 1217875) B1217875
theorem B7787897 : Blo 479788 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B4385663 : Blo 479788 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B1082555 : Blo 479788 1082555 := bstep (se 1 (by rfl) ⟨811916, by rfl⟩ : syracuseStep 1082555 = 1623833) B1623833
theorem B2923775 : Blo 479788 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B5191931 : Blo 479788 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B1101223 : Blo 479788 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B11719997 : Blo 479788 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B1627559 : Blo 479788 1627559 := bstep (se 1 (by rfl) ⟨1220669, by rfl⟩ : syracuseStep 1627559 = 2441339) B2441339
theorem B721703 : Blo 479788 721703 := bstep (se 1 (by rfl) ⟨541277, by rfl⟩ : syracuseStep 721703 = 1082555) B1082555
theorem B1085039 : Blo 479788 1085039 := bstep (se 1 (by rfl) ⟨813779, by rfl⟩ : syracuseStep 1085039 = 1627559) B1627559
theorem B7813331 : Blo 479788 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B1949183 : Blo 479788 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B3461287 : Blo 479788 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B1468297 : Blo 479788 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B723359 : Blo 479788 723359 := bstep (se 1 (by rfl) ⟨542519, by rfl⟩ : syracuseStep 723359 = 1085039) B1085039
theorem B1299455 : Blo 479788 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B481135 : Blo 479788 481135 := bstep (se 1 (by rfl) ⟨360851, by rfl⟩ : syracuseStep 481135 = 721703) B721703
theorem B4615049 : Blo 479788 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B5208887 : Blo 479788 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B7830917 : Blo 479788 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B5220611 : Blo 479788 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B866303 : Blo 479788 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B482239 : Blo 479788 482239 := bstep (se 1 (by rfl) ⟨361679, by rfl⟩ : syracuseStep 482239 = 723359) B723359
theorem B3076699 : Blo 479788 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B3472591 : Blo 479788 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B4102265 : Blo 479788 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B3480407 : Blo 479788 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B4630121 : Blo 479788 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B577535 : Blo 479788 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B3086747 : Blo 479788 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B2734843 : Blo 479788 2734843 := bstep (se 1 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 2734843 = 4102265) B4102265
theorem B2320271 : Blo 479788 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B1540093 : Blo 479788 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B1546847 : Blo 479788 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B3646457 : Blo 479788 3646457 := bstep (se 2 (by rfl) ⟨1367421, by rfl⟩ : syracuseStep 3646457 = 2734843) B2734843
theorem B2053457 : Blo 479788 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B2057831 : Blo 479788 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B2430971 : Blo 479788 2430971 := bstep (se 1 (by rfl) ⟨1823228, by rfl⟩ : syracuseStep 2430971 = 3646457) B3646457
theorem B1031231 : Blo 479788 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B1368971 : Blo 479788 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B1371887 : Blo 479788 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B1620647 : Blo 479788 1620647 := bstep (se 1 (by rfl) ⟨1215485, by rfl⟩ : syracuseStep 1620647 = 2430971) B2430971
theorem B912647 : Blo 479788 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B914591 : Blo 479788 914591 := bstep (se 1 (by rfl) ⟨685943, by rfl⟩ : syracuseStep 914591 = 1371887) B1371887
theorem B2749949 : Blo 479788 2749949 := bstep (se 3 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 2749949 = 1031231) B1031231
theorem B2433725 : Blo 479788 2433725 := bstep (se 3 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 2433725 = 912647) B912647
theorem B2438909 : Blo 479788 2438909 := bstep (se 3 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 2438909 = 914591) B914591
theorem B1833299 : Blo 479788 1833299 := bstep (se 1 (by rfl) ⟨1374974, by rfl⟩ : syracuseStep 1833299 = 2749949) B2749949
theorem B1080431 : Blo 479788 1080431 := bstep (se 1 (by rfl) ⟨810323, by rfl⟩ : syracuseStep 1080431 = 1620647) B1620647
theorem B1222199 : Blo 479788 1222199 := bstep (se 1 (by rfl) ⟨916649, by rfl⟩ : syracuseStep 1222199 = 1833299) B1833299
theorem B1622483 : Blo 479788 1622483 := bstep (se 1 (by rfl) ⟨1216862, by rfl⟩ : syracuseStep 1622483 = 2433725) B2433725
theorem B1625939 : Blo 479788 1625939 := bstep (se 1 (by rfl) ⟨1219454, by rfl⟩ : syracuseStep 1625939 = 2438909) B2438909
theorem B720287 : Blo 479788 720287 := bstep (se 1 (by rfl) ⟨540215, by rfl⟩ : syracuseStep 720287 = 1080431) B1080431
theorem B1081655 : Blo 479788 1081655 := bstep (se 1 (by rfl) ⟨811241, by rfl⟩ : syracuseStep 1081655 = 1622483) B1622483
theorem B1083959 : Blo 479788 1083959 := bstep (se 1 (by rfl) ⟨812969, by rfl⟩ : syracuseStep 1083959 = 1625939) B1625939
theorem B480191 : Blo 479788 480191 := bstep (se 1 (by rfl) ⟨360143, by rfl⟩ : syracuseStep 480191 = 720287) B720287
theorem B814799 : Blo 479788 814799 := bstep (se 1 (by rfl) ⟨611099, by rfl⟩ : syracuseStep 814799 = 1222199) B1222199
theorem B721103 : Blo 479788 721103 := bstep (se 1 (by rfl) ⟨540827, by rfl⟩ : syracuseStep 721103 = 1081655) B1081655
theorem B722639 : Blo 479788 722639 := bstep (se 1 (by rfl) ⟨541979, by rfl⟩ : syracuseStep 722639 = 1083959) B1083959
theorem B543199 : Blo 479788 543199 := bstep (se 1 (by rfl) ⟨407399, by rfl⟩ : syracuseStep 543199 = 814799) B814799
theorem B724265 : Blo 479788 724265 := bstep (se 2 (by rfl) ⟨271599, by rfl⟩ : syracuseStep 724265 = 543199) B543199
theorem B480735 : Blo 479788 480735 := bstep (se 1 (by rfl) ⟨360551, by rfl⟩ : syracuseStep 480735 = 721103) B721103
theorem B481759 : Blo 479788 481759 := bstep (se 1 (by rfl) ⟨361319, by rfl⟩ : syracuseStep 481759 = 722639) B722639
theorem B482843 : Blo 479788 482843 := bstep (se 1 (by rfl) ⟨362132, by rfl⟩ : syracuseStep 482843 = 724265) B724265

theorem C0 (j : ℕ) (h1 : 119947 ≤ j) (h2 : j ≤ 120646) : Blo 479788 (4 * j + 3) := by
  interval_cases j
  · exact B479791
  · exact B479795
  · exact B479799
  · exact B479803
  · exact B479807
  · exact B479811
  · exact B479815
  · exact B479819
  · exact B479823
  · exact B479827
  · exact B479831
  · exact B479835
  · exact B479839
  · exact B479843
  · exact B479847
  · exact B479851
  · exact B479855
  · exact B479859
  · exact B479863
  · exact B479867
  · exact B479871
  · exact B479875
  · exact B479879
  · exact B479883
  · exact B479887
  · exact B479891
  · exact B479895
  · exact B479899
  · exact B479903
  · exact B479907
  · exact B479911
  · exact B479915
  · exact B479919
  · exact B479923
  · exact B479927
  · exact B479931
  · exact B479935
  · exact B479939
  · exact B479943
  · exact B479947
  · exact B479951
  · exact B479955
  · exact B479959
  · exact B479963
  · exact B479967
  · exact B479971
  · exact B479975
  · exact B479979
  · exact B479983
  · exact B479987
  · exact B479991
  · exact B479995
  · exact B479999
  · exact B480003
  · exact B480007
  · exact B480011
  · exact B480015
  · exact B480019
  · exact B480023
  · exact B480027
  · exact B480031
  · exact B480035
  · exact B480039
  · exact B480043
  · exact B480047
  · exact B480051
  · exact B480055
  · exact B480059
  · exact B480063
  · exact B480067
  · exact B480071
  · exact B480075
  · exact B480079
  · exact B480083
  · exact B480087
  · exact B480091
  · exact B480095
  · exact B480099
  · exact B480103
  · exact B480107
  · exact B480111
  · exact B480115
  · exact B480119
  · exact B480123
  · exact B480127
  · exact B480131
  · exact B480135
  · exact B480139
  · exact B480143
  · exact B480147
  · exact B480151
  · exact B480155
  · exact B480159
  · exact B480163
  · exact B480167
  · exact B480171
  · exact B480175
  · exact B480179
  · exact B480183
  · exact B480187
  · exact B480191
  · exact B480195
  · exact B480199
  · exact B480203
  · exact B480207
  · exact B480211
  · exact B480215
  · exact B480219
  · exact B480223
  · exact B480227
  · exact B480231
  · exact B480235
  · exact B480239
  · exact B480243
  · exact B480247
  · exact B480251
  · exact B480255
  · exact B480259
  · exact B480263
  · exact B480267
  · exact B480271
  · exact B480275
  · exact B480279
  · exact B480283
  · exact B480287
  · exact B480291
  · exact B480295
  · exact B480299
  · exact B480303
  · exact B480307
  · exact B480311
  · exact B480315
  · exact B480319
  · exact B480323
  · exact B480327
  · exact B480331
  · exact B480335
  · exact B480339
  · exact B480343
  · exact B480347
  · exact B480351
  · exact B480355
  · exact B480359
  · exact B480363
  · exact B480367
  · exact B480371
  · exact B480375
  · exact B480379
  · exact B480383
  · exact B480387
  · exact B480391
  · exact B480395
  · exact B480399
  · exact B480403
  · exact B480407
  · exact B480411
  · exact B480415
  · exact B480419
  · exact B480423
  · exact B480427
  · exact B480431
  · exact B480435
  · exact B480439
  · exact B480443
  · exact B480447
  · exact B480451
  · exact B480455
  · exact B480459
  · exact B480463
  · exact B480467
  · exact B480471
  · exact B480475
  · exact B480479
  · exact B480483
  · exact B480487
  · exact B480491
  · exact B480495
  · exact B480499
  · exact B480503
  · exact B480507
  · exact B480511
  · exact B480515
  · exact B480519
  · exact B480523
  · exact B480527
  · exact B480531
  · exact B480535
  · exact B480539
  · exact B480543
  · exact B480547
  · exact B480551
  · exact B480555
  · exact B480559
  · exact B480563
  · exact B480567
  · exact B480571
  · exact B480575
  · exact B480579
  · exact B480583
  · exact B480587
  · exact B480591
  · exact B480595
  · exact B480599
  · exact B480603
  · exact B480607
  · exact B480611
  · exact B480615
  · exact B480619
  · exact B480623
  · exact B480627
  · exact B480631
  · exact B480635
  · exact B480639
  · exact B480643
  · exact B480647
  · exact B480651
  · exact B480655
  · exact B480659
  · exact B480663
  · exact B480667
  · exact B480671
  · exact B480675
  · exact B480679
  · exact B480683
  · exact B480687
  · exact B480691
  · exact B480695
  · exact B480699
  · exact B480703
  · exact B480707
  · exact B480711
  · exact B480715
  · exact B480719
  · exact B480723
  · exact B480727
  · exact B480731
  · exact B480735
  · exact B480739
  · exact B480743
  · exact B480747
  · exact B480751
  · exact B480755
  · exact B480759
  · exact B480763
  · exact B480767
  · exact B480771
  · exact B480775
  · exact B480779
  · exact B480783
  · exact B480787
  · exact B480791
  · exact B480795
  · exact B480799
  · exact B480803
  · exact B480807
  · exact B480811
  · exact B480815
  · exact B480819
  · exact B480823
  · exact B480827
  · exact B480831
  · exact B480835
  · exact B480839
  · exact B480843
  · exact B480847
  · exact B480851
  · exact B480855
  · exact B480859
  · exact B480863
  · exact B480867
  · exact B480871
  · exact B480875
  · exact B480879
  · exact B480883
  · exact B480887
  · exact B480891
  · exact B480895
  · exact B480899
  · exact B480903
  · exact B480907
  · exact B480911
  · exact B480915
  · exact B480919
  · exact B480923
  · exact B480927
  · exact B480931
  · exact B480935
  · exact B480939
  · exact B480943
  · exact B480947
  · exact B480951
  · exact B480955
  · exact B480959
  · exact B480963
  · exact B480967
  · exact B480971
  · exact B480975
  · exact B480979
  · exact B480983
  · exact B480987
  · exact B480991
  · exact B480995
  · exact B480999
  · exact B481003
  · exact B481007
  · exact B481011
  · exact B481015
  · exact B481019
  · exact B481023
  · exact B481027
  · exact B481031
  · exact B481035
  · exact B481039
  · exact B481043
  · exact B481047
  · exact B481051
  · exact B481055
  · exact B481059
  · exact B481063
  · exact B481067
  · exact B481071
  · exact B481075
  · exact B481079
  · exact B481083
  · exact B481087
  · exact B481091
  · exact B481095
  · exact B481099
  · exact B481103
  · exact B481107
  · exact B481111
  · exact B481115
  · exact B481119
  · exact B481123
  · exact B481127
  · exact B481131
  · exact B481135
  · exact B481139
  · exact B481143
  · exact B481147
  · exact B481151
  · exact B481155
  · exact B481159
  · exact B481163
  · exact B481167
  · exact B481171
  · exact B481175
  · exact B481179
  · exact B481183
  · exact B481187
  · exact B481191
  · exact B481195
  · exact B481199
  · exact B481203
  · exact B481207
  · exact B481211
  · exact B481215
  · exact B481219
  · exact B481223
  · exact B481227
  · exact B481231
  · exact B481235
  · exact B481239
  · exact B481243
  · exact B481247
  · exact B481251
  · exact B481255
  · exact B481259
  · exact B481263
  · exact B481267
  · exact B481271
  · exact B481275
  · exact B481279
  · exact B481283
  · exact B481287
  · exact B481291
  · exact B481295
  · exact B481299
  · exact B481303
  · exact B481307
  · exact B481311
  · exact B481315
  · exact B481319
  · exact B481323
  · exact B481327
  · exact B481331
  · exact B481335
  · exact B481339
  · exact B481343
  · exact B481347
  · exact B481351
  · exact B481355
  · exact B481359
  · exact B481363
  · exact B481367
  · exact B481371
  · exact B481375
  · exact B481379
  · exact B481383
  · exact B481387
  · exact B481391
  · exact B481395
  · exact B481399
  · exact B481403
  · exact B481407
  · exact B481411
  · exact B481415
  · exact B481419
  · exact B481423
  · exact B481427
  · exact B481431
  · exact B481435
  · exact B481439
  · exact B481443
  · exact B481447
  · exact B481451
  · exact B481455
  · exact B481459
  · exact B481463
  · exact B481467
  · exact B481471
  · exact B481475
  · exact B481479
  · exact B481483
  · exact B481487
  · exact B481491
  · exact B481495
  · exact B481499
  · exact B481503
  · exact B481507
  · exact B481511
  · exact B481515
  · exact B481519
  · exact B481523
  · exact B481527
  · exact B481531
  · exact B481535
  · exact B481539
  · exact B481543
  · exact B481547
  · exact B481551
  · exact B481555
  · exact B481559
  · exact B481563
  · exact B481567
  · exact B481571
  · exact B481575
  · exact B481579
  · exact B481583
  · exact B481587
  · exact B481591
  · exact B481595
  · exact B481599
  · exact B481603
  · exact B481607
  · exact B481611
  · exact B481615
  · exact B481619
  · exact B481623
  · exact B481627
  · exact B481631
  · exact B481635
  · exact B481639
  · exact B481643
  · exact B481647
  · exact B481651
  · exact B481655
  · exact B481659
  · exact B481663
  · exact B481667
  · exact B481671
  · exact B481675
  · exact B481679
  · exact B481683
  · exact B481687
  · exact B481691
  · exact B481695
  · exact B481699
  · exact B481703
  · exact B481707
  · exact B481711
  · exact B481715
  · exact B481719
  · exact B481723
  · exact B481727
  · exact B481731
  · exact B481735
  · exact B481739
  · exact B481743
  · exact B481747
  · exact B481751
  · exact B481755
  · exact B481759
  · exact B481763
  · exact B481767
  · exact B481771
  · exact B481775
  · exact B481779
  · exact B481783
  · exact B481787
  · exact B481791
  · exact B481795
  · exact B481799
  · exact B481803
  · exact B481807
  · exact B481811
  · exact B481815
  · exact B481819
  · exact B481823
  · exact B481827
  · exact B481831
  · exact B481835
  · exact B481839
  · exact B481843
  · exact B481847
  · exact B481851
  · exact B481855
  · exact B481859
  · exact B481863
  · exact B481867
  · exact B481871
  · exact B481875
  · exact B481879
  · exact B481883
  · exact B481887
  · exact B481891
  · exact B481895
  · exact B481899
  · exact B481903
  · exact B481907
  · exact B481911
  · exact B481915
  · exact B481919
  · exact B481923
  · exact B481927
  · exact B481931
  · exact B481935
  · exact B481939
  · exact B481943
  · exact B481947
  · exact B481951
  · exact B481955
  · exact B481959
  · exact B481963
  · exact B481967
  · exact B481971
  · exact B481975
  · exact B481979
  · exact B481983
  · exact B481987
  · exact B481991
  · exact B481995
  · exact B481999
  · exact B482003
  · exact B482007
  · exact B482011
  · exact B482015
  · exact B482019
  · exact B482023
  · exact B482027
  · exact B482031
  · exact B482035
  · exact B482039
  · exact B482043
  · exact B482047
  · exact B482051
  · exact B482055
  · exact B482059
  · exact B482063
  · exact B482067
  · exact B482071
  · exact B482075
  · exact B482079
  · exact B482083
  · exact B482087
  · exact B482091
  · exact B482095
  · exact B482099
  · exact B482103
  · exact B482107
  · exact B482111
  · exact B482115
  · exact B482119
  · exact B482123
  · exact B482127
  · exact B482131
  · exact B482135
  · exact B482139
  · exact B482143
  · exact B482147
  · exact B482151
  · exact B482155
  · exact B482159
  · exact B482163
  · exact B482167
  · exact B482171
  · exact B482175
  · exact B482179
  · exact B482183
  · exact B482187
  · exact B482191
  · exact B482195
  · exact B482199
  · exact B482203
  · exact B482207
  · exact B482211
  · exact B482215
  · exact B482219
  · exact B482223
  · exact B482227
  · exact B482231
  · exact B482235
  · exact B482239
  · exact B482243
  · exact B482247
  · exact B482251
  · exact B482255
  · exact B482259
  · exact B482263
  · exact B482267
  · exact B482271
  · exact B482275
  · exact B482279
  · exact B482283
  · exact B482287
  · exact B482291
  · exact B482295
  · exact B482299
  · exact B482303
  · exact B482307
  · exact B482311
  · exact B482315
  · exact B482319
  · exact B482323
  · exact B482327
  · exact B482331
  · exact B482335
  · exact B482339
  · exact B482343
  · exact B482347
  · exact B482351
  · exact B482355
  · exact B482359
  · exact B482363
  · exact B482367
  · exact B482371
  · exact B482375
  · exact B482379
  · exact B482383
  · exact B482387
  · exact B482391
  · exact B482395
  · exact B482399
  · exact B482403
  · exact B482407
  · exact B482411
  · exact B482415
  · exact B482419
  · exact B482423
  · exact B482427
  · exact B482431
  · exact B482435
  · exact B482439
  · exact B482443
  · exact B482447
  · exact B482451
  · exact B482455
  · exact B482459
  · exact B482463
  · exact B482467
  · exact B482471
  · exact B482475
  · exact B482479
  · exact B482483
  · exact B482487
  · exact B482491
  · exact B482495
  · exact B482499
  · exact B482503
  · exact B482507
  · exact B482511
  · exact B482515
  · exact B482519
  · exact B482523
  · exact B482527
  · exact B482531
  · exact B482535
  · exact B482539
  · exact B482543
  · exact B482547
  · exact B482551
  · exact B482555
  · exact B482559
  · exact B482563
  · exact B482567
  · exact B482571
  · exact B482575
  · exact B482579
  · exact B482583
  · exact B482587

theorem C1 (j : ℕ) (h1 : 120647 ≤ j) (h2 : j ≤ 120946) : Blo 479788 (4 * j + 3) := by
  interval_cases j
  · exact B482591
  · exact B482595
  · exact B482599
  · exact B482603
  · exact B482607
  · exact B482611
  · exact B482615
  · exact B482619
  · exact B482623
  · exact B482627
  · exact B482631
  · exact B482635
  · exact B482639
  · exact B482643
  · exact B482647
  · exact B482651
  · exact B482655
  · exact B482659
  · exact B482663
  · exact B482667
  · exact B482671
  · exact B482675
  · exact B482679
  · exact B482683
  · exact B482687
  · exact B482691
  · exact B482695
  · exact B482699
  · exact B482703
  · exact B482707
  · exact B482711
  · exact B482715
  · exact B482719
  · exact B482723
  · exact B482727
  · exact B482731
  · exact B482735
  · exact B482739
  · exact B482743
  · exact B482747
  · exact B482751
  · exact B482755
  · exact B482759
  · exact B482763
  · exact B482767
  · exact B482771
  · exact B482775
  · exact B482779
  · exact B482783
  · exact B482787
  · exact B482791
  · exact B482795
  · exact B482799
  · exact B482803
  · exact B482807
  · exact B482811
  · exact B482815
  · exact B482819
  · exact B482823
  · exact B482827
  · exact B482831
  · exact B482835
  · exact B482839
  · exact B482843
  · exact B482847
  · exact B482851
  · exact B482855
  · exact B482859
  · exact B482863
  · exact B482867
  · exact B482871
  · exact B482875
  · exact B482879
  · exact B482883
  · exact B482887
  · exact B482891
  · exact B482895
  · exact B482899
  · exact B482903
  · exact B482907
  · exact B482911
  · exact B482915
  · exact B482919
  · exact B482923
  · exact B482927
  · exact B482931
  · exact B482935
  · exact B482939
  · exact B482943
  · exact B482947
  · exact B482951
  · exact B482955
  · exact B482959
  · exact B482963
  · exact B482967
  · exact B482971
  · exact B482975
  · exact B482979
  · exact B482983
  · exact B482987
  · exact B482991
  · exact B482995
  · exact B482999
  · exact B483003
  · exact B483007
  · exact B483011
  · exact B483015
  · exact B483019
  · exact B483023
  · exact B483027
  · exact B483031
  · exact B483035
  · exact B483039
  · exact B483043
  · exact B483047
  · exact B483051
  · exact B483055
  · exact B483059
  · exact B483063
  · exact B483067
  · exact B483071
  · exact B483075
  · exact B483079
  · exact B483083
  · exact B483087
  · exact B483091
  · exact B483095
  · exact B483099
  · exact B483103
  · exact B483107
  · exact B483111
  · exact B483115
  · exact B483119
  · exact B483123
  · exact B483127
  · exact B483131
  · exact B483135
  · exact B483139
  · exact B483143
  · exact B483147
  · exact B483151
  · exact B483155
  · exact B483159
  · exact B483163
  · exact B483167
  · exact B483171
  · exact B483175
  · exact B483179
  · exact B483183
  · exact B483187
  · exact B483191
  · exact B483195
  · exact B483199
  · exact B483203
  · exact B483207
  · exact B483211
  · exact B483215
  · exact B483219
  · exact B483223
  · exact B483227
  · exact B483231
  · exact B483235
  · exact B483239
  · exact B483243
  · exact B483247
  · exact B483251
  · exact B483255
  · exact B483259
  · exact B483263
  · exact B483267
  · exact B483271
  · exact B483275
  · exact B483279
  · exact B483283
  · exact B483287
  · exact B483291
  · exact B483295
  · exact B483299
  · exact B483303
  · exact B483307
  · exact B483311
  · exact B483315
  · exact B483319
  · exact B483323
  · exact B483327
  · exact B483331
  · exact B483335
  · exact B483339
  · exact B483343
  · exact B483347
  · exact B483351
  · exact B483355
  · exact B483359
  · exact B483363
  · exact B483367
  · exact B483371
  · exact B483375
  · exact B483379
  · exact B483383
  · exact B483387
  · exact B483391
  · exact B483395
  · exact B483399
  · exact B483403
  · exact B483407
  · exact B483411
  · exact B483415
  · exact B483419
  · exact B483423
  · exact B483427
  · exact B483431
  · exact B483435
  · exact B483439
  · exact B483443
  · exact B483447
  · exact B483451
  · exact B483455
  · exact B483459
  · exact B483463
  · exact B483467
  · exact B483471
  · exact B483475
  · exact B483479
  · exact B483483
  · exact B483487
  · exact B483491
  · exact B483495
  · exact B483499
  · exact B483503
  · exact B483507
  · exact B483511
  · exact B483515
  · exact B483519
  · exact B483523
  · exact B483527
  · exact B483531
  · exact B483535
  · exact B483539
  · exact B483543
  · exact B483547
  · exact B483551
  · exact B483555
  · exact B483559
  · exact B483563
  · exact B483567
  · exact B483571
  · exact B483575
  · exact B483579
  · exact B483583
  · exact B483587
  · exact B483591
  · exact B483595
  · exact B483599
  · exact B483603
  · exact B483607
  · exact B483611
  · exact B483615
  · exact B483619
  · exact B483623
  · exact B483627
  · exact B483631
  · exact B483635
  · exact B483639
  · exact B483643
  · exact B483647
  · exact B483651
  · exact B483655
  · exact B483659
  · exact B483663
  · exact B483667
  · exact B483671
  · exact B483675
  · exact B483679
  · exact B483683
  · exact B483687
  · exact B483691
  · exact B483695
  · exact B483699
  · exact B483703
  · exact B483707
  · exact B483711
  · exact B483715
  · exact B483719
  · exact B483723
  · exact B483727
  · exact B483731
  · exact B483735
  · exact B483739
  · exact B483743
  · exact B483747
  · exact B483751
  · exact B483755
  · exact B483759
  · exact B483763
  · exact B483767
  · exact B483771
  · exact B483775
  · exact B483779
  · exact B483783
  · exact B483787

theorem solution (m : ℕ) (hlo : 479788 ≤ m) (hhi : m ≤ 483788) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 119947 ≤ j := by omega
    have hj2 : j ≤ 120946 := by omega
    have hb : Blo 479788 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 120647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
