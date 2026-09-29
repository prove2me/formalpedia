-- Prove2me | solution 1 for syracuse_descends_range_928581_932581
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:55.06506+00:00
-- url     : https://prove2.me/submissions/dd598c6a-9d60-4e83-b73d-b918280a0e1a

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


theorem B1048585 : Blo 928581 1048585 := bbase (se 2 (by rfl) ⟨393219, by rfl⟩ : syracuseStep 1048585 = 786439) (by norm_num)
theorem B2097197 : Blo 928581 2097197 := bbase (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) (by norm_num)
theorem B1048621 : Blo 928581 1048621 := bbase (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) (by norm_num)
theorem B1572925 : Blo 928581 1572925 := bbase (se 3 (by rfl) ⟨294923, by rfl⟩ : syracuseStep 1572925 = 589847) (by norm_num)
theorem B1048657 : Blo 928581 1048657 := bbase (se 2 (by rfl) ⟨393246, by rfl⟩ : syracuseStep 1048657 = 786493) (by norm_num)
theorem B2097269 : Blo 928581 2097269 := bbase (se 5 (by rfl) ⟨98309, by rfl⟩ : syracuseStep 2097269 = 196619) (by norm_num)
theorem B1048693 : Blo 928581 1048693 := bbase (se 5 (by rfl) ⟨49157, by rfl⟩ : syracuseStep 1048693 = 98315) (by norm_num)
theorem B1179785 : Blo 928581 1179785 := bbase (se 2 (by rfl) ⟨442419, by rfl⟩ : syracuseStep 1179785 = 884839) (by norm_num)
theorem B3145877 : Blo 928581 3145877 := bbase (se 6 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 3145877 = 147463) (by norm_num)
theorem B1573013 : Blo 928581 1573013 := bbase (se 6 (by rfl) ⟨36867, by rfl⟩ : syracuseStep 1573013 = 73735) (by norm_num)
theorem B1048729 : Blo 928581 1048729 := bbase (se 2 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 1048729 = 786547) (by norm_num)
theorem B2359469 : Blo 928581 2359469 := bbase (se 3 (by rfl) ⟨442400, by rfl⟩ : syracuseStep 2359469 = 884801) (by norm_num)
theorem B2097341 : Blo 928581 2097341 := bbase (se 3 (by rfl) ⟨393251, by rfl⟩ : syracuseStep 2097341 = 786503) (by norm_num)
theorem B1048765 : Blo 928581 1048765 := bbase (se 3 (by rfl) ⟨196643, by rfl⟩ : syracuseStep 1048765 = 393287) (by norm_num)
theorem B1179841 : Blo 928581 1179841 := bbase (se 2 (by rfl) ⟨442440, by rfl⟩ : syracuseStep 1179841 = 884881) (by norm_num)
theorem B1048801 : Blo 928581 1048801 := bbase (se 2 (by rfl) ⟨393300, by rfl⟩ : syracuseStep 1048801 = 786601) (by norm_num)
theorem B3539173 : Blo 928581 3539173 := bbase (se 4 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 3539173 = 663595) (by norm_num)
theorem B1769701 : Blo 928581 1769701 := bbase (se 4 (by rfl) ⟨165909, by rfl⟩ : syracuseStep 1769701 = 331819) (by norm_num)
theorem B2097413 : Blo 928581 2097413 := bbase (se 4 (by rfl) ⟨196632, by rfl⟩ : syracuseStep 2097413 = 393265) (by norm_num)
theorem B1048837 : Blo 928581 1048837 := bbase (se 4 (by rfl) ⟨98328, by rfl⟩ : syracuseStep 1048837 = 196657) (by norm_num)
theorem B1573141 : Blo 928581 1573141 := bbase (se 6 (by rfl) ⟨36870, by rfl⟩ : syracuseStep 1573141 = 73741) (by norm_num)
theorem B1179937 : Blo 928581 1179937 := bbase (se 2 (by rfl) ⟨442476, by rfl⟩ : syracuseStep 1179937 = 884953) (by norm_num)
theorem B1048873 : Blo 928581 1048873 := bbase (se 2 (by rfl) ⟨393327, by rfl⟩ : syracuseStep 1048873 = 786655) (by norm_num)
theorem B2097485 : Blo 928581 2097485 := bbase (se 3 (by rfl) ⟨393278, by rfl⟩ : syracuseStep 2097485 = 786557) (by norm_num)
theorem B1048909 : Blo 928581 1048909 := bbase (se 3 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 1048909 = 393341) (by norm_num)
theorem B1573229 : Blo 928581 1573229 := bbase (se 3 (by rfl) ⟨294980, by rfl⟩ : syracuseStep 1573229 = 589961) (by norm_num)
theorem B1048945 : Blo 928581 1048945 := bbase (se 2 (by rfl) ⟨393354, by rfl⟩ : syracuseStep 1048945 = 786709) (by norm_num)
theorem B1769845 : Blo 928581 1769845 := bbase (se 5 (by rfl) ⟨82961, by rfl⟩ : syracuseStep 1769845 = 165923) (by norm_num)
theorem B2097557 : Blo 928581 2097557 := bbase (se 6 (by rfl) ⟨49161, by rfl⟩ : syracuseStep 2097557 = 98323) (by norm_num)
theorem B1048981 : Blo 928581 1048981 := bbase (se 6 (by rfl) ⟨24585, by rfl⟩ : syracuseStep 1048981 = 49171) (by norm_num)
theorem B1049017 : Blo 928581 1049017 := bbase (se 2 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 1049017 = 786763) (by norm_num)
theorem B1180109 : Blo 928581 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B2097629 : Blo 928581 2097629 := bbase (se 3 (by rfl) ⟨393305, by rfl⟩ : syracuseStep 2097629 = 786611) (by norm_num)
theorem B1049053 : Blo 928581 1049053 := bbase (se 3 (by rfl) ⟨196697, by rfl⟩ : syracuseStep 1049053 = 393395) (by norm_num)
theorem B1573357 : Blo 928581 1573357 := bbase (se 3 (by rfl) ⟨295004, by rfl⟩ : syracuseStep 1573357 = 590009) (by norm_num)
theorem B8487413 : Blo 928581 8487413 := bbase (se 5 (by rfl) ⟨397847, by rfl⟩ : syracuseStep 8487413 = 795695) (by norm_num)
theorem B1049089 : Blo 928581 1049089 := bbase (se 2 (by rfl) ⟨393408, by rfl⟩ : syracuseStep 1049089 = 786817) (by norm_num)
theorem B2359813 : Blo 928581 2359813 := bbase (se 4 (by rfl) ⟨221232, by rfl⟩ : syracuseStep 2359813 = 442465) (by norm_num)
theorem B1180165 : Blo 928581 1180165 := bbase (se 4 (by rfl) ⟨110640, by rfl⟩ : syracuseStep 1180165 = 221281) (by norm_num)
theorem B8946197 : Blo 928581 8946197 := bbase (se 6 (by rfl) ⟨209676, by rfl⟩ : syracuseStep 8946197 = 419353) (by norm_num)
theorem B3539477 : Blo 928581 3539477 := bbase (se 6 (by rfl) ⟨82956, by rfl⟩ : syracuseStep 3539477 = 165913) (by norm_num)
theorem B1770005 : Blo 928581 1770005 := bbase (se 6 (by rfl) ⟨41484, by rfl⟩ : syracuseStep 1770005 = 82969) (by norm_num)
theorem B2097701 : Blo 928581 2097701 := bbase (se 4 (by rfl) ⟨196659, by rfl⟩ : syracuseStep 2097701 = 393319) (by norm_num)
theorem B1049125 : Blo 928581 1049125 := bbase (se 4 (by rfl) ⟨98355, by rfl⟩ : syracuseStep 1049125 = 196711) (by norm_num)
theorem B3146309 : Blo 928581 3146309 := bbase (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) (by norm_num)
theorem B1573445 : Blo 928581 1573445 := bbase (se 4 (by rfl) ⟨147510, by rfl⟩ : syracuseStep 1573445 = 295021) (by norm_num)
theorem B1180261 : Blo 928581 1180261 := bbase (se 4 (by rfl) ⟨110649, by rfl⟩ : syracuseStep 1180261 = 221299) (by norm_num)
theorem B2097773 : Blo 928581 2097773 := bbase (se 3 (by rfl) ⟨393332, by rfl⟩ : syracuseStep 2097773 = 786665) (by norm_num)
theorem B4719221 : Blo 928581 4719221 := bbase (se 5 (by rfl) ⟨221213, by rfl⟩ : syracuseStep 4719221 = 442427) (by norm_num)
theorem B2359925 : Blo 928581 2359925 := bbase (se 5 (by rfl) ⟨110621, by rfl⟩ : syracuseStep 2359925 = 221243) (by norm_num)
theorem B1770149 : Blo 928581 1770149 := bbase (se 4 (by rfl) ⟨165951, by rfl⟩ : syracuseStep 1770149 = 331903) (by norm_num)
theorem B2097845 : Blo 928581 2097845 := bbase (se 5 (by rfl) ⟨98336, by rfl⟩ : syracuseStep 2097845 = 196673) (by norm_num)
theorem B1573573 : Blo 928581 1573573 := bbase (se 4 (by rfl) ⟨147522, by rfl⟩ : syracuseStep 1573573 = 295045) (by norm_num)
theorem B1508053 : Blo 928581 1508053 := bbase (se 7 (by rfl) ⟨17672, by rfl⟩ : syracuseStep 1508053 = 35345) (by norm_num)
theorem B2097917 : Blo 928581 2097917 := bbase (se 3 (by rfl) ⟨393359, by rfl⟩ : syracuseStep 2097917 = 786719) (by norm_num)
theorem B1573661 : Blo 928581 1573661 := bbase (se 3 (by rfl) ⟨295061, by rfl⟩ : syracuseStep 1573661 = 590123) (by norm_num)
theorem B2360117 : Blo 928581 2360117 := bbase (se 5 (by rfl) ⟨110630, by rfl⟩ : syracuseStep 2360117 = 221261) (by norm_num)
theorem B2097989 : Blo 928581 2097989 := bbase (se 4 (by rfl) ⟨196686, by rfl⟩ : syracuseStep 2097989 = 393373) (by norm_num)
theorem B2655109 : Blo 928581 2655109 := bbase (se 4 (by rfl) ⟨248916, by rfl⟩ : syracuseStep 2655109 = 497833) (by norm_num)
theorem B2098061 : Blo 928581 2098061 := bbase (se 3 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 2098061 = 786773) (by norm_num)
theorem B1770437 : Blo 928581 1770437 := bbase (se 4 (by rfl) ⟨165978, by rfl⟩ : syracuseStep 1770437 = 331957) (by norm_num)
theorem B2098133 : Blo 928581 2098133 := bbase (se 7 (by rfl) ⟨24587, by rfl⟩ : syracuseStep 2098133 = 49175) (by norm_num)
theorem B3146741 : Blo 928581 3146741 := bbase (se 5 (by rfl) ⟨147503, by rfl⟩ : syracuseStep 3146741 = 295007) (by norm_num)
theorem B2098205 : Blo 928581 2098205 := bbase (se 3 (by rfl) ⟨393413, by rfl⟩ : syracuseStep 2098205 = 786827) (by norm_num)
theorem B2098277 : Blo 928581 2098277 := bbase (se 4 (by rfl) ⟨196713, by rfl⟩ : syracuseStep 2098277 = 393427) (by norm_num)
theorem B2360461 : Blo 928581 2360461 := bbase (se 3 (by rfl) ⟨442586, by rfl⟩ : syracuseStep 2360461 = 885173) (by norm_num)
theorem B2360573 : Blo 928581 2360573 := bbase (se 3 (by rfl) ⟨442607, by rfl⟩ : syracuseStep 2360573 = 885215) (by norm_num)
theorem B2983205 : Blo 928581 2983205 := bbase (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) (by norm_num)
theorem B1148213 : Blo 928581 1148213 := bbase (se 5 (by rfl) ⟨53822, by rfl⟩ : syracuseStep 1148213 = 107645) (by norm_num)
theorem B3147173 : Blo 928581 3147173 := bbase (se 4 (by rfl) ⟨295047, by rfl⟩ : syracuseStep 3147173 = 590095) (by norm_num)
theorem B8619605 : Blo 928581 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B9537173 : Blo 928581 9537173 := bbase (se 6 (by rfl) ⟨223527, by rfl⟩ : syracuseStep 9537173 = 447055) (by norm_num)
theorem B5310197 : Blo 928581 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B2066197 : Blo 928581 2066197 := bbase (se 6 (by rfl) ⟨48426, by rfl⟩ : syracuseStep 2066197 = 96853) (by norm_num)
theorem B5965589 : Blo 928581 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B4720517 : Blo 928581 4720517 := bbase (se 4 (by rfl) ⟨442548, by rfl⟩ : syracuseStep 4720517 = 885097) (by norm_num)
theorem B2066485 : Blo 928581 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1345621 : Blo 928581 1345621 := bbase (se 8 (by rfl) ⟨7884, by rfl⟩ : syracuseStep 1345621 = 15769) (by norm_num)
theorem B2721925 : Blo 928581 2721925 := bbase (se 4 (by rfl) ⟨255180, by rfl⟩ : syracuseStep 2721925 = 510361) (by norm_num)
theorem B7637237 : Blo 928581 7637237 := bbase (se 5 (by rfl) ⟨357995, by rfl⟩ : syracuseStep 7637237 = 715991) (by norm_num)
theorem B7080533 : Blo 928581 7080533 := bbase (se 8 (by rfl) ⟨41487, by rfl⟩ : syracuseStep 7080533 = 82975) (by norm_num)
theorem B1117049 : Blo 928581 1117049 := bbase (se 2 (by rfl) ⟨418893, by rfl⟩ : syracuseStep 1117049 = 837787) (by norm_num)
theorem B1117261 : Blo 928581 1117261 := bbase (se 3 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 1117261 = 418973) (by norm_num)
theorem B1117405 : Blo 928581 1117405 := bbase (se 3 (by rfl) ⟨209513, by rfl⟩ : syracuseStep 1117405 = 419027) (by norm_num)
theorem B1412453 : Blo 928581 1412453 := bbase (se 4 (by rfl) ⟨132417, by rfl⟩ : syracuseStep 1412453 = 264835) (by norm_num)
theorem B2985461 : Blo 928581 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B2264573 : Blo 928581 2264573 := bbase (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) (by norm_num)
theorem B2985589 : Blo 928581 2985589 := bbase (se 5 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 2985589 = 279899) (by norm_num)
theorem B2231965 : Blo 928581 2231965 := bbase (se 3 (by rfl) ⟨418493, by rfl⟩ : syracuseStep 2231965 = 836987) (by norm_num)
theorem B7966421 : Blo 928581 7966421 := bbase (se 7 (by rfl) ⟨93356, by rfl⟩ : syracuseStep 7966421 = 186713) (by norm_num)
theorem B9539797 : Blo 928581 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B3969269 : Blo 928581 3969269 := bbase (se 5 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 3969269 = 372119) (by norm_num)
theorem B2232677 : Blo 928581 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B5968565 : Blo 928581 5968565 := bbase (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) (by norm_num)
theorem B3773141 : Blo 928581 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B2233061 : Blo 928581 2233061 := bbase (se 4 (by rfl) ⟨209349, by rfl⟩ : syracuseStep 2233061 = 418699) (by norm_num)
theorem B1118981 : Blo 928581 1118981 := bbase (se 4 (by rfl) ⟨104904, by rfl⟩ : syracuseStep 1118981 = 209809) (by norm_num)
theorem B1413973 : Blo 928581 1413973 := bbase (se 9 (by rfl) ⟨4142, by rfl⟩ : syracuseStep 1413973 = 8285) (by norm_num)
theorem B2233349 : Blo 928581 2233349 := bbase (se 4 (by rfl) ⟨209376, by rfl⟩ : syracuseStep 2233349 = 418753) (by norm_num)
theorem B1414181 : Blo 928581 1414181 := bbase (se 4 (by rfl) ⟨132579, by rfl⟩ : syracuseStep 1414181 = 265159) (by norm_num)
theorem B1119317 : Blo 928581 1119317 := bbase (se 8 (by rfl) ⟨6558, by rfl⟩ : syracuseStep 1119317 = 13117) (by norm_num)
theorem B1676381 : Blo 928581 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B1119433 : Blo 928581 1119433 := bbase (se 2 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 1119433 = 839575) (by norm_num)
theorem B1119505 : Blo 928581 1119505 := bbase (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) (by norm_num)
theorem B1119529 : Blo 928581 1119529 := bbase (se 2 (by rfl) ⟨419823, by rfl⟩ : syracuseStep 1119529 = 839647) (by norm_num)
theorem B1119673 : Blo 928581 1119673 := bbase (se 2 (by rfl) ⟨419877, by rfl⟩ : syracuseStep 1119673 = 839755) (by norm_num)
theorem B956257 : Blo 928581 956257 := bbase (se 2 (by rfl) ⟨358596, by rfl⟩ : syracuseStep 956257 = 717193) (by norm_num)
theorem B9050069 : Blo 928581 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B3971045 : Blo 928581 3971045 := bbase (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) (by norm_num)
theorem B3774485 : Blo 928581 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B5380181 : Blo 928581 5380181 := bbase (se 8 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 5380181 = 63049) (by norm_num)
theorem B4528261 : Blo 928581 4528261 := bbase (se 4 (by rfl) ⟨424524, by rfl⟩ : syracuseStep 4528261 = 849049) (by norm_num)
theorem B4463045 : Blo 928581 4463045 := bbase (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) (by norm_num)
theorem B1088257 : Blo 928581 1088257 := bbase (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) (by norm_num)
theorem B3972037 : Blo 928581 3972037 := bbase (se 4 (by rfl) ⟨372378, by rfl⟩ : syracuseStep 3972037 = 744757) (by norm_num)
theorem B2236405 : Blo 928581 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B1679437 : Blo 928581 1679437 := bbase (se 3 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 1679437 = 629789) (by norm_num)
theorem B991801 : Blo 928581 991801 := bbase (se 2 (by rfl) ⟨371925, by rfl⟩ : syracuseStep 991801 = 743851) (by norm_num)
theorem B2237021 : Blo 928581 2237021 := bbase (se 3 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 2237021 = 838883) (by norm_num)
theorem B991873 : Blo 928581 991873 := bbase (se 2 (by rfl) ⟨371952, by rfl⟩ : syracuseStep 991873 = 743905) (by norm_num)
theorem B2237213 : Blo 928581 2237213 := bbase (se 3 (by rfl) ⟨419477, by rfl⟩ : syracuseStep 2237213 = 838955) (by norm_num)
theorem B3351365 : Blo 928581 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B992245 : Blo 928581 992245 := bbase (se 5 (by rfl) ⟨46511, by rfl⟩ : syracuseStep 992245 = 93023) (by norm_num)
theorem B16950293 : Blo 928581 16950293 := bbase (se 6 (by rfl) ⟨397272, by rfl⟩ : syracuseStep 16950293 = 794545) (by norm_num)
theorem B4465813 : Blo 928581 4465813 := bbase (se 6 (by rfl) ⟨104667, by rfl⟩ : syracuseStep 4465813 = 209335) (by norm_num)
theorem B3679445 : Blo 928581 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2237789 : Blo 928581 2237789 := bbase (se 3 (by rfl) ⟨419585, by rfl⟩ : syracuseStep 2237789 = 839171) (by norm_num)
theorem B992621 : Blo 928581 992621 := bbase (se 3 (by rfl) ⟨186116, by rfl⟩ : syracuseStep 992621 = 372233) (by norm_num)
theorem B992693 : Blo 928581 992693 := bbase (se 5 (by rfl) ⟨46532, by rfl⟩ : syracuseStep 992693 = 93065) (by norm_num)
theorem B992881 : Blo 928581 992881 := bbase (se 2 (by rfl) ⟨372330, by rfl⟩ : syracuseStep 992881 = 744661) (by norm_num)
theorem B2238173 : Blo 928581 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B993065 : Blo 928581 993065 := bbase (se 2 (by rfl) ⟨372399, by rfl⟩ : syracuseStep 993065 = 744799) (by norm_num)
theorem B2271149 : Blo 928581 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B1255405 : Blo 928581 1255405 := bbase (se 3 (by rfl) ⟨235388, by rfl⟩ : syracuseStep 1255405 = 470777) (by norm_num)
theorem B1255469 : Blo 928581 1255469 := bbase (se 3 (by rfl) ⟨235400, by rfl⟩ : syracuseStep 1255469 = 470801) (by norm_num)
theorem B4237541 : Blo 928581 4237541 := bbase (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) (by norm_num)
theorem B3188965 : Blo 928581 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B1550765 : Blo 928581 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B993817 : Blo 928581 993817 := bbase (se 2 (by rfl) ⟨372681, by rfl⟩ : syracuseStep 993817 = 745363) (by norm_num)
theorem B3025493 : Blo 928581 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B993889 : Blo 928581 993889 := bbase (se 2 (by rfl) ⟨372708, by rfl⟩ : syracuseStep 993889 = 745417) (by norm_num)
theorem B1059485 : Blo 928581 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B994069 : Blo 928581 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B10595285 : Blo 928581 10595285 := bbase (se 7 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 10595285 = 248327) (by norm_num)
theorem B1322173 : Blo 928581 1322173 := bbase (se 3 (by rfl) ⟨247907, by rfl⟩ : syracuseStep 1322173 = 495815) (by norm_num)
theorem B994513 : Blo 928581 994513 := bbase (se 2 (by rfl) ⟨372942, by rfl⟩ : syracuseStep 994513 = 745885) (by norm_num)
theorem B994637 : Blo 928581 994637 := bbase (se 3 (by rfl) ⟨186494, by rfl⟩ : syracuseStep 994637 = 372989) (by norm_num)
theorem B2239933 : Blo 928581 2239933 := bbase (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) (by norm_num)
theorem B4304341 : Blo 928581 4304341 := bbase (se 7 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 4304341 = 100883) (by norm_num)
theorem B1322509 : Blo 928581 1322509 := bbase (se 3 (by rfl) ⟨247970, by rfl⟩ : syracuseStep 1322509 = 495941) (by norm_num)
theorem B2862661 : Blo 928581 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B994889 : Blo 928581 994889 := bbase (se 2 (by rfl) ⟨373083, by rfl⟩ : syracuseStep 994889 = 746167) (by norm_num)
theorem B1191629 : Blo 928581 1191629 := bbase (se 3 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 1191629 = 446861) (by norm_num)
theorem B1322725 : Blo 928581 1322725 := bbase (se 4 (by rfl) ⟨124005, by rfl⟩ : syracuseStep 1322725 = 248011) (by norm_num)
theorem B7057205 : Blo 928581 7057205 := bbase (se 5 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 7057205 = 661613) (by norm_num)
theorem B3977045 : Blo 928581 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B1257373 : Blo 928581 1257373 := bbase (se 3 (by rfl) ⟨235757, by rfl⟩ : syracuseStep 1257373 = 471515) (by norm_num)
theorem B995333 : Blo 928581 995333 := bbase (se 4 (by rfl) ⟨93312, by rfl⟩ : syracuseStep 995333 = 186625) (by norm_num)
theorem B4239397 : Blo 928581 4239397 := bbase (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) (by norm_num)
theorem B1323101 : Blo 928581 1323101 := bbase (se 3 (by rfl) ⟨248081, by rfl⟩ : syracuseStep 1323101 = 496163) (by norm_num)
theorem B3977333 : Blo 928581 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B995581 : Blo 928581 995581 := bbase (se 3 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 995581 = 373343) (by norm_num)
theorem B1061137 : Blo 928581 1061137 := bbase (se 2 (by rfl) ⟨397926, by rfl⟩ : syracuseStep 1061137 = 795853) (by norm_num)
theorem B1257773 : Blo 928581 1257773 := bbase (se 3 (by rfl) ⟨235832, by rfl⟩ : syracuseStep 1257773 = 471665) (by norm_num)
theorem B17904149 : Blo 928581 17904149 := bbase (se 6 (by rfl) ⟨419628, by rfl⟩ : syracuseStep 17904149 = 839257) (by norm_num)
theorem B1487413 : Blo 928581 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B1487477 : Blo 928581 1487477 := bbase (se 5 (by rfl) ⟨69725, by rfl⟩ : syracuseStep 1487477 = 139451) (by norm_num)
theorem B7549685 : Blo 928581 7549685 := bbase (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) (by norm_num)
theorem B1258237 : Blo 928581 1258237 := bbase (se 3 (by rfl) ⟨235919, by rfl⟩ : syracuseStep 1258237 = 471839) (by norm_num)
theorem B3978085 : Blo 928581 3978085 := bbase (se 4 (by rfl) ⟨372945, by rfl⟩ : syracuseStep 3978085 = 745891) (by norm_num)
theorem B1258405 : Blo 928581 1258405 := bbase (se 4 (by rfl) ⟨117975, by rfl⟩ : syracuseStep 1258405 = 235951) (by norm_num)
theorem B3027989 : Blo 928581 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B5289077 : Blo 928581 5289077 := bbase (se 5 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 5289077 = 495851) (by norm_num)
theorem B2831813 : Blo 928581 2831813 := bbase (se 4 (by rfl) ⟨265482, by rfl⟩ : syracuseStep 2831813 = 530965) (by norm_num)
theorem B1324525 : Blo 928581 1324525 := bbase (se 3 (by rfl) ⟨248348, by rfl⟩ : syracuseStep 1324525 = 496697) (by norm_num)
theorem B3978821 : Blo 928581 3978821 := bbase (se 4 (by rfl) ⟨373014, by rfl⟩ : syracuseStep 3978821 = 746029) (by norm_num)
theorem B4470389 : Blo 928581 4470389 := bbase (se 5 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 4470389 = 419099) (by norm_num)
theorem B1193681 : Blo 928581 1193681 := bbase (se 2 (by rfl) ⟨447630, by rfl⟩ : syracuseStep 1193681 = 895261) (by norm_num)
theorem B3356453 : Blo 928581 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B1488797 : Blo 928581 1488797 := bbase (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) (by norm_num)
theorem B1325117 : Blo 928581 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B3356741 : Blo 928581 3356741 := bbase (se 4 (by rfl) ⟨314694, by rfl⟩ : syracuseStep 3356741 = 629389) (by norm_num)
theorem B7944277 : Blo 928581 7944277 := bbase (se 8 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 7944277 = 93097) (by norm_num)
theorem B1488989 : Blo 928581 1488989 := bbase (se 3 (by rfl) ⟨279185, by rfl⟩ : syracuseStep 1488989 = 558371) (by norm_num)
theorem B1325197 : Blo 928581 1325197 := bbase (se 3 (by rfl) ⟨248474, by rfl⟩ : syracuseStep 1325197 = 496949) (by norm_num)
theorem B1489117 : Blo 928581 1489117 := bbase (se 3 (by rfl) ⟨279209, by rfl⟩ : syracuseStep 1489117 = 558419) (by norm_num)
theorem B1325317 : Blo 928581 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B1063189 : Blo 928581 1063189 := bbase (se 6 (by rfl) ⟨24918, by rfl⟩ : syracuseStep 1063189 = 49837) (by norm_num)
theorem B1325413 : Blo 928581 1325413 := bbase (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) (by norm_num)
theorem B1194445 : Blo 928581 1194445 := bbase (se 3 (by rfl) ⟨223958, by rfl⟩ : syracuseStep 1194445 = 447917) (by norm_num)
theorem B1325909 : Blo 928581 1325909 := bbase (se 9 (by rfl) ⟨3884, by rfl⟩ : syracuseStep 1325909 = 7769) (by norm_num)
theorem B1489757 : Blo 928581 1489757 := bbase (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) (by norm_num)
theorem B4701077 : Blo 928581 4701077 := bbase (se 6 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 4701077 = 220363) (by norm_num)
theorem B7551893 : Blo 928581 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B1883197 : Blo 928581 1883197 := bbase (se 3 (by rfl) ⟨353099, by rfl⟩ : syracuseStep 1883197 = 706199) (by norm_num)
theorem B7552277 : Blo 928581 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B1490213 : Blo 928581 1490213 := bbase (se 4 (by rfl) ⟨139707, by rfl⟩ : syracuseStep 1490213 = 279415) (by norm_num)
theorem B1326461 : Blo 928581 1326461 := bbase (se 3 (by rfl) ⟨248711, by rfl⟩ : syracuseStep 1326461 = 497423) (by norm_num)
theorem B1490437 : Blo 928581 1490437 := bbase (se 4 (by rfl) ⟨139728, by rfl⟩ : syracuseStep 1490437 = 279457) (by norm_num)
theorem B1490501 : Blo 928581 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B1490629 : Blo 928581 1490629 := bbase (se 4 (by rfl) ⟨139746, by rfl⟩ : syracuseStep 1490629 = 279493) (by norm_num)
theorem B1883917 : Blo 928581 1883917 := bbase (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) (by norm_num)
theorem B7946261 : Blo 928581 7946261 := bbase (se 6 (by rfl) ⟨186240, by rfl⟩ : syracuseStep 7946261 = 372481) (by norm_num)
theorem B1327213 : Blo 928581 1327213 := bbase (se 3 (by rfl) ⟨248852, by rfl⟩ : syracuseStep 1327213 = 497705) (by norm_num)
theorem B4702373 : Blo 928581 4702373 := bbase (se 4 (by rfl) ⟨440847, by rfl⟩ : syracuseStep 4702373 = 881695) (by norm_num)
theorem B1392893 : Blo 928581 1392893 := bbase (se 3 (by rfl) ⟨261167, by rfl⟩ : syracuseStep 1392893 = 522335) (by norm_num)
theorem B1392917 : Blo 928581 1392917 := bbase (se 6 (by rfl) ⟨32646, by rfl⟩ : syracuseStep 1392917 = 65293) (by norm_num)
theorem B1392941 : Blo 928581 1392941 := bbase (se 3 (by rfl) ⟨261176, by rfl⟩ : syracuseStep 1392941 = 522353) (by norm_num)
theorem B1392965 : Blo 928581 1392965 := bbase (se 4 (by rfl) ⟨130590, by rfl⟩ : syracuseStep 1392965 = 261181) (by norm_num)
theorem B1818949 : Blo 928581 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B1392989 : Blo 928581 1392989 := bbase (se 3 (by rfl) ⟨261185, by rfl⟩ : syracuseStep 1392989 = 522371) (by norm_num)
theorem B1393013 : Blo 928581 1393013 := bbase (se 5 (by rfl) ⟨65297, by rfl⟩ : syracuseStep 1393013 = 130595) (by norm_num)
theorem B1393037 : Blo 928581 1393037 := bbase (se 3 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 1393037 = 522389) (by norm_num)
theorem B1393061 : Blo 928581 1393061 := bbase (se 4 (by rfl) ⟨130599, by rfl⟩ : syracuseStep 1393061 = 261199) (by norm_num)
theorem B1393085 : Blo 928581 1393085 := bbase (se 3 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 1393085 = 522407) (by norm_num)
theorem B1393109 : Blo 928581 1393109 := bbase (se 7 (by rfl) ⟨16325, by rfl⟩ : syracuseStep 1393109 = 32651) (by norm_num)
theorem B1393133 : Blo 928581 1393133 := bbase (se 3 (by rfl) ⟨261212, by rfl⟩ : syracuseStep 1393133 = 522425) (by norm_num)
theorem B1393157 : Blo 928581 1393157 := bbase (se 4 (by rfl) ⟨130608, by rfl⟩ : syracuseStep 1393157 = 261217) (by norm_num)
theorem B1393181 : Blo 928581 1393181 := bbase (se 3 (by rfl) ⟨261221, by rfl⟩ : syracuseStep 1393181 = 522443) (by norm_num)
theorem B1393205 : Blo 928581 1393205 := bbase (se 5 (by rfl) ⟨65306, by rfl⟩ : syracuseStep 1393205 = 130613) (by norm_num)
theorem B1393229 : Blo 928581 1393229 := bbase (se 3 (by rfl) ⟨261230, by rfl⟩ : syracuseStep 1393229 = 522461) (by norm_num)
theorem B1360469 : Blo 928581 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B1393253 : Blo 928581 1393253 := bbase (se 4 (by rfl) ⟨130617, by rfl⟩ : syracuseStep 1393253 = 261235) (by norm_num)
theorem B4244069 : Blo 928581 4244069 := bbase (se 4 (by rfl) ⟨397881, by rfl⟩ : syracuseStep 4244069 = 795763) (by norm_num)
theorem B1393277 : Blo 928581 1393277 := bbase (se 3 (by rfl) ⟨261239, by rfl⟩ : syracuseStep 1393277 = 522479) (by norm_num)
theorem B1393301 : Blo 928581 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B1393325 : Blo 928581 1393325 := bbase (se 3 (by rfl) ⟨261248, by rfl⟩ : syracuseStep 1393325 = 522497) (by norm_num)
theorem B1393349 : Blo 928581 1393349 := bbase (se 4 (by rfl) ⟨130626, by rfl⟩ : syracuseStep 1393349 = 261253) (by norm_num)
theorem B1393373 : Blo 928581 1393373 := bbase (se 3 (by rfl) ⟨261257, by rfl⟩ : syracuseStep 1393373 = 522515) (by norm_num)
theorem B1393397 : Blo 928581 1393397 := bbase (se 5 (by rfl) ⟨65315, by rfl⟩ : syracuseStep 1393397 = 130631) (by norm_num)
theorem B1393421 : Blo 928581 1393421 := bbase (se 3 (by rfl) ⟨261266, by rfl⟩ : syracuseStep 1393421 = 522533) (by norm_num)
theorem B1393445 : Blo 928581 1393445 := bbase (se 4 (by rfl) ⟨130635, by rfl⟩ : syracuseStep 1393445 = 261271) (by norm_num)
theorem B3982117 : Blo 928581 3982117 := bbase (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) (by norm_num)
theorem B1393469 : Blo 928581 1393469 := bbase (se 3 (by rfl) ⟨261275, by rfl⟩ : syracuseStep 1393469 = 522551) (by norm_num)
theorem B2147141 : Blo 928581 2147141 := bbase (se 4 (by rfl) ⟨201294, by rfl⟩ : syracuseStep 2147141 = 402589) (by norm_num)
theorem B1393493 : Blo 928581 1393493 := bbase (se 9 (by rfl) ⟨4082, by rfl⟩ : syracuseStep 1393493 = 8165) (by norm_num)
theorem B1393517 : Blo 928581 1393517 := bbase (se 3 (by rfl) ⟨261284, by rfl⟩ : syracuseStep 1393517 = 522569) (by norm_num)
theorem B1393541 : Blo 928581 1393541 := bbase (se 4 (by rfl) ⟨130644, by rfl⟩ : syracuseStep 1393541 = 261289) (by norm_num)
theorem B1491853 : Blo 928581 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B1393565 : Blo 928581 1393565 := bbase (se 3 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 1393565 = 522587) (by norm_num)
theorem B1393589 : Blo 928581 1393589 := bbase (se 5 (by rfl) ⟨65324, by rfl⟩ : syracuseStep 1393589 = 130649) (by norm_num)
theorem B1393613 : Blo 928581 1393613 := bbase (se 3 (by rfl) ⟨261302, by rfl⟩ : syracuseStep 1393613 = 522605) (by norm_num)
theorem B1393637 : Blo 928581 1393637 := bbase (se 4 (by rfl) ⟨130653, by rfl⟩ : syracuseStep 1393637 = 261307) (by norm_num)
theorem B1393661 : Blo 928581 1393661 := bbase (se 3 (by rfl) ⟨261311, by rfl⟩ : syracuseStep 1393661 = 522623) (by norm_num)
theorem B8471573 : Blo 928581 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B1393685 : Blo 928581 1393685 := bbase (se 6 (by rfl) ⟨32664, by rfl⟩ : syracuseStep 1393685 = 65329) (by norm_num)
theorem B1393709 : Blo 928581 1393709 := bbase (se 3 (by rfl) ⟨261320, by rfl⟩ : syracuseStep 1393709 = 522641) (by norm_num)
theorem B1983541 : Blo 928581 1983541 := bbase (se 5 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 1983541 = 185957) (by norm_num)
theorem B1393733 : Blo 928581 1393733 := bbase (se 4 (by rfl) ⟨130662, by rfl⟩ : syracuseStep 1393733 = 261325) (by norm_num)
theorem B1393757 : Blo 928581 1393757 := bbase (se 3 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 1393757 = 522659) (by norm_num)
theorem B1393781 : Blo 928581 1393781 := bbase (se 5 (by rfl) ⟨65333, by rfl⟩ : syracuseStep 1393781 = 130667) (by norm_num)
theorem B1393805 : Blo 928581 1393805 := bbase (se 3 (by rfl) ⟨261338, by rfl⟩ : syracuseStep 1393805 = 522677) (by norm_num)
theorem B1393829 : Blo 928581 1393829 := bbase (se 4 (by rfl) ⟨130671, by rfl⟩ : syracuseStep 1393829 = 261343) (by norm_num)
theorem B1393853 : Blo 928581 1393853 := bbase (se 3 (by rfl) ⟨261347, by rfl⟩ : syracuseStep 1393853 = 522695) (by norm_num)
theorem B1393877 : Blo 928581 1393877 := bbase (se 7 (by rfl) ⟨16334, by rfl⟩ : syracuseStep 1393877 = 32669) (by norm_num)
theorem B1393901 : Blo 928581 1393901 := bbase (se 3 (by rfl) ⟨261356, by rfl⟩ : syracuseStep 1393901 = 522713) (by norm_num)
theorem B1393925 : Blo 928581 1393925 := bbase (se 4 (by rfl) ⟨130680, by rfl⟩ : syracuseStep 1393925 = 261361) (by norm_num)
theorem B1393949 : Blo 928581 1393949 := bbase (se 3 (by rfl) ⟨261365, by rfl⟩ : syracuseStep 1393949 = 522731) (by norm_num)
theorem B1393973 : Blo 928581 1393973 := bbase (se 5 (by rfl) ⟨65342, by rfl⟩ : syracuseStep 1393973 = 130685) (by norm_num)
theorem B1393997 : Blo 928581 1393997 := bbase (se 3 (by rfl) ⟨261374, by rfl⟩ : syracuseStep 1393997 = 522749) (by norm_num)
theorem B1394021 : Blo 928581 1394021 := bbase (se 4 (by rfl) ⟨130689, by rfl⟩ : syracuseStep 1394021 = 261379) (by norm_num)
theorem B1394045 : Blo 928581 1394045 := bbase (se 3 (by rfl) ⟨261383, by rfl⟩ : syracuseStep 1394045 = 522767) (by norm_num)
theorem B1394069 : Blo 928581 1394069 := bbase (se 6 (by rfl) ⟨32673, by rfl⟩ : syracuseStep 1394069 = 65347) (by norm_num)
theorem B1394093 : Blo 928581 1394093 := bbase (se 3 (by rfl) ⟨261392, by rfl⟩ : syracuseStep 1394093 = 522785) (by norm_num)
theorem B4703669 : Blo 928581 4703669 := bbase (se 5 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 4703669 = 440969) (by norm_num)
theorem B1394117 : Blo 928581 1394117 := bbase (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) (by norm_num)
theorem B1394141 : Blo 928581 1394141 := bbase (se 3 (by rfl) ⟨261401, by rfl⟩ : syracuseStep 1394141 = 522803) (by norm_num)
theorem B1394165 : Blo 928581 1394165 := bbase (se 5 (by rfl) ⟨65351, by rfl⟩ : syracuseStep 1394165 = 130703) (by norm_num)
theorem B1394189 : Blo 928581 1394189 := bbase (se 3 (by rfl) ⟨261410, by rfl⟩ : syracuseStep 1394189 = 522821) (by norm_num)
theorem B1394213 : Blo 928581 1394213 := bbase (se 4 (by rfl) ⟨130707, by rfl⟩ : syracuseStep 1394213 = 261415) (by norm_num)
theorem B1492525 : Blo 928581 1492525 := bbase (se 3 (by rfl) ⟨279848, by rfl⟩ : syracuseStep 1492525 = 559697) (by norm_num)
theorem B1394237 : Blo 928581 1394237 := bbase (se 3 (by rfl) ⟨261419, by rfl⟩ : syracuseStep 1394237 = 522839) (by norm_num)
theorem B1394261 : Blo 928581 1394261 := bbase (se 8 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 1394261 = 16339) (by norm_num)
theorem B1394285 : Blo 928581 1394285 := bbase (se 3 (by rfl) ⟨261428, by rfl⟩ : syracuseStep 1394285 = 522857) (by norm_num)
theorem B1394309 : Blo 928581 1394309 := bbase (se 4 (by rfl) ⟨130716, by rfl⟩ : syracuseStep 1394309 = 261433) (by norm_num)
theorem B1394333 : Blo 928581 1394333 := bbase (se 3 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 1394333 = 522875) (by norm_num)
theorem B1394357 : Blo 928581 1394357 := bbase (se 5 (by rfl) ⟨65360, by rfl⟩ : syracuseStep 1394357 = 130721) (by norm_num)
theorem B1394381 : Blo 928581 1394381 := bbase (se 3 (by rfl) ⟨261446, by rfl⟩ : syracuseStep 1394381 = 522893) (by norm_num)
theorem B1394405 : Blo 928581 1394405 := bbase (se 4 (by rfl) ⟨130725, by rfl⟩ : syracuseStep 1394405 = 261451) (by norm_num)
theorem B1394429 : Blo 928581 1394429 := bbase (se 3 (by rfl) ⟨261455, by rfl⟩ : syracuseStep 1394429 = 522911) (by norm_num)
theorem B1394453 : Blo 928581 1394453 := bbase (se 6 (by rfl) ⟨32682, by rfl⟩ : syracuseStep 1394453 = 65365) (by norm_num)
theorem B1394477 : Blo 928581 1394477 := bbase (se 3 (by rfl) ⟨261464, by rfl⟩ : syracuseStep 1394477 = 522929) (by norm_num)
theorem B1394501 : Blo 928581 1394501 := bbase (se 4 (by rfl) ⟨130734, by rfl⟩ : syracuseStep 1394501 = 261469) (by norm_num)
theorem B4474693 : Blo 928581 4474693 := bbase (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) (by norm_num)
theorem B1394525 : Blo 928581 1394525 := bbase (se 3 (by rfl) ⟨261473, by rfl⟩ : syracuseStep 1394525 = 522947) (by norm_num)
theorem B1394549 : Blo 928581 1394549 := bbase (se 5 (by rfl) ⟨65369, by rfl⟩ : syracuseStep 1394549 = 130739) (by norm_num)
theorem B1394573 : Blo 928581 1394573 := bbase (se 3 (by rfl) ⟨261482, by rfl⟩ : syracuseStep 1394573 = 522965) (by norm_num)
theorem B1394597 : Blo 928581 1394597 := bbase (se 4 (by rfl) ⟨130743, by rfl⟩ : syracuseStep 1394597 = 261487) (by norm_num)
theorem B1984429 : Blo 928581 1984429 := bbase (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) (by norm_num)
theorem B1394621 : Blo 928581 1394621 := bbase (se 3 (by rfl) ⟨261491, by rfl⟩ : syracuseStep 1394621 = 522983) (by norm_num)
theorem B1394645 : Blo 928581 1394645 := bbase (se 7 (by rfl) ⟨16343, by rfl⟩ : syracuseStep 1394645 = 32687) (by norm_num)
theorem B1394669 : Blo 928581 1394669 := bbase (se 3 (by rfl) ⟨261500, by rfl⟩ : syracuseStep 1394669 = 523001) (by norm_num)
theorem B1394693 : Blo 928581 1394693 := bbase (se 4 (by rfl) ⟨130752, by rfl⟩ : syracuseStep 1394693 = 261505) (by norm_num)
theorem B1394717 : Blo 928581 1394717 := bbase (se 3 (by rfl) ⟨261509, by rfl⟩ : syracuseStep 1394717 = 523019) (by norm_num)
theorem B1394741 : Blo 928581 1394741 := bbase (se 5 (by rfl) ⟨65378, by rfl⟩ : syracuseStep 1394741 = 130757) (by norm_num)
theorem B1394765 : Blo 928581 1394765 := bbase (se 3 (by rfl) ⟨261518, by rfl⟩ : syracuseStep 1394765 = 523037) (by norm_num)
theorem B1394789 : Blo 928581 1394789 := bbase (se 4 (by rfl) ⟨130761, by rfl⟩ : syracuseStep 1394789 = 261523) (by norm_num)
theorem B1394813 : Blo 928581 1394813 := bbase (se 3 (by rfl) ⟨261527, by rfl⟩ : syracuseStep 1394813 = 523055) (by norm_num)
theorem B1394837 : Blo 928581 1394837 := bbase (se 6 (by rfl) ⟨32691, by rfl⟩ : syracuseStep 1394837 = 65383) (by norm_num)
theorem B1394861 : Blo 928581 1394861 := bbase (se 3 (by rfl) ⟨261536, by rfl⟩ : syracuseStep 1394861 = 523073) (by norm_num)
theorem B1394885 : Blo 928581 1394885 := bbase (se 4 (by rfl) ⟨130770, by rfl⟩ : syracuseStep 1394885 = 261541) (by norm_num)
theorem B1591501 : Blo 928581 1591501 := bbase (se 3 (by rfl) ⟨298406, by rfl⟩ : syracuseStep 1591501 = 596813) (by norm_num)
theorem B1394909 : Blo 928581 1394909 := bbase (se 3 (by rfl) ⟨261545, by rfl⟩ : syracuseStep 1394909 = 523091) (by norm_num)
theorem B1394933 : Blo 928581 1394933 := bbase (se 5 (by rfl) ⟨65387, by rfl⟩ : syracuseStep 1394933 = 130775) (by norm_num)
theorem B1394957 : Blo 928581 1394957 := bbase (se 3 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 1394957 = 523109) (by norm_num)
theorem B1394981 : Blo 928581 1394981 := bbase (se 4 (by rfl) ⟨130779, by rfl⟩ : syracuseStep 1394981 = 261559) (by norm_num)
theorem B1395005 : Blo 928581 1395005 := bbase (se 3 (by rfl) ⟨261563, by rfl⟩ : syracuseStep 1395005 = 523127) (by norm_num)
theorem B1395029 : Blo 928581 1395029 := bbase (se 10 (by rfl) ⟨2043, by rfl⟩ : syracuseStep 1395029 = 4087) (by norm_num)
theorem B1395053 : Blo 928581 1395053 := bbase (se 3 (by rfl) ⟨261572, by rfl⟩ : syracuseStep 1395053 = 523145) (by norm_num)
theorem B1395077 : Blo 928581 1395077 := bbase (se 4 (by rfl) ⟨130788, by rfl⟩ : syracuseStep 1395077 = 261577) (by norm_num)
theorem B1984925 : Blo 928581 1984925 := bbase (se 3 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 1984925 = 744347) (by norm_num)
theorem B1395101 : Blo 928581 1395101 := bbase (se 3 (by rfl) ⟨261581, by rfl⟩ : syracuseStep 1395101 = 523163) (by norm_num)
theorem B1395125 : Blo 928581 1395125 := bbase (se 5 (by rfl) ⟨65396, by rfl⟩ : syracuseStep 1395125 = 130793) (by norm_num)
theorem B1395149 : Blo 928581 1395149 := bbase (se 3 (by rfl) ⟨261590, by rfl⟩ : syracuseStep 1395149 = 523181) (by norm_num)
theorem B1395173 : Blo 928581 1395173 := bbase (se 4 (by rfl) ⟨130797, by rfl⟩ : syracuseStep 1395173 = 261595) (by norm_num)
theorem B1395197 : Blo 928581 1395197 := bbase (se 3 (by rfl) ⟨261599, by rfl⟩ : syracuseStep 1395197 = 523199) (by norm_num)
theorem B1395221 : Blo 928581 1395221 := bbase (se 6 (by rfl) ⟨32700, by rfl⟩ : syracuseStep 1395221 = 65401) (by norm_num)
theorem B1493525 : Blo 928581 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B1395245 : Blo 928581 1395245 := bbase (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) (by norm_num)
theorem B1395269 : Blo 928581 1395269 := bbase (se 4 (by rfl) ⟨130806, by rfl⟩ : syracuseStep 1395269 = 261613) (by norm_num)
theorem B1395293 : Blo 928581 1395293 := bbase (se 3 (by rfl) ⟨261617, by rfl⟩ : syracuseStep 1395293 = 523235) (by norm_num)
theorem B1395317 : Blo 928581 1395317 := bbase (se 5 (by rfl) ⟨65405, by rfl⟩ : syracuseStep 1395317 = 130811) (by norm_num)
theorem B1395341 : Blo 928581 1395341 := bbase (se 3 (by rfl) ⟨261626, by rfl⟩ : syracuseStep 1395341 = 523253) (by norm_num)
theorem B1395365 : Blo 928581 1395365 := bbase (se 4 (by rfl) ⟨130815, by rfl⟩ : syracuseStep 1395365 = 261631) (by norm_num)
theorem B1395389 : Blo 928581 1395389 := bbase (se 3 (by rfl) ⟨261635, by rfl⟩ : syracuseStep 1395389 = 523271) (by norm_num)
theorem B4704965 : Blo 928581 4704965 := bbase (se 4 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 4704965 = 882181) (by norm_num)
theorem B1395413 : Blo 928581 1395413 := bbase (se 7 (by rfl) ⟨16352, by rfl⟩ : syracuseStep 1395413 = 32705) (by norm_num)
theorem B1395437 : Blo 928581 1395437 := bbase (se 3 (by rfl) ⟨261644, by rfl⟩ : syracuseStep 1395437 = 523289) (by norm_num)
theorem B1395461 : Blo 928581 1395461 := bbase (se 4 (by rfl) ⟨130824, by rfl⟩ : syracuseStep 1395461 = 261649) (by norm_num)
theorem B1395485 : Blo 928581 1395485 := bbase (se 3 (by rfl) ⟨261653, by rfl⟩ : syracuseStep 1395485 = 523307) (by norm_num)
theorem B1395509 : Blo 928581 1395509 := bbase (se 5 (by rfl) ⟨65414, by rfl⟩ : syracuseStep 1395509 = 130829) (by norm_num)
theorem B1395533 : Blo 928581 1395533 := bbase (se 3 (by rfl) ⟨261662, by rfl⟩ : syracuseStep 1395533 = 523325) (by norm_num)
theorem B1395557 : Blo 928581 1395557 := bbase (se 4 (by rfl) ⟨130833, by rfl⟩ : syracuseStep 1395557 = 261667) (by norm_num)
theorem B1395581 : Blo 928581 1395581 := bbase (se 3 (by rfl) ⟨261671, by rfl⟩ : syracuseStep 1395581 = 523343) (by norm_num)
theorem B1395605 : Blo 928581 1395605 := bbase (se 6 (by rfl) ⟨32709, by rfl⟩ : syracuseStep 1395605 = 65419) (by norm_num)
theorem B1395629 : Blo 928581 1395629 := bbase (se 3 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 1395629 = 523361) (by norm_num)
theorem B1395653 : Blo 928581 1395653 := bbase (se 4 (by rfl) ⟨130842, by rfl⟩ : syracuseStep 1395653 = 261685) (by norm_num)
theorem B1395677 : Blo 928581 1395677 := bbase (se 3 (by rfl) ⟨261689, by rfl⟩ : syracuseStep 1395677 = 523379) (by norm_num)
theorem B1395701 : Blo 928581 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B1395725 : Blo 928581 1395725 := bbase (se 3 (by rfl) ⟨261698, by rfl⟩ : syracuseStep 1395725 = 523397) (by norm_num)
theorem B1592341 : Blo 928581 1592341 := bbase (se 6 (by rfl) ⟨37320, by rfl⟩ : syracuseStep 1592341 = 74641) (by norm_num)
theorem B1395749 : Blo 928581 1395749 := bbase (se 4 (by rfl) ⟨130851, by rfl⟩ : syracuseStep 1395749 = 261703) (by norm_num)
theorem B1395773 : Blo 928581 1395773 := bbase (se 3 (by rfl) ⟨261707, by rfl⟩ : syracuseStep 1395773 = 523415) (by norm_num)
theorem B1395797 : Blo 928581 1395797 := bbase (se 8 (by rfl) ⟨8178, by rfl⟩ : syracuseStep 1395797 = 16357) (by norm_num)
theorem B1395821 : Blo 928581 1395821 := bbase (se 3 (by rfl) ⟨261716, by rfl⟩ : syracuseStep 1395821 = 523433) (by norm_num)
theorem B1395845 : Blo 928581 1395845 := bbase (se 4 (by rfl) ⟨130860, by rfl⟩ : syracuseStep 1395845 = 261721) (by norm_num)
theorem B1789069 : Blo 928581 1789069 := bbase (se 3 (by rfl) ⟨335450, by rfl⟩ : syracuseStep 1789069 = 670901) (by norm_num)
theorem B1395869 : Blo 928581 1395869 := bbase (se 3 (by rfl) ⟨261725, by rfl⟩ : syracuseStep 1395869 = 523451) (by norm_num)
theorem B1395893 : Blo 928581 1395893 := bbase (se 5 (by rfl) ⟨65432, by rfl⟩ : syracuseStep 1395893 = 130865) (by norm_num)
theorem B1395917 : Blo 928581 1395917 := bbase (se 3 (by rfl) ⟨261734, by rfl⟩ : syracuseStep 1395917 = 523469) (by norm_num)
theorem B1395941 : Blo 928581 1395941 := bbase (se 4 (by rfl) ⟨130869, by rfl⟩ : syracuseStep 1395941 = 261739) (by norm_num)
theorem B1985789 : Blo 928581 1985789 := bbase (se 3 (by rfl) ⟨372335, by rfl⟩ : syracuseStep 1985789 = 744671) (by norm_num)
theorem B1395965 : Blo 928581 1395965 := bbase (se 3 (by rfl) ⟨261743, by rfl⟩ : syracuseStep 1395965 = 523487) (by norm_num)
theorem B1395989 : Blo 928581 1395989 := bbase (se 6 (by rfl) ⟨32718, by rfl⟩ : syracuseStep 1395989 = 65437) (by norm_num)
theorem B2870549 : Blo 928581 2870549 := bbase (se 6 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 2870549 = 134557) (by norm_num)
theorem B1396013 : Blo 928581 1396013 := bbase (se 3 (by rfl) ⟨261752, by rfl⟩ : syracuseStep 1396013 = 523505) (by norm_num)
theorem B1396037 : Blo 928581 1396037 := bbase (se 4 (by rfl) ⟨130878, by rfl⟩ : syracuseStep 1396037 = 261757) (by norm_num)
theorem B1396061 : Blo 928581 1396061 := bbase (se 3 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 1396061 = 523523) (by norm_num)
theorem B1396085 : Blo 928581 1396085 := bbase (se 5 (by rfl) ⟨65441, by rfl⟩ : syracuseStep 1396085 = 130883) (by norm_num)
theorem B1985933 : Blo 928581 1985933 := bbase (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) (by norm_num)
theorem B1396109 : Blo 928581 1396109 := bbase (se 3 (by rfl) ⟨261770, by rfl⟩ : syracuseStep 1396109 = 523541) (by norm_num)
theorem B3526037 : Blo 928581 3526037 := bbase (se 6 (by rfl) ⟨82641, by rfl⟩ : syracuseStep 3526037 = 165283) (by norm_num)
theorem B7064981 : Blo 928581 7064981 := bbase (se 6 (by rfl) ⟨165585, by rfl⟩ : syracuseStep 7064981 = 331171) (by norm_num)
theorem B1396133 : Blo 928581 1396133 := bbase (se 4 (by rfl) ⟨130887, by rfl⟩ : syracuseStep 1396133 = 261775) (by norm_num)
theorem B1396157 : Blo 928581 1396157 := bbase (se 3 (by rfl) ⟨261779, by rfl⟩ : syracuseStep 1396157 = 523559) (by norm_num)
theorem B1396181 : Blo 928581 1396181 := bbase (se 7 (by rfl) ⟨16361, by rfl⟩ : syracuseStep 1396181 = 32723) (by norm_num)
theorem B1396205 : Blo 928581 1396205 := bbase (se 3 (by rfl) ⟨261788, by rfl⟩ : syracuseStep 1396205 = 523577) (by norm_num)
theorem B1396229 : Blo 928581 1396229 := bbase (se 4 (by rfl) ⟨130896, by rfl⟩ : syracuseStep 1396229 = 261793) (by norm_num)
theorem B1396253 : Blo 928581 1396253 := bbase (se 3 (by rfl) ⟨261797, by rfl⟩ : syracuseStep 1396253 = 523595) (by norm_num)
theorem B1396277 : Blo 928581 1396277 := bbase (se 5 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 1396277 = 130901) (by norm_num)
theorem B1396301 : Blo 928581 1396301 := bbase (se 3 (by rfl) ⟨261806, by rfl⟩ : syracuseStep 1396301 = 523613) (by norm_num)
theorem B1396325 : Blo 928581 1396325 := bbase (se 4 (by rfl) ⟨130905, by rfl⟩ : syracuseStep 1396325 = 261811) (by norm_num)
theorem B1396349 : Blo 928581 1396349 := bbase (se 3 (by rfl) ⟨261815, by rfl⟩ : syracuseStep 1396349 = 523631) (by norm_num)
theorem B1396373 : Blo 928581 1396373 := bbase (se 6 (by rfl) ⟨32727, by rfl⟩ : syracuseStep 1396373 = 65455) (by norm_num)
theorem B1396397 : Blo 928581 1396397 := bbase (se 3 (by rfl) ⟨261824, by rfl⟩ : syracuseStep 1396397 = 523649) (by norm_num)
theorem B3526325 : Blo 928581 3526325 := bbase (se 5 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 3526325 = 330593) (by norm_num)
theorem B1396421 : Blo 928581 1396421 := bbase (se 4 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 1396421 = 261829) (by norm_num)
theorem B1396445 : Blo 928581 1396445 := bbase (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) (by norm_num)
theorem B1396469 : Blo 928581 1396469 := bbase (se 5 (by rfl) ⟨65459, by rfl⟩ : syracuseStep 1396469 = 130919) (by norm_num)
theorem B1396493 : Blo 928581 1396493 := bbase (se 3 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 1396493 = 523685) (by norm_num)
theorem B1396517 : Blo 928581 1396517 := bbase (se 4 (by rfl) ⟨130923, by rfl⟩ : syracuseStep 1396517 = 261847) (by norm_num)
theorem B1396541 : Blo 928581 1396541 := bbase (se 3 (by rfl) ⟨261851, by rfl⟩ : syracuseStep 1396541 = 523703) (by norm_num)
theorem B1396565 : Blo 928581 1396565 := bbase (se 9 (by rfl) ⟨4091, by rfl⟩ : syracuseStep 1396565 = 8183) (by norm_num)
theorem B1396589 : Blo 928581 1396589 := bbase (se 3 (by rfl) ⟨261860, by rfl⟩ : syracuseStep 1396589 = 523721) (by norm_num)
theorem B1396613 : Blo 928581 1396613 := bbase (se 4 (by rfl) ⟨130932, by rfl⟩ : syracuseStep 1396613 = 261865) (by norm_num)
theorem B1396637 : Blo 928581 1396637 := bbase (se 3 (by rfl) ⟨261869, by rfl⟩ : syracuseStep 1396637 = 523739) (by norm_num)
theorem B1396661 : Blo 928581 1396661 := bbase (se 5 (by rfl) ⟨65468, by rfl⟩ : syracuseStep 1396661 = 130937) (by norm_num)
theorem B1396685 : Blo 928581 1396685 := bbase (se 3 (by rfl) ⟨261878, by rfl⟩ : syracuseStep 1396685 = 523757) (by norm_num)
theorem B4706261 : Blo 928581 4706261 := bbase (se 7 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 4706261 = 110303) (by norm_num)
theorem B1396709 : Blo 928581 1396709 := bbase (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) (by norm_num)
theorem B1396733 : Blo 928581 1396733 := bbase (se 3 (by rfl) ⟨261887, by rfl⟩ : syracuseStep 1396733 = 523775) (by norm_num)
theorem B1396757 : Blo 928581 1396757 := bbase (se 6 (by rfl) ⟨32736, by rfl⟩ : syracuseStep 1396757 = 65473) (by norm_num)
theorem B1396781 : Blo 928581 1396781 := bbase (se 3 (by rfl) ⟨261896, by rfl⟩ : syracuseStep 1396781 = 523793) (by norm_num)
theorem B1396805 : Blo 928581 1396805 := bbase (se 4 (by rfl) ⟨130950, by rfl⟩ : syracuseStep 1396805 = 261901) (by norm_num)
theorem B1396829 : Blo 928581 1396829 := bbase (se 3 (by rfl) ⟨261905, by rfl⟩ : syracuseStep 1396829 = 523811) (by norm_num)
theorem B1986677 : Blo 928581 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B1396853 : Blo 928581 1396853 := bbase (se 5 (by rfl) ⟨65477, by rfl⟩ : syracuseStep 1396853 = 130955) (by norm_num)
theorem B1396877 : Blo 928581 1396877 := bbase (se 3 (by rfl) ⟨261914, by rfl⟩ : syracuseStep 1396877 = 523829) (by norm_num)
theorem B1396901 : Blo 928581 1396901 := bbase (se 4 (by rfl) ⟨130959, by rfl⟩ : syracuseStep 1396901 = 261919) (by norm_num)
theorem B1396925 : Blo 928581 1396925 := bbase (se 3 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 1396925 = 523847) (by norm_num)
theorem B1396949 : Blo 928581 1396949 := bbase (se 7 (by rfl) ⟨16370, by rfl⟩ : syracuseStep 1396949 = 32741) (by norm_num)
theorem B1396973 : Blo 928581 1396973 := bbase (se 3 (by rfl) ⟨261932, by rfl⟩ : syracuseStep 1396973 = 523865) (by norm_num)
theorem B1396997 : Blo 928581 1396997 := bbase (se 4 (by rfl) ⟨130968, by rfl⟩ : syracuseStep 1396997 = 261937) (by norm_num)
theorem B1397021 : Blo 928581 1397021 := bbase (se 3 (by rfl) ⟨261941, by rfl⟩ : syracuseStep 1397021 = 523883) (by norm_num)
theorem B1397045 : Blo 928581 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B1397069 : Blo 928581 1397069 := bbase (se 3 (by rfl) ⟨261950, by rfl⟩ : syracuseStep 1397069 = 523901) (by norm_num)
theorem B1397093 : Blo 928581 1397093 := bbase (se 4 (by rfl) ⟨130977, by rfl⟩ : syracuseStep 1397093 = 261955) (by norm_num)
theorem B1397117 : Blo 928581 1397117 := bbase (se 3 (by rfl) ⟨261959, by rfl⟩ : syracuseStep 1397117 = 523919) (by norm_num)
theorem B1397141 : Blo 928581 1397141 := bbase (se 6 (by rfl) ⟨32745, by rfl⟩ : syracuseStep 1397141 = 65491) (by norm_num)
theorem B1397165 : Blo 928581 1397165 := bbase (se 3 (by rfl) ⟨261968, by rfl⟩ : syracuseStep 1397165 = 523937) (by norm_num)
theorem B1397189 : Blo 928581 1397189 := bbase (se 4 (by rfl) ⟨130986, by rfl⟩ : syracuseStep 1397189 = 261973) (by norm_num)
theorem B1397213 : Blo 928581 1397213 := bbase (se 3 (by rfl) ⟨261977, by rfl⟩ : syracuseStep 1397213 = 523955) (by norm_num)
theorem B1397237 : Blo 928581 1397237 := bbase (se 5 (by rfl) ⟨65495, by rfl⟩ : syracuseStep 1397237 = 130991) (by norm_num)
theorem B1397261 : Blo 928581 1397261 := bbase (se 3 (by rfl) ⟨261986, by rfl⟩ : syracuseStep 1397261 = 523973) (by norm_num)
theorem B1397285 : Blo 928581 1397285 := bbase (se 4 (by rfl) ⟨130995, by rfl⟩ : syracuseStep 1397285 = 261991) (by norm_num)
theorem B1397309 : Blo 928581 1397309 := bbase (se 3 (by rfl) ⟨261995, by rfl⟩ : syracuseStep 1397309 = 523991) (by norm_num)
theorem B1397333 : Blo 928581 1397333 := bbase (se 8 (by rfl) ⟨8187, by rfl⟩ : syracuseStep 1397333 = 16375) (by norm_num)
theorem B1397357 : Blo 928581 1397357 := bbase (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) (by norm_num)
theorem B1397381 : Blo 928581 1397381 := bbase (se 4 (by rfl) ⟨131004, by rfl⟩ : syracuseStep 1397381 = 262009) (by norm_num)
theorem B1397405 : Blo 928581 1397405 := bbase (se 3 (by rfl) ⟨262013, by rfl⟩ : syracuseStep 1397405 = 524027) (by norm_num)
theorem B1397429 : Blo 928581 1397429 := bbase (se 5 (by rfl) ⟨65504, by rfl⟩ : syracuseStep 1397429 = 131009) (by norm_num)
theorem B1397453 : Blo 928581 1397453 := bbase (se 3 (by rfl) ⟨262022, by rfl⟩ : syracuseStep 1397453 = 524045) (by norm_num)
theorem B1397477 : Blo 928581 1397477 := bbase (se 4 (by rfl) ⟨131013, by rfl⟩ : syracuseStep 1397477 = 262027) (by norm_num)
theorem B1397501 : Blo 928581 1397501 := bbase (se 3 (by rfl) ⟨262031, by rfl⟩ : syracuseStep 1397501 = 524063) (by norm_num)
theorem B3134213 : Blo 928581 3134213 := bbase (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) (by norm_num)
theorem B1397525 : Blo 928581 1397525 := bbase (se 6 (by rfl) ⟨32754, by rfl⟩ : syracuseStep 1397525 = 65509) (by norm_num)
theorem B1397549 : Blo 928581 1397549 := bbase (se 3 (by rfl) ⟨262040, by rfl⟩ : syracuseStep 1397549 = 524081) (by norm_num)
theorem B1397573 : Blo 928581 1397573 := bbase (se 4 (by rfl) ⟨131022, by rfl⟩ : syracuseStep 1397573 = 262045) (by norm_num)
theorem B3527509 : Blo 928581 3527509 := bbase (se 9 (by rfl) ⟨10334, by rfl⟩ : syracuseStep 3527509 = 20669) (by norm_num)
theorem B67982165 : Blo 928581 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B1397597 : Blo 928581 1397597 := bbase (se 3 (by rfl) ⟨262049, by rfl⟩ : syracuseStep 1397597 = 524099) (by norm_num)
theorem B1987429 : Blo 928581 1987429 := bbase (se 4 (by rfl) ⟨186321, by rfl⟩ : syracuseStep 1987429 = 372643) (by norm_num)
theorem B3232613 : Blo 928581 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B1397621 : Blo 928581 1397621 := bbase (se 5 (by rfl) ⟨65513, by rfl⟩ : syracuseStep 1397621 = 131027) (by norm_num)
theorem B1397645 : Blo 928581 1397645 := bbase (se 3 (by rfl) ⟨262058, by rfl⟩ : syracuseStep 1397645 = 524117) (by norm_num)
theorem B1889173 : Blo 928581 1889173 := bbase (se 6 (by rfl) ⟨44277, by rfl⟩ : syracuseStep 1889173 = 88555) (by norm_num)
theorem B1397669 : Blo 928581 1397669 := bbase (se 4 (by rfl) ⟨131031, by rfl⟩ : syracuseStep 1397669 = 262063) (by norm_num)
theorem B1397693 : Blo 928581 1397693 := bbase (se 3 (by rfl) ⟨262067, by rfl⟩ : syracuseStep 1397693 = 524135) (by norm_num)
theorem B1397717 : Blo 928581 1397717 := bbase (se 7 (by rfl) ⟨16379, by rfl⟩ : syracuseStep 1397717 = 32759) (by norm_num)
theorem B1397741 : Blo 928581 1397741 := bbase (se 3 (by rfl) ⟨262076, by rfl⟩ : syracuseStep 1397741 = 524153) (by norm_num)
theorem B1987573 : Blo 928581 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B1397765 : Blo 928581 1397765 := bbase (se 4 (by rfl) ⟨131040, by rfl⟩ : syracuseStep 1397765 = 262081) (by norm_num)
theorem B2184197 : Blo 928581 2184197 := bbase (se 4 (by rfl) ⟨204768, by rfl⟩ : syracuseStep 2184197 = 409537) (by norm_num)
theorem B1397789 : Blo 928581 1397789 := bbase (se 3 (by rfl) ⟨262085, by rfl⟩ : syracuseStep 1397789 = 524171) (by norm_num)
theorem B1397813 : Blo 928581 1397813 := bbase (se 5 (by rfl) ⟨65522, by rfl⟩ : syracuseStep 1397813 = 131045) (by norm_num)
theorem B1397837 : Blo 928581 1397837 := bbase (se 3 (by rfl) ⟨262094, by rfl⟩ : syracuseStep 1397837 = 524189) (by norm_num)
theorem B1397861 : Blo 928581 1397861 := bbase (se 4 (by rfl) ⟨131049, by rfl⟩ : syracuseStep 1397861 = 262099) (by norm_num)
theorem B1397885 : Blo 928581 1397885 := bbase (se 3 (by rfl) ⟨262103, by rfl⟩ : syracuseStep 1397885 = 524207) (by norm_num)
theorem B3527813 : Blo 928581 3527813 := bbase (se 4 (by rfl) ⟨330732, by rfl⟩ : syracuseStep 3527813 = 661465) (by norm_num)
theorem B1397909 : Blo 928581 1397909 := bbase (se 6 (by rfl) ⟨32763, by rfl⟩ : syracuseStep 1397909 = 65527) (by norm_num)
theorem B1397933 : Blo 928581 1397933 := bbase (se 3 (by rfl) ⟨262112, by rfl⟩ : syracuseStep 1397933 = 524225) (by norm_num)
theorem B3134645 : Blo 928581 3134645 := bbase (se 5 (by rfl) ⟨146936, by rfl⟩ : syracuseStep 3134645 = 293873) (by norm_num)
theorem B1397957 : Blo 928581 1397957 := bbase (se 4 (by rfl) ⟨131058, by rfl⟩ : syracuseStep 1397957 = 262117) (by norm_num)
theorem B1397981 : Blo 928581 1397981 := bbase (se 3 (by rfl) ⟨262121, by rfl⟩ : syracuseStep 1397981 = 524243) (by norm_num)
theorem B4707557 : Blo 928581 4707557 := bbase (se 4 (by rfl) ⟨441333, by rfl⟩ : syracuseStep 4707557 = 882667) (by norm_num)
theorem B6706421 : Blo 928581 6706421 := bbase (se 5 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 6706421 = 628727) (by norm_num)
theorem B1398005 : Blo 928581 1398005 := bbase (se 5 (by rfl) ⟨65531, by rfl⟩ : syracuseStep 1398005 = 131063) (by norm_num)
theorem B1398029 : Blo 928581 1398029 := bbase (se 3 (by rfl) ⟨262130, by rfl⟩ : syracuseStep 1398029 = 524261) (by norm_num)
theorem B7165205 : Blo 928581 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B1398053 : Blo 928581 1398053 := bbase (se 4 (by rfl) ⟨131067, by rfl⟩ : syracuseStep 1398053 = 262135) (by norm_num)
theorem B3626293 : Blo 928581 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B1398077 : Blo 928581 1398077 := bbase (se 3 (by rfl) ⟨262139, by rfl⟩ : syracuseStep 1398077 = 524279) (by norm_num)
theorem B1398101 : Blo 928581 1398101 := bbase (se 22 (by rfl) ⟨0, by rfl⟩ : syracuseStep 1398101 = 1) (by norm_num)
theorem B1987949 : Blo 928581 1987949 := bbase (se 3 (by rfl) ⟨372740, by rfl⟩ : syracuseStep 1987949 = 745481) (by norm_num)
theorem B1398125 : Blo 928581 1398125 := bbase (se 3 (by rfl) ⟨262148, by rfl⟩ : syracuseStep 1398125 = 524297) (by norm_num)
theorem B1398149 : Blo 928581 1398149 := bbase (se 4 (by rfl) ⟨131076, by rfl⟩ : syracuseStep 1398149 = 262153) (by norm_num)
theorem B13620629 : Blo 928581 13620629 := bbase (se 6 (by rfl) ⟨319233, by rfl⟩ : syracuseStep 13620629 = 638467) (by norm_num)
theorem B1398173 : Blo 928581 1398173 := bbase (se 3 (by rfl) ⟨262157, by rfl⟩ : syracuseStep 1398173 = 524315) (by norm_num)
theorem B1398197 : Blo 928581 1398197 := bbase (se 5 (by rfl) ⟨65540, by rfl⟩ : syracuseStep 1398197 = 131081) (by norm_num)
theorem B1398221 : Blo 928581 1398221 := bbase (se 3 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 1398221 = 524333) (by norm_num)
theorem B1398245 : Blo 928581 1398245 := bbase (se 4 (by rfl) ⟨131085, by rfl⟩ : syracuseStep 1398245 = 262171) (by norm_num)
theorem B1889773 : Blo 928581 1889773 := bbase (se 3 (by rfl) ⟨354332, by rfl⟩ : syracuseStep 1889773 = 708665) (by norm_num)
theorem B1398269 : Blo 928581 1398269 := bbase (se 3 (by rfl) ⟨262175, by rfl⟩ : syracuseStep 1398269 = 524351) (by norm_num)
theorem B1398293 : Blo 928581 1398293 := bbase (se 6 (by rfl) ⟨32772, by rfl⟩ : syracuseStep 1398293 = 65545) (by norm_num)
theorem B1791533 : Blo 928581 1791533 := bbase (se 3 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 1791533 = 671825) (by norm_num)
theorem B1398317 : Blo 928581 1398317 := bbase (se 3 (by rfl) ⟨262184, by rfl⟩ : syracuseStep 1398317 = 524369) (by norm_num)
theorem B2512453 : Blo 928581 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B1398341 : Blo 928581 1398341 := bbase (se 4 (by rfl) ⟨131094, by rfl⟩ : syracuseStep 1398341 = 262189) (by norm_num)
theorem B1398365 : Blo 928581 1398365 := bbase (se 3 (by rfl) ⟨262193, by rfl⟩ : syracuseStep 1398365 = 524387) (by norm_num)
theorem B3135077 : Blo 928581 3135077 := bbase (se 4 (by rfl) ⟨293913, by rfl⟩ : syracuseStep 3135077 = 587827) (by norm_num)
theorem B1398389 : Blo 928581 1398389 := bbase (se 5 (by rfl) ⟨65549, by rfl⟩ : syracuseStep 1398389 = 131099) (by norm_num)
theorem B1398413 : Blo 928581 1398413 := bbase (se 3 (by rfl) ⟨262202, by rfl⟩ : syracuseStep 1398413 = 524405) (by norm_num)
theorem B1791653 : Blo 928581 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B1398437 : Blo 928581 1398437 := bbase (se 4 (by rfl) ⟨131103, by rfl⟩ : syracuseStep 1398437 = 262207) (by norm_num)
theorem B1398461 : Blo 928581 1398461 := bbase (se 3 (by rfl) ⟨262211, by rfl⟩ : syracuseStep 1398461 = 524423) (by norm_num)
theorem B1398485 : Blo 928581 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B1988317 : Blo 928581 1988317 := bbase (se 3 (by rfl) ⟨372809, by rfl⟩ : syracuseStep 1988317 = 745619) (by norm_num)
theorem B1398509 : Blo 928581 1398509 := bbase (se 3 (by rfl) ⟨262220, by rfl⟩ : syracuseStep 1398509 = 524441) (by norm_num)
theorem B1398533 : Blo 928581 1398533 := bbase (se 4 (by rfl) ⟨131112, by rfl⟩ : syracuseStep 1398533 = 262225) (by norm_num)
theorem B1398557 : Blo 928581 1398557 := bbase (se 3 (by rfl) ⟨262229, by rfl⟩ : syracuseStep 1398557 = 524459) (by norm_num)
theorem B1398581 : Blo 928581 1398581 := bbase (se 5 (by rfl) ⟨65558, by rfl⟩ : syracuseStep 1398581 = 131117) (by norm_num)
theorem B1398605 : Blo 928581 1398605 := bbase (se 3 (by rfl) ⟨262238, by rfl⟩ : syracuseStep 1398605 = 524477) (by norm_num)
theorem B1398629 : Blo 928581 1398629 := bbase (se 4 (by rfl) ⟨131121, by rfl⟩ : syracuseStep 1398629 = 262243) (by norm_num)
theorem B1398653 : Blo 928581 1398653 := bbase (se 3 (by rfl) ⟨262247, by rfl⟩ : syracuseStep 1398653 = 524495) (by norm_num)
theorem B1398677 : Blo 928581 1398677 := bbase (se 6 (by rfl) ⟨32781, by rfl⟩ : syracuseStep 1398677 = 65563) (by norm_num)
theorem B4478885 : Blo 928581 4478885 := bbase (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) (by norm_num)
theorem B1398701 : Blo 928581 1398701 := bbase (se 3 (by rfl) ⟨262256, by rfl⟩ : syracuseStep 1398701 = 524513) (by norm_num)
theorem B1398725 : Blo 928581 1398725 := bbase (se 4 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 1398725 = 262261) (by norm_num)
theorem B5953493 : Blo 928581 5953493 := bbase (se 7 (by rfl) ⟨69767, by rfl⟩ : syracuseStep 5953493 = 139535) (by norm_num)
theorem B1398749 : Blo 928581 1398749 := bbase (se 3 (by rfl) ⟨262265, by rfl⟩ : syracuseStep 1398749 = 524531) (by norm_num)
theorem B1398773 : Blo 928581 1398773 := bbase (se 5 (by rfl) ⟨65567, by rfl⟩ : syracuseStep 1398773 = 131135) (by norm_num)
theorem B1398797 : Blo 928581 1398797 := bbase (se 3 (by rfl) ⟨262274, by rfl⟩ : syracuseStep 1398797 = 524549) (by norm_num)
theorem B3135509 : Blo 928581 3135509 := bbase (se 6 (by rfl) ⟨73488, by rfl⟩ : syracuseStep 3135509 = 146977) (by norm_num)
theorem B1398821 : Blo 928581 1398821 := bbase (se 4 (by rfl) ⟨131139, by rfl⟩ : syracuseStep 1398821 = 262279) (by norm_num)
theorem B1398845 : Blo 928581 1398845 := bbase (se 3 (by rfl) ⟨262283, by rfl⟩ : syracuseStep 1398845 = 524567) (by norm_num)
theorem B1890373 : Blo 928581 1890373 := bbase (se 4 (by rfl) ⟨177222, by rfl⟩ : syracuseStep 1890373 = 354445) (by norm_num)
theorem B2119765 : Blo 928581 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B1398869 : Blo 928581 1398869 := bbase (se 8 (by rfl) ⟨8196, by rfl⟩ : syracuseStep 1398869 = 16393) (by norm_num)
theorem B8477045 : Blo 928581 8477045 := bbase (se 5 (by rfl) ⟨397361, by rfl⟩ : syracuseStep 8477045 = 794723) (by norm_num)
theorem B3135941 : Blo 928581 3135941 := bbase (se 4 (by rfl) ⟨293994, by rfl⟩ : syracuseStep 3135941 = 587989) (by norm_num)
theorem B4708853 : Blo 928581 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B6380117 : Blo 928581 6380117 := bbase (se 8 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 6380117 = 74767) (by norm_num)
theorem B2120357 : Blo 928581 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B3627733 : Blo 928581 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B5298965 : Blo 928581 5298965 := bbase (se 6 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 5298965 = 248389) (by norm_num)
theorem B3824437 : Blo 928581 3824437 := bbase (se 5 (by rfl) ⟨179270, by rfl⟩ : syracuseStep 3824437 = 358541) (by norm_num)
theorem B1006445 : Blo 928581 1006445 := bbase (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) (by norm_num)
theorem B3136373 : Blo 928581 3136373 := bbase (se 5 (by rfl) ⟨147017, by rfl⟩ : syracuseStep 3136373 = 294035) (by norm_num)
theorem B3824501 : Blo 928581 3824501 := bbase (se 5 (by rfl) ⟨179273, by rfl⟩ : syracuseStep 3824501 = 358547) (by norm_num)
theorem B1792901 : Blo 928581 1792901 := bbase (se 4 (by rfl) ⟨168084, by rfl⟩ : syracuseStep 1792901 = 336169) (by norm_num)
theorem B17882005 : Blo 928581 17882005 := bbase (se 6 (by rfl) ⟨419109, by rfl⟩ : syracuseStep 17882005 = 838219) (by norm_num)
theorem B2382797 : Blo 928581 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B2644949 : Blo 928581 2644949 := bbase (se 7 (by rfl) ⟨30995, by rfl⟩ : syracuseStep 2644949 = 61991) (by norm_num)
theorem B1793173 : Blo 928581 1793173 := bbase (se 6 (by rfl) ⟨42027, by rfl⟩ : syracuseStep 1793173 = 84055) (by norm_num)
theorem B5364917 : Blo 928581 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B1989821 : Blo 928581 1989821 := bbase (se 3 (by rfl) ⟨373091, by rfl⟩ : syracuseStep 1989821 = 746183) (by norm_num)
theorem B3529925 : Blo 928581 3529925 := bbase (se 4 (by rfl) ⟨330930, by rfl⟩ : syracuseStep 3529925 = 661861) (by norm_num)
theorem B3136805 : Blo 928581 3136805 := bbase (se 4 (by rfl) ⟨294075, by rfl⟩ : syracuseStep 3136805 = 588151) (by norm_num)
theorem B1989965 : Blo 928581 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B3530213 : Blo 928581 3530213 := bbase (se 4 (by rfl) ⟨330957, by rfl⟩ : syracuseStep 3530213 = 661915) (by norm_num)
theorem B2514485 : Blo 928581 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B1793669 : Blo 928581 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B2350741 : Blo 928581 2350741 := bbase (se 6 (by rfl) ⟨55095, by rfl⟩ : syracuseStep 2350741 = 110191) (by norm_num)
theorem B1990325 : Blo 928581 1990325 := bbase (se 5 (by rfl) ⟨93296, by rfl⟩ : syracuseStep 1990325 = 186593) (by norm_num)
theorem B3137237 : Blo 928581 3137237 := bbase (se 7 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 3137237 = 73529) (by norm_num)
theorem B2350853 : Blo 928581 2350853 := bbase (se 4 (by rfl) ⟨220392, by rfl⟩ : syracuseStep 2350853 = 440785) (by norm_num)
theorem B4710149 : Blo 928581 4710149 := bbase (se 4 (by rfl) ⟨441576, by rfl⟩ : syracuseStep 4710149 = 883153) (by norm_num)
theorem B1793917 : Blo 928581 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B2351045 : Blo 928581 2351045 := bbase (se 4 (by rfl) ⟨220410, by rfl⟩ : syracuseStep 2351045 = 440821) (by norm_num)
theorem B942121 : Blo 928581 942121 := bbase (se 2 (by rfl) ⟨353295, by rfl⟩ : syracuseStep 942121 = 706591) (by norm_num)
theorem B3137669 : Blo 928581 3137669 := bbase (se 4 (by rfl) ⟨294156, by rfl⟩ : syracuseStep 3137669 = 588313) (by norm_num)
theorem B2351389 : Blo 928581 2351389 := bbase (se 3 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 2351389 = 881771) (by norm_num)
theorem B942413 : Blo 928581 942413 := bbase (se 3 (by rfl) ⟨176702, by rfl⟩ : syracuseStep 942413 = 353405) (by norm_num)
theorem B2089349 : Blo 928581 2089349 := bbase (se 4 (by rfl) ⟨195876, by rfl⟩ : syracuseStep 2089349 = 391753) (by norm_num)
theorem B2351501 : Blo 928581 2351501 := bbase (se 3 (by rfl) ⟨440906, by rfl⟩ : syracuseStep 2351501 = 881813) (by norm_num)
theorem B2122181 : Blo 928581 2122181 := bbase (se 4 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 2122181 = 397909) (by norm_num)
theorem B2089421 : Blo 928581 2089421 := bbase (se 3 (by rfl) ⟨391766, by rfl⟩ : syracuseStep 2089421 = 783533) (by norm_num)
theorem B2646533 : Blo 928581 2646533 := bbase (se 4 (by rfl) ⟨248112, by rfl⟩ : syracuseStep 2646533 = 496225) (by norm_num)
theorem B2089493 : Blo 928581 2089493 := bbase (se 6 (by rfl) ⟨48972, by rfl⟩ : syracuseStep 2089493 = 97945) (by norm_num)
theorem B1991213 : Blo 928581 1991213 := bbase (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) (by norm_num)
theorem B3138101 : Blo 928581 3138101 := bbase (se 5 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 3138101 = 294197) (by norm_num)
theorem B2351693 : Blo 928581 2351693 := bbase (se 3 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 2351693 = 881885) (by norm_num)
theorem B942673 : Blo 928581 942673 := bbase (se 2 (by rfl) ⟨353502, by rfl⟩ : syracuseStep 942673 = 707005) (by norm_num)
theorem B2089565 : Blo 928581 2089565 := bbase (se 3 (by rfl) ⟨391793, by rfl⟩ : syracuseStep 2089565 = 783587) (by norm_num)
theorem B942721 : Blo 928581 942721 := bbase (se 2 (by rfl) ⟨353520, by rfl⟩ : syracuseStep 942721 = 707041) (by norm_num)
theorem B3531397 : Blo 928581 3531397 := bbase (se 4 (by rfl) ⟨331068, by rfl⟩ : syracuseStep 3531397 = 662137) (by norm_num)
theorem B2089637 : Blo 928581 2089637 := bbase (se 4 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 2089637 = 391807) (by norm_num)
theorem B2089709 : Blo 928581 2089709 := bbase (se 3 (by rfl) ⟨391820, by rfl⟩ : syracuseStep 2089709 = 783641) (by norm_num)
theorem B1991461 : Blo 928581 1991461 := bbase (se 4 (by rfl) ⟨186699, by rfl⟩ : syracuseStep 1991461 = 373399) (by norm_num)
theorem B2089781 : Blo 928581 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B2089853 : Blo 928581 2089853 := bbase (se 3 (by rfl) ⟨391847, by rfl⟩ : syracuseStep 2089853 = 783695) (by norm_num)
theorem B2352037 : Blo 928581 2352037 := bbase (se 4 (by rfl) ⟨220503, by rfl⟩ : syracuseStep 2352037 = 441007) (by norm_num)
theorem B3531701 : Blo 928581 3531701 := bbase (se 5 (by rfl) ⟨165548, by rfl⟩ : syracuseStep 3531701 = 331097) (by norm_num)
theorem B2089925 : Blo 928581 2089925 := bbase (se 4 (by rfl) ⟨195930, by rfl⟩ : syracuseStep 2089925 = 391861) (by norm_num)
theorem B3138533 : Blo 928581 3138533 := bbase (se 4 (by rfl) ⟨294237, by rfl⟩ : syracuseStep 3138533 = 588475) (by norm_num)
theorem B2089997 : Blo 928581 2089997 := bbase (se 3 (by rfl) ⟨391874, by rfl⟩ : syracuseStep 2089997 = 783749) (by norm_num)
theorem B2352149 : Blo 928581 2352149 := bbase (se 6 (by rfl) ⟨55128, by rfl⟩ : syracuseStep 2352149 = 110257) (by norm_num)
theorem B4711445 : Blo 928581 4711445 := bbase (se 6 (by rfl) ⟨110424, by rfl⟩ : syracuseStep 4711445 = 220849) (by norm_num)
theorem B2090069 : Blo 928581 2090069 := bbase (se 8 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 2090069 = 24493) (by norm_num)
theorem B1434757 : Blo 928581 1434757 := bbase (se 4 (by rfl) ⟨134508, by rfl⟩ : syracuseStep 1434757 = 269017) (by norm_num)
theorem B2090141 : Blo 928581 2090141 := bbase (se 3 (by rfl) ⟨391901, by rfl⟩ : syracuseStep 2090141 = 783803) (by norm_num)
theorem B2647205 : Blo 928581 2647205 := bbase (se 4 (by rfl) ⟨248175, by rfl⟩ : syracuseStep 2647205 = 496351) (by norm_num)
theorem B2352341 : Blo 928581 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B2090213 : Blo 928581 2090213 := bbase (se 4 (by rfl) ⟨195957, by rfl⟩ : syracuseStep 2090213 = 391915) (by norm_num)
theorem B2090285 : Blo 928581 2090285 := bbase (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) (by norm_num)
theorem B2385229 : Blo 928581 2385229 := bbase (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) (by norm_num)
theorem B2090357 : Blo 928581 2090357 := bbase (se 5 (by rfl) ⟨97985, by rfl⟩ : syracuseStep 2090357 = 195971) (by norm_num)
theorem B3138965 : Blo 928581 3138965 := bbase (se 6 (by rfl) ⟨73569, by rfl⟩ : syracuseStep 3138965 = 147139) (by norm_num)
theorem B2090429 : Blo 928581 2090429 := bbase (se 3 (by rfl) ⟨391955, by rfl⟩ : syracuseStep 2090429 = 783911) (by norm_num)
theorem B2090501 : Blo 928581 2090501 := bbase (se 4 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 2090501 = 391969) (by norm_num)
theorem B2352685 : Blo 928581 2352685 := bbase (se 3 (by rfl) ⟨441128, by rfl⟩ : syracuseStep 2352685 = 882257) (by norm_num)
theorem B6809141 : Blo 928581 6809141 := bbase (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) (by norm_num)
theorem B2090573 : Blo 928581 2090573 := bbase (se 3 (by rfl) ⟨391982, by rfl⟩ : syracuseStep 2090573 = 783965) (by norm_num)
theorem B2647637 : Blo 928581 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B23881301 : Blo 928581 23881301 := bbase (se 8 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 23881301 = 279859) (by norm_num)
theorem B2090645 : Blo 928581 2090645 := bbase (se 6 (by rfl) ⟨48999, by rfl⟩ : syracuseStep 2090645 = 97999) (by norm_num)
theorem B2352797 : Blo 928581 2352797 := bbase (se 3 (by rfl) ⟨441149, by rfl⟩ : syracuseStep 2352797 = 882299) (by norm_num)
theorem B20113109 : Blo 928581 20113109 := bbase (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) (by norm_num)
theorem B2090717 : Blo 928581 2090717 := bbase (se 3 (by rfl) ⟨392009, by rfl⟩ : syracuseStep 2090717 = 784019) (by norm_num)
theorem B943849 : Blo 928581 943849 := bbase (se 2 (by rfl) ⟨353943, by rfl⟩ : syracuseStep 943849 = 707887) (by norm_num)
theorem B2090789 : Blo 928581 2090789 := bbase (se 4 (by rfl) ⟨196011, by rfl⟩ : syracuseStep 2090789 = 392023) (by norm_num)
theorem B1763117 : Blo 928581 1763117 := bbase (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) (by norm_num)
theorem B3139397 : Blo 928581 3139397 := bbase (se 4 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 3139397 = 588637) (by norm_num)
theorem B2352989 : Blo 928581 2352989 := bbase (se 3 (by rfl) ⟨441185, by rfl⟩ : syracuseStep 2352989 = 882371) (by norm_num)
theorem B1632101 : Blo 928581 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B2090861 : Blo 928581 2090861 := bbase (se 3 (by rfl) ⟨392036, by rfl⟩ : syracuseStep 2090861 = 784073) (by norm_num)
theorem B2090933 : Blo 928581 2090933 := bbase (se 5 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 2090933 = 196025) (by norm_num)
theorem B2091005 : Blo 928581 2091005 := bbase (se 3 (by rfl) ⟨392063, by rfl⟩ : syracuseStep 2091005 = 784127) (by norm_num)
theorem B2091077 : Blo 928581 2091077 := bbase (se 4 (by rfl) ⟨196038, by rfl⟩ : syracuseStep 2091077 = 392077) (by norm_num)
theorem B2091149 : Blo 928581 2091149 := bbase (se 3 (by rfl) ⟨392090, by rfl⟩ : syracuseStep 2091149 = 784181) (by norm_num)
theorem B2418853 : Blo 928581 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B2353333 : Blo 928581 2353333 := bbase (se 5 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 2353333 = 220625) (by norm_num)
theorem B2091221 : Blo 928581 2091221 := bbase (se 7 (by rfl) ⟨24506, by rfl⟩ : syracuseStep 2091221 = 49013) (by norm_num)
theorem B3139829 : Blo 928581 3139829 := bbase (se 5 (by rfl) ⟨147179, by rfl⟩ : syracuseStep 3139829 = 294359) (by norm_num)
theorem B2091293 : Blo 928581 2091293 := bbase (se 3 (by rfl) ⟨392117, by rfl⟩ : syracuseStep 2091293 = 784235) (by norm_num)
theorem B2353445 : Blo 928581 2353445 := bbase (se 4 (by rfl) ⟨220635, by rfl⟩ : syracuseStep 2353445 = 441271) (by norm_num)
theorem B4712741 : Blo 928581 4712741 := bbase (se 4 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 4712741 = 883639) (by norm_num)
theorem B2648389 : Blo 928581 2648389 := bbase (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) (by norm_num)
theorem B944465 : Blo 928581 944465 := bbase (se 2 (by rfl) ⟨354174, by rfl⟩ : syracuseStep 944465 = 708349) (by norm_num)
theorem B2091365 : Blo 928581 2091365 := bbase (se 4 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 2091365 = 392131) (by norm_num)
theorem B1567093 : Blo 928581 1567093 := bbase (se 5 (by rfl) ⟨73457, by rfl⟩ : syracuseStep 1567093 = 146915) (by norm_num)
theorem B2091437 : Blo 928581 2091437 := bbase (se 3 (by rfl) ⟨392144, by rfl⟩ : syracuseStep 2091437 = 784289) (by norm_num)
theorem B2550197 : Blo 928581 2550197 := bbase (se 5 (by rfl) ⟨119540, by rfl⟩ : syracuseStep 2550197 = 239081) (by norm_num)
theorem B1567181 : Blo 928581 1567181 := bbase (se 3 (by rfl) ⟨293846, by rfl⟩ : syracuseStep 1567181 = 587693) (by norm_num)
theorem B2353637 : Blo 928581 2353637 := bbase (se 4 (by rfl) ⟨220653, by rfl⟩ : syracuseStep 2353637 = 441307) (by norm_num)
theorem B2091509 : Blo 928581 2091509 := bbase (se 5 (by rfl) ⟨98039, by rfl⟩ : syracuseStep 2091509 = 196079) (by norm_num)
theorem B1763869 : Blo 928581 1763869 := bbase (se 3 (by rfl) ⟨330725, by rfl⟩ : syracuseStep 1763869 = 661451) (by norm_num)
theorem B2091581 : Blo 928581 2091581 := bbase (se 3 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 2091581 = 784343) (by norm_num)
theorem B1567309 : Blo 928581 1567309 := bbase (se 3 (by rfl) ⟨293870, by rfl⟩ : syracuseStep 1567309 = 587741) (by norm_num)
theorem B2976389 : Blo 928581 2976389 := bbase (se 4 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 2976389 = 558073) (by norm_num)
theorem B2091653 : Blo 928581 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B1567397 : Blo 928581 1567397 := bbase (se 4 (by rfl) ⟨146943, by rfl⟩ : syracuseStep 1567397 = 293887) (by norm_num)
theorem B3140261 : Blo 928581 3140261 := bbase (se 4 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 3140261 = 588799) (by norm_num)
theorem B1764013 : Blo 928581 1764013 := bbase (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) (by norm_num)
theorem B2091725 : Blo 928581 2091725 := bbase (se 3 (by rfl) ⟨392198, by rfl⟩ : syracuseStep 2091725 = 784397) (by norm_num)
theorem B2091797 : Blo 928581 2091797 := bbase (se 6 (by rfl) ⟨49026, by rfl⟩ : syracuseStep 2091797 = 98053) (by norm_num)
theorem B1567525 : Blo 928581 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B2353981 : Blo 928581 2353981 := bbase (se 3 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 2353981 = 882743) (by norm_num)
theorem B1764173 : Blo 928581 1764173 := bbase (se 3 (by rfl) ⟨330782, by rfl⟩ : syracuseStep 1764173 = 661565) (by norm_num)
theorem B2091869 : Blo 928581 2091869 := bbase (se 3 (by rfl) ⟨392225, by rfl⟩ : syracuseStep 2091869 = 784451) (by norm_num)
theorem B1567613 : Blo 928581 1567613 := bbase (se 3 (by rfl) ⟨293927, by rfl⟩ : syracuseStep 1567613 = 587855) (by norm_num)
theorem B2091941 : Blo 928581 2091941 := bbase (se 4 (by rfl) ⟨196119, by rfl⟩ : syracuseStep 2091941 = 392239) (by norm_num)
theorem B2354093 : Blo 928581 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B1764317 : Blo 928581 1764317 := bbase (se 3 (by rfl) ⟨330809, by rfl⟩ : syracuseStep 1764317 = 661619) (by norm_num)
theorem B2092013 : Blo 928581 2092013 := bbase (se 3 (by rfl) ⟨392252, by rfl⟩ : syracuseStep 2092013 = 784505) (by norm_num)
theorem B3533813 : Blo 928581 3533813 := bbase (se 5 (by rfl) ⟨165647, by rfl⟩ : syracuseStep 3533813 = 331295) (by norm_num)
theorem B7072757 : Blo 928581 7072757 := bbase (se 5 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 7072757 = 663071) (by norm_num)
theorem B1567741 : Blo 928581 1567741 := bbase (se 3 (by rfl) ⟨293951, by rfl⟩ : syracuseStep 1567741 = 587903) (by norm_num)
theorem B2092085 : Blo 928581 2092085 := bbase (se 5 (by rfl) ⟨98066, by rfl⟩ : syracuseStep 2092085 = 196133) (by norm_num)
theorem B1567829 : Blo 928581 1567829 := bbase (se 8 (by rfl) ⟨9186, by rfl⟩ : syracuseStep 1567829 = 18373) (by norm_num)
theorem B3140693 : Blo 928581 3140693 := bbase (se 8 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 3140693 = 36805) (by norm_num)
theorem B2518117 : Blo 928581 2518117 := bbase (se 4 (by rfl) ⟨236073, by rfl⟩ : syracuseStep 2518117 = 472147) (by norm_num)
theorem B2354285 : Blo 928581 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B2092157 : Blo 928581 2092157 := bbase (se 3 (by rfl) ⟨392279, by rfl⟩ : syracuseStep 2092157 = 784559) (by norm_num)
theorem B2092229 : Blo 928581 2092229 := bbase (se 4 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 2092229 = 392293) (by norm_num)
theorem B1567957 : Blo 928581 1567957 := bbase (se 7 (by rfl) ⟨18374, by rfl⟩ : syracuseStep 1567957 = 36749) (by norm_num)
theorem B1764605 : Blo 928581 1764605 := bbase (se 3 (by rfl) ⟨330863, by rfl⟩ : syracuseStep 1764605 = 661727) (by norm_num)
theorem B2092301 : Blo 928581 2092301 := bbase (se 3 (by rfl) ⟨392306, by rfl⟩ : syracuseStep 2092301 = 784613) (by norm_num)
theorem B3534101 : Blo 928581 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B1568045 : Blo 928581 1568045 := bbase (se 3 (by rfl) ⟨294008, by rfl⟩ : syracuseStep 1568045 = 588017) (by norm_num)
theorem B2092373 : Blo 928581 2092373 := bbase (se 11 (by rfl) ⟨1532, by rfl⟩ : syracuseStep 2092373 = 3065) (by norm_num)
theorem B2977157 : Blo 928581 2977157 := bbase (se 4 (by rfl) ⟨279108, by rfl⟩ : syracuseStep 2977157 = 558217) (by norm_num)
theorem B1764757 : Blo 928581 1764757 := bbase (se 6 (by rfl) ⟨41361, by rfl⟩ : syracuseStep 1764757 = 82723) (by norm_num)
theorem B2092445 : Blo 928581 2092445 := bbase (se 3 (by rfl) ⟨392333, by rfl⟩ : syracuseStep 2092445 = 784667) (by norm_num)
theorem B1568173 : Blo 928581 1568173 := bbase (se 3 (by rfl) ⟨294032, by rfl⟩ : syracuseStep 1568173 = 588065) (by norm_num)
theorem B2354629 : Blo 928581 2354629 := bbase (se 4 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 2354629 = 441493) (by norm_num)
theorem B2092517 : Blo 928581 2092517 := bbase (se 4 (by rfl) ⟨196173, by rfl⟩ : syracuseStep 2092517 = 392347) (by norm_num)
theorem B1568261 : Blo 928581 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B3141125 : Blo 928581 3141125 := bbase (se 4 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 3141125 = 588961) (by norm_num)
theorem B2092589 : Blo 928581 2092589 := bbase (se 3 (by rfl) ⟨392360, by rfl⟩ : syracuseStep 2092589 = 784721) (by norm_num)
theorem B4714037 : Blo 928581 4714037 := bbase (se 5 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 4714037 = 441941) (by norm_num)
theorem B2354741 : Blo 928581 2354741 := bbase (se 5 (by rfl) ⟨110378, by rfl⟩ : syracuseStep 2354741 = 220757) (by norm_num)
theorem B2092661 : Blo 928581 2092661 := bbase (se 5 (by rfl) ⟨98093, by rfl⟩ : syracuseStep 2092661 = 196187) (by norm_num)
theorem B1568389 : Blo 928581 1568389 := bbase (se 4 (by rfl) ⟨147036, by rfl⟩ : syracuseStep 1568389 = 294073) (by norm_num)
theorem B2092733 : Blo 928581 2092733 := bbase (se 3 (by rfl) ⟨392387, by rfl⟩ : syracuseStep 2092733 = 784775) (by norm_num)
theorem B1765061 : Blo 928581 1765061 := bbase (se 4 (by rfl) ⟨165474, by rfl⟩ : syracuseStep 1765061 = 330949) (by norm_num)
theorem B1175249 : Blo 928581 1175249 := bbase (se 2 (by rfl) ⟨440718, by rfl⟩ : syracuseStep 1175249 = 881437) (by norm_num)
theorem B1568477 : Blo 928581 1568477 := bbase (se 3 (by rfl) ⟨294089, by rfl⟩ : syracuseStep 1568477 = 588179) (by norm_num)
theorem B2354933 : Blo 928581 2354933 := bbase (se 5 (by rfl) ⟨110387, by rfl⟩ : syracuseStep 2354933 = 220775) (by norm_num)
theorem B2092805 : Blo 928581 2092805 := bbase (se 4 (by rfl) ⟨196200, by rfl⟩ : syracuseStep 2092805 = 392401) (by norm_num)
theorem B1175305 : Blo 928581 1175305 := bbase (se 2 (by rfl) ⟨440739, by rfl⟩ : syracuseStep 1175305 = 881479) (by norm_num)
theorem B1208137 : Blo 928581 1208137 := bbase (se 2 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 1208137 = 906103) (by norm_num)
theorem B2092877 : Blo 928581 2092877 := bbase (se 3 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 2092877 = 784829) (by norm_num)
theorem B7958357 : Blo 928581 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B1568605 : Blo 928581 1568605 := bbase (se 3 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 1568605 = 588227) (by norm_num)
theorem B1175401 : Blo 928581 1175401 := bbase (se 2 (by rfl) ⟨440775, by rfl⟩ : syracuseStep 1175401 = 881551) (by norm_num)
theorem B1077121 : Blo 928581 1077121 := bbase (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) (by norm_num)
theorem B2977669 : Blo 928581 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B2092949 : Blo 928581 2092949 := bbase (se 6 (by rfl) ⟨49053, by rfl⟩ : syracuseStep 2092949 = 98107) (by norm_num)
theorem B2387885 : Blo 928581 2387885 := bbase (se 3 (by rfl) ⟨447728, by rfl⟩ : syracuseStep 2387885 = 895457) (by norm_num)
theorem B1568693 : Blo 928581 1568693 := bbase (se 5 (by rfl) ⟨73532, by rfl⟩ : syracuseStep 1568693 = 147065) (by norm_num)
theorem B3141557 : Blo 928581 3141557 := bbase (se 5 (by rfl) ⟨147260, by rfl⟩ : syracuseStep 3141557 = 294521) (by norm_num)
theorem B2093021 : Blo 928581 2093021 := bbase (se 3 (by rfl) ⟨392441, by rfl⟩ : syracuseStep 2093021 = 784883) (by norm_num)
theorem B1175573 : Blo 928581 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B2093093 : Blo 928581 2093093 := bbase (se 4 (by rfl) ⟨196227, by rfl⟩ : syracuseStep 2093093 = 392455) (by norm_num)
theorem B1568821 : Blo 928581 1568821 := bbase (se 5 (by rfl) ⟨73538, by rfl⟩ : syracuseStep 1568821 = 147077) (by norm_num)
theorem B1175629 : Blo 928581 1175629 := bbase (se 3 (by rfl) ⟨220430, by rfl⟩ : syracuseStep 1175629 = 440861) (by norm_num)
theorem B2355277 : Blo 928581 2355277 := bbase (se 3 (by rfl) ⟨441614, by rfl⟩ : syracuseStep 2355277 = 883229) (by norm_num)
theorem B2093165 : Blo 928581 2093165 := bbase (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) (by norm_num)
theorem B1568909 : Blo 928581 1568909 := bbase (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) (by norm_num)
theorem B1175725 : Blo 928581 1175725 := bbase (se 3 (by rfl) ⟨220448, by rfl⟩ : syracuseStep 1175725 = 440897) (by norm_num)
theorem B1044661 : Blo 928581 1044661 := bbase (se 5 (by rfl) ⟨48968, by rfl⟩ : syracuseStep 1044661 = 97937) (by norm_num)
theorem B2093237 : Blo 928581 2093237 := bbase (se 5 (by rfl) ⟨98120, by rfl⟩ : syracuseStep 2093237 = 196241) (by norm_num)
theorem B2355389 : Blo 928581 2355389 := bbase (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) (by norm_num)
theorem B1241285 : Blo 928581 1241285 := bbase (se 4 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 1241285 = 232741) (by norm_num)
theorem B1044697 : Blo 928581 1044697 := bbase (se 2 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 1044697 = 783523) (by norm_num)
theorem B1044733 : Blo 928581 1044733 := bbase (se 3 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 1044733 = 391775) (by norm_num)
theorem B2093309 : Blo 928581 2093309 := bbase (se 3 (by rfl) ⟨392495, by rfl⟩ : syracuseStep 2093309 = 784991) (by norm_num)
theorem B1569037 : Blo 928581 1569037 := bbase (se 3 (by rfl) ⟨294194, by rfl⟩ : syracuseStep 1569037 = 588389) (by norm_num)
theorem B1044769 : Blo 928581 1044769 := bbase (se 2 (by rfl) ⟨391788, by rfl⟩ : syracuseStep 1044769 = 783577) (by norm_num)
theorem B1044805 : Blo 928581 1044805 := bbase (se 4 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 1044805 = 195901) (by norm_num)
theorem B2093381 : Blo 928581 2093381 := bbase (se 4 (by rfl) ⟨196254, by rfl⟩ : syracuseStep 2093381 = 392509) (by norm_num)
theorem B1175897 : Blo 928581 1175897 := bbase (se 2 (by rfl) ⟨440961, by rfl⟩ : syracuseStep 1175897 = 881923) (by norm_num)
theorem B1569125 : Blo 928581 1569125 := bbase (se 4 (by rfl) ⟨147105, by rfl⟩ : syracuseStep 1569125 = 294211) (by norm_num)
theorem B3141989 : Blo 928581 3141989 := bbase (se 4 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 3141989 = 589123) (by norm_num)
theorem B1044841 : Blo 928581 1044841 := bbase (se 2 (by rfl) ⟨391815, by rfl⟩ : syracuseStep 1044841 = 783631) (by norm_num)
theorem B2355581 : Blo 928581 2355581 := bbase (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) (by norm_num)
theorem B1044877 : Blo 928581 1044877 := bbase (se 3 (by rfl) ⟨195914, by rfl⟩ : syracuseStep 1044877 = 391829) (by norm_num)
theorem B2093453 : Blo 928581 2093453 := bbase (se 3 (by rfl) ⟨392522, by rfl⟩ : syracuseStep 2093453 = 785045) (by norm_num)
theorem B1175953 : Blo 928581 1175953 := bbase (se 2 (by rfl) ⟨440982, by rfl⟩ : syracuseStep 1175953 = 881965) (by norm_num)
theorem B1044913 : Blo 928581 1044913 := bbase (se 2 (by rfl) ⟨391842, by rfl⟩ : syracuseStep 1044913 = 783685) (by norm_num)
theorem B1765813 : Blo 928581 1765813 := bbase (se 5 (by rfl) ⟨82772, by rfl⟩ : syracuseStep 1765813 = 165545) (by norm_num)
theorem B3535285 : Blo 928581 3535285 := bbase (se 5 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 3535285 = 331433) (by norm_num)
theorem B1044949 : Blo 928581 1044949 := bbase (se 7 (by rfl) ⟨12245, by rfl⟩ : syracuseStep 1044949 = 24491) (by norm_num)
theorem B2093525 : Blo 928581 2093525 := bbase (se 7 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 2093525 = 49067) (by norm_num)
theorem B1569253 : Blo 928581 1569253 := bbase (se 4 (by rfl) ⟨147117, by rfl⟩ : syracuseStep 1569253 = 294235) (by norm_num)
theorem B1176049 : Blo 928581 1176049 := bbase (se 2 (by rfl) ⟨441018, by rfl⟩ : syracuseStep 1176049 = 882037) (by norm_num)
theorem B1044985 : Blo 928581 1044985 := bbase (se 2 (by rfl) ⟨391869, by rfl⟩ : syracuseStep 1044985 = 783739) (by norm_num)
theorem B2126341 : Blo 928581 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B1045021 : Blo 928581 1045021 := bbase (se 3 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 1045021 = 391883) (by norm_num)
theorem B2093597 : Blo 928581 2093597 := bbase (se 3 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 2093597 = 785099) (by norm_num)
theorem B1569341 : Blo 928581 1569341 := bbase (se 3 (by rfl) ⟨294251, by rfl⟩ : syracuseStep 1569341 = 588503) (by norm_num)
theorem B1045057 : Blo 928581 1045057 := bbase (se 2 (by rfl) ⟨391896, by rfl⟩ : syracuseStep 1045057 = 783793) (by norm_num)
theorem B1765957 : Blo 928581 1765957 := bbase (se 4 (by rfl) ⟨165558, by rfl⟩ : syracuseStep 1765957 = 331117) (by norm_num)
theorem B1045093 : Blo 928581 1045093 := bbase (se 4 (by rfl) ⟨97977, by rfl⟩ : syracuseStep 1045093 = 195955) (by norm_num)
theorem B2093669 : Blo 928581 2093669 := bbase (se 4 (by rfl) ⟨196281, by rfl⟩ : syracuseStep 2093669 = 392563) (by norm_num)
theorem B1045129 : Blo 928581 1045129 := bbase (se 2 (by rfl) ⟨391923, by rfl⟩ : syracuseStep 1045129 = 783847) (by norm_num)
theorem B1176221 : Blo 928581 1176221 := bbase (se 3 (by rfl) ⟨220541, by rfl⟩ : syracuseStep 1176221 = 441083) (by norm_num)
theorem B1045165 : Blo 928581 1045165 := bbase (se 3 (by rfl) ⟨195968, by rfl⟩ : syracuseStep 1045165 = 391937) (by norm_num)
theorem B2093741 : Blo 928581 2093741 := bbase (se 3 (by rfl) ⟨392576, by rfl⟩ : syracuseStep 2093741 = 785153) (by norm_num)
theorem B1569469 : Blo 928581 1569469 := bbase (se 3 (by rfl) ⟨294275, by rfl⟩ : syracuseStep 1569469 = 588551) (by norm_num)
theorem B1045201 : Blo 928581 1045201 := bbase (se 2 (by rfl) ⟨391950, by rfl⟩ : syracuseStep 1045201 = 783901) (by norm_num)
theorem B1176277 : Blo 928581 1176277 := bbase (se 7 (by rfl) ⟨13784, by rfl⟩ : syracuseStep 1176277 = 27569) (by norm_num)
theorem B2355925 : Blo 928581 2355925 := bbase (se 7 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 2355925 = 55217) (by norm_num)
theorem B1766117 : Blo 928581 1766117 := bbase (se 4 (by rfl) ⟨165573, by rfl⟩ : syracuseStep 1766117 = 331147) (by norm_num)
theorem B3535589 : Blo 928581 3535589 := bbase (se 4 (by rfl) ⟨331461, by rfl⟩ : syracuseStep 3535589 = 662923) (by norm_num)
theorem B1045237 : Blo 928581 1045237 := bbase (se 5 (by rfl) ⟨48995, by rfl⟩ : syracuseStep 1045237 = 97991) (by norm_num)
theorem B2093813 : Blo 928581 2093813 := bbase (se 5 (by rfl) ⟨98147, by rfl⟩ : syracuseStep 2093813 = 196295) (by norm_num)
theorem B1569557 : Blo 928581 1569557 := bbase (se 6 (by rfl) ⟨36786, by rfl⟩ : syracuseStep 1569557 = 73573) (by norm_num)
theorem B3142421 : Blo 928581 3142421 := bbase (se 6 (by rfl) ⟨73650, by rfl⟩ : syracuseStep 3142421 = 147301) (by norm_num)
theorem B1045273 : Blo 928581 1045273 := bbase (se 2 (by rfl) ⟨391977, by rfl⟩ : syracuseStep 1045273 = 783955) (by norm_num)
theorem B1176373 : Blo 928581 1176373 := bbase (se 5 (by rfl) ⟨55142, by rfl⟩ : syracuseStep 1176373 = 110285) (by norm_num)
theorem B1045309 : Blo 928581 1045309 := bbase (se 3 (by rfl) ⟨195995, by rfl⟩ : syracuseStep 1045309 = 391991) (by norm_num)
theorem B2093885 : Blo 928581 2093885 := bbase (se 3 (by rfl) ⟨392603, by rfl⟩ : syracuseStep 2093885 = 785207) (by norm_num)
theorem B2356037 : Blo 928581 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B4715333 : Blo 928581 4715333 := bbase (se 4 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 4715333 = 884125) (by norm_num)
theorem B5665621 : Blo 928581 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1045345 : Blo 928581 1045345 := bbase (se 2 (by rfl) ⟨392004, by rfl⟩ : syracuseStep 1045345 = 784009) (by norm_num)
theorem B1766261 : Blo 928581 1766261 := bbase (se 5 (by rfl) ⟨82793, by rfl⟩ : syracuseStep 1766261 = 165587) (by norm_num)
theorem B1045381 : Blo 928581 1045381 := bbase (se 4 (by rfl) ⟨98004, by rfl⟩ : syracuseStep 1045381 = 196009) (by norm_num)
theorem B2093957 : Blo 928581 2093957 := bbase (se 4 (by rfl) ⟨196308, by rfl⟩ : syracuseStep 2093957 = 392617) (by norm_num)
theorem B1569685 : Blo 928581 1569685 := bbase (se 6 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 1569685 = 73579) (by norm_num)
theorem B1045417 : Blo 928581 1045417 := bbase (se 2 (by rfl) ⟨392031, by rfl⟩ : syracuseStep 1045417 = 784063) (by norm_num)
theorem B1045453 : Blo 928581 1045453 := bbase (se 3 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 1045453 = 392045) (by norm_num)
theorem B2094029 : Blo 928581 2094029 := bbase (se 3 (by rfl) ⟨392630, by rfl⟩ : syracuseStep 2094029 = 785261) (by norm_num)
theorem B1176545 : Blo 928581 1176545 := bbase (se 2 (by rfl) ⟨441204, by rfl⟩ : syracuseStep 1176545 = 882409) (by norm_num)
theorem B1569773 : Blo 928581 1569773 := bbase (se 3 (by rfl) ⟨294332, by rfl⟩ : syracuseStep 1569773 = 588665) (by norm_num)
theorem B1045489 : Blo 928581 1045489 := bbase (se 2 (by rfl) ⟨392058, by rfl⟩ : syracuseStep 1045489 = 784117) (by norm_num)
theorem B2356229 : Blo 928581 2356229 := bbase (se 4 (by rfl) ⟨220896, by rfl⟩ : syracuseStep 2356229 = 441793) (by norm_num)
theorem B1045525 : Blo 928581 1045525 := bbase (se 6 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 1045525 = 49009) (by norm_num)
theorem B2094101 : Blo 928581 2094101 := bbase (se 6 (by rfl) ⟨49080, by rfl⟩ : syracuseStep 2094101 = 98161) (by norm_num)
theorem B1176601 : Blo 928581 1176601 := bbase (se 2 (by rfl) ⟨441225, by rfl⟩ : syracuseStep 1176601 = 882451) (by norm_num)
theorem B1045561 : Blo 928581 1045561 := bbase (se 2 (by rfl) ⟨392085, by rfl⟩ : syracuseStep 1045561 = 784171) (by norm_num)
theorem B1045597 : Blo 928581 1045597 := bbase (se 3 (by rfl) ⟨196049, by rfl⟩ : syracuseStep 1045597 = 392099) (by norm_num)
theorem B2094173 : Blo 928581 2094173 := bbase (se 3 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 2094173 = 785315) (by norm_num)
theorem B2651237 : Blo 928581 2651237 := bbase (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) (by norm_num)
theorem B1569901 : Blo 928581 1569901 := bbase (se 3 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 1569901 = 588713) (by norm_num)
theorem B1176697 : Blo 928581 1176697 := bbase (se 2 (by rfl) ⟨441261, by rfl⟩ : syracuseStep 1176697 = 882523) (by norm_num)
theorem B1045633 : Blo 928581 1045633 := bbase (se 2 (by rfl) ⟨392112, by rfl⟩ : syracuseStep 1045633 = 784225) (by norm_num)
theorem B1766549 : Blo 928581 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B1045669 : Blo 928581 1045669 := bbase (se 4 (by rfl) ⟨98031, by rfl⟩ : syracuseStep 1045669 = 196063) (by norm_num)
theorem B2094245 : Blo 928581 2094245 := bbase (se 4 (by rfl) ⟨196335, by rfl⟩ : syracuseStep 2094245 = 392671) (by norm_num)
theorem B1569989 : Blo 928581 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B3142853 : Blo 928581 3142853 := bbase (se 4 (by rfl) ⟨294642, by rfl⟩ : syracuseStep 3142853 = 589285) (by norm_num)
theorem B1045705 : Blo 928581 1045705 := bbase (se 2 (by rfl) ⟨392139, by rfl⟩ : syracuseStep 1045705 = 784279) (by norm_num)
theorem B1045741 : Blo 928581 1045741 := bbase (se 3 (by rfl) ⟨196076, by rfl⟩ : syracuseStep 1045741 = 392153) (by norm_num)
theorem B2094317 : Blo 928581 2094317 := bbase (se 3 (by rfl) ⟨392684, by rfl⟩ : syracuseStep 2094317 = 785369) (by norm_num)
theorem B1045777 : Blo 928581 1045777 := bbase (se 2 (by rfl) ⟨392166, by rfl⟩ : syracuseStep 1045777 = 784333) (by norm_num)
theorem B1176869 : Blo 928581 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B1766701 : Blo 928581 1766701 := bbase (se 3 (by rfl) ⟨331256, by rfl⟩ : syracuseStep 1766701 = 662513) (by norm_num)
theorem B1045813 : Blo 928581 1045813 := bbase (se 5 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 1045813 = 98045) (by norm_num)
theorem B2094389 : Blo 928581 2094389 := bbase (se 5 (by rfl) ⟨98174, by rfl⟩ : syracuseStep 2094389 = 196349) (by norm_num)
theorem B1570117 : Blo 928581 1570117 := bbase (se 4 (by rfl) ⟨147198, by rfl⟩ : syracuseStep 1570117 = 294397) (by norm_num)
theorem B1045849 : Blo 928581 1045849 := bbase (se 2 (by rfl) ⟨392193, by rfl⟩ : syracuseStep 1045849 = 784387) (by norm_num)
theorem B1176925 : Blo 928581 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B1275229 : Blo 928581 1275229 := bbase (se 3 (by rfl) ⟨239105, by rfl⟩ : syracuseStep 1275229 = 478211) (by norm_num)
theorem B2356573 : Blo 928581 2356573 := bbase (se 3 (by rfl) ⟨441857, by rfl⟩ : syracuseStep 2356573 = 883715) (by norm_num)
theorem B1045885 : Blo 928581 1045885 := bbase (se 3 (by rfl) ⟨196103, by rfl⟩ : syracuseStep 1045885 = 392207) (by norm_num)
theorem B2094461 : Blo 928581 2094461 := bbase (se 3 (by rfl) ⟨392711, by rfl⟩ : syracuseStep 2094461 = 785423) (by norm_num)
theorem B1570205 : Blo 928581 1570205 := bbase (se 3 (by rfl) ⟨294413, by rfl⟩ : syracuseStep 1570205 = 588827) (by norm_num)
theorem B1045921 : Blo 928581 1045921 := bbase (se 2 (by rfl) ⟨392220, by rfl⟩ : syracuseStep 1045921 = 784441) (by norm_num)
theorem B1177021 : Blo 928581 1177021 := bbase (se 3 (by rfl) ⟨220691, by rfl⟩ : syracuseStep 1177021 = 441383) (by norm_num)
theorem B1045957 : Blo 928581 1045957 := bbase (se 4 (by rfl) ⟨98058, by rfl⟩ : syracuseStep 1045957 = 196117) (by norm_num)
theorem B2094533 : Blo 928581 2094533 := bbase (se 4 (by rfl) ⟨196362, by rfl⟩ : syracuseStep 2094533 = 392725) (by norm_num)
theorem B2356685 : Blo 928581 2356685 := bbase (se 3 (by rfl) ⟨441878, by rfl⟩ : syracuseStep 2356685 = 883757) (by norm_num)
theorem B1045993 : Blo 928581 1045993 := bbase (se 2 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 1045993 = 784495) (by norm_num)
theorem B1046029 : Blo 928581 1046029 := bbase (se 3 (by rfl) ⟨196130, by rfl⟩ : syracuseStep 1046029 = 392261) (by norm_num)
theorem B2094605 : Blo 928581 2094605 := bbase (se 3 (by rfl) ⟨392738, by rfl⟩ : syracuseStep 2094605 = 785477) (by norm_num)
theorem B1570333 : Blo 928581 1570333 := bbase (se 3 (by rfl) ⟨294437, by rfl⟩ : syracuseStep 1570333 = 588875) (by norm_num)
theorem B1046065 : Blo 928581 1046065 := bbase (se 2 (by rfl) ⟨392274, by rfl⟩ : syracuseStep 1046065 = 784549) (by norm_num)
theorem B1046101 : Blo 928581 1046101 := bbase (se 8 (by rfl) ⟨6129, by rfl⟩ : syracuseStep 1046101 = 12259) (by norm_num)
theorem B2979413 : Blo 928581 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B2094677 : Blo 928581 2094677 := bbase (se 8 (by rfl) ⟨12273, by rfl⟩ : syracuseStep 2094677 = 24547) (by norm_num)
theorem B1767005 : Blo 928581 1767005 := bbase (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) (by norm_num)
theorem B1177193 : Blo 928581 1177193 := bbase (se 2 (by rfl) ⟨441447, by rfl⟩ : syracuseStep 1177193 = 882895) (by norm_num)
theorem B1570421 : Blo 928581 1570421 := bbase (se 5 (by rfl) ⟨73613, by rfl⟩ : syracuseStep 1570421 = 147227) (by norm_num)
theorem B3143285 : Blo 928581 3143285 := bbase (se 5 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 3143285 = 294683) (by norm_num)
theorem B1046137 : Blo 928581 1046137 := bbase (se 2 (by rfl) ⟨392301, by rfl⟩ : syracuseStep 1046137 = 784603) (by norm_num)
theorem B2356877 : Blo 928581 2356877 := bbase (se 3 (by rfl) ⟨441914, by rfl⟩ : syracuseStep 2356877 = 883829) (by norm_num)
theorem B1046173 : Blo 928581 1046173 := bbase (se 3 (by rfl) ⟨196157, by rfl⟩ : syracuseStep 1046173 = 392315) (by norm_num)
theorem B2094749 : Blo 928581 2094749 := bbase (se 3 (by rfl) ⟨392765, by rfl⟩ : syracuseStep 2094749 = 785531) (by norm_num)
theorem B1177249 : Blo 928581 1177249 := bbase (se 2 (by rfl) ⟨441468, by rfl⟩ : syracuseStep 1177249 = 882937) (by norm_num)
theorem B2520757 : Blo 928581 2520757 := bbase (se 5 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 2520757 = 236321) (by norm_num)
theorem B1046209 : Blo 928581 1046209 := bbase (se 2 (by rfl) ⟨392328, by rfl⟩ : syracuseStep 1046209 = 784657) (by norm_num)
theorem B1046245 : Blo 928581 1046245 := bbase (se 4 (by rfl) ⟨98085, by rfl⟩ : syracuseStep 1046245 = 196171) (by norm_num)
theorem B2094821 : Blo 928581 2094821 := bbase (se 4 (by rfl) ⟨196389, by rfl⟩ : syracuseStep 2094821 = 392779) (by norm_num)
theorem B1570549 : Blo 928581 1570549 := bbase (se 5 (by rfl) ⟨73619, by rfl⟩ : syracuseStep 1570549 = 147239) (by norm_num)
theorem B1177345 : Blo 928581 1177345 := bbase (se 2 (by rfl) ⟨441504, by rfl⟩ : syracuseStep 1177345 = 883009) (by norm_num)
theorem B1046281 : Blo 928581 1046281 := bbase (se 2 (by rfl) ⟨392355, by rfl⟩ : syracuseStep 1046281 = 784711) (by norm_num)
theorem B2979605 : Blo 928581 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B1046317 : Blo 928581 1046317 := bbase (se 3 (by rfl) ⟨196184, by rfl⟩ : syracuseStep 1046317 = 392369) (by norm_num)
theorem B2094893 : Blo 928581 2094893 := bbase (se 3 (by rfl) ⟨392792, by rfl⟩ : syracuseStep 2094893 = 785585) (by norm_num)
theorem B1570637 : Blo 928581 1570637 := bbase (se 3 (by rfl) ⟨294494, by rfl⟩ : syracuseStep 1570637 = 588989) (by norm_num)
theorem B1046353 : Blo 928581 1046353 := bbase (se 2 (by rfl) ⟨392382, by rfl⟩ : syracuseStep 1046353 = 784765) (by norm_num)
theorem B1046389 : Blo 928581 1046389 := bbase (se 5 (by rfl) ⟨49049, by rfl⟩ : syracuseStep 1046389 = 98099) (by norm_num)
theorem B2094965 : Blo 928581 2094965 := bbase (se 5 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 2094965 = 196403) (by norm_num)
theorem B1046425 : Blo 928581 1046425 := bbase (se 2 (by rfl) ⟨392409, by rfl⟩ : syracuseStep 1046425 = 784819) (by norm_num)
theorem B3766181 : Blo 928581 3766181 := bbase (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) (by norm_num)
theorem B1177517 : Blo 928581 1177517 := bbase (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) (by norm_num)
theorem B1046461 : Blo 928581 1046461 := bbase (se 3 (by rfl) ⟨196211, by rfl⟩ : syracuseStep 1046461 = 392423) (by norm_num)
theorem B2095037 : Blo 928581 2095037 := bbase (se 3 (by rfl) ⟨392819, by rfl⟩ : syracuseStep 2095037 = 785639) (by norm_num)
theorem B1570765 : Blo 928581 1570765 := bbase (se 3 (by rfl) ⟨294518, by rfl⟩ : syracuseStep 1570765 = 589037) (by norm_num)
theorem B1046497 : Blo 928581 1046497 := bbase (se 2 (by rfl) ⟨392436, by rfl⟩ : syracuseStep 1046497 = 784873) (by norm_num)
theorem B1177573 : Blo 928581 1177573 := bbase (se 4 (by rfl) ⟨110397, by rfl⟩ : syracuseStep 1177573 = 220795) (by norm_num)
theorem B2357221 : Blo 928581 2357221 := bbase (se 4 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 2357221 = 441979) (by norm_num)
theorem B1046533 : Blo 928581 1046533 := bbase (se 4 (by rfl) ⟨98112, by rfl⟩ : syracuseStep 1046533 = 196225) (by norm_num)
theorem B2095109 : Blo 928581 2095109 := bbase (se 4 (by rfl) ⟨196416, by rfl⟩ : syracuseStep 2095109 = 392833) (by norm_num)
theorem B1570853 : Blo 928581 1570853 := bbase (se 4 (by rfl) ⟨147267, by rfl⟩ : syracuseStep 1570853 = 294535) (by norm_num)
theorem B3143717 : Blo 928581 3143717 := bbase (se 4 (by rfl) ⟨294723, by rfl⟩ : syracuseStep 3143717 = 589447) (by norm_num)
theorem B1046569 : Blo 928581 1046569 := bbase (se 2 (by rfl) ⟨392463, by rfl⟩ : syracuseStep 1046569 = 784927) (by norm_num)
theorem B1177669 : Blo 928581 1177669 := bbase (se 4 (by rfl) ⟨110406, by rfl⟩ : syracuseStep 1177669 = 220813) (by norm_num)
theorem B1046605 : Blo 928581 1046605 := bbase (se 3 (by rfl) ⟨196238, by rfl⟩ : syracuseStep 1046605 = 392477) (by norm_num)
theorem B2095181 : Blo 928581 2095181 := bbase (se 3 (by rfl) ⟨392846, by rfl⟩ : syracuseStep 2095181 = 785693) (by norm_num)
theorem B2357333 : Blo 928581 2357333 := bbase (se 8 (by rfl) ⟨13812, by rfl⟩ : syracuseStep 2357333 = 27625) (by norm_num)
theorem B4716629 : Blo 928581 4716629 := bbase (se 8 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 4716629 = 55273) (by norm_num)
theorem B1046641 : Blo 928581 1046641 := bbase (se 2 (by rfl) ⟨392490, by rfl⟩ : syracuseStep 1046641 = 784981) (by norm_num)
theorem B1046677 : Blo 928581 1046677 := bbase (se 6 (by rfl) ⟨24531, by rfl⟩ : syracuseStep 1046677 = 49063) (by norm_num)
theorem B2095253 : Blo 928581 2095253 := bbase (se 6 (by rfl) ⟨49107, by rfl⟩ : syracuseStep 2095253 = 98215) (by norm_num)
theorem B1570981 : Blo 928581 1570981 := bbase (se 4 (by rfl) ⟨147279, by rfl⟩ : syracuseStep 1570981 = 294559) (by norm_num)
theorem B1046713 : Blo 928581 1046713 := bbase (se 2 (by rfl) ⟨392517, by rfl⟩ : syracuseStep 1046713 = 785035) (by norm_num)
theorem B1046749 : Blo 928581 1046749 := bbase (se 3 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 1046749 = 392531) (by norm_num)
theorem B2095325 : Blo 928581 2095325 := bbase (se 3 (by rfl) ⟨392873, by rfl⟩ : syracuseStep 2095325 = 785747) (by norm_num)
theorem B1177841 : Blo 928581 1177841 := bbase (se 2 (by rfl) ⟨441690, by rfl⟩ : syracuseStep 1177841 = 883381) (by norm_num)
theorem B1571069 : Blo 928581 1571069 := bbase (se 3 (by rfl) ⟨294575, by rfl⟩ : syracuseStep 1571069 = 589151) (by norm_num)
theorem B1046785 : Blo 928581 1046785 := bbase (se 2 (by rfl) ⟨392544, by rfl⟩ : syracuseStep 1046785 = 785089) (by norm_num)
theorem B2652421 : Blo 928581 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B2357525 : Blo 928581 2357525 := bbase (se 6 (by rfl) ⟨55254, by rfl⟩ : syracuseStep 2357525 = 110509) (by norm_num)
theorem B1046821 : Blo 928581 1046821 := bbase (se 4 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 1046821 = 196279) (by norm_num)
theorem B2095397 : Blo 928581 2095397 := bbase (se 4 (by rfl) ⟨196443, by rfl⟩ : syracuseStep 2095397 = 392887) (by norm_num)
theorem B1177897 : Blo 928581 1177897 := bbase (se 2 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 1177897 = 883423) (by norm_num)
theorem B2390317 : Blo 928581 2390317 := bbase (se 3 (by rfl) ⟨448184, by rfl⟩ : syracuseStep 2390317 = 896369) (by norm_num)
theorem B1046857 : Blo 928581 1046857 := bbase (se 2 (by rfl) ⟨392571, by rfl⟩ : syracuseStep 1046857 = 785143) (by norm_num)
theorem B1767757 : Blo 928581 1767757 := bbase (se 3 (by rfl) ⟨331454, by rfl⟩ : syracuseStep 1767757 = 662909) (by norm_num)
theorem B1046893 : Blo 928581 1046893 := bbase (se 3 (by rfl) ⟨196292, by rfl⟩ : syracuseStep 1046893 = 392585) (by norm_num)
theorem B2095469 : Blo 928581 2095469 := bbase (se 3 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 2095469 = 785801) (by norm_num)
theorem B1571197 : Blo 928581 1571197 := bbase (se 3 (by rfl) ⟨294599, by rfl⟩ : syracuseStep 1571197 = 589199) (by norm_num)
theorem B1177993 : Blo 928581 1177993 := bbase (se 2 (by rfl) ⟨441747, by rfl⟩ : syracuseStep 1177993 = 883495) (by norm_num)
theorem B1046929 : Blo 928581 1046929 := bbase (se 2 (by rfl) ⟨392598, by rfl⟩ : syracuseStep 1046929 = 785197) (by norm_num)
theorem B2652581 : Blo 928581 2652581 := bbase (se 4 (by rfl) ⟨248679, by rfl⟩ : syracuseStep 2652581 = 497359) (by norm_num)
theorem B1046965 : Blo 928581 1046965 := bbase (se 5 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 1046965 = 98153) (by norm_num)
theorem B2095541 : Blo 928581 2095541 := bbase (se 5 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 2095541 = 196457) (by norm_num)
theorem B1571285 : Blo 928581 1571285 := bbase (se 7 (by rfl) ⟨18413, by rfl⟩ : syracuseStep 1571285 = 36827) (by norm_num)
theorem B3144149 : Blo 928581 3144149 := bbase (se 7 (by rfl) ⟨36845, by rfl⟩ : syracuseStep 3144149 = 73691) (by norm_num)
theorem B1047001 : Blo 928581 1047001 := bbase (se 2 (by rfl) ⟨392625, by rfl⟩ : syracuseStep 1047001 = 785251) (by norm_num)
theorem B1767901 : Blo 928581 1767901 := bbase (se 3 (by rfl) ⟨331481, by rfl⟩ : syracuseStep 1767901 = 662963) (by norm_num)
theorem B1047037 : Blo 928581 1047037 := bbase (se 3 (by rfl) ⟨196319, by rfl⟩ : syracuseStep 1047037 = 392639) (by norm_num)
theorem B2095613 : Blo 928581 2095613 := bbase (se 3 (by rfl) ⟨392927, by rfl⟩ : syracuseStep 2095613 = 785855) (by norm_num)
theorem B1047073 : Blo 928581 1047073 := bbase (se 2 (by rfl) ⟨392652, by rfl⟩ : syracuseStep 1047073 = 785305) (by norm_num)
theorem B1178165 : Blo 928581 1178165 := bbase (se 5 (by rfl) ⟨55226, by rfl⟩ : syracuseStep 1178165 = 110453) (by norm_num)
theorem B1047109 : Blo 928581 1047109 := bbase (se 4 (by rfl) ⟨98166, by rfl⟩ : syracuseStep 1047109 = 196333) (by norm_num)
theorem B2095685 : Blo 928581 2095685 := bbase (se 4 (by rfl) ⟨196470, by rfl⟩ : syracuseStep 2095685 = 392941) (by norm_num)
theorem B1571413 : Blo 928581 1571413 := bbase (se 8 (by rfl) ⟨9207, by rfl⟩ : syracuseStep 1571413 = 18415) (by norm_num)
theorem B1047145 : Blo 928581 1047145 := bbase (se 2 (by rfl) ⟨392679, by rfl⟩ : syracuseStep 1047145 = 785359) (by norm_num)
theorem B1178221 : Blo 928581 1178221 := bbase (se 3 (by rfl) ⟨220916, by rfl⟩ : syracuseStep 1178221 = 441833) (by norm_num)
theorem B2357869 : Blo 928581 2357869 := bbase (se 3 (by rfl) ⟨442100, by rfl⟩ : syracuseStep 2357869 = 884201) (by norm_num)
theorem B1768061 : Blo 928581 1768061 := bbase (se 3 (by rfl) ⟨331511, by rfl⟩ : syracuseStep 1768061 = 663023) (by norm_num)
theorem B1047181 : Blo 928581 1047181 := bbase (se 3 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 1047181 = 392693) (by norm_num)
theorem B2095757 : Blo 928581 2095757 := bbase (se 3 (by rfl) ⟨392954, by rfl⟩ : syracuseStep 2095757 = 785909) (by norm_num)
theorem B2652821 : Blo 928581 2652821 := bbase (se 6 (by rfl) ⟨62175, by rfl⟩ : syracuseStep 2652821 = 124351) (by norm_num)
theorem B5307029 : Blo 928581 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B1571501 : Blo 928581 1571501 := bbase (se 3 (by rfl) ⟨294656, by rfl⟩ : syracuseStep 1571501 = 589313) (by norm_num)
theorem B1047217 : Blo 928581 1047217 := bbase (se 2 (by rfl) ⟨392706, by rfl⟩ : syracuseStep 1047217 = 785413) (by norm_num)
theorem B1178317 : Blo 928581 1178317 := bbase (se 3 (by rfl) ⟨220934, by rfl⟩ : syracuseStep 1178317 = 441869) (by norm_num)
theorem B1047253 : Blo 928581 1047253 := bbase (se 7 (by rfl) ⟨12272, by rfl⟩ : syracuseStep 1047253 = 24545) (by norm_num)
theorem B2095829 : Blo 928581 2095829 := bbase (se 7 (by rfl) ⟨24560, by rfl⟩ : syracuseStep 2095829 = 49121) (by norm_num)
theorem B2357981 : Blo 928581 2357981 := bbase (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) (by norm_num)
theorem B1047289 : Blo 928581 1047289 := bbase (se 2 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 1047289 = 785467) (by norm_num)
theorem B1768205 : Blo 928581 1768205 := bbase (se 3 (by rfl) ⟨331538, by rfl⟩ : syracuseStep 1768205 = 663077) (by norm_num)
theorem B4193045 : Blo 928581 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B1047325 : Blo 928581 1047325 := bbase (se 3 (by rfl) ⟨196373, by rfl⟩ : syracuseStep 1047325 = 392747) (by norm_num)
theorem B2095901 : Blo 928581 2095901 := bbase (se 3 (by rfl) ⟨392981, by rfl⟩ : syracuseStep 2095901 = 785963) (by norm_num)
theorem B3537701 : Blo 928581 3537701 := bbase (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) (by norm_num)
theorem B1571629 : Blo 928581 1571629 := bbase (se 3 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 1571629 = 589361) (by norm_num)
theorem B3767093 : Blo 928581 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B1047361 : Blo 928581 1047361 := bbase (se 2 (by rfl) ⟨392760, by rfl⟩ : syracuseStep 1047361 = 785521) (by norm_num)
theorem B2653013 : Blo 928581 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B1047397 : Blo 928581 1047397 := bbase (se 4 (by rfl) ⟨98193, by rfl⟩ : syracuseStep 1047397 = 196387) (by norm_num)
theorem B2095973 : Blo 928581 2095973 := bbase (se 4 (by rfl) ⟨196497, by rfl⟩ : syracuseStep 2095973 = 392995) (by norm_num)
theorem B1178489 : Blo 928581 1178489 := bbase (se 2 (by rfl) ⟨441933, by rfl⟩ : syracuseStep 1178489 = 883867) (by norm_num)
theorem B1571717 : Blo 928581 1571717 := bbase (se 4 (by rfl) ⟨147348, by rfl⟩ : syracuseStep 1571717 = 294697) (by norm_num)
theorem B3144581 : Blo 928581 3144581 := bbase (se 4 (by rfl) ⟨294804, by rfl⟩ : syracuseStep 3144581 = 589609) (by norm_num)
theorem B1047433 : Blo 928581 1047433 := bbase (se 2 (by rfl) ⟨392787, by rfl⟩ : syracuseStep 1047433 = 785575) (by norm_num)
theorem B2358173 : Blo 928581 2358173 := bbase (se 3 (by rfl) ⟨442157, by rfl⟩ : syracuseStep 2358173 = 884315) (by norm_num)
theorem B1047469 : Blo 928581 1047469 := bbase (se 3 (by rfl) ⟨196400, by rfl⟩ : syracuseStep 1047469 = 392801) (by norm_num)
theorem B2096045 : Blo 928581 2096045 := bbase (se 3 (by rfl) ⟨393008, by rfl⟩ : syracuseStep 2096045 = 786017) (by norm_num)
theorem B1178545 : Blo 928581 1178545 := bbase (se 2 (by rfl) ⟨441954, by rfl⟩ : syracuseStep 1178545 = 883909) (by norm_num)
theorem B1047505 : Blo 928581 1047505 := bbase (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) (by norm_num)
theorem B1047541 : Blo 928581 1047541 := bbase (se 5 (by rfl) ⟨49103, by rfl⟩ : syracuseStep 1047541 = 98207) (by norm_num)
theorem B2096117 : Blo 928581 2096117 := bbase (se 5 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 2096117 = 196511) (by norm_num)
theorem B1571845 : Blo 928581 1571845 := bbase (se 4 (by rfl) ⟨147360, by rfl⟩ : syracuseStep 1571845 = 294721) (by norm_num)
theorem B1178641 : Blo 928581 1178641 := bbase (se 2 (by rfl) ⟨441990, by rfl⟩ : syracuseStep 1178641 = 883981) (by norm_num)
theorem B1047577 : Blo 928581 1047577 := bbase (se 2 (by rfl) ⟨392841, by rfl⟩ : syracuseStep 1047577 = 785683) (by norm_num)
theorem B1768493 : Blo 928581 1768493 := bbase (se 3 (by rfl) ⟨331592, by rfl⟩ : syracuseStep 1768493 = 663185) (by norm_num)
theorem B1047613 : Blo 928581 1047613 := bbase (se 3 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 1047613 = 392855) (by norm_num)
theorem B2096189 : Blo 928581 2096189 := bbase (se 3 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 2096189 = 786071) (by norm_num)
theorem B3537989 : Blo 928581 3537989 := bbase (se 4 (by rfl) ⟨331686, by rfl⟩ : syracuseStep 3537989 = 663373) (by norm_num)
theorem B1571933 : Blo 928581 1571933 := bbase (se 3 (by rfl) ⟨294737, by rfl⟩ : syracuseStep 1571933 = 589475) (by norm_num)
theorem B1047649 : Blo 928581 1047649 := bbase (se 2 (by rfl) ⟨392868, by rfl⟩ : syracuseStep 1047649 = 785737) (by norm_num)
theorem B1047685 : Blo 928581 1047685 := bbase (se 4 (by rfl) ⟨98220, by rfl⟩ : syracuseStep 1047685 = 196441) (by norm_num)
theorem B2096261 : Blo 928581 2096261 := bbase (se 4 (by rfl) ⟨196524, by rfl⟩ : syracuseStep 2096261 = 393049) (by norm_num)
theorem B1047721 : Blo 928581 1047721 := bbase (se 2 (by rfl) ⟨392895, by rfl⟩ : syracuseStep 1047721 = 785791) (by norm_num)
theorem B1178813 : Blo 928581 1178813 := bbase (se 3 (by rfl) ⟨221027, by rfl⟩ : syracuseStep 1178813 = 442055) (by norm_num)
theorem B1768645 : Blo 928581 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B1047757 : Blo 928581 1047757 := bbase (se 3 (by rfl) ⟨196454, by rfl⟩ : syracuseStep 1047757 = 392909) (by norm_num)
theorem B2096333 : Blo 928581 2096333 := bbase (se 3 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 2096333 = 786125) (by norm_num)
theorem B1572061 : Blo 928581 1572061 := bbase (se 3 (by rfl) ⟨294761, by rfl⟩ : syracuseStep 1572061 = 589523) (by norm_num)
theorem B1047793 : Blo 928581 1047793 := bbase (se 2 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 1047793 = 785845) (by norm_num)
theorem B1178869 : Blo 928581 1178869 := bbase (se 5 (by rfl) ⟨55259, by rfl⟩ : syracuseStep 1178869 = 110519) (by norm_num)
theorem B2358517 : Blo 928581 2358517 := bbase (se 5 (by rfl) ⟨110555, by rfl⟩ : syracuseStep 2358517 = 221111) (by norm_num)
theorem B1047829 : Blo 928581 1047829 := bbase (se 6 (by rfl) ⟨24558, by rfl⟩ : syracuseStep 1047829 = 49117) (by norm_num)
theorem B2096405 : Blo 928581 2096405 := bbase (se 6 (by rfl) ⟨49134, by rfl⟩ : syracuseStep 2096405 = 98269) (by norm_num)
theorem B2424109 : Blo 928581 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B1572149 : Blo 928581 1572149 := bbase (se 5 (by rfl) ⟨73694, by rfl⟩ : syracuseStep 1572149 = 147389) (by norm_num)
theorem B3145013 : Blo 928581 3145013 := bbase (se 5 (by rfl) ⟨147422, by rfl⟩ : syracuseStep 3145013 = 294845) (by norm_num)
theorem B1047865 : Blo 928581 1047865 := bbase (se 2 (by rfl) ⟨392949, by rfl⟩ : syracuseStep 1047865 = 785899) (by norm_num)
theorem B1178965 : Blo 928581 1178965 := bbase (se 11 (by rfl) ⟨863, by rfl⟩ : syracuseStep 1178965 = 1727) (by norm_num)
theorem B1047901 : Blo 928581 1047901 := bbase (se 3 (by rfl) ⟨196481, by rfl⟩ : syracuseStep 1047901 = 392963) (by norm_num)
theorem B2096477 : Blo 928581 2096477 := bbase (se 3 (by rfl) ⟨393089, by rfl⟩ : syracuseStep 2096477 = 786179) (by norm_num)
theorem B2358629 : Blo 928581 2358629 := bbase (se 4 (by rfl) ⟨221121, by rfl⟩ : syracuseStep 2358629 = 442243) (by norm_num)
theorem B4717925 : Blo 928581 4717925 := bbase (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) (by norm_num)
theorem B1047937 : Blo 928581 1047937 := bbase (se 2 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 1047937 = 785953) (by norm_num)
theorem B1047973 : Blo 928581 1047973 := bbase (se 4 (by rfl) ⟨98247, by rfl⟩ : syracuseStep 1047973 = 196495) (by norm_num)
theorem B2096549 : Blo 928581 2096549 := bbase (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) (by norm_num)
theorem B1572277 : Blo 928581 1572277 := bbase (se 5 (by rfl) ⟨73700, by rfl⟩ : syracuseStep 1572277 = 147401) (by norm_num)
theorem B1048009 : Blo 928581 1048009 := bbase (se 2 (by rfl) ⟨393003, by rfl⟩ : syracuseStep 1048009 = 786007) (by norm_num)
theorem B1048045 : Blo 928581 1048045 := bbase (se 3 (by rfl) ⟨196508, by rfl⟩ : syracuseStep 1048045 = 393017) (by norm_num)
theorem B2096621 : Blo 928581 2096621 := bbase (se 3 (by rfl) ⟨393116, by rfl⟩ : syracuseStep 2096621 = 786233) (by norm_num)
theorem B1703405 : Blo 928581 1703405 := bbase (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) (by norm_num)
theorem B1768949 : Blo 928581 1768949 := bbase (se 5 (by rfl) ⟨82919, by rfl⟩ : syracuseStep 1768949 = 165839) (by norm_num)
theorem B1179137 : Blo 928581 1179137 := bbase (se 2 (by rfl) ⟨442176, by rfl⟩ : syracuseStep 1179137 = 884353) (by norm_num)
theorem B1572365 : Blo 928581 1572365 := bbase (se 3 (by rfl) ⟨294818, by rfl⟩ : syracuseStep 1572365 = 589637) (by norm_num)
theorem B1048081 : Blo 928581 1048081 := bbase (se 2 (by rfl) ⟨393030, by rfl⟩ : syracuseStep 1048081 = 786061) (by norm_num)
theorem B2358821 : Blo 928581 2358821 := bbase (se 4 (by rfl) ⟨221139, by rfl⟩ : syracuseStep 2358821 = 442279) (by norm_num)
theorem B1048117 : Blo 928581 1048117 := bbase (se 5 (by rfl) ⟨49130, by rfl⟩ : syracuseStep 1048117 = 98261) (by norm_num)
theorem B2096693 : Blo 928581 2096693 := bbase (se 5 (by rfl) ⟨98282, by rfl⟩ : syracuseStep 2096693 = 196565) (by norm_num)
theorem B1179193 : Blo 928581 1179193 := bbase (se 2 (by rfl) ⟨442197, by rfl⟩ : syracuseStep 1179193 = 884395) (by norm_num)
theorem B1048153 : Blo 928581 1048153 := bbase (se 2 (by rfl) ⟨393057, by rfl⟩ : syracuseStep 1048153 = 786115) (by norm_num)
theorem B1638005 : Blo 928581 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B1048189 : Blo 928581 1048189 := bbase (se 3 (by rfl) ⟨196535, by rfl⟩ : syracuseStep 1048189 = 393071) (by norm_num)
theorem B2096765 : Blo 928581 2096765 := bbase (se 3 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 2096765 = 786287) (by norm_num)
theorem B1572493 : Blo 928581 1572493 := bbase (se 3 (by rfl) ⟨294842, by rfl⟩ : syracuseStep 1572493 = 589685) (by norm_num)
theorem B1179289 : Blo 928581 1179289 := bbase (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) (by norm_num)
theorem B1048225 : Blo 928581 1048225 := bbase (se 2 (by rfl) ⟨393084, by rfl⟩ : syracuseStep 1048225 = 786169) (by norm_num)
theorem B1048261 : Blo 928581 1048261 := bbase (se 4 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 1048261 = 196549) (by norm_num)
theorem B2096837 : Blo 928581 2096837 := bbase (se 4 (by rfl) ⟨196578, by rfl⟩ : syracuseStep 2096837 = 393157) (by norm_num)
theorem B1572581 : Blo 928581 1572581 := bbase (se 4 (by rfl) ⟨147429, by rfl⟩ : syracuseStep 1572581 = 294859) (by norm_num)
theorem B3145445 : Blo 928581 3145445 := bbase (se 4 (by rfl) ⟨294885, by rfl⟩ : syracuseStep 3145445 = 589771) (by norm_num)
theorem B1048297 : Blo 928581 1048297 := bbase (se 2 (by rfl) ⟨393111, by rfl⟩ : syracuseStep 1048297 = 786223) (by norm_num)
theorem B1048333 : Blo 928581 1048333 := bbase (se 3 (by rfl) ⟨196562, by rfl⟩ : syracuseStep 1048333 = 393125) (by norm_num)
theorem B2096909 : Blo 928581 2096909 := bbase (se 3 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 2096909 = 786341) (by norm_num)
theorem B1048369 : Blo 928581 1048369 := bbase (se 2 (by rfl) ⟨393138, by rfl⟩ : syracuseStep 1048369 = 786277) (by norm_num)
theorem B2654005 : Blo 928581 2654005 := bbase (se 5 (by rfl) ⟨124406, by rfl⟩ : syracuseStep 2654005 = 248813) (by norm_num)
theorem B5308213 : Blo 928581 5308213 := bbase (se 5 (by rfl) ⟨248822, by rfl⟩ : syracuseStep 5308213 = 497645) (by norm_num)
theorem B1179461 : Blo 928581 1179461 := bbase (se 4 (by rfl) ⟨110574, by rfl⟩ : syracuseStep 1179461 = 221149) (by norm_num)
theorem B1048405 : Blo 928581 1048405 := bbase (se 9 (by rfl) ⟨3071, by rfl⟩ : syracuseStep 1048405 = 6143) (by norm_num)
theorem B2096981 : Blo 928581 2096981 := bbase (se 9 (by rfl) ⟨6143, by rfl⟩ : syracuseStep 2096981 = 12287) (by norm_num)
theorem B1572709 : Blo 928581 1572709 := bbase (se 4 (by rfl) ⟨147441, by rfl⟩ : syracuseStep 1572709 = 294883) (by norm_num)
theorem B1048441 : Blo 928581 1048441 := bbase (se 2 (by rfl) ⟨393165, by rfl⟩ : syracuseStep 1048441 = 786331) (by norm_num)
theorem B1179517 : Blo 928581 1179517 := bbase (se 3 (by rfl) ⟨221159, by rfl⟩ : syracuseStep 1179517 = 442319) (by norm_num)
theorem B2359165 : Blo 928581 2359165 := bbase (se 3 (by rfl) ⟨442343, by rfl⟩ : syracuseStep 2359165 = 884687) (by norm_num)
theorem B19136405 : Blo 928581 19136405 := bbase (se 6 (by rfl) ⟨448509, by rfl⟩ : syracuseStep 19136405 = 897019) (by norm_num)
theorem B1048477 : Blo 928581 1048477 := bbase (se 3 (by rfl) ⟨196589, by rfl⟩ : syracuseStep 1048477 = 393179) (by norm_num)
theorem B2097053 : Blo 928581 2097053 := bbase (se 3 (by rfl) ⟨393197, by rfl⟩ : syracuseStep 2097053 = 786395) (by norm_num)
theorem B1343405 : Blo 928581 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B1572797 : Blo 928581 1572797 := bbase (se 3 (by rfl) ⟨294899, by rfl⟩ : syracuseStep 1572797 = 589799) (by norm_num)
theorem B1048513 : Blo 928581 1048513 := bbase (se 2 (by rfl) ⟨393192, by rfl⟩ : syracuseStep 1048513 = 786385) (by norm_num)
theorem B1179613 : Blo 928581 1179613 := bbase (se 3 (by rfl) ⟨221177, by rfl⟩ : syracuseStep 1179613 = 442355) (by norm_num)
theorem B1048549 : Blo 928581 1048549 := bbase (se 4 (by rfl) ⟨98301, by rfl⟩ : syracuseStep 1048549 = 196603) (by norm_num)
theorem B2097125 : Blo 928581 2097125 := bbase (se 4 (by rfl) ⟨196605, by rfl⟩ : syracuseStep 2097125 = 393211) (by norm_num)
theorem B2359277 : Blo 928581 2359277 := bbase (se 3 (by rfl) ⟨442364, by rfl⟩ : syracuseStep 2359277 = 884729) (by norm_num)
theorem B2654221 : Blo 928581 2654221 := bstep (se 3 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 2654221 = 995333) B995333
theorem B23298101 : Blo 928581 23298101 := bstep (se 5 (by rfl) ⟨1092098, by rfl⟩ : syracuseStep 23298101 = 2184197) B2184197
theorem B2097233 : Blo 928581 2097233 := bstep (se 2 (by rfl) ⟨786462, by rfl⟩ : syracuseStep 2097233 = 1572925) B1572925
theorem B2097251 : Blo 928581 2097251 := bstep (se 1 (by rfl) ⟨1572938, by rfl⟩ : syracuseStep 2097251 = 3145877) B3145877
theorem B1048675 : Blo 928581 1048675 := bstep (se 1 (by rfl) ⟨786506, by rfl⟩ : syracuseStep 1048675 = 1573013) B1573013
theorem B1572979 : Blo 928581 1572979 := bstep (se 1 (by rfl) ⟨1179734, by rfl⟩ : syracuseStep 1572979 = 2359469) B2359469
theorem B1769617 : Blo 928581 1769617 := bstep (se 2 (by rfl) ⟨663606, by rfl⟩ : syracuseStep 1769617 = 1327213) B1327213
theorem B22610117 : Blo 928581 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B1048819 : Blo 928581 1048819 := bstep (se 1 (by rfl) ⟨786614, by rfl⟩ : syracuseStep 1048819 = 1573229) B1573229
theorem B1573121 : Blo 928581 1573121 := bstep (se 2 (by rfl) ⟨589920, by rfl⟩ : syracuseStep 1573121 = 1179841) B1179841
theorem B4718897 : Blo 928581 4718897 := bstep (se 2 (by rfl) ⟨1769586, by rfl⟩ : syracuseStep 4718897 = 3539173) B3539173
theorem B2359601 : Blo 928581 2359601 := bstep (se 2 (by rfl) ⟨884850, by rfl⟩ : syracuseStep 2359601 = 1769701) B1769701
theorem B5964131 : Blo 928581 5964131 := bstep (se 1 (by rfl) ⟨4473098, by rfl⟩ : syracuseStep 5964131 = 8946197) B8946197
theorem B2359651 : Blo 928581 2359651 := bstep (se 1 (by rfl) ⟨1769738, by rfl⟩ : syracuseStep 2359651 = 3539477) B3539477
theorem B1180003 : Blo 928581 1180003 := bstep (se 1 (by rfl) ⟨885002, by rfl⟩ : syracuseStep 1180003 = 1770005) B1770005
theorem B3146093 : Blo 928581 3146093 := bstep (se 3 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 3146093 = 1179785) B1179785
theorem B2097521 : Blo 928581 2097521 := bstep (se 2 (by rfl) ⟨786570, by rfl⟩ : syracuseStep 2097521 = 1573141) B1573141
theorem B1573249 : Blo 928581 1573249 := bstep (se 2 (by rfl) ⟨589968, by rfl⟩ : syracuseStep 1573249 = 1179937) B1179937
theorem B2097539 : Blo 928581 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B1048963 : Blo 928581 1048963 := bstep (se 1 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 1048963 = 1573445) B1573445
theorem B3146147 : Blo 928581 3146147 := bstep (se 1 (by rfl) ⟨2359610, by rfl⟩ : syracuseStep 3146147 = 4719221) B4719221
theorem B1573283 : Blo 928581 1573283 := bstep (se 1 (by rfl) ⟨1179962, by rfl⟩ : syracuseStep 1573283 = 2359925) B2359925
theorem B2425265 : Blo 928581 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B1180099 : Blo 928581 1180099 := bstep (se 1 (by rfl) ⟨885074, by rfl⟩ : syracuseStep 1180099 = 1770149) B1770149
theorem B2359793 : Blo 928581 2359793 := bstep (se 2 (by rfl) ⟨884922, by rfl⟩ : syracuseStep 2359793 = 1769845) B1769845
theorem B3310093 : Blo 928581 3310093 := bstep (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) B1241285
theorem B1049107 : Blo 928581 1049107 := bstep (se 1 (by rfl) ⟨786830, by rfl⟩ : syracuseStep 1049107 = 1573661) B1573661
theorem B1573411 : Blo 928581 1573411 := bstep (se 1 (by rfl) ⟨1180058, by rfl⟩ : syracuseStep 1573411 = 2360117) B2360117
theorem B2097809 : Blo 928581 2097809 := bstep (se 2 (by rfl) ⟨786678, by rfl⟩ : syracuseStep 2097809 = 1573357) B1573357
theorem B2097827 : Blo 928581 2097827 := bstep (se 1 (by rfl) ⟨1573370, by rfl⟩ : syracuseStep 2097827 = 3146741) B3146741
theorem B3146417 : Blo 928581 3146417 := bstep (se 2 (by rfl) ⟨1179906, by rfl⟩ : syracuseStep 3146417 = 2359813) B2359813
theorem B1573553 : Blo 928581 1573553 := bstep (se 2 (by rfl) ⟨590082, by rfl⟩ : syracuseStep 1573553 = 1180165) B1180165
theorem B1573681 : Blo 928581 1573681 := bstep (se 2 (by rfl) ⟨590130, by rfl⟩ : syracuseStep 1573681 = 1180261) B1180261
theorem B1573715 : Blo 928581 1573715 := bstep (se 1 (by rfl) ⟨1180286, by rfl⟩ : syracuseStep 1573715 = 2360573) B2360573
theorem B2098097 : Blo 928581 2098097 := bstep (se 2 (by rfl) ⟨786786, by rfl⟩ : syracuseStep 2098097 = 1573573) B1573573
theorem B2098115 : Blo 928581 2098115 := bstep (se 1 (by rfl) ⟨1573586, by rfl⟩ : syracuseStep 2098115 = 3147173) B3147173
theorem B5309489 : Blo 928581 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B2655281 : Blo 928581 2655281 := bstep (se 2 (by rfl) ⟨995730, by rfl⟩ : syracuseStep 2655281 = 1991461) B1991461
theorem B6358115 : Blo 928581 6358115 := bstep (se 1 (by rfl) ⟨4768586, by rfl⟩ : syracuseStep 6358115 = 9537173) B9537173
theorem B3540131 : Blo 928581 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B3540145 : Blo 928581 3540145 := bstep (se 2 (by rfl) ⟨1327554, by rfl⟩ : syracuseStep 3540145 = 2655109) B2655109
theorem B3146957 : Blo 928581 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B3147011 : Blo 928581 3147011 := bstep (se 1 (by rfl) ⟨2360258, by rfl⟩ : syracuseStep 3147011 = 4720517) B4720517
theorem B3147281 : Blo 928581 3147281 := bstep (se 2 (by rfl) ⟨1180230, by rfl⟩ : syracuseStep 3147281 = 2360461) B2360461
theorem B12748357 : Blo 928581 12748357 := bstep (se 4 (by rfl) ⟨1195158, by rfl⟩ : syracuseStep 12748357 = 2390317) B2390317
theorem B4720355 : Blo 928581 4720355 := bstep (se 1 (by rfl) ⟨3540266, by rfl⟩ : syracuseStep 4720355 = 7080533) B7080533
theorem B3180305 : Blo 928581 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B2983949 : Blo 928581 2983949 := bstep (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) B1118981
theorem B1509715 : Blo 928581 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B2754929 : Blo 928581 2754929 := bstep (se 2 (by rfl) ⟨1033098, by rfl⟩ : syracuseStep 2754929 = 2066197) B2066197
theorem B5966257 : Blo 928581 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B5310947 : Blo 928581 5310947 := bstep (se 1 (by rfl) ⟨3983210, by rfl⟩ : syracuseStep 5310947 = 7966421) B7966421
theorem B4721165 : Blo 928581 4721165 := bstep (se 3 (by rfl) ⟨885218, by rfl⟩ : syracuseStep 4721165 = 1770437) B1770437
theorem B1673873 : Blo 928581 1673873 := bstep (se 2 (by rfl) ⟨627702, by rfl⟩ : syracuseStep 1673873 = 1255405) B1255405
theorem B11340485 : Blo 928581 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B2755313 : Blo 928581 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2984845 : Blo 928581 2984845 := bstep (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) B1119317
theorem B45321443 : Blo 928581 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B9080419 : Blo 928581 9080419 := bstep (se 1 (by rfl) ⟨6810314, by rfl⟩ : syracuseStep 9080419 = 13620629) B13620629
theorem B2985923 : Blo 928581 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B6033379 : Blo 928581 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B3968995 : Blo 928581 3968995 := bstep (se 1 (by rfl) ⟨2976746, by rfl⟩ : syracuseStep 3968995 = 5953493) B5953493
theorem B18157709 : Blo 928581 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B3183149 : Blo 928581 3183149 := bstep (se 3 (by rfl) ⟨596840, by rfl⟩ : syracuseStep 3183149 = 1193681) B1193681
theorem B2986577 : Blo 928581 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B5739121 : Blo 928581 5739121 := bstep (se 2 (by rfl) ⟨2152170, by rfl⟩ : syracuseStep 5739121 = 4304341) B4304341
theorem B3576611 : Blo 928581 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B1676323 : Blo 928581 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B1610849 : Blo 928581 1610849 := bstep (se 2 (by rfl) ⟨604068, by rfl⟩ : syracuseStep 1610849 = 1208137) B1208137
theorem B3970225 : Blo 928581 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B1676497 : Blo 928581 1676497 := bstep (se 2 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 1676497 = 1257373) B1257373
theorem B10589453 : Blo 928581 10589453 := bstep (se 3 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 10589453 = 3971045) B3971045
theorem B10065293 : Blo 928581 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B8951309 : Blo 928581 8951309 := bstep (se 3 (by rfl) ⟨1678370, by rfl⟩ : syracuseStep 8951309 = 3356741) B3356741
theorem B12719729 : Blo 928581 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B1414787 : Blo 928581 1414787 := bstep (se 1 (by rfl) ⟨1061090, by rfl⟩ : syracuseStep 1414787 = 2122181) B2122181
theorem B1414849 : Blo 928581 1414849 := bstep (se 2 (by rfl) ⟨530568, by rfl⟩ : syracuseStep 1414849 = 1061137) B1061137
theorem B2234243 : Blo 928581 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B4135373 : Blo 928581 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B13408739 : Blo 928581 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B1514099 : Blo 928581 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B2825027 : Blo 928581 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B2825293 : Blo 928581 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B3349937 : Blo 928581 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B5971589 : Blo 928581 5971589 := bstep (se 4 (by rfl) ⟨559836, by rfl⟩ : syracuseStep 5971589 = 1119673) B1119673
theorem B10198669 : Blo 928581 10198669 := bstep (se 3 (by rfl) ⟨1912250, by rfl⟩ : syracuseStep 10198669 = 3824501) B3824501
theorem B2826353 : Blo 928581 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B10592369 : Blo 928581 10592369 := bstep (se 2 (by rfl) ⟨3972138, by rfl⟩ : syracuseStep 10592369 = 7944277) B7944277
theorem B6037681 : Blo 928581 6037681 := bstep (se 2 (by rfl) ⟨2264130, by rfl⟩ : syracuseStep 6037681 = 4528261) B4528261
theorem B11936099 : Blo 928581 11936099 := bstep (se 1 (by rfl) ⟨8952074, by rfl⟩ : syracuseStep 11936099 = 17904149) B17904149
theorem B1417585 : Blo 928581 1417585 := bstep (se 2 (by rfl) ⟨531594, by rfl⟩ : syracuseStep 1417585 = 1063189) B1063189
theorem B991651 : Blo 928581 991651 := bstep (se 1 (by rfl) ⟨743738, by rfl⟩ : syracuseStep 991651 = 1487477) B1487477
theorem B1451009 : Blo 928581 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B17409077 : Blo 928581 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B2237635 : Blo 928581 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B992531 : Blo 928581 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B992659 : Blo 928581 992659 := bstep (se 1 (by rfl) ⟨744494, by rfl⟩ : syracuseStep 992659 = 1488989) B1488989
theorem B3974669 : Blo 928581 3974669 := bstep (se 3 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 3974669 = 1490501) B1490501
theorem B4368013 : Blo 928581 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B2795363 : Blo 928581 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B993475 : Blo 928581 993475 := bstep (se 1 (by rfl) ⟨745106, by rfl⟩ : syracuseStep 993475 = 1490213) B1490213
theorem B6367693 : Blo 928581 6367693 := bstep (se 3 (by rfl) ⟨1193942, by rfl⟩ : syracuseStep 6367693 = 2387885) B2387885
theorem B3582413 : Blo 928581 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B12757603 : Blo 928581 12757603 := bstep (se 1 (by rfl) ⟨9568202, by rfl⟩ : syracuseStep 12757603 = 19136405) B19136405
theorem B2239249 : Blo 928581 2239249 := bstep (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) B1679437
theorem B928595 : Blo 928581 928595 := bstep (se 1 (by rfl) ⟨696446, by rfl⟩ : syracuseStep 928595 = 1392893) B1392893
theorem B928611 : Blo 928581 928611 := bstep (se 1 (by rfl) ⟨696458, by rfl⟩ : syracuseStep 928611 = 1392917) B1392917
theorem B928627 : Blo 928581 928627 := bstep (se 1 (by rfl) ⟨696470, by rfl⟩ : syracuseStep 928627 = 1392941) B1392941
theorem B928643 : Blo 928581 928643 := bstep (se 1 (by rfl) ⟨696482, by rfl⟩ : syracuseStep 928643 = 1392965) B1392965
theorem B5024645 : Blo 928581 5024645 := bstep (se 4 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 5024645 = 942121) B942121
theorem B928659 : Blo 928581 928659 := bstep (se 1 (by rfl) ⟨696494, by rfl⟩ : syracuseStep 928659 = 1392989) B1392989
theorem B928675 : Blo 928581 928675 := bstep (se 1 (by rfl) ⟨696506, by rfl⟩ : syracuseStep 928675 = 1393013) B1393013
theorem B928691 : Blo 928581 928691 := bstep (se 1 (by rfl) ⟨696518, by rfl⟩ : syracuseStep 928691 = 1393037) B1393037
theorem B928707 : Blo 928581 928707 := bstep (se 1 (by rfl) ⟨696530, by rfl⟩ : syracuseStep 928707 = 1393061) B1393061
theorem B928723 : Blo 928581 928723 := bstep (se 1 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 928723 = 1393085) B1393085
theorem B928739 : Blo 928581 928739 := bstep (se 1 (by rfl) ⟨696554, by rfl⟩ : syracuseStep 928739 = 1393109) B1393109
theorem B928755 : Blo 928581 928755 := bstep (se 1 (by rfl) ⟨696566, by rfl⟩ : syracuseStep 928755 = 1393133) B1393133
theorem B928771 : Blo 928581 928771 := bstep (se 1 (by rfl) ⟨696578, by rfl⟩ : syracuseStep 928771 = 1393157) B1393157
theorem B928787 : Blo 928581 928787 := bstep (se 1 (by rfl) ⟨696590, by rfl⟩ : syracuseStep 928787 = 1393181) B1393181
theorem B928803 : Blo 928581 928803 := bstep (se 1 (by rfl) ⟨696602, by rfl⟩ : syracuseStep 928803 = 1393205) B1393205
theorem B928819 : Blo 928581 928819 := bstep (se 1 (by rfl) ⟨696614, by rfl⟩ : syracuseStep 928819 = 1393229) B1393229
theorem B928835 : Blo 928581 928835 := bstep (se 1 (by rfl) ⟨696626, by rfl⟩ : syracuseStep 928835 = 1393253) B1393253
theorem B2829379 : Blo 928581 2829379 := bstep (se 1 (by rfl) ⟨2122034, by rfl⟩ : syracuseStep 2829379 = 4244069) B4244069
theorem B928851 : Blo 928581 928851 := bstep (se 1 (by rfl) ⟨696638, by rfl⟩ : syracuseStep 928851 = 1393277) B1393277
theorem B928867 : Blo 928581 928867 := bstep (se 1 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 928867 = 1393301) B1393301
theorem B928883 : Blo 928581 928883 := bstep (se 1 (by rfl) ⟨696662, by rfl⟩ : syracuseStep 928883 = 1393325) B1393325
theorem B928899 : Blo 928581 928899 := bstep (se 1 (by rfl) ⟨696674, by rfl⟩ : syracuseStep 928899 = 1393349) B1393349
theorem B928915 : Blo 928581 928915 := bstep (se 1 (by rfl) ⟨696686, by rfl⟩ : syracuseStep 928915 = 1393373) B1393373
theorem B928931 : Blo 928581 928931 := bstep (se 1 (by rfl) ⟨696698, by rfl⟩ : syracuseStep 928931 = 1393397) B1393397
theorem B928947 : Blo 928581 928947 := bstep (se 1 (by rfl) ⟨696710, by rfl⟩ : syracuseStep 928947 = 1393421) B1393421
theorem B928963 : Blo 928581 928963 := bstep (se 1 (by rfl) ⟨696722, by rfl⟩ : syracuseStep 928963 = 1393445) B1393445
theorem B928979 : Blo 928581 928979 := bstep (se 1 (by rfl) ⟨696734, by rfl⟩ : syracuseStep 928979 = 1393469) B1393469
theorem B928995 : Blo 928581 928995 := bstep (se 1 (by rfl) ⟨696746, by rfl⟩ : syracuseStep 928995 = 1393493) B1393493
theorem B929011 : Blo 928581 929011 := bstep (se 1 (by rfl) ⟨696758, by rfl⟩ : syracuseStep 929011 = 1393517) B1393517
theorem B929027 : Blo 928581 929027 := bstep (se 1 (by rfl) ⟨696770, by rfl⟩ : syracuseStep 929027 = 1393541) B1393541
theorem B929043 : Blo 928581 929043 := bstep (se 1 (by rfl) ⟨696782, by rfl⟩ : syracuseStep 929043 = 1393565) B1393565
theorem B929059 : Blo 928581 929059 := bstep (se 1 (by rfl) ⟨696794, by rfl⟩ : syracuseStep 929059 = 1393589) B1393589
theorem B929075 : Blo 928581 929075 := bstep (se 1 (by rfl) ⟨696806, by rfl⟩ : syracuseStep 929075 = 1393613) B1393613
theorem B929091 : Blo 928581 929091 := bstep (se 1 (by rfl) ⟨696818, by rfl⟩ : syracuseStep 929091 = 1393637) B1393637
theorem B929107 : Blo 928581 929107 := bstep (se 1 (by rfl) ⟨696830, by rfl⟩ : syracuseStep 929107 = 1393661) B1393661
theorem B5647715 : Blo 928581 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B929123 : Blo 928581 929123 := bstep (se 1 (by rfl) ⟨696842, by rfl⟩ : syracuseStep 929123 = 1393685) B1393685
theorem B929139 : Blo 928581 929139 := bstep (se 1 (by rfl) ⟨696854, by rfl⟩ : syracuseStep 929139 = 1393709) B1393709
theorem B929155 : Blo 928581 929155 := bstep (se 1 (by rfl) ⟨696866, by rfl⟩ : syracuseStep 929155 = 1393733) B1393733
theorem B929171 : Blo 928581 929171 := bstep (se 1 (by rfl) ⟨696878, by rfl⟩ : syracuseStep 929171 = 1393757) B1393757
theorem B1322401 : Blo 928581 1322401 := bstep (se 2 (by rfl) ⟨495900, by rfl⟩ : syracuseStep 1322401 = 991801) B991801
theorem B929187 : Blo 928581 929187 := bstep (se 1 (by rfl) ⟨696890, by rfl⟩ : syracuseStep 929187 = 1393781) B1393781
theorem B929203 : Blo 928581 929203 := bstep (se 1 (by rfl) ⟨696902, by rfl⟩ : syracuseStep 929203 = 1393805) B1393805
theorem B1256897 : Blo 928581 1256897 := bstep (se 2 (by rfl) ⟨471336, by rfl⟩ : syracuseStep 1256897 = 942673) B942673
theorem B929219 : Blo 928581 929219 := bstep (se 1 (by rfl) ⟨696914, by rfl⟩ : syracuseStep 929219 = 1393829) B1393829
theorem B3354061 : Blo 928581 3354061 := bstep (se 3 (by rfl) ⟨628886, by rfl⟩ : syracuseStep 3354061 = 1257773) B1257773
theorem B929235 : Blo 928581 929235 := bstep (se 1 (by rfl) ⟨696926, by rfl⟩ : syracuseStep 929235 = 1393853) B1393853
theorem B929251 : Blo 928581 929251 := bstep (se 1 (by rfl) ⟨696938, by rfl⟩ : syracuseStep 929251 = 1393877) B1393877
theorem B929267 : Blo 928581 929267 := bstep (se 1 (by rfl) ⟨696950, by rfl⟩ : syracuseStep 929267 = 1393901) B1393901
theorem B1322497 : Blo 928581 1322497 := bstep (se 2 (by rfl) ⟨495936, by rfl⟩ : syracuseStep 1322497 = 991873) B991873
theorem B929283 : Blo 928581 929283 := bstep (se 1 (by rfl) ⟨696962, by rfl⟩ : syracuseStep 929283 = 1393925) B1393925
theorem B929299 : Blo 928581 929299 := bstep (se 1 (by rfl) ⟨696974, by rfl⟩ : syracuseStep 929299 = 1393949) B1393949
theorem B929315 : Blo 928581 929315 := bstep (se 1 (by rfl) ⟨696986, by rfl⟩ : syracuseStep 929315 = 1393973) B1393973
theorem B929331 : Blo 928581 929331 := bstep (se 1 (by rfl) ⟨696998, by rfl⟩ : syracuseStep 929331 = 1393997) B1393997
theorem B929347 : Blo 928581 929347 := bstep (se 1 (by rfl) ⟨697010, by rfl⟩ : syracuseStep 929347 = 1394021) B1394021
theorem B929363 : Blo 928581 929363 := bstep (se 1 (by rfl) ⟨697022, by rfl⟩ : syracuseStep 929363 = 1394045) B1394045
theorem B929379 : Blo 928581 929379 := bstep (se 1 (by rfl) ⟨697034, by rfl⟩ : syracuseStep 929379 = 1394069) B1394069
theorem B2010737 : Blo 928581 2010737 := bstep (se 2 (by rfl) ⟨754026, by rfl⟩ : syracuseStep 2010737 = 1508053) B1508053
theorem B929395 : Blo 928581 929395 := bstep (se 1 (by rfl) ⟨697046, by rfl⟩ : syracuseStep 929395 = 1394093) B1394093
theorem B929411 : Blo 928581 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B929427 : Blo 928581 929427 := bstep (se 1 (by rfl) ⟨697070, by rfl⟩ : syracuseStep 929427 = 1394141) B1394141
theorem B929443 : Blo 928581 929443 := bstep (se 1 (by rfl) ⟨697082, by rfl⟩ : syracuseStep 929443 = 1394165) B1394165
theorem B929459 : Blo 928581 929459 := bstep (se 1 (by rfl) ⟨697094, by rfl⟩ : syracuseStep 929459 = 1394189) B1394189
theorem B929475 : Blo 928581 929475 := bstep (se 1 (by rfl) ⟨697106, by rfl⟩ : syracuseStep 929475 = 1394213) B1394213
theorem B929491 : Blo 928581 929491 := bstep (se 1 (by rfl) ⟨697118, by rfl⟩ : syracuseStep 929491 = 1394237) B1394237
theorem B929507 : Blo 928581 929507 := bstep (se 1 (by rfl) ⟨697130, by rfl⟩ : syracuseStep 929507 = 1394261) B1394261
theorem B5746403 : Blo 928581 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B929523 : Blo 928581 929523 := bstep (se 1 (by rfl) ⟨697142, by rfl⟩ : syracuseStep 929523 = 1394285) B1394285
theorem B929539 : Blo 928581 929539 := bstep (se 1 (by rfl) ⟨697154, by rfl⟩ : syracuseStep 929539 = 1394309) B1394309
theorem B929555 : Blo 928581 929555 := bstep (se 1 (by rfl) ⟨697166, by rfl⟩ : syracuseStep 929555 = 1394333) B1394333
theorem B929571 : Blo 928581 929571 := bstep (se 1 (by rfl) ⟨697178, by rfl⟩ : syracuseStep 929571 = 1394357) B1394357
theorem B929587 : Blo 928581 929587 := bstep (se 1 (by rfl) ⟨697190, by rfl⟩ : syracuseStep 929587 = 1394381) B1394381
theorem B929603 : Blo 928581 929603 := bstep (se 1 (by rfl) ⟨697202, by rfl⟩ : syracuseStep 929603 = 1394405) B1394405
theorem B929619 : Blo 928581 929619 := bstep (se 1 (by rfl) ⟨697214, by rfl⟩ : syracuseStep 929619 = 1394429) B1394429
theorem B929635 : Blo 928581 929635 := bstep (se 1 (by rfl) ⟨697226, by rfl⟩ : syracuseStep 929635 = 1394453) B1394453
theorem B929651 : Blo 928581 929651 := bstep (se 1 (by rfl) ⟨697238, by rfl⟩ : syracuseStep 929651 = 1394477) B1394477
theorem B929667 : Blo 928581 929667 := bstep (se 1 (by rfl) ⟨697250, by rfl⟩ : syracuseStep 929667 = 1394501) B1394501
theorem B929683 : Blo 928581 929683 := bstep (se 1 (by rfl) ⟨697262, by rfl⟩ : syracuseStep 929683 = 1394525) B1394525
theorem B929699 : Blo 928581 929699 := bstep (se 1 (by rfl) ⟨697274, by rfl⟩ : syracuseStep 929699 = 1394549) B1394549
theorem B929715 : Blo 928581 929715 := bstep (se 1 (by rfl) ⟨697286, by rfl⟩ : syracuseStep 929715 = 1394573) B1394573
theorem B929731 : Blo 928581 929731 := bstep (se 1 (by rfl) ⟨697298, by rfl⟩ : syracuseStep 929731 = 1394597) B1394597
theorem B929747 : Blo 928581 929747 := bstep (se 1 (by rfl) ⟨697310, by rfl⟩ : syracuseStep 929747 = 1394621) B1394621
theorem B929763 : Blo 928581 929763 := bstep (se 1 (by rfl) ⟨697322, by rfl⟩ : syracuseStep 929763 = 1394645) B1394645
theorem B1322993 : Blo 928581 1322993 := bstep (se 2 (by rfl) ⟨496122, by rfl⟩ : syracuseStep 1322993 = 992245) B992245
theorem B929779 : Blo 928581 929779 := bstep (se 1 (by rfl) ⟨697334, by rfl⟩ : syracuseStep 929779 = 1394669) B1394669
theorem B929795 : Blo 928581 929795 := bstep (se 1 (by rfl) ⟨697346, by rfl⟩ : syracuseStep 929795 = 1394693) B1394693
theorem B929811 : Blo 928581 929811 := bstep (se 1 (by rfl) ⟨697358, by rfl⟩ : syracuseStep 929811 = 1394717) B1394717
theorem B929827 : Blo 928581 929827 := bstep (se 1 (by rfl) ⟨697370, by rfl⟩ : syracuseStep 929827 = 1394741) B1394741
theorem B929843 : Blo 928581 929843 := bstep (se 1 (by rfl) ⟨697382, by rfl⟩ : syracuseStep 929843 = 1394765) B1394765
theorem B929859 : Blo 928581 929859 := bstep (se 1 (by rfl) ⟨697394, by rfl⟩ : syracuseStep 929859 = 1394789) B1394789
theorem B929875 : Blo 928581 929875 := bstep (se 1 (by rfl) ⟨697406, by rfl⟩ : syracuseStep 929875 = 1394813) B1394813
theorem B929891 : Blo 928581 929891 := bstep (se 1 (by rfl) ⟨697418, by rfl⟩ : syracuseStep 929891 = 1394837) B1394837
theorem B929907 : Blo 928581 929907 := bstep (se 1 (by rfl) ⟨697430, by rfl⟩ : syracuseStep 929907 = 1394861) B1394861
theorem B929923 : Blo 928581 929923 := bstep (se 1 (by rfl) ⟨697442, by rfl⟩ : syracuseStep 929923 = 1394885) B1394885
theorem B929939 : Blo 928581 929939 := bstep (se 1 (by rfl) ⟨697454, by rfl⟩ : syracuseStep 929939 = 1394909) B1394909
theorem B5091491 : Blo 928581 5091491 := bstep (se 1 (by rfl) ⟨3818618, by rfl⟩ : syracuseStep 5091491 = 7637237) B7637237
theorem B929955 : Blo 928581 929955 := bstep (se 1 (by rfl) ⟨697466, by rfl⟩ : syracuseStep 929955 = 1394933) B1394933
theorem B1913009 : Blo 928581 1913009 := bstep (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) B1434757
theorem B929971 : Blo 928581 929971 := bstep (se 1 (by rfl) ⟨697478, by rfl⟩ : syracuseStep 929971 = 1394957) B1394957
theorem B929987 : Blo 928581 929987 := bstep (se 1 (by rfl) ⟨697490, by rfl⟩ : syracuseStep 929987 = 1394981) B1394981
theorem B930003 : Blo 928581 930003 := bstep (se 1 (by rfl) ⟨697502, by rfl⟩ : syracuseStep 930003 = 1395005) B1395005
theorem B930019 : Blo 928581 930019 := bstep (se 1 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 930019 = 1395029) B1395029
theorem B930035 : Blo 928581 930035 := bstep (se 1 (by rfl) ⟨697526, by rfl⟩ : syracuseStep 930035 = 1395053) B1395053
theorem B930051 : Blo 928581 930051 := bstep (se 1 (by rfl) ⟨697538, by rfl⟩ : syracuseStep 930051 = 1395077) B1395077
theorem B930067 : Blo 928581 930067 := bstep (se 1 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 930067 = 1395101) B1395101
theorem B930083 : Blo 928581 930083 := bstep (se 1 (by rfl) ⟨697562, by rfl⟩ : syracuseStep 930083 = 1395125) B1395125
theorem B930099 : Blo 928581 930099 := bstep (se 1 (by rfl) ⟨697574, by rfl⟩ : syracuseStep 930099 = 1395149) B1395149
theorem B930115 : Blo 928581 930115 := bstep (se 1 (by rfl) ⟨697586, by rfl⟩ : syracuseStep 930115 = 1395173) B1395173
theorem B930131 : Blo 928581 930131 := bstep (se 1 (by rfl) ⟨697598, by rfl⟩ : syracuseStep 930131 = 1395197) B1395197
theorem B930147 : Blo 928581 930147 := bstep (se 1 (by rfl) ⟨697610, by rfl⟩ : syracuseStep 930147 = 1395221) B1395221
theorem B930163 : Blo 928581 930163 := bstep (se 1 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 930163 = 1395245) B1395245
theorem B930179 : Blo 928581 930179 := bstep (se 1 (by rfl) ⟨697634, by rfl⟩ : syracuseStep 930179 = 1395269) B1395269
theorem B930195 : Blo 928581 930195 := bstep (se 1 (by rfl) ⟨697646, by rfl⟩ : syracuseStep 930195 = 1395293) B1395293
theorem B930211 : Blo 928581 930211 := bstep (se 1 (by rfl) ⟨697658, by rfl⟩ : syracuseStep 930211 = 1395317) B1395317
theorem B930227 : Blo 928581 930227 := bstep (se 1 (by rfl) ⟨697670, by rfl⟩ : syracuseStep 930227 = 1395341) B1395341
theorem B930243 : Blo 928581 930243 := bstep (se 1 (by rfl) ⟨697682, by rfl⟩ : syracuseStep 930243 = 1395365) B1395365
theorem B930259 : Blo 928581 930259 := bstep (se 1 (by rfl) ⟨697694, by rfl⟩ : syracuseStep 930259 = 1395389) B1395389
theorem B930275 : Blo 928581 930275 := bstep (se 1 (by rfl) ⟨697706, by rfl⟩ : syracuseStep 930275 = 1395413) B1395413
theorem B930291 : Blo 928581 930291 := bstep (se 1 (by rfl) ⟨697718, by rfl⟩ : syracuseStep 930291 = 1395437) B1395437
theorem B930307 : Blo 928581 930307 := bstep (se 1 (by rfl) ⟨697730, by rfl⟩ : syracuseStep 930307 = 1395461) B1395461
theorem B930323 : Blo 928581 930323 := bstep (se 1 (by rfl) ⟨697742, by rfl⟩ : syracuseStep 930323 = 1395485) B1395485
theorem B930339 : Blo 928581 930339 := bstep (se 1 (by rfl) ⟨697754, by rfl⟩ : syracuseStep 930339 = 1395509) B1395509
theorem B930355 : Blo 928581 930355 := bstep (se 1 (by rfl) ⟨697766, by rfl⟩ : syracuseStep 930355 = 1395533) B1395533
theorem B930371 : Blo 928581 930371 := bstep (se 1 (by rfl) ⟨697778, by rfl⟩ : syracuseStep 930371 = 1395557) B1395557
theorem B930387 : Blo 928581 930387 := bstep (se 1 (by rfl) ⟨697790, by rfl⟩ : syracuseStep 930387 = 1395581) B1395581
theorem B930403 : Blo 928581 930403 := bstep (se 1 (by rfl) ⟨697802, by rfl⟩ : syracuseStep 930403 = 1395605) B1395605
theorem B930419 : Blo 928581 930419 := bstep (se 1 (by rfl) ⟨697814, by rfl⟩ : syracuseStep 930419 = 1395629) B1395629
theorem B930435 : Blo 928581 930435 := bstep (se 1 (by rfl) ⟨697826, by rfl⟩ : syracuseStep 930435 = 1395653) B1395653
theorem B930451 : Blo 928581 930451 := bstep (se 1 (by rfl) ⟨697838, by rfl⟩ : syracuseStep 930451 = 1395677) B1395677
theorem B930467 : Blo 928581 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B930483 : Blo 928581 930483 := bstep (se 1 (by rfl) ⟨697862, by rfl⟩ : syracuseStep 930483 = 1395725) B1395725
theorem B930499 : Blo 928581 930499 := bstep (se 1 (by rfl) ⟨697874, by rfl⟩ : syracuseStep 930499 = 1395749) B1395749
theorem B930515 : Blo 928581 930515 := bstep (se 1 (by rfl) ⟨697886, by rfl⟩ : syracuseStep 930515 = 1395773) B1395773
theorem B930531 : Blo 928581 930531 := bstep (se 1 (by rfl) ⟨697898, by rfl⟩ : syracuseStep 930531 = 1395797) B1395797
theorem B930547 : Blo 928581 930547 := bstep (se 1 (by rfl) ⟨697910, by rfl⟩ : syracuseStep 930547 = 1395821) B1395821
theorem B930563 : Blo 928581 930563 := bstep (se 1 (by rfl) ⟨697922, by rfl⟩ : syracuseStep 930563 = 1395845) B1395845
theorem B930579 : Blo 928581 930579 := bstep (se 1 (by rfl) ⟨697934, by rfl⟩ : syracuseStep 930579 = 1395869) B1395869
theorem B930595 : Blo 928581 930595 := bstep (se 1 (by rfl) ⟨697946, by rfl⟩ : syracuseStep 930595 = 1395893) B1395893
theorem B930611 : Blo 928581 930611 := bstep (se 1 (by rfl) ⟨697958, by rfl⟩ : syracuseStep 930611 = 1395917) B1395917
theorem B930627 : Blo 928581 930627 := bstep (se 1 (by rfl) ⟨697970, by rfl⟩ : syracuseStep 930627 = 1395941) B1395941
theorem B1323859 : Blo 928581 1323859 := bstep (se 1 (by rfl) ⟨992894, by rfl⟩ : syracuseStep 1323859 = 1985789) B1985789
theorem B930643 : Blo 928581 930643 := bstep (se 1 (by rfl) ⟨697982, by rfl⟩ : syracuseStep 930643 = 1395965) B1395965
theorem B930659 : Blo 928581 930659 := bstep (se 1 (by rfl) ⟨697994, by rfl⟩ : syracuseStep 930659 = 1395989) B1395989
theorem B1913699 : Blo 928581 1913699 := bstep (se 1 (by rfl) ⟨1435274, by rfl⟩ : syracuseStep 1913699 = 2870549) B2870549
theorem B930675 : Blo 928581 930675 := bstep (se 1 (by rfl) ⟨698006, by rfl⟩ : syracuseStep 930675 = 1396013) B1396013
theorem B930691 : Blo 928581 930691 := bstep (se 1 (by rfl) ⟨698018, by rfl⟩ : syracuseStep 930691 = 1396037) B1396037
theorem B930707 : Blo 928581 930707 := bstep (se 1 (by rfl) ⟨698030, by rfl⟩ : syracuseStep 930707 = 1396061) B1396061
theorem B930723 : Blo 928581 930723 := bstep (se 1 (by rfl) ⟨698042, by rfl⟩ : syracuseStep 930723 = 1396085) B1396085
theorem B1323955 : Blo 928581 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B930739 : Blo 928581 930739 := bstep (se 1 (by rfl) ⟨698054, by rfl⟩ : syracuseStep 930739 = 1396109) B1396109
theorem B930755 : Blo 928581 930755 := bstep (se 1 (by rfl) ⟨698066, by rfl⟩ : syracuseStep 930755 = 1396133) B1396133
theorem B930771 : Blo 928581 930771 := bstep (se 1 (by rfl) ⟨698078, by rfl⟩ : syracuseStep 930771 = 1396157) B1396157
theorem B1258465 : Blo 928581 1258465 := bstep (se 2 (by rfl) ⟨471924, by rfl⟩ : syracuseStep 1258465 = 943849) B943849
theorem B930787 : Blo 928581 930787 := bstep (se 1 (by rfl) ⟨698090, by rfl⟩ : syracuseStep 930787 = 1396181) B1396181
theorem B930803 : Blo 928581 930803 := bstep (se 1 (by rfl) ⟨698102, by rfl⟩ : syracuseStep 930803 = 1396205) B1396205
theorem B930819 : Blo 928581 930819 := bstep (se 1 (by rfl) ⟨698114, by rfl⟩ : syracuseStep 930819 = 1396229) B1396229
theorem B930835 : Blo 928581 930835 := bstep (se 1 (by rfl) ⟨698126, by rfl⟩ : syracuseStep 930835 = 1396253) B1396253
theorem B930851 : Blo 928581 930851 := bstep (se 1 (by rfl) ⟨698138, by rfl⟩ : syracuseStep 930851 = 1396277) B1396277
theorem B930867 : Blo 928581 930867 := bstep (se 1 (by rfl) ⟨698150, by rfl⟩ : syracuseStep 930867 = 1396301) B1396301
theorem B930883 : Blo 928581 930883 := bstep (se 1 (by rfl) ⟨698162, by rfl⟩ : syracuseStep 930883 = 1396325) B1396325
theorem B6370373 : Blo 928581 6370373 := bstep (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) B1194445
theorem B930899 : Blo 928581 930899 := bstep (se 1 (by rfl) ⟨698174, by rfl⟩ : syracuseStep 930899 = 1396349) B1396349
theorem B930915 : Blo 928581 930915 := bstep (se 1 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 930915 = 1396373) B1396373
theorem B930931 : Blo 928581 930931 := bstep (se 1 (by rfl) ⟨698198, by rfl⟩ : syracuseStep 930931 = 1396397) B1396397
theorem B930947 : Blo 928581 930947 := bstep (se 1 (by rfl) ⟨698210, by rfl⟩ : syracuseStep 930947 = 1396421) B1396421
theorem B930963 : Blo 928581 930963 := bstep (se 1 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 930963 = 1396445) B1396445
theorem B930979 : Blo 928581 930979 := bstep (se 1 (by rfl) ⟨698234, by rfl⟩ : syracuseStep 930979 = 1396469) B1396469
theorem B930995 : Blo 928581 930995 := bstep (se 1 (by rfl) ⟨698246, by rfl⟩ : syracuseStep 930995 = 1396493) B1396493
theorem B931011 : Blo 928581 931011 := bstep (se 1 (by rfl) ⟨698258, by rfl⟩ : syracuseStep 931011 = 1396517) B1396517
theorem B931027 : Blo 928581 931027 := bstep (se 1 (by rfl) ⟨698270, by rfl⟩ : syracuseStep 931027 = 1396541) B1396541
theorem B931043 : Blo 928581 931043 := bstep (se 1 (by rfl) ⟨698282, by rfl⟩ : syracuseStep 931043 = 1396565) B1396565
theorem B931059 : Blo 928581 931059 := bstep (se 1 (by rfl) ⟨698294, by rfl⟩ : syracuseStep 931059 = 1396589) B1396589
theorem B931075 : Blo 928581 931075 := bstep (se 1 (by rfl) ⟨698306, by rfl⟩ : syracuseStep 931075 = 1396613) B1396613
theorem B931091 : Blo 928581 931091 := bstep (se 1 (by rfl) ⟨698318, by rfl⟩ : syracuseStep 931091 = 1396637) B1396637
theorem B931107 : Blo 928581 931107 := bstep (se 1 (by rfl) ⟨698330, by rfl⟩ : syracuseStep 931107 = 1396661) B1396661
theorem B931123 : Blo 928581 931123 := bstep (se 1 (by rfl) ⟨698342, by rfl⟩ : syracuseStep 931123 = 1396685) B1396685
theorem B931139 : Blo 928581 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B931155 : Blo 928581 931155 := bstep (se 1 (by rfl) ⟨698366, by rfl⟩ : syracuseStep 931155 = 1396733) B1396733
theorem B931171 : Blo 928581 931171 := bstep (se 1 (by rfl) ⟨698378, by rfl⟩ : syracuseStep 931171 = 1396757) B1396757
theorem B931187 : Blo 928581 931187 := bstep (se 1 (by rfl) ⟨698390, by rfl⟩ : syracuseStep 931187 = 1396781) B1396781
theorem B931203 : Blo 928581 931203 := bstep (se 1 (by rfl) ⟨698402, by rfl⟩ : syracuseStep 931203 = 1396805) B1396805
theorem B8074637 : Blo 928581 8074637 := bstep (se 3 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 8074637 = 3027989) B3027989
theorem B931219 : Blo 928581 931219 := bstep (se 1 (by rfl) ⟨698414, by rfl⟩ : syracuseStep 931219 = 1396829) B1396829
theorem B1324451 : Blo 928581 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B931235 : Blo 928581 931235 := bstep (se 1 (by rfl) ⟨698426, by rfl⟩ : syracuseStep 931235 = 1396853) B1396853
theorem B931251 : Blo 928581 931251 := bstep (se 1 (by rfl) ⟨698438, by rfl⟩ : syracuseStep 931251 = 1396877) B1396877
theorem B931267 : Blo 928581 931267 := bstep (se 1 (by rfl) ⟨698450, by rfl⟩ : syracuseStep 931267 = 1396901) B1396901
theorem B931283 : Blo 928581 931283 := bstep (se 1 (by rfl) ⟨698462, by rfl⟩ : syracuseStep 931283 = 1396925) B1396925
theorem B931299 : Blo 928581 931299 := bstep (se 1 (by rfl) ⟨698474, by rfl⟩ : syracuseStep 931299 = 1396949) B1396949
theorem B931315 : Blo 928581 931315 := bstep (se 1 (by rfl) ⟨698486, by rfl⟩ : syracuseStep 931315 = 1396973) B1396973
theorem B931331 : Blo 928581 931331 := bstep (se 1 (by rfl) ⟨698498, by rfl⟩ : syracuseStep 931331 = 1396997) B1396997
theorem B931347 : Blo 928581 931347 := bstep (se 1 (by rfl) ⟨698510, by rfl⟩ : syracuseStep 931347 = 1397021) B1397021
theorem B931363 : Blo 928581 931363 := bstep (se 1 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 931363 = 1397045) B1397045
theorem B931379 : Blo 928581 931379 := bstep (se 1 (by rfl) ⟨698534, by rfl⟩ : syracuseStep 931379 = 1397069) B1397069
theorem B1488451 : Blo 928581 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B931395 : Blo 928581 931395 := bstep (se 1 (by rfl) ⟨698546, by rfl⟩ : syracuseStep 931395 = 1397093) B1397093
theorem B4470349 : Blo 928581 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B931411 : Blo 928581 931411 := bstep (se 1 (by rfl) ⟨698558, by rfl⟩ : syracuseStep 931411 = 1397117) B1397117
theorem B931427 : Blo 928581 931427 := bstep (se 1 (by rfl) ⟨698570, by rfl⟩ : syracuseStep 931427 = 1397141) B1397141
theorem B931443 : Blo 928581 931443 := bstep (se 1 (by rfl) ⟨698582, by rfl⟩ : syracuseStep 931443 = 1397165) B1397165
theorem B931459 : Blo 928581 931459 := bstep (se 1 (by rfl) ⟨698594, by rfl⟩ : syracuseStep 931459 = 1397189) B1397189
theorem B931475 : Blo 928581 931475 := bstep (se 1 (by rfl) ⟨698606, by rfl⟩ : syracuseStep 931475 = 1397213) B1397213
theorem B931491 : Blo 928581 931491 := bstep (se 1 (by rfl) ⟨698618, by rfl⟩ : syracuseStep 931491 = 1397237) B1397237
theorem B931507 : Blo 928581 931507 := bstep (se 1 (by rfl) ⟨698630, by rfl⟩ : syracuseStep 931507 = 1397261) B1397261
theorem B931523 : Blo 928581 931523 := bstep (se 1 (by rfl) ⟨698642, by rfl⟩ : syracuseStep 931523 = 1397285) B1397285
theorem B931539 : Blo 928581 931539 := bstep (se 1 (by rfl) ⟨698654, by rfl⟩ : syracuseStep 931539 = 1397309) B1397309
theorem B931555 : Blo 928581 931555 := bstep (se 1 (by rfl) ⟨698666, by rfl⟩ : syracuseStep 931555 = 1397333) B1397333
theorem B931571 : Blo 928581 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B931587 : Blo 928581 931587 := bstep (se 1 (by rfl) ⟨698690, by rfl⟩ : syracuseStep 931587 = 1397381) B1397381
theorem B931603 : Blo 928581 931603 := bstep (se 1 (by rfl) ⟨698702, by rfl⟩ : syracuseStep 931603 = 1397405) B1397405
theorem B3979043 : Blo 928581 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B931619 : Blo 928581 931619 := bstep (se 1 (by rfl) ⟨698714, by rfl⟩ : syracuseStep 931619 = 1397429) B1397429
theorem B931635 : Blo 928581 931635 := bstep (se 1 (by rfl) ⟨698726, by rfl⟩ : syracuseStep 931635 = 1397453) B1397453
theorem B1488707 : Blo 928581 1488707 := bstep (se 1 (by rfl) ⟨1116530, by rfl⟩ : syracuseStep 1488707 = 2233061) B2233061
theorem B931651 : Blo 928581 931651 := bstep (se 1 (by rfl) ⟨698738, by rfl⟩ : syracuseStep 931651 = 1397477) B1397477
theorem B931667 : Blo 928581 931667 := bstep (se 1 (by rfl) ⟨698750, by rfl⟩ : syracuseStep 931667 = 1397501) B1397501
theorem B931683 : Blo 928581 931683 := bstep (se 1 (by rfl) ⟨698762, by rfl⟩ : syracuseStep 931683 = 1397525) B1397525
theorem B931699 : Blo 928581 931699 := bstep (se 1 (by rfl) ⟨698774, by rfl⟩ : syracuseStep 931699 = 1397549) B1397549
theorem B931715 : Blo 928581 931715 := bstep (se 1 (by rfl) ⟨698786, by rfl⟩ : syracuseStep 931715 = 1397573) B1397573
theorem B9811853 : Blo 928581 9811853 := bstep (se 3 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 9811853 = 3679445) B3679445
theorem B931731 : Blo 928581 931731 := bstep (se 1 (by rfl) ⟨698798, by rfl⟩ : syracuseStep 931731 = 1397597) B1397597
theorem B931747 : Blo 928581 931747 := bstep (se 1 (by rfl) ⟨698810, by rfl⟩ : syracuseStep 931747 = 1397621) B1397621
theorem B931763 : Blo 928581 931763 := bstep (se 1 (by rfl) ⟨698822, by rfl⟩ : syracuseStep 931763 = 1397645) B1397645
theorem B931779 : Blo 928581 931779 := bstep (se 1 (by rfl) ⟨698834, by rfl⟩ : syracuseStep 931779 = 1397669) B1397669
theorem B931795 : Blo 928581 931795 := bstep (se 1 (by rfl) ⟨698846, by rfl⟩ : syracuseStep 931795 = 1397693) B1397693
theorem B931811 : Blo 928581 931811 := bstep (se 1 (by rfl) ⟨698858, by rfl⟩ : syracuseStep 931811 = 1397717) B1397717
theorem B931827 : Blo 928581 931827 := bstep (se 1 (by rfl) ⟨698870, by rfl⟩ : syracuseStep 931827 = 1397741) B1397741
theorem B1488899 : Blo 928581 1488899 := bstep (se 1 (by rfl) ⟨1116674, by rfl⟩ : syracuseStep 1488899 = 2233349) B2233349
theorem B931843 : Blo 928581 931843 := bstep (se 1 (by rfl) ⟨698882, by rfl⟩ : syracuseStep 931843 = 1397765) B1397765
theorem B5027845 : Blo 928581 5027845 := bstep (se 4 (by rfl) ⟨471360, by rfl⟩ : syracuseStep 5027845 = 942721) B942721
theorem B931859 : Blo 928581 931859 := bstep (se 1 (by rfl) ⟨698894, by rfl⟩ : syracuseStep 931859 = 1397789) B1397789
theorem B1325089 : Blo 928581 1325089 := bstep (se 2 (by rfl) ⟨496908, by rfl⟩ : syracuseStep 1325089 = 993817) B993817
theorem B931875 : Blo 928581 931875 := bstep (se 1 (by rfl) ⟨698906, by rfl⟩ : syracuseStep 931875 = 1397813) B1397813
theorem B931891 : Blo 928581 931891 := bstep (se 1 (by rfl) ⟨698918, by rfl⟩ : syracuseStep 931891 = 1397837) B1397837
theorem B931907 : Blo 928581 931907 := bstep (se 1 (by rfl) ⟨698930, by rfl⟩ : syracuseStep 931907 = 1397861) B1397861
theorem B931923 : Blo 928581 931923 := bstep (se 1 (by rfl) ⟨698942, by rfl⟩ : syracuseStep 931923 = 1397885) B1397885
theorem B931939 : Blo 928581 931939 := bstep (se 1 (by rfl) ⟨698954, by rfl⟩ : syracuseStep 931939 = 1397909) B1397909
theorem B931955 : Blo 928581 931955 := bstep (se 1 (by rfl) ⟨698966, by rfl⟩ : syracuseStep 931955 = 1397933) B1397933
theorem B931971 : Blo 928581 931971 := bstep (se 1 (by rfl) ⟨698978, by rfl⟩ : syracuseStep 931971 = 1397957) B1397957
theorem B3061901 : Blo 928581 3061901 := bstep (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) B1148213
theorem B931987 : Blo 928581 931987 := bstep (se 1 (by rfl) ⟨698990, by rfl⟩ : syracuseStep 931987 = 1397981) B1397981
theorem B4470947 : Blo 928581 4470947 := bstep (se 1 (by rfl) ⟨3353210, by rfl⟩ : syracuseStep 4470947 = 6706421) B6706421
theorem B932003 : Blo 928581 932003 := bstep (se 1 (by rfl) ⟨699002, by rfl⟩ : syracuseStep 932003 = 1398005) B1398005
theorem B932019 : Blo 928581 932019 := bstep (se 1 (by rfl) ⟨699014, by rfl⟩ : syracuseStep 932019 = 1398029) B1398029
theorem B10074293 : Blo 928581 10074293 := bstep (se 5 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 10074293 = 944465) B944465
theorem B932035 : Blo 928581 932035 := bstep (se 1 (by rfl) ⟨699026, by rfl⟩ : syracuseStep 932035 = 1398053) B1398053
theorem B932051 : Blo 928581 932051 := bstep (se 1 (by rfl) ⟨699038, by rfl⟩ : syracuseStep 932051 = 1398077) B1398077
theorem B932067 : Blo 928581 932067 := bstep (se 1 (by rfl) ⟨699050, by rfl⟩ : syracuseStep 932067 = 1398101) B1398101
theorem B932083 : Blo 928581 932083 := bstep (se 1 (by rfl) ⟨699062, by rfl⟩ : syracuseStep 932083 = 1398125) B1398125
theorem B932099 : Blo 928581 932099 := bstep (se 1 (by rfl) ⟨699074, by rfl⟩ : syracuseStep 932099 = 1398149) B1398149
theorem B932115 : Blo 928581 932115 := bstep (se 1 (by rfl) ⟨699086, by rfl⟩ : syracuseStep 932115 = 1398173) B1398173
theorem B932131 : Blo 928581 932131 := bstep (se 1 (by rfl) ⟨699098, by rfl⟩ : syracuseStep 932131 = 1398197) B1398197
theorem B932147 : Blo 928581 932147 := bstep (se 1 (by rfl) ⟨699110, by rfl⟩ : syracuseStep 932147 = 1398221) B1398221
theorem B932163 : Blo 928581 932163 := bstep (se 1 (by rfl) ⟨699122, by rfl⟩ : syracuseStep 932163 = 1398245) B1398245
theorem B932179 : Blo 928581 932179 := bstep (se 1 (by rfl) ⟨699134, by rfl⟩ : syracuseStep 932179 = 1398269) B1398269
theorem B932195 : Blo 928581 932195 := bstep (se 1 (by rfl) ⟨699146, by rfl⟩ : syracuseStep 932195 = 1398293) B1398293
theorem B1325425 : Blo 928581 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B1194355 : Blo 928581 1194355 := bstep (se 1 (by rfl) ⟨895766, by rfl⟩ : syracuseStep 1194355 = 1791533) B1791533
theorem B932211 : Blo 928581 932211 := bstep (se 1 (by rfl) ⟨699158, by rfl⟩ : syracuseStep 932211 = 1398317) B1398317
theorem B932227 : Blo 928581 932227 := bstep (se 1 (by rfl) ⟨699170, by rfl⟩ : syracuseStep 932227 = 1398341) B1398341
theorem B932243 : Blo 928581 932243 := bstep (se 1 (by rfl) ⟨699182, by rfl⟩ : syracuseStep 932243 = 1398365) B1398365
theorem B932259 : Blo 928581 932259 := bstep (se 1 (by rfl) ⟨699194, by rfl⟩ : syracuseStep 932259 = 1398389) B1398389
theorem B932275 : Blo 928581 932275 := bstep (se 1 (by rfl) ⟨699206, by rfl⟩ : syracuseStep 932275 = 1398413) B1398413
theorem B932291 : Blo 928581 932291 := bstep (se 1 (by rfl) ⟨699218, by rfl⟩ : syracuseStep 932291 = 1398437) B1398437
theorem B932307 : Blo 928581 932307 := bstep (se 1 (by rfl) ⟨699230, by rfl⟩ : syracuseStep 932307 = 1398461) B1398461
theorem B932323 : Blo 928581 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B932339 : Blo 928581 932339 := bstep (se 1 (by rfl) ⟨699254, by rfl⟩ : syracuseStep 932339 = 1398509) B1398509
theorem B932355 : Blo 928581 932355 := bstep (se 1 (by rfl) ⟨699266, by rfl⟩ : syracuseStep 932355 = 1398533) B1398533
theorem B932371 : Blo 928581 932371 := bstep (se 1 (by rfl) ⟨699278, by rfl⟩ : syracuseStep 932371 = 1398557) B1398557
theorem B932387 : Blo 928581 932387 := bstep (se 1 (by rfl) ⟨699290, by rfl⟩ : syracuseStep 932387 = 1398581) B1398581
theorem B932403 : Blo 928581 932403 := bstep (se 1 (by rfl) ⟨699302, by rfl⟩ : syracuseStep 932403 = 1398605) B1398605
theorem B932419 : Blo 928581 932419 := bstep (se 1 (by rfl) ⟨699314, by rfl⟩ : syracuseStep 932419 = 1398629) B1398629
theorem B932435 : Blo 928581 932435 := bstep (se 1 (by rfl) ⟨699326, by rfl⟩ : syracuseStep 932435 = 1398653) B1398653
theorem B932451 : Blo 928581 932451 := bstep (se 1 (by rfl) ⟨699338, by rfl⟩ : syracuseStep 932451 = 1398677) B1398677
theorem B932467 : Blo 928581 932467 := bstep (se 1 (by rfl) ⟨699350, by rfl⟩ : syracuseStep 932467 = 1398701) B1398701
theorem B932483 : Blo 928581 932483 := bstep (se 1 (by rfl) ⟨699362, by rfl⟩ : syracuseStep 932483 = 1398725) B1398725
theorem B932499 : Blo 928581 932499 := bstep (se 1 (by rfl) ⟨699374, by rfl⟩ : syracuseStep 932499 = 1398749) B1398749
theorem B932515 : Blo 928581 932515 := bstep (se 1 (by rfl) ⟨699386, by rfl⟩ : syracuseStep 932515 = 1398773) B1398773
theorem B932531 : Blo 928581 932531 := bstep (se 1 (by rfl) ⟨699398, by rfl⟩ : syracuseStep 932531 = 1398797) B1398797
theorem B932547 : Blo 928581 932547 := bstep (se 1 (by rfl) ⟨699410, by rfl⟩ : syracuseStep 932547 = 1398821) B1398821
theorem B932563 : Blo 928581 932563 := bstep (se 1 (by rfl) ⟨699422, by rfl⟩ : syracuseStep 932563 = 1398845) B1398845
theorem B3586787 : Blo 928581 3586787 := bstep (se 1 (by rfl) ⟨2690090, by rfl⟩ : syracuseStep 3586787 = 5380181) B5380181
theorem B932579 : Blo 928581 932579 := bstep (se 1 (by rfl) ⟨699434, by rfl⟩ : syracuseStep 932579 = 1398869) B1398869
theorem B1489681 : Blo 928581 1489681 := bstep (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) B1117261
theorem B5651363 : Blo 928581 5651363 := bstep (se 1 (by rfl) ⟨4238522, by rfl⟩ : syracuseStep 5651363 = 8477045) B8477045
theorem B1326017 : Blo 928581 1326017 := bstep (se 2 (by rfl) ⟨497256, by rfl⟩ : syracuseStep 1326017 = 994513) B994513
theorem B1195267 : Blo 928581 1195267 := bstep (se 1 (by rfl) ⟨896450, by rfl⟩ : syracuseStep 1195267 = 1792901) B1792901
theorem B7945613 : Blo 928581 7945613 := bstep (se 3 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 7945613 = 2979605) B2979605
theorem B15908237 : Blo 928581 15908237 := bstep (se 3 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 15908237 = 5965589) B5965589
theorem B3816881 : Blo 928581 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B1326547 : Blo 928581 1326547 := bstep (se 1 (by rfl) ⟨994910, by rfl⟩ : syracuseStep 1326547 = 1989821) B1989821
theorem B3980785 : Blo 928581 3980785 := bstep (se 2 (by rfl) ⟨1492794, by rfl⟩ : syracuseStep 3980785 = 2985589) B2985589
theorem B10043149 : Blo 928581 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B1326883 : Blo 928581 1326883 := bstep (se 1 (by rfl) ⟨995162, by rfl⟩ : syracuseStep 1326883 = 1990325) B1990325
theorem B1392881 : Blo 928581 1392881 := bstep (se 2 (by rfl) ⟨522330, by rfl⟩ : syracuseStep 1392881 = 1044661) B1044661
theorem B1392899 : Blo 928581 1392899 := bstep (se 1 (by rfl) ⟨1044674, by rfl⟩ : syracuseStep 1392899 = 2089349) B2089349
theorem B1392929 : Blo 928581 1392929 := bstep (se 2 (by rfl) ⟨522348, by rfl⟩ : syracuseStep 1392929 = 1044697) B1044697
theorem B1392947 : Blo 928581 1392947 := bstep (se 1 (by rfl) ⟨1044710, by rfl⟩ : syracuseStep 1392947 = 2089421) B2089421
theorem B1392977 : Blo 928581 1392977 := bstep (se 2 (by rfl) ⟨522366, by rfl⟩ : syracuseStep 1392977 = 1044733) B1044733
theorem B1327441 : Blo 928581 1327441 := bstep (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) B995581
theorem B1392995 : Blo 928581 1392995 := bstep (se 1 (by rfl) ⟨1044746, by rfl⟩ : syracuseStep 1392995 = 2089493) B2089493
theorem B1327475 : Blo 928581 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B1393025 : Blo 928581 1393025 := bstep (se 2 (by rfl) ⟨522384, by rfl⟩ : syracuseStep 1393025 = 1044769) B1044769
theorem B1393043 : Blo 928581 1393043 := bstep (se 1 (by rfl) ⟨1044782, by rfl⟩ : syracuseStep 1393043 = 2089565) B2089565
theorem B1491347 : Blo 928581 1491347 := bstep (se 1 (by rfl) ⟨1118510, by rfl⟩ : syracuseStep 1491347 = 2237021) B2237021
theorem B1393073 : Blo 928581 1393073 := bstep (se 2 (by rfl) ⟨522402, by rfl⟩ : syracuseStep 1393073 = 1044805) B1044805
theorem B1393091 : Blo 928581 1393091 := bstep (se 1 (by rfl) ⟨1044818, by rfl⟩ : syracuseStep 1393091 = 2089637) B2089637
theorem B1393121 : Blo 928581 1393121 := bstep (se 2 (by rfl) ⟨522420, by rfl⟩ : syracuseStep 1393121 = 1044841) B1044841
theorem B1393139 : Blo 928581 1393139 := bstep (se 1 (by rfl) ⟨1044854, by rfl⟩ : syracuseStep 1393139 = 2089709) B2089709
theorem B1393169 : Blo 928581 1393169 := bstep (se 2 (by rfl) ⟨522438, by rfl⟩ : syracuseStep 1393169 = 1044877) B1044877
theorem B1491475 : Blo 928581 1491475 := bstep (se 1 (by rfl) ⟨1118606, by rfl⟩ : syracuseStep 1491475 = 2237213) B2237213
theorem B1393187 : Blo 928581 1393187 := bstep (se 1 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 1393187 = 2089781) B2089781
theorem B1393217 : Blo 928581 1393217 := bstep (se 2 (by rfl) ⟨522456, by rfl⟩ : syracuseStep 1393217 = 1044913) B1044913
theorem B1393235 : Blo 928581 1393235 := bstep (se 1 (by rfl) ⟨1044926, by rfl⟩ : syracuseStep 1393235 = 2089853) B2089853
theorem B1393265 : Blo 928581 1393265 := bstep (se 2 (by rfl) ⟨522474, by rfl⟩ : syracuseStep 1393265 = 1044949) B1044949
theorem B1393283 : Blo 928581 1393283 := bstep (se 1 (by rfl) ⟨1044962, by rfl⟩ : syracuseStep 1393283 = 2089925) B2089925
theorem B1393313 : Blo 928581 1393313 := bstep (se 2 (by rfl) ⟨522492, by rfl⟩ : syracuseStep 1393313 = 1044985) B1044985
theorem B1393331 : Blo 928581 1393331 := bstep (se 1 (by rfl) ⟨1044998, by rfl⟩ : syracuseStep 1393331 = 2089997) B2089997
theorem B1393361 : Blo 928581 1393361 := bstep (se 2 (by rfl) ⟨522510, by rfl⟩ : syracuseStep 1393361 = 1045021) B1045021
theorem B1393379 : Blo 928581 1393379 := bstep (se 1 (by rfl) ⟨1045034, by rfl⟩ : syracuseStep 1393379 = 2090069) B2090069
theorem B1983217 : Blo 928581 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B1393409 : Blo 928581 1393409 := bstep (se 2 (by rfl) ⟨522528, by rfl⟩ : syracuseStep 1393409 = 1045057) B1045057
theorem B1393427 : Blo 928581 1393427 := bstep (se 1 (by rfl) ⟨1045070, by rfl⟩ : syracuseStep 1393427 = 2090141) B2090141
theorem B1393457 : Blo 928581 1393457 := bstep (se 2 (by rfl) ⟨522546, by rfl⟩ : syracuseStep 1393457 = 1045093) B1045093
theorem B1393475 : Blo 928581 1393475 := bstep (se 1 (by rfl) ⟨1045106, by rfl⟩ : syracuseStep 1393475 = 2090213) B2090213
theorem B1393505 : Blo 928581 1393505 := bstep (se 2 (by rfl) ⟨522564, by rfl⟩ : syracuseStep 1393505 = 1045129) B1045129
theorem B1393523 : Blo 928581 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B1393553 : Blo 928581 1393553 := bstep (se 2 (by rfl) ⟨522582, by rfl⟩ : syracuseStep 1393553 = 1045165) B1045165
theorem B1491859 : Blo 928581 1491859 := bstep (se 1 (by rfl) ⟨1118894, by rfl⟩ : syracuseStep 1491859 = 2237789) B2237789
theorem B1393571 : Blo 928581 1393571 := bstep (se 1 (by rfl) ⟨1045178, by rfl⟩ : syracuseStep 1393571 = 2090357) B2090357
theorem B1393601 : Blo 928581 1393601 := bstep (se 2 (by rfl) ⟨522600, by rfl⟩ : syracuseStep 1393601 = 1045201) B1045201
theorem B1393619 : Blo 928581 1393619 := bstep (se 1 (by rfl) ⟨1045214, by rfl⟩ : syracuseStep 1393619 = 2090429) B2090429
theorem B1393649 : Blo 928581 1393649 := bstep (se 2 (by rfl) ⟨522618, by rfl⟩ : syracuseStep 1393649 = 1045237) B1045237
theorem B1393667 : Blo 928581 1393667 := bstep (se 1 (by rfl) ⟨1045250, by rfl⟩ : syracuseStep 1393667 = 2090501) B2090501
theorem B1393697 : Blo 928581 1393697 := bstep (se 2 (by rfl) ⟨522636, by rfl⟩ : syracuseStep 1393697 = 1045273) B1045273
theorem B1393715 : Blo 928581 1393715 := bstep (se 1 (by rfl) ⟨1045286, by rfl⟩ : syracuseStep 1393715 = 2090573) B2090573
theorem B5293133 : Blo 928581 5293133 := bstep (se 3 (by rfl) ⟨992462, by rfl⟩ : syracuseStep 5293133 = 1984925) B1984925
theorem B1393745 : Blo 928581 1393745 := bstep (se 2 (by rfl) ⟨522654, by rfl⟩ : syracuseStep 1393745 = 1045309) B1045309
theorem B1393763 : Blo 928581 1393763 := bstep (se 1 (by rfl) ⟨1045322, by rfl⟩ : syracuseStep 1393763 = 2090645) B2090645
theorem B4703345 : Blo 928581 4703345 := bstep (se 2 (by rfl) ⟨1763754, by rfl⟩ : syracuseStep 4703345 = 3527509) B3527509
theorem B1885297 : Blo 928581 1885297 := bstep (se 2 (by rfl) ⟨706986, by rfl⟩ : syracuseStep 1885297 = 1413973) B1413973
theorem B7554161 : Blo 928581 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1393793 : Blo 928581 1393793 := bstep (se 2 (by rfl) ⟨522672, by rfl⟩ : syracuseStep 1393793 = 1045345) B1045345
theorem B1393811 : Blo 928581 1393811 := bstep (se 1 (by rfl) ⟨1045358, by rfl⟩ : syracuseStep 1393811 = 2090717) B2090717
theorem B1492115 : Blo 928581 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B1393841 : Blo 928581 1393841 := bstep (se 2 (by rfl) ⟨522690, by rfl⟩ : syracuseStep 1393841 = 1045381) B1045381
theorem B1393859 : Blo 928581 1393859 := bstep (se 1 (by rfl) ⟨1045394, by rfl⟩ : syracuseStep 1393859 = 2090789) B2090789
theorem B1393889 : Blo 928581 1393889 := bstep (se 2 (by rfl) ⟨522708, by rfl⟩ : syracuseStep 1393889 = 1045417) B1045417
theorem B1393907 : Blo 928581 1393907 := bstep (se 1 (by rfl) ⟨1045430, by rfl⟩ : syracuseStep 1393907 = 2090861) B2090861
theorem B1393937 : Blo 928581 1393937 := bstep (se 2 (by rfl) ⟨522726, by rfl⟩ : syracuseStep 1393937 = 1045453) B1045453
theorem B1393955 : Blo 928581 1393955 := bstep (se 1 (by rfl) ⟨1045466, by rfl⟩ : syracuseStep 1393955 = 2090933) B2090933
theorem B1393985 : Blo 928581 1393985 := bstep (se 2 (by rfl) ⟨522744, by rfl⟩ : syracuseStep 1393985 = 1045489) B1045489
theorem B1394003 : Blo 928581 1394003 := bstep (se 1 (by rfl) ⟨1045502, by rfl⟩ : syracuseStep 1394003 = 2091005) B2091005
theorem B1394033 : Blo 928581 1394033 := bstep (se 2 (by rfl) ⟨522762, by rfl⟩ : syracuseStep 1394033 = 1045525) B1045525
theorem B1394051 : Blo 928581 1394051 := bstep (se 1 (by rfl) ⟨1045538, by rfl⟩ : syracuseStep 1394051 = 2091077) B2091077
theorem B3982733 : Blo 928581 3982733 := bstep (se 3 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 3982733 = 1493525) B1493525
theorem B1394081 : Blo 928581 1394081 := bstep (se 2 (by rfl) ⟨522780, by rfl⟩ : syracuseStep 1394081 = 1045561) B1045561
theorem B1394099 : Blo 928581 1394099 := bstep (se 1 (by rfl) ⟨1045574, by rfl⟩ : syracuseStep 1394099 = 2091149) B2091149
theorem B1394129 : Blo 928581 1394129 := bstep (se 2 (by rfl) ⟨522798, by rfl⟩ : syracuseStep 1394129 = 1045597) B1045597
theorem B1394147 : Blo 928581 1394147 := bstep (se 1 (by rfl) ⟨1045610, by rfl⟩ : syracuseStep 1394147 = 2091221) B2091221
theorem B1394177 : Blo 928581 1394177 := bstep (se 2 (by rfl) ⟨522816, by rfl⟩ : syracuseStep 1394177 = 1045633) B1045633
theorem B1394195 : Blo 928581 1394195 := bstep (se 1 (by rfl) ⟨1045646, by rfl⟩ : syracuseStep 1394195 = 2091293) B2091293
theorem B1394225 : Blo 928581 1394225 := bstep (se 2 (by rfl) ⟨522834, by rfl⟩ : syracuseStep 1394225 = 1045669) B1045669
theorem B1394243 : Blo 928581 1394243 := bstep (se 1 (by rfl) ⟨1045682, by rfl⟩ : syracuseStep 1394243 = 2091365) B2091365
theorem B1394273 : Blo 928581 1394273 := bstep (se 2 (by rfl) ⟨522852, by rfl⟩ : syracuseStep 1394273 = 1045705) B1045705
theorem B1492577 : Blo 928581 1492577 := bstep (se 2 (by rfl) ⟨559716, by rfl⟩ : syracuseStep 1492577 = 1119433) B1119433
theorem B1394291 : Blo 928581 1394291 := bstep (se 1 (by rfl) ⟨1045718, by rfl⟩ : syracuseStep 1394291 = 2091437) B2091437
theorem B1394321 : Blo 928581 1394321 := bstep (se 2 (by rfl) ⟨522870, by rfl⟩ : syracuseStep 1394321 = 1045741) B1045741
theorem B1394339 : Blo 928581 1394339 := bstep (se 1 (by rfl) ⟨1045754, by rfl⟩ : syracuseStep 1394339 = 2091509) B2091509
theorem B1394369 : Blo 928581 1394369 := bstep (se 2 (by rfl) ⟨522888, by rfl⟩ : syracuseStep 1394369 = 1045777) B1045777
theorem B1492673 : Blo 928581 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B1394387 : Blo 928581 1394387 := bstep (se 1 (by rfl) ⟨1045790, by rfl⟩ : syracuseStep 1394387 = 2091581) B2091581
theorem B1492705 : Blo 928581 1492705 := bstep (se 2 (by rfl) ⟨559764, by rfl⟩ : syracuseStep 1492705 = 1119529) B1119529
theorem B2016995 : Blo 928581 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B4835057 : Blo 928581 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B1394417 : Blo 928581 1394417 := bstep (se 2 (by rfl) ⟨522906, by rfl⟩ : syracuseStep 1394417 = 1045813) B1045813
theorem B1984259 : Blo 928581 1984259 := bstep (se 1 (by rfl) ⟨1488194, by rfl⟩ : syracuseStep 1984259 = 2976389) B2976389
theorem B1394435 : Blo 928581 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B5654285 : Blo 928581 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B1394465 : Blo 928581 1394465 := bstep (se 2 (by rfl) ⟨522924, by rfl⟩ : syracuseStep 1394465 = 1045849) B1045849
theorem B1394483 : Blo 928581 1394483 := bstep (se 1 (by rfl) ⟨1045862, by rfl⟩ : syracuseStep 1394483 = 2091725) B2091725
theorem B6801221 : Blo 928581 6801221 := bstep (se 4 (by rfl) ⟨637614, by rfl⟩ : syracuseStep 6801221 = 1275229) B1275229
theorem B1394513 : Blo 928581 1394513 := bstep (se 2 (by rfl) ⟨522942, by rfl⟩ : syracuseStep 1394513 = 1045885) B1045885
theorem B1394531 : Blo 928581 1394531 := bstep (se 1 (by rfl) ⟨1045898, by rfl⟩ : syracuseStep 1394531 = 2091797) B2091797
theorem B1394561 : Blo 928581 1394561 := bstep (se 2 (by rfl) ⟨522960, by rfl⟩ : syracuseStep 1394561 = 1045921) B1045921
theorem B1394579 : Blo 928581 1394579 := bstep (se 1 (by rfl) ⟨1045934, by rfl⟩ : syracuseStep 1394579 = 2091869) B2091869
theorem B1394609 : Blo 928581 1394609 := bstep (se 2 (by rfl) ⟨522978, by rfl⟩ : syracuseStep 1394609 = 1045957) B1045957
theorem B1394627 : Blo 928581 1394627 := bstep (se 1 (by rfl) ⟨1045970, by rfl⟩ : syracuseStep 1394627 = 2091941) B2091941
theorem B1394657 : Blo 928581 1394657 := bstep (se 2 (by rfl) ⟨522996, by rfl⟩ : syracuseStep 1394657 = 1045993) B1045993
theorem B7063523 : Blo 928581 7063523 := bstep (se 1 (by rfl) ⟨5297642, by rfl⟩ : syracuseStep 7063523 = 10595285) B10595285
theorem B1394675 : Blo 928581 1394675 := bstep (se 1 (by rfl) ⟨1046006, by rfl⟩ : syracuseStep 1394675 = 2092013) B2092013
theorem B1394705 : Blo 928581 1394705 := bstep (se 2 (by rfl) ⟨523014, by rfl⟩ : syracuseStep 1394705 = 1046029) B1046029
theorem B20400149 : Blo 928581 20400149 := bstep (se 6 (by rfl) ⟨478128, by rfl⟩ : syracuseStep 20400149 = 956257) B956257
theorem B1394723 : Blo 928581 1394723 := bstep (se 1 (by rfl) ⟨1046042, by rfl⟩ : syracuseStep 1394723 = 2092085) B2092085
theorem B1394753 : Blo 928581 1394753 := bstep (se 2 (by rfl) ⟨523032, by rfl⟩ : syracuseStep 1394753 = 1046065) B1046065
theorem B1394771 : Blo 928581 1394771 := bstep (se 1 (by rfl) ⟨1046078, by rfl⟩ : syracuseStep 1394771 = 2092157) B2092157
theorem B1394801 : Blo 928581 1394801 := bstep (se 2 (by rfl) ⟨523050, by rfl⟩ : syracuseStep 1394801 = 1046101) B1046101
theorem B1394819 : Blo 928581 1394819 := bstep (se 1 (by rfl) ⟨1046114, by rfl⟩ : syracuseStep 1394819 = 2092229) B2092229
theorem B1394849 : Blo 928581 1394849 := bstep (se 2 (by rfl) ⟨523068, by rfl⟩ : syracuseStep 1394849 = 1046137) B1046137
theorem B1394867 : Blo 928581 1394867 := bstep (se 1 (by rfl) ⟨1046150, by rfl⟩ : syracuseStep 1394867 = 2092301) B2092301
theorem B1394897 : Blo 928581 1394897 := bstep (se 2 (by rfl) ⟨523086, by rfl⟩ : syracuseStep 1394897 = 1046173) B1046173
theorem B1394915 : Blo 928581 1394915 := bstep (se 1 (by rfl) ⟨1046186, by rfl⟩ : syracuseStep 1394915 = 2092373) B2092373
theorem B3361009 : Blo 928581 3361009 := bstep (se 2 (by rfl) ⟨1260378, by rfl⟩ : syracuseStep 3361009 = 2520757) B2520757
theorem B1394945 : Blo 928581 1394945 := bstep (se 2 (by rfl) ⟨523104, by rfl⟩ : syracuseStep 1394945 = 1046209) B1046209
theorem B1984771 : Blo 928581 1984771 := bstep (se 1 (by rfl) ⟨1488578, by rfl⟩ : syracuseStep 1984771 = 2977157) B2977157
theorem B1394963 : Blo 928581 1394963 := bstep (se 1 (by rfl) ⟨1046222, by rfl⟩ : syracuseStep 1394963 = 2092445) B2092445
theorem B1394993 : Blo 928581 1394993 := bstep (se 2 (by rfl) ⟨523122, by rfl⟩ : syracuseStep 1394993 = 1046245) B1046245
theorem B1395011 : Blo 928581 1395011 := bstep (se 1 (by rfl) ⟨1046258, by rfl⟩ : syracuseStep 1395011 = 2092517) B2092517
theorem B1395041 : Blo 928581 1395041 := bstep (se 2 (by rfl) ⟨523140, by rfl⟩ : syracuseStep 1395041 = 1046281) B1046281
theorem B1395059 : Blo 928581 1395059 := bstep (se 1 (by rfl) ⟨1046294, by rfl⟩ : syracuseStep 1395059 = 2092589) B2092589
theorem B1395089 : Blo 928581 1395089 := bstep (se 2 (by rfl) ⟨523158, by rfl⟩ : syracuseStep 1395089 = 1046317) B1046317
theorem B1395107 : Blo 928581 1395107 := bstep (se 1 (by rfl) ⟨1046330, by rfl⟩ : syracuseStep 1395107 = 2092661) B2092661
theorem B1395137 : Blo 928581 1395137 := bstep (se 2 (by rfl) ⟨523176, by rfl⟩ : syracuseStep 1395137 = 1046353) B1046353
theorem B1395155 : Blo 928581 1395155 := bstep (se 1 (by rfl) ⟨1046366, by rfl⟩ : syracuseStep 1395155 = 2092733) B2092733
theorem B1395185 : Blo 928581 1395185 := bstep (se 2 (by rfl) ⟨523194, by rfl⟩ : syracuseStep 1395185 = 1046389) B1046389
theorem B1395203 : Blo 928581 1395203 := bstep (se 1 (by rfl) ⟨1046402, by rfl⟩ : syracuseStep 1395203 = 2092805) B2092805
theorem B1395233 : Blo 928581 1395233 := bstep (se 2 (by rfl) ⟨523212, by rfl⟩ : syracuseStep 1395233 = 1046425) B1046425
theorem B4704803 : Blo 928581 4704803 := bstep (se 1 (by rfl) ⟨3528602, by rfl⟩ : syracuseStep 4704803 = 7057205) B7057205
theorem B1395251 : Blo 928581 1395251 := bstep (se 1 (by rfl) ⟨1046438, by rfl⟩ : syracuseStep 1395251 = 2092877) B2092877
theorem B10078789 : Blo 928581 10078789 := bstep (se 4 (by rfl) ⟨944886, by rfl⟩ : syracuseStep 10078789 = 1889773) B1889773
theorem B1395281 : Blo 928581 1395281 := bstep (se 2 (by rfl) ⟨523230, by rfl⟩ : syracuseStep 1395281 = 1046461) B1046461
theorem B1395299 : Blo 928581 1395299 := bstep (se 1 (by rfl) ⟨1046474, by rfl⟩ : syracuseStep 1395299 = 2092949) B2092949
theorem B1395329 : Blo 928581 1395329 := bstep (se 2 (by rfl) ⟨523248, by rfl⟩ : syracuseStep 1395329 = 1046497) B1046497
theorem B1395347 : Blo 928581 1395347 := bstep (se 1 (by rfl) ⟨1046510, by rfl⟩ : syracuseStep 1395347 = 2093021) B2093021
theorem B1395377 : Blo 928581 1395377 := bstep (se 2 (by rfl) ⟨523266, by rfl⟩ : syracuseStep 1395377 = 1046533) B1046533
theorem B1395395 : Blo 928581 1395395 := bstep (se 1 (by rfl) ⟨1046546, by rfl⟩ : syracuseStep 1395395 = 2093093) B2093093
theorem B1395425 : Blo 928581 1395425 := bstep (se 2 (by rfl) ⟨523284, by rfl⟩ : syracuseStep 1395425 = 1046569) B1046569
theorem B1395443 : Blo 928581 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B1395473 : Blo 928581 1395473 := bstep (se 2 (by rfl) ⟨523302, by rfl⟩ : syracuseStep 1395473 = 1046605) B1046605
theorem B1395491 : Blo 928581 1395491 := bstep (se 1 (by rfl) ⟨1046618, by rfl⟩ : syracuseStep 1395491 = 2093237) B2093237
theorem B1395521 : Blo 928581 1395521 := bstep (se 2 (by rfl) ⟨523320, by rfl⟩ : syracuseStep 1395521 = 1046641) B1046641
theorem B1395539 : Blo 928581 1395539 := bstep (se 1 (by rfl) ⟨1046654, by rfl⟩ : syracuseStep 1395539 = 2093309) B2093309
theorem B1395569 : Blo 928581 1395569 := bstep (se 2 (by rfl) ⟨523338, by rfl⟩ : syracuseStep 1395569 = 1046677) B1046677
theorem B1395587 : Blo 928581 1395587 := bstep (se 1 (by rfl) ⟨1046690, by rfl⟩ : syracuseStep 1395587 = 2093381) B2093381
theorem B1395617 : Blo 928581 1395617 := bstep (se 2 (by rfl) ⟨523356, by rfl⟩ : syracuseStep 1395617 = 1046713) B1046713
theorem B1395635 : Blo 928581 1395635 := bstep (se 1 (by rfl) ⟨1046726, by rfl⟩ : syracuseStep 1395635 = 2093453) B2093453
theorem B1985489 : Blo 928581 1985489 := bstep (se 2 (by rfl) ⟨744558, by rfl⟩ : syracuseStep 1985489 = 1489117) B1489117
theorem B1395665 : Blo 928581 1395665 := bstep (se 2 (by rfl) ⟨523374, by rfl⟩ : syracuseStep 1395665 = 1046749) B1046749
theorem B1395683 : Blo 928581 1395683 := bstep (se 1 (by rfl) ⟨1046762, by rfl⟩ : syracuseStep 1395683 = 2093525) B2093525
theorem B1395713 : Blo 928581 1395713 := bstep (se 2 (by rfl) ⟨523392, by rfl⟩ : syracuseStep 1395713 = 1046785) B1046785
theorem B1395731 : Blo 928581 1395731 := bstep (se 1 (by rfl) ⟨1046798, by rfl⟩ : syracuseStep 1395731 = 2093597) B2093597
theorem B1395761 : Blo 928581 1395761 := bstep (se 2 (by rfl) ⟨523410, by rfl⟩ : syracuseStep 1395761 = 1046821) B1046821
theorem B1395779 : Blo 928581 1395779 := bstep (se 1 (by rfl) ⟨1046834, by rfl⟩ : syracuseStep 1395779 = 2093669) B2093669
theorem B1395809 : Blo 928581 1395809 := bstep (se 2 (by rfl) ⟨523428, by rfl⟩ : syracuseStep 1395809 = 1046857) B1046857
theorem B1395827 : Blo 928581 1395827 := bstep (se 1 (by rfl) ⟨1046870, by rfl⟩ : syracuseStep 1395827 = 2093741) B2093741
theorem B1395857 : Blo 928581 1395857 := bstep (se 2 (by rfl) ⟨523446, by rfl⟩ : syracuseStep 1395857 = 1046893) B1046893
theorem B1395875 : Blo 928581 1395875 := bstep (se 1 (by rfl) ⟨1046906, by rfl⟩ : syracuseStep 1395875 = 2093813) B2093813
theorem B5033123 : Blo 928581 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B1395905 : Blo 928581 1395905 := bstep (se 2 (by rfl) ⟨523464, by rfl⟩ : syracuseStep 1395905 = 1046929) B1046929
theorem B1395923 : Blo 928581 1395923 := bstep (se 1 (by rfl) ⟨1046942, by rfl⟩ : syracuseStep 1395923 = 2093885) B2093885
theorem B1395953 : Blo 928581 1395953 := bstep (se 2 (by rfl) ⟨523482, by rfl⟩ : syracuseStep 1395953 = 1046965) B1046965
theorem B1395971 : Blo 928581 1395971 := bstep (se 1 (by rfl) ⟨1046978, by rfl⟩ : syracuseStep 1395971 = 2093957) B2093957
theorem B5295365 : Blo 928581 5295365 := bstep (se 4 (by rfl) ⟨496440, by rfl⟩ : syracuseStep 5295365 = 992881) B992881
theorem B1396001 : Blo 928581 1396001 := bstep (se 2 (by rfl) ⟨523500, by rfl⟩ : syracuseStep 1396001 = 1047001) B1047001
theorem B1396019 : Blo 928581 1396019 := bstep (se 1 (by rfl) ⟨1047014, by rfl⟩ : syracuseStep 1396019 = 2094029) B2094029
theorem B4705613 : Blo 928581 4705613 := bstep (se 3 (by rfl) ⟨882302, by rfl⟩ : syracuseStep 4705613 = 1764605) B1764605
theorem B1396049 : Blo 928581 1396049 := bstep (se 2 (by rfl) ⟨523518, by rfl⟩ : syracuseStep 1396049 = 1047037) B1047037
theorem B1396067 : Blo 928581 1396067 := bstep (se 1 (by rfl) ⟨1047050, by rfl⟩ : syracuseStep 1396067 = 2094101) B2094101
theorem B1396097 : Blo 928581 1396097 := bstep (se 2 (by rfl) ⟨523536, by rfl⟩ : syracuseStep 1396097 = 1047073) B1047073
theorem B1396115 : Blo 928581 1396115 := bstep (se 1 (by rfl) ⟨1047086, by rfl⟩ : syracuseStep 1396115 = 2094173) B2094173
theorem B3526051 : Blo 928581 3526051 := bstep (se 1 (by rfl) ⟨2644538, by rfl⟩ : syracuseStep 3526051 = 5289077) B5289077
theorem B1396145 : Blo 928581 1396145 := bstep (se 2 (by rfl) ⟨523554, by rfl⟩ : syracuseStep 1396145 = 1047109) B1047109
theorem B1396163 : Blo 928581 1396163 := bstep (se 1 (by rfl) ⟨1047122, by rfl⟩ : syracuseStep 1396163 = 2094245) B2094245
theorem B1396193 : Blo 928581 1396193 := bstep (se 2 (by rfl) ⟨523572, by rfl⟩ : syracuseStep 1396193 = 1047145) B1047145
theorem B1396211 : Blo 928581 1396211 := bstep (se 1 (by rfl) ⟨1047158, by rfl⟩ : syracuseStep 1396211 = 2094317) B2094317
theorem B1396241 : Blo 928581 1396241 := bstep (se 2 (by rfl) ⟨523590, by rfl⟩ : syracuseStep 1396241 = 1047181) B1047181
theorem B1396259 : Blo 928581 1396259 := bstep (se 1 (by rfl) ⟨1047194, by rfl⟩ : syracuseStep 1396259 = 2094389) B2094389
theorem B1396289 : Blo 928581 1396289 := bstep (se 2 (by rfl) ⟨523608, by rfl⟩ : syracuseStep 1396289 = 1047217) B1047217
theorem B1396307 : Blo 928581 1396307 := bstep (se 1 (by rfl) ⟨1047230, by rfl⟩ : syracuseStep 1396307 = 2094461) B2094461
theorem B4836977 : Blo 928581 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B1396337 : Blo 928581 1396337 := bstep (se 2 (by rfl) ⟨523626, by rfl⟩ : syracuseStep 1396337 = 1047253) B1047253
theorem B1396355 : Blo 928581 1396355 := bstep (se 1 (by rfl) ⟨1047266, by rfl⟩ : syracuseStep 1396355 = 2094533) B2094533
theorem B1887875 : Blo 928581 1887875 := bstep (se 1 (by rfl) ⟨1415906, by rfl⟩ : syracuseStep 1887875 = 2831813) B2831813
theorem B1396385 : Blo 928581 1396385 := bstep (se 2 (by rfl) ⟨523644, by rfl⟩ : syracuseStep 1396385 = 1047289) B1047289
theorem B1396403 : Blo 928581 1396403 := bstep (se 1 (by rfl) ⟨1047302, by rfl⟩ : syracuseStep 1396403 = 2094605) B2094605
theorem B1396433 : Blo 928581 1396433 := bstep (se 2 (by rfl) ⟨523662, by rfl⟩ : syracuseStep 1396433 = 1047325) B1047325
theorem B1986275 : Blo 928581 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B1396451 : Blo 928581 1396451 := bstep (se 1 (by rfl) ⟨1047338, by rfl⟩ : syracuseStep 1396451 = 2094677) B2094677
theorem B5099249 : Blo 928581 5099249 := bstep (se 2 (by rfl) ⟨1912218, by rfl⟩ : syracuseStep 5099249 = 3824437) B3824437
theorem B1396481 : Blo 928581 1396481 := bstep (se 2 (by rfl) ⟨523680, by rfl⟩ : syracuseStep 1396481 = 1047361) B1047361
theorem B1396499 : Blo 928581 1396499 := bstep (se 1 (by rfl) ⟨1047374, by rfl⟩ : syracuseStep 1396499 = 2094749) B2094749
theorem B1396529 : Blo 928581 1396529 := bstep (se 2 (by rfl) ⟨523698, by rfl⟩ : syracuseStep 1396529 = 1047397) B1047397
theorem B1396547 : Blo 928581 1396547 := bstep (se 1 (by rfl) ⟨1047410, by rfl⟩ : syracuseStep 1396547 = 2094821) B2094821
theorem B1396577 : Blo 928581 1396577 := bstep (se 2 (by rfl) ⟨523716, by rfl⟩ : syracuseStep 1396577 = 1047433) B1047433
theorem B23842673 : Blo 928581 23842673 := bstep (se 2 (by rfl) ⟨8941002, by rfl⟩ : syracuseStep 23842673 = 17882005) B17882005
theorem B1396595 : Blo 928581 1396595 := bstep (se 1 (by rfl) ⟨1047446, by rfl⟩ : syracuseStep 1396595 = 2094893) B2094893
theorem B1396625 : Blo 928581 1396625 := bstep (se 2 (by rfl) ⟨523734, by rfl⟩ : syracuseStep 1396625 = 1047469) B1047469
theorem B1396643 : Blo 928581 1396643 := bstep (se 1 (by rfl) ⟨1047482, by rfl⟩ : syracuseStep 1396643 = 2094965) B2094965
theorem B5296049 : Blo 928581 5296049 := bstep (se 2 (by rfl) ⟨1986018, by rfl⟩ : syracuseStep 5296049 = 3972037) B3972037
theorem B1396673 : Blo 928581 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B1396691 : Blo 928581 1396691 := bstep (se 1 (by rfl) ⟨1047518, by rfl⟩ : syracuseStep 1396691 = 2095037) B2095037
theorem B1396721 : Blo 928581 1396721 := bstep (se 2 (by rfl) ⟨523770, by rfl⟩ : syracuseStep 1396721 = 1047541) B1047541
theorem B1396739 : Blo 928581 1396739 := bstep (se 1 (by rfl) ⟨1047554, by rfl⟩ : syracuseStep 1396739 = 2095109) B2095109
theorem B1396769 : Blo 928581 1396769 := bstep (se 2 (by rfl) ⟨523788, by rfl⟩ : syracuseStep 1396769 = 1047577) B1047577
theorem B1396787 : Blo 928581 1396787 := bstep (se 1 (by rfl) ⟨1047590, by rfl⟩ : syracuseStep 1396787 = 2095181) B2095181
theorem B10047557 : Blo 928581 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B2510929 : Blo 928581 2510929 := bstep (se 2 (by rfl) ⟨941598, by rfl⟩ : syracuseStep 2510929 = 1883197) B1883197
theorem B1396817 : Blo 928581 1396817 := bstep (se 2 (by rfl) ⟨523806, by rfl⟩ : syracuseStep 1396817 = 1047613) B1047613
theorem B1396835 : Blo 928581 1396835 := bstep (se 1 (by rfl) ⟨1047626, by rfl⟩ : syracuseStep 1396835 = 2095253) B2095253
theorem B1396865 : Blo 928581 1396865 := bstep (se 2 (by rfl) ⟨523824, by rfl⟩ : syracuseStep 1396865 = 1047649) B1047649
theorem B1396883 : Blo 928581 1396883 := bstep (se 1 (by rfl) ⟨1047662, by rfl⟩ : syracuseStep 1396883 = 2095325) B2095325
theorem B1396913 : Blo 928581 1396913 := bstep (se 2 (by rfl) ⟨523842, by rfl⟩ : syracuseStep 1396913 = 1047685) B1047685
theorem B1396931 : Blo 928581 1396931 := bstep (se 1 (by rfl) ⟨1047698, by rfl⟩ : syracuseStep 1396931 = 2095397) B2095397
theorem B1396961 : Blo 928581 1396961 := bstep (se 2 (by rfl) ⟨523860, by rfl⟩ : syracuseStep 1396961 = 1047721) B1047721
theorem B1396979 : Blo 928581 1396979 := bstep (se 1 (by rfl) ⟨1047734, by rfl⟩ : syracuseStep 1396979 = 2095469) B2095469
theorem B1397009 : Blo 928581 1397009 := bstep (se 2 (by rfl) ⟨523878, by rfl⟩ : syracuseStep 1397009 = 1047757) B1047757
theorem B1397027 : Blo 928581 1397027 := bstep (se 1 (by rfl) ⟨1047770, by rfl⟩ : syracuseStep 1397027 = 2095541) B2095541
theorem B1397057 : Blo 928581 1397057 := bstep (se 2 (by rfl) ⟨523896, by rfl⟩ : syracuseStep 1397057 = 1047793) B1047793
theorem B1397075 : Blo 928581 1397075 := bstep (se 1 (by rfl) ⟨1047806, by rfl⟩ : syracuseStep 1397075 = 2095613) B2095613
theorem B1397105 : Blo 928581 1397105 := bstep (se 2 (by rfl) ⟨523914, by rfl⟩ : syracuseStep 1397105 = 1047829) B1047829
theorem B1397123 : Blo 928581 1397123 := bstep (se 1 (by rfl) ⟨1047842, by rfl⟩ : syracuseStep 1397123 = 2095685) B2095685
theorem B3232145 : Blo 928581 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B1397153 : Blo 928581 1397153 := bstep (se 2 (by rfl) ⟨523932, by rfl⟩ : syracuseStep 1397153 = 1047865) B1047865
theorem B1397171 : Blo 928581 1397171 := bstep (se 1 (by rfl) ⟨1047878, by rfl⟩ : syracuseStep 1397171 = 2095757) B2095757
theorem B1397201 : Blo 928581 1397201 := bstep (se 2 (by rfl) ⟨523950, by rfl⟩ : syracuseStep 1397201 = 1047901) B1047901
theorem B1397219 : Blo 928581 1397219 := bstep (se 1 (by rfl) ⟨1047914, by rfl⟩ : syracuseStep 1397219 = 2095829) B2095829
theorem B1397249 : Blo 928581 1397249 := bstep (se 2 (by rfl) ⟨523968, by rfl⟩ : syracuseStep 1397249 = 1047937) B1047937
theorem B1397267 : Blo 928581 1397267 := bstep (se 1 (by rfl) ⟨1047950, by rfl⟩ : syracuseStep 1397267 = 2095901) B2095901
theorem B2511395 : Blo 928581 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B3133997 : Blo 928581 3133997 := bstep (se 3 (by rfl) ⟨587624, by rfl⟩ : syracuseStep 3133997 = 1175249) B1175249
theorem B1397297 : Blo 928581 1397297 := bstep (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) B1047973
theorem B1397315 : Blo 928581 1397315 := bstep (se 1 (by rfl) ⟨1047986, by rfl⟩ : syracuseStep 1397315 = 2095973) B2095973
theorem B1397345 : Blo 928581 1397345 := bstep (se 2 (by rfl) ⟨524004, by rfl⟩ : syracuseStep 1397345 = 1048009) B1048009
theorem B3134051 : Blo 928581 3134051 := bstep (se 1 (by rfl) ⟨2350538, by rfl⟩ : syracuseStep 3134051 = 4701077) B4701077
theorem B5034595 : Blo 928581 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B1397363 : Blo 928581 1397363 := bstep (se 1 (by rfl) ⟨1048022, by rfl⟩ : syracuseStep 1397363 = 2096045) B2096045
theorem B1397393 : Blo 928581 1397393 := bstep (se 2 (by rfl) ⟨524022, by rfl⟩ : syracuseStep 1397393 = 1048045) B1048045
theorem B1397411 : Blo 928581 1397411 := bstep (se 1 (by rfl) ⟨1048058, by rfl⟩ : syracuseStep 1397411 = 2096117) B2096117
theorem B1987249 : Blo 928581 1987249 := bstep (se 2 (by rfl) ⟨745218, by rfl⟩ : syracuseStep 1987249 = 1490437) B1490437
theorem B1397441 : Blo 928581 1397441 := bstep (se 2 (by rfl) ⟨524040, by rfl⟩ : syracuseStep 1397441 = 1048081) B1048081
theorem B1397459 : Blo 928581 1397459 := bstep (se 1 (by rfl) ⟨1048094, by rfl⟩ : syracuseStep 1397459 = 2096189) B2096189
theorem B1397489 : Blo 928581 1397489 := bstep (se 2 (by rfl) ⟨524058, by rfl⟩ : syracuseStep 1397489 = 1048117) B1048117
theorem B1397507 : Blo 928581 1397507 := bstep (se 1 (by rfl) ⟨1048130, by rfl⟩ : syracuseStep 1397507 = 2096261) B2096261
theorem B1397537 : Blo 928581 1397537 := bstep (se 2 (by rfl) ⟨524076, by rfl⟩ : syracuseStep 1397537 = 1048153) B1048153
theorem B1397555 : Blo 928581 1397555 := bstep (se 1 (by rfl) ⟨1048166, by rfl⟩ : syracuseStep 1397555 = 2096333) B2096333
theorem B1397585 : Blo 928581 1397585 := bstep (se 2 (by rfl) ⟨524094, by rfl⟩ : syracuseStep 1397585 = 1048189) B1048189
theorem B1397603 : Blo 928581 1397603 := bstep (se 1 (by rfl) ⟨1048202, by rfl⟩ : syracuseStep 1397603 = 2096405) B2096405
theorem B5034851 : Blo 928581 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B3134321 : Blo 928581 3134321 := bstep (se 2 (by rfl) ⟨1175370, by rfl⟩ : syracuseStep 3134321 = 2350741) B2350741
theorem B1397633 : Blo 928581 1397633 := bstep (se 2 (by rfl) ⟨524112, by rfl⟩ : syracuseStep 1397633 = 1048225) B1048225
theorem B1397651 : Blo 928581 1397651 := bstep (se 1 (by rfl) ⟨1048238, by rfl⟩ : syracuseStep 1397651 = 2096477) B2096477
theorem B1987505 : Blo 928581 1987505 := bstep (se 2 (by rfl) ⟨745314, by rfl⟩ : syracuseStep 1987505 = 1490629) B1490629
theorem B1397681 : Blo 928581 1397681 := bstep (se 2 (by rfl) ⟨524130, by rfl⟩ : syracuseStep 1397681 = 1048261) B1048261
theorem B1397699 : Blo 928581 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B1397729 : Blo 928581 1397729 := bstep (se 2 (by rfl) ⟨524148, by rfl⟩ : syracuseStep 1397729 = 1048297) B1048297
theorem B1397747 : Blo 928581 1397747 := bstep (se 1 (by rfl) ⟨1048310, by rfl⟩ : syracuseStep 1397747 = 2096621) B2096621
theorem B1135603 : Blo 928581 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B1397777 : Blo 928581 1397777 := bstep (se 2 (by rfl) ⟨524166, by rfl⟩ : syracuseStep 1397777 = 1048333) B1048333
theorem B1397795 : Blo 928581 1397795 := bstep (se 1 (by rfl) ⟨1048346, by rfl⟩ : syracuseStep 1397795 = 2096693) B2096693
theorem B1397825 : Blo 928581 1397825 := bstep (se 2 (by rfl) ⟨524184, by rfl⟩ : syracuseStep 1397825 = 1048369) B1048369
theorem B1397843 : Blo 928581 1397843 := bstep (se 1 (by rfl) ⟨1048382, by rfl⟩ : syracuseStep 1397843 = 2096765) B2096765
theorem B1397873 : Blo 928581 1397873 := bstep (se 2 (by rfl) ⟨524202, by rfl⟩ : syracuseStep 1397873 = 1048405) B1048405
theorem B1397891 : Blo 928581 1397891 := bstep (se 1 (by rfl) ⟨1048418, by rfl⟩ : syracuseStep 1397891 = 2096837) B2096837
theorem B1397921 : Blo 928581 1397921 := bstep (se 2 (by rfl) ⟨524220, by rfl⟩ : syracuseStep 1397921 = 1048441) B1048441
theorem B1397939 : Blo 928581 1397939 := bstep (se 1 (by rfl) ⟨1048454, by rfl⟩ : syracuseStep 1397939 = 2096909) B2096909
theorem B1397969 : Blo 928581 1397969 := bstep (se 2 (by rfl) ⟨524238, by rfl⟩ : syracuseStep 1397969 = 1048477) B1048477
theorem B1397987 : Blo 928581 1397987 := bstep (se 1 (by rfl) ⟨1048490, by rfl⟩ : syracuseStep 1397987 = 2096981) B2096981
theorem B1398017 : Blo 928581 1398017 := bstep (se 2 (by rfl) ⟨524256, by rfl⟩ : syracuseStep 1398017 = 1048513) B1048513
theorem B1398035 : Blo 928581 1398035 := bstep (se 1 (by rfl) ⟨1048526, by rfl⟩ : syracuseStep 1398035 = 2097053) B2097053
theorem B1398065 : Blo 928581 1398065 := bstep (se 2 (by rfl) ⟨524274, by rfl⟩ : syracuseStep 1398065 = 1048549) B1048549
theorem B1398083 : Blo 928581 1398083 := bstep (se 1 (by rfl) ⟨1048562, by rfl⟩ : syracuseStep 1398083 = 2097125) B2097125
theorem B1398113 : Blo 928581 1398113 := bstep (se 2 (by rfl) ⟨524292, by rfl⟩ : syracuseStep 1398113 = 1048585) B1048585
theorem B5297507 : Blo 928581 5297507 := bstep (se 1 (by rfl) ⟨3973130, by rfl⟩ : syracuseStep 5297507 = 7946261) B7946261
theorem B1398131 : Blo 928581 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B3134861 : Blo 928581 3134861 := bstep (se 3 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 3134861 = 1175573) B1175573
theorem B1398161 : Blo 928581 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B1398179 : Blo 928581 1398179 := bstep (se 1 (by rfl) ⟨1048634, by rfl⟩ : syracuseStep 1398179 = 2097269) B2097269
theorem B1398209 : Blo 928581 1398209 := bstep (se 2 (by rfl) ⟨524328, by rfl⟩ : syracuseStep 1398209 = 1048657) B1048657
theorem B3134915 : Blo 928581 3134915 := bstep (se 1 (by rfl) ⟨2351186, by rfl⟩ : syracuseStep 3134915 = 4702373) B4702373
theorem B1398227 : Blo 928581 1398227 := bstep (se 1 (by rfl) ⟨1048670, by rfl⟩ : syracuseStep 1398227 = 2097341) B2097341
theorem B1398257 : Blo 928581 1398257 := bstep (se 2 (by rfl) ⟨524346, by rfl⟩ : syracuseStep 1398257 = 1048693) B1048693
theorem B1398275 : Blo 928581 1398275 := bstep (se 1 (by rfl) ⟨1048706, by rfl⟩ : syracuseStep 1398275 = 2097413) B2097413
theorem B1398305 : Blo 928581 1398305 := bstep (se 2 (by rfl) ⟨524364, by rfl⟩ : syracuseStep 1398305 = 1048729) B1048729
theorem B1398323 : Blo 928581 1398323 := bstep (se 1 (by rfl) ⟨1048742, by rfl⟩ : syracuseStep 1398323 = 2097485) B2097485
theorem B3528269 : Blo 928581 3528269 := bstep (se 3 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 3528269 = 1323101) B1323101
theorem B1398353 : Blo 928581 1398353 := bstep (se 2 (by rfl) ⟨524382, by rfl⟩ : syracuseStep 1398353 = 1048765) B1048765
theorem B1398371 : Blo 928581 1398371 := bstep (se 1 (by rfl) ⟨1048778, by rfl⟩ : syracuseStep 1398371 = 2097557) B2097557
theorem B1398401 : Blo 928581 1398401 := bstep (se 2 (by rfl) ⟨524400, by rfl⟩ : syracuseStep 1398401 = 1048801) B1048801
theorem B1398419 : Blo 928581 1398419 := bstep (se 1 (by rfl) ⟨1048814, by rfl⟩ : syracuseStep 1398419 = 2097629) B2097629
theorem B5658275 : Blo 928581 5658275 := bstep (se 1 (by rfl) ⟨4243706, by rfl⟩ : syracuseStep 5658275 = 8487413) B8487413
theorem B1398449 : Blo 928581 1398449 := bstep (se 2 (by rfl) ⟨524418, by rfl⟩ : syracuseStep 1398449 = 1048837) B1048837
theorem B1398467 : Blo 928581 1398467 := bstep (se 1 (by rfl) ⟨1048850, by rfl⟩ : syracuseStep 1398467 = 2097701) B2097701
theorem B3135185 : Blo 928581 3135185 := bstep (se 2 (by rfl) ⟨1175694, by rfl⟩ : syracuseStep 3135185 = 2351389) B2351389
theorem B1398497 : Blo 928581 1398497 := bstep (se 2 (by rfl) ⟨524436, by rfl⟩ : syracuseStep 1398497 = 1048873) B1048873
theorem B1398515 : Blo 928581 1398515 := bstep (se 1 (by rfl) ⟨1048886, by rfl⟩ : syracuseStep 1398515 = 2097773) B2097773
theorem B1398545 : Blo 928581 1398545 := bstep (se 2 (by rfl) ⟨524454, by rfl⟩ : syracuseStep 1398545 = 1048909) B1048909
theorem B33969941 : Blo 928581 33969941 := bstep (se 6 (by rfl) ⟨796170, by rfl⟩ : syracuseStep 33969941 = 1592341) B1592341
theorem B1398563 : Blo 928581 1398563 := bstep (se 1 (by rfl) ⟨1048922, by rfl⟩ : syracuseStep 1398563 = 2097845) B2097845
theorem B13391669 : Blo 928581 13391669 := bstep (se 5 (by rfl) ⟨627734, by rfl⟩ : syracuseStep 13391669 = 1255469) B1255469
theorem B1398593 : Blo 928581 1398593 := bstep (se 2 (by rfl) ⟨524472, by rfl⟩ : syracuseStep 1398593 = 1048945) B1048945
theorem B1398611 : Blo 928581 1398611 := bstep (se 1 (by rfl) ⟨1048958, by rfl⟩ : syracuseStep 1398611 = 2097917) B2097917
theorem B1398641 : Blo 928581 1398641 := bstep (se 2 (by rfl) ⟨524490, by rfl⟩ : syracuseStep 1398641 = 1048981) B1048981
theorem B1431427 : Blo 928581 1431427 := bstep (se 1 (by rfl) ⟨1073570, by rfl⟩ : syracuseStep 1431427 = 2147141) B2147141
theorem B1398659 : Blo 928581 1398659 := bstep (se 1 (by rfl) ⟨1048994, by rfl⟩ : syracuseStep 1398659 = 2097989) B2097989
theorem B1398689 : Blo 928581 1398689 := bstep (se 2 (by rfl) ⟨524508, by rfl⟩ : syracuseStep 1398689 = 1049017) B1049017
theorem B1398707 : Blo 928581 1398707 := bstep (se 1 (by rfl) ⟨1049030, by rfl⟩ : syracuseStep 1398707 = 2098061) B2098061
theorem B1398737 : Blo 928581 1398737 := bstep (se 2 (by rfl) ⟨524526, by rfl⟩ : syracuseStep 1398737 = 1049053) B1049053
theorem B1398755 : Blo 928581 1398755 := bstep (se 1 (by rfl) ⟨1049066, by rfl⟩ : syracuseStep 1398755 = 2098133) B2098133
theorem B1398785 : Blo 928581 1398785 := bstep (se 2 (by rfl) ⟨524544, by rfl⟩ : syracuseStep 1398785 = 1049089) B1049089
theorem B1398803 : Blo 928581 1398803 := bstep (se 1 (by rfl) ⟨1049102, by rfl⟩ : syracuseStep 1398803 = 2098205) B2098205
theorem B1398833 : Blo 928581 1398833 := bstep (se 2 (by rfl) ⟨524562, by rfl⟩ : syracuseStep 1398833 = 1049125) B1049125
theorem B1398851 : Blo 928581 1398851 := bstep (se 1 (by rfl) ⟨1049138, by rfl⟩ : syracuseStep 1398851 = 2098277) B2098277
theorem B4708529 : Blo 928581 4708529 := bstep (se 2 (by rfl) ⟨1765698, by rfl⟩ : syracuseStep 4708529 = 3531397) B3531397
theorem B1988803 : Blo 928581 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B2513101 : Blo 928581 2513101 := bstep (se 3 (by rfl) ⟨471206, by rfl⟩ : syracuseStep 2513101 = 942413) B942413
theorem B3135725 : Blo 928581 3135725 := bstep (se 3 (by rfl) ⟨587948, by rfl⟩ : syracuseStep 3135725 = 1175897) B1175897
theorem B3135779 : Blo 928581 3135779 := bstep (se 1 (by rfl) ⟨2351834, by rfl⟩ : syracuseStep 3135779 = 4703669) B4703669
theorem B1989137 : Blo 928581 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B3136049 : Blo 928581 3136049 := bstep (se 2 (by rfl) ⟨1176018, by rfl⟩ : syracuseStep 3136049 = 2352037) B2352037
theorem B2644721 : Blo 928581 2644721 := bstep (se 2 (by rfl) ⟨991770, by rfl⟩ : syracuseStep 2644721 = 1983541) B1983541
theorem B5954417 : Blo 928581 5954417 := bstep (se 2 (by rfl) ⟨2232906, by rfl⟩ : syracuseStep 5954417 = 4465813) B4465813
theorem B3627917 : Blo 928581 3627917 := bstep (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) B1360469
theorem B3136589 : Blo 928581 3136589 := bstep (se 3 (by rfl) ⟨588110, by rfl⟩ : syracuseStep 3136589 = 1176221) B1176221
theorem B3136643 : Blo 928581 3136643 := bstep (se 1 (by rfl) ⟨2352482, by rfl⟩ : syracuseStep 3136643 = 4704965) B4704965
theorem B7068869 : Blo 928581 7068869 := bstep (se 4 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 7068869 = 1325413) B1325413
theorem B3136913 : Blo 928581 3136913 := bstep (se 2 (by rfl) ⟨1176342, by rfl⟩ : syracuseStep 3136913 = 2352685) B2352685
theorem B941635 : Blo 928581 941635 := bstep (se 1 (by rfl) ⟨706226, by rfl⟩ : syracuseStep 941635 = 1412453) B1412453
theorem B2350691 : Blo 928581 2350691 := bstep (se 1 (by rfl) ⟨1763018, by rfl⟩ : syracuseStep 2350691 = 3526037) B3526037
theorem B4709987 : Blo 928581 4709987 := bstep (se 1 (by rfl) ⟨3532490, by rfl⟩ : syracuseStep 4709987 = 7064981) B7064981
theorem B1990307 : Blo 928581 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B2350883 : Blo 928581 2350883 := bstep (se 1 (by rfl) ⟨1763162, by rfl⟩ : syracuseStep 2350883 = 3526325) B3526325
theorem B3137453 : Blo 928581 3137453 := bstep (se 3 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 3137453 = 1176545) B1176545
theorem B3137507 : Blo 928581 3137507 := bstep (se 1 (by rfl) ⟨2353130, by rfl⟩ : syracuseStep 3137507 = 4706261) B4706261
theorem B1794161 : Blo 928581 1794161 := bstep (se 2 (by rfl) ⟨672810, by rfl⟩ : syracuseStep 1794161 = 1345621) B1345621
theorem B2646179 : Blo 928581 2646179 := bstep (se 1 (by rfl) ⟨1984634, by rfl⟩ : syracuseStep 2646179 = 3969269) B3969269
theorem B3629233 : Blo 928581 3629233 := bstep (se 2 (by rfl) ⟨1360962, by rfl⟩ : syracuseStep 3629233 = 2721925) B2721925
theorem B3137777 : Blo 928581 3137777 := bstep (se 2 (by rfl) ⟨1176666, by rfl⟩ : syracuseStep 3137777 = 2353333) B2353333
theorem B2122001 : Blo 928581 2122001 := bstep (se 2 (by rfl) ⟨795750, by rfl⟩ : syracuseStep 2122001 = 1591501) B1591501
theorem B4251953 : Blo 928581 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B4710797 : Blo 928581 4710797 := bstep (se 3 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 4710797 = 1766549) B1766549
theorem B3531185 : Blo 928581 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B2515427 : Blo 928581 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B2089457 : Blo 928581 2089457 := bstep (se 2 (by rfl) ⟨783546, by rfl⟩ : syracuseStep 2089457 = 1567093) B1567093
theorem B2089475 : Blo 928581 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B5300741 : Blo 928581 5300741 := bstep (se 4 (by rfl) ⟨496944, by rfl⟩ : syracuseStep 5300741 = 993889) B993889
theorem B2155075 : Blo 928581 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B942787 : Blo 928581 942787 := bstep (se 1 (by rfl) ⟨707090, by rfl⟩ : syracuseStep 942787 = 1414181) B1414181
theorem B2351825 : Blo 928581 2351825 := bstep (se 2 (by rfl) ⟨881934, by rfl⟩ : syracuseStep 2351825 = 1763869) B1763869
theorem B2351875 : Blo 928581 2351875 := bstep (se 1 (by rfl) ⟨1763906, by rfl⟩ : syracuseStep 2351875 = 3527813) B3527813
theorem B3138317 : Blo 928581 3138317 := bstep (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) B1176869
theorem B2089745 : Blo 928581 2089745 := bstep (se 2 (by rfl) ⟨783654, by rfl⟩ : syracuseStep 2089745 = 1567309) B1567309
theorem B51602197 : Blo 928581 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B2089763 : Blo 928581 2089763 := bstep (se 1 (by rfl) ⟨1567322, by rfl⟩ : syracuseStep 2089763 = 3134645) B3134645
theorem B3138371 : Blo 928581 3138371 := bstep (se 1 (by rfl) ⟨2353778, by rfl⟩ : syracuseStep 3138371 = 4707557) B4707557
theorem B4776803 : Blo 928581 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B2352017 : Blo 928581 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B2646989 : Blo 928581 2646989 := bstep (se 3 (by rfl) ⟨496310, by rfl⟩ : syracuseStep 2646989 = 992621) B992621
theorem B5301197 : Blo 928581 5301197 := bstep (se 3 (by rfl) ⟨993974, by rfl⟩ : syracuseStep 5301197 = 1987949) B1987949
theorem B2090033 : Blo 928581 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B2090051 : Blo 928581 2090051 := bstep (se 1 (by rfl) ⟨1567538, by rfl⟩ : syracuseStep 2090051 = 3135077) B3135077
theorem B3138641 : Blo 928581 3138641 := bstep (se 2 (by rfl) ⟨1176990, by rfl⟩ : syracuseStep 3138641 = 2353981) B2353981
theorem B2647181 : Blo 928581 2647181 := bstep (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) B992693
theorem B6710597 : Blo 928581 6710597 := bstep (se 4 (by rfl) ⟨629118, by rfl⟩ : syracuseStep 6710597 = 1258237) B1258237
theorem B2090321 : Blo 928581 2090321 := bstep (se 2 (by rfl) ⟨783870, by rfl⟩ : syracuseStep 2090321 = 1567741) B1567741
theorem B2090339 : Blo 928581 2090339 := bstep (se 1 (by rfl) ⟨1567754, by rfl⟩ : syracuseStep 2090339 = 3135509) B3135509
theorem B2385425 : Blo 928581 2385425 := bstep (se 2 (by rfl) ⟨894534, by rfl⟩ : syracuseStep 2385425 = 1789069) B1789069
theorem B1762897 : Blo 928581 1762897 := bstep (se 2 (by rfl) ⟨661086, by rfl⟩ : syracuseStep 1762897 = 1322173) B1322173
theorem B3139181 : Blo 928581 3139181 := bstep (se 3 (by rfl) ⟨588596, by rfl⟩ : syracuseStep 3139181 = 1177193) B1177193
theorem B2090609 : Blo 928581 2090609 := bstep (se 2 (by rfl) ⟨783978, by rfl⟩ : syracuseStep 2090609 = 1567957) B1567957
theorem B2975363 : Blo 928581 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B2090627 : Blo 928581 2090627 := bstep (se 1 (by rfl) ⟨1567970, by rfl⟩ : syracuseStep 2090627 = 3135941) B3135941
theorem B3139235 : Blo 928581 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B4253411 : Blo 928581 4253411 := bstep (se 1 (by rfl) ⟨3190058, by rfl⟩ : syracuseStep 4253411 = 6380117) B6380117
theorem B4777741 : Blo 928581 4777741 := bstep (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) B1791653
theorem B3532643 : Blo 928581 3532643 := bstep (se 1 (by rfl) ⟨2649482, by rfl⟩ : syracuseStep 3532643 = 5298965) B5298965
theorem B2353009 : Blo 928581 2353009 := bstep (se 2 (by rfl) ⟨882378, by rfl⟩ : syracuseStep 2353009 = 1764757) B1764757
theorem B2090897 : Blo 928581 2090897 := bstep (se 2 (by rfl) ⟨784086, by rfl⟩ : syracuseStep 2090897 = 1568173) B1568173
theorem B2090915 : Blo 928581 2090915 := bstep (se 1 (by rfl) ⟨1568186, by rfl⟩ : syracuseStep 2090915 = 3136373) B3136373
theorem B3139505 : Blo 928581 3139505 := bstep (se 2 (by rfl) ⟨1177314, by rfl⟩ : syracuseStep 3139505 = 2354629) B2354629
theorem B1763299 : Blo 928581 1763299 := bstep (se 1 (by rfl) ⟨1322474, by rfl⟩ : syracuseStep 1763299 = 2644949) B2644949
theorem B1763345 : Blo 928581 1763345 := bstep (se 2 (by rfl) ⟨661254, by rfl⟩ : syracuseStep 1763345 = 1322509) B1322509
theorem B2648173 : Blo 928581 2648173 := bstep (se 3 (by rfl) ⟨496532, by rfl⟩ : syracuseStep 2648173 = 993065) B993065
theorem B2353283 : Blo 928581 2353283 := bstep (se 1 (by rfl) ⟨1764962, by rfl⟩ : syracuseStep 2353283 = 3529925) B3529925
theorem B2091185 : Blo 928581 2091185 := bstep (se 2 (by rfl) ⟨784194, by rfl⟩ : syracuseStep 2091185 = 1568389) B1568389
theorem B2091203 : Blo 928581 2091203 := bstep (se 1 (by rfl) ⟨1568402, by rfl⟩ : syracuseStep 2091203 = 3136805) B3136805
theorem B6711493 : Blo 928581 6711493 := bstep (se 4 (by rfl) ⟨629202, by rfl⟩ : syracuseStep 6711493 = 1258405) B1258405
theorem B2975953 : Blo 928581 2975953 := bstep (se 2 (by rfl) ⟨1115982, by rfl⟩ : syracuseStep 2975953 = 2231965) B2231965
theorem B1763633 : Blo 928581 1763633 := bstep (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) B1322725
theorem B2353475 : Blo 928581 2353475 := bstep (se 1 (by rfl) ⟨1765106, by rfl⟩ : syracuseStep 2353475 = 3530213) B3530213
theorem B1567073 : Blo 928581 1567073 := bstep (se 2 (by rfl) ⟨587652, by rfl⟩ : syracuseStep 1567073 = 1175305) B1175305
theorem B3140045 : Blo 928581 3140045 := bstep (se 3 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 3140045 = 1177517) B1177517
theorem B2091473 : Blo 928581 2091473 := bstep (se 2 (by rfl) ⟨784302, by rfl⟩ : syracuseStep 2091473 = 1568605) B1568605
theorem B1567201 : Blo 928581 1567201 := bstep (se 2 (by rfl) ⟨587700, by rfl⟩ : syracuseStep 1567201 = 1175401) B1175401
theorem B2091491 : Blo 928581 2091491 := bstep (se 1 (by rfl) ⟨1568618, by rfl⟩ : syracuseStep 2091491 = 3137237) B3137237
theorem B1436161 : Blo 928581 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B1567235 : Blo 928581 1567235 := bstep (se 1 (by rfl) ⟨1175426, by rfl⟩ : syracuseStep 1567235 = 2350853) B2350853
theorem B3140099 : Blo 928581 3140099 := bstep (se 1 (by rfl) ⟨2355074, by rfl⟩ : syracuseStep 3140099 = 4710149) B4710149
theorem B1567363 : Blo 928581 1567363 := bstep (se 1 (by rfl) ⟨1175522, by rfl⟩ : syracuseStep 1567363 = 2351045) B2351045
theorem B2091761 : Blo 928581 2091761 := bstep (se 2 (by rfl) ⟨784410, by rfl⟩ : syracuseStep 2091761 = 1568821) B1568821
theorem B2091779 : Blo 928581 2091779 := bstep (se 1 (by rfl) ⟨1568834, by rfl⟩ : syracuseStep 2091779 = 3137669) B3137669
theorem B1567505 : Blo 928581 1567505 := bstep (se 2 (by rfl) ⟨587814, by rfl⟩ : syracuseStep 1567505 = 1175629) B1175629
theorem B3140369 : Blo 928581 3140369 := bstep (se 2 (by rfl) ⟨1177638, by rfl⟩ : syracuseStep 3140369 = 2355277) B2355277
theorem B3533645 : Blo 928581 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B1567633 : Blo 928581 1567633 := bstep (se 2 (by rfl) ⟨587862, by rfl⟩ : syracuseStep 1567633 = 1175725) B1175725
theorem B1567667 : Blo 928581 1567667 := bstep (se 1 (by rfl) ⟨1175750, by rfl⟩ : syracuseStep 1567667 = 2351501) B2351501
theorem B1764355 : Blo 928581 1764355 := bstep (se 1 (by rfl) ⟨1323266, by rfl⟩ : syracuseStep 1764355 = 2646533) B2646533
theorem B2092049 : Blo 928581 2092049 := bstep (se 2 (by rfl) ⟨784518, by rfl⟩ : syracuseStep 2092049 = 1569037) B1569037
theorem B2092067 : Blo 928581 2092067 := bstep (se 1 (by rfl) ⟨1569050, by rfl⟩ : syracuseStep 2092067 = 3138101) B3138101
theorem B1567795 : Blo 928581 1567795 := bstep (se 1 (by rfl) ⟨1175846, by rfl⟩ : syracuseStep 1567795 = 2351693) B2351693
theorem B1567937 : Blo 928581 1567937 := bstep (se 2 (by rfl) ⟨587976, by rfl⟩ : syracuseStep 1567937 = 1175953) B1175953
theorem B13429957 : Blo 928581 13429957 := bstep (se 4 (by rfl) ⟨1259058, by rfl⟩ : syracuseStep 13429957 = 2518117) B2518117
theorem B2354417 : Blo 928581 2354417 := bstep (se 2 (by rfl) ⟨882906, by rfl⟩ : syracuseStep 2354417 = 1765813) B1765813
theorem B4713713 : Blo 928581 4713713 := bstep (se 2 (by rfl) ⟨1767642, by rfl⟩ : syracuseStep 4713713 = 3535285) B3535285
theorem B2354467 : Blo 928581 2354467 := bstep (se 1 (by rfl) ⟨1765850, by rfl⟩ : syracuseStep 2354467 = 3531701) B3531701
theorem B3140909 : Blo 928581 3140909 := bstep (se 3 (by rfl) ⟨588920, by rfl⟩ : syracuseStep 3140909 = 1177841) B1177841
theorem B2092337 : Blo 928581 2092337 := bstep (se 2 (by rfl) ⟨784626, by rfl⟩ : syracuseStep 2092337 = 1569253) B1569253
theorem B1568065 : Blo 928581 1568065 := bstep (se 2 (by rfl) ⟨588024, by rfl⟩ : syracuseStep 1568065 = 1176049) B1176049
theorem B2092355 : Blo 928581 2092355 := bstep (se 1 (by rfl) ⟨1569266, by rfl⟩ : syracuseStep 2092355 = 3138533) B3138533
theorem B3140963 : Blo 928581 3140963 := bstep (se 1 (by rfl) ⟨2355722, by rfl⟩ : syracuseStep 3140963 = 4711445) B4711445
theorem B11300195 : Blo 928581 11300195 := bstep (se 1 (by rfl) ⟨8475146, by rfl⟩ : syracuseStep 11300195 = 16950293) B16950293
theorem B1568099 : Blo 928581 1568099 := bstep (se 1 (by rfl) ⟨1176074, by rfl⟩ : syracuseStep 1568099 = 2352149) B2352149
theorem B2354609 : Blo 928581 2354609 := bstep (se 2 (by rfl) ⟨882978, by rfl⟩ : syracuseStep 2354609 = 1765957) B1765957
theorem B1764803 : Blo 928581 1764803 := bstep (se 1 (by rfl) ⟨1323602, by rfl⟩ : syracuseStep 1764803 = 2647205) B2647205
theorem B1568227 : Blo 928581 1568227 := bstep (se 1 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 1568227 = 2352341) B2352341
theorem B2092625 : Blo 928581 2092625 := bstep (se 2 (by rfl) ⟨784734, by rfl⟩ : syracuseStep 2092625 = 1569469) B1569469
theorem B2092643 : Blo 928581 2092643 := bstep (se 1 (by rfl) ⟨1569482, by rfl⟩ : syracuseStep 2092643 = 3138965) B3138965
theorem B1568369 : Blo 928581 1568369 := bstep (se 2 (by rfl) ⟨588138, by rfl⟩ : syracuseStep 1568369 = 1176277) B1176277
theorem B3141233 : Blo 928581 3141233 := bstep (se 2 (by rfl) ⟨1177962, by rfl⟩ : syracuseStep 3141233 = 2355925) B2355925
theorem B1765091 : Blo 928581 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B15920867 : Blo 928581 15920867 := bstep (se 1 (by rfl) ⟨11940650, by rfl⟩ : syracuseStep 15920867 = 23881301) B23881301
theorem B1568497 : Blo 928581 1568497 := bstep (se 2 (by rfl) ⟨588186, by rfl⟩ : syracuseStep 1568497 = 1176373) B1176373
theorem B1568531 : Blo 928581 1568531 := bstep (se 1 (by rfl) ⟨1176398, by rfl⟩ : syracuseStep 1568531 = 2352797) B2352797
theorem B2649905 : Blo 928581 2649905 := bstep (se 2 (by rfl) ⟨993714, by rfl⟩ : syracuseStep 2649905 = 1987429) B1987429
theorem B5304113 : Blo 928581 5304113 := bstep (se 2 (by rfl) ⟨1989042, by rfl⟩ : syracuseStep 5304113 = 3978085) B3978085
theorem B5959493 : Blo 928581 5959493 := bstep (se 4 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 5959493 = 1117405) B1117405
theorem B2092913 : Blo 928581 2092913 := bstep (se 2 (by rfl) ⟨784842, by rfl⟩ : syracuseStep 2092913 = 1569685) B1569685
theorem B2518897 : Blo 928581 2518897 := bstep (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) B1889173
theorem B1175411 : Blo 928581 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B2092931 : Blo 928581 2092931 := bstep (se 1 (by rfl) ⟨1569698, by rfl⟩ : syracuseStep 2092931 = 3139397) B3139397
theorem B1568659 : Blo 928581 1568659 := bstep (se 1 (by rfl) ⟨1176494, by rfl⟩ : syracuseStep 1568659 = 2352989) B2352989
theorem B2650097 : Blo 928581 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B1568801 : Blo 928581 1568801 := bstep (se 2 (by rfl) ⟨588300, by rfl⟩ : syracuseStep 1568801 = 1176601) B1176601
theorem B19132469 : Blo 928581 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B3141773 : Blo 928581 3141773 := bstep (se 3 (by rfl) ⟨589082, by rfl⟩ : syracuseStep 3141773 = 1178165) B1178165
theorem B2093201 : Blo 928581 2093201 := bstep (se 2 (by rfl) ⟨784950, by rfl⟩ : syracuseStep 2093201 = 1569901) B1569901
theorem B1568929 : Blo 928581 1568929 := bstep (se 2 (by rfl) ⟨588348, by rfl⟩ : syracuseStep 1568929 = 1176697) B1176697
theorem B2093219 : Blo 928581 2093219 := bstep (se 1 (by rfl) ⟨1569914, by rfl⟩ : syracuseStep 2093219 = 3139829) B3139829
theorem B1568963 : Blo 928581 1568963 := bstep (se 1 (by rfl) ⟨1176722, by rfl⟩ : syracuseStep 1568963 = 2353445) B2353445
theorem B3141827 : Blo 928581 3141827 := bstep (se 1 (by rfl) ⟨2356370, by rfl⟩ : syracuseStep 3141827 = 4712741) B4712741
theorem B1700131 : Blo 928581 1700131 := bstep (se 1 (by rfl) ⟨1275098, by rfl⟩ : syracuseStep 1700131 = 2550197) B2550197
theorem B1044787 : Blo 928581 1044787 := bstep (se 1 (by rfl) ⟨783590, by rfl⟩ : syracuseStep 1044787 = 1567181) B1567181
theorem B1569091 : Blo 928581 1569091 := bstep (se 1 (by rfl) ⟨1176818, by rfl⟩ : syracuseStep 1569091 = 2353637) B2353637
theorem B2355601 : Blo 928581 2355601 := bstep (se 2 (by rfl) ⟨883350, by rfl⟩ : syracuseStep 2355601 = 1766701) B1766701
theorem B2093489 : Blo 928581 2093489 := bstep (se 2 (by rfl) ⟨785058, by rfl⟩ : syracuseStep 2093489 = 1570117) B1570117
theorem B1044931 : Blo 928581 1044931 := bstep (se 1 (by rfl) ⟨783698, by rfl⟩ : syracuseStep 1044931 = 1567397) B1567397
theorem B2093507 : Blo 928581 2093507 := bstep (se 1 (by rfl) ⟨1570130, by rfl⟩ : syracuseStep 2093507 = 3140261) B3140261
theorem B1569233 : Blo 928581 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B3142097 : Blo 928581 3142097 := bstep (se 2 (by rfl) ⟨1178286, by rfl⟩ : syracuseStep 3142097 = 2356573) B2356573
theorem B1176115 : Blo 928581 1176115 := bstep (se 1 (by rfl) ⟨882086, by rfl⟩ : syracuseStep 1176115 = 1764173) B1764173
theorem B1569361 : Blo 928581 1569361 := bstep (se 2 (by rfl) ⟨588510, by rfl⟩ : syracuseStep 1569361 = 1177021) B1177021
theorem B1045075 : Blo 928581 1045075 := bstep (se 1 (by rfl) ⟨783806, by rfl⟩ : syracuseStep 1045075 = 1567613) B1567613
theorem B1569395 : Blo 928581 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B1766033 : Blo 928581 1766033 := bstep (se 2 (by rfl) ⟨662262, by rfl⟩ : syracuseStep 1766033 = 1324525) B1324525
theorem B1176211 : Blo 928581 1176211 := bstep (se 1 (by rfl) ⟨882158, by rfl⟩ : syracuseStep 1176211 = 1764317) B1764317
theorem B2355875 : Blo 928581 2355875 := bstep (se 1 (by rfl) ⟨1766906, by rfl⟩ : syracuseStep 2355875 = 3533813) B3533813
theorem B4715171 : Blo 928581 4715171 := bstep (se 1 (by rfl) ⟨3536378, by rfl⟩ : syracuseStep 4715171 = 7072757) B7072757
theorem B2093777 : Blo 928581 2093777 := bstep (se 2 (by rfl) ⟨785166, by rfl⟩ : syracuseStep 2093777 = 1570333) B1570333
theorem B1045219 : Blo 928581 1045219 := bstep (se 1 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 1045219 = 1567829) B1567829
theorem B2093795 : Blo 928581 2093795 := bstep (se 1 (by rfl) ⟨1570346, by rfl⟩ : syracuseStep 2093795 = 3140693) B3140693
theorem B1569523 : Blo 928581 1569523 := bstep (se 1 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 1569523 = 2354285) B2354285
theorem B2356067 : Blo 928581 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B1045363 : Blo 928581 1045363 := bstep (se 1 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 1045363 = 1568045) B1568045
theorem B1569665 : Blo 928581 1569665 := bstep (se 2 (by rfl) ⟨588624, by rfl⟩ : syracuseStep 1569665 = 1177249) B1177249
theorem B3535757 : Blo 928581 3535757 := bstep (se 3 (by rfl) ⟨662954, by rfl⟩ : syracuseStep 3535757 = 1325909) B1325909
theorem B7074701 : Blo 928581 7074701 := bstep (se 3 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 7074701 = 2653013) B2653013
theorem B2683853 : Blo 928581 2683853 := bstep (se 3 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 2683853 = 1006445) B1006445
theorem B2651089 : Blo 928581 2651089 := bstep (se 2 (by rfl) ⟨994158, by rfl⟩ : syracuseStep 2651089 = 1988317) B1988317
theorem B3142637 : Blo 928581 3142637 := bstep (se 3 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 3142637 = 1178489) B1178489
theorem B2978797 : Blo 928581 2978797 := bstep (se 3 (by rfl) ⟨558524, by rfl⟩ : syracuseStep 2978797 = 1117049) B1117049
theorem B2094065 : Blo 928581 2094065 := bstep (se 2 (by rfl) ⟨785274, by rfl⟩ : syracuseStep 2094065 = 1570549) B1570549
theorem B1569793 : Blo 928581 1569793 := bstep (se 2 (by rfl) ⟨588672, by rfl⟩ : syracuseStep 1569793 = 1177345) B1177345
theorem B1045507 : Blo 928581 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B2094083 : Blo 928581 2094083 := bstep (se 1 (by rfl) ⟨1570562, by rfl⟩ : syracuseStep 2094083 = 3141125) B3141125
theorem B3142691 : Blo 928581 3142691 := bstep (se 1 (by rfl) ⟨2357018, by rfl⟩ : syracuseStep 3142691 = 4714037) B4714037
theorem B1569827 : Blo 928581 1569827 := bstep (se 1 (by rfl) ⟨1177370, by rfl⟩ : syracuseStep 1569827 = 2354741) B2354741
theorem B1176707 : Blo 928581 1176707 := bstep (se 1 (by rfl) ⟨882530, by rfl⟩ : syracuseStep 1176707 = 1765061) B1765061
theorem B1045651 : Blo 928581 1045651 := bstep (se 1 (by rfl) ⟨784238, by rfl⟩ : syracuseStep 1045651 = 1568477) B1568477
theorem B1569955 : Blo 928581 1569955 := bstep (se 1 (by rfl) ⟨1177466, by rfl⟩ : syracuseStep 1569955 = 2354933) B2354933
theorem B6354125 : Blo 928581 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B2651363 : Blo 928581 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B5305571 : Blo 928581 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B2094353 : Blo 928581 2094353 := bstep (se 2 (by rfl) ⟨785382, by rfl⟩ : syracuseStep 2094353 = 1570765) B1570765
theorem B1045795 : Blo 928581 1045795 := bstep (se 1 (by rfl) ⟨784346, by rfl⟩ : syracuseStep 1045795 = 1568693) B1568693
theorem B2094371 : Blo 928581 2094371 := bstep (se 1 (by rfl) ⟨1570778, by rfl⟩ : syracuseStep 2094371 = 3141557) B3141557
theorem B1570097 : Blo 928581 1570097 := bstep (se 2 (by rfl) ⟨588786, by rfl⟩ : syracuseStep 1570097 = 1177573) B1177573
theorem B3142961 : Blo 928581 3142961 := bstep (se 2 (by rfl) ⟨1178610, by rfl⟩ : syracuseStep 3142961 = 2357221) B2357221
theorem B2651555 : Blo 928581 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B1570225 : Blo 928581 1570225 := bstep (se 2 (by rfl) ⟨588834, by rfl⟩ : syracuseStep 1570225 = 1177669) B1177669
theorem B2520497 : Blo 928581 2520497 := bstep (se 2 (by rfl) ⟨945186, by rfl⟩ : syracuseStep 2520497 = 1890373) B1890373
theorem B1045939 : Blo 928581 1045939 := bstep (se 1 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 1045939 = 1568909) B1568909
theorem B4715981 : Blo 928581 4715981 := bstep (se 3 (by rfl) ⟨884246, by rfl⟩ : syracuseStep 4715981 = 1768493) B1768493
theorem B1570259 : Blo 928581 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B1766929 : Blo 928581 1766929 := bstep (se 2 (by rfl) ⟨662598, by rfl⟩ : syracuseStep 1766929 = 1325197) B1325197
theorem B2094641 : Blo 928581 2094641 := bstep (se 2 (by rfl) ⟨785490, by rfl⟩ : syracuseStep 2094641 = 1570981) B1570981
theorem B1046083 : Blo 928581 1046083 := bstep (se 1 (by rfl) ⟨784562, by rfl⟩ : syracuseStep 1046083 = 1569125) B1569125
theorem B2094659 : Blo 928581 2094659 := bstep (se 1 (by rfl) ⟨1570994, by rfl⟩ : syracuseStep 2094659 = 3141989) B3141989
theorem B7960133 : Blo 928581 7960133 := bstep (se 4 (by rfl) ⟨746262, by rfl⟩ : syracuseStep 7960133 = 1492525) B1492525
theorem B1570387 : Blo 928581 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B1767089 : Blo 928581 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B3536561 : Blo 928581 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B1046227 : Blo 928581 1046227 := bstep (se 1 (by rfl) ⟨784670, by rfl⟩ : syracuseStep 1046227 = 1569341) B1569341
theorem B1570529 : Blo 928581 1570529 := bstep (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) B1177897
theorem B2357009 : Blo 928581 2357009 := bstep (se 2 (by rfl) ⟨883878, by rfl⟩ : syracuseStep 2357009 = 1767757) B1767757
theorem B1177411 : Blo 928581 1177411 := bstep (se 1 (by rfl) ⟨883058, by rfl⟩ : syracuseStep 1177411 = 1766117) B1766117
theorem B2357059 : Blo 928581 2357059 := bstep (se 1 (by rfl) ⟨1767794, by rfl⟩ : syracuseStep 2357059 = 3535589) B3535589
theorem B3143501 : Blo 928581 3143501 := bstep (se 3 (by rfl) ⟨589406, by rfl⟩ : syracuseStep 3143501 = 1178813) B1178813
theorem B2094929 : Blo 928581 2094929 := bstep (se 2 (by rfl) ⟨785598, by rfl⟩ : syracuseStep 2094929 = 1571197) B1571197
theorem B1570657 : Blo 928581 1570657 := bstep (se 2 (by rfl) ⟨588996, by rfl⟩ : syracuseStep 1570657 = 1177993) B1177993
theorem B1046371 : Blo 928581 1046371 := bstep (se 1 (by rfl) ⟨784778, by rfl⟩ : syracuseStep 1046371 = 1569557) B1569557
theorem B2094947 : Blo 928581 2094947 := bstep (se 1 (by rfl) ⟨1571210, by rfl⟩ : syracuseStep 2094947 = 3142421) B3142421
theorem B1570691 : Blo 928581 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B3143555 : Blo 928581 3143555 := bstep (se 1 (by rfl) ⟨2357666, by rfl⟩ : syracuseStep 3143555 = 4715333) B4715333
theorem B1177507 : Blo 928581 1177507 := bstep (se 1 (by rfl) ⟨883130, by rfl⟩ : syracuseStep 1177507 = 1766261) B1766261
theorem B2357201 : Blo 928581 2357201 := bstep (se 2 (by rfl) ⟨883950, by rfl⟩ : syracuseStep 2357201 = 1767901) B1767901
theorem B1046515 : Blo 928581 1046515 := bstep (se 1 (by rfl) ⟨784886, by rfl⟩ : syracuseStep 1046515 = 1569773) B1569773
theorem B1570819 : Blo 928581 1570819 := bstep (se 1 (by rfl) ⟨1178114, by rfl⟩ : syracuseStep 1570819 = 2356229) B2356229
theorem B1767491 : Blo 928581 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B2095217 : Blo 928581 2095217 := bstep (se 2 (by rfl) ⟨785706, by rfl⟩ : syracuseStep 2095217 = 1571413) B1571413
theorem B1046659 : Blo 928581 1046659 := bstep (se 1 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 1046659 = 1569989) B1569989
theorem B2095235 : Blo 928581 2095235 := bstep (se 1 (by rfl) ⟨1571426, by rfl⟩ : syracuseStep 2095235 = 3142853) B3142853
theorem B1570961 : Blo 928581 1570961 := bstep (se 2 (by rfl) ⟨589110, by rfl⟩ : syracuseStep 1570961 = 1178221) B1178221
theorem B3143825 : Blo 928581 3143825 := bstep (se 2 (by rfl) ⟨1178934, by rfl⟩ : syracuseStep 3143825 = 2357869) B2357869
theorem B2652365 : Blo 928581 2652365 := bstep (se 3 (by rfl) ⟨497318, by rfl⟩ : syracuseStep 2652365 = 994637) B994637
theorem B5306573 : Blo 928581 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B1571089 : Blo 928581 1571089 := bstep (se 2 (by rfl) ⟨589158, by rfl⟩ : syracuseStep 1571089 = 1178317) B1178317
theorem B1046803 : Blo 928581 1046803 := bstep (se 1 (by rfl) ⟨785102, by rfl⟩ : syracuseStep 1046803 = 1570205) B1570205
theorem B1571123 : Blo 928581 1571123 := bstep (se 1 (by rfl) ⟨1178342, by rfl⟩ : syracuseStep 1571123 = 2356685) B2356685
theorem B15890741 : Blo 928581 15890741 := bstep (se 5 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 15890741 = 1489757) B1489757
theorem B3537229 : Blo 928581 3537229 := bstep (se 3 (by rfl) ⟨663230, by rfl⟩ : syracuseStep 3537229 = 1326461) B1326461
theorem B2652547 : Blo 928581 2652547 := bstep (se 1 (by rfl) ⟨1989410, by rfl⟩ : syracuseStep 2652547 = 3978821) B3978821
theorem B2095505 : Blo 928581 2095505 := bstep (se 2 (by rfl) ⟨785814, by rfl⟩ : syracuseStep 2095505 = 1571629) B1571629
theorem B1178003 : Blo 928581 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B2980259 : Blo 928581 2980259 := bstep (se 1 (by rfl) ⟨2235194, by rfl⟩ : syracuseStep 2980259 = 4470389) B4470389
theorem B1046947 : Blo 928581 1046947 := bstep (se 1 (by rfl) ⟨785210, by rfl⟩ : syracuseStep 1046947 = 1570421) B1570421
theorem B2095523 : Blo 928581 2095523 := bstep (se 1 (by rfl) ⟨1571642, by rfl⟩ : syracuseStep 2095523 = 3143285) B3143285
theorem B1571251 : Blo 928581 1571251 := bstep (se 1 (by rfl) ⟨1178438, by rfl⟩ : syracuseStep 1571251 = 2356877) B2356877
theorem B1047091 : Blo 928581 1047091 := bstep (se 1 (by rfl) ⟨785318, by rfl⟩ : syracuseStep 1047091 = 1570637) B1570637
theorem B1571393 : Blo 928581 1571393 := bstep (se 2 (by rfl) ⟨589272, by rfl⟩ : syracuseStep 1571393 = 1178545) B1178545
theorem B3144365 : Blo 928581 3144365 := bstep (se 3 (by rfl) ⟨589568, by rfl⟩ : syracuseStep 3144365 = 1179137) B1179137
theorem B2095793 : Blo 928581 2095793 := bstep (se 2 (by rfl) ⟨785922, by rfl⟩ : syracuseStep 2095793 = 1571845) B1571845
theorem B1571521 : Blo 928581 1571521 := bstep (se 2 (by rfl) ⟨589320, by rfl⟩ : syracuseStep 1571521 = 1178641) B1178641
theorem B1047235 : Blo 928581 1047235 := bstep (se 1 (by rfl) ⟨785426, by rfl⟩ : syracuseStep 1047235 = 1570853) B1570853
theorem B2095811 : Blo 928581 2095811 := bstep (se 1 (by rfl) ⟨1571858, by rfl⟩ : syracuseStep 2095811 = 3143717) B3143717
theorem B1571555 : Blo 928581 1571555 := bstep (se 1 (by rfl) ⟨1178666, by rfl⟩ : syracuseStep 1571555 = 2357333) B2357333
theorem B3144419 : Blo 928581 3144419 := bstep (se 1 (by rfl) ⟨2358314, by rfl⟩ : syracuseStep 3144419 = 4716629) B4716629
theorem B1047379 : Blo 928581 1047379 := bstep (se 1 (by rfl) ⟨785534, by rfl⟩ : syracuseStep 1047379 = 1571069) B1571069
theorem B1571683 : Blo 928581 1571683 := bstep (se 1 (by rfl) ⟨1178762, by rfl⟩ : syracuseStep 1571683 = 2357525) B2357525
theorem B2653037 : Blo 928581 2653037 := bstep (se 3 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 2653037 = 994889) B994889
theorem B2390897 : Blo 928581 2390897 := bstep (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) B1793173
theorem B2358193 : Blo 928581 2358193 := bstep (se 2 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 2358193 = 1768645) B1768645
theorem B1768387 : Blo 928581 1768387 := bstep (se 1 (by rfl) ⟨1326290, by rfl⟩ : syracuseStep 1768387 = 2652581) B2652581
theorem B2096081 : Blo 928581 2096081 := bstep (se 2 (by rfl) ⟨786030, by rfl⟩ : syracuseStep 2096081 = 1572061) B1572061
theorem B1047523 : Blo 928581 1047523 := bstep (se 1 (by rfl) ⟨785642, by rfl⟩ : syracuseStep 1047523 = 1571285) B1571285
theorem B2096099 : Blo 928581 2096099 := bstep (se 1 (by rfl) ⟨1572074, by rfl⟩ : syracuseStep 2096099 = 3144149) B3144149
theorem B1571825 : Blo 928581 1571825 := bstep (se 2 (by rfl) ⟨589434, by rfl⟩ : syracuseStep 1571825 = 1178869) B1178869
theorem B3144689 : Blo 928581 3144689 := bstep (se 2 (by rfl) ⟨1179258, by rfl⟩ : syracuseStep 3144689 = 2358517) B2358517
theorem B1178707 : Blo 928581 1178707 := bstep (se 1 (by rfl) ⟨884030, by rfl⟩ : syracuseStep 1178707 = 1768061) B1768061
theorem B1768547 : Blo 928581 1768547 := bstep (se 1 (by rfl) ⟨1326410, by rfl⟩ : syracuseStep 1768547 = 2652821) B2652821
theorem B3538019 : Blo 928581 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B1571953 : Blo 928581 1571953 := bstep (se 2 (by rfl) ⟨589482, by rfl⟩ : syracuseStep 1571953 = 1178965) B1178965
theorem B1047667 : Blo 928581 1047667 := bstep (se 1 (by rfl) ⟨785750, by rfl⟩ : syracuseStep 1047667 = 1571501) B1571501
theorem B1571987 : Blo 928581 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B1178803 : Blo 928581 1178803 := bstep (se 1 (by rfl) ⟨884102, by rfl⟩ : syracuseStep 1178803 = 1768205) B1768205
theorem B2358467 : Blo 928581 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B3177677 : Blo 928581 3177677 := bstep (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) B1191629
theorem B2096369 : Blo 928581 2096369 := bstep (se 2 (by rfl) ⟨786138, by rfl⟩ : syracuseStep 2096369 = 1572277) B1572277
theorem B1047811 : Blo 928581 1047811 := bstep (se 1 (by rfl) ⟨785858, by rfl⟩ : syracuseStep 1047811 = 1571717) B1571717
theorem B2096387 : Blo 928581 2096387 := bstep (se 1 (by rfl) ⟨1572290, by rfl⟩ : syracuseStep 2096387 = 3144581) B3144581
theorem B1572115 : Blo 928581 1572115 := bstep (se 1 (by rfl) ⟨1179086, by rfl⟩ : syracuseStep 1572115 = 2358173) B2358173
theorem B9567557 : Blo 928581 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B2358659 : Blo 928581 2358659 := bstep (se 1 (by rfl) ⟨1768994, by rfl⟩ : syracuseStep 2358659 = 3537989) B3537989
theorem B1047955 : Blo 928581 1047955 := bstep (se 1 (by rfl) ⟨785966, by rfl⟩ : syracuseStep 1047955 = 1571933) B1571933
theorem B1572257 : Blo 928581 1572257 := bstep (se 2 (by rfl) ⟨589596, by rfl⟩ : syracuseStep 1572257 = 1179193) B1179193
theorem B3145229 : Blo 928581 3145229 := bstep (se 3 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 3145229 = 1179461) B1179461
theorem B2096657 : Blo 928581 2096657 := bstep (se 2 (by rfl) ⟨786246, by rfl⟩ : syracuseStep 2096657 = 1572493) B1572493
theorem B1572385 : Blo 928581 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B1048099 : Blo 928581 1048099 := bstep (se 1 (by rfl) ⟨786074, by rfl⟩ : syracuseStep 1048099 = 1572149) B1572149
theorem B2096675 : Blo 928581 2096675 := bstep (se 1 (by rfl) ⟨1572506, by rfl⟩ : syracuseStep 2096675 = 3145013) B3145013
theorem B1572419 : Blo 928581 1572419 := bstep (se 1 (by rfl) ⟨1179314, by rfl⟩ : syracuseStep 1572419 = 2358629) B2358629
theorem B3145283 : Blo 928581 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B10583621 : Blo 928581 10583621 := bstep (se 4 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 10583621 = 1984429) B1984429
theorem B1179299 : Blo 928581 1179299 := bstep (se 1 (by rfl) ⟨884474, by rfl⟩ : syracuseStep 1179299 = 1768949) B1768949
theorem B1048243 : Blo 928581 1048243 := bstep (se 1 (by rfl) ⟨786182, by rfl⟩ : syracuseStep 1048243 = 1572365) B1572365
theorem B1572547 : Blo 928581 1572547 := bstep (se 1 (by rfl) ⟨1179410, by rfl⟩ : syracuseStep 1572547 = 2358821) B2358821
theorem B3538673 : Blo 928581 3538673 := bstep (se 2 (by rfl) ⟨1327002, by rfl⟩ : syracuseStep 3538673 = 2654005) B2654005
theorem B7077617 : Blo 928581 7077617 := bstep (se 2 (by rfl) ⟨2654106, by rfl⟩ : syracuseStep 7077617 = 5308213) B5308213
theorem B2096945 : Blo 928581 2096945 := bstep (se 2 (by rfl) ⟨786354, by rfl⟩ : syracuseStep 2096945 = 1572709) B1572709
theorem B1048387 : Blo 928581 1048387 := bstep (se 1 (by rfl) ⟨786290, by rfl⟩ : syracuseStep 1048387 = 1572581) B1572581
theorem B2096963 : Blo 928581 2096963 := bstep (se 1 (by rfl) ⟨1572722, by rfl⟩ : syracuseStep 2096963 = 3145445) B3145445
theorem B1572689 : Blo 928581 1572689 := bstep (se 2 (by rfl) ⟨589758, by rfl⟩ : syracuseStep 1572689 = 1179517) B1179517
theorem B3145553 : Blo 928581 3145553 := bstep (se 2 (by rfl) ⟨1179582, by rfl⟩ : syracuseStep 3145553 = 2359165) B2359165
theorem B1572817 : Blo 928581 1572817 := bstep (se 2 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 1572817 = 1179613) B1179613
theorem B1048531 : Blo 928581 1048531 := bstep (se 1 (by rfl) ⟨786398, by rfl⟩ : syracuseStep 1048531 = 1572797) B1572797
theorem B2981873 : Blo 928581 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B1572851 : Blo 928581 1572851 := bstep (se 1 (by rfl) ⟨1179638, by rfl⟩ : syracuseStep 1572851 = 2359277) B2359277
theorem B3538961 : Blo 928581 3538961 := bstep (se 2 (by rfl) ⟨1327110, by rfl⟩ : syracuseStep 3538961 = 2654221) B2654221
theorem B15532067 : Blo 928581 15532067 := bstep (se 1 (by rfl) ⟨11649050, by rfl⟩ : syracuseStep 15532067 = 23298101) B23298101
theorem B2097305 : Blo 928581 2097305 := bstep (se 2 (by rfl) ⟨786489, by rfl⟩ : syracuseStep 2097305 = 1572979) B1572979
theorem B1048747 : Blo 928581 1048747 := bstep (se 1 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 1048747 = 1573121) B1573121
theorem B2359489 : Blo 928581 2359489 := bstep (se 2 (by rfl) ⟨884808, by rfl⟩ : syracuseStep 2359489 = 1769617) B1769617
theorem B3145931 : Blo 928581 3145931 := bstep (se 1 (by rfl) ⟨2359448, by rfl⟩ : syracuseStep 3145931 = 4718897) B4718897
theorem B1573067 : Blo 928581 1573067 := bstep (se 1 (by rfl) ⟨1179800, by rfl⟩ : syracuseStep 1573067 = 2359601) B2359601
theorem B2097395 : Blo 928581 2097395 := bstep (se 1 (by rfl) ⟨1573046, by rfl⟩ : syracuseStep 2097395 = 3146093) B3146093
theorem B2097431 : Blo 928581 2097431 := bstep (se 1 (by rfl) ⟨1573073, by rfl⟩ : syracuseStep 2097431 = 3146147) B3146147
theorem B1048855 : Blo 928581 1048855 := bstep (se 1 (by rfl) ⟨786641, by rfl⟩ : syracuseStep 1048855 = 1573283) B1573283
theorem B4784429 : Blo 928581 4784429 := bstep (se 3 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 4784429 = 1794161) B1794161
theorem B1573195 : Blo 928581 1573195 := bstep (se 1 (by rfl) ⟨1179896, by rfl⟩ : syracuseStep 1573195 = 2359793) B2359793
theorem B1769921 : Blo 928581 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B2097611 : Blo 928581 2097611 := bstep (se 1 (by rfl) ⟨1573208, by rfl⟩ : syracuseStep 2097611 = 3146417) B3146417
theorem B1049035 : Blo 928581 1049035 := bstep (se 1 (by rfl) ⟨786776, by rfl⟩ : syracuseStep 1049035 = 1573553) B1573553
theorem B3146201 : Blo 928581 3146201 := bstep (se 2 (by rfl) ⟨1179825, by rfl⟩ : syracuseStep 3146201 = 2359651) B2359651
theorem B1573337 : Blo 928581 1573337 := bstep (se 2 (by rfl) ⟨590001, by rfl⟩ : syracuseStep 1573337 = 1180003) B1180003
theorem B2097665 : Blo 928581 2097665 := bstep (se 2 (by rfl) ⟨786624, by rfl⟩ : syracuseStep 2097665 = 1573249) B1573249
theorem B60293645 : Blo 928581 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B1049143 : Blo 928581 1049143 := bstep (se 1 (by rfl) ⟨786857, by rfl⟩ : syracuseStep 1049143 = 1573715) B1573715
theorem B1573465 : Blo 928581 1573465 := bstep (se 2 (by rfl) ⟨590049, by rfl⟩ : syracuseStep 1573465 = 1180099) B1180099
theorem B3539659 : Blo 928581 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B1770187 : Blo 928581 1770187 := bstep (se 1 (by rfl) ⟨1327640, by rfl⟩ : syracuseStep 1770187 = 2655281) B2655281
theorem B2097881 : Blo 928581 2097881 := bstep (se 2 (by rfl) ⟨786705, by rfl⟩ : syracuseStep 2097881 = 1573411) B1573411
theorem B2360087 : Blo 928581 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B2097971 : Blo 928581 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B2098007 : Blo 928581 2098007 := bstep (se 1 (by rfl) ⟨1573505, by rfl⟩ : syracuseStep 2098007 = 3147011) B3147011
theorem B2655155 : Blo 928581 2655155 := bstep (se 1 (by rfl) ⟨1991366, by rfl⟩ : syracuseStep 2655155 = 3982733) B3982733
theorem B3539933 : Blo 928581 3539933 := bstep (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) B1327475
theorem B2098187 : Blo 928581 2098187 := bstep (se 1 (by rfl) ⟨1573640, by rfl⟩ : syracuseStep 2098187 = 3147281) B3147281
theorem B2098241 : Blo 928581 2098241 := bstep (se 2 (by rfl) ⟨786840, by rfl⟩ : syracuseStep 2098241 = 1573681) B1573681
theorem B3146903 : Blo 928581 3146903 := bstep (se 1 (by rfl) ⟨2360177, by rfl⟩ : syracuseStep 3146903 = 4720355) B4720355
theorem B3769523 : Blo 928581 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B13600099 : Blo 928581 13600099 := bstep (se 1 (by rfl) ⟨10200074, by rfl⟩ : syracuseStep 13600099 = 20400149) B20400149
theorem B8488397 : Blo 928581 8488397 := bstep (se 3 (by rfl) ⟨1591574, by rfl⟩ : syracuseStep 8488397 = 3183149) B3183149
theorem B4720193 : Blo 928581 4720193 := bstep (se 2 (by rfl) ⟨1770072, by rfl⟩ : syracuseStep 4720193 = 3540145) B3540145
theorem B2983513 : Blo 928581 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B3540631 : Blo 928581 3540631 := bstep (se 1 (by rfl) ⟨2655473, by rfl⟩ : syracuseStep 3540631 = 5310947) B5310947
theorem B3147443 : Blo 928581 3147443 := bstep (se 1 (by rfl) ⟨2360582, by rfl⟩ : syracuseStep 3147443 = 4721165) B4721165
theorem B1115915 : Blo 928581 1115915 := bstep (se 1 (by rfl) ⟨836936, by rfl⟩ : syracuseStep 1115915 = 1673873) B1673873
theorem B1836875 : Blo 928581 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B30214295 : Blo 928581 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B15895115 : Blo 928581 15895115 := bstep (se 1 (by rfl) ⟨11921336, by rfl⟩ : syracuseStep 15895115 = 23842673) B23842673
theorem B8948657 : Blo 928581 8948657 := bstep (se 2 (by rfl) ⟨3355746, by rfl⟩ : syracuseStep 8948657 = 6711493) B6711493
theorem B3967937 : Blo 928581 3967937 := bstep (se 2 (by rfl) ⟨1487976, by rfl⟩ : syracuseStep 3967937 = 2975953) B2975953
theorem B1674263 : Blo 928581 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B8490257 : Blo 928581 8490257 := bstep (se 2 (by rfl) ⟨3183846, by rfl⟩ : syracuseStep 8490257 = 6367693) B6367693
theorem B13438385 : Blo 928581 13438385 := bstep (se 2 (by rfl) ⟨5039394, by rfl⟩ : syracuseStep 13438385 = 10078789) B10078789
theorem B17010137 : Blo 928581 17010137 := bstep (se 2 (by rfl) ⟨6378801, by rfl⟩ : syracuseStep 17010137 = 12757603) B12757603
theorem B5967539 : Blo 928581 5967539 := bstep (se 1 (by rfl) ⟨4475654, by rfl⟩ : syracuseStep 5967539 = 8951309) B8951309
theorem B2985665 : Blo 928581 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B3772183 : Blo 928581 3772183 := bstep (se 1 (by rfl) ⟨2829137, by rfl⟩ : syracuseStep 3772183 = 5658275) B5658275
theorem B6721325 : Blo 928581 6721325 := bstep (se 3 (by rfl) ⟨1260248, by rfl⟩ : syracuseStep 6721325 = 2520497) B2520497
theorem B22646627 : Blo 928581 22646627 := bstep (se 1 (by rfl) ⟨16984970, by rfl⟩ : syracuseStep 22646627 = 33969941) B33969941
theorem B3772505 : Blo 928581 3772505 := bstep (se 2 (by rfl) ⟨1414689, by rfl⟩ : syracuseStep 3772505 = 2829379) B2829379
theorem B2756915 : Blo 928581 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B3772765 : Blo 928581 3772765 := bstep (se 3 (by rfl) ⟨707393, by rfl⟩ : syracuseStep 3772765 = 1414787) B1414787
theorem B3969611 : Blo 928581 3969611 := bstep (se 1 (by rfl) ⟨2977208, by rfl⟩ : syracuseStep 3969611 = 5954417) B5954417
theorem B5378653 : Blo 928581 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B11342429 : Blo 928581 11342429 := bstep (se 3 (by rfl) ⟨2126705, by rfl⟩ : syracuseStep 11342429 = 4253411) B4253411
theorem B3970397 : Blo 928581 3970397 := bstep (se 3 (by rfl) ⟨744449, by rfl⟩ : syracuseStep 3970397 = 1488899) B1488899
theorem B3347905 : Blo 928581 3347905 := bstep (se 2 (by rfl) ⟨1255464, by rfl⟩ : syracuseStep 3347905 = 2510929) B2510929
theorem B1414667 : Blo 928581 1414667 := bstep (se 1 (by rfl) ⟨1061000, by rfl⟩ : syracuseStep 1414667 = 2122001) B2122001
theorem B1676951 : Blo 928581 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B8165069 : Blo 928581 8165069 := bstep (se 3 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 8165069 = 3061901) B3061901
theorem B2266841 : Blo 928581 2266841 := bstep (se 2 (by rfl) ⟨850065, by rfl⟩ : syracuseStep 2266841 = 1700131) B1700131
theorem B3184535 : Blo 928581 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B11606051 : Blo 928581 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B7346477 : Blo 928581 7346477 := bstep (se 3 (by rfl) ⟨1377464, by rfl⟩ : syracuseStep 7346477 = 2754929) B2754929
theorem B1677953 : Blo 928581 1677953 := bstep (se 2 (by rfl) ⟨629232, by rfl⟩ : syracuseStep 1677953 = 1258465) B1258465
theorem B3971729 : Blo 928581 3971729 := bstep (se 2 (by rfl) ⟨1489398, by rfl⟩ : syracuseStep 3971729 = 2978797) B2978797
theorem B1514137 : Blo 928581 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B2235097 : Blo 928581 2235097 := bstep (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) B1676323
theorem B2235329 : Blo 928581 2235329 := bstep (se 2 (by rfl) ⟨838248, by rfl⟩ : syracuseStep 2235329 = 1676497) B1676497
theorem B4037597 : Blo 928581 4037597 := bstep (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) B1514099
theorem B3349763 : Blo 928581 3349763 := bstep (se 1 (by rfl) ⟨2512322, by rfl⟩ : syracuseStep 3349763 = 5024645) B5024645
theorem B1908569 : Blo 928581 1908569 := bstep (se 2 (by rfl) ⟨715713, by rfl⟩ : syracuseStep 1908569 = 1431427) B1431427
theorem B3972995 : Blo 928581 3972995 := bstep (se 1 (by rfl) ⟨2979746, by rfl⟩ : syracuseStep 3972995 = 5959493) B5959493
theorem B7053317 : Blo 928581 7053317 := bstep (se 4 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 7053317 = 1322497) B1322497
theorem B12754979 : Blo 928581 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B3350801 : Blo 928581 3350801 := bstep (se 2 (by rfl) ⟨1256550, by rfl⟩ : syracuseStep 3350801 = 2513101) B2513101
theorem B4236083 : Blo 928581 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B5383091 : Blo 928581 5383091 := bstep (se 1 (by rfl) ⟨4037318, by rfl⟩ : syracuseStep 5383091 = 8074637) B8074637
theorem B3351725 : Blo 928581 3351725 := bstep (se 3 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 3351725 = 1256897) B1256897
theorem B992471 : Blo 928581 992471 := bstep (se 1 (by rfl) ⟨744353, by rfl⟩ : syracuseStep 992471 = 1488707) B1488707
theorem B10593827 : Blo 928581 10593827 := bstep (se 1 (by rfl) ⟨7945370, by rfl⟩ : syracuseStep 10593827 = 15890741) B15890741
theorem B1255513 : Blo 928581 1255513 := bstep (se 2 (by rfl) ⟨470817, by rfl⟩ : syracuseStep 1255513 = 941635) B941635
theorem B7055747 : Blo 928581 7055747 := bstep (se 1 (by rfl) ⟨5291810, by rfl⟩ : syracuseStep 7055747 = 10583621) B10583621
theorem B928587 : Blo 928581 928587 := bstep (se 1 (by rfl) ⟨696440, by rfl⟩ : syracuseStep 928587 = 1392881) B1392881
theorem B928599 : Blo 928581 928599 := bstep (se 1 (by rfl) ⟨696449, by rfl⟩ : syracuseStep 928599 = 1392899) B1392899
theorem B928619 : Blo 928581 928619 := bstep (se 1 (by rfl) ⟨696464, by rfl⟩ : syracuseStep 928619 = 1392929) B1392929
theorem B928631 : Blo 928581 928631 := bstep (se 1 (by rfl) ⟨696473, by rfl⟩ : syracuseStep 928631 = 1392947) B1392947
theorem B928651 : Blo 928581 928651 := bstep (se 1 (by rfl) ⟨696488, by rfl⟩ : syracuseStep 928651 = 1392977) B1392977
theorem B928663 : Blo 928581 928663 := bstep (se 1 (by rfl) ⟨696497, by rfl⟩ : syracuseStep 928663 = 1392995) B1392995
theorem B3976087 : Blo 928581 3976087 := bstep (se 1 (by rfl) ⟨2982065, by rfl⟩ : syracuseStep 3976087 = 5964131) B5964131
theorem B928683 : Blo 928581 928683 := bstep (se 1 (by rfl) ⟨696512, by rfl⟩ : syracuseStep 928683 = 1393025) B1393025
theorem B928695 : Blo 928581 928695 := bstep (se 1 (by rfl) ⟨696521, by rfl⟩ : syracuseStep 928695 = 1393043) B1393043
theorem B994231 : Blo 928581 994231 := bstep (se 1 (by rfl) ⟨745673, by rfl⟩ : syracuseStep 994231 = 1491347) B1491347
theorem B928715 : Blo 928581 928715 := bstep (se 1 (by rfl) ⟨696536, by rfl⟩ : syracuseStep 928715 = 1393073) B1393073
theorem B1616843 : Blo 928581 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B928727 : Blo 928581 928727 := bstep (se 1 (by rfl) ⟨696545, by rfl⟩ : syracuseStep 928727 = 1393091) B1393091
theorem B928747 : Blo 928581 928747 := bstep (se 1 (by rfl) ⟨696560, by rfl⟩ : syracuseStep 928747 = 1393121) B1393121
theorem B928759 : Blo 928581 928759 := bstep (se 1 (by rfl) ⟨696569, by rfl⟩ : syracuseStep 928759 = 1393139) B1393139
theorem B928779 : Blo 928581 928779 := bstep (se 1 (by rfl) ⟨696584, by rfl⟩ : syracuseStep 928779 = 1393169) B1393169
theorem B928791 : Blo 928581 928791 := bstep (se 1 (by rfl) ⟨696593, by rfl⟩ : syracuseStep 928791 = 1393187) B1393187
theorem B928811 : Blo 928581 928811 := bstep (se 1 (by rfl) ⟨696608, by rfl⟩ : syracuseStep 928811 = 1393217) B1393217
theorem B928823 : Blo 928581 928823 := bstep (se 1 (by rfl) ⟨696617, by rfl⟩ : syracuseStep 928823 = 1393235) B1393235
theorem B928843 : Blo 928581 928843 := bstep (se 1 (by rfl) ⟨696632, by rfl⟩ : syracuseStep 928843 = 1393265) B1393265
theorem B928855 : Blo 928581 928855 := bstep (se 1 (by rfl) ⟨696641, by rfl⟩ : syracuseStep 928855 = 1393283) B1393283
theorem B928875 : Blo 928581 928875 := bstep (se 1 (by rfl) ⟨696656, by rfl⟩ : syracuseStep 928875 = 1393313) B1393313
theorem B928887 : Blo 928581 928887 := bstep (se 1 (by rfl) ⟨696665, by rfl⟩ : syracuseStep 928887 = 1393331) B1393331
theorem B928907 : Blo 928581 928907 := bstep (se 1 (by rfl) ⟨696680, by rfl⟩ : syracuseStep 928907 = 1393361) B1393361
theorem B928919 : Blo 928581 928919 := bstep (se 1 (by rfl) ⟨696689, by rfl⟩ : syracuseStep 928919 = 1393379) B1393379
theorem B928939 : Blo 928581 928939 := bstep (se 1 (by rfl) ⟨696704, by rfl⟩ : syracuseStep 928939 = 1393409) B1393409
theorem B928951 : Blo 928581 928951 := bstep (se 1 (by rfl) ⟨696713, by rfl⟩ : syracuseStep 928951 = 1393427) B1393427
theorem B928971 : Blo 928581 928971 := bstep (se 1 (by rfl) ⟨696728, by rfl⟩ : syracuseStep 928971 = 1393457) B1393457
theorem B928983 : Blo 928581 928983 := bstep (se 1 (by rfl) ⟨696737, by rfl⟩ : syracuseStep 928983 = 1393475) B1393475
theorem B1322201 : Blo 928581 1322201 := bstep (se 2 (by rfl) ⟨495825, by rfl⟩ : syracuseStep 1322201 = 991651) B991651
theorem B929003 : Blo 928581 929003 := bstep (se 1 (by rfl) ⟨696752, by rfl⟩ : syracuseStep 929003 = 1393505) B1393505
theorem B929015 : Blo 928581 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B929035 : Blo 928581 929035 := bstep (se 1 (by rfl) ⟨696776, by rfl⟩ : syracuseStep 929035 = 1393553) B1393553
theorem B929047 : Blo 928581 929047 := bstep (se 1 (by rfl) ⟨696785, by rfl⟩ : syracuseStep 929047 = 1393571) B1393571
theorem B929067 : Blo 928581 929067 := bstep (se 1 (by rfl) ⟨696800, by rfl⟩ : syracuseStep 929067 = 1393601) B1393601
theorem B929079 : Blo 928581 929079 := bstep (se 1 (by rfl) ⟨696809, by rfl⟩ : syracuseStep 929079 = 1393619) B1393619
theorem B929099 : Blo 928581 929099 := bstep (se 1 (by rfl) ⟨696824, by rfl⟩ : syracuseStep 929099 = 1393649) B1393649
theorem B929111 : Blo 928581 929111 := bstep (se 1 (by rfl) ⟨696833, by rfl⟩ : syracuseStep 929111 = 1393667) B1393667
theorem B929131 : Blo 928581 929131 := bstep (se 1 (by rfl) ⟨696848, by rfl⟩ : syracuseStep 929131 = 1393697) B1393697
theorem B929143 : Blo 928581 929143 := bstep (se 1 (by rfl) ⟨696857, by rfl⟩ : syracuseStep 929143 = 1393715) B1393715
theorem B929163 : Blo 928581 929163 := bstep (se 1 (by rfl) ⟨696872, by rfl⟩ : syracuseStep 929163 = 1393745) B1393745
theorem B929175 : Blo 928581 929175 := bstep (se 1 (by rfl) ⟨696881, by rfl⟩ : syracuseStep 929175 = 1393763) B1393763
theorem B4238743 : Blo 928581 4238743 := bstep (se 1 (by rfl) ⟨3179057, by rfl⟩ : syracuseStep 4238743 = 6358115) B6358115
theorem B929195 : Blo 928581 929195 := bstep (se 1 (by rfl) ⟨696896, by rfl⟩ : syracuseStep 929195 = 1393793) B1393793
theorem B929207 : Blo 928581 929207 := bstep (se 1 (by rfl) ⟨696905, by rfl⟩ : syracuseStep 929207 = 1393811) B1393811
theorem B929227 : Blo 928581 929227 := bstep (se 1 (by rfl) ⟨696920, by rfl⟩ : syracuseStep 929227 = 1393841) B1393841
theorem B929239 : Blo 928581 929239 := bstep (se 1 (by rfl) ⟨696929, by rfl⟩ : syracuseStep 929239 = 1393859) B1393859
theorem B929259 : Blo 928581 929259 := bstep (se 1 (by rfl) ⟨696944, by rfl⟩ : syracuseStep 929259 = 1393889) B1393889
theorem B929271 : Blo 928581 929271 := bstep (se 1 (by rfl) ⟨696953, by rfl⟩ : syracuseStep 929271 = 1393907) B1393907
theorem B929291 : Blo 928581 929291 := bstep (se 1 (by rfl) ⟨696968, by rfl⟩ : syracuseStep 929291 = 1393937) B1393937
theorem B929303 : Blo 928581 929303 := bstep (se 1 (by rfl) ⟨696977, by rfl⟩ : syracuseStep 929303 = 1393955) B1393955
theorem B929323 : Blo 928581 929323 := bstep (se 1 (by rfl) ⟨696992, by rfl⟩ : syracuseStep 929323 = 1393985) B1393985
theorem B929335 : Blo 928581 929335 := bstep (se 1 (by rfl) ⟨697001, by rfl⟩ : syracuseStep 929335 = 1394003) B1394003
theorem B929355 : Blo 928581 929355 := bstep (se 1 (by rfl) ⟨697016, by rfl⟩ : syracuseStep 929355 = 1394033) B1394033
theorem B929367 : Blo 928581 929367 := bstep (se 1 (by rfl) ⟨697025, by rfl⟩ : syracuseStep 929367 = 1394051) B1394051
theorem B1257049 : Blo 928581 1257049 := bstep (se 2 (by rfl) ⟨471393, by rfl⟩ : syracuseStep 1257049 = 942787) B942787
theorem B929387 : Blo 928581 929387 := bstep (se 1 (by rfl) ⟨697040, by rfl⟩ : syracuseStep 929387 = 1394081) B1394081
theorem B929399 : Blo 928581 929399 := bstep (se 1 (by rfl) ⟨697049, by rfl⟩ : syracuseStep 929399 = 1394099) B1394099
theorem B929419 : Blo 928581 929419 := bstep (se 1 (by rfl) ⟨697064, by rfl⟩ : syracuseStep 929419 = 1394129) B1394129
theorem B929431 : Blo 928581 929431 := bstep (se 1 (by rfl) ⟨697073, by rfl⟩ : syracuseStep 929431 = 1394147) B1394147
theorem B929451 : Blo 928581 929451 := bstep (se 1 (by rfl) ⟨697088, by rfl⟩ : syracuseStep 929451 = 1394177) B1394177
theorem B929463 : Blo 928581 929463 := bstep (se 1 (by rfl) ⟨697097, by rfl⟩ : syracuseStep 929463 = 1394195) B1394195
theorem B929483 : Blo 928581 929483 := bstep (se 1 (by rfl) ⟨697112, by rfl⟩ : syracuseStep 929483 = 1394225) B1394225
theorem B929495 : Blo 928581 929495 := bstep (se 1 (by rfl) ⟨697121, by rfl⟩ : syracuseStep 929495 = 1394243) B1394243
theorem B929515 : Blo 928581 929515 := bstep (se 1 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 929515 = 1394273) B1394273
theorem B995051 : Blo 928581 995051 := bstep (se 1 (by rfl) ⟨746288, by rfl⟩ : syracuseStep 995051 = 1492577) B1492577
theorem B929527 : Blo 928581 929527 := bstep (se 1 (by rfl) ⟨697145, by rfl⟩ : syracuseStep 929527 = 1394291) B1394291
theorem B929547 : Blo 928581 929547 := bstep (se 1 (by rfl) ⟨697160, by rfl⟩ : syracuseStep 929547 = 1394321) B1394321
theorem B929559 : Blo 928581 929559 := bstep (se 1 (by rfl) ⟨697169, by rfl⟩ : syracuseStep 929559 = 1394339) B1394339
theorem B929579 : Blo 928581 929579 := bstep (se 1 (by rfl) ⟨697184, by rfl⟩ : syracuseStep 929579 = 1394369) B1394369
theorem B929591 : Blo 928581 929591 := bstep (se 1 (by rfl) ⟨697193, by rfl⟩ : syracuseStep 929591 = 1394387) B1394387
theorem B929611 : Blo 928581 929611 := bstep (se 1 (by rfl) ⟨697208, by rfl⟩ : syracuseStep 929611 = 1394417) B1394417
theorem B1322839 : Blo 928581 1322839 := bstep (se 1 (by rfl) ⟨992129, by rfl⟩ : syracuseStep 1322839 = 1984259) B1984259
theorem B929623 : Blo 928581 929623 := bstep (se 1 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 929623 = 1394435) B1394435
theorem B929643 : Blo 928581 929643 := bstep (se 1 (by rfl) ⟨697232, by rfl⟩ : syracuseStep 929643 = 1394465) B1394465
theorem B929655 : Blo 928581 929655 := bstep (se 1 (by rfl) ⟨697241, by rfl⟩ : syracuseStep 929655 = 1394483) B1394483
theorem B4534147 : Blo 928581 4534147 := bstep (se 1 (by rfl) ⟨3400610, by rfl⟩ : syracuseStep 4534147 = 6801221) B6801221
theorem B929675 : Blo 928581 929675 := bstep (se 1 (by rfl) ⟨697256, by rfl⟩ : syracuseStep 929675 = 1394513) B1394513
theorem B929687 : Blo 928581 929687 := bstep (se 1 (by rfl) ⟨697265, by rfl⟩ : syracuseStep 929687 = 1394531) B1394531
theorem B929707 : Blo 928581 929707 := bstep (se 1 (by rfl) ⟨697280, by rfl⟩ : syracuseStep 929707 = 1394561) B1394561
theorem B929719 : Blo 928581 929719 := bstep (se 1 (by rfl) ⟨697289, by rfl⟩ : syracuseStep 929719 = 1394579) B1394579
theorem B929739 : Blo 928581 929739 := bstep (se 1 (by rfl) ⟨697304, by rfl⟩ : syracuseStep 929739 = 1394609) B1394609
theorem B929751 : Blo 928581 929751 := bstep (se 1 (by rfl) ⟨697313, by rfl⟩ : syracuseStep 929751 = 1394627) B1394627
theorem B929771 : Blo 928581 929771 := bstep (se 1 (by rfl) ⟨697328, by rfl⟩ : syracuseStep 929771 = 1394657) B1394657
theorem B929783 : Blo 928581 929783 := bstep (se 1 (by rfl) ⟨697337, by rfl⟩ : syracuseStep 929783 = 1394675) B1394675
theorem B929803 : Blo 928581 929803 := bstep (se 1 (by rfl) ⟨697352, by rfl⟩ : syracuseStep 929803 = 1394705) B1394705
theorem B929815 : Blo 928581 929815 := bstep (se 1 (by rfl) ⟨697361, by rfl⟩ : syracuseStep 929815 = 1394723) B1394723
theorem B929835 : Blo 928581 929835 := bstep (se 1 (by rfl) ⟨697376, by rfl⟩ : syracuseStep 929835 = 1394753) B1394753
theorem B929847 : Blo 928581 929847 := bstep (se 1 (by rfl) ⟨697385, by rfl⟩ : syracuseStep 929847 = 1394771) B1394771
theorem B929867 : Blo 928581 929867 := bstep (se 1 (by rfl) ⟨697400, by rfl⟩ : syracuseStep 929867 = 1394801) B1394801
theorem B929879 : Blo 928581 929879 := bstep (se 1 (by rfl) ⟨697409, by rfl⟩ : syracuseStep 929879 = 1394819) B1394819
theorem B929899 : Blo 928581 929899 := bstep (se 1 (by rfl) ⟨697424, by rfl⟩ : syracuseStep 929899 = 1394849) B1394849
theorem B929911 : Blo 928581 929911 := bstep (se 1 (by rfl) ⟨697433, by rfl⟩ : syracuseStep 929911 = 1394867) B1394867
theorem B929931 : Blo 928581 929931 := bstep (se 1 (by rfl) ⟨697448, by rfl⟩ : syracuseStep 929931 = 1394897) B1394897
theorem B929943 : Blo 928581 929943 := bstep (se 1 (by rfl) ⟨697457, by rfl⟩ : syracuseStep 929943 = 1394915) B1394915
theorem B929963 : Blo 928581 929963 := bstep (se 1 (by rfl) ⟨697472, by rfl⟩ : syracuseStep 929963 = 1394945) B1394945
theorem B929975 : Blo 928581 929975 := bstep (se 1 (by rfl) ⟨697481, by rfl⟩ : syracuseStep 929975 = 1394963) B1394963
theorem B929995 : Blo 928581 929995 := bstep (se 1 (by rfl) ⟨697496, by rfl⟩ : syracuseStep 929995 = 1394993) B1394993
theorem B930007 : Blo 928581 930007 := bstep (se 1 (by rfl) ⟨697505, by rfl⟩ : syracuseStep 930007 = 1395011) B1395011
theorem B930027 : Blo 928581 930027 := bstep (se 1 (by rfl) ⟨697520, by rfl⟩ : syracuseStep 930027 = 1395041) B1395041
theorem B930039 : Blo 928581 930039 := bstep (se 1 (by rfl) ⟨697529, by rfl⟩ : syracuseStep 930039 = 1395059) B1395059
theorem B930059 : Blo 928581 930059 := bstep (se 1 (by rfl) ⟨697544, by rfl⟩ : syracuseStep 930059 = 1395089) B1395089
theorem B930071 : Blo 928581 930071 := bstep (se 1 (by rfl) ⟨697553, by rfl⟩ : syracuseStep 930071 = 1395107) B1395107
theorem B930091 : Blo 928581 930091 := bstep (se 1 (by rfl) ⟨697568, by rfl⟩ : syracuseStep 930091 = 1395137) B1395137
theorem B930103 : Blo 928581 930103 := bstep (se 1 (by rfl) ⟨697577, by rfl⟩ : syracuseStep 930103 = 1395155) B1395155
theorem B930123 : Blo 928581 930123 := bstep (se 1 (by rfl) ⟨697592, by rfl⟩ : syracuseStep 930123 = 1395185) B1395185
theorem B930135 : Blo 928581 930135 := bstep (se 1 (by rfl) ⟨697601, by rfl⟩ : syracuseStep 930135 = 1395203) B1395203
theorem B930155 : Blo 928581 930155 := bstep (se 1 (by rfl) ⟨697616, by rfl⟩ : syracuseStep 930155 = 1395233) B1395233
theorem B930167 : Blo 928581 930167 := bstep (se 1 (by rfl) ⟨697625, by rfl⟩ : syracuseStep 930167 = 1395251) B1395251
theorem B930187 : Blo 928581 930187 := bstep (se 1 (by rfl) ⟨697640, by rfl⟩ : syracuseStep 930187 = 1395281) B1395281
theorem B930199 : Blo 928581 930199 := bstep (se 1 (by rfl) ⟨697649, by rfl⟩ : syracuseStep 930199 = 1395299) B1395299
theorem B930219 : Blo 928581 930219 := bstep (se 1 (by rfl) ⟨697664, by rfl⟩ : syracuseStep 930219 = 1395329) B1395329
theorem B930231 : Blo 928581 930231 := bstep (se 1 (by rfl) ⟨697673, by rfl⟩ : syracuseStep 930231 = 1395347) B1395347
theorem B930251 : Blo 928581 930251 := bstep (se 1 (by rfl) ⟨697688, by rfl⟩ : syracuseStep 930251 = 1395377) B1395377
theorem B930263 : Blo 928581 930263 := bstep (se 1 (by rfl) ⟨697697, by rfl⟩ : syracuseStep 930263 = 1395395) B1395395
theorem B930283 : Blo 928581 930283 := bstep (se 1 (by rfl) ⟨697712, by rfl⟩ : syracuseStep 930283 = 1395425) B1395425
theorem B930295 : Blo 928581 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B930315 : Blo 928581 930315 := bstep (se 1 (by rfl) ⟨697736, by rfl⟩ : syracuseStep 930315 = 1395473) B1395473
theorem B930327 : Blo 928581 930327 := bstep (se 1 (by rfl) ⟨697745, by rfl⟩ : syracuseStep 930327 = 1395491) B1395491
theorem B1323545 : Blo 928581 1323545 := bstep (se 2 (by rfl) ⟨496329, by rfl⟩ : syracuseStep 1323545 = 992659) B992659
theorem B930347 : Blo 928581 930347 := bstep (se 1 (by rfl) ⟨697760, by rfl⟩ : syracuseStep 930347 = 1395521) B1395521
theorem B930359 : Blo 928581 930359 := bstep (se 1 (by rfl) ⟨697769, by rfl⟩ : syracuseStep 930359 = 1395539) B1395539
theorem B930379 : Blo 928581 930379 := bstep (se 1 (by rfl) ⟨697784, by rfl⟩ : syracuseStep 930379 = 1395569) B1395569
theorem B930391 : Blo 928581 930391 := bstep (se 1 (by rfl) ⟨697793, by rfl⟩ : syracuseStep 930391 = 1395587) B1395587
theorem B930411 : Blo 928581 930411 := bstep (se 1 (by rfl) ⟨697808, by rfl⟩ : syracuseStep 930411 = 1395617) B1395617
theorem B930423 : Blo 928581 930423 := bstep (se 1 (by rfl) ⟨697817, by rfl⟩ : syracuseStep 930423 = 1395635) B1395635
theorem B1323659 : Blo 928581 1323659 := bstep (se 1 (by rfl) ⟨992744, by rfl⟩ : syracuseStep 1323659 = 1985489) B1985489
theorem B930443 : Blo 928581 930443 := bstep (se 1 (by rfl) ⟨697832, by rfl⟩ : syracuseStep 930443 = 1395665) B1395665
theorem B930455 : Blo 928581 930455 := bstep (se 1 (by rfl) ⟨697841, by rfl⟩ : syracuseStep 930455 = 1395683) B1395683
theorem B930475 : Blo 928581 930475 := bstep (se 1 (by rfl) ⟨697856, by rfl⟩ : syracuseStep 930475 = 1395713) B1395713
theorem B930487 : Blo 928581 930487 := bstep (se 1 (by rfl) ⟨697865, by rfl⟩ : syracuseStep 930487 = 1395731) B1395731
theorem B930507 : Blo 928581 930507 := bstep (se 1 (by rfl) ⟨697880, by rfl⟩ : syracuseStep 930507 = 1395761) B1395761
theorem B930519 : Blo 928581 930519 := bstep (se 1 (by rfl) ⟨697889, by rfl⟩ : syracuseStep 930519 = 1395779) B1395779
theorem B930539 : Blo 928581 930539 := bstep (se 1 (by rfl) ⟨697904, by rfl⟩ : syracuseStep 930539 = 1395809) B1395809
theorem B930551 : Blo 928581 930551 := bstep (se 1 (by rfl) ⟨697913, by rfl⟩ : syracuseStep 930551 = 1395827) B1395827
theorem B930571 : Blo 928581 930571 := bstep (se 1 (by rfl) ⟨697928, by rfl⟩ : syracuseStep 930571 = 1395857) B1395857
theorem B930583 : Blo 928581 930583 := bstep (se 1 (by rfl) ⟨697937, by rfl⟩ : syracuseStep 930583 = 1395875) B1395875
theorem B3355415 : Blo 928581 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B930603 : Blo 928581 930603 := bstep (se 1 (by rfl) ⟨697952, by rfl⟩ : syracuseStep 930603 = 1395905) B1395905
theorem B930615 : Blo 928581 930615 := bstep (se 1 (by rfl) ⟨697961, by rfl⟩ : syracuseStep 930615 = 1395923) B1395923
theorem B930635 : Blo 928581 930635 := bstep (se 1 (by rfl) ⟨697976, by rfl⟩ : syracuseStep 930635 = 1395953) B1395953
theorem B930647 : Blo 928581 930647 := bstep (se 1 (by rfl) ⟨697985, by rfl⟩ : syracuseStep 930647 = 1395971) B1395971
theorem B930667 : Blo 928581 930667 := bstep (se 1 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 930667 = 1396001) B1396001
theorem B930679 : Blo 928581 930679 := bstep (se 1 (by rfl) ⟨698009, by rfl⟩ : syracuseStep 930679 = 1396019) B1396019
theorem B930699 : Blo 928581 930699 := bstep (se 1 (by rfl) ⟨698024, by rfl⟩ : syracuseStep 930699 = 1396049) B1396049
theorem B930711 : Blo 928581 930711 := bstep (se 1 (by rfl) ⟨698033, by rfl⟩ : syracuseStep 930711 = 1396067) B1396067
theorem B930731 : Blo 928581 930731 := bstep (se 1 (by rfl) ⟨698048, by rfl⟩ : syracuseStep 930731 = 1396097) B1396097
theorem B930743 : Blo 928581 930743 := bstep (se 1 (by rfl) ⟨698057, by rfl⟩ : syracuseStep 930743 = 1396115) B1396115
theorem B930763 : Blo 928581 930763 := bstep (se 1 (by rfl) ⟨698072, by rfl⟩ : syracuseStep 930763 = 1396145) B1396145
theorem B930775 : Blo 928581 930775 := bstep (se 1 (by rfl) ⟨698081, by rfl⟩ : syracuseStep 930775 = 1396163) B1396163
theorem B930795 : Blo 928581 930795 := bstep (se 1 (by rfl) ⟨698096, by rfl⟩ : syracuseStep 930795 = 1396193) B1396193
theorem B930807 : Blo 928581 930807 := bstep (se 1 (by rfl) ⟨698105, by rfl⟩ : syracuseStep 930807 = 1396211) B1396211
theorem B930827 : Blo 928581 930827 := bstep (se 1 (by rfl) ⟨698120, by rfl⟩ : syracuseStep 930827 = 1396241) B1396241
theorem B6370321 : Blo 928581 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B930839 : Blo 928581 930839 := bstep (se 1 (by rfl) ⟨698129, by rfl⟩ : syracuseStep 930839 = 1396259) B1396259
theorem B930859 : Blo 928581 930859 := bstep (se 1 (by rfl) ⟨698144, by rfl⟩ : syracuseStep 930859 = 1396289) B1396289
theorem B930871 : Blo 928581 930871 := bstep (se 1 (by rfl) ⟨698153, by rfl⟩ : syracuseStep 930871 = 1396307) B1396307
theorem B3224651 : Blo 928581 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B930891 : Blo 928581 930891 := bstep (se 1 (by rfl) ⟨698168, by rfl⟩ : syracuseStep 930891 = 1396337) B1396337
theorem B930903 : Blo 928581 930903 := bstep (se 1 (by rfl) ⟨698177, by rfl⟩ : syracuseStep 930903 = 1396355) B1396355
theorem B1258583 : Blo 928581 1258583 := bstep (se 1 (by rfl) ⟨943937, by rfl⟩ : syracuseStep 1258583 = 1887875) B1887875
theorem B930923 : Blo 928581 930923 := bstep (se 1 (by rfl) ⟨698192, by rfl⟩ : syracuseStep 930923 = 1396385) B1396385
theorem B930935 : Blo 928581 930935 := bstep (se 1 (by rfl) ⟨698201, by rfl⟩ : syracuseStep 930935 = 1396403) B1396403
theorem B930955 : Blo 928581 930955 := bstep (se 1 (by rfl) ⟨698216, by rfl⟩ : syracuseStep 930955 = 1396433) B1396433
theorem B1324183 : Blo 928581 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B930967 : Blo 928581 930967 := bstep (se 1 (by rfl) ⟨698225, by rfl⟩ : syracuseStep 930967 = 1396451) B1396451
theorem B930987 : Blo 928581 930987 := bstep (se 1 (by rfl) ⟨698240, by rfl⟩ : syracuseStep 930987 = 1396481) B1396481
theorem B930999 : Blo 928581 930999 := bstep (se 1 (by rfl) ⟨698249, by rfl⟩ : syracuseStep 930999 = 1396499) B1396499
theorem B931019 : Blo 928581 931019 := bstep (se 1 (by rfl) ⟨698264, by rfl⟩ : syracuseStep 931019 = 1396529) B1396529
theorem B931031 : Blo 928581 931031 := bstep (se 1 (by rfl) ⟨698273, by rfl⟩ : syracuseStep 931031 = 1396547) B1396547
theorem B931051 : Blo 928581 931051 := bstep (se 1 (by rfl) ⟨698288, by rfl⟩ : syracuseStep 931051 = 1396577) B1396577
theorem B931063 : Blo 928581 931063 := bstep (se 1 (by rfl) ⟨698297, by rfl⟩ : syracuseStep 931063 = 1396595) B1396595
theorem B931083 : Blo 928581 931083 := bstep (se 1 (by rfl) ⟨698312, by rfl⟩ : syracuseStep 931083 = 1396625) B1396625
theorem B931095 : Blo 928581 931095 := bstep (se 1 (by rfl) ⟨698321, by rfl⟩ : syracuseStep 931095 = 1396643) B1396643
theorem B931115 : Blo 928581 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B931127 : Blo 928581 931127 := bstep (se 1 (by rfl) ⟨698345, by rfl⟩ : syracuseStep 931127 = 1396691) B1396691
theorem B931147 : Blo 928581 931147 := bstep (se 1 (by rfl) ⟨698360, by rfl⟩ : syracuseStep 931147 = 1396721) B1396721
theorem B931159 : Blo 928581 931159 := bstep (se 1 (by rfl) ⟨698369, by rfl⟩ : syracuseStep 931159 = 1396739) B1396739
theorem B931179 : Blo 928581 931179 := bstep (se 1 (by rfl) ⟨698384, by rfl⟩ : syracuseStep 931179 = 1396769) B1396769
theorem B931191 : Blo 928581 931191 := bstep (se 1 (by rfl) ⟨698393, by rfl⟩ : syracuseStep 931191 = 1396787) B1396787
theorem B6698371 : Blo 928581 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B931211 : Blo 928581 931211 := bstep (se 1 (by rfl) ⟨698408, by rfl⟩ : syracuseStep 931211 = 1396817) B1396817
theorem B931223 : Blo 928581 931223 := bstep (se 1 (by rfl) ⟨698417, by rfl⟩ : syracuseStep 931223 = 1396835) B1396835
theorem B931243 : Blo 928581 931243 := bstep (se 1 (by rfl) ⟨698432, by rfl⟩ : syracuseStep 931243 = 1396865) B1396865
theorem B931255 : Blo 928581 931255 := bstep (se 1 (by rfl) ⟨698441, by rfl⟩ : syracuseStep 931255 = 1396883) B1396883
theorem B931275 : Blo 928581 931275 := bstep (se 1 (by rfl) ⟨698456, by rfl⟩ : syracuseStep 931275 = 1396913) B1396913
theorem B931287 : Blo 928581 931287 := bstep (se 1 (by rfl) ⟨698465, by rfl⟩ : syracuseStep 931287 = 1396931) B1396931
theorem B931307 : Blo 928581 931307 := bstep (se 1 (by rfl) ⟨698480, by rfl⟩ : syracuseStep 931307 = 1396961) B1396961
theorem B931319 : Blo 928581 931319 := bstep (se 1 (by rfl) ⟨698489, by rfl⟩ : syracuseStep 931319 = 1396979) B1396979
theorem B931339 : Blo 928581 931339 := bstep (se 1 (by rfl) ⟨698504, by rfl⟩ : syracuseStep 931339 = 1397009) B1397009
theorem B931351 : Blo 928581 931351 := bstep (se 1 (by rfl) ⟨698513, by rfl⟩ : syracuseStep 931351 = 1397027) B1397027
theorem B931371 : Blo 928581 931371 := bstep (se 1 (by rfl) ⟨698528, by rfl⟩ : syracuseStep 931371 = 1397057) B1397057
theorem B931383 : Blo 928581 931383 := bstep (se 1 (by rfl) ⟨698537, by rfl⟩ : syracuseStep 931383 = 1397075) B1397075
theorem B931403 : Blo 928581 931403 := bstep (se 1 (by rfl) ⟨698552, by rfl⟩ : syracuseStep 931403 = 1397105) B1397105
theorem B931415 : Blo 928581 931415 := bstep (se 1 (by rfl) ⟨698561, by rfl⟩ : syracuseStep 931415 = 1397123) B1397123
theorem B931435 : Blo 928581 931435 := bstep (se 1 (by rfl) ⟨698576, by rfl⟩ : syracuseStep 931435 = 1397153) B1397153
theorem B931447 : Blo 928581 931447 := bstep (se 1 (by rfl) ⟨698585, by rfl⟩ : syracuseStep 931447 = 1397171) B1397171
theorem B931467 : Blo 928581 931467 := bstep (se 1 (by rfl) ⟨698600, by rfl⟩ : syracuseStep 931467 = 1397201) B1397201
theorem B931479 : Blo 928581 931479 := bstep (se 1 (by rfl) ⟨698609, by rfl⟩ : syracuseStep 931479 = 1397219) B1397219
theorem B931499 : Blo 928581 931499 := bstep (se 1 (by rfl) ⟨698624, by rfl⟩ : syracuseStep 931499 = 1397249) B1397249
theorem B931511 : Blo 928581 931511 := bstep (se 1 (by rfl) ⟨698633, by rfl⟩ : syracuseStep 931511 = 1397267) B1397267
theorem B931531 : Blo 928581 931531 := bstep (se 1 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 931531 = 1397297) B1397297
theorem B7059149 : Blo 928581 7059149 := bstep (se 3 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 7059149 = 2647181) B2647181
theorem B931543 : Blo 928581 931543 := bstep (se 1 (by rfl) ⟨698657, by rfl⟩ : syracuseStep 931543 = 1397315) B1397315
theorem B3978973 : Blo 928581 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B931563 : Blo 928581 931563 := bstep (se 1 (by rfl) ⟨698672, by rfl⟩ : syracuseStep 931563 = 1397345) B1397345
theorem B931575 : Blo 928581 931575 := bstep (se 1 (by rfl) ⟨698681, by rfl⟩ : syracuseStep 931575 = 1397363) B1397363
theorem B931595 : Blo 928581 931595 := bstep (se 1 (by rfl) ⟨698696, by rfl⟩ : syracuseStep 931595 = 1397393) B1397393
theorem B931607 : Blo 928581 931607 := bstep (se 1 (by rfl) ⟨698705, by rfl⟩ : syracuseStep 931607 = 1397411) B1397411
theorem B2012953 : Blo 928581 2012953 := bstep (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) B1509715
theorem B931627 : Blo 928581 931627 := bstep (se 1 (by rfl) ⟨698720, by rfl⟩ : syracuseStep 931627 = 1397441) B1397441
theorem B931639 : Blo 928581 931639 := bstep (se 1 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 931639 = 1397459) B1397459
theorem B931659 : Blo 928581 931659 := bstep (se 1 (by rfl) ⟨698744, by rfl⟩ : syracuseStep 931659 = 1397489) B1397489
theorem B931671 : Blo 928581 931671 := bstep (se 1 (by rfl) ⟨698753, by rfl⟩ : syracuseStep 931671 = 1397507) B1397507
theorem B931691 : Blo 928581 931691 := bstep (se 1 (by rfl) ⟨698768, by rfl⟩ : syracuseStep 931691 = 1397537) B1397537
theorem B931703 : Blo 928581 931703 := bstep (se 1 (by rfl) ⟨698777, by rfl⟩ : syracuseStep 931703 = 1397555) B1397555
theorem B931723 : Blo 928581 931723 := bstep (se 1 (by rfl) ⟨698792, by rfl⟩ : syracuseStep 931723 = 1397585) B1397585
theorem B3356567 : Blo 928581 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B931735 : Blo 928581 931735 := bstep (se 1 (by rfl) ⟨698801, by rfl⟩ : syracuseStep 931735 = 1397603) B1397603
theorem B931755 : Blo 928581 931755 := bstep (se 1 (by rfl) ⟨698816, by rfl⟩ : syracuseStep 931755 = 1397633) B1397633
theorem B931767 : Blo 928581 931767 := bstep (se 1 (by rfl) ⟨698825, by rfl⟩ : syracuseStep 931767 = 1397651) B1397651
theorem B1325003 : Blo 928581 1325003 := bstep (se 1 (by rfl) ⟨993752, by rfl⟩ : syracuseStep 1325003 = 1987505) B1987505
theorem B931787 : Blo 928581 931787 := bstep (se 1 (by rfl) ⟨698840, by rfl⟩ : syracuseStep 931787 = 1397681) B1397681
theorem B931799 : Blo 928581 931799 := bstep (se 1 (by rfl) ⟨698849, by rfl⟩ : syracuseStep 931799 = 1397699) B1397699
theorem B931819 : Blo 928581 931819 := bstep (se 1 (by rfl) ⟨698864, by rfl⟩ : syracuseStep 931819 = 1397729) B1397729
theorem B931831 : Blo 928581 931831 := bstep (se 1 (by rfl) ⟨698873, by rfl⟩ : syracuseStep 931831 = 1397747) B1397747
theorem B1914881 : Blo 928581 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B931851 : Blo 928581 931851 := bstep (se 1 (by rfl) ⟨698888, by rfl⟩ : syracuseStep 931851 = 1397777) B1397777
theorem B931863 : Blo 928581 931863 := bstep (se 1 (by rfl) ⟨698897, by rfl⟩ : syracuseStep 931863 = 1397795) B1397795
theorem B931883 : Blo 928581 931883 := bstep (se 1 (by rfl) ⟨698912, by rfl⟩ : syracuseStep 931883 = 1397825) B1397825
theorem B931895 : Blo 928581 931895 := bstep (se 1 (by rfl) ⟨698921, by rfl⟩ : syracuseStep 931895 = 1397843) B1397843
theorem B931915 : Blo 928581 931915 := bstep (se 1 (by rfl) ⟨698936, by rfl⟩ : syracuseStep 931915 = 1397873) B1397873
theorem B931927 : Blo 928581 931927 := bstep (se 1 (by rfl) ⟨698945, by rfl⟩ : syracuseStep 931927 = 1397891) B1397891
theorem B931947 : Blo 928581 931947 := bstep (se 1 (by rfl) ⟨698960, by rfl⟩ : syracuseStep 931947 = 1397921) B1397921
theorem B931959 : Blo 928581 931959 := bstep (se 1 (by rfl) ⟨698969, by rfl⟩ : syracuseStep 931959 = 1397939) B1397939
theorem B931979 : Blo 928581 931979 := bstep (se 1 (by rfl) ⟨698984, by rfl⟩ : syracuseStep 931979 = 1397969) B1397969
theorem B931991 : Blo 928581 931991 := bstep (se 1 (by rfl) ⟨698993, by rfl⟩ : syracuseStep 931991 = 1397987) B1397987
theorem B932011 : Blo 928581 932011 := bstep (se 1 (by rfl) ⟨699008, by rfl⟩ : syracuseStep 932011 = 1398017) B1398017
theorem B7059635 : Blo 928581 7059635 := bstep (se 1 (by rfl) ⟨5294726, by rfl⟩ : syracuseStep 7059635 = 10589453) B10589453
theorem B932023 : Blo 928581 932023 := bstep (se 1 (by rfl) ⟨699017, by rfl⟩ : syracuseStep 932023 = 1398035) B1398035
theorem B932043 : Blo 928581 932043 := bstep (se 1 (by rfl) ⟨699032, by rfl⟩ : syracuseStep 932043 = 1398065) B1398065
theorem B932055 : Blo 928581 932055 := bstep (se 1 (by rfl) ⟨699041, by rfl⟩ : syracuseStep 932055 = 1398083) B1398083
theorem B932075 : Blo 928581 932075 := bstep (se 1 (by rfl) ⟨699056, by rfl⟩ : syracuseStep 932075 = 1398113) B1398113
theorem B932087 : Blo 928581 932087 := bstep (se 1 (by rfl) ⟨699065, by rfl⟩ : syracuseStep 932087 = 1398131) B1398131
theorem B932107 : Blo 928581 932107 := bstep (se 1 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 932107 = 1398161) B1398161
theorem B932119 : Blo 928581 932119 := bstep (se 1 (by rfl) ⟨699089, by rfl⟩ : syracuseStep 932119 = 1398179) B1398179
theorem B932139 : Blo 928581 932139 := bstep (se 1 (by rfl) ⟨699104, by rfl⟩ : syracuseStep 932139 = 1398209) B1398209
theorem B932151 : Blo 928581 932151 := bstep (se 1 (by rfl) ⟨699113, by rfl⟩ : syracuseStep 932151 = 1398227) B1398227
theorem B932171 : Blo 928581 932171 := bstep (se 1 (by rfl) ⟨699128, by rfl⟩ : syracuseStep 932171 = 1398257) B1398257
theorem B932183 : Blo 928581 932183 := bstep (se 1 (by rfl) ⟨699137, by rfl⟩ : syracuseStep 932183 = 1398275) B1398275
theorem B932203 : Blo 928581 932203 := bstep (se 1 (by rfl) ⟨699152, by rfl⟩ : syracuseStep 932203 = 1398305) B1398305
theorem B932215 : Blo 928581 932215 := bstep (se 1 (by rfl) ⟨699161, by rfl⟩ : syracuseStep 932215 = 1398323) B1398323
theorem B932235 : Blo 928581 932235 := bstep (se 1 (by rfl) ⟨699176, by rfl⟩ : syracuseStep 932235 = 1398353) B1398353
theorem B932247 : Blo 928581 932247 := bstep (se 1 (by rfl) ⟨699185, by rfl⟩ : syracuseStep 932247 = 1398371) B1398371
theorem B932267 : Blo 928581 932267 := bstep (se 1 (by rfl) ⟨699200, by rfl⟩ : syracuseStep 932267 = 1398401) B1398401
theorem B932279 : Blo 928581 932279 := bstep (se 1 (by rfl) ⟨699209, by rfl⟩ : syracuseStep 932279 = 1398419) B1398419
theorem B932299 : Blo 928581 932299 := bstep (se 1 (by rfl) ⟨699224, by rfl⟩ : syracuseStep 932299 = 1398449) B1398449
theorem B932311 : Blo 928581 932311 := bstep (se 1 (by rfl) ⟨699233, by rfl⟩ : syracuseStep 932311 = 1398467) B1398467
theorem B932331 : Blo 928581 932331 := bstep (se 1 (by rfl) ⟨699248, by rfl⟩ : syracuseStep 932331 = 1398497) B1398497
theorem B932343 : Blo 928581 932343 := bstep (se 1 (by rfl) ⟨699257, by rfl⟩ : syracuseStep 932343 = 1398515) B1398515
theorem B932363 : Blo 928581 932363 := bstep (se 1 (by rfl) ⟨699272, by rfl⟩ : syracuseStep 932363 = 1398545) B1398545
theorem B3979793 : Blo 928581 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B932375 : Blo 928581 932375 := bstep (se 1 (by rfl) ⟨699281, by rfl⟩ : syracuseStep 932375 = 1398563) B1398563
theorem B8927779 : Blo 928581 8927779 := bstep (se 1 (by rfl) ⟨6695834, by rfl⟩ : syracuseStep 8927779 = 13391669) B13391669
theorem B932395 : Blo 928581 932395 := bstep (se 1 (by rfl) ⟨699296, by rfl⟩ : syracuseStep 932395 = 1398593) B1398593
theorem B932407 : Blo 928581 932407 := bstep (se 1 (by rfl) ⟨699305, by rfl⟩ : syracuseStep 932407 = 1398611) B1398611
theorem B932427 : Blo 928581 932427 := bstep (se 1 (by rfl) ⟨699320, by rfl⟩ : syracuseStep 932427 = 1398641) B1398641
theorem B932439 : Blo 928581 932439 := bstep (se 1 (by rfl) ⟨699329, by rfl⟩ : syracuseStep 932439 = 1398659) B1398659
theorem B932459 : Blo 928581 932459 := bstep (se 1 (by rfl) ⟨699344, by rfl⟩ : syracuseStep 932459 = 1398689) B1398689
theorem B932471 : Blo 928581 932471 := bstep (se 1 (by rfl) ⟨699353, by rfl⟩ : syracuseStep 932471 = 1398707) B1398707
theorem B932491 : Blo 928581 932491 := bstep (se 1 (by rfl) ⟨699368, by rfl⟩ : syracuseStep 932491 = 1398737) B1398737
theorem B932503 : Blo 928581 932503 := bstep (se 1 (by rfl) ⟨699377, by rfl⟩ : syracuseStep 932503 = 1398755) B1398755
theorem B932523 : Blo 928581 932523 := bstep (se 1 (by rfl) ⟨699392, by rfl⟩ : syracuseStep 932523 = 1398785) B1398785
theorem B932535 : Blo 928581 932535 := bstep (se 1 (by rfl) ⟨699401, by rfl⟩ : syracuseStep 932535 = 1398803) B1398803
theorem B932555 : Blo 928581 932555 := bstep (se 1 (by rfl) ⟨699416, by rfl⟩ : syracuseStep 932555 = 1398833) B1398833
theorem B932567 : Blo 928581 932567 := bstep (se 1 (by rfl) ⟨699425, by rfl⟩ : syracuseStep 932567 = 1398851) B1398851
theorem B17906609 : Blo 928581 17906609 := bstep (se 2 (by rfl) ⟨6714978, by rfl⟩ : syracuseStep 17906609 = 13429957) B13429957
theorem B3980461 : Blo 928581 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B1883351 : Blo 928581 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B4701401 : Blo 928581 4701401 := bstep (se 2 (by rfl) ⟨1763025, by rfl⟩ : syracuseStep 4701401 = 3526051) B3526051
theorem B4472081 : Blo 928581 4472081 := bstep (se 2 (by rfl) ⟨1677030, by rfl⟩ : syracuseStep 4472081 = 3354061) B3354061
theorem B12107225 : Blo 928581 12107225 := bstep (se 2 (by rfl) ⟨4540209, by rfl⟩ : syracuseStep 12107225 = 9080419) B9080419
theorem B7061093 : Blo 928581 7061093 := bstep (se 4 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 7061093 = 1323955) B1323955
theorem B3981059 : Blo 928581 3981059 := bstep (se 1 (by rfl) ⟨2985794, by rfl⟩ : syracuseStep 3981059 = 5971589) B5971589
theorem B1326871 : Blo 928581 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B3358529 : Blo 928581 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B8044505 : Blo 928581 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B5291993 : Blo 928581 5291993 := bstep (se 2 (by rfl) ⟨1984497, by rfl⟩ : syracuseStep 5291993 = 3968995) B3968995
theorem B1884235 : Blo 928581 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B7061579 : Blo 928581 7061579 := bstep (se 1 (by rfl) ⟨5296184, by rfl⟩ : syracuseStep 7061579 = 10592369) B10592369
theorem B2834635 : Blo 928581 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B1392971 : Blo 928581 1392971 := bstep (se 1 (by rfl) ⟨1044728, by rfl⟩ : syracuseStep 1392971 = 2089457) B2089457
theorem B1392983 : Blo 928581 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B1393049 : Blo 928581 1393049 := bstep (se 2 (by rfl) ⟨522393, by rfl⟩ : syracuseStep 1393049 = 1044787) B1044787
theorem B1393163 : Blo 928581 1393163 := bstep (se 1 (by rfl) ⟨1044872, by rfl⟩ : syracuseStep 1393163 = 2089745) B2089745
theorem B1393175 : Blo 928581 1393175 := bstep (se 1 (by rfl) ⟨1044881, by rfl⟩ : syracuseStep 1393175 = 2089763) B2089763
theorem B1393241 : Blo 928581 1393241 := bstep (se 2 (by rfl) ⟨522465, by rfl⟩ : syracuseStep 1393241 = 1044931) B1044931
theorem B967339 : Blo 928581 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B1393355 : Blo 928581 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B1393367 : Blo 928581 1393367 := bstep (se 1 (by rfl) ⟨1045025, by rfl⟩ : syracuseStep 1393367 = 2090051) B2090051
theorem B1393433 : Blo 928581 1393433 := bstep (se 2 (by rfl) ⟨522537, by rfl⟩ : syracuseStep 1393433 = 1045075) B1045075
theorem B4703021 : Blo 928581 4703021 := bstep (se 3 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 4703021 = 1763633) B1763633
theorem B7652161 : Blo 928581 7652161 := bstep (se 2 (by rfl) ⟨2869560, by rfl⟩ : syracuseStep 7652161 = 5739121) B5739121
theorem B4473731 : Blo 928581 4473731 := bstep (se 1 (by rfl) ⟨3355298, by rfl⟩ : syracuseStep 4473731 = 6710597) B6710597
theorem B1393547 : Blo 928581 1393547 := bstep (se 1 (by rfl) ⟨1045160, by rfl⟩ : syracuseStep 1393547 = 2090321) B2090321
theorem B1393559 : Blo 928581 1393559 := bstep (se 1 (by rfl) ⟨1045169, by rfl⟩ : syracuseStep 1393559 = 2090339) B2090339
theorem B1393625 : Blo 928581 1393625 := bstep (se 2 (by rfl) ⟨522609, by rfl⟩ : syracuseStep 1393625 = 1045219) B1045219
theorem B1590283 : Blo 928581 1590283 := bstep (se 1 (by rfl) ⟨1192712, by rfl⟩ : syracuseStep 1590283 = 2385425) B2385425
theorem B1393739 : Blo 928581 1393739 := bstep (se 1 (by rfl) ⟨1045304, by rfl⟩ : syracuseStep 1393739 = 2090609) B2090609
theorem B1983575 : Blo 928581 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B1393751 : Blo 928581 1393751 := bstep (se 1 (by rfl) ⟨1045313, by rfl⟩ : syracuseStep 1393751 = 2090627) B2090627
theorem B1393817 : Blo 928581 1393817 := bstep (se 2 (by rfl) ⟨522681, by rfl⟩ : syracuseStep 1393817 = 1045363) B1045363
theorem B1393931 : Blo 928581 1393931 := bstep (se 1 (by rfl) ⟨1045448, by rfl⟩ : syracuseStep 1393931 = 2090897) B2090897
theorem B1393943 : Blo 928581 1393943 := bstep (se 1 (by rfl) ⟨1045457, by rfl⟩ : syracuseStep 1393943 = 2090915) B2090915
theorem B1394009 : Blo 928581 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B1394123 : Blo 928581 1394123 := bstep (se 1 (by rfl) ⟨1045592, by rfl⟩ : syracuseStep 1394123 = 2091185) B2091185
theorem B1394135 : Blo 928581 1394135 := bstep (se 1 (by rfl) ⟨1045601, by rfl⟩ : syracuseStep 1394135 = 2091203) B2091203
theorem B1394201 : Blo 928581 1394201 := bstep (se 2 (by rfl) ⟨522825, by rfl⟩ : syracuseStep 1394201 = 1045651) B1045651
theorem B5293633 : Blo 928581 5293633 := bstep (se 2 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 5293633 = 3970225) B3970225
theorem B1394315 : Blo 928581 1394315 := bstep (se 1 (by rfl) ⟨1045736, by rfl⟩ : syracuseStep 1394315 = 2091473) B2091473
theorem B1394327 : Blo 928581 1394327 := bstep (se 1 (by rfl) ⟨1045745, by rfl⟩ : syracuseStep 1394327 = 2091491) B2091491
theorem B1394393 : Blo 928581 1394393 := bstep (se 2 (by rfl) ⟨522897, by rfl⟩ : syracuseStep 1394393 = 1045795) B1045795
theorem B1394507 : Blo 928581 1394507 := bstep (se 1 (by rfl) ⟨1045880, by rfl⟩ : syracuseStep 1394507 = 2091761) B2091761
theorem B1394519 : Blo 928581 1394519 := bstep (se 1 (by rfl) ⟨1045889, by rfl⟩ : syracuseStep 1394519 = 2091779) B2091779
theorem B1394585 : Blo 928581 1394585 := bstep (se 2 (by rfl) ⟨522969, by rfl⟩ : syracuseStep 1394585 = 1045939) B1045939
theorem B1394699 : Blo 928581 1394699 := bstep (se 1 (by rfl) ⟨1046024, by rfl⟩ : syracuseStep 1394699 = 2092049) B2092049
theorem B1394711 : Blo 928581 1394711 := bstep (se 1 (by rfl) ⟨1046033, by rfl⟩ : syracuseStep 1394711 = 2092067) B2092067
theorem B1984601 : Blo 928581 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B1394777 : Blo 928581 1394777 := bstep (se 2 (by rfl) ⟨523041, by rfl⟩ : syracuseStep 1394777 = 1046083) B1046083
theorem B1394891 : Blo 928581 1394891 := bstep (se 1 (by rfl) ⟨1046168, by rfl⟩ : syracuseStep 1394891 = 2092337) B2092337
theorem B1394903 : Blo 928581 1394903 := bstep (se 1 (by rfl) ⟨1046177, by rfl⟩ : syracuseStep 1394903 = 2092355) B2092355
theorem B1886465 : Blo 928581 1886465 := bstep (se 2 (by rfl) ⟨707424, by rfl⟩ : syracuseStep 1886465 = 1414849) B1414849
theorem B1394969 : Blo 928581 1394969 := bstep (se 2 (by rfl) ⟨523113, by rfl⟩ : syracuseStep 1394969 = 1046227) B1046227
theorem B1395083 : Blo 928581 1395083 := bstep (se 1 (by rfl) ⟨1046312, by rfl⟩ : syracuseStep 1395083 = 2092625) B2092625
theorem B1395095 : Blo 928581 1395095 := bstep (se 1 (by rfl) ⟨1046321, by rfl⟩ : syracuseStep 1395095 = 2092643) B2092643
theorem B1395161 : Blo 928581 1395161 := bstep (se 2 (by rfl) ⟨523185, by rfl⟩ : syracuseStep 1395161 = 1046371) B1046371
theorem B1395275 : Blo 928581 1395275 := bstep (se 1 (by rfl) ⟨1046456, by rfl⟩ : syracuseStep 1395275 = 2092913) B2092913
theorem B1395287 : Blo 928581 1395287 := bstep (se 1 (by rfl) ⟨1046465, by rfl⟩ : syracuseStep 1395287 = 2092931) B2092931
theorem B1395353 : Blo 928581 1395353 := bstep (se 2 (by rfl) ⟨523257, by rfl⟩ : syracuseStep 1395353 = 1046515) B1046515
theorem B6703793 : Blo 928581 6703793 := bstep (se 2 (by rfl) ⟨2513922, by rfl⟩ : syracuseStep 6703793 = 5027845) B5027845
theorem B1395467 : Blo 928581 1395467 := bstep (se 1 (by rfl) ⟨1046600, by rfl⟩ : syracuseStep 1395467 = 2093201) B2093201
theorem B3394327 : Blo 928581 3394327 := bstep (se 1 (by rfl) ⟨2545745, by rfl⟩ : syracuseStep 3394327 = 5091491) B5091491
theorem B1395479 : Blo 928581 1395479 := bstep (se 1 (by rfl) ⟨1046609, by rfl⟩ : syracuseStep 1395479 = 2093219) B2093219
theorem B1395545 : Blo 928581 1395545 := bstep (se 2 (by rfl) ⟨523329, by rfl⟩ : syracuseStep 1395545 = 1046659) B1046659
theorem B1395659 : Blo 928581 1395659 := bstep (se 1 (by rfl) ⟨1046744, by rfl⟩ : syracuseStep 1395659 = 2093489) B2093489
theorem B1395671 : Blo 928581 1395671 := bstep (se 1 (by rfl) ⟨1046753, by rfl⟩ : syracuseStep 1395671 = 2093507) B2093507
theorem B1395737 : Blo 928581 1395737 := bstep (se 2 (by rfl) ⟨523401, by rfl⟩ : syracuseStep 1395737 = 1046803) B1046803
theorem B1395851 : Blo 928581 1395851 := bstep (se 1 (by rfl) ⟨1046888, by rfl⟩ : syracuseStep 1395851 = 2093777) B2093777
theorem B1395863 : Blo 928581 1395863 := bstep (se 1 (by rfl) ⟨1046897, by rfl⟩ : syracuseStep 1395863 = 2093795) B2093795
theorem B1592473 : Blo 928581 1592473 := bstep (se 2 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 1592473 = 1194355) B1194355
theorem B8473805 : Blo 928581 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B1395929 : Blo 928581 1395929 := bstep (se 2 (by rfl) ⟨523473, by rfl⟩ : syracuseStep 1395929 = 1046947) B1046947
theorem B1789235 : Blo 928581 1789235 := bstep (se 1 (by rfl) ⟨1341926, by rfl⟩ : syracuseStep 1789235 = 2683853) B2683853
theorem B1396043 : Blo 928581 1396043 := bstep (se 1 (by rfl) ⟨1047032, by rfl⟩ : syracuseStep 1396043 = 2094065) B2094065
theorem B1396055 : Blo 928581 1396055 := bstep (se 1 (by rfl) ⟨1047041, by rfl⟩ : syracuseStep 1396055 = 2094083) B2094083
theorem B4246915 : Blo 928581 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B1396121 : Blo 928581 1396121 := bstep (se 2 (by rfl) ⟨523545, by rfl⟩ : syracuseStep 1396121 = 1047091) B1047091
theorem B1396235 : Blo 928581 1396235 := bstep (se 1 (by rfl) ⟨1047176, by rfl⟩ : syracuseStep 1396235 = 2094353) B2094353
theorem B1396247 : Blo 928581 1396247 := bstep (se 1 (by rfl) ⟨1047185, by rfl⟩ : syracuseStep 1396247 = 2094371) B2094371
theorem B1396313 : Blo 928581 1396313 := bstep (se 2 (by rfl) ⟨523617, by rfl⟩ : syracuseStep 1396313 = 1047235) B1047235
theorem B30133853 : Blo 928581 30133853 := bstep (se 3 (by rfl) ⟨5650097, by rfl⟩ : syracuseStep 30133853 = 11300195) B11300195
theorem B1986241 : Blo 928581 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B1396427 : Blo 928581 1396427 := bstep (se 1 (by rfl) ⟨1047320, by rfl⟩ : syracuseStep 1396427 = 2094641) B2094641
theorem B1396439 : Blo 928581 1396439 := bstep (se 1 (by rfl) ⟨1047329, by rfl⟩ : syracuseStep 1396439 = 2094659) B2094659
theorem B1396505 : Blo 928581 1396505 := bstep (se 2 (by rfl) ⟨523689, by rfl⟩ : syracuseStep 1396505 = 1047379) B1047379
theorem B8933165 : Blo 928581 8933165 := bstep (se 3 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 8933165 = 3349937) B3349937
theorem B1396619 : Blo 928581 1396619 := bstep (se 1 (by rfl) ⟨1047464, by rfl⟩ : syracuseStep 1396619 = 2094929) B2094929
theorem B1396631 : Blo 928581 1396631 := bstep (se 1 (by rfl) ⟨1047473, by rfl⟩ : syracuseStep 1396631 = 2094947) B2094947
theorem B6541235 : Blo 928581 6541235 := bstep (se 1 (by rfl) ⟨4905926, by rfl⟩ : syracuseStep 6541235 = 9811853) B9811853
theorem B1396697 : Blo 928581 1396697 := bstep (se 2 (by rfl) ⟨523761, by rfl⟩ : syracuseStep 1396697 = 1047523) B1047523
theorem B1396811 : Blo 928581 1396811 := bstep (se 1 (by rfl) ⟨1047608, by rfl⟩ : syracuseStep 1396811 = 2095217) B2095217
theorem B1396823 : Blo 928581 1396823 := bstep (se 1 (by rfl) ⟨1047617, by rfl⟩ : syracuseStep 1396823 = 2095235) B2095235
theorem B1396889 : Blo 928581 1396889 := bstep (se 2 (by rfl) ⟨523833, by rfl⟩ : syracuseStep 1396889 = 1047667) B1047667
theorem B1397003 : Blo 928581 1397003 := bstep (se 1 (by rfl) ⟨1047752, by rfl⟩ : syracuseStep 1397003 = 2095505) B2095505
theorem B1986839 : Blo 928581 1986839 := bstep (se 1 (by rfl) ⟨1490129, by rfl⟩ : syracuseStep 1986839 = 2980259) B2980259
theorem B1397015 : Blo 928581 1397015 := bstep (se 1 (by rfl) ⟨1047761, by rfl⟩ : syracuseStep 1397015 = 2095523) B2095523
theorem B1397081 : Blo 928581 1397081 := bstep (se 2 (by rfl) ⟨523905, by rfl⟩ : syracuseStep 1397081 = 1047811) B1047811
theorem B1593689 : Blo 928581 1593689 := bstep (se 2 (by rfl) ⟨597633, by rfl⟩ : syracuseStep 1593689 = 1195267) B1195267
theorem B1397195 : Blo 928581 1397195 := bstep (se 1 (by rfl) ⟨1047896, by rfl⟩ : syracuseStep 1397195 = 2095793) B2095793
theorem B1397207 : Blo 928581 1397207 := bstep (se 1 (by rfl) ⟨1047905, by rfl⟩ : syracuseStep 1397207 = 2095811) B2095811
theorem B1397273 : Blo 928581 1397273 := bstep (se 2 (by rfl) ⟨523977, by rfl⟩ : syracuseStep 1397273 = 1047955) B1047955
theorem B1593931 : Blo 928581 1593931 := bstep (se 1 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 1593931 = 2390897) B2390897
theorem B4706909 : Blo 928581 4706909 := bstep (se 3 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 4706909 = 1765091) B1765091
theorem B15323741 : Blo 928581 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B1397387 : Blo 928581 1397387 := bstep (se 1 (by rfl) ⟨1048040, by rfl⟩ : syracuseStep 1397387 = 2096081) B2096081
theorem B1397399 : Blo 928581 1397399 := bstep (se 1 (by rfl) ⟨1048049, by rfl⟩ : syracuseStep 1397399 = 2096099) B2096099
theorem B1397465 : Blo 928581 1397465 := bstep (se 2 (by rfl) ⟨524049, by rfl⟩ : syracuseStep 1397465 = 1048099) B1048099
theorem B1397579 : Blo 928581 1397579 := bstep (se 1 (by rfl) ⟨1048184, by rfl⟩ : syracuseStep 1397579 = 2096369) B2096369
theorem B1397591 : Blo 928581 1397591 := bstep (se 1 (by rfl) ⟨1048193, by rfl⟩ : syracuseStep 1397591 = 2096387) B2096387
theorem B6378371 : Blo 928581 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B1397657 : Blo 928581 1397657 := bstep (se 2 (by rfl) ⟨524121, by rfl⟩ : syracuseStep 1397657 = 1048243) B1048243
theorem B5297075 : Blo 928581 5297075 := bstep (se 1 (by rfl) ⟨3972806, by rfl⟩ : syracuseStep 5297075 = 7945613) B7945613
theorem B10605491 : Blo 928581 10605491 := bstep (se 1 (by rfl) ⟨7954118, by rfl⟩ : syracuseStep 10605491 = 15908237) B15908237
theorem B2544587 : Blo 928581 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B3134429 : Blo 928581 3134429 := bstep (se 3 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 3134429 = 1175411) B1175411
theorem B1397771 : Blo 928581 1397771 := bstep (se 1 (by rfl) ⟨1048328, by rfl⟩ : syracuseStep 1397771 = 2096657) B2096657
theorem B13390865 : Blo 928581 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B1397783 : Blo 928581 1397783 := bstep (se 1 (by rfl) ⟨1048337, by rfl⟩ : syracuseStep 1397783 = 2096675) B2096675
theorem B1397849 : Blo 928581 1397849 := bstep (se 2 (by rfl) ⟨524193, by rfl⟩ : syracuseStep 1397849 = 1048387) B1048387
theorem B1397963 : Blo 928581 1397963 := bstep (se 1 (by rfl) ⟨1048472, by rfl⟩ : syracuseStep 1397963 = 2096945) B2096945
theorem B1397975 : Blo 928581 1397975 := bstep (se 1 (by rfl) ⟨1048481, by rfl⟩ : syracuseStep 1397975 = 2096963) B2096963
theorem B1398041 : Blo 928581 1398041 := bstep (se 2 (by rfl) ⟨524265, by rfl⟩ : syracuseStep 1398041 = 1048531) B1048531
theorem B3527981 : Blo 928581 3527981 := bstep (se 3 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 3527981 = 1322993) B1322993
theorem B7066925 : Blo 928581 7066925 := bstep (se 3 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 7066925 = 2650097) B2650097
theorem B1987915 : Blo 928581 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B1398155 : Blo 928581 1398155 := bstep (se 1 (by rfl) ⟨1048616, by rfl⟩ : syracuseStep 1398155 = 2097233) B2097233
theorem B1398167 : Blo 928581 1398167 := bstep (se 1 (by rfl) ⟨1048625, by rfl⟩ : syracuseStep 1398167 = 2097251) B2097251
theorem B1398233 : Blo 928581 1398233 := bstep (se 2 (by rfl) ⟨524337, by rfl⟩ : syracuseStep 1398233 = 1048675) B1048675
theorem B4838977 : Blo 928581 4838977 := bstep (se 2 (by rfl) ⟨1814616, by rfl⟩ : syracuseStep 4838977 = 3629233) B3629233
theorem B1398347 : Blo 928581 1398347 := bstep (se 1 (by rfl) ⟨1048760, by rfl⟩ : syracuseStep 1398347 = 2097521) B2097521
theorem B1398359 : Blo 928581 1398359 := bstep (se 1 (by rfl) ⟨1048769, by rfl⟩ : syracuseStep 1398359 = 2097539) B2097539
theorem B1398425 : Blo 928581 1398425 := bstep (se 2 (by rfl) ⟨524409, by rfl⟩ : syracuseStep 1398425 = 1048819) B1048819
theorem B48420557 : Blo 928581 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B1398539 : Blo 928581 1398539 := bstep (se 1 (by rfl) ⟨1048904, by rfl⟩ : syracuseStep 1398539 = 2097809) B2097809
theorem B1398551 : Blo 928581 1398551 := bstep (se 1 (by rfl) ⟨1048913, by rfl⟩ : syracuseStep 1398551 = 2097827) B2097827
theorem B1890113 : Blo 928581 1890113 := bstep (se 2 (by rfl) ⟨708792, by rfl⟩ : syracuseStep 1890113 = 1417585) B1417585
theorem B1398617 : Blo 928581 1398617 := bstep (se 2 (by rfl) ⟨524481, by rfl⟩ : syracuseStep 1398617 = 1048963) B1048963
theorem B1398731 : Blo 928581 1398731 := bstep (se 1 (by rfl) ⟨1049048, by rfl⟩ : syracuseStep 1398731 = 2098097) B2098097
theorem B1398743 : Blo 928581 1398743 := bstep (se 1 (by rfl) ⟨1049057, by rfl⟩ : syracuseStep 1398743 = 2098115) B2098115
theorem B4413457 : Blo 928581 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B1988633 : Blo 928581 1988633 := bstep (se 2 (by rfl) ⟨745737, by rfl⟩ : syracuseStep 1988633 = 1491475) B1491475
theorem B1398809 : Blo 928581 1398809 := bstep (se 2 (by rfl) ⟨524553, by rfl⟩ : syracuseStep 1398809 = 1049107) B1049107
theorem B3528755 : Blo 928581 3528755 := bstep (se 1 (by rfl) ⟨2646566, by rfl⟩ : syracuseStep 3528755 = 5293133) B5293133
theorem B3135563 : Blo 928581 3135563 := bstep (se 1 (by rfl) ⟨2351672, by rfl⟩ : syracuseStep 3135563 = 4703345) B4703345
theorem B5036107 : Blo 928581 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B2644289 : Blo 928581 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B3135833 : Blo 928581 3135833 := bstep (se 2 (by rfl) ⟨1175937, by rfl⟩ : syracuseStep 3135833 = 2351875) B2351875
theorem B5298533 : Blo 928581 5298533 := bstep (se 4 (by rfl) ⟨496737, by rfl⟩ : syracuseStep 5298533 = 993475) B993475
theorem B10606949 : Blo 928581 10606949 := bstep (se 4 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 10606949 = 1988803) B1988803
theorem B68802929 : Blo 928581 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B2120203 : Blo 928581 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B1989145 : Blo 928581 1989145 := bstep (se 2 (by rfl) ⟨745929, by rfl⟩ : syracuseStep 1989145 = 1491859) B1491859
theorem B4709015 : Blo 928581 4709015 := bstep (se 1 (by rfl) ⟨3531761, by rfl⟩ : syracuseStep 4709015 = 7063523) B7063523
theorem B1989299 : Blo 928581 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B2513729 : Blo 928581 2513729 := bstep (se 2 (by rfl) ⟨942648, by rfl⟩ : syracuseStep 2513729 = 1885297) B1885297
theorem B3136535 : Blo 928581 3136535 := bstep (se 1 (by rfl) ⟨2352401, by rfl⟩ : syracuseStep 3136535 = 4704803) B4704803
theorem B7560323 : Blo 928581 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B20405429 : Blo 928581 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B16997809 : Blo 928581 16997809 := bstep (se 2 (by rfl) ⟨6374178, by rfl⟩ : syracuseStep 16997809 = 12748357) B12748357
theorem B2350529 : Blo 928581 2350529 := bstep (se 2 (by rfl) ⟨881448, by rfl⟩ : syracuseStep 2350529 = 1762897) B1762897
theorem B3530243 : Blo 928581 3530243 := bstep (se 1 (by rfl) ⟨2647682, by rfl⟩ : syracuseStep 3530243 = 5295365) B5295365
theorem B3137075 : Blo 928581 3137075 := bstep (se 1 (by rfl) ⟨2352806, by rfl⟩ : syracuseStep 3137075 = 4705613) B4705613
theorem B1990273 : Blo 928581 1990273 := bstep (se 2 (by rfl) ⟨746352, by rfl⟩ : syracuseStep 1990273 = 1492705) B1492705
theorem B3137345 : Blo 928581 3137345 := bstep (se 2 (by rfl) ⟨1176504, by rfl⟩ : syracuseStep 3137345 = 2353009) B2353009
theorem B3399499 : Blo 928581 3399499 := bstep (se 1 (by rfl) ⟨2549624, by rfl⟩ : syracuseStep 3399499 = 5099249) B5099249
theorem B3530699 : Blo 928581 3530699 := bstep (se 1 (by rfl) ⟨2648024, by rfl⟩ : syracuseStep 3530699 = 5296049) B5296049
theorem B1990615 : Blo 928581 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B2351065 : Blo 928581 2351065 := bstep (se 2 (by rfl) ⟨881649, by rfl⟩ : syracuseStep 2351065 = 1763299) B1763299
theorem B3530897 : Blo 928581 3530897 := bstep (se 2 (by rfl) ⟨1324086, by rfl⟩ : syracuseStep 3530897 = 2648173) B2648173
theorem B2154763 : Blo 928581 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B93184277 : Blo 928581 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B4481345 : Blo 928581 4481345 := bstep (se 2 (by rfl) ⟨1680504, by rfl⟩ : syracuseStep 4481345 = 3361009) B3361009
theorem B2646361 : Blo 928581 2646361 := bstep (se 2 (by rfl) ⟨992385, by rfl⟩ : syracuseStep 2646361 = 1984771) B1984771
theorem B3137885 : Blo 928581 3137885 := bstep (se 3 (by rfl) ⟨588353, by rfl⟩ : syracuseStep 3137885 = 1176707) B1176707
theorem B11493733 : Blo 928581 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B2089331 : Blo 928581 2089331 := bstep (se 1 (by rfl) ⟨1566998, by rfl⟩ : syracuseStep 2089331 = 3133997) B3133997
theorem B1991051 : Blo 928581 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B2089367 : Blo 928581 2089367 := bstep (se 1 (by rfl) ⟨1567025, by rfl⟩ : syracuseStep 2089367 = 3134051) B3134051
theorem B2384407 : Blo 928581 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B7955009 : Blo 928581 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B2089547 : Blo 928581 2089547 := bstep (se 1 (by rfl) ⟨1567160, by rfl⟩ : syracuseStep 2089547 = 3134321) B3134321
theorem B2089601 : Blo 928581 2089601 := bstep (se 2 (by rfl) ⟨783600, by rfl⟩ : syracuseStep 2089601 = 1567201) B1567201
theorem B2646749 : Blo 928581 2646749 := bstep (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) B992531
theorem B1073899 : Blo 928581 1073899 := bstep (se 1 (by rfl) ⟨805424, by rfl⟩ : syracuseStep 1073899 = 1610849) B1610849
theorem B2089817 : Blo 928581 2089817 := bstep (se 2 (by rfl) ⟨783681, by rfl⟩ : syracuseStep 2089817 = 1567363) B1567363
theorem B3531671 : Blo 928581 3531671 := bstep (se 1 (by rfl) ⟨2648753, by rfl⟩ : syracuseStep 3531671 = 5297507) B5297507
theorem B2089907 : Blo 928581 2089907 := bstep (se 1 (by rfl) ⟨1567430, by rfl⟩ : syracuseStep 2089907 = 3134861) B3134861
theorem B6710195 : Blo 928581 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B2089943 : Blo 928581 2089943 := bstep (se 1 (by rfl) ⟨1567457, by rfl⟩ : syracuseStep 2089943 = 3134915) B3134915
theorem B128803861 : Blo 928581 128803861 := bstep (se 6 (by rfl) ⟨3018840, by rfl⟩ : syracuseStep 128803861 = 6037681) B6037681
theorem B2352179 : Blo 928581 2352179 := bstep (se 1 (by rfl) ⟨1764134, by rfl⟩ : syracuseStep 2352179 = 3528269) B3528269
theorem B8479819 : Blo 928581 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B3531869 : Blo 928581 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B7070813 : Blo 928581 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B2090123 : Blo 928581 2090123 := bstep (se 1 (by rfl) ⟨1567592, by rfl⟩ : syracuseStep 2090123 = 3135185) B3135185
theorem B2090177 : Blo 928581 2090177 := bstep (se 2 (by rfl) ⟨783816, by rfl⟩ : syracuseStep 2090177 = 1567633) B1567633
theorem B2352473 : Blo 928581 2352473 := bstep (se 2 (by rfl) ⟨882177, by rfl⟩ : syracuseStep 2352473 = 1764355) B1764355
theorem B2090393 : Blo 928581 2090393 := bstep (se 2 (by rfl) ⟨783897, by rfl⟩ : syracuseStep 2090393 = 1567795) B1567795
theorem B3139019 : Blo 928581 3139019 := bstep (se 1 (by rfl) ⟨2354264, by rfl⟩ : syracuseStep 3139019 = 4708529) B4708529
theorem B2090483 : Blo 928581 2090483 := bstep (se 1 (by rfl) ⟨1567862, by rfl⟩ : syracuseStep 2090483 = 3135725) B3135725
theorem B2090519 : Blo 928581 2090519 := bstep (se 1 (by rfl) ⟨1567889, by rfl⟩ : syracuseStep 2090519 = 3135779) B3135779
theorem B8939159 : Blo 928581 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B2090699 : Blo 928581 2090699 := bstep (se 1 (by rfl) ⟨1568024, by rfl⟩ : syracuseStep 2090699 = 3136049) B3136049
theorem B3139289 : Blo 928581 3139289 := bstep (se 2 (by rfl) ⟨1177233, by rfl⟩ : syracuseStep 3139289 = 2354467) B2354467
theorem B2090753 : Blo 928581 2090753 := bstep (se 2 (by rfl) ⟨784032, by rfl⟩ : syracuseStep 2090753 = 1568065) B1568065
theorem B1763147 : Blo 928581 1763147 := bstep (se 1 (by rfl) ⟨1322360, by rfl⟩ : syracuseStep 1763147 = 2644721) B2644721
theorem B1763201 : Blo 928581 1763201 := bstep (se 2 (by rfl) ⟨661200, by rfl⟩ : syracuseStep 1763201 = 1322401) B1322401
theorem B2418611 : Blo 928581 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B2090969 : Blo 928581 2090969 := bstep (se 2 (by rfl) ⟨784113, by rfl⟩ : syracuseStep 2090969 = 1568227) B1568227
theorem B2091059 : Blo 928581 2091059 := bstep (se 1 (by rfl) ⟨1568294, by rfl⟩ : syracuseStep 2091059 = 3136589) B3136589
theorem B2091095 : Blo 928581 2091095 := bstep (se 1 (by rfl) ⟨1568321, by rfl⟩ : syracuseStep 2091095 = 3136643) B3136643
theorem B4712579 : Blo 928581 4712579 := bstep (se 1 (by rfl) ⟨3534434, by rfl⟩ : syracuseStep 4712579 = 7068869) B7068869
theorem B2091275 : Blo 928581 2091275 := bstep (se 1 (by rfl) ⟨1568456, by rfl⟩ : syracuseStep 2091275 = 3136913) B3136913
theorem B2091329 : Blo 928581 2091329 := bstep (se 2 (by rfl) ⟨784248, by rfl⟩ : syracuseStep 2091329 = 1568497) B1568497
theorem B5957981 : Blo 928581 5957981 := bstep (se 3 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 5957981 = 2234243) B2234243
theorem B1567127 : Blo 928581 1567127 := bstep (se 1 (by rfl) ⟨1175345, by rfl⟩ : syracuseStep 1567127 = 2350691) B2350691
theorem B3139991 : Blo 928581 3139991 := bstep (se 1 (by rfl) ⟨2354993, by rfl⟩ : syracuseStep 3139991 = 4709987) B4709987
theorem B1567255 : Blo 928581 1567255 := bstep (se 1 (by rfl) ⟨1175441, by rfl⟩ : syracuseStep 1567255 = 2350883) B2350883
theorem B2091545 : Blo 928581 2091545 := bstep (se 2 (by rfl) ⟨784329, by rfl⟩ : syracuseStep 2091545 = 1568659) B1568659
theorem B2091635 : Blo 928581 2091635 := bstep (se 1 (by rfl) ⟨1568726, by rfl⟩ : syracuseStep 2091635 = 3137453) B3137453
theorem B2091671 : Blo 928581 2091671 := bstep (se 1 (by rfl) ⟨1568753, by rfl⟩ : syracuseStep 2091671 = 3137507) B3137507
theorem B1764119 : Blo 928581 1764119 := bstep (se 1 (by rfl) ⟨1323089, by rfl⟩ : syracuseStep 1764119 = 2646179) B2646179
theorem B2091851 : Blo 928581 2091851 := bstep (se 1 (by rfl) ⟨1568888, by rfl⟩ : syracuseStep 2091851 = 3137777) B3137777
theorem B2091905 : Blo 928581 2091905 := bstep (se 2 (by rfl) ⟨784464, by rfl⟩ : syracuseStep 2091905 = 1568929) B1568929
theorem B7957399 : Blo 928581 7957399 := bstep (se 1 (by rfl) ⟨5968049, by rfl⟩ : syracuseStep 7957399 = 11936099) B11936099
theorem B3140531 : Blo 928581 3140531 := bstep (se 1 (by rfl) ⟨2355398, by rfl⟩ : syracuseStep 3140531 = 4710797) B4710797
theorem B2354123 : Blo 928581 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B3533827 : Blo 928581 3533827 := bstep (se 1 (by rfl) ⟨2650370, by rfl⟩ : syracuseStep 3533827 = 5300741) B5300741
theorem B2092121 : Blo 928581 2092121 := bstep (se 2 (by rfl) ⟨784545, by rfl⟩ : syracuseStep 2092121 = 1569091) B1569091
theorem B1567883 : Blo 928581 1567883 := bstep (se 1 (by rfl) ⟨1175912, by rfl⟩ : syracuseStep 1567883 = 2351825) B2351825
theorem B2092211 : Blo 928581 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B3140801 : Blo 928581 3140801 := bstep (se 2 (by rfl) ⟨1177800, by rfl⟩ : syracuseStep 3140801 = 2355601) B2355601
theorem B2092247 : Blo 928581 2092247 := bstep (se 1 (by rfl) ⟨1569185, by rfl⟩ : syracuseStep 2092247 = 3138371) B3138371
theorem B1568011 : Blo 928581 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B1764659 : Blo 928581 1764659 := bstep (se 1 (by rfl) ⟨1323494, by rfl⟩ : syracuseStep 1764659 = 2646989) B2646989
theorem B3534131 : Blo 928581 3534131 := bstep (se 1 (by rfl) ⟨2650598, by rfl⟩ : syracuseStep 3534131 = 5301197) B5301197
theorem B2092427 : Blo 928581 2092427 := bstep (se 1 (by rfl) ⟨1569320, by rfl⟩ : syracuseStep 2092427 = 3138641) B3138641
theorem B1568153 : Blo 928581 1568153 := bstep (se 2 (by rfl) ⟨588057, by rfl⟩ : syracuseStep 1568153 = 1176115) B1176115
theorem B2092481 : Blo 928581 2092481 := bstep (se 2 (by rfl) ⟨784680, by rfl⟩ : syracuseStep 2092481 = 1569361) B1569361
theorem B6712793 : Blo 928581 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B1568281 : Blo 928581 1568281 := bstep (se 2 (by rfl) ⟨588105, by rfl⟩ : syracuseStep 1568281 = 1176211) B1176211
theorem B2649665 : Blo 928581 2649665 := bstep (se 2 (by rfl) ⟨993624, by rfl⟩ : syracuseStep 2649665 = 1987249) B1987249
theorem B2092697 : Blo 928581 2092697 := bstep (se 2 (by rfl) ⟨784761, by rfl⟩ : syracuseStep 2092697 = 1569523) B1569523
theorem B2649779 : Blo 928581 2649779 := bstep (se 1 (by rfl) ⟨1987334, by rfl⟩ : syracuseStep 2649779 = 3974669) B3974669
theorem B3141341 : Blo 928581 3141341 := bstep (se 3 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 3141341 = 1178003) B1178003
theorem B2092787 : Blo 928581 2092787 := bstep (se 1 (by rfl) ⟨1569590, by rfl⟩ : syracuseStep 2092787 = 3139181) B3139181
theorem B2092823 : Blo 928581 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B1765145 : Blo 928581 1765145 := bstep (se 2 (by rfl) ⟨661929, by rfl⟩ : syracuseStep 1765145 = 1323859) B1323859
theorem B1863575 : Blo 928581 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B2355095 : Blo 928581 2355095 := bstep (se 1 (by rfl) ⟨1766321, by rfl⟩ : syracuseStep 2355095 = 3532643) B3532643
theorem B3534785 : Blo 928581 3534785 := bstep (se 2 (by rfl) ⟨1325544, by rfl⟩ : syracuseStep 3534785 = 2651089) B2651089
theorem B2093003 : Blo 928581 2093003 := bstep (se 1 (by rfl) ⟨1569752, by rfl⟩ : syracuseStep 2093003 = 3139505) B3139505
theorem B2093057 : Blo 928581 2093057 := bstep (se 2 (by rfl) ⟨784896, by rfl⟩ : syracuseStep 2093057 = 1569793) B1569793
theorem B1175563 : Blo 928581 1175563 := bstep (se 1 (by rfl) ⟨881672, by rfl⟩ : syracuseStep 1175563 = 1763345) B1763345
theorem B5304365 : Blo 928581 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B1568855 : Blo 928581 1568855 := bstep (se 1 (by rfl) ⟨1176641, by rfl⟩ : syracuseStep 1568855 = 2353283) B2353283
theorem B1568983 : Blo 928581 1568983 := bstep (se 1 (by rfl) ⟨1176737, by rfl⟩ : syracuseStep 1568983 = 2353475) B2353475
theorem B2093273 : Blo 928581 2093273 := bstep (se 2 (by rfl) ⟨784977, by rfl⟩ : syracuseStep 2093273 = 1569955) B1569955
theorem B1044715 : Blo 928581 1044715 := bstep (se 1 (by rfl) ⟨783536, by rfl⟩ : syracuseStep 1044715 = 1567073) B1567073
theorem B2093363 : Blo 928581 2093363 := bstep (se 1 (by rfl) ⟨1570022, by rfl⟩ : syracuseStep 2093363 = 3140045) B3140045
theorem B2388275 : Blo 928581 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1044823 : Blo 928581 1044823 := bstep (se 1 (by rfl) ⟨783617, by rfl⟩ : syracuseStep 1044823 = 1567235) B1567235
theorem B2093399 : Blo 928581 2093399 := bstep (se 1 (by rfl) ⟨1570049, by rfl⟩ : syracuseStep 2093399 = 3140099) B3140099
theorem B1045003 : Blo 928581 1045003 := bstep (se 1 (by rfl) ⟨783752, by rfl⟩ : syracuseStep 1045003 = 1567505) B1567505
theorem B2093579 : Blo 928581 2093579 := bstep (se 1 (by rfl) ⟨1570184, by rfl⟩ : syracuseStep 2093579 = 3140369) B3140369
theorem B2355763 : Blo 928581 2355763 := bstep (se 1 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 2355763 = 3533645) B3533645
theorem B2093633 : Blo 928581 2093633 := bstep (se 2 (by rfl) ⟨785112, by rfl⟩ : syracuseStep 2093633 = 1570225) B1570225
theorem B1045111 : Blo 928581 1045111 := bstep (se 1 (by rfl) ⟨783833, by rfl⟩ : syracuseStep 1045111 = 1567667) B1567667
theorem B2355905 : Blo 928581 2355905 := bstep (se 2 (by rfl) ⟨883464, by rfl⟩ : syracuseStep 2355905 = 1766929) B1766929
theorem B5960465 : Blo 928581 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B2093849 : Blo 928581 2093849 := bstep (se 2 (by rfl) ⟨785193, by rfl⟩ : syracuseStep 2093849 = 1570387) B1570387
theorem B1045291 : Blo 928581 1045291 := bstep (se 1 (by rfl) ⟨783968, by rfl⟩ : syracuseStep 1045291 = 1567937) B1567937
theorem B1569611 : Blo 928581 1569611 := bstep (se 1 (by rfl) ⟨1177208, by rfl⟩ : syracuseStep 1569611 = 2354417) B2354417
theorem B3142475 : Blo 928581 3142475 := bstep (se 1 (by rfl) ⟨2356856, by rfl⟩ : syracuseStep 3142475 = 4713713) B4713713
theorem B2093939 : Blo 928581 2093939 := bstep (se 1 (by rfl) ⟨1570454, by rfl⟩ : syracuseStep 2093939 = 3140909) B3140909
theorem B3765143 : Blo 928581 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B1045399 : Blo 928581 1045399 := bstep (se 1 (by rfl) ⟨784049, by rfl⟩ : syracuseStep 1045399 = 1568099) B1568099
theorem B2093975 : Blo 928581 2093975 := bstep (se 1 (by rfl) ⟨1570481, by rfl⟩ : syracuseStep 2093975 = 3140963) B3140963
theorem B1569739 : Blo 928581 1569739 := bstep (se 1 (by rfl) ⟨1177304, by rfl⟩ : syracuseStep 1569739 = 2354609) B2354609
theorem B1176535 : Blo 928581 1176535 := bstep (se 1 (by rfl) ⟨882401, by rfl⟩ : syracuseStep 1176535 = 1764803) B1764803
theorem B1340491 : Blo 928581 1340491 := bstep (se 1 (by rfl) ⟨1005368, by rfl⟩ : syracuseStep 1340491 = 2010737) B2010737
theorem B1045579 : Blo 928581 1045579 := bstep (se 1 (by rfl) ⟨784184, by rfl⟩ : syracuseStep 1045579 = 1568369) B1568369
theorem B2094155 : Blo 928581 2094155 := bstep (se 1 (by rfl) ⟨1570616, by rfl⟩ : syracuseStep 2094155 = 3141233) B3141233
theorem B1569881 : Blo 928581 1569881 := bstep (se 2 (by rfl) ⟨588705, by rfl⟩ : syracuseStep 1569881 = 1177411) B1177411
theorem B3142745 : Blo 928581 3142745 := bstep (se 2 (by rfl) ⟨1178529, by rfl⟩ : syracuseStep 3142745 = 2357059) B2357059
theorem B2094209 : Blo 928581 2094209 := bstep (se 2 (by rfl) ⟨785328, by rfl⟩ : syracuseStep 2094209 = 1570657) B1570657
theorem B10613911 : Blo 928581 10613911 := bstep (se 1 (by rfl) ⟨7960433, by rfl⟩ : syracuseStep 10613911 = 15920867) B15920867
theorem B3536045 : Blo 928581 3536045 := bstep (se 3 (by rfl) ⟨663008, by rfl⟩ : syracuseStep 3536045 = 1326017) B1326017
theorem B51573941 : Blo 928581 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B1045687 : Blo 928581 1045687 := bstep (se 1 (by rfl) ⟨784265, by rfl⟩ : syracuseStep 1045687 = 1568531) B1568531
theorem B1766603 : Blo 928581 1766603 := bstep (se 1 (by rfl) ⟨1324952, by rfl⟩ : syracuseStep 1766603 = 2649905) B2649905
theorem B3536075 : Blo 928581 3536075 := bstep (se 1 (by rfl) ⟨2652056, by rfl⟩ : syracuseStep 3536075 = 5304113) B5304113
theorem B1570009 : Blo 928581 1570009 := bstep (se 2 (by rfl) ⟨588753, by rfl⟩ : syracuseStep 1570009 = 1177507) B1177507
theorem B2094425 : Blo 928581 2094425 := bstep (se 2 (by rfl) ⟨785409, by rfl⟩ : syracuseStep 2094425 = 1570819) B1570819
theorem B1045867 : Blo 928581 1045867 := bstep (se 1 (by rfl) ⟨784400, by rfl⟩ : syracuseStep 1045867 = 1568801) B1568801
theorem B1766785 : Blo 928581 1766785 := bstep (se 2 (by rfl) ⟨662544, by rfl⟩ : syracuseStep 1766785 = 1325089) B1325089
theorem B2094515 : Blo 928581 2094515 := bstep (se 1 (by rfl) ⟨1570886, by rfl⟩ : syracuseStep 2094515 = 3141773) B3141773
theorem B1045975 : Blo 928581 1045975 := bstep (se 1 (by rfl) ⟨784481, by rfl⟩ : syracuseStep 1045975 = 1568963) B1568963
theorem B2094551 : Blo 928581 2094551 := bstep (se 1 (by rfl) ⟨1570913, by rfl⟩ : syracuseStep 2094551 = 3141827) B3141827
theorem B1046155 : Blo 928581 1046155 := bstep (se 1 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 1046155 = 1569233) B1569233
theorem B2094731 : Blo 928581 2094731 := bstep (se 1 (by rfl) ⟨1571048, by rfl⟩ : syracuseStep 2094731 = 3142097) B3142097
theorem B2094785 : Blo 928581 2094785 := bstep (se 2 (by rfl) ⟨785544, by rfl⟩ : syracuseStep 2094785 = 1571089) B1571089
theorem B1046263 : Blo 928581 1046263 := bstep (se 1 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 1046263 = 1569395) B1569395
theorem B1177355 : Blo 928581 1177355 := bstep (se 1 (by rfl) ⟨883016, by rfl⟩ : syracuseStep 1177355 = 1766033) B1766033
theorem B4716305 : Blo 928581 4716305 := bstep (se 2 (by rfl) ⟨1768614, by rfl⟩ : syracuseStep 4716305 = 3537229) B3537229
theorem B1570583 : Blo 928581 1570583 := bstep (se 1 (by rfl) ⟨1177937, by rfl⟩ : syracuseStep 1570583 = 2355875) B2355875
theorem B3143447 : Blo 928581 3143447 := bstep (se 1 (by rfl) ⟨2357585, by rfl⟩ : syracuseStep 3143447 = 4715171) B4715171
theorem B1767233 : Blo 928581 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B3536729 : Blo 928581 3536729 := bstep (se 2 (by rfl) ⟨1326273, by rfl⟩ : syracuseStep 3536729 = 2652547) B2652547
theorem B1570711 : Blo 928581 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B1275799 : Blo 928581 1275799 := bstep (se 1 (by rfl) ⟨956849, by rfl⟩ : syracuseStep 1275799 = 1913699) B1913699
theorem B2095001 : Blo 928581 2095001 := bstep (se 2 (by rfl) ⟨785625, by rfl⟩ : syracuseStep 2095001 = 1571251) B1571251
theorem B1046443 : Blo 928581 1046443 := bstep (se 1 (by rfl) ⟨784832, by rfl⟩ : syracuseStep 1046443 = 1569665) B1569665
theorem B2357171 : Blo 928581 2357171 := bstep (se 1 (by rfl) ⟨1767878, by rfl⟩ : syracuseStep 2357171 = 3535757) B3535757
theorem B4716467 : Blo 928581 4716467 := bstep (se 1 (by rfl) ⟨3537350, by rfl⟩ : syracuseStep 4716467 = 7074701) B7074701
theorem B2095091 : Blo 928581 2095091 := bstep (se 1 (by rfl) ⟨1571318, by rfl⟩ : syracuseStep 2095091 = 3142637) B3142637
theorem B1046551 : Blo 928581 1046551 := bstep (se 1 (by rfl) ⟨784913, by rfl⟩ : syracuseStep 1046551 = 1569827) B1569827
theorem B2095127 : Blo 928581 2095127 := bstep (se 1 (by rfl) ⟨1571345, by rfl⟩ : syracuseStep 2095127 = 3142691) B3142691
theorem B1767575 : Blo 928581 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B3537047 : Blo 928581 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B1046731 : Blo 928581 1046731 := bstep (se 1 (by rfl) ⟨785048, by rfl⟩ : syracuseStep 1046731 = 1570097) B1570097
theorem B2095307 : Blo 928581 2095307 := bstep (se 1 (by rfl) ⟨1571480, by rfl⟩ : syracuseStep 2095307 = 3142961) B3142961
theorem B2095361 : Blo 928581 2095361 := bstep (se 2 (by rfl) ⟨785760, by rfl⟩ : syracuseStep 2095361 = 1571521) B1571521
theorem B3143987 : Blo 928581 3143987 := bstep (se 1 (by rfl) ⟨2357990, by rfl⟩ : syracuseStep 3143987 = 4715981) B4715981
theorem B1046839 : Blo 928581 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B5306755 : Blo 928581 5306755 := bstep (se 1 (by rfl) ⟨3980066, by rfl⟩ : syracuseStep 5306755 = 7960133) B7960133
theorem B1178059 : Blo 928581 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B2357707 : Blo 928581 2357707 := bstep (se 1 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 2357707 = 3536561) B3536561
theorem B2095577 : Blo 928581 2095577 := bstep (se 2 (by rfl) ⟨785841, by rfl⟩ : syracuseStep 2095577 = 1571683) B1571683
theorem B1047019 : Blo 928581 1047019 := bstep (se 1 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 1047019 = 1570529) B1570529
theorem B1571339 : Blo 928581 1571339 := bstep (se 1 (by rfl) ⟨1178504, by rfl⟩ : syracuseStep 1571339 = 2357009) B2357009
theorem B2652695 : Blo 928581 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B2095667 : Blo 928581 2095667 := bstep (se 1 (by rfl) ⟨1571750, by rfl⟩ : syracuseStep 2095667 = 3143501) B3143501
theorem B3144257 : Blo 928581 3144257 := bstep (se 2 (by rfl) ⟨1179096, by rfl⟩ : syracuseStep 3144257 = 2358193) B2358193
theorem B1047127 : Blo 928581 1047127 := bstep (se 1 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 1047127 = 1570691) B1570691
theorem B2095703 : Blo 928581 2095703 := bstep (se 1 (by rfl) ⟨1571777, by rfl⟩ : syracuseStep 2095703 = 3143555) B3143555
theorem B2357849 : Blo 928581 2357849 := bstep (se 2 (by rfl) ⟨884193, by rfl⟩ : syracuseStep 2357849 = 1768387) B1768387
theorem B1571467 : Blo 928581 1571467 := bstep (se 1 (by rfl) ⟨1178600, by rfl⟩ : syracuseStep 1571467 = 2357201) B2357201
theorem B1178327 : Blo 928581 1178327 := bstep (se 1 (by rfl) ⟨883745, by rfl⟩ : syracuseStep 1178327 = 1767491) B1767491
theorem B1047307 : Blo 928581 1047307 := bstep (se 1 (by rfl) ⟨785480, by rfl⟩ : syracuseStep 1047307 = 1570961) B1570961
theorem B2095883 : Blo 928581 2095883 := bstep (se 1 (by rfl) ⟨1571912, by rfl⟩ : syracuseStep 2095883 = 3143825) B3143825
theorem B3767057 : Blo 928581 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2980631 : Blo 928581 2980631 := bstep (se 1 (by rfl) ⟨2235473, by rfl⟩ : syracuseStep 2980631 = 4470947) B4470947
theorem B1571609 : Blo 928581 1571609 := bstep (se 2 (by rfl) ⟨589353, by rfl⟩ : syracuseStep 1571609 = 1178707) B1178707
theorem B6716195 : Blo 928581 6716195 := bstep (se 1 (by rfl) ⟨5037146, by rfl⟩ : syracuseStep 6716195 = 10074293) B10074293
theorem B1768243 : Blo 928581 1768243 := bstep (se 1 (by rfl) ⟨1326182, by rfl⟩ : syracuseStep 1768243 = 2652365) B2652365
theorem B3537715 : Blo 928581 3537715 := bstep (se 1 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 3537715 = 5306573) B5306573
theorem B2095937 : Blo 928581 2095937 := bstep (se 2 (by rfl) ⟨785976, by rfl⟩ : syracuseStep 2095937 = 1571953) B1571953
theorem B1047415 : Blo 928581 1047415 := bstep (se 1 (by rfl) ⟨785561, by rfl⟩ : syracuseStep 1047415 = 1571123) B1571123
theorem B1571737 : Blo 928581 1571737 := bstep (se 2 (by rfl) ⟨589401, by rfl⟩ : syracuseStep 1571737 = 1178803) B1178803
theorem B2096153 : Blo 928581 2096153 := bstep (se 2 (by rfl) ⟨786057, by rfl⟩ : syracuseStep 2096153 = 1572115) B1572115
theorem B1047595 : Blo 928581 1047595 := bstep (se 1 (by rfl) ⟨785696, by rfl⟩ : syracuseStep 1047595 = 1571393) B1571393
theorem B3144797 : Blo 928581 3144797 := bstep (se 3 (by rfl) ⟨589649, by rfl⟩ : syracuseStep 3144797 = 1179299) B1179299
theorem B2096243 : Blo 928581 2096243 := bstep (se 1 (by rfl) ⟨1572182, by rfl⟩ : syracuseStep 2096243 = 3144365) B3144365
theorem B1047703 : Blo 928581 1047703 := bstep (se 1 (by rfl) ⟨785777, by rfl⟩ : syracuseStep 1047703 = 1571555) B1571555
theorem B2096279 : Blo 928581 2096279 := bstep (se 1 (by rfl) ⟨1572209, by rfl⟩ : syracuseStep 2096279 = 3144419) B3144419
theorem B2391191 : Blo 928581 2391191 := bstep (se 1 (by rfl) ⟨1793393, by rfl⟩ : syracuseStep 2391191 = 3586787) B3586787
theorem B1768691 : Blo 928581 1768691 := bstep (se 1 (by rfl) ⟨1326518, by rfl⟩ : syracuseStep 1768691 = 2653037) B2653037
theorem B3767575 : Blo 928581 3767575 := bstep (se 1 (by rfl) ⟨2825681, by rfl⟩ : syracuseStep 3767575 = 5651363) B5651363
theorem B1768729 : Blo 928581 1768729 := bstep (se 2 (by rfl) ⟨663273, by rfl⟩ : syracuseStep 1768729 = 1326547) B1326547
theorem B5307713 : Blo 928581 5307713 := bstep (se 2 (by rfl) ⟨1990392, by rfl⟩ : syracuseStep 5307713 = 3980785) B3980785
theorem B1047883 : Blo 928581 1047883 := bstep (se 1 (by rfl) ⟨785912, by rfl⟩ : syracuseStep 1047883 = 1571825) B1571825
theorem B2096459 : Blo 928581 2096459 := bstep (se 1 (by rfl) ⟨1572344, by rfl⟩ : syracuseStep 2096459 = 3144689) B3144689
theorem B2096513 : Blo 928581 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B1179031 : Blo 928581 1179031 := bstep (se 1 (by rfl) ⟨884273, by rfl⟩ : syracuseStep 1179031 = 1768547) B1768547
theorem B2358679 : Blo 928581 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B1047991 : Blo 928581 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B1572311 : Blo 928581 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B13598225 : Blo 928581 13598225 := bstep (se 2 (by rfl) ⟨5099334, by rfl⟩ : syracuseStep 13598225 = 10198669) B10198669
theorem B1572439 : Blo 928581 1572439 := bstep (se 1 (by rfl) ⟨1179329, by rfl⟩ : syracuseStep 1572439 = 2358659) B2358659
theorem B2096729 : Blo 928581 2096729 := bstep (se 2 (by rfl) ⟨786273, by rfl⟩ : syracuseStep 2096729 = 1572547) B1572547
theorem B1048171 : Blo 928581 1048171 := bstep (se 1 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 1048171 = 1572257) B1572257
theorem B2096819 : Blo 928581 2096819 := bstep (se 1 (by rfl) ⟨1572614, by rfl⟩ : syracuseStep 2096819 = 3145229) B3145229
theorem B1048279 : Blo 928581 1048279 := bstep (se 1 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 1048279 = 1572419) B1572419
theorem B2096855 : Blo 928581 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B1769177 : Blo 928581 1769177 := bstep (se 2 (by rfl) ⟨663441, by rfl⟩ : syracuseStep 1769177 = 1326883) B1326883
theorem B2359115 : Blo 928581 2359115 := bstep (se 1 (by rfl) ⟨1769336, by rfl⟩ : syracuseStep 2359115 = 3538673) B3538673
theorem B4718411 : Blo 928581 4718411 := bstep (se 1 (by rfl) ⟨3538808, by rfl⟩ : syracuseStep 4718411 = 7077617) B7077617
theorem B1048459 : Blo 928581 1048459 := bstep (se 1 (by rfl) ⟨786344, by rfl⟩ : syracuseStep 1048459 = 1572689) B1572689
theorem B2097035 : Blo 928581 2097035 := bstep (se 1 (by rfl) ⟨1572776, by rfl⟩ : syracuseStep 2097035 = 3145553) B3145553
theorem B2097089 : Blo 928581 2097089 := bstep (se 2 (by rfl) ⟨786408, by rfl⟩ : syracuseStep 2097089 = 1572817) B1572817
theorem B1048567 : Blo 928581 1048567 := bstep (se 1 (by rfl) ⟨786425, by rfl⟩ : syracuseStep 1048567 = 1572851) B1572851
theorem B2359307 : Blo 928581 2359307 := bstep (se 1 (by rfl) ⟨1769480, by rfl⟩ : syracuseStep 2359307 = 3538961) B3538961
theorem B10354711 : Blo 928581 10354711 := bstep (se 1 (by rfl) ⟨7766033, by rfl⟩ : syracuseStep 10354711 = 15532067) B15532067
theorem B2097287 : Blo 928581 2097287 := bstep (se 1 (by rfl) ⟨1572965, by rfl⟩ : syracuseStep 2097287 = 3145931) B3145931
theorem B1048711 : Blo 928581 1048711 := bstep (se 1 (by rfl) ⟨786533, by rfl⟩ : syracuseStep 1048711 = 1573067) B1573067
theorem B10060013 : Blo 928581 10060013 := bstep (se 3 (by rfl) ⟨1886252, by rfl⟩ : syracuseStep 10060013 = 3772505) B3772505
theorem B3145985 : Blo 928581 3145985 := bstep (se 2 (by rfl) ⟨1179744, by rfl⟩ : syracuseStep 3145985 = 2359489) B2359489
theorem B1179947 : Blo 928581 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B2097467 : Blo 928581 2097467 := bstep (se 1 (by rfl) ⟨1573100, by rfl⟩ : syracuseStep 2097467 = 3146201) B3146201
theorem B1048891 : Blo 928581 1048891 := bstep (se 1 (by rfl) ⟨786668, by rfl⟩ : syracuseStep 1048891 = 1573337) B1573337
theorem B2097593 : Blo 928581 2097593 := bstep (se 2 (by rfl) ⟨786597, by rfl⟩ : syracuseStep 2097593 = 1573195) B1573195
theorem B1573391 : Blo 928581 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B1770103 : Blo 928581 1770103 := bstep (se 1 (by rfl) ⟨1327577, by rfl⟩ : syracuseStep 1770103 = 2655155) B2655155
theorem B2359955 : Blo 928581 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B2097935 : Blo 928581 2097935 := bstep (se 1 (by rfl) ⟨1573451, by rfl⟩ : syracuseStep 2097935 = 3146903) B3146903
theorem B2097953 : Blo 928581 2097953 := bstep (se 2 (by rfl) ⟨786732, by rfl⟩ : syracuseStep 2097953 = 1573465) B1573465
theorem B4719545 : Blo 928581 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B2360249 : Blo 928581 2360249 := bstep (se 2 (by rfl) ⟨885093, by rfl⟩ : syracuseStep 2360249 = 1770187) B1770187
theorem B3146795 : Blo 928581 3146795 := bstep (se 1 (by rfl) ⟨2360096, by rfl⟩ : syracuseStep 3146795 = 4720193) B4720193
theorem B2098295 : Blo 928581 2098295 := bstep (se 1 (by rfl) ⟨1573721, by rfl⟩ : syracuseStep 2098295 = 3147443) B3147443
theorem B171738481 : Blo 928581 171738481 := bstep (se 2 (by rfl) ⟨64401930, by rfl⟩ : syracuseStep 171738481 = 128803861) B128803861
theorem B11306425 : Blo 928581 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B5965771 : Blo 928581 5965771 := bstep (se 1 (by rfl) ⟨4474328, by rfl⟩ : syracuseStep 5965771 = 8948657) B8948657
theorem B1116175 : Blo 928581 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B4720841 : Blo 928581 4720841 := bstep (se 2 (by rfl) ⟨1770315, by rfl⟩ : syracuseStep 4720841 = 3540631) B3540631
theorem B11340091 : Blo 928581 11340091 := bstep (se 1 (by rfl) ⟨8505068, by rfl⟩ : syracuseStep 11340091 = 17010137) B17010137
theorem B11929949 : Blo 928581 11929949 := bstep (se 3 (by rfl) ⟨2236865, by rfl⟩ : syracuseStep 11929949 = 4473731) B4473731
theorem B20089235 : Blo 928581 20089235 := bstep (se 1 (by rfl) ⟨15066926, by rfl⟩ : syracuseStep 20089235 = 30133853) B30133853
theorem B4360823 : Blo 928581 4360823 := bstep (se 1 (by rfl) ⟨3270617, by rfl⟩ : syracuseStep 4360823 = 6541235) B6541235
theorem B1674017 : Blo 928581 1674017 := bstep (se 2 (by rfl) ⟨627756, by rfl⟩ : syracuseStep 1674017 = 1255513) B1255513
theorem B12716837 : Blo 928581 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B4525769 : Blo 928581 4525769 := bstep (se 2 (by rfl) ⟨1697163, by rfl⟩ : syracuseStep 4525769 = 3394327) B3394327
theorem B1117967 : Blo 928581 1117967 := bstep (se 1 (by rfl) ⟨838475, by rfl⟩ : syracuseStep 1117967 = 1676951) B1676951
theorem B5443379 : Blo 928581 5443379 := bstep (se 1 (by rfl) ⟨4082534, by rfl⟩ : syracuseStep 5443379 = 8165069) B8165069
theorem B32280371 : Blo 928581 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B1511227 : Blo 928581 1511227 := bstep (se 1 (by rfl) ⟨1133420, by rfl⟩ : syracuseStep 1511227 = 2266841) B2266841
theorem B7737367 : Blo 928581 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B1675819 : Blo 928581 1675819 := bstep (se 1 (by rfl) ⟨1256864, by rfl⟩ : syracuseStep 1675819 = 2513729) B2513729
theorem B2691731 : Blo 928581 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B1676065 : Blo 928581 1676065 := bstep (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) B1257049
theorem B13603619 : Blo 928581 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B2233175 : Blo 928581 2233175 := bstep (se 1 (by rfl) ⟨1674881, by rfl⟩ : syracuseStep 2233175 = 3349763) B3349763
theorem B2233867 : Blo 928581 2233867 := bstep (se 1 (by rfl) ⟨1675400, by rfl⟩ : syracuseStep 2233867 = 3350801) B3350801
theorem B2987563 : Blo 928581 2987563 := bstep (se 1 (by rfl) ⟨2240672, by rfl⟩ : syracuseStep 2987563 = 4481345) B4481345
theorem B2824055 : Blo 928581 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B2234483 : Blo 928581 2234483 := bstep (se 1 (by rfl) ⟨1675862, by rfl⟩ : syracuseStep 2234483 = 3351725) B3351725
theorem B8493761 : Blo 928581 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B3971987 : Blo 928581 3971987 := bstep (se 1 (by rfl) ⟨2978990, by rfl⟩ : syracuseStep 3971987 = 5957981) B5957981
theorem B4463873 : Blo 928581 4463873 := bstep (se 2 (by rfl) ⟨1673952, by rfl⟩ : syracuseStep 4463873 = 3347905) B3347905
theorem B3973643 : Blo 928581 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B2236943 : Blo 928581 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B5022269 : Blo 928581 5022269 := bstep (se 3 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 5022269 = 1883351) B1883351
theorem B2826937 : Blo 928581 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B11903705 : Blo 928581 11903705 := bstep (se 2 (by rfl) ⟨4463889, by rfl⟩ : syracuseStep 11903705 = 8927779) B8927779
theorem B34382627 : Blo 928581 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B2237711 : Blo 928581 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B5023433 : Blo 928581 5023433 := bstep (se 2 (by rfl) ⟨1883787, by rfl⟩ : syracuseStep 5023433 = 3767575) B3767575
theorem B11937739 : Blo 928581 11937739 := bstep (se 1 (by rfl) ⟨8953304, by rfl⟩ : syracuseStep 11937739 = 17906609) B17906609
theorem B8071483 : Blo 928581 8071483 := bstep (se 1 (by rfl) ⟨6053612, by rfl⟩ : syracuseStep 8071483 = 12107225) B12107225
theorem B4532665 : Blo 928581 4532665 := bstep (se 2 (by rfl) ⟨1699749, by rfl⟩ : syracuseStep 4532665 = 3399499) B3399499
theorem B2239019 : Blo 928581 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B23538437 : Blo 928581 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B928647 : Blo 928581 928647 := bstep (se 1 (by rfl) ⟨696485, by rfl⟩ : syracuseStep 928647 = 1392971) B1392971
theorem B928655 : Blo 928581 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B3779513 : Blo 928581 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B928699 : Blo 928581 928699 := bstep (se 1 (by rfl) ⟨696524, by rfl⟩ : syracuseStep 928699 = 1393049) B1393049
theorem B928775 : Blo 928581 928775 := bstep (se 1 (by rfl) ⟨696581, by rfl⟩ : syracuseStep 928775 = 1393163) B1393163
theorem B928783 : Blo 928581 928783 := bstep (se 1 (by rfl) ⟨696587, by rfl⟩ : syracuseStep 928783 = 1393175) B1393175
theorem B928827 : Blo 928581 928827 := bstep (se 1 (by rfl) ⟨696620, by rfl⟩ : syracuseStep 928827 = 1393241) B1393241
theorem B928903 : Blo 928581 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B928911 : Blo 928581 928911 := bstep (se 1 (by rfl) ⟨696683, by rfl⟩ : syracuseStep 928911 = 1393367) B1393367
theorem B928955 : Blo 928581 928955 := bstep (se 1 (by rfl) ⟨696716, by rfl⟩ : syracuseStep 928955 = 1393433) B1393433
theorem B929031 : Blo 928581 929031 := bstep (se 1 (by rfl) ⟨696773, by rfl⟩ : syracuseStep 929031 = 1393547) B1393547
theorem B929039 : Blo 928581 929039 := bstep (se 1 (by rfl) ⟨696779, by rfl⟩ : syracuseStep 929039 = 1393559) B1393559
theorem B929083 : Blo 928581 929083 := bstep (se 1 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 929083 = 1393625) B1393625
theorem B929159 : Blo 928581 929159 := bstep (se 1 (by rfl) ⟨696869, by rfl⟩ : syracuseStep 929159 = 1393739) B1393739
theorem B248491405 : Blo 928581 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B929167 : Blo 928581 929167 := bstep (se 1 (by rfl) ⟨696875, by rfl⟩ : syracuseStep 929167 = 1393751) B1393751
theorem B929211 : Blo 928581 929211 := bstep (se 1 (by rfl) ⟨696908, by rfl⟩ : syracuseStep 929211 = 1393817) B1393817
theorem B12758477 : Blo 928581 12758477 := bstep (se 3 (by rfl) ⟨2392214, by rfl⟩ : syracuseStep 12758477 = 4784429) B4784429
theorem B929287 : Blo 928581 929287 := bstep (se 1 (by rfl) ⟨696965, by rfl⟩ : syracuseStep 929287 = 1393931) B1393931
theorem B929295 : Blo 928581 929295 := bstep (se 1 (by rfl) ⟨696971, by rfl⟩ : syracuseStep 929295 = 1393943) B1393943
theorem B1289785 : Blo 928581 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B929339 : Blo 928581 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B929415 : Blo 928581 929415 := bstep (se 1 (by rfl) ⟨697061, by rfl⟩ : syracuseStep 929415 = 1394123) B1394123
theorem B929423 : Blo 928581 929423 := bstep (se 1 (by rfl) ⟨697067, by rfl⟩ : syracuseStep 929423 = 1394135) B1394135
theorem B929467 : Blo 928581 929467 := bstep (se 1 (by rfl) ⟨697100, by rfl⟩ : syracuseStep 929467 = 1394201) B1394201
theorem B929543 : Blo 928581 929543 := bstep (se 1 (by rfl) ⟨697157, by rfl⟩ : syracuseStep 929543 = 1394315) B1394315
theorem B929551 : Blo 928581 929551 := bstep (se 1 (by rfl) ⟨697163, by rfl⟩ : syracuseStep 929551 = 1394327) B1394327
theorem B929595 : Blo 928581 929595 := bstep (se 1 (by rfl) ⟨697196, by rfl⟩ : syracuseStep 929595 = 1394393) B1394393
theorem B929671 : Blo 928581 929671 := bstep (se 1 (by rfl) ⟨697253, by rfl⟩ : syracuseStep 929671 = 1394507) B1394507
theorem B929679 : Blo 928581 929679 := bstep (se 1 (by rfl) ⟨697259, by rfl⟩ : syracuseStep 929679 = 1394519) B1394519
theorem B929723 : Blo 928581 929723 := bstep (se 1 (by rfl) ⟨697292, by rfl⟩ : syracuseStep 929723 = 1394585) B1394585
theorem B929799 : Blo 928581 929799 := bstep (se 1 (by rfl) ⟨697349, by rfl⟩ : syracuseStep 929799 = 1394699) B1394699
theorem B929807 : Blo 928581 929807 := bstep (se 1 (by rfl) ⟨697355, by rfl⟩ : syracuseStep 929807 = 1394711) B1394711
theorem B1323067 : Blo 928581 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B929851 : Blo 928581 929851 := bstep (se 1 (by rfl) ⟨697388, by rfl⟩ : syracuseStep 929851 = 1394777) B1394777
theorem B929927 : Blo 928581 929927 := bstep (se 1 (by rfl) ⟨697445, by rfl⟩ : syracuseStep 929927 = 1394891) B1394891
theorem B929935 : Blo 928581 929935 := bstep (se 1 (by rfl) ⟨697451, by rfl⟩ : syracuseStep 929935 = 1394903) B1394903
theorem B1257643 : Blo 928581 1257643 := bstep (se 1 (by rfl) ⟨943232, by rfl⟩ : syracuseStep 1257643 = 1886465) B1886465
theorem B929979 : Blo 928581 929979 := bstep (se 1 (by rfl) ⟨697484, by rfl⟩ : syracuseStep 929979 = 1394969) B1394969
theorem B930055 : Blo 928581 930055 := bstep (se 1 (by rfl) ⟨697541, by rfl⟩ : syracuseStep 930055 = 1395083) B1395083
theorem B930063 : Blo 928581 930063 := bstep (se 1 (by rfl) ⟨697547, by rfl⟩ : syracuseStep 930063 = 1395095) B1395095
theorem B930107 : Blo 928581 930107 := bstep (se 1 (by rfl) ⟨697580, by rfl⟩ : syracuseStep 930107 = 1395161) B1395161
theorem B930183 : Blo 928581 930183 := bstep (se 1 (by rfl) ⟨697637, by rfl⟩ : syracuseStep 930183 = 1395275) B1395275
theorem B10596743 : Blo 928581 10596743 := bstep (se 1 (by rfl) ⟨7947557, by rfl⟩ : syracuseStep 10596743 = 15895115) B15895115
theorem B930191 : Blo 928581 930191 := bstep (se 1 (by rfl) ⟨697643, by rfl⟩ : syracuseStep 930191 = 1395287) B1395287
theorem B930235 : Blo 928581 930235 := bstep (se 1 (by rfl) ⟨697676, by rfl⟩ : syracuseStep 930235 = 1395353) B1395353
theorem B4469195 : Blo 928581 4469195 := bstep (se 1 (by rfl) ⟨3351896, by rfl⟩ : syracuseStep 4469195 = 6703793) B6703793
theorem B18133465 : Blo 928581 18133465 := bstep (se 2 (by rfl) ⟨6800049, by rfl⟩ : syracuseStep 18133465 = 13600099) B13600099
theorem B930311 : Blo 928581 930311 := bstep (se 1 (by rfl) ⟨697733, by rfl⟩ : syracuseStep 930311 = 1395467) B1395467
theorem B930319 : Blo 928581 930319 := bstep (se 1 (by rfl) ⟨697739, by rfl⟩ : syracuseStep 930319 = 1395479) B1395479
theorem B930363 : Blo 928581 930363 := bstep (se 1 (by rfl) ⟨697772, by rfl⟩ : syracuseStep 930363 = 1395545) B1395545
theorem B930439 : Blo 928581 930439 := bstep (se 1 (by rfl) ⟨697829, by rfl⟩ : syracuseStep 930439 = 1395659) B1395659
theorem B930447 : Blo 928581 930447 := bstep (se 1 (by rfl) ⟨697835, by rfl⟩ : syracuseStep 930447 = 1395671) B1395671
theorem B930491 : Blo 928581 930491 := bstep (se 1 (by rfl) ⟨697868, by rfl⟩ : syracuseStep 930491 = 1395737) B1395737
theorem B7058177 : Blo 928581 7058177 := bstep (se 2 (by rfl) ⟨2646816, by rfl⟩ : syracuseStep 7058177 = 5293633) B5293633
theorem B930567 : Blo 928581 930567 := bstep (se 1 (by rfl) ⟨697925, by rfl⟩ : syracuseStep 930567 = 1395851) B1395851
theorem B930575 : Blo 928581 930575 := bstep (se 1 (by rfl) ⟨697931, by rfl⟩ : syracuseStep 930575 = 1395863) B1395863
theorem B3978017 : Blo 928581 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B5649203 : Blo 928581 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B930619 : Blo 928581 930619 := bstep (se 1 (by rfl) ⟨697964, by rfl⟩ : syracuseStep 930619 = 1395929) B1395929
theorem B1192823 : Blo 928581 1192823 := bstep (se 1 (by rfl) ⟨894617, by rfl⟩ : syracuseStep 1192823 = 1789235) B1789235
theorem B930695 : Blo 928581 930695 := bstep (se 1 (by rfl) ⟨698021, by rfl⟩ : syracuseStep 930695 = 1396043) B1396043
theorem B930703 : Blo 928581 930703 := bstep (se 1 (by rfl) ⟨698027, by rfl⟩ : syracuseStep 930703 = 1396055) B1396055
theorem B930747 : Blo 928581 930747 := bstep (se 1 (by rfl) ⟨698060, by rfl⟩ : syracuseStep 930747 = 1396121) B1396121
theorem B8958923 : Blo 928581 8958923 := bstep (se 1 (by rfl) ⟨6719192, by rfl⟩ : syracuseStep 8958923 = 13438385) B13438385
theorem B930823 : Blo 928581 930823 := bstep (se 1 (by rfl) ⟨698117, by rfl⟩ : syracuseStep 930823 = 1396235) B1396235
theorem B930831 : Blo 928581 930831 := bstep (se 1 (by rfl) ⟨698123, by rfl⟩ : syracuseStep 930831 = 1396247) B1396247
theorem B930875 : Blo 928581 930875 := bstep (se 1 (by rfl) ⟨698156, by rfl⟩ : syracuseStep 930875 = 1396313) B1396313
theorem B10040381 : Blo 928581 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B3978359 : Blo 928581 3978359 := bstep (se 1 (by rfl) ⟨2983769, by rfl⟩ : syracuseStep 3978359 = 5967539) B5967539
theorem B930951 : Blo 928581 930951 := bstep (se 1 (by rfl) ⟨698213, by rfl⟩ : syracuseStep 930951 = 1396427) B1396427
theorem B930959 : Blo 928581 930959 := bstep (se 1 (by rfl) ⟨698219, by rfl⟩ : syracuseStep 930959 = 1396439) B1396439
theorem B931003 : Blo 928581 931003 := bstep (se 1 (by rfl) ⟨698252, by rfl⟩ : syracuseStep 931003 = 1396505) B1396505
theorem B931079 : Blo 928581 931079 := bstep (se 1 (by rfl) ⟨698309, by rfl⟩ : syracuseStep 931079 = 1396619) B1396619
theorem B931087 : Blo 928581 931087 := bstep (se 1 (by rfl) ⟨698315, by rfl⟩ : syracuseStep 931087 = 1396631) B1396631
theorem B931131 : Blo 928581 931131 := bstep (se 1 (by rfl) ⟨698348, by rfl⟩ : syracuseStep 931131 = 1396697) B1396697
theorem B931207 : Blo 928581 931207 := bstep (se 1 (by rfl) ⟨698405, by rfl⟩ : syracuseStep 931207 = 1396811) B1396811
theorem B931215 : Blo 928581 931215 := bstep (se 1 (by rfl) ⟨698411, by rfl⟩ : syracuseStep 931215 = 1396823) B1396823
theorem B931259 : Blo 928581 931259 := bstep (se 1 (by rfl) ⟨698444, by rfl⟩ : syracuseStep 931259 = 1396889) B1396889
theorem B931335 : Blo 928581 931335 := bstep (se 1 (by rfl) ⟨698501, by rfl⟩ : syracuseStep 931335 = 1397003) B1397003
theorem B1324559 : Blo 928581 1324559 := bstep (se 1 (by rfl) ⟨993419, by rfl⟩ : syracuseStep 1324559 = 1986839) B1986839
theorem B931343 : Blo 928581 931343 := bstep (se 1 (by rfl) ⟨698507, by rfl⟩ : syracuseStep 931343 = 1397015) B1397015
theorem B8599069 : Blo 928581 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B931387 : Blo 928581 931387 := bstep (se 1 (by rfl) ⟨698540, by rfl⟩ : syracuseStep 931387 = 1397081) B1397081
theorem B5289533 : Blo 928581 5289533 := bstep (se 3 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 5289533 = 1983575) B1983575
theorem B931463 : Blo 928581 931463 := bstep (se 1 (by rfl) ⟨698597, by rfl⟩ : syracuseStep 931463 = 1397195) B1397195
theorem B931471 : Blo 928581 931471 := bstep (se 1 (by rfl) ⟨698603, by rfl⟩ : syracuseStep 931471 = 1397207) B1397207
theorem B931515 : Blo 928581 931515 := bstep (se 1 (by rfl) ⟨698636, by rfl⟩ : syracuseStep 931515 = 1397273) B1397273
theorem B931591 : Blo 928581 931591 := bstep (se 1 (by rfl) ⟨698693, by rfl⟩ : syracuseStep 931591 = 1397387) B1397387
theorem B931599 : Blo 928581 931599 := bstep (se 1 (by rfl) ⟨698699, by rfl⟩ : syracuseStep 931599 = 1397399) B1397399
theorem B931643 : Blo 928581 931643 := bstep (se 1 (by rfl) ⟨698732, by rfl⟩ : syracuseStep 931643 = 1397465) B1397465
theorem B28686149 : Blo 928581 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B29407093 : Blo 928581 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B931719 : Blo 928581 931719 := bstep (se 1 (by rfl) ⟨698789, by rfl⟩ : syracuseStep 931719 = 1397579) B1397579
theorem B931727 : Blo 928581 931727 := bstep (se 1 (by rfl) ⟨698795, by rfl⟩ : syracuseStep 931727 = 1397591) B1397591
theorem B931771 : Blo 928581 931771 := bstep (se 1 (by rfl) ⟨698828, by rfl⟩ : syracuseStep 931771 = 1397657) B1397657
theorem B931847 : Blo 928581 931847 := bstep (se 1 (by rfl) ⟨698885, by rfl⟩ : syracuseStep 931847 = 1397771) B1397771
theorem B8927243 : Blo 928581 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B931855 : Blo 928581 931855 := bstep (se 1 (by rfl) ⟨698891, by rfl⟩ : syracuseStep 931855 = 1397783) B1397783
theorem B931899 : Blo 928581 931899 := bstep (se 1 (by rfl) ⟨698924, by rfl⟩ : syracuseStep 931899 = 1397849) B1397849
theorem B931975 : Blo 928581 931975 := bstep (se 1 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 931975 = 1397963) B1397963
theorem B931983 : Blo 928581 931983 := bstep (se 1 (by rfl) ⟨698987, by rfl⟩ : syracuseStep 931983 = 1397975) B1397975
theorem B932027 : Blo 928581 932027 := bstep (se 1 (by rfl) ⟨699020, by rfl⟩ : syracuseStep 932027 = 1398041) B1398041
theorem B932103 : Blo 928581 932103 := bstep (se 1 (by rfl) ⟨699077, by rfl⟩ : syracuseStep 932103 = 1398155) B1398155
theorem B932111 : Blo 928581 932111 := bstep (se 1 (by rfl) ⟨699083, by rfl⟩ : syracuseStep 932111 = 1398167) B1398167
theorem B932155 : Blo 928581 932155 := bstep (se 1 (by rfl) ⟨699116, by rfl⟩ : syracuseStep 932155 = 1398233) B1398233
theorem B932231 : Blo 928581 932231 := bstep (se 1 (by rfl) ⟨699173, by rfl⟩ : syracuseStep 932231 = 1398347) B1398347
theorem B932239 : Blo 928581 932239 := bstep (se 1 (by rfl) ⟨699179, by rfl⟩ : syracuseStep 932239 = 1398359) B1398359
theorem B932283 : Blo 928581 932283 := bstep (se 1 (by rfl) ⟨699212, by rfl⟩ : syracuseStep 932283 = 1398425) B1398425
theorem B932359 : Blo 928581 932359 := bstep (se 1 (by rfl) ⟨699269, by rfl⟩ : syracuseStep 932359 = 1398539) B1398539
theorem B932367 : Blo 928581 932367 := bstep (se 1 (by rfl) ⟨699275, by rfl⟩ : syracuseStep 932367 = 1398551) B1398551
theorem B932411 : Blo 928581 932411 := bstep (se 1 (by rfl) ⟨699308, by rfl⟩ : syracuseStep 932411 = 1398617) B1398617
theorem B1325641 : Blo 928581 1325641 := bstep (se 2 (by rfl) ⟨497115, by rfl⟩ : syracuseStep 1325641 = 994231) B994231
theorem B932487 : Blo 928581 932487 := bstep (se 1 (by rfl) ⟨699365, by rfl⟩ : syracuseStep 932487 = 1398731) B1398731
theorem B932495 : Blo 928581 932495 := bstep (se 1 (by rfl) ⟨699371, by rfl⟩ : syracuseStep 932495 = 1398743) B1398743
theorem B1325755 : Blo 928581 1325755 := bstep (se 1 (by rfl) ⟨994316, by rfl⟩ : syracuseStep 1325755 = 1988633) B1988633
theorem B932539 : Blo 928581 932539 := bstep (se 1 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 932539 = 1398809) B1398809
theorem B40811525 : Blo 928581 40811525 := bstep (se 4 (by rfl) ⟨3826080, by rfl⟩ : syracuseStep 40811525 = 7652161) B7652161
theorem B5651657 : Blo 928581 5651657 := bstep (se 2 (by rfl) ⟨2119371, by rfl⟩ : syracuseStep 5651657 = 4238743) B4238743
theorem B1490219 : Blo 928581 1490219 := bstep (se 1 (by rfl) ⟨1117664, by rfl⟩ : syracuseStep 1490219 = 2235329) B2235329
theorem B4701725 : Blo 928581 4701725 := bstep (se 3 (by rfl) ⟨881573, by rfl⟩ : syracuseStep 4701725 = 1763147) B1763147
theorem B4898333 : Blo 928581 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B5029577 : Blo 928581 5029577 := bstep (se 2 (by rfl) ⟨1886091, by rfl⟩ : syracuseStep 5029577 = 3772183) B3772183
theorem B6045529 : Blo 928581 6045529 := bstep (se 2 (by rfl) ⟨2267073, by rfl⟩ : syracuseStep 6045529 = 4534147) B4534147
theorem B4702211 : Blo 928581 4702211 := bstep (se 1 (by rfl) ⟨3526658, by rfl⟩ : syracuseStep 4702211 = 7053317) B7053317
theorem B8503319 : Blo 928581 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B1392887 : Blo 928581 1392887 := bstep (se 1 (by rfl) ⟨1044665, by rfl⟩ : syracuseStep 1392887 = 2089331) B2089331
theorem B1327367 : Blo 928581 1327367 := bstep (se 1 (by rfl) ⟨995525, by rfl⟩ : syracuseStep 1327367 = 1991051) B1991051
theorem B1392911 : Blo 928581 1392911 := bstep (se 1 (by rfl) ⟨1044683, by rfl⟩ : syracuseStep 1392911 = 2089367) B2089367
theorem B1392953 : Blo 928581 1392953 := bstep (se 2 (by rfl) ⟨522357, by rfl⟩ : syracuseStep 1392953 = 1044715) B1044715
theorem B1393031 : Blo 928581 1393031 := bstep (se 1 (by rfl) ⟨1044773, by rfl⟩ : syracuseStep 1393031 = 2089547) B2089547
theorem B1393067 : Blo 928581 1393067 := bstep (se 1 (by rfl) ⟨1044800, by rfl⟩ : syracuseStep 1393067 = 2089601) B2089601
theorem B1393097 : Blo 928581 1393097 := bstep (se 2 (by rfl) ⟨522411, by rfl⟩ : syracuseStep 1393097 = 1044823) B1044823
theorem B5030353 : Blo 928581 5030353 := bstep (se 2 (by rfl) ⟨1886382, by rfl⟩ : syracuseStep 5030353 = 3772765) B3772765
theorem B1393211 : Blo 928581 1393211 := bstep (se 1 (by rfl) ⟨1044908, by rfl⟩ : syracuseStep 1393211 = 2089817) B2089817
theorem B1393271 : Blo 928581 1393271 := bstep (se 1 (by rfl) ⟨1044953, by rfl⟩ : syracuseStep 1393271 = 2089907) B2089907
theorem B4473463 : Blo 928581 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B3588727 : Blo 928581 3588727 := bstep (se 1 (by rfl) ⟨2691545, by rfl⟩ : syracuseStep 3588727 = 5383091) B5383091
theorem B1393295 : Blo 928581 1393295 := bstep (se 1 (by rfl) ⟨1044971, by rfl⟩ : syracuseStep 1393295 = 2089943) B2089943
theorem B1393337 : Blo 928581 1393337 := bstep (se 2 (by rfl) ⟨522501, by rfl⟩ : syracuseStep 1393337 = 1045003) B1045003
theorem B1393415 : Blo 928581 1393415 := bstep (se 1 (by rfl) ⟨1045061, by rfl⟩ : syracuseStep 1393415 = 2090123) B2090123
theorem B1393451 : Blo 928581 1393451 := bstep (se 1 (by rfl) ⟨1045088, by rfl⟩ : syracuseStep 1393451 = 2090177) B2090177
theorem B1393481 : Blo 928581 1393481 := bstep (se 2 (by rfl) ⟨522555, by rfl⟩ : syracuseStep 1393481 = 1045111) B1045111
theorem B1393595 : Blo 928581 1393595 := bstep (se 1 (by rfl) ⟨1045196, by rfl⟩ : syracuseStep 1393595 = 2090393) B2090393
theorem B1393655 : Blo 928581 1393655 := bstep (se 1 (by rfl) ⟨1045241, by rfl⟩ : syracuseStep 1393655 = 2090483) B2090483
theorem B1393679 : Blo 928581 1393679 := bstep (se 1 (by rfl) ⟨1045259, by rfl⟩ : syracuseStep 1393679 = 2090519) B2090519
theorem B7062551 : Blo 928581 7062551 := bstep (se 1 (by rfl) ⟨5296913, by rfl⟩ : syracuseStep 7062551 = 10593827) B10593827
theorem B1393721 : Blo 928581 1393721 := bstep (se 2 (by rfl) ⟨522645, by rfl⟩ : syracuseStep 1393721 = 1045291) B1045291
theorem B1393799 : Blo 928581 1393799 := bstep (se 1 (by rfl) ⟨1045349, by rfl⟩ : syracuseStep 1393799 = 2090699) B2090699
theorem B1393835 : Blo 928581 1393835 := bstep (se 1 (by rfl) ⟨1045376, by rfl⟩ : syracuseStep 1393835 = 2090753) B2090753
theorem B1393865 : Blo 928581 1393865 := bstep (se 2 (by rfl) ⟨522699, by rfl⟩ : syracuseStep 1393865 = 1045399) B1045399
theorem B1393979 : Blo 928581 1393979 := bstep (se 1 (by rfl) ⟨1045484, by rfl⟩ : syracuseStep 1393979 = 2090969) B2090969
theorem B1394039 : Blo 928581 1394039 := bstep (se 1 (by rfl) ⟨1045529, by rfl⟩ : syracuseStep 1394039 = 2091059) B2091059
theorem B1394063 : Blo 928581 1394063 := bstep (se 1 (by rfl) ⟨1045547, by rfl⟩ : syracuseStep 1394063 = 2091095) B2091095
theorem B1787321 : Blo 928581 1787321 := bstep (se 2 (by rfl) ⟨670245, by rfl⟩ : syracuseStep 1787321 = 1340491) B1340491
theorem B1394105 : Blo 928581 1394105 := bstep (se 2 (by rfl) ⟨522789, by rfl⟩ : syracuseStep 1394105 = 1045579) B1045579
theorem B1394183 : Blo 928581 1394183 := bstep (se 1 (by rfl) ⟨1045637, by rfl⟩ : syracuseStep 1394183 = 2091275) B2091275
theorem B1394219 : Blo 928581 1394219 := bstep (se 1 (by rfl) ⟨1045664, by rfl⟩ : syracuseStep 1394219 = 2091329) B2091329
theorem B1394249 : Blo 928581 1394249 := bstep (se 2 (by rfl) ⟨522843, by rfl⟩ : syracuseStep 1394249 = 1045687) B1045687
theorem B4703831 : Blo 928581 4703831 := bstep (se 1 (by rfl) ⟨3527873, by rfl⟩ : syracuseStep 4703831 = 7055747) B7055747
theorem B4474541 : Blo 928581 4474541 := bstep (se 3 (by rfl) ⟨838976, by rfl⟩ : syracuseStep 4474541 = 1677953) B1677953
theorem B1394363 : Blo 928581 1394363 := bstep (se 1 (by rfl) ⟨1045772, by rfl⟩ : syracuseStep 1394363 = 2091545) B2091545
theorem B1394423 : Blo 928581 1394423 := bstep (se 1 (by rfl) ⟨1045817, by rfl⟩ : syracuseStep 1394423 = 2091635) B2091635
theorem B1394447 : Blo 928581 1394447 := bstep (se 1 (by rfl) ⟨1045835, by rfl⟩ : syracuseStep 1394447 = 2091671) B2091671
theorem B1394489 : Blo 928581 1394489 := bstep (se 2 (by rfl) ⟨522933, by rfl⟩ : syracuseStep 1394489 = 1045867) B1045867
theorem B8931161 : Blo 928581 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B1394567 : Blo 928581 1394567 := bstep (se 1 (by rfl) ⟨1045925, by rfl⟩ : syracuseStep 1394567 = 2091851) B2091851
theorem B1394603 : Blo 928581 1394603 := bstep (se 1 (by rfl) ⟨1045952, by rfl⟩ : syracuseStep 1394603 = 2091905) B2091905
theorem B1394633 : Blo 928581 1394633 := bstep (se 2 (by rfl) ⟨522987, by rfl⟩ : syracuseStep 1394633 = 1045975) B1045975
theorem B1394747 : Blo 928581 1394747 := bstep (se 1 (by rfl) ⟨1046060, by rfl⟩ : syracuseStep 1394747 = 2092121) B2092121
theorem B4704317 : Blo 928581 4704317 := bstep (se 3 (by rfl) ⟨882059, by rfl⟩ : syracuseStep 4704317 = 1764119) B1764119
theorem B1394807 : Blo 928581 1394807 := bstep (se 1 (by rfl) ⟨1046105, by rfl⟩ : syracuseStep 1394807 = 2092211) B2092211
theorem B1394831 : Blo 928581 1394831 := bstep (se 1 (by rfl) ⟨1046123, by rfl⟩ : syracuseStep 1394831 = 2092247) B2092247
theorem B1394873 : Blo 928581 1394873 := bstep (se 2 (by rfl) ⟨523077, by rfl⟩ : syracuseStep 1394873 = 1046155) B1046155
theorem B1394951 : Blo 928581 1394951 := bstep (se 1 (by rfl) ⟨1046213, by rfl⟩ : syracuseStep 1394951 = 2092427) B2092427
theorem B1394987 : Blo 928581 1394987 := bstep (se 1 (by rfl) ⟨1046240, by rfl⟩ : syracuseStep 1394987 = 2092481) B2092481
theorem B4475195 : Blo 928581 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B1395017 : Blo 928581 1395017 := bstep (se 2 (by rfl) ⟨523131, by rfl⟩ : syracuseStep 1395017 = 1046263) B1046263
theorem B1395131 : Blo 928581 1395131 := bstep (se 1 (by rfl) ⟨1046348, by rfl⟩ : syracuseStep 1395131 = 2092697) B2092697
theorem B1395191 : Blo 928581 1395191 := bstep (se 1 (by rfl) ⟨1046393, by rfl⟩ : syracuseStep 1395191 = 2092787) B2092787
theorem B1395215 : Blo 928581 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B1395257 : Blo 928581 1395257 := bstep (se 2 (by rfl) ⟨523221, by rfl⟩ : syracuseStep 1395257 = 1046443) B1046443
theorem B1395335 : Blo 928581 1395335 := bstep (se 1 (by rfl) ⟨1046501, by rfl⟩ : syracuseStep 1395335 = 2093003) B2093003
theorem B1395371 : Blo 928581 1395371 := bstep (se 1 (by rfl) ⟨1046528, by rfl⟩ : syracuseStep 1395371 = 2093057) B2093057
theorem B1395401 : Blo 928581 1395401 := bstep (se 2 (by rfl) ⟨523275, by rfl⟩ : syracuseStep 1395401 = 1046551) B1046551
theorem B1395515 : Blo 928581 1395515 := bstep (se 1 (by rfl) ⟨1046636, by rfl⟩ : syracuseStep 1395515 = 2093273) B2093273
theorem B1395575 : Blo 928581 1395575 := bstep (se 1 (by rfl) ⟨1046681, by rfl⟩ : syracuseStep 1395575 = 2093363) B2093363
theorem B1592183 : Blo 928581 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B1395599 : Blo 928581 1395599 := bstep (se 1 (by rfl) ⟨1046699, by rfl⟩ : syracuseStep 1395599 = 2093399) B2093399
theorem B1395641 : Blo 928581 1395641 := bstep (se 2 (by rfl) ⟨523365, by rfl⟩ : syracuseStep 1395641 = 1046731) B1046731
theorem B1395719 : Blo 928581 1395719 := bstep (se 1 (by rfl) ⟨1046789, by rfl⟩ : syracuseStep 1395719 = 2093579) B2093579
theorem B1395755 : Blo 928581 1395755 := bstep (se 1 (by rfl) ⟨1046816, by rfl⟩ : syracuseStep 1395755 = 2093633) B2093633
theorem B1395785 : Blo 928581 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B1395899 : Blo 928581 1395899 := bstep (se 1 (by rfl) ⟨1046924, by rfl⟩ : syracuseStep 1395899 = 2093849) B2093849
theorem B3525869 : Blo 928581 3525869 := bstep (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) B1322201
theorem B1395959 : Blo 928581 1395959 := bstep (se 1 (by rfl) ⟨1046969, by rfl⟩ : syracuseStep 1395959 = 2093939) B2093939
theorem B1395983 : Blo 928581 1395983 := bstep (se 1 (by rfl) ⟨1046987, by rfl⟩ : syracuseStep 1395983 = 2093975) B2093975
theorem B1396025 : Blo 928581 1396025 := bstep (se 2 (by rfl) ⟨523509, by rfl⟩ : syracuseStep 1396025 = 1047019) B1047019
theorem B1396103 : Blo 928581 1396103 := bstep (se 1 (by rfl) ⟨1047077, by rfl⟩ : syracuseStep 1396103 = 2094155) B2094155
theorem B1396139 : Blo 928581 1396139 := bstep (se 1 (by rfl) ⟨1047104, by rfl⟩ : syracuseStep 1396139 = 2094209) B2094209
theorem B1396169 : Blo 928581 1396169 := bstep (se 2 (by rfl) ⟨523563, by rfl⟩ : syracuseStep 1396169 = 1047127) B1047127
theorem B2018849 : Blo 928581 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B1396283 : Blo 928581 1396283 := bstep (se 1 (by rfl) ⟨1047212, by rfl⟩ : syracuseStep 1396283 = 2094425) B2094425
theorem B1396343 : Blo 928581 1396343 := bstep (se 1 (by rfl) ⟨1047257, by rfl⟩ : syracuseStep 1396343 = 2094515) B2094515
theorem B1396367 : Blo 928581 1396367 := bstep (se 1 (by rfl) ⟨1047275, by rfl⟩ : syracuseStep 1396367 = 2094551) B2094551
theorem B1396409 : Blo 928581 1396409 := bstep (se 2 (by rfl) ⟨523653, by rfl⟩ : syracuseStep 1396409 = 1047307) B1047307
theorem B1396487 : Blo 928581 1396487 := bstep (se 1 (by rfl) ⟨1047365, by rfl⟩ : syracuseStep 1396487 = 2094731) B2094731
theorem B1396523 : Blo 928581 1396523 := bstep (se 1 (by rfl) ⟨1047392, by rfl⟩ : syracuseStep 1396523 = 2094785) B2094785
theorem B4706099 : Blo 928581 4706099 := bstep (se 1 (by rfl) ⟨3529574, by rfl⟩ : syracuseStep 4706099 = 7059149) B7059149
theorem B1396553 : Blo 928581 1396553 := bstep (se 2 (by rfl) ⟨523707, by rfl⟩ : syracuseStep 1396553 = 1047415) B1047415
theorem B1396667 : Blo 928581 1396667 := bstep (se 1 (by rfl) ⟨1047500, by rfl⟩ : syracuseStep 1396667 = 2095001) B2095001
theorem B1396727 : Blo 928581 1396727 := bstep (se 1 (by rfl) ⟨1047545, by rfl⟩ : syracuseStep 1396727 = 2095091) B2095091
theorem B1396751 : Blo 928581 1396751 := bstep (se 1 (by rfl) ⟨1047563, by rfl⟩ : syracuseStep 1396751 = 2095127) B2095127
theorem B1396793 : Blo 928581 1396793 := bstep (se 2 (by rfl) ⟨523797, by rfl⟩ : syracuseStep 1396793 = 1047595) B1047595
theorem B4706423 : Blo 928581 4706423 := bstep (se 1 (by rfl) ⟨3529817, by rfl⟩ : syracuseStep 4706423 = 7059635) B7059635
theorem B1396871 : Blo 928581 1396871 := bstep (se 1 (by rfl) ⟨1047653, by rfl⟩ : syracuseStep 1396871 = 2095307) B2095307
theorem B1396907 : Blo 928581 1396907 := bstep (se 1 (by rfl) ⟨1047680, by rfl⟩ : syracuseStep 1396907 = 2095361) B2095361
theorem B1396937 : Blo 928581 1396937 := bstep (se 2 (by rfl) ⟨523851, by rfl⟩ : syracuseStep 1396937 = 1047703) B1047703
theorem B1397051 : Blo 928581 1397051 := bstep (se 1 (by rfl) ⟨1047788, by rfl⟩ : syracuseStep 1397051 = 2095577) B2095577
theorem B1397111 : Blo 928581 1397111 := bstep (se 1 (by rfl) ⟨1047833, by rfl⟩ : syracuseStep 1397111 = 2095667) B2095667
theorem B1397135 : Blo 928581 1397135 := bstep (se 1 (by rfl) ⟨1047851, by rfl⟩ : syracuseStep 1397135 = 2095703) B2095703
theorem B1397177 : Blo 928581 1397177 := bstep (se 2 (by rfl) ⟨523941, by rfl⟩ : syracuseStep 1397177 = 1047883) B1047883
theorem B1397255 : Blo 928581 1397255 := bstep (se 1 (by rfl) ⟨1047941, by rfl⟩ : syracuseStep 1397255 = 2095883) B2095883
theorem B2511371 : Blo 928581 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1987087 : Blo 928581 1987087 := bstep (se 1 (by rfl) ⟨1490315, by rfl⟩ : syracuseStep 1987087 = 2980631) B2980631
theorem B4477463 : Blo 928581 4477463 := bstep (se 1 (by rfl) ⟨3358097, by rfl⟩ : syracuseStep 4477463 = 6716195) B6716195
theorem B1397291 : Blo 928581 1397291 := bstep (se 1 (by rfl) ⟨1047968, by rfl⟩ : syracuseStep 1397291 = 2095937) B2095937
theorem B22663745 : Blo 928581 22663745 := bstep (se 2 (by rfl) ⟨8498904, by rfl⟩ : syracuseStep 22663745 = 16997809) B16997809
theorem B1397321 : Blo 928581 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B1397435 : Blo 928581 1397435 := bstep (se 1 (by rfl) ⟨1048076, by rfl⟩ : syracuseStep 1397435 = 2096153) B2096153
theorem B1397495 : Blo 928581 1397495 := bstep (se 1 (by rfl) ⟨1048121, by rfl⟩ : syracuseStep 1397495 = 2096243) B2096243
theorem B1397519 : Blo 928581 1397519 := bstep (se 1 (by rfl) ⟨1048139, by rfl⟩ : syracuseStep 1397519 = 2096279) B2096279
theorem B1594127 : Blo 928581 1594127 := bstep (se 1 (by rfl) ⟨1195595, by rfl⟩ : syracuseStep 1594127 = 2391191) B2391191
theorem B1397561 : Blo 928581 1397561 := bstep (se 2 (by rfl) ⟨524085, by rfl⟩ : syracuseStep 1397561 = 1048171) B1048171
theorem B3134267 : Blo 928581 3134267 := bstep (se 1 (by rfl) ⟨2350700, by rfl⟩ : syracuseStep 3134267 = 4701401) B4701401
theorem B1397639 : Blo 928581 1397639 := bstep (se 1 (by rfl) ⟨1048229, by rfl⟩ : syracuseStep 1397639 = 2096459) B2096459
theorem B1397675 : Blo 928581 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B1397705 : Blo 928581 1397705 := bstep (se 2 (by rfl) ⟨524139, by rfl⟩ : syracuseStep 1397705 = 1048279) B1048279
theorem B9065483 : Blo 928581 9065483 := bstep (se 1 (by rfl) ⟨6799112, by rfl⟩ : syracuseStep 9065483 = 13598225) B13598225
theorem B1397819 : Blo 928581 1397819 := bstep (se 1 (by rfl) ⟨1048364, by rfl⟩ : syracuseStep 1397819 = 2096729) B2096729
theorem B4707395 : Blo 928581 4707395 := bstep (se 1 (by rfl) ⟨3530546, by rfl⟩ : syracuseStep 4707395 = 7061093) B7061093
theorem B1397879 : Blo 928581 1397879 := bstep (se 1 (by rfl) ⟨1048409, by rfl⟩ : syracuseStep 1397879 = 2096819) B2096819
theorem B1397903 : Blo 928581 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B1397945 : Blo 928581 1397945 := bstep (se 2 (by rfl) ⟨524229, by rfl⟩ : syracuseStep 1397945 = 1048459) B1048459
theorem B1398023 : Blo 928581 1398023 := bstep (se 1 (by rfl) ⟨1048517, by rfl⟩ : syracuseStep 1398023 = 2097035) B2097035
theorem B3134753 : Blo 928581 3134753 := bstep (se 2 (by rfl) ⟨1175532, by rfl⟩ : syracuseStep 3134753 = 2351065) B2351065
theorem B1398059 : Blo 928581 1398059 := bstep (se 1 (by rfl) ⟨1048544, by rfl⟩ : syracuseStep 1398059 = 2097089) B2097089
theorem B5363003 : Blo 928581 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B3527995 : Blo 928581 3527995 := bstep (se 1 (by rfl) ⟨2645996, by rfl⟩ : syracuseStep 3527995 = 5291993) B5291993
theorem B1398089 : Blo 928581 1398089 := bstep (se 2 (by rfl) ⟨524283, by rfl⟩ : syracuseStep 1398089 = 1048567) B1048567
theorem B4707719 : Blo 928581 4707719 := bstep (se 1 (by rfl) ⟨3530789, by rfl⟩ : syracuseStep 4707719 = 7061579) B7061579
theorem B2512313 : Blo 928581 2512313 := bstep (se 2 (by rfl) ⟨942117, by rfl⟩ : syracuseStep 2512313 = 1884235) B1884235
theorem B1398203 : Blo 928581 1398203 := bstep (se 1 (by rfl) ⟨1048652, by rfl⟩ : syracuseStep 1398203 = 2097305) B2097305
theorem B1398263 : Blo 928581 1398263 := bstep (se 1 (by rfl) ⟨1048697, by rfl⟩ : syracuseStep 1398263 = 2097395) B2097395
theorem B1398287 : Blo 928581 1398287 := bstep (se 1 (by rfl) ⟨1048715, by rfl⟩ : syracuseStep 1398287 = 2097431) B2097431
theorem B1398329 : Blo 928581 1398329 := bstep (se 2 (by rfl) ⟨524373, by rfl⟩ : syracuseStep 1398329 = 1048747) B1048747
theorem B1398407 : Blo 928581 1398407 := bstep (se 1 (by rfl) ⟨1048805, by rfl⟩ : syracuseStep 1398407 = 2097611) B2097611
theorem B1398443 : Blo 928581 1398443 := bstep (se 1 (by rfl) ⟨1048832, by rfl⟩ : syracuseStep 1398443 = 2097665) B2097665
theorem B40195763 : Blo 928581 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B2873017 : Blo 928581 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B1398473 : Blo 928581 1398473 := bstep (se 2 (by rfl) ⟨524427, by rfl⟩ : syracuseStep 1398473 = 1048855) B1048855
theorem B3528481 : Blo 928581 3528481 := bstep (se 2 (by rfl) ⟨1323180, by rfl⟩ : syracuseStep 3528481 = 2646361) B2646361
theorem B15324977 : Blo 928581 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B1398587 : Blo 928581 1398587 := bstep (se 1 (by rfl) ⟨1048940, by rfl⟩ : syracuseStep 1398587 = 2097881) B2097881
theorem B3135347 : Blo 928581 3135347 := bstep (se 1 (by rfl) ⟨2351510, by rfl⟩ : syracuseStep 3135347 = 4703021) B4703021
theorem B1398647 : Blo 928581 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B1398671 : Blo 928581 1398671 := bstep (se 1 (by rfl) ⟨1049003, by rfl⟩ : syracuseStep 1398671 = 2098007) B2098007
theorem B1398713 : Blo 928581 1398713 := bstep (se 2 (by rfl) ⟨524517, by rfl⟩ : syracuseStep 1398713 = 1049035) B1049035
theorem B1398791 : Blo 928581 1398791 := bstep (se 1 (by rfl) ⟨1049093, by rfl⟩ : syracuseStep 1398791 = 2098187) B2098187
theorem B1398827 : Blo 928581 1398827 := bstep (se 1 (by rfl) ⟨1049120, by rfl⟩ : syracuseStep 1398827 = 2098241) B2098241
theorem B1398857 : Blo 928581 1398857 := bstep (se 2 (by rfl) ⟨524571, by rfl⟩ : syracuseStep 1398857 = 1049143) B1049143
theorem B2513015 : Blo 928581 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B4249837 : Blo 928581 4249837 := bstep (se 3 (by rfl) ⟨796844, by rfl⟩ : syracuseStep 4249837 = 1593689) B1593689
theorem B13424885 : Blo 928581 13424885 := bstep (se 5 (by rfl) ⟨629291, by rfl⟩ : syracuseStep 13424885 = 1258583) B1258583
theorem B5658931 : Blo 928581 5658931 := bstep (se 1 (by rfl) ⟨4244198, by rfl⟩ : syracuseStep 5658931 = 8488397) B8488397
theorem B1431865 : Blo 928581 1431865 := bstep (se 2 (by rfl) ⟨536949, by rfl⟩ : syracuseStep 1431865 = 1073899) B1073899
theorem B2120377 : Blo 928581 2120377 := bstep (se 2 (by rfl) ⟨795141, by rfl⟩ : syracuseStep 2120377 = 1590283) B1590283
theorem B3529453 : Blo 928581 3529453 := bstep (se 3 (by rfl) ⟨661772, by rfl⟩ : syracuseStep 3529453 = 1323545) B1323545
theorem B20142863 : Blo 928581 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B3529757 : Blo 928581 3529757 := bstep (se 3 (by rfl) ⟨661829, by rfl⟩ : syracuseStep 3529757 = 1323659) B1323659
theorem B2645291 : Blo 928581 2645291 := bstep (se 1 (by rfl) ⟨1983968, by rfl⟩ : syracuseStep 2645291 = 3967937) B3967937
theorem B5660171 : Blo 928581 5660171 := bstep (se 1 (by rfl) ⟨4245128, by rfl⟩ : syracuseStep 5660171 = 8490257) B8490257
theorem B5955443 : Blo 928581 5955443 := bstep (se 1 (by rfl) ⟨4466582, by rfl⟩ : syracuseStep 5955443 = 8933165) B8933165
theorem B4480883 : Blo 928581 4480883 := bstep (se 1 (by rfl) ⟨3360662, by rfl⟩ : syracuseStep 4480883 = 6721325) B6721325
theorem B15097751 : Blo 928581 15097751 := bstep (se 1 (by rfl) ⟨11323313, by rfl⟩ : syracuseStep 15097751 = 22646627) B22646627
theorem B2646407 : Blo 928581 2646407 := bstep (se 1 (by rfl) ⟨1984805, by rfl⟩ : syracuseStep 2646407 = 3969611) B3969611
theorem B3137939 : Blo 928581 3137939 := bstep (se 1 (by rfl) ⟨2353454, by rfl⟩ : syracuseStep 3137939 = 4706909) B4706909
theorem B10215827 : Blo 928581 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B7561619 : Blo 928581 7561619 := bstep (se 1 (by rfl) ⟨5671214, by rfl⟩ : syracuseStep 7561619 = 11342429) B11342429
theorem B2646589 : Blo 928581 2646589 := bstep (se 3 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 2646589 = 992471) B992471
theorem B4252247 : Blo 928581 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B3531383 : Blo 928581 3531383 := bstep (se 1 (by rfl) ⟨2648537, by rfl⟩ : syracuseStep 3531383 = 5297075) B5297075
theorem B7070327 : Blo 928581 7070327 := bstep (se 1 (by rfl) ⟨5302745, by rfl⟩ : syracuseStep 7070327 = 10605491) B10605491
theorem B1696391 : Blo 928581 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B2089619 : Blo 928581 2089619 := bstep (se 1 (by rfl) ⟨1567214, by rfl⟩ : syracuseStep 2089619 = 3134429) B3134429
theorem B2089673 : Blo 928581 2089673 := bstep (se 2 (by rfl) ⟨783627, by rfl⟩ : syracuseStep 2089673 = 1567255) B1567255
theorem B2351987 : Blo 928581 2351987 := bstep (se 1 (by rfl) ⟨1763990, by rfl⟩ : syracuseStep 2351987 = 3527981) B3527981
theorem B4711283 : Blo 928581 4711283 := bstep (se 1 (by rfl) ⟨3533462, by rfl⟩ : syracuseStep 4711283 = 7066925) B7066925
theorem B2646931 : Blo 928581 2646931 := bstep (se 1 (by rfl) ⟨1985198, by rfl⟩ : syracuseStep 2646931 = 3970397) B3970397
theorem B943111 : Blo 928581 943111 := bstep (se 1 (by rfl) ⟨707333, by rfl⟩ : syracuseStep 943111 = 1414667) B1414667
theorem B11920517 : Blo 928581 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B5301449 : Blo 928581 5301449 := bstep (se 2 (by rfl) ⟨1988043, by rfl⟩ : syracuseStep 5301449 = 3976087) B3976087
theorem B10609865 : Blo 928581 10609865 := bstep (se 2 (by rfl) ⟨3978699, by rfl⟩ : syracuseStep 10609865 = 7957399) B7957399
theorem B2123023 : Blo 928581 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B4711769 : Blo 928581 4711769 := bstep (se 2 (by rfl) ⟨1766913, by rfl⟩ : syracuseStep 4711769 = 3533827) B3533827
theorem B2352503 : Blo 928581 2352503 := bstep (se 1 (by rfl) ⟨1764377, by rfl⟩ : syracuseStep 2352503 = 3528755) B3528755
theorem B2090375 : Blo 928581 2090375 := bstep (se 1 (by rfl) ⟨1567781, by rfl⟩ : syracuseStep 2090375 = 3135563) B3135563
theorem B2123297 : Blo 928581 2123297 := bstep (se 2 (by rfl) ⟨796236, by rfl⟩ : syracuseStep 2123297 = 1592473) B1592473
theorem B1762859 : Blo 928581 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B2090555 : Blo 928581 2090555 := bstep (se 1 (by rfl) ⟨1567916, by rfl⟩ : syracuseStep 2090555 = 3135833) B3135833
theorem B3532355 : Blo 928581 3532355 := bstep (se 1 (by rfl) ⟨2649266, by rfl⟩ : syracuseStep 3532355 = 5298533) B5298533
theorem B7071299 : Blo 928581 7071299 := bstep (se 1 (by rfl) ⟨5303474, by rfl⟩ : syracuseStep 7071299 = 10606949) B10606949
theorem B45868619 : Blo 928581 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B2090681 : Blo 928581 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B2647819 : Blo 928581 2647819 := bstep (se 1 (by rfl) ⟨1985864, by rfl⟩ : syracuseStep 2647819 = 3971729) B3971729
theorem B3139343 : Blo 928581 3139343 := bstep (se 1 (by rfl) ⟨2354507, by rfl⟩ : syracuseStep 3139343 = 4709015) B4709015
theorem B5662553 : Blo 928581 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B2091023 : Blo 928581 2091023 := bstep (se 1 (by rfl) ⟨1568267, by rfl⟩ : syracuseStep 2091023 = 3136535) B3136535
theorem B2975773 : Blo 928581 2975773 := bstep (se 3 (by rfl) ⟨557957, by rfl⟩ : syracuseStep 2975773 = 1115915) B1115915
theorem B3139613 : Blo 928581 3139613 := bstep (se 3 (by rfl) ⟨588677, by rfl⟩ : syracuseStep 3139613 = 1177355) B1177355
theorem B2091041 : Blo 928581 2091041 := bstep (se 2 (by rfl) ⟨784140, by rfl⟩ : syracuseStep 2091041 = 1568281) B1568281
theorem B5040215 : Blo 928581 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B5040301 : Blo 928581 5040301 := bstep (se 3 (by rfl) ⟨945056, by rfl⟩ : syracuseStep 5040301 = 1890113) B1890113
theorem B2648321 : Blo 928581 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B1567019 : Blo 928581 1567019 := bstep (se 1 (by rfl) ⟨1175264, by rfl⟩ : syracuseStep 1567019 = 2350529) B2350529
theorem B2353495 : Blo 928581 2353495 := bstep (se 1 (by rfl) ⟨1765121, by rfl⟩ : syracuseStep 2353495 = 3530243) B3530243
theorem B2091383 : Blo 928581 2091383 := bstep (se 1 (by rfl) ⟨1568537, by rfl⟩ : syracuseStep 2091383 = 3137075) B3137075
theorem B1763785 : Blo 928581 1763785 := bstep (se 2 (by rfl) ⟨661419, by rfl⟩ : syracuseStep 1763785 = 1322839) B1322839
theorem B6449629 : Blo 928581 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B3533341 : Blo 928581 3533341 := bstep (se 3 (by rfl) ⟨662501, by rfl⟩ : syracuseStep 3533341 = 1325003) B1325003
theorem B2091563 : Blo 928581 2091563 := bstep (se 1 (by rfl) ⟨1568672, by rfl⟩ : syracuseStep 2091563 = 3137345) B3137345
theorem B1272379 : Blo 928581 1272379 := bstep (se 1 (by rfl) ⟨954284, by rfl⟩ : syracuseStep 1272379 = 1908569) B1908569
theorem B2648663 : Blo 928581 2648663 := bstep (se 1 (by rfl) ⟨1986497, by rfl⟩ : syracuseStep 2648663 = 3972995) B3972995
theorem B2353799 : Blo 928581 2353799 := bstep (se 1 (by rfl) ⟨1765349, by rfl⟩ : syracuseStep 2353799 = 3530699) B3530699
theorem B5106349 : Blo 928581 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B1567417 : Blo 928581 1567417 := bstep (se 2 (by rfl) ⟨587781, by rfl⟩ : syracuseStep 1567417 = 1175563) B1175563
theorem B2353931 : Blo 928581 2353931 := bstep (se 1 (by rfl) ⟨1765448, by rfl⟩ : syracuseStep 2353931 = 3530897) B3530897
theorem B2091923 : Blo 928581 2091923 := bstep (se 1 (by rfl) ⟨1568942, by rfl⟩ : syracuseStep 2091923 = 3137885) B3137885
theorem B2091977 : Blo 928581 2091977 := bstep (se 2 (by rfl) ⟨784491, by rfl⟩ : syracuseStep 2091977 = 1568983) B1568983
theorem B5303339 : Blo 928581 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B1764499 : Blo 928581 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B2354447 : Blo 928581 2354447 := bstep (se 1 (by rfl) ⟨1765835, by rfl⟩ : syracuseStep 2354447 = 3531671) B3531671
theorem B1568119 : Blo 928581 1568119 := bstep (se 1 (by rfl) ⟨1176089, by rfl⟩ : syracuseStep 1568119 = 2352179) B2352179
theorem B4713875 : Blo 928581 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B2354579 : Blo 928581 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B3141017 : Blo 928581 3141017 := bstep (se 2 (by rfl) ⟨1177881, by rfl⟩ : syracuseStep 3141017 = 2355763) B2355763
theorem B2125241 : Blo 928581 2125241 := bstep (se 2 (by rfl) ⟨796965, by rfl⟩ : syracuseStep 2125241 = 1593931) B1593931
theorem B19590605 : Blo 928581 19590605 := bstep (se 3 (by rfl) ⟨3673238, by rfl⟩ : syracuseStep 19590605 = 7346477) B7346477
theorem B1568315 : Blo 928581 1568315 := bstep (se 1 (by rfl) ⟨1176236, by rfl⟩ : syracuseStep 1568315 = 2352473) B2352473
theorem B2092679 : Blo 928581 2092679 := bstep (se 1 (by rfl) ⟨1569509, by rfl⟩ : syracuseStep 2092679 = 3139019) B3139019
theorem B5959439 : Blo 928581 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B2092859 : Blo 928581 2092859 := bstep (se 1 (by rfl) ⟨1569644, by rfl⟩ : syracuseStep 2092859 = 3139289) B3139289
theorem B1175467 : Blo 928581 1175467 := bstep (se 1 (by rfl) ⟨881600, by rfl⟩ : syracuseStep 1175467 = 1763201) B1763201
theorem B2092985 : Blo 928581 2092985 := bstep (se 2 (by rfl) ⟨784869, by rfl⟩ : syracuseStep 2092985 = 1569739) B1569739
theorem B1568713 : Blo 928581 1568713 := bstep (se 2 (by rfl) ⟨588267, by rfl⟩ : syracuseStep 1568713 = 1176535) B1176535
theorem B10612781 : Blo 928581 10612781 := bstep (se 3 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 10612781 = 3979793) B3979793
theorem B3141719 : Blo 928581 3141719 := bstep (se 1 (by rfl) ⟨2356289, by rfl⟩ : syracuseStep 3141719 = 4712579) B4712579
theorem B14151881 : Blo 928581 14151881 := bstep (se 2 (by rfl) ⟨5306955, by rfl⟩ : syracuseStep 14151881 = 10613911) B10613911
theorem B1765577 : Blo 928581 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B1044751 : Blo 928581 1044751 := bstep (se 1 (by rfl) ⟨783563, by rfl⟩ : syracuseStep 1044751 = 1567127) B1567127
theorem B2093327 : Blo 928581 2093327 := bstep (se 1 (by rfl) ⟨1569995, by rfl⟩ : syracuseStep 2093327 = 3139991) B3139991
theorem B2093345 : Blo 928581 2093345 := bstep (se 2 (by rfl) ⟨785004, by rfl⟩ : syracuseStep 2093345 = 1570009) B1570009
theorem B2650553 : Blo 928581 2650553 := bstep (se 2 (by rfl) ⟨993957, by rfl⟩ : syracuseStep 2650553 = 1987915) B1987915
theorem B5304797 : Blo 928581 5304797 := bstep (se 3 (by rfl) ⟨994649, by rfl⟩ : syracuseStep 5304797 = 1989299) B1989299
theorem B2355713 : Blo 928581 2355713 := bstep (se 2 (by rfl) ⟨883392, by rfl⟩ : syracuseStep 2355713 = 1766785) B1766785
theorem B3142205 : Blo 928581 3142205 := bstep (se 3 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 3142205 = 1178327) B1178327
theorem B2093687 : Blo 928581 2093687 := bstep (se 1 (by rfl) ⟨1570265, by rfl⟩ : syracuseStep 2093687 = 3140531) B3140531
theorem B1569415 : Blo 928581 1569415 := bstep (se 1 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 1569415 = 2354123) B2354123
theorem B1077895 : Blo 928581 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B6451969 : Blo 928581 6451969 := bstep (se 2 (by rfl) ⟨2419488, by rfl⟩ : syracuseStep 6451969 = 4838977) B4838977
theorem B1045255 : Blo 928581 1045255 := bstep (se 1 (by rfl) ⟨783941, by rfl⟩ : syracuseStep 1045255 = 1567883) B1567883
theorem B2093867 : Blo 928581 2093867 := bstep (se 1 (by rfl) ⟨1570400, by rfl⟩ : syracuseStep 2093867 = 3140801) B3140801
theorem B1176439 : Blo 928581 1176439 := bstep (se 1 (by rfl) ⟨882329, by rfl⟩ : syracuseStep 1176439 = 1764659) B1764659
theorem B2356087 : Blo 928581 2356087 := bstep (se 1 (by rfl) ⟨1767065, by rfl⟩ : syracuseStep 2356087 = 3534131) B3534131
theorem B1045435 : Blo 928581 1045435 := bstep (se 1 (by rfl) ⟨784076, by rfl⟩ : syracuseStep 1045435 = 1568153) B1568153
theorem B5305297 : Blo 928581 5305297 := bstep (se 2 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 5305297 = 3978973) B3978973
theorem B2683937 : Blo 928581 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B1766443 : Blo 928581 1766443 := bstep (se 1 (by rfl) ⟨1324832, by rfl⟩ : syracuseStep 1766443 = 2649665) B2649665
theorem B1766519 : Blo 928581 1766519 := bstep (se 1 (by rfl) ⟨1324889, by rfl⟩ : syracuseStep 1766519 = 2649779) B2649779
theorem B2094227 : Blo 928581 2094227 := bstep (se 1 (by rfl) ⟨1570670, by rfl⟩ : syracuseStep 2094227 = 3141341) B3141341
theorem B1176763 : Blo 928581 1176763 := bstep (se 1 (by rfl) ⟨882572, by rfl⟩ : syracuseStep 1176763 = 1765145) B1765145
theorem B2094281 : Blo 928581 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B1701065 : Blo 928581 1701065 := bstep (se 2 (by rfl) ⟨637899, by rfl⟩ : syracuseStep 1701065 = 1275799) B1275799
theorem B1242383 : Blo 928581 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B1570063 : Blo 928581 1570063 := bstep (se 1 (by rfl) ⟨1177547, by rfl⟩ : syracuseStep 1570063 = 2355095) B2355095
theorem B2356523 : Blo 928581 2356523 := bstep (se 1 (by rfl) ⟨1767392, by rfl⟩ : syracuseStep 2356523 = 3534785) B3534785
theorem B3536243 : Blo 928581 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B1045903 : Blo 928581 1045903 := bstep (se 1 (by rfl) ⟨784427, by rfl⟩ : syracuseStep 1045903 = 1568855) B1568855
theorem B6714809 : Blo 928581 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B1570603 : Blo 928581 1570603 := bstep (se 1 (by rfl) ⟨1177952, by rfl⟩ : syracuseStep 1570603 = 2355905) B2355905
theorem B7075673 : Blo 928581 7075673 := bstep (se 2 (by rfl) ⟨2653377, by rfl⟩ : syracuseStep 7075673 = 5306755) B5306755
theorem B1046407 : Blo 928581 1046407 := bstep (se 1 (by rfl) ⟨784805, by rfl⟩ : syracuseStep 1046407 = 1569611) B1569611
theorem B2094983 : Blo 928581 2094983 := bstep (se 1 (by rfl) ⟨1571237, by rfl⟩ : syracuseStep 2094983 = 3142475) B3142475
theorem B1570745 : Blo 928581 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B3143609 : Blo 928581 3143609 := bstep (se 2 (by rfl) ⟨1178853, by rfl⟩ : syracuseStep 3143609 = 2357707) B2357707
theorem B2652193 : Blo 928581 2652193 := bstep (se 2 (by rfl) ⟨994572, by rfl⟩ : syracuseStep 2652193 = 1989145) B1989145
theorem B1046587 : Blo 928581 1046587 := bstep (se 1 (by rfl) ⟨784940, by rfl⟩ : syracuseStep 1046587 = 1569881) B1569881
theorem B2095163 : Blo 928581 2095163 := bstep (se 1 (by rfl) ⟨1571372, by rfl⟩ : syracuseStep 2095163 = 3142745) B3142745
theorem B2357363 : Blo 928581 2357363 := bstep (se 1 (by rfl) ⟨1768022, by rfl⟩ : syracuseStep 2357363 = 3536045) B3536045
theorem B1177735 : Blo 928581 1177735 := bstep (se 1 (by rfl) ⟨883301, by rfl⟩ : syracuseStep 1177735 = 1766603) B1766603
theorem B2357383 : Blo 928581 2357383 := bstep (se 1 (by rfl) ⟨1768037, by rfl⟩ : syracuseStep 2357383 = 3536075) B3536075
theorem B2095289 : Blo 928581 2095289 := bstep (se 2 (by rfl) ⟨785733, by rfl⟩ : syracuseStep 2095289 = 1571467) B1571467
theorem B2357657 : Blo 928581 2357657 := bstep (se 2 (by rfl) ⟨884121, by rfl⟩ : syracuseStep 2357657 = 1768243) B1768243
theorem B4716953 : Blo 928581 4716953 := bstep (se 2 (by rfl) ⟨1768857, by rfl⟩ : syracuseStep 4716953 = 3537715) B3537715
theorem B3144203 : Blo 928581 3144203 := bstep (se 1 (by rfl) ⟨2358152, by rfl⟩ : syracuseStep 3144203 = 4716305) B4716305
theorem B1047055 : Blo 928581 1047055 := bstep (se 1 (by rfl) ⟨785291, by rfl⟩ : syracuseStep 1047055 = 1570583) B1570583
theorem B2095631 : Blo 928581 2095631 := bstep (se 1 (by rfl) ⟨1571723, by rfl⟩ : syracuseStep 2095631 = 3143447) B3143447
theorem B2095649 : Blo 928581 2095649 := bstep (se 2 (by rfl) ⟨785868, by rfl⟩ : syracuseStep 2095649 = 1571737) B1571737
theorem B1178155 : Blo 928581 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B2357819 : Blo 928581 2357819 := bstep (se 1 (by rfl) ⟨1768364, by rfl⟩ : syracuseStep 2357819 = 3536729) B3536729
theorem B1571447 : Blo 928581 1571447 := bstep (se 1 (by rfl) ⟨1178585, by rfl⟩ : syracuseStep 1571447 = 2357171) B2357171
theorem B3144311 : Blo 928581 3144311 := bstep (se 1 (by rfl) ⟨2358233, by rfl⟩ : syracuseStep 3144311 = 4716467) B4716467
theorem B1178383 : Blo 928581 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B2358031 : Blo 928581 2358031 := bstep (se 1 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 2358031 = 3537047) B3537047
theorem B7076645 : Blo 928581 7076645 := bstep (se 4 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 7076645 = 1326871) B1326871
theorem B2095991 : Blo 928581 2095991 := bstep (se 1 (by rfl) ⟨1571993, by rfl⟩ : syracuseStep 2095991 = 3143987) B3143987
theorem B5307281 : Blo 928581 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B1047559 : Blo 928581 1047559 := bstep (se 1 (by rfl) ⟨785669, by rfl⟩ : syracuseStep 1047559 = 1571339) B1571339
theorem B1768463 : Blo 928581 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B2358305 : Blo 928581 2358305 := bstep (se 2 (by rfl) ⟨884364, by rfl⟩ : syracuseStep 2358305 = 1768729) B1768729
theorem B2096171 : Blo 928581 2096171 := bstep (se 1 (by rfl) ⟨1572128, by rfl⟩ : syracuseStep 2096171 = 3144257) B3144257
theorem B1571899 : Blo 928581 1571899 := bstep (se 1 (by rfl) ⟨1178924, by rfl⟩ : syracuseStep 1571899 = 2357849) B2357849
theorem B7961773 : Blo 928581 7961773 := bstep (se 3 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 7961773 = 2985665) B2985665
theorem B1047739 : Blo 928581 1047739 := bstep (se 1 (by rfl) ⟨785804, by rfl⟩ : syracuseStep 1047739 = 1571609) B1571609
theorem B1572041 : Blo 928581 1572041 := bstep (se 2 (by rfl) ⟨589515, by rfl⟩ : syracuseStep 1572041 = 1179031) B1179031
theorem B3144905 : Blo 928581 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B2653469 : Blo 928581 2653469 := bstep (se 3 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 2653469 = 995051) B995051
theorem B2096531 : Blo 928581 2096531 := bstep (se 1 (by rfl) ⟨1572398, by rfl⟩ : syracuseStep 2096531 = 3144797) B3144797
theorem B2096585 : Blo 928581 2096585 := bstep (se 2 (by rfl) ⟨786219, by rfl⟩ : syracuseStep 2096585 = 1572439) B1572439
theorem B1179127 : Blo 928581 1179127 := bstep (se 1 (by rfl) ⟨884345, by rfl⟩ : syracuseStep 1179127 = 1768691) B1768691
theorem B2653697 : Blo 928581 2653697 := bstep (se 2 (by rfl) ⟨995136, by rfl⟩ : syracuseStep 2653697 = 1990273) B1990273
theorem B2981387 : Blo 928581 2981387 := bstep (se 1 (by rfl) ⟨2236040, by rfl⟩ : syracuseStep 2981387 = 4472081) B4472081
theorem B3538475 : Blo 928581 3538475 := bstep (se 1 (by rfl) ⟨2653856, by rfl⟩ : syracuseStep 3538475 = 5307713) B5307713
theorem B1048207 : Blo 928581 1048207 := bstep (se 1 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 1048207 = 1572311) B1572311
theorem B1179451 : Blo 928581 1179451 := bstep (se 1 (by rfl) ⟨884588, by rfl⟩ : syracuseStep 1179451 = 1769177) B1769177
theorem B2654039 : Blo 928581 2654039 := bstep (se 1 (by rfl) ⟨1990529, by rfl⟩ : syracuseStep 2654039 = 3981059) B3981059
theorem B1572743 : Blo 928581 1572743 := bstep (se 1 (by rfl) ⟨1179557, by rfl⟩ : syracuseStep 1572743 = 2359115) B2359115
theorem B3145607 : Blo 928581 3145607 := bstep (se 1 (by rfl) ⟨2359205, by rfl⟩ : syracuseStep 3145607 = 4718411) B4718411
theorem B2654153 : Blo 928581 2654153 := bstep (se 2 (by rfl) ⟨995307, by rfl⟩ : syracuseStep 2654153 = 1990615) B1990615
theorem B1572871 : Blo 928581 1572871 := bstep (se 1 (by rfl) ⟨1179653, by rfl⟩ : syracuseStep 1572871 = 2359307) B2359307
theorem B5668879 : Blo 928581 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B2097323 : Blo 928581 2097323 := bstep (se 1 (by rfl) ⟨1572992, by rfl⟩ : syracuseStep 2097323 = 3145985) B3145985
theorem B1048927 : Blo 928581 1048927 := bstep (se 1 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 1048927 = 1573391) B1573391
theorem B1573303 : Blo 928581 1573303 := bstep (se 1 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 1573303 = 2359955) B2359955
theorem B3146363 : Blo 928581 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B1573499 : Blo 928581 1573499 := bstep (se 1 (by rfl) ⟨1180124, by rfl⟩ : syracuseStep 1573499 = 2360249) B2360249
theorem B3539645 : Blo 928581 3539645 := bstep (se 3 (by rfl) ⟨663683, by rfl⟩ : syracuseStep 3539645 = 1327367) B1327367
theorem B2097863 : Blo 928581 2097863 := bstep (se 1 (by rfl) ⟨1573397, by rfl⟩ : syracuseStep 2097863 = 3146795) B3146795
theorem B3146525 : Blo 928581 3146525 := bstep (se 3 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 3146525 = 1179947) B1179947
theorem B5964617 : Blo 928581 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B2360137 : Blo 928581 2360137 := bstep (se 2 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 2360137 = 1770103) B1770103
theorem B4784969 : Blo 928581 4784969 := bstep (se 2 (by rfl) ⟨1794363, by rfl⟩ : syracuseStep 4784969 = 3588727) B3588727
theorem B3769249 : Blo 928581 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B2983027 : Blo 928581 2983027 := bstep (se 1 (by rfl) ⟨2237270, by rfl⟩ : syracuseStep 2983027 = 4474541) B4474541
theorem B3147227 : Blo 928581 3147227 := bstep (se 1 (by rfl) ⟨2360420, by rfl⟩ : syracuseStep 3147227 = 4720841) B4720841
theorem B2983463 : Blo 928581 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B228984641 : Blo 928581 228984641 := bstep (se 2 (by rfl) ⟨85869240, by rfl⟩ : syracuseStep 228984641 = 171738481) B171738481
theorem B1116011 : Blo 928581 1116011 := bstep (se 1 (by rfl) ⟨837008, by rfl⟩ : syracuseStep 1116011 = 1674017) B1674017
theorem B15075233 : Blo 928581 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B3017179 : Blo 928581 3017179 := bstep (se 1 (by rfl) ⟨2262884, by rfl⟩ : syracuseStep 3017179 = 4525769) B4525769
theorem B3967697 : Blo 928581 3967697 := bstep (se 2 (by rfl) ⟨1487886, by rfl⟩ : syracuseStep 3967697 = 2975773) B2975773
theorem B6720401 : Blo 928581 6720401 := bstep (se 2 (by rfl) ⟨2520150, by rfl⟩ : syracuseStep 6720401 = 5040301) B5040301
theorem B2984975 : Blo 928581 2984975 := bstep (se 1 (by rfl) ⟨2238731, by rfl⟩ : syracuseStep 2984975 = 4477463) B4477463
theorem B15109163 : Blo 928581 15109163 := bstep (se 1 (by rfl) ⟨11331872, by rfl⟩ : syracuseStep 15109163 = 22663745) B22663745
theorem B3313021 : Blo 928581 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B3575335 : Blo 928581 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B1674875 : Blo 928581 1674875 := bstep (se 1 (by rfl) ⟨1256156, by rfl⟩ : syracuseStep 1674875 = 2512313) B2512313
theorem B1675343 : Blo 928581 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B8949923 : Blo 928581 8949923 := bstep (se 1 (by rfl) ⟨6712442, by rfl⟩ : syracuseStep 8949923 = 13424885) B13424885
theorem B331321873 : Blo 928581 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B3773447 : Blo 928581 3773447 := bstep (se 1 (by rfl) ⟨2830085, by rfl⟩ : syracuseStep 3773447 = 5660171) B5660171
theorem B3970295 : Blo 928581 3970295 := bstep (se 1 (by rfl) ⟨2977721, by rfl⟩ : syracuseStep 3970295 = 5955443) B5955443
theorem B2987255 : Blo 928581 2987255 := bstep (se 1 (by rfl) ⟨2240441, by rfl⟩ : syracuseStep 2987255 = 4480883) B4480883
theorem B10065167 : Blo 928581 10065167 := bstep (se 1 (by rfl) ⟨7548875, by rfl⟩ : syracuseStep 10065167 = 15097751) B15097751
theorem B1676857 : Blo 928581 1676857 := bstep (se 2 (by rfl) ⟨628821, by rfl⟩ : syracuseStep 1676857 = 1257643) B1257643
theorem B3348179 : Blo 928581 3348179 := bstep (se 1 (by rfl) ⟨2511134, by rfl⟩ : syracuseStep 3348179 = 5022269) B5022269
theorem B7935803 : Blo 928581 7935803 := bstep (se 1 (by rfl) ⟨5951852, by rfl⟩ : syracuseStep 7935803 = 11903705) B11903705
theorem B1415531 : Blo 928581 1415531 := bstep (se 1 (by rfl) ⟨1061648, by rfl⟩ : syracuseStep 1415531 = 2123297) B2123297
theorem B2234753 : Blo 928581 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B30579079 : Blo 928581 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B3348955 : Blo 928581 3348955 := bstep (se 1 (by rfl) ⟨2511716, by rfl⟩ : syracuseStep 3348955 = 5023433) B5023433
theorem B22650029 : Blo 928581 22650029 := bstep (se 3 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 22650029 = 8493761) B8493761
theorem B1416827 : Blo 928581 1416827 := bstep (se 1 (by rfl) ⟨1062620, by rfl⟩ : syracuseStep 1416827 = 2125241) B2125241
theorem B627351317 : Blo 928581 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B3972959 : Blo 928581 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B7545241 : Blo 928581 7545241 := bstep (se 2 (by rfl) ⟨2829465, by rfl⟩ : syracuseStep 7545241 = 5658931) B5658931
theorem B1909153 : Blo 928581 1909153 := bstep (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) B1431865
theorem B5972615 : Blo 928581 5972615 := bstep (se 1 (by rfl) ⟨4479461, by rfl⟩ : syracuseStep 5972615 = 8958923) B8958923
theorem B6693587 : Blo 928581 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B2827169 : Blo 928581 2827169 := bstep (se 2 (by rfl) ⟨1060188, by rfl⟩ : syracuseStep 2827169 = 2120377) B2120377
theorem B60400565 : Blo 928581 60400565 := bstep (se 5 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 60400565 = 5662553) B5662553
theorem B34022605 : Blo 928581 34022605 := bstep (se 3 (by rfl) ⟨6379238, by rfl⟩ : syracuseStep 34022605 = 12758477) B12758477
theorem B12723445 : Blo 928581 12723445 := bstep (se 5 (by rfl) ⟨596411, by rfl⟩ : syracuseStep 12723445 = 1192823) B1192823
theorem B5383597 : Blo 928581 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B27207683 : Blo 928581 27207683 := bstep (se 1 (by rfl) ⟨20405762, by rfl⟩ : syracuseStep 27207683 = 40811525) B40811525
theorem B993479 : Blo 928581 993479 := bstep (se 1 (by rfl) ⟨745109, by rfl⟩ : syracuseStep 993479 = 1490219) B1490219
theorem B3353051 : Blo 928581 3353051 := bstep (se 1 (by rfl) ⟨2514788, by rfl⟩ : syracuseStep 3353051 = 5029577) B5029577
theorem B13806281 : Blo 928581 13806281 := bstep (se 2 (by rfl) ⟨5177355, by rfl⟩ : syracuseStep 13806281 = 10354711) B10354711
theorem B928591 : Blo 928581 928591 := bstep (se 1 (by rfl) ⟨696443, by rfl⟩ : syracuseStep 928591 = 1392887) B1392887
theorem B928607 : Blo 928581 928607 := bstep (se 1 (by rfl) ⟨696455, by rfl⟩ : syracuseStep 928607 = 1392911) B1392911
theorem B928635 : Blo 928581 928635 := bstep (se 1 (by rfl) ⟨696476, by rfl⟩ : syracuseStep 928635 = 1392953) B1392953
theorem B928687 : Blo 928581 928687 := bstep (se 1 (by rfl) ⟨696515, by rfl⟩ : syracuseStep 928687 = 1393031) B1393031
theorem B928711 : Blo 928581 928711 := bstep (se 1 (by rfl) ⟨696533, by rfl⟩ : syracuseStep 928711 = 1393067) B1393067
theorem B928731 : Blo 928581 928731 := bstep (se 1 (by rfl) ⟨696548, by rfl⟩ : syracuseStep 928731 = 1393097) B1393097
theorem B928807 : Blo 928581 928807 := bstep (se 1 (by rfl) ⟨696605, by rfl⟩ : syracuseStep 928807 = 1393211) B1393211
theorem B928847 : Blo 928581 928847 := bstep (se 1 (by rfl) ⟨696635, by rfl⟩ : syracuseStep 928847 = 1393271) B1393271
theorem B928863 : Blo 928581 928863 := bstep (se 1 (by rfl) ⟨696647, by rfl⟩ : syracuseStep 928863 = 1393295) B1393295
theorem B928891 : Blo 928581 928891 := bstep (se 1 (by rfl) ⟨696668, by rfl⟩ : syracuseStep 928891 = 1393337) B1393337
theorem B928943 : Blo 928581 928943 := bstep (se 1 (by rfl) ⟨696707, by rfl⟩ : syracuseStep 928943 = 1393415) B1393415
theorem B928967 : Blo 928581 928967 := bstep (se 1 (by rfl) ⟨696725, by rfl⟩ : syracuseStep 928967 = 1393451) B1393451
theorem B928987 : Blo 928581 928987 := bstep (se 1 (by rfl) ⟨696740, by rfl⟩ : syracuseStep 928987 = 1393481) B1393481
theorem B929063 : Blo 928581 929063 := bstep (se 1 (by rfl) ⟨696797, by rfl⟩ : syracuseStep 929063 = 1393595) B1393595
theorem B929103 : Blo 928581 929103 := bstep (se 1 (by rfl) ⟨696827, by rfl⟩ : syracuseStep 929103 = 1393655) B1393655
theorem B929119 : Blo 928581 929119 := bstep (se 1 (by rfl) ⟨696839, by rfl⟩ : syracuseStep 929119 = 1393679) B1393679
theorem B929147 : Blo 928581 929147 := bstep (se 1 (by rfl) ⟨696860, by rfl⟩ : syracuseStep 929147 = 1393721) B1393721
theorem B929199 : Blo 928581 929199 := bstep (se 1 (by rfl) ⟨696899, by rfl⟩ : syracuseStep 929199 = 1393799) B1393799
theorem B929223 : Blo 928581 929223 := bstep (se 1 (by rfl) ⟨696917, by rfl⟩ : syracuseStep 929223 = 1393835) B1393835
theorem B929243 : Blo 928581 929243 := bstep (se 1 (by rfl) ⟨696932, by rfl⟩ : syracuseStep 929243 = 1393865) B1393865
theorem B929319 : Blo 928581 929319 := bstep (se 1 (by rfl) ⟨696989, by rfl⟩ : syracuseStep 929319 = 1393979) B1393979
theorem B929359 : Blo 928581 929359 := bstep (se 1 (by rfl) ⟨697019, by rfl⟩ : syracuseStep 929359 = 1394039) B1394039
theorem B929375 : Blo 928581 929375 := bstep (se 1 (by rfl) ⟨697031, by rfl⟩ : syracuseStep 929375 = 1394063) B1394063
theorem B1191547 : Blo 928581 1191547 := bstep (se 1 (by rfl) ⟨893660, by rfl⟩ : syracuseStep 1191547 = 1787321) B1787321
theorem B929403 : Blo 928581 929403 := bstep (se 1 (by rfl) ⟨697052, by rfl⟩ : syracuseStep 929403 = 1394105) B1394105
theorem B929455 : Blo 928581 929455 := bstep (se 1 (by rfl) ⟨697091, by rfl⟩ : syracuseStep 929455 = 1394183) B1394183
theorem B929479 : Blo 928581 929479 := bstep (se 1 (by rfl) ⟨697109, by rfl⟩ : syracuseStep 929479 = 1394219) B1394219
theorem B929499 : Blo 928581 929499 := bstep (se 1 (by rfl) ⟨697124, by rfl⟩ : syracuseStep 929499 = 1394249) B1394249
theorem B929575 : Blo 928581 929575 := bstep (se 1 (by rfl) ⟨697181, by rfl⟩ : syracuseStep 929575 = 1394363) B1394363
theorem B929615 : Blo 928581 929615 := bstep (se 1 (by rfl) ⟨697211, by rfl⟩ : syracuseStep 929615 = 1394423) B1394423
theorem B929631 : Blo 928581 929631 := bstep (se 1 (by rfl) ⟨697223, by rfl⟩ : syracuseStep 929631 = 1394447) B1394447
theorem B929659 : Blo 928581 929659 := bstep (se 1 (by rfl) ⟨697244, by rfl⟩ : syracuseStep 929659 = 1394489) B1394489
theorem B929711 : Blo 928581 929711 := bstep (se 1 (by rfl) ⟨697283, by rfl⟩ : syracuseStep 929711 = 1394567) B1394567
theorem B929735 : Blo 928581 929735 := bstep (se 1 (by rfl) ⟨697301, by rfl⟩ : syracuseStep 929735 = 1394603) B1394603
theorem B929755 : Blo 928581 929755 := bstep (se 1 (by rfl) ⟨697316, by rfl⟩ : syracuseStep 929755 = 1394633) B1394633
theorem B1257481 : Blo 928581 1257481 := bstep (se 2 (by rfl) ⟨471555, by rfl⟩ : syracuseStep 1257481 = 943111) B943111
theorem B6696989 : Blo 928581 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B929831 : Blo 928581 929831 := bstep (se 1 (by rfl) ⟨697373, by rfl⟩ : syracuseStep 929831 = 1394747) B1394747
theorem B929871 : Blo 928581 929871 := bstep (se 1 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 929871 = 1394807) B1394807
theorem B929887 : Blo 928581 929887 := bstep (se 1 (by rfl) ⟨697415, by rfl⟩ : syracuseStep 929887 = 1394831) B1394831
theorem B929915 : Blo 928581 929915 := bstep (se 1 (by rfl) ⟨697436, by rfl⟩ : syracuseStep 929915 = 1394873) B1394873
theorem B929967 : Blo 928581 929967 := bstep (se 1 (by rfl) ⟨697475, by rfl⟩ : syracuseStep 929967 = 1394951) B1394951
theorem B929991 : Blo 928581 929991 := bstep (se 1 (by rfl) ⟨697493, by rfl⟩ : syracuseStep 929991 = 1394987) B1394987
theorem B930011 : Blo 928581 930011 := bstep (se 1 (by rfl) ⟨697508, by rfl⟩ : syracuseStep 930011 = 1395017) B1395017
theorem B930087 : Blo 928581 930087 := bstep (se 1 (by rfl) ⟨697565, by rfl⟩ : syracuseStep 930087 = 1395131) B1395131
theorem B930127 : Blo 928581 930127 := bstep (se 1 (by rfl) ⟨697595, by rfl⟩ : syracuseStep 930127 = 1395191) B1395191
theorem B930143 : Blo 928581 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B2830697 : Blo 928581 2830697 := bstep (se 2 (by rfl) ⟨1061511, by rfl⟩ : syracuseStep 2830697 = 2123023) B2123023
theorem B930171 : Blo 928581 930171 := bstep (se 1 (by rfl) ⟨697628, by rfl⟩ : syracuseStep 930171 = 1395257) B1395257
theorem B930223 : Blo 928581 930223 := bstep (se 1 (by rfl) ⟨697667, by rfl⟩ : syracuseStep 930223 = 1395335) B1395335
theorem B930247 : Blo 928581 930247 := bstep (se 1 (by rfl) ⟨697685, by rfl⟩ : syracuseStep 930247 = 1395371) B1395371
theorem B930267 : Blo 928581 930267 := bstep (se 1 (by rfl) ⟨697700, by rfl⟩ : syracuseStep 930267 = 1395401) B1395401
theorem B930343 : Blo 928581 930343 := bstep (se 1 (by rfl) ⟨697757, by rfl⟩ : syracuseStep 930343 = 1395515) B1395515
theorem B930383 : Blo 928581 930383 := bstep (se 1 (by rfl) ⟨697787, by rfl⟩ : syracuseStep 930383 = 1395575) B1395575
theorem B930399 : Blo 928581 930399 := bstep (se 1 (by rfl) ⟨697799, by rfl⟩ : syracuseStep 930399 = 1395599) B1395599
theorem B930427 : Blo 928581 930427 := bstep (se 1 (by rfl) ⟨697820, by rfl⟩ : syracuseStep 930427 = 1395641) B1395641
theorem B930479 : Blo 928581 930479 := bstep (se 1 (by rfl) ⟨697859, by rfl⟩ : syracuseStep 930479 = 1395719) B1395719
theorem B930503 : Blo 928581 930503 := bstep (se 1 (by rfl) ⟨697877, by rfl⟩ : syracuseStep 930503 = 1395755) B1395755
theorem B930523 : Blo 928581 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B930599 : Blo 928581 930599 := bstep (se 1 (by rfl) ⟨697949, by rfl⟩ : syracuseStep 930599 = 1395899) B1395899
theorem B930639 : Blo 928581 930639 := bstep (se 1 (by rfl) ⟨697979, by rfl⟩ : syracuseStep 930639 = 1395959) B1395959
theorem B930655 : Blo 928581 930655 := bstep (se 1 (by rfl) ⟨697991, by rfl⟩ : syracuseStep 930655 = 1395983) B1395983
theorem B930683 : Blo 928581 930683 := bstep (se 1 (by rfl) ⟨698012, by rfl⟩ : syracuseStep 930683 = 1396025) B1396025
theorem B930735 : Blo 928581 930735 := bstep (se 1 (by rfl) ⟨698051, by rfl⟩ : syracuseStep 930735 = 1396103) B1396103
theorem B930759 : Blo 928581 930759 := bstep (se 1 (by rfl) ⟨698069, by rfl⟩ : syracuseStep 930759 = 1396139) B1396139
theorem B930779 : Blo 928581 930779 := bstep (se 1 (by rfl) ⟨698084, by rfl⟩ : syracuseStep 930779 = 1396169) B1396169
theorem B930855 : Blo 928581 930855 := bstep (se 1 (by rfl) ⟨698141, by rfl⟩ : syracuseStep 930855 = 1396283) B1396283
theorem B930895 : Blo 928581 930895 := bstep (se 1 (by rfl) ⟨698171, by rfl⟩ : syracuseStep 930895 = 1396343) B1396343
theorem B930911 : Blo 928581 930911 := bstep (se 1 (by rfl) ⟨698183, by rfl⟩ : syracuseStep 930911 = 1396367) B1396367
theorem B930939 : Blo 928581 930939 := bstep (se 1 (by rfl) ⟨698204, by rfl⟩ : syracuseStep 930939 = 1396409) B1396409
theorem B930991 : Blo 928581 930991 := bstep (se 1 (by rfl) ⟨698243, by rfl⟩ : syracuseStep 930991 = 1396487) B1396487
theorem B931015 : Blo 928581 931015 := bstep (se 1 (by rfl) ⟨698261, by rfl⟩ : syracuseStep 931015 = 1396523) B1396523
theorem B931035 : Blo 928581 931035 := bstep (se 1 (by rfl) ⟨698276, by rfl⟩ : syracuseStep 931035 = 1396553) B1396553
theorem B931111 : Blo 928581 931111 := bstep (se 1 (by rfl) ⟨698333, by rfl⟩ : syracuseStep 931111 = 1396667) B1396667
theorem B931151 : Blo 928581 931151 := bstep (se 1 (by rfl) ⟨698363, by rfl⟩ : syracuseStep 931151 = 1396727) B1396727
theorem B931167 : Blo 928581 931167 := bstep (se 1 (by rfl) ⟨698375, by rfl⟩ : syracuseStep 931167 = 1396751) B1396751
theorem B1488233 : Blo 928581 1488233 := bstep (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) B1116175
theorem B931195 : Blo 928581 931195 := bstep (se 1 (by rfl) ⟨698396, by rfl⟩ : syracuseStep 931195 = 1396793) B1396793
theorem B931247 : Blo 928581 931247 := bstep (se 1 (by rfl) ⟨698435, by rfl⟩ : syracuseStep 931247 = 1396871) B1396871
theorem B931271 : Blo 928581 931271 := bstep (se 1 (by rfl) ⟨698453, by rfl⟩ : syracuseStep 931271 = 1396907) B1396907
theorem B931291 : Blo 928581 931291 := bstep (se 1 (by rfl) ⟨698468, by rfl⟩ : syracuseStep 931291 = 1396937) B1396937
theorem B23868917 : Blo 928581 23868917 := bstep (se 5 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 23868917 = 2237711) B2237711
theorem B931367 : Blo 928581 931367 := bstep (se 1 (by rfl) ⟨698525, by rfl⟩ : syracuseStep 931367 = 1397051) B1397051
theorem B931407 : Blo 928581 931407 := bstep (se 1 (by rfl) ⟨698555, by rfl⟩ : syracuseStep 931407 = 1397111) B1397111
theorem B931423 : Blo 928581 931423 := bstep (se 1 (by rfl) ⟨698567, by rfl⟩ : syracuseStep 931423 = 1397135) B1397135
theorem B931451 : Blo 928581 931451 := bstep (se 1 (by rfl) ⟨698588, by rfl⟩ : syracuseStep 931451 = 1397177) B1397177
theorem B931503 : Blo 928581 931503 := bstep (se 1 (by rfl) ⟨698627, by rfl⟩ : syracuseStep 931503 = 1397255) B1397255
theorem B931527 : Blo 928581 931527 := bstep (se 1 (by rfl) ⟨698645, by rfl⟩ : syracuseStep 931527 = 1397291) B1397291
theorem B931547 : Blo 928581 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B10761977 : Blo 928581 10761977 := bstep (se 2 (by rfl) ⟨4035741, by rfl⟩ : syracuseStep 10761977 = 8071483) B8071483
theorem B15120121 : Blo 928581 15120121 := bstep (se 2 (by rfl) ⟨5670045, by rfl⟩ : syracuseStep 15120121 = 11340091) B11340091
theorem B931623 : Blo 928581 931623 := bstep (se 1 (by rfl) ⟨698717, by rfl⟩ : syracuseStep 931623 = 1397435) B1397435
theorem B931663 : Blo 928581 931663 := bstep (se 1 (by rfl) ⟨698747, by rfl⟩ : syracuseStep 931663 = 1397495) B1397495
theorem B931679 : Blo 928581 931679 := bstep (se 1 (by rfl) ⟨698759, by rfl⟩ : syracuseStep 931679 = 1397519) B1397519
theorem B931707 : Blo 928581 931707 := bstep (se 1 (by rfl) ⟨698780, by rfl⟩ : syracuseStep 931707 = 1397561) B1397561
theorem B6043553 : Blo 928581 6043553 := bstep (se 2 (by rfl) ⟨2266332, by rfl⟩ : syracuseStep 6043553 = 4532665) B4532665
theorem B931759 : Blo 928581 931759 := bstep (se 1 (by rfl) ⟨698819, by rfl⟩ : syracuseStep 931759 = 1397639) B1397639
theorem B931783 : Blo 928581 931783 := bstep (se 1 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 931783 = 1397675) B1397675
theorem B8599505 : Blo 928581 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B931803 : Blo 928581 931803 := bstep (se 1 (by rfl) ⟨698852, by rfl⟩ : syracuseStep 931803 = 1397705) B1397705
theorem B6043655 : Blo 928581 6043655 := bstep (se 1 (by rfl) ⟨4532741, by rfl⟩ : syracuseStep 6043655 = 9065483) B9065483
theorem B931879 : Blo 928581 931879 := bstep (se 1 (by rfl) ⟨698909, by rfl⟩ : syracuseStep 931879 = 1397819) B1397819
theorem B931919 : Blo 928581 931919 := bstep (se 1 (by rfl) ⟨698939, by rfl⟩ : syracuseStep 931919 = 1397879) B1397879
theorem B931935 : Blo 928581 931935 := bstep (se 1 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 931935 = 1397903) B1397903
theorem B931963 : Blo 928581 931963 := bstep (se 1 (by rfl) ⟨698972, by rfl⟩ : syracuseStep 931963 = 1397945) B1397945
theorem B932015 : Blo 928581 932015 := bstep (se 1 (by rfl) ⟨699011, by rfl⟩ : syracuseStep 932015 = 1398023) B1398023
theorem B932039 : Blo 928581 932039 := bstep (se 1 (by rfl) ⟨699029, by rfl⟩ : syracuseStep 932039 = 1398059) B1398059
theorem B932059 : Blo 928581 932059 := bstep (se 1 (by rfl) ⟨699044, by rfl⟩ : syracuseStep 932059 = 1398089) B1398089
theorem B932135 : Blo 928581 932135 := bstep (se 1 (by rfl) ⟨699101, by rfl⟩ : syracuseStep 932135 = 1398203) B1398203
theorem B932175 : Blo 928581 932175 := bstep (se 1 (by rfl) ⟨699131, by rfl⟩ : syracuseStep 932175 = 1398263) B1398263
theorem B932191 : Blo 928581 932191 := bstep (se 1 (by rfl) ⟨699143, by rfl⟩ : syracuseStep 932191 = 1398287) B1398287
theorem B932219 : Blo 928581 932219 := bstep (se 1 (by rfl) ⟨699164, by rfl⟩ : syracuseStep 932219 = 1398329) B1398329
theorem B932271 : Blo 928581 932271 := bstep (se 1 (by rfl) ⟨699203, by rfl⟩ : syracuseStep 932271 = 1398407) B1398407
theorem B932295 : Blo 928581 932295 := bstep (se 1 (by rfl) ⟨699221, by rfl⟩ : syracuseStep 932295 = 1398443) B1398443
theorem B932315 : Blo 928581 932315 := bstep (se 1 (by rfl) ⟨699236, by rfl⟩ : syracuseStep 932315 = 1398473) B1398473
theorem B932391 : Blo 928581 932391 := bstep (se 1 (by rfl) ⟨699293, by rfl⟩ : syracuseStep 932391 = 1398587) B1398587
theorem B1882703 : Blo 928581 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B932431 : Blo 928581 932431 := bstep (se 1 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 932431 = 1398647) B1398647
theorem B932447 : Blo 928581 932447 := bstep (se 1 (by rfl) ⟨699335, by rfl⟩ : syracuseStep 932447 = 1398671) B1398671
theorem B932475 : Blo 928581 932475 := bstep (se 1 (by rfl) ⟨699356, by rfl⟩ : syracuseStep 932475 = 1398713) B1398713
theorem B932527 : Blo 928581 932527 := bstep (se 1 (by rfl) ⟨699395, by rfl⟩ : syracuseStep 932527 = 1398791) B1398791
theorem B932551 : Blo 928581 932551 := bstep (se 1 (by rfl) ⟨699413, by rfl⟩ : syracuseStep 932551 = 1398827) B1398827
theorem B932571 : Blo 928581 932571 := bstep (se 1 (by rfl) ⟨699428, by rfl⟩ : syracuseStep 932571 = 1398857) B1398857
theorem B1489655 : Blo 928581 1489655 := bstep (se 1 (by rfl) ⟨1117241, by rfl⟩ : syracuseStep 1489655 = 2234483) B2234483
theorem B1719713 : Blo 928581 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B2014969 : Blo 928581 2014969 := bstep (se 2 (by rfl) ⟨755613, by rfl⟩ : syracuseStep 2014969 = 1511227) B1511227
theorem B1491295 : Blo 928581 1491295 := bstep (se 1 (by rfl) ⟨1118471, by rfl⟩ : syracuseStep 1491295 = 2236943) B2236943
theorem B1393001 : Blo 928581 1393001 := bstep (se 2 (by rfl) ⟨522375, by rfl⟩ : syracuseStep 1393001 = 1044751) B1044751
theorem B2834831 : Blo 928581 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B1130927 : Blo 928581 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B1393079 : Blo 928581 1393079 := bstep (se 1 (by rfl) ⟨1044809, by rfl⟩ : syracuseStep 1393079 = 2089619) B2089619
theorem B1393115 : Blo 928581 1393115 := bstep (se 1 (by rfl) ⟨1044836, by rfl⟩ : syracuseStep 1393115 = 2089673) B2089673
theorem B22921751 : Blo 928581 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B7947011 : Blo 928581 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B1393583 : Blo 928581 1393583 := bstep (se 1 (by rfl) ⟨1045187, by rfl⟩ : syracuseStep 1393583 = 2090375) B2090375
theorem B8602625 : Blo 928581 8602625 := bstep (se 2 (by rfl) ⟨3225984, by rfl⟩ : syracuseStep 8602625 = 6451969) B6451969
theorem B1393673 : Blo 928581 1393673 := bstep (se 2 (by rfl) ⟨522627, by rfl⟩ : syracuseStep 1393673 = 1045255) B1045255
theorem B1393703 : Blo 928581 1393703 := bstep (se 1 (by rfl) ⟨1045277, by rfl⟩ : syracuseStep 1393703 = 2090555) B2090555
theorem B1393787 : Blo 928581 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B1393913 : Blo 928581 1393913 := bstep (se 2 (by rfl) ⟨522717, by rfl⟩ : syracuseStep 1393913 = 1045435) B1045435
theorem B1394015 : Blo 928581 1394015 := bstep (se 1 (by rfl) ⟨1045511, by rfl⟩ : syracuseStep 1394015 = 2091023) B2091023
theorem B1394027 : Blo 928581 1394027 := bstep (se 1 (by rfl) ⟨1045520, by rfl⟩ : syracuseStep 1394027 = 2091041) B2091041
theorem B3360143 : Blo 928581 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B1394255 : Blo 928581 1394255 := bstep (se 1 (by rfl) ⟨1045691, by rfl⟩ : syracuseStep 1394255 = 2091383) B2091383
theorem B1394375 : Blo 928581 1394375 := bstep (se 1 (by rfl) ⟨1045781, by rfl⟩ : syracuseStep 1394375 = 2091563) B2091563
theorem B1492679 : Blo 928581 1492679 := bstep (se 1 (by rfl) ⟨1119509, by rfl⟩ : syracuseStep 1492679 = 2239019) B2239019
theorem B4703993 : Blo 928581 4703993 := bstep (se 2 (by rfl) ⟨1763997, by rfl⟩ : syracuseStep 4703993 = 3527995) B3527995
theorem B1394537 : Blo 928581 1394537 := bstep (se 2 (by rfl) ⟨522951, by rfl⟩ : syracuseStep 1394537 = 1045903) B1045903
theorem B1394615 : Blo 928581 1394615 := bstep (se 1 (by rfl) ⟨1045961, by rfl⟩ : syracuseStep 1394615 = 2091923) B2091923
theorem B1394651 : Blo 928581 1394651 := bstep (se 1 (by rfl) ⟨1045988, by rfl⟩ : syracuseStep 1394651 = 2091977) B2091977
theorem B3983417 : Blo 928581 3983417 := bstep (se 2 (by rfl) ⟨1493781, by rfl⟩ : syracuseStep 3983417 = 2987563) B2987563
theorem B13060403 : Blo 928581 13060403 := bstep (se 1 (by rfl) ⟨9795302, by rfl⟩ : syracuseStep 13060403 = 19590605) B19590605
theorem B4245821 : Blo 928581 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B4704641 : Blo 928581 4704641 := bstep (se 2 (by rfl) ⟨1764240, by rfl⟩ : syracuseStep 4704641 = 3528481) B3528481
theorem B1395119 : Blo 928581 1395119 := bstep (se 1 (by rfl) ⟨1046339, by rfl⟩ : syracuseStep 1395119 = 2092679) B2092679
theorem B1395209 : Blo 928581 1395209 := bstep (se 2 (by rfl) ⟨523203, by rfl⟩ : syracuseStep 1395209 = 1046407) B1046407
theorem B1395239 : Blo 928581 1395239 := bstep (se 1 (by rfl) ⟨1046429, by rfl⟩ : syracuseStep 1395239 = 2092859) B2092859
theorem B1395323 : Blo 928581 1395323 := bstep (se 1 (by rfl) ⟨1046492, by rfl⟩ : syracuseStep 1395323 = 2092985) B2092985
theorem B1395449 : Blo 928581 1395449 := bstep (se 2 (by rfl) ⟨523293, by rfl⟩ : syracuseStep 1395449 = 1046587) B1046587
theorem B1395551 : Blo 928581 1395551 := bstep (se 1 (by rfl) ⟨1046663, by rfl⟩ : syracuseStep 1395551 = 2093327) B2093327
theorem B1395563 : Blo 928581 1395563 := bstep (se 1 (by rfl) ⟨1046672, by rfl⟩ : syracuseStep 1395563 = 2093345) B2093345
theorem B7064495 : Blo 928581 7064495 := bstep (se 1 (by rfl) ⟨5298371, by rfl⟩ : syracuseStep 7064495 = 10596743) B10596743
theorem B1395791 : Blo 928581 1395791 := bstep (se 1 (by rfl) ⟨1046843, by rfl⟩ : syracuseStep 1395791 = 2093687) B2093687
theorem B4705451 : Blo 928581 4705451 := bstep (se 1 (by rfl) ⟨3529088, by rfl⟩ : syracuseStep 4705451 = 7058177) B7058177
theorem B1395911 : Blo 928581 1395911 := bstep (se 1 (by rfl) ⟨1046933, by rfl⟩ : syracuseStep 1395911 = 2093867) B2093867
theorem B1396073 : Blo 928581 1396073 := bstep (se 2 (by rfl) ⟨523527, by rfl⟩ : syracuseStep 1396073 = 1047055) B1047055
theorem B1789291 : Blo 928581 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B1396151 : Blo 928581 1396151 := bstep (se 1 (by rfl) ⟨1047113, by rfl⟩ : syracuseStep 1396151 = 2094227) B2094227
theorem B1396187 : Blo 928581 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B1134043 : Blo 928581 1134043 := bstep (se 1 (by rfl) ⟨850532, by rfl⟩ : syracuseStep 1134043 = 1701065) B1701065
theorem B4476539 : Blo 928581 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B4705937 : Blo 928581 4705937 := bstep (se 2 (by rfl) ⟨1764726, by rfl⟩ : syracuseStep 4705937 = 3529453) B3529453
theorem B3526355 : Blo 928581 3526355 := bstep (se 1 (by rfl) ⟨2644766, by rfl⟩ : syracuseStep 3526355 = 5289533) B5289533
theorem B19124099 : Blo 928581 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B1396655 : Blo 928581 1396655 := bstep (se 1 (by rfl) ⟨1047491, by rfl⟩ : syracuseStep 1396655 = 2094983) B2094983
theorem B5951495 : Blo 928581 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B1396745 : Blo 928581 1396745 := bstep (se 2 (by rfl) ⟨523779, by rfl⟩ : syracuseStep 1396745 = 1047559) B1047559
theorem B1396775 : Blo 928581 1396775 := bstep (se 1 (by rfl) ⟨1047581, by rfl⟩ : syracuseStep 1396775 = 2095163) B2095163
theorem B13062221 : Blo 928581 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B1396859 : Blo 928581 1396859 := bstep (se 1 (by rfl) ⟨1047644, by rfl⟩ : syracuseStep 1396859 = 2095289) B2095289
theorem B1396985 : Blo 928581 1396985 := bstep (se 2 (by rfl) ⟨523869, by rfl⟩ : syracuseStep 1396985 = 1047739) B1047739
theorem B1397087 : Blo 928581 1397087 := bstep (se 1 (by rfl) ⟨1047815, by rfl⟩ : syracuseStep 1397087 = 2095631) B2095631
theorem B1397099 : Blo 928581 1397099 := bstep (se 1 (by rfl) ⟨1047824, by rfl⟩ : syracuseStep 1397099 = 2095649) B2095649
theorem B1397327 : Blo 928581 1397327 := bstep (se 1 (by rfl) ⟨1047995, by rfl⟩ : syracuseStep 1397327 = 2095991) B2095991
theorem B1397447 : Blo 928581 1397447 := bstep (se 1 (by rfl) ⟨1048085, by rfl⟩ : syracuseStep 1397447 = 2096171) B2096171
theorem B1397609 : Blo 928581 1397609 := bstep (se 2 (by rfl) ⟨524103, by rfl⟩ : syracuseStep 1397609 = 1048207) B1048207
theorem B1397687 : Blo 928581 1397687 := bstep (se 1 (by rfl) ⟨1048265, by rfl⟩ : syracuseStep 1397687 = 2096531) B2096531
theorem B1397723 : Blo 928581 1397723 := bstep (se 1 (by rfl) ⟨1048292, by rfl⟩ : syracuseStep 1397723 = 2096585) B2096585
theorem B1987591 : Blo 928581 1987591 := bstep (se 1 (by rfl) ⟨1490693, by rfl⟩ : syracuseStep 1987591 = 2981387) B2981387
theorem B3134483 : Blo 928581 3134483 := bstep (se 1 (by rfl) ⟨2350862, by rfl⟩ : syracuseStep 3134483 = 4701725) B4701725
theorem B3134807 : Blo 928581 3134807 := bstep (se 1 (by rfl) ⟨2351105, by rfl⟩ : syracuseStep 3134807 = 4702211) B4702211
theorem B1398191 : Blo 928581 1398191 := bstep (se 1 (by rfl) ⟨1048643, by rfl⟩ : syracuseStep 1398191 = 2097287) B2097287
theorem B6706675 : Blo 928581 6706675 := bstep (se 1 (by rfl) ⟨5030006, by rfl⟩ : syracuseStep 6706675 = 10060013) B10060013
theorem B1398281 : Blo 928581 1398281 := bstep (se 2 (by rfl) ⟨524355, by rfl⟩ : syracuseStep 1398281 = 1048711) B1048711
theorem B1398311 : Blo 928581 1398311 := bstep (se 1 (by rfl) ⟨1048733, by rfl⟩ : syracuseStep 1398311 = 2097467) B2097467
theorem B1398395 : Blo 928581 1398395 := bstep (se 1 (by rfl) ⟨1048796, by rfl⟩ : syracuseStep 1398395 = 2097593) B2097593
theorem B1398521 : Blo 928581 1398521 := bstep (se 2 (by rfl) ⟨524445, by rfl⟩ : syracuseStep 1398521 = 1048891) B1048891
theorem B1398623 : Blo 928581 1398623 := bstep (se 1 (by rfl) ⟨1048967, by rfl⟩ : syracuseStep 1398623 = 2097935) B2097935
theorem B1398635 : Blo 928581 1398635 := bstep (se 1 (by rfl) ⟨1048976, by rfl⟩ : syracuseStep 1398635 = 2097953) B2097953
theorem B37738349 : Blo 928581 37738349 := bstep (se 3 (by rfl) ⟨7075940, by rfl⟩ : syracuseStep 37738349 = 14151881) B14151881
theorem B4708205 : Blo 928581 4708205 := bstep (se 3 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 4708205 = 1765577) B1765577
theorem B6707137 : Blo 928581 6707137 := bstep (se 2 (by rfl) ⟨2515176, by rfl⟩ : syracuseStep 6707137 = 5030353) B5030353
theorem B4708367 : Blo 928581 4708367 := bstep (se 1 (by rfl) ⟨3531275, by rfl⟩ : syracuseStep 4708367 = 7062551) B7062551
theorem B1398863 : Blo 928581 1398863 := bstep (se 1 (by rfl) ⟨1049147, by rfl⟩ : syracuseStep 1398863 = 2098295) B2098295
theorem B3528785 : Blo 928581 3528785 := bstep (se 2 (by rfl) ⟨1323294, by rfl⟩ : syracuseStep 3528785 = 2646589) B2646589
theorem B3135887 : Blo 928581 3135887 := bstep (se 1 (by rfl) ⟨2351915, by rfl⟩ : syracuseStep 3135887 = 4703831) B4703831
theorem B3529241 : Blo 928581 3529241 := bstep (se 2 (by rfl) ⟨1323465, by rfl⟩ : syracuseStep 3529241 = 2646931) B2646931
theorem B11917853 : Blo 928581 11917853 := bstep (se 3 (by rfl) ⟨2234597, by rfl⟩ : syracuseStep 11917853 = 4469195) B4469195
theorem B3136211 : Blo 928581 3136211 := bstep (se 1 (by rfl) ⟨2352158, by rfl⟩ : syracuseStep 3136211 = 4704317) B4704317
theorem B7953299 : Blo 928581 7953299 := bstep (se 1 (by rfl) ⟨5964974, by rfl⟩ : syracuseStep 7953299 = 11929949) B11929949
theorem B13392823 : Blo 928581 13392823 := bstep (se 1 (by rfl) ⟨10044617, by rfl⟩ : syracuseStep 13392823 = 20089235) B20089235
theorem B2907215 : Blo 928581 2907215 := bstep (se 1 (by rfl) ⟨2180411, by rfl⟩ : syracuseStep 2907215 = 4360823) B4360823
theorem B8477891 : Blo 928581 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B4251005 : Blo 928581 4251005 := bstep (se 3 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 4251005 = 1594127) B1594127
theorem B2350579 : Blo 928581 2350579 := bstep (se 1 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 2350579 = 3525869) B3525869
theorem B5955133 : Blo 928581 5955133 := bstep (se 3 (by rfl) ⟨1116587, by rfl⟩ : syracuseStep 5955133 = 2233175) B2233175
theorem B3530425 : Blo 928581 3530425 := bstep (se 2 (by rfl) ⟨1323909, by rfl⟩ : syracuseStep 3530425 = 2647819) B2647819
theorem B3137399 : Blo 928581 3137399 := bstep (se 1 (by rfl) ⟨2353049, by rfl⟩ : syracuseStep 3137399 = 4706099) B4706099
theorem B3628919 : Blo 928581 3628919 := bstep (se 1 (by rfl) ⟨2721689, by rfl⟩ : syracuseStep 3628919 = 5443379) B5443379
theorem B21520247 : Blo 928581 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B7954361 : Blo 928581 7954361 := bstep (se 2 (by rfl) ⟨2982885, by rfl⟩ : syracuseStep 7954361 = 5965771) B5965771
theorem B15916985 : Blo 928581 15916985 := bstep (se 2 (by rfl) ⟨5968869, by rfl⟩ : syracuseStep 15916985 = 11937739) B11937739
theorem B3137615 : Blo 928581 3137615 := bstep (se 1 (by rfl) ⟨2353211, by rfl⟩ : syracuseStep 3137615 = 4706423) B4706423
theorem B8937701 : Blo 928581 8937701 := bstep (se 4 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 8937701 = 1675819) B1675819
theorem B1794487 : Blo 928581 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B3137993 : Blo 928581 3137993 := bstep (se 2 (by rfl) ⟨1176747, by rfl⟩ : syracuseStep 3137993 = 2353495) B2353495
theorem B9069079 : Blo 928581 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B2089511 : Blo 928581 2089511 := bstep (se 1 (by rfl) ⟨1567133, by rfl⟩ : syracuseStep 2089511 = 3134267) B3134267
theorem B2351713 : Blo 928581 2351713 := bstep (se 2 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 2351713 = 1763785) B1763785
theorem B4711121 : Blo 928581 4711121 := bstep (se 2 (by rfl) ⟨1766670, by rfl⟩ : syracuseStep 4711121 = 3533341) B3533341
theorem B3138263 : Blo 928581 3138263 := bstep (se 1 (by rfl) ⟨2353697, by rfl⟩ : syracuseStep 3138263 = 4707395) B4707395
theorem B1696505 : Blo 928581 1696505 := bstep (se 2 (by rfl) ⟨636189, by rfl⟩ : syracuseStep 1696505 = 1272379) B1272379
theorem B2089835 : Blo 928581 2089835 := bstep (se 1 (by rfl) ⟨1567376, by rfl⟩ : syracuseStep 2089835 = 3134753) B3134753
theorem B6808465 : Blo 928581 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B2089889 : Blo 928581 2089889 := bstep (se 2 (by rfl) ⟨783708, by rfl⟩ : syracuseStep 2089889 = 1567417) B1567417
theorem B3138479 : Blo 928581 3138479 := bstep (se 1 (by rfl) ⟨2353859, by rfl⟩ : syracuseStep 3138479 = 4707719) B4707719
theorem B26797175 : Blo 928581 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B10216651 : Blo 928581 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B2090231 : Blo 928581 2090231 := bstep (se 1 (by rfl) ⟨1567673, by rfl⟩ : syracuseStep 2090231 = 3135347) B3135347
theorem B3532157 : Blo 928581 3532157 := bstep (se 3 (by rfl) ⟨662279, by rfl⟩ : syracuseStep 3532157 = 1324559) B1324559
theorem B2352665 : Blo 928581 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B2090825 : Blo 928581 2090825 := bstep (se 2 (by rfl) ⟨784059, by rfl⟩ : syracuseStep 2090825 = 1568119) B1568119
theorem B13428575 : Blo 928581 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B2647991 : Blo 928581 2647991 := bstep (se 1 (by rfl) ⟨1985993, by rfl⟩ : syracuseStep 2647991 = 3971987) B3971987
theorem B2353171 : Blo 928581 2353171 := bstep (se 1 (by rfl) ⟨1764878, by rfl⟩ : syracuseStep 2353171 = 3529757) B3529757
theorem B2975915 : Blo 928581 2975915 := bstep (se 1 (by rfl) ⟨2231936, by rfl⟩ : syracuseStep 2975915 = 4463873) B4463873
theorem B1763527 : Blo 928581 1763527 := bstep (se 1 (by rfl) ⟨1322645, by rfl⟩ : syracuseStep 1763527 = 2645291) B2645291
theorem B23816429 : Blo 928581 23816429 := bstep (se 3 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 23816429 = 8931161) B8931161
theorem B1567289 : Blo 928581 1567289 := bstep (se 2 (by rfl) ⟨587733, by rfl⟩ : syracuseStep 1567289 = 1175467) B1175467
theorem B2091617 : Blo 928581 2091617 := bstep (se 2 (by rfl) ⟨784356, by rfl⟩ : syracuseStep 2091617 = 1568713) B1568713
theorem B10316489 : Blo 928581 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B1764089 : Blo 928581 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B1764271 : Blo 928581 1764271 := bstep (se 1 (by rfl) ⟨1323203, by rfl⟩ : syracuseStep 1764271 = 2646407) B2646407
theorem B2091959 : Blo 928581 2091959 := bstep (se 1 (by rfl) ⟨1568969, by rfl⟩ : syracuseStep 2091959 = 3137939) B3137939
theorem B6810551 : Blo 928581 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B5041079 : Blo 928581 5041079 := bstep (se 1 (by rfl) ⟨3780809, by rfl⟩ : syracuseStep 5041079 = 7561619) B7561619
theorem B2649095 : Blo 928581 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B2354255 : Blo 928581 2354255 := bstep (se 1 (by rfl) ⟨1765691, by rfl⟩ : syracuseStep 2354255 = 3531383) B3531383
theorem B4713551 : Blo 928581 4713551 := bstep (se 1 (by rfl) ⟨3535163, by rfl⟩ : syracuseStep 4713551 = 7070327) B7070327
theorem B1567991 : Blo 928581 1567991 := bstep (se 1 (by rfl) ⟨1175993, by rfl⟩ : syracuseStep 1567991 = 2351987) B2351987
theorem B3140855 : Blo 928581 3140855 := bstep (se 1 (by rfl) ⟨2355641, by rfl⟩ : syracuseStep 3140855 = 4711283) B4711283
theorem B24177953 : Blo 928581 24177953 := bstep (se 2 (by rfl) ⟨9066732, by rfl⟩ : syracuseStep 24177953 = 18133465) B18133465
theorem B2649449 : Blo 928581 2649449 := bstep (se 2 (by rfl) ⟨993543, by rfl⟩ : syracuseStep 2649449 = 1987087) B1987087
theorem B3534299 : Blo 928581 3534299 := bstep (se 1 (by rfl) ⟨2650724, by rfl⟩ : syracuseStep 3534299 = 5301449) B5301449
theorem B7073243 : Blo 928581 7073243 := bstep (se 1 (by rfl) ⟨5304932, by rfl⟩ : syracuseStep 7073243 = 10609865) B10609865
theorem B2092553 : Blo 928581 2092553 := bstep (se 2 (by rfl) ⟨784707, by rfl⟩ : syracuseStep 2092553 = 1569415) B1569415
theorem B1437193 : Blo 928581 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B3141179 : Blo 928581 3141179 := bstep (se 1 (by rfl) ⟨2355884, by rfl⟩ : syracuseStep 3141179 = 4711769) B4711769
theorem B1568335 : Blo 928581 1568335 := bstep (se 1 (by rfl) ⟨1176251, by rfl⟩ : syracuseStep 1568335 = 2352503) B2352503
theorem B1175239 : Blo 928581 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B2354903 : Blo 928581 2354903 := bstep (se 1 (by rfl) ⟨1766177, by rfl⟩ : syracuseStep 2354903 = 3532355) B3532355
theorem B4714199 : Blo 928581 4714199 := bstep (se 1 (by rfl) ⟨3535649, by rfl⟩ : syracuseStep 4714199 = 7071299) B7071299
theorem B1568585 : Blo 928581 1568585 := bstep (se 2 (by rfl) ⟨588219, by rfl⟩ : syracuseStep 1568585 = 1176439) B1176439
theorem B3141449 : Blo 928581 3141449 := bstep (se 2 (by rfl) ⟨1178043, by rfl⟩ : syracuseStep 3141449 = 2356087) B2356087
theorem B2092895 : Blo 928581 2092895 := bstep (se 1 (by rfl) ⟨1569671, by rfl⟩ : syracuseStep 2092895 = 3139343) B3139343
theorem B7073729 : Blo 928581 7073729 := bstep (se 2 (by rfl) ⟨2652648, by rfl⟩ : syracuseStep 7073729 = 5305297) B5305297
theorem B2093075 : Blo 928581 2093075 := bstep (se 1 (by rfl) ⟨1569806, by rfl⟩ : syracuseStep 2093075 = 3139613) B3139613
theorem B2355257 : Blo 928581 2355257 := bstep (se 2 (by rfl) ⟨883221, by rfl⟩ : syracuseStep 2355257 = 1766443) B1766443
theorem B1765547 : Blo 928581 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B1044679 : Blo 928581 1044679 := bstep (se 1 (by rfl) ⟨783509, by rfl⟩ : syracuseStep 1044679 = 1567019) B1567019
theorem B1569017 : Blo 928581 1569017 := bstep (se 2 (by rfl) ⟨588381, by rfl⟩ : syracuseStep 1569017 = 1176763) B1176763
theorem B2093417 : Blo 928581 2093417 := bstep (se 2 (by rfl) ⟨785031, by rfl⟩ : syracuseStep 2093417 = 1570063) B1570063
theorem B1765775 : Blo 928581 1765775 := bstep (se 1 (by rfl) ⟨1324331, by rfl⟩ : syracuseStep 1765775 = 2648663) B2648663
theorem B1569199 : Blo 928581 1569199 := bstep (se 1 (by rfl) ⟨1176899, by rfl⟩ : syracuseStep 1569199 = 2353799) B2353799
theorem B15692291 : Blo 928581 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B1569287 : Blo 928581 1569287 := bstep (se 1 (by rfl) ⟨1176965, by rfl⟩ : syracuseStep 1569287 = 2353931) B2353931
theorem B2519675 : Blo 928581 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B2978489 : Blo 928581 2978489 := bstep (se 2 (by rfl) ⟨1116933, by rfl⟩ : syracuseStep 2978489 = 2233867) B2233867
theorem B3535559 : Blo 928581 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B11465425 : Blo 928581 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B1569631 : Blo 928581 1569631 := bstep (se 1 (by rfl) ⟨1177223, by rfl⟩ : syracuseStep 1569631 = 2354447) B2354447
theorem B3830689 : Blo 928581 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B1569719 : Blo 928581 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B3142583 : Blo 928581 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B2094011 : Blo 928581 2094011 := bstep (se 1 (by rfl) ⟨1570508, by rfl⟩ : syracuseStep 2094011 = 3141017) B3141017
theorem B1045543 : Blo 928581 1045543 := bstep (se 1 (by rfl) ⟨784157, by rfl⟩ : syracuseStep 1045543 = 1568315) B1568315
theorem B2094137 : Blo 928581 2094137 := bstep (se 2 (by rfl) ⟨785301, by rfl⟩ : syracuseStep 2094137 = 1570603) B1570603
theorem B7075187 : Blo 928581 7075187 := bstep (se 1 (by rfl) ⟨5306390, by rfl⟩ : syracuseStep 7075187 = 10612781) B10612781
theorem B3536257 : Blo 928581 3536257 := bstep (se 2 (by rfl) ⟨1326096, by rfl⟩ : syracuseStep 3536257 = 2652193) B2652193
theorem B2094479 : Blo 928581 2094479 := bstep (se 1 (by rfl) ⟨1570859, by rfl⟩ : syracuseStep 2094479 = 3141719) B3141719
theorem B11924981 : Blo 928581 11924981 := bstep (se 5 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 11924981 = 1117967) B1117967
theorem B1570313 : Blo 928581 1570313 := bstep (se 2 (by rfl) ⟨588867, by rfl⟩ : syracuseStep 1570313 = 1177735) B1177735
theorem B3143177 : Blo 928581 3143177 := bstep (se 2 (by rfl) ⟨1178691, by rfl⟩ : syracuseStep 3143177 = 2357383) B2357383
theorem B1767035 : Blo 928581 1767035 := bstep (se 1 (by rfl) ⟨1325276, by rfl⟩ : syracuseStep 1767035 = 2650553) B2650553
theorem B5666449 : Blo 928581 5666449 := bstep (se 2 (by rfl) ⟨2124918, by rfl⟩ : syracuseStep 5666449 = 4249837) B4249837
theorem B3536531 : Blo 928581 3536531 := bstep (se 1 (by rfl) ⟨2652398, by rfl⟩ : syracuseStep 3536531 = 5304797) B5304797
theorem B1570475 : Blo 928581 1570475 := bstep (se 1 (by rfl) ⟨1177856, by rfl⟩ : syracuseStep 1570475 = 2355713) B2355713
theorem B2094803 : Blo 928581 2094803 := bstep (se 1 (by rfl) ⟨1571102, by rfl⟩ : syracuseStep 2094803 = 3142205) B3142205
theorem B2652011 : Blo 928581 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B3766135 : Blo 928581 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B1570873 : Blo 928581 1570873 := bstep (se 2 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 1570873 = 1178155) B1178155
theorem B1177679 : Blo 928581 1177679 := bstep (se 1 (by rfl) ⟨883259, by rfl⟩ : syracuseStep 1177679 = 1766519) B1766519
theorem B2652239 : Blo 928581 2652239 := bstep (se 1 (by rfl) ⟨1989179, by rfl⟩ : syracuseStep 2652239 = 3978359) B3978359
theorem B1767521 : Blo 928581 1767521 := bstep (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) B1325641
theorem B1571015 : Blo 928581 1571015 := bstep (se 1 (by rfl) ⟨1178261, by rfl⟩ : syracuseStep 1571015 = 2356523) B2356523
theorem B2357495 : Blo 928581 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B1767673 : Blo 928581 1767673 := bstep (se 2 (by rfl) ⟨662877, by rfl⟩ : syracuseStep 1767673 = 1325755) B1325755
theorem B1571177 : Blo 928581 1571177 := bstep (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) B1178383
theorem B3144041 : Blo 928581 3144041 := bstep (se 2 (by rfl) ⟨1179015, by rfl⟩ : syracuseStep 3144041 = 2358031) B2358031
theorem B4717115 : Blo 928581 4717115 := bstep (se 1 (by rfl) ⟨3537836, by rfl⟩ : syracuseStep 4717115 = 7075673) B7075673
theorem B1047163 : Blo 928581 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B2095739 : Blo 928581 2095739 := bstep (se 1 (by rfl) ⟨1571804, by rfl⟩ : syracuseStep 2095739 = 3143609) B3143609
theorem B1571575 : Blo 928581 1571575 := bstep (se 1 (by rfl) ⟨1178681, by rfl⟩ : syracuseStep 1571575 = 2357363) B2357363
theorem B2095865 : Blo 928581 2095865 := bstep (se 2 (by rfl) ⟨785949, by rfl⟩ : syracuseStep 2095865 = 1571899) B1571899
theorem B10615697 : Blo 928581 10615697 := bstep (se 2 (by rfl) ⟨3980886, by rfl⟩ : syracuseStep 10615697 = 7961773) B7961773
theorem B1571771 : Blo 928581 1571771 := bstep (se 1 (by rfl) ⟨1178828, by rfl⟩ : syracuseStep 1571771 = 2357657) B2357657
theorem B3144635 : Blo 928581 3144635 := bstep (se 1 (by rfl) ⟨2358476, by rfl⟩ : syracuseStep 3144635 = 4716953) B4716953
theorem B2096135 : Blo 928581 2096135 := bstep (se 1 (by rfl) ⟨1572101, by rfl⟩ : syracuseStep 2096135 = 3144203) B3144203
theorem B1571879 : Blo 928581 1571879 := bstep (se 1 (by rfl) ⟨1178909, by rfl⟩ : syracuseStep 1571879 = 2357819) B2357819
theorem B1047631 : Blo 928581 1047631 := bstep (se 1 (by rfl) ⟨785723, by rfl⟩ : syracuseStep 1047631 = 1571447) B1571447
theorem B2096207 : Blo 928581 2096207 := bstep (se 1 (by rfl) ⟨1572155, by rfl⟩ : syracuseStep 2096207 = 3144311) B3144311
theorem B4717763 : Blo 928581 4717763 := bstep (se 1 (by rfl) ⟨3538322, by rfl⟩ : syracuseStep 4717763 = 7076645) B7076645
theorem B3538187 : Blo 928581 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B1572169 : Blo 928581 1572169 := bstep (se 2 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 1572169 = 1179127) B1179127
theorem B1178975 : Blo 928581 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B1572203 : Blo 928581 1572203 := bstep (se 1 (by rfl) ⟨1179152, by rfl⟩ : syracuseStep 1572203 = 2358305) B2358305
theorem B3767771 : Blo 928581 3767771 := bstep (se 1 (by rfl) ⟨2825828, by rfl⟩ : syracuseStep 3767771 = 5651657) B5651657
theorem B1048027 : Blo 928581 1048027 := bstep (se 1 (by rfl) ⟨786020, by rfl⟩ : syracuseStep 1048027 = 1572041) B1572041
theorem B2096603 : Blo 928581 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B1768979 : Blo 928581 1768979 := bstep (se 1 (by rfl) ⟨1326734, by rfl⟩ : syracuseStep 1768979 = 2653469) B2653469
theorem B1769131 : Blo 928581 1769131 := bstep (se 1 (by rfl) ⟨1326848, by rfl⟩ : syracuseStep 1769131 = 2653697) B2653697
theorem B2358983 : Blo 928581 2358983 := bstep (se 1 (by rfl) ⟨1769237, by rfl⟩ : syracuseStep 2358983 = 3538475) B3538475
theorem B1572601 : Blo 928581 1572601 := bstep (se 2 (by rfl) ⟨589725, by rfl⟩ : syracuseStep 1572601 = 1179451) B1179451
theorem B8060705 : Blo 928581 8060705 := bstep (se 2 (by rfl) ⟨3022764, by rfl⟩ : syracuseStep 8060705 = 6045529) B6045529
theorem B1769359 : Blo 928581 1769359 := bstep (se 1 (by rfl) ⟨1327019, by rfl⟩ : syracuseStep 1769359 = 2654039) B2654039
theorem B1048495 : Blo 928581 1048495 := bstep (se 1 (by rfl) ⟨786371, by rfl⟩ : syracuseStep 1048495 = 1572743) B1572743
theorem B2097071 : Blo 928581 2097071 := bstep (se 1 (by rfl) ⟨1572803, by rfl⟩ : syracuseStep 2097071 = 3145607) B3145607
theorem B1769435 : Blo 928581 1769435 := bstep (se 1 (by rfl) ⟨1327076, by rfl⟩ : syracuseStep 1769435 = 2654153) B2654153
theorem B2097161 : Blo 928581 2097161 := bstep (se 2 (by rfl) ⟨786435, by rfl⟩ : syracuseStep 2097161 = 1572871) B1572871
theorem B2097575 : Blo 928581 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B1048999 : Blo 928581 1048999 := bstep (se 1 (by rfl) ⟨786749, by rfl⟩ : syracuseStep 1048999 = 1573499) B1573499
theorem B2359763 : Blo 928581 2359763 := bstep (se 1 (by rfl) ⟨1769822, by rfl⟩ : syracuseStep 2359763 = 3539645) B3539645
theorem B2097683 : Blo 928581 2097683 := bstep (se 1 (by rfl) ⟨1573262, by rfl⟩ : syracuseStep 2097683 = 3146525) B3146525
theorem B10060321 : Blo 928581 10060321 := bstep (se 2 (by rfl) ⟨3772620, by rfl⟩ : syracuseStep 10060321 = 7545241) B7545241
theorem B2097737 : Blo 928581 2097737 := bstep (se 2 (by rfl) ⟨786651, by rfl⟩ : syracuseStep 2097737 = 1573303) B1573303
theorem B2392649 : Blo 928581 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B12092105 : Blo 928581 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B2098151 : Blo 928581 2098151 := bstep (se 1 (by rfl) ⟨1573613, by rfl⟩ : syracuseStep 2098151 = 3147227) B3147227
theorem B3146849 : Blo 928581 3146849 := bstep (se 2 (by rfl) ⟨1180068, by rfl⟩ : syracuseStep 3146849 = 2360137) B2360137
theorem B3015805 : Blo 928581 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B9077953 : Blo 928581 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B2655611 : Blo 928581 2655611 := bstep (se 1 (by rfl) ⟨1991708, by rfl⟩ : syracuseStep 2655611 = 3983417) B3983417
theorem B7178129 : Blo 928581 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B4524013 : Blo 928581 4524013 := bstep (se 3 (by rfl) ⟨848252, by rfl⟩ : syracuseStep 4524013 = 1696505) B1696505
theorem B2984359 : Blo 928581 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B16091621 : Blo 928581 16091621 := bstep (se 4 (by rfl) ⟨1508589, by rfl⟩ : syracuseStep 16091621 = 3017179) B3017179
theorem B17861093 : Blo 928581 17861093 := bstep (se 4 (by rfl) ⟨1674477, by rfl⟩ : syracuseStep 17861093 = 3348955) B3348955
theorem B12749399 : Blo 928581 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B22940333 : Blo 928581 22940333 := bstep (se 3 (by rfl) ⟨4301312, by rfl⟩ : syracuseStep 22940333 = 8602625) B8602625
theorem B3967663 : Blo 928581 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B5966615 : Blo 928581 5966615 := bstep (se 1 (by rfl) ⟨4474961, by rfl⟩ : syracuseStep 5966615 = 8949923) B8949923
theorem B3968621 : Blo 928581 3968621 := bstep (se 3 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 3968621 = 1488233) B1488233
theorem B2232119 : Blo 928581 2232119 := bstep (se 1 (by rfl) ⟨1674089, by rfl⟩ : syracuseStep 2232119 = 3348179) B3348179
theorem B1938143 : Blo 928581 1938143 := bstep (se 1 (by rfl) ⟨1453607, by rfl⟩ : syracuseStep 1938143 = 2907215) B2907215
theorem B1676641 : Blo 928581 1676641 := bstep (se 2 (by rfl) ⟨628740, by rfl⟩ : syracuseStep 1676641 = 1257481) B1257481
theorem B4462391 : Blo 928581 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B17864783 : Blo 928581 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B8952383 : Blo 928581 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B5020541 : Blo 928581 5020541 := bstep (se 3 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 5020541 = 1882703) B1882703
theorem B2235367 : Blo 928581 2235367 := bstep (se 1 (by rfl) ⟨1676525, by rfl⟩ : syracuseStep 2235367 = 3353051) B3353051
theorem B2235809 : Blo 928581 2235809 := bstep (se 2 (by rfl) ⟨838428, by rfl⟩ : syracuseStep 2235809 = 1676857) B1676857
theorem B110042549 : Blo 928581 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B20160161 : Blo 928581 20160161 := bstep (se 2 (by rfl) ⟨7560060, by rfl⟩ : syracuseStep 20160161 = 15120121) B15120121
theorem B5021513 : Blo 928581 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B4464659 : Blo 928581 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B10461527 : Blo 928581 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B1679783 : Blo 928581 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B40772105 : Blo 928581 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B4466333 : Blo 928581 4466333 := bstep (se 3 (by rfl) ⟨837437, by rfl⟩ : syracuseStep 4466333 = 1674875) B1674875
theorem B993103 : Blo 928581 993103 := bstep (se 1 (by rfl) ⟨744827, by rfl⟩ : syracuseStep 993103 = 1489655) B1489655
theorem B7940177 : Blo 928581 7940177 := bstep (se 2 (by rfl) ⟨2977566, by rfl⟩ : syracuseStep 7940177 = 5955133) B5955133
theorem B9677117 : Blo 928581 9677117 := bstep (se 3 (by rfl) ⟨1814459, by rfl⟩ : syracuseStep 9677117 = 3628919) B3628919
theorem B57387325 : Blo 928581 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B4467581 : Blo 928581 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B928667 : Blo 928581 928667 := bstep (se 1 (by rfl) ⟨696500, by rfl⟩ : syracuseStep 928667 = 1393001) B1393001
theorem B928719 : Blo 928581 928719 := bstep (se 1 (by rfl) ⟨696539, by rfl⟩ : syracuseStep 928719 = 1393079) B1393079
theorem B928743 : Blo 928581 928743 := bstep (se 1 (by rfl) ⟨696557, by rfl⟩ : syracuseStep 928743 = 1393115) B1393115
theorem B15281167 : Blo 928581 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B3976411 : Blo 928581 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B3189979 : Blo 928581 3189979 := bstep (se 1 (by rfl) ⟨2392484, by rfl⟩ : syracuseStep 3189979 = 4784969) B4784969
theorem B929055 : Blo 928581 929055 := bstep (se 1 (by rfl) ⟨696791, by rfl⟩ : syracuseStep 929055 = 1393583) B1393583
theorem B929115 : Blo 928581 929115 := bstep (se 1 (by rfl) ⟨696836, by rfl⟩ : syracuseStep 929115 = 1393673) B1393673
theorem B929135 : Blo 928581 929135 := bstep (se 1 (by rfl) ⟨696851, by rfl⟩ : syracuseStep 929135 = 1393703) B1393703
theorem B929191 : Blo 928581 929191 := bstep (se 1 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 929191 = 1393787) B1393787
theorem B929275 : Blo 928581 929275 := bstep (se 1 (by rfl) ⟨696956, by rfl⟩ : syracuseStep 929275 = 1393913) B1393913
theorem B929343 : Blo 928581 929343 := bstep (se 1 (by rfl) ⟨697007, by rfl⟩ : syracuseStep 929343 = 1394015) B1394015
theorem B929351 : Blo 928581 929351 := bstep (se 1 (by rfl) ⟨697013, by rfl⟩ : syracuseStep 929351 = 1394027) B1394027
theorem B929503 : Blo 928581 929503 := bstep (se 1 (by rfl) ⟨697127, by rfl⟩ : syracuseStep 929503 = 1394255) B1394255
theorem B929583 : Blo 928581 929583 := bstep (se 1 (by rfl) ⟨697187, by rfl⟩ : syracuseStep 929583 = 1394375) B1394375
theorem B5025665 : Blo 928581 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B929691 : Blo 928581 929691 := bstep (se 1 (by rfl) ⟨697268, by rfl⟩ : syracuseStep 929691 = 1394537) B1394537
theorem B929743 : Blo 928581 929743 := bstep (se 1 (by rfl) ⟨697307, by rfl⟩ : syracuseStep 929743 = 1394615) B1394615
theorem B929767 : Blo 928581 929767 := bstep (se 1 (by rfl) ⟨697325, by rfl⟩ : syracuseStep 929767 = 1394651) B1394651
theorem B3977369 : Blo 928581 3977369 := bstep (se 2 (by rfl) ⟨1491513, by rfl⟩ : syracuseStep 3977369 = 2983027) B2983027
theorem B2830547 : Blo 928581 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B45363473 : Blo 928581 45363473 := bstep (se 2 (by rfl) ⟨17011302, by rfl⟩ : syracuseStep 45363473 = 34022605) B34022605
theorem B930079 : Blo 928581 930079 := bstep (se 1 (by rfl) ⟨697559, by rfl⟩ : syracuseStep 930079 = 1395119) B1395119
theorem B930139 : Blo 928581 930139 := bstep (se 1 (by rfl) ⟨697604, by rfl⟩ : syracuseStep 930139 = 1395209) B1395209
theorem B930159 : Blo 928581 930159 := bstep (se 1 (by rfl) ⟨697619, by rfl⟩ : syracuseStep 930159 = 1395239) B1395239
theorem B930215 : Blo 928581 930215 := bstep (se 1 (by rfl) ⟨697661, by rfl⟩ : syracuseStep 930215 = 1395323) B1395323
theorem B7942637 : Blo 928581 7942637 := bstep (se 3 (by rfl) ⟨1489244, by rfl⟩ : syracuseStep 7942637 = 2978489) B2978489
theorem B930299 : Blo 928581 930299 := bstep (se 1 (by rfl) ⟨697724, by rfl⟩ : syracuseStep 930299 = 1395449) B1395449
theorem B930367 : Blo 928581 930367 := bstep (se 1 (by rfl) ⟨697775, by rfl⟩ : syracuseStep 930367 = 1395551) B1395551
theorem B930375 : Blo 928581 930375 := bstep (se 1 (by rfl) ⟨697781, by rfl⟩ : syracuseStep 930375 = 1395563) B1395563
theorem B10072775 : Blo 928581 10072775 := bstep (se 1 (by rfl) ⟨7554581, by rfl⟩ : syracuseStep 10072775 = 15109163) B15109163
theorem B930527 : Blo 928581 930527 := bstep (se 1 (by rfl) ⟨697895, by rfl⟩ : syracuseStep 930527 = 1395791) B1395791
theorem B930607 : Blo 928581 930607 := bstep (se 1 (by rfl) ⟨697955, by rfl⟩ : syracuseStep 930607 = 1395911) B1395911
theorem B930715 : Blo 928581 930715 := bstep (se 1 (by rfl) ⟨698036, by rfl⟩ : syracuseStep 930715 = 1396073) B1396073
theorem B930767 : Blo 928581 930767 := bstep (se 1 (by rfl) ⟨698075, by rfl⟩ : syracuseStep 930767 = 1396151) B1396151
theorem B930791 : Blo 928581 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B931103 : Blo 928581 931103 := bstep (se 1 (by rfl) ⟨698327, by rfl⟩ : syracuseStep 931103 = 1396655) B1396655
theorem B931163 : Blo 928581 931163 := bstep (se 1 (by rfl) ⟨698372, by rfl⟩ : syracuseStep 931163 = 1396745) B1396745
theorem B931183 : Blo 928581 931183 := bstep (se 1 (by rfl) ⟨698387, by rfl⟩ : syracuseStep 931183 = 1396775) B1396775
theorem B931239 : Blo 928581 931239 := bstep (se 1 (by rfl) ⟨698429, by rfl⟩ : syracuseStep 931239 = 1396859) B1396859
theorem B931323 : Blo 928581 931323 := bstep (se 1 (by rfl) ⟨698492, by rfl⟩ : syracuseStep 931323 = 1396985) B1396985
theorem B931391 : Blo 928581 931391 := bstep (se 1 (by rfl) ⟨698543, by rfl⟩ : syracuseStep 931391 = 1397087) B1397087
theorem B931399 : Blo 928581 931399 := bstep (se 1 (by rfl) ⟨698549, by rfl⟩ : syracuseStep 931399 = 1397099) B1397099
theorem B931551 : Blo 928581 931551 := bstep (se 1 (by rfl) ⟨698663, by rfl⟩ : syracuseStep 931551 = 1397327) B1397327
theorem B931631 : Blo 928581 931631 := bstep (se 1 (by rfl) ⟨698723, by rfl⟩ : syracuseStep 931631 = 1397447) B1397447
theorem B931739 : Blo 928581 931739 := bstep (se 1 (by rfl) ⟨698804, by rfl⟩ : syracuseStep 931739 = 1397609) B1397609
theorem B931791 : Blo 928581 931791 := bstep (se 1 (by rfl) ⟨698843, by rfl⟩ : syracuseStep 931791 = 1397687) B1397687
theorem B931815 : Blo 928581 931815 := bstep (se 1 (by rfl) ⟨698861, by rfl⟩ : syracuseStep 931815 = 1397723) B1397723
theorem B932127 : Blo 928581 932127 := bstep (se 1 (by rfl) ⟨699095, by rfl⟩ : syracuseStep 932127 = 1398191) B1398191
theorem B932187 : Blo 928581 932187 := bstep (se 1 (by rfl) ⟨699140, by rfl⟩ : syracuseStep 932187 = 1398281) B1398281
theorem B932207 : Blo 928581 932207 := bstep (se 1 (by rfl) ⟨699155, by rfl⟩ : syracuseStep 932207 = 1398311) B1398311
theorem B8960381 : Blo 928581 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B932263 : Blo 928581 932263 := bstep (se 1 (by rfl) ⟨699197, by rfl⟩ : syracuseStep 932263 = 1398395) B1398395
theorem B932347 : Blo 928581 932347 := bstep (se 1 (by rfl) ⟨699260, by rfl⟩ : syracuseStep 932347 = 1398521) B1398521
theorem B5290535 : Blo 928581 5290535 := bstep (se 1 (by rfl) ⟨3967901, by rfl⟩ : syracuseStep 5290535 = 7935803) B7935803
theorem B932415 : Blo 928581 932415 := bstep (se 1 (by rfl) ⟨699311, by rfl⟩ : syracuseStep 932415 = 1398623) B1398623
theorem B932423 : Blo 928581 932423 := bstep (se 1 (by rfl) ⟨699317, by rfl⟩ : syracuseStep 932423 = 1398635) B1398635
theorem B932575 : Blo 928581 932575 := bstep (se 1 (by rfl) ⟨699431, by rfl⟩ : syracuseStep 932575 = 1398863) B1398863
theorem B1489835 : Blo 928581 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B7945235 : Blo 928581 7945235 := bstep (se 1 (by rfl) ⟨5958926, by rfl⟩ : syracuseStep 7945235 = 11917853) B11917853
theorem B3980477 : Blo 928581 3980477 := bstep (se 3 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 3980477 = 1492679) B1492679
theorem B1916257 : Blo 928581 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B4767113 : Blo 928581 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B5651927 : Blo 928581 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B1588729 : Blo 928581 1588729 := bstep (se 2 (by rfl) ⟨595773, by rfl⟩ : syracuseStep 1588729 = 1191547) B1191547
theorem B2834003 : Blo 928581 2834003 := bstep (se 1 (by rfl) ⟨2125502, by rfl⟩ : syracuseStep 2834003 = 4251005) B4251005
theorem B418234211 : Blo 928581 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B1392905 : Blo 928581 1392905 := bstep (se 2 (by rfl) ⟨522339, by rfl⟩ : syracuseStep 1392905 = 1044679) B1044679
theorem B1393007 : Blo 928581 1393007 := bstep (se 1 (by rfl) ⟨1044755, by rfl⟩ : syracuseStep 1393007 = 2089511) B2089511
theorem B3981743 : Blo 928581 3981743 := bstep (se 1 (by rfl) ⟨2986307, by rfl⟩ : syracuseStep 3981743 = 5972615) B5972615
theorem B1393223 : Blo 928581 1393223 := bstep (se 1 (by rfl) ⟨1044917, by rfl⟩ : syracuseStep 1393223 = 2089835) B2089835
theorem B1393259 : Blo 928581 1393259 := bstep (se 1 (by rfl) ⟨1044944, by rfl⟩ : syracuseStep 1393259 = 2089889) B2089889
theorem B1884779 : Blo 928581 1884779 := bstep (se 1 (by rfl) ⟨1413584, by rfl⟩ : syracuseStep 1884779 = 2827169) B2827169
theorem B441762497 : Blo 928581 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B1393487 : Blo 928581 1393487 := bstep (se 1 (by rfl) ⟨1045115, by rfl⟩ : syracuseStep 1393487 = 2090231) B2090231
theorem B15287233 : Blo 928581 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B1393883 : Blo 928581 1393883 := bstep (se 1 (by rfl) ⟨1045412, by rfl⟩ : syracuseStep 1393883 = 2090825) B2090825
theorem B18138455 : Blo 928581 18138455 := bstep (se 1 (by rfl) ⟨13603841, by rfl⟩ : syracuseStep 18138455 = 27207683) B27207683
theorem B1394057 : Blo 928581 1394057 := bstep (se 2 (by rfl) ⟨522771, by rfl⟩ : syracuseStep 1394057 = 1045543) B1045543
theorem B1983943 : Blo 928581 1983943 := bstep (se 1 (by rfl) ⟨1487957, by rfl⟩ : syracuseStep 1983943 = 2975915) B2975915
theorem B15877619 : Blo 928581 15877619 := bstep (se 1 (by rfl) ⟨11908214, by rfl⟩ : syracuseStep 15877619 = 23816429) B23816429
theorem B1394411 : Blo 928581 1394411 := bstep (se 1 (by rfl) ⟨1045808, by rfl⟩ : syracuseStep 1394411 = 2091617) B2091617
theorem B1394639 : Blo 928581 1394639 := bstep (se 1 (by rfl) ⟨1045979, by rfl⟩ : syracuseStep 1394639 = 2091959) B2091959
theorem B4540367 : Blo 928581 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B3360719 : Blo 928581 3360719 := bstep (se 1 (by rfl) ⟨2520539, by rfl⟩ : syracuseStep 3360719 = 5041079) B5041079
theorem B7555265 : Blo 928581 7555265 := bstep (se 2 (by rfl) ⟨2833224, by rfl⟩ : syracuseStep 7555265 = 5666449) B5666449
theorem B1395035 : Blo 928581 1395035 := bstep (se 1 (by rfl) ⟨1046276, by rfl⟩ : syracuseStep 1395035 = 2092553) B2092553
theorem B6048229 : Blo 928581 6048229 := bstep (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) B1134043
theorem B1395263 : Blo 928581 1395263 := bstep (se 1 (by rfl) ⟨1046447, by rfl⟩ : syracuseStep 1395263 = 2092895) B2092895
theorem B1395383 : Blo 928581 1395383 := bstep (se 1 (by rfl) ⟨1046537, by rfl⟩ : syracuseStep 1395383 = 2093075) B2093075
theorem B1395611 : Blo 928581 1395611 := bstep (se 1 (by rfl) ⟨1046708, by rfl⟩ : syracuseStep 1395611 = 2093417) B2093417
theorem B1887131 : Blo 928581 1887131 := bstep (se 1 (by rfl) ⟨1415348, by rfl⟩ : syracuseStep 1887131 = 2830697) B2830697
theorem B1396007 : Blo 928581 1396007 := bstep (se 1 (by rfl) ⟨1047005, by rfl⟩ : syracuseStep 1396007 = 2094011) B2094011
theorem B1396091 : Blo 928581 1396091 := bstep (se 1 (by rfl) ⟨1047068, by rfl⟩ : syracuseStep 1396091 = 2094137) B2094137
theorem B1396217 : Blo 928581 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B1396319 : Blo 928581 1396319 := bstep (se 1 (by rfl) ⟨1047239, by rfl⟩ : syracuseStep 1396319 = 2094479) B2094479
theorem B7949987 : Blo 928581 7949987 := bstep (se 1 (by rfl) ⟨5962490, by rfl⟩ : syracuseStep 7949987 = 11924981) B11924981
theorem B15912611 : Blo 928581 15912611 := bstep (se 1 (by rfl) ⟨11934458, by rfl⟩ : syracuseStep 15912611 = 23868917) B23868917
theorem B1396535 : Blo 928581 1396535 := bstep (se 1 (by rfl) ⟨1047401, by rfl⟩ : syracuseStep 1396535 = 2094803) B2094803
theorem B1396841 : Blo 928581 1396841 := bstep (se 2 (by rfl) ⟨523815, by rfl⟩ : syracuseStep 1396841 = 1047631) B1047631
theorem B1397159 : Blo 928581 1397159 := bstep (se 1 (by rfl) ⟨1047869, by rfl⟩ : syracuseStep 1397159 = 2095739) B2095739
theorem B1397243 : Blo 928581 1397243 := bstep (se 1 (by rfl) ⟨1047932, by rfl⟩ : syracuseStep 1397243 = 2095865) B2095865
theorem B1397369 : Blo 928581 1397369 := bstep (se 2 (by rfl) ⟨524013, by rfl⟩ : syracuseStep 1397369 = 1048027) B1048027
theorem B3134105 : Blo 928581 3134105 := bstep (se 2 (by rfl) ⟨1175289, by rfl⟩ : syracuseStep 3134105 = 2350579) B2350579
theorem B1397423 : Blo 928581 1397423 := bstep (se 1 (by rfl) ⟨1048067, by rfl⟩ : syracuseStep 1397423 = 2096135) B2096135
theorem B1397471 : Blo 928581 1397471 := bstep (se 1 (by rfl) ⟨1048103, by rfl⟩ : syracuseStep 1397471 = 2096207) B2096207
theorem B4707233 : Blo 928581 4707233 := bstep (se 2 (by rfl) ⟨1765212, by rfl⟩ : syracuseStep 4707233 = 3530425) B3530425
theorem B2511847 : Blo 928581 2511847 := bstep (se 1 (by rfl) ⟨1883885, by rfl⟩ : syracuseStep 2511847 = 3767771) B3767771
theorem B1397735 : Blo 928581 1397735 := bstep (se 1 (by rfl) ⟨1048301, by rfl⟩ : syracuseStep 1397735 = 2096603) B2096603
theorem B1397993 : Blo 928581 1397993 := bstep (se 2 (by rfl) ⟨524247, by rfl⟩ : syracuseStep 1397993 = 1048495) B1048495
theorem B1398047 : Blo 928581 1398047 := bstep (se 1 (by rfl) ⟨1048535, by rfl⟩ : syracuseStep 1398047 = 2097071) B2097071
theorem B7558505 : Blo 928581 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B1398215 : Blo 928581 1398215 := bstep (se 1 (by rfl) ⟨1048661, by rfl⟩ : syracuseStep 1398215 = 2097323) B2097323
theorem B1889887 : Blo 928581 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B1988393 : Blo 928581 1988393 := bstep (se 2 (by rfl) ⟨745647, by rfl⟩ : syracuseStep 1988393 = 1491295) B1491295
theorem B1398569 : Blo 928581 1398569 := bstep (se 2 (by rfl) ⟨524463, by rfl⟩ : syracuseStep 1398569 = 1048927) B1048927
theorem B1398575 : Blo 928581 1398575 := bstep (se 1 (by rfl) ⟨1048931, by rfl⟩ : syracuseStep 1398575 = 2097863) B2097863
theorem B5298007 : Blo 928581 5298007 := bstep (se 1 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 5298007 = 7947011) B7947011
theorem B2545537 : Blo 928581 2545537 := bstep (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) B1909153
theorem B3135617 : Blo 928581 3135617 := bstep (se 2 (by rfl) ⟨1175856, by rfl⟩ : syracuseStep 3135617 = 2351713) B2351713
theorem B1988975 : Blo 928581 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B3135995 : Blo 928581 3135995 := bstep (se 1 (by rfl) ⟨2351996, by rfl⟩ : syracuseStep 3135995 = 4703993) B4703993
theorem B152656427 : Blo 928581 152656427 := bstep (se 1 (by rfl) ⟨114492320, by rfl⟩ : syracuseStep 152656427 = 228984641) B228984641
theorem B10050155 : Blo 928581 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B8706935 : Blo 928581 8706935 := bstep (se 1 (by rfl) ⟨6530201, by rfl⟩ : syracuseStep 8706935 = 13060403) B13060403
theorem B3136427 : Blo 928581 3136427 := bstep (se 1 (by rfl) ⟨2352320, by rfl⟩ : syracuseStep 3136427 = 4704641) B4704641
theorem B13622201 : Blo 928581 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B2645131 : Blo 928581 2645131 := bstep (se 1 (by rfl) ⟨1983848, by rfl⟩ : syracuseStep 2645131 = 3967697) B3967697
theorem B4480267 : Blo 928581 4480267 := bstep (se 1 (by rfl) ⟨3360200, by rfl⟩ : syracuseStep 4480267 = 6720401) B6720401
theorem B4709663 : Blo 928581 4709663 := bstep (se 1 (by rfl) ⟨3532247, by rfl⟩ : syracuseStep 4709663 = 7064495) B7064495
theorem B1989983 : Blo 928581 1989983 := bstep (se 1 (by rfl) ⟨1492487, by rfl⟩ : syracuseStep 1989983 = 2984975) B2984975
theorem B3136967 : Blo 928581 3136967 := bstep (se 1 (by rfl) ⟨2352725, by rfl⟩ : syracuseStep 3136967 = 4705451) B4705451
theorem B3137291 : Blo 928581 3137291 := bstep (se 1 (by rfl) ⟨2352968, by rfl⟩ : syracuseStep 3137291 = 4705937) B4705937
theorem B2350903 : Blo 928581 2350903 := bstep (se 1 (by rfl) ⟨1763177, by rfl⟩ : syracuseStep 2350903 = 3526355) B3526355
theorem B3137561 : Blo 928581 3137561 := bstep (se 2 (by rfl) ⟨1176585, by rfl⟩ : syracuseStep 3137561 = 2353171) B2353171
theorem B8708147 : Blo 928581 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B2351369 : Blo 928581 2351369 := bstep (se 2 (by rfl) ⟨881763, by rfl⟩ : syracuseStep 2351369 = 1763527) B1763527
theorem B2515631 : Blo 928581 2515631 := bstep (se 1 (by rfl) ⟨1886723, by rfl⟩ : syracuseStep 2515631 = 3773447) B3773447
theorem B2089655 : Blo 928581 2089655 := bstep (se 1 (by rfl) ⟨1567241, by rfl⟩ : syracuseStep 2089655 = 3134483) B3134483
theorem B2646863 : Blo 928581 2646863 := bstep (se 1 (by rfl) ⟨1985147, by rfl⟩ : syracuseStep 2646863 = 3970295) B3970295
theorem B1991503 : Blo 928581 1991503 := bstep (se 1 (by rfl) ⟨1493627, by rfl⟩ : syracuseStep 1991503 = 2987255) B2987255
theorem B6710111 : Blo 928581 6710111 := bstep (se 1 (by rfl) ⟨5032583, by rfl⟩ : syracuseStep 6710111 = 10065167) B10065167
theorem B2089871 : Blo 928581 2089871 := bstep (se 1 (by rfl) ⟨1567403, by rfl⟩ : syracuseStep 2089871 = 3134807) B3134807
theorem B2352361 : Blo 928581 2352361 := bstep (se 2 (by rfl) ⟨882135, by rfl⟩ : syracuseStep 2352361 = 1764271) B1764271
theorem B25158899 : Blo 928581 25158899 := bstep (se 1 (by rfl) ⟨18869174, by rfl⟩ : syracuseStep 25158899 = 37738349) B37738349
theorem B3138803 : Blo 928581 3138803 := bstep (se 1 (by rfl) ⟨2354102, by rfl⟩ : syracuseStep 3138803 = 4708205) B4708205
theorem B3138911 : Blo 928581 3138911 := bstep (se 1 (by rfl) ⟨2354183, by rfl⟩ : syracuseStep 3138911 = 4708367) B4708367
theorem B2352523 : Blo 928581 2352523 := bstep (se 1 (by rfl) ⟨1764392, by rfl⟩ : syracuseStep 2352523 = 3528785) B3528785
theorem B943687 : Blo 928581 943687 := bstep (se 1 (by rfl) ⟨707765, by rfl⟩ : syracuseStep 943687 = 1415531) B1415531
theorem B2090591 : Blo 928581 2090591 := bstep (se 1 (by rfl) ⟨1567943, by rfl⟩ : syracuseStep 2090591 = 3135887) B3135887
theorem B4712093 : Blo 928581 4712093 := bstep (se 3 (by rfl) ⟨883517, by rfl⟩ : syracuseStep 4712093 = 1767035) B1767035
theorem B2352827 : Blo 928581 2352827 := bstep (se 1 (by rfl) ⟨1764620, by rfl⟩ : syracuseStep 2352827 = 3529241) B3529241
theorem B2090807 : Blo 928581 2090807 := bstep (se 1 (by rfl) ⟨1568105, by rfl⟩ : syracuseStep 2090807 = 3136211) B3136211
theorem B2385721 : Blo 928581 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B4417361 : Blo 928581 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B5302199 : Blo 928581 5302199 := bstep (se 1 (by rfl) ⟨3976649, by rfl⟩ : syracuseStep 5302199 = 7953299) B7953299
theorem B2091113 : Blo 928581 2091113 := bstep (se 2 (by rfl) ⟨784167, by rfl⟩ : syracuseStep 2091113 = 1568335) B1568335
theorem B15100019 : Blo 928581 15100019 := bstep (se 1 (by rfl) ⟨11325014, by rfl⟩ : syracuseStep 15100019 = 22650029) B22650029
theorem B1566985 : Blo 928581 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B2976029 : Blo 928581 2976029 := bstep (se 3 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 2976029 = 1116011) B1116011
theorem B944551 : Blo 928581 944551 := bstep (se 1 (by rfl) ⟨708413, by rfl⟩ : syracuseStep 944551 = 1416827) B1416827
theorem B22932013 : Blo 928581 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B2648639 : Blo 928581 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B2091599 : Blo 928581 2091599 := bstep (se 1 (by rfl) ⟨1568699, by rfl⟩ : syracuseStep 2091599 = 3137399) B3137399
theorem B5302907 : Blo 928581 5302907 := bstep (se 1 (by rfl) ⟨3977180, by rfl⟩ : syracuseStep 5302907 = 7954361) B7954361
theorem B10611323 : Blo 928581 10611323 := bstep (se 1 (by rfl) ⟨7958492, by rfl⟩ : syracuseStep 10611323 = 15916985) B15916985
theorem B16116413 : Blo 928581 16116413 := bstep (se 3 (by rfl) ⟨3021827, by rfl⟩ : syracuseStep 16116413 = 6043655) B6043655
theorem B2091743 : Blo 928581 2091743 := bstep (se 1 (by rfl) ⟨1568807, by rfl⟩ : syracuseStep 2091743 = 3137615) B3137615
theorem B5958467 : Blo 928581 5958467 := bstep (se 1 (by rfl) ⟨4468850, by rfl⟩ : syracuseStep 5958467 = 8937701) B8937701
theorem B3140477 : Blo 928581 3140477 := bstep (se 3 (by rfl) ⟨588839, by rfl⟩ : syracuseStep 3140477 = 1177679) B1177679
theorem B4713389 : Blo 928581 4713389 := bstep (se 3 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 4713389 = 1767521) B1767521
theorem B2091995 : Blo 928581 2091995 := bstep (se 1 (by rfl) ⟨1568996, by rfl⟩ : syracuseStep 2091995 = 3137993) B3137993
theorem B3140747 : Blo 928581 3140747 := bstep (se 1 (by rfl) ⟨2355560, by rfl⟩ : syracuseStep 3140747 = 4711121) B4711121
theorem B2092175 : Blo 928581 2092175 := bstep (se 1 (by rfl) ⟨1569131, by rfl⟩ : syracuseStep 2092175 = 3138263) B3138263
theorem B2649277 : Blo 928581 2649277 := bstep (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) B993479
theorem B2092265 : Blo 928581 2092265 := bstep (se 2 (by rfl) ⟨784599, by rfl⟩ : syracuseStep 2092265 = 1569199) B1569199
theorem B2092319 : Blo 928581 2092319 := bstep (se 1 (by rfl) ⟨1569239, by rfl⟩ : syracuseStep 2092319 = 3138479) B3138479
theorem B40267043 : Blo 928581 40267043 := bstep (se 1 (by rfl) ⟨30200282, by rfl⟩ : syracuseStep 40267043 = 60400565) B60400565
theorem B2354771 : Blo 928581 2354771 := bstep (se 1 (by rfl) ⟨1766078, by rfl⟩ : syracuseStep 2354771 = 3532157) B3532157
theorem B1568443 : Blo 928581 1568443 := bstep (se 1 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 1568443 = 2352665) B2352665
theorem B2092841 : Blo 928581 2092841 := bstep (se 2 (by rfl) ⟨784815, by rfl⟩ : syracuseStep 2092841 = 1569631) B1569631
theorem B5107585 : Blo 928581 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B67858373 : Blo 928581 67858373 := bstep (se 4 (by rfl) ⟨6361722, by rfl⟩ : syracuseStep 67858373 = 12723445) B12723445
theorem B1765327 : Blo 928581 1765327 := bstep (se 1 (by rfl) ⟨1323995, by rfl⟩ : syracuseStep 1765327 = 2647991) B2647991
theorem B2650121 : Blo 928581 2650121 := bstep (se 2 (by rfl) ⟨993795, by rfl⟩ : syracuseStep 2650121 = 1987591) B1987591
theorem B1044859 : Blo 928581 1044859 := bstep (se 1 (by rfl) ⟨783644, by rfl⟩ : syracuseStep 1044859 = 1567289) B1567289
theorem B9204187 : Blo 928581 9204187 := bstep (se 1 (by rfl) ⟨6903140, by rfl⟩ : syracuseStep 9204187 = 13806281) B13806281
theorem B1176059 : Blo 928581 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B4715009 : Blo 928581 4715009 := bstep (se 2 (by rfl) ⟨1768128, by rfl⟩ : syracuseStep 4715009 = 3536257) B3536257
theorem B8942233 : Blo 928581 8942233 := bstep (se 2 (by rfl) ⟨3353337, by rfl⟩ : syracuseStep 8942233 = 6706675) B6706675
theorem B1766063 : Blo 928581 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B1569503 : Blo 928581 1569503 := bstep (se 1 (by rfl) ⟨1177127, by rfl⟩ : syracuseStep 1569503 = 2354255) B2354255
theorem B3142367 : Blo 928581 3142367 := bstep (se 1 (by rfl) ⟨2356775, by rfl⟩ : syracuseStep 3142367 = 4713551) B4713551
theorem B1045327 : Blo 928581 1045327 := bstep (se 1 (by rfl) ⟨783995, by rfl⟩ : syracuseStep 1045327 = 1567991) B1567991
theorem B2093903 : Blo 928581 2093903 := bstep (se 1 (by rfl) ⟨1570427, by rfl⟩ : syracuseStep 2093903 = 3140855) B3140855
theorem B16118635 : Blo 928581 16118635 := bstep (se 1 (by rfl) ⟨12088976, by rfl⟩ : syracuseStep 16118635 = 24177953) B24177953
theorem B1766299 : Blo 928581 1766299 := bstep (se 1 (by rfl) ⟨1324724, by rfl⟩ : syracuseStep 1766299 = 2649449) B2649449
theorem B2356199 : Blo 928581 2356199 := bstep (se 1 (by rfl) ⟨1767149, by rfl⟩ : syracuseStep 2356199 = 3534299) B3534299
theorem B4715495 : Blo 928581 4715495 := bstep (se 1 (by rfl) ⟨3536621, by rfl⟩ : syracuseStep 4715495 = 7073243) B7073243
theorem B2094119 : Blo 928581 2094119 := bstep (se 1 (by rfl) ⟨1570589, by rfl⟩ : syracuseStep 2094119 = 3141179) B3141179
theorem B1569935 : Blo 928581 1569935 := bstep (se 1 (by rfl) ⟨1177451, by rfl⟩ : syracuseStep 1569935 = 2354903) B2354903
theorem B3142799 : Blo 928581 3142799 := bstep (se 1 (by rfl) ⟨2357099, by rfl⟩ : syracuseStep 3142799 = 4714199) B4714199
theorem B1045723 : Blo 928581 1045723 := bstep (se 1 (by rfl) ⟨784292, by rfl⟩ : syracuseStep 1045723 = 1568585) B1568585
theorem B2094299 : Blo 928581 2094299 := bstep (se 1 (by rfl) ⟨1570724, by rfl⟩ : syracuseStep 2094299 = 3141449) B3141449
theorem B8942849 : Blo 928581 8942849 := bstep (se 2 (by rfl) ⟨3353568, by rfl⟩ : syracuseStep 8942849 = 6707137) B6707137
theorem B4715819 : Blo 928581 4715819 := bstep (se 1 (by rfl) ⟨3536864, by rfl⟩ : syracuseStep 4715819 = 7073729) B7073729
theorem B1570171 : Blo 928581 1570171 := bstep (se 1 (by rfl) ⟨1177628, by rfl⟩ : syracuseStep 1570171 = 2355257) B2355257
theorem B2094497 : Blo 928581 2094497 := bstep (se 2 (by rfl) ⟨785436, by rfl⟩ : syracuseStep 2094497 = 1570873) B1570873
theorem B1177031 : Blo 928581 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B1046011 : Blo 928581 1046011 := bstep (se 1 (by rfl) ⟨784508, by rfl⟩ : syracuseStep 1046011 = 1569017) B1569017
theorem B1177183 : Blo 928581 1177183 := bstep (se 1 (by rfl) ⟨882887, by rfl⟩ : syracuseStep 1177183 = 1765775) B1765775
theorem B2356897 : Blo 928581 2356897 := bstep (se 2 (by rfl) ⟨883836, by rfl⟩ : syracuseStep 2356897 = 1767673) B1767673
theorem B1046191 : Blo 928581 1046191 := bstep (se 1 (by rfl) ⟨784643, by rfl⟩ : syracuseStep 1046191 = 1569287) B1569287
theorem B2357039 : Blo 928581 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B1046479 : Blo 928581 1046479 := bstep (se 1 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 1046479 = 1569719) B1569719
theorem B2095055 : Blo 928581 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B4716791 : Blo 928581 4716791 := bstep (se 1 (by rfl) ⟨3537593, by rfl⟩ : syracuseStep 4716791 = 7075187) B7075187
theorem B3143933 : Blo 928581 3143933 := bstep (se 3 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 3143933 = 1178975) B1178975
theorem B2095433 : Blo 928581 2095433 := bstep (se 2 (by rfl) ⟨785787, by rfl⟩ : syracuseStep 2095433 = 1571575) B1571575
theorem B1046875 : Blo 928581 1046875 := bstep (se 1 (by rfl) ⟨785156, by rfl⟩ : syracuseStep 1046875 = 1570313) B1570313
theorem B2095451 : Blo 928581 2095451 := bstep (se 1 (by rfl) ⟨1571588, by rfl⟩ : syracuseStep 2095451 = 3143177) B3143177
theorem B2357687 : Blo 928581 2357687 := bstep (se 1 (by rfl) ⟨1768265, by rfl⟩ : syracuseStep 2357687 = 3536531) B3536531
theorem B1046983 : Blo 928581 1046983 := bstep (se 1 (by rfl) ⟨785237, by rfl⟩ : syracuseStep 1046983 = 1570475) B1570475
theorem B7174651 : Blo 928581 7174651 := bstep (se 1 (by rfl) ⟨5380988, by rfl⟩ : syracuseStep 7174651 = 10761977) B10761977
theorem B1768007 : Blo 928581 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B17857097 : Blo 928581 17857097 := bstep (se 2 (by rfl) ⟨6696411, by rfl⟩ : syracuseStep 17857097 = 13392823) B13392823
theorem B4029035 : Blo 928581 4029035 := bstep (se 1 (by rfl) ⟨3021776, by rfl⟩ : syracuseStep 4029035 = 6043553) B6043553
theorem B4717277 : Blo 928581 4717277 := bstep (se 3 (by rfl) ⟨884489, by rfl⟩ : syracuseStep 4717277 = 1768979) B1768979
theorem B1768159 : Blo 928581 1768159 := bstep (se 1 (by rfl) ⟨1326119, by rfl⟩ : syracuseStep 1768159 = 2652239) B2652239
theorem B1047343 : Blo 928581 1047343 := bstep (se 1 (by rfl) ⟨785507, by rfl⟩ : syracuseStep 1047343 = 1571015) B1571015
theorem B1571663 : Blo 928581 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B1047451 : Blo 928581 1047451 := bstep (se 1 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 1047451 = 1571177) B1571177
theorem B2096027 : Blo 928581 2096027 := bstep (se 1 (by rfl) ⟨1572020, by rfl⟩ : syracuseStep 2096027 = 3144041) B3144041
theorem B3144743 : Blo 928581 3144743 := bstep (se 1 (by rfl) ⟨2358557, by rfl⟩ : syracuseStep 3144743 = 4717115) B4717115
theorem B2096225 : Blo 928581 2096225 := bstep (se 2 (by rfl) ⟨786084, by rfl⟩ : syracuseStep 2096225 = 1572169) B1572169
theorem B7077131 : Blo 928581 7077131 := bstep (se 1 (by rfl) ⟨5307848, by rfl⟩ : syracuseStep 7077131 = 10615697) B10615697
theorem B1047847 : Blo 928581 1047847 := bstep (se 1 (by rfl) ⟨785885, by rfl⟩ : syracuseStep 1047847 = 1571771) B1571771
theorem B2096423 : Blo 928581 2096423 := bstep (se 1 (by rfl) ⟨1572317, by rfl⟩ : syracuseStep 2096423 = 3144635) B3144635
theorem B1047919 : Blo 928581 1047919 := bstep (se 1 (by rfl) ⟨785939, by rfl⟩ : syracuseStep 1047919 = 1571879) B1571879
theorem B3145175 : Blo 928581 3145175 := bstep (se 1 (by rfl) ⟨2358881, by rfl⟩ : syracuseStep 3145175 = 4717763) B4717763
theorem B2358791 : Blo 928581 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B2358841 : Blo 928581 2358841 := bstep (se 2 (by rfl) ⟨884565, by rfl⟩ : syracuseStep 2358841 = 1769131) B1769131
theorem B1048135 : Blo 928581 1048135 := bstep (se 1 (by rfl) ⟨786101, by rfl⟩ : syracuseStep 1048135 = 1572203) B1572203
theorem B1146475 : Blo 928581 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B2686625 : Blo 928581 2686625 := bstep (se 2 (by rfl) ⟨1007484, by rfl⟩ : syracuseStep 2686625 = 2014969) B2014969
theorem B2096801 : Blo 928581 2096801 := bstep (se 2 (by rfl) ⟨786300, by rfl⟩ : syracuseStep 2096801 = 1572601) B1572601
theorem B1572655 : Blo 928581 1572655 := bstep (se 1 (by rfl) ⟨1179491, by rfl⟩ : syracuseStep 1572655 = 2358983) B2358983
theorem B2359145 : Blo 928581 2359145 := bstep (se 2 (by rfl) ⟨884679, by rfl⟩ : syracuseStep 2359145 = 1769359) B1769359
theorem B5373803 : Blo 928581 5373803 := bstep (se 1 (by rfl) ⟨4030352, by rfl⟩ : syracuseStep 5373803 = 8060705) B8060705
theorem B1179623 : Blo 928581 1179623 := bstep (se 1 (by rfl) ⟨884717, by rfl⟩ : syracuseStep 1179623 = 1769435) B1769435
theorem B2654495 : Blo 928581 2654495 := bstep (se 1 (by rfl) ⟨1990871, by rfl⟩ : syracuseStep 2654495 = 3981743) B3981743
theorem B1573175 : Blo 928581 1573175 := bstep (se 1 (by rfl) ⟨1179881, by rfl⟩ : syracuseStep 1573175 = 2359763) B2359763
theorem B8061403 : Blo 928581 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B2097899 : Blo 928581 2097899 := bstep (se 1 (by rfl) ⟨1573424, by rfl⟩ : syracuseStep 2097899 = 3146849) B3146849
theorem B12092303 : Blo 928581 12092303 := bstep (se 1 (by rfl) ⟨9069227, by rfl⟩ : syracuseStep 12092303 = 18138455) B18138455
theorem B1770407 : Blo 928581 1770407 := bstep (se 1 (by rfl) ⟨1327805, by rfl⟩ : syracuseStep 1770407 = 2655611) B2655611
theorem B10585079 : Blo 928581 10585079 := bstep (se 1 (by rfl) ⟨7938809, by rfl⟩ : syracuseStep 10585079 = 15877619) B15877619
theorem B2655337 : Blo 928581 2655337 := bstep (se 2 (by rfl) ⟨995751, by rfl⟩ : syracuseStep 2655337 = 1991503) B1991503
theorem B20382977 : Blo 928581 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B4785419 : Blo 928581 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B3180961 : Blo 928581 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B6032017 : Blo 928581 6032017 := bstep (se 2 (by rfl) ⟨2262006, by rfl⟩ : syracuseStep 6032017 = 4524013) B4524013
theorem B76516433 : Blo 928581 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B8064305 : Blo 928581 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B30576017 : Blo 928581 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B5968255 : Blo 928581 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B5804623 : Blo 928581 5804623 := bstep (se 1 (by rfl) ⟨4353467, by rfl⟩ : syracuseStep 5804623 = 8706935) B8706935
theorem B3347027 : Blo 928581 3347027 := bstep (se 1 (by rfl) ⟨2510270, by rfl⟩ : syracuseStep 3347027 = 5020541) B5020541
theorem B9081467 : Blo 928581 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B11899709 : Blo 928581 11899709 := bstep (se 3 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 11899709 = 4462391) B4462391
theorem B13440107 : Blo 928581 13440107 := bstep (se 1 (by rfl) ⟨10080080, by rfl⟩ : syracuseStep 13440107 = 20160161) B20160161
theorem B3347675 : Blo 928581 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B5805431 : Blo 928581 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B3349129 : Blo 928581 3349129 := bstep (se 2 (by rfl) ⟨1255923, by rfl⟩ : syracuseStep 3349129 = 2511847) B2511847
theorem B10066679 : Blo 928581 10066679 := bstep (se 1 (by rfl) ⟨7550009, by rfl⟩ : syracuseStep 10066679 = 15100019) B15100019
theorem B2235521 : Blo 928581 2235521 := bstep (se 2 (by rfl) ⟨838320, by rfl⟩ : syracuseStep 2235521 = 1676641) B1676641
theorem B3972311 : Blo 928581 3972311 := bstep (se 1 (by rfl) ⟨2979233, by rfl⟩ : syracuseStep 3972311 = 5958467) B5958467
theorem B171908405 : Blo 928581 171908405 := bstep (se 5 (by rfl) ⟨8058206, by rfl⟩ : syracuseStep 171908405 = 16116413) B16116413
theorem B26844695 : Blo 928581 26844695 := bstep (se 1 (by rfl) ⟨20133521, by rfl⟩ : syracuseStep 26844695 = 40267043) B40267043
theorem B3350443 : Blo 928581 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B5973587 : Blo 928581 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B5973689 : Blo 928581 5973689 := bstep (se 2 (by rfl) ⟨2240133, by rfl⟩ : syracuseStep 5973689 = 4480267) B4480267
theorem B11904731 : Blo 928581 11904731 := bstep (se 1 (by rfl) ⟨8928548, by rfl⟩ : syracuseStep 11904731 = 17857097) B17857097
theorem B993223 : Blo 928581 993223 := bstep (se 1 (by rfl) ⟨744917, by rfl⟩ : syracuseStep 993223 = 1489835) B1489835
theorem B14330141 : Blo 928581 14330141 := bstep (se 3 (by rfl) ⟨2686901, by rfl⟩ : syracuseStep 14330141 = 5373803) B5373803
theorem B928603 : Blo 928581 928603 := bstep (se 1 (by rfl) ⟨696452, by rfl⟩ : syracuseStep 928603 = 1392905) B1392905
theorem B928671 : Blo 928581 928671 := bstep (se 1 (by rfl) ⟨696503, by rfl⟩ : syracuseStep 928671 = 1393007) B1393007
theorem B928815 : Blo 928581 928815 := bstep (se 1 (by rfl) ⟨696611, by rfl⟩ : syracuseStep 928815 = 1393223) B1393223
theorem B928839 : Blo 928581 928839 := bstep (se 1 (by rfl) ⟨696629, by rfl⟩ : syracuseStep 928839 = 1393259) B1393259
theorem B1256519 : Blo 928581 1256519 := bstep (se 1 (by rfl) ⟨942389, by rfl⟩ : syracuseStep 1256519 = 1884779) B1884779
theorem B928991 : Blo 928581 928991 := bstep (se 1 (by rfl) ⟨696743, by rfl⟩ : syracuseStep 928991 = 1393487) B1393487
theorem B13413761 : Blo 928581 13413761 := bstep (se 2 (by rfl) ⟨5030160, by rfl⟩ : syracuseStep 13413761 = 10060321) B10060321
theorem B929255 : Blo 928581 929255 := bstep (se 1 (by rfl) ⟨696941, by rfl⟩ : syracuseStep 929255 = 1393883) B1393883
theorem B929371 : Blo 928581 929371 := bstep (se 1 (by rfl) ⟨697028, by rfl⟩ : syracuseStep 929371 = 1394057) B1394057
theorem B929607 : Blo 928581 929607 := bstep (se 1 (by rfl) ⟨697205, by rfl⟩ : syracuseStep 929607 = 1394411) B1394411
theorem B929759 : Blo 928581 929759 := bstep (se 1 (by rfl) ⟨697319, by rfl⟩ : syracuseStep 929759 = 1394639) B1394639
theorem B3026911 : Blo 928581 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B2240479 : Blo 928581 2240479 := bstep (se 1 (by rfl) ⟨1680359, by rfl⟩ : syracuseStep 2240479 = 3360719) B3360719
theorem B930023 : Blo 928581 930023 := bstep (se 1 (by rfl) ⟨697517, by rfl⟩ : syracuseStep 930023 = 1395035) B1395035
theorem B12103937 : Blo 928581 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B10727747 : Blo 928581 10727747 := bstep (se 1 (by rfl) ⟨8045810, by rfl⟩ : syracuseStep 10727747 = 16091621) B16091621
theorem B11907395 : Blo 928581 11907395 := bstep (se 1 (by rfl) ⟨8930546, by rfl⟩ : syracuseStep 11907395 = 17861093) B17861093
theorem B930175 : Blo 928581 930175 := bstep (se 1 (by rfl) ⟨697631, by rfl⟩ : syracuseStep 930175 = 1395263) B1395263
theorem B8499599 : Blo 928581 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B930255 : Blo 928581 930255 := bstep (se 1 (by rfl) ⟨697691, by rfl⟩ : syracuseStep 930255 = 1395383) B1395383
theorem B3977743 : Blo 928581 3977743 := bstep (se 1 (by rfl) ⟨2983307, by rfl⟩ : syracuseStep 3977743 = 5966615) B5966615
theorem B930407 : Blo 928581 930407 := bstep (se 1 (by rfl) ⟨697805, by rfl⟩ : syracuseStep 930407 = 1395611) B1395611
theorem B1258087 : Blo 928581 1258087 := bstep (se 1 (by rfl) ⟨943565, by rfl⟩ : syracuseStep 1258087 = 1887131) B1887131
theorem B1258249 : Blo 928581 1258249 := bstep (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) B943687
theorem B930671 : Blo 928581 930671 := bstep (se 1 (by rfl) ⟨698003, by rfl⟩ : syracuseStep 930671 = 1396007) B1396007
theorem B930727 : Blo 928581 930727 := bstep (se 1 (by rfl) ⟨698045, by rfl⟩ : syracuseStep 930727 = 1396091) B1396091
theorem B930811 : Blo 928581 930811 := bstep (se 1 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 930811 = 1396217) B1396217
theorem B930879 : Blo 928581 930879 := bstep (se 1 (by rfl) ⟨698159, by rfl⟩ : syracuseStep 930879 = 1396319) B1396319
theorem B1488079 : Blo 928581 1488079 := bstep (se 1 (by rfl) ⟨1116059, by rfl⟩ : syracuseStep 1488079 = 2232119) B2232119
theorem B931023 : Blo 928581 931023 := bstep (se 1 (by rfl) ⟨698267, by rfl⟩ : syracuseStep 931023 = 1396535) B1396535
theorem B931227 : Blo 928581 931227 := bstep (se 1 (by rfl) ⟨698420, by rfl⟩ : syracuseStep 931227 = 1396841) B1396841
theorem B931439 : Blo 928581 931439 := bstep (se 1 (by rfl) ⟨698579, by rfl⟩ : syracuseStep 931439 = 1397159) B1397159
theorem B931495 : Blo 928581 931495 := bstep (se 1 (by rfl) ⟨698621, by rfl⟩ : syracuseStep 931495 = 1397243) B1397243
theorem B931579 : Blo 928581 931579 := bstep (se 1 (by rfl) ⟨698684, by rfl⟩ : syracuseStep 931579 = 1397369) B1397369
theorem B931615 : Blo 928581 931615 := bstep (se 1 (by rfl) ⟨698711, by rfl⟩ : syracuseStep 931615 = 1397423) B1397423
theorem B931647 : Blo 928581 931647 := bstep (se 1 (by rfl) ⟨698735, by rfl⟩ : syracuseStep 931647 = 1397471) B1397471
theorem B3979145 : Blo 928581 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1259401 : Blo 928581 1259401 := bstep (se 2 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 1259401 = 944551) B944551
theorem B931823 : Blo 928581 931823 := bstep (se 1 (by rfl) ⟨698867, by rfl⟩ : syracuseStep 931823 = 1397735) B1397735
theorem B931995 : Blo 928581 931995 := bstep (se 1 (by rfl) ⟨698996, by rfl⟩ : syracuseStep 931995 = 1397993) B1397993
theorem B932031 : Blo 928581 932031 := bstep (se 1 (by rfl) ⟨699023, by rfl⟩ : syracuseStep 932031 = 1398047) B1398047
theorem B5290217 : Blo 928581 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B932143 : Blo 928581 932143 := bstep (se 1 (by rfl) ⟨699107, by rfl⟩ : syracuseStep 932143 = 1398215) B1398215
theorem B932379 : Blo 928581 932379 := bstep (se 1 (by rfl) ⟨699284, by rfl⟩ : syracuseStep 932379 = 1398569) B1398569
theorem B932383 : Blo 928581 932383 := bstep (se 1 (by rfl) ⟨699287, by rfl⟩ : syracuseStep 932383 = 1398575) B1398575
theorem B11909855 : Blo 928581 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B1325983 : Blo 928581 1325983 := bstep (se 1 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 1325983 = 1988975) B1988975
theorem B6700103 : Blo 928581 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B1326655 : Blo 928581 1326655 := bstep (se 1 (by rfl) ⟨994991, by rfl⟩ : syracuseStep 1326655 = 1989983) B1989983
theorem B27181403 : Blo 928581 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B1393103 : Blo 928581 1393103 := bstep (se 1 (by rfl) ⟨1044827, by rfl⟩ : syracuseStep 1393103 = 2089655) B2089655
theorem B1393145 : Blo 928581 1393145 := bstep (se 2 (by rfl) ⟨522429, by rfl⟩ : syracuseStep 1393145 = 1044859) B1044859
theorem B4473407 : Blo 928581 4473407 := bstep (se 1 (by rfl) ⟨3355055, by rfl⟩ : syracuseStep 4473407 = 6710111) B6710111
theorem B1393247 : Blo 928581 1393247 := bstep (se 1 (by rfl) ⟨1044935, by rfl⟩ : syracuseStep 1393247 = 2089871) B2089871
theorem B12272249 : Blo 928581 12272249 := bstep (se 2 (by rfl) ⟨4602093, by rfl⟩ : syracuseStep 12272249 = 9204187) B9204187
theorem B1393727 : Blo 928581 1393727 := bstep (se 1 (by rfl) ⟨1045295, by rfl⟩ : syracuseStep 1393727 = 2090591) B2090591
theorem B1393769 : Blo 928581 1393769 := bstep (se 2 (by rfl) ⟨522663, by rfl⟩ : syracuseStep 1393769 = 1045327) B1045327
theorem B1393871 : Blo 928581 1393871 := bstep (se 1 (by rfl) ⟨1045403, by rfl⟩ : syracuseStep 1393871 = 2090807) B2090807
theorem B5293451 : Blo 928581 5293451 := bstep (se 1 (by rfl) ⟨3970088, by rfl⟩ : syracuseStep 5293451 = 7940177) B7940177
theorem B1394075 : Blo 928581 1394075 := bstep (se 1 (by rfl) ⟨1045556, by rfl⟩ : syracuseStep 1394075 = 2091113) B2091113
theorem B7063037 : Blo 928581 7063037 := bstep (se 3 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 7063037 = 2648639) B2648639
theorem B1984019 : Blo 928581 1984019 := bstep (se 1 (by rfl) ⟨1488014, by rfl⟩ : syracuseStep 1984019 = 2976029) B2976029
theorem B1394297 : Blo 928581 1394297 := bstep (se 2 (by rfl) ⟨522861, by rfl⟩ : syracuseStep 1394297 = 1045723) B1045723
theorem B1394399 : Blo 928581 1394399 := bstep (se 1 (by rfl) ⟨1045799, by rfl⟩ : syracuseStep 1394399 = 2091599) B2091599
theorem B1394495 : Blo 928581 1394495 := bstep (se 1 (by rfl) ⟨1045871, by rfl⟩ : syracuseStep 1394495 = 2091743) B2091743
theorem B1394663 : Blo 928581 1394663 := bstep (se 1 (by rfl) ⟨1045997, by rfl⟩ : syracuseStep 1394663 = 2091995) B2091995
theorem B1394681 : Blo 928581 1394681 := bstep (se 2 (by rfl) ⟨523005, by rfl⟩ : syracuseStep 1394681 = 1046011) B1046011
theorem B1394783 : Blo 928581 1394783 := bstep (se 1 (by rfl) ⟨1046087, by rfl⟩ : syracuseStep 1394783 = 2092175) B2092175
theorem B1394843 : Blo 928581 1394843 := bstep (se 1 (by rfl) ⟨1046132, by rfl⟩ : syracuseStep 1394843 = 2092265) B2092265
theorem B1394879 : Blo 928581 1394879 := bstep (se 1 (by rfl) ⟨1046159, by rfl⟩ : syracuseStep 1394879 = 2092319) B2092319
theorem B1394921 : Blo 928581 1394921 := bstep (se 2 (by rfl) ⟨523095, by rfl⟩ : syracuseStep 1394921 = 1046191) B1046191
theorem B7064009 : Blo 928581 7064009 := bstep (se 2 (by rfl) ⟨2649003, by rfl⟩ : syracuseStep 7064009 = 5298007) B5298007
theorem B3394049 : Blo 928581 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B1395227 : Blo 928581 1395227 := bstep (se 1 (by rfl) ⟨1046420, by rfl⟩ : syracuseStep 1395227 = 2092841) B2092841
theorem B1395305 : Blo 928581 1395305 := bstep (se 2 (by rfl) ⟨523239, by rfl⟩ : syracuseStep 1395305 = 1046479) B1046479
theorem B45238915 : Blo 928581 45238915 := bstep (se 1 (by rfl) ⟨33929186, by rfl⟩ : syracuseStep 45238915 = 67858373) B67858373
theorem B1887031 : Blo 928581 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B5295091 : Blo 928581 5295091 := bstep (se 1 (by rfl) ⟨3971318, by rfl⟩ : syracuseStep 5295091 = 7942637) B7942637
theorem B1395833 : Blo 928581 1395833 := bstep (se 2 (by rfl) ⟨523437, by rfl⟩ : syracuseStep 1395833 = 1046875) B1046875
theorem B1395935 : Blo 928581 1395935 := bstep (se 1 (by rfl) ⟨1046951, by rfl⟩ : syracuseStep 1395935 = 2093903) B2093903
theorem B1395977 : Blo 928581 1395977 := bstep (se 2 (by rfl) ⟨523491, by rfl⟩ : syracuseStep 1395977 = 1046983) B1046983
theorem B1396079 : Blo 928581 1396079 := bstep (se 1 (by rfl) ⟨1047059, by rfl⟩ : syracuseStep 1396079 = 2094119) B2094119
theorem B1396199 : Blo 928581 1396199 := bstep (se 1 (by rfl) ⟨1047149, by rfl⟩ : syracuseStep 1396199 = 2094299) B2094299
theorem B1396331 : Blo 928581 1396331 := bstep (se 1 (by rfl) ⟨1047248, by rfl⟩ : syracuseStep 1396331 = 2094497) B2094497
theorem B1396457 : Blo 928581 1396457 := bstep (se 2 (by rfl) ⟨523671, by rfl⟩ : syracuseStep 1396457 = 1047343) B1047343
theorem B1396601 : Blo 928581 1396601 := bstep (se 2 (by rfl) ⟨523725, by rfl⟩ : syracuseStep 1396601 = 1047451) B1047451
theorem B1396703 : Blo 928581 1396703 := bstep (se 1 (by rfl) ⟨1047527, by rfl⟩ : syracuseStep 1396703 = 2095055) B2095055
theorem B3526841 : Blo 928581 3526841 := bstep (se 2 (by rfl) ⟨1322565, by rfl⟩ : syracuseStep 3526841 = 2645131) B2645131
theorem B1396955 : Blo 928581 1396955 := bstep (se 1 (by rfl) ⟨1047716, by rfl⟩ : syracuseStep 1396955 = 2095433) B2095433
theorem B1396967 : Blo 928581 1396967 := bstep (se 1 (by rfl) ⟨1047725, by rfl⟩ : syracuseStep 1396967 = 2095451) B2095451
theorem B3527023 : Blo 928581 3527023 := bstep (se 1 (by rfl) ⟨2645267, by rfl⟩ : syracuseStep 3527023 = 5290535) B5290535
theorem B1397129 : Blo 928581 1397129 := bstep (se 2 (by rfl) ⟨523923, by rfl⟩ : syracuseStep 1397129 = 1047847) B1047847
theorem B5296549 : Blo 928581 5296549 := bstep (se 4 (by rfl) ⟨496551, by rfl⟩ : syracuseStep 5296549 = 993103) B993103
theorem B1397225 : Blo 928581 1397225 := bstep (se 2 (by rfl) ⟨523959, by rfl⟩ : syracuseStep 1397225 = 1047919) B1047919
theorem B1397351 : Blo 928581 1397351 := bstep (se 1 (by rfl) ⟨1048013, by rfl⟩ : syracuseStep 1397351 = 2096027) B2096027
theorem B2118305 : Blo 928581 2118305 := bstep (se 2 (by rfl) ⟨794364, by rfl⟩ : syracuseStep 2118305 = 1588729) B1588729
theorem B5296823 : Blo 928581 5296823 := bstep (se 1 (by rfl) ⟨3972617, by rfl⟩ : syracuseStep 5296823 = 7945235) B7945235
theorem B1397483 : Blo 928581 1397483 := bstep (se 1 (by rfl) ⟨1048112, by rfl⟩ : syracuseStep 1397483 = 2096225) B2096225
theorem B1397513 : Blo 928581 1397513 := bstep (se 2 (by rfl) ⟨524067, by rfl⟩ : syracuseStep 1397513 = 1048135) B1048135
theorem B1528633 : Blo 928581 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B1397615 : Blo 928581 1397615 := bstep (se 1 (by rfl) ⟨1048211, by rfl⟩ : syracuseStep 1397615 = 2096423) B2096423
theorem B1889335 : Blo 928581 1889335 := bstep (se 1 (by rfl) ⟨1417001, by rfl⟩ : syracuseStep 1889335 = 2834003) B2834003
theorem B3134537 : Blo 928581 3134537 := bstep (se 2 (by rfl) ⟨1175451, by rfl⟩ : syracuseStep 3134537 = 2350903) B2350903
theorem B1791083 : Blo 928581 1791083 := bstep (se 1 (by rfl) ⟨1343312, by rfl⟩ : syracuseStep 1791083 = 2686625) B2686625
theorem B1397867 : Blo 928581 1397867 := bstep (se 1 (by rfl) ⟨1048400, by rfl⟩ : syracuseStep 1397867 = 2096801) B2096801
theorem B1398107 : Blo 928581 1398107 := bstep (se 1 (by rfl) ⟨1048580, by rfl⟩ : syracuseStep 1398107 = 2097161) B2097161
theorem B1398383 : Blo 928581 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B325998229 : Blo 928581 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B1398455 : Blo 928581 1398455 := bstep (se 1 (by rfl) ⟨1048841, by rfl⟩ : syracuseStep 1398455 = 2097683) B2097683
theorem B1398491 : Blo 928581 1398491 := bstep (se 1 (by rfl) ⟨1048868, by rfl⟩ : syracuseStep 1398491 = 2097737) B2097737
theorem B1595099 : Blo 928581 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B294508331 : Blo 928581 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B1398665 : Blo 928581 1398665 := bstep (se 2 (by rfl) ⟨524499, by rfl⟩ : syracuseStep 1398665 = 1048999) B1048999
theorem B1398767 : Blo 928581 1398767 := bstep (se 1 (by rfl) ⟨1049075, by rfl⟩ : syracuseStep 1398767 = 2098151) B2098151
theorem B4479421 : Blo 928581 4479421 := bstep (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) B1679783
theorem B3136157 : Blo 928581 3136157 := bstep (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) B1176059
theorem B5036843 : Blo 928581 5036843 := bstep (se 1 (by rfl) ⟨3777632, by rfl⟩ : syracuseStep 5036843 = 7555265) B7555265
theorem B4021073 : Blo 928581 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B3136481 : Blo 928581 3136481 := bstep (se 2 (by rfl) ⟨1176180, by rfl⟩ : syracuseStep 3136481 = 2352361) B2352361
theorem B15293555 : Blo 928581 15293555 := bstep (se 1 (by rfl) ⟨11470166, by rfl⟩ : syracuseStep 15293555 = 22940333) B22940333
theorem B4709501 : Blo 928581 4709501 := bstep (se 3 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 4709501 = 1766063) B1766063
theorem B6708349 : Blo 928581 6708349 := bstep (se 3 (by rfl) ⟨1257815, by rfl⟩ : syracuseStep 6708349 = 2515631) B2515631
theorem B3136697 : Blo 928581 3136697 := bstep (se 2 (by rfl) ⟨1176261, by rfl⟩ : syracuseStep 3136697 = 2352523) B2352523
theorem B26860733 : Blo 928581 26860733 := bstep (se 3 (by rfl) ⟨5036387, by rfl⟩ : syracuseStep 26860733 = 10072775) B10072775
theorem B5168381 : Blo 928581 5168381 := bstep (se 3 (by rfl) ⟨969071, by rfl⟩ : syracuseStep 5168381 = 1938143) B1938143
theorem B2645257 : Blo 928581 2645257 := bstep (se 2 (by rfl) ⟨991971, by rfl⟩ : syracuseStep 2645257 = 1983943) B1983943
theorem B2645747 : Blo 928581 2645747 := bstep (se 1 (by rfl) ⟨1984310, by rfl⟩ : syracuseStep 2645747 = 3968621) B3968621
theorem B5299991 : Blo 928581 5299991 := bstep (se 1 (by rfl) ⟨3974993, by rfl⟩ : syracuseStep 5299991 = 7949987) B7949987
theorem B10608407 : Blo 928581 10608407 := bstep (se 1 (by rfl) ⟨7956305, by rfl⟩ : syracuseStep 10608407 = 15912611) B15912611
theorem B2089313 : Blo 928581 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B2089403 : Blo 928581 2089403 := bstep (se 1 (by rfl) ⟨1567052, by rfl⟩ : syracuseStep 2089403 = 3134105) B3134105
theorem B3138155 : Blo 928581 3138155 := bstep (se 1 (by rfl) ⟨2353616, by rfl⟩ : syracuseStep 3138155 = 4707233) B4707233
theorem B5039003 : Blo 928581 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B3138749 : Blo 928581 3138749 := bstep (se 3 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 3138749 = 1177031) B1177031
theorem B2090411 : Blo 928581 2090411 := bstep (se 1 (by rfl) ⟨1567808, by rfl⟩ : syracuseStep 2090411 = 3135617) B3135617
theorem B3532369 : Blo 928581 3532369 := bstep (se 2 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 3532369 = 2649277) B2649277
theorem B5301881 : Blo 928581 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B4253305 : Blo 928581 4253305 := bstep (se 2 (by rfl) ⟨1594989, by rfl⟩ : syracuseStep 4253305 = 3189979) B3189979
theorem B2090663 : Blo 928581 2090663 := bstep (se 1 (by rfl) ⟨1567997, by rfl⟩ : syracuseStep 2090663 = 3135995) B3135995
theorem B101770951 : Blo 928581 101770951 := bstep (se 1 (by rfl) ⟨76328213, by rfl⟩ : syracuseStep 101770951 = 152656427) B152656427
theorem B2090951 : Blo 928581 2090951 := bstep (se 1 (by rfl) ⟨1568213, by rfl⟩ : syracuseStep 2090951 = 3136427) B3136427
theorem B5302381 : Blo 928581 5302381 := bstep (se 3 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 5302381 = 1988393) B1988393
theorem B3139775 : Blo 928581 3139775 := bstep (se 1 (by rfl) ⟨2354831, by rfl⟩ : syracuseStep 3139775 = 4709663) B4709663
theorem B2091257 : Blo 928581 2091257 := bstep (se 2 (by rfl) ⟨784221, by rfl⟩ : syracuseStep 2091257 = 1568443) B1568443
theorem B73361699 : Blo 928581 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B2091311 : Blo 928581 2091311 := bstep (se 1 (by rfl) ⟨1568483, by rfl⟩ : syracuseStep 2091311 = 3136967) B3136967
theorem B6810113 : Blo 928581 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B2091527 : Blo 928581 2091527 := bstep (se 1 (by rfl) ⟨1568645, by rfl⟩ : syracuseStep 2091527 = 3137291) B3137291
theorem B2353769 : Blo 928581 2353769 := bstep (se 2 (by rfl) ⟨882663, by rfl⟩ : syracuseStep 2353769 = 1765327) B1765327
theorem B2976439 : Blo 928581 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B2091707 : Blo 928581 2091707 := bstep (se 1 (by rfl) ⟨1568780, by rfl⟩ : syracuseStep 2091707 = 3137561) B3137561
theorem B1567579 : Blo 928581 1567579 := bstep (se 1 (by rfl) ⟨1175684, by rfl⟩ : syracuseStep 1567579 = 2351369) B2351369
theorem B6974351 : Blo 928581 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B1764575 : Blo 928581 1764575 := bstep (se 1 (by rfl) ⟨1323431, by rfl⟩ : syracuseStep 1764575 = 2646863) B2646863
theorem B16772599 : Blo 928581 16772599 := bstep (se 1 (by rfl) ⟨12579449, by rfl⟩ : syracuseStep 16772599 = 25158899) B25158899
theorem B2092535 : Blo 928581 2092535 := bstep (se 1 (by rfl) ⟨1569401, by rfl⟩ : syracuseStep 2092535 = 3138803) B3138803
theorem B11922977 : Blo 928581 11922977 := bstep (se 2 (by rfl) ⟨4471116, by rfl⟩ : syracuseStep 11922977 = 8942233) B8942233
theorem B2092607 : Blo 928581 2092607 := bstep (se 1 (by rfl) ⟨1569455, by rfl⟩ : syracuseStep 2092607 = 3138911) B3138911
theorem B2977555 : Blo 928581 2977555 := bstep (se 1 (by rfl) ⟨2233166, by rfl⟩ : syracuseStep 2977555 = 4466333) B4466333
theorem B3141395 : Blo 928581 3141395 := bstep (se 1 (by rfl) ⟨2356046, by rfl⟩ : syracuseStep 3141395 = 4712093) B4712093
theorem B1568551 : Blo 928581 1568551 := bstep (se 1 (by rfl) ⟨1176413, by rfl⟩ : syracuseStep 1568551 = 2352827) B2352827
theorem B21491513 : Blo 928581 21491513 := bstep (se 2 (by rfl) ⟨8059317, by rfl⟩ : syracuseStep 21491513 = 16118635) B16118635
theorem B2355065 : Blo 928581 2355065 := bstep (se 2 (by rfl) ⟨883149, by rfl⟩ : syracuseStep 2355065 = 1766299) B1766299
theorem B2944907 : Blo 928581 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B3534799 : Blo 928581 3534799 := bstep (se 1 (by rfl) ⟨2651099, by rfl⟩ : syracuseStep 3534799 = 5302199) B5302199
theorem B4714685 : Blo 928581 4714685 := bstep (se 3 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 4714685 = 1768007) B1768007
theorem B6451411 : Blo 928581 6451411 := bstep (se 1 (by rfl) ⟨4838558, by rfl⟩ : syracuseStep 6451411 = 9677117) B9677117
theorem B10744093 : Blo 928581 10744093 := bstep (se 3 (by rfl) ⟨2014517, by rfl⟩ : syracuseStep 10744093 = 4029035) B4029035
theorem B3535271 : Blo 928581 3535271 := bstep (se 1 (by rfl) ⟨2651453, by rfl⟩ : syracuseStep 3535271 = 5302907) B5302907
theorem B7074215 : Blo 928581 7074215 := bstep (se 1 (by rfl) ⟨5305661, by rfl⟩ : syracuseStep 7074215 = 10611323) B10611323
theorem B2093561 : Blo 928581 2093561 := bstep (se 2 (by rfl) ⟨785085, by rfl⟩ : syracuseStep 2093561 = 1570171) B1570171
theorem B2978387 : Blo 928581 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B2093651 : Blo 928581 2093651 := bstep (se 1 (by rfl) ⟨1570238, by rfl⟩ : syracuseStep 2093651 = 3140477) B3140477
theorem B3142259 : Blo 928581 3142259 := bstep (se 1 (by rfl) ⟨2356694, by rfl⟩ : syracuseStep 3142259 = 4713389) B4713389
theorem B2093831 : Blo 928581 2093831 := bstep (se 1 (by rfl) ⟨1570373, by rfl⟩ : syracuseStep 2093831 = 3140747) B3140747
theorem B1569577 : Blo 928581 1569577 := bstep (se 2 (by rfl) ⟨588591, by rfl⟩ : syracuseStep 1569577 = 1177183) B1177183
theorem B2519849 : Blo 928581 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B3142529 : Blo 928581 3142529 := bstep (se 2 (by rfl) ⟨1178448, by rfl⟩ : syracuseStep 3142529 = 2356897) B2356897
theorem B1569847 : Blo 928581 1569847 := bstep (se 1 (by rfl) ⟨1177385, by rfl⟩ : syracuseStep 1569847 = 2354771) B2354771
theorem B1766747 : Blo 928581 1766747 := bstep (se 1 (by rfl) ⟨1325060, by rfl⟩ : syracuseStep 1766747 = 2650121) B2650121
theorem B2651579 : Blo 928581 2651579 := bstep (se 1 (by rfl) ⟨1988684, by rfl⟩ : syracuseStep 2651579 = 3977369) B3977369
theorem B30242315 : Blo 928581 30242315 := bstep (se 1 (by rfl) ⟨22681736, by rfl⟩ : syracuseStep 30242315 = 45363473) B45363473
theorem B3143339 : Blo 928581 3143339 := bstep (se 1 (by rfl) ⟨2357504, by rfl⟩ : syracuseStep 3143339 = 4715009) B4715009
theorem B1046335 : Blo 928581 1046335 := bstep (se 1 (by rfl) ⟨784751, by rfl⟩ : syracuseStep 1046335 = 1569503) B1569503
theorem B2094911 : Blo 928581 2094911 := bstep (se 1 (by rfl) ⟨1571183, by rfl⟩ : syracuseStep 2094911 = 3142367) B3142367
theorem B1570799 : Blo 928581 1570799 := bstep (se 1 (by rfl) ⟨1178099, by rfl⟩ : syracuseStep 1570799 = 2356199) B2356199
theorem B3143663 : Blo 928581 3143663 := bstep (se 1 (by rfl) ⟨2357747, by rfl⟩ : syracuseStep 3143663 = 4715495) B4715495
theorem B9566201 : Blo 928581 9566201 := bstep (se 2 (by rfl) ⟨3587325, by rfl⟩ : syracuseStep 9566201 = 7174651) B7174651
theorem B1046623 : Blo 928581 1046623 := bstep (se 1 (by rfl) ⟨784967, by rfl⟩ : syracuseStep 1046623 = 1569935) B1569935
theorem B2095199 : Blo 928581 2095199 := bstep (se 1 (by rfl) ⟨1571399, by rfl⟩ : syracuseStep 2095199 = 3142799) B3142799
theorem B5961899 : Blo 928581 5961899 := bstep (se 1 (by rfl) ⟨4471424, by rfl⟩ : syracuseStep 5961899 = 8942849) B8942849
theorem B3143879 : Blo 928581 3143879 := bstep (se 1 (by rfl) ⟨2357909, by rfl⟩ : syracuseStep 3143879 = 4715819) B4715819
theorem B2357545 : Blo 928581 2357545 := bstep (se 2 (by rfl) ⟨884079, by rfl⟩ : syracuseStep 2357545 = 1768159) B1768159
theorem B12712301 : Blo 928581 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B5962157 : Blo 928581 5962157 := bstep (se 3 (by rfl) ⟨1117904, by rfl⟩ : syracuseStep 5962157 = 2235809) B2235809
theorem B1571359 : Blo 928581 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B2980489 : Blo 928581 2980489 := bstep (se 2 (by rfl) ⟨1117683, by rfl⟩ : syracuseStep 2980489 = 2235367) B2235367
theorem B3144527 : Blo 928581 3144527 := bstep (se 1 (by rfl) ⟨2358395, by rfl⟩ : syracuseStep 3144527 = 4716791) B4716791
theorem B2095955 : Blo 928581 2095955 := bstep (se 1 (by rfl) ⟨1571966, by rfl⟩ : syracuseStep 2095955 = 3143933) B3143933
theorem B1571791 : Blo 928581 1571791 := bstep (se 1 (by rfl) ⟨1178843, by rfl⟩ : syracuseStep 1571791 = 2357687) B2357687
theorem B2555009 : Blo 928581 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B3144851 : Blo 928581 3144851 := bstep (se 1 (by rfl) ⟨2358638, by rfl⟩ : syracuseStep 3144851 = 4717277) B4717277
theorem B1047775 : Blo 928581 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B2096495 : Blo 928581 2096495 := bstep (se 1 (by rfl) ⟨1572371, by rfl⟩ : syracuseStep 2096495 = 3144743) B3144743
theorem B3145121 : Blo 928581 3145121 := bstep (se 2 (by rfl) ⟨1179420, by rfl⟩ : syracuseStep 3145121 = 2358841) B2358841
theorem B2653651 : Blo 928581 2653651 := bstep (se 1 (by rfl) ⟨1990238, by rfl⟩ : syracuseStep 2653651 = 3980477) B3980477
theorem B4718087 : Blo 928581 4718087 := bstep (se 1 (by rfl) ⟨3538565, by rfl⟩ : syracuseStep 4718087 = 7077131) B7077131
theorem B3767951 : Blo 928581 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2096783 : Blo 928581 2096783 := bstep (se 1 (by rfl) ⟨1572587, by rfl⟩ : syracuseStep 2096783 = 3145175) B3145175
theorem B1572527 : Blo 928581 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B2096873 : Blo 928581 2096873 := bstep (se 2 (by rfl) ⟨786327, by rfl⟩ : syracuseStep 2096873 = 1572655) B1572655
theorem B278822807 : Blo 928581 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B1572763 : Blo 928581 1572763 := bstep (se 1 (by rfl) ⟨1179572, by rfl⟩ : syracuseStep 1572763 = 2359145) B2359145
theorem B3145661 : Blo 928581 3145661 := bstep (se 3 (by rfl) ⟨589811, by rfl⟩ : syracuseStep 3145661 = 1179623) B1179623
theorem B1769663 : Blo 928581 1769663 := bstep (se 1 (by rfl) ⟨1327247, by rfl⟩ : syracuseStep 1769663 = 2654495) B2654495
theorem B1048783 : Blo 928581 1048783 := bstep (se 1 (by rfl) ⟨786587, by rfl⟩ : syracuseStep 1048783 = 1573175) B1573175
theorem B18120935 : Blo 928581 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B2982271 : Blo 928581 2982271 := bstep (se 1 (by rfl) ⟨2236703, by rfl⟩ : syracuseStep 2982271 = 4473407) B4473407
theorem B8061535 : Blo 928581 8061535 := bstep (se 1 (by rfl) ⟨6046151, by rfl⟩ : syracuseStep 8061535 = 12092303) B12092303
theorem B1180271 : Blo 928581 1180271 := bstep (se 1 (by rfl) ⟨885203, by rfl⟩ : syracuseStep 1180271 = 1770407) B1770407
theorem B10748537 : Blo 928581 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B3540449 : Blo 928581 3540449 := bstep (se 2 (by rfl) ⟨1327668, by rfl⟩ : syracuseStep 3540449 = 2655337) B2655337
theorem B5671073 : Blo 928581 5671073 := bstep (se 2 (by rfl) ⟨2126652, by rfl⟩ : syracuseStep 5671073 = 4253305) B4253305
theorem B5376203 : Blo 928581 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B135694601 : Blo 928581 135694601 := bstep (se 2 (by rfl) ⟨50885475, by rfl⟩ : syracuseStep 135694601 = 101770951) B101770951
theorem B20384011 : Blo 928581 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B2231351 : Blo 928581 2231351 := bstep (se 1 (by rfl) ⟨1673513, by rfl⟩ : syracuseStep 2231351 = 3347027) B3347027
theorem B1412203 : Blo 928581 1412203 := bstep (se 1 (by rfl) ⟨1059152, by rfl⟩ : syracuseStep 1412203 = 2118305) B2118305
theorem B7933139 : Blo 928581 7933139 := bstep (se 1 (by rfl) ⟨5949854, by rfl⟩ : syracuseStep 7933139 = 11899709) B11899709
theorem B2231783 : Blo 928581 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B3968585 : Blo 928581 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B3870287 : Blo 928581 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B10195703 : Blo 928581 10195703 := bstep (se 1 (by rfl) ⟨7646777, by rfl⟩ : syracuseStep 10195703 = 15293555) B15293555
theorem B17896463 : Blo 928581 17896463 := bstep (se 1 (by rfl) ⟨13422347, by rfl⟩ : syracuseStep 17896463 = 26844695) B26844695
theorem B3970073 : Blo 928581 3970073 := bstep (se 2 (by rfl) ⟨1488777, by rfl⟩ : syracuseStep 3970073 = 2977555) B2977555
theorem B4035881 : Blo 928581 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B7739497 : Blo 928581 7739497 := bstep (se 2 (by rfl) ⟨2902311, by rfl⟩ : syracuseStep 7739497 = 5804623) B5804623
theorem B1677449 : Blo 928581 1677449 := bstep (se 2 (by rfl) ⟨629043, by rfl⟩ : syracuseStep 1677449 = 1258087) B1258087
theorem B1677665 : Blo 928581 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B7936487 : Blo 928581 7936487 := bstep (se 1 (by rfl) ⟨5952365, by rfl⟩ : syracuseStep 7936487 = 11904731) B11904731
theorem B9050797 : Blo 928581 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B18160301 : Blo 928581 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B1679201 : Blo 928581 1679201 := bstep (se 2 (by rfl) ⟨629700, by rfl⟩ : syracuseStep 1679201 = 1259401) B1259401
theorem B14327675 : Blo 928581 14327675 := bstep (se 1 (by rfl) ⟨10745756, by rfl⟩ : syracuseStep 14327675 = 21491513) B21491513
theorem B8069291 : Blo 928581 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B3350717 : Blo 928581 3350717 := bstep (se 3 (by rfl) ⟨628259, by rfl⟩ : syracuseStep 3350717 = 1256519) B1256519
theorem B7151831 : Blo 928581 7151831 := bstep (se 1 (by rfl) ⟨5363873, by rfl⟩ : syracuseStep 7151831 = 10727747) B10727747
theorem B7938263 : Blo 928581 7938263 := bstep (se 1 (by rfl) ⟨5953697, by rfl⟩ : syracuseStep 7938263 = 11907395) B11907395
theorem B1679899 : Blo 928581 1679899 := bstep (se 1 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 1679899 = 2519849) B2519849
theorem B5972561 : Blo 928581 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B4465505 : Blo 928581 4465505 := bstep (se 2 (by rfl) ⟨1674564, by rfl⟩ : syracuseStep 4465505 = 3349129) B3349129
theorem B3973985 : Blo 928581 3973985 := bstep (se 2 (by rfl) ⟨1490244, by rfl⟩ : syracuseStep 3973985 = 2980489) B2980489
theorem B20161543 : Blo 928581 20161543 := bstep (se 1 (by rfl) ⟨15121157, by rfl⟩ : syracuseStep 20161543 = 30242315) B30242315
theorem B3974599 : Blo 928581 3974599 := bstep (se 1 (by rfl) ⟨2980949, by rfl⟩ : syracuseStep 3974599 = 5961899) B5961899
theorem B3974771 : Blo 928581 3974771 := bstep (se 1 (by rfl) ⟨2981078, by rfl⟩ : syracuseStep 3974771 = 5962157) B5962157
theorem B7939903 : Blo 928581 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B4466735 : Blo 928581 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B4467257 : Blo 928581 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B928735 : Blo 928581 928735 := bstep (se 1 (by rfl) ⟨696551, by rfl⟩ : syracuseStep 928735 = 1393103) B1393103
theorem B928763 : Blo 928581 928763 := bstep (se 1 (by rfl) ⟨696572, by rfl⟩ : syracuseStep 928763 = 1393145) B1393145
theorem B928831 : Blo 928581 928831 := bstep (se 1 (by rfl) ⟨696623, by rfl⟩ : syracuseStep 928831 = 1393247) B1393247
theorem B7056719 : Blo 928581 7056719 := bstep (se 1 (by rfl) ⟨5292539, by rfl⟩ : syracuseStep 7056719 = 10585079) B10585079
theorem B929151 : Blo 928581 929151 := bstep (se 1 (by rfl) ⟨696863, by rfl⟩ : syracuseStep 929151 = 1393727) B1393727
theorem B929179 : Blo 928581 929179 := bstep (se 1 (by rfl) ⟨696884, by rfl⟩ : syracuseStep 929179 = 1393769) B1393769
theorem B929247 : Blo 928581 929247 := bstep (se 1 (by rfl) ⟨696935, by rfl⟩ : syracuseStep 929247 = 1393871) B1393871
theorem B3190279 : Blo 928581 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B929383 : Blo 928581 929383 := bstep (se 1 (by rfl) ⟨697037, by rfl⟩ : syracuseStep 929383 = 1394075) B1394075
theorem B929531 : Blo 928581 929531 := bstep (se 1 (by rfl) ⟨697148, by rfl⟩ : syracuseStep 929531 = 1394297) B1394297
theorem B929599 : Blo 928581 929599 := bstep (se 1 (by rfl) ⟨697199, by rfl⟩ : syracuseStep 929599 = 1394399) B1394399
theorem B929663 : Blo 928581 929663 := bstep (se 1 (by rfl) ⟨697247, by rfl⟩ : syracuseStep 929663 = 1394495) B1394495
theorem B929775 : Blo 928581 929775 := bstep (se 1 (by rfl) ⟨697331, by rfl⟩ : syracuseStep 929775 = 1394663) B1394663
theorem B929787 : Blo 928581 929787 := bstep (se 1 (by rfl) ⟨697340, by rfl⟩ : syracuseStep 929787 = 1394681) B1394681
theorem B929855 : Blo 928581 929855 := bstep (se 1 (by rfl) ⟨697391, by rfl⟩ : syracuseStep 929855 = 1394783) B1394783
theorem B929895 : Blo 928581 929895 := bstep (se 1 (by rfl) ⟨697421, by rfl⟩ : syracuseStep 929895 = 1394843) B1394843
theorem B929919 : Blo 928581 929919 := bstep (se 1 (by rfl) ⟨697439, by rfl⟩ : syracuseStep 929919 = 1394879) B1394879
theorem B929947 : Blo 928581 929947 := bstep (se 1 (by rfl) ⟨697460, by rfl⟩ : syracuseStep 929947 = 1394921) B1394921
theorem B930151 : Blo 928581 930151 := bstep (se 1 (by rfl) ⟨697613, by rfl⟩ : syracuseStep 930151 = 1395227) B1395227
theorem B930203 : Blo 928581 930203 := bstep (se 1 (by rfl) ⟨697652, by rfl⟩ : syracuseStep 930203 = 1395305) B1395305
theorem B930555 : Blo 928581 930555 := bstep (se 1 (by rfl) ⟨697916, by rfl⟩ : syracuseStep 930555 = 1395833) B1395833
theorem B930623 : Blo 928581 930623 := bstep (se 1 (by rfl) ⟨697967, by rfl⟩ : syracuseStep 930623 = 1395935) B1395935
theorem B930651 : Blo 928581 930651 := bstep (se 1 (by rfl) ⟨697988, by rfl⟩ : syracuseStep 930651 = 1395977) B1395977
theorem B930719 : Blo 928581 930719 := bstep (se 1 (by rfl) ⟨698039, by rfl⟩ : syracuseStep 930719 = 1396079) B1396079
theorem B930799 : Blo 928581 930799 := bstep (se 1 (by rfl) ⟨698099, by rfl⟩ : syracuseStep 930799 = 1396199) B1396199
theorem B930887 : Blo 928581 930887 := bstep (se 1 (by rfl) ⟨698165, by rfl⟩ : syracuseStep 930887 = 1396331) B1396331
theorem B930971 : Blo 928581 930971 := bstep (se 1 (by rfl) ⟨698228, by rfl⟩ : syracuseStep 930971 = 1396457) B1396457
theorem B931067 : Blo 928581 931067 := bstep (se 1 (by rfl) ⟨698300, by rfl⟩ : syracuseStep 931067 = 1396601) B1396601
theorem B1324297 : Blo 928581 1324297 := bstep (se 2 (by rfl) ⟨496611, by rfl⟩ : syracuseStep 1324297 = 993223) B993223
theorem B931135 : Blo 928581 931135 := bstep (se 1 (by rfl) ⟨698351, by rfl⟩ : syracuseStep 931135 = 1396703) B1396703
theorem B931303 : Blo 928581 931303 := bstep (se 1 (by rfl) ⟨698477, by rfl⟩ : syracuseStep 931303 = 1396955) B1396955
theorem B931311 : Blo 928581 931311 := bstep (se 1 (by rfl) ⟨698483, by rfl⟩ : syracuseStep 931311 = 1396967) B1396967
theorem B931419 : Blo 928581 931419 := bstep (se 1 (by rfl) ⟨698564, by rfl⟩ : syracuseStep 931419 = 1397129) B1397129
theorem B931483 : Blo 928581 931483 := bstep (se 1 (by rfl) ⟨698612, by rfl⟩ : syracuseStep 931483 = 1397225) B1397225
theorem B931567 : Blo 928581 931567 := bstep (se 1 (by rfl) ⟨698675, by rfl⟩ : syracuseStep 931567 = 1397351) B1397351
theorem B931655 : Blo 928581 931655 := bstep (se 1 (by rfl) ⟨698741, by rfl⟩ : syracuseStep 931655 = 1397483) B1397483
theorem B931675 : Blo 928581 931675 := bstep (se 1 (by rfl) ⟨698756, by rfl⟩ : syracuseStep 931675 = 1397513) B1397513
theorem B4241281 : Blo 928581 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B931743 : Blo 928581 931743 := bstep (se 1 (by rfl) ⟨698807, by rfl⟩ : syracuseStep 931743 = 1397615) B1397615
theorem B931911 : Blo 928581 931911 := bstep (se 1 (by rfl) ⟨698933, by rfl⟩ : syracuseStep 931911 = 1397867) B1397867
theorem B8960071 : Blo 928581 8960071 := bstep (se 1 (by rfl) ⟨6720053, by rfl⟩ : syracuseStep 8960071 = 13440107) B13440107
theorem B8042689 : Blo 928581 8042689 := bstep (se 2 (by rfl) ⟨3016008, by rfl⟩ : syracuseStep 8042689 = 6032017) B6032017
theorem B932071 : Blo 928581 932071 := bstep (se 1 (by rfl) ⟨699053, by rfl⟩ : syracuseStep 932071 = 1398107) B1398107
theorem B932255 : Blo 928581 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B932303 : Blo 928581 932303 := bstep (se 1 (by rfl) ⟨699227, by rfl⟩ : syracuseStep 932303 = 1398455) B1398455
theorem B932327 : Blo 928581 932327 := bstep (se 1 (by rfl) ⟨699245, by rfl⟩ : syracuseStep 932327 = 1398491) B1398491
theorem B932443 : Blo 928581 932443 := bstep (se 1 (by rfl) ⟨699332, by rfl⟩ : syracuseStep 932443 = 1398665) B1398665
theorem B7060121 : Blo 928581 7060121 := bstep (se 2 (by rfl) ⟨2647545, by rfl⟩ : syracuseStep 7060121 = 5295091) B5295091
theorem B932511 : Blo 928581 932511 := bstep (se 1 (by rfl) ⟨699383, by rfl⟩ : syracuseStep 932511 = 1398767) B1398767
theorem B5290717 : Blo 928581 5290717 := bstep (se 3 (by rfl) ⟨992009, by rfl⟩ : syracuseStep 5290717 = 1984019) B1984019
theorem B3357895 : Blo 928581 3357895 := bstep (se 1 (by rfl) ⟨2518421, by rfl⟩ : syracuseStep 3357895 = 5036843) B5036843
theorem B22363465 : Blo 928581 22363465 := bstep (se 2 (by rfl) ⟨8386299, by rfl⟩ : syracuseStep 22363465 = 16772599) B16772599
theorem B1490347 : Blo 928581 1490347 := bstep (se 1 (by rfl) ⟨1117760, by rfl⟩ : syracuseStep 1490347 = 2235521) B2235521
theorem B17907155 : Blo 928581 17907155 := bstep (se 1 (by rfl) ⟨13430366, by rfl⟩ : syracuseStep 17907155 = 26860733) B26860733
theorem B114605603 : Blo 928581 114605603 := bstep (se 1 (by rfl) ⟨85954202, by rfl⟩ : syracuseStep 114605603 = 171908405) B171908405
theorem B1392875 : Blo 928581 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B8601881 : Blo 928581 8601881 := bstep (se 2 (by rfl) ⟨3225705, by rfl⟩ : syracuseStep 8601881 = 6451411) B6451411
theorem B1392935 : Blo 928581 1392935 := bstep (se 1 (by rfl) ⟨1044701, by rfl⟩ : syracuseStep 1392935 = 2089403) B2089403
theorem B4702697 : Blo 928581 4702697 := bstep (se 2 (by rfl) ⟨1763511, by rfl⟩ : syracuseStep 4702697 = 3527023) B3527023
theorem B7062065 : Blo 928581 7062065 := bstep (se 2 (by rfl) ⟨2648274, by rfl⟩ : syracuseStep 7062065 = 5296549) B5296549
theorem B3359335 : Blo 928581 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B1393607 : Blo 928581 1393607 := bstep (se 1 (by rfl) ⟨1045205, by rfl⟩ : syracuseStep 1393607 = 2090411) B2090411
theorem B3982391 : Blo 928581 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B1393775 : Blo 928581 1393775 := bstep (se 1 (by rfl) ⟨1045331, by rfl⟩ : syracuseStep 1393775 = 2090663) B2090663
theorem B3982459 : Blo 928581 3982459 := bstep (se 1 (by rfl) ⟨2986844, by rfl⟩ : syracuseStep 3982459 = 5973689) B5973689
theorem B1393967 : Blo 928581 1393967 := bstep (se 1 (by rfl) ⟨1045475, by rfl⟩ : syracuseStep 1393967 = 2090951) B2090951
theorem B1394171 : Blo 928581 1394171 := bstep (se 1 (by rfl) ⟨1045628, by rfl⟩ : syracuseStep 1394171 = 2091257) B2091257
theorem B9553427 : Blo 928581 9553427 := bstep (se 1 (by rfl) ⟨7165070, by rfl⟩ : syracuseStep 9553427 = 14330141) B14330141
theorem B48907799 : Blo 928581 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B1394207 : Blo 928581 1394207 := bstep (se 1 (by rfl) ⟨1045655, by rfl⟩ : syracuseStep 1394207 = 2091311) B2091311
theorem B1984105 : Blo 928581 1984105 := bstep (se 2 (by rfl) ⟨744039, by rfl⟩ : syracuseStep 1984105 = 1488079) B1488079
theorem B1394351 : Blo 928581 1394351 := bstep (se 1 (by rfl) ⟨1045763, by rfl⟩ : syracuseStep 1394351 = 2091527) B2091527
theorem B1394471 : Blo 928581 1394471 := bstep (se 1 (by rfl) ⟨1045853, by rfl⟩ : syracuseStep 1394471 = 2091707) B2091707
theorem B1395023 : Blo 928581 1395023 := bstep (se 1 (by rfl) ⟨1046267, by rfl⟩ : syracuseStep 1395023 = 2092535) B2092535
theorem B7948651 : Blo 928581 7948651 := bstep (se 1 (by rfl) ⟨5961488, by rfl⟩ : syracuseStep 7948651 = 11922977) B11922977
theorem B1395071 : Blo 928581 1395071 := bstep (se 1 (by rfl) ⟨1046303, by rfl⟩ : syracuseStep 1395071 = 2092607) B2092607
theorem B1395113 : Blo 928581 1395113 := bstep (se 2 (by rfl) ⟨523167, by rfl⟩ : syracuseStep 1395113 = 1046335) B1046335
theorem B1395497 : Blo 928581 1395497 := bstep (se 2 (by rfl) ⟨523311, by rfl⟩ : syracuseStep 1395497 = 1046623) B1046623
theorem B1395707 : Blo 928581 1395707 := bstep (se 1 (by rfl) ⟨1046780, by rfl⟩ : syracuseStep 1395707 = 2093561) B2093561
theorem B1985591 : Blo 928581 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B1395767 : Blo 928581 1395767 := bstep (se 1 (by rfl) ⟨1046825, by rfl⟩ : syracuseStep 1395767 = 2093651) B2093651
theorem B1395887 : Blo 928581 1395887 := bstep (se 1 (by rfl) ⟨1046915, by rfl⟩ : syracuseStep 1395887 = 2093831) B2093831
theorem B13782349 : Blo 928581 13782349 := bstep (se 3 (by rfl) ⟨2584190, by rfl⟩ : syracuseStep 13782349 = 5168381) B5168381
theorem B1396607 : Blo 928581 1396607 := bstep (se 1 (by rfl) ⟨1047455, by rfl⟩ : syracuseStep 1396607 = 2094911) B2094911
theorem B6377467 : Blo 928581 6377467 := bstep (se 1 (by rfl) ⟨4783100, by rfl⟩ : syracuseStep 6377467 = 9566201) B9566201
theorem B1396799 : Blo 928581 1396799 := bstep (se 1 (by rfl) ⟨1047599, by rfl⟩ : syracuseStep 1396799 = 2095199) B2095199
theorem B3526811 : Blo 928581 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B8474867 : Blo 928581 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B1397033 : Blo 928581 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B3527009 : Blo 928581 3527009 := bstep (se 2 (by rfl) ⟨1322628, by rfl⟩ : syracuseStep 3527009 = 2645257) B2645257
theorem B1397303 : Blo 928581 1397303 := bstep (se 1 (by rfl) ⟨1047977, by rfl⟩ : syracuseStep 1397303 = 2095955) B2095955
theorem B1397663 : Blo 928581 1397663 := bstep (se 1 (by rfl) ⟨1048247, by rfl⟩ : syracuseStep 1397663 = 2096495) B2096495
theorem B2511967 : Blo 928581 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B1397855 : Blo 928581 1397855 := bstep (se 1 (by rfl) ⟨1048391, by rfl⟩ : syracuseStep 1397855 = 2096783) B2096783
theorem B1397915 : Blo 928581 1397915 := bstep (se 1 (by rfl) ⟨1048436, by rfl⟩ : syracuseStep 1397915 = 2096873) B2096873
theorem B11949221 : Blo 928581 11949221 := bstep (se 4 (by rfl) ⟨1120239, by rfl⟩ : syracuseStep 11949221 = 2240479) B2240479
theorem B185881871 : Blo 928581 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B8181499 : Blo 928581 8181499 := bstep (se 1 (by rfl) ⟨6136124, by rfl⟩ : syracuseStep 8181499 = 12272249) B12272249
theorem B1398599 : Blo 928581 1398599 := bstep (se 1 (by rfl) ⟨1048949, by rfl⟩ : syracuseStep 1398599 = 2097899) B2097899
theorem B13588651 : Blo 928581 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B3528967 : Blo 928581 3528967 := bstep (se 1 (by rfl) ⟨2646725, by rfl⟩ : syracuseStep 3528967 = 5293451) B5293451
theorem B4708691 : Blo 928581 4708691 := bstep (se 1 (by rfl) ⟨3531518, by rfl⟩ : syracuseStep 4708691 = 7063037) B7063037
theorem B57301829 : Blo 928581 57301829 := bstep (se 4 (by rfl) ⟨5372046, by rfl⟩ : syracuseStep 57301829 = 10744093) B10744093
theorem B4709339 : Blo 928581 4709339 := bstep (se 1 (by rfl) ⟨3532004, by rfl⟩ : syracuseStep 4709339 = 7064009) B7064009
theorem B51010955 : Blo 928581 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B4709825 : Blo 928581 4709825 := bstep (se 2 (by rfl) ⟨1766184, by rfl⟩ : syracuseStep 4709825 = 3532369) B3532369
theorem B2351227 : Blo 928581 2351227 := bstep (se 1 (by rfl) ⟨1763420, by rfl⟩ : syracuseStep 2351227 = 3526841) B3526841
theorem B7069841 : Blo 928581 7069841 := bstep (se 2 (by rfl) ⟨2651190, by rfl⟩ : syracuseStep 7069841 = 5302381) B5302381
theorem B4776221 : Blo 928581 4776221 := bstep (se 3 (by rfl) ⟨895541, by rfl⟩ : syracuseStep 4776221 = 1791083) B1791083
theorem B6054311 : Blo 928581 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B3531215 : Blo 928581 3531215 := bstep (se 1 (by rfl) ⟨2648411, by rfl⟩ : syracuseStep 3531215 = 5296823) B5296823
theorem B2089691 : Blo 928581 2089691 := bstep (se 1 (by rfl) ⟨1567268, by rfl⟩ : syracuseStep 2089691 = 3134537) B3134537
theorem B60318553 : Blo 928581 60318553 := bstep (se 2 (by rfl) ⟨22619457, by rfl⟩ : syracuseStep 60318553 = 45238915) B45238915
theorem B2516041 : Blo 928581 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B2090105 : Blo 928581 2090105 := bstep (se 2 (by rfl) ⟨783789, by rfl⟩ : syracuseStep 2090105 = 1567579) B1567579
theorem B196338887 : Blo 928581 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B8152709 : Blo 928581 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B2090771 : Blo 928581 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B6711119 : Blo 928581 6711119 := bstep (se 1 (by rfl) ⟨5033339, by rfl⟩ : syracuseStep 6711119 = 10066679) B10066679
theorem B2680715 : Blo 928581 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B4253597 : Blo 928581 4253597 := bstep (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) B1595099
theorem B2090987 : Blo 928581 2090987 := bstep (se 1 (by rfl) ⟨1568240, by rfl⟩ : syracuseStep 2090987 = 3136481) B3136481
theorem B3139667 : Blo 928581 3139667 := bstep (se 1 (by rfl) ⟨2354750, by rfl⟩ : syracuseStep 3139667 = 4709501) B4709501
theorem B2091131 : Blo 928581 2091131 := bstep (se 1 (by rfl) ⟨1568348, by rfl⟩ : syracuseStep 2091131 = 3136697) B3136697
theorem B2648207 : Blo 928581 2648207 := bstep (se 1 (by rfl) ⟨1986155, by rfl⟩ : syracuseStep 2648207 = 3972311) B3972311
theorem B2091401 : Blo 928581 2091401 := bstep (se 2 (by rfl) ⟨784275, by rfl⟩ : syracuseStep 2091401 = 1568551) B1568551
theorem B1763831 : Blo 928581 1763831 := bstep (se 1 (by rfl) ⟨1322873, by rfl⟩ : syracuseStep 1763831 = 2645747) B2645747
theorem B3533327 : Blo 928581 3533327 := bstep (se 1 (by rfl) ⟨2649995, by rfl⟩ : syracuseStep 3533327 = 5299991) B5299991
theorem B7072271 : Blo 928581 7072271 := bstep (se 1 (by rfl) ⟨5304203, by rfl⟩ : syracuseStep 7072271 = 10608407) B10608407
theorem B4713065 : Blo 928581 4713065 := bstep (se 2 (by rfl) ⟨1767399, by rfl⟩ : syracuseStep 4713065 = 3534799) B3534799
theorem B2092103 : Blo 928581 2092103 := bstep (se 1 (by rfl) ⟨1569077, by rfl⟩ : syracuseStep 2092103 = 3138155) B3138155
theorem B7957673 : Blo 928581 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B5303657 : Blo 928581 5303657 := bstep (se 2 (by rfl) ⟨1988871, by rfl⟩ : syracuseStep 5303657 = 3977743) B3977743
theorem B2092499 : Blo 928581 2092499 := bstep (se 1 (by rfl) ⟨1569374, by rfl⟩ : syracuseStep 2092499 = 3138749) B3138749
theorem B2092769 : Blo 928581 2092769 := bstep (se 2 (by rfl) ⟨784788, by rfl⟩ : syracuseStep 2092769 = 1569577) B1569577
theorem B3534587 : Blo 928581 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B2093129 : Blo 928581 2093129 := bstep (se 2 (by rfl) ⟨784923, by rfl⟩ : syracuseStep 2093129 = 1569847) B1569847
theorem B2519113 : Blo 928581 2519113 := bstep (se 2 (by rfl) ⟨944667, by rfl⟩ : syracuseStep 2519113 = 1889335) B1889335
theorem B2093183 : Blo 928581 2093183 := bstep (se 1 (by rfl) ⟨1569887, by rfl⟩ : syracuseStep 2093183 = 3139775) B3139775
theorem B1569179 : Blo 928581 1569179 := bstep (se 1 (by rfl) ⟨1176884, by rfl⟩ : syracuseStep 1569179 = 2353769) B2353769
theorem B4649567 : Blo 928581 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B1176383 : Blo 928581 1176383 := bstep (se 1 (by rfl) ⟨882287, by rfl⟩ : syracuseStep 1176383 = 1764575) B1764575
theorem B434664305 : Blo 928581 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B8942507 : Blo 928581 8942507 := bstep (se 1 (by rfl) ⟨6706880, by rfl⟩ : syracuseStep 8942507 = 13413761) B13413761
theorem B2094263 : Blo 928581 2094263 := bstep (se 1 (by rfl) ⟨1570697, by rfl⟩ : syracuseStep 2094263 = 3141395) B3141395
theorem B1570043 : Blo 928581 1570043 := bstep (se 1 (by rfl) ⟨1177532, by rfl⟩ : syracuseStep 1570043 = 2355065) B2355065
theorem B1963271 : Blo 928581 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B3143123 : Blo 928581 3143123 := bstep (se 1 (by rfl) ⟨2357342, by rfl⟩ : syracuseStep 3143123 = 4714685) B4714685
theorem B5666399 : Blo 928581 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B4716143 : Blo 928581 4716143 := bstep (se 1 (by rfl) ⟨3537107, by rfl⟩ : syracuseStep 4716143 = 7074215) B7074215
theorem B2356847 : Blo 928581 2356847 := bstep (se 1 (by rfl) ⟨1767635, by rfl⟩ : syracuseStep 2356847 = 3535271) B3535271
theorem B3143393 : Blo 928581 3143393 := bstep (se 2 (by rfl) ⟨1178772, by rfl⟩ : syracuseStep 3143393 = 2357545) B2357545
theorem B2094839 : Blo 928581 2094839 := bstep (se 1 (by rfl) ⟨1571129, by rfl⟩ : syracuseStep 2094839 = 3142259) B3142259
theorem B2095019 : Blo 928581 2095019 := bstep (se 1 (by rfl) ⟨1571264, by rfl⟩ : syracuseStep 2095019 = 3142529) B3142529
theorem B2095145 : Blo 928581 2095145 := bstep (se 2 (by rfl) ⟨785679, by rfl⟩ : syracuseStep 2095145 = 1571359) B1571359
theorem B1177831 : Blo 928581 1177831 := bstep (se 1 (by rfl) ⟨883373, by rfl⟩ : syracuseStep 1177831 = 1766747) B1766747
theorem B1767719 : Blo 928581 1767719 := bstep (se 1 (by rfl) ⟨1325789, by rfl⟩ : syracuseStep 1767719 = 2651579) B2651579
theorem B2095559 : Blo 928581 2095559 := bstep (se 1 (by rfl) ⟨1571669, by rfl⟩ : syracuseStep 2095559 = 3143339) B3143339
theorem B1767977 : Blo 928581 1767977 := bstep (se 2 (by rfl) ⟨662991, by rfl⟩ : syracuseStep 1767977 = 1325983) B1325983
theorem B2652763 : Blo 928581 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B2095721 : Blo 928581 2095721 := bstep (se 2 (by rfl) ⟨785895, by rfl⟩ : syracuseStep 2095721 = 1571791) B1571791
theorem B1047199 : Blo 928581 1047199 := bstep (se 1 (by rfl) ⟨785399, by rfl⟩ : syracuseStep 1047199 = 1570799) B1570799
theorem B2095775 : Blo 928581 2095775 := bstep (se 1 (by rfl) ⟨1571831, by rfl⟩ : syracuseStep 2095775 = 3143663) B3143663
theorem B2095919 : Blo 928581 2095919 := bstep (se 1 (by rfl) ⟨1571939, by rfl⟩ : syracuseStep 2095919 = 3143879) B3143879
theorem B8944465 : Blo 928581 8944465 := bstep (se 2 (by rfl) ⟨3354174, by rfl⟩ : syracuseStep 8944465 = 6708349) B6708349
theorem B2096351 : Blo 928581 2096351 := bstep (se 1 (by rfl) ⟨1572263, by rfl⟩ : syracuseStep 2096351 = 3144527) B3144527
theorem B3538201 : Blo 928581 3538201 := bstep (se 2 (by rfl) ⟨1326825, by rfl⟩ : syracuseStep 3538201 = 2653651) B2653651
theorem B1768873 : Blo 928581 1768873 := bstep (se 2 (by rfl) ⟨663327, by rfl⟩ : syracuseStep 1768873 = 1326655) B1326655
theorem B1703339 : Blo 928581 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B2096567 : Blo 928581 2096567 := bstep (se 1 (by rfl) ⟨1572425, by rfl⟩ : syracuseStep 2096567 = 3144851) B3144851
theorem B2096747 : Blo 928581 2096747 := bstep (se 1 (by rfl) ⟨1572560, by rfl⟩ : syracuseStep 2096747 = 3145121) B3145121
theorem B3145391 : Blo 928581 3145391 := bstep (se 1 (by rfl) ⟨2359043, by rfl⟩ : syracuseStep 3145391 = 4718087) B4718087
theorem B1048351 : Blo 928581 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B2097017 : Blo 928581 2097017 := bstep (se 2 (by rfl) ⟨786381, by rfl⟩ : syracuseStep 2097017 = 1572763) B1572763
theorem B2097107 : Blo 928581 2097107 := bstep (se 1 (by rfl) ⟨1572830, by rfl⟩ : syracuseStep 2097107 = 3145661) B3145661
theorem B1179775 : Blo 928581 1179775 := bstep (se 1 (by rfl) ⟨884831, by rfl⟩ : syracuseStep 1179775 = 1769663) B1769663
theorem B2654927 : Blo 928581 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B22938349 : Blo 928581 22938349 := bstep (se 3 (by rfl) ⟨4300940, by rfl⟩ : syracuseStep 22938349 = 8601881) B8601881
theorem B10748713 : Blo 928581 10748713 := bstep (se 2 (by rfl) ⟨4030767, by rfl⟩ : syracuseStep 10748713 = 8061535) B8061535
theorem B2360299 : Blo 928581 2360299 := bstep (se 1 (by rfl) ⟨1770224, by rfl⟩ : syracuseStep 2360299 = 3540449) B3540449
theorem B32605199 : Blo 928581 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B5309945 : Blo 928581 5309945 := bstep (se 2 (by rfl) ⟨1991229, by rfl⟩ : syracuseStep 5309945 = 3982459) B3982459
theorem B3147389 : Blo 928581 3147389 := bstep (se 3 (by rfl) ⟨590135, by rfl⟩ : syracuseStep 3147389 = 1180271) B1180271
theorem B10586537 : Blo 928581 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B11930975 : Blo 928581 11930975 := bstep (se 1 (by rfl) ⟨8948231, by rfl⟩ : syracuseStep 11930975 = 17896463) B17896463
theorem B7966147 : Blo 928581 7966147 := bstep (se 1 (by rfl) ⟨5974610, by rfl⟩ : syracuseStep 7966147 = 11949221) B11949221
theorem B2690587 : Blo 928581 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B48270917 : Blo 928581 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B1118299 : Blo 928581 1118299 := bstep (se 1 (by rfl) ⟨838724, by rfl⟩ : syracuseStep 1118299 = 1677449) B1677449
theorem B1118443 : Blo 928581 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B7148573 : Blo 928581 7148573 := bstep (se 3 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 7148573 = 2680715) B2680715
theorem B1119467 : Blo 928581 1119467 := bstep (se 1 (by rfl) ⟨839600, by rfl⟩ : syracuseStep 1119467 = 1679201) B1679201
theorem B5379527 : Blo 928581 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B2233811 : Blo 928581 2233811 := bstep (se 1 (by rfl) ⟨1675358, by rfl⟩ : syracuseStep 2233811 = 3350717) B3350717
theorem B3184147 : Blo 928581 3184147 := bstep (se 1 (by rfl) ⟨2388110, by rfl⟩ : syracuseStep 3184147 = 4776221) B4776221
theorem B3349289 : Blo 928581 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B10723585 : Blo 928581 10723585 := bstep (se 2 (by rfl) ⟨4021344, by rfl⟩ : syracuseStep 10723585 = 8042689) B8042689
theorem B289776203 : Blo 928581 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B7054289 : Blo 928581 7054289 := bstep (se 2 (by rfl) ⟨2645358, by rfl⟩ : syracuseStep 7054289 = 5290717) B5290717
theorem B3777599 : Blo 928581 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B11938103 : Blo 928581 11938103 := bstep (se 1 (by rfl) ⟨8953577, by rfl⟩ : syracuseStep 11938103 = 17907155) B17907155
theorem B928583 : Blo 928581 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B928623 : Blo 928581 928623 := bstep (se 1 (by rfl) ⟨696467, by rfl⟩ : syracuseStep 928623 = 1392935) B1392935
theorem B3976361 : Blo 928581 3976361 := bstep (se 2 (by rfl) ⟨1491135, by rfl⟩ : syracuseStep 3976361 = 2982271) B2982271
theorem B929071 : Blo 928581 929071 := bstep (se 1 (by rfl) ⟨696803, by rfl⟩ : syracuseStep 929071 = 1393607) B1393607
theorem B2239865 : Blo 928581 2239865 := bstep (se 2 (by rfl) ⟨839949, by rfl⟩ : syracuseStep 2239865 = 1679899) B1679899
theorem B929183 : Blo 928581 929183 := bstep (se 1 (by rfl) ⟨696887, by rfl⟩ : syracuseStep 929183 = 1393775) B1393775
theorem B929311 : Blo 928581 929311 := bstep (se 1 (by rfl) ⟨696983, by rfl⟩ : syracuseStep 929311 = 1393967) B1393967
theorem B929447 : Blo 928581 929447 := bstep (se 1 (by rfl) ⟨697085, by rfl⟩ : syracuseStep 929447 = 1394171) B1394171
theorem B6368951 : Blo 928581 6368951 := bstep (se 1 (by rfl) ⟨4776713, by rfl⟩ : syracuseStep 6368951 = 9553427) B9553427
theorem B929471 : Blo 928581 929471 := bstep (se 1 (by rfl) ⟨697103, by rfl⟩ : syracuseStep 929471 = 1394207) B1394207
theorem B929567 : Blo 928581 929567 := bstep (se 1 (by rfl) ⟨697175, by rfl⟩ : syracuseStep 929567 = 1394351) B1394351
theorem B80424737 : Blo 928581 80424737 := bstep (se 2 (by rfl) ⟨30159276, by rfl⟩ : syracuseStep 80424737 = 60318553) B60318553
theorem B929647 : Blo 928581 929647 := bstep (se 1 (by rfl) ⟨697235, by rfl⟩ : syracuseStep 929647 = 1394471) B1394471
theorem B26882057 : Blo 928581 26882057 := bstep (se 2 (by rfl) ⟨10080771, by rfl⟩ : syracuseStep 26882057 = 20161543) B20161543
theorem B3780715 : Blo 928581 3780715 := bstep (se 1 (by rfl) ⟨2835536, by rfl⟩ : syracuseStep 3780715 = 5671073) B5671073
theorem B3584135 : Blo 928581 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B930015 : Blo 928581 930015 := bstep (se 1 (by rfl) ⟨697511, by rfl⟩ : syracuseStep 930015 = 1395023) B1395023
theorem B12398845 : Blo 928581 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B930047 : Blo 928581 930047 := bstep (se 1 (by rfl) ⟨697535, by rfl⟩ : syracuseStep 930047 = 1395071) B1395071
theorem B930075 : Blo 928581 930075 := bstep (se 1 (by rfl) ⟨697556, by rfl⟩ : syracuseStep 930075 = 1395113) B1395113
theorem B930331 : Blo 928581 930331 := bstep (se 1 (by rfl) ⟨697748, by rfl⟩ : syracuseStep 930331 = 1395497) B1395497
theorem B930471 : Blo 928581 930471 := bstep (se 1 (by rfl) ⟨697853, by rfl⟩ : syracuseStep 930471 = 1395707) B1395707
theorem B1487567 : Blo 928581 1487567 := bstep (se 1 (by rfl) ⟨1115675, by rfl⟩ : syracuseStep 1487567 = 2231351) B2231351
theorem B930511 : Blo 928581 930511 := bstep (se 1 (by rfl) ⟨697883, by rfl⟩ : syracuseStep 930511 = 1395767) B1395767
theorem B930591 : Blo 928581 930591 := bstep (se 1 (by rfl) ⟨697943, by rfl⟩ : syracuseStep 930591 = 1395887) B1395887
theorem B5288759 : Blo 928581 5288759 := bstep (se 1 (by rfl) ⟨3966569, by rfl⟩ : syracuseStep 5288759 = 7933139) B7933139
theorem B1487855 : Blo 928581 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B931071 : Blo 928581 931071 := bstep (se 1 (by rfl) ⟨698303, by rfl⟩ : syracuseStep 931071 = 1396607) B1396607
theorem B931199 : Blo 928581 931199 := bstep (se 1 (by rfl) ⟨698399, by rfl⟩ : syracuseStep 931199 = 1396799) B1396799
theorem B5649911 : Blo 928581 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B931355 : Blo 928581 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B27178681 : Blo 928581 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B931535 : Blo 928581 931535 := bstep (se 1 (by rfl) ⟨698651, by rfl⟩ : syracuseStep 931535 = 1397303) B1397303
theorem B10598201 : Blo 928581 10598201 := bstep (se 2 (by rfl) ⟨3974325, by rfl⟩ : syracuseStep 10598201 = 7948651) B7948651
theorem B6797135 : Blo 928581 6797135 := bstep (se 1 (by rfl) ⟨5097851, by rfl⟩ : syracuseStep 6797135 = 10195703) B10195703
theorem B931775 : Blo 928581 931775 := bstep (se 1 (by rfl) ⟨698831, by rfl⟩ : syracuseStep 931775 = 1397663) B1397663
theorem B931903 : Blo 928581 931903 := bstep (se 1 (by rfl) ⟨698927, by rfl⟩ : syracuseStep 931903 = 1397855) B1397855
theorem B931943 : Blo 928581 931943 := bstep (se 1 (by rfl) ⟨698957, by rfl⟩ : syracuseStep 931943 = 1397915) B1397915
theorem B932399 : Blo 928581 932399 := bstep (se 1 (by rfl) ⟨699299, by rfl⟩ : syracuseStep 932399 = 1398599) B1398599
theorem B1882937 : Blo 928581 1882937 := bstep (se 2 (by rfl) ⟨706101, by rfl⟩ : syracuseStep 1882937 = 1412203) B1412203
theorem B5290991 : Blo 928581 5290991 := bstep (se 1 (by rfl) ⟨3968243, by rfl⟩ : syracuseStep 5290991 = 7936487) B7936487
theorem B21740557 : Blo 928581 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B12106867 : Blo 928581 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B9551783 : Blo 928581 9551783 := bstep (se 1 (by rfl) ⟨7163837, by rfl⟩ : syracuseStep 9551783 = 14327675) B14327675
theorem B8503289 : Blo 928581 8503289 := bstep (se 2 (by rfl) ⟨3188733, by rfl⟩ : syracuseStep 8503289 = 6377467) B6377467
theorem B3358817 : Blo 928581 3358817 := bstep (se 2 (by rfl) ⟨1259556, by rfl⟩ : syracuseStep 3358817 = 2519113) B2519113
theorem B4767887 : Blo 928581 4767887 := bstep (se 1 (by rfl) ⟨3575915, by rfl⟩ : syracuseStep 4767887 = 7151831) B7151831
theorem B5292175 : Blo 928581 5292175 := bstep (se 1 (by rfl) ⟨3969131, by rfl⟩ : syracuseStep 5292175 = 7938263) B7938263
theorem B13418885 : Blo 928581 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B3981707 : Blo 928581 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B1393127 : Blo 928581 1393127 := bstep (se 1 (by rfl) ⟨1044845, by rfl⟩ : syracuseStep 1393127 = 2089691) B2089691
theorem B1393403 : Blo 928581 1393403 := bstep (se 1 (by rfl) ⟨1045052, by rfl⟩ : syracuseStep 1393403 = 2090105) B2090105
theorem B130892591 : Blo 928581 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B1393847 : Blo 928581 1393847 := bstep (se 1 (by rfl) ⟨1045385, by rfl⟩ : syracuseStep 1393847 = 2090771) B2090771
theorem B4474079 : Blo 928581 4474079 := bstep (se 1 (by rfl) ⟨3355559, by rfl⟩ : syracuseStep 4474079 = 6711119) B6711119
theorem B2835731 : Blo 928581 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B1393991 : Blo 928581 1393991 := bstep (se 1 (by rfl) ⟨1045493, by rfl⟩ : syracuseStep 1393991 = 2090987) B2090987
theorem B1394087 : Blo 928581 1394087 := bstep (se 1 (by rfl) ⟨1045565, by rfl⟩ : syracuseStep 1394087 = 2091131) B2091131
theorem B1394267 : Blo 928581 1394267 := bstep (se 1 (by rfl) ⟨1045700, by rfl⟩ : syracuseStep 1394267 = 2091401) B2091401
theorem B1394735 : Blo 928581 1394735 := bstep (se 1 (by rfl) ⟨1046051, by rfl⟩ : syracuseStep 1394735 = 2092103) B2092103
theorem B4704479 : Blo 928581 4704479 := bstep (se 1 (by rfl) ⟨3528359, by rfl⟩ : syracuseStep 4704479 = 7056719) B7056719
theorem B1394999 : Blo 928581 1394999 := bstep (se 1 (by rfl) ⟨1046249, by rfl⟩ : syracuseStep 1394999 = 2092499) B2092499
theorem B1395179 : Blo 928581 1395179 := bstep (se 1 (by rfl) ⟨1046384, by rfl⟩ : syracuseStep 1395179 = 2092769) B2092769
theorem B5655041 : Blo 928581 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B1395419 : Blo 928581 1395419 := bstep (se 1 (by rfl) ⟨1046564, by rfl⟩ : syracuseStep 1395419 = 2093129) B2093129
theorem B1395455 : Blo 928581 1395455 := bstep (se 1 (by rfl) ⟨1046591, by rfl⟩ : syracuseStep 1395455 = 2093183) B2093183
theorem B11946761 : Blo 928581 11946761 := bstep (se 2 (by rfl) ⟨4480035, by rfl⟩ : syracuseStep 11946761 = 8960071) B8960071
theorem B5294909 : Blo 928581 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B4705289 : Blo 928581 4705289 := bstep (se 2 (by rfl) ⟨1764483, by rfl⟩ : syracuseStep 4705289 = 3528967) B3528967
theorem B1396175 : Blo 928581 1396175 := bstep (se 1 (by rfl) ⟨1047131, by rfl⟩ : syracuseStep 1396175 = 2094263) B2094263
theorem B1396265 : Blo 928581 1396265 := bstep (se 2 (by rfl) ⟨523599, by rfl⟩ : syracuseStep 1396265 = 1047199) B1047199
theorem B1396559 : Blo 928581 1396559 := bstep (se 1 (by rfl) ⟨1047419, by rfl⟩ : syracuseStep 1396559 = 2094839) B2094839
theorem B1396679 : Blo 928581 1396679 := bstep (se 1 (by rfl) ⟨1047509, by rfl⟩ : syracuseStep 1396679 = 2095019) B2095019
theorem B1396763 : Blo 928581 1396763 := bstep (se 1 (by rfl) ⟨1047572, by rfl⟩ : syracuseStep 1396763 = 2095145) B2095145
theorem B4477193 : Blo 928581 4477193 := bstep (se 2 (by rfl) ⟨1678947, by rfl⟩ : syracuseStep 4477193 = 3357895) B3357895
theorem B1397039 : Blo 928581 1397039 := bstep (se 1 (by rfl) ⟨1047779, by rfl⟩ : syracuseStep 1397039 = 2095559) B2095559
theorem B1397147 : Blo 928581 1397147 := bstep (se 1 (by rfl) ⟨1047860, by rfl⟩ : syracuseStep 1397147 = 2095721) B2095721
theorem B4706747 : Blo 928581 4706747 := bstep (se 1 (by rfl) ⟨3530060, by rfl⟩ : syracuseStep 4706747 = 7060121) B7060121
theorem B1397183 : Blo 928581 1397183 := bstep (se 1 (by rfl) ⟨1047887, by rfl⟩ : syracuseStep 1397183 = 2095775) B2095775
theorem B1397279 : Blo 928581 1397279 := bstep (se 1 (by rfl) ⟨1047959, by rfl⟩ : syracuseStep 1397279 = 2095919) B2095919
theorem B1987129 : Blo 928581 1987129 := bstep (se 2 (by rfl) ⟨745173, by rfl⟩ : syracuseStep 1987129 = 1490347) B1490347
theorem B1397567 : Blo 928581 1397567 := bstep (se 1 (by rfl) ⟨1048175, by rfl⟩ : syracuseStep 1397567 = 2096351) B2096351
theorem B1135559 : Blo 928581 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B1397711 : Blo 928581 1397711 := bstep (se 1 (by rfl) ⟨1048283, by rfl⟩ : syracuseStep 1397711 = 2096567) B2096567
theorem B76403735 : Blo 928581 76403735 := bstep (se 1 (by rfl) ⟨57302801, by rfl⟩ : syracuseStep 76403735 = 114605603) B114605603
theorem B1397801 : Blo 928581 1397801 := bstep (se 2 (by rfl) ⟨524175, by rfl⟩ : syracuseStep 1397801 = 1048351) B1048351
theorem B1397831 : Blo 928581 1397831 := bstep (se 1 (by rfl) ⟨1048373, by rfl⟩ : syracuseStep 1397831 = 2096747) B2096747
theorem B1398011 : Blo 928581 1398011 := bstep (se 1 (by rfl) ⟨1048508, by rfl⟩ : syracuseStep 1398011 = 2097017) B2097017
theorem B1398071 : Blo 928581 1398071 := bstep (se 1 (by rfl) ⟨1048553, by rfl⟩ : syracuseStep 1398071 = 2097107) B2097107
theorem B12080623 : Blo 928581 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B3134969 : Blo 928581 3134969 := bstep (se 2 (by rfl) ⟨1175613, by rfl⟩ : syracuseStep 3134969 = 2351227) B2351227
theorem B1398377 : Blo 928581 1398377 := bstep (se 2 (by rfl) ⟨524391, by rfl⟩ : syracuseStep 1398377 = 1048783) B1048783
theorem B3135131 : Blo 928581 3135131 := bstep (se 1 (by rfl) ⟨2351348, by rfl⟩ : syracuseStep 3135131 = 4702697) B4702697
theorem B4708043 : Blo 928581 4708043 := bstep (se 1 (by rfl) ⟨3531032, by rfl⟩ : syracuseStep 4708043 = 7062065) B7062065
theorem B7165691 : Blo 928581 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B4479113 : Blo 928581 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B16144829 : Blo 928581 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B90463067 : Blo 928581 90463067 := bstep (se 1 (by rfl) ⟨67847300, by rfl⟩ : syracuseStep 90463067 = 135694601) B135694601
theorem B5299465 : Blo 928581 5299465 := bstep (se 2 (by rfl) ⟨1987299, by rfl⟩ : syracuseStep 5299465 = 3974599) B3974599
theorem B2645473 : Blo 928581 2645473 := bstep (se 2 (by rfl) ⟨992052, by rfl⟩ : syracuseStep 2645473 = 1984105) B1984105
theorem B3137021 : Blo 928581 3137021 := bstep (se 3 (by rfl) ⟨588191, by rfl⟩ : syracuseStep 3137021 = 1176383) B1176383
theorem B2645723 : Blo 928581 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B2580191 : Blo 928581 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B2351207 : Blo 928581 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B2351339 : Blo 928581 2351339 := bstep (se 1 (by rfl) ⟨1763504, by rfl⟩ : syracuseStep 2351339 = 3527009) B3527009
theorem B2646715 : Blo 928581 2646715 := bstep (se 1 (by rfl) ⟨1985036, by rfl⟩ : syracuseStep 2646715 = 3970073) B3970073
theorem B123921247 : Blo 928581 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B3139127 : Blo 928581 3139127 := bstep (se 1 (by rfl) ⟨2354345, by rfl⟩ : syracuseStep 3139127 = 4708691) B4708691
theorem B18376465 : Blo 928581 18376465 := bstep (se 2 (by rfl) ⟨6891174, by rfl⟩ : syracuseStep 18376465 = 13782349) B13782349
theorem B38201219 : Blo 928581 38201219 := bstep (se 1 (by rfl) ⟨28650914, by rfl⟩ : syracuseStep 38201219 = 57301829) B57301829
theorem B3139559 : Blo 928581 3139559 := bstep (se 1 (by rfl) ⟨2354669, by rfl⟩ : syracuseStep 3139559 = 4709339) B4709339
theorem B4253705 : Blo 928581 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B34007303 : Blo 928581 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B3139883 : Blo 928581 3139883 := bstep (se 1 (by rfl) ⟨2354912, by rfl⟩ : syracuseStep 3139883 = 4709825) B4709825
theorem B4713227 : Blo 928581 4713227 := bstep (se 1 (by rfl) ⟨3534920, by rfl⟩ : syracuseStep 4713227 = 7069841) B7069841
theorem B2354143 : Blo 928581 2354143 := bstep (se 1 (by rfl) ⟨1765607, by rfl⟩ : syracuseStep 2354143 = 3531215) B3531215
theorem B2977003 : Blo 928581 2977003 := bstep (se 1 (by rfl) ⟨2232752, by rfl⟩ : syracuseStep 2977003 = 4465505) B4465505
theorem B2649323 : Blo 928581 2649323 := bstep (se 1 (by rfl) ⟨1986992, by rfl⟩ : syracuseStep 2649323 = 3973985) B3973985
theorem B2649847 : Blo 928581 2649847 := bstep (se 1 (by rfl) ⟨1987385, by rfl⟩ : syracuseStep 2649847 = 3974771) B3974771
theorem B2977823 : Blo 928581 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B2093111 : Blo 928581 2093111 := bstep (se 1 (by rfl) ⟨1569833, by rfl⟩ : syracuseStep 2093111 = 3139667) B3139667
theorem B1765471 : Blo 928581 1765471 := bstep (se 1 (by rfl) ⟨1324103, by rfl⟩ : syracuseStep 1765471 = 2648207) B2648207
theorem B1175887 : Blo 928581 1175887 := bstep (se 1 (by rfl) ⟨881915, by rfl⟩ : syracuseStep 1175887 = 1763831) B1763831
theorem B2355551 : Blo 928581 2355551 := bstep (se 1 (by rfl) ⟨1766663, by rfl⟩ : syracuseStep 2355551 = 3533327) B3533327
theorem B4714847 : Blo 928581 4714847 := bstep (se 1 (by rfl) ⟨3536135, by rfl⟩ : syracuseStep 4714847 = 7072271) B7072271
theorem B1765729 : Blo 928581 1765729 := bstep (se 2 (by rfl) ⟨662148, by rfl⟩ : syracuseStep 1765729 = 1324297) B1324297
theorem B2978171 : Blo 928581 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B3142043 : Blo 928581 3142043 := bstep (se 1 (by rfl) ⟨2356532, by rfl⟩ : syracuseStep 3142043 = 4713065) B4713065
theorem B5305115 : Blo 928581 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B3535771 : Blo 928581 3535771 := bstep (se 1 (by rfl) ⟨2651828, by rfl⟩ : syracuseStep 3535771 = 5303657) B5303657
theorem B10908665 : Blo 928581 10908665 := bstep (se 2 (by rfl) ⟨4090749, by rfl⟩ : syracuseStep 10908665 = 8181499) B8181499
theorem B2356391 : Blo 928581 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B10319329 : Blo 928581 10319329 := bstep (se 2 (by rfl) ⟨3869748, by rfl⟩ : syracuseStep 10319329 = 7739497) B7739497
theorem B18118201 : Blo 928581 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B1046119 : Blo 928581 1046119 := bstep (se 1 (by rfl) ⟨784589, by rfl⟩ : syracuseStep 1046119 = 1569179) B1569179
theorem B1570441 : Blo 928581 1570441 := bstep (se 2 (by rfl) ⟨588915, by rfl⟩ : syracuseStep 1570441 = 1177831) B1177831
theorem B5961671 : Blo 928581 5961671 := bstep (se 1 (by rfl) ⟨4471253, by rfl⟩ : syracuseStep 5961671 = 8942507) B8942507
theorem B3537017 : Blo 928581 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1046695 : Blo 928581 1046695 := bstep (se 1 (by rfl) ⟨785021, by rfl⟩ : syracuseStep 1046695 = 1570043) B1570043
theorem B1308847 : Blo 928581 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B2095415 : Blo 928581 2095415 := bstep (se 1 (by rfl) ⟨1571561, by rfl⟩ : syracuseStep 2095415 = 3143123) B3143123
theorem B1571231 : Blo 928581 1571231 := bstep (se 1 (by rfl) ⟨1178423, by rfl⟩ : syracuseStep 1571231 = 2356847) B2356847
theorem B3144095 : Blo 928581 3144095 := bstep (se 1 (by rfl) ⟨2358071, by rfl⟩ : syracuseStep 3144095 = 4716143) B4716143
theorem B11925953 : Blo 928581 11925953 := bstep (se 2 (by rfl) ⟨4472232, by rfl⟩ : syracuseStep 11925953 = 8944465) B8944465
theorem B2095595 : Blo 928581 2095595 := bstep (se 1 (by rfl) ⟨1571696, by rfl⟩ : syracuseStep 2095595 = 3143393) B3143393
theorem B1178479 : Blo 928581 1178479 := bstep (se 1 (by rfl) ⟨883859, by rfl⟩ : syracuseStep 1178479 = 1767719) B1767719
theorem B1178651 : Blo 928581 1178651 := bstep (se 1 (by rfl) ⟨883988, by rfl⟩ : syracuseStep 1178651 = 1767977) B1767977
theorem B4717601 : Blo 928581 4717601 := bstep (se 2 (by rfl) ⟨1769100, by rfl⟩ : syracuseStep 4717601 = 3538201) B3538201
theorem B29817953 : Blo 928581 29817953 := bstep (se 2 (by rfl) ⟨11181732, by rfl⟩ : syracuseStep 29817953 = 22363465) B22363465
theorem B2358497 : Blo 928581 2358497 := bstep (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) B1768873
theorem B2096927 : Blo 928581 2096927 := bstep (se 1 (by rfl) ⟨1572695, by rfl⟩ : syracuseStep 2096927 = 3145391) B3145391
theorem B3178591 : Blo 928581 3178591 := bstep (se 1 (by rfl) ⟨2383943, by rfl⟩ : syracuseStep 3178591 = 4767887) B4767887
theorem B1573033 : Blo 928581 1573033 := bstep (se 2 (by rfl) ⟨589887, by rfl⟩ : syracuseStep 1573033 = 1179775) B1179775
theorem B2654471 : Blo 928581 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B1769951 : Blo 928581 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B2982719 : Blo 928581 2982719 := bstep (se 1 (by rfl) ⟨2237039, by rfl⟩ : syracuseStep 2982719 = 4474079) B4474079
theorem B3539963 : Blo 928581 3539963 := bstep (se 1 (by rfl) ⟨2654972, by rfl⟩ : syracuseStep 3539963 = 5309945) B5309945
theorem B35783693 : Blo 928581 35783693 := bstep (se 3 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 35783693 = 13418885) B13418885
theorem B2098259 : Blo 928581 2098259 := bstep (se 1 (by rfl) ⟨1573694, by rfl⟩ : syracuseStep 2098259 = 3147389) B3147389
theorem B3147065 : Blo 928581 3147065 := bstep (se 2 (by rfl) ⟨1180149, by rfl⟩ : syracuseStep 3147065 = 2360299) B2360299
theorem B3770027 : Blo 928581 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B7964507 : Blo 928581 7964507 := bstep (se 1 (by rfl) ⟨5973380, by rfl⟩ : syracuseStep 7964507 = 11946761) B11946761
theorem B349046909 : Blo 928581 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B3967613 : Blo 928581 3967613 := bstep (se 3 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 3967613 = 1487855) B1487855
theorem B2984795 : Blo 928581 2984795 := bstep (se 1 (by rfl) ⟨2238596, by rfl⟩ : syracuseStep 2984795 = 4477193) B4477193
theorem B2985245 : Blo 928581 2985245 := bstep (se 3 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 2985245 = 1119467) B1119467
theorem B2986075 : Blo 928581 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B3969337 : Blo 928581 3969337 := bstep (se 2 (by rfl) ⟨1488501, by rfl⟩ : syracuseStep 3969337 = 2977003) B2977003
theorem B2232859 : Blo 928581 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B10621529 : Blo 928581 10621529 := bstep (se 2 (by rfl) ⟨3983073, by rfl⟩ : syracuseStep 10621529 = 7966147) B7966147
theorem B25467479 : Blo 928581 25467479 := bstep (se 1 (by rfl) ⟨19100609, by rfl⟩ : syracuseStep 25467479 = 38201219) B38201219
theorem B24157601 : Blo 928581 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B5021165 : Blo 928581 5021165 := bstep (se 3 (by rfl) ⟨941468, by rfl⟩ : syracuseStep 5021165 = 1882937) B1882937
theorem B53616491 : Blo 928581 53616491 := bstep (se 1 (by rfl) ⟨40212368, by rfl⟩ : syracuseStep 53616491 = 80424737) B80424737
theorem B1745129 : Blo 928581 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B991711 : Blo 928581 991711 := bstep (se 1 (by rfl) ⟨743783, by rfl⟩ : syracuseStep 991711 = 1487567) B1487567
theorem B4531423 : Blo 928581 4531423 := bstep (se 1 (by rfl) ⟨3398567, by rfl⟩ : syracuseStep 4531423 = 6797135) B6797135
theorem B3974447 : Blo 928581 3974447 := bstep (se 1 (by rfl) ⟨2980835, by rfl⟩ : syracuseStep 3974447 = 5961671) B5961671
theorem B128722445 : Blo 928581 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B7055261 : Blo 928581 7055261 := bstep (se 3 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 7055261 = 2645723) B2645723
theorem B25471421 : Blo 928581 25471421 := bstep (se 3 (by rfl) ⟨4775891, by rfl⟩ : syracuseStep 25471421 = 9551783) B9551783
theorem B2239211 : Blo 928581 2239211 := bstep (se 1 (by rfl) ⟨1679408, by rfl⟩ : syracuseStep 2239211 = 3358817) B3358817
theorem B7940861 : Blo 928581 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B7056233 : Blo 928581 7056233 := bstep (se 2 (by rfl) ⟨2646087, by rfl⟩ : syracuseStep 7056233 = 5292175) B5292175
theorem B928751 : Blo 928581 928751 := bstep (se 1 (by rfl) ⟨696563, by rfl⟩ : syracuseStep 928751 = 1393127) B1393127
theorem B14298113 : Blo 928581 14298113 := bstep (se 2 (by rfl) ⟨5361792, by rfl⟩ : syracuseStep 14298113 = 10723585) B10723585
theorem B928935 : Blo 928581 928935 := bstep (se 1 (by rfl) ⟨696701, by rfl⟩ : syracuseStep 928935 = 1393403) B1393403
theorem B21736799 : Blo 928581 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B929231 : Blo 928581 929231 := bstep (se 1 (by rfl) ⟨696923, by rfl⟩ : syracuseStep 929231 = 1393847) B1393847
theorem B929327 : Blo 928581 929327 := bstep (se 1 (by rfl) ⟨696995, by rfl⟩ : syracuseStep 929327 = 1393991) B1393991
theorem B929391 : Blo 928581 929391 := bstep (se 1 (by rfl) ⟨697043, by rfl⟩ : syracuseStep 929391 = 1394087) B1394087
theorem B30584465 : Blo 928581 30584465 := bstep (se 2 (by rfl) ⟨11469174, by rfl⟩ : syracuseStep 30584465 = 22938349) B22938349
theorem B14331617 : Blo 928581 14331617 := bstep (se 2 (by rfl) ⟨5374356, by rfl⟩ : syracuseStep 14331617 = 10748713) B10748713
theorem B929511 : Blo 928581 929511 := bstep (se 1 (by rfl) ⟨697133, by rfl⟩ : syracuseStep 929511 = 1394267) B1394267
theorem B165228329 : Blo 928581 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B929823 : Blo 928581 929823 := bstep (se 1 (by rfl) ⟨697367, by rfl⟩ : syracuseStep 929823 = 1394735) B1394735
theorem B929999 : Blo 928581 929999 := bstep (se 1 (by rfl) ⟨697499, by rfl⟩ : syracuseStep 929999 = 1394999) B1394999
theorem B7057691 : Blo 928581 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B930119 : Blo 928581 930119 := bstep (se 1 (by rfl) ⟨697589, by rfl⟩ : syracuseStep 930119 = 1395179) B1395179
theorem B930279 : Blo 928581 930279 := bstep (se 1 (by rfl) ⟨697709, by rfl⟩ : syracuseStep 930279 = 1395419) B1395419
theorem B930303 : Blo 928581 930303 := bstep (se 1 (by rfl) ⟨697727, by rfl⟩ : syracuseStep 930303 = 1395455) B1395455
theorem B930783 : Blo 928581 930783 := bstep (se 1 (by rfl) ⟨698087, by rfl⟩ : syracuseStep 930783 = 1396175) B1396175
theorem B930843 : Blo 928581 930843 := bstep (se 1 (by rfl) ⟨698132, by rfl⟩ : syracuseStep 930843 = 1396265) B1396265
theorem B3028157 : Blo 928581 3028157 := bstep (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) B1135559
theorem B931039 : Blo 928581 931039 := bstep (se 1 (by rfl) ⟨698279, by rfl⟩ : syracuseStep 931039 = 1396559) B1396559
theorem B931119 : Blo 928581 931119 := bstep (se 1 (by rfl) ⟨698339, by rfl⟩ : syracuseStep 931119 = 1396679) B1396679
theorem B931175 : Blo 928581 931175 := bstep (se 1 (by rfl) ⟨698381, by rfl⟩ : syracuseStep 931175 = 1396763) B1396763
theorem B931359 : Blo 928581 931359 := bstep (se 1 (by rfl) ⟨698519, by rfl⟩ : syracuseStep 931359 = 1397039) B1397039
theorem B931431 : Blo 928581 931431 := bstep (se 1 (by rfl) ⟨698573, by rfl⟩ : syracuseStep 931431 = 1397147) B1397147
theorem B931455 : Blo 928581 931455 := bstep (se 1 (by rfl) ⟨698591, by rfl⟩ : syracuseStep 931455 = 1397183) B1397183
theorem B931519 : Blo 928581 931519 := bstep (se 1 (by rfl) ⟨698639, by rfl⟩ : syracuseStep 931519 = 1397279) B1397279
theorem B931711 : Blo 928581 931711 := bstep (se 1 (by rfl) ⟨698783, by rfl⟩ : syracuseStep 931711 = 1397567) B1397567
theorem B931807 : Blo 928581 931807 := bstep (se 1 (by rfl) ⟨698855, by rfl⟩ : syracuseStep 931807 = 1397711) B1397711
theorem B50935823 : Blo 928581 50935823 := bstep (se 1 (by rfl) ⟨38201867, by rfl⟩ : syracuseStep 50935823 = 76403735) B76403735
theorem B4765715 : Blo 928581 4765715 := bstep (se 1 (by rfl) ⟨3574286, by rfl⟩ : syracuseStep 4765715 = 7148573) B7148573
theorem B931867 : Blo 928581 931867 := bstep (se 1 (by rfl) ⟨698900, by rfl⟩ : syracuseStep 931867 = 1397801) B1397801
theorem B931887 : Blo 928581 931887 := bstep (se 1 (by rfl) ⟨698915, by rfl⟩ : syracuseStep 931887 = 1397831) B1397831
theorem B932007 : Blo 928581 932007 := bstep (se 1 (by rfl) ⟨699005, by rfl⟩ : syracuseStep 932007 = 1398011) B1398011
theorem B932047 : Blo 928581 932047 := bstep (se 1 (by rfl) ⟨699035, by rfl⟩ : syracuseStep 932047 = 1398071) B1398071
theorem B1489207 : Blo 928581 1489207 := bstep (se 1 (by rfl) ⟨1116905, by rfl⟩ : syracuseStep 1489207 = 2233811) B2233811
theorem B932251 : Blo 928581 932251 := bstep (se 1 (by rfl) ⟨699188, by rfl⟩ : syracuseStep 932251 = 1398377) B1398377
theorem B10763219 : Blo 928581 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B60308711 : Blo 928581 60308711 := bstep (se 1 (by rfl) ⟨45231533, by rfl⟩ : syracuseStep 60308711 = 90463067) B90463067
theorem B1720127 : Blo 928581 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B1491065 : Blo 928581 1491065 := bstep (se 2 (by rfl) ⟨559149, by rfl⟩ : syracuseStep 1491065 = 1118299) B1118299
theorem B1491257 : Blo 928581 1491257 := bstep (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) B1118443
theorem B16531793 : Blo 928581 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B193184135 : Blo 928581 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B4702859 : Blo 928581 4702859 := bstep (se 1 (by rfl) ⟨3527144, by rfl⟩ : syracuseStep 4702859 = 7054289) B7054289
theorem B2835803 : Blo 928581 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B16107497 : Blo 928581 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B4245529 : Blo 928581 4245529 := bstep (se 2 (by rfl) ⟨1592073, by rfl⟩ : syracuseStep 4245529 = 3184147) B3184147
theorem B1394825 : Blo 928581 1394825 := bstep (se 2 (by rfl) ⟨523059, by rfl⟩ : syracuseStep 1394825 = 1046119) B1046119
theorem B1493243 : Blo 928581 1493243 := bstep (se 1 (by rfl) ⟨1119932, by rfl⟩ : syracuseStep 1493243 = 2239865) B2239865
theorem B4245967 : Blo 928581 4245967 := bstep (se 1 (by rfl) ⟨3184475, by rfl⟩ : syracuseStep 4245967 = 6368951) B6368951
theorem B1395407 : Blo 928581 1395407 := bstep (se 1 (by rfl) ⟨1046555, by rfl⟩ : syracuseStep 1395407 = 2093111) B2093111
theorem B1395593 : Blo 928581 1395593 := bstep (se 2 (by rfl) ⟨523347, by rfl⟩ : syracuseStep 1395593 = 1046695) B1046695
theorem B1985447 : Blo 928581 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B3525839 : Blo 928581 3525839 := bstep (se 1 (by rfl) ⟨2644379, by rfl⟩ : syracuseStep 3525839 = 5288759) B5288759
theorem B7065467 : Blo 928581 7065467 := bstep (se 1 (by rfl) ⟨5299100, by rfl⟩ : syracuseStep 7065467 = 10598201) B10598201
theorem B28987409 : Blo 928581 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B16142489 : Blo 928581 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B1396943 : Blo 928581 1396943 := bstep (se 1 (by rfl) ⟨1047707, by rfl⟩ : syracuseStep 1396943 = 2095415) B2095415
theorem B7950635 : Blo 928581 7950635 := bstep (se 1 (by rfl) ⟨5962976, by rfl⟩ : syracuseStep 7950635 = 11925953) B11925953
theorem B1397063 : Blo 928581 1397063 := bstep (se 1 (by rfl) ⟨1047797, by rfl⟩ : syracuseStep 1397063 = 2095595) B2095595
theorem B7065953 : Blo 928581 7065953 := bstep (se 2 (by rfl) ⟨2649732, by rfl⟩ : syracuseStep 7065953 = 5299465) B5299465
theorem B3527297 : Blo 928581 3527297 := bstep (se 2 (by rfl) ⟨1322736, by rfl⟩ : syracuseStep 3527297 = 2645473) B2645473
theorem B3527327 : Blo 928581 3527327 := bstep (se 1 (by rfl) ⟨2645495, by rfl⟩ : syracuseStep 3527327 = 5290991) B5290991
theorem B19878635 : Blo 928581 19878635 := bstep (se 1 (by rfl) ⟨14908976, by rfl⟩ : syracuseStep 19878635 = 29817953) B29817953
theorem B1397951 : Blo 928581 1397951 := bstep (se 1 (by rfl) ⟨1048463, by rfl⟩ : syracuseStep 1397951 = 2096927) B2096927
theorem B9557693 : Blo 928581 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B1890487 : Blo 928581 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B3528953 : Blo 928581 3528953 := bstep (se 2 (by rfl) ⟨1323357, by rfl⟩ : syracuseStep 3528953 = 2646715) B2646715
theorem B3136319 : Blo 928581 3136319 := bstep (se 1 (by rfl) ⟨2352239, by rfl⟩ : syracuseStep 3136319 = 4704479) B4704479
theorem B3529939 : Blo 928581 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B3136859 : Blo 928581 3136859 := bstep (se 1 (by rfl) ⟨2352644, by rfl⟩ : syracuseStep 3136859 = 4705289) B4705289
theorem B7953983 : Blo 928581 7953983 := bstep (se 1 (by rfl) ⟨5965487, by rfl⟩ : syracuseStep 7953983 = 11930975) B11930975
theorem B24501953 : Blo 928581 24501953 := bstep (se 2 (by rfl) ⟨9188232, by rfl⟩ : syracuseStep 24501953 = 18376465) B18376465
theorem B3137831 : Blo 928581 3137831 := bstep (se 1 (by rfl) ⟨2353373, by rfl⟩ : syracuseStep 3137831 = 4706747) B4706747
theorem B2089979 : Blo 928581 2089979 := bstep (se 1 (by rfl) ⟨1567484, by rfl⟩ : syracuseStep 2089979 = 3134969) B3134969
theorem B2090087 : Blo 928581 2090087 := bstep (se 1 (by rfl) ⟨1567565, by rfl⟩ : syracuseStep 2090087 = 3135131) B3135131
theorem B3138695 : Blo 928581 3138695 := bstep (se 1 (by rfl) ⟨2354021, by rfl⟩ : syracuseStep 3138695 = 4708043) B4708043
theorem B4777127 : Blo 928581 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B14345405 : Blo 928581 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B3138857 : Blo 928581 3138857 := bstep (se 2 (by rfl) ⟨1177071, by rfl⟩ : syracuseStep 3138857 = 2354143) B2354143
theorem B3533129 : Blo 928581 3533129 := bstep (se 2 (by rfl) ⟨1324923, by rfl⟩ : syracuseStep 3533129 = 2649847) B2649847
theorem B2091347 : Blo 928581 2091347 := bstep (se 1 (by rfl) ⟨1568510, by rfl⟩ : syracuseStep 2091347 = 3137021) B3137021
theorem B1567471 : Blo 928581 1567471 := bstep (se 1 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 1567471 = 2351207) B2351207
theorem B2353961 : Blo 928581 2353961 := bstep (se 2 (by rfl) ⟨882735, by rfl⟩ : syracuseStep 2353961 = 1765471) B1765471
theorem B5040953 : Blo 928581 5040953 := bstep (se 2 (by rfl) ⟨1890357, by rfl⟩ : syracuseStep 5040953 = 3780715) B3780715
theorem B1567559 : Blo 928581 1567559 := bstep (se 1 (by rfl) ⟨1175669, by rfl⟩ : syracuseStep 1567559 = 2351339) B2351339
theorem B1567849 : Blo 928581 1567849 := bstep (se 2 (by rfl) ⟨587943, by rfl⟩ : syracuseStep 1567849 = 1175887) B1175887
theorem B2354305 : Blo 928581 2354305 := bstep (se 2 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 2354305 = 1765729) B1765729
theorem B2518399 : Blo 928581 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B2649505 : Blo 928581 2649505 := bstep (se 2 (by rfl) ⟨993564, by rfl⟩ : syracuseStep 2649505 = 1987129) B1987129
theorem B2092751 : Blo 928581 2092751 := bstep (se 1 (by rfl) ⟨1569563, by rfl⟩ : syracuseStep 2092751 = 3139127) B3139127
theorem B4714361 : Blo 928581 4714361 := bstep (se 2 (by rfl) ⟨1767885, by rfl⟩ : syracuseStep 4714361 = 3535771) B3535771
theorem B2093039 : Blo 928581 2093039 := bstep (se 1 (by rfl) ⟨1569779, by rfl⟩ : syracuseStep 2093039 = 3139559) B3139559
theorem B22671535 : Blo 928581 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B2093255 : Blo 928581 2093255 := bstep (se 1 (by rfl) ⟨1569941, by rfl⟩ : syracuseStep 2093255 = 3139883) B3139883
theorem B7958735 : Blo 928581 7958735 := bstep (se 1 (by rfl) ⟨5969051, by rfl⟩ : syracuseStep 7958735 = 11938103) B11938103
theorem B3142151 : Blo 928581 3142151 := bstep (se 1 (by rfl) ⟨2356613, by rfl⟩ : syracuseStep 3142151 = 4713227) B4713227
theorem B13759105 : Blo 928581 13759105 := bstep (se 2 (by rfl) ⟨5159664, by rfl⟩ : syracuseStep 13759105 = 10319329) B10319329
theorem B2650907 : Blo 928581 2650907 := bstep (se 1 (by rfl) ⟨1988180, by rfl⟩ : syracuseStep 2650907 = 3976361) B3976361
theorem B1766215 : Blo 928581 1766215 := bstep (se 1 (by rfl) ⟨1324661, by rfl⟩ : syracuseStep 1766215 = 2649323) B2649323
theorem B2093921 : Blo 928581 2093921 := bstep (se 2 (by rfl) ⟨785220, by rfl⟩ : syracuseStep 2093921 = 1570441) B1570441
theorem B36238241 : Blo 928581 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B17921371 : Blo 928581 17921371 := bstep (se 1 (by rfl) ⟨13441028, by rfl⟩ : syracuseStep 17921371 = 26882057) B26882057
theorem B3143069 : Blo 928581 3143069 := bstep (se 3 (by rfl) ⟨589325, by rfl⟩ : syracuseStep 3143069 = 1178651) B1178651
theorem B14349797 : Blo 928581 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B1570367 : Blo 928581 1570367 := bstep (se 1 (by rfl) ⟨1177775, by rfl⟩ : syracuseStep 1570367 = 2355551) B2355551
theorem B3143231 : Blo 928581 3143231 := bstep (se 1 (by rfl) ⟨2357423, by rfl⟩ : syracuseStep 3143231 = 4714847) B4714847
theorem B2094695 : Blo 928581 2094695 := bstep (se 1 (by rfl) ⟨1571021, by rfl⟩ : syracuseStep 2094695 = 3142043) B3142043
theorem B3536743 : Blo 928581 3536743 := bstep (se 1 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 3536743 = 5305115) B5305115
theorem B7272443 : Blo 928581 7272443 := bstep (se 1 (by rfl) ⟨5454332, by rfl⟩ : syracuseStep 7272443 = 10908665) B10908665
theorem B1570927 : Blo 928581 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B3766607 : Blo 928581 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B1571305 : Blo 928581 1571305 := bstep (se 2 (by rfl) ⟨589239, by rfl⟩ : syracuseStep 1571305 = 1178479) B1178479
theorem B2358011 : Blo 928581 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B1047487 : Blo 928581 1047487 := bstep (se 1 (by rfl) ⟨785615, by rfl⟩ : syracuseStep 1047487 = 1571231) B1571231
theorem B2096063 : Blo 928581 2096063 := bstep (se 1 (by rfl) ⟨1572047, by rfl⟩ : syracuseStep 2096063 = 3144095) B3144095
theorem B3145067 : Blo 928581 3145067 := bstep (se 1 (by rfl) ⟨2358800, by rfl⟩ : syracuseStep 3145067 = 4717601) B4717601
theorem B1572331 : Blo 928581 1572331 := bstep (se 1 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 1572331 = 2358497) B2358497
theorem B5668859 : Blo 928581 5668859 := bstep (se 1 (by rfl) ⟨4251644, by rfl⟩ : syracuseStep 5668859 = 8503289) B8503289
theorem B77299757 : Blo 928581 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B2097377 : Blo 928581 2097377 := bstep (se 2 (by rfl) ⟨786516, by rfl⟩ : syracuseStep 2097377 = 1573033) B1573033
theorem B15925733 : Blo 928581 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B4653677 : Blo 928581 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B2359975 : Blo 928581 2359975 := bstep (se 1 (by rfl) ⟨1769981, by rfl⟩ : syracuseStep 2359975 = 3539963) B3539963
theorem B23855795 : Blo 928581 23855795 := bstep (se 1 (by rfl) ⟨17891846, by rfl⟩ : syracuseStep 23855795 = 35783693) B35783693
theorem B7078589 : Blo 928581 7078589 := bstep (se 3 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 7078589 = 2654471) B2654471
theorem B2098043 : Blo 928581 2098043 := bstep (se 1 (by rfl) ⟨1573532, by rfl⟩ : syracuseStep 2098043 = 3147065) B3147065
theorem B5309671 : Blo 928581 5309671 := bstep (se 1 (by rfl) ⟨3982253, by rfl⟩ : syracuseStep 5309671 = 7964507) B7964507
theorem B4719869 : Blo 928581 4719869 := bstep (se 3 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 4719869 = 1769951) B1769951
theorem B7081019 : Blo 928581 7081019 := bstep (se 1 (by rfl) ⟨5310764, by rfl⟩ : syracuseStep 7081019 = 10621529) B10621529
theorem B16978319 : Blo 928581 16978319 := bstep (se 1 (by rfl) ⟨12733739, by rfl⟩ : syracuseStep 16978319 = 25467479) B25467479
theorem B3347443 : Blo 928581 3347443 := bstep (se 1 (by rfl) ⟨2510582, by rfl⟩ : syracuseStep 3347443 = 5021165) B5021165
theorem B3184751 : Blo 928581 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B16980947 : Blo 928581 16980947 := bstep (se 1 (by rfl) ⟨12735710, by rfl⟩ : syracuseStep 16980947 = 25471421) B25471421
theorem B23895161 : Blo 928581 23895161 := bstep (se 2 (by rfl) ⟨8960685, by rfl⟩ : syracuseStep 23895161 = 17921371) B17921371
theorem B5971229 : Blo 928581 5971229 := bstep (se 3 (by rfl) ⟨1119605, by rfl⟩ : syracuseStep 5971229 = 2239211) B2239211
theorem B14491199 : Blo 928581 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B20389643 : Blo 928581 20389643 := bstep (se 1 (by rfl) ⟨15292232, by rfl⟩ : syracuseStep 20389643 = 30584465) B30584465
theorem B24158827 : Blo 928581 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B33957215 : Blo 928581 33957215 := bstep (se 1 (by rfl) ⟨25467911, by rfl⟩ : syracuseStep 33957215 = 50935823) B50935823
theorem B3779239 : Blo 928581 3779239 := bstep (se 1 (by rfl) ⟨2834429, by rfl⟩ : syracuseStep 3779239 = 5668859) B5668859
theorem B994043 : Blo 928581 994043 := bstep (se 1 (by rfl) ⟨745532, by rfl⟩ : syracuseStep 994043 = 1491065) B1491065
theorem B11021195 : Blo 928581 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B128789423 : Blo 928581 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B16952485 : Blo 928581 16952485 := bstep (se 4 (by rfl) ⟨1589295, by rfl⟩ : syracuseStep 16952485 = 3178591) B3178591
theorem B1322281 : Blo 928581 1322281 := bstep (se 2 (by rfl) ⟨495855, by rfl⟩ : syracuseStep 1322281 = 991711) B991711
theorem B3976685 : Blo 928581 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B232697939 : Blo 928581 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B929883 : Blo 928581 929883 := bstep (se 1 (by rfl) ⟨697412, by rfl⟩ : syracuseStep 929883 = 1394825) B1394825
theorem B995495 : Blo 928581 995495 := bstep (se 1 (by rfl) ⟨746621, by rfl⟩ : syracuseStep 995495 = 1493243) B1493243
theorem B6041897 : Blo 928581 6041897 := bstep (se 2 (by rfl) ⟨2265711, by rfl⟩ : syracuseStep 6041897 = 4531423) B4531423
theorem B930271 : Blo 928581 930271 := bstep (se 1 (by rfl) ⟨697703, by rfl⟩ : syracuseStep 930271 = 1395407) B1395407
theorem B930395 : Blo 928581 930395 := bstep (se 1 (by rfl) ⟨697796, by rfl⟩ : syracuseStep 930395 = 1395593) B1395593
theorem B1323631 : Blo 928581 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B10761659 : Blo 928581 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B931295 : Blo 928581 931295 := bstep (se 1 (by rfl) ⟨698471, by rfl⟩ : syracuseStep 931295 = 1396943) B1396943
theorem B931375 : Blo 928581 931375 := bstep (se 1 (by rfl) ⟨698531, by rfl⟩ : syracuseStep 931375 = 1397063) B1397063
theorem B13252423 : Blo 928581 13252423 := bstep (se 1 (by rfl) ⟨9939317, by rfl⟩ : syracuseStep 13252423 = 19878635) B19878635
theorem B931967 : Blo 928581 931967 := bstep (se 1 (by rfl) ⟨698975, by rfl⟩ : syracuseStep 931967 = 1397951) B1397951
theorem B6371795 : Blo 928581 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B3357865 : Blo 928581 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B16105067 : Blo 928581 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B16334635 : Blo 928581 16334635 := bstep (se 1 (by rfl) ⟨12250976, by rfl⟩ : syracuseStep 16334635 = 24501953) B24501953
theorem B30228713 : Blo 928581 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B5292449 : Blo 928581 5292449 := bstep (se 2 (by rfl) ⟨1984668, by rfl⟩ : syracuseStep 5292449 = 3969337) B3969337
theorem B1393319 : Blo 928581 1393319 := bstep (se 1 (by rfl) ⟨1044989, by rfl⟩ : syracuseStep 1393319 = 2089979) B2089979
theorem B1393391 : Blo 928581 1393391 := bstep (se 1 (by rfl) ⟨1045043, by rfl⟩ : syracuseStep 1393391 = 2090087) B2090087
theorem B4703507 : Blo 928581 4703507 := bstep (se 1 (by rfl) ⟨3527630, by rfl⟩ : syracuseStep 4703507 = 7055261) B7055261
theorem B1394231 : Blo 928581 1394231 := bstep (se 1 (by rfl) ⟨1045673, by rfl⟩ : syracuseStep 1394231 = 2091347) B2091347
theorem B5293907 : Blo 928581 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B3360635 : Blo 928581 3360635 := bstep (se 1 (by rfl) ⟨2520476, by rfl⟩ : syracuseStep 3360635 = 5040953) B5040953
theorem B4704155 : Blo 928581 4704155 := bstep (se 1 (by rfl) ⟨3528116, by rfl⟩ : syracuseStep 4704155 = 7056233) B7056233
theorem B1395167 : Blo 928581 1395167 := bstep (se 1 (by rfl) ⟨1046375, by rfl⟩ : syracuseStep 1395167 = 2092751) B2092751
theorem B9554411 : Blo 928581 9554411 := bstep (se 1 (by rfl) ⟨7165808, by rfl⟩ : syracuseStep 9554411 = 14331617) B14331617
theorem B110152219 : Blo 928581 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B1395359 : Blo 928581 1395359 := bstep (se 1 (by rfl) ⟨1046519, by rfl⟩ : syracuseStep 1395359 = 2093039) B2093039
theorem B1395503 : Blo 928581 1395503 := bstep (se 1 (by rfl) ⟨1046627, by rfl⟩ : syracuseStep 1395503 = 2093255) B2093255
theorem B4705127 : Blo 928581 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B1985609 : Blo 928581 1985609 := bstep (se 2 (by rfl) ⟨744603, by rfl⟩ : syracuseStep 1985609 = 1489207) B1489207
theorem B1395947 : Blo 928581 1395947 := bstep (se 1 (by rfl) ⟨1046960, by rfl⟩ : syracuseStep 1395947 = 2093921) B2093921
theorem B2018771 : Blo 928581 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B1396463 : Blo 928581 1396463 := bstep (se 1 (by rfl) ⟨1047347, by rfl⟩ : syracuseStep 1396463 = 2094695) B2094695
theorem B1396649 : Blo 928581 1396649 := bstep (se 2 (by rfl) ⟨523743, by rfl⟩ : syracuseStep 1396649 = 1047487) B1047487
theorem B2511071 : Blo 928581 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B4706585 : Blo 928581 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B1397375 : Blo 928581 1397375 := bstep (se 1 (by rfl) ⟨1048031, by rfl⟩ : syracuseStep 1397375 = 2096063) B2096063
theorem B3135239 : Blo 928581 3135239 := bstep (se 1 (by rfl) ⟨2351429, by rfl⟩ : syracuseStep 3135239 = 4702859) B4702859
theorem B1988479 : Blo 928581 1988479 := bstep (se 1 (by rfl) ⟨1491359, by rfl⟩ : syracuseStep 1988479 = 2982719) B2982719
theorem B1398839 : Blo 928581 1398839 := bstep (se 1 (by rfl) ⟨1049129, by rfl⟩ : syracuseStep 1398839 = 2098259) B2098259
theorem B1890535 : Blo 928581 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B2513351 : Blo 928581 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B10738331 : Blo 928581 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B2645075 : Blo 928581 2645075 := bstep (se 1 (by rfl) ⟨1983806, by rfl⟩ : syracuseStep 2645075 = 3967613) B3967613
theorem B1989863 : Blo 928581 1989863 := bstep (se 1 (by rfl) ⟨1492397, by rfl⟩ : syracuseStep 1989863 = 2984795) B2984795
theorem B2350559 : Blo 928581 2350559 := bstep (se 1 (by rfl) ⟨1762919, by rfl⟩ : syracuseStep 2350559 = 3525839) B3525839
theorem B1990163 : Blo 928581 1990163 := bstep (se 1 (by rfl) ⟨1492622, by rfl⟩ : syracuseStep 1990163 = 2985245) B2985245
theorem B4710311 : Blo 928581 4710311 := bstep (se 1 (by rfl) ⟨3532733, by rfl⟩ : syracuseStep 4710311 = 7065467) B7065467
theorem B5660705 : Blo 928581 5660705 := bstep (se 2 (by rfl) ⟨2122764, by rfl⟩ : syracuseStep 5660705 = 4245529) B4245529
theorem B5300423 : Blo 928581 5300423 := bstep (se 1 (by rfl) ⟨3975317, by rfl⟩ : syracuseStep 5300423 = 7950635) B7950635
theorem B4710635 : Blo 928581 4710635 := bstep (se 1 (by rfl) ⟨3532976, by rfl⟩ : syracuseStep 4710635 = 7065953) B7065953
theorem B2351531 : Blo 928581 2351531 := bstep (se 1 (by rfl) ⟨1763648, by rfl⟩ : syracuseStep 2351531 = 3527297) B3527297
theorem B2351551 : Blo 928581 2351551 := bstep (se 1 (by rfl) ⟨1763663, by rfl⟩ : syracuseStep 2351551 = 3527327) B3527327
theorem B5661289 : Blo 928581 5661289 := bstep (se 2 (by rfl) ⟨2122983, by rfl⟩ : syracuseStep 5661289 = 4245967) B4245967
theorem B2089961 : Blo 928581 2089961 := bstep (se 2 (by rfl) ⟨783735, by rfl⟩ : syracuseStep 2089961 = 1567471) B1567471
theorem B2090465 : Blo 928581 2090465 := bstep (se 2 (by rfl) ⟨783924, by rfl⟩ : syracuseStep 2090465 = 1567849) B1567849
theorem B2352635 : Blo 928581 2352635 := bstep (se 1 (by rfl) ⟨1764476, by rfl⟩ : syracuseStep 2352635 = 3528953) B3528953
theorem B3139073 : Blo 928581 3139073 := bstep (se 2 (by rfl) ⟨1177152, by rfl⟩ : syracuseStep 3139073 = 2354305) B2354305
theorem B2090879 : Blo 928581 2090879 := bstep (se 1 (by rfl) ⟨1568159, by rfl⟩ : syracuseStep 2090879 = 3136319) B3136319
theorem B3532673 : Blo 928581 3532673 := bstep (se 2 (by rfl) ⟨1324752, by rfl⟩ : syracuseStep 3532673 = 2649505) B2649505
theorem B2091239 : Blo 928581 2091239 := bstep (se 1 (by rfl) ⟨1568429, by rfl⟩ : syracuseStep 2091239 = 3136859) B3136859
theorem B5302655 : Blo 928581 5302655 := bstep (se 1 (by rfl) ⟨3976991, by rfl⟩ : syracuseStep 5302655 = 7953983) B7953983
theorem B35744327 : Blo 928581 35744327 := bstep (se 1 (by rfl) ⟨26808245, by rfl⟩ : syracuseStep 35744327 = 53616491) B53616491
theorem B2091887 : Blo 928581 2091887 := bstep (se 1 (by rfl) ⟨1568915, by rfl⟩ : syracuseStep 2091887 = 3137831) B3137831
theorem B2977145 : Blo 928581 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B2092463 : Blo 928581 2092463 := bstep (se 1 (by rfl) ⟨1569347, by rfl⟩ : syracuseStep 2092463 = 3138695) B3138695
theorem B9563603 : Blo 928581 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B18345473 : Blo 928581 18345473 := bstep (se 2 (by rfl) ⟨6879552, by rfl⟩ : syracuseStep 18345473 = 13759105) B13759105
theorem B2092571 : Blo 928581 2092571 := bstep (se 1 (by rfl) ⟨1569428, by rfl⟩ : syracuseStep 2092571 = 3138857) B3138857
theorem B2649631 : Blo 928581 2649631 := bstep (se 1 (by rfl) ⟨1987223, by rfl⟩ : syracuseStep 2649631 = 3974447) B3974447
theorem B85814963 : Blo 928581 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B2354953 : Blo 928581 2354953 := bstep (se 2 (by rfl) ⟨883107, by rfl⟩ : syracuseStep 2354953 = 1766215) B1766215
theorem B2355419 : Blo 928581 2355419 := bstep (se 1 (by rfl) ⟨1766564, by rfl⟩ : syracuseStep 2355419 = 3533129) B3533129
theorem B1569307 : Blo 928581 1569307 := bstep (se 1 (by rfl) ⟨1176980, by rfl⟩ : syracuseStep 1569307 = 2353961) B2353961
theorem B1045039 : Blo 928581 1045039 := bstep (se 1 (by rfl) ⟨783779, by rfl⟩ : syracuseStep 1045039 = 1567559) B1567559
theorem B9532075 : Blo 928581 9532075 := bstep (se 1 (by rfl) ⟨7149056, by rfl⟩ : syracuseStep 9532075 = 14298113) B14298113
theorem B4715657 : Blo 928581 4715657 := bstep (se 2 (by rfl) ⟨1768371, by rfl⟩ : syracuseStep 4715657 = 3536743) B3536743
theorem B3142907 : Blo 928581 3142907 := bstep (se 1 (by rfl) ⟨2357180, by rfl⟩ : syracuseStep 3142907 = 4714361) B4714361
theorem B5305823 : Blo 928581 5305823 := bstep (se 1 (by rfl) ⟨3979367, by rfl⟩ : syracuseStep 5305823 = 7958735) B7958735
theorem B2094569 : Blo 928581 2094569 := bstep (se 2 (by rfl) ⟨785463, by rfl⟩ : syracuseStep 2094569 = 1570927) B1570927
theorem B2520649 : Blo 928581 2520649 := bstep (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) B1890487
theorem B2094767 : Blo 928581 2094767 := bstep (se 1 (by rfl) ⟨1571075, by rfl⟩ : syracuseStep 2094767 = 3142151) B3142151
theorem B1767271 : Blo 928581 1767271 := bstep (se 1 (by rfl) ⟨1325453, by rfl⟩ : syracuseStep 1767271 = 2650907) B2650907
theorem B2095073 : Blo 928581 2095073 := bstep (se 2 (by rfl) ⟨785652, by rfl⟩ : syracuseStep 2095073 = 1571305) B1571305
theorem B2095379 : Blo 928581 2095379 := bstep (se 1 (by rfl) ⟨1571534, by rfl⟩ : syracuseStep 2095379 = 3143069) B3143069
theorem B9566531 : Blo 928581 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B1046911 : Blo 928581 1046911 := bstep (se 1 (by rfl) ⟨785183, by rfl⟩ : syracuseStep 1046911 = 1570367) B1570367
theorem B2095487 : Blo 928581 2095487 := bstep (se 1 (by rfl) ⟨1571615, by rfl⟩ : syracuseStep 2095487 = 3143231) B3143231
theorem B4848295 : Blo 928581 4848295 := bstep (se 1 (by rfl) ⟨3636221, by rfl⟩ : syracuseStep 4848295 = 7272443) B7272443
theorem B3177143 : Blo 928581 3177143 := bstep (se 1 (by rfl) ⟨2382857, by rfl⟩ : syracuseStep 3177143 = 4765715) B4765715
theorem B1572007 : Blo 928581 1572007 := bstep (se 1 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 1572007 = 2358011) B2358011
theorem B7175479 : Blo 928581 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B2096441 : Blo 928581 2096441 := bstep (se 2 (by rfl) ⟨786165, by rfl⟩ : syracuseStep 2096441 = 1572331) B1572331
theorem B40205807 : Blo 928581 40205807 := bstep (se 1 (by rfl) ⟨30154355, by rfl⟩ : syracuseStep 40205807 = 60308711) B60308711
theorem B4587005 : Blo 928581 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B2096711 : Blo 928581 2096711 := bstep (se 1 (by rfl) ⟨1572533, by rfl⟩ : syracuseStep 2096711 = 3145067) B3145067
theorem B20152475 : Blo 928581 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B620527837 : Blo 928581 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B10617155 : Blo 928581 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B4719059 : Blo 928581 4719059 := bstep (se 1 (by rfl) ⟨3539294, by rfl⟩ : syracuseStep 4719059 = 7078589) B7078589
theorem B32211769 : Blo 928581 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B3146579 : Blo 928581 3146579 := bstep (se 1 (by rfl) ⟨2359934, by rfl⟩ : syracuseStep 3146579 = 4719869) B4719869
theorem B3146633 : Blo 928581 3146633 := bstep (se 2 (by rfl) ⟨1179987, by rfl⟩ : syracuseStep 3146633 = 2359975) B2359975
theorem B7079561 : Blo 928581 7079561 := bstep (se 2 (by rfl) ⟨2654835, by rfl⟩ : syracuseStep 7079561 = 5309671) B5309671
theorem B10618613 : Blo 928581 10618613 := bstep (se 5 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 10618613 = 995495) B995495
theorem B4720679 : Blo 928581 4720679 := bstep (se 1 (by rfl) ⟨3540509, by rfl⟩ : syracuseStep 4720679 = 7081019) B7081019
theorem B1345847 : Blo 928581 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B1674047 : Blo 928581 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B146869625 : Blo 928581 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B1675567 : Blo 928581 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B15930107 : Blo 928581 15930107 := bstep (se 1 (by rfl) ⟨11947580, by rfl⟩ : syracuseStep 15930107 = 23895161) B23895161
theorem B3773803 : Blo 928581 3773803 := bstep (se 1 (by rfl) ⟨2830352, by rfl⟩ : syracuseStep 3773803 = 5660705) B5660705
theorem B4463257 : Blo 928581 4463257 := bstep (se 2 (by rfl) ⟨1673721, by rfl⟩ : syracuseStep 4463257 = 3347443) B3347443
theorem B23829551 : Blo 928581 23829551 := bstep (se 1 (by rfl) ⟨17872163, by rfl⟩ : syracuseStep 23829551 = 35744327) B35744327
theorem B85859615 : Blo 928581 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B12230315 : Blo 928581 12230315 := bstep (se 1 (by rfl) ⟨9172736, by rfl⟩ : syracuseStep 12230315 = 18345473) B18345473
theorem B17669897 : Blo 928581 17669897 := bstep (se 2 (by rfl) ⟨6626211, by rfl⟩ : syracuseStep 17669897 = 13252423) B13252423
theorem B6464393 : Blo 928581 6464393 := bstep (se 2 (by rfl) ⟨2424147, by rfl⟩ : syracuseStep 6464393 = 4848295) B4848295
theorem B25502941 : Blo 928581 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B3058003 : Blo 928581 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B928879 : Blo 928581 928879 := bstep (se 1 (by rfl) ⟨696659, by rfl⟩ : syracuseStep 928879 = 1393319) B1393319
theorem B15903863 : Blo 928581 15903863 := bstep (se 1 (by rfl) ⟨11927897, by rfl⟩ : syracuseStep 15903863 = 23855795) B23855795
theorem B928927 : Blo 928581 928927 := bstep (se 1 (by rfl) ⟨696695, by rfl⟩ : syracuseStep 928927 = 1393391) B1393391
theorem B7548385 : Blo 928581 7548385 := bstep (se 2 (by rfl) ⟨2830644, by rfl⟩ : syracuseStep 7548385 = 5661289) B5661289
theorem B929487 : Blo 928581 929487 := bstep (se 1 (by rfl) ⟨697115, by rfl⟩ : syracuseStep 929487 = 1394231) B1394231
theorem B2240423 : Blo 928581 2240423 := bstep (se 1 (by rfl) ⟨1680317, by rfl⟩ : syracuseStep 2240423 = 3360635) B3360635
theorem B930111 : Blo 928581 930111 := bstep (se 1 (by rfl) ⟨697583, by rfl⟩ : syracuseStep 930111 = 1395167) B1395167
theorem B6369607 : Blo 928581 6369607 := bstep (se 1 (by rfl) ⟨4777205, by rfl⟩ : syracuseStep 6369607 = 9554411) B9554411
theorem B930239 : Blo 928581 930239 := bstep (se 1 (by rfl) ⟨697679, by rfl⟩ : syracuseStep 930239 = 1395359) B1395359
theorem B930335 : Blo 928581 930335 := bstep (se 1 (by rfl) ⟨697751, by rfl⟩ : syracuseStep 930335 = 1395503) B1395503
theorem B1323739 : Blo 928581 1323739 := bstep (se 1 (by rfl) ⟨992804, by rfl⟩ : syracuseStep 1323739 = 1985609) B1985609
theorem B930631 : Blo 928581 930631 := bstep (se 1 (by rfl) ⟨697973, by rfl⟩ : syracuseStep 930631 = 1395947) B1395947
theorem B930975 : Blo 928581 930975 := bstep (se 1 (by rfl) ⟨698231, by rfl⟩ : syracuseStep 930975 = 1396463) B1396463
theorem B931099 : Blo 928581 931099 := bstep (se 1 (by rfl) ⟨698324, by rfl⟩ : syracuseStep 931099 = 1396649) B1396649
theorem B11318879 : Blo 928581 11318879 := bstep (se 1 (by rfl) ⟨8489159, by rfl⟩ : syracuseStep 11318879 = 16978319) B16978319
theorem B931583 : Blo 928581 931583 := bstep (se 1 (by rfl) ⟨698687, by rfl⟩ : syracuseStep 931583 = 1397375) B1397375
theorem B932559 : Blo 928581 932559 := bstep (se 1 (by rfl) ⟨699419, by rfl⟩ : syracuseStep 932559 = 1398839) B1398839
theorem B7158887 : Blo 928581 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B11320631 : Blo 928581 11320631 := bstep (se 1 (by rfl) ⟨8490473, by rfl⟩ : syracuseStep 11320631 = 16980947) B16980947
theorem B1326575 : Blo 928581 1326575 := bstep (se 1 (by rfl) ⟨994931, by rfl⟩ : syracuseStep 1326575 = 1989863) B1989863
theorem B3980819 : Blo 928581 3980819 := bstep (se 1 (by rfl) ⟨2985614, by rfl⟩ : syracuseStep 3980819 = 5971229) B5971229
theorem B1326775 : Blo 928581 1326775 := bstep (se 1 (by rfl) ⟨995081, by rfl⟩ : syracuseStep 1326775 = 1990163) B1990163
theorem B1393307 : Blo 928581 1393307 := bstep (se 1 (by rfl) ⟨1044980, by rfl⟩ : syracuseStep 1393307 = 2089961) B2089961
theorem B1393385 : Blo 928581 1393385 := bstep (se 2 (by rfl) ⟨522519, by rfl⟩ : syracuseStep 1393385 = 1045039) B1045039
theorem B17908613 : Blo 928581 17908613 := bstep (se 4 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 17908613 = 3357865) B3357865
theorem B1393643 : Blo 928581 1393643 := bstep (se 1 (by rfl) ⟨1045232, by rfl⟩ : syracuseStep 1393643 = 2090465) B2090465
theorem B16991453 : Blo 928581 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B1393919 : Blo 928581 1393919 := bstep (se 1 (by rfl) ⟨1045439, by rfl⟩ : syracuseStep 1393919 = 2090879) B2090879
theorem B1394159 : Blo 928581 1394159 := bstep (se 1 (by rfl) ⟨1045619, by rfl⟩ : syracuseStep 1394159 = 2091239) B2091239
theorem B1394591 : Blo 928581 1394591 := bstep (se 1 (by rfl) ⟨1045943, by rfl⟩ : syracuseStep 1394591 = 2091887) B2091887
theorem B3360865 : Blo 928581 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B1984763 : Blo 928581 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B1394975 : Blo 928581 1394975 := bstep (se 1 (by rfl) ⟨1046231, by rfl⟩ : syracuseStep 1394975 = 2092463) B2092463
theorem B1395047 : Blo 928581 1395047 := bstep (se 1 (by rfl) ⟨1046285, by rfl⟩ : syracuseStep 1395047 = 2092571) B2092571
theorem B1395881 : Blo 928581 1395881 := bstep (se 2 (by rfl) ⟨523455, by rfl⟩ : syracuseStep 1395881 = 1046911) B1046911
theorem B1396379 : Blo 928581 1396379 := bstep (se 1 (by rfl) ⟨1047284, by rfl⟩ : syracuseStep 1396379 = 2094569) B2094569
theorem B1396511 : Blo 928581 1396511 := bstep (se 1 (by rfl) ⟨1047383, by rfl⟩ : syracuseStep 1396511 = 2094767) B2094767
theorem B1396715 : Blo 928581 1396715 := bstep (se 1 (by rfl) ⟨1047536, by rfl⟩ : syracuseStep 1396715 = 2095073) B2095073
theorem B1396919 : Blo 928581 1396919 := bstep (se 1 (by rfl) ⟨1047689, by rfl⟩ : syracuseStep 1396919 = 2095379) B2095379
theorem B6377687 : Blo 928581 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B1396991 : Blo 928581 1396991 := bstep (se 1 (by rfl) ⟨1047743, by rfl⟩ : syracuseStep 1396991 = 2095487) B2095487
theorem B2118095 : Blo 928581 2118095 := bstep (se 1 (by rfl) ⟨1588571, by rfl⟩ : syracuseStep 2118095 = 3177143) B3177143
theorem B1397627 : Blo 928581 1397627 := bstep (se 1 (by rfl) ⟨1048220, by rfl⟩ : syracuseStep 1397627 = 2096441) B2096441
theorem B1397807 : Blo 928581 1397807 := bstep (se 1 (by rfl) ⟨1048355, by rfl⟩ : syracuseStep 1397807 = 2096711) B2096711
theorem B21779513 : Blo 928581 21779513 := bstep (se 2 (by rfl) ⟨8167317, by rfl⟩ : syracuseStep 21779513 = 16334635) B16334635
theorem B10736711 : Blo 928581 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B51533171 : Blo 928581 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B1398251 : Blo 928581 1398251 := bstep (se 1 (by rfl) ⟨1048688, by rfl⟩ : syracuseStep 1398251 = 2097377) B2097377
theorem B3528299 : Blo 928581 3528299 := bstep (se 1 (by rfl) ⟨2646224, by rfl⟩ : syracuseStep 3528299 = 5292449) B5292449
theorem B1398695 : Blo 928581 1398695 := bstep (se 1 (by rfl) ⟨1049021, by rfl⟩ : syracuseStep 1398695 = 2098043) B2098043
theorem B3135401 : Blo 928581 3135401 := bstep (se 2 (by rfl) ⟨1175775, by rfl⟩ : syracuseStep 3135401 = 2351551) B2351551
theorem B3135671 : Blo 928581 3135671 := bstep (se 1 (by rfl) ⟨2351753, by rfl⟩ : syracuseStep 3135671 = 4703507) B4703507
theorem B3529271 : Blo 928581 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B3136103 : Blo 928581 3136103 := bstep (se 1 (by rfl) ⟨2352077, by rfl⟩ : syracuseStep 3136103 = 4704155) B4704155
theorem B12409805 : Blo 928581 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B3136751 : Blo 928581 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B3137723 : Blo 928581 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B5038985 : Blo 928581 5038985 := bstep (se 2 (by rfl) ⟨1889619, by rfl⟩ : syracuseStep 5038985 = 3779239) B3779239
theorem B2090159 : Blo 928581 2090159 := bstep (se 1 (by rfl) ⟨1567619, by rfl⟩ : syracuseStep 2090159 = 3135239) B3135239
theorem B2123167 : Blo 928581 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B22603313 : Blo 928581 22603313 := bstep (se 2 (by rfl) ⟨8476242, by rfl⟩ : syracuseStep 22603313 = 16952485) B16952485
theorem B1763041 : Blo 928581 1763041 := bstep (se 2 (by rfl) ⟨661140, by rfl⟩ : syracuseStep 1763041 = 1322281) B1322281
theorem B3532841 : Blo 928581 3532841 := bstep (se 2 (by rfl) ⟨1324815, by rfl⟩ : syracuseStep 3532841 = 2649631) B2649631
theorem B1763383 : Blo 928581 1763383 := bstep (se 1 (by rfl) ⟨1322537, by rfl⟩ : syracuseStep 1763383 = 2645075) B2645075
theorem B1567039 : Blo 928581 1567039 := bstep (se 1 (by rfl) ⟨1175279, by rfl⟩ : syracuseStep 1567039 = 2350559) B2350559
theorem B3139937 : Blo 928581 3139937 := bstep (se 2 (by rfl) ⟨1177476, by rfl⟩ : syracuseStep 3139937 = 2354953) B2354953
theorem B9660799 : Blo 928581 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B13593095 : Blo 928581 13593095 := bstep (se 1 (by rfl) ⟨10194821, by rfl⟩ : syracuseStep 13593095 = 20389643) B20389643
theorem B3140207 : Blo 928581 3140207 := bstep (se 1 (by rfl) ⟨2355155, by rfl⟩ : syracuseStep 3140207 = 4710311) B4710311
theorem B3533615 : Blo 928581 3533615 := bstep (se 1 (by rfl) ⟨2650211, by rfl⟩ : syracuseStep 3533615 = 5300423) B5300423
theorem B3140423 : Blo 928581 3140423 := bstep (se 1 (by rfl) ⟨2355317, by rfl⟩ : syracuseStep 3140423 = 4710635) B4710635
theorem B1567687 : Blo 928581 1567687 := bstep (se 1 (by rfl) ⟨1175765, by rfl⟩ : syracuseStep 1567687 = 2351531) B2351531
theorem B2092409 : Blo 928581 2092409 := bstep (se 2 (by rfl) ⟨784653, by rfl⟩ : syracuseStep 2092409 = 1569307) B1569307
theorem B1764841 : Blo 928581 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B12709433 : Blo 928581 12709433 := bstep (se 2 (by rfl) ⟨4766037, by rfl⟩ : syracuseStep 12709433 = 9532075) B9532075
theorem B22638143 : Blo 928581 22638143 := bstep (se 1 (by rfl) ⟨16978607, by rfl⟩ : syracuseStep 22638143 = 33957215) B33957215
theorem B1568423 : Blo 928581 1568423 := bstep (se 1 (by rfl) ⟨1176317, by rfl⟩ : syracuseStep 1568423 = 2352635) B2352635
theorem B2092715 : Blo 928581 2092715 := bstep (se 1 (by rfl) ⟨1569536, by rfl⟩ : syracuseStep 2092715 = 3139073) B3139073
theorem B2355115 : Blo 928581 2355115 := bstep (se 1 (by rfl) ⟨1766336, by rfl⟩ : syracuseStep 2355115 = 3532673) B3532673
theorem B3535103 : Blo 928581 3535103 := bstep (se 1 (by rfl) ⟨2651327, by rfl⟩ : syracuseStep 3535103 = 5302655) B5302655
theorem B2650781 : Blo 928581 2650781 := bstep (se 3 (by rfl) ⟨497021, by rfl⟩ : syracuseStep 2650781 = 994043) B994043
theorem B2651123 : Blo 928581 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B29389853 : Blo 928581 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B57209975 : Blo 928581 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B2356361 : Blo 928581 2356361 := bstep (se 2 (by rfl) ⟨883635, by rfl⟩ : syracuseStep 2356361 = 1767271) B1767271
theorem B2651305 : Blo 928581 2651305 := bstep (se 2 (by rfl) ⟨994239, by rfl⟩ : syracuseStep 2651305 = 1988479) B1988479
theorem B1570279 : Blo 928581 1570279 := bstep (se 1 (by rfl) ⟨1177709, by rfl⟩ : syracuseStep 1570279 = 2355419) B2355419
theorem B4027931 : Blo 928581 4027931 := bstep (se 1 (by rfl) ⟨3020948, by rfl⟩ : syracuseStep 4027931 = 6041897) B6041897
theorem B2520713 : Blo 928581 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B3143771 : Blo 928581 3143771 := bstep (se 1 (by rfl) ⟨2357828, by rfl⟩ : syracuseStep 3143771 = 4715657) B4715657
theorem B2095271 : Blo 928581 2095271 := bstep (se 1 (by rfl) ⟨1571453, by rfl⟩ : syracuseStep 2095271 = 3142907) B3142907
theorem B7174439 : Blo 928581 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B3537215 : Blo 928581 3537215 := bstep (se 1 (by rfl) ⟨2652911, by rfl⟩ : syracuseStep 3537215 = 5305823) B5305823
theorem B2096009 : Blo 928581 2096009 := bstep (se 2 (by rfl) ⟨786003, by rfl⟩ : syracuseStep 2096009 = 1572007) B1572007
theorem B9567305 : Blo 928581 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B26803871 : Blo 928581 26803871 := bstep (se 1 (by rfl) ⟨20102903, by rfl⟩ : syracuseStep 26803871 = 40205807) B40205807
theorem B13434983 : Blo 928581 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B7078103 : Blo 928581 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B3146039 : Blo 928581 3146039 := bstep (se 1 (by rfl) ⟨2359529, by rfl⟩ : syracuseStep 3146039 = 4719059) B4719059
theorem B2097719 : Blo 928581 2097719 := bstep (se 1 (by rfl) ⟨1573289, by rfl⟩ : syracuseStep 2097719 = 3146579) B3146579
theorem B2097755 : Blo 928581 2097755 := bstep (se 1 (by rfl) ⟨1573316, by rfl⟩ : syracuseStep 2097755 = 3146633) B3146633
theorem B4719707 : Blo 928581 4719707 := bstep (se 1 (by rfl) ⟨3539780, by rfl⟩ : syracuseStep 4719707 = 7079561) B7079561
theorem B7079075 : Blo 928581 7079075 := bstep (se 1 (by rfl) ⟨5309306, by rfl⟩ : syracuseStep 7079075 = 10618613) B10618613
theorem B3147119 : Blo 928581 3147119 := bstep (se 1 (by rfl) ⟨2360339, by rfl⟩ : syracuseStep 3147119 = 4720679) B4720679
theorem B1116031 : Blo 928581 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B97913083 : Blo 928581 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B1412063 : Blo 928581 1412063 := bstep (se 1 (by rfl) ⟨1059047, by rfl⟩ : syracuseStep 1412063 = 2118095) B2118095
theorem B10620071 : Blo 928581 10620071 := bstep (se 1 (by rfl) ⟨7965053, by rfl⟩ : syracuseStep 10620071 = 15930107) B15930107
theorem B12881065 : Blo 928581 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B14355701 : Blo 928581 14355701 := bstep (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) B1345847
theorem B14519675 : Blo 928581 14519675 := bstep (se 1 (by rfl) ⟨10889756, by rfl⟩ : syracuseStep 14519675 = 21779513) B21779513
theorem B30183677 : Blo 928581 30183677 := bstep (se 3 (by rfl) ⟨5659439, by rfl⟩ : syracuseStep 30183677 = 11318879) B11318879
theorem B10064513 : Blo 928581 10064513 := bstep (se 2 (by rfl) ⟨3774192, by rfl⟩ : syracuseStep 10064513 = 7548385) B7548385
theorem B2234089 : Blo 928581 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B8492809 : Blo 928581 8492809 := bstep (se 2 (by rfl) ⟨3184803, by rfl⟩ : syracuseStep 8492809 = 6369607) B6369607
theorem B1680475 : Blo 928581 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B33891821 : Blo 928581 33891821 := bstep (se 3 (by rfl) ⟨6354716, by rfl⟩ : syracuseStep 33891821 = 12709433) B12709433
theorem B7547087 : Blo 928581 7547087 := bstep (se 1 (by rfl) ⟨5660315, by rfl⟩ : syracuseStep 7547087 = 11320631) B11320631
theorem B17869247 : Blo 928581 17869247 := bstep (se 1 (by rfl) ⟨13401935, by rfl⟩ : syracuseStep 17869247 = 26803871) B26803871
theorem B827370449 : Blo 928581 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B928871 : Blo 928581 928871 := bstep (se 1 (by rfl) ⟨696653, by rfl⟩ : syracuseStep 928871 = 1393307) B1393307
theorem B928923 : Blo 928581 928923 := bstep (se 1 (by rfl) ⟨696692, by rfl⟩ : syracuseStep 928923 = 1393385) B1393385
theorem B11939075 : Blo 928581 11939075 := bstep (se 1 (by rfl) ⟨8954306, by rfl⟩ : syracuseStep 11939075 = 17908613) B17908613
theorem B929095 : Blo 928581 929095 := bstep (se 1 (by rfl) ⟨696821, by rfl⟩ : syracuseStep 929095 = 1393643) B1393643
theorem B929279 : Blo 928581 929279 := bstep (se 1 (by rfl) ⟨696959, by rfl⟩ : syracuseStep 929279 = 1393919) B1393919
theorem B929439 : Blo 928581 929439 := bstep (se 1 (by rfl) ⟨697079, by rfl⟩ : syracuseStep 929439 = 1394159) B1394159
theorem B929727 : Blo 928581 929727 := bstep (se 1 (by rfl) ⟨697295, by rfl⟩ : syracuseStep 929727 = 1394591) B1394591
theorem B929983 : Blo 928581 929983 := bstep (se 1 (by rfl) ⟨697487, by rfl⟩ : syracuseStep 929983 = 1394975) B1394975
theorem B930031 : Blo 928581 930031 := bstep (se 1 (by rfl) ⟨697523, by rfl⟩ : syracuseStep 930031 = 1395047) B1395047
theorem B2830889 : Blo 928581 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B930587 : Blo 928581 930587 := bstep (se 1 (by rfl) ⟨697940, by rfl⟩ : syracuseStep 930587 = 1395881) B1395881
theorem B930919 : Blo 928581 930919 := bstep (se 1 (by rfl) ⟨698189, by rfl⟩ : syracuseStep 930919 = 1396379) B1396379
theorem B931007 : Blo 928581 931007 := bstep (se 1 (by rfl) ⟨698255, by rfl⟩ : syracuseStep 931007 = 1396511) B1396511
theorem B931143 : Blo 928581 931143 := bstep (se 1 (by rfl) ⟨698357, by rfl⟩ : syracuseStep 931143 = 1396715) B1396715
theorem B931279 : Blo 928581 931279 := bstep (se 1 (by rfl) ⟨698459, by rfl⟩ : syracuseStep 931279 = 1396919) B1396919
theorem B931327 : Blo 928581 931327 := bstep (se 1 (by rfl) ⟨698495, by rfl⟩ : syracuseStep 931327 = 1396991) B1396991
theorem B931751 : Blo 928581 931751 := bstep (se 1 (by rfl) ⟨698813, by rfl⟩ : syracuseStep 931751 = 1397627) B1397627
theorem B931871 : Blo 928581 931871 := bstep (se 1 (by rfl) ⟨698903, by rfl⟩ : syracuseStep 931871 = 1397807) B1397807
theorem B7157807 : Blo 928581 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B34355447 : Blo 928581 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B932167 : Blo 928581 932167 := bstep (se 1 (by rfl) ⟨699125, by rfl⟩ : syracuseStep 932167 = 1398251) B1398251
theorem B932463 : Blo 928581 932463 := bstep (se 1 (by rfl) ⟨699347, by rfl⟩ : syracuseStep 932463 = 1398695) B1398695
theorem B11779931 : Blo 928581 11779931 := bstep (se 1 (by rfl) ⟨8834948, by rfl⟩ : syracuseStep 11779931 = 17669897) B17669897
theorem B4309595 : Blo 928581 4309595 := bstep (se 1 (by rfl) ⟨3232196, by rfl⟩ : syracuseStep 4309595 = 6464393) B6464393
theorem B3359323 : Blo 928581 3359323 := bstep (se 1 (by rfl) ⟨2519492, by rfl⟩ : syracuseStep 3359323 = 5038985) B5038985
theorem B5292701 : Blo 928581 5292701 := bstep (se 3 (by rfl) ⟨992381, by rfl⟩ : syracuseStep 5292701 = 1984763) B1984763
theorem B1393439 : Blo 928581 1393439 := bstep (se 1 (by rfl) ⟨1045079, by rfl⟩ : syracuseStep 1393439 = 2090159) B2090159
theorem B9062063 : Blo 928581 9062063 := bstep (se 1 (by rfl) ⟨6796547, by rfl⟩ : syracuseStep 9062063 = 13593095) B13593095
theorem B5031737 : Blo 928581 5031737 := bstep (se 2 (by rfl) ⟨1886901, by rfl⟩ : syracuseStep 5031737 = 3773803) B3773803
theorem B10602575 : Blo 928581 10602575 := bstep (se 1 (by rfl) ⟨7951931, by rfl⟩ : syracuseStep 10602575 = 15903863) B15903863
theorem B1394939 : Blo 928581 1394939 := bstep (se 1 (by rfl) ⟨1046204, by rfl⟩ : syracuseStep 1394939 = 2092409) B2092409
theorem B15092095 : Blo 928581 15092095 := bstep (se 1 (by rfl) ⟨11319071, by rfl⟩ : syracuseStep 15092095 = 22638143) B22638143
theorem B1395143 : Blo 928581 1395143 := bstep (se 1 (by rfl) ⟨1046357, by rfl⟩ : syracuseStep 1395143 = 2092715) B2092715
theorem B1493615 : Blo 928581 1493615 := bstep (se 1 (by rfl) ⟨1120211, by rfl⟩ : syracuseStep 1493615 = 2240423) B2240423
theorem B5951009 : Blo 928581 5951009 := bstep (se 2 (by rfl) ⟨2231628, by rfl⟩ : syracuseStep 5951009 = 4463257) B4463257
theorem B1396847 : Blo 928581 1396847 := bstep (se 1 (by rfl) ⟨1047635, by rfl⟩ : syracuseStep 1396847 = 2095271) B2095271
theorem B1397339 : Blo 928581 1397339 := bstep (se 1 (by rfl) ⟨1048004, by rfl⟩ : syracuseStep 1397339 = 2096009) B2096009
theorem B6378203 : Blo 928581 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B4772591 : Blo 928581 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B11327635 : Blo 928581 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B42949025 : Blo 928581 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B34003921 : Blo 928581 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B16309349 : Blo 928581 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B2350721 : Blo 928581 2350721 := bstep (se 2 (by rfl) ⟨881520, by rfl⟩ : syracuseStep 2350721 = 1763041) B1763041
theorem B2351177 : Blo 928581 2351177 := bstep (se 2 (by rfl) ⟨881691, by rfl⟩ : syracuseStep 2351177 = 1763383) B1763383
theorem B4481153 : Blo 928581 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B4251791 : Blo 928581 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B2089385 : Blo 928581 2089385 := bstep (se 2 (by rfl) ⟨783519, by rfl⟩ : syracuseStep 2089385 = 1567039) B1567039
theorem B2352199 : Blo 928581 2352199 := bstep (se 1 (by rfl) ⟨1764149, by rfl⟩ : syracuseStep 2352199 = 3528299) B3528299
theorem B2090249 : Blo 928581 2090249 := bstep (se 2 (by rfl) ⟨783843, by rfl⟩ : syracuseStep 2090249 = 1567687) B1567687
theorem B2090267 : Blo 928581 2090267 := bstep (se 1 (by rfl) ⟨1567700, by rfl⟩ : syracuseStep 2090267 = 3135401) B3135401
theorem B2090447 : Blo 928581 2090447 := bstep (se 1 (by rfl) ⟨1567835, by rfl⟩ : syracuseStep 2090447 = 3135671) B3135671
theorem B2352847 : Blo 928581 2352847 := bstep (se 1 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 2352847 = 3529271) B3529271
theorem B2090735 : Blo 928581 2090735 := bstep (se 1 (by rfl) ⟨1568051, by rfl⟩ : syracuseStep 2090735 = 3136103) B3136103
theorem B2353121 : Blo 928581 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B15886367 : Blo 928581 15886367 := bstep (se 1 (by rfl) ⟨11914775, by rfl⟩ : syracuseStep 15886367 = 23829551) B23829551
theorem B2091167 : Blo 928581 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B57239743 : Blo 928581 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B8153543 : Blo 928581 8153543 := bstep (se 1 (by rfl) ⟨6115157, by rfl⟩ : syracuseStep 8153543 = 12230315) B12230315
theorem B3140153 : Blo 928581 3140153 := bstep (se 2 (by rfl) ⟨1177557, by rfl⟩ : syracuseStep 3140153 = 2355115) B2355115
theorem B2091815 : Blo 928581 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B1764985 : Blo 928581 1764985 := bstep (se 2 (by rfl) ⟨661869, by rfl⟩ : syracuseStep 1764985 = 1323739) B1323739
theorem B15068875 : Blo 928581 15068875 := bstep (se 1 (by rfl) ⟨11301656, by rfl⟩ : syracuseStep 15068875 = 22603313) B22603313
theorem B2355227 : Blo 928581 2355227 := bstep (se 1 (by rfl) ⟨1766420, by rfl⟩ : syracuseStep 2355227 = 3532841) B3532841
theorem B3535073 : Blo 928581 3535073 := bstep (se 2 (by rfl) ⟨1325652, by rfl⟩ : syracuseStep 3535073 = 2651305) B2651305
theorem B2093291 : Blo 928581 2093291 := bstep (se 1 (by rfl) ⟨1569968, by rfl⟩ : syracuseStep 2093291 = 3139937) B3139937
theorem B2093471 : Blo 928581 2093471 := bstep (se 1 (by rfl) ⟨1570103, by rfl⟩ : syracuseStep 2093471 = 3140207) B3140207
theorem B2355743 : Blo 928581 2355743 := bstep (se 1 (by rfl) ⟨1766807, by rfl⟩ : syracuseStep 2355743 = 3533615) B3533615
theorem B2093615 : Blo 928581 2093615 := bstep (se 1 (by rfl) ⟨1570211, by rfl⟩ : syracuseStep 2093615 = 3140423) B3140423
theorem B2093705 : Blo 928581 2093705 := bstep (se 2 (by rfl) ⟨785139, by rfl⟩ : syracuseStep 2093705 = 1570279) B1570279
theorem B1045615 : Blo 928581 1045615 := bstep (se 1 (by rfl) ⟨784211, by rfl⟩ : syracuseStep 1045615 = 1568423) B1568423
theorem B33092813 : Blo 928581 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B2356735 : Blo 928581 2356735 := bstep (se 1 (by rfl) ⟨1767551, by rfl⟩ : syracuseStep 2356735 = 3535103) B3535103
theorem B1767187 : Blo 928581 1767187 := bstep (se 1 (by rfl) ⟨1325390, by rfl⟩ : syracuseStep 1767187 = 2650781) B2650781
theorem B1767415 : Blo 928581 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B19593235 : Blo 928581 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B38139983 : Blo 928581 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B1570907 : Blo 928581 1570907 := bstep (se 1 (by rfl) ⟨1178180, by rfl⟩ : syracuseStep 1570907 = 2356361) B2356361
theorem B2685287 : Blo 928581 2685287 := bstep (se 1 (by rfl) ⟨2013965, by rfl⟩ : syracuseStep 2685287 = 4027931) B4027931
theorem B3537533 : Blo 928581 3537533 := bstep (se 3 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 3537533 = 1326575) B1326575
theorem B2095847 : Blo 928581 2095847 := bstep (se 1 (by rfl) ⟨1571885, by rfl⟩ : syracuseStep 2095847 = 3143771) B3143771
theorem B4782959 : Blo 928581 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B2358143 : Blo 928581 2358143 := bstep (se 1 (by rfl) ⟨1768607, by rfl⟩ : syracuseStep 2358143 = 3537215) B3537215
theorem B1769033 : Blo 928581 1769033 := bstep (se 2 (by rfl) ⟨663387, by rfl⟩ : syracuseStep 1769033 = 1326775) B1326775
theorem B2653879 : Blo 928581 2653879 := bstep (se 1 (by rfl) ⟨1990409, by rfl⟩ : syracuseStep 2653879 = 3980819) B3980819
theorem B104497253 : Blo 928581 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B4718735 : Blo 928581 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B2097359 : Blo 928581 2097359 := bstep (se 1 (by rfl) ⟨1573019, by rfl⟩ : syracuseStep 2097359 = 3146039) B3146039
theorem B3146471 : Blo 928581 3146471 := bstep (se 1 (by rfl) ⟨2359853, by rfl⟩ : syracuseStep 3146471 = 4719707) B4719707
theorem B4719383 : Blo 928581 4719383 := bstep (se 1 (by rfl) ⟨3539537, by rfl⟩ : syracuseStep 4719383 = 7079075) B7079075
theorem B2098079 : Blo 928581 2098079 := bstep (se 1 (by rfl) ⟨1573559, by rfl⟩ : syracuseStep 2098079 = 3147119) B3147119
theorem B17008541 : Blo 928581 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B7080047 : Blo 928581 7080047 := bstep (se 1 (by rfl) ⟨5310035, by rfl⟩ : syracuseStep 7080047 = 10620071) B10620071
theorem B9570467 : Blo 928581 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B3967339 : Blo 928581 3967339 := bstep (se 1 (by rfl) ⟨2975504, by rfl⟩ : syracuseStep 3967339 = 5951009) B5951009
theorem B20122451 : Blo 928581 20122451 := bstep (se 1 (by rfl) ⟨15091838, by rfl⟩ : syracuseStep 20122451 = 30183677) B30183677
theorem B76319657 : Blo 928581 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B130550777 : Blo 928581 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B3181727 : Blo 928581 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B20122793 : Blo 928581 20122793 := bstep (se 2 (by rfl) ⟨7546047, by rfl⟩ : syracuseStep 20122793 = 15092095) B15092095
theorem B88247501 : Blo 928581 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B17174753 : Blo 928581 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B20091833 : Blo 928581 20091833 := bstep (se 2 (by rfl) ⟨7534437, by rfl⟩ : syracuseStep 20091833 = 15068875) B15068875
theorem B2987435 : Blo 928581 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B10590911 : Blo 928581 10590911 := bstep (se 1 (by rfl) ⟨7943183, by rfl⟩ : syracuseStep 10590911 = 15886367) B15886367
theorem B3188639 : Blo 928581 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B8956655 : Blo 928581 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B928959 : Blo 928581 928959 := bstep (se 1 (by rfl) ⟨696719, by rfl⟩ : syracuseStep 928959 = 1393439) B1393439
theorem B6041375 : Blo 928581 6041375 := bstep (se 1 (by rfl) ⟨4531031, by rfl⟩ : syracuseStep 6041375 = 9062063) B9062063
theorem B3354491 : Blo 928581 3354491 := bstep (se 1 (by rfl) ⟨2515868, by rfl⟩ : syracuseStep 3354491 = 5031737) B5031737
theorem B7549037 : Blo 928581 7549037 := bstep (se 3 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 7549037 = 2830889) B2830889
theorem B2240633 : Blo 928581 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B929959 : Blo 928581 929959 := bstep (se 1 (by rfl) ⟨697469, by rfl⟩ : syracuseStep 929959 = 1394939) B1394939
theorem B930095 : Blo 928581 930095 := bstep (se 1 (by rfl) ⟨697571, by rfl⟩ : syracuseStep 930095 = 1395143) B1395143
theorem B995743 : Blo 928581 995743 := bstep (se 1 (by rfl) ⟨746807, by rfl⟩ : syracuseStep 995743 = 1493615) B1493615
theorem B9679783 : Blo 928581 9679783 := bstep (se 1 (by rfl) ⟨7259837, by rfl⟩ : syracuseStep 9679783 = 14519675) B14519675
theorem B1488041 : Blo 928581 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B931231 : Blo 928581 931231 := bstep (se 1 (by rfl) ⟨698423, by rfl⟩ : syracuseStep 931231 = 1396847) B1396847
theorem B931559 : Blo 928581 931559 := bstep (se 1 (by rfl) ⟨698669, by rfl⟩ : syracuseStep 931559 = 1397339) B1397339
theorem B2834527 : Blo 928581 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B1392923 : Blo 928581 1392923 := bstep (se 1 (by rfl) ⟨1044692, by rfl⟩ : syracuseStep 1392923 = 2089385) B2089385
theorem B1393499 : Blo 928581 1393499 := bstep (se 1 (by rfl) ⟨1045124, by rfl⟩ : syracuseStep 1393499 = 2090249) B2090249
theorem B1393511 : Blo 928581 1393511 := bstep (se 1 (by rfl) ⟨1045133, by rfl⟩ : syracuseStep 1393511 = 2090267) B2090267
theorem B1393631 : Blo 928581 1393631 := bstep (se 1 (by rfl) ⟨1045223, by rfl⟩ : syracuseStep 1393631 = 2090447) B2090447
theorem B22594547 : Blo 928581 22594547 := bstep (se 1 (by rfl) ⟨16945910, by rfl⟩ : syracuseStep 22594547 = 33891821) B33891821
theorem B1393823 : Blo 928581 1393823 := bstep (se 1 (by rfl) ⟨1045367, by rfl⟩ : syracuseStep 1393823 = 2090735) B2090735
theorem B1394111 : Blo 928581 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B5031391 : Blo 928581 5031391 := bstep (se 1 (by rfl) ⟨3773543, by rfl⟩ : syracuseStep 5031391 = 7547087) B7547087
theorem B1394153 : Blo 928581 1394153 := bstep (se 2 (by rfl) ⟨522807, by rfl⟩ : syracuseStep 1394153 = 1045615) B1045615
theorem B11912831 : Blo 928581 11912831 := bstep (se 1 (by rfl) ⟨8934623, by rfl⟩ : syracuseStep 11912831 = 17869247) B17869247
theorem B1394543 : Blo 928581 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B11323745 : Blo 928581 11323745 := bstep (se 2 (by rfl) ⟨4246404, by rfl⟩ : syracuseStep 11323745 = 8492809) B8492809
theorem B1395527 : Blo 928581 1395527 := bstep (se 1 (by rfl) ⟨1046645, by rfl⟩ : syracuseStep 1395527 = 2093291) B2093291
theorem B1395647 : Blo 928581 1395647 := bstep (se 1 (by rfl) ⟨1046735, by rfl⟩ : syracuseStep 1395647 = 2093471) B2093471
theorem B1395743 : Blo 928581 1395743 := bstep (se 1 (by rfl) ⟨1046807, by rfl⟩ : syracuseStep 1395743 = 2093615) B2093615
theorem B1395803 : Blo 928581 1395803 := bstep (se 1 (by rfl) ⟨1046852, by rfl⟩ : syracuseStep 1395803 = 2093705) B2093705
theorem B45338561 : Blo 928581 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B4771871 : Blo 928581 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B1790191 : Blo 928581 1790191 := bstep (se 1 (by rfl) ⟨1342643, by rfl⟩ : syracuseStep 1790191 = 2685287) B2685287
theorem B1397231 : Blo 928581 1397231 := bstep (se 1 (by rfl) ⟨1047923, by rfl⟩ : syracuseStep 1397231 = 2095847) B2095847
theorem B7853287 : Blo 928581 7853287 := bstep (se 1 (by rfl) ⟨5889965, by rfl⟩ : syracuseStep 7853287 = 11779931) B11779931
theorem B1398479 : Blo 928581 1398479 := bstep (se 1 (by rfl) ⟨1048859, by rfl⟩ : syracuseStep 1398479 = 2097719) B2097719
theorem B2873063 : Blo 928581 2873063 := bstep (se 1 (by rfl) ⟨2154797, by rfl⟩ : syracuseStep 2873063 = 4309595) B4309595
theorem B1398503 : Blo 928581 1398503 := bstep (se 1 (by rfl) ⟨1048877, by rfl⟩ : syracuseStep 1398503 = 2097755) B2097755
theorem B3528467 : Blo 928581 3528467 := bstep (se 1 (by rfl) ⟨2646350, by rfl⟩ : syracuseStep 3528467 = 5292701) B5292701
theorem B4479097 : Blo 928581 4479097 := bstep (se 2 (by rfl) ⟨1679661, by rfl⟩ : syracuseStep 4479097 = 3359323) B3359323
theorem B7068383 : Blo 928581 7068383 := bstep (se 1 (by rfl) ⟨5301287, by rfl⟩ : syracuseStep 7068383 = 10602575) B10602575
theorem B3136265 : Blo 928581 3136265 := bstep (se 2 (by rfl) ⟨1176099, by rfl⟩ : syracuseStep 3136265 = 2352199) B2352199
theorem B941375 : Blo 928581 941375 := bstep (se 1 (by rfl) ⟨706031, by rfl⟩ : syracuseStep 941375 = 1412063) B1412063
theorem B3137129 : Blo 928581 3137129 := bstep (se 2 (by rfl) ⟨1176423, by rfl⟩ : syracuseStep 3137129 = 2352847) B2352847
theorem B6709675 : Blo 928581 6709675 := bstep (se 1 (by rfl) ⟨5032256, by rfl⟩ : syracuseStep 6709675 = 10064513) B10064513
theorem B28632683 : Blo 928581 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B10872899 : Blo 928581 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B2353313 : Blo 928581 2353313 := bstep (se 2 (by rfl) ⟨882492, by rfl⟩ : syracuseStep 2353313 = 1764985) B1764985
theorem B1567147 : Blo 928581 1567147 := bstep (se 1 (by rfl) ⟨1175360, by rfl⟩ : syracuseStep 1567147 = 2350721) B2350721
theorem B1567451 : Blo 928581 1567451 := bstep (se 1 (by rfl) ⟨1175588, by rfl⟩ : syracuseStep 1567451 = 2351177) B2351177
theorem B1568747 : Blo 928581 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B5435695 : Blo 928581 5435695 := bstep (se 1 (by rfl) ⟨4076771, by rfl⟩ : syracuseStep 5435695 = 8153543) B8153543
theorem B2093435 : Blo 928581 2093435 := bstep (se 1 (by rfl) ⟨1570076, by rfl⟩ : syracuseStep 2093435 = 3140153) B3140153
theorem B551580299 : Blo 928581 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B3142313 : Blo 928581 3142313 := bstep (se 2 (by rfl) ⟨1178367, by rfl⟩ : syracuseStep 3142313 = 2356735) B2356735
theorem B7959383 : Blo 928581 7959383 := bstep (se 1 (by rfl) ⟨5969537, by rfl⟩ : syracuseStep 7959383 = 11939075) B11939075
theorem B2978785 : Blo 928581 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B2356249 : Blo 928581 2356249 := bstep (se 2 (by rfl) ⟨883593, by rfl⟩ : syracuseStep 2356249 = 1767187) B1767187
theorem B2356553 : Blo 928581 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B1570151 : Blo 928581 1570151 := bstep (se 1 (by rfl) ⟨1177613, by rfl⟩ : syracuseStep 1570151 = 2355227) B2355227
theorem B2356715 : Blo 928581 2356715 := bstep (se 1 (by rfl) ⟨1767536, by rfl⟩ : syracuseStep 2356715 = 3535073) B3535073
theorem B15103513 : Blo 928581 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B1570495 : Blo 928581 1570495 := bstep (se 1 (by rfl) ⟨1177871, by rfl⟩ : syracuseStep 1570495 = 2355743) B2355743
theorem B25426655 : Blo 928581 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B1047271 : Blo 928581 1047271 := bstep (se 1 (by rfl) ⟨785453, by rfl⟩ : syracuseStep 1047271 = 1570907) B1570907
theorem B22903631 : Blo 928581 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B2358355 : Blo 928581 2358355 := bstep (se 1 (by rfl) ⟨1768766, by rfl⟩ : syracuseStep 2358355 = 3537533) B3537533
theorem B1572095 : Blo 928581 1572095 := bstep (se 1 (by rfl) ⟨1179071, by rfl⟩ : syracuseStep 1572095 = 2358143) B2358143
theorem B3538505 : Blo 928581 3538505 := bstep (se 2 (by rfl) ⟨1326939, by rfl⟩ : syracuseStep 3538505 = 2653879) B2653879
theorem B1179355 : Blo 928581 1179355 := bstep (se 1 (by rfl) ⟨884516, by rfl⟩ : syracuseStep 1179355 = 1769033) B1769033
theorem B69664835 : Blo 928581 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B3145823 : Blo 928581 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B2097647 : Blo 928581 2097647 := bstep (se 1 (by rfl) ⟨1573235, by rfl⟩ : syracuseStep 2097647 = 3146471) B3146471
theorem B3146255 : Blo 928581 3146255 := bstep (se 1 (by rfl) ⟨2359691, by rfl⟩ : syracuseStep 3146255 = 4719383) B4719383
theorem B8946233 : Blo 928581 8946233 := bstep (se 2 (by rfl) ⟨3354837, by rfl⟩ : syracuseStep 8946233 = 6709675) B6709675
theorem B11339027 : Blo 928581 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B4720031 : Blo 928581 4720031 := bstep (se 1 (by rfl) ⟨3540023, by rfl⟩ : syracuseStep 4720031 = 7080047) B7080047
theorem B87033851 : Blo 928581 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B5310629 : Blo 928581 5310629 := bstep (se 4 (by rfl) ⟨497871, by rfl⟩ : syracuseStep 5310629 = 995743) B995743
theorem B3181247 : Blo 928581 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B7247593 : Blo 928581 7247593 := bstep (se 2 (by rfl) ⟨2717847, by rfl⟩ : syracuseStep 7247593 = 5435695) B5435695
theorem B3971713 : Blo 928581 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B7248599 : Blo 928581 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B5971103 : Blo 928581 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B5972129 : Blo 928581 5972129 := bstep (se 2 (by rfl) ⟨2239548, by rfl⟩ : syracuseStep 5972129 = 4479097) B4479097
theorem B992027 : Blo 928581 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B16951103 : Blo 928581 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B3779369 : Blo 928581 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B928615 : Blo 928581 928615 := bstep (se 1 (by rfl) ⟨696461, by rfl⟩ : syracuseStep 928615 = 1392923) B1392923
theorem B5975021 : Blo 928581 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B928999 : Blo 928581 928999 := bstep (se 1 (by rfl) ⟨696749, by rfl⟩ : syracuseStep 928999 = 1393499) B1393499
theorem B929007 : Blo 928581 929007 := bstep (se 1 (by rfl) ⟨696755, by rfl⟩ : syracuseStep 929007 = 1393511) B1393511
theorem B929087 : Blo 928581 929087 := bstep (se 1 (by rfl) ⟨696815, by rfl⟩ : syracuseStep 929087 = 1393631) B1393631
theorem B929215 : Blo 928581 929215 := bstep (se 1 (by rfl) ⟨696911, by rfl⟩ : syracuseStep 929215 = 1393823) B1393823
theorem B929407 : Blo 928581 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B929435 : Blo 928581 929435 := bstep (se 1 (by rfl) ⟨697076, by rfl⟩ : syracuseStep 929435 = 1394153) B1394153
theorem B7941887 : Blo 928581 7941887 := bstep (se 1 (by rfl) ⟨5956415, by rfl⟩ : syracuseStep 7941887 = 11912831) B11912831
theorem B929695 : Blo 928581 929695 := bstep (se 1 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 929695 = 1394543) B1394543
theorem B7549163 : Blo 928581 7549163 := bstep (se 1 (by rfl) ⟨5661872, by rfl⟩ : syracuseStep 7549163 = 11323745) B11323745
theorem B930351 : Blo 928581 930351 := bstep (se 1 (by rfl) ⟨697763, by rfl⟩ : syracuseStep 930351 = 1395527) B1395527
theorem B13414967 : Blo 928581 13414967 := bstep (se 1 (by rfl) ⟨10061225, by rfl⟩ : syracuseStep 13414967 = 20122451) B20122451
theorem B930431 : Blo 928581 930431 := bstep (se 1 (by rfl) ⟨697823, by rfl⟩ : syracuseStep 930431 = 1395647) B1395647
theorem B930495 : Blo 928581 930495 := bstep (se 1 (by rfl) ⟨697871, by rfl⟩ : syracuseStep 930495 = 1395743) B1395743
theorem B930535 : Blo 928581 930535 := bstep (se 1 (by rfl) ⟨697901, by rfl⟩ : syracuseStep 930535 = 1395803) B1395803
theorem B13415195 : Blo 928581 13415195 := bstep (se 1 (by rfl) ⟨10061396, by rfl⟩ : syracuseStep 13415195 = 20122793) B20122793
theorem B58831667 : Blo 928581 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B30225707 : Blo 928581 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B11449835 : Blo 928581 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B931487 : Blo 928581 931487 := bstep (se 1 (by rfl) ⟨698615, by rfl⟩ : syracuseStep 931487 = 1397231) B1397231
theorem B5289785 : Blo 928581 5289785 := bstep (se 2 (by rfl) ⟨1983669, by rfl⟩ : syracuseStep 5289785 = 3967339) B3967339
theorem B932319 : Blo 928581 932319 := bstep (se 1 (by rfl) ⟨699239, by rfl⟩ : syracuseStep 932319 = 1398479) B1398479
theorem B1915375 : Blo 928581 1915375 := bstep (se 1 (by rfl) ⟨1436531, by rfl⟩ : syracuseStep 1915375 = 2873063) B2873063
theorem B932335 : Blo 928581 932335 := bstep (se 1 (by rfl) ⟨699251, by rfl⟩ : syracuseStep 932335 = 1398503) B1398503
theorem B7060607 : Blo 928581 7060607 := bstep (se 1 (by rfl) ⟨5295455, by rfl⟩ : syracuseStep 7060607 = 10590911) B10590911
theorem B19088455 : Blo 928581 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B10471049 : Blo 928581 10471049 := bstep (se 2 (by rfl) ⟨3926643, by rfl⟩ : syracuseStep 10471049 = 7853287) B7853287
theorem B20138017 : Blo 928581 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B5032691 : Blo 928581 5032691 := bstep (se 1 (by rfl) ⟨3774518, by rfl⟩ : syracuseStep 5032691 = 7549037) B7549037
theorem B1395623 : Blo 928581 1395623 := bstep (se 1 (by rfl) ⟨1046717, by rfl⟩ : syracuseStep 1395623 = 2093435) B2093435
theorem B2510333 : Blo 928581 2510333 := bstep (se 3 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 2510333 = 941375) B941375
theorem B1396361 : Blo 928581 1396361 := bstep (se 2 (by rfl) ⟨523635, by rfl⟩ : syracuseStep 1396361 = 1047271) B1047271
theorem B1398239 : Blo 928581 1398239 := bstep (se 1 (by rfl) ⟨1048679, by rfl⟩ : syracuseStep 1398239 = 2097359) B2097359
theorem B1398719 : Blo 928581 1398719 := bstep (se 1 (by rfl) ⟨1049039, by rfl⟩ : syracuseStep 1398719 = 2098079) B2098079
theorem B15063031 : Blo 928581 15063031 := bstep (se 1 (by rfl) ⟨11297273, by rfl⟩ : syracuseStep 15063031 = 22594547) B22594547
theorem B6380311 : Blo 928581 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B50879771 : Blo 928581 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B6708521 : Blo 928581 6708521 := bstep (se 2 (by rfl) ⟨2515695, by rfl⟩ : syracuseStep 6708521 = 5031391) B5031391
theorem B2121151 : Blo 928581 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B2089529 : Blo 928581 2089529 := bstep (se 2 (by rfl) ⟨783573, by rfl⟩ : syracuseStep 2089529 = 1567147) B1567147
theorem B13394555 : Blo 928581 13394555 := bstep (se 1 (by rfl) ⟨10045916, by rfl⟩ : syracuseStep 13394555 = 20091833) B20091833
theorem B1991623 : Blo 928581 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B2352311 : Blo 928581 2352311 := bstep (se 1 (by rfl) ⟨1764233, by rfl⟩ : syracuseStep 2352311 = 3528467) B3528467
theorem B4712255 : Blo 928581 4712255 := bstep (se 1 (by rfl) ⟨3534191, by rfl⟩ : syracuseStep 4712255 = 7068383) B7068383
theorem B2090843 : Blo 928581 2090843 := bstep (se 1 (by rfl) ⟨1568132, by rfl⟩ : syracuseStep 2090843 = 3136265) B3136265
theorem B2091419 : Blo 928581 2091419 := bstep (se 1 (by rfl) ⟨1568564, by rfl⟩ : syracuseStep 2091419 = 3137129) B3137129
theorem B2386921 : Blo 928581 2386921 := bstep (se 2 (by rfl) ⟨895095, by rfl⟩ : syracuseStep 2386921 = 1790191) B1790191
theorem B12906377 : Blo 928581 12906377 := bstep (se 2 (by rfl) ⟨4839891, by rfl⟩ : syracuseStep 12906377 = 9679783) B9679783
theorem B2125759 : Blo 928581 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B3141665 : Blo 928581 3141665 := bstep (se 2 (by rfl) ⟨1178124, by rfl⟩ : syracuseStep 3141665 = 2356249) B2356249
theorem B1568875 : Blo 928581 1568875 := bstep (se 1 (by rfl) ⟨1176656, by rfl⟩ : syracuseStep 1568875 = 2353313) B2353313
theorem B1044967 : Blo 928581 1044967 := bstep (se 1 (by rfl) ⟨783725, by rfl⟩ : syracuseStep 1044967 = 1567451) B1567451
theorem B2093993 : Blo 928581 2093993 := bstep (se 2 (by rfl) ⟨785247, by rfl⟩ : syracuseStep 2093993 = 1570495) B1570495
theorem B4027583 : Blo 928581 4027583 := bstep (se 1 (by rfl) ⟨3020687, by rfl⟩ : syracuseStep 4027583 = 6041375) B6041375
theorem B1045831 : Blo 928581 1045831 := bstep (se 1 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 1045831 = 1568747) B1568747
theorem B367720199 : Blo 928581 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B2094875 : Blo 928581 2094875 := bstep (se 1 (by rfl) ⟨1571156, by rfl⟩ : syracuseStep 2094875 = 3142313) B3142313
theorem B5306255 : Blo 928581 5306255 := bstep (se 1 (by rfl) ⟨3979691, by rfl⟩ : syracuseStep 5306255 = 7959383) B7959383
theorem B1571035 : Blo 928581 1571035 := bstep (se 1 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 1571035 = 2356553) B2356553
theorem B1046767 : Blo 928581 1046767 := bstep (se 1 (by rfl) ⟨785075, by rfl⟩ : syracuseStep 1046767 = 1570151) B1570151
theorem B1571143 : Blo 928581 1571143 := bstep (se 1 (by rfl) ⟨1178357, by rfl⟩ : syracuseStep 1571143 = 2356715) B2356715
theorem B3144473 : Blo 928581 3144473 := bstep (se 2 (by rfl) ⟨1179177, by rfl⟩ : syracuseStep 3144473 = 2358355) B2358355
theorem B15269087 : Blo 928581 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B1048063 : Blo 928581 1048063 := bstep (se 1 (by rfl) ⟨786047, by rfl⟩ : syracuseStep 1048063 = 1572095) B1572095
theorem B1572473 : Blo 928581 1572473 := bstep (se 2 (by rfl) ⟨589677, by rfl⟩ : syracuseStep 1572473 = 1179355) B1179355
theorem B8945309 : Blo 928581 8945309 := bstep (se 3 (by rfl) ⟨1677245, by rfl⟩ : syracuseStep 8945309 = 3354491) B3354491
theorem B2359003 : Blo 928581 2359003 := bstep (se 1 (by rfl) ⟨1769252, by rfl⟩ : syracuseStep 2359003 = 3538505) B3538505
theorem B2097215 : Blo 928581 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B2097503 : Blo 928581 2097503 := bstep (se 1 (by rfl) ⟨1573127, by rfl⟩ : syracuseStep 2097503 = 3146255) B3146255
theorem B5964155 : Blo 928581 5964155 := bstep (se 1 (by rfl) ⟨4473116, by rfl⟩ : syracuseStep 5964155 = 8946233) B8946233
theorem B3146687 : Blo 928581 3146687 := bstep (se 1 (by rfl) ⟨2360015, by rfl⟩ : syracuseStep 3146687 = 4720031) B4720031
theorem B6980699 : Blo 928581 6980699 := bstep (se 1 (by rfl) ⟨5235524, by rfl⟩ : syracuseStep 6980699 = 10471049) B10471049
theorem B2655497 : Blo 928581 2655497 := bstep (se 2 (by rfl) ⟨995811, by rfl⟩ : syracuseStep 2655497 = 1991623) B1991623
theorem B3540419 : Blo 928581 3540419 := bstep (se 1 (by rfl) ⟨2655314, by rfl⟩ : syracuseStep 3540419 = 5310629) B5310629
theorem B1673555 : Blo 928581 1673555 := bstep (se 1 (by rfl) ⟨1255166, by rfl⟩ : syracuseStep 1673555 = 2510333) B2510333
theorem B3182561 : Blo 928581 3182561 := bstep (se 2 (by rfl) ⟨1193460, by rfl⟩ : syracuseStep 3182561 = 2386921) B2386921
theorem B33919847 : Blo 928581 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B245146799 : Blo 928581 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B2828201 : Blo 928581 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B46443223 : Blo 928581 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B3355127 : Blo 928581 3355127 := bstep (se 1 (by rfl) ⟨2516345, by rfl⟩ : syracuseStep 3355127 = 5032691) B5032691
theorem B930415 : Blo 928581 930415 := bstep (se 1 (by rfl) ⟨697811, by rfl⟩ : syracuseStep 930415 = 1395623) B1395623
theorem B930907 : Blo 928581 930907 := bstep (se 1 (by rfl) ⟨698180, by rfl⟩ : syracuseStep 930907 = 1396361) B1396361
theorem B26850689 : Blo 928581 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B932159 : Blo 928581 932159 := bstep (se 1 (by rfl) ⟨699119, by rfl⟩ : syracuseStep 932159 = 1398239) B1398239
theorem B932479 : Blo 928581 932479 := bstep (se 1 (by rfl) ⟨699359, by rfl⟩ : syracuseStep 932479 = 1398719) B1398719
theorem B4832399 : Blo 928581 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B3980735 : Blo 928581 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B4472347 : Blo 928581 4472347 := bstep (se 1 (by rfl) ⟨3354260, by rfl⟩ : syracuseStep 4472347 = 6708521) B6708521
theorem B2834345 : Blo 928581 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B3981419 : Blo 928581 3981419 := bstep (se 1 (by rfl) ⟨2986064, by rfl⟩ : syracuseStep 3981419 = 5972129) B5972129
theorem B1393019 : Blo 928581 1393019 := bstep (se 1 (by rfl) ⟨1044764, by rfl⟩ : syracuseStep 1393019 = 2089529) B2089529
theorem B8929703 : Blo 928581 8929703 := bstep (se 1 (by rfl) ⟨6697277, by rfl⟩ : syracuseStep 8929703 = 13394555) B13394555
theorem B1393289 : Blo 928581 1393289 := bstep (se 2 (by rfl) ⟨522483, by rfl⟩ : syracuseStep 1393289 = 1044967) B1044967
theorem B1393895 : Blo 928581 1393895 := bstep (se 1 (by rfl) ⟨1045421, by rfl⟩ : syracuseStep 1393895 = 2090843) B2090843
theorem B1394279 : Blo 928581 1394279 := bstep (se 1 (by rfl) ⟨1045709, by rfl⟩ : syracuseStep 1394279 = 2091419) B2091419
theorem B1394441 : Blo 928581 1394441 := bstep (se 2 (by rfl) ⟨522915, by rfl⟩ : syracuseStep 1394441 = 1045831) B1045831
theorem B3983347 : Blo 928581 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B5294591 : Blo 928581 5294591 := bstep (se 1 (by rfl) ⟨3970943, by rfl⟩ : syracuseStep 5294591 = 7941887) B7941887
theorem B8604251 : Blo 928581 8604251 := bstep (se 1 (by rfl) ⟨6453188, by rfl⟩ : syracuseStep 8604251 = 12906377) B12906377
theorem B5032775 : Blo 928581 5032775 := bstep (se 1 (by rfl) ⟨3774581, by rfl⟩ : syracuseStep 5032775 = 7549163) B7549163
theorem B1395689 : Blo 928581 1395689 := bstep (se 2 (by rfl) ⟨523383, by rfl⟩ : syracuseStep 1395689 = 1046767) B1046767
theorem B40717565 : Blo 928581 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B1395995 : Blo 928581 1395995 := bstep (se 1 (by rfl) ⟨1046996, by rfl⟩ : syracuseStep 1395995 = 2093993) B2093993
theorem B5295617 : Blo 928581 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B8507081 : Blo 928581 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B1396583 : Blo 928581 1396583 := bstep (se 1 (by rfl) ⟨1047437, by rfl⟩ : syracuseStep 1396583 = 2094875) B2094875
theorem B3526523 : Blo 928581 3526523 := bstep (se 1 (by rfl) ⟨2644892, by rfl⟩ : syracuseStep 3526523 = 5289785) B5289785
theorem B1397417 : Blo 928581 1397417 := bstep (se 2 (by rfl) ⟨524031, by rfl⟩ : syracuseStep 1397417 = 1048063) B1048063
theorem B4707071 : Blo 928581 4707071 := bstep (se 1 (by rfl) ⟨3530303, by rfl⟩ : syracuseStep 4707071 = 7060607) B7060607
theorem B1398431 : Blo 928581 1398431 := bstep (se 1 (by rfl) ⟨1048823, by rfl⟩ : syracuseStep 1398431 = 2097647) B2097647
theorem B7559351 : Blo 928581 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B58022567 : Blo 928581 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B25451273 : Blo 928581 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B2120831 : Blo 928581 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B2645405 : Blo 928581 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B10740221 : Blo 928581 10740221 := bstep (se 3 (by rfl) ⟨2013791, by rfl⟩ : syracuseStep 10740221 = 4027583) B4027583
theorem B2091833 : Blo 928581 2091833 := bstep (se 2 (by rfl) ⟨784437, by rfl⟩ : syracuseStep 2091833 = 1568875) B1568875
theorem B1568207 : Blo 928581 1568207 := bstep (se 1 (by rfl) ⟨1176155, by rfl⟩ : syracuseStep 1568207 = 2352311) B2352311
theorem B11300735 : Blo 928581 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B3141503 : Blo 928581 3141503 := bstep (se 1 (by rfl) ⟨2356127, by rfl⟩ : syracuseStep 3141503 = 4712255) B4712255
theorem B2519579 : Blo 928581 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B9663457 : Blo 928581 9663457 := bstep (se 2 (by rfl) ⟨3623796, by rfl⟩ : syracuseStep 9663457 = 7247593) B7247593
theorem B20084041 : Blo 928581 20084041 := bstep (se 2 (by rfl) ⟨7531515, by rfl⟩ : syracuseStep 20084041 = 15063031) B15063031
theorem B2094443 : Blo 928581 2094443 := bstep (se 1 (by rfl) ⟨1570832, by rfl⟩ : syracuseStep 2094443 = 3141665) B3141665
theorem B2094713 : Blo 928581 2094713 := bstep (se 2 (by rfl) ⟨785517, by rfl⟩ : syracuseStep 2094713 = 1571035) B1571035
theorem B8943311 : Blo 928581 8943311 := bstep (se 1 (by rfl) ⟨6707483, by rfl⟩ : syracuseStep 8943311 = 13414967) B13414967
theorem B2094857 : Blo 928581 2094857 := bstep (se 2 (by rfl) ⟨785571, by rfl⟩ : syracuseStep 2094857 = 1571143) B1571143
theorem B8943463 : Blo 928581 8943463 := bstep (se 1 (by rfl) ⟨6707597, by rfl⟩ : syracuseStep 8943463 = 13415195) B13415195
theorem B39221111 : Blo 928581 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B2553833 : Blo 928581 2553833 := bstep (se 2 (by rfl) ⟨957687, by rfl⟩ : syracuseStep 2553833 = 1915375) B1915375
theorem B20150471 : Blo 928581 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B7633223 : Blo 928581 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B3537503 : Blo 928581 3537503 := bstep (se 1 (by rfl) ⟨2653127, by rfl⟩ : syracuseStep 3537503 = 5306255) B5306255
theorem B2096315 : Blo 928581 2096315 := bstep (se 1 (by rfl) ⟨1572236, by rfl⟩ : syracuseStep 2096315 = 3144473) B3144473
theorem B3145337 : Blo 928581 3145337 := bstep (se 2 (by rfl) ⟨1179501, by rfl⟩ : syracuseStep 3145337 = 2359003) B2359003
theorem B1048315 : Blo 928581 1048315 := bstep (se 1 (by rfl) ⟨786236, by rfl⟩ : syracuseStep 1048315 = 1572473) B1572473
theorem B5963539 : Blo 928581 5963539 := bstep (se 1 (by rfl) ⟨4472654, by rfl⟩ : syracuseStep 5963539 = 8945309) B8945309
theorem B2654279 : Blo 928581 2654279 := bstep (se 1 (by rfl) ⟨1990709, by rfl⟩ : syracuseStep 2654279 = 3981419) B3981419
theorem B2097791 : Blo 928581 2097791 := bstep (se 1 (by rfl) ⟨1573343, by rfl⟩ : syracuseStep 2097791 = 3146687) B3146687
theorem B1770331 : Blo 928581 1770331 := bstep (se 1 (by rfl) ⟨1327748, by rfl⟩ : syracuseStep 1770331 = 2655497) B2655497
theorem B2360279 : Blo 928581 2360279 := bstep (se 1 (by rfl) ⟨1770209, by rfl⟩ : syracuseStep 2360279 = 3540419) B3540419
theorem B5736167 : Blo 928581 5736167 := bstep (se 1 (by rfl) ⟨4302125, by rfl⟩ : syracuseStep 5736167 = 8604251) B8604251
theorem B5671387 : Blo 928581 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B5311129 : Blo 928581 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B18615197 : Blo 928581 18615197 := bstep (se 3 (by rfl) ⟨3490349, by rfl⟩ : syracuseStep 18615197 = 6980699) B6980699
theorem B22613231 : Blo 928581 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B1413887 : Blo 928581 1413887 := bstep (se 1 (by rfl) ⟨1060415, by rfl⟩ : syracuseStep 1413887 = 2120831) B2120831
theorem B4462813 : Blo 928581 4462813 := bstep (se 3 (by rfl) ⟨836777, by rfl⟩ : syracuseStep 4462813 = 1673555) B1673555
theorem B12884609 : Blo 928581 12884609 := bstep (se 2 (by rfl) ⟨4831728, by rfl⟩ : syracuseStep 12884609 = 9663457) B9663457
theorem B26778721 : Blo 928581 26778721 := bstep (se 2 (by rfl) ⟨10042020, by rfl⟩ : syracuseStep 26778721 = 20084041) B20084041
theorem B67870061 : Blo 928581 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B2236751 : Blo 928581 2236751 := bstep (se 1 (by rfl) ⟨1677563, by rfl⟩ : syracuseStep 2236751 = 3355127) B3355127
theorem B1679719 : Blo 928581 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B12886397 : Blo 928581 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B17900459 : Blo 928581 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B5088815 : Blo 928581 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B928679 : Blo 928581 928679 := bstep (se 1 (by rfl) ⟨696509, by rfl⟩ : syracuseStep 928679 = 1393019) B1393019
theorem B3976103 : Blo 928581 3976103 := bstep (se 1 (by rfl) ⟨2982077, by rfl⟩ : syracuseStep 3976103 = 5964155) B5964155
theorem B928859 : Blo 928581 928859 := bstep (se 1 (by rfl) ⟨696644, by rfl⟩ : syracuseStep 928859 = 1393289) B1393289
theorem B929263 : Blo 928581 929263 := bstep (se 1 (by rfl) ⟨696947, by rfl⟩ : syracuseStep 929263 = 1393895) B1393895
theorem B929519 : Blo 928581 929519 := bstep (se 1 (by rfl) ⟨697139, by rfl⟩ : syracuseStep 929519 = 1394279) B1394279
theorem B929627 : Blo 928581 929627 := bstep (se 1 (by rfl) ⟨697220, by rfl⟩ : syracuseStep 929627 = 1394441) B1394441
theorem B3355183 : Blo 928581 3355183 := bstep (se 1 (by rfl) ⟨2516387, by rfl⟩ : syracuseStep 3355183 = 5032775) B5032775
theorem B930459 : Blo 928581 930459 := bstep (se 1 (by rfl) ⟨697844, by rfl⟩ : syracuseStep 930459 = 1395689) B1395689
theorem B27145043 : Blo 928581 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B930663 : Blo 928581 930663 := bstep (se 1 (by rfl) ⟨697997, by rfl⟩ : syracuseStep 930663 = 1395995) B1395995
theorem B931055 : Blo 928581 931055 := bstep (se 1 (by rfl) ⟨698291, by rfl⟩ : syracuseStep 931055 = 1396583) B1396583
theorem B931611 : Blo 928581 931611 := bstep (se 1 (by rfl) ⟨698708, by rfl⟩ : syracuseStep 931611 = 1397417) B1397417
theorem B932287 : Blo 928581 932287 := bstep (se 1 (by rfl) ⟨699215, by rfl⟩ : syracuseStep 932287 = 1398431) B1398431
theorem B38681711 : Blo 928581 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B7160147 : Blo 928581 7160147 := bstep (se 1 (by rfl) ⟨5370110, by rfl⟩ : syracuseStep 7160147 = 10740221) B10740221
theorem B163431199 : Blo 928581 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B1394555 : Blo 928581 1394555 := bstep (se 1 (by rfl) ⟨1045916, by rfl⟩ : syracuseStep 1394555 = 2091833) B2091833
theorem B1396295 : Blo 928581 1396295 := bstep (se 1 (by rfl) ⟨1047221, by rfl⟩ : syracuseStep 1396295 = 2094443) B2094443
theorem B1396475 : Blo 928581 1396475 := bstep (se 1 (by rfl) ⟨1047356, by rfl⟩ : syracuseStep 1396475 = 2094713) B2094713
theorem B1396571 : Blo 928581 1396571 := bstep (se 1 (by rfl) ⟨1047428, by rfl⟩ : syracuseStep 1396571 = 2094857) B2094857
theorem B30167477 : Blo 928581 30167477 := bstep (se 5 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 30167477 = 2828201) B2828201
theorem B1397543 : Blo 928581 1397543 := bstep (se 1 (by rfl) ⟨1048157, by rfl⟩ : syracuseStep 1397543 = 2096315) B2096315
theorem B1397753 : Blo 928581 1397753 := bstep (se 2 (by rfl) ⟨524157, by rfl⟩ : syracuseStep 1397753 = 1048315) B1048315
theorem B7951385 : Blo 928581 7951385 := bstep (se 2 (by rfl) ⟨2981769, by rfl⟩ : syracuseStep 7951385 = 5963539) B5963539
theorem B1889563 : Blo 928581 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B1398143 : Blo 928581 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B1398335 : Blo 928581 1398335 := bstep (se 1 (by rfl) ⟨1048751, by rfl⟩ : syracuseStep 1398335 = 2097503) B2097503
theorem B5953135 : Blo 928581 5953135 := bstep (se 1 (by rfl) ⟨4464851, by rfl⟩ : syracuseStep 5953135 = 8929703) B8929703
theorem B3529727 : Blo 928581 3529727 := bstep (se 1 (by rfl) ⟨2647295, by rfl⟩ : syracuseStep 3529727 = 5294591) B5294591
theorem B3530411 : Blo 928581 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B2351015 : Blo 928581 2351015 := bstep (se 1 (by rfl) ⟨1763261, by rfl⟩ : syracuseStep 2351015 = 3526523) B3526523
theorem B2121707 : Blo 928581 2121707 := bstep (se 1 (by rfl) ⟨1591280, by rfl⟩ : syracuseStep 2121707 = 3182561) B3182561
theorem B3138047 : Blo 928581 3138047 := bstep (se 1 (by rfl) ⟨2353535, by rfl⟩ : syracuseStep 3138047 = 4707071) B4707071
theorem B61924297 : Blo 928581 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B5039567 : Blo 928581 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B1763603 : Blo 928581 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B53734589 : Blo 928581 53734589 := bstep (se 3 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 53734589 = 20150471) B20150471
theorem B1045471 : Blo 928581 1045471 := bstep (se 1 (by rfl) ⟨784103, by rfl⟩ : syracuseStep 1045471 = 1568207) B1568207
theorem B11924617 : Blo 928581 11924617 := bstep (se 2 (by rfl) ⟨4471731, by rfl⟩ : syracuseStep 11924617 = 8943463) B8943463
theorem B7533823 : Blo 928581 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B2094335 : Blo 928581 2094335 := bstep (se 1 (by rfl) ⟨1570751, by rfl⟩ : syracuseStep 2094335 = 3141503) B3141503
theorem B5962207 : Blo 928581 5962207 := bstep (se 1 (by rfl) ⟨4471655, by rfl⟩ : syracuseStep 5962207 = 8943311) B8943311
theorem B26147407 : Blo 928581 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B1702555 : Blo 928581 1702555 := bstep (se 1 (by rfl) ⟨1276916, by rfl⟩ : syracuseStep 1702555 = 2553833) B2553833
theorem B2358335 : Blo 928581 2358335 := bstep (se 1 (by rfl) ⟨1768751, by rfl⟩ : syracuseStep 2358335 = 3537503) B3537503
theorem B5963129 : Blo 928581 5963129 := bstep (se 2 (by rfl) ⟨2236173, by rfl⟩ : syracuseStep 5963129 = 4472347) B4472347
theorem B2653823 : Blo 928581 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B2096891 : Blo 928581 2096891 := bstep (se 1 (by rfl) ⟨1572668, by rfl⟩ : syracuseStep 2096891 = 3145337) B3145337
theorem B1769519 : Blo 928581 1769519 := bstep (se 1 (by rfl) ⟨1327139, by rfl⟩ : syracuseStep 1769519 = 2654279) B2654279
theorem B1573519 : Blo 928581 1573519 := bstep (se 1 (by rfl) ⟨1180139, by rfl⟩ : syracuseStep 1573519 = 2360279) B2360279
theorem B217908265 : Blo 928581 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B2360441 : Blo 928581 2360441 := bstep (se 2 (by rfl) ⟨885165, by rfl⟩ : syracuseStep 2360441 = 1770331) B1770331
theorem B15075487 : Blo 928581 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B7081505 : Blo 928581 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B1414471 : Blo 928581 1414471 := bstep (se 1 (by rfl) ⟨1060853, by rfl⟩ : syracuseStep 1414471 = 2121707) B2121707
theorem B8590931 : Blo 928581 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B11933639 : Blo 928581 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B15899489 : Blo 928581 15899489 := bstep (se 2 (by rfl) ⟨5962308, by rfl⟩ : syracuseStep 15899489 = 11924617) B11924617
theorem B35823059 : Blo 928581 35823059 := bstep (se 1 (by rfl) ⟨26867294, by rfl⟩ : syracuseStep 35823059 = 53734589) B53734589
theorem B7937513 : Blo 928581 7937513 := bstep (se 2 (by rfl) ⟨2976567, by rfl⟩ : syracuseStep 7937513 = 5953135) B5953135
theorem B15081461 : Blo 928581 15081461 := bstep (se 5 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 15081461 = 1413887) B1413887
theorem B18096695 : Blo 928581 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B3975419 : Blo 928581 3975419 := bstep (se 1 (by rfl) ⟨2981564, by rfl⟩ : syracuseStep 3975419 = 5963129) B5963129
theorem B2239625 : Blo 928581 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B929703 : Blo 928581 929703 := bstep (se 1 (by rfl) ⟨697277, by rfl⟩ : syracuseStep 929703 = 1394555) B1394555
theorem B930863 : Blo 928581 930863 := bstep (se 1 (by rfl) ⟨698147, by rfl⟩ : syracuseStep 930863 = 1396295) B1396295
theorem B930983 : Blo 928581 930983 := bstep (se 1 (by rfl) ⟨698237, by rfl⟩ : syracuseStep 930983 = 1396475) B1396475
theorem B931047 : Blo 928581 931047 := bstep (se 1 (by rfl) ⟨698285, by rfl⟩ : syracuseStep 931047 = 1396571) B1396571
theorem B931695 : Blo 928581 931695 := bstep (se 1 (by rfl) ⟨698771, by rfl⟩ : syracuseStep 931695 = 1397543) B1397543
theorem B36321173 : Blo 928581 36321173 := bstep (se 6 (by rfl) ⟨851277, by rfl⟩ : syracuseStep 36321173 = 1702555) B1702555
theorem B931835 : Blo 928581 931835 := bstep (se 1 (by rfl) ⟨698876, by rfl⟩ : syracuseStep 931835 = 1397753) B1397753
theorem B932095 : Blo 928581 932095 := bstep (se 1 (by rfl) ⟨699071, by rfl⟩ : syracuseStep 932095 = 1398143) B1398143
theorem B932223 : Blo 928581 932223 := bstep (se 1 (by rfl) ⟨699167, by rfl⟩ : syracuseStep 932223 = 1398335) B1398335
theorem B1491167 : Blo 928581 1491167 := bstep (se 1 (by rfl) ⟨1118375, by rfl⟩ : syracuseStep 1491167 = 2236751) B2236751
theorem B4473577 : Blo 928581 4473577 := bstep (se 2 (by rfl) ⟨1677591, by rfl⟩ : syracuseStep 4473577 = 3355183) B3355183
theorem B3359711 : Blo 928581 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B3392543 : Blo 928581 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B1393961 : Blo 928581 1393961 := bstep (se 2 (by rfl) ⟨522735, by rfl⟩ : syracuseStep 1393961 = 1045471) B1045471
theorem B10045097 : Blo 928581 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B34358957 : Blo 928581 34358957 := bstep (se 3 (by rfl) ⟨6442304, by rfl⟩ : syracuseStep 34358957 = 12884609) B12884609
theorem B5950417 : Blo 928581 5950417 := bstep (se 2 (by rfl) ⟨2231406, by rfl⟩ : syracuseStep 5950417 = 4462813) B4462813
theorem B7949609 : Blo 928581 7949609 := bstep (se 2 (by rfl) ⟨2981103, by rfl⟩ : syracuseStep 7949609 = 5962207) B5962207
theorem B1396223 : Blo 928581 1396223 := bstep (se 1 (by rfl) ⟨1047167, by rfl⟩ : syracuseStep 1396223 = 2094335) B2094335
theorem B35704961 : Blo 928581 35704961 := bstep (se 2 (by rfl) ⟨13389360, by rfl⟩ : syracuseStep 35704961 = 26778721) B26778721
theorem B1397927 : Blo 928581 1397927 := bstep (se 1 (by rfl) ⟨1048445, by rfl⟩ : syracuseStep 1397927 = 2096891) B2096891
theorem B4773431 : Blo 928581 4773431 := bstep (se 1 (by rfl) ⟨3580073, by rfl⟩ : syracuseStep 4773431 = 7160147) B7160147
theorem B1398527 : Blo 928581 1398527 := bstep (se 1 (by rfl) ⟨1048895, by rfl⟩ : syracuseStep 1398527 = 2097791) B2097791
theorem B3824111 : Blo 928581 3824111 := bstep (se 1 (by rfl) ⟨2868083, by rfl⟩ : syracuseStep 3824111 = 5736167) B5736167
theorem B82565729 : Blo 928581 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B12410131 : Blo 928581 12410131 := bstep (se 1 (by rfl) ⟨9307598, by rfl⟩ : syracuseStep 12410131 = 18615197) B18615197
theorem B20111651 : Blo 928581 20111651 := bstep (se 1 (by rfl) ⟨15083738, by rfl⟩ : syracuseStep 20111651 = 30167477) B30167477
theorem B7561849 : Blo 928581 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B5300923 : Blo 928581 5300923 := bstep (se 1 (by rfl) ⟨3975692, by rfl⟩ : syracuseStep 5300923 = 7951385) B7951385
theorem B2353151 : Blo 928581 2353151 := bstep (se 1 (by rfl) ⟨1764863, by rfl⟩ : syracuseStep 2353151 = 3529727) B3529727
theorem B45246707 : Blo 928581 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B2353607 : Blo 928581 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B1567343 : Blo 928581 1567343 := bstep (se 1 (by rfl) ⟨1175507, by rfl⟩ : syracuseStep 1567343 = 2351015) B2351015
theorem B2092031 : Blo 928581 2092031 := bstep (se 1 (by rfl) ⟨1569023, by rfl⟩ : syracuseStep 2092031 = 3138047) B3138047
theorem B1175735 : Blo 928581 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B2519417 : Blo 928581 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B2650735 : Blo 928581 2650735 := bstep (se 1 (by rfl) ⟨1988051, by rfl⟩ : syracuseStep 2650735 = 3976103) B3976103
theorem B34863209 : Blo 928581 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B1572223 : Blo 928581 1572223 := bstep (se 1 (by rfl) ⟨1179167, by rfl⟩ : syracuseStep 1572223 = 2358335) B2358335
theorem B25787807 : Blo 928581 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B1769215 : Blo 928581 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B1179679 : Blo 928581 1179679 := bstep (se 1 (by rfl) ⟨884759, by rfl⟩ : syracuseStep 1179679 = 1769519) B1769519
theorem B1573627 : Blo 928581 1573627 := bstep (se 1 (by rfl) ⟨1180220, by rfl⟩ : syracuseStep 1573627 = 2360441) B2360441
theorem B2098025 : Blo 928581 2098025 := bstep (se 2 (by rfl) ⟨786759, by rfl⟩ : syracuseStep 2098025 = 1573519) B1573519
theorem B5964769 : Blo 928581 5964769 := bstep (se 2 (by rfl) ⟨2236788, by rfl⟩ : syracuseStep 5964769 = 4473577) B4473577
theorem B22905971 : Blo 928581 22905971 := bstep (se 1 (by rfl) ⟨17179478, by rfl⟩ : syracuseStep 22905971 = 34358957) B34358957
theorem B4721003 : Blo 928581 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B9046781 : Blo 928581 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B3182287 : Blo 928581 3182287 := bstep (se 1 (by rfl) ⟨2386715, by rfl⟩ : syracuseStep 3182287 = 4773431) B4773431
theorem B7933889 : Blo 928581 7933889 := bstep (se 2 (by rfl) ⟨2975208, by rfl⟩ : syracuseStep 7933889 = 5950417) B5950417
theorem B13407767 : Blo 928581 13407767 := bstep (se 1 (by rfl) ⟨10055825, by rfl⟩ : syracuseStep 13407767 = 20111651) B20111651
theorem B12064463 : Blo 928581 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B1679611 : Blo 928581 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B23242139 : Blo 928581 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B3976445 : Blo 928581 3976445 := bstep (se 3 (by rfl) ⟨745583, by rfl⟩ : syracuseStep 3976445 = 1491167) B1491167
theorem B2239807 : Blo 928581 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B929307 : Blo 928581 929307 := bstep (se 1 (by rfl) ⟨696980, by rfl⟩ : syracuseStep 929307 = 1393961) B1393961
theorem B6696731 : Blo 928581 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B930815 : Blo 928581 930815 := bstep (se 1 (by rfl) ⟨698111, by rfl⟩ : syracuseStep 930815 = 1396223) B1396223
theorem B23803307 : Blo 928581 23803307 := bstep (se 1 (by rfl) ⟨17852480, by rfl⟩ : syracuseStep 23803307 = 35704961) B35704961
theorem B20100649 : Blo 928581 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B931951 : Blo 928581 931951 := bstep (se 1 (by rfl) ⟨698963, by rfl⟩ : syracuseStep 931951 = 1397927) B1397927
theorem B932351 : Blo 928581 932351 := bstep (se 1 (by rfl) ⟨699263, by rfl⟩ : syracuseStep 932351 = 1398527) B1398527
theorem B10599659 : Blo 928581 10599659 := bstep (se 1 (by rfl) ⟨7949744, by rfl⟩ : syracuseStep 10599659 = 15899489) B15899489
theorem B5291675 : Blo 928581 5291675 := bstep (se 1 (by rfl) ⟨3968756, by rfl⟩ : syracuseStep 5291675 = 7937513) B7937513
theorem B10601117 : Blo 928581 10601117 := bstep (se 3 (by rfl) ⟨1987709, by rfl⟩ : syracuseStep 10601117 = 3975419) B3975419
theorem B30164471 : Blo 928581 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B1885961 : Blo 928581 1885961 := bstep (se 2 (by rfl) ⟨707235, by rfl⟩ : syracuseStep 1885961 = 1414471) B1414471
theorem B1394687 : Blo 928581 1394687 := bstep (se 1 (by rfl) ⟨1046015, by rfl⟩ : syracuseStep 1394687 = 2092031) B2092031
theorem B1493083 : Blo 928581 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B17191871 : Blo 928581 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B3135293 : Blo 928581 3135293 := bstep (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) B1175735
theorem B10082465 : Blo 928581 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B7067897 : Blo 928581 7067897 := bstep (se 2 (by rfl) ⟨2650461, by rfl⟩ : syracuseStep 7067897 = 5300923) B5300923
theorem B290544353 : Blo 928581 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B5299739 : Blo 928581 5299739 := bstep (se 1 (by rfl) ⟨3974804, by rfl⟩ : syracuseStep 5299739 = 7949609) B7949609
theorem B5727287 : Blo 928581 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B7955759 : Blo 928581 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B2549407 : Blo 928581 2549407 := bstep (se 1 (by rfl) ⟨1912055, by rfl⟩ : syracuseStep 2549407 = 3824111) B3824111
theorem B55043819 : Blo 928581 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B23882039 : Blo 928581 23882039 := bstep (se 1 (by rfl) ⟨17911529, by rfl⟩ : syracuseStep 23882039 = 35823059) B35823059
theorem B10054307 : Blo 928581 10054307 := bstep (se 1 (by rfl) ⟨7540730, by rfl⟩ : syracuseStep 10054307 = 15081461) B15081461
theorem B3534313 : Blo 928581 3534313 := bstep (se 2 (by rfl) ⟨1325367, by rfl⟩ : syracuseStep 3534313 = 2650735) B2650735
theorem B1568767 : Blo 928581 1568767 := bstep (se 1 (by rfl) ⟨1176575, by rfl⟩ : syracuseStep 1568767 = 2353151) B2353151
theorem B1569071 : Blo 928581 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B1044895 : Blo 928581 1044895 := bstep (se 1 (by rfl) ⟨783671, by rfl⟩ : syracuseStep 1044895 = 1567343) B1567343
theorem B24214115 : Blo 928581 24214115 := bstep (se 1 (by rfl) ⟨18160586, by rfl⟩ : syracuseStep 24214115 = 36321173) B36321173
theorem B16546841 : Blo 928581 16546841 := bstep (se 2 (by rfl) ⟨6205065, by rfl⟩ : syracuseStep 16546841 = 12410131) B12410131
theorem B2096297 : Blo 928581 2096297 := bstep (se 2 (by rfl) ⟨786111, by rfl⟩ : syracuseStep 2096297 = 1572223) B1572223
theorem B2358953 : Blo 928581 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B1572905 : Blo 928581 1572905 := bstep (se 2 (by rfl) ⟨589839, by rfl⟩ : syracuseStep 1572905 = 1179679) B1179679
theorem B7963109 : Blo 928581 7963109 := bstep (se 4 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 7963109 = 1493083) B1493083
theorem B15270647 : Blo 928581 15270647 := bstep (se 1 (by rfl) ⟨11452985, by rfl⟩ : syracuseStep 15270647 = 22905971) B22905971
theorem B2098169 : Blo 928581 2098169 := bstep (se 2 (by rfl) ⟨786813, by rfl⟩ : syracuseStep 2098169 = 1573627) B1573627
theorem B3147335 : Blo 928581 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B6031187 : Blo 928581 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B6721643 : Blo 928581 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B2986409 : Blo 928581 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B193696235 : Blo 928581 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B4464487 : Blo 928581 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B15868871 : Blo 928581 15868871 := bstep (se 1 (by rfl) ⟨11901653, by rfl⟩ : syracuseStep 15868871 = 23803307) B23803307
theorem B2239481 : Blo 928581 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B929791 : Blo 928581 929791 := bstep (se 1 (by rfl) ⟨697343, by rfl⟩ : syracuseStep 929791 = 1394687) B1394687
theorem B5289259 : Blo 928581 5289259 := bstep (se 1 (by rfl) ⟨3966944, by rfl⟩ : syracuseStep 5289259 = 7933889) B7933889
theorem B8042975 : Blo 928581 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B5029229 : Blo 928581 5029229 := bstep (se 3 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 5029229 = 1885961) B1885961
theorem B4243049 : Blo 928581 4243049 := bstep (se 2 (by rfl) ⟨1591143, by rfl⟩ : syracuseStep 4243049 = 3182287) B3182287
theorem B1393193 : Blo 928581 1393193 := bstep (se 2 (by rfl) ⟨522447, by rfl⟩ : syracuseStep 1393193 = 1044895) B1044895
theorem B3818191 : Blo 928581 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B6702871 : Blo 928581 6702871 := bstep (se 1 (by rfl) ⟨5027153, by rfl⟩ : syracuseStep 6702871 = 10054307) B10054307
theorem B16142743 : Blo 928581 16142743 := bstep (se 1 (by rfl) ⟨12107057, by rfl⟩ : syracuseStep 16142743 = 24214115) B24214115
theorem B11031227 : Blo 928581 11031227 := bstep (se 1 (by rfl) ⟨8273420, by rfl⟩ : syracuseStep 11031227 = 16546841) B16546841
theorem B1397531 : Blo 928581 1397531 := bstep (se 1 (by rfl) ⟨1048148, by rfl⟩ : syracuseStep 1397531 = 2096297) B2096297
theorem B7066439 : Blo 928581 7066439 := bstep (se 1 (by rfl) ⟨5299829, by rfl⟩ : syracuseStep 7066439 = 10599659) B10599659
theorem B3527783 : Blo 928581 3527783 := bstep (se 1 (by rfl) ⟨2645837, by rfl⟩ : syracuseStep 3527783 = 5291675) B5291675
theorem B7067411 : Blo 928581 7067411 := bstep (se 1 (by rfl) ⟨5300558, by rfl⟩ : syracuseStep 7067411 = 10601117) B10601117
theorem B1398683 : Blo 928581 1398683 := bstep (se 1 (by rfl) ⟨1049012, by rfl⟩ : syracuseStep 1398683 = 2098025) B2098025
theorem B20109647 : Blo 928581 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B7953025 : Blo 928581 7953025 := bstep (se 2 (by rfl) ⟨2982384, by rfl⟩ : syracuseStep 7953025 = 5964769) B5964769
theorem B3399209 : Blo 928581 3399209 := bstep (se 2 (by rfl) ⟨1274703, by rfl⟩ : syracuseStep 3399209 = 2549407) B2549407
theorem B11461247 : Blo 928581 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B8938511 : Blo 928581 8938511 := bstep (se 1 (by rfl) ⟨6703883, by rfl⟩ : syracuseStep 8938511 = 13407767) B13407767
theorem B2090195 : Blo 928581 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B4711931 : Blo 928581 4711931 := bstep (se 1 (by rfl) ⟨3533948, by rfl⟩ : syracuseStep 4711931 = 7067897) B7067897
theorem B4712417 : Blo 928581 4712417 := bstep (se 2 (by rfl) ⟨1767156, by rfl⟩ : syracuseStep 4712417 = 3534313) B3534313
theorem B3533159 : Blo 928581 3533159 := bstep (se 1 (by rfl) ⟨2649869, by rfl⟩ : syracuseStep 3533159 = 5299739) B5299739
theorem B2091689 : Blo 928581 2091689 := bstep (se 2 (by rfl) ⟨784383, by rfl⟩ : syracuseStep 2091689 = 1568767) B1568767
theorem B5303839 : Blo 928581 5303839 := bstep (se 1 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 5303839 = 7955759) B7955759
theorem B15494759 : Blo 928581 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B36695879 : Blo 928581 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B15921359 : Blo 928581 15921359 := bstep (se 1 (by rfl) ⟨11941019, by rfl⟩ : syracuseStep 15921359 = 23882039) B23882039
theorem B26800865 : Blo 928581 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B2650963 : Blo 928581 2650963 := bstep (se 1 (by rfl) ⟨1988222, by rfl⟩ : syracuseStep 2650963 = 3976445) B3976445
theorem B1046047 : Blo 928581 1046047 := bstep (se 1 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 1046047 = 1569071) B1569071
theorem B1572635 : Blo 928581 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B1048603 : Blo 928581 1048603 := bstep (se 1 (by rfl) ⟨786452, by rfl⟩ : syracuseStep 1048603 = 1572905) B1572905
theorem B5308739 : Blo 928581 5308739 := bstep (se 1 (by rfl) ⟨3981554, by rfl⟩ : syracuseStep 5308739 = 7963109) B7963109
theorem B2098223 : Blo 928581 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B7963757 : Blo 928581 7963757 := bstep (se 3 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 7963757 = 2986409) B2986409
theorem B13406431 : Blo 928581 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B2266139 : Blo 928581 2266139 := bstep (se 1 (by rfl) ⟨1699604, by rfl⟩ : syracuseStep 2266139 = 3399209) B3399209
theorem B7640831 : Blo 928581 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B7052345 : Blo 928581 7052345 := bstep (se 2 (by rfl) ⟨2644629, by rfl⟩ : syracuseStep 7052345 = 5289259) B5289259
theorem B10329839 : Blo 928581 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B17867243 : Blo 928581 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B13411277 : Blo 928581 13411277 := bstep (se 3 (by rfl) ⟨2514614, by rfl⟩ : syracuseStep 13411277 = 5029229) B5029229
theorem B2828699 : Blo 928581 2828699 := bstep (se 1 (by rfl) ⟨2121524, by rfl⟩ : syracuseStep 2828699 = 4243049) B4243049
theorem B928795 : Blo 928581 928795 := bstep (se 1 (by rfl) ⟨696596, by rfl⟩ : syracuseStep 928795 = 1393193) B1393193
theorem B5090921 : Blo 928581 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B7354151 : Blo 928581 7354151 := bstep (se 1 (by rfl) ⟨5515613, by rfl⟩ : syracuseStep 7354151 = 11031227) B11031227
theorem B931687 : Blo 928581 931687 := bstep (se 1 (by rfl) ⟨698765, by rfl⟩ : syracuseStep 931687 = 1397531) B1397531
theorem B932455 : Blo 928581 932455 := bstep (se 1 (by rfl) ⟨699341, by rfl⟩ : syracuseStep 932455 = 1398683) B1398683
theorem B1393463 : Blo 928581 1393463 := bstep (se 1 (by rfl) ⟨1045097, by rfl⟩ : syracuseStep 1393463 = 2090195) B2090195
theorem B1394459 : Blo 928581 1394459 := bstep (se 1 (by rfl) ⟨1045844, by rfl⟩ : syracuseStep 1394459 = 2091689) B2091689
theorem B1492987 : Blo 928581 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B1394729 : Blo 928581 1394729 := bstep (se 2 (by rfl) ⟨523023, by rfl⟩ : syracuseStep 1394729 = 1046047) B1046047
theorem B24463919 : Blo 928581 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B10604033 : Blo 928581 10604033 := bstep (se 2 (by rfl) ⟨3976512, by rfl⟩ : syracuseStep 10604033 = 7953025) B7953025
theorem B5361983 : Blo 928581 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B5952649 : Blo 928581 5952649 := bstep (se 2 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 5952649 = 4464487) B4464487
theorem B1398779 : Blo 928581 1398779 := bstep (se 1 (by rfl) ⟨1049084, by rfl⟩ : syracuseStep 1398779 = 2098169) B2098169
theorem B4020791 : Blo 928581 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B40721725 : Blo 928581 40721725 := bstep (se 3 (by rfl) ⟨7635323, by rfl⟩ : syracuseStep 40721725 = 15270647) B15270647
theorem B8937161 : Blo 928581 8937161 := bstep (se 2 (by rfl) ⟨3351435, by rfl⟩ : syracuseStep 8937161 = 6702871) B6702871
theorem B4481095 : Blo 928581 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B129130823 : Blo 928581 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B4710959 : Blo 928581 4710959 := bstep (se 1 (by rfl) ⟨3533219, by rfl⟩ : syracuseStep 4710959 = 7066439) B7066439
theorem B2351855 : Blo 928581 2351855 := bstep (se 1 (by rfl) ⟨1763891, by rfl⟩ : syracuseStep 2351855 = 3527783) B3527783
theorem B4711607 : Blo 928581 4711607 := bstep (se 1 (by rfl) ⟨3533705, by rfl⟩ : syracuseStep 4711607 = 7067411) B7067411
theorem B7071785 : Blo 928581 7071785 := bstep (se 2 (by rfl) ⟨2651919, by rfl⟩ : syracuseStep 7071785 = 5303839) B5303839
theorem B21523657 : Blo 928581 21523657 := bstep (se 2 (by rfl) ⟨8071371, by rfl⟩ : syracuseStep 21523657 = 16142743) B16142743
theorem B10579247 : Blo 928581 10579247 := bstep (se 1 (by rfl) ⟨7934435, by rfl⟩ : syracuseStep 10579247 = 15868871) B15868871
theorem B5959007 : Blo 928581 5959007 := bstep (se 1 (by rfl) ⟨4469255, by rfl⟩ : syracuseStep 5959007 = 8938511) B8938511
theorem B3141287 : Blo 928581 3141287 := bstep (se 1 (by rfl) ⟨2355965, by rfl⟩ : syracuseStep 3141287 = 4711931) B4711931
theorem B3534617 : Blo 928581 3534617 := bstep (se 2 (by rfl) ⟨1325481, by rfl⟩ : syracuseStep 3534617 = 2650963) B2650963
theorem B3141611 : Blo 928581 3141611 := bstep (se 1 (by rfl) ⟨2356208, by rfl⟩ : syracuseStep 3141611 = 4712417) B4712417
theorem B2355439 : Blo 928581 2355439 := bstep (se 1 (by rfl) ⟨1766579, by rfl⟩ : syracuseStep 2355439 = 3533159) B3533159
theorem B10614239 : Blo 928581 10614239 := bstep (se 1 (by rfl) ⟨7960679, by rfl⟩ : syracuseStep 10614239 = 15921359) B15921359
theorem B1048423 : Blo 928581 1048423 := bstep (se 1 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 1048423 = 1572635) B1572635
theorem B3539159 : Blo 928581 3539159 := bstep (se 1 (by rfl) ⟨2654369, by rfl⟩ : syracuseStep 3539159 = 5308739) B5308739
theorem B5309171 : Blo 928581 5309171 := bstep (se 1 (by rfl) ⟨3981878, by rfl⟩ : syracuseStep 5309171 = 7963757) B7963757
theorem B3574655 : Blo 928581 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B1510759 : Blo 928581 1510759 := bstep (se 1 (by rfl) ⟨1133069, by rfl⟩ : syracuseStep 1510759 = 2266139) B2266139
theorem B6886559 : Blo 928581 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B86087215 : Blo 928581 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B7936865 : Blo 928581 7936865 := bstep (se 2 (by rfl) ⟨2976324, by rfl⟩ : syracuseStep 7936865 = 5952649) B5952649
theorem B7052831 : Blo 928581 7052831 := bstep (se 1 (by rfl) ⟨5289623, by rfl⟩ : syracuseStep 7052831 = 10579247) B10579247
theorem B3972671 : Blo 928581 3972671 := bstep (se 1 (by rfl) ⟨2979503, by rfl⟩ : syracuseStep 3972671 = 5959007) B5959007
theorem B5974793 : Blo 928581 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B928975 : Blo 928581 928975 := bstep (se 1 (by rfl) ⟨696731, by rfl⟩ : syracuseStep 928975 = 1393463) B1393463
theorem B929639 : Blo 928581 929639 := bstep (se 1 (by rfl) ⟨697229, by rfl⟩ : syracuseStep 929639 = 1394459) B1394459
theorem B929819 : Blo 928581 929819 := bstep (se 1 (by rfl) ⟨697364, by rfl⟩ : syracuseStep 929819 = 1394729) B1394729
theorem B932519 : Blo 928581 932519 := bstep (se 1 (by rfl) ⟨699389, by rfl⟩ : syracuseStep 932519 = 1398779) B1398779
theorem B4701563 : Blo 928581 4701563 := bstep (se 1 (by rfl) ⟨3526172, by rfl⟩ : syracuseStep 4701563 = 7052345) B7052345
theorem B17875241 : Blo 928581 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B11911495 : Blo 928581 11911495 := bstep (se 1 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 11911495 = 17867243) B17867243
theorem B1885799 : Blo 928581 1885799 := bstep (se 1 (by rfl) ⟨1414349, by rfl⟩ : syracuseStep 1885799 = 2828699) B2828699
theorem B3393947 : Blo 928581 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B4902767 : Blo 928581 4902767 := bstep (se 1 (by rfl) ⟨3677075, by rfl⟩ : syracuseStep 4902767 = 7354151) B7354151
theorem B1397897 : Blo 928581 1397897 := bstep (se 2 (by rfl) ⟨524211, by rfl⟩ : syracuseStep 1397897 = 1048423) B1048423
theorem B1398137 : Blo 928581 1398137 := bstep (se 2 (by rfl) ⟨524301, by rfl⟩ : syracuseStep 1398137 = 1048603) B1048603
theorem B1398815 : Blo 928581 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B16309279 : Blo 928581 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B7069355 : Blo 928581 7069355 := bstep (se 1 (by rfl) ⟨5302016, by rfl⟩ : syracuseStep 7069355 = 10604033) B10604033
theorem B1990649 : Blo 928581 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B28698209 : Blo 928581 28698209 := bstep (se 2 (by rfl) ⟨10761828, by rfl⟩ : syracuseStep 28698209 = 21523657) B21523657
theorem B20375549 : Blo 928581 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B5958107 : Blo 928581 5958107 := bstep (se 1 (by rfl) ⟨4468580, by rfl⟩ : syracuseStep 5958107 = 8937161) B8937161
theorem B3140585 : Blo 928581 3140585 := bstep (se 2 (by rfl) ⟨1177719, by rfl⟩ : syracuseStep 3140585 = 2355439) B2355439
theorem B3140639 : Blo 928581 3140639 := bstep (se 1 (by rfl) ⟨2355479, by rfl⟩ : syracuseStep 3140639 = 4710959) B4710959
theorem B1567903 : Blo 928581 1567903 := bstep (se 1 (by rfl) ⟨1175927, by rfl⟩ : syracuseStep 1567903 = 2351855) B2351855
theorem B42888437 : Blo 928581 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B8940851 : Blo 928581 8940851 := bstep (se 1 (by rfl) ⟨6705638, by rfl⟩ : syracuseStep 8940851 = 13411277) B13411277
theorem B3141071 : Blo 928581 3141071 := bstep (se 1 (by rfl) ⟨2355803, by rfl⟩ : syracuseStep 3141071 = 4711607) B4711607
theorem B4714523 : Blo 928581 4714523 := bstep (se 1 (by rfl) ⟨3535892, by rfl⟩ : syracuseStep 4714523 = 7071785) B7071785
theorem B2094191 : Blo 928581 2094191 := bstep (se 1 (by rfl) ⟨1570643, by rfl⟩ : syracuseStep 2094191 = 3141287) B3141287
theorem B2356411 : Blo 928581 2356411 := bstep (se 1 (by rfl) ⟨1767308, by rfl⟩ : syracuseStep 2356411 = 3534617) B3534617
theorem B2094407 : Blo 928581 2094407 := bstep (se 1 (by rfl) ⟨1570805, by rfl⟩ : syracuseStep 2094407 = 3141611) B3141611
theorem B7076159 : Blo 928581 7076159 := bstep (se 1 (by rfl) ⟨5307119, by rfl⟩ : syracuseStep 7076159 = 10614239) B10614239
theorem B54295633 : Blo 928581 54295633 := bstep (se 2 (by rfl) ⟨20360862, by rfl⟩ : syracuseStep 54295633 = 40721725) B40721725
theorem B2359439 : Blo 928581 2359439 := bstep (se 1 (by rfl) ⟨1769579, by rfl⟩ : syracuseStep 2359439 = 3539159) B3539159
theorem B3539447 : Blo 928581 3539447 := bstep (se 1 (by rfl) ⟨2654585, by rfl⟩ : syracuseStep 3539447 = 5309171) B5309171
theorem B9050525 : Blo 928581 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B3972071 : Blo 928581 3972071 := bstep (se 1 (by rfl) ⟨2979053, by rfl⟩ : syracuseStep 3972071 = 5958107) B5958107
theorem B72394177 : Blo 928581 72394177 := bstep (se 2 (by rfl) ⟨27147816, by rfl⟩ : syracuseStep 72394177 = 54295633) B54295633
theorem B18364157 : Blo 928581 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B931931 : Blo 928581 931931 := bstep (se 1 (by rfl) ⟨698948, by rfl⟩ : syracuseStep 931931 = 1397897) B1397897
theorem B932091 : Blo 928581 932091 := bstep (se 1 (by rfl) ⟨699068, by rfl⟩ : syracuseStep 932091 = 1398137) B1398137
theorem B932543 : Blo 928581 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B5028797 : Blo 928581 5028797 := bstep (se 3 (by rfl) ⟨942899, by rfl⟩ : syracuseStep 5028797 = 1885799) B1885799
theorem B2014345 : Blo 928581 2014345 := bstep (se 2 (by rfl) ⟨755379, by rfl⟩ : syracuseStep 2014345 = 1510759) B1510759
theorem B5291243 : Blo 928581 5291243 := bstep (se 1 (by rfl) ⟨3968432, by rfl⟩ : syracuseStep 5291243 = 7936865) B7936865
theorem B4701887 : Blo 928581 4701887 := bstep (se 1 (by rfl) ⟨3526415, by rfl⟩ : syracuseStep 4701887 = 7052831) B7052831
theorem B1327099 : Blo 928581 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B13583699 : Blo 928581 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B3983195 : Blo 928581 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B28592291 : Blo 928581 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B1396127 : Blo 928581 1396127 := bstep (se 1 (by rfl) ⟨1047095, by rfl⟩ : syracuseStep 1396127 = 2094191) B2094191
theorem B1396271 : Blo 928581 1396271 := bstep (se 1 (by rfl) ⟨1047203, by rfl⟩ : syracuseStep 1396271 = 2094407) B2094407
theorem B21745705 : Blo 928581 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B3134375 : Blo 928581 3134375 := bstep (se 1 (by rfl) ⟨2350781, by rfl⟩ : syracuseStep 3134375 = 4701563) B4701563
theorem B11916827 : Blo 928581 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B15881993 : Blo 928581 15881993 := bstep (se 2 (by rfl) ⟨5955747, by rfl⟩ : syracuseStep 15881993 = 11911495) B11911495
theorem B2383103 : Blo 928581 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B3268511 : Blo 928581 3268511 := bstep (se 1 (by rfl) ⟨2451383, by rfl⟩ : syracuseStep 3268511 = 4902767) B4902767
theorem B2090537 : Blo 928581 2090537 := bstep (se 2 (by rfl) ⟨783951, by rfl⟩ : syracuseStep 2090537 = 1567903) B1567903
theorem B2648447 : Blo 928581 2648447 := bstep (se 1 (by rfl) ⟨1986335, by rfl⟩ : syracuseStep 2648447 = 3972671) B3972671
theorem B4712903 : Blo 928581 4712903 := bstep (se 1 (by rfl) ⟨3534677, by rfl⟩ : syracuseStep 4712903 = 7069355) B7069355
theorem B19132139 : Blo 928581 19132139 := bstep (se 1 (by rfl) ⟨14349104, by rfl⟩ : syracuseStep 19132139 = 28698209) B28698209
theorem B3141881 : Blo 928581 3141881 := bstep (se 2 (by rfl) ⟨1178205, by rfl⟩ : syracuseStep 3141881 = 2356411) B2356411
theorem B2093723 : Blo 928581 2093723 := bstep (se 1 (by rfl) ⟨1570292, by rfl⟩ : syracuseStep 2093723 = 3140585) B3140585
theorem B2093759 : Blo 928581 2093759 := bstep (se 1 (by rfl) ⟨1570319, by rfl⟩ : syracuseStep 2093759 = 3140639) B3140639
theorem B114782953 : Blo 928581 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B5960567 : Blo 928581 5960567 := bstep (se 1 (by rfl) ⟨4470425, by rfl⟩ : syracuseStep 5960567 = 8940851) B8940851
theorem B2094047 : Blo 928581 2094047 := bstep (se 1 (by rfl) ⟨1570535, by rfl⟩ : syracuseStep 2094047 = 3141071) B3141071
theorem B3143015 : Blo 928581 3143015 := bstep (se 1 (by rfl) ⟨2357261, by rfl⟩ : syracuseStep 3143015 = 4714523) B4714523
theorem B4717439 : Blo 928581 4717439 := bstep (se 1 (by rfl) ⟨3538079, by rfl⟩ : syracuseStep 4717439 = 7076159) B7076159
theorem B1572959 : Blo 928581 1572959 := bstep (se 1 (by rfl) ⟨1179719, by rfl⟩ : syracuseStep 1572959 = 2359439) B2359439
theorem B2359631 : Blo 928581 2359631 := bstep (se 1 (by rfl) ⟨1769723, by rfl⟩ : syracuseStep 2359631 = 3539447) B3539447
theorem B2655463 : Blo 928581 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B10587995 : Blo 928581 10587995 := bstep (se 1 (by rfl) ⟨7940996, by rfl⟩ : syracuseStep 10587995 = 15881993) B15881993
theorem B6033683 : Blo 928581 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B12754759 : Blo 928581 12754759 := bstep (se 1 (by rfl) ⟨9566069, by rfl⟩ : syracuseStep 12754759 = 19132139) B19132139
theorem B3973711 : Blo 928581 3973711 := bstep (se 1 (by rfl) ⟨2980283, by rfl⟩ : syracuseStep 3973711 = 5960567) B5960567
theorem B3352531 : Blo 928581 3352531 := bstep (se 1 (by rfl) ⟨2514398, by rfl⟩ : syracuseStep 3352531 = 5028797) B5028797
theorem B9055799 : Blo 928581 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B930751 : Blo 928581 930751 := bstep (se 1 (by rfl) ⟨698063, by rfl⟩ : syracuseStep 930751 = 1396127) B1396127
theorem B930847 : Blo 928581 930847 := bstep (se 1 (by rfl) ⟨698135, by rfl⟩ : syracuseStep 930847 = 1396271) B1396271
theorem B7944551 : Blo 928581 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B1588735 : Blo 928581 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B2179007 : Blo 928581 2179007 := bstep (se 1 (by rfl) ⟨1634255, by rfl⟩ : syracuseStep 2179007 = 3268511) B3268511
theorem B153043937 : Blo 928581 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B1393691 : Blo 928581 1393691 := bstep (se 1 (by rfl) ⟨1045268, by rfl⟩ : syracuseStep 1393691 = 2090537) B2090537
theorem B1395815 : Blo 928581 1395815 := bstep (se 1 (by rfl) ⟨1046861, by rfl⟩ : syracuseStep 1395815 = 2093723) B2093723
theorem B1395839 : Blo 928581 1395839 := bstep (se 1 (by rfl) ⟨1046879, by rfl⟩ : syracuseStep 1395839 = 2093759) B2093759
theorem B1396031 : Blo 928581 1396031 := bstep (se 1 (by rfl) ⟨1047023, by rfl⟩ : syracuseStep 1396031 = 2094047) B2094047
theorem B12242771 : Blo 928581 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B3527495 : Blo 928581 3527495 := bstep (se 1 (by rfl) ⟨2645621, by rfl⟩ : syracuseStep 3527495 = 5291243) B5291243
theorem B3134591 : Blo 928581 3134591 := bstep (se 1 (by rfl) ⟨2350943, by rfl⟩ : syracuseStep 3134591 = 4701887) B4701887
theorem B19061527 : Blo 928581 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B96525569 : Blo 928581 96525569 := bstep (se 2 (by rfl) ⟨36197088, by rfl⟩ : syracuseStep 96525569 = 72394177) B72394177
theorem B2089583 : Blo 928581 2089583 := bstep (se 1 (by rfl) ⟨1567187, by rfl⟩ : syracuseStep 2089583 = 3134375) B3134375
theorem B2648047 : Blo 928581 2648047 := bstep (se 1 (by rfl) ⟨1986035, by rfl⟩ : syracuseStep 2648047 = 3972071) B3972071
theorem B28994273 : Blo 928581 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B1765631 : Blo 928581 1765631 := bstep (se 1 (by rfl) ⟨1324223, by rfl⟩ : syracuseStep 1765631 = 2648447) B2648447
theorem B3141935 : Blo 928581 3141935 := bstep (se 1 (by rfl) ⟨2356451, by rfl⟩ : syracuseStep 3141935 = 4712903) B4712903
theorem B2094587 : Blo 928581 2094587 := bstep (se 1 (by rfl) ⟨1570940, by rfl⟩ : syracuseStep 2094587 = 3141881) B3141881
theorem B2095343 : Blo 928581 2095343 := bstep (se 1 (by rfl) ⟨1571507, by rfl⟩ : syracuseStep 2095343 = 3143015) B3143015
theorem B2685793 : Blo 928581 2685793 := bstep (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) B2014345
theorem B3144959 : Blo 928581 3144959 := bstep (se 1 (by rfl) ⟨2358719, by rfl⟩ : syracuseStep 3144959 = 4717439) B4717439
theorem B1769465 : Blo 928581 1769465 := bstep (se 2 (by rfl) ⟨663549, by rfl⟩ : syracuseStep 1769465 = 1327099) B1327099
theorem B1048639 : Blo 928581 1048639 := bstep (se 1 (by rfl) ⟨786479, by rfl⟩ : syracuseStep 1048639 = 1572959) B1572959
theorem B1573087 : Blo 928581 1573087 := bstep (se 1 (by rfl) ⟨1179815, by rfl⟩ : syracuseStep 1573087 = 2359631) B2359631
theorem B3540617 : Blo 928581 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B8161847 : Blo 928581 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B6037199 : Blo 928581 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B3581057 : Blo 928581 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B1452671 : Blo 928581 1452671 := bstep (se 1 (by rfl) ⟨1089503, by rfl⟩ : syracuseStep 1452671 = 2179007) B2179007
theorem B929127 : Blo 928581 929127 := bstep (se 1 (by rfl) ⟨696845, by rfl⟩ : syracuseStep 929127 = 1393691) B1393691
theorem B930543 : Blo 928581 930543 := bstep (se 1 (by rfl) ⟨697907, by rfl⟩ : syracuseStep 930543 = 1395815) B1395815
theorem B930559 : Blo 928581 930559 := bstep (se 1 (by rfl) ⟨697919, by rfl⟩ : syracuseStep 930559 = 1395839) B1395839
theorem B930687 : Blo 928581 930687 := bstep (se 1 (by rfl) ⟨698015, by rfl⟩ : syracuseStep 930687 = 1396031) B1396031
theorem B7058663 : Blo 928581 7058663 := bstep (se 1 (by rfl) ⟨5293997, by rfl⟩ : syracuseStep 7058663 = 10587995) B10587995
theorem B4470041 : Blo 928581 4470041 := bstep (se 2 (by rfl) ⟨1676265, by rfl⟩ : syracuseStep 4470041 = 3352531) B3352531
theorem B1393055 : Blo 928581 1393055 := bstep (se 1 (by rfl) ⟨1044791, by rfl⟩ : syracuseStep 1393055 = 2089583) B2089583
theorem B1396391 : Blo 928581 1396391 := bstep (se 1 (by rfl) ⟨1047293, by rfl⟩ : syracuseStep 1396391 = 2094587) B2094587
theorem B25415369 : Blo 928581 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B1396895 : Blo 928581 1396895 := bstep (se 1 (by rfl) ⟨1047671, by rfl⟩ : syracuseStep 1396895 = 2095343) B2095343
theorem B5296367 : Blo 928581 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B2118313 : Blo 928581 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B102029291 : Blo 928581 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B5298281 : Blo 928581 5298281 := bstep (se 2 (by rfl) ⟨1986855, by rfl⟩ : syracuseStep 5298281 = 3973711) B3973711
theorem B3530729 : Blo 928581 3530729 := bstep (se 2 (by rfl) ⟨1324023, by rfl⟩ : syracuseStep 3530729 = 2648047) B2648047
theorem B4022455 : Blo 928581 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B2351663 : Blo 928581 2351663 := bstep (se 1 (by rfl) ⟨1763747, by rfl⟩ : syracuseStep 2351663 = 3527495) B3527495
theorem B2089727 : Blo 928581 2089727 := bstep (se 1 (by rfl) ⟨1567295, by rfl⟩ : syracuseStep 2089727 = 3134591) B3134591
theorem B64350379 : Blo 928581 64350379 := bstep (se 1 (by rfl) ⟨48262784, by rfl⟩ : syracuseStep 64350379 = 96525569) B96525569
theorem B19329515 : Blo 928581 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B1177087 : Blo 928581 1177087 := bstep (se 1 (by rfl) ⟨882815, by rfl⟩ : syracuseStep 1177087 = 1765631) B1765631
theorem B2094623 : Blo 928581 2094623 := bstep (se 1 (by rfl) ⟨1570967, by rfl⟩ : syracuseStep 2094623 = 3141935) B3141935
theorem B2096639 : Blo 928581 2096639 := bstep (se 1 (by rfl) ⟨1572479, by rfl⟩ : syracuseStep 2096639 = 3144959) B3144959
theorem B17006345 : Blo 928581 17006345 := bstep (se 2 (by rfl) ⟨6377379, by rfl⟩ : syracuseStep 17006345 = 12754759) B12754759
theorem B4718573 : Blo 928581 4718573 := bstep (se 3 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 4718573 = 1769465) B1769465
theorem B2097449 : Blo 928581 2097449 := bstep (se 2 (by rfl) ⟨786543, by rfl⟩ : syracuseStep 2097449 = 1573087) B1573087
theorem B2360411 : Blo 928581 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B5441231 : Blo 928581 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B16943579 : Blo 928581 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B2824417 : Blo 928581 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B12886343 : Blo 928581 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B928703 : Blo 928581 928703 := bstep (se 1 (by rfl) ⟨696527, by rfl⟩ : syracuseStep 928703 = 1393055) B1393055
theorem B930927 : Blo 928581 930927 := bstep (se 1 (by rfl) ⟨698195, by rfl⟩ : syracuseStep 930927 = 1396391) B1396391
theorem B931263 : Blo 928581 931263 := bstep (se 1 (by rfl) ⟨698447, by rfl⟩ : syracuseStep 931263 = 1396895) B1396895
theorem B85800505 : Blo 928581 85800505 := bstep (se 2 (by rfl) ⟨32175189, by rfl⟩ : syracuseStep 85800505 = 64350379) B64350379
theorem B9549485 : Blo 928581 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B1393151 : Blo 928581 1393151 := bstep (se 1 (by rfl) ⟨1044863, by rfl⟩ : syracuseStep 1393151 = 2089727) B2089727
theorem B968447 : Blo 928581 968447 := bstep (se 1 (by rfl) ⟨726335, by rfl⟩ : syracuseStep 968447 = 1452671) B1452671
theorem B4705775 : Blo 928581 4705775 := bstep (se 1 (by rfl) ⟨3529331, by rfl⟩ : syracuseStep 4705775 = 7058663) B7058663
theorem B1396415 : Blo 928581 1396415 := bstep (se 1 (by rfl) ⟨1047311, by rfl⟩ : syracuseStep 1396415 = 2094623) B2094623
theorem B1397759 : Blo 928581 1397759 := bstep (se 1 (by rfl) ⟨1048319, by rfl⟩ : syracuseStep 1397759 = 2096639) B2096639
theorem B1398185 : Blo 928581 1398185 := bstep (se 2 (by rfl) ⟨524319, by rfl⟩ : syracuseStep 1398185 = 1048639) B1048639
theorem B5363273 : Blo 928581 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B3530911 : Blo 928581 3530911 := bstep (se 1 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 3530911 = 5296367) B5296367
theorem B68019527 : Blo 928581 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B3532187 : Blo 928581 3532187 := bstep (se 1 (by rfl) ⟨2649140, by rfl⟩ : syracuseStep 3532187 = 5298281) B5298281
theorem B4024799 : Blo 928581 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B2353819 : Blo 928581 2353819 := bstep (se 1 (by rfl) ⟨1765364, by rfl⟩ : syracuseStep 2353819 = 3530729) B3530729
theorem B1567775 : Blo 928581 1567775 := bstep (se 1 (by rfl) ⟨1175831, by rfl⟩ : syracuseStep 1567775 = 2351663) B2351663
theorem B1569449 : Blo 928581 1569449 := bstep (se 2 (by rfl) ⟨588543, by rfl⟩ : syracuseStep 1569449 = 1177087) B1177087
theorem B2980027 : Blo 928581 2980027 := bstep (se 1 (by rfl) ⟨2235020, by rfl⟩ : syracuseStep 2980027 = 4470041) B4470041
theorem B11337563 : Blo 928581 11337563 := bstep (se 1 (by rfl) ⟨8503172, by rfl⟩ : syracuseStep 11337563 = 17006345) B17006345
theorem B3145715 : Blo 928581 3145715 := bstep (se 1 (by rfl) ⟨2359286, by rfl⟩ : syracuseStep 3145715 = 4718573) B4718573
theorem B1573607 : Blo 928581 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B3575515 : Blo 928581 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B8590895 : Blo 928581 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B114400673 : Blo 928581 114400673 := bstep (se 2 (by rfl) ⟨42900252, by rfl⟩ : syracuseStep 114400673 = 85800505) B85800505
theorem B3973369 : Blo 928581 3973369 := bstep (se 2 (by rfl) ⟨1490013, by rfl⟩ : syracuseStep 3973369 = 2980027) B2980027
theorem B6366323 : Blo 928581 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B928767 : Blo 928581 928767 := bstep (se 1 (by rfl) ⟨696575, by rfl⟩ : syracuseStep 928767 = 1393151) B1393151
theorem B930943 : Blo 928581 930943 := bstep (se 1 (by rfl) ⟨698207, by rfl⟩ : syracuseStep 930943 = 1396415) B1396415
theorem B931839 : Blo 928581 931839 := bstep (se 1 (by rfl) ⟨698879, by rfl⟩ : syracuseStep 931839 = 1397759) B1397759
theorem B932123 : Blo 928581 932123 := bstep (se 1 (by rfl) ⟨699092, by rfl⟩ : syracuseStep 932123 = 1398185) B1398185
theorem B7558375 : Blo 928581 7558375 := bstep (se 1 (by rfl) ⟨5668781, by rfl⟩ : syracuseStep 7558375 = 11337563) B11337563
theorem B1398299 : Blo 928581 1398299 := bstep (se 1 (by rfl) ⟨1048724, by rfl⟩ : syracuseStep 1398299 = 2097449) B2097449
theorem B4707881 : Blo 928581 4707881 := bstep (se 2 (by rfl) ⟨1765455, by rfl⟩ : syracuseStep 4707881 = 3530911) B3530911
theorem B3627487 : Blo 928581 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B11295719 : Blo 928581 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B3137183 : Blo 928581 3137183 := bstep (se 1 (by rfl) ⟨2352887, by rfl⟩ : syracuseStep 3137183 = 4705775) B4705775
theorem B3138425 : Blo 928581 3138425 := bstep (se 2 (by rfl) ⟨1176909, by rfl⟩ : syracuseStep 3138425 = 2353819) B2353819
theorem B2582525 : Blo 928581 2582525 := bstep (se 3 (by rfl) ⟨484223, by rfl⟩ : syracuseStep 2582525 = 968447) B968447
theorem B45346351 : Blo 928581 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B2354791 : Blo 928581 2354791 := bstep (se 1 (by rfl) ⟨1766093, by rfl⟩ : syracuseStep 2354791 = 3532187) B3532187
theorem B2683199 : Blo 928581 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B1045183 : Blo 928581 1045183 := bstep (se 1 (by rfl) ⟨783887, by rfl⟩ : syracuseStep 1045183 = 1567775) B1567775
theorem B3765889 : Blo 928581 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B1046299 : Blo 928581 1046299 := bstep (se 1 (by rfl) ⟨784724, by rfl⟩ : syracuseStep 1046299 = 1569449) B1569449
theorem B2097143 : Blo 928581 2097143 := bstep (se 1 (by rfl) ⟨1572857, by rfl⟩ : syracuseStep 2097143 = 3145715) B3145715
theorem B1049071 : Blo 928581 1049071 := bstep (se 1 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 1049071 = 1573607) B1573607
theorem B16976861 : Blo 928581 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B60461801 : Blo 928581 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B5021185 : Blo 928581 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B19346597 : Blo 928581 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B932199 : Blo 928581 932199 := bstep (se 1 (by rfl) ⟨699149, by rfl⟩ : syracuseStep 932199 = 1398299) B1398299
theorem B76267115 : Blo 928581 76267115 := bstep (se 1 (by rfl) ⟨57200336, by rfl⟩ : syracuseStep 76267115 = 114400673) B114400673
theorem B4767353 : Blo 928581 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B1393577 : Blo 928581 1393577 := bstep (se 2 (by rfl) ⟨522591, by rfl⟩ : syracuseStep 1393577 = 1045183) B1045183
theorem B1721683 : Blo 928581 1721683 := bstep (se 1 (by rfl) ⟨1291262, by rfl⟩ : syracuseStep 1721683 = 2582525) B2582525
theorem B10077833 : Blo 928581 10077833 := bstep (se 2 (by rfl) ⟨3779187, by rfl⟩ : syracuseStep 10077833 = 7558375) B7558375
theorem B1395065 : Blo 928581 1395065 := bstep (se 2 (by rfl) ⟨523149, by rfl⟩ : syracuseStep 1395065 = 1046299) B1046299
theorem B1788799 : Blo 928581 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B1398095 : Blo 928581 1398095 := bstep (se 1 (by rfl) ⟨1048571, by rfl⟩ : syracuseStep 1398095 = 2097143) B2097143
theorem B5297825 : Blo 928581 5297825 := bstep (se 2 (by rfl) ⟨1986684, by rfl⟩ : syracuseStep 5297825 = 3973369) B3973369
theorem B3138587 : Blo 928581 3138587 := bstep (se 1 (by rfl) ⟨2353940, by rfl⟩ : syracuseStep 3138587 = 4707881) B4707881
theorem B5727263 : Blo 928581 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B7530479 : Blo 928581 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B3139721 : Blo 928581 3139721 := bstep (se 2 (by rfl) ⟨1177395, by rfl⟩ : syracuseStep 3139721 = 2354791) B2354791
theorem B2091455 : Blo 928581 2091455 := bstep (se 1 (by rfl) ⟨1568591, by rfl⟩ : syracuseStep 2091455 = 3137183) B3137183
theorem B2092283 : Blo 928581 2092283 := bstep (se 1 (by rfl) ⟨1569212, by rfl⟩ : syracuseStep 2092283 = 3138425) B3138425
theorem B6718555 : Blo 928581 6718555 := bstep (se 1 (by rfl) ⟨5038916, by rfl⟩ : syracuseStep 6718555 = 10077833) B10077833
theorem B2295577 : Blo 928581 2295577 := bstep (se 2 (by rfl) ⟨860841, by rfl⟩ : syracuseStep 2295577 = 1721683) B1721683
theorem B15272701 : Blo 928581 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B40307867 : Blo 928581 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B5020319 : Blo 928581 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B6694913 : Blo 928581 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B929051 : Blo 928581 929051 := bstep (se 1 (by rfl) ⟨696788, by rfl⟩ : syracuseStep 929051 = 1393577) B1393577
theorem B930043 : Blo 928581 930043 := bstep (se 1 (by rfl) ⟨697532, by rfl⟩ : syracuseStep 930043 = 1395065) B1395065
theorem B11317907 : Blo 928581 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B932063 : Blo 928581 932063 := bstep (se 1 (by rfl) ⟨699047, by rfl⟩ : syracuseStep 932063 = 1398095) B1398095
theorem B1394303 : Blo 928581 1394303 := bstep (se 1 (by rfl) ⟨1045727, by rfl⟩ : syracuseStep 1394303 = 2091455) B2091455
theorem B1394855 : Blo 928581 1394855 := bstep (se 1 (by rfl) ⟨1046141, by rfl⟩ : syracuseStep 1394855 = 2092283) B2092283
theorem B12897731 : Blo 928581 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B50844743 : Blo 928581 50844743 := bstep (se 1 (by rfl) ⟨38133557, by rfl⟩ : syracuseStep 50844743 = 76267115) B76267115
theorem B1398761 : Blo 928581 1398761 := bstep (se 2 (by rfl) ⟨524535, by rfl⟩ : syracuseStep 1398761 = 1049071) B1049071
theorem B3531883 : Blo 928581 3531883 := bstep (se 1 (by rfl) ⟨2648912, by rfl⟩ : syracuseStep 3531883 = 5297825) B5297825
theorem B2385065 : Blo 928581 2385065 := bstep (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) B1788799
theorem B2092391 : Blo 928581 2092391 := bstep (se 1 (by rfl) ⟨1569293, by rfl⟩ : syracuseStep 2092391 = 3138587) B3138587
theorem B2093147 : Blo 928581 2093147 := bstep (se 1 (by rfl) ⟨1569860, by rfl⟩ : syracuseStep 2093147 = 3139721) B3139721
theorem B3178235 : Blo 928581 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B26871911 : Blo 928581 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B4463275 : Blo 928581 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B7545271 : Blo 928581 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B929535 : Blo 928581 929535 := bstep (se 1 (by rfl) ⟨697151, by rfl⟩ : syracuseStep 929535 = 1394303) B1394303
theorem B929903 : Blo 928581 929903 := bstep (se 1 (by rfl) ⟨697427, by rfl⟩ : syracuseStep 929903 = 1394855) B1394855
theorem B8958073 : Blo 928581 8958073 := bstep (se 2 (by rfl) ⟨3359277, by rfl⟩ : syracuseStep 8958073 = 6718555) B6718555
theorem B8598487 : Blo 928581 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B33896495 : Blo 928581 33896495 := bstep (se 1 (by rfl) ⟨25422371, by rfl⟩ : syracuseStep 33896495 = 50844743) B50844743
theorem B932507 : Blo 928581 932507 := bstep (se 1 (by rfl) ⟨699380, by rfl⟩ : syracuseStep 932507 = 1398761) B1398761
theorem B1590043 : Blo 928581 1590043 := bstep (se 1 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 1590043 = 2385065) B2385065
theorem B13387517 : Blo 928581 13387517 := bstep (se 3 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 13387517 = 5020319) B5020319
theorem B1394927 : Blo 928581 1394927 := bstep (se 1 (by rfl) ⟨1046195, by rfl⟩ : syracuseStep 1394927 = 2092391) B2092391
theorem B1395431 : Blo 928581 1395431 := bstep (se 1 (by rfl) ⟨1046573, by rfl⟩ : syracuseStep 1395431 = 2093147) B2093147
theorem B12243077 : Blo 928581 12243077 := bstep (se 4 (by rfl) ⟨1147788, by rfl⟩ : syracuseStep 12243077 = 2295577) B2295577
theorem B8475293 : Blo 928581 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B4709177 : Blo 928581 4709177 := bstep (se 2 (by rfl) ⟨1765941, by rfl⟩ : syracuseStep 4709177 = 3531883) B3531883
theorem B81454405 : Blo 928581 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B10060361 : Blo 928581 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B8162051 : Blo 928581 8162051 := bstep (se 1 (by rfl) ⟨6121538, by rfl⟩ : syracuseStep 8162051 = 12243077) B12243077
theorem B8925011 : Blo 928581 8925011 := bstep (se 1 (by rfl) ⟨6693758, by rfl⟩ : syracuseStep 8925011 = 13387517) B13387517
theorem B929951 : Blo 928581 929951 := bstep (se 1 (by rfl) ⟨697463, by rfl⟩ : syracuseStep 929951 = 1394927) B1394927
theorem B108605873 : Blo 928581 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B930287 : Blo 928581 930287 := bstep (se 1 (by rfl) ⟨697715, by rfl⟩ : syracuseStep 930287 = 1395431) B1395431
theorem B5650195 : Blo 928581 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B11944097 : Blo 928581 11944097 := bstep (se 2 (by rfl) ⟨4479036, by rfl⟩ : syracuseStep 11944097 = 8958073) B8958073
theorem B5951033 : Blo 928581 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B22597663 : Blo 928581 22597663 := bstep (se 1 (by rfl) ⟨16948247, by rfl⟩ : syracuseStep 22597663 = 33896495) B33896495
theorem B2120057 : Blo 928581 2120057 := bstep (se 2 (by rfl) ⟨795021, by rfl⟩ : syracuseStep 2120057 = 1590043) B1590043
theorem B17914607 : Blo 928581 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B3139451 : Blo 928581 3139451 := bstep (se 1 (by rfl) ⟨2354588, by rfl⟩ : syracuseStep 3139451 = 4709177) B4709177
theorem B11464649 : Blo 928581 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B7962731 : Blo 928581 7962731 := bstep (se 1 (by rfl) ⟨5972048, by rfl⟩ : syracuseStep 7962731 = 11944097) B11944097
theorem B3967355 : Blo 928581 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B1413371 : Blo 928581 1413371 := bstep (se 1 (by rfl) ⟨1060028, by rfl⟩ : syracuseStep 1413371 = 2120057) B2120057
theorem B21765469 : Blo 928581 21765469 := bstep (se 3 (by rfl) ⟨4081025, by rfl⟩ : syracuseStep 21765469 = 8162051) B8162051
theorem B7643099 : Blo 928581 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B11943071 : Blo 928581 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B30130217 : Blo 928581 30130217 := bstep (se 2 (by rfl) ⟨11298831, by rfl⟩ : syracuseStep 30130217 = 22597663) B22597663
theorem B5950007 : Blo 928581 5950007 := bstep (se 1 (by rfl) ⟨4462505, by rfl⟩ : syracuseStep 5950007 = 8925011) B8925011
theorem B72403915 : Blo 928581 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B6706907 : Blo 928581 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B2092967 : Blo 928581 2092967 := bstep (se 1 (by rfl) ⟨1569725, by rfl⟩ : syracuseStep 2092967 = 3139451) B3139451
theorem B7533593 : Blo 928581 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B20086811 : Blo 928581 20086811 := bstep (se 1 (by rfl) ⟨15065108, by rfl⟩ : syracuseStep 20086811 = 30130217) B30130217
theorem B5308487 : Blo 928581 5308487 := bstep (se 1 (by rfl) ⟨3981365, by rfl⟩ : syracuseStep 5308487 = 7962731) B7962731
theorem B3966671 : Blo 928581 3966671 := bstep (se 1 (by rfl) ⟨2975003, by rfl⟩ : syracuseStep 3966671 = 5950007) B5950007
theorem B96538553 : Blo 928581 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B5022395 : Blo 928581 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B4471271 : Blo 928581 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B5095399 : Blo 928581 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B1395311 : Blo 928581 1395311 := bstep (se 1 (by rfl) ⟨1046483, by rfl⟩ : syracuseStep 1395311 = 2092967) B2092967
theorem B29020625 : Blo 928581 29020625 := bstep (se 2 (by rfl) ⟨10882734, by rfl⟩ : syracuseStep 29020625 = 21765469) B21765469
theorem B2644903 : Blo 928581 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B942247 : Blo 928581 942247 := bstep (se 1 (by rfl) ⟨706685, by rfl⟩ : syracuseStep 942247 = 1413371) B1413371
theorem B7962047 : Blo 928581 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B3538991 : Blo 928581 3538991 := bstep (se 1 (by rfl) ⟨2654243, by rfl⟩ : syracuseStep 3538991 = 5308487) B5308487
theorem B64359035 : Blo 928581 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B3348263 : Blo 928581 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B6793865 : Blo 928581 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B1256329 : Blo 928581 1256329 := bstep (se 2 (by rfl) ⟨471123, by rfl⟩ : syracuseStep 1256329 = 942247) B942247
theorem B930207 : Blo 928581 930207 := bstep (se 1 (by rfl) ⟨697655, by rfl⟩ : syracuseStep 930207 = 1395311) B1395311
theorem B19347083 : Blo 928581 19347083 := bstep (se 1 (by rfl) ⟨14510312, by rfl⟩ : syracuseStep 19347083 = 29020625) B29020625
theorem B3526537 : Blo 928581 3526537 := bstep (se 2 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 3526537 = 2644903) B2644903
theorem B13391207 : Blo 928581 13391207 := bstep (se 1 (by rfl) ⟨10043405, by rfl⟩ : syracuseStep 13391207 = 20086811) B20086811
theorem B10577789 : Blo 928581 10577789 := bstep (se 3 (by rfl) ⟨1983335, by rfl⟩ : syracuseStep 10577789 = 3966671) B3966671
theorem B2980847 : Blo 928581 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B5308031 : Blo 928581 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B2359327 : Blo 928581 2359327 := bstep (se 1 (by rfl) ⟨1769495, by rfl⟩ : syracuseStep 2359327 = 3538991) B3538991
theorem B7051859 : Blo 928581 7051859 := bstep (se 1 (by rfl) ⟨5288894, by rfl⟩ : syracuseStep 7051859 = 10577789) B10577789
theorem B4529243 : Blo 928581 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B42906023 : Blo 928581 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B8927471 : Blo 928581 8927471 := bstep (se 1 (by rfl) ⟨6695603, by rfl⟩ : syracuseStep 8927471 = 13391207) B13391207
theorem B6700421 : Blo 928581 6700421 := bstep (se 4 (by rfl) ⟨628164, by rfl⟩ : syracuseStep 6700421 = 1256329) B1256329
theorem B8928701 : Blo 928581 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B4702049 : Blo 928581 4702049 := bstep (se 2 (by rfl) ⟨1763268, by rfl⟩ : syracuseStep 4702049 = 3526537) B3526537
theorem B7948925 : Blo 928581 7948925 := bstep (se 3 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 7948925 = 2980847) B2980847
theorem B12898055 : Blo 928581 12898055 := bstep (se 1 (by rfl) ⟨9673541, by rfl⟩ : syracuseStep 12898055 = 19347083) B19347083
theorem B3538687 : Blo 928581 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B3145769 : Blo 928581 3145769 := bstep (se 2 (by rfl) ⟨1179663, by rfl⟩ : syracuseStep 3145769 = 2359327) B2359327
theorem B17867789 : Blo 928581 17867789 := bstep (se 3 (by rfl) ⟨3350210, by rfl⟩ : syracuseStep 17867789 = 6700421) B6700421
theorem B4701239 : Blo 928581 4701239 := bstep (se 1 (by rfl) ⟨3525929, by rfl⟩ : syracuseStep 4701239 = 7051859) B7051859
theorem B12077981 : Blo 928581 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B5951647 : Blo 928581 5951647 := bstep (se 1 (by rfl) ⟨4463735, by rfl⟩ : syracuseStep 5951647 = 8927471) B8927471
theorem B34394813 : Blo 928581 34394813 := bstep (se 3 (by rfl) ⟨6449027, by rfl⟩ : syracuseStep 34394813 = 12898055) B12898055
theorem B5952467 : Blo 928581 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B3134699 : Blo 928581 3134699 := bstep (se 1 (by rfl) ⟨2351024, by rfl⟩ : syracuseStep 3134699 = 4702049) B4702049
theorem B5299283 : Blo 928581 5299283 := bstep (se 1 (by rfl) ⟨3974462, by rfl⟩ : syracuseStep 5299283 = 7948925) B7948925
theorem B28604015 : Blo 928581 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B4718249 : Blo 928581 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B2097179 : Blo 928581 2097179 := bstep (se 1 (by rfl) ⟨1572884, by rfl⟩ : syracuseStep 2097179 = 3145769) B3145769
theorem B7935529 : Blo 928581 7935529 := bstep (se 2 (by rfl) ⟨2975823, by rfl⟩ : syracuseStep 7935529 = 5951647) B5951647
theorem B15873245 : Blo 928581 15873245 := bstep (se 3 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 15873245 = 5952467) B5952467
theorem B11911859 : Blo 928581 11911859 := bstep (se 1 (by rfl) ⟨8933894, by rfl⟩ : syracuseStep 11911859 = 17867789) B17867789
theorem B3134159 : Blo 928581 3134159 := bstep (se 1 (by rfl) ⟨2350619, by rfl⟩ : syracuseStep 3134159 = 4701239) B4701239
theorem B8051987 : Blo 928581 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B22929875 : Blo 928581 22929875 := bstep (se 1 (by rfl) ⟨17197406, by rfl⟩ : syracuseStep 22929875 = 34394813) B34394813
theorem B2089799 : Blo 928581 2089799 := bstep (se 1 (by rfl) ⟨1567349, by rfl⟩ : syracuseStep 2089799 = 3134699) B3134699
theorem B3532855 : Blo 928581 3532855 := bstep (se 1 (by rfl) ⟨2649641, by rfl⟩ : syracuseStep 3532855 = 5299283) B5299283
theorem B19069343 : Blo 928581 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B3145499 : Blo 928581 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B7941239 : Blo 928581 7941239 := bstep (se 1 (by rfl) ⟨5955929, by rfl⟩ : syracuseStep 7941239 = 11911859) B11911859
theorem B15286583 : Blo 928581 15286583 := bstep (se 1 (by rfl) ⟨11464937, by rfl⟩ : syracuseStep 15286583 = 22929875) B22929875
theorem B1393199 : Blo 928581 1393199 := bstep (se 1 (by rfl) ⟨1044899, by rfl⟩ : syracuseStep 1393199 = 2089799) B2089799
theorem B1398119 : Blo 928581 1398119 := bstep (se 1 (by rfl) ⟨1048589, by rfl⟩ : syracuseStep 1398119 = 2097179) B2097179
theorem B4710473 : Blo 928581 4710473 := bstep (se 2 (by rfl) ⟨1766427, by rfl⟩ : syracuseStep 4710473 = 3532855) B3532855
theorem B2089439 : Blo 928581 2089439 := bstep (se 1 (by rfl) ⟨1567079, by rfl⟩ : syracuseStep 2089439 = 3134159) B3134159
theorem B5367991 : Blo 928581 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B10580705 : Blo 928581 10580705 := bstep (se 2 (by rfl) ⟨3967764, by rfl⟩ : syracuseStep 10580705 = 7935529) B7935529
theorem B10582163 : Blo 928581 10582163 := bstep (se 1 (by rfl) ⟨7936622, by rfl⟩ : syracuseStep 10582163 = 15873245) B15873245
theorem B12712895 : Blo 928581 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B2096999 : Blo 928581 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B10191055 : Blo 928581 10191055 := bstep (se 1 (by rfl) ⟨7643291, by rfl⟩ : syracuseStep 10191055 = 15286583) B15286583
theorem B7053803 : Blo 928581 7053803 := bstep (se 1 (by rfl) ⟨5290352, by rfl⟩ : syracuseStep 7053803 = 10580705) B10580705
theorem B7054775 : Blo 928581 7054775 := bstep (se 1 (by rfl) ⟨5291081, by rfl⟩ : syracuseStep 7054775 = 10582163) B10582163
theorem B928799 : Blo 928581 928799 := bstep (se 1 (by rfl) ⟨696599, by rfl⟩ : syracuseStep 928799 = 1393199) B1393199
theorem B7157321 : Blo 928581 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B932079 : Blo 928581 932079 := bstep (se 1 (by rfl) ⟨699059, by rfl⟩ : syracuseStep 932079 = 1398119) B1398119
theorem B1392959 : Blo 928581 1392959 := bstep (se 1 (by rfl) ⟨1044719, by rfl⟩ : syracuseStep 1392959 = 2089439) B2089439
theorem B5294159 : Blo 928581 5294159 := bstep (se 1 (by rfl) ⟨3970619, by rfl⟩ : syracuseStep 5294159 = 7941239) B7941239
theorem B8475263 : Blo 928581 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B1397999 : Blo 928581 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B3140315 : Blo 928581 3140315 := bstep (se 1 (by rfl) ⟨2355236, by rfl⟩ : syracuseStep 3140315 = 4710473) B4710473
theorem B928639 : Blo 928581 928639 := bstep (se 1 (by rfl) ⟨696479, by rfl⟩ : syracuseStep 928639 = 1392959) B1392959
theorem B5650175 : Blo 928581 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B931999 : Blo 928581 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B4702535 : Blo 928581 4702535 := bstep (se 1 (by rfl) ⟨3526901, by rfl⟩ : syracuseStep 4702535 = 7053803) B7053803
theorem B4703183 : Blo 928581 4703183 := bstep (se 1 (by rfl) ⟨3527387, by rfl⟩ : syracuseStep 4703183 = 7054775) B7054775
theorem B4771547 : Blo 928581 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B13588073 : Blo 928581 13588073 := bstep (se 2 (by rfl) ⟨5095527, by rfl⟩ : syracuseStep 13588073 = 10191055) B10191055
theorem B3529439 : Blo 928581 3529439 := bstep (se 1 (by rfl) ⟨2647079, by rfl⟩ : syracuseStep 3529439 = 5294159) B5294159
theorem B2093543 : Blo 928581 2093543 := bstep (se 1 (by rfl) ⟨1570157, by rfl⟩ : syracuseStep 2093543 = 3140315) B3140315
theorem B3181031 : Blo 928581 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B9058715 : Blo 928581 9058715 := bstep (se 1 (by rfl) ⟨6794036, by rfl⟩ : syracuseStep 9058715 = 13588073) B13588073
theorem B1395695 : Blo 928581 1395695 := bstep (se 1 (by rfl) ⟨1046771, by rfl⟩ : syracuseStep 1395695 = 2093543) B2093543
theorem B3135023 : Blo 928581 3135023 := bstep (se 1 (by rfl) ⟨2351267, by rfl⟩ : syracuseStep 3135023 = 4702535) B4702535
theorem B3135455 : Blo 928581 3135455 := bstep (se 1 (by rfl) ⟨2351591, by rfl⟩ : syracuseStep 3135455 = 4703183) B4703183
theorem B2352959 : Blo 928581 2352959 := bstep (se 1 (by rfl) ⟨1764719, by rfl⟩ : syracuseStep 2352959 = 3529439) B3529439
theorem B15067133 : Blo 928581 15067133 := bstep (se 3 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 15067133 = 5650175) B5650175
theorem B6039143 : Blo 928581 6039143 := bstep (se 1 (by rfl) ⟨4529357, by rfl⟩ : syracuseStep 6039143 = 9058715) B9058715
theorem B930463 : Blo 928581 930463 := bstep (se 1 (by rfl) ⟨697847, by rfl⟩ : syracuseStep 930463 = 1395695) B1395695
theorem B10044755 : Blo 928581 10044755 := bstep (se 1 (by rfl) ⟨7533566, by rfl⟩ : syracuseStep 10044755 = 15067133) B15067133
theorem B2120687 : Blo 928581 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B2090015 : Blo 928581 2090015 := bstep (se 1 (by rfl) ⟨1567511, by rfl⟩ : syracuseStep 2090015 = 3135023) B3135023
theorem B2090303 : Blo 928581 2090303 := bstep (se 1 (by rfl) ⟨1567727, by rfl⟩ : syracuseStep 2090303 = 3135455) B3135455
theorem B1568639 : Blo 928581 1568639 := bstep (se 1 (by rfl) ⟨1176479, by rfl⟩ : syracuseStep 1568639 = 2352959) B2352959
theorem B1413791 : Blo 928581 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B6696503 : Blo 928581 6696503 := bstep (se 1 (by rfl) ⟨5022377, by rfl⟩ : syracuseStep 6696503 = 10044755) B10044755
theorem B1393343 : Blo 928581 1393343 := bstep (se 1 (by rfl) ⟨1045007, by rfl⟩ : syracuseStep 1393343 = 2090015) B2090015
theorem B1393535 : Blo 928581 1393535 := bstep (se 1 (by rfl) ⟨1045151, by rfl⟩ : syracuseStep 1393535 = 2090303) B2090303
theorem B4026095 : Blo 928581 4026095 := bstep (se 1 (by rfl) ⟨3019571, by rfl⟩ : syracuseStep 4026095 = 6039143) B6039143
theorem B1045759 : Blo 928581 1045759 := bstep (se 1 (by rfl) ⟨784319, by rfl⟩ : syracuseStep 1045759 = 1568639) B1568639
theorem B4464335 : Blo 928581 4464335 := bstep (se 1 (by rfl) ⟨3348251, by rfl⟩ : syracuseStep 4464335 = 6696503) B6696503
theorem B928895 : Blo 928581 928895 := bstep (se 1 (by rfl) ⟨696671, by rfl⟩ : syracuseStep 928895 = 1393343) B1393343
theorem B929023 : Blo 928581 929023 := bstep (se 1 (by rfl) ⟨696767, by rfl⟩ : syracuseStep 929023 = 1393535) B1393535
theorem B1394345 : Blo 928581 1394345 := bstep (se 2 (by rfl) ⟨522879, by rfl⟩ : syracuseStep 1394345 = 1045759) B1045759
theorem B942527 : Blo 928581 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B2684063 : Blo 928581 2684063 := bstep (se 1 (by rfl) ⟨2013047, by rfl⟩ : syracuseStep 2684063 = 4026095) B4026095
theorem B929563 : Blo 928581 929563 := bstep (se 1 (by rfl) ⟨697172, by rfl⟩ : syracuseStep 929563 = 1394345) B1394345
theorem B7157501 : Blo 928581 7157501 := bstep (se 3 (by rfl) ⟨1342031, by rfl⟩ : syracuseStep 7157501 = 2684063) B2684063
theorem B2513405 : Blo 928581 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B2976223 : Blo 928581 2976223 := bstep (se 1 (by rfl) ⟨2232167, by rfl⟩ : syracuseStep 2976223 = 4464335) B4464335
theorem B3968297 : Blo 928581 3968297 := bstep (se 2 (by rfl) ⟨1488111, by rfl⟩ : syracuseStep 3968297 = 2976223) B2976223
theorem B1675603 : Blo 928581 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B4771667 : Blo 928581 4771667 := bstep (se 1 (by rfl) ⟨3578750, by rfl⟩ : syracuseStep 4771667 = 7157501) B7157501
theorem B2234137 : Blo 928581 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B12724445 : Blo 928581 12724445 := bstep (se 3 (by rfl) ⟨2385833, by rfl⟩ : syracuseStep 12724445 = 4771667) B4771667
theorem B2645531 : Blo 928581 2645531 := bstep (se 1 (by rfl) ⟨1984148, by rfl⟩ : syracuseStep 2645531 = 3968297) B3968297
theorem B1763687 : Blo 928581 1763687 := bstep (se 1 (by rfl) ⟨1322765, by rfl⟩ : syracuseStep 1763687 = 2645531) B2645531
theorem B8482963 : Blo 928581 8482963 := bstep (se 1 (by rfl) ⟨6362222, by rfl⟩ : syracuseStep 8482963 = 12724445) B12724445
theorem B2978849 : Blo 928581 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B11310617 : Blo 928581 11310617 := bstep (se 2 (by rfl) ⟨4241481, by rfl⟩ : syracuseStep 11310617 = 8482963) B8482963
theorem B1985899 : Blo 928581 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B1175791 : Blo 928581 1175791 := bstep (se 1 (by rfl) ⟨881843, by rfl⟩ : syracuseStep 1175791 = 1763687) B1763687
theorem B7540411 : Blo 928581 7540411 := bstep (se 1 (by rfl) ⟨5655308, by rfl⟩ : syracuseStep 7540411 = 11310617) B11310617
theorem B2647865 : Blo 928581 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B1567721 : Blo 928581 1567721 := bstep (se 2 (by rfl) ⟨587895, by rfl⟩ : syracuseStep 1567721 = 1175791) B1175791
theorem B10053881 : Blo 928581 10053881 := bstep (se 2 (by rfl) ⟨3770205, by rfl⟩ : syracuseStep 10053881 = 7540411) B7540411
theorem B1765243 : Blo 928581 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B1045147 : Blo 928581 1045147 := bstep (se 1 (by rfl) ⟨783860, by rfl⟩ : syracuseStep 1045147 = 1567721) B1567721
theorem B1393529 : Blo 928581 1393529 := bstep (se 2 (by rfl) ⟨522573, by rfl⟩ : syracuseStep 1393529 = 1045147) B1045147
theorem B6702587 : Blo 928581 6702587 := bstep (se 1 (by rfl) ⟨5026940, by rfl⟩ : syracuseStep 6702587 = 10053881) B10053881
theorem B2353657 : Blo 928581 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B929019 : Blo 928581 929019 := bstep (se 1 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 929019 = 1393529) B1393529
theorem B4468391 : Blo 928581 4468391 := bstep (se 1 (by rfl) ⟨3351293, by rfl⟩ : syracuseStep 4468391 = 6702587) B6702587
theorem B3138209 : Blo 928581 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B2092139 : Blo 928581 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B2978927 : Blo 928581 2978927 := bstep (se 1 (by rfl) ⟨2234195, by rfl⟩ : syracuseStep 2978927 = 4468391) B4468391
theorem B1394759 : Blo 928581 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B1985951 : Blo 928581 1985951 := bstep (se 1 (by rfl) ⟨1489463, by rfl⟩ : syracuseStep 1985951 = 2978927) B2978927
theorem B929839 : Blo 928581 929839 := bstep (se 1 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 929839 = 1394759) B1394759
theorem B1323967 : Blo 928581 1323967 := bstep (se 1 (by rfl) ⟨992975, by rfl⟩ : syracuseStep 1323967 = 1985951) B1985951
theorem B1765289 : Blo 928581 1765289 := bstep (se 2 (by rfl) ⟨661983, by rfl⟩ : syracuseStep 1765289 = 1323967) B1323967
theorem B1176859 : Blo 928581 1176859 := bstep (se 1 (by rfl) ⟨882644, by rfl⟩ : syracuseStep 1176859 = 1765289) B1765289
theorem B1569145 : Blo 928581 1569145 := bstep (se 2 (by rfl) ⟨588429, by rfl⟩ : syracuseStep 1569145 = 1176859) B1176859
theorem B2092193 : Blo 928581 2092193 := bstep (se 2 (by rfl) ⟨784572, by rfl⟩ : syracuseStep 2092193 = 1569145) B1569145
theorem B1394795 : Blo 928581 1394795 := bstep (se 1 (by rfl) ⟨1046096, by rfl⟩ : syracuseStep 1394795 = 2092193) B2092193
theorem B929863 : Blo 928581 929863 := bstep (se 1 (by rfl) ⟨697397, by rfl⟩ : syracuseStep 929863 = 1394795) B1394795

theorem C0 (j : ℕ) (h1 : 232145 ≤ j) (h2 : j ≤ 232844) : Blo 928581 (4 * j + 3) := by
  interval_cases j
  · exact B928583
  · exact B928587
  · exact B928591
  · exact B928595
  · exact B928599
  · exact B928603
  · exact B928607
  · exact B928611
  · exact B928615
  · exact B928619
  · exact B928623
  · exact B928627
  · exact B928631
  · exact B928635
  · exact B928639
  · exact B928643
  · exact B928647
  · exact B928651
  · exact B928655
  · exact B928659
  · exact B928663
  · exact B928667
  · exact B928671
  · exact B928675
  · exact B928679
  · exact B928683
  · exact B928687
  · exact B928691
  · exact B928695
  · exact B928699
  · exact B928703
  · exact B928707
  · exact B928711
  · exact B928715
  · exact B928719
  · exact B928723
  · exact B928727
  · exact B928731
  · exact B928735
  · exact B928739
  · exact B928743
  · exact B928747
  · exact B928751
  · exact B928755
  · exact B928759
  · exact B928763
  · exact B928767
  · exact B928771
  · exact B928775
  · exact B928779
  · exact B928783
  · exact B928787
  · exact B928791
  · exact B928795
  · exact B928799
  · exact B928803
  · exact B928807
  · exact B928811
  · exact B928815
  · exact B928819
  · exact B928823
  · exact B928827
  · exact B928831
  · exact B928835
  · exact B928839
  · exact B928843
  · exact B928847
  · exact B928851
  · exact B928855
  · exact B928859
  · exact B928863
  · exact B928867
  · exact B928871
  · exact B928875
  · exact B928879
  · exact B928883
  · exact B928887
  · exact B928891
  · exact B928895
  · exact B928899
  · exact B928903
  · exact B928907
  · exact B928911
  · exact B928915
  · exact B928919
  · exact B928923
  · exact B928927
  · exact B928931
  · exact B928935
  · exact B928939
  · exact B928943
  · exact B928947
  · exact B928951
  · exact B928955
  · exact B928959
  · exact B928963
  · exact B928967
  · exact B928971
  · exact B928975
  · exact B928979
  · exact B928983
  · exact B928987
  · exact B928991
  · exact B928995
  · exact B928999
  · exact B929003
  · exact B929007
  · exact B929011
  · exact B929015
  · exact B929019
  · exact B929023
  · exact B929027
  · exact B929031
  · exact B929035
  · exact B929039
  · exact B929043
  · exact B929047
  · exact B929051
  · exact B929055
  · exact B929059
  · exact B929063
  · exact B929067
  · exact B929071
  · exact B929075
  · exact B929079
  · exact B929083
  · exact B929087
  · exact B929091
  · exact B929095
  · exact B929099
  · exact B929103
  · exact B929107
  · exact B929111
  · exact B929115
  · exact B929119
  · exact B929123
  · exact B929127
  · exact B929131
  · exact B929135
  · exact B929139
  · exact B929143
  · exact B929147
  · exact B929151
  · exact B929155
  · exact B929159
  · exact B929163
  · exact B929167
  · exact B929171
  · exact B929175
  · exact B929179
  · exact B929183
  · exact B929187
  · exact B929191
  · exact B929195
  · exact B929199
  · exact B929203
  · exact B929207
  · exact B929211
  · exact B929215
  · exact B929219
  · exact B929223
  · exact B929227
  · exact B929231
  · exact B929235
  · exact B929239
  · exact B929243
  · exact B929247
  · exact B929251
  · exact B929255
  · exact B929259
  · exact B929263
  · exact B929267
  · exact B929271
  · exact B929275
  · exact B929279
  · exact B929283
  · exact B929287
  · exact B929291
  · exact B929295
  · exact B929299
  · exact B929303
  · exact B929307
  · exact B929311
  · exact B929315
  · exact B929319
  · exact B929323
  · exact B929327
  · exact B929331
  · exact B929335
  · exact B929339
  · exact B929343
  · exact B929347
  · exact B929351
  · exact B929355
  · exact B929359
  · exact B929363
  · exact B929367
  · exact B929371
  · exact B929375
  · exact B929379
  · exact B929383
  · exact B929387
  · exact B929391
  · exact B929395
  · exact B929399
  · exact B929403
  · exact B929407
  · exact B929411
  · exact B929415
  · exact B929419
  · exact B929423
  · exact B929427
  · exact B929431
  · exact B929435
  · exact B929439
  · exact B929443
  · exact B929447
  · exact B929451
  · exact B929455
  · exact B929459
  · exact B929463
  · exact B929467
  · exact B929471
  · exact B929475
  · exact B929479
  · exact B929483
  · exact B929487
  · exact B929491
  · exact B929495
  · exact B929499
  · exact B929503
  · exact B929507
  · exact B929511
  · exact B929515
  · exact B929519
  · exact B929523
  · exact B929527
  · exact B929531
  · exact B929535
  · exact B929539
  · exact B929543
  · exact B929547
  · exact B929551
  · exact B929555
  · exact B929559
  · exact B929563
  · exact B929567
  · exact B929571
  · exact B929575
  · exact B929579
  · exact B929583
  · exact B929587
  · exact B929591
  · exact B929595
  · exact B929599
  · exact B929603
  · exact B929607
  · exact B929611
  · exact B929615
  · exact B929619
  · exact B929623
  · exact B929627
  · exact B929631
  · exact B929635
  · exact B929639
  · exact B929643
  · exact B929647
  · exact B929651
  · exact B929655
  · exact B929659
  · exact B929663
  · exact B929667
  · exact B929671
  · exact B929675
  · exact B929679
  · exact B929683
  · exact B929687
  · exact B929691
  · exact B929695
  · exact B929699
  · exact B929703
  · exact B929707
  · exact B929711
  · exact B929715
  · exact B929719
  · exact B929723
  · exact B929727
  · exact B929731
  · exact B929735
  · exact B929739
  · exact B929743
  · exact B929747
  · exact B929751
  · exact B929755
  · exact B929759
  · exact B929763
  · exact B929767
  · exact B929771
  · exact B929775
  · exact B929779
  · exact B929783
  · exact B929787
  · exact B929791
  · exact B929795
  · exact B929799
  · exact B929803
  · exact B929807
  · exact B929811
  · exact B929815
  · exact B929819
  · exact B929823
  · exact B929827
  · exact B929831
  · exact B929835
  · exact B929839
  · exact B929843
  · exact B929847
  · exact B929851
  · exact B929855
  · exact B929859
  · exact B929863
  · exact B929867
  · exact B929871
  · exact B929875
  · exact B929879
  · exact B929883
  · exact B929887
  · exact B929891
  · exact B929895
  · exact B929899
  · exact B929903
  · exact B929907
  · exact B929911
  · exact B929915
  · exact B929919
  · exact B929923
  · exact B929927
  · exact B929931
  · exact B929935
  · exact B929939
  · exact B929943
  · exact B929947
  · exact B929951
  · exact B929955
  · exact B929959
  · exact B929963
  · exact B929967
  · exact B929971
  · exact B929975
  · exact B929979
  · exact B929983
  · exact B929987
  · exact B929991
  · exact B929995
  · exact B929999
  · exact B930003
  · exact B930007
  · exact B930011
  · exact B930015
  · exact B930019
  · exact B930023
  · exact B930027
  · exact B930031
  · exact B930035
  · exact B930039
  · exact B930043
  · exact B930047
  · exact B930051
  · exact B930055
  · exact B930059
  · exact B930063
  · exact B930067
  · exact B930071
  · exact B930075
  · exact B930079
  · exact B930083
  · exact B930087
  · exact B930091
  · exact B930095
  · exact B930099
  · exact B930103
  · exact B930107
  · exact B930111
  · exact B930115
  · exact B930119
  · exact B930123
  · exact B930127
  · exact B930131
  · exact B930135
  · exact B930139
  · exact B930143
  · exact B930147
  · exact B930151
  · exact B930155
  · exact B930159
  · exact B930163
  · exact B930167
  · exact B930171
  · exact B930175
  · exact B930179
  · exact B930183
  · exact B930187
  · exact B930191
  · exact B930195
  · exact B930199
  · exact B930203
  · exact B930207
  · exact B930211
  · exact B930215
  · exact B930219
  · exact B930223
  · exact B930227
  · exact B930231
  · exact B930235
  · exact B930239
  · exact B930243
  · exact B930247
  · exact B930251
  · exact B930255
  · exact B930259
  · exact B930263
  · exact B930267
  · exact B930271
  · exact B930275
  · exact B930279
  · exact B930283
  · exact B930287
  · exact B930291
  · exact B930295
  · exact B930299
  · exact B930303
  · exact B930307
  · exact B930311
  · exact B930315
  · exact B930319
  · exact B930323
  · exact B930327
  · exact B930331
  · exact B930335
  · exact B930339
  · exact B930343
  · exact B930347
  · exact B930351
  · exact B930355
  · exact B930359
  · exact B930363
  · exact B930367
  · exact B930371
  · exact B930375
  · exact B930379
  · exact B930383
  · exact B930387
  · exact B930391
  · exact B930395
  · exact B930399
  · exact B930403
  · exact B930407
  · exact B930411
  · exact B930415
  · exact B930419
  · exact B930423
  · exact B930427
  · exact B930431
  · exact B930435
  · exact B930439
  · exact B930443
  · exact B930447
  · exact B930451
  · exact B930455
  · exact B930459
  · exact B930463
  · exact B930467
  · exact B930471
  · exact B930475
  · exact B930479
  · exact B930483
  · exact B930487
  · exact B930491
  · exact B930495
  · exact B930499
  · exact B930503
  · exact B930507
  · exact B930511
  · exact B930515
  · exact B930519
  · exact B930523
  · exact B930527
  · exact B930531
  · exact B930535
  · exact B930539
  · exact B930543
  · exact B930547
  · exact B930551
  · exact B930555
  · exact B930559
  · exact B930563
  · exact B930567
  · exact B930571
  · exact B930575
  · exact B930579
  · exact B930583
  · exact B930587
  · exact B930591
  · exact B930595
  · exact B930599
  · exact B930603
  · exact B930607
  · exact B930611
  · exact B930615
  · exact B930619
  · exact B930623
  · exact B930627
  · exact B930631
  · exact B930635
  · exact B930639
  · exact B930643
  · exact B930647
  · exact B930651
  · exact B930655
  · exact B930659
  · exact B930663
  · exact B930667
  · exact B930671
  · exact B930675
  · exact B930679
  · exact B930683
  · exact B930687
  · exact B930691
  · exact B930695
  · exact B930699
  · exact B930703
  · exact B930707
  · exact B930711
  · exact B930715
  · exact B930719
  · exact B930723
  · exact B930727
  · exact B930731
  · exact B930735
  · exact B930739
  · exact B930743
  · exact B930747
  · exact B930751
  · exact B930755
  · exact B930759
  · exact B930763
  · exact B930767
  · exact B930771
  · exact B930775
  · exact B930779
  · exact B930783
  · exact B930787
  · exact B930791
  · exact B930795
  · exact B930799
  · exact B930803
  · exact B930807
  · exact B930811
  · exact B930815
  · exact B930819
  · exact B930823
  · exact B930827
  · exact B930831
  · exact B930835
  · exact B930839
  · exact B930843
  · exact B930847
  · exact B930851
  · exact B930855
  · exact B930859
  · exact B930863
  · exact B930867
  · exact B930871
  · exact B930875
  · exact B930879
  · exact B930883
  · exact B930887
  · exact B930891
  · exact B930895
  · exact B930899
  · exact B930903
  · exact B930907
  · exact B930911
  · exact B930915
  · exact B930919
  · exact B930923
  · exact B930927
  · exact B930931
  · exact B930935
  · exact B930939
  · exact B930943
  · exact B930947
  · exact B930951
  · exact B930955
  · exact B930959
  · exact B930963
  · exact B930967
  · exact B930971
  · exact B930975
  · exact B930979
  · exact B930983
  · exact B930987
  · exact B930991
  · exact B930995
  · exact B930999
  · exact B931003
  · exact B931007
  · exact B931011
  · exact B931015
  · exact B931019
  · exact B931023
  · exact B931027
  · exact B931031
  · exact B931035
  · exact B931039
  · exact B931043
  · exact B931047
  · exact B931051
  · exact B931055
  · exact B931059
  · exact B931063
  · exact B931067
  · exact B931071
  · exact B931075
  · exact B931079
  · exact B931083
  · exact B931087
  · exact B931091
  · exact B931095
  · exact B931099
  · exact B931103
  · exact B931107
  · exact B931111
  · exact B931115
  · exact B931119
  · exact B931123
  · exact B931127
  · exact B931131
  · exact B931135
  · exact B931139
  · exact B931143
  · exact B931147
  · exact B931151
  · exact B931155
  · exact B931159
  · exact B931163
  · exact B931167
  · exact B931171
  · exact B931175
  · exact B931179
  · exact B931183
  · exact B931187
  · exact B931191
  · exact B931195
  · exact B931199
  · exact B931203
  · exact B931207
  · exact B931211
  · exact B931215
  · exact B931219
  · exact B931223
  · exact B931227
  · exact B931231
  · exact B931235
  · exact B931239
  · exact B931243
  · exact B931247
  · exact B931251
  · exact B931255
  · exact B931259
  · exact B931263
  · exact B931267
  · exact B931271
  · exact B931275
  · exact B931279
  · exact B931283
  · exact B931287
  · exact B931291
  · exact B931295
  · exact B931299
  · exact B931303
  · exact B931307
  · exact B931311
  · exact B931315
  · exact B931319
  · exact B931323
  · exact B931327
  · exact B931331
  · exact B931335
  · exact B931339
  · exact B931343
  · exact B931347
  · exact B931351
  · exact B931355
  · exact B931359
  · exact B931363
  · exact B931367
  · exact B931371
  · exact B931375
  · exact B931379

theorem C1 (j : ℕ) (h1 : 232845 ≤ j) (h2 : j ≤ 233144) : Blo 928581 (4 * j + 3) := by
  interval_cases j
  · exact B931383
  · exact B931387
  · exact B931391
  · exact B931395
  · exact B931399
  · exact B931403
  · exact B931407
  · exact B931411
  · exact B931415
  · exact B931419
  · exact B931423
  · exact B931427
  · exact B931431
  · exact B931435
  · exact B931439
  · exact B931443
  · exact B931447
  · exact B931451
  · exact B931455
  · exact B931459
  · exact B931463
  · exact B931467
  · exact B931471
  · exact B931475
  · exact B931479
  · exact B931483
  · exact B931487
  · exact B931491
  · exact B931495
  · exact B931499
  · exact B931503
  · exact B931507
  · exact B931511
  · exact B931515
  · exact B931519
  · exact B931523
  · exact B931527
  · exact B931531
  · exact B931535
  · exact B931539
  · exact B931543
  · exact B931547
  · exact B931551
  · exact B931555
  · exact B931559
  · exact B931563
  · exact B931567
  · exact B931571
  · exact B931575
  · exact B931579
  · exact B931583
  · exact B931587
  · exact B931591
  · exact B931595
  · exact B931599
  · exact B931603
  · exact B931607
  · exact B931611
  · exact B931615
  · exact B931619
  · exact B931623
  · exact B931627
  · exact B931631
  · exact B931635
  · exact B931639
  · exact B931643
  · exact B931647
  · exact B931651
  · exact B931655
  · exact B931659
  · exact B931663
  · exact B931667
  · exact B931671
  · exact B931675
  · exact B931679
  · exact B931683
  · exact B931687
  · exact B931691
  · exact B931695
  · exact B931699
  · exact B931703
  · exact B931707
  · exact B931711
  · exact B931715
  · exact B931719
  · exact B931723
  · exact B931727
  · exact B931731
  · exact B931735
  · exact B931739
  · exact B931743
  · exact B931747
  · exact B931751
  · exact B931755
  · exact B931759
  · exact B931763
  · exact B931767
  · exact B931771
  · exact B931775
  · exact B931779
  · exact B931783
  · exact B931787
  · exact B931791
  · exact B931795
  · exact B931799
  · exact B931803
  · exact B931807
  · exact B931811
  · exact B931815
  · exact B931819
  · exact B931823
  · exact B931827
  · exact B931831
  · exact B931835
  · exact B931839
  · exact B931843
  · exact B931847
  · exact B931851
  · exact B931855
  · exact B931859
  · exact B931863
  · exact B931867
  · exact B931871
  · exact B931875
  · exact B931879
  · exact B931883
  · exact B931887
  · exact B931891
  · exact B931895
  · exact B931899
  · exact B931903
  · exact B931907
  · exact B931911
  · exact B931915
  · exact B931919
  · exact B931923
  · exact B931927
  · exact B931931
  · exact B931935
  · exact B931939
  · exact B931943
  · exact B931947
  · exact B931951
  · exact B931955
  · exact B931959
  · exact B931963
  · exact B931967
  · exact B931971
  · exact B931975
  · exact B931979
  · exact B931983
  · exact B931987
  · exact B931991
  · exact B931995
  · exact B931999
  · exact B932003
  · exact B932007
  · exact B932011
  · exact B932015
  · exact B932019
  · exact B932023
  · exact B932027
  · exact B932031
  · exact B932035
  · exact B932039
  · exact B932043
  · exact B932047
  · exact B932051
  · exact B932055
  · exact B932059
  · exact B932063
  · exact B932067
  · exact B932071
  · exact B932075
  · exact B932079
  · exact B932083
  · exact B932087
  · exact B932091
  · exact B932095
  · exact B932099
  · exact B932103
  · exact B932107
  · exact B932111
  · exact B932115
  · exact B932119
  · exact B932123
  · exact B932127
  · exact B932131
  · exact B932135
  · exact B932139
  · exact B932143
  · exact B932147
  · exact B932151
  · exact B932155
  · exact B932159
  · exact B932163
  · exact B932167
  · exact B932171
  · exact B932175
  · exact B932179
  · exact B932183
  · exact B932187
  · exact B932191
  · exact B932195
  · exact B932199
  · exact B932203
  · exact B932207
  · exact B932211
  · exact B932215
  · exact B932219
  · exact B932223
  · exact B932227
  · exact B932231
  · exact B932235
  · exact B932239
  · exact B932243
  · exact B932247
  · exact B932251
  · exact B932255
  · exact B932259
  · exact B932263
  · exact B932267
  · exact B932271
  · exact B932275
  · exact B932279
  · exact B932283
  · exact B932287
  · exact B932291
  · exact B932295
  · exact B932299
  · exact B932303
  · exact B932307
  · exact B932311
  · exact B932315
  · exact B932319
  · exact B932323
  · exact B932327
  · exact B932331
  · exact B932335
  · exact B932339
  · exact B932343
  · exact B932347
  · exact B932351
  · exact B932355
  · exact B932359
  · exact B932363
  · exact B932367
  · exact B932371
  · exact B932375
  · exact B932379
  · exact B932383
  · exact B932387
  · exact B932391
  · exact B932395
  · exact B932399
  · exact B932403
  · exact B932407
  · exact B932411
  · exact B932415
  · exact B932419
  · exact B932423
  · exact B932427
  · exact B932431
  · exact B932435
  · exact B932439
  · exact B932443
  · exact B932447
  · exact B932451
  · exact B932455
  · exact B932459
  · exact B932463
  · exact B932467
  · exact B932471
  · exact B932475
  · exact B932479
  · exact B932483
  · exact B932487
  · exact B932491
  · exact B932495
  · exact B932499
  · exact B932503
  · exact B932507
  · exact B932511
  · exact B932515
  · exact B932519
  · exact B932523
  · exact B932527
  · exact B932531
  · exact B932535
  · exact B932539
  · exact B932543
  · exact B932547
  · exact B932551
  · exact B932555
  · exact B932559
  · exact B932563
  · exact B932567
  · exact B932571
  · exact B932575
  · exact B932579

theorem solution (m : ℕ) (hlo : 928581 ≤ m) (hhi : m ≤ 932581) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 232145 ≤ j := by omega
    have hj2 : j ≤ 233144 := by omega
    have hb : Blo 928581 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 232845 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
