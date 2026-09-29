-- Prove2me | solution 1 for syracuse_descends_range_1574485_1576485
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:07:19.884309+00:00
-- url     : https://prove2.me/submissions/261a40fb-42d9-462e-ad5a-8b3e480ed0f4

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


theorem B3989533 : Blo 1574485 3989533 := bbase (se 3 (by rfl) ⟨748037, by rfl⟩ : syracuseStep 3989533 = 1496075) (by norm_num)
theorem B1892413 : Blo 1574485 1892413 := bbase (se 3 (by rfl) ⟨354827, by rfl⟩ : syracuseStep 1892413 = 709655) (by norm_num)
theorem B7970885 : Blo 1574485 7970885 := bbase (se 4 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 7970885 = 1494541) (by norm_num)
theorem B5316677 : Blo 1574485 5316677 := bbase (se 4 (by rfl) ⟨498438, by rfl⟩ : syracuseStep 5316677 = 996877) (by norm_num)
theorem B4259909 : Blo 1574485 4259909 := bbase (se 4 (by rfl) ⟨399366, by rfl⟩ : syracuseStep 4259909 = 798733) (by norm_num)
theorem B3989645 : Blo 1574485 3989645 := bbase (se 3 (by rfl) ⟨748058, by rfl⟩ : syracuseStep 3989645 = 1496117) (by norm_num)
theorem B2695349 : Blo 1574485 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B1597649 : Blo 1574485 1597649 := bbase (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) (by norm_num)
theorem B6725845 : Blo 1574485 6725845 := bbase (se 7 (by rfl) ⟨78818, by rfl⟩ : syracuseStep 6725845 = 157637) (by norm_num)
theorem B3989837 : Blo 1574485 3989837 := bbase (se 3 (by rfl) ⟨748094, by rfl⟩ : syracuseStep 3989837 = 1496189) (by norm_num)
theorem B13648213 : Blo 1574485 13648213 := bbase (se 10 (by rfl) ⟨19992, by rfl⟩ : syracuseStep 13648213 = 39985) (by norm_num)
theorem B2130349 : Blo 1574485 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B8511925 : Blo 1574485 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B7569845 : Blo 1574485 7569845 := bbase (se 5 (by rfl) ⟨354836, by rfl⟩ : syracuseStep 7569845 = 709673) (by norm_num)
theorem B2990533 : Blo 1574485 2990533 := bbase (se 4 (by rfl) ⟨280362, by rfl⟩ : syracuseStep 2990533 = 560725) (by norm_num)
theorem B8970709 : Blo 1574485 8970709 := bbase (se 7 (by rfl) ⟨105125, by rfl⟩ : syracuseStep 8970709 = 210251) (by norm_num)
theorem B5317109 : Blo 1574485 5317109 := bbase (se 5 (by rfl) ⟨249239, by rfl⟩ : syracuseStep 5317109 = 498479) (by norm_num)
theorem B5677573 : Blo 1574485 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B2990677 : Blo 1574485 2990677 := bbase (se 8 (by rfl) ⟨17523, by rfl⟩ : syracuseStep 2990677 = 35047) (by norm_num)
theorem B2523781 : Blo 1574485 2523781 := bbase (se 4 (by rfl) ⟨236604, by rfl⟩ : syracuseStep 2523781 = 473209) (by norm_num)
theorem B3195541 : Blo 1574485 3195541 := bbase (se 6 (by rfl) ⟨74895, by rfl⟩ : syracuseStep 3195541 = 149791) (by norm_num)
theorem B5980837 : Blo 1574485 5980837 := bbase (se 4 (by rfl) ⟨560703, by rfl⟩ : syracuseStep 5980837 = 1121407) (by norm_num)
theorem B3990181 : Blo 1574485 3990181 := bbase (se 4 (by rfl) ⟨374079, by rfl⟩ : syracuseStep 3990181 = 748159) (by norm_num)
theorem B2990837 : Blo 1574485 2990837 := bbase (se 5 (by rfl) ⟨140195, by rfl⟩ : syracuseStep 2990837 = 280391) (by norm_num)
theorem B3990293 : Blo 1574485 3990293 := bbase (se 6 (by rfl) ⟨93522, by rfl⟩ : syracuseStep 3990293 = 187045) (by norm_num)
theorem B3785557 : Blo 1574485 3785557 := bbase (se 9 (by rfl) ⟨11090, by rfl⟩ : syracuseStep 3785557 = 22181) (by norm_num)
theorem B2990981 : Blo 1574485 2990981 := bbase (se 4 (by rfl) ⟨280404, by rfl⟩ : syracuseStep 2990981 = 560809) (by norm_num)
theorem B5317541 : Blo 1574485 5317541 := bbase (se 4 (by rfl) ⟨498519, by rfl⟩ : syracuseStep 5317541 = 997039) (by norm_num)
theorem B7979957 : Blo 1574485 7979957 := bbase (se 5 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 7979957 = 748121) (by norm_num)
theorem B5981141 : Blo 1574485 5981141 := bbase (se 7 (by rfl) ⟨70091, by rfl⟩ : syracuseStep 5981141 = 140183) (by norm_num)
theorem B2556917 : Blo 1574485 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B2524205 : Blo 1574485 2524205 := bbase (se 3 (by rfl) ⟨473288, by rfl⟩ : syracuseStep 2524205 = 946577) (by norm_num)
theorem B1893461 : Blo 1574485 1893461 := bbase (se 8 (by rfl) ⟨11094, by rfl⟩ : syracuseStep 1893461 = 22189) (by norm_num)
theorem B2991269 : Blo 1574485 2991269 := bbase (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) (by norm_num)
theorem B5465269 : Blo 1574485 5465269 := bbase (se 5 (by rfl) ⟨256184, by rfl⟩ : syracuseStep 5465269 = 512369) (by norm_num)
theorem B5047589 : Blo 1574485 5047589 := bbase (se 4 (by rfl) ⟨473211, by rfl⟩ : syracuseStep 5047589 = 946423) (by norm_num)
theorem B2991421 : Blo 1574485 2991421 := bbase (se 3 (by rfl) ⟨560891, by rfl⟩ : syracuseStep 2991421 = 1121783) (by norm_num)
theorem B2524493 : Blo 1574485 2524493 := bbase (se 3 (by rfl) ⟨473342, by rfl⟩ : syracuseStep 2524493 = 946685) (by norm_num)
theorem B7972181 : Blo 1574485 7972181 := bbase (se 12 (by rfl) ⟨2919, by rfl⟩ : syracuseStep 7972181 = 5839) (by norm_num)
theorem B5317973 : Blo 1574485 5317973 := bbase (se 12 (by rfl) ⟨1947, by rfl⟩ : syracuseStep 5317973 = 3895) (by norm_num)
theorem B3786077 : Blo 1574485 3786077 := bbase (se 3 (by rfl) ⟨709889, by rfl⟩ : syracuseStep 3786077 = 1419779) (by norm_num)
theorem B3409309 : Blo 1574485 3409309 := bbase (se 3 (by rfl) ⟨639245, by rfl⟩ : syracuseStep 3409309 = 1278491) (by norm_num)
theorem B5047717 : Blo 1574485 5047717 := bbase (se 4 (by rfl) ⟨473223, by rfl⟩ : syracuseStep 5047717 = 946447) (by norm_num)
theorem B1893817 : Blo 1574485 1893817 := bbase (se 2 (by rfl) ⟨710181, by rfl⟩ : syracuseStep 1893817 = 1420363) (by norm_num)
theorem B3786173 : Blo 1574485 3786173 := bbase (se 3 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 3786173 = 1419815) (by norm_num)
theorem B5319701 : Blo 1574485 5319701 := bbase (se 6 (by rfl) ⟨124680, by rfl⟩ : syracuseStep 5319701 = 249361) (by norm_num)
theorem B2557397 : Blo 1574485 2557397 := bbase (se 7 (by rfl) ⟨29969, by rfl⟩ : syracuseStep 2557397 = 59939) (by norm_num)
theorem B2524717 : Blo 1574485 2524717 := bbase (se 3 (by rfl) ⟨473384, by rfl⟩ : syracuseStep 2524717 = 946769) (by norm_num)
theorem B2991725 : Blo 1574485 2991725 := bbase (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) (by norm_num)
theorem B28731029 : Blo 1574485 28731029 := bbase (se 6 (by rfl) ⟨673383, by rfl⟩ : syracuseStep 28731029 = 1346767) (by norm_num)
theorem B7677589 : Blo 1574485 7677589 := bbase (se 6 (by rfl) ⟨179943, by rfl⟩ : syracuseStep 7677589 = 359887) (by norm_num)
theorem B6727333 : Blo 1574485 6727333 := bbase (se 4 (by rfl) ⟨630687, by rfl⟩ : syracuseStep 6727333 = 1261375) (by norm_num)
theorem B5047973 : Blo 1574485 5047973 := bbase (se 4 (by rfl) ⟨473247, by rfl⟩ : syracuseStep 5047973 = 946495) (by norm_num)
theorem B6727349 : Blo 1574485 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B15140533 : Blo 1574485 15140533 := bbase (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) (by norm_num)
theorem B7571189 : Blo 1574485 7571189 := bbase (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) (by norm_num)
theorem B5318405 : Blo 1574485 5318405 := bbase (se 4 (by rfl) ⟨498600, by rfl⟩ : syracuseStep 5318405 = 997201) (by norm_num)
theorem B1771321 : Blo 1574485 1771321 := bbase (se 2 (by rfl) ⟨664245, by rfl⟩ : syracuseStep 1771321 = 1328491) (by norm_num)
theorem B1771357 : Blo 1574485 1771357 := bbase (se 3 (by rfl) ⟨332129, by rfl⟩ : syracuseStep 1771357 = 664259) (by norm_num)
theorem B1771393 : Blo 1574485 1771393 := bbase (se 2 (by rfl) ⟨664272, by rfl⟩ : syracuseStep 1771393 = 1328545) (by norm_num)
theorem B1771429 : Blo 1574485 1771429 := bbase (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) (by norm_num)
theorem B2877365 : Blo 1574485 2877365 := bbase (se 5 (by rfl) ⟨134876, by rfl⟩ : syracuseStep 2877365 = 269753) (by norm_num)
theorem B5392325 : Blo 1574485 5392325 := bbase (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) (by norm_num)
theorem B1771465 : Blo 1574485 1771465 := bbase (se 2 (by rfl) ⟨664299, by rfl⟩ : syracuseStep 1771465 = 1328599) (by norm_num)
theorem B1771501 : Blo 1574485 1771501 := bbase (se 3 (by rfl) ⟨332156, by rfl⟩ : syracuseStep 1771501 = 664313) (by norm_num)
theorem B1771537 : Blo 1574485 1771537 := bbase (se 2 (by rfl) ⟨664326, by rfl⟩ : syracuseStep 1771537 = 1328653) (by norm_num)
theorem B1992757 : Blo 1574485 1992757 := bbase (se 5 (by rfl) ⟨93410, by rfl⟩ : syracuseStep 1992757 = 186821) (by norm_num)
theorem B1771573 : Blo 1574485 1771573 := bbase (se 5 (by rfl) ⟨83042, by rfl⟩ : syracuseStep 1771573 = 166085) (by norm_num)
theorem B1771609 : Blo 1574485 1771609 := bbase (se 2 (by rfl) ⟨664353, by rfl⟩ : syracuseStep 1771609 = 1328707) (by norm_num)
theorem B1771645 : Blo 1574485 1771645 := bbase (se 3 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 1771645 = 664367) (by norm_num)
theorem B1992853 : Blo 1574485 1992853 := bbase (se 6 (by rfl) ⟨46707, by rfl⟩ : syracuseStep 1992853 = 93415) (by norm_num)
theorem B1771681 : Blo 1574485 1771681 := bbase (se 2 (by rfl) ⟨664380, by rfl⟩ : syracuseStep 1771681 = 1328761) (by norm_num)
theorem B5318837 : Blo 1574485 5318837 := bbase (se 5 (by rfl) ⟨249320, by rfl⟩ : syracuseStep 5318837 = 498641) (by norm_num)
theorem B1771717 : Blo 1574485 1771717 := bbase (se 4 (by rfl) ⟨166098, by rfl⟩ : syracuseStep 1771717 = 332197) (by norm_num)
theorem B1771753 : Blo 1574485 1771753 := bbase (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) (by norm_num)
theorem B1771789 : Blo 1574485 1771789 := bbase (se 3 (by rfl) ⟨332210, by rfl⟩ : syracuseStep 1771789 = 664421) (by norm_num)
theorem B1771825 : Blo 1574485 1771825 := bbase (se 2 (by rfl) ⟨664434, by rfl⟩ : syracuseStep 1771825 = 1328869) (by norm_num)
theorem B1993025 : Blo 1574485 1993025 := bbase (se 2 (by rfl) ⟨747384, by rfl⟩ : syracuseStep 1993025 = 1494769) (by norm_num)
theorem B1771861 : Blo 1574485 1771861 := bbase (se 10 (by rfl) ⟨2595, by rfl⟩ : syracuseStep 1771861 = 5191) (by norm_num)
theorem B2992477 : Blo 1574485 2992477 := bbase (se 3 (by rfl) ⟨561089, by rfl⟩ : syracuseStep 2992477 = 1122179) (by norm_num)
theorem B1681769 : Blo 1574485 1681769 := bbase (se 2 (by rfl) ⟨630663, by rfl⟩ : syracuseStep 1681769 = 1261327) (by norm_num)
theorem B1993081 : Blo 1574485 1993081 := bbase (se 2 (by rfl) ⟨747405, by rfl⟩ : syracuseStep 1993081 = 1494811) (by norm_num)
theorem B1771897 : Blo 1574485 1771897 := bbase (se 2 (by rfl) ⟨664461, by rfl⟩ : syracuseStep 1771897 = 1328923) (by norm_num)
theorem B2361749 : Blo 1574485 2361749 := bbase (se 6 (by rfl) ⟨55353, by rfl⟩ : syracuseStep 2361749 = 110707) (by norm_num)
theorem B8972693 : Blo 1574485 8972693 := bbase (se 6 (by rfl) ⟨210297, by rfl⟩ : syracuseStep 8972693 = 420595) (by norm_num)
theorem B1771933 : Blo 1574485 1771933 := bbase (se 3 (by rfl) ⟨332237, by rfl⟩ : syracuseStep 1771933 = 664475) (by norm_num)
theorem B2361773 : Blo 1574485 2361773 := bbase (se 3 (by rfl) ⟨442832, by rfl⟩ : syracuseStep 2361773 = 885665) (by norm_num)
theorem B1771969 : Blo 1574485 1771969 := bbase (se 2 (by rfl) ⟨664488, by rfl⟩ : syracuseStep 1771969 = 1328977) (by norm_num)
theorem B2361797 : Blo 1574485 2361797 := bbase (se 4 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 2361797 = 442837) (by norm_num)
theorem B1993177 : Blo 1574485 1993177 := bbase (se 2 (by rfl) ⟨747441, by rfl⟩ : syracuseStep 1993177 = 1494883) (by norm_num)
theorem B2361821 : Blo 1574485 2361821 := bbase (se 3 (by rfl) ⟨442841, by rfl⟩ : syracuseStep 2361821 = 885683) (by norm_num)
theorem B1772005 : Blo 1574485 1772005 := bbase (se 4 (by rfl) ⟨166125, by rfl⟩ : syracuseStep 1772005 = 332251) (by norm_num)
theorem B2992621 : Blo 1574485 2992621 := bbase (se 3 (by rfl) ⟨561116, by rfl⟩ : syracuseStep 2992621 = 1122233) (by norm_num)
theorem B2361845 : Blo 1574485 2361845 := bbase (se 5 (by rfl) ⟨110711, by rfl⟩ : syracuseStep 2361845 = 221423) (by norm_num)
theorem B1772041 : Blo 1574485 1772041 := bbase (se 2 (by rfl) ⟨664515, by rfl⟩ : syracuseStep 1772041 = 1329031) (by norm_num)
theorem B2361869 : Blo 1574485 2361869 := bbase (se 3 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 2361869 = 885701) (by norm_num)
theorem B2361893 : Blo 1574485 2361893 := bbase (se 4 (by rfl) ⟨221427, by rfl⟩ : syracuseStep 2361893 = 442855) (by norm_num)
theorem B1772077 : Blo 1574485 1772077 := bbase (se 3 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 1772077 = 664529) (by norm_num)
theorem B13453877 : Blo 1574485 13453877 := bbase (se 5 (by rfl) ⟨630650, by rfl⟩ : syracuseStep 13453877 = 1261301) (by norm_num)
theorem B2361917 : Blo 1574485 2361917 := bbase (se 3 (by rfl) ⟨442859, by rfl⟩ : syracuseStep 2361917 = 885719) (by norm_num)
theorem B1772113 : Blo 1574485 1772113 := bbase (se 2 (by rfl) ⟨664542, by rfl⟩ : syracuseStep 1772113 = 1329085) (by norm_num)
theorem B4483669 : Blo 1574485 4483669 := bbase (se 8 (by rfl) ⟨26271, by rfl⟩ : syracuseStep 4483669 = 52543) (by norm_num)
theorem B2361941 : Blo 1574485 2361941 := bbase (se 8 (by rfl) ⟨13839, by rfl⟩ : syracuseStep 2361941 = 27679) (by norm_num)
theorem B7973477 : Blo 1574485 7973477 := bbase (se 4 (by rfl) ⟨747513, by rfl⟩ : syracuseStep 7973477 = 1495027) (by norm_num)
theorem B5319269 : Blo 1574485 5319269 := bbase (se 4 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 5319269 = 997363) (by norm_num)
theorem B2361965 : Blo 1574485 2361965 := bbase (se 3 (by rfl) ⟨442868, by rfl⟩ : syracuseStep 2361965 = 885737) (by norm_num)
theorem B1772149 : Blo 1574485 1772149 := bbase (se 5 (by rfl) ⟨83069, by rfl⟩ : syracuseStep 1772149 = 166139) (by norm_num)
theorem B2361989 : Blo 1574485 2361989 := bbase (se 4 (by rfl) ⟨221436, by rfl⟩ : syracuseStep 2361989 = 442873) (by norm_num)
theorem B1993349 : Blo 1574485 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B2992781 : Blo 1574485 2992781 := bbase (se 3 (by rfl) ⟨561146, by rfl⟩ : syracuseStep 2992781 = 1122293) (by norm_num)
theorem B1772185 : Blo 1574485 1772185 := bbase (se 2 (by rfl) ⟨664569, by rfl⟩ : syracuseStep 1772185 = 1329139) (by norm_num)
theorem B2362013 : Blo 1574485 2362013 := bbase (se 3 (by rfl) ⟨442877, by rfl⟩ : syracuseStep 2362013 = 885755) (by norm_num)
theorem B2362037 : Blo 1574485 2362037 := bbase (se 5 (by rfl) ⟨110720, by rfl⟩ : syracuseStep 2362037 = 221441) (by norm_num)
theorem B1993405 : Blo 1574485 1993405 := bbase (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) (by norm_num)
theorem B1772221 : Blo 1574485 1772221 := bbase (se 3 (by rfl) ⟨332291, by rfl⟩ : syracuseStep 1772221 = 664583) (by norm_num)
theorem B2362061 : Blo 1574485 2362061 := bbase (se 3 (by rfl) ⟨442886, by rfl⟩ : syracuseStep 2362061 = 885773) (by norm_num)
theorem B1772257 : Blo 1574485 1772257 := bbase (se 2 (by rfl) ⟨664596, by rfl⟩ : syracuseStep 1772257 = 1329193) (by norm_num)
theorem B2362085 : Blo 1574485 2362085 := bbase (se 4 (by rfl) ⟨221445, by rfl⟩ : syracuseStep 2362085 = 442891) (by norm_num)
theorem B4483829 : Blo 1574485 4483829 := bbase (se 5 (by rfl) ⟨210179, by rfl⟩ : syracuseStep 4483829 = 420359) (by norm_num)
theorem B2362109 : Blo 1574485 2362109 := bbase (se 3 (by rfl) ⟨442895, by rfl⟩ : syracuseStep 2362109 = 885791) (by norm_num)
theorem B3787517 : Blo 1574485 3787517 := bbase (se 3 (by rfl) ⟨710159, by rfl⟩ : syracuseStep 3787517 = 1420319) (by norm_num)
theorem B2657029 : Blo 1574485 2657029 := bbase (se 4 (by rfl) ⟨249096, by rfl⟩ : syracuseStep 2657029 = 498193) (by norm_num)
theorem B1772293 : Blo 1574485 1772293 := bbase (se 4 (by rfl) ⟨166152, by rfl⟩ : syracuseStep 1772293 = 332305) (by norm_num)
theorem B2362133 : Blo 1574485 2362133 := bbase (se 6 (by rfl) ⟨55362, by rfl⟩ : syracuseStep 2362133 = 110725) (by norm_num)
theorem B1993501 : Blo 1574485 1993501 := bbase (se 3 (by rfl) ⟨373781, by rfl⟩ : syracuseStep 1993501 = 747563) (by norm_num)
theorem B2394917 : Blo 1574485 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1682213 : Blo 1574485 1682213 := bbase (se 4 (by rfl) ⟨157707, by rfl⟩ : syracuseStep 1682213 = 315415) (by norm_num)
theorem B1772329 : Blo 1574485 1772329 := bbase (se 2 (by rfl) ⟨664623, by rfl⟩ : syracuseStep 1772329 = 1329247) (by norm_num)
theorem B2362157 : Blo 1574485 2362157 := bbase (se 3 (by rfl) ⟨442904, by rfl⟩ : syracuseStep 2362157 = 885809) (by norm_num)
theorem B2362181 : Blo 1574485 2362181 := bbase (se 4 (by rfl) ⟨221454, by rfl⟩ : syracuseStep 2362181 = 442909) (by norm_num)
theorem B1772365 : Blo 1574485 1772365 := bbase (se 3 (by rfl) ⟨332318, by rfl⟩ : syracuseStep 1772365 = 664637) (by norm_num)
theorem B2657117 : Blo 1574485 2657117 := bbase (se 3 (by rfl) ⟨498209, by rfl⟩ : syracuseStep 2657117 = 996419) (by norm_num)
theorem B2362205 : Blo 1574485 2362205 := bbase (se 3 (by rfl) ⟨442913, by rfl⟩ : syracuseStep 2362205 = 885827) (by norm_num)
theorem B1772401 : Blo 1574485 1772401 := bbase (se 2 (by rfl) ⟨664650, by rfl⟩ : syracuseStep 1772401 = 1329301) (by norm_num)
theorem B2362229 : Blo 1574485 2362229 := bbase (se 5 (by rfl) ⟨110729, by rfl⟩ : syracuseStep 2362229 = 221459) (by norm_num)
theorem B2362253 : Blo 1574485 2362253 := bbase (se 3 (by rfl) ⟨442922, by rfl⟩ : syracuseStep 2362253 = 885845) (by norm_num)
theorem B1772437 : Blo 1574485 1772437 := bbase (se 6 (by rfl) ⟨41541, by rfl⟩ : syracuseStep 1772437 = 83083) (by norm_num)
theorem B2362277 : Blo 1574485 2362277 := bbase (se 4 (by rfl) ⟨221463, by rfl⟩ : syracuseStep 2362277 = 442927) (by norm_num)
theorem B1772473 : Blo 1574485 1772473 := bbase (se 2 (by rfl) ⟨664677, by rfl⟩ : syracuseStep 1772473 = 1329355) (by norm_num)
theorem B2362301 : Blo 1574485 2362301 := bbase (se 3 (by rfl) ⟨442931, by rfl⟩ : syracuseStep 2362301 = 885863) (by norm_num)
theorem B1993673 : Blo 1574485 1993673 := bbase (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) (by norm_num)
theorem B2362325 : Blo 1574485 2362325 := bbase (se 7 (by rfl) ⟨27683, by rfl⟩ : syracuseStep 2362325 = 55367) (by norm_num)
theorem B2657245 : Blo 1574485 2657245 := bbase (se 3 (by rfl) ⟨498233, by rfl⟩ : syracuseStep 2657245 = 996467) (by norm_num)
theorem B1772509 : Blo 1574485 1772509 := bbase (se 3 (by rfl) ⟨332345, by rfl⟩ : syracuseStep 1772509 = 664691) (by norm_num)
theorem B4484069 : Blo 1574485 4484069 := bbase (se 4 (by rfl) ⟨420381, by rfl⟩ : syracuseStep 4484069 = 840763) (by norm_num)
theorem B7187429 : Blo 1574485 7187429 := bbase (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) (by norm_num)
theorem B2362349 : Blo 1574485 2362349 := bbase (se 3 (by rfl) ⟨442940, by rfl⟩ : syracuseStep 2362349 = 885881) (by norm_num)
theorem B1993729 : Blo 1574485 1993729 := bbase (se 2 (by rfl) ⟨747648, by rfl⟩ : syracuseStep 1993729 = 1495297) (by norm_num)
theorem B1772545 : Blo 1574485 1772545 := bbase (se 2 (by rfl) ⟨664704, by rfl⟩ : syracuseStep 1772545 = 1329409) (by norm_num)
theorem B2362373 : Blo 1574485 2362373 := bbase (se 4 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 2362373 = 442945) (by norm_num)
theorem B3836933 : Blo 1574485 3836933 := bbase (se 4 (by rfl) ⟨359712, by rfl⟩ : syracuseStep 3836933 = 719425) (by norm_num)
theorem B10095637 : Blo 1574485 10095637 := bbase (se 6 (by rfl) ⟨236616, by rfl⟩ : syracuseStep 10095637 = 473233) (by norm_num)
theorem B5983253 : Blo 1574485 5983253 := bbase (se 6 (by rfl) ⟨140232, by rfl⟩ : syracuseStep 5983253 = 280465) (by norm_num)
theorem B2362397 : Blo 1574485 2362397 := bbase (se 3 (by rfl) ⟨442949, by rfl⟩ : syracuseStep 2362397 = 885899) (by norm_num)
theorem B1682461 : Blo 1574485 1682461 := bbase (se 3 (by rfl) ⟨315461, by rfl⟩ : syracuseStep 1682461 = 630923) (by norm_num)
theorem B1772581 : Blo 1574485 1772581 := bbase (se 4 (by rfl) ⟨166179, by rfl⟩ : syracuseStep 1772581 = 332359) (by norm_num)
theorem B2657333 : Blo 1574485 2657333 := bbase (se 5 (by rfl) ⟨124562, by rfl⟩ : syracuseStep 2657333 = 249125) (by norm_num)
theorem B2362421 : Blo 1574485 2362421 := bbase (se 5 (by rfl) ⟨110738, by rfl⟩ : syracuseStep 2362421 = 221477) (by norm_num)
theorem B5680181 : Blo 1574485 5680181 := bbase (se 5 (by rfl) ⟨266258, by rfl⟩ : syracuseStep 5680181 = 532517) (by norm_num)
theorem B1772617 : Blo 1574485 1772617 := bbase (se 2 (by rfl) ⟨664731, by rfl⟩ : syracuseStep 1772617 = 1329463) (by norm_num)
theorem B2362445 : Blo 1574485 2362445 := bbase (se 3 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 2362445 = 885917) (by norm_num)
theorem B1993825 : Blo 1574485 1993825 := bbase (se 2 (by rfl) ⟨747684, by rfl⟩ : syracuseStep 1993825 = 1495369) (by norm_num)
theorem B2362469 : Blo 1574485 2362469 := bbase (se 4 (by rfl) ⟨221481, by rfl⟩ : syracuseStep 2362469 = 442963) (by norm_num)
theorem B1772653 : Blo 1574485 1772653 := bbase (se 3 (by rfl) ⟨332372, by rfl⟩ : syracuseStep 1772653 = 664745) (by norm_num)
theorem B2362493 : Blo 1574485 2362493 := bbase (se 3 (by rfl) ⟨442967, by rfl⟩ : syracuseStep 2362493 = 885935) (by norm_num)
theorem B1772689 : Blo 1574485 1772689 := bbase (se 2 (by rfl) ⟨664758, by rfl⟩ : syracuseStep 1772689 = 1329517) (by norm_num)
theorem B2362517 : Blo 1574485 2362517 := bbase (se 6 (by rfl) ⟨55371, by rfl⟩ : syracuseStep 2362517 = 110743) (by norm_num)
theorem B4484261 : Blo 1574485 4484261 := bbase (se 4 (by rfl) ⟨420399, by rfl⟩ : syracuseStep 4484261 = 840799) (by norm_num)
theorem B2362541 : Blo 1574485 2362541 := bbase (se 3 (by rfl) ⟨442976, by rfl⟩ : syracuseStep 2362541 = 885953) (by norm_num)
theorem B2657461 : Blo 1574485 2657461 := bbase (se 5 (by rfl) ⟨124568, by rfl⟩ : syracuseStep 2657461 = 249137) (by norm_num)
theorem B1772725 : Blo 1574485 1772725 := bbase (se 5 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 1772725 = 166193) (by norm_num)
theorem B2362565 : Blo 1574485 2362565 := bbase (se 4 (by rfl) ⟨221490, by rfl⟩ : syracuseStep 2362565 = 442981) (by norm_num)
theorem B1772761 : Blo 1574485 1772761 := bbase (se 2 (by rfl) ⟨664785, by rfl⟩ : syracuseStep 1772761 = 1329571) (by norm_num)
theorem B2362589 : Blo 1574485 2362589 := bbase (se 3 (by rfl) ⟨442985, by rfl⟩ : syracuseStep 2362589 = 885971) (by norm_num)
theorem B2837749 : Blo 1574485 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B2362613 : Blo 1574485 2362613 := bbase (se 5 (by rfl) ⟨110747, by rfl⟩ : syracuseStep 2362613 = 221495) (by norm_num)
theorem B1772797 : Blo 1574485 1772797 := bbase (se 3 (by rfl) ⟨332399, by rfl⟩ : syracuseStep 1772797 = 664799) (by norm_num)
theorem B2657549 : Blo 1574485 2657549 := bbase (se 3 (by rfl) ⟨498290, by rfl⟩ : syracuseStep 2657549 = 996581) (by norm_num)
theorem B2362637 : Blo 1574485 2362637 := bbase (se 3 (by rfl) ⟨442994, by rfl⟩ : syracuseStep 2362637 = 885989) (by norm_num)
theorem B1993997 : Blo 1574485 1993997 := bbase (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) (by norm_num)
theorem B1772833 : Blo 1574485 1772833 := bbase (se 2 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 1772833 = 1329625) (by norm_num)
theorem B2362661 : Blo 1574485 2362661 := bbase (se 4 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 2362661 = 442999) (by norm_num)
theorem B5983541 : Blo 1574485 5983541 := bbase (se 5 (by rfl) ⟨280478, by rfl⟩ : syracuseStep 5983541 = 560957) (by norm_num)
theorem B2362685 : Blo 1574485 2362685 := bbase (se 3 (by rfl) ⟨443003, by rfl⟩ : syracuseStep 2362685 = 886007) (by norm_num)
theorem B1994053 : Blo 1574485 1994053 := bbase (se 4 (by rfl) ⟨186942, by rfl⟩ : syracuseStep 1994053 = 373885) (by norm_num)
theorem B1772869 : Blo 1574485 1772869 := bbase (se 4 (by rfl) ⟨166206, by rfl⟩ : syracuseStep 1772869 = 332413) (by norm_num)
theorem B32320853 : Blo 1574485 32320853 := bbase (se 11 (by rfl) ⟨23672, by rfl⟩ : syracuseStep 32320853 = 47345) (by norm_num)
theorem B2362709 : Blo 1574485 2362709 := bbase (se 11 (by rfl) ⟨1730, by rfl⟩ : syracuseStep 2362709 = 3461) (by norm_num)
theorem B5680469 : Blo 1574485 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B1772905 : Blo 1574485 1772905 := bbase (se 2 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 1772905 = 1329679) (by norm_num)
theorem B2362733 : Blo 1574485 2362733 := bbase (se 3 (by rfl) ⟨443012, by rfl⟩ : syracuseStep 2362733 = 886025) (by norm_num)
theorem B2362757 : Blo 1574485 2362757 := bbase (se 4 (by rfl) ⟨221508, by rfl⟩ : syracuseStep 2362757 = 443017) (by norm_num)
theorem B2657677 : Blo 1574485 2657677 := bbase (se 3 (by rfl) ⟨498314, by rfl⟩ : syracuseStep 2657677 = 996629) (by norm_num)
theorem B2428301 : Blo 1574485 2428301 := bbase (se 3 (by rfl) ⟨455306, by rfl⟩ : syracuseStep 2428301 = 910613) (by norm_num)
theorem B1772941 : Blo 1574485 1772941 := bbase (se 3 (by rfl) ⟨332426, by rfl⟩ : syracuseStep 1772941 = 664853) (by norm_num)
theorem B2362781 : Blo 1574485 2362781 := bbase (se 3 (by rfl) ⟨443021, by rfl⟩ : syracuseStep 2362781 = 886043) (by norm_num)
theorem B1994149 : Blo 1574485 1994149 := bbase (se 4 (by rfl) ⟨186951, by rfl⟩ : syracuseStep 1994149 = 373903) (by norm_num)
theorem B1772977 : Blo 1574485 1772977 := bbase (se 2 (by rfl) ⟨664866, by rfl⟩ : syracuseStep 1772977 = 1329733) (by norm_num)
theorem B2362805 : Blo 1574485 2362805 := bbase (se 5 (by rfl) ⟨110756, by rfl⟩ : syracuseStep 2362805 = 221513) (by norm_num)
theorem B5320133 : Blo 1574485 5320133 := bbase (se 4 (by rfl) ⟨498762, by rfl⟩ : syracuseStep 5320133 = 997525) (by norm_num)
theorem B2362829 : Blo 1574485 2362829 := bbase (se 3 (by rfl) ⟨443030, by rfl⟩ : syracuseStep 2362829 = 886061) (by norm_num)
theorem B1682893 : Blo 1574485 1682893 := bbase (se 3 (by rfl) ⟨315542, by rfl⟩ : syracuseStep 1682893 = 631085) (by norm_num)
theorem B11963861 : Blo 1574485 11963861 := bbase (se 7 (by rfl) ⟨140201, by rfl⟩ : syracuseStep 11963861 = 280403) (by norm_num)
theorem B1773013 : Blo 1574485 1773013 := bbase (se 7 (by rfl) ⟨20777, by rfl⟩ : syracuseStep 1773013 = 41555) (by norm_num)
theorem B2657765 : Blo 1574485 2657765 := bbase (se 4 (by rfl) ⟨249165, by rfl⟩ : syracuseStep 2657765 = 498331) (by norm_num)
theorem B2362853 : Blo 1574485 2362853 := bbase (se 4 (by rfl) ⟨221517, by rfl⟩ : syracuseStep 2362853 = 443035) (by norm_num)
theorem B1773049 : Blo 1574485 1773049 := bbase (se 2 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 1773049 = 1329787) (by norm_num)
theorem B2362877 : Blo 1574485 2362877 := bbase (se 3 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 2362877 = 886079) (by norm_num)
theorem B2362901 : Blo 1574485 2362901 := bbase (se 6 (by rfl) ⟨55380, by rfl⟩ : syracuseStep 2362901 = 110761) (by norm_num)
theorem B1682965 : Blo 1574485 1682965 := bbase (se 6 (by rfl) ⟨39444, by rfl⟩ : syracuseStep 1682965 = 78889) (by norm_num)
theorem B1773085 : Blo 1574485 1773085 := bbase (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) (by norm_num)
theorem B2362925 : Blo 1574485 2362925 := bbase (se 3 (by rfl) ⟨443048, by rfl⟩ : syracuseStep 2362925 = 886097) (by norm_num)
theorem B1773121 : Blo 1574485 1773121 := bbase (se 2 (by rfl) ⟨664920, by rfl⟩ : syracuseStep 1773121 = 1329841) (by norm_num)
theorem B3542597 : Blo 1574485 3542597 := bbase (se 4 (by rfl) ⟨332118, by rfl⟩ : syracuseStep 3542597 = 664237) (by norm_num)
theorem B2362949 : Blo 1574485 2362949 := bbase (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) (by norm_num)
theorem B1994321 : Blo 1574485 1994321 := bbase (se 2 (by rfl) ⟨747870, by rfl⟩ : syracuseStep 1994321 = 1495741) (by norm_num)
theorem B2362973 : Blo 1574485 2362973 := bbase (se 3 (by rfl) ⟨443057, by rfl⟩ : syracuseStep 2362973 = 886115) (by norm_num)
theorem B2657893 : Blo 1574485 2657893 := bbase (se 4 (by rfl) ⟨249177, by rfl⟩ : syracuseStep 2657893 = 498355) (by norm_num)
theorem B1773157 : Blo 1574485 1773157 := bbase (se 4 (by rfl) ⟨166233, by rfl⟩ : syracuseStep 1773157 = 332467) (by norm_num)
theorem B2362997 : Blo 1574485 2362997 := bbase (se 5 (by rfl) ⟨110765, by rfl⟩ : syracuseStep 2362997 = 221531) (by norm_num)
theorem B1994377 : Blo 1574485 1994377 := bbase (se 2 (by rfl) ⟨747891, by rfl⟩ : syracuseStep 1994377 = 1495783) (by norm_num)
theorem B1773193 : Blo 1574485 1773193 := bbase (se 2 (by rfl) ⟨664947, by rfl⟩ : syracuseStep 1773193 = 1329895) (by norm_num)
theorem B3542669 : Blo 1574485 3542669 := bbase (se 3 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 3542669 = 1328501) (by norm_num)
theorem B2363021 : Blo 1574485 2363021 := bbase (se 3 (by rfl) ⟨443066, by rfl⟩ : syracuseStep 2363021 = 886133) (by norm_num)
theorem B2363045 : Blo 1574485 2363045 := bbase (se 4 (by rfl) ⟨221535, by rfl⟩ : syracuseStep 2363045 = 443071) (by norm_num)
theorem B1773229 : Blo 1574485 1773229 := bbase (se 3 (by rfl) ⟨332480, by rfl⟩ : syracuseStep 1773229 = 664961) (by norm_num)
theorem B2657981 : Blo 1574485 2657981 := bbase (se 3 (by rfl) ⟨498371, by rfl⟩ : syracuseStep 2657981 = 996743) (by norm_num)
theorem B2363069 : Blo 1574485 2363069 := bbase (se 3 (by rfl) ⟨443075, by rfl⟩ : syracuseStep 2363069 = 886151) (by norm_num)
theorem B7573189 : Blo 1574485 7573189 := bbase (se 4 (by rfl) ⟨709986, by rfl⟩ : syracuseStep 7573189 = 1419973) (by norm_num)
theorem B1773265 : Blo 1574485 1773265 := bbase (se 2 (by rfl) ⟨664974, by rfl⟩ : syracuseStep 1773265 = 1329949) (by norm_num)
theorem B3542741 : Blo 1574485 3542741 := bbase (se 7 (by rfl) ⟨41516, by rfl⟩ : syracuseStep 3542741 = 83033) (by norm_num)
theorem B2363093 : Blo 1574485 2363093 := bbase (se 7 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 2363093 = 55385) (by norm_num)
theorem B2838245 : Blo 1574485 2838245 := bbase (se 4 (by rfl) ⟨266085, by rfl⟩ : syracuseStep 2838245 = 532171) (by norm_num)
theorem B1994473 : Blo 1574485 1994473 := bbase (se 2 (by rfl) ⟨747927, by rfl⟩ : syracuseStep 1994473 = 1495855) (by norm_num)
theorem B2363117 : Blo 1574485 2363117 := bbase (se 3 (by rfl) ⟨443084, by rfl⟩ : syracuseStep 2363117 = 886169) (by norm_num)
theorem B12775157 : Blo 1574485 12775157 := bbase (se 5 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 12775157 = 1197671) (by norm_num)
theorem B1773301 : Blo 1574485 1773301 := bbase (se 5 (by rfl) ⟨83123, by rfl⟩ : syracuseStep 1773301 = 166247) (by norm_num)
theorem B2363141 : Blo 1574485 2363141 := bbase (se 4 (by rfl) ⟨221544, by rfl⟩ : syracuseStep 2363141 = 443089) (by norm_num)
theorem B1773337 : Blo 1574485 1773337 := bbase (se 2 (by rfl) ⟨665001, by rfl⟩ : syracuseStep 1773337 = 1330003) (by norm_num)
theorem B3542813 : Blo 1574485 3542813 := bbase (se 3 (by rfl) ⟨664277, by rfl⟩ : syracuseStep 3542813 = 1328555) (by norm_num)
theorem B2363165 : Blo 1574485 2363165 := bbase (se 3 (by rfl) ⟨443093, by rfl⟩ : syracuseStep 2363165 = 886187) (by norm_num)
theorem B2363189 : Blo 1574485 2363189 := bbase (se 5 (by rfl) ⟨110774, by rfl⟩ : syracuseStep 2363189 = 221549) (by norm_num)
theorem B2658109 : Blo 1574485 2658109 := bbase (se 3 (by rfl) ⟨498395, by rfl⟩ : syracuseStep 2658109 = 996791) (by norm_num)
theorem B2879293 : Blo 1574485 2879293 := bbase (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) (by norm_num)
theorem B1773373 : Blo 1574485 1773373 := bbase (se 3 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 1773373 = 665015) (by norm_num)
theorem B2363213 : Blo 1574485 2363213 := bbase (se 3 (by rfl) ⟨443102, by rfl⟩ : syracuseStep 2363213 = 886205) (by norm_num)
theorem B1773409 : Blo 1574485 1773409 := bbase (se 2 (by rfl) ⟨665028, by rfl⟩ : syracuseStep 1773409 = 1330057) (by norm_num)
theorem B3542885 : Blo 1574485 3542885 := bbase (se 4 (by rfl) ⟨332145, by rfl⟩ : syracuseStep 3542885 = 664291) (by norm_num)
theorem B2363237 : Blo 1574485 2363237 := bbase (se 4 (by rfl) ⟨221553, by rfl⟩ : syracuseStep 2363237 = 443107) (by norm_num)
theorem B3592045 : Blo 1574485 3592045 := bbase (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) (by norm_num)
theorem B7974773 : Blo 1574485 7974773 := bbase (se 5 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 7974773 = 747635) (by norm_num)
theorem B5320565 : Blo 1574485 5320565 := bbase (se 5 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 5320565 = 498803) (by norm_num)
theorem B2273149 : Blo 1574485 2273149 := bbase (se 3 (by rfl) ⟨426215, by rfl⟩ : syracuseStep 2273149 = 852431) (by norm_num)
theorem B2363261 : Blo 1574485 2363261 := bbase (se 3 (by rfl) ⟨443111, by rfl⟩ : syracuseStep 2363261 = 886223) (by norm_num)
theorem B6729605 : Blo 1574485 6729605 := bbase (se 4 (by rfl) ⟨630900, by rfl⟩ : syracuseStep 6729605 = 1261801) (by norm_num)
theorem B1773445 : Blo 1574485 1773445 := bbase (se 4 (by rfl) ⟨166260, by rfl⟩ : syracuseStep 1773445 = 332521) (by norm_num)
theorem B1683337 : Blo 1574485 1683337 := bbase (se 2 (by rfl) ⟨631251, by rfl⟩ : syracuseStep 1683337 = 1262503) (by norm_num)
theorem B2658197 : Blo 1574485 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2363285 : Blo 1574485 2363285 := bbase (se 6 (by rfl) ⟨55389, by rfl⟩ : syracuseStep 2363285 = 110779) (by norm_num)
theorem B1994645 : Blo 1574485 1994645 := bbase (se 6 (by rfl) ⟨46749, by rfl⟩ : syracuseStep 1994645 = 93499) (by norm_num)
theorem B1773481 : Blo 1574485 1773481 := bbase (se 2 (by rfl) ⟨665055, by rfl⟩ : syracuseStep 1773481 = 1330111) (by norm_num)
theorem B3542957 : Blo 1574485 3542957 := bbase (se 3 (by rfl) ⟨664304, by rfl⟩ : syracuseStep 3542957 = 1328609) (by norm_num)
theorem B2363309 : Blo 1574485 2363309 := bbase (se 3 (by rfl) ⟨443120, by rfl⟩ : syracuseStep 2363309 = 886241) (by norm_num)
theorem B2363333 : Blo 1574485 2363333 := bbase (se 4 (by rfl) ⟨221562, by rfl⟩ : syracuseStep 2363333 = 443125) (by norm_num)
theorem B1994701 : Blo 1574485 1994701 := bbase (se 3 (by rfl) ⟨374006, by rfl⟩ : syracuseStep 1994701 = 748013) (by norm_num)
theorem B1773517 : Blo 1574485 1773517 := bbase (se 3 (by rfl) ⟨332534, by rfl⟩ : syracuseStep 1773517 = 665069) (by norm_num)
theorem B2363357 : Blo 1574485 2363357 := bbase (se 3 (by rfl) ⟨443129, by rfl⟩ : syracuseStep 2363357 = 886259) (by norm_num)
theorem B8089573 : Blo 1574485 8089573 := bbase (se 4 (by rfl) ⟨758397, by rfl⟩ : syracuseStep 8089573 = 1516795) (by norm_num)
theorem B3543029 : Blo 1574485 3543029 := bbase (se 5 (by rfl) ⟨166079, by rfl⟩ : syracuseStep 3543029 = 332159) (by norm_num)
theorem B2363381 : Blo 1574485 2363381 := bbase (se 5 (by rfl) ⟨110783, by rfl⟩ : syracuseStep 2363381 = 221567) (by norm_num)
theorem B5615621 : Blo 1574485 5615621 := bbase (se 4 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 5615621 = 1052929) (by norm_num)
theorem B2363405 : Blo 1574485 2363405 := bbase (se 3 (by rfl) ⟨443138, by rfl⟩ : syracuseStep 2363405 = 886277) (by norm_num)
theorem B2658325 : Blo 1574485 2658325 := bbase (se 6 (by rfl) ⟨62304, by rfl⟩ : syracuseStep 2658325 = 124609) (by norm_num)
theorem B6066197 : Blo 1574485 6066197 := bbase (se 6 (by rfl) ⟨142176, by rfl⟩ : syracuseStep 6066197 = 284353) (by norm_num)
theorem B2363429 : Blo 1574485 2363429 := bbase (se 4 (by rfl) ⟨221571, by rfl⟩ : syracuseStep 2363429 = 443143) (by norm_num)
theorem B1994797 : Blo 1574485 1994797 := bbase (se 3 (by rfl) ⟨374024, by rfl⟩ : syracuseStep 1994797 = 748049) (by norm_num)
theorem B5050421 : Blo 1574485 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B3543101 : Blo 1574485 3543101 := bbase (se 3 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 3543101 = 1328663) (by norm_num)
theorem B2363453 : Blo 1574485 2363453 := bbase (se 3 (by rfl) ⟨443147, by rfl⟩ : syracuseStep 2363453 = 886295) (by norm_num)
theorem B2363477 : Blo 1574485 2363477 := bbase (se 8 (by rfl) ⟨13848, by rfl⟩ : syracuseStep 2363477 = 27697) (by norm_num)
theorem B2658413 : Blo 1574485 2658413 := bbase (se 3 (by rfl) ⟨498452, by rfl⟩ : syracuseStep 2658413 = 996905) (by norm_num)
theorem B2363501 : Blo 1574485 2363501 := bbase (se 3 (by rfl) ⟨443156, by rfl⟩ : syracuseStep 2363501 = 886313) (by norm_num)
theorem B3543173 : Blo 1574485 3543173 := bbase (se 4 (by rfl) ⟨332172, by rfl⟩ : syracuseStep 3543173 = 664345) (by norm_num)
theorem B4485253 : Blo 1574485 4485253 := bbase (se 4 (by rfl) ⟨420492, by rfl⟩ : syracuseStep 4485253 = 840985) (by norm_num)
theorem B2363525 : Blo 1574485 2363525 := bbase (se 4 (by rfl) ⟨221580, by rfl⟩ : syracuseStep 2363525 = 443161) (by norm_num)
theorem B2363549 : Blo 1574485 2363549 := bbase (se 3 (by rfl) ⟨443165, by rfl⟩ : syracuseStep 2363549 = 886331) (by norm_num)
theorem B2363573 : Blo 1574485 2363573 := bbase (se 5 (by rfl) ⟨110792, by rfl⟩ : syracuseStep 2363573 = 221585) (by norm_num)
theorem B3838141 : Blo 1574485 3838141 := bbase (se 3 (by rfl) ⟨719651, by rfl⟩ : syracuseStep 3838141 = 1439303) (by norm_num)
theorem B3543245 : Blo 1574485 3543245 := bbase (se 3 (by rfl) ⟨664358, by rfl⟩ : syracuseStep 3543245 = 1328717) (by norm_num)
theorem B2363597 : Blo 1574485 2363597 := bbase (se 3 (by rfl) ⟨443174, by rfl⟩ : syracuseStep 2363597 = 886349) (by norm_num)
theorem B1994969 : Blo 1574485 1994969 := bbase (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) (by norm_num)
theorem B2363621 : Blo 1574485 2363621 := bbase (se 4 (by rfl) ⟨221589, by rfl⟩ : syracuseStep 2363621 = 443179) (by norm_num)
theorem B3985645 : Blo 1574485 3985645 := bbase (se 3 (by rfl) ⟨747308, by rfl⟩ : syracuseStep 3985645 = 1494617) (by norm_num)
theorem B2658541 : Blo 1574485 2658541 := bbase (se 3 (by rfl) ⟨498476, by rfl⟩ : syracuseStep 2658541 = 996953) (by norm_num)
theorem B2363645 : Blo 1574485 2363645 := bbase (se 3 (by rfl) ⟨443183, by rfl⟩ : syracuseStep 2363645 = 886367) (by norm_num)
theorem B1995025 : Blo 1574485 1995025 := bbase (se 2 (by rfl) ⟨748134, by rfl⟩ : syracuseStep 1995025 = 1496269) (by norm_num)
theorem B3543317 : Blo 1574485 3543317 := bbase (se 6 (by rfl) ⟨83046, by rfl⟩ : syracuseStep 3543317 = 166093) (by norm_num)
theorem B2363669 : Blo 1574485 2363669 := bbase (se 6 (by rfl) ⟨55398, by rfl⟩ : syracuseStep 2363669 = 110797) (by norm_num)
theorem B2363693 : Blo 1574485 2363693 := bbase (se 3 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 2363693 = 886385) (by norm_num)
theorem B11350325 : Blo 1574485 11350325 := bbase (se 5 (by rfl) ⟨532046, by rfl⟩ : syracuseStep 11350325 = 1064093) (by norm_num)
theorem B2658629 : Blo 1574485 2658629 := bbase (se 4 (by rfl) ⟨249246, by rfl⟩ : syracuseStep 2658629 = 498493) (by norm_num)
theorem B2363717 : Blo 1574485 2363717 := bbase (se 4 (by rfl) ⟨221598, by rfl⟩ : syracuseStep 2363717 = 443197) (by norm_num)
theorem B3985757 : Blo 1574485 3985757 := bbase (se 3 (by rfl) ⟨747329, by rfl⟩ : syracuseStep 3985757 = 1494659) (by norm_num)
theorem B3543389 : Blo 1574485 3543389 := bbase (se 3 (by rfl) ⟨664385, by rfl⟩ : syracuseStep 3543389 = 1328771) (by norm_num)
theorem B2363741 : Blo 1574485 2363741 := bbase (se 3 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 2363741 = 886403) (by norm_num)
theorem B1995121 : Blo 1574485 1995121 := bbase (se 2 (by rfl) ⟨748170, by rfl⟩ : syracuseStep 1995121 = 1496341) (by norm_num)
theorem B4043125 : Blo 1574485 4043125 := bbase (se 5 (by rfl) ⟨189521, by rfl⟩ : syracuseStep 4043125 = 379043) (by norm_num)
theorem B2363765 : Blo 1574485 2363765 := bbase (se 5 (by rfl) ⟨110801, by rfl⟩ : syracuseStep 2363765 = 221603) (by norm_num)
theorem B2363789 : Blo 1574485 2363789 := bbase (se 3 (by rfl) ⟨443210, by rfl⟩ : syracuseStep 2363789 = 886421) (by norm_num)
theorem B3543461 : Blo 1574485 3543461 := bbase (se 4 (by rfl) ⟨332199, by rfl⟩ : syracuseStep 3543461 = 664399) (by norm_num)
theorem B2363813 : Blo 1574485 2363813 := bbase (se 4 (by rfl) ⟨221607, by rfl⟩ : syracuseStep 2363813 = 443215) (by norm_num)
theorem B2363837 : Blo 1574485 2363837 := bbase (se 3 (by rfl) ⟨443219, by rfl⟩ : syracuseStep 2363837 = 886439) (by norm_num)
theorem B2658757 : Blo 1574485 2658757 := bbase (se 4 (by rfl) ⟨249258, by rfl⟩ : syracuseStep 2658757 = 498517) (by norm_num)
theorem B64664021 : Blo 1574485 64664021 := bbase (se 7 (by rfl) ⟨757781, by rfl⟩ : syracuseStep 64664021 = 1515563) (by norm_num)
theorem B15143381 : Blo 1574485 15143381 := bbase (se 7 (by rfl) ⟨177461, by rfl⟩ : syracuseStep 15143381 = 354923) (by norm_num)
theorem B2363861 : Blo 1574485 2363861 := bbase (se 7 (by rfl) ⟨27701, by rfl⟩ : syracuseStep 2363861 = 55403) (by norm_num)
theorem B5984725 : Blo 1574485 5984725 := bbase (se 7 (by rfl) ⟨70133, by rfl⟩ : syracuseStep 5984725 = 140267) (by norm_num)
theorem B5681621 : Blo 1574485 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B3543533 : Blo 1574485 3543533 := bbase (se 3 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 3543533 = 1328825) (by norm_num)
theorem B2363885 : Blo 1574485 2363885 := bbase (se 3 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 2363885 = 886457) (by norm_num)
theorem B2363909 : Blo 1574485 2363909 := bbase (se 4 (by rfl) ⟨221616, by rfl⟩ : syracuseStep 2363909 = 443233) (by norm_num)
theorem B3985949 : Blo 1574485 3985949 := bbase (se 3 (by rfl) ⟨747365, by rfl⟩ : syracuseStep 3985949 = 1494731) (by norm_num)
theorem B2658845 : Blo 1574485 2658845 := bbase (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) (by norm_num)
theorem B2363933 : Blo 1574485 2363933 := bbase (se 3 (by rfl) ⟨443237, by rfl⟩ : syracuseStep 2363933 = 886475) (by norm_num)
theorem B3838493 : Blo 1574485 3838493 := bbase (se 3 (by rfl) ⟨719717, by rfl⟩ : syracuseStep 3838493 = 1439435) (by norm_num)
theorem B4256309 : Blo 1574485 4256309 := bbase (se 5 (by rfl) ⟨199514, by rfl⟩ : syracuseStep 4256309 = 399029) (by norm_num)
theorem B3543605 : Blo 1574485 3543605 := bbase (se 5 (by rfl) ⟨166106, by rfl⟩ : syracuseStep 3543605 = 332213) (by norm_num)
theorem B8974901 : Blo 1574485 8974901 := bbase (se 5 (by rfl) ⟨420698, by rfl⟩ : syracuseStep 8974901 = 841397) (by norm_num)
theorem B2363957 : Blo 1574485 2363957 := bbase (se 5 (by rfl) ⟨110810, by rfl⟩ : syracuseStep 2363957 = 221621) (by norm_num)
theorem B6386245 : Blo 1574485 6386245 := bbase (se 4 (by rfl) ⟨598710, by rfl⟩ : syracuseStep 6386245 = 1197421) (by norm_num)
theorem B2363981 : Blo 1574485 2363981 := bbase (se 3 (by rfl) ⟨443246, by rfl⟩ : syracuseStep 2363981 = 886493) (by norm_num)
theorem B2839133 : Blo 1574485 2839133 := bbase (se 3 (by rfl) ⟨532337, by rfl⟩ : syracuseStep 2839133 = 1064675) (by norm_num)
theorem B2364005 : Blo 1574485 2364005 := bbase (se 4 (by rfl) ⟨221625, by rfl⟩ : syracuseStep 2364005 = 443251) (by norm_num)
theorem B3543677 : Blo 1574485 3543677 := bbase (se 3 (by rfl) ⟨664439, by rfl⟩ : syracuseStep 3543677 = 1328879) (by norm_num)
theorem B2364029 : Blo 1574485 2364029 := bbase (se 3 (by rfl) ⟨443255, by rfl⟩ : syracuseStep 2364029 = 886511) (by norm_num)
theorem B2364053 : Blo 1574485 2364053 := bbase (se 6 (by rfl) ⟨55407, by rfl⟩ : syracuseStep 2364053 = 110815) (by norm_num)
theorem B2658973 : Blo 1574485 2658973 := bbase (se 3 (by rfl) ⟨498557, by rfl⟩ : syracuseStep 2658973 = 997115) (by norm_num)
theorem B2396837 : Blo 1574485 2396837 := bbase (se 4 (by rfl) ⟨224703, by rfl⟩ : syracuseStep 2396837 = 449407) (by norm_num)
theorem B2364077 : Blo 1574485 2364077 := bbase (se 3 (by rfl) ⟨443264, by rfl⟩ : syracuseStep 2364077 = 886529) (by norm_num)
theorem B3543749 : Blo 1574485 3543749 := bbase (se 4 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 3543749 = 664453) (by norm_num)
theorem B2364101 : Blo 1574485 2364101 := bbase (se 4 (by rfl) ⟨221634, by rfl⟩ : syracuseStep 2364101 = 443269) (by norm_num)
theorem B2364125 : Blo 1574485 2364125 := bbase (se 3 (by rfl) ⟨443273, by rfl⟩ : syracuseStep 2364125 = 886547) (by norm_num)
theorem B2659061 : Blo 1574485 2659061 := bbase (se 5 (by rfl) ⟨124643, by rfl⟩ : syracuseStep 2659061 = 249287) (by norm_num)
theorem B2364149 : Blo 1574485 2364149 := bbase (se 5 (by rfl) ⟨110819, by rfl⟩ : syracuseStep 2364149 = 221639) (by norm_num)
theorem B5985029 : Blo 1574485 5985029 := bbase (se 4 (by rfl) ⟨561096, by rfl⟩ : syracuseStep 5985029 = 1122193) (by norm_num)
theorem B3543821 : Blo 1574485 3543821 := bbase (se 3 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 3543821 = 1328933) (by norm_num)
theorem B2364173 : Blo 1574485 2364173 := bbase (se 3 (by rfl) ⟨443282, by rfl⟩ : syracuseStep 2364173 = 886565) (by norm_num)
theorem B2364197 : Blo 1574485 2364197 := bbase (se 4 (by rfl) ⟨221643, by rfl⟩ : syracuseStep 2364197 = 443287) (by norm_num)
theorem B2364221 : Blo 1574485 2364221 := bbase (se 3 (by rfl) ⟨443291, by rfl⟩ : syracuseStep 2364221 = 886583) (by norm_num)
theorem B3543893 : Blo 1574485 3543893 := bbase (se 9 (by rfl) ⟨10382, by rfl⟩ : syracuseStep 3543893 = 20765) (by norm_num)
theorem B2364245 : Blo 1574485 2364245 := bbase (se 9 (by rfl) ⟨6926, by rfl⟩ : syracuseStep 2364245 = 13853) (by norm_num)
theorem B2364269 : Blo 1574485 2364269 := bbase (se 3 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 2364269 = 886601) (by norm_num)
theorem B3986293 : Blo 1574485 3986293 := bbase (se 5 (by rfl) ⟨186857, by rfl⟩ : syracuseStep 3986293 = 373715) (by norm_num)
theorem B2659189 : Blo 1574485 2659189 := bbase (se 5 (by rfl) ⟨124649, by rfl⟩ : syracuseStep 2659189 = 249299) (by norm_num)
theorem B3363709 : Blo 1574485 3363709 := bbase (se 3 (by rfl) ⟨630695, by rfl⟩ : syracuseStep 3363709 = 1261391) (by norm_num)
theorem B2839421 : Blo 1574485 2839421 := bbase (se 3 (by rfl) ⟨532391, by rfl⟩ : syracuseStep 2839421 = 1064783) (by norm_num)
theorem B2364293 : Blo 1574485 2364293 := bbase (se 4 (by rfl) ⟨221652, by rfl⟩ : syracuseStep 2364293 = 443305) (by norm_num)
theorem B3543965 : Blo 1574485 3543965 := bbase (se 3 (by rfl) ⟨664493, by rfl⟩ : syracuseStep 3543965 = 1328987) (by norm_num)
theorem B2364317 : Blo 1574485 2364317 := bbase (se 3 (by rfl) ⟨443309, by rfl⟩ : syracuseStep 2364317 = 886619) (by norm_num)
theorem B2364341 : Blo 1574485 2364341 := bbase (se 5 (by rfl) ⟨110828, by rfl⟩ : syracuseStep 2364341 = 221657) (by norm_num)
theorem B2659277 : Blo 1574485 2659277 := bbase (se 3 (by rfl) ⟨498614, by rfl⟩ : syracuseStep 2659277 = 997229) (by norm_num)
theorem B2364365 : Blo 1574485 2364365 := bbase (se 3 (by rfl) ⟨443318, by rfl⟩ : syracuseStep 2364365 = 886637) (by norm_num)
theorem B3986405 : Blo 1574485 3986405 := bbase (se 4 (by rfl) ⟨373725, by rfl⟩ : syracuseStep 3986405 = 747451) (by norm_num)
theorem B3544037 : Blo 1574485 3544037 := bbase (se 4 (by rfl) ⟨332253, by rfl⟩ : syracuseStep 3544037 = 664507) (by norm_num)
theorem B2364389 : Blo 1574485 2364389 := bbase (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) (by norm_num)
theorem B2364413 : Blo 1574485 2364413 := bbase (se 3 (by rfl) ⟨443327, by rfl⟩ : syracuseStep 2364413 = 886655) (by norm_num)
theorem B2364437 : Blo 1574485 2364437 := bbase (se 6 (by rfl) ⟨55416, by rfl⟩ : syracuseStep 2364437 = 110833) (by norm_num)
theorem B3544109 : Blo 1574485 3544109 := bbase (se 3 (by rfl) ⟨664520, by rfl⟩ : syracuseStep 3544109 = 1329041) (by norm_num)
theorem B2364461 : Blo 1574485 2364461 := bbase (se 3 (by rfl) ⟨443336, by rfl⟩ : syracuseStep 2364461 = 886673) (by norm_num)
theorem B2364485 : Blo 1574485 2364485 := bbase (se 4 (by rfl) ⟨221670, by rfl⟩ : syracuseStep 2364485 = 443341) (by norm_num)
theorem B2659405 : Blo 1574485 2659405 := bbase (se 3 (by rfl) ⟨498638, by rfl⟩ : syracuseStep 2659405 = 997277) (by norm_num)
theorem B2364509 : Blo 1574485 2364509 := bbase (se 3 (by rfl) ⟨443345, by rfl⟩ : syracuseStep 2364509 = 886691) (by norm_num)
theorem B3544181 : Blo 1574485 3544181 := bbase (se 5 (by rfl) ⟨166133, by rfl⟩ : syracuseStep 3544181 = 332267) (by norm_num)
theorem B2364533 : Blo 1574485 2364533 := bbase (se 5 (by rfl) ⟨110837, by rfl⟩ : syracuseStep 2364533 = 221675) (by norm_num)
theorem B7976069 : Blo 1574485 7976069 := bbase (se 4 (by rfl) ⟨747756, by rfl⟩ : syracuseStep 7976069 = 1495513) (by norm_num)
theorem B2364557 : Blo 1574485 2364557 := bbase (se 3 (by rfl) ⟨443354, by rfl⟩ : syracuseStep 2364557 = 886709) (by norm_num)
theorem B3986597 : Blo 1574485 3986597 := bbase (se 4 (by rfl) ⟨373743, by rfl⟩ : syracuseStep 3986597 = 747487) (by norm_num)
theorem B2659493 : Blo 1574485 2659493 := bbase (se 4 (by rfl) ⟨249327, by rfl⟩ : syracuseStep 2659493 = 498655) (by norm_num)
theorem B2364581 : Blo 1574485 2364581 := bbase (se 4 (by rfl) ⟨221679, by rfl⟩ : syracuseStep 2364581 = 443359) (by norm_num)
theorem B3544253 : Blo 1574485 3544253 := bbase (se 3 (by rfl) ⟨664547, by rfl⟩ : syracuseStep 3544253 = 1329095) (by norm_num)
theorem B2364605 : Blo 1574485 2364605 := bbase (se 3 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 2364605 = 886727) (by norm_num)
theorem B4486357 : Blo 1574485 4486357 := bbase (se 7 (by rfl) ⟨52574, by rfl⟩ : syracuseStep 4486357 = 105149) (by norm_num)
theorem B2364629 : Blo 1574485 2364629 := bbase (se 7 (by rfl) ⟨27710, by rfl⟩ : syracuseStep 2364629 = 55421) (by norm_num)
theorem B2364653 : Blo 1574485 2364653 := bbase (se 3 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 2364653 = 886745) (by norm_num)
theorem B3364085 : Blo 1574485 3364085 := bbase (se 5 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 3364085 = 315383) (by norm_num)
theorem B3544325 : Blo 1574485 3544325 := bbase (se 4 (by rfl) ⟨332280, by rfl⟩ : syracuseStep 3544325 = 664561) (by norm_num)
theorem B2364677 : Blo 1574485 2364677 := bbase (se 4 (by rfl) ⟨221688, by rfl⟩ : syracuseStep 2364677 = 443377) (by norm_num)
theorem B3192085 : Blo 1574485 3192085 := bbase (se 6 (by rfl) ⟨74814, by rfl⟩ : syracuseStep 3192085 = 149629) (by norm_num)
theorem B2364701 : Blo 1574485 2364701 := bbase (se 3 (by rfl) ⟨443381, by rfl⟩ : syracuseStep 2364701 = 886763) (by norm_num)
theorem B2659621 : Blo 1574485 2659621 := bbase (se 4 (by rfl) ⟨249339, by rfl⟩ : syracuseStep 2659621 = 498679) (by norm_num)
theorem B2364725 : Blo 1574485 2364725 := bbase (se 5 (by rfl) ⟨110846, by rfl⟩ : syracuseStep 2364725 = 221693) (by norm_num)
theorem B3544397 : Blo 1574485 3544397 := bbase (se 3 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 3544397 = 1329149) (by norm_num)
theorem B2659709 : Blo 1574485 2659709 := bbase (se 3 (by rfl) ⟨498695, by rfl⟩ : syracuseStep 2659709 = 997391) (by norm_num)
theorem B3544469 : Blo 1574485 3544469 := bbase (se 6 (by rfl) ⟨83073, by rfl⟩ : syracuseStep 3544469 = 166147) (by norm_num)
theorem B13456853 : Blo 1574485 13456853 := bbase (se 7 (by rfl) ⟨157697, by rfl⟩ : syracuseStep 13456853 = 315395) (by norm_num)
theorem B3544541 : Blo 1574485 3544541 := bbase (se 3 (by rfl) ⟨664601, by rfl⟩ : syracuseStep 3544541 = 1329203) (by norm_num)
theorem B3986941 : Blo 1574485 3986941 := bbase (se 3 (by rfl) ⟨747551, by rfl⟩ : syracuseStep 3986941 = 1495103) (by norm_num)
theorem B2659837 : Blo 1574485 2659837 := bbase (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) (by norm_num)
theorem B5314085 : Blo 1574485 5314085 := bbase (se 4 (by rfl) ⟨498195, by rfl⟩ : syracuseStep 5314085 = 996391) (by norm_num)
theorem B2242085 : Blo 1574485 2242085 := bbase (se 4 (by rfl) ⟨210195, by rfl⟩ : syracuseStep 2242085 = 420391) (by norm_num)
theorem B3544613 : Blo 1574485 3544613 := bbase (se 4 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 3544613 = 664615) (by norm_num)
theorem B2659925 : Blo 1574485 2659925 := bbase (se 8 (by rfl) ⟨15585, by rfl⟩ : syracuseStep 2659925 = 31171) (by norm_num)
theorem B3987053 : Blo 1574485 3987053 := bbase (se 3 (by rfl) ⟨747572, by rfl⟩ : syracuseStep 3987053 = 1495145) (by norm_num)
theorem B3544685 : Blo 1574485 3544685 := bbase (se 3 (by rfl) ⟨664628, by rfl⟩ : syracuseStep 3544685 = 1329257) (by norm_num)
theorem B2021041 : Blo 1574485 2021041 := bbase (se 2 (by rfl) ⟨757890, by rfl⟩ : syracuseStep 2021041 = 1515781) (by norm_num)
theorem B3544757 : Blo 1574485 3544757 := bbase (se 5 (by rfl) ⟨166160, by rfl⟩ : syracuseStep 3544757 = 332321) (by norm_num)
theorem B2660053 : Blo 1574485 2660053 := bbase (se 7 (by rfl) ⟨31172, by rfl⟩ : syracuseStep 2660053 = 62345) (by norm_num)
theorem B3544829 : Blo 1574485 3544829 := bbase (se 3 (by rfl) ⟨664655, by rfl⟩ : syracuseStep 3544829 = 1329311) (by norm_num)
theorem B3192605 : Blo 1574485 3192605 := bbase (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) (by norm_num)
theorem B3987245 : Blo 1574485 3987245 := bbase (se 3 (by rfl) ⟨747608, by rfl⟩ : syracuseStep 3987245 = 1495217) (by norm_num)
theorem B2660141 : Blo 1574485 2660141 := bbase (se 3 (by rfl) ⟨498776, by rfl⟩ : syracuseStep 2660141 = 997553) (by norm_num)
theorem B5674805 : Blo 1574485 5674805 := bbase (se 5 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 5674805 = 532013) (by norm_num)
theorem B3544901 : Blo 1574485 3544901 := bbase (se 4 (by rfl) ⟨332334, by rfl⟩ : syracuseStep 3544901 = 664669) (by norm_num)
theorem B2840437 : Blo 1574485 2840437 := bbase (se 5 (by rfl) ⟨133145, by rfl⟩ : syracuseStep 2840437 = 266291) (by norm_num)
theorem B3544973 : Blo 1574485 3544973 := bbase (se 3 (by rfl) ⟨664682, by rfl⟩ : syracuseStep 3544973 = 1329365) (by norm_num)
theorem B2660269 : Blo 1574485 2660269 := bbase (se 3 (by rfl) ⟨498800, by rfl⟩ : syracuseStep 2660269 = 997601) (by norm_num)
theorem B5314517 : Blo 1574485 5314517 := bbase (se 7 (by rfl) ⟨62279, by rfl⟩ : syracuseStep 5314517 = 124559) (by norm_num)
theorem B3545045 : Blo 1574485 3545045 := bbase (se 7 (by rfl) ⟨41543, by rfl⟩ : syracuseStep 3545045 = 83087) (by norm_num)
theorem B3545117 : Blo 1574485 3545117 := bbase (se 3 (by rfl) ⟨664709, by rfl⟩ : syracuseStep 3545117 = 1329419) (by norm_num)
theorem B11352149 : Blo 1574485 11352149 := bbase (se 8 (by rfl) ⟨66516, by rfl⟩ : syracuseStep 11352149 = 133033) (by norm_num)
theorem B3545189 : Blo 1574485 3545189 := bbase (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) (by norm_num)
theorem B3987589 : Blo 1574485 3987589 := bbase (se 4 (by rfl) ⟨373836, by rfl⟩ : syracuseStep 3987589 = 747673) (by norm_num)
theorem B2128013 : Blo 1574485 2128013 := bbase (se 3 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 2128013 = 798005) (by norm_num)
theorem B3545261 : Blo 1574485 3545261 := bbase (se 3 (by rfl) ⟨664736, by rfl⟩ : syracuseStep 3545261 = 1329473) (by norm_num)
theorem B4856021 : Blo 1574485 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B2021593 : Blo 1574485 2021593 := bbase (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) (by norm_num)
theorem B3987701 : Blo 1574485 3987701 := bbase (se 5 (by rfl) ⟨186923, by rfl⟩ : syracuseStep 3987701 = 373847) (by norm_num)
theorem B3545333 : Blo 1574485 3545333 := bbase (se 5 (by rfl) ⟨166187, by rfl⟩ : syracuseStep 3545333 = 332375) (by norm_num)
theorem B2242837 : Blo 1574485 2242837 := bbase (se 6 (by rfl) ⟨52566, by rfl⟩ : syracuseStep 2242837 = 105133) (by norm_num)
theorem B2840869 : Blo 1574485 2840869 := bbase (se 4 (by rfl) ⟨266331, by rfl⟩ : syracuseStep 2840869 = 532663) (by norm_num)
theorem B3545405 : Blo 1574485 3545405 := bbase (se 3 (by rfl) ⟨664763, by rfl⟩ : syracuseStep 3545405 = 1329527) (by norm_num)
theorem B5314949 : Blo 1574485 5314949 := bbase (se 4 (by rfl) ⟨498276, by rfl⟩ : syracuseStep 5314949 = 996553) (by norm_num)
theorem B3545477 : Blo 1574485 3545477 := bbase (se 4 (by rfl) ⟨332388, by rfl⟩ : syracuseStep 3545477 = 664777) (by norm_num)
theorem B7977365 : Blo 1574485 7977365 := bbase (se 6 (by rfl) ⟨186969, by rfl⟩ : syracuseStep 7977365 = 373939) (by norm_num)
theorem B2128285 : Blo 1574485 2128285 := bbase (se 3 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 2128285 = 798107) (by norm_num)
theorem B3987893 : Blo 1574485 3987893 := bbase (se 5 (by rfl) ⟨186932, by rfl⟩ : syracuseStep 3987893 = 373865) (by norm_num)
theorem B3545549 : Blo 1574485 3545549 := bbase (se 3 (by rfl) ⟨664790, by rfl⟩ : syracuseStep 3545549 = 1329581) (by norm_num)
theorem B3545621 : Blo 1574485 3545621 := bbase (se 6 (by rfl) ⟨83100, by rfl⟩ : syracuseStep 3545621 = 166201) (by norm_num)
theorem B3545693 : Blo 1574485 3545693 := bbase (se 3 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 3545693 = 1329635) (by norm_num)
theorem B3545765 : Blo 1574485 3545765 := bbase (se 4 (by rfl) ⟨332415, by rfl⟩ : syracuseStep 3545765 = 664831) (by norm_num)
theorem B4487861 : Blo 1574485 4487861 := bbase (se 5 (by rfl) ⟨210368, by rfl⟩ : syracuseStep 4487861 = 420737) (by norm_num)
theorem B5044949 : Blo 1574485 5044949 := bbase (se 7 (by rfl) ⟨59120, by rfl⟩ : syracuseStep 5044949 = 118241) (by norm_num)
theorem B3545837 : Blo 1574485 3545837 := bbase (se 3 (by rfl) ⟨664844, by rfl⟩ : syracuseStep 3545837 = 1329689) (by norm_num)
theorem B3988237 : Blo 1574485 3988237 := bbase (se 3 (by rfl) ⟨747794, by rfl⟩ : syracuseStep 3988237 = 1495589) (by norm_num)
theorem B5315381 : Blo 1574485 5315381 := bbase (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) (by norm_num)
theorem B3545909 : Blo 1574485 3545909 := bbase (se 5 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 3545909 = 332429) (by norm_num)
theorem B3365725 : Blo 1574485 3365725 := bbase (se 3 (by rfl) ⟨631073, by rfl⟩ : syracuseStep 3365725 = 1262147) (by norm_num)
theorem B3988349 : Blo 1574485 3988349 := bbase (se 3 (by rfl) ⟨747815, by rfl⟩ : syracuseStep 3988349 = 1495631) (by norm_num)
theorem B3545981 : Blo 1574485 3545981 := bbase (se 3 (by rfl) ⟨664871, by rfl⟩ : syracuseStep 3545981 = 1329743) (by norm_num)
theorem B3546053 : Blo 1574485 3546053 := bbase (se 4 (by rfl) ⟨332442, by rfl⟩ : syracuseStep 3546053 = 664885) (by norm_num)
theorem B3193805 : Blo 1574485 3193805 := bbase (se 3 (by rfl) ⟨598838, by rfl⟩ : syracuseStep 3193805 = 1197677) (by norm_num)
theorem B3546125 : Blo 1574485 3546125 := bbase (se 3 (by rfl) ⟨664898, by rfl⟩ : syracuseStep 3546125 = 1329797) (by norm_num)
theorem B2243629 : Blo 1574485 2243629 := bbase (se 3 (by rfl) ⟨420680, by rfl⟩ : syracuseStep 2243629 = 841361) (by norm_num)
theorem B3988541 : Blo 1574485 3988541 := bbase (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) (by norm_num)
theorem B1596493 : Blo 1574485 1596493 := bbase (se 3 (by rfl) ⟨299342, by rfl⟩ : syracuseStep 1596493 = 598685) (by norm_num)
theorem B3546197 : Blo 1574485 3546197 := bbase (se 8 (by rfl) ⟨20778, by rfl⟩ : syracuseStep 3546197 = 41557) (by norm_num)
theorem B1596529 : Blo 1574485 1596529 := bbase (se 2 (by rfl) ⟨598698, by rfl⟩ : syracuseStep 1596529 = 1197397) (by norm_num)
theorem B11361397 : Blo 1574485 11361397 := bbase (se 5 (by rfl) ⟨532565, by rfl⟩ : syracuseStep 11361397 = 1065131) (by norm_num)
theorem B2522269 : Blo 1574485 2522269 := bbase (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) (by norm_num)
theorem B3546269 : Blo 1574485 3546269 := bbase (se 3 (by rfl) ⟨664925, by rfl⟩ : syracuseStep 3546269 = 1329851) (by norm_num)
theorem B1891525 : Blo 1574485 1891525 := bbase (se 4 (by rfl) ⟨177330, by rfl⟩ : syracuseStep 1891525 = 354661) (by norm_num)
theorem B5979365 : Blo 1574485 5979365 := bbase (se 4 (by rfl) ⟨560565, by rfl⟩ : syracuseStep 5979365 = 1121131) (by norm_num)
theorem B5315813 : Blo 1574485 5315813 := bbase (se 4 (by rfl) ⟨498357, by rfl⟩ : syracuseStep 5315813 = 996715) (by norm_num)
theorem B3546341 : Blo 1574485 3546341 := bbase (se 4 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 3546341 = 664939) (by norm_num)
theorem B2989325 : Blo 1574485 2989325 := bbase (se 3 (by rfl) ⟨560498, by rfl⟩ : syracuseStep 2989325 = 1120997) (by norm_num)
theorem B3546413 : Blo 1574485 3546413 := bbase (se 3 (by rfl) ⟨664952, by rfl⟩ : syracuseStep 3546413 = 1329905) (by norm_num)
theorem B8969525 : Blo 1574485 8969525 := bbase (se 5 (by rfl) ⟨420446, by rfl⟩ : syracuseStep 8969525 = 840893) (by norm_num)
theorem B4259141 : Blo 1574485 4259141 := bbase (se 4 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 4259141 = 798589) (by norm_num)
theorem B5610853 : Blo 1574485 5610853 := bbase (se 4 (by rfl) ⟨526017, by rfl⟩ : syracuseStep 5610853 = 1052035) (by norm_num)
theorem B3546485 : Blo 1574485 3546485 := bbase (se 5 (by rfl) ⟨166241, by rfl⟩ : syracuseStep 3546485 = 332483) (by norm_num)
theorem B2243965 : Blo 1574485 2243965 := bbase (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) (by norm_num)
theorem B3988885 : Blo 1574485 3988885 := bbase (se 6 (by rfl) ⟨93489, by rfl⟩ : syracuseStep 3988885 = 186979) (by norm_num)
theorem B2989477 : Blo 1574485 2989477 := bbase (se 4 (by rfl) ⟨280263, by rfl⟩ : syracuseStep 2989477 = 560527) (by norm_num)
theorem B3546557 : Blo 1574485 3546557 := bbase (se 3 (by rfl) ⟨664979, by rfl⟩ : syracuseStep 3546557 = 1329959) (by norm_num)
theorem B2694637 : Blo 1574485 2694637 := bbase (se 3 (by rfl) ⟨505244, by rfl⟩ : syracuseStep 2694637 = 1010489) (by norm_num)
theorem B5979653 : Blo 1574485 5979653 := bbase (se 4 (by rfl) ⟨560592, by rfl⟩ : syracuseStep 5979653 = 1121185) (by norm_num)
theorem B3988997 : Blo 1574485 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B3546629 : Blo 1574485 3546629 := bbase (se 4 (by rfl) ⟨332496, by rfl⟩ : syracuseStep 3546629 = 664993) (by norm_num)
theorem B3546701 : Blo 1574485 3546701 := bbase (se 3 (by rfl) ⟨665006, by rfl⟩ : syracuseStep 3546701 = 1330013) (by norm_num)
theorem B2244181 : Blo 1574485 2244181 := bbase (se 8 (by rfl) ⟨13149, by rfl⟩ : syracuseStep 2244181 = 26299) (by norm_num)
theorem B5316245 : Blo 1574485 5316245 := bbase (se 6 (by rfl) ⟨124599, by rfl⟩ : syracuseStep 5316245 = 249199) (by norm_num)
theorem B3546773 : Blo 1574485 3546773 := bbase (se 6 (by rfl) ⟨83127, by rfl⟩ : syracuseStep 3546773 = 166255) (by norm_num)
theorem B7978661 : Blo 1574485 7978661 := bbase (se 4 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 7978661 = 1495999) (by norm_num)
theorem B2916013 : Blo 1574485 2916013 := bbase (se 3 (by rfl) ⟨546752, by rfl⟩ : syracuseStep 2916013 = 1093505) (by norm_num)
theorem B2522821 : Blo 1574485 2522821 := bbase (se 4 (by rfl) ⟨236514, by rfl⟩ : syracuseStep 2522821 = 473029) (by norm_num)
theorem B3989189 : Blo 1574485 3989189 := bbase (se 4 (by rfl) ⟨373986, by rfl⟩ : syracuseStep 3989189 = 747973) (by norm_num)
theorem B2989781 : Blo 1574485 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B24592085 : Blo 1574485 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B3366613 : Blo 1574485 3366613 := bbase (se 7 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 3366613 = 78905) (by norm_num)
theorem B3546845 : Blo 1574485 3546845 := bbase (se 3 (by rfl) ⟨665033, by rfl⟩ : syracuseStep 3546845 = 1330067) (by norm_num)
theorem B3546917 : Blo 1574485 3546917 := bbase (se 4 (by rfl) ⟨332523, by rfl⟩ : syracuseStep 3546917 = 665047) (by norm_num)
theorem B4792117 : Blo 1574485 4792117 := bbase (se 5 (by rfl) ⟨224630, by rfl⟩ : syracuseStep 4792117 = 449261) (by norm_num)
theorem B6733637 : Blo 1574485 6733637 := bbase (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) (by norm_num)
theorem B3546989 : Blo 1574485 3546989 := bbase (se 3 (by rfl) ⟨665060, by rfl⟩ : syracuseStep 3546989 = 1330121) (by norm_num)
theorem B10092437 : Blo 1574485 10092437 := bbase (se 6 (by rfl) ⟨236541, by rfl⟩ : syracuseStep 10092437 = 473083) (by norm_num)
theorem B4317077 : Blo 1574485 4317077 := bbase (se 6 (by rfl) ⟨101181, by rfl⟩ : syracuseStep 4317077 = 202363) (by norm_num)
theorem B3547061 : Blo 1574485 3547061 := bbase (se 5 (by rfl) ⟨166268, by rfl⟩ : syracuseStep 3547061 = 332537) (by norm_num)
theorem B2523077 : Blo 1574485 2523077 := bbase (se 4 (by rfl) ⟨236538, by rfl⟩ : syracuseStep 2523077 = 473077) (by norm_num)
theorem B2244557 : Blo 1574485 2244557 := bbase (se 3 (by rfl) ⟨420854, by rfl⟩ : syracuseStep 2244557 = 841709) (by norm_num)
theorem B5046229 : Blo 1574485 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B3743747 : Blo 1574485 3743747 := bstep (se 1 (by rfl) ⟨2807810, by rfl⟩ : syracuseStep 3743747 = 5615621) B5615621
theorem B3366947 : Blo 1574485 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B5980337 : Blo 1574485 5980337 := bstep (se 2 (by rfl) ⟨2242626, by rfl⟩ : syracuseStep 5980337 = 4485253) B4485253
theorem B5316785 : Blo 1574485 5316785 := bstep (se 2 (by rfl) ⟨1993794, by rfl⟩ : syracuseStep 5316785 = 3987589) B3987589
theorem B2695457 : Blo 1574485 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B5046563 : Blo 1574485 5046563 := bstep (se 1 (by rfl) ⟨3784922, by rfl⟩ : syracuseStep 5046563 = 7569845) B7569845
theorem B10092869 : Blo 1574485 10092869 := bstep (se 4 (by rfl) ⟨946206, by rfl⟩ : syracuseStep 10092869 = 1892413) B1892413
theorem B2990449 : Blo 1574485 2990449 := bstep (se 2 (by rfl) ⟨1121418, by rfl⟩ : syracuseStep 2990449 = 2242837) B2242837
theorem B1892755 : Blo 1574485 1892755 := bstep (se 1 (by rfl) ⟨1419566, by rfl⟩ : syracuseStep 1892755 = 2839133) B2839133
theorem B3989969 : Blo 1574485 3989969 := bstep (se 2 (by rfl) ⟨1496238, by rfl⟩ : syracuseStep 3989969 = 2992477) B2992477
theorem B5390833 : Blo 1574485 5390833 := bstep (se 2 (by rfl) ⟨2021562, by rfl⟩ : syracuseStep 5390833 = 4043125) B4043125
theorem B3990019 : Blo 1574485 3990019 := bstep (se 1 (by rfl) ⟨2992514, by rfl⟩ : syracuseStep 3990019 = 5985029) B5985029
theorem B4260397 : Blo 1574485 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B11960945 : Blo 1574485 11960945 := bstep (se 2 (by rfl) ⟨4485354, by rfl⟩ : syracuseStep 11960945 = 8970709) B8970709
theorem B7979633 : Blo 1574485 7979633 := bstep (se 2 (by rfl) ⟨2992362, by rfl⟩ : syracuseStep 7979633 = 5984725) B5984725
theorem B3990161 : Blo 1574485 3990161 := bstep (se 2 (by rfl) ⟨1496310, by rfl⟩ : syracuseStep 3990161 = 2992621) B2992621
theorem B1704611 : Blo 1574485 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B7570097 : Blo 1574485 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B13460165 : Blo 1574485 13460165 := bstep (se 4 (by rfl) ⟨1261890, by rfl⟩ : syracuseStep 13460165 = 2523781) B2523781
theorem B7971533 : Blo 1574485 7971533 := bstep (se 3 (by rfl) ⟨1494662, by rfl⟩ : syracuseStep 7971533 = 2989325) B2989325
theorem B5317325 : Blo 1574485 5317325 := bstep (se 3 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 5317325 = 1993997) B1993997
theorem B5317379 : Blo 1574485 5317379 := bstep (se 1 (by rfl) ⟨3988034, by rfl⟩ : syracuseStep 5317379 = 7976069) B7976069
theorem B13452101 : Blo 1574485 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B4260721 : Blo 1574485 4260721 := bstep (se 2 (by rfl) ⟨1597770, by rfl⟩ : syracuseStep 4260721 = 3195541) B3195541
theorem B2524051 : Blo 1574485 2524051 := bstep (se 1 (by rfl) ⟨1893038, by rfl⟩ : syracuseStep 2524051 = 3786077) B3786077
theorem B2524115 : Blo 1574485 2524115 := bstep (se 1 (by rfl) ⟨1893086, by rfl⟩ : syracuseStep 2524115 = 3786173) B3786173
theorem B1704931 : Blo 1574485 1704931 := bstep (se 1 (by rfl) ⟨1278698, by rfl⟩ : syracuseStep 1704931 = 2557397) B2557397
theorem B8971235 : Blo 1574485 8971235 := bstep (se 1 (by rfl) ⟨6728426, by rfl⟩ : syracuseStep 8971235 = 13456853) B13456853
theorem B5317649 : Blo 1574485 5317649 := bstep (se 2 (by rfl) ⟨1994118, by rfl⟩ : syracuseStep 5317649 = 3988237) B3988237
theorem B5047409 : Blo 1574485 5047409 := bstep (se 2 (by rfl) ⟨1892778, by rfl⟩ : syracuseStep 5047409 = 3785557) B3785557
theorem B1918243 : Blo 1574485 1918243 := bstep (se 1 (by rfl) ⟨1438682, by rfl⟩ : syracuseStep 1918243 = 2877365) B2877365
theorem B13460849 : Blo 1574485 13460849 := bstep (se 2 (by rfl) ⟨5047818, by rfl⟩ : syracuseStep 13460849 = 10095637) B10095637
theorem B2991505 : Blo 1574485 2991505 := bstep (se 2 (by rfl) ⟨1121814, by rfl⟩ : syracuseStep 2991505 = 2243629) B2243629
theorem B3237347 : Blo 1574485 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B15148529 : Blo 1574485 15148529 := bstep (se 2 (by rfl) ⟨5680698, by rfl⟩ : syracuseStep 15148529 = 11361397) B11361397
theorem B5318189 : Blo 1574485 5318189 := bstep (se 3 (by rfl) ⟨997160, by rfl⟩ : syracuseStep 5318189 = 1994321) B1994321
theorem B1574499 : Blo 1574485 1574499 := bstep (se 1 (by rfl) ⟨1180874, by rfl⟩ : syracuseStep 1574499 = 2361749) B2361749
theorem B5981795 : Blo 1574485 5981795 := bstep (se 1 (by rfl) ⟨4486346, by rfl⟩ : syracuseStep 5981795 = 8972693) B8972693
theorem B5318243 : Blo 1574485 5318243 := bstep (se 1 (by rfl) ⟨3988682, by rfl⟩ : syracuseStep 5318243 = 7977365) B7977365
theorem B5981809 : Blo 1574485 5981809 := bstep (se 2 (by rfl) ⟨2243178, by rfl⟩ : syracuseStep 5981809 = 4486357) B4486357
theorem B1574515 : Blo 1574485 1574515 := bstep (se 1 (by rfl) ⟨1180886, by rfl⟩ : syracuseStep 1574515 = 2361773) B2361773
theorem B1574531 : Blo 1574485 1574531 := bstep (se 1 (by rfl) ⟨1180898, by rfl⟩ : syracuseStep 1574531 = 2361797) B2361797
theorem B1574547 : Blo 1574485 1574547 := bstep (se 1 (by rfl) ⟨1180910, by rfl⟩ : syracuseStep 1574547 = 2361821) B2361821
theorem B1574563 : Blo 1574485 1574563 := bstep (se 1 (by rfl) ⟨1180922, by rfl⟩ : syracuseStep 1574563 = 2361845) B2361845
theorem B1574579 : Blo 1574485 1574579 := bstep (se 1 (by rfl) ⟨1180934, by rfl⟩ : syracuseStep 1574579 = 2361869) B2361869
theorem B1574595 : Blo 1574485 1574595 := bstep (se 1 (by rfl) ⟨1180946, by rfl⟩ : syracuseStep 1574595 = 2361893) B2361893
theorem B1574611 : Blo 1574485 1574611 := bstep (se 1 (by rfl) ⟨1180958, by rfl⟩ : syracuseStep 1574611 = 2361917) B2361917
theorem B1574627 : Blo 1574485 1574627 := bstep (se 1 (by rfl) ⟨1180970, by rfl⟩ : syracuseStep 1574627 = 2361941) B2361941
theorem B1574643 : Blo 1574485 1574643 := bstep (se 1 (by rfl) ⟨1180982, by rfl⟩ : syracuseStep 1574643 = 2361965) B2361965
theorem B1574659 : Blo 1574485 1574659 := bstep (se 1 (by rfl) ⟨1180994, by rfl⟩ : syracuseStep 1574659 = 2361989) B2361989
theorem B6391565 : Blo 1574485 6391565 := bstep (se 3 (by rfl) ⟨1198418, by rfl⟩ : syracuseStep 6391565 = 2396837) B2396837
theorem B1574675 : Blo 1574485 1574675 := bstep (se 1 (by rfl) ⟨1181006, by rfl⟩ : syracuseStep 1574675 = 2362013) B2362013
theorem B1574691 : Blo 1574485 1574691 := bstep (se 1 (by rfl) ⟨1181018, by rfl⟩ : syracuseStep 1574691 = 2362037) B2362037
theorem B2991907 : Blo 1574485 2991907 := bstep (se 1 (by rfl) ⟨2243930, by rfl⟩ : syracuseStep 2991907 = 4487861) B4487861
theorem B1574707 : Blo 1574485 1574707 := bstep (se 1 (by rfl) ⟨1181030, by rfl⟩ : syracuseStep 1574707 = 2362061) B2362061
theorem B1574723 : Blo 1574485 1574723 := bstep (se 1 (by rfl) ⟨1181042, by rfl⟩ : syracuseStep 1574723 = 2362085) B2362085
theorem B2991953 : Blo 1574485 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B1574739 : Blo 1574485 1574739 := bstep (se 1 (by rfl) ⟨1181054, by rfl⟩ : syracuseStep 1574739 = 2362109) B2362109
theorem B1574755 : Blo 1574485 1574755 := bstep (se 1 (by rfl) ⟨1181066, by rfl⟩ : syracuseStep 1574755 = 2362133) B2362133
theorem B5318513 : Blo 1574485 5318513 := bstep (se 2 (by rfl) ⟨1994442, by rfl⟩ : syracuseStep 5318513 = 3988885) B3988885
theorem B1574771 : Blo 1574485 1574771 := bstep (se 1 (by rfl) ⟨1181078, by rfl⟩ : syracuseStep 1574771 = 2362157) B2362157
theorem B1574787 : Blo 1574485 1574787 := bstep (se 1 (by rfl) ⟨1181090, by rfl⟩ : syracuseStep 1574787 = 2362181) B2362181
theorem B1771411 : Blo 1574485 1771411 := bstep (se 1 (by rfl) ⟨1328558, by rfl⟩ : syracuseStep 1771411 = 2657117) B2657117
theorem B1574803 : Blo 1574485 1574803 := bstep (se 1 (by rfl) ⟨1181102, by rfl⟩ : syracuseStep 1574803 = 2362205) B2362205
theorem B2525089 : Blo 1574485 2525089 := bstep (se 2 (by rfl) ⟨946908, by rfl⟩ : syracuseStep 2525089 = 1893817) B1893817
theorem B1574819 : Blo 1574485 1574819 := bstep (se 1 (by rfl) ⟨1181114, by rfl⟩ : syracuseStep 1574819 = 2362229) B2362229
theorem B1574835 : Blo 1574485 1574835 := bstep (se 1 (by rfl) ⟨1181126, by rfl⟩ : syracuseStep 1574835 = 2362253) B2362253
theorem B1574851 : Blo 1574485 1574851 := bstep (se 1 (by rfl) ⟨1181138, by rfl⟩ : syracuseStep 1574851 = 2362277) B2362277
theorem B1574867 : Blo 1574485 1574867 := bstep (se 1 (by rfl) ⟨1181150, by rfl⟩ : syracuseStep 1574867 = 2362301) B2362301
theorem B1574883 : Blo 1574485 1574883 := bstep (se 1 (by rfl) ⟨1181162, by rfl⟩ : syracuseStep 1574883 = 2362325) B2362325
theorem B1574899 : Blo 1574485 1574899 := bstep (se 1 (by rfl) ⟨1181174, by rfl⟩ : syracuseStep 1574899 = 2362349) B2362349
theorem B1574915 : Blo 1574485 1574915 := bstep (se 1 (by rfl) ⟨1181186, by rfl⟩ : syracuseStep 1574915 = 2362373) B2362373
theorem B2557955 : Blo 1574485 2557955 := bstep (se 1 (by rfl) ⟨1918466, by rfl⟩ : syracuseStep 2557955 = 3836933) B3836933
theorem B1574931 : Blo 1574485 1574931 := bstep (se 1 (by rfl) ⟨1181198, by rfl⟩ : syracuseStep 1574931 = 2362397) B2362397
theorem B1771555 : Blo 1574485 1771555 := bstep (se 1 (by rfl) ⟨1328666, by rfl⟩ : syracuseStep 1771555 = 2657333) B2657333
theorem B1574947 : Blo 1574485 1574947 := bstep (se 1 (by rfl) ⟨1181210, by rfl⟩ : syracuseStep 1574947 = 2362421) B2362421
theorem B3786787 : Blo 1574485 3786787 := bstep (se 1 (by rfl) ⟨2840090, by rfl⟩ : syracuseStep 3786787 = 5680181) B5680181
theorem B1574963 : Blo 1574485 1574963 := bstep (se 1 (by rfl) ⟨1181222, by rfl⟩ : syracuseStep 1574963 = 2362445) B2362445
theorem B1574979 : Blo 1574485 1574979 := bstep (se 1 (by rfl) ⟨1181234, by rfl⟩ : syracuseStep 1574979 = 2362469) B2362469
theorem B1574995 : Blo 1574485 1574995 := bstep (se 1 (by rfl) ⟨1181246, by rfl⟩ : syracuseStep 1574995 = 2362493) B2362493
theorem B1575011 : Blo 1574485 1575011 := bstep (se 1 (by rfl) ⟨1181258, by rfl⟩ : syracuseStep 1575011 = 2362517) B2362517
theorem B2992241 : Blo 1574485 2992241 := bstep (se 2 (by rfl) ⟨1122090, by rfl⟩ : syracuseStep 2992241 = 2244181) B2244181
theorem B1575027 : Blo 1574485 1575027 := bstep (se 1 (by rfl) ⟨1181270, by rfl⟩ : syracuseStep 1575027 = 2362541) B2362541
theorem B1575043 : Blo 1574485 1575043 := bstep (se 1 (by rfl) ⟨1181282, by rfl⟩ : syracuseStep 1575043 = 2362565) B2362565
theorem B1575059 : Blo 1574485 1575059 := bstep (se 1 (by rfl) ⟨1181294, by rfl⟩ : syracuseStep 1575059 = 2362589) B2362589
theorem B1575075 : Blo 1574485 1575075 := bstep (se 1 (by rfl) ⟨1181306, by rfl⟩ : syracuseStep 1575075 = 2362613) B2362613
theorem B1771699 : Blo 1574485 1771699 := bstep (se 1 (by rfl) ⟨1328774, by rfl⟩ : syracuseStep 1771699 = 2657549) B2657549
theorem B1575091 : Blo 1574485 1575091 := bstep (se 1 (by rfl) ⟨1181318, by rfl⟩ : syracuseStep 1575091 = 2362637) B2362637
theorem B1575107 : Blo 1574485 1575107 := bstep (se 1 (by rfl) ⟨1181330, by rfl⟩ : syracuseStep 1575107 = 2362661) B2362661
theorem B1575123 : Blo 1574485 1575123 := bstep (se 1 (by rfl) ⟨1181342, by rfl⟩ : syracuseStep 1575123 = 2362685) B2362685
theorem B21547235 : Blo 1574485 21547235 := bstep (se 1 (by rfl) ⟨16160426, by rfl⟩ : syracuseStep 21547235 = 32320853) B32320853
theorem B1575139 : Blo 1574485 1575139 := bstep (se 1 (by rfl) ⟨1181354, by rfl⟩ : syracuseStep 1575139 = 2362709) B2362709
theorem B3786979 : Blo 1574485 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B20187377 : Blo 1574485 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B1575155 : Blo 1574485 1575155 := bstep (se 1 (by rfl) ⟨1181366, by rfl⟩ : syracuseStep 1575155 = 2362733) B2362733
theorem B1575171 : Blo 1574485 1575171 := bstep (se 1 (by rfl) ⟨1181378, by rfl⟩ : syracuseStep 1575171 = 2362757) B2362757
theorem B1575187 : Blo 1574485 1575187 := bstep (se 1 (by rfl) ⟨1181390, by rfl⟩ : syracuseStep 1575187 = 2362781) B2362781
theorem B1575203 : Blo 1574485 1575203 := bstep (se 1 (by rfl) ⟨1181402, by rfl⟩ : syracuseStep 1575203 = 2362805) B2362805
theorem B1575219 : Blo 1574485 1575219 := bstep (se 1 (by rfl) ⟨1181414, by rfl⟩ : syracuseStep 1575219 = 2362829) B2362829
theorem B1771843 : Blo 1574485 1771843 := bstep (se 1 (by rfl) ⟨1328882, by rfl⟩ : syracuseStep 1771843 = 2657765) B2657765
theorem B1575235 : Blo 1574485 1575235 := bstep (se 1 (by rfl) ⟨1181426, by rfl⟩ : syracuseStep 1575235 = 2362853) B2362853
theorem B7571789 : Blo 1574485 7571789 := bstep (se 3 (by rfl) ⟨1419710, by rfl⟩ : syracuseStep 7571789 = 2839421) B2839421
theorem B1575251 : Blo 1574485 1575251 := bstep (se 1 (by rfl) ⟨1181438, by rfl⟩ : syracuseStep 1575251 = 2362877) B2362877
theorem B1575267 : Blo 1574485 1575267 := bstep (se 1 (by rfl) ⟨1181450, by rfl⟩ : syracuseStep 1575267 = 2362901) B2362901
theorem B1575283 : Blo 1574485 1575283 := bstep (se 1 (by rfl) ⟨1181462, by rfl⟩ : syracuseStep 1575283 = 2362925) B2362925
theorem B2361731 : Blo 1574485 2361731 := bstep (se 1 (by rfl) ⟨1771298, by rfl⟩ : syracuseStep 2361731 = 3542597) B3542597
theorem B1575299 : Blo 1574485 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B5319053 : Blo 1574485 5319053 := bstep (se 3 (by rfl) ⟨997322, by rfl⟩ : syracuseStep 5319053 = 1994645) B1994645
theorem B1575315 : Blo 1574485 1575315 := bstep (se 1 (by rfl) ⟨1181486, by rfl⟩ : syracuseStep 1575315 = 2362973) B2362973
theorem B2361761 : Blo 1574485 2361761 := bstep (se 2 (by rfl) ⟨885660, by rfl⟩ : syracuseStep 2361761 = 1771321) B1771321
theorem B1575331 : Blo 1574485 1575331 := bstep (se 1 (by rfl) ⟨1181498, by rfl⟩ : syracuseStep 1575331 = 2362997) B2362997
theorem B2361779 : Blo 1574485 2361779 := bstep (se 1 (by rfl) ⟨1771334, by rfl⟩ : syracuseStep 2361779 = 3542669) B3542669
theorem B1575347 : Blo 1574485 1575347 := bstep (se 1 (by rfl) ⟨1181510, by rfl⟩ : syracuseStep 1575347 = 2363021) B2363021
theorem B1575363 : Blo 1574485 1575363 := bstep (se 1 (by rfl) ⟨1181522, by rfl⟩ : syracuseStep 1575363 = 2363045) B2363045
theorem B26913221 : Blo 1574485 26913221 := bstep (se 4 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 26913221 = 5046229) B5046229
theorem B5319107 : Blo 1574485 5319107 := bstep (se 1 (by rfl) ⟨3989330, by rfl⟩ : syracuseStep 5319107 = 7978661) B7978661
theorem B2361809 : Blo 1574485 2361809 := bstep (se 2 (by rfl) ⟨885678, by rfl⟩ : syracuseStep 2361809 = 1771357) B1771357
theorem B1771987 : Blo 1574485 1771987 := bstep (se 1 (by rfl) ⟨1328990, by rfl⟩ : syracuseStep 1771987 = 2657981) B2657981
theorem B1575379 : Blo 1574485 1575379 := bstep (se 1 (by rfl) ⟨1181534, by rfl⟩ : syracuseStep 1575379 = 2363069) B2363069
theorem B2361827 : Blo 1574485 2361827 := bstep (se 1 (by rfl) ⟨1771370, by rfl⟩ : syracuseStep 2361827 = 3542741) B3542741
theorem B1993187 : Blo 1574485 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1575395 : Blo 1574485 1575395 := bstep (se 1 (by rfl) ⟨1181546, by rfl⟩ : syracuseStep 1575395 = 2363093) B2363093
theorem B16394723 : Blo 1574485 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B3787249 : Blo 1574485 3787249 := bstep (se 2 (by rfl) ⟨1420218, by rfl⟩ : syracuseStep 3787249 = 2840437) B2840437
theorem B1575411 : Blo 1574485 1575411 := bstep (se 1 (by rfl) ⟨1181558, by rfl⟩ : syracuseStep 1575411 = 2363117) B2363117
theorem B2361857 : Blo 1574485 2361857 := bstep (se 2 (by rfl) ⟨885696, by rfl⟩ : syracuseStep 2361857 = 1771393) B1771393
theorem B1575427 : Blo 1574485 1575427 := bstep (se 1 (by rfl) ⟨1181570, by rfl⟩ : syracuseStep 1575427 = 2363141) B2363141
theorem B2361875 : Blo 1574485 2361875 := bstep (se 1 (by rfl) ⟨1771406, by rfl⟩ : syracuseStep 2361875 = 3542813) B3542813
theorem B1575443 : Blo 1574485 1575443 := bstep (se 1 (by rfl) ⟨1181582, by rfl⟩ : syracuseStep 1575443 = 2363165) B2363165
theorem B1575459 : Blo 1574485 1575459 := bstep (se 1 (by rfl) ⟨1181594, by rfl⟩ : syracuseStep 1575459 = 2363189) B2363189
theorem B2361905 : Blo 1574485 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B1575475 : Blo 1574485 1575475 := bstep (se 1 (by rfl) ⟨1181606, by rfl⟩ : syracuseStep 1575475 = 2363213) B2363213
theorem B2361923 : Blo 1574485 2361923 := bstep (se 1 (by rfl) ⟨1771442, by rfl⟩ : syracuseStep 2361923 = 3542885) B3542885
theorem B1575491 : Blo 1574485 1575491 := bstep (se 1 (by rfl) ⟨1181618, by rfl⟩ : syracuseStep 1575491 = 2363237) B2363237
theorem B1575507 : Blo 1574485 1575507 := bstep (se 1 (by rfl) ⟨1181630, by rfl⟩ : syracuseStep 1575507 = 2363261) B2363261
theorem B2361953 : Blo 1574485 2361953 := bstep (se 2 (by rfl) ⟨885732, by rfl⟩ : syracuseStep 2361953 = 1771465) B1771465
theorem B6728291 : Blo 1574485 6728291 := bstep (se 1 (by rfl) ⟨5046218, by rfl⟩ : syracuseStep 6728291 = 10092437) B10092437
theorem B1772131 : Blo 1574485 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B1575523 : Blo 1574485 1575523 := bstep (se 1 (by rfl) ⟨1181642, by rfl⟩ : syracuseStep 1575523 = 2363285) B2363285
theorem B2878051 : Blo 1574485 2878051 := bstep (se 1 (by rfl) ⟨2158538, by rfl⟩ : syracuseStep 2878051 = 4317077) B4317077
theorem B2361971 : Blo 1574485 2361971 := bstep (se 1 (by rfl) ⟨1771478, by rfl⟩ : syracuseStep 2361971 = 3542957) B3542957
theorem B1575539 : Blo 1574485 1575539 := bstep (se 1 (by rfl) ⟨1181654, by rfl⟩ : syracuseStep 1575539 = 2363309) B2363309
theorem B1682051 : Blo 1574485 1682051 := bstep (se 1 (by rfl) ⟨1261538, by rfl⟩ : syracuseStep 1682051 = 2523077) B2523077
theorem B1575555 : Blo 1574485 1575555 := bstep (se 1 (by rfl) ⟨1181666, by rfl⟩ : syracuseStep 1575555 = 2363333) B2363333
theorem B2362001 : Blo 1574485 2362001 := bstep (se 2 (by rfl) ⟨885750, by rfl⟩ : syracuseStep 2362001 = 1771501) B1771501
theorem B1575571 : Blo 1574485 1575571 := bstep (se 1 (by rfl) ⟨1181678, by rfl⟩ : syracuseStep 1575571 = 2363357) B2363357
theorem B2362019 : Blo 1574485 2362019 := bstep (se 1 (by rfl) ⟨1771514, by rfl⟩ : syracuseStep 2362019 = 3543029) B3543029
theorem B1575587 : Blo 1574485 1575587 := bstep (se 1 (by rfl) ⟨1181690, by rfl⟩ : syracuseStep 1575587 = 2363381) B2363381
theorem B1575603 : Blo 1574485 1575603 := bstep (se 1 (by rfl) ⟨1181702, by rfl⟩ : syracuseStep 1575603 = 2363405) B2363405
theorem B2362049 : Blo 1574485 2362049 := bstep (se 2 (by rfl) ⟨885768, by rfl⟩ : syracuseStep 2362049 = 1771537) B1771537
theorem B1575619 : Blo 1574485 1575619 := bstep (se 1 (by rfl) ⟨1181714, by rfl⟩ : syracuseStep 1575619 = 2363429) B2363429
theorem B5319377 : Blo 1574485 5319377 := bstep (se 2 (by rfl) ⟨1994766, by rfl⟩ : syracuseStep 5319377 = 3989533) B3989533
theorem B2362067 : Blo 1574485 2362067 := bstep (se 1 (by rfl) ⟨1771550, by rfl⟩ : syracuseStep 2362067 = 3543101) B3543101
theorem B1575635 : Blo 1574485 1575635 := bstep (se 1 (by rfl) ⟨1181726, by rfl⟩ : syracuseStep 1575635 = 2363453) B2363453
theorem B1575651 : Blo 1574485 1575651 := bstep (se 1 (by rfl) ⟨1181738, by rfl⟩ : syracuseStep 1575651 = 2363477) B2363477
theorem B2657009 : Blo 1574485 2657009 := bstep (se 2 (by rfl) ⟨996378, by rfl⟩ : syracuseStep 2657009 = 1992757) B1992757
theorem B2362097 : Blo 1574485 2362097 := bstep (se 2 (by rfl) ⟨885786, by rfl⟩ : syracuseStep 2362097 = 1771573) B1771573
theorem B1772275 : Blo 1574485 1772275 := bstep (se 1 (by rfl) ⟨1329206, by rfl⟩ : syracuseStep 1772275 = 2658413) B2658413
theorem B1575667 : Blo 1574485 1575667 := bstep (se 1 (by rfl) ⟨1181750, by rfl⟩ : syracuseStep 1575667 = 2363501) B2363501
theorem B2362115 : Blo 1574485 2362115 := bstep (se 1 (by rfl) ⟨1771586, by rfl⟩ : syracuseStep 2362115 = 3543173) B3543173
theorem B1575683 : Blo 1574485 1575683 := bstep (se 1 (by rfl) ⟨1181762, by rfl⟩ : syracuseStep 1575683 = 2363525) B2363525
theorem B1575699 : Blo 1574485 1575699 := bstep (se 1 (by rfl) ⟨1181774, by rfl⟩ : syracuseStep 1575699 = 2363549) B2363549
theorem B2362145 : Blo 1574485 2362145 := bstep (se 2 (by rfl) ⟨885804, by rfl⟩ : syracuseStep 2362145 = 1771609) B1771609
theorem B1575715 : Blo 1574485 1575715 := bstep (se 1 (by rfl) ⟨1181786, by rfl⟩ : syracuseStep 1575715 = 2363573) B2363573
theorem B1796899 : Blo 1574485 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B2362163 : Blo 1574485 2362163 := bstep (se 1 (by rfl) ⟨1771622, by rfl⟩ : syracuseStep 2362163 = 3543245) B3543245
theorem B1575731 : Blo 1574485 1575731 := bstep (se 1 (by rfl) ⟨1181798, by rfl⟩ : syracuseStep 1575731 = 2363597) B2363597
theorem B1575747 : Blo 1574485 1575747 := bstep (se 1 (by rfl) ⟨1181810, by rfl⟩ : syracuseStep 1575747 = 2363621) B2363621
theorem B8973125 : Blo 1574485 8973125 := bstep (se 4 (by rfl) ⟨841230, by rfl⟩ : syracuseStep 8973125 = 1682461) B1682461
theorem B2362193 : Blo 1574485 2362193 := bstep (se 2 (by rfl) ⟨885822, by rfl⟩ : syracuseStep 2362193 = 1771645) B1771645
theorem B1575763 : Blo 1574485 1575763 := bstep (se 1 (by rfl) ⟨1181822, by rfl⟩ : syracuseStep 1575763 = 2363645) B2363645
theorem B2362211 : Blo 1574485 2362211 := bstep (se 1 (by rfl) ⟨1771658, by rfl⟩ : syracuseStep 2362211 = 3543317) B3543317
theorem B1575779 : Blo 1574485 1575779 := bstep (se 1 (by rfl) ⟨1181834, by rfl⟩ : syracuseStep 1575779 = 2363669) B2363669
theorem B2657137 : Blo 1574485 2657137 := bstep (se 2 (by rfl) ⟨996426, by rfl⟩ : syracuseStep 2657137 = 1992853) B1992853
theorem B1575795 : Blo 1574485 1575795 := bstep (se 1 (by rfl) ⟨1181846, by rfl⟩ : syracuseStep 1575795 = 2363693) B2363693
theorem B2362241 : Blo 1574485 2362241 := bstep (se 2 (by rfl) ⟨885840, by rfl⟩ : syracuseStep 2362241 = 1771681) B1771681
theorem B1772419 : Blo 1574485 1772419 := bstep (se 1 (by rfl) ⟨1329314, by rfl⟩ : syracuseStep 1772419 = 2658629) B2658629
theorem B1575811 : Blo 1574485 1575811 := bstep (se 1 (by rfl) ⟨1181858, by rfl⟩ : syracuseStep 1575811 = 2363717) B2363717
theorem B5049229 : Blo 1574485 5049229 := bstep (se 3 (by rfl) ⟨946730, by rfl⟩ : syracuseStep 5049229 = 1893461) B1893461
theorem B2657171 : Blo 1574485 2657171 := bstep (se 1 (by rfl) ⟨1992878, by rfl⟩ : syracuseStep 2657171 = 3985757) B3985757
theorem B2362259 : Blo 1574485 2362259 := bstep (se 1 (by rfl) ⟨1771694, by rfl⟩ : syracuseStep 2362259 = 3543389) B3543389
theorem B1575827 : Blo 1574485 1575827 := bstep (se 1 (by rfl) ⟨1181870, by rfl⟩ : syracuseStep 1575827 = 2363741) B2363741
theorem B1575843 : Blo 1574485 1575843 := bstep (se 1 (by rfl) ⟨1181882, by rfl⟩ : syracuseStep 1575843 = 2363765) B2363765
theorem B2362289 : Blo 1574485 2362289 := bstep (se 2 (by rfl) ⟨885858, by rfl⟩ : syracuseStep 2362289 = 1771717) B1771717
theorem B1575859 : Blo 1574485 1575859 := bstep (se 1 (by rfl) ⟨1181894, by rfl⟩ : syracuseStep 1575859 = 2363789) B2363789
theorem B2362307 : Blo 1574485 2362307 := bstep (se 1 (by rfl) ⟨1771730, by rfl⟩ : syracuseStep 2362307 = 3543461) B3543461
theorem B1575875 : Blo 1574485 1575875 := bstep (se 1 (by rfl) ⟨1181906, by rfl⟩ : syracuseStep 1575875 = 2363813) B2363813
theorem B1575891 : Blo 1574485 1575891 := bstep (se 1 (by rfl) ⟨1181918, by rfl⟩ : syracuseStep 1575891 = 2363837) B2363837
theorem B2362337 : Blo 1574485 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B43109347 : Blo 1574485 43109347 := bstep (se 1 (by rfl) ⟨32332010, by rfl⟩ : syracuseStep 43109347 = 64664021) B64664021
theorem B10095587 : Blo 1574485 10095587 := bstep (se 1 (by rfl) ⟨7571690, by rfl⟩ : syracuseStep 10095587 = 15143381) B15143381
theorem B1575907 : Blo 1574485 1575907 := bstep (se 1 (by rfl) ⟨1181930, by rfl⟩ : syracuseStep 1575907 = 2363861) B2363861
theorem B2362355 : Blo 1574485 2362355 := bstep (se 1 (by rfl) ⟨1771766, by rfl⟩ : syracuseStep 2362355 = 3543533) B3543533
theorem B1575923 : Blo 1574485 1575923 := bstep (se 1 (by rfl) ⟨1181942, by rfl⟩ : syracuseStep 1575923 = 2363885) B2363885
theorem B1575939 : Blo 1574485 1575939 := bstep (se 1 (by rfl) ⟨1181954, by rfl⟩ : syracuseStep 1575939 = 2363909) B2363909
theorem B2362385 : Blo 1574485 2362385 := bstep (se 2 (by rfl) ⟨885894, by rfl⟩ : syracuseStep 2362385 = 1771789) B1771789
theorem B2657299 : Blo 1574485 2657299 := bstep (se 1 (by rfl) ⟨1992974, by rfl⟩ : syracuseStep 2657299 = 3985949) B3985949
theorem B1772563 : Blo 1574485 1772563 := bstep (se 1 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 1772563 = 2658845) B2658845
theorem B1575955 : Blo 1574485 1575955 := bstep (se 1 (by rfl) ⟨1181966, by rfl⟩ : syracuseStep 1575955 = 2363933) B2363933
theorem B2558995 : Blo 1574485 2558995 := bstep (se 1 (by rfl) ⟨1919246, by rfl⟩ : syracuseStep 2558995 = 3838493) B3838493
theorem B2837539 : Blo 1574485 2837539 := bstep (se 1 (by rfl) ⟨2128154, by rfl⟩ : syracuseStep 2837539 = 4256309) B4256309
theorem B2362403 : Blo 1574485 2362403 := bstep (se 1 (by rfl) ⟨1771802, by rfl⟩ : syracuseStep 2362403 = 3543605) B3543605
theorem B5983267 : Blo 1574485 5983267 := bstep (se 1 (by rfl) ⟨4487450, by rfl⟩ : syracuseStep 5983267 = 8974901) B8974901
theorem B1575971 : Blo 1574485 1575971 := bstep (se 1 (by rfl) ⟨1181978, by rfl⟩ : syracuseStep 1575971 = 2363957) B2363957
theorem B3787825 : Blo 1574485 3787825 := bstep (se 2 (by rfl) ⟨1420434, by rfl⟩ : syracuseStep 3787825 = 2840869) B2840869
theorem B1575987 : Blo 1574485 1575987 := bstep (se 1 (by rfl) ⟨1181990, by rfl⟩ : syracuseStep 1575987 = 2363981) B2363981
theorem B17943605 : Blo 1574485 17943605 := bstep (se 5 (by rfl) ⟨841106, by rfl⟩ : syracuseStep 17943605 = 1682213) B1682213
theorem B2362433 : Blo 1574485 2362433 := bstep (se 2 (by rfl) ⟨885912, by rfl⟩ : syracuseStep 2362433 = 1771825) B1771825
theorem B1576003 : Blo 1574485 1576003 := bstep (se 1 (by rfl) ⟨1182002, by rfl⟩ : syracuseStep 1576003 = 2364005) B2364005
theorem B8514629 : Blo 1574485 8514629 := bstep (se 4 (by rfl) ⟨798246, by rfl⟩ : syracuseStep 8514629 = 1596493) B1596493
theorem B2362451 : Blo 1574485 2362451 := bstep (se 1 (by rfl) ⟨1771838, by rfl⟩ : syracuseStep 2362451 = 3543677) B3543677
theorem B1576019 : Blo 1574485 1576019 := bstep (se 1 (by rfl) ⟨1182014, by rfl⟩ : syracuseStep 1576019 = 2364029) B2364029
theorem B1576035 : Blo 1574485 1576035 := bstep (se 1 (by rfl) ⟨1182026, by rfl⟩ : syracuseStep 1576035 = 2364053) B2364053
theorem B2362481 : Blo 1574485 2362481 := bstep (se 2 (by rfl) ⟨885930, by rfl⟩ : syracuseStep 2362481 = 1771861) B1771861
theorem B18197617 : Blo 1574485 18197617 := bstep (se 2 (by rfl) ⟨6824106, by rfl⟩ : syracuseStep 18197617 = 13648213) B13648213
theorem B1576051 : Blo 1574485 1576051 := bstep (se 1 (by rfl) ⟨1182038, by rfl⟩ : syracuseStep 1576051 = 2364077) B2364077
theorem B2362499 : Blo 1574485 2362499 := bstep (se 1 (by rfl) ⟨1771874, by rfl⟩ : syracuseStep 2362499 = 3543749) B3543749
theorem B1576067 : Blo 1574485 1576067 := bstep (se 1 (by rfl) ⟨1182050, by rfl⟩ : syracuseStep 1576067 = 2364101) B2364101
theorem B1576083 : Blo 1574485 1576083 := bstep (se 1 (by rfl) ⟨1182062, by rfl⟩ : syracuseStep 1576083 = 2364125) B2364125
theorem B2657441 : Blo 1574485 2657441 := bstep (se 2 (by rfl) ⟨996540, by rfl⟩ : syracuseStep 2657441 = 1993081) B1993081
theorem B2362529 : Blo 1574485 2362529 := bstep (se 2 (by rfl) ⟨885948, by rfl⟩ : syracuseStep 2362529 = 1771897) B1771897
theorem B1993891 : Blo 1574485 1993891 := bstep (se 1 (by rfl) ⟨1495418, by rfl⟩ : syracuseStep 1993891 = 2990837) B2990837
theorem B1772707 : Blo 1574485 1772707 := bstep (se 1 (by rfl) ⟨1329530, by rfl⟩ : syracuseStep 1772707 = 2659061) B2659061
theorem B1576099 : Blo 1574485 1576099 := bstep (se 1 (by rfl) ⟨1182074, by rfl⟩ : syracuseStep 1576099 = 2364149) B2364149
theorem B2362547 : Blo 1574485 2362547 := bstep (se 1 (by rfl) ⟨1771910, by rfl⟩ : syracuseStep 2362547 = 3543821) B3543821
theorem B1576115 : Blo 1574485 1576115 := bstep (se 1 (by rfl) ⟨1182086, by rfl⟩ : syracuseStep 1576115 = 2364173) B2364173
theorem B1576131 : Blo 1574485 1576131 := bstep (se 1 (by rfl) ⟨1182098, by rfl⟩ : syracuseStep 1576131 = 2364197) B2364197
theorem B2837713 : Blo 1574485 2837713 := bstep (se 2 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 2837713 = 2128285) B2128285
theorem B2362577 : Blo 1574485 2362577 := bstep (se 2 (by rfl) ⟨885966, by rfl⟩ : syracuseStep 2362577 = 1771933) B1771933
theorem B1576147 : Blo 1574485 1576147 := bstep (se 1 (by rfl) ⟨1182110, by rfl⟩ : syracuseStep 1576147 = 2364221) B2364221
theorem B2362595 : Blo 1574485 2362595 := bstep (se 1 (by rfl) ⟨1771946, by rfl⟩ : syracuseStep 2362595 = 3543893) B3543893
theorem B1576163 : Blo 1574485 1576163 := bstep (se 1 (by rfl) ⟨1182122, by rfl⟩ : syracuseStep 1576163 = 2364245) B2364245
theorem B11349233 : Blo 1574485 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B1576179 : Blo 1574485 1576179 := bstep (se 1 (by rfl) ⟨1182134, by rfl⟩ : syracuseStep 1576179 = 2364269) B2364269
theorem B5319917 : Blo 1574485 5319917 := bstep (se 3 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 5319917 = 1994969) B1994969
theorem B2362625 : Blo 1574485 2362625 := bstep (se 2 (by rfl) ⟨885984, by rfl⟩ : syracuseStep 2362625 = 1771969) B1771969
theorem B1993987 : Blo 1574485 1993987 := bstep (se 1 (by rfl) ⟨1495490, by rfl⟩ : syracuseStep 1993987 = 2990981) B2990981
theorem B1576195 : Blo 1574485 1576195 := bstep (se 1 (by rfl) ⟨1182146, by rfl⟩ : syracuseStep 1576195 = 2364293) B2364293
theorem B8514821 : Blo 1574485 8514821 := bstep (se 4 (by rfl) ⟨798264, by rfl⟩ : syracuseStep 8514821 = 1596529) B1596529
theorem B2362643 : Blo 1574485 2362643 := bstep (se 1 (by rfl) ⟨1771982, by rfl⟩ : syracuseStep 2362643 = 3543965) B3543965
theorem B1576211 : Blo 1574485 1576211 := bstep (se 1 (by rfl) ⟨1182158, by rfl⟩ : syracuseStep 1576211 = 2364317) B2364317
theorem B2657569 : Blo 1574485 2657569 := bstep (se 2 (by rfl) ⟨996588, by rfl⟩ : syracuseStep 2657569 = 1993177) B1993177
theorem B1576227 : Blo 1574485 1576227 := bstep (se 1 (by rfl) ⟨1182170, by rfl⟩ : syracuseStep 1576227 = 2364341) B2364341
theorem B5319971 : Blo 1574485 5319971 := bstep (se 1 (by rfl) ⟨3989978, by rfl⟩ : syracuseStep 5319971 = 7979957) B7979957
theorem B2362673 : Blo 1574485 2362673 := bstep (se 2 (by rfl) ⟨886002, by rfl⟩ : syracuseStep 2362673 = 1772005) B1772005
theorem B1772851 : Blo 1574485 1772851 := bstep (se 1 (by rfl) ⟨1329638, by rfl⟩ : syracuseStep 1772851 = 2659277) B2659277
theorem B1576243 : Blo 1574485 1576243 := bstep (se 1 (by rfl) ⟨1182182, by rfl⟩ : syracuseStep 1576243 = 2364365) B2364365
theorem B2657603 : Blo 1574485 2657603 := bstep (se 1 (by rfl) ⟨1993202, by rfl⟩ : syracuseStep 2657603 = 3986405) B3986405
theorem B2362691 : Blo 1574485 2362691 := bstep (se 1 (by rfl) ⟨1772018, by rfl⟩ : syracuseStep 2362691 = 3544037) B3544037
theorem B1576259 : Blo 1574485 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B1576275 : Blo 1574485 1576275 := bstep (se 1 (by rfl) ⟨1182206, by rfl⟩ : syracuseStep 1576275 = 2364413) B2364413
theorem B2362721 : Blo 1574485 2362721 := bstep (se 2 (by rfl) ⟨886020, by rfl⟩ : syracuseStep 2362721 = 1772041) B1772041
theorem B1576291 : Blo 1574485 1576291 := bstep (se 1 (by rfl) ⟨1182218, by rfl⟩ : syracuseStep 1576291 = 2364437) B2364437
theorem B2362739 : Blo 1574485 2362739 := bstep (se 1 (by rfl) ⟨1772054, by rfl⟩ : syracuseStep 2362739 = 3544109) B3544109
theorem B1682803 : Blo 1574485 1682803 := bstep (se 1 (by rfl) ⟨1262102, by rfl⟩ : syracuseStep 1682803 = 2524205) B2524205
theorem B1576307 : Blo 1574485 1576307 := bstep (se 1 (by rfl) ⟨1182230, by rfl⟩ : syracuseStep 1576307 = 2364461) B2364461
theorem B1576323 : Blo 1574485 1576323 := bstep (se 1 (by rfl) ⟨1182242, by rfl⟩ : syracuseStep 1576323 = 2364485) B2364485
theorem B2362769 : Blo 1574485 2362769 := bstep (se 2 (by rfl) ⟨886038, by rfl⟩ : syracuseStep 2362769 = 1772077) B1772077
theorem B1576339 : Blo 1574485 1576339 := bstep (se 1 (by rfl) ⟨1182254, by rfl⟩ : syracuseStep 1576339 = 2364509) B2364509
theorem B2362787 : Blo 1574485 2362787 := bstep (se 1 (by rfl) ⟨1772090, by rfl⟩ : syracuseStep 2362787 = 3544181) B3544181
theorem B1576355 : Blo 1574485 1576355 := bstep (se 1 (by rfl) ⟨1182266, by rfl⟩ : syracuseStep 1576355 = 2364533) B2364533
theorem B1576371 : Blo 1574485 1576371 := bstep (se 1 (by rfl) ⟨1182278, by rfl⟩ : syracuseStep 1576371 = 2364557) B2364557
theorem B2362817 : Blo 1574485 2362817 := bstep (se 2 (by rfl) ⟨886056, by rfl⟩ : syracuseStep 2362817 = 1772113) B1772113
theorem B2657731 : Blo 1574485 2657731 := bstep (se 1 (by rfl) ⟨1993298, by rfl⟩ : syracuseStep 2657731 = 3986597) B3986597
theorem B1772995 : Blo 1574485 1772995 := bstep (se 1 (by rfl) ⟨1329746, by rfl⟩ : syracuseStep 1772995 = 2659493) B2659493
theorem B1576387 : Blo 1574485 1576387 := bstep (se 1 (by rfl) ⟨1182290, by rfl⟩ : syracuseStep 1576387 = 2364581) B2364581
theorem B2362835 : Blo 1574485 2362835 := bstep (se 1 (by rfl) ⟨1772126, by rfl⟩ : syracuseStep 2362835 = 3544253) B3544253
theorem B1576403 : Blo 1574485 1576403 := bstep (se 1 (by rfl) ⟨1182302, by rfl⟩ : syracuseStep 1576403 = 2364605) B2364605
theorem B1576419 : Blo 1574485 1576419 := bstep (se 1 (by rfl) ⟨1182314, by rfl⟩ : syracuseStep 1576419 = 2364629) B2364629
theorem B2362865 : Blo 1574485 2362865 := bstep (se 2 (by rfl) ⟨886074, by rfl⟩ : syracuseStep 2362865 = 1772149) B1772149
theorem B1576435 : Blo 1574485 1576435 := bstep (se 1 (by rfl) ⟨1182326, by rfl⟩ : syracuseStep 1576435 = 2364653) B2364653
theorem B2362883 : Blo 1574485 2362883 := bstep (se 1 (by rfl) ⟨1772162, by rfl⟩ : syracuseStep 2362883 = 3544325) B3544325
theorem B1576451 : Blo 1574485 1576451 := bstep (se 1 (by rfl) ⟨1182338, by rfl⟩ : syracuseStep 1576451 = 2364677) B2364677
theorem B1576467 : Blo 1574485 1576467 := bstep (se 1 (by rfl) ⟨1182350, by rfl⟩ : syracuseStep 1576467 = 2364701) B2364701
theorem B2362913 : Blo 1574485 2362913 := bstep (se 2 (by rfl) ⟨886092, by rfl⟩ : syracuseStep 2362913 = 1772185) B1772185
theorem B1576483 : Blo 1574485 1576483 := bstep (se 1 (by rfl) ⟨1182362, by rfl⟩ : syracuseStep 1576483 = 2364725) B2364725
theorem B7974449 : Blo 1574485 7974449 := bstep (se 2 (by rfl) ⟨2990418, by rfl⟩ : syracuseStep 7974449 = 5980837) B5980837
theorem B2362931 : Blo 1574485 2362931 := bstep (se 1 (by rfl) ⟨1772198, by rfl⟩ : syracuseStep 2362931 = 3544397) B3544397
theorem B5320241 : Blo 1574485 5320241 := bstep (se 2 (by rfl) ⟨1995090, by rfl⟩ : syracuseStep 5320241 = 3990181) B3990181
theorem B2657873 : Blo 1574485 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B2362961 : Blo 1574485 2362961 := bstep (se 2 (by rfl) ⟨886110, by rfl⟩ : syracuseStep 2362961 = 1772221) B1772221
theorem B1773139 : Blo 1574485 1773139 := bstep (se 1 (by rfl) ⟨1329854, by rfl⟩ : syracuseStep 1773139 = 2659709) B2659709
theorem B2362979 : Blo 1574485 2362979 := bstep (se 1 (by rfl) ⟨1772234, by rfl⟩ : syracuseStep 2362979 = 3544469) B3544469
theorem B4484717 : Blo 1574485 4484717 := bstep (se 3 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 4484717 = 1681769) B1681769
theorem B2363009 : Blo 1574485 2363009 := bstep (se 2 (by rfl) ⟨886128, by rfl⟩ : syracuseStep 2363009 = 1772257) B1772257
theorem B2363027 : Blo 1574485 2363027 := bstep (se 1 (by rfl) ⟨1772270, by rfl⟩ : syracuseStep 2363027 = 3544541) B3544541
theorem B3542705 : Blo 1574485 3542705 := bstep (se 2 (by rfl) ⟨1328514, by rfl⟩ : syracuseStep 3542705 = 2657029) B2657029
theorem B2363057 : Blo 1574485 2363057 := bstep (se 2 (by rfl) ⟨886146, by rfl⟩ : syracuseStep 2363057 = 1772293) B1772293
theorem B3542723 : Blo 1574485 3542723 := bstep (se 1 (by rfl) ⟨2657042, by rfl⟩ : syracuseStep 3542723 = 5314085) B5314085
theorem B2363075 : Blo 1574485 2363075 := bstep (se 1 (by rfl) ⟨1772306, by rfl⟩ : syracuseStep 2363075 = 3544613) B3544613
theorem B2658001 : Blo 1574485 2658001 := bstep (se 2 (by rfl) ⟨996750, by rfl⟩ : syracuseStep 2658001 = 1993501) B1993501
theorem B2363105 : Blo 1574485 2363105 := bstep (se 2 (by rfl) ⟨886164, by rfl⟩ : syracuseStep 2363105 = 1772329) B1772329
theorem B1773283 : Blo 1574485 1773283 := bstep (se 1 (by rfl) ⟨1329962, by rfl⟩ : syracuseStep 1773283 = 2659925) B2659925
theorem B2658035 : Blo 1574485 2658035 := bstep (se 1 (by rfl) ⟨1993526, by rfl⟩ : syracuseStep 2658035 = 3987053) B3987053
theorem B2363123 : Blo 1574485 2363123 := bstep (se 1 (by rfl) ⟨1772342, by rfl⟩ : syracuseStep 2363123 = 3544685) B3544685
theorem B1994483 : Blo 1574485 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B2363153 : Blo 1574485 2363153 := bstep (se 2 (by rfl) ⟨886182, by rfl⟩ : syracuseStep 2363153 = 1772365) B1772365
theorem B4484899 : Blo 1574485 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B2363171 : Blo 1574485 2363171 := bstep (se 1 (by rfl) ⟨1772378, by rfl⟩ : syracuseStep 2363171 = 3544757) B3544757
theorem B2363201 : Blo 1574485 2363201 := bstep (se 2 (by rfl) ⟨886200, by rfl⟩ : syracuseStep 2363201 = 1772401) B1772401
theorem B4484945 : Blo 1574485 4484945 := bstep (se 2 (by rfl) ⟨1681854, by rfl⟩ : syracuseStep 4484945 = 3363709) B3363709
theorem B2363219 : Blo 1574485 2363219 := bstep (se 1 (by rfl) ⟨1772414, by rfl⟩ : syracuseStep 2363219 = 3544829) B3544829
theorem B2363249 : Blo 1574485 2363249 := bstep (se 2 (by rfl) ⟨886218, by rfl⟩ : syracuseStep 2363249 = 1772437) B1772437
theorem B2658163 : Blo 1574485 2658163 := bstep (se 1 (by rfl) ⟨1993622, by rfl⟩ : syracuseStep 2658163 = 3987245) B3987245
theorem B1773427 : Blo 1574485 1773427 := bstep (se 1 (by rfl) ⟨1330070, by rfl⟩ : syracuseStep 1773427 = 2660141) B2660141
theorem B2363267 : Blo 1574485 2363267 := bstep (se 1 (by rfl) ⟨1772450, by rfl⟩ : syracuseStep 2363267 = 3544901) B3544901
theorem B15150989 : Blo 1574485 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B2363297 : Blo 1574485 2363297 := bstep (se 2 (by rfl) ⟨886236, by rfl⟩ : syracuseStep 2363297 = 1772473) B1772473
theorem B2363315 : Blo 1574485 2363315 := bstep (se 1 (by rfl) ⟨1772486, by rfl⟩ : syracuseStep 2363315 = 3544973) B3544973
theorem B3542993 : Blo 1574485 3542993 := bstep (se 2 (by rfl) ⟨1328622, by rfl⟩ : syracuseStep 3542993 = 2657245) B2657245
theorem B2363345 : Blo 1574485 2363345 := bstep (se 2 (by rfl) ⟨886254, by rfl⟩ : syracuseStep 2363345 = 1772509) B1772509
theorem B3543011 : Blo 1574485 3543011 := bstep (se 1 (by rfl) ⟨2657258, by rfl⟩ : syracuseStep 3543011 = 5314517) B5314517
theorem B2363363 : Blo 1574485 2363363 := bstep (se 1 (by rfl) ⟨1772522, by rfl⟩ : syracuseStep 2363363 = 3545045) B3545045
theorem B2658305 : Blo 1574485 2658305 := bstep (se 2 (by rfl) ⟨996864, by rfl⟩ : syracuseStep 2658305 = 1993729) B1993729
theorem B2363393 : Blo 1574485 2363393 := bstep (se 2 (by rfl) ⟨886272, by rfl⟩ : syracuseStep 2363393 = 1772545) B1772545
theorem B2363411 : Blo 1574485 2363411 := bstep (se 1 (by rfl) ⟨1772558, by rfl⟩ : syracuseStep 2363411 = 3545117) B3545117
theorem B2363441 : Blo 1574485 2363441 := bstep (se 2 (by rfl) ⟨886290, by rfl⟩ : syracuseStep 2363441 = 1772581) B1772581
theorem B2363459 : Blo 1574485 2363459 := bstep (se 1 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 2363459 = 3545189) B3545189
theorem B2363489 : Blo 1574485 2363489 := bstep (se 2 (by rfl) ⟨886308, by rfl⟩ : syracuseStep 2363489 = 1772617) B1772617
theorem B2363507 : Blo 1574485 2363507 := bstep (se 1 (by rfl) ⟨1772630, by rfl⟩ : syracuseStep 2363507 = 3545261) B3545261
theorem B2658433 : Blo 1574485 2658433 := bstep (se 2 (by rfl) ⟨996912, by rfl⟩ : syracuseStep 2658433 = 1993825) B1993825
theorem B2363537 : Blo 1574485 2363537 := bstep (se 2 (by rfl) ⟨886326, by rfl⟩ : syracuseStep 2363537 = 1772653) B1772653
theorem B2658467 : Blo 1574485 2658467 := bstep (se 1 (by rfl) ⟨1993850, by rfl⟩ : syracuseStep 2658467 = 3987701) B3987701
theorem B2363555 : Blo 1574485 2363555 := bstep (se 1 (by rfl) ⟨1772666, by rfl⟩ : syracuseStep 2363555 = 3545333) B3545333
theorem B2363585 : Blo 1574485 2363585 := bstep (se 2 (by rfl) ⟨886344, by rfl⟩ : syracuseStep 2363585 = 1772689) B1772689
theorem B2363603 : Blo 1574485 2363603 := bstep (se 1 (by rfl) ⟨1772702, by rfl⟩ : syracuseStep 2363603 = 3545405) B3545405
theorem B3543281 : Blo 1574485 3543281 := bstep (se 2 (by rfl) ⟨1328730, by rfl⟩ : syracuseStep 3543281 = 2657461) B2657461
theorem B2363633 : Blo 1574485 2363633 := bstep (se 2 (by rfl) ⟨886362, by rfl⟩ : syracuseStep 2363633 = 1772725) B1772725
theorem B7287025 : Blo 1574485 7287025 := bstep (se 2 (by rfl) ⟨2732634, by rfl⟩ : syracuseStep 7287025 = 5465269) B5465269
theorem B3543299 : Blo 1574485 3543299 := bstep (se 1 (by rfl) ⟨2657474, by rfl⟩ : syracuseStep 3543299 = 5314949) B5314949
theorem B2363651 : Blo 1574485 2363651 := bstep (se 1 (by rfl) ⟨1772738, by rfl⟩ : syracuseStep 2363651 = 3545477) B3545477
theorem B2363681 : Blo 1574485 2363681 := bstep (se 2 (by rfl) ⟨886380, by rfl⟩ : syracuseStep 2363681 = 1772761) B1772761
theorem B2658595 : Blo 1574485 2658595 := bstep (se 1 (by rfl) ⟨1993946, by rfl⟩ : syracuseStep 2658595 = 3987893) B3987893
theorem B2363699 : Blo 1574485 2363699 := bstep (se 1 (by rfl) ⟨1772774, by rfl⟩ : syracuseStep 2363699 = 3545549) B3545549
theorem B2363729 : Blo 1574485 2363729 := bstep (se 2 (by rfl) ⟨886398, by rfl⟩ : syracuseStep 2363729 = 1772797) B1772797
theorem B2363747 : Blo 1574485 2363747 := bstep (se 1 (by rfl) ⟨1772810, by rfl⟩ : syracuseStep 2363747 = 3545621) B3545621
theorem B4256113 : Blo 1574485 4256113 := bstep (se 2 (by rfl) ⟨1596042, by rfl⟩ : syracuseStep 4256113 = 3192085) B3192085
theorem B2363777 : Blo 1574485 2363777 := bstep (se 2 (by rfl) ⟨886416, by rfl⟩ : syracuseStep 2363777 = 1772833) B1772833
theorem B76616077 : Blo 1574485 76616077 := bstep (se 3 (by rfl) ⟨14365514, by rfl⟩ : syracuseStep 76616077 = 28731029) B28731029
theorem B2363795 : Blo 1574485 2363795 := bstep (se 1 (by rfl) ⟨1772846, by rfl⟩ : syracuseStep 2363795 = 3545693) B3545693
theorem B2658737 : Blo 1574485 2658737 := bstep (se 2 (by rfl) ⟨997026, by rfl⟩ : syracuseStep 2658737 = 1994053) B1994053
theorem B2363825 : Blo 1574485 2363825 := bstep (se 2 (by rfl) ⟨886434, by rfl⟩ : syracuseStep 2363825 = 1772869) B1772869
theorem B1995187 : Blo 1574485 1995187 := bstep (se 1 (by rfl) ⟨1496390, by rfl⟩ : syracuseStep 1995187 = 2992781) B2992781
theorem B2363843 : Blo 1574485 2363843 := bstep (se 1 (by rfl) ⟨1772882, by rfl⟩ : syracuseStep 2363843 = 3545765) B3545765
theorem B2363873 : Blo 1574485 2363873 := bstep (se 2 (by rfl) ⟨886452, by rfl⟩ : syracuseStep 2363873 = 1772905) B1772905
theorem B3363299 : Blo 1574485 3363299 := bstep (se 1 (by rfl) ⟨2522474, by rfl⟩ : syracuseStep 3363299 = 5044949) B5044949
theorem B2363891 : Blo 1574485 2363891 := bstep (se 1 (by rfl) ⟨1772918, by rfl⟩ : syracuseStep 2363891 = 3545837) B3545837
theorem B3543569 : Blo 1574485 3543569 := bstep (se 2 (by rfl) ⟨1328838, by rfl⟩ : syracuseStep 3543569 = 2657677) B2657677
theorem B2363921 : Blo 1574485 2363921 := bstep (se 2 (by rfl) ⟨886470, by rfl⟩ : syracuseStep 2363921 = 1772941) B1772941
theorem B3543587 : Blo 1574485 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B2363939 : Blo 1574485 2363939 := bstep (se 1 (by rfl) ⟨1772954, by rfl⟩ : syracuseStep 2363939 = 3545909) B3545909
theorem B3985969 : Blo 1574485 3985969 := bstep (se 2 (by rfl) ⟨1494738, by rfl⟩ : syracuseStep 3985969 = 2989477) B2989477
theorem B2658865 : Blo 1574485 2658865 := bstep (se 2 (by rfl) ⟨997074, by rfl⟩ : syracuseStep 2658865 = 1994149) B1994149
theorem B6730289 : Blo 1574485 6730289 := bstep (se 2 (by rfl) ⟨2523858, by rfl⟩ : syracuseStep 6730289 = 5047717) B5047717
theorem B2363969 : Blo 1574485 2363969 := bstep (se 2 (by rfl) ⟨886488, by rfl⟩ : syracuseStep 2363969 = 1772977) B1772977
theorem B19157573 : Blo 1574485 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B2658899 : Blo 1574485 2658899 := bstep (se 1 (by rfl) ⟨1994174, by rfl⟩ : syracuseStep 2658899 = 3988349) B3988349
theorem B2363987 : Blo 1574485 2363987 := bstep (se 1 (by rfl) ⟨1772990, by rfl⟩ : syracuseStep 2363987 = 3545981) B3545981
theorem B2364017 : Blo 1574485 2364017 := bstep (se 2 (by rfl) ⟨886506, by rfl⟩ : syracuseStep 2364017 = 1773013) B1773013
theorem B2364035 : Blo 1574485 2364035 := bstep (se 1 (by rfl) ⟨1773026, by rfl⟩ : syracuseStep 2364035 = 3546053) B3546053
theorem B20189837 : Blo 1574485 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B3592849 : Blo 1574485 3592849 := bstep (se 2 (by rfl) ⟨1347318, by rfl⟩ : syracuseStep 3592849 = 2694637) B2694637
theorem B2364065 : Blo 1574485 2364065 := bstep (se 2 (by rfl) ⟨886524, by rfl⟩ : syracuseStep 2364065 = 1773049) B1773049
theorem B2364083 : Blo 1574485 2364083 := bstep (se 1 (by rfl) ⟨1773062, by rfl⟩ : syracuseStep 2364083 = 3546125) B3546125
theorem B2364113 : Blo 1574485 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B2659027 : Blo 1574485 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B2364131 : Blo 1574485 2364131 := bstep (se 1 (by rfl) ⟨1773098, by rfl⟩ : syracuseStep 2364131 = 3546197) B3546197
theorem B2364161 : Blo 1574485 2364161 := bstep (se 2 (by rfl) ⟨886560, by rfl⟩ : syracuseStep 2364161 = 1773121) B1773121
theorem B2364179 : Blo 1574485 2364179 := bstep (se 1 (by rfl) ⟨1773134, by rfl⟩ : syracuseStep 2364179 = 3546269) B3546269
theorem B3543857 : Blo 1574485 3543857 := bstep (se 2 (by rfl) ⟨1328946, by rfl⟩ : syracuseStep 3543857 = 2657893) B2657893
theorem B2364209 : Blo 1574485 2364209 := bstep (se 2 (by rfl) ⟨886578, by rfl⟩ : syracuseStep 2364209 = 1773157) B1773157
theorem B3986243 : Blo 1574485 3986243 := bstep (se 1 (by rfl) ⟨2989682, by rfl⟩ : syracuseStep 3986243 = 5979365) B5979365
theorem B3543875 : Blo 1574485 3543875 := bstep (se 1 (by rfl) ⟨2657906, by rfl⟩ : syracuseStep 3543875 = 5315813) B5315813
theorem B18182981 : Blo 1574485 18182981 := bstep (se 4 (by rfl) ⟨1704654, by rfl⟩ : syracuseStep 18182981 = 3409309) B3409309
theorem B2364227 : Blo 1574485 2364227 := bstep (se 1 (by rfl) ⟨1773170, by rfl⟩ : syracuseStep 2364227 = 3546341) B3546341
theorem B2659169 : Blo 1574485 2659169 := bstep (se 2 (by rfl) ⟨997188, by rfl⟩ : syracuseStep 2659169 = 1994377) B1994377
theorem B2364257 : Blo 1574485 2364257 := bstep (se 2 (by rfl) ⟨886596, by rfl⟩ : syracuseStep 2364257 = 1773193) B1773193
theorem B10236785 : Blo 1574485 10236785 := bstep (se 2 (by rfl) ⟨3838794, by rfl⟩ : syracuseStep 10236785 = 7677589) B7677589
theorem B2364275 : Blo 1574485 2364275 := bstep (se 1 (by rfl) ⟨1773206, by rfl⟩ : syracuseStep 2364275 = 3546413) B3546413
theorem B2839427 : Blo 1574485 2839427 := bstep (se 1 (by rfl) ⟨2129570, by rfl⟩ : syracuseStep 2839427 = 4259141) B4259141
theorem B3888017 : Blo 1574485 3888017 := bstep (se 2 (by rfl) ⟨1458006, by rfl⟩ : syracuseStep 3888017 = 2916013) B2916013
theorem B2364305 : Blo 1574485 2364305 := bstep (se 2 (by rfl) ⟨886614, by rfl⟩ : syracuseStep 2364305 = 1773229) B1773229
theorem B2364323 : Blo 1574485 2364323 := bstep (se 1 (by rfl) ⟨1773242, by rfl⟩ : syracuseStep 2364323 = 3546485) B3546485
theorem B3363761 : Blo 1574485 3363761 := bstep (se 2 (by rfl) ⟨1261410, by rfl⟩ : syracuseStep 3363761 = 2522821) B2522821
theorem B1618867 : Blo 1574485 1618867 := bstep (se 1 (by rfl) ⟨1214150, by rfl⟩ : syracuseStep 1618867 = 2428301) B2428301
theorem B10097585 : Blo 1574485 10097585 := bstep (se 2 (by rfl) ⟨3786594, by rfl⟩ : syracuseStep 10097585 = 7573189) B7573189
theorem B2364353 : Blo 1574485 2364353 := bstep (se 2 (by rfl) ⟨886632, by rfl⟩ : syracuseStep 2364353 = 1773265) B1773265
theorem B2364371 : Blo 1574485 2364371 := bstep (se 1 (by rfl) ⟨1773278, by rfl⟩ : syracuseStep 2364371 = 3546557) B3546557
theorem B2659297 : Blo 1574485 2659297 := bstep (se 2 (by rfl) ⟨997236, by rfl⟩ : syracuseStep 2659297 = 1994473) B1994473
theorem B7975907 : Blo 1574485 7975907 := bstep (se 1 (by rfl) ⟨5981930, by rfl⟩ : syracuseStep 7975907 = 11963861) B11963861
theorem B2364401 : Blo 1574485 2364401 := bstep (se 2 (by rfl) ⟨886650, by rfl⟩ : syracuseStep 2364401 = 1773301) B1773301
theorem B3986435 : Blo 1574485 3986435 := bstep (se 1 (by rfl) ⟨2989826, by rfl⟩ : syracuseStep 3986435 = 5979653) B5979653
theorem B2659331 : Blo 1574485 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B2364419 : Blo 1574485 2364419 := bstep (se 1 (by rfl) ⟨1773314, by rfl⟩ : syracuseStep 2364419 = 3546629) B3546629
theorem B2364449 : Blo 1574485 2364449 := bstep (se 2 (by rfl) ⟨886668, by rfl⟩ : syracuseStep 2364449 = 1773337) B1773337
theorem B2364467 : Blo 1574485 2364467 := bstep (se 1 (by rfl) ⟨1773350, by rfl⟩ : syracuseStep 2364467 = 3546701) B3546701
theorem B3544145 : Blo 1574485 3544145 := bstep (se 2 (by rfl) ⟨1329054, by rfl⟩ : syracuseStep 3544145 = 2658109) B2658109
theorem B3839057 : Blo 1574485 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B2364497 : Blo 1574485 2364497 := bstep (se 2 (by rfl) ⟨886686, by rfl⟩ : syracuseStep 2364497 = 1773373) B1773373
theorem B3544163 : Blo 1574485 3544163 := bstep (se 1 (by rfl) ⟨2658122, by rfl⟩ : syracuseStep 3544163 = 5316245) B5316245
theorem B2364515 : Blo 1574485 2364515 := bstep (se 1 (by rfl) ⟨1773386, by rfl⟩ : syracuseStep 2364515 = 3546773) B3546773
theorem B2364545 : Blo 1574485 2364545 := bstep (se 2 (by rfl) ⟨886704, by rfl⟩ : syracuseStep 2364545 = 1773409) B1773409
theorem B2659459 : Blo 1574485 2659459 := bstep (se 1 (by rfl) ⟨1994594, by rfl⟩ : syracuseStep 2659459 = 3989189) B3989189
theorem B2364563 : Blo 1574485 2364563 := bstep (se 1 (by rfl) ⟨1773422, by rfl⟩ : syracuseStep 2364563 = 3546845) B3546845
theorem B8516771 : Blo 1574485 8516771 := bstep (se 1 (by rfl) ⟨6387578, by rfl⟩ : syracuseStep 8516771 = 12775157) B12775157
theorem B2364593 : Blo 1574485 2364593 := bstep (se 2 (by rfl) ⟨886722, by rfl⟩ : syracuseStep 2364593 = 1773445) B1773445
theorem B2364611 : Blo 1574485 2364611 := bstep (se 1 (by rfl) ⟨1773458, by rfl⟩ : syracuseStep 2364611 = 3546917) B3546917
theorem B5985485 : Blo 1574485 5985485 := bstep (se 3 (by rfl) ⟨1122278, by rfl⟩ : syracuseStep 5985485 = 2244557) B2244557
theorem B2364641 : Blo 1574485 2364641 := bstep (se 2 (by rfl) ⟨886740, by rfl⟩ : syracuseStep 2364641 = 1773481) B1773481
theorem B2364659 : Blo 1574485 2364659 := bstep (se 1 (by rfl) ⟨1773494, by rfl⟩ : syracuseStep 2364659 = 3546989) B3546989
theorem B4486403 : Blo 1574485 4486403 := bstep (se 1 (by rfl) ⟨3364802, by rfl⟩ : syracuseStep 4486403 = 6729605) B6729605
theorem B2659601 : Blo 1574485 2659601 := bstep (se 2 (by rfl) ⟨997350, by rfl⟩ : syracuseStep 2659601 = 1994701) B1994701
theorem B2364689 : Blo 1574485 2364689 := bstep (se 2 (by rfl) ⟨886758, by rfl⟩ : syracuseStep 2364689 = 1773517) B1773517
theorem B2364707 : Blo 1574485 2364707 := bstep (se 1 (by rfl) ⟨1773530, by rfl⟩ : syracuseStep 2364707 = 3547061) B3547061
theorem B10786097 : Blo 1574485 10786097 := bstep (se 2 (by rfl) ⟨4044786, by rfl⟩ : syracuseStep 10786097 = 8089573) B8089573
theorem B4044131 : Blo 1574485 4044131 := bstep (se 1 (by rfl) ⟨3033098, by rfl⟩ : syracuseStep 4044131 = 6066197) B6066197
theorem B3544433 : Blo 1574485 3544433 := bstep (se 2 (by rfl) ⟨1329162, by rfl⟩ : syracuseStep 3544433 = 2658325) B2658325
theorem B5313923 : Blo 1574485 5313923 := bstep (se 1 (by rfl) ⟨3985442, by rfl⟩ : syracuseStep 5313923 = 7970885) B7970885
theorem B3544451 : Blo 1574485 3544451 := bstep (se 1 (by rfl) ⟨2658338, by rfl⟩ : syracuseStep 3544451 = 5316677) B5316677
theorem B2659729 : Blo 1574485 2659729 := bstep (se 2 (by rfl) ⟨997398, by rfl⟩ : syracuseStep 2659729 = 1994797) B1994797
theorem B2659763 : Blo 1574485 2659763 := bstep (se 1 (by rfl) ⟨1994822, by rfl⟩ : syracuseStep 2659763 = 3989645) B3989645
theorem B11359757 : Blo 1574485 11359757 := bstep (se 3 (by rfl) ⟨2129954, by rfl⟩ : syracuseStep 11359757 = 4259909) B4259909
theorem B2659891 : Blo 1574485 2659891 := bstep (se 1 (by rfl) ⟨1994918, by rfl⟩ : syracuseStep 2659891 = 3989837) B3989837
theorem B5117521 : Blo 1574485 5117521 := bstep (se 2 (by rfl) ⟨1919070, by rfl⟩ : syracuseStep 5117521 = 3838141) B3838141
theorem B8967793 : Blo 1574485 8967793 := bstep (se 2 (by rfl) ⟨3362922, by rfl⟩ : syracuseStep 8967793 = 6725845) B6725845
theorem B5314193 : Blo 1574485 5314193 := bstep (se 2 (by rfl) ⟨1992822, by rfl⟩ : syracuseStep 5314193 = 3985645) B3985645
theorem B3544721 : Blo 1574485 3544721 := bstep (se 2 (by rfl) ⟨1329270, by rfl⟩ : syracuseStep 3544721 = 2658541) B2658541
theorem B3544739 : Blo 1574485 3544739 := bstep (se 1 (by rfl) ⟨2658554, by rfl⟩ : syracuseStep 3544739 = 5317109) B5317109
theorem B2660033 : Blo 1574485 2660033 := bstep (se 2 (by rfl) ⟨997512, by rfl⟩ : syracuseStep 2660033 = 1995025) B1995025
theorem B34059973 : Blo 1574485 34059973 := bstep (se 4 (by rfl) ⟨3193122, by rfl⟩ : syracuseStep 34059973 = 6386245) B6386245
theorem B11958029 : Blo 1574485 11958029 := bstep (se 3 (by rfl) ⟨2242130, by rfl⟩ : syracuseStep 11958029 = 4484261) B4484261
theorem B7976717 : Blo 1574485 7976717 := bstep (se 3 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 7976717 = 2991269) B2991269
theorem B2660161 : Blo 1574485 2660161 := bstep (se 2 (by rfl) ⟨997560, by rfl⟩ : syracuseStep 2660161 = 1995121) B1995121
theorem B2660195 : Blo 1574485 2660195 := bstep (se 1 (by rfl) ⟨1995146, by rfl⟩ : syracuseStep 2660195 = 3990293) B3990293
theorem B2840465 : Blo 1574485 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B3987377 : Blo 1574485 3987377 := bstep (se 2 (by rfl) ⟨1495266, by rfl⟩ : syracuseStep 3987377 = 2990533) B2990533
theorem B3545009 : Blo 1574485 3545009 := bstep (se 2 (by rfl) ⟨1329378, by rfl⟩ : syracuseStep 3545009 = 2658757) B2658757
theorem B3545027 : Blo 1574485 3545027 := bstep (se 1 (by rfl) ⟨2658770, by rfl⟩ : syracuseStep 3545027 = 5317541) B5317541
theorem B3987427 : Blo 1574485 3987427 := bstep (se 1 (by rfl) ⟨2990570, by rfl⟩ : syracuseStep 3987427 = 5981141) B5981141
theorem B5978225 : Blo 1574485 5978225 := bstep (se 2 (by rfl) ⟨2241834, by rfl⟩ : syracuseStep 5978225 = 4483669) B4483669
theorem B3987569 : Blo 1574485 3987569 := bstep (se 2 (by rfl) ⟨1495338, by rfl⟩ : syracuseStep 3987569 = 2990677) B2990677
theorem B30267533 : Blo 1574485 30267533 := bstep (se 3 (by rfl) ⟨5675162, by rfl⟩ : syracuseStep 30267533 = 11350325) B11350325
theorem B2242723 : Blo 1574485 2242723 := bstep (se 1 (by rfl) ⟨1682042, by rfl⟩ : syracuseStep 2242723 = 3364085) B3364085
theorem B5314733 : Blo 1574485 5314733 := bstep (se 3 (by rfl) ⟨996512, by rfl⟩ : syracuseStep 5314733 = 1993025) B1993025
theorem B3365059 : Blo 1574485 3365059 := bstep (se 1 (by rfl) ⟨2523794, by rfl⟩ : syracuseStep 3365059 = 5047589) B5047589
theorem B6731981 : Blo 1574485 6731981 := bstep (se 3 (by rfl) ⟨1262246, by rfl⟩ : syracuseStep 6731981 = 2524493) B2524493
theorem B3545297 : Blo 1574485 3545297 := bstep (se 2 (by rfl) ⟨1329486, by rfl⟩ : syracuseStep 3545297 = 2658973) B2658973
theorem B5314787 : Blo 1574485 5314787 := bstep (se 1 (by rfl) ⟨3986090, by rfl⟩ : syracuseStep 5314787 = 7972181) B7972181
theorem B3545315 : Blo 1574485 3545315 := bstep (se 1 (by rfl) ⟨2658986, by rfl⟩ : syracuseStep 3545315 = 5317973) B5317973
theorem B3365315 : Blo 1574485 3365315 := bstep (se 1 (by rfl) ⟨2523986, by rfl⟩ : syracuseStep 3365315 = 5047973) B5047973
theorem B17955269 : Blo 1574485 17955269 := bstep (se 4 (by rfl) ⟨1683306, by rfl⟩ : syracuseStep 17955269 = 3366613) B3366613
theorem B4487633 : Blo 1574485 4487633 := bstep (se 2 (by rfl) ⟨1682862, by rfl⟩ : syracuseStep 4487633 = 3365725) B3365725
theorem B5315057 : Blo 1574485 5315057 := bstep (se 2 (by rfl) ⟨1993146, by rfl⟩ : syracuseStep 5315057 = 3986293) B3986293
theorem B3545585 : Blo 1574485 3545585 := bstep (se 2 (by rfl) ⟨1329594, by rfl⟩ : syracuseStep 3545585 = 2659189) B2659189
theorem B3545603 : Blo 1574485 3545603 := bstep (se 1 (by rfl) ⟨2659202, by rfl⟩ : syracuseStep 3545603 = 5318405) B5318405
theorem B2128403 : Blo 1574485 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B3783203 : Blo 1574485 3783203 := bstep (se 1 (by rfl) ⟨2837402, by rfl⟩ : syracuseStep 3783203 = 5674805) B5674805
theorem B3594883 : Blo 1574485 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B7568099 : Blo 1574485 7568099 := bstep (se 1 (by rfl) ⟨5676074, by rfl⟩ : syracuseStep 7568099 = 11352149) B11352149
theorem B5978893 : Blo 1574485 5978893 := bstep (se 3 (by rfl) ⟨1121042, by rfl⟩ : syracuseStep 5978893 = 2242085) B2242085
theorem B3545873 : Blo 1574485 3545873 := bstep (se 2 (by rfl) ⟨1329702, by rfl⟩ : syracuseStep 3545873 = 2659405) B2659405
theorem B3545891 : Blo 1574485 3545891 := bstep (se 1 (by rfl) ⟨2659418, by rfl⟩ : syracuseStep 3545891 = 5318837) B5318837
theorem B22698805 : Blo 1574485 22698805 := bstep (se 5 (by rfl) ⟨1064006, by rfl⟩ : syracuseStep 22698805 = 2128013) B2128013
theorem B2522033 : Blo 1574485 2522033 := bstep (se 2 (by rfl) ⟨945762, by rfl⟩ : syracuseStep 2522033 = 1891525) B1891525
theorem B3783665 : Blo 1574485 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B5315597 : Blo 1574485 5315597 := bstep (se 3 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 5315597 = 1993349) B1993349
theorem B8969251 : Blo 1574485 8969251 := bstep (se 1 (by rfl) ⟨6726938, by rfl⟩ : syracuseStep 8969251 = 13453877) B13453877
theorem B3546161 : Blo 1574485 3546161 := bstep (se 2 (by rfl) ⟨1329810, by rfl⟩ : syracuseStep 3546161 = 2659621) B2659621
theorem B5315651 : Blo 1574485 5315651 := bstep (se 1 (by rfl) ⟨3986738, by rfl⟩ : syracuseStep 5315651 = 7973477) B7973477
theorem B3546179 : Blo 1574485 3546179 := bstep (se 1 (by rfl) ⟨2659634, by rfl⟩ : syracuseStep 3546179 = 5319269) B5319269
theorem B3988561 : Blo 1574485 3988561 := bstep (se 2 (by rfl) ⟨1495710, by rfl⟩ : syracuseStep 3988561 = 2991421) B2991421
theorem B2989219 : Blo 1574485 2989219 := bstep (se 1 (by rfl) ⟨2241914, by rfl⟩ : syracuseStep 2989219 = 4483829) B4483829
theorem B1596611 : Blo 1574485 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B29924549 : Blo 1574485 29924549 := bstep (se 4 (by rfl) ⟨2805426, by rfl⟩ : syracuseStep 29924549 = 5610853) B5610853
theorem B7568653 : Blo 1574485 7568653 := bstep (se 3 (by rfl) ⟨1419122, by rfl⟩ : syracuseStep 7568653 = 2838245) B2838245
theorem B2243857 : Blo 1574485 2243857 := bstep (se 2 (by rfl) ⟨841446, by rfl⟩ : syracuseStep 2243857 = 1682893) B1682893
theorem B2129203 : Blo 1574485 2129203 := bstep (se 1 (by rfl) ⟨1596902, by rfl⟩ : syracuseStep 2129203 = 3193805) B3193805
theorem B2989379 : Blo 1574485 2989379 := bstep (se 1 (by rfl) ⟨2242034, by rfl⟩ : syracuseStep 2989379 = 4484069) B4484069
theorem B4791619 : Blo 1574485 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B10100045 : Blo 1574485 10100045 := bstep (se 3 (by rfl) ⟨1893758, by rfl⟩ : syracuseStep 10100045 = 3787517) B3787517
theorem B5315921 : Blo 1574485 5315921 := bstep (se 2 (by rfl) ⟨1993470, by rfl⟩ : syracuseStep 5315921 = 3986941) B3986941
theorem B3546449 : Blo 1574485 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B3988835 : Blo 1574485 3988835 := bstep (se 1 (by rfl) ⟨2991626, by rfl⟩ : syracuseStep 3988835 = 5983253) B5983253
theorem B3546467 : Blo 1574485 3546467 := bstep (se 1 (by rfl) ⟨2659850, by rfl⟩ : syracuseStep 3546467 = 5319701) B5319701
theorem B2243953 : Blo 1574485 2243953 := bstep (se 2 (by rfl) ⟨841482, by rfl⟩ : syracuseStep 2243953 = 1682965) B1682965
theorem B3366289 : Blo 1574485 3366289 := bstep (se 2 (by rfl) ⟨1262358, by rfl⟩ : syracuseStep 3366289 = 2524717) B2524717
theorem B5979683 : Blo 1574485 5979683 := bstep (se 1 (by rfl) ⟨4484762, by rfl⟩ : syracuseStep 5979683 = 8969525) B8969525
theorem B3989027 : Blo 1574485 3989027 := bstep (se 1 (by rfl) ⟨2991770, by rfl⟩ : syracuseStep 3989027 = 5983541) B5983541
theorem B8969777 : Blo 1574485 8969777 := bstep (se 2 (by rfl) ⟨3363666, by rfl⟩ : syracuseStep 8969777 = 6727333) B6727333
theorem B2694721 : Blo 1574485 2694721 := bstep (se 2 (by rfl) ⟨1010520, by rfl⟩ : syracuseStep 2694721 = 2021041) B2021041
theorem B3546737 : Blo 1574485 3546737 := bstep (se 2 (by rfl) ⟨1330026, by rfl⟩ : syracuseStep 3546737 = 2660053) B2660053
theorem B3546755 : Blo 1574485 3546755 := bstep (se 1 (by rfl) ⟨2660066, by rfl⟩ : syracuseStep 3546755 = 5320133) B5320133
theorem B6389489 : Blo 1574485 6389489 := bstep (se 2 (by rfl) ⟨2396058, by rfl⟩ : syracuseStep 6389489 = 4792117) B4792117
theorem B3030865 : Blo 1574485 3030865 := bstep (se 2 (by rfl) ⟨1136574, by rfl⟩ : syracuseStep 3030865 = 2273149) B2273149
theorem B2244449 : Blo 1574485 2244449 := bstep (se 2 (by rfl) ⟨841668, by rfl⟩ : syracuseStep 2244449 = 1683337) B1683337
theorem B5316461 : Blo 1574485 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B4489091 : Blo 1574485 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B3547025 : Blo 1574485 3547025 := bstep (se 2 (by rfl) ⟨1330134, by rfl⟩ : syracuseStep 3547025 = 2660269) B2660269
theorem B5316515 : Blo 1574485 5316515 := bstep (se 1 (by rfl) ⟨3987386, by rfl⟩ : syracuseStep 5316515 = 7974773) B7974773
theorem B3547043 : Blo 1574485 3547043 := bstep (se 1 (by rfl) ⟨2660282, by rfl⟩ : syracuseStep 3547043 = 5320565) B5320565
theorem B8978525 : Blo 1574485 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B13647973 : Blo 1574485 13647973 := bstep (se 4 (by rfl) ⟨1279497, by rfl⟩ : syracuseStep 13647973 = 2558995) B2558995
theorem B2990297 : Blo 1574485 2990297 := bstep (se 2 (by rfl) ⟨1121361, by rfl⟩ : syracuseStep 2990297 = 2242723) B2242723
theorem B7979309 : Blo 1574485 7979309 := bstep (se 3 (by rfl) ⟨1496120, by rfl⟩ : syracuseStep 7979309 = 2992241) B2992241
theorem B9716033 : Blo 1574485 9716033 := bstep (se 2 (by rfl) ⟨3643512, by rfl⟩ : syracuseStep 9716033 = 7287025) B7287025
theorem B12771715 : Blo 1574485 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B13459891 : Blo 1574485 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B5046731 : Blo 1574485 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B102154769 : Blo 1574485 102154769 := bstep (se 2 (by rfl) ⟨38308038, by rfl⟩ : syracuseStep 102154769 = 76616077) B76616077
theorem B2523673 : Blo 1574485 2523673 := bstep (se 2 (by rfl) ⟨946377, by rfl⟩ : syracuseStep 2523673 = 1892755) B1892755
theorem B1892951 : Blo 1574485 1892951 := bstep (se 1 (by rfl) ⟨1419713, by rfl⟩ : syracuseStep 1892951 = 2839427) B2839427
theorem B57459293 : Blo 1574485 57459293 := bstep (se 3 (by rfl) ⟨10773617, by rfl⟩ : syracuseStep 57459293 = 21547235) B21547235
theorem B5980823 : Blo 1574485 5980823 := bstep (se 1 (by rfl) ⟨4485617, by rfl⟩ : syracuseStep 5980823 = 8971235) B8971235
theorem B5317271 : Blo 1574485 5317271 := bstep (se 1 (by rfl) ⟨3987953, by rfl⟩ : syracuseStep 5317271 = 7975907) B7975907
theorem B5677847 : Blo 1574485 5677847 := bstep (se 1 (by rfl) ⟨4258385, by rfl⟩ : syracuseStep 5677847 = 8516771) B8516771
theorem B3990323 : Blo 1574485 3990323 := bstep (se 1 (by rfl) ⟨2992742, by rfl⟩ : syracuseStep 3990323 = 5985485) B5985485
theorem B2990935 : Blo 1574485 2990935 := bstep (se 1 (by rfl) ⟨2243201, by rfl⟩ : syracuseStep 2990935 = 4486403) B4486403
theorem B4793177 : Blo 1574485 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B2696087 : Blo 1574485 2696087 := bstep (se 1 (by rfl) ⟨2022065, by rfl⟩ : syracuseStep 2696087 = 4044131) B4044131
theorem B7971857 : Blo 1574485 7971857 := bstep (se 2 (by rfl) ⟨2989446, by rfl⟩ : syracuseStep 7971857 = 5978893) B5978893
theorem B7972019 : Blo 1574485 7972019 := bstep (se 1 (by rfl) ⟨5979014, by rfl⟩ : syracuseStep 7972019 = 11958029) B11958029
theorem B5317811 : Blo 1574485 5317811 := bstep (se 1 (by rfl) ⟨3988358, by rfl⟩ : syracuseStep 5317811 = 7976717) B7976717
theorem B4261043 : Blo 1574485 4261043 := bstep (se 1 (by rfl) ⟨3195782, by rfl⟩ : syracuseStep 4261043 = 6391565) B6391565
theorem B1705303 : Blo 1574485 1705303 := bstep (se 1 (by rfl) ⟨1278977, by rfl⟩ : syracuseStep 1705303 = 2557955) B2557955
theorem B20178355 : Blo 1574485 20178355 := bstep (se 1 (by rfl) ⟨15133766, by rfl⟩ : syracuseStep 20178355 = 30267533) B30267533
theorem B5318081 : Blo 1574485 5318081 := bstep (se 2 (by rfl) ⟨1994280, by rfl⟩ : syracuseStep 5318081 = 3988561) B3988561
theorem B5047859 : Blo 1574485 5047859 := bstep (se 1 (by rfl) ⟨3785894, by rfl⟩ : syracuseStep 5047859 = 7571789) B7571789
theorem B1574487 : Blo 1574485 1574487 := bstep (se 1 (by rfl) ⟨1180865, by rfl⟩ : syracuseStep 1574487 = 2361731) B2361731
theorem B1574507 : Blo 1574485 1574507 := bstep (se 1 (by rfl) ⟨1180880, by rfl⟩ : syracuseStep 1574507 = 2361761) B2361761
theorem B1574519 : Blo 1574485 1574519 := bstep (se 1 (by rfl) ⟨1180889, by rfl⟩ : syracuseStep 1574519 = 2361779) B2361779
theorem B17942147 : Blo 1574485 17942147 := bstep (se 1 (by rfl) ⟨13456610, by rfl⟩ : syracuseStep 17942147 = 26913221) B26913221
theorem B11970179 : Blo 1574485 11970179 := bstep (se 1 (by rfl) ⟨8977634, by rfl⟩ : syracuseStep 11970179 = 17955269) B17955269
theorem B1574539 : Blo 1574485 1574539 := bstep (se 1 (by rfl) ⟨1180904, by rfl⟩ : syracuseStep 1574539 = 2361809) B2361809
theorem B2991755 : Blo 1574485 2991755 := bstep (se 1 (by rfl) ⟨2243816, by rfl⟩ : syracuseStep 2991755 = 4487633) B4487633
theorem B1574551 : Blo 1574485 1574551 := bstep (se 1 (by rfl) ⟨1180913, by rfl⟩ : syracuseStep 1574551 = 2361827) B2361827
theorem B10929815 : Blo 1574485 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B1574571 : Blo 1574485 1574571 := bstep (se 1 (by rfl) ⟨1180928, by rfl⟩ : syracuseStep 1574571 = 2361857) B2361857
theorem B1574583 : Blo 1574485 1574583 := bstep (se 1 (by rfl) ⟨1180937, by rfl⟩ : syracuseStep 1574583 = 2361875) B2361875
theorem B2991809 : Blo 1574485 2991809 := bstep (se 2 (by rfl) ⟨1121928, by rfl⟩ : syracuseStep 2991809 = 2243857) B2243857
theorem B1574603 : Blo 1574485 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B1574615 : Blo 1574485 1574615 := bstep (se 1 (by rfl) ⟨1180961, by rfl⟩ : syracuseStep 1574615 = 2361923) B2361923
theorem B2557657 : Blo 1574485 2557657 := bstep (se 2 (by rfl) ⟨959121, by rfl⟩ : syracuseStep 2557657 = 1918243) B1918243
theorem B1574635 : Blo 1574485 1574635 := bstep (se 1 (by rfl) ⟨1180976, by rfl⟩ : syracuseStep 1574635 = 2361953) B2361953
theorem B1574647 : Blo 1574485 1574647 := bstep (se 1 (by rfl) ⟨1180985, by rfl⟩ : syracuseStep 1574647 = 2361971) B2361971
theorem B16164613 : Blo 1574485 16164613 := bstep (se 4 (by rfl) ⟨1515432, by rfl⟩ : syracuseStep 16164613 = 3030865) B3030865
theorem B1574667 : Blo 1574485 1574667 := bstep (se 1 (by rfl) ⟨1181000, by rfl⟩ : syracuseStep 1574667 = 2362001) B2362001
theorem B1574679 : Blo 1574485 1574679 := bstep (se 1 (by rfl) ⟨1181009, by rfl⟩ : syracuseStep 1574679 = 2362019) B2362019
theorem B1574699 : Blo 1574485 1574699 := bstep (se 1 (by rfl) ⟨1181024, by rfl⟩ : syracuseStep 1574699 = 2362049) B2362049
theorem B1574711 : Blo 1574485 1574711 := bstep (se 1 (by rfl) ⟨1181033, by rfl⟩ : syracuseStep 1574711 = 2362067) B2362067
theorem B1771339 : Blo 1574485 1771339 := bstep (se 1 (by rfl) ⟨1328504, by rfl⟩ : syracuseStep 1771339 = 2657009) B2657009
theorem B1574731 : Blo 1574485 1574731 := bstep (se 1 (by rfl) ⟨1181048, by rfl⟩ : syracuseStep 1574731 = 2362097) B2362097
theorem B1574743 : Blo 1574485 1574743 := bstep (se 1 (by rfl) ⟨1181057, by rfl⟩ : syracuseStep 1574743 = 2362115) B2362115
theorem B1574763 : Blo 1574485 1574763 := bstep (se 1 (by rfl) ⟨1181072, by rfl⟩ : syracuseStep 1574763 = 2362145) B2362145
theorem B1574775 : Blo 1574485 1574775 := bstep (se 1 (by rfl) ⟨1181081, by rfl⟩ : syracuseStep 1574775 = 2362163) B2362163
theorem B5982083 : Blo 1574485 5982083 := bstep (se 1 (by rfl) ⟨4486562, by rfl⟩ : syracuseStep 5982083 = 8973125) B8973125
theorem B1574795 : Blo 1574485 1574795 := bstep (se 1 (by rfl) ⟨1181096, by rfl⟩ : syracuseStep 1574795 = 2362193) B2362193
theorem B1574807 : Blo 1574485 1574807 := bstep (se 1 (by rfl) ⟨1181105, by rfl⟩ : syracuseStep 1574807 = 2362211) B2362211
theorem B1574827 : Blo 1574485 1574827 := bstep (se 1 (by rfl) ⟨1181120, by rfl⟩ : syracuseStep 1574827 = 2362241) B2362241
theorem B1771447 : Blo 1574485 1771447 := bstep (se 1 (by rfl) ⟨1328585, by rfl⟩ : syracuseStep 1771447 = 2657171) B2657171
theorem B1574839 : Blo 1574485 1574839 := bstep (se 1 (by rfl) ⟨1181129, by rfl⟩ : syracuseStep 1574839 = 2362259) B2362259
theorem B1681355 : Blo 1574485 1681355 := bstep (se 1 (by rfl) ⟨1261016, by rfl⟩ : syracuseStep 1681355 = 2522033) B2522033
theorem B1574859 : Blo 1574485 1574859 := bstep (se 1 (by rfl) ⟨1181144, by rfl⟩ : syracuseStep 1574859 = 2362289) B2362289
theorem B1574871 : Blo 1574485 1574871 := bstep (se 1 (by rfl) ⟨1181153, by rfl⟩ : syracuseStep 1574871 = 2362307) B2362307
theorem B5318621 : Blo 1574485 5318621 := bstep (se 3 (by rfl) ⟨997241, by rfl⟩ : syracuseStep 5318621 = 1994483) B1994483
theorem B1574891 : Blo 1574485 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B1574903 : Blo 1574485 1574903 := bstep (se 1 (by rfl) ⟨1181177, by rfl⟩ : syracuseStep 1574903 = 2362355) B2362355
theorem B1574923 : Blo 1574485 1574923 := bstep (se 1 (by rfl) ⟨1181192, by rfl⟩ : syracuseStep 1574923 = 2362385) B2362385
theorem B1574935 : Blo 1574485 1574935 := bstep (se 1 (by rfl) ⟨1181201, by rfl⟩ : syracuseStep 1574935 = 2362403) B2362403
theorem B11962403 : Blo 1574485 11962403 := bstep (se 1 (by rfl) ⟨8971802, by rfl⟩ : syracuseStep 11962403 = 17943605) B17943605
theorem B1574955 : Blo 1574485 1574955 := bstep (se 1 (by rfl) ⟨1181216, by rfl⟩ : syracuseStep 1574955 = 2362433) B2362433
theorem B1574967 : Blo 1574485 1574967 := bstep (se 1 (by rfl) ⟨1181225, by rfl⟩ : syracuseStep 1574967 = 2362451) B2362451
theorem B1574987 : Blo 1574485 1574987 := bstep (se 1 (by rfl) ⟨1181240, by rfl⟩ : syracuseStep 1574987 = 2362481) B2362481
theorem B1574999 : Blo 1574485 1574999 := bstep (se 1 (by rfl) ⟨1181249, by rfl⟩ : syracuseStep 1574999 = 2362499) B2362499
theorem B1771627 : Blo 1574485 1771627 := bstep (se 1 (by rfl) ⟨1328720, by rfl⟩ : syracuseStep 1771627 = 2657441) B2657441
theorem B1575019 : Blo 1574485 1575019 := bstep (se 1 (by rfl) ⟨1181264, by rfl⟩ : syracuseStep 1575019 = 2362529) B2362529
theorem B1575031 : Blo 1574485 1575031 := bstep (se 1 (by rfl) ⟨1181273, by rfl⟩ : syracuseStep 1575031 = 2362547) B2362547
theorem B19949699 : Blo 1574485 19949699 := bstep (se 1 (by rfl) ⟨14962274, by rfl⟩ : syracuseStep 19949699 = 29924549) B29924549
theorem B1575051 : Blo 1574485 1575051 := bstep (se 1 (by rfl) ⟨1181288, by rfl⟩ : syracuseStep 1575051 = 2362577) B2362577
theorem B1575063 : Blo 1574485 1575063 := bstep (se 1 (by rfl) ⟨1181297, by rfl⟩ : syracuseStep 1575063 = 2362595) B2362595
theorem B1575083 : Blo 1574485 1575083 := bstep (se 1 (by rfl) ⟨1181312, by rfl⟩ : syracuseStep 1575083 = 2362625) B2362625
theorem B1575095 : Blo 1574485 1575095 := bstep (se 1 (by rfl) ⟨1181321, by rfl⟩ : syracuseStep 1575095 = 2362643) B2362643
theorem B1575115 : Blo 1574485 1575115 := bstep (se 1 (by rfl) ⟨1181336, by rfl⟩ : syracuseStep 1575115 = 2362673) B2362673
theorem B1992919 : Blo 1574485 1992919 := bstep (se 1 (by rfl) ⟨1494689, by rfl⟩ : syracuseStep 1992919 = 2989379) B2989379
theorem B1771735 : Blo 1574485 1771735 := bstep (se 1 (by rfl) ⟨1328801, by rfl⟩ : syracuseStep 1771735 = 2657603) B2657603
theorem B1575127 : Blo 1574485 1575127 := bstep (se 1 (by rfl) ⟨1181345, by rfl⟩ : syracuseStep 1575127 = 2362691) B2362691
theorem B1575147 : Blo 1574485 1575147 := bstep (se 1 (by rfl) ⟨1181360, by rfl⟩ : syracuseStep 1575147 = 2362721) B2362721
theorem B1575159 : Blo 1574485 1575159 := bstep (se 1 (by rfl) ⟨1181369, by rfl⟩ : syracuseStep 1575159 = 2362739) B2362739
theorem B1575179 : Blo 1574485 1575179 := bstep (se 1 (by rfl) ⟨1181384, by rfl⟩ : syracuseStep 1575179 = 2362769) B2362769
theorem B1575191 : Blo 1574485 1575191 := bstep (se 1 (by rfl) ⟨1181393, by rfl⟩ : syracuseStep 1575191 = 2362787) B2362787
theorem B1575211 : Blo 1574485 1575211 := bstep (se 1 (by rfl) ⟨1181408, by rfl⟩ : syracuseStep 1575211 = 2362817) B2362817
theorem B27298093 : Blo 1574485 27298093 := bstep (se 3 (by rfl) ⟨5118392, by rfl⟩ : syracuseStep 27298093 = 10236785) B10236785
theorem B1575223 : Blo 1574485 1575223 := bstep (se 1 (by rfl) ⟨1181417, by rfl⟩ : syracuseStep 1575223 = 2362835) B2362835
theorem B1575243 : Blo 1574485 1575243 := bstep (se 1 (by rfl) ⟨1181432, by rfl⟩ : syracuseStep 1575243 = 2362865) B2362865
theorem B1575255 : Blo 1574485 1575255 := bstep (se 1 (by rfl) ⟨1181441, by rfl⟩ : syracuseStep 1575255 = 2362883) B2362883
theorem B1575275 : Blo 1574485 1575275 := bstep (se 1 (by rfl) ⟨1181456, by rfl⟩ : syracuseStep 1575275 = 2362913) B2362913
theorem B1575287 : Blo 1574485 1575287 := bstep (se 1 (by rfl) ⟨1181465, by rfl⟩ : syracuseStep 1575287 = 2362931) B2362931
theorem B1771915 : Blo 1574485 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B1575307 : Blo 1574485 1575307 := bstep (se 1 (by rfl) ⟨1181480, by rfl⟩ : syracuseStep 1575307 = 2362961) B2362961
theorem B1575319 : Blo 1574485 1575319 := bstep (se 1 (by rfl) ⟨1181489, by rfl⟩ : syracuseStep 1575319 = 2362979) B2362979
theorem B1575339 : Blo 1574485 1575339 := bstep (se 1 (by rfl) ⟨1181504, by rfl⟩ : syracuseStep 1575339 = 2363009) B2363009
theorem B1575351 : Blo 1574485 1575351 := bstep (se 1 (by rfl) ⟨1181513, by rfl⟩ : syracuseStep 1575351 = 2363027) B2363027
theorem B2361803 : Blo 1574485 2361803 := bstep (se 1 (by rfl) ⟨1771352, by rfl⟩ : syracuseStep 2361803 = 3542705) B3542705
theorem B1575371 : Blo 1574485 1575371 := bstep (se 1 (by rfl) ⟨1181528, by rfl⟩ : syracuseStep 1575371 = 2363057) B2363057
theorem B2361815 : Blo 1574485 2361815 := bstep (se 1 (by rfl) ⟨1771361, by rfl⟩ : syracuseStep 2361815 = 3542723) B3542723
theorem B1575383 : Blo 1574485 1575383 := bstep (se 1 (by rfl) ⟨1181537, by rfl⟩ : syracuseStep 1575383 = 2363075) B2363075
theorem B1575403 : Blo 1574485 1575403 := bstep (se 1 (by rfl) ⟨1181552, by rfl⟩ : syracuseStep 1575403 = 2363105) B2363105
theorem B1772023 : Blo 1574485 1772023 := bstep (se 1 (by rfl) ⟨1329017, by rfl⟩ : syracuseStep 1772023 = 2658035) B2658035
theorem B1575415 : Blo 1574485 1575415 := bstep (se 1 (by rfl) ⟨1181561, by rfl⟩ : syracuseStep 1575415 = 2363123) B2363123
theorem B1575435 : Blo 1574485 1575435 := bstep (se 1 (by rfl) ⟨1181576, by rfl⟩ : syracuseStep 1575435 = 2363153) B2363153
theorem B1575447 : Blo 1574485 1575447 := bstep (se 1 (by rfl) ⟨1181585, by rfl⟩ : syracuseStep 1575447 = 2363171) B2363171
theorem B2361881 : Blo 1574485 2361881 := bstep (se 2 (by rfl) ⟨885705, by rfl⟩ : syracuseStep 2361881 = 1771411) B1771411
theorem B1575467 : Blo 1574485 1575467 := bstep (se 1 (by rfl) ⟨1181600, by rfl⟩ : syracuseStep 1575467 = 2363201) B2363201
theorem B1575479 : Blo 1574485 1575479 := bstep (se 1 (by rfl) ⟨1181609, by rfl⟩ : syracuseStep 1575479 = 2363219) B2363219
theorem B1575499 : Blo 1574485 1575499 := bstep (se 1 (by rfl) ⟨1181624, by rfl⟩ : syracuseStep 1575499 = 2363249) B2363249
theorem B1575511 : Blo 1574485 1575511 := bstep (se 1 (by rfl) ⟨1181633, by rfl⟩ : syracuseStep 1575511 = 2363267) B2363267
theorem B2992727 : Blo 1574485 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B1575531 : Blo 1574485 1575531 := bstep (se 1 (by rfl) ⟨1181648, by rfl⟩ : syracuseStep 1575531 = 2363297) B2363297
theorem B1575543 : Blo 1574485 1575543 := bstep (se 1 (by rfl) ⟨1181657, by rfl⟩ : syracuseStep 1575543 = 2363315) B2363315
theorem B2361995 : Blo 1574485 2361995 := bstep (se 1 (by rfl) ⟨1771496, by rfl⟩ : syracuseStep 2361995 = 3542993) B3542993
theorem B1575563 : Blo 1574485 1575563 := bstep (se 1 (by rfl) ⟨1181672, by rfl⟩ : syracuseStep 1575563 = 2363345) B2363345
theorem B2362007 : Blo 1574485 2362007 := bstep (se 1 (by rfl) ⟨1771505, by rfl⟩ : syracuseStep 2362007 = 3543011) B3543011
theorem B1575575 : Blo 1574485 1575575 := bstep (se 1 (by rfl) ⟨1181681, by rfl⟩ : syracuseStep 1575575 = 2363363) B2363363
theorem B1772203 : Blo 1574485 1772203 := bstep (se 1 (by rfl) ⟨1329152, by rfl⟩ : syracuseStep 1772203 = 2658305) B2658305
theorem B1575595 : Blo 1574485 1575595 := bstep (se 1 (by rfl) ⟨1181696, by rfl⟩ : syracuseStep 1575595 = 2363393) B2363393
theorem B1575607 : Blo 1574485 1575607 := bstep (se 1 (by rfl) ⟨1181705, by rfl⟩ : syracuseStep 1575607 = 2363411) B2363411
theorem B1575627 : Blo 1574485 1575627 := bstep (se 1 (by rfl) ⟨1181720, by rfl⟩ : syracuseStep 1575627 = 2363441) B2363441
theorem B1575639 : Blo 1574485 1575639 := bstep (se 1 (by rfl) ⟨1181729, by rfl⟩ : syracuseStep 1575639 = 2363459) B2363459
theorem B2362073 : Blo 1574485 2362073 := bstep (se 2 (by rfl) ⟨885777, by rfl⟩ : syracuseStep 2362073 = 1771555) B1771555
theorem B5049049 : Blo 1574485 5049049 := bstep (se 2 (by rfl) ⟨1893393, by rfl⟩ : syracuseStep 5049049 = 3786787) B3786787
theorem B1575659 : Blo 1574485 1575659 := bstep (se 1 (by rfl) ⟨1181744, by rfl⟩ : syracuseStep 1575659 = 2363489) B2363489
theorem B1575671 : Blo 1574485 1575671 := bstep (se 1 (by rfl) ⟨1181753, by rfl⟩ : syracuseStep 1575671 = 2363507) B2363507
theorem B1575691 : Blo 1574485 1575691 := bstep (se 1 (by rfl) ⟨1181768, by rfl⟩ : syracuseStep 1575691 = 2363537) B2363537
theorem B1772311 : Blo 1574485 1772311 := bstep (se 1 (by rfl) ⟨1329233, by rfl⟩ : syracuseStep 1772311 = 2658467) B2658467
theorem B1575703 : Blo 1574485 1575703 := bstep (se 1 (by rfl) ⟨1181777, by rfl⟩ : syracuseStep 1575703 = 2363555) B2363555
theorem B1575723 : Blo 1574485 1575723 := bstep (se 1 (by rfl) ⟨1181792, by rfl⟩ : syracuseStep 1575723 = 2363585) B2363585
theorem B1575735 : Blo 1574485 1575735 := bstep (se 1 (by rfl) ⟨1181801, by rfl⟩ : syracuseStep 1575735 = 2363603) B2363603
theorem B2362187 : Blo 1574485 2362187 := bstep (se 1 (by rfl) ⟨1771640, by rfl⟩ : syracuseStep 2362187 = 3543281) B3543281
theorem B1575755 : Blo 1574485 1575755 := bstep (se 1 (by rfl) ⟨1181816, by rfl⟩ : syracuseStep 1575755 = 2363633) B2363633
theorem B2362199 : Blo 1574485 2362199 := bstep (se 1 (by rfl) ⟨1771649, by rfl⟩ : syracuseStep 2362199 = 3543299) B3543299
theorem B1575767 : Blo 1574485 1575767 := bstep (se 1 (by rfl) ⟨1181825, by rfl⟩ : syracuseStep 1575767 = 2363651) B2363651
theorem B1575787 : Blo 1574485 1575787 := bstep (se 1 (by rfl) ⟨1181840, by rfl⟩ : syracuseStep 1575787 = 2363681) B2363681
theorem B1796971 : Blo 1574485 1796971 := bstep (se 1 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 1796971 = 2695457) B2695457
theorem B1575799 : Blo 1574485 1575799 := bstep (se 1 (by rfl) ⟨1181849, by rfl⟩ : syracuseStep 1575799 = 2363699) B2363699
theorem B6728579 : Blo 1574485 6728579 := bstep (se 1 (by rfl) ⟨5046434, by rfl⟩ : syracuseStep 6728579 = 10092869) B10092869
theorem B1575819 : Blo 1574485 1575819 := bstep (se 1 (by rfl) ⟨1181864, by rfl⟩ : syracuseStep 1575819 = 2363729) B2363729
theorem B1575831 : Blo 1574485 1575831 := bstep (se 1 (by rfl) ⟨1181873, by rfl⟩ : syracuseStep 1575831 = 2363747) B2363747
theorem B2362265 : Blo 1574485 2362265 := bstep (se 2 (by rfl) ⟨885849, by rfl⟩ : syracuseStep 2362265 = 1771699) B1771699
theorem B1575851 : Blo 1574485 1575851 := bstep (se 1 (by rfl) ⟨1181888, by rfl⟩ : syracuseStep 1575851 = 2363777) B2363777
theorem B1575863 : Blo 1574485 1575863 := bstep (se 1 (by rfl) ⟨1181897, by rfl⟩ : syracuseStep 1575863 = 2363795) B2363795
theorem B1772491 : Blo 1574485 1772491 := bstep (se 1 (by rfl) ⟨1329368, by rfl⟩ : syracuseStep 1772491 = 2658737) B2658737
theorem B1575883 : Blo 1574485 1575883 := bstep (se 1 (by rfl) ⟨1181912, by rfl⟩ : syracuseStep 1575883 = 2363825) B2363825
theorem B1575895 : Blo 1574485 1575895 := bstep (se 1 (by rfl) ⟨1181921, by rfl⟩ : syracuseStep 1575895 = 2363843) B2363843
theorem B5049305 : Blo 1574485 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B1575915 : Blo 1574485 1575915 := bstep (se 1 (by rfl) ⟨1181936, by rfl⟩ : syracuseStep 1575915 = 2363873) B2363873
theorem B1575927 : Blo 1574485 1575927 := bstep (se 1 (by rfl) ⟨1181945, by rfl⟩ : syracuseStep 1575927 = 2363891) B2363891
theorem B2362379 : Blo 1574485 2362379 := bstep (se 1 (by rfl) ⟨1771784, by rfl⟩ : syracuseStep 2362379 = 3543569) B3543569
theorem B1575947 : Blo 1574485 1575947 := bstep (se 1 (by rfl) ⟨1181960, by rfl⟩ : syracuseStep 1575947 = 2363921) B2363921
theorem B2362391 : Blo 1574485 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B1575959 : Blo 1574485 1575959 := bstep (se 1 (by rfl) ⟨1181969, by rfl⟩ : syracuseStep 1575959 = 2363939) B2363939
theorem B1575979 : Blo 1574485 1575979 := bstep (se 1 (by rfl) ⟨1181984, by rfl⟩ : syracuseStep 1575979 = 2363969) B2363969
theorem B1772599 : Blo 1574485 1772599 := bstep (se 1 (by rfl) ⟨1329449, by rfl⟩ : syracuseStep 1772599 = 2658899) B2658899
theorem B1575991 : Blo 1574485 1575991 := bstep (se 1 (by rfl) ⟨1181993, by rfl⟩ : syracuseStep 1575991 = 2363987) B2363987
theorem B7973963 : Blo 1574485 7973963 := bstep (se 1 (by rfl) ⟨5980472, by rfl⟩ : syracuseStep 7973963 = 11960945) B11960945
theorem B1576011 : Blo 1574485 1576011 := bstep (se 1 (by rfl) ⟨1182008, by rfl⟩ : syracuseStep 1576011 = 2364017) B2364017
theorem B5319755 : Blo 1574485 5319755 := bstep (se 1 (by rfl) ⟨3989816, by rfl⟩ : syracuseStep 5319755 = 7979633) B7979633
theorem B1576023 : Blo 1574485 1576023 := bstep (se 1 (by rfl) ⟨1182017, by rfl⟩ : syracuseStep 1576023 = 2364035) B2364035
theorem B2362457 : Blo 1574485 2362457 := bstep (se 2 (by rfl) ⟨885921, by rfl⟩ : syracuseStep 2362457 = 1771843) B1771843
theorem B1576043 : Blo 1574485 1576043 := bstep (se 1 (by rfl) ⟨1182032, by rfl⟩ : syracuseStep 1576043 = 2364065) B2364065
theorem B1576055 : Blo 1574485 1576055 := bstep (se 1 (by rfl) ⟨1182041, by rfl⟩ : syracuseStep 1576055 = 2364083) B2364083
theorem B8973443 : Blo 1574485 8973443 := bstep (se 1 (by rfl) ⟨6730082, by rfl⟩ : syracuseStep 8973443 = 13460165) B13460165
theorem B1576075 : Blo 1574485 1576075 := bstep (se 1 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 1576075 = 2364113) B2364113
theorem B1576087 : Blo 1574485 1576087 := bstep (se 1 (by rfl) ⟨1182065, by rfl⟩ : syracuseStep 1576087 = 2364131) B2364131
theorem B1576107 : Blo 1574485 1576107 := bstep (se 1 (by rfl) ⟨1182080, by rfl⟩ : syracuseStep 1576107 = 2364161) B2364161
theorem B1576119 : Blo 1574485 1576119 := bstep (se 1 (by rfl) ⟨1182089, by rfl⟩ : syracuseStep 1576119 = 2364179) B2364179
theorem B2362571 : Blo 1574485 2362571 := bstep (se 1 (by rfl) ⟨1771928, by rfl⟩ : syracuseStep 2362571 = 3543857) B3543857
theorem B1576139 : Blo 1574485 1576139 := bstep (se 1 (by rfl) ⟨1182104, by rfl⟩ : syracuseStep 1576139 = 2364209) B2364209
theorem B2657495 : Blo 1574485 2657495 := bstep (se 1 (by rfl) ⟨1993121, by rfl⟩ : syracuseStep 2657495 = 3986243) B3986243
theorem B2362583 : Blo 1574485 2362583 := bstep (se 1 (by rfl) ⟨1771937, by rfl⟩ : syracuseStep 2362583 = 3543875) B3543875
theorem B1576151 : Blo 1574485 1576151 := bstep (se 1 (by rfl) ⟨1182113, by rfl⟩ : syracuseStep 1576151 = 2364227) B2364227
theorem B1772779 : Blo 1574485 1772779 := bstep (se 1 (by rfl) ⟨1329584, by rfl⟩ : syracuseStep 1772779 = 2659169) B2659169
theorem B1576171 : Blo 1574485 1576171 := bstep (se 1 (by rfl) ⟨1182128, by rfl⟩ : syracuseStep 1576171 = 2364257) B2364257
theorem B1576183 : Blo 1574485 1576183 := bstep (se 1 (by rfl) ⟨1182137, by rfl⟩ : syracuseStep 1576183 = 2364275) B2364275
theorem B2592011 : Blo 1574485 2592011 := bstep (se 1 (by rfl) ⟨1944008, by rfl⟩ : syracuseStep 2592011 = 3888017) B3888017
theorem B1576203 : Blo 1574485 1576203 := bstep (se 1 (by rfl) ⟨1182152, by rfl⟩ : syracuseStep 1576203 = 2364305) B2364305
theorem B1576215 : Blo 1574485 1576215 := bstep (se 1 (by rfl) ⟨1182161, by rfl⟩ : syracuseStep 1576215 = 2364323) B2364323
theorem B2362649 : Blo 1574485 2362649 := bstep (se 2 (by rfl) ⟨885993, by rfl⟩ : syracuseStep 2362649 = 1771987) B1771987
theorem B1576235 : Blo 1574485 1576235 := bstep (se 1 (by rfl) ⟨1182176, by rfl⟩ : syracuseStep 1576235 = 2364353) B2364353
theorem B1682743 : Blo 1574485 1682743 := bstep (se 1 (by rfl) ⟨1262057, by rfl⟩ : syracuseStep 1682743 = 2524115) B2524115
theorem B1576247 : Blo 1574485 1576247 := bstep (se 1 (by rfl) ⟨1182185, by rfl⟩ : syracuseStep 1576247 = 2364371) B2364371
theorem B7187777 : Blo 1574485 7187777 := bstep (se 2 (by rfl) ⟨2695416, by rfl⟩ : syracuseStep 7187777 = 5390833) B5390833
theorem B5049665 : Blo 1574485 5049665 := bstep (se 2 (by rfl) ⟨1893624, by rfl⟩ : syracuseStep 5049665 = 3787249) B3787249
theorem B1576267 : Blo 1574485 1576267 := bstep (se 1 (by rfl) ⟨1182200, by rfl⟩ : syracuseStep 1576267 = 2364401) B2364401
theorem B2657623 : Blo 1574485 2657623 := bstep (se 1 (by rfl) ⟨1993217, by rfl⟩ : syracuseStep 2657623 = 3986435) B3986435
theorem B1772887 : Blo 1574485 1772887 := bstep (se 1 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 1772887 = 2659331) B2659331
theorem B1576279 : Blo 1574485 1576279 := bstep (se 1 (by rfl) ⟨1182209, by rfl⟩ : syracuseStep 1576279 = 2364419) B2364419
theorem B5320025 : Blo 1574485 5320025 := bstep (se 2 (by rfl) ⟨1995009, by rfl⟩ : syracuseStep 5320025 = 3990019) B3990019
theorem B1576299 : Blo 1574485 1576299 := bstep (se 1 (by rfl) ⟨1182224, by rfl⟩ : syracuseStep 1576299 = 2364449) B2364449
theorem B1576311 : Blo 1574485 1576311 := bstep (se 1 (by rfl) ⟨1182233, by rfl⟩ : syracuseStep 1576311 = 2364467) B2364467
theorem B2362763 : Blo 1574485 2362763 := bstep (se 1 (by rfl) ⟨1772072, by rfl⟩ : syracuseStep 2362763 = 3544145) B3544145
theorem B2559371 : Blo 1574485 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B5680529 : Blo 1574485 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B1576331 : Blo 1574485 1576331 := bstep (se 1 (by rfl) ⟨1182248, by rfl⟩ : syracuseStep 1576331 = 2364497) B2364497
theorem B2362775 : Blo 1574485 2362775 := bstep (se 1 (by rfl) ⟨1772081, by rfl⟩ : syracuseStep 2362775 = 3544163) B3544163
theorem B1576343 : Blo 1574485 1576343 := bstep (se 1 (by rfl) ⟨1182257, by rfl⟩ : syracuseStep 1576343 = 2364515) B2364515
theorem B1576363 : Blo 1574485 1576363 := bstep (se 1 (by rfl) ⟨1182272, by rfl⟩ : syracuseStep 1576363 = 2364545) B2364545
theorem B1576375 : Blo 1574485 1576375 := bstep (se 1 (by rfl) ⟨1182281, by rfl⟩ : syracuseStep 1576375 = 2364563) B2364563
theorem B1576395 : Blo 1574485 1576395 := bstep (se 1 (by rfl) ⟨1182296, by rfl⟩ : syracuseStep 1576395 = 2364593) B2364593
theorem B1576407 : Blo 1574485 1576407 := bstep (se 1 (by rfl) ⟨1182305, by rfl⟩ : syracuseStep 1576407 = 2364611) B2364611
theorem B2362841 : Blo 1574485 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B3837401 : Blo 1574485 3837401 := bstep (se 2 (by rfl) ⟨1439025, by rfl⟩ : syracuseStep 3837401 = 2878051) B2878051
theorem B1576427 : Blo 1574485 1576427 := bstep (se 1 (by rfl) ⟨1182320, by rfl⟩ : syracuseStep 1576427 = 2364641) B2364641
theorem B1576439 : Blo 1574485 1576439 := bstep (se 1 (by rfl) ⟨1182329, by rfl⟩ : syracuseStep 1576439 = 2364659) B2364659
theorem B1773067 : Blo 1574485 1773067 := bstep (se 1 (by rfl) ⟨1329800, by rfl⟩ : syracuseStep 1773067 = 2659601) B2659601
theorem B1576459 : Blo 1574485 1576459 := bstep (se 1 (by rfl) ⟨1182344, by rfl⟩ : syracuseStep 1576459 = 2364689) B2364689
theorem B1576471 : Blo 1574485 1576471 := bstep (se 1 (by rfl) ⟨1182353, by rfl⟩ : syracuseStep 1576471 = 2364707) B2364707
theorem B2362955 : Blo 1574485 2362955 := bstep (se 1 (by rfl) ⟨1772216, by rfl⟩ : syracuseStep 2362955 = 3544433) B3544433
theorem B8973899 : Blo 1574485 8973899 := bstep (se 1 (by rfl) ⟨6730424, by rfl⟩ : syracuseStep 8973899 = 13460849) B13460849
theorem B3542615 : Blo 1574485 3542615 := bstep (se 1 (by rfl) ⟨2656961, by rfl⟩ : syracuseStep 3542615 = 5313923) B5313923
theorem B2362967 : Blo 1574485 2362967 := bstep (se 1 (by rfl) ⟨1772225, by rfl⟩ : syracuseStep 2362967 = 3544451) B3544451
theorem B1773175 : Blo 1574485 1773175 := bstep (se 1 (by rfl) ⟨1329881, by rfl⟩ : syracuseStep 1773175 = 2659763) B2659763
theorem B2363033 : Blo 1574485 2363033 := bstep (se 2 (by rfl) ⟨886137, by rfl⟩ : syracuseStep 2363033 = 1772275) B1772275
theorem B7573171 : Blo 1574485 7573171 := bstep (se 1 (by rfl) ⟨5679878, by rfl⟩ : syracuseStep 7573171 = 11359757) B11359757
theorem B2395865 : Blo 1574485 2395865 := bstep (se 2 (by rfl) ⟨898449, by rfl⟩ : syracuseStep 2395865 = 1796899) B1796899
theorem B30265073 : Blo 1574485 30265073 := bstep (se 2 (by rfl) ⟨11349402, by rfl⟩ : syracuseStep 30265073 = 22698805) B22698805
theorem B3542795 : Blo 1574485 3542795 := bstep (se 1 (by rfl) ⟨2657096, by rfl⟩ : syracuseStep 3542795 = 5314193) B5314193
theorem B2363147 : Blo 1574485 2363147 := bstep (se 1 (by rfl) ⟨1772360, by rfl⟩ : syracuseStep 2363147 = 3544721) B3544721
theorem B2363159 : Blo 1574485 2363159 := bstep (se 1 (by rfl) ⟨1772369, by rfl⟩ : syracuseStep 2363159 = 3544739) B3544739
theorem B1773355 : Blo 1574485 1773355 := bstep (se 1 (by rfl) ⟨1330016, by rfl⟩ : syracuseStep 1773355 = 2660033) B2660033
theorem B3542849 : Blo 1574485 3542849 := bstep (se 2 (by rfl) ⟨1328568, by rfl⟩ : syracuseStep 3542849 = 2657137) B2657137
theorem B5680961 : Blo 1574485 5680961 := bstep (se 2 (by rfl) ⟨2130360, by rfl⟩ : syracuseStep 5680961 = 4260721) B4260721
theorem B2363225 : Blo 1574485 2363225 := bstep (se 2 (by rfl) ⟨886209, by rfl⟩ : syracuseStep 2363225 = 1772419) B1772419
theorem B1994635 : Blo 1574485 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B1773463 : Blo 1574485 1773463 := bstep (se 1 (by rfl) ⟨1330097, by rfl⟩ : syracuseStep 1773463 = 2660195) B2660195
theorem B2158489 : Blo 1574485 2158489 := bstep (se 2 (by rfl) ⟨809433, by rfl⟩ : syracuseStep 2158489 = 1618867) B1618867
theorem B2658251 : Blo 1574485 2658251 := bstep (se 1 (by rfl) ⟨1993688, by rfl⟩ : syracuseStep 2658251 = 3987377) B3987377
theorem B2363339 : Blo 1574485 2363339 := bstep (se 1 (by rfl) ⟨1772504, by rfl⟩ : syracuseStep 2363339 = 3545009) B3545009
theorem B2363351 : Blo 1574485 2363351 := bstep (se 1 (by rfl) ⟨1772513, by rfl⟩ : syracuseStep 2363351 = 3545027) B3545027
theorem B57479129 : Blo 1574485 57479129 := bstep (se 2 (by rfl) ⟨21554673, by rfl⟩ : syracuseStep 57479129 = 43109347) B43109347
theorem B3543065 : Blo 1574485 3543065 := bstep (se 2 (by rfl) ⟨1328649, by rfl⟩ : syracuseStep 3543065 = 2657299) B2657299
theorem B2363417 : Blo 1574485 2363417 := bstep (se 2 (by rfl) ⟨886281, by rfl⟩ : syracuseStep 2363417 = 1772563) B1772563
theorem B5050433 : Blo 1574485 5050433 := bstep (se 2 (by rfl) ⟨1893912, by rfl⟩ : syracuseStep 5050433 = 3787825) B3787825
theorem B3985483 : Blo 1574485 3985483 := bstep (se 1 (by rfl) ⟨2989112, by rfl⟩ : syracuseStep 3985483 = 5978225) B5978225
theorem B2658379 : Blo 1574485 2658379 := bstep (se 1 (by rfl) ⟨1993784, by rfl⟩ : syracuseStep 2658379 = 3987569) B3987569
theorem B3543155 : Blo 1574485 3543155 := bstep (se 1 (by rfl) ⟨2657366, by rfl⟩ : syracuseStep 3543155 = 5314733) B5314733
theorem B2363531 : Blo 1574485 2363531 := bstep (se 1 (by rfl) ⟨1772648, by rfl⟩ : syracuseStep 2363531 = 3545297) B3545297
theorem B3543191 : Blo 1574485 3543191 := bstep (se 1 (by rfl) ⟨2657393, by rfl⟩ : syracuseStep 3543191 = 5314787) B5314787
theorem B2363543 : Blo 1574485 2363543 := bstep (se 1 (by rfl) ⟨1772657, by rfl⟩ : syracuseStep 2363543 = 3545315) B3545315
theorem B3985625 : Blo 1574485 3985625 := bstep (se 2 (by rfl) ⟨1494609, by rfl⟩ : syracuseStep 3985625 = 2989219) B2989219
theorem B2658521 : Blo 1574485 2658521 := bstep (se 2 (by rfl) ⟨996945, by rfl⟩ : syracuseStep 2658521 = 1993891) B1993891
theorem B2363609 : Blo 1574485 2363609 := bstep (se 2 (by rfl) ⟨886353, by rfl⟩ : syracuseStep 2363609 = 1772707) B1772707
theorem B3543371 : Blo 1574485 3543371 := bstep (se 1 (by rfl) ⟨2657528, by rfl⟩ : syracuseStep 3543371 = 5315057) B5315057
theorem B2363723 : Blo 1574485 2363723 := bstep (se 1 (by rfl) ⟨1772792, by rfl⟩ : syracuseStep 2363723 = 3545585) B3545585
theorem B2363735 : Blo 1574485 2363735 := bstep (se 1 (by rfl) ⟨1772801, by rfl⟩ : syracuseStep 2363735 = 3545603) B3545603
theorem B2658649 : Blo 1574485 2658649 := bstep (se 2 (by rfl) ⟨996993, by rfl⟩ : syracuseStep 2658649 = 1993987) B1993987
theorem B4485469 : Blo 1574485 4485469 := bstep (se 3 (by rfl) ⟨841025, by rfl⟩ : syracuseStep 4485469 = 1682051) B1682051
theorem B25555301 : Blo 1574485 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B3543425 : Blo 1574485 3543425 := bstep (se 2 (by rfl) ⟨1328784, by rfl⟩ : syracuseStep 3543425 = 2657569) B2657569
theorem B4485527 : Blo 1574485 4485527 := bstep (se 1 (by rfl) ⟨3364145, by rfl⟩ : syracuseStep 4485527 = 6728291) B6728291
theorem B2838937 : Blo 1574485 2838937 := bstep (se 2 (by rfl) ⟨1064601, by rfl⟩ : syracuseStep 2838937 = 2129203) B2129203
theorem B2363801 : Blo 1574485 2363801 := bstep (se 2 (by rfl) ⟨886425, by rfl⟩ : syracuseStep 2363801 = 1772851) B1772851
theorem B2363915 : Blo 1574485 2363915 := bstep (se 1 (by rfl) ⟨1772936, by rfl⟩ : syracuseStep 2363915 = 3545873) B3545873
theorem B2363927 : Blo 1574485 2363927 := bstep (se 1 (by rfl) ⟨1772945, by rfl⟩ : syracuseStep 2363927 = 3545891) B3545891
theorem B3543641 : Blo 1574485 3543641 := bstep (se 2 (by rfl) ⟨1328865, by rfl⟩ : syracuseStep 3543641 = 2657731) B2657731
theorem B2363993 : Blo 1574485 2363993 := bstep (se 2 (by rfl) ⟨886497, by rfl⟩ : syracuseStep 2363993 = 1772995) B1772995
theorem B6730391 : Blo 1574485 6730391 := bstep (se 1 (by rfl) ⟨5047793, by rfl⟩ : syracuseStep 6730391 = 10095587) B10095587
theorem B3543731 : Blo 1574485 3543731 := bstep (se 1 (by rfl) ⟨2657798, by rfl⟩ : syracuseStep 3543731 = 5315597) B5315597
theorem B2364107 : Blo 1574485 2364107 := bstep (se 1 (by rfl) ⟨1773080, by rfl⟩ : syracuseStep 2364107 = 3546161) B3546161
theorem B3543767 : Blo 1574485 3543767 := bstep (se 1 (by rfl) ⟨2657825, by rfl⟩ : syracuseStep 3543767 = 5315651) B5315651
theorem B2364119 : Blo 1574485 2364119 := bstep (se 1 (by rfl) ⟨1773089, by rfl⟩ : syracuseStep 2364119 = 3546179) B3546179
theorem B3592961 : Blo 1574485 3592961 := bstep (se 2 (by rfl) ⟨1347360, by rfl⟩ : syracuseStep 3592961 = 2694721) B2694721
theorem B2364185 : Blo 1574485 2364185 := bstep (se 2 (by rfl) ⟨886569, by rfl⟩ : syracuseStep 2364185 = 1773139) B1773139
theorem B11957057 : Blo 1574485 11957057 := bstep (se 2 (by rfl) ⟨4483896, by rfl⟩ : syracuseStep 11957057 = 8967793) B8967793
theorem B7975745 : Blo 1574485 7975745 := bstep (se 2 (by rfl) ⟨2990904, by rfl⟩ : syracuseStep 7975745 = 5981809) B5981809
theorem B7566155 : Blo 1574485 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B3543947 : Blo 1574485 3543947 := bstep (se 1 (by rfl) ⟨2657960, by rfl⟩ : syracuseStep 3543947 = 5315921) B5315921
theorem B2364299 : Blo 1574485 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B2659223 : Blo 1574485 2659223 := bstep (se 1 (by rfl) ⟨1994417, by rfl⟩ : syracuseStep 2659223 = 3988835) B3988835
theorem B2364311 : Blo 1574485 2364311 := bstep (se 1 (by rfl) ⟨1773233, by rfl⟩ : syracuseStep 2364311 = 3546467) B3546467
theorem B5985197 : Blo 1574485 5985197 := bstep (se 3 (by rfl) ⟨1122224, by rfl⟩ : syracuseStep 5985197 = 2244449) B2244449
theorem B45413297 : Blo 1574485 45413297 := bstep (se 2 (by rfl) ⟨17029986, by rfl⟩ : syracuseStep 45413297 = 34059973) B34059973
theorem B3544001 : Blo 1574485 3544001 := bstep (se 2 (by rfl) ⟨1329000, by rfl⟩ : syracuseStep 3544001 = 2658001) B2658001
theorem B2364377 : Blo 1574485 2364377 := bstep (se 2 (by rfl) ⟨886641, by rfl⟩ : syracuseStep 2364377 = 1773283) B1773283
theorem B3986455 : Blo 1574485 3986455 := bstep (se 1 (by rfl) ⟨2989841, by rfl⟩ : syracuseStep 3986455 = 5979683) B5979683
theorem B2659351 : Blo 1574485 2659351 := bstep (se 1 (by rfl) ⟨1994513, by rfl⟩ : syracuseStep 2659351 = 3989027) B3989027
theorem B7574573 : Blo 1574485 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B2364491 : Blo 1574485 2364491 := bstep (se 1 (by rfl) ⟨1773368, by rfl⟩ : syracuseStep 2364491 = 3546737) B3546737
theorem B2364503 : Blo 1574485 2364503 := bstep (se 1 (by rfl) ⟨1773377, by rfl⟩ : syracuseStep 2364503 = 3546755) B3546755
theorem B3544217 : Blo 1574485 3544217 := bstep (se 2 (by rfl) ⟨1329081, by rfl⟩ : syracuseStep 3544217 = 2658163) B2658163
theorem B2364569 : Blo 1574485 2364569 := bstep (se 2 (by rfl) ⟨886713, by rfl⟩ : syracuseStep 2364569 = 1773427) B1773427
theorem B3544307 : Blo 1574485 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B2364683 : Blo 1574485 2364683 := bstep (se 1 (by rfl) ⟨1773512, by rfl⟩ : syracuseStep 2364683 = 3547025) B3547025
theorem B3544343 : Blo 1574485 3544343 := bstep (se 1 (by rfl) ⟨2658257, by rfl⟩ : syracuseStep 3544343 = 5316515) B5316515
theorem B2364695 : Blo 1574485 2364695 := bstep (se 1 (by rfl) ⟨1773521, by rfl⟩ : syracuseStep 2364695 = 3547043) B3547043
theorem B2495831 : Blo 1574485 2495831 := bstep (se 1 (by rfl) ⟨1871873, by rfl⟩ : syracuseStep 2495831 = 3743747) B3743747
theorem B3986891 : Blo 1574485 3986891 := bstep (se 1 (by rfl) ⟨2990168, by rfl⟩ : syracuseStep 3986891 = 5980337) B5980337
theorem B3544523 : Blo 1574485 3544523 := bstep (se 1 (by rfl) ⟨2658392, by rfl⟩ : syracuseStep 3544523 = 5316785) B5316785
theorem B3544577 : Blo 1574485 3544577 := bstep (se 2 (by rfl) ⟨1329216, by rfl⟩ : syracuseStep 3544577 = 2658433) B2658433
theorem B4486745 : Blo 1574485 4486745 := bstep (se 2 (by rfl) ⟨1682529, by rfl⟩ : syracuseStep 4486745 = 3365059) B3365059
theorem B2659979 : Blo 1574485 2659979 := bstep (se 1 (by rfl) ⟨1994984, by rfl⟩ : syracuseStep 2659979 = 3989969) B3989969
theorem B2242199 : Blo 1574485 2242199 := bstep (se 1 (by rfl) ⟨1681649, by rfl⟩ : syracuseStep 2242199 = 3363299) B3363299
theorem B4486859 : Blo 1574485 4486859 := bstep (se 1 (by rfl) ⟨3365144, by rfl⟩ : syracuseStep 4486859 = 6730289) B6730289
theorem B3544793 : Blo 1574485 3544793 := bstep (se 2 (by rfl) ⟨1329297, by rfl⟩ : syracuseStep 3544793 = 2658595) B2658595
theorem B2660107 : Blo 1574485 2660107 := bstep (se 1 (by rfl) ⟨1995080, by rfl⟩ : syracuseStep 2660107 = 3990161) B3990161
theorem B5314355 : Blo 1574485 5314355 := bstep (se 1 (by rfl) ⟨3985766, by rfl⟩ : syracuseStep 5314355 = 7971533) B7971533
theorem B3544883 : Blo 1574485 3544883 := bstep (se 1 (by rfl) ⟨2658662, by rfl⟩ : syracuseStep 3544883 = 5317325) B5317325
theorem B5674817 : Blo 1574485 5674817 := bstep (se 2 (by rfl) ⟨2128056, by rfl⟩ : syracuseStep 5674817 = 4256113) B4256113
theorem B3987265 : Blo 1574485 3987265 := bstep (se 2 (by rfl) ⟨1495224, by rfl⟩ : syracuseStep 3987265 = 2990449) B2990449
theorem B3544919 : Blo 1574485 3544919 := bstep (se 1 (by rfl) ⟨2658689, by rfl⟩ : syracuseStep 3544919 = 5317379) B5317379
theorem B4257629 : Blo 1574485 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B8968067 : Blo 1574485 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B12121987 : Blo 1574485 12121987 := bstep (se 1 (by rfl) ⟨9091490, by rfl⟩ : syracuseStep 12121987 = 18182981) B18182981
theorem B2660249 : Blo 1574485 2660249 := bstep (se 2 (by rfl) ⟨997593, by rfl⟩ : syracuseStep 2660249 = 1995187) B1995187
theorem B2242507 : Blo 1574485 2242507 := bstep (se 1 (by rfl) ⟨1681880, by rfl⟩ : syracuseStep 2242507 = 3363761) B3363761
theorem B6731723 : Blo 1574485 6731723 := bstep (se 1 (by rfl) ⟨5048792, by rfl⟩ : syracuseStep 6731723 = 10097585) B10097585
theorem B3545099 : Blo 1574485 3545099 := bstep (se 1 (by rfl) ⟨2658824, by rfl⟩ : syracuseStep 3545099 = 5317649) B5317649
theorem B5314625 : Blo 1574485 5314625 := bstep (se 2 (by rfl) ⟨1992984, by rfl⟩ : syracuseStep 5314625 = 3985969) B3985969
theorem B3545153 : Blo 1574485 3545153 := bstep (se 2 (by rfl) ⟨1329432, by rfl⟩ : syracuseStep 3545153 = 2658865) B2658865
theorem B3364939 : Blo 1574485 3364939 := bstep (se 1 (by rfl) ⟨2523704, by rfl⟩ : syracuseStep 3364939 = 5047409) B5047409
theorem B13457501 : Blo 1574485 13457501 := bstep (se 3 (by rfl) ⟨2523281, by rfl⟩ : syracuseStep 13457501 = 5046563) B5046563
theorem B4790465 : Blo 1574485 4790465 := bstep (se 2 (by rfl) ⟨1796424, by rfl⟩ : syracuseStep 4790465 = 3592849) B3592849
theorem B7190731 : Blo 1574485 7190731 := bstep (se 1 (by rfl) ⟨5393048, by rfl⟩ : syracuseStep 7190731 = 10786097) B10786097
theorem B3545369 : Blo 1574485 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B10099019 : Blo 1574485 10099019 := bstep (se 1 (by rfl) ⟨7574264, by rfl⟩ : syracuseStep 10099019 = 15148529) B15148529
theorem B3545459 : Blo 1574485 3545459 := bstep (se 1 (by rfl) ⟨2659094, by rfl⟩ : syracuseStep 3545459 = 5318189) B5318189
theorem B3987863 : Blo 1574485 3987863 := bstep (se 1 (by rfl) ⟨2990897, by rfl⟩ : syracuseStep 3987863 = 5981795) B5981795
theorem B3545495 : Blo 1574485 3545495 := bstep (se 1 (by rfl) ⟨2659121, by rfl⟩ : syracuseStep 3545495 = 5318243) B5318243
theorem B6732305 : Blo 1574485 6732305 := bstep (se 2 (by rfl) ⟨2524614, by rfl⟩ : syracuseStep 6732305 = 5049229) B5049229
theorem B3365401 : Blo 1574485 3365401 := bstep (se 2 (by rfl) ⟨1262025, by rfl⟩ : syracuseStep 3365401 = 2524051) B2524051
theorem B3545675 : Blo 1574485 3545675 := bstep (se 1 (by rfl) ⟨2659256, by rfl⟩ : syracuseStep 3545675 = 5318513) B5318513
theorem B5315165 : Blo 1574485 5315165 := bstep (se 3 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 5315165 = 1993187) B1993187
theorem B8632925 : Blo 1574485 8632925 := bstep (se 3 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 8632925 = 3237347) B3237347
theorem B3545729 : Blo 1574485 3545729 := bstep (se 2 (by rfl) ⟨1329648, by rfl⟩ : syracuseStep 3545729 = 2659297) B2659297
theorem B3783385 : Blo 1574485 3783385 := bstep (se 2 (by rfl) ⟨1418769, by rfl⟩ : syracuseStep 3783385 = 2837539) B2837539
theorem B11959001 : Blo 1574485 11959001 := bstep (se 2 (by rfl) ⟨4484625, by rfl⟩ : syracuseStep 11959001 = 8969251) B8969251
theorem B5675741 : Blo 1574485 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B7977689 : Blo 1574485 7977689 := bstep (se 2 (by rfl) ⟨2991633, by rfl⟩ : syracuseStep 7977689 = 5983267) B5983267
theorem B4487987 : Blo 1574485 4487987 := bstep (se 1 (by rfl) ⟨3365990, by rfl⟩ : syracuseStep 4487987 = 6731981) B6731981
theorem B24263489 : Blo 1574485 24263489 := bstep (se 2 (by rfl) ⟨9098808, by rfl⟩ : syracuseStep 24263489 = 18197617) B18197617
theorem B13458251 : Blo 1574485 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B3545945 : Blo 1574485 3545945 := bstep (se 2 (by rfl) ⟨1329729, by rfl⟩ : syracuseStep 3545945 = 2659459) B2659459
theorem B3546035 : Blo 1574485 3546035 := bstep (se 1 (by rfl) ⟨2659526, by rfl⟩ : syracuseStep 3546035 = 5319053) B5319053
theorem B3783617 : Blo 1574485 3783617 := bstep (se 2 (by rfl) ⟨1418856, by rfl⟩ : syracuseStep 3783617 = 2837713) B2837713
theorem B2243543 : Blo 1574485 2243543 := bstep (se 1 (by rfl) ⟨1682657, by rfl⟩ : syracuseStep 2243543 = 3365315) B3365315
theorem B3546071 : Blo 1574485 3546071 := bstep (se 1 (by rfl) ⟨2659553, by rfl⟩ : syracuseStep 3546071 = 5319107) B5319107
theorem B10091537 : Blo 1574485 10091537 := bstep (se 2 (by rfl) ⟨3784326, by rfl⟩ : syracuseStep 10091537 = 7568653) B7568653
theorem B2522135 : Blo 1574485 2522135 := bstep (se 1 (by rfl) ⟨1891601, by rfl⟩ : syracuseStep 2522135 = 3783203) B3783203
theorem B4545629 : Blo 1574485 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B3546251 : Blo 1574485 3546251 := bstep (se 1 (by rfl) ⟨2659688, by rfl⟩ : syracuseStep 3546251 = 5319377) B5319377
theorem B5045399 : Blo 1574485 5045399 := bstep (se 1 (by rfl) ⟨3784049, by rfl⟩ : syracuseStep 5045399 = 7568099) B7568099
theorem B2243737 : Blo 1574485 2243737 := bstep (se 2 (by rfl) ⟨841401, by rfl⟩ : syracuseStep 2243737 = 1682803) B1682803
theorem B3988673 : Blo 1574485 3988673 := bstep (se 2 (by rfl) ⟨1495752, by rfl⟩ : syracuseStep 3988673 = 2991505) B2991505
theorem B3546305 : Blo 1574485 3546305 := bstep (se 2 (by rfl) ⟨1329864, by rfl⟩ : syracuseStep 3546305 = 2659729) B2659729
theorem B4488385 : Blo 1574485 4488385 := bstep (se 2 (by rfl) ⟨1683144, by rfl⟩ : syracuseStep 4488385 = 3366289) B3366289
theorem B11967749 : Blo 1574485 11967749 := bstep (se 4 (by rfl) ⟨1121976, by rfl⟩ : syracuseStep 11967749 = 2243953) B2243953
theorem B17038637 : Blo 1574485 17038637 := bstep (se 3 (by rfl) ⟨3194744, by rfl⟩ : syracuseStep 17038637 = 6389489) B6389489
theorem B2522443 : Blo 1574485 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B5676419 : Blo 1574485 5676419 := bstep (se 1 (by rfl) ⟨4257314, by rfl⟩ : syracuseStep 5676419 = 8514629) B8514629
theorem B36371861 : Blo 1574485 36371861 := bstep (se 6 (by rfl) ⟨852465, by rfl⟩ : syracuseStep 36371861 = 1704931) B1704931
theorem B3546521 : Blo 1574485 3546521 := bstep (se 2 (by rfl) ⟨1329945, by rfl⟩ : syracuseStep 3546521 = 2659891) B2659891
theorem B6823361 : Blo 1574485 6823361 := bstep (se 2 (by rfl) ⟨2558760, by rfl⟩ : syracuseStep 6823361 = 5117521) B5117521
theorem B3546611 : Blo 1574485 3546611 := bstep (se 1 (by rfl) ⟨2659958, by rfl⟩ : syracuseStep 3546611 = 5319917) B5319917
theorem B5676547 : Blo 1574485 5676547 := bstep (se 1 (by rfl) ⟨4257410, by rfl⟩ : syracuseStep 5676547 = 8514821) B8514821
theorem B3546647 : Blo 1574485 3546647 := bstep (se 1 (by rfl) ⟨2659985, by rfl⟩ : syracuseStep 3546647 = 5319971) B5319971
theorem B6733363 : Blo 1574485 6733363 := bstep (se 1 (by rfl) ⟨5050022, by rfl⟩ : syracuseStep 6733363 = 10100045) B10100045
theorem B5979851 : Blo 1574485 5979851 := bstep (se 1 (by rfl) ⟨4484888, by rfl⟩ : syracuseStep 5979851 = 8969777) B8969777
theorem B5316299 : Blo 1574485 5316299 := bstep (se 1 (by rfl) ⟨3987224, by rfl⟩ : syracuseStep 5316299 = 7974449) B7974449
theorem B3546827 : Blo 1574485 3546827 := bstep (se 1 (by rfl) ⟨2660120, by rfl⟩ : syracuseStep 3546827 = 5320241) B5320241
theorem B40402637 : Blo 1574485 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B5979865 : Blo 1574485 5979865 := bstep (se 2 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 5979865 = 4484899) B4484899
theorem B3989209 : Blo 1574485 3989209 := bstep (se 2 (by rfl) ⟨1495953, by rfl⟩ : syracuseStep 3989209 = 2991907) B2991907
theorem B2989811 : Blo 1574485 2989811 := bstep (se 1 (by rfl) ⟨2242358, by rfl⟩ : syracuseStep 2989811 = 4484717) B4484717
theorem B3546881 : Blo 1574485 3546881 := bstep (se 2 (by rfl) ⟨1330080, by rfl⟩ : syracuseStep 3546881 = 2660161) B2660161
theorem B3366785 : Blo 1574485 3366785 := bstep (se 2 (by rfl) ⟨1262544, by rfl⟩ : syracuseStep 3366785 = 2525089) B2525089
theorem B2989963 : Blo 1574485 2989963 := bstep (se 1 (by rfl) ⟨2242472, by rfl⟩ : syracuseStep 2989963 = 4484945) B4484945
theorem B5316569 : Blo 1574485 5316569 := bstep (se 2 (by rfl) ⟨1993713, by rfl⟩ : syracuseStep 5316569 = 3987427) B3987427
theorem B3366955 : Blo 1574485 3366955 := bstep (se 1 (by rfl) ⟨2525216, by rfl⟩ : syracuseStep 3366955 = 5050433) B5050433
theorem B6725693 : Blo 1574485 6725693 := bstep (se 3 (by rfl) ⟨1261067, by rfl⟩ : syracuseStep 6725693 = 2522135) B2522135
theorem B2990351 : Blo 1574485 2990351 := bstep (se 1 (by rfl) ⟨2242763, by rfl⟩ : syracuseStep 2990351 = 4485527) B4485527
theorem B53199197 : Blo 1574485 53199197 := bstep (se 3 (by rfl) ⟨9974849, by rfl⟩ : syracuseStep 53199197 = 19949699) B19949699
theorem B36397457 : Blo 1574485 36397457 := bstep (se 2 (by rfl) ⟨13649046, by rfl⟩ : syracuseStep 36397457 = 27298093) B27298093
theorem B38306195 : Blo 1574485 38306195 := bstep (se 1 (by rfl) ⟨28729646, by rfl⟩ : syracuseStep 38306195 = 57459293) B57459293
theorem B5980625 : Blo 1574485 5980625 := bstep (se 2 (by rfl) ⟨2242734, by rfl⟩ : syracuseStep 5980625 = 4485469) B4485469
theorem B11362781 : Blo 1574485 11362781 := bstep (se 3 (by rfl) ⟨2130521, by rfl⟩ : syracuseStep 11362781 = 4261043) B4261043
theorem B3785231 : Blo 1574485 3785231 := bstep (se 1 (by rfl) ⟨2838923, by rfl⟩ : syracuseStep 3785231 = 5677847) B5677847
theorem B3785249 : Blo 1574485 3785249 := bstep (se 2 (by rfl) ⟨1419468, by rfl⟩ : syracuseStep 3785249 = 2838937) B2838937
theorem B7971371 : Blo 1574485 7971371 := bstep (se 1 (by rfl) ⟨5978528, by rfl⟩ : syracuseStep 7971371 = 11957057) B11957057
theorem B5317163 : Blo 1574485 5317163 := bstep (se 1 (by rfl) ⟨3987872, by rfl⟩ : syracuseStep 5317163 = 7975745) B7975745
theorem B3195451 : Blo 1574485 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B3990131 : Blo 1574485 3990131 := bstep (se 1 (by rfl) ⟨2992598, by rfl⟩ : syracuseStep 3990131 = 5985197) B5985197
theorem B6824989 : Blo 1574485 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B2991163 : Blo 1574485 2991163 := bstep (se 1 (by rfl) ⟨2243372, by rfl⟩ : syracuseStep 2991163 = 4486745) B4486745
theorem B11961431 : Blo 1574485 11961431 := bstep (se 1 (by rfl) ⟨8971073, by rfl⟩ : syracuseStep 11961431 = 17942147) B17942147
theorem B7980119 : Blo 1574485 7980119 := bstep (se 1 (by rfl) ⟨5985089, by rfl⟩ : syracuseStep 7980119 = 11970179) B11970179
theorem B2991239 : Blo 1574485 2991239 := bstep (se 1 (by rfl) ⟨2243429, by rfl⟩ : syracuseStep 2991239 = 4486859) B4486859
theorem B8971667 : Blo 1574485 8971667 := bstep (se 1 (by rfl) ⟨6728750, by rfl⟩ : syracuseStep 8971667 = 13457501) B13457501
theorem B2991649 : Blo 1574485 2991649 := bstep (se 2 (by rfl) ⟨1121868, by rfl⟩ : syracuseStep 2991649 = 2243737) B2243737
theorem B7980605 : Blo 1574485 7980605 := bstep (se 3 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 7980605 = 2992727) B2992727
theorem B1574535 : Blo 1574485 1574535 := bstep (se 1 (by rfl) ⟨1180901, by rfl⟩ : syracuseStep 1574535 = 2361803) B2361803
theorem B1574543 : Blo 1574485 1574543 := bstep (se 1 (by rfl) ⟨1180907, by rfl⟩ : syracuseStep 1574543 = 2361815) B2361815
theorem B1574587 : Blo 1574485 1574587 := bstep (se 1 (by rfl) ⟨1180940, by rfl⟩ : syracuseStep 1574587 = 2361881) B2361881
theorem B1574663 : Blo 1574485 1574663 := bstep (se 1 (by rfl) ⟨1180997, by rfl⟩ : syracuseStep 1574663 = 2361995) B2361995
theorem B1574671 : Blo 1574485 1574671 := bstep (se 1 (by rfl) ⟨1181003, by rfl⟩ : syracuseStep 1574671 = 2362007) B2362007
theorem B1574715 : Blo 1574485 1574715 := bstep (se 1 (by rfl) ⟨1181036, by rfl⟩ : syracuseStep 1574715 = 2362073) B2362073
theorem B7972667 : Blo 1574485 7972667 := bstep (se 1 (by rfl) ⟨5979500, by rfl⟩ : syracuseStep 7972667 = 11959001) B11959001
theorem B5318459 : Blo 1574485 5318459 := bstep (se 1 (by rfl) ⟨3988844, by rfl⟩ : syracuseStep 5318459 = 7977689) B7977689
theorem B2991991 : Blo 1574485 2991991 := bstep (se 1 (by rfl) ⟨2243993, by rfl⟩ : syracuseStep 2991991 = 4487987) B4487987
theorem B1574791 : Blo 1574485 1574791 := bstep (se 1 (by rfl) ⟨1181093, by rfl⟩ : syracuseStep 1574791 = 2362187) B2362187
theorem B8972167 : Blo 1574485 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B1574799 : Blo 1574485 1574799 := bstep (se 1 (by rfl) ⟨1181099, by rfl⟩ : syracuseStep 1574799 = 2362199) B2362199
theorem B26904473 : Blo 1574485 26904473 := bstep (se 2 (by rfl) ⟨10089177, by rfl⟩ : syracuseStep 26904473 = 20178355) B20178355
theorem B1574843 : Blo 1574485 1574843 := bstep (se 1 (by rfl) ⟨1181132, by rfl⟩ : syracuseStep 1574843 = 2362265) B2362265
theorem B7972829 : Blo 1574485 7972829 := bstep (se 3 (by rfl) ⟨1494905, by rfl⟩ : syracuseStep 7972829 = 2989811) B2989811
theorem B1574919 : Blo 1574485 1574919 := bstep (se 1 (by rfl) ⟨1181189, by rfl⟩ : syracuseStep 1574919 = 2362379) B2362379
theorem B6727691 : Blo 1574485 6727691 := bstep (se 1 (by rfl) ⟨5045768, by rfl⟩ : syracuseStep 6727691 = 10091537) B10091537
theorem B1574927 : Blo 1574485 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B1574971 : Blo 1574485 1574971 := bstep (se 1 (by rfl) ⟨1181228, by rfl⟩ : syracuseStep 1574971 = 2362457) B2362457
theorem B5982295 : Blo 1574485 5982295 := bstep (se 1 (by rfl) ⟨4486721, by rfl⟩ : syracuseStep 5982295 = 8973443) B8973443
theorem B1575047 : Blo 1574485 1575047 := bstep (se 1 (by rfl) ⟨1181285, by rfl⟩ : syracuseStep 1575047 = 2362571) B2362571
theorem B1771663 : Blo 1574485 1771663 := bstep (se 1 (by rfl) ⟨1328747, by rfl⟩ : syracuseStep 1771663 = 2657495) B2657495
theorem B1575055 : Blo 1574485 1575055 := bstep (se 1 (by rfl) ⟨1181291, by rfl⟩ : syracuseStep 1575055 = 2362583) B2362583
theorem B15132845 : Blo 1574485 15132845 := bstep (se 3 (by rfl) ⟨2837408, by rfl⟩ : syracuseStep 15132845 = 5674817) B5674817
theorem B64702637 : Blo 1574485 64702637 := bstep (se 3 (by rfl) ⟨12131744, by rfl⟩ : syracuseStep 64702637 = 24263489) B24263489
theorem B1575099 : Blo 1574485 1575099 := bstep (se 1 (by rfl) ⟨1181324, by rfl⟩ : syracuseStep 1575099 = 2362649) B2362649
theorem B1575175 : Blo 1574485 1575175 := bstep (se 1 (by rfl) ⟨1181381, by rfl⟩ : syracuseStep 1575175 = 2362763) B2362763
theorem B3787019 : Blo 1574485 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B1575183 : Blo 1574485 1575183 := bstep (se 1 (by rfl) ⟨1181387, by rfl⟩ : syracuseStep 1575183 = 2362775) B2362775
theorem B7973153 : Blo 1574485 7973153 := bstep (se 2 (by rfl) ⟨2989932, by rfl⟩ : syracuseStep 7973153 = 5979865) B5979865
theorem B3410209 : Blo 1574485 3410209 := bstep (se 2 (by rfl) ⟨1278828, by rfl⟩ : syracuseStep 3410209 = 2557657) B2557657
theorem B5318945 : Blo 1574485 5318945 := bstep (se 2 (by rfl) ⟨1994604, by rfl⟩ : syracuseStep 5318945 = 3989209) B3989209
theorem B4548907 : Blo 1574485 4548907 := bstep (se 1 (by rfl) ⟨3411680, by rfl⟩ : syracuseStep 4548907 = 6823361) B6823361
theorem B1575227 : Blo 1574485 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B2558267 : Blo 1574485 2558267 := bstep (se 1 (by rfl) ⟨1918700, by rfl⟩ : syracuseStep 2558267 = 3837401) B3837401
theorem B1575303 : Blo 1574485 1575303 := bstep (se 1 (by rfl) ⟨1181477, by rfl⟩ : syracuseStep 1575303 = 2362955) B2362955
theorem B5982599 : Blo 1574485 5982599 := bstep (se 1 (by rfl) ⟨4486949, by rfl⟩ : syracuseStep 5982599 = 8973899) B8973899
theorem B2361743 : Blo 1574485 2361743 := bstep (se 1 (by rfl) ⟨1771307, by rfl⟩ : syracuseStep 2361743 = 3542615) B3542615
theorem B1575311 : Blo 1574485 1575311 := bstep (se 1 (by rfl) ⟨1181483, by rfl⟩ : syracuseStep 1575311 = 2362967) B2362967
theorem B2361785 : Blo 1574485 2361785 := bstep (se 2 (by rfl) ⟨885669, by rfl⟩ : syracuseStep 2361785 = 1771339) B1771339
theorem B1575355 : Blo 1574485 1575355 := bstep (se 1 (by rfl) ⟨1181516, by rfl⟩ : syracuseStep 1575355 = 2363033) B2363033
theorem B2361863 : Blo 1574485 2361863 := bstep (se 1 (by rfl) ⟨1771397, by rfl⟩ : syracuseStep 2361863 = 3542795) B3542795
theorem B1575431 : Blo 1574485 1575431 := bstep (se 1 (by rfl) ⟨1181573, by rfl⟩ : syracuseStep 1575431 = 2363147) B2363147
theorem B1575439 : Blo 1574485 1575439 := bstep (se 1 (by rfl) ⟨1181579, by rfl⟩ : syracuseStep 1575439 = 2363159) B2363159
theorem B4483613 : Blo 1574485 4483613 := bstep (se 3 (by rfl) ⟨840677, by rfl⟩ : syracuseStep 4483613 = 1681355) B1681355
theorem B2877985 : Blo 1574485 2877985 := bstep (se 2 (by rfl) ⟨1079244, by rfl⟩ : syracuseStep 2877985 = 2158489) B2158489
theorem B2361899 : Blo 1574485 2361899 := bstep (se 1 (by rfl) ⟨1771424, by rfl⟩ : syracuseStep 2361899 = 3542849) B3542849
theorem B3787307 : Blo 1574485 3787307 := bstep (se 1 (by rfl) ⟨2840480, by rfl⟩ : syracuseStep 3787307 = 5680961) B5680961
theorem B1575483 : Blo 1574485 1575483 := bstep (se 1 (by rfl) ⟨1181612, by rfl⟩ : syracuseStep 1575483 = 2363225) B2363225
theorem B5982781 : Blo 1574485 5982781 := bstep (se 3 (by rfl) ⟨1121771, by rfl⟩ : syracuseStep 5982781 = 2243543) B2243543
theorem B2361929 : Blo 1574485 2361929 := bstep (se 2 (by rfl) ⟨885723, by rfl⟩ : syracuseStep 2361929 = 1771447) B1771447
theorem B1772167 : Blo 1574485 1772167 := bstep (se 1 (by rfl) ⟨1329125, by rfl⟩ : syracuseStep 1772167 = 2658251) B2658251
theorem B1575559 : Blo 1574485 1575559 := bstep (se 1 (by rfl) ⟨1181669, by rfl⟩ : syracuseStep 1575559 = 2363339) B2363339
theorem B1575567 : Blo 1574485 1575567 := bstep (se 1 (by rfl) ⟨1181675, by rfl⟩ : syracuseStep 1575567 = 2363351) B2363351
theorem B2362043 : Blo 1574485 2362043 := bstep (se 1 (by rfl) ⟨1771532, by rfl⟩ : syracuseStep 2362043 = 3543065) B3543065
theorem B1575611 : Blo 1574485 1575611 := bstep (se 1 (by rfl) ⟨1181708, by rfl⟩ : syracuseStep 1575611 = 2363417) B2363417
theorem B2362103 : Blo 1574485 2362103 := bstep (se 1 (by rfl) ⟨1771577, by rfl⟩ : syracuseStep 2362103 = 3543155) B3543155
theorem B1575687 : Blo 1574485 1575687 := bstep (se 1 (by rfl) ⟨1181765, by rfl⟩ : syracuseStep 1575687 = 2363531) B2363531
theorem B2362127 : Blo 1574485 2362127 := bstep (se 1 (by rfl) ⟨1771595, by rfl⟩ : syracuseStep 2362127 = 3543191) B3543191
theorem B1575695 : Blo 1574485 1575695 := bstep (se 1 (by rfl) ⟨1181771, by rfl⟩ : syracuseStep 1575695 = 2363543) B2363543
theorem B18197297 : Blo 1574485 18197297 := bstep (se 2 (by rfl) ⟨6823986, by rfl⟩ : syracuseStep 18197297 = 13647973) B13647973
theorem B2362169 : Blo 1574485 2362169 := bstep (se 2 (by rfl) ⟨885813, by rfl⟩ : syracuseStep 2362169 = 1771627) B1771627
theorem B2657083 : Blo 1574485 2657083 := bstep (se 1 (by rfl) ⟨1992812, by rfl⟩ : syracuseStep 2657083 = 3985625) B3985625
theorem B1772347 : Blo 1574485 1772347 := bstep (se 1 (by rfl) ⟨1329260, by rfl⟩ : syracuseStep 1772347 = 2658521) B2658521
theorem B1575739 : Blo 1574485 1575739 := bstep (se 1 (by rfl) ⟨1181804, by rfl⟩ : syracuseStep 1575739 = 2363609) B2363609
theorem B5319539 : Blo 1574485 5319539 := bstep (se 1 (by rfl) ⟨3989654, by rfl⟩ : syracuseStep 5319539 = 7979309) B7979309
theorem B2362247 : Blo 1574485 2362247 := bstep (se 1 (by rfl) ⟨1771685, by rfl⟩ : syracuseStep 2362247 = 3543371) B3543371
theorem B1575815 : Blo 1574485 1575815 := bstep (se 1 (by rfl) ⟨1181861, by rfl⟩ : syracuseStep 1575815 = 2363723) B2363723
theorem B1575823 : Blo 1574485 1575823 := bstep (se 1 (by rfl) ⟨1181867, by rfl⟩ : syracuseStep 1575823 = 2363735) B2363735
theorem B2362283 : Blo 1574485 2362283 := bstep (se 1 (by rfl) ⟨1771712, by rfl⟩ : syracuseStep 2362283 = 3543425) B3543425
theorem B1575867 : Blo 1574485 1575867 := bstep (se 1 (by rfl) ⟨1181900, by rfl⟩ : syracuseStep 1575867 = 2363801) B2363801
theorem B9587641 : Blo 1574485 9587641 := bstep (se 2 (by rfl) ⟨3595365, by rfl⟩ : syracuseStep 9587641 = 7190731) B7190731
theorem B2657225 : Blo 1574485 2657225 := bstep (se 2 (by rfl) ⟨996459, by rfl⟩ : syracuseStep 2657225 = 1992919) B1992919
theorem B2362313 : Blo 1574485 2362313 := bstep (se 2 (by rfl) ⟨885867, by rfl⟩ : syracuseStep 2362313 = 1771735) B1771735
theorem B1575943 : Blo 1574485 1575943 := bstep (se 1 (by rfl) ⟨1181957, by rfl⟩ : syracuseStep 1575943 = 2363915) B2363915
theorem B68103179 : Blo 1574485 68103179 := bstep (se 1 (by rfl) ⟨51077384, by rfl⟩ : syracuseStep 68103179 = 102154769) B102154769
theorem B1575951 : Blo 1574485 1575951 := bstep (se 1 (by rfl) ⟨1181963, by rfl⟩ : syracuseStep 1575951 = 2363927) B2363927
theorem B2362427 : Blo 1574485 2362427 := bstep (se 1 (by rfl) ⟨1771820, by rfl⟩ : syracuseStep 2362427 = 3543641) B3543641
theorem B1575995 : Blo 1574485 1575995 := bstep (se 1 (by rfl) ⟨1181996, by rfl⟩ : syracuseStep 1575995 = 2363993) B2363993
theorem B2362487 : Blo 1574485 2362487 := bstep (se 1 (by rfl) ⟨1771865, by rfl⟩ : syracuseStep 2362487 = 3543731) B3543731
theorem B1576071 : Blo 1574485 1576071 := bstep (se 1 (by rfl) ⟨1182053, by rfl⟩ : syracuseStep 1576071 = 2364107) B2364107
theorem B2362511 : Blo 1574485 2362511 := bstep (se 1 (by rfl) ⟨1771883, by rfl⟩ : syracuseStep 2362511 = 3543767) B3543767
theorem B1576079 : Blo 1574485 1576079 := bstep (se 1 (by rfl) ⟨1182059, by rfl⟩ : syracuseStep 1576079 = 2364119) B2364119
theorem B2395307 : Blo 1574485 2395307 := bstep (se 1 (by rfl) ⟨1796480, by rfl⟩ : syracuseStep 2395307 = 3592961) B3592961
theorem B2362553 : Blo 1574485 2362553 := bstep (se 2 (by rfl) ⟨885957, by rfl⟩ : syracuseStep 2362553 = 1771915) B1771915
theorem B1576123 : Blo 1574485 1576123 := bstep (se 1 (by rfl) ⟨1182092, by rfl⟩ : syracuseStep 1576123 = 2364185) B2364185
theorem B7974125 : Blo 1574485 7974125 := bstep (se 3 (by rfl) ⟨1495148, by rfl⟩ : syracuseStep 7974125 = 2990297) B2990297
theorem B2362631 : Blo 1574485 2362631 := bstep (se 1 (by rfl) ⟨1771973, by rfl⟩ : syracuseStep 2362631 = 3543947) B3543947
theorem B1576199 : Blo 1574485 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B1772815 : Blo 1574485 1772815 := bstep (se 1 (by rfl) ⟨1329611, by rfl⟩ : syracuseStep 1772815 = 2659223) B2659223
theorem B1797391 : Blo 1574485 1797391 := bstep (se 1 (by rfl) ⟨1348043, by rfl⟩ : syracuseStep 1797391 = 2696087) B2696087
theorem B1576207 : Blo 1574485 1576207 := bstep (se 1 (by rfl) ⟨1182155, by rfl⟩ : syracuseStep 1576207 = 2364311) B2364311
theorem B2362667 : Blo 1574485 2362667 := bstep (se 1 (by rfl) ⟨1772000, by rfl⟩ : syracuseStep 2362667 = 3544001) B3544001
theorem B1576251 : Blo 1574485 1576251 := bstep (se 1 (by rfl) ⟨1182188, by rfl⟩ : syracuseStep 1576251 = 2364377) B2364377
theorem B2362697 : Blo 1574485 2362697 := bstep (se 2 (by rfl) ⟨886011, by rfl⟩ : syracuseStep 2362697 = 1772023) B1772023
theorem B5049715 : Blo 1574485 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B1576327 : Blo 1574485 1576327 := bstep (se 1 (by rfl) ⟨1182245, by rfl⟩ : syracuseStep 1576327 = 2364491) B2364491
theorem B1576335 : Blo 1574485 1576335 := bstep (se 1 (by rfl) ⟨1182251, by rfl⟩ : syracuseStep 1576335 = 2364503) B2364503
theorem B2362811 : Blo 1574485 2362811 := bstep (se 1 (by rfl) ⟨1772108, by rfl⟩ : syracuseStep 2362811 = 3544217) B3544217
theorem B1576379 : Blo 1574485 1576379 := bstep (se 1 (by rfl) ⟨1182284, by rfl⟩ : syracuseStep 1576379 = 2364569) B2364569
theorem B2362871 : Blo 1574485 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B1576455 : Blo 1574485 1576455 := bstep (se 1 (by rfl) ⟨1182341, by rfl⟩ : syracuseStep 1576455 = 2364683) B2364683
theorem B2362895 : Blo 1574485 2362895 := bstep (se 1 (by rfl) ⟨1772171, by rfl⟩ : syracuseStep 2362895 = 3544343) B3544343
theorem B1576463 : Blo 1574485 1576463 := bstep (se 1 (by rfl) ⟨1182347, by rfl⟩ : syracuseStep 1576463 = 2364695) B2364695
theorem B26930717 : Blo 1574485 26930717 := bstep (se 3 (by rfl) ⟨5049509, by rfl⟩ : syracuseStep 26930717 = 10099019) B10099019
theorem B2362937 : Blo 1574485 2362937 := bstep (se 2 (by rfl) ⟨886101, by rfl⟩ : syracuseStep 2362937 = 1772203) B1772203
theorem B6655549 : Blo 1574485 6655549 := bstep (se 3 (by rfl) ⟨1247915, by rfl⟩ : syracuseStep 6655549 = 2495831) B2495831
theorem B2363015 : Blo 1574485 2363015 := bstep (se 1 (by rfl) ⟨1772261, by rfl⟩ : syracuseStep 2363015 = 3544523) B3544523
theorem B2657927 : Blo 1574485 2657927 := bstep (se 1 (by rfl) ⟨1993445, by rfl⟩ : syracuseStep 2657927 = 3986891) B3986891
theorem B2363051 : Blo 1574485 2363051 := bstep (se 1 (by rfl) ⟨1772288, by rfl⟩ : syracuseStep 2363051 = 3544577) B3544577
theorem B2363081 : Blo 1574485 2363081 := bstep (se 2 (by rfl) ⟨886155, by rfl⟩ : syracuseStep 2363081 = 1772311) B1772311
theorem B1773319 : Blo 1574485 1773319 := bstep (se 1 (by rfl) ⟨1329989, by rfl⟩ : syracuseStep 1773319 = 2659979) B2659979
theorem B7286543 : Blo 1574485 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B1994539 : Blo 1574485 1994539 := bstep (se 1 (by rfl) ⟨1495904, by rfl⟩ : syracuseStep 1994539 = 2991809) B2991809
theorem B2395961 : Blo 1574485 2395961 := bstep (se 2 (by rfl) ⟨898485, by rfl⟩ : syracuseStep 2395961 = 1796971) B1796971
theorem B2363195 : Blo 1574485 2363195 := bstep (se 1 (by rfl) ⟨1772396, by rfl⟩ : syracuseStep 2363195 = 3544793) B3544793
theorem B3542903 : Blo 1574485 3542903 := bstep (se 1 (by rfl) ⟨2657177, by rfl⟩ : syracuseStep 3542903 = 5314355) B5314355
theorem B2363255 : Blo 1574485 2363255 := bstep (se 1 (by rfl) ⟨1772441, by rfl⟩ : syracuseStep 2363255 = 3544883) B3544883
theorem B2363279 : Blo 1574485 2363279 := bstep (se 1 (by rfl) ⟨1772459, by rfl⟩ : syracuseStep 2363279 = 3544919) B3544919
theorem B2838419 : Blo 1574485 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B2363321 : Blo 1574485 2363321 := bstep (se 2 (by rfl) ⟨886245, by rfl⟩ : syracuseStep 2363321 = 1772491) B1772491
theorem B1773499 : Blo 1574485 1773499 := bstep (se 1 (by rfl) ⟨1330124, by rfl⟩ : syracuseStep 1773499 = 2660249) B2660249
theorem B2363399 : Blo 1574485 2363399 := bstep (se 1 (by rfl) ⟨1772549, by rfl⟩ : syracuseStep 2363399 = 3545099) B3545099
theorem B7974935 : Blo 1574485 7974935 := bstep (se 1 (by rfl) ⟨5981201, by rfl⟩ : syracuseStep 7974935 = 11962403) B11962403
theorem B3543083 : Blo 1574485 3543083 := bstep (se 1 (by rfl) ⟨2657312, by rfl⟩ : syracuseStep 3543083 = 5314625) B5314625
theorem B2363435 : Blo 1574485 2363435 := bstep (se 1 (by rfl) ⟨1772576, by rfl⟩ : syracuseStep 2363435 = 3545153) B3545153
theorem B2363465 : Blo 1574485 2363465 := bstep (se 2 (by rfl) ⟨886299, by rfl⟩ : syracuseStep 2363465 = 1772599) B1772599
theorem B2363579 : Blo 1574485 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B2363639 : Blo 1574485 2363639 := bstep (se 1 (by rfl) ⟨1772729, by rfl⟩ : syracuseStep 2363639 = 3545459) B3545459
theorem B5984513 : Blo 1574485 5984513 := bstep (se 2 (by rfl) ⟨2244192, by rfl⟩ : syracuseStep 5984513 = 4488385) B4488385
theorem B2658575 : Blo 1574485 2658575 := bstep (se 1 (by rfl) ⟨1993931, by rfl⟩ : syracuseStep 2658575 = 3987863) B3987863
theorem B2363663 : Blo 1574485 2363663 := bstep (se 1 (by rfl) ⟨1772747, by rfl⟩ : syracuseStep 2363663 = 3545495) B3545495
theorem B2363705 : Blo 1574485 2363705 := bstep (se 2 (by rfl) ⟨886389, by rfl⟩ : syracuseStep 2363705 = 1772779) B1772779
theorem B2363783 : Blo 1574485 2363783 := bstep (se 1 (by rfl) ⟨1772837, by rfl⟩ : syracuseStep 2363783 = 3545675) B3545675
theorem B3543443 : Blo 1574485 3543443 := bstep (se 1 (by rfl) ⟨2657582, by rfl⟩ : syracuseStep 3543443 = 5315165) B5315165
theorem B5755283 : Blo 1574485 5755283 := bstep (se 1 (by rfl) ⟨4316462, by rfl⟩ : syracuseStep 5755283 = 8632925) B8632925
theorem B2363819 : Blo 1574485 2363819 := bstep (se 1 (by rfl) ⟨1772864, by rfl⟩ : syracuseStep 2363819 = 3545729) B3545729
theorem B3363257 : Blo 1574485 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B3543497 : Blo 1574485 3543497 := bstep (se 2 (by rfl) ⟨1328811, by rfl⟩ : syracuseStep 3543497 = 2657623) B2657623
theorem B2273737 : Blo 1574485 2273737 := bstep (se 2 (by rfl) ⟨852651, by rfl⟩ : syracuseStep 2273737 = 1705303) B1705303
theorem B2363849 : Blo 1574485 2363849 := bstep (se 2 (by rfl) ⟨886443, by rfl⟩ : syracuseStep 2363849 = 1772887) B1772887
theorem B2363963 : Blo 1574485 2363963 := bstep (se 1 (by rfl) ⟨1772972, by rfl⟩ : syracuseStep 2363963 = 3545945) B3545945
theorem B4485719 : Blo 1574485 4485719 := bstep (se 1 (by rfl) ⟨3364289, by rfl⟩ : syracuseStep 4485719 = 6728579) B6728579
theorem B2364023 : Blo 1574485 2364023 := bstep (se 1 (by rfl) ⟨1773017, by rfl⟩ : syracuseStep 2364023 = 3546035) B3546035
theorem B2364047 : Blo 1574485 2364047 := bstep (se 1 (by rfl) ⟨1773035, by rfl⟩ : syracuseStep 2364047 = 3546071) B3546071
theorem B2364089 : Blo 1574485 2364089 := bstep (se 2 (by rfl) ⟨886533, by rfl⟩ : syracuseStep 2364089 = 1773067) B1773067
theorem B2364167 : Blo 1574485 2364167 := bstep (se 1 (by rfl) ⟨1773125, by rfl⟩ : syracuseStep 2364167 = 3546251) B3546251
theorem B3363599 : Blo 1574485 3363599 := bstep (se 1 (by rfl) ⟨2522699, by rfl⟩ : syracuseStep 3363599 = 5045399) B5045399
theorem B2659115 : Blo 1574485 2659115 := bstep (se 1 (by rfl) ⟨1994336, by rfl⟩ : syracuseStep 2659115 = 3988673) B3988673
theorem B2364203 : Blo 1574485 2364203 := bstep (se 1 (by rfl) ⟨1773152, by rfl⟩ : syracuseStep 2364203 = 3546305) B3546305
theorem B2364233 : Blo 1574485 2364233 := bstep (se 2 (by rfl) ⟨886587, by rfl⟩ : syracuseStep 2364233 = 1773175) B1773175
theorem B11359091 : Blo 1574485 11359091 := bstep (se 1 (by rfl) ⟨8519318, by rfl⟩ : syracuseStep 11359091 = 17038637) B17038637
theorem B10097561 : Blo 1574485 10097561 := bstep (se 2 (by rfl) ⟨3786585, by rfl⟩ : syracuseStep 10097561 = 7573171) B7573171
theorem B2364347 : Blo 1574485 2364347 := bstep (se 1 (by rfl) ⟨1773260, by rfl⟩ : syracuseStep 2364347 = 3546521) B3546521
theorem B2364407 : Blo 1574485 2364407 := bstep (se 1 (by rfl) ⟨1773305, by rfl⟩ : syracuseStep 2364407 = 3546611) B3546611
theorem B2364431 : Blo 1574485 2364431 := bstep (se 1 (by rfl) ⟨1773323, by rfl⟩ : syracuseStep 2364431 = 3546647) B3546647
theorem B2364473 : Blo 1574485 2364473 := bstep (se 2 (by rfl) ⟨886677, by rfl⟩ : syracuseStep 2364473 = 1773355) B1773355
theorem B3986567 : Blo 1574485 3986567 := bstep (se 1 (by rfl) ⟨2989925, by rfl⟩ : syracuseStep 3986567 = 5979851) B5979851
theorem B3544199 : Blo 1574485 3544199 := bstep (se 1 (by rfl) ⟨2658149, by rfl⟩ : syracuseStep 3544199 = 5316299) B5316299
theorem B2364551 : Blo 1574485 2364551 := bstep (se 1 (by rfl) ⟨1773413, by rfl⟩ : syracuseStep 2364551 = 3546827) B3546827
theorem B2364587 : Blo 1574485 2364587 := bstep (se 1 (by rfl) ⟨1773440, by rfl⟩ : syracuseStep 2364587 = 3546881) B3546881
theorem B3986617 : Blo 1574485 3986617 := bstep (se 2 (by rfl) ⟨1494981, by rfl⟩ : syracuseStep 3986617 = 2989963) B2989963
theorem B2659513 : Blo 1574485 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B2364617 : Blo 1574485 2364617 := bstep (se 2 (by rfl) ⟨886731, by rfl⟩ : syracuseStep 2364617 = 1773463) B1773463
theorem B38319419 : Blo 1574485 38319419 := bstep (se 1 (by rfl) ⟨28739564, by rfl⟩ : syracuseStep 38319419 = 57479129) B57479129
theorem B3544379 : Blo 1574485 3544379 := bstep (se 1 (by rfl) ⟨2658284, by rfl⟩ : syracuseStep 3544379 = 5316569) B5316569
theorem B5985683 : Blo 1574485 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B5313977 : Blo 1574485 5313977 := bstep (se 2 (by rfl) ⟨1992741, by rfl⟩ : syracuseStep 5313977 = 3985483) B3985483
theorem B3544505 : Blo 1574485 3544505 := bstep (se 2 (by rfl) ⟨1329189, by rfl⟩ : syracuseStep 3544505 = 2658379) B2658379
theorem B4486585 : Blo 1574485 4486585 := bstep (se 2 (by rfl) ⟨1682469, by rfl⟩ : syracuseStep 4486585 = 3364939) B3364939
theorem B6477355 : Blo 1574485 6477355 := bstep (se 1 (by rfl) ⟨4858016, by rfl⟩ : syracuseStep 6477355 = 9716033) B9716033
theorem B17036867 : Blo 1574485 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B3364487 : Blo 1574485 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B3987215 : Blo 1574485 3987215 := bstep (se 1 (by rfl) ⟨2990411, by rfl⟩ : syracuseStep 3987215 = 5980823) B5980823
theorem B3544847 : Blo 1574485 3544847 := bstep (se 1 (by rfl) ⟨2658635, by rfl⟩ : syracuseStep 3544847 = 5317271) B5317271
theorem B4486927 : Blo 1574485 4486927 := bstep (se 1 (by rfl) ⟨3365195, by rfl⟩ : syracuseStep 4486927 = 6730391) B6730391
theorem B3544865 : Blo 1574485 3544865 := bstep (se 2 (by rfl) ⟨1329324, by rfl⟩ : syracuseStep 3544865 = 2658649) B2658649
theorem B17028953 : Blo 1574485 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B2660215 : Blo 1574485 2660215 := bstep (se 1 (by rfl) ⟨1995161, by rfl⟩ : syracuseStep 2660215 = 3990323) B3990323
theorem B5044103 : Blo 1574485 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B17946521 : Blo 1574485 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B30275531 : Blo 1574485 30275531 := bstep (se 1 (by rfl) ⟨22706648, by rfl⟩ : syracuseStep 30275531 = 45413297) B45413297
theorem B5314571 : Blo 1574485 5314571 := bstep (se 1 (by rfl) ⟨3985928, by rfl⟩ : syracuseStep 5314571 = 7971857) B7971857
theorem B6912029 : Blo 1574485 6912029 := bstep (se 3 (by rfl) ⟨1296005, by rfl⟩ : syracuseStep 6912029 = 2592011) B2592011
theorem B3364897 : Blo 1574485 3364897 := bstep (se 2 (by rfl) ⟨1261836, by rfl⟩ : syracuseStep 3364897 = 2523673) B2523673
theorem B4487201 : Blo 1574485 4487201 := bstep (se 2 (by rfl) ⟨1682700, by rfl⟩ : syracuseStep 4487201 = 3365401) B3365401
theorem B5314679 : Blo 1574485 5314679 := bstep (se 1 (by rfl) ⟨3986009, by rfl⟩ : syracuseStep 5314679 = 7972019) B7972019
theorem B3545207 : Blo 1574485 3545207 := bstep (se 1 (by rfl) ⟨2658905, by rfl⟩ : syracuseStep 3545207 = 5317811) B5317811
theorem B20191477 : Blo 1574485 20191477 := bstep (se 5 (by rfl) ⟨946475, by rfl⟩ : syracuseStep 20191477 = 1892951) B1892951
theorem B5044513 : Blo 1574485 5044513 := bstep (se 2 (by rfl) ⟨1891692, by rfl⟩ : syracuseStep 5044513 = 3783385) B3783385
theorem B6732065 : Blo 1574485 6732065 := bstep (se 2 (by rfl) ⟨2524524, by rfl⟩ : syracuseStep 6732065 = 5049049) B5049049
theorem B3545387 : Blo 1574485 3545387 := bstep (se 1 (by rfl) ⟨2659040, by rfl⟩ : syracuseStep 3545387 = 5318081) B5318081
theorem B15137117 : Blo 1574485 15137117 := bstep (se 3 (by rfl) ⟨2838209, by rfl⟩ : syracuseStep 15137117 = 5676419) B5676419
theorem B3365239 : Blo 1574485 3365239 := bstep (se 1 (by rfl) ⟨2523929, by rfl⟩ : syracuseStep 3365239 = 5047859) B5047859
theorem B3987913 : Blo 1574485 3987913 := bstep (se 2 (by rfl) ⟨1495467, by rfl⟩ : syracuseStep 3987913 = 2990935) B2990935
theorem B5978711 : Blo 1574485 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B3988055 : Blo 1574485 3988055 := bstep (se 1 (by rfl) ⟨2991041, by rfl⟩ : syracuseStep 3988055 = 5982083) B5982083
theorem B4487815 : Blo 1574485 4487815 := bstep (se 1 (by rfl) ⟨3365861, by rfl⟩ : syracuseStep 4487815 = 6731723) B6731723
theorem B3545747 : Blo 1574485 3545747 := bstep (se 1 (by rfl) ⟨2659310, by rfl⟩ : syracuseStep 3545747 = 5318621) B5318621
theorem B5315273 : Blo 1574485 5315273 := bstep (se 2 (by rfl) ⟨1993227, by rfl⟩ : syracuseStep 5315273 = 3986455) B3986455
theorem B3545801 : Blo 1574485 3545801 := bstep (se 2 (by rfl) ⟨1329675, by rfl⟩ : syracuseStep 3545801 = 2659351) B2659351
theorem B3193643 : Blo 1574485 3193643 := bstep (se 1 (by rfl) ⟨2395232, by rfl⟩ : syracuseStep 3193643 = 4790465) B4790465
theorem B4488203 : Blo 1574485 4488203 := bstep (se 1 (by rfl) ⟨3366152, by rfl⟩ : syracuseStep 4488203 = 6732305) B6732305
theorem B7978013 : Blo 1574485 7978013 := bstep (se 3 (by rfl) ⟨1495877, by rfl⟩ : syracuseStep 7978013 = 2991755) B2991755
theorem B5979197 : Blo 1574485 5979197 := bstep (se 3 (by rfl) ⟨1121099, by rfl⟩ : syracuseStep 5979197 = 2242199) B2242199
theorem B2243657 : Blo 1574485 2243657 := bstep (se 2 (by rfl) ⟨841371, by rfl⟩ : syracuseStep 2243657 = 1682743) B1682743
theorem B3783827 : Blo 1574485 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B2522411 : Blo 1574485 2522411 := bstep (se 1 (by rfl) ⟨1891808, by rfl⟩ : syracuseStep 2522411 = 3783617) B3783617
theorem B3366203 : Blo 1574485 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B7568729 : Blo 1574485 7568729 := bstep (se 2 (by rfl) ⟨2838273, by rfl⟩ : syracuseStep 7568729 = 5676547) B5676547
theorem B5315975 : Blo 1574485 5315975 := bstep (se 1 (by rfl) ⟨3986981, by rfl⟩ : syracuseStep 5315975 = 7973963) B7973963
theorem B3546503 : Blo 1574485 3546503 := bstep (se 1 (by rfl) ⟨2659877, by rfl⟩ : syracuseStep 3546503 = 5319755) B5319755
theorem B3030419 : Blo 1574485 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B8977817 : Blo 1574485 8977817 := bstep (se 2 (by rfl) ⟨3366681, by rfl⟩ : syracuseStep 8977817 = 6733363) B6733363
theorem B7978499 : Blo 1574485 7978499 := bstep (se 1 (by rfl) ⟨5983874, by rfl⟩ : syracuseStep 7978499 = 11967749) B11967749
theorem B4791851 : Blo 1574485 4791851 := bstep (se 1 (by rfl) ⟨3593888, by rfl⟩ : syracuseStep 4791851 = 7187777) B7187777
theorem B3366443 : Blo 1574485 3366443 := bstep (se 1 (by rfl) ⟨2524832, by rfl⟩ : syracuseStep 3366443 = 5049665) B5049665
theorem B3546683 : Blo 1574485 3546683 := bstep (se 1 (by rfl) ⟨2660012, by rfl⟩ : syracuseStep 3546683 = 5320025) B5320025
theorem B24247907 : Blo 1574485 24247907 := bstep (se 1 (by rfl) ⟨18185930, by rfl⟩ : syracuseStep 24247907 = 36371861) B36371861
theorem B21552817 : Blo 1574485 21552817 := bstep (se 2 (by rfl) ⟨8082306, by rfl⟩ : syracuseStep 21552817 = 16164613) B16164613
theorem B3546809 : Blo 1574485 3546809 := bstep (se 2 (by rfl) ⟨1330053, by rfl⟩ : syracuseStep 3546809 = 2660107) B2660107
theorem B5316353 : Blo 1574485 5316353 := bstep (se 2 (by rfl) ⟨1993632, by rfl⟩ : syracuseStep 5316353 = 3987265) B3987265
theorem B26935091 : Blo 1574485 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B1597243 : Blo 1574485 1597243 := bstep (se 1 (by rfl) ⟨1197932, by rfl⟩ : syracuseStep 1597243 = 2395865) B2395865
theorem B20176715 : Blo 1574485 20176715 := bstep (se 1 (by rfl) ⟨15132536, by rfl⟩ : syracuseStep 20176715 = 30265073) B30265073
theorem B16162649 : Blo 1574485 16162649 := bstep (se 2 (by rfl) ⟨6060993, by rfl⟩ : syracuseStep 16162649 = 12121987) B12121987
theorem B2244523 : Blo 1574485 2244523 := bstep (se 1 (by rfl) ⟨1683392, by rfl⟩ : syracuseStep 2244523 = 3366785) B3366785
theorem B2990009 : Blo 1574485 2990009 := bstep (se 2 (by rfl) ⟨1121253, by rfl⟩ : syracuseStep 2990009 = 2242507) B2242507
theorem B5316623 : Blo 1574485 5316623 := bstep (se 1 (by rfl) ⟨3987467, by rfl⟩ : syracuseStep 5316623 = 7974935) B7974935
theorem B4489273 : Blo 1574485 4489273 := bstep (se 2 (by rfl) ⟨1683477, by rfl⟩ : syracuseStep 4489273 = 3366955) B3366955
theorem B3989675 : Blo 1574485 3989675 := bstep (se 1 (by rfl) ⟨2992256, by rfl⟩ : syracuseStep 3989675 = 5984513) B5984513
theorem B24264971 : Blo 1574485 24264971 := bstep (se 1 (by rfl) ⟨18198728, by rfl⟩ : syracuseStep 24264971 = 36397457) B36397457
theorem B2523487 : Blo 1574485 2523487 := bstep (se 1 (by rfl) ⟨1892615, by rfl⟩ : syracuseStep 2523487 = 3785231) B3785231
theorem B6726017 : Blo 1574485 6726017 := bstep (se 2 (by rfl) ⟨2522256, by rfl⟩ : syracuseStep 6726017 = 5044513) B5044513
theorem B4546945 : Blo 1574485 4546945 := bstep (se 2 (by rfl) ⟨1705104, by rfl⟩ : syracuseStep 4546945 = 3410209) B3410209
theorem B3031649 : Blo 1574485 3031649 := bstep (se 2 (by rfl) ⟨1136868, by rfl⟩ : syracuseStep 3031649 = 2273737) B2273737
theorem B5317217 : Blo 1574485 5317217 := bstep (se 2 (by rfl) ⟨1993956, by rfl⟩ : syracuseStep 5317217 = 3987913) B3987913
theorem B4260601 : Blo 1574485 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B5981111 : Blo 1574485 5981111 := bstep (se 1 (by rfl) ⟨4485833, by rfl⟩ : syracuseStep 5981111 = 8971667) B8971667
theorem B3990455 : Blo 1574485 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B2991467 : Blo 1574485 2991467 := bstep (se 1 (by rfl) ⟨2243600, by rfl⟩ : syracuseStep 2991467 = 4487201) B4487201
theorem B10093997 : Blo 1574485 10093997 := bstep (se 3 (by rfl) ⟨1892624, by rfl⟩ : syracuseStep 10093997 = 3785249) B3785249
theorem B2524679 : Blo 1574485 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B1705511 : Blo 1574485 1705511 := bstep (se 1 (by rfl) ⟨1279133, by rfl⟩ : syracuseStep 1705511 = 2558267) B2558267
theorem B11961917 : Blo 1574485 11961917 := bstep (se 3 (by rfl) ⟨2242859, by rfl⟩ : syracuseStep 11961917 = 4485719) B4485719
theorem B1574495 : Blo 1574485 1574495 := bstep (se 1 (by rfl) ⟨1180871, by rfl⟩ : syracuseStep 1574495 = 2361743) B2361743
theorem B1574523 : Blo 1574485 1574523 := bstep (se 1 (by rfl) ⟨1180892, by rfl⟩ : syracuseStep 1574523 = 2361785) B2361785
theorem B1574575 : Blo 1574485 1574575 := bstep (se 1 (by rfl) ⟨1180931, by rfl⟩ : syracuseStep 1574575 = 2361863) B2361863
theorem B1574599 : Blo 1574485 1574599 := bstep (se 1 (by rfl) ⟨1180949, by rfl⟩ : syracuseStep 1574599 = 2361899) B2361899
theorem B2524871 : Blo 1574485 2524871 := bstep (se 1 (by rfl) ⟨1893653, by rfl⟩ : syracuseStep 2524871 = 3787307) B3787307
theorem B1574619 : Blo 1574485 1574619 := bstep (se 1 (by rfl) ⟨1180964, by rfl⟩ : syracuseStep 1574619 = 2361929) B2361929
theorem B1574695 : Blo 1574485 1574695 := bstep (se 1 (by rfl) ⟨1181021, by rfl⟩ : syracuseStep 1574695 = 2362043) B2362043
theorem B1574735 : Blo 1574485 1574735 := bstep (se 1 (by rfl) ⟨1181051, by rfl⟩ : syracuseStep 1574735 = 2362103) B2362103
theorem B1574751 : Blo 1574485 1574751 := bstep (se 1 (by rfl) ⟨1181063, by rfl⟩ : syracuseStep 1574751 = 2362127) B2362127
theorem B1574779 : Blo 1574485 1574779 := bstep (se 1 (by rfl) ⟨1181084, by rfl⟩ : syracuseStep 1574779 = 2362169) B2362169
theorem B5982113 : Blo 1574485 5982113 := bstep (se 2 (by rfl) ⟨2243292, by rfl⟩ : syracuseStep 5982113 = 4486585) B4486585
theorem B1574831 : Blo 1574485 1574831 := bstep (se 1 (by rfl) ⟨1181123, by rfl⟩ : syracuseStep 1574831 = 2362247) B2362247
theorem B1574855 : Blo 1574485 1574855 := bstep (se 1 (by rfl) ⟨1181141, by rfl⟩ : syracuseStep 1574855 = 2362283) B2362283
theorem B1771483 : Blo 1574485 1771483 := bstep (se 1 (by rfl) ⟨1328612, by rfl⟩ : syracuseStep 1771483 = 2657225) B2657225
theorem B1574875 : Blo 1574485 1574875 := bstep (se 1 (by rfl) ⟨1181156, by rfl⟩ : syracuseStep 1574875 = 2362313) B2362313
theorem B45402119 : Blo 1574485 45402119 := bstep (se 1 (by rfl) ⟨34051589, by rfl⟩ : syracuseStep 45402119 = 68103179) B68103179
theorem B2992135 : Blo 1574485 2992135 := bstep (se 1 (by rfl) ⟨2244101, by rfl⟩ : syracuseStep 2992135 = 4488203) B4488203
theorem B5318675 : Blo 1574485 5318675 := bstep (se 1 (by rfl) ⟨3989006, by rfl⟩ : syracuseStep 5318675 = 7978013) B7978013
theorem B1574951 : Blo 1574485 1574951 := bstep (se 1 (by rfl) ⟨1181213, by rfl⟩ : syracuseStep 1574951 = 2362427) B2362427
theorem B8636473 : Blo 1574485 8636473 := bstep (se 2 (by rfl) ⟨3238677, by rfl⟩ : syracuseStep 8636473 = 6477355) B6477355
theorem B1574991 : Blo 1574485 1574991 := bstep (se 1 (by rfl) ⟨1181243, by rfl⟩ : syracuseStep 1574991 = 2362487) B2362487
theorem B8874065 : Blo 1574485 8874065 := bstep (se 2 (by rfl) ⟨3327774, by rfl⟩ : syracuseStep 8874065 = 6655549) B6655549
theorem B1575007 : Blo 1574485 1575007 := bstep (se 1 (by rfl) ⟨1181255, by rfl⟩ : syracuseStep 1575007 = 2362511) B2362511
theorem B1575035 : Blo 1574485 1575035 := bstep (se 1 (by rfl) ⟨1181276, by rfl⟩ : syracuseStep 1575035 = 2362553) B2362553
theorem B1575087 : Blo 1574485 1575087 := bstep (se 1 (by rfl) ⟨1181315, by rfl⟩ : syracuseStep 1575087 = 2362631) B2362631
theorem B1681607 : Blo 1574485 1681607 := bstep (se 1 (by rfl) ⟨1261205, by rfl⟩ : syracuseStep 1681607 = 2522411) B2522411
theorem B1575111 : Blo 1574485 1575111 := bstep (se 1 (by rfl) ⟨1181333, by rfl⟩ : syracuseStep 1575111 = 2362667) B2362667
theorem B1575131 : Blo 1574485 1575131 := bstep (se 1 (by rfl) ⟨1181348, by rfl⟩ : syracuseStep 1575131 = 2362697) B2362697
theorem B1575207 : Blo 1574485 1575207 := bstep (se 1 (by rfl) ⟨1181405, by rfl⟩ : syracuseStep 1575207 = 2362811) B2362811
theorem B1575247 : Blo 1574485 1575247 := bstep (se 1 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 1575247 = 2362871) B2362871
theorem B5318999 : Blo 1574485 5318999 := bstep (se 1 (by rfl) ⟨3989249, by rfl⟩ : syracuseStep 5318999 = 7978499) B7978499
theorem B1575263 : Blo 1574485 1575263 := bstep (se 1 (by rfl) ⟨1181447, by rfl⟩ : syracuseStep 1575263 = 2362895) B2362895
theorem B5982569 : Blo 1574485 5982569 := bstep (se 2 (by rfl) ⟨2243463, by rfl⟩ : syracuseStep 5982569 = 4486927) B4486927
theorem B1575291 : Blo 1574485 1575291 := bstep (se 1 (by rfl) ⟨1181468, by rfl⟩ : syracuseStep 1575291 = 2362937) B2362937
theorem B16165271 : Blo 1574485 16165271 := bstep (se 1 (by rfl) ⟨12123953, by rfl⟩ : syracuseStep 16165271 = 24247907) B24247907
theorem B1771951 : Blo 1574485 1771951 := bstep (se 1 (by rfl) ⟨1328963, by rfl⟩ : syracuseStep 1771951 = 2657927) B2657927
theorem B1575343 : Blo 1574485 1575343 := bstep (se 1 (by rfl) ⟨1181507, by rfl⟩ : syracuseStep 1575343 = 2363015) B2363015
theorem B1575367 : Blo 1574485 1575367 := bstep (se 1 (by rfl) ⟨1181525, by rfl⟩ : syracuseStep 1575367 = 2363051) B2363051
theorem B1575387 : Blo 1574485 1575387 := bstep (se 1 (by rfl) ⟨1181540, by rfl⟩ : syracuseStep 1575387 = 2363081) B2363081
theorem B11962889 : Blo 1574485 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B1575463 : Blo 1574485 1575463 := bstep (se 1 (by rfl) ⟨1181597, by rfl⟩ : syracuseStep 1575463 = 2363195) B2363195
theorem B2992697 : Blo 1574485 2992697 := bstep (se 2 (by rfl) ⟨1122261, by rfl⟩ : syracuseStep 2992697 = 2244523) B2244523
theorem B10775099 : Blo 1574485 10775099 := bstep (se 1 (by rfl) ⟨8081324, by rfl⟩ : syracuseStep 10775099 = 16162649) B16162649
theorem B2361935 : Blo 1574485 2361935 := bstep (se 1 (by rfl) ⟨1771451, by rfl⟩ : syracuseStep 2361935 = 3542903) B3542903
theorem B1575503 : Blo 1574485 1575503 := bstep (se 1 (by rfl) ⟨1181627, by rfl⟩ : syracuseStep 1575503 = 2363255) B2363255
theorem B1575519 : Blo 1574485 1575519 := bstep (se 1 (by rfl) ⟨1181639, by rfl⟩ : syracuseStep 1575519 = 2363279) B2363279
theorem B1993339 : Blo 1574485 1993339 := bstep (se 1 (by rfl) ⟨1495004, by rfl⟩ : syracuseStep 1993339 = 2990009) B2990009
theorem B1575547 : Blo 1574485 1575547 := bstep (se 1 (by rfl) ⟨1181660, by rfl⟩ : syracuseStep 1575547 = 2363321) B2363321
theorem B1575599 : Blo 1574485 1575599 := bstep (se 1 (by rfl) ⟨1181699, by rfl⟩ : syracuseStep 1575599 = 2363399) B2363399
theorem B2362055 : Blo 1574485 2362055 := bstep (se 1 (by rfl) ⟨1771541, by rfl⟩ : syracuseStep 2362055 = 3543083) B3543083
theorem B1575623 : Blo 1574485 1575623 := bstep (se 1 (by rfl) ⟨1181717, by rfl⟩ : syracuseStep 1575623 = 2363435) B2363435
theorem B4483795 : Blo 1574485 4483795 := bstep (se 1 (by rfl) ⟨3362846, by rfl⟩ : syracuseStep 4483795 = 6725693) B6725693
theorem B1575643 : Blo 1574485 1575643 := bstep (se 1 (by rfl) ⟨1181732, by rfl⟩ : syracuseStep 1575643 = 2363465) B2363465
theorem B1575719 : Blo 1574485 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B1575759 : Blo 1574485 1575759 := bstep (se 1 (by rfl) ⟨1181819, by rfl⟩ : syracuseStep 1575759 = 2363639) B2363639
theorem B1993567 : Blo 1574485 1993567 := bstep (se 1 (by rfl) ⟨1495175, by rfl⟩ : syracuseStep 1993567 = 2990351) B2990351
theorem B1772383 : Blo 1574485 1772383 := bstep (se 1 (by rfl) ⟨1329287, by rfl⟩ : syracuseStep 1772383 = 2658575) B2658575
theorem B1575775 : Blo 1574485 1575775 := bstep (se 1 (by rfl) ⟨1181831, by rfl⟩ : syracuseStep 1575775 = 2363663) B2363663
theorem B2362217 : Blo 1574485 2362217 := bstep (se 2 (by rfl) ⟨885831, by rfl⟩ : syracuseStep 2362217 = 1771663) B1771663
theorem B5983085 : Blo 1574485 5983085 := bstep (se 3 (by rfl) ⟨1121828, by rfl⟩ : syracuseStep 5983085 = 2243657) B2243657
theorem B1575803 : Blo 1574485 1575803 := bstep (se 1 (by rfl) ⟨1181852, by rfl⟩ : syracuseStep 1575803 = 2363705) B2363705
theorem B35466131 : Blo 1574485 35466131 := bstep (se 1 (by rfl) ⟨26599598, by rfl⟩ : syracuseStep 35466131 = 53199197) B53199197
theorem B1575855 : Blo 1574485 1575855 := bstep (se 1 (by rfl) ⟨1181891, by rfl⟩ : syracuseStep 1575855 = 2363783) B2363783
theorem B25537463 : Blo 1574485 25537463 := bstep (se 1 (by rfl) ⟨19153097, by rfl⟩ : syracuseStep 25537463 = 38306195) B38306195
theorem B2362295 : Blo 1574485 2362295 := bstep (se 1 (by rfl) ⟨1771721, by rfl⟩ : syracuseStep 2362295 = 3543443) B3543443
theorem B3836855 : Blo 1574485 3836855 := bstep (se 1 (by rfl) ⟨2877641, by rfl⟩ : syracuseStep 3836855 = 5755283) B5755283
theorem B1575879 : Blo 1574485 1575879 := bstep (se 1 (by rfl) ⟨1181909, by rfl⟩ : syracuseStep 1575879 = 2363819) B2363819
theorem B2362331 : Blo 1574485 2362331 := bstep (se 1 (by rfl) ⟨1771748, by rfl⟩ : syracuseStep 2362331 = 3543497) B3543497
theorem B1575899 : Blo 1574485 1575899 := bstep (se 1 (by rfl) ⟨1181924, by rfl⟩ : syracuseStep 1575899 = 2363849) B2363849
theorem B26921969 : Blo 1574485 26921969 := bstep (se 2 (by rfl) ⟨10095738, by rfl⟩ : syracuseStep 26921969 = 20191477) B20191477
theorem B1575975 : Blo 1574485 1575975 := bstep (se 1 (by rfl) ⟨1181981, by rfl⟩ : syracuseStep 1575975 = 2363963) B2363963
theorem B6065209 : Blo 1574485 6065209 := bstep (se 2 (by rfl) ⟨2274453, by rfl⟩ : syracuseStep 6065209 = 4548907) B4548907
theorem B1576015 : Blo 1574485 1576015 := bstep (se 1 (by rfl) ⟨1182011, by rfl⟩ : syracuseStep 1576015 = 2364023) B2364023
theorem B1576031 : Blo 1574485 1576031 := bstep (se 1 (by rfl) ⟨1182023, by rfl⟩ : syracuseStep 1576031 = 2364047) B2364047
theorem B1576059 : Blo 1574485 1576059 := bstep (se 1 (by rfl) ⟨1182044, by rfl⟩ : syracuseStep 1576059 = 2364089) B2364089
theorem B1576111 : Blo 1574485 1576111 := bstep (se 1 (by rfl) ⟨1182083, by rfl⟩ : syracuseStep 1576111 = 2364167) B2364167
theorem B1772743 : Blo 1574485 1772743 := bstep (se 1 (by rfl) ⟨1329557, by rfl⟩ : syracuseStep 1772743 = 2659115) B2659115
theorem B1576135 : Blo 1574485 1576135 := bstep (se 1 (by rfl) ⟨1182101, by rfl⟩ : syracuseStep 1576135 = 2364203) B2364203
theorem B1576155 : Blo 1574485 1576155 := bstep (se 1 (by rfl) ⟨1182116, by rfl⟩ : syracuseStep 1576155 = 2364233) B2364233
theorem B7572727 : Blo 1574485 7572727 := bstep (se 1 (by rfl) ⟨5679545, by rfl⟩ : syracuseStep 7572727 = 11359091) B11359091
theorem B1576231 : Blo 1574485 1576231 := bstep (se 1 (by rfl) ⟨1182173, by rfl⟩ : syracuseStep 1576231 = 2364347) B2364347
theorem B1576271 : Blo 1574485 1576271 := bstep (se 1 (by rfl) ⟨1182203, by rfl⟩ : syracuseStep 1576271 = 2364407) B2364407
theorem B1576287 : Blo 1574485 1576287 := bstep (se 1 (by rfl) ⟨1182215, by rfl⟩ : syracuseStep 1576287 = 2364431) B2364431
theorem B1576315 : Blo 1574485 1576315 := bstep (se 1 (by rfl) ⟨1182236, by rfl⟩ : syracuseStep 1576315 = 2364473) B2364473
theorem B3837313 : Blo 1574485 3837313 := bstep (se 2 (by rfl) ⟨1438992, by rfl⟩ : syracuseStep 3837313 = 2877985) B2877985
theorem B7974287 : Blo 1574485 7974287 := bstep (se 1 (by rfl) ⟨5980715, by rfl⟩ : syracuseStep 7974287 = 11961431) B11961431
theorem B5320079 : Blo 1574485 5320079 := bstep (se 1 (by rfl) ⟨3990059, by rfl⟩ : syracuseStep 5320079 = 7980119) B7980119
theorem B2657711 : Blo 1574485 2657711 := bstep (se 1 (by rfl) ⟨1993283, by rfl⟩ : syracuseStep 2657711 = 3986567) B3986567
theorem B2362799 : Blo 1574485 2362799 := bstep (se 1 (by rfl) ⟨1772099, by rfl⟩ : syracuseStep 2362799 = 3544199) B3544199
theorem B1994159 : Blo 1574485 1994159 := bstep (se 1 (by rfl) ⟨1495619, by rfl⟩ : syracuseStep 1994159 = 2991239) B2991239
theorem B1576367 : Blo 1574485 1576367 := bstep (se 1 (by rfl) ⟨1182275, by rfl⟩ : syracuseStep 1576367 = 2364551) B2364551
theorem B1576391 : Blo 1574485 1576391 := bstep (se 1 (by rfl) ⟨1182293, by rfl⟩ : syracuseStep 1576391 = 2364587) B2364587
theorem B1576411 : Blo 1574485 1576411 := bstep (se 1 (by rfl) ⟨1182308, by rfl⟩ : syracuseStep 1576411 = 2364617) B2364617
theorem B2362889 : Blo 1574485 2362889 := bstep (se 2 (by rfl) ⟨886083, by rfl⟩ : syracuseStep 2362889 = 1772167) B1772167
theorem B5983753 : Blo 1574485 5983753 := bstep (se 2 (by rfl) ⟨2243907, by rfl⟩ : syracuseStep 5983753 = 4487815) B4487815
theorem B25546279 : Blo 1574485 25546279 := bstep (se 1 (by rfl) ⟨19159709, by rfl⟩ : syracuseStep 25546279 = 38319419) B38319419
theorem B2362919 : Blo 1574485 2362919 := bstep (se 1 (by rfl) ⟨1772189, by rfl⟩ : syracuseStep 2362919 = 3544379) B3544379
theorem B3542651 : Blo 1574485 3542651 := bstep (se 1 (by rfl) ⟨2656988, by rfl⟩ : syracuseStep 3542651 = 5313977) B5313977
theorem B2363003 : Blo 1574485 2363003 := bstep (se 1 (by rfl) ⟨1772252, by rfl⟩ : syracuseStep 2363003 = 3544505) B3544505
theorem B5320403 : Blo 1574485 5320403 := bstep (se 1 (by rfl) ⟨3990302, by rfl⟩ : syracuseStep 5320403 = 7980605) B7980605
theorem B11357911 : Blo 1574485 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B8081117 : Blo 1574485 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B3542777 : Blo 1574485 3542777 := bstep (se 2 (by rfl) ⟨1328541, by rfl⟩ : syracuseStep 3542777 = 2657083) B2657083
theorem B2363129 : Blo 1574485 2363129 := bstep (se 2 (by rfl) ⟨886173, by rfl⟩ : syracuseStep 2363129 = 1772347) B1772347
theorem B2658143 : Blo 1574485 2658143 := bstep (se 1 (by rfl) ⟨1993607, by rfl⟩ : syracuseStep 2658143 = 3987215) B3987215
theorem B2363231 : Blo 1574485 2363231 := bstep (se 1 (by rfl) ⟨1772423, by rfl⟩ : syracuseStep 2363231 = 3544847) B3544847
theorem B2363243 : Blo 1574485 2363243 := bstep (se 1 (by rfl) ⟨1772432, by rfl⟩ : syracuseStep 2363243 = 3544865) B3544865
theorem B12783521 : Blo 1574485 12783521 := bstep (se 2 (by rfl) ⟨4793820, by rfl⟩ : syracuseStep 12783521 = 9587641) B9587641
theorem B3362735 : Blo 1574485 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B17936315 : Blo 1574485 17936315 := bstep (se 1 (by rfl) ⟨13452236, by rfl⟩ : syracuseStep 17936315 = 26904473) B26904473
theorem B11964347 : Blo 1574485 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B3543047 : Blo 1574485 3543047 := bstep (se 1 (by rfl) ⟨2657285, by rfl⟩ : syracuseStep 3543047 = 5314571) B5314571
theorem B4485127 : Blo 1574485 4485127 := bstep (se 1 (by rfl) ⟨3363845, by rfl⟩ : syracuseStep 4485127 = 6727691) B6727691
theorem B4608019 : Blo 1574485 4608019 := bstep (se 1 (by rfl) ⟨3456014, by rfl⟩ : syracuseStep 4608019 = 6912029) B6912029
theorem B3543119 : Blo 1574485 3543119 := bstep (se 1 (by rfl) ⟨2657339, by rfl⟩ : syracuseStep 3543119 = 5314679) B5314679
theorem B2363471 : Blo 1574485 2363471 := bstep (se 1 (by rfl) ⟨1772603, by rfl⟩ : syracuseStep 2363471 = 3545207) B3545207
theorem B10088563 : Blo 1574485 10088563 := bstep (se 1 (by rfl) ⟨7566422, by rfl⟩ : syracuseStep 10088563 = 15132845) B15132845
theorem B43135091 : Blo 1574485 43135091 := bstep (se 1 (by rfl) ⟨32351318, by rfl⟩ : syracuseStep 43135091 = 64702637) B64702637
theorem B2363591 : Blo 1574485 2363591 := bstep (se 1 (by rfl) ⟨1772693, by rfl⟩ : syracuseStep 2363591 = 3545387) B3545387
theorem B2363753 : Blo 1574485 2363753 := bstep (se 2 (by rfl) ⟨886407, by rfl⟩ : syracuseStep 2363753 = 1772815) B1772815
theorem B2396521 : Blo 1574485 2396521 := bstep (se 2 (by rfl) ⟨898695, by rfl⟩ : syracuseStep 2396521 = 1797391) B1797391
theorem B3985807 : Blo 1574485 3985807 := bstep (se 1 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 3985807 = 5978711) B5978711
theorem B2658703 : Blo 1574485 2658703 := bstep (se 1 (by rfl) ⟨1994027, by rfl⟩ : syracuseStep 2658703 = 3988055) B3988055
theorem B2363831 : Blo 1574485 2363831 := bstep (se 1 (by rfl) ⟨1772873, by rfl⟩ : syracuseStep 2363831 = 3545747) B3545747
theorem B3543515 : Blo 1574485 3543515 := bstep (se 1 (by rfl) ⟨2657636, by rfl⟩ : syracuseStep 3543515 = 5315273) B5315273
theorem B2363867 : Blo 1574485 2363867 := bstep (se 1 (by rfl) ⟨1772900, by rfl⟩ : syracuseStep 2363867 = 3545801) B3545801
theorem B3986131 : Blo 1574485 3986131 := bstep (se 1 (by rfl) ⟨2989598, by rfl⟩ : syracuseStep 3986131 = 5979197) B5979197
theorem B3543983 : Blo 1574485 3543983 := bstep (se 1 (by rfl) ⟨2657987, by rfl⟩ : syracuseStep 3543983 = 5315975) B5315975
theorem B2364335 : Blo 1574485 2364335 := bstep (se 1 (by rfl) ⟨1773251, by rfl⟩ : syracuseStep 2364335 = 3546503) B3546503
theorem B5985211 : Blo 1574485 5985211 := bstep (se 1 (by rfl) ⟨4488908, by rfl⟩ : syracuseStep 5985211 = 8977817) B8977817
theorem B2364425 : Blo 1574485 2364425 := bstep (se 2 (by rfl) ⟨886659, by rfl⟩ : syracuseStep 2364425 = 1773319) B1773319
theorem B17953811 : Blo 1574485 17953811 := bstep (se 1 (by rfl) ⟨13465358, by rfl⟩ : syracuseStep 17953811 = 26930717) B26930717
theorem B2364455 : Blo 1574485 2364455 := bstep (se 1 (by rfl) ⟨1773341, by rfl⟩ : syracuseStep 2364455 = 3546683) B3546683
theorem B2659385 : Blo 1574485 2659385 := bstep (se 2 (by rfl) ⟨997269, by rfl⟩ : syracuseStep 2659385 = 1994539) B1994539
theorem B2364539 : Blo 1574485 2364539 := bstep (se 1 (by rfl) ⟨1773404, by rfl⟩ : syracuseStep 2364539 = 3546809) B3546809
theorem B3544235 : Blo 1574485 3544235 := bstep (se 1 (by rfl) ⟨2658176, by rfl⟩ : syracuseStep 3544235 = 5316353) B5316353
theorem B2364665 : Blo 1574485 2364665 := bstep (se 2 (by rfl) ⟨886749, by rfl⟩ : syracuseStep 2364665 = 1773499) B1773499
theorem B4486529 : Blo 1574485 4486529 := bstep (se 2 (by rfl) ⟨1682448, by rfl⟩ : syracuseStep 4486529 = 3364897) B3364897
theorem B7976393 : Blo 1574485 7976393 := bstep (se 2 (by rfl) ⟨2991147, by rfl⟩ : syracuseStep 7976393 = 5982295) B5982295
theorem B2242171 : Blo 1574485 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B3987083 : Blo 1574485 3987083 := bstep (se 1 (by rfl) ⟨2990312, by rfl⟩ : syracuseStep 3987083 = 5980625) B5980625
theorem B5314247 : Blo 1574485 5314247 := bstep (se 1 (by rfl) ⟨3985685, by rfl⟩ : syracuseStep 5314247 = 7971371) B7971371
theorem B3544775 : Blo 1574485 3544775 := bstep (se 1 (by rfl) ⟨2658581, by rfl⟩ : syracuseStep 3544775 = 5317163) B5317163
theorem B2660087 : Blo 1574485 2660087 := bstep (se 1 (by rfl) ⟨1995065, by rfl⟩ : syracuseStep 2660087 = 3990131) B3990131
theorem B4486985 : Blo 1574485 4486985 := bstep (se 2 (by rfl) ⟨1682619, by rfl⟩ : syracuseStep 4486985 = 3365239) B3365239
theorem B2242399 : Blo 1574485 2242399 := bstep (se 1 (by rfl) ⟨1681799, by rfl⟩ : syracuseStep 2242399 = 3363599) B3363599
theorem B25556917 : Blo 1574485 25556917 := bstep (se 5 (by rfl) ⟨1197980, by rfl⟩ : syracuseStep 25556917 = 2395961) B2395961
theorem B6731707 : Blo 1574485 6731707 := bstep (se 1 (by rfl) ⟨5048780, by rfl⟩ : syracuseStep 6731707 = 10097561) B10097561
theorem B7977041 : Blo 1574485 7977041 := bstep (se 2 (by rfl) ⟨2991390, by rfl⟩ : syracuseStep 7977041 = 5982781) B5982781
theorem B8976541 : Blo 1574485 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B2242991 : Blo 1574485 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B5315111 : Blo 1574485 5315111 := bstep (se 1 (by rfl) ⟨3986333, by rfl⟩ : syracuseStep 5315111 = 7972667) B7972667
theorem B3545639 : Blo 1574485 3545639 := bstep (se 1 (by rfl) ⟨2659229, by rfl⟩ : syracuseStep 3545639 = 5318459) B5318459
theorem B11352635 : Blo 1574485 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B30300749 : Blo 1574485 30300749 := bstep (se 3 (by rfl) ⟨5681390, by rfl⟩ : syracuseStep 30300749 = 11362781) B11362781
theorem B20183687 : Blo 1574485 20183687 := bstep (se 1 (by rfl) ⟨15137765, by rfl⟩ : syracuseStep 20183687 = 30275531) B30275531
theorem B5315219 : Blo 1574485 5315219 := bstep (se 1 (by rfl) ⟨3986414, by rfl⟩ : syracuseStep 5315219 = 7972829) B7972829
theorem B9099985 : Blo 1574485 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B3988217 : Blo 1574485 3988217 := bstep (se 2 (by rfl) ⟨1495581, by rfl⟩ : syracuseStep 3988217 = 2991163) B2991163
theorem B5315435 : Blo 1574485 5315435 := bstep (se 1 (by rfl) ⟨3986576, by rfl⟩ : syracuseStep 5315435 = 7973153) B7973153
theorem B3545963 : Blo 1574485 3545963 := bstep (se 1 (by rfl) ⟨2659472, by rfl⟩ : syracuseStep 3545963 = 5318945) B5318945
theorem B4488043 : Blo 1574485 4488043 := bstep (se 1 (by rfl) ⟨3366032, by rfl⟩ : syracuseStep 4488043 = 6732065) B6732065
theorem B10091411 : Blo 1574485 10091411 := bstep (se 1 (by rfl) ⟨7568558, by rfl⟩ : syracuseStep 10091411 = 15137117) B15137117
theorem B5315489 : Blo 1574485 5315489 := bstep (se 2 (by rfl) ⟨1993308, by rfl⟩ : syracuseStep 5315489 = 3986617) B3986617
theorem B3546017 : Blo 1574485 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B3988399 : Blo 1574485 3988399 := bstep (se 1 (by rfl) ⟨2991299, by rfl⟩ : syracuseStep 3988399 = 5982599) B5982599
theorem B2989075 : Blo 1574485 2989075 := bstep (se 1 (by rfl) ⟨2241806, by rfl⟩ : syracuseStep 2989075 = 4483613) B4483613
theorem B6732953 : Blo 1574485 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B2129095 : Blo 1574485 2129095 := bstep (se 1 (by rfl) ⟨1596821, by rfl⟩ : syracuseStep 2129095 = 3193643) B3193643
theorem B12131531 : Blo 1574485 12131531 := bstep (se 1 (by rfl) ⟨9098648, by rfl⟩ : syracuseStep 12131531 = 18197297) B18197297
theorem B3546359 : Blo 1574485 3546359 := bstep (se 1 (by rfl) ⟨2659769, by rfl⟩ : syracuseStep 3546359 = 5319539) B5319539
theorem B3988865 : Blo 1574485 3988865 := bstep (se 2 (by rfl) ⟨1495824, by rfl⟩ : syracuseStep 3988865 = 2991649) B2991649
theorem B2522551 : Blo 1574485 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1596871 : Blo 1574485 1596871 := bstep (se 1 (by rfl) ⟨1197653, by rfl⟩ : syracuseStep 1596871 = 2395307) B2395307
theorem B5316083 : Blo 1574485 5316083 := bstep (se 1 (by rfl) ⟨3987062, by rfl⟩ : syracuseStep 5316083 = 7974125) B7974125
theorem B5045819 : Blo 1574485 5045819 := bstep (se 1 (by rfl) ⟨3784364, by rfl⟩ : syracuseStep 5045819 = 7568729) B7568729
theorem B28737089 : Blo 1574485 28737089 := bstep (se 2 (by rfl) ⟨10776408, by rfl⟩ : syracuseStep 28737089 = 21552817) B21552817
theorem B3194567 : Blo 1574485 3194567 := bstep (se 1 (by rfl) ⟨2395925, by rfl⟩ : syracuseStep 3194567 = 4791851) B4791851
theorem B2244295 : Blo 1574485 2244295 := bstep (se 1 (by rfl) ⟨1683221, by rfl⟩ : syracuseStep 2244295 = 3366443) B3366443
theorem B2129657 : Blo 1574485 2129657 := bstep (se 2 (by rfl) ⟨798621, by rfl⟩ : syracuseStep 2129657 = 1597243) B1597243
theorem B3989321 : Blo 1574485 3989321 := bstep (se 2 (by rfl) ⟨1495995, by rfl⟩ : syracuseStep 3989321 = 2991991) B2991991
theorem B3546953 : Blo 1574485 3546953 := bstep (se 2 (by rfl) ⟨1330107, by rfl⟩ : syracuseStep 3546953 = 2660215) B2660215
theorem B4857695 : Blo 1574485 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B17956727 : Blo 1574485 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B13451143 : Blo 1574485 13451143 := bstep (se 1 (by rfl) ⟨10088357, by rfl⟩ : syracuseStep 13451143 = 20176715) B20176715
theorem B1892279 : Blo 1574485 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B5980169 : Blo 1574485 5980169 := bstep (se 2 (by rfl) ⟨2242563, by rfl⟩ : syracuseStep 5980169 = 4485127) B4485127
theorem B3989513 : Blo 1574485 3989513 := bstep (se 2 (by rfl) ⟨1496067, by rfl⟩ : syracuseStep 3989513 = 2992135) B2992135
theorem B6144025 : Blo 1574485 6144025 := bstep (se 2 (by rfl) ⟨2304009, by rfl⟩ : syracuseStep 6144025 = 4608019) B4608019
theorem B13451417 : Blo 1574485 13451417 := bstep (se 2 (by rfl) ⟨5044281, by rfl⟩ : syracuseStep 13451417 = 10088563) B10088563
theorem B11968721 : Blo 1574485 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B3195361 : Blo 1574485 3195361 := bstep (se 2 (by rfl) ⟨1198260, by rfl⟩ : syracuseStep 3195361 = 2396521) B2396521
theorem B11969207 : Blo 1574485 11969207 := bstep (se 1 (by rfl) ⟨8976905, by rfl⟩ : syracuseStep 11969207 = 17953811) B17953811
theorem B2991019 : Blo 1574485 2991019 := bstep (se 1 (by rfl) ⟨2243264, by rfl⟩ : syracuseStep 2991019 = 4486529) B4486529
theorem B12133313 : Blo 1574485 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B5317595 : Blo 1574485 5317595 := bstep (se 1 (by rfl) ⟨3988196, by rfl⟩ : syracuseStep 5317595 = 7976393) B7976393
theorem B43107389 : Blo 1574485 43107389 := bstep (se 3 (by rfl) ⟨8082635, by rfl⟩ : syracuseStep 43107389 = 16165271) B16165271
theorem B5981309 : Blo 1574485 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B5317757 : Blo 1574485 5317757 := bstep (se 3 (by rfl) ⟨997079, by rfl⟩ : syracuseStep 5317757 = 1994159) B1994159
theorem B2991323 : Blo 1574485 2991323 := bstep (se 1 (by rfl) ⟨2243492, by rfl⟩ : syracuseStep 2991323 = 4486985) B4486985
theorem B5317865 : Blo 1574485 5317865 := bstep (se 2 (by rfl) ⟨1994199, by rfl⟩ : syracuseStep 5317865 = 3988399) B3988399
theorem B7980281 : Blo 1574485 7980281 := bstep (se 2 (by rfl) ⟨2992605, by rfl⟩ : syracuseStep 7980281 = 5985211) B5985211
theorem B5318027 : Blo 1574485 5318027 := bstep (se 1 (by rfl) ⟨3988520, by rfl⟩ : syracuseStep 5318027 = 7977041) B7977041
theorem B5916043 : Blo 1574485 5916043 := bstep (se 1 (by rfl) ⟨4437032, by rfl⟩ : syracuseStep 5916043 = 8874065) B8874065
theorem B4548029 : Blo 1574485 4548029 := bstep (se 3 (by rfl) ⟨852755, by rfl⟩ : syracuseStep 4548029 = 1705511) B1705511
theorem B1574623 : Blo 1574485 1574623 := bstep (se 1 (by rfl) ⟨1180967, by rfl⟩ : syracuseStep 1574623 = 2361935) B2361935
theorem B1574703 : Blo 1574485 1574703 := bstep (se 1 (by rfl) ⟨1181027, by rfl⟩ : syracuseStep 1574703 = 2362055) B2362055
theorem B1574811 : Blo 1574485 1574811 := bstep (se 1 (by rfl) ⟨1181108, by rfl⟩ : syracuseStep 1574811 = 2362217) B2362217
theorem B6727607 : Blo 1574485 6727607 := bstep (se 1 (by rfl) ⟨5045705, by rfl⟩ : syracuseStep 6727607 = 10091411) B10091411
theorem B17024975 : Blo 1574485 17024975 := bstep (se 1 (by rfl) ⟨12768731, by rfl⟩ : syracuseStep 17024975 = 25537463) B25537463
theorem B1574863 : Blo 1574485 1574863 := bstep (se 1 (by rfl) ⟨1181147, by rfl⟩ : syracuseStep 1574863 = 2362295) B2362295
theorem B2557903 : Blo 1574485 2557903 := bstep (se 1 (by rfl) ⟨1918427, by rfl⟩ : syracuseStep 2557903 = 3836855) B3836855
theorem B1574887 : Blo 1574485 1574887 := bstep (se 1 (by rfl) ⟨1181165, by rfl⟩ : syracuseStep 1574887 = 2362331) B2362331
theorem B5679085 : Blo 1574485 5679085 := bstep (se 3 (by rfl) ⟨1064828, by rfl⟩ : syracuseStep 5679085 = 2129657) B2129657
theorem B24250373 : Blo 1574485 24250373 := bstep (se 4 (by rfl) ⟨2273472, by rfl⟩ : syracuseStep 24250373 = 4546945) B4546945
theorem B20465669 : Blo 1574485 20465669 := bstep (se 4 (by rfl) ⟨1918656, by rfl⟩ : syracuseStep 20465669 = 3837313) B3837313
theorem B8087687 : Blo 1574485 8087687 := bstep (se 1 (by rfl) ⟨6065765, by rfl⟩ : syracuseStep 8087687 = 12131531) B12131531
theorem B2992393 : Blo 1574485 2992393 := bstep (se 2 (by rfl) ⟨1122147, by rfl⟩ : syracuseStep 2992393 = 2244295) B2244295
theorem B1771807 : Blo 1574485 1771807 := bstep (se 1 (by rfl) ⟨1328855, by rfl⟩ : syracuseStep 1771807 = 2657711) B2657711
theorem B1575199 : Blo 1574485 1575199 := bstep (se 1 (by rfl) ⟨1181399, by rfl⟩ : syracuseStep 1575199 = 2362799) B2362799
theorem B1575259 : Blo 1574485 1575259 := bstep (se 1 (by rfl) ⟨1181444, by rfl⟩ : syracuseStep 1575259 = 2362889) B2362889
theorem B1575279 : Blo 1574485 1575279 := bstep (se 1 (by rfl) ⟨1181459, by rfl⟩ : syracuseStep 1575279 = 2362919) B2362919
theorem B2361767 : Blo 1574485 2361767 := bstep (se 1 (by rfl) ⟨1771325, by rfl⟩ : syracuseStep 2361767 = 3542651) B3542651
theorem B1575335 : Blo 1574485 1575335 := bstep (se 1 (by rfl) ⟨1181501, by rfl⟩ : syracuseStep 1575335 = 2363003) B2363003
theorem B2361851 : Blo 1574485 2361851 := bstep (se 1 (by rfl) ⟨1771388, by rfl⟩ : syracuseStep 2361851 = 3542777) B3542777
theorem B1575419 : Blo 1574485 1575419 := bstep (se 1 (by rfl) ⟨1181564, by rfl⟩ : syracuseStep 1575419 = 2363129) B2363129
theorem B17934857 : Blo 1574485 17934857 := bstep (se 2 (by rfl) ⟨6725571, by rfl⟩ : syracuseStep 17934857 = 13451143) B13451143
theorem B1772095 : Blo 1574485 1772095 := bstep (se 1 (by rfl) ⟨1329071, by rfl⟩ : syracuseStep 1772095 = 2658143) B2658143
theorem B1575487 : Blo 1574485 1575487 := bstep (se 1 (by rfl) ⟨1181615, by rfl⟩ : syracuseStep 1575487 = 2363231) B2363231
theorem B3238463 : Blo 1574485 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B1575495 : Blo 1574485 1575495 := bstep (se 1 (by rfl) ⟨1181621, by rfl⟩ : syracuseStep 1575495 = 2363243) B2363243
theorem B11971151 : Blo 1574485 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B8522347 : Blo 1574485 8522347 := bstep (se 1 (by rfl) ⟨6391760, by rfl⟩ : syracuseStep 8522347 = 12783521) B12783521
theorem B2361977 : Blo 1574485 2361977 := bstep (se 2 (by rfl) ⟨885741, by rfl⟩ : syracuseStep 2361977 = 1771483) B1771483
theorem B2362031 : Blo 1574485 2362031 := bstep (se 1 (by rfl) ⟨1771523, by rfl⟩ : syracuseStep 2362031 = 3543047) B3543047
theorem B2362079 : Blo 1574485 2362079 := bstep (se 1 (by rfl) ⟨1771559, by rfl⟩ : syracuseStep 2362079 = 3543119) B3543119
theorem B1575647 : Blo 1574485 1575647 := bstep (se 1 (by rfl) ⟨1181735, by rfl⟩ : syracuseStep 1575647 = 2363471) B2363471
theorem B28756727 : Blo 1574485 28756727 := bstep (se 1 (by rfl) ⟨21567545, by rfl⟩ : syracuseStep 28756727 = 43135091) B43135091
theorem B1575727 : Blo 1574485 1575727 := bstep (se 1 (by rfl) ⟨1181795, by rfl⟩ : syracuseStep 1575727 = 2363591) B2363591
theorem B1575835 : Blo 1574485 1575835 := bstep (se 1 (by rfl) ⟨1181876, by rfl⟩ : syracuseStep 1575835 = 2363753) B2363753
theorem B4484011 : Blo 1574485 4484011 := bstep (se 1 (by rfl) ⟨3363008, by rfl⟩ : syracuseStep 4484011 = 6726017) B6726017
theorem B1575887 : Blo 1574485 1575887 := bstep (se 1 (by rfl) ⟨1181915, by rfl⟩ : syracuseStep 1575887 = 2363831) B2363831
theorem B2362343 : Blo 1574485 2362343 := bstep (se 1 (by rfl) ⟨1771757, by rfl⟩ : syracuseStep 2362343 = 3543515) B3543515
theorem B1575911 : Blo 1574485 1575911 := bstep (se 1 (by rfl) ⟨1181933, by rfl⟩ : syracuseStep 1575911 = 2363867) B2363867
theorem B4484285 : Blo 1574485 4484285 := bstep (se 3 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 4484285 = 1681607) B1681607
theorem B2362601 : Blo 1574485 2362601 := bstep (se 2 (by rfl) ⟨885975, by rfl⟩ : syracuseStep 2362601 = 1771951) B1771951
theorem B2362655 : Blo 1574485 2362655 := bstep (se 1 (by rfl) ⟨1771991, by rfl⟩ : syracuseStep 2362655 = 3543983) B3543983
theorem B1576223 : Blo 1574485 1576223 := bstep (se 1 (by rfl) ⟨1182167, by rfl⟩ : syracuseStep 1576223 = 2364335) B2364335
theorem B1576283 : Blo 1574485 1576283 := bstep (se 1 (by rfl) ⟨1182212, by rfl⟩ : syracuseStep 1576283 = 2364425) B2364425
theorem B1576303 : Blo 1574485 1576303 := bstep (se 1 (by rfl) ⟨1182227, by rfl⟩ : syracuseStep 1576303 = 2364455) B2364455
theorem B1772923 : Blo 1574485 1772923 := bstep (se 1 (by rfl) ⟨1329692, by rfl⟩ : syracuseStep 1772923 = 2659385) B2659385
theorem B1576359 : Blo 1574485 1576359 := bstep (se 1 (by rfl) ⟨1182269, by rfl⟩ : syracuseStep 1576359 = 2364539) B2364539
theorem B2362823 : Blo 1574485 2362823 := bstep (se 1 (by rfl) ⟨1772117, by rfl⟩ : syracuseStep 2362823 = 3544235) B3544235
theorem B2657785 : Blo 1574485 2657785 := bstep (se 2 (by rfl) ⟨996669, by rfl⟩ : syracuseStep 2657785 = 1993339) B1993339
theorem B1576443 : Blo 1574485 1576443 := bstep (se 1 (by rfl) ⟨1182332, by rfl⟩ : syracuseStep 1576443 = 2364665) B2364665
theorem B1994311 : Blo 1574485 1994311 := bstep (se 1 (by rfl) ⟨1495733, by rfl⟩ : syracuseStep 1994311 = 2991467) B2991467
theorem B6729331 : Blo 1574485 6729331 := bstep (se 1 (by rfl) ⟨5046998, by rfl⟩ : syracuseStep 6729331 = 10093997) B10093997
theorem B5680801 : Blo 1574485 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B1683119 : Blo 1574485 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B7974611 : Blo 1574485 7974611 := bstep (se 1 (by rfl) ⟨5980958, by rfl⟩ : syracuseStep 7974611 = 11961917) B11961917
theorem B2658055 : Blo 1574485 2658055 := bstep (se 1 (by rfl) ⟨1993541, by rfl⟩ : syracuseStep 2658055 = 3987083) B3987083
theorem B2658089 : Blo 1574485 2658089 := bstep (se 2 (by rfl) ⟨996783, by rfl⟩ : syracuseStep 2658089 = 1993567) B1993567
theorem B2363177 : Blo 1574485 2363177 := bstep (se 2 (by rfl) ⟨886191, by rfl⟩ : syracuseStep 2363177 = 1772383) B1772383
theorem B3542831 : Blo 1574485 3542831 := bstep (se 1 (by rfl) ⟨2657123, by rfl⟩ : syracuseStep 3542831 = 5314247) B5314247
theorem B2363183 : Blo 1574485 2363183 := bstep (se 1 (by rfl) ⟨1772387, by rfl⟩ : syracuseStep 2363183 = 3544775) B3544775
theorem B5984057 : Blo 1574485 5984057 := bstep (se 2 (by rfl) ⟨2244021, by rfl⟩ : syracuseStep 5984057 = 4488043) B4488043
theorem B1773391 : Blo 1574485 1773391 := bstep (se 1 (by rfl) ⟨1330043, by rfl⟩ : syracuseStep 1773391 = 2660087) B2660087
theorem B3985433 : Blo 1574485 3985433 := bstep (se 2 (by rfl) ⟨1494537, by rfl⟩ : syracuseStep 3985433 = 2989075) B2989075
theorem B13455517 : Blo 1574485 13455517 := bstep (se 3 (by rfl) ⟨2522909, by rfl⟩ : syracuseStep 13455517 = 5045819) B5045819
theorem B2838793 : Blo 1574485 2838793 := bstep (se 2 (by rfl) ⟨1064547, by rfl⟩ : syracuseStep 2838793 = 2129095) B2129095
theorem B2363657 : Blo 1574485 2363657 := bstep (se 2 (by rfl) ⟨886371, by rfl⟩ : syracuseStep 2363657 = 1772743) B1772743
theorem B10096969 : Blo 1574485 10096969 := bstep (se 2 (by rfl) ⟨3786363, by rfl⟩ : syracuseStep 10096969 = 7572727) B7572727
theorem B7975259 : Blo 1574485 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B3543407 : Blo 1574485 3543407 := bstep (se 1 (by rfl) ⟨2657555, by rfl⟩ : syracuseStep 3543407 = 5315111) B5315111
theorem B2363759 : Blo 1574485 2363759 := bstep (se 1 (by rfl) ⟨1772819, by rfl⟩ : syracuseStep 2363759 = 3545639) B3545639
theorem B1995131 : Blo 1574485 1995131 := bstep (se 1 (by rfl) ⟨1496348, by rfl⟩ : syracuseStep 1995131 = 2992697) B2992697
theorem B13455791 : Blo 1574485 13455791 := bstep (se 1 (by rfl) ⟨10091843, by rfl⟩ : syracuseStep 13455791 = 20183687) B20183687
theorem B3543479 : Blo 1574485 3543479 := bstep (se 1 (by rfl) ⟨2657609, by rfl⟩ : syracuseStep 3543479 = 5315219) B5315219
theorem B2658811 : Blo 1574485 2658811 := bstep (se 1 (by rfl) ⟨1994108, by rfl⟩ : syracuseStep 2658811 = 3988217) B3988217
theorem B3543623 : Blo 1574485 3543623 := bstep (se 1 (by rfl) ⟨2657717, by rfl⟩ : syracuseStep 3543623 = 5315435) B5315435
theorem B2363975 : Blo 1574485 2363975 := bstep (se 1 (by rfl) ⟨1772981, by rfl⟩ : syracuseStep 2363975 = 3545963) B3545963
theorem B3363401 : Blo 1574485 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B3543659 : Blo 1574485 3543659 := bstep (se 1 (by rfl) ⟨2657744, by rfl⟩ : syracuseStep 3543659 = 5315489) B5315489
theorem B2364011 : Blo 1574485 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B2364239 : Blo 1574485 2364239 := bstep (se 1 (by rfl) ⟨1773179, by rfl⟩ : syracuseStep 2364239 = 3546359) B3546359
theorem B2659243 : Blo 1574485 2659243 := bstep (se 1 (by rfl) ⟨1994432, by rfl⟩ : syracuseStep 2659243 = 3988865) B3988865
theorem B15143881 : Blo 1574485 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B3544055 : Blo 1574485 3544055 := bstep (se 1 (by rfl) ⟨2658041, by rfl⟩ : syracuseStep 3544055 = 5316083) B5316083
theorem B19158059 : Blo 1574485 19158059 := bstep (se 1 (by rfl) ⟨14368544, by rfl⟩ : syracuseStep 19158059 = 28737089) B28737089
theorem B8967293 : Blo 1574485 8967293 := bstep (se 3 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 8967293 = 3362735) B3362735
theorem B5387411 : Blo 1574485 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B2659547 : Blo 1574485 2659547 := bstep (se 1 (by rfl) ⟨1994660, by rfl⟩ : syracuseStep 2659547 = 3989321) B3989321
theorem B2364635 : Blo 1574485 2364635 := bstep (se 1 (by rfl) ⟨1773476, by rfl⟩ : syracuseStep 2364635 = 3546953) B3546953
theorem B34075889 : Blo 1574485 34075889 := bstep (se 2 (by rfl) ⟨12778458, by rfl⟩ : syracuseStep 34075889 = 25556917) B25556917
theorem B8975609 : Blo 1574485 8975609 := bstep (se 2 (by rfl) ⟨3365853, by rfl⟩ : syracuseStep 8975609 = 6731707) B6731707
theorem B11957543 : Blo 1574485 11957543 := bstep (se 1 (by rfl) ⟨8968157, by rfl⟩ : syracuseStep 11957543 = 17936315) B17936315
theorem B7976231 : Blo 1574485 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B3544415 : Blo 1574485 3544415 := bstep (se 1 (by rfl) ⟨2658311, by rfl⟩ : syracuseStep 3544415 = 5316623) B5316623
theorem B11515297 : Blo 1574485 11515297 := bstep (se 2 (by rfl) ⟨4318236, by rfl⟩ : syracuseStep 11515297 = 8636473) B8636473
theorem B5985697 : Blo 1574485 5985697 := bstep (se 2 (by rfl) ⟨2244636, by rfl⟩ : syracuseStep 5985697 = 4489273) B4489273
theorem B2659783 : Blo 1574485 2659783 := bstep (se 1 (by rfl) ⟨1994837, by rfl⟩ : syracuseStep 2659783 = 3989675) B3989675
theorem B16176647 : Blo 1574485 16176647 := bstep (se 1 (by rfl) ⟨12132485, by rfl⟩ : syracuseStep 16176647 = 24264971) B24264971
theorem B32347781 : Blo 1574485 32347781 := bstep (se 4 (by rfl) ⟨3032604, by rfl⟩ : syracuseStep 32347781 = 6065209) B6065209
theorem B3544811 : Blo 1574485 3544811 := bstep (se 1 (by rfl) ⟨2658608, by rfl⟩ : syracuseStep 3544811 = 5317217) B5317217
theorem B3364649 : Blo 1574485 3364649 := bstep (se 2 (by rfl) ⟨1261743, by rfl⟩ : syracuseStep 3364649 = 2523487) B2523487
theorem B5314409 : Blo 1574485 5314409 := bstep (se 2 (by rfl) ⟨1992903, by rfl⟩ : syracuseStep 5314409 = 3985807) B3985807
theorem B3544937 : Blo 1574485 3544937 := bstep (se 2 (by rfl) ⟨1329351, by rfl⟩ : syracuseStep 3544937 = 2658703) B2658703
theorem B3987407 : Blo 1574485 3987407 := bstep (se 1 (by rfl) ⟨2990555, by rfl⟩ : syracuseStep 3987407 = 5981111) B5981111
theorem B2660303 : Blo 1574485 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B5978393 : Blo 1574485 5978393 := bstep (se 2 (by rfl) ⟨2241897, by rfl⟩ : syracuseStep 5978393 = 4483795) B4483795
theorem B5314841 : Blo 1574485 5314841 := bstep (se 2 (by rfl) ⟨1993065, by rfl⟩ : syracuseStep 5314841 = 3986131) B3986131
theorem B3988075 : Blo 1574485 3988075 := bstep (se 1 (by rfl) ⟨2991056, by rfl⟩ : syracuseStep 3988075 = 5982113) B5982113
theorem B30268079 : Blo 1574485 30268079 := bstep (se 1 (by rfl) ⟨22701059, by rfl⟩ : syracuseStep 30268079 = 45402119) B45402119
theorem B3545783 : Blo 1574485 3545783 := bstep (se 1 (by rfl) ⟨2659337, by rfl⟩ : syracuseStep 3545783 = 5318675) B5318675
theorem B129350357 : Blo 1574485 129350357 := bstep (se 7 (by rfl) ⟨1515824, by rfl⟩ : syracuseStep 129350357 = 3031649) B3031649
theorem B3545999 : Blo 1574485 3545999 := bstep (se 1 (by rfl) ⟨2659499, by rfl⟩ : syracuseStep 3545999 = 5318999) B5318999
theorem B3988379 : Blo 1574485 3988379 := bstep (se 1 (by rfl) ⟨2991284, by rfl⟩ : syracuseStep 3988379 = 5982569) B5982569
theorem B7183399 : Blo 1574485 7183399 := bstep (se 1 (by rfl) ⟨5387549, by rfl⟩ : syracuseStep 7183399 = 10775099) B10775099
theorem B7568423 : Blo 1574485 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B20200499 : Blo 1574485 20200499 := bstep (se 1 (by rfl) ⟨15150374, by rfl⟩ : syracuseStep 20200499 = 30300749) B30300749
theorem B6732989 : Blo 1574485 6732989 := bstep (se 3 (by rfl) ⟨1262435, by rfl⟩ : syracuseStep 6732989 = 2524871) B2524871
theorem B3988723 : Blo 1574485 3988723 := bstep (se 1 (by rfl) ⟨2991542, by rfl⟩ : syracuseStep 3988723 = 5983085) B5983085
theorem B2129161 : Blo 1574485 2129161 := bstep (se 2 (by rfl) ⟨798435, by rfl⟩ : syracuseStep 2129161 = 1596871) B1596871
theorem B17947979 : Blo 1574485 17947979 := bstep (se 1 (by rfl) ⟨13460984, by rfl⟩ : syracuseStep 17947979 = 26921969) B26921969
theorem B7978337 : Blo 1574485 7978337 := bstep (se 2 (by rfl) ⟨2991876, by rfl⟩ : syracuseStep 7978337 = 5983753) B5983753
theorem B34061705 : Blo 1574485 34061705 := bstep (se 2 (by rfl) ⟨12773139, by rfl⟩ : syracuseStep 34061705 = 25546279) B25546279
theorem B4488635 : Blo 1574485 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B2989561 : Blo 1574485 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B5316191 : Blo 1574485 5316191 := bstep (se 1 (by rfl) ⟨3987143, by rfl⟩ : syracuseStep 5316191 = 7974287) B7974287
theorem B3546719 : Blo 1574485 3546719 := bstep (se 1 (by rfl) ⟨2660039, by rfl⟩ : syracuseStep 3546719 = 5320079) B5320079
theorem B94576349 : Blo 1574485 94576349 := bstep (se 3 (by rfl) ⟨17733065, by rfl⟩ : syracuseStep 94576349 = 35466131) B35466131
theorem B2989865 : Blo 1574485 2989865 := bstep (se 2 (by rfl) ⟨1121199, by rfl⟩ : syracuseStep 2989865 = 2242399) B2242399
theorem B2129711 : Blo 1574485 2129711 := bstep (se 1 (by rfl) ⟨1597283, by rfl⟩ : syracuseStep 2129711 = 3194567) B3194567
theorem B3546935 : Blo 1574485 3546935 := bstep (se 1 (by rfl) ⟨2660201, by rfl⟩ : syracuseStep 3546935 = 5320403) B5320403
theorem B5046077 : Blo 1574485 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B54575117 : Blo 1574485 54575117 := bstep (se 3 (by rfl) ⟨10232834, by rfl⟩ : syracuseStep 54575117 = 20465669) B20465669
theorem B8192033 : Blo 1574485 8192033 := bstep (se 2 (by rfl) ⟨3072012, by rfl⟩ : syracuseStep 8192033 = 6144025) B6144025
theorem B7979147 : Blo 1574485 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B17940689 : Blo 1574485 17940689 := bstep (se 2 (by rfl) ⟨6727758, by rfl⟩ : syracuseStep 17940689 = 13455517) B13455517
theorem B5316839 : Blo 1574485 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B8970527 : Blo 1574485 8970527 := bstep (se 1 (by rfl) ⟨6727895, by rfl⟩ : syracuseStep 8970527 = 13455791) B13455791
theorem B3785057 : Blo 1574485 3785057 := bstep (se 2 (by rfl) ⟨1419396, by rfl⟩ : syracuseStep 3785057 = 2838793) B2838793
theorem B3989857 : Blo 1574485 3989857 := bstep (se 2 (by rfl) ⟨1496196, by rfl⟩ : syracuseStep 3989857 = 2992393) B2992393
theorem B7979471 : Blo 1574485 7979471 := bstep (se 1 (by rfl) ⟨5984603, by rfl⟩ : syracuseStep 7979471 = 11969207) B11969207
theorem B4260481 : Blo 1574485 4260481 := bstep (se 2 (by rfl) ⟨1597680, by rfl⟩ : syracuseStep 4260481 = 3195361) B3195361
theorem B12772039 : Blo 1574485 12772039 := bstep (se 1 (by rfl) ⟨9579029, by rfl⟩ : syracuseStep 12772039 = 19158059) B19158059
theorem B28738259 : Blo 1574485 28738259 := bstep (se 1 (by rfl) ⟨21553694, by rfl⟩ : syracuseStep 28738259 = 43107389) B43107389
theorem B5317433 : Blo 1574485 5317433 := bstep (se 2 (by rfl) ⟨1994037, by rfl⟩ : syracuseStep 5317433 = 3988075) B3988075
theorem B11363129 : Blo 1574485 11363129 := bstep (se 2 (by rfl) ⟨4261173, by rfl⟩ : syracuseStep 11363129 = 8522347) B8522347
theorem B22717259 : Blo 1574485 22717259 := bstep (se 1 (by rfl) ⟨17037944, by rfl⟩ : syracuseStep 22717259 = 34075889) B34075889
theorem B7971695 : Blo 1574485 7971695 := bstep (se 1 (by rfl) ⟨5978771, by rfl⟩ : syracuseStep 7971695 = 11957543) B11957543
theorem B5317487 : Blo 1574485 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B11969693 : Blo 1574485 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B9577865 : Blo 1574485 9577865 := bstep (se 2 (by rfl) ⟨3591699, by rfl⟩ : syracuseStep 9577865 = 7183399) B7183399
theorem B5391791 : Blo 1574485 5391791 := bstep (se 1 (by rfl) ⟨4043843, by rfl⟩ : syracuseStep 5391791 = 8087687) B8087687
theorem B8635901 : Blo 1574485 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B1574511 : Blo 1574485 1574511 := bstep (se 1 (by rfl) ⟨1180883, by rfl⟩ : syracuseStep 1574511 = 2361767) B2361767
theorem B5318297 : Blo 1574485 5318297 := bstep (se 2 (by rfl) ⟨1994361, by rfl⟩ : syracuseStep 5318297 = 3988723) B3988723
theorem B1574567 : Blo 1574485 1574567 := bstep (se 1 (by rfl) ⟨1180925, by rfl⟩ : syracuseStep 1574567 = 2361851) B2361851
theorem B7980767 : Blo 1574485 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B1574651 : Blo 1574485 1574651 := bstep (se 1 (by rfl) ⟨1180988, by rfl⟩ : syracuseStep 1574651 = 2361977) B2361977
theorem B20178719 : Blo 1574485 20178719 := bstep (se 1 (by rfl) ⟨15134039, by rfl⟩ : syracuseStep 20178719 = 30268079) B30268079
theorem B1574687 : Blo 1574485 1574687 := bstep (se 1 (by rfl) ⟨1181015, by rfl⟩ : syracuseStep 1574687 = 2362031) B2362031
theorem B1574719 : Blo 1574485 1574719 := bstep (se 1 (by rfl) ⟨1181039, by rfl⟩ : syracuseStep 1574719 = 2362079) B2362079
theorem B19171151 : Blo 1574485 19171151 := bstep (se 1 (by rfl) ⟨14378363, by rfl⟩ : syracuseStep 19171151 = 28756727) B28756727
theorem B15353729 : Blo 1574485 15353729 := bstep (se 2 (by rfl) ⟨5757648, by rfl⟩ : syracuseStep 15353729 = 11515297) B11515297
theorem B7980929 : Blo 1574485 7980929 := bstep (se 2 (by rfl) ⟨2992848, by rfl⟩ : syracuseStep 7980929 = 5985697) B5985697
theorem B1574895 : Blo 1574485 1574895 := bstep (se 1 (by rfl) ⟨1181171, by rfl⟩ : syracuseStep 1574895 = 2362343) B2362343
theorem B5679229 : Blo 1574485 5679229 := bstep (se 3 (by rfl) ⟨1064855, by rfl⟩ : syracuseStep 5679229 = 2129711) B2129711
theorem B8972441 : Blo 1574485 8972441 := bstep (se 2 (by rfl) ⟨3364665, by rfl⟩ : syracuseStep 8972441 = 6729331) B6729331
theorem B1575067 : Blo 1574485 1575067 := bstep (se 1 (by rfl) ⟨1181300, by rfl⟩ : syracuseStep 1575067 = 2362601) B2362601
theorem B1575103 : Blo 1574485 1575103 := bstep (se 1 (by rfl) ⟨1181327, by rfl⟩ : syracuseStep 1575103 = 2362655) B2362655
theorem B5318891 : Blo 1574485 5318891 := bstep (se 1 (by rfl) ⟨3989168, by rfl⟩ : syracuseStep 5318891 = 7978337) B7978337
theorem B1575215 : Blo 1574485 1575215 := bstep (se 1 (by rfl) ⟨1181411, by rfl⟩ : syracuseStep 1575215 = 2362823) B2362823
theorem B1993243 : Blo 1574485 1993243 := bstep (se 1 (by rfl) ⟨1494932, by rfl⟩ : syracuseStep 1993243 = 2989865) B2989865
theorem B1772059 : Blo 1574485 1772059 := bstep (se 1 (by rfl) ⟨1329044, by rfl⟩ : syracuseStep 1772059 = 2658089) B2658089
theorem B1575451 : Blo 1574485 1575451 := bstep (se 1 (by rfl) ⟨1181588, by rfl⟩ : syracuseStep 1575451 = 2363177) B2363177
theorem B2361887 : Blo 1574485 2361887 := bstep (se 1 (by rfl) ⟨1771415, by rfl⟩ : syracuseStep 2361887 = 3542831) B3542831
theorem B1575455 : Blo 1574485 1575455 := bstep (se 1 (by rfl) ⟨1181591, by rfl⟩ : syracuseStep 1575455 = 2363183) B2363183
theorem B3410537 : Blo 1574485 3410537 := bstep (se 2 (by rfl) ⟨1278951, by rfl⟩ : syracuseStep 3410537 = 2557903) B2557903
theorem B7572113 : Blo 1574485 7572113 := bstep (se 2 (by rfl) ⟨2839542, by rfl⟩ : syracuseStep 7572113 = 5679085) B5679085
theorem B2656955 : Blo 1574485 2656955 := bstep (se 1 (by rfl) ⟨1992716, by rfl⟩ : syracuseStep 2656955 = 3985433) B3985433
theorem B1575771 : Blo 1574485 1575771 := bstep (se 1 (by rfl) ⟨1181828, by rfl⟩ : syracuseStep 1575771 = 2363657) B2363657
theorem B2362271 : Blo 1574485 2362271 := bstep (se 1 (by rfl) ⟨1771703, by rfl⟩ : syracuseStep 2362271 = 3543407) B3543407
theorem B1575839 : Blo 1574485 1575839 := bstep (se 1 (by rfl) ⟨1181879, by rfl⟩ : syracuseStep 1575839 = 2363759) B2363759
theorem B2362319 : Blo 1574485 2362319 := bstep (se 1 (by rfl) ⟨1771739, by rfl⟩ : syracuseStep 2362319 = 3543479) B3543479
theorem B2362409 : Blo 1574485 2362409 := bstep (se 2 (by rfl) ⟨885903, by rfl⟩ : syracuseStep 2362409 = 1771807) B1771807
theorem B2362415 : Blo 1574485 2362415 := bstep (se 1 (by rfl) ⟨1771811, by rfl⟩ : syracuseStep 2362415 = 3543623) B3543623
theorem B1575983 : Blo 1574485 1575983 := bstep (se 1 (by rfl) ⟨1181987, by rfl⟩ : syracuseStep 1575983 = 2363975) B2363975
theorem B2362439 : Blo 1574485 2362439 := bstep (se 1 (by rfl) ⟨1771829, by rfl⟩ : syracuseStep 2362439 = 3543659) B3543659
theorem B1576007 : Blo 1574485 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B13462625 : Blo 1574485 13462625 := bstep (se 2 (by rfl) ⟨5048484, by rfl⟩ : syracuseStep 13462625 = 10096969) B10096969
theorem B1576159 : Blo 1574485 1576159 := bstep (se 1 (by rfl) ⟨1182119, by rfl⟩ : syracuseStep 1576159 = 2364239) B2364239
theorem B8088875 : Blo 1574485 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B2362703 : Blo 1574485 2362703 := bstep (se 1 (by rfl) ⟨1772027, by rfl⟩ : syracuseStep 2362703 = 3544055) B3544055
theorem B2362793 : Blo 1574485 2362793 := bstep (se 2 (by rfl) ⟨886047, by rfl⟩ : syracuseStep 2362793 = 1772095) B1772095
theorem B3591607 : Blo 1574485 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B1994215 : Blo 1574485 1994215 := bstep (se 1 (by rfl) ⟨1495661, by rfl⟩ : syracuseStep 1994215 = 2991323) B2991323
theorem B1773031 : Blo 1574485 1773031 := bstep (se 1 (by rfl) ⟨1329773, by rfl⟩ : syracuseStep 1773031 = 2659547) B2659547
theorem B1576423 : Blo 1574485 1576423 := bstep (se 1 (by rfl) ⟨1182317, by rfl⟩ : syracuseStep 1576423 = 2364635) B2364635
theorem B5983739 : Blo 1574485 5983739 := bstep (se 1 (by rfl) ⟨4487804, by rfl⟩ : syracuseStep 5983739 = 8975609) B8975609
theorem B5320187 : Blo 1574485 5320187 := bstep (se 1 (by rfl) ⟨3990140, by rfl⟩ : syracuseStep 5320187 = 7980281) B7980281
theorem B2362943 : Blo 1574485 2362943 := bstep (se 1 (by rfl) ⟨1772207, by rfl⟩ : syracuseStep 2362943 = 3544415) B3544415
theorem B5320349 : Blo 1574485 5320349 := bstep (se 3 (by rfl) ⟨997565, by rfl⟩ : syracuseStep 5320349 = 1995131) B1995131
theorem B10784431 : Blo 1574485 10784431 := bstep (se 1 (by rfl) ⟨8088323, by rfl⟩ : syracuseStep 10784431 = 16176647) B16176647
theorem B21565187 : Blo 1574485 21565187 := bstep (se 1 (by rfl) ⟨16173890, by rfl⟩ : syracuseStep 21565187 = 32347781) B32347781
theorem B2363207 : Blo 1574485 2363207 := bstep (se 1 (by rfl) ⟨1772405, by rfl⟩ : syracuseStep 2363207 = 3544811) B3544811
theorem B12128077 : Blo 1574485 12128077 := bstep (se 3 (by rfl) ⟨2274014, by rfl⟩ : syracuseStep 12128077 = 4548029) B4548029
theorem B3542939 : Blo 1574485 3542939 := bstep (se 1 (by rfl) ⟨2657204, by rfl⟩ : syracuseStep 3542939 = 5314409) B5314409
theorem B2363291 : Blo 1574485 2363291 := bstep (se 1 (by rfl) ⟨1772468, by rfl⟩ : syracuseStep 2363291 = 3544937) B3544937
theorem B4485071 : Blo 1574485 4485071 := bstep (se 1 (by rfl) ⟨3363803, by rfl⟩ : syracuseStep 4485071 = 6727607) B6727607
theorem B11349983 : Blo 1574485 11349983 := bstep (se 1 (by rfl) ⟨8512487, by rfl⟩ : syracuseStep 11349983 = 17024975) B17024975
theorem B2658271 : Blo 1574485 2658271 := bstep (se 1 (by rfl) ⟨1993703, by rfl⟩ : syracuseStep 2658271 = 3987407) B3987407
theorem B1773535 : Blo 1574485 1773535 := bstep (se 1 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 1773535 = 2660303) B2660303
theorem B16166915 : Blo 1574485 16166915 := bstep (se 1 (by rfl) ⟨12125186, by rfl⟩ : syracuseStep 16166915 = 24250373) B24250373
theorem B3985595 : Blo 1574485 3985595 := bstep (se 1 (by rfl) ⟨2989196, by rfl⟩ : syracuseStep 3985595 = 5978393) B5978393
theorem B3543227 : Blo 1574485 3543227 := bstep (se 1 (by rfl) ⟨2657420, by rfl⟩ : syracuseStep 3543227 = 5314841) B5314841
theorem B11956571 : Blo 1574485 11956571 := bstep (se 1 (by rfl) ⟨8967428, by rfl⟩ : syracuseStep 11956571 = 17934857) B17934857
theorem B2838881 : Blo 1574485 2838881 := bstep (se 2 (by rfl) ⟨1064580, by rfl⟩ : syracuseStep 2838881 = 2129161) B2129161
theorem B2363855 : Blo 1574485 2363855 := bstep (se 1 (by rfl) ⟨1772891, by rfl⟩ : syracuseStep 2363855 = 3545783) B3545783
theorem B86233571 : Blo 1574485 86233571 := bstep (se 1 (by rfl) ⟨64675178, by rfl⟩ : syracuseStep 86233571 = 129350357) B129350357
theorem B2363897 : Blo 1574485 2363897 := bstep (se 2 (by rfl) ⟨886461, by rfl⟩ : syracuseStep 2363897 = 1772923) B1772923
theorem B2363999 : Blo 1574485 2363999 := bstep (se 1 (by rfl) ⟨1772999, by rfl⟩ : syracuseStep 2363999 = 3545999) B3545999
theorem B2658919 : Blo 1574485 2658919 := bstep (se 1 (by rfl) ⟨1994189, by rfl⟩ : syracuseStep 2658919 = 3988379) B3988379
theorem B3986081 : Blo 1574485 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B3543713 : Blo 1574485 3543713 := bstep (se 2 (by rfl) ⟨1328892, by rfl⟩ : syracuseStep 3543713 = 2657785) B2657785
theorem B31552229 : Blo 1574485 31552229 := bstep (se 4 (by rfl) ⟨2958021, by rfl⟩ : syracuseStep 31552229 = 5916043) B5916043
theorem B2659081 : Blo 1574485 2659081 := bstep (se 2 (by rfl) ⟨997155, by rfl⟩ : syracuseStep 2659081 = 1994311) B1994311
theorem B7574401 : Blo 1574485 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B11965319 : Blo 1574485 11965319 := bstep (se 1 (by rfl) ⟨8973989, by rfl⟩ : syracuseStep 11965319 = 17947979) B17947979
theorem B3544073 : Blo 1574485 3544073 := bstep (se 2 (by rfl) ⟨1329027, by rfl⟩ : syracuseStep 3544073 = 2658055) B2658055
theorem B3544127 : Blo 1574485 3544127 := bstep (se 1 (by rfl) ⟨2658095, by rfl⟩ : syracuseStep 3544127 = 5316191) B5316191
theorem B2364479 : Blo 1574485 2364479 := bstep (se 1 (by rfl) ⟨1773359, by rfl⟩ : syracuseStep 2364479 = 3546719) B3546719
theorem B2364521 : Blo 1574485 2364521 := bstep (se 2 (by rfl) ⟨886695, by rfl⟩ : syracuseStep 2364521 = 1773391) B1773391
theorem B63050899 : Blo 1574485 63050899 := bstep (se 1 (by rfl) ⟨47288174, by rfl⟩ : syracuseStep 63050899 = 94576349) B94576349
theorem B2364623 : Blo 1574485 2364623 := bstep (se 1 (by rfl) ⟨1773467, by rfl⟩ : syracuseStep 2364623 = 3546935) B3546935
theorem B3364051 : Blo 1574485 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B3986779 : Blo 1574485 3986779 := bstep (se 1 (by rfl) ⟨2990084, by rfl⟩ : syracuseStep 3986779 = 5980169) B5980169
theorem B2659675 : Blo 1574485 2659675 := bstep (se 1 (by rfl) ⟨1994756, by rfl⟩ : syracuseStep 2659675 = 3989513) B3989513
theorem B8967611 : Blo 1574485 8967611 := bstep (se 1 (by rfl) ⟨6725708, by rfl⟩ : syracuseStep 8967611 = 13451417) B13451417
theorem B3545063 : Blo 1574485 3545063 := bstep (se 1 (by rfl) ⟨2658797, by rfl⟩ : syracuseStep 3545063 = 5317595) B5317595
theorem B3545081 : Blo 1574485 3545081 := bstep (se 2 (by rfl) ⟨1329405, by rfl⟩ : syracuseStep 3545081 = 2658811) B2658811
theorem B5978195 : Blo 1574485 5978195 := bstep (se 1 (by rfl) ⟨4483646, by rfl⟩ : syracuseStep 5978195 = 8967293) B8967293
theorem B3987539 : Blo 1574485 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B3545171 : Blo 1574485 3545171 := bstep (se 1 (by rfl) ⟨2658878, by rfl⟩ : syracuseStep 3545171 = 5317757) B5317757
theorem B3545243 : Blo 1574485 3545243 := bstep (se 1 (by rfl) ⟨2658932, by rfl⟩ : syracuseStep 3545243 = 5317865) B5317865
theorem B3545351 : Blo 1574485 3545351 := bstep (se 1 (by rfl) ⟨2659013, by rfl⟩ : syracuseStep 3545351 = 5318027) B5318027
theorem B2243099 : Blo 1574485 2243099 := bstep (se 1 (by rfl) ⟨1682324, by rfl⟩ : syracuseStep 2243099 = 3364649) B3364649
theorem B5978681 : Blo 1574485 5978681 := bstep (se 2 (by rfl) ⟨2242005, by rfl⟩ : syracuseStep 5978681 = 4484011) B4484011
theorem B3988025 : Blo 1574485 3988025 := bstep (se 2 (by rfl) ⟨1495509, by rfl⟩ : syracuseStep 3988025 = 2991019) B2991019
theorem B3545657 : Blo 1574485 3545657 := bstep (se 2 (by rfl) ⟨1329621, by rfl⟩ : syracuseStep 3545657 = 2659243) B2659243
theorem B20191841 : Blo 1574485 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B8969069 : Blo 1574485 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B4488317 : Blo 1574485 4488317 := bstep (se 3 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 4488317 = 1683119) B1683119
theorem B3546377 : Blo 1574485 3546377 := bstep (se 2 (by rfl) ⟨1329891, by rfl⟩ : syracuseStep 3546377 = 2659783) B2659783
theorem B5045615 : Blo 1574485 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B13466999 : Blo 1574485 13466999 := bstep (se 1 (by rfl) ⟨10100249, by rfl⟩ : syracuseStep 13466999 = 20200499) B20200499
theorem B2989523 : Blo 1574485 2989523 := bstep (se 1 (by rfl) ⟨2242142, by rfl⟩ : syracuseStep 2989523 = 4484285) B4484285
theorem B4488659 : Blo 1574485 4488659 := bstep (se 1 (by rfl) ⟨3366494, by rfl⟩ : syracuseStep 4488659 = 6732989) B6732989
theorem B22707803 : Blo 1574485 22707803 := bstep (se 1 (by rfl) ⟨17030852, by rfl⟩ : syracuseStep 22707803 = 34061705) B34061705
theorem B5316407 : Blo 1574485 5316407 := bstep (se 1 (by rfl) ⟨3987305, by rfl⟩ : syracuseStep 5316407 = 7974611) B7974611
theorem B3989371 : Blo 1574485 3989371 := bstep (se 1 (by rfl) ⟨2992028, by rfl⟩ : syracuseStep 3989371 = 5984057) B5984057
theorem B11960459 : Blo 1574485 11960459 := bstep (se 1 (by rfl) ⟨8970344, by rfl⟩ : syracuseStep 11960459 = 17940689) B17940689
theorem B5980351 : Blo 1574485 5980351 := bstep (se 1 (by rfl) ⟨4485263, by rfl⟩ : syracuseStep 5980351 = 8970527) B8970527
theorem B7971047 : Blo 1574485 7971047 := bstep (se 1 (by rfl) ⟨5978285, by rfl⟩ : syracuseStep 7971047 = 11956571) B11956571
theorem B2523371 : Blo 1574485 2523371 := bstep (se 1 (by rfl) ⟨1892528, by rfl⟩ : syracuseStep 2523371 = 3785057) B3785057
theorem B1892587 : Blo 1574485 1892587 := bstep (se 1 (by rfl) ⟨1419440, by rfl⟩ : syracuseStep 1892587 = 2838881) B2838881
theorem B7979795 : Blo 1574485 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B13452479 : Blo 1574485 13452479 := bstep (se 1 (by rfl) ⟨10089359, by rfl⟩ : syracuseStep 13452479 = 20178719) B20178719
theorem B12780767 : Blo 1574485 12780767 := bstep (se 1 (by rfl) ⟨9585575, by rfl⟩ : syracuseStep 12780767 = 19171151) B19171151
theorem B23029069 : Blo 1574485 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B5981597 : Blo 1574485 5981597 := bstep (se 3 (by rfl) ⟨1121549, by rfl⟩ : syracuseStep 5981597 = 2243099) B2243099
theorem B5981627 : Blo 1574485 5981627 := bstep (se 1 (by rfl) ⟨4486220, by rfl⟩ : syracuseStep 5981627 = 8972441) B8972441
theorem B84067865 : Blo 1574485 84067865 := bstep (se 2 (by rfl) ⟨31525449, by rfl⟩ : syracuseStep 84067865 = 63050899) B63050899
theorem B9094765 : Blo 1574485 9094765 := bstep (se 3 (by rfl) ⟨1705268, by rfl⟩ : syracuseStep 9094765 = 3410537) B3410537
theorem B1574591 : Blo 1574485 1574591 := bstep (se 1 (by rfl) ⟨1180943, by rfl⟩ : syracuseStep 1574591 = 2361887) B2361887
theorem B13461227 : Blo 1574485 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B5048075 : Blo 1574485 5048075 := bstep (se 1 (by rfl) ⟨3786056, by rfl⟩ : syracuseStep 5048075 = 7572113) B7572113
theorem B1771303 : Blo 1574485 1771303 := bstep (se 1 (by rfl) ⟨1328477, by rfl⟩ : syracuseStep 1771303 = 2656955) B2656955
theorem B1574847 : Blo 1574485 1574847 := bstep (se 1 (by rfl) ⟨1181135, by rfl⟩ : syracuseStep 1574847 = 2362271) B2362271
theorem B1574879 : Blo 1574485 1574879 := bstep (se 1 (by rfl) ⟨1181159, by rfl⟩ : syracuseStep 1574879 = 2362319) B2362319
theorem B1574939 : Blo 1574485 1574939 := bstep (se 1 (by rfl) ⟨1181204, by rfl⟩ : syracuseStep 1574939 = 2362409) B2362409
theorem B1574943 : Blo 1574485 1574943 := bstep (se 1 (by rfl) ⟨1181207, by rfl⟩ : syracuseStep 1574943 = 2362415) B2362415
theorem B1574959 : Blo 1574485 1574959 := bstep (se 1 (by rfl) ⟨1181219, by rfl⟩ : syracuseStep 1574959 = 2362439) B2362439
theorem B2992211 : Blo 1574485 2992211 := bstep (se 1 (by rfl) ⟨2244158, by rfl⟩ : syracuseStep 2992211 = 4488317) B4488317
theorem B5392583 : Blo 1574485 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B1575135 : Blo 1574485 1575135 := bstep (se 1 (by rfl) ⟨1181351, by rfl⟩ : syracuseStep 1575135 = 2362703) B2362703
theorem B14379241 : Blo 1574485 14379241 := bstep (se 2 (by rfl) ⟨5392215, by rfl⟩ : syracuseStep 14379241 = 10784431) B10784431
theorem B1575195 : Blo 1574485 1575195 := bstep (se 1 (by rfl) ⟨1181396, by rfl⟩ : syracuseStep 1575195 = 2362793) B2362793
theorem B1993015 : Blo 1574485 1993015 := bstep (se 1 (by rfl) ⟨1494761, by rfl⟩ : syracuseStep 1993015 = 2989523) B2989523
theorem B2992439 : Blo 1574485 2992439 := bstep (se 1 (by rfl) ⟨2244329, by rfl⟩ : syracuseStep 2992439 = 4488659) B4488659
theorem B1575295 : Blo 1574485 1575295 := bstep (se 1 (by rfl) ⟨1181471, by rfl⟩ : syracuseStep 1575295 = 2362943) B2362943
theorem B5319161 : Blo 1574485 5319161 := bstep (se 2 (by rfl) ⟨1994685, by rfl⟩ : syracuseStep 5319161 = 3989371) B3989371
theorem B1575471 : Blo 1574485 1575471 := bstep (se 1 (by rfl) ⟨1181603, by rfl⟩ : syracuseStep 1575471 = 2363207) B2363207
theorem B2361959 : Blo 1574485 2361959 := bstep (se 1 (by rfl) ⟨1771469, by rfl⟩ : syracuseStep 2361959 = 3542939) B3542939
theorem B1575527 : Blo 1574485 1575527 := bstep (se 1 (by rfl) ⟨1181645, by rfl⟩ : syracuseStep 1575527 = 2363291) B2363291
theorem B36383411 : Blo 1574485 36383411 := bstep (se 1 (by rfl) ⟨27287558, by rfl⟩ : syracuseStep 36383411 = 54575117) B54575117
theorem B5319431 : Blo 1574485 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B2657063 : Blo 1574485 2657063 := bstep (se 1 (by rfl) ⟨1992797, by rfl⟩ : syracuseStep 2657063 = 3985595) B3985595
theorem B2362151 : Blo 1574485 2362151 := bstep (se 1 (by rfl) ⟨1771613, by rfl⟩ : syracuseStep 2362151 = 3543227) B3543227
theorem B7572305 : Blo 1574485 7572305 := bstep (se 2 (by rfl) ⟨2839614, by rfl⟩ : syracuseStep 7572305 = 5679229) B5679229
theorem B1575903 : Blo 1574485 1575903 := bstep (se 1 (by rfl) ⟨1181927, by rfl⟩ : syracuseStep 1575903 = 2363855) B2363855
theorem B5319647 : Blo 1574485 5319647 := bstep (se 1 (by rfl) ⟨3989735, by rfl⟩ : syracuseStep 5319647 = 7979471) B7979471
theorem B1575931 : Blo 1574485 1575931 := bstep (se 1 (by rfl) ⟨1181948, by rfl⟩ : syracuseStep 1575931 = 2363897) B2363897
theorem B1575999 : Blo 1574485 1575999 := bstep (se 1 (by rfl) ⟨1181999, by rfl⟩ : syracuseStep 1575999 = 2363999) B2363999
theorem B2657387 : Blo 1574485 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B2362475 : Blo 1574485 2362475 := bstep (se 1 (by rfl) ⟨1771856, by rfl⟩ : syracuseStep 2362475 = 3543713) B3543713
theorem B5319809 : Blo 1574485 5319809 := bstep (se 2 (by rfl) ⟨1994928, by rfl⟩ : syracuseStep 5319809 = 3989857) B3989857
theorem B2362715 : Blo 1574485 2362715 := bstep (se 1 (by rfl) ⟨1772036, by rfl⟩ : syracuseStep 2362715 = 3544073) B3544073
theorem B2657657 : Blo 1574485 2657657 := bstep (se 2 (by rfl) ⟨996621, by rfl⟩ : syracuseStep 2657657 = 1993243) B1993243
theorem B2362745 : Blo 1574485 2362745 := bstep (se 2 (by rfl) ⟨886029, by rfl⟩ : syracuseStep 2362745 = 1772059) B1772059
theorem B2362751 : Blo 1574485 2362751 := bstep (se 1 (by rfl) ⟨1772063, by rfl⟩ : syracuseStep 2362751 = 3544127) B3544127
theorem B1576319 : Blo 1574485 1576319 := bstep (se 1 (by rfl) ⟨1182239, by rfl⟩ : syracuseStep 1576319 = 2364479) B2364479
theorem B1576347 : Blo 1574485 1576347 := bstep (se 1 (by rfl) ⟨1182260, by rfl⟩ : syracuseStep 1576347 = 2364521) B2364521
theorem B1576415 : Blo 1574485 1576415 := bstep (se 1 (by rfl) ⟨1182311, by rfl⟩ : syracuseStep 1576415 = 2364623) B2364623
theorem B6385243 : Blo 1574485 6385243 := bstep (se 1 (by rfl) ⟨4788932, by rfl⟩ : syracuseStep 6385243 = 9577865) B9577865
theorem B5320511 : Blo 1574485 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B10235819 : Blo 1574485 10235819 := bstep (se 1 (by rfl) ⟨7676864, by rfl⟩ : syracuseStep 10235819 = 15353729) B15353729
theorem B5320619 : Blo 1574485 5320619 := bstep (se 1 (by rfl) ⟨3990464, by rfl⟩ : syracuseStep 5320619 = 7980929) B7980929
theorem B2363375 : Blo 1574485 2363375 := bstep (se 1 (by rfl) ⟨1772531, by rfl⟩ : syracuseStep 2363375 = 3545063) B3545063
theorem B2363387 : Blo 1574485 2363387 := bstep (se 1 (by rfl) ⟨1772540, by rfl⟩ : syracuseStep 2363387 = 3545081) B3545081
theorem B3985463 : Blo 1574485 3985463 := bstep (se 1 (by rfl) ⟨2989097, by rfl⟩ : syracuseStep 3985463 = 5978195) B5978195
theorem B2658359 : Blo 1574485 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B2363447 : Blo 1574485 2363447 := bstep (se 1 (by rfl) ⟨1772585, by rfl⟩ : syracuseStep 2363447 = 3545171) B3545171
theorem B2363495 : Blo 1574485 2363495 := bstep (se 1 (by rfl) ⟨1772621, by rfl⟩ : syracuseStep 2363495 = 3545243) B3545243
theorem B2363567 : Blo 1574485 2363567 := bstep (se 1 (by rfl) ⟨1772675, by rfl⟩ : syracuseStep 2363567 = 3545351) B3545351
theorem B4485401 : Blo 1574485 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B3985787 : Blo 1574485 3985787 := bstep (se 1 (by rfl) ⟨2989340, by rfl⟩ : syracuseStep 3985787 = 5978681) B5978681
theorem B2658683 : Blo 1574485 2658683 := bstep (se 1 (by rfl) ⟨1994012, by rfl⟩ : syracuseStep 2658683 = 3988025) B3988025
theorem B2363771 : Blo 1574485 2363771 := bstep (se 1 (by rfl) ⟨1772828, by rfl⟩ : syracuseStep 2363771 = 3545657) B3545657
theorem B4788809 : Blo 1574485 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B2658953 : Blo 1574485 2658953 := bstep (se 2 (by rfl) ⟨997107, by rfl⟩ : syracuseStep 2658953 = 1994215) B1994215
theorem B2364041 : Blo 1574485 2364041 := bstep (se 2 (by rfl) ⟨886515, by rfl⟩ : syracuseStep 2364041 = 1773031) B1773031
theorem B8975083 : Blo 1574485 8975083 := bstep (se 1 (by rfl) ⟨6731312, by rfl⟩ : syracuseStep 8975083 = 13462625) B13462625
theorem B2364251 : Blo 1574485 2364251 := bstep (se 1 (by rfl) ⟨1773188, by rfl⟩ : syracuseStep 2364251 = 3546377) B3546377
theorem B3363743 : Blo 1574485 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B3544271 : Blo 1574485 3544271 := bstep (se 1 (by rfl) ⟨2658203, by rfl⟩ : syracuseStep 3544271 = 5316407) B5316407
theorem B3544361 : Blo 1574485 3544361 := bstep (se 2 (by rfl) ⟨1329135, by rfl⟩ : syracuseStep 3544361 = 2658271) B2658271
theorem B2364713 : Blo 1574485 2364713 := bstep (se 2 (by rfl) ⟨886767, by rfl⟩ : syracuseStep 2364713 = 1773535) B1773535
theorem B7566655 : Blo 1574485 7566655 := bstep (se 1 (by rfl) ⟨5674991, by rfl⟩ : syracuseStep 7566655 = 11349983) B11349983
theorem B10777943 : Blo 1574485 10777943 := bstep (se 1 (by rfl) ⟨8083457, by rfl⟩ : syracuseStep 10777943 = 16166915) B16166915
theorem B5461355 : Blo 1574485 5461355 := bstep (se 1 (by rfl) ⟨4096016, by rfl⟩ : syracuseStep 5461355 = 8192033) B8192033
theorem B3544559 : Blo 1574485 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B57489047 : Blo 1574485 57489047 := bstep (se 1 (by rfl) ⟨43116785, by rfl⟩ : syracuseStep 57489047 = 86233571) B86233571
theorem B19158839 : Blo 1574485 19158839 := bstep (se 1 (by rfl) ⟨14369129, by rfl⟩ : syracuseStep 19158839 = 28738259) B28738259
theorem B21034819 : Blo 1574485 21034819 := bstep (se 1 (by rfl) ⟨15776114, by rfl⟩ : syracuseStep 21034819 = 31552229) B31552229
theorem B3544955 : Blo 1574485 3544955 := bstep (se 1 (by rfl) ⟨2658716, by rfl⟩ : syracuseStep 3544955 = 5317433) B5317433
theorem B7575419 : Blo 1574485 7575419 := bstep (se 1 (by rfl) ⟨5681564, by rfl⟩ : syracuseStep 7575419 = 11363129) B11363129
theorem B15144839 : Blo 1574485 15144839 := bstep (se 1 (by rfl) ⟨11358629, by rfl⟩ : syracuseStep 15144839 = 22717259) B22717259
theorem B5314463 : Blo 1574485 5314463 := bstep (se 1 (by rfl) ⟨3985847, by rfl⟩ : syracuseStep 5314463 = 7971695) B7971695
theorem B3544991 : Blo 1574485 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B7976879 : Blo 1574485 7976879 := bstep (se 1 (by rfl) ⟨5982659, by rfl⟩ : syracuseStep 7976879 = 11965319) B11965319
theorem B22722565 : Blo 1574485 22722565 := bstep (se 4 (by rfl) ⟨2130240, by rfl⟩ : syracuseStep 22722565 = 4260481) B4260481
theorem B3545225 : Blo 1574485 3545225 := bstep (se 2 (by rfl) ⟨1329459, by rfl⟩ : syracuseStep 3545225 = 2658919) B2658919
theorem B17029385 : Blo 1574485 17029385 := bstep (se 2 (by rfl) ⟨6386019, by rfl⟩ : syracuseStep 17029385 = 12772039) B12772039
theorem B3594527 : Blo 1574485 3594527 := bstep (se 1 (by rfl) ⟨2695895, by rfl⟩ : syracuseStep 3594527 = 5391791) B5391791
theorem B5978407 : Blo 1574485 5978407 := bstep (se 1 (by rfl) ⟨4483805, by rfl⟩ : syracuseStep 5978407 = 8967611) B8967611
theorem B3545441 : Blo 1574485 3545441 := bstep (se 2 (by rfl) ⟨1329540, by rfl⟩ : syracuseStep 3545441 = 2659081) B2659081
theorem B3545531 : Blo 1574485 3545531 := bstep (se 1 (by rfl) ⟨2659148, by rfl⟩ : syracuseStep 3545531 = 5318297) B5318297
theorem B10099201 : Blo 1574485 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B3545927 : Blo 1574485 3545927 := bstep (se 1 (by rfl) ⟨2659445, by rfl⟩ : syracuseStep 3545927 = 5318891) B5318891
theorem B5315705 : Blo 1574485 5315705 := bstep (se 2 (by rfl) ⟨1993389, by rfl⟩ : syracuseStep 5315705 = 3986779) B3986779
theorem B3546233 : Blo 1574485 3546233 := bstep (se 2 (by rfl) ⟨1329837, by rfl⟩ : syracuseStep 3546233 = 2659675) B2659675
theorem B5979379 : Blo 1574485 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B8977999 : Blo 1574485 8977999 := bstep (se 1 (by rfl) ⟨6733499, by rfl⟩ : syracuseStep 8977999 = 13466999) B13466999
theorem B3989159 : Blo 1574485 3989159 := bstep (se 1 (by rfl) ⟨2991869, by rfl⟩ : syracuseStep 3989159 = 5983739) B5983739
theorem B3546791 : Blo 1574485 3546791 := bstep (se 1 (by rfl) ⟨2660093, by rfl⟩ : syracuseStep 3546791 = 5320187) B5320187
theorem B15138535 : Blo 1574485 15138535 := bstep (se 1 (by rfl) ⟨11353901, by rfl⟩ : syracuseStep 15138535 = 22707803) B22707803
theorem B16170769 : Blo 1574485 16170769 := bstep (se 2 (by rfl) ⟨6064038, by rfl⟩ : syracuseStep 16170769 = 12128077) B12128077
theorem B3546899 : Blo 1574485 3546899 := bstep (se 1 (by rfl) ⟨2660174, by rfl⟩ : syracuseStep 3546899 = 5320349) B5320349
theorem B14376791 : Blo 1574485 14376791 := bstep (se 1 (by rfl) ⟨10782593, by rfl⟩ : syracuseStep 14376791 = 21565187) B21565187
theorem B2990047 : Blo 1574485 2990047 := bstep (se 1 (by rfl) ⟨2242535, by rfl⟩ : syracuseStep 2990047 = 4485071) B4485071
theorem B2990267 : Blo 1574485 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B2523449 : Blo 1574485 2523449 := bstep (se 2 (by rfl) ⟨946293, by rfl⟩ : syracuseStep 2523449 = 1892587) B1892587
theorem B7971209 : Blo 1574485 7971209 := bstep (se 2 (by rfl) ⟨2989203, by rfl⟩ : syracuseStep 7971209 = 5978407) B5978407
theorem B8520511 : Blo 1574485 8520511 := bstep (se 1 (by rfl) ⟨6390383, by rfl⟩ : syracuseStep 8520511 = 12780767) B12780767
theorem B7185295 : Blo 1574485 7185295 := bstep (se 1 (by rfl) ⟨5388971, by rfl⟩ : syracuseStep 7185295 = 10777943) B10777943
theorem B12772559 : Blo 1574485 12772559 := bstep (se 1 (by rfl) ⟨9579419, by rfl⟩ : syracuseStep 12772559 = 19158839) B19158839
theorem B5317919 : Blo 1574485 5317919 := bstep (se 1 (by rfl) ⟨3988439, by rfl⟩ : syracuseStep 5317919 = 7976879) B7976879
theorem B7972505 : Blo 1574485 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B1574639 : Blo 1574485 1574639 := bstep (se 1 (by rfl) ⟨1180979, by rfl⟩ : syracuseStep 1574639 = 2361959) B2361959
theorem B30705425 : Blo 1574485 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B1771375 : Blo 1574485 1771375 := bstep (se 1 (by rfl) ⟨1328531, by rfl⟩ : syracuseStep 1771375 = 2657063) B2657063
theorem B1574767 : Blo 1574485 1574767 := bstep (se 1 (by rfl) ⟨1181075, by rfl⟩ : syracuseStep 1574767 = 2362151) B2362151
theorem B1771591 : Blo 1574485 1771591 := bstep (se 1 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 1771591 = 2657387) B2657387
theorem B1574983 : Blo 1574485 1574983 := bstep (se 1 (by rfl) ⟨1181237, by rfl⟩ : syracuseStep 1574983 = 2362475) B2362475
theorem B11970665 : Blo 1574485 11970665 := bstep (se 2 (by rfl) ⟨4488999, by rfl⟩ : syracuseStep 11970665 = 8977999) B8977999
theorem B8513657 : Blo 1574485 8513657 := bstep (se 2 (by rfl) ⟨3192621, by rfl⟩ : syracuseStep 8513657 = 6385243) B6385243
theorem B12126353 : Blo 1574485 12126353 := bstep (se 2 (by rfl) ⟨4547382, by rfl⟩ : syracuseStep 12126353 = 9094765) B9094765
theorem B1575143 : Blo 1574485 1575143 := bstep (se 1 (by rfl) ⟨1181357, by rfl⟩ : syracuseStep 1575143 = 2362715) B2362715
theorem B1771771 : Blo 1574485 1771771 := bstep (se 1 (by rfl) ⟨1328828, by rfl⟩ : syracuseStep 1771771 = 2657657) B2657657
theorem B1575163 : Blo 1574485 1575163 := bstep (se 1 (by rfl) ⟨1181372, by rfl⟩ : syracuseStep 1575163 = 2362745) B2362745
theorem B1575167 : Blo 1574485 1575167 := bstep (se 1 (by rfl) ⟨1181375, by rfl⟩ : syracuseStep 1575167 = 2362751) B2362751
theorem B2361737 : Blo 1574485 2361737 := bstep (se 2 (by rfl) ⟨885651, by rfl⟩ : syracuseStep 2361737 = 1771303) B1771303
theorem B1575583 : Blo 1574485 1575583 := bstep (se 1 (by rfl) ⟨1181687, by rfl⟩ : syracuseStep 1575583 = 2363375) B2363375
theorem B1575591 : Blo 1574485 1575591 := bstep (se 1 (by rfl) ⟨1181693, by rfl⟩ : syracuseStep 1575591 = 2363387) B2363387
theorem B30296753 : Blo 1574485 30296753 := bstep (se 2 (by rfl) ⟨11361282, by rfl⟩ : syracuseStep 30296753 = 22722565) B22722565
theorem B2656975 : Blo 1574485 2656975 := bstep (se 1 (by rfl) ⟨1992731, by rfl⟩ : syracuseStep 2656975 = 3985463) B3985463
theorem B1772239 : Blo 1574485 1772239 := bstep (se 1 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 1772239 = 2658359) B2658359
theorem B1575631 : Blo 1574485 1575631 := bstep (se 1 (by rfl) ⟨1181723, by rfl⟩ : syracuseStep 1575631 = 2363447) B2363447
theorem B1575663 : Blo 1574485 1575663 := bstep (se 1 (by rfl) ⟨1181747, by rfl⟩ : syracuseStep 1575663 = 2363495) B2363495
theorem B7973639 : Blo 1574485 7973639 := bstep (se 1 (by rfl) ⟨5980229, by rfl⟩ : syracuseStep 7973639 = 11960459) B11960459
theorem B1575711 : Blo 1574485 1575711 := bstep (se 1 (by rfl) ⟨1181783, by rfl⟩ : syracuseStep 1575711 = 2363567) B2363567
theorem B2657191 : Blo 1574485 2657191 := bstep (se 1 (by rfl) ⟨1992893, by rfl⟩ : syracuseStep 2657191 = 3985787) B3985787
theorem B7973801 : Blo 1574485 7973801 := bstep (se 2 (by rfl) ⟨2990175, by rfl⟩ : syracuseStep 7973801 = 5980351) B5980351
theorem B1772455 : Blo 1574485 1772455 := bstep (se 1 (by rfl) ⟨1329341, by rfl⟩ : syracuseStep 1772455 = 2658683) B2658683
theorem B1575847 : Blo 1574485 1575847 := bstep (se 1 (by rfl) ⟨1181885, by rfl⟩ : syracuseStep 1575847 = 2363771) B2363771
theorem B19172321 : Blo 1574485 19172321 := bstep (se 2 (by rfl) ⟨7189620, by rfl⟩ : syracuseStep 19172321 = 14379241) B14379241
theorem B2657353 : Blo 1574485 2657353 := bstep (se 2 (by rfl) ⟨996507, by rfl⟩ : syracuseStep 2657353 = 1993015) B1993015
theorem B1772635 : Blo 1574485 1772635 := bstep (se 1 (by rfl) ⟨1329476, by rfl⟩ : syracuseStep 1772635 = 2658953) B2658953
theorem B1576027 : Blo 1574485 1576027 := bstep (se 1 (by rfl) ⟨1182020, by rfl⟩ : syracuseStep 1576027 = 2364041) B2364041
theorem B5319863 : Blo 1574485 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B1576167 : Blo 1574485 1576167 := bstep (se 1 (by rfl) ⟨1182125, by rfl⟩ : syracuseStep 1576167 = 2364251) B2364251
theorem B6728989 : Blo 1574485 6728989 := bstep (se 3 (by rfl) ⟨1261685, by rfl⟩ : syracuseStep 6728989 = 2523371) B2523371
theorem B2362847 : Blo 1574485 2362847 := bstep (se 1 (by rfl) ⟨1772135, by rfl⟩ : syracuseStep 2362847 = 3544271) B3544271
theorem B2362907 : Blo 1574485 2362907 := bstep (se 1 (by rfl) ⟨1772180, by rfl⟩ : syracuseStep 2362907 = 3544361) B3544361
theorem B1576475 : Blo 1574485 1576475 := bstep (se 1 (by rfl) ⟨1182356, by rfl⟩ : syracuseStep 1576475 = 2364713) B2364713
theorem B2363039 : Blo 1574485 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B56045243 : Blo 1574485 56045243 := bstep (se 1 (by rfl) ⟨42033932, by rfl⟩ : syracuseStep 56045243 = 84067865) B84067865
theorem B38326031 : Blo 1574485 38326031 := bstep (se 1 (by rfl) ⟨28744523, by rfl⟩ : syracuseStep 38326031 = 57489047) B57489047
theorem B8974151 : Blo 1574485 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B2363303 : Blo 1574485 2363303 := bstep (se 1 (by rfl) ⟨1772477, by rfl⟩ : syracuseStep 2363303 = 3544955) B3544955
theorem B5050279 : Blo 1574485 5050279 := bstep (se 1 (by rfl) ⟨3787709, by rfl⟩ : syracuseStep 5050279 = 7575419) B7575419
theorem B10096559 : Blo 1574485 10096559 := bstep (se 1 (by rfl) ⟨7572419, by rfl⟩ : syracuseStep 10096559 = 15144839) B15144839
theorem B3542975 : Blo 1574485 3542975 := bstep (se 1 (by rfl) ⟨2657231, by rfl⟩ : syracuseStep 3542975 = 5314463) B5314463
theorem B2363327 : Blo 1574485 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B1994807 : Blo 1574485 1994807 := bstep (se 1 (by rfl) ⟨1496105, by rfl⟩ : syracuseStep 1994807 = 2992211) B2992211
theorem B2363483 : Blo 1574485 2363483 := bstep (se 1 (by rfl) ⟨1772612, by rfl⟩ : syracuseStep 2363483 = 3545225) B3545225
theorem B2396351 : Blo 1574485 2396351 := bstep (se 1 (by rfl) ⟨1797263, by rfl⟩ : syracuseStep 2396351 = 3594527) B3594527
theorem B1994959 : Blo 1574485 1994959 := bstep (se 1 (by rfl) ⟨1496219, by rfl⟩ : syracuseStep 1994959 = 2992439) B2992439
theorem B2363627 : Blo 1574485 2363627 := bstep (se 1 (by rfl) ⟨1772720, by rfl⟩ : syracuseStep 2363627 = 3545441) B3545441
theorem B2363687 : Blo 1574485 2363687 := bstep (se 1 (by rfl) ⟨1772765, by rfl⟩ : syracuseStep 2363687 = 3545531) B3545531
theorem B10088873 : Blo 1574485 10088873 := bstep (se 2 (by rfl) ⟨3783327, by rfl⟩ : syracuseStep 10088873 = 7566655) B7566655
theorem B2363951 : Blo 1574485 2363951 := bstep (se 1 (by rfl) ⟨1772963, by rfl⟩ : syracuseStep 2363951 = 3545927) B3545927
theorem B3543803 : Blo 1574485 3543803 := bstep (se 1 (by rfl) ⟨2657852, by rfl⟩ : syracuseStep 3543803 = 5315705) B5315705
theorem B2364155 : Blo 1574485 2364155 := bstep (se 1 (by rfl) ⟨1773116, by rfl⟩ : syracuseStep 2364155 = 3546233) B3546233
theorem B28046425 : Blo 1574485 28046425 := bstep (se 2 (by rfl) ⟨10517409, by rfl⟩ : syracuseStep 28046425 = 21034819) B21034819
theorem B2659439 : Blo 1574485 2659439 := bstep (se 1 (by rfl) ⟨1994579, by rfl⟩ : syracuseStep 2659439 = 3989159) B3989159
theorem B2364527 : Blo 1574485 2364527 := bstep (se 1 (by rfl) ⟨1773395, by rfl⟩ : syracuseStep 2364527 = 3546791) B3546791
theorem B2364599 : Blo 1574485 2364599 := bstep (se 1 (by rfl) ⟨1773449, by rfl⟩ : syracuseStep 2364599 = 3546899) B3546899
theorem B3986729 : Blo 1574485 3986729 := bstep (se 2 (by rfl) ⟨1495023, by rfl⟩ : syracuseStep 3986729 = 2990047) B2990047
theorem B5314031 : Blo 1574485 5314031 := bstep (se 1 (by rfl) ⟨3985523, by rfl⟩ : syracuseStep 5314031 = 7971047) B7971047
theorem B3192539 : Blo 1574485 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B2242495 : Blo 1574485 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B13465601 : Blo 1574485 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B8968319 : Blo 1574485 8968319 := bstep (se 1 (by rfl) ⟨6726239, by rfl⟩ : syracuseStep 8968319 = 13452479) B13452479
theorem B3987731 : Blo 1574485 3987731 := bstep (se 1 (by rfl) ⟨2990798, by rfl⟩ : syracuseStep 3987731 = 5981597) B5981597
theorem B14563613 : Blo 1574485 14563613 := bstep (se 3 (by rfl) ⟨2730677, by rfl⟩ : syracuseStep 14563613 = 5461355) B5461355
theorem B3987751 : Blo 1574485 3987751 := bstep (se 1 (by rfl) ⟨2990813, by rfl⟩ : syracuseStep 3987751 = 5981627) B5981627
theorem B11966777 : Blo 1574485 11966777 := bstep (se 2 (by rfl) ⟨4487541, by rfl⟩ : syracuseStep 11966777 = 8975083) B8975083
theorem B3365383 : Blo 1574485 3365383 := bstep (se 1 (by rfl) ⟨2524037, by rfl⟩ : syracuseStep 3365383 = 5048075) B5048075
theorem B3595055 : Blo 1574485 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B11352923 : Blo 1574485 11352923 := bstep (se 1 (by rfl) ⟨8514692, by rfl⟩ : syracuseStep 11352923 = 17029385) B17029385
theorem B3546107 : Blo 1574485 3546107 := bstep (se 1 (by rfl) ⟨2659580, by rfl⟩ : syracuseStep 3546107 = 5319161) B5319161
theorem B24255607 : Blo 1574485 24255607 := bstep (se 1 (by rfl) ⟨18191705, by rfl⟩ : syracuseStep 24255607 = 36383411) B36383411
theorem B3546287 : Blo 1574485 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B3546431 : Blo 1574485 3546431 := bstep (se 1 (by rfl) ⟨2659823, by rfl⟩ : syracuseStep 3546431 = 5319647) B5319647
theorem B3546539 : Blo 1574485 3546539 := bstep (se 1 (by rfl) ⟨2659904, by rfl⟩ : syracuseStep 3546539 = 5319809) B5319809
theorem B20192813 : Blo 1574485 20192813 := bstep (se 3 (by rfl) ⟨3786152, by rfl⟩ : syracuseStep 20192813 = 7572305) B7572305
theorem B38338109 : Blo 1574485 38338109 := bstep (se 3 (by rfl) ⟨7188395, by rfl⟩ : syracuseStep 38338109 = 14376791) B14376791
theorem B20184713 : Blo 1574485 20184713 := bstep (se 2 (by rfl) ⟨7569267, by rfl⟩ : syracuseStep 20184713 = 15138535) B15138535
theorem B21561025 : Blo 1574485 21561025 := bstep (se 2 (by rfl) ⟨8085384, by rfl⟩ : syracuseStep 21561025 = 16170769) B16170769
theorem B27295517 : Blo 1574485 27295517 := bstep (se 3 (by rfl) ⟨5117909, by rfl⟩ : syracuseStep 27295517 = 10235819) B10235819
theorem B3547007 : Blo 1574485 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B3547079 : Blo 1574485 3547079 := bstep (se 1 (by rfl) ⟨2660309, by rfl⟩ : syracuseStep 3547079 = 5320619) B5320619
theorem B1597567 : Blo 1574485 1597567 := bstep (se 1 (by rfl) ⟨1198175, by rfl⟩ : syracuseStep 1597567 = 2396351) B2396351
theorem B6725915 : Blo 1574485 6725915 := bstep (se 1 (by rfl) ⟨5044436, by rfl⟩ : syracuseStep 6725915 = 10088873) B10088873
theorem B5317001 : Blo 1574485 5317001 := bstep (se 2 (by rfl) ⟨1993875, by rfl⟩ : syracuseStep 5317001 = 3987751) B3987751
theorem B38347253 : Blo 1574485 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B7980443 : Blo 1574485 7980443 := bstep (se 1 (by rfl) ⟨5985332, by rfl⟩ : syracuseStep 7980443 = 11970665) B11970665
theorem B9709075 : Blo 1574485 9709075 := bstep (se 1 (by rfl) ⟨7281806, by rfl⟩ : syracuseStep 9709075 = 14563613) B14563613
theorem B1574491 : Blo 1574485 1574491 := bstep (se 1 (by rfl) ⟨1180868, by rfl⟩ : syracuseStep 1574491 = 2361737) B2361737
theorem B8971985 : Blo 1574485 8971985 := bstep (se 2 (by rfl) ⟨3364494, by rfl⟩ : syracuseStep 8971985 = 6728989) B6728989
theorem B8513437 : Blo 1574485 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B12781547 : Blo 1574485 12781547 := bstep (se 1 (by rfl) ⟨9586160, by rfl⟩ : syracuseStep 12781547 = 19172321) B19172321
theorem B28748033 : Blo 1574485 28748033 := bstep (se 2 (by rfl) ⟨10780512, by rfl⟩ : syracuseStep 28748033 = 21561025) B21561025
theorem B1575231 : Blo 1574485 1575231 := bstep (se 1 (by rfl) ⟨1181423, by rfl⟩ : syracuseStep 1575231 = 2362847) B2362847
theorem B1575271 : Blo 1574485 1575271 := bstep (se 1 (by rfl) ⟨1181453, by rfl⟩ : syracuseStep 1575271 = 2362907) B2362907
theorem B13461875 : Blo 1574485 13461875 := bstep (se 1 (by rfl) ⟨10096406, by rfl⟩ : syracuseStep 13461875 = 20192813) B20192813
theorem B1575359 : Blo 1574485 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B2361833 : Blo 1574485 2361833 := bstep (se 2 (by rfl) ⟨885687, by rfl⟩ : syracuseStep 2361833 = 1771375) B1771375
theorem B18197011 : Blo 1574485 18197011 := bstep (se 1 (by rfl) ⟨13647758, by rfl⟩ : syracuseStep 18197011 = 27295517) B27295517
theorem B5982767 : Blo 1574485 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B1575535 : Blo 1574485 1575535 := bstep (se 1 (by rfl) ⟨1181651, by rfl⟩ : syracuseStep 1575535 = 2363303) B2363303
theorem B2361983 : Blo 1574485 2361983 := bstep (se 1 (by rfl) ⟨1771487, by rfl⟩ : syracuseStep 2361983 = 3542975) B3542975
theorem B1575551 : Blo 1574485 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B1575655 : Blo 1574485 1575655 := bstep (se 1 (by rfl) ⟨1181741, by rfl⟩ : syracuseStep 1575655 = 2363483) B2363483
theorem B2362121 : Blo 1574485 2362121 := bstep (se 2 (by rfl) ⟨885795, by rfl⟩ : syracuseStep 2362121 = 1771591) B1771591
theorem B1993511 : Blo 1574485 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B5319485 : Blo 1574485 5319485 := bstep (se 3 (by rfl) ⟨997403, by rfl⟩ : syracuseStep 5319485 = 1994807) B1994807
theorem B1575751 : Blo 1574485 1575751 := bstep (se 1 (by rfl) ⟨1181813, by rfl⟩ : syracuseStep 1575751 = 2363627) B2363627
theorem B1575791 : Blo 1574485 1575791 := bstep (se 1 (by rfl) ⟨1181843, by rfl⟩ : syracuseStep 1575791 = 2363687) B2363687
theorem B1682299 : Blo 1574485 1682299 := bstep (se 1 (by rfl) ⟨1261724, by rfl⟩ : syracuseStep 1682299 = 2523449) B2523449
theorem B2362361 : Blo 1574485 2362361 := bstep (se 2 (by rfl) ⟨885885, by rfl⟩ : syracuseStep 2362361 = 1771771) B1771771
theorem B1575967 : Blo 1574485 1575967 := bstep (se 1 (by rfl) ⟨1181975, by rfl⟩ : syracuseStep 1575967 = 2363951) B2363951
theorem B32336941 : Blo 1574485 32336941 := bstep (se 3 (by rfl) ⟨6063176, by rfl⟩ : syracuseStep 32336941 = 12126353) B12126353
theorem B2362535 : Blo 1574485 2362535 := bstep (se 1 (by rfl) ⟨1771901, by rfl⟩ : syracuseStep 2362535 = 3543803) B3543803
theorem B1576103 : Blo 1574485 1576103 := bstep (se 1 (by rfl) ⟨1182077, by rfl⟩ : syracuseStep 1576103 = 2364155) B2364155
theorem B1772959 : Blo 1574485 1772959 := bstep (se 1 (by rfl) ⟨1329719, by rfl⟩ : syracuseStep 1772959 = 2659439) B2659439
theorem B1576351 : Blo 1574485 1576351 := bstep (se 1 (by rfl) ⟨1182263, by rfl⟩ : syracuseStep 1576351 = 2364527) B2364527
theorem B1576399 : Blo 1574485 1576399 := bstep (se 1 (by rfl) ⟨1182299, by rfl⟩ : syracuseStep 1576399 = 2364599) B2364599
theorem B8515039 : Blo 1574485 8515039 := bstep (se 1 (by rfl) ⟨6386279, by rfl⟩ : syracuseStep 8515039 = 12772559) B12772559
theorem B2657819 : Blo 1574485 2657819 := bstep (se 1 (by rfl) ⟨1993364, by rfl⟩ : syracuseStep 2657819 = 3986729) B3986729
theorem B3542633 : Blo 1574485 3542633 := bstep (se 2 (by rfl) ⟨1328487, by rfl⟩ : syracuseStep 3542633 = 2656975) B2656975
theorem B2362985 : Blo 1574485 2362985 := bstep (se 2 (by rfl) ⟨886119, by rfl⟩ : syracuseStep 2362985 = 1772239) B1772239
theorem B3542687 : Blo 1574485 3542687 := bstep (se 1 (by rfl) ⟨2657015, by rfl⟩ : syracuseStep 3542687 = 5314031) B5314031
theorem B9580393 : Blo 1574485 9580393 := bstep (se 2 (by rfl) ⟨3592647, by rfl⟩ : syracuseStep 9580393 = 7185295) B7185295
theorem B3542921 : Blo 1574485 3542921 := bstep (se 2 (by rfl) ⟨1328595, by rfl⟩ : syracuseStep 3542921 = 2657191) B2657191
theorem B2363273 : Blo 1574485 2363273 := bstep (se 2 (by rfl) ⟨886227, by rfl⟩ : syracuseStep 2363273 = 1772455) B1772455
theorem B3543137 : Blo 1574485 3543137 := bstep (se 2 (by rfl) ⟨1328676, by rfl⟩ : syracuseStep 3543137 = 2657353) B2657353
theorem B2363513 : Blo 1574485 2363513 := bstep (se 2 (by rfl) ⟨886317, by rfl⟩ : syracuseStep 2363513 = 1772635) B1772635
theorem B2658487 : Blo 1574485 2658487 := bstep (se 1 (by rfl) ⟨1993865, by rfl⟩ : syracuseStep 2658487 = 3987731) B3987731
theorem B20197835 : Blo 1574485 20197835 := bstep (se 1 (by rfl) ⟨15148376, by rfl⟩ : syracuseStep 20197835 = 30296753) B30296753
theorem B2364071 : Blo 1574485 2364071 := bstep (se 1 (by rfl) ⟨1773053, by rfl⟩ : syracuseStep 2364071 = 3546107) B3546107
theorem B2364191 : Blo 1574485 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B2364287 : Blo 1574485 2364287 := bstep (se 1 (by rfl) ⟨1773215, by rfl⟩ : syracuseStep 2364287 = 3546431) B3546431
theorem B2364359 : Blo 1574485 2364359 := bstep (se 1 (by rfl) ⟨1773269, by rfl⟩ : syracuseStep 2364359 = 3546539) B3546539
theorem B13456475 : Blo 1574485 13456475 := bstep (se 1 (by rfl) ⟨10092356, by rfl⟩ : syracuseStep 13456475 = 20184713) B20184713
theorem B2364671 : Blo 1574485 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B6731039 : Blo 1574485 6731039 := bstep (se 1 (by rfl) ⟨5048279, by rfl⟩ : syracuseStep 6731039 = 10096559) B10096559
theorem B2364719 : Blo 1574485 2364719 := bstep (se 1 (by rfl) ⟨1773539, by rfl⟩ : syracuseStep 2364719 = 3547079) B3547079
theorem B5314139 : Blo 1574485 5314139 := bstep (se 1 (by rfl) ⟨3985604, by rfl⟩ : syracuseStep 5314139 = 7971209) B7971209
theorem B2659945 : Blo 1574485 2659945 := bstep (se 2 (by rfl) ⟨997479, by rfl⟩ : syracuseStep 2659945 = 1994959) B1994959
theorem B4487177 : Blo 1574485 4487177 := bstep (se 2 (by rfl) ⟨1682691, by rfl⟩ : syracuseStep 4487177 = 3365383) B3365383
theorem B3545279 : Blo 1574485 3545279 := bstep (se 1 (by rfl) ⟨2658959, by rfl⟩ : syracuseStep 3545279 = 5317919) B5317919
theorem B11360681 : Blo 1574485 11360681 := bstep (se 2 (by rfl) ⟨4260255, by rfl⟩ : syracuseStep 11360681 = 8520511) B8520511
theorem B5315003 : Blo 1574485 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B20470283 : Blo 1574485 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B8977067 : Blo 1574485 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B5675771 : Blo 1574485 5675771 := bstep (se 1 (by rfl) ⟨4256828, by rfl⟩ : syracuseStep 5675771 = 8513657) B8513657
theorem B5978879 : Blo 1574485 5978879 := bstep (se 1 (by rfl) ⟨4484159, by rfl⟩ : syracuseStep 5978879 = 8968319) B8968319
theorem B37395233 : Blo 1574485 37395233 := bstep (se 2 (by rfl) ⟨14023212, by rfl⟩ : syracuseStep 37395233 = 28046425) B28046425
theorem B32340809 : Blo 1574485 32340809 := bstep (se 2 (by rfl) ⟨12127803, by rfl⟩ : syracuseStep 32340809 = 24255607) B24255607
theorem B7977851 : Blo 1574485 7977851 := bstep (se 1 (by rfl) ⟨5983388, by rfl⟩ : syracuseStep 7977851 = 11966777) B11966777
theorem B149453981 : Blo 1574485 149453981 := bstep (se 3 (by rfl) ⟨28022621, by rfl⟩ : syracuseStep 149453981 = 56045243) B56045243
theorem B5315759 : Blo 1574485 5315759 := bstep (se 1 (by rfl) ⟨3986819, by rfl⟩ : syracuseStep 5315759 = 7973639) B7973639
theorem B7568615 : Blo 1574485 7568615 := bstep (se 1 (by rfl) ⟨5676461, by rfl⟩ : syracuseStep 7568615 = 11352923) B11352923
theorem B5315867 : Blo 1574485 5315867 := bstep (se 1 (by rfl) ⟨3986900, by rfl⟩ : syracuseStep 5315867 = 7973801) B7973801
theorem B3546575 : Blo 1574485 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B11959973 : Blo 1574485 11959973 := bstep (se 4 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 11959973 = 2242495) B2242495
theorem B25558739 : Blo 1574485 25558739 := bstep (se 1 (by rfl) ⟨19169054, by rfl⟩ : syracuseStep 25558739 = 38338109) B38338109
theorem B25550687 : Blo 1574485 25550687 := bstep (se 1 (by rfl) ⟨19163015, by rfl⟩ : syracuseStep 25550687 = 38326031) B38326031
theorem B6733705 : Blo 1574485 6733705 := bstep (se 2 (by rfl) ⟨2525139, by rfl⟩ : syracuseStep 6733705 = 5050279) B5050279
theorem B51781733 : Blo 1574485 51781733 := bstep (se 4 (by rfl) ⟨4854537, by rfl⟩ : syracuseStep 51781733 = 9709075) B9709075
theorem B2130089 : Blo 1574485 2130089 := bstep (se 2 (by rfl) ⟨798783, by rfl⟩ : syracuseStep 2130089 = 1597567) B1597567
theorem B8970983 : Blo 1574485 8970983 := bstep (se 1 (by rfl) ⟨6728237, by rfl⟩ : syracuseStep 8970983 = 13456475) B13456475
theorem B17949437 : Blo 1574485 17949437 := bstep (se 3 (by rfl) ⟨3365519, by rfl⟩ : syracuseStep 17949437 = 6731039) B6731039
theorem B5981323 : Blo 1574485 5981323 := bstep (se 1 (by rfl) ⟨4485992, by rfl⟩ : syracuseStep 5981323 = 8971985) B8971985
theorem B8521031 : Blo 1574485 8521031 := bstep (se 1 (by rfl) ⟨6390773, by rfl⟩ : syracuseStep 8521031 = 12781547) B12781547
theorem B43115921 : Blo 1574485 43115921 := bstep (se 2 (by rfl) ⟨16168470, by rfl⟩ : syracuseStep 43115921 = 32336941) B32336941
theorem B1574555 : Blo 1574485 1574555 := bstep (se 1 (by rfl) ⟨1180916, by rfl⟩ : syracuseStep 1574555 = 2361833) B2361833
theorem B1574655 : Blo 1574485 1574655 := bstep (se 1 (by rfl) ⟨1180991, by rfl⟩ : syracuseStep 1574655 = 2361983) B2361983
theorem B1574747 : Blo 1574485 1574747 := bstep (se 1 (by rfl) ⟨1181060, by rfl⟩ : syracuseStep 1574747 = 2362121) B2362121
theorem B24930155 : Blo 1574485 24930155 := bstep (se 1 (by rfl) ⟨18697616, by rfl⟩ : syracuseStep 24930155 = 37395233) B37395233
theorem B5318567 : Blo 1574485 5318567 := bstep (se 1 (by rfl) ⟨3988925, by rfl⟩ : syracuseStep 5318567 = 7977851) B7977851
theorem B1574907 : Blo 1574485 1574907 := bstep (se 1 (by rfl) ⟨1181180, by rfl⟩ : syracuseStep 1574907 = 2362361) B2362361
theorem B1575023 : Blo 1574485 1575023 := bstep (se 1 (by rfl) ⟨1181267, by rfl⟩ : syracuseStep 1575023 = 2362535) B2362535
theorem B68135165 : Blo 1574485 68135165 := bstep (se 3 (by rfl) ⟨12775343, by rfl⟩ : syracuseStep 68135165 = 25550687) B25550687
theorem B1771879 : Blo 1574485 1771879 := bstep (se 1 (by rfl) ⟨1328909, by rfl⟩ : syracuseStep 1771879 = 2657819) B2657819
theorem B2361755 : Blo 1574485 2361755 := bstep (se 1 (by rfl) ⟨1771316, by rfl⟩ : syracuseStep 2361755 = 3542633) B3542633
theorem B1575323 : Blo 1574485 1575323 := bstep (se 1 (by rfl) ⟨1181492, by rfl⟩ : syracuseStep 1575323 = 2362985) B2362985
theorem B2361791 : Blo 1574485 2361791 := bstep (se 1 (by rfl) ⟨1771343, by rfl⟩ : syracuseStep 2361791 = 3542687) B3542687
theorem B7973315 : Blo 1574485 7973315 := bstep (se 1 (by rfl) ⟨5979986, by rfl⟩ : syracuseStep 7973315 = 11959973) B11959973
theorem B12773857 : Blo 1574485 12773857 := bstep (se 2 (by rfl) ⟨4790196, by rfl⟩ : syracuseStep 12773857 = 9580393) B9580393
theorem B2361947 : Blo 1574485 2361947 := bstep (se 1 (by rfl) ⟨1771460, by rfl⟩ : syracuseStep 2361947 = 3542921) B3542921
theorem B1575515 : Blo 1574485 1575515 := bstep (se 1 (by rfl) ⟨1181636, by rfl⟩ : syracuseStep 1575515 = 2363273) B2363273
theorem B2362091 : Blo 1574485 2362091 := bstep (se 1 (by rfl) ⟨1771568, by rfl⟩ : syracuseStep 2362091 = 3543137) B3543137
theorem B1575675 : Blo 1574485 1575675 := bstep (se 1 (by rfl) ⟨1181756, by rfl⟩ : syracuseStep 1575675 = 2363513) B2363513
theorem B4483943 : Blo 1574485 4483943 := bstep (se 1 (by rfl) ⟨3362957, by rfl⟩ : syracuseStep 4483943 = 6725915) B6725915
theorem B1576047 : Blo 1574485 1576047 := bstep (se 1 (by rfl) ⟨1182035, by rfl⟩ : syracuseStep 1576047 = 2364071) B2364071
theorem B1576127 : Blo 1574485 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B1576191 : Blo 1574485 1576191 := bstep (se 1 (by rfl) ⟨1182143, by rfl⟩ : syracuseStep 1576191 = 2364287) B2364287
theorem B1576239 : Blo 1574485 1576239 := bstep (se 1 (by rfl) ⟨1182179, by rfl⟩ : syracuseStep 1576239 = 2364359) B2364359
theorem B1576447 : Blo 1574485 1576447 := bstep (se 1 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 1576447 = 2364671) B2364671
theorem B1576479 : Blo 1574485 1576479 := bstep (se 1 (by rfl) ⟨1182359, by rfl⟩ : syracuseStep 1576479 = 2364719) B2364719
theorem B5320295 : Blo 1574485 5320295 := bstep (se 1 (by rfl) ⟨3990221, by rfl⟩ : syracuseStep 5320295 = 7980443) B7980443
theorem B3542759 : Blo 1574485 3542759 := bstep (se 1 (by rfl) ⟨2657069, by rfl⟩ : syracuseStep 3542759 = 5314139) B5314139
theorem B2363519 : Blo 1574485 2363519 := bstep (se 1 (by rfl) ⟨1772639, by rfl⟩ : syracuseStep 2363519 = 3545279) B3545279
theorem B19165355 : Blo 1574485 19165355 := bstep (se 1 (by rfl) ⟨14374016, by rfl⟩ : syracuseStep 19165355 = 28748033) B28748033
theorem B8974583 : Blo 1574485 8974583 := bstep (se 1 (by rfl) ⟨6730937, by rfl⟩ : syracuseStep 8974583 = 13461875) B13461875
theorem B7573787 : Blo 1574485 7573787 := bstep (se 1 (by rfl) ⟨5680340, by rfl⟩ : syracuseStep 7573787 = 11360681) B11360681
theorem B3543335 : Blo 1574485 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B5984711 : Blo 1574485 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B3985919 : Blo 1574485 3985919 := bstep (se 1 (by rfl) ⟨2989439, by rfl⟩ : syracuseStep 3985919 = 5978879) B5978879
theorem B2363945 : Blo 1574485 2363945 := bstep (se 2 (by rfl) ⟨886479, by rfl⟩ : syracuseStep 2363945 = 1772959) B1772959
theorem B99635987 : Blo 1574485 99635987 := bstep (se 1 (by rfl) ⟨74726990, by rfl⟩ : syracuseStep 99635987 = 149453981) B149453981
theorem B3543839 : Blo 1574485 3543839 := bstep (se 1 (by rfl) ⟨2657879, by rfl⟩ : syracuseStep 3543839 = 5315759) B5315759
theorem B3543911 : Blo 1574485 3543911 := bstep (se 1 (by rfl) ⟨2657933, by rfl⟩ : syracuseStep 3543911 = 5315867) B5315867
theorem B2364383 : Blo 1574485 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B11351249 : Blo 1574485 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B11965805 : Blo 1574485 11965805 := bstep (se 3 (by rfl) ⟨2243588, by rfl⟩ : syracuseStep 11965805 = 4487177) B4487177
theorem B3544649 : Blo 1574485 3544649 := bstep (se 2 (by rfl) ⟨1329243, by rfl⟩ : syracuseStep 3544649 = 2658487) B2658487
theorem B3544667 : Blo 1574485 3544667 := bstep (se 1 (by rfl) ⟨2658500, by rfl⟩ : syracuseStep 3544667 = 5317001) B5317001
theorem B13465223 : Blo 1574485 13465223 := bstep (se 1 (by rfl) ⟨10098917, by rfl⟩ : syracuseStep 13465223 = 20197835) B20197835
theorem B25564835 : Blo 1574485 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B24262681 : Blo 1574485 24262681 := bstep (se 2 (by rfl) ⟨9098505, by rfl⟩ : syracuseStep 24262681 = 18197011) B18197011
theorem B2243065 : Blo 1574485 2243065 := bstep (se 2 (by rfl) ⟨841149, by rfl⟩ : syracuseStep 2243065 = 1682299) B1682299
theorem B13646855 : Blo 1574485 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B3988511 : Blo 1574485 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B3783847 : Blo 1574485 3783847 := bstep (se 1 (by rfl) ⟨2837885, by rfl⟩ : syracuseStep 3783847 = 5675771) B5675771
theorem B3546323 : Blo 1574485 3546323 := bstep (se 1 (by rfl) ⟨2659742, by rfl⟩ : syracuseStep 3546323 = 5319485) B5319485
theorem B21560539 : Blo 1574485 21560539 := bstep (se 1 (by rfl) ⟨16170404, by rfl⟩ : syracuseStep 21560539 = 32340809) B32340809
theorem B11353385 : Blo 1574485 11353385 := bstep (se 2 (by rfl) ⟨4257519, by rfl⟩ : syracuseStep 11353385 = 8515039) B8515039
theorem B5316029 : Blo 1574485 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B3546593 : Blo 1574485 3546593 := bstep (se 2 (by rfl) ⟨1329972, by rfl⟩ : syracuseStep 3546593 = 2659945) B2659945
theorem B5045743 : Blo 1574485 5045743 := bstep (se 1 (by rfl) ⟨3784307, by rfl⟩ : syracuseStep 5045743 = 7568615) B7568615
theorem B17039159 : Blo 1574485 17039159 := bstep (se 1 (by rfl) ⟨12779369, by rfl⟩ : syracuseStep 17039159 = 25558739) B25558739
theorem B8978273 : Blo 1574485 8978273 := bstep (se 2 (by rfl) ⟨3366852, by rfl⟩ : syracuseStep 8978273 = 6733705) B6733705
theorem B32350241 : Blo 1574485 32350241 := bstep (se 2 (by rfl) ⟨12131340, by rfl⟩ : syracuseStep 32350241 = 24262681) B24262681
theorem B34521155 : Blo 1574485 34521155 := bstep (se 1 (by rfl) ⟨25890866, by rfl⟩ : syracuseStep 34521155 = 51781733) B51781733
theorem B3989807 : Blo 1574485 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B5980655 : Blo 1574485 5980655 := bstep (se 1 (by rfl) ⟨4485491, by rfl⟩ : syracuseStep 5980655 = 8970983) B8970983
theorem B17031809 : Blo 1574485 17031809 := bstep (se 2 (by rfl) ⟨6386928, by rfl⟩ : syracuseStep 17031809 = 12773857) B12773857
theorem B2990753 : Blo 1574485 2990753 := bstep (se 2 (by rfl) ⟨1121532, by rfl⟩ : syracuseStep 2990753 = 2243065) B2243065
theorem B1574503 : Blo 1574485 1574503 := bstep (se 1 (by rfl) ⟨1180877, by rfl⟩ : syracuseStep 1574503 = 2361755) B2361755
theorem B28747385 : Blo 1574485 28747385 := bstep (se 2 (by rfl) ⟨10780269, by rfl⟩ : syracuseStep 28747385 = 21560539) B21560539
theorem B1574527 : Blo 1574485 1574527 := bstep (se 1 (by rfl) ⟨1180895, by rfl⟩ : syracuseStep 1574527 = 2361791) B2361791
theorem B1574631 : Blo 1574485 1574631 := bstep (se 1 (by rfl) ⟨1180973, by rfl⟩ : syracuseStep 1574631 = 2361947) B2361947
theorem B1574727 : Blo 1574485 1574727 := bstep (se 1 (by rfl) ⟨1181045, by rfl⟩ : syracuseStep 1574727 = 2362091) B2362091
theorem B6727657 : Blo 1574485 6727657 := bstep (se 2 (by rfl) ⟨2522871, by rfl⟩ : syracuseStep 6727657 = 5045743) B5045743
theorem B2361839 : Blo 1574485 2361839 := bstep (se 1 (by rfl) ⟨1771379, by rfl⟩ : syracuseStep 2361839 = 3542759) B3542759
theorem B1575679 : Blo 1574485 1575679 := bstep (se 1 (by rfl) ⟨1181759, by rfl⟩ : syracuseStep 1575679 = 2363519) B2363519
theorem B5983055 : Blo 1574485 5983055 := bstep (se 1 (by rfl) ⟨4487291, by rfl⟩ : syracuseStep 5983055 = 8974583) B8974583
theorem B5049191 : Blo 1574485 5049191 := bstep (se 1 (by rfl) ⟨3786893, by rfl⟩ : syracuseStep 5049191 = 7573787) B7573787
theorem B2362223 : Blo 1574485 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B2657279 : Blo 1574485 2657279 := bstep (se 1 (by rfl) ⟨1992959, by rfl⟩ : syracuseStep 2657279 = 3985919) B3985919
theorem B1575963 : Blo 1574485 1575963 := bstep (se 1 (by rfl) ⟨1181972, by rfl⟩ : syracuseStep 1575963 = 2363945) B2363945
theorem B2362505 : Blo 1574485 2362505 := bstep (se 2 (by rfl) ⟨885939, by rfl⟩ : syracuseStep 2362505 = 1771879) B1771879
theorem B2362559 : Blo 1574485 2362559 := bstep (se 1 (by rfl) ⟨1771919, by rfl⟩ : syracuseStep 2362559 = 3543839) B3543839
theorem B2362607 : Blo 1574485 2362607 := bstep (se 1 (by rfl) ⟨1771955, by rfl⟩ : syracuseStep 2362607 = 3543911) B3543911
theorem B1576255 : Blo 1574485 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B5680687 : Blo 1574485 5680687 := bstep (se 1 (by rfl) ⟨4260515, by rfl⟩ : syracuseStep 5680687 = 8521031) B8521031
theorem B2363099 : Blo 1574485 2363099 := bstep (se 1 (by rfl) ⟨1772324, by rfl⟩ : syracuseStep 2363099 = 3544649) B3544649
theorem B2363111 : Blo 1574485 2363111 := bstep (se 1 (by rfl) ⟨1772333, by rfl⟩ : syracuseStep 2363111 = 3544667) B3544667
theorem B17043223 : Blo 1574485 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B7975097 : Blo 1574485 7975097 := bstep (se 2 (by rfl) ⟨2990661, by rfl⟩ : syracuseStep 7975097 = 5981323) B5981323
theorem B22720949 : Blo 1574485 22720949 := bstep (se 5 (by rfl) ⟨1065044, by rfl⟩ : syracuseStep 22720949 = 2130089) B2130089
theorem B9097903 : Blo 1574485 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B2659007 : Blo 1574485 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B265695965 : Blo 1574485 265695965 := bstep (se 3 (by rfl) ⟨49817993, by rfl⟩ : syracuseStep 265695965 = 99635987) B99635987
theorem B2364215 : Blo 1574485 2364215 := bstep (se 1 (by rfl) ⟨1773161, by rfl⟩ : syracuseStep 2364215 = 3546323) B3546323
theorem B3544019 : Blo 1574485 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B2364395 : Blo 1574485 2364395 := bstep (se 1 (by rfl) ⟨1773296, by rfl⟩ : syracuseStep 2364395 = 3546593) B3546593
theorem B11359439 : Blo 1574485 11359439 := bstep (se 1 (by rfl) ⟨8519579, by rfl⟩ : syracuseStep 11359439 = 17039159) B17039159
theorem B5985515 : Blo 1574485 5985515 := bstep (se 1 (by rfl) ⟨4489136, by rfl⟩ : syracuseStep 5985515 = 8978273) B8978273
theorem B12776903 : Blo 1574485 12776903 := bstep (se 1 (by rfl) ⟨9582677, by rfl⟩ : syracuseStep 12776903 = 19165355) B19165355
theorem B11966291 : Blo 1574485 11966291 := bstep (se 1 (by rfl) ⟨8974718, by rfl⟩ : syracuseStep 11966291 = 17949437) B17949437
theorem B7567499 : Blo 1574485 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B7977203 : Blo 1574485 7977203 := bstep (se 1 (by rfl) ⟨5982902, by rfl⟩ : syracuseStep 7977203 = 11965805) B11965805
theorem B28743947 : Blo 1574485 28743947 := bstep (se 1 (by rfl) ⟨21557960, by rfl⟩ : syracuseStep 28743947 = 43115921) B43115921
theorem B8976815 : Blo 1574485 8976815 := bstep (se 1 (by rfl) ⟨6732611, by rfl⟩ : syracuseStep 8976815 = 13465223) B13465223
theorem B16620103 : Blo 1574485 16620103 := bstep (se 1 (by rfl) ⟨12465077, by rfl⟩ : syracuseStep 16620103 = 24930155) B24930155
theorem B3545711 : Blo 1574485 3545711 := bstep (se 1 (by rfl) ⟨2659283, by rfl⟩ : syracuseStep 3545711 = 5318567) B5318567
theorem B45423443 : Blo 1574485 45423443 := bstep (se 1 (by rfl) ⟨34067582, by rfl⟩ : syracuseStep 45423443 = 68135165) B68135165
theorem B5045129 : Blo 1574485 5045129 := bstep (se 2 (by rfl) ⟨1891923, by rfl⟩ : syracuseStep 5045129 = 3783847) B3783847
theorem B5315543 : Blo 1574485 5315543 := bstep (se 1 (by rfl) ⟨3986657, by rfl⟩ : syracuseStep 5315543 = 7973315) B7973315
theorem B2989295 : Blo 1574485 2989295 := bstep (se 1 (by rfl) ⟨2241971, by rfl⟩ : syracuseStep 2989295 = 4483943) B4483943
theorem B7568923 : Blo 1574485 7568923 := bstep (se 1 (by rfl) ⟨5676692, by rfl⟩ : syracuseStep 7568923 = 11353385) B11353385
theorem B3546863 : Blo 1574485 3546863 := bstep (se 1 (by rfl) ⟨2660147, by rfl⟩ : syracuseStep 3546863 = 5320295) B5320295
theorem B5316731 : Blo 1574485 5316731 := bstep (se 1 (by rfl) ⟨3987548, by rfl⟩ : syracuseStep 5316731 = 7975097) B7975097
theorem B15147299 : Blo 1574485 15147299 := bstep (se 1 (by rfl) ⟨11360474, by rfl⟩ : syracuseStep 15147299 = 22720949) B22720949
theorem B11354539 : Blo 1574485 11354539 := bstep (se 1 (by rfl) ⟨8515904, by rfl⟩ : syracuseStep 11354539 = 17031809) B17031809
theorem B22160137 : Blo 1574485 22160137 := bstep (se 2 (by rfl) ⟨8310051, by rfl⟩ : syracuseStep 22160137 = 16620103) B16620103
theorem B3990343 : Blo 1574485 3990343 := bstep (se 1 (by rfl) ⟨2992757, by rfl⟩ : syracuseStep 3990343 = 5985515) B5985515
theorem B48522149 : Blo 1574485 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B5318135 : Blo 1574485 5318135 := bstep (se 1 (by rfl) ⟨3988601, by rfl⟩ : syracuseStep 5318135 = 7977203) B7977203
theorem B19162631 : Blo 1574485 19162631 := bstep (se 1 (by rfl) ⟨14371973, by rfl⟩ : syracuseStep 19162631 = 28743947) B28743947
theorem B1574559 : Blo 1574485 1574559 := bstep (se 1 (by rfl) ⟨1180919, by rfl⟩ : syracuseStep 1574559 = 2361839) B2361839
theorem B1574815 : Blo 1574485 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B1771519 : Blo 1574485 1771519 := bstep (se 1 (by rfl) ⟨1328639, by rfl⟩ : syracuseStep 1771519 = 2657279) B2657279
theorem B1575003 : Blo 1574485 1575003 := bstep (se 1 (by rfl) ⟨1181252, by rfl⟩ : syracuseStep 1575003 = 2362505) B2362505
theorem B1575039 : Blo 1574485 1575039 := bstep (se 1 (by rfl) ⟨1181279, by rfl⟩ : syracuseStep 1575039 = 2362559) B2362559
theorem B1992863 : Blo 1574485 1992863 := bstep (se 1 (by rfl) ⟨1494647, by rfl⟩ : syracuseStep 1992863 = 2989295) B2989295
theorem B1575071 : Blo 1574485 1575071 := bstep (se 1 (by rfl) ⟨1181303, by rfl⟩ : syracuseStep 1575071 = 2362607) B2362607
theorem B1575399 : Blo 1574485 1575399 := bstep (se 1 (by rfl) ⟨1181549, by rfl⟩ : syracuseStep 1575399 = 2363099) B2363099
theorem B1575407 : Blo 1574485 1575407 := bstep (se 1 (by rfl) ⟨1181555, by rfl⟩ : syracuseStep 1575407 = 2363111) B2363111
theorem B23014103 : Blo 1574485 23014103 := bstep (se 1 (by rfl) ⟨17260577, by rfl⟩ : syracuseStep 23014103 = 34521155) B34521155
theorem B1993835 : Blo 1574485 1993835 := bstep (se 1 (by rfl) ⟨1495376, by rfl⟩ : syracuseStep 1993835 = 2990753) B2990753
theorem B1772671 : Blo 1574485 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B177130643 : Blo 1574485 177130643 := bstep (se 1 (by rfl) ⟨132847982, by rfl⟩ : syracuseStep 177130643 = 265695965) B265695965
theorem B1576143 : Blo 1574485 1576143 := bstep (se 1 (by rfl) ⟨1182107, by rfl⟩ : syracuseStep 1576143 = 2364215) B2364215
theorem B2362679 : Blo 1574485 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B1576263 : Blo 1574485 1576263 := bstep (se 1 (by rfl) ⟨1182197, by rfl⟩ : syracuseStep 1576263 = 2364395) B2364395
theorem B7572959 : Blo 1574485 7572959 := bstep (se 1 (by rfl) ⟨5679719, by rfl⟩ : syracuseStep 7572959 = 11359439) B11359439
theorem B19164923 : Blo 1574485 19164923 := bstep (se 1 (by rfl) ⟨14373692, by rfl⟩ : syracuseStep 19164923 = 28747385) B28747385
theorem B5984543 : Blo 1574485 5984543 := bstep (se 1 (by rfl) ⟨4488407, by rfl⟩ : syracuseStep 5984543 = 8976815) B8976815
theorem B2363807 : Blo 1574485 2363807 := bstep (se 1 (by rfl) ⟨1772855, by rfl⟩ : syracuseStep 2363807 = 3545711) B3545711
theorem B30282295 : Blo 1574485 30282295 := bstep (se 1 (by rfl) ⟨22711721, by rfl⟩ : syracuseStep 30282295 = 45423443) B45423443
theorem B3363419 : Blo 1574485 3363419 := bstep (se 1 (by rfl) ⟨2522564, by rfl⟩ : syracuseStep 3363419 = 5045129) B5045129
theorem B3543695 : Blo 1574485 3543695 := bstep (se 1 (by rfl) ⟨2657771, by rfl⟩ : syracuseStep 3543695 = 5315543) B5315543
theorem B7574249 : Blo 1574485 7574249 := bstep (se 2 (by rfl) ⟨2840343, by rfl⟩ : syracuseStep 7574249 = 5680687) B5680687
theorem B2364575 : Blo 1574485 2364575 := bstep (se 1 (by rfl) ⟨1773431, by rfl⟩ : syracuseStep 2364575 = 3546863) B3546863
theorem B21566827 : Blo 1574485 21566827 := bstep (se 1 (by rfl) ⟨16175120, by rfl⟩ : syracuseStep 21566827 = 32350241) B32350241
theorem B2659871 : Blo 1574485 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B3987103 : Blo 1574485 3987103 := bstep (se 1 (by rfl) ⟨2990327, by rfl⟩ : syracuseStep 3987103 = 5980655) B5980655
theorem B8517935 : Blo 1574485 8517935 := bstep (se 1 (by rfl) ⟨6388451, by rfl⟩ : syracuseStep 8517935 = 12776903) B12776903
theorem B7977527 : Blo 1574485 7977527 := bstep (se 1 (by rfl) ⟨5983145, by rfl⟩ : syracuseStep 7977527 = 11966291) B11966291
theorem B5044999 : Blo 1574485 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B3988703 : Blo 1574485 3988703 := bstep (se 1 (by rfl) ⟨2991527, by rfl⟩ : syracuseStep 3988703 = 5983055) B5983055
theorem B3366127 : Blo 1574485 3366127 := bstep (se 1 (by rfl) ⟨2524595, by rfl⟩ : syracuseStep 3366127 = 5049191) B5049191
theorem B10091897 : Blo 1574485 10091897 := bstep (se 2 (by rfl) ⟨3784461, by rfl⟩ : syracuseStep 10091897 = 7568923) B7568923
theorem B22724297 : Blo 1574485 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B8970209 : Blo 1574485 8970209 := bstep (se 2 (by rfl) ⟨3363828, by rfl⟩ : syracuseStep 8970209 = 6727657) B6727657
theorem B3989695 : Blo 1574485 3989695 := bstep (se 1 (by rfl) ⟨2992271, by rfl⟩ : syracuseStep 3989695 = 5984543) B5984543
theorem B5316893 : Blo 1574485 5316893 := bstep (se 3 (by rfl) ⟨996917, by rfl⟩ : syracuseStep 5316893 = 1993835) B1993835
theorem B15139385 : Blo 1574485 15139385 := bstep (se 2 (by rfl) ⟨5677269, by rfl⟩ : syracuseStep 15139385 = 11354539) B11354539
theorem B6726665 : Blo 1574485 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B5678623 : Blo 1574485 5678623 := bstep (se 1 (by rfl) ⟨4258967, by rfl⟩ : syracuseStep 5678623 = 8517935) B8517935
theorem B5318351 : Blo 1574485 5318351 := bstep (se 1 (by rfl) ⟨3988763, by rfl⟩ : syracuseStep 5318351 = 7977527) B7977527
theorem B1575119 : Blo 1574485 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B6727931 : Blo 1574485 6727931 := bstep (se 1 (by rfl) ⟨5045948, by rfl⟩ : syracuseStep 6727931 = 10091897) B10091897
theorem B5048639 : Blo 1574485 5048639 := bstep (se 1 (by rfl) ⟨3786479, by rfl⟩ : syracuseStep 5048639 = 7572959) B7572959
theorem B15149531 : Blo 1574485 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B2362025 : Blo 1574485 2362025 := bstep (se 2 (by rfl) ⟨885759, by rfl⟩ : syracuseStep 2362025 = 1771519) B1771519
theorem B1575871 : Blo 1574485 1575871 := bstep (se 1 (by rfl) ⟨1181903, by rfl⟩ : syracuseStep 1575871 = 2363807) B2363807
theorem B2362463 : Blo 1574485 2362463 := bstep (se 1 (by rfl) ⟨1771847, by rfl⟩ : syracuseStep 2362463 = 3543695) B3543695
theorem B5049499 : Blo 1574485 5049499 := bstep (se 1 (by rfl) ⟨3787124, by rfl⟩ : syracuseStep 5049499 = 7574249) B7574249
theorem B1576383 : Blo 1574485 1576383 := bstep (se 1 (by rfl) ⟨1182287, by rfl⟩ : syracuseStep 1576383 = 2364575) B2364575
theorem B12775087 : Blo 1574485 12775087 := bstep (se 1 (by rfl) ⟨9581315, by rfl⟩ : syracuseStep 12775087 = 19162631) B19162631
theorem B1773247 : Blo 1574485 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B5320457 : Blo 1574485 5320457 := bstep (se 2 (by rfl) ⟨1995171, by rfl⟩ : syracuseStep 5320457 = 3990343) B3990343
theorem B2363561 : Blo 1574485 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B61370941 : Blo 1574485 61370941 := bstep (se 3 (by rfl) ⟨11507051, by rfl⟩ : syracuseStep 61370941 = 23014103) B23014103
theorem B2659135 : Blo 1574485 2659135 := bstep (se 1 (by rfl) ⟨1994351, by rfl⟩ : syracuseStep 2659135 = 3988703) B3988703
theorem B12776615 : Blo 1574485 12776615 := bstep (se 1 (by rfl) ⟨9582461, by rfl⟩ : syracuseStep 12776615 = 19164923) B19164923
theorem B3544487 : Blo 1574485 3544487 := bstep (se 1 (by rfl) ⟨2658365, by rfl⟩ : syracuseStep 3544487 = 5316731) B5316731
theorem B10098199 : Blo 1574485 10098199 := bstep (se 1 (by rfl) ⟨7573649, by rfl⟩ : syracuseStep 10098199 = 15147299) B15147299
theorem B472348381 : Blo 1574485 472348381 := bstep (se 3 (by rfl) ⟨88565321, by rfl⟩ : syracuseStep 472348381 = 177130643) B177130643
theorem B2242279 : Blo 1574485 2242279 := bstep (se 1 (by rfl) ⟨1681709, by rfl⟩ : syracuseStep 2242279 = 3363419) B3363419
theorem B5314301 : Blo 1574485 5314301 := bstep (se 3 (by rfl) ⟨996431, by rfl⟩ : syracuseStep 5314301 = 1992863) B1992863
theorem B32348099 : Blo 1574485 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B40376393 : Blo 1574485 40376393 := bstep (se 2 (by rfl) ⟨15141147, by rfl⟩ : syracuseStep 40376393 = 30282295) B30282295
theorem B3545423 : Blo 1574485 3545423 := bstep (se 1 (by rfl) ⟨2659067, by rfl⟩ : syracuseStep 3545423 = 5318135) B5318135
theorem B29546849 : Blo 1574485 29546849 := bstep (se 2 (by rfl) ⟨11080068, by rfl⟩ : syracuseStep 29546849 = 22160137) B22160137
theorem B4488169 : Blo 1574485 4488169 := bstep (se 2 (by rfl) ⟨1683063, by rfl⟩ : syracuseStep 4488169 = 3366127) B3366127
theorem B115023077 : Blo 1574485 115023077 := bstep (se 4 (by rfl) ⟨10783413, by rfl⟩ : syracuseStep 115023077 = 21566827) B21566827
theorem B5316137 : Blo 1574485 5316137 := bstep (se 2 (by rfl) ⟨1993551, by rfl⟩ : syracuseStep 5316137 = 3987103) B3987103
theorem B5980139 : Blo 1574485 5980139 := bstep (se 1 (by rfl) ⟨4485104, by rfl⟩ : syracuseStep 5980139 = 8970209) B8970209
theorem B10092923 : Blo 1574485 10092923 := bstep (se 1 (by rfl) ⟨7569692, by rfl⟩ : syracuseStep 10092923 = 15139385) B15139385
theorem B1574683 : Blo 1574485 1574683 := bstep (se 1 (by rfl) ⟨1181012, by rfl⟩ : syracuseStep 1574683 = 2362025) B2362025
theorem B7571497 : Blo 1574485 7571497 := bstep (se 2 (by rfl) ⟨2839311, by rfl⟩ : syracuseStep 7571497 = 5678623) B5678623
theorem B1574975 : Blo 1574485 1574975 := bstep (se 1 (by rfl) ⟨1181231, by rfl⟩ : syracuseStep 1574975 = 2362463) B2362463
theorem B17033449 : Blo 1574485 17033449 := bstep (se 2 (by rfl) ⟨6387543, by rfl⟩ : syracuseStep 17033449 = 12775087) B12775087
theorem B1575707 : Blo 1574485 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B5319593 : Blo 1574485 5319593 := bstep (se 2 (by rfl) ⟨1994847, by rfl⟩ : syracuseStep 5319593 = 3989695) B3989695
theorem B2362991 : Blo 1574485 2362991 := bstep (se 1 (by rfl) ⟨1772243, by rfl⟩ : syracuseStep 2362991 = 3544487) B3544487
theorem B3542867 : Blo 1574485 3542867 := bstep (se 1 (by rfl) ⟨2657150, by rfl⟩ : syracuseStep 3542867 = 5314301) B5314301
theorem B5984225 : Blo 1574485 5984225 := bstep (se 2 (by rfl) ⟨2244084, by rfl⟩ : syracuseStep 5984225 = 4488169) B4488169
theorem B4485287 : Blo 1574485 4485287 := bstep (se 1 (by rfl) ⟨3363965, by rfl⟩ : syracuseStep 4485287 = 6727931) B6727931
theorem B2363615 : Blo 1574485 2363615 := bstep (se 1 (by rfl) ⟨1772711, by rfl⟩ : syracuseStep 2363615 = 3545423) B3545423
theorem B19697899 : Blo 1574485 19697899 := bstep (se 1 (by rfl) ⟨14773424, by rfl⟩ : syracuseStep 19697899 = 29546849) B29546849
theorem B13464265 : Blo 1574485 13464265 := bstep (se 2 (by rfl) ⟨5049099, by rfl⟩ : syracuseStep 13464265 = 10098199) B10098199
theorem B76682051 : Blo 1574485 76682051 := bstep (se 1 (by rfl) ⟨57511538, by rfl⟩ : syracuseStep 76682051 = 115023077) B115023077
theorem B2364329 : Blo 1574485 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B629797841 : Blo 1574485 629797841 := bstep (se 2 (by rfl) ⟨236174190, by rfl⟩ : syracuseStep 629797841 = 472348381) B472348381
theorem B3544091 : Blo 1574485 3544091 := bstep (se 1 (by rfl) ⟨2658068, by rfl⟩ : syracuseStep 3544091 = 5316137) B5316137
theorem B3986759 : Blo 1574485 3986759 := bstep (se 1 (by rfl) ⟨2990069, by rfl⟩ : syracuseStep 3986759 = 5980139) B5980139
theorem B17937773 : Blo 1574485 17937773 := bstep (se 3 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 17937773 = 6726665) B6726665
theorem B3544595 : Blo 1574485 3544595 := bstep (se 1 (by rfl) ⟨2658446, by rfl⟩ : syracuseStep 3544595 = 5316893) B5316893
theorem B81827921 : Blo 1574485 81827921 := bstep (se 2 (by rfl) ⟨30685470, by rfl⟩ : syracuseStep 81827921 = 61370941) B61370941
theorem B8517743 : Blo 1574485 8517743 := bstep (se 1 (by rfl) ⟨6388307, by rfl⟩ : syracuseStep 8517743 = 12776615) B12776615
theorem B3545513 : Blo 1574485 3545513 := bstep (se 2 (by rfl) ⟨1329567, by rfl⟩ : syracuseStep 3545513 = 2659135) B2659135
theorem B3545567 : Blo 1574485 3545567 := bstep (se 1 (by rfl) ⟨2659175, by rfl⟩ : syracuseStep 3545567 = 5318351) B5318351
theorem B26917595 : Blo 1574485 26917595 := bstep (se 1 (by rfl) ⟨20188196, by rfl⟩ : syracuseStep 26917595 = 40376393) B40376393
theorem B6732665 : Blo 1574485 6732665 := bstep (se 2 (by rfl) ⟨2524749, by rfl⟩ : syracuseStep 6732665 = 5049499) B5049499
theorem B3365759 : Blo 1574485 3365759 := bstep (se 1 (by rfl) ⟨2524319, by rfl⟩ : syracuseStep 3365759 = 5048639) B5048639
theorem B10099687 : Blo 1574485 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B2989705 : Blo 1574485 2989705 := bstep (se 2 (by rfl) ⟨1121139, by rfl⟩ : syracuseStep 2989705 = 2242279) B2242279
theorem B3546971 : Blo 1574485 3546971 := bstep (se 1 (by rfl) ⟨2660228, by rfl⟩ : syracuseStep 3546971 = 5320457) B5320457
theorem B86261597 : Blo 1574485 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B2990191 : Blo 1574485 2990191 := bstep (se 1 (by rfl) ⟨2242643, by rfl⟩ : syracuseStep 2990191 = 4485287) B4485287
theorem B26263865 : Blo 1574485 26263865 := bstep (se 2 (by rfl) ⟨9848949, by rfl⟩ : syracuseStep 26263865 = 19697899) B19697899
theorem B419865227 : Blo 1574485 419865227 := bstep (se 1 (by rfl) ⟨314898920, by rfl⟩ : syracuseStep 419865227 = 629797841) B629797841
theorem B5678495 : Blo 1574485 5678495 := bstep (se 1 (by rfl) ⟨4258871, by rfl⟩ : syracuseStep 5678495 = 8517743) B8517743
theorem B1575327 : Blo 1574485 1575327 := bstep (se 1 (by rfl) ⟨1181495, by rfl⟩ : syracuseStep 1575327 = 2362991) B2362991
theorem B2361911 : Blo 1574485 2361911 := bstep (se 1 (by rfl) ⟨1771433, by rfl⟩ : syracuseStep 2361911 = 3542867) B3542867
theorem B10095329 : Blo 1574485 10095329 := bstep (se 2 (by rfl) ⟨3785748, by rfl⟩ : syracuseStep 10095329 = 7571497) B7571497
theorem B1575743 : Blo 1574485 1575743 := bstep (se 1 (by rfl) ⟨1181807, by rfl⟩ : syracuseStep 1575743 = 2363615) B2363615
theorem B6728615 : Blo 1574485 6728615 := bstep (se 1 (by rfl) ⟨5046461, by rfl⟩ : syracuseStep 6728615 = 10092923) B10092923
theorem B22711265 : Blo 1574485 22711265 := bstep (se 2 (by rfl) ⟨8516724, by rfl⟩ : syracuseStep 22711265 = 17033449) B17033449
theorem B51121367 : Blo 1574485 51121367 := bstep (se 1 (by rfl) ⟨38341025, by rfl⟩ : syracuseStep 51121367 = 76682051) B76682051
theorem B1576219 : Blo 1574485 1576219 := bstep (se 1 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 1576219 = 2364329) B2364329
theorem B2362727 : Blo 1574485 2362727 := bstep (se 1 (by rfl) ⟨1772045, by rfl⟩ : syracuseStep 2362727 = 3544091) B3544091
theorem B2657839 : Blo 1574485 2657839 := bstep (se 1 (by rfl) ⟨1993379, by rfl⟩ : syracuseStep 2657839 = 3986759) B3986759
theorem B17952353 : Blo 1574485 17952353 := bstep (se 2 (by rfl) ⟨6732132, by rfl⟩ : syracuseStep 17952353 = 13464265) B13464265
theorem B2363063 : Blo 1574485 2363063 := bstep (se 1 (by rfl) ⟨1772297, by rfl⟩ : syracuseStep 2363063 = 3544595) B3544595
theorem B2363675 : Blo 1574485 2363675 := bstep (se 1 (by rfl) ⟨1772756, by rfl⟩ : syracuseStep 2363675 = 3545513) B3545513
theorem B2363711 : Blo 1574485 2363711 := bstep (se 1 (by rfl) ⟨1772783, by rfl⟩ : syracuseStep 2363711 = 3545567) B3545567
theorem B17945063 : Blo 1574485 17945063 := bstep (se 1 (by rfl) ⟨13458797, by rfl⟩ : syracuseStep 17945063 = 26917595) B26917595
theorem B3986273 : Blo 1574485 3986273 := bstep (se 2 (by rfl) ⟨1494852, by rfl⟩ : syracuseStep 3986273 = 2989705) B2989705
theorem B8975357 : Blo 1574485 8975357 := bstep (se 3 (by rfl) ⟨1682879, by rfl⟩ : syracuseStep 8975357 = 3365759) B3365759
theorem B2364647 : Blo 1574485 2364647 := bstep (se 1 (by rfl) ⟨1773485, by rfl⟩ : syracuseStep 2364647 = 3546971) B3546971
theorem B218207789 : Blo 1574485 218207789 := bstep (se 3 (by rfl) ⟨40913960, by rfl⟩ : syracuseStep 218207789 = 81827921) B81827921
theorem B11958515 : Blo 1574485 11958515 := bstep (se 1 (by rfl) ⟨8968886, by rfl⟩ : syracuseStep 11958515 = 17937773) B17937773
theorem B13466249 : Blo 1574485 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B4488443 : Blo 1574485 4488443 := bstep (se 1 (by rfl) ⟨3366332, by rfl⟩ : syracuseStep 4488443 = 6732665) B6732665
theorem B3546395 : Blo 1574485 3546395 := bstep (se 1 (by rfl) ⟨2659796, by rfl⟩ : syracuseStep 3546395 = 5319593) B5319593
theorem B57507731 : Blo 1574485 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B3989483 : Blo 1574485 3989483 := bstep (se 1 (by rfl) ⟨2992112, by rfl⟩ : syracuseStep 3989483 = 5984225) B5984225
theorem B3785663 : Blo 1574485 3785663 := bstep (se 1 (by rfl) ⟨2839247, by rfl⟩ : syracuseStep 3785663 = 5678495) B5678495
theorem B7972343 : Blo 1574485 7972343 := bstep (se 1 (by rfl) ⟨5979257, by rfl⟩ : syracuseStep 7972343 = 11958515) B11958515
theorem B1574607 : Blo 1574485 1574607 := bstep (se 1 (by rfl) ⟨1180955, by rfl⟩ : syracuseStep 1574607 = 2361911) B2361911
theorem B15140843 : Blo 1574485 15140843 := bstep (se 1 (by rfl) ⟨11355632, by rfl⟩ : syracuseStep 15140843 = 22711265) B22711265
theorem B34080911 : Blo 1574485 34080911 := bstep (se 1 (by rfl) ⟨25560683, by rfl⟩ : syracuseStep 34080911 = 51121367) B51121367
theorem B2992295 : Blo 1574485 2992295 := bstep (se 1 (by rfl) ⟨2244221, by rfl⟩ : syracuseStep 2992295 = 4488443) B4488443
theorem B1575151 : Blo 1574485 1575151 := bstep (se 1 (by rfl) ⟨1181363, by rfl⟩ : syracuseStep 1575151 = 2362727) B2362727
theorem B1575375 : Blo 1574485 1575375 := bstep (se 1 (by rfl) ⟨1181531, by rfl⟩ : syracuseStep 1575375 = 2363063) B2363063
theorem B1575783 : Blo 1574485 1575783 := bstep (se 1 (by rfl) ⟨1181837, by rfl⟩ : syracuseStep 1575783 = 2363675) B2363675
theorem B17509243 : Blo 1574485 17509243 := bstep (se 1 (by rfl) ⟨13131932, by rfl⟩ : syracuseStep 17509243 = 26263865) B26263865
theorem B1575807 : Blo 1574485 1575807 := bstep (se 1 (by rfl) ⟨1181855, by rfl⟩ : syracuseStep 1575807 = 2363711) B2363711
theorem B11963375 : Blo 1574485 11963375 := bstep (se 1 (by rfl) ⟨8972531, by rfl⟩ : syracuseStep 11963375 = 17945063) B17945063
theorem B2657515 : Blo 1574485 2657515 := bstep (se 1 (by rfl) ⟨1993136, by rfl⟩ : syracuseStep 2657515 = 3986273) B3986273
theorem B5983571 : Blo 1574485 5983571 := bstep (se 1 (by rfl) ⟨4487678, by rfl⟩ : syracuseStep 5983571 = 8975357) B8975357
theorem B1576431 : Blo 1574485 1576431 := bstep (se 1 (by rfl) ⟨1182323, by rfl⟩ : syracuseStep 1576431 = 2364647) B2364647
theorem B6730219 : Blo 1574485 6730219 := bstep (se 1 (by rfl) ⟨5047664, by rfl⟩ : syracuseStep 6730219 = 10095329) B10095329
theorem B4485743 : Blo 1574485 4485743 := bstep (se 1 (by rfl) ⟨3364307, by rfl⟩ : syracuseStep 4485743 = 6728615) B6728615
theorem B3543785 : Blo 1574485 3543785 := bstep (se 2 (by rfl) ⟨1328919, by rfl⟩ : syracuseStep 3543785 = 2657839) B2657839
theorem B2364263 : Blo 1574485 2364263 := bstep (se 1 (by rfl) ⟨1773197, by rfl⟩ : syracuseStep 2364263 = 3546395) B3546395
theorem B2659655 : Blo 1574485 2659655 := bstep (se 1 (by rfl) ⟨1994741, by rfl⟩ : syracuseStep 2659655 = 3989483) B3989483
theorem B3986921 : Blo 1574485 3986921 := bstep (se 2 (by rfl) ⟨1495095, by rfl⟩ : syracuseStep 3986921 = 2990191) B2990191
theorem B279910151 : Blo 1574485 279910151 := bstep (se 1 (by rfl) ⟨209932613, by rfl⟩ : syracuseStep 279910151 = 419865227) B419865227
theorem B145471859 : Blo 1574485 145471859 := bstep (se 1 (by rfl) ⟨109103894, by rfl⟩ : syracuseStep 145471859 = 218207789) B218207789
theorem B8977499 : Blo 1574485 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B11968235 : Blo 1574485 11968235 := bstep (se 1 (by rfl) ⟨8976176, by rfl⟩ : syracuseStep 11968235 = 17952353) B17952353
theorem B38338487 : Blo 1574485 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B2990495 : Blo 1574485 2990495 := bstep (se 1 (by rfl) ⟨2242871, by rfl⟩ : syracuseStep 2990495 = 4485743) B4485743
theorem B186606767 : Blo 1574485 186606767 := bstep (se 1 (by rfl) ⟨139955075, by rfl⟩ : syracuseStep 186606767 = 279910151) B279910151
theorem B10093895 : Blo 1574485 10093895 := bstep (se 1 (by rfl) ⟨7570421, by rfl⟩ : syracuseStep 10093895 = 15140843) B15140843
theorem B10095101 : Blo 1574485 10095101 := bstep (se 3 (by rfl) ⟨1892831, by rfl⟩ : syracuseStep 10095101 = 3785663) B3785663
theorem B2362523 : Blo 1574485 2362523 := bstep (se 1 (by rfl) ⟨1771892, by rfl⟩ : syracuseStep 2362523 = 3543785) B3543785
theorem B1576175 : Blo 1574485 1576175 := bstep (se 1 (by rfl) ⟨1182131, by rfl⟩ : syracuseStep 1576175 = 2364263) B2364263
theorem B8973625 : Blo 1574485 8973625 := bstep (se 2 (by rfl) ⟨3365109, by rfl⟩ : syracuseStep 8973625 = 6730219) B6730219
theorem B1773103 : Blo 1574485 1773103 := bstep (se 1 (by rfl) ⟨1329827, by rfl⟩ : syracuseStep 1773103 = 2659655) B2659655
theorem B2657947 : Blo 1574485 2657947 := bstep (se 1 (by rfl) ⟨1993460, by rfl⟩ : syracuseStep 2657947 = 3986921) B3986921
theorem B22720607 : Blo 1574485 22720607 := bstep (se 1 (by rfl) ⟨17040455, by rfl⟩ : syracuseStep 22720607 = 34080911) B34080911
theorem B1994863 : Blo 1574485 1994863 := bstep (se 1 (by rfl) ⟨1496147, by rfl⟩ : syracuseStep 1994863 = 2992295) B2992295
theorem B96981239 : Blo 1574485 96981239 := bstep (se 1 (by rfl) ⟨72735929, by rfl⟩ : syracuseStep 96981239 = 145471859) B145471859
theorem B3543353 : Blo 1574485 3543353 := bstep (se 2 (by rfl) ⟨1328757, by rfl⟩ : syracuseStep 3543353 = 2657515) B2657515
theorem B7975583 : Blo 1574485 7975583 := bstep (se 1 (by rfl) ⟨5981687, by rfl⟩ : syracuseStep 7975583 = 11963375) B11963375
theorem B5984999 : Blo 1574485 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B5314895 : Blo 1574485 5314895 := bstep (se 1 (by rfl) ⟨3986171, by rfl⟩ : syracuseStep 5314895 = 7972343) B7972343
theorem B23345657 : Blo 1574485 23345657 := bstep (se 2 (by rfl) ⟨8754621, by rfl⟩ : syracuseStep 23345657 = 17509243) B17509243
theorem B3989047 : Blo 1574485 3989047 := bstep (se 1 (by rfl) ⟨2991785, by rfl⟩ : syracuseStep 3989047 = 5983571) B5983571
theorem B7978823 : Blo 1574485 7978823 := bstep (se 1 (by rfl) ⟨5984117, by rfl⟩ : syracuseStep 7978823 = 11968235) B11968235
theorem B25558991 : Blo 1574485 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B15147071 : Blo 1574485 15147071 := bstep (se 1 (by rfl) ⟨11360303, by rfl⟩ : syracuseStep 15147071 = 22720607) B22720607
theorem B5317055 : Blo 1574485 5317055 := bstep (se 1 (by rfl) ⟨3987791, by rfl⟩ : syracuseStep 5317055 = 7975583) B7975583
theorem B3989999 : Blo 1574485 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B124404511 : Blo 1574485 124404511 := bstep (se 1 (by rfl) ⟨93303383, by rfl⟩ : syracuseStep 124404511 = 186606767) B186606767
theorem B5318729 : Blo 1574485 5318729 := bstep (se 2 (by rfl) ⟨1994523, by rfl⟩ : syracuseStep 5318729 = 3989047) B3989047
theorem B1575015 : Blo 1574485 1575015 := bstep (se 1 (by rfl) ⟨1181261, by rfl⟩ : syracuseStep 1575015 = 2362523) B2362523
theorem B5319215 : Blo 1574485 5319215 := bstep (se 1 (by rfl) ⟨3989411, by rfl⟩ : syracuseStep 5319215 = 7978823) B7978823
theorem B64654159 : Blo 1574485 64654159 := bstep (se 1 (by rfl) ⟨48490619, by rfl⟩ : syracuseStep 64654159 = 96981239) B96981239
theorem B2362235 : Blo 1574485 2362235 := bstep (se 1 (by rfl) ⟨1771676, by rfl⟩ : syracuseStep 2362235 = 3543353) B3543353
theorem B1993663 : Blo 1574485 1993663 := bstep (se 1 (by rfl) ⟨1495247, by rfl⟩ : syracuseStep 1993663 = 2990495) B2990495
theorem B6729263 : Blo 1574485 6729263 := bstep (se 1 (by rfl) ⟨5046947, by rfl⟩ : syracuseStep 6729263 = 10093895) B10093895
theorem B3543263 : Blo 1574485 3543263 := bstep (se 1 (by rfl) ⟨2657447, by rfl⟩ : syracuseStep 3543263 = 5314895) B5314895
theorem B6730067 : Blo 1574485 6730067 := bstep (se 1 (by rfl) ⟨5047550, by rfl⟩ : syracuseStep 6730067 = 10095101) B10095101
theorem B11964833 : Blo 1574485 11964833 := bstep (se 2 (by rfl) ⟨4486812, by rfl⟩ : syracuseStep 11964833 = 8973625) B8973625
theorem B2364137 : Blo 1574485 2364137 := bstep (se 2 (by rfl) ⟨886551, by rfl⟩ : syracuseStep 2364137 = 1773103) B1773103
theorem B3543929 : Blo 1574485 3543929 := bstep (se 2 (by rfl) ⟨1328973, by rfl⟩ : syracuseStep 3543929 = 2657947) B2657947
theorem B2659817 : Blo 1574485 2659817 := bstep (se 2 (by rfl) ⟨997431, by rfl⟩ : syracuseStep 2659817 = 1994863) B1994863
theorem B15563771 : Blo 1574485 15563771 := bstep (se 1 (by rfl) ⟨11672828, by rfl⟩ : syracuseStep 15563771 = 23345657) B23345657
theorem B17039327 : Blo 1574485 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B165872681 : Blo 1574485 165872681 := bstep (se 2 (by rfl) ⟨62202255, by rfl⟩ : syracuseStep 165872681 = 124404511) B124404511
theorem B86205545 : Blo 1574485 86205545 := bstep (se 2 (by rfl) ⟨32327079, by rfl⟩ : syracuseStep 86205545 = 64654159) B64654159
theorem B1574823 : Blo 1574485 1574823 := bstep (se 1 (by rfl) ⟨1181117, by rfl⟩ : syracuseStep 1574823 = 2362235) B2362235
theorem B2362175 : Blo 1574485 2362175 := bstep (se 1 (by rfl) ⟨1771631, by rfl⟩ : syracuseStep 2362175 = 3543263) B3543263
theorem B1576091 : Blo 1574485 1576091 := bstep (se 1 (by rfl) ⟨1182068, by rfl⟩ : syracuseStep 1576091 = 2364137) B2364137
theorem B2362619 : Blo 1574485 2362619 := bstep (se 1 (by rfl) ⟨1771964, by rfl⟩ : syracuseStep 2362619 = 3543929) B3543929
theorem B1773211 : Blo 1574485 1773211 := bstep (se 1 (by rfl) ⟨1329908, by rfl⟩ : syracuseStep 1773211 = 2659817) B2659817
theorem B2658217 : Blo 1574485 2658217 := bstep (se 2 (by rfl) ⟨996831, by rfl⟩ : syracuseStep 2658217 = 1993663) B1993663
theorem B10375847 : Blo 1574485 10375847 := bstep (se 1 (by rfl) ⟨7781885, by rfl⟩ : syracuseStep 10375847 = 15563771) B15563771
theorem B4486175 : Blo 1574485 4486175 := bstep (se 1 (by rfl) ⟨3364631, by rfl⟩ : syracuseStep 4486175 = 6729263) B6729263
theorem B45438205 : Blo 1574485 45438205 := bstep (se 3 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 45438205 = 17039327) B17039327
theorem B10098047 : Blo 1574485 10098047 := bstep (se 1 (by rfl) ⟨7573535, by rfl⟩ : syracuseStep 10098047 = 15147071) B15147071
theorem B4486711 : Blo 1574485 4486711 := bstep (se 1 (by rfl) ⟨3365033, by rfl⟩ : syracuseStep 4486711 = 6730067) B6730067
theorem B7976555 : Blo 1574485 7976555 := bstep (se 1 (by rfl) ⟨5982416, by rfl⟩ : syracuseStep 7976555 = 11964833) B11964833
theorem B3544703 : Blo 1574485 3544703 := bstep (se 1 (by rfl) ⟨2658527, by rfl⟩ : syracuseStep 3544703 = 5317055) B5317055
theorem B2659999 : Blo 1574485 2659999 := bstep (se 1 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 2659999 = 3989999) B3989999
theorem B3545819 : Blo 1574485 3545819 := bstep (se 1 (by rfl) ⟨2659364, by rfl⟩ : syracuseStep 3545819 = 5318729) B5318729
theorem B3546143 : Blo 1574485 3546143 := bstep (se 1 (by rfl) ⟨2659607, by rfl⟩ : syracuseStep 3546143 = 5319215) B5319215
theorem B2990783 : Blo 1574485 2990783 := bstep (se 1 (by rfl) ⟨2243087, by rfl⟩ : syracuseStep 2990783 = 4486175) B4486175
theorem B5317703 : Blo 1574485 5317703 := bstep (se 1 (by rfl) ⟨3988277, by rfl⟩ : syracuseStep 5317703 = 7976555) B7976555
theorem B1574783 : Blo 1574485 1574783 := bstep (se 1 (by rfl) ⟨1181087, by rfl⟩ : syracuseStep 1574783 = 2362175) B2362175
theorem B5982281 : Blo 1574485 5982281 := bstep (se 2 (by rfl) ⟨2243355, by rfl⟩ : syracuseStep 5982281 = 4486711) B4486711
theorem B1575079 : Blo 1574485 1575079 := bstep (se 1 (by rfl) ⟨1181309, by rfl⟩ : syracuseStep 1575079 = 2362619) B2362619
theorem B6917231 : Blo 1574485 6917231 := bstep (se 1 (by rfl) ⟨5187923, by rfl⟩ : syracuseStep 6917231 = 10375847) B10375847
theorem B57470363 : Blo 1574485 57470363 := bstep (se 1 (by rfl) ⟨43102772, by rfl⟩ : syracuseStep 57470363 = 86205545) B86205545
theorem B2363135 : Blo 1574485 2363135 := bstep (se 1 (by rfl) ⟨1772351, by rfl⟩ : syracuseStep 2363135 = 3544703) B3544703
theorem B60584273 : Blo 1574485 60584273 := bstep (se 2 (by rfl) ⟨22719102, by rfl⟩ : syracuseStep 60584273 = 45438205) B45438205
theorem B2363879 : Blo 1574485 2363879 := bstep (se 1 (by rfl) ⟨1772909, by rfl⟩ : syracuseStep 2363879 = 3545819) B3545819
theorem B2364095 : Blo 1574485 2364095 := bstep (se 1 (by rfl) ⟨1773071, by rfl⟩ : syracuseStep 2364095 = 3546143) B3546143
theorem B2364281 : Blo 1574485 2364281 := bstep (se 2 (by rfl) ⟨886605, by rfl⟩ : syracuseStep 2364281 = 1773211) B1773211
theorem B3544289 : Blo 1574485 3544289 := bstep (se 2 (by rfl) ⟨1329108, by rfl⟩ : syracuseStep 3544289 = 2658217) B2658217
theorem B110581787 : Blo 1574485 110581787 := bstep (se 1 (by rfl) ⟨82936340, by rfl⟩ : syracuseStep 110581787 = 165872681) B165872681
theorem B6732031 : Blo 1574485 6732031 := bstep (se 1 (by rfl) ⟨5049023, by rfl⟩ : syracuseStep 6732031 = 10098047) B10098047
theorem B3546665 : Blo 1574485 3546665 := bstep (se 2 (by rfl) ⟨1329999, by rfl⟩ : syracuseStep 3546665 = 2659999) B2659999
theorem B73721191 : Blo 1574485 73721191 := bstep (se 1 (by rfl) ⟨55290893, by rfl⟩ : syracuseStep 73721191 = 110581787) B110581787
theorem B1575423 : Blo 1574485 1575423 := bstep (se 1 (by rfl) ⟨1181567, by rfl⟩ : syracuseStep 1575423 = 2363135) B2363135
theorem B40389515 : Blo 1574485 40389515 := bstep (se 1 (by rfl) ⟨30292136, by rfl⟩ : syracuseStep 40389515 = 60584273) B60584273
theorem B1575919 : Blo 1574485 1575919 := bstep (se 1 (by rfl) ⟨1181939, by rfl⟩ : syracuseStep 1575919 = 2363879) B2363879
theorem B1576063 : Blo 1574485 1576063 := bstep (se 1 (by rfl) ⟨1182047, by rfl⟩ : syracuseStep 1576063 = 2364095) B2364095
theorem B1576187 : Blo 1574485 1576187 := bstep (se 1 (by rfl) ⟨1182140, by rfl⟩ : syracuseStep 1576187 = 2364281) B2364281
theorem B2362859 : Blo 1574485 2362859 := bstep (se 1 (by rfl) ⟨1772144, by rfl⟩ : syracuseStep 2362859 = 3544289) B3544289
theorem B7975421 : Blo 1574485 7975421 := bstep (se 3 (by rfl) ⟨1495391, by rfl⟩ : syracuseStep 7975421 = 2990783) B2990783
theorem B2364443 : Blo 1574485 2364443 := bstep (se 1 (by rfl) ⟨1773332, by rfl⟩ : syracuseStep 2364443 = 3546665) B3546665
theorem B8976041 : Blo 1574485 8976041 := bstep (se 2 (by rfl) ⟨3366015, by rfl⟩ : syracuseStep 8976041 = 6732031) B6732031
theorem B3545135 : Blo 1574485 3545135 := bstep (se 1 (by rfl) ⟨2658851, by rfl⟩ : syracuseStep 3545135 = 5317703) B5317703
theorem B3988187 : Blo 1574485 3988187 := bstep (se 1 (by rfl) ⟨2991140, by rfl⟩ : syracuseStep 3988187 = 5982281) B5982281
theorem B4611487 : Blo 1574485 4611487 := bstep (se 1 (by rfl) ⟨3458615, by rfl⟩ : syracuseStep 4611487 = 6917231) B6917231
theorem B38313575 : Blo 1574485 38313575 := bstep (se 1 (by rfl) ⟨28735181, by rfl⟩ : syracuseStep 38313575 = 57470363) B57470363
theorem B5316947 : Blo 1574485 5316947 := bstep (se 1 (by rfl) ⟨3987710, by rfl⟩ : syracuseStep 5316947 = 7975421) B7975421
theorem B1575239 : Blo 1574485 1575239 := bstep (se 1 (by rfl) ⟨1181429, by rfl⟩ : syracuseStep 1575239 = 2362859) B2362859
theorem B1576295 : Blo 1574485 1576295 := bstep (se 1 (by rfl) ⟨1182221, by rfl⟩ : syracuseStep 1576295 = 2364443) B2364443
theorem B5984027 : Blo 1574485 5984027 := bstep (se 1 (by rfl) ⟨4488020, by rfl⟩ : syracuseStep 5984027 = 8976041) B8976041
theorem B2363423 : Blo 1574485 2363423 := bstep (se 1 (by rfl) ⟨1772567, by rfl⟩ : syracuseStep 2363423 = 3545135) B3545135
theorem B2658791 : Blo 1574485 2658791 := bstep (se 1 (by rfl) ⟨1994093, by rfl⟩ : syracuseStep 2658791 = 3988187) B3988187
theorem B6148649 : Blo 1574485 6148649 := bstep (se 2 (by rfl) ⟨2305743, by rfl⟩ : syracuseStep 6148649 = 4611487) B4611487
theorem B98294921 : Blo 1574485 98294921 := bstep (se 2 (by rfl) ⟨36860595, by rfl⟩ : syracuseStep 98294921 = 73721191) B73721191
theorem B26926343 : Blo 1574485 26926343 := bstep (se 1 (by rfl) ⟨20194757, by rfl⟩ : syracuseStep 26926343 = 40389515) B40389515
theorem B25542383 : Blo 1574485 25542383 := bstep (se 1 (by rfl) ⟨19156787, by rfl⟩ : syracuseStep 25542383 = 38313575) B38313575
theorem B65529947 : Blo 1574485 65529947 := bstep (se 1 (by rfl) ⟨49147460, by rfl⟩ : syracuseStep 65529947 = 98294921) B98294921
theorem B17950895 : Blo 1574485 17950895 := bstep (se 1 (by rfl) ⟨13463171, by rfl⟩ : syracuseStep 17950895 = 26926343) B26926343
theorem B1575615 : Blo 1574485 1575615 := bstep (se 1 (by rfl) ⟨1181711, by rfl⟩ : syracuseStep 1575615 = 2363423) B2363423
theorem B1772527 : Blo 1574485 1772527 := bstep (se 1 (by rfl) ⟨1329395, by rfl⟩ : syracuseStep 1772527 = 2658791) B2658791
theorem B4099099 : Blo 1574485 4099099 := bstep (se 1 (by rfl) ⟨3074324, by rfl⟩ : syracuseStep 4099099 = 6148649) B6148649
theorem B68113021 : Blo 1574485 68113021 := bstep (se 3 (by rfl) ⟨12771191, by rfl⟩ : syracuseStep 68113021 = 25542383) B25542383
theorem B3544631 : Blo 1574485 3544631 := bstep (se 1 (by rfl) ⟨2658473, by rfl⟩ : syracuseStep 3544631 = 5316947) B5316947
theorem B3989351 : Blo 1574485 3989351 := bstep (se 1 (by rfl) ⟨2992013, by rfl⟩ : syracuseStep 3989351 = 5984027) B5984027
theorem B90817361 : Blo 1574485 90817361 := bstep (se 2 (by rfl) ⟨34056510, by rfl⟩ : syracuseStep 90817361 = 68113021) B68113021
theorem B5465465 : Blo 1574485 5465465 := bstep (se 2 (by rfl) ⟨2049549, by rfl⟩ : syracuseStep 5465465 = 4099099) B4099099
theorem B2363087 : Blo 1574485 2363087 := bstep (se 1 (by rfl) ⟨1772315, by rfl⟩ : syracuseStep 2363087 = 3544631) B3544631
theorem B2363369 : Blo 1574485 2363369 := bstep (se 2 (by rfl) ⟨886263, by rfl⟩ : syracuseStep 2363369 = 1772527) B1772527
theorem B2659567 : Blo 1574485 2659567 := bstep (se 1 (by rfl) ⟨1994675, by rfl⟩ : syracuseStep 2659567 = 3989351) B3989351
theorem B43686631 : Blo 1574485 43686631 := bstep (se 1 (by rfl) ⟨32764973, by rfl⟩ : syracuseStep 43686631 = 65529947) B65529947
theorem B11967263 : Blo 1574485 11967263 := bstep (se 1 (by rfl) ⟨8975447, by rfl⟩ : syracuseStep 11967263 = 17950895) B17950895
theorem B1575391 : Blo 1574485 1575391 := bstep (se 1 (by rfl) ⟨1181543, by rfl⟩ : syracuseStep 1575391 = 2363087) B2363087
theorem B1575579 : Blo 1574485 1575579 := bstep (se 1 (by rfl) ⟨1181684, by rfl⟩ : syracuseStep 1575579 = 2363369) B2363369
theorem B58248841 : Blo 1574485 58248841 := bstep (se 2 (by rfl) ⟨21843315, by rfl⟩ : syracuseStep 58248841 = 43686631) B43686631
theorem B60544907 : Blo 1574485 60544907 := bstep (se 1 (by rfl) ⟨45408680, by rfl⟩ : syracuseStep 60544907 = 90817361) B90817361
theorem B3643643 : Blo 1574485 3643643 := bstep (se 1 (by rfl) ⟨2732732, by rfl⟩ : syracuseStep 3643643 = 5465465) B5465465
theorem B3546089 : Blo 1574485 3546089 := bstep (se 2 (by rfl) ⟨1329783, by rfl⟩ : syracuseStep 3546089 = 2659567) B2659567
theorem B7978175 : Blo 1574485 7978175 := bstep (se 1 (by rfl) ⟨5983631, by rfl⟩ : syracuseStep 7978175 = 11967263) B11967263
theorem B9716381 : Blo 1574485 9716381 := bstep (se 3 (by rfl) ⟨1821821, by rfl⟩ : syracuseStep 9716381 = 3643643) B3643643
theorem B40363271 : Blo 1574485 40363271 := bstep (se 1 (by rfl) ⟨30272453, by rfl⟩ : syracuseStep 40363271 = 60544907) B60544907
theorem B5318783 : Blo 1574485 5318783 := bstep (se 1 (by rfl) ⟨3989087, by rfl⟩ : syracuseStep 5318783 = 7978175) B7978175
theorem B2364059 : Blo 1574485 2364059 := bstep (se 1 (by rfl) ⟨1773044, by rfl⟩ : syracuseStep 2364059 = 3546089) B3546089
theorem B77665121 : Blo 1574485 77665121 := bstep (se 2 (by rfl) ⟨29124420, by rfl⟩ : syracuseStep 77665121 = 58248841) B58248841
theorem B1576039 : Blo 1574485 1576039 := bstep (se 1 (by rfl) ⟨1182029, by rfl⟩ : syracuseStep 1576039 = 2364059) B2364059
theorem B51776747 : Blo 1574485 51776747 := bstep (se 1 (by rfl) ⟨38832560, by rfl⟩ : syracuseStep 51776747 = 77665121) B77665121
theorem B6477587 : Blo 1574485 6477587 := bstep (se 1 (by rfl) ⟨4858190, by rfl⟩ : syracuseStep 6477587 = 9716381) B9716381
theorem B26908847 : Blo 1574485 26908847 := bstep (se 1 (by rfl) ⟨20181635, by rfl⟩ : syracuseStep 26908847 = 40363271) B40363271
theorem B3545855 : Blo 1574485 3545855 := bstep (se 1 (by rfl) ⟨2659391, by rfl⟩ : syracuseStep 3545855 = 5318783) B5318783
theorem B4318391 : Blo 1574485 4318391 := bstep (se 1 (by rfl) ⟨3238793, by rfl⟩ : syracuseStep 4318391 = 6477587) B6477587
theorem B2363903 : Blo 1574485 2363903 := bstep (se 1 (by rfl) ⟨1772927, by rfl⟩ : syracuseStep 2363903 = 3545855) B3545855
theorem B34517831 : Blo 1574485 34517831 := bstep (se 1 (by rfl) ⟨25888373, by rfl⟩ : syracuseStep 34517831 = 51776747) B51776747
theorem B17939231 : Blo 1574485 17939231 := bstep (se 1 (by rfl) ⟨13454423, by rfl⟩ : syracuseStep 17939231 = 26908847) B26908847
theorem B368190197 : Blo 1574485 368190197 := bstep (se 5 (by rfl) ⟨17258915, by rfl⟩ : syracuseStep 368190197 = 34517831) B34517831
theorem B1575935 : Blo 1574485 1575935 := bstep (se 1 (by rfl) ⟨1181951, by rfl⟩ : syracuseStep 1575935 = 2363903) B2363903
theorem B11515709 : Blo 1574485 11515709 := bstep (se 3 (by rfl) ⟨2159195, by rfl⟩ : syracuseStep 11515709 = 4318391) B4318391
theorem B11959487 : Blo 1574485 11959487 := bstep (se 1 (by rfl) ⟨8969615, by rfl⟩ : syracuseStep 11959487 = 17939231) B17939231
theorem B7972991 : Blo 1574485 7972991 := bstep (se 1 (by rfl) ⟨5979743, by rfl⟩ : syracuseStep 7972991 = 11959487) B11959487
theorem B245460131 : Blo 1574485 245460131 := bstep (se 1 (by rfl) ⟨184095098, by rfl⟩ : syracuseStep 245460131 = 368190197) B368190197
theorem B30708557 : Blo 1574485 30708557 := bstep (se 3 (by rfl) ⟨5757854, by rfl⟩ : syracuseStep 30708557 = 11515709) B11515709
theorem B20472371 : Blo 1574485 20472371 := bstep (se 1 (by rfl) ⟨15354278, by rfl⟩ : syracuseStep 20472371 = 30708557) B30708557
theorem B163640087 : Blo 1574485 163640087 := bstep (se 1 (by rfl) ⟨122730065, by rfl⟩ : syracuseStep 163640087 = 245460131) B245460131
theorem B5315327 : Blo 1574485 5315327 := bstep (se 1 (by rfl) ⟨3986495, by rfl⟩ : syracuseStep 5315327 = 7972991) B7972991
theorem B13648247 : Blo 1574485 13648247 := bstep (se 1 (by rfl) ⟨10236185, by rfl⟩ : syracuseStep 13648247 = 20472371) B20472371
theorem B109093391 : Blo 1574485 109093391 := bstep (se 1 (by rfl) ⟨81820043, by rfl⟩ : syracuseStep 109093391 = 163640087) B163640087
theorem B3543551 : Blo 1574485 3543551 := bstep (se 1 (by rfl) ⟨2657663, by rfl⟩ : syracuseStep 3543551 = 5315327) B5315327
theorem B72728927 : Blo 1574485 72728927 := bstep (se 1 (by rfl) ⟨54546695, by rfl⟩ : syracuseStep 72728927 = 109093391) B109093391
theorem B2362367 : Blo 1574485 2362367 := bstep (se 1 (by rfl) ⟨1771775, by rfl⟩ : syracuseStep 2362367 = 3543551) B3543551
theorem B9098831 : Blo 1574485 9098831 := bstep (se 1 (by rfl) ⟨6824123, by rfl⟩ : syracuseStep 9098831 = 13648247) B13648247
theorem B1574911 : Blo 1574485 1574911 := bstep (se 1 (by rfl) ⟨1181183, by rfl⟩ : syracuseStep 1574911 = 2362367) B2362367
theorem B6065887 : Blo 1574485 6065887 := bstep (se 1 (by rfl) ⟨4549415, by rfl⟩ : syracuseStep 6065887 = 9098831) B9098831
theorem B48485951 : Blo 1574485 48485951 := bstep (se 1 (by rfl) ⟨36364463, by rfl⟩ : syracuseStep 48485951 = 72728927) B72728927
theorem B8087849 : Blo 1574485 8087849 := bstep (se 2 (by rfl) ⟨3032943, by rfl⟩ : syracuseStep 8087849 = 6065887) B6065887
theorem B32323967 : Blo 1574485 32323967 := bstep (se 1 (by rfl) ⟨24242975, by rfl⟩ : syracuseStep 32323967 = 48485951) B48485951
theorem B5391899 : Blo 1574485 5391899 := bstep (se 1 (by rfl) ⟨4043924, by rfl⟩ : syracuseStep 5391899 = 8087849) B8087849
theorem B21549311 : Blo 1574485 21549311 := bstep (se 1 (by rfl) ⟨16161983, by rfl⟩ : syracuseStep 21549311 = 32323967) B32323967
theorem B14366207 : Blo 1574485 14366207 := bstep (se 1 (by rfl) ⟨10774655, by rfl⟩ : syracuseStep 14366207 = 21549311) B21549311
theorem B3594599 : Blo 1574485 3594599 := bstep (se 1 (by rfl) ⟨2695949, by rfl⟩ : syracuseStep 3594599 = 5391899) B5391899
theorem B38309885 : Blo 1574485 38309885 := bstep (se 3 (by rfl) ⟨7183103, by rfl⟩ : syracuseStep 38309885 = 14366207) B14366207
theorem B2396399 : Blo 1574485 2396399 := bstep (se 1 (by rfl) ⟨1797299, by rfl⟩ : syracuseStep 2396399 = 3594599) B3594599
theorem B6390397 : Blo 1574485 6390397 := bstep (se 3 (by rfl) ⟨1198199, by rfl⟩ : syracuseStep 6390397 = 2396399) B2396399
theorem B25539923 : Blo 1574485 25539923 := bstep (se 1 (by rfl) ⟨19154942, by rfl⟩ : syracuseStep 25539923 = 38309885) B38309885
theorem B34082117 : Blo 1574485 34082117 := bstep (se 4 (by rfl) ⟨3195198, by rfl⟩ : syracuseStep 34082117 = 6390397) B6390397
theorem B17026615 : Blo 1574485 17026615 := bstep (se 1 (by rfl) ⟨12769961, by rfl⟩ : syracuseStep 17026615 = 25539923) B25539923
theorem B22702153 : Blo 1574485 22702153 := bstep (se 2 (by rfl) ⟨8513307, by rfl⟩ : syracuseStep 22702153 = 17026615) B17026615
theorem B22721411 : Blo 1574485 22721411 := bstep (se 1 (by rfl) ⟨17041058, by rfl⟩ : syracuseStep 22721411 = 34082117) B34082117
theorem B30269537 : Blo 1574485 30269537 := bstep (se 2 (by rfl) ⟨11351076, by rfl⟩ : syracuseStep 30269537 = 22702153) B22702153
theorem B15147607 : Blo 1574485 15147607 := bstep (se 1 (by rfl) ⟨11360705, by rfl⟩ : syracuseStep 15147607 = 22721411) B22721411
theorem B20179691 : Blo 1574485 20179691 := bstep (se 1 (by rfl) ⟨15134768, by rfl⟩ : syracuseStep 20179691 = 30269537) B30269537
theorem B20196809 : Blo 1574485 20196809 := bstep (se 2 (by rfl) ⟨7573803, by rfl⟩ : syracuseStep 20196809 = 15147607) B15147607
theorem B13453127 : Blo 1574485 13453127 := bstep (se 1 (by rfl) ⟨10089845, by rfl⟩ : syracuseStep 13453127 = 20179691) B20179691
theorem B13464539 : Blo 1574485 13464539 := bstep (se 1 (by rfl) ⟨10098404, by rfl⟩ : syracuseStep 13464539 = 20196809) B20196809
theorem B8976359 : Blo 1574485 8976359 := bstep (se 1 (by rfl) ⟨6732269, by rfl⟩ : syracuseStep 8976359 = 13464539) B13464539
theorem B8968751 : Blo 1574485 8968751 := bstep (se 1 (by rfl) ⟨6726563, by rfl⟩ : syracuseStep 8968751 = 13453127) B13453127
theorem B5984239 : Blo 1574485 5984239 := bstep (se 1 (by rfl) ⟨4488179, by rfl⟩ : syracuseStep 5984239 = 8976359) B8976359
theorem B5979167 : Blo 1574485 5979167 := bstep (se 1 (by rfl) ⟨4484375, by rfl⟩ : syracuseStep 5979167 = 8968751) B8968751
theorem B3986111 : Blo 1574485 3986111 := bstep (se 1 (by rfl) ⟨2989583, by rfl⟩ : syracuseStep 3986111 = 5979167) B5979167
theorem B7978985 : Blo 1574485 7978985 := bstep (se 2 (by rfl) ⟨2992119, by rfl⟩ : syracuseStep 7978985 = 5984239) B5984239
theorem B5319323 : Blo 1574485 5319323 := bstep (se 1 (by rfl) ⟨3989492, by rfl⟩ : syracuseStep 5319323 = 7978985) B7978985
theorem B2657407 : Blo 1574485 2657407 := bstep (se 1 (by rfl) ⟨1993055, by rfl⟩ : syracuseStep 2657407 = 3986111) B3986111
theorem B3543209 : Blo 1574485 3543209 := bstep (se 2 (by rfl) ⟨1328703, by rfl⟩ : syracuseStep 3543209 = 2657407) B2657407
theorem B3546215 : Blo 1574485 3546215 := bstep (se 1 (by rfl) ⟨2659661, by rfl⟩ : syracuseStep 3546215 = 5319323) B5319323
theorem B2362139 : Blo 1574485 2362139 := bstep (se 1 (by rfl) ⟨1771604, by rfl⟩ : syracuseStep 2362139 = 3543209) B3543209
theorem B2364143 : Blo 1574485 2364143 := bstep (se 1 (by rfl) ⟨1773107, by rfl⟩ : syracuseStep 2364143 = 3546215) B3546215
theorem B1574759 : Blo 1574485 1574759 := bstep (se 1 (by rfl) ⟨1181069, by rfl⟩ : syracuseStep 1574759 = 2362139) B2362139
theorem B1576095 : Blo 1574485 1576095 := bstep (se 1 (by rfl) ⟨1182071, by rfl⟩ : syracuseStep 1576095 = 2364143) B2364143

theorem C0 (j : ℕ) (h1 : 393621 ≤ j) (h2 : j ≤ 394120) : Blo 1574485 (4 * j + 3) := by
  interval_cases j
  · exact B1574487
  · exact B1574491
  · exact B1574495
  · exact B1574499
  · exact B1574503
  · exact B1574507
  · exact B1574511
  · exact B1574515
  · exact B1574519
  · exact B1574523
  · exact B1574527
  · exact B1574531
  · exact B1574535
  · exact B1574539
  · exact B1574543
  · exact B1574547
  · exact B1574551
  · exact B1574555
  · exact B1574559
  · exact B1574563
  · exact B1574567
  · exact B1574571
  · exact B1574575
  · exact B1574579
  · exact B1574583
  · exact B1574587
  · exact B1574591
  · exact B1574595
  · exact B1574599
  · exact B1574603
  · exact B1574607
  · exact B1574611
  · exact B1574615
  · exact B1574619
  · exact B1574623
  · exact B1574627
  · exact B1574631
  · exact B1574635
  · exact B1574639
  · exact B1574643
  · exact B1574647
  · exact B1574651
  · exact B1574655
  · exact B1574659
  · exact B1574663
  · exact B1574667
  · exact B1574671
  · exact B1574675
  · exact B1574679
  · exact B1574683
  · exact B1574687
  · exact B1574691
  · exact B1574695
  · exact B1574699
  · exact B1574703
  · exact B1574707
  · exact B1574711
  · exact B1574715
  · exact B1574719
  · exact B1574723
  · exact B1574727
  · exact B1574731
  · exact B1574735
  · exact B1574739
  · exact B1574743
  · exact B1574747
  · exact B1574751
  · exact B1574755
  · exact B1574759
  · exact B1574763
  · exact B1574767
  · exact B1574771
  · exact B1574775
  · exact B1574779
  · exact B1574783
  · exact B1574787
  · exact B1574791
  · exact B1574795
  · exact B1574799
  · exact B1574803
  · exact B1574807
  · exact B1574811
  · exact B1574815
  · exact B1574819
  · exact B1574823
  · exact B1574827
  · exact B1574831
  · exact B1574835
  · exact B1574839
  · exact B1574843
  · exact B1574847
  · exact B1574851
  · exact B1574855
  · exact B1574859
  · exact B1574863
  · exact B1574867
  · exact B1574871
  · exact B1574875
  · exact B1574879
  · exact B1574883
  · exact B1574887
  · exact B1574891
  · exact B1574895
  · exact B1574899
  · exact B1574903
  · exact B1574907
  · exact B1574911
  · exact B1574915
  · exact B1574919
  · exact B1574923
  · exact B1574927
  · exact B1574931
  · exact B1574935
  · exact B1574939
  · exact B1574943
  · exact B1574947
  · exact B1574951
  · exact B1574955
  · exact B1574959
  · exact B1574963
  · exact B1574967
  · exact B1574971
  · exact B1574975
  · exact B1574979
  · exact B1574983
  · exact B1574987
  · exact B1574991
  · exact B1574995
  · exact B1574999
  · exact B1575003
  · exact B1575007
  · exact B1575011
  · exact B1575015
  · exact B1575019
  · exact B1575023
  · exact B1575027
  · exact B1575031
  · exact B1575035
  · exact B1575039
  · exact B1575043
  · exact B1575047
  · exact B1575051
  · exact B1575055
  · exact B1575059
  · exact B1575063
  · exact B1575067
  · exact B1575071
  · exact B1575075
  · exact B1575079
  · exact B1575083
  · exact B1575087
  · exact B1575091
  · exact B1575095
  · exact B1575099
  · exact B1575103
  · exact B1575107
  · exact B1575111
  · exact B1575115
  · exact B1575119
  · exact B1575123
  · exact B1575127
  · exact B1575131
  · exact B1575135
  · exact B1575139
  · exact B1575143
  · exact B1575147
  · exact B1575151
  · exact B1575155
  · exact B1575159
  · exact B1575163
  · exact B1575167
  · exact B1575171
  · exact B1575175
  · exact B1575179
  · exact B1575183
  · exact B1575187
  · exact B1575191
  · exact B1575195
  · exact B1575199
  · exact B1575203
  · exact B1575207
  · exact B1575211
  · exact B1575215
  · exact B1575219
  · exact B1575223
  · exact B1575227
  · exact B1575231
  · exact B1575235
  · exact B1575239
  · exact B1575243
  · exact B1575247
  · exact B1575251
  · exact B1575255
  · exact B1575259
  · exact B1575263
  · exact B1575267
  · exact B1575271
  · exact B1575275
  · exact B1575279
  · exact B1575283
  · exact B1575287
  · exact B1575291
  · exact B1575295
  · exact B1575299
  · exact B1575303
  · exact B1575307
  · exact B1575311
  · exact B1575315
  · exact B1575319
  · exact B1575323
  · exact B1575327
  · exact B1575331
  · exact B1575335
  · exact B1575339
  · exact B1575343
  · exact B1575347
  · exact B1575351
  · exact B1575355
  · exact B1575359
  · exact B1575363
  · exact B1575367
  · exact B1575371
  · exact B1575375
  · exact B1575379
  · exact B1575383
  · exact B1575387
  · exact B1575391
  · exact B1575395
  · exact B1575399
  · exact B1575403
  · exact B1575407
  · exact B1575411
  · exact B1575415
  · exact B1575419
  · exact B1575423
  · exact B1575427
  · exact B1575431
  · exact B1575435
  · exact B1575439
  · exact B1575443
  · exact B1575447
  · exact B1575451
  · exact B1575455
  · exact B1575459
  · exact B1575463
  · exact B1575467
  · exact B1575471
  · exact B1575475
  · exact B1575479
  · exact B1575483
  · exact B1575487
  · exact B1575491
  · exact B1575495
  · exact B1575499
  · exact B1575503
  · exact B1575507
  · exact B1575511
  · exact B1575515
  · exact B1575519
  · exact B1575523
  · exact B1575527
  · exact B1575531
  · exact B1575535
  · exact B1575539
  · exact B1575543
  · exact B1575547
  · exact B1575551
  · exact B1575555
  · exact B1575559
  · exact B1575563
  · exact B1575567
  · exact B1575571
  · exact B1575575
  · exact B1575579
  · exact B1575583
  · exact B1575587
  · exact B1575591
  · exact B1575595
  · exact B1575599
  · exact B1575603
  · exact B1575607
  · exact B1575611
  · exact B1575615
  · exact B1575619
  · exact B1575623
  · exact B1575627
  · exact B1575631
  · exact B1575635
  · exact B1575639
  · exact B1575643
  · exact B1575647
  · exact B1575651
  · exact B1575655
  · exact B1575659
  · exact B1575663
  · exact B1575667
  · exact B1575671
  · exact B1575675
  · exact B1575679
  · exact B1575683
  · exact B1575687
  · exact B1575691
  · exact B1575695
  · exact B1575699
  · exact B1575703
  · exact B1575707
  · exact B1575711
  · exact B1575715
  · exact B1575719
  · exact B1575723
  · exact B1575727
  · exact B1575731
  · exact B1575735
  · exact B1575739
  · exact B1575743
  · exact B1575747
  · exact B1575751
  · exact B1575755
  · exact B1575759
  · exact B1575763
  · exact B1575767
  · exact B1575771
  · exact B1575775
  · exact B1575779
  · exact B1575783
  · exact B1575787
  · exact B1575791
  · exact B1575795
  · exact B1575799
  · exact B1575803
  · exact B1575807
  · exact B1575811
  · exact B1575815
  · exact B1575819
  · exact B1575823
  · exact B1575827
  · exact B1575831
  · exact B1575835
  · exact B1575839
  · exact B1575843
  · exact B1575847
  · exact B1575851
  · exact B1575855
  · exact B1575859
  · exact B1575863
  · exact B1575867
  · exact B1575871
  · exact B1575875
  · exact B1575879
  · exact B1575883
  · exact B1575887
  · exact B1575891
  · exact B1575895
  · exact B1575899
  · exact B1575903
  · exact B1575907
  · exact B1575911
  · exact B1575915
  · exact B1575919
  · exact B1575923
  · exact B1575927
  · exact B1575931
  · exact B1575935
  · exact B1575939
  · exact B1575943
  · exact B1575947
  · exact B1575951
  · exact B1575955
  · exact B1575959
  · exact B1575963
  · exact B1575967
  · exact B1575971
  · exact B1575975
  · exact B1575979
  · exact B1575983
  · exact B1575987
  · exact B1575991
  · exact B1575995
  · exact B1575999
  · exact B1576003
  · exact B1576007
  · exact B1576011
  · exact B1576015
  · exact B1576019
  · exact B1576023
  · exact B1576027
  · exact B1576031
  · exact B1576035
  · exact B1576039
  · exact B1576043
  · exact B1576047
  · exact B1576051
  · exact B1576055
  · exact B1576059
  · exact B1576063
  · exact B1576067
  · exact B1576071
  · exact B1576075
  · exact B1576079
  · exact B1576083
  · exact B1576087
  · exact B1576091
  · exact B1576095
  · exact B1576099
  · exact B1576103
  · exact B1576107
  · exact B1576111
  · exact B1576115
  · exact B1576119
  · exact B1576123
  · exact B1576127
  · exact B1576131
  · exact B1576135
  · exact B1576139
  · exact B1576143
  · exact B1576147
  · exact B1576151
  · exact B1576155
  · exact B1576159
  · exact B1576163
  · exact B1576167
  · exact B1576171
  · exact B1576175
  · exact B1576179
  · exact B1576183
  · exact B1576187
  · exact B1576191
  · exact B1576195
  · exact B1576199
  · exact B1576203
  · exact B1576207
  · exact B1576211
  · exact B1576215
  · exact B1576219
  · exact B1576223
  · exact B1576227
  · exact B1576231
  · exact B1576235
  · exact B1576239
  · exact B1576243
  · exact B1576247
  · exact B1576251
  · exact B1576255
  · exact B1576259
  · exact B1576263
  · exact B1576267
  · exact B1576271
  · exact B1576275
  · exact B1576279
  · exact B1576283
  · exact B1576287
  · exact B1576291
  · exact B1576295
  · exact B1576299
  · exact B1576303
  · exact B1576307
  · exact B1576311
  · exact B1576315
  · exact B1576319
  · exact B1576323
  · exact B1576327
  · exact B1576331
  · exact B1576335
  · exact B1576339
  · exact B1576343
  · exact B1576347
  · exact B1576351
  · exact B1576355
  · exact B1576359
  · exact B1576363
  · exact B1576367
  · exact B1576371
  · exact B1576375
  · exact B1576379
  · exact B1576383
  · exact B1576387
  · exact B1576391
  · exact B1576395
  · exact B1576399
  · exact B1576403
  · exact B1576407
  · exact B1576411
  · exact B1576415
  · exact B1576419
  · exact B1576423
  · exact B1576427
  · exact B1576431
  · exact B1576435
  · exact B1576439
  · exact B1576443
  · exact B1576447
  · exact B1576451
  · exact B1576455
  · exact B1576459
  · exact B1576463
  · exact B1576467
  · exact B1576471
  · exact B1576475
  · exact B1576479
  · exact B1576483

theorem solution (m : ℕ) (hlo : 1574485 ≤ m) (hhi : m ≤ 1576485) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 393621 ≤ j := by omega
    have hj2 : j ≤ 394120 := by omega
    have hb : Blo 1574485 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
