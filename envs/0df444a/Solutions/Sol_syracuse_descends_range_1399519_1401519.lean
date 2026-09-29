-- Prove2me | solution 1 for syracuse_descends_range_1399519_1401519
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:13:52.296998+00:00
-- url     : https://prove2.me/submissions/691c994c-b949-4cc3-9a95-d948f3f2302c

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


theorem B2990125 : Blo 1399519 2990125 := bbase (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) (by norm_num)
theorem B3547253 : Blo 1399519 3547253 := bbase (se 5 (by rfl) ⟨166277, by rfl⟩ : syracuseStep 3547253 = 332555) (by norm_num)
theorem B4726997 : Blo 1399519 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B4858085 : Blo 1399519 4858085 := bbase (se 4 (by rfl) ⟨455445, by rfl⟩ : syracuseStep 4858085 = 910891) (by norm_num)
theorem B3989749 : Blo 1399519 3989749 := bbase (se 5 (by rfl) ⟨187019, by rfl⟩ : syracuseStep 3989749 = 374039) (by norm_num)
theorem B2695493 : Blo 1399519 2695493 := bbase (se 4 (by rfl) ⟨252702, by rfl⟩ : syracuseStep 2695493 = 505405) (by norm_num)
theorem B7569749 : Blo 1399519 7569749 := bbase (se 10 (by rfl) ⟨11088, by rfl⟩ : syracuseStep 7569749 = 22177) (by norm_num)
theorem B2130349 : Blo 1399519 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B3547597 : Blo 1399519 3547597 := bbase (se 3 (by rfl) ⟨665174, by rfl⟩ : syracuseStep 3547597 = 1330349) (by norm_num)
theorem B8970709 : Blo 1399519 8970709 := bbase (se 7 (by rfl) ⟨105125, by rfl⟩ : syracuseStep 8970709 = 210251) (by norm_num)
theorem B1515989 : Blo 1399519 1515989 := bbase (se 7 (by rfl) ⟨17765, by rfl⟩ : syracuseStep 1515989 = 35531) (by norm_num)
theorem B1597909 : Blo 1399519 1597909 := bbase (se 7 (by rfl) ⟨18725, by rfl⟩ : syracuseStep 1597909 = 37451) (by norm_num)
theorem B5980661 : Blo 1399519 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B5677573 : Blo 1399519 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B3785221 : Blo 1399519 3785221 := bbase (se 4 (by rfl) ⟨354864, by rfl⟩ : syracuseStep 3785221 = 709729) (by norm_num)
theorem B7094789 : Blo 1399519 7094789 := bbase (se 4 (by rfl) ⟨665136, by rfl⟩ : syracuseStep 7094789 = 1330273) (by norm_num)
theorem B10641941 : Blo 1399519 10641941 := bbase (se 6 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 10641941 = 498841) (by norm_num)
theorem B2990621 : Blo 1399519 2990621 := bbase (se 3 (by rfl) ⟨560741, by rfl⟩ : syracuseStep 2990621 = 1121483) (by norm_num)
theorem B1892909 : Blo 1399519 1892909 := bbase (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) (by norm_num)
theorem B4727429 : Blo 1399519 4727429 := bbase (se 4 (by rfl) ⟨443196, by rfl⟩ : syracuseStep 4727429 = 886393) (by norm_num)
theorem B4489877 : Blo 1399519 4489877 := bbase (se 6 (by rfl) ⟨105231, by rfl⟩ : syracuseStep 4489877 = 210463) (by norm_num)
theorem B1516249 : Blo 1399519 1516249 := bbase (se 2 (by rfl) ⟨568593, by rfl⟩ : syracuseStep 1516249 = 1137187) (by norm_num)
theorem B6390517 : Blo 1399519 6390517 := bbase (se 5 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 6390517 = 599111) (by norm_num)
theorem B3031805 : Blo 1399519 3031805 := bbase (se 3 (by rfl) ⟨568463, by rfl⟩ : syracuseStep 3031805 = 1136927) (by norm_num)
theorem B3834629 : Blo 1399519 3834629 := bbase (se 4 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 3834629 = 718993) (by norm_num)
theorem B28025621 : Blo 1399519 28025621 := bbase (se 6 (by rfl) ⟨656850, by rfl⟩ : syracuseStep 28025621 = 1313701) (by norm_num)
theorem B3785557 : Blo 1399519 3785557 := bbase (se 9 (by rfl) ⟨11090, by rfl⟩ : syracuseStep 3785557 = 22181) (by norm_num)
theorem B12944245 : Blo 1399519 12944245 := bbase (se 5 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 12944245 = 1213523) (by norm_num)
theorem B7087013 : Blo 1399519 7087013 := bbase (se 4 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 7087013 = 1328815) (by norm_num)
theorem B10634165 : Blo 1399519 10634165 := bbase (se 5 (by rfl) ⟨498476, by rfl⟩ : syracuseStep 10634165 = 996953) (by norm_num)
theorem B3785653 : Blo 1399519 3785653 := bbase (se 5 (by rfl) ⟨177452, by rfl⟩ : syracuseStep 3785653 = 354905) (by norm_num)
theorem B7971797 : Blo 1399519 7971797 := bbase (se 7 (by rfl) ⟨93419, by rfl⟩ : syracuseStep 7971797 = 186839) (by norm_num)
theorem B4727861 : Blo 1399519 4727861 := bbase (se 5 (by rfl) ⟨221618, by rfl⟩ : syracuseStep 4727861 = 443237) (by norm_num)
theorem B5465269 : Blo 1399519 5465269 := bbase (se 5 (by rfl) ⟨256184, by rfl⟩ : syracuseStep 5465269 = 512369) (by norm_num)
theorem B2991509 : Blo 1399519 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B1516973 : Blo 1399519 1516973 := bbase (se 3 (by rfl) ⟨284432, by rfl⟩ : syracuseStep 1516973 = 568865) (by norm_num)
theorem B1705429 : Blo 1399519 1705429 := bbase (se 7 (by rfl) ⟨19985, by rfl⟩ : syracuseStep 1705429 = 39971) (by norm_num)
theorem B4728293 : Blo 1399519 4728293 := bbase (se 4 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 4728293 = 886555) (by norm_num)
theorem B4793845 : Blo 1399519 4793845 := bbase (se 5 (by rfl) ⟨224711, by rfl⟩ : syracuseStep 4793845 = 449423) (by norm_num)
theorem B2991629 : Blo 1399519 2991629 := bbase (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) (by norm_num)
theorem B6727205 : Blo 1399519 6727205 := bbase (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) (by norm_num)
theorem B1574473 : Blo 1399519 1574473 := bbase (se 2 (by rfl) ⟨590427, by rfl⟩ : syracuseStep 1574473 = 1180855) (by norm_num)
theorem B1574509 : Blo 1399519 1574509 := bbase (se 3 (by rfl) ⟨295220, by rfl⟩ : syracuseStep 1574509 = 590441) (by norm_num)
theorem B1574545 : Blo 1399519 1574545 := bbase (se 2 (by rfl) ⟨590454, by rfl⟩ : syracuseStep 1574545 = 1180909) (by norm_num)
theorem B7677589 : Blo 1399519 7677589 := bbase (se 6 (by rfl) ⟨179943, by rfl⟩ : syracuseStep 7677589 = 359887) (by norm_num)
theorem B1574581 : Blo 1399519 1574581 := bbase (se 5 (by rfl) ⟨73808, by rfl⟩ : syracuseStep 1574581 = 147617) (by norm_num)
theorem B1574617 : Blo 1399519 1574617 := bbase (se 2 (by rfl) ⟨590481, by rfl⟩ : syracuseStep 1574617 = 1180963) (by norm_num)
theorem B1574653 : Blo 1399519 1574653 := bbase (se 3 (by rfl) ⟨295247, by rfl⟩ : syracuseStep 1574653 = 590495) (by norm_num)
theorem B5318405 : Blo 1399519 5318405 := bbase (se 4 (by rfl) ⟨498600, by rfl⟩ : syracuseStep 5318405 = 997201) (by norm_num)
theorem B7669525 : Blo 1399519 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B1574689 : Blo 1399519 1574689 := bbase (se 2 (by rfl) ⟨590508, by rfl⟩ : syracuseStep 1574689 = 1181017) (by norm_num)
theorem B1574725 : Blo 1399519 1574725 := bbase (se 4 (by rfl) ⟨147630, by rfl⟩ : syracuseStep 1574725 = 295261) (by norm_num)
theorem B1419077 : Blo 1399519 1419077 := bbase (se 4 (by rfl) ⟨133038, by rfl⟩ : syracuseStep 1419077 = 266077) (by norm_num)
theorem B23938901 : Blo 1399519 23938901 := bbase (se 9 (by rfl) ⟨70133, by rfl⟩ : syracuseStep 23938901 = 140267) (by norm_num)
theorem B1574761 : Blo 1399519 1574761 := bbase (se 2 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 1574761 = 1181071) (by norm_num)
theorem B4794229 : Blo 1399519 4794229 := bbase (se 5 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 4794229 = 449459) (by norm_num)
theorem B1574797 : Blo 1399519 1574797 := bbase (se 3 (by rfl) ⟨295274, by rfl⟩ : syracuseStep 1574797 = 590549) (by norm_num)
theorem B1771409 : Blo 1399519 1771409 := bbase (se 2 (by rfl) ⟨664278, by rfl⟩ : syracuseStep 1771409 = 1328557) (by norm_num)
theorem B4728725 : Blo 1399519 4728725 := bbase (se 6 (by rfl) ⟨110829, by rfl⟩ : syracuseStep 4728725 = 221659) (by norm_num)
theorem B6727589 : Blo 1399519 6727589 := bbase (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) (by norm_num)
theorem B1574833 : Blo 1399519 1574833 := bbase (se 2 (by rfl) ⟨590562, by rfl⟩ : syracuseStep 1574833 = 1181125) (by norm_num)
theorem B5392325 : Blo 1399519 5392325 := bbase (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) (by norm_num)
theorem B1771465 : Blo 1399519 1771465 := bbase (se 2 (by rfl) ⟨664299, by rfl⟩ : syracuseStep 1771465 = 1328599) (by norm_num)
theorem B1574869 : Blo 1399519 1574869 := bbase (se 7 (by rfl) ⟨18455, by rfl⟩ : syracuseStep 1574869 = 36911) (by norm_num)
theorem B1574905 : Blo 1399519 1574905 := bbase (se 2 (by rfl) ⟨590589, by rfl⟩ : syracuseStep 1574905 = 1181179) (by norm_num)
theorem B1574941 : Blo 1399519 1574941 := bbase (se 3 (by rfl) ⟨295301, by rfl⟩ : syracuseStep 1574941 = 590603) (by norm_num)
theorem B5318693 : Blo 1399519 5318693 := bbase (se 4 (by rfl) ⟨498627, by rfl⟩ : syracuseStep 5318693 = 997255) (by norm_num)
theorem B1771561 : Blo 1399519 1771561 := bbase (se 2 (by rfl) ⟨664335, by rfl⟩ : syracuseStep 1771561 = 1328671) (by norm_num)
theorem B1574977 : Blo 1399519 1574977 := bbase (se 2 (by rfl) ⟨590616, by rfl⟩ : syracuseStep 1574977 = 1181233) (by norm_num)
theorem B2099285 : Blo 1399519 2099285 := bbase (se 8 (by rfl) ⟨12300, by rfl⟩ : syracuseStep 2099285 = 24601) (by norm_num)
theorem B1575013 : Blo 1399519 1575013 := bbase (se 4 (by rfl) ⟨147657, by rfl⟩ : syracuseStep 1575013 = 295315) (by norm_num)
theorem B2099309 : Blo 1399519 2099309 := bbase (se 3 (by rfl) ⟨393620, by rfl⟩ : syracuseStep 2099309 = 787241) (by norm_num)
theorem B2099333 : Blo 1399519 2099333 := bbase (se 4 (by rfl) ⟨196812, by rfl⟩ : syracuseStep 2099333 = 393625) (by norm_num)
theorem B2992261 : Blo 1399519 2992261 := bbase (se 4 (by rfl) ⟨280524, by rfl⟩ : syracuseStep 2992261 = 561049) (by norm_num)
theorem B1575049 : Blo 1399519 1575049 := bbase (se 2 (by rfl) ⟨590643, by rfl⟩ : syracuseStep 1575049 = 1181287) (by norm_num)
theorem B1992853 : Blo 1399519 1992853 := bbase (se 6 (by rfl) ⟨46707, by rfl⟩ : syracuseStep 1992853 = 93415) (by norm_num)
theorem B2099357 : Blo 1399519 2099357 := bbase (se 3 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 2099357 = 787259) (by norm_num)
theorem B1419425 : Blo 1399519 1419425 := bbase (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) (by norm_num)
theorem B1575085 : Blo 1399519 1575085 := bbase (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) (by norm_num)
theorem B2099381 : Blo 1399519 2099381 := bbase (se 5 (by rfl) ⟨98408, by rfl⟩ : syracuseStep 2099381 = 196817) (by norm_num)
theorem B7088309 : Blo 1399519 7088309 := bbase (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) (by norm_num)
theorem B2099405 : Blo 1399519 2099405 := bbase (se 3 (by rfl) ⟨393638, by rfl⟩ : syracuseStep 2099405 = 787277) (by norm_num)
theorem B1575121 : Blo 1399519 1575121 := bbase (se 2 (by rfl) ⟨590670, by rfl⟩ : syracuseStep 1575121 = 1181341) (by norm_num)
theorem B1771733 : Blo 1399519 1771733 := bbase (se 7 (by rfl) ⟨20762, by rfl⟩ : syracuseStep 1771733 = 41525) (by norm_num)
theorem B7678165 : Blo 1399519 7678165 := bbase (se 7 (by rfl) ⟨89978, by rfl⟩ : syracuseStep 7678165 = 179957) (by norm_num)
theorem B2099429 : Blo 1399519 2099429 := bbase (se 4 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 2099429 = 393643) (by norm_num)
theorem B5982437 : Blo 1399519 5982437 := bbase (se 4 (by rfl) ⟨560853, by rfl⟩ : syracuseStep 5982437 = 1121707) (by norm_num)
theorem B1575157 : Blo 1399519 1575157 := bbase (se 5 (by rfl) ⟨73835, by rfl⟩ : syracuseStep 1575157 = 147671) (by norm_num)
theorem B2099453 : Blo 1399519 2099453 := bbase (se 3 (by rfl) ⟨393647, by rfl⟩ : syracuseStep 2099453 = 787295) (by norm_num)
theorem B1771789 : Blo 1399519 1771789 := bbase (se 3 (by rfl) ⟨332210, by rfl⟩ : syracuseStep 1771789 = 664421) (by norm_num)
theorem B2099477 : Blo 1399519 2099477 := bbase (se 6 (by rfl) ⟨49206, by rfl⟩ : syracuseStep 2099477 = 98413) (by norm_num)
theorem B1575193 : Blo 1399519 1575193 := bbase (se 2 (by rfl) ⟨590697, by rfl⟩ : syracuseStep 1575193 = 1181395) (by norm_num)
theorem B1681705 : Blo 1399519 1681705 := bbase (se 2 (by rfl) ⟨630639, by rfl⟩ : syracuseStep 1681705 = 1261279) (by norm_num)
theorem B2099501 : Blo 1399519 2099501 := bbase (se 3 (by rfl) ⟨393656, by rfl⟩ : syracuseStep 2099501 = 787313) (by norm_num)
theorem B1575229 : Blo 1399519 1575229 := bbase (se 3 (by rfl) ⟨295355, by rfl⟩ : syracuseStep 1575229 = 590711) (by norm_num)
theorem B2099525 : Blo 1399519 2099525 := bbase (se 4 (by rfl) ⟨196830, by rfl⟩ : syracuseStep 2099525 = 393661) (by norm_num)
theorem B4729157 : Blo 1399519 4729157 := bbase (se 4 (by rfl) ⟨443358, by rfl⟩ : syracuseStep 4729157 = 886717) (by norm_num)
theorem B2099549 : Blo 1399519 2099549 := bbase (se 3 (by rfl) ⟨393665, by rfl⟩ : syracuseStep 2099549 = 787331) (by norm_num)
theorem B1575265 : Blo 1399519 1575265 := bbase (se 2 (by rfl) ⟨590724, by rfl⟩ : syracuseStep 1575265 = 1181449) (by norm_num)
theorem B1771885 : Blo 1399519 1771885 := bbase (se 3 (by rfl) ⟨332228, by rfl⟩ : syracuseStep 1771885 = 664457) (by norm_num)
theorem B2099573 : Blo 1399519 2099573 := bbase (se 5 (by rfl) ⟨98417, by rfl⟩ : syracuseStep 2099573 = 196835) (by norm_num)
theorem B2427253 : Blo 1399519 2427253 := bbase (se 5 (by rfl) ⟨113777, by rfl⟩ : syracuseStep 2427253 = 227555) (by norm_num)
theorem B1706365 : Blo 1399519 1706365 := bbase (se 3 (by rfl) ⟨319943, by rfl⟩ : syracuseStep 1706365 = 639887) (by norm_num)
theorem B1575301 : Blo 1399519 1575301 := bbase (se 4 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 1575301 = 295369) (by norm_num)
theorem B2099597 : Blo 1399519 2099597 := bbase (se 3 (by rfl) ⟨393674, by rfl⟩ : syracuseStep 2099597 = 787349) (by norm_num)
theorem B2361757 : Blo 1399519 2361757 := bbase (se 3 (by rfl) ⟨442829, by rfl⟩ : syracuseStep 2361757 = 885659) (by norm_num)
theorem B2099621 : Blo 1399519 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B1575337 : Blo 1399519 1575337 := bbase (se 2 (by rfl) ⟨590751, by rfl⟩ : syracuseStep 1575337 = 1181503) (by norm_num)
theorem B2099645 : Blo 1399519 2099645 := bbase (se 3 (by rfl) ⟨393683, by rfl⟩ : syracuseStep 2099645 = 787367) (by norm_num)
theorem B1575373 : Blo 1399519 1575373 := bbase (se 3 (by rfl) ⟨295382, by rfl⟩ : syracuseStep 1575373 = 590765) (by norm_num)
theorem B2099669 : Blo 1399519 2099669 := bbase (se 7 (by rfl) ⟨24605, by rfl⟩ : syracuseStep 2099669 = 49211) (by norm_num)
theorem B1993189 : Blo 1399519 1993189 := bbase (se 4 (by rfl) ⟨186861, by rfl⟩ : syracuseStep 1993189 = 373723) (by norm_num)
theorem B2099693 : Blo 1399519 2099693 := bbase (se 3 (by rfl) ⟨393692, by rfl⟩ : syracuseStep 2099693 = 787385) (by norm_num)
theorem B1575409 : Blo 1399519 1575409 := bbase (se 2 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 1575409 = 1181557) (by norm_num)
theorem B2361845 : Blo 1399519 2361845 := bbase (se 5 (by rfl) ⟨110711, by rfl⟩ : syracuseStep 2361845 = 221423) (by norm_num)
theorem B2099717 : Blo 1399519 2099717 := bbase (se 4 (by rfl) ⟨196848, by rfl⟩ : syracuseStep 2099717 = 393697) (by norm_num)
theorem B1575445 : Blo 1399519 1575445 := bbase (se 6 (by rfl) ⟨36924, by rfl⟩ : syracuseStep 1575445 = 73849) (by norm_num)
theorem B1772057 : Blo 1399519 1772057 := bbase (se 2 (by rfl) ⟨664521, by rfl⟩ : syracuseStep 1772057 = 1329043) (by norm_num)
theorem B2099741 : Blo 1399519 2099741 := bbase (se 3 (by rfl) ⟨393701, by rfl⟩ : syracuseStep 2099741 = 787403) (by norm_num)
theorem B2099765 : Blo 1399519 2099765 := bbase (se 5 (by rfl) ⟨98426, by rfl⟩ : syracuseStep 2099765 = 196853) (by norm_num)
theorem B1575481 : Blo 1399519 1575481 := bbase (se 2 (by rfl) ⟨590805, by rfl⟩ : syracuseStep 1575481 = 1181611) (by norm_num)
theorem B2099789 : Blo 1399519 2099789 := bbase (se 3 (by rfl) ⟨393710, by rfl⟩ : syracuseStep 2099789 = 787421) (by norm_num)
theorem B1772113 : Blo 1399519 1772113 := bbase (se 2 (by rfl) ⟨664542, by rfl⟩ : syracuseStep 1772113 = 1329085) (by norm_num)
theorem B1575517 : Blo 1399519 1575517 := bbase (se 3 (by rfl) ⟨295409, by rfl⟩ : syracuseStep 1575517 = 590819) (by norm_num)
theorem B2099813 : Blo 1399519 2099813 := bbase (se 4 (by rfl) ⟨196857, by rfl⟩ : syracuseStep 2099813 = 393715) (by norm_num)
theorem B2361973 : Blo 1399519 2361973 := bbase (se 5 (by rfl) ⟨110717, by rfl⟩ : syracuseStep 2361973 = 221435) (by norm_num)
theorem B7981685 : Blo 1399519 7981685 := bbase (se 5 (by rfl) ⟨374141, by rfl⟩ : syracuseStep 7981685 = 748283) (by norm_num)
theorem B2099837 : Blo 1399519 2099837 := bbase (se 3 (by rfl) ⟨393719, by rfl⟩ : syracuseStep 2099837 = 787439) (by norm_num)
theorem B1575553 : Blo 1399519 1575553 := bbase (se 2 (by rfl) ⟨590832, by rfl⟩ : syracuseStep 1575553 = 1181665) (by norm_num)
theorem B2656901 : Blo 1399519 2656901 := bbase (se 4 (by rfl) ⟨249084, by rfl⟩ : syracuseStep 2656901 = 498169) (by norm_num)
theorem B2099861 : Blo 1399519 2099861 := bbase (se 6 (by rfl) ⟨49215, by rfl⟩ : syracuseStep 2099861 = 98431) (by norm_num)
theorem B15960725 : Blo 1399519 15960725 := bbase (se 6 (by rfl) ⟨374079, by rfl⟩ : syracuseStep 15960725 = 748159) (by norm_num)
theorem B1575589 : Blo 1399519 1575589 := bbase (se 4 (by rfl) ⟨147711, by rfl⟩ : syracuseStep 1575589 = 295423) (by norm_num)
theorem B2099885 : Blo 1399519 2099885 := bbase (se 3 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 2099885 = 787457) (by norm_num)
theorem B1772209 : Blo 1399519 1772209 := bbase (se 2 (by rfl) ⟨664578, by rfl⟩ : syracuseStep 1772209 = 1329157) (by norm_num)
theorem B1993405 : Blo 1399519 1993405 := bbase (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) (by norm_num)
theorem B2099909 : Blo 1399519 2099909 := bbase (se 4 (by rfl) ⟨196866, by rfl⟩ : syracuseStep 2099909 = 393733) (by norm_num)
theorem B1419973 : Blo 1399519 1419973 := bbase (se 4 (by rfl) ⟨133122, by rfl⟩ : syracuseStep 1419973 = 266245) (by norm_num)
theorem B1575625 : Blo 1399519 1575625 := bbase (se 2 (by rfl) ⟨590859, by rfl⟩ : syracuseStep 1575625 = 1181719) (by norm_num)
theorem B1419977 : Blo 1399519 1419977 := bbase (se 2 (by rfl) ⟨532491, by rfl⟩ : syracuseStep 1419977 = 1064983) (by norm_num)
theorem B2362061 : Blo 1399519 2362061 := bbase (se 3 (by rfl) ⟨442886, by rfl⟩ : syracuseStep 2362061 = 885773) (by norm_num)
theorem B2099933 : Blo 1399519 2099933 := bbase (se 3 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 2099933 = 787475) (by norm_num)
theorem B1575661 : Blo 1399519 1575661 := bbase (se 3 (by rfl) ⟨295436, by rfl⟩ : syracuseStep 1575661 = 590873) (by norm_num)
theorem B4483829 : Blo 1399519 4483829 := bbase (se 5 (by rfl) ⟨210179, by rfl⟩ : syracuseStep 4483829 = 420359) (by norm_num)
theorem B2099957 : Blo 1399519 2099957 := bbase (se 5 (by rfl) ⟨98435, by rfl⟩ : syracuseStep 2099957 = 196871) (by norm_num)
theorem B4729589 : Blo 1399519 4729589 := bbase (se 5 (by rfl) ⟨221699, by rfl⟩ : syracuseStep 4729589 = 443399) (by norm_num)
theorem B2099981 : Blo 1399519 2099981 := bbase (se 3 (by rfl) ⟨393746, by rfl⟩ : syracuseStep 2099981 = 787493) (by norm_num)
theorem B1575697 : Blo 1399519 1575697 := bbase (se 2 (by rfl) ⟨590886, by rfl⟩ : syracuseStep 1575697 = 1181773) (by norm_num)
theorem B2657053 : Blo 1399519 2657053 := bbase (se 3 (by rfl) ⟨498197, by rfl⟩ : syracuseStep 2657053 = 996395) (by norm_num)
theorem B2100005 : Blo 1399519 2100005 := bbase (se 4 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 2100005 = 393751) (by norm_num)
theorem B1575733 : Blo 1399519 1575733 := bbase (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) (by norm_num)
theorem B2100029 : Blo 1399519 2100029 := bbase (se 3 (by rfl) ⟨393755, by rfl⟩ : syracuseStep 2100029 = 787511) (by norm_num)
theorem B2362189 : Blo 1399519 2362189 := bbase (se 3 (by rfl) ⟨442910, by rfl⟩ : syracuseStep 2362189 = 885821) (by norm_num)
theorem B2157397 : Blo 1399519 2157397 := bbase (se 9 (by rfl) ⟨6320, by rfl⟩ : syracuseStep 2157397 = 12641) (by norm_num)
theorem B2100053 : Blo 1399519 2100053 := bbase (se 9 (by rfl) ⟨6152, by rfl⟩ : syracuseStep 2100053 = 12305) (by norm_num)
theorem B1575769 : Blo 1399519 1575769 := bbase (se 2 (by rfl) ⟨590913, by rfl⟩ : syracuseStep 1575769 = 1181827) (by norm_num)
theorem B1772381 : Blo 1399519 1772381 := bbase (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) (by norm_num)
theorem B5679973 : Blo 1399519 5679973 := bbase (se 4 (by rfl) ⟨532497, by rfl⟩ : syracuseStep 5679973 = 1064995) (by norm_num)
theorem B2100077 : Blo 1399519 2100077 := bbase (se 3 (by rfl) ⟨393764, by rfl⟩ : syracuseStep 2100077 = 787529) (by norm_num)
theorem B1575805 : Blo 1399519 1575805 := bbase (se 3 (by rfl) ⟨295463, by rfl⟩ : syracuseStep 1575805 = 590927) (by norm_num)
theorem B2100101 : Blo 1399519 2100101 := bbase (se 4 (by rfl) ⟨196884, by rfl⟩ : syracuseStep 2100101 = 393769) (by norm_num)
theorem B2395021 : Blo 1399519 2395021 := bbase (se 3 (by rfl) ⟨449066, by rfl⟩ : syracuseStep 2395021 = 898133) (by norm_num)
theorem B1772437 : Blo 1399519 1772437 := bbase (se 6 (by rfl) ⟨41541, by rfl⟩ : syracuseStep 1772437 = 83083) (by norm_num)
theorem B2100125 : Blo 1399519 2100125 := bbase (se 3 (by rfl) ⟨393773, by rfl⟩ : syracuseStep 2100125 = 787547) (by norm_num)
theorem B1575841 : Blo 1399519 1575841 := bbase (se 2 (by rfl) ⟨590940, by rfl⟩ : syracuseStep 1575841 = 1181881) (by norm_num)
theorem B2362277 : Blo 1399519 2362277 := bbase (se 4 (by rfl) ⟨221463, by rfl⟩ : syracuseStep 2362277 = 442927) (by norm_num)
theorem B2100149 : Blo 1399519 2100149 := bbase (se 5 (by rfl) ⟨98444, by rfl⟩ : syracuseStep 2100149 = 196889) (by norm_num)
theorem B1575877 : Blo 1399519 1575877 := bbase (se 4 (by rfl) ⟨147738, by rfl⟩ : syracuseStep 1575877 = 295477) (by norm_num)
theorem B2100173 : Blo 1399519 2100173 := bbase (se 3 (by rfl) ⟨393782, by rfl⟩ : syracuseStep 2100173 = 787565) (by norm_num)
theorem B2100197 : Blo 1399519 2100197 := bbase (se 4 (by rfl) ⟨196893, by rfl⟩ : syracuseStep 2100197 = 393787) (by norm_num)
theorem B1575913 : Blo 1399519 1575913 := bbase (se 2 (by rfl) ⟨590967, by rfl⟩ : syracuseStep 1575913 = 1181935) (by norm_num)
theorem B11348981 : Blo 1399519 11348981 := bbase (se 5 (by rfl) ⟨531983, by rfl⟩ : syracuseStep 11348981 = 1063967) (by norm_num)
theorem B1772533 : Blo 1399519 1772533 := bbase (se 5 (by rfl) ⟨83087, by rfl⟩ : syracuseStep 1772533 = 166175) (by norm_num)
theorem B2100221 : Blo 1399519 2100221 := bbase (se 3 (by rfl) ⟨393791, by rfl⟩ : syracuseStep 2100221 = 787583) (by norm_num)
theorem B2993149 : Blo 1399519 2993149 := bbase (se 3 (by rfl) ⟨561215, by rfl⟩ : syracuseStep 2993149 = 1122431) (by norm_num)
theorem B1575949 : Blo 1399519 1575949 := bbase (se 3 (by rfl) ⟨295490, by rfl⟩ : syracuseStep 1575949 = 590981) (by norm_num)
theorem B2100245 : Blo 1399519 2100245 := bbase (se 6 (by rfl) ⟨49224, by rfl⟩ : syracuseStep 2100245 = 98449) (by norm_num)
theorem B2362405 : Blo 1399519 2362405 := bbase (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) (by norm_num)
theorem B2100269 : Blo 1399519 2100269 := bbase (se 3 (by rfl) ⟨393800, by rfl⟩ : syracuseStep 2100269 = 787601) (by norm_num)
theorem B1575985 : Blo 1399519 1575985 := bbase (se 2 (by rfl) ⟨590994, by rfl⟩ : syracuseStep 1575985 = 1181989) (by norm_num)
theorem B1993781 : Blo 1399519 1993781 := bbase (se 5 (by rfl) ⟨93458, by rfl⟩ : syracuseStep 1993781 = 186917) (by norm_num)
theorem B2100293 : Blo 1399519 2100293 := bbase (se 4 (by rfl) ⟨196902, by rfl⟩ : syracuseStep 2100293 = 393805) (by norm_num)
theorem B2657357 : Blo 1399519 2657357 := bbase (se 3 (by rfl) ⟨498254, by rfl⟩ : syracuseStep 2657357 = 996509) (by norm_num)
theorem B1576021 : Blo 1399519 1576021 := bbase (se 8 (by rfl) ⟨9234, by rfl⟩ : syracuseStep 1576021 = 18469) (by norm_num)
theorem B2100317 : Blo 1399519 2100317 := bbase (se 3 (by rfl) ⟨393809, by rfl⟩ : syracuseStep 2100317 = 787619) (by norm_num)
theorem B2100341 : Blo 1399519 2100341 := bbase (se 5 (by rfl) ⟨98453, by rfl⟩ : syracuseStep 2100341 = 196907) (by norm_num)
theorem B2993269 : Blo 1399519 2993269 := bbase (se 5 (by rfl) ⟨140309, by rfl⟩ : syracuseStep 2993269 = 280619) (by norm_num)
theorem B1576057 : Blo 1399519 1576057 := bbase (se 2 (by rfl) ⟨591021, by rfl⟩ : syracuseStep 1576057 = 1182043) (by norm_num)
theorem B2362493 : Blo 1399519 2362493 := bbase (se 3 (by rfl) ⟨442967, by rfl⟩ : syracuseStep 2362493 = 885935) (by norm_num)
theorem B2100365 : Blo 1399519 2100365 := bbase (se 3 (by rfl) ⟨393818, by rfl⟩ : syracuseStep 2100365 = 787637) (by norm_num)
theorem B1576093 : Blo 1399519 1576093 := bbase (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) (by norm_num)
theorem B1772705 : Blo 1399519 1772705 := bbase (se 2 (by rfl) ⟨664764, by rfl⟩ : syracuseStep 1772705 = 1329529) (by norm_num)
theorem B2100389 : Blo 1399519 2100389 := bbase (se 4 (by rfl) ⟨196911, by rfl⟩ : syracuseStep 2100389 = 393823) (by norm_num)
theorem B4730021 : Blo 1399519 4730021 := bbase (se 4 (by rfl) ⟨443439, by rfl⟩ : syracuseStep 4730021 = 886879) (by norm_num)
theorem B3148973 : Blo 1399519 3148973 := bbase (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) (by norm_num)
theorem B11349173 : Blo 1399519 11349173 := bbase (se 5 (by rfl) ⟨531992, by rfl⟩ : syracuseStep 11349173 = 1063985) (by norm_num)
theorem B2100413 : Blo 1399519 2100413 := bbase (se 3 (by rfl) ⟨393827, by rfl⟩ : syracuseStep 2100413 = 787655) (by norm_num)
theorem B1576129 : Blo 1399519 1576129 := bbase (se 2 (by rfl) ⟨591048, by rfl⟩ : syracuseStep 1576129 = 1182097) (by norm_num)
theorem B5319877 : Blo 1399519 5319877 := bbase (se 4 (by rfl) ⟨498738, by rfl⟩ : syracuseStep 5319877 = 997477) (by norm_num)
theorem B2100437 : Blo 1399519 2100437 := bbase (se 7 (by rfl) ⟨24614, by rfl⟩ : syracuseStep 2100437 = 49229) (by norm_num)
theorem B1772761 : Blo 1399519 1772761 := bbase (se 2 (by rfl) ⟨664785, by rfl⟩ : syracuseStep 1772761 = 1329571) (by norm_num)
theorem B1576165 : Blo 1399519 1576165 := bbase (se 4 (by rfl) ⟨147765, by rfl⟩ : syracuseStep 1576165 = 295531) (by norm_num)
theorem B2100461 : Blo 1399519 2100461 := bbase (se 3 (by rfl) ⟨393836, by rfl⟩ : syracuseStep 2100461 = 787673) (by norm_num)
theorem B3149045 : Blo 1399519 3149045 := bbase (se 5 (by rfl) ⟨147611, by rfl⟩ : syracuseStep 3149045 = 295223) (by norm_num)
theorem B2837749 : Blo 1399519 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B2362621 : Blo 1399519 2362621 := bbase (se 3 (by rfl) ⟨442991, by rfl⟩ : syracuseStep 2362621 = 885983) (by norm_num)
theorem B2100485 : Blo 1399519 2100485 := bbase (se 4 (by rfl) ⟨196920, by rfl⟩ : syracuseStep 2100485 = 393841) (by norm_num)
theorem B1576201 : Blo 1399519 1576201 := bbase (se 2 (by rfl) ⟨591075, by rfl⟩ : syracuseStep 1576201 = 1182151) (by norm_num)
theorem B2100509 : Blo 1399519 2100509 := bbase (se 3 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 2100509 = 787691) (by norm_num)
theorem B1576237 : Blo 1399519 1576237 := bbase (se 3 (by rfl) ⟨295544, by rfl⟩ : syracuseStep 1576237 = 591089) (by norm_num)
theorem B2100533 : Blo 1399519 2100533 := bbase (se 5 (by rfl) ⟨98462, by rfl⟩ : syracuseStep 2100533 = 196925) (by norm_num)
theorem B1772857 : Blo 1399519 1772857 := bbase (se 2 (by rfl) ⟨664821, by rfl⟩ : syracuseStep 1772857 = 1329643) (by norm_num)
theorem B3149117 : Blo 1399519 3149117 := bbase (se 3 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 3149117 = 1180919) (by norm_num)
theorem B2100557 : Blo 1399519 2100557 := bbase (se 3 (by rfl) ⟨393854, by rfl⟩ : syracuseStep 2100557 = 787709) (by norm_num)
theorem B1576273 : Blo 1399519 1576273 := bbase (se 2 (by rfl) ⟨591102, by rfl⟩ : syracuseStep 1576273 = 1182205) (by norm_num)
theorem B2362709 : Blo 1399519 2362709 := bbase (se 11 (by rfl) ⟨1730, by rfl⟩ : syracuseStep 2362709 = 3461) (by norm_num)
theorem B2100581 : Blo 1399519 2100581 := bbase (se 4 (by rfl) ⟨196929, by rfl⟩ : syracuseStep 2100581 = 393859) (by norm_num)
theorem B1576309 : Blo 1399519 1576309 := bbase (se 5 (by rfl) ⟨73889, by rfl⟩ : syracuseStep 1576309 = 147779) (by norm_num)
theorem B2100605 : Blo 1399519 2100605 := bbase (se 3 (by rfl) ⟨393863, by rfl⟩ : syracuseStep 2100605 = 787727) (by norm_num)
theorem B3149189 : Blo 1399519 3149189 := bbase (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) (by norm_num)
theorem B2100629 : Blo 1399519 2100629 := bbase (se 6 (by rfl) ⟨49233, by rfl⟩ : syracuseStep 2100629 = 98467) (by norm_num)
theorem B1576345 : Blo 1399519 1576345 := bbase (se 2 (by rfl) ⟨591129, by rfl⟩ : syracuseStep 1576345 = 1182259) (by norm_num)
theorem B2100653 : Blo 1399519 2100653 := bbase (se 3 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 2100653 = 787745) (by norm_num)
theorem B1576381 : Blo 1399519 1576381 := bbase (se 3 (by rfl) ⟨295571, by rfl⟩ : syracuseStep 1576381 = 591143) (by norm_num)
theorem B7089605 : Blo 1399519 7089605 := bbase (se 4 (by rfl) ⟨664650, by rfl⟩ : syracuseStep 7089605 = 1329301) (by norm_num)
theorem B2100677 : Blo 1399519 2100677 := bbase (se 4 (by rfl) ⟨196938, by rfl⟩ : syracuseStep 2100677 = 393877) (by norm_num)
theorem B3149261 : Blo 1399519 3149261 := bbase (se 3 (by rfl) ⟨590486, by rfl⟩ : syracuseStep 3149261 = 1180973) (by norm_num)
theorem B1682893 : Blo 1399519 1682893 := bbase (se 3 (by rfl) ⟨315542, by rfl⟩ : syracuseStep 1682893 = 631085) (by norm_num)
theorem B17935829 : Blo 1399519 17935829 := bbase (se 7 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 17935829 = 420371) (by norm_num)
theorem B2362837 : Blo 1399519 2362837 := bbase (se 7 (by rfl) ⟨27689, by rfl⟩ : syracuseStep 2362837 = 55379) (by norm_num)
theorem B2100701 : Blo 1399519 2100701 := bbase (se 3 (by rfl) ⟨393881, by rfl⟩ : syracuseStep 2100701 = 787763) (by norm_num)
theorem B1576417 : Blo 1399519 1576417 := bbase (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) (by norm_num)
theorem B1773029 : Blo 1399519 1773029 := bbase (se 4 (by rfl) ⟨166221, by rfl⟩ : syracuseStep 1773029 = 332443) (by norm_num)
theorem B2100725 : Blo 1399519 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B5320181 : Blo 1399519 5320181 := bbase (se 5 (by rfl) ⟨249383, by rfl⟩ : syracuseStep 5320181 = 498767) (by norm_num)
theorem B1576453 : Blo 1399519 1576453 := bbase (se 4 (by rfl) ⟨147792, by rfl⟩ : syracuseStep 1576453 = 295585) (by norm_num)
theorem B2100749 : Blo 1399519 2100749 := bbase (se 3 (by rfl) ⟨393890, by rfl⟩ : syracuseStep 2100749 = 787781) (by norm_num)
theorem B3149333 : Blo 1399519 3149333 := bbase (se 6 (by rfl) ⟨73812, by rfl⟩ : syracuseStep 3149333 = 147625) (by norm_num)
theorem B13454869 : Blo 1399519 13454869 := bbase (se 6 (by rfl) ⟨315348, by rfl⟩ : syracuseStep 13454869 = 630697) (by norm_num)
theorem B1773085 : Blo 1399519 1773085 := bbase (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) (by norm_num)
theorem B2100773 : Blo 1399519 2100773 := bbase (se 4 (by rfl) ⟨196947, by rfl⟩ : syracuseStep 2100773 = 393895) (by norm_num)
theorem B1576489 : Blo 1399519 1576489 := bbase (se 2 (by rfl) ⟨591183, by rfl⟩ : syracuseStep 1576489 = 1182367) (by norm_num)
theorem B2362925 : Blo 1399519 2362925 := bbase (se 3 (by rfl) ⟨443048, by rfl⟩ : syracuseStep 2362925 = 886097) (by norm_num)
theorem B2100797 : Blo 1399519 2100797 := bbase (se 3 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 2100797 = 787799) (by norm_num)
theorem B1576525 : Blo 1399519 1576525 := bbase (se 3 (by rfl) ⟨295598, by rfl⟩ : syracuseStep 1576525 = 591197) (by norm_num)
theorem B2100821 : Blo 1399519 2100821 := bbase (se 8 (by rfl) ⟨12309, by rfl⟩ : syracuseStep 2100821 = 24619) (by norm_num)
theorem B3149405 : Blo 1399519 3149405 := bbase (se 3 (by rfl) ⟨590513, by rfl⟩ : syracuseStep 3149405 = 1181027) (by norm_num)
theorem B2100845 : Blo 1399519 2100845 := bbase (se 3 (by rfl) ⟨393908, by rfl⟩ : syracuseStep 2100845 = 787817) (by norm_num)
theorem B1576561 : Blo 1399519 1576561 := bbase (se 2 (by rfl) ⟨591210, by rfl⟩ : syracuseStep 1576561 = 1182421) (by norm_num)
theorem B1773181 : Blo 1399519 1773181 := bbase (se 3 (by rfl) ⟨332471, by rfl⟩ : syracuseStep 1773181 = 664943) (by norm_num)
theorem B1494661 : Blo 1399519 1494661 := bbase (se 4 (by rfl) ⟨140124, by rfl⟩ : syracuseStep 1494661 = 280249) (by norm_num)
theorem B2100869 : Blo 1399519 2100869 := bbase (se 4 (by rfl) ⟨196956, by rfl⟩ : syracuseStep 2100869 = 393913) (by norm_num)
theorem B5049989 : Blo 1399519 5049989 := bbase (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) (by norm_num)
theorem B1683085 : Blo 1399519 1683085 := bbase (se 3 (by rfl) ⟨315578, by rfl⟩ : syracuseStep 1683085 = 631157) (by norm_num)
theorem B1576597 : Blo 1399519 1576597 := bbase (se 6 (by rfl) ⟨36951, by rfl⟩ : syracuseStep 1576597 = 73903) (by norm_num)
theorem B2100893 : Blo 1399519 2100893 := bbase (se 3 (by rfl) ⟨393917, by rfl⟩ : syracuseStep 2100893 = 787835) (by norm_num)
theorem B3149477 : Blo 1399519 3149477 := bbase (se 4 (by rfl) ⟨295263, by rfl⟩ : syracuseStep 3149477 = 590527) (by norm_num)
theorem B2363053 : Blo 1399519 2363053 := bbase (se 3 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 2363053 = 886145) (by norm_num)
theorem B3239597 : Blo 1399519 3239597 := bbase (se 3 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 3239597 = 1214849) (by norm_num)
theorem B2100917 : Blo 1399519 2100917 := bbase (se 5 (by rfl) ⟨98480, by rfl⟩ : syracuseStep 2100917 = 196961) (by norm_num)
theorem B1576633 : Blo 1399519 1576633 := bbase (se 2 (by rfl) ⟨591237, by rfl⟩ : syracuseStep 1576633 = 1182475) (by norm_num)
theorem B3542717 : Blo 1399519 3542717 := bbase (se 3 (by rfl) ⟨664259, by rfl⟩ : syracuseStep 3542717 = 1328519) (by norm_num)
theorem B1494721 : Blo 1399519 1494721 := bbase (se 2 (by rfl) ⟨560520, by rfl⟩ : syracuseStep 1494721 = 1121041) (by norm_num)
theorem B2100941 : Blo 1399519 2100941 := bbase (se 3 (by rfl) ⟨393926, by rfl⟩ : syracuseStep 2100941 = 787853) (by norm_num)
theorem B1576669 : Blo 1399519 1576669 := bbase (se 3 (by rfl) ⟨295625, by rfl⟩ : syracuseStep 1576669 = 591251) (by norm_num)
theorem B2100965 : Blo 1399519 2100965 := bbase (se 4 (by rfl) ⟨196965, by rfl⟩ : syracuseStep 2100965 = 393931) (by norm_num)
theorem B3149549 : Blo 1399519 3149549 := bbase (se 3 (by rfl) ⟨590540, by rfl⟩ : syracuseStep 3149549 = 1181081) (by norm_num)
theorem B1683185 : Blo 1399519 1683185 := bbase (se 2 (by rfl) ⟨631194, by rfl⟩ : syracuseStep 1683185 = 1262389) (by norm_num)
theorem B2100989 : Blo 1399519 2100989 := bbase (se 3 (by rfl) ⟨393935, by rfl⟩ : syracuseStep 2100989 = 787871) (by norm_num)
theorem B1576705 : Blo 1399519 1576705 := bbase (se 2 (by rfl) ⟨591264, by rfl⟩ : syracuseStep 1576705 = 1182529) (by norm_num)
theorem B2363141 : Blo 1399519 2363141 := bbase (se 4 (by rfl) ⟨221544, by rfl⟩ : syracuseStep 2363141 = 443089) (by norm_num)
theorem B2101013 : Blo 1399519 2101013 := bbase (se 6 (by rfl) ⟨49242, by rfl⟩ : syracuseStep 2101013 = 98485) (by norm_num)
theorem B1773353 : Blo 1399519 1773353 := bbase (se 2 (by rfl) ⟨665007, by rfl⟩ : syracuseStep 1773353 = 1330015) (by norm_num)
theorem B2101037 : Blo 1399519 2101037 := bbase (se 3 (by rfl) ⟨393944, by rfl⟩ : syracuseStep 2101037 = 787889) (by norm_num)
theorem B3149621 : Blo 1399519 3149621 := bbase (se 5 (by rfl) ⟨147638, by rfl⟩ : syracuseStep 3149621 = 295277) (by norm_num)
theorem B2658109 : Blo 1399519 2658109 := bbase (se 3 (by rfl) ⟨498395, by rfl⟩ : syracuseStep 2658109 = 996791) (by norm_num)
theorem B2879293 : Blo 1399519 2879293 := bbase (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) (by norm_num)
theorem B2101061 : Blo 1399519 2101061 := bbase (se 4 (by rfl) ⟨196974, by rfl⟩ : syracuseStep 2101061 = 393949) (by norm_num)
theorem B2101085 : Blo 1399519 2101085 := bbase (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) (by norm_num)
theorem B1773409 : Blo 1399519 1773409 := bbase (se 2 (by rfl) ⟨665028, by rfl⟩ : syracuseStep 1773409 = 1330057) (by norm_num)
theorem B2101109 : Blo 1399519 2101109 := bbase (se 5 (by rfl) ⟨98489, by rfl⟩ : syracuseStep 2101109 = 196979) (by norm_num)
theorem B3149693 : Blo 1399519 3149693 := bbase (se 3 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 3149693 = 1181135) (by norm_num)
theorem B2363269 : Blo 1399519 2363269 := bbase (se 4 (by rfl) ⟨221556, by rfl⟩ : syracuseStep 2363269 = 443113) (by norm_num)
theorem B2101133 : Blo 1399519 2101133 := bbase (se 3 (by rfl) ⟨393962, by rfl⟩ : syracuseStep 2101133 = 787925) (by norm_num)
theorem B2101157 : Blo 1399519 2101157 := bbase (se 4 (by rfl) ⟨196983, by rfl⟩ : syracuseStep 2101157 = 393967) (by norm_num)
theorem B2101181 : Blo 1399519 2101181 := bbase (se 3 (by rfl) ⟨393971, by rfl⟩ : syracuseStep 2101181 = 787943) (by norm_num)
theorem B1773505 : Blo 1399519 1773505 := bbase (se 2 (by rfl) ⟨665064, by rfl⟩ : syracuseStep 1773505 = 1330129) (by norm_num)
theorem B3149765 : Blo 1399519 3149765 := bbase (se 4 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 3149765 = 590581) (by norm_num)
theorem B2658253 : Blo 1399519 2658253 := bbase (se 3 (by rfl) ⟨498422, by rfl⟩ : syracuseStep 2658253 = 996845) (by norm_num)
theorem B2101205 : Blo 1399519 2101205 := bbase (se 7 (by rfl) ⟨24623, by rfl⟩ : syracuseStep 2101205 = 49247) (by norm_num)
theorem B2363357 : Blo 1399519 2363357 := bbase (se 3 (by rfl) ⟨443129, by rfl⟩ : syracuseStep 2363357 = 886259) (by norm_num)
theorem B2101229 : Blo 1399519 2101229 := bbase (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) (by norm_num)
theorem B1495037 : Blo 1399519 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B2101253 : Blo 1399519 2101253 := bbase (se 4 (by rfl) ⟨196992, by rfl⟩ : syracuseStep 2101253 = 393985) (by norm_num)
theorem B3149837 : Blo 1399519 3149837 := bbase (se 3 (by rfl) ⟨590594, by rfl⟩ : syracuseStep 3149837 = 1181189) (by norm_num)
theorem B3543061 : Blo 1399519 3543061 := bbase (se 6 (by rfl) ⟨83040, by rfl⟩ : syracuseStep 3543061 = 166081) (by norm_num)
theorem B2101277 : Blo 1399519 2101277 := bbase (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) (by norm_num)
theorem B2101301 : Blo 1399519 2101301 := bbase (se 5 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 2101301 = 196997) (by norm_num)
theorem B5050421 : Blo 1399519 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B2101325 : Blo 1399519 2101325 := bbase (se 3 (by rfl) ⟨393998, by rfl⟩ : syracuseStep 2101325 = 787997) (by norm_num)
theorem B3149909 : Blo 1399519 3149909 := bbase (se 8 (by rfl) ⟨18456, by rfl⟩ : syracuseStep 3149909 = 36913) (by norm_num)
theorem B2363485 : Blo 1399519 2363485 := bbase (se 3 (by rfl) ⟨443153, by rfl⟩ : syracuseStep 2363485 = 886307) (by norm_num)
theorem B2101349 : Blo 1399519 2101349 := bbase (se 4 (by rfl) ⟨197001, by rfl⟩ : syracuseStep 2101349 = 394003) (by norm_num)
theorem B2658413 : Blo 1399519 2658413 := bbase (se 3 (by rfl) ⟨498452, by rfl⟩ : syracuseStep 2658413 = 996905) (by norm_num)
theorem B1773677 : Blo 1399519 1773677 := bbase (se 3 (by rfl) ⟨332564, by rfl⟩ : syracuseStep 1773677 = 665129) (by norm_num)
theorem B2101373 : Blo 1399519 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B3543173 : Blo 1399519 3543173 := bbase (se 4 (by rfl) ⟨332172, by rfl⟩ : syracuseStep 3543173 = 664345) (by norm_num)
theorem B4485253 : Blo 1399519 4485253 := bbase (se 4 (by rfl) ⟨420492, by rfl⟩ : syracuseStep 4485253 = 840985) (by norm_num)
theorem B2101397 : Blo 1399519 2101397 := bbase (se 6 (by rfl) ⟨49251, by rfl⟩ : syracuseStep 2101397 = 98503) (by norm_num)
theorem B3149981 : Blo 1399519 3149981 := bbase (se 3 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 3149981 = 1181243) (by norm_num)
theorem B1773733 : Blo 1399519 1773733 := bbase (se 4 (by rfl) ⟨166287, by rfl⟩ : syracuseStep 1773733 = 332575) (by norm_num)
theorem B2101421 : Blo 1399519 2101421 := bbase (se 3 (by rfl) ⟨394016, by rfl⟩ : syracuseStep 2101421 = 788033) (by norm_num)
theorem B2363573 : Blo 1399519 2363573 := bbase (se 5 (by rfl) ⟨110792, by rfl⟩ : syracuseStep 2363573 = 221585) (by norm_num)
theorem B2101445 : Blo 1399519 2101445 := bbase (se 4 (by rfl) ⟨197010, by rfl⟩ : syracuseStep 2101445 = 394021) (by norm_num)
theorem B10367189 : Blo 1399519 10367189 := bbase (se 7 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 10367189 = 242981) (by norm_num)
theorem B2101469 : Blo 1399519 2101469 := bbase (se 3 (by rfl) ⟨394025, by rfl⟩ : syracuseStep 2101469 = 788051) (by norm_num)
theorem B3150053 : Blo 1399519 3150053 := bbase (se 4 (by rfl) ⟨295317, by rfl⟩ : syracuseStep 3150053 = 590635) (by norm_num)
theorem B2101493 : Blo 1399519 2101493 := bbase (se 5 (by rfl) ⟨98507, by rfl⟩ : syracuseStep 2101493 = 197015) (by norm_num)
theorem B2658557 : Blo 1399519 2658557 := bbase (se 3 (by rfl) ⟨498479, by rfl⟩ : syracuseStep 2658557 = 996959) (by norm_num)
theorem B2101517 : Blo 1399519 2101517 := bbase (se 3 (by rfl) ⟨394034, by rfl⟩ : syracuseStep 2101517 = 788069) (by norm_num)
theorem B2101541 : Blo 1399519 2101541 := bbase (se 4 (by rfl) ⟨197019, by rfl⟩ : syracuseStep 2101541 = 394039) (by norm_num)
theorem B3150125 : Blo 1399519 3150125 := bbase (se 3 (by rfl) ⟨590648, by rfl⟩ : syracuseStep 3150125 = 1181297) (by norm_num)
theorem B2363701 : Blo 1399519 2363701 := bbase (se 5 (by rfl) ⟨110798, by rfl⟩ : syracuseStep 2363701 = 221597) (by norm_num)
theorem B2101565 : Blo 1399519 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B3543365 : Blo 1399519 3543365 := bbase (se 4 (by rfl) ⟨332190, by rfl⟩ : syracuseStep 3543365 = 664381) (by norm_num)
theorem B2101589 : Blo 1399519 2101589 := bbase (se 10 (by rfl) ⟨3078, by rfl⟩ : syracuseStep 2101589 = 6157) (by norm_num)
theorem B2101613 : Blo 1399519 2101613 := bbase (se 3 (by rfl) ⟨394052, by rfl⟩ : syracuseStep 2101613 = 788105) (by norm_num)
theorem B3150197 : Blo 1399519 3150197 := bbase (se 5 (by rfl) ⟨147665, by rfl⟩ : syracuseStep 3150197 = 295331) (by norm_num)
theorem B2101637 : Blo 1399519 2101637 := bbase (se 4 (by rfl) ⟨197028, by rfl⟩ : syracuseStep 2101637 = 394057) (by norm_num)
theorem B2363789 : Blo 1399519 2363789 := bbase (se 3 (by rfl) ⟨443210, by rfl⟩ : syracuseStep 2363789 = 886421) (by norm_num)
theorem B2101661 : Blo 1399519 2101661 := bbase (se 3 (by rfl) ⟨394061, by rfl⟩ : syracuseStep 2101661 = 788123) (by norm_num)
theorem B2101685 : Blo 1399519 2101685 := bbase (se 5 (by rfl) ⟨98516, by rfl⟩ : syracuseStep 2101685 = 197033) (by norm_num)
theorem B1495481 : Blo 1399519 1495481 := bbase (se 2 (by rfl) ⟨560805, by rfl⟩ : syracuseStep 1495481 = 1121611) (by norm_num)
theorem B3150269 : Blo 1399519 3150269 := bbase (se 3 (by rfl) ⟨590675, by rfl⟩ : syracuseStep 3150269 = 1181351) (by norm_num)
theorem B1995205 : Blo 1399519 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B2101709 : Blo 1399519 2101709 := bbase (se 3 (by rfl) ⟨394070, by rfl⟩ : syracuseStep 2101709 = 788141) (by norm_num)
theorem B2101733 : Blo 1399519 2101733 := bbase (se 4 (by rfl) ⟨197037, by rfl⟩ : syracuseStep 2101733 = 394075) (by norm_num)
theorem B1495541 : Blo 1399519 1495541 := bbase (se 5 (by rfl) ⟨70103, by rfl⟩ : syracuseStep 1495541 = 140207) (by norm_num)
theorem B2101757 : Blo 1399519 2101757 := bbase (se 3 (by rfl) ⟨394079, by rfl⟩ : syracuseStep 2101757 = 788159) (by norm_num)
theorem B3150341 : Blo 1399519 3150341 := bbase (se 4 (by rfl) ⟨295344, by rfl⟩ : syracuseStep 3150341 = 590689) (by norm_num)
theorem B2363917 : Blo 1399519 2363917 := bbase (se 3 (by rfl) ⟨443234, by rfl⟩ : syracuseStep 2363917 = 886469) (by norm_num)
theorem B2101781 : Blo 1399519 2101781 := bbase (se 6 (by rfl) ⟨49260, by rfl⟩ : syracuseStep 2101781 = 98521) (by norm_num)
theorem B2658845 : Blo 1399519 2658845 := bbase (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) (by norm_num)
theorem B2101805 : Blo 1399519 2101805 := bbase (se 3 (by rfl) ⟨394088, by rfl⟩ : syracuseStep 2101805 = 788177) (by norm_num)
theorem B6386245 : Blo 1399519 6386245 := bbase (se 4 (by rfl) ⟨598710, by rfl⟩ : syracuseStep 6386245 = 1197421) (by norm_num)
theorem B2101829 : Blo 1399519 2101829 := bbase (se 4 (by rfl) ⟨197046, by rfl⟩ : syracuseStep 2101829 = 394093) (by norm_num)
theorem B3150413 : Blo 1399519 3150413 := bbase (se 3 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 3150413 = 1181405) (by norm_num)
theorem B2101853 : Blo 1399519 2101853 := bbase (se 3 (by rfl) ⟨394097, by rfl⟩ : syracuseStep 2101853 = 788195) (by norm_num)
theorem B2364005 : Blo 1399519 2364005 := bbase (se 4 (by rfl) ⟨221625, by rfl⟩ : syracuseStep 2364005 = 443251) (by norm_num)
theorem B1495669 : Blo 1399519 1495669 := bbase (se 5 (by rfl) ⟨70109, by rfl⟩ : syracuseStep 1495669 = 140219) (by norm_num)
theorem B2101877 : Blo 1399519 2101877 := bbase (se 5 (by rfl) ⟨98525, by rfl⟩ : syracuseStep 2101877 = 197051) (by norm_num)
theorem B2101901 : Blo 1399519 2101901 := bbase (se 3 (by rfl) ⟨394106, by rfl⟩ : syracuseStep 2101901 = 788213) (by norm_num)
theorem B3150485 : Blo 1399519 3150485 := bbase (se 6 (by rfl) ⟨73839, by rfl⟩ : syracuseStep 3150485 = 147679) (by norm_num)
theorem B3543709 : Blo 1399519 3543709 := bbase (se 3 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 3543709 = 1328891) (by norm_num)
theorem B2101925 : Blo 1399519 2101925 := bbase (se 4 (by rfl) ⟨197055, by rfl⟩ : syracuseStep 2101925 = 394111) (by norm_num)
theorem B2658997 : Blo 1399519 2658997 := bbase (se 5 (by rfl) ⟨124640, by rfl⟩ : syracuseStep 2658997 = 249281) (by norm_num)
theorem B2101949 : Blo 1399519 2101949 := bbase (se 3 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 2101949 = 788231) (by norm_num)
theorem B7090901 : Blo 1399519 7090901 := bbase (se 7 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 7090901 = 166193) (by norm_num)
theorem B2101973 : Blo 1399519 2101973 := bbase (se 7 (by rfl) ⟨24632, by rfl⟩ : syracuseStep 2101973 = 49265) (by norm_num)
theorem B3150557 : Blo 1399519 3150557 := bbase (se 3 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 3150557 = 1181459) (by norm_num)
theorem B2364133 : Blo 1399519 2364133 := bbase (se 4 (by rfl) ⟨221637, by rfl⟩ : syracuseStep 2364133 = 443275) (by norm_num)
theorem B2101997 : Blo 1399519 2101997 := bbase (se 3 (by rfl) ⟨394124, by rfl⟩ : syracuseStep 2101997 = 788249) (by norm_num)
theorem B2102021 : Blo 1399519 2102021 := bbase (se 4 (by rfl) ⟨197064, by rfl⟩ : syracuseStep 2102021 = 394129) (by norm_num)
theorem B3543821 : Blo 1399519 3543821 := bbase (se 3 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 3543821 = 1328933) (by norm_num)
theorem B2102045 : Blo 1399519 2102045 := bbase (se 3 (by rfl) ⟨394133, by rfl⟩ : syracuseStep 2102045 = 788267) (by norm_num)
theorem B3150629 : Blo 1399519 3150629 := bbase (se 4 (by rfl) ⟨295371, by rfl⟩ : syracuseStep 3150629 = 590743) (by norm_num)
theorem B2102069 : Blo 1399519 2102069 := bbase (se 5 (by rfl) ⟨98534, by rfl⟩ : syracuseStep 2102069 = 197069) (by norm_num)
theorem B2364221 : Blo 1399519 2364221 := bbase (se 3 (by rfl) ⟨443291, by rfl⟩ : syracuseStep 2364221 = 886583) (by norm_num)
theorem B2102093 : Blo 1399519 2102093 := bbase (se 3 (by rfl) ⟨394142, by rfl⟩ : syracuseStep 2102093 = 788285) (by norm_num)
theorem B4723541 : Blo 1399519 4723541 := bbase (se 9 (by rfl) ⟨13838, by rfl⟩ : syracuseStep 4723541 = 27677) (by norm_num)
theorem B3593045 : Blo 1399519 3593045 := bbase (se 9 (by rfl) ⟨10526, by rfl⟩ : syracuseStep 3593045 = 21053) (by norm_num)
theorem B2102117 : Blo 1399519 2102117 := bbase (se 4 (by rfl) ⟨197073, by rfl⟩ : syracuseStep 2102117 = 394147) (by norm_num)
theorem B3150701 : Blo 1399519 3150701 := bbase (se 3 (by rfl) ⟨590756, by rfl⟩ : syracuseStep 3150701 = 1181513) (by norm_num)
theorem B3363709 : Blo 1399519 3363709 := bbase (se 3 (by rfl) ⟨630695, by rfl⟩ : syracuseStep 3363709 = 1261391) (by norm_num)
theorem B2102141 : Blo 1399519 2102141 := bbase (se 3 (by rfl) ⟨394151, by rfl⟩ : syracuseStep 2102141 = 788303) (by norm_num)
theorem B3986309 : Blo 1399519 3986309 := bbase (se 4 (by rfl) ⟨373716, by rfl⟩ : syracuseStep 3986309 = 747433) (by norm_num)
theorem B2102165 : Blo 1399519 2102165 := bbase (se 6 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 2102165 = 98539) (by norm_num)
theorem B2102189 : Blo 1399519 2102189 := bbase (se 3 (by rfl) ⟨394160, by rfl⟩ : syracuseStep 2102189 = 788321) (by norm_num)
theorem B3150773 : Blo 1399519 3150773 := bbase (se 5 (by rfl) ⟨147692, by rfl⟩ : syracuseStep 3150773 = 295385) (by norm_num)
theorem B2364349 : Blo 1399519 2364349 := bbase (se 3 (by rfl) ⟨443315, by rfl⟩ : syracuseStep 2364349 = 886631) (by norm_num)
theorem B2102213 : Blo 1399519 2102213 := bbase (se 4 (by rfl) ⟨197082, by rfl⟩ : syracuseStep 2102213 = 394165) (by norm_num)
theorem B3544013 : Blo 1399519 3544013 := bbase (se 3 (by rfl) ⟨664502, by rfl⟩ : syracuseStep 3544013 = 1329005) (by norm_num)
theorem B2102237 : Blo 1399519 2102237 := bbase (se 3 (by rfl) ⟨394169, by rfl⟩ : syracuseStep 2102237 = 788339) (by norm_num)
theorem B2659301 : Blo 1399519 2659301 := bbase (se 4 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 2659301 = 498619) (by norm_num)
theorem B2102261 : Blo 1399519 2102261 := bbase (se 5 (by rfl) ⟨98543, by rfl⟩ : syracuseStep 2102261 = 197087) (by norm_num)
theorem B3150845 : Blo 1399519 3150845 := bbase (se 3 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 3150845 = 1181567) (by norm_num)
theorem B2364437 : Blo 1399519 2364437 := bbase (se 6 (by rfl) ⟨55416, by rfl⟩ : syracuseStep 2364437 = 110833) (by norm_num)
theorem B1496113 : Blo 1399519 1496113 := bbase (se 2 (by rfl) ⟨561042, by rfl⟩ : syracuseStep 1496113 = 1122085) (by norm_num)
theorem B3150917 : Blo 1399519 3150917 := bbase (se 4 (by rfl) ⟨295398, by rfl⟩ : syracuseStep 3150917 = 590797) (by norm_num)
theorem B3150989 : Blo 1399519 3150989 := bbase (se 3 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 3150989 = 1181621) (by norm_num)
theorem B2462861 : Blo 1399519 2462861 := bbase (se 3 (by rfl) ⟨461786, by rfl⟩ : syracuseStep 2462861 = 923573) (by norm_num)
theorem B2364565 : Blo 1399519 2364565 := bbase (se 6 (by rfl) ⟨55419, by rfl⟩ : syracuseStep 2364565 = 110839) (by norm_num)
theorem B2159765 : Blo 1399519 2159765 := bbase (se 6 (by rfl) ⟨50619, by rfl⟩ : syracuseStep 2159765 = 101239) (by norm_num)
theorem B1496233 : Blo 1399519 1496233 := bbase (se 2 (by rfl) ⟨561087, by rfl⟩ : syracuseStep 1496233 = 1122175) (by norm_num)
theorem B3151061 : Blo 1399519 3151061 := bbase (se 7 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 3151061 = 73853) (by norm_num)
theorem B2364653 : Blo 1399519 2364653 := bbase (se 3 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 2364653 = 886745) (by norm_num)
theorem B4723973 : Blo 1399519 4723973 := bbase (se 4 (by rfl) ⟨442872, by rfl⟩ : syracuseStep 4723973 = 885745) (by norm_num)
theorem B3151133 : Blo 1399519 3151133 := bbase (se 3 (by rfl) ⟨590837, by rfl⟩ : syracuseStep 3151133 = 1181675) (by norm_num)
theorem B3544357 : Blo 1399519 3544357 := bbase (se 4 (by rfl) ⟨332283, by rfl⟩ : syracuseStep 3544357 = 664567) (by norm_num)
theorem B3151205 : Blo 1399519 3151205 := bbase (se 4 (by rfl) ⟨295425, by rfl⟩ : syracuseStep 3151205 = 590851) (by norm_num)
theorem B2364781 : Blo 1399519 2364781 := bbase (se 3 (by rfl) ⟨443396, by rfl⟩ : syracuseStep 2364781 = 886793) (by norm_num)
theorem B3544469 : Blo 1399519 3544469 := bbase (se 6 (by rfl) ⟨83073, by rfl⟩ : syracuseStep 3544469 = 166147) (by norm_num)
theorem B1496485 : Blo 1399519 1496485 := bbase (se 4 (by rfl) ⟨140295, by rfl⟩ : syracuseStep 1496485 = 280591) (by norm_num)
theorem B1496489 : Blo 1399519 1496489 := bbase (se 2 (by rfl) ⟨561183, by rfl⟩ : syracuseStep 1496489 = 1122367) (by norm_num)
theorem B3151277 : Blo 1399519 3151277 := bbase (se 3 (by rfl) ⟨590864, by rfl⟩ : syracuseStep 3151277 = 1181729) (by norm_num)
theorem B2364869 : Blo 1399519 2364869 := bbase (se 4 (by rfl) ⟨221706, by rfl⟩ : syracuseStep 2364869 = 443413) (by norm_num)
theorem B3364325 : Blo 1399519 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B3151349 : Blo 1399519 3151349 := bbase (se 5 (by rfl) ⟨147719, by rfl⟩ : syracuseStep 3151349 = 295439) (by norm_num)
theorem B3151421 : Blo 1399519 3151421 := bbase (se 3 (by rfl) ⟨590891, by rfl⟩ : syracuseStep 3151421 = 1181783) (by norm_num)
theorem B2364997 : Blo 1399519 2364997 := bbase (se 4 (by rfl) ⟨221718, by rfl⟩ : syracuseStep 2364997 = 443437) (by norm_num)
theorem B3544661 : Blo 1399519 3544661 := bbase (se 8 (by rfl) ⟨20769, by rfl⟩ : syracuseStep 3544661 = 41539) (by norm_num)
theorem B3593845 : Blo 1399519 3593845 := bbase (se 5 (by rfl) ⟨168461, by rfl⟩ : syracuseStep 3593845 = 336923) (by norm_num)
theorem B3151493 : Blo 1399519 3151493 := bbase (se 4 (by rfl) ⟨295452, by rfl⟩ : syracuseStep 3151493 = 590905) (by norm_num)
theorem B2840213 : Blo 1399519 2840213 := bbase (se 6 (by rfl) ⟨66567, by rfl⟩ : syracuseStep 2840213 = 133135) (by norm_num)
theorem B3364525 : Blo 1399519 3364525 := bbase (se 3 (by rfl) ⟨630848, by rfl⟩ : syracuseStep 3364525 = 1261697) (by norm_num)
theorem B4724405 : Blo 1399519 4724405 := bbase (se 5 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 4724405 = 442913) (by norm_num)
theorem B3593909 : Blo 1399519 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B4486853 : Blo 1399519 4486853 := bbase (se 4 (by rfl) ⟨420642, by rfl⟩ : syracuseStep 4486853 = 841285) (by norm_num)
theorem B3151565 : Blo 1399519 3151565 := bbase (se 3 (by rfl) ⟨590918, by rfl⟩ : syracuseStep 3151565 = 1181837) (by norm_num)
theorem B2660053 : Blo 1399519 2660053 := bbase (se 7 (by rfl) ⟨31172, by rfl⟩ : syracuseStep 2660053 = 62345) (by norm_num)
theorem B2242325 : Blo 1399519 2242325 := bbase (se 6 (by rfl) ⟨52554, by rfl⟩ : syracuseStep 2242325 = 105109) (by norm_num)
theorem B3151637 : Blo 1399519 3151637 := bbase (se 6 (by rfl) ⟨73866, by rfl⟩ : syracuseStep 3151637 = 147733) (by norm_num)
theorem B3192605 : Blo 1399519 3192605 := bbase (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) (by norm_num)
theorem B3151709 : Blo 1399519 3151709 := bbase (se 3 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 3151709 = 1181891) (by norm_num)
theorem B2660197 : Blo 1399519 2660197 := bbase (se 4 (by rfl) ⟨249393, by rfl⟩ : syracuseStep 2660197 = 498787) (by norm_num)
theorem B3151781 : Blo 1399519 3151781 := bbase (se 4 (by rfl) ⟨295479, by rfl⟩ : syracuseStep 3151781 = 590959) (by norm_num)
theorem B3545005 : Blo 1399519 3545005 := bbase (se 3 (by rfl) ⟨664688, by rfl⟩ : syracuseStep 3545005 = 1329377) (by norm_num)
theorem B5314517 : Blo 1399519 5314517 := bbase (se 7 (by rfl) ⟨62279, by rfl⟩ : syracuseStep 5314517 = 124559) (by norm_num)
theorem B7092197 : Blo 1399519 7092197 := bbase (se 4 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 7092197 = 1329787) (by norm_num)
theorem B3151853 : Blo 1399519 3151853 := bbase (se 3 (by rfl) ⟨590972, by rfl⟩ : syracuseStep 3151853 = 1181945) (by norm_num)
theorem B2660357 : Blo 1399519 2660357 := bbase (se 4 (by rfl) ⟨249408, by rfl⟩ : syracuseStep 2660357 = 498817) (by norm_num)
theorem B3545117 : Blo 1399519 3545117 := bbase (se 3 (by rfl) ⟨664709, by rfl⟩ : syracuseStep 3545117 = 1329419) (by norm_num)
theorem B1620005 : Blo 1399519 1620005 := bbase (se 4 (by rfl) ⟨151875, by rfl⟩ : syracuseStep 1620005 = 303751) (by norm_num)
theorem B3151925 : Blo 1399519 3151925 := bbase (se 5 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 3151925 = 295493) (by norm_num)
theorem B4790341 : Blo 1399519 4790341 := bbase (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) (by norm_num)
theorem B4724837 : Blo 1399519 4724837 := bbase (se 4 (by rfl) ⟨442953, by rfl⟩ : syracuseStep 4724837 = 885907) (by norm_num)
theorem B3151997 : Blo 1399519 3151997 := bbase (se 3 (by rfl) ⟨590999, by rfl⟩ : syracuseStep 3151997 = 1181999) (by norm_num)
theorem B2128013 : Blo 1399519 2128013 := bbase (se 3 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 2128013 = 798005) (by norm_num)
theorem B2660501 : Blo 1399519 2660501 := bbase (se 6 (by rfl) ⟨62355, by rfl⟩ : syracuseStep 2660501 = 124711) (by norm_num)
theorem B6387893 : Blo 1399519 6387893 := bbase (se 5 (by rfl) ⟨299432, by rfl⟩ : syracuseStep 6387893 = 598865) (by norm_num)
theorem B3152069 : Blo 1399519 3152069 := bbase (se 4 (by rfl) ⟨295506, by rfl⟩ : syracuseStep 3152069 = 591013) (by norm_num)
theorem B4856021 : Blo 1399519 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B3545309 : Blo 1399519 3545309 := bbase (se 3 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 3545309 = 1329491) (by norm_num)
theorem B5314805 : Blo 1399519 5314805 := bbase (se 5 (by rfl) ⟨249131, by rfl⟩ : syracuseStep 5314805 = 498263) (by norm_num)
theorem B3152141 : Blo 1399519 3152141 := bbase (se 3 (by rfl) ⟨591026, by rfl⟩ : syracuseStep 3152141 = 1182053) (by norm_num)
theorem B2242837 : Blo 1399519 2242837 := bbase (se 6 (by rfl) ⟨52566, by rfl⟩ : syracuseStep 2242837 = 105133) (by norm_num)
theorem B6822181 : Blo 1399519 6822181 := bbase (se 4 (by rfl) ⟨639579, by rfl⟩ : syracuseStep 6822181 = 1279159) (by norm_num)
theorem B3152213 : Blo 1399519 3152213 := bbase (se 10 (by rfl) ⟨4617, by rfl⟩ : syracuseStep 3152213 = 9235) (by norm_num)
theorem B3152285 : Blo 1399519 3152285 := bbase (se 3 (by rfl) ⟨591053, by rfl⟩ : syracuseStep 3152285 = 1182107) (by norm_num)
theorem B3987893 : Blo 1399519 3987893 := bbase (se 5 (by rfl) ⟨186932, by rfl⟩ : syracuseStep 3987893 = 373865) (by norm_num)
theorem B3365333 : Blo 1399519 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B3152357 : Blo 1399519 3152357 := bbase (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) (by norm_num)
theorem B4725269 : Blo 1399519 4725269 := bbase (se 6 (by rfl) ⟨110748, by rfl⟩ : syracuseStep 4725269 = 221497) (by norm_num)
theorem B3152429 : Blo 1399519 3152429 := bbase (se 3 (by rfl) ⟨591080, by rfl⟩ : syracuseStep 3152429 = 1182161) (by norm_num)
theorem B3545653 : Blo 1399519 3545653 := bbase (se 5 (by rfl) ⟨166202, by rfl⟩ : syracuseStep 3545653 = 332405) (by norm_num)
theorem B3152501 : Blo 1399519 3152501 := bbase (se 5 (by rfl) ⟨147773, by rfl⟩ : syracuseStep 3152501 = 295547) (by norm_num)
theorem B3545765 : Blo 1399519 3545765 := bbase (se 4 (by rfl) ⟨332415, by rfl⟩ : syracuseStep 3545765 = 664831) (by norm_num)
theorem B3152573 : Blo 1399519 3152573 := bbase (se 3 (by rfl) ⟨591107, by rfl⟩ : syracuseStep 3152573 = 1182215) (by norm_num)
theorem B3152645 : Blo 1399519 3152645 := bbase (se 4 (by rfl) ⟨295560, by rfl⟩ : syracuseStep 3152645 = 591121) (by norm_num)
theorem B4487957 : Blo 1399519 4487957 := bbase (se 6 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 4487957 = 210373) (by norm_num)
theorem B1596197 : Blo 1399519 1596197 := bbase (se 4 (by rfl) ⟨149643, by rfl⟩ : syracuseStep 1596197 = 299287) (by norm_num)
theorem B3152717 : Blo 1399519 3152717 := bbase (se 3 (by rfl) ⟨591134, by rfl⟩ : syracuseStep 3152717 = 1182269) (by norm_num)
theorem B3545957 : Blo 1399519 3545957 := bbase (se 4 (by rfl) ⟨332433, by rfl⟩ : syracuseStep 3545957 = 664867) (by norm_num)
theorem B3152789 : Blo 1399519 3152789 := bbase (se 6 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 3152789 = 147787) (by norm_num)
theorem B4725701 : Blo 1399519 4725701 := bbase (se 4 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 4725701 = 886069) (by norm_num)
theorem B3152861 : Blo 1399519 3152861 := bbase (se 3 (by rfl) ⟨591161, by rfl⟩ : syracuseStep 3152861 = 1182323) (by norm_num)
theorem B3152933 : Blo 1399519 3152933 := bbase (se 4 (by rfl) ⟨295587, by rfl⟩ : syracuseStep 3152933 = 591175) (by norm_num)
theorem B3988565 : Blo 1399519 3988565 := bbase (se 8 (by rfl) ⟨23370, by rfl⟩ : syracuseStep 3988565 = 46741) (by norm_num)
theorem B3153005 : Blo 1399519 3153005 := bbase (se 3 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 3153005 = 1182377) (by norm_num)
theorem B2694293 : Blo 1399519 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B2522269 : Blo 1399519 2522269 := bbase (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) (by norm_num)
theorem B2989237 : Blo 1399519 2989237 := bbase (se 5 (by rfl) ⟨140120, by rfl⟩ : syracuseStep 2989237 = 280241) (by norm_num)
theorem B3153077 : Blo 1399519 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B3546301 : Blo 1399519 3546301 := bbase (se 3 (by rfl) ⟨664931, by rfl⟩ : syracuseStep 3546301 = 1329863) (by norm_num)
theorem B1891525 : Blo 1399519 1891525 := bbase (se 4 (by rfl) ⟨177330, by rfl⟩ : syracuseStep 1891525 = 354661) (by norm_num)
theorem B3366101 : Blo 1399519 3366101 := bbase (se 7 (by rfl) ⟨39446, by rfl⟩ : syracuseStep 3366101 = 78893) (by norm_num)
theorem B7093493 : Blo 1399519 7093493 := bbase (se 5 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 7093493 = 665015) (by norm_num)
theorem B2243837 : Blo 1399519 2243837 := bbase (se 3 (by rfl) ⟨420719, by rfl⟩ : syracuseStep 2243837 = 841439) (by norm_num)
theorem B3153149 : Blo 1399519 3153149 := bbase (se 3 (by rfl) ⟨591215, by rfl⟩ : syracuseStep 3153149 = 1182431) (by norm_num)
theorem B3546413 : Blo 1399519 3546413 := bbase (se 3 (by rfl) ⟨664952, by rfl⟩ : syracuseStep 3546413 = 1329905) (by norm_num)
theorem B4259141 : Blo 1399519 4259141 := bbase (se 4 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 4259141 = 798589) (by norm_num)
theorem B3153221 : Blo 1399519 3153221 := bbase (se 4 (by rfl) ⟨295614, by rfl⟩ : syracuseStep 3153221 = 591229) (by norm_num)
theorem B4726133 : Blo 1399519 4726133 := bbase (se 5 (by rfl) ⟨221537, by rfl⟩ : syracuseStep 4726133 = 443075) (by norm_num)
theorem B2243965 : Blo 1399519 2243965 := bbase (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) (by norm_num)
theorem B3153293 : Blo 1399519 3153293 := bbase (se 3 (by rfl) ⟨591242, by rfl⟩ : syracuseStep 3153293 = 1182485) (by norm_num)
theorem B5315989 : Blo 1399519 5315989 := bbase (se 6 (by rfl) ⟨124593, by rfl⟩ : syracuseStep 5315989 = 249187) (by norm_num)
theorem B2244029 : Blo 1399519 2244029 := bbase (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) (by norm_num)
theorem B3153365 : Blo 1399519 3153365 := bbase (se 7 (by rfl) ⟨36953, by rfl⟩ : syracuseStep 3153365 = 73907) (by norm_num)
theorem B3546605 : Blo 1399519 3546605 := bbase (se 3 (by rfl) ⟨664988, by rfl⟩ : syracuseStep 3546605 = 1329977) (by norm_num)
theorem B5979653 : Blo 1399519 5979653 := bbase (se 4 (by rfl) ⟨560592, by rfl⟩ : syracuseStep 5979653 = 1121185) (by norm_num)
theorem B3988997 : Blo 1399519 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B3595877 : Blo 1399519 3595877 := bbase (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) (by norm_num)
theorem B7085717 : Blo 1399519 7085717 := bbase (se 6 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 7085717 = 332143) (by norm_num)
theorem B5316293 : Blo 1399519 5316293 := bbase (se 4 (by rfl) ⟨498402, by rfl⟩ : syracuseStep 5316293 = 996805) (by norm_num)
theorem B24592085 : Blo 1399519 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B2129669 : Blo 1399519 2129669 := bbase (se 4 (by rfl) ⟨199656, by rfl⟩ : syracuseStep 2129669 = 399313) (by norm_num)
theorem B7282469 : Blo 1399519 7282469 := bbase (se 4 (by rfl) ⟨682731, by rfl⟩ : syracuseStep 7282469 = 1365463) (by norm_num)
theorem B4726565 : Blo 1399519 4726565 := bbase (se 4 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 4726565 = 886231) (by norm_num)
theorem B3546949 : Blo 1399519 3546949 := bbase (se 4 (by rfl) ⟨332526, by rfl⟩ : syracuseStep 3546949 = 665053) (by norm_num)
theorem B3547061 : Blo 1399519 3547061 := bbase (se 5 (by rfl) ⟨166268, by rfl⟩ : syracuseStep 3547061 = 332537) (by norm_num)
theorem B2523077 : Blo 1399519 2523077 := bbase (se 4 (by rfl) ⟨236538, by rfl⟩ : syracuseStep 2523077 = 473077) (by norm_num)
theorem B1400835 : Blo 1399519 1400835 := bstep (se 1 (by rfl) ⟨1050626, by rfl⟩ : syracuseStep 1400835 = 2101253) B2101253
theorem B1400851 : Blo 1399519 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B1400867 : Blo 1399519 1400867 := bstep (se 1 (by rfl) ⟨1050650, by rfl⟩ : syracuseStep 1400867 = 2101301) B2101301
theorem B3366947 : Blo 1399519 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B1400883 : Blo 1399519 1400883 := bstep (se 1 (by rfl) ⟨1050662, by rfl⟩ : syracuseStep 1400883 = 2101325) B2101325
theorem B1400899 : Blo 1399519 1400899 := bstep (se 1 (by rfl) ⟨1050674, by rfl⟩ : syracuseStep 1400899 = 2101349) B2101349
theorem B1400915 : Blo 1399519 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B1400931 : Blo 1399519 1400931 := bstep (se 1 (by rfl) ⟨1050698, by rfl⟩ : syracuseStep 1400931 = 2101397) B2101397
theorem B1400947 : Blo 1399519 1400947 := bstep (se 1 (by rfl) ⟨1050710, by rfl⟩ : syracuseStep 1400947 = 2101421) B2101421
theorem B1400963 : Blo 1399519 1400963 := bstep (se 1 (by rfl) ⟨1050722, by rfl⟩ : syracuseStep 1400963 = 2101445) B2101445
theorem B5316749 : Blo 1399519 5316749 := bstep (se 3 (by rfl) ⟨996890, by rfl⟩ : syracuseStep 5316749 = 1993781) B1993781
theorem B1400979 : Blo 1399519 1400979 := bstep (se 1 (by rfl) ⟨1050734, by rfl⟩ : syracuseStep 1400979 = 2101469) B2101469
theorem B1400995 : Blo 1399519 1400995 := bstep (se 1 (by rfl) ⟨1050746, by rfl⟩ : syracuseStep 1400995 = 2101493) B2101493
theorem B5980337 : Blo 1399519 5980337 := bstep (se 2 (by rfl) ⟨2242626, by rfl⟩ : syracuseStep 5980337 = 4485253) B4485253
theorem B3989681 : Blo 1399519 3989681 := bstep (se 2 (by rfl) ⟨1496130, by rfl⟩ : syracuseStep 3989681 = 2992261) B2992261
theorem B1401011 : Blo 1399519 1401011 := bstep (se 1 (by rfl) ⟨1050758, by rfl⟩ : syracuseStep 1401011 = 2101517) B2101517
theorem B1401027 : Blo 1399519 1401027 := bstep (se 1 (by rfl) ⟨1050770, by rfl⟩ : syracuseStep 1401027 = 2101541) B2101541
theorem B1401043 : Blo 1399519 1401043 := bstep (se 1 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 1401043 = 2101565) B2101565
theorem B5046499 : Blo 1399519 5046499 := bstep (se 1 (by rfl) ⟨3784874, by rfl⟩ : syracuseStep 5046499 = 7569749) B7569749
theorem B1401059 : Blo 1399519 1401059 := bstep (se 1 (by rfl) ⟨1050794, by rfl⟩ : syracuseStep 1401059 = 2101589) B2101589
theorem B1401075 : Blo 1399519 1401075 := bstep (se 1 (by rfl) ⟨1050806, by rfl⟩ : syracuseStep 1401075 = 2101613) B2101613
theorem B1401091 : Blo 1399519 1401091 := bstep (se 1 (by rfl) ⟨1050818, by rfl⟩ : syracuseStep 1401091 = 2101637) B2101637
theorem B7979269 : Blo 1399519 7979269 := bstep (se 4 (by rfl) ⟨748056, by rfl⟩ : syracuseStep 7979269 = 1496113) B1496113
theorem B1401107 : Blo 1399519 1401107 := bstep (se 1 (by rfl) ⟨1050830, by rfl⟩ : syracuseStep 1401107 = 2101661) B2101661
theorem B1401123 : Blo 1399519 1401123 := bstep (se 1 (by rfl) ⟨1050842, by rfl⟩ : syracuseStep 1401123 = 2101685) B2101685
theorem B1401139 : Blo 1399519 1401139 := bstep (se 1 (by rfl) ⟨1050854, by rfl⟩ : syracuseStep 1401139 = 2101709) B2101709
theorem B1401155 : Blo 1399519 1401155 := bstep (se 1 (by rfl) ⟨1050866, by rfl⟩ : syracuseStep 1401155 = 2101733) B2101733
theorem B1401171 : Blo 1399519 1401171 := bstep (se 1 (by rfl) ⟨1050878, by rfl⟩ : syracuseStep 1401171 = 2101757) B2101757
theorem B1401187 : Blo 1399519 1401187 := bstep (se 1 (by rfl) ⟨1050890, by rfl⟩ : syracuseStep 1401187 = 2101781) B2101781
theorem B7094627 : Blo 1399519 7094627 := bstep (se 1 (by rfl) ⟨5320970, by rfl⟩ : syracuseStep 7094627 = 10641941) B10641941
theorem B2990449 : Blo 1399519 2990449 := bstep (se 2 (by rfl) ⟨1121418, by rfl⟩ : syracuseStep 2990449 = 2242837) B2242837
theorem B1401203 : Blo 1399519 1401203 := bstep (se 1 (by rfl) ⟨1050902, by rfl⟩ : syracuseStep 1401203 = 2101805) B2101805
theorem B1401219 : Blo 1399519 1401219 := bstep (se 1 (by rfl) ⟨1050914, by rfl⟩ : syracuseStep 1401219 = 2101829) B2101829
theorem B1401235 : Blo 1399519 1401235 := bstep (se 1 (by rfl) ⟨1050926, by rfl⟩ : syracuseStep 1401235 = 2101853) B2101853
theorem B1401251 : Blo 1399519 1401251 := bstep (se 1 (by rfl) ⟨1050938, by rfl⟩ : syracuseStep 1401251 = 2101877) B2101877
theorem B4727213 : Blo 1399519 4727213 := bstep (se 3 (by rfl) ⟨886352, by rfl⟩ : syracuseStep 4727213 = 1772705) B1772705
theorem B1401267 : Blo 1399519 1401267 := bstep (se 1 (by rfl) ⟨1050950, by rfl⟩ : syracuseStep 1401267 = 2101901) B2101901
theorem B1401283 : Blo 1399519 1401283 := bstep (se 1 (by rfl) ⟨1050962, by rfl⟩ : syracuseStep 1401283 = 2101925) B2101925
theorem B1401299 : Blo 1399519 1401299 := bstep (se 1 (by rfl) ⟨1050974, by rfl⟩ : syracuseStep 1401299 = 2101949) B2101949
theorem B4727267 : Blo 1399519 4727267 := bstep (se 1 (by rfl) ⟨3545450, by rfl⟩ : syracuseStep 4727267 = 7090901) B7090901
theorem B1401315 : Blo 1399519 1401315 := bstep (se 1 (by rfl) ⟨1050986, by rfl⟩ : syracuseStep 1401315 = 2101973) B2101973
theorem B1401331 : Blo 1399519 1401331 := bstep (se 1 (by rfl) ⟨1050998, by rfl⟩ : syracuseStep 1401331 = 2101997) B2101997
theorem B2556419 : Blo 1399519 2556419 := bstep (se 1 (by rfl) ⟨1917314, by rfl⟩ : syracuseStep 2556419 = 3834629) B3834629
theorem B1401347 : Blo 1399519 1401347 := bstep (se 1 (by rfl) ⟨1051010, by rfl⟩ : syracuseStep 1401347 = 2102021) B2102021
theorem B1401363 : Blo 1399519 1401363 := bstep (se 1 (by rfl) ⟨1051022, by rfl⟩ : syracuseStep 1401363 = 2102045) B2102045
theorem B1401379 : Blo 1399519 1401379 := bstep (se 1 (by rfl) ⟨1051034, by rfl⟩ : syracuseStep 1401379 = 2102069) B2102069
theorem B1401395 : Blo 1399519 1401395 := bstep (se 1 (by rfl) ⟨1051046, by rfl⟩ : syracuseStep 1401395 = 2102093) B2102093
theorem B1401411 : Blo 1399519 1401411 := bstep (se 1 (by rfl) ⟨1051058, by rfl⟩ : syracuseStep 1401411 = 2102117) B2102117
theorem B1401427 : Blo 1399519 1401427 := bstep (se 1 (by rfl) ⟨1051070, by rfl⟩ : syracuseStep 1401427 = 2102141) B2102141
theorem B1401443 : Blo 1399519 1401443 := bstep (se 1 (by rfl) ⟨1051082, by rfl⟩ : syracuseStep 1401443 = 2102165) B2102165
theorem B11960945 : Blo 1399519 11960945 := bstep (se 2 (by rfl) ⟨4485354, by rfl⟩ : syracuseStep 11960945 = 8970709) B8970709
theorem B2130545 : Blo 1399519 2130545 := bstep (se 2 (by rfl) ⟨798954, by rfl⟩ : syracuseStep 2130545 = 1597909) B1597909
theorem B1401459 : Blo 1399519 1401459 := bstep (se 1 (by rfl) ⟨1051094, by rfl⟩ : syracuseStep 1401459 = 2102189) B2102189
theorem B1401475 : Blo 1399519 1401475 := bstep (se 1 (by rfl) ⟨1051106, by rfl⟩ : syracuseStep 1401475 = 2102213) B2102213
theorem B1401491 : Blo 1399519 1401491 := bstep (se 1 (by rfl) ⟨1051118, by rfl⟩ : syracuseStep 1401491 = 2102237) B2102237
theorem B1401507 : Blo 1399519 1401507 := bstep (se 1 (by rfl) ⟨1051130, by rfl⟩ : syracuseStep 1401507 = 2102261) B2102261
theorem B7570097 : Blo 1399519 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B5046961 : Blo 1399519 5046961 := bstep (se 2 (by rfl) ⟨1892610, by rfl⟩ : syracuseStep 5046961 = 3785221) B3785221
theorem B4727537 : Blo 1399519 4727537 := bstep (se 2 (by rfl) ⟨1772826, by rfl⟩ : syracuseStep 4727537 = 3545653) B3545653
theorem B13452101 : Blo 1399519 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B8520689 : Blo 1399519 8520689 := bstep (se 2 (by rfl) ⟨3195258, by rfl⟩ : syracuseStep 8520689 = 6390517) B6390517
theorem B1893475 : Blo 1399519 1893475 := bstep (se 1 (by rfl) ⟨1420106, by rfl⟩ : syracuseStep 1893475 = 2840213) B2840213
theorem B3990637 : Blo 1399519 3990637 := bstep (se 3 (by rfl) ⟨748244, by rfl⟩ : syracuseStep 3990637 = 1496489) B1496489
theorem B5047409 : Blo 1399519 5047409 := bstep (se 2 (by rfl) ⟨1892778, by rfl⟩ : syracuseStep 5047409 = 3785557) B3785557
theorem B8086661 : Blo 1399519 8086661 := bstep (se 4 (by rfl) ⟨758124, by rfl⟩ : syracuseStep 8086661 = 1516249) B1516249
theorem B15959267 : Blo 1399519 15959267 := bstep (se 1 (by rfl) ⟨11969450, by rfl⟩ : syracuseStep 15959267 = 23938901) B23938901
theorem B5047537 : Blo 1399519 5047537 := bstep (se 2 (by rfl) ⟨1892826, by rfl⟩ : syracuseStep 5047537 = 3785653) B3785653
theorem B4728077 : Blo 1399519 4728077 := bstep (se 3 (by rfl) ⟨886514, by rfl⟩ : syracuseStep 4728077 = 1773029) B1773029
theorem B4728131 : Blo 1399519 4728131 := bstep (se 1 (by rfl) ⟨3546098, by rfl⟩ : syracuseStep 4728131 = 7092197) B7092197
theorem B3990865 : Blo 1399519 3990865 := bstep (se 2 (by rfl) ⟨1496574, by rfl⟩ : syracuseStep 3990865 = 2993149) B2993149
theorem B5047757 : Blo 1399519 5047757 := bstep (se 3 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 5047757 = 1892909) B1892909
theorem B3237347 : Blo 1399519 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B3991025 : Blo 1399519 3991025 := bstep (se 2 (by rfl) ⟨1496634, by rfl⟩ : syracuseStep 3991025 = 2993269) B2993269
theorem B4728401 : Blo 1399519 4728401 := bstep (se 2 (by rfl) ⟨1773150, by rfl⟩ : syracuseStep 4728401 = 3546301) B3546301
theorem B1574563 : Blo 1399519 1574563 := bstep (se 1 (by rfl) ⟨1180922, by rfl⟩ : syracuseStep 1574563 = 2361845) B2361845
theorem B15140533 : Blo 1399519 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B1574707 : Blo 1399519 1574707 := bstep (se 1 (by rfl) ⟨1181030, by rfl⟩ : syracuseStep 1574707 = 2362061) B2362061
theorem B16181045 : Blo 1399519 16181045 := bstep (se 5 (by rfl) ⟨758486, by rfl⟩ : syracuseStep 16181045 = 1516973) B1516973
theorem B2991953 : Blo 1399519 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B2991971 : Blo 1399519 2991971 := bstep (se 1 (by rfl) ⟨2243978, by rfl⟩ : syracuseStep 2991971 = 4487957) B4487957
theorem B3786605 : Blo 1399519 3786605 := bstep (se 3 (by rfl) ⟨709988, by rfl⟩ : syracuseStep 3786605 = 1419977) B1419977
theorem B7087985 : Blo 1399519 7087985 := bstep (se 2 (by rfl) ⟨2657994, by rfl⟩ : syracuseStep 7087985 = 5315989) B5315989
theorem B1574851 : Blo 1399519 1574851 := bstep (se 1 (by rfl) ⟨1181138, by rfl⟩ : syracuseStep 1574851 = 2362277) B2362277
theorem B12945349 : Blo 1399519 12945349 := bstep (se 4 (by rfl) ⟨1213626, by rfl⟩ : syracuseStep 12945349 = 2427253) B2427253
theorem B6391793 : Blo 1399519 6391793 := bstep (se 2 (by rfl) ⟨2396922, by rfl⟩ : syracuseStep 6391793 = 4793845) B4793845
theorem B1771571 : Blo 1399519 1771571 := bstep (se 1 (by rfl) ⟨1328678, by rfl⟩ : syracuseStep 1771571 = 2657357) B2657357
theorem B1574995 : Blo 1399519 1574995 := bstep (se 1 (by rfl) ⟨1181246, by rfl⟩ : syracuseStep 1574995 = 2362493) B2362493
theorem B2099297 : Blo 1399519 2099297 := bstep (se 2 (by rfl) ⟨787236, by rfl⟩ : syracuseStep 2099297 = 1574473) B1574473
theorem B1796195 : Blo 1399519 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B4728941 : Blo 1399519 4728941 := bstep (se 3 (by rfl) ⟨886676, by rfl⟩ : syracuseStep 4728941 = 1773353) B1773353
theorem B2099315 : Blo 1399519 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B2099345 : Blo 1399519 2099345 := bstep (se 2 (by rfl) ⟨787254, by rfl⟩ : syracuseStep 2099345 = 1574509) B1574509
theorem B2099363 : Blo 1399519 2099363 := bstep (se 1 (by rfl) ⟨1574522, by rfl⟩ : syracuseStep 2099363 = 3149045) B3149045
theorem B4728995 : Blo 1399519 4728995 := bstep (se 1 (by rfl) ⟨3546746, by rfl⟩ : syracuseStep 4728995 = 7093493) B7093493
theorem B1992881 : Blo 1399519 1992881 := bstep (se 2 (by rfl) ⟨747330, by rfl⟩ : syracuseStep 1992881 = 1494661) B1494661
theorem B2099393 : Blo 1399519 2099393 := bstep (se 2 (by rfl) ⟨787272, by rfl⟩ : syracuseStep 2099393 = 1574545) B1574545
theorem B7981253 : Blo 1399519 7981253 := bstep (se 4 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 7981253 = 1496485) B1496485
theorem B2099411 : Blo 1399519 2099411 := bstep (se 1 (by rfl) ⟨1574558, by rfl⟩ : syracuseStep 2099411 = 3149117) B3149117
theorem B1575139 : Blo 1399519 1575139 := bstep (se 1 (by rfl) ⟨1181354, by rfl⟩ : syracuseStep 1575139 = 2362709) B2362709
theorem B2099441 : Blo 1399519 2099441 := bstep (se 2 (by rfl) ⟨787290, by rfl⟩ : syracuseStep 2099441 = 1574581) B1574581
theorem B1992961 : Blo 1399519 1992961 := bstep (se 2 (by rfl) ⟨747360, by rfl⟩ : syracuseStep 1992961 = 1494721) B1494721
theorem B2099459 : Blo 1399519 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B2099489 : Blo 1399519 2099489 := bstep (se 2 (by rfl) ⟨787308, by rfl⟩ : syracuseStep 2099489 = 1574617) B1574617
theorem B2099507 : Blo 1399519 2099507 := bstep (se 1 (by rfl) ⟨1574630, by rfl⟩ : syracuseStep 2099507 = 3149261) B3149261
theorem B2099537 : Blo 1399519 2099537 := bstep (se 2 (by rfl) ⟨787326, by rfl⟩ : syracuseStep 2099537 = 1574653) B1574653
theorem B2099555 : Blo 1399519 2099555 := bstep (se 1 (by rfl) ⟨1574666, by rfl⟩ : syracuseStep 2099555 = 3149333) B3149333
theorem B10226033 : Blo 1399519 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B1575283 : Blo 1399519 1575283 := bstep (se 1 (by rfl) ⟨1181462, by rfl⟩ : syracuseStep 1575283 = 2362925) B2362925
theorem B2099585 : Blo 1399519 2099585 := bstep (se 2 (by rfl) ⟨787344, by rfl⟩ : syracuseStep 2099585 = 1574689) B1574689
theorem B2099603 : Blo 1399519 2099603 := bstep (se 1 (by rfl) ⟨1574702, by rfl⟩ : syracuseStep 2099603 = 3149405) B3149405
theorem B2099633 : Blo 1399519 2099633 := bstep (se 2 (by rfl) ⟨787362, by rfl⟩ : syracuseStep 2099633 = 1574725) B1574725
theorem B4729265 : Blo 1399519 4729265 := bstep (se 2 (by rfl) ⟨1773474, by rfl⟩ : syracuseStep 4729265 = 3546949) B3546949
theorem B2099651 : Blo 1399519 2099651 := bstep (se 1 (by rfl) ⟨1574738, by rfl⟩ : syracuseStep 2099651 = 3149477) B3149477
theorem B2361811 : Blo 1399519 2361811 := bstep (se 1 (by rfl) ⟨1771358, by rfl⟩ : syracuseStep 2361811 = 3542717) B3542717
theorem B2099681 : Blo 1399519 2099681 := bstep (se 2 (by rfl) ⟨787380, by rfl⟩ : syracuseStep 2099681 = 1574761) B1574761
theorem B16394723 : Blo 1399519 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B6392305 : Blo 1399519 6392305 := bstep (se 2 (by rfl) ⟨2397114, by rfl⟩ : syracuseStep 6392305 = 4794229) B4794229
theorem B2099699 : Blo 1399519 2099699 := bstep (se 1 (by rfl) ⟨1574774, by rfl⟩ : syracuseStep 2099699 = 3149549) B3149549
theorem B1575427 : Blo 1399519 1575427 := bstep (se 1 (by rfl) ⟨1181570, by rfl⟩ : syracuseStep 1575427 = 2363141) B2363141
theorem B1419779 : Blo 1399519 1419779 := bstep (se 1 (by rfl) ⟨1064834, by rfl⟩ : syracuseStep 1419779 = 2129669) B2129669
theorem B2099729 : Blo 1399519 2099729 := bstep (se 2 (by rfl) ⟨787398, by rfl⟩ : syracuseStep 2099729 = 1574797) B1574797
theorem B2099747 : Blo 1399519 2099747 := bstep (se 1 (by rfl) ⟨1574810, by rfl⟩ : syracuseStep 2099747 = 3149621) B3149621
theorem B2099777 : Blo 1399519 2099777 := bstep (se 2 (by rfl) ⟨787416, by rfl⟩ : syracuseStep 2099777 = 1574833) B1574833
theorem B2099795 : Blo 1399519 2099795 := bstep (se 1 (by rfl) ⟨1574846, by rfl⟩ : syracuseStep 2099795 = 3149693) B3149693
theorem B2361953 : Blo 1399519 2361953 := bstep (se 2 (by rfl) ⟨885732, by rfl⟩ : syracuseStep 2361953 = 1771465) B1771465
theorem B2099825 : Blo 1399519 2099825 := bstep (se 2 (by rfl) ⟨787434, by rfl⟩ : syracuseStep 2099825 = 1574869) B1574869
theorem B2099843 : Blo 1399519 2099843 := bstep (se 1 (by rfl) ⟨1574882, by rfl⟩ : syracuseStep 2099843 = 3149765) B3149765
theorem B1682051 : Blo 1399519 1682051 := bstep (se 1 (by rfl) ⟨1261538, by rfl⟩ : syracuseStep 1682051 = 2523077) B2523077
theorem B1575571 : Blo 1399519 1575571 := bstep (se 1 (by rfl) ⟨1181678, by rfl⟩ : syracuseStep 1575571 = 2363357) B2363357
theorem B2099873 : Blo 1399519 2099873 := bstep (se 2 (by rfl) ⟨787452, by rfl⟩ : syracuseStep 2099873 = 1574905) B1574905
theorem B2099891 : Blo 1399519 2099891 := bstep (se 1 (by rfl) ⟨1574918, by rfl⟩ : syracuseStep 2099891 = 3149837) B3149837
theorem B2099921 : Blo 1399519 2099921 := bstep (se 2 (by rfl) ⟨787470, by rfl⟩ : syracuseStep 2099921 = 1574941) B1574941
theorem B2362081 : Blo 1399519 2362081 := bstep (se 2 (by rfl) ⟨885780, by rfl⟩ : syracuseStep 2362081 = 1771561) B1771561
theorem B2099939 : Blo 1399519 2099939 := bstep (se 1 (by rfl) ⟨1574954, by rfl⟩ : syracuseStep 2099939 = 3149909) B3149909
theorem B1772275 : Blo 1399519 1772275 := bstep (se 1 (by rfl) ⟨1329206, by rfl⟩ : syracuseStep 1772275 = 2658413) B2658413
theorem B2099969 : Blo 1399519 2099969 := bstep (se 2 (by rfl) ⟨787488, by rfl⟩ : syracuseStep 2099969 = 1574977) B1574977
theorem B2362115 : Blo 1399519 2362115 := bstep (se 1 (by rfl) ⟨1771586, by rfl⟩ : syracuseStep 2362115 = 3543173) B3543173
theorem B2099987 : Blo 1399519 2099987 := bstep (se 1 (by rfl) ⟨1574990, by rfl⟩ : syracuseStep 2099987 = 3149981) B3149981
theorem B1575715 : Blo 1399519 1575715 := bstep (se 1 (by rfl) ⟨1181786, by rfl⟩ : syracuseStep 1575715 = 2363573) B2363573
theorem B2100017 : Blo 1399519 2100017 := bstep (se 2 (by rfl) ⟨787506, by rfl⟩ : syracuseStep 2100017 = 1575013) B1575013
theorem B2100035 : Blo 1399519 2100035 := bstep (se 1 (by rfl) ⟨1575026, by rfl⟩ : syracuseStep 2100035 = 3150053) B3150053
theorem B3238723 : Blo 1399519 3238723 := bstep (se 1 (by rfl) ⟨2429042, by rfl⟩ : syracuseStep 3238723 = 4858085) B4858085
theorem B1772371 : Blo 1399519 1772371 := bstep (se 1 (by rfl) ⟨1329278, by rfl⟩ : syracuseStep 1772371 = 2658557) B2658557
theorem B2100065 : Blo 1399519 2100065 := bstep (se 2 (by rfl) ⟨787524, by rfl⟩ : syracuseStep 2100065 = 1575049) B1575049
theorem B2657137 : Blo 1399519 2657137 := bstep (se 2 (by rfl) ⟨996426, by rfl⟩ : syracuseStep 2657137 = 1992853) B1992853
theorem B2100083 : Blo 1399519 2100083 := bstep (se 1 (by rfl) ⟨1575062, by rfl⟩ : syracuseStep 2100083 = 3150125) B3150125
theorem B2362243 : Blo 1399519 2362243 := bstep (se 1 (by rfl) ⟨1771682, by rfl⟩ : syracuseStep 2362243 = 3543365) B3543365
theorem B1796995 : Blo 1399519 1796995 := bstep (se 1 (by rfl) ⟨1347746, by rfl⟩ : syracuseStep 1796995 = 2695493) B2695493
theorem B2100113 : Blo 1399519 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B2100131 : Blo 1399519 2100131 := bstep (se 1 (by rfl) ⟨1575098, by rfl⟩ : syracuseStep 2100131 = 3150197) B3150197
theorem B1575859 : Blo 1399519 1575859 := bstep (se 1 (by rfl) ⟨1181894, by rfl⟩ : syracuseStep 1575859 = 2363789) B2363789
theorem B2100161 : Blo 1399519 2100161 := bstep (se 2 (by rfl) ⟨787560, by rfl⟩ : syracuseStep 2100161 = 1575121) B1575121
theorem B4729805 : Blo 1399519 4729805 := bstep (se 3 (by rfl) ⟨886838, by rfl⟩ : syracuseStep 4729805 = 1773677) B1773677
theorem B2100179 : Blo 1399519 2100179 := bstep (se 1 (by rfl) ⟨1575134, by rfl⟩ : syracuseStep 2100179 = 3150269) B3150269
theorem B2100209 : Blo 1399519 2100209 := bstep (se 2 (by rfl) ⟨787578, by rfl⟩ : syracuseStep 2100209 = 1575157) B1575157
theorem B5319665 : Blo 1399519 5319665 := bstep (se 2 (by rfl) ⟨1994874, by rfl⟩ : syracuseStep 5319665 = 3989749) B3989749
theorem B2100227 : Blo 1399519 2100227 := bstep (se 1 (by rfl) ⟨1575170, by rfl⟩ : syracuseStep 2100227 = 3150341) B3150341
theorem B4729859 : Blo 1399519 4729859 := bstep (se 1 (by rfl) ⟨3547394, by rfl⟩ : syracuseStep 4729859 = 7094789) B7094789
theorem B2362385 : Blo 1399519 2362385 := bstep (se 2 (by rfl) ⟨885894, by rfl⟩ : syracuseStep 2362385 = 1771789) B1771789
theorem B1993747 : Blo 1399519 1993747 := bstep (se 1 (by rfl) ⟨1495310, by rfl⟩ : syracuseStep 1993747 = 2990621) B2990621
theorem B2100257 : Blo 1399519 2100257 := bstep (se 2 (by rfl) ⟨787596, by rfl⟩ : syracuseStep 2100257 = 1575193) B1575193
theorem B9096241 : Blo 1399519 9096241 := bstep (se 2 (by rfl) ⟨3411090, by rfl⟩ : syracuseStep 9096241 = 6822181) B6822181
theorem B2100275 : Blo 1399519 2100275 := bstep (se 1 (by rfl) ⟨1575206, by rfl⟩ : syracuseStep 2100275 = 3150413) B3150413
theorem B17280053 : Blo 1399519 17280053 := bstep (se 5 (by rfl) ⟨810002, by rfl⟩ : syracuseStep 17280053 = 1620005) B1620005
theorem B1576003 : Blo 1399519 1576003 := bstep (se 1 (by rfl) ⟨1182002, by rfl⟩ : syracuseStep 1576003 = 2364005) B2364005
theorem B2100305 : Blo 1399519 2100305 := bstep (se 2 (by rfl) ⟨787614, by rfl⟩ : syracuseStep 2100305 = 1575229) B1575229
theorem B2100323 : Blo 1399519 2100323 := bstep (se 1 (by rfl) ⟨1575242, by rfl⟩ : syracuseStep 2100323 = 3150485) B3150485
theorem B2100353 : Blo 1399519 2100353 := bstep (se 2 (by rfl) ⟨787632, by rfl⟩ : syracuseStep 2100353 = 1575265) B1575265
theorem B2362513 : Blo 1399519 2362513 := bstep (se 2 (by rfl) ⟨885942, by rfl⟩ : syracuseStep 2362513 = 1771885) B1771885
theorem B2100371 : Blo 1399519 2100371 := bstep (se 1 (by rfl) ⟨1575278, by rfl⟩ : syracuseStep 2100371 = 3150557) B3150557
theorem B2100401 : Blo 1399519 2100401 := bstep (se 2 (by rfl) ⟨787650, by rfl⟩ : syracuseStep 2100401 = 1575301) B1575301
theorem B2362547 : Blo 1399519 2362547 := bstep (se 1 (by rfl) ⟨1771910, by rfl⟩ : syracuseStep 2362547 = 3543821) B3543821
theorem B2100419 : Blo 1399519 2100419 := bstep (se 1 (by rfl) ⟨1575314, by rfl⟩ : syracuseStep 2100419 = 3150629) B3150629
theorem B3149009 : Blo 1399519 3149009 := bstep (se 2 (by rfl) ⟨1180878, by rfl⟩ : syracuseStep 3149009 = 2361757) B2361757
theorem B1576147 : Blo 1399519 1576147 := bstep (se 1 (by rfl) ⟨1182110, by rfl⟩ : syracuseStep 1576147 = 2364221) B2364221
theorem B2100449 : Blo 1399519 2100449 := bstep (se 2 (by rfl) ⟨787668, by rfl⟩ : syracuseStep 2100449 = 1575337) B1575337
theorem B3149027 : Blo 1399519 3149027 := bstep (se 1 (by rfl) ⟨2361770, by rfl⟩ : syracuseStep 3149027 = 4723541) B4723541
theorem B2100467 : Blo 1399519 2100467 := bstep (se 1 (by rfl) ⟨1575350, by rfl⟩ : syracuseStep 2100467 = 3150701) B3150701
theorem B2657539 : Blo 1399519 2657539 := bstep (se 1 (by rfl) ⟨1993154, by rfl⟩ : syracuseStep 2657539 = 3986309) B3986309
theorem B2100497 : Blo 1399519 2100497 := bstep (se 2 (by rfl) ⟨787686, by rfl⟩ : syracuseStep 2100497 = 1575373) B1575373
theorem B4730129 : Blo 1399519 4730129 := bstep (se 2 (by rfl) ⟨1773798, by rfl⟩ : syracuseStep 4730129 = 3547597) B3547597
theorem B2100515 : Blo 1399519 2100515 := bstep (se 1 (by rfl) ⟨1575386, by rfl⟩ : syracuseStep 2100515 = 3150773) B3150773
theorem B7089443 : Blo 1399519 7089443 := bstep (se 1 (by rfl) ⟨5317082, by rfl⟩ : syracuseStep 7089443 = 10634165) B10634165
theorem B2657585 : Blo 1399519 2657585 := bstep (se 2 (by rfl) ⟨996594, by rfl⟩ : syracuseStep 2657585 = 1993189) B1993189
theorem B2362675 : Blo 1399519 2362675 := bstep (se 1 (by rfl) ⟨1772006, by rfl⟩ : syracuseStep 2362675 = 3544013) B3544013
theorem B2100545 : Blo 1399519 2100545 := bstep (se 2 (by rfl) ⟨787704, by rfl⟩ : syracuseStep 2100545 = 1575409) B1575409
theorem B1772867 : Blo 1399519 1772867 := bstep (se 1 (by rfl) ⟨1329650, by rfl⟩ : syracuseStep 1772867 = 2659301) B2659301
theorem B2100563 : Blo 1399519 2100563 := bstep (se 1 (by rfl) ⟨1575422, by rfl⟩ : syracuseStep 2100563 = 3150845) B3150845
theorem B1576291 : Blo 1399519 1576291 := bstep (se 1 (by rfl) ⟨1182218, by rfl⟩ : syracuseStep 1576291 = 2364437) B2364437
theorem B2100593 : Blo 1399519 2100593 := bstep (se 2 (by rfl) ⟨787722, by rfl⟩ : syracuseStep 2100593 = 1575445) B1575445
theorem B2100611 : Blo 1399519 2100611 := bstep (se 1 (by rfl) ⟨1575458, by rfl⟩ : syracuseStep 2100611 = 3150917) B3150917
theorem B2100641 : Blo 1399519 2100641 := bstep (se 2 (by rfl) ⟨787740, by rfl⟩ : syracuseStep 2100641 = 1575481) B1575481
theorem B2100659 : Blo 1399519 2100659 := bstep (se 1 (by rfl) ⟨1575494, by rfl⟩ : syracuseStep 2100659 = 3150989) B3150989
theorem B1641907 : Blo 1399519 1641907 := bstep (se 1 (by rfl) ⟨1231430, by rfl⟩ : syracuseStep 1641907 = 2462861) B2462861
theorem B2362817 : Blo 1399519 2362817 := bstep (se 2 (by rfl) ⟨886056, by rfl⟩ : syracuseStep 2362817 = 1772113) B1772113
theorem B2100689 : Blo 1399519 2100689 := bstep (se 2 (by rfl) ⟨787758, by rfl⟩ : syracuseStep 2100689 = 1575517) B1575517
theorem B2100707 : Blo 1399519 2100707 := bstep (se 1 (by rfl) ⟨1575530, by rfl⟩ : syracuseStep 2100707 = 3151061) B3151061
theorem B3149297 : Blo 1399519 3149297 := bstep (se 2 (by rfl) ⟨1180986, by rfl⟩ : syracuseStep 3149297 = 2361973) B2361973
theorem B1994225 : Blo 1399519 1994225 := bstep (se 2 (by rfl) ⟨747834, by rfl⟩ : syracuseStep 1994225 = 1495669) B1495669
theorem B1576435 : Blo 1399519 1576435 := bstep (se 1 (by rfl) ⟨1182326, by rfl⟩ : syracuseStep 1576435 = 2364653) B2364653
theorem B2100737 : Blo 1399519 2100737 := bstep (se 2 (by rfl) ⟨787776, by rfl⟩ : syracuseStep 2100737 = 1575553) B1575553
theorem B3149315 : Blo 1399519 3149315 := bstep (se 1 (by rfl) ⟨2361986, by rfl⟩ : syracuseStep 3149315 = 4723973) B4723973
theorem B2100755 : Blo 1399519 2100755 := bstep (se 1 (by rfl) ⟨1575566, by rfl⟩ : syracuseStep 2100755 = 3151133) B3151133
theorem B2100785 : Blo 1399519 2100785 := bstep (se 2 (by rfl) ⟨787794, by rfl⟩ : syracuseStep 2100785 = 1575589) B1575589
theorem B2362945 : Blo 1399519 2362945 := bstep (se 2 (by rfl) ⟨886104, by rfl⟩ : syracuseStep 2362945 = 1772209) B1772209
theorem B2100803 : Blo 1399519 2100803 := bstep (se 1 (by rfl) ⟨1575602, by rfl⟩ : syracuseStep 2100803 = 3151205) B3151205
theorem B2657873 : Blo 1399519 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B2100833 : Blo 1399519 2100833 := bstep (se 2 (by rfl) ⟨787812, by rfl⟩ : syracuseStep 2100833 = 1575625) B1575625
theorem B2362979 : Blo 1399519 2362979 := bstep (se 1 (by rfl) ⟨1772234, by rfl⟩ : syracuseStep 2362979 = 3544469) B3544469
theorem B1994339 : Blo 1399519 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B2100851 : Blo 1399519 2100851 := bstep (se 1 (by rfl) ⟨1575638, by rfl⟩ : syracuseStep 2100851 = 3151277) B3151277
theorem B1576579 : Blo 1399519 1576579 := bstep (se 1 (by rfl) ⟨1182434, by rfl⟩ : syracuseStep 1576579 = 2364869) B2364869
theorem B2100881 : Blo 1399519 2100881 := bstep (se 2 (by rfl) ⟨787830, by rfl⟩ : syracuseStep 2100881 = 1575661) B1575661
theorem B2100899 : Blo 1399519 2100899 := bstep (se 1 (by rfl) ⟨1575674, by rfl⟩ : syracuseStep 2100899 = 3151349) B3151349
theorem B1994419 : Blo 1399519 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B2100929 : Blo 1399519 2100929 := bstep (se 2 (by rfl) ⟨787848, by rfl⟩ : syracuseStep 2100929 = 1575697) B1575697
theorem B4484803 : Blo 1399519 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B7573189 : Blo 1399519 7573189 := bstep (se 4 (by rfl) ⟨709986, by rfl⟩ : syracuseStep 7573189 = 1419973) B1419973
theorem B3542737 : Blo 1399519 3542737 := bstep (se 2 (by rfl) ⟨1328526, by rfl⟩ : syracuseStep 3542737 = 2657053) B2657053
theorem B2100947 : Blo 1399519 2100947 := bstep (se 1 (by rfl) ⟨1575710, by rfl⟩ : syracuseStep 2100947 = 3151421) B3151421
theorem B2363107 : Blo 1399519 2363107 := bstep (se 1 (by rfl) ⟨1772330, by rfl⟩ : syracuseStep 2363107 = 3544661) B3544661
theorem B2100977 : Blo 1399519 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B2100995 : Blo 1399519 2100995 := bstep (se 1 (by rfl) ⟨1575746, by rfl⟩ : syracuseStep 2100995 = 3151493) B3151493
theorem B3149585 : Blo 1399519 3149585 := bstep (se 2 (by rfl) ⟨1181094, by rfl⟩ : syracuseStep 3149585 = 2362189) B2362189
theorem B2101025 : Blo 1399519 2101025 := bstep (se 2 (by rfl) ⟨787884, by rfl⟩ : syracuseStep 2101025 = 1575769) B1575769
theorem B3149603 : Blo 1399519 3149603 := bstep (se 1 (by rfl) ⟨2362202, by rfl⟩ : syracuseStep 3149603 = 4724405) B4724405
theorem B2395939 : Blo 1399519 2395939 := bstep (se 1 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 2395939 = 3593909) B3593909
theorem B7573297 : Blo 1399519 7573297 := bstep (se 2 (by rfl) ⟨2839986, by rfl⟩ : syracuseStep 7573297 = 5679973) B5679973
theorem B2101043 : Blo 1399519 2101043 := bstep (se 1 (by rfl) ⟨1575782, by rfl⟩ : syracuseStep 2101043 = 3151565) B3151565
theorem B5984077 : Blo 1399519 5984077 := bstep (se 3 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 5984077 = 2244029) B2244029
theorem B4484945 : Blo 1399519 4484945 := bstep (se 2 (by rfl) ⟨1681854, by rfl⟩ : syracuseStep 4484945 = 3363709) B3363709
theorem B2101073 : Blo 1399519 2101073 := bstep (se 2 (by rfl) ⟨787902, by rfl⟩ : syracuseStep 2101073 = 1575805) B1575805
theorem B1494883 : Blo 1399519 1494883 := bstep (se 1 (by rfl) ⟨1121162, by rfl⟩ : syracuseStep 1494883 = 2242325) B2242325
theorem B2101091 : Blo 1399519 2101091 := bstep (se 1 (by rfl) ⟨1575818, by rfl⟩ : syracuseStep 2101091 = 3151637) B3151637
theorem B2363249 : Blo 1399519 2363249 := bstep (se 2 (by rfl) ⟨886218, by rfl⟩ : syracuseStep 2363249 = 1772437) B1772437
theorem B2101121 : Blo 1399519 2101121 := bstep (se 2 (by rfl) ⟨787920, by rfl⟩ : syracuseStep 2101121 = 1575841) B1575841
theorem B4042637 : Blo 1399519 4042637 := bstep (se 3 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 4042637 = 1515989) B1515989
theorem B2101139 : Blo 1399519 2101139 := bstep (se 1 (by rfl) ⟨1575854, by rfl⟩ : syracuseStep 2101139 = 3151709) B3151709
theorem B2101169 : Blo 1399519 2101169 := bstep (se 2 (by rfl) ⟨787938, by rfl⟩ : syracuseStep 2101169 = 1575877) B1575877
theorem B4485059 : Blo 1399519 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B2101187 : Blo 1399519 2101187 := bstep (se 1 (by rfl) ⟨1575890, by rfl⟩ : syracuseStep 2101187 = 3151781) B3151781
theorem B2101217 : Blo 1399519 2101217 := bstep (se 2 (by rfl) ⟨787956, by rfl⟩ : syracuseStep 2101217 = 1575913) B1575913
theorem B3543011 : Blo 1399519 3543011 := bstep (se 1 (by rfl) ⟨2657258, by rfl⟩ : syracuseStep 3543011 = 5314517) B5314517
theorem B2363377 : Blo 1399519 2363377 := bstep (se 2 (by rfl) ⟨886266, by rfl⟩ : syracuseStep 2363377 = 1772533) B1772533
theorem B2101235 : Blo 1399519 2101235 := bstep (se 1 (by rfl) ⟨1575926, by rfl⟩ : syracuseStep 2101235 = 3151853) B3151853
theorem B1773571 : Blo 1399519 1773571 := bstep (se 1 (by rfl) ⟨1330178, by rfl⟩ : syracuseStep 1773571 = 2660357) B2660357
theorem B2101265 : Blo 1399519 2101265 := bstep (se 2 (by rfl) ⟨787974, by rfl⟩ : syracuseStep 2101265 = 1575949) B1575949
theorem B2363411 : Blo 1399519 2363411 := bstep (se 1 (by rfl) ⟨1772558, by rfl⟩ : syracuseStep 2363411 = 3545117) B3545117
theorem B2101283 : Blo 1399519 2101283 := bstep (se 1 (by rfl) ⟨1575962, by rfl⟩ : syracuseStep 2101283 = 3151925) B3151925
theorem B3149873 : Blo 1399519 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B2101313 : Blo 1399519 2101313 := bstep (se 2 (by rfl) ⟨787992, by rfl⟩ : syracuseStep 2101313 = 1575985) B1575985
theorem B3149891 : Blo 1399519 3149891 := bstep (se 1 (by rfl) ⟨2362418, by rfl⟩ : syracuseStep 3149891 = 4724837) B4724837
theorem B7090253 : Blo 1399519 7090253 := bstep (se 3 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 7090253 = 2658845) B2658845
theorem B2101331 : Blo 1399519 2101331 := bstep (se 1 (by rfl) ⟨1575998, by rfl⟩ : syracuseStep 2101331 = 3151997) B3151997
theorem B1773667 : Blo 1399519 1773667 := bstep (se 1 (by rfl) ⟨1330250, by rfl⟩ : syracuseStep 1773667 = 2660501) B2660501
theorem B2101361 : Blo 1399519 2101361 := bstep (se 2 (by rfl) ⟨788010, by rfl⟩ : syracuseStep 2101361 = 1576021) B1576021
theorem B2101379 : Blo 1399519 2101379 := bstep (se 1 (by rfl) ⟨1576034, by rfl⟩ : syracuseStep 2101379 = 3152069) B3152069
theorem B2363539 : Blo 1399519 2363539 := bstep (se 1 (by rfl) ⟨1772654, by rfl⟩ : syracuseStep 2363539 = 3545309) B3545309
theorem B2101409 : Blo 1399519 2101409 := bstep (se 2 (by rfl) ⟨788028, by rfl⟩ : syracuseStep 2101409 = 1576057) B1576057
theorem B3543203 : Blo 1399519 3543203 := bstep (se 1 (by rfl) ⟨2657402, by rfl⟩ : syracuseStep 3543203 = 5314805) B5314805
theorem B2101427 : Blo 1399519 2101427 := bstep (se 1 (by rfl) ⟨1576070, by rfl⟩ : syracuseStep 2101427 = 3152141) B3152141
theorem B2101457 : Blo 1399519 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B1994977 : Blo 1399519 1994977 := bstep (se 2 (by rfl) ⟨748116, by rfl⟩ : syracuseStep 1994977 = 1496233) B1496233
theorem B2101475 : Blo 1399519 2101475 := bstep (se 1 (by rfl) ⟨1576106, by rfl⟩ : syracuseStep 2101475 = 3152213) B3152213
theorem B3985649 : Blo 1399519 3985649 := bstep (se 2 (by rfl) ⟨1494618, by rfl⟩ : syracuseStep 3985649 = 2989237) B2989237
theorem B7287025 : Blo 1399519 7287025 := bstep (se 2 (by rfl) ⟨2732634, by rfl⟩ : syracuseStep 7287025 = 5465269) B5465269
theorem B2101505 : Blo 1399519 2101505 := bstep (se 2 (by rfl) ⟨788064, by rfl⟩ : syracuseStep 2101505 = 1576129) B1576129
theorem B2101523 : Blo 1399519 2101523 := bstep (se 1 (by rfl) ⟨1576142, by rfl⟩ : syracuseStep 2101523 = 3152285) B3152285
theorem B2363681 : Blo 1399519 2363681 := bstep (se 2 (by rfl) ⟨886380, by rfl⟩ : syracuseStep 2363681 = 1772761) B1772761
theorem B2658595 : Blo 1399519 2658595 := bstep (se 1 (by rfl) ⟨1993946, by rfl⟩ : syracuseStep 2658595 = 3987893) B3987893
theorem B2101553 : Blo 1399519 2101553 := bstep (se 2 (by rfl) ⟨788082, by rfl⟩ : syracuseStep 2101553 = 1576165) B1576165
theorem B2101571 : Blo 1399519 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B3150161 : Blo 1399519 3150161 := bstep (se 2 (by rfl) ⟨1181310, by rfl⟩ : syracuseStep 3150161 = 2362621) B2362621
theorem B2101601 : Blo 1399519 2101601 := bstep (se 2 (by rfl) ⟨788100, by rfl⟩ : syracuseStep 2101601 = 1576201) B1576201
theorem B3150179 : Blo 1399519 3150179 := bstep (se 1 (by rfl) ⟨2362634, by rfl⟩ : syracuseStep 3150179 = 4725269) B4725269
theorem B2101619 : Blo 1399519 2101619 := bstep (se 1 (by rfl) ⟨1576214, by rfl⟩ : syracuseStep 2101619 = 3152429) B3152429
theorem B11973005 : Blo 1399519 11973005 := bstep (se 3 (by rfl) ⟨2244938, by rfl⟩ : syracuseStep 11973005 = 4489877) B4489877
theorem B2101649 : Blo 1399519 2101649 := bstep (se 2 (by rfl) ⟨788118, by rfl⟩ : syracuseStep 2101649 = 1576237) B1576237
theorem B2363809 : Blo 1399519 2363809 := bstep (se 2 (by rfl) ⟨886428, by rfl⟩ : syracuseStep 2363809 = 1772857) B1772857
theorem B2101667 : Blo 1399519 2101667 := bstep (se 1 (by rfl) ⟨1576250, by rfl⟩ : syracuseStep 2101667 = 3152501) B3152501
theorem B5321123 : Blo 1399519 5321123 := bstep (se 1 (by rfl) ⟨3990842, by rfl⟩ : syracuseStep 5321123 = 7981685) B7981685
theorem B2101697 : Blo 1399519 2101697 := bstep (se 2 (by rfl) ⟨788136, by rfl⟩ : syracuseStep 2101697 = 1576273) B1576273
theorem B2363843 : Blo 1399519 2363843 := bstep (se 1 (by rfl) ⟨1772882, by rfl⟩ : syracuseStep 2363843 = 3545765) B3545765
theorem B11506117 : Blo 1399519 11506117 := bstep (se 4 (by rfl) ⟨1078698, by rfl⟩ : syracuseStep 11506117 = 2157397) B2157397
theorem B2101715 : Blo 1399519 2101715 := bstep (se 1 (by rfl) ⟨1576286, by rfl⟩ : syracuseStep 2101715 = 3152573) B3152573
theorem B2101745 : Blo 1399519 2101745 := bstep (se 2 (by rfl) ⟨788154, by rfl⟩ : syracuseStep 2101745 = 1576309) B1576309
theorem B2101763 : Blo 1399519 2101763 := bstep (se 1 (by rfl) ⟨1576322, by rfl⟩ : syracuseStep 2101763 = 3152645) B3152645
theorem B11964941 : Blo 1399519 11964941 := bstep (se 3 (by rfl) ⟨2243426, by rfl⟩ : syracuseStep 11964941 = 4486853) B4486853
theorem B2101793 : Blo 1399519 2101793 := bstep (se 2 (by rfl) ⟨788172, by rfl⟩ : syracuseStep 2101793 = 1576345) B1576345
theorem B2101811 : Blo 1399519 2101811 := bstep (se 1 (by rfl) ⟨1576358, by rfl⟩ : syracuseStep 2101811 = 3152717) B3152717
theorem B2363971 : Blo 1399519 2363971 := bstep (se 1 (by rfl) ⟨1772978, by rfl⟩ : syracuseStep 2363971 = 3545957) B3545957
theorem B2101841 : Blo 1399519 2101841 := bstep (se 2 (by rfl) ⟨788190, by rfl⟩ : syracuseStep 2101841 = 1576381) B1576381
theorem B2101859 : Blo 1399519 2101859 := bstep (se 1 (by rfl) ⟨1576394, by rfl⟩ : syracuseStep 2101859 = 3152789) B3152789
theorem B3150449 : Blo 1399519 3150449 := bstep (se 2 (by rfl) ⟨1181418, by rfl⟩ : syracuseStep 3150449 = 2362837) B2362837
theorem B2273905 : Blo 1399519 2273905 := bstep (se 2 (by rfl) ⟨852714, by rfl⟩ : syracuseStep 2273905 = 1705429) B1705429
theorem B2101889 : Blo 1399519 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B3150467 : Blo 1399519 3150467 := bstep (se 1 (by rfl) ⟨2362850, by rfl⟩ : syracuseStep 3150467 = 4725701) B4725701
theorem B2101907 : Blo 1399519 2101907 := bstep (se 1 (by rfl) ⟨1576430, by rfl⟩ : syracuseStep 2101907 = 3152861) B3152861
theorem B7565987 : Blo 1399519 7565987 := bstep (se 1 (by rfl) ⟨5674490, by rfl⟩ : syracuseStep 7565987 = 11348981) B11348981
theorem B2101937 : Blo 1399519 2101937 := bstep (se 2 (by rfl) ⟨788226, by rfl⟩ : syracuseStep 2101937 = 1576453) B1576453
theorem B2101955 : Blo 1399519 2101955 := bstep (se 1 (by rfl) ⟨1576466, by rfl⟩ : syracuseStep 2101955 = 3152933) B3152933
theorem B2364113 : Blo 1399519 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B2101985 : Blo 1399519 2101985 := bstep (se 2 (by rfl) ⟨788244, by rfl⟩ : syracuseStep 2101985 = 1576489) B1576489
theorem B2659043 : Blo 1399519 2659043 := bstep (se 1 (by rfl) ⟨1994282, by rfl⟩ : syracuseStep 2659043 = 3988565) B3988565
theorem B2102003 : Blo 1399519 2102003 := bstep (se 1 (by rfl) ⟨1576502, by rfl⟩ : syracuseStep 2102003 = 3153005) B3153005
theorem B4256525 : Blo 1399519 4256525 := bstep (se 3 (by rfl) ⟨798098, by rfl⟩ : syracuseStep 4256525 = 1596197) B1596197
theorem B2102033 : Blo 1399519 2102033 := bstep (se 2 (by rfl) ⟨788262, by rfl⟩ : syracuseStep 2102033 = 1576525) B1576525
theorem B7566115 : Blo 1399519 7566115 := bstep (se 1 (by rfl) ⟨5674586, by rfl⟩ : syracuseStep 7566115 = 11349173) B11349173
theorem B2102051 : Blo 1399519 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B2102081 : Blo 1399519 2102081 := bstep (se 2 (by rfl) ⟨788280, by rfl⟩ : syracuseStep 2102081 = 1576561) B1576561
theorem B2364241 : Blo 1399519 2364241 := bstep (se 2 (by rfl) ⟨886590, by rfl⟩ : syracuseStep 2364241 = 1773181) B1773181
theorem B1495891 : Blo 1399519 1495891 := bstep (se 1 (by rfl) ⟨1121918, by rfl⟩ : syracuseStep 1495891 = 2243837) B2243837
theorem B2102099 : Blo 1399519 2102099 := bstep (se 1 (by rfl) ⟨1576574, by rfl⟩ : syracuseStep 2102099 = 3153149) B3153149
theorem B10236785 : Blo 1399519 10236785 := bstep (se 2 (by rfl) ⟨3838794, by rfl⟩ : syracuseStep 10236785 = 7677589) B7677589
theorem B2102129 : Blo 1399519 2102129 := bstep (se 2 (by rfl) ⟨788298, by rfl⟩ : syracuseStep 2102129 = 1576597) B1576597
theorem B2364275 : Blo 1399519 2364275 := bstep (se 1 (by rfl) ⟨1773206, by rfl⟩ : syracuseStep 2364275 = 3546413) B3546413
theorem B2839427 : Blo 1399519 2839427 := bstep (se 1 (by rfl) ⟨2129570, by rfl⟩ : syracuseStep 2839427 = 4259141) B4259141
theorem B2102147 : Blo 1399519 2102147 := bstep (se 1 (by rfl) ⟨1576610, by rfl⟩ : syracuseStep 2102147 = 3153221) B3153221
theorem B9581453 : Blo 1399519 9581453 := bstep (se 3 (by rfl) ⟨1796522, by rfl⟩ : syracuseStep 9581453 = 3593045) B3593045
theorem B4486033 : Blo 1399519 4486033 := bstep (se 2 (by rfl) ⟨1682262, by rfl⟩ : syracuseStep 4486033 = 3364525) B3364525
theorem B3150737 : Blo 1399519 3150737 := bstep (se 2 (by rfl) ⟨1181526, by rfl⟩ : syracuseStep 3150737 = 2363053) B2363053
theorem B2102177 : Blo 1399519 2102177 := bstep (se 2 (by rfl) ⟨788316, by rfl⟩ : syracuseStep 2102177 = 1576633) B1576633
theorem B3150755 : Blo 1399519 3150755 := bstep (se 1 (by rfl) ⟨2363066, by rfl⟩ : syracuseStep 3150755 = 4726133) B4726133
theorem B2102195 : Blo 1399519 2102195 := bstep (se 1 (by rfl) ⟨1576646, by rfl⟩ : syracuseStep 2102195 = 3153293) B3153293
theorem B2102225 : Blo 1399519 2102225 := bstep (se 2 (by rfl) ⟨788334, by rfl⟩ : syracuseStep 2102225 = 1576669) B1576669
theorem B11957219 : Blo 1399519 11957219 := bstep (se 1 (by rfl) ⟨8967914, by rfl⟩ : syracuseStep 11957219 = 17935829) B17935829
theorem B2102243 : Blo 1399519 2102243 := bstep (se 1 (by rfl) ⟨1576682, by rfl⟩ : syracuseStep 2102243 = 3153365) B3153365
theorem B2364403 : Blo 1399519 2364403 := bstep (se 1 (by rfl) ⟨1773302, by rfl⟩ : syracuseStep 2364403 = 3546605) B3546605
theorem B2102273 : Blo 1399519 2102273 := bstep (se 2 (by rfl) ⟨788352, by rfl⟩ : syracuseStep 2102273 = 1576705) B1576705
theorem B3986435 : Blo 1399519 3986435 := bstep (se 1 (by rfl) ⟨2989826, by rfl⟩ : syracuseStep 3986435 = 5979653) B5979653
theorem B2659331 : Blo 1399519 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B4723757 : Blo 1399519 4723757 := bstep (se 3 (by rfl) ⟨885704, by rfl⟩ : syracuseStep 4723757 = 1771409) B1771409
theorem B2397251 : Blo 1399519 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B3544145 : Blo 1399519 3544145 := bstep (se 2 (by rfl) ⟨1329054, by rfl⟩ : syracuseStep 3544145 = 2658109) B2658109
theorem B3839057 : Blo 1399519 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B4723811 : Blo 1399519 4723811 := bstep (se 1 (by rfl) ⟨3542858, by rfl⟩ : syracuseStep 4723811 = 7085717) B7085717
theorem B2159731 : Blo 1399519 2159731 := bstep (se 1 (by rfl) ⟨1619798, by rfl⟩ : syracuseStep 2159731 = 3239597) B3239597
theorem B2364545 : Blo 1399519 2364545 := bstep (se 2 (by rfl) ⟨886704, by rfl⟩ : syracuseStep 2364545 = 1773409) B1773409
theorem B3544195 : Blo 1399519 3544195 := bstep (se 1 (by rfl) ⟨2658146, by rfl⟩ : syracuseStep 3544195 = 5316293) B5316293
theorem B3151025 : Blo 1399519 3151025 := bstep (se 2 (by rfl) ⟨1181634, by rfl⟩ : syracuseStep 3151025 = 2363269) B2363269
theorem B17953973 : Blo 1399519 17953973 := bstep (se 5 (by rfl) ⟨841592, by rfl⟩ : syracuseStep 17953973 = 1683185) B1683185
theorem B4854979 : Blo 1399519 4854979 := bstep (se 1 (by rfl) ⟨3641234, by rfl⟩ : syracuseStep 4854979 = 7282469) B7282469
theorem B3151043 : Blo 1399519 3151043 := bstep (se 1 (by rfl) ⟨2363282, by rfl⟩ : syracuseStep 3151043 = 4726565) B4726565
theorem B2364673 : Blo 1399519 2364673 := bstep (se 2 (by rfl) ⟨886752, by rfl⟩ : syracuseStep 2364673 = 1773505) B1773505
theorem B3544337 : Blo 1399519 3544337 := bstep (se 2 (by rfl) ⟨1329126, by rfl⟩ : syracuseStep 3544337 = 2658253) B2658253
theorem B2364707 : Blo 1399519 2364707 := bstep (se 1 (by rfl) ⟨1773530, by rfl⟩ : syracuseStep 2364707 = 3547061) B3547061
theorem B3986765 : Blo 1399519 3986765 := bstep (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) B1495037
theorem B4724081 : Blo 1399519 4724081 := bstep (se 2 (by rfl) ⟨1771530, by rfl⟩ : syracuseStep 4724081 = 3543061) B3543061
theorem B3986833 : Blo 1399519 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B2364835 : Blo 1399519 2364835 := bstep (se 1 (by rfl) ⟨1773626, by rfl⟩ : syracuseStep 2364835 = 3547253) B3547253
theorem B6387121 : Blo 1399519 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B3151313 : Blo 1399519 3151313 := bstep (se 2 (by rfl) ⟨1181742, by rfl⟩ : syracuseStep 3151313 = 2363485) B2363485
theorem B6911459 : Blo 1399519 6911459 := bstep (se 1 (by rfl) ⟨5183594, by rfl⟩ : syracuseStep 6911459 = 10367189) B10367189
theorem B3151331 : Blo 1399519 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B2364977 : Blo 1399519 2364977 := bstep (se 2 (by rfl) ⟨886866, by rfl⟩ : syracuseStep 2364977 = 1773733) B1773733
theorem B10237553 : Blo 1399519 10237553 := bstep (se 2 (by rfl) ⟨3839082, by rfl⟩ : syracuseStep 10237553 = 7678165) B7678165
theorem B3987107 : Blo 1399519 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B34059973 : Blo 1399519 34059973 := bstep (se 4 (by rfl) ⟨3193122, by rfl⟩ : syracuseStep 34059973 = 6386245) B6386245
theorem B3151601 : Blo 1399519 3151601 := bstep (se 2 (by rfl) ⟨1181850, by rfl⟩ : syracuseStep 3151601 = 2363701) B2363701
theorem B3151619 : Blo 1399519 3151619 := bstep (se 1 (by rfl) ⟨2363714, by rfl⟩ : syracuseStep 3151619 = 4727429) B4727429
theorem B2021203 : Blo 1399519 2021203 := bstep (se 1 (by rfl) ⟨1515902, by rfl⟩ : syracuseStep 2021203 = 3031805) B3031805
theorem B18683747 : Blo 1399519 18683747 := bstep (se 1 (by rfl) ⟨14012810, by rfl⟩ : syracuseStep 18683747 = 28025621) B28025621
theorem B4724621 : Blo 1399519 4724621 := bstep (se 3 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 4724621 = 1771733) B1771733
theorem B2840465 : Blo 1399519 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B2660273 : Blo 1399519 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B4724675 : Blo 1399519 4724675 := bstep (se 1 (by rfl) ⟨3543506, by rfl⟩ : syracuseStep 4724675 = 7087013) B7087013
theorem B5314531 : Blo 1399519 5314531 := bstep (se 1 (by rfl) ⟨3985898, by rfl⟩ : syracuseStep 5314531 = 7971797) B7971797
theorem B3151889 : Blo 1399519 3151889 := bstep (se 2 (by rfl) ⟨1181958, by rfl⟩ : syracuseStep 3151889 = 2363917) B2363917
theorem B3151907 : Blo 1399519 3151907 := bstep (se 1 (by rfl) ⟨2363930, by rfl⟩ : syracuseStep 3151907 = 4727861) B4727861
theorem B1439843 : Blo 1399519 1439843 := bstep (se 1 (by rfl) ⟨1079882, by rfl⟩ : syracuseStep 1439843 = 2159765) B2159765
theorem B4724945 : Blo 1399519 4724945 := bstep (se 2 (by rfl) ⟨1771854, by rfl⟩ : syracuseStep 4724945 = 3543709) B3543709
theorem B3545329 : Blo 1399519 3545329 := bstep (se 2 (by rfl) ⟨1329498, by rfl⟩ : syracuseStep 3545329 = 2658997) B2658997
theorem B3152177 : Blo 1399519 3152177 := bstep (se 2 (by rfl) ⟨1182066, by rfl⟩ : syracuseStep 3152177 = 2364133) B2364133
theorem B2242883 : Blo 1399519 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B3152195 : Blo 1399519 3152195 := bstep (se 1 (by rfl) ⟨2364146, by rfl⟩ : syracuseStep 3152195 = 4728293) B4728293
theorem B3987949 : Blo 1399519 3987949 := bstep (se 3 (by rfl) ⟨747740, by rfl⟩ : syracuseStep 3987949 = 1495481) B1495481
theorem B17258993 : Blo 1399519 17258993 := bstep (se 2 (by rfl) ⟨6472122, by rfl⟩ : syracuseStep 17258993 = 12944245) B12944245
theorem B3545603 : Blo 1399519 3545603 := bstep (se 1 (by rfl) ⟨2659202, by rfl⟩ : syracuseStep 3545603 = 5318405) B5318405
theorem B3193361 : Blo 1399519 3193361 := bstep (se 2 (by rfl) ⟨1197510, by rfl⟩ : syracuseStep 3193361 = 2395021) B2395021
theorem B2128403 : Blo 1399519 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B3152465 : Blo 1399519 3152465 := bstep (se 2 (by rfl) ⟨1182174, by rfl⟩ : syracuseStep 3152465 = 2364349) B2364349
theorem B3152483 : Blo 1399519 3152483 := bstep (se 1 (by rfl) ⟨2364362, by rfl⟩ : syracuseStep 3152483 = 4728725) B4728725
theorem B3594883 : Blo 1399519 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B3988109 : Blo 1399519 3988109 := bstep (se 3 (by rfl) ⟨747770, by rfl⟩ : syracuseStep 3988109 = 1495541) B1495541
theorem B3545795 : Blo 1399519 3545795 := bstep (se 1 (by rfl) ⟨2659346, by rfl⟩ : syracuseStep 3545795 = 5318693) B5318693
theorem B1399523 : Blo 1399519 1399523 := bstep (se 1 (by rfl) ⟨1049642, by rfl⟩ : syracuseStep 1399523 = 2099285) B2099285
theorem B4725485 : Blo 1399519 4725485 := bstep (se 3 (by rfl) ⟨886028, by rfl⟩ : syracuseStep 4725485 = 1772057) B1772057
theorem B1399539 : Blo 1399519 1399539 := bstep (se 1 (by rfl) ⟨1049654, by rfl⟩ : syracuseStep 1399539 = 2099309) B2099309
theorem B1399555 : Blo 1399519 1399555 := bstep (se 1 (by rfl) ⟨1049666, by rfl⟩ : syracuseStep 1399555 = 2099333) B2099333
theorem B1399571 : Blo 1399519 1399571 := bstep (se 1 (by rfl) ⟨1049678, by rfl⟩ : syracuseStep 1399571 = 2099357) B2099357
theorem B1399587 : Blo 1399519 1399587 := bstep (se 1 (by rfl) ⟨1049690, by rfl⟩ : syracuseStep 1399587 = 2099381) B2099381
theorem B4725539 : Blo 1399519 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B4258595 : Blo 1399519 4258595 := bstep (se 1 (by rfl) ⟨3193946, by rfl⟩ : syracuseStep 4258595 = 6387893) B6387893
theorem B1399603 : Blo 1399519 1399603 := bstep (se 1 (by rfl) ⟨1049702, by rfl⟩ : syracuseStep 1399603 = 2099405) B2099405
theorem B22698805 : Blo 1399519 22698805 := bstep (se 5 (by rfl) ⟨1064006, by rfl⟩ : syracuseStep 22698805 = 2128013) B2128013
theorem B1399619 : Blo 1399519 1399619 := bstep (se 1 (by rfl) ⟨1049714, by rfl⟩ : syracuseStep 1399619 = 2099429) B2099429
theorem B3988291 : Blo 1399519 3988291 := bstep (se 1 (by rfl) ⟨2991218, by rfl⟩ : syracuseStep 3988291 = 5982437) B5982437
theorem B1399635 : Blo 1399519 1399635 := bstep (se 1 (by rfl) ⟨1049726, by rfl⟩ : syracuseStep 1399635 = 2099453) B2099453
theorem B1399651 : Blo 1399519 1399651 := bstep (se 1 (by rfl) ⟨1049738, by rfl⟩ : syracuseStep 1399651 = 2099477) B2099477
theorem B3152753 : Blo 1399519 3152753 := bstep (se 2 (by rfl) ⟨1182282, by rfl⟩ : syracuseStep 3152753 = 2364565) B2364565
theorem B1399667 : Blo 1399519 1399667 := bstep (se 1 (by rfl) ⟨1049750, by rfl⟩ : syracuseStep 1399667 = 2099501) B2099501
theorem B1399683 : Blo 1399519 1399683 := bstep (se 1 (by rfl) ⟨1049762, by rfl⟩ : syracuseStep 1399683 = 2099525) B2099525
theorem B3152771 : Blo 1399519 3152771 := bstep (se 1 (by rfl) ⟨2364578, by rfl⟩ : syracuseStep 3152771 = 4729157) B4729157
theorem B8969093 : Blo 1399519 8969093 := bstep (se 4 (by rfl) ⟨840852, by rfl⟩ : syracuseStep 8969093 = 1681705) B1681705
theorem B1399699 : Blo 1399519 1399699 := bstep (se 1 (by rfl) ⟨1049774, by rfl⟩ : syracuseStep 1399699 = 2099549) B2099549
theorem B1399715 : Blo 1399519 1399715 := bstep (se 1 (by rfl) ⟨1049786, by rfl⟩ : syracuseStep 1399715 = 2099573) B2099573
theorem B2522033 : Blo 1399519 2522033 := bstep (se 2 (by rfl) ⟨945762, by rfl⟩ : syracuseStep 2522033 = 1891525) B1891525
theorem B1399731 : Blo 1399519 1399731 := bstep (se 1 (by rfl) ⟨1049798, by rfl⟩ : syracuseStep 1399731 = 2099597) B2099597
theorem B7093169 : Blo 1399519 7093169 := bstep (se 2 (by rfl) ⟨2659938, by rfl⟩ : syracuseStep 7093169 = 5319877) B5319877
theorem B1399747 : Blo 1399519 1399747 := bstep (se 1 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 1399747 = 2099621) B2099621
theorem B1399763 : Blo 1399519 1399763 := bstep (se 1 (by rfl) ⟨1049822, by rfl⟩ : syracuseStep 1399763 = 2099645) B2099645
theorem B1399779 : Blo 1399519 1399779 := bstep (se 1 (by rfl) ⟨1049834, by rfl⟩ : syracuseStep 1399779 = 2099669) B2099669
theorem B2243555 : Blo 1399519 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B3783665 : Blo 1399519 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B1399795 : Blo 1399519 1399795 := bstep (se 1 (by rfl) ⟨1049846, by rfl⟩ : syracuseStep 1399795 = 2099693) B2099693
theorem B1399811 : Blo 1399519 1399811 := bstep (se 1 (by rfl) ⟨1049858, by rfl⟩ : syracuseStep 1399811 = 2099717) B2099717
theorem B7085069 : Blo 1399519 7085069 := bstep (se 3 (by rfl) ⟨1328450, by rfl⟩ : syracuseStep 7085069 = 2656901) B2656901
theorem B1399827 : Blo 1399519 1399827 := bstep (se 1 (by rfl) ⟨1049870, by rfl⟩ : syracuseStep 1399827 = 2099741) B2099741
theorem B1399843 : Blo 1399519 1399843 := bstep (se 1 (by rfl) ⟨1049882, by rfl⟩ : syracuseStep 1399843 = 2099765) B2099765
theorem B4725809 : Blo 1399519 4725809 := bstep (se 2 (by rfl) ⟨1772178, by rfl⟩ : syracuseStep 4725809 = 3544357) B3544357
theorem B1399859 : Blo 1399519 1399859 := bstep (se 1 (by rfl) ⟨1049894, by rfl⟩ : syracuseStep 1399859 = 2099789) B2099789
theorem B1399875 : Blo 1399519 1399875 := bstep (se 1 (by rfl) ⟨1049906, by rfl⟩ : syracuseStep 1399875 = 2099813) B2099813
theorem B1399891 : Blo 1399519 1399891 := bstep (se 1 (by rfl) ⟨1049918, by rfl⟩ : syracuseStep 1399891 = 2099837) B2099837
theorem B1399907 : Blo 1399519 1399907 := bstep (se 1 (by rfl) ⟨1049930, by rfl⟩ : syracuseStep 1399907 = 2099861) B2099861
theorem B10640483 : Blo 1399519 10640483 := bstep (se 1 (by rfl) ⟨7980362, by rfl⟩ : syracuseStep 10640483 = 15960725) B15960725
theorem B1399923 : Blo 1399519 1399923 := bstep (se 1 (by rfl) ⟨1049942, by rfl⟩ : syracuseStep 1399923 = 2099885) B2099885
theorem B1399939 : Blo 1399519 1399939 := bstep (se 1 (by rfl) ⟨1049954, by rfl⟩ : syracuseStep 1399939 = 2099909) B2099909
theorem B3153041 : Blo 1399519 3153041 := bstep (se 2 (by rfl) ⟨1182390, by rfl⟩ : syracuseStep 3153041 = 2364781) B2364781
theorem B1399955 : Blo 1399519 1399955 := bstep (se 1 (by rfl) ⟨1049966, by rfl⟩ : syracuseStep 1399955 = 2099933) B2099933
theorem B2989219 : Blo 1399519 2989219 := bstep (se 1 (by rfl) ⟨2241914, by rfl⟩ : syracuseStep 2989219 = 4483829) B4483829
theorem B1399971 : Blo 1399519 1399971 := bstep (se 1 (by rfl) ⟨1049978, by rfl⟩ : syracuseStep 1399971 = 2099957) B2099957
theorem B3153059 : Blo 1399519 3153059 := bstep (se 1 (by rfl) ⟨2364794, by rfl⟩ : syracuseStep 3153059 = 4729589) B4729589
theorem B1399987 : Blo 1399519 1399987 := bstep (se 1 (by rfl) ⟨1049990, by rfl⟩ : syracuseStep 1399987 = 2099981) B2099981
theorem B1400003 : Blo 1399519 1400003 := bstep (se 1 (by rfl) ⟨1050002, by rfl⟩ : syracuseStep 1400003 = 2100005) B2100005
theorem B1400019 : Blo 1399519 1400019 := bstep (se 1 (by rfl) ⟨1050014, by rfl⟩ : syracuseStep 1400019 = 2100029) B2100029
theorem B1400035 : Blo 1399519 1400035 := bstep (se 1 (by rfl) ⟨1050026, by rfl⟩ : syracuseStep 1400035 = 2100053) B2100053
theorem B1400051 : Blo 1399519 1400051 := bstep (se 1 (by rfl) ⟨1050038, by rfl⟩ : syracuseStep 1400051 = 2100077) B2100077
theorem B1400067 : Blo 1399519 1400067 := bstep (se 1 (by rfl) ⟨1050050, by rfl⟩ : syracuseStep 1400067 = 2100101) B2100101
theorem B2243857 : Blo 1399519 2243857 := bstep (se 2 (by rfl) ⟨841446, by rfl⟩ : syracuseStep 2243857 = 1682893) B1682893
theorem B1400083 : Blo 1399519 1400083 := bstep (se 1 (by rfl) ⟨1050062, by rfl⟩ : syracuseStep 1400083 = 2100125) B2100125
theorem B1400099 : Blo 1399519 1400099 := bstep (se 1 (by rfl) ⟨1050074, by rfl⟩ : syracuseStep 1400099 = 2100149) B2100149
theorem B1400115 : Blo 1399519 1400115 := bstep (se 1 (by rfl) ⟨1050086, by rfl⟩ : syracuseStep 1400115 = 2100173) B2100173
theorem B1400131 : Blo 1399519 1400131 := bstep (se 1 (by rfl) ⟨1050098, by rfl⟩ : syracuseStep 1400131 = 2100197) B2100197
theorem B9100613 : Blo 1399519 9100613 := bstep (se 4 (by rfl) ⟨853182, by rfl⟩ : syracuseStep 9100613 = 1706365) B1706365
theorem B1400147 : Blo 1399519 1400147 := bstep (se 1 (by rfl) ⟨1050110, by rfl⟩ : syracuseStep 1400147 = 2100221) B2100221
theorem B1400163 : Blo 1399519 1400163 := bstep (se 1 (by rfl) ⟨1050122, by rfl⟩ : syracuseStep 1400163 = 2100245) B2100245
theorem B17939825 : Blo 1399519 17939825 := bstep (se 2 (by rfl) ⟨6727434, by rfl⟩ : syracuseStep 17939825 = 13454869) B13454869
theorem B1400179 : Blo 1399519 1400179 := bstep (se 1 (by rfl) ⟨1050134, by rfl⟩ : syracuseStep 1400179 = 2100269) B2100269
theorem B1400195 : Blo 1399519 1400195 := bstep (se 1 (by rfl) ⟨1050146, by rfl⟩ : syracuseStep 1400195 = 2100293) B2100293
theorem B1400211 : Blo 1399519 1400211 := bstep (se 1 (by rfl) ⟨1050158, by rfl⟩ : syracuseStep 1400211 = 2100317) B2100317
theorem B1400227 : Blo 1399519 1400227 := bstep (se 1 (by rfl) ⟨1050170, by rfl⟩ : syracuseStep 1400227 = 2100341) B2100341
theorem B3153329 : Blo 1399519 3153329 := bstep (se 2 (by rfl) ⟨1182498, by rfl⟩ : syracuseStep 3153329 = 2364997) B2364997
theorem B1400243 : Blo 1399519 1400243 := bstep (se 1 (by rfl) ⟨1050182, by rfl⟩ : syracuseStep 1400243 = 2100365) B2100365
theorem B1400259 : Blo 1399519 1400259 := bstep (se 1 (by rfl) ⟨1050194, by rfl⟩ : syracuseStep 1400259 = 2100389) B2100389
theorem B3153347 : Blo 1399519 3153347 := bstep (se 1 (by rfl) ⟨2365010, by rfl⟩ : syracuseStep 3153347 = 4730021) B4730021
theorem B1400275 : Blo 1399519 1400275 := bstep (se 1 (by rfl) ⟨1050206, by rfl⟩ : syracuseStep 1400275 = 2100413) B2100413
theorem B1400291 : Blo 1399519 1400291 := bstep (se 1 (by rfl) ⟨1050218, by rfl⟩ : syracuseStep 1400291 = 2100437) B2100437
theorem B2244067 : Blo 1399519 2244067 := bstep (se 1 (by rfl) ⟨1683050, by rfl⟩ : syracuseStep 2244067 = 3366101) B3366101
theorem B4791793 : Blo 1399519 4791793 := bstep (se 2 (by rfl) ⟨1796922, by rfl⟩ : syracuseStep 4791793 = 3593845) B3593845
theorem B1400307 : Blo 1399519 1400307 := bstep (se 1 (by rfl) ⟨1050230, by rfl⟩ : syracuseStep 1400307 = 2100461) B2100461
theorem B1400323 : Blo 1399519 1400323 := bstep (se 1 (by rfl) ⟨1050242, by rfl⟩ : syracuseStep 1400323 = 2100485) B2100485
theorem B3784205 : Blo 1399519 3784205 := bstep (se 3 (by rfl) ⟨709538, by rfl⟩ : syracuseStep 3784205 = 1419077) B1419077
theorem B2244113 : Blo 1399519 2244113 := bstep (se 2 (by rfl) ⟨841542, by rfl⟩ : syracuseStep 2244113 = 1683085) B1683085
theorem B1400339 : Blo 1399519 1400339 := bstep (se 1 (by rfl) ⟨1050254, by rfl⟩ : syracuseStep 1400339 = 2100509) B2100509
theorem B1400355 : Blo 1399519 1400355 := bstep (se 1 (by rfl) ⟨1050266, by rfl⟩ : syracuseStep 1400355 = 2100533) B2100533
theorem B1400371 : Blo 1399519 1400371 := bstep (se 1 (by rfl) ⟨1050278, by rfl⟩ : syracuseStep 1400371 = 2100557) B2100557
theorem B1400387 : Blo 1399519 1400387 := bstep (se 1 (by rfl) ⟨1050290, by rfl⟩ : syracuseStep 1400387 = 2100581) B2100581
theorem B4726349 : Blo 1399519 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B1400403 : Blo 1399519 1400403 := bstep (se 1 (by rfl) ⟨1050302, by rfl⟩ : syracuseStep 1400403 = 2100605) B2100605
theorem B1400419 : Blo 1399519 1400419 := bstep (se 1 (by rfl) ⟨1050314, by rfl⟩ : syracuseStep 1400419 = 2100629) B2100629
theorem B3546737 : Blo 1399519 3546737 := bstep (se 2 (by rfl) ⟨1330026, by rfl⟩ : syracuseStep 3546737 = 2660053) B2660053
theorem B1400435 : Blo 1399519 1400435 := bstep (se 1 (by rfl) ⟨1050326, by rfl⟩ : syracuseStep 1400435 = 2100653) B2100653
theorem B4726403 : Blo 1399519 4726403 := bstep (se 1 (by rfl) ⟨3544802, by rfl⟩ : syracuseStep 4726403 = 7089605) B7089605
theorem B1400451 : Blo 1399519 1400451 := bstep (se 1 (by rfl) ⟨1050338, by rfl⟩ : syracuseStep 1400451 = 2100677) B2100677
theorem B1400467 : Blo 1399519 1400467 := bstep (se 1 (by rfl) ⟨1050350, by rfl⟩ : syracuseStep 1400467 = 2100701) B2100701
theorem B1400483 : Blo 1399519 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B3546787 : Blo 1399519 3546787 := bstep (se 1 (by rfl) ⟨2660090, by rfl⟩ : syracuseStep 3546787 = 5320181) B5320181
theorem B1400499 : Blo 1399519 1400499 := bstep (se 1 (by rfl) ⟨1050374, by rfl⟩ : syracuseStep 1400499 = 2100749) B2100749
theorem B1400515 : Blo 1399519 1400515 := bstep (se 1 (by rfl) ⟨1050386, by rfl⟩ : syracuseStep 1400515 = 2100773) B2100773
theorem B1400531 : Blo 1399519 1400531 := bstep (se 1 (by rfl) ⟨1050398, by rfl⟩ : syracuseStep 1400531 = 2100797) B2100797
theorem B1400547 : Blo 1399519 1400547 := bstep (se 1 (by rfl) ⟨1050410, by rfl⟩ : syracuseStep 1400547 = 2100821) B2100821
theorem B1400563 : Blo 1399519 1400563 := bstep (se 1 (by rfl) ⟨1050422, by rfl⟩ : syracuseStep 1400563 = 2100845) B2100845
theorem B1400579 : Blo 1399519 1400579 := bstep (se 1 (by rfl) ⟨1050434, by rfl⟩ : syracuseStep 1400579 = 2100869) B2100869
theorem B3366659 : Blo 1399519 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B1400595 : Blo 1399519 1400595 := bstep (se 1 (by rfl) ⟨1050446, by rfl⟩ : syracuseStep 1400595 = 2100893) B2100893
theorem B1400611 : Blo 1399519 1400611 := bstep (se 1 (by rfl) ⟨1050458, by rfl⟩ : syracuseStep 1400611 = 2100917) B2100917
theorem B3546929 : Blo 1399519 3546929 := bstep (se 2 (by rfl) ⟨1330098, by rfl⟩ : syracuseStep 3546929 = 2660197) B2660197
theorem B1400627 : Blo 1399519 1400627 := bstep (se 1 (by rfl) ⟨1050470, by rfl⟩ : syracuseStep 1400627 = 2100941) B2100941
theorem B1400643 : Blo 1399519 1400643 := bstep (se 1 (by rfl) ⟨1050482, by rfl⟩ : syracuseStep 1400643 = 2100965) B2100965
theorem B1400659 : Blo 1399519 1400659 := bstep (se 1 (by rfl) ⟨1050494, by rfl⟩ : syracuseStep 1400659 = 2100989) B2100989
theorem B1400675 : Blo 1399519 1400675 := bstep (se 1 (by rfl) ⟨1050506, by rfl⟩ : syracuseStep 1400675 = 2101013) B2101013
theorem B1400691 : Blo 1399519 1400691 := bstep (se 1 (by rfl) ⟨1050518, by rfl⟩ : syracuseStep 1400691 = 2101037) B2101037
theorem B1400707 : Blo 1399519 1400707 := bstep (se 1 (by rfl) ⟨1050530, by rfl⟩ : syracuseStep 1400707 = 2101061) B2101061
theorem B4726673 : Blo 1399519 4726673 := bstep (se 2 (by rfl) ⟨1772502, by rfl⟩ : syracuseStep 4726673 = 3545005) B3545005
theorem B1400723 : Blo 1399519 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B1400739 : Blo 1399519 1400739 := bstep (se 1 (by rfl) ⟨1050554, by rfl⟩ : syracuseStep 1400739 = 2101109) B2101109
theorem B1400755 : Blo 1399519 1400755 := bstep (se 1 (by rfl) ⟨1050566, by rfl⟩ : syracuseStep 1400755 = 2101133) B2101133
theorem B1400771 : Blo 1399519 1400771 := bstep (se 1 (by rfl) ⟨1050578, by rfl⟩ : syracuseStep 1400771 = 2101157) B2101157
theorem B1400787 : Blo 1399519 1400787 := bstep (se 1 (by rfl) ⟨1050590, by rfl⟩ : syracuseStep 1400787 = 2101181) B2101181
theorem B1400803 : Blo 1399519 1400803 := bstep (se 1 (by rfl) ⟨1050602, by rfl⟩ : syracuseStep 1400803 = 2101205) B2101205
theorem B1400819 : Blo 1399519 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B1400843 : Blo 1399519 1400843 := bstep (se 1 (by rfl) ⟨1050632, by rfl⟩ : syracuseStep 1400843 = 2101265) B2101265
theorem B1400855 : Blo 1399519 1400855 := bstep (se 1 (by rfl) ⟨1050641, by rfl⟩ : syracuseStep 1400855 = 2101283) B2101283
theorem B1400875 : Blo 1399519 1400875 := bstep (se 1 (by rfl) ⟨1050656, by rfl⟩ : syracuseStep 1400875 = 2101313) B2101313
theorem B4726835 : Blo 1399519 4726835 := bstep (se 1 (by rfl) ⟨3545126, by rfl⟩ : syracuseStep 4726835 = 7090253) B7090253
theorem B1400887 : Blo 1399519 1400887 := bstep (se 1 (by rfl) ⟨1050665, by rfl⟩ : syracuseStep 1400887 = 2101331) B2101331
theorem B1400907 : Blo 1399519 1400907 := bstep (se 1 (by rfl) ⟨1050680, by rfl⟩ : syracuseStep 1400907 = 2101361) B2101361
theorem B1400919 : Blo 1399519 1400919 := bstep (se 1 (by rfl) ⟨1050689, by rfl⟩ : syracuseStep 1400919 = 2101379) B2101379
theorem B8978525 : Blo 1399519 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B1400939 : Blo 1399519 1400939 := bstep (se 1 (by rfl) ⟨1050704, by rfl⟩ : syracuseStep 1400939 = 2101409) B2101409
theorem B1400951 : Blo 1399519 1400951 := bstep (se 1 (by rfl) ⟨1050713, by rfl⟩ : syracuseStep 1400951 = 2101427) B2101427
theorem B1400971 : Blo 1399519 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B1400983 : Blo 1399519 1400983 := bstep (se 1 (by rfl) ⟨1050737, by rfl⟩ : syracuseStep 1400983 = 2101475) B2101475
theorem B1401003 : Blo 1399519 1401003 := bstep (se 1 (by rfl) ⟨1050752, by rfl⟩ : syracuseStep 1401003 = 2101505) B2101505
theorem B1401015 : Blo 1399519 1401015 := bstep (se 1 (by rfl) ⟨1050761, by rfl⟩ : syracuseStep 1401015 = 2101523) B2101523
theorem B1401035 : Blo 1399519 1401035 := bstep (se 1 (by rfl) ⟨1050776, by rfl⟩ : syracuseStep 1401035 = 2101553) B2101553
theorem B1401047 : Blo 1399519 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B1401067 : Blo 1399519 1401067 := bstep (se 1 (by rfl) ⟨1050800, by rfl⟩ : syracuseStep 1401067 = 2101601) B2101601
theorem B1401079 : Blo 1399519 1401079 := bstep (se 1 (by rfl) ⟨1050809, by rfl⟩ : syracuseStep 1401079 = 2101619) B2101619
theorem B1401099 : Blo 1399519 1401099 := bstep (se 1 (by rfl) ⟨1050824, by rfl⟩ : syracuseStep 1401099 = 2101649) B2101649
theorem B1401111 : Blo 1399519 1401111 := bstep (se 1 (by rfl) ⟨1050833, by rfl⟩ : syracuseStep 1401111 = 2101667) B2101667
theorem B3547415 : Blo 1399519 3547415 := bstep (se 1 (by rfl) ⟨2660561, by rfl⟩ : syracuseStep 3547415 = 5321123) B5321123
theorem B1401131 : Blo 1399519 1401131 := bstep (se 1 (by rfl) ⟨1050848, by rfl⟩ : syracuseStep 1401131 = 2101697) B2101697
theorem B1401143 : Blo 1399519 1401143 := bstep (se 1 (by rfl) ⟨1050857, by rfl⟩ : syracuseStep 1401143 = 2101715) B2101715
theorem B4727105 : Blo 1399519 4727105 := bstep (se 2 (by rfl) ⟨1772664, by rfl⟩ : syracuseStep 4727105 = 3545329) B3545329
theorem B9716033 : Blo 1399519 9716033 := bstep (se 2 (by rfl) ⟨3643512, by rfl⟩ : syracuseStep 9716033 = 7287025) B7287025
theorem B1401163 : Blo 1399519 1401163 := bstep (se 1 (by rfl) ⟨1050872, by rfl⟩ : syracuseStep 1401163 = 2101745) B2101745
theorem B1401175 : Blo 1399519 1401175 := bstep (se 1 (by rfl) ⟨1050881, by rfl⟩ : syracuseStep 1401175 = 2101763) B2101763
theorem B1401195 : Blo 1399519 1401195 := bstep (se 1 (by rfl) ⟨1050896, by rfl⟩ : syracuseStep 1401195 = 2101793) B2101793
theorem B1401207 : Blo 1399519 1401207 := bstep (se 1 (by rfl) ⟨1050905, by rfl⟩ : syracuseStep 1401207 = 2101811) B2101811
theorem B1401227 : Blo 1399519 1401227 := bstep (se 1 (by rfl) ⟨1050920, by rfl⟩ : syracuseStep 1401227 = 2101841) B2101841
theorem B1401239 : Blo 1399519 1401239 := bstep (se 1 (by rfl) ⟨1050929, by rfl⟩ : syracuseStep 1401239 = 2101859) B2101859
theorem B1401259 : Blo 1399519 1401259 := bstep (se 1 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 1401259 = 2101889) B2101889
theorem B1401271 : Blo 1399519 1401271 := bstep (se 1 (by rfl) ⟨1050953, by rfl⟩ : syracuseStep 1401271 = 2101907) B2101907
theorem B5046731 : Blo 1399519 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B1401291 : Blo 1399519 1401291 := bstep (se 1 (by rfl) ⟨1050968, by rfl⟩ : syracuseStep 1401291 = 2101937) B2101937
theorem B1401303 : Blo 1399519 1401303 := bstep (se 1 (by rfl) ⟨1050977, by rfl⟩ : syracuseStep 1401303 = 2101955) B2101955
theorem B1401323 : Blo 1399519 1401323 := bstep (se 1 (by rfl) ⟨1050992, by rfl⟩ : syracuseStep 1401323 = 2101985) B2101985
theorem B1401335 : Blo 1399519 1401335 := bstep (se 1 (by rfl) ⟨1051001, by rfl⟩ : syracuseStep 1401335 = 2102003) B2102003
theorem B1401355 : Blo 1399519 1401355 := bstep (se 1 (by rfl) ⟨1051016, by rfl⟩ : syracuseStep 1401355 = 2102033) B2102033
theorem B1401367 : Blo 1399519 1401367 := bstep (se 1 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 1401367 = 2102051) B2102051
theorem B1401387 : Blo 1399519 1401387 := bstep (se 1 (by rfl) ⟨1051040, by rfl⟩ : syracuseStep 1401387 = 2102081) B2102081
theorem B1401399 : Blo 1399519 1401399 := bstep (se 1 (by rfl) ⟨1051049, by rfl⟩ : syracuseStep 1401399 = 2102099) B2102099
theorem B1401419 : Blo 1399519 1401419 := bstep (se 1 (by rfl) ⟨1051064, by rfl⟩ : syracuseStep 1401419 = 2102129) B2102129
theorem B1892951 : Blo 1399519 1892951 := bstep (se 1 (by rfl) ⟨1419713, by rfl⟩ : syracuseStep 1892951 = 2839427) B2839427
theorem B1401431 : Blo 1399519 1401431 := bstep (se 1 (by rfl) ⟨1051073, by rfl⟩ : syracuseStep 1401431 = 2102147) B2102147
theorem B1401451 : Blo 1399519 1401451 := bstep (se 1 (by rfl) ⟨1051088, by rfl⟩ : syracuseStep 1401451 = 2102177) B2102177
theorem B1401463 : Blo 1399519 1401463 := bstep (se 1 (by rfl) ⟨1051097, by rfl⟩ : syracuseStep 1401463 = 2102195) B2102195
theorem B1401483 : Blo 1399519 1401483 := bstep (se 1 (by rfl) ⟨1051112, by rfl⟩ : syracuseStep 1401483 = 2102225) B2102225
theorem B5317265 : Blo 1399519 5317265 := bstep (se 2 (by rfl) ⟨1993974, by rfl⟩ : syracuseStep 5317265 = 3987949) B3987949
theorem B7971479 : Blo 1399519 7971479 := bstep (se 1 (by rfl) ⟨5978609, by rfl⟩ : syracuseStep 7971479 = 11957219) B11957219
theorem B1401495 : Blo 1399519 1401495 := bstep (se 1 (by rfl) ⟨1051121, by rfl⟩ : syracuseStep 1401495 = 2102243) B2102243
theorem B1401515 : Blo 1399519 1401515 := bstep (se 1 (by rfl) ⟨1051136, by rfl⟩ : syracuseStep 1401515 = 2102273) B2102273
theorem B1598167 : Blo 1399519 1598167 := bstep (se 1 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 1598167 = 2397251) B2397251
theorem B5391107 : Blo 1399519 5391107 := bstep (se 1 (by rfl) ⟨4043330, by rfl⟩ : syracuseStep 5391107 = 8086661) B8086661
theorem B11969315 : Blo 1399519 11969315 := bstep (se 1 (by rfl) ⟨8976986, by rfl⟩ : syracuseStep 11969315 = 17953973) B17953973
theorem B3031873 : Blo 1399519 3031873 := bstep (se 2 (by rfl) ⟨1136952, by rfl⟩ : syracuseStep 3031873 = 2273905) B2273905
theorem B4793177 : Blo 1399519 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B4727645 : Blo 1399519 4727645 := bstep (se 3 (by rfl) ⟨886433, by rfl⟩ : syracuseStep 4727645 = 1772867) B1772867
theorem B6825035 : Blo 1399519 6825035 := bstep (se 1 (by rfl) ⟨5118776, by rfl⟩ : syracuseStep 6825035 = 10237553) B10237553
theorem B5317721 : Blo 1399519 5317721 := bstep (se 2 (by rfl) ⟨1994145, by rfl⟩ : syracuseStep 5317721 = 3988291) B3988291
theorem B4318297 : Blo 1399519 4318297 := bstep (se 2 (by rfl) ⟨1619361, by rfl⟩ : syracuseStep 4318297 = 3238723) B3238723
theorem B5981377 : Blo 1399519 5981377 := bstep (se 2 (by rfl) ⟨2243016, by rfl⟩ : syracuseStep 5981377 = 4486033) B4486033
theorem B2524403 : Blo 1399519 2524403 := bstep (se 1 (by rfl) ⟨1893302, by rfl⟩ : syracuseStep 2524403 = 3786605) B3786605
theorem B5317933 : Blo 1399519 5317933 := bstep (se 3 (by rfl) ⟨997112, by rfl⟩ : syracuseStep 5317933 = 1994225) B1994225
theorem B4261195 : Blo 1399519 4261195 := bstep (se 1 (by rfl) ⟨3195896, by rfl⟩ : syracuseStep 4261195 = 6391793) B6391793
theorem B6817117 : Blo 1399519 6817117 := bstep (se 3 (by rfl) ⟨1278209, by rfl⟩ : syracuseStep 6817117 = 2556419) B2556419
theorem B3786077 : Blo 1399519 3786077 := bstep (se 3 (by rfl) ⟨709889, by rfl⟩ : syracuseStep 3786077 = 1419779) B1419779
theorem B7087661 : Blo 1399519 7087661 := bstep (se 3 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 7087661 = 2657873) B2657873
theorem B6817355 : Blo 1399519 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B6473305 : Blo 1399519 6473305 := bstep (se 2 (by rfl) ⟨2427489, by rfl⟩ : syracuseStep 6473305 = 4854979) B4854979
theorem B5318237 : Blo 1399519 5318237 := bstep (se 3 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 5318237 = 1994339) B1994339
theorem B10929815 : Blo 1399519 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B2991809 : Blo 1399519 2991809 := bstep (se 2 (by rfl) ⟨1121928, by rfl⟩ : syracuseStep 2991809 = 2243857) B2243857
theorem B1574635 : Blo 1399519 1574635 := bstep (se 1 (by rfl) ⟨1180976, by rfl⟩ : syracuseStep 1574635 = 2361953) B2361953
theorem B1574743 : Blo 1399519 1574743 := bstep (se 1 (by rfl) ⟨1181057, by rfl⟩ : syracuseStep 1574743 = 2362115) B2362115
theorem B2189209 : Blo 1399519 2189209 := bstep (se 2 (by rfl) ⟨820953, by rfl⟩ : syracuseStep 2189209 = 1641907) B1641907
theorem B1681355 : Blo 1399519 1681355 := bstep (se 1 (by rfl) ⟨1261016, by rfl⟩ : syracuseStep 1681355 = 2522033) B2522033
theorem B4728779 : Blo 1399519 4728779 := bstep (se 1 (by rfl) ⟨3546584, by rfl⟩ : syracuseStep 4728779 = 7093169) B7093169
theorem B1574923 : Blo 1399519 1574923 := bstep (se 1 (by rfl) ⟨1181192, by rfl⟩ : syracuseStep 1574923 = 2362385) B2362385
theorem B11520035 : Blo 1399519 11520035 := bstep (se 1 (by rfl) ⟨8640026, by rfl⟩ : syracuseStep 11520035 = 17280053) B17280053
theorem B1575031 : Blo 1399519 1575031 := bstep (se 1 (by rfl) ⟨1181273, by rfl⟩ : syracuseStep 1575031 = 2362547) B2362547
theorem B2099339 : Blo 1399519 2099339 := bstep (se 1 (by rfl) ⟨1574504, by rfl⟩ : syracuseStep 2099339 = 3149009) B3149009
theorem B2099351 : Blo 1399519 2099351 := bstep (se 1 (by rfl) ⟨1574513, by rfl⟩ : syracuseStep 2099351 = 3149027) B3149027
theorem B1771723 : Blo 1399519 1771723 := bstep (se 1 (by rfl) ⟨1328792, by rfl⟩ : syracuseStep 1771723 = 2657585) B2657585
theorem B2099417 : Blo 1399519 2099417 := bstep (se 2 (by rfl) ⟨787281, by rfl⟩ : syracuseStep 2099417 = 1574563) B1574563
theorem B4729049 : Blo 1399519 4729049 := bstep (se 2 (by rfl) ⟨1773393, by rfl⟩ : syracuseStep 4729049 = 3546787) B3546787
theorem B20187377 : Blo 1399519 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B1575211 : Blo 1399519 1575211 := bstep (se 1 (by rfl) ⟨1181408, by rfl⟩ : syracuseStep 1575211 = 2362817) B2362817
theorem B27298093 : Blo 1399519 27298093 := bstep (se 3 (by rfl) ⟨5118392, by rfl⟩ : syracuseStep 27298093 = 10236785) B10236785
theorem B2099531 : Blo 1399519 2099531 := bstep (se 1 (by rfl) ⟨1574648, by rfl⟩ : syracuseStep 2099531 = 3149297) B3149297
theorem B2099543 : Blo 1399519 2099543 := bstep (se 1 (by rfl) ⟨1574657, by rfl⟩ : syracuseStep 2099543 = 3149315) B3149315
theorem B1575319 : Blo 1399519 1575319 := bstep (se 1 (by rfl) ⟨1181489, by rfl⟩ : syracuseStep 1575319 = 2362979) B2362979
theorem B2099609 : Blo 1399519 2099609 := bstep (se 2 (by rfl) ⟨787353, by rfl⟩ : syracuseStep 2099609 = 1574707) B1574707
theorem B1993177 : Blo 1399519 1993177 := bstep (se 2 (by rfl) ⟨747441, by rfl⟩ : syracuseStep 1993177 = 1494883) B1494883
theorem B2099723 : Blo 1399519 2099723 := bstep (se 1 (by rfl) ⟨1574792, by rfl⟩ : syracuseStep 2099723 = 3149585) B3149585
theorem B2099735 : Blo 1399519 2099735 := bstep (se 1 (by rfl) ⟨1574801, by rfl⟩ : syracuseStep 2099735 = 3149603) B3149603
theorem B1575499 : Blo 1399519 1575499 := bstep (se 1 (by rfl) ⟨1181624, by rfl⟩ : syracuseStep 1575499 = 2363249) B2363249
theorem B2099801 : Blo 1399519 2099801 := bstep (se 2 (by rfl) ⟨787425, by rfl⟩ : syracuseStep 2099801 = 1574851) B1574851
theorem B2362007 : Blo 1399519 2362007 := bstep (se 1 (by rfl) ⟨1771505, by rfl⟩ : syracuseStep 2362007 = 3543011) B3543011
theorem B1575607 : Blo 1399519 1575607 := bstep (se 1 (by rfl) ⟨1181705, by rfl⟩ : syracuseStep 1575607 = 2363411) B2363411
theorem B2099915 : Blo 1399519 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B1400823 : Blo 1399519 1400823 := bstep (se 1 (by rfl) ⟨1050617, by rfl⟩ : syracuseStep 1400823 = 2101235) B2101235
theorem B2099927 : Blo 1399519 2099927 := bstep (se 1 (by rfl) ⟨1574945, by rfl⟩ : syracuseStep 2099927 = 3149891) B3149891
theorem B2362135 : Blo 1399519 2362135 := bstep (se 1 (by rfl) ⟨1771601, by rfl⟩ : syracuseStep 2362135 = 3543203) B3543203
theorem B2099993 : Blo 1399519 2099993 := bstep (se 2 (by rfl) ⟨787497, by rfl⟩ : syracuseStep 2099993 = 1574995) B1574995
theorem B2657099 : Blo 1399519 2657099 := bstep (se 1 (by rfl) ⟨1992824, by rfl⟩ : syracuseStep 2657099 = 3985649) B3985649
theorem B1575787 : Blo 1399519 1575787 := bstep (se 1 (by rfl) ⟨1181840, by rfl⟩ : syracuseStep 1575787 = 2363681) B2363681
theorem B2100107 : Blo 1399519 2100107 := bstep (se 1 (by rfl) ⟨1575080, by rfl⟩ : syracuseStep 2100107 = 3150161) B3150161
theorem B2100119 : Blo 1399519 2100119 := bstep (se 1 (by rfl) ⟨1575089, by rfl⟩ : syracuseStep 2100119 = 3150179) B3150179
theorem B4729751 : Blo 1399519 4729751 := bstep (se 1 (by rfl) ⟨3547313, by rfl⟩ : syracuseStep 4729751 = 7094627) B7094627
theorem B7982003 : Blo 1399519 7982003 := bstep (se 1 (by rfl) ⟨5986502, by rfl⟩ : syracuseStep 7982003 = 11973005) B11973005
theorem B1575895 : Blo 1399519 1575895 := bstep (se 1 (by rfl) ⟨1181921, by rfl⟩ : syracuseStep 1575895 = 2363843) B2363843
theorem B2100185 : Blo 1399519 2100185 := bstep (se 2 (by rfl) ⟨787569, by rfl⟩ : syracuseStep 2100185 = 1575139) B1575139
theorem B6728665 : Blo 1399519 6728665 := bstep (se 2 (by rfl) ⟨2523249, by rfl⟩ : syracuseStep 6728665 = 5046499) B5046499
theorem B2657281 : Blo 1399519 2657281 := bstep (se 2 (by rfl) ⟨996480, by rfl⟩ : syracuseStep 2657281 = 1992961) B1992961
theorem B7973963 : Blo 1399519 7973963 := bstep (se 1 (by rfl) ⟨5980472, by rfl⟩ : syracuseStep 7973963 = 11960945) B11960945
theorem B2100299 : Blo 1399519 2100299 := bstep (se 1 (by rfl) ⟨1575224, by rfl⟩ : syracuseStep 2100299 = 3150449) B3150449
theorem B1420363 : Blo 1399519 1420363 := bstep (se 1 (by rfl) ⟨1065272, by rfl⟩ : syracuseStep 1420363 = 2130545) B2130545
theorem B2100311 : Blo 1399519 2100311 := bstep (se 1 (by rfl) ⟨1575233, by rfl⟩ : syracuseStep 2100311 = 3150467) B3150467
theorem B1576075 : Blo 1399519 1576075 := bstep (se 1 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 1576075 = 2364113) B2364113
theorem B1772695 : Blo 1399519 1772695 := bstep (se 1 (by rfl) ⟨1329521, by rfl⟩ : syracuseStep 1772695 = 2659043) B2659043
theorem B2100377 : Blo 1399519 2100377 := bstep (se 2 (by rfl) ⟨787641, by rfl⟩ : syracuseStep 2100377 = 1575283) B1575283
theorem B2837683 : Blo 1399519 2837683 := bstep (se 1 (by rfl) ⟨2128262, by rfl⟩ : syracuseStep 2837683 = 4256525) B4256525
theorem B1576183 : Blo 1399519 1576183 := bstep (se 1 (by rfl) ⟨1182137, by rfl⟩ : syracuseStep 1576183 = 2364275) B2364275
theorem B2100491 : Blo 1399519 2100491 := bstep (se 1 (by rfl) ⟨1575368, by rfl⟩ : syracuseStep 2100491 = 3150737) B3150737
theorem B2100503 : Blo 1399519 2100503 := bstep (se 1 (by rfl) ⟨1575377, by rfl⟩ : syracuseStep 2100503 = 3150755) B3150755
theorem B3149081 : Blo 1399519 3149081 := bstep (se 2 (by rfl) ⟨1180905, by rfl⟩ : syracuseStep 3149081 = 2361811) B2361811
theorem B8523073 : Blo 1399519 8523073 := bstep (se 2 (by rfl) ⟨3196152, by rfl⟩ : syracuseStep 8523073 = 6392305) B6392305
theorem B5680459 : Blo 1399519 5680459 := bstep (se 1 (by rfl) ⟨4260344, by rfl⟩ : syracuseStep 5680459 = 8520689) B8520689
theorem B2657623 : Blo 1399519 2657623 := bstep (se 1 (by rfl) ⟨1993217, by rfl⟩ : syracuseStep 2657623 = 3986435) B3986435
theorem B2100569 : Blo 1399519 2100569 := bstep (se 2 (by rfl) ⟨787713, by rfl⟩ : syracuseStep 2100569 = 1575427) B1575427
theorem B3149171 : Blo 1399519 3149171 := bstep (se 1 (by rfl) ⟨2361878, by rfl⟩ : syracuseStep 3149171 = 4723757) B4723757
theorem B2362763 : Blo 1399519 2362763 := bstep (se 1 (by rfl) ⟨1772072, by rfl⟩ : syracuseStep 2362763 = 3544145) B3544145
theorem B2559371 : Blo 1399519 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B3149207 : Blo 1399519 3149207 := bstep (se 1 (by rfl) ⟨2361905, by rfl⟩ : syracuseStep 3149207 = 4723811) B4723811
theorem B1576363 : Blo 1399519 1576363 := bstep (se 1 (by rfl) ⟨1182272, by rfl⟩ : syracuseStep 1576363 = 2364545) B2364545
theorem B2100683 : Blo 1399519 2100683 := bstep (se 1 (by rfl) ⟨1575512, by rfl⟩ : syracuseStep 2100683 = 3151025) B3151025
theorem B2100695 : Blo 1399519 2100695 := bstep (se 1 (by rfl) ⟨1575521, by rfl⟩ : syracuseStep 2100695 = 3151043) B3151043
theorem B2362891 : Blo 1399519 2362891 := bstep (se 1 (by rfl) ⟨1772168, by rfl⟩ : syracuseStep 2362891 = 3544337) B3544337
theorem B1576471 : Blo 1399519 1576471 := bstep (se 1 (by rfl) ⟨1182353, by rfl⟩ : syracuseStep 1576471 = 2364707) B2364707
theorem B2100761 : Blo 1399519 2100761 := bstep (se 2 (by rfl) ⟨787785, by rfl⟩ : syracuseStep 2100761 = 1575571) B1575571
theorem B2657843 : Blo 1399519 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B6729281 : Blo 1399519 6729281 := bstep (se 2 (by rfl) ⟨2523480, by rfl⟩ : syracuseStep 6729281 = 5046961) B5046961
theorem B3149387 : Blo 1399519 3149387 := bstep (se 1 (by rfl) ⟨2362040, by rfl⟩ : syracuseStep 3149387 = 4724081) B4724081
theorem B3149441 : Blo 1399519 3149441 := bstep (se 2 (by rfl) ⟨1181040, by rfl⟩ : syracuseStep 3149441 = 2362081) B2362081
theorem B2100875 : Blo 1399519 2100875 := bstep (se 1 (by rfl) ⟨1575656, by rfl⟩ : syracuseStep 2100875 = 3151313) B3151313
theorem B4607639 : Blo 1399519 4607639 := bstep (se 1 (by rfl) ⟨3455729, by rfl⟩ : syracuseStep 4607639 = 6911459) B6911459
theorem B2100887 : Blo 1399519 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B2363033 : Blo 1399519 2363033 := bstep (se 2 (by rfl) ⟨886137, by rfl⟩ : syracuseStep 2363033 = 1772275) B1772275
theorem B1576651 : Blo 1399519 1576651 := bstep (se 1 (by rfl) ⟨1182488, by rfl⟩ : syracuseStep 1576651 = 2364977) B2364977
theorem B10088153 : Blo 1399519 10088153 := bstep (se 2 (by rfl) ⟨3783057, by rfl⟩ : syracuseStep 10088153 = 7566115) B7566115
theorem B2100953 : Blo 1399519 2100953 := bstep (se 2 (by rfl) ⟨787857, by rfl⟩ : syracuseStep 2100953 = 1575715) B1575715
theorem B30265073 : Blo 1399519 30265073 := bstep (se 2 (by rfl) ⟨11349402, by rfl⟩ : syracuseStep 30265073 = 22698805) B22698805
theorem B2658071 : Blo 1399519 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B2363161 : Blo 1399519 2363161 := bstep (se 2 (by rfl) ⟨886185, by rfl⟩ : syracuseStep 2363161 = 1772371) B1772371
theorem B3542849 : Blo 1399519 3542849 := bstep (se 2 (by rfl) ⟨1328568, by rfl⟩ : syracuseStep 3542849 = 2657137) B2657137
theorem B2101067 : Blo 1399519 2101067 := bstep (se 1 (by rfl) ⟨1575800, by rfl⟩ : syracuseStep 2101067 = 3151601) B3151601
theorem B2101079 : Blo 1399519 2101079 := bstep (se 1 (by rfl) ⟨1575809, by rfl⟩ : syracuseStep 2101079 = 3151619) B3151619
theorem B3149657 : Blo 1399519 3149657 := bstep (se 2 (by rfl) ⟨1181121, by rfl⟩ : syracuseStep 3149657 = 2362243) B2362243
theorem B2395993 : Blo 1399519 2395993 := bstep (se 2 (by rfl) ⟨898497, by rfl⟩ : syracuseStep 2395993 = 1796995) B1796995
theorem B1994635 : Blo 1399519 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B12455831 : Blo 1399519 12455831 := bstep (se 1 (by rfl) ⟨9341873, by rfl⟩ : syracuseStep 12455831 = 18683747) B18683747
theorem B1994647 : Blo 1399519 1994647 := bstep (se 1 (by rfl) ⟨1495985, by rfl⟩ : syracuseStep 1994647 = 2991971) B2991971
theorem B2101145 : Blo 1399519 2101145 := bstep (se 2 (by rfl) ⟨787929, by rfl⟩ : syracuseStep 2101145 = 1575859) B1575859
theorem B3149747 : Blo 1399519 3149747 := bstep (se 1 (by rfl) ⟨2362310, by rfl⟩ : syracuseStep 3149747 = 4724621) B4724621
theorem B1773515 : Blo 1399519 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B3149783 : Blo 1399519 3149783 := bstep (se 1 (by rfl) ⟨2362337, by rfl⟩ : syracuseStep 3149783 = 4724675) B4724675
theorem B2101259 : Blo 1399519 2101259 := bstep (se 1 (by rfl) ⟨1575944, by rfl⟩ : syracuseStep 2101259 = 3151889) B3151889
theorem B2101271 : Blo 1399519 2101271 := bstep (se 1 (by rfl) ⟨1575953, by rfl⟩ : syracuseStep 2101271 = 3151907) B3151907
theorem B2658329 : Blo 1399519 2658329 := bstep (se 2 (by rfl) ⟨996873, by rfl⟩ : syracuseStep 2658329 = 1993747) B1993747
theorem B12128321 : Blo 1399519 12128321 := bstep (se 2 (by rfl) ⟨4548120, by rfl⟩ : syracuseStep 12128321 = 9096241) B9096241
theorem B2101337 : Blo 1399519 2101337 := bstep (se 2 (by rfl) ⟨788001, by rfl⟩ : syracuseStep 2101337 = 1576003) B1576003
theorem B5320835 : Blo 1399519 5320835 := bstep (se 1 (by rfl) ⟨3990626, by rfl⟩ : syracuseStep 5320835 = 7981253) B7981253
theorem B3149963 : Blo 1399519 3149963 := bstep (se 1 (by rfl) ⟨2362472, by rfl⟩ : syracuseStep 3149963 = 4724945) B4724945
theorem B5320849 : Blo 1399519 5320849 := bstep (se 2 (by rfl) ⟨1995318, by rfl⟩ : syracuseStep 5320849 = 3990637) B3990637
theorem B2879641 : Blo 1399519 2879641 := bstep (se 2 (by rfl) ⟨1079865, by rfl⟩ : syracuseStep 2879641 = 2159731) B2159731
theorem B3150017 : Blo 1399519 3150017 := bstep (se 2 (by rfl) ⟨1181256, by rfl⟩ : syracuseStep 3150017 = 2362513) B2362513
theorem B2101451 : Blo 1399519 2101451 := bstep (se 1 (by rfl) ⟨1576088, by rfl⟩ : syracuseStep 2101451 = 3152177) B3152177
theorem B1495255 : Blo 1399519 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B2101463 : Blo 1399519 2101463 := bstep (se 1 (by rfl) ⟨1576097, by rfl⟩ : syracuseStep 2101463 = 3152195) B3152195
theorem B3985625 : Blo 1399519 3985625 := bstep (se 2 (by rfl) ⟨1494609, by rfl⟩ : syracuseStep 3985625 = 2989219) B2989219
theorem B2101529 : Blo 1399519 2101529 := bstep (se 2 (by rfl) ⟨788073, by rfl⟩ : syracuseStep 2101529 = 1576147) B1576147
theorem B6730049 : Blo 1399519 6730049 := bstep (se 2 (by rfl) ⟨2523768, by rfl⟩ : syracuseStep 6730049 = 5047537) B5047537
theorem B11505995 : Blo 1399519 11505995 := bstep (se 1 (by rfl) ⟨8629496, by rfl⟩ : syracuseStep 11505995 = 17258993) B17258993
theorem B2363735 : Blo 1399519 2363735 := bstep (se 1 (by rfl) ⟨1772801, by rfl⟩ : syracuseStep 2363735 = 3545603) B3545603
theorem B3543385 : Blo 1399519 3543385 := bstep (se 2 (by rfl) ⟨1328769, by rfl⟩ : syracuseStep 3543385 = 2657539) B2657539
theorem B4485469 : Blo 1399519 4485469 := bstep (se 3 (by rfl) ⟨841025, by rfl⟩ : syracuseStep 4485469 = 1682051) B1682051
theorem B2101643 : Blo 1399519 2101643 := bstep (se 1 (by rfl) ⟨1576232, by rfl⟩ : syracuseStep 2101643 = 3152465) B3152465
theorem B2101655 : Blo 1399519 2101655 := bstep (se 1 (by rfl) ⟨1576241, by rfl⟩ : syracuseStep 2101655 = 3152483) B3152483
theorem B3150233 : Blo 1399519 3150233 := bstep (se 2 (by rfl) ⟨1181337, by rfl⟩ : syracuseStep 3150233 = 2362675) B2362675
theorem B2658739 : Blo 1399519 2658739 := bstep (se 1 (by rfl) ⟨1994054, by rfl⟩ : syracuseStep 2658739 = 3988109) B3988109
theorem B5321153 : Blo 1399519 5321153 := bstep (se 2 (by rfl) ⟨1995432, by rfl⟩ : syracuseStep 5321153 = 3990865) B3990865
theorem B2363863 : Blo 1399519 2363863 := bstep (se 1 (by rfl) ⟨1772897, by rfl⟩ : syracuseStep 2363863 = 3545795) B3545795
theorem B2101721 : Blo 1399519 2101721 := bstep (se 2 (by rfl) ⟨788145, by rfl⟩ : syracuseStep 2101721 = 1576291) B1576291
theorem B3150323 : Blo 1399519 3150323 := bstep (se 1 (by rfl) ⟨2362742, by rfl⟩ : syracuseStep 3150323 = 4725485) B4725485
theorem B3150359 : Blo 1399519 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B2839063 : Blo 1399519 2839063 := bstep (se 1 (by rfl) ⟨2129297, by rfl⟩ : syracuseStep 2839063 = 4258595) B4258595
theorem B8516161 : Blo 1399519 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B2101835 : Blo 1399519 2101835 := bstep (se 1 (by rfl) ⟨1576376, by rfl⟩ : syracuseStep 2101835 = 3152753) B3152753
theorem B2101847 : Blo 1399519 2101847 := bstep (se 1 (by rfl) ⟨1576385, by rfl⟩ : syracuseStep 2101847 = 3152771) B3152771
theorem B1495703 : Blo 1399519 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B2101913 : Blo 1399519 2101913 := bstep (se 2 (by rfl) ⟨788217, by rfl⟩ : syracuseStep 2101913 = 1576435) B1576435
theorem B4723379 : Blo 1399519 4723379 := bstep (se 1 (by rfl) ⟨3542534, by rfl⟩ : syracuseStep 4723379 = 7085069) B7085069
theorem B3150539 : Blo 1399519 3150539 := bstep (se 1 (by rfl) ⟨2362904, by rfl⟩ : syracuseStep 3150539 = 4725809) B4725809
theorem B3150593 : Blo 1399519 3150593 := bstep (se 2 (by rfl) ⟨1181472, by rfl⟩ : syracuseStep 3150593 = 2362945) B2362945
theorem B2102027 : Blo 1399519 2102027 := bstep (se 1 (by rfl) ⟨1576520, by rfl⟩ : syracuseStep 2102027 = 3153041) B3153041
theorem B2102039 : Blo 1399519 2102039 := bstep (se 1 (by rfl) ⟨1576529, by rfl⟩ : syracuseStep 2102039 = 3153059) B3153059
theorem B2102105 : Blo 1399519 2102105 := bstep (se 2 (by rfl) ⟨788289, by rfl⟩ : syracuseStep 2102105 = 1576579) B1576579
theorem B6067075 : Blo 1399519 6067075 := bstep (se 1 (by rfl) ⟨4550306, by rfl⟩ : syracuseStep 6067075 = 9100613) B9100613
theorem B2659225 : Blo 1399519 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B45413297 : Blo 1399519 45413297 := bstep (se 2 (by rfl) ⟨17029986, by rfl⟩ : syracuseStep 45413297 = 34059973) B34059973
theorem B10097585 : Blo 1399519 10097585 := bstep (se 2 (by rfl) ⟨3786594, by rfl⟩ : syracuseStep 10097585 = 7573189) B7573189
theorem B4723649 : Blo 1399519 4723649 := bstep (se 2 (by rfl) ⟨1771368, by rfl⟩ : syracuseStep 4723649 = 3542737) B3542737
theorem B2102219 : Blo 1399519 2102219 := bstep (se 1 (by rfl) ⟨1576664, by rfl⟩ : syracuseStep 2102219 = 3153329) B3153329
theorem B2102231 : Blo 1399519 2102231 := bstep (se 1 (by rfl) ⟨1576673, by rfl⟩ : syracuseStep 2102231 = 3153347) B3153347
theorem B3150809 : Blo 1399519 3150809 := bstep (se 2 (by rfl) ⟨1181553, by rfl⟩ : syracuseStep 3150809 = 2363107) B2363107
theorem B1496075 : Blo 1399519 1496075 := bstep (se 1 (by rfl) ⟨1122056, by rfl⟩ : syracuseStep 1496075 = 2244113) B2244113
theorem B7574573 : Blo 1399519 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B3150899 : Blo 1399519 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B10097729 : Blo 1399519 10097729 := bstep (se 2 (by rfl) ⟨3786648, by rfl⟩ : syracuseStep 10097729 = 7573297) B7573297
theorem B2364491 : Blo 1399519 2364491 := bstep (se 1 (by rfl) ⟨1773368, by rfl⟩ : syracuseStep 2364491 = 3546737) B3546737
theorem B3150935 : Blo 1399519 3150935 := bstep (se 1 (by rfl) ⟨2363201, by rfl⟩ : syracuseStep 3150935 = 4726403) B4726403
theorem B2364619 : Blo 1399519 2364619 := bstep (se 1 (by rfl) ⟨1773464, by rfl⟩ : syracuseStep 2364619 = 3546929) B3546929
theorem B3151115 : Blo 1399519 3151115 := bstep (se 1 (by rfl) ⟨2363336, by rfl⟩ : syracuseStep 3151115 = 4726673) B4726673
theorem B3151169 : Blo 1399519 3151169 := bstep (se 2 (by rfl) ⟨1181688, by rfl⟩ : syracuseStep 3151169 = 2363377) B2363377
theorem B2364761 : Blo 1399519 2364761 := bstep (se 2 (by rfl) ⟨886785, by rfl⟩ : syracuseStep 2364761 = 1773571) B1773571
theorem B7091549 : Blo 1399519 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B3544499 : Blo 1399519 3544499 := bstep (se 1 (by rfl) ⟨2658374, by rfl⟩ : syracuseStep 3544499 = 5316749) B5316749
theorem B3986891 : Blo 1399519 3986891 := bstep (se 1 (by rfl) ⟨2990168, by rfl⟩ : syracuseStep 3986891 = 5980337) B5980337
theorem B2659787 : Blo 1399519 2659787 := bstep (se 1 (by rfl) ⟨1994840, by rfl⟩ : syracuseStep 2659787 = 3989681) B3989681
theorem B2364889 : Blo 1399519 2364889 := bstep (se 2 (by rfl) ⟨886833, by rfl⟩ : syracuseStep 2364889 = 1773667) B1773667
theorem B4724189 : Blo 1399519 4724189 := bstep (se 3 (by rfl) ⟨885785, by rfl⟩ : syracuseStep 4724189 = 1771571) B1771571
theorem B3151385 : Blo 1399519 3151385 := bstep (se 2 (by rfl) ⟨1181769, by rfl⟩ : syracuseStep 3151385 = 2363539) B2363539
theorem B4789853 : Blo 1399519 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B3839581 : Blo 1399519 3839581 := bstep (se 3 (by rfl) ⟨719921, by rfl⟩ : syracuseStep 3839581 = 1439843) B1439843
theorem B3151475 : Blo 1399519 3151475 := bstep (se 1 (by rfl) ⟨2363606, by rfl⟩ : syracuseStep 3151475 = 4727213) B4727213
theorem B2659969 : Blo 1399519 2659969 := bstep (se 2 (by rfl) ⟨997488, by rfl⟩ : syracuseStep 2659969 = 1994977) B1994977
theorem B3151511 : Blo 1399519 3151511 := bstep (se 1 (by rfl) ⟨2363633, by rfl⟩ : syracuseStep 3151511 = 4727267) B4727267
theorem B10639025 : Blo 1399519 10639025 := bstep (se 2 (by rfl) ⟨3989634, by rfl⟩ : syracuseStep 10639025 = 7979269) B7979269
theorem B7976627 : Blo 1399519 7976627 := bstep (se 1 (by rfl) ⟨5982470, by rfl⟩ : syracuseStep 7976627 = 11964941) B11964941
theorem B3544793 : Blo 1399519 3544793 := bstep (se 2 (by rfl) ⟨1329297, by rfl⟩ : syracuseStep 3544793 = 2658595) B2658595
theorem B5314349 : Blo 1399519 5314349 := bstep (se 3 (by rfl) ⟨996440, by rfl⟩ : syracuseStep 5314349 = 1992881) B1992881
theorem B3151691 : Blo 1399519 3151691 := bstep (se 1 (by rfl) ⟨2363768, by rfl⟩ : syracuseStep 3151691 = 4727537) B4727537
theorem B10098533 : Blo 1399519 10098533 := bstep (se 4 (by rfl) ⟨946737, by rfl⟩ : syracuseStep 10098533 = 1893475) B1893475
theorem B3151745 : Blo 1399519 3151745 := bstep (se 2 (by rfl) ⟨1181904, by rfl⟩ : syracuseStep 3151745 = 2363809) B2363809
theorem B8968067 : Blo 1399519 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B15341489 : Blo 1399519 15341489 := bstep (se 2 (by rfl) ⟨5753058, by rfl⟩ : syracuseStep 15341489 = 11506117) B11506117
theorem B6387635 : Blo 1399519 6387635 := bstep (se 1 (by rfl) ⟨4790726, by rfl⟩ : syracuseStep 6387635 = 9581453) B9581453
theorem B3364939 : Blo 1399519 3364939 := bstep (se 1 (by rfl) ⟨2523704, by rfl⟩ : syracuseStep 3364939 = 5047409) B5047409
theorem B3151961 : Blo 1399519 3151961 := bstep (se 2 (by rfl) ⟨1181985, by rfl⟩ : syracuseStep 3151961 = 2363971) B2363971
theorem B10639511 : Blo 1399519 10639511 := bstep (se 1 (by rfl) ⟨7979633, by rfl⟩ : syracuseStep 10639511 = 15959267) B15959267
theorem B3152051 : Blo 1399519 3152051 := bstep (se 1 (by rfl) ⟨2364038, by rfl⟩ : syracuseStep 3152051 = 4728077) B4728077
theorem B3152087 : Blo 1399519 3152087 := bstep (se 1 (by rfl) ⟨2364065, by rfl⟩ : syracuseStep 3152087 = 4728131) B4728131
theorem B3365171 : Blo 1399519 3365171 := bstep (se 1 (by rfl) ⟨2523878, by rfl⟩ : syracuseStep 3365171 = 5047757) B5047757
theorem B2660683 : Blo 1399519 2660683 := bstep (se 1 (by rfl) ⟨1995512, by rfl⟩ : syracuseStep 2660683 = 3991025) B3991025
theorem B3152267 : Blo 1399519 3152267 := bstep (se 1 (by rfl) ⟨2364200, by rfl⟩ : syracuseStep 3152267 = 4728401) B4728401
theorem B3152321 : Blo 1399519 3152321 := bstep (se 2 (by rfl) ⟨1182120, by rfl⟩ : syracuseStep 3152321 = 2364241) B2364241
theorem B10787363 : Blo 1399519 10787363 := bstep (se 1 (by rfl) ⟨8090522, by rfl⟩ : syracuseStep 10787363 = 16181045) B16181045
theorem B4725323 : Blo 1399519 4725323 := bstep (se 1 (by rfl) ⟨3543992, by rfl⟩ : syracuseStep 4725323 = 7087985) B7087985
theorem B8632925 : Blo 1399519 8632925 := bstep (se 3 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 8632925 = 3237347) B3237347
theorem B3152537 : Blo 1399519 3152537 := bstep (se 2 (by rfl) ⟨1182201, by rfl⟩ : syracuseStep 3152537 = 2364403) B2364403
theorem B10091213 : Blo 1399519 10091213 := bstep (se 3 (by rfl) ⟨1892102, by rfl⟩ : syracuseStep 10091213 = 3784205) B3784205
theorem B5675741 : Blo 1399519 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B1399531 : Blo 1399519 1399531 := bstep (se 1 (by rfl) ⟨1049648, by rfl⟩ : syracuseStep 1399531 = 2099297) B2099297
theorem B3152627 : Blo 1399519 3152627 := bstep (se 1 (by rfl) ⟨2364470, by rfl⟩ : syracuseStep 3152627 = 4728941) B4728941
theorem B1399543 : Blo 1399519 1399543 := bstep (se 1 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 1399543 = 2099315) B2099315
theorem B1399563 : Blo 1399519 1399563 := bstep (se 1 (by rfl) ⟨1049672, by rfl⟩ : syracuseStep 1399563 = 2099345) B2099345
theorem B1399575 : Blo 1399519 1399575 := bstep (se 1 (by rfl) ⟨1049681, by rfl⟩ : syracuseStep 1399575 = 2099363) B2099363
theorem B3152663 : Blo 1399519 3152663 := bstep (se 1 (by rfl) ⟨2364497, by rfl⟩ : syracuseStep 3152663 = 4728995) B4728995
theorem B1399595 : Blo 1399519 1399595 := bstep (se 1 (by rfl) ⟨1049696, by rfl⟩ : syracuseStep 1399595 = 2099393) B2099393
theorem B1399607 : Blo 1399519 1399607 := bstep (se 1 (by rfl) ⟨1049705, by rfl⟩ : syracuseStep 1399607 = 2099411) B2099411
theorem B1399627 : Blo 1399519 1399627 := bstep (se 1 (by rfl) ⟨1049720, by rfl⟩ : syracuseStep 1399627 = 2099441) B2099441
theorem B1399639 : Blo 1399519 1399639 := bstep (se 1 (by rfl) ⟨1049729, by rfl⟩ : syracuseStep 1399639 = 2099459) B2099459
theorem B4725593 : Blo 1399519 4725593 := bstep (se 2 (by rfl) ⟨1772097, by rfl⟩ : syracuseStep 4725593 = 3544195) B3544195
theorem B1399659 : Blo 1399519 1399659 := bstep (se 1 (by rfl) ⟨1049744, by rfl⟩ : syracuseStep 1399659 = 2099489) B2099489
theorem B1399671 : Blo 1399519 1399671 := bstep (se 1 (by rfl) ⟨1049753, by rfl⟩ : syracuseStep 1399671 = 2099507) B2099507
theorem B1399691 : Blo 1399519 1399691 := bstep (se 1 (by rfl) ⟨1049768, by rfl⟩ : syracuseStep 1399691 = 2099537) B2099537
theorem B1399703 : Blo 1399519 1399703 := bstep (se 1 (by rfl) ⟨1049777, by rfl⟩ : syracuseStep 1399703 = 2099555) B2099555
theorem B1399723 : Blo 1399519 1399723 := bstep (se 1 (by rfl) ⟨1049792, by rfl⟩ : syracuseStep 1399723 = 2099585) B2099585
theorem B1399735 : Blo 1399519 1399735 := bstep (se 1 (by rfl) ⟨1049801, by rfl⟩ : syracuseStep 1399735 = 2099603) B2099603
theorem B1399755 : Blo 1399519 1399755 := bstep (se 1 (by rfl) ⟨1049816, by rfl⟩ : syracuseStep 1399755 = 2099633) B2099633
theorem B3152843 : Blo 1399519 3152843 := bstep (se 1 (by rfl) ⟨2364632, by rfl⟩ : syracuseStep 3152843 = 4729265) B4729265
theorem B1399767 : Blo 1399519 1399767 := bstep (se 1 (by rfl) ⟨1049825, by rfl⟩ : syracuseStep 1399767 = 2099651) B2099651
theorem B1399787 : Blo 1399519 1399787 := bstep (se 1 (by rfl) ⟨1049840, by rfl⟩ : syracuseStep 1399787 = 2099681) B2099681
theorem B1399799 : Blo 1399519 1399799 := bstep (se 1 (by rfl) ⟨1049849, by rfl⟩ : syracuseStep 1399799 = 2099699) B2099699
theorem B3152897 : Blo 1399519 3152897 := bstep (se 2 (by rfl) ⟨1182336, by rfl⟩ : syracuseStep 3152897 = 2364673) B2364673
theorem B1399819 : Blo 1399519 1399819 := bstep (se 1 (by rfl) ⟨1049864, by rfl⟩ : syracuseStep 1399819 = 2099729) B2099729
theorem B2128907 : Blo 1399519 2128907 := bstep (se 1 (by rfl) ⟨1596680, by rfl⟩ : syracuseStep 2128907 = 3193361) B3193361
theorem B1399831 : Blo 1399519 1399831 := bstep (se 1 (by rfl) ⟨1049873, by rfl⟩ : syracuseStep 1399831 = 2099747) B2099747
theorem B1399851 : Blo 1399519 1399851 := bstep (se 1 (by rfl) ⟨1049888, by rfl⟩ : syracuseStep 1399851 = 2099777) B2099777
theorem B1399863 : Blo 1399519 1399863 := bstep (se 1 (by rfl) ⟨1049897, by rfl⟩ : syracuseStep 1399863 = 2099795) B2099795
theorem B1399883 : Blo 1399519 1399883 := bstep (se 1 (by rfl) ⟨1049912, by rfl⟩ : syracuseStep 1399883 = 2099825) B2099825
theorem B1399895 : Blo 1399519 1399895 := bstep (se 1 (by rfl) ⟨1049921, by rfl⟩ : syracuseStep 1399895 = 2099843) B2099843
theorem B20175965 : Blo 1399519 20175965 := bstep (se 3 (by rfl) ⟨3782993, by rfl⟩ : syracuseStep 20175965 = 7565987) B7565987
theorem B7978085 : Blo 1399519 7978085 := bstep (se 4 (by rfl) ⟨747945, by rfl⟩ : syracuseStep 7978085 = 1495891) B1495891
theorem B1399915 : Blo 1399519 1399915 := bstep (se 1 (by rfl) ⟨1049936, by rfl⟩ : syracuseStep 1399915 = 2099873) B2099873
theorem B1399927 : Blo 1399519 1399927 := bstep (se 1 (by rfl) ⟨1049945, by rfl⟩ : syracuseStep 1399927 = 2099891) B2099891
theorem B1399947 : Blo 1399519 1399947 := bstep (se 1 (by rfl) ⟨1049960, by rfl⟩ : syracuseStep 1399947 = 2099921) B2099921
theorem B1399959 : Blo 1399519 1399959 := bstep (se 1 (by rfl) ⟨1049969, by rfl⟩ : syracuseStep 1399959 = 2099939) B2099939
theorem B1399979 : Blo 1399519 1399979 := bstep (se 1 (by rfl) ⟨1049984, by rfl⟩ : syracuseStep 1399979 = 2099969) B2099969
theorem B1399991 : Blo 1399519 1399991 := bstep (se 1 (by rfl) ⟨1049993, by rfl⟩ : syracuseStep 1399991 = 2099987) B2099987
theorem B5315777 : Blo 1399519 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B1400011 : Blo 1399519 1400011 := bstep (se 1 (by rfl) ⟨1050008, by rfl⟩ : syracuseStep 1400011 = 2100017) B2100017
theorem B1400023 : Blo 1399519 1400023 := bstep (se 1 (by rfl) ⟨1050017, by rfl⟩ : syracuseStep 1400023 = 2100035) B2100035
theorem B3153113 : Blo 1399519 3153113 := bstep (se 2 (by rfl) ⟨1182417, by rfl⟩ : syracuseStep 3153113 = 2364835) B2364835
theorem B1400043 : Blo 1399519 1400043 := bstep (se 1 (by rfl) ⟨1050032, by rfl⟩ : syracuseStep 1400043 = 2100065) B2100065
theorem B1400055 : Blo 1399519 1400055 := bstep (se 1 (by rfl) ⟨1050041, by rfl⟩ : syracuseStep 1400055 = 2100083) B2100083
theorem B5979395 : Blo 1399519 5979395 := bstep (se 1 (by rfl) ⟨4484546, by rfl⟩ : syracuseStep 5979395 = 8969093) B8969093
theorem B15949061 : Blo 1399519 15949061 := bstep (se 4 (by rfl) ⟨1495224, by rfl⟩ : syracuseStep 15949061 = 2990449) B2990449
theorem B1400075 : Blo 1399519 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1400087 : Blo 1399519 1400087 := bstep (se 1 (by rfl) ⟨1050065, by rfl⟩ : syracuseStep 1400087 = 2100131) B2100131
theorem B1400107 : Blo 1399519 1400107 := bstep (se 1 (by rfl) ⟨1050080, by rfl⟩ : syracuseStep 1400107 = 2100161) B2100161
theorem B3153203 : Blo 1399519 3153203 := bstep (se 1 (by rfl) ⟨2364902, by rfl⟩ : syracuseStep 3153203 = 4729805) B4729805
theorem B1400119 : Blo 1399519 1400119 := bstep (se 1 (by rfl) ⟨1050089, by rfl⟩ : syracuseStep 1400119 = 2100179) B2100179
theorem B6389057 : Blo 1399519 6389057 := bstep (se 2 (by rfl) ⟨2395896, by rfl⟩ : syracuseStep 6389057 = 4791793) B4791793
theorem B2522443 : Blo 1399519 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B1400139 : Blo 1399519 1400139 := bstep (se 1 (by rfl) ⟨1050104, by rfl⟩ : syracuseStep 1400139 = 2100209) B2100209
theorem B3546443 : Blo 1399519 3546443 := bstep (se 1 (by rfl) ⟨2659832, by rfl⟩ : syracuseStep 3546443 = 5319665) B5319665
theorem B1400151 : Blo 1399519 1400151 := bstep (se 1 (by rfl) ⟨1050113, by rfl⟩ : syracuseStep 1400151 = 2100227) B2100227
theorem B3153239 : Blo 1399519 3153239 := bstep (se 1 (by rfl) ⟨2364929, by rfl⟩ : syracuseStep 3153239 = 4729859) B4729859
theorem B1400171 : Blo 1399519 1400171 := bstep (se 1 (by rfl) ⟨1050128, by rfl⟩ : syracuseStep 1400171 = 2100257) B2100257
theorem B1400183 : Blo 1399519 1400183 := bstep (se 1 (by rfl) ⟨1050137, by rfl⟩ : syracuseStep 1400183 = 2100275) B2100275
theorem B1400203 : Blo 1399519 1400203 := bstep (se 1 (by rfl) ⟨1050152, by rfl⟩ : syracuseStep 1400203 = 2100305) B2100305
theorem B1400215 : Blo 1399519 1400215 := bstep (se 1 (by rfl) ⟨1050161, by rfl⟩ : syracuseStep 1400215 = 2100323) B2100323
theorem B7093655 : Blo 1399519 7093655 := bstep (se 1 (by rfl) ⟨5320241, by rfl⟩ : syracuseStep 7093655 = 10640483) B10640483
theorem B1400235 : Blo 1399519 1400235 := bstep (se 1 (by rfl) ⟨1050176, by rfl⟩ : syracuseStep 1400235 = 2100353) B2100353
theorem B1400247 : Blo 1399519 1400247 := bstep (se 1 (by rfl) ⟨1050185, by rfl⟩ : syracuseStep 1400247 = 2100371) B2100371
theorem B1400267 : Blo 1399519 1400267 := bstep (se 1 (by rfl) ⟨1050200, by rfl⟩ : syracuseStep 1400267 = 2100401) B2100401
theorem B1400279 : Blo 1399519 1400279 := bstep (se 1 (by rfl) ⟨1050209, by rfl⟩ : syracuseStep 1400279 = 2100419) B2100419
theorem B1400299 : Blo 1399519 1400299 := bstep (se 1 (by rfl) ⟨1050224, by rfl⟩ : syracuseStep 1400299 = 2100449) B2100449
theorem B1400311 : Blo 1399519 1400311 := bstep (se 1 (by rfl) ⟨1050233, by rfl⟩ : syracuseStep 1400311 = 2100467) B2100467
theorem B1400331 : Blo 1399519 1400331 := bstep (se 1 (by rfl) ⟨1050248, by rfl⟩ : syracuseStep 1400331 = 2100497) B2100497
theorem B3153419 : Blo 1399519 3153419 := bstep (se 1 (by rfl) ⟨2365064, by rfl⟩ : syracuseStep 3153419 = 4730129) B4730129
theorem B1400343 : Blo 1399519 1400343 := bstep (se 1 (by rfl) ⟨1050257, by rfl⟩ : syracuseStep 1400343 = 2100515) B2100515
theorem B4726295 : Blo 1399519 4726295 := bstep (se 1 (by rfl) ⟨3544721, by rfl⟩ : syracuseStep 4726295 = 7089443) B7089443
theorem B1400363 : Blo 1399519 1400363 := bstep (se 1 (by rfl) ⟨1050272, by rfl⟩ : syracuseStep 1400363 = 2100545) B2100545
theorem B1400375 : Blo 1399519 1400375 := bstep (se 1 (by rfl) ⟨1050281, by rfl⟩ : syracuseStep 1400375 = 2100563) B2100563
theorem B11959883 : Blo 1399519 11959883 := bstep (se 1 (by rfl) ⟨8969912, by rfl⟩ : syracuseStep 11959883 = 17939825) B17939825
theorem B1400395 : Blo 1399519 1400395 := bstep (se 1 (by rfl) ⟨1050296, by rfl⟩ : syracuseStep 1400395 = 2100593) B2100593
theorem B1400407 : Blo 1399519 1400407 := bstep (se 1 (by rfl) ⟨1050305, by rfl⟩ : syracuseStep 1400407 = 2100611) B2100611
theorem B5979737 : Blo 1399519 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B1400427 : Blo 1399519 1400427 := bstep (se 1 (by rfl) ⟨1050320, by rfl⟩ : syracuseStep 1400427 = 2100641) B2100641
theorem B1400439 : Blo 1399519 1400439 := bstep (se 1 (by rfl) ⟨1050329, by rfl⟩ : syracuseStep 1400439 = 2100659) B2100659
theorem B1400459 : Blo 1399519 1400459 := bstep (se 1 (by rfl) ⟨1050344, by rfl⟩ : syracuseStep 1400459 = 2100689) B2100689
theorem B1400471 : Blo 1399519 1400471 := bstep (se 1 (by rfl) ⟨1050353, by rfl⟩ : syracuseStep 1400471 = 2100707) B2100707
theorem B1400491 : Blo 1399519 1400491 := bstep (se 1 (by rfl) ⟨1050368, by rfl⟩ : syracuseStep 1400491 = 2100737) B2100737
theorem B1400503 : Blo 1399519 1400503 := bstep (se 1 (by rfl) ⟨1050377, by rfl⟩ : syracuseStep 1400503 = 2100755) B2100755
theorem B1400523 : Blo 1399519 1400523 := bstep (se 1 (by rfl) ⟨1050392, by rfl⟩ : syracuseStep 1400523 = 2100785) B2100785
theorem B1400535 : Blo 1399519 1400535 := bstep (se 1 (by rfl) ⟨1050401, by rfl⟩ : syracuseStep 1400535 = 2100803) B2100803
theorem B3194585 : Blo 1399519 3194585 := bstep (se 2 (by rfl) ⟨1197969, by rfl⟩ : syracuseStep 3194585 = 2395939) B2395939
theorem B1400555 : Blo 1399519 1400555 := bstep (se 1 (by rfl) ⟨1050416, by rfl⟩ : syracuseStep 1400555 = 2100833) B2100833
theorem B1400567 : Blo 1399519 1400567 := bstep (se 1 (by rfl) ⟨1050425, by rfl⟩ : syracuseStep 1400567 = 2100851) B2100851
theorem B1400587 : Blo 1399519 1400587 := bstep (se 1 (by rfl) ⟨1050440, by rfl⟩ : syracuseStep 1400587 = 2100881) B2100881
theorem B7978769 : Blo 1399519 7978769 := bstep (se 2 (by rfl) ⟨2992038, by rfl⟩ : syracuseStep 7978769 = 5984077) B5984077
theorem B1400599 : Blo 1399519 1400599 := bstep (se 1 (by rfl) ⟨1050449, by rfl⟩ : syracuseStep 1400599 = 2100899) B2100899
theorem B2694937 : Blo 1399519 2694937 := bstep (se 2 (by rfl) ⟨1010601, by rfl⟩ : syracuseStep 2694937 = 2021203) B2021203
theorem B1400619 : Blo 1399519 1400619 := bstep (se 1 (by rfl) ⟨1050464, by rfl⟩ : syracuseStep 1400619 = 2100929) B2100929
theorem B1400631 : Blo 1399519 1400631 := bstep (se 1 (by rfl) ⟨1050473, by rfl⟩ : syracuseStep 1400631 = 2100947) B2100947
theorem B1400651 : Blo 1399519 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B1400663 : Blo 1399519 1400663 := bstep (se 1 (by rfl) ⟨1050497, by rfl⟩ : syracuseStep 1400663 = 2100995) B2100995
theorem B2244439 : Blo 1399519 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B11968357 : Blo 1399519 11968357 := bstep (se 4 (by rfl) ⟨1122033, by rfl⟩ : syracuseStep 11968357 = 2244067) B2244067
theorem B1400683 : Blo 1399519 1400683 := bstep (se 1 (by rfl) ⟨1050512, by rfl⟩ : syracuseStep 1400683 = 2101025) B2101025
theorem B1400695 : Blo 1399519 1400695 := bstep (se 1 (by rfl) ⟨1050521, by rfl⟩ : syracuseStep 1400695 = 2101043) B2101043
theorem B2989963 : Blo 1399519 2989963 := bstep (se 1 (by rfl) ⟨2242472, by rfl⟩ : syracuseStep 2989963 = 4484945) B4484945
theorem B1400715 : Blo 1399519 1400715 := bstep (se 1 (by rfl) ⟨1050536, by rfl⟩ : syracuseStep 1400715 = 2101073) B2101073
theorem B1400727 : Blo 1399519 1400727 := bstep (se 1 (by rfl) ⟨1050545, by rfl⟩ : syracuseStep 1400727 = 2101091) B2101091
theorem B1400747 : Blo 1399519 1400747 := bstep (se 1 (by rfl) ⟨1050560, by rfl⟩ : syracuseStep 1400747 = 2101121) B2101121
theorem B17260465 : Blo 1399519 17260465 := bstep (se 2 (by rfl) ⟨6472674, by rfl⟩ : syracuseStep 17260465 = 12945349) B12945349
theorem B2695091 : Blo 1399519 2695091 := bstep (se 1 (by rfl) ⟨2021318, by rfl⟩ : syracuseStep 2695091 = 4042637) B4042637
theorem B1400759 : Blo 1399519 1400759 := bstep (se 1 (by rfl) ⟨1050569, by rfl⟩ : syracuseStep 1400759 = 2101139) B2101139
theorem B1400779 : Blo 1399519 1400779 := bstep (se 1 (by rfl) ⟨1050584, by rfl⟩ : syracuseStep 1400779 = 2101169) B2101169
theorem B2990039 : Blo 1399519 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B7086041 : Blo 1399519 7086041 := bstep (se 2 (by rfl) ⟨2657265, by rfl⟩ : syracuseStep 7086041 = 5314531) B5314531
theorem B1400791 : Blo 1399519 1400791 := bstep (se 1 (by rfl) ⟨1050593, by rfl⟩ : syracuseStep 1400791 = 2101187) B2101187
theorem B1400811 : Blo 1399519 1400811 := bstep (se 1 (by rfl) ⟨1050608, by rfl⟩ : syracuseStep 1400811 = 2101217) B2101217
theorem B1400839 : Blo 1399519 1400839 := bstep (se 1 (by rfl) ⟨1050629, by rfl⟩ : syracuseStep 1400839 = 2101259) B2101259
theorem B1400847 : Blo 1399519 1400847 := bstep (se 1 (by rfl) ⟨1050635, by rfl⟩ : syracuseStep 1400847 = 2101271) B2101271
theorem B5677085 : Blo 1399519 5677085 := bstep (se 3 (by rfl) ⟨1064453, by rfl⟩ : syracuseStep 5677085 = 2128907) B2128907
theorem B3989533 : Blo 1399519 3989533 := bstep (se 3 (by rfl) ⟨748037, by rfl⟩ : syracuseStep 3989533 = 1496075) B1496075
theorem B8085547 : Blo 1399519 8085547 := bstep (se 1 (by rfl) ⟨6064160, by rfl⟩ : syracuseStep 8085547 = 12128321) B12128321
theorem B1400891 : Blo 1399519 1400891 := bstep (se 1 (by rfl) ⟨1050668, by rfl⟩ : syracuseStep 1400891 = 2101337) B2101337
theorem B3547223 : Blo 1399519 3547223 := bstep (se 1 (by rfl) ⟨2660417, by rfl⟩ : syracuseStep 3547223 = 5320835) B5320835
theorem B1400967 : Blo 1399519 1400967 := bstep (se 1 (by rfl) ⟨1050725, by rfl⟩ : syracuseStep 1400967 = 2101451) B2101451
theorem B1400975 : Blo 1399519 1400975 := bstep (se 1 (by rfl) ⟨1050731, by rfl⟩ : syracuseStep 1400975 = 2101463) B2101463
theorem B1401019 : Blo 1399519 1401019 := bstep (se 1 (by rfl) ⟨1050764, by rfl⟩ : syracuseStep 1401019 = 2101529) B2101529
theorem B7094465 : Blo 1399519 7094465 := bstep (se 2 (by rfl) ⟨2660424, by rfl⟩ : syracuseStep 7094465 = 5320849) B5320849
theorem B1401095 : Blo 1399519 1401095 := bstep (se 1 (by rfl) ⟨1050821, by rfl⟩ : syracuseStep 1401095 = 2101643) B2101643
theorem B1401103 : Blo 1399519 1401103 := bstep (se 1 (by rfl) ⟨1050827, by rfl⟩ : syracuseStep 1401103 = 2101655) B2101655
theorem B3547435 : Blo 1399519 3547435 := bstep (se 1 (by rfl) ⟨2660576, by rfl⟩ : syracuseStep 3547435 = 5321153) B5321153
theorem B1401147 : Blo 1399519 1401147 := bstep (se 1 (by rfl) ⟨1050860, by rfl⟩ : syracuseStep 1401147 = 2101721) B2101721
theorem B1401223 : Blo 1399519 1401223 := bstep (se 1 (by rfl) ⟨1050917, by rfl⟩ : syracuseStep 1401223 = 2101835) B2101835
theorem B1401231 : Blo 1399519 1401231 := bstep (se 1 (by rfl) ⟨1050923, by rfl⟩ : syracuseStep 1401231 = 2101847) B2101847
theorem B36397457 : Blo 1399519 36397457 := bstep (se 2 (by rfl) ⟨13649046, by rfl⟩ : syracuseStep 36397457 = 27298093) B27298093
theorem B3547577 : Blo 1399519 3547577 := bstep (se 2 (by rfl) ⟨1330341, by rfl⟩ : syracuseStep 3547577 = 2660683) B2660683
theorem B1401275 : Blo 1399519 1401275 := bstep (se 1 (by rfl) ⟨1050956, by rfl⟩ : syracuseStep 1401275 = 2101913) B2101913
theorem B5980625 : Blo 1399519 5980625 := bstep (se 2 (by rfl) ⟨2242734, by rfl⟩ : syracuseStep 5980625 = 4485469) B4485469
theorem B1401351 : Blo 1399519 1401351 := bstep (se 1 (by rfl) ⟨1051013, by rfl⟩ : syracuseStep 1401351 = 2102027) B2102027
theorem B1401359 : Blo 1399519 1401359 := bstep (se 1 (by rfl) ⟨1051019, by rfl⟩ : syracuseStep 1401359 = 2102039) B2102039
theorem B7979543 : Blo 1399519 7979543 := bstep (se 1 (by rfl) ⟨5984657, by rfl⟩ : syracuseStep 7979543 = 11969315) B11969315
theorem B3195451 : Blo 1399519 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B1401403 : Blo 1399519 1401403 := bstep (se 1 (by rfl) ⟨1051052, by rfl⟩ : syracuseStep 1401403 = 2102105) B2102105
theorem B1401479 : Blo 1399519 1401479 := bstep (se 1 (by rfl) ⟨1051109, by rfl⟩ : syracuseStep 1401479 = 2102219) B2102219
theorem B1401487 : Blo 1399519 1401487 := bstep (se 1 (by rfl) ⟨1051115, by rfl⟩ : syracuseStep 1401487 = 2102231) B2102231
theorem B3785417 : Blo 1399519 3785417 := bstep (se 2 (by rfl) ⟨1419531, by rfl⟩ : syracuseStep 3785417 = 2839063) B2839063
theorem B2524051 : Blo 1399519 2524051 := bstep (se 1 (by rfl) ⟨1893038, by rfl⟩ : syracuseStep 2524051 = 3786077) B3786077
theorem B4727699 : Blo 1399519 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B6824989 : Blo 1399519 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B5317751 : Blo 1399519 5317751 := bstep (se 1 (by rfl) ⟨3988313, by rfl⟩ : syracuseStep 5317751 = 7976627) B7976627
theorem B8971553 : Blo 1399519 8971553 := bstep (se 2 (by rfl) ⟨3364332, by rfl⟩ : syracuseStep 8971553 = 6728665) B6728665
theorem B1893817 : Blo 1399519 1893817 := bstep (se 2 (by rfl) ⟨710181, by rfl⟩ : syracuseStep 1893817 = 1420363) B1420363
theorem B30295781 : Blo 1399519 30295781 := bstep (se 4 (by rfl) ⟨2840229, by rfl⟩ : syracuseStep 30295781 = 5680459) B5680459
theorem B11364097 : Blo 1399519 11364097 := bstep (se 2 (by rfl) ⟨4261536, by rfl⟩ : syracuseStep 11364097 = 8523073) B8523073
theorem B1574671 : Blo 1399519 1574671 := bstep (se 1 (by rfl) ⟨1181003, by rfl⟩ : syracuseStep 1574671 = 2362007) B2362007
theorem B11970341 : Blo 1399519 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B6727475 : Blo 1399519 6727475 := bstep (se 1 (by rfl) ⟨5045606, by rfl⟩ : syracuseStep 6727475 = 10091213) B10091213
theorem B28747637 : Blo 1399519 28747637 := bstep (se 5 (by rfl) ⟨1347545, by rfl⟩ : syracuseStep 28747637 = 2695091) B2695091
theorem B1771399 : Blo 1399519 1771399 := bstep (se 1 (by rfl) ⟨1328549, by rfl⟩ : syracuseStep 1771399 = 2657099) B2657099
theorem B5318723 : Blo 1399519 5318723 := bstep (se 1 (by rfl) ⟨3989042, by rfl⟩ : syracuseStep 5318723 = 7978085) B7978085
theorem B2099387 : Blo 1399519 2099387 := bstep (se 1 (by rfl) ⟨1574540, by rfl⟩ : syracuseStep 2099387 = 3149081) B3149081
theorem B2099447 : Blo 1399519 2099447 := bstep (se 1 (by rfl) ⟨1574585, by rfl⟩ : syracuseStep 2099447 = 3149171) B3149171
theorem B1575175 : Blo 1399519 1575175 := bstep (se 1 (by rfl) ⟨1181381, by rfl⟩ : syracuseStep 1575175 = 2362763) B2362763
theorem B26929421 : Blo 1399519 26929421 := bstep (se 3 (by rfl) ⟨5049266, by rfl⟩ : syracuseStep 26929421 = 10098533) B10098533
theorem B2099471 : Blo 1399519 2099471 := bstep (se 1 (by rfl) ⟨1574603, by rfl⟩ : syracuseStep 2099471 = 3149207) B3149207
theorem B4729103 : Blo 1399519 4729103 := bstep (se 1 (by rfl) ⟨3546827, by rfl⟩ : syracuseStep 4729103 = 7093655) B7093655
theorem B2099513 : Blo 1399519 2099513 := bstep (se 2 (by rfl) ⟨787317, by rfl⟩ : syracuseStep 2099513 = 1574635) B1574635
theorem B1771895 : Blo 1399519 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B2099591 : Blo 1399519 2099591 := bstep (se 1 (by rfl) ⟨1574693, by rfl⟩ : syracuseStep 2099591 = 3149387) B3149387
theorem B7973255 : Blo 1399519 7973255 := bstep (se 1 (by rfl) ⟨5979941, by rfl⟩ : syracuseStep 7973255 = 11959883) B11959883
theorem B2099627 : Blo 1399519 2099627 := bstep (se 1 (by rfl) ⟨1574720, by rfl⟩ : syracuseStep 2099627 = 3149441) B3149441
theorem B1575355 : Blo 1399519 1575355 := bstep (se 1 (by rfl) ⟨1181516, by rfl⟩ : syracuseStep 1575355 = 2363033) B2363033
theorem B2099657 : Blo 1399519 2099657 := bstep (se 2 (by rfl) ⟨787371, by rfl⟩ : syracuseStep 2099657 = 1574743) B1574743
theorem B5319179 : Blo 1399519 5319179 := bstep (se 1 (by rfl) ⟨3989384, by rfl⟩ : syracuseStep 5319179 = 7978769) B7978769
theorem B1772047 : Blo 1399519 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B4483613 : Blo 1399519 4483613 := bstep (se 3 (by rfl) ⟨840677, by rfl⟩ : syracuseStep 4483613 = 1681355) B1681355
theorem B4729373 : Blo 1399519 4729373 := bstep (se 3 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 4729373 = 1773515) B1773515
theorem B2918945 : Blo 1399519 2918945 := bstep (se 2 (by rfl) ⟨1094604, by rfl⟩ : syracuseStep 2918945 = 2189209) B2189209
theorem B2361899 : Blo 1399519 2361899 := bstep (se 1 (by rfl) ⟨1771424, by rfl⟩ : syracuseStep 2361899 = 3542849) B3542849
theorem B2099771 : Blo 1399519 2099771 := bstep (se 1 (by rfl) ⟨1574828, by rfl⟩ : syracuseStep 2099771 = 3149657) B3149657
theorem B7973437 : Blo 1399519 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B23013953 : Blo 1399519 23013953 := bstep (se 2 (by rfl) ⟨8630232, by rfl⟩ : syracuseStep 23013953 = 17260465) B17260465
theorem B2099831 : Blo 1399519 2099831 := bstep (se 1 (by rfl) ⟨1574873, by rfl⟩ : syracuseStep 2099831 = 3149747) B3149747
theorem B2099855 : Blo 1399519 2099855 := bstep (se 1 (by rfl) ⟨1574891, by rfl⟩ : syracuseStep 2099855 = 3149783) B3149783
theorem B2099897 : Blo 1399519 2099897 := bstep (se 2 (by rfl) ⟨787461, by rfl⟩ : syracuseStep 2099897 = 1574923) B1574923
theorem B1772219 : Blo 1399519 1772219 := bstep (se 1 (by rfl) ⟨1329164, by rfl⟩ : syracuseStep 1772219 = 2658329) B2658329
theorem B2099975 : Blo 1399519 2099975 := bstep (se 1 (by rfl) ⟨1574981, by rfl⟩ : syracuseStep 2099975 = 3149963) B3149963
theorem B2100011 : Blo 1399519 2100011 := bstep (se 1 (by rfl) ⟨1575008, by rfl⟩ : syracuseStep 2100011 = 3150017) B3150017
theorem B2100041 : Blo 1399519 2100041 := bstep (se 2 (by rfl) ⟨787515, by rfl⟩ : syracuseStep 2100041 = 1575031) B1575031
theorem B7670663 : Blo 1399519 7670663 := bstep (se 1 (by rfl) ⟨5752997, by rfl⟩ : syracuseStep 7670663 = 11505995) B11505995
theorem B1575823 : Blo 1399519 1575823 := bstep (se 1 (by rfl) ⟨1181867, by rfl⟩ : syracuseStep 1575823 = 2363735) B2363735
theorem B2362297 : Blo 1399519 2362297 := bstep (se 2 (by rfl) ⟨885861, by rfl⟩ : syracuseStep 2362297 = 1771723) B1771723
theorem B2100155 : Blo 1399519 2100155 := bstep (se 1 (by rfl) ⟨1575116, by rfl⟩ : syracuseStep 2100155 = 3150233) B3150233
theorem B1993673 : Blo 1399519 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B2100215 : Blo 1399519 2100215 := bstep (se 1 (by rfl) ⟨1575161, by rfl⟩ : syracuseStep 2100215 = 3150323) B3150323
theorem B45419525 : Blo 1399519 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B2100239 : Blo 1399519 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B2100281 : Blo 1399519 2100281 := bstep (se 2 (by rfl) ⟨787605, by rfl⟩ : syracuseStep 2100281 = 1575211) B1575211
theorem B3148919 : Blo 1399519 3148919 := bstep (se 1 (by rfl) ⟨2361689, by rfl⟩ : syracuseStep 3148919 = 4723379) B4723379
theorem B2100359 : Blo 1399519 2100359 := bstep (se 1 (by rfl) ⟨1575269, by rfl⟩ : syracuseStep 2100359 = 3150539) B3150539
theorem B2100395 : Blo 1399519 2100395 := bstep (se 1 (by rfl) ⟨1575296, by rfl⟩ : syracuseStep 2100395 = 3150593) B3150593
theorem B2100425 : Blo 1399519 2100425 := bstep (se 2 (by rfl) ⟨787659, by rfl⟩ : syracuseStep 2100425 = 1575319) B1575319
theorem B10628333 : Blo 1399519 10628333 := bstep (se 3 (by rfl) ⟨1992812, by rfl⟩ : syracuseStep 10628333 = 3985625) B3985625
theorem B3149099 : Blo 1399519 3149099 := bstep (se 1 (by rfl) ⟨2361824, by rfl⟩ : syracuseStep 3149099 = 4723649) B4723649
theorem B2100539 : Blo 1399519 2100539 := bstep (se 1 (by rfl) ⟨1575404, by rfl⟩ : syracuseStep 2100539 = 3150809) B3150809
theorem B5049715 : Blo 1399519 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B2100599 : Blo 1399519 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B4550023 : Blo 1399519 4550023 := bstep (se 1 (by rfl) ⟨3412517, by rfl⟩ : syracuseStep 4550023 = 6825035) B6825035
theorem B1576327 : Blo 1399519 1576327 := bstep (se 1 (by rfl) ⟨1182245, by rfl⟩ : syracuseStep 1576327 = 2364491) B2364491
theorem B2100623 : Blo 1399519 2100623 := bstep (se 1 (by rfl) ⟨1575467, by rfl⟩ : syracuseStep 2100623 = 3150935) B3150935
theorem B2100665 : Blo 1399519 2100665 := bstep (se 2 (by rfl) ⟨787749, by rfl⟩ : syracuseStep 2100665 = 1575499) B1575499
theorem B2100743 : Blo 1399519 2100743 := bstep (se 1 (by rfl) ⟨1575557, by rfl⟩ : syracuseStep 2100743 = 3151115) B3151115
theorem B2100779 : Blo 1399519 2100779 := bstep (se 1 (by rfl) ⟨1575584, by rfl⟩ : syracuseStep 2100779 = 3151169) B3151169
theorem B1576507 : Blo 1399519 1576507 := bstep (se 1 (by rfl) ⟨1182380, by rfl⟩ : syracuseStep 1576507 = 2364761) B2364761
theorem B2100809 : Blo 1399519 2100809 := bstep (se 2 (by rfl) ⟨787803, by rfl⟩ : syracuseStep 2100809 = 1575607) B1575607
theorem B2362999 : Blo 1399519 2362999 := bstep (se 1 (by rfl) ⟨1772249, by rfl⟩ : syracuseStep 2362999 = 3544499) B3544499
theorem B2657927 : Blo 1399519 2657927 := bstep (se 1 (by rfl) ⟨1993445, by rfl⟩ : syracuseStep 2657927 = 3986891) B3986891
theorem B1773191 : Blo 1399519 1773191 := bstep (se 1 (by rfl) ⟨1329893, by rfl⟩ : syracuseStep 1773191 = 2659787) B2659787
theorem B3149459 : Blo 1399519 3149459 := bstep (se 1 (by rfl) ⟨2362094, by rfl⟩ : syracuseStep 3149459 = 4724189) B4724189
theorem B2100923 : Blo 1399519 2100923 := bstep (se 1 (by rfl) ⟨1575692, by rfl⟩ : syracuseStep 2100923 = 3151385) B3151385
theorem B3149513 : Blo 1399519 3149513 := bstep (se 2 (by rfl) ⟨1181067, by rfl⟩ : syracuseStep 3149513 = 2362135) B2362135
theorem B2100983 : Blo 1399519 2100983 := bstep (se 1 (by rfl) ⟨1575737, by rfl⟩ : syracuseStep 2100983 = 3151475) B3151475
theorem B2101007 : Blo 1399519 2101007 := bstep (se 1 (by rfl) ⟨1575755, by rfl⟩ : syracuseStep 2101007 = 3151511) B3151511
theorem B7286543 : Blo 1399519 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B8523557 : Blo 1399519 8523557 := bstep (se 4 (by rfl) ⟨799083, by rfl⟩ : syracuseStep 8523557 = 1598167) B1598167
theorem B1994539 : Blo 1399519 1994539 := bstep (se 1 (by rfl) ⟨1495904, by rfl⟩ : syracuseStep 1994539 = 2991809) B2991809
theorem B2101049 : Blo 1399519 2101049 := bstep (se 2 (by rfl) ⟨787893, by rfl⟩ : syracuseStep 2101049 = 1575787) B1575787
theorem B2363195 : Blo 1399519 2363195 := bstep (se 1 (by rfl) ⟨1772396, by rfl⟩ : syracuseStep 2363195 = 3544793) B3544793
theorem B8089433 : Blo 1399519 8089433 := bstep (se 2 (by rfl) ⟨3033537, by rfl⟩ : syracuseStep 8089433 = 6067075) B6067075
theorem B3542899 : Blo 1399519 3542899 := bstep (se 1 (by rfl) ⟨2657174, by rfl⟩ : syracuseStep 3542899 = 5314349) B5314349
theorem B2101127 : Blo 1399519 2101127 := bstep (se 1 (by rfl) ⟨1575845, by rfl⟩ : syracuseStep 2101127 = 3151691) B3151691
theorem B2101163 : Blo 1399519 2101163 := bstep (se 1 (by rfl) ⟨1575872, by rfl⟩ : syracuseStep 2101163 = 3151745) B3151745
theorem B2101193 : Blo 1399519 2101193 := bstep (se 2 (by rfl) ⟨787947, by rfl⟩ : syracuseStep 2101193 = 1575895) B1575895
theorem B10227659 : Blo 1399519 10227659 := bstep (se 1 (by rfl) ⟨7670744, by rfl⟩ : syracuseStep 10227659 = 15341489) B15341489
theorem B3543041 : Blo 1399519 3543041 := bstep (se 2 (by rfl) ⟨1328640, by rfl⟩ : syracuseStep 3543041 = 2657281) B2657281
theorem B64679957 : Blo 1399519 64679957 := bstep (se 6 (by rfl) ⟨1515936, by rfl⟩ : syracuseStep 64679957 = 3031873) B3031873
theorem B7680023 : Blo 1399519 7680023 := bstep (se 1 (by rfl) ⟨5760017, by rfl⟩ : syracuseStep 7680023 = 11520035) B11520035
theorem B2101307 : Blo 1399519 2101307 := bstep (se 1 (by rfl) ⟨1575980, by rfl⟩ : syracuseStep 2101307 = 3151961) B3151961
theorem B2101367 : Blo 1399519 2101367 := bstep (se 1 (by rfl) ⟨1576025, by rfl⟩ : syracuseStep 2101367 = 3152051) B3152051
theorem B2101391 : Blo 1399519 2101391 := bstep (se 1 (by rfl) ⟨1576043, by rfl⟩ : syracuseStep 2101391 = 3152087) B3152087
theorem B2101433 : Blo 1399519 2101433 := bstep (se 2 (by rfl) ⟨788037, by rfl⟩ : syracuseStep 2101433 = 1576075) B1576075
theorem B2363593 : Blo 1399519 2363593 := bstep (se 2 (by rfl) ⟨886347, by rfl⟩ : syracuseStep 2363593 = 1772695) B1772695
theorem B7975169 : Blo 1399519 7975169 := bstep (se 2 (by rfl) ⟨2990688, by rfl⟩ : syracuseStep 7975169 = 5981377) B5981377
theorem B2101511 : Blo 1399519 2101511 := bstep (se 1 (by rfl) ⟨1576133, by rfl⟩ : syracuseStep 2101511 = 3152267) B3152267
theorem B2101547 : Blo 1399519 2101547 := bstep (se 1 (by rfl) ⟨1576160, by rfl⟩ : syracuseStep 2101547 = 3152321) B3152321
theorem B2101577 : Blo 1399519 2101577 := bstep (se 2 (by rfl) ⟨788091, by rfl⟩ : syracuseStep 2101577 = 1576183) B1576183
theorem B3150215 : Blo 1399519 3150215 := bstep (se 1 (by rfl) ⟨2362661, by rfl⟩ : syracuseStep 3150215 = 4725323) B4725323
theorem B7090577 : Blo 1399519 7090577 := bstep (se 2 (by rfl) ⟨2658966, by rfl⟩ : syracuseStep 7090577 = 5317933) B5317933
theorem B5755283 : Blo 1399519 5755283 := bstep (se 1 (by rfl) ⟨4316462, by rfl⟩ : syracuseStep 5755283 = 8632925) B8632925
theorem B3363257 : Blo 1399519 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B2101691 : Blo 1399519 2101691 := bstep (se 1 (by rfl) ⟨1576268, by rfl⟩ : syracuseStep 2101691 = 3152537) B3152537
theorem B5681593 : Blo 1399519 5681593 := bstep (se 2 (by rfl) ⟨2130597, by rfl⟩ : syracuseStep 5681593 = 4261195) B4261195
theorem B3543497 : Blo 1399519 3543497 := bstep (se 2 (by rfl) ⟨1328811, by rfl⟩ : syracuseStep 3543497 = 2657623) B2657623
theorem B9089489 : Blo 1399519 9089489 := bstep (se 2 (by rfl) ⟨3408558, by rfl⟩ : syracuseStep 9089489 = 6817117) B6817117
theorem B2101751 : Blo 1399519 2101751 := bstep (se 1 (by rfl) ⟨1576313, by rfl⟩ : syracuseStep 2101751 = 3152627) B3152627
theorem B2101775 : Blo 1399519 2101775 := bstep (se 1 (by rfl) ⟨1576331, by rfl⟩ : syracuseStep 2101775 = 3152663) B3152663
theorem B92123669 : Blo 1399519 92123669 := bstep (se 6 (by rfl) ⟨2159148, by rfl⟩ : syracuseStep 92123669 = 4318297) B4318297
theorem B2101817 : Blo 1399519 2101817 := bstep (se 2 (by rfl) ⟨788181, by rfl⟩ : syracuseStep 2101817 = 1576363) B1576363
theorem B3150395 : Blo 1399519 3150395 := bstep (se 1 (by rfl) ⟨2362796, by rfl⟩ : syracuseStep 3150395 = 4725593) B4725593
theorem B5321335 : Blo 1399519 5321335 := bstep (se 1 (by rfl) ⟨3991001, by rfl⟩ : syracuseStep 5321335 = 7982003) B7982003
theorem B2101895 : Blo 1399519 2101895 := bstep (se 1 (by rfl) ⟨1576421, by rfl⟩ : syracuseStep 2101895 = 3152843) B3152843
theorem B2101931 : Blo 1399519 2101931 := bstep (se 1 (by rfl) ⟨1576448, by rfl⟩ : syracuseStep 2101931 = 3152897) B3152897
theorem B3150521 : Blo 1399519 3150521 := bstep (se 2 (by rfl) ⟨1181445, by rfl⟩ : syracuseStep 3150521 = 2362891) B2362891
theorem B2101961 : Blo 1399519 2101961 := bstep (se 2 (by rfl) ⟨788235, by rfl⟩ : syracuseStep 2101961 = 1576471) B1576471
theorem B10638053 : Blo 1399519 10638053 := bstep (se 4 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 10638053 = 1994635) B1994635
theorem B8631073 : Blo 1399519 8631073 := bstep (se 2 (by rfl) ⟨3236652, by rfl⟩ : syracuseStep 8631073 = 6473305) B6473305
theorem B3543851 : Blo 1399519 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B2102075 : Blo 1399519 2102075 := bstep (se 1 (by rfl) ⟨1576556, by rfl⟩ : syracuseStep 2102075 = 3153113) B3153113
theorem B3986263 : Blo 1399519 3986263 := bstep (se 1 (by rfl) ⟨2989697, by rfl⟩ : syracuseStep 3986263 = 5979395) B5979395
theorem B2102135 : Blo 1399519 2102135 := bstep (se 1 (by rfl) ⟨1576601, by rfl⟩ : syracuseStep 2102135 = 3153203) B3153203
theorem B2364295 : Blo 1399519 2364295 := bstep (se 1 (by rfl) ⟨1773221, by rfl⟩ : syracuseStep 2364295 = 3546443) B3546443
theorem B2102159 : Blo 1399519 2102159 := bstep (se 1 (by rfl) ⟨1576619, by rfl⟩ : syracuseStep 2102159 = 3153239) B3153239
theorem B2102201 : Blo 1399519 2102201 := bstep (se 2 (by rfl) ⟨788325, by rfl⟩ : syracuseStep 2102201 = 1576651) B1576651
theorem B2102279 : Blo 1399519 2102279 := bstep (se 1 (by rfl) ⟨1576709, by rfl⟩ : syracuseStep 2102279 = 3153419) B3153419
theorem B3150863 : Blo 1399519 3150863 := bstep (se 1 (by rfl) ⟨2363147, by rfl⟩ : syracuseStep 3150863 = 4726295) B4726295
theorem B3150881 : Blo 1399519 3150881 := bstep (se 2 (by rfl) ⟨1181580, by rfl⟩ : syracuseStep 3150881 = 2363161) B2363161
theorem B3593249 : Blo 1399519 3593249 := bstep (se 2 (by rfl) ⟨1347468, by rfl⟩ : syracuseStep 3593249 = 2694937) B2694937
theorem B4486187 : Blo 1399519 4486187 := bstep (se 1 (by rfl) ⟨3364640, by rfl⟩ : syracuseStep 4486187 = 6729281) B6729281
theorem B3986491 : Blo 1399519 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B10630277 : Blo 1399519 10630277 := bstep (se 4 (by rfl) ⟨996588, by rfl⟩ : syracuseStep 10630277 = 1993177) B1993177
theorem B3986617 : Blo 1399519 3986617 := bstep (se 2 (by rfl) ⟨1494981, by rfl⟩ : syracuseStep 3986617 = 2989963) B2989963
theorem B2659529 : Blo 1399519 2659529 := bstep (se 2 (by rfl) ⟨997323, by rfl⟩ : syracuseStep 2659529 = 1994647) B1994647
theorem B8303887 : Blo 1399519 8303887 := bstep (se 1 (by rfl) ⟨6227915, by rfl⟩ : syracuseStep 8303887 = 12455831) B12455831
theorem B4724027 : Blo 1399519 4724027 := bstep (se 1 (by rfl) ⟨3543020, by rfl⟩ : syracuseStep 4724027 = 7086041) B7086041
theorem B3151223 : Blo 1399519 3151223 := bstep (se 1 (by rfl) ⟨2363417, by rfl⟩ : syracuseStep 3151223 = 4726835) B4726835
theorem B5985683 : Blo 1399519 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B4486585 : Blo 1399519 4486585 := bstep (se 2 (by rfl) ⟨1682469, by rfl⟩ : syracuseStep 4486585 = 3364939) B3364939
theorem B2364943 : Blo 1399519 2364943 := bstep (se 1 (by rfl) ⟨1773707, by rfl⟩ : syracuseStep 2364943 = 3547415) B3547415
theorem B3839521 : Blo 1399519 3839521 := bstep (se 2 (by rfl) ⟨1439820, by rfl⟩ : syracuseStep 3839521 = 2879641) B2879641
theorem B4486699 : Blo 1399519 4486699 := bstep (se 1 (by rfl) ⟨3365024, by rfl⟩ : syracuseStep 4486699 = 6730049) B6730049
theorem B3151403 : Blo 1399519 3151403 := bstep (se 1 (by rfl) ⟨2363552, by rfl⟩ : syracuseStep 3151403 = 4727105) B4727105
theorem B6477355 : Blo 1399519 6477355 := bstep (se 1 (by rfl) ⟨4858016, by rfl⟩ : syracuseStep 6477355 = 9716033) B9716033
theorem B3364487 : Blo 1399519 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B3544843 : Blo 1399519 3544843 := bstep (se 1 (by rfl) ⟨2658632, by rfl⟩ : syracuseStep 3544843 = 5317265) B5317265
theorem B5314319 : Blo 1399519 5314319 := bstep (se 1 (by rfl) ⟨3985739, by rfl⟩ : syracuseStep 5314319 = 7971479) B7971479
theorem B4724513 : Blo 1399519 4724513 := bstep (se 2 (by rfl) ⟨1771692, by rfl⟩ : syracuseStep 4724513 = 3543385) B3543385
theorem B3594071 : Blo 1399519 3594071 := bstep (se 1 (by rfl) ⟨2695553, by rfl⟩ : syracuseStep 3594071 = 5391107) B5391107
theorem B3151763 : Blo 1399519 3151763 := bstep (se 1 (by rfl) ⟨2363822, by rfl⟩ : syracuseStep 3151763 = 4727645) B4727645
theorem B3544985 : Blo 1399519 3544985 := bstep (se 2 (by rfl) ⟨1329369, by rfl⟩ : syracuseStep 3544985 = 2658739) B2658739
theorem B3151817 : Blo 1399519 3151817 := bstep (se 2 (by rfl) ⟨1181931, by rfl⟩ : syracuseStep 3151817 = 2363863) B2363863
theorem B30275531 : Blo 1399519 30275531 := bstep (se 1 (by rfl) ⟨22706648, by rfl⟩ : syracuseStep 30275531 = 45413297) B45413297
theorem B6731723 : Blo 1399519 6731723 := bstep (se 1 (by rfl) ⟨5048792, by rfl⟩ : syracuseStep 6731723 = 10097585) B10097585
theorem B6731741 : Blo 1399519 6731741 := bstep (se 3 (by rfl) ⟨1262201, by rfl⟩ : syracuseStep 6731741 = 2524403) B2524403
theorem B6731819 : Blo 1399519 6731819 := bstep (se 1 (by rfl) ⟨5048864, by rfl⟩ : syracuseStep 6731819 = 10097729) B10097729
theorem B3545147 : Blo 1399519 3545147 := bstep (se 1 (by rfl) ⟨2658860, by rfl⟩ : syracuseStep 3545147 = 5317721) B5317721
theorem B20191477 : Blo 1399519 20191477 := bstep (se 5 (by rfl) ⟨946475, by rfl⟩ : syracuseStep 20191477 = 1892951) B1892951
theorem B4725107 : Blo 1399519 4725107 := bstep (se 1 (by rfl) ⟨3543830, by rfl⟩ : syracuseStep 4725107 = 7087661) B7087661
theorem B4544903 : Blo 1399519 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B3193235 : Blo 1399519 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B3545491 : Blo 1399519 3545491 := bstep (se 1 (by rfl) ⟨2659118, by rfl⟩ : syracuseStep 3545491 = 5318237) B5318237
theorem B7092683 : Blo 1399519 7092683 := bstep (se 1 (by rfl) ⟨5319512, by rfl⟩ : syracuseStep 7092683 = 10639025) B10639025
theorem B3545633 : Blo 1399519 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B5978711 : Blo 1399519 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B4258423 : Blo 1399519 4258423 := bstep (se 1 (by rfl) ⟨3193817, by rfl⟩ : syracuseStep 4258423 = 6387635) B6387635
theorem B3152519 : Blo 1399519 3152519 := bstep (se 1 (by rfl) ⟨2364389, by rfl⟩ : syracuseStep 3152519 = 4728779) B4728779
theorem B1399559 : Blo 1399519 1399559 := bstep (se 1 (by rfl) ⟨1049669, by rfl⟩ : syracuseStep 1399559 = 2099339) B2099339
theorem B1399567 : Blo 1399519 1399567 := bstep (se 1 (by rfl) ⟨1049675, by rfl⟩ : syracuseStep 1399567 = 2099351) B2099351
theorem B7093007 : Blo 1399519 7093007 := bstep (se 1 (by rfl) ⟨5319755, by rfl⟩ : syracuseStep 7093007 = 10639511) B10639511
theorem B1399611 : Blo 1399519 1399611 := bstep (se 1 (by rfl) ⟨1049708, by rfl⟩ : syracuseStep 1399611 = 2099417) B2099417
theorem B3152699 : Blo 1399519 3152699 := bstep (se 1 (by rfl) ⟨2364524, by rfl⟩ : syracuseStep 3152699 = 4729049) B4729049
theorem B13458251 : Blo 1399519 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B2243447 : Blo 1399519 2243447 := bstep (se 1 (by rfl) ⟨1682585, by rfl⟩ : syracuseStep 2243447 = 3365171) B3365171
theorem B1399687 : Blo 1399519 1399687 := bstep (se 1 (by rfl) ⟨1049765, by rfl⟩ : syracuseStep 1399687 = 2099531) B2099531
theorem B1399695 : Blo 1399519 1399695 := bstep (se 1 (by rfl) ⟨1049771, by rfl⟩ : syracuseStep 1399695 = 2099543) B2099543
theorem B3783577 : Blo 1399519 3783577 := bstep (se 2 (by rfl) ⟨1418841, by rfl⟩ : syracuseStep 3783577 = 2837683) B2837683
theorem B3152825 : Blo 1399519 3152825 := bstep (se 2 (by rfl) ⟨1182309, by rfl⟩ : syracuseStep 3152825 = 2364619) B2364619
theorem B1399739 : Blo 1399519 1399739 := bstep (se 1 (by rfl) ⟨1049804, by rfl⟩ : syracuseStep 1399739 = 2099609) B2099609
theorem B1399815 : Blo 1399519 1399815 := bstep (se 1 (by rfl) ⟨1049861, by rfl⟩ : syracuseStep 1399815 = 2099723) B2099723
theorem B1399823 : Blo 1399519 1399823 := bstep (se 1 (by rfl) ⟨1049867, by rfl⟩ : syracuseStep 1399823 = 2099735) B2099735
theorem B7191575 : Blo 1399519 7191575 := bstep (se 1 (by rfl) ⟨5393681, by rfl⟩ : syracuseStep 7191575 = 10787363) B10787363
theorem B1399867 : Blo 1399519 1399867 := bstep (se 1 (by rfl) ⟨1049900, by rfl⟩ : syracuseStep 1399867 = 2099801) B2099801
theorem B3988541 : Blo 1399519 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B1399943 : Blo 1399519 1399943 := bstep (se 1 (by rfl) ⟨1049957, by rfl⟩ : syracuseStep 1399943 = 2099915) B2099915
theorem B1399951 : Blo 1399519 1399951 := bstep (se 1 (by rfl) ⟨1049963, by rfl⟩ : syracuseStep 1399951 = 2099927) B2099927
theorem B3783827 : Blo 1399519 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B1399995 : Blo 1399519 1399995 := bstep (se 1 (by rfl) ⟨1049996, by rfl⟩ : syracuseStep 1399995 = 2099993) B2099993
theorem B1400071 : Blo 1399519 1400071 := bstep (se 1 (by rfl) ⟨1050053, by rfl⟩ : syracuseStep 1400071 = 2100107) B2100107
theorem B1400079 : Blo 1399519 1400079 := bstep (se 1 (by rfl) ⟨1050059, by rfl⟩ : syracuseStep 1400079 = 2100119) B2100119
theorem B3153167 : Blo 1399519 3153167 := bstep (se 1 (by rfl) ⟨2364875, by rfl⟩ : syracuseStep 3153167 = 4729751) B4729751
theorem B3153185 : Blo 1399519 3153185 := bstep (se 2 (by rfl) ⟨1182444, by rfl⟩ : syracuseStep 3153185 = 2364889) B2364889
theorem B1400123 : Blo 1399519 1400123 := bstep (se 1 (by rfl) ⟨1050092, by rfl⟩ : syracuseStep 1400123 = 2100185) B2100185
theorem B5315975 : Blo 1399519 5315975 := bstep (se 1 (by rfl) ⟨3986981, by rfl⟩ : syracuseStep 5315975 = 7973963) B7973963
theorem B1400199 : Blo 1399519 1400199 := bstep (se 1 (by rfl) ⟨1050149, by rfl⟩ : syracuseStep 1400199 = 2100299) B2100299
theorem B1400207 : Blo 1399519 1400207 := bstep (se 1 (by rfl) ⟨1050155, by rfl⟩ : syracuseStep 1400207 = 2100311) B2100311
theorem B13450643 : Blo 1399519 13450643 := bstep (se 1 (by rfl) ⟨10087982, by rfl⟩ : syracuseStep 13450643 = 20175965) B20175965
theorem B1400251 : Blo 1399519 1400251 := bstep (se 1 (by rfl) ⟨1050188, by rfl⟩ : syracuseStep 1400251 = 2100377) B2100377
theorem B5119441 : Blo 1399519 5119441 := bstep (se 2 (by rfl) ⟨1919790, by rfl⟩ : syracuseStep 5119441 = 3839581) B3839581
theorem B3546625 : Blo 1399519 3546625 := bstep (se 2 (by rfl) ⟨1329984, by rfl⟩ : syracuseStep 3546625 = 2659969) B2659969
theorem B10632707 : Blo 1399519 10632707 := bstep (se 1 (by rfl) ⟨7974530, by rfl⟩ : syracuseStep 10632707 = 15949061) B15949061
theorem B1400327 : Blo 1399519 1400327 := bstep (se 1 (by rfl) ⟨1050245, by rfl⟩ : syracuseStep 1400327 = 2100491) B2100491
theorem B1400335 : Blo 1399519 1400335 := bstep (se 1 (by rfl) ⟨1050251, by rfl⟩ : syracuseStep 1400335 = 2100503) B2100503
theorem B4259371 : Blo 1399519 4259371 := bstep (se 1 (by rfl) ⟨3194528, by rfl⟩ : syracuseStep 4259371 = 6389057) B6389057
theorem B1400379 : Blo 1399519 1400379 := bstep (se 1 (by rfl) ⟨1050284, by rfl⟩ : syracuseStep 1400379 = 2100569) B2100569
theorem B1400455 : Blo 1399519 1400455 := bstep (se 1 (by rfl) ⟨1050341, by rfl⟩ : syracuseStep 1400455 = 2100683) B2100683
theorem B1400463 : Blo 1399519 1400463 := bstep (se 1 (by rfl) ⟨1050347, by rfl⟩ : syracuseStep 1400463 = 2100695) B2100695
theorem B1400507 : Blo 1399519 1400507 := bstep (se 1 (by rfl) ⟨1050380, by rfl⟩ : syracuseStep 1400507 = 2100761) B2100761
theorem B1400583 : Blo 1399519 1400583 := bstep (se 1 (by rfl) ⟨1050437, by rfl⟩ : syracuseStep 1400583 = 2100875) B2100875
theorem B3071759 : Blo 1399519 3071759 := bstep (se 1 (by rfl) ⟨2303819, by rfl⟩ : syracuseStep 3071759 = 4607639) B4607639
theorem B1400591 : Blo 1399519 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B3194657 : Blo 1399519 3194657 := bstep (se 2 (by rfl) ⟨1197996, by rfl⟩ : syracuseStep 3194657 = 2395993) B2395993
theorem B15957809 : Blo 1399519 15957809 := bstep (se 2 (by rfl) ⟨5984178, by rfl⟩ : syracuseStep 15957809 = 11968357) B11968357
theorem B6725435 : Blo 1399519 6725435 := bstep (se 1 (by rfl) ⟨5044076, by rfl⟩ : syracuseStep 6725435 = 10088153) B10088153
theorem B1400635 : Blo 1399519 1400635 := bstep (se 1 (by rfl) ⟨1050476, by rfl⟩ : syracuseStep 1400635 = 2100953) B2100953
theorem B2129723 : Blo 1399519 2129723 := bstep (se 1 (by rfl) ⟨1597292, by rfl⟩ : syracuseStep 2129723 = 3194585) B3194585
theorem B20176715 : Blo 1399519 20176715 := bstep (se 1 (by rfl) ⟨15132536, by rfl⟩ : syracuseStep 20176715 = 30265073) B30265073
theorem B1400711 : Blo 1399519 1400711 := bstep (se 1 (by rfl) ⟨1050533, by rfl⟩ : syracuseStep 1400711 = 2101067) B2101067
theorem B1400719 : Blo 1399519 1400719 := bstep (se 1 (by rfl) ⟨1050539, by rfl⟩ : syracuseStep 1400719 = 2101079) B2101079
theorem B1400763 : Blo 1399519 1400763 := bstep (se 1 (by rfl) ⟨1050572, by rfl⟩ : syracuseStep 1400763 = 2101145) B2101145
theorem B5120015 : Blo 1399519 5120015 := bstep (se 1 (by rfl) ⟨3840011, by rfl⟩ : syracuseStep 5120015 = 7680023) B7680023
theorem B1400871 : Blo 1399519 1400871 := bstep (se 1 (by rfl) ⟨1050653, by rfl⟩ : syracuseStep 1400871 = 2101307) B2101307
theorem B15138893 : Blo 1399519 15138893 := bstep (se 3 (by rfl) ⟨2838542, by rfl⟩ : syracuseStep 15138893 = 5677085) B5677085
theorem B1400911 : Blo 1399519 1400911 := bstep (se 1 (by rfl) ⟨1050683, by rfl⟩ : syracuseStep 1400911 = 2101367) B2101367
theorem B1400927 : Blo 1399519 1400927 := bstep (se 1 (by rfl) ⟨1050695, by rfl⟩ : syracuseStep 1400927 = 2101391) B2101391
theorem B1400955 : Blo 1399519 1400955 := bstep (se 1 (by rfl) ⟨1050716, by rfl⟩ : syracuseStep 1400955 = 2101433) B2101433
theorem B5316779 : Blo 1399519 5316779 := bstep (se 1 (by rfl) ⟨3987584, by rfl⟩ : syracuseStep 5316779 = 7975169) B7975169
theorem B1401007 : Blo 1399519 1401007 := bstep (se 1 (by rfl) ⟨1050755, by rfl⟩ : syracuseStep 1401007 = 2101511) B2101511
theorem B1401031 : Blo 1399519 1401031 := bstep (se 1 (by rfl) ⟨1050773, by rfl⟩ : syracuseStep 1401031 = 2101547) B2101547
theorem B1401051 : Blo 1399519 1401051 := bstep (se 1 (by rfl) ⟨1050788, by rfl⟩ : syracuseStep 1401051 = 2101577) B2101577
theorem B43122917 : Blo 1399519 43122917 := bstep (se 4 (by rfl) ⟨4042773, by rfl⟩ : syracuseStep 43122917 = 8085547) B8085547
theorem B4727051 : Blo 1399519 4727051 := bstep (se 1 (by rfl) ⟨3545288, by rfl⟩ : syracuseStep 4727051 = 7090577) B7090577
theorem B24264971 : Blo 1399519 24264971 := bstep (se 1 (by rfl) ⟨18198728, by rfl⟩ : syracuseStep 24264971 = 36397457) B36397457
theorem B1401127 : Blo 1399519 1401127 := bstep (se 1 (by rfl) ⟨1050845, by rfl⟩ : syracuseStep 1401127 = 2101691) B2101691
theorem B1401167 : Blo 1399519 1401167 := bstep (se 1 (by rfl) ⟨1050875, by rfl⟩ : syracuseStep 1401167 = 2101751) B2101751
theorem B1401183 : Blo 1399519 1401183 := bstep (se 1 (by rfl) ⟨1050887, by rfl⟩ : syracuseStep 1401183 = 2101775) B2101775
theorem B61415779 : Blo 1399519 61415779 := bstep (se 1 (by rfl) ⟨46061834, by rfl⟩ : syracuseStep 61415779 = 92123669) B92123669
theorem B1401211 : Blo 1399519 1401211 := bstep (se 1 (by rfl) ⟨1050908, by rfl⟩ : syracuseStep 1401211 = 2101817) B2101817
theorem B1401263 : Blo 1399519 1401263 := bstep (se 1 (by rfl) ⟨1050947, by rfl⟩ : syracuseStep 1401263 = 2101895) B2101895
theorem B1401287 : Blo 1399519 1401287 := bstep (se 1 (by rfl) ⟨1050965, by rfl⟩ : syracuseStep 1401287 = 2101931) B2101931
theorem B2523611 : Blo 1399519 2523611 := bstep (se 1 (by rfl) ⟨1892708, by rfl⟩ : syracuseStep 2523611 = 3785417) B3785417
theorem B1401307 : Blo 1399519 1401307 := bstep (se 1 (by rfl) ⟨1050980, by rfl⟩ : syracuseStep 1401307 = 2101961) B2101961
theorem B4727321 : Blo 1399519 4727321 := bstep (se 2 (by rfl) ⟨1772745, by rfl⟩ : syracuseStep 4727321 = 3545491) B3545491
theorem B1401383 : Blo 1399519 1401383 := bstep (se 1 (by rfl) ⟨1051037, by rfl⟩ : syracuseStep 1401383 = 2102075) B2102075
theorem B1401423 : Blo 1399519 1401423 := bstep (se 1 (by rfl) ⟨1051067, by rfl⟩ : syracuseStep 1401423 = 2102135) B2102135
theorem B1401439 : Blo 1399519 1401439 := bstep (se 1 (by rfl) ⟨1051079, by rfl⟩ : syracuseStep 1401439 = 2102159) B2102159
theorem B1401467 : Blo 1399519 1401467 := bstep (se 1 (by rfl) ⟨1051100, by rfl⟩ : syracuseStep 1401467 = 2102201) B2102201
theorem B1401519 : Blo 1399519 1401519 := bstep (se 1 (by rfl) ⟨1051139, by rfl⟩ : syracuseStep 1401519 = 2102279) B2102279
theorem B2990791 : Blo 1399519 2990791 := bstep (se 1 (by rfl) ⟨2243093, by rfl⟩ : syracuseStep 2990791 = 4486187) B4486187
theorem B4260601 : Blo 1399519 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B7086851 : Blo 1399519 7086851 := bstep (se 1 (by rfl) ⟨5315138, by rfl⟩ : syracuseStep 7086851 = 10630277) B10630277
theorem B5677897 : Blo 1399519 5677897 := bstep (se 2 (by rfl) ⟨2129211, by rfl⟩ : syracuseStep 5677897 = 4258423) B4258423
theorem B7095113 : Blo 1399519 7095113 := bstep (se 2 (by rfl) ⟨2660667, by rfl⟩ : syracuseStep 7095113 = 5321335) B5321335
theorem B5981035 : Blo 1399519 5981035 := bstep (se 1 (by rfl) ⟨4485776, by rfl⟩ : syracuseStep 5981035 = 8971553) B8971553
theorem B3990455 : Blo 1399519 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B7980227 : Blo 1399519 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B15943229 : Blo 1399519 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B4728455 : Blo 1399519 4728455 := bstep (se 1 (by rfl) ⟨3546341, by rfl⟩ : syracuseStep 4728455 = 7092683) B7092683
theorem B4728509 : Blo 1399519 4728509 := bstep (se 3 (by rfl) ⟨886595, by rfl⟩ : syracuseStep 4728509 = 1773191) B1773191
theorem B1574599 : Blo 1399519 1574599 := bstep (se 1 (by rfl) ⟨1180949, by rfl⟩ : syracuseStep 1574599 = 2361899) B2361899
theorem B4728671 : Blo 1399519 4728671 := bstep (se 1 (by rfl) ⟨3546503, by rfl⟩ : syracuseStep 4728671 = 7093007) B7093007
theorem B5982113 : Blo 1399519 5982113 := bstep (se 2 (by rfl) ⟨2243292, by rfl⟩ : syracuseStep 5982113 = 4486585) B4486585
theorem B2525089 : Blo 1399519 2525089 := bstep (se 2 (by rfl) ⟨946908, by rfl⟩ : syracuseStep 2525089 = 1893817) B1893817
theorem B5113775 : Blo 1399519 5113775 := bstep (se 1 (by rfl) ⟨3835331, by rfl⟩ : syracuseStep 5113775 = 7670663) B7670663
theorem B4728833 : Blo 1399519 4728833 := bstep (se 2 (by rfl) ⟨1773312, by rfl⟩ : syracuseStep 4728833 = 3546625) B3546625
theorem B30279683 : Blo 1399519 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B4794383 : Blo 1399519 4794383 := bstep (se 1 (by rfl) ⟨3595787, by rfl⟩ : syracuseStep 4794383 = 7191575) B7191575
theorem B5982265 : Blo 1399519 5982265 := bstep (se 2 (by rfl) ⟨2243349, by rfl⟩ : syracuseStep 5982265 = 4486699) B4486699
theorem B5679161 : Blo 1399519 5679161 := bstep (se 2 (by rfl) ⟨2129685, by rfl⟩ : syracuseStep 5679161 = 4259371) B4259371
theorem B8636473 : Blo 1399519 8636473 := bstep (se 2 (by rfl) ⟨3238677, by rfl⟩ : syracuseStep 8636473 = 6477355) B6477355
theorem B2099279 : Blo 1399519 2099279 := bstep (se 1 (by rfl) ⟨1574459, by rfl⟩ : syracuseStep 2099279 = 3148919) B3148919
theorem B17934493 : Blo 1399519 17934493 := bstep (se 3 (by rfl) ⟨3362717, by rfl⟩ : syracuseStep 17934493 = 6725435) B6725435
theorem B2099399 : Blo 1399519 2099399 := bstep (se 1 (by rfl) ⟨1574549, by rfl⟩ : syracuseStep 2099399 = 3149099) B3149099
theorem B7088471 : Blo 1399519 7088471 := bstep (se 1 (by rfl) ⟨5316353, by rfl⟩ : syracuseStep 7088471 = 10632707) B10632707
theorem B2099561 : Blo 1399519 2099561 := bstep (se 2 (by rfl) ⟨787335, by rfl⟩ : syracuseStep 2099561 = 1574671) B1574671
theorem B1771951 : Blo 1399519 1771951 := bstep (se 1 (by rfl) ⟨1328963, by rfl⟩ : syracuseStep 1771951 = 2657927) B2657927
theorem B2099639 : Blo 1399519 2099639 := bstep (se 1 (by rfl) ⟨1574729, by rfl⟩ : syracuseStep 2099639 = 3149459) B3149459
theorem B2099675 : Blo 1399519 2099675 := bstep (se 1 (by rfl) ⟨1574756, by rfl⟩ : syracuseStep 2099675 = 3149513) B3149513
theorem B2361865 : Blo 1399519 2361865 := bstep (se 2 (by rfl) ⟨885699, by rfl⟩ : syracuseStep 2361865 = 1771399) B1771399
theorem B27273757 : Blo 1399519 27273757 := bstep (se 3 (by rfl) ⟨5113829, by rfl⟩ : syracuseStep 27273757 = 10227659) B10227659
theorem B1575463 : Blo 1399519 1575463 := bstep (se 1 (by rfl) ⟨1181597, by rfl⟩ : syracuseStep 1575463 = 2363195) B2363195
theorem B1419815 : Blo 1399519 1419815 := bstep (se 1 (by rfl) ⟨1064861, by rfl⟩ : syracuseStep 1419815 = 2129723) B2129723
theorem B5392955 : Blo 1399519 5392955 := bstep (se 1 (by rfl) ⟨4044716, by rfl⟩ : syracuseStep 5392955 = 8089433) B8089433
theorem B2362027 : Blo 1399519 2362027 := bstep (se 1 (by rfl) ⟨1771520, by rfl⟩ : syracuseStep 2362027 = 3543041) B3543041
theorem B5319377 : Blo 1399519 5319377 := bstep (se 2 (by rfl) ⟨1994766, by rfl⟩ : syracuseStep 5319377 = 3989533) B3989533
theorem B4729643 : Blo 1399519 4729643 := bstep (se 1 (by rfl) ⟨3547232, by rfl⟩ : syracuseStep 4729643 = 7094465) B7094465
theorem B10636109 : Blo 1399519 10636109 := bstep (se 3 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 10636109 = 3988541) B3988541
theorem B2100143 : Blo 1399519 2100143 := bstep (se 1 (by rfl) ⟨1575107, by rfl⟩ : syracuseStep 2100143 = 3150215) B3150215
theorem B3836855 : Blo 1399519 3836855 := bstep (se 1 (by rfl) ⟨2877641, by rfl⟩ : syracuseStep 3836855 = 5755283) B5755283
theorem B2362331 : Blo 1399519 2362331 := bstep (se 1 (by rfl) ⟨1771748, by rfl⟩ : syracuseStep 2362331 = 3543497) B3543497
theorem B26921969 : Blo 1399519 26921969 := bstep (se 2 (by rfl) ⟨10095738, by rfl⟩ : syracuseStep 26921969 = 20191477) B20191477
theorem B2100233 : Blo 1399519 2100233 := bstep (se 2 (by rfl) ⟨787587, by rfl⟩ : syracuseStep 2100233 = 1575175) B1575175
theorem B5319695 : Blo 1399519 5319695 := bstep (se 1 (by rfl) ⟨3989771, by rfl⟩ : syracuseStep 5319695 = 7979543) B7979543
theorem B2100263 : Blo 1399519 2100263 := bstep (se 1 (by rfl) ⟨1575197, by rfl⟩ : syracuseStep 2100263 = 3150395) B3150395
theorem B4729913 : Blo 1399519 4729913 := bstep (se 2 (by rfl) ⟨1773717, by rfl⟩ : syracuseStep 4729913 = 3547435) B3547435
theorem B2100347 : Blo 1399519 2100347 := bstep (se 1 (by rfl) ⟨1575260, by rfl⟩ : syracuseStep 2100347 = 3150521) B3150521
theorem B2362567 : Blo 1399519 2362567 := bstep (se 1 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 2362567 = 3543851) B3543851
theorem B2100473 : Blo 1399519 2100473 := bstep (se 2 (by rfl) ⟨787677, by rfl⟩ : syracuseStep 2100473 = 1575355) B1575355
theorem B2100575 : Blo 1399519 2100575 := bstep (se 1 (by rfl) ⟨1575431, by rfl⟩ : syracuseStep 2100575 = 3150863) B3150863
theorem B2362729 : Blo 1399519 2362729 := bstep (se 2 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 2362729 = 1772047) B1772047
theorem B2100587 : Blo 1399519 2100587 := bstep (se 1 (by rfl) ⟨1575440, by rfl⟩ : syracuseStep 2100587 = 3150881) B3150881
theorem B2395499 : Blo 1399519 2395499 := bstep (se 1 (by rfl) ⟨1796624, by rfl⟩ : syracuseStep 2395499 = 3593249) B3593249
theorem B1773019 : Blo 1399519 1773019 := bstep (se 1 (by rfl) ⟨1329764, by rfl⟩ : syracuseStep 1773019 = 2659529) B2659529
theorem B3149351 : Blo 1399519 3149351 := bstep (se 1 (by rfl) ⟨2362013, by rfl⟩ : syracuseStep 3149351 = 4724027) B4724027
theorem B2100815 : Blo 1399519 2100815 := bstep (se 1 (by rfl) ⟨1575611, by rfl⟩ : syracuseStep 2100815 = 3151223) B3151223
theorem B2100935 : Blo 1399519 2100935 := bstep (se 1 (by rfl) ⟨1575701, by rfl⟩ : syracuseStep 2100935 = 3151403) B3151403
theorem B20197187 : Blo 1399519 20197187 := bstep (se 1 (by rfl) ⟨15147890, by rfl⟩ : syracuseStep 20197187 = 30295781) B30295781
theorem B3542879 : Blo 1399519 3542879 := bstep (se 1 (by rfl) ⟨2657159, by rfl⟩ : syracuseStep 3542879 = 5314319) B5314319
theorem B2101097 : Blo 1399519 2101097 := bstep (se 2 (by rfl) ⟨787911, by rfl⟩ : syracuseStep 2101097 = 1575823) B1575823
theorem B3149675 : Blo 1399519 3149675 := bstep (se 1 (by rfl) ⟨2362256, by rfl⟩ : syracuseStep 3149675 = 4724513) B4724513
theorem B4484983 : Blo 1399519 4484983 := bstep (se 1 (by rfl) ⟨3363737, by rfl⟩ : syracuseStep 4484983 = 6727475) B6727475
theorem B2396047 : Blo 1399519 2396047 := bstep (se 1 (by rfl) ⟨1797035, by rfl⟩ : syracuseStep 2396047 = 3594071) B3594071
theorem B3149729 : Blo 1399519 3149729 := bstep (se 2 (by rfl) ⟨1181148, by rfl⟩ : syracuseStep 3149729 = 2362297) B2362297
theorem B19165091 : Blo 1399519 19165091 := bstep (se 1 (by rfl) ⟨14373818, by rfl⟩ : syracuseStep 19165091 = 28747637) B28747637
theorem B2101175 : Blo 1399519 2101175 := bstep (se 1 (by rfl) ⟨1575881, by rfl⟩ : syracuseStep 2101175 = 3151763) B3151763
theorem B2363323 : Blo 1399519 2363323 := bstep (se 1 (by rfl) ⟨1772492, by rfl⟩ : syracuseStep 2363323 = 3544985) B3544985
theorem B2101211 : Blo 1399519 2101211 := bstep (se 1 (by rfl) ⟨1575908, by rfl⟩ : syracuseStep 2101211 = 3151817) B3151817
theorem B2363431 : Blo 1399519 2363431 := bstep (se 1 (by rfl) ⟨1772573, by rfl⟩ : syracuseStep 2363431 = 3545147) B3545147
theorem B17952947 : Blo 1399519 17952947 := bstep (se 1 (by rfl) ⟨13464710, by rfl⟩ : syracuseStep 17952947 = 26929421) B26929421
theorem B3150071 : Blo 1399519 3150071 := bstep (se 1 (by rfl) ⟨2362553, by rfl⟩ : syracuseStep 3150071 = 4725107) B4725107
theorem B11071849 : Blo 1399519 11071849 := bstep (se 2 (by rfl) ⟨4151943, by rfl⟩ : syracuseStep 11071849 = 8303887) B8303887
theorem B2363755 : Blo 1399519 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B1945963 : Blo 1399519 1945963 := bstep (se 1 (by rfl) ⟨1459472, by rfl⟩ : syracuseStep 1945963 = 2918945) B2918945
theorem B2101679 : Blo 1399519 2101679 := bstep (se 1 (by rfl) ⟨1576259, by rfl⟩ : syracuseStep 2101679 = 3152519) B3152519
theorem B6066697 : Blo 1399519 6066697 := bstep (se 2 (by rfl) ⟨2275011, by rfl⟩ : syracuseStep 6066697 = 4550023) B4550023
theorem B2101769 : Blo 1399519 2101769 := bstep (se 2 (by rfl) ⟨788163, by rfl⟩ : syracuseStep 2101769 = 1576327) B1576327
theorem B2101799 : Blo 1399519 2101799 := bstep (se 1 (by rfl) ⟨1576349, by rfl⟩ : syracuseStep 2101799 = 3152699) B3152699
theorem B1495631 : Blo 1399519 1495631 := bstep (se 1 (by rfl) ⟨1121723, by rfl⟩ : syracuseStep 1495631 = 2243447) B2243447
theorem B2101883 : Blo 1399519 2101883 := bstep (se 1 (by rfl) ⟨1576412, by rfl⟩ : syracuseStep 2101883 = 3152825) B3152825
theorem B2102009 : Blo 1399519 2102009 := bstep (se 2 (by rfl) ⟨788253, by rfl⟩ : syracuseStep 2102009 = 1576507) B1576507
theorem B3150665 : Blo 1399519 3150665 := bstep (se 2 (by rfl) ⟨1181499, by rfl⟩ : syracuseStep 3150665 = 2362999) B2362999
theorem B2102111 : Blo 1399519 2102111 := bstep (se 1 (by rfl) ⟨1576583, by rfl⟩ : syracuseStep 2102111 = 3153167) B3153167
theorem B2102123 : Blo 1399519 2102123 := bstep (se 1 (by rfl) ⟨1576592, by rfl⟩ : syracuseStep 2102123 = 3153185) B3153185
theorem B3543983 : Blo 1399519 3543983 := bstep (se 1 (by rfl) ⟨2657987, by rfl⟩ : syracuseStep 3543983 = 5315975) B5315975
theorem B8967095 : Blo 1399519 8967095 := bstep (se 1 (by rfl) ⟨6725321, by rfl⟩ : syracuseStep 8967095 = 13450643) B13450643
theorem B15152129 : Blo 1399519 15152129 := bstep (se 2 (by rfl) ⟨5682048, by rfl⟩ : syracuseStep 15152129 = 11364097) B11364097
theorem B2659385 : Blo 1399519 2659385 := bstep (se 2 (by rfl) ⟨997269, by rfl⟩ : syracuseStep 2659385 = 1994539) B1994539
theorem B4723865 : Blo 1399519 4723865 := bstep (se 2 (by rfl) ⟨1771449, by rfl⟩ : syracuseStep 4723865 = 3542899) B3542899
theorem B5682371 : Blo 1399519 5682371 := bstep (se 1 (by rfl) ⟨4261778, by rfl⟩ : syracuseStep 5682371 = 8523557) B8523557
theorem B10638539 : Blo 1399519 10638539 := bstep (se 1 (by rfl) ⟨7978904, by rfl⟩ : syracuseStep 10638539 = 15957809) B15957809
theorem B43119971 : Blo 1399519 43119971 := bstep (se 1 (by rfl) ⟨32339978, by rfl⟩ : syracuseStep 43119971 = 64679957) B64679957
theorem B2364815 : Blo 1399519 2364815 := bstep (se 1 (by rfl) ⟨1773611, by rfl⟩ : syracuseStep 2364815 = 3547223) B3547223
theorem B32765429 : Blo 1399519 32765429 := bstep (se 5 (by rfl) ⟨1535879, by rfl⟩ : syracuseStep 32765429 = 3071759) B3071759
theorem B3151457 : Blo 1399519 3151457 := bstep (se 2 (by rfl) ⟨1181796, by rfl⟩ : syracuseStep 3151457 = 2363593) B2363593
theorem B2242171 : Blo 1399519 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B2365051 : Blo 1399519 2365051 := bstep (se 1 (by rfl) ⟨1773788, by rfl⟩ : syracuseStep 2365051 = 3547577) B3547577
theorem B6059659 : Blo 1399519 6059659 := bstep (se 1 (by rfl) ⟨4544744, by rfl⟩ : syracuseStep 6059659 = 9089489) B9089489
theorem B3987083 : Blo 1399519 3987083 := bstep (se 1 (by rfl) ⟨2990312, by rfl⟩ : syracuseStep 3987083 = 5980625) B5980625
theorem B7092035 : Blo 1399519 7092035 := bstep (se 1 (by rfl) ⟨5319026, by rfl⟩ : syracuseStep 7092035 = 10638053) B10638053
theorem B7575457 : Blo 1399519 7575457 := bstep (se 2 (by rfl) ⟨2840796, by rfl⟩ : syracuseStep 7575457 = 5681593) B5681593
theorem B3151799 : Blo 1399519 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B3545167 : Blo 1399519 3545167 := bstep (se 1 (by rfl) ⟨2658875, by rfl⟩ : syracuseStep 3545167 = 5317751) B5317751
theorem B10631249 : Blo 1399519 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B4725053 : Blo 1399519 4725053 := bstep (se 3 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 4725053 = 1771895) B1771895
theorem B11508097 : Blo 1399519 11508097 := bstep (se 2 (by rfl) ⟨4315536, by rfl⟩ : syracuseStep 11508097 = 8631073) B8631073
theorem B2242991 : Blo 1399519 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B5315017 : Blo 1399519 5315017 := bstep (se 2 (by rfl) ⟨1993131, by rfl⟩ : syracuseStep 5315017 = 3986263) B3986263
theorem B3152393 : Blo 1399519 3152393 := bstep (se 2 (by rfl) ⟨1182147, by rfl⟩ : syracuseStep 3152393 = 2364295) B2364295
theorem B3365401 : Blo 1399519 3365401 := bstep (se 2 (by rfl) ⟨1262025, by rfl⟩ : syracuseStep 3365401 = 2524051) B2524051
theorem B5044769 : Blo 1399519 5044769 := bstep (se 2 (by rfl) ⟨1891788, by rfl⟩ : syracuseStep 5044769 = 3783577) B3783577
theorem B20183687 : Blo 1399519 20183687 := bstep (se 1 (by rfl) ⟨15137765, by rfl⟩ : syracuseStep 20183687 = 30275531) B30275531
theorem B4487815 : Blo 1399519 4487815 := bstep (se 1 (by rfl) ⟨3365861, by rfl⟩ : syracuseStep 4487815 = 6731723) B6731723
theorem B4487827 : Blo 1399519 4487827 := bstep (se 1 (by rfl) ⟨3365870, by rfl⟩ : syracuseStep 4487827 = 6731741) B6731741
theorem B4487879 : Blo 1399519 4487879 := bstep (se 1 (by rfl) ⟨3365909, by rfl⟩ : syracuseStep 4487879 = 6731819) B6731819
theorem B9099985 : Blo 1399519 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B3545815 : Blo 1399519 3545815 := bstep (se 1 (by rfl) ⟨2659361, by rfl⟩ : syracuseStep 3545815 = 5318723) B5318723
theorem B5315321 : Blo 1399519 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B1399591 : Blo 1399519 1399591 := bstep (se 1 (by rfl) ⟨1049693, by rfl⟩ : syracuseStep 1399591 = 2099387) B2099387
theorem B1399631 : Blo 1399519 1399631 := bstep (se 1 (by rfl) ⟨1049723, by rfl⟩ : syracuseStep 1399631 = 2099447) B2099447
theorem B1399647 : Blo 1399519 1399647 := bstep (se 1 (by rfl) ⟨1049735, by rfl⟩ : syracuseStep 1399647 = 2099471) B2099471
theorem B3152735 : Blo 1399519 3152735 := bstep (se 1 (by rfl) ⟨2364551, by rfl⟩ : syracuseStep 3152735 = 4729103) B4729103
theorem B1399675 : Blo 1399519 1399675 := bstep (se 1 (by rfl) ⟨1049756, by rfl⟩ : syracuseStep 1399675 = 2099513) B2099513
theorem B5315489 : Blo 1399519 5315489 := bstep (se 2 (by rfl) ⟨1993308, by rfl⟩ : syracuseStep 5315489 = 3986617) B3986617
theorem B3029935 : Blo 1399519 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B1399727 : Blo 1399519 1399727 := bstep (se 1 (by rfl) ⟨1049795, by rfl⟩ : syracuseStep 1399727 = 2099591) B2099591
theorem B5315503 : Blo 1399519 5315503 := bstep (se 1 (by rfl) ⟨3986627, by rfl⟩ : syracuseStep 5315503 = 7973255) B7973255
theorem B2128823 : Blo 1399519 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B1399751 : Blo 1399519 1399751 := bstep (se 1 (by rfl) ⟨1049813, by rfl⟩ : syracuseStep 1399751 = 2099627) B2099627
theorem B1399771 : Blo 1399519 1399771 := bstep (se 1 (by rfl) ⟨1049828, by rfl⟩ : syracuseStep 1399771 = 2099657) B2099657
theorem B3546119 : Blo 1399519 3546119 := bstep (se 1 (by rfl) ⟨2659589, by rfl⟩ : syracuseStep 3546119 = 5319179) B5319179
theorem B2989075 : Blo 1399519 2989075 := bstep (se 1 (by rfl) ⟨2241806, by rfl⟩ : syracuseStep 2989075 = 4483613) B4483613
theorem B3152915 : Blo 1399519 3152915 := bstep (se 1 (by rfl) ⟨2364686, by rfl⟩ : syracuseStep 3152915 = 4729373) B4729373
theorem B1399847 : Blo 1399519 1399847 := bstep (se 1 (by rfl) ⟨1049885, by rfl⟩ : syracuseStep 1399847 = 2099771) B2099771
theorem B15342635 : Blo 1399519 15342635 := bstep (se 1 (by rfl) ⟨11506976, by rfl⟩ : syracuseStep 15342635 = 23013953) B23013953
theorem B1399887 : Blo 1399519 1399887 := bstep (se 1 (by rfl) ⟨1049915, by rfl⟩ : syracuseStep 1399887 = 2099831) B2099831
theorem B1399903 : Blo 1399519 1399903 := bstep (se 1 (by rfl) ⟨1049927, by rfl⟩ : syracuseStep 1399903 = 2099855) B2099855
theorem B1399931 : Blo 1399519 1399931 := bstep (se 1 (by rfl) ⟨1049948, by rfl⟩ : syracuseStep 1399931 = 2099897) B2099897
theorem B6732953 : Blo 1399519 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B4725917 : Blo 1399519 4725917 := bstep (se 3 (by rfl) ⟨886109, by rfl⟩ : syracuseStep 4725917 = 1772219) B1772219
theorem B1399983 : Blo 1399519 1399983 := bstep (se 1 (by rfl) ⟨1049987, by rfl⟩ : syracuseStep 1399983 = 2099975) B2099975
theorem B1400007 : Blo 1399519 1400007 := bstep (se 1 (by rfl) ⟨1050005, by rfl⟩ : syracuseStep 1400007 = 2100011) B2100011
theorem B1400027 : Blo 1399519 1400027 := bstep (se 1 (by rfl) ⟨1050020, by rfl⟩ : syracuseStep 1400027 = 2100041) B2100041
theorem B1400103 : Blo 1399519 1400103 := bstep (se 1 (by rfl) ⟨1050077, by rfl⟩ : syracuseStep 1400103 = 2100155) B2100155
theorem B1400143 : Blo 1399519 1400143 := bstep (se 1 (by rfl) ⟨1050107, by rfl⟩ : syracuseStep 1400143 = 2100215) B2100215
theorem B1400159 : Blo 1399519 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B3153257 : Blo 1399519 3153257 := bstep (se 2 (by rfl) ⟨1182471, by rfl⟩ : syracuseStep 3153257 = 2364943) B2364943
theorem B1400187 : Blo 1399519 1400187 := bstep (se 1 (by rfl) ⟨1050140, by rfl⟩ : syracuseStep 1400187 = 2100281) B2100281
theorem B5119361 : Blo 1399519 5119361 := bstep (se 2 (by rfl) ⟨1919760, by rfl⟩ : syracuseStep 5119361 = 3839521) B3839521
theorem B1400239 : Blo 1399519 1400239 := bstep (se 1 (by rfl) ⟨1050179, by rfl⟩ : syracuseStep 1400239 = 2100359) B2100359
theorem B2522551 : Blo 1399519 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1400263 : Blo 1399519 1400263 := bstep (se 1 (by rfl) ⟨1050197, by rfl⟩ : syracuseStep 1400263 = 2100395) B2100395
theorem B1400283 : Blo 1399519 1400283 := bstep (se 1 (by rfl) ⟨1050212, by rfl⟩ : syracuseStep 1400283 = 2100425) B2100425
theorem B7085555 : Blo 1399519 7085555 := bstep (se 1 (by rfl) ⟨5314166, by rfl⟩ : syracuseStep 7085555 = 10628333) B10628333
theorem B35888669 : Blo 1399519 35888669 := bstep (se 3 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 35888669 = 13458251) B13458251
theorem B1400359 : Blo 1399519 1400359 := bstep (se 1 (by rfl) ⟨1050269, by rfl⟩ : syracuseStep 1400359 = 2100539) B2100539
theorem B1400399 : Blo 1399519 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B1400415 : Blo 1399519 1400415 := bstep (se 1 (by rfl) ⟨1050311, by rfl⟩ : syracuseStep 1400415 = 2100623) B2100623
theorem B1400443 : Blo 1399519 1400443 := bstep (se 1 (by rfl) ⟨1050332, by rfl⟩ : syracuseStep 1400443 = 2100665) B2100665
theorem B1400495 : Blo 1399519 1400495 := bstep (se 1 (by rfl) ⟨1050371, by rfl⟩ : syracuseStep 1400495 = 2100743) B2100743
theorem B4726457 : Blo 1399519 4726457 := bstep (se 2 (by rfl) ⟨1772421, by rfl⟩ : syracuseStep 4726457 = 3544843) B3544843
theorem B1400519 : Blo 1399519 1400519 := bstep (se 1 (by rfl) ⟨1050389, by rfl⟩ : syracuseStep 1400519 = 2100779) B2100779
theorem B1400539 : Blo 1399519 1400539 := bstep (se 1 (by rfl) ⟨1050404, by rfl⟩ : syracuseStep 1400539 = 2100809) B2100809
theorem B27303685 : Blo 1399519 27303685 := bstep (se 4 (by rfl) ⟨2559720, by rfl⟩ : syracuseStep 27303685 = 5119441) B5119441
theorem B1400615 : Blo 1399519 1400615 := bstep (se 1 (by rfl) ⟨1050461, by rfl⟩ : syracuseStep 1400615 = 2100923) B2100923
theorem B1400655 : Blo 1399519 1400655 := bstep (se 1 (by rfl) ⟨1050491, by rfl⟩ : syracuseStep 1400655 = 2100983) B2100983
theorem B1400671 : Blo 1399519 1400671 := bstep (se 1 (by rfl) ⟨1050503, by rfl⟩ : syracuseStep 1400671 = 2101007) B2101007
theorem B4857695 : Blo 1399519 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B2129771 : Blo 1399519 2129771 := bstep (se 1 (by rfl) ⟨1597328, by rfl⟩ : syracuseStep 2129771 = 3194657) B3194657
theorem B5316461 : Blo 1399519 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B1400699 : Blo 1399519 1400699 := bstep (se 1 (by rfl) ⟨1050524, by rfl⟩ : syracuseStep 1400699 = 2101049) B2101049
theorem B13451143 : Blo 1399519 13451143 := bstep (se 1 (by rfl) ⟨10088357, by rfl⟩ : syracuseStep 13451143 = 20176715) B20176715
theorem B1400751 : Blo 1399519 1400751 := bstep (se 1 (by rfl) ⟨1050563, by rfl⟩ : syracuseStep 1400751 = 2101127) B2101127
theorem B1400775 : Blo 1399519 1400775 := bstep (se 1 (by rfl) ⟨1050581, by rfl⟩ : syracuseStep 1400775 = 2101163) B2101163
theorem B1400795 : Blo 1399519 1400795 := bstep (se 1 (by rfl) ⟨1050596, by rfl⟩ : syracuseStep 1400795 = 2101193) B2101193
theorem B10092595 : Blo 1399519 10092595 := bstep (se 1 (by rfl) ⟨7569446, by rfl⟩ : syracuseStep 10092595 = 15138893) B15138893
theorem B4726889 : Blo 1399519 4726889 := bstep (se 2 (by rfl) ⟨1772583, by rfl⟩ : syracuseStep 4726889 = 3545167) B3545167
theorem B11968631 : Blo 1399519 11968631 := bstep (se 1 (by rfl) ⟨8976473, by rfl⟩ : syracuseStep 11968631 = 17952947) B17952947
theorem B23912657 : Blo 1399519 23912657 := bstep (se 2 (by rfl) ⟨8967246, by rfl⟩ : syracuseStep 23912657 = 17934493) B17934493
theorem B1401119 : Blo 1399519 1401119 := bstep (se 1 (by rfl) ⟨1050839, by rfl⟩ : syracuseStep 1401119 = 2101679) B2101679
theorem B1401179 : Blo 1399519 1401179 := bstep (se 1 (by rfl) ⟨1050884, by rfl⟩ : syracuseStep 1401179 = 2101769) B2101769
theorem B1401199 : Blo 1399519 1401199 := bstep (se 1 (by rfl) ⟨1050899, by rfl⟩ : syracuseStep 1401199 = 2101799) B2101799
theorem B1401255 : Blo 1399519 1401255 := bstep (se 1 (by rfl) ⟨1050941, by rfl⟩ : syracuseStep 1401255 = 2101883) B2101883
theorem B81887705 : Blo 1399519 81887705 := bstep (se 2 (by rfl) ⟨30707889, by rfl⟩ : syracuseStep 81887705 = 61415779) B61415779
theorem B14762465 : Blo 1399519 14762465 := bstep (se 2 (by rfl) ⟨5535924, by rfl⟩ : syracuseStep 14762465 = 11071849) B11071849
theorem B1401339 : Blo 1399519 1401339 := bstep (se 1 (by rfl) ⟨1051004, by rfl⟩ : syracuseStep 1401339 = 2102009) B2102009
theorem B15344129 : Blo 1399519 15344129 := bstep (se 2 (by rfl) ⟨5754048, by rfl⟩ : syracuseStep 15344129 = 11508097) B11508097
theorem B1401407 : Blo 1399519 1401407 := bstep (se 1 (by rfl) ⟨1051055, by rfl⟩ : syracuseStep 1401407 = 2102111) B2102111
theorem B1401415 : Blo 1399519 1401415 := bstep (se 1 (by rfl) ⟨1051061, by rfl⟩ : syracuseStep 1401415 = 2102123) B2102123
theorem B7086689 : Blo 1399519 7086689 := bstep (se 2 (by rfl) ⟨2657508, by rfl⟩ : syracuseStep 7086689 = 5315017) B5315017
theorem B10101419 : Blo 1399519 10101419 := bstep (se 1 (by rfl) ⟨7576064, by rfl⟩ : syracuseStep 10101419 = 15152129) B15152129
theorem B36365009 : Blo 1399519 36365009 := bstep (se 2 (by rfl) ⟨13636878, by rfl⟩ : syracuseStep 36365009 = 27273757) B27273757
theorem B28746647 : Blo 1399519 28746647 := bstep (se 1 (by rfl) ⟨21559985, by rfl⟩ : syracuseStep 28746647 = 43119971) B43119971
theorem B12133313 : Blo 1399519 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B4727753 : Blo 1399519 4727753 := bstep (se 2 (by rfl) ⟨1772907, by rfl⟩ : syracuseStep 4727753 = 3545815) B3545815
theorem B7570529 : Blo 1399519 7570529 := bstep (se 2 (by rfl) ⟨2838948, by rfl⟩ : syracuseStep 7570529 = 5677897) B5677897
theorem B5981309 : Blo 1399519 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B4728023 : Blo 1399519 4728023 := bstep (se 1 (by rfl) ⟨3546017, by rfl⟩ : syracuseStep 4728023 = 7092035) B7092035
theorem B4039913 : Blo 1399519 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B7087337 : Blo 1399519 7087337 := bstep (se 2 (by rfl) ⟨2657751, by rfl⟩ : syracuseStep 7087337 = 5315503) B5315503
theorem B3409183 : Blo 1399519 3409183 := bstep (se 1 (by rfl) ⟨2556887, by rfl⟩ : syracuseStep 3409183 = 5113775) B5113775
theorem B20186455 : Blo 1399519 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B3196255 : Blo 1399519 3196255 := bstep (se 1 (by rfl) ⟨2397191, by rfl⟩ : syracuseStep 3196255 = 4794383) B4794383
theorem B3786107 : Blo 1399519 3786107 := bstep (se 1 (by rfl) ⟨2839580, by rfl⟩ : syracuseStep 3786107 = 5679161) B5679161
theorem B7087499 : Blo 1399519 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B3786173 : Blo 1399519 3786173 := bstep (se 3 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 3786173 = 1419815) B1419815
theorem B2991919 : Blo 1399519 2991919 := bstep (se 1 (by rfl) ⟨2243939, by rfl⟩ : syracuseStep 2991919 = 4487879) B4487879
theorem B1419215 : Blo 1399519 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B2557903 : Blo 1399519 2557903 := bstep (se 1 (by rfl) ⟨1918427, by rfl⟩ : syracuseStep 2557903 = 3836855) B3836855
theorem B1574887 : Blo 1399519 1574887 := bstep (se 1 (by rfl) ⟨1181165, by rfl⟩ : syracuseStep 1574887 = 2362331) B2362331
theorem B8079545 : Blo 1399519 8079545 := bstep (se 2 (by rfl) ⟨3029829, by rfl⟩ : syracuseStep 8079545 = 6059659) B6059659
theorem B2099465 : Blo 1399519 2099465 := bstep (se 2 (by rfl) ⟨787299, by rfl⟩ : syracuseStep 2099465 = 1574599) B1574599
theorem B5679389 : Blo 1399519 5679389 := bstep (se 3 (by rfl) ⟨1064885, by rfl⟩ : syracuseStep 5679389 = 2129771) B2129771
theorem B2099567 : Blo 1399519 2099567 := bstep (se 1 (by rfl) ⟨1574675, by rfl⟩ : syracuseStep 2099567 = 3149351) B3149351
theorem B17934857 : Blo 1399519 17934857 := bstep (se 2 (by rfl) ⟨6725571, by rfl⟩ : syracuseStep 17934857 = 13451143) B13451143
theorem B2361919 : Blo 1399519 2361919 := bstep (se 1 (by rfl) ⟨1771439, by rfl⟩ : syracuseStep 2361919 = 3542879) B3542879
theorem B3238463 : Blo 1399519 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B2099783 : Blo 1399519 2099783 := bstep (se 1 (by rfl) ⟨1574837, by rfl⟩ : syracuseStep 2099783 = 3149675) B3149675
theorem B2099819 : Blo 1399519 2099819 := bstep (se 1 (by rfl) ⟨1574864, by rfl⟩ : syracuseStep 2099819 = 3149729) B3149729
theorem B40913693 : Blo 1399519 40913693 := bstep (se 3 (by rfl) ⟨7671317, by rfl⟩ : syracuseStep 40913693 = 15342635) B15342635
theorem B28748611 : Blo 1399519 28748611 := bstep (se 1 (by rfl) ⟨21561458, by rfl⟩ : syracuseStep 28748611 = 43122917) B43122917
theorem B2100047 : Blo 1399519 2100047 := bstep (se 1 (by rfl) ⟨1575035, by rfl⟩ : syracuseStep 2100047 = 3150071) B3150071
theorem B1682407 : Blo 1399519 1682407 := bstep (se 1 (by rfl) ⟨1261805, by rfl⟩ : syracuseStep 1682407 = 2523611) B2523611
theorem B2100443 : Blo 1399519 2100443 := bstep (se 1 (by rfl) ⟨1575332, by rfl⟩ : syracuseStep 2100443 = 3150665) B3150665
theorem B4730075 : Blo 1399519 4730075 := bstep (se 1 (by rfl) ⟨3547556, by rfl⟩ : syracuseStep 4730075 = 7095113) B7095113
theorem B2362601 : Blo 1399519 2362601 := bstep (se 2 (by rfl) ⟨885975, by rfl⟩ : syracuseStep 2362601 = 1771951) B1771951
theorem B2362655 : Blo 1399519 2362655 := bstep (se 1 (by rfl) ⟨1771991, by rfl⟩ : syracuseStep 2362655 = 3543983) B3543983
theorem B3149153 : Blo 1399519 3149153 := bstep (se 2 (by rfl) ⟨1180932, by rfl⟩ : syracuseStep 3149153 = 2361865) B2361865
theorem B8088929 : Blo 1399519 8088929 := bstep (se 2 (by rfl) ⟨3033348, by rfl⟩ : syracuseStep 8088929 = 6066697) B6066697
theorem B1772923 : Blo 1399519 1772923 := bstep (se 1 (by rfl) ⟨1329692, by rfl⟩ : syracuseStep 1772923 = 2659385) B2659385
theorem B2100617 : Blo 1399519 2100617 := bstep (se 2 (by rfl) ⟨787731, by rfl⟩ : syracuseStep 2100617 = 1575463) B1575463
theorem B3149243 : Blo 1399519 3149243 := bstep (se 1 (by rfl) ⟨2361932, by rfl⟩ : syracuseStep 3149243 = 4723865) B4723865
theorem B5320151 : Blo 1399519 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B5983753 : Blo 1399519 5983753 := bstep (se 2 (by rfl) ⟨2243907, by rfl⟩ : syracuseStep 5983753 = 4487815) B4487815
theorem B5983769 : Blo 1399519 5983769 := bstep (se 2 (by rfl) ⟨2243913, by rfl⟩ : syracuseStep 5983769 = 4487827) B4487827
theorem B3149369 : Blo 1399519 3149369 := bstep (se 2 (by rfl) ⟨1181013, by rfl⟩ : syracuseStep 3149369 = 2362027) B2362027
theorem B1576543 : Blo 1399519 1576543 := bstep (se 1 (by rfl) ⟨1182407, by rfl⟩ : syracuseStep 1576543 = 2364815) B2364815
theorem B5680801 : Blo 1399519 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B10628819 : Blo 1399519 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B2100971 : Blo 1399519 2100971 := bstep (se 1 (by rfl) ⟨1575728, by rfl⟩ : syracuseStep 2100971 = 3151457) B3151457
theorem B7974713 : Blo 1399519 7974713 := bstep (se 2 (by rfl) ⟨2990517, by rfl⟩ : syracuseStep 7974713 = 5981035) B5981035
theorem B2101199 : Blo 1399519 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B3985433 : Blo 1399519 3985433 := bstep (se 2 (by rfl) ⟨1494537, by rfl⟩ : syracuseStep 3985433 = 2989075) B2989075
theorem B3150035 : Blo 1399519 3150035 := bstep (se 1 (by rfl) ⟨2362526, by rfl⟩ : syracuseStep 3150035 = 4725053) B4725053
theorem B3150089 : Blo 1399519 3150089 := bstep (se 2 (by rfl) ⟨1181283, by rfl⟩ : syracuseStep 3150089 = 2362567) B2362567
theorem B2101595 : Blo 1399519 2101595 := bstep (se 1 (by rfl) ⟨1576196, by rfl⟩ : syracuseStep 2101595 = 3152393) B3152393
theorem B3363179 : Blo 1399519 3363179 := bstep (se 1 (by rfl) ⟨2522384, by rfl⟩ : syracuseStep 3363179 = 5044769) B5044769
theorem B13455791 : Blo 1399519 13455791 := bstep (se 1 (by rfl) ⟨10091843, by rfl⟩ : syracuseStep 13455791 = 20183687) B20183687
theorem B3150305 : Blo 1399519 3150305 := bstep (se 2 (by rfl) ⟨1181364, by rfl⟩ : syracuseStep 3150305 = 2362729) B2362729
theorem B3543547 : Blo 1399519 3543547 := bstep (se 1 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 3543547 = 5315321) B5315321
theorem B7090739 : Blo 1399519 7090739 := bstep (se 1 (by rfl) ⟨5318054, by rfl⟩ : syracuseStep 7090739 = 10636109) B10636109
theorem B2101823 : Blo 1399519 2101823 := bstep (se 1 (by rfl) ⟨1576367, by rfl⟩ : syracuseStep 2101823 = 3152735) B3152735
theorem B3363401 : Blo 1399519 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B3543659 : Blo 1399519 3543659 := bstep (se 1 (by rfl) ⟨2657744, by rfl⟩ : syracuseStep 3543659 = 5315489) B5315489
theorem B2364025 : Blo 1399519 2364025 := bstep (se 2 (by rfl) ⟨886509, by rfl⟩ : syracuseStep 2364025 = 1773019) B1773019
theorem B2364079 : Blo 1399519 2364079 := bstep (se 1 (by rfl) ⟨1773059, by rfl⟩ : syracuseStep 2364079 = 3546119) B3546119
theorem B2101943 : Blo 1399519 2101943 := bstep (se 1 (by rfl) ⟨1576457, by rfl⟩ : syracuseStep 2101943 = 3152915) B3152915
theorem B3150611 : Blo 1399519 3150611 := bstep (se 1 (by rfl) ⟨2362958, by rfl⟩ : syracuseStep 3150611 = 4725917) B4725917
theorem B2102171 : Blo 1399519 2102171 := bstep (se 1 (by rfl) ⟨1576628, by rfl⟩ : syracuseStep 2102171 = 3153257) B3153257
theorem B3412907 : Blo 1399519 3412907 := bstep (se 1 (by rfl) ⟨2559680, by rfl⟩ : syracuseStep 3412907 = 5119361) B5119361
theorem B4723703 : Blo 1399519 4723703 := bstep (se 1 (by rfl) ⟨3542777, by rfl⟩ : syracuseStep 4723703 = 7085555) B7085555
theorem B23925779 : Blo 1399519 23925779 := bstep (se 1 (by rfl) ⟨17944334, by rfl⟩ : syracuseStep 23925779 = 35888669) B35888669
theorem B51106909 : Blo 1399519 51106909 := bstep (se 3 (by rfl) ⟨9582545, by rfl⟩ : syracuseStep 51106909 = 19165091) B19165091
theorem B3150971 : Blo 1399519 3150971 := bstep (se 1 (by rfl) ⟨2363228, by rfl⟩ : syracuseStep 3150971 = 4726457) B4726457
theorem B13464791 : Blo 1399519 13464791 := bstep (se 1 (by rfl) ⟨10098593, by rfl⟩ : syracuseStep 13464791 = 20197187) B20197187
theorem B3544307 : Blo 1399519 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B3151097 : Blo 1399519 3151097 := bstep (se 2 (by rfl) ⟨1181661, by rfl⟩ : syracuseStep 3151097 = 2363323) B2363323
theorem B13653373 : Blo 1399519 13653373 := bstep (se 3 (by rfl) ⟨2560007, by rfl⟩ : syracuseStep 13653373 = 5120015) B5120015
theorem B3151241 : Blo 1399519 3151241 := bstep (se 2 (by rfl) ⟨1181715, by rfl⟩ : syracuseStep 3151241 = 2363431) B2363431
theorem B7976353 : Blo 1399519 7976353 := bstep (se 2 (by rfl) ⟨2991132, by rfl⟩ : syracuseStep 7976353 = 5982265) B5982265
theorem B11515297 : Blo 1399519 11515297 := bstep (se 2 (by rfl) ⟨4318236, by rfl⟩ : syracuseStep 11515297 = 8636473) B8636473
theorem B3544519 : Blo 1399519 3544519 := bstep (se 1 (by rfl) ⟨2658389, by rfl⟩ : syracuseStep 3544519 = 5316779) B5316779
theorem B3151367 : Blo 1399519 3151367 := bstep (se 1 (by rfl) ⟨2363525, by rfl⟩ : syracuseStep 3151367 = 4727051) B4727051
theorem B16176647 : Blo 1399519 16176647 := bstep (se 1 (by rfl) ⟨12132485, by rfl⟩ : syracuseStep 16176647 = 24264971) B24264971
theorem B3151547 : Blo 1399519 3151547 := bstep (se 1 (by rfl) ⟨2363660, by rfl⟩ : syracuseStep 3151547 = 4727321) B4727321
theorem B3151673 : Blo 1399519 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B4724567 : Blo 1399519 4724567 := bstep (se 1 (by rfl) ⟨3543425, by rfl⟩ : syracuseStep 4724567 = 7086851) B7086851
theorem B15152989 : Blo 1399519 15152989 := bstep (se 3 (by rfl) ⟨2841185, by rfl⟩ : syracuseStep 15152989 = 5682371) B5682371
theorem B5978063 : Blo 1399519 5978063 := bstep (se 1 (by rfl) ⟨4483547, by rfl⟩ : syracuseStep 5978063 = 8967095) B8967095
theorem B2660303 : Blo 1399519 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B4487201 : Blo 1399519 4487201 := bstep (se 2 (by rfl) ⟨1682700, by rfl⟩ : syracuseStep 4487201 = 3365401) B3365401
theorem B7092359 : Blo 1399519 7092359 := bstep (se 1 (by rfl) ⟨5319269, by rfl⟩ : syracuseStep 7092359 = 10638539) B10638539
theorem B3987721 : Blo 1399519 3987721 := bstep (se 2 (by rfl) ⟨1495395, by rfl⟩ : syracuseStep 3987721 = 2990791) B2990791
theorem B6387997 : Blo 1399519 6387997 := bstep (se 3 (by rfl) ⟨1197749, by rfl⟩ : syracuseStep 6387997 = 2395499) B2395499
theorem B3152303 : Blo 1399519 3152303 := bstep (se 1 (by rfl) ⟨2364227, by rfl⟩ : syracuseStep 3152303 = 4728455) B4728455
theorem B3152339 : Blo 1399519 3152339 := bstep (se 1 (by rfl) ⟨2364254, by rfl⟩ : syracuseStep 3152339 = 4728509) B4728509
theorem B3152447 : Blo 1399519 3152447 := bstep (se 1 (by rfl) ⟨2364335, by rfl⟩ : syracuseStep 3152447 = 4728671) B4728671
theorem B3988075 : Blo 1399519 3988075 := bstep (se 1 (by rfl) ⟨2991056, by rfl⟩ : syracuseStep 3988075 = 5982113) B5982113
theorem B87374477 : Blo 1399519 87374477 := bstep (se 3 (by rfl) ⟨16382714, by rfl⟩ : syracuseStep 87374477 = 32765429) B32765429
theorem B3152555 : Blo 1399519 3152555 := bstep (se 1 (by rfl) ⟨2364416, by rfl⟩ : syracuseStep 3152555 = 4728833) B4728833
theorem B145619653 : Blo 1399519 145619653 := bstep (se 4 (by rfl) ⟨13651842, by rfl⟩ : syracuseStep 145619653 = 27303685) B27303685
theorem B1399519 : Blo 1399519 1399519 := bstep (se 1 (by rfl) ⟨1049639, by rfl⟩ : syracuseStep 1399519 = 2099279) B2099279
theorem B1399599 : Blo 1399519 1399599 := bstep (se 1 (by rfl) ⟨1049699, by rfl⟩ : syracuseStep 1399599 = 2099399) B2099399
theorem B3988349 : Blo 1399519 3988349 := bstep (se 3 (by rfl) ⟨747815, by rfl⟩ : syracuseStep 3988349 = 1495631) B1495631
theorem B4725647 : Blo 1399519 4725647 := bstep (se 1 (by rfl) ⟨3544235, by rfl⟩ : syracuseStep 4725647 = 7088471) B7088471
theorem B1399707 : Blo 1399519 1399707 := bstep (se 1 (by rfl) ⟨1049780, by rfl⟩ : syracuseStep 1399707 = 2099561) B2099561
theorem B1399759 : Blo 1399519 1399759 := bstep (se 1 (by rfl) ⟨1049819, by rfl⟩ : syracuseStep 1399759 = 2099639) B2099639
theorem B1399783 : Blo 1399519 1399783 := bstep (se 1 (by rfl) ⟨1049837, by rfl⟩ : syracuseStep 1399783 = 2099675) B2099675
theorem B10632221 : Blo 1399519 10632221 := bstep (se 3 (by rfl) ⟨1993541, by rfl⟩ : syracuseStep 10632221 = 3987083) B3987083
theorem B3595303 : Blo 1399519 3595303 := bstep (se 1 (by rfl) ⟨2696477, by rfl⟩ : syracuseStep 3595303 = 5392955) B5392955
theorem B3546251 : Blo 1399519 3546251 := bstep (se 1 (by rfl) ⟨2659688, by rfl⟩ : syracuseStep 3546251 = 5319377) B5319377
theorem B3153095 : Blo 1399519 3153095 := bstep (se 1 (by rfl) ⟨2364821, by rfl⟩ : syracuseStep 3153095 = 4729643) B4729643
theorem B10378469 : Blo 1399519 10378469 := bstep (se 4 (by rfl) ⟨972981, by rfl⟩ : syracuseStep 10378469 = 1945963) B1945963
theorem B1400095 : Blo 1399519 1400095 := bstep (se 1 (by rfl) ⟨1050071, by rfl⟩ : syracuseStep 1400095 = 2100143) B2100143
theorem B17947979 : Blo 1399519 17947979 := bstep (se 1 (by rfl) ⟨13460984, by rfl⟩ : syracuseStep 17947979 = 26921969) B26921969
theorem B1400155 : Blo 1399519 1400155 := bstep (se 1 (by rfl) ⟨1050116, by rfl⟩ : syracuseStep 1400155 = 2100233) B2100233
theorem B3546463 : Blo 1399519 3546463 := bstep (se 1 (by rfl) ⟨2659847, by rfl⟩ : syracuseStep 3546463 = 5319695) B5319695
theorem B1400175 : Blo 1399519 1400175 := bstep (se 1 (by rfl) ⟨1050131, by rfl⟩ : syracuseStep 1400175 = 2100263) B2100263
theorem B3153275 : Blo 1399519 3153275 := bstep (se 1 (by rfl) ⟨2364956, by rfl⟩ : syracuseStep 3153275 = 4729913) B4729913
theorem B1400231 : Blo 1399519 1400231 := bstep (se 1 (by rfl) ⟨1050173, by rfl⟩ : syracuseStep 1400231 = 2100347) B2100347
theorem B4488635 : Blo 1399519 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B2989561 : Blo 1399519 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B3153401 : Blo 1399519 3153401 := bstep (se 2 (by rfl) ⟨1182525, by rfl⟩ : syracuseStep 3153401 = 2365051) B2365051
theorem B1400315 : Blo 1399519 1400315 := bstep (se 1 (by rfl) ⟨1050236, by rfl⟩ : syracuseStep 1400315 = 2100473) B2100473
theorem B1400383 : Blo 1399519 1400383 := bstep (se 1 (by rfl) ⟨1050287, by rfl⟩ : syracuseStep 1400383 = 2100575) B2100575
theorem B1400391 : Blo 1399519 1400391 := bstep (se 1 (by rfl) ⟨1050293, by rfl⟩ : syracuseStep 1400391 = 2100587) B2100587
theorem B1400543 : Blo 1399519 1400543 := bstep (se 1 (by rfl) ⟨1050407, by rfl⟩ : syracuseStep 1400543 = 2100815) B2100815
theorem B1400623 : Blo 1399519 1400623 := bstep (se 1 (by rfl) ⟨1050467, by rfl⟩ : syracuseStep 1400623 = 2100935) B2100935
theorem B5979977 : Blo 1399519 5979977 := bstep (se 2 (by rfl) ⟨2242491, by rfl⟩ : syracuseStep 5979977 = 4484983) B4484983
theorem B3194729 : Blo 1399519 3194729 := bstep (se 2 (by rfl) ⟨1198023, by rfl⟩ : syracuseStep 3194729 = 2396047) B2396047
theorem B3366785 : Blo 1399519 3366785 := bstep (se 2 (by rfl) ⟨1262544, by rfl⟩ : syracuseStep 3366785 = 2525089) B2525089
theorem B10100609 : Blo 1399519 10100609 := bstep (se 2 (by rfl) ⟨3787728, by rfl⟩ : syracuseStep 10100609 = 7575457) B7575457
theorem B1400731 : Blo 1399519 1400731 := bstep (se 1 (by rfl) ⟨1050548, by rfl⟩ : syracuseStep 1400731 = 2101097) B2101097
theorem B1400783 : Blo 1399519 1400783 := bstep (se 1 (by rfl) ⟨1050587, by rfl⟩ : syracuseStep 1400783 = 2101175) B2101175
theorem B1400807 : Blo 1399519 1400807 := bstep (se 1 (by rfl) ⟨1050605, by rfl⟩ : syracuseStep 1400807 = 2101211) B2101211
theorem B7979087 : Blo 1399519 7979087 := bstep (se 1 (by rfl) ⟨5984315, by rfl⟩ : syracuseStep 7979087 = 11968631) B11968631
theorem B15941771 : Blo 1399519 15941771 := bstep (se 1 (by rfl) ⟨11956328, by rfl⟩ : syracuseStep 15941771 = 23912657) B23912657
theorem B1401063 : Blo 1399519 1401063 := bstep (se 1 (by rfl) ⟨1050797, by rfl⟩ : syracuseStep 1401063 = 2101595) B2101595
theorem B8970527 : Blo 1399519 8970527 := bstep (se 1 (by rfl) ⟨6727895, by rfl⟩ : syracuseStep 8970527 = 13455791) B13455791
theorem B54591803 : Blo 1399519 54591803 := bstep (se 1 (by rfl) ⟨40943852, by rfl⟩ : syracuseStep 54591803 = 81887705) B81887705
theorem B5316961 : Blo 1399519 5316961 := bstep (se 2 (by rfl) ⟨1993860, by rfl⟩ : syracuseStep 5316961 = 3987721) B3987721
theorem B4727159 : Blo 1399519 4727159 := bstep (se 1 (by rfl) ⟨3545369, by rfl⟩ : syracuseStep 4727159 = 7090739) B7090739
theorem B1401215 : Blo 1399519 1401215 := bstep (se 1 (by rfl) ⟨1050911, by rfl⟩ : syracuseStep 1401215 = 2101823) B2101823
theorem B6734279 : Blo 1399519 6734279 := bstep (se 1 (by rfl) ⟨5050709, by rfl⟩ : syracuseStep 6734279 = 10101419) B10101419
theorem B1401295 : Blo 1399519 1401295 := bstep (se 1 (by rfl) ⟨1050971, by rfl⟩ : syracuseStep 1401295 = 2101943) B2101943
theorem B21545453 : Blo 1399519 21545453 := bstep (se 3 (by rfl) ⟨4039772, by rfl⟩ : syracuseStep 21545453 = 8079545) B8079545
theorem B1401447 : Blo 1399519 1401447 := bstep (se 1 (by rfl) ⟨1051085, by rfl⟩ : syracuseStep 1401447 = 2102171) B2102171
theorem B10773101 : Blo 1399519 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B15950519 : Blo 1399519 15950519 := bstep (se 1 (by rfl) ⟨11962889, by rfl⟩ : syracuseStep 15950519 = 23925779) B23925779
theorem B5047019 : Blo 1399519 5047019 := bstep (se 1 (by rfl) ⟨3785264, by rfl⟩ : syracuseStep 5047019 = 7570529) B7570529
theorem B5317433 : Blo 1399519 5317433 := bstep (se 2 (by rfl) ⟨1994037, by rfl⟩ : syracuseStep 5317433 = 3988075) B3988075
theorem B194159537 : Blo 1399519 194159537 := bstep (se 2 (by rfl) ⟨72809826, by rfl⟩ : syracuseStep 194159537 = 145619653) B145619653
theorem B2524115 : Blo 1399519 2524115 := bstep (se 1 (by rfl) ⟨1893086, by rfl⟩ : syracuseStep 2524115 = 3786173) B3786173
theorem B38331481 : Blo 1399519 38331481 := bstep (se 2 (by rfl) ⟨14374305, by rfl⟩ : syracuseStep 38331481 = 28748611) B28748611
theorem B11969693 : Blo 1399519 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B2991467 : Blo 1399519 2991467 := bstep (se 1 (by rfl) ⟨2243600, by rfl⟩ : syracuseStep 2991467 = 4487201) B4487201
theorem B4793737 : Blo 1399519 4793737 := bstep (se 2 (by rfl) ⟨1797651, by rfl⟩ : syracuseStep 4793737 = 3595303) B3595303
theorem B4728239 : Blo 1399519 4728239 := bstep (se 1 (by rfl) ⟨3546179, by rfl⟩ : syracuseStep 4728239 = 7092359) B7092359
theorem B68142545 : Blo 1399519 68142545 := bstep (se 2 (by rfl) ⟨25553454, by rfl⟩ : syracuseStep 68142545 = 51106909) B51106909
theorem B8635901 : Blo 1399519 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B3786259 : Blo 1399519 3786259 := bstep (se 1 (by rfl) ⟨2839694, by rfl⟩ : syracuseStep 3786259 = 5679389) B5679389
theorem B4728617 : Blo 1399519 4728617 := bstep (se 2 (by rfl) ⟨1773231, by rfl⟩ : syracuseStep 4728617 = 3546463) B3546463
theorem B4261673 : Blo 1399519 4261673 := bstep (se 2 (by rfl) ⟨1598127, by rfl⟩ : syracuseStep 4261673 = 3196255) B3196255
theorem B18204497 : Blo 1399519 18204497 := bstep (se 2 (by rfl) ⟨6826686, by rfl⟩ : syracuseStep 18204497 = 13653373) B13653373
theorem B10635137 : Blo 1399519 10635137 := bstep (se 2 (by rfl) ⟨3988176, by rfl⟩ : syracuseStep 10635137 = 7976353) B7976353
theorem B15353729 : Blo 1399519 15353729 := bstep (se 2 (by rfl) ⟨5757648, by rfl⟩ : syracuseStep 15353729 = 11515297) B11515297
theorem B7088147 : Blo 1399519 7088147 := bstep (se 1 (by rfl) ⟨5316110, by rfl⟩ : syracuseStep 7088147 = 10632221) B10632221
theorem B1575067 : Blo 1399519 1575067 := bstep (se 1 (by rfl) ⟨1181300, by rfl⟩ : syracuseStep 1575067 = 2362601) B2362601
theorem B1575103 : Blo 1399519 1575103 := bstep (se 1 (by rfl) ⟨1181327, by rfl⟩ : syracuseStep 1575103 = 2362655) B2362655
theorem B2099435 : Blo 1399519 2099435 := bstep (se 1 (by rfl) ⟨1574576, by rfl⟩ : syracuseStep 2099435 = 3149153) B3149153
theorem B5392619 : Blo 1399519 5392619 := bstep (se 1 (by rfl) ⟨4044464, by rfl⟩ : syracuseStep 5392619 = 8088929) B8088929
theorem B2099495 : Blo 1399519 2099495 := bstep (se 1 (by rfl) ⟨1574621, by rfl⟩ : syracuseStep 2099495 = 3149243) B3149243
theorem B2099579 : Blo 1399519 2099579 := bstep (se 1 (by rfl) ⟨1574684, by rfl⟩ : syracuseStep 2099579 = 3149369) B3149369
theorem B20203985 : Blo 1399519 20203985 := bstep (se 2 (by rfl) ⟨7576494, by rfl⟩ : syracuseStep 20203985 = 15152989) B15152989
theorem B3410537 : Blo 1399519 3410537 := bstep (se 2 (by rfl) ⟨1278951, by rfl⟩ : syracuseStep 3410537 = 2557903) B2557903
theorem B2099849 : Blo 1399519 2099849 := bstep (se 2 (by rfl) ⟨787443, by rfl⟩ : syracuseStep 2099849 = 1574887) B1574887
theorem B2656955 : Blo 1399519 2656955 := bstep (se 1 (by rfl) ⟨1992716, by rfl⟩ : syracuseStep 2656955 = 3985433) B3985433
theorem B2100023 : Blo 1399519 2100023 := bstep (se 1 (by rfl) ⟨1575017, by rfl⟩ : syracuseStep 2100023 = 3150035) B3150035
theorem B2100059 : Blo 1399519 2100059 := bstep (se 1 (by rfl) ⟨1575044, by rfl⟩ : syracuseStep 2100059 = 3150089) B3150089
theorem B9841643 : Blo 1399519 9841643 := bstep (se 1 (by rfl) ⟨7381232, by rfl⟩ : syracuseStep 9841643 = 14762465) B14762465
theorem B2100203 : Blo 1399519 2100203 := bstep (se 1 (by rfl) ⟨1575152, by rfl⟩ : syracuseStep 2100203 = 3150305) B3150305
theorem B2362439 : Blo 1399519 2362439 := bstep (se 1 (by rfl) ⟨1771829, by rfl⟩ : syracuseStep 2362439 = 3543659) B3543659
theorem B2100407 : Blo 1399519 2100407 := bstep (se 1 (by rfl) ⟨1575305, by rfl⟩ : syracuseStep 2100407 = 3150611) B3150611
theorem B27675917 : Blo 1399519 27675917 := bstep (se 3 (by rfl) ⟨5189234, by rfl⟩ : syracuseStep 27675917 = 10378469) B10378469
theorem B19164431 : Blo 1399519 19164431 := bstep (se 1 (by rfl) ⟨14373323, by rfl⟩ : syracuseStep 19164431 = 28746647) B28746647
theorem B8088875 : Blo 1399519 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B3149135 : Blo 1399519 3149135 := bstep (se 1 (by rfl) ⟨2361851, by rfl⟩ : syracuseStep 3149135 = 4723703) B4723703
theorem B2100647 : Blo 1399519 2100647 := bstep (se 1 (by rfl) ⟨1575485, by rfl⟩ : syracuseStep 2100647 = 3150971) B3150971
theorem B3149225 : Blo 1399519 3149225 := bstep (se 2 (by rfl) ⟨1180959, by rfl⟩ : syracuseStep 3149225 = 2361919) B2361919
theorem B2362871 : Blo 1399519 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B2100731 : Blo 1399519 2100731 := bstep (se 1 (by rfl) ⟨1575548, by rfl⟩ : syracuseStep 2100731 = 3151097) B3151097
theorem B2100827 : Blo 1399519 2100827 := bstep (se 1 (by rfl) ⟨1575620, by rfl⟩ : syracuseStep 2100827 = 3151241) B3151241
theorem B2100911 : Blo 1399519 2100911 := bstep (se 1 (by rfl) ⟨1575683, by rfl⟩ : syracuseStep 2100911 = 3151367) B3151367
theorem B10784431 : Blo 1399519 10784431 := bstep (se 1 (by rfl) ⟨8088323, by rfl⟩ : syracuseStep 10784431 = 16176647) B16176647
theorem B2101031 : Blo 1399519 2101031 := bstep (se 1 (by rfl) ⟨1575773, by rfl⟩ : syracuseStep 2101031 = 3151547) B3151547
theorem B2101115 : Blo 1399519 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B3149711 : Blo 1399519 3149711 := bstep (se 1 (by rfl) ⟨2362283, by rfl⟩ : syracuseStep 3149711 = 4724567) B4724567
theorem B3985375 : Blo 1399519 3985375 := bstep (se 1 (by rfl) ⟨2989031, by rfl⟩ : syracuseStep 3985375 = 5978063) B5978063
theorem B2101535 : Blo 1399519 2101535 := bstep (se 1 (by rfl) ⟨1576151, by rfl⟩ : syracuseStep 2101535 = 3152303) B3152303
theorem B2101559 : Blo 1399519 2101559 := bstep (se 1 (by rfl) ⟨1576169, by rfl⟩ : syracuseStep 2101559 = 3152339) B3152339
theorem B11956571 : Blo 1399519 11956571 := bstep (se 1 (by rfl) ⟨8967428, by rfl⟩ : syracuseStep 11956571 = 17934857) B17934857
theorem B2101631 : Blo 1399519 2101631 := bstep (se 1 (by rfl) ⟨1576223, by rfl⟩ : syracuseStep 2101631 = 3152447) B3152447
theorem B58249651 : Blo 1399519 58249651 := bstep (se 1 (by rfl) ⟨43687238, by rfl⟩ : syracuseStep 58249651 = 87374477) B87374477
theorem B2101703 : Blo 1399519 2101703 := bstep (se 1 (by rfl) ⟨1576277, by rfl⟩ : syracuseStep 2101703 = 3152555) B3152555
theorem B26915273 : Blo 1399519 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B2363897 : Blo 1399519 2363897 := bstep (se 2 (by rfl) ⟨886461, by rfl⟩ : syracuseStep 2363897 = 1772923) B1772923
theorem B27275795 : Blo 1399519 27275795 := bstep (se 1 (by rfl) ⟨20456846, by rfl⟩ : syracuseStep 27275795 = 40913693) B40913693
theorem B96973357 : Blo 1399519 96973357 := bstep (se 3 (by rfl) ⟨18182504, by rfl⟩ : syracuseStep 96973357 = 36365009) B36365009
theorem B2658899 : Blo 1399519 2658899 := bstep (se 1 (by rfl) ⟨1994174, by rfl⟩ : syracuseStep 2658899 = 3988349) B3988349
theorem B3150431 : Blo 1399519 3150431 := bstep (se 1 (by rfl) ⟨2362823, by rfl⟩ : syracuseStep 3150431 = 4725647) B4725647
theorem B3986081 : Blo 1399519 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B2364167 : Blo 1399519 2364167 := bstep (se 1 (by rfl) ⟨1773125, by rfl⟩ : syracuseStep 2364167 = 3546251) B3546251
theorem B2102057 : Blo 1399519 2102057 := bstep (se 2 (by rfl) ⟨788271, by rfl⟩ : syracuseStep 2102057 = 1576543) B1576543
theorem B2102063 : Blo 1399519 2102063 := bstep (se 1 (by rfl) ⟨1576547, by rfl⟩ : syracuseStep 2102063 = 3153095) B3153095
theorem B7574401 : Blo 1399519 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B11965319 : Blo 1399519 11965319 := bstep (se 1 (by rfl) ⟨8973989, by rfl⟩ : syracuseStep 11965319 = 17947979) B17947979
theorem B2102183 : Blo 1399519 2102183 := bstep (se 1 (by rfl) ⟨1576637, by rfl⟩ : syracuseStep 2102183 = 3153275) B3153275
theorem B2102267 : Blo 1399519 2102267 := bstep (se 1 (by rfl) ⟨1576700, by rfl⟩ : syracuseStep 2102267 = 3153401) B3153401
theorem B3986651 : Blo 1399519 3986651 := bstep (se 1 (by rfl) ⟨2989988, by rfl⟩ : syracuseStep 3986651 = 5979977) B5979977
theorem B13456793 : Blo 1399519 13456793 := bstep (se 2 (by rfl) ⟨5046297, by rfl⟩ : syracuseStep 13456793 = 10092595) B10092595
theorem B3151259 : Blo 1399519 3151259 := bstep (se 1 (by rfl) ⟨2363444, by rfl⟩ : syracuseStep 3151259 = 4726889) B4726889
theorem B10229419 : Blo 1399519 10229419 := bstep (se 1 (by rfl) ⟨7672064, by rfl⟩ : syracuseStep 10229419 = 15344129) B15344129
theorem B8517329 : Blo 1399519 8517329 := bstep (se 2 (by rfl) ⟨3193998, by rfl⟩ : syracuseStep 8517329 = 6387997) B6387997
theorem B4724459 : Blo 1399519 4724459 := bstep (se 1 (by rfl) ⟨3543344, by rfl⟩ : syracuseStep 4724459 = 7086689) B7086689
theorem B2275271 : Blo 1399519 2275271 := bstep (se 1 (by rfl) ⟨1706453, by rfl⟩ : syracuseStep 2275271 = 3412907) B3412907
theorem B3151835 : Blo 1399519 3151835 := bstep (se 1 (by rfl) ⟨2363876, by rfl⟩ : syracuseStep 3151835 = 4727753) B4727753
theorem B4724729 : Blo 1399519 4724729 := bstep (se 2 (by rfl) ⟨1771773, by rfl⟩ : syracuseStep 4724729 = 3543547) B3543547
theorem B3987539 : Blo 1399519 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B3152015 : Blo 1399519 3152015 := bstep (se 1 (by rfl) ⟨2364011, by rfl⟩ : syracuseStep 3152015 = 4728023) B4728023
theorem B8976527 : Blo 1399519 8976527 := bstep (se 1 (by rfl) ⟨6732395, by rfl⟩ : syracuseStep 8976527 = 13464791) B13464791
theorem B4724891 : Blo 1399519 4724891 := bstep (se 1 (by rfl) ⟨3543668, by rfl⟩ : syracuseStep 4724891 = 7087337) B7087337
theorem B3152033 : Blo 1399519 3152033 := bstep (se 2 (by rfl) ⟨1182012, by rfl⟩ : syracuseStep 3152033 = 2364025) B2364025
theorem B3152105 : Blo 1399519 3152105 := bstep (se 2 (by rfl) ⟨1182039, by rfl⟩ : syracuseStep 3152105 = 2364079) B2364079
theorem B4724999 : Blo 1399519 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B8968477 : Blo 1399519 8968477 := bstep (se 3 (by rfl) ⟨1681589, by rfl⟩ : syracuseStep 8968477 = 3363179) B3363179
theorem B40385141 : Blo 1399519 40385141 := bstep (se 5 (by rfl) ⟨1893053, by rfl⟩ : syracuseStep 40385141 = 3786107) B3786107
theorem B2243209 : Blo 1399519 2243209 := bstep (se 2 (by rfl) ⟨841203, by rfl⟩ : syracuseStep 2243209 = 1682407) B1682407
theorem B1399643 : Blo 1399519 1399643 := bstep (se 1 (by rfl) ⟨1049732, by rfl⟩ : syracuseStep 1399643 = 2099465) B2099465
theorem B8969069 : Blo 1399519 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B1399711 : Blo 1399519 1399711 := bstep (se 1 (by rfl) ⟨1049783, by rfl⟩ : syracuseStep 1399711 = 2099567) B2099567
theorem B4545577 : Blo 1399519 4545577 := bstep (se 2 (by rfl) ⟨1704591, by rfl⟩ : syracuseStep 4545577 = 3409183) B3409183
theorem B1399855 : Blo 1399519 1399855 := bstep (se 1 (by rfl) ⟨1049891, by rfl⟩ : syracuseStep 1399855 = 2099783) B2099783
theorem B1399879 : Blo 1399519 1399879 := bstep (se 1 (by rfl) ⟨1049909, by rfl⟩ : syracuseStep 1399879 = 2099819) B2099819
theorem B1400031 : Blo 1399519 1400031 := bstep (se 1 (by rfl) ⟨1050023, by rfl⟩ : syracuseStep 1400031 = 2100047) B2100047
theorem B4726025 : Blo 1399519 4726025 := bstep (se 2 (by rfl) ⟨1772259, by rfl⟩ : syracuseStep 4726025 = 3544519) B3544519
theorem B7978337 : Blo 1399519 7978337 := bstep (se 2 (by rfl) ⟨2991876, by rfl⟩ : syracuseStep 7978337 = 5983753) B5983753
theorem B1400295 : Blo 1399519 1400295 := bstep (se 1 (by rfl) ⟨1050221, by rfl⟩ : syracuseStep 1400295 = 2100443) B2100443
theorem B3153383 : Blo 1399519 3153383 := bstep (se 1 (by rfl) ⟨2365037, by rfl⟩ : syracuseStep 3153383 = 4730075) B4730075
theorem B1400411 : Blo 1399519 1400411 := bstep (se 1 (by rfl) ⟨1050308, by rfl⟩ : syracuseStep 1400411 = 2100617) B2100617
theorem B3546767 : Blo 1399519 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B3989179 : Blo 1399519 3989179 := bstep (se 1 (by rfl) ⟨2991884, by rfl⟩ : syracuseStep 3989179 = 5983769) B5983769
theorem B3989225 : Blo 1399519 3989225 := bstep (se 2 (by rfl) ⟨1495959, by rfl⟩ : syracuseStep 3989225 = 2991919) B2991919
theorem B7085879 : Blo 1399519 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B1400647 : Blo 1399519 1400647 := bstep (se 1 (by rfl) ⟨1050485, by rfl⟩ : syracuseStep 1400647 = 2100971) B2100971
theorem B5316475 : Blo 1399519 5316475 := bstep (se 1 (by rfl) ⟨3987356, by rfl⟩ : syracuseStep 5316475 = 7974713) B7974713
theorem B3784573 : Blo 1399519 3784573 := bstep (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) B1419215
theorem B7094141 : Blo 1399519 7094141 := bstep (se 3 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 7094141 = 2660303) B2660303
theorem B2129819 : Blo 1399519 2129819 := bstep (se 1 (by rfl) ⟨1597364, by rfl⟩ : syracuseStep 2129819 = 3194729) B3194729
theorem B2244523 : Blo 1399519 2244523 := bstep (se 1 (by rfl) ⟨1683392, by rfl⟩ : syracuseStep 2244523 = 3366785) B3366785
theorem B6733739 : Blo 1399519 6733739 := bstep (se 1 (by rfl) ⟨5050304, by rfl⟩ : syracuseStep 6733739 = 10100609) B10100609
theorem B1400799 : Blo 1399519 1400799 := bstep (se 1 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 1400799 = 2101199) B2101199
theorem B1401023 : Blo 1399519 1401023 := bstep (se 1 (by rfl) ⟨1050767, by rfl⟩ : syracuseStep 1401023 = 2101535) B2101535
theorem B1401039 : Blo 1399519 1401039 := bstep (se 1 (by rfl) ⟨1050779, by rfl⟩ : syracuseStep 1401039 = 2101559) B2101559
theorem B7971047 : Blo 1399519 7971047 := bstep (se 1 (by rfl) ⟨5978285, by rfl⟩ : syracuseStep 7971047 = 11956571) B11956571
theorem B1401087 : Blo 1399519 1401087 := bstep (se 1 (by rfl) ⟨1050815, by rfl⟩ : syracuseStep 1401087 = 2101631) B2101631
theorem B1401135 : Blo 1399519 1401135 := bstep (se 1 (by rfl) ⟨1050851, by rfl⟩ : syracuseStep 1401135 = 2101703) B2101703
theorem B4489519 : Blo 1399519 4489519 := bstep (se 1 (by rfl) ⟨3367139, by rfl⟩ : syracuseStep 4489519 = 6734279) B6734279
theorem B10633679 : Blo 1399519 10633679 := bstep (se 1 (by rfl) ⟨7975259, by rfl⟩ : syracuseStep 10633679 = 15950519) B15950519
theorem B1401371 : Blo 1399519 1401371 := bstep (se 1 (by rfl) ⟨1051028, by rfl⟩ : syracuseStep 1401371 = 2102057) B2102057
theorem B1401375 : Blo 1399519 1401375 := bstep (se 1 (by rfl) ⟨1051031, by rfl⟩ : syracuseStep 1401375 = 2102063) B2102063
theorem B1401455 : Blo 1399519 1401455 := bstep (se 1 (by rfl) ⟨1051091, by rfl⟩ : syracuseStep 1401455 = 2102183) B2102183
theorem B1401511 : Blo 1399519 1401511 := bstep (se 1 (by rfl) ⟨1051133, by rfl⟩ : syracuseStep 1401511 = 2102267) B2102267
theorem B23921405 : Blo 1399519 23921405 := bstep (se 3 (by rfl) ⟨4485263, by rfl⟩ : syracuseStep 23921405 = 8970527) B8970527
theorem B7979795 : Blo 1399519 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B2990945 : Blo 1399519 2990945 := bstep (se 2 (by rfl) ⟨1121604, by rfl⟩ : syracuseStep 2990945 = 2243209) B2243209
theorem B8971195 : Blo 1399519 8971195 := bstep (se 1 (by rfl) ⟨6728396, by rfl⟩ : syracuseStep 8971195 = 13456793) B13456793
theorem B5678219 : Blo 1399519 5678219 := bstep (se 1 (by rfl) ⟨4258664, by rfl⟩ : syracuseStep 5678219 = 8517329) B8517329
theorem B1516847 : Blo 1399519 1516847 := bstep (se 1 (by rfl) ⟨1137635, by rfl⟩ : syracuseStep 1516847 = 2275271) B2275271
theorem B23029069 : Blo 1399519 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B9094765 : Blo 1399519 9094765 := bstep (se 3 (by rfl) ⟨1705268, by rfl⟩ : syracuseStep 9094765 = 3410537) B3410537
theorem B22718069 : Blo 1399519 22718069 := bstep (se 5 (by rfl) ⟨1064909, by rfl⟩ : syracuseStep 22718069 = 2129819) B2129819
theorem B13469323 : Blo 1399519 13469323 := bstep (se 1 (by rfl) ⟨10101992, by rfl⟩ : syracuseStep 13469323 = 20203985) B20203985
theorem B1771303 : Blo 1399519 1771303 := bstep (se 1 (by rfl) ⟨1328477, by rfl⟩ : syracuseStep 1771303 = 2656955) B2656955
theorem B6391649 : Blo 1399519 6391649 := bstep (se 2 (by rfl) ⟨2396868, by rfl⟩ : syracuseStep 6391649 = 4793737) B4793737
theorem B5048345 : Blo 1399519 5048345 := bstep (se 2 (by rfl) ⟨1893129, by rfl⟩ : syracuseStep 5048345 = 3786259) B3786259
theorem B1574959 : Blo 1399519 1574959 := bstep (se 1 (by rfl) ⟨1181219, by rfl⟩ : syracuseStep 1574959 = 2362439) B2362439
theorem B18450611 : Blo 1399519 18450611 := bstep (se 1 (by rfl) ⟨13837958, by rfl⟩ : syracuseStep 18450611 = 27675917) B27675917
theorem B5392583 : Blo 1399519 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B2099423 : Blo 1399519 2099423 := bstep (se 1 (by rfl) ⟨1574567, by rfl⟩ : syracuseStep 2099423 = 3149135) B3149135
theorem B14379241 : Blo 1399519 14379241 := bstep (se 2 (by rfl) ⟨5392215, by rfl⟩ : syracuseStep 14379241 = 10784431) B10784431
theorem B5318891 : Blo 1399519 5318891 := bstep (se 1 (by rfl) ⟨3989168, by rfl⟩ : syracuseStep 5318891 = 7978337) B7978337
theorem B5318905 : Blo 1399519 5318905 := bstep (se 2 (by rfl) ⟨1994589, by rfl⟩ : syracuseStep 5318905 = 3989179) B3989179
theorem B2099483 : Blo 1399519 2099483 := bstep (se 1 (by rfl) ⟨1574612, by rfl⟩ : syracuseStep 2099483 = 3149225) B3149225
theorem B1575247 : Blo 1399519 1575247 := bstep (se 1 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 1575247 = 2362871) B2362871
theorem B7088633 : Blo 1399519 7088633 := bstep (se 2 (by rfl) ⟨2658237, by rfl⟩ : syracuseStep 7088633 = 5316475) B5316475
theorem B2992697 : Blo 1399519 2992697 := bstep (se 2 (by rfl) ⟨1122261, by rfl⟩ : syracuseStep 2992697 = 2244523) B2244523
theorem B4729427 : Blo 1399519 4729427 := bstep (se 1 (by rfl) ⟨3547070, by rfl⟩ : syracuseStep 4729427 = 7094141) B7094141
theorem B2099807 : Blo 1399519 2099807 := bstep (se 1 (by rfl) ⟨1574855, by rfl⟩ : syracuseStep 2099807 = 3149711) B3149711
theorem B5319391 : Blo 1399519 5319391 := bstep (se 1 (by rfl) ⟨3989543, by rfl⟩ : syracuseStep 5319391 = 7979087) B7979087
theorem B10627847 : Blo 1399519 10627847 := bstep (se 1 (by rfl) ⟨7970885, by rfl⟩ : syracuseStep 10627847 = 15941771) B15941771
theorem B2100089 : Blo 1399519 2100089 := bstep (se 2 (by rfl) ⟨787533, by rfl⟩ : syracuseStep 2100089 = 1575067) B1575067
theorem B24243077 : Blo 1399519 24243077 := bstep (se 4 (by rfl) ⟨2272788, by rfl⟩ : syracuseStep 24243077 = 4545577) B4545577
theorem B2100137 : Blo 1399519 2100137 := bstep (se 2 (by rfl) ⟨787551, by rfl⟩ : syracuseStep 2100137 = 1575103) B1575103
theorem B17943515 : Blo 1399519 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B1575931 : Blo 1399519 1575931 := bstep (se 1 (by rfl) ⟨1181948, by rfl⟩ : syracuseStep 1575931 = 2363897) B2363897
theorem B1772599 : Blo 1399519 1772599 := bstep (se 1 (by rfl) ⟨1329449, by rfl⟩ : syracuseStep 1772599 = 2658899) B2658899
theorem B2100287 : Blo 1399519 2100287 := bstep (se 1 (by rfl) ⟨1575215, by rfl⟩ : syracuseStep 2100287 = 3150431) B3150431
theorem B2657387 : Blo 1399519 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B7089281 : Blo 1399519 7089281 := bstep (se 2 (by rfl) ⟨2658480, by rfl⟩ : syracuseStep 7089281 = 5316961) B5316961
theorem B1576111 : Blo 1399519 1576111 := bstep (se 1 (by rfl) ⟨1182083, by rfl⟩ : syracuseStep 1576111 = 2364167) B2364167
theorem B1682743 : Blo 1399519 1682743 := bstep (se 1 (by rfl) ⟨1262057, by rfl⟩ : syracuseStep 1682743 = 2524115) B2524115
theorem B129297809 : Blo 1399519 129297809 := bstep (se 2 (by rfl) ⟨48486678, by rfl⟩ : syracuseStep 129297809 = 96973357) B96973357
theorem B2657767 : Blo 1399519 2657767 := bstep (se 1 (by rfl) ⟨1993325, by rfl⟩ : syracuseStep 2657767 = 3986651) B3986651
theorem B1994311 : Blo 1399519 1994311 := bstep (se 1 (by rfl) ⟨1495733, by rfl⟩ : syracuseStep 1994311 = 2991467) B2991467
theorem B2100839 : Blo 1399519 2100839 := bstep (se 1 (by rfl) ⟨1575629, by rfl⟩ : syracuseStep 2100839 = 3151259) B3151259
theorem B45428363 : Blo 1399519 45428363 := bstep (se 1 (by rfl) ⟨34071272, by rfl⟩ : syracuseStep 45428363 = 68142545) B68142545
theorem B3149639 : Blo 1399519 3149639 := bstep (se 1 (by rfl) ⟨2362229, by rfl⟩ : syracuseStep 3149639 = 4724459) B4724459
theorem B12136331 : Blo 1399519 12136331 := bstep (se 1 (by rfl) ⟨9102248, by rfl⟩ : syracuseStep 12136331 = 18204497) B18204497
theorem B7090091 : Blo 1399519 7090091 := bstep (se 1 (by rfl) ⟨5317568, by rfl⟩ : syracuseStep 7090091 = 10635137) B10635137
theorem B10235819 : Blo 1399519 10235819 := bstep (se 1 (by rfl) ⟨7676864, by rfl⟩ : syracuseStep 10235819 = 15353729) B15353729
theorem B57454541 : Blo 1399519 57454541 := bstep (se 3 (by rfl) ⟨10772726, by rfl⟩ : syracuseStep 57454541 = 21545453) B21545453
theorem B2101223 : Blo 1399519 2101223 := bstep (se 1 (by rfl) ⟨1575917, by rfl⟩ : syracuseStep 2101223 = 3151835) B3151835
theorem B3149819 : Blo 1399519 3149819 := bstep (se 1 (by rfl) ⟨2362364, by rfl⟩ : syracuseStep 3149819 = 4724729) B4724729
theorem B2658359 : Blo 1399519 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B2101343 : Blo 1399519 2101343 := bstep (se 1 (by rfl) ⟨1576007, by rfl⟩ : syracuseStep 2101343 = 3152015) B3152015
theorem B5984351 : Blo 1399519 5984351 := bstep (se 1 (by rfl) ⟨4488263, by rfl⟩ : syracuseStep 5984351 = 8976527) B8976527
theorem B3149927 : Blo 1399519 3149927 := bstep (se 1 (by rfl) ⟨2362445, by rfl⟩ : syracuseStep 3149927 = 4724891) B4724891
theorem B2101355 : Blo 1399519 2101355 := bstep (se 1 (by rfl) ⟨1576016, by rfl⟩ : syracuseStep 2101355 = 3152033) B3152033
theorem B2101403 : Blo 1399519 2101403 := bstep (se 1 (by rfl) ⟨1576052, by rfl⟩ : syracuseStep 2101403 = 3152105) B3152105
theorem B3149999 : Blo 1399519 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B26923427 : Blo 1399519 26923427 := bstep (se 1 (by rfl) ⟨20192570, by rfl⟩ : syracuseStep 26923427 = 40385141) B40385141
theorem B3150683 : Blo 1399519 3150683 := bstep (se 1 (by rfl) ⟨2363012, by rfl⟩ : syracuseStep 3150683 = 4726025) B4726025
theorem B12776287 : Blo 1399519 12776287 := bstep (se 1 (by rfl) ⟨9582215, by rfl⟩ : syracuseStep 12776287 = 19164431) B19164431
theorem B2102255 : Blo 1399519 2102255 := bstep (se 1 (by rfl) ⟨1576691, by rfl⟩ : syracuseStep 2102255 = 3153383) B3153383
theorem B2364511 : Blo 1399519 2364511 := bstep (se 1 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 2364511 = 3546767) B3546767
theorem B2659483 : Blo 1399519 2659483 := bstep (se 1 (by rfl) ⟨1994612, by rfl⟩ : syracuseStep 2659483 = 3989225) B3989225
theorem B4723919 : Blo 1399519 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B5313833 : Blo 1399519 5313833 := bstep (se 2 (by rfl) ⟨1992687, by rfl⟩ : syracuseStep 5313833 = 3985375) B3985375
theorem B36394535 : Blo 1399519 36394535 := bstep (se 1 (by rfl) ⟨27295901, by rfl⟩ : syracuseStep 36394535 = 54591803) B54591803
theorem B3151439 : Blo 1399519 3151439 := bstep (se 1 (by rfl) ⟨2363579, by rfl⟩ : syracuseStep 3151439 = 4727159) B4727159
theorem B18183863 : Blo 1399519 18183863 := bstep (se 1 (by rfl) ⟨13637897, by rfl⟩ : syracuseStep 18183863 = 27275795) B27275795
theorem B11957969 : Blo 1399519 11957969 := bstep (se 2 (by rfl) ⟨4484238, by rfl⟩ : syracuseStep 11957969 = 8968477) B8968477
theorem B7182067 : Blo 1399519 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B3364679 : Blo 1399519 3364679 := bstep (se 1 (by rfl) ⟨2523509, by rfl⟩ : syracuseStep 3364679 = 5047019) B5047019
theorem B3544955 : Blo 1399519 3544955 := bstep (se 1 (by rfl) ⟨2658716, by rfl⟩ : syracuseStep 3544955 = 5317433) B5317433
theorem B77666201 : Blo 1399519 77666201 := bstep (se 2 (by rfl) ⟨29124825, by rfl⟩ : syracuseStep 77666201 = 58249651) B58249651
theorem B7976879 : Blo 1399519 7976879 := bstep (se 1 (by rfl) ⟨5982659, by rfl⟩ : syracuseStep 7976879 = 11965319) B11965319
theorem B129439691 : Blo 1399519 129439691 := bstep (se 1 (by rfl) ⟨97079768, by rfl⟩ : syracuseStep 129439691 = 194159537) B194159537
theorem B54556901 : Blo 1399519 54556901 := bstep (se 4 (by rfl) ⟨5114709, by rfl⟩ : syracuseStep 54556901 = 10229419) B10229419
theorem B3152159 : Blo 1399519 3152159 := bstep (se 1 (by rfl) ⟨2364119, by rfl⟩ : syracuseStep 3152159 = 4728239) B4728239
theorem B10099201 : Blo 1399519 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B3152411 : Blo 1399519 3152411 := bstep (se 1 (by rfl) ⟨2364308, by rfl⟩ : syracuseStep 3152411 = 4728617) B4728617
theorem B2841115 : Blo 1399519 2841115 := bstep (se 1 (by rfl) ⟨2130836, by rfl⟩ : syracuseStep 2841115 = 4261673) B4261673
theorem B4725431 : Blo 1399519 4725431 := bstep (se 1 (by rfl) ⟨3544073, by rfl⟩ : syracuseStep 4725431 = 7088147) B7088147
theorem B51108641 : Blo 1399519 51108641 := bstep (se 2 (by rfl) ⟨19165740, by rfl⟩ : syracuseStep 51108641 = 38331481) B38331481
theorem B1399623 : Blo 1399519 1399623 := bstep (se 1 (by rfl) ⟨1049717, by rfl⟩ : syracuseStep 1399623 = 2099435) B2099435
theorem B3595079 : Blo 1399519 3595079 := bstep (se 1 (by rfl) ⟨2696309, by rfl⟩ : syracuseStep 3595079 = 5392619) B5392619
theorem B1399663 : Blo 1399519 1399663 := bstep (se 1 (by rfl) ⟨1049747, by rfl⟩ : syracuseStep 1399663 = 2099495) B2099495
theorem B1399719 : Blo 1399519 1399719 := bstep (se 1 (by rfl) ⟨1049789, by rfl⟩ : syracuseStep 1399719 = 2099579) B2099579
theorem B1399899 : Blo 1399519 1399899 := bstep (se 1 (by rfl) ⟨1049924, by rfl⟩ : syracuseStep 1399899 = 2099849) B2099849
theorem B1400015 : Blo 1399519 1400015 := bstep (se 1 (by rfl) ⟨1050011, by rfl⟩ : syracuseStep 1400015 = 2100023) B2100023
theorem B1400039 : Blo 1399519 1400039 := bstep (se 1 (by rfl) ⟨1050029, by rfl⟩ : syracuseStep 1400039 = 2100059) B2100059
theorem B5979379 : Blo 1399519 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B6561095 : Blo 1399519 6561095 := bstep (se 1 (by rfl) ⟨4920821, by rfl⟩ : syracuseStep 6561095 = 9841643) B9841643
theorem B1400135 : Blo 1399519 1400135 := bstep (se 1 (by rfl) ⟨1050101, by rfl⟩ : syracuseStep 1400135 = 2100203) B2100203
theorem B1400271 : Blo 1399519 1400271 := bstep (se 1 (by rfl) ⟨1050203, by rfl⟩ : syracuseStep 1400271 = 2100407) B2100407
theorem B1400431 : Blo 1399519 1400431 := bstep (se 1 (by rfl) ⟨1050323, by rfl⟩ : syracuseStep 1400431 = 2100647) B2100647
theorem B1400487 : Blo 1399519 1400487 := bstep (se 1 (by rfl) ⟨1050365, by rfl⟩ : syracuseStep 1400487 = 2100731) B2100731
theorem B1400551 : Blo 1399519 1400551 := bstep (se 1 (by rfl) ⟨1050413, by rfl⟩ : syracuseStep 1400551 = 2100827) B2100827
theorem B17956637 : Blo 1399519 17956637 := bstep (se 3 (by rfl) ⟨3366869, by rfl⟩ : syracuseStep 17956637 = 6733739) B6733739
theorem B1400607 : Blo 1399519 1400607 := bstep (se 1 (by rfl) ⟨1050455, by rfl⟩ : syracuseStep 1400607 = 2100911) B2100911
theorem B5046097 : Blo 1399519 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B1400687 : Blo 1399519 1400687 := bstep (se 1 (by rfl) ⟨1050515, by rfl⟩ : syracuseStep 1400687 = 2101031) B2101031
theorem B1400743 : Blo 1399519 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B1400895 : Blo 1399519 1400895 := bstep (se 1 (by rfl) ⟨1050671, by rfl⟩ : syracuseStep 1400895 = 2101343) B2101343
theorem B3989567 : Blo 1399519 3989567 := bstep (se 1 (by rfl) ⟨2992175, by rfl⟩ : syracuseStep 3989567 = 5984351) B5984351
theorem B1400903 : Blo 1399519 1400903 := bstep (se 1 (by rfl) ⟨1050677, by rfl⟩ : syracuseStep 1400903 = 2101355) B2101355
theorem B1400935 : Blo 1399519 1400935 := bstep (se 1 (by rfl) ⟨1050701, by rfl⟩ : syracuseStep 1400935 = 2101403) B2101403
theorem B17948951 : Blo 1399519 17948951 := bstep (se 1 (by rfl) ⟨13461713, by rfl⟩ : syracuseStep 17948951 = 26923427) B26923427
theorem B7086365 : Blo 1399519 7086365 := bstep (se 3 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 7086365 = 2657387) B2657387
theorem B1401503 : Blo 1399519 1401503 := bstep (se 1 (by rfl) ⟨1051127, by rfl⟩ : syracuseStep 1401503 = 2102255) B2102255
theorem B7971979 : Blo 1399519 7971979 := bstep (se 1 (by rfl) ⟨5978984, by rfl⟩ : syracuseStep 7971979 = 11957969) B11957969
theorem B4261099 : Blo 1399519 4261099 := bstep (se 1 (by rfl) ⟨3195824, by rfl⟩ : syracuseStep 4261099 = 6391649) B6391649
theorem B11961593 : Blo 1399519 11961593 := bstep (se 2 (by rfl) ⟨4485597, by rfl⟩ : syracuseStep 11961593 = 8971195) B8971195
theorem B5317919 : Blo 1399519 5317919 := bstep (se 1 (by rfl) ⟨3988439, by rfl⟩ : syracuseStep 5317919 = 7976879) B7976879
theorem B7972505 : Blo 1399519 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B30705425 : Blo 1399519 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B48490301 : Blo 1399519 48490301 := bstep (se 3 (by rfl) ⟨9091931, by rfl⟩ : syracuseStep 48490301 = 18183863) B18183863
theorem B34072427 : Blo 1399519 34072427 := bstep (se 1 (by rfl) ⟨25554320, by rfl⟩ : syracuseStep 34072427 = 51108641) B51108641
theorem B11962343 : Blo 1399519 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B12126353 : Blo 1399519 12126353 := bstep (se 2 (by rfl) ⟨4547382, by rfl⟩ : syracuseStep 12126353 = 9094765) B9094765
theorem B17959097 : Blo 1399519 17959097 := bstep (se 2 (by rfl) ⟨6734661, by rfl⟩ : syracuseStep 17959097 = 13469323) B13469323
theorem B8972477 : Blo 1399519 8972477 := bstep (se 3 (by rfl) ⟨1682339, by rfl⟩ : syracuseStep 8972477 = 3364679) B3364679
theorem B86198539 : Blo 1399519 86198539 := bstep (se 1 (by rfl) ⟨64648904, by rfl⟩ : syracuseStep 86198539 = 129297809) B129297809
theorem B2361737 : Blo 1399519 2361737 := bstep (se 2 (by rfl) ⟨885651, by rfl⟩ : syracuseStep 2361737 = 1771303) B1771303
theorem B6728129 : Blo 1399519 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B11971091 : Blo 1399519 11971091 := bstep (se 1 (by rfl) ⟨8978318, by rfl⟩ : syracuseStep 11971091 = 17956637) B17956637
theorem B2099759 : Blo 1399519 2099759 := bstep (se 1 (by rfl) ⟨1574819, by rfl⟩ : syracuseStep 2099759 = 3149639) B3149639
theorem B2099879 : Blo 1399519 2099879 := bstep (se 1 (by rfl) ⟨1574909, by rfl⟩ : syracuseStep 2099879 = 3149819) B3149819
theorem B2099945 : Blo 1399519 2099945 := bstep (se 2 (by rfl) ⟨787479, by rfl⟩ : syracuseStep 2099945 = 1574959) B1574959
theorem B2099951 : Blo 1399519 2099951 := bstep (se 1 (by rfl) ⟨1574963, by rfl⟩ : syracuseStep 2099951 = 3149927) B3149927
theorem B2099999 : Blo 1399519 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B7088957 : Blo 1399519 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B7089119 : Blo 1399519 7089119 := bstep (se 1 (by rfl) ⟨5316839, by rfl⟩ : syracuseStep 7089119 = 10633679) B10633679
theorem B19172321 : Blo 1399519 19172321 := bstep (se 2 (by rfl) ⟨7189620, by rfl⟩ : syracuseStep 19172321 = 14379241) B14379241
theorem B15141917 : Blo 1399519 15141917 := bstep (se 3 (by rfl) ⟨2839109, by rfl⟩ : syracuseStep 15141917 = 5678219) B5678219
theorem B2100329 : Blo 1399519 2100329 := bstep (se 2 (by rfl) ⟨787623, by rfl⟩ : syracuseStep 2100329 = 1575247) B1575247
theorem B5319863 : Blo 1399519 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B2100455 : Blo 1399519 2100455 := bstep (se 1 (by rfl) ⟨1575341, by rfl⟩ : syracuseStep 2100455 = 3150683) B3150683
theorem B3788153 : Blo 1399519 3788153 := bstep (se 2 (by rfl) ⟨1420557, by rfl⟩ : syracuseStep 3788153 = 2841115) B2841115
theorem B3149279 : Blo 1399519 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B3542555 : Blo 1399519 3542555 := bstep (se 1 (by rfl) ⟨2656916, by rfl⟩ : syracuseStep 3542555 = 5313833) B5313833
theorem B2100959 : Blo 1399519 2100959 := bstep (se 1 (by rfl) ⟨1575719, by rfl⟩ : syracuseStep 2100959 = 3151439) B3151439
theorem B17035049 : Blo 1399519 17035049 := bstep (se 2 (by rfl) ⟨6388143, by rfl⟩ : syracuseStep 17035049 = 12776287) B12776287
theorem B2363303 : Blo 1399519 2363303 := bstep (se 1 (by rfl) ⟨1772477, by rfl⟩ : syracuseStep 2363303 = 3544955) B3544955
theorem B51777467 : Blo 1399519 51777467 := bstep (se 1 (by rfl) ⟨38833100, by rfl⟩ : syracuseStep 51777467 = 77666201) B77666201
theorem B2101241 : Blo 1399519 2101241 := bstep (se 2 (by rfl) ⟨787965, by rfl⟩ : syracuseStep 2101241 = 1575931) B1575931
theorem B2363465 : Blo 1399519 2363465 := bstep (se 2 (by rfl) ⟨886299, by rfl⟩ : syracuseStep 2363465 = 1772599) B1772599
theorem B12300407 : Blo 1399519 12300407 := bstep (se 1 (by rfl) ⟨9225305, by rfl⟩ : syracuseStep 12300407 = 18450611) B18450611
theorem B2101439 : Blo 1399519 2101439 := bstep (se 1 (by rfl) ⟨1576079, by rfl⟩ : syracuseStep 2101439 = 3152159) B3152159
theorem B2101481 : Blo 1399519 2101481 := bstep (se 2 (by rfl) ⟨788055, by rfl⟩ : syracuseStep 2101481 = 1576111) B1576111
theorem B2101607 : Blo 1399519 2101607 := bstep (se 1 (by rfl) ⟨1576205, by rfl⟩ : syracuseStep 2101607 = 3152411) B3152411
theorem B1995131 : Blo 1399519 1995131 := bstep (se 1 (by rfl) ⟨1496348, by rfl⟩ : syracuseStep 1995131 = 2992697) B2992697
theorem B3150287 : Blo 1399519 3150287 := bstep (se 1 (by rfl) ⟨2362715, by rfl⟩ : syracuseStep 3150287 = 4725431) B4725431
theorem B2396719 : Blo 1399519 2396719 := bstep (se 1 (by rfl) ⟨1797539, by rfl⟩ : syracuseStep 2396719 = 3595079) B3595079
theorem B3543689 : Blo 1399519 3543689 := bstep (se 2 (by rfl) ⟨1328883, by rfl⟩ : syracuseStep 3543689 = 2657767) B2657767
theorem B2659081 : Blo 1399519 2659081 := bstep (se 2 (by rfl) ⟨997155, by rfl⟩ : syracuseStep 2659081 = 1994311) B1994311
theorem B7975853 : Blo 1399519 7975853 := bstep (se 3 (by rfl) ⟨1495472, by rfl⟩ : syracuseStep 7975853 = 2990945) B2990945
theorem B8090887 : Blo 1399519 8090887 := bstep (se 1 (by rfl) ⟨6068165, by rfl⟩ : syracuseStep 8090887 = 12136331) B12136331
theorem B38303027 : Blo 1399519 38303027 := bstep (se 1 (by rfl) ⟨28727270, by rfl⟩ : syracuseStep 38303027 = 57454541) B57454541
theorem B5314031 : Blo 1399519 5314031 := bstep (se 1 (by rfl) ⟨3985523, by rfl⟩ : syracuseStep 5314031 = 7971047) B7971047
theorem B7091873 : Blo 1399519 7091873 := bstep (se 2 (by rfl) ⟨2659452, by rfl⟩ : syracuseStep 7091873 = 5318905) B5318905
theorem B5986025 : Blo 1399519 5986025 := bstep (se 2 (by rfl) ⟨2244759, by rfl⟩ : syracuseStep 5986025 = 4489519) B4489519
theorem B15947603 : Blo 1399519 15947603 := bstep (se 1 (by rfl) ⟨11960702, by rfl⟩ : syracuseStep 15947603 = 23921405) B23921405
theorem B13465601 : Blo 1399519 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B4044925 : Blo 1399519 4044925 := bstep (se 3 (by rfl) ⟨758423, by rfl⟩ : syracuseStep 4044925 = 1516847) B1516847
theorem B17496253 : Blo 1399519 17496253 := bstep (se 3 (by rfl) ⟨3280547, by rfl⟩ : syracuseStep 17496253 = 6561095) B6561095
theorem B7092521 : Blo 1399519 7092521 := bstep (se 2 (by rfl) ⟨2659695, by rfl⟩ : syracuseStep 7092521 = 5319391) B5319391
theorem B24263023 : Blo 1399519 24263023 := bstep (se 1 (by rfl) ⟨18197267, by rfl⟩ : syracuseStep 24263023 = 36394535) B36394535
theorem B15145379 : Blo 1399519 15145379 := bstep (se 1 (by rfl) ⟨11359034, by rfl⟩ : syracuseStep 15145379 = 22718069) B22718069
theorem B86293127 : Blo 1399519 86293127 := bstep (se 1 (by rfl) ⟨64719845, by rfl⟩ : syracuseStep 86293127 = 129439691) B129439691
theorem B3365563 : Blo 1399519 3365563 := bstep (se 1 (by rfl) ⟨2524172, by rfl⟩ : syracuseStep 3365563 = 5048345) B5048345
theorem B3152681 : Blo 1399519 3152681 := bstep (se 2 (by rfl) ⟨1182255, by rfl⟩ : syracuseStep 3152681 = 2364511) B2364511
theorem B3595055 : Blo 1399519 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B1399615 : Blo 1399519 1399615 := bstep (se 1 (by rfl) ⟨1049711, by rfl⟩ : syracuseStep 1399615 = 2099423) B2099423
theorem B36371267 : Blo 1399519 36371267 := bstep (se 1 (by rfl) ⟨27278450, by rfl⟩ : syracuseStep 36371267 = 54556901) B54556901
theorem B3545927 : Blo 1399519 3545927 := bstep (se 1 (by rfl) ⟨2659445, by rfl⟩ : syracuseStep 3545927 = 5318891) B5318891
theorem B1399655 : Blo 1399519 1399655 := bstep (se 1 (by rfl) ⟨1049741, by rfl⟩ : syracuseStep 1399655 = 2099483) B2099483
theorem B3545977 : Blo 1399519 3545977 := bstep (se 2 (by rfl) ⟨1329741, by rfl⟩ : syracuseStep 3545977 = 2659483) B2659483
theorem B4725755 : Blo 1399519 4725755 := bstep (se 1 (by rfl) ⟨3544316, by rfl⟩ : syracuseStep 4725755 = 7088633) B7088633
theorem B3152951 : Blo 1399519 3152951 := bstep (se 1 (by rfl) ⟨2364713, by rfl⟩ : syracuseStep 3152951 = 4729427) B4729427
theorem B1399871 : Blo 1399519 1399871 := bstep (se 1 (by rfl) ⟨1049903, by rfl⟩ : syracuseStep 1399871 = 2099807) B2099807
theorem B2243657 : Blo 1399519 2243657 := bstep (se 2 (by rfl) ⟨841371, by rfl⟩ : syracuseStep 2243657 = 1682743) B1682743
theorem B7085231 : Blo 1399519 7085231 := bstep (se 1 (by rfl) ⟨5313923, by rfl⟩ : syracuseStep 7085231 = 10627847) B10627847
theorem B1400059 : Blo 1399519 1400059 := bstep (se 1 (by rfl) ⟨1050044, by rfl⟩ : syracuseStep 1400059 = 2100089) B2100089
theorem B16162051 : Blo 1399519 16162051 := bstep (se 1 (by rfl) ⟨12121538, by rfl⟩ : syracuseStep 16162051 = 24243077) B24243077
theorem B1400091 : Blo 1399519 1400091 := bstep (se 1 (by rfl) ⟨1050068, by rfl⟩ : syracuseStep 1400091 = 2100137) B2100137
theorem B1400191 : Blo 1399519 1400191 := bstep (se 1 (by rfl) ⟨1050143, by rfl⟩ : syracuseStep 1400191 = 2100287) B2100287
theorem B4726187 : Blo 1399519 4726187 := bstep (se 1 (by rfl) ⟨3544640, by rfl⟩ : syracuseStep 4726187 = 7089281) B7089281
theorem B9576089 : Blo 1399519 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B1400559 : Blo 1399519 1400559 := bstep (se 1 (by rfl) ⟨1050419, by rfl⟩ : syracuseStep 1400559 = 2100839) B2100839
theorem B30285575 : Blo 1399519 30285575 := bstep (se 1 (by rfl) ⟨22714181, by rfl⟩ : syracuseStep 30285575 = 45428363) B45428363
theorem B27295517 : Blo 1399519 27295517 := bstep (se 3 (by rfl) ⟨5117909, by rfl⟩ : syracuseStep 27295517 = 10235819) B10235819
theorem B4726727 : Blo 1399519 4726727 := bstep (se 1 (by rfl) ⟨3545045, by rfl⟩ : syracuseStep 4726727 = 7090091) B7090091
theorem B1400815 : Blo 1399519 1400815 := bstep (se 1 (by rfl) ⟨1050611, by rfl⟩ : syracuseStep 1400815 = 2101223) B2101223
theorem B40378445 : Blo 1399519 40378445 := bstep (se 3 (by rfl) ⟨7570958, by rfl⟩ : syracuseStep 40378445 = 15141917) B15141917
theorem B8200271 : Blo 1399519 8200271 := bstep (se 1 (by rfl) ⟨6150203, by rfl⟩ : syracuseStep 8200271 = 12300407) B12300407
theorem B1400959 : Blo 1399519 1400959 := bstep (se 1 (by rfl) ⟨1050719, by rfl⟩ : syracuseStep 1400959 = 2101439) B2101439
theorem B1400987 : Blo 1399519 1400987 := bstep (se 1 (by rfl) ⟨1050740, by rfl⟩ : syracuseStep 1400987 = 2101481) B2101481
theorem B1401071 : Blo 1399519 1401071 := bstep (se 1 (by rfl) ⟨1050803, by rfl⟩ : syracuseStep 1401071 = 2101607) B2101607
theorem B32350697 : Blo 1399519 32350697 := bstep (se 2 (by rfl) ⟨12131511, by rfl⟩ : syracuseStep 32350697 = 24263023) B24263023
theorem B38347253 : Blo 1399519 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B5317235 : Blo 1399519 5317235 := bstep (se 1 (by rfl) ⟨3987926, by rfl⟩ : syracuseStep 5317235 = 7975853) B7975853
theorem B3195625 : Blo 1399519 3195625 := bstep (se 2 (by rfl) ⟨1198359, by rfl⟩ : syracuseStep 3195625 = 2396719) B2396719
theorem B25535351 : Blo 1399519 25535351 := bstep (se 1 (by rfl) ⟨19151513, by rfl⟩ : syracuseStep 25535351 = 38303027) B38303027
theorem B4727915 : Blo 1399519 4727915 := bstep (se 1 (by rfl) ⟨3545936, by rfl⟩ : syracuseStep 4727915 = 7091873) B7091873
theorem B3990683 : Blo 1399519 3990683 := bstep (se 1 (by rfl) ⟨2993012, by rfl⟩ : syracuseStep 3990683 = 5986025) B5986025
theorem B4727969 : Blo 1399519 4727969 := bstep (se 2 (by rfl) ⟨1772988, by rfl⟩ : syracuseStep 4727969 = 3545977) B3545977
theorem B32326867 : Blo 1399519 32326867 := bstep (se 1 (by rfl) ⟨24245150, by rfl⟩ : syracuseStep 32326867 = 48490301) B48490301
theorem B5981651 : Blo 1399519 5981651 := bstep (se 1 (by rfl) ⟨4486238, by rfl⟩ : syracuseStep 5981651 = 8972477) B8972477
theorem B4728347 : Blo 1399519 4728347 := bstep (se 1 (by rfl) ⟨3546260, by rfl⟩ : syracuseStep 4728347 = 7092521) B7092521
theorem B1574491 : Blo 1399519 1574491 := bstep (se 1 (by rfl) ⟨1180868, by rfl⟩ : syracuseStep 1574491 = 2361737) B2361737
theorem B7980727 : Blo 1399519 7980727 := bstep (se 1 (by rfl) ⟨5985545, by rfl⟩ : syracuseStep 7980727 = 11971091) B11971091
theorem B12781547 : Blo 1399519 12781547 := bstep (se 1 (by rfl) ⟨9586160, by rfl⟩ : syracuseStep 12781547 = 19172321) B19172321
theorem B2525435 : Blo 1399519 2525435 := bstep (se 1 (by rfl) ⟨1894076, by rfl⟩ : syracuseStep 2525435 = 3788153) B3788153
theorem B90859805 : Blo 1399519 90859805 := bstep (se 3 (by rfl) ⟨17036213, by rfl⟩ : syracuseStep 90859805 = 34072427) B34072427
theorem B2099519 : Blo 1399519 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B2361703 : Blo 1399519 2361703 := bstep (se 1 (by rfl) ⟨1771277, by rfl⟩ : syracuseStep 2361703 = 3542555) B3542555
theorem B6384059 : Blo 1399519 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B18197011 : Blo 1399519 18197011 := bstep (se 1 (by rfl) ⟨13647758, by rfl⟩ : syracuseStep 18197011 = 27295517) B27295517
theorem B11356699 : Blo 1399519 11356699 := bstep (se 1 (by rfl) ⟨8517524, by rfl⟩ : syracuseStep 11356699 = 17035049) B17035049
theorem B1575535 : Blo 1399519 1575535 := bstep (se 1 (by rfl) ⟨1181651, by rfl⟩ : syracuseStep 1575535 = 2363303) B2363303
theorem B1575643 : Blo 1399519 1575643 := bstep (se 1 (by rfl) ⟨1181732, by rfl⟩ : syracuseStep 1575643 = 2363465) B2363465
theorem B5393233 : Blo 1399519 5393233 := bstep (se 2 (by rfl) ⟨2022462, by rfl⟩ : syracuseStep 5393233 = 4044925) B4044925
theorem B5983085 : Blo 1399519 5983085 := bstep (se 3 (by rfl) ⟨1121828, by rfl⟩ : syracuseStep 5983085 = 2243657) B2243657
theorem B2100191 : Blo 1399519 2100191 := bstep (se 1 (by rfl) ⟨1575143, by rfl⟩ : syracuseStep 2100191 = 3150287) B3150287
theorem B32336941 : Blo 1399519 32336941 := bstep (se 3 (by rfl) ⟨6063176, by rfl⟩ : syracuseStep 32336941 = 12126353) B12126353
theorem B2362459 : Blo 1399519 2362459 := bstep (se 1 (by rfl) ⟨1771844, by rfl⟩ : syracuseStep 2362459 = 3543689) B3543689
theorem B7974395 : Blo 1399519 7974395 := bstep (se 1 (by rfl) ⟨5980796, by rfl⟩ : syracuseStep 7974395 = 11961593) B11961593
theorem B5320349 : Blo 1399519 5320349 := bstep (se 3 (by rfl) ⟨997565, by rfl⟩ : syracuseStep 5320349 = 1995131) B1995131
theorem B3542687 : Blo 1399519 3542687 := bstep (se 1 (by rfl) ⟨2657015, by rfl⟩ : syracuseStep 3542687 = 5314031) B5314031
theorem B7974895 : Blo 1399519 7974895 := bstep (se 1 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 7974895 = 11962343) B11962343
theorem B11972731 : Blo 1399519 11972731 := bstep (se 1 (by rfl) ⟨8979548, by rfl⟩ : syracuseStep 11972731 = 17959097) B17959097
theorem B10629305 : Blo 1399519 10629305 := bstep (se 2 (by rfl) ⟨3985989, by rfl⟩ : syracuseStep 10629305 = 7971979) B7971979
theorem B10096919 : Blo 1399519 10096919 := bstep (se 1 (by rfl) ⟨7572689, by rfl⟩ : syracuseStep 10096919 = 15145379) B15145379
theorem B4485419 : Blo 1399519 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B5681465 : Blo 1399519 5681465 := bstep (se 2 (by rfl) ⟨2130549, by rfl⟩ : syracuseStep 5681465 = 4261099) B4261099
theorem B21549401 : Blo 1399519 21549401 := bstep (se 2 (by rfl) ⟨8081025, by rfl⟩ : syracuseStep 21549401 = 16162051) B16162051
theorem B57528751 : Blo 1399519 57528751 := bstep (se 1 (by rfl) ⟨43146563, by rfl⟩ : syracuseStep 57528751 = 86293127) B86293127
theorem B2101787 : Blo 1399519 2101787 := bstep (se 1 (by rfl) ⟨1576340, by rfl⟩ : syracuseStep 2101787 = 3152681) B3152681
theorem B2363951 : Blo 1399519 2363951 := bstep (se 1 (by rfl) ⟨1772963, by rfl⟩ : syracuseStep 2363951 = 3545927) B3545927
theorem B3150503 : Blo 1399519 3150503 := bstep (se 1 (by rfl) ⟨2362877, by rfl⟩ : syracuseStep 3150503 = 4725755) B4725755
theorem B2101967 : Blo 1399519 2101967 := bstep (se 1 (by rfl) ⟨1576475, by rfl⟩ : syracuseStep 2101967 = 3152951) B3152951
theorem B4723487 : Blo 1399519 4723487 := bstep (se 1 (by rfl) ⟨3542615, by rfl⟩ : syracuseStep 4723487 = 7085231) B7085231
theorem B3150791 : Blo 1399519 3150791 := bstep (se 1 (by rfl) ⟨2363093, by rfl⟩ : syracuseStep 3150791 = 4726187) B4726187
theorem B20190383 : Blo 1399519 20190383 := bstep (se 1 (by rfl) ⟨15142787, by rfl⟩ : syracuseStep 20190383 = 30285575) B30285575
theorem B34518311 : Blo 1399519 34518311 := bstep (se 1 (by rfl) ⟨25888733, by rfl⟩ : syracuseStep 34518311 = 51777467) B51777467
theorem B3151151 : Blo 1399519 3151151 := bstep (se 1 (by rfl) ⟨2363363, by rfl⟩ : syracuseStep 3151151 = 4726727) B4726727
theorem B2659711 : Blo 1399519 2659711 := bstep (se 1 (by rfl) ⟨1994783, by rfl⟩ : syracuseStep 2659711 = 3989567) B3989567
theorem B11965967 : Blo 1399519 11965967 := bstep (se 1 (by rfl) ⟨8974475, by rfl⟩ : syracuseStep 11965967 = 17948951) B17948951
theorem B4724243 : Blo 1399519 4724243 := bstep (se 1 (by rfl) ⟨3543182, by rfl⟩ : syracuseStep 4724243 = 7086365) B7086365
theorem B23328337 : Blo 1399519 23328337 := bstep (se 2 (by rfl) ⟨8748126, by rfl⟩ : syracuseStep 23328337 = 17496253) B17496253
theorem B114931385 : Blo 1399519 114931385 := bstep (se 2 (by rfl) ⟨43099269, by rfl⟩ : syracuseStep 114931385 = 86198539) B86198539
theorem B3545279 : Blo 1399519 3545279 := bstep (se 1 (by rfl) ⟨2658959, by rfl⟩ : syracuseStep 3545279 = 5317919) B5317919
theorem B4487417 : Blo 1399519 4487417 := bstep (se 2 (by rfl) ⟨1682781, by rfl⟩ : syracuseStep 4487417 = 3365563) B3365563
theorem B3545441 : Blo 1399519 3545441 := bstep (se 2 (by rfl) ⟨1329540, by rfl⟩ : syracuseStep 3545441 = 2659081) B2659081
theorem B5315003 : Blo 1399519 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B20470283 : Blo 1399519 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B10631735 : Blo 1399519 10631735 := bstep (se 1 (by rfl) ⟨7973801, by rfl⟩ : syracuseStep 10631735 = 15947603) B15947603
theorem B8977067 : Blo 1399519 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B10787849 : Blo 1399519 10787849 := bstep (se 2 (by rfl) ⟨4045443, by rfl⟩ : syracuseStep 10787849 = 8090887) B8090887
theorem B1399839 : Blo 1399519 1399839 := bstep (se 1 (by rfl) ⟨1049879, by rfl⟩ : syracuseStep 1399839 = 2099759) B2099759
theorem B1399919 : Blo 1399519 1399919 := bstep (se 1 (by rfl) ⟨1049939, by rfl⟩ : syracuseStep 1399919 = 2099879) B2099879
theorem B1399963 : Blo 1399519 1399963 := bstep (se 1 (by rfl) ⟨1049972, by rfl⟩ : syracuseStep 1399963 = 2099945) B2099945
theorem B1399967 : Blo 1399519 1399967 := bstep (se 1 (by rfl) ⟨1049975, by rfl⟩ : syracuseStep 1399967 = 2099951) B2099951
theorem B1399999 : Blo 1399519 1399999 := bstep (se 1 (by rfl) ⟨1049999, by rfl⟩ : syracuseStep 1399999 = 2099999) B2099999
theorem B4725971 : Blo 1399519 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B24247511 : Blo 1399519 24247511 := bstep (se 1 (by rfl) ⟨18185633, by rfl⟩ : syracuseStep 24247511 = 36371267) B36371267
theorem B4726079 : Blo 1399519 4726079 := bstep (se 1 (by rfl) ⟨3544559, by rfl⟩ : syracuseStep 4726079 = 7089119) B7089119
theorem B1400219 : Blo 1399519 1400219 := bstep (se 1 (by rfl) ⟨1050164, by rfl⟩ : syracuseStep 1400219 = 2100329) B2100329
theorem B3546575 : Blo 1399519 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B1400303 : Blo 1399519 1400303 := bstep (se 1 (by rfl) ⟨1050227, by rfl⟩ : syracuseStep 1400303 = 2100455) B2100455
theorem B1400639 : Blo 1399519 1400639 := bstep (se 1 (by rfl) ⟨1050479, by rfl⟩ : syracuseStep 1400639 = 2100959) B2100959
theorem B1400827 : Blo 1399519 1400827 := bstep (se 1 (by rfl) ⟨1050620, by rfl⟩ : syracuseStep 1400827 = 2101241) B2101241
theorem B26918963 : Blo 1399519 26918963 := bstep (se 1 (by rfl) ⟨20189222, by rfl⟩ : syracuseStep 26918963 = 40378445) B40378445
theorem B7086203 : Blo 1399519 7086203 := bstep (se 1 (by rfl) ⟨5314652, by rfl⟩ : syracuseStep 7086203 = 10629305) B10629305
theorem B2990279 : Blo 1399519 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B1401191 : Blo 1399519 1401191 := bstep (se 1 (by rfl) ⟨1050893, by rfl⟩ : syracuseStep 1401191 = 2101787) B2101787
theorem B1401311 : Blo 1399519 1401311 := bstep (se 1 (by rfl) ⟨1050983, by rfl⟩ : syracuseStep 1401311 = 2101967) B2101967
theorem B17023567 : Blo 1399519 17023567 := bstep (se 1 (by rfl) ⟨12767675, by rfl⟩ : syracuseStep 17023567 = 25535351) B25535351
theorem B13460255 : Blo 1399519 13460255 := bstep (se 1 (by rfl) ⟨10095191, by rfl⟩ : syracuseStep 13460255 = 20190383) B20190383
theorem B23012207 : Blo 1399519 23012207 := bstep (se 1 (by rfl) ⟨17259155, by rfl⟩ : syracuseStep 23012207 = 34518311) B34518311
theorem B4260833 : Blo 1399519 4260833 := bstep (se 2 (by rfl) ⟨1597812, by rfl⟩ : syracuseStep 4260833 = 3195625) B3195625
theorem B76620923 : Blo 1399519 76620923 := bstep (se 1 (by rfl) ⟨57465692, by rfl⟩ : syracuseStep 76620923 = 114931385) B114931385
theorem B8521031 : Blo 1399519 8521031 := bstep (se 1 (by rfl) ⟨6390773, by rfl⟩ : syracuseStep 8521031 = 12781547) B12781547
theorem B43115921 : Blo 1399519 43115921 := bstep (se 2 (by rfl) ⟨16168470, by rfl⟩ : syracuseStep 43115921 = 32336941) B32336941
theorem B2991611 : Blo 1399519 2991611 := bstep (se 1 (by rfl) ⟨2243708, by rfl⟩ : syracuseStep 2991611 = 4487417) B4487417
theorem B60573203 : Blo 1399519 60573203 := bstep (se 1 (by rfl) ⟨45429902, by rfl⟩ : syracuseStep 60573203 = 90859805) B90859805
theorem B7087823 : Blo 1399519 7087823 := bstep (se 1 (by rfl) ⟨5315867, by rfl⟩ : syracuseStep 7087823 = 10631735) B10631735
theorem B2099321 : Blo 1399519 2099321 := bstep (se 2 (by rfl) ⟨787245, by rfl⟩ : syracuseStep 2099321 = 1574491) B1574491
theorem B16165007 : Blo 1399519 16165007 := bstep (se 1 (by rfl) ⟨12123755, by rfl⟩ : syracuseStep 16165007 = 24247511) B24247511
theorem B2361791 : Blo 1399519 2361791 := bstep (se 1 (by rfl) ⟨1771343, by rfl⟩ : syracuseStep 2361791 = 3542687) B3542687
theorem B5466847 : Blo 1399519 5466847 := bstep (se 1 (by rfl) ⟨4100135, by rfl⟩ : syracuseStep 5466847 = 8200271) B8200271
theorem B3787643 : Blo 1399519 3787643 := bstep (se 1 (by rfl) ⟨2840732, by rfl⟩ : syracuseStep 3787643 = 5681465) B5681465
theorem B1575967 : Blo 1399519 1575967 := bstep (se 1 (by rfl) ⟨1181975, by rfl⟩ : syracuseStep 1575967 = 2363951) B2363951
theorem B2100335 : Blo 1399519 2100335 := bstep (se 1 (by rfl) ⟨1575251, by rfl⟩ : syracuseStep 2100335 = 3150503) B3150503
theorem B3148937 : Blo 1399519 3148937 := bstep (se 2 (by rfl) ⟨1180851, by rfl⟩ : syracuseStep 3148937 = 2361703) B2361703
theorem B3148991 : Blo 1399519 3148991 := bstep (se 1 (by rfl) ⟨2361743, by rfl⟩ : syracuseStep 3148991 = 4723487) B4723487
theorem B76705001 : Blo 1399519 76705001 := bstep (se 2 (by rfl) ⟨28764375, by rfl⟩ : syracuseStep 76705001 = 57528751) B57528751
theorem B2100527 : Blo 1399519 2100527 := bstep (se 1 (by rfl) ⟨1575395, by rfl⟩ : syracuseStep 2100527 = 3150791) B3150791
theorem B15142265 : Blo 1399519 15142265 := bstep (se 2 (by rfl) ⟨5678349, by rfl⟩ : syracuseStep 15142265 = 11356699) B11356699
theorem B2100713 : Blo 1399519 2100713 := bstep (se 2 (by rfl) ⟨787767, by rfl⟩ : syracuseStep 2100713 = 1575535) B1575535
theorem B2100767 : Blo 1399519 2100767 := bstep (se 1 (by rfl) ⟨1575575, by rfl⟩ : syracuseStep 2100767 = 3151151) B3151151
theorem B2100857 : Blo 1399519 2100857 := bstep (se 2 (by rfl) ⟨787821, by rfl⟩ : syracuseStep 2100857 = 1575643) B1575643
theorem B3149495 : Blo 1399519 3149495 := bstep (se 1 (by rfl) ⟨2362121, by rfl⟩ : syracuseStep 3149495 = 4724243) B4724243
theorem B3149945 : Blo 1399519 3149945 := bstep (se 2 (by rfl) ⟨1181229, by rfl⟩ : syracuseStep 3149945 = 2362459) B2362459
theorem B2363519 : Blo 1399519 2363519 := bstep (se 1 (by rfl) ⟨1772639, by rfl⟩ : syracuseStep 2363519 = 3545279) B3545279
theorem B1683623 : Blo 1399519 1683623 := bstep (se 1 (by rfl) ⟨1262717, by rfl⟩ : syracuseStep 1683623 = 2525435) B2525435
theorem B2363627 : Blo 1399519 2363627 := bstep (se 1 (by rfl) ⟨1772720, by rfl⟩ : syracuseStep 2363627 = 3545441) B3545441
theorem B43102489 : Blo 1399519 43102489 := bstep (se 2 (by rfl) ⟨16163433, by rfl⟩ : syracuseStep 43102489 = 32326867) B32326867
theorem B4256039 : Blo 1399519 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B3543335 : Blo 1399519 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B5984711 : Blo 1399519 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B3150647 : Blo 1399519 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B3150719 : Blo 1399519 3150719 := bstep (se 1 (by rfl) ⟨2363039, by rfl⟩ : syracuseStep 3150719 = 4726079) B4726079
theorem B15954893 : Blo 1399519 15954893 := bstep (se 3 (by rfl) ⟨2991542, by rfl⟩ : syracuseStep 15954893 = 5983085) B5983085
theorem B2364383 : Blo 1399519 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B15963641 : Blo 1399519 15963641 := bstep (se 2 (by rfl) ⟨5986365, by rfl⟩ : syracuseStep 15963641 = 11972731) B11972731
theorem B6731279 : Blo 1399519 6731279 := bstep (se 1 (by rfl) ⟨5048459, by rfl⟩ : syracuseStep 6731279 = 10096919) B10096919
theorem B14366267 : Blo 1399519 14366267 := bstep (se 1 (by rfl) ⟨10774700, by rfl⟩ : syracuseStep 14366267 = 21549401) B21549401
theorem B21567131 : Blo 1399519 21567131 := bstep (se 1 (by rfl) ⟨16175348, by rfl⟩ : syracuseStep 21567131 = 32350697) B32350697
theorem B25564835 : Blo 1399519 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B3544823 : Blo 1399519 3544823 := bstep (se 1 (by rfl) ⟨2658617, by rfl⟩ : syracuseStep 3544823 = 5317235) B5317235
theorem B24262681 : Blo 1399519 24262681 := bstep (se 2 (by rfl) ⟨9098505, by rfl⟩ : syracuseStep 24262681 = 18197011) B18197011
theorem B3151943 : Blo 1399519 3151943 := bstep (se 1 (by rfl) ⟨2363957, by rfl⟩ : syracuseStep 3151943 = 4727915) B4727915
theorem B2660455 : Blo 1399519 2660455 := bstep (se 1 (by rfl) ⟨1995341, by rfl⟩ : syracuseStep 2660455 = 3990683) B3990683
theorem B3151979 : Blo 1399519 3151979 := bstep (se 1 (by rfl) ⟨2363984, by rfl⟩ : syracuseStep 3151979 = 4727969) B4727969
theorem B3987767 : Blo 1399519 3987767 := bstep (se 1 (by rfl) ⟨2990825, by rfl⟩ : syracuseStep 3987767 = 5981651) B5981651
theorem B7977311 : Blo 1399519 7977311 := bstep (se 1 (by rfl) ⟨5982983, by rfl⟩ : syracuseStep 7977311 = 11965967) B11965967
theorem B3152231 : Blo 1399519 3152231 := bstep (se 1 (by rfl) ⟨2364173, by rfl⟩ : syracuseStep 3152231 = 4728347) B4728347
theorem B7190977 : Blo 1399519 7190977 := bstep (se 2 (by rfl) ⟨2696616, by rfl⟩ : syracuseStep 7190977 = 5393233) B5393233
theorem B1399679 : Blo 1399519 1399679 := bstep (se 1 (by rfl) ⟨1049759, by rfl⟩ : syracuseStep 1399679 = 2099519) B2099519
theorem B13646855 : Blo 1399519 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B3546281 : Blo 1399519 3546281 := bstep (se 2 (by rfl) ⟨1329855, by rfl⟩ : syracuseStep 3546281 = 2659711) B2659711
theorem B1400127 : Blo 1399519 1400127 := bstep (se 1 (by rfl) ⟨1050095, by rfl⟩ : syracuseStep 1400127 = 2100191) B2100191
theorem B7191899 : Blo 1399519 7191899 := bstep (se 1 (by rfl) ⟨5393924, by rfl⟩ : syracuseStep 7191899 = 10787849) B10787849
theorem B31104449 : Blo 1399519 31104449 := bstep (se 2 (by rfl) ⟨11664168, by rfl⟩ : syracuseStep 31104449 = 23328337) B23328337
theorem B10640969 : Blo 1399519 10640969 := bstep (se 2 (by rfl) ⟨3990363, by rfl⟩ : syracuseStep 10640969 = 7980727) B7980727
theorem B5316263 : Blo 1399519 5316263 := bstep (se 1 (by rfl) ⟨3987197, by rfl⟩ : syracuseStep 5316263 = 7974395) B7974395
theorem B3546899 : Blo 1399519 3546899 := bstep (se 1 (by rfl) ⟨2660174, by rfl⟩ : syracuseStep 3546899 = 5320349) B5320349
theorem B10633193 : Blo 1399519 10633193 := bstep (se 2 (by rfl) ⟨3987447, by rfl⟩ : syracuseStep 10633193 = 7974895) B7974895
theorem B32350241 : Blo 1399519 32350241 := bstep (se 2 (by rfl) ⟨12131340, by rfl⟩ : syracuseStep 32350241 = 24262681) B24262681
theorem B3547273 : Blo 1399519 3547273 := bstep (se 2 (by rfl) ⟨1330227, by rfl⟩ : syracuseStep 3547273 = 2660455) B2660455
theorem B3989807 : Blo 1399519 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B4489661 : Blo 1399519 4489661 := bstep (se 3 (by rfl) ⟨841811, by rfl⟩ : syracuseStep 4489661 = 1683623) B1683623
theorem B10642427 : Blo 1399519 10642427 := bstep (se 1 (by rfl) ⟨7981820, by rfl⟩ : syracuseStep 10642427 = 15963641) B15963641
theorem B9577511 : Blo 1399519 9577511 := bstep (se 1 (by rfl) ⟨7183133, by rfl⟩ : syracuseStep 9577511 = 14366267) B14366267
theorem B14378087 : Blo 1399519 14378087 := bstep (se 1 (by rfl) ⟨10783565, by rfl⟩ : syracuseStep 14378087 = 21567131) B21567131
theorem B5318207 : Blo 1399519 5318207 := bstep (se 1 (by rfl) ⟨3988655, by rfl⟩ : syracuseStep 5318207 = 7977311) B7977311
theorem B1574527 : Blo 1399519 1574527 := bstep (se 1 (by rfl) ⟨1180895, by rfl⟩ : syracuseStep 1574527 = 2361791) B2361791
theorem B2525095 : Blo 1399519 2525095 := bstep (se 1 (by rfl) ⟨1893821, by rfl⟩ : syracuseStep 2525095 = 3787643) B3787643
theorem B2099291 : Blo 1399519 2099291 := bstep (se 1 (by rfl) ⟨1574468, by rfl⟩ : syracuseStep 2099291 = 3148937) B3148937
theorem B2099327 : Blo 1399519 2099327 := bstep (se 1 (by rfl) ⟨1574495, by rfl⟩ : syracuseStep 2099327 = 3148991) B3148991
theorem B51136667 : Blo 1399519 51136667 := bstep (se 1 (by rfl) ⟨38352500, by rfl⟩ : syracuseStep 51136667 = 76705001) B76705001
theorem B4794599 : Blo 1399519 4794599 := bstep (se 1 (by rfl) ⟨3595949, by rfl⟩ : syracuseStep 4794599 = 7191899) B7191899
theorem B10094843 : Blo 1399519 10094843 := bstep (se 1 (by rfl) ⟨7571132, by rfl⟩ : syracuseStep 10094843 = 15142265) B15142265
theorem B20736299 : Blo 1399519 20736299 := bstep (se 1 (by rfl) ⟨15552224, by rfl⟩ : syracuseStep 20736299 = 31104449) B31104449
theorem B2099663 : Blo 1399519 2099663 := bstep (se 1 (by rfl) ⟨1574747, by rfl⟩ : syracuseStep 2099663 = 3149495) B3149495
theorem B7088795 : Blo 1399519 7088795 := bstep (se 1 (by rfl) ⟨5316596, by rfl⟩ : syracuseStep 7088795 = 10633193) B10633193
theorem B2099963 : Blo 1399519 2099963 := bstep (se 1 (by rfl) ⟨1574972, by rfl⟩ : syracuseStep 2099963 = 3149945) B3149945
theorem B1575679 : Blo 1399519 1575679 := bstep (se 1 (by rfl) ⟨1181759, by rfl⟩ : syracuseStep 1575679 = 2363519) B2363519
theorem B1993519 : Blo 1399519 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B1575751 : Blo 1399519 1575751 := bstep (se 1 (by rfl) ⟨1181813, by rfl⟩ : syracuseStep 1575751 = 2363627) B2363627
theorem B2837359 : Blo 1399519 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B2362223 : Blo 1399519 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B57469985 : Blo 1399519 57469985 := bstep (se 2 (by rfl) ⟨21551244, by rfl⟩ : syracuseStep 57469985 = 43102489) B43102489
theorem B8973503 : Blo 1399519 8973503 := bstep (se 1 (by rfl) ⟨6730127, by rfl⟩ : syracuseStep 8973503 = 13460255) B13460255
theorem B2100431 : Blo 1399519 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B2100479 : Blo 1399519 2100479 := bstep (se 1 (by rfl) ⟨1575359, by rfl⟩ : syracuseStep 2100479 = 3150719) B3150719
theorem B9587969 : Blo 1399519 9587969 := bstep (se 2 (by rfl) ⟨3595488, by rfl⟩ : syracuseStep 9587969 = 7190977) B7190977
theorem B10636595 : Blo 1399519 10636595 := bstep (se 1 (by rfl) ⟨7977446, by rfl⟩ : syracuseStep 10636595 = 15954893) B15954893
theorem B1576255 : Blo 1399519 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B51080615 : Blo 1399519 51080615 := bstep (se 1 (by rfl) ⟨38310461, by rfl⟩ : syracuseStep 51080615 = 76620923) B76620923
theorem B5680687 : Blo 1399519 5680687 := bstep (se 1 (by rfl) ⟨4260515, by rfl⟩ : syracuseStep 5680687 = 8521031) B8521031
theorem B40382135 : Blo 1399519 40382135 := bstep (se 1 (by rfl) ⟨30286601, by rfl⟩ : syracuseStep 40382135 = 60573203) B60573203
theorem B17043223 : Blo 1399519 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B2363215 : Blo 1399519 2363215 := bstep (se 1 (by rfl) ⟨1772411, by rfl⟩ : syracuseStep 2363215 = 3544823) B3544823
theorem B2101289 : Blo 1399519 2101289 := bstep (se 2 (by rfl) ⟨787983, by rfl⟩ : syracuseStep 2101289 = 1575967) B1575967
theorem B2101295 : Blo 1399519 2101295 := bstep (se 1 (by rfl) ⟨1575971, by rfl⟩ : syracuseStep 2101295 = 3151943) B3151943
theorem B2101319 : Blo 1399519 2101319 := bstep (se 1 (by rfl) ⟨1575989, by rfl⟩ : syracuseStep 2101319 = 3151979) B3151979
theorem B10776671 : Blo 1399519 10776671 := bstep (se 1 (by rfl) ⟨8082503, by rfl⟩ : syracuseStep 10776671 = 16165007) B16165007
theorem B2658511 : Blo 1399519 2658511 := bstep (se 1 (by rfl) ⟨1993883, by rfl⟩ : syracuseStep 2658511 = 3987767) B3987767
theorem B2101487 : Blo 1399519 2101487 := bstep (se 1 (by rfl) ⟨1576115, by rfl⟩ : syracuseStep 2101487 = 3152231) B3152231
theorem B9097903 : Blo 1399519 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B2364187 : Blo 1399519 2364187 := bstep (se 1 (by rfl) ⟨1773140, by rfl⟩ : syracuseStep 2364187 = 3546281) B3546281
theorem B3544175 : Blo 1399519 3544175 := bstep (se 1 (by rfl) ⟨2658131, by rfl⟩ : syracuseStep 3544175 = 5316263) B5316263
theorem B2364599 : Blo 1399519 2364599 := bstep (se 1 (by rfl) ⟨1773449, by rfl⟩ : syracuseStep 2364599 = 3546899) B3546899
theorem B17945975 : Blo 1399519 17945975 := bstep (se 1 (by rfl) ⟨13459481, by rfl⟩ : syracuseStep 17945975 = 26918963) B26918963
theorem B4724135 : Blo 1399519 4724135 := bstep (se 1 (by rfl) ⟨3543101, by rfl⟩ : syracuseStep 4724135 = 7086203) B7086203
theorem B15341471 : Blo 1399519 15341471 := bstep (se 1 (by rfl) ⟨11506103, by rfl⟩ : syracuseStep 15341471 = 23012207) B23012207
theorem B2840555 : Blo 1399519 2840555 := bstep (se 1 (by rfl) ⟨2130416, by rfl⟩ : syracuseStep 2840555 = 4260833) B4260833
theorem B22698089 : Blo 1399519 22698089 := bstep (se 2 (by rfl) ⟨8511783, by rfl⟩ : syracuseStep 22698089 = 17023567) B17023567
theorem B28743947 : Blo 1399519 28743947 := bstep (se 1 (by rfl) ⟨21557960, by rfl⟩ : syracuseStep 28743947 = 43115921) B43115921
theorem B7289129 : Blo 1399519 7289129 := bstep (se 2 (by rfl) ⟨2733423, by rfl⟩ : syracuseStep 7289129 = 5466847) B5466847
theorem B4487519 : Blo 1399519 4487519 := bstep (se 1 (by rfl) ⟨3365639, by rfl⟩ : syracuseStep 4487519 = 6731279) B6731279
theorem B4725215 : Blo 1399519 4725215 := bstep (se 1 (by rfl) ⟨3543911, by rfl⟩ : syracuseStep 4725215 = 7087823) B7087823
theorem B7977629 : Blo 1399519 7977629 := bstep (se 3 (by rfl) ⟨1495805, by rfl⟩ : syracuseStep 7977629 = 2991611) B2991611
theorem B1399547 : Blo 1399519 1399547 := bstep (se 1 (by rfl) ⟨1049660, by rfl⟩ : syracuseStep 1399547 = 2099321) B2099321
theorem B1400223 : Blo 1399519 1400223 := bstep (se 1 (by rfl) ⟨1050167, by rfl⟩ : syracuseStep 1400223 = 2100335) B2100335
theorem B1400351 : Blo 1399519 1400351 := bstep (se 1 (by rfl) ⟨1050263, by rfl⟩ : syracuseStep 1400351 = 2100527) B2100527
theorem B1400475 : Blo 1399519 1400475 := bstep (se 1 (by rfl) ⟨1050356, by rfl⟩ : syracuseStep 1400475 = 2100713) B2100713
theorem B1400511 : Blo 1399519 1400511 := bstep (se 1 (by rfl) ⟨1050383, by rfl⟩ : syracuseStep 1400511 = 2100767) B2100767
theorem B7093979 : Blo 1399519 7093979 := bstep (se 1 (by rfl) ⟨5320484, by rfl⟩ : syracuseStep 7093979 = 10640969) B10640969
theorem B1400571 : Blo 1399519 1400571 := bstep (se 1 (by rfl) ⟨1050428, by rfl⟩ : syracuseStep 1400571 = 2100857) B2100857
theorem B1400859 : Blo 1399519 1400859 := bstep (se 1 (by rfl) ⟨1050644, by rfl⟩ : syracuseStep 1400859 = 2101289) B2101289
theorem B1400863 : Blo 1399519 1400863 := bstep (se 1 (by rfl) ⟨1050647, by rfl⟩ : syracuseStep 1400863 = 2101295) B2101295
theorem B1400879 : Blo 1399519 1400879 := bstep (se 1 (by rfl) ⟨1050659, by rfl⟩ : syracuseStep 1400879 = 2101319) B2101319
theorem B7184447 : Blo 1399519 7184447 := bstep (se 1 (by rfl) ⟨5388335, by rfl⟩ : syracuseStep 7184447 = 10776671) B10776671
theorem B1400991 : Blo 1399519 1400991 := bstep (se 1 (by rfl) ⟨1050743, by rfl⟩ : syracuseStep 1400991 = 2101487) B2101487
theorem B7094951 : Blo 1399519 7094951 := bstep (se 1 (by rfl) ⟨5321213, by rfl⟩ : syracuseStep 7094951 = 10642427) B10642427
theorem B9585391 : Blo 1399519 9585391 := bstep (se 1 (by rfl) ⟨7189043, by rfl⟩ : syracuseStep 9585391 = 14378087) B14378087
theorem B48522149 : Blo 1399519 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B1893703 : Blo 1399519 1893703 := bstep (se 1 (by rfl) ⟨1420277, by rfl⟩ : syracuseStep 1893703 = 2840555) B2840555
theorem B15132059 : Blo 1399519 15132059 := bstep (se 1 (by rfl) ⟨11349044, by rfl⟩ : syracuseStep 15132059 = 22698089) B22698089
theorem B19162631 : Blo 1399519 19162631 := bstep (se 1 (by rfl) ⟨14371973, by rfl⟩ : syracuseStep 19162631 = 28743947) B28743947
theorem B5318419 : Blo 1399519 5318419 := bstep (se 1 (by rfl) ⟨3988814, by rfl⟩ : syracuseStep 5318419 = 7977629) B7977629
theorem B1574815 : Blo 1399519 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B15132581 : Blo 1399519 15132581 := bstep (se 4 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 15132581 = 2837359) B2837359
theorem B5982335 : Blo 1399519 5982335 := bstep (se 1 (by rfl) ⟨4486751, by rfl⟩ : syracuseStep 5982335 = 8973503) B8973503
theorem B2099369 : Blo 1399519 2099369 := bstep (se 2 (by rfl) ⟨787263, by rfl⟩ : syracuseStep 2099369 = 1574527) B1574527
theorem B6391979 : Blo 1399519 6391979 := bstep (se 1 (by rfl) ⟨4793984, by rfl⟩ : syracuseStep 6391979 = 9587969) B9587969
theorem B26921423 : Blo 1399519 26921423 := bstep (se 1 (by rfl) ⟨20191067, by rfl⟩ : syracuseStep 26921423 = 40382135) B40382135
theorem B4729319 : Blo 1399519 4729319 := bstep (se 1 (by rfl) ⟨3546989, by rfl⟩ : syracuseStep 4729319 = 7093979) B7093979
theorem B4729697 : Blo 1399519 4729697 := bstep (se 2 (by rfl) ⟨1773636, by rfl⟩ : syracuseStep 4729697 = 3547273) B3547273
theorem B2993107 : Blo 1399519 2993107 := bstep (se 1 (by rfl) ⟨2244830, by rfl⟩ : syracuseStep 2993107 = 4489661) B4489661
theorem B6385007 : Blo 1399519 6385007 := bstep (se 1 (by rfl) ⟨4788755, by rfl⟩ : syracuseStep 6385007 = 9577511) B9577511
theorem B2362783 : Blo 1399519 2362783 := bstep (se 1 (by rfl) ⟨1772087, by rfl⟩ : syracuseStep 2362783 = 3544175) B3544175
theorem B1576399 : Blo 1399519 1576399 := bstep (se 1 (by rfl) ⟨1182299, by rfl⟩ : syracuseStep 1576399 = 2364599) B2364599
theorem B11963983 : Blo 1399519 11963983 := bstep (se 1 (by rfl) ⟨8972987, by rfl⟩ : syracuseStep 11963983 = 17945975) B17945975
theorem B3149423 : Blo 1399519 3149423 := bstep (se 1 (by rfl) ⟨2362067, by rfl⟩ : syracuseStep 3149423 = 4724135) B4724135
theorem B2100905 : Blo 1399519 2100905 := bstep (se 2 (by rfl) ⟨787839, by rfl⟩ : syracuseStep 2100905 = 1575679) B1575679
theorem B2658025 : Blo 1399519 2658025 := bstep (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) B1993519
theorem B2101001 : Blo 1399519 2101001 := bstep (se 2 (by rfl) ⟨787875, by rfl⟩ : syracuseStep 2101001 = 1575751) B1575751
theorem B10227647 : Blo 1399519 10227647 := bstep (se 1 (by rfl) ⟨7670735, by rfl⟩ : syracuseStep 10227647 = 15341471) B15341471
theorem B34091111 : Blo 1399519 34091111 := bstep (se 1 (by rfl) ⟨25568333, by rfl⟩ : syracuseStep 34091111 = 51136667) B51136667
theorem B6729895 : Blo 1399519 6729895 := bstep (se 1 (by rfl) ⟨5047421, by rfl⟩ : syracuseStep 6729895 = 10094843) B10094843
theorem B13824199 : Blo 1399519 13824199 := bstep (se 1 (by rfl) ⟨10368149, by rfl⟩ : syracuseStep 13824199 = 20736299) B20736299
theorem B3150143 : Blo 1399519 3150143 := bstep (se 1 (by rfl) ⟨2362607, by rfl⟩ : syracuseStep 3150143 = 4725215) B4725215
theorem B2101673 : Blo 1399519 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B7574249 : Blo 1399519 7574249 := bstep (se 2 (by rfl) ⟨2840343, by rfl⟩ : syracuseStep 7574249 = 5680687) B5680687
theorem B7091063 : Blo 1399519 7091063 := bstep (se 1 (by rfl) ⟨5318297, by rfl⟩ : syracuseStep 7091063 = 10636595) B10636595
theorem B3150953 : Blo 1399519 3150953 := bstep (se 2 (by rfl) ⟨1181607, by rfl⟩ : syracuseStep 3150953 = 2363215) B2363215
theorem B21566827 : Blo 1399519 21566827 := bstep (se 1 (by rfl) ⟨16175120, by rfl⟩ : syracuseStep 21566827 = 32350241) B32350241
theorem B2659871 : Blo 1399519 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B3544681 : Blo 1399519 3544681 := bstep (se 2 (by rfl) ⟨1329255, by rfl⟩ : syracuseStep 3544681 = 2658511) B2658511
theorem B12785597 : Blo 1399519 12785597 := bstep (se 3 (by rfl) ⟨2397299, by rfl⟩ : syracuseStep 12785597 = 4794599) B4794599
theorem B19437677 : Blo 1399519 19437677 := bstep (se 3 (by rfl) ⟨3644564, by rfl⟩ : syracuseStep 19437677 = 7289129) B7289129
theorem B11966717 : Blo 1399519 11966717 := bstep (se 3 (by rfl) ⟨2243759, by rfl⟩ : syracuseStep 11966717 = 4487519) B4487519
theorem B3152249 : Blo 1399519 3152249 := bstep (se 2 (by rfl) ⟨1182093, by rfl⟩ : syracuseStep 3152249 = 2364187) B2364187
theorem B3545471 : Blo 1399519 3545471 := bstep (se 1 (by rfl) ⟨2659103, by rfl⟩ : syracuseStep 3545471 = 5318207) B5318207
theorem B1399527 : Blo 1399519 1399527 := bstep (se 1 (by rfl) ⟨1049645, by rfl⟩ : syracuseStep 1399527 = 2099291) B2099291
theorem B1399551 : Blo 1399519 1399551 := bstep (se 1 (by rfl) ⟨1049663, by rfl⟩ : syracuseStep 1399551 = 2099327) B2099327
theorem B1399775 : Blo 1399519 1399775 := bstep (se 1 (by rfl) ⟨1049831, by rfl⟩ : syracuseStep 1399775 = 2099663) B2099663
theorem B4725863 : Blo 1399519 4725863 := bstep (se 1 (by rfl) ⟨3544397, by rfl⟩ : syracuseStep 4725863 = 7088795) B7088795
theorem B1399975 : Blo 1399519 1399975 := bstep (se 1 (by rfl) ⟨1049981, by rfl⟩ : syracuseStep 1399975 = 2099963) B2099963
theorem B38313323 : Blo 1399519 38313323 := bstep (se 1 (by rfl) ⟨28734992, by rfl⟩ : syracuseStep 38313323 = 57469985) B57469985
theorem B1400287 : Blo 1399519 1400287 := bstep (se 1 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 1400287 = 2100431) B2100431
theorem B1400319 : Blo 1399519 1400319 := bstep (se 1 (by rfl) ⟨1050239, by rfl⟩ : syracuseStep 1400319 = 2100479) B2100479
theorem B34053743 : Blo 1399519 34053743 := bstep (se 1 (by rfl) ⟨25540307, by rfl⟩ : syracuseStep 34053743 = 51080615) B51080615
theorem B22724297 : Blo 1399519 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B3366793 : Blo 1399519 3366793 := bstep (se 2 (by rfl) ⟨1262547, by rfl⟩ : syracuseStep 3366793 = 2525095) B2525095
theorem B1401115 : Blo 1399519 1401115 := bstep (se 1 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 1401115 = 2101673) B2101673
theorem B4727375 : Blo 1399519 4727375 := bstep (se 1 (by rfl) ⟨3545531, by rfl⟩ : syracuseStep 4727375 = 7091063) B7091063
theorem B12780521 : Blo 1399519 12780521 := bstep (se 2 (by rfl) ⟨4792695, by rfl⟩ : syracuseStep 12780521 = 9585391) B9585391
theorem B73729061 : Blo 1399519 73729061 := bstep (se 4 (by rfl) ⟨6912099, by rfl⟩ : syracuseStep 73729061 = 13824199) B13824199
theorem B3990809 : Blo 1399519 3990809 := bstep (se 2 (by rfl) ⟨1496553, by rfl⟩ : syracuseStep 3990809 = 2993107) B2993107
theorem B4261319 : Blo 1399519 4261319 := bstep (se 1 (by rfl) ⟨3195989, by rfl⟩ : syracuseStep 4261319 = 6391979) B6391979
theorem B90809981 : Blo 1399519 90809981 := bstep (se 3 (by rfl) ⟨17026871, by rfl⟩ : syracuseStep 90809981 = 34053743) B34053743
theorem B2524937 : Blo 1399519 2524937 := bstep (se 2 (by rfl) ⟨946851, by rfl⟩ : syracuseStep 2524937 = 1893703) B1893703
theorem B15951977 : Blo 1399519 15951977 := bstep (se 2 (by rfl) ⟨5981991, by rfl⟩ : syracuseStep 15951977 = 11963983) B11963983
theorem B2099615 : Blo 1399519 2099615 := bstep (se 1 (by rfl) ⟨1574711, by rfl⟩ : syracuseStep 2099615 = 3149423) B3149423
theorem B15149531 : Blo 1399519 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B2099753 : Blo 1399519 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B6818431 : Blo 1399519 6818431 := bstep (se 1 (by rfl) ⟨5113823, by rfl⟩ : syracuseStep 6818431 = 10227647) B10227647
theorem B22727407 : Blo 1399519 22727407 := bstep (se 1 (by rfl) ⟨17045555, by rfl⟩ : syracuseStep 22727407 = 34091111) B34091111
theorem B2100095 : Blo 1399519 2100095 := bstep (se 1 (by rfl) ⟨1575071, by rfl⟩ : syracuseStep 2100095 = 3150143) B3150143
theorem B8973193 : Blo 1399519 8973193 := bstep (se 2 (by rfl) ⟨3364947, by rfl⟩ : syracuseStep 8973193 = 6729895) B6729895
theorem B4729967 : Blo 1399519 4729967 := bstep (se 1 (by rfl) ⟨3547475, by rfl⟩ : syracuseStep 4729967 = 7094951) B7094951
theorem B5049499 : Blo 1399519 5049499 := bstep (se 1 (by rfl) ⟨3787124, by rfl⟩ : syracuseStep 5049499 = 7574249) B7574249
theorem B2100635 : Blo 1399519 2100635 := bstep (se 1 (by rfl) ⟨1575476, by rfl⟩ : syracuseStep 2100635 = 3150953) B3150953
theorem B10088039 : Blo 1399519 10088039 := bstep (se 1 (by rfl) ⟨7566029, by rfl⟩ : syracuseStep 10088039 = 15132059) B15132059
theorem B17026685 : Blo 1399519 17026685 := bstep (se 3 (by rfl) ⟨3192503, by rfl⟩ : syracuseStep 17026685 = 6385007) B6385007
theorem B12775087 : Blo 1399519 12775087 := bstep (se 1 (by rfl) ⟨9581315, by rfl⟩ : syracuseStep 12775087 = 19162631) B19162631
theorem B1773247 : Blo 1399519 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B10088387 : Blo 1399519 10088387 := bstep (se 1 (by rfl) ⟨7566290, by rfl⟩ : syracuseStep 10088387 = 15132581) B15132581
theorem B8523731 : Blo 1399519 8523731 := bstep (se 1 (by rfl) ⟨6392798, by rfl⟩ : syracuseStep 8523731 = 12785597) B12785597
theorem B2101499 : Blo 1399519 2101499 := bstep (se 1 (by rfl) ⟨1576124, by rfl⟩ : syracuseStep 2101499 = 3152249) B3152249
theorem B2363647 : Blo 1399519 2363647 := bstep (se 1 (by rfl) ⟨1772735, by rfl⟩ : syracuseStep 2363647 = 3545471) B3545471
theorem B3150377 : Blo 1399519 3150377 := bstep (se 2 (by rfl) ⟨1181391, by rfl⟩ : syracuseStep 3150377 = 2362783) B2362783
theorem B2101865 : Blo 1399519 2101865 := bstep (se 2 (by rfl) ⟨788199, by rfl⟩ : syracuseStep 2101865 = 1576399) B1576399
theorem B3150575 : Blo 1399519 3150575 := bstep (se 1 (by rfl) ⟨2362931, by rfl⟩ : syracuseStep 3150575 = 4725863) B4725863
theorem B3544033 : Blo 1399519 3544033 := bstep (se 2 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 3544033 = 2658025) B2658025
theorem B7091225 : Blo 1399519 7091225 := bstep (se 2 (by rfl) ⟨2659209, by rfl⟩ : syracuseStep 7091225 = 5318419) B5318419
theorem B4789631 : Blo 1399519 4789631 := bstep (se 1 (by rfl) ⟨3592223, by rfl⟩ : syracuseStep 4789631 = 7184447) B7184447
theorem B32348099 : Blo 1399519 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B12958451 : Blo 1399519 12958451 := bstep (se 1 (by rfl) ⟨9718838, by rfl⟩ : syracuseStep 12958451 = 19437677) B19437677
theorem B3988223 : Blo 1399519 3988223 := bstep (se 1 (by rfl) ⟨2991167, by rfl⟩ : syracuseStep 3988223 = 5982335) B5982335
theorem B1399579 : Blo 1399519 1399579 := bstep (se 1 (by rfl) ⟨1049684, by rfl⟩ : syracuseStep 1399579 = 2099369) B2099369
theorem B7977811 : Blo 1399519 7977811 := bstep (se 1 (by rfl) ⟨5983358, by rfl⟩ : syracuseStep 7977811 = 11966717) B11966717
theorem B17947615 : Blo 1399519 17947615 := bstep (se 1 (by rfl) ⟨13460711, by rfl⟩ : syracuseStep 17947615 = 26921423) B26921423
theorem B3152879 : Blo 1399519 3152879 := bstep (se 1 (by rfl) ⟨2364659, by rfl⟩ : syracuseStep 3152879 = 4729319) B4729319
theorem B115023077 : Blo 1399519 115023077 := bstep (se 4 (by rfl) ⟨10783413, by rfl⟩ : syracuseStep 115023077 = 21566827) B21566827
theorem B3153131 : Blo 1399519 3153131 := bstep (se 1 (by rfl) ⟨2364848, by rfl⟩ : syracuseStep 3153131 = 4729697) B4729697
theorem B4726241 : Blo 1399519 4726241 := bstep (se 2 (by rfl) ⟨1772340, by rfl⟩ : syracuseStep 4726241 = 3544681) B3544681
theorem B25542215 : Blo 1399519 25542215 := bstep (se 1 (by rfl) ⟨19156661, by rfl⟩ : syracuseStep 25542215 = 38313323) B38313323
theorem B1400603 : Blo 1399519 1400603 := bstep (se 1 (by rfl) ⟨1050452, by rfl⟩ : syracuseStep 1400603 = 2100905) B2100905
theorem B1400667 : Blo 1399519 1400667 := bstep (se 1 (by rfl) ⟨1050500, by rfl⟩ : syracuseStep 1400667 = 2101001) B2101001
theorem B4489057 : Blo 1399519 4489057 := bstep (se 2 (by rfl) ⟨1683396, by rfl⟩ : syracuseStep 4489057 = 3366793) B3366793
theorem B1400999 : Blo 1399519 1400999 := bstep (se 1 (by rfl) ⟨1050749, by rfl⟩ : syracuseStep 1400999 = 2101499) B2101499
theorem B1401243 : Blo 1399519 1401243 := bstep (se 1 (by rfl) ⟨1050932, by rfl⟩ : syracuseStep 1401243 = 2101865) B2101865
theorem B8520347 : Blo 1399519 8520347 := bstep (se 1 (by rfl) ⟨6390260, by rfl⟩ : syracuseStep 8520347 = 12780521) B12780521
theorem B4727483 : Blo 1399519 4727483 := bstep (se 1 (by rfl) ⟨3545612, by rfl⟩ : syracuseStep 4727483 = 7091225) B7091225
theorem B49152707 : Blo 1399519 49152707 := bstep (se 1 (by rfl) ⟨36864530, by rfl⟩ : syracuseStep 49152707 = 73729061) B73729061
theorem B30303209 : Blo 1399519 30303209 := bstep (se 2 (by rfl) ⟨11363703, by rfl⟩ : syracuseStep 30303209 = 22727407) B22727407
theorem B60539987 : Blo 1399519 60539987 := bstep (se 1 (by rfl) ⟨45404990, by rfl⟩ : syracuseStep 60539987 = 90809981) B90809981
theorem B23930153 : Blo 1399519 23930153 := bstep (se 2 (by rfl) ⟨8973807, by rfl⟩ : syracuseStep 23930153 = 17947615) B17947615
theorem B10634651 : Blo 1399519 10634651 := bstep (se 1 (by rfl) ⟨7975988, by rfl⟩ : syracuseStep 10634651 = 15951977) B15951977
theorem B17033449 : Blo 1399519 17033449 := bstep (se 2 (by rfl) ⟨6387543, by rfl⟩ : syracuseStep 17033449 = 12775087) B12775087
theorem B2100251 : Blo 1399519 2100251 := bstep (se 1 (by rfl) ⟨1575188, by rfl⟩ : syracuseStep 2100251 = 3150377) B3150377
theorem B2100383 : Blo 1399519 2100383 := bstep (se 1 (by rfl) ⟨1575287, by rfl⟩ : syracuseStep 2100383 = 3150575) B3150575
theorem B10637081 : Blo 1399519 10637081 := bstep (se 2 (by rfl) ⟨3988905, by rfl⟩ : syracuseStep 10637081 = 7977811) B7977811
theorem B11964257 : Blo 1399519 11964257 := bstep (se 2 (by rfl) ⟨4486596, by rfl⟩ : syracuseStep 11964257 = 8973193) B8973193
theorem B8638967 : Blo 1399519 8638967 := bstep (se 1 (by rfl) ⟨6479225, by rfl⟩ : syracuseStep 8638967 = 12958451) B12958451
theorem B2658815 : Blo 1399519 2658815 := bstep (se 1 (by rfl) ⟨1994111, by rfl⟩ : syracuseStep 2658815 = 3988223) B3988223
theorem B2101919 : Blo 1399519 2101919 := bstep (se 1 (by rfl) ⟨1576439, by rfl⟩ : syracuseStep 2101919 = 3152879) B3152879
theorem B76682051 : Blo 1399519 76682051 := bstep (se 1 (by rfl) ⟨57511538, by rfl⟩ : syracuseStep 76682051 = 115023077) B115023077
theorem B2102087 : Blo 1399519 2102087 := bstep (se 1 (by rfl) ⟨1576565, by rfl⟩ : syracuseStep 2102087 = 3153131) B3153131
theorem B2364329 : Blo 1399519 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B3150827 : Blo 1399519 3150827 := bstep (se 1 (by rfl) ⟨2363120, by rfl⟩ : syracuseStep 3150827 = 4726241) B4726241
theorem B17028143 : Blo 1399519 17028143 := bstep (se 1 (by rfl) ⟨12771107, by rfl⟩ : syracuseStep 17028143 = 25542215) B25542215
theorem B11351123 : Blo 1399519 11351123 := bstep (se 1 (by rfl) ⟨8513342, by rfl⟩ : syracuseStep 11351123 = 17026685) B17026685
theorem B5985409 : Blo 1399519 5985409 := bstep (se 2 (by rfl) ⟨2244528, by rfl⟩ : syracuseStep 5985409 = 4489057) B4489057
theorem B5682487 : Blo 1399519 5682487 := bstep (se 1 (by rfl) ⟨4261865, by rfl⟩ : syracuseStep 5682487 = 8523731) B8523731
theorem B3151529 : Blo 1399519 3151529 := bstep (se 2 (by rfl) ⟨1181823, by rfl⟩ : syracuseStep 3151529 = 2363647) B2363647
theorem B3151583 : Blo 1399519 3151583 := bstep (se 1 (by rfl) ⟨2363687, by rfl⟩ : syracuseStep 3151583 = 4727375) B4727375
theorem B9091241 : Blo 1399519 9091241 := bstep (se 2 (by rfl) ⟨3409215, by rfl⟩ : syracuseStep 9091241 = 6818431) B6818431
theorem B2660539 : Blo 1399519 2660539 := bstep (se 1 (by rfl) ⟨1995404, by rfl⟩ : syracuseStep 2660539 = 3990809) B3990809
theorem B3193087 : Blo 1399519 3193087 := bstep (se 1 (by rfl) ⟨2394815, by rfl⟩ : syracuseStep 3193087 = 4789631) B4789631
theorem B2840879 : Blo 1399519 2840879 := bstep (se 1 (by rfl) ⟨2130659, by rfl⟩ : syracuseStep 2840879 = 4261319) B4261319
theorem B4725377 : Blo 1399519 4725377 := bstep (se 2 (by rfl) ⟨1772016, by rfl⟩ : syracuseStep 4725377 = 3544033) B3544033
theorem B6732665 : Blo 1399519 6732665 := bstep (se 2 (by rfl) ⟨2524749, by rfl⟩ : syracuseStep 6732665 = 5049499) B5049499
theorem B1399743 : Blo 1399519 1399743 := bstep (se 1 (by rfl) ⟨1049807, by rfl⟩ : syracuseStep 1399743 = 2099615) B2099615
theorem B10099687 : Blo 1399519 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B1399835 : Blo 1399519 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B1400063 : Blo 1399519 1400063 := bstep (se 1 (by rfl) ⟨1050047, by rfl⟩ : syracuseStep 1400063 = 2100095) B2100095
theorem B6733165 : Blo 1399519 6733165 := bstep (se 3 (by rfl) ⟨1262468, by rfl⟩ : syracuseStep 6733165 = 2524937) B2524937
theorem B3153311 : Blo 1399519 3153311 := bstep (se 1 (by rfl) ⟨2364983, by rfl⟩ : syracuseStep 3153311 = 4729967) B4729967
theorem B1400423 : Blo 1399519 1400423 := bstep (se 1 (by rfl) ⟨1050317, by rfl⟩ : syracuseStep 1400423 = 2100635) B2100635
theorem B6725359 : Blo 1399519 6725359 := bstep (se 1 (by rfl) ⟨5044019, by rfl⟩ : syracuseStep 6725359 = 10088039) B10088039
theorem B86261597 : Blo 1399519 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B6725591 : Blo 1399519 6725591 := bstep (se 1 (by rfl) ⟨5044193, by rfl⟩ : syracuseStep 6725591 = 10088387) B10088387
theorem B3547385 : Blo 1399519 3547385 := bstep (se 2 (by rfl) ⟨1330269, by rfl⟩ : syracuseStep 3547385 = 2660539) B2660539
theorem B5759311 : Blo 1399519 5759311 := bstep (se 1 (by rfl) ⟨4319483, by rfl⟩ : syracuseStep 5759311 = 8638967) B8638967
theorem B1401279 : Blo 1399519 1401279 := bstep (se 1 (by rfl) ⟨1050959, by rfl⟩ : syracuseStep 1401279 = 2101919) B2101919
theorem B32768471 : Blo 1399519 32768471 := bstep (se 1 (by rfl) ⟨24576353, by rfl⟩ : syracuseStep 32768471 = 49152707) B49152707
theorem B1401391 : Blo 1399519 1401391 := bstep (se 1 (by rfl) ⟨1051043, by rfl⟩ : syracuseStep 1401391 = 2102087) B2102087
theorem B20202139 : Blo 1399519 20202139 := bstep (se 1 (by rfl) ⟨15151604, by rfl⟩ : syracuseStep 20202139 = 30303209) B30303209
theorem B7980545 : Blo 1399519 7980545 := bstep (se 2 (by rfl) ⟨2992704, by rfl⟩ : syracuseStep 7980545 = 5985409) B5985409
theorem B4483727 : Blo 1399519 4483727 := bstep (se 1 (by rfl) ⟨3362795, by rfl⟩ : syracuseStep 4483727 = 6725591) B6725591
theorem B22711265 : Blo 1399519 22711265 := bstep (se 2 (by rfl) ⟨8516724, by rfl⟩ : syracuseStep 22711265 = 17033449) B17033449
theorem B1772543 : Blo 1399519 1772543 := bstep (se 1 (by rfl) ⟨1329407, by rfl⟩ : syracuseStep 1772543 = 2658815) B2658815
theorem B51121367 : Blo 1399519 51121367 := bstep (se 1 (by rfl) ⟨38341025, by rfl⟩ : syracuseStep 51121367 = 76682051) B76682051
theorem B1576219 : Blo 1399519 1576219 := bstep (se 1 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 1576219 = 2364329) B2364329
theorem B2100551 : Blo 1399519 2100551 := bstep (se 1 (by rfl) ⟨1575413, by rfl⟩ : syracuseStep 2100551 = 3150827) B3150827
theorem B15953435 : Blo 1399519 15953435 := bstep (se 1 (by rfl) ⟨11965076, by rfl⟩ : syracuseStep 15953435 = 23930153) B23930153
theorem B7089767 : Blo 1399519 7089767 := bstep (se 1 (by rfl) ⟨5317325, by rfl⟩ : syracuseStep 7089767 = 10634651) B10634651
theorem B2101019 : Blo 1399519 2101019 := bstep (se 1 (by rfl) ⟨1575764, by rfl⟩ : syracuseStep 2101019 = 3151529) B3151529
theorem B2101055 : Blo 1399519 2101055 := bstep (se 1 (by rfl) ⟨1575791, by rfl⟩ : syracuseStep 2101055 = 3151583) B3151583
theorem B22720925 : Blo 1399519 22720925 := bstep (se 3 (by rfl) ⟨4260173, by rfl⟩ : syracuseStep 22720925 = 8520347) B8520347
theorem B3150251 : Blo 1399519 3150251 := bstep (se 1 (by rfl) ⟨2362688, by rfl⟩ : syracuseStep 3150251 = 4725377) B4725377
theorem B2102207 : Blo 1399519 2102207 := bstep (se 1 (by rfl) ⟨1576655, by rfl⟩ : syracuseStep 2102207 = 3153311) B3153311
theorem B8967145 : Blo 1399519 8967145 := bstep (se 2 (by rfl) ⟨3362679, by rfl⟩ : syracuseStep 8967145 = 6725359) B6725359
theorem B7091387 : Blo 1399519 7091387 := bstep (se 1 (by rfl) ⟨5318540, by rfl⟩ : syracuseStep 7091387 = 10637081) B10637081
theorem B7976171 : Blo 1399519 7976171 := bstep (se 1 (by rfl) ⟨5982128, by rfl⟩ : syracuseStep 7976171 = 11964257) B11964257
theorem B4257449 : Blo 1399519 4257449 := bstep (se 2 (by rfl) ⟨1596543, by rfl⟩ : syracuseStep 4257449 = 3193087) B3193087
theorem B3151655 : Blo 1399519 3151655 := bstep (se 1 (by rfl) ⟨2363741, by rfl⟩ : syracuseStep 3151655 = 4727483) B4727483
theorem B11352095 : Blo 1399519 11352095 := bstep (se 1 (by rfl) ⟨8514071, by rfl⟩ : syracuseStep 11352095 = 17028143) B17028143
theorem B7567415 : Blo 1399519 7567415 := bstep (se 1 (by rfl) ⟨5675561, by rfl⟩ : syracuseStep 7567415 = 11351123) B11351123
theorem B40359991 : Blo 1399519 40359991 := bstep (se 1 (by rfl) ⟨30269993, by rfl⟩ : syracuseStep 40359991 = 60539987) B60539987
theorem B7575677 : Blo 1399519 7575677 := bstep (se 3 (by rfl) ⟨1420439, by rfl⟩ : syracuseStep 7575677 = 2840879) B2840879
theorem B13466249 : Blo 1399519 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B6060827 : Blo 1399519 6060827 := bstep (se 1 (by rfl) ⟨4545620, by rfl⟩ : syracuseStep 6060827 = 9091241) B9091241
theorem B7576649 : Blo 1399519 7576649 := bstep (se 2 (by rfl) ⟨2841243, by rfl⟩ : syracuseStep 7576649 = 5682487) B5682487
theorem B8977553 : Blo 1399519 8977553 := bstep (se 2 (by rfl) ⟨3366582, by rfl⟩ : syracuseStep 8977553 = 6733165) B6733165
theorem B4488443 : Blo 1399519 4488443 := bstep (se 1 (by rfl) ⟨3366332, by rfl⟩ : syracuseStep 4488443 = 6732665) B6732665
theorem B1400167 : Blo 1399519 1400167 := bstep (se 1 (by rfl) ⟨1050125, by rfl⟩ : syracuseStep 1400167 = 2100251) B2100251
theorem B1400255 : Blo 1399519 1400255 := bstep (se 1 (by rfl) ⟨1050191, by rfl⟩ : syracuseStep 1400255 = 2100383) B2100383
theorem B57507731 : Blo 1399519 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B53813321 : Blo 1399519 53813321 := bstep (se 2 (by rfl) ⟨20179995, by rfl⟩ : syracuseStep 53813321 = 40359991) B40359991
theorem B15147283 : Blo 1399519 15147283 := bstep (se 1 (by rfl) ⟨11360462, by rfl⟩ : syracuseStep 15147283 = 22720925) B22720925
theorem B1401471 : Blo 1399519 1401471 := bstep (se 1 (by rfl) ⟨1051103, by rfl⟩ : syracuseStep 1401471 = 2102207) B2102207
theorem B4727591 : Blo 1399519 4727591 := bstep (se 1 (by rfl) ⟨3545693, by rfl⟩ : syracuseStep 4727591 = 7091387) B7091387
theorem B5317447 : Blo 1399519 5317447 := bstep (se 1 (by rfl) ⟨3988085, by rfl⟩ : syracuseStep 5317447 = 7976171) B7976171
theorem B26936185 : Blo 1399519 26936185 := bstep (se 2 (by rfl) ⟨10101069, by rfl⟩ : syracuseStep 26936185 = 20202139) B20202139
theorem B4040551 : Blo 1399519 4040551 := bstep (se 1 (by rfl) ⟨3030413, by rfl⟩ : syracuseStep 4040551 = 6060827) B6060827
theorem B15140843 : Blo 1399519 15140843 := bstep (se 1 (by rfl) ⟨11355632, by rfl⟩ : syracuseStep 15140843 = 22711265) B22711265
theorem B34080911 : Blo 1399519 34080911 := bstep (se 1 (by rfl) ⟨25560683, by rfl⟩ : syracuseStep 34080911 = 51121367) B51121367
theorem B2992295 : Blo 1399519 2992295 := bstep (se 1 (by rfl) ⟨2244221, by rfl⟩ : syracuseStep 2992295 = 4488443) B4488443
theorem B10635623 : Blo 1399519 10635623 := bstep (se 1 (by rfl) ⟨7976717, by rfl⟩ : syracuseStep 10635623 = 15953435) B15953435
theorem B2100167 : Blo 1399519 2100167 := bstep (se 1 (by rfl) ⟨1575125, by rfl⟩ : syracuseStep 2100167 = 3150251) B3150251
theorem B7679081 : Blo 1399519 7679081 := bstep (se 2 (by rfl) ⟨2879655, by rfl⟩ : syracuseStep 7679081 = 5759311) B5759311
theorem B5320363 : Blo 1399519 5320363 := bstep (se 1 (by rfl) ⟨3990272, by rfl⟩ : syracuseStep 5320363 = 7980545) B7980545
theorem B2838299 : Blo 1399519 2838299 := bstep (se 1 (by rfl) ⟨2128724, by rfl⟩ : syracuseStep 2838299 = 4257449) B4257449
theorem B2101103 : Blo 1399519 2101103 := bstep (se 1 (by rfl) ⟨1575827, by rfl⟩ : syracuseStep 2101103 = 3151655) B3151655
theorem B11956193 : Blo 1399519 11956193 := bstep (se 2 (by rfl) ⟨4483572, by rfl⟩ : syracuseStep 11956193 = 8967145) B8967145
theorem B5050451 : Blo 1399519 5050451 := bstep (se 1 (by rfl) ⟨3787838, by rfl⟩ : syracuseStep 5050451 = 7575677) B7575677
theorem B2101625 : Blo 1399519 2101625 := bstep (se 2 (by rfl) ⟨788109, by rfl⟩ : syracuseStep 2101625 = 1576219) B1576219
theorem B5051099 : Blo 1399519 5051099 := bstep (se 1 (by rfl) ⟨3788324, by rfl⟩ : syracuseStep 5051099 = 7576649) B7576649
theorem B5985035 : Blo 1399519 5985035 := bstep (se 1 (by rfl) ⟨4488776, by rfl⟩ : syracuseStep 5985035 = 8977553) B8977553
theorem B2364923 : Blo 1399519 2364923 := bstep (se 1 (by rfl) ⟨1773692, by rfl⟩ : syracuseStep 2364923 = 3547385) B3547385
theorem B21845647 : Blo 1399519 21845647 := bstep (se 1 (by rfl) ⟨16384235, by rfl⟩ : syracuseStep 21845647 = 32768471) B32768471
theorem B7568063 : Blo 1399519 7568063 := bstep (se 1 (by rfl) ⟨5676047, by rfl⟩ : syracuseStep 7568063 = 11352095) B11352095
theorem B5044943 : Blo 1399519 5044943 := bstep (se 1 (by rfl) ⟨3783707, by rfl⟩ : syracuseStep 5044943 = 7567415) B7567415
theorem B8977499 : Blo 1399519 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B2989151 : Blo 1399519 2989151 := bstep (se 1 (by rfl) ⟨2241863, by rfl⟩ : syracuseStep 2989151 = 4483727) B4483727
theorem B1400367 : Blo 1399519 1400367 := bstep (se 1 (by rfl) ⟨1050275, by rfl⟩ : syracuseStep 1400367 = 2100551) B2100551
theorem B4726511 : Blo 1399519 4726511 := bstep (se 1 (by rfl) ⟨3544883, by rfl⟩ : syracuseStep 4726511 = 7089767) B7089767
theorem B1400679 : Blo 1399519 1400679 := bstep (se 1 (by rfl) ⟨1050509, by rfl⟩ : syracuseStep 1400679 = 2101019) B2101019
theorem B1400703 : Blo 1399519 1400703 := bstep (se 1 (by rfl) ⟨1050527, by rfl⟩ : syracuseStep 1400703 = 2101055) B2101055
theorem B38338487 : Blo 1399519 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B4726781 : Blo 1399519 4726781 := bstep (se 3 (by rfl) ⟨886271, by rfl⟩ : syracuseStep 4726781 = 1772543) B1772543
theorem B3366967 : Blo 1399519 3366967 := bstep (se 1 (by rfl) ⟨2525225, by rfl⟩ : syracuseStep 3366967 = 5050451) B5050451
theorem B1401083 : Blo 1399519 1401083 := bstep (se 1 (by rfl) ⟨1050812, by rfl⟩ : syracuseStep 1401083 = 2101625) B2101625
theorem B3990023 : Blo 1399519 3990023 := bstep (se 1 (by rfl) ⟨2992517, by rfl⟩ : syracuseStep 3990023 = 5985035) B5985035
theorem B35914913 : Blo 1399519 35914913 := bstep (se 2 (by rfl) ⟨13468092, by rfl⟩ : syracuseStep 35914913 = 26936185) B26936185
theorem B10093895 : Blo 1399519 10093895 := bstep (se 1 (by rfl) ⟨7570421, by rfl⟩ : syracuseStep 10093895 = 15140843) B15140843
theorem B13469597 : Blo 1399519 13469597 := bstep (se 3 (by rfl) ⟨2525549, by rfl⟩ : syracuseStep 13469597 = 5051099) B5051099
theorem B1992767 : Blo 1399519 1992767 := bstep (se 1 (by rfl) ⟨1494575, by rfl⟩ : syracuseStep 1992767 = 2989151) B2989151
theorem B35875547 : Blo 1399519 35875547 := bstep (se 1 (by rfl) ⟨26906660, by rfl⟩ : syracuseStep 35875547 = 53813321) B53813321
theorem B20196377 : Blo 1399519 20196377 := bstep (se 2 (by rfl) ⟨7573641, by rfl⟩ : syracuseStep 20196377 = 15147283) B15147283
theorem B1576615 : Blo 1399519 1576615 := bstep (se 1 (by rfl) ⟨1182461, by rfl⟩ : syracuseStep 1576615 = 2364923) B2364923
theorem B7089929 : Blo 1399519 7089929 := bstep (se 2 (by rfl) ⟨2658723, by rfl⟩ : syracuseStep 7089929 = 5317447) B5317447
theorem B22720607 : Blo 1399519 22720607 := bstep (se 1 (by rfl) ⟨17040455, by rfl⟩ : syracuseStep 22720607 = 34080911) B34080911
theorem B1994863 : Blo 1399519 1994863 := bstep (se 1 (by rfl) ⟨1496147, by rfl⟩ : syracuseStep 1994863 = 2992295) B2992295
theorem B7090415 : Blo 1399519 7090415 := bstep (se 1 (by rfl) ⟨5317811, by rfl⟩ : syracuseStep 7090415 = 10635623) B10635623
theorem B3363295 : Blo 1399519 3363295 := bstep (se 1 (by rfl) ⟨2522471, by rfl⟩ : syracuseStep 3363295 = 5044943) B5044943
theorem B5984999 : Blo 1399519 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B29127529 : Blo 1399519 29127529 := bstep (se 2 (by rfl) ⟨10922823, by rfl⟩ : syracuseStep 29127529 = 21845647) B21845647
theorem B5387401 : Blo 1399519 5387401 := bstep (se 2 (by rfl) ⟨2020275, by rfl⟩ : syracuseStep 5387401 = 4040551) B4040551
theorem B3151007 : Blo 1399519 3151007 := bstep (se 1 (by rfl) ⟨2363255, by rfl⟩ : syracuseStep 3151007 = 4726511) B4726511
theorem B3151187 : Blo 1399519 3151187 := bstep (se 1 (by rfl) ⟨2363390, by rfl⟩ : syracuseStep 3151187 = 4726781) B4726781
theorem B20477549 : Blo 1399519 20477549 := bstep (se 3 (by rfl) ⟨3839540, by rfl⟩ : syracuseStep 20477549 = 7679081) B7679081
theorem B3151727 : Blo 1399519 3151727 := bstep (se 1 (by rfl) ⟨2363795, by rfl⟩ : syracuseStep 3151727 = 4727591) B4727591
theorem B5045375 : Blo 1399519 5045375 := bstep (se 1 (by rfl) ⟨3784031, by rfl⟩ : syracuseStep 5045375 = 7568063) B7568063
theorem B1400111 : Blo 1399519 1400111 := bstep (se 1 (by rfl) ⟨1050083, by rfl⟩ : syracuseStep 1400111 = 2100167) B2100167
theorem B7568797 : Blo 1399519 7568797 := bstep (se 3 (by rfl) ⟨1419149, by rfl⟩ : syracuseStep 7568797 = 2838299) B2838299
theorem B7093817 : Blo 1399519 7093817 := bstep (se 2 (by rfl) ⟨2660181, by rfl⟩ : syracuseStep 7093817 = 5320363) B5320363
theorem B1400735 : Blo 1399519 1400735 := bstep (se 1 (by rfl) ⟨1050551, by rfl⟩ : syracuseStep 1400735 = 2101103) B2101103
theorem B25558991 : Blo 1399519 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B7970795 : Blo 1399519 7970795 := bstep (se 1 (by rfl) ⟨5978096, by rfl⟩ : syracuseStep 7970795 = 11956193) B11956193
theorem B15147071 : Blo 1399519 15147071 := bstep (se 1 (by rfl) ⟨11360303, by rfl⟩ : syracuseStep 15147071 = 22720607) B22720607
theorem B4489289 : Blo 1399519 4489289 := bstep (se 2 (by rfl) ⟨1683483, by rfl⟩ : syracuseStep 4489289 = 3366967) B3366967
theorem B4726943 : Blo 1399519 4726943 := bstep (se 1 (by rfl) ⟨3545207, by rfl⟩ : syracuseStep 4726943 = 7090415) B7090415
theorem B3989999 : Blo 1399519 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B8979731 : Blo 1399519 8979731 := bstep (se 1 (by rfl) ⟨6734798, by rfl⟩ : syracuseStep 8979731 = 13469597) B13469597
theorem B4729211 : Blo 1399519 4729211 := bstep (se 1 (by rfl) ⟨3546908, by rfl⟩ : syracuseStep 4729211 = 7093817) B7093817
theorem B13454333 : Blo 1399519 13454333 := bstep (se 3 (by rfl) ⟨2522687, by rfl⟩ : syracuseStep 13454333 = 5045375) B5045375
theorem B4484393 : Blo 1399519 4484393 := bstep (se 2 (by rfl) ⟨1681647, by rfl⟩ : syracuseStep 4484393 = 3363295) B3363295
theorem B28732805 : Blo 1399519 28732805 := bstep (se 4 (by rfl) ⟨2693700, by rfl⟩ : syracuseStep 28732805 = 5387401) B5387401
theorem B2100671 : Blo 1399519 2100671 := bstep (se 1 (by rfl) ⟨1575503, by rfl⟩ : syracuseStep 2100671 = 3151007) B3151007
theorem B6729263 : Blo 1399519 6729263 := bstep (se 1 (by rfl) ⟨5046947, by rfl⟩ : syracuseStep 6729263 = 10093895) B10093895
theorem B2100791 : Blo 1399519 2100791 := bstep (se 1 (by rfl) ⟨1575593, by rfl⟩ : syracuseStep 2100791 = 3151187) B3151187
theorem B13651699 : Blo 1399519 13651699 := bstep (se 1 (by rfl) ⟨10238774, by rfl⟩ : syracuseStep 13651699 = 20477549) B20477549
theorem B2101151 : Blo 1399519 2101151 := bstep (se 1 (by rfl) ⟨1575863, by rfl⟩ : syracuseStep 2101151 = 3151727) B3151727
theorem B23917031 : Blo 1399519 23917031 := bstep (se 1 (by rfl) ⟨17937773, by rfl⟩ : syracuseStep 23917031 = 35875547) B35875547
theorem B13464251 : Blo 1399519 13464251 := bstep (se 1 (by rfl) ⟨10098188, by rfl⟩ : syracuseStep 13464251 = 20196377) B20196377
theorem B2102153 : Blo 1399519 2102153 := bstep (se 2 (by rfl) ⟨788307, by rfl⟩ : syracuseStep 2102153 = 1576615) B1576615
theorem B5313863 : Blo 1399519 5313863 := bstep (se 1 (by rfl) ⟨3985397, by rfl⟩ : syracuseStep 5313863 = 7970795) B7970795
theorem B2659817 : Blo 1399519 2659817 := bstep (se 2 (by rfl) ⟨997431, by rfl⟩ : syracuseStep 2659817 = 1994863) B1994863
theorem B5314045 : Blo 1399519 5314045 := bstep (se 3 (by rfl) ⟨996383, by rfl⟩ : syracuseStep 5314045 = 1992767) B1992767
theorem B2660015 : Blo 1399519 2660015 := bstep (se 1 (by rfl) ⟨1995011, by rfl⟩ : syracuseStep 2660015 = 3990023) B3990023
theorem B23943275 : Blo 1399519 23943275 := bstep (se 1 (by rfl) ⟨17957456, by rfl⟩ : syracuseStep 23943275 = 35914913) B35914913
theorem B38836705 : Blo 1399519 38836705 := bstep (se 2 (by rfl) ⟨14563764, by rfl⟩ : syracuseStep 38836705 = 29127529) B29127529
theorem B10091729 : Blo 1399519 10091729 := bstep (se 2 (by rfl) ⟨3784398, by rfl⟩ : syracuseStep 10091729 = 7568797) B7568797
theorem B4726619 : Blo 1399519 4726619 := bstep (se 1 (by rfl) ⟨3544964, by rfl⟩ : syracuseStep 4726619 = 7089929) B7089929
theorem B17039327 : Blo 1399519 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B26911277 : Blo 1399519 26911277 := bstep (se 3 (by rfl) ⟨5045864, by rfl⟩ : syracuseStep 26911277 = 10091729) B10091729
theorem B1401435 : Blo 1399519 1401435 := bstep (se 1 (by rfl) ⟨1051076, by rfl⟩ : syracuseStep 1401435 = 2102153) B2102153
theorem B51782273 : Blo 1399519 51782273 := bstep (se 2 (by rfl) ⟨19418352, by rfl⟩ : syracuseStep 51782273 = 38836705) B38836705
theorem B19155203 : Blo 1399519 19155203 := bstep (se 1 (by rfl) ⟨14366402, by rfl⟩ : syracuseStep 19155203 = 28732805) B28732805
theorem B2992859 : Blo 1399519 2992859 := bstep (se 1 (by rfl) ⟨2244644, by rfl⟩ : syracuseStep 2992859 = 4489289) B4489289
theorem B15944687 : Blo 1399519 15944687 := bstep (se 1 (by rfl) ⟨11958515, by rfl⟩ : syracuseStep 15944687 = 23917031) B23917031
theorem B3542575 : Blo 1399519 3542575 := bstep (se 1 (by rfl) ⟨2656931, by rfl⟩ : syracuseStep 3542575 = 5313863) B5313863
theorem B1773343 : Blo 1399519 1773343 := bstep (se 1 (by rfl) ⟨1330007, by rfl⟩ : syracuseStep 1773343 = 2660015) B2660015
theorem B15962183 : Blo 1399519 15962183 := bstep (se 1 (by rfl) ⟨11971637, by rfl⟩ : syracuseStep 15962183 = 23943275) B23943275
theorem B181752821 : Blo 1399519 181752821 := bstep (se 5 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 181752821 = 17039327) B17039327
theorem B4486175 : Blo 1399519 4486175 := bstep (se 1 (by rfl) ⟨3364631, by rfl⟩ : syracuseStep 4486175 = 6729263) B6729263
theorem B3151079 : Blo 1399519 3151079 := bstep (se 1 (by rfl) ⟨2363309, by rfl⟩ : syracuseStep 3151079 = 4726619) B4726619
theorem B10098047 : Blo 1399519 10098047 := bstep (se 1 (by rfl) ⟨7573535, by rfl⟩ : syracuseStep 10098047 = 15147071) B15147071
theorem B3151295 : Blo 1399519 3151295 := bstep (se 1 (by rfl) ⟨2363471, by rfl⟩ : syracuseStep 3151295 = 4726943) B4726943
theorem B8976167 : Blo 1399519 8976167 := bstep (se 1 (by rfl) ⟨6732125, by rfl⟩ : syracuseStep 8976167 = 13464251) B13464251
theorem B5986487 : Blo 1399519 5986487 := bstep (se 1 (by rfl) ⟨4489865, by rfl⟩ : syracuseStep 5986487 = 8979731) B8979731
theorem B7092845 : Blo 1399519 7092845 := bstep (se 3 (by rfl) ⟨1329908, by rfl⟩ : syracuseStep 7092845 = 2659817) B2659817
theorem B10639997 : Blo 1399519 10639997 := bstep (se 3 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 10639997 = 3989999) B3989999
theorem B3152807 : Blo 1399519 3152807 := bstep (se 1 (by rfl) ⟨2364605, by rfl⟩ : syracuseStep 3152807 = 4729211) B4729211
theorem B7085393 : Blo 1399519 7085393 := bstep (se 2 (by rfl) ⟨2657022, by rfl⟩ : syracuseStep 7085393 = 5314045) B5314045
theorem B8969555 : Blo 1399519 8969555 := bstep (se 1 (by rfl) ⟨6727166, by rfl⟩ : syracuseStep 8969555 = 13454333) B13454333
theorem B2989595 : Blo 1399519 2989595 := bstep (se 1 (by rfl) ⟨2242196, by rfl⟩ : syracuseStep 2989595 = 4484393) B4484393
theorem B1400447 : Blo 1399519 1400447 := bstep (se 1 (by rfl) ⟨1050335, by rfl⟩ : syracuseStep 1400447 = 2100671) B2100671
theorem B18202265 : Blo 1399519 18202265 := bstep (se 2 (by rfl) ⟨6825849, by rfl⟩ : syracuseStep 18202265 = 13651699) B13651699
theorem B1400527 : Blo 1399519 1400527 := bstep (se 1 (by rfl) ⟨1050395, by rfl⟩ : syracuseStep 1400527 = 2100791) B2100791
theorem B1400767 : Blo 1399519 1400767 := bstep (se 1 (by rfl) ⟨1050575, by rfl⟩ : syracuseStep 1400767 = 2101151) B2101151
theorem B10641455 : Blo 1399519 10641455 := bstep (se 1 (by rfl) ⟨7981091, by rfl⟩ : syracuseStep 10641455 = 15962183) B15962183
theorem B17940851 : Blo 1399519 17940851 := bstep (se 1 (by rfl) ⟨13455638, by rfl⟩ : syracuseStep 17940851 = 26911277) B26911277
theorem B34521515 : Blo 1399519 34521515 := bstep (se 1 (by rfl) ⟨25891136, by rfl⟩ : syracuseStep 34521515 = 51782273) B51782273
theorem B121168547 : Blo 1399519 121168547 := bstep (se 1 (by rfl) ⟨90876410, by rfl⟩ : syracuseStep 121168547 = 181752821) B181752821
theorem B2990783 : Blo 1399519 2990783 := bstep (se 1 (by rfl) ⟨2243087, by rfl⟩ : syracuseStep 2990783 = 4486175) B4486175
theorem B7972253 : Blo 1399519 7972253 := bstep (se 3 (by rfl) ⟨1494797, by rfl⟩ : syracuseStep 7972253 = 2989595) B2989595
theorem B3990991 : Blo 1399519 3990991 := bstep (se 1 (by rfl) ⟨2993243, by rfl⟩ : syracuseStep 3990991 = 5986487) B5986487
theorem B4728563 : Blo 1399519 4728563 := bstep (se 1 (by rfl) ⟨3546422, by rfl⟩ : syracuseStep 4728563 = 7092845) B7092845
theorem B12134843 : Blo 1399519 12134843 := bstep (se 1 (by rfl) ⟨9101132, by rfl⟩ : syracuseStep 12134843 = 18202265) B18202265
theorem B2100719 : Blo 1399519 2100719 := bstep (se 1 (by rfl) ⟨1575539, by rfl⟩ : syracuseStep 2100719 = 3151079) B3151079
theorem B2100863 : Blo 1399519 2100863 := bstep (se 1 (by rfl) ⟨1575647, by rfl⟩ : syracuseStep 2100863 = 3151295) B3151295
theorem B5984111 : Blo 1399519 5984111 := bstep (se 1 (by rfl) ⟨4488083, by rfl⟩ : syracuseStep 5984111 = 8976167) B8976167
theorem B1995239 : Blo 1399519 1995239 := bstep (se 1 (by rfl) ⟨1496429, by rfl⟩ : syracuseStep 1995239 = 2992859) B2992859
theorem B2101871 : Blo 1399519 2101871 := bstep (se 1 (by rfl) ⟨1576403, by rfl⟩ : syracuseStep 2101871 = 3152807) B3152807
theorem B10629791 : Blo 1399519 10629791 := bstep (se 1 (by rfl) ⟨7972343, by rfl⟩ : syracuseStep 10629791 = 15944687) B15944687
theorem B4723433 : Blo 1399519 4723433 := bstep (se 2 (by rfl) ⟨1771287, by rfl⟩ : syracuseStep 4723433 = 3542575) B3542575
theorem B4723595 : Blo 1399519 4723595 := bstep (se 1 (by rfl) ⟨3542696, by rfl⟩ : syracuseStep 4723595 = 7085393) B7085393
theorem B2364457 : Blo 1399519 2364457 := bstep (se 2 (by rfl) ⟨886671, by rfl⟩ : syracuseStep 2364457 = 1773343) B1773343
theorem B6732031 : Blo 1399519 6732031 := bstep (se 1 (by rfl) ⟨5049023, by rfl⟩ : syracuseStep 6732031 = 10098047) B10098047
theorem B12770135 : Blo 1399519 12770135 := bstep (se 1 (by rfl) ⟨9577601, by rfl⟩ : syracuseStep 12770135 = 19155203) B19155203
theorem B7093331 : Blo 1399519 7093331 := bstep (se 1 (by rfl) ⟨5319998, by rfl⟩ : syracuseStep 7093331 = 10639997) B10639997
theorem B5979703 : Blo 1399519 5979703 := bstep (se 1 (by rfl) ⟨4484777, by rfl⟩ : syracuseStep 5979703 = 8969555) B8969555
theorem B7094303 : Blo 1399519 7094303 := bstep (se 1 (by rfl) ⟨5320727, by rfl⟩ : syracuseStep 7094303 = 10641455) B10641455
theorem B11960567 : Blo 1399519 11960567 := bstep (se 1 (by rfl) ⟨8970425, by rfl⟩ : syracuseStep 11960567 = 17940851) B17940851
theorem B1401247 : Blo 1399519 1401247 := bstep (se 1 (by rfl) ⟨1050935, by rfl⟩ : syracuseStep 1401247 = 2101871) B2101871
theorem B7086527 : Blo 1399519 7086527 := bstep (se 1 (by rfl) ⟨5314895, by rfl⟩ : syracuseStep 7086527 = 10629791) B10629791
theorem B8513423 : Blo 1399519 8513423 := bstep (se 1 (by rfl) ⟨6385067, by rfl⟩ : syracuseStep 8513423 = 12770135) B12770135
theorem B4728887 : Blo 1399519 4728887 := bstep (se 1 (by rfl) ⟨3546665, by rfl⟩ : syracuseStep 4728887 = 7093331) B7093331
theorem B7972937 : Blo 1399519 7972937 := bstep (se 2 (by rfl) ⟨2989851, by rfl⟩ : syracuseStep 7972937 = 5979703) B5979703
theorem B23014343 : Blo 1399519 23014343 := bstep (se 1 (by rfl) ⟨17260757, by rfl⟩ : syracuseStep 23014343 = 34521515) B34521515
theorem B3148955 : Blo 1399519 3148955 := bstep (se 1 (by rfl) ⟨2361716, by rfl⟩ : syracuseStep 3148955 = 4723433) B4723433
theorem B3149063 : Blo 1399519 3149063 := bstep (se 1 (by rfl) ⟨2361797, by rfl⟩ : syracuseStep 3149063 = 4723595) B4723595
theorem B5320637 : Blo 1399519 5320637 := bstep (se 3 (by rfl) ⟨997619, by rfl⟩ : syracuseStep 5320637 = 1995239) B1995239
theorem B8089895 : Blo 1399519 8089895 := bstep (se 1 (by rfl) ⟨6067421, by rfl⟩ : syracuseStep 8089895 = 12134843) B12134843
theorem B7975421 : Blo 1399519 7975421 := bstep (se 3 (by rfl) ⟨1495391, by rfl⟩ : syracuseStep 7975421 = 2990783) B2990783
theorem B5321321 : Blo 1399519 5321321 := bstep (se 2 (by rfl) ⟨1995495, by rfl⟩ : syracuseStep 5321321 = 3990991) B3990991
theorem B8976041 : Blo 1399519 8976041 := bstep (se 2 (by rfl) ⟨3366015, by rfl⟩ : syracuseStep 8976041 = 6732031) B6732031
theorem B80779031 : Blo 1399519 80779031 := bstep (se 1 (by rfl) ⟨60584273, by rfl⟩ : syracuseStep 80779031 = 121168547) B121168547
theorem B5314835 : Blo 1399519 5314835 := bstep (se 1 (by rfl) ⟨3986126, by rfl⟩ : syracuseStep 5314835 = 7972253) B7972253
theorem B3152375 : Blo 1399519 3152375 := bstep (se 1 (by rfl) ⟨2364281, by rfl⟩ : syracuseStep 3152375 = 4728563) B4728563
theorem B3152609 : Blo 1399519 3152609 := bstep (se 2 (by rfl) ⟨1182228, by rfl⟩ : syracuseStep 3152609 = 2364457) B2364457
theorem B1400479 : Blo 1399519 1400479 := bstep (se 1 (by rfl) ⟨1050359, by rfl⟩ : syracuseStep 1400479 = 2100719) B2100719
theorem B1400575 : Blo 1399519 1400575 := bstep (se 1 (by rfl) ⟨1050431, by rfl⟩ : syracuseStep 1400575 = 2100863) B2100863
theorem B3989407 : Blo 1399519 3989407 := bstep (se 1 (by rfl) ⟨2992055, by rfl⟩ : syracuseStep 3989407 = 5984111) B5984111
theorem B5316947 : Blo 1399519 5316947 := bstep (se 1 (by rfl) ⟨3987710, by rfl⟩ : syracuseStep 5316947 = 7975421) B7975421
theorem B3547547 : Blo 1399519 3547547 := bstep (se 1 (by rfl) ⟨2660660, by rfl⟩ : syracuseStep 3547547 = 5321321) B5321321
theorem B2099303 : Blo 1399519 2099303 := bstep (se 1 (by rfl) ⟨1574477, by rfl⟩ : syracuseStep 2099303 = 3148955) B3148955
theorem B2099375 : Blo 1399519 2099375 := bstep (se 1 (by rfl) ⟨1574531, by rfl⟩ : syracuseStep 2099375 = 3149063) B3149063
theorem B5319209 : Blo 1399519 5319209 := bstep (se 2 (by rfl) ⟨1994703, by rfl⟩ : syracuseStep 5319209 = 3989407) B3989407
theorem B4729535 : Blo 1399519 4729535 := bstep (se 1 (by rfl) ⟨3547151, by rfl⟩ : syracuseStep 4729535 = 7094303) B7094303
theorem B7973711 : Blo 1399519 7973711 := bstep (se 1 (by rfl) ⟨5980283, by rfl⟩ : syracuseStep 7973711 = 11960567) B11960567
theorem B5393263 : Blo 1399519 5393263 := bstep (se 1 (by rfl) ⟨4044947, by rfl⟩ : syracuseStep 5393263 = 8089895) B8089895
theorem B5984027 : Blo 1399519 5984027 := bstep (se 1 (by rfl) ⟨4488020, by rfl⟩ : syracuseStep 5984027 = 8976041) B8976041
theorem B3543223 : Blo 1399519 3543223 := bstep (se 1 (by rfl) ⟨2657417, by rfl⟩ : syracuseStep 3543223 = 5314835) B5314835
theorem B2101583 : Blo 1399519 2101583 := bstep (se 1 (by rfl) ⟨1576187, by rfl⟩ : syracuseStep 2101583 = 3152375) B3152375
theorem B2101739 : Blo 1399519 2101739 := bstep (se 1 (by rfl) ⟨1576304, by rfl⟩ : syracuseStep 2101739 = 3152609) B3152609
theorem B4724351 : Blo 1399519 4724351 := bstep (se 1 (by rfl) ⟨3543263, by rfl⟩ : syracuseStep 4724351 = 7086527) B7086527
theorem B53852687 : Blo 1399519 53852687 := bstep (se 1 (by rfl) ⟨40389515, by rfl⟩ : syracuseStep 53852687 = 80779031) B80779031
theorem B5675615 : Blo 1399519 5675615 := bstep (se 1 (by rfl) ⟨4256711, by rfl⟩ : syracuseStep 5675615 = 8513423) B8513423
theorem B3152591 : Blo 1399519 3152591 := bstep (se 1 (by rfl) ⟨2364443, by rfl⟩ : syracuseStep 3152591 = 4728887) B4728887
theorem B5315291 : Blo 1399519 5315291 := bstep (se 1 (by rfl) ⟨3986468, by rfl⟩ : syracuseStep 5315291 = 7972937) B7972937
theorem B15342895 : Blo 1399519 15342895 := bstep (se 1 (by rfl) ⟨11507171, by rfl⟩ : syracuseStep 15342895 = 23014343) B23014343
theorem B3547091 : Blo 1399519 3547091 := bstep (se 1 (by rfl) ⟨2660318, by rfl⟩ : syracuseStep 3547091 = 5320637) B5320637
theorem B1401055 : Blo 1399519 1401055 := bstep (se 1 (by rfl) ⟨1050791, by rfl⟩ : syracuseStep 1401055 = 2101583) B2101583
theorem B1401159 : Blo 1399519 1401159 := bstep (se 1 (by rfl) ⟨1050869, by rfl⟩ : syracuseStep 1401159 = 2101739) B2101739
theorem B20457193 : Blo 1399519 20457193 := bstep (se 2 (by rfl) ⟨7671447, by rfl⟩ : syracuseStep 20457193 = 15342895) B15342895
theorem B3149567 : Blo 1399519 3149567 := bstep (se 1 (by rfl) ⟨2362175, by rfl⟩ : syracuseStep 3149567 = 4724351) B4724351
theorem B35901791 : Blo 1399519 35901791 := bstep (se 1 (by rfl) ⟨26926343, by rfl⟩ : syracuseStep 35901791 = 53852687) B53852687
theorem B2101727 : Blo 1399519 2101727 := bstep (se 1 (by rfl) ⟨1576295, by rfl⟩ : syracuseStep 2101727 = 3152591) B3152591
theorem B3543527 : Blo 1399519 3543527 := bstep (se 1 (by rfl) ⟨2657645, by rfl⟩ : syracuseStep 3543527 = 5315291) B5315291
theorem B2364727 : Blo 1399519 2364727 := bstep (se 1 (by rfl) ⟨1773545, by rfl⟩ : syracuseStep 2364727 = 3547091) B3547091
theorem B3544631 : Blo 1399519 3544631 := bstep (se 1 (by rfl) ⟨2658473, by rfl⟩ : syracuseStep 3544631 = 5316947) B5316947
theorem B4724297 : Blo 1399519 4724297 := bstep (se 2 (by rfl) ⟨1771611, by rfl⟩ : syracuseStep 4724297 = 3543223) B3543223
theorem B2365031 : Blo 1399519 2365031 := bstep (se 1 (by rfl) ⟨1773773, by rfl⟩ : syracuseStep 2365031 = 3547547) B3547547
theorem B7191017 : Blo 1399519 7191017 := bstep (se 2 (by rfl) ⟨2696631, by rfl⟩ : syracuseStep 7191017 = 5393263) B5393263
theorem B1399535 : Blo 1399519 1399535 := bstep (se 1 (by rfl) ⟨1049651, by rfl⟩ : syracuseStep 1399535 = 2099303) B2099303
theorem B1399583 : Blo 1399519 1399583 := bstep (se 1 (by rfl) ⟨1049687, by rfl⟩ : syracuseStep 1399583 = 2099375) B2099375
theorem B3546139 : Blo 1399519 3546139 := bstep (se 1 (by rfl) ⟨2659604, by rfl⟩ : syracuseStep 3546139 = 5319209) B5319209
theorem B3783743 : Blo 1399519 3783743 := bstep (se 1 (by rfl) ⟨2837807, by rfl⟩ : syracuseStep 3783743 = 5675615) B5675615
theorem B3153023 : Blo 1399519 3153023 := bstep (se 1 (by rfl) ⟨2364767, by rfl⟩ : syracuseStep 3153023 = 4729535) B4729535
theorem B5315807 : Blo 1399519 5315807 := bstep (se 1 (by rfl) ⟨3986855, by rfl⟩ : syracuseStep 5315807 = 7973711) B7973711
theorem B3989351 : Blo 1399519 3989351 := bstep (se 1 (by rfl) ⟨2992013, by rfl⟩ : syracuseStep 3989351 = 5984027) B5984027
theorem B1401151 : Blo 1399519 1401151 := bstep (se 1 (by rfl) ⟨1050863, by rfl⟩ : syracuseStep 1401151 = 2101727) B2101727
theorem B4728185 : Blo 1399519 4728185 := bstep (se 2 (by rfl) ⟨1773069, by rfl⟩ : syracuseStep 4728185 = 3546139) B3546139
theorem B4794011 : Blo 1399519 4794011 := bstep (se 1 (by rfl) ⟨3595508, by rfl⟩ : syracuseStep 4794011 = 7191017) B7191017
theorem B2099711 : Blo 1399519 2099711 := bstep (se 1 (by rfl) ⟨1574783, by rfl⟩ : syracuseStep 2099711 = 3149567) B3149567
theorem B2362351 : Blo 1399519 2362351 := bstep (se 1 (by rfl) ⟨1771763, by rfl⟩ : syracuseStep 2362351 = 3543527) B3543527
theorem B2363087 : Blo 1399519 2363087 := bstep (se 1 (by rfl) ⟨1772315, by rfl⟩ : syracuseStep 2363087 = 3544631) B3544631
theorem B3149531 : Blo 1399519 3149531 := bstep (se 1 (by rfl) ⟨2362148, by rfl⟩ : syracuseStep 3149531 = 4724297) B4724297
theorem B1576687 : Blo 1399519 1576687 := bstep (se 1 (by rfl) ⟨1182515, by rfl⟩ : syracuseStep 1576687 = 2365031) B2365031
theorem B2102015 : Blo 1399519 2102015 := bstep (se 1 (by rfl) ⟨1576511, by rfl⟩ : syracuseStep 2102015 = 3153023) B3153023
theorem B3543871 : Blo 1399519 3543871 := bstep (se 1 (by rfl) ⟨2657903, by rfl⟩ : syracuseStep 3543871 = 5315807) B5315807
theorem B27276257 : Blo 1399519 27276257 := bstep (se 2 (by rfl) ⟨10228596, by rfl⟩ : syracuseStep 27276257 = 20457193) B20457193
theorem B2659567 : Blo 1399519 2659567 := bstep (se 1 (by rfl) ⟨1994675, by rfl⟩ : syracuseStep 2659567 = 3989351) B3989351
theorem B23934527 : Blo 1399519 23934527 := bstep (se 1 (by rfl) ⟨17950895, by rfl⟩ : syracuseStep 23934527 = 35901791) B35901791
theorem B3152969 : Blo 1399519 3152969 := bstep (se 2 (by rfl) ⟨1182363, by rfl⟩ : syracuseStep 3152969 = 2364727) B2364727
theorem B2522495 : Blo 1399519 2522495 := bstep (se 1 (by rfl) ⟨1891871, by rfl⟩ : syracuseStep 2522495 = 3783743) B3783743
theorem B1401343 : Blo 1399519 1401343 := bstep (se 1 (by rfl) ⟨1051007, by rfl⟩ : syracuseStep 1401343 = 2102015) B2102015
theorem B3196007 : Blo 1399519 3196007 := bstep (se 1 (by rfl) ⟨2397005, by rfl⟩ : syracuseStep 3196007 = 4794011) B4794011
theorem B1681663 : Blo 1399519 1681663 := bstep (se 1 (by rfl) ⟨1261247, by rfl⟩ : syracuseStep 1681663 = 2522495) B2522495
theorem B1575391 : Blo 1399519 1575391 := bstep (se 1 (by rfl) ⟨1181543, by rfl⟩ : syracuseStep 1575391 = 2363087) B2363087
theorem B2099687 : Blo 1399519 2099687 := bstep (se 1 (by rfl) ⟨1574765, by rfl⟩ : syracuseStep 2099687 = 3149531) B3149531
theorem B3149801 : Blo 1399519 3149801 := bstep (se 2 (by rfl) ⟨1181175, by rfl⟩ : syracuseStep 3149801 = 2362351) B2362351
theorem B2101979 : Blo 1399519 2101979 := bstep (se 1 (by rfl) ⟨1576484, by rfl⟩ : syracuseStep 2101979 = 3152969) B3152969
theorem B2102249 : Blo 1399519 2102249 := bstep (se 2 (by rfl) ⟨788343, by rfl⟩ : syracuseStep 2102249 = 1576687) B1576687
theorem B18184171 : Blo 1399519 18184171 := bstep (se 1 (by rfl) ⟨13638128, by rfl⟩ : syracuseStep 18184171 = 27276257) B27276257
theorem B3152123 : Blo 1399519 3152123 := bstep (se 1 (by rfl) ⟨2364092, by rfl⟩ : syracuseStep 3152123 = 4728185) B4728185
theorem B15956351 : Blo 1399519 15956351 := bstep (se 1 (by rfl) ⟨11967263, by rfl⟩ : syracuseStep 15956351 = 23934527) B23934527
theorem B4725161 : Blo 1399519 4725161 := bstep (se 2 (by rfl) ⟨1771935, by rfl⟩ : syracuseStep 4725161 = 3543871) B3543871
theorem B3546089 : Blo 1399519 3546089 := bstep (se 2 (by rfl) ⟨1329783, by rfl⟩ : syracuseStep 3546089 = 2659567) B2659567
theorem B1399807 : Blo 1399519 1399807 := bstep (se 1 (by rfl) ⟨1049855, by rfl⟩ : syracuseStep 1399807 = 2099711) B2099711
theorem B1401319 : Blo 1399519 1401319 := bstep (se 1 (by rfl) ⟨1050989, by rfl⟩ : syracuseStep 1401319 = 2101979) B2101979
theorem B1401499 : Blo 1399519 1401499 := bstep (se 1 (by rfl) ⟨1051124, by rfl⟩ : syracuseStep 1401499 = 2102249) B2102249
theorem B2130671 : Blo 1399519 2130671 := bstep (se 1 (by rfl) ⟨1598003, by rfl⟩ : syracuseStep 2130671 = 3196007) B3196007
theorem B2099867 : Blo 1399519 2099867 := bstep (se 1 (by rfl) ⟨1574900, by rfl⟩ : syracuseStep 2099867 = 3149801) B3149801
theorem B2100521 : Blo 1399519 2100521 := bstep (se 2 (by rfl) ⟨787695, by rfl⟩ : syracuseStep 2100521 = 1575391) B1575391
theorem B2101415 : Blo 1399519 2101415 := bstep (se 1 (by rfl) ⟨1576061, by rfl⟩ : syracuseStep 2101415 = 3152123) B3152123
theorem B10637567 : Blo 1399519 10637567 := bstep (se 1 (by rfl) ⟨7978175, by rfl⟩ : syracuseStep 10637567 = 15956351) B15956351
theorem B3150107 : Blo 1399519 3150107 := bstep (se 1 (by rfl) ⟨2362580, by rfl⟩ : syracuseStep 3150107 = 4725161) B4725161
theorem B2364059 : Blo 1399519 2364059 := bstep (se 1 (by rfl) ⟨1773044, by rfl⟩ : syracuseStep 2364059 = 3546089) B3546089
theorem B24245561 : Blo 1399519 24245561 := bstep (se 2 (by rfl) ⟨9092085, by rfl⟩ : syracuseStep 24245561 = 18184171) B18184171
theorem B2242217 : Blo 1399519 2242217 := bstep (se 2 (by rfl) ⟨840831, by rfl⟩ : syracuseStep 2242217 = 1681663) B1681663
theorem B1399791 : Blo 1399519 1399791 := bstep (se 1 (by rfl) ⟨1049843, by rfl⟩ : syracuseStep 1399791 = 2099687) B2099687
theorem B1400943 : Blo 1399519 1400943 := bstep (se 1 (by rfl) ⟨1050707, by rfl⟩ : syracuseStep 1400943 = 2101415) B2101415
theorem B16163707 : Blo 1399519 16163707 := bstep (se 1 (by rfl) ⟨12122780, by rfl⟩ : syracuseStep 16163707 = 24245561) B24245561
theorem B2100071 : Blo 1399519 2100071 := bstep (se 1 (by rfl) ⟨1575053, by rfl⟩ : syracuseStep 2100071 = 3150107) B3150107
theorem B1576039 : Blo 1399519 1576039 := bstep (se 1 (by rfl) ⟨1182029, by rfl⟩ : syracuseStep 1576039 = 2364059) B2364059
theorem B1494811 : Blo 1399519 1494811 := bstep (se 1 (by rfl) ⟨1121108, by rfl⟩ : syracuseStep 1494811 = 2242217) B2242217
theorem B5681789 : Blo 1399519 5681789 := bstep (se 3 (by rfl) ⟨1065335, by rfl⟩ : syracuseStep 5681789 = 2130671) B2130671
theorem B7091711 : Blo 1399519 7091711 := bstep (se 1 (by rfl) ⟨5318783, by rfl⟩ : syracuseStep 7091711 = 10637567) B10637567
theorem B1399911 : Blo 1399519 1399911 := bstep (se 1 (by rfl) ⟨1049933, by rfl⟩ : syracuseStep 1399911 = 2099867) B2099867
theorem B1400347 : Blo 1399519 1400347 := bstep (se 1 (by rfl) ⟨1050260, by rfl⟩ : syracuseStep 1400347 = 2100521) B2100521
theorem B4727807 : Blo 1399519 4727807 := bstep (se 1 (by rfl) ⟨3545855, by rfl⟩ : syracuseStep 4727807 = 7091711) B7091711
theorem B1993081 : Blo 1399519 1993081 := bstep (se 2 (by rfl) ⟨747405, by rfl⟩ : syracuseStep 1993081 = 1494811) B1494811
theorem B3787859 : Blo 1399519 3787859 := bstep (se 1 (by rfl) ⟨2840894, by rfl⟩ : syracuseStep 3787859 = 5681789) B5681789
theorem B2101385 : Blo 1399519 2101385 := bstep (se 2 (by rfl) ⟨788019, by rfl⟩ : syracuseStep 2101385 = 1576039) B1576039
theorem B21551609 : Blo 1399519 21551609 := bstep (se 2 (by rfl) ⟨8081853, by rfl⟩ : syracuseStep 21551609 = 16163707) B16163707
theorem B1400047 : Blo 1399519 1400047 := bstep (se 1 (by rfl) ⟨1050035, by rfl⟩ : syracuseStep 1400047 = 2100071) B2100071
theorem B1400923 : Blo 1399519 1400923 := bstep (se 1 (by rfl) ⟨1050692, by rfl⟩ : syracuseStep 1400923 = 2101385) B2101385
theorem B2525239 : Blo 1399519 2525239 := bstep (se 1 (by rfl) ⟨1893929, by rfl⟩ : syracuseStep 2525239 = 3787859) B3787859
theorem B2657441 : Blo 1399519 2657441 := bstep (se 2 (by rfl) ⟨996540, by rfl⟩ : syracuseStep 2657441 = 1993081) B1993081
theorem B57470957 : Blo 1399519 57470957 := bstep (se 3 (by rfl) ⟨10775804, by rfl⟩ : syracuseStep 57470957 = 21551609) B21551609
theorem B3151871 : Blo 1399519 3151871 := bstep (se 1 (by rfl) ⟨2363903, by rfl⟩ : syracuseStep 3151871 = 4727807) B4727807
theorem B13467941 : Blo 1399519 13467941 := bstep (se 4 (by rfl) ⟨1262619, by rfl⟩ : syracuseStep 13467941 = 2525239) B2525239
theorem B1771627 : Blo 1399519 1771627 := bstep (se 1 (by rfl) ⟨1328720, by rfl⟩ : syracuseStep 1771627 = 2657441) B2657441
theorem B2101247 : Blo 1399519 2101247 := bstep (se 1 (by rfl) ⟨1575935, by rfl⟩ : syracuseStep 2101247 = 3151871) B3151871
theorem B38313971 : Blo 1399519 38313971 := bstep (se 1 (by rfl) ⟨28735478, by rfl⟩ : syracuseStep 38313971 = 57470957) B57470957
theorem B8978627 : Blo 1399519 8978627 := bstep (se 1 (by rfl) ⟨6733970, by rfl⟩ : syracuseStep 8978627 = 13467941) B13467941
theorem B2362169 : Blo 1399519 2362169 := bstep (se 2 (by rfl) ⟨885813, by rfl⟩ : syracuseStep 2362169 = 1771627) B1771627
theorem B25542647 : Blo 1399519 25542647 := bstep (se 1 (by rfl) ⟨19156985, by rfl⟩ : syracuseStep 25542647 = 38313971) B38313971
theorem B1400831 : Blo 1399519 1400831 := bstep (se 1 (by rfl) ⟨1050623, by rfl⟩ : syracuseStep 1400831 = 2101247) B2101247
theorem B1574779 : Blo 1399519 1574779 := bstep (se 1 (by rfl) ⟨1181084, by rfl⟩ : syracuseStep 1574779 = 2362169) B2362169
theorem B17028431 : Blo 1399519 17028431 := bstep (se 1 (by rfl) ⟨12771323, by rfl⟩ : syracuseStep 17028431 = 25542647) B25542647
theorem B5985751 : Blo 1399519 5985751 := bstep (se 1 (by rfl) ⟨4489313, by rfl⟩ : syracuseStep 5985751 = 8978627) B8978627
theorem B7981001 : Blo 1399519 7981001 := bstep (se 2 (by rfl) ⟨2992875, by rfl⟩ : syracuseStep 7981001 = 5985751) B5985751
theorem B2099705 : Blo 1399519 2099705 := bstep (se 2 (by rfl) ⟨787389, by rfl⟩ : syracuseStep 2099705 = 1574779) B1574779
theorem B11352287 : Blo 1399519 11352287 := bstep (se 1 (by rfl) ⟨8514215, by rfl⟩ : syracuseStep 11352287 = 17028431) B17028431
theorem B5320667 : Blo 1399519 5320667 := bstep (se 1 (by rfl) ⟨3990500, by rfl⟩ : syracuseStep 5320667 = 7981001) B7981001
theorem B7568191 : Blo 1399519 7568191 := bstep (se 1 (by rfl) ⟨5676143, by rfl⟩ : syracuseStep 7568191 = 11352287) B11352287
theorem B1399803 : Blo 1399519 1399803 := bstep (se 1 (by rfl) ⟨1049852, by rfl⟩ : syracuseStep 1399803 = 2099705) B2099705
theorem B10090921 : Blo 1399519 10090921 := bstep (se 2 (by rfl) ⟨3784095, by rfl⟩ : syracuseStep 10090921 = 7568191) B7568191
theorem B3547111 : Blo 1399519 3547111 := bstep (se 1 (by rfl) ⟨2660333, by rfl⟩ : syracuseStep 3547111 = 5320667) B5320667
theorem B4729481 : Blo 1399519 4729481 := bstep (se 2 (by rfl) ⟨1773555, by rfl⟩ : syracuseStep 4729481 = 3547111) B3547111
theorem B13454561 : Blo 1399519 13454561 := bstep (se 2 (by rfl) ⟨5045460, by rfl⟩ : syracuseStep 13454561 = 10090921) B10090921
theorem B3152987 : Blo 1399519 3152987 := bstep (se 1 (by rfl) ⟨2364740, by rfl⟩ : syracuseStep 3152987 = 4729481) B4729481
theorem B8969707 : Blo 1399519 8969707 := bstep (se 1 (by rfl) ⟨6727280, by rfl⟩ : syracuseStep 8969707 = 13454561) B13454561
theorem B2101991 : Blo 1399519 2101991 := bstep (se 1 (by rfl) ⟨1576493, by rfl⟩ : syracuseStep 2101991 = 3152987) B3152987
theorem B11959609 : Blo 1399519 11959609 := bstep (se 2 (by rfl) ⟨4484853, by rfl⟩ : syracuseStep 11959609 = 8969707) B8969707
theorem B1401327 : Blo 1399519 1401327 := bstep (se 1 (by rfl) ⟨1050995, by rfl⟩ : syracuseStep 1401327 = 2101991) B2101991
theorem B15946145 : Blo 1399519 15946145 := bstep (se 2 (by rfl) ⟨5979804, by rfl⟩ : syracuseStep 15946145 = 11959609) B11959609
theorem B10630763 : Blo 1399519 10630763 := bstep (se 1 (by rfl) ⟨7973072, by rfl⟩ : syracuseStep 10630763 = 15946145) B15946145
theorem B7087175 : Blo 1399519 7087175 := bstep (se 1 (by rfl) ⟨5315381, by rfl⟩ : syracuseStep 7087175 = 10630763) B10630763
theorem B4724783 : Blo 1399519 4724783 := bstep (se 1 (by rfl) ⟨3543587, by rfl⟩ : syracuseStep 4724783 = 7087175) B7087175
theorem B3149855 : Blo 1399519 3149855 := bstep (se 1 (by rfl) ⟨2362391, by rfl⟩ : syracuseStep 3149855 = 4724783) B4724783
theorem B2099903 : Blo 1399519 2099903 := bstep (se 1 (by rfl) ⟨1574927, by rfl⟩ : syracuseStep 2099903 = 3149855) B3149855
theorem B1399935 : Blo 1399519 1399935 := bstep (se 1 (by rfl) ⟨1049951, by rfl⟩ : syracuseStep 1399935 = 2099903) B2099903

theorem C0 (j : ℕ) (h1 : 349879 ≤ j) (h2 : j ≤ 350379) : Blo 1399519 (4 * j + 3) := by
  interval_cases j
  · exact B1399519
  · exact B1399523
  · exact B1399527
  · exact B1399531
  · exact B1399535
  · exact B1399539
  · exact B1399543
  · exact B1399547
  · exact B1399551
  · exact B1399555
  · exact B1399559
  · exact B1399563
  · exact B1399567
  · exact B1399571
  · exact B1399575
  · exact B1399579
  · exact B1399583
  · exact B1399587
  · exact B1399591
  · exact B1399595
  · exact B1399599
  · exact B1399603
  · exact B1399607
  · exact B1399611
  · exact B1399615
  · exact B1399619
  · exact B1399623
  · exact B1399627
  · exact B1399631
  · exact B1399635
  · exact B1399639
  · exact B1399643
  · exact B1399647
  · exact B1399651
  · exact B1399655
  · exact B1399659
  · exact B1399663
  · exact B1399667
  · exact B1399671
  · exact B1399675
  · exact B1399679
  · exact B1399683
  · exact B1399687
  · exact B1399691
  · exact B1399695
  · exact B1399699
  · exact B1399703
  · exact B1399707
  · exact B1399711
  · exact B1399715
  · exact B1399719
  · exact B1399723
  · exact B1399727
  · exact B1399731
  · exact B1399735
  · exact B1399739
  · exact B1399743
  · exact B1399747
  · exact B1399751
  · exact B1399755
  · exact B1399759
  · exact B1399763
  · exact B1399767
  · exact B1399771
  · exact B1399775
  · exact B1399779
  · exact B1399783
  · exact B1399787
  · exact B1399791
  · exact B1399795
  · exact B1399799
  · exact B1399803
  · exact B1399807
  · exact B1399811
  · exact B1399815
  · exact B1399819
  · exact B1399823
  · exact B1399827
  · exact B1399831
  · exact B1399835
  · exact B1399839
  · exact B1399843
  · exact B1399847
  · exact B1399851
  · exact B1399855
  · exact B1399859
  · exact B1399863
  · exact B1399867
  · exact B1399871
  · exact B1399875
  · exact B1399879
  · exact B1399883
  · exact B1399887
  · exact B1399891
  · exact B1399895
  · exact B1399899
  · exact B1399903
  · exact B1399907
  · exact B1399911
  · exact B1399915
  · exact B1399919
  · exact B1399923
  · exact B1399927
  · exact B1399931
  · exact B1399935
  · exact B1399939
  · exact B1399943
  · exact B1399947
  · exact B1399951
  · exact B1399955
  · exact B1399959
  · exact B1399963
  · exact B1399967
  · exact B1399971
  · exact B1399975
  · exact B1399979
  · exact B1399983
  · exact B1399987
  · exact B1399991
  · exact B1399995
  · exact B1399999
  · exact B1400003
  · exact B1400007
  · exact B1400011
  · exact B1400015
  · exact B1400019
  · exact B1400023
  · exact B1400027
  · exact B1400031
  · exact B1400035
  · exact B1400039
  · exact B1400043
  · exact B1400047
  · exact B1400051
  · exact B1400055
  · exact B1400059
  · exact B1400063
  · exact B1400067
  · exact B1400071
  · exact B1400075
  · exact B1400079
  · exact B1400083
  · exact B1400087
  · exact B1400091
  · exact B1400095
  · exact B1400099
  · exact B1400103
  · exact B1400107
  · exact B1400111
  · exact B1400115
  · exact B1400119
  · exact B1400123
  · exact B1400127
  · exact B1400131
  · exact B1400135
  · exact B1400139
  · exact B1400143
  · exact B1400147
  · exact B1400151
  · exact B1400155
  · exact B1400159
  · exact B1400163
  · exact B1400167
  · exact B1400171
  · exact B1400175
  · exact B1400179
  · exact B1400183
  · exact B1400187
  · exact B1400191
  · exact B1400195
  · exact B1400199
  · exact B1400203
  · exact B1400207
  · exact B1400211
  · exact B1400215
  · exact B1400219
  · exact B1400223
  · exact B1400227
  · exact B1400231
  · exact B1400235
  · exact B1400239
  · exact B1400243
  · exact B1400247
  · exact B1400251
  · exact B1400255
  · exact B1400259
  · exact B1400263
  · exact B1400267
  · exact B1400271
  · exact B1400275
  · exact B1400279
  · exact B1400283
  · exact B1400287
  · exact B1400291
  · exact B1400295
  · exact B1400299
  · exact B1400303
  · exact B1400307
  · exact B1400311
  · exact B1400315
  · exact B1400319
  · exact B1400323
  · exact B1400327
  · exact B1400331
  · exact B1400335
  · exact B1400339
  · exact B1400343
  · exact B1400347
  · exact B1400351
  · exact B1400355
  · exact B1400359
  · exact B1400363
  · exact B1400367
  · exact B1400371
  · exact B1400375
  · exact B1400379
  · exact B1400383
  · exact B1400387
  · exact B1400391
  · exact B1400395
  · exact B1400399
  · exact B1400403
  · exact B1400407
  · exact B1400411
  · exact B1400415
  · exact B1400419
  · exact B1400423
  · exact B1400427
  · exact B1400431
  · exact B1400435
  · exact B1400439
  · exact B1400443
  · exact B1400447
  · exact B1400451
  · exact B1400455
  · exact B1400459
  · exact B1400463
  · exact B1400467
  · exact B1400471
  · exact B1400475
  · exact B1400479
  · exact B1400483
  · exact B1400487
  · exact B1400491
  · exact B1400495
  · exact B1400499
  · exact B1400503
  · exact B1400507
  · exact B1400511
  · exact B1400515
  · exact B1400519
  · exact B1400523
  · exact B1400527
  · exact B1400531
  · exact B1400535
  · exact B1400539
  · exact B1400543
  · exact B1400547
  · exact B1400551
  · exact B1400555
  · exact B1400559
  · exact B1400563
  · exact B1400567
  · exact B1400571
  · exact B1400575
  · exact B1400579
  · exact B1400583
  · exact B1400587
  · exact B1400591
  · exact B1400595
  · exact B1400599
  · exact B1400603
  · exact B1400607
  · exact B1400611
  · exact B1400615
  · exact B1400619
  · exact B1400623
  · exact B1400627
  · exact B1400631
  · exact B1400635
  · exact B1400639
  · exact B1400643
  · exact B1400647
  · exact B1400651
  · exact B1400655
  · exact B1400659
  · exact B1400663
  · exact B1400667
  · exact B1400671
  · exact B1400675
  · exact B1400679
  · exact B1400683
  · exact B1400687
  · exact B1400691
  · exact B1400695
  · exact B1400699
  · exact B1400703
  · exact B1400707
  · exact B1400711
  · exact B1400715
  · exact B1400719
  · exact B1400723
  · exact B1400727
  · exact B1400731
  · exact B1400735
  · exact B1400739
  · exact B1400743
  · exact B1400747
  · exact B1400751
  · exact B1400755
  · exact B1400759
  · exact B1400763
  · exact B1400767
  · exact B1400771
  · exact B1400775
  · exact B1400779
  · exact B1400783
  · exact B1400787
  · exact B1400791
  · exact B1400795
  · exact B1400799
  · exact B1400803
  · exact B1400807
  · exact B1400811
  · exact B1400815
  · exact B1400819
  · exact B1400823
  · exact B1400827
  · exact B1400831
  · exact B1400835
  · exact B1400839
  · exact B1400843
  · exact B1400847
  · exact B1400851
  · exact B1400855
  · exact B1400859
  · exact B1400863
  · exact B1400867
  · exact B1400871
  · exact B1400875
  · exact B1400879
  · exact B1400883
  · exact B1400887
  · exact B1400891
  · exact B1400895
  · exact B1400899
  · exact B1400903
  · exact B1400907
  · exact B1400911
  · exact B1400915
  · exact B1400919
  · exact B1400923
  · exact B1400927
  · exact B1400931
  · exact B1400935
  · exact B1400939
  · exact B1400943
  · exact B1400947
  · exact B1400951
  · exact B1400955
  · exact B1400959
  · exact B1400963
  · exact B1400967
  · exact B1400971
  · exact B1400975
  · exact B1400979
  · exact B1400983
  · exact B1400987
  · exact B1400991
  · exact B1400995
  · exact B1400999
  · exact B1401003
  · exact B1401007
  · exact B1401011
  · exact B1401015
  · exact B1401019
  · exact B1401023
  · exact B1401027
  · exact B1401031
  · exact B1401035
  · exact B1401039
  · exact B1401043
  · exact B1401047
  · exact B1401051
  · exact B1401055
  · exact B1401059
  · exact B1401063
  · exact B1401067
  · exact B1401071
  · exact B1401075
  · exact B1401079
  · exact B1401083
  · exact B1401087
  · exact B1401091
  · exact B1401095
  · exact B1401099
  · exact B1401103
  · exact B1401107
  · exact B1401111
  · exact B1401115
  · exact B1401119
  · exact B1401123
  · exact B1401127
  · exact B1401131
  · exact B1401135
  · exact B1401139
  · exact B1401143
  · exact B1401147
  · exact B1401151
  · exact B1401155
  · exact B1401159
  · exact B1401163
  · exact B1401167
  · exact B1401171
  · exact B1401175
  · exact B1401179
  · exact B1401183
  · exact B1401187
  · exact B1401191
  · exact B1401195
  · exact B1401199
  · exact B1401203
  · exact B1401207
  · exact B1401211
  · exact B1401215
  · exact B1401219
  · exact B1401223
  · exact B1401227
  · exact B1401231
  · exact B1401235
  · exact B1401239
  · exact B1401243
  · exact B1401247
  · exact B1401251
  · exact B1401255
  · exact B1401259
  · exact B1401263
  · exact B1401267
  · exact B1401271
  · exact B1401275
  · exact B1401279
  · exact B1401283
  · exact B1401287
  · exact B1401291
  · exact B1401295
  · exact B1401299
  · exact B1401303
  · exact B1401307
  · exact B1401311
  · exact B1401315
  · exact B1401319
  · exact B1401323
  · exact B1401327
  · exact B1401331
  · exact B1401335
  · exact B1401339
  · exact B1401343
  · exact B1401347
  · exact B1401351
  · exact B1401355
  · exact B1401359
  · exact B1401363
  · exact B1401367
  · exact B1401371
  · exact B1401375
  · exact B1401379
  · exact B1401383
  · exact B1401387
  · exact B1401391
  · exact B1401395
  · exact B1401399
  · exact B1401403
  · exact B1401407
  · exact B1401411
  · exact B1401415
  · exact B1401419
  · exact B1401423
  · exact B1401427
  · exact B1401431
  · exact B1401435
  · exact B1401439
  · exact B1401443
  · exact B1401447
  · exact B1401451
  · exact B1401455
  · exact B1401459
  · exact B1401463
  · exact B1401467
  · exact B1401471
  · exact B1401475
  · exact B1401479
  · exact B1401483
  · exact B1401487
  · exact B1401491
  · exact B1401495
  · exact B1401499
  · exact B1401503
  · exact B1401507
  · exact B1401511
  · exact B1401515
  · exact B1401519

theorem solution (m : ℕ) (hlo : 1399519 ≤ m) (hhi : m ≤ 1401519) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 349879 ≤ j := by omega
    have hj2 : j ≤ 350379 := by omega
    have hb : Blo 1399519 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
