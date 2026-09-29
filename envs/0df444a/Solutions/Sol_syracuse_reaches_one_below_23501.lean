-- Prove2me | solution 1 for syracuse_reaches_one_below_23501
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:05:59.321838+00:00
-- url     : https://prove2.me/submissions/930f2af3-951c-4b49-91df-97f5253c5b6b

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_20001

set_option maxHeartbeats 1000000

open Nat

abbrev Reach (n : ℕ) : Prop := ∃ j : ℕ, syracuseStep^[j] n = 1

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem rs {x y : ℕ} (h : syracuseStep x = y) (hy : Reach y) : Reach x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact hj⟩

/-- Everything below the previously verified bound is already known to reach 1. -/
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 20000) : Reach n :=
  syracuse_reaches_one_below_20001 n h1 h2 h3
theorem R32789 : Reach 32789 := rs (se 6 (by rfl) ⟨768, by rfl⟩) (B 1537 (by norm_num) ⟨768, by rfl⟩ (by norm_num))
theorem R32813 : Reach 32813 := rs (se 3 (by rfl) ⟨6152, by rfl⟩) (B 12305 (by norm_num) ⟨6152, by rfl⟩ (by norm_num))
theorem R32837 : Reach 32837 := rs (se 4 (by rfl) ⟨3078, by rfl⟩) (B 6157 (by norm_num) ⟨3078, by rfl⟩ (by norm_num))
theorem R32861 : Reach 32861 := rs (se 3 (by rfl) ⟨6161, by rfl⟩) (B 12323 (by norm_num) ⟨6161, by rfl⟩ (by norm_num))
theorem R32885 : Reach 32885 := rs (se 5 (by rfl) ⟨1541, by rfl⟩) (B 3083 (by norm_num) ⟨1541, by rfl⟩ (by norm_num))
theorem R32909 : Reach 32909 := rs (se 3 (by rfl) ⟨6170, by rfl⟩) (B 12341 (by norm_num) ⟨6170, by rfl⟩ (by norm_num))
theorem R65701 : Reach 65701 := rs (se 4 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R32933 : Reach 32933 := rs (se 4 (by rfl) ⟨3087, by rfl⟩) (B 6175 (by norm_num) ⟨3087, by rfl⟩ (by norm_num))
theorem R32957 : Reach 32957 := rs (se 3 (by rfl) ⟨6179, by rfl⟩) (B 12359 (by norm_num) ⟨6179, by rfl⟩ (by norm_num))
theorem R32981 : Reach 32981 := rs (se 7 (by rfl) ⟨386, by rfl⟩) (B 773 (by norm_num) ⟨386, by rfl⟩ (by norm_num))
theorem R65765 : Reach 65765 := rs (se 4 (by rfl) ⟨6165, by rfl⟩) (B 12331 (by norm_num) ⟨6165, by rfl⟩ (by norm_num))
theorem R33005 : Reach 33005 := rs (se 3 (by rfl) ⟨6188, by rfl⟩) (B 12377 (by norm_num) ⟨6188, by rfl⟩ (by norm_num))
theorem R33029 : Reach 33029 := rs (se 4 (by rfl) ⟨3096, by rfl⟩) (B 6193 (by norm_num) ⟨3096, by rfl⟩ (by norm_num))
theorem R33053 : Reach 33053 := rs (se 3 (by rfl) ⟨6197, by rfl⟩) (B 12395 (by norm_num) ⟨6197, by rfl⟩ (by norm_num))
theorem R33077 : Reach 33077 := rs (se 5 (by rfl) ⟨1550, by rfl⟩) (B 3101 (by norm_num) ⟨1550, by rfl⟩ (by norm_num))
theorem R131381 : Reach 131381 := rs (se 5 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R33101 : Reach 33101 := rs (se 3 (by rfl) ⟨6206, by rfl⟩) (B 12413 (by norm_num) ⟨6206, by rfl⟩ (by norm_num))
theorem R33125 : Reach 33125 := rs (se 4 (by rfl) ⟨3105, by rfl⟩) (B 6211 (by norm_num) ⟨3105, by rfl⟩ (by norm_num))
theorem R33149 : Reach 33149 := rs (se 3 (by rfl) ⟨6215, by rfl⟩) (B 12431 (by norm_num) ⟨6215, by rfl⟩ (by norm_num))
theorem R33173 : Reach 33173 := rs (se 6 (by rfl) ⟨777, by rfl⟩) (B 1555 (by norm_num) ⟨777, by rfl⟩ (by norm_num))
theorem R33197 : Reach 33197 := rs (se 3 (by rfl) ⟨6224, by rfl⟩) (B 12449 (by norm_num) ⟨6224, by rfl⟩ (by norm_num))
theorem R33221 : Reach 33221 := rs (se 4 (by rfl) ⟨3114, by rfl⟩) (B 6229 (by norm_num) ⟨3114, by rfl⟩ (by norm_num))
theorem R33245 : Reach 33245 := rs (se 3 (by rfl) ⟨6233, by rfl⟩) (B 12467 (by norm_num) ⟨6233, by rfl⟩ (by norm_num))
theorem R33253 : Reach 33253 := rs (se 4 (by rfl) ⟨3117, by rfl⟩) (B 6235 (by norm_num) ⟨3117, by rfl⟩ (by norm_num))
theorem R33269 : Reach 33269 := rs (se 5 (by rfl) ⟨1559, by rfl⟩) (B 3119 (by norm_num) ⟨1559, by rfl⟩ (by norm_num))
theorem R33293 : Reach 33293 := rs (se 3 (by rfl) ⟨6242, by rfl⟩) (B 12485 (by norm_num) ⟨6242, by rfl⟩ (by norm_num))
theorem R33301 : Reach 33301 := rs (se 6 (by rfl) ⟨780, by rfl⟩) (B 1561 (by norm_num) ⟨780, by rfl⟩ (by norm_num))
theorem R33317 : Reach 33317 := rs (se 4 (by rfl) ⟨3123, by rfl⟩) (B 6247 (by norm_num) ⟨3123, by rfl⟩ (by norm_num))
theorem R33341 : Reach 33341 := rs (se 3 (by rfl) ⟨6251, by rfl⟩) (B 12503 (by norm_num) ⟨6251, by rfl⟩ (by norm_num))
theorem R33365 : Reach 33365 := rs (se 8 (by rfl) ⟨195, by rfl⟩) (B 391 (by norm_num) ⟨195, by rfl⟩ (by norm_num))
theorem R33389 : Reach 33389 := rs (se 3 (by rfl) ⟨6260, by rfl⟩) (B 12521 (by norm_num) ⟨6260, by rfl⟩ (by norm_num))
theorem R33413 : Reach 33413 := rs (se 4 (by rfl) ⟨3132, by rfl⟩) (B 6265 (by norm_num) ⟨3132, by rfl⟩ (by norm_num))
theorem R33437 : Reach 33437 := rs (se 3 (by rfl) ⟨6269, by rfl⟩) (B 12539 (by norm_num) ⟨6269, by rfl⟩ (by norm_num))
theorem R33461 : Reach 33461 := rs (se 5 (by rfl) ⟨1568, by rfl⟩) (B 3137 (by norm_num) ⟨1568, by rfl⟩ (by norm_num))
theorem R33485 : Reach 33485 := rs (se 3 (by rfl) ⟨6278, by rfl⟩) (B 12557 (by norm_num) ⟨6278, by rfl⟩ (by norm_num))
theorem R33509 : Reach 33509 := rs (se 4 (by rfl) ⟨3141, by rfl⟩) (B 6283 (by norm_num) ⟨3141, by rfl⟩ (by norm_num))
theorem R33533 : Reach 33533 := rs (se 3 (by rfl) ⟨6287, by rfl⟩) (B 12575 (by norm_num) ⟨6287, by rfl⟩ (by norm_num))
theorem R33557 : Reach 33557 := rs (se 6 (by rfl) ⟨786, by rfl⟩) (B 1573 (by norm_num) ⟨786, by rfl⟩ (by norm_num))
theorem R33581 : Reach 33581 := rs (se 3 (by rfl) ⟨6296, by rfl⟩) (B 12593 (by norm_num) ⟨6296, by rfl⟩ (by norm_num))
theorem R33605 : Reach 33605 := rs (se 4 (by rfl) ⟨3150, by rfl⟩) (B 6301 (by norm_num) ⟨3150, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R33629 : Reach 33629 := rs (se 3 (by rfl) ⟨6305, by rfl⟩) (B 12611 (by norm_num) ⟨6305, by rfl⟩ (by norm_num))
theorem R33653 : Reach 33653 := rs (se 5 (by rfl) ⟨1577, by rfl⟩) (B 3155 (by norm_num) ⟨1577, by rfl⟩ (by norm_num))
theorem R33677 : Reach 33677 := rs (se 3 (by rfl) ⟨6314, by rfl⟩) (B 12629 (by norm_num) ⟨6314, by rfl⟩ (by norm_num))
theorem R33701 : Reach 33701 := rs (se 4 (by rfl) ⟨3159, by rfl⟩) (B 6319 (by norm_num) ⟨3159, by rfl⟩ (by norm_num))
theorem R33725 : Reach 33725 := rs (se 3 (by rfl) ⟨6323, by rfl⟩) (B 12647 (by norm_num) ⟨6323, by rfl⟩ (by norm_num))
theorem R33749 : Reach 33749 := rs (se 7 (by rfl) ⟨395, by rfl⟩) (B 791 (by norm_num) ⟨395, by rfl⟩ (by norm_num))
theorem R33773 : Reach 33773 := rs (se 3 (by rfl) ⟨6332, by rfl⟩) (B 12665 (by norm_num) ⟨6332, by rfl⟩ (by norm_num))
theorem R33797 : Reach 33797 := rs (se 4 (by rfl) ⟨3168, by rfl⟩) (B 6337 (by norm_num) ⟨3168, by rfl⟩ (by norm_num))
theorem R33805 : Reach 33805 := rs (se 3 (by rfl) ⟨6338, by rfl⟩) (B 12677 (by norm_num) ⟨6338, by rfl⟩ (by norm_num))
theorem R33821 : Reach 33821 := rs (se 3 (by rfl) ⟨6341, by rfl⟩) (B 12683 (by norm_num) ⟨6341, by rfl⟩ (by norm_num))
theorem R33845 : Reach 33845 := rs (se 5 (by rfl) ⟨1586, by rfl⟩) (B 3173 (by norm_num) ⟨1586, by rfl⟩ (by norm_num))
theorem R33869 : Reach 33869 := rs (se 3 (by rfl) ⟨6350, by rfl⟩) (B 12701 (by norm_num) ⟨6350, by rfl⟩ (by norm_num))
theorem R33893 : Reach 33893 := rs (se 4 (by rfl) ⟨3177, by rfl⟩) (B 6355 (by norm_num) ⟨3177, by rfl⟩ (by norm_num))
theorem R33917 : Reach 33917 := rs (se 3 (by rfl) ⟨6359, by rfl⟩) (B 12719 (by norm_num) ⟨6359, by rfl⟩ (by norm_num))
theorem R33925 : Reach 33925 := rs (se 4 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R33941 : Reach 33941 := rs (se 6 (by rfl) ⟨795, by rfl⟩) (B 1591 (by norm_num) ⟨795, by rfl⟩ (by norm_num))
theorem R33965 : Reach 33965 := rs (se 3 (by rfl) ⟨6368, by rfl⟩) (B 12737 (by norm_num) ⟨6368, by rfl⟩ (by norm_num))
theorem R33989 : Reach 33989 := rs (se 4 (by rfl) ⟨3186, by rfl⟩) (B 6373 (by norm_num) ⟨3186, by rfl⟩ (by norm_num))
theorem R34013 : Reach 34013 := rs (se 3 (by rfl) ⟨6377, by rfl⟩) (B 12755 (by norm_num) ⟨6377, by rfl⟩ (by norm_num))
theorem R34037 : Reach 34037 := rs (se 5 (by rfl) ⟨1595, by rfl⟩) (B 3191 (by norm_num) ⟨1595, by rfl⟩ (by norm_num))
theorem R99589 : Reach 99589 := rs (se 4 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R34061 : Reach 34061 := rs (se 3 (by rfl) ⟨6386, by rfl⟩) (B 12773 (by norm_num) ⟨6386, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R34085 : Reach 34085 := rs (se 4 (by rfl) ⟨3195, by rfl⟩) (B 6391 (by norm_num) ⟨3195, by rfl⟩ (by norm_num))
theorem R34109 : Reach 34109 := rs (se 3 (by rfl) ⟨6395, by rfl⟩) (B 12791 (by norm_num) ⟨6395, by rfl⟩ (by norm_num))
theorem R34133 : Reach 34133 := rs (se 12 (by rfl) ⟨12, by rfl⟩) (B 25 (by norm_num) ⟨12, by rfl⟩ (by norm_num))
theorem R34141 : Reach 34141 := rs (se 3 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R34157 : Reach 34157 := rs (se 3 (by rfl) ⟨6404, by rfl⟩) (B 12809 (by norm_num) ⟨6404, by rfl⟩ (by norm_num))
theorem R34181 : Reach 34181 := rs (se 4 (by rfl) ⟨3204, by rfl⟩) (B 6409 (by norm_num) ⟨3204, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R34205 : Reach 34205 := rs (se 3 (by rfl) ⟨6413, by rfl⟩) (B 12827 (by norm_num) ⟨6413, by rfl⟩ (by norm_num))
theorem R34229 : Reach 34229 := rs (se 5 (by rfl) ⟨1604, by rfl⟩) (B 3209 (by norm_num) ⟨1604, by rfl⟩ (by norm_num))
theorem R34253 : Reach 34253 := rs (se 3 (by rfl) ⟨6422, by rfl⟩) (B 12845 (by norm_num) ⟨6422, by rfl⟩ (by norm_num))
theorem R34277 : Reach 34277 := rs (se 4 (by rfl) ⟨3213, by rfl⟩) (B 6427 (by norm_num) ⟨3213, by rfl⟩ (by norm_num))
theorem R34301 : Reach 34301 := rs (se 3 (by rfl) ⟨6431, by rfl⟩) (B 12863 (by norm_num) ⟨6431, by rfl⟩ (by norm_num))
theorem R34325 : Reach 34325 := rs (se 6 (by rfl) ⟨804, by rfl⟩) (B 1609 (by norm_num) ⟨804, by rfl⟩ (by norm_num))
theorem R34349 : Reach 34349 := rs (se 3 (by rfl) ⟨6440, by rfl⟩) (B 12881 (by norm_num) ⟨6440, by rfl⟩ (by norm_num))
theorem R34357 : Reach 34357 := rs (se 5 (by rfl) ⟨1610, by rfl⟩) (B 3221 (by norm_num) ⟨1610, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R34373 : Reach 34373 := rs (se 4 (by rfl) ⟨3222, by rfl⟩) (B 6445 (by norm_num) ⟨3222, by rfl⟩ (by norm_num))
theorem R34397 : Reach 34397 := rs (se 3 (by rfl) ⟨6449, by rfl⟩) (B 12899 (by norm_num) ⟨6449, by rfl⟩ (by norm_num))
theorem R34421 : Reach 34421 := rs (se 5 (by rfl) ⟨1613, by rfl⟩) (B 3227 (by norm_num) ⟨1613, by rfl⟩ (by norm_num))
theorem R34445 : Reach 34445 := rs (se 3 (by rfl) ⟨6458, by rfl⟩) (B 12917 (by norm_num) ⟨6458, by rfl⟩ (by norm_num))
theorem R34469 : Reach 34469 := rs (se 4 (by rfl) ⟨3231, by rfl⟩) (B 6463 (by norm_num) ⟨3231, by rfl⟩ (by norm_num))
theorem R34493 : Reach 34493 := rs (se 3 (by rfl) ⟨6467, by rfl⟩) (B 12935 (by norm_num) ⟨6467, by rfl⟩ (by norm_num))
theorem R34517 : Reach 34517 := rs (se 7 (by rfl) ⟨404, by rfl⟩) (B 809 (by norm_num) ⟨404, by rfl⟩ (by norm_num))
theorem R34541 : Reach 34541 := rs (se 3 (by rfl) ⟨6476, by rfl⟩) (B 12953 (by norm_num) ⟨6476, by rfl⟩ (by norm_num))
theorem R34565 : Reach 34565 := rs (se 4 (by rfl) ⟨3240, by rfl⟩) (B 6481 (by norm_num) ⟨3240, by rfl⟩ (by norm_num))
theorem R34573 : Reach 34573 := rs (se 3 (by rfl) ⟨6482, by rfl⟩) (B 12965 (by norm_num) ⟨6482, by rfl⟩ (by norm_num))
theorem R34589 : Reach 34589 := rs (se 3 (by rfl) ⟨6485, by rfl⟩) (B 12971 (by norm_num) ⟨6485, by rfl⟩ (by norm_num))
theorem R100133 : Reach 100133 := rs (se 4 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R34613 : Reach 34613 := rs (se 5 (by rfl) ⟨1622, by rfl⟩) (B 3245 (by norm_num) ⟨1622, by rfl⟩ (by norm_num))
theorem R34637 : Reach 34637 := rs (se 3 (by rfl) ⟨6494, by rfl⟩) (B 12989 (by norm_num) ⟨6494, by rfl⟩ (by norm_num))
theorem R34661 : Reach 34661 := rs (se 4 (by rfl) ⟨3249, by rfl⟩) (B 6499 (by norm_num) ⟨3249, by rfl⟩ (by norm_num))
theorem R34685 : Reach 34685 := rs (se 3 (by rfl) ⟨6503, by rfl⟩) (B 13007 (by norm_num) ⟨6503, by rfl⟩ (by norm_num))
theorem R34709 : Reach 34709 := rs (se 6 (by rfl) ⟨813, by rfl⟩) (B 1627 (by norm_num) ⟨813, by rfl⟩ (by norm_num))
theorem R34733 : Reach 34733 := rs (se 3 (by rfl) ⟨6512, by rfl⟩) (B 13025 (by norm_num) ⟨6512, by rfl⟩ (by norm_num))
theorem R34757 : Reach 34757 := rs (se 4 (by rfl) ⟨3258, by rfl⟩) (B 6517 (by norm_num) ⟨3258, by rfl⟩ (by norm_num))
theorem R165845 : Reach 165845 := rs (se 7 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R34781 : Reach 34781 := rs (se 3 (by rfl) ⟨6521, by rfl⟩) (B 13043 (by norm_num) ⟨6521, by rfl⟩ (by norm_num))
theorem R34789 : Reach 34789 := rs (se 4 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R34805 : Reach 34805 := rs (se 5 (by rfl) ⟨1631, by rfl⟩) (B 3263 (by norm_num) ⟨1631, by rfl⟩ (by norm_num))
theorem R34829 : Reach 34829 := rs (se 3 (by rfl) ⟨6530, by rfl⟩) (B 13061 (by norm_num) ⟨6530, by rfl⟩ (by norm_num))
theorem R34853 : Reach 34853 := rs (se 4 (by rfl) ⟨3267, by rfl⟩) (B 6535 (by norm_num) ⟨3267, by rfl⟩ (by norm_num))
theorem R34877 : Reach 34877 := rs (se 3 (by rfl) ⟨6539, by rfl⟩) (B 13079 (by norm_num) ⟨6539, by rfl⟩ (by norm_num))
theorem R34901 : Reach 34901 := rs (se 8 (by rfl) ⟨204, by rfl⟩) (B 409 (by norm_num) ⟨204, by rfl⟩ (by norm_num))
theorem R34925 : Reach 34925 := rs (se 3 (by rfl) ⟨6548, by rfl⟩) (B 13097 (by norm_num) ⟨6548, by rfl⟩ (by norm_num))
theorem R34933 : Reach 34933 := rs (se 5 (by rfl) ⟨1637, by rfl⟩) (B 3275 (by norm_num) ⟨1637, by rfl⟩ (by norm_num))
theorem R34949 : Reach 34949 := rs (se 4 (by rfl) ⟨3276, by rfl⟩) (B 6553 (by norm_num) ⟨3276, by rfl⟩ (by norm_num))
theorem R34973 : Reach 34973 := rs (se 3 (by rfl) ⟨6557, by rfl⟩) (B 13115 (by norm_num) ⟨6557, by rfl⟩ (by norm_num))
theorem R34997 : Reach 34997 := rs (se 5 (by rfl) ⟨1640, by rfl⟩) (B 3281 (by norm_num) ⟨1640, by rfl⟩ (by norm_num))
theorem R35005 : Reach 35005 := rs (se 3 (by rfl) ⟨6563, by rfl⟩) (B 13127 (by norm_num) ⟨6563, by rfl⟩ (by norm_num))
theorem R35021 : Reach 35021 := rs (se 3 (by rfl) ⟨6566, by rfl⟩) (B 13133 (by norm_num) ⟨6566, by rfl⟩ (by norm_num))
theorem R35045 : Reach 35045 := rs (se 4 (by rfl) ⟨3285, by rfl⟩) (B 6571 (by norm_num) ⟨3285, by rfl⟩ (by norm_num))
theorem R35069 : Reach 35069 := rs (se 3 (by rfl) ⟨6575, by rfl⟩) (B 13151 (by norm_num) ⟨6575, by rfl⟩ (by norm_num))
theorem R35093 : Reach 35093 := rs (se 6 (by rfl) ⟨822, by rfl⟩) (B 1645 (by norm_num) ⟨822, by rfl⟩ (by norm_num))
theorem R67877 : Reach 67877 := rs (se 4 (by rfl) ⟨6363, by rfl⟩) (B 12727 (by norm_num) ⟨6363, by rfl⟩ (by norm_num))
theorem R35117 : Reach 35117 := rs (se 3 (by rfl) ⟨6584, by rfl⟩) (B 13169 (by norm_num) ⟨6584, by rfl⟩ (by norm_num))
theorem R35141 : Reach 35141 := rs (se 4 (by rfl) ⟨3294, by rfl⟩) (B 6589 (by norm_num) ⟨3294, by rfl⟩ (by norm_num))
theorem R35165 : Reach 35165 := rs (se 3 (by rfl) ⟨6593, by rfl⟩) (B 13187 (by norm_num) ⟨6593, by rfl⟩ (by norm_num))
theorem R35189 : Reach 35189 := rs (se 5 (by rfl) ⟨1649, by rfl⟩) (B 3299 (by norm_num) ⟨1649, by rfl⟩ (by norm_num))
theorem R35213 : Reach 35213 := rs (se 3 (by rfl) ⟨6602, by rfl⟩) (B 13205 (by norm_num) ⟨6602, by rfl⟩ (by norm_num))
theorem R35221 : Reach 35221 := rs (se 6 (by rfl) ⟨825, by rfl⟩) (B 1651 (by norm_num) ⟨825, by rfl⟩ (by norm_num))
theorem R35237 : Reach 35237 := rs (se 4 (by rfl) ⟨3303, by rfl⟩) (B 6607 (by norm_num) ⟨3303, by rfl⟩ (by norm_num))
theorem R133589 : Reach 133589 := rs (se 7 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R35309 : Reach 35309 := rs (se 3 (by rfl) ⟨6620, by rfl⟩) (B 13241 (by norm_num) ⟨6620, by rfl⟩ (by norm_num))
theorem R35317 : Reach 35317 := rs (se 5 (by rfl) ⟨1655, by rfl⟩) (B 3311 (by norm_num) ⟨1655, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R35437 : Reach 35437 := rs (se 3 (by rfl) ⟨6644, by rfl⟩) (B 13289 (by norm_num) ⟨6644, by rfl⟩ (by norm_num))
theorem R35525 : Reach 35525 := rs (se 4 (by rfl) ⟨3330, by rfl⟩) (B 6661 (by norm_num) ⟨3330, by rfl⟩ (by norm_num))
theorem R68309 : Reach 68309 := rs (se 7 (by rfl) ⟨800, by rfl⟩) (B 1601 (by norm_num) ⟨800, by rfl⟩ (by norm_num))
theorem R35573 : Reach 35573 := rs (se 5 (by rfl) ⟨1667, by rfl⟩) (B 3335 (by norm_num) ⟨1667, by rfl⟩ (by norm_num))
theorem R35653 : Reach 35653 := rs (se 4 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R35741 : Reach 35741 := rs (se 3 (by rfl) ⟨6701, by rfl⟩) (B 13403 (by norm_num) ⟨6701, by rfl⟩ (by norm_num))
theorem R35869 : Reach 35869 := rs (se 3 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R35957 : Reach 35957 := rs (se 5 (by rfl) ⟨1685, by rfl⟩) (B 3371 (by norm_num) ⟨1685, by rfl⟩ (by norm_num))
theorem R68741 : Reach 68741 := rs (se 4 (by rfl) ⟨6444, by rfl⟩) (B 12889 (by norm_num) ⟨6444, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R101573 : Reach 101573 := rs (se 4 (by rfl) ⟨9522, by rfl⟩) (B 19045 (by norm_num) ⟨9522, by rfl⟩ (by norm_num))
theorem R36085 : Reach 36085 := rs (se 5 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R36173 : Reach 36173 := rs (se 3 (by rfl) ⟨6782, by rfl⟩) (B 13565 (by norm_num) ⟨6782, by rfl⟩ (by norm_num))
theorem R36301 : Reach 36301 := rs (se 3 (by rfl) ⟨6806, by rfl⟩) (B 13613 (by norm_num) ⟨6806, by rfl⟩ (by norm_num))
theorem R36389 : Reach 36389 := rs (se 4 (by rfl) ⟨3411, by rfl⟩) (B 6823 (by norm_num) ⟨3411, by rfl⟩ (by norm_num))
theorem R69173 : Reach 69173 := rs (se 5 (by rfl) ⟨3242, by rfl⟩) (B 6485 (by norm_num) ⟨3242, by rfl⟩ (by norm_num))
theorem R36445 : Reach 36445 := rs (se 3 (by rfl) ⟨6833, by rfl⟩) (B 13667 (by norm_num) ⟨6833, by rfl⟩ (by norm_num))
theorem R36517 : Reach 36517 := rs (se 4 (by rfl) ⟨3423, by rfl⟩) (B 6847 (by norm_num) ⟨3423, by rfl⟩ (by norm_num))
theorem R36541 : Reach 36541 := rs (se 3 (by rfl) ⟨6851, by rfl⟩) (B 13703 (by norm_num) ⟨6851, by rfl⟩ (by norm_num))
theorem R167669 : Reach 167669 := rs (se 5 (by rfl) ⟨7859, by rfl⟩) (B 15719 (by norm_num) ⟨7859, by rfl⟩ (by norm_num))
theorem R36605 : Reach 36605 := rs (se 3 (by rfl) ⟨6863, by rfl⟩) (B 13727 (by norm_num) ⟨6863, by rfl⟩ (by norm_num))
theorem R36701 : Reach 36701 := rs (se 3 (by rfl) ⟨6881, by rfl⟩) (B 13763 (by norm_num) ⟨6881, by rfl⟩ (by norm_num))
theorem R36733 : Reach 36733 := rs (se 3 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R36749 : Reach 36749 := rs (se 3 (by rfl) ⟨6890, by rfl⟩) (B 13781 (by norm_num) ⟨6890, by rfl⟩ (by norm_num))
theorem R36821 : Reach 36821 := rs (se 7 (by rfl) ⟨431, by rfl⟩) (B 863 (by norm_num) ⟨431, by rfl⟩ (by norm_num))
theorem R69605 : Reach 69605 := rs (se 4 (by rfl) ⟨6525, by rfl⟩) (B 13051 (by norm_num) ⟨6525, by rfl⟩ (by norm_num))
theorem R36949 : Reach 36949 := rs (se 8 (by rfl) ⟨216, by rfl⟩) (B 433 (by norm_num) ⟨216, by rfl⟩ (by norm_num))
theorem R37037 : Reach 37037 := rs (se 3 (by rfl) ⟨6944, by rfl⟩) (B 13889 (by norm_num) ⟨6944, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R37165 : Reach 37165 := rs (se 3 (by rfl) ⟨6968, by rfl⟩) (B 13937 (by norm_num) ⟨6968, by rfl⟩ (by norm_num))
theorem R37253 : Reach 37253 := rs (se 4 (by rfl) ⟨3492, by rfl⟩) (B 6985 (by norm_num) ⟨3492, by rfl⟩ (by norm_num))
theorem R70037 : Reach 70037 := rs (se 6 (by rfl) ⟨1641, by rfl⟩) (B 3283 (by norm_num) ⟨1641, by rfl⟩ (by norm_num))
theorem R102869 : Reach 102869 := rs (se 7 (by rfl) ⟨1205, by rfl⟩) (B 2411 (by norm_num) ⟨1205, by rfl⟩ (by norm_num))
theorem R37381 : Reach 37381 := rs (se 4 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R37469 : Reach 37469 := rs (se 3 (by rfl) ⟨7025, by rfl⟩) (B 14051 (by norm_num) ⟨7025, by rfl⟩ (by norm_num))
theorem R37597 : Reach 37597 := rs (se 3 (by rfl) ⟨7049, by rfl⟩) (B 14099 (by norm_num) ⟨7049, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R37685 : Reach 37685 := rs (se 5 (by rfl) ⟨1766, by rfl⟩) (B 3533 (by norm_num) ⟨1766, by rfl⟩ (by norm_num))
theorem R70469 : Reach 70469 := rs (se 4 (by rfl) ⟨6606, by rfl⟩) (B 13213 (by norm_num) ⟨6606, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R37813 : Reach 37813 := rs (se 5 (by rfl) ⟨1772, by rfl⟩) (B 3545 (by norm_num) ⟨1772, by rfl⟩ (by norm_num))
theorem R37901 : Reach 37901 := rs (se 3 (by rfl) ⟨7106, by rfl⟩) (B 14213 (by norm_num) ⟨7106, by rfl⟩ (by norm_num))
theorem R38029 : Reach 38029 := rs (se 3 (by rfl) ⟨7130, by rfl⟩) (B 14261 (by norm_num) ⟨7130, by rfl⟩ (by norm_num))
theorem R38045 : Reach 38045 := rs (se 3 (by rfl) ⟨7133, by rfl⟩) (B 14267 (by norm_num) ⟨7133, by rfl⟩ (by norm_num))
theorem R38117 : Reach 38117 := rs (se 4 (by rfl) ⟨3573, by rfl⟩) (B 7147 (by norm_num) ⟨3573, by rfl⟩ (by norm_num))
theorem R70901 : Reach 70901 := rs (se 5 (by rfl) ⟨3323, by rfl⟩) (B 6647 (by norm_num) ⟨3323, by rfl⟩ (by norm_num))
theorem R38245 : Reach 38245 := rs (se 4 (by rfl) ⟨3585, by rfl⟩) (B 7171 (by norm_num) ⟨3585, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R38333 : Reach 38333 := rs (se 3 (by rfl) ⟨7187, by rfl⟩) (B 14375 (by norm_num) ⟨7187, by rfl⟩ (by norm_num))
theorem R38341 : Reach 38341 := rs (se 4 (by rfl) ⟨3594, by rfl⟩) (B 7189 (by norm_num) ⟨3594, by rfl⟩ (by norm_num))
theorem R38461 : Reach 38461 := rs (se 3 (by rfl) ⟨7211, by rfl⟩) (B 14423 (by norm_num) ⟨7211, by rfl⟩ (by norm_num))
theorem R38485 : Reach 38485 := rs (se 8 (by rfl) ⟨225, by rfl⟩) (B 451 (by norm_num) ⟨225, by rfl⟩ (by norm_num))
theorem R38549 : Reach 38549 := rs (se 6 (by rfl) ⟨903, by rfl⟩) (B 1807 (by norm_num) ⟨903, by rfl⟩ (by norm_num))
theorem R71333 : Reach 71333 := rs (se 4 (by rfl) ⟨6687, by rfl⟩) (B 13375 (by norm_num) ⟨6687, by rfl⟩ (by norm_num))
theorem R104165 : Reach 104165 := rs (se 4 (by rfl) ⟨9765, by rfl⟩) (B 19531 (by norm_num) ⟨9765, by rfl⟩ (by norm_num))
theorem R38677 : Reach 38677 := rs (se 6 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R38765 : Reach 38765 := rs (se 3 (by rfl) ⟨7268, by rfl⟩) (B 14537 (by norm_num) ⟨7268, by rfl⟩ (by norm_num))
theorem R38789 : Reach 38789 := rs (se 4 (by rfl) ⟨3636, by rfl⟩) (B 7273 (by norm_num) ⟨3636, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R38893 : Reach 38893 := rs (se 3 (by rfl) ⟨7292, by rfl⟩) (B 14585 (by norm_num) ⟨7292, by rfl⟩ (by norm_num))
theorem R104453 : Reach 104453 := rs (se 4 (by rfl) ⟨9792, by rfl⟩) (B 19585 (by norm_num) ⟨9792, by rfl⟩ (by norm_num))
theorem R38981 : Reach 38981 := rs (se 4 (by rfl) ⟨3654, by rfl⟩) (B 7309 (by norm_num) ⟨3654, by rfl⟩ (by norm_num))
theorem R71765 : Reach 71765 := rs (se 8 (by rfl) ⟨420, by rfl⟩) (B 841 (by norm_num) ⟨420, by rfl⟩ (by norm_num))
theorem R39109 : Reach 39109 := rs (se 4 (by rfl) ⟨3666, by rfl⟩) (B 7333 (by norm_num) ⟨3666, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R39197 : Reach 39197 := rs (se 3 (by rfl) ⟨7349, by rfl⟩) (B 14699 (by norm_num) ⟨7349, by rfl⟩ (by norm_num))
theorem R39325 : Reach 39325 := rs (se 3 (by rfl) ⟨7373, by rfl⟩) (B 14747 (by norm_num) ⟨7373, by rfl⟩ (by norm_num))
theorem R39413 : Reach 39413 := rs (se 5 (by rfl) ⟨1847, by rfl⟩) (B 3695 (by norm_num) ⟨1847, by rfl⟩ (by norm_num))
theorem R72197 : Reach 72197 := rs (se 4 (by rfl) ⟨6768, by rfl⟩) (B 13537 (by norm_num) ⟨6768, by rfl⟩ (by norm_num))
theorem R39541 : Reach 39541 := rs (se 5 (by rfl) ⟨1853, by rfl⟩) (B 3707 (by norm_num) ⟨1853, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R39629 : Reach 39629 := rs (se 3 (by rfl) ⟨7430, by rfl⟩) (B 14861 (by norm_num) ⟨7430, by rfl⟩ (by norm_num))
theorem R39685 : Reach 39685 := rs (se 4 (by rfl) ⟨3720, by rfl⟩) (B 7441 (by norm_num) ⟨3720, by rfl⟩ (by norm_num))
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) (B 13609 (by norm_num) ⟨6804, by rfl⟩ (by norm_num))
theorem R39845 : Reach 39845 := rs (se 4 (by rfl) ⟨3735, by rfl⟩) (B 7471 (by norm_num) ⟨3735, by rfl⟩ (by norm_num))
theorem R72629 : Reach 72629 := rs (se 5 (by rfl) ⟨3404, by rfl⟩) (B 6809 (by norm_num) ⟨3404, by rfl⟩ (by norm_num))
theorem R105461 : Reach 105461 := rs (se 5 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R39989 : Reach 39989 := rs (se 5 (by rfl) ⟨1874, by rfl⟩) (B 3749 (by norm_num) ⟨1874, by rfl⟩ (by norm_num))
theorem R40277 : Reach 40277 := rs (se 11 (by rfl) ⟨29, by rfl⟩) (B 59 (by norm_num) ⟨29, by rfl⟩ (by norm_num))
theorem R73061 : Reach 73061 := rs (se 4 (by rfl) ⟨6849, by rfl⟩) (B 13699 (by norm_num) ⟨6849, by rfl⟩ (by norm_num))
theorem R40429 : Reach 40429 := rs (se 3 (by rfl) ⟨7580, by rfl⟩) (B 15161 (by norm_num) ⟨7580, by rfl⟩ (by norm_num))
theorem R73493 : Reach 73493 := rs (se 6 (by rfl) ⟨1722, by rfl⟩) (B 3445 (by norm_num) ⟨1722, by rfl⟩ (by norm_num))
theorem R40733 : Reach 40733 := rs (se 3 (by rfl) ⟨7637, by rfl⟩) (B 15275 (by norm_num) ⟨7637, by rfl⟩ (by norm_num))
theorem R41029 : Reach 41029 := rs (se 4 (by rfl) ⟨3846, by rfl⟩) (B 7693 (by norm_num) ⟨3846, by rfl⟩ (by norm_num))
theorem R237653 : Reach 237653 := rs (se 8 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R73925 : Reach 73925 := rs (se 4 (by rfl) ⟨6930, by rfl⟩) (B 13861 (by norm_num) ⟨6930, by rfl⟩ (by norm_num))
theorem R41485 : Reach 41485 := rs (se 3 (by rfl) ⟨7778, by rfl⟩) (B 15557 (by norm_num) ⟨7778, by rfl⟩ (by norm_num))
theorem R74357 : Reach 74357 := rs (se 5 (by rfl) ⟨3485, by rfl⟩) (B 6971 (by norm_num) ⟨3485, by rfl⟩ (by norm_num))
theorem R41629 : Reach 41629 := rs (se 3 (by rfl) ⟨7805, by rfl⟩) (B 15611 (by norm_num) ⟨7805, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R41789 : Reach 41789 := rs (se 3 (by rfl) ⟨7835, by rfl⟩) (B 15671 (by norm_num) ⟨7835, by rfl⟩ (by norm_num))
theorem R41861 : Reach 41861 := rs (se 4 (by rfl) ⟨3924, by rfl⟩) (B 7849 (by norm_num) ⟨3924, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R41933 : Reach 41933 := rs (se 3 (by rfl) ⟨7862, by rfl⟩) (B 15725 (by norm_num) ⟨7862, by rfl⟩ (by norm_num))
theorem R74789 : Reach 74789 := rs (se 4 (by rfl) ⟨7011, by rfl⟩) (B 14023 (by norm_num) ⟨7011, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) (B 15833 (by norm_num) ⟨7916, by rfl⟩ (by norm_num))
theorem R42277 : Reach 42277 := rs (se 4 (by rfl) ⟨3963, by rfl⟩) (B 7927 (by norm_num) ⟨3963, by rfl⟩ (by norm_num))
theorem R42373 : Reach 42373 := rs (se 4 (by rfl) ⟨3972, by rfl⟩) (B 7945 (by norm_num) ⟨3972, by rfl⟩ (by norm_num))
theorem R75221 : Reach 75221 := rs (se 7 (by rfl) ⟨881, by rfl⟩) (B 1763 (by norm_num) ⟨881, by rfl⟩ (by norm_num))
theorem R42461 : Reach 42461 := rs (se 3 (by rfl) ⟨7961, by rfl⟩) (B 15923 (by norm_num) ⟨7961, by rfl⟩ (by norm_num))
theorem R42493 : Reach 42493 := rs (se 3 (by rfl) ⟨7967, by rfl⟩) (B 15935 (by norm_num) ⟨7967, by rfl⟩ (by norm_num))
theorem R108053 : Reach 108053 := rs (se 6 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R42557 : Reach 42557 := rs (se 3 (by rfl) ⟨7979, by rfl⟩) (B 15959 (by norm_num) ⟨7979, by rfl⟩ (by norm_num))
theorem R42677 : Reach 42677 := rs (se 5 (by rfl) ⟨2000, by rfl⟩) (B 4001 (by norm_num) ⟨2000, by rfl⟩ (by norm_num))
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R42869 : Reach 42869 := rs (se 5 (by rfl) ⟨2009, by rfl⟩) (B 4019 (by norm_num) ⟨2009, by rfl⟩ (by norm_num))
theorem R75653 : Reach 75653 := rs (se 4 (by rfl) ⟨7092, by rfl⟩) (B 14185 (by norm_num) ⟨7092, by rfl⟩ (by norm_num))
theorem R76085 : Reach 76085 := rs (se 5 (by rfl) ⟨3566, by rfl⟩) (B 7133 (by norm_num) ⟨3566, by rfl⟩ (by norm_num))
theorem R43429 : Reach 43429 := rs (se 4 (by rfl) ⟨4071, by rfl⟩) (B 8143 (by norm_num) ⟨4071, by rfl⟩ (by norm_num))
theorem R43573 : Reach 43573 := rs (se 5 (by rfl) ⟨2042, by rfl⟩) (B 4085 (by norm_num) ⟨2042, by rfl⟩ (by norm_num))
theorem R43661 : Reach 43661 := rs (se 3 (by rfl) ⟨8186, by rfl⟩) (B 16373 (by norm_num) ⟨8186, by rfl⟩ (by norm_num))
theorem R43733 : Reach 43733 := rs (se 7 (by rfl) ⟨512, by rfl⟩) (B 1025 (by norm_num) ⟨512, by rfl⟩ (by norm_num))
theorem R76517 : Reach 76517 := rs (se 4 (by rfl) ⟨7173, by rfl⟩) (B 14347 (by norm_num) ⟨7173, by rfl⟩ (by norm_num))
theorem R109333 : Reach 109333 := rs (se 6 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R43877 : Reach 43877 := rs (se 4 (by rfl) ⟨4113, by rfl⟩) (B 8227 (by norm_num) ⟨4113, by rfl⟩ (by norm_num))
theorem R44101 : Reach 44101 := rs (se 4 (by rfl) ⟨4134, by rfl⟩) (B 8269 (by norm_num) ⟨4134, by rfl⟩ (by norm_num))
theorem R44165 : Reach 44165 := rs (se 4 (by rfl) ⟨4140, by rfl⟩) (B 8281 (by norm_num) ⟨4140, by rfl⟩ (by norm_num))
theorem R76949 : Reach 76949 := rs (se 6 (by rfl) ⟨1803, by rfl⟩) (B 3607 (by norm_num) ⟨1803, by rfl⟩ (by norm_num))
theorem R44317 : Reach 44317 := rs (se 3 (by rfl) ⟨8309, by rfl⟩) (B 16619 (by norm_num) ⟨8309, by rfl⟩ (by norm_num))
theorem R175445 : Reach 175445 := rs (se 11 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R77381 : Reach 77381 := rs (se 4 (by rfl) ⟨7254, by rfl⟩) (B 14509 (by norm_num) ⟨7254, by rfl⟩ (by norm_num))
theorem R44621 : Reach 44621 := rs (se 3 (by rfl) ⟨8366, by rfl⟩) (B 16733 (by norm_num) ⟨8366, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R77669 : Reach 77669 := rs (se 4 (by rfl) ⟨7281, by rfl⟩) (B 14563 (by norm_num) ⟨7281, by rfl⟩ (by norm_num))
theorem R176053 : Reach 176053 := rs (se 5 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R77813 : Reach 77813 := rs (se 5 (by rfl) ⟨3647, by rfl⟩) (B 7295 (by norm_num) ⟨3647, by rfl⟩ (by norm_num))
theorem R45053 : Reach 45053 := rs (se 3 (by rfl) ⟨8447, by rfl⟩) (B 16895 (by norm_num) ⟨8447, by rfl⟩ (by norm_num))
theorem R110645 : Reach 110645 := rs (se 5 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R45125 : Reach 45125 := rs (se 4 (by rfl) ⟨4230, by rfl⟩) (B 8461 (by norm_num) ⟨4230, by rfl⟩ (by norm_num))
theorem R45197 : Reach 45197 := rs (se 3 (by rfl) ⟨8474, by rfl⟩) (B 16949 (by norm_num) ⟨8474, by rfl⟩ (by norm_num))
theorem R45269 : Reach 45269 := rs (se 7 (by rfl) ⟨530, by rfl⟩) (B 1061 (by norm_num) ⟨530, by rfl⟩ (by norm_num))
theorem R45341 : Reach 45341 := rs (se 3 (by rfl) ⟨8501, by rfl⟩) (B 17003 (by norm_num) ⟨8501, by rfl⟩ (by norm_num))
theorem R45373 : Reach 45373 := rs (se 3 (by rfl) ⟨8507, by rfl⟩) (B 17015 (by norm_num) ⟨8507, by rfl⟩ (by norm_num))
theorem R45413 : Reach 45413 := rs (se 4 (by rfl) ⟨4257, by rfl⟩) (B 8515 (by norm_num) ⟨4257, by rfl⟩ (by norm_num))
theorem R78245 : Reach 78245 := rs (se 4 (by rfl) ⟨7335, by rfl⟩) (B 14671 (by norm_num) ⟨7335, by rfl⟩ (by norm_num))
theorem R45485 : Reach 45485 := rs (se 3 (by rfl) ⟨8528, by rfl⟩) (B 17057 (by norm_num) ⟨8528, by rfl⟩ (by norm_num))
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) (B 17069 (by norm_num) ⟨8534, by rfl⟩ (by norm_num))
theorem R45557 : Reach 45557 := rs (se 5 (by rfl) ⟨2135, by rfl⟩) (B 4271 (by norm_num) ⟨2135, by rfl⟩ (by norm_num))
theorem R45629 : Reach 45629 := rs (se 3 (by rfl) ⟨8555, by rfl⟩) (B 17111 (by norm_num) ⟨8555, by rfl⟩ (by norm_num))
theorem R45701 : Reach 45701 := rs (se 4 (by rfl) ⟨4284, by rfl⟩) (B 8569 (by norm_num) ⟨4284, by rfl⟩ (by norm_num))
theorem R45773 : Reach 45773 := rs (se 3 (by rfl) ⟨8582, by rfl⟩) (B 17165 (by norm_num) ⟨8582, by rfl⟩ (by norm_num))
theorem R45845 : Reach 45845 := rs (se 6 (by rfl) ⟨1074, by rfl⟩) (B 2149 (by norm_num) ⟨1074, by rfl⟩ (by norm_num))
theorem R45893 : Reach 45893 := rs (se 4 (by rfl) ⟨4302, by rfl⟩) (B 8605 (by norm_num) ⟨4302, by rfl⟩ (by norm_num))
theorem R78677 : Reach 78677 := rs (se 9 (by rfl) ⟨230, by rfl⟩) (B 461 (by norm_num) ⟨230, by rfl⟩ (by norm_num))
theorem R45917 : Reach 45917 := rs (se 3 (by rfl) ⟨8609, by rfl⟩) (B 17219 (by norm_num) ⟨8609, by rfl⟩ (by norm_num))
theorem R45989 : Reach 45989 := rs (se 4 (by rfl) ⟨4311, by rfl⟩) (B 8623 (by norm_num) ⟨4311, by rfl⟩ (by norm_num))
theorem R46061 : Reach 46061 := rs (se 3 (by rfl) ⟨8636, by rfl⟩) (B 17273 (by norm_num) ⟨8636, by rfl⟩ (by norm_num))
theorem R78853 : Reach 78853 := rs (se 4 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R46133 : Reach 46133 := rs (se 5 (by rfl) ⟨2162, by rfl⟩) (B 4325 (by norm_num) ⟨2162, by rfl⟩ (by norm_num))
theorem R46205 : Reach 46205 := rs (se 3 (by rfl) ⟨8663, by rfl⟩) (B 17327 (by norm_num) ⟨8663, by rfl⟩ (by norm_num))
theorem R46261 : Reach 46261 := rs (se 5 (by rfl) ⟨2168, by rfl⟩) (B 4337 (by norm_num) ⟨2168, by rfl⟩ (by norm_num))
theorem R46277 : Reach 46277 := rs (se 4 (by rfl) ⟨4338, by rfl⟩) (B 8677 (by norm_num) ⟨4338, by rfl⟩ (by norm_num))
theorem R79109 : Reach 79109 := rs (se 4 (by rfl) ⟨7416, by rfl⟩) (B 14833 (by norm_num) ⟨7416, by rfl⟩ (by norm_num))
theorem R46349 : Reach 46349 := rs (se 3 (by rfl) ⟨8690, by rfl⟩) (B 17381 (by norm_num) ⟨8690, by rfl⟩ (by norm_num))
theorem R79157 : Reach 79157 := rs (se 5 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R46421 : Reach 46421 := rs (se 13 (by rfl) ⟨8, by rfl⟩) (B 17 (by norm_num) ⟨8, by rfl⟩ (by norm_num))
theorem R46493 : Reach 46493 := rs (se 3 (by rfl) ⟨8717, by rfl⟩) (B 17435 (by norm_num) ⟨8717, by rfl⟩ (by norm_num))
theorem R46565 : Reach 46565 := rs (se 4 (by rfl) ⟨4365, by rfl⟩) (B 8731 (by norm_num) ⟨4365, by rfl⟩ (by norm_num))
theorem R46637 : Reach 46637 := rs (se 3 (by rfl) ⟨8744, by rfl⟩) (B 17489 (by norm_num) ⟨8744, by rfl⟩ (by norm_num))
theorem R46709 : Reach 46709 := rs (se 5 (by rfl) ⟨2189, by rfl⟩) (B 4379 (by norm_num) ⟨2189, by rfl⟩ (by norm_num))
theorem R46781 : Reach 46781 := rs (se 3 (by rfl) ⟨8771, by rfl⟩) (B 17543 (by norm_num) ⟨8771, by rfl⟩ (by norm_num))
theorem R46853 : Reach 46853 := rs (se 4 (by rfl) ⟨4392, by rfl⟩) (B 8785 (by norm_num) ⟨4392, by rfl⟩ (by norm_num))
theorem R46901 : Reach 46901 := rs (se 5 (by rfl) ⟨2198, by rfl⟩) (B 4397 (by norm_num) ⟨2198, by rfl⟩ (by norm_num))
theorem R46925 : Reach 46925 := rs (se 3 (by rfl) ⟨8798, by rfl⟩) (B 17597 (by norm_num) ⟨8798, by rfl⟩ (by norm_num))
theorem R178037 : Reach 178037 := rs (se 5 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R46997 : Reach 46997 := rs (se 6 (by rfl) ⟨1101, by rfl⟩) (B 2203 (by norm_num) ⟨1101, by rfl⟩ (by norm_num))
theorem R47069 : Reach 47069 := rs (se 3 (by rfl) ⟨8825, by rfl⟩) (B 17651 (by norm_num) ⟨8825, by rfl⟩ (by norm_num))
theorem R47141 : Reach 47141 := rs (se 4 (by rfl) ⟨4419, by rfl⟩) (B 8839 (by norm_num) ⟨4419, by rfl⟩ (by norm_num))
theorem R47213 : Reach 47213 := rs (se 3 (by rfl) ⟨8852, by rfl⟩) (B 17705 (by norm_num) ⟨8852, by rfl⟩ (by norm_num))
theorem R47285 : Reach 47285 := rs (se 5 (by rfl) ⟨2216, by rfl⟩) (B 4433 (by norm_num) ⟨2216, by rfl⟩ (by norm_num))
theorem R47357 : Reach 47357 := rs (se 3 (by rfl) ⟨8879, by rfl⟩) (B 17759 (by norm_num) ⟨8879, by rfl⟩ (by norm_num))
theorem R47429 : Reach 47429 := rs (se 4 (by rfl) ⟨4446, by rfl⟩) (B 8893 (by norm_num) ⟨4446, by rfl⟩ (by norm_num))
theorem R47501 : Reach 47501 := rs (se 3 (by rfl) ⟨8906, by rfl⟩) (B 17813 (by norm_num) ⟨8906, by rfl⟩ (by norm_num))
theorem R47573 : Reach 47573 := rs (se 7 (by rfl) ⟨557, by rfl⟩) (B 1115 (by norm_num) ⟨557, by rfl⟩ (by norm_num))
theorem R47645 : Reach 47645 := rs (se 3 (by rfl) ⟨8933, by rfl⟩) (B 17867 (by norm_num) ⟨8933, by rfl⟩ (by norm_num))
theorem R113237 : Reach 113237 := rs (se 8 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R47717 : Reach 47717 := rs (se 4 (by rfl) ⟨4473, by rfl⟩) (B 8947 (by norm_num) ⟨4473, by rfl⟩ (by norm_num))
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R47765 : Reach 47765 := rs (se 6 (by rfl) ⟨1119, by rfl⟩) (B 2239 (by norm_num) ⟨1119, by rfl⟩ (by norm_num))
theorem R47789 : Reach 47789 := rs (se 3 (by rfl) ⟨8960, by rfl⟩) (B 17921 (by norm_num) ⟨8960, by rfl⟩ (by norm_num))
theorem R47861 : Reach 47861 := rs (se 5 (by rfl) ⟨2243, by rfl⟩) (B 4487 (by norm_num) ⟨2243, by rfl⟩ (by norm_num))
theorem R47909 : Reach 47909 := rs (se 4 (by rfl) ⟨4491, by rfl⟩) (B 8983 (by norm_num) ⟨4491, by rfl⟩ (by norm_num))
theorem R47933 : Reach 47933 := rs (se 3 (by rfl) ⟨8987, by rfl⟩) (B 17975 (by norm_num) ⟨8987, by rfl⟩ (by norm_num))
theorem R48005 : Reach 48005 := rs (se 4 (by rfl) ⟨4500, by rfl⟩) (B 9001 (by norm_num) ⟨4500, by rfl⟩ (by norm_num))
theorem R48077 : Reach 48077 := rs (se 3 (by rfl) ⟨9014, by rfl⟩) (B 18029 (by norm_num) ⟨9014, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R48149 : Reach 48149 := rs (se 6 (by rfl) ⟨1128, by rfl⟩) (B 2257 (by norm_num) ⟨1128, by rfl⟩ (by norm_num))
theorem R48221 : Reach 48221 := rs (se 3 (by rfl) ⟨9041, by rfl⟩) (B 18083 (by norm_num) ⟨9041, by rfl⟩ (by norm_num))
theorem R48269 : Reach 48269 := rs (se 3 (by rfl) ⟨9050, by rfl⟩) (B 18101 (by norm_num) ⟨9050, by rfl⟩ (by norm_num))
theorem R48293 : Reach 48293 := rs (se 4 (by rfl) ⟨4527, by rfl⟩) (B 9055 (by norm_num) ⟨4527, by rfl⟩ (by norm_num))
theorem R48365 : Reach 48365 := rs (se 3 (by rfl) ⟨9068, by rfl⟩) (B 18137 (by norm_num) ⟨9068, by rfl⟩ (by norm_num))
theorem R48437 : Reach 48437 := rs (se 5 (by rfl) ⟨2270, by rfl⟩) (B 4541 (by norm_num) ⟨2270, by rfl⟩ (by norm_num))
theorem R81269 : Reach 81269 := rs (se 5 (by rfl) ⟨3809, by rfl⟩) (B 7619 (by norm_num) ⟨3809, by rfl⟩ (by norm_num))
theorem R48509 : Reach 48509 := rs (se 3 (by rfl) ⟨9095, by rfl⟩) (B 18191 (by norm_num) ⟨9095, by rfl⟩ (by norm_num))
theorem R48581 : Reach 48581 := rs (se 4 (by rfl) ⟨4554, by rfl⟩) (B 9109 (by norm_num) ⟨4554, by rfl⟩ (by norm_num))
theorem R146933 : Reach 146933 := rs (se 5 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R48653 : Reach 48653 := rs (se 3 (by rfl) ⟨9122, by rfl⟩) (B 18245 (by norm_num) ⟨9122, by rfl⟩ (by norm_num))
theorem R48725 : Reach 48725 := rs (se 8 (by rfl) ⟨285, by rfl⟩) (B 571 (by norm_num) ⟨285, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R48797 : Reach 48797 := rs (se 3 (by rfl) ⟨9149, by rfl⟩) (B 18299 (by norm_num) ⟨9149, by rfl⟩ (by norm_num))
theorem R48869 : Reach 48869 := rs (se 4 (by rfl) ⟨4581, by rfl⟩) (B 9163 (by norm_num) ⟨4581, by rfl⟩ (by norm_num))
theorem R48941 : Reach 48941 := rs (se 3 (by rfl) ⟨9176, by rfl⟩) (B 18353 (by norm_num) ⟨9176, by rfl⟩ (by norm_num))
theorem R49013 : Reach 49013 := rs (se 5 (by rfl) ⟨2297, by rfl⟩) (B 4595 (by norm_num) ⟨2297, by rfl⟩ (by norm_num))
theorem R49085 : Reach 49085 := rs (se 3 (by rfl) ⟨9203, by rfl⟩) (B 18407 (by norm_num) ⟨9203, by rfl⟩ (by norm_num))
theorem R49157 : Reach 49157 := rs (se 4 (by rfl) ⟨4608, by rfl⟩) (B 9217 (by norm_num) ⟨4608, by rfl⟩ (by norm_num))
theorem R49229 : Reach 49229 := rs (se 3 (by rfl) ⟨9230, by rfl⟩) (B 18461 (by norm_num) ⟨9230, by rfl⟩ (by norm_num))
theorem R49285 : Reach 49285 := rs (se 4 (by rfl) ⟨4620, by rfl⟩) (B 9241 (by norm_num) ⟨4620, by rfl⟩ (by norm_num))
theorem R49301 : Reach 49301 := rs (se 6 (by rfl) ⟨1155, by rfl⟩) (B 2311 (by norm_num) ⟨1155, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R49373 : Reach 49373 := rs (se 3 (by rfl) ⟨9257, by rfl⟩) (B 18515 (by norm_num) ⟨9257, by rfl⟩ (by norm_num))
theorem R49405 : Reach 49405 := rs (se 3 (by rfl) ⟨9263, by rfl⟩) (B 18527 (by norm_num) ⟨9263, by rfl⟩ (by norm_num))
theorem R49445 : Reach 49445 := rs (se 4 (by rfl) ⟨4635, by rfl⟩) (B 9271 (by norm_num) ⟨4635, by rfl⟩ (by norm_num))
theorem R49517 : Reach 49517 := rs (se 3 (by rfl) ⟨9284, by rfl⟩) (B 18569 (by norm_num) ⟨9284, by rfl⟩ (by norm_num))
theorem R49589 : Reach 49589 := rs (se 5 (by rfl) ⟨2324, by rfl⟩) (B 4649 (by norm_num) ⟨2324, by rfl⟩ (by norm_num))
theorem R49661 : Reach 49661 := rs (se 3 (by rfl) ⟨9311, by rfl⟩) (B 18623 (by norm_num) ⟨9311, by rfl⟩ (by norm_num))
theorem R49709 : Reach 49709 := rs (se 3 (by rfl) ⟨9320, by rfl⟩) (B 18641 (by norm_num) ⟨9320, by rfl⟩ (by norm_num))
theorem R49733 : Reach 49733 := rs (se 4 (by rfl) ⟨4662, by rfl⟩) (B 9325 (by norm_num) ⟨4662, by rfl⟩ (by norm_num))
theorem R49805 : Reach 49805 := rs (se 3 (by rfl) ⟨9338, by rfl⟩) (B 18677 (by norm_num) ⟨9338, by rfl⟩ (by norm_num))
theorem R49877 : Reach 49877 := rs (se 7 (by rfl) ⟨584, by rfl⟩) (B 1169 (by norm_num) ⟨584, by rfl⟩ (by norm_num))
theorem R49909 : Reach 49909 := rs (se 5 (by rfl) ⟨2339, by rfl⟩) (B 4679 (by norm_num) ⟨2339, by rfl⟩ (by norm_num))
theorem R49949 : Reach 49949 := rs (se 3 (by rfl) ⟨9365, by rfl⟩) (B 18731 (by norm_num) ⟨9365, by rfl⟩ (by norm_num))
theorem R82741 : Reach 82741 := rs (se 5 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R49997 : Reach 49997 := rs (se 3 (by rfl) ⟨9374, by rfl⟩) (B 18749 (by norm_num) ⟨9374, by rfl⟩ (by norm_num))
theorem R50021 : Reach 50021 := rs (se 4 (by rfl) ⟨4689, by rfl⟩) (B 9379 (by norm_num) ⟨4689, by rfl⟩ (by norm_num))
theorem R50093 : Reach 50093 := rs (se 3 (by rfl) ⟨9392, by rfl⟩) (B 18785 (by norm_num) ⟨9392, by rfl⟩ (by norm_num))
theorem R50165 : Reach 50165 := rs (se 5 (by rfl) ⟨2351, by rfl⟩) (B 4703 (by norm_num) ⟨2351, by rfl⟩ (by norm_num))
theorem R82981 : Reach 82981 := rs (se 4 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R50237 : Reach 50237 := rs (se 3 (by rfl) ⟨9419, by rfl⟩) (B 18839 (by norm_num) ⟨9419, by rfl⟩ (by norm_num))
theorem R83045 : Reach 83045 := rs (se 4 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R115829 : Reach 115829 := rs (se 5 (by rfl) ⟨5429, by rfl⟩) (B 10859 (by norm_num) ⟨5429, by rfl⟩ (by norm_num))
theorem R50309 : Reach 50309 := rs (se 4 (by rfl) ⟨4716, by rfl⟩) (B 9433 (by norm_num) ⟨4716, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R50381 : Reach 50381 := rs (se 3 (by rfl) ⟨9446, by rfl⟩) (B 18893 (by norm_num) ⟨9446, by rfl⟩ (by norm_num))
theorem R50453 : Reach 50453 := rs (se 6 (by rfl) ⟨1182, by rfl⟩) (B 2365 (by norm_num) ⟨1182, by rfl⟩ (by norm_num))
theorem R50525 : Reach 50525 := rs (se 3 (by rfl) ⟨9473, by rfl⟩) (B 18947 (by norm_num) ⟨9473, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R50597 : Reach 50597 := rs (se 4 (by rfl) ⟨4743, by rfl⟩) (B 9487 (by norm_num) ⟨4743, by rfl⟩ (by norm_num))
theorem R50645 : Reach 50645 := rs (se 7 (by rfl) ⟨593, by rfl⟩) (B 1187 (by norm_num) ⟨593, by rfl⟩ (by norm_num))
theorem R50669 : Reach 50669 := rs (se 3 (by rfl) ⟨9500, by rfl⟩) (B 19001 (by norm_num) ⟨9500, by rfl⟩ (by norm_num))
theorem R50741 : Reach 50741 := rs (se 5 (by rfl) ⟨2378, by rfl⟩) (B 4757 (by norm_num) ⟨2378, by rfl⟩ (by norm_num))
theorem R50813 : Reach 50813 := rs (se 3 (by rfl) ⟨9527, by rfl⟩) (B 19055 (by norm_num) ⟨9527, by rfl⟩ (by norm_num))
theorem R50885 : Reach 50885 := rs (se 4 (by rfl) ⟨4770, by rfl⟩) (B 9541 (by norm_num) ⟨4770, by rfl⟩ (by norm_num))
theorem R50957 : Reach 50957 := rs (se 3 (by rfl) ⟨9554, by rfl⟩) (B 19109 (by norm_num) ⟨9554, by rfl⟩ (by norm_num))
theorem R50989 : Reach 50989 := rs (se 3 (by rfl) ⟨9560, by rfl⟩) (B 19121 (by norm_num) ⟨9560, by rfl⟩ (by norm_num))
theorem R51029 : Reach 51029 := rs (se 9 (by rfl) ⟨149, by rfl⟩) (B 299 (by norm_num) ⟨149, by rfl⟩ (by norm_num))
theorem R51101 : Reach 51101 := rs (se 3 (by rfl) ⟨9581, by rfl⟩) (B 19163 (by norm_num) ⟨9581, by rfl⟩ (by norm_num))
theorem R51173 : Reach 51173 := rs (se 4 (by rfl) ⟨4797, by rfl⟩) (B 9595 (by norm_num) ⟨4797, by rfl⟩ (by norm_num))
theorem R51245 : Reach 51245 := rs (se 3 (by rfl) ⟨9608, by rfl⟩) (B 19217 (by norm_num) ⟨9608, by rfl⟩ (by norm_num))
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) (B 19235 (by norm_num) ⟨9617, by rfl⟩ (by norm_num))
theorem R51317 : Reach 51317 := rs (se 5 (by rfl) ⟨2405, by rfl⟩) (B 4811 (by norm_num) ⟨2405, by rfl⟩ (by norm_num))
theorem R51389 : Reach 51389 := rs (se 3 (by rfl) ⟨9635, by rfl⟩) (B 19271 (by norm_num) ⟨9635, by rfl⟩ (by norm_num))
theorem R51461 : Reach 51461 := rs (se 4 (by rfl) ⟨4824, by rfl⟩) (B 9649 (by norm_num) ⟨4824, by rfl⟩ (by norm_num))
theorem R51533 : Reach 51533 := rs (se 3 (by rfl) ⟨9662, by rfl⟩) (B 19325 (by norm_num) ⟨9662, by rfl⟩ (by norm_num))
theorem R51605 : Reach 51605 := rs (se 6 (by rfl) ⟨1209, by rfl⟩) (B 2419 (by norm_num) ⟨1209, by rfl⟩ (by norm_num))
theorem R51637 : Reach 51637 := rs (se 5 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R51677 : Reach 51677 := rs (se 3 (by rfl) ⟨9689, by rfl⟩) (B 19379 (by norm_num) ⟨9689, by rfl⟩ (by norm_num))
theorem R51749 : Reach 51749 := rs (se 4 (by rfl) ⟨4851, by rfl⟩) (B 9703 (by norm_num) ⟨4851, by rfl⟩ (by norm_num))
theorem R51821 : Reach 51821 := rs (se 3 (by rfl) ⟨9716, by rfl⟩) (B 19433 (by norm_num) ⟨9716, by rfl⟩ (by norm_num))
theorem R51893 : Reach 51893 := rs (se 5 (by rfl) ⟨2432, by rfl⟩) (B 4865 (by norm_num) ⟨2432, by rfl⟩ (by norm_num))
theorem R51941 : Reach 51941 := rs (se 4 (by rfl) ⟨4869, by rfl⟩) (B 9739 (by norm_num) ⟨4869, by rfl⟩ (by norm_num))
theorem R51965 : Reach 51965 := rs (se 3 (by rfl) ⟨9743, by rfl⟩) (B 19487 (by norm_num) ⟨9743, by rfl⟩ (by norm_num))
theorem R52037 : Reach 52037 := rs (se 4 (by rfl) ⟨4878, by rfl⟩) (B 9757 (by norm_num) ⟨4878, by rfl⟩ (by norm_num))
theorem R52109 : Reach 52109 := rs (se 3 (by rfl) ⟨9770, by rfl⟩) (B 19541 (by norm_num) ⟨9770, by rfl⟩ (by norm_num))
theorem R52181 : Reach 52181 := rs (se 7 (by rfl) ⟨611, by rfl⟩) (B 1223 (by norm_num) ⟨611, by rfl⟩ (by norm_num))
theorem R52253 : Reach 52253 := rs (se 3 (by rfl) ⟨9797, by rfl⟩) (B 19595 (by norm_num) ⟨9797, by rfl⟩ (by norm_num))
theorem R52285 : Reach 52285 := rs (se 3 (by rfl) ⟨9803, by rfl⟩) (B 19607 (by norm_num) ⟨9803, by rfl⟩ (by norm_num))
theorem R52325 : Reach 52325 := rs (se 4 (by rfl) ⟨4905, by rfl⟩) (B 9811 (by norm_num) ⟨4905, by rfl⟩ (by norm_num))
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) (B 15967 (by norm_num) ⟨7983, by rfl⟩ (by norm_num))
theorem R52397 : Reach 52397 := rs (se 3 (by rfl) ⟨9824, by rfl⟩) (B 19649 (by norm_num) ⟨9824, by rfl⟩ (by norm_num))
theorem R52469 : Reach 52469 := rs (se 5 (by rfl) ⟨2459, by rfl⟩) (B 4919 (by norm_num) ⟨2459, by rfl⟩ (by norm_num))
theorem R52541 : Reach 52541 := rs (se 3 (by rfl) ⟨9851, by rfl⟩) (B 19703 (by norm_num) ⟨9851, by rfl⟩ (by norm_num))
theorem R52589 : Reach 52589 := rs (se 3 (by rfl) ⟨9860, by rfl⟩) (B 19721 (by norm_num) ⟨9860, by rfl⟩ (by norm_num))
theorem R52613 : Reach 52613 := rs (se 4 (by rfl) ⟨4932, by rfl⟩) (B 9865 (by norm_num) ⟨4932, by rfl⟩ (by norm_num))
theorem R85445 : Reach 85445 := rs (se 4 (by rfl) ⟨8010, by rfl⟩) (B 16021 (by norm_num) ⟨8010, by rfl⟩ (by norm_num))
theorem R52685 : Reach 52685 := rs (se 3 (by rfl) ⟨9878, by rfl⟩) (B 19757 (by norm_num) ⟨9878, by rfl⟩ (by norm_num))
theorem R52757 : Reach 52757 := rs (se 6 (by rfl) ⟨1236, by rfl⟩) (B 2473 (by norm_num) ⟨1236, by rfl⟩ (by norm_num))
theorem R20001 : Reach 20001 := rs (se 2 (by rfl) ⟨7500, by rfl⟩) (B 15001 (by norm_num) ⟨7500, by rfl⟩ (by norm_num))
theorem R20005 : Reach 20005 := rs (se 4 (by rfl) ⟨1875, by rfl⟩) (B 3751 (by norm_num) ⟨1875, by rfl⟩ (by norm_num))
theorem R20009 : Reach 20009 := rs (se 2 (by rfl) ⟨7503, by rfl⟩) (B 15007 (by norm_num) ⟨7503, by rfl⟩ (by norm_num))
theorem R20013 : Reach 20013 := rs (se 3 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R20017 : Reach 20017 := rs (se 2 (by rfl) ⟨7506, by rfl⟩) (B 15013 (by norm_num) ⟨7506, by rfl⟩ (by norm_num))
theorem R20021 : Reach 20021 := rs (se 5 (by rfl) ⟨938, by rfl⟩) (B 1877 (by norm_num) ⟨938, by rfl⟩ (by norm_num))
theorem R20025 : Reach 20025 := rs (se 2 (by rfl) ⟨7509, by rfl⟩) (B 15019 (by norm_num) ⟨7509, by rfl⟩ (by norm_num))
theorem R20029 : Reach 20029 := rs (se 3 (by rfl) ⟨3755, by rfl⟩) (B 7511 (by norm_num) ⟨3755, by rfl⟩ (by norm_num))
theorem R20033 : Reach 20033 := rs (se 2 (by rfl) ⟨7512, by rfl⟩) (B 15025 (by norm_num) ⟨7512, by rfl⟩ (by norm_num))
theorem R20037 : Reach 20037 := rs (se 4 (by rfl) ⟨1878, by rfl⟩) (B 3757 (by norm_num) ⟨1878, by rfl⟩ (by norm_num))
theorem R52805 : Reach 52805 := rs (se 4 (by rfl) ⟨4950, by rfl⟩) (B 9901 (by norm_num) ⟨4950, by rfl⟩ (by norm_num))
theorem R20041 : Reach 20041 := rs (se 2 (by rfl) ⟨7515, by rfl⟩) (B 15031 (by norm_num) ⟨7515, by rfl⟩ (by norm_num))
theorem R20045 : Reach 20045 := rs (se 3 (by rfl) ⟨3758, by rfl⟩) (B 7517 (by norm_num) ⟨3758, by rfl⟩ (by norm_num))
theorem R20049 : Reach 20049 := rs (se 2 (by rfl) ⟨7518, by rfl⟩) (B 15037 (by norm_num) ⟨7518, by rfl⟩ (by norm_num))
theorem R20053 : Reach 20053 := rs (se 8 (by rfl) ⟨117, by rfl⟩) (B 235 (by norm_num) ⟨117, by rfl⟩ (by norm_num))
theorem R20057 : Reach 20057 := rs (se 2 (by rfl) ⟨7521, by rfl⟩) (B 15043 (by norm_num) ⟨7521, by rfl⟩ (by norm_num))
theorem R20061 : Reach 20061 := rs (se 3 (by rfl) ⟨3761, by rfl⟩) (B 7523 (by norm_num) ⟨3761, by rfl⟩ (by norm_num))
theorem R52829 : Reach 52829 := rs (se 3 (by rfl) ⟨9905, by rfl⟩) (B 19811 (by norm_num) ⟨9905, by rfl⟩ (by norm_num))
theorem R20065 : Reach 20065 := rs (se 2 (by rfl) ⟨7524, by rfl⟩) (B 15049 (by norm_num) ⟨7524, by rfl⟩ (by norm_num))
theorem R20069 : Reach 20069 := rs (se 4 (by rfl) ⟨1881, by rfl⟩) (B 3763 (by norm_num) ⟨1881, by rfl⟩ (by norm_num))
theorem R20073 : Reach 20073 := rs (se 2 (by rfl) ⟨7527, by rfl⟩) (B 15055 (by norm_num) ⟨7527, by rfl⟩ (by norm_num))
theorem R20077 : Reach 20077 := rs (se 3 (by rfl) ⟨3764, by rfl⟩) (B 7529 (by norm_num) ⟨3764, by rfl⟩ (by norm_num))
theorem R20081 : Reach 20081 := rs (se 2 (by rfl) ⟨7530, by rfl⟩) (B 15061 (by norm_num) ⟨7530, by rfl⟩ (by norm_num))
theorem R20085 : Reach 20085 := rs (se 5 (by rfl) ⟨941, by rfl⟩) (B 1883 (by norm_num) ⟨941, by rfl⟩ (by norm_num))
theorem R20089 : Reach 20089 := rs (se 2 (by rfl) ⟨7533, by rfl⟩) (B 15067 (by norm_num) ⟨7533, by rfl⟩ (by norm_num))
theorem R20093 : Reach 20093 := rs (se 3 (by rfl) ⟨3767, by rfl⟩) (B 7535 (by norm_num) ⟨3767, by rfl⟩ (by norm_num))
theorem R20097 : Reach 20097 := rs (se 2 (by rfl) ⟨7536, by rfl⟩) (B 15073 (by norm_num) ⟨7536, by rfl⟩ (by norm_num))
theorem R20101 : Reach 20101 := rs (se 4 (by rfl) ⟨1884, by rfl⟩) (B 3769 (by norm_num) ⟨1884, by rfl⟩ (by norm_num))
theorem R20105 : Reach 20105 := rs (se 2 (by rfl) ⟨7539, by rfl⟩) (B 15079 (by norm_num) ⟨7539, by rfl⟩ (by norm_num))
theorem R20109 : Reach 20109 := rs (se 3 (by rfl) ⟨3770, by rfl⟩) (B 7541 (by norm_num) ⟨3770, by rfl⟩ (by norm_num))
theorem R20113 : Reach 20113 := rs (se 2 (by rfl) ⟨7542, by rfl⟩) (B 15085 (by norm_num) ⟨7542, by rfl⟩ (by norm_num))
theorem R20117 : Reach 20117 := rs (se 6 (by rfl) ⟨471, by rfl⟩) (B 943 (by norm_num) ⟨471, by rfl⟩ (by norm_num))
theorem R118421 : Reach 118421 := rs (se 6 (by rfl) ⟨2775, by rfl⟩) (B 5551 (by norm_num) ⟨2775, by rfl⟩ (by norm_num))
theorem R20121 : Reach 20121 := rs (se 2 (by rfl) ⟨7545, by rfl⟩) (B 15091 (by norm_num) ⟨7545, by rfl⟩ (by norm_num))
theorem R20125 : Reach 20125 := rs (se 3 (by rfl) ⟨3773, by rfl⟩) (B 7547 (by norm_num) ⟨3773, by rfl⟩ (by norm_num))
theorem R20129 : Reach 20129 := rs (se 2 (by rfl) ⟨7548, by rfl⟩) (B 15097 (by norm_num) ⟨7548, by rfl⟩ (by norm_num))
theorem R20133 : Reach 20133 := rs (se 4 (by rfl) ⟨1887, by rfl⟩) (B 3775 (by norm_num) ⟨1887, by rfl⟩ (by norm_num))
theorem R20137 : Reach 20137 := rs (se 2 (by rfl) ⟨7551, by rfl⟩) (B 15103 (by norm_num) ⟨7551, by rfl⟩ (by norm_num))
theorem R20141 : Reach 20141 := rs (se 3 (by rfl) ⟨3776, by rfl⟩) (B 7553 (by norm_num) ⟨3776, by rfl⟩ (by norm_num))
theorem R20145 : Reach 20145 := rs (se 2 (by rfl) ⟨7554, by rfl⟩) (B 15109 (by norm_num) ⟨7554, by rfl⟩ (by norm_num))
theorem R20149 : Reach 20149 := rs (se 5 (by rfl) ⟨944, by rfl⟩) (B 1889 (by norm_num) ⟨944, by rfl⟩ (by norm_num))
theorem R20153 : Reach 20153 := rs (se 2 (by rfl) ⟨7557, by rfl⟩) (B 15115 (by norm_num) ⟨7557, by rfl⟩ (by norm_num))
theorem R20157 : Reach 20157 := rs (se 3 (by rfl) ⟨3779, by rfl⟩) (B 7559 (by norm_num) ⟨3779, by rfl⟩ (by norm_num))
theorem R20161 : Reach 20161 := rs (se 2 (by rfl) ⟨7560, by rfl⟩) (B 15121 (by norm_num) ⟨7560, by rfl⟩ (by norm_num))
theorem R20165 : Reach 20165 := rs (se 4 (by rfl) ⟨1890, by rfl⟩) (B 3781 (by norm_num) ⟨1890, by rfl⟩ (by norm_num))
theorem R52933 : Reach 52933 := rs (se 4 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R20169 : Reach 20169 := rs (se 2 (by rfl) ⟨7563, by rfl⟩) (B 15127 (by norm_num) ⟨7563, by rfl⟩ (by norm_num))
theorem R20173 : Reach 20173 := rs (se 3 (by rfl) ⟨3782, by rfl⟩) (B 7565 (by norm_num) ⟨3782, by rfl⟩ (by norm_num))
theorem R20177 : Reach 20177 := rs (se 2 (by rfl) ⟨7566, by rfl⟩) (B 15133 (by norm_num) ⟨7566, by rfl⟩ (by norm_num))
theorem R20181 : Reach 20181 := rs (se 7 (by rfl) ⟨236, by rfl⟩) (B 473 (by norm_num) ⟨236, by rfl⟩ (by norm_num))
theorem R20185 : Reach 20185 := rs (se 2 (by rfl) ⟨7569, by rfl⟩) (B 15139 (by norm_num) ⟨7569, by rfl⟩ (by norm_num))
theorem R20189 : Reach 20189 := rs (se 3 (by rfl) ⟨3785, by rfl⟩) (B 7571 (by norm_num) ⟨3785, by rfl⟩ (by norm_num))
theorem R20193 : Reach 20193 := rs (se 2 (by rfl) ⟨7572, by rfl⟩) (B 15145 (by norm_num) ⟨7572, by rfl⟩ (by norm_num))
theorem R20197 : Reach 20197 := rs (se 4 (by rfl) ⟨1893, by rfl⟩) (B 3787 (by norm_num) ⟨1893, by rfl⟩ (by norm_num))
theorem R20201 : Reach 20201 := rs (se 2 (by rfl) ⟨7575, by rfl⟩) (B 15151 (by norm_num) ⟨7575, by rfl⟩ (by norm_num))
theorem R20205 : Reach 20205 := rs (se 3 (by rfl) ⟨3788, by rfl⟩) (B 7577 (by norm_num) ⟨3788, by rfl⟩ (by norm_num))
theorem R20209 : Reach 20209 := rs (se 2 (by rfl) ⟨7578, by rfl⟩) (B 15157 (by norm_num) ⟨7578, by rfl⟩ (by norm_num))
theorem R20213 : Reach 20213 := rs (se 5 (by rfl) ⟨947, by rfl⟩) (B 1895 (by norm_num) ⟨947, by rfl⟩ (by norm_num))
theorem R20217 : Reach 20217 := rs (se 2 (by rfl) ⟨7581, by rfl⟩) (B 15163 (by norm_num) ⟨7581, by rfl⟩ (by norm_num))
theorem R20221 : Reach 20221 := rs (se 3 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R20225 : Reach 20225 := rs (se 2 (by rfl) ⟨7584, by rfl⟩) (B 15169 (by norm_num) ⟨7584, by rfl⟩ (by norm_num))
theorem R20229 : Reach 20229 := rs (se 4 (by rfl) ⟨1896, by rfl⟩) (B 3793 (by norm_num) ⟨1896, by rfl⟩ (by norm_num))
theorem R20233 : Reach 20233 := rs (se 2 (by rfl) ⟨7587, by rfl⟩) (B 15175 (by norm_num) ⟨7587, by rfl⟩ (by norm_num))
theorem R20237 : Reach 20237 := rs (se 3 (by rfl) ⟨3794, by rfl⟩) (B 7589 (by norm_num) ⟨3794, by rfl⟩ (by norm_num))
theorem R20241 : Reach 20241 := rs (se 2 (by rfl) ⟨7590, by rfl⟩) (B 15181 (by norm_num) ⟨7590, by rfl⟩ (by norm_num))
theorem R20245 : Reach 20245 := rs (se 6 (by rfl) ⟨474, by rfl⟩) (B 949 (by norm_num) ⟨474, by rfl⟩ (by norm_num))
theorem R20249 : Reach 20249 := rs (se 2 (by rfl) ⟨7593, by rfl⟩) (B 15187 (by norm_num) ⟨7593, by rfl⟩ (by norm_num))
theorem R20253 : Reach 20253 := rs (se 3 (by rfl) ⟨3797, by rfl⟩) (B 7595 (by norm_num) ⟨3797, by rfl⟩ (by norm_num))
theorem R20257 : Reach 20257 := rs (se 2 (by rfl) ⟨7596, by rfl⟩) (B 15193 (by norm_num) ⟨7596, by rfl⟩ (by norm_num))
theorem R20261 : Reach 20261 := rs (se 4 (by rfl) ⟨1899, by rfl⟩) (B 3799 (by norm_num) ⟨1899, by rfl⟩ (by norm_num))
theorem R20265 : Reach 20265 := rs (se 2 (by rfl) ⟨7599, by rfl⟩) (B 15199 (by norm_num) ⟨7599, by rfl⟩ (by norm_num))
theorem R20269 : Reach 20269 := rs (se 3 (by rfl) ⟨3800, by rfl⟩) (B 7601 (by norm_num) ⟨3800, by rfl⟩ (by norm_num))
theorem R20273 : Reach 20273 := rs (se 2 (by rfl) ⟨7602, by rfl⟩) (B 15205 (by norm_num) ⟨7602, by rfl⟩ (by norm_num))
theorem R20277 : Reach 20277 := rs (se 5 (by rfl) ⟨950, by rfl⟩) (B 1901 (by norm_num) ⟨950, by rfl⟩ (by norm_num))
theorem R53045 : Reach 53045 := rs (se 5 (by rfl) ⟨2486, by rfl⟩) (B 4973 (by norm_num) ⟨2486, by rfl⟩ (by norm_num))
theorem R20281 : Reach 20281 := rs (se 2 (by rfl) ⟨7605, by rfl⟩) (B 15211 (by norm_num) ⟨7605, by rfl⟩ (by norm_num))
theorem R20285 : Reach 20285 := rs (se 3 (by rfl) ⟨3803, by rfl⟩) (B 7607 (by norm_num) ⟨3803, by rfl⟩ (by norm_num))
theorem R20289 : Reach 20289 := rs (se 2 (by rfl) ⟨7608, by rfl⟩) (B 15217 (by norm_num) ⟨7608, by rfl⟩ (by norm_num))
theorem R20293 : Reach 20293 := rs (se 4 (by rfl) ⟨1902, by rfl⟩) (B 3805 (by norm_num) ⟨1902, by rfl⟩ (by norm_num))
theorem R20297 : Reach 20297 := rs (se 2 (by rfl) ⟨7611, by rfl⟩) (B 15223 (by norm_num) ⟨7611, by rfl⟩ (by norm_num))
theorem R20301 : Reach 20301 := rs (se 3 (by rfl) ⟨3806, by rfl⟩) (B 7613 (by norm_num) ⟨3806, by rfl⟩ (by norm_num))
theorem R20305 : Reach 20305 := rs (se 2 (by rfl) ⟨7614, by rfl⟩) (B 15229 (by norm_num) ⟨7614, by rfl⟩ (by norm_num))
theorem R20309 : Reach 20309 := rs (se 9 (by rfl) ⟨59, by rfl⟩) (B 119 (by norm_num) ⟨59, by rfl⟩ (by norm_num))
theorem R20313 : Reach 20313 := rs (se 2 (by rfl) ⟨7617, by rfl⟩) (B 15235 (by norm_num) ⟨7617, by rfl⟩ (by norm_num))
theorem R20317 : Reach 20317 := rs (se 3 (by rfl) ⟨3809, by rfl⟩) (B 7619 (by norm_num) ⟨3809, by rfl⟩ (by norm_num))
theorem R20321 : Reach 20321 := rs (se 2 (by rfl) ⟨7620, by rfl⟩) (B 15241 (by norm_num) ⟨7620, by rfl⟩ (by norm_num))
theorem R20325 : Reach 20325 := rs (se 4 (by rfl) ⟨1905, by rfl⟩) (B 3811 (by norm_num) ⟨1905, by rfl⟩ (by norm_num))
theorem R20329 : Reach 20329 := rs (se 2 (by rfl) ⟨7623, by rfl⟩) (B 15247 (by norm_num) ⟨7623, by rfl⟩ (by norm_num))
theorem R20333 : Reach 20333 := rs (se 3 (by rfl) ⟨3812, by rfl⟩) (B 7625 (by norm_num) ⟨3812, by rfl⟩ (by norm_num))
theorem R20337 : Reach 20337 := rs (se 2 (by rfl) ⟨7626, by rfl⟩) (B 15253 (by norm_num) ⟨7626, by rfl⟩ (by norm_num))
theorem R20341 : Reach 20341 := rs (se 5 (by rfl) ⟨953, by rfl⟩) (B 1907 (by norm_num) ⟨953, by rfl⟩ (by norm_num))
theorem R20345 : Reach 20345 := rs (se 2 (by rfl) ⟨7629, by rfl⟩) (B 15259 (by norm_num) ⟨7629, by rfl⟩ (by norm_num))
theorem R20349 : Reach 20349 := rs (se 3 (by rfl) ⟨3815, by rfl⟩) (B 7631 (by norm_num) ⟨3815, by rfl⟩ (by norm_num))
theorem R20353 : Reach 20353 := rs (se 2 (by rfl) ⟨7632, by rfl⟩) (B 15265 (by norm_num) ⟨7632, by rfl⟩ (by norm_num))
theorem R20357 : Reach 20357 := rs (se 4 (by rfl) ⟨1908, by rfl⟩) (B 3817 (by norm_num) ⟨1908, by rfl⟩ (by norm_num))
theorem R20361 : Reach 20361 := rs (se 2 (by rfl) ⟨7635, by rfl⟩) (B 15271 (by norm_num) ⟨7635, by rfl⟩ (by norm_num))
theorem R20365 : Reach 20365 := rs (se 3 (by rfl) ⟨3818, by rfl⟩) (B 7637 (by norm_num) ⟨3818, by rfl⟩ (by norm_num))
theorem R20369 : Reach 20369 := rs (se 2 (by rfl) ⟨7638, by rfl⟩) (B 15277 (by norm_num) ⟨7638, by rfl⟩ (by norm_num))
theorem R20373 : Reach 20373 := rs (se 6 (by rfl) ⟨477, by rfl⟩) (B 955 (by norm_num) ⟨477, by rfl⟩ (by norm_num))
theorem R20377 : Reach 20377 := rs (se 2 (by rfl) ⟨7641, by rfl⟩) (B 15283 (by norm_num) ⟨7641, by rfl⟩ (by norm_num))
theorem R20381 : Reach 20381 := rs (se 3 (by rfl) ⟨3821, by rfl⟩) (B 7643 (by norm_num) ⟨3821, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R20385 : Reach 20385 := rs (se 2 (by rfl) ⟨7644, by rfl⟩) (B 15289 (by norm_num) ⟨7644, by rfl⟩ (by norm_num))
theorem R20389 : Reach 20389 := rs (se 4 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R20393 : Reach 20393 := rs (se 2 (by rfl) ⟨7647, by rfl⟩) (B 15295 (by norm_num) ⟨7647, by rfl⟩ (by norm_num))
theorem R20397 : Reach 20397 := rs (se 3 (by rfl) ⟨3824, by rfl⟩) (B 7649 (by norm_num) ⟨3824, by rfl⟩ (by norm_num))
theorem R20401 : Reach 20401 := rs (se 2 (by rfl) ⟨7650, by rfl⟩) (B 15301 (by norm_num) ⟨7650, by rfl⟩ (by norm_num))
theorem R20405 : Reach 20405 := rs (se 5 (by rfl) ⟨956, by rfl⟩) (B 1913 (by norm_num) ⟨956, by rfl⟩ (by norm_num))
theorem R20409 : Reach 20409 := rs (se 2 (by rfl) ⟨7653, by rfl⟩) (B 15307 (by norm_num) ⟨7653, by rfl⟩ (by norm_num))
theorem R20413 : Reach 20413 := rs (se 3 (by rfl) ⟨3827, by rfl⟩) (B 7655 (by norm_num) ⟨3827, by rfl⟩ (by norm_num))
theorem R20417 : Reach 20417 := rs (se 2 (by rfl) ⟨7656, by rfl⟩) (B 15313 (by norm_num) ⟨7656, by rfl⟩ (by norm_num))
theorem R20421 : Reach 20421 := rs (se 4 (by rfl) ⟨1914, by rfl⟩) (B 3829 (by norm_num) ⟨1914, by rfl⟩ (by norm_num))
theorem R20425 : Reach 20425 := rs (se 2 (by rfl) ⟨7659, by rfl⟩) (B 15319 (by norm_num) ⟨7659, by rfl⟩ (by norm_num))
theorem R20429 : Reach 20429 := rs (se 3 (by rfl) ⟨3830, by rfl⟩) (B 7661 (by norm_num) ⟨3830, by rfl⟩ (by norm_num))
theorem R20433 : Reach 20433 := rs (se 2 (by rfl) ⟨7662, by rfl⟩) (B 15325 (by norm_num) ⟨7662, by rfl⟩ (by norm_num))
theorem R20437 : Reach 20437 := rs (se 7 (by rfl) ⟨239, by rfl⟩) (B 479 (by norm_num) ⟨239, by rfl⟩ (by norm_num))
theorem R20441 : Reach 20441 := rs (se 2 (by rfl) ⟨7665, by rfl⟩) (B 15331 (by norm_num) ⟨7665, by rfl⟩ (by norm_num))
theorem R20445 : Reach 20445 := rs (se 3 (by rfl) ⟨3833, by rfl⟩) (B 7667 (by norm_num) ⟨3833, by rfl⟩ (by norm_num))
theorem R20449 : Reach 20449 := rs (se 2 (by rfl) ⟨7668, by rfl⟩) (B 15337 (by norm_num) ⟨7668, by rfl⟩ (by norm_num))
theorem R20453 : Reach 20453 := rs (se 4 (by rfl) ⟨1917, by rfl⟩) (B 3835 (by norm_num) ⟨1917, by rfl⟩ (by norm_num))
theorem R20457 : Reach 20457 := rs (se 2 (by rfl) ⟨7671, by rfl⟩) (B 15343 (by norm_num) ⟨7671, by rfl⟩ (by norm_num))
theorem R20461 : Reach 20461 := rs (se 3 (by rfl) ⟨3836, by rfl⟩) (B 7673 (by norm_num) ⟨3836, by rfl⟩ (by norm_num))
theorem R20465 : Reach 20465 := rs (se 2 (by rfl) ⟨7674, by rfl⟩) (B 15349 (by norm_num) ⟨7674, by rfl⟩ (by norm_num))
theorem R20469 : Reach 20469 := rs (se 5 (by rfl) ⟨959, by rfl⟩) (B 1919 (by norm_num) ⟨959, by rfl⟩ (by norm_num))
theorem R53237 : Reach 53237 := rs (se 5 (by rfl) ⟨2495, by rfl⟩) (B 4991 (by norm_num) ⟨2495, by rfl⟩ (by norm_num))
theorem R20473 : Reach 20473 := rs (se 2 (by rfl) ⟨7677, by rfl⟩) (B 15355 (by norm_num) ⟨7677, by rfl⟩ (by norm_num))
theorem R20477 : Reach 20477 := rs (se 3 (by rfl) ⟨3839, by rfl⟩) (B 7679 (by norm_num) ⟨3839, by rfl⟩ (by norm_num))
theorem R20481 : Reach 20481 := rs (se 2 (by rfl) ⟨7680, by rfl⟩) (B 15361 (by norm_num) ⟨7680, by rfl⟩ (by norm_num))
theorem R20485 : Reach 20485 := rs (se 4 (by rfl) ⟨1920, by rfl⟩) (B 3841 (by norm_num) ⟨1920, by rfl⟩ (by norm_num))
theorem R20489 : Reach 20489 := rs (se 2 (by rfl) ⟨7683, by rfl⟩) (B 15367 (by norm_num) ⟨7683, by rfl⟩ (by norm_num))
theorem R20493 : Reach 20493 := rs (se 3 (by rfl) ⟨3842, by rfl⟩) (B 7685 (by norm_num) ⟨3842, by rfl⟩ (by norm_num))
theorem R20497 : Reach 20497 := rs (se 2 (by rfl) ⟨7686, by rfl⟩) (B 15373 (by norm_num) ⟨7686, by rfl⟩ (by norm_num))
theorem R20501 : Reach 20501 := rs (se 6 (by rfl) ⟨480, by rfl⟩) (B 961 (by norm_num) ⟨480, by rfl⟩ (by norm_num))
theorem R20505 : Reach 20505 := rs (se 2 (by rfl) ⟨7689, by rfl⟩) (B 15379 (by norm_num) ⟨7689, by rfl⟩ (by norm_num))
theorem R20509 : Reach 20509 := rs (se 3 (by rfl) ⟨3845, by rfl⟩) (B 7691 (by norm_num) ⟨3845, by rfl⟩ (by norm_num))
theorem R20513 : Reach 20513 := rs (se 2 (by rfl) ⟨7692, by rfl⟩) (B 15385 (by norm_num) ⟨7692, by rfl⟩ (by norm_num))
theorem R20517 : Reach 20517 := rs (se 4 (by rfl) ⟨1923, by rfl⟩) (B 3847 (by norm_num) ⟨1923, by rfl⟩ (by norm_num))
theorem R20521 : Reach 20521 := rs (se 2 (by rfl) ⟨7695, by rfl⟩) (B 15391 (by norm_num) ⟨7695, by rfl⟩ (by norm_num))
theorem R20525 : Reach 20525 := rs (se 3 (by rfl) ⟨3848, by rfl⟩) (B 7697 (by norm_num) ⟨3848, by rfl⟩ (by norm_num))
theorem R20529 : Reach 20529 := rs (se 2 (by rfl) ⟨7698, by rfl⟩) (B 15397 (by norm_num) ⟨7698, by rfl⟩ (by norm_num))
theorem R20533 : Reach 20533 := rs (se 5 (by rfl) ⟨962, by rfl⟩) (B 1925 (by norm_num) ⟨962, by rfl⟩ (by norm_num))
theorem R20537 : Reach 20537 := rs (se 2 (by rfl) ⟨7701, by rfl⟩) (B 15403 (by norm_num) ⟨7701, by rfl⟩ (by norm_num))
theorem R20541 : Reach 20541 := rs (se 3 (by rfl) ⟨3851, by rfl⟩) (B 7703 (by norm_num) ⟨3851, by rfl⟩ (by norm_num))
theorem R20545 : Reach 20545 := rs (se 2 (by rfl) ⟨7704, by rfl⟩) (B 15409 (by norm_num) ⟨7704, by rfl⟩ (by norm_num))
theorem R20549 : Reach 20549 := rs (se 4 (by rfl) ⟨1926, by rfl⟩) (B 3853 (by norm_num) ⟨1926, by rfl⟩ (by norm_num))
theorem R20553 : Reach 20553 := rs (se 2 (by rfl) ⟨7707, by rfl⟩) (B 15415 (by norm_num) ⟨7707, by rfl⟩ (by norm_num))
theorem R20557 : Reach 20557 := rs (se 3 (by rfl) ⟨3854, by rfl⟩) (B 7709 (by norm_num) ⟨3854, by rfl⟩ (by norm_num))
theorem R20561 : Reach 20561 := rs (se 2 (by rfl) ⟨7710, by rfl⟩) (B 15421 (by norm_num) ⟨7710, by rfl⟩ (by norm_num))
theorem R20565 : Reach 20565 := rs (se 8 (by rfl) ⟨120, by rfl⟩) (B 241 (by norm_num) ⟨120, by rfl⟩ (by norm_num))
theorem R20569 : Reach 20569 := rs (se 2 (by rfl) ⟨7713, by rfl⟩) (B 15427 (by norm_num) ⟨7713, by rfl⟩ (by norm_num))
theorem R20573 : Reach 20573 := rs (se 3 (by rfl) ⟨3857, by rfl⟩) (B 7715 (by norm_num) ⟨3857, by rfl⟩ (by norm_num))
theorem R20577 : Reach 20577 := rs (se 2 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R20581 : Reach 20581 := rs (se 4 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R20585 : Reach 20585 := rs (se 2 (by rfl) ⟨7719, by rfl⟩) (B 15439 (by norm_num) ⟨7719, by rfl⟩ (by norm_num))
theorem R20589 : Reach 20589 := rs (se 3 (by rfl) ⟨3860, by rfl⟩) (B 7721 (by norm_num) ⟨3860, by rfl⟩ (by norm_num))
theorem R20593 : Reach 20593 := rs (se 2 (by rfl) ⟨7722, by rfl⟩) (B 15445 (by norm_num) ⟨7722, by rfl⟩ (by norm_num))
theorem R20597 : Reach 20597 := rs (se 5 (by rfl) ⟨965, by rfl⟩) (B 1931 (by norm_num) ⟨965, by rfl⟩ (by norm_num))
theorem R20601 : Reach 20601 := rs (se 2 (by rfl) ⟨7725, by rfl⟩) (B 15451 (by norm_num) ⟨7725, by rfl⟩ (by norm_num))
theorem R20605 : Reach 20605 := rs (se 3 (by rfl) ⟨3863, by rfl⟩) (B 7727 (by norm_num) ⟨3863, by rfl⟩ (by norm_num))
theorem R20609 : Reach 20609 := rs (se 2 (by rfl) ⟨7728, by rfl⟩) (B 15457 (by norm_num) ⟨7728, by rfl⟩ (by norm_num))
theorem R20613 : Reach 20613 := rs (se 4 (by rfl) ⟨1932, by rfl⟩) (B 3865 (by norm_num) ⟨1932, by rfl⟩ (by norm_num))
theorem R20617 : Reach 20617 := rs (se 2 (by rfl) ⟨7731, by rfl⟩) (B 15463 (by norm_num) ⟨7731, by rfl⟩ (by norm_num))
theorem R20621 : Reach 20621 := rs (se 3 (by rfl) ⟨3866, by rfl⟩) (B 7733 (by norm_num) ⟨3866, by rfl⟩ (by norm_num))
theorem R20625 : Reach 20625 := rs (se 2 (by rfl) ⟨7734, by rfl⟩) (B 15469 (by norm_num) ⟨7734, by rfl⟩ (by norm_num))
theorem R20629 : Reach 20629 := rs (se 6 (by rfl) ⟨483, by rfl⟩) (B 967 (by norm_num) ⟨483, by rfl⟩ (by norm_num))
theorem R20633 : Reach 20633 := rs (se 2 (by rfl) ⟨7737, by rfl⟩) (B 15475 (by norm_num) ⟨7737, by rfl⟩ (by norm_num))
theorem R20637 : Reach 20637 := rs (se 3 (by rfl) ⟨3869, by rfl⟩) (B 7739 (by norm_num) ⟨3869, by rfl⟩ (by norm_num))
theorem R20641 : Reach 20641 := rs (se 2 (by rfl) ⟨7740, by rfl⟩) (B 15481 (by norm_num) ⟨7740, by rfl⟩ (by norm_num))
theorem R20645 : Reach 20645 := rs (se 4 (by rfl) ⟨1935, by rfl⟩) (B 3871 (by norm_num) ⟨1935, by rfl⟩ (by norm_num))
theorem R20649 : Reach 20649 := rs (se 2 (by rfl) ⟨7743, by rfl⟩) (B 15487 (by norm_num) ⟨7743, by rfl⟩ (by norm_num))
theorem R20653 : Reach 20653 := rs (se 3 (by rfl) ⟨3872, by rfl⟩) (B 7745 (by norm_num) ⟨3872, by rfl⟩ (by norm_num))
theorem R20657 : Reach 20657 := rs (se 2 (by rfl) ⟨7746, by rfl⟩) (B 15493 (by norm_num) ⟨7746, by rfl⟩ (by norm_num))
theorem R20661 : Reach 20661 := rs (se 5 (by rfl) ⟨968, by rfl⟩) (B 1937 (by norm_num) ⟨968, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R20665 : Reach 20665 := rs (se 2 (by rfl) ⟨7749, by rfl⟩) (B 15499 (by norm_num) ⟨7749, by rfl⟩ (by norm_num))
theorem R20669 : Reach 20669 := rs (se 3 (by rfl) ⟨3875, by rfl⟩) (B 7751 (by norm_num) ⟨3875, by rfl⟩ (by norm_num))
theorem R20673 : Reach 20673 := rs (se 2 (by rfl) ⟨7752, by rfl⟩) (B 15505 (by norm_num) ⟨7752, by rfl⟩ (by norm_num))
theorem R20677 : Reach 20677 := rs (se 4 (by rfl) ⟨1938, by rfl⟩) (B 3877 (by norm_num) ⟨1938, by rfl⟩ (by norm_num))
theorem R20681 : Reach 20681 := rs (se 2 (by rfl) ⟨7755, by rfl⟩) (B 15511 (by norm_num) ⟨7755, by rfl⟩ (by norm_num))
theorem R20685 : Reach 20685 := rs (se 3 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R20689 : Reach 20689 := rs (se 2 (by rfl) ⟨7758, by rfl⟩) (B 15517 (by norm_num) ⟨7758, by rfl⟩ (by norm_num))
theorem R20693 : Reach 20693 := rs (se 7 (by rfl) ⟨242, by rfl⟩) (B 485 (by norm_num) ⟨242, by rfl⟩ (by norm_num))
theorem R20697 : Reach 20697 := rs (se 2 (by rfl) ⟨7761, by rfl⟩) (B 15523 (by norm_num) ⟨7761, by rfl⟩ (by norm_num))
theorem R20701 : Reach 20701 := rs (se 3 (by rfl) ⟨3881, by rfl⟩) (B 7763 (by norm_num) ⟨3881, by rfl⟩ (by norm_num))
theorem R20705 : Reach 20705 := rs (se 2 (by rfl) ⟨7764, by rfl⟩) (B 15529 (by norm_num) ⟨7764, by rfl⟩ (by norm_num))
theorem R20709 : Reach 20709 := rs (se 4 (by rfl) ⟨1941, by rfl⟩) (B 3883 (by norm_num) ⟨1941, by rfl⟩ (by norm_num))
theorem R20713 : Reach 20713 := rs (se 2 (by rfl) ⟨7767, by rfl⟩) (B 15535 (by norm_num) ⟨7767, by rfl⟩ (by norm_num))
theorem R20717 : Reach 20717 := rs (se 3 (by rfl) ⟨3884, by rfl⟩) (B 7769 (by norm_num) ⟨3884, by rfl⟩ (by norm_num))
theorem R20721 : Reach 20721 := rs (se 2 (by rfl) ⟨7770, by rfl⟩) (B 15541 (by norm_num) ⟨7770, by rfl⟩ (by norm_num))
theorem R20725 : Reach 20725 := rs (se 5 (by rfl) ⟨971, by rfl⟩) (B 1943 (by norm_num) ⟨971, by rfl⟩ (by norm_num))
theorem R20729 : Reach 20729 := rs (se 2 (by rfl) ⟨7773, by rfl⟩) (B 15547 (by norm_num) ⟨7773, by rfl⟩ (by norm_num))
theorem R20733 : Reach 20733 := rs (se 3 (by rfl) ⟨3887, by rfl⟩) (B 7775 (by norm_num) ⟨3887, by rfl⟩ (by norm_num))
theorem R20737 : Reach 20737 := rs (se 2 (by rfl) ⟨7776, by rfl⟩) (B 15553 (by norm_num) ⟨7776, by rfl⟩ (by norm_num))
theorem R20741 : Reach 20741 := rs (se 4 (by rfl) ⟨1944, by rfl⟩) (B 3889 (by norm_num) ⟨1944, by rfl⟩ (by norm_num))
theorem R20745 : Reach 20745 := rs (se 2 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R20749 : Reach 20749 := rs (se 3 (by rfl) ⟨3890, by rfl⟩) (B 7781 (by norm_num) ⟨3890, by rfl⟩ (by norm_num))
theorem R20753 : Reach 20753 := rs (se 2 (by rfl) ⟨7782, by rfl⟩) (B 15565 (by norm_num) ⟨7782, by rfl⟩ (by norm_num))
theorem R20757 : Reach 20757 := rs (se 6 (by rfl) ⟨486, by rfl⟩) (B 973 (by norm_num) ⟨486, by rfl⟩ (by norm_num))
theorem R20761 : Reach 20761 := rs (se 2 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R20765 : Reach 20765 := rs (se 3 (by rfl) ⟨3893, by rfl⟩) (B 7787 (by norm_num) ⟨3893, by rfl⟩ (by norm_num))
theorem R20769 : Reach 20769 := rs (se 2 (by rfl) ⟨7788, by rfl⟩) (B 15577 (by norm_num) ⟨7788, by rfl⟩ (by norm_num))
theorem R20773 : Reach 20773 := rs (se 4 (by rfl) ⟨1947, by rfl⟩) (B 3895 (by norm_num) ⟨1947, by rfl⟩ (by norm_num))
theorem R20777 : Reach 20777 := rs (se 2 (by rfl) ⟨7791, by rfl⟩) (B 15583 (by norm_num) ⟨7791, by rfl⟩ (by norm_num))
theorem R20781 : Reach 20781 := rs (se 3 (by rfl) ⟨3896, by rfl⟩) (B 7793 (by norm_num) ⟨3896, by rfl⟩ (by norm_num))
theorem R20785 : Reach 20785 := rs (se 2 (by rfl) ⟨7794, by rfl⟩) (B 15589 (by norm_num) ⟨7794, by rfl⟩ (by norm_num))
theorem R20789 : Reach 20789 := rs (se 5 (by rfl) ⟨974, by rfl⟩) (B 1949 (by norm_num) ⟨974, by rfl⟩ (by norm_num))
theorem R20793 : Reach 20793 := rs (se 2 (by rfl) ⟨7797, by rfl⟩) (B 15595 (by norm_num) ⟨7797, by rfl⟩ (by norm_num))
theorem R20797 : Reach 20797 := rs (se 3 (by rfl) ⟨3899, by rfl⟩) (B 7799 (by norm_num) ⟨3899, by rfl⟩ (by norm_num))
theorem R20801 : Reach 20801 := rs (se 2 (by rfl) ⟨7800, by rfl⟩) (B 15601 (by norm_num) ⟨7800, by rfl⟩ (by norm_num))
theorem R20805 : Reach 20805 := rs (se 4 (by rfl) ⟨1950, by rfl⟩) (B 3901 (by norm_num) ⟨1950, by rfl⟩ (by norm_num))
theorem R20809 : Reach 20809 := rs (se 2 (by rfl) ⟨7803, by rfl⟩) (B 15607 (by norm_num) ⟨7803, by rfl⟩ (by norm_num))
theorem R20813 : Reach 20813 := rs (se 3 (by rfl) ⟨3902, by rfl⟩) (B 7805 (by norm_num) ⟨3902, by rfl⟩ (by norm_num))
theorem R20817 : Reach 20817 := rs (se 2 (by rfl) ⟨7806, by rfl⟩) (B 15613 (by norm_num) ⟨7806, by rfl⟩ (by norm_num))
theorem R20821 : Reach 20821 := rs (se 10 (by rfl) ⟨30, by rfl⟩) (B 61 (by norm_num) ⟨30, by rfl⟩ (by norm_num))
theorem R20825 : Reach 20825 := rs (se 2 (by rfl) ⟨7809, by rfl⟩) (B 15619 (by norm_num) ⟨7809, by rfl⟩ (by norm_num))
theorem R20829 : Reach 20829 := rs (se 3 (by rfl) ⟨3905, by rfl⟩) (B 7811 (by norm_num) ⟨3905, by rfl⟩ (by norm_num))
theorem R20833 : Reach 20833 := rs (se 2 (by rfl) ⟨7812, by rfl⟩) (B 15625 (by norm_num) ⟨7812, by rfl⟩ (by norm_num))
theorem R20837 : Reach 20837 := rs (se 4 (by rfl) ⟨1953, by rfl⟩) (B 3907 (by norm_num) ⟨1953, by rfl⟩ (by norm_num))
theorem R20841 : Reach 20841 := rs (se 2 (by rfl) ⟨7815, by rfl⟩) (B 15631 (by norm_num) ⟨7815, by rfl⟩ (by norm_num))
theorem R20845 : Reach 20845 := rs (se 3 (by rfl) ⟨3908, by rfl⟩) (B 7817 (by norm_num) ⟨3908, by rfl⟩ (by norm_num))
theorem R20849 : Reach 20849 := rs (se 2 (by rfl) ⟨7818, by rfl⟩) (B 15637 (by norm_num) ⟨7818, by rfl⟩ (by norm_num))
theorem R20853 : Reach 20853 := rs (se 5 (by rfl) ⟨977, by rfl⟩) (B 1955 (by norm_num) ⟨977, by rfl⟩ (by norm_num))
theorem R20857 : Reach 20857 := rs (se 2 (by rfl) ⟨7821, by rfl⟩) (B 15643 (by norm_num) ⟨7821, by rfl⟩ (by norm_num))
theorem R20861 : Reach 20861 := rs (se 3 (by rfl) ⟨3911, by rfl⟩) (B 7823 (by norm_num) ⟨3911, by rfl⟩ (by norm_num))
theorem R20865 : Reach 20865 := rs (se 2 (by rfl) ⟨7824, by rfl⟩) (B 15649 (by norm_num) ⟨7824, by rfl⟩ (by norm_num))
theorem R20869 : Reach 20869 := rs (se 4 (by rfl) ⟨1956, by rfl⟩) (B 3913 (by norm_num) ⟨1956, by rfl⟩ (by norm_num))
theorem R20873 : Reach 20873 := rs (se 2 (by rfl) ⟨7827, by rfl⟩) (B 15655 (by norm_num) ⟨7827, by rfl⟩ (by norm_num))
theorem R20877 : Reach 20877 := rs (se 3 (by rfl) ⟨3914, by rfl⟩) (B 7829 (by norm_num) ⟨3914, by rfl⟩ (by norm_num))
theorem R20881 : Reach 20881 := rs (se 2 (by rfl) ⟨7830, by rfl⟩) (B 15661 (by norm_num) ⟨7830, by rfl⟩ (by norm_num))
theorem R20885 : Reach 20885 := rs (se 6 (by rfl) ⟨489, by rfl⟩) (B 979 (by norm_num) ⟨489, by rfl⟩ (by norm_num))
theorem R20889 : Reach 20889 := rs (se 2 (by rfl) ⟨7833, by rfl⟩) (B 15667 (by norm_num) ⟨7833, by rfl⟩ (by norm_num))
theorem R20893 : Reach 20893 := rs (se 3 (by rfl) ⟨3917, by rfl⟩) (B 7835 (by norm_num) ⟨3917, by rfl⟩ (by norm_num))
theorem R20897 : Reach 20897 := rs (se 2 (by rfl) ⟨7836, by rfl⟩) (B 15673 (by norm_num) ⟨7836, by rfl⟩ (by norm_num))
theorem R20901 : Reach 20901 := rs (se 4 (by rfl) ⟨1959, by rfl⟩) (B 3919 (by norm_num) ⟨1959, by rfl⟩ (by norm_num))
theorem R20905 : Reach 20905 := rs (se 2 (by rfl) ⟨7839, by rfl⟩) (B 15679 (by norm_num) ⟨7839, by rfl⟩ (by norm_num))
theorem R20909 : Reach 20909 := rs (se 3 (by rfl) ⟨3920, by rfl⟩) (B 7841 (by norm_num) ⟨3920, by rfl⟩ (by norm_num))
theorem R20913 : Reach 20913 := rs (se 2 (by rfl) ⟨7842, by rfl⟩) (B 15685 (by norm_num) ⟨7842, by rfl⟩ (by norm_num))
theorem R20917 : Reach 20917 := rs (se 5 (by rfl) ⟨980, by rfl⟩) (B 1961 (by norm_num) ⟨980, by rfl⟩ (by norm_num))
theorem R20921 : Reach 20921 := rs (se 2 (by rfl) ⟨7845, by rfl⟩) (B 15691 (by norm_num) ⟨7845, by rfl⟩ (by norm_num))
theorem R20925 : Reach 20925 := rs (se 3 (by rfl) ⟨3923, by rfl⟩) (B 7847 (by norm_num) ⟨3923, by rfl⟩ (by norm_num))
theorem R20929 : Reach 20929 := rs (se 2 (by rfl) ⟨7848, by rfl⟩) (B 15697 (by norm_num) ⟨7848, by rfl⟩ (by norm_num))
theorem R20933 : Reach 20933 := rs (se 4 (by rfl) ⟨1962, by rfl⟩) (B 3925 (by norm_num) ⟨1962, by rfl⟩ (by norm_num))
theorem R20937 : Reach 20937 := rs (se 2 (by rfl) ⟨7851, by rfl⟩) (B 15703 (by norm_num) ⟨7851, by rfl⟩ (by norm_num))
theorem R20941 : Reach 20941 := rs (se 3 (by rfl) ⟨3926, by rfl⟩) (B 7853 (by norm_num) ⟨3926, by rfl⟩ (by norm_num))
theorem R20945 : Reach 20945 := rs (se 2 (by rfl) ⟨7854, by rfl⟩) (B 15709 (by norm_num) ⟨7854, by rfl⟩ (by norm_num))
theorem R20949 : Reach 20949 := rs (se 7 (by rfl) ⟨245, by rfl⟩) (B 491 (by norm_num) ⟨245, by rfl⟩ (by norm_num))
theorem R20953 : Reach 20953 := rs (se 2 (by rfl) ⟨7857, by rfl⟩) (B 15715 (by norm_num) ⟨7857, by rfl⟩ (by norm_num))
theorem R20957 : Reach 20957 := rs (se 3 (by rfl) ⟨3929, by rfl⟩) (B 7859 (by norm_num) ⟨3929, by rfl⟩ (by norm_num))
theorem R20961 : Reach 20961 := rs (se 2 (by rfl) ⟨7860, by rfl⟩) (B 15721 (by norm_num) ⟨7860, by rfl⟩ (by norm_num))
theorem R20965 : Reach 20965 := rs (se 4 (by rfl) ⟨1965, by rfl⟩) (B 3931 (by norm_num) ⟨1965, by rfl⟩ (by norm_num))
theorem R20969 : Reach 20969 := rs (se 2 (by rfl) ⟨7863, by rfl⟩) (B 15727 (by norm_num) ⟨7863, by rfl⟩ (by norm_num))
theorem R20973 : Reach 20973 := rs (se 3 (by rfl) ⟨3932, by rfl⟩) (B 7865 (by norm_num) ⟨3932, by rfl⟩ (by norm_num))
theorem R20977 : Reach 20977 := rs (se 2 (by rfl) ⟨7866, by rfl⟩) (B 15733 (by norm_num) ⟨7866, by rfl⟩ (by norm_num))
theorem R20981 : Reach 20981 := rs (se 5 (by rfl) ⟨983, by rfl⟩) (B 1967 (by norm_num) ⟨983, by rfl⟩ (by norm_num))
theorem R20985 : Reach 20985 := rs (se 2 (by rfl) ⟨7869, by rfl⟩) (B 15739 (by norm_num) ⟨7869, by rfl⟩ (by norm_num))
theorem R20989 : Reach 20989 := rs (se 3 (by rfl) ⟨3935, by rfl⟩) (B 7871 (by norm_num) ⟨3935, by rfl⟩ (by norm_num))
theorem R20993 : Reach 20993 := rs (se 2 (by rfl) ⟨7872, by rfl⟩) (B 15745 (by norm_num) ⟨7872, by rfl⟩ (by norm_num))
theorem R20997 : Reach 20997 := rs (se 4 (by rfl) ⟨1968, by rfl⟩) (B 3937 (by norm_num) ⟨1968, by rfl⟩ (by norm_num))
theorem R21001 : Reach 21001 := rs (se 2 (by rfl) ⟨7875, by rfl⟩) (B 15751 (by norm_num) ⟨7875, by rfl⟩ (by norm_num))
theorem R21005 : Reach 21005 := rs (se 3 (by rfl) ⟨3938, by rfl⟩) (B 7877 (by norm_num) ⟨3938, by rfl⟩ (by norm_num))
theorem R21009 : Reach 21009 := rs (se 2 (by rfl) ⟨7878, by rfl⟩) (B 15757 (by norm_num) ⟨7878, by rfl⟩ (by norm_num))
theorem R21013 : Reach 21013 := rs (se 6 (by rfl) ⟨492, by rfl⟩) (B 985 (by norm_num) ⟨492, by rfl⟩ (by norm_num))
theorem R21017 : Reach 21017 := rs (se 2 (by rfl) ⟨7881, by rfl⟩) (B 15763 (by norm_num) ⟨7881, by rfl⟩ (by norm_num))
theorem R21021 : Reach 21021 := rs (se 3 (by rfl) ⟨3941, by rfl⟩) (B 7883 (by norm_num) ⟨3941, by rfl⟩ (by norm_num))
theorem R21025 : Reach 21025 := rs (se 2 (by rfl) ⟨7884, by rfl⟩) (B 15769 (by norm_num) ⟨7884, by rfl⟩ (by norm_num))
theorem R21029 : Reach 21029 := rs (se 4 (by rfl) ⟨1971, by rfl⟩) (B 3943 (by norm_num) ⟨1971, by rfl⟩ (by norm_num))
theorem R21033 : Reach 21033 := rs (se 2 (by rfl) ⟨7887, by rfl⟩) (B 15775 (by norm_num) ⟨7887, by rfl⟩ (by norm_num))
theorem R21037 : Reach 21037 := rs (se 3 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R21041 : Reach 21041 := rs (se 2 (by rfl) ⟨7890, by rfl⟩) (B 15781 (by norm_num) ⟨7890, by rfl⟩ (by norm_num))
theorem R152117 : Reach 152117 := rs (se 5 (by rfl) ⟨7130, by rfl⟩) (B 14261 (by norm_num) ⟨7130, by rfl⟩ (by norm_num))
theorem R21045 : Reach 21045 := rs (se 5 (by rfl) ⟨986, by rfl⟩) (B 1973 (by norm_num) ⟨986, by rfl⟩ (by norm_num))
theorem R21049 : Reach 21049 := rs (se 2 (by rfl) ⟨7893, by rfl⟩) (B 15787 (by norm_num) ⟨7893, by rfl⟩ (by norm_num))
theorem R21053 : Reach 21053 := rs (se 3 (by rfl) ⟨3947, by rfl⟩) (B 7895 (by norm_num) ⟨3947, by rfl⟩ (by norm_num))
theorem R21057 : Reach 21057 := rs (se 2 (by rfl) ⟨7896, by rfl⟩) (B 15793 (by norm_num) ⟨7896, by rfl⟩ (by norm_num))
theorem R21061 : Reach 21061 := rs (se 4 (by rfl) ⟨1974, by rfl⟩) (B 3949 (by norm_num) ⟨1974, by rfl⟩ (by norm_num))
theorem R21065 : Reach 21065 := rs (se 2 (by rfl) ⟨7899, by rfl⟩) (B 15799 (by norm_num) ⟨7899, by rfl⟩ (by norm_num))
theorem R21069 : Reach 21069 := rs (se 3 (by rfl) ⟨3950, by rfl⟩) (B 7901 (by norm_num) ⟨3950, by rfl⟩ (by norm_num))
theorem R21073 : Reach 21073 := rs (se 2 (by rfl) ⟨7902, by rfl⟩) (B 15805 (by norm_num) ⟨7902, by rfl⟩ (by norm_num))
theorem R21077 : Reach 21077 := rs (se 8 (by rfl) ⟨123, by rfl⟩) (B 247 (by norm_num) ⟨123, by rfl⟩ (by norm_num))
theorem R21081 : Reach 21081 := rs (se 2 (by rfl) ⟨7905, by rfl⟩) (B 15811 (by norm_num) ⟨7905, by rfl⟩ (by norm_num))
theorem R21085 : Reach 21085 := rs (se 3 (by rfl) ⟨3953, by rfl⟩) (B 7907 (by norm_num) ⟨3953, by rfl⟩ (by norm_num))
theorem R21089 : Reach 21089 := rs (se 2 (by rfl) ⟨7908, by rfl⟩) (B 15817 (by norm_num) ⟨7908, by rfl⟩ (by norm_num))
theorem R21093 : Reach 21093 := rs (se 4 (by rfl) ⟨1977, by rfl⟩) (B 3955 (by norm_num) ⟨1977, by rfl⟩ (by norm_num))
theorem R86629 : Reach 86629 := rs (se 4 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R21097 : Reach 21097 := rs (se 2 (by rfl) ⟨7911, by rfl⟩) (B 15823 (by norm_num) ⟨7911, by rfl⟩ (by norm_num))
theorem R21101 : Reach 21101 := rs (se 3 (by rfl) ⟨3956, by rfl⟩) (B 7913 (by norm_num) ⟨3956, by rfl⟩ (by norm_num))
theorem R21105 : Reach 21105 := rs (se 2 (by rfl) ⟨7914, by rfl⟩) (B 15829 (by norm_num) ⟨7914, by rfl⟩ (by norm_num))
theorem R21109 : Reach 21109 := rs (se 5 (by rfl) ⟨989, by rfl⟩) (B 1979 (by norm_num) ⟨989, by rfl⟩ (by norm_num))
theorem R21113 : Reach 21113 := rs (se 2 (by rfl) ⟨7917, by rfl⟩) (B 15835 (by norm_num) ⟨7917, by rfl⟩ (by norm_num))
theorem R21117 : Reach 21117 := rs (se 3 (by rfl) ⟨3959, by rfl⟩) (B 7919 (by norm_num) ⟨3959, by rfl⟩ (by norm_num))
theorem R21121 : Reach 21121 := rs (se 2 (by rfl) ⟨7920, by rfl⟩) (B 15841 (by norm_num) ⟨7920, by rfl⟩ (by norm_num))
theorem R21125 : Reach 21125 := rs (se 4 (by rfl) ⟨1980, by rfl⟩) (B 3961 (by norm_num) ⟨1980, by rfl⟩ (by norm_num))
theorem R21129 : Reach 21129 := rs (se 2 (by rfl) ⟨7923, by rfl⟩) (B 15847 (by norm_num) ⟨7923, by rfl⟩ (by norm_num))
theorem R21133 : Reach 21133 := rs (se 3 (by rfl) ⟨3962, by rfl⟩) (B 7925 (by norm_num) ⟨3962, by rfl⟩ (by norm_num))
theorem R21137 : Reach 21137 := rs (se 2 (by rfl) ⟨7926, by rfl⟩) (B 15853 (by norm_num) ⟨7926, by rfl⟩ (by norm_num))
theorem R21141 : Reach 21141 := rs (se 6 (by rfl) ⟨495, by rfl⟩) (B 991 (by norm_num) ⟨495, by rfl⟩ (by norm_num))
theorem R21145 : Reach 21145 := rs (se 2 (by rfl) ⟨7929, by rfl⟩) (B 15859 (by norm_num) ⟨7929, by rfl⟩ (by norm_num))
theorem R21149 : Reach 21149 := rs (se 3 (by rfl) ⟨3965, by rfl⟩) (B 7931 (by norm_num) ⟨3965, by rfl⟩ (by norm_num))
theorem R21153 : Reach 21153 := rs (se 2 (by rfl) ⟨7932, by rfl⟩) (B 15865 (by norm_num) ⟨7932, by rfl⟩ (by norm_num))
theorem R21157 : Reach 21157 := rs (se 4 (by rfl) ⟨1983, by rfl⟩) (B 3967 (by norm_num) ⟨1983, by rfl⟩ (by norm_num))
theorem R21161 : Reach 21161 := rs (se 2 (by rfl) ⟨7935, by rfl⟩) (B 15871 (by norm_num) ⟨7935, by rfl⟩ (by norm_num))
theorem R21165 : Reach 21165 := rs (se 3 (by rfl) ⟨3968, by rfl⟩) (B 7937 (by norm_num) ⟨3968, by rfl⟩ (by norm_num))
theorem R21169 : Reach 21169 := rs (se 2 (by rfl) ⟨7938, by rfl⟩) (B 15877 (by norm_num) ⟨7938, by rfl⟩ (by norm_num))
theorem R21173 : Reach 21173 := rs (se 5 (by rfl) ⟨992, by rfl⟩) (B 1985 (by norm_num) ⟨992, by rfl⟩ (by norm_num))
theorem R21177 : Reach 21177 := rs (se 2 (by rfl) ⟨7941, by rfl⟩) (B 15883 (by norm_num) ⟨7941, by rfl⟩ (by norm_num))
theorem R21181 : Reach 21181 := rs (se 3 (by rfl) ⟨3971, by rfl⟩) (B 7943 (by norm_num) ⟨3971, by rfl⟩ (by norm_num))
theorem R21185 : Reach 21185 := rs (se 2 (by rfl) ⟨7944, by rfl⟩) (B 15889 (by norm_num) ⟨7944, by rfl⟩ (by norm_num))
theorem R21189 : Reach 21189 := rs (se 4 (by rfl) ⟨1986, by rfl⟩) (B 3973 (by norm_num) ⟨1986, by rfl⟩ (by norm_num))
theorem R21193 : Reach 21193 := rs (se 2 (by rfl) ⟨7947, by rfl⟩) (B 15895 (by norm_num) ⟨7947, by rfl⟩ (by norm_num))
theorem R21197 : Reach 21197 := rs (se 3 (by rfl) ⟨3974, by rfl⟩) (B 7949 (by norm_num) ⟨3974, by rfl⟩ (by norm_num))
theorem R21201 : Reach 21201 := rs (se 2 (by rfl) ⟨7950, by rfl⟩) (B 15901 (by norm_num) ⟨7950, by rfl⟩ (by norm_num))
theorem R21205 : Reach 21205 := rs (se 7 (by rfl) ⟨248, by rfl⟩) (B 497 (by norm_num) ⟨248, by rfl⟩ (by norm_num))
theorem R21209 : Reach 21209 := rs (se 2 (by rfl) ⟨7953, by rfl⟩) (B 15907 (by norm_num) ⟨7953, by rfl⟩ (by norm_num))
theorem R21213 : Reach 21213 := rs (se 3 (by rfl) ⟨3977, by rfl⟩) (B 7955 (by norm_num) ⟨3977, by rfl⟩ (by norm_num))
theorem R21217 : Reach 21217 := rs (se 2 (by rfl) ⟨7956, by rfl⟩) (B 15913 (by norm_num) ⟨7956, by rfl⟩ (by norm_num))
theorem R21221 : Reach 21221 := rs (se 4 (by rfl) ⟨1989, by rfl⟩) (B 3979 (by norm_num) ⟨1989, by rfl⟩ (by norm_num))
theorem R21225 : Reach 21225 := rs (se 2 (by rfl) ⟨7959, by rfl⟩) (B 15919 (by norm_num) ⟨7959, by rfl⟩ (by norm_num))
theorem R21229 : Reach 21229 := rs (se 3 (by rfl) ⟨3980, by rfl⟩) (B 7961 (by norm_num) ⟨3980, by rfl⟩ (by norm_num))
theorem R21233 : Reach 21233 := rs (se 2 (by rfl) ⟨7962, by rfl⟩) (B 15925 (by norm_num) ⟨7962, by rfl⟩ (by norm_num))
theorem R21237 : Reach 21237 := rs (se 5 (by rfl) ⟨995, by rfl⟩) (B 1991 (by norm_num) ⟨995, by rfl⟩ (by norm_num))
theorem R21241 : Reach 21241 := rs (se 2 (by rfl) ⟨7965, by rfl⟩) (B 15931 (by norm_num) ⟨7965, by rfl⟩ (by norm_num))
theorem R21245 : Reach 21245 := rs (se 3 (by rfl) ⟨3983, by rfl⟩) (B 7967 (by norm_num) ⟨3983, by rfl⟩ (by norm_num))
theorem R21249 : Reach 21249 := rs (se 2 (by rfl) ⟨7968, by rfl⟩) (B 15937 (by norm_num) ⟨7968, by rfl⟩ (by norm_num))
theorem R21253 : Reach 21253 := rs (se 4 (by rfl) ⟨1992, by rfl⟩) (B 3985 (by norm_num) ⟨1992, by rfl⟩ (by norm_num))
theorem R21257 : Reach 21257 := rs (se 2 (by rfl) ⟨7971, by rfl⟩) (B 15943 (by norm_num) ⟨7971, by rfl⟩ (by norm_num))
theorem R21261 : Reach 21261 := rs (se 3 (by rfl) ⟨3986, by rfl⟩) (B 7973 (by norm_num) ⟨3986, by rfl⟩ (by norm_num))
theorem R21265 : Reach 21265 := rs (se 2 (by rfl) ⟨7974, by rfl⟩) (B 15949 (by norm_num) ⟨7974, by rfl⟩ (by norm_num))
theorem R21269 : Reach 21269 := rs (se 6 (by rfl) ⟨498, by rfl⟩) (B 997 (by norm_num) ⟨498, by rfl⟩ (by norm_num))
theorem R21273 : Reach 21273 := rs (se 2 (by rfl) ⟨7977, by rfl⟩) (B 15955 (by norm_num) ⟨7977, by rfl⟩ (by norm_num))
theorem R21277 : Reach 21277 := rs (se 3 (by rfl) ⟨3989, by rfl⟩) (B 7979 (by norm_num) ⟨3989, by rfl⟩ (by norm_num))
theorem R21281 : Reach 21281 := rs (se 2 (by rfl) ⟨7980, by rfl⟩) (B 15961 (by norm_num) ⟨7980, by rfl⟩ (by norm_num))
theorem R21285 : Reach 21285 := rs (se 4 (by rfl) ⟨1995, by rfl⟩) (B 3991 (by norm_num) ⟨1995, by rfl⟩ (by norm_num))
theorem R54053 : Reach 54053 := rs (se 4 (by rfl) ⟨5067, by rfl⟩) (B 10135 (by norm_num) ⟨5067, by rfl⟩ (by norm_num))
theorem R21289 : Reach 21289 := rs (se 2 (by rfl) ⟨7983, by rfl⟩) (B 15967 (by norm_num) ⟨7983, by rfl⟩ (by norm_num))
theorem R21293 : Reach 21293 := rs (se 3 (by rfl) ⟨3992, by rfl⟩) (B 7985 (by norm_num) ⟨3992, by rfl⟩ (by norm_num))
theorem R21297 : Reach 21297 := rs (se 2 (by rfl) ⟨7986, by rfl⟩) (B 15973 (by norm_num) ⟨7986, by rfl⟩ (by norm_num))
theorem R21301 : Reach 21301 := rs (se 5 (by rfl) ⟨998, by rfl⟩) (B 1997 (by norm_num) ⟨998, by rfl⟩ (by norm_num))
theorem R21305 : Reach 21305 := rs (se 2 (by rfl) ⟨7989, by rfl⟩) (B 15979 (by norm_num) ⟨7989, by rfl⟩ (by norm_num))
theorem R21309 : Reach 21309 := rs (se 3 (by rfl) ⟨3995, by rfl⟩) (B 7991 (by norm_num) ⟨3995, by rfl⟩ (by norm_num))
theorem R21313 : Reach 21313 := rs (se 2 (by rfl) ⟨7992, by rfl⟩) (B 15985 (by norm_num) ⟨7992, by rfl⟩ (by norm_num))
theorem R21317 : Reach 21317 := rs (se 4 (by rfl) ⟨1998, by rfl⟩) (B 3997 (by norm_num) ⟨1998, by rfl⟩ (by norm_num))
theorem R21321 : Reach 21321 := rs (se 2 (by rfl) ⟨7995, by rfl⟩) (B 15991 (by norm_num) ⟨7995, by rfl⟩ (by norm_num))
theorem R21325 : Reach 21325 := rs (se 3 (by rfl) ⟨3998, by rfl⟩) (B 7997 (by norm_num) ⟨3998, by rfl⟩ (by norm_num))
theorem R21329 : Reach 21329 := rs (se 2 (by rfl) ⟨7998, by rfl⟩) (B 15997 (by norm_num) ⟨7998, by rfl⟩ (by norm_num))
theorem R54101 : Reach 54101 := rs (se 9 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R21333 : Reach 21333 := rs (se 9 (by rfl) ⟨62, by rfl⟩) (B 125 (by norm_num) ⟨62, by rfl⟩ (by norm_num))
theorem R21337 : Reach 21337 := rs (se 2 (by rfl) ⟨8001, by rfl⟩) (B 16003 (by norm_num) ⟨8001, by rfl⟩ (by norm_num))
theorem R21341 : Reach 21341 := rs (se 3 (by rfl) ⟨4001, by rfl⟩) (B 8003 (by norm_num) ⟨4001, by rfl⟩ (by norm_num))
theorem R21345 : Reach 21345 := rs (se 2 (by rfl) ⟨8004, by rfl⟩) (B 16009 (by norm_num) ⟨8004, by rfl⟩ (by norm_num))
theorem R21349 : Reach 21349 := rs (se 4 (by rfl) ⟨2001, by rfl⟩) (B 4003 (by norm_num) ⟨2001, by rfl⟩ (by norm_num))
theorem R21353 : Reach 21353 := rs (se 2 (by rfl) ⟨8007, by rfl⟩) (B 16015 (by norm_num) ⟨8007, by rfl⟩ (by norm_num))
theorem R21357 : Reach 21357 := rs (se 3 (by rfl) ⟨4004, by rfl⟩) (B 8009 (by norm_num) ⟨4004, by rfl⟩ (by norm_num))
theorem R21361 : Reach 21361 := rs (se 2 (by rfl) ⟨8010, by rfl⟩) (B 16021 (by norm_num) ⟨8010, by rfl⟩ (by norm_num))
theorem R21365 : Reach 21365 := rs (se 5 (by rfl) ⟨1001, by rfl⟩) (B 2003 (by norm_num) ⟨1001, by rfl⟩ (by norm_num))
theorem R21369 : Reach 21369 := rs (se 2 (by rfl) ⟨8013, by rfl⟩) (B 16027 (by norm_num) ⟨8013, by rfl⟩ (by norm_num))
theorem R21373 : Reach 21373 := rs (se 3 (by rfl) ⟨4007, by rfl⟩) (B 8015 (by norm_num) ⟨4007, by rfl⟩ (by norm_num))
theorem R21377 : Reach 21377 := rs (se 2 (by rfl) ⟨8016, by rfl⟩) (B 16033 (by norm_num) ⟨8016, by rfl⟩ (by norm_num))
theorem R21381 : Reach 21381 := rs (se 4 (by rfl) ⟨2004, by rfl⟩) (B 4009 (by norm_num) ⟨2004, by rfl⟩ (by norm_num))
theorem R21385 : Reach 21385 := rs (se 2 (by rfl) ⟨8019, by rfl⟩) (B 16039 (by norm_num) ⟨8019, by rfl⟩ (by norm_num))
theorem R21389 : Reach 21389 := rs (se 3 (by rfl) ⟨4010, by rfl⟩) (B 8021 (by norm_num) ⟨4010, by rfl⟩ (by norm_num))
theorem R21393 : Reach 21393 := rs (se 2 (by rfl) ⟨8022, by rfl⟩) (B 16045 (by norm_num) ⟨8022, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R21397 : Reach 21397 := rs (se 6 (by rfl) ⟨501, by rfl⟩) (B 1003 (by norm_num) ⟨501, by rfl⟩ (by norm_num))
theorem R21401 : Reach 21401 := rs (se 2 (by rfl) ⟨8025, by rfl⟩) (B 16051 (by norm_num) ⟨8025, by rfl⟩ (by norm_num))
theorem R21405 : Reach 21405 := rs (se 3 (by rfl) ⟨4013, by rfl⟩) (B 8027 (by norm_num) ⟨4013, by rfl⟩ (by norm_num))
theorem R21409 : Reach 21409 := rs (se 2 (by rfl) ⟨8028, by rfl⟩) (B 16057 (by norm_num) ⟨8028, by rfl⟩ (by norm_num))
theorem R21413 : Reach 21413 := rs (se 4 (by rfl) ⟨2007, by rfl⟩) (B 4015 (by norm_num) ⟨2007, by rfl⟩ (by norm_num))
theorem R21417 : Reach 21417 := rs (se 2 (by rfl) ⟨8031, by rfl⟩) (B 16063 (by norm_num) ⟨8031, by rfl⟩ (by norm_num))
theorem R21421 : Reach 21421 := rs (se 3 (by rfl) ⟨4016, by rfl⟩) (B 8033 (by norm_num) ⟨4016, by rfl⟩ (by norm_num))
theorem R21425 : Reach 21425 := rs (se 2 (by rfl) ⟨8034, by rfl⟩) (B 16069 (by norm_num) ⟨8034, by rfl⟩ (by norm_num))
theorem R21429 : Reach 21429 := rs (se 5 (by rfl) ⟨1004, by rfl⟩) (B 2009 (by norm_num) ⟨1004, by rfl⟩ (by norm_num))
theorem R54197 : Reach 54197 := rs (se 5 (by rfl) ⟨2540, by rfl⟩) (B 5081 (by norm_num) ⟨2540, by rfl⟩ (by norm_num))
theorem R21433 : Reach 21433 := rs (se 2 (by rfl) ⟨8037, by rfl⟩) (B 16075 (by norm_num) ⟨8037, by rfl⟩ (by norm_num))
theorem R21437 : Reach 21437 := rs (se 3 (by rfl) ⟨4019, by rfl⟩) (B 8039 (by norm_num) ⟨4019, by rfl⟩ (by norm_num))
theorem R21441 : Reach 21441 := rs (se 2 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R21445 : Reach 21445 := rs (se 4 (by rfl) ⟨2010, by rfl⟩) (B 4021 (by norm_num) ⟨2010, by rfl⟩ (by norm_num))
theorem R21449 : Reach 21449 := rs (se 2 (by rfl) ⟨8043, by rfl⟩) (B 16087 (by norm_num) ⟨8043, by rfl⟩ (by norm_num))
theorem R21453 : Reach 21453 := rs (se 3 (by rfl) ⟨4022, by rfl⟩) (B 8045 (by norm_num) ⟨4022, by rfl⟩ (by norm_num))
theorem R21457 : Reach 21457 := rs (se 2 (by rfl) ⟨8046, by rfl⟩) (B 16093 (by norm_num) ⟨8046, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R54229 : Reach 54229 := rs (se 7 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R21461 : Reach 21461 := rs (se 7 (by rfl) ⟨251, by rfl⟩) (B 503 (by norm_num) ⟨251, by rfl⟩ (by norm_num))
theorem R21465 : Reach 21465 := rs (se 2 (by rfl) ⟨8049, by rfl⟩) (B 16099 (by norm_num) ⟨8049, by rfl⟩ (by norm_num))
theorem R21469 : Reach 21469 := rs (se 3 (by rfl) ⟨4025, by rfl⟩) (B 8051 (by norm_num) ⟨4025, by rfl⟩ (by norm_num))
theorem R21473 : Reach 21473 := rs (se 2 (by rfl) ⟨8052, by rfl⟩) (B 16105 (by norm_num) ⟨8052, by rfl⟩ (by norm_num))
theorem R21477 : Reach 21477 := rs (se 4 (by rfl) ⟨2013, by rfl⟩) (B 4027 (by norm_num) ⟨2013, by rfl⟩ (by norm_num))
theorem R54245 : Reach 54245 := rs (se 4 (by rfl) ⟨5085, by rfl⟩) (B 10171 (by norm_num) ⟨5085, by rfl⟩ (by norm_num))
theorem R21481 : Reach 21481 := rs (se 2 (by rfl) ⟨8055, by rfl⟩) (B 16111 (by norm_num) ⟨8055, by rfl⟩ (by norm_num))
theorem R21485 : Reach 21485 := rs (se 3 (by rfl) ⟨4028, by rfl⟩) (B 8057 (by norm_num) ⟨4028, by rfl⟩ (by norm_num))
theorem R21489 : Reach 21489 := rs (se 2 (by rfl) ⟨8058, by rfl⟩) (B 16117 (by norm_num) ⟨8058, by rfl⟩ (by norm_num))
theorem R21493 : Reach 21493 := rs (se 5 (by rfl) ⟨1007, by rfl⟩) (B 2015 (by norm_num) ⟨1007, by rfl⟩ (by norm_num))
theorem R21497 : Reach 21497 := rs (se 2 (by rfl) ⟨8061, by rfl⟩) (B 16123 (by norm_num) ⟨8061, by rfl⟩ (by norm_num))
theorem R21501 : Reach 21501 := rs (se 3 (by rfl) ⟨4031, by rfl⟩) (B 8063 (by norm_num) ⟨4031, by rfl⟩ (by norm_num))
theorem R21505 : Reach 21505 := rs (se 2 (by rfl) ⟨8064, by rfl⟩) (B 16129 (by norm_num) ⟨8064, by rfl⟩ (by norm_num))
theorem R21509 : Reach 21509 := rs (se 4 (by rfl) ⟨2016, by rfl⟩) (B 4033 (by norm_num) ⟨2016, by rfl⟩ (by norm_num))
theorem R21513 : Reach 21513 := rs (se 2 (by rfl) ⟨8067, by rfl⟩) (B 16135 (by norm_num) ⟨8067, by rfl⟩ (by norm_num))
theorem R21517 : Reach 21517 := rs (se 3 (by rfl) ⟨4034, by rfl⟩) (B 8069 (by norm_num) ⟨4034, by rfl⟩ (by norm_num))
theorem R21521 : Reach 21521 := rs (se 2 (by rfl) ⟨8070, by rfl⟩) (B 16141 (by norm_num) ⟨8070, by rfl⟩ (by norm_num))
theorem R21525 : Reach 21525 := rs (se 6 (by rfl) ⟨504, by rfl⟩) (B 1009 (by norm_num) ⟨504, by rfl⟩ (by norm_num))
theorem R21529 : Reach 21529 := rs (se 2 (by rfl) ⟨8073, by rfl⟩) (B 16147 (by norm_num) ⟨8073, by rfl⟩ (by norm_num))
theorem R21533 : Reach 21533 := rs (se 3 (by rfl) ⟨4037, by rfl⟩) (B 8075 (by norm_num) ⟨4037, by rfl⟩ (by norm_num))
theorem R21537 : Reach 21537 := rs (se 2 (by rfl) ⟨8076, by rfl⟩) (B 16153 (by norm_num) ⟨8076, by rfl⟩ (by norm_num))
theorem R21541 : Reach 21541 := rs (se 4 (by rfl) ⟨2019, by rfl⟩) (B 4039 (by norm_num) ⟨2019, by rfl⟩ (by norm_num))
theorem R21545 : Reach 21545 := rs (se 2 (by rfl) ⟨8079, by rfl⟩) (B 16159 (by norm_num) ⟨8079, by rfl⟩ (by norm_num))
theorem R21549 : Reach 21549 := rs (se 3 (by rfl) ⟨4040, by rfl⟩) (B 8081 (by norm_num) ⟨4040, by rfl⟩ (by norm_num))
theorem R21553 : Reach 21553 := rs (se 2 (by rfl) ⟨8082, by rfl⟩) (B 16165 (by norm_num) ⟨8082, by rfl⟩ (by norm_num))
theorem R21557 : Reach 21557 := rs (se 5 (by rfl) ⟨1010, by rfl⟩) (B 2021 (by norm_num) ⟨1010, by rfl⟩ (by norm_num))
theorem R21561 : Reach 21561 := rs (se 2 (by rfl) ⟨8085, by rfl⟩) (B 16171 (by norm_num) ⟨8085, by rfl⟩ (by norm_num))
theorem R21565 : Reach 21565 := rs (se 3 (by rfl) ⟨4043, by rfl⟩) (B 8087 (by norm_num) ⟨4043, by rfl⟩ (by norm_num))
theorem R21569 : Reach 21569 := rs (se 2 (by rfl) ⟨8088, by rfl⟩) (B 16177 (by norm_num) ⟨8088, by rfl⟩ (by norm_num))
theorem R54341 : Reach 54341 := rs (se 4 (by rfl) ⟨5094, by rfl⟩) (B 10189 (by norm_num) ⟨5094, by rfl⟩ (by norm_num))
theorem R21573 : Reach 21573 := rs (se 4 (by rfl) ⟨2022, by rfl⟩) (B 4045 (by norm_num) ⟨2022, by rfl⟩ (by norm_num))
theorem R21577 : Reach 21577 := rs (se 2 (by rfl) ⟨8091, by rfl⟩) (B 16183 (by norm_num) ⟨8091, by rfl⟩ (by norm_num))
theorem R21581 : Reach 21581 := rs (se 3 (by rfl) ⟨4046, by rfl⟩) (B 8093 (by norm_num) ⟨4046, by rfl⟩ (by norm_num))
theorem R21585 : Reach 21585 := rs (se 2 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R21589 : Reach 21589 := rs (se 8 (by rfl) ⟨126, by rfl⟩) (B 253 (by norm_num) ⟨126, by rfl⟩ (by norm_num))
theorem R21593 : Reach 21593 := rs (se 2 (by rfl) ⟨8097, by rfl⟩) (B 16195 (by norm_num) ⟨8097, by rfl⟩ (by norm_num))
theorem R21597 : Reach 21597 := rs (se 3 (by rfl) ⟨4049, by rfl⟩) (B 8099 (by norm_num) ⟨4049, by rfl⟩ (by norm_num))
theorem R21601 : Reach 21601 := rs (se 2 (by rfl) ⟨8100, by rfl⟩) (B 16201 (by norm_num) ⟨8100, by rfl⟩ (by norm_num))
theorem R21605 : Reach 21605 := rs (se 4 (by rfl) ⟨2025, by rfl⟩) (B 4051 (by norm_num) ⟨2025, by rfl⟩ (by norm_num))
theorem R21609 : Reach 21609 := rs (se 2 (by rfl) ⟨8103, by rfl⟩) (B 16207 (by norm_num) ⟨8103, by rfl⟩ (by norm_num))
theorem R21613 : Reach 21613 := rs (se 3 (by rfl) ⟨4052, by rfl⟩) (B 8105 (by norm_num) ⟨4052, by rfl⟩ (by norm_num))
theorem R21617 : Reach 21617 := rs (se 2 (by rfl) ⟨8106, by rfl⟩) (B 16213 (by norm_num) ⟨8106, by rfl⟩ (by norm_num))
theorem R21621 : Reach 21621 := rs (se 5 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R21625 : Reach 21625 := rs (se 2 (by rfl) ⟨8109, by rfl⟩) (B 16219 (by norm_num) ⟨8109, by rfl⟩ (by norm_num))
theorem R21629 : Reach 21629 := rs (se 3 (by rfl) ⟨4055, by rfl⟩) (B 8111 (by norm_num) ⟨4055, by rfl⟩ (by norm_num))
theorem R21633 : Reach 21633 := rs (se 2 (by rfl) ⟨8112, by rfl⟩) (B 16225 (by norm_num) ⟨8112, by rfl⟩ (by norm_num))
theorem R21637 : Reach 21637 := rs (se 4 (by rfl) ⟨2028, by rfl⟩) (B 4057 (by norm_num) ⟨2028, by rfl⟩ (by norm_num))
theorem R21641 : Reach 21641 := rs (se 2 (by rfl) ⟨8115, by rfl⟩) (B 16231 (by norm_num) ⟨8115, by rfl⟩ (by norm_num))
theorem R21645 : Reach 21645 := rs (se 3 (by rfl) ⟨4058, by rfl⟩) (B 8117 (by norm_num) ⟨4058, by rfl⟩ (by norm_num))
theorem R21649 : Reach 21649 := rs (se 2 (by rfl) ⟨8118, by rfl⟩) (B 16237 (by norm_num) ⟨8118, by rfl⟩ (by norm_num))
theorem R21653 : Reach 21653 := rs (se 6 (by rfl) ⟨507, by rfl⟩) (B 1015 (by norm_num) ⟨507, by rfl⟩ (by norm_num))
theorem R21657 : Reach 21657 := rs (se 2 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R21661 : Reach 21661 := rs (se 3 (by rfl) ⟨4061, by rfl⟩) (B 8123 (by norm_num) ⟨4061, by rfl⟩ (by norm_num))
theorem R21665 : Reach 21665 := rs (se 2 (by rfl) ⟨8124, by rfl⟩) (B 16249 (by norm_num) ⟨8124, by rfl⟩ (by norm_num))
theorem R21669 : Reach 21669 := rs (se 4 (by rfl) ⟨2031, by rfl⟩) (B 4063 (by norm_num) ⟨2031, by rfl⟩ (by norm_num))
theorem R21673 : Reach 21673 := rs (se 2 (by rfl) ⟨8127, by rfl⟩) (B 16255 (by norm_num) ⟨8127, by rfl⟩ (by norm_num))
theorem R21677 : Reach 21677 := rs (se 3 (by rfl) ⟨4064, by rfl⟩) (B 8129 (by norm_num) ⟨4064, by rfl⟩ (by norm_num))
theorem R21681 : Reach 21681 := rs (se 2 (by rfl) ⟨8130, by rfl⟩) (B 16261 (by norm_num) ⟨8130, by rfl⟩ (by norm_num))
theorem R21685 : Reach 21685 := rs (se 5 (by rfl) ⟨1016, by rfl⟩) (B 2033 (by norm_num) ⟨1016, by rfl⟩ (by norm_num))
theorem R21689 : Reach 21689 := rs (se 2 (by rfl) ⟨8133, by rfl⟩) (B 16267 (by norm_num) ⟨8133, by rfl⟩ (by norm_num))
theorem R21693 : Reach 21693 := rs (se 3 (by rfl) ⟨4067, by rfl⟩) (B 8135 (by norm_num) ⟨4067, by rfl⟩ (by norm_num))
theorem R21697 : Reach 21697 := rs (se 2 (by rfl) ⟨8136, by rfl⟩) (B 16273 (by norm_num) ⟨8136, by rfl⟩ (by norm_num))
theorem R21701 : Reach 21701 := rs (se 4 (by rfl) ⟨2034, by rfl⟩) (B 4069 (by norm_num) ⟨2034, by rfl⟩ (by norm_num))
theorem R21705 : Reach 21705 := rs (se 2 (by rfl) ⟨8139, by rfl⟩) (B 16279 (by norm_num) ⟨8139, by rfl⟩ (by norm_num))
theorem R21709 : Reach 21709 := rs (se 3 (by rfl) ⟨4070, by rfl⟩) (B 8141 (by norm_num) ⟨4070, by rfl⟩ (by norm_num))
theorem R21713 : Reach 21713 := rs (se 2 (by rfl) ⟨8142, by rfl⟩) (B 16285 (by norm_num) ⟨8142, by rfl⟩ (by norm_num))
theorem R21717 : Reach 21717 := rs (se 7 (by rfl) ⟨254, by rfl⟩) (B 509 (by norm_num) ⟨254, by rfl⟩ (by norm_num))
theorem R21721 : Reach 21721 := rs (se 2 (by rfl) ⟨8145, by rfl⟩) (B 16291 (by norm_num) ⟨8145, by rfl⟩ (by norm_num))
theorem R21725 : Reach 21725 := rs (se 3 (by rfl) ⟨4073, by rfl⟩) (B 8147 (by norm_num) ⟨4073, by rfl⟩ (by norm_num))
theorem R21729 : Reach 21729 := rs (se 2 (by rfl) ⟨8148, by rfl⟩) (B 16297 (by norm_num) ⟨8148, by rfl⟩ (by norm_num))
theorem R21733 : Reach 21733 := rs (se 4 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R21737 : Reach 21737 := rs (se 2 (by rfl) ⟨8151, by rfl⟩) (B 16303 (by norm_num) ⟨8151, by rfl⟩ (by norm_num))
theorem R21741 : Reach 21741 := rs (se 3 (by rfl) ⟨4076, by rfl⟩) (B 8153 (by norm_num) ⟨4076, by rfl⟩ (by norm_num))
theorem R21745 : Reach 21745 := rs (se 2 (by rfl) ⟨8154, by rfl⟩) (B 16309 (by norm_num) ⟨8154, by rfl⟩ (by norm_num))
theorem R21749 : Reach 21749 := rs (se 5 (by rfl) ⟨1019, by rfl⟩) (B 2039 (by norm_num) ⟨1019, by rfl⟩ (by norm_num))
theorem R21753 : Reach 21753 := rs (se 2 (by rfl) ⟨8157, by rfl⟩) (B 16315 (by norm_num) ⟨8157, by rfl⟩ (by norm_num))
theorem R21757 : Reach 21757 := rs (se 3 (by rfl) ⟨4079, by rfl⟩) (B 8159 (by norm_num) ⟨4079, by rfl⟩ (by norm_num))
theorem R21761 : Reach 21761 := rs (se 2 (by rfl) ⟨8160, by rfl⟩) (B 16321 (by norm_num) ⟨8160, by rfl⟩ (by norm_num))
theorem R54533 : Reach 54533 := rs (se 4 (by rfl) ⟨5112, by rfl⟩) (B 10225 (by norm_num) ⟨5112, by rfl⟩ (by norm_num))
theorem R21765 : Reach 21765 := rs (se 4 (by rfl) ⟨2040, by rfl⟩) (B 4081 (by norm_num) ⟨2040, by rfl⟩ (by norm_num))
theorem R21769 : Reach 21769 := rs (se 2 (by rfl) ⟨8163, by rfl⟩) (B 16327 (by norm_num) ⟨8163, by rfl⟩ (by norm_num))
theorem R21773 : Reach 21773 := rs (se 3 (by rfl) ⟨4082, by rfl⟩) (B 8165 (by norm_num) ⟨4082, by rfl⟩ (by norm_num))
theorem R21777 : Reach 21777 := rs (se 2 (by rfl) ⟨8166, by rfl⟩) (B 16333 (by norm_num) ⟨8166, by rfl⟩ (by norm_num))
theorem R21781 : Reach 21781 := rs (se 6 (by rfl) ⟨510, by rfl⟩) (B 1021 (by norm_num) ⟨510, by rfl⟩ (by norm_num))
theorem R21785 : Reach 21785 := rs (se 2 (by rfl) ⟨8169, by rfl⟩) (B 16339 (by norm_num) ⟨8169, by rfl⟩ (by norm_num))
theorem R21789 : Reach 21789 := rs (se 3 (by rfl) ⟨4085, by rfl⟩) (B 8171 (by norm_num) ⟨4085, by rfl⟩ (by norm_num))
theorem R21793 : Reach 21793 := rs (se 2 (by rfl) ⟨8172, by rfl⟩) (B 16345 (by norm_num) ⟨8172, by rfl⟩ (by norm_num))
theorem R21797 : Reach 21797 := rs (se 4 (by rfl) ⟨2043, by rfl⟩) (B 4087 (by norm_num) ⟨2043, by rfl⟩ (by norm_num))
theorem R21801 : Reach 21801 := rs (se 2 (by rfl) ⟨8175, by rfl⟩) (B 16351 (by norm_num) ⟨8175, by rfl⟩ (by norm_num))
theorem R21805 : Reach 21805 := rs (se 3 (by rfl) ⟨4088, by rfl⟩) (B 8177 (by norm_num) ⟨4088, by rfl⟩ (by norm_num))
theorem R21809 : Reach 21809 := rs (se 2 (by rfl) ⟨8178, by rfl⟩) (B 16357 (by norm_num) ⟨8178, by rfl⟩ (by norm_num))
theorem R21813 : Reach 21813 := rs (se 5 (by rfl) ⟨1022, by rfl⟩) (B 2045 (by norm_num) ⟨1022, by rfl⟩ (by norm_num))
theorem R21817 : Reach 21817 := rs (se 2 (by rfl) ⟨8181, by rfl⟩) (B 16363 (by norm_num) ⟨8181, by rfl⟩ (by norm_num))
theorem R21821 : Reach 21821 := rs (se 3 (by rfl) ⟨4091, by rfl⟩) (B 8183 (by norm_num) ⟨4091, by rfl⟩ (by norm_num))
theorem R21825 : Reach 21825 := rs (se 2 (by rfl) ⟨8184, by rfl⟩) (B 16369 (by norm_num) ⟨8184, by rfl⟩ (by norm_num))
theorem R21829 : Reach 21829 := rs (se 4 (by rfl) ⟨2046, by rfl⟩) (B 4093 (by norm_num) ⟨2046, by rfl⟩ (by norm_num))
theorem R21833 : Reach 21833 := rs (se 2 (by rfl) ⟨8187, by rfl⟩) (B 16375 (by norm_num) ⟨8187, by rfl⟩ (by norm_num))
theorem R21837 : Reach 21837 := rs (se 3 (by rfl) ⟨4094, by rfl⟩) (B 8189 (by norm_num) ⟨4094, by rfl⟩ (by norm_num))
theorem R21841 : Reach 21841 := rs (se 2 (by rfl) ⟨8190, by rfl⟩) (B 16381 (by norm_num) ⟨8190, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R21845 : Reach 21845 := rs (se 16 (by rfl) ⟨0, by rfl⟩) (B 1 (by norm_num) ⟨0, by rfl⟩ (by norm_num))
theorem R21849 : Reach 21849 := rs (se 2 (by rfl) ⟨8193, by rfl⟩) (B 16387 (by norm_num) ⟨8193, by rfl⟩ (by norm_num))
theorem R21853 : Reach 21853 := rs (se 3 (by rfl) ⟨4097, by rfl⟩) (B 8195 (by norm_num) ⟨4097, by rfl⟩ (by norm_num))
theorem R21857 : Reach 21857 := rs (se 2 (by rfl) ⟨8196, by rfl⟩) (B 16393 (by norm_num) ⟨8196, by rfl⟩ (by norm_num))
theorem R21861 : Reach 21861 := rs (se 4 (by rfl) ⟨2049, by rfl⟩) (B 4099 (by norm_num) ⟨2049, by rfl⟩ (by norm_num))
theorem R21865 : Reach 21865 := rs (se 2 (by rfl) ⟨8199, by rfl⟩) (B 16399 (by norm_num) ⟨8199, by rfl⟩ (by norm_num))
theorem R21869 : Reach 21869 := rs (se 3 (by rfl) ⟨4100, by rfl⟩) (B 8201 (by norm_num) ⟨4100, by rfl⟩ (by norm_num))
theorem R21873 : Reach 21873 := rs (se 2 (by rfl) ⟨8202, by rfl⟩) (B 16405 (by norm_num) ⟨8202, by rfl⟩ (by norm_num))
theorem R21877 : Reach 21877 := rs (se 5 (by rfl) ⟨1025, by rfl⟩) (B 2051 (by norm_num) ⟨1025, by rfl⟩ (by norm_num))
theorem R21881 : Reach 21881 := rs (se 2 (by rfl) ⟨8205, by rfl⟩) (B 16411 (by norm_num) ⟨8205, by rfl⟩ (by norm_num))
theorem R21885 : Reach 21885 := rs (se 3 (by rfl) ⟨4103, by rfl⟩) (B 8207 (by norm_num) ⟨4103, by rfl⟩ (by norm_num))
theorem R21889 : Reach 21889 := rs (se 2 (by rfl) ⟨8208, by rfl⟩) (B 16417 (by norm_num) ⟨8208, by rfl⟩ (by norm_num))
theorem R21893 : Reach 21893 := rs (se 4 (by rfl) ⟨2052, by rfl⟩) (B 4105 (by norm_num) ⟨2052, by rfl⟩ (by norm_num))
theorem R21897 : Reach 21897 := rs (se 2 (by rfl) ⟨8211, by rfl⟩) (B 16423 (by norm_num) ⟨8211, by rfl⟩ (by norm_num))
theorem R21901 : Reach 21901 := rs (se 3 (by rfl) ⟨4106, by rfl⟩) (B 8213 (by norm_num) ⟨4106, by rfl⟩ (by norm_num))
theorem R21905 : Reach 21905 := rs (se 2 (by rfl) ⟨8214, by rfl⟩) (B 16429 (by norm_num) ⟨8214, by rfl⟩ (by norm_num))
theorem R21909 : Reach 21909 := rs (se 6 (by rfl) ⟨513, by rfl⟩) (B 1027 (by norm_num) ⟨513, by rfl⟩ (by norm_num))
theorem R21913 : Reach 21913 := rs (se 2 (by rfl) ⟨8217, by rfl⟩) (B 16435 (by norm_num) ⟨8217, by rfl⟩ (by norm_num))
theorem R21917 : Reach 21917 := rs (se 3 (by rfl) ⟨4109, by rfl⟩) (B 8219 (by norm_num) ⟨4109, by rfl⟩ (by norm_num))
theorem R21921 : Reach 21921 := rs (se 2 (by rfl) ⟨8220, by rfl⟩) (B 16441 (by norm_num) ⟨8220, by rfl⟩ (by norm_num))
theorem R21925 : Reach 21925 := rs (se 4 (by rfl) ⟨2055, by rfl⟩) (B 4111 (by norm_num) ⟨2055, by rfl⟩ (by norm_num))
theorem R21929 : Reach 21929 := rs (se 2 (by rfl) ⟨8223, by rfl⟩) (B 16447 (by norm_num) ⟨8223, by rfl⟩ (by norm_num))
theorem R21933 : Reach 21933 := rs (se 3 (by rfl) ⟨4112, by rfl⟩) (B 8225 (by norm_num) ⟨4112, by rfl⟩ (by norm_num))
theorem R21937 : Reach 21937 := rs (se 2 (by rfl) ⟨8226, by rfl⟩) (B 16453 (by norm_num) ⟨8226, by rfl⟩ (by norm_num))
theorem R21941 : Reach 21941 := rs (se 5 (by rfl) ⟨1028, by rfl⟩) (B 2057 (by norm_num) ⟨1028, by rfl⟩ (by norm_num))
theorem R21945 : Reach 21945 := rs (se 2 (by rfl) ⟨8229, by rfl⟩) (B 16459 (by norm_num) ⟨8229, by rfl⟩ (by norm_num))
theorem R21949 : Reach 21949 := rs (se 3 (by rfl) ⟨4115, by rfl⟩) (B 8231 (by norm_num) ⟨4115, by rfl⟩ (by norm_num))
theorem R21953 : Reach 21953 := rs (se 2 (by rfl) ⟨8232, by rfl⟩) (B 16465 (by norm_num) ⟨8232, by rfl⟩ (by norm_num))
theorem R21957 : Reach 21957 := rs (se 4 (by rfl) ⟨2058, by rfl⟩) (B 4117 (by norm_num) ⟨2058, by rfl⟩ (by norm_num))
theorem R21961 : Reach 21961 := rs (se 2 (by rfl) ⟨8235, by rfl⟩) (B 16471 (by norm_num) ⟨8235, by rfl⟩ (by norm_num))
theorem R21965 : Reach 21965 := rs (se 3 (by rfl) ⟨4118, by rfl⟩) (B 8237 (by norm_num) ⟨4118, by rfl⟩ (by norm_num))
theorem R21969 : Reach 21969 := rs (se 2 (by rfl) ⟨8238, by rfl⟩) (B 16477 (by norm_num) ⟨8238, by rfl⟩ (by norm_num))
theorem R21973 : Reach 21973 := rs (se 7 (by rfl) ⟨257, by rfl⟩) (B 515 (by norm_num) ⟨257, by rfl⟩ (by norm_num))
theorem R21977 : Reach 21977 := rs (se 2 (by rfl) ⟨8241, by rfl⟩) (B 16483 (by norm_num) ⟨8241, by rfl⟩ (by norm_num))
theorem R21981 : Reach 21981 := rs (se 3 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R21985 : Reach 21985 := rs (se 2 (by rfl) ⟨8244, by rfl⟩) (B 16489 (by norm_num) ⟨8244, by rfl⟩ (by norm_num))
theorem R21989 : Reach 21989 := rs (se 4 (by rfl) ⟨2061, by rfl⟩) (B 4123 (by norm_num) ⟨2061, by rfl⟩ (by norm_num))
theorem R21993 : Reach 21993 := rs (se 2 (by rfl) ⟨8247, by rfl⟩) (B 16495 (by norm_num) ⟨8247, by rfl⟩ (by norm_num))
theorem R21997 : Reach 21997 := rs (se 3 (by rfl) ⟨4124, by rfl⟩) (B 8249 (by norm_num) ⟨4124, by rfl⟩ (by norm_num))
theorem R22001 : Reach 22001 := rs (se 2 (by rfl) ⟨8250, by rfl⟩) (B 16501 (by norm_num) ⟨8250, by rfl⟩ (by norm_num))
theorem R22005 : Reach 22005 := rs (se 5 (by rfl) ⟨1031, by rfl⟩) (B 2063 (by norm_num) ⟨1031, by rfl⟩ (by norm_num))
theorem R22009 : Reach 22009 := rs (se 2 (by rfl) ⟨8253, by rfl⟩) (B 16507 (by norm_num) ⟨8253, by rfl⟩ (by norm_num))
theorem R22013 : Reach 22013 := rs (se 3 (by rfl) ⟨4127, by rfl⟩) (B 8255 (by norm_num) ⟨4127, by rfl⟩ (by norm_num))
theorem R22017 : Reach 22017 := rs (se 2 (by rfl) ⟨8256, by rfl⟩) (B 16513 (by norm_num) ⟨8256, by rfl⟩ (by norm_num))
theorem R22021 : Reach 22021 := rs (se 4 (by rfl) ⟨2064, by rfl⟩) (B 4129 (by norm_num) ⟨2064, by rfl⟩ (by norm_num))
theorem R22025 : Reach 22025 := rs (se 2 (by rfl) ⟨8259, by rfl⟩) (B 16519 (by norm_num) ⟨8259, by rfl⟩ (by norm_num))
theorem R22029 : Reach 22029 := rs (se 3 (by rfl) ⟨4130, by rfl⟩) (B 8261 (by norm_num) ⟨4130, by rfl⟩ (by norm_num))
theorem R22033 : Reach 22033 := rs (se 2 (by rfl) ⟨8262, by rfl⟩) (B 16525 (by norm_num) ⟨8262, by rfl⟩ (by norm_num))
theorem R22037 : Reach 22037 := rs (se 6 (by rfl) ⟨516, by rfl⟩) (B 1033 (by norm_num) ⟨516, by rfl⟩ (by norm_num))
theorem R22041 : Reach 22041 := rs (se 2 (by rfl) ⟨8265, by rfl⟩) (B 16531 (by norm_num) ⟨8265, by rfl⟩ (by norm_num))
theorem R22045 : Reach 22045 := rs (se 3 (by rfl) ⟨4133, by rfl⟩) (B 8267 (by norm_num) ⟨4133, by rfl⟩ (by norm_num))
theorem R22049 : Reach 22049 := rs (se 2 (by rfl) ⟨8268, by rfl⟩) (B 16537 (by norm_num) ⟨8268, by rfl⟩ (by norm_num))
theorem R22053 : Reach 22053 := rs (se 4 (by rfl) ⟨2067, by rfl⟩) (B 4135 (by norm_num) ⟨2067, by rfl⟩ (by norm_num))
theorem R22057 : Reach 22057 := rs (se 2 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R22061 : Reach 22061 := rs (se 3 (by rfl) ⟨4136, by rfl⟩) (B 8273 (by norm_num) ⟨4136, by rfl⟩ (by norm_num))
theorem R22065 : Reach 22065 := rs (se 2 (by rfl) ⟨8274, by rfl⟩) (B 16549 (by norm_num) ⟨8274, by rfl⟩ (by norm_num))
theorem R22069 : Reach 22069 := rs (se 5 (by rfl) ⟨1034, by rfl⟩) (B 2069 (by norm_num) ⟨1034, by rfl⟩ (by norm_num))
theorem R22073 : Reach 22073 := rs (se 2 (by rfl) ⟨8277, by rfl⟩) (B 16555 (by norm_num) ⟨8277, by rfl⟩ (by norm_num))
theorem R22077 : Reach 22077 := rs (se 3 (by rfl) ⟨4139, by rfl⟩) (B 8279 (by norm_num) ⟨4139, by rfl⟩ (by norm_num))
theorem R22081 : Reach 22081 := rs (se 2 (by rfl) ⟨8280, by rfl⟩) (B 16561 (by norm_num) ⟨8280, by rfl⟩ (by norm_num))
theorem R22085 : Reach 22085 := rs (se 4 (by rfl) ⟨2070, by rfl⟩) (B 4141 (by norm_num) ⟨2070, by rfl⟩ (by norm_num))
theorem R22089 : Reach 22089 := rs (se 2 (by rfl) ⟨8283, by rfl⟩) (B 16567 (by norm_num) ⟨8283, by rfl⟩ (by norm_num))
theorem R22093 : Reach 22093 := rs (se 3 (by rfl) ⟨4142, by rfl⟩) (B 8285 (by norm_num) ⟨4142, by rfl⟩ (by norm_num))
theorem R22097 : Reach 22097 := rs (se 2 (by rfl) ⟨8286, by rfl⟩) (B 16573 (by norm_num) ⟨8286, by rfl⟩ (by norm_num))
theorem R22101 : Reach 22101 := rs (se 8 (by rfl) ⟨129, by rfl⟩) (B 259 (by norm_num) ⟨129, by rfl⟩ (by norm_num))
theorem R22105 : Reach 22105 := rs (se 2 (by rfl) ⟨8289, by rfl⟩) (B 16579 (by norm_num) ⟨8289, by rfl⟩ (by norm_num))
theorem R22109 : Reach 22109 := rs (se 3 (by rfl) ⟨4145, by rfl⟩) (B 8291 (by norm_num) ⟨4145, by rfl⟩ (by norm_num))
theorem R22113 : Reach 22113 := rs (se 2 (by rfl) ⟨8292, by rfl⟩) (B 16585 (by norm_num) ⟨8292, by rfl⟩ (by norm_num))
theorem R22117 : Reach 22117 := rs (se 4 (by rfl) ⟨2073, by rfl⟩) (B 4147 (by norm_num) ⟨2073, by rfl⟩ (by norm_num))
theorem R22121 : Reach 22121 := rs (se 2 (by rfl) ⟨8295, by rfl⟩) (B 16591 (by norm_num) ⟨8295, by rfl⟩ (by norm_num))
theorem R22125 : Reach 22125 := rs (se 3 (by rfl) ⟨4148, by rfl⟩) (B 8297 (by norm_num) ⟨4148, by rfl⟩ (by norm_num))
theorem R22129 : Reach 22129 := rs (se 2 (by rfl) ⟨8298, by rfl⟩) (B 16597 (by norm_num) ⟨8298, by rfl⟩ (by norm_num))
theorem R22133 : Reach 22133 := rs (se 5 (by rfl) ⟨1037, by rfl⟩) (B 2075 (by norm_num) ⟨1037, by rfl⟩ (by norm_num))
theorem R22137 : Reach 22137 := rs (se 2 (by rfl) ⟨8301, by rfl⟩) (B 16603 (by norm_num) ⟨8301, by rfl⟩ (by norm_num))
theorem R22141 : Reach 22141 := rs (se 3 (by rfl) ⟨4151, by rfl⟩) (B 8303 (by norm_num) ⟨4151, by rfl⟩ (by norm_num))
theorem R22145 : Reach 22145 := rs (se 2 (by rfl) ⟨8304, by rfl⟩) (B 16609 (by norm_num) ⟨8304, by rfl⟩ (by norm_num))
theorem R22149 : Reach 22149 := rs (se 4 (by rfl) ⟨2076, by rfl⟩) (B 4153 (by norm_num) ⟨2076, by rfl⟩ (by norm_num))
theorem R22153 : Reach 22153 := rs (se 2 (by rfl) ⟨8307, by rfl⟩) (B 16615 (by norm_num) ⟨8307, by rfl⟩ (by norm_num))
theorem R22157 : Reach 22157 := rs (se 3 (by rfl) ⟨4154, by rfl⟩) (B 8309 (by norm_num) ⟨4154, by rfl⟩ (by norm_num))
theorem R22161 : Reach 22161 := rs (se 2 (by rfl) ⟨8310, by rfl⟩) (B 16621 (by norm_num) ⟨8310, by rfl⟩ (by norm_num))
theorem R22165 : Reach 22165 := rs (se 6 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R22169 : Reach 22169 := rs (se 2 (by rfl) ⟨8313, by rfl⟩) (B 16627 (by norm_num) ⟨8313, by rfl⟩ (by norm_num))
theorem R22173 : Reach 22173 := rs (se 3 (by rfl) ⟨4157, by rfl⟩) (B 8315 (by norm_num) ⟨4157, by rfl⟩ (by norm_num))
theorem R22177 : Reach 22177 := rs (se 2 (by rfl) ⟨8316, by rfl⟩) (B 16633 (by norm_num) ⟨8316, by rfl⟩ (by norm_num))
theorem R22181 : Reach 22181 := rs (se 4 (by rfl) ⟨2079, by rfl⟩) (B 4159 (by norm_num) ⟨2079, by rfl⟩ (by norm_num))
theorem R22185 : Reach 22185 := rs (se 2 (by rfl) ⟨8319, by rfl⟩) (B 16639 (by norm_num) ⟨8319, by rfl⟩ (by norm_num))
theorem R22189 : Reach 22189 := rs (se 3 (by rfl) ⟨4160, by rfl⟩) (B 8321 (by norm_num) ⟨4160, by rfl⟩ (by norm_num))
theorem R22193 : Reach 22193 := rs (se 2 (by rfl) ⟨8322, by rfl⟩) (B 16645 (by norm_num) ⟨8322, by rfl⟩ (by norm_num))
theorem R22197 : Reach 22197 := rs (se 5 (by rfl) ⟨1040, by rfl⟩) (B 2081 (by norm_num) ⟨1040, by rfl⟩ (by norm_num))
theorem R22201 : Reach 22201 := rs (se 2 (by rfl) ⟨8325, by rfl⟩) (B 16651 (by norm_num) ⟨8325, by rfl⟩ (by norm_num))
theorem R22205 : Reach 22205 := rs (se 3 (by rfl) ⟨4163, by rfl⟩) (B 8327 (by norm_num) ⟨4163, by rfl⟩ (by norm_num))
theorem R22209 : Reach 22209 := rs (se 2 (by rfl) ⟨8328, by rfl⟩) (B 16657 (by norm_num) ⟨8328, by rfl⟩ (by norm_num))
theorem R22213 : Reach 22213 := rs (se 4 (by rfl) ⟨2082, by rfl⟩) (B 4165 (by norm_num) ⟨2082, by rfl⟩ (by norm_num))
theorem R22217 : Reach 22217 := rs (se 2 (by rfl) ⟨8331, by rfl⟩) (B 16663 (by norm_num) ⟨8331, by rfl⟩ (by norm_num))
theorem R22221 : Reach 22221 := rs (se 3 (by rfl) ⟨4166, by rfl⟩) (B 8333 (by norm_num) ⟨4166, by rfl⟩ (by norm_num))
theorem R22225 : Reach 22225 := rs (se 2 (by rfl) ⟨8334, by rfl⟩) (B 16669 (by norm_num) ⟨8334, by rfl⟩ (by norm_num))
theorem R22229 : Reach 22229 := rs (se 7 (by rfl) ⟨260, by rfl⟩) (B 521 (by norm_num) ⟨260, by rfl⟩ (by norm_num))
theorem R22233 : Reach 22233 := rs (se 2 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R22237 : Reach 22237 := rs (se 3 (by rfl) ⟨4169, by rfl⟩) (B 8339 (by norm_num) ⟨4169, by rfl⟩ (by norm_num))
theorem R22241 : Reach 22241 := rs (se 2 (by rfl) ⟨8340, by rfl⟩) (B 16681 (by norm_num) ⟨8340, by rfl⟩ (by norm_num))
theorem R22245 : Reach 22245 := rs (se 4 (by rfl) ⟨2085, by rfl⟩) (B 4171 (by norm_num) ⟨2085, by rfl⟩ (by norm_num))
theorem R22249 : Reach 22249 := rs (se 2 (by rfl) ⟨8343, by rfl⟩) (B 16687 (by norm_num) ⟨8343, by rfl⟩ (by norm_num))
theorem R22253 : Reach 22253 := rs (se 3 (by rfl) ⟨4172, by rfl⟩) (B 8345 (by norm_num) ⟨4172, by rfl⟩ (by norm_num))
theorem R22257 : Reach 22257 := rs (se 2 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R22261 : Reach 22261 := rs (se 5 (by rfl) ⟨1043, by rfl⟩) (B 2087 (by norm_num) ⟨1043, by rfl⟩ (by norm_num))
theorem R22265 : Reach 22265 := rs (se 2 (by rfl) ⟨8349, by rfl⟩) (B 16699 (by norm_num) ⟨8349, by rfl⟩ (by norm_num))
theorem R22269 : Reach 22269 := rs (se 3 (by rfl) ⟨4175, by rfl⟩) (B 8351 (by norm_num) ⟨4175, by rfl⟩ (by norm_num))
theorem R22273 : Reach 22273 := rs (se 2 (by rfl) ⟨8352, by rfl⟩) (B 16705 (by norm_num) ⟨8352, by rfl⟩ (by norm_num))
theorem R22277 : Reach 22277 := rs (se 4 (by rfl) ⟨2088, by rfl⟩) (B 4177 (by norm_num) ⟨2088, by rfl⟩ (by norm_num))
theorem R22281 : Reach 22281 := rs (se 2 (by rfl) ⟨8355, by rfl⟩) (B 16711 (by norm_num) ⟨8355, by rfl⟩ (by norm_num))
theorem R22285 : Reach 22285 := rs (se 3 (by rfl) ⟨4178, by rfl⟩) (B 8357 (by norm_num) ⟨4178, by rfl⟩ (by norm_num))
theorem R22289 : Reach 22289 := rs (se 2 (by rfl) ⟨8358, by rfl⟩) (B 16717 (by norm_num) ⟨8358, by rfl⟩ (by norm_num))
theorem R22293 : Reach 22293 := rs (se 6 (by rfl) ⟨522, by rfl⟩) (B 1045 (by norm_num) ⟨522, by rfl⟩ (by norm_num))
theorem R22297 : Reach 22297 := rs (se 2 (by rfl) ⟨8361, by rfl⟩) (B 16723 (by norm_num) ⟨8361, by rfl⟩ (by norm_num))
theorem R22301 : Reach 22301 := rs (se 3 (by rfl) ⟨4181, by rfl⟩) (B 8363 (by norm_num) ⟨4181, by rfl⟩ (by norm_num))
theorem R22305 : Reach 22305 := rs (se 2 (by rfl) ⟨8364, by rfl⟩) (B 16729 (by norm_num) ⟨8364, by rfl⟩ (by norm_num))
theorem R22309 : Reach 22309 := rs (se 4 (by rfl) ⟨2091, by rfl⟩) (B 4183 (by norm_num) ⟨2091, by rfl⟩ (by norm_num))
theorem R22313 : Reach 22313 := rs (se 2 (by rfl) ⟨8367, by rfl⟩) (B 16735 (by norm_num) ⟨8367, by rfl⟩ (by norm_num))
theorem R22317 : Reach 22317 := rs (se 3 (by rfl) ⟨4184, by rfl⟩) (B 8369 (by norm_num) ⟨4184, by rfl⟩ (by norm_num))
theorem R22321 : Reach 22321 := rs (se 2 (by rfl) ⟨8370, by rfl⟩) (B 16741 (by norm_num) ⟨8370, by rfl⟩ (by norm_num))
theorem R22325 : Reach 22325 := rs (se 5 (by rfl) ⟨1046, by rfl⟩) (B 2093 (by norm_num) ⟨1046, by rfl⟩ (by norm_num))
theorem R22329 : Reach 22329 := rs (se 2 (by rfl) ⟨8373, by rfl⟩) (B 16747 (by norm_num) ⟨8373, by rfl⟩ (by norm_num))
theorem R22333 : Reach 22333 := rs (se 3 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R22337 : Reach 22337 := rs (se 2 (by rfl) ⟨8376, by rfl⟩) (B 16753 (by norm_num) ⟨8376, by rfl⟩ (by norm_num))
theorem R22341 : Reach 22341 := rs (se 4 (by rfl) ⟨2094, by rfl⟩) (B 4189 (by norm_num) ⟨2094, by rfl⟩ (by norm_num))
theorem R22345 : Reach 22345 := rs (se 2 (by rfl) ⟨8379, by rfl⟩) (B 16759 (by norm_num) ⟨8379, by rfl⟩ (by norm_num))
theorem R22349 : Reach 22349 := rs (se 3 (by rfl) ⟨4190, by rfl⟩) (B 8381 (by norm_num) ⟨4190, by rfl⟩ (by norm_num))
theorem R22353 : Reach 22353 := rs (se 2 (by rfl) ⟨8382, by rfl⟩) (B 16765 (by norm_num) ⟨8382, by rfl⟩ (by norm_num))
theorem R22357 : Reach 22357 := rs (se 9 (by rfl) ⟨65, by rfl⟩) (B 131 (by norm_num) ⟨65, by rfl⟩ (by norm_num))
theorem R22361 : Reach 22361 := rs (se 2 (by rfl) ⟨8385, by rfl⟩) (B 16771 (by norm_num) ⟨8385, by rfl⟩ (by norm_num))
theorem R22365 : Reach 22365 := rs (se 3 (by rfl) ⟨4193, by rfl⟩) (B 8387 (by norm_num) ⟨4193, by rfl⟩ (by norm_num))
theorem R22369 : Reach 22369 := rs (se 2 (by rfl) ⟨8388, by rfl⟩) (B 16777 (by norm_num) ⟨8388, by rfl⟩ (by norm_num))
theorem R22373 : Reach 22373 := rs (se 4 (by rfl) ⟨2097, by rfl⟩) (B 4195 (by norm_num) ⟨2097, by rfl⟩ (by norm_num))
theorem R22377 : Reach 22377 := rs (se 2 (by rfl) ⟨8391, by rfl⟩) (B 16783 (by norm_num) ⟨8391, by rfl⟩ (by norm_num))
theorem R22381 : Reach 22381 := rs (se 3 (by rfl) ⟨4196, by rfl⟩) (B 8393 (by norm_num) ⟨4196, by rfl⟩ (by norm_num))
theorem R22385 : Reach 22385 := rs (se 2 (by rfl) ⟨8394, by rfl⟩) (B 16789 (by norm_num) ⟨8394, by rfl⟩ (by norm_num))
theorem R87925 : Reach 87925 := rs (se 5 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R22389 : Reach 22389 := rs (se 5 (by rfl) ⟨1049, by rfl⟩) (B 2099 (by norm_num) ⟨1049, by rfl⟩ (by norm_num))
theorem R22393 : Reach 22393 := rs (se 2 (by rfl) ⟨8397, by rfl⟩) (B 16795 (by norm_num) ⟨8397, by rfl⟩ (by norm_num))
theorem R22397 : Reach 22397 := rs (se 3 (by rfl) ⟨4199, by rfl⟩) (B 8399 (by norm_num) ⟨4199, by rfl⟩ (by norm_num))
theorem R22401 : Reach 22401 := rs (se 2 (by rfl) ⟨8400, by rfl⟩) (B 16801 (by norm_num) ⟨8400, by rfl⟩ (by norm_num))
theorem R22405 : Reach 22405 := rs (se 4 (by rfl) ⟨2100, by rfl⟩) (B 4201 (by norm_num) ⟨2100, by rfl⟩ (by norm_num))
theorem R22409 : Reach 22409 := rs (se 2 (by rfl) ⟨8403, by rfl⟩) (B 16807 (by norm_num) ⟨8403, by rfl⟩ (by norm_num))
theorem R22413 : Reach 22413 := rs (se 3 (by rfl) ⟨4202, by rfl⟩) (B 8405 (by norm_num) ⟨4202, by rfl⟩ (by norm_num))
theorem R22417 : Reach 22417 := rs (se 2 (by rfl) ⟨8406, by rfl⟩) (B 16813 (by norm_num) ⟨8406, by rfl⟩ (by norm_num))
theorem R22421 : Reach 22421 := rs (se 6 (by rfl) ⟨525, by rfl⟩) (B 1051 (by norm_num) ⟨525, by rfl⟩ (by norm_num))
theorem R22425 : Reach 22425 := rs (se 2 (by rfl) ⟨8409, by rfl⟩) (B 16819 (by norm_num) ⟨8409, by rfl⟩ (by norm_num))
theorem R22429 : Reach 22429 := rs (se 3 (by rfl) ⟨4205, by rfl⟩) (B 8411 (by norm_num) ⟨4205, by rfl⟩ (by norm_num))
theorem R22433 : Reach 22433 := rs (se 2 (by rfl) ⟨8412, by rfl⟩) (B 16825 (by norm_num) ⟨8412, by rfl⟩ (by norm_num))
theorem R22437 : Reach 22437 := rs (se 4 (by rfl) ⟨2103, by rfl⟩) (B 4207 (by norm_num) ⟨2103, by rfl⟩ (by norm_num))
theorem R22441 : Reach 22441 := rs (se 2 (by rfl) ⟨8415, by rfl⟩) (B 16831 (by norm_num) ⟨8415, by rfl⟩ (by norm_num))
theorem R22445 : Reach 22445 := rs (se 3 (by rfl) ⟨4208, by rfl⟩) (B 8417 (by norm_num) ⟨4208, by rfl⟩ (by norm_num))
theorem R22449 : Reach 22449 := rs (se 2 (by rfl) ⟨8418, by rfl⟩) (B 16837 (by norm_num) ⟨8418, by rfl⟩ (by norm_num))
theorem R22453 : Reach 22453 := rs (se 5 (by rfl) ⟨1052, by rfl⟩) (B 2105 (by norm_num) ⟨1052, by rfl⟩ (by norm_num))
theorem R22457 : Reach 22457 := rs (se 2 (by rfl) ⟨8421, by rfl⟩) (B 16843 (by norm_num) ⟨8421, by rfl⟩ (by norm_num))
theorem R22461 : Reach 22461 := rs (se 3 (by rfl) ⟨4211, by rfl⟩) (B 8423 (by norm_num) ⟨4211, by rfl⟩ (by norm_num))
theorem R22465 : Reach 22465 := rs (se 2 (by rfl) ⟨8424, by rfl⟩) (B 16849 (by norm_num) ⟨8424, by rfl⟩ (by norm_num))
theorem R22469 : Reach 22469 := rs (se 4 (by rfl) ⟨2106, by rfl⟩) (B 4213 (by norm_num) ⟨2106, by rfl⟩ (by norm_num))
theorem R22473 : Reach 22473 := rs (se 2 (by rfl) ⟨8427, by rfl⟩) (B 16855 (by norm_num) ⟨8427, by rfl⟩ (by norm_num))
theorem R22477 : Reach 22477 := rs (se 3 (by rfl) ⟨4214, by rfl⟩) (B 8429 (by norm_num) ⟨4214, by rfl⟩ (by norm_num))
theorem R22481 : Reach 22481 := rs (se 2 (by rfl) ⟨8430, by rfl⟩) (B 16861 (by norm_num) ⟨8430, by rfl⟩ (by norm_num))
theorem R22485 : Reach 22485 := rs (se 7 (by rfl) ⟨263, by rfl⟩) (B 527 (by norm_num) ⟨263, by rfl⟩ (by norm_num))
theorem R22489 : Reach 22489 := rs (se 2 (by rfl) ⟨8433, by rfl⟩) (B 16867 (by norm_num) ⟨8433, by rfl⟩ (by norm_num))
theorem R22493 : Reach 22493 := rs (se 3 (by rfl) ⟨4217, by rfl⟩) (B 8435 (by norm_num) ⟨4217, by rfl⟩ (by norm_num))
theorem R22497 : Reach 22497 := rs (se 2 (by rfl) ⟨8436, by rfl⟩) (B 16873 (by norm_num) ⟨8436, by rfl⟩ (by norm_num))
theorem R22501 : Reach 22501 := rs (se 4 (by rfl) ⟨2109, by rfl⟩) (B 4219 (by norm_num) ⟨2109, by rfl⟩ (by norm_num))
theorem R22505 : Reach 22505 := rs (se 2 (by rfl) ⟨8439, by rfl⟩) (B 16879 (by norm_num) ⟨8439, by rfl⟩ (by norm_num))
theorem R22509 : Reach 22509 := rs (se 3 (by rfl) ⟨4220, by rfl⟩) (B 8441 (by norm_num) ⟨4220, by rfl⟩ (by norm_num))
theorem R22513 : Reach 22513 := rs (se 2 (by rfl) ⟨8442, by rfl⟩) (B 16885 (by norm_num) ⟨8442, by rfl⟩ (by norm_num))
theorem R22517 : Reach 22517 := rs (se 5 (by rfl) ⟨1055, by rfl⟩) (B 2111 (by norm_num) ⟨1055, by rfl⟩ (by norm_num))
theorem R22521 : Reach 22521 := rs (se 2 (by rfl) ⟨8445, by rfl⟩) (B 16891 (by norm_num) ⟨8445, by rfl⟩ (by norm_num))
theorem R22525 : Reach 22525 := rs (se 3 (by rfl) ⟨4223, by rfl⟩) (B 8447 (by norm_num) ⟨4223, by rfl⟩ (by norm_num))
theorem R22529 : Reach 22529 := rs (se 2 (by rfl) ⟨8448, by rfl⟩) (B 16897 (by norm_num) ⟨8448, by rfl⟩ (by norm_num))
theorem R22533 : Reach 22533 := rs (se 4 (by rfl) ⟨2112, by rfl⟩) (B 4225 (by norm_num) ⟨2112, by rfl⟩ (by norm_num))
theorem R22537 : Reach 22537 := rs (se 2 (by rfl) ⟨8451, by rfl⟩) (B 16903 (by norm_num) ⟨8451, by rfl⟩ (by norm_num))
theorem R22541 : Reach 22541 := rs (se 3 (by rfl) ⟨4226, by rfl⟩) (B 8453 (by norm_num) ⟨4226, by rfl⟩ (by norm_num))
theorem R22545 : Reach 22545 := rs (se 2 (by rfl) ⟨8454, by rfl⟩) (B 16909 (by norm_num) ⟨8454, by rfl⟩ (by norm_num))
theorem R22549 : Reach 22549 := rs (se 6 (by rfl) ⟨528, by rfl⟩) (B 1057 (by norm_num) ⟨528, by rfl⟩ (by norm_num))
theorem R22553 : Reach 22553 := rs (se 2 (by rfl) ⟨8457, by rfl⟩) (B 16915 (by norm_num) ⟨8457, by rfl⟩ (by norm_num))
theorem R22557 : Reach 22557 := rs (se 3 (by rfl) ⟨4229, by rfl⟩) (B 8459 (by norm_num) ⟨4229, by rfl⟩ (by norm_num))
theorem R22561 : Reach 22561 := rs (se 2 (by rfl) ⟨8460, by rfl⟩) (B 16921 (by norm_num) ⟨8460, by rfl⟩ (by norm_num))
theorem R22565 : Reach 22565 := rs (se 4 (by rfl) ⟨2115, by rfl⟩) (B 4231 (by norm_num) ⟨2115, by rfl⟩ (by norm_num))
theorem R22569 : Reach 22569 := rs (se 2 (by rfl) ⟨8463, by rfl⟩) (B 16927 (by norm_num) ⟨8463, by rfl⟩ (by norm_num))
theorem R22573 : Reach 22573 := rs (se 3 (by rfl) ⟨4232, by rfl⟩) (B 8465 (by norm_num) ⟨4232, by rfl⟩ (by norm_num))
theorem R22577 : Reach 22577 := rs (se 2 (by rfl) ⟨8466, by rfl⟩) (B 16933 (by norm_num) ⟨8466, by rfl⟩ (by norm_num))
theorem R22581 : Reach 22581 := rs (se 5 (by rfl) ⟨1058, by rfl⟩) (B 2117 (by norm_num) ⟨1058, by rfl⟩ (by norm_num))
theorem R22585 : Reach 22585 := rs (se 2 (by rfl) ⟨8469, by rfl⟩) (B 16939 (by norm_num) ⟨8469, by rfl⟩ (by norm_num))
theorem R22589 : Reach 22589 := rs (se 3 (by rfl) ⟨4235, by rfl⟩) (B 8471 (by norm_num) ⟨4235, by rfl⟩ (by norm_num))
theorem R22593 : Reach 22593 := rs (se 2 (by rfl) ⟨8472, by rfl⟩) (B 16945 (by norm_num) ⟨8472, by rfl⟩ (by norm_num))
theorem R22597 : Reach 22597 := rs (se 4 (by rfl) ⟨2118, by rfl⟩) (B 4237 (by norm_num) ⟨2118, by rfl⟩ (by norm_num))
theorem R22601 : Reach 22601 := rs (se 2 (by rfl) ⟨8475, by rfl⟩) (B 16951 (by norm_num) ⟨8475, by rfl⟩ (by norm_num))
theorem R22605 : Reach 22605 := rs (se 3 (by rfl) ⟨4238, by rfl⟩) (B 8477 (by norm_num) ⟨4238, by rfl⟩ (by norm_num))
theorem R22609 : Reach 22609 := rs (se 2 (by rfl) ⟨8478, by rfl⟩) (B 16957 (by norm_num) ⟨8478, by rfl⟩ (by norm_num))
theorem R22613 : Reach 22613 := rs (se 8 (by rfl) ⟨132, by rfl⟩) (B 265 (by norm_num) ⟨132, by rfl⟩ (by norm_num))
theorem R22617 : Reach 22617 := rs (se 2 (by rfl) ⟨8481, by rfl⟩) (B 16963 (by norm_num) ⟨8481, by rfl⟩ (by norm_num))
theorem R22621 : Reach 22621 := rs (se 3 (by rfl) ⟨4241, by rfl⟩) (B 8483 (by norm_num) ⟨4241, by rfl⟩ (by norm_num))
theorem R22625 : Reach 22625 := rs (se 2 (by rfl) ⟨8484, by rfl⟩) (B 16969 (by norm_num) ⟨8484, by rfl⟩ (by norm_num))
theorem R22629 : Reach 22629 := rs (se 4 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R22633 : Reach 22633 := rs (se 2 (by rfl) ⟨8487, by rfl⟩) (B 16975 (by norm_num) ⟨8487, by rfl⟩ (by norm_num))
theorem R22637 : Reach 22637 := rs (se 3 (by rfl) ⟨4244, by rfl⟩) (B 8489 (by norm_num) ⟨4244, by rfl⟩ (by norm_num))
theorem R22641 : Reach 22641 := rs (se 2 (by rfl) ⟨8490, by rfl⟩) (B 16981 (by norm_num) ⟨8490, by rfl⟩ (by norm_num))
theorem R22645 : Reach 22645 := rs (se 5 (by rfl) ⟨1061, by rfl⟩) (B 2123 (by norm_num) ⟨1061, by rfl⟩ (by norm_num))
theorem R22649 : Reach 22649 := rs (se 2 (by rfl) ⟨8493, by rfl⟩) (B 16987 (by norm_num) ⟨8493, by rfl⟩ (by norm_num))
theorem R22653 : Reach 22653 := rs (se 3 (by rfl) ⟨4247, by rfl⟩) (B 8495 (by norm_num) ⟨4247, by rfl⟩ (by norm_num))
theorem R22657 : Reach 22657 := rs (se 2 (by rfl) ⟨8496, by rfl⟩) (B 16993 (by norm_num) ⟨8496, by rfl⟩ (by norm_num))
theorem R22661 : Reach 22661 := rs (se 4 (by rfl) ⟨2124, by rfl⟩) (B 4249 (by norm_num) ⟨2124, by rfl⟩ (by norm_num))
theorem R22665 : Reach 22665 := rs (se 2 (by rfl) ⟨8499, by rfl⟩) (B 16999 (by norm_num) ⟨8499, by rfl⟩ (by norm_num))
theorem R22669 : Reach 22669 := rs (se 3 (by rfl) ⟨4250, by rfl⟩) (B 8501 (by norm_num) ⟨4250, by rfl⟩ (by norm_num))
theorem R22673 : Reach 22673 := rs (se 2 (by rfl) ⟨8502, by rfl⟩) (B 17005 (by norm_num) ⟨8502, by rfl⟩ (by norm_num))
theorem R22677 : Reach 22677 := rs (se 6 (by rfl) ⟨531, by rfl⟩) (B 1063 (by norm_num) ⟨531, by rfl⟩ (by norm_num))
theorem R22681 : Reach 22681 := rs (se 2 (by rfl) ⟨8505, by rfl⟩) (B 17011 (by norm_num) ⟨8505, by rfl⟩ (by norm_num))
theorem R22685 : Reach 22685 := rs (se 3 (by rfl) ⟨4253, by rfl⟩) (B 8507 (by norm_num) ⟨4253, by rfl⟩ (by norm_num))
theorem R22689 : Reach 22689 := rs (se 2 (by rfl) ⟨8508, by rfl⟩) (B 17017 (by norm_num) ⟨8508, by rfl⟩ (by norm_num))
theorem R22693 : Reach 22693 := rs (se 4 (by rfl) ⟨2127, by rfl⟩) (B 4255 (by norm_num) ⟨2127, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R22697 : Reach 22697 := rs (se 2 (by rfl) ⟨8511, by rfl⟩) (B 17023 (by norm_num) ⟨8511, by rfl⟩ (by norm_num))
theorem R22701 : Reach 22701 := rs (se 3 (by rfl) ⟨4256, by rfl⟩) (B 8513 (by norm_num) ⟨4256, by rfl⟩ (by norm_num))
theorem R22705 : Reach 22705 := rs (se 2 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R22709 : Reach 22709 := rs (se 5 (by rfl) ⟨1064, by rfl⟩) (B 2129 (by norm_num) ⟨1064, by rfl⟩ (by norm_num))
theorem R22713 : Reach 22713 := rs (se 2 (by rfl) ⟨8517, by rfl⟩) (B 17035 (by norm_num) ⟨8517, by rfl⟩ (by norm_num))
theorem R22717 : Reach 22717 := rs (se 3 (by rfl) ⟨4259, by rfl⟩) (B 8519 (by norm_num) ⟨4259, by rfl⟩ (by norm_num))
theorem R22721 : Reach 22721 := rs (se 2 (by rfl) ⟨8520, by rfl⟩) (B 17041 (by norm_num) ⟨8520, by rfl⟩ (by norm_num))
theorem R22725 : Reach 22725 := rs (se 4 (by rfl) ⟨2130, by rfl⟩) (B 4261 (by norm_num) ⟨2130, by rfl⟩ (by norm_num))
theorem R22729 : Reach 22729 := rs (se 2 (by rfl) ⟨8523, by rfl⟩) (B 17047 (by norm_num) ⟨8523, by rfl⟩ (by norm_num))
theorem R22733 : Reach 22733 := rs (se 3 (by rfl) ⟨4262, by rfl⟩) (B 8525 (by norm_num) ⟨4262, by rfl⟩ (by norm_num))
theorem R22737 : Reach 22737 := rs (se 2 (by rfl) ⟨8526, by rfl⟩) (B 17053 (by norm_num) ⟨8526, by rfl⟩ (by norm_num))
theorem R22741 : Reach 22741 := rs (se 7 (by rfl) ⟨266, by rfl⟩) (B 533 (by norm_num) ⟨266, by rfl⟩ (by norm_num))
theorem R22745 : Reach 22745 := rs (se 2 (by rfl) ⟨8529, by rfl⟩) (B 17059 (by norm_num) ⟨8529, by rfl⟩ (by norm_num))
theorem R22749 : Reach 22749 := rs (se 3 (by rfl) ⟨4265, by rfl⟩) (B 8531 (by norm_num) ⟨4265, by rfl⟩ (by norm_num))
theorem R22753 : Reach 22753 := rs (se 2 (by rfl) ⟨8532, by rfl⟩) (B 17065 (by norm_num) ⟨8532, by rfl⟩ (by norm_num))
theorem R55525 : Reach 55525 := rs (se 4 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R22757 : Reach 22757 := rs (se 4 (by rfl) ⟨2133, by rfl⟩) (B 4267 (by norm_num) ⟨2133, by rfl⟩ (by norm_num))
theorem R22761 : Reach 22761 := rs (se 2 (by rfl) ⟨8535, by rfl⟩) (B 17071 (by norm_num) ⟨8535, by rfl⟩ (by norm_num))
theorem R22765 : Reach 22765 := rs (se 3 (by rfl) ⟨4268, by rfl⟩) (B 8537 (by norm_num) ⟨4268, by rfl⟩ (by norm_num))
theorem R22769 : Reach 22769 := rs (se 2 (by rfl) ⟨8538, by rfl⟩) (B 17077 (by norm_num) ⟨8538, by rfl⟩ (by norm_num))
theorem R22773 : Reach 22773 := rs (se 5 (by rfl) ⟨1067, by rfl⟩) (B 2135 (by norm_num) ⟨1067, by rfl⟩ (by norm_num))
theorem R22777 : Reach 22777 := rs (se 2 (by rfl) ⟨8541, by rfl⟩) (B 17083 (by norm_num) ⟨8541, by rfl⟩ (by norm_num))
theorem R22781 : Reach 22781 := rs (se 3 (by rfl) ⟨4271, by rfl⟩) (B 8543 (by norm_num) ⟨4271, by rfl⟩ (by norm_num))
theorem R22785 : Reach 22785 := rs (se 2 (by rfl) ⟨8544, by rfl⟩) (B 17089 (by norm_num) ⟨8544, by rfl⟩ (by norm_num))
theorem R22789 : Reach 22789 := rs (se 4 (by rfl) ⟨2136, by rfl⟩) (B 4273 (by norm_num) ⟨2136, by rfl⟩ (by norm_num))
theorem R22793 : Reach 22793 := rs (se 2 (by rfl) ⟨8547, by rfl⟩) (B 17095 (by norm_num) ⟨8547, by rfl⟩ (by norm_num))
theorem R22797 : Reach 22797 := rs (se 3 (by rfl) ⟨4274, by rfl⟩) (B 8549 (by norm_num) ⟨4274, by rfl⟩ (by norm_num))
theorem R22801 : Reach 22801 := rs (se 2 (by rfl) ⟨8550, by rfl⟩) (B 17101 (by norm_num) ⟨8550, by rfl⟩ (by norm_num))
theorem R22805 : Reach 22805 := rs (se 6 (by rfl) ⟨534, by rfl⟩) (B 1069 (by norm_num) ⟨534, by rfl⟩ (by norm_num))
theorem R22809 : Reach 22809 := rs (se 2 (by rfl) ⟨8553, by rfl⟩) (B 17107 (by norm_num) ⟨8553, by rfl⟩ (by norm_num))
theorem R22813 : Reach 22813 := rs (se 3 (by rfl) ⟨4277, by rfl⟩) (B 8555 (by norm_num) ⟨4277, by rfl⟩ (by norm_num))
theorem R22817 : Reach 22817 := rs (se 2 (by rfl) ⟨8556, by rfl⟩) (B 17113 (by norm_num) ⟨8556, by rfl⟩ (by norm_num))
theorem R22821 : Reach 22821 := rs (se 4 (by rfl) ⟨2139, by rfl⟩) (B 4279 (by norm_num) ⟨2139, by rfl⟩ (by norm_num))
theorem R22825 : Reach 22825 := rs (se 2 (by rfl) ⟨8559, by rfl⟩) (B 17119 (by norm_num) ⟨8559, by rfl⟩ (by norm_num))
theorem R22829 : Reach 22829 := rs (se 3 (by rfl) ⟨4280, by rfl⟩) (B 8561 (by norm_num) ⟨4280, by rfl⟩ (by norm_num))
theorem R22833 : Reach 22833 := rs (se 2 (by rfl) ⟨8562, by rfl⟩) (B 17125 (by norm_num) ⟨8562, by rfl⟩ (by norm_num))
theorem R22837 : Reach 22837 := rs (se 5 (by rfl) ⟨1070, by rfl⟩) (B 2141 (by norm_num) ⟨1070, by rfl⟩ (by norm_num))
theorem R22841 : Reach 22841 := rs (se 2 (by rfl) ⟨8565, by rfl⟩) (B 17131 (by norm_num) ⟨8565, by rfl⟩ (by norm_num))
theorem R22845 : Reach 22845 := rs (se 3 (by rfl) ⟨4283, by rfl⟩) (B 8567 (by norm_num) ⟨4283, by rfl⟩ (by norm_num))
theorem R22849 : Reach 22849 := rs (se 2 (by rfl) ⟨8568, by rfl⟩) (B 17137 (by norm_num) ⟨8568, by rfl⟩ (by norm_num))
theorem R22853 : Reach 22853 := rs (se 4 (by rfl) ⟨2142, by rfl⟩) (B 4285 (by norm_num) ⟨2142, by rfl⟩ (by norm_num))
theorem R22857 : Reach 22857 := rs (se 2 (by rfl) ⟨8571, by rfl⟩) (B 17143 (by norm_num) ⟨8571, by rfl⟩ (by norm_num))
theorem R22861 : Reach 22861 := rs (se 3 (by rfl) ⟨4286, by rfl⟩) (B 8573 (by norm_num) ⟨4286, by rfl⟩ (by norm_num))
theorem R22865 : Reach 22865 := rs (se 2 (by rfl) ⟨8574, by rfl⟩) (B 17149 (by norm_num) ⟨8574, by rfl⟩ (by norm_num))
theorem R55637 : Reach 55637 := rs (se 10 (by rfl) ⟨81, by rfl⟩) (B 163 (by norm_num) ⟨81, by rfl⟩ (by norm_num))
theorem R22869 : Reach 22869 := rs (se 10 (by rfl) ⟨33, by rfl⟩) (B 67 (by norm_num) ⟨33, by rfl⟩ (by norm_num))
theorem R22873 : Reach 22873 := rs (se 2 (by rfl) ⟨8577, by rfl⟩) (B 17155 (by norm_num) ⟨8577, by rfl⟩ (by norm_num))
theorem R22877 : Reach 22877 := rs (se 3 (by rfl) ⟨4289, by rfl⟩) (B 8579 (by norm_num) ⟨4289, by rfl⟩ (by norm_num))
theorem R22881 : Reach 22881 := rs (se 2 (by rfl) ⟨8580, by rfl⟩) (B 17161 (by norm_num) ⟨8580, by rfl⟩ (by norm_num))
theorem R22885 : Reach 22885 := rs (se 4 (by rfl) ⟨2145, by rfl⟩) (B 4291 (by norm_num) ⟨2145, by rfl⟩ (by norm_num))
theorem R22889 : Reach 22889 := rs (se 2 (by rfl) ⟨8583, by rfl⟩) (B 17167 (by norm_num) ⟨8583, by rfl⟩ (by norm_num))
theorem R22893 : Reach 22893 := rs (se 3 (by rfl) ⟨4292, by rfl⟩) (B 8585 (by norm_num) ⟨4292, by rfl⟩ (by norm_num))
theorem R22897 : Reach 22897 := rs (se 2 (by rfl) ⟨8586, by rfl⟩) (B 17173 (by norm_num) ⟨8586, by rfl⟩ (by norm_num))
theorem R22901 : Reach 22901 := rs (se 5 (by rfl) ⟨1073, by rfl⟩) (B 2147 (by norm_num) ⟨1073, by rfl⟩ (by norm_num))
theorem R22905 : Reach 22905 := rs (se 2 (by rfl) ⟨8589, by rfl⟩) (B 17179 (by norm_num) ⟨8589, by rfl⟩ (by norm_num))
theorem R22909 : Reach 22909 := rs (se 3 (by rfl) ⟨4295, by rfl⟩) (B 8591 (by norm_num) ⟨4295, by rfl⟩ (by norm_num))
theorem R22913 : Reach 22913 := rs (se 2 (by rfl) ⟨8592, by rfl⟩) (B 17185 (by norm_num) ⟨8592, by rfl⟩ (by norm_num))
theorem R22917 : Reach 22917 := rs (se 4 (by rfl) ⟨2148, by rfl⟩) (B 4297 (by norm_num) ⟨2148, by rfl⟩ (by norm_num))
theorem R22921 : Reach 22921 := rs (se 2 (by rfl) ⟨8595, by rfl⟩) (B 17191 (by norm_num) ⟨8595, by rfl⟩ (by norm_num))
theorem R22925 : Reach 22925 := rs (se 3 (by rfl) ⟨4298, by rfl⟩) (B 8597 (by norm_num) ⟨4298, by rfl⟩ (by norm_num))
theorem R22929 : Reach 22929 := rs (se 2 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R22933 : Reach 22933 := rs (se 6 (by rfl) ⟨537, by rfl⟩) (B 1075 (by norm_num) ⟨537, by rfl⟩ (by norm_num))
theorem R22937 : Reach 22937 := rs (se 2 (by rfl) ⟨8601, by rfl⟩) (B 17203 (by norm_num) ⟨8601, by rfl⟩ (by norm_num))
theorem R22941 : Reach 22941 := rs (se 3 (by rfl) ⟨4301, by rfl⟩) (B 8603 (by norm_num) ⟨4301, by rfl⟩ (by norm_num))
theorem R22945 : Reach 22945 := rs (se 2 (by rfl) ⟨8604, by rfl⟩) (B 17209 (by norm_num) ⟨8604, by rfl⟩ (by norm_num))
theorem R22949 : Reach 22949 := rs (se 4 (by rfl) ⟨2151, by rfl⟩) (B 4303 (by norm_num) ⟨2151, by rfl⟩ (by norm_num))
theorem R22953 : Reach 22953 := rs (se 2 (by rfl) ⟨8607, by rfl⟩) (B 17215 (by norm_num) ⟨8607, by rfl⟩ (by norm_num))
theorem R22957 : Reach 22957 := rs (se 3 (by rfl) ⟨4304, by rfl⟩) (B 8609 (by norm_num) ⟨4304, by rfl⟩ (by norm_num))
theorem R22961 : Reach 22961 := rs (se 2 (by rfl) ⟨8610, by rfl⟩) (B 17221 (by norm_num) ⟨8610, by rfl⟩ (by norm_num))
theorem R22965 : Reach 22965 := rs (se 5 (by rfl) ⟨1076, by rfl⟩) (B 2153 (by norm_num) ⟨1076, by rfl⟩ (by norm_num))
theorem R22969 : Reach 22969 := rs (se 2 (by rfl) ⟨8613, by rfl⟩) (B 17227 (by norm_num) ⟨8613, by rfl⟩ (by norm_num))
theorem R22973 : Reach 22973 := rs (se 3 (by rfl) ⟨4307, by rfl⟩) (B 8615 (by norm_num) ⟨4307, by rfl⟩ (by norm_num))
theorem R22977 : Reach 22977 := rs (se 2 (by rfl) ⟨8616, by rfl⟩) (B 17233 (by norm_num) ⟨8616, by rfl⟩ (by norm_num))
theorem R22981 : Reach 22981 := rs (se 4 (by rfl) ⟨2154, by rfl⟩) (B 4309 (by norm_num) ⟨2154, by rfl⟩ (by norm_num))
theorem R22985 : Reach 22985 := rs (se 2 (by rfl) ⟨8619, by rfl⟩) (B 17239 (by norm_num) ⟨8619, by rfl⟩ (by norm_num))
theorem R22989 : Reach 22989 := rs (se 3 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R22993 : Reach 22993 := rs (se 2 (by rfl) ⟨8622, by rfl⟩) (B 17245 (by norm_num) ⟨8622, by rfl⟩ (by norm_num))
theorem R22997 : Reach 22997 := rs (se 7 (by rfl) ⟨269, by rfl⟩) (B 539 (by norm_num) ⟨269, by rfl⟩ (by norm_num))
theorem R23001 : Reach 23001 := rs (se 2 (by rfl) ⟨8625, by rfl⟩) (B 17251 (by norm_num) ⟨8625, by rfl⟩ (by norm_num))
theorem R23005 : Reach 23005 := rs (se 3 (by rfl) ⟨4313, by rfl⟩) (B 8627 (by norm_num) ⟨4313, by rfl⟩ (by norm_num))
theorem R23009 : Reach 23009 := rs (se 2 (by rfl) ⟨8628, by rfl⟩) (B 17257 (by norm_num) ⟨8628, by rfl⟩ (by norm_num))
theorem R23013 : Reach 23013 := rs (se 4 (by rfl) ⟨2157, by rfl⟩) (B 4315 (by norm_num) ⟨2157, by rfl⟩ (by norm_num))
theorem R23017 : Reach 23017 := rs (se 2 (by rfl) ⟨8631, by rfl⟩) (B 17263 (by norm_num) ⟨8631, by rfl⟩ (by norm_num))
theorem R23021 : Reach 23021 := rs (se 3 (by rfl) ⟨4316, by rfl⟩) (B 8633 (by norm_num) ⟨4316, by rfl⟩ (by norm_num))
theorem R23025 : Reach 23025 := rs (se 2 (by rfl) ⟨8634, by rfl⟩) (B 17269 (by norm_num) ⟨8634, by rfl⟩ (by norm_num))
theorem R23029 : Reach 23029 := rs (se 5 (by rfl) ⟨1079, by rfl⟩) (B 2159 (by norm_num) ⟨1079, by rfl⟩ (by norm_num))
theorem R23033 : Reach 23033 := rs (se 2 (by rfl) ⟨8637, by rfl⟩) (B 17275 (by norm_num) ⟨8637, by rfl⟩ (by norm_num))
theorem R23037 : Reach 23037 := rs (se 3 (by rfl) ⟨4319, by rfl⟩) (B 8639 (by norm_num) ⟨4319, by rfl⟩ (by norm_num))
theorem R23041 : Reach 23041 := rs (se 2 (by rfl) ⟨8640, by rfl⟩) (B 17281 (by norm_num) ⟨8640, by rfl⟩ (by norm_num))
theorem R23045 : Reach 23045 := rs (se 4 (by rfl) ⟨2160, by rfl⟩) (B 4321 (by norm_num) ⟨2160, by rfl⟩ (by norm_num))
theorem R23049 : Reach 23049 := rs (se 2 (by rfl) ⟨8643, by rfl⟩) (B 17287 (by norm_num) ⟨8643, by rfl⟩ (by norm_num))
theorem R23053 : Reach 23053 := rs (se 3 (by rfl) ⟨4322, by rfl⟩) (B 8645 (by norm_num) ⟨4322, by rfl⟩ (by norm_num))
theorem R23057 : Reach 23057 := rs (se 2 (by rfl) ⟨8646, by rfl⟩) (B 17293 (by norm_num) ⟨8646, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R23061 : Reach 23061 := rs (se 6 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R23065 : Reach 23065 := rs (se 2 (by rfl) ⟨8649, by rfl⟩) (B 17299 (by norm_num) ⟨8649, by rfl⟩ (by norm_num))
theorem R23069 : Reach 23069 := rs (se 3 (by rfl) ⟨4325, by rfl⟩) (B 8651 (by norm_num) ⟨4325, by rfl⟩ (by norm_num))
theorem R23073 : Reach 23073 := rs (se 2 (by rfl) ⟨8652, by rfl⟩) (B 17305 (by norm_num) ⟨8652, by rfl⟩ (by norm_num))
theorem R23077 : Reach 23077 := rs (se 4 (by rfl) ⟨2163, by rfl⟩) (B 4327 (by norm_num) ⟨2163, by rfl⟩ (by norm_num))
theorem R23081 : Reach 23081 := rs (se 2 (by rfl) ⟨8655, by rfl⟩) (B 17311 (by norm_num) ⟨8655, by rfl⟩ (by norm_num))
theorem R23085 : Reach 23085 := rs (se 3 (by rfl) ⟨4328, by rfl⟩) (B 8657 (by norm_num) ⟨4328, by rfl⟩ (by norm_num))
theorem R23089 : Reach 23089 := rs (se 2 (by rfl) ⟨8658, by rfl⟩) (B 17317 (by norm_num) ⟨8658, by rfl⟩ (by norm_num))
theorem R23093 : Reach 23093 := rs (se 5 (by rfl) ⟨1082, by rfl⟩) (B 2165 (by norm_num) ⟨1082, by rfl⟩ (by norm_num))
theorem R23097 : Reach 23097 := rs (se 2 (by rfl) ⟨8661, by rfl⟩) (B 17323 (by norm_num) ⟨8661, by rfl⟩ (by norm_num))
theorem R23101 : Reach 23101 := rs (se 3 (by rfl) ⟨4331, by rfl⟩) (B 8663 (by norm_num) ⟨4331, by rfl⟩ (by norm_num))
theorem R23105 : Reach 23105 := rs (se 2 (by rfl) ⟨8664, by rfl⟩) (B 17329 (by norm_num) ⟨8664, by rfl⟩ (by norm_num))
theorem R23109 : Reach 23109 := rs (se 4 (by rfl) ⟨2166, by rfl⟩) (B 4333 (by norm_num) ⟨2166, by rfl⟩ (by norm_num))
theorem R23113 : Reach 23113 := rs (se 2 (by rfl) ⟨8667, by rfl⟩) (B 17335 (by norm_num) ⟨8667, by rfl⟩ (by norm_num))
theorem R23117 : Reach 23117 := rs (se 3 (by rfl) ⟨4334, by rfl⟩) (B 8669 (by norm_num) ⟨4334, by rfl⟩ (by norm_num))
theorem R23121 : Reach 23121 := rs (se 2 (by rfl) ⟨8670, by rfl⟩) (B 17341 (by norm_num) ⟨8670, by rfl⟩ (by norm_num))
theorem R23125 : Reach 23125 := rs (se 8 (by rfl) ⟨135, by rfl⟩) (B 271 (by norm_num) ⟨135, by rfl⟩ (by norm_num))
theorem R23129 : Reach 23129 := rs (se 2 (by rfl) ⟨8673, by rfl⟩) (B 17347 (by norm_num) ⟨8673, by rfl⟩ (by norm_num))
theorem R23133 : Reach 23133 := rs (se 3 (by rfl) ⟨4337, by rfl⟩) (B 8675 (by norm_num) ⟨4337, by rfl⟩ (by norm_num))
theorem R23137 : Reach 23137 := rs (se 2 (by rfl) ⟨8676, by rfl⟩) (B 17353 (by norm_num) ⟨8676, by rfl⟩ (by norm_num))
theorem R23141 : Reach 23141 := rs (se 4 (by rfl) ⟨2169, by rfl⟩) (B 4339 (by norm_num) ⟨2169, by rfl⟩ (by norm_num))
theorem R23145 : Reach 23145 := rs (se 2 (by rfl) ⟨8679, by rfl⟩) (B 17359 (by norm_num) ⟨8679, by rfl⟩ (by norm_num))
theorem R23149 : Reach 23149 := rs (se 3 (by rfl) ⟨4340, by rfl⟩) (B 8681 (by norm_num) ⟨4340, by rfl⟩ (by norm_num))
theorem R23153 : Reach 23153 := rs (se 2 (by rfl) ⟨8682, by rfl⟩) (B 17365 (by norm_num) ⟨8682, by rfl⟩ (by norm_num))
theorem R23157 : Reach 23157 := rs (se 5 (by rfl) ⟨1085, by rfl⟩) (B 2171 (by norm_num) ⟨1085, by rfl⟩ (by norm_num))
theorem R23161 : Reach 23161 := rs (se 2 (by rfl) ⟨8685, by rfl⟩) (B 17371 (by norm_num) ⟨8685, by rfl⟩ (by norm_num))
theorem R23165 : Reach 23165 := rs (se 3 (by rfl) ⟨4343, by rfl⟩) (B 8687 (by norm_num) ⟨4343, by rfl⟩ (by norm_num))
theorem R23169 : Reach 23169 := rs (se 2 (by rfl) ⟨8688, by rfl⟩) (B 17377 (by norm_num) ⟨8688, by rfl⟩ (by norm_num))
theorem R23173 : Reach 23173 := rs (se 4 (by rfl) ⟨2172, by rfl⟩) (B 4345 (by norm_num) ⟨2172, by rfl⟩ (by norm_num))
theorem R23177 : Reach 23177 := rs (se 2 (by rfl) ⟨8691, by rfl⟩) (B 17383 (by norm_num) ⟨8691, by rfl⟩ (by norm_num))
theorem R23181 : Reach 23181 := rs (se 3 (by rfl) ⟨4346, by rfl⟩) (B 8693 (by norm_num) ⟨4346, by rfl⟩ (by norm_num))
theorem R23185 : Reach 23185 := rs (se 2 (by rfl) ⟨8694, by rfl⟩) (B 17389 (by norm_num) ⟨8694, by rfl⟩ (by norm_num))
theorem R23189 : Reach 23189 := rs (se 6 (by rfl) ⟨543, by rfl⟩) (B 1087 (by norm_num) ⟨543, by rfl⟩ (by norm_num))
theorem R23193 : Reach 23193 := rs (se 2 (by rfl) ⟨8697, by rfl⟩) (B 17395 (by norm_num) ⟨8697, by rfl⟩ (by norm_num))
theorem R23197 : Reach 23197 := rs (se 3 (by rfl) ⟨4349, by rfl⟩) (B 8699 (by norm_num) ⟨4349, by rfl⟩ (by norm_num))
theorem R23201 : Reach 23201 := rs (se 2 (by rfl) ⟨8700, by rfl⟩) (B 17401 (by norm_num) ⟨8700, by rfl⟩ (by norm_num))
theorem R23205 : Reach 23205 := rs (se 4 (by rfl) ⟨2175, by rfl⟩) (B 4351 (by norm_num) ⟨2175, by rfl⟩ (by norm_num))
theorem R23209 : Reach 23209 := rs (se 2 (by rfl) ⟨8703, by rfl⟩) (B 17407 (by norm_num) ⟨8703, by rfl⟩ (by norm_num))
theorem R23213 : Reach 23213 := rs (se 3 (by rfl) ⟨4352, by rfl⟩) (B 8705 (by norm_num) ⟨4352, by rfl⟩ (by norm_num))
theorem R23217 : Reach 23217 := rs (se 2 (by rfl) ⟨8706, by rfl⟩) (B 17413 (by norm_num) ⟨8706, by rfl⟩ (by norm_num))
theorem R23221 : Reach 23221 := rs (se 5 (by rfl) ⟨1088, by rfl⟩) (B 2177 (by norm_num) ⟨1088, by rfl⟩ (by norm_num))
theorem R23225 : Reach 23225 := rs (se 2 (by rfl) ⟨8709, by rfl⟩) (B 17419 (by norm_num) ⟨8709, by rfl⟩ (by norm_num))
theorem R23229 : Reach 23229 := rs (se 3 (by rfl) ⟨4355, by rfl⟩) (B 8711 (by norm_num) ⟨4355, by rfl⟩ (by norm_num))
theorem R23233 : Reach 23233 := rs (se 2 (by rfl) ⟨8712, by rfl⟩) (B 17425 (by norm_num) ⟨8712, by rfl⟩ (by norm_num))
theorem R23237 : Reach 23237 := rs (se 4 (by rfl) ⟨2178, by rfl⟩) (B 4357 (by norm_num) ⟨2178, by rfl⟩ (by norm_num))
theorem R23241 : Reach 23241 := rs (se 2 (by rfl) ⟨8715, by rfl⟩) (B 17431 (by norm_num) ⟨8715, by rfl⟩ (by norm_num))
theorem R23245 : Reach 23245 := rs (se 3 (by rfl) ⟨4358, by rfl⟩) (B 8717 (by norm_num) ⟨4358, by rfl⟩ (by norm_num))
theorem R23249 : Reach 23249 := rs (se 2 (by rfl) ⟨8718, by rfl⟩) (B 17437 (by norm_num) ⟨8718, by rfl⟩ (by norm_num))
theorem R23253 : Reach 23253 := rs (se 7 (by rfl) ⟨272, by rfl⟩) (B 545 (by norm_num) ⟨272, by rfl⟩ (by norm_num))
theorem R23257 : Reach 23257 := rs (se 2 (by rfl) ⟨8721, by rfl⟩) (B 17443 (by norm_num) ⟨8721, by rfl⟩ (by norm_num))
theorem R23261 : Reach 23261 := rs (se 3 (by rfl) ⟨4361, by rfl⟩) (B 8723 (by norm_num) ⟨4361, by rfl⟩ (by norm_num))
theorem R23265 : Reach 23265 := rs (se 2 (by rfl) ⟨8724, by rfl⟩) (B 17449 (by norm_num) ⟨8724, by rfl⟩ (by norm_num))
theorem R23269 : Reach 23269 := rs (se 4 (by rfl) ⟨2181, by rfl⟩) (B 4363 (by norm_num) ⟨2181, by rfl⟩ (by norm_num))
theorem R23273 : Reach 23273 := rs (se 2 (by rfl) ⟨8727, by rfl⟩) (B 17455 (by norm_num) ⟨8727, by rfl⟩ (by norm_num))
theorem R23277 : Reach 23277 := rs (se 3 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R23281 : Reach 23281 := rs (se 2 (by rfl) ⟨8730, by rfl⟩) (B 17461 (by norm_num) ⟨8730, by rfl⟩ (by norm_num))
theorem R23285 : Reach 23285 := rs (se 5 (by rfl) ⟨1091, by rfl⟩) (B 2183 (by norm_num) ⟨1091, by rfl⟩ (by norm_num))
theorem R23289 : Reach 23289 := rs (se 2 (by rfl) ⟨8733, by rfl⟩) (B 17467 (by norm_num) ⟨8733, by rfl⟩ (by norm_num))
theorem R23293 : Reach 23293 := rs (se 3 (by rfl) ⟨4367, by rfl⟩) (B 8735 (by norm_num) ⟨4367, by rfl⟩ (by norm_num))
theorem R23297 : Reach 23297 := rs (se 2 (by rfl) ⟨8736, by rfl⟩) (B 17473 (by norm_num) ⟨8736, by rfl⟩ (by norm_num))
theorem R23301 : Reach 23301 := rs (se 4 (by rfl) ⟨2184, by rfl⟩) (B 4369 (by norm_num) ⟨2184, by rfl⟩ (by norm_num))
theorem R23305 : Reach 23305 := rs (se 2 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R23309 : Reach 23309 := rs (se 3 (by rfl) ⟨4370, by rfl⟩) (B 8741 (by norm_num) ⟨4370, by rfl⟩ (by norm_num))
theorem R23313 : Reach 23313 := rs (se 2 (by rfl) ⟨8742, by rfl⟩) (B 17485 (by norm_num) ⟨8742, by rfl⟩ (by norm_num))
theorem R23317 : Reach 23317 := rs (se 6 (by rfl) ⟨546, by rfl⟩) (B 1093 (by norm_num) ⟨546, by rfl⟩ (by norm_num))
theorem R23321 : Reach 23321 := rs (se 2 (by rfl) ⟨8745, by rfl⟩) (B 17491 (by norm_num) ⟨8745, by rfl⟩ (by norm_num))
theorem R23325 : Reach 23325 := rs (se 3 (by rfl) ⟨4373, by rfl⟩) (B 8747 (by norm_num) ⟨4373, by rfl⟩ (by norm_num))
theorem R23329 : Reach 23329 := rs (se 2 (by rfl) ⟨8748, by rfl⟩) (B 17497 (by norm_num) ⟨8748, by rfl⟩ (by norm_num))
theorem R23333 : Reach 23333 := rs (se 4 (by rfl) ⟨2187, by rfl⟩) (B 4375 (by norm_num) ⟨2187, by rfl⟩ (by norm_num))
theorem R23337 : Reach 23337 := rs (se 2 (by rfl) ⟨8751, by rfl⟩) (B 17503 (by norm_num) ⟨8751, by rfl⟩ (by norm_num))
theorem R23341 : Reach 23341 := rs (se 3 (by rfl) ⟨4376, by rfl⟩) (B 8753 (by norm_num) ⟨4376, by rfl⟩ (by norm_num))
theorem R23345 : Reach 23345 := rs (se 2 (by rfl) ⟨8754, by rfl⟩) (B 17509 (by norm_num) ⟨8754, by rfl⟩ (by norm_num))
theorem R23349 : Reach 23349 := rs (se 5 (by rfl) ⟨1094, by rfl⟩) (B 2189 (by norm_num) ⟨1094, by rfl⟩ (by norm_num))
theorem R23353 : Reach 23353 := rs (se 2 (by rfl) ⟨8757, by rfl⟩) (B 17515 (by norm_num) ⟨8757, by rfl⟩ (by norm_num))
theorem R23357 : Reach 23357 := rs (se 3 (by rfl) ⟨4379, by rfl⟩) (B 8759 (by norm_num) ⟨4379, by rfl⟩ (by norm_num))
theorem R23361 : Reach 23361 := rs (se 2 (by rfl) ⟨8760, by rfl⟩) (B 17521 (by norm_num) ⟨8760, by rfl⟩ (by norm_num))
theorem R23365 : Reach 23365 := rs (se 4 (by rfl) ⟨2190, by rfl⟩) (B 4381 (by norm_num) ⟨2190, by rfl⟩ (by norm_num))
theorem R23369 : Reach 23369 := rs (se 2 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R23373 : Reach 23373 := rs (se 3 (by rfl) ⟨4382, by rfl⟩) (B 8765 (by norm_num) ⟨4382, by rfl⟩ (by norm_num))
theorem R23377 : Reach 23377 := rs (se 2 (by rfl) ⟨8766, by rfl⟩) (B 17533 (by norm_num) ⟨8766, by rfl⟩ (by norm_num))
theorem R23381 : Reach 23381 := rs (se 9 (by rfl) ⟨68, by rfl⟩) (B 137 (by norm_num) ⟨68, by rfl⟩ (by norm_num))
theorem R23385 : Reach 23385 := rs (se 2 (by rfl) ⟨8769, by rfl⟩) (B 17539 (by norm_num) ⟨8769, by rfl⟩ (by norm_num))
theorem R23389 : Reach 23389 := rs (se 3 (by rfl) ⟨4385, by rfl⟩) (B 8771 (by norm_num) ⟨4385, by rfl⟩ (by norm_num))
theorem R23393 : Reach 23393 := rs (se 2 (by rfl) ⟨8772, by rfl⟩) (B 17545 (by norm_num) ⟨8772, by rfl⟩ (by norm_num))
theorem R23397 : Reach 23397 := rs (se 4 (by rfl) ⟨2193, by rfl⟩) (B 4387 (by norm_num) ⟨2193, by rfl⟩ (by norm_num))
theorem R23401 : Reach 23401 := rs (se 2 (by rfl) ⟨8775, by rfl⟩) (B 17551 (by norm_num) ⟨8775, by rfl⟩ (by norm_num))
theorem R23405 : Reach 23405 := rs (se 3 (by rfl) ⟨4388, by rfl⟩) (B 8777 (by norm_num) ⟨4388, by rfl⟩ (by norm_num))
theorem R23409 : Reach 23409 := rs (se 2 (by rfl) ⟨8778, by rfl⟩) (B 17557 (by norm_num) ⟨8778, by rfl⟩ (by norm_num))
theorem R23413 : Reach 23413 := rs (se 5 (by rfl) ⟨1097, by rfl⟩) (B 2195 (by norm_num) ⟨1097, by rfl⟩ (by norm_num))
theorem R23417 : Reach 23417 := rs (se 2 (by rfl) ⟨8781, by rfl⟩) (B 17563 (by norm_num) ⟨8781, by rfl⟩ (by norm_num))
theorem R23421 : Reach 23421 := rs (se 3 (by rfl) ⟨4391, by rfl⟩) (B 8783 (by norm_num) ⟨4391, by rfl⟩ (by norm_num))
theorem R23425 : Reach 23425 := rs (se 2 (by rfl) ⟨8784, by rfl⟩) (B 17569 (by norm_num) ⟨8784, by rfl⟩ (by norm_num))
theorem R23429 : Reach 23429 := rs (se 4 (by rfl) ⟨2196, by rfl⟩) (B 4393 (by norm_num) ⟨2196, by rfl⟩ (by norm_num))
theorem R23433 : Reach 23433 := rs (se 2 (by rfl) ⟨8787, by rfl⟩) (B 17575 (by norm_num) ⟨8787, by rfl⟩ (by norm_num))
theorem R23437 : Reach 23437 := rs (se 3 (by rfl) ⟨4394, by rfl⟩) (B 8789 (by norm_num) ⟨4394, by rfl⟩ (by norm_num))
theorem R23441 : Reach 23441 := rs (se 2 (by rfl) ⟨8790, by rfl⟩) (B 17581 (by norm_num) ⟨8790, by rfl⟩ (by norm_num))
theorem R23445 : Reach 23445 := rs (se 6 (by rfl) ⟨549, by rfl⟩) (B 1099 (by norm_num) ⟨549, by rfl⟩ (by norm_num))
theorem R23449 : Reach 23449 := rs (se 2 (by rfl) ⟨8793, by rfl⟩) (B 17587 (by norm_num) ⟨8793, by rfl⟩ (by norm_num))
theorem R23453 : Reach 23453 := rs (se 3 (by rfl) ⟨4397, by rfl⟩) (B 8795 (by norm_num) ⟨4397, by rfl⟩ (by norm_num))
theorem R23457 : Reach 23457 := rs (se 2 (by rfl) ⟨8796, by rfl⟩) (B 17593 (by norm_num) ⟨8796, by rfl⟩ (by norm_num))
theorem R23461 : Reach 23461 := rs (se 4 (by rfl) ⟨2199, by rfl⟩) (B 4399 (by norm_num) ⟨2199, by rfl⟩ (by norm_num))
theorem R23465 : Reach 23465 := rs (se 2 (by rfl) ⟨8799, by rfl⟩) (B 17599 (by norm_num) ⟨8799, by rfl⟩ (by norm_num))
theorem R23469 : Reach 23469 := rs (se 3 (by rfl) ⟨4400, by rfl⟩) (B 8801 (by norm_num) ⟨4400, by rfl⟩ (by norm_num))
theorem R23473 : Reach 23473 := rs (se 2 (by rfl) ⟨8802, by rfl⟩) (B 17605 (by norm_num) ⟨8802, by rfl⟩ (by norm_num))
theorem R23477 : Reach 23477 := rs (se 5 (by rfl) ⟨1100, by rfl⟩) (B 2201 (by norm_num) ⟨1100, by rfl⟩ (by norm_num))
theorem R23481 : Reach 23481 := rs (se 2 (by rfl) ⟨8805, by rfl⟩) (B 17611 (by norm_num) ⟨8805, by rfl⟩ (by norm_num))
theorem R23485 : Reach 23485 := rs (se 3 (by rfl) ⟨4403, by rfl⟩) (B 8807 (by norm_num) ⟨4403, by rfl⟩ (by norm_num))
theorem R23489 : Reach 23489 := rs (se 2 (by rfl) ⟨8808, by rfl⟩) (B 17617 (by norm_num) ⟨8808, by rfl⟩ (by norm_num))
theorem R23493 : Reach 23493 := rs (se 4 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R23497 : Reach 23497 := rs (se 2 (by rfl) ⟨8811, by rfl⟩) (B 17623 (by norm_num) ⟨8811, by rfl⟩ (by norm_num))
theorem R89045 : Reach 89045 := rs (se 7 (by rfl) ⟨1043, by rfl⟩) (B 2087 (by norm_num) ⟨1043, by rfl⟩ (by norm_num))
theorem R23521 : Reach 23521 := rs (se 2 (by rfl) ⟨8820, by rfl⟩) (B 17641 (by norm_num) ⟨8820, by rfl⟩ (by norm_num))
theorem R23557 : Reach 23557 := rs (se 4 (by rfl) ⟨2208, by rfl⟩) (B 4417 (by norm_num) ⟨2208, by rfl⟩ (by norm_num))
theorem R23593 : Reach 23593 := rs (se 2 (by rfl) ⟨8847, by rfl⟩) (B 17695 (by norm_num) ⟨8847, by rfl⟩ (by norm_num))
theorem R23609 : Reach 23609 := rs (se 2 (by rfl) ⟨8853, by rfl⟩) (B 17707 (by norm_num) ⟨8853, by rfl⟩ (by norm_num))
theorem R23629 : Reach 23629 := rs (se 3 (by rfl) ⟨4430, by rfl⟩) (B 8861 (by norm_num) ⟨4430, by rfl⟩ (by norm_num))
theorem R23665 : Reach 23665 := rs (se 2 (by rfl) ⟨8874, by rfl⟩) (B 17749 (by norm_num) ⟨8874, by rfl⟩ (by norm_num))
theorem R23701 : Reach 23701 := rs (se 6 (by rfl) ⟨555, by rfl⟩) (B 1111 (by norm_num) ⟨555, by rfl⟩ (by norm_num))
theorem R23737 : Reach 23737 := rs (se 2 (by rfl) ⟨8901, by rfl⟩) (B 17803 (by norm_num) ⟨8901, by rfl⟩ (by norm_num))
theorem R23773 : Reach 23773 := rs (se 3 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R23809 : Reach 23809 := rs (se 2 (by rfl) ⟨8928, by rfl⟩) (B 17857 (by norm_num) ⟨8928, by rfl⟩ (by norm_num))
theorem R23845 : Reach 23845 := rs (se 4 (by rfl) ⟨2235, by rfl⟩) (B 4471 (by norm_num) ⟨2235, by rfl⟩ (by norm_num))
theorem R122165 : Reach 122165 := rs (se 5 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R23861 : Reach 23861 := rs (se 5 (by rfl) ⟨1118, by rfl⟩) (B 2237 (by norm_num) ⟨1118, by rfl⟩ (by norm_num))
theorem R23881 : Reach 23881 := rs (se 2 (by rfl) ⟨8955, by rfl⟩) (B 17911 (by norm_num) ⟨8955, by rfl⟩ (by norm_num))
theorem R23917 : Reach 23917 := rs (se 3 (by rfl) ⟨4484, by rfl⟩) (B 8969 (by norm_num) ⟨4484, by rfl⟩ (by norm_num))
theorem R23953 : Reach 23953 := rs (se 2 (by rfl) ⟨8982, by rfl⟩) (B 17965 (by norm_num) ⟨8982, by rfl⟩ (by norm_num))
theorem R23989 : Reach 23989 := rs (se 5 (by rfl) ⟨1124, by rfl⟩) (B 2249 (by norm_num) ⟨1124, by rfl⟩ (by norm_num))
theorem R24025 : Reach 24025 := rs (se 2 (by rfl) ⟨9009, by rfl⟩) (B 18019 (by norm_num) ⟨9009, by rfl⟩ (by norm_num))
theorem R56821 : Reach 56821 := rs (se 5 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R24061 : Reach 24061 := rs (se 3 (by rfl) ⟨4511, by rfl⟩) (B 9023 (by norm_num) ⟨4511, by rfl⟩ (by norm_num))
theorem R24085 : Reach 24085 := rs (se 6 (by rfl) ⟨564, by rfl⟩) (B 1129 (by norm_num) ⟨564, by rfl⟩ (by norm_num))
theorem R24097 : Reach 24097 := rs (se 2 (by rfl) ⟨9036, by rfl⟩) (B 18073 (by norm_num) ⟨9036, by rfl⟩ (by norm_num))
theorem R24133 : Reach 24133 := rs (se 4 (by rfl) ⟨2262, by rfl⟩) (B 4525 (by norm_num) ⟨2262, by rfl⟩ (by norm_num))
theorem R56933 : Reach 56933 := rs (se 4 (by rfl) ⟨5337, by rfl⟩) (B 10675 (by norm_num) ⟨5337, by rfl⟩ (by norm_num))
theorem R24169 : Reach 24169 := rs (se 2 (by rfl) ⟨9063, by rfl⟩) (B 18127 (by norm_num) ⟨9063, by rfl⟩ (by norm_num))
theorem R24181 : Reach 24181 := rs (se 5 (by rfl) ⟨1133, by rfl⟩) (B 2267 (by norm_num) ⟨1133, by rfl⟩ (by norm_num))
theorem R24205 : Reach 24205 := rs (se 3 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R24241 : Reach 24241 := rs (se 2 (by rfl) ⟨9090, by rfl⟩) (B 18181 (by norm_num) ⟨9090, by rfl⟩ (by norm_num))
theorem R24277 : Reach 24277 := rs (se 7 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R24305 : Reach 24305 := rs (se 2 (by rfl) ⟨9114, by rfl⟩) (B 18229 (by norm_num) ⟨9114, by rfl⟩ (by norm_num))
theorem R24313 : Reach 24313 := rs (se 2 (by rfl) ⟨9117, by rfl⟩) (B 18235 (by norm_num) ⟨9117, by rfl⟩ (by norm_num))
theorem R24349 : Reach 24349 := rs (se 3 (by rfl) ⟨4565, by rfl⟩) (B 9131 (by norm_num) ⟨4565, by rfl⟩ (by norm_num))
theorem R57125 : Reach 57125 := rs (se 4 (by rfl) ⟨5355, by rfl⟩) (B 10711 (by norm_num) ⟨5355, by rfl⟩ (by norm_num))
theorem R24385 : Reach 24385 := rs (se 2 (by rfl) ⟨9144, by rfl⟩) (B 18289 (by norm_num) ⟨9144, by rfl⟩ (by norm_num))
theorem R24421 : Reach 24421 := rs (se 4 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R24457 : Reach 24457 := rs (se 2 (by rfl) ⟨9171, by rfl⟩) (B 18343 (by norm_num) ⟨9171, by rfl⟩ (by norm_num))
theorem R24493 : Reach 24493 := rs (se 3 (by rfl) ⟨4592, by rfl⟩) (B 9185 (by norm_num) ⟨4592, by rfl⟩ (by norm_num))
theorem R24529 : Reach 24529 := rs (se 2 (by rfl) ⟨9198, by rfl⟩) (B 18397 (by norm_num) ⟨9198, by rfl⟩ (by norm_num))
theorem R24553 : Reach 24553 := rs (se 2 (by rfl) ⟨9207, by rfl⟩) (B 18415 (by norm_num) ⟨9207, by rfl⟩ (by norm_num))
theorem R24565 : Reach 24565 := rs (se 5 (by rfl) ⟨1151, by rfl⟩) (B 2303 (by norm_num) ⟨1151, by rfl⟩ (by norm_num))
theorem R24601 : Reach 24601 := rs (se 2 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R24637 : Reach 24637 := rs (se 3 (by rfl) ⟨4619, by rfl⟩) (B 9239 (by norm_num) ⟨4619, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R24673 : Reach 24673 := rs (se 2 (by rfl) ⟨9252, by rfl⟩) (B 18505 (by norm_num) ⟨9252, by rfl⟩ (by norm_num))
theorem R24709 : Reach 24709 := rs (se 4 (by rfl) ⟨2316, by rfl⟩) (B 4633 (by norm_num) ⟨2316, by rfl⟩ (by norm_num))
theorem R24745 : Reach 24745 := rs (se 2 (by rfl) ⟨9279, by rfl⟩) (B 18559 (by norm_num) ⟨9279, by rfl⟩ (by norm_num))
theorem R24781 : Reach 24781 := rs (se 3 (by rfl) ⟨4646, by rfl⟩) (B 9293 (by norm_num) ⟨4646, by rfl⟩ (by norm_num))
theorem R24817 : Reach 24817 := rs (se 2 (by rfl) ⟨9306, by rfl⟩) (B 18613 (by norm_num) ⟨9306, by rfl⟩ (by norm_num))
theorem R24853 : Reach 24853 := rs (se 6 (by rfl) ⟨582, by rfl⟩) (B 1165 (by norm_num) ⟨582, by rfl⟩ (by norm_num))
theorem R24889 : Reach 24889 := rs (se 2 (by rfl) ⟨9333, by rfl⟩) (B 18667 (by norm_num) ⟨9333, by rfl⟩ (by norm_num))
theorem R24925 : Reach 24925 := rs (se 3 (by rfl) ⟨4673, by rfl⟩) (B 9347 (by norm_num) ⟨4673, by rfl⟩ (by norm_num))
theorem R24961 : Reach 24961 := rs (se 2 (by rfl) ⟨9360, by rfl⟩) (B 18721 (by norm_num) ⟨9360, by rfl⟩ (by norm_num))
theorem R24997 : Reach 24997 := rs (se 4 (by rfl) ⟨2343, by rfl⟩) (B 4687 (by norm_num) ⟨2343, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R57797 : Reach 57797 := rs (se 4 (by rfl) ⟨5418, by rfl⟩) (B 10837 (by norm_num) ⟨5418, by rfl⟩ (by norm_num))
theorem R25033 : Reach 25033 := rs (se 2 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R25057 : Reach 25057 := rs (se 2 (by rfl) ⟨9396, by rfl⟩) (B 18793 (by norm_num) ⟨9396, by rfl⟩ (by norm_num))
theorem R25069 : Reach 25069 := rs (se 3 (by rfl) ⟨4700, by rfl⟩) (B 9401 (by norm_num) ⟨4700, by rfl⟩ (by norm_num))
theorem R25105 : Reach 25105 := rs (se 2 (by rfl) ⟨9414, by rfl⟩) (B 18829 (by norm_num) ⟨9414, by rfl⟩ (by norm_num))
theorem R25141 : Reach 25141 := rs (se 5 (by rfl) ⟨1178, by rfl⟩) (B 2357 (by norm_num) ⟨1178, by rfl⟩ (by norm_num))
theorem R25177 : Reach 25177 := rs (se 2 (by rfl) ⟨9441, by rfl⟩) (B 18883 (by norm_num) ⟨9441, by rfl⟩ (by norm_num))
theorem R25213 : Reach 25213 := rs (se 3 (by rfl) ⟨4727, by rfl⟩) (B 9455 (by norm_num) ⟨4727, by rfl⟩ (by norm_num))
theorem R25249 : Reach 25249 := rs (se 2 (by rfl) ⟨9468, by rfl⟩) (B 18937 (by norm_num) ⟨9468, by rfl⟩ (by norm_num))
theorem R25277 : Reach 25277 := rs (se 3 (by rfl) ⟨4739, by rfl⟩) (B 9479 (by norm_num) ⟨4739, by rfl⟩ (by norm_num))
theorem R25285 : Reach 25285 := rs (se 4 (by rfl) ⟨2370, by rfl⟩) (B 4741 (by norm_num) ⟨2370, by rfl⟩ (by norm_num))
theorem R25321 : Reach 25321 := rs (se 2 (by rfl) ⟨9495, by rfl⟩) (B 18991 (by norm_num) ⟨9495, by rfl⟩ (by norm_num))
theorem R58117 : Reach 58117 := rs (se 4 (by rfl) ⟨5448, by rfl⟩) (B 10897 (by norm_num) ⟨5448, by rfl⟩ (by norm_num))
theorem R25357 : Reach 25357 := rs (se 3 (by rfl) ⟨4754, by rfl⟩) (B 9509 (by norm_num) ⟨4754, by rfl⟩ (by norm_num))
theorem R25373 : Reach 25373 := rs (se 3 (by rfl) ⟨4757, by rfl⟩) (B 9515 (by norm_num) ⟨4757, by rfl⟩ (by norm_num))
theorem R25393 : Reach 25393 := rs (se 2 (by rfl) ⟨9522, by rfl⟩) (B 19045 (by norm_num) ⟨9522, by rfl⟩ (by norm_num))
theorem R25429 : Reach 25429 := rs (se 9 (by rfl) ⟨74, by rfl⟩) (B 149 (by norm_num) ⟨74, by rfl⟩ (by norm_num))
theorem R58229 : Reach 58229 := rs (se 5 (by rfl) ⟨2729, by rfl⟩) (B 5459 (by norm_num) ⟨2729, by rfl⟩ (by norm_num))
theorem R25465 : Reach 25465 := rs (se 2 (by rfl) ⟨9549, by rfl⟩) (B 19099 (by norm_num) ⟨9549, by rfl⟩ (by norm_num))
theorem R25501 : Reach 25501 := rs (se 3 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R25517 : Reach 25517 := rs (se 3 (by rfl) ⟨4784, by rfl⟩) (B 9569 (by norm_num) ⟨4784, by rfl⟩ (by norm_num))
theorem R25525 : Reach 25525 := rs (se 5 (by rfl) ⟨1196, by rfl⟩) (B 2393 (by norm_num) ⟨1196, by rfl⟩ (by norm_num))
theorem R25537 : Reach 25537 := rs (se 2 (by rfl) ⟨9576, by rfl⟩) (B 19153 (by norm_num) ⟨9576, by rfl⟩ (by norm_num))
theorem R25573 : Reach 25573 := rs (se 4 (by rfl) ⟨2397, by rfl⟩) (B 4795 (by norm_num) ⟨2397, by rfl⟩ (by norm_num))
theorem R25609 : Reach 25609 := rs (se 2 (by rfl) ⟨9603, by rfl⟩) (B 19207 (by norm_num) ⟨9603, by rfl⟩ (by norm_num))
theorem R25645 : Reach 25645 := rs (se 3 (by rfl) ⟨4808, by rfl⟩) (B 9617 (by norm_num) ⟨4808, by rfl⟩ (by norm_num))
theorem R58421 : Reach 58421 := rs (se 5 (by rfl) ⟨2738, by rfl⟩) (B 5477 (by norm_num) ⟨2738, by rfl⟩ (by norm_num))
theorem R25681 : Reach 25681 := rs (se 2 (by rfl) ⟨9630, by rfl⟩) (B 19261 (by norm_num) ⟨9630, by rfl⟩ (by norm_num))
theorem R25697 : Reach 25697 := rs (se 2 (by rfl) ⟨9636, by rfl⟩) (B 19273 (by norm_num) ⟨9636, by rfl⟩ (by norm_num))
theorem R25717 : Reach 25717 := rs (se 5 (by rfl) ⟨1205, by rfl⟩) (B 2411 (by norm_num) ⟨1205, by rfl⟩ (by norm_num))
theorem R25753 : Reach 25753 := rs (se 2 (by rfl) ⟨9657, by rfl⟩) (B 19315 (by norm_num) ⟨9657, by rfl⟩ (by norm_num))
theorem R25789 : Reach 25789 := rs (se 3 (by rfl) ⟨4835, by rfl⟩) (B 9671 (by norm_num) ⟨4835, by rfl⟩ (by norm_num))
theorem R25825 : Reach 25825 := rs (se 2 (by rfl) ⟨9684, by rfl⟩) (B 19369 (by norm_num) ⟨9684, by rfl⟩ (by norm_num))
theorem R25849 : Reach 25849 := rs (se 2 (by rfl) ⟨9693, by rfl⟩) (B 19387 (by norm_num) ⟨9693, by rfl⟩ (by norm_num))
theorem R25861 : Reach 25861 := rs (se 4 (by rfl) ⟨2424, by rfl⟩) (B 4849 (by norm_num) ⟨2424, by rfl⟩ (by norm_num))
theorem R25897 : Reach 25897 := rs (se 2 (by rfl) ⟨9711, by rfl⟩) (B 19423 (by norm_num) ⟨9711, by rfl⟩ (by norm_num))
theorem R25933 : Reach 25933 := rs (se 3 (by rfl) ⟨4862, by rfl⟩) (B 9725 (by norm_num) ⟨4862, by rfl⟩ (by norm_num))
theorem R25969 : Reach 25969 := rs (se 2 (by rfl) ⟨9738, by rfl⟩) (B 19477 (by norm_num) ⟨9738, by rfl⟩ (by norm_num))
theorem R26005 : Reach 26005 := rs (se 6 (by rfl) ⟨609, by rfl⟩) (B 1219 (by norm_num) ⟨609, by rfl⟩ (by norm_num))
theorem R26021 : Reach 26021 := rs (se 4 (by rfl) ⟨2439, by rfl⟩) (B 4879 (by norm_num) ⟨2439, by rfl⟩ (by norm_num))
theorem R26041 : Reach 26041 := rs (se 2 (by rfl) ⟨9765, by rfl⟩) (B 19531 (by norm_num) ⟨9765, by rfl⟩ (by norm_num))
theorem R26065 : Reach 26065 := rs (se 2 (by rfl) ⟨9774, by rfl⟩) (B 19549 (by norm_num) ⟨9774, by rfl⟩ (by norm_num))
theorem R26077 : Reach 26077 := rs (se 3 (by rfl) ⟨4889, by rfl⟩) (B 9779 (by norm_num) ⟨4889, by rfl⟩ (by norm_num))
theorem R26113 : Reach 26113 := rs (se 2 (by rfl) ⟨9792, by rfl⟩) (B 19585 (by norm_num) ⟨9792, by rfl⟩ (by norm_num))
theorem R26149 : Reach 26149 := rs (se 4 (by rfl) ⟨2451, by rfl⟩) (B 4903 (by norm_num) ⟨2451, by rfl⟩ (by norm_num))
theorem R26173 : Reach 26173 := rs (se 3 (by rfl) ⟨4907, by rfl⟩) (B 9815 (by norm_num) ⟨4907, by rfl⟩ (by norm_num))
theorem R26185 : Reach 26185 := rs (se 2 (by rfl) ⟨9819, by rfl⟩) (B 19639 (by norm_num) ⟨9819, by rfl⟩ (by norm_num))
theorem R26201 : Reach 26201 := rs (se 2 (by rfl) ⟨9825, by rfl⟩) (B 19651 (by norm_num) ⟨9825, by rfl⟩ (by norm_num))
theorem R58981 : Reach 58981 := rs (se 4 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R26221 : Reach 26221 := rs (se 3 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R26257 : Reach 26257 := rs (se 2 (by rfl) ⟨9846, by rfl⟩) (B 19693 (by norm_num) ⟨9846, by rfl⟩ (by norm_num))
theorem R190133 : Reach 190133 := rs (se 5 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R26293 : Reach 26293 := rs (se 5 (by rfl) ⟨1232, by rfl⟩) (B 2465 (by norm_num) ⟨1232, by rfl⟩ (by norm_num))
theorem R26329 : Reach 26329 := rs (se 2 (by rfl) ⟨9873, by rfl⟩) (B 19747 (by norm_num) ⟨9873, by rfl⟩ (by norm_num))
theorem R26345 : Reach 26345 := rs (se 2 (by rfl) ⟨9879, by rfl⟩) (B 19759 (by norm_num) ⟨9879, by rfl⟩ (by norm_num))
theorem R26365 : Reach 26365 := rs (se 3 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R26401 : Reach 26401 := rs (se 2 (by rfl) ⟨9900, by rfl⟩) (B 19801 (by norm_num) ⟨9900, by rfl⟩ (by norm_num))
theorem R26437 : Reach 26437 := rs (se 4 (by rfl) ⟨2478, by rfl⟩) (B 4957 (by norm_num) ⟨2478, by rfl⟩ (by norm_num))
theorem R26449 : Reach 26449 := rs (se 2 (by rfl) ⟨9918, by rfl⟩) (B 19837 (by norm_num) ⟨9918, by rfl⟩ (by norm_num))
theorem R26453 : Reach 26453 := rs (se 9 (by rfl) ⟨77, by rfl⟩) (B 155 (by norm_num) ⟨77, by rfl⟩ (by norm_num))
theorem R26497 : Reach 26497 := rs (se 2 (by rfl) ⟨9936, by rfl⟩) (B 19873 (by norm_num) ⟨9936, by rfl⟩ (by norm_num))
theorem R59413 : Reach 59413 := rs (se 6 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R26669 : Reach 26669 := rs (se 3 (by rfl) ⟨5000, by rfl⟩) (B 10001 (by norm_num) ⟨5000, by rfl⟩ (by norm_num))
theorem R26725 : Reach 26725 := rs (se 4 (by rfl) ⟨2505, by rfl⟩) (B 5011 (by norm_num) ⟨2505, by rfl⟩ (by norm_num))
theorem R26821 : Reach 26821 := rs (se 4 (by rfl) ⟨2514, by rfl⟩) (B 5029 (by norm_num) ⟨2514, by rfl⟩ (by norm_num))
theorem R27317 : Reach 27317 := rs (se 5 (by rfl) ⟨1280, by rfl⟩) (B 2561 (by norm_num) ⟨1280, by rfl⟩ (by norm_num))
theorem R27373 : Reach 27373 := rs (se 3 (by rfl) ⟨5132, by rfl⟩) (B 10265 (by norm_num) ⟨5132, by rfl⟩ (by norm_num))
theorem R92933 : Reach 92933 := rs (se 4 (by rfl) ⟨8712, by rfl⟩) (B 17425 (by norm_num) ⟨8712, by rfl⟩ (by norm_num))
theorem R27469 : Reach 27469 := rs (se 3 (by rfl) ⟨5150, by rfl⟩) (B 10301 (by norm_num) ⟨5150, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R125941 : Reach 125941 := rs (se 5 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R27805 : Reach 27805 := rs (se 3 (by rfl) ⟨5213, by rfl⟩) (B 10427 (by norm_num) ⟨5213, by rfl⟩ (by norm_num))
theorem R27965 : Reach 27965 := rs (se 3 (by rfl) ⟨5243, by rfl⟩) (B 10487 (by norm_num) ⟨5243, by rfl⟩ (by norm_num))
theorem R28021 : Reach 28021 := rs (se 5 (by rfl) ⟨1313, by rfl⟩) (B 2627 (by norm_num) ⟨1313, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R28117 : Reach 28117 := rs (se 7 (by rfl) ⟨329, by rfl⟩) (B 659 (by norm_num) ⟨329, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R28613 : Reach 28613 := rs (se 4 (by rfl) ⟨2682, by rfl⟩) (B 5365 (by norm_num) ⟨2682, by rfl⟩ (by norm_num))
theorem R28669 : Reach 28669 := rs (se 3 (by rfl) ⟨5375, by rfl⟩) (B 10751 (by norm_num) ⟨5375, by rfl⟩ (by norm_num))
theorem R28765 : Reach 28765 := rs (se 3 (by rfl) ⟨5393, by rfl⟩) (B 10787 (by norm_num) ⟨5393, by rfl⟩ (by norm_num))
theorem R159893 : Reach 159893 := rs (se 6 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R61829 : Reach 61829 := rs (se 4 (by rfl) ⟨5796, by rfl⟩) (B 11593 (by norm_num) ⟨5796, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R29261 : Reach 29261 := rs (se 3 (by rfl) ⟨5486, by rfl⟩) (B 10973 (by norm_num) ⟨5486, by rfl⟩ (by norm_num))
theorem R29317 : Reach 29317 := rs (se 4 (by rfl) ⟨2748, by rfl⟩) (B 5497 (by norm_num) ⟨2748, by rfl⟩ (by norm_num))
theorem R29413 : Reach 29413 := rs (se 4 (by rfl) ⟨2757, by rfl⟩) (B 5515 (by norm_num) ⟨2757, by rfl⟩ (by norm_num))
theorem R29821 : Reach 29821 := rs (se 3 (by rfl) ⟨5591, by rfl⟩) (B 11183 (by norm_num) ⟨5591, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R30005 : Reach 30005 := rs (se 5 (by rfl) ⟨1406, by rfl⟩) (B 2813 (by norm_num) ⟨1406, by rfl⟩ (by norm_num))
theorem R30029 : Reach 30029 := rs (se 3 (by rfl) ⟨5630, by rfl⟩) (B 11261 (by norm_num) ⟨5630, by rfl⟩ (by norm_num))
theorem R30053 : Reach 30053 := rs (se 4 (by rfl) ⟨2817, by rfl⟩) (B 5635 (by norm_num) ⟨2817, by rfl⟩ (by norm_num))
theorem R30077 : Reach 30077 := rs (se 3 (by rfl) ⟨5639, by rfl⟩) (B 11279 (by norm_num) ⟨5639, by rfl⟩ (by norm_num))
theorem R30101 : Reach 30101 := rs (se 6 (by rfl) ⟨705, by rfl⟩) (B 1411 (by norm_num) ⟨705, by rfl⟩ (by norm_num))
theorem R30125 : Reach 30125 := rs (se 3 (by rfl) ⟨5648, by rfl⟩) (B 11297 (by norm_num) ⟨5648, by rfl⟩ (by norm_num))
theorem R30149 : Reach 30149 := rs (se 4 (by rfl) ⟨2826, by rfl⟩) (B 5653 (by norm_num) ⟨2826, by rfl⟩ (by norm_num))
theorem R30173 : Reach 30173 := rs (se 3 (by rfl) ⟨5657, by rfl⟩) (B 11315 (by norm_num) ⟨5657, by rfl⟩ (by norm_num))
theorem R30197 : Reach 30197 := rs (se 5 (by rfl) ⟨1415, by rfl⟩) (B 2831 (by norm_num) ⟨1415, by rfl⟩ (by norm_num))
theorem R30221 : Reach 30221 := rs (se 3 (by rfl) ⟨5666, by rfl⟩) (B 11333 (by norm_num) ⟨5666, by rfl⟩ (by norm_num))
theorem R30245 : Reach 30245 := rs (se 4 (by rfl) ⟨2835, by rfl⟩) (B 5671 (by norm_num) ⟨2835, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R30269 : Reach 30269 := rs (se 3 (by rfl) ⟨5675, by rfl⟩) (B 11351 (by norm_num) ⟨5675, by rfl⟩ (by norm_num))
theorem R30293 : Reach 30293 := rs (se 8 (by rfl) ⟨177, by rfl⟩) (B 355 (by norm_num) ⟨177, by rfl⟩ (by norm_num))
theorem R30317 : Reach 30317 := rs (se 3 (by rfl) ⟨5684, by rfl⟩) (B 11369 (by norm_num) ⟨5684, by rfl⟩ (by norm_num))
theorem R30341 : Reach 30341 := rs (se 4 (by rfl) ⟨2844, by rfl⟩) (B 5689 (by norm_num) ⟨2844, by rfl⟩ (by norm_num))
theorem R30365 : Reach 30365 := rs (se 3 (by rfl) ⟨5693, by rfl⟩) (B 11387 (by norm_num) ⟨5693, by rfl⟩ (by norm_num))
theorem R30389 : Reach 30389 := rs (se 5 (by rfl) ⟨1424, by rfl⟩) (B 2849 (by norm_num) ⟨1424, by rfl⟩ (by norm_num))
theorem R63173 : Reach 63173 := rs (se 4 (by rfl) ⟨5922, by rfl⟩) (B 11845 (by norm_num) ⟨5922, by rfl⟩ (by norm_num))
theorem R30413 : Reach 30413 := rs (se 3 (by rfl) ⟨5702, by rfl⟩) (B 11405 (by norm_num) ⟨5702, by rfl⟩ (by norm_num))
theorem R30437 : Reach 30437 := rs (se 4 (by rfl) ⟨2853, by rfl⟩) (B 5707 (by norm_num) ⟨2853, by rfl⟩ (by norm_num))
theorem R30461 : Reach 30461 := rs (se 3 (by rfl) ⟨5711, by rfl⟩) (B 11423 (by norm_num) ⟨5711, by rfl⟩ (by norm_num))
theorem R30485 : Reach 30485 := rs (se 6 (by rfl) ⟨714, by rfl⟩) (B 1429 (by norm_num) ⟨714, by rfl⟩ (by norm_num))
theorem R30493 : Reach 30493 := rs (se 3 (by rfl) ⟨5717, by rfl⟩) (B 11435 (by norm_num) ⟨5717, by rfl⟩ (by norm_num))
theorem R30509 : Reach 30509 := rs (se 3 (by rfl) ⟨5720, by rfl⟩) (B 11441 (by norm_num) ⟨5720, by rfl⟩ (by norm_num))
theorem R30533 : Reach 30533 := rs (se 4 (by rfl) ⟨2862, by rfl⟩) (B 5725 (by norm_num) ⟨2862, by rfl⟩ (by norm_num))
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R30557 : Reach 30557 := rs (se 3 (by rfl) ⟨5729, by rfl⟩) (B 11459 (by norm_num) ⟨5729, by rfl⟩ (by norm_num))
theorem R30581 : Reach 30581 := rs (se 5 (by rfl) ⟨1433, by rfl⟩) (B 2867 (by norm_num) ⟨1433, by rfl⟩ (by norm_num))
theorem R30605 : Reach 30605 := rs (se 3 (by rfl) ⟨5738, by rfl⟩) (B 11477 (by norm_num) ⟨5738, by rfl⟩ (by norm_num))
theorem R30613 : Reach 30613 := rs (se 6 (by rfl) ⟨717, by rfl⟩) (B 1435 (by norm_num) ⟨717, by rfl⟩ (by norm_num))
theorem R30629 : Reach 30629 := rs (se 4 (by rfl) ⟨2871, by rfl⟩) (B 5743 (by norm_num) ⟨2871, by rfl⟩ (by norm_num))
theorem R63413 : Reach 63413 := rs (se 5 (by rfl) ⟨2972, by rfl⟩) (B 5945 (by norm_num) ⟨2972, by rfl⟩ (by norm_num))
theorem R30653 : Reach 30653 := rs (se 3 (by rfl) ⟨5747, by rfl⟩) (B 11495 (by norm_num) ⟨5747, by rfl⟩ (by norm_num))
theorem R30677 : Reach 30677 := rs (se 7 (by rfl) ⟨359, by rfl⟩) (B 719 (by norm_num) ⟨359, by rfl⟩ (by norm_num))
theorem R30701 : Reach 30701 := rs (se 3 (by rfl) ⟨5756, by rfl⟩) (B 11513 (by norm_num) ⟨5756, by rfl⟩ (by norm_num))
theorem R30709 : Reach 30709 := rs (se 5 (by rfl) ⟨1439, by rfl⟩) (B 2879 (by norm_num) ⟨1439, by rfl⟩ (by norm_num))
theorem R30725 : Reach 30725 := rs (se 4 (by rfl) ⟨2880, by rfl⟩) (B 5761 (by norm_num) ⟨2880, by rfl⟩ (by norm_num))
theorem R391189 : Reach 391189 := rs (se 6 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R30749 : Reach 30749 := rs (se 3 (by rfl) ⟨5765, by rfl⟩) (B 11531 (by norm_num) ⟨5765, by rfl⟩ (by norm_num))
theorem R30773 : Reach 30773 := rs (se 5 (by rfl) ⟨1442, by rfl⟩) (B 2885 (by norm_num) ⟨1442, by rfl⟩ (by norm_num))
theorem R30797 : Reach 30797 := rs (se 3 (by rfl) ⟨5774, by rfl⟩) (B 11549 (by norm_num) ⟨5774, by rfl⟩ (by norm_num))
theorem R30821 : Reach 30821 := rs (se 4 (by rfl) ⟨2889, by rfl⟩) (B 5779 (by norm_num) ⟨2889, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R30845 : Reach 30845 := rs (se 3 (by rfl) ⟨5783, by rfl⟩) (B 11567 (by norm_num) ⟨5783, by rfl⟩ (by norm_num))
theorem R30869 : Reach 30869 := rs (se 6 (by rfl) ⟨723, by rfl⟩) (B 1447 (by norm_num) ⟨723, by rfl⟩ (by norm_num))
theorem R30893 : Reach 30893 := rs (se 3 (by rfl) ⟨5792, by rfl⟩) (B 11585 (by norm_num) ⟨5792, by rfl⟩ (by norm_num))
theorem R30917 : Reach 30917 := rs (se 4 (by rfl) ⟨2898, by rfl⟩) (B 5797 (by norm_num) ⟨2898, by rfl⟩ (by norm_num))
theorem R30941 : Reach 30941 := rs (se 3 (by rfl) ⟨5801, by rfl⟩) (B 11603 (by norm_num) ⟨5801, by rfl⟩ (by norm_num))
theorem R30965 : Reach 30965 := rs (se 5 (by rfl) ⟨1451, by rfl⟩) (B 2903 (by norm_num) ⟨1451, by rfl⟩ (by norm_num))
theorem R30989 : Reach 30989 := rs (se 3 (by rfl) ⟨5810, by rfl⟩) (B 11621 (by norm_num) ⟨5810, by rfl⟩ (by norm_num))
theorem R31013 : Reach 31013 := rs (se 4 (by rfl) ⟨2907, by rfl⟩) (B 5815 (by norm_num) ⟨2907, by rfl⟩ (by norm_num))
theorem R31037 : Reach 31037 := rs (se 3 (by rfl) ⟨5819, by rfl⟩) (B 11639 (by norm_num) ⟨5819, by rfl⟩ (by norm_num))
theorem R31061 : Reach 31061 := rs (se 10 (by rfl) ⟨45, by rfl⟩) (B 91 (by norm_num) ⟨45, by rfl⟩ (by norm_num))
theorem R31085 : Reach 31085 := rs (se 3 (by rfl) ⟨5828, by rfl⟩) (B 11657 (by norm_num) ⟨5828, by rfl⟩ (by norm_num))
theorem R129397 : Reach 129397 := rs (se 5 (by rfl) ⟨6065, by rfl⟩) (B 12131 (by norm_num) ⟨6065, by rfl⟩ (by norm_num))
theorem R31109 : Reach 31109 := rs (se 4 (by rfl) ⟨2916, by rfl⟩) (B 5833 (by norm_num) ⟨2916, by rfl⟩ (by norm_num))
theorem R31133 : Reach 31133 := rs (se 3 (by rfl) ⟨5837, by rfl⟩) (B 11675 (by norm_num) ⟨5837, by rfl⟩ (by norm_num))
theorem R31157 : Reach 31157 := rs (se 5 (by rfl) ⟨1460, by rfl⟩) (B 2921 (by norm_num) ⟨1460, by rfl⟩ (by norm_num))
theorem R31181 : Reach 31181 := rs (se 3 (by rfl) ⟨5846, by rfl⟩) (B 11693 (by norm_num) ⟨5846, by rfl⟩ (by norm_num))
theorem R31205 : Reach 31205 := rs (se 4 (by rfl) ⟨2925, by rfl⟩) (B 5851 (by norm_num) ⟨2925, by rfl⟩ (by norm_num))
theorem R31229 : Reach 31229 := rs (se 3 (by rfl) ⟨5855, by rfl⟩) (B 11711 (by norm_num) ⟨5855, by rfl⟩ (by norm_num))
theorem R31253 : Reach 31253 := rs (se 6 (by rfl) ⟨732, by rfl⟩) (B 1465 (by norm_num) ⟨732, by rfl⟩ (by norm_num))
theorem R31277 : Reach 31277 := rs (se 3 (by rfl) ⟨5864, by rfl⟩) (B 11729 (by norm_num) ⟨5864, by rfl⟩ (by norm_num))
theorem R31301 : Reach 31301 := rs (se 4 (by rfl) ⟨2934, by rfl⟩) (B 5869 (by norm_num) ⟨2934, by rfl⟩ (by norm_num))
theorem R31325 : Reach 31325 := rs (se 3 (by rfl) ⟨5873, by rfl⟩) (B 11747 (by norm_num) ⟨5873, by rfl⟩ (by norm_num))
theorem R31349 : Reach 31349 := rs (se 5 (by rfl) ⟨1469, by rfl⟩) (B 2939 (by norm_num) ⟨1469, by rfl⟩ (by norm_num))
theorem R31373 : Reach 31373 := rs (se 3 (by rfl) ⟨5882, by rfl⟩) (B 11765 (by norm_num) ⟨5882, by rfl⟩ (by norm_num))
theorem R31397 : Reach 31397 := rs (se 4 (by rfl) ⟨2943, by rfl⟩) (B 5887 (by norm_num) ⟨2943, by rfl⟩ (by norm_num))
theorem R31421 : Reach 31421 := rs (se 3 (by rfl) ⟨5891, by rfl⟩) (B 11783 (by norm_num) ⟨5891, by rfl⟩ (by norm_num))
theorem R31445 : Reach 31445 := rs (se 7 (by rfl) ⟨368, by rfl⟩) (B 737 (by norm_num) ⟨368, by rfl⟩ (by norm_num))
theorem R31469 : Reach 31469 := rs (se 3 (by rfl) ⟨5900, by rfl⟩) (B 11801 (by norm_num) ⟨5900, by rfl⟩ (by norm_num))
theorem R31493 : Reach 31493 := rs (se 4 (by rfl) ⟨2952, by rfl⟩) (B 5905 (by norm_num) ⟨2952, by rfl⟩ (by norm_num))
theorem R31517 : Reach 31517 := rs (se 3 (by rfl) ⟨5909, by rfl⟩) (B 11819 (by norm_num) ⟨5909, by rfl⟩ (by norm_num))
theorem R31541 : Reach 31541 := rs (se 5 (by rfl) ⟨1478, by rfl⟩) (B 2957 (by norm_num) ⟨1478, by rfl⟩ (by norm_num))
theorem R31565 : Reach 31565 := rs (se 3 (by rfl) ⟨5918, by rfl⟩) (B 11837 (by norm_num) ⟨5918, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R31589 : Reach 31589 := rs (se 4 (by rfl) ⟨2961, by rfl⟩) (B 5923 (by norm_num) ⟨2961, by rfl⟩ (by norm_num))
theorem R31613 : Reach 31613 := rs (se 3 (by rfl) ⟨5927, by rfl⟩) (B 11855 (by norm_num) ⟨5927, by rfl⟩ (by norm_num))
theorem R31637 : Reach 31637 := rs (se 6 (by rfl) ⟨741, by rfl⟩) (B 1483 (by norm_num) ⟨741, by rfl⟩ (by norm_num))
theorem R64421 : Reach 64421 := rs (se 4 (by rfl) ⟨6039, by rfl⟩) (B 12079 (by norm_num) ⟨6039, by rfl⟩ (by norm_num))
theorem R31661 : Reach 31661 := rs (se 3 (by rfl) ⟨5936, by rfl⟩) (B 11873 (by norm_num) ⟨5936, by rfl⟩ (by norm_num))
theorem R31685 : Reach 31685 := rs (se 4 (by rfl) ⟨2970, by rfl⟩) (B 5941 (by norm_num) ⟨2970, by rfl⟩ (by norm_num))
theorem R31709 : Reach 31709 := rs (se 3 (by rfl) ⟨5945, by rfl⟩) (B 11891 (by norm_num) ⟨5945, by rfl⟩ (by norm_num))
theorem R31733 : Reach 31733 := rs (se 5 (by rfl) ⟨1487, by rfl⟩) (B 2975 (by norm_num) ⟨1487, by rfl⟩ (by norm_num))
theorem R31757 : Reach 31757 := rs (se 3 (by rfl) ⟨5954, by rfl⟩) (B 11909 (by norm_num) ⟨5954, by rfl⟩ (by norm_num))
theorem R31781 : Reach 31781 := rs (se 4 (by rfl) ⟨2979, by rfl⟩) (B 5959 (by norm_num) ⟨2979, by rfl⟩ (by norm_num))
theorem R31805 : Reach 31805 := rs (se 3 (by rfl) ⟨5963, by rfl⟩) (B 11927 (by norm_num) ⟨5963, by rfl⟩ (by norm_num))
theorem R31829 : Reach 31829 := rs (se 8 (by rfl) ⟨186, by rfl⟩) (B 373 (by norm_num) ⟨186, by rfl⟩ (by norm_num))
theorem R64597 : Reach 64597 := rs (se 8 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R31853 : Reach 31853 := rs (se 3 (by rfl) ⟨5972, by rfl⟩) (B 11945 (by norm_num) ⟨5972, by rfl⟩ (by norm_num))
theorem R31877 : Reach 31877 := rs (se 4 (by rfl) ⟨2988, by rfl⟩) (B 5977 (by norm_num) ⟨2988, by rfl⟩ (by norm_num))
theorem R31901 : Reach 31901 := rs (se 3 (by rfl) ⟨5981, by rfl⟩) (B 11963 (by norm_num) ⟨5981, by rfl⟩ (by norm_num))
theorem R31925 : Reach 31925 := rs (se 5 (by rfl) ⟨1496, by rfl⟩) (B 2993 (by norm_num) ⟨1496, by rfl⟩ (by norm_num))
theorem R31949 : Reach 31949 := rs (se 3 (by rfl) ⟨5990, by rfl⟩) (B 11981 (by norm_num) ⟨5990, by rfl⟩ (by norm_num))
theorem R31973 : Reach 31973 := rs (se 4 (by rfl) ⟨2997, by rfl⟩) (B 5995 (by norm_num) ⟨2997, by rfl⟩ (by norm_num))
theorem R31997 : Reach 31997 := rs (se 3 (by rfl) ⟨5999, by rfl⟩) (B 11999 (by norm_num) ⟨5999, by rfl⟩ (by norm_num))
theorem R32021 : Reach 32021 := rs (se 6 (by rfl) ⟨750, by rfl⟩) (B 1501 (by norm_num) ⟨750, by rfl⟩ (by norm_num))
theorem R32045 : Reach 32045 := rs (se 3 (by rfl) ⟨6008, by rfl⟩) (B 12017 (by norm_num) ⟨6008, by rfl⟩ (by norm_num))
theorem R32069 : Reach 32069 := rs (se 4 (by rfl) ⟨3006, by rfl⟩) (B 6013 (by norm_num) ⟨3006, by rfl⟩ (by norm_num))
theorem R32093 : Reach 32093 := rs (se 3 (by rfl) ⟨6017, by rfl⟩) (B 12035 (by norm_num) ⟨6017, by rfl⟩ (by norm_num))
theorem R32117 : Reach 32117 := rs (se 5 (by rfl) ⟨1505, by rfl⟩) (B 3011 (by norm_num) ⟨1505, by rfl⟩ (by norm_num))
theorem R32141 : Reach 32141 := rs (se 3 (by rfl) ⟨6026, by rfl⟩) (B 12053 (by norm_num) ⟨6026, by rfl⟩ (by norm_num))
theorem R32165 : Reach 32165 := rs (se 4 (by rfl) ⟨3015, by rfl⟩) (B 6031 (by norm_num) ⟨3015, by rfl⟩ (by norm_num))
theorem R32189 : Reach 32189 := rs (se 3 (by rfl) ⟨6035, by rfl⟩) (B 12071 (by norm_num) ⟨6035, by rfl⟩ (by norm_num))
theorem R32213 : Reach 32213 := rs (se 7 (by rfl) ⟨377, by rfl⟩) (B 755 (by norm_num) ⟨377, by rfl⟩ (by norm_num))
theorem R32237 : Reach 32237 := rs (se 3 (by rfl) ⟨6044, by rfl⟩) (B 12089 (by norm_num) ⟨6044, by rfl⟩ (by norm_num))
theorem R32261 : Reach 32261 := rs (se 4 (by rfl) ⟨3024, by rfl⟩) (B 6049 (by norm_num) ⟨3024, by rfl⟩ (by norm_num))
theorem R32285 : Reach 32285 := rs (se 3 (by rfl) ⟨6053, by rfl⟩) (B 12107 (by norm_num) ⟨6053, by rfl⟩ (by norm_num))
theorem R32309 : Reach 32309 := rs (se 5 (by rfl) ⟨1514, by rfl⟩) (B 3029 (by norm_num) ⟨1514, by rfl⟩ (by norm_num))
theorem R32333 : Reach 32333 := rs (se 3 (by rfl) ⟨6062, by rfl⟩) (B 12125 (by norm_num) ⟨6062, by rfl⟩ (by norm_num))
theorem R32357 : Reach 32357 := rs (se 4 (by rfl) ⟨3033, by rfl⟩) (B 6067 (by norm_num) ⟨3033, by rfl⟩ (by norm_num))
theorem R32381 : Reach 32381 := rs (se 3 (by rfl) ⟨6071, by rfl⟩) (B 12143 (by norm_num) ⟨6071, by rfl⟩ (by norm_num))
theorem R32405 : Reach 32405 := rs (se 6 (by rfl) ⟨759, by rfl⟩) (B 1519 (by norm_num) ⟨759, by rfl⟩ (by norm_num))
theorem R32429 : Reach 32429 := rs (se 3 (by rfl) ⟨6080, by rfl⟩) (B 12161 (by norm_num) ⟨6080, by rfl⟩ (by norm_num))
theorem R32453 : Reach 32453 := rs (se 4 (by rfl) ⟨3042, by rfl⟩) (B 6085 (by norm_num) ⟨3042, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R32477 : Reach 32477 := rs (se 3 (by rfl) ⟨6089, by rfl⟩) (B 12179 (by norm_num) ⟨6089, by rfl⟩ (by norm_num))
theorem R32501 : Reach 32501 := rs (se 5 (by rfl) ⟨1523, by rfl⟩) (B 3047 (by norm_num) ⟨1523, by rfl⟩ (by norm_num))
theorem R32509 : Reach 32509 := rs (se 3 (by rfl) ⟨6095, by rfl⟩) (B 12191 (by norm_num) ⟨6095, by rfl⟩ (by norm_num))
theorem R32525 : Reach 32525 := rs (se 3 (by rfl) ⟨6098, by rfl⟩) (B 12197 (by norm_num) ⟨6098, by rfl⟩ (by norm_num))
theorem R32549 : Reach 32549 := rs (se 4 (by rfl) ⟨3051, by rfl⟩) (B 6103 (by norm_num) ⟨3051, by rfl⟩ (by norm_num))
theorem R32573 : Reach 32573 := rs (se 3 (by rfl) ⟨6107, by rfl⟩) (B 12215 (by norm_num) ⟨6107, by rfl⟩ (by norm_num))
theorem R32597 : Reach 32597 := rs (se 9 (by rfl) ⟨95, by rfl⟩) (B 191 (by norm_num) ⟨95, by rfl⟩ (by norm_num))
theorem R32621 : Reach 32621 := rs (se 3 (by rfl) ⟨6116, by rfl⟩) (B 12233 (by norm_num) ⟨6116, by rfl⟩ (by norm_num))
theorem R32645 : Reach 32645 := rs (se 4 (by rfl) ⟨3060, by rfl⟩) (B 6121 (by norm_num) ⟨3060, by rfl⟩ (by norm_num))
theorem R32669 : Reach 32669 := rs (se 3 (by rfl) ⟨6125, by rfl⟩) (B 12251 (by norm_num) ⟨6125, by rfl⟩ (by norm_num))
theorem R32693 : Reach 32693 := rs (se 5 (by rfl) ⟨1532, by rfl⟩) (B 3065 (by norm_num) ⟨1532, by rfl⟩ (by norm_num))
theorem R32717 : Reach 32717 := rs (se 3 (by rfl) ⟨6134, by rfl⟩) (B 12269 (by norm_num) ⟨6134, by rfl⟩ (by norm_num))
theorem R32741 : Reach 32741 := rs (se 4 (by rfl) ⟨3069, by rfl⟩) (B 6139 (by norm_num) ⟨3069, by rfl⟩ (by norm_num))
theorem R32765 : Reach 32765 := rs (se 3 (by rfl) ⟨6143, by rfl⟩) (B 12287 (by norm_num) ⟨6143, by rfl⟩ (by norm_num))
theorem R32771 : Reach 32771 := rs (se 1 (by rfl) ⟨24578, by rfl⟩) R49157
theorem R32801 : Reach 32801 := rs (se 2 (by rfl) ⟨12300, by rfl⟩) R24601
theorem R32819 : Reach 32819 := rs (se 1 (by rfl) ⟨24614, by rfl⟩) R49229
theorem R32849 : Reach 32849 := rs (se 2 (by rfl) ⟨12318, by rfl⟩) R24637
theorem R32867 : Reach 32867 := rs (se 1 (by rfl) ⟨24650, by rfl⟩) R49301
theorem R32897 : Reach 32897 := rs (se 2 (by rfl) ⟨12336, by rfl⟩) R24673
theorem R32915 : Reach 32915 := rs (se 1 (by rfl) ⟨24686, by rfl⟩) R49373
theorem R65713 : Reach 65713 := rs (se 2 (by rfl) ⟨24642, by rfl⟩) R49285
theorem R32945 : Reach 32945 := rs (se 2 (by rfl) ⟨12354, by rfl⟩) R24709
theorem R32963 : Reach 32963 := rs (se 1 (by rfl) ⟨24722, by rfl⟩) R49445
theorem R32993 : Reach 32993 := rs (se 2 (by rfl) ⟨12372, by rfl⟩) R24745
theorem R33011 : Reach 33011 := rs (se 1 (by rfl) ⟨24758, by rfl⟩) R49517
theorem R33041 : Reach 33041 := rs (se 2 (by rfl) ⟨12390, by rfl⟩) R24781
theorem R33059 : Reach 33059 := rs (se 1 (by rfl) ⟨24794, by rfl⟩) R49589
theorem R33089 : Reach 33089 := rs (se 2 (by rfl) ⟨12408, by rfl⟩) R24817
theorem R65873 : Reach 65873 := rs (se 2 (by rfl) ⟨24702, by rfl⟩) R49405
theorem R33107 : Reach 33107 := rs (se 1 (by rfl) ⟨24830, by rfl⟩) R49661
theorem R33137 : Reach 33137 := rs (se 2 (by rfl) ⟨12426, by rfl⟩) R24853
theorem R33139 : Reach 33139 := rs (se 1 (by rfl) ⟨24854, by rfl⟩) R49709
theorem R33155 : Reach 33155 := rs (se 1 (by rfl) ⟨24866, by rfl⟩) R49733
theorem R33185 : Reach 33185 := rs (se 2 (by rfl) ⟨12444, by rfl⟩) R24889
theorem R33203 : Reach 33203 := rs (se 1 (by rfl) ⟨24902, by rfl⟩) R49805
theorem R98765 : Reach 98765 := rs (se 3 (by rfl) ⟨18518, by rfl⟩) R37037
theorem R33233 : Reach 33233 := rs (se 2 (by rfl) ⟨12462, by rfl⟩) R24925
theorem R33251 : Reach 33251 := rs (se 1 (by rfl) ⟨24938, by rfl⟩) R49877
theorem R33281 : Reach 33281 := rs (se 2 (by rfl) ⟨12480, by rfl⟩) R24961
theorem R33299 : Reach 33299 := rs (se 1 (by rfl) ⟨24974, by rfl⟩) R49949
theorem R33329 : Reach 33329 := rs (se 2 (by rfl) ⟨12498, by rfl⟩) R24997
theorem R33347 : Reach 33347 := rs (se 1 (by rfl) ⟨25010, by rfl⟩) R50021
theorem R33377 : Reach 33377 := rs (se 2 (by rfl) ⟨12516, by rfl⟩) R25033
theorem R33395 : Reach 33395 := rs (se 1 (by rfl) ⟨25046, by rfl⟩) R50093
theorem R33409 : Reach 33409 := rs (se 2 (by rfl) ⟨12528, by rfl⟩) R25057
theorem R33425 : Reach 33425 := rs (se 2 (by rfl) ⟨12534, by rfl⟩) R25069
theorem R33443 : Reach 33443 := rs (se 1 (by rfl) ⟨25082, by rfl⟩) R50165
theorem R33473 : Reach 33473 := rs (se 2 (by rfl) ⟨12552, by rfl⟩) R25105
theorem R33491 : Reach 33491 := rs (se 1 (by rfl) ⟨25118, by rfl⟩) R50237
theorem R33521 : Reach 33521 := rs (se 2 (by rfl) ⟨12570, by rfl⟩) R25141
theorem R33539 : Reach 33539 := rs (se 1 (by rfl) ⟨25154, by rfl⟩) R50309
theorem R33569 : Reach 33569 := rs (se 2 (by rfl) ⟨12588, by rfl⟩) R25177
theorem R33587 : Reach 33587 := rs (se 1 (by rfl) ⟨25190, by rfl⟩) R50381
theorem R33617 : Reach 33617 := rs (se 2 (by rfl) ⟨12606, by rfl⟩) R25213
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R33635 : Reach 33635 := rs (se 1 (by rfl) ⟨25226, by rfl⟩) R50453
theorem R33665 : Reach 33665 := rs (se 2 (by rfl) ⟨12624, by rfl⟩) R25249
theorem R33683 : Reach 33683 := rs (se 1 (by rfl) ⟨25262, by rfl⟩) R50525
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R33713 : Reach 33713 := rs (se 2 (by rfl) ⟨12642, by rfl⟩) R25285
theorem R33731 : Reach 33731 := rs (se 1 (by rfl) ⟨25298, by rfl⟩) R50597
theorem R33761 : Reach 33761 := rs (se 2 (by rfl) ⟨12660, by rfl⟩) R25321
theorem R33763 : Reach 33763 := rs (se 1 (by rfl) ⟨25322, by rfl⟩) R50645
theorem R66545 : Reach 66545 := rs (se 2 (by rfl) ⟨24954, by rfl⟩) R49909
theorem R33779 : Reach 33779 := rs (se 1 (by rfl) ⟨25334, by rfl⟩) R50669
theorem R33809 : Reach 33809 := rs (se 2 (by rfl) ⟨12678, by rfl⟩) R25357
theorem R33827 : Reach 33827 := rs (se 1 (by rfl) ⟨25370, by rfl⟩) R50741
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R33857 : Reach 33857 := rs (se 2 (by rfl) ⟨12696, by rfl⟩) R25393
theorem R33875 : Reach 33875 := rs (se 1 (by rfl) ⟨25406, by rfl⟩) R50813
theorem R33905 : Reach 33905 := rs (se 2 (by rfl) ⟨12714, by rfl⟩) R25429
theorem R33923 : Reach 33923 := rs (se 1 (by rfl) ⟨25442, by rfl⟩) R50885
theorem R33953 : Reach 33953 := rs (se 2 (by rfl) ⟨12732, by rfl⟩) R25465
theorem R33971 : Reach 33971 := rs (se 1 (by rfl) ⟨25478, by rfl⟩) R50957
theorem R66755 : Reach 66755 := rs (se 1 (by rfl) ⟨50066, by rfl⟩) R100133
theorem R34001 : Reach 34001 := rs (se 2 (by rfl) ⟨12750, by rfl⟩) R25501
theorem R34019 : Reach 34019 := rs (se 1 (by rfl) ⟨25514, by rfl⟩) R51029
theorem R34033 : Reach 34033 := rs (se 2 (by rfl) ⟨12762, by rfl⟩) R25525
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R34049 : Reach 34049 := rs (se 2 (by rfl) ⟨12768, by rfl⟩) R25537
theorem R34067 : Reach 34067 := rs (se 1 (by rfl) ⟨25550, by rfl⟩) R51101
theorem R34097 : Reach 34097 := rs (se 2 (by rfl) ⟨12786, by rfl⟩) R25573
theorem R34115 : Reach 34115 := rs (se 1 (by rfl) ⟨25586, by rfl⟩) R51173
theorem R34145 : Reach 34145 := rs (se 2 (by rfl) ⟨12804, by rfl⟩) R25609
theorem R34163 : Reach 34163 := rs (se 1 (by rfl) ⟨25622, by rfl⟩) R51245
theorem R34193 : Reach 34193 := rs (se 2 (by rfl) ⟨12822, by rfl⟩) R25645
theorem R34195 : Reach 34195 := rs (se 1 (by rfl) ⟨25646, by rfl⟩) R51293
theorem R34211 : Reach 34211 := rs (se 1 (by rfl) ⟨25658, by rfl⟩) R51317
theorem R34241 : Reach 34241 := rs (se 2 (by rfl) ⟨12840, by rfl⟩) R25681
theorem R34259 : Reach 34259 := rs (se 1 (by rfl) ⟨25694, by rfl⟩) R51389
theorem R34289 : Reach 34289 := rs (se 2 (by rfl) ⟨12858, by rfl⟩) R25717
theorem R34307 : Reach 34307 := rs (se 1 (by rfl) ⟨25730, by rfl⟩) R51461
theorem R34337 : Reach 34337 := rs (se 2 (by rfl) ⟨12876, by rfl⟩) R25753
theorem R34355 : Reach 34355 := rs (se 1 (by rfl) ⟨25766, by rfl⟩) R51533
theorem R34385 : Reach 34385 := rs (se 2 (by rfl) ⟨12894, by rfl⟩) R25789
theorem R34403 : Reach 34403 := rs (se 1 (by rfl) ⟨25802, by rfl⟩) R51605
theorem R34433 : Reach 34433 := rs (se 2 (by rfl) ⟨12912, by rfl⟩) R25825
theorem R34451 : Reach 34451 := rs (se 1 (by rfl) ⟨25838, by rfl⟩) R51677
theorem R34465 : Reach 34465 := rs (se 2 (by rfl) ⟨12924, by rfl⟩) R25849
theorem R132785 : Reach 132785 := rs (se 2 (by rfl) ⟨49794, by rfl⟩) R99589
theorem R34481 : Reach 34481 := rs (se 2 (by rfl) ⟨12930, by rfl⟩) R25861
theorem R34499 : Reach 34499 := rs (se 1 (by rfl) ⟨25874, by rfl⟩) R51749
theorem R34529 : Reach 34529 := rs (se 2 (by rfl) ⟨12948, by rfl⟩) R25897
theorem R34547 : Reach 34547 := rs (se 1 (by rfl) ⟨25910, by rfl⟩) R51821
theorem R34577 : Reach 34577 := rs (se 2 (by rfl) ⟨12966, by rfl⟩) R25933
theorem R34595 : Reach 34595 := rs (se 1 (by rfl) ⟨25946, by rfl⟩) R51893
theorem R34625 : Reach 34625 := rs (se 2 (by rfl) ⟨12984, by rfl⟩) R25969
theorem R34627 : Reach 34627 := rs (se 1 (by rfl) ⟨25970, by rfl⟩) R51941
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) R25277
theorem R34643 : Reach 34643 := rs (se 1 (by rfl) ⟨25982, by rfl⟩) R51965
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R34673 : Reach 34673 := rs (se 2 (by rfl) ⟨13002, by rfl⟩) R26005
theorem R34691 : Reach 34691 := rs (se 1 (by rfl) ⟨26018, by rfl⟩) R52037
theorem R34721 : Reach 34721 := rs (se 2 (by rfl) ⟨13020, by rfl⟩) R26041
theorem R34739 : Reach 34739 := rs (se 1 (by rfl) ⟨26054, by rfl⟩) R52109
theorem R34753 : Reach 34753 := rs (se 2 (by rfl) ⟨13032, by rfl⟩) R26065
theorem R34769 : Reach 34769 := rs (se 2 (by rfl) ⟨13038, by rfl⟩) R26077
theorem R34787 : Reach 34787 := rs (se 1 (by rfl) ⟨26090, by rfl⟩) R52181
theorem R34817 : Reach 34817 := rs (se 2 (by rfl) ⟨13056, by rfl⟩) R26113
theorem R34835 : Reach 34835 := rs (se 1 (by rfl) ⟨26126, by rfl⟩) R52253
theorem R34865 : Reach 34865 := rs (se 2 (by rfl) ⟨13074, by rfl⟩) R26149
theorem R34883 : Reach 34883 := rs (se 1 (by rfl) ⟨26162, by rfl⟩) R52325
theorem R67661 : Reach 67661 := rs (se 3 (by rfl) ⟨12686, by rfl⟩) R25373
theorem R34897 : Reach 34897 := rs (se 2 (by rfl) ⟨13086, by rfl⟩) R26173
theorem R34913 : Reach 34913 := rs (se 2 (by rfl) ⟨13092, by rfl⟩) R26185
theorem R34931 : Reach 34931 := rs (se 1 (by rfl) ⟨26198, by rfl⟩) R52397
theorem R67715 : Reach 67715 := rs (se 1 (by rfl) ⟨50786, by rfl⟩) R101573
theorem R34961 : Reach 34961 := rs (se 2 (by rfl) ⟨13110, by rfl⟩) R26221
theorem R34979 : Reach 34979 := rs (se 1 (by rfl) ⟨26234, by rfl⟩) R52469
theorem R35009 : Reach 35009 := rs (se 2 (by rfl) ⟨13128, by rfl⟩) R26257
theorem R133325 : Reach 133325 := rs (se 3 (by rfl) ⟨24998, by rfl⟩) R49997
theorem R35027 : Reach 35027 := rs (se 1 (by rfl) ⟨26270, by rfl⟩) R52541
theorem R35057 : Reach 35057 := rs (se 2 (by rfl) ⟨13146, by rfl⟩) R26293
theorem R35059 : Reach 35059 := rs (se 1 (by rfl) ⟨26294, by rfl⟩) R52589
theorem R35075 : Reach 35075 := rs (se 1 (by rfl) ⟨26306, by rfl⟩) R52613
theorem R35105 : Reach 35105 := rs (se 2 (by rfl) ⟨13164, by rfl⟩) R26329
theorem R35123 : Reach 35123 := rs (se 1 (by rfl) ⟨26342, by rfl⟩) R52685
theorem R35153 : Reach 35153 := rs (se 2 (by rfl) ⟨13182, by rfl⟩) R26365
theorem R35171 : Reach 35171 := rs (se 1 (by rfl) ⟨26378, by rfl⟩) R52757
theorem R35201 : Reach 35201 := rs (se 2 (by rfl) ⟨13200, by rfl⟩) R26401
theorem R35203 : Reach 35203 := rs (se 1 (by rfl) ⟨26402, by rfl⟩) R52805
theorem R231821 : Reach 231821 := rs (se 3 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R67985 : Reach 67985 := rs (se 2 (by rfl) ⟨25494, by rfl⟩) R50989
theorem R35219 : Reach 35219 := rs (se 1 (by rfl) ⟨26414, by rfl⟩) R52829
theorem R35249 : Reach 35249 := rs (se 2 (by rfl) ⟨13218, by rfl⟩) R26437
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) R25517
theorem R35329 : Reach 35329 := rs (se 2 (by rfl) ⟨13248, by rfl⟩) R26497
theorem R35363 : Reach 35363 := rs (se 1 (by rfl) ⟨26522, by rfl⟩) R53045
theorem R35491 : Reach 35491 := rs (se 1 (by rfl) ⟨26618, by rfl⟩) R53237
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R35633 : Reach 35633 := rs (se 2 (by rfl) ⟨13362, by rfl⟩) R26725
theorem R68525 : Reach 68525 := rs (se 3 (by rfl) ⟨12848, by rfl⟩) R25697
theorem R35761 : Reach 35761 := rs (se 2 (by rfl) ⟨13410, by rfl⟩) R26821
theorem R68579 : Reach 68579 := rs (se 1 (by rfl) ⟨51434, by rfl⟩) R102869
theorem R101411 : Reach 101411 := rs (se 1 (by rfl) ⟨76058, by rfl⟩) R152117
theorem R36035 : Reach 36035 := rs (se 1 (by rfl) ⟨27026, by rfl⟩) R54053
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R36067 : Reach 36067 := rs (se 1 (by rfl) ⟨27050, by rfl⟩) R54101
theorem R68849 : Reach 68849 := rs (se 2 (by rfl) ⟨25818, by rfl⟩) R51637
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) R38117
theorem R36131 : Reach 36131 := rs (se 1 (by rfl) ⟨27098, by rfl⟩) R54197
theorem R36163 : Reach 36163 := rs (se 1 (by rfl) ⟨27122, by rfl⟩) R54245
theorem R36227 : Reach 36227 := rs (se 1 (by rfl) ⟨27170, by rfl⟩) R54341
theorem R36355 : Reach 36355 := rs (se 1 (by rfl) ⟨27266, by rfl⟩) R54533
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R36497 : Reach 36497 := rs (se 2 (by rfl) ⟨13686, by rfl⟩) R27373
theorem R69389 : Reach 69389 := rs (se 3 (by rfl) ⟨13010, by rfl⟩) R26021
theorem R36625 : Reach 36625 := rs (se 2 (by rfl) ⟨13734, by rfl⟩) R27469
theorem R69443 : Reach 69443 := rs (se 1 (by rfl) ⟨52082, by rfl⟩) R104165
theorem R102221 : Reach 102221 := rs (se 3 (by rfl) ⟨19166, by rfl⟩) R38333
theorem R167921 : Reach 167921 := rs (se 2 (by rfl) ⟨62970, by rfl⟩) R125941
theorem R69635 : Reach 69635 := rs (se 1 (by rfl) ⟨52226, by rfl⟩) R104453
theorem R69713 : Reach 69713 := rs (se 2 (by rfl) ⟨26142, by rfl⟩) R52285
theorem R37073 : Reach 37073 := rs (se 2 (by rfl) ⟨13902, by rfl⟩) R27805
theorem R37091 : Reach 37091 := rs (se 1 (by rfl) ⟨27818, by rfl⟩) R55637
theorem R69869 : Reach 69869 := rs (se 3 (by rfl) ⟨13100, by rfl⟩) R26201
theorem R37219 : Reach 37219 := rs (se 1 (by rfl) ⟨27914, by rfl⟩) R55829
theorem R37361 : Reach 37361 := rs (se 2 (by rfl) ⟨14010, by rfl⟩) R28021
theorem R70253 : Reach 70253 := rs (se 3 (by rfl) ⟨13172, by rfl⟩) R26345
theorem R37489 : Reach 37489 := rs (se 2 (by rfl) ⟨14058, by rfl⟩) R28117
theorem R70307 : Reach 70307 := rs (se 1 (by rfl) ⟨52730, by rfl⟩) R105461
theorem R70541 : Reach 70541 := rs (se 3 (by rfl) ⟨13226, by rfl⟩) R26453
theorem R70577 : Reach 70577 := rs (se 2 (by rfl) ⟨26466, by rfl⟩) R52933
theorem R37955 : Reach 37955 := rs (se 1 (by rfl) ⟨28466, by rfl⟩) R56933
theorem R38083 : Reach 38083 := rs (se 1 (by rfl) ⟨28562, by rfl⟩) R57125
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R234737 : Reach 234737 := rs (se 2 (by rfl) ⟨88026, by rfl⟩) R176053
theorem R38225 : Reach 38225 := rs (se 2 (by rfl) ⟨14334, by rfl⟩) R28669
theorem R71117 : Reach 71117 := rs (se 3 (by rfl) ⟨13334, by rfl⟩) R26669
theorem R38353 : Reach 38353 := rs (se 2 (by rfl) ⟨14382, by rfl⟩) R28765
theorem R38531 : Reach 38531 := rs (se 1 (by rfl) ⟨28898, by rfl⟩) R57797
theorem R169613 : Reach 169613 := rs (se 3 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R38819 : Reach 38819 := rs (se 1 (by rfl) ⟨29114, by rfl⟩) R58229
theorem R38947 : Reach 38947 := rs (se 1 (by rfl) ⟨29210, by rfl⟩) R58421
theorem R39089 : Reach 39089 := rs (se 2 (by rfl) ⟨14658, by rfl⟩) R29317
theorem R39217 : Reach 39217 := rs (se 2 (by rfl) ⟨14706, by rfl⟩) R29413
theorem R72035 : Reach 72035 := rs (se 1 (by rfl) ⟨54026, by rfl⟩) R108053
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R72305 : Reach 72305 := rs (se 2 (by rfl) ⟨27114, by rfl⟩) R54229
theorem R105137 : Reach 105137 := rs (se 2 (by rfl) ⟨39426, by rfl⟩) R78853
theorem R39761 : Reach 39761 := rs (se 2 (by rfl) ⟨14910, by rfl⟩) R29821
theorem R564245 : Reach 564245 := rs (se 6 (by rfl) ⟨13224, by rfl⟩) R26449
theorem R72845 : Reach 72845 := rs (se 3 (by rfl) ⟨13658, by rfl⟩) R27317
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R40657 : Reach 40657 := rs (se 2 (by rfl) ⟨15246, by rfl⟩) R30493
theorem R40817 : Reach 40817 := rs (se 2 (by rfl) ⟨15306, by rfl⟩) R30613
theorem R73763 : Reach 73763 := rs (se 1 (by rfl) ⟨55322, by rfl⟩) R110645
theorem R106595 : Reach 106595 := rs (se 1 (by rfl) ⟨79946, by rfl⟩) R159893
theorem R41219 : Reach 41219 := rs (se 1 (by rfl) ⟨30914, by rfl⟩) R61829
theorem R106757 : Reach 106757 := rs (se 4 (by rfl) ⟨10008, by rfl⟩) R20017
theorem R74033 : Reach 74033 := rs (se 2 (by rfl) ⟨27762, by rfl⟩) R55525
theorem R172529 : Reach 172529 := rs (se 2 (by rfl) ⟨64698, by rfl⟩) R129397
theorem R74573 : Reach 74573 := rs (se 3 (by rfl) ⟨13982, by rfl⟩) R27965
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R107405 : Reach 107405 := rs (se 3 (by rfl) ⟨20138, by rfl⟩) R40277
theorem R42115 : Reach 42115 := rs (se 1 (by rfl) ⟨31586, by rfl⟩) R63173
theorem R42211 : Reach 42211 := rs (se 1 (by rfl) ⟨31658, by rfl⟩) R63317
theorem R42275 : Reach 42275 := rs (se 1 (by rfl) ⟨31706, by rfl⟩) R63413
theorem R75491 : Reach 75491 := rs (se 1 (by rfl) ⟨56618, by rfl⟩) R113237
theorem R42947 : Reach 42947 := rs (se 1 (by rfl) ⟨32210, by rfl⟩) R64421
theorem R75761 : Reach 75761 := rs (se 2 (by rfl) ⟨28410, by rfl⟩) R56821
theorem R43345 : Reach 43345 := rs (se 2 (by rfl) ⟨16254, by rfl⟩) R32509
theorem R76301 : Reach 76301 := rs (se 3 (by rfl) ⟨14306, by rfl⟩) R28613
theorem R43843 : Reach 43843 := rs (se 1 (by rfl) ⟨32882, by rfl⟩) R65765
theorem R306317 : Reach 306317 := rs (se 3 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R44401 : Reach 44401 := rs (se 2 (by rfl) ⟨16650, by rfl⟩) R33301
theorem R77219 : Reach 77219 := rs (se 1 (by rfl) ⟨57914, by rfl⟩) R115829
theorem R77489 : Reach 77489 := rs (se 2 (by rfl) ⟨29058, by rfl⟩) R58117
theorem R110321 : Reach 110321 := rs (se 2 (by rfl) ⟨41370, by rfl⟩) R82741
theorem R45073 : Reach 45073 := rs (se 2 (by rfl) ⟨16902, by rfl⟩) R33805
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) R82981
theorem R45233 : Reach 45233 := rs (se 2 (by rfl) ⟨16962, by rfl⟩) R33925
theorem R45251 : Reach 45251 := rs (se 1 (by rfl) ⟨33938, by rfl⟩) R67877
theorem R78029 : Reach 78029 := rs (se 3 (by rfl) ⟨14630, by rfl⟩) R29261
theorem R45521 : Reach 45521 := rs (se 2 (by rfl) ⟨17070, by rfl⟩) R34141
theorem R45539 : Reach 45539 := rs (se 1 (by rfl) ⟨34154, by rfl⟩) R68309
theorem R45809 : Reach 45809 := rs (se 2 (by rfl) ⟨17178, by rfl⟩) R34357
theorem R45827 : Reach 45827 := rs (se 1 (by rfl) ⟨34370, by rfl⟩) R68741
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R78641 : Reach 78641 := rs (se 2 (by rfl) ⟨29490, by rfl⟩) R58981
theorem R46097 : Reach 46097 := rs (se 2 (by rfl) ⟨17286, by rfl⟩) R34573
theorem R46115 : Reach 46115 := rs (se 1 (by rfl) ⟨34586, by rfl⟩) R69173
theorem R78947 : Reach 78947 := rs (se 1 (by rfl) ⟨59210, by rfl⟩) R118421
theorem R111779 : Reach 111779 := rs (se 1 (by rfl) ⟨83834, by rfl⟩) R167669
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) R33253
theorem R46385 : Reach 46385 := rs (se 2 (by rfl) ⟨17394, by rfl⟩) R34789
theorem R46403 : Reach 46403 := rs (se 1 (by rfl) ⟨34802, by rfl⟩) R69605
theorem R111941 : Reach 111941 := rs (se 4 (by rfl) ⟨10494, by rfl⟩) R20989
theorem R79217 : Reach 79217 := rs (se 2 (by rfl) ⟨29706, by rfl⟩) R59413
theorem R46577 : Reach 46577 := rs (se 2 (by rfl) ⟨17466, by rfl⟩) R34933
theorem R46673 : Reach 46673 := rs (se 2 (by rfl) ⟨17502, by rfl⟩) R35005
theorem R46691 : Reach 46691 := rs (se 1 (by rfl) ⟨35018, by rfl⟩) R70037
theorem R46961 : Reach 46961 := rs (se 2 (by rfl) ⟨17610, by rfl⟩) R35221
theorem R46979 : Reach 46979 := rs (se 1 (by rfl) ⟨35234, by rfl⟩) R70469
theorem R112589 : Reach 112589 := rs (se 3 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R47089 : Reach 47089 := rs (se 2 (by rfl) ⟨17658, by rfl⟩) R35317
theorem R145421 : Reach 145421 := rs (se 3 (by rfl) ⟨27266, by rfl⟩) R54533
theorem R47249 : Reach 47249 := rs (se 2 (by rfl) ⟨17718, by rfl⟩) R35437
theorem R47267 : Reach 47267 := rs (se 1 (by rfl) ⟨35450, by rfl⟩) R70901
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R47537 : Reach 47537 := rs (se 2 (by rfl) ⟨17826, by rfl⟩) R35653
theorem R47555 : Reach 47555 := rs (se 1 (by rfl) ⟨35666, by rfl⟩) R71333
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R47825 : Reach 47825 := rs (se 2 (by rfl) ⟨17934, by rfl⟩) R35869
theorem R47843 : Reach 47843 := rs (se 1 (by rfl) ⟨35882, by rfl⟩) R71765
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) R42557
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R48113 : Reach 48113 := rs (se 2 (by rfl) ⟨18042, by rfl⟩) R36085
theorem R48131 : Reach 48131 := rs (se 1 (by rfl) ⟨36098, by rfl⟩) R72197
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) R30413
theorem R48401 : Reach 48401 := rs (se 2 (by rfl) ⟨18150, by rfl⟩) R36301
theorem R48419 : Reach 48419 := rs (se 1 (by rfl) ⟨36314, by rfl⟩) R72629
theorem R48593 : Reach 48593 := rs (se 2 (by rfl) ⟨18222, by rfl⟩) R36445
theorem R81443 : Reach 81443 := rs (se 1 (by rfl) ⟨61082, by rfl⟩) R122165
theorem R48689 : Reach 48689 := rs (se 2 (by rfl) ⟨18258, by rfl⟩) R36517
theorem R48707 : Reach 48707 := rs (se 1 (by rfl) ⟨36530, by rfl⟩) R73061
theorem R114317 : Reach 114317 := rs (se 3 (by rfl) ⟨21434, by rfl⟩) R42869
theorem R114437 : Reach 114437 := rs (se 4 (by rfl) ⟨10728, by rfl⟩) R21457
theorem R48977 : Reach 48977 := rs (se 2 (by rfl) ⟨18366, by rfl⟩) R36733
theorem R48995 : Reach 48995 := rs (se 1 (by rfl) ⟨36746, by rfl⟩) R73493
theorem R442253 : Reach 442253 := rs (se 3 (by rfl) ⟨82922, by rfl⟩) R165845
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R49265 : Reach 49265 := rs (se 2 (by rfl) ⟨18474, by rfl⟩) R36949
theorem R49283 : Reach 49283 := rs (se 1 (by rfl) ⟨36962, by rfl⟩) R73925
theorem R49553 : Reach 49553 := rs (se 2 (by rfl) ⟨18582, by rfl⟩) R37165
theorem R49571 : Reach 49571 := rs (se 1 (by rfl) ⟨37178, by rfl⟩) R74357
theorem R49841 : Reach 49841 := rs (se 2 (by rfl) ⟨18690, by rfl⟩) R37381
theorem R49859 : Reach 49859 := rs (se 1 (by rfl) ⟨37394, by rfl⟩) R74789
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R115505 : Reach 115505 := rs (se 2 (by rfl) ⟨43314, by rfl⟩) R86629
theorem R50129 : Reach 50129 := rs (se 2 (by rfl) ⟨18798, by rfl⟩) R37597
theorem R50147 : Reach 50147 := rs (se 1 (by rfl) ⟨37610, by rfl⟩) R75221
theorem R50417 : Reach 50417 := rs (se 2 (by rfl) ⟨18906, by rfl⟩) R37813
theorem R50435 : Reach 50435 := rs (se 1 (by rfl) ⟨37826, by rfl⟩) R75653
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R50705 : Reach 50705 := rs (se 2 (by rfl) ⟨19014, by rfl⟩) R38029
theorem R50723 : Reach 50723 := rs (se 1 (by rfl) ⟨38042, by rfl⟩) R76085
theorem R50993 : Reach 50993 := rs (se 2 (by rfl) ⟨19122, by rfl⟩) R38245
theorem R51011 : Reach 51011 := rs (se 1 (by rfl) ⟨38258, by rfl⟩) R76517
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) R21853
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) R38341
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) R63013
theorem R51281 : Reach 51281 := rs (se 2 (by rfl) ⟨19230, by rfl⟩) R38461
theorem R51299 : Reach 51299 := rs (se 1 (by rfl) ⟨38474, by rfl⟩) R76949
theorem R51313 : Reach 51313 := rs (se 2 (by rfl) ⟨19242, by rfl⟩) R38485
theorem R116963 : Reach 116963 := rs (se 1 (by rfl) ⟨87722, by rfl⟩) R175445
theorem R51569 : Reach 51569 := rs (se 2 (by rfl) ⟨19338, by rfl⟩) R38677
theorem R51587 : Reach 51587 := rs (se 1 (by rfl) ⟨38690, by rfl⟩) R77381
theorem R117125 : Reach 117125 := rs (se 4 (by rfl) ⟨10980, by rfl⟩) R21961
theorem R51619 : Reach 51619 := rs (se 1 (by rfl) ⟨38714, by rfl⟩) R77429
theorem R117233 : Reach 117233 := rs (se 2 (by rfl) ⟨43962, by rfl⟩) R87925
theorem R51779 : Reach 51779 := rs (se 1 (by rfl) ⟨38834, by rfl⟩) R77669
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R51857 : Reach 51857 := rs (se 2 (by rfl) ⟨19446, by rfl⟩) R38893
theorem R51875 : Reach 51875 := rs (se 1 (by rfl) ⟨38906, by rfl⟩) R77813
theorem R84685 : Reach 84685 := rs (se 3 (by rfl) ⟨15878, by rfl⟩) R31757
theorem R52145 : Reach 52145 := rs (se 2 (by rfl) ⟨19554, by rfl⟩) R39109
theorem R52163 : Reach 52163 := rs (se 1 (by rfl) ⟨39122, by rfl⟩) R78245
theorem R117773 : Reach 117773 := rs (se 3 (by rfl) ⟨22082, by rfl⟩) R44165
theorem R52433 : Reach 52433 := rs (se 2 (by rfl) ⟨19662, by rfl⟩) R39325
theorem R52451 : Reach 52451 := rs (se 1 (by rfl) ⟨39338, by rfl⟩) R78677
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R52721 : Reach 52721 := rs (se 2 (by rfl) ⟨19770, by rfl⟩) R39541
theorem R52739 : Reach 52739 := rs (se 1 (by rfl) ⟨39554, by rfl⟩) R79109
theorem R20003 : Reach 20003 := rs (se 1 (by rfl) ⟨15002, by rfl⟩) R30005
theorem R52771 : Reach 52771 := rs (se 1 (by rfl) ⟨39578, by rfl⟩) R79157
theorem R20019 : Reach 20019 := rs (se 1 (by rfl) ⟨15014, by rfl⟩) R30029
theorem R20035 : Reach 20035 := rs (se 1 (by rfl) ⟨15026, by rfl⟩) R30053
theorem R20051 : Reach 20051 := rs (se 1 (by rfl) ⟨15038, by rfl⟩) R30077
theorem R20067 : Reach 20067 := rs (se 1 (by rfl) ⟨15050, by rfl⟩) R30101
theorem R20083 : Reach 20083 := rs (se 1 (by rfl) ⟨15062, by rfl⟩) R30125
theorem R20099 : Reach 20099 := rs (se 1 (by rfl) ⟨15074, by rfl⟩) R30149
theorem R20115 : Reach 20115 := rs (se 1 (by rfl) ⟨15086, by rfl⟩) R30173
theorem R20131 : Reach 20131 := rs (se 1 (by rfl) ⟨15098, by rfl⟩) R30197
theorem R52913 : Reach 52913 := rs (se 2 (by rfl) ⟨19842, by rfl⟩) R39685
theorem R20147 : Reach 20147 := rs (se 1 (by rfl) ⟨15110, by rfl⟩) R30221
theorem R20163 : Reach 20163 := rs (se 1 (by rfl) ⟨15122, by rfl⟩) R30245
theorem R20179 : Reach 20179 := rs (se 1 (by rfl) ⟨15134, by rfl⟩) R30269
theorem R20195 : Reach 20195 := rs (se 1 (by rfl) ⟨15146, by rfl⟩) R30293
theorem R20211 : Reach 20211 := rs (se 1 (by rfl) ⟨15158, by rfl⟩) R30317
theorem R20227 : Reach 20227 := rs (se 1 (by rfl) ⟨15170, by rfl⟩) R30341
theorem R20243 : Reach 20243 := rs (se 1 (by rfl) ⟨15182, by rfl⟩) R30365
theorem R20259 : Reach 20259 := rs (se 1 (by rfl) ⟨15194, by rfl⟩) R30389
theorem R20275 : Reach 20275 := rs (se 1 (by rfl) ⟨15206, by rfl⟩) R30413
theorem R20291 : Reach 20291 := rs (se 1 (by rfl) ⟨15218, by rfl⟩) R30437
theorem R20307 : Reach 20307 := rs (se 1 (by rfl) ⟨15230, by rfl⟩) R30461
theorem R20323 : Reach 20323 := rs (se 1 (by rfl) ⟨15242, by rfl⟩) R30485
theorem R20339 : Reach 20339 := rs (se 1 (by rfl) ⟨15254, by rfl⟩) R30509
theorem R20355 : Reach 20355 := rs (se 1 (by rfl) ⟨15266, by rfl⟩) R30533
theorem R20371 : Reach 20371 := rs (se 1 (by rfl) ⟨15278, by rfl⟩) R30557
theorem R20387 : Reach 20387 := rs (se 1 (by rfl) ⟨15290, by rfl⟩) R30581
theorem R118691 : Reach 118691 := rs (se 1 (by rfl) ⟨89018, by rfl⟩) R178037
theorem R20403 : Reach 20403 := rs (se 1 (by rfl) ⟨15302, by rfl⟩) R30605
theorem R20419 : Reach 20419 := rs (se 1 (by rfl) ⟨15314, by rfl⟩) R30629
theorem R20435 : Reach 20435 := rs (se 1 (by rfl) ⟨15326, by rfl⟩) R30653
theorem R20451 : Reach 20451 := rs (se 1 (by rfl) ⟨15338, by rfl⟩) R30677
theorem R20467 : Reach 20467 := rs (se 1 (by rfl) ⟨15350, by rfl⟩) R30701
theorem R20483 : Reach 20483 := rs (se 1 (by rfl) ⟨15362, by rfl⟩) R30725
theorem R20499 : Reach 20499 := rs (se 1 (by rfl) ⟨15374, by rfl⟩) R30749
theorem R20515 : Reach 20515 := rs (se 1 (by rfl) ⟨15386, by rfl⟩) R30773
theorem R20531 : Reach 20531 := rs (se 1 (by rfl) ⟨15398, by rfl⟩) R30797
theorem R20547 : Reach 20547 := rs (se 1 (by rfl) ⟨15410, by rfl⟩) R30821
theorem R20563 : Reach 20563 := rs (se 1 (by rfl) ⟨15422, by rfl⟩) R30845
theorem R20579 : Reach 20579 := rs (se 1 (by rfl) ⟨15434, by rfl⟩) R30869
theorem R86129 : Reach 86129 := rs (se 2 (by rfl) ⟨32298, by rfl⟩) R64597
theorem R20595 : Reach 20595 := rs (se 1 (by rfl) ⟨15446, by rfl⟩) R30893
theorem R20611 : Reach 20611 := rs (se 1 (by rfl) ⟨15458, by rfl⟩) R30917
theorem R20627 : Reach 20627 := rs (se 1 (by rfl) ⟨15470, by rfl⟩) R30941
theorem R20643 : Reach 20643 := rs (se 1 (by rfl) ⟨15482, by rfl⟩) R30965
theorem R20659 : Reach 20659 := rs (se 1 (by rfl) ⟨15494, by rfl⟩) R30989
theorem R20675 : Reach 20675 := rs (se 1 (by rfl) ⟨15506, by rfl⟩) R31013
theorem R20691 : Reach 20691 := rs (se 1 (by rfl) ⟨15518, by rfl⟩) R31037
theorem R20707 : Reach 20707 := rs (se 1 (by rfl) ⟨15530, by rfl⟩) R31061
theorem R20723 : Reach 20723 := rs (se 1 (by rfl) ⟨15542, by rfl⟩) R31085
theorem R20739 : Reach 20739 := rs (se 1 (by rfl) ⟨15554, by rfl⟩) R31109
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) R32357
theorem R20755 : Reach 20755 := rs (se 1 (by rfl) ⟨15566, by rfl⟩) R31133
theorem R20771 : Reach 20771 := rs (se 1 (by rfl) ⟨15578, by rfl⟩) R31157
theorem R20787 : Reach 20787 := rs (se 1 (by rfl) ⟨15590, by rfl⟩) R31181
theorem R20803 : Reach 20803 := rs (se 1 (by rfl) ⟨15602, by rfl⟩) R31205
theorem R53581 : Reach 53581 := rs (se 3 (by rfl) ⟨10046, by rfl⟩) R20093
theorem R20819 : Reach 20819 := rs (se 1 (by rfl) ⟨15614, by rfl⟩) R31229
theorem R20835 : Reach 20835 := rs (se 1 (by rfl) ⟨15626, by rfl⟩) R31253
theorem R20851 : Reach 20851 := rs (se 1 (by rfl) ⟨15638, by rfl⟩) R31277
theorem R20867 : Reach 20867 := rs (se 1 (by rfl) ⟨15650, by rfl⟩) R31301
theorem R20883 : Reach 20883 := rs (se 1 (by rfl) ⟨15662, by rfl⟩) R31325
theorem R20899 : Reach 20899 := rs (se 1 (by rfl) ⟨15674, by rfl⟩) R31349
theorem R20915 : Reach 20915 := rs (se 1 (by rfl) ⟨15686, by rfl⟩) R31373
theorem R20931 : Reach 20931 := rs (se 1 (by rfl) ⟨15698, by rfl⟩) R31397
theorem R20947 : Reach 20947 := rs (se 1 (by rfl) ⟨15710, by rfl⟩) R31421
theorem R20963 : Reach 20963 := rs (se 1 (by rfl) ⟨15722, by rfl⟩) R31445
theorem R20979 : Reach 20979 := rs (se 1 (by rfl) ⟨15734, by rfl⟩) R31469
theorem R20995 : Reach 20995 := rs (se 1 (by rfl) ⟨15746, by rfl⟩) R31493
theorem R21011 : Reach 21011 := rs (se 1 (by rfl) ⟨15758, by rfl⟩) R31517
theorem R21027 : Reach 21027 := rs (se 1 (by rfl) ⟨15770, by rfl⟩) R31541
theorem R21043 : Reach 21043 := rs (se 1 (by rfl) ⟨15782, by rfl⟩) R31565
theorem R21059 : Reach 21059 := rs (se 1 (by rfl) ⟨15794, by rfl⟩) R31589
theorem R21075 : Reach 21075 := rs (se 1 (by rfl) ⟨15806, by rfl⟩) R31613
theorem R21091 : Reach 21091 := rs (se 1 (by rfl) ⟨15818, by rfl⟩) R31637
theorem R21107 : Reach 21107 := rs (se 1 (by rfl) ⟨15830, by rfl⟩) R31661
theorem R21123 : Reach 21123 := rs (se 1 (by rfl) ⟨15842, by rfl⟩) R31685
theorem R53905 : Reach 53905 := rs (se 2 (by rfl) ⟨20214, by rfl⟩) R40429
theorem R21139 : Reach 21139 := rs (se 1 (by rfl) ⟨15854, by rfl⟩) R31709
theorem R21155 : Reach 21155 := rs (se 1 (by rfl) ⟨15866, by rfl⟩) R31733
theorem R21171 : Reach 21171 := rs (se 1 (by rfl) ⟨15878, by rfl⟩) R31757
theorem R21187 : Reach 21187 := rs (se 1 (by rfl) ⟨15890, by rfl⟩) R31781
theorem R21203 : Reach 21203 := rs (se 1 (by rfl) ⟨15902, by rfl⟩) R31805
theorem R21219 : Reach 21219 := rs (se 1 (by rfl) ⟨15914, by rfl⟩) R31829
theorem R21235 : Reach 21235 := rs (se 1 (by rfl) ⟨15926, by rfl⟩) R31853
theorem R21251 : Reach 21251 := rs (se 1 (by rfl) ⟨15938, by rfl⟩) R31877
theorem R21267 : Reach 21267 := rs (se 1 (by rfl) ⟨15950, by rfl⟩) R31901
theorem R21283 : Reach 21283 := rs (se 1 (by rfl) ⟨15962, by rfl⟩) R31925
theorem R21299 : Reach 21299 := rs (se 1 (by rfl) ⟨15974, by rfl⟩) R31949
theorem R21315 : Reach 21315 := rs (se 1 (by rfl) ⟨15986, by rfl⟩) R31973
theorem R21331 : Reach 21331 := rs (se 1 (by rfl) ⟨15998, by rfl⟩) R31997
theorem R21347 : Reach 21347 := rs (se 1 (by rfl) ⟨16010, by rfl⟩) R32021
theorem R21363 : Reach 21363 := rs (se 1 (by rfl) ⟨16022, by rfl⟩) R32045
theorem R21379 : Reach 21379 := rs (se 1 (by rfl) ⟨16034, by rfl⟩) R32069
theorem R21395 : Reach 21395 := rs (se 1 (by rfl) ⟨16046, by rfl⟩) R32093
theorem R54179 : Reach 54179 := rs (se 1 (by rfl) ⟨40634, by rfl⟩) R81269
theorem R21411 : Reach 21411 := rs (se 1 (by rfl) ⟨16058, by rfl⟩) R32117
theorem R21427 : Reach 21427 := rs (se 1 (by rfl) ⟨16070, by rfl⟩) R32141
theorem R21443 : Reach 21443 := rs (se 1 (by rfl) ⟨16082, by rfl⟩) R32165
theorem R21459 : Reach 21459 := rs (se 1 (by rfl) ⟨16094, by rfl⟩) R32189
theorem R21475 : Reach 21475 := rs (se 1 (by rfl) ⟨16106, by rfl⟩) R32213
theorem R21491 : Reach 21491 := rs (se 1 (by rfl) ⟨16118, by rfl⟩) R32237
theorem R21507 : Reach 21507 := rs (se 1 (by rfl) ⟨16130, by rfl⟩) R32261
theorem R21523 : Reach 21523 := rs (se 1 (by rfl) ⟨16142, by rfl⟩) R32285
theorem R21539 : Reach 21539 := rs (se 1 (by rfl) ⟨16154, by rfl⟩) R32309
theorem R21555 : Reach 21555 := rs (se 1 (by rfl) ⟨16166, by rfl⟩) R32333
theorem R21571 : Reach 21571 := rs (se 1 (by rfl) ⟨16178, by rfl⟩) R32357
theorem R21587 : Reach 21587 := rs (se 1 (by rfl) ⟨16190, by rfl⟩) R32381
theorem R54371 : Reach 54371 := rs (se 1 (by rfl) ⟨40778, by rfl⟩) R81557
theorem R21603 : Reach 21603 := rs (se 1 (by rfl) ⟨16202, by rfl⟩) R32405
theorem R21619 : Reach 21619 := rs (se 1 (by rfl) ⟨16214, by rfl⟩) R32429
theorem R21635 : Reach 21635 := rs (se 1 (by rfl) ⟨16226, by rfl⟩) R32453
theorem R21651 : Reach 21651 := rs (se 1 (by rfl) ⟨16238, by rfl⟩) R32477
theorem R21667 : Reach 21667 := rs (se 1 (by rfl) ⟨16250, by rfl⟩) R32501
theorem R21683 : Reach 21683 := rs (se 1 (by rfl) ⟨16262, by rfl⟩) R32525
theorem R21699 : Reach 21699 := rs (se 1 (by rfl) ⟨16274, by rfl⟩) R32549
theorem R21715 : Reach 21715 := rs (se 1 (by rfl) ⟨16286, by rfl⟩) R32573
theorem R21731 : Reach 21731 := rs (se 1 (by rfl) ⟨16298, by rfl⟩) R32597
theorem R21747 : Reach 21747 := rs (se 1 (by rfl) ⟨16310, by rfl⟩) R32621
theorem R21763 : Reach 21763 := rs (se 1 (by rfl) ⟨16322, by rfl⟩) R32645
theorem R21779 : Reach 21779 := rs (se 1 (by rfl) ⟨16334, by rfl⟩) R32669
theorem R21795 : Reach 21795 := rs (se 1 (by rfl) ⟨16346, by rfl⟩) R32693
theorem R21811 : Reach 21811 := rs (se 1 (by rfl) ⟨16358, by rfl⟩) R32717
theorem R21827 : Reach 21827 := rs (se 1 (by rfl) ⟨16370, by rfl⟩) R32741
theorem R21843 : Reach 21843 := rs (se 1 (by rfl) ⟨16382, by rfl⟩) R32765
theorem R21859 : Reach 21859 := rs (se 1 (by rfl) ⟨16394, by rfl⟩) R32789
theorem R21875 : Reach 21875 := rs (se 1 (by rfl) ⟨16406, by rfl⟩) R32813
theorem R21891 : Reach 21891 := rs (se 1 (by rfl) ⟨16418, by rfl⟩) R32837
theorem R21907 : Reach 21907 := rs (se 1 (by rfl) ⟨16430, by rfl⟩) R32861
theorem R21923 : Reach 21923 := rs (se 1 (by rfl) ⟨16442, by rfl⟩) R32885
theorem R21939 : Reach 21939 := rs (se 1 (by rfl) ⟨16454, by rfl⟩) R32909
theorem R21955 : Reach 21955 := rs (se 1 (by rfl) ⟨16466, by rfl⟩) R32933
theorem R21971 : Reach 21971 := rs (se 1 (by rfl) ⟨16478, by rfl⟩) R32957
theorem R21987 : Reach 21987 := rs (se 1 (by rfl) ⟨16490, by rfl⟩) R32981
theorem R22003 : Reach 22003 := rs (se 1 (by rfl) ⟨16502, by rfl⟩) R33005
theorem R22019 : Reach 22019 := rs (se 1 (by rfl) ⟨16514, by rfl⟩) R33029
theorem R22035 : Reach 22035 := rs (se 1 (by rfl) ⟨16526, by rfl⟩) R33053
theorem R22051 : Reach 22051 := rs (se 1 (by rfl) ⟨16538, by rfl⟩) R33077
theorem R87587 : Reach 87587 := rs (se 1 (by rfl) ⟨65690, by rfl⟩) R131381
theorem R87601 : Reach 87601 := rs (se 2 (by rfl) ⟨32850, by rfl⟩) R65701
theorem R22067 : Reach 22067 := rs (se 1 (by rfl) ⟨16550, by rfl⟩) R33101
theorem R22083 : Reach 22083 := rs (se 1 (by rfl) ⟨16562, by rfl⟩) R33125
theorem R22099 : Reach 22099 := rs (se 1 (by rfl) ⟨16574, by rfl⟩) R33149
theorem R22115 : Reach 22115 := rs (se 1 (by rfl) ⟨16586, by rfl⟩) R33173
theorem R22131 : Reach 22131 := rs (se 1 (by rfl) ⟨16598, by rfl⟩) R33197
theorem R22147 : Reach 22147 := rs (se 1 (by rfl) ⟨16610, by rfl⟩) R33221
theorem R22163 : Reach 22163 := rs (se 1 (by rfl) ⟨16622, by rfl⟩) R33245
theorem R22179 : Reach 22179 := rs (se 1 (by rfl) ⟨16634, by rfl⟩) R33269
theorem R22195 : Reach 22195 := rs (se 1 (by rfl) ⟨16646, by rfl⟩) R33293
theorem R22211 : Reach 22211 := rs (se 1 (by rfl) ⟨16658, by rfl⟩) R33317
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) R41029
theorem R54989 : Reach 54989 := rs (se 3 (by rfl) ⟨10310, by rfl⟩) R20621
theorem R22227 : Reach 22227 := rs (se 1 (by rfl) ⟨16670, by rfl⟩) R33341
theorem R22243 : Reach 22243 := rs (se 1 (by rfl) ⟨16682, by rfl⟩) R33365
theorem R22259 : Reach 22259 := rs (se 1 (by rfl) ⟨16694, by rfl⟩) R33389
theorem R22275 : Reach 22275 := rs (se 1 (by rfl) ⟨16706, by rfl⟩) R33413
theorem R22291 : Reach 22291 := rs (se 1 (by rfl) ⟨16718, by rfl⟩) R33437
theorem R22307 : Reach 22307 := rs (se 1 (by rfl) ⟨16730, by rfl⟩) R33461
theorem R22323 : Reach 22323 := rs (se 1 (by rfl) ⟨16742, by rfl⟩) R33485
theorem R22339 : Reach 22339 := rs (se 1 (by rfl) ⟨16754, by rfl⟩) R33509
theorem R22355 : Reach 22355 := rs (se 1 (by rfl) ⟨16766, by rfl⟩) R33533
theorem R22371 : Reach 22371 := rs (se 1 (by rfl) ⟨16778, by rfl⟩) R33557
theorem R22387 : Reach 22387 := rs (se 1 (by rfl) ⟨16790, by rfl⟩) R33581
theorem R22403 : Reach 22403 := rs (se 1 (by rfl) ⟨16802, by rfl⟩) R33605
theorem R55181 : Reach 55181 := rs (se 3 (by rfl) ⟨10346, by rfl⟩) R20693
theorem R22419 : Reach 22419 := rs (se 1 (by rfl) ⟨16814, by rfl⟩) R33629
theorem R22435 : Reach 22435 := rs (se 1 (by rfl) ⟨16826, by rfl⟩) R33653
theorem R22451 : Reach 22451 := rs (se 1 (by rfl) ⟨16838, by rfl⟩) R33677
theorem R22467 : Reach 22467 := rs (se 1 (by rfl) ⟨16850, by rfl⟩) R33701
theorem R22483 : Reach 22483 := rs (se 1 (by rfl) ⟨16862, by rfl⟩) R33725
theorem R22499 : Reach 22499 := rs (se 1 (by rfl) ⟨16874, by rfl⟩) R33749
theorem R22515 : Reach 22515 := rs (se 1 (by rfl) ⟨16886, by rfl⟩) R33773
theorem R22531 : Reach 22531 := rs (se 1 (by rfl) ⟨16898, by rfl⟩) R33797
theorem R55313 : Reach 55313 := rs (se 2 (by rfl) ⟨20742, by rfl⟩) R41485
theorem R22547 : Reach 22547 := rs (se 1 (by rfl) ⟨16910, by rfl⟩) R33821
theorem R22563 : Reach 22563 := rs (se 1 (by rfl) ⟨16922, by rfl⟩) R33845
theorem R22579 : Reach 22579 := rs (se 1 (by rfl) ⟨16934, by rfl⟩) R33869
theorem R55363 : Reach 55363 := rs (se 1 (by rfl) ⟨41522, by rfl⟩) R83045
theorem R22595 : Reach 22595 := rs (se 1 (by rfl) ⟨16946, by rfl⟩) R33893
theorem R22611 : Reach 22611 := rs (se 1 (by rfl) ⟨16958, by rfl⟩) R33917
theorem R22627 : Reach 22627 := rs (se 1 (by rfl) ⟨16970, by rfl⟩) R33941
theorem R22643 : Reach 22643 := rs (se 1 (by rfl) ⟨16982, by rfl⟩) R33965
theorem R22659 : Reach 22659 := rs (se 1 (by rfl) ⟨16994, by rfl⟩) R33989
theorem R22675 : Reach 22675 := rs (se 1 (by rfl) ⟨17006, by rfl⟩) R34013
theorem R22691 : Reach 22691 := rs (se 1 (by rfl) ⟨17018, by rfl⟩) R34037
theorem R22707 : Reach 22707 := rs (se 1 (by rfl) ⟨17030, by rfl⟩) R34061
theorem R22723 : Reach 22723 := rs (se 1 (by rfl) ⟨17042, by rfl⟩) R34085
theorem R55505 : Reach 55505 := rs (se 2 (by rfl) ⟨20814, by rfl⟩) R41629
theorem R22739 : Reach 22739 := rs (se 1 (by rfl) ⟨17054, by rfl⟩) R34109
theorem R22755 : Reach 22755 := rs (se 1 (by rfl) ⟨17066, by rfl⟩) R34133
theorem R22771 : Reach 22771 := rs (se 1 (by rfl) ⟨17078, by rfl⟩) R34157
theorem R22787 : Reach 22787 := rs (se 1 (by rfl) ⟨17090, by rfl⟩) R34181
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R22803 : Reach 22803 := rs (se 1 (by rfl) ⟨17102, by rfl⟩) R34205
theorem R22819 : Reach 22819 := rs (se 1 (by rfl) ⟨17114, by rfl⟩) R34229
theorem R22835 : Reach 22835 := rs (se 1 (by rfl) ⟨17126, by rfl⟩) R34253
theorem R22851 : Reach 22851 := rs (se 1 (by rfl) ⟨17138, by rfl⟩) R34277
theorem R22867 : Reach 22867 := rs (se 1 (by rfl) ⟨17150, by rfl⟩) R34301
theorem R22883 : Reach 22883 := rs (se 1 (by rfl) ⟨17162, by rfl⟩) R34325
theorem R22899 : Reach 22899 := rs (se 1 (by rfl) ⟨17174, by rfl⟩) R34349
theorem R22915 : Reach 22915 := rs (se 1 (by rfl) ⟨17186, by rfl⟩) R34373
theorem R22931 : Reach 22931 := rs (se 1 (by rfl) ⟨17198, by rfl⟩) R34397
theorem R22947 : Reach 22947 := rs (se 1 (by rfl) ⟨17210, by rfl⟩) R34421
theorem R22963 : Reach 22963 := rs (se 1 (by rfl) ⟨17222, by rfl⟩) R34445
theorem R22979 : Reach 22979 := rs (se 1 (by rfl) ⟨17234, by rfl⟩) R34469
theorem R22995 : Reach 22995 := rs (se 1 (by rfl) ⟨17246, by rfl⟩) R34493
theorem R23011 : Reach 23011 := rs (se 1 (by rfl) ⟨17258, by rfl⟩) R34517
theorem R23027 : Reach 23027 := rs (se 1 (by rfl) ⟨17270, by rfl⟩) R34541
theorem R23043 : Reach 23043 := rs (se 1 (by rfl) ⟨17282, by rfl⟩) R34565
theorem R23059 : Reach 23059 := rs (se 1 (by rfl) ⟨17294, by rfl⟩) R34589
theorem R23075 : Reach 23075 := rs (se 1 (by rfl) ⟨17306, by rfl⟩) R34613
theorem R23091 : Reach 23091 := rs (se 1 (by rfl) ⟨17318, by rfl⟩) R34637
theorem R23107 : Reach 23107 := rs (se 1 (by rfl) ⟨17330, by rfl⟩) R34661
theorem R23123 : Reach 23123 := rs (se 1 (by rfl) ⟨17342, by rfl⟩) R34685
theorem R23139 : Reach 23139 := rs (se 1 (by rfl) ⟨17354, by rfl⟩) R34709
theorem R23155 : Reach 23155 := rs (se 1 (by rfl) ⟨17366, by rfl⟩) R34733
theorem R23171 : Reach 23171 := rs (se 1 (by rfl) ⟨17378, by rfl⟩) R34757
theorem R23187 : Reach 23187 := rs (se 1 (by rfl) ⟨17390, by rfl⟩) R34781
theorem R23203 : Reach 23203 := rs (se 1 (by rfl) ⟨17402, by rfl⟩) R34805
theorem R23219 : Reach 23219 := rs (se 1 (by rfl) ⟨17414, by rfl⟩) R34829
theorem R23235 : Reach 23235 := rs (se 1 (by rfl) ⟨17426, by rfl⟩) R34853
theorem R23251 : Reach 23251 := rs (se 1 (by rfl) ⟨17438, by rfl⟩) R34877
theorem R23267 : Reach 23267 := rs (se 1 (by rfl) ⟨17450, by rfl⟩) R34901
theorem R23283 : Reach 23283 := rs (se 1 (by rfl) ⟨17462, by rfl⟩) R34925
theorem R23299 : Reach 23299 := rs (se 1 (by rfl) ⟨17474, by rfl⟩) R34949
theorem R23315 : Reach 23315 := rs (se 1 (by rfl) ⟨17486, by rfl⟩) R34973
theorem R23331 : Reach 23331 := rs (se 1 (by rfl) ⟨17498, by rfl⟩) R34997
theorem R23347 : Reach 23347 := rs (se 1 (by rfl) ⟨17510, by rfl⟩) R35021
theorem R23363 : Reach 23363 := rs (se 1 (by rfl) ⟨17522, by rfl⟩) R35045
theorem R23379 : Reach 23379 := rs (se 1 (by rfl) ⟨17534, by rfl⟩) R35069
theorem R23395 : Reach 23395 := rs (se 1 (by rfl) ⟨17546, by rfl⟩) R35093
theorem R56173 : Reach 56173 := rs (se 3 (by rfl) ⟨10532, by rfl⟩) R21065
theorem R23411 : Reach 23411 := rs (se 1 (by rfl) ⟨17558, by rfl⟩) R35117
theorem R23427 : Reach 23427 := rs (se 1 (by rfl) ⟨17570, by rfl⟩) R35141
theorem R23443 : Reach 23443 := rs (se 1 (by rfl) ⟨17582, by rfl⟩) R35165
theorem R23459 : Reach 23459 := rs (se 1 (by rfl) ⟨17594, by rfl⟩) R35189
theorem R23475 : Reach 23475 := rs (se 1 (by rfl) ⟨17606, by rfl⟩) R35213
theorem R23491 : Reach 23491 := rs (se 1 (by rfl) ⟨17618, by rfl⟩) R35237
theorem R89059 : Reach 89059 := rs (se 1 (by rfl) ⟨66794, by rfl⟩) R133589
theorem R23539 : Reach 23539 := rs (se 1 (by rfl) ⟨17654, by rfl⟩) R35309
theorem R56369 : Reach 56369 := rs (se 2 (by rfl) ⟨21138, by rfl⟩) R42277
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) R22861
theorem R23683 : Reach 23683 := rs (se 1 (by rfl) ⟨17762, by rfl⟩) R35525
theorem R56497 : Reach 56497 := rs (se 2 (by rfl) ⟨21186, by rfl⟩) R42373
theorem R23827 : Reach 23827 := rs (se 1 (by rfl) ⟨17870, by rfl⟩) R35741
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) R42493
theorem R23971 : Reach 23971 := rs (se 1 (by rfl) ⟨17978, by rfl⟩) R35957
theorem R56771 : Reach 56771 := rs (se 1 (by rfl) ⟨42578, by rfl⟩) R85157
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) R45893
theorem R24115 : Reach 24115 := rs (se 1 (by rfl) ⟨18086, by rfl⟩) R36173
theorem R56963 : Reach 56963 := rs (se 1 (by rfl) ⟨42722, by rfl⟩) R85445
theorem R24259 : Reach 24259 := rs (se 1 (by rfl) ⟨18194, by rfl⟩) R36389
theorem R24403 : Reach 24403 := rs (se 1 (by rfl) ⟨18302, by rfl⟩) R36605
theorem R24467 : Reach 24467 := rs (se 1 (by rfl) ⟨18350, by rfl⟩) R36701
theorem R24499 : Reach 24499 := rs (se 1 (by rfl) ⟨18374, by rfl⟩) R36749
theorem R24547 : Reach 24547 := rs (se 1 (by rfl) ⟨18410, by rfl⟩) R36821
theorem R24691 : Reach 24691 := rs (se 1 (by rfl) ⟨18518, by rfl⟩) R37037
theorem R57581 : Reach 57581 := rs (se 3 (by rfl) ⟨10796, by rfl⟩) R21593
theorem R24835 : Reach 24835 := rs (se 1 (by rfl) ⟨18626, by rfl⟩) R37253
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R24979 : Reach 24979 := rs (se 1 (by rfl) ⟨18734, by rfl⟩) R37469
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) R21665
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R25123 : Reach 25123 := rs (se 1 (by rfl) ⟨18842, by rfl⟩) R37685
theorem R57905 : Reach 57905 := rs (se 2 (by rfl) ⟨21714, by rfl⟩) R43429
theorem R57955 : Reach 57955 := rs (se 1 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R25267 : Reach 25267 := rs (se 1 (by rfl) ⟨18950, by rfl⟩) R37901
theorem R58097 : Reach 58097 := rs (se 2 (by rfl) ⟨21786, by rfl⟩) R43573
theorem R25363 : Reach 25363 := rs (se 1 (by rfl) ⟨19022, by rfl⟩) R38045
theorem R25411 : Reach 25411 := rs (se 1 (by rfl) ⟨19058, by rfl⟩) R38117
theorem R25555 : Reach 25555 := rs (se 1 (by rfl) ⟨19166, by rfl⟩) R38333
theorem R25699 : Reach 25699 := rs (se 1 (by rfl) ⟨19274, by rfl⟩) R38549
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R25843 : Reach 25843 := rs (se 1 (by rfl) ⟨19382, by rfl⟩) R38765
theorem R25859 : Reach 25859 := rs (se 1 (by rfl) ⟨19394, by rfl⟩) R38789
theorem R25987 : Reach 25987 := rs (se 1 (by rfl) ⟨19490, by rfl⟩) R38981
theorem R58765 : Reach 58765 := rs (se 3 (by rfl) ⟨11018, by rfl⟩) R22037
theorem R58801 : Reach 58801 := rs (se 2 (by rfl) ⟨22050, by rfl⟩) R44101
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R583109 : Reach 583109 := rs (se 4 (by rfl) ⟨54666, by rfl⟩) R109333
theorem R26131 : Reach 26131 := rs (se 1 (by rfl) ⟨19598, by rfl⟩) R39197
theorem R26275 : Reach 26275 := rs (se 1 (by rfl) ⟨19706, by rfl⟩) R39413
theorem R59089 : Reach 59089 := rs (se 2 (by rfl) ⟨22158, by rfl⟩) R44317
theorem R26419 : Reach 26419 := rs (se 1 (by rfl) ⟨19814, by rfl⟩) R39629
theorem R26563 : Reach 26563 := rs (se 1 (by rfl) ⟨19922, by rfl⟩) R39845
theorem R59363 : Reach 59363 := rs (se 1 (by rfl) ⟨44522, by rfl⟩) R89045
theorem R26659 : Reach 26659 := rs (se 1 (by rfl) ⟨19994, by rfl⟩) R39989
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) R46901
theorem R26993 : Reach 26993 := rs (se 2 (by rfl) ⟨10122, by rfl⟩) R20245
theorem R125297 : Reach 125297 := rs (se 2 (by rfl) ⟨46986, by rfl⟩) R93973
theorem R27155 : Reach 27155 := rs (se 1 (by rfl) ⟨20366, by rfl⟩) R40733
theorem R158435 : Reach 158435 := rs (se 1 (by rfl) ⟨118826, by rfl⟩) R237653
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) R69925
theorem R27697 : Reach 27697 := rs (se 2 (by rfl) ⟨10386, by rfl⟩) R20773
theorem R60497 : Reach 60497 := rs (se 2 (by rfl) ⟨22686, by rfl⟩) R45373
theorem R27793 : Reach 27793 := rs (se 2 (by rfl) ⟨10422, by rfl⟩) R20845
theorem R27859 : Reach 27859 := rs (se 1 (by rfl) ⟨20894, by rfl⟩) R41789
theorem R27907 : Reach 27907 := rs (se 1 (by rfl) ⟨20930, by rfl⟩) R41861
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) R45517
theorem R27955 : Reach 27955 := rs (se 1 (by rfl) ⟨20966, by rfl⟩) R41933
theorem R28081 : Reach 28081 := rs (se 2 (by rfl) ⟨10530, by rfl⟩) R21061
theorem R28289 : Reach 28289 := rs (se 2 (by rfl) ⟨10608, by rfl⟩) R21217
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) R22901
theorem R28307 : Reach 28307 := rs (se 1 (by rfl) ⟨21230, by rfl⟩) R42461
theorem R126755 : Reach 126755 := rs (se 1 (by rfl) ⟨95066, by rfl⟩) R190133
theorem R28451 : Reach 28451 := rs (se 1 (by rfl) ⟨21338, by rfl⟩) R42677
theorem R61681 : Reach 61681 := rs (se 2 (by rfl) ⟨23130, by rfl⟩) R46261
theorem R28993 : Reach 28993 := rs (se 2 (by rfl) ⟨10872, by rfl⟩) R21745
theorem R29089 : Reach 29089 := rs (se 2 (by rfl) ⟨10908, by rfl⟩) R21817
theorem R29107 : Reach 29107 := rs (se 1 (by rfl) ⟨21830, by rfl⟩) R43661
theorem R29155 : Reach 29155 := rs (se 1 (by rfl) ⟨21866, by rfl⟩) R43733
theorem R61955 : Reach 61955 := rs (se 1 (by rfl) ⟨46466, by rfl⟩) R92933
theorem R29251 : Reach 29251 := rs (se 1 (by rfl) ⟨21938, by rfl⟩) R43877
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) R35573
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R127757 : Reach 127757 := rs (se 3 (by rfl) ⟨23954, by rfl⟩) R47909
theorem R29585 : Reach 29585 := rs (se 2 (by rfl) ⟨11094, by rfl⟩) R22189
theorem R193549 : Reach 193549 := rs (se 3 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R29713 : Reach 29713 := rs (se 2 (by rfl) ⟨11142, by rfl⟩) R22285
theorem R29747 : Reach 29747 := rs (se 1 (by rfl) ⟨22310, by rfl⟩) R44621
theorem R30017 : Reach 30017 := rs (se 2 (by rfl) ⟨11256, by rfl⟩) R22513
theorem R30035 : Reach 30035 := rs (se 1 (by rfl) ⟨22526, by rfl⟩) R45053
theorem R30065 : Reach 30065 := rs (se 2 (by rfl) ⟨11274, by rfl⟩) R22549
theorem R521585 : Reach 521585 := rs (se 2 (by rfl) ⟨195594, by rfl⟩) R391189
theorem R30083 : Reach 30083 := rs (se 1 (by rfl) ⟨22562, by rfl⟩) R45125
theorem R30113 : Reach 30113 := rs (se 2 (by rfl) ⟨11292, by rfl⟩) R22585
theorem R30131 : Reach 30131 := rs (se 1 (by rfl) ⟨22598, by rfl⟩) R45197
theorem R30161 : Reach 30161 := rs (se 2 (by rfl) ⟨11310, by rfl⟩) R22621
theorem R30179 : Reach 30179 := rs (se 1 (by rfl) ⟨22634, by rfl⟩) R45269
theorem R62957 : Reach 62957 := rs (se 3 (by rfl) ⟨11804, by rfl⟩) R23609
theorem R30209 : Reach 30209 := rs (se 2 (by rfl) ⟨11328, by rfl⟩) R22657
theorem R30227 : Reach 30227 := rs (se 1 (by rfl) ⟨22670, by rfl⟩) R45341
theorem R30257 : Reach 30257 := rs (se 2 (by rfl) ⟨11346, by rfl⟩) R22693
theorem R30275 : Reach 30275 := rs (se 1 (by rfl) ⟨22706, by rfl⟩) R45413
theorem R30305 : Reach 30305 := rs (se 2 (by rfl) ⟨11364, by rfl⟩) R22729
theorem R30323 : Reach 30323 := rs (se 1 (by rfl) ⟨22742, by rfl⟩) R45485
theorem R30353 : Reach 30353 := rs (se 2 (by rfl) ⟨11382, by rfl⟩) R22765
theorem R30371 : Reach 30371 := rs (se 1 (by rfl) ⟨22778, by rfl⟩) R45557
theorem R63139 : Reach 63139 := rs (se 1 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R30385 : Reach 30385 := rs (se 2 (by rfl) ⟨11394, by rfl⟩) R22789
theorem R30401 : Reach 30401 := rs (se 2 (by rfl) ⟨11400, by rfl⟩) R22801
theorem R30419 : Reach 30419 := rs (se 1 (by rfl) ⟨22814, by rfl⟩) R45629
theorem R30449 : Reach 30449 := rs (se 2 (by rfl) ⟨11418, by rfl⟩) R22837
theorem R30467 : Reach 30467 := rs (se 1 (by rfl) ⟨22850, by rfl⟩) R45701
theorem R30497 : Reach 30497 := rs (se 2 (by rfl) ⟨11436, by rfl⟩) R22873
theorem R30515 : Reach 30515 := rs (se 1 (by rfl) ⟨22886, by rfl⟩) R45773
theorem R30545 : Reach 30545 := rs (se 2 (by rfl) ⟨11454, by rfl⟩) R22909
theorem R30563 : Reach 30563 := rs (se 1 (by rfl) ⟨22922, by rfl⟩) R45845
theorem R30593 : Reach 30593 := rs (se 2 (by rfl) ⟨11472, by rfl⟩) R22945
theorem R30611 : Reach 30611 := rs (se 1 (by rfl) ⟨22958, by rfl⟩) R45917
theorem R30641 : Reach 30641 := rs (se 2 (by rfl) ⟨11490, by rfl⟩) R22981
theorem R30659 : Reach 30659 := rs (se 1 (by rfl) ⟨22994, by rfl⟩) R45989
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) R24181
theorem R30689 : Reach 30689 := rs (se 2 (by rfl) ⟨11508, by rfl⟩) R23017
theorem R30707 : Reach 30707 := rs (se 1 (by rfl) ⟨23030, by rfl⟩) R46061
theorem R30721 : Reach 30721 := rs (se 2 (by rfl) ⟨11520, by rfl⟩) R23041
theorem R30737 : Reach 30737 := rs (se 2 (by rfl) ⟨11526, by rfl⟩) R23053
theorem R30755 : Reach 30755 := rs (se 1 (by rfl) ⟨23066, by rfl⟩) R46133
theorem R30785 : Reach 30785 := rs (se 2 (by rfl) ⟨11544, by rfl⟩) R23089
theorem R30803 : Reach 30803 := rs (se 1 (by rfl) ⟨23102, by rfl⟩) R46205
theorem R30833 : Reach 30833 := rs (se 2 (by rfl) ⟨11562, by rfl⟩) R23125
theorem R30851 : Reach 30851 := rs (se 1 (by rfl) ⟨23138, by rfl⟩) R46277
theorem R63629 : Reach 63629 := rs (se 3 (by rfl) ⟨11930, by rfl⟩) R23861
theorem R30881 : Reach 30881 := rs (se 2 (by rfl) ⟨11580, by rfl⟩) R23161
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R30899 : Reach 30899 := rs (se 1 (by rfl) ⟨23174, by rfl⟩) R46349
theorem R30929 : Reach 30929 := rs (se 2 (by rfl) ⟨11598, by rfl⟩) R23197
theorem R30947 : Reach 30947 := rs (se 1 (by rfl) ⟨23210, by rfl⟩) R46421
theorem R30977 : Reach 30977 := rs (se 2 (by rfl) ⟨11616, by rfl⟩) R23233
theorem R30995 : Reach 30995 := rs (se 1 (by rfl) ⟨23246, by rfl⟩) R46493
theorem R31025 : Reach 31025 := rs (se 2 (by rfl) ⟨11634, by rfl⟩) R23269
theorem R31043 : Reach 31043 := rs (se 1 (by rfl) ⟨23282, by rfl⟩) R46565
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R31073 : Reach 31073 := rs (se 2 (by rfl) ⟨11652, by rfl⟩) R23305
theorem R31091 : Reach 31091 := rs (se 1 (by rfl) ⟨23318, by rfl⟩) R46637
theorem R31121 : Reach 31121 := rs (se 2 (by rfl) ⟨11670, by rfl⟩) R23341
theorem R31139 : Reach 31139 := rs (se 1 (by rfl) ⟨23354, by rfl⟩) R46709
theorem R31169 : Reach 31169 := rs (se 2 (by rfl) ⟨11688, by rfl⟩) R23377
theorem R31187 : Reach 31187 := rs (se 1 (by rfl) ⟨23390, by rfl⟩) R46781
theorem R31217 : Reach 31217 := rs (se 2 (by rfl) ⟨11706, by rfl⟩) R23413
theorem R31235 : Reach 31235 := rs (se 1 (by rfl) ⟨23426, by rfl⟩) R46853
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R31265 : Reach 31265 := rs (se 2 (by rfl) ⟨11724, by rfl⟩) R23449
theorem R31283 : Reach 31283 := rs (se 1 (by rfl) ⟨23462, by rfl⟩) R46925
theorem R31313 : Reach 31313 := rs (se 2 (by rfl) ⟨11742, by rfl⟩) R23485
theorem R31331 : Reach 31331 := rs (se 1 (by rfl) ⟨23498, by rfl⟩) R46997
theorem R31361 : Reach 31361 := rs (se 2 (by rfl) ⟨11760, by rfl⟩) R23521
theorem R31379 : Reach 31379 := rs (se 1 (by rfl) ⟨23534, by rfl⟩) R47069
theorem R31409 : Reach 31409 := rs (se 2 (by rfl) ⟨11778, by rfl⟩) R23557
theorem R31427 : Reach 31427 := rs (se 1 (by rfl) ⟨23570, by rfl⟩) R47141
theorem R31457 : Reach 31457 := rs (se 2 (by rfl) ⟨11796, by rfl⟩) R23593
theorem R31475 : Reach 31475 := rs (se 1 (by rfl) ⟨23606, by rfl⟩) R47213
theorem R31505 : Reach 31505 := rs (se 2 (by rfl) ⟨11814, by rfl⟩) R23629
theorem R31523 : Reach 31523 := rs (se 1 (by rfl) ⟨23642, by rfl⟩) R47285
theorem R31553 : Reach 31553 := rs (se 2 (by rfl) ⟨11832, by rfl⟩) R23665
theorem R31571 : Reach 31571 := rs (se 1 (by rfl) ⟨23678, by rfl⟩) R47357
theorem R31601 : Reach 31601 := rs (se 2 (by rfl) ⟨11850, by rfl⟩) R23701
theorem R31619 : Reach 31619 := rs (se 1 (by rfl) ⟨23714, by rfl⟩) R47429
theorem R31649 : Reach 31649 := rs (se 2 (by rfl) ⟨11868, by rfl⟩) R23737
theorem R31667 : Reach 31667 := rs (se 1 (by rfl) ⟨23750, by rfl⟩) R47501
theorem R31697 : Reach 31697 := rs (se 2 (by rfl) ⟨11886, by rfl⟩) R23773
theorem R31715 : Reach 31715 := rs (se 1 (by rfl) ⟨23786, by rfl⟩) R47573
theorem R31745 : Reach 31745 := rs (se 2 (by rfl) ⟨11904, by rfl⟩) R23809
theorem R31763 : Reach 31763 := rs (se 1 (by rfl) ⟨23822, by rfl⟩) R47645
theorem R31793 : Reach 31793 := rs (se 2 (by rfl) ⟨11922, by rfl⟩) R23845
theorem R31811 : Reach 31811 := rs (se 1 (by rfl) ⟨23858, by rfl⟩) R47717
theorem R31841 : Reach 31841 := rs (se 2 (by rfl) ⟨11940, by rfl⟩) R23881
theorem R31843 : Reach 31843 := rs (se 1 (by rfl) ⟨23882, by rfl⟩) R47765
theorem R31859 : Reach 31859 := rs (se 1 (by rfl) ⟨23894, by rfl⟩) R47789
theorem R31889 : Reach 31889 := rs (se 2 (by rfl) ⟨11958, by rfl⟩) R23917
theorem R31907 : Reach 31907 := rs (se 1 (by rfl) ⟨23930, by rfl⟩) R47861
theorem R31937 : Reach 31937 := rs (se 2 (by rfl) ⟨11976, by rfl⟩) R23953
theorem R31955 : Reach 31955 := rs (se 1 (by rfl) ⟨23966, by rfl⟩) R47933
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R31985 : Reach 31985 := rs (se 2 (by rfl) ⟨11994, by rfl⟩) R23989
theorem R32003 : Reach 32003 := rs (se 1 (by rfl) ⟨24002, by rfl⟩) R48005
theorem R32033 : Reach 32033 := rs (se 2 (by rfl) ⟨12012, by rfl⟩) R24025
theorem R64813 : Reach 64813 := rs (se 3 (by rfl) ⟨12152, by rfl⟩) R24305
theorem R32051 : Reach 32051 := rs (se 1 (by rfl) ⟨24038, by rfl⟩) R48077
theorem R32081 : Reach 32081 := rs (se 2 (by rfl) ⟨12030, by rfl⟩) R24061
theorem R32099 : Reach 32099 := rs (se 1 (by rfl) ⟨24074, by rfl⟩) R48149
theorem R32113 : Reach 32113 := rs (se 2 (by rfl) ⟨12042, by rfl⟩) R24085
theorem R32129 : Reach 32129 := rs (se 2 (by rfl) ⟨12048, by rfl⟩) R24097
theorem R32147 : Reach 32147 := rs (se 1 (by rfl) ⟨24110, by rfl⟩) R48221
theorem R32177 : Reach 32177 := rs (se 2 (by rfl) ⟨12066, by rfl⟩) R24133
theorem R32179 : Reach 32179 := rs (se 1 (by rfl) ⟨24134, by rfl⟩) R48269
theorem R32195 : Reach 32195 := rs (se 1 (by rfl) ⟨24146, by rfl⟩) R48293
theorem R32225 : Reach 32225 := rs (se 2 (by rfl) ⟨12084, by rfl⟩) R24169
theorem R32243 : Reach 32243 := rs (se 1 (by rfl) ⟨24182, by rfl⟩) R48365
theorem R32273 : Reach 32273 := rs (se 2 (by rfl) ⟨12102, by rfl⟩) R24205
theorem R32291 : Reach 32291 := rs (se 1 (by rfl) ⟨24218, by rfl⟩) R48437
theorem R32321 : Reach 32321 := rs (se 2 (by rfl) ⟨12120, by rfl⟩) R24241
theorem R32339 : Reach 32339 := rs (se 1 (by rfl) ⟨24254, by rfl⟩) R48509
theorem R32369 : Reach 32369 := rs (se 2 (by rfl) ⟨12138, by rfl⟩) R24277
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R32387 : Reach 32387 := rs (se 1 (by rfl) ⟨24290, by rfl⟩) R48581
theorem R32417 : Reach 32417 := rs (se 2 (by rfl) ⟨12156, by rfl⟩) R24313
theorem R97955 : Reach 97955 := rs (se 1 (by rfl) ⟨73466, by rfl⟩) R146933
theorem R32435 : Reach 32435 := rs (se 1 (by rfl) ⟨24326, by rfl⟩) R48653
theorem R32465 : Reach 32465 := rs (se 2 (by rfl) ⟨12174, by rfl⟩) R24349
theorem R32483 : Reach 32483 := rs (se 1 (by rfl) ⟨24362, by rfl⟩) R48725
theorem R32513 : Reach 32513 := rs (se 2 (by rfl) ⟨12192, by rfl⟩) R24385
theorem R32531 : Reach 32531 := rs (se 1 (by rfl) ⟨24398, by rfl⟩) R48797
theorem R32561 : Reach 32561 := rs (se 2 (by rfl) ⟨12210, by rfl⟩) R24421
theorem R32579 : Reach 32579 := rs (se 1 (by rfl) ⟨24434, by rfl⟩) R48869
theorem R32609 : Reach 32609 := rs (se 2 (by rfl) ⟨12228, by rfl⟩) R24457
theorem R32627 : Reach 32627 := rs (se 1 (by rfl) ⟨24470, by rfl⟩) R48941
theorem R32657 : Reach 32657 := rs (se 2 (by rfl) ⟨12246, by rfl⟩) R24493
theorem R32675 : Reach 32675 := rs (se 1 (by rfl) ⟨24506, by rfl⟩) R49013
theorem R32705 : Reach 32705 := rs (se 2 (by rfl) ⟨12264, by rfl⟩) R24529
theorem R163781 : Reach 163781 := rs (se 4 (by rfl) ⟨15354, by rfl⟩) R30709
theorem R32723 : Reach 32723 := rs (se 1 (by rfl) ⟨24542, by rfl⟩) R49085
theorem R32737 : Reach 32737 := rs (se 2 (by rfl) ⟨12276, by rfl⟩) R24553
theorem R32753 : Reach 32753 := rs (se 2 (by rfl) ⟨12282, by rfl⟩) R24565
theorem R32843 : Reach 32843 := rs (se 1 (by rfl) ⟨24632, by rfl⟩) R49265
theorem R32855 : Reach 32855 := rs (se 1 (by rfl) ⟨24641, by rfl⟩) R49283
theorem R32921 : Reach 32921 := rs (se 2 (by rfl) ⟨12345, by rfl⟩) R24691
theorem R33035 : Reach 33035 := rs (se 1 (by rfl) ⟨24776, by rfl⟩) R49553
theorem R33047 : Reach 33047 := rs (se 1 (by rfl) ⟨24785, by rfl⟩) R49571
theorem R65843 : Reach 65843 := rs (se 1 (by rfl) ⟨49382, by rfl⟩) R98765
theorem R33113 : Reach 33113 := rs (se 2 (by rfl) ⟨12417, by rfl⟩) R24835
theorem R33227 : Reach 33227 := rs (se 1 (by rfl) ⟨24920, by rfl⟩) R49841
theorem R33239 : Reach 33239 := rs (se 1 (by rfl) ⟨24929, by rfl⟩) R49859
theorem R33305 : Reach 33305 := rs (se 2 (by rfl) ⟨12489, by rfl⟩) R24979
theorem R33419 : Reach 33419 := rs (se 1 (by rfl) ⟨25064, by rfl⟩) R50129
theorem R33431 : Reach 33431 := rs (se 1 (by rfl) ⟨25073, by rfl⟩) R50147
theorem R33497 : Reach 33497 := rs (se 2 (by rfl) ⟨12561, by rfl⟩) R25123
theorem R33611 : Reach 33611 := rs (se 1 (by rfl) ⟨25208, by rfl⟩) R50417
theorem R33623 : Reach 33623 := rs (se 1 (by rfl) ⟨25217, by rfl⟩) R50435
theorem R33689 : Reach 33689 := rs (se 2 (by rfl) ⟨12633, by rfl⟩) R25267
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) R49891
theorem R33803 : Reach 33803 := rs (se 1 (by rfl) ⟨25352, by rfl⟩) R50705
theorem R33815 : Reach 33815 := rs (se 1 (by rfl) ⟨25361, by rfl⟩) R50723
theorem R33817 : Reach 33817 := rs (se 2 (by rfl) ⟨12681, by rfl⟩) R25363
theorem R33881 : Reach 33881 := rs (se 2 (by rfl) ⟨12705, by rfl⟩) R25411
theorem R33995 : Reach 33995 := rs (se 1 (by rfl) ⟨25496, by rfl⟩) R50993
theorem R34007 : Reach 34007 := rs (se 1 (by rfl) ⟨25505, by rfl⟩) R51011
theorem R132313 : Reach 132313 := rs (se 2 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R34073 : Reach 34073 := rs (se 2 (by rfl) ⟨12777, by rfl⟩) R25555
theorem R34187 : Reach 34187 := rs (se 1 (by rfl) ⟨25640, by rfl⟩) R51281
theorem R34199 : Reach 34199 := rs (se 1 (by rfl) ⟨25649, by rfl⟩) R51299
theorem R34265 : Reach 34265 := rs (se 2 (by rfl) ⟨12849, by rfl⟩) R25699
theorem R34379 : Reach 34379 := rs (se 1 (by rfl) ⟨25784, by rfl⟩) R51569
theorem R34391 : Reach 34391 := rs (se 1 (by rfl) ⟨25793, by rfl⟩) R51587
theorem R34457 : Reach 34457 := rs (se 2 (by rfl) ⟨12921, by rfl⟩) R25843
theorem R34519 : Reach 34519 := rs (se 1 (by rfl) ⟨25889, by rfl⟩) R51779
theorem R34571 : Reach 34571 := rs (se 1 (by rfl) ⟨25928, by rfl⟩) R51857
theorem R34583 : Reach 34583 := rs (se 1 (by rfl) ⟨25937, by rfl⟩) R51875
theorem R34649 : Reach 34649 := rs (se 2 (by rfl) ⟨12993, by rfl⟩) R25987
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R34763 : Reach 34763 := rs (se 1 (by rfl) ⟨26072, by rfl⟩) R52145
theorem R34775 : Reach 34775 := rs (se 1 (by rfl) ⟨26081, by rfl⟩) R52163
theorem R67607 : Reach 67607 := rs (se 1 (by rfl) ⟨50705, by rfl⟩) R101411
theorem R34841 : Reach 34841 := rs (se 2 (by rfl) ⟨13065, by rfl⟩) R26131
theorem R34955 : Reach 34955 := rs (se 1 (by rfl) ⟨26216, by rfl⟩) R52433
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R34967 : Reach 34967 := rs (se 1 (by rfl) ⟨26225, by rfl⟩) R52451
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R35033 : Reach 35033 := rs (se 2 (by rfl) ⟨13137, by rfl⟩) R26275
theorem R35147 : Reach 35147 := rs (se 1 (by rfl) ⟨26360, by rfl⟩) R52721
theorem R35159 : Reach 35159 := rs (se 1 (by rfl) ⟨26369, by rfl⟩) R52739
theorem R35225 : Reach 35225 := rs (se 2 (by rfl) ⟨13209, by rfl⟩) R26419
theorem R35275 : Reach 35275 := rs (se 1 (by rfl) ⟨26456, by rfl⟩) R52913
theorem R68147 : Reach 68147 := rs (se 1 (by rfl) ⟨51110, by rfl⟩) R102221
theorem R35417 : Reach 35417 := rs (se 2 (by rfl) ⟨13281, by rfl⟩) R26563
theorem R35545 : Reach 35545 := rs (se 2 (by rfl) ⟨13329, by rfl⟩) R26659
theorem R68417 : Reach 68417 := rs (se 2 (by rfl) ⟨25656, by rfl⟩) R51313
theorem R68825 : Reach 68825 := rs (se 2 (by rfl) ⟨25809, by rfl⟩) R51619
theorem R36119 : Reach 36119 := rs (se 1 (by rfl) ⟨27089, by rfl⟩) R54179
theorem R265517 : Reach 265517 := rs (se 3 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R68957 : Reach 68957 := rs (se 3 (by rfl) ⟨12929, by rfl⟩) R25859
theorem R36247 : Reach 36247 := rs (se 1 (by rfl) ⟨27185, by rfl⟩) R54371
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R36659 : Reach 36659 := rs (se 1 (by rfl) ⟨27494, by rfl⟩) R54989
theorem R36787 : Reach 36787 := rs (se 1 (by rfl) ⟨27590, by rfl⟩) R55181
theorem R36875 : Reach 36875 := rs (se 1 (by rfl) ⟨27656, by rfl⟩) R55313
theorem R36929 : Reach 36929 := rs (se 2 (by rfl) ⟨13848, by rfl⟩) R27697
theorem R37003 : Reach 37003 := rs (se 1 (by rfl) ⟨27752, by rfl⟩) R55505
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R37057 : Reach 37057 := rs (se 2 (by rfl) ⟨13896, by rfl⟩) R27793
theorem R37145 : Reach 37145 := rs (se 2 (by rfl) ⟨13929, by rfl⟩) R27859
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R37273 : Reach 37273 := rs (se 2 (by rfl) ⟨13977, by rfl⟩) R27955
theorem R70091 : Reach 70091 := rs (se 1 (by rfl) ⟨52568, by rfl⟩) R105137
theorem R37441 : Reach 37441 := rs (se 2 (by rfl) ⟨14040, by rfl⟩) R28081
theorem R37579 : Reach 37579 := rs (se 1 (by rfl) ⟨28184, by rfl⟩) R56369
theorem R70361 : Reach 70361 := rs (se 2 (by rfl) ⟨26385, by rfl⟩) R52771
theorem R37847 : Reach 37847 := rs (se 1 (by rfl) ⟨28385, by rfl⟩) R56771
theorem R37975 : Reach 37975 := rs (se 1 (by rfl) ⟨28481, by rfl⟩) R56963
theorem R103517 : Reach 103517 := rs (se 3 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R71063 : Reach 71063 := rs (se 1 (by rfl) ⟨53297, by rfl⟩) R106595
theorem R38387 : Reach 38387 := rs (se 1 (by rfl) ⟨28790, by rfl⟩) R57581
theorem R71171 : Reach 71171 := rs (se 1 (by rfl) ⟨53378, by rfl⟩) R106757
theorem R38515 : Reach 38515 := rs (se 1 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R38603 : Reach 38603 := rs (se 1 (by rfl) ⟨28952, by rfl⟩) R57905
theorem R38657 : Reach 38657 := rs (se 2 (by rfl) ⟨14496, by rfl⟩) R28993
theorem R71441 : Reach 71441 := rs (se 2 (by rfl) ⟨26790, by rfl⟩) R53581
theorem R38731 : Reach 38731 := rs (se 1 (by rfl) ⟨29048, by rfl⟩) R58097
theorem R38785 : Reach 38785 := rs (se 2 (by rfl) ⟨14544, by rfl⟩) R29089
theorem R38809 : Reach 38809 := rs (se 2 (by rfl) ⟨14553, by rfl⟩) R29107
theorem R71603 : Reach 71603 := rs (se 1 (by rfl) ⟨53702, by rfl⟩) R107405
theorem R38873 : Reach 38873 := rs (se 2 (by rfl) ⟨14577, by rfl⟩) R29155
theorem R39001 : Reach 39001 := rs (se 2 (by rfl) ⟨14625, by rfl⟩) R29251
theorem R71873 : Reach 71873 := rs (se 2 (by rfl) ⟨26952, by rfl⟩) R53905
theorem R71981 : Reach 71981 := rs (se 3 (by rfl) ⟨13496, by rfl⟩) R26993
theorem R39575 : Reach 39575 := rs (se 1 (by rfl) ⟨29681, by rfl⟩) R59363
theorem R39617 : Reach 39617 := rs (se 2 (by rfl) ⟨14856, by rfl⟩) R29713
theorem R72413 : Reach 72413 := rs (se 3 (by rfl) ⟨13577, by rfl⟩) R27155
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R105623 : Reach 105623 := rs (se 1 (by rfl) ⟨79217, by rfl⟩) R158435
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R40331 : Reach 40331 := rs (se 1 (by rfl) ⟨30248, by rfl⟩) R60497
theorem R204211 : Reach 204211 := rs (se 1 (by rfl) ⟨153158, by rfl⟩) R306317
theorem R40513 : Reach 40513 := rs (se 2 (by rfl) ⟨15192, by rfl⟩) R30385
theorem R73547 : Reach 73547 := rs (se 1 (by rfl) ⟨55160, by rfl⟩) R110321
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R40961 : Reach 40961 := rs (se 2 (by rfl) ⟨15360, by rfl⟩) R30721
theorem R73817 : Reach 73817 := rs (se 2 (by rfl) ⟨27681, by rfl⟩) R55363
theorem R41303 : Reach 41303 := rs (se 1 (by rfl) ⟨30977, by rfl⟩) R61955
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R74519 : Reach 74519 := rs (se 1 (by rfl) ⟨55889, by rfl⟩) R111779
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) R20131
theorem R74627 : Reach 74627 := rs (se 1 (by rfl) ⟨55970, by rfl⟩) R111941
theorem R41971 : Reach 41971 := rs (se 1 (by rfl) ⟨31478, by rfl⟩) R62957
theorem R74897 : Reach 74897 := rs (se 2 (by rfl) ⟨28086, by rfl⟩) R56173
theorem R75059 : Reach 75059 := rs (se 1 (by rfl) ⟨56294, by rfl⟩) R112589
theorem R42419 : Reach 42419 := rs (se 1 (by rfl) ⟨31814, by rfl⟩) R63629
theorem R42457 : Reach 42457 := rs (se 2 (by rfl) ⟨15921, by rfl⟩) R31843
theorem R75329 : Reach 75329 := rs (se 2 (by rfl) ⟨28248, by rfl⟩) R56497
theorem R75437 : Reach 75437 := rs (se 3 (by rfl) ⟨14144, by rfl⟩) R28289
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R75485 : Reach 75485 := rs (se 3 (by rfl) ⟨14153, by rfl⟩) R28307
theorem R42817 : Reach 42817 := rs (se 2 (by rfl) ⟨16056, by rfl⟩) R32113
theorem R42905 : Reach 42905 := rs (se 2 (by rfl) ⟨16089, by rfl⟩) R32179
theorem R75869 : Reach 75869 := rs (se 3 (by rfl) ⟨14225, by rfl⟩) R28451
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R76211 : Reach 76211 := rs (se 1 (by rfl) ⟨57158, by rfl⟩) R114317
theorem R76291 : Reach 76291 := rs (se 1 (by rfl) ⟨57218, by rfl⟩) R114437
theorem R43649 : Reach 43649 := rs (se 2 (by rfl) ⟨16368, by rfl⟩) R32737
theorem R109187 : Reach 109187 := rs (se 1 (by rfl) ⟨81890, by rfl⟩) R163781
theorem R43915 : Reach 43915 := rs (se 1 (by rfl) ⟨32936, by rfl⟩) R65873
theorem R44185 : Reach 44185 := rs (se 2 (by rfl) ⟨16569, by rfl⟩) R33139
theorem R77003 : Reach 77003 := rs (se 1 (by rfl) ⟨57752, by rfl⟩) R115505
theorem R44363 : Reach 44363 := rs (se 1 (by rfl) ⟨33272, by rfl⟩) R66545
theorem R77273 : Reach 77273 := rs (se 2 (by rfl) ⟨28977, by rfl⟩) R57955
theorem R44545 : Reach 44545 := rs (se 2 (by rfl) ⟨16704, by rfl⟩) R33409
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R45017 : Reach 45017 := rs (se 2 (by rfl) ⟨16881, by rfl⟩) R33763
theorem R45107 : Reach 45107 := rs (se 1 (by rfl) ⟨33830, by rfl⟩) R67661
theorem R45143 : Reach 45143 := rs (se 1 (by rfl) ⟨33857, by rfl⟩) R67715
theorem R77975 : Reach 77975 := rs (se 1 (by rfl) ⟨58481, by rfl⟩) R116963
theorem R78083 : Reach 78083 := rs (se 1 (by rfl) ⟨58562, by rfl⟩) R117125
theorem R45323 : Reach 45323 := rs (se 1 (by rfl) ⟨33992, by rfl⟩) R67985
theorem R45377 : Reach 45377 := rs (se 2 (by rfl) ⟨17016, by rfl⟩) R34033
theorem R78155 : Reach 78155 := rs (se 1 (by rfl) ⟨58616, by rfl⟩) R117233
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R78353 : Reach 78353 := rs (se 2 (by rfl) ⟨29382, by rfl⟩) R58765
theorem R45593 : Reach 45593 := rs (se 2 (by rfl) ⟨17097, by rfl⟩) R34195
theorem R78401 : Reach 78401 := rs (se 2 (by rfl) ⟨29400, by rfl⟩) R58801
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R45683 : Reach 45683 := rs (se 1 (by rfl) ⟨34262, by rfl⟩) R68525
theorem R45719 : Reach 45719 := rs (se 1 (by rfl) ⟨34289, by rfl⟩) R68579
theorem R78515 : Reach 78515 := rs (se 1 (by rfl) ⟨58886, by rfl⟩) R117773
theorem R45899 : Reach 45899 := rs (se 1 (by rfl) ⟨34424, by rfl⟩) R68849
theorem R45953 : Reach 45953 := rs (se 2 (by rfl) ⟨17232, by rfl⟩) R34465
theorem R78785 : Reach 78785 := rs (se 2 (by rfl) ⟨29544, by rfl⟩) R59089
theorem R78893 : Reach 78893 := rs (se 3 (by rfl) ⟨14792, by rfl⟩) R29585
theorem R46169 : Reach 46169 := rs (se 2 (by rfl) ⟨17313, by rfl⟩) R34627
theorem R46259 : Reach 46259 := rs (se 1 (by rfl) ⟨34694, by rfl⟩) R69389
theorem R46295 : Reach 46295 := rs (se 1 (by rfl) ⟨34721, by rfl⟩) R69443
theorem R46337 : Reach 46337 := rs (se 2 (by rfl) ⟨17376, by rfl⟩) R34753
theorem R79127 : Reach 79127 := rs (se 1 (by rfl) ⟨59345, by rfl⟩) R118691
theorem R111947 : Reach 111947 := rs (se 1 (by rfl) ⟨83960, by rfl⟩) R167921
theorem R46423 : Reach 46423 := rs (se 1 (by rfl) ⟨34817, by rfl⟩) R69635
theorem R46475 : Reach 46475 := rs (se 1 (by rfl) ⟨34856, by rfl⟩) R69713
theorem R46529 : Reach 46529 := rs (se 2 (by rfl) ⟨17448, by rfl⟩) R34897
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) R29747
theorem R46745 : Reach 46745 := rs (se 2 (by rfl) ⟨17529, by rfl⟩) R35059
theorem R46835 : Reach 46835 := rs (se 1 (by rfl) ⟨35126, by rfl⟩) R70253
theorem R46871 : Reach 46871 := rs (se 1 (by rfl) ⟨35153, by rfl⟩) R70307
theorem R46937 : Reach 46937 := rs (se 2 (by rfl) ⟨17601, by rfl⟩) R35203
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) R66755
theorem R47027 : Reach 47027 := rs (se 1 (by rfl) ⟨35270, by rfl⟩) R70541
theorem R47051 : Reach 47051 := rs (se 1 (by rfl) ⟨35288, by rfl⟩) R70577
theorem R47105 : Reach 47105 := rs (se 2 (by rfl) ⟨17664, by rfl⟩) R35329
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R47321 : Reach 47321 := rs (se 2 (by rfl) ⟨17745, by rfl⟩) R35491
theorem R112913 : Reach 112913 := rs (se 2 (by rfl) ⟨42342, by rfl⟩) R84685
theorem R47411 : Reach 47411 := rs (se 1 (by rfl) ⟨35558, by rfl⟩) R71117
theorem R113075 : Reach 113075 := rs (se 1 (by rfl) ⟨84806, by rfl⟩) R169613
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R47681 : Reach 47681 := rs (se 2 (by rfl) ⟨17880, by rfl⟩) R35761
theorem R48023 : Reach 48023 := rs (se 1 (by rfl) ⟨36017, by rfl⟩) R72035
theorem R48089 : Reach 48089 := rs (se 2 (by rfl) ⟨18033, by rfl⟩) R36067
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R48203 : Reach 48203 := rs (se 1 (by rfl) ⟨36152, by rfl⟩) R72305
theorem R48217 : Reach 48217 := rs (se 2 (by rfl) ⟨18081, by rfl⟩) R36163
theorem R48473 : Reach 48473 := rs (se 2 (by rfl) ⟨18177, by rfl⟩) R36355
theorem R376163 : Reach 376163 := rs (se 1 (by rfl) ⟨282122, by rfl⟩) R564245
theorem R81283 : Reach 81283 := rs (se 1 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R48563 : Reach 48563 := rs (se 1 (by rfl) ⟨36422, by rfl⟩) R72845
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) R61069
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R48833 : Reach 48833 := rs (se 2 (by rfl) ⟨18312, by rfl⟩) R36625
theorem R114533 : Reach 114533 := rs (se 4 (by rfl) ⟨10737, by rfl⟩) R21475
theorem R49175 : Reach 49175 := rs (se 1 (by rfl) ⟨36881, by rfl⟩) R73763
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R49355 : Reach 49355 := rs (se 1 (by rfl) ⟨37016, by rfl⟩) R74033
theorem R82241 : Reach 82241 := rs (se 2 (by rfl) ⟨30840, by rfl⟩) R61681
theorem R115019 : Reach 115019 := rs (se 1 (by rfl) ⟨86264, by rfl⟩) R172529
theorem R49625 : Reach 49625 := rs (se 2 (by rfl) ⟨18609, by rfl⟩) R37219
theorem R49715 : Reach 49715 := rs (se 1 (by rfl) ⟨37286, by rfl⟩) R74573
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R49985 : Reach 49985 := rs (se 2 (by rfl) ⟨18744, by rfl⟩) R37489
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R82781 : Reach 82781 := rs (se 3 (by rfl) ⟨15521, by rfl⟩) R31043
theorem R50327 : Reach 50327 := rs (se 1 (by rfl) ⟨37745, by rfl⟩) R75491
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R50507 : Reach 50507 := rs (se 1 (by rfl) ⟨37880, by rfl⟩) R75761
theorem R148837 : Reach 148837 := rs (se 4 (by rfl) ⟨13953, by rfl⟩) R27907
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) R31313
theorem R83531 : Reach 83531 := rs (se 1 (by rfl) ⟨62648, by rfl⟩) R125297
theorem R50777 : Reach 50777 := rs (se 2 (by rfl) ⟨19041, by rfl⟩) R38083
theorem R50867 : Reach 50867 := rs (se 1 (by rfl) ⟨38150, by rfl⟩) R76301
theorem R51137 : Reach 51137 := rs (se 2 (by rfl) ⟨19176, by rfl⟩) R38353
theorem R116801 : Reach 116801 := rs (se 2 (by rfl) ⟨43800, by rfl⟩) R87601
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R84185 : Reach 84185 := rs (se 2 (by rfl) ⟨31569, by rfl⟩) R63139
theorem R51479 : Reach 51479 := rs (se 1 (by rfl) ⟨38609, by rfl⟩) R77219
theorem R51659 : Reach 51659 := rs (se 1 (by rfl) ⟨38744, by rfl⟩) R77489
theorem R84503 : Reach 84503 := rs (se 1 (by rfl) ⟨63377, by rfl⟩) R126755
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) R31745
theorem R51929 : Reach 51929 := rs (se 2 (by rfl) ⟨19473, by rfl⟩) R38947
theorem R52019 : Reach 52019 := rs (se 1 (by rfl) ⟨39014, by rfl⟩) R78029
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) R31811
theorem R52289 : Reach 52289 := rs (se 2 (by rfl) ⟨19608, by rfl⟩) R39217
theorem R85171 : Reach 85171 := rs (se 1 (by rfl) ⟨63878, by rfl⟩) R127757
theorem R52427 : Reach 52427 := rs (se 1 (by rfl) ⟨39320, by rfl⟩) R78641
theorem R52631 : Reach 52631 := rs (se 1 (by rfl) ⟨39473, by rfl⟩) R78947
theorem R20011 : Reach 20011 := rs (se 1 (by rfl) ⟨15008, by rfl⟩) R30017
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R20023 : Reach 20023 := rs (se 1 (by rfl) ⟨15017, by rfl⟩) R30035
theorem R20043 : Reach 20043 := rs (se 1 (by rfl) ⟨15032, by rfl⟩) R30065
theorem R347723 : Reach 347723 := rs (se 1 (by rfl) ⟨260792, by rfl⟩) R521585
theorem R52811 : Reach 52811 := rs (se 1 (by rfl) ⟨39608, by rfl⟩) R79217
theorem R20055 : Reach 20055 := rs (se 1 (by rfl) ⟨15041, by rfl⟩) R30083
theorem R20075 : Reach 20075 := rs (se 1 (by rfl) ⟨15056, by rfl⟩) R30113
theorem R20087 : Reach 20087 := rs (se 1 (by rfl) ⟨15065, by rfl⟩) R30131
theorem R20107 : Reach 20107 := rs (se 1 (by rfl) ⟨15080, by rfl⟩) R30161
theorem R20119 : Reach 20119 := rs (se 1 (by rfl) ⟨15089, by rfl⟩) R30179
theorem R20139 : Reach 20139 := rs (se 1 (by rfl) ⟨15104, by rfl⟩) R30209
theorem R20151 : Reach 20151 := rs (se 1 (by rfl) ⟨15113, by rfl⟩) R30227
theorem R20171 : Reach 20171 := rs (se 1 (by rfl) ⟨15128, by rfl⟩) R30257
theorem R20183 : Reach 20183 := rs (se 1 (by rfl) ⟨15137, by rfl⟩) R30275
theorem R20203 : Reach 20203 := rs (se 1 (by rfl) ⟨15152, by rfl⟩) R30305
theorem R20215 : Reach 20215 := rs (se 1 (by rfl) ⟨15161, by rfl⟩) R30323
theorem R20235 : Reach 20235 := rs (se 1 (by rfl) ⟨15176, by rfl⟩) R30353
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R20247 : Reach 20247 := rs (se 1 (by rfl) ⟨15185, by rfl⟩) R30371
theorem R20267 : Reach 20267 := rs (se 1 (by rfl) ⟨15200, by rfl⟩) R30401
theorem R20279 : Reach 20279 := rs (se 1 (by rfl) ⟨15209, by rfl⟩) R30419
theorem R20299 : Reach 20299 := rs (se 1 (by rfl) ⟨15224, by rfl⟩) R30449
theorem R20311 : Reach 20311 := rs (se 1 (by rfl) ⟨15233, by rfl⟩) R30467
theorem R20331 : Reach 20331 := rs (se 1 (by rfl) ⟨15248, by rfl⟩) R30497
theorem R20343 : Reach 20343 := rs (se 1 (by rfl) ⟨15257, by rfl⟩) R30515
theorem R20363 : Reach 20363 := rs (se 1 (by rfl) ⟨15272, by rfl⟩) R30545
theorem R20375 : Reach 20375 := rs (se 1 (by rfl) ⟨15281, by rfl⟩) R30563
theorem R20395 : Reach 20395 := rs (se 1 (by rfl) ⟨15296, by rfl⟩) R30593
theorem R20407 : Reach 20407 := rs (se 1 (by rfl) ⟨15305, by rfl⟩) R30611
theorem R20427 : Reach 20427 := rs (se 1 (by rfl) ⟨15320, by rfl⟩) R30641
theorem R20439 : Reach 20439 := rs (se 1 (by rfl) ⟨15329, by rfl⟩) R30659
theorem R118745 : Reach 118745 := rs (se 2 (by rfl) ⟨44529, by rfl⟩) R89059
theorem R20459 : Reach 20459 := rs (se 1 (by rfl) ⟨15344, by rfl⟩) R30689
theorem R20471 : Reach 20471 := rs (se 1 (by rfl) ⟨15353, by rfl⟩) R30707
theorem R20491 : Reach 20491 := rs (se 1 (by rfl) ⟨15368, by rfl⟩) R30737
theorem R20503 : Reach 20503 := rs (se 1 (by rfl) ⟨15377, by rfl⟩) R30755
theorem R20523 : Reach 20523 := rs (se 1 (by rfl) ⟨15392, by rfl⟩) R30785
theorem R20535 : Reach 20535 := rs (se 1 (by rfl) ⟨15401, by rfl⟩) R30803
theorem R20555 : Reach 20555 := rs (se 1 (by rfl) ⟨15416, by rfl⟩) R30833
theorem R20567 : Reach 20567 := rs (se 1 (by rfl) ⟨15425, by rfl⟩) R30851
theorem R217181 : Reach 217181 := rs (se 3 (by rfl) ⟨40721, by rfl⟩) R81443
theorem R20587 : Reach 20587 := rs (se 1 (by rfl) ⟨15440, by rfl⟩) R30881
theorem R20599 : Reach 20599 := rs (se 1 (by rfl) ⟨15449, by rfl⟩) R30899
theorem R20619 : Reach 20619 := rs (se 1 (by rfl) ⟨15464, by rfl⟩) R30929
theorem R20631 : Reach 20631 := rs (se 1 (by rfl) ⟨15473, by rfl⟩) R30947
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R20651 : Reach 20651 := rs (se 1 (by rfl) ⟨15488, by rfl⟩) R30977
theorem R20663 : Reach 20663 := rs (se 1 (by rfl) ⟨15497, by rfl⟩) R30995
theorem R20683 : Reach 20683 := rs (se 1 (by rfl) ⟨15512, by rfl⟩) R31025
theorem R20695 : Reach 20695 := rs (se 1 (by rfl) ⟨15521, by rfl⟩) R31043
theorem R20715 : Reach 20715 := rs (se 1 (by rfl) ⟨15536, by rfl⟩) R31073
theorem R20727 : Reach 20727 := rs (se 1 (by rfl) ⟨15545, by rfl⟩) R31091
theorem R20747 : Reach 20747 := rs (se 1 (by rfl) ⟨15560, by rfl⟩) R31121
theorem R20759 : Reach 20759 := rs (se 1 (by rfl) ⟨15569, by rfl⟩) R31139
theorem R20779 : Reach 20779 := rs (se 1 (by rfl) ⟨15584, by rfl⟩) R31169
theorem R20791 : Reach 20791 := rs (se 1 (by rfl) ⟨15593, by rfl⟩) R31187
theorem R20811 : Reach 20811 := rs (se 1 (by rfl) ⟨15608, by rfl⟩) R31217
theorem R20823 : Reach 20823 := rs (se 1 (by rfl) ⟨15617, by rfl⟩) R31235
theorem R20843 : Reach 20843 := rs (se 1 (by rfl) ⟨15632, by rfl⟩) R31265
theorem R20855 : Reach 20855 := rs (se 1 (by rfl) ⟨15641, by rfl⟩) R31283
theorem R20875 : Reach 20875 := rs (se 1 (by rfl) ⟨15656, by rfl⟩) R31313
theorem R86417 : Reach 86417 := rs (se 2 (by rfl) ⟨32406, by rfl⟩) R64813
theorem R20887 : Reach 20887 := rs (se 1 (by rfl) ⟨15665, by rfl⟩) R31331
theorem R119191 : Reach 119191 := rs (se 1 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R20907 : Reach 20907 := rs (se 1 (by rfl) ⟨15680, by rfl⟩) R31361
theorem R20919 : Reach 20919 := rs (se 1 (by rfl) ⟨15689, by rfl⟩) R31379
theorem R20939 : Reach 20939 := rs (se 1 (by rfl) ⟨15704, by rfl⟩) R31409
theorem R20951 : Reach 20951 := rs (se 1 (by rfl) ⟨15713, by rfl⟩) R31427
theorem R20971 : Reach 20971 := rs (se 1 (by rfl) ⟨15728, by rfl⟩) R31457
theorem R20983 : Reach 20983 := rs (se 1 (by rfl) ⟨15737, by rfl⟩) R31475
theorem R21003 : Reach 21003 := rs (se 1 (by rfl) ⟨15752, by rfl⟩) R31505
theorem R21015 : Reach 21015 := rs (se 1 (by rfl) ⟨15761, by rfl⟩) R31523
theorem R21035 : Reach 21035 := rs (se 1 (by rfl) ⟨15776, by rfl⟩) R31553
theorem R21047 : Reach 21047 := rs (se 1 (by rfl) ⟨15785, by rfl⟩) R31571
theorem R21067 : Reach 21067 := rs (se 1 (by rfl) ⟨15800, by rfl⟩) R31601
theorem R21079 : Reach 21079 := rs (se 1 (by rfl) ⟨15809, by rfl⟩) R31619
theorem R21099 : Reach 21099 := rs (se 1 (by rfl) ⟨15824, by rfl⟩) R31649
theorem R21111 : Reach 21111 := rs (se 1 (by rfl) ⟨15833, by rfl⟩) R31667
theorem R21131 : Reach 21131 := rs (se 1 (by rfl) ⟨15848, by rfl⟩) R31697
theorem R21143 : Reach 21143 := rs (se 1 (by rfl) ⟨15857, by rfl⟩) R31715
theorem R21163 : Reach 21163 := rs (se 1 (by rfl) ⟨15872, by rfl⟩) R31745
theorem R21175 : Reach 21175 := rs (se 1 (by rfl) ⟨15881, by rfl⟩) R31763
theorem R21195 : Reach 21195 := rs (se 1 (by rfl) ⟨15896, by rfl⟩) R31793
theorem R21207 : Reach 21207 := rs (se 1 (by rfl) ⟨15905, by rfl⟩) R31811
theorem R21227 : Reach 21227 := rs (se 1 (by rfl) ⟨15920, by rfl⟩) R31841
theorem R21239 : Reach 21239 := rs (se 1 (by rfl) ⟨15929, by rfl⟩) R31859
theorem R21259 : Reach 21259 := rs (se 1 (by rfl) ⟨15944, by rfl⟩) R31889
theorem R21271 : Reach 21271 := rs (se 1 (by rfl) ⟨15953, by rfl⟩) R31907
theorem R21291 : Reach 21291 := rs (se 1 (by rfl) ⟨15968, by rfl⟩) R31937
theorem R54067 : Reach 54067 := rs (se 1 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R21303 : Reach 21303 := rs (se 1 (by rfl) ⟨15977, by rfl⟩) R31955
theorem R21323 : Reach 21323 := rs (se 1 (by rfl) ⟨15992, by rfl⟩) R31985
theorem R21335 : Reach 21335 := rs (se 1 (by rfl) ⟨16001, by rfl⟩) R32003
theorem R21355 : Reach 21355 := rs (se 1 (by rfl) ⟨16016, by rfl⟩) R32033
theorem R21367 : Reach 21367 := rs (se 1 (by rfl) ⟨16025, by rfl⟩) R32051
theorem R21387 : Reach 21387 := rs (se 1 (by rfl) ⟨16040, by rfl⟩) R32081
theorem R21399 : Reach 21399 := rs (se 1 (by rfl) ⟨16049, by rfl⟩) R32099
theorem R21419 : Reach 21419 := rs (se 1 (by rfl) ⟨16064, by rfl⟩) R32129
theorem R21431 : Reach 21431 := rs (se 1 (by rfl) ⟨16073, by rfl⟩) R32147
theorem R54209 : Reach 54209 := rs (se 2 (by rfl) ⟨20328, by rfl⟩) R40657
theorem R21451 : Reach 21451 := rs (se 1 (by rfl) ⟨16088, by rfl⟩) R32177
theorem R21463 : Reach 21463 := rs (se 1 (by rfl) ⟨16097, by rfl⟩) R32195
theorem R21483 : Reach 21483 := rs (se 1 (by rfl) ⟨16112, by rfl⟩) R32225
theorem R21495 : Reach 21495 := rs (se 1 (by rfl) ⟨16121, by rfl⟩) R32243
theorem R21515 : Reach 21515 := rs (se 1 (by rfl) ⟨16136, by rfl⟩) R32273
theorem R21527 : Reach 21527 := rs (se 1 (by rfl) ⟨16145, by rfl⟩) R32291
theorem R21547 : Reach 21547 := rs (se 1 (by rfl) ⟨16160, by rfl⟩) R32321
theorem R21559 : Reach 21559 := rs (se 1 (by rfl) ⟨16169, by rfl⟩) R32339
theorem R21579 : Reach 21579 := rs (se 1 (by rfl) ⟨16184, by rfl⟩) R32369
theorem R87115 : Reach 87115 := rs (se 1 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R21591 : Reach 21591 := rs (se 1 (by rfl) ⟨16193, by rfl⟩) R32387
theorem R21611 : Reach 21611 := rs (se 1 (by rfl) ⟨16208, by rfl⟩) R32417
theorem R21623 : Reach 21623 := rs (se 1 (by rfl) ⟨16217, by rfl⟩) R32435
theorem R21643 : Reach 21643 := rs (se 1 (by rfl) ⟨16232, by rfl⟩) R32465
theorem R21655 : Reach 21655 := rs (se 1 (by rfl) ⟨16241, by rfl⟩) R32483
theorem R21675 : Reach 21675 := rs (se 1 (by rfl) ⟨16256, by rfl⟩) R32513
theorem R21687 : Reach 21687 := rs (se 1 (by rfl) ⟨16265, by rfl⟩) R32531
theorem R21707 : Reach 21707 := rs (se 1 (by rfl) ⟨16280, by rfl⟩) R32561
theorem R21719 : Reach 21719 := rs (se 1 (by rfl) ⟨16289, by rfl⟩) R32579
theorem R21739 : Reach 21739 := rs (se 1 (by rfl) ⟨16304, by rfl⟩) R32609
theorem R21751 : Reach 21751 := rs (se 1 (by rfl) ⟨16313, by rfl⟩) R32627
theorem R21771 : Reach 21771 := rs (se 1 (by rfl) ⟨16328, by rfl⟩) R32657
theorem R21783 : Reach 21783 := rs (se 1 (by rfl) ⟨16337, by rfl⟩) R32675
theorem R21803 : Reach 21803 := rs (se 1 (by rfl) ⟨16352, by rfl⟩) R32705
theorem R21815 : Reach 21815 := rs (se 1 (by rfl) ⟨16361, by rfl⟩) R32723
theorem R21835 : Reach 21835 := rs (se 1 (by rfl) ⟨16376, by rfl⟩) R32753
theorem R21847 : Reach 21847 := rs (se 1 (by rfl) ⟨16385, by rfl⟩) R32771
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) R32771
theorem R21867 : Reach 21867 := rs (se 1 (by rfl) ⟨16400, by rfl⟩) R32801
theorem R21879 : Reach 21879 := rs (se 1 (by rfl) ⟨16409, by rfl⟩) R32819
theorem R21899 : Reach 21899 := rs (se 1 (by rfl) ⟨16424, by rfl⟩) R32849
theorem R21911 : Reach 21911 := rs (se 1 (by rfl) ⟨16433, by rfl⟩) R32867
theorem R21931 : Reach 21931 := rs (se 1 (by rfl) ⟨16448, by rfl⟩) R32897
theorem R21943 : Reach 21943 := rs (se 1 (by rfl) ⟨16457, by rfl⟩) R32915
theorem R21963 : Reach 21963 := rs (se 1 (by rfl) ⟨16472, by rfl⟩) R32945
theorem R21975 : Reach 21975 := rs (se 1 (by rfl) ⟨16481, by rfl⟩) R32963
theorem R21995 : Reach 21995 := rs (se 1 (by rfl) ⟨16496, by rfl⟩) R32993
theorem R22007 : Reach 22007 := rs (se 1 (by rfl) ⟨16505, by rfl⟩) R33011
theorem R22027 : Reach 22027 := rs (se 1 (by rfl) ⟨16520, by rfl⟩) R33041
theorem R22039 : Reach 22039 := rs (se 1 (by rfl) ⟨16529, by rfl⟩) R33059
theorem R22059 : Reach 22059 := rs (se 1 (by rfl) ⟨16544, by rfl⟩) R33089
theorem R22071 : Reach 22071 := rs (se 1 (by rfl) ⟨16553, by rfl⟩) R33107
theorem R87617 : Reach 87617 := rs (se 2 (by rfl) ⟨32856, by rfl⟩) R65713
theorem R22091 : Reach 22091 := rs (se 1 (by rfl) ⟨16568, by rfl⟩) R33137
theorem R22103 : Reach 22103 := rs (se 1 (by rfl) ⟨16577, by rfl⟩) R33155
theorem R54877 : Reach 54877 := rs (se 3 (by rfl) ⟨10289, by rfl⟩) R20579
theorem R22123 : Reach 22123 := rs (se 1 (by rfl) ⟨16592, by rfl⟩) R33185
theorem R22135 : Reach 22135 := rs (se 1 (by rfl) ⟨16601, by rfl⟩) R33203
theorem R22155 : Reach 22155 := rs (se 1 (by rfl) ⟨16616, by rfl⟩) R33233
theorem R22167 : Reach 22167 := rs (se 1 (by rfl) ⟨16625, by rfl⟩) R33251
theorem R22187 : Reach 22187 := rs (se 1 (by rfl) ⟨16640, by rfl⟩) R33281
theorem R22199 : Reach 22199 := rs (se 1 (by rfl) ⟨16649, by rfl⟩) R33299
theorem R22219 : Reach 22219 := rs (se 1 (by rfl) ⟨16664, by rfl⟩) R33329
theorem R22231 : Reach 22231 := rs (se 1 (by rfl) ⟨16673, by rfl⟩) R33347
theorem R22251 : Reach 22251 := rs (se 1 (by rfl) ⟨16688, by rfl⟩) R33377
theorem R22263 : Reach 22263 := rs (se 1 (by rfl) ⟨16697, by rfl⟩) R33395
theorem R22283 : Reach 22283 := rs (se 1 (by rfl) ⟨16712, by rfl⟩) R33425
theorem R22295 : Reach 22295 := rs (se 1 (by rfl) ⟨16721, by rfl⟩) R33443
theorem R22315 : Reach 22315 := rs (se 1 (by rfl) ⟨16736, by rfl⟩) R33473
theorem R22327 : Reach 22327 := rs (se 1 (by rfl) ⟨16745, by rfl⟩) R33491
theorem R22347 : Reach 22347 := rs (se 1 (by rfl) ⟨16760, by rfl⟩) R33521
theorem R22359 : Reach 22359 := rs (se 1 (by rfl) ⟨16769, by rfl⟩) R33539
theorem R22379 : Reach 22379 := rs (se 1 (by rfl) ⟨16784, by rfl⟩) R33569
theorem R22391 : Reach 22391 := rs (se 1 (by rfl) ⟨16793, by rfl⟩) R33587
theorem R22411 : Reach 22411 := rs (se 1 (by rfl) ⟨16808, by rfl⟩) R33617
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R22423 : Reach 22423 := rs (se 1 (by rfl) ⟨16817, by rfl⟩) R33635
theorem R22443 : Reach 22443 := rs (se 1 (by rfl) ⟨16832, by rfl⟩) R33665
theorem R22455 : Reach 22455 := rs (se 1 (by rfl) ⟨16841, by rfl⟩) R33683
theorem R22475 : Reach 22475 := rs (se 1 (by rfl) ⟨16856, by rfl⟩) R33713
theorem R186317 : Reach 186317 := rs (se 3 (by rfl) ⟨34934, by rfl⟩) R69869
theorem R22487 : Reach 22487 := rs (se 1 (by rfl) ⟨16865, by rfl⟩) R33731
theorem R22507 : Reach 22507 := rs (se 1 (by rfl) ⟨16880, by rfl⟩) R33761
theorem R22519 : Reach 22519 := rs (se 1 (by rfl) ⟨16889, by rfl⟩) R33779
theorem R22539 : Reach 22539 := rs (se 1 (by rfl) ⟨16904, by rfl⟩) R33809
theorem R22551 : Reach 22551 := rs (se 1 (by rfl) ⟨16913, by rfl⟩) R33827
theorem R88087 : Reach 88087 := rs (se 1 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R22571 : Reach 22571 := rs (se 1 (by rfl) ⟨16928, by rfl⟩) R33857
theorem R22583 : Reach 22583 := rs (se 1 (by rfl) ⟨16937, by rfl⟩) R33875
theorem R22603 : Reach 22603 := rs (se 1 (by rfl) ⟨16952, by rfl⟩) R33905
theorem R22615 : Reach 22615 := rs (se 1 (by rfl) ⟨16961, by rfl⟩) R33923
theorem R22635 : Reach 22635 := rs (se 1 (by rfl) ⟨16976, by rfl⟩) R33953
theorem R22647 : Reach 22647 := rs (se 1 (by rfl) ⟨16985, by rfl⟩) R33971
theorem R22667 : Reach 22667 := rs (se 1 (by rfl) ⟨17000, by rfl⟩) R34001
theorem R22679 : Reach 22679 := rs (se 1 (by rfl) ⟨17009, by rfl⟩) R34019
theorem R22699 : Reach 22699 := rs (se 1 (by rfl) ⟨17024, by rfl⟩) R34049
theorem R55475 : Reach 55475 := rs (se 1 (by rfl) ⟨41606, by rfl⟩) R83213
theorem R22711 : Reach 22711 := rs (se 1 (by rfl) ⟨17033, by rfl⟩) R34067
theorem R22731 : Reach 22731 := rs (se 1 (by rfl) ⟨17048, by rfl⟩) R34097
theorem R22743 : Reach 22743 := rs (se 1 (by rfl) ⟨17057, by rfl⟩) R34115
theorem R22763 : Reach 22763 := rs (se 1 (by rfl) ⟨17072, by rfl⟩) R34145
theorem R22775 : Reach 22775 := rs (se 1 (by rfl) ⟨17081, by rfl⟩) R34163
theorem R22795 : Reach 22795 := rs (se 1 (by rfl) ⟨17096, by rfl⟩) R34193
theorem R22807 : Reach 22807 := rs (se 1 (by rfl) ⟨17105, by rfl⟩) R34211
theorem R22827 : Reach 22827 := rs (se 1 (by rfl) ⟨17120, by rfl⟩) R34241
theorem R22839 : Reach 22839 := rs (se 1 (by rfl) ⟨17129, by rfl⟩) R34259
theorem R22859 : Reach 22859 := rs (se 1 (by rfl) ⟨17144, by rfl⟩) R34289
theorem R22871 : Reach 22871 := rs (se 1 (by rfl) ⟨17153, by rfl⟩) R34307
theorem R22891 : Reach 22891 := rs (se 1 (by rfl) ⟨17168, by rfl⟩) R34337
theorem R22903 : Reach 22903 := rs (se 1 (by rfl) ⟨17177, by rfl⟩) R34355
theorem R22923 : Reach 22923 := rs (se 1 (by rfl) ⟨17192, by rfl⟩) R34385
theorem R22935 : Reach 22935 := rs (se 1 (by rfl) ⟨17201, by rfl⟩) R34403
theorem R22955 : Reach 22955 := rs (se 1 (by rfl) ⟨17216, by rfl⟩) R34433
theorem R22967 : Reach 22967 := rs (se 1 (by rfl) ⟨17225, by rfl⟩) R34451
theorem R88523 : Reach 88523 := rs (se 1 (by rfl) ⟨66392, by rfl⟩) R132785
theorem R22987 : Reach 22987 := rs (se 1 (by rfl) ⟨17240, by rfl⟩) R34481
theorem R154061 : Reach 154061 := rs (se 3 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R22999 : Reach 22999 := rs (se 1 (by rfl) ⟨17249, by rfl⟩) R34499
theorem R23019 : Reach 23019 := rs (se 1 (by rfl) ⟨17264, by rfl⟩) R34529
theorem R23031 : Reach 23031 := rs (se 1 (by rfl) ⟨17273, by rfl⟩) R34547
theorem R23051 : Reach 23051 := rs (se 1 (by rfl) ⟨17288, by rfl⟩) R34577
theorem R23063 : Reach 23063 := rs (se 1 (by rfl) ⟨17297, by rfl⟩) R34595
theorem R23083 : Reach 23083 := rs (se 1 (by rfl) ⟨17312, by rfl⟩) R34625
theorem R23095 : Reach 23095 := rs (se 1 (by rfl) ⟨17321, by rfl⟩) R34643
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R23115 : Reach 23115 := rs (se 1 (by rfl) ⟨17336, by rfl⟩) R34673
theorem R23127 : Reach 23127 := rs (se 1 (by rfl) ⟨17345, by rfl⟩) R34691
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) R22771
theorem R23147 : Reach 23147 := rs (se 1 (by rfl) ⟨17360, by rfl⟩) R34721
theorem R23159 : Reach 23159 := rs (se 1 (by rfl) ⟨17369, by rfl⟩) R34739
theorem R23179 : Reach 23179 := rs (se 1 (by rfl) ⟨17384, by rfl⟩) R34769
theorem R23191 : Reach 23191 := rs (se 1 (by rfl) ⟨17393, by rfl⟩) R34787
theorem R23211 : Reach 23211 := rs (se 1 (by rfl) ⟨17408, by rfl⟩) R34817
theorem R23223 : Reach 23223 := rs (se 1 (by rfl) ⟨17417, by rfl⟩) R34835
theorem R56011 : Reach 56011 := rs (se 1 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R23243 : Reach 23243 := rs (se 1 (by rfl) ⟨17432, by rfl⟩) R34865
theorem R23255 : Reach 23255 := rs (se 1 (by rfl) ⟨17441, by rfl⟩) R34883
theorem R23275 : Reach 23275 := rs (se 1 (by rfl) ⟨17456, by rfl⟩) R34913
theorem R23287 : Reach 23287 := rs (se 1 (by rfl) ⟨17465, by rfl⟩) R34931
theorem R23307 : Reach 23307 := rs (se 1 (by rfl) ⟨17480, by rfl⟩) R34961
theorem R23319 : Reach 23319 := rs (se 1 (by rfl) ⟨17489, by rfl⟩) R34979
theorem R23339 : Reach 23339 := rs (se 1 (by rfl) ⟨17504, by rfl⟩) R35009
theorem R88877 : Reach 88877 := rs (se 3 (by rfl) ⟨16664, by rfl⟩) R33329
theorem R88883 : Reach 88883 := rs (se 1 (by rfl) ⟨66662, by rfl⟩) R133325
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R23351 : Reach 23351 := rs (se 1 (by rfl) ⟨17513, by rfl⟩) R35027
theorem R23371 : Reach 23371 := rs (se 1 (by rfl) ⟨17528, by rfl⟩) R35057
theorem R23383 : Reach 23383 := rs (se 1 (by rfl) ⟨17537, by rfl⟩) R35075
theorem R56153 : Reach 56153 := rs (se 2 (by rfl) ⟨21057, by rfl⟩) R42115
theorem R23403 : Reach 23403 := rs (se 1 (by rfl) ⟨17552, by rfl⟩) R35105
theorem R23415 : Reach 23415 := rs (se 1 (by rfl) ⟨17561, by rfl⟩) R35123
theorem R23435 : Reach 23435 := rs (se 1 (by rfl) ⟨17576, by rfl⟩) R35153
theorem R23447 : Reach 23447 := rs (se 1 (by rfl) ⟨17585, by rfl⟩) R35171
theorem R23467 : Reach 23467 := rs (se 1 (by rfl) ⟨17600, by rfl⟩) R35201
theorem R154547 : Reach 154547 := rs (se 1 (by rfl) ⟨115910, by rfl⟩) R231821
theorem R23479 : Reach 23479 := rs (se 1 (by rfl) ⟨17609, by rfl⟩) R35219
theorem R23499 : Reach 23499 := rs (se 1 (by rfl) ⟨17624, by rfl⟩) R35249
theorem R56285 : Reach 56285 := rs (se 3 (by rfl) ⟨10553, by rfl⟩) R21107
theorem R23575 : Reach 23575 := rs (se 1 (by rfl) ⟨17681, by rfl⟩) R35363
theorem R23755 : Reach 23755 := rs (se 1 (by rfl) ⟨17816, by rfl⟩) R35633
theorem R24023 : Reach 24023 := rs (se 1 (by rfl) ⟨18017, by rfl⟩) R36035
theorem R24151 : Reach 24151 := rs (se 1 (by rfl) ⟨18113, by rfl⟩) R36227
theorem R56983 : Reach 56983 := rs (se 1 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R24331 : Reach 24331 := rs (se 1 (by rfl) ⟨18248, by rfl⟩) R36497
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) R67405
theorem R57181 : Reach 57181 := rs (se 3 (by rfl) ⟨10721, by rfl⟩) R21443
theorem R57419 : Reach 57419 := rs (se 1 (by rfl) ⟨43064, by rfl⟩) R86129
theorem R24715 : Reach 24715 := rs (se 1 (by rfl) ⟨18536, by rfl⟩) R37073
theorem R24727 : Reach 24727 := rs (se 1 (by rfl) ⟨18545, by rfl⟩) R37091
theorem R57523 : Reach 57523 := rs (se 1 (by rfl) ⟨43142, by rfl⟩) R86285
theorem R24907 : Reach 24907 := rs (se 1 (by rfl) ⟨18680, by rfl⟩) R37361
theorem R156005 : Reach 156005 := rs (se 4 (by rfl) ⟨14625, by rfl⟩) R29251
theorem R57793 : Reach 57793 := rs (se 2 (by rfl) ⟨21672, by rfl⟩) R43345
theorem R25303 : Reach 25303 := rs (se 1 (by rfl) ⟨18977, by rfl⟩) R37955
theorem R156491 : Reach 156491 := rs (se 1 (by rfl) ⟨117368, by rfl⟩) R234737
theorem R25483 : Reach 25483 := rs (se 1 (by rfl) ⟨19112, by rfl⟩) R38225
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R58391 : Reach 58391 := rs (se 1 (by rfl) ⟨43793, by rfl⟩) R87587
theorem R25687 : Reach 25687 := rs (se 1 (by rfl) ⟨19265, by rfl⟩) R38531
theorem R58457 : Reach 58457 := rs (se 2 (by rfl) ⟨21921, by rfl⟩) R43843
theorem R25879 : Reach 25879 := rs (se 1 (by rfl) ⟨19409, by rfl⟩) R38819
theorem R26059 : Reach 26059 := rs (se 1 (by rfl) ⟨19544, by rfl⟩) R39089
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R59201 : Reach 59201 := rs (se 2 (by rfl) ⟨22200, by rfl⟩) R44401
theorem R26507 : Reach 26507 := rs (se 1 (by rfl) ⟨19880, by rfl⟩) R39761
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) R69187
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) R34625
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) R22451
theorem R27211 : Reach 27211 := rs (se 1 (by rfl) ⟨20408, by rfl⟩) R40817
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) R34787
theorem R60097 : Reach 60097 := rs (se 2 (by rfl) ⟨22536, by rfl⟩) R45073
theorem R27479 : Reach 27479 := rs (se 1 (by rfl) ⟨20609, by rfl⟩) R41219
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R60439 : Reach 60439 := rs (se 1 (by rfl) ⟨45329, by rfl⟩) R90659
theorem R126481 : Reach 126481 := rs (se 2 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R28183 : Reach 28183 := rs (se 1 (by rfl) ⟨21137, by rfl⟩) R42275
theorem R388739 : Reach 388739 := rs (se 1 (by rfl) ⟨291554, by rfl⟩) R583109
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) R45859
theorem R28441 : Reach 28441 := rs (se 2 (by rfl) ⟨10665, by rfl⟩) R21331
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) R42211
theorem R28631 : Reach 28631 := rs (se 1 (by rfl) ⟨21473, by rfl⟩) R42947
theorem R258065 : Reach 258065 := rs (se 2 (by rfl) ⟨96774, by rfl⟩) R193549
theorem R62155 : Reach 62155 := rs (se 1 (by rfl) ⟨46616, by rfl⟩) R93233
theorem R29593 : Reach 29593 := rs (se 2 (by rfl) ⟨11097, by rfl⟩) R22195
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R62785 : Reach 62785 := rs (se 2 (by rfl) ⟨23544, by rfl⟩) R47089
theorem R30041 : Reach 30041 := rs (se 2 (by rfl) ⟨11265, by rfl⟩) R22531
theorem R30155 : Reach 30155 := rs (se 1 (by rfl) ⟨22616, by rfl⟩) R45233
theorem R30167 : Reach 30167 := rs (se 1 (by rfl) ⟨22625, by rfl⟩) R45251
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R30233 : Reach 30233 := rs (se 2 (by rfl) ⟨11337, by rfl⟩) R22675
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) R21091
theorem R30347 : Reach 30347 := rs (se 1 (by rfl) ⟨22760, by rfl⟩) R45521
theorem R30359 : Reach 30359 := rs (se 1 (by rfl) ⟨22769, by rfl⟩) R45539
theorem R30425 : Reach 30425 := rs (se 2 (by rfl) ⟨11409, by rfl⟩) R22819
theorem R30539 : Reach 30539 := rs (se 1 (by rfl) ⟨22904, by rfl⟩) R45809
theorem R30551 : Reach 30551 := rs (se 1 (by rfl) ⟨22913, by rfl⟩) R45827
theorem R30617 : Reach 30617 := rs (se 2 (by rfl) ⟨11481, by rfl⟩) R22963
theorem R30731 : Reach 30731 := rs (se 1 (by rfl) ⟨23048, by rfl⟩) R46097
theorem R30743 : Reach 30743 := rs (se 1 (by rfl) ⟨23057, by rfl⟩) R46115
theorem R161837 : Reach 161837 := rs (se 3 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R30809 : Reach 30809 := rs (se 2 (by rfl) ⟨11553, by rfl⟩) R23107
theorem R96349 : Reach 96349 := rs (se 3 (by rfl) ⟨18065, by rfl⟩) R36131
theorem R30923 : Reach 30923 := rs (se 1 (by rfl) ⟨23192, by rfl⟩) R46385
theorem R30935 : Reach 30935 := rs (se 1 (by rfl) ⟨23201, by rfl⟩) R46403
theorem R30937 : Reach 30937 := rs (se 2 (by rfl) ⟨11601, by rfl⟩) R23203
theorem R31001 : Reach 31001 := rs (se 2 (by rfl) ⟨11625, by rfl⟩) R23251
theorem R31051 : Reach 31051 := rs (se 1 (by rfl) ⟨23288, by rfl⟩) R46577
theorem R31115 : Reach 31115 := rs (se 1 (by rfl) ⟨23336, by rfl⟩) R46673
theorem R31127 : Reach 31127 := rs (se 1 (by rfl) ⟨23345, by rfl⟩) R46691
theorem R31193 : Reach 31193 := rs (se 2 (by rfl) ⟨11697, by rfl⟩) R23395
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R31307 : Reach 31307 := rs (se 1 (by rfl) ⟨23480, by rfl⟩) R46961
theorem R31319 : Reach 31319 := rs (se 1 (by rfl) ⟨23489, by rfl⟩) R46979
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R31385 : Reach 31385 := rs (se 2 (by rfl) ⟨11769, by rfl⟩) R23539
theorem R96947 : Reach 96947 := rs (se 1 (by rfl) ⟨72710, by rfl⟩) R145421
theorem R31499 : Reach 31499 := rs (se 1 (by rfl) ⟨23624, by rfl⟩) R47249
theorem R31511 : Reach 31511 := rs (se 1 (by rfl) ⟨23633, by rfl⟩) R47267
theorem R31577 : Reach 31577 := rs (se 2 (by rfl) ⟨11841, by rfl⟩) R23683
theorem R260981 : Reach 260981 := rs (se 5 (by rfl) ⟨12233, by rfl⟩) R24467
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R31691 : Reach 31691 := rs (se 1 (by rfl) ⟨23768, by rfl⟩) R47537
theorem R31703 : Reach 31703 := rs (se 1 (by rfl) ⟨23777, by rfl⟩) R47555
theorem R31769 : Reach 31769 := rs (se 2 (by rfl) ⟨11913, by rfl⟩) R23827
theorem R31883 : Reach 31883 := rs (se 1 (by rfl) ⟨23912, by rfl⟩) R47825
theorem R31895 : Reach 31895 := rs (se 1 (by rfl) ⟨23921, by rfl⟩) R47843
theorem R31961 : Reach 31961 := rs (se 2 (by rfl) ⟨11985, by rfl⟩) R23971
theorem R32075 : Reach 32075 := rs (se 1 (by rfl) ⟨24056, by rfl⟩) R48113
theorem R32087 : Reach 32087 := rs (se 1 (by rfl) ⟨24065, by rfl⟩) R48131
theorem R32153 : Reach 32153 := rs (se 2 (by rfl) ⟨12057, by rfl⟩) R24115
theorem R32267 : Reach 32267 := rs (se 1 (by rfl) ⟨24200, by rfl⟩) R48401
theorem R32279 : Reach 32279 := rs (se 1 (by rfl) ⟨24209, by rfl⟩) R48419
theorem R32345 : Reach 32345 := rs (se 2 (by rfl) ⟨12129, by rfl⟩) R24259
theorem R32395 : Reach 32395 := rs (se 1 (by rfl) ⟨24296, by rfl⟩) R48593
theorem R32459 : Reach 32459 := rs (se 1 (by rfl) ⟨24344, by rfl⟩) R48689
theorem R32471 : Reach 32471 := rs (se 1 (by rfl) ⟨24353, by rfl⟩) R48707
theorem R65303 : Reach 65303 := rs (se 1 (by rfl) ⟨48977, by rfl⟩) R97955
theorem R32537 : Reach 32537 := rs (se 2 (by rfl) ⟨12201, by rfl⟩) R24403
theorem R32651 : Reach 32651 := rs (se 1 (by rfl) ⟨24488, by rfl⟩) R48977
theorem R32663 : Reach 32663 := rs (se 1 (by rfl) ⟨24497, by rfl⟩) R48995
theorem R32665 : Reach 32665 := rs (se 2 (by rfl) ⟨12249, by rfl⟩) R24499
theorem R294835 : Reach 294835 := rs (se 1 (by rfl) ⟨221126, by rfl⟩) R442253
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R32729 : Reach 32729 := rs (se 2 (by rfl) ⟨12273, by rfl⟩) R24547
theorem R32783 : Reach 32783 := rs (se 1 (by rfl) ⟨24587, by rfl⟩) R49175
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R32903 : Reach 32903 := rs (se 1 (by rfl) ⟨24677, by rfl⟩) R49355
theorem R32969 : Reach 32969 := rs (se 2 (by rfl) ⟨12363, by rfl⟩) R24727
theorem R33083 : Reach 33083 := rs (se 1 (by rfl) ⟨24812, by rfl⟩) R49625
theorem R33143 : Reach 33143 := rs (se 1 (by rfl) ⟨24857, by rfl⟩) R49715
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R33209 : Reach 33209 := rs (se 2 (by rfl) ⟨12453, by rfl⟩) R24907
theorem R33323 : Reach 33323 := rs (se 1 (by rfl) ⟨24992, by rfl⟩) R49985
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) R24715
theorem R33551 : Reach 33551 := rs (se 1 (by rfl) ⟨25163, by rfl⟩) R50327
theorem R33671 : Reach 33671 := rs (se 1 (by rfl) ⟨25253, by rfl⟩) R50507
theorem R33737 : Reach 33737 := rs (se 2 (by rfl) ⟨12651, by rfl⟩) R25303
theorem R33851 : Reach 33851 := rs (se 1 (by rfl) ⟨25388, by rfl⟩) R50777
theorem R33911 : Reach 33911 := rs (se 1 (by rfl) ⟨25433, by rfl⟩) R50867
theorem R33977 : Reach 33977 := rs (se 2 (by rfl) ⟨12741, by rfl⟩) R25483
theorem R34091 : Reach 34091 := rs (se 1 (by rfl) ⟨25568, by rfl⟩) R51137
theorem R34249 : Reach 34249 := rs (se 2 (by rfl) ⟨12843, by rfl⟩) R25687
theorem R34319 : Reach 34319 := rs (se 1 (by rfl) ⟨25739, by rfl⟩) R51479
theorem R34439 : Reach 34439 := rs (se 1 (by rfl) ⟨25829, by rfl⟩) R51659
theorem R34505 : Reach 34505 := rs (se 2 (by rfl) ⟨12939, by rfl⟩) R25879
theorem R198449 : Reach 198449 := rs (se 2 (by rfl) ⟨74418, by rfl⟩) R148837
theorem R34619 : Reach 34619 := rs (se 1 (by rfl) ⟨25964, by rfl⟩) R51929
theorem R34679 : Reach 34679 := rs (se 1 (by rfl) ⟨26009, by rfl⟩) R52019
theorem R34745 : Reach 34745 := rs (se 2 (by rfl) ⟨13029, by rfl⟩) R26059
theorem R34859 : Reach 34859 := rs (se 1 (by rfl) ⟨26144, by rfl⟩) R52289
theorem R34951 : Reach 34951 := rs (se 1 (by rfl) ⟨26213, by rfl⟩) R52427
theorem R35087 : Reach 35087 := rs (se 1 (by rfl) ⟨26315, by rfl⟩) R52631
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R231815 : Reach 231815 := rs (se 1 (by rfl) ⟨173861, by rfl⟩) R347723
theorem R35207 : Reach 35207 := rs (se 1 (by rfl) ⟨26405, by rfl⟩) R52811
theorem R494261 : Reach 494261 := rs (se 5 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R35599 : Reach 35599 := rs (se 1 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) R37441
theorem R36139 : Reach 36139 := rs (se 1 (by rfl) ⟨27104, by rfl⟩) R54209
theorem R69011 : Reach 69011 := rs (se 1 (by rfl) ⟨51758, by rfl⟩) R103517
theorem R36281 : Reach 36281 := rs (se 2 (by rfl) ⟨13605, by rfl⟩) R27211
theorem R298525 : Reach 298525 := rs (se 3 (by rfl) ⟨55973, by rfl⟩) R111947
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R36983 : Reach 36983 := rs (se 1 (by rfl) ⟨27737, by rfl⟩) R55475
theorem R102707 : Reach 102707 := rs (se 1 (by rfl) ⟨77030, by rfl⟩) R154061
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R37435 : Reach 37435 := rs (se 1 (by rfl) ⟨28076, by rfl⟩) R56153
theorem R103031 : Reach 103031 := rs (se 1 (by rfl) ⟨77273, by rfl⟩) R154547
theorem R37523 : Reach 37523 := rs (se 1 (by rfl) ⟨28142, by rfl⟩) R56285
theorem R168641 : Reach 168641 := rs (se 2 (by rfl) ⟨63240, by rfl⟩) R126481
theorem R37577 : Reach 37577 := rs (se 2 (by rfl) ⟨14091, by rfl⟩) R28183
theorem R70415 : Reach 70415 := rs (se 1 (by rfl) ⟨52811, by rfl⟩) R105623
theorem R70685 : Reach 70685 := rs (se 3 (by rfl) ⟨13253, by rfl⟩) R26507
theorem R37921 : Reach 37921 := rs (se 2 (by rfl) ⟨14220, by rfl⟩) R28441
theorem R38279 : Reach 38279 := rs (se 1 (by rfl) ⟨28709, by rfl⟩) R57419
theorem R104003 : Reach 104003 := rs (se 1 (by rfl) ⟨78002, by rfl⟩) R156005
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) R25687
theorem R104327 : Reach 104327 := rs (se 1 (by rfl) ⟨78245, by rfl⟩) R156491
theorem R38927 : Reach 38927 := rs (se 1 (by rfl) ⟨29195, by rfl⟩) R58391
theorem R38971 : Reach 38971 := rs (se 1 (by rfl) ⟨29228, by rfl⟩) R58457
theorem R72089 : Reach 72089 := rs (se 2 (by rfl) ⟨27033, by rfl⟩) R54067
theorem R39457 : Reach 39457 := rs (se 2 (by rfl) ⟨14796, by rfl⟩) R29593
theorem R39467 : Reach 39467 := rs (se 1 (by rfl) ⟨29600, by rfl⟩) R59201
theorem R72791 : Reach 72791 := rs (se 1 (by rfl) ⟨54593, by rfl⟩) R109187
theorem R73169 : Reach 73169 := rs (se 2 (by rfl) ⟨27438, by rfl⟩) R54877
theorem R73277 : Reach 73277 := rs (se 3 (by rfl) ⟨13739, by rfl⟩) R27479
theorem R40763 : Reach 40763 := rs (se 1 (by rfl) ⟨30572, by rfl⟩) R61145
theorem R172043 : Reach 172043 := rs (se 1 (by rfl) ⟨129032, by rfl⟩) R258065
theorem R41249 : Reach 41249 := rs (se 2 (by rfl) ⟨15468, by rfl⟩) R30937
theorem R41401 : Reach 41401 := rs (se 2 (by rfl) ⟨15525, by rfl⟩) R31051
theorem R74681 : Reach 74681 := rs (se 2 (by rfl) ⟨28005, by rfl⟩) R56011
theorem R107891 : Reach 107891 := rs (se 1 (by rfl) ⟨80918, by rfl⟩) R161837
theorem R75275 : Reach 75275 := rs (se 1 (by rfl) ⟨56456, by rfl⟩) R112913
theorem R75383 : Reach 75383 := rs (se 1 (by rfl) ⟨56537, by rfl⟩) R113075
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R108377 : Reach 108377 := rs (se 2 (by rfl) ⟨40641, by rfl⟩) R81283
theorem R272281 : Reach 272281 := rs (se 2 (by rfl) ⟨102105, by rfl⟩) R204211
theorem R173987 : Reach 173987 := rs (se 1 (by rfl) ⟨130490, by rfl⟩) R260981
theorem R403501 : Reach 403501 := rs (se 3 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R206981 : Reach 206981 := rs (se 4 (by rfl) ⟨19404, by rfl⟩) R38809
theorem R43193 : Reach 43193 := rs (se 2 (by rfl) ⟨16197, by rfl⟩) R32395
theorem R75977 : Reach 75977 := rs (se 2 (by rfl) ⟨28491, by rfl⟩) R56983
theorem R76241 : Reach 76241 := rs (se 2 (by rfl) ⟨28590, by rfl⟩) R57181
theorem R43535 : Reach 43535 := rs (se 1 (by rfl) ⟨32651, by rfl⟩) R65303
theorem R43553 : Reach 43553 := rs (se 2 (by rfl) ⟨16332, by rfl⟩) R32665
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) R28631
theorem R76355 : Reach 76355 := rs (se 1 (by rfl) ⟨57266, by rfl⟩) R114533
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R109349 : Reach 109349 := rs (se 4 (by rfl) ⟨10251, by rfl⟩) R20503
theorem R43895 : Reach 43895 := rs (se 1 (by rfl) ⟨32921, by rfl⟩) R65843
theorem R76679 : Reach 76679 := rs (se 1 (by rfl) ⟨57509, by rfl⟩) R115019
theorem R76697 : Reach 76697 := rs (se 2 (by rfl) ⟨28761, by rfl⟩) R57523
theorem R142397 : Reach 142397 := rs (se 3 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R77057 : Reach 77057 := rs (se 2 (by rfl) ⟨28896, by rfl⟩) R57793
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R45071 : Reach 45071 := rs (se 1 (by rfl) ⟨33803, by rfl⟩) R67607
theorem R45089 : Reach 45089 := rs (se 2 (by rfl) ⟨16908, by rfl⟩) R33817
theorem R77867 : Reach 77867 := rs (se 1 (by rfl) ⟨58400, by rfl⟩) R116801
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R176417 : Reach 176417 := rs (se 2 (by rfl) ⟨66156, by rfl⟩) R132313
theorem R45431 : Reach 45431 := rs (se 1 (by rfl) ⟨34073, by rfl⟩) R68147
theorem R45611 : Reach 45611 := rs (se 1 (by rfl) ⟨34208, by rfl⟩) R68417
theorem R45883 : Reach 45883 := rs (se 1 (by rfl) ⟨34412, by rfl⟩) R68825
theorem R177011 : Reach 177011 := rs (se 1 (by rfl) ⟨132758, by rfl⟩) R265517
theorem R45971 : Reach 45971 := rs (se 1 (by rfl) ⟨34478, by rfl⟩) R68957
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R46025 : Reach 46025 := rs (se 2 (by rfl) ⟨17259, by rfl⟩) R34519
theorem R177389 : Reach 177389 := rs (se 3 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R79163 : Reach 79163 := rs (se 1 (by rfl) ⟨59372, by rfl⟩) R118745
theorem R406885 : Reach 406885 := rs (se 4 (by rfl) ⟨38145, by rfl⟩) R76291
theorem R144787 : Reach 144787 := rs (se 1 (by rfl) ⟨108590, by rfl⟩) R217181
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R46727 : Reach 46727 := rs (se 1 (by rfl) ⟨35045, by rfl⟩) R70091
theorem R46907 : Reach 46907 := rs (se 1 (by rfl) ⟨35180, by rfl⟩) R70361
theorem R47033 : Reach 47033 := rs (se 2 (by rfl) ⟨17637, by rfl⟩) R35275
theorem R79825 : Reach 79825 := rs (se 2 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R80129 : Reach 80129 := rs (se 2 (by rfl) ⟨30048, by rfl⟩) R60097
theorem R47375 : Reach 47375 := rs (se 1 (by rfl) ⟨35531, by rfl⟩) R71063
theorem R47393 : Reach 47393 := rs (se 2 (by rfl) ⟨17772, by rfl⟩) R35545
theorem R47447 : Reach 47447 := rs (se 1 (by rfl) ⟨35585, by rfl⟩) R71171
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R47627 : Reach 47627 := rs (se 1 (by rfl) ⟨35720, by rfl⟩) R71441
theorem R47735 : Reach 47735 := rs (se 1 (by rfl) ⟨35801, by rfl⟩) R71603
theorem R80585 : Reach 80585 := rs (se 2 (by rfl) ⟨30219, by rfl⟩) R60439
theorem R47915 : Reach 47915 := rs (se 1 (by rfl) ⟨35936, by rfl⟩) R71873
theorem R47987 : Reach 47987 := rs (se 1 (by rfl) ⟨35990, by rfl⟩) R71981
theorem R113561 : Reach 113561 := rs (se 2 (by rfl) ⟨42585, by rfl⟩) R85171
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R48275 : Reach 48275 := rs (se 1 (by rfl) ⟨36206, by rfl⟩) R72413
theorem R48329 : Reach 48329 := rs (se 2 (by rfl) ⟨18123, by rfl⟩) R36247
theorem R49031 : Reach 49031 := rs (se 1 (by rfl) ⟨36773, by rfl⟩) R73547
theorem R49049 : Reach 49049 := rs (se 2 (by rfl) ⟨18393, by rfl⟩) R36787
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R49211 : Reach 49211 := rs (se 1 (by rfl) ⟨36908, by rfl⟩) R73817
theorem R49337 : Reach 49337 := rs (se 2 (by rfl) ⟨18501, by rfl⟩) R37003
theorem R49409 : Reach 49409 := rs (se 2 (by rfl) ⟨18528, by rfl⟩) R37057
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R49679 : Reach 49679 := rs (se 1 (by rfl) ⟨37259, by rfl⟩) R74519
theorem R49697 : Reach 49697 := rs (se 2 (by rfl) ⟨18636, by rfl⟩) R37273
theorem R49751 : Reach 49751 := rs (se 1 (by rfl) ⟨37313, by rfl⟩) R74627
theorem R49931 : Reach 49931 := rs (se 1 (by rfl) ⟨37448, by rfl⟩) R74897
theorem R50039 : Reach 50039 := rs (se 1 (by rfl) ⟨37529, by rfl⟩) R75059
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) R62155
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) R37579
theorem R50219 : Reach 50219 := rs (se 1 (by rfl) ⟨37664, by rfl⟩) R75329
theorem R50291 : Reach 50291 := rs (se 1 (by rfl) ⟨37718, by rfl⟩) R75437
theorem R50323 : Reach 50323 := rs (se 1 (by rfl) ⟨37742, by rfl⟩) R75485
theorem R50579 : Reach 50579 := rs (se 1 (by rfl) ⟨37934, by rfl⟩) R75869
theorem R116153 : Reach 116153 := rs (se 2 (by rfl) ⟨43557, by rfl⟩) R87115
theorem R50633 : Reach 50633 := rs (se 2 (by rfl) ⟨18987, by rfl⟩) R37975
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R247373 : Reach 247373 := rs (se 3 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R50807 : Reach 50807 := rs (se 1 (by rfl) ⟨38105, by rfl⟩) R76211
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R83713 : Reach 83713 := rs (se 2 (by rfl) ⟨31392, by rfl⟩) R62785
theorem R51335 : Reach 51335 := rs (se 1 (by rfl) ⟨38501, by rfl⟩) R77003
theorem R51353 : Reach 51353 := rs (se 2 (by rfl) ⟨19257, by rfl⟩) R38515
theorem R51515 : Reach 51515 := rs (se 1 (by rfl) ⟨38636, by rfl⟩) R77273
theorem R51641 : Reach 51641 := rs (se 2 (by rfl) ⟨19365, by rfl⟩) R38731
theorem R51713 : Reach 51713 := rs (se 2 (by rfl) ⟨19392, by rfl⟩) R38785
theorem R51745 : Reach 51745 := rs (se 2 (by rfl) ⟨19404, by rfl⟩) R38809
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R51799 : Reach 51799 := rs (se 1 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R117449 : Reach 117449 := rs (se 2 (by rfl) ⟨44043, by rfl⟩) R88087
theorem R51983 : Reach 51983 := rs (se 1 (by rfl) ⟨38987, by rfl⟩) R77975
theorem R52001 : Reach 52001 := rs (se 2 (by rfl) ⟨19500, by rfl⟩) R39001
theorem R52055 : Reach 52055 := rs (se 1 (by rfl) ⟨39041, by rfl⟩) R78083
theorem R52103 : Reach 52103 := rs (se 1 (by rfl) ⟨39077, by rfl⟩) R78155
theorem R52235 : Reach 52235 := rs (se 1 (by rfl) ⟨39176, by rfl⟩) R78353
theorem R52267 : Reach 52267 := rs (se 1 (by rfl) ⟨39200, by rfl⟩) R78401
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R52343 : Reach 52343 := rs (se 1 (by rfl) ⟨39257, by rfl⟩) R78515
theorem R52523 : Reach 52523 := rs (se 1 (by rfl) ⟨39392, by rfl⟩) R78785
theorem R52595 : Reach 52595 := rs (se 1 (by rfl) ⟨39446, by rfl⟩) R78893
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R52751 : Reach 52751 := rs (se 1 (by rfl) ⟨39563, by rfl⟩) R79127
theorem R20027 : Reach 20027 := rs (se 1 (by rfl) ⟨15020, by rfl⟩) R30041
theorem R20103 : Reach 20103 := rs (se 1 (by rfl) ⟨15077, by rfl⟩) R30155
theorem R20111 : Reach 20111 := rs (se 1 (by rfl) ⟨15083, by rfl⟩) R30167
theorem R52883 : Reach 52883 := rs (se 1 (by rfl) ⟨39662, by rfl⟩) R79325
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R20155 : Reach 20155 := rs (se 1 (by rfl) ⟨15116, by rfl⟩) R30233
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R20231 : Reach 20231 := rs (se 1 (by rfl) ⟨15173, by rfl⟩) R30347
theorem R20239 : Reach 20239 := rs (se 1 (by rfl) ⟨15179, by rfl⟩) R30359
theorem R20283 : Reach 20283 := rs (se 1 (by rfl) ⟨15212, by rfl⟩) R30425
theorem R20359 : Reach 20359 := rs (se 1 (by rfl) ⟨15269, by rfl⟩) R30539
theorem R20367 : Reach 20367 := rs (se 1 (by rfl) ⟨15275, by rfl⟩) R30551
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R20411 : Reach 20411 := rs (se 1 (by rfl) ⟨15308, by rfl⟩) R30617
theorem R20487 : Reach 20487 := rs (se 1 (by rfl) ⟨15365, by rfl⟩) R30731
theorem R20495 : Reach 20495 := rs (se 1 (by rfl) ⟨15371, by rfl⟩) R30743
theorem R20539 : Reach 20539 := rs (se 1 (by rfl) ⟨15404, by rfl⟩) R30809
theorem R20615 : Reach 20615 := rs (se 1 (by rfl) ⟨15461, by rfl⟩) R30923
theorem R20623 : Reach 20623 := rs (se 1 (by rfl) ⟨15467, by rfl⟩) R30935
theorem R20667 : Reach 20667 := rs (se 1 (by rfl) ⟨15500, by rfl⟩) R31001
theorem R20743 : Reach 20743 := rs (se 1 (by rfl) ⟨15557, by rfl⟩) R31115
theorem R20751 : Reach 20751 := rs (se 1 (by rfl) ⟨15563, by rfl⟩) R31127
theorem R20795 : Reach 20795 := rs (se 1 (by rfl) ⟨15596, by rfl⟩) R31193
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R20871 : Reach 20871 := rs (se 1 (by rfl) ⟨15653, by rfl⟩) R31307
theorem R20879 : Reach 20879 := rs (se 1 (by rfl) ⟨15659, by rfl⟩) R31319
theorem R20923 : Reach 20923 := rs (se 1 (by rfl) ⟨15692, by rfl⟩) R31385
theorem R20999 : Reach 20999 := rs (se 1 (by rfl) ⟨15749, by rfl⟩) R31499
theorem R21007 : Reach 21007 := rs (se 1 (by rfl) ⟨15755, by rfl⟩) R31511
theorem R21051 : Reach 21051 := rs (se 1 (by rfl) ⟨15788, by rfl⟩) R31577
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) R20183
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R21127 : Reach 21127 := rs (se 1 (by rfl) ⟨15845, by rfl⟩) R31691
theorem R21135 : Reach 21135 := rs (se 1 (by rfl) ⟨15851, by rfl⟩) R31703
theorem R21179 : Reach 21179 := rs (se 1 (by rfl) ⟨15884, by rfl⟩) R31769
theorem R54017 : Reach 54017 := rs (se 2 (by rfl) ⟨20256, by rfl⟩) R40513
theorem R21255 : Reach 21255 := rs (se 1 (by rfl) ⟨15941, by rfl⟩) R31883
theorem R21263 : Reach 21263 := rs (se 1 (by rfl) ⟨15947, by rfl⟩) R31895
theorem R21307 : Reach 21307 := rs (se 1 (by rfl) ⟨15980, by rfl⟩) R31961
theorem R21383 : Reach 21383 := rs (se 1 (by rfl) ⟨16037, by rfl⟩) R32075
theorem R21391 : Reach 21391 := rs (se 1 (by rfl) ⟨16043, by rfl⟩) R32087
theorem R250775 : Reach 250775 := rs (se 1 (by rfl) ⟨188081, by rfl⟩) R376163
theorem R21435 : Reach 21435 := rs (se 1 (by rfl) ⟨16076, by rfl⟩) R32153
theorem R21511 : Reach 21511 := rs (se 1 (by rfl) ⟨16133, by rfl⟩) R32267
theorem R54283 : Reach 54283 := rs (se 1 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R21519 : Reach 21519 := rs (se 1 (by rfl) ⟨16139, by rfl⟩) R32279
theorem R21563 : Reach 21563 := rs (se 1 (by rfl) ⟨16172, by rfl⟩) R32345
theorem R87101 : Reach 87101 := rs (se 3 (by rfl) ⟨16331, by rfl⟩) R32663
theorem R54391 : Reach 54391 := rs (se 1 (by rfl) ⟨40793, by rfl⟩) R81587
theorem R21639 : Reach 21639 := rs (se 1 (by rfl) ⟨16229, by rfl⟩) R32459
theorem R21647 : Reach 21647 := rs (se 1 (by rfl) ⟨16235, by rfl⟩) R32471
theorem R21691 : Reach 21691 := rs (se 1 (by rfl) ⟨16268, by rfl⟩) R32537
theorem R21767 : Reach 21767 := rs (se 1 (by rfl) ⟨16325, by rfl⟩) R32651
theorem R21775 : Reach 21775 := rs (se 1 (by rfl) ⟨16331, by rfl⟩) R32663
theorem R21819 : Reach 21819 := rs (se 1 (by rfl) ⟨16364, by rfl⟩) R32729
theorem R21895 : Reach 21895 := rs (se 1 (by rfl) ⟨16421, by rfl⟩) R32843
theorem R21903 : Reach 21903 := rs (se 1 (by rfl) ⟨16427, by rfl⟩) R32855
theorem R21947 : Reach 21947 := rs (se 1 (by rfl) ⟨16460, by rfl⟩) R32921
theorem R22023 : Reach 22023 := rs (se 1 (by rfl) ⟨16517, by rfl⟩) R33035
theorem R22031 : Reach 22031 := rs (se 1 (by rfl) ⟨16523, by rfl⟩) R33047
theorem R54827 : Reach 54827 := rs (se 1 (by rfl) ⟨41120, by rfl⟩) R82241
theorem R22075 : Reach 22075 := rs (se 1 (by rfl) ⟨16556, by rfl⟩) R33113
theorem R22151 : Reach 22151 := rs (se 1 (by rfl) ⟨16613, by rfl⟩) R33227
theorem R22159 : Reach 22159 := rs (se 1 (by rfl) ⟨16619, by rfl⟩) R33239
theorem R22203 : Reach 22203 := rs (se 1 (by rfl) ⟨16652, by rfl⟩) R33305
theorem R22279 : Reach 22279 := rs (se 1 (by rfl) ⟨16709, by rfl⟩) R33419
theorem R22287 : Reach 22287 := rs (se 1 (by rfl) ⟨16715, by rfl⟩) R33431
theorem R22331 : Reach 22331 := rs (se 1 (by rfl) ⟨16748, by rfl⟩) R33497
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R22407 : Reach 22407 := rs (se 1 (by rfl) ⟨16805, by rfl⟩) R33611
theorem R22415 : Reach 22415 := rs (se 1 (by rfl) ⟨16811, by rfl⟩) R33623
theorem R55187 : Reach 55187 := rs (se 1 (by rfl) ⟨41390, by rfl⟩) R82781
theorem R22459 : Reach 22459 := rs (se 1 (by rfl) ⟨16844, by rfl⟩) R33689
theorem R22535 : Reach 22535 := rs (se 1 (by rfl) ⟨16901, by rfl⟩) R33803
theorem R22543 : Reach 22543 := rs (se 1 (by rfl) ⟨16907, by rfl⟩) R33815
theorem R22587 : Reach 22587 := rs (se 1 (by rfl) ⟨16940, by rfl⟩) R33881
theorem R22663 : Reach 22663 := rs (se 1 (by rfl) ⟨16997, by rfl⟩) R33995
theorem R22671 : Reach 22671 := rs (se 1 (by rfl) ⟨17003, by rfl⟩) R34007
theorem R22715 : Reach 22715 := rs (se 1 (by rfl) ⟨17036, by rfl⟩) R34073
theorem R22791 : Reach 22791 := rs (se 1 (by rfl) ⟨17093, by rfl⟩) R34187
theorem R22799 : Reach 22799 := rs (se 1 (by rfl) ⟨17099, by rfl⟩) R34199
theorem R22843 : Reach 22843 := rs (se 1 (by rfl) ⟨17132, by rfl⟩) R34265
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R55687 : Reach 55687 := rs (se 1 (by rfl) ⟨41765, by rfl⟩) R83531
theorem R22919 : Reach 22919 := rs (se 1 (by rfl) ⟨17189, by rfl⟩) R34379
theorem R22927 : Reach 22927 := rs (se 1 (by rfl) ⟨17195, by rfl⟩) R34391
theorem R22971 : Reach 22971 := rs (se 1 (by rfl) ⟨17228, by rfl⟩) R34457
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R23047 : Reach 23047 := rs (se 1 (by rfl) ⟨17285, by rfl⟩) R34571
theorem R23055 : Reach 23055 := rs (se 1 (by rfl) ⟨17291, by rfl⟩) R34583
theorem R23099 : Reach 23099 := rs (se 1 (by rfl) ⟨17324, by rfl⟩) R34649
theorem R23175 : Reach 23175 := rs (se 1 (by rfl) ⟨17381, by rfl⟩) R34763
theorem R23183 : Reach 23183 := rs (se 1 (by rfl) ⟨17387, by rfl⟩) R34775
theorem R55961 : Reach 55961 := rs (se 2 (by rfl) ⟨20985, by rfl⟩) R41971
theorem R23227 : Reach 23227 := rs (se 1 (by rfl) ⟨17420, by rfl⟩) R34841
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) R33305
theorem R23303 : Reach 23303 := rs (se 1 (by rfl) ⟨17477, by rfl⟩) R34955
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R23311 : Reach 23311 := rs (se 1 (by rfl) ⟨17483, by rfl⟩) R34967
theorem R56123 : Reach 56123 := rs (se 1 (by rfl) ⟨42092, by rfl⟩) R84185
theorem R23355 : Reach 23355 := rs (se 1 (by rfl) ⟨17516, by rfl⟩) R35033
theorem R23431 : Reach 23431 := rs (se 1 (by rfl) ⟨17573, by rfl⟩) R35147
theorem R23439 : Reach 23439 := rs (se 1 (by rfl) ⟨17579, by rfl⟩) R35159
theorem R23483 : Reach 23483 := rs (se 1 (by rfl) ⟨17612, by rfl⟩) R35225
theorem R56335 : Reach 56335 := rs (se 1 (by rfl) ⟨42251, by rfl⟩) R84503
theorem R23611 : Reach 23611 := rs (se 1 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R56609 : Reach 56609 := rs (se 2 (by rfl) ⟨21228, by rfl⟩) R42457
theorem R24079 : Reach 24079 := rs (se 1 (by rfl) ⟨18059, by rfl⟩) R36119
theorem R57089 : Reach 57089 := rs (se 2 (by rfl) ⟨21408, by rfl⟩) R42817
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R24439 : Reach 24439 := rs (se 1 (by rfl) ⟨18329, by rfl⟩) R36659
theorem R24583 : Reach 24583 := rs (se 1 (by rfl) ⟨18437, by rfl⟩) R36875
theorem R24619 : Reach 24619 := rs (se 1 (by rfl) ⟨18464, by rfl⟩) R36929
theorem R24763 : Reach 24763 := rs (se 1 (by rfl) ⟨18572, by rfl⟩) R37145
theorem R57611 : Reach 57611 := rs (se 1 (by rfl) ⟨43208, by rfl⟩) R86417
theorem R25231 : Reach 25231 := rs (se 1 (by rfl) ⟨18923, by rfl⟩) R37847
theorem R123565 : Reach 123565 := rs (se 3 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R58259 : Reach 58259 := rs (se 1 (by rfl) ⟨43694, by rfl⟩) R87389
theorem R25591 : Reach 25591 := rs (se 1 (by rfl) ⟨19193, by rfl⟩) R38387
theorem R58411 : Reach 58411 := rs (se 1 (by rfl) ⟨43808, by rfl⟩) R87617
theorem R25735 : Reach 25735 := rs (se 1 (by rfl) ⟨19301, by rfl⟩) R38603
theorem R25771 : Reach 25771 := rs (se 1 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R58553 : Reach 58553 := rs (se 2 (by rfl) ⟨21957, by rfl⟩) R43915
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R124211 : Reach 124211 := rs (se 1 (by rfl) ⟨93158, by rfl⟩) R186317
theorem R25915 : Reach 25915 := rs (se 1 (by rfl) ⟨19436, by rfl⟩) R38873
theorem R58913 : Reach 58913 := rs (se 2 (by rfl) ⟨22092, by rfl⟩) R44185
theorem R59015 : Reach 59015 := rs (se 1 (by rfl) ⟨44261, by rfl⟩) R88523
theorem R26383 : Reach 26383 := rs (se 1 (by rfl) ⟨19787, by rfl⟩) R39575
theorem R26411 : Reach 26411 := rs (se 1 (by rfl) ⟨19808, by rfl⟩) R39617
theorem R59251 : Reach 59251 := rs (se 1 (by rfl) ⟨44438, by rfl⟩) R88877
theorem R59255 : Reach 59255 := rs (se 1 (by rfl) ⟨44441, by rfl⟩) R88883
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R59393 : Reach 59393 := rs (se 2 (by rfl) ⟨22272, by rfl⟩) R44545
theorem R125165 : Reach 125165 := rs (se 3 (by rfl) ⟨23468, by rfl⟩) R46937
theorem R26887 : Reach 26887 := rs (se 1 (by rfl) ⟨20165, by rfl⟩) R40331
theorem R59915 : Reach 59915 := rs (se 1 (by rfl) ⟨44936, by rfl⟩) R89873
theorem R27307 : Reach 27307 := rs (se 1 (by rfl) ⟨20480, by rfl⟩) R40961
theorem R27535 : Reach 27535 := rs (se 1 (by rfl) ⟨20651, by rfl⟩) R41303
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R27833 : Reach 27833 := rs (se 2 (by rfl) ⟨10437, by rfl⟩) R20875
theorem R158921 : Reach 158921 := rs (se 2 (by rfl) ⟨59595, by rfl⟩) R119191
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R28279 : Reach 28279 := rs (se 1 (by rfl) ⟨21209, by rfl⟩) R42419
theorem R28345 : Reach 28345 := rs (se 2 (by rfl) ⟨10629, by rfl⟩) R21259
theorem R61199 : Reach 61199 := rs (se 1 (by rfl) ⟨45899, by rfl⟩) R91799
theorem R28603 : Reach 28603 := rs (se 1 (by rfl) ⟨21452, by rfl⟩) R42905
theorem R61499 : Reach 61499 := rs (se 1 (by rfl) ⟨46124, by rfl⟩) R92249
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R61555 : Reach 61555 := rs (se 1 (by rfl) ⟨46166, by rfl⟩) R92333
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) R35417
theorem R29099 : Reach 29099 := rs (se 1 (by rfl) ⟨21824, by rfl⟩) R43649
theorem R61897 : Reach 61897 := rs (se 2 (by rfl) ⟨23211, by rfl⟩) R46423
theorem R29575 : Reach 29575 := rs (se 1 (by rfl) ⟨22181, by rfl⟩) R44363
theorem R29641 : Reach 29641 := rs (se 2 (by rfl) ⟨11115, by rfl⟩) R22231
theorem R259159 : Reach 259159 := rs (se 1 (by rfl) ⟨194369, by rfl⟩) R388739
theorem R30011 : Reach 30011 := rs (se 1 (by rfl) ⟨22508, by rfl⟩) R45017
theorem R30071 : Reach 30071 := rs (se 1 (by rfl) ⟨22553, by rfl⟩) R45107
theorem R30095 : Reach 30095 := rs (se 1 (by rfl) ⟨22571, by rfl⟩) R45143
theorem R30137 : Reach 30137 := rs (se 2 (by rfl) ⟨11301, by rfl⟩) R22603
theorem R128465 : Reach 128465 := rs (se 2 (by rfl) ⟨48174, by rfl⟩) R96349
theorem R30215 : Reach 30215 := rs (se 1 (by rfl) ⟨22661, by rfl⟩) R45323
theorem R30251 : Reach 30251 := rs (se 1 (by rfl) ⟨22688, by rfl⟩) R45377
theorem R30281 : Reach 30281 := rs (se 2 (by rfl) ⟨11355, by rfl⟩) R22711
theorem R30395 : Reach 30395 := rs (se 1 (by rfl) ⟨22796, by rfl⟩) R45593
theorem R30455 : Reach 30455 := rs (se 1 (by rfl) ⟨22841, by rfl⟩) R45683
theorem R30479 : Reach 30479 := rs (se 1 (by rfl) ⟨22859, by rfl⟩) R45719
theorem R30521 : Reach 30521 := rs (se 2 (by rfl) ⟨11445, by rfl⟩) R22891
theorem R30599 : Reach 30599 := rs (se 1 (by rfl) ⟨22949, by rfl⟩) R45899
theorem R30635 : Reach 30635 := rs (se 1 (by rfl) ⟨22976, by rfl⟩) R45953
theorem R30665 : Reach 30665 := rs (se 2 (by rfl) ⟨11499, by rfl⟩) R22999
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R30779 : Reach 30779 := rs (se 1 (by rfl) ⟨23084, by rfl⟩) R46169
theorem R30839 : Reach 30839 := rs (se 1 (by rfl) ⟨23129, by rfl⟩) R46259
theorem R30863 : Reach 30863 := rs (se 1 (by rfl) ⟨23147, by rfl⟩) R46295
theorem R30905 : Reach 30905 := rs (se 2 (by rfl) ⟨11589, by rfl⟩) R23179
theorem R30983 : Reach 30983 := rs (se 1 (by rfl) ⟨23237, by rfl⟩) R46475
theorem R31019 : Reach 31019 := rs (se 1 (by rfl) ⟨23264, by rfl⟩) R46529
theorem R31049 : Reach 31049 := rs (se 2 (by rfl) ⟨11643, by rfl⟩) R23287
theorem R31163 : Reach 31163 := rs (se 1 (by rfl) ⟨23372, by rfl⟩) R46745
theorem R31223 : Reach 31223 := rs (se 1 (by rfl) ⟨23417, by rfl⟩) R46835
theorem R31247 : Reach 31247 := rs (se 1 (by rfl) ⟨23435, by rfl⟩) R46871
theorem R31289 : Reach 31289 := rs (se 2 (by rfl) ⟨11733, by rfl⟩) R23467
theorem R64061 : Reach 64061 := rs (se 3 (by rfl) ⟨12011, by rfl⟩) R24023
theorem R31351 : Reach 31351 := rs (se 1 (by rfl) ⟨23513, by rfl⟩) R47027
theorem R31367 : Reach 31367 := rs (se 1 (by rfl) ⟨23525, by rfl⟩) R47051
theorem R31403 : Reach 31403 := rs (se 1 (by rfl) ⟨23552, by rfl⟩) R47105
theorem R31433 : Reach 31433 := rs (se 2 (by rfl) ⟨11787, by rfl⟩) R23575
theorem R64289 : Reach 64289 := rs (se 2 (by rfl) ⟨24108, by rfl⟩) R48217
theorem R31547 : Reach 31547 := rs (se 1 (by rfl) ⟨23660, by rfl⟩) R47321
theorem R31607 : Reach 31607 := rs (se 1 (by rfl) ⟨23705, by rfl⟩) R47411
theorem R31673 : Reach 31673 := rs (se 2 (by rfl) ⟨11877, by rfl⟩) R23755
theorem R31787 : Reach 31787 := rs (se 1 (by rfl) ⟨23840, by rfl⟩) R47681
theorem R64631 : Reach 64631 := rs (se 1 (by rfl) ⟨48473, by rfl⟩) R96947
theorem R32015 : Reach 32015 := rs (se 1 (by rfl) ⟨24011, by rfl⟩) R48023
theorem R32059 : Reach 32059 := rs (se 1 (by rfl) ⟨24044, by rfl⟩) R48089
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R32135 : Reach 32135 := rs (se 1 (by rfl) ⟨24101, by rfl⟩) R48203
theorem R32201 : Reach 32201 := rs (se 2 (by rfl) ⟨12075, by rfl⟩) R24151
theorem R32315 : Reach 32315 := rs (se 1 (by rfl) ⟨24236, by rfl⟩) R48473
theorem R32375 : Reach 32375 := rs (se 1 (by rfl) ⟨24281, by rfl⟩) R48563
theorem R32441 : Reach 32441 := rs (se 2 (by rfl) ⟨12165, by rfl⟩) R24331
theorem R32555 : Reach 32555 := rs (se 1 (by rfl) ⟨24416, by rfl⟩) R48833
theorem R393113 : Reach 393113 := rs (se 2 (by rfl) ⟨147417, by rfl⟩) R294835
theorem R32777 : Reach 32777 := rs (se 2 (by rfl) ⟨12291, by rfl⟩) R24583
theorem R32807 : Reach 32807 := rs (se 1 (by rfl) ⟨24605, by rfl⟩) R49211
theorem R32825 : Reach 32825 := rs (se 2 (by rfl) ⟨12309, by rfl⟩) R24619
theorem R131129 : Reach 131129 := rs (se 2 (by rfl) ⟨49173, by rfl⟩) R98347
theorem R32891 : Reach 32891 := rs (se 1 (by rfl) ⟨24668, by rfl⟩) R49337
theorem R32939 : Reach 32939 := rs (se 1 (by rfl) ⟨24704, by rfl⟩) R49409
theorem R33017 : Reach 33017 := rs (se 2 (by rfl) ⟨12381, by rfl⟩) R24763
theorem R98621 : Reach 98621 := rs (se 3 (by rfl) ⟨18491, by rfl⟩) R36983
theorem R33119 : Reach 33119 := rs (se 1 (by rfl) ⟨24839, by rfl⟩) R49679
theorem R33131 : Reach 33131 := rs (se 1 (by rfl) ⟨24848, by rfl⟩) R49697
theorem R33167 : Reach 33167 := rs (se 1 (by rfl) ⟨24875, by rfl⟩) R49751
theorem R33287 : Reach 33287 := rs (se 1 (by rfl) ⟨24965, by rfl⟩) R49931
theorem R33359 : Reach 33359 := rs (se 1 (by rfl) ⟨25019, by rfl⟩) R50039
theorem R33479 : Reach 33479 := rs (se 1 (by rfl) ⟨25109, by rfl⟩) R50219
theorem R33527 : Reach 33527 := rs (se 1 (by rfl) ⟨25145, by rfl⟩) R50291
theorem R33641 : Reach 33641 := rs (se 2 (by rfl) ⟨12615, by rfl⟩) R25231
theorem R164753 : Reach 164753 := rs (se 2 (by rfl) ⟨61782, by rfl⟩) R123565
theorem R33719 : Reach 33719 := rs (se 1 (by rfl) ⟨25289, by rfl⟩) R50579
theorem R33755 : Reach 33755 := rs (se 1 (by rfl) ⟨25316, by rfl⟩) R50633
theorem R164915 : Reach 164915 := rs (se 1 (by rfl) ⟨123686, by rfl⟩) R247373
theorem R33871 : Reach 33871 := rs (se 1 (by rfl) ⟨25403, by rfl⟩) R50807
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R132299 : Reach 132299 := rs (se 1 (by rfl) ⟨99224, by rfl⟩) R198449
theorem R34121 : Reach 34121 := rs (se 2 (by rfl) ⟨12795, by rfl⟩) R25591
theorem R34223 : Reach 34223 := rs (se 1 (by rfl) ⟨25667, by rfl⟩) R51335
theorem R34235 : Reach 34235 := rs (se 1 (by rfl) ⟨25676, by rfl⟩) R51353
theorem R34313 : Reach 34313 := rs (se 2 (by rfl) ⟨12867, by rfl⟩) R25735
theorem R67097 : Reach 67097 := rs (se 2 (by rfl) ⟨25161, by rfl⟩) R50323
theorem R34343 : Reach 34343 := rs (se 1 (by rfl) ⟨25757, by rfl⟩) R51515
theorem R34361 : Reach 34361 := rs (se 2 (by rfl) ⟨12885, by rfl⟩) R25771
theorem R34427 : Reach 34427 := rs (se 1 (by rfl) ⟨25820, by rfl⟩) R51641
theorem R34475 : Reach 34475 := rs (se 1 (by rfl) ⟨25856, by rfl⟩) R51713
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R34553 : Reach 34553 := rs (se 2 (by rfl) ⟨12957, by rfl⟩) R25915
theorem R329507 : Reach 329507 := rs (se 1 (by rfl) ⟨247130, by rfl⟩) R494261
theorem R34655 : Reach 34655 := rs (se 1 (by rfl) ⟨25991, by rfl⟩) R51983
theorem R34667 : Reach 34667 := rs (se 1 (by rfl) ⟨26000, by rfl⟩) R52001
theorem R34703 : Reach 34703 := rs (se 1 (by rfl) ⟨26027, by rfl⟩) R52055
theorem R34735 : Reach 34735 := rs (se 1 (by rfl) ⟨26051, by rfl⟩) R52103
theorem R296885 : Reach 296885 := rs (se 5 (by rfl) ⟨13916, by rfl⟩) R27833
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R34823 : Reach 34823 := rs (se 1 (by rfl) ⟨26117, by rfl⟩) R52235
theorem R34895 : Reach 34895 := rs (se 1 (by rfl) ⟨26171, by rfl⟩) R52343
theorem R35015 : Reach 35015 := rs (se 1 (by rfl) ⟨26261, by rfl⟩) R52523
theorem R35063 : Reach 35063 := rs (se 1 (by rfl) ⟨26297, by rfl⟩) R52595
theorem R35167 : Reach 35167 := rs (se 1 (by rfl) ⟨26375, by rfl⟩) R52751
theorem R35177 : Reach 35177 := rs (se 2 (by rfl) ⟨13191, by rfl⟩) R26383
theorem R35255 : Reach 35255 := rs (se 1 (by rfl) ⟨26441, by rfl⟩) R52883
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R363041 : Reach 363041 := rs (se 2 (by rfl) ⟨136140, by rfl⟩) R272281
theorem R68471 : Reach 68471 := rs (se 1 (by rfl) ⟨51353, by rfl⟩) R102707
theorem R35849 : Reach 35849 := rs (se 2 (by rfl) ⟨13443, by rfl⟩) R26887
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R68687 : Reach 68687 := rs (se 1 (by rfl) ⟨51515, by rfl⟩) R103031
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R36011 : Reach 36011 := rs (se 1 (by rfl) ⟨27008, by rfl⟩) R54017
theorem R167183 : Reach 167183 := rs (se 1 (by rfl) ⟨125387, by rfl⟩) R250775
theorem R68993 : Reach 68993 := rs (se 2 (by rfl) ⟨25872, by rfl⟩) R51745
theorem R69065 : Reach 69065 := rs (se 2 (by rfl) ⟨25899, by rfl⟩) R51799
theorem R331229 : Reach 331229 := rs (se 3 (by rfl) ⟨62105, by rfl⟩) R124211
theorem R36409 : Reach 36409 := rs (se 2 (by rfl) ⟨13653, by rfl⟩) R27307
theorem R36551 : Reach 36551 := rs (se 1 (by rfl) ⟨27413, by rfl⟩) R54827
theorem R69335 : Reach 69335 := rs (se 1 (by rfl) ⟨52001, by rfl⟩) R104003
theorem R36713 : Reach 36713 := rs (se 2 (by rfl) ⟨13767, by rfl⟩) R27535
theorem R69551 : Reach 69551 := rs (se 1 (by rfl) ⟨52163, by rfl⟩) R104327
theorem R36791 : Reach 36791 := rs (se 1 (by rfl) ⟨27593, by rfl⟩) R55187
theorem R69689 : Reach 69689 := rs (se 2 (by rfl) ⟨26133, by rfl⟩) R52267
theorem R37111 : Reach 37111 := rs (se 1 (by rfl) ⟨27833, by rfl⟩) R55667
theorem R37307 : Reach 37307 := rs (se 1 (by rfl) ⟨27980, by rfl⟩) R55961
theorem R37415 : Reach 37415 := rs (se 1 (by rfl) ⟨28061, by rfl⟩) R56123
theorem R398033 : Reach 398033 := rs (se 2 (by rfl) ⟨149262, by rfl⟩) R298525
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) R26411
theorem R37705 : Reach 37705 := rs (se 2 (by rfl) ⟨14139, by rfl⟩) R28279
theorem R37739 : Reach 37739 := rs (se 1 (by rfl) ⟨28304, by rfl⟩) R56609
theorem R37793 : Reach 37793 := rs (se 2 (by rfl) ⟨14172, by rfl⟩) R28345
theorem R38059 : Reach 38059 := rs (se 1 (by rfl) ⟨28544, by rfl⟩) R57089
theorem R38137 : Reach 38137 := rs (se 2 (by rfl) ⟨14301, by rfl⟩) R28603
theorem R38407 : Reach 38407 := rs (se 1 (by rfl) ⟨28805, by rfl⟩) R57611
theorem R38839 : Reach 38839 := rs (se 1 (by rfl) ⟨29129, by rfl⟩) R58259
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) R53821
theorem R39035 : Reach 39035 := rs (se 1 (by rfl) ⟨29276, by rfl⟩) R58553
theorem R71927 : Reach 71927 := rs (se 1 (by rfl) ⟨53945, by rfl⟩) R107891
theorem R39275 : Reach 39275 := rs (se 1 (by rfl) ⟨29456, by rfl⟩) R58913
theorem R39433 : Reach 39433 := rs (se 2 (by rfl) ⟨14787, by rfl⟩) R29575
theorem R72251 : Reach 72251 := rs (se 1 (by rfl) ⟨54188, by rfl⟩) R108377
theorem R39503 : Reach 39503 := rs (se 1 (by rfl) ⟨29627, by rfl⟩) R59255
theorem R39521 : Reach 39521 := rs (se 2 (by rfl) ⟨14820, by rfl⟩) R29641
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R39595 : Reach 39595 := rs (se 1 (by rfl) ⟨29696, by rfl⟩) R59393
theorem R72377 : Reach 72377 := rs (se 2 (by rfl) ⟨27141, by rfl⟩) R54283
theorem R137987 : Reach 137987 := rs (se 1 (by rfl) ⟨103490, by rfl⟩) R206981
theorem R72521 : Reach 72521 := rs (se 2 (by rfl) ⟨27195, by rfl⟩) R54391
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) R32059
theorem R39943 : Reach 39943 := rs (se 1 (by rfl) ⟨29957, by rfl⟩) R59915
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R72899 : Reach 72899 := rs (se 1 (by rfl) ⟨54674, by rfl⟩) R109349
theorem R105947 : Reach 105947 := rs (se 1 (by rfl) ⟨79460, by rfl⟩) R158921
theorem R40799 : Reach 40799 := rs (se 1 (by rfl) ⟨30599, by rfl⟩) R61199
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R106433 : Reach 106433 := rs (se 2 (by rfl) ⟨39912, by rfl⟩) R79825
theorem R40999 : Reach 40999 := rs (se 1 (by rfl) ⟨30749, by rfl⟩) R61499
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R74249 : Reach 74249 := rs (se 2 (by rfl) ⟨27843, by rfl⟩) R55687
theorem R41801 : Reach 41801 := rs (se 2 (by rfl) ⟨15675, by rfl⟩) R31351
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) R50039
theorem R75113 : Reach 75113 := rs (se 2 (by rfl) ⟨28167, by rfl⟩) R56335
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R42707 : Reach 42707 := rs (se 1 (by rfl) ⟨32030, by rfl⟩) R64061
theorem R42859 : Reach 42859 := rs (se 1 (by rfl) ⟨32144, by rfl⟩) R64289
theorem R75707 : Reach 75707 := rs (se 1 (by rfl) ⟨56780, by rfl⟩) R113561
theorem R43087 : Reach 43087 := rs (se 1 (by rfl) ⟨32315, by rfl⟩) R64631
theorem R632933 : Reach 632933 := rs (se 4 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R108701 : Reach 108701 := rs (se 3 (by rfl) ⟨20381, by rfl⟩) R40763
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R76423 : Reach 76423 := rs (se 1 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R109997 : Reach 109997 := rs (se 3 (by rfl) ⟨20624, by rfl⟩) R41249
theorem R77435 : Reach 77435 := rs (se 1 (by rfl) ⟨58076, by rfl⟩) R116153
theorem R77597 : Reach 77597 := rs (se 3 (by rfl) ⟨14549, by rfl⟩) R29099
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R77881 : Reach 77881 := rs (se 2 (by rfl) ⟨29205, by rfl⟩) R58411
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) R58639
theorem R78299 : Reach 78299 := rs (se 1 (by rfl) ⟨58724, by rfl⟩) R117449
theorem R45665 : Reach 45665 := rs (se 2 (by rfl) ⟨17124, by rfl⟩) R34249
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R46007 : Reach 46007 := rs (se 1 (by rfl) ⟨34505, by rfl⟩) R69011
theorem R111617 : Reach 111617 := rs (se 2 (by rfl) ⟨41856, by rfl⟩) R83713
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R79001 : Reach 79001 := rs (se 2 (by rfl) ⟨29625, by rfl⟩) R59251
theorem R538001 : Reach 538001 := rs (se 2 (by rfl) ⟨201750, by rfl⟩) R403501
theorem R46601 : Reach 46601 := rs (se 2 (by rfl) ⟨17475, by rfl⟩) R34951
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R112427 : Reach 112427 := rs (se 1 (by rfl) ⟨84320, by rfl⟩) R168641
theorem R46943 : Reach 46943 := rs (se 1 (by rfl) ⟨35207, by rfl⟩) R70415
theorem R47123 : Reach 47123 := rs (se 1 (by rfl) ⟨35342, by rfl⟩) R70685
theorem R47465 : Reach 47465 := rs (se 2 (by rfl) ⟨17799, by rfl⟩) R35599
theorem R48059 : Reach 48059 := rs (se 1 (by rfl) ⟨36044, by rfl⟩) R72089
theorem R48185 : Reach 48185 := rs (se 2 (by rfl) ⟨18069, by rfl⟩) R36139
theorem R48527 : Reach 48527 := rs (se 1 (by rfl) ⟨36395, by rfl⟩) R72791
theorem R48779 : Reach 48779 := rs (se 1 (by rfl) ⟨36584, by rfl⟩) R73169
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R48851 : Reach 48851 := rs (se 1 (by rfl) ⟨36638, by rfl⟩) R73277
theorem R114695 : Reach 114695 := rs (se 1 (by rfl) ⟨86021, by rfl⟩) R172043
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) R61555
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) R30863
theorem R115181 : Reach 115181 := rs (se 3 (by rfl) ⟨21596, by rfl⟩) R43193
theorem R82529 : Reach 82529 := rs (se 2 (by rfl) ⟨30948, by rfl⟩) R61897
theorem R49787 : Reach 49787 := rs (se 1 (by rfl) ⟨37340, by rfl⟩) R74681
theorem R49913 : Reach 49913 := rs (se 2 (by rfl) ⟨18717, by rfl⟩) R37435
theorem R50183 : Reach 50183 := rs (se 1 (by rfl) ⟨37637, by rfl⟩) R75275
theorem R50255 : Reach 50255 := rs (se 1 (by rfl) ⟨37691, by rfl⟩) R75383
theorem R115991 : Reach 115991 := rs (se 1 (by rfl) ⟨86993, by rfl⟩) R173987
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) R43535
theorem R50561 : Reach 50561 := rs (se 2 (by rfl) ⟨18960, by rfl⟩) R37921
theorem R345545 : Reach 345545 := rs (se 2 (by rfl) ⟨129579, by rfl⟩) R259159
theorem R50651 : Reach 50651 := rs (se 1 (by rfl) ⟨37988, by rfl⟩) R75977
theorem R83443 : Reach 83443 := rs (se 1 (by rfl) ⟨62582, by rfl⟩) R125165
theorem R50827 : Reach 50827 := rs (se 1 (by rfl) ⟨38120, by rfl⟩) R76241
theorem R50903 : Reach 50903 := rs (se 1 (by rfl) ⟨38177, by rfl⟩) R76355
theorem R542513 : Reach 542513 := rs (se 2 (by rfl) ⟨203442, by rfl⟩) R406885
theorem R51119 : Reach 51119 := rs (se 1 (by rfl) ⟨38339, by rfl⟩) R76679
theorem R51131 : Reach 51131 := rs (se 1 (by rfl) ⟨38348, by rfl⟩) R76697
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R51371 : Reach 51371 := rs (se 1 (by rfl) ⟨38528, by rfl⟩) R77057
theorem R51911 : Reach 51911 := rs (se 1 (by rfl) ⟨38933, by rfl⟩) R77867
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R51961 : Reach 51961 := rs (se 2 (by rfl) ⟨19485, by rfl⟩) R38971
theorem R117611 : Reach 117611 := rs (se 1 (by rfl) ⟨88208, by rfl⟩) R176417
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R117733 : Reach 117733 := rs (se 4 (by rfl) ⟨11037, by rfl⟩) R22075
theorem R118007 : Reach 118007 := rs (se 1 (by rfl) ⟨88505, by rfl⟩) R177011
theorem R52609 : Reach 52609 := rs (se 2 (by rfl) ⟨19728, by rfl⟩) R39457
theorem R118259 : Reach 118259 := rs (se 1 (by rfl) ⟨88694, by rfl⟩) R177389
theorem R20007 : Reach 20007 := rs (se 1 (by rfl) ⟨15005, by rfl⟩) R30011
theorem R52775 : Reach 52775 := rs (se 1 (by rfl) ⟨39581, by rfl⟩) R79163
theorem R20047 : Reach 20047 := rs (se 1 (by rfl) ⟨15035, by rfl⟩) R30071
theorem R20063 : Reach 20063 := rs (se 1 (by rfl) ⟨15047, by rfl⟩) R30095
theorem R20091 : Reach 20091 := rs (se 1 (by rfl) ⟨15068, by rfl⟩) R30137
theorem R85643 : Reach 85643 := rs (se 1 (by rfl) ⟨64232, by rfl⟩) R128465
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R20143 : Reach 20143 := rs (se 1 (by rfl) ⟨15107, by rfl⟩) R30215
theorem R20167 : Reach 20167 := rs (se 1 (by rfl) ⟨15125, by rfl⟩) R30251
theorem R20187 : Reach 20187 := rs (se 1 (by rfl) ⟨15140, by rfl⟩) R30281
theorem R20263 : Reach 20263 := rs (se 1 (by rfl) ⟨15197, by rfl⟩) R30395
theorem R20303 : Reach 20303 := rs (se 1 (by rfl) ⟨15227, by rfl⟩) R30455
theorem R20319 : Reach 20319 := rs (se 1 (by rfl) ⟨15239, by rfl⟩) R30479
theorem R20347 : Reach 20347 := rs (se 1 (by rfl) ⟨15260, by rfl⟩) R30521
theorem R20399 : Reach 20399 := rs (se 1 (by rfl) ⟨15299, by rfl⟩) R30599
theorem R20423 : Reach 20423 := rs (se 1 (by rfl) ⟨15317, by rfl⟩) R30635
theorem R20443 : Reach 20443 := rs (se 1 (by rfl) ⟨15332, by rfl⟩) R30665
theorem R20519 : Reach 20519 := rs (se 1 (by rfl) ⟨15389, by rfl⟩) R30779
theorem R20559 : Reach 20559 := rs (se 1 (by rfl) ⟨15419, by rfl⟩) R30839
theorem R20575 : Reach 20575 := rs (se 1 (by rfl) ⟨15431, by rfl⟩) R30863
theorem R20603 : Reach 20603 := rs (se 1 (by rfl) ⟨15452, by rfl⟩) R30905
theorem R53419 : Reach 53419 := rs (se 1 (by rfl) ⟨40064, by rfl⟩) R80129
theorem R20655 : Reach 20655 := rs (se 1 (by rfl) ⟨15491, by rfl⟩) R30983
theorem R20679 : Reach 20679 := rs (se 1 (by rfl) ⟨15509, by rfl⟩) R31019
theorem R20699 : Reach 20699 := rs (se 1 (by rfl) ⟨15524, by rfl⟩) R31049
theorem R20775 : Reach 20775 := rs (se 1 (by rfl) ⟨15581, by rfl⟩) R31163
theorem R20815 : Reach 20815 := rs (se 1 (by rfl) ⟨15611, by rfl⟩) R31223
theorem R20831 : Reach 20831 := rs (se 1 (by rfl) ⟨15623, by rfl⟩) R31247
theorem R20859 : Reach 20859 := rs (se 1 (by rfl) ⟨15644, by rfl⟩) R31289
theorem R20911 : Reach 20911 := rs (se 1 (by rfl) ⟨15683, by rfl⟩) R31367
theorem R20935 : Reach 20935 := rs (se 1 (by rfl) ⟨15701, by rfl⟩) R31403
theorem R20955 : Reach 20955 := rs (se 1 (by rfl) ⟨15716, by rfl⟩) R31433
theorem R53723 : Reach 53723 := rs (se 1 (by rfl) ⟨40292, by rfl⟩) R80585
theorem R21031 : Reach 21031 := rs (se 1 (by rfl) ⟨15773, by rfl⟩) R31547
theorem R21071 : Reach 21071 := rs (se 1 (by rfl) ⟨15803, by rfl⟩) R31607
theorem R21115 : Reach 21115 := rs (se 1 (by rfl) ⟨15836, by rfl⟩) R31673
theorem R21191 : Reach 21191 := rs (se 1 (by rfl) ⟨15893, by rfl⟩) R31787
theorem R53975 : Reach 53975 := rs (se 1 (by rfl) ⟨40481, by rfl⟩) R80963
theorem R21343 : Reach 21343 := rs (se 1 (by rfl) ⟨16007, by rfl⟩) R32015
theorem R21423 : Reach 21423 := rs (se 1 (by rfl) ⟨16067, by rfl⟩) R32135
theorem R21467 : Reach 21467 := rs (se 1 (by rfl) ⟨16100, by rfl⟩) R32201
theorem R21543 : Reach 21543 := rs (se 1 (by rfl) ⟨16157, by rfl⟩) R32315
theorem R21583 : Reach 21583 := rs (se 1 (by rfl) ⟨16187, by rfl⟩) R32375
theorem R21627 : Reach 21627 := rs (se 1 (by rfl) ⟨16220, by rfl⟩) R32441
theorem R21703 : Reach 21703 := rs (se 1 (by rfl) ⟨16277, by rfl⟩) R32555
theorem R21855 : Reach 21855 := rs (se 1 (by rfl) ⟨16391, by rfl⟩) R32783
theorem R21935 : Reach 21935 := rs (se 1 (by rfl) ⟨16451, by rfl⟩) R32903
theorem R21979 : Reach 21979 := rs (se 1 (by rfl) ⟨16484, by rfl⟩) R32969
theorem R22055 : Reach 22055 := rs (se 1 (by rfl) ⟨16541, by rfl⟩) R33083
theorem R22095 : Reach 22095 := rs (se 1 (by rfl) ⟨16571, by rfl⟩) R33143
theorem R22139 : Reach 22139 := rs (se 1 (by rfl) ⟨16604, by rfl⟩) R33209
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R22215 : Reach 22215 := rs (se 1 (by rfl) ⟨16661, by rfl⟩) R33323
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R22367 : Reach 22367 := rs (se 1 (by rfl) ⟨16775, by rfl⟩) R33551
theorem R55201 : Reach 55201 := rs (se 2 (by rfl) ⟨20700, by rfl⟩) R41401
theorem R22447 : Reach 22447 := rs (se 1 (by rfl) ⟨16835, by rfl⟩) R33671
theorem R22491 : Reach 22491 := rs (se 1 (by rfl) ⟨16868, by rfl⟩) R33737
theorem R22567 : Reach 22567 := rs (se 1 (by rfl) ⟨16925, by rfl⟩) R33851
theorem R22607 : Reach 22607 := rs (se 1 (by rfl) ⟨16955, by rfl⟩) R33911
theorem R22651 : Reach 22651 := rs (se 1 (by rfl) ⟨16988, by rfl⟩) R33977
theorem R22727 : Reach 22727 := rs (se 1 (by rfl) ⟨17045, by rfl⟩) R34091
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R22879 : Reach 22879 := rs (se 1 (by rfl) ⟨17159, by rfl⟩) R34319
theorem R22959 : Reach 22959 := rs (se 1 (by rfl) ⟨17219, by rfl⟩) R34439
theorem R23003 : Reach 23003 := rs (se 1 (by rfl) ⟨17252, by rfl⟩) R34505
theorem R23079 : Reach 23079 := rs (se 1 (by rfl) ⟨17309, by rfl⟩) R34619
theorem R23119 : Reach 23119 := rs (se 1 (by rfl) ⟨17339, by rfl⟩) R34679
theorem R23163 : Reach 23163 := rs (se 1 (by rfl) ⟨17372, by rfl⟩) R34745
theorem R23239 : Reach 23239 := rs (se 1 (by rfl) ⟨17429, by rfl⟩) R34859
theorem R23391 : Reach 23391 := rs (se 1 (by rfl) ⟨17543, by rfl⟩) R35087
theorem R154543 : Reach 154543 := rs (se 1 (by rfl) ⟨115907, by rfl⟩) R231815
theorem R23471 : Reach 23471 := rs (se 1 (by rfl) ⟨17603, by rfl⟩) R35207
theorem R56477 : Reach 56477 := rs (se 3 (by rfl) ⟨10589, by rfl⟩) R21179
theorem R24187 : Reach 24187 := rs (se 1 (by rfl) ⟨18140, by rfl⟩) R36281
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) R23047
theorem R24655 : Reach 24655 := rs (se 1 (by rfl) ⟨18491, by rfl⟩) R36983
theorem R57743 : Reach 57743 := rs (se 1 (by rfl) ⟨43307, by rfl⟩) R86615
theorem R25015 : Reach 25015 := rs (se 1 (by rfl) ⟨18761, by rfl⟩) R37523
theorem R25051 : Reach 25051 := rs (se 1 (by rfl) ⟨18788, by rfl⟩) R37577
theorem R58067 : Reach 58067 := rs (se 1 (by rfl) ⟨43550, by rfl⟩) R87101
theorem R25519 : Reach 25519 := rs (se 1 (by rfl) ⟨19139, by rfl⟩) R38279
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R25951 : Reach 25951 := rs (se 1 (by rfl) ⟨19463, by rfl⟩) R38927
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R157373 : Reach 157373 := rs (se 3 (by rfl) ⟨29507, by rfl⟩) R59015
theorem R59069 : Reach 59069 := rs (se 3 (by rfl) ⟨11075, by rfl⟩) R22151
theorem R26311 : Reach 26311 := rs (se 1 (by rfl) ⟨19733, by rfl⟩) R39467
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) R22331
theorem R27145 : Reach 27145 := rs (se 2 (by rfl) ⟨10179, by rfl⟩) R20359
theorem R27497 : Reach 27497 := rs (se 2 (by rfl) ⟨10311, by rfl⟩) R20623
theorem R28409 : Reach 28409 := rs (se 2 (by rfl) ⟨10653, by rfl⟩) R21307
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) R45883
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R29035 : Reach 29035 := rs (se 1 (by rfl) ⟨21776, by rfl⟩) R43553
theorem R193049 : Reach 193049 := rs (se 2 (by rfl) ⟨72393, by rfl⟩) R144787
theorem R29263 : Reach 29263 := rs (se 1 (by rfl) ⟨21947, by rfl⟩) R43895
theorem R94931 : Reach 94931 := rs (se 1 (by rfl) ⟨71198, by rfl⟩) R142397
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R30047 : Reach 30047 := rs (se 1 (by rfl) ⟨22535, by rfl⟩) R45071
theorem R30059 : Reach 30059 := rs (se 1 (by rfl) ⟨22544, by rfl⟩) R45089
theorem R62963 : Reach 62963 := rs (se 1 (by rfl) ⟨47222, by rfl⟩) R94445
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R30287 : Reach 30287 := rs (se 1 (by rfl) ⟨22715, by rfl⟩) R45431
theorem R30407 : Reach 30407 := rs (se 1 (by rfl) ⟨22805, by rfl⟩) R45611
theorem R30569 : Reach 30569 := rs (se 2 (by rfl) ⟨11463, by rfl⟩) R22927
theorem R30647 : Reach 30647 := rs (se 1 (by rfl) ⟨22985, by rfl⟩) R45971
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R30683 : Reach 30683 := rs (se 1 (by rfl) ⟨23012, by rfl⟩) R46025
theorem R31151 : Reach 31151 := rs (se 1 (by rfl) ⟨23363, by rfl⟩) R46727
theorem R31241 : Reach 31241 := rs (se 2 (by rfl) ⟨11715, by rfl⟩) R23431
theorem R31271 : Reach 31271 := rs (se 1 (by rfl) ⟨23453, by rfl⟩) R46907
theorem R31355 : Reach 31355 := rs (se 1 (by rfl) ⟨23516, by rfl⟩) R47033
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R31481 : Reach 31481 := rs (se 2 (by rfl) ⟨11805, by rfl⟩) R23611
theorem R31583 : Reach 31583 := rs (se 1 (by rfl) ⟨23687, by rfl⟩) R47375
theorem R31595 : Reach 31595 := rs (se 1 (by rfl) ⟨23696, by rfl⟩) R47393
theorem R31631 : Reach 31631 := rs (se 1 (by rfl) ⟨23723, by rfl⟩) R47447
theorem R31751 : Reach 31751 := rs (se 1 (by rfl) ⟨23813, by rfl⟩) R47627
theorem R31823 : Reach 31823 := rs (se 1 (by rfl) ⟨23867, by rfl⟩) R47735
theorem R31943 : Reach 31943 := rs (se 1 (by rfl) ⟨23957, by rfl⟩) R47915
theorem R31991 : Reach 31991 := rs (se 1 (by rfl) ⟨23993, by rfl⟩) R47987
theorem R32105 : Reach 32105 := rs (se 2 (by rfl) ⟨12039, by rfl⟩) R24079
theorem R32183 : Reach 32183 := rs (se 1 (by rfl) ⟨24137, by rfl⟩) R48275
theorem R32219 : Reach 32219 := rs (se 1 (by rfl) ⟨24164, by rfl⟩) R48329
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R32585 : Reach 32585 := rs (se 2 (by rfl) ⟨12219, by rfl⟩) R24439
theorem R32687 : Reach 32687 := rs (se 1 (by rfl) ⟨24515, by rfl⟩) R49031
theorem R262075 : Reach 262075 := rs (se 1 (by rfl) ⟨196556, by rfl⟩) R393113
theorem R32699 : Reach 32699 := rs (se 1 (by rfl) ⟨24524, by rfl⟩) R49049
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R32873 : Reach 32873 := rs (se 2 (by rfl) ⟨12327, by rfl⟩) R24655
theorem R65747 : Reach 65747 := rs (se 1 (by rfl) ⟨49310, by rfl⟩) R98621
theorem R33191 : Reach 33191 := rs (se 1 (by rfl) ⟨24893, by rfl⟩) R49787
theorem R33275 : Reach 33275 := rs (se 1 (by rfl) ⟨24956, by rfl⟩) R49913
theorem R33353 : Reach 33353 := rs (se 2 (by rfl) ⟨12507, by rfl⟩) R25015
theorem R33401 : Reach 33401 := rs (se 2 (by rfl) ⟨12525, by rfl⟩) R25051
theorem R33455 : Reach 33455 := rs (se 1 (by rfl) ⟨25091, by rfl⟩) R50183
theorem R33503 : Reach 33503 := rs (se 1 (by rfl) ⟨25127, by rfl⟩) R50255
theorem R66271 : Reach 66271 := rs (se 1 (by rfl) ⟨49703, by rfl⟩) R99407
theorem R33707 : Reach 33707 := rs (se 1 (by rfl) ⟨25280, by rfl⟩) R50561
theorem R230363 : Reach 230363 := rs (se 1 (by rfl) ⟨172772, by rfl⟩) R345545
theorem R33767 : Reach 33767 := rs (se 1 (by rfl) ⟨25325, by rfl⟩) R50651
theorem R33935 : Reach 33935 := rs (se 1 (by rfl) ⟨25451, by rfl⟩) R50903
theorem R361675 : Reach 361675 := rs (se 1 (by rfl) ⟨271256, by rfl⟩) R542513
theorem R34025 : Reach 34025 := rs (se 2 (by rfl) ⟨12759, by rfl⟩) R25519
theorem R34079 : Reach 34079 := rs (se 1 (by rfl) ⟨25559, by rfl⟩) R51119
theorem R197923 : Reach 197923 := rs (se 1 (by rfl) ⟨148442, by rfl⟩) R296885
theorem R34087 : Reach 34087 := rs (se 1 (by rfl) ⟨25565, by rfl⟩) R51131
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R34247 : Reach 34247 := rs (se 1 (by rfl) ⟨25685, by rfl⟩) R51371
theorem R34601 : Reach 34601 := rs (se 2 (by rfl) ⟨12975, by rfl⟩) R25951
theorem R34607 : Reach 34607 := rs (se 1 (by rfl) ⟨25955, by rfl⟩) R51911
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R67769 : Reach 67769 := rs (se 2 (by rfl) ⟨25413, by rfl⟩) R50827
theorem R35081 : Reach 35081 := rs (se 2 (by rfl) ⟨13155, by rfl⟩) R26311
theorem R35183 : Reach 35183 := rs (se 1 (by rfl) ⟨26387, by rfl⟩) R52775
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R35815 : Reach 35815 := rs (se 1 (by rfl) ⟨26861, by rfl⟩) R53723
theorem R265355 : Reach 265355 := rs (se 1 (by rfl) ⟨199016, by rfl⟩) R398033
theorem R35983 : Reach 35983 := rs (se 1 (by rfl) ⟨26987, by rfl⟩) R53975
theorem R36193 : Reach 36193 := rs (se 2 (by rfl) ⟨13572, by rfl⟩) R27145
theorem R101897 : Reach 101897 := rs (se 2 (by rfl) ⟨38211, by rfl⟩) R76423
theorem R69281 : Reach 69281 := rs (se 2 (by rfl) ⟨25980, by rfl⟩) R51961
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R430109 : Reach 430109 := rs (se 3 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R70145 : Reach 70145 := rs (se 2 (by rfl) ⟨26304, by rfl⟩) R52609
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R266813 : Reach 266813 := rs (se 3 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R37651 : Reach 37651 := rs (se 1 (by rfl) ⟨28238, by rfl⟩) R56477
theorem R70631 : Reach 70631 := rs (se 1 (by rfl) ⟨52973, by rfl⟩) R105947
theorem R70955 : Reach 70955 := rs (se 1 (by rfl) ⟨53216, by rfl⟩) R106433
theorem R103841 : Reach 103841 := rs (se 2 (by rfl) ⟨38940, by rfl⟩) R77881
theorem R71225 : Reach 71225 := rs (se 2 (by rfl) ⟨26709, by rfl⟩) R53419
theorem R38495 : Reach 38495 := rs (se 1 (by rfl) ⟨28871, by rfl⟩) R57743
theorem R38711 : Reach 38711 := rs (se 1 (by rfl) ⟨29033, by rfl⟩) R58067
theorem R38713 : Reach 38713 := rs (se 2 (by rfl) ⟨14517, by rfl⟩) R29035
theorem R39017 : Reach 39017 := rs (se 2 (by rfl) ⟨14631, by rfl⟩) R29263
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) R38059
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R104915 : Reach 104915 := rs (se 1 (by rfl) ⟨78686, by rfl⟩) R157373
theorem R39379 : Reach 39379 := rs (se 1 (by rfl) ⟨29534, by rfl⟩) R59069
theorem R39487 : Reach 39487 := rs (se 1 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R72467 : Reach 72467 := rs (se 1 (by rfl) ⟨54350, by rfl⟩) R108701
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) R27497
theorem R73331 : Reach 73331 := rs (se 1 (by rfl) ⟨54998, by rfl⟩) R109997
theorem R73601 : Reach 73601 := rs (se 2 (by rfl) ⟨27600, by rfl⟩) R55201
theorem R74411 : Reach 74411 := rs (se 1 (by rfl) ⟨55808, by rfl⟩) R111617
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R41975 : Reach 41975 := rs (se 1 (by rfl) ⟨31481, by rfl⟩) R62963
theorem R74951 : Reach 74951 := rs (se 1 (by rfl) ⟨56213, by rfl⟩) R112427
theorem R206057 : Reach 206057 := rs (se 2 (by rfl) ⟨77271, by rfl⟩) R154543
theorem R173501 : Reach 173501 := rs (se 3 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) R28409
theorem R76463 : Reach 76463 := rs (se 1 (by rfl) ⟨57347, by rfl⟩) R114695
theorem R76787 : Reach 76787 := rs (se 1 (by rfl) ⟨57590, by rfl⟩) R115181
theorem R371789 : Reach 371789 := rs (se 3 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R109835 : Reach 109835 := rs (se 1 (by rfl) ⟨82376, by rfl⟩) R164753
theorem R109943 : Reach 109943 := rs (se 1 (by rfl) ⟨82457, by rfl⟩) R164915
theorem R77327 : Reach 77327 := rs (se 1 (by rfl) ⟨57995, by rfl⟩) R115991
theorem R77395 : Reach 77395 := rs (se 1 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R44731 : Reach 44731 := rs (se 1 (by rfl) ⟨33548, by rfl⟩) R67097
theorem R45161 : Reach 45161 := rs (se 2 (by rfl) ⟨16935, by rfl⟩) R33871
theorem R242027 : Reach 242027 := rs (se 1 (by rfl) ⟨181520, by rfl⟩) R363041
theorem R78407 : Reach 78407 := rs (se 1 (by rfl) ⟨58805, by rfl⟩) R117611
theorem R45647 : Reach 45647 := rs (se 1 (by rfl) ⟨34235, by rfl⟩) R68471
theorem R111257 : Reach 111257 := rs (se 2 (by rfl) ⟨41721, by rfl⟩) R83443
theorem R45791 : Reach 45791 := rs (se 1 (by rfl) ⟨34343, by rfl⟩) R68687
theorem R78671 : Reach 78671 := rs (se 1 (by rfl) ⟨59003, by rfl⟩) R118007
theorem R111455 : Reach 111455 := rs (se 1 (by rfl) ⟨83591, by rfl⟩) R167183
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) R41801
theorem R46043 : Reach 46043 := rs (se 1 (by rfl) ⟨34532, by rfl⟩) R69065
theorem R78839 : Reach 78839 := rs (se 1 (by rfl) ⟨59129, by rfl⟩) R118259
theorem R46223 : Reach 46223 := rs (se 1 (by rfl) ⟨34667, by rfl⟩) R69335
theorem R46313 : Reach 46313 := rs (se 2 (by rfl) ⟨17367, by rfl⟩) R34735
theorem R46367 : Reach 46367 := rs (se 1 (by rfl) ⟨34775, by rfl⟩) R69551
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R46459 : Reach 46459 := rs (se 1 (by rfl) ⟨34844, by rfl⟩) R69689
theorem R243485 : Reach 243485 := rs (se 3 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R46889 : Reach 46889 := rs (se 2 (by rfl) ⟨17583, by rfl⟩) R35167
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R80311 : Reach 80311 := rs (se 1 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R735925 : Reach 735925 := rs (se 5 (by rfl) ⟨34496, by rfl⟩) R68993
theorem R47951 : Reach 47951 := rs (se 1 (by rfl) ⟨35963, by rfl⟩) R71927
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R48167 : Reach 48167 := rs (se 1 (by rfl) ⟨36125, by rfl⟩) R72251
theorem R48251 : Reach 48251 := rs (se 1 (by rfl) ⟨36188, by rfl⟩) R72377
theorem R48347 : Reach 48347 := rs (se 1 (by rfl) ⟨36260, by rfl⟩) R72521
theorem R113885 : Reach 113885 := rs (se 3 (by rfl) ⟨21353, by rfl⟩) R42707
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R48545 : Reach 48545 := rs (se 2 (by rfl) ⟨18204, by rfl⟩) R36409
theorem R48599 : Reach 48599 := rs (se 1 (by rfl) ⟨36449, by rfl⟩) R72899
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) R61177
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R49103 : Reach 49103 := rs (se 1 (by rfl) ⟨36827, by rfl⟩) R73655
theorem R49481 : Reach 49481 := rs (se 2 (by rfl) ⟨18555, by rfl⟩) R37111
theorem R49499 : Reach 49499 := rs (se 1 (by rfl) ⟨37124, by rfl⟩) R74249
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R50075 : Reach 50075 := rs (se 1 (by rfl) ⟨37556, by rfl⟩) R75113
theorem R50273 : Reach 50273 := rs (se 2 (by rfl) ⟨18852, by rfl⟩) R37705
theorem R50471 : Reach 50471 := rs (se 1 (by rfl) ⟨37853, by rfl⟩) R75707
theorem R50849 : Reach 50849 := rs (se 2 (by rfl) ⟨19068, by rfl⟩) R38137
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R51151 : Reach 51151 := rs (se 1 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R51209 : Reach 51209 := rs (se 2 (by rfl) ⟨19203, by rfl⟩) R38407
theorem R51623 : Reach 51623 := rs (se 1 (by rfl) ⟨38717, by rfl⟩) R77435
theorem R51731 : Reach 51731 := rs (se 1 (by rfl) ⟨38798, by rfl⟩) R77597
theorem R51785 : Reach 51785 := rs (se 2 (by rfl) ⟨19419, by rfl⟩) R38839
theorem R52123 : Reach 52123 := rs (se 1 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R52199 : Reach 52199 := rs (se 1 (by rfl) ⟨39149, by rfl⟩) R78299
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R52577 : Reach 52577 := rs (se 2 (by rfl) ⟨19716, by rfl⟩) R39433
theorem R52667 : Reach 52667 := rs (se 1 (by rfl) ⟨39500, by rfl⟩) R79001
theorem R52793 : Reach 52793 := rs (se 2 (by rfl) ⟨19797, by rfl⟩) R39595
theorem R20031 : Reach 20031 := rs (se 1 (by rfl) ⟨15023, by rfl⟩) R30047
theorem R20039 : Reach 20039 := rs (se 1 (by rfl) ⟨15029, by rfl⟩) R30059
theorem R20191 : Reach 20191 := rs (se 1 (by rfl) ⟨15143, by rfl⟩) R30287
theorem R20271 : Reach 20271 := rs (se 1 (by rfl) ⟨15203, by rfl⟩) R30407
theorem R20379 : Reach 20379 := rs (se 1 (by rfl) ⟨15284, by rfl⟩) R30569
theorem R20431 : Reach 20431 := rs (se 1 (by rfl) ⟨15323, by rfl⟩) R30647
theorem R20455 : Reach 20455 := rs (se 1 (by rfl) ⟨15341, by rfl⟩) R30683
theorem R53257 : Reach 53257 := rs (se 2 (by rfl) ⟨19971, by rfl⟩) R39943
theorem R20767 : Reach 20767 := rs (se 1 (by rfl) ⟨15575, by rfl⟩) R31151
theorem R20827 : Reach 20827 := rs (se 1 (by rfl) ⟨15620, by rfl⟩) R31241
theorem R20847 : Reach 20847 := rs (se 1 (by rfl) ⟨15635, by rfl⟩) R31271
theorem R20903 : Reach 20903 := rs (se 1 (by rfl) ⟨15677, by rfl⟩) R31355
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R20987 : Reach 20987 := rs (se 1 (by rfl) ⟨15740, by rfl⟩) R31481
theorem R21055 : Reach 21055 := rs (se 1 (by rfl) ⟨15791, by rfl⟩) R31583
theorem R21063 : Reach 21063 := rs (se 1 (by rfl) ⟨15797, by rfl⟩) R31595
theorem R21087 : Reach 21087 := rs (se 1 (by rfl) ⟨15815, by rfl⟩) R31631
theorem R21167 : Reach 21167 := rs (se 1 (by rfl) ⟨15875, by rfl⟩) R31751
theorem R21215 : Reach 21215 := rs (se 1 (by rfl) ⟨15911, by rfl⟩) R31823
theorem R21295 : Reach 21295 := rs (se 1 (by rfl) ⟨15971, by rfl⟩) R31943
theorem R21327 : Reach 21327 := rs (se 1 (by rfl) ⟨15995, by rfl⟩) R31991
theorem R21403 : Reach 21403 := rs (se 1 (by rfl) ⟨16052, by rfl⟩) R32105
theorem R119717 : Reach 119717 := rs (se 4 (by rfl) ⟨11223, by rfl⟩) R22447
theorem R21455 : Reach 21455 := rs (se 1 (by rfl) ⟨16091, by rfl⟩) R32183
theorem R21479 : Reach 21479 := rs (se 1 (by rfl) ⟨16109, by rfl⟩) R32219
theorem R21723 : Reach 21723 := rs (se 1 (by rfl) ⟨16292, by rfl⟩) R32585
theorem R349433 : Reach 349433 := rs (se 2 (by rfl) ⟨131037, by rfl⟩) R262075
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R21791 : Reach 21791 := rs (se 1 (by rfl) ⟨16343, by rfl⟩) R32687
theorem R21799 : Reach 21799 := rs (se 1 (by rfl) ⟨16349, by rfl⟩) R32699
theorem R21851 : Reach 21851 := rs (se 1 (by rfl) ⟨16388, by rfl⟩) R32777
theorem R21871 : Reach 21871 := rs (se 1 (by rfl) ⟨16403, by rfl⟩) R32807
theorem R21883 : Reach 21883 := rs (se 1 (by rfl) ⟨16412, by rfl⟩) R32825
theorem R87419 : Reach 87419 := rs (se 1 (by rfl) ⟨65564, by rfl⟩) R131129
theorem R54665 : Reach 54665 := rs (se 2 (by rfl) ⟨20499, by rfl⟩) R40999
theorem R21927 : Reach 21927 := rs (se 1 (by rfl) ⟨16445, by rfl⟩) R32891
theorem R54715 : Reach 54715 := rs (se 1 (by rfl) ⟨41036, by rfl⟩) R82073
theorem R21959 : Reach 21959 := rs (se 1 (by rfl) ⟨16469, by rfl⟩) R32939
theorem R22011 : Reach 22011 := rs (se 1 (by rfl) ⟨16508, by rfl⟩) R33017
theorem R22079 : Reach 22079 := rs (se 1 (by rfl) ⟨16559, by rfl⟩) R33119
theorem R22087 : Reach 22087 := rs (se 1 (by rfl) ⟨16565, by rfl⟩) R33131
theorem R22111 : Reach 22111 := rs (se 1 (by rfl) ⟨16583, by rfl⟩) R33167
theorem R22191 : Reach 22191 := rs (se 1 (by rfl) ⟨16643, by rfl⟩) R33287
theorem R22239 : Reach 22239 := rs (se 1 (by rfl) ⟨16679, by rfl⟩) R33359
theorem R55019 : Reach 55019 := rs (se 1 (by rfl) ⟨41264, by rfl⟩) R82529
theorem R22319 : Reach 22319 := rs (se 1 (by rfl) ⟨16739, by rfl⟩) R33479
theorem R22351 : Reach 22351 := rs (se 1 (by rfl) ⟨16763, by rfl⟩) R33527
theorem R22427 : Reach 22427 := rs (se 1 (by rfl) ⟨16820, by rfl⟩) R33641
theorem R22479 : Reach 22479 := rs (se 1 (by rfl) ⟨16859, by rfl⟩) R33719
theorem R22503 : Reach 22503 := rs (se 1 (by rfl) ⟨16877, by rfl⟩) R33755
theorem R88199 : Reach 88199 := rs (se 1 (by rfl) ⟨66149, by rfl⟩) R132299
theorem R22747 : Reach 22747 := rs (se 1 (by rfl) ⟨17060, by rfl⟩) R34121
theorem R22815 : Reach 22815 := rs (se 1 (by rfl) ⟨17111, by rfl⟩) R34223
theorem R22823 : Reach 22823 := rs (se 1 (by rfl) ⟨17117, by rfl⟩) R34235
theorem R22875 : Reach 22875 := rs (se 1 (by rfl) ⟨17156, by rfl⟩) R34313
theorem R22895 : Reach 22895 := rs (se 1 (by rfl) ⟨17171, by rfl⟩) R34343
theorem R22907 : Reach 22907 := rs (se 1 (by rfl) ⟨17180, by rfl⟩) R34361
theorem R22951 : Reach 22951 := rs (se 1 (by rfl) ⟨17213, by rfl⟩) R34427
theorem R22983 : Reach 22983 := rs (se 1 (by rfl) ⟨17237, by rfl⟩) R34475
theorem R23035 : Reach 23035 := rs (se 1 (by rfl) ⟨17276, by rfl⟩) R34553
theorem R219671 : Reach 219671 := rs (se 1 (by rfl) ⟨164753, by rfl⟩) R329507
theorem R23103 : Reach 23103 := rs (se 1 (by rfl) ⟨17327, by rfl⟩) R34655
theorem R23111 : Reach 23111 := rs (se 1 (by rfl) ⟨17333, by rfl⟩) R34667
theorem R23135 : Reach 23135 := rs (se 1 (by rfl) ⟨17351, by rfl⟩) R34703
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) R32891
theorem R23215 : Reach 23215 := rs (se 1 (by rfl) ⟨17411, by rfl⟩) R34823
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R23263 : Reach 23263 := rs (se 1 (by rfl) ⟨17447, by rfl⟩) R34895
theorem R23343 : Reach 23343 := rs (se 1 (by rfl) ⟨17507, by rfl⟩) R35015
theorem R23375 : Reach 23375 := rs (se 1 (by rfl) ⟨17531, by rfl⟩) R35063
theorem R23451 : Reach 23451 := rs (se 1 (by rfl) ⟨17588, by rfl⟩) R35177
theorem R23503 : Reach 23503 := rs (se 1 (by rfl) ⟨17627, by rfl⟩) R35255
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R23899 : Reach 23899 := rs (se 1 (by rfl) ⟨17924, by rfl⟩) R35849
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R24007 : Reach 24007 := rs (se 1 (by rfl) ⟨18005, by rfl⟩) R36011
theorem R220819 : Reach 220819 := rs (se 1 (by rfl) ⟨165614, by rfl⟩) R331229
theorem R57095 : Reach 57095 := rs (se 1 (by rfl) ⟨42821, by rfl⟩) R85643
theorem R24367 : Reach 24367 := rs (se 1 (by rfl) ⟨18275, by rfl⟩) R36551
theorem R57145 : Reach 57145 := rs (se 2 (by rfl) ⟨21429, by rfl⟩) R42859
theorem R24475 : Reach 24475 := rs (se 1 (by rfl) ⟨18356, by rfl⟩) R36713
theorem R24527 : Reach 24527 := rs (se 1 (by rfl) ⟨18395, by rfl⟩) R36791
theorem R57449 : Reach 57449 := rs (se 2 (by rfl) ⟨21543, by rfl⟩) R43087
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R24871 : Reach 24871 := rs (se 1 (by rfl) ⟨18653, by rfl⟩) R37307
theorem R24943 : Reach 24943 := rs (se 1 (by rfl) ⟨18707, by rfl⟩) R37415
theorem R25159 : Reach 25159 := rs (se 1 (by rfl) ⟨18869, by rfl⟩) R37739
theorem R25195 : Reach 25195 := rs (se 1 (by rfl) ⟨18896, by rfl⟩) R37793
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) R34121
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R156977 : Reach 156977 := rs (se 2 (by rfl) ⟨58866, by rfl⟩) R117733
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R26023 : Reach 26023 := rs (se 1 (by rfl) ⟨19517, by rfl⟩) R39035
theorem R26183 : Reach 26183 := rs (se 1 (by rfl) ⟨19637, by rfl⟩) R39275
theorem R26335 : Reach 26335 := rs (se 1 (by rfl) ⟨19751, by rfl⟩) R39503
theorem R26347 : Reach 26347 := rs (se 1 (by rfl) ⟨19760, by rfl⟩) R39521
theorem R91991 : Reach 91991 := rs (se 1 (by rfl) ⟨68993, by rfl⟩) R137987
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R157949 : Reach 157949 := rs (se 3 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R27199 : Reach 27199 := rs (se 1 (by rfl) ⟨20399, by rfl⟩) R40799
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R60887 : Reach 60887 := rs (se 1 (by rfl) ⟨45665, by rfl⟩) R91331
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R421955 : Reach 421955 := rs (se 1 (by rfl) ⟨316466, by rfl⟩) R632933
theorem R28937 : Reach 28937 := rs (se 2 (by rfl) ⟨10851, by rfl⟩) R21703
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R30089 : Reach 30089 := rs (se 2 (by rfl) ⟨11283, by rfl⟩) R22567
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R128699 : Reach 128699 := rs (se 1 (by rfl) ⟨96524, by rfl⟩) R193049
theorem R30443 : Reach 30443 := rs (se 1 (by rfl) ⟨22832, by rfl⟩) R45665
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R63287 : Reach 63287 := rs (se 1 (by rfl) ⟨47465, by rfl⟩) R94931
theorem R30671 : Reach 30671 := rs (se 1 (by rfl) ⟨23003, by rfl⟩) R46007
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R358667 : Reach 358667 := rs (se 1 (by rfl) ⟨269000, by rfl⟩) R538001
theorem R31067 : Reach 31067 := rs (se 1 (by rfl) ⟨23300, by rfl⟩) R46601
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R31295 : Reach 31295 := rs (se 1 (by rfl) ⟨23471, by rfl⟩) R46943
theorem R31415 : Reach 31415 := rs (se 1 (by rfl) ⟨23561, by rfl⟩) R47123
theorem R31643 : Reach 31643 := rs (se 1 (by rfl) ⟨23732, by rfl⟩) R47465
theorem R32039 : Reach 32039 := rs (se 1 (by rfl) ⟨24029, by rfl⟩) R48059
theorem R32123 : Reach 32123 := rs (se 1 (by rfl) ⟨24092, by rfl⟩) R48185
theorem R32249 : Reach 32249 := rs (se 2 (by rfl) ⟨12093, by rfl⟩) R24187
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R32351 : Reach 32351 := rs (se 1 (by rfl) ⟨24263, by rfl⟩) R48527
theorem R32519 : Reach 32519 := rs (se 1 (by rfl) ⟨24389, by rfl⟩) R48779
theorem R32567 : Reach 32567 := rs (se 1 (by rfl) ⟨24425, by rfl⟩) R48851
theorem R32987 : Reach 32987 := rs (se 1 (by rfl) ⟨24740, by rfl⟩) R49481
theorem R32999 : Reach 32999 := rs (se 1 (by rfl) ⟨24749, by rfl⟩) R49499
theorem R33161 : Reach 33161 := rs (se 2 (by rfl) ⟨12435, by rfl⟩) R24871
theorem R33257 : Reach 33257 := rs (se 2 (by rfl) ⟨12471, by rfl⟩) R24943
theorem R33383 : Reach 33383 := rs (se 1 (by rfl) ⟨25037, by rfl⟩) R50075
theorem R33515 : Reach 33515 := rs (se 1 (by rfl) ⟨25136, by rfl⟩) R50273
theorem R33545 : Reach 33545 := rs (se 2 (by rfl) ⟨12579, by rfl⟩) R25159
theorem R33593 : Reach 33593 := rs (se 2 (by rfl) ⟨12597, by rfl⟩) R25195
theorem R33647 : Reach 33647 := rs (se 1 (by rfl) ⟨25235, by rfl⟩) R50471
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R33899 : Reach 33899 := rs (se 1 (by rfl) ⟨25424, by rfl⟩) R50849
theorem R230525 : Reach 230525 := rs (se 3 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R34139 : Reach 34139 := rs (se 1 (by rfl) ⟨25604, by rfl⟩) R51209
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R34415 : Reach 34415 := rs (se 1 (by rfl) ⟨25811, by rfl⟩) R51623
theorem R34487 : Reach 34487 := rs (se 1 (by rfl) ⟨25865, by rfl⟩) R51731
theorem R263897 : Reach 263897 := rs (se 2 (by rfl) ⟨98961, by rfl⟩) R197923
theorem R34523 : Reach 34523 := rs (se 1 (by rfl) ⟨25892, by rfl⟩) R51785
theorem R34697 : Reach 34697 := rs (se 2 (by rfl) ⟨13011, by rfl⟩) R26023
theorem R34799 : Reach 34799 := rs (se 1 (by rfl) ⟨26099, by rfl⟩) R52199
theorem R35051 : Reach 35051 := rs (se 1 (by rfl) ⟨26288, by rfl⟩) R52577
theorem R35111 : Reach 35111 := rs (se 1 (by rfl) ⟨26333, by rfl⟩) R52667
theorem R35113 : Reach 35113 := rs (se 2 (by rfl) ⟨13167, by rfl⟩) R26335
theorem R35129 : Reach 35129 := rs (se 2 (by rfl) ⟨13173, by rfl⟩) R26347
theorem R67931 : Reach 67931 := rs (se 1 (by rfl) ⟨50948, by rfl⟩) R101897
theorem R35195 : Reach 35195 := rs (se 1 (by rfl) ⟨26396, by rfl⟩) R52793
theorem R68201 : Reach 68201 := rs (se 2 (by rfl) ⟨25575, by rfl⟩) R51151
theorem R133771 : Reach 133771 := rs (se 1 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R232955 : Reach 232955 := rs (se 1 (by rfl) ⟨174716, by rfl⟩) R349433
theorem R36443 : Reach 36443 := rs (se 1 (by rfl) ⟨27332, by rfl⟩) R54665
theorem R69227 : Reach 69227 := rs (se 1 (by rfl) ⟨51920, by rfl⟩) R103841
theorem R36679 : Reach 36679 := rs (se 1 (by rfl) ⟨27509, by rfl⟩) R55019
theorem R69497 : Reach 69497 := rs (se 2 (by rfl) ⟨26061, by rfl⟩) R52123
theorem R69821 : Reach 69821 := rs (se 3 (by rfl) ⟨13091, by rfl⟩) R26183
theorem R69943 : Reach 69943 := rs (se 1 (by rfl) ⟨52457, by rfl⟩) R104915
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R37327 : Reach 37327 := rs (se 1 (by rfl) ⟨27995, by rfl⟩) R55991
theorem R103193 : Reach 103193 := rs (se 2 (by rfl) ⟨38697, by rfl⟩) R77395
theorem R38063 : Reach 38063 := rs (se 1 (by rfl) ⟨28547, by rfl⟩) R57095
theorem R71009 : Reach 71009 := rs (se 2 (by rfl) ⟨26628, by rfl⟩) R53257
theorem R38299 : Reach 38299 := rs (se 1 (by rfl) ⟨28724, by rfl⟩) R57449
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R39055 : Reach 39055 := rs (se 1 (by rfl) ⟨29291, by rfl⟩) R58583
theorem R137371 : Reach 137371 := rs (se 1 (by rfl) ⟨103028, by rfl⟩) R206057
theorem R104651 : Reach 104651 := rs (se 1 (by rfl) ⟨78488, by rfl⟩) R156977
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R105299 : Reach 105299 := rs (se 1 (by rfl) ⟨78974, by rfl⟩) R157949
theorem R72953 : Reach 72953 := rs (se 2 (by rfl) ⟨27357, by rfl⟩) R54715
theorem R73223 : Reach 73223 := rs (se 1 (by rfl) ⟨54917, by rfl⟩) R109835
theorem R73295 : Reach 73295 := rs (se 1 (by rfl) ⟨54971, by rfl⟩) R109943
theorem R40591 : Reach 40591 := rs (se 1 (by rfl) ⟨30443, by rfl⟩) R60887
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R74171 : Reach 74171 := rs (se 1 (by rfl) ⟨55628, by rfl⟩) R111257
theorem R74303 : Reach 74303 := rs (se 1 (by rfl) ⟨55727, by rfl⟩) R111455
theorem R107081 : Reach 107081 := rs (se 2 (by rfl) ⟨40155, by rfl⟩) R80311
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R238565 : Reach 238565 := rs (se 4 (by rfl) ⟨22365, by rfl⟩) R44731
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R42191 : Reach 42191 := rs (se 1 (by rfl) ⟨31643, by rfl⟩) R63287
theorem R239111 : Reach 239111 := rs (se 1 (by rfl) ⟨179333, by rfl⟩) R358667
theorem R75923 : Reach 75923 := rs (se 1 (by rfl) ⟨56942, by rfl⟩) R113885
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R76193 : Reach 76193 := rs (se 2 (by rfl) ⟨28572, by rfl⟩) R57145
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R43831 : Reach 43831 := rs (se 1 (by rfl) ⟨32873, by rfl⟩) R65747
theorem R77165 : Reach 77165 := rs (se 3 (by rfl) ⟨14468, by rfl⟩) R28937
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R45179 : Reach 45179 := rs (se 1 (by rfl) ⟨33884, by rfl⟩) R67769
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R45449 : Reach 45449 := rs (se 2 (by rfl) ⟨17043, by rfl⟩) R34087
theorem R176903 : Reach 176903 := rs (se 1 (by rfl) ⟨132677, by rfl⟩) R265355
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R46187 : Reach 46187 := rs (se 1 (by rfl) ⟨34640, by rfl⟩) R69281
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) R27199
theorem R46763 : Reach 46763 := rs (se 1 (by rfl) ⟨35072, by rfl⟩) R70145
theorem R177875 : Reach 177875 := rs (se 1 (by rfl) ⟨133406, by rfl⟩) R266813
theorem R79811 : Reach 79811 := rs (se 1 (by rfl) ⟨59858, by rfl⟩) R119717
theorem R47087 : Reach 47087 := rs (se 1 (by rfl) ⟨35315, by rfl⟩) R70631
theorem R47303 : Reach 47303 := rs (se 1 (by rfl) ⟨35477, by rfl⟩) R70955
theorem R47483 : Reach 47483 := rs (se 1 (by rfl) ⟨35612, by rfl⟩) R71225
theorem R47753 : Reach 47753 := rs (se 2 (by rfl) ⟨17907, by rfl⟩) R35815
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R146447 : Reach 146447 := rs (se 1 (by rfl) ⟨109835, by rfl⟩) R219671
theorem R48257 : Reach 48257 := rs (se 2 (by rfl) ⟨18096, by rfl⟩) R36193
theorem R48311 : Reach 48311 := rs (se 1 (by rfl) ⟨36233, by rfl⟩) R72467
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R48887 : Reach 48887 := rs (se 1 (by rfl) ⟨36665, by rfl⟩) R73331
theorem R49067 : Reach 49067 := rs (se 1 (by rfl) ⟨36800, by rfl⟩) R73601
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R49607 : Reach 49607 := rs (se 1 (by rfl) ⟨37205, by rfl⟩) R74411
theorem R49967 : Reach 49967 := rs (se 1 (by rfl) ⟨37475, by rfl⟩) R74951
theorem R115667 : Reach 115667 := rs (se 1 (by rfl) ⟨86750, by rfl⟩) R173501
theorem R50201 : Reach 50201 := rs (se 2 (by rfl) ⟨18825, by rfl⟩) R37651
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R50975 : Reach 50975 := rs (se 1 (by rfl) ⟨38231, by rfl⟩) R76463
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) R46459
theorem R51191 : Reach 51191 := rs (se 1 (by rfl) ⟨38393, by rfl⟩) R76787
theorem R247859 : Reach 247859 := rs (se 1 (by rfl) ⟨185894, by rfl⟩) R371789
theorem R51551 : Reach 51551 := rs (se 1 (by rfl) ⟨38663, by rfl⟩) R77327
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) R38713
theorem R281303 : Reach 281303 := rs (se 1 (by rfl) ⟨210977, by rfl⟩) R421955
theorem R52271 : Reach 52271 := rs (se 1 (by rfl) ⟨39203, by rfl⟩) R78407
theorem R52447 : Reach 52447 := rs (se 1 (by rfl) ⟨39335, by rfl⟩) R78671
theorem R52505 : Reach 52505 := rs (se 2 (by rfl) ⟨19689, by rfl⟩) R39379
theorem R52559 : Reach 52559 := rs (se 1 (by rfl) ⟨39419, by rfl⟩) R78839
theorem R52649 : Reach 52649 := rs (se 2 (by rfl) ⟨19743, by rfl⟩) R39487
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R20059 : Reach 20059 := rs (se 1 (by rfl) ⟨15044, by rfl⟩) R30089
theorem R85799 : Reach 85799 := rs (se 1 (by rfl) ⟨64349, by rfl⟩) R128699
theorem R20295 : Reach 20295 := rs (se 1 (by rfl) ⟨15221, by rfl⟩) R30443
theorem R20447 : Reach 20447 := rs (se 1 (by rfl) ⟨15335, by rfl⟩) R30671
theorem R20711 : Reach 20711 := rs (se 1 (by rfl) ⟨15533, by rfl⟩) R31067
theorem R20863 : Reach 20863 := rs (se 1 (by rfl) ⟨15647, by rfl⟩) R31295
theorem R20943 : Reach 20943 := rs (se 1 (by rfl) ⟨15707, by rfl⟩) R31415
theorem R53855 : Reach 53855 := rs (se 1 (by rfl) ⟨40391, by rfl⟩) R80783
theorem R21095 : Reach 21095 := rs (se 1 (by rfl) ⟨15821, by rfl⟩) R31643
theorem R21359 : Reach 21359 := rs (se 1 (by rfl) ⟨16019, by rfl⟩) R32039
theorem R21415 : Reach 21415 := rs (se 1 (by rfl) ⟨16061, by rfl⟩) R32123
theorem R21499 : Reach 21499 := rs (se 1 (by rfl) ⟨16124, by rfl⟩) R32249
theorem R21567 : Reach 21567 := rs (se 1 (by rfl) ⟨16175, by rfl⟩) R32351
theorem R54379 : Reach 54379 := rs (se 1 (by rfl) ⟨40784, by rfl⟩) R81569
theorem R21679 : Reach 21679 := rs (se 1 (by rfl) ⟨16259, by rfl⟩) R32519
theorem R21711 : Reach 21711 := rs (se 1 (by rfl) ⟨16283, by rfl⟩) R32567
theorem R21915 : Reach 21915 := rs (se 1 (by rfl) ⟨16436, by rfl⟩) R32873
theorem R22127 : Reach 22127 := rs (se 1 (by rfl) ⟨16595, by rfl⟩) R33191
theorem R22183 : Reach 22183 := rs (se 1 (by rfl) ⟨16637, by rfl⟩) R33275
theorem R22235 : Reach 22235 := rs (se 1 (by rfl) ⟨16676, by rfl⟩) R33353
theorem R22267 : Reach 22267 := rs (se 1 (by rfl) ⟨16700, by rfl⟩) R33401
theorem R22303 : Reach 22303 := rs (se 1 (by rfl) ⟨16727, by rfl⟩) R33455
theorem R22335 : Reach 22335 := rs (se 1 (by rfl) ⟨16751, by rfl⟩) R33503
theorem R22471 : Reach 22471 := rs (se 1 (by rfl) ⟨16853, by rfl⟩) R33707
theorem R153575 : Reach 153575 := rs (se 1 (by rfl) ⟨115181, by rfl⟩) R230363
theorem R22511 : Reach 22511 := rs (se 1 (by rfl) ⟨16883, by rfl⟩) R33767
theorem R22623 : Reach 22623 := rs (se 1 (by rfl) ⟨16967, by rfl⟩) R33935
theorem R22683 : Reach 22683 := rs (se 1 (by rfl) ⟨17012, by rfl⟩) R34025
theorem R22719 : Reach 22719 := rs (se 1 (by rfl) ⟨17039, by rfl⟩) R34079
theorem R88361 : Reach 88361 := rs (se 2 (by rfl) ⟨33135, by rfl⟩) R66271
theorem R22831 : Reach 22831 := rs (se 1 (by rfl) ⟨17123, by rfl⟩) R34247
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R23067 : Reach 23067 := rs (se 1 (by rfl) ⟨17300, by rfl⟩) R34601
theorem R23071 : Reach 23071 := rs (se 1 (by rfl) ⟨17303, by rfl⟩) R34607
theorem R23387 : Reach 23387 := rs (se 1 (by rfl) ⟨17540, by rfl⟩) R35081
theorem R23455 : Reach 23455 := rs (se 1 (by rfl) ⟨17591, by rfl⟩) R35183
theorem R482233 : Reach 482233 := rs (se 2 (by rfl) ⟨180837, by rfl⟩) R361675
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R286739 : Reach 286739 := rs (se 1 (by rfl) ⟨215054, by rfl⟩) R430109
theorem R57631 : Reach 57631 := rs (se 1 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R58279 : Reach 58279 := rs (se 1 (by rfl) ⟨43709, by rfl⟩) R87419
theorem R25663 : Reach 25663 := rs (se 1 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R255149 : Reach 255149 := rs (se 3 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R25807 : Reach 25807 := rs (se 1 (by rfl) ⟨19355, by rfl⟩) R38711
theorem R26011 : Reach 26011 := rs (se 1 (by rfl) ⟨19508, by rfl⟩) R39017
theorem R58799 : Reach 58799 := rs (se 1 (by rfl) ⟨44099, by rfl⟩) R88199
theorem R58877 : Reach 58877 := rs (se 3 (by rfl) ⟨11039, by rfl⟩) R22079
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R59687 : Reach 59687 := rs (se 1 (by rfl) ⟨44765, by rfl⟩) R89531
theorem R60659 : Reach 60659 := rs (se 1 (by rfl) ⟨45494, by rfl⟩) R90989
theorem R27983 : Reach 27983 := rs (se 1 (by rfl) ⟨20987, by rfl⟩) R41975
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) R35983
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R61327 : Reach 61327 := rs (se 1 (by rfl) ⟨45995, by rfl⟩) R91991
theorem R389285 : Reach 389285 := rs (se 4 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R30107 : Reach 30107 := rs (se 1 (by rfl) ⟨22580, by rfl⟩) R45161
theorem R161351 : Reach 161351 := rs (se 1 (by rfl) ⟨121013, by rfl⟩) R242027
theorem R30329 : Reach 30329 := rs (se 2 (by rfl) ⟨11373, by rfl⟩) R22747
theorem R30431 : Reach 30431 := rs (se 1 (by rfl) ⟨22823, by rfl⟩) R45647
theorem R30527 : Reach 30527 := rs (se 1 (by rfl) ⟨22895, by rfl⟩) R45791
theorem R30695 : Reach 30695 := rs (se 1 (by rfl) ⟨23021, by rfl⟩) R46043
theorem R30713 : Reach 30713 := rs (se 2 (by rfl) ⟨11517, by rfl⟩) R23035
theorem R30815 : Reach 30815 := rs (se 1 (by rfl) ⟨23111, by rfl⟩) R46223
theorem R30875 : Reach 30875 := rs (se 1 (by rfl) ⟨23156, by rfl⟩) R46313
theorem R30911 : Reach 30911 := rs (se 1 (by rfl) ⟨23183, by rfl⟩) R46367
theorem R30953 : Reach 30953 := rs (se 2 (by rfl) ⟨11607, by rfl⟩) R23215
theorem R981233 : Reach 981233 := rs (se 2 (by rfl) ⟨367962, by rfl⟩) R735925
theorem R162323 : Reach 162323 := rs (se 1 (by rfl) ⟨121742, by rfl⟩) R243485
theorem R31259 : Reach 31259 := rs (se 1 (by rfl) ⟨23444, by rfl⟩) R46889
theorem R31337 : Reach 31337 := rs (se 2 (by rfl) ⟨11751, by rfl⟩) R23503
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R195533 : Reach 195533 := rs (se 3 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R31865 : Reach 31865 := rs (se 2 (by rfl) ⟨11949, by rfl⟩) R23899
theorem R31967 : Reach 31967 := rs (se 1 (by rfl) ⟨23975, by rfl⟩) R47951
theorem R32009 : Reach 32009 := rs (se 2 (by rfl) ⟨12003, by rfl⟩) R24007
theorem R32111 : Reach 32111 := rs (se 1 (by rfl) ⟨24083, by rfl⟩) R48167
theorem R32167 : Reach 32167 := rs (se 1 (by rfl) ⟨24125, by rfl⟩) R48251
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R32231 : Reach 32231 := rs (se 1 (by rfl) ⟨24173, by rfl⟩) R48347
theorem R294425 : Reach 294425 := rs (se 2 (by rfl) ⟨110409, by rfl⟩) R220819
theorem R32363 : Reach 32363 := rs (se 1 (by rfl) ⟨24272, by rfl⟩) R48545
theorem R32399 : Reach 32399 := rs (se 1 (by rfl) ⟨24299, by rfl⟩) R48599
theorem R32489 : Reach 32489 := rs (se 2 (by rfl) ⟨12183, by rfl⟩) R24367
theorem R32633 : Reach 32633 := rs (se 2 (by rfl) ⟨12237, by rfl⟩) R24475
theorem R65405 : Reach 65405 := rs (se 3 (by rfl) ⟨12263, by rfl⟩) R24527
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R32735 : Reach 32735 := rs (se 1 (by rfl) ⟨24551, by rfl⟩) R49103
theorem R33071 : Reach 33071 := rs (se 1 (by rfl) ⟨24803, by rfl⟩) R49607
theorem R33311 : Reach 33311 := rs (se 1 (by rfl) ⟨24983, by rfl⟩) R49967
theorem R33467 : Reach 33467 := rs (se 1 (by rfl) ⟨25100, by rfl⟩) R50201
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R33983 : Reach 33983 := rs (se 1 (by rfl) ⟨25487, by rfl⟩) R50975
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R34127 : Reach 34127 := rs (se 1 (by rfl) ⟨25595, by rfl⟩) R51191
theorem R165239 : Reach 165239 := rs (se 1 (by rfl) ⟨123929, by rfl⟩) R247859
theorem R34217 : Reach 34217 := rs (se 2 (by rfl) ⟨12831, by rfl⟩) R25663
theorem R34367 : Reach 34367 := rs (se 1 (by rfl) ⟨25775, by rfl⟩) R51551
theorem R34409 : Reach 34409 := rs (se 2 (by rfl) ⟨12903, by rfl⟩) R25807
theorem R34411 : Reach 34411 := rs (se 1 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R34681 : Reach 34681 := rs (se 2 (by rfl) ⟨13005, by rfl⟩) R26011
theorem R34847 : Reach 34847 := rs (se 1 (by rfl) ⟨26135, by rfl⟩) R52271
theorem R35003 : Reach 35003 := rs (se 1 (by rfl) ⟨26252, by rfl⟩) R52505
theorem R35039 : Reach 35039 := rs (se 1 (by rfl) ⟨26279, by rfl⟩) R52559
theorem R35099 : Reach 35099 := rs (se 1 (by rfl) ⟨26324, by rfl⟩) R52649
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R35903 : Reach 35903 := rs (se 1 (by rfl) ⟨26927, by rfl⟩) R53855
theorem R68795 : Reach 68795 := rs (se 1 (by rfl) ⟨51596, by rfl⟩) R103193
theorem R102383 : Reach 102383 := rs (se 1 (by rfl) ⟨76787, by rfl⟩) R153575
theorem R69767 : Reach 69767 := rs (se 1 (by rfl) ⟨52325, by rfl⟩) R104651
theorem R69929 : Reach 69929 := rs (se 2 (by rfl) ⟨26223, by rfl⟩) R52447
theorem R70199 : Reach 70199 := rs (se 1 (by rfl) ⟨52649, by rfl⟩) R105299
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R71387 : Reach 71387 := rs (se 1 (by rfl) ⟨53540, by rfl⟩) R107081
theorem R170099 : Reach 170099 := rs (se 1 (by rfl) ⟨127574, by rfl⟩) R255149
theorem R39199 : Reach 39199 := rs (se 1 (by rfl) ⟨29399, by rfl⟩) R58799
theorem R39251 : Reach 39251 := rs (se 1 (by rfl) ⟨29438, by rfl⟩) R58877
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) R54379
theorem R39791 : Reach 39791 := rs (se 1 (by rfl) ⟨29843, by rfl⟩) R59687
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R40439 : Reach 40439 := rs (se 1 (by rfl) ⟨30329, by rfl⟩) R60659
theorem R171557 : Reach 171557 := rs (se 4 (by rfl) ⟨16083, by rfl⟩) R32167
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R41735 : Reach 41735 := rs (se 1 (by rfl) ⟨31301, by rfl⟩) R62603
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) R27983
theorem R107567 : Reach 107567 := rs (se 1 (by rfl) ⟨80675, by rfl⟩) R161351
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R108215 : Reach 108215 := rs (se 1 (by rfl) ⟨81161, by rfl⟩) R162323
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R42943 : Reach 42943 := rs (se 1 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R174413 : Reach 174413 := rs (se 3 (by rfl) ⟨32702, by rfl⟩) R65405
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R76841 : Reach 76841 := rs (se 2 (by rfl) ⟨28815, by rfl⟩) R57631
theorem R77111 : Reach 77111 := rs (se 1 (by rfl) ⟨57833, by rfl⟩) R115667
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R175931 : Reach 175931 := rs (se 1 (by rfl) ⟨131948, by rfl⟩) R263897
theorem R77705 : Reach 77705 := rs (se 2 (by rfl) ⟨29139, by rfl⟩) R58279
theorem R45287 : Reach 45287 := rs (se 1 (by rfl) ⟨33965, by rfl⟩) R67931
theorem R45467 : Reach 45467 := rs (se 1 (by rfl) ⟨34100, by rfl⟩) R68201
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R46151 : Reach 46151 := rs (se 1 (by rfl) ⟨34613, by rfl⟩) R69227
theorem R46331 : Reach 46331 := rs (se 1 (by rfl) ⟨34748, by rfl⟩) R69497
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R46547 : Reach 46547 := rs (se 1 (by rfl) ⟨34910, by rfl⟩) R69821
theorem R46817 : Reach 46817 := rs (se 2 (by rfl) ⟨17556, by rfl⟩) R35113
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R178361 : Reach 178361 := rs (se 2 (by rfl) ⟨66885, by rfl⟩) R133771
theorem R47339 : Reach 47339 := rs (se 1 (by rfl) ⟨35504, by rfl⟩) R71009
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R48635 : Reach 48635 := rs (se 1 (by rfl) ⟨36476, by rfl⟩) R72953
theorem R48815 : Reach 48815 := rs (se 1 (by rfl) ⟨36611, by rfl⟩) R73223
theorem R48863 : Reach 48863 := rs (se 1 (by rfl) ⟨36647, by rfl⟩) R73295
theorem R48905 : Reach 48905 := rs (se 2 (by rfl) ⟨18339, by rfl⟩) R36679
theorem R81769 : Reach 81769 := rs (se 2 (by rfl) ⟨30663, by rfl⟩) R61327
theorem R180427 : Reach 180427 := rs (se 1 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R49447 : Reach 49447 := rs (se 1 (by rfl) ⟨37085, by rfl⟩) R74171
theorem R49535 : Reach 49535 := rs (se 1 (by rfl) ⟨37151, by rfl⟩) R74303
theorem R49769 : Reach 49769 := rs (se 2 (by rfl) ⟨18663, by rfl⟩) R37327
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R50615 : Reach 50615 := rs (se 1 (by rfl) ⟨37961, by rfl⟩) R75923
theorem R50795 : Reach 50795 := rs (se 1 (by rfl) ⟨38096, by rfl⟩) R76193
theorem R51065 : Reach 51065 := rs (se 2 (by rfl) ⟨19149, by rfl⟩) R38299
theorem R51443 : Reach 51443 := rs (se 1 (by rfl) ⟨38582, by rfl⟩) R77165
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R52073 : Reach 52073 := rs (se 2 (by rfl) ⟨19527, by rfl⟩) R39055
theorem R183161 : Reach 183161 := rs (se 2 (by rfl) ⟨68685, by rfl⟩) R137371
theorem R117935 : Reach 117935 := rs (se 1 (by rfl) ⟨88451, by rfl⟩) R176903
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R20071 : Reach 20071 := rs (se 1 (by rfl) ⟨15053, by rfl⟩) R30107
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R20219 : Reach 20219 := rs (se 1 (by rfl) ⟨15164, by rfl⟩) R30329
theorem R118583 : Reach 118583 := rs (se 1 (by rfl) ⟨88937, by rfl⟩) R177875
theorem R20287 : Reach 20287 := rs (se 1 (by rfl) ⟨15215, by rfl⟩) R30431
theorem R20351 : Reach 20351 := rs (se 1 (by rfl) ⟨15263, by rfl⟩) R30527
theorem R642977 : Reach 642977 := rs (se 2 (by rfl) ⟨241116, by rfl⟩) R482233
theorem R53207 : Reach 53207 := rs (se 1 (by rfl) ⟨39905, by rfl⟩) R79811
theorem R20463 : Reach 20463 := rs (se 1 (by rfl) ⟨15347, by rfl⟩) R30695
theorem R20475 : Reach 20475 := rs (se 1 (by rfl) ⟨15356, by rfl⟩) R30713
theorem R20543 : Reach 20543 := rs (se 1 (by rfl) ⟨15407, by rfl⟩) R30815
theorem R20583 : Reach 20583 := rs (se 1 (by rfl) ⟨15437, by rfl⟩) R30875
theorem R20607 : Reach 20607 := rs (se 1 (by rfl) ⟨15455, by rfl⟩) R30911
theorem R20635 : Reach 20635 := rs (se 1 (by rfl) ⟨15476, by rfl⟩) R30953
theorem R20839 : Reach 20839 := rs (se 1 (by rfl) ⟨15629, by rfl⟩) R31259
theorem R20891 : Reach 20891 := rs (se 1 (by rfl) ⟨15668, by rfl⟩) R31337
theorem R21243 : Reach 21243 := rs (se 1 (by rfl) ⟨15932, by rfl⟩) R31865
theorem R21311 : Reach 21311 := rs (se 1 (by rfl) ⟨15983, by rfl⟩) R31967
theorem R21339 : Reach 21339 := rs (se 1 (by rfl) ⟨16004, by rfl⟩) R32009
theorem R54121 : Reach 54121 := rs (se 2 (by rfl) ⟨20295, by rfl⟩) R40591
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R21407 : Reach 21407 := rs (se 1 (by rfl) ⟨16055, by rfl⟩) R32111
theorem R21487 : Reach 21487 := rs (se 1 (by rfl) ⟨16115, by rfl⟩) R32231
theorem R21575 : Reach 21575 := rs (se 1 (by rfl) ⟨16181, by rfl⟩) R32363
theorem R21599 : Reach 21599 := rs (se 1 (by rfl) ⟨16199, by rfl⟩) R32399
theorem R21659 : Reach 21659 := rs (se 1 (by rfl) ⟨16244, by rfl⟩) R32489
theorem R21755 : Reach 21755 := rs (se 1 (by rfl) ⟨16316, by rfl⟩) R32633
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) R32735
theorem R21823 : Reach 21823 := rs (se 1 (by rfl) ⟨16367, by rfl⟩) R32735
theorem R21991 : Reach 21991 := rs (se 1 (by rfl) ⟨16493, by rfl⟩) R32987
theorem R21999 : Reach 21999 := rs (se 1 (by rfl) ⟨16499, by rfl⟩) R32999
theorem R22107 : Reach 22107 := rs (se 1 (by rfl) ⟨16580, by rfl⟩) R33161
theorem R22171 : Reach 22171 := rs (se 1 (by rfl) ⟨16628, by rfl⟩) R33257
theorem R22255 : Reach 22255 := rs (se 1 (by rfl) ⟨16691, by rfl⟩) R33383
theorem R22343 : Reach 22343 := rs (se 1 (by rfl) ⟨16757, by rfl⟩) R33515
theorem R120649 : Reach 120649 := rs (se 2 (by rfl) ⟨45243, by rfl⟩) R90487
theorem R22363 : Reach 22363 := rs (se 1 (by rfl) ⟨16772, by rfl⟩) R33545
theorem R22395 : Reach 22395 := rs (se 1 (by rfl) ⟨16796, by rfl⟩) R33593
theorem R22431 : Reach 22431 := rs (se 1 (by rfl) ⟨16823, by rfl⟩) R33647
theorem R22599 : Reach 22599 := rs (se 1 (by rfl) ⟨16949, by rfl⟩) R33899
theorem R153683 : Reach 153683 := rs (se 1 (by rfl) ⟨115262, by rfl⟩) R230525
theorem R22759 : Reach 22759 := rs (se 1 (by rfl) ⟨17069, by rfl⟩) R34139
theorem R22943 : Reach 22943 := rs (se 1 (by rfl) ⟨17207, by rfl⟩) R34415
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R22991 : Reach 22991 := rs (se 1 (by rfl) ⟨17243, by rfl⟩) R34487
theorem R23015 : Reach 23015 := rs (se 1 (by rfl) ⟨17261, by rfl⟩) R34523
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R23131 : Reach 23131 := rs (se 1 (by rfl) ⟨17348, by rfl⟩) R34697
theorem R23199 : Reach 23199 := rs (se 1 (by rfl) ⟨17399, by rfl⟩) R34799
theorem R23367 : Reach 23367 := rs (se 1 (by rfl) ⟨17525, by rfl⟩) R35051
theorem R23407 : Reach 23407 := rs (se 1 (by rfl) ⟨17555, by rfl⟩) R35111
theorem R23419 : Reach 23419 := rs (se 1 (by rfl) ⟨17564, by rfl⟩) R35129
theorem R23463 : Reach 23463 := rs (se 1 (by rfl) ⟨17597, by rfl⟩) R35195
theorem R187535 : Reach 187535 := rs (se 1 (by rfl) ⟨140651, by rfl⟩) R281303
theorem R56999 : Reach 56999 := rs (se 1 (by rfl) ⟨42749, by rfl⟩) R85499
theorem R155303 : Reach 155303 := rs (se 1 (by rfl) ⟨116477, by rfl⟩) R232955
theorem R24295 : Reach 24295 := rs (se 1 (by rfl) ⟨18221, by rfl⟩) R36443
theorem R57199 : Reach 57199 := rs (se 1 (by rfl) ⟨42899, by rfl⟩) R85799
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R25375 : Reach 25375 := rs (se 1 (by rfl) ⟨19031, by rfl⟩) R38063
theorem R58441 : Reach 58441 := rs (se 2 (by rfl) ⟨21915, by rfl⟩) R43831
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R58907 : Reach 58907 := rs (se 1 (by rfl) ⟨44180, by rfl⟩) R88361
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R191159 : Reach 191159 := rs (se 1 (by rfl) ⟨143369, by rfl⟩) R286739
theorem R93257 : Reach 93257 := rs (se 2 (by rfl) ⟨34971, by rfl⟩) R69943
theorem R159043 : Reach 159043 := rs (se 1 (by rfl) ⟨119282, by rfl⟩) R238565
theorem R28127 : Reach 28127 := rs (se 1 (by rfl) ⟨21095, by rfl⟩) R42191
theorem R159407 : Reach 159407 := rs (se 1 (by rfl) ⟨119555, by rfl⟩) R239111
theorem R127939 : Reach 127939 := rs (se 1 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R29737 : Reach 29737 := rs (se 2 (by rfl) ⟨11151, by rfl⟩) R22303
theorem R30119 : Reach 30119 := rs (se 1 (by rfl) ⟨22589, by rfl⟩) R45179
theorem R259523 : Reach 259523 := rs (se 1 (by rfl) ⟨194642, by rfl⟩) R389285
theorem R30299 : Reach 30299 := rs (se 1 (by rfl) ⟨22724, by rfl⟩) R45449
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R30761 : Reach 30761 := rs (se 2 (by rfl) ⟨11535, by rfl⟩) R23071
theorem R30791 : Reach 30791 := rs (se 1 (by rfl) ⟨23093, by rfl⟩) R46187
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R31175 : Reach 31175 := rs (se 1 (by rfl) ⟨23381, by rfl⟩) R46763
theorem R31391 : Reach 31391 := rs (se 1 (by rfl) ⟨23543, by rfl⟩) R47087
theorem R31535 : Reach 31535 := rs (se 1 (by rfl) ⟨23651, by rfl⟩) R47303
theorem R654155 : Reach 654155 := rs (se 1 (by rfl) ⟨490616, by rfl⟩) R981233
theorem R31655 : Reach 31655 := rs (se 1 (by rfl) ⟨23741, by rfl⟩) R47483
theorem R31835 : Reach 31835 := rs (se 1 (by rfl) ⟨23876, by rfl⟩) R47753
theorem R130355 : Reach 130355 := rs (se 1 (by rfl) ⟨97766, by rfl⟩) R195533
theorem R97631 : Reach 97631 := rs (se 1 (by rfl) ⟨73223, by rfl⟩) R146447
theorem R32171 : Reach 32171 := rs (se 1 (by rfl) ⟨24128, by rfl⟩) R48257
theorem R32207 : Reach 32207 := rs (se 1 (by rfl) ⟨24155, by rfl⟩) R48311
theorem R196283 : Reach 196283 := rs (se 1 (by rfl) ⟨147212, by rfl⟩) R294425
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R32591 : Reach 32591 := rs (se 1 (by rfl) ⟨24443, by rfl⟩) R48887
theorem R32711 : Reach 32711 := rs (se 1 (by rfl) ⟨24533, by rfl⟩) R49067
theorem R33023 : Reach 33023 := rs (se 1 (by rfl) ⟨24767, by rfl⟩) R49535
theorem R65929 : Reach 65929 := rs (se 2 (by rfl) ⟨24723, by rfl⟩) R49447
theorem R33179 : Reach 33179 := rs (se 1 (by rfl) ⟨24884, by rfl⟩) R49769
theorem R66055 : Reach 66055 := rs (se 1 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R33743 : Reach 33743 := rs (se 1 (by rfl) ⟨25307, by rfl⟩) R50615
theorem R33833 : Reach 33833 := rs (se 2 (by rfl) ⟨12687, by rfl⟩) R25375
theorem R33863 : Reach 33863 := rs (se 1 (by rfl) ⟨25397, by rfl⟩) R50795
theorem R34043 : Reach 34043 := rs (se 1 (by rfl) ⟨25532, by rfl⟩) R51065
theorem R34295 : Reach 34295 := rs (se 1 (by rfl) ⟨25721, by rfl⟩) R51443
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R34715 : Reach 34715 := rs (se 1 (by rfl) ⟨26036, by rfl⟩) R52073
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R428651 : Reach 428651 := rs (se 1 (by rfl) ⟨321488, by rfl⟩) R642977
theorem R35471 : Reach 35471 := rs (se 1 (by rfl) ⟨26603, by rfl⟩) R53207
theorem R68255 : Reach 68255 := rs (se 1 (by rfl) ⟨51191, by rfl⟩) R102383
theorem R102455 : Reach 102455 := rs (se 1 (by rfl) ⟨76841, by rfl⟩) R153683
theorem R37999 : Reach 37999 := rs (se 1 (by rfl) ⟨28499, by rfl⟩) R56999
theorem R103535 : Reach 103535 := rs (se 1 (by rfl) ⟨77651, by rfl⟩) R155303
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R71711 : Reach 71711 := rs (se 1 (by rfl) ⟨53783, by rfl⟩) R107567
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R39271 : Reach 39271 := rs (se 1 (by rfl) ⟨29453, by rfl⟩) R58907
theorem R72143 : Reach 72143 := rs (se 1 (by rfl) ⟨54107, by rfl⟩) R108215
theorem R72161 : Reach 72161 := rs (se 2 (by rfl) ⟨27060, by rfl⟩) R54121
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R170585 : Reach 170585 := rs (se 2 (by rfl) ⟨63969, by rfl⟩) R127939
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R39649 : Reach 39649 := rs (se 2 (by rfl) ⟨14868, by rfl⟩) R29737
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R106109 : Reach 106109 := rs (se 3 (by rfl) ⟨19895, by rfl⟩) R39791
theorem R106271 : Reach 106271 := rs (se 1 (by rfl) ⟨79703, by rfl⟩) R159407
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R173015 : Reach 173015 := rs (se 1 (by rfl) ⟨129761, by rfl⟩) R259523
theorem R75005 : Reach 75005 := rs (se 3 (by rfl) ⟨14063, by rfl⟩) R28127
theorem R107837 : Reach 107837 := rs (se 3 (by rfl) ⟨20219, by rfl⟩) R40439
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R436103 : Reach 436103 := rs (se 1 (by rfl) ⟨327077, by rfl⟩) R654155
theorem R109025 : Reach 109025 := rs (se 2 (by rfl) ⟨40884, by rfl⟩) R81769
theorem R76265 : Reach 76265 := rs (se 2 (by rfl) ⟨28599, by rfl⟩) R57199
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R240569 : Reach 240569 := rs (se 2 (by rfl) ⟨90213, by rfl⟩) R180427
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R110159 : Reach 110159 := rs (se 1 (by rfl) ⟨82619, by rfl⟩) R165239
theorem R77921 : Reach 77921 := rs (se 2 (by rfl) ⟨29220, by rfl⟩) R58441
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R111293 : Reach 111293 := rs (se 3 (by rfl) ⟨20867, by rfl⟩) R41735
theorem R78623 : Reach 78623 := rs (se 1 (by rfl) ⟨58967, by rfl⟩) R117935
theorem R45863 : Reach 45863 := rs (se 1 (by rfl) ⟨34397, by rfl⟩) R68795
theorem R45881 : Reach 45881 := rs (se 2 (by rfl) ⟨17205, by rfl⟩) R34411
theorem R46241 : Reach 46241 := rs (se 2 (by rfl) ⟨17340, by rfl⟩) R34681
theorem R79055 : Reach 79055 := rs (se 1 (by rfl) ⟨59291, by rfl⟩) R118583
theorem R46511 : Reach 46511 := rs (se 1 (by rfl) ⟨34883, by rfl⟩) R69767
theorem R46619 : Reach 46619 := rs (se 1 (by rfl) ⟨34964, by rfl⟩) R69929
theorem R46799 : Reach 46799 := rs (se 1 (by rfl) ⟨35099, by rfl⟩) R70199
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R47591 : Reach 47591 := rs (se 1 (by rfl) ⟨35693, by rfl⟩) R71387
theorem R113399 : Reach 113399 := rs (se 1 (by rfl) ⟨85049, by rfl⟩) R170099
theorem R80797 : Reach 80797 := rs (se 3 (by rfl) ⟨15149, by rfl⟩) R30299
theorem R212057 : Reach 212057 := rs (se 2 (by rfl) ⟨79521, by rfl⟩) R159043
theorem R48559 : Reach 48559 := rs (se 1 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R114371 : Reach 114371 := rs (se 1 (by rfl) ⟨85778, by rfl⟩) R171557
theorem R49747 : Reach 49747 := rs (se 1 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R50495 : Reach 50495 := rs (se 1 (by rfl) ⟨37871, by rfl⟩) R75743
theorem R116275 : Reach 116275 := rs (se 1 (by rfl) ⟨87206, by rfl⟩) R174413
theorem R51227 : Reach 51227 := rs (se 1 (by rfl) ⟨38420, by rfl⟩) R76841
theorem R51407 : Reach 51407 := rs (se 1 (by rfl) ⟨38555, by rfl⟩) R77111
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R117287 : Reach 117287 := rs (se 1 (by rfl) ⟨87965, by rfl⟩) R175931
theorem R51803 : Reach 51803 := rs (se 1 (by rfl) ⟨38852, by rfl⟩) R77705
theorem R52265 : Reach 52265 := rs (se 2 (by rfl) ⟨19599, by rfl⟩) R39199
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R20079 : Reach 20079 := rs (se 1 (by rfl) ⟨15059, by rfl⟩) R30119
theorem R20199 : Reach 20199 := rs (se 1 (by rfl) ⟨15149, by rfl⟩) R30299
theorem R20507 : Reach 20507 := rs (se 1 (by rfl) ⟨15380, by rfl⟩) R30761
theorem R20527 : Reach 20527 := rs (se 1 (by rfl) ⟨15395, by rfl⟩) R30791
theorem R118907 : Reach 118907 := rs (se 1 (by rfl) ⟨89180, by rfl⟩) R178361
theorem R20783 : Reach 20783 := rs (se 1 (by rfl) ⟨15587, by rfl⟩) R31175
theorem R20927 : Reach 20927 := rs (se 1 (by rfl) ⟨15695, by rfl⟩) R31391
theorem R21023 : Reach 21023 := rs (se 1 (by rfl) ⟨15767, by rfl⟩) R31535
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R21103 : Reach 21103 := rs (se 1 (by rfl) ⟨15827, by rfl⟩) R31655
theorem R21223 : Reach 21223 := rs (se 1 (by rfl) ⟨15917, by rfl⟩) R31835
theorem R86903 : Reach 86903 := rs (se 1 (by rfl) ⟨65177, by rfl⟩) R130355
theorem R21447 : Reach 21447 := rs (se 1 (by rfl) ⟨16085, by rfl⟩) R32171
theorem R21471 : Reach 21471 := rs (se 1 (by rfl) ⟨16103, by rfl⟩) R32207
theorem R21727 : Reach 21727 := rs (se 1 (by rfl) ⟨16295, by rfl⟩) R32591
theorem R21807 : Reach 21807 := rs (se 1 (by rfl) ⟨16355, by rfl⟩) R32711
theorem R22047 : Reach 22047 := rs (se 1 (by rfl) ⟨16535, by rfl⟩) R33071
theorem R22207 : Reach 22207 := rs (se 1 (by rfl) ⟨16655, by rfl⟩) R33311
theorem R22311 : Reach 22311 := rs (se 1 (by rfl) ⟨16733, by rfl⟩) R33467
theorem R22655 : Reach 22655 := rs (se 1 (by rfl) ⟨16991, by rfl⟩) R33983
theorem R22751 : Reach 22751 := rs (se 1 (by rfl) ⟨17063, by rfl⟩) R34127
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R22811 : Reach 22811 := rs (se 1 (by rfl) ⟨17108, by rfl⟩) R34217
theorem R22911 : Reach 22911 := rs (se 1 (by rfl) ⟨17183, by rfl⟩) R34367
theorem R22939 : Reach 22939 := rs (se 1 (by rfl) ⟨17204, by rfl⟩) R34409
theorem R23231 : Reach 23231 := rs (se 1 (by rfl) ⟨17423, by rfl⟩) R34847
theorem R23335 : Reach 23335 := rs (se 1 (by rfl) ⟨17501, by rfl⟩) R35003
theorem R23359 : Reach 23359 := rs (se 1 (by rfl) ⟨17519, by rfl⟩) R35039
theorem R23399 : Reach 23399 := rs (se 1 (by rfl) ⟨17549, by rfl⟩) R35099
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R122107 : Reach 122107 := rs (se 1 (by rfl) ⟨91580, by rfl⟩) R183161
theorem R23935 : Reach 23935 := rs (se 1 (by rfl) ⟨17951, by rfl⟩) R35903
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R57257 : Reach 57257 := rs (se 2 (by rfl) ⟨21471, by rfl⟩) R42943
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R26167 : Reach 26167 := rs (se 1 (by rfl) ⟨19625, by rfl⟩) R39251
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R125023 : Reach 125023 := rs (se 1 (by rfl) ⟨93767, by rfl⟩) R187535
theorem R27049 : Reach 27049 := rs (se 2 (by rfl) ⟨10143, by rfl⟩) R20287
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R61373 : Reach 61373 := rs (se 3 (by rfl) ⟨11507, by rfl⟩) R23015
theorem R127439 : Reach 127439 := rs (se 1 (by rfl) ⟨95579, by rfl⟩) R191159
theorem R62171 : Reach 62171 := rs (se 1 (by rfl) ⟨46628, by rfl⟩) R93257
theorem R160865 : Reach 160865 := rs (se 2 (by rfl) ⟨60324, by rfl⟩) R120649
theorem R30191 : Reach 30191 := rs (se 1 (by rfl) ⟨22643, by rfl⟩) R45287
theorem R30311 : Reach 30311 := rs (se 1 (by rfl) ⟨22733, by rfl⟩) R45467
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R30767 : Reach 30767 := rs (se 1 (by rfl) ⟨23075, by rfl⟩) R46151
theorem R30887 : Reach 30887 := rs (se 1 (by rfl) ⟨23165, by rfl⟩) R46331
theorem R31031 : Reach 31031 := rs (se 1 (by rfl) ⟨23273, by rfl⟩) R46547
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) R72505
theorem R31211 : Reach 31211 := rs (se 1 (by rfl) ⟨23408, by rfl⟩) R46817
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R31559 : Reach 31559 := rs (se 1 (by rfl) ⟨23669, by rfl⟩) R47339
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R65087 : Reach 65087 := rs (se 1 (by rfl) ⟨48815, by rfl⟩) R97631
theorem R32393 : Reach 32393 := rs (se 2 (by rfl) ⟨12147, by rfl⟩) R24295
theorem R32423 : Reach 32423 := rs (se 1 (by rfl) ⟨24317, by rfl⟩) R48635
theorem R32543 : Reach 32543 := rs (se 1 (by rfl) ⟨24407, by rfl⟩) R48815
theorem R130855 : Reach 130855 := rs (se 1 (by rfl) ⟨98141, by rfl⟩) R196283
theorem R32575 : Reach 32575 := rs (se 1 (by rfl) ⟨24431, by rfl⟩) R48863
theorem R32603 : Reach 32603 := rs (se 1 (by rfl) ⟨24452, by rfl⟩) R48905
theorem R66329 : Reach 66329 := rs (se 2 (by rfl) ⟨24873, by rfl⟩) R49747
theorem R34151 : Reach 34151 := rs (se 1 (by rfl) ⟨25613, by rfl⟩) R51227
theorem R34271 : Reach 34271 := rs (se 1 (by rfl) ⟨25703, by rfl⟩) R51407
theorem R34535 : Reach 34535 := rs (se 1 (by rfl) ⟨25901, by rfl⟩) R51803
theorem R1771469 : Reach 1771469 := rs (se 3 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R34843 : Reach 34843 := rs (se 1 (by rfl) ⟨26132, by rfl⟩) R52265
theorem R34889 : Reach 34889 := rs (se 2 (by rfl) ⟨13083, by rfl⟩) R26167
theorem R68303 : Reach 68303 := rs (se 1 (by rfl) ⟨51227, by rfl⟩) R102455
theorem R166697 : Reach 166697 := rs (se 2 (by rfl) ⟨62511, by rfl⟩) R125023
theorem R36065 : Reach 36065 := rs (se 2 (by rfl) ⟨13524, by rfl⟩) R27049
theorem R69023 : Reach 69023 := rs (se 1 (by rfl) ⟨51767, by rfl⟩) R103535
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) R52591
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R70739 : Reach 70739 := rs (se 1 (by rfl) ⟨53054, by rfl⟩) R106109
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R70847 : Reach 70847 := rs (se 1 (by rfl) ⟨53135, by rfl⟩) R106271
theorem R38171 : Reach 38171 := rs (se 1 (by rfl) ⟨28628, by rfl⟩) R57257
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R71891 : Reach 71891 := rs (se 1 (by rfl) ⟨53918, by rfl⟩) R107837
theorem R72683 : Reach 72683 := rs (se 1 (by rfl) ⟨54512, by rfl⟩) R109025
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R73439 : Reach 73439 := rs (se 1 (by rfl) ⟨55079, by rfl⟩) R110159
theorem R40915 : Reach 40915 := rs (se 1 (by rfl) ⟨30686, by rfl⟩) R61373
theorem R74195 : Reach 74195 := rs (se 1 (by rfl) ⟨55646, by rfl⟩) R111293
theorem R41447 : Reach 41447 := rs (se 1 (by rfl) ⟨31085, by rfl⟩) R62171
theorem R107243 : Reach 107243 := rs (se 1 (by rfl) ⟨80432, by rfl⟩) R160865
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R107729 : Reach 107729 := rs (se 2 (by rfl) ⟨40398, by rfl⟩) R80797
theorem R75599 : Reach 75599 := rs (se 1 (by rfl) ⟨56699, by rfl⟩) R113399
theorem R141371 : Reach 141371 := rs (se 1 (by rfl) ⟨106028, by rfl⟩) R212057
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R43391 : Reach 43391 := rs (se 1 (by rfl) ⟨32543, by rfl⟩) R65087
theorem R174473 : Reach 174473 := rs (se 2 (by rfl) ⟨65427, by rfl⟩) R130855
theorem R43433 : Reach 43433 := rs (se 2 (by rfl) ⟨16287, by rfl⟩) R32575
theorem R76247 : Reach 76247 := rs (se 1 (by rfl) ⟨57185, by rfl⟩) R114371
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) R58195
theorem R45031 : Reach 45031 := rs (se 1 (by rfl) ⟨33773, by rfl⟩) R67547
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R78191 : Reach 78191 := rs (se 1 (by rfl) ⟨58643, by rfl⟩) R117287
theorem R45503 : Reach 45503 := rs (se 1 (by rfl) ⟨34127, by rfl⟩) R68255
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R79271 : Reach 79271 := rs (se 1 (by rfl) ⟨59453, by rfl⟩) R118907
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) R50495
theorem R47807 : Reach 47807 := rs (se 1 (by rfl) ⟨35855, by rfl⟩) R71711
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R48095 : Reach 48095 := rs (se 1 (by rfl) ⟨36071, by rfl⟩) R72143
theorem R48107 : Reach 48107 := rs (se 1 (by rfl) ⟨36080, by rfl⟩) R72161
theorem R113723 : Reach 113723 := rs (se 1 (by rfl) ⟨85292, by rfl⟩) R170585
theorem R442867 : Reach 442867 := rs (se 1 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R115343 : Reach 115343 := rs (se 1 (by rfl) ⟨86507, by rfl⟩) R173015
theorem R50003 : Reach 50003 := rs (se 1 (by rfl) ⟨37502, by rfl⟩) R75005
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R50665 : Reach 50665 := rs (se 2 (by rfl) ⟨18999, by rfl⟩) R37999
theorem R50843 : Reach 50843 := rs (se 1 (by rfl) ⟨38132, by rfl⟩) R76265
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R51947 : Reach 51947 := rs (se 1 (by rfl) ⟨38960, by rfl⟩) R77921
theorem R84959 : Reach 84959 := rs (se 1 (by rfl) ⟨63719, by rfl⟩) R127439
theorem R52361 : Reach 52361 := rs (se 2 (by rfl) ⟨19635, by rfl⟩) R39271
theorem R52415 : Reach 52415 := rs (se 1 (by rfl) ⟨39311, by rfl⟩) R78623
theorem R52703 : Reach 52703 := rs (se 1 (by rfl) ⟨39527, by rfl⟩) R79055
theorem R52865 : Reach 52865 := rs (se 2 (by rfl) ⟨19824, by rfl⟩) R39649
theorem R20127 : Reach 20127 := rs (se 1 (by rfl) ⟨15095, by rfl⟩) R30191
theorem R20207 : Reach 20207 := rs (se 1 (by rfl) ⟨15155, by rfl⟩) R30311
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R20511 : Reach 20511 := rs (se 1 (by rfl) ⟨15383, by rfl⟩) R30767
theorem R20591 : Reach 20591 := rs (se 1 (by rfl) ⟨15443, by rfl⟩) R30887
theorem R20687 : Reach 20687 := rs (se 1 (by rfl) ⟨15515, by rfl⟩) R31031
theorem R20807 : Reach 20807 := rs (se 1 (by rfl) ⟨15605, by rfl⟩) R31211
theorem R21039 : Reach 21039 := rs (se 1 (by rfl) ⟨15779, by rfl⟩) R31559
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R21595 : Reach 21595 := rs (se 1 (by rfl) ⟨16196, by rfl⟩) R32393
theorem R21615 : Reach 21615 := rs (se 1 (by rfl) ⟨16211, by rfl⟩) R32423
theorem R21695 : Reach 21695 := rs (se 1 (by rfl) ⟨16271, by rfl⟩) R32543
theorem R21735 : Reach 21735 := rs (se 1 (by rfl) ⟨16301, by rfl⟩) R32603
theorem R22015 : Reach 22015 := rs (se 1 (by rfl) ⟨16511, by rfl⟩) R33023
theorem R22119 : Reach 22119 := rs (se 1 (by rfl) ⟨16589, by rfl⟩) R33179
theorem R87905 : Reach 87905 := rs (se 2 (by rfl) ⟨32964, by rfl⟩) R65929
theorem R22495 : Reach 22495 := rs (se 1 (by rfl) ⟨16871, by rfl⟩) R33743
theorem R88073 : Reach 88073 := rs (se 2 (by rfl) ⟨33027, by rfl⟩) R66055
theorem R22555 : Reach 22555 := rs (se 1 (by rfl) ⟨16916, by rfl⟩) R33833
theorem R22575 : Reach 22575 := rs (se 1 (by rfl) ⟨16931, by rfl⟩) R33863
theorem R22695 : Reach 22695 := rs (se 1 (by rfl) ⟨17021, by rfl⟩) R34043
theorem R22863 : Reach 22863 := rs (se 1 (by rfl) ⟨17147, by rfl⟩) R34295
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R23143 : Reach 23143 := rs (se 1 (by rfl) ⟨17357, by rfl⟩) R34715
theorem R285767 : Reach 285767 := rs (se 1 (by rfl) ⟨214325, by rfl⟩) R428651
theorem R23647 : Reach 23647 := rs (se 1 (by rfl) ⟨17735, by rfl⟩) R35471
theorem R155033 : Reach 155033 := rs (se 2 (by rfl) ⟨58137, by rfl⟩) R116275
theorem R57935 : Reach 57935 := rs (se 1 (by rfl) ⟨43451, by rfl⟩) R86903
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) R34715
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R290735 : Reach 290735 := rs (se 1 (by rfl) ⟨218051, by rfl⟩) R436103
theorem R160379 : Reach 160379 := rs (se 1 (by rfl) ⟨120284, by rfl⟩) R240569
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R30575 : Reach 30575 := rs (se 1 (by rfl) ⟨22931, by rfl⟩) R45863
theorem R30587 : Reach 30587 := rs (se 1 (by rfl) ⟨22940, by rfl⟩) R45881
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R30827 : Reach 30827 := rs (se 1 (by rfl) ⟨23120, by rfl⟩) R46241
theorem R31007 : Reach 31007 := rs (se 1 (by rfl) ⟨23255, by rfl⟩) R46511
theorem R31079 : Reach 31079 := rs (se 1 (by rfl) ⟨23309, by rfl⟩) R46619
theorem R31145 : Reach 31145 := rs (se 2 (by rfl) ⟨11679, by rfl⟩) R23359
theorem R31199 : Reach 31199 := rs (se 1 (by rfl) ⟨23399, by rfl⟩) R46799
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R31727 : Reach 31727 := rs (se 1 (by rfl) ⟨23795, by rfl⟩) R47591
theorem R162809 : Reach 162809 := rs (se 2 (by rfl) ⟨61053, by rfl⟩) R122107
theorem R31913 : Reach 31913 := rs (se 2 (by rfl) ⟨11967, by rfl⟩) R23935
theorem R64745 : Reach 64745 := rs (se 2 (by rfl) ⟨24279, by rfl⟩) R48559
theorem R33335 : Reach 33335 := rs (se 1 (by rfl) ⟨25001, by rfl⟩) R50003
theorem R590489 : Reach 590489 := rs (se 2 (by rfl) ⟨221433, by rfl⟩) R442867
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R33895 : Reach 33895 := rs (se 1 (by rfl) ⟨25421, by rfl⟩) R50843
theorem R1180979 : Reach 1180979 := rs (se 1 (by rfl) ⟨885734, by rfl⟩) R1771469
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R34631 : Reach 34631 := rs (se 1 (by rfl) ⟨25973, by rfl⟩) R51947
theorem R67553 : Reach 67553 := rs (se 2 (by rfl) ⟨25332, by rfl⟩) R50665
theorem R34907 : Reach 34907 := rs (se 1 (by rfl) ⟨26180, by rfl⟩) R52361
theorem R34943 : Reach 34943 := rs (se 1 (by rfl) ⟨26207, by rfl⟩) R52415
theorem R35135 : Reach 35135 := rs (se 1 (by rfl) ⟨26351, by rfl⟩) R52703
theorem R35243 : Reach 35243 := rs (se 1 (by rfl) ⟨26432, by rfl⟩) R52865
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) R62375
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R103355 : Reach 103355 := rs (se 1 (by rfl) ⟨77516, by rfl⟩) R155033
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R38623 : Reach 38623 := rs (se 1 (by rfl) ⟨28967, by rfl⟩) R57935
theorem R71495 : Reach 71495 := rs (se 1 (by rfl) ⟨53621, by rfl⟩) R107243
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R71819 : Reach 71819 := rs (se 1 (by rfl) ⟨53864, by rfl⟩) R107729
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R826685 : Reach 826685 := rs (se 3 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R106919 : Reach 106919 := rs (se 1 (by rfl) ⟨80189, by rfl⟩) R160379
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R108539 : Reach 108539 := rs (se 1 (by rfl) ⟨81404, by rfl⟩) R162809
theorem R75815 : Reach 75815 := rs (se 1 (by rfl) ⟨56861, by rfl⟩) R113723
theorem R43163 : Reach 43163 := rs (se 1 (by rfl) ⟨32372, by rfl⟩) R64745
theorem R76895 : Reach 76895 := rs (se 1 (by rfl) ⟨57671, by rfl⟩) R115343
theorem R44219 : Reach 44219 := rs (se 1 (by rfl) ⟨33164, by rfl⟩) R66329
theorem R45535 : Reach 45535 := rs (se 1 (by rfl) ⟨34151, by rfl⟩) R68303
theorem R111131 : Reach 111131 := rs (se 1 (by rfl) ⟨83348, by rfl⟩) R166697
theorem R46015 : Reach 46015 := rs (se 1 (by rfl) ⟨34511, by rfl⟩) R69023
theorem R46457 : Reach 46457 := rs (se 2 (by rfl) ⟨17421, by rfl⟩) R34843
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R46747 : Reach 46747 := rs (se 1 (by rfl) ⟨35060, by rfl⟩) R70121
theorem R46919 : Reach 46919 := rs (se 1 (by rfl) ⟨35189, by rfl⟩) R70379
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R47159 : Reach 47159 := rs (se 1 (by rfl) ⟨35369, by rfl⟩) R70739
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R47231 : Reach 47231 := rs (se 1 (by rfl) ⟨35423, by rfl⟩) R70847
theorem R47927 : Reach 47927 := rs (se 1 (by rfl) ⟨35945, by rfl⟩) R71891
theorem R48455 : Reach 48455 := rs (se 1 (by rfl) ⟨36341, by rfl⟩) R72683
theorem R48959 : Reach 48959 := rs (se 1 (by rfl) ⟨36719, by rfl⟩) R73439
theorem R49463 : Reach 49463 := rs (se 1 (by rfl) ⟨37097, by rfl⟩) R74195
theorem R50399 : Reach 50399 := rs (se 1 (by rfl) ⟨37799, by rfl⟩) R75599
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R116315 : Reach 116315 := rs (se 1 (by rfl) ⟨87236, by rfl⟩) R174473
theorem R50831 : Reach 50831 := rs (se 1 (by rfl) ⟨38123, by rfl⟩) R76247
theorem R84199 : Reach 84199 := rs (se 1 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R52127 : Reach 52127 := rs (se 1 (by rfl) ⟨39095, by rfl⟩) R78191
theorem R52847 : Reach 52847 := rs (se 1 (by rfl) ⟨39635, by rfl⟩) R79271
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R20383 : Reach 20383 := rs (se 1 (by rfl) ⟨15287, by rfl⟩) R30575
theorem R20391 : Reach 20391 := rs (se 1 (by rfl) ⟨15293, by rfl⟩) R30587
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R20551 : Reach 20551 := rs (se 1 (by rfl) ⟨15413, by rfl⟩) R30827
theorem R20671 : Reach 20671 := rs (se 1 (by rfl) ⟨15503, by rfl⟩) R31007
theorem R20719 : Reach 20719 := rs (se 1 (by rfl) ⟨15539, by rfl⟩) R31079
theorem R20763 : Reach 20763 := rs (se 1 (by rfl) ⟨15572, by rfl⟩) R31145
theorem R20799 : Reach 20799 := rs (se 1 (by rfl) ⟨15599, by rfl⟩) R31199
theorem R184801 : Reach 184801 := rs (se 2 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R53885 : Reach 53885 := rs (se 3 (by rfl) ⟨10103, by rfl⟩) R20207
theorem R21151 : Reach 21151 := rs (se 1 (by rfl) ⟨15863, by rfl⟩) R31727
theorem R21275 : Reach 21275 := rs (se 1 (by rfl) ⟨15956, by rfl⟩) R31913
theorem R54553 : Reach 54553 := rs (se 2 (by rfl) ⟨20457, by rfl⟩) R40915
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R22767 : Reach 22767 := rs (se 1 (by rfl) ⟨17075, by rfl⟩) R34151
theorem R22847 : Reach 22847 := rs (se 1 (by rfl) ⟨17135, by rfl⟩) R34271
theorem R23023 : Reach 23023 := rs (se 1 (by rfl) ⟨17267, by rfl⟩) R34535
theorem R23259 : Reach 23259 := rs (se 1 (by rfl) ⟨17444, by rfl⟩) R34889
theorem R56639 : Reach 56639 := rs (se 1 (by rfl) ⟨42479, by rfl⟩) R84959
theorem R24043 : Reach 24043 := rs (se 1 (by rfl) ⟨18032, by rfl⟩) R36065
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R57307 : Reach 57307 := rs (se 1 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R25447 : Reach 25447 := rs (se 1 (by rfl) ⟨19085, by rfl⟩) R38171
theorem R58603 : Reach 58603 := rs (se 1 (by rfl) ⟨43952, by rfl⟩) R87905
theorem R58715 : Reach 58715 := rs (se 1 (by rfl) ⟨44036, by rfl⟩) R88073
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R190511 : Reach 190511 := rs (se 1 (by rfl) ⟨142883, by rfl⟩) R285767
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) R45031
theorem R27631 : Reach 27631 := rs (se 1 (by rfl) ⟨20723, by rfl⟩) R41447
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R94247 : Reach 94247 := rs (se 1 (by rfl) ⟨70685, by rfl⟩) R141371
theorem R28927 : Reach 28927 := rs (se 1 (by rfl) ⟨21695, by rfl⟩) R43391
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R28955 : Reach 28955 := rs (se 1 (by rfl) ⟨21716, by rfl⟩) R43433
theorem R193823 : Reach 193823 := rs (se 1 (by rfl) ⟨145367, by rfl⟩) R290735
theorem R30335 : Reach 30335 := rs (se 1 (by rfl) ⟨22751, by rfl⟩) R45503
theorem R30857 : Reach 30857 := rs (se 2 (by rfl) ⟨11571, by rfl⟩) R23143
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R31529 : Reach 31529 := rs (se 2 (by rfl) ⟨11823, by rfl⟩) R23647
theorem R31871 : Reach 31871 := rs (se 1 (by rfl) ⟨23903, by rfl⟩) R47807
theorem R32063 : Reach 32063 := rs (se 1 (by rfl) ⟨24047, by rfl⟩) R48095
theorem R32071 : Reach 32071 := rs (se 1 (by rfl) ⟨24053, by rfl⟩) R48107
theorem R32975 : Reach 32975 := rs (se 1 (by rfl) ⟨24731, by rfl⟩) R49463
theorem R393659 : Reach 393659 := rs (se 1 (by rfl) ⟨295244, by rfl⟩) R590489
theorem R33599 : Reach 33599 := rs (se 1 (by rfl) ⟨25199, by rfl⟩) R50399
theorem R787319 : Reach 787319 := rs (se 1 (by rfl) ⟨590489, by rfl⟩) R1180979
theorem R33887 : Reach 33887 := rs (se 1 (by rfl) ⟨25415, by rfl⟩) R50831
theorem R33929 : Reach 33929 := rs (se 2 (by rfl) ⟨12723, by rfl⟩) R25447
theorem R34751 : Reach 34751 := rs (se 1 (by rfl) ⟨26063, by rfl⟩) R52127
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) R50743
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R35231 : Reach 35231 := rs (se 1 (by rfl) ⟨26423, by rfl⟩) R52847
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R35923 : Reach 35923 := rs (se 1 (by rfl) ⟨26942, by rfl⟩) R53885
theorem R68903 : Reach 68903 := rs (se 1 (by rfl) ⟨51677, by rfl⟩) R103355
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R36841 : Reach 36841 := rs (se 2 (by rfl) ⟨13815, by rfl⟩) R27631
theorem R36895 : Reach 36895 := rs (se 1 (by rfl) ⟨27671, by rfl⟩) R55343
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R37759 : Reach 37759 := rs (se 1 (by rfl) ⟨28319, by rfl⟩) R56639
theorem R71279 : Reach 71279 := rs (se 1 (by rfl) ⟨53459, by rfl⟩) R106919
theorem R38569 : Reach 38569 := rs (se 2 (by rfl) ⟨14463, by rfl⟩) R28927
theorem R39143 : Reach 39143 := rs (se 1 (by rfl) ⟨29357, by rfl⟩) R58715
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R72359 : Reach 72359 := rs (se 1 (by rfl) ⟨54269, by rfl⟩) R108539
theorem R72737 : Reach 72737 := rs (se 2 (by rfl) ⟨27276, by rfl⟩) R54553
theorem R40027 : Reach 40027 := rs (se 1 (by rfl) ⟨30020, by rfl⟩) R60041
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R41143 : Reach 41143 := rs (se 1 (by rfl) ⟨30857, by rfl⟩) R61715
theorem R74087 : Reach 74087 := rs (se 1 (by rfl) ⟨55565, by rfl⟩) R111131
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R42761 : Reach 42761 := rs (se 2 (by rfl) ⟨16035, by rfl⟩) R32071
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R76409 : Reach 76409 := rs (se 2 (by rfl) ⟨28653, by rfl⟩) R57307
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) R28955
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R77543 : Reach 77543 := rs (se 1 (by rfl) ⟨58157, by rfl⟩) R116315
theorem R45035 : Reach 45035 := rs (se 1 (by rfl) ⟨33776, by rfl⟩) R67553
theorem R45193 : Reach 45193 := rs (se 2 (by rfl) ⟨16947, by rfl⟩) R33895
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R78137 : Reach 78137 := rs (se 2 (by rfl) ⟨29301, by rfl⟩) R58603
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R112265 : Reach 112265 := rs (se 2 (by rfl) ⟨42099, by rfl⟩) R84199
theorem R47663 : Reach 47663 := rs (se 1 (by rfl) ⟨35747, by rfl⟩) R71495
theorem R47879 : Reach 47879 := rs (se 1 (by rfl) ⟨35909, by rfl⟩) R71819
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) R46015
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R246401 : Reach 246401 := rs (se 2 (by rfl) ⟨92400, by rfl⟩) R184801
theorem R50543 : Reach 50543 := rs (se 1 (by rfl) ⟨37907, by rfl⟩) R75815
theorem R51263 : Reach 51263 := rs (se 1 (by rfl) ⟨38447, by rfl⟩) R76895
theorem R51497 : Reach 51497 := rs (se 2 (by rfl) ⟨19311, by rfl⟩) R38623
theorem R84989 : Reach 84989 := rs (se 3 (by rfl) ⟨15935, by rfl⟩) R31871
theorem R249317 : Reach 249317 := rs (se 4 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R20223 : Reach 20223 := rs (se 1 (by rfl) ⟨15167, by rfl⟩) R30335
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R20571 : Reach 20571 := rs (se 1 (by rfl) ⟨15428, by rfl⟩) R30857
theorem R21019 : Reach 21019 := rs (se 1 (by rfl) ⟨15764, by rfl⟩) R31529
theorem R21247 : Reach 21247 := rs (se 1 (by rfl) ⟨15935, by rfl⟩) R31871
theorem R21375 : Reach 21375 := rs (se 1 (by rfl) ⟨16031, by rfl⟩) R32063
theorem R22223 : Reach 22223 := rs (se 1 (by rfl) ⟨16667, by rfl⟩) R33335
theorem R23087 : Reach 23087 := rs (se 1 (by rfl) ⟨17315, by rfl⟩) R34631
theorem R23271 : Reach 23271 := rs (se 1 (by rfl) ⟨17453, by rfl⟩) R34907
theorem R23295 : Reach 23295 := rs (se 1 (by rfl) ⟨17471, by rfl⟩) R34943
theorem R23423 : Reach 23423 := rs (se 1 (by rfl) ⟨17567, by rfl⟩) R35135
theorem R23495 : Reach 23495 := rs (se 1 (by rfl) ⟨17621, by rfl⟩) R35243
theorem R57287 : Reach 57287 := rs (se 1 (by rfl) ⟨42965, by rfl⟩) R85931
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R551123 : Reach 551123 := rs (se 1 (by rfl) ⟨413342, by rfl⟩) R826685
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R60713 : Reach 60713 := rs (se 2 (by rfl) ⟨22767, by rfl⟩) R45535
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R127007 : Reach 127007 := rs (se 1 (by rfl) ⟨95255, by rfl⟩) R190511
theorem R28775 : Reach 28775 := rs (se 1 (by rfl) ⟨21581, by rfl⟩) R43163
theorem R29479 : Reach 29479 := rs (se 1 (by rfl) ⟨22109, by rfl⟩) R44219
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R62831 : Reach 62831 := rs (se 1 (by rfl) ⟨47123, by rfl⟩) R94247
theorem R129215 : Reach 129215 := rs (se 1 (by rfl) ⟨96911, by rfl⟩) R193823
theorem R30971 : Reach 30971 := rs (se 1 (by rfl) ⟨23228, by rfl⟩) R46457
theorem R31279 : Reach 31279 := rs (se 1 (by rfl) ⟨23459, by rfl⟩) R46919
theorem R31439 : Reach 31439 := rs (se 1 (by rfl) ⟨23579, by rfl⟩) R47159
theorem R31487 : Reach 31487 := rs (se 1 (by rfl) ⟨23615, by rfl⟩) R47231
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R31951 : Reach 31951 := rs (se 1 (by rfl) ⟨23963, by rfl⟩) R47927
theorem R32057 : Reach 32057 := rs (se 2 (by rfl) ⟨12021, by rfl⟩) R24043
theorem R32303 : Reach 32303 := rs (se 1 (by rfl) ⟨24227, by rfl⟩) R48455
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R32639 : Reach 32639 := rs (se 1 (by rfl) ⟨24479, by rfl⟩) R48959
theorem R262439 : Reach 262439 := rs (se 1 (by rfl) ⟨196829, by rfl⟩) R393659
theorem R164267 : Reach 164267 := rs (se 1 (by rfl) ⟨123200, by rfl⟩) R246401
theorem R524879 : Reach 524879 := rs (se 1 (by rfl) ⟨393659, by rfl⟩) R787319
theorem R33695 : Reach 33695 := rs (se 1 (by rfl) ⟨25271, by rfl⟩) R50543
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R34175 : Reach 34175 := rs (se 1 (by rfl) ⟨25631, by rfl⟩) R51263
theorem R34331 : Reach 34331 := rs (se 1 (by rfl) ⟨25748, by rfl⟩) R51497
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R166211 : Reach 166211 := rs (se 1 (by rfl) ⟨124658, by rfl⟩) R249317
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R38191 : Reach 38191 := rs (se 1 (by rfl) ⟨28643, by rfl⟩) R57287
theorem R39305 : Reach 39305 := rs (se 2 (by rfl) ⟨14739, by rfl⟩) R29479
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R367415 : Reach 367415 := rs (se 1 (by rfl) ⟨275561, by rfl⟩) R551123
theorem R40475 : Reach 40475 := rs (se 1 (by rfl) ⟨30356, by rfl⟩) R60713
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R41705 : Reach 41705 := rs (se 2 (by rfl) ⟨15639, by rfl⟩) R31279
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R41887 : Reach 41887 := rs (se 1 (by rfl) ⟨31415, by rfl⟩) R62831
theorem R74843 : Reach 74843 := rs (se 1 (by rfl) ⟨56132, by rfl⟩) R112265
theorem R42601 : Reach 42601 := rs (se 2 (by rfl) ⟨15975, by rfl⟩) R31951
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R76733 : Reach 76733 := rs (se 3 (by rfl) ⟨14387, by rfl⟩) R28775
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R45935 : Reach 45935 := rs (se 1 (by rfl) ⟨34451, by rfl⟩) R68903
theorem R47519 : Reach 47519 := rs (se 1 (by rfl) ⟨35639, by rfl⟩) R71279
theorem R47897 : Reach 47897 := rs (se 2 (by rfl) ⟨17961, by rfl⟩) R35923
theorem R48239 : Reach 48239 := rs (se 1 (by rfl) ⟨36179, by rfl⟩) R72359
theorem R48491 : Reach 48491 := rs (se 1 (by rfl) ⟨36368, by rfl⟩) R72737
theorem R49121 : Reach 49121 := rs (se 2 (by rfl) ⟨18420, by rfl⟩) R36841
theorem R49193 : Reach 49193 := rs (se 2 (by rfl) ⟨18447, by rfl⟩) R36895
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R49391 : Reach 49391 := rs (se 1 (by rfl) ⟨37043, by rfl⟩) R74087
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R50345 : Reach 50345 := rs (se 2 (by rfl) ⟨18879, by rfl⟩) R37759
theorem R50939 : Reach 50939 := rs (se 1 (by rfl) ⟨38204, by rfl⟩) R76409
theorem R51425 : Reach 51425 := rs (se 2 (by rfl) ⟨19284, by rfl⟩) R38569
theorem R51475 : Reach 51475 := rs (se 1 (by rfl) ⟨38606, by rfl⟩) R77213
theorem R51695 : Reach 51695 := rs (se 1 (by rfl) ⟨38771, by rfl⟩) R77543
theorem R84671 : Reach 84671 := rs (se 1 (by rfl) ⟨63503, by rfl⟩) R127007
theorem R52091 : Reach 52091 := rs (se 1 (by rfl) ⟨39068, by rfl⟩) R78137
theorem R53369 : Reach 53369 := rs (se 2 (by rfl) ⟨20013, by rfl⟩) R40027
theorem R86143 : Reach 86143 := rs (se 1 (by rfl) ⟨64607, by rfl⟩) R129215
theorem R20647 : Reach 20647 := rs (se 1 (by rfl) ⟨15485, by rfl⟩) R30971
theorem R20959 : Reach 20959 := rs (se 1 (by rfl) ⟨15719, by rfl⟩) R31439
theorem R20991 : Reach 20991 := rs (se 1 (by rfl) ⟨15743, by rfl⟩) R31487
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R21371 : Reach 21371 := rs (se 1 (by rfl) ⟨16028, by rfl⟩) R32057
theorem R21535 : Reach 21535 := rs (se 1 (by rfl) ⟨16151, by rfl⟩) R32303
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R21759 : Reach 21759 := rs (se 1 (by rfl) ⟨16319, by rfl⟩) R32639
theorem R21983 : Reach 21983 := rs (se 1 (by rfl) ⟨16487, by rfl⟩) R32975
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) R41143
theorem R22399 : Reach 22399 := rs (se 1 (by rfl) ⟨16799, by rfl⟩) R33599
theorem R22591 : Reach 22591 := rs (se 1 (by rfl) ⟨16943, by rfl⟩) R33887
theorem R22619 : Reach 22619 := rs (se 1 (by rfl) ⟨16964, by rfl⟩) R33929
theorem R23167 : Reach 23167 := rs (se 1 (by rfl) ⟨17375, by rfl⟩) R34751
theorem R285403 : Reach 285403 := rs (se 1 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R23487 : Reach 23487 := rs (se 1 (by rfl) ⟨17615, by rfl⟩) R35231
theorem R56659 : Reach 56659 := rs (se 1 (by rfl) ⟨42494, by rfl⟩) R84989
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R26095 : Reach 26095 := rs (se 1 (by rfl) ⟨19571, by rfl⟩) R39143
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) R68971
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R60257 : Reach 60257 := rs (se 2 (by rfl) ⟨22596, by rfl⟩) R45193
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R28507 : Reach 28507 := rs (se 1 (by rfl) ⟨21380, by rfl⟩) R42761
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R30023 : Reach 30023 := rs (se 1 (by rfl) ⟨22517, by rfl⟩) R45035
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R31775 : Reach 31775 := rs (se 1 (by rfl) ⟨23831, by rfl⟩) R47663
theorem R31919 : Reach 31919 := rs (se 1 (by rfl) ⟨23939, by rfl⟩) R47879
theorem R32795 : Reach 32795 := rs (se 1 (by rfl) ⟨24596, by rfl⟩) R49193
theorem R32927 : Reach 32927 := rs (se 1 (by rfl) ⟨24695, by rfl⟩) R49391
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R33563 : Reach 33563 := rs (se 1 (by rfl) ⟨25172, by rfl⟩) R50345
theorem R33959 : Reach 33959 := rs (se 1 (by rfl) ⟨25469, by rfl⟩) R50939
theorem R34283 : Reach 34283 := rs (se 1 (by rfl) ⟨25712, by rfl⟩) R51425
theorem R34463 : Reach 34463 := rs (se 1 (by rfl) ⟨25847, by rfl⟩) R51695
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R34727 : Reach 34727 := rs (se 1 (by rfl) ⟨26045, by rfl⟩) R52091
theorem R34793 : Reach 34793 := rs (se 2 (by rfl) ⟨13047, by rfl⟩) R26095
theorem R35579 : Reach 35579 := rs (se 1 (by rfl) ⟨26684, by rfl⟩) R53369
theorem R68633 : Reach 68633 := rs (se 2 (by rfl) ⟨25737, by rfl⟩) R51475
theorem R36571 : Reach 36571 := rs (se 1 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R38009 : Reach 38009 := rs (se 2 (by rfl) ⟨14253, by rfl⟩) R28507
theorem R104813 : Reach 104813 := rs (se 3 (by rfl) ⟨19652, by rfl⟩) R39305
theorem R40171 : Reach 40171 := rs (se 1 (by rfl) ⟨30128, by rfl⟩) R60257
theorem R75545 : Reach 75545 := rs (se 2 (by rfl) ⟨28329, by rfl⟩) R56659
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R174959 : Reach 174959 := rs (se 1 (by rfl) ⟨131219, by rfl⟩) R262439
theorem R109511 : Reach 109511 := rs (se 1 (by rfl) ⟨82133, by rfl⟩) R164267
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R110807 : Reach 110807 := rs (se 1 (by rfl) ⟨83105, by rfl⟩) R166211
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R244943 : Reach 244943 := rs (se 1 (by rfl) ⟨183707, by rfl⟩) R367415
theorem R114857 : Reach 114857 := rs (se 2 (by rfl) ⟨43071, by rfl⟩) R86143
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R49895 : Reach 49895 := rs (se 1 (by rfl) ⟨37421, by rfl⟩) R74843
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R50921 : Reach 50921 := rs (se 2 (by rfl) ⟨19095, by rfl⟩) R38191
theorem R51155 : Reach 51155 := rs (se 1 (by rfl) ⟨38366, by rfl⟩) R76733
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R20015 : Reach 20015 := rs (se 1 (by rfl) ⟨15011, by rfl⟩) R30023
theorem R380537 : Reach 380537 := rs (se 2 (by rfl) ⟨142701, by rfl⟩) R285403
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R21183 : Reach 21183 := rs (se 1 (by rfl) ⟨15887, by rfl⟩) R31775
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R21279 : Reach 21279 := rs (se 1 (by rfl) ⟨15959, by rfl⟩) R31919
theorem R349919 : Reach 349919 := rs (se 1 (by rfl) ⟨262439, by rfl⟩) R524879
theorem R22463 : Reach 22463 := rs (se 1 (by rfl) ⟨16847, by rfl⟩) R33695
theorem R22783 : Reach 22783 := rs (se 1 (by rfl) ⟨17087, by rfl⟩) R34175
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R22887 : Reach 22887 := rs (se 1 (by rfl) ⟨17165, by rfl⟩) R34331
theorem R55849 : Reach 55849 := rs (se 2 (by rfl) ⟨20943, by rfl⟩) R41887
theorem R56447 : Reach 56447 := rs (se 1 (by rfl) ⟨42335, by rfl⟩) R84671
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) R42601
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R189175 : Reach 189175 := rs (se 1 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R26203 : Reach 26203 := rs (se 1 (by rfl) ⟨19652, by rfl⟩) R39305
theorem R91975 : Reach 91975 := rs (se 1 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R26983 : Reach 26983 := rs (se 1 (by rfl) ⟨20237, by rfl⟩) R40475
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R27803 : Reach 27803 := rs (se 1 (by rfl) ⟨20852, by rfl⟩) R41705
theorem R61307 : Reach 61307 := rs (se 1 (by rfl) ⟨45980, by rfl⟩) R91961
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R30623 : Reach 30623 := rs (se 1 (by rfl) ⟨22967, by rfl⟩) R45935
theorem R31679 : Reach 31679 := rs (se 1 (by rfl) ⟨23759, by rfl⟩) R47519
theorem R31931 : Reach 31931 := rs (se 1 (by rfl) ⟨23948, by rfl⟩) R47897
theorem R32159 : Reach 32159 := rs (se 1 (by rfl) ⟨24119, by rfl⟩) R48239
theorem R32327 : Reach 32327 := rs (se 1 (by rfl) ⟨24245, by rfl⟩) R48491
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R32747 : Reach 32747 := rs (se 1 (by rfl) ⟨24560, by rfl⟩) R49121
theorem R65711 : Reach 65711 := rs (se 1 (by rfl) ⟨49283, by rfl⟩) R98567
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R33263 : Reach 33263 := rs (se 1 (by rfl) ⟨24947, by rfl⟩) R49895
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R33947 : Reach 33947 := rs (se 1 (by rfl) ⟨25460, by rfl⟩) R50921
theorem R34103 : Reach 34103 := rs (se 1 (by rfl) ⟨25577, by rfl⟩) R51155
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R34937 : Reach 34937 := rs (se 2 (by rfl) ⟨13101, by rfl⟩) R26203
theorem R35977 : Reach 35977 := rs (se 2 (by rfl) ⟨13491, by rfl⟩) R26983
theorem R233279 : Reach 233279 := rs (se 1 (by rfl) ⟨174959, by rfl⟩) R349919
theorem R69875 : Reach 69875 := rs (se 1 (by rfl) ⟨52406, by rfl⟩) R104813
theorem R37631 : Reach 37631 := rs (se 1 (by rfl) ⟨28223, by rfl⟩) R56447
theorem R37867 : Reach 37867 := rs (se 1 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R73007 : Reach 73007 := rs (se 1 (by rfl) ⟨54755, by rfl⟩) R109511
theorem R40871 : Reach 40871 := rs (se 1 (by rfl) ⟨30653, by rfl⟩) R61307
theorem R73871 : Reach 73871 := rs (se 1 (by rfl) ⟨55403, by rfl⟩) R110807
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R74141 : Reach 74141 := rs (se 3 (by rfl) ⟨13901, by rfl⟩) R27803
theorem R74465 : Reach 74465 := rs (se 2 (by rfl) ⟨27924, by rfl⟩) R55849
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R76571 : Reach 76571 := rs (se 1 (by rfl) ⟨57428, by rfl⟩) R114857
theorem R110969 : Reach 110969 := rs (se 2 (by rfl) ⟨41613, by rfl⟩) R83227
theorem R45755 : Reach 45755 := rs (se 1 (by rfl) ⟨34316, by rfl⟩) R68633
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R48761 : Reach 48761 := rs (se 2 (by rfl) ⟨18285, by rfl⟩) R36571
theorem R82255 : Reach 82255 := rs (se 1 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R50363 : Reach 50363 := rs (se 1 (by rfl) ⟨37772, by rfl⟩) R75545
theorem R116639 : Reach 116639 := rs (se 1 (by rfl) ⟨87479, by rfl⟩) R174959
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R20415 : Reach 20415 := rs (se 1 (by rfl) ⟨15311, by rfl⟩) R30623
theorem R53561 : Reach 53561 := rs (se 2 (by rfl) ⟨20085, by rfl⟩) R40171
theorem R21119 : Reach 21119 := rs (se 1 (by rfl) ⟨15839, by rfl⟩) R31679
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R21287 : Reach 21287 := rs (se 1 (by rfl) ⟨15965, by rfl⟩) R31931
theorem R21439 : Reach 21439 := rs (se 1 (by rfl) ⟨16079, by rfl⟩) R32159
theorem R21551 : Reach 21551 := rs (se 1 (by rfl) ⟨16163, by rfl⟩) R32327
theorem R21831 : Reach 21831 := rs (se 1 (by rfl) ⟨16373, by rfl⟩) R32747
theorem R21863 : Reach 21863 := rs (se 1 (by rfl) ⟨16397, by rfl⟩) R32795
theorem R21951 : Reach 21951 := rs (se 1 (by rfl) ⟨16463, by rfl⟩) R32927
theorem R22375 : Reach 22375 := rs (se 1 (by rfl) ⟨16781, by rfl⟩) R33563
theorem R22639 : Reach 22639 := rs (se 1 (by rfl) ⟨16979, by rfl⟩) R33959
theorem R22855 : Reach 22855 := rs (se 1 (by rfl) ⟨17141, by rfl⟩) R34283
theorem R252233 : Reach 252233 := rs (se 2 (by rfl) ⟨94587, by rfl⟩) R189175
theorem R22975 : Reach 22975 := rs (se 1 (by rfl) ⟨17231, by rfl⟩) R34463
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R23151 : Reach 23151 := rs (se 1 (by rfl) ⟨17363, by rfl⟩) R34727
theorem R23195 : Reach 23195 := rs (se 1 (by rfl) ⟨17396, by rfl⟩) R34793
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R23719 : Reach 23719 := rs (se 1 (by rfl) ⟨17789, by rfl⟩) R35579
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R253691 : Reach 253691 := rs (se 1 (by rfl) ⟨190268, by rfl⟩) R380537
theorem R122633 : Reach 122633 := rs (se 2 (by rfl) ⟨45987, by rfl⟩) R91975
theorem R90557 : Reach 90557 := rs (se 3 (by rfl) ⟨16979, by rfl⟩) R33959
theorem R1237493 : Reach 1237493 := rs (se 5 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R25339 : Reach 25339 := rs (se 1 (by rfl) ⟨19004, by rfl⟩) R38009
theorem R60223 : Reach 60223 := rs (se 1 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R30377 : Reach 30377 := rs (se 2 (by rfl) ⟨11391, by rfl⟩) R22783
theorem R163295 : Reach 163295 := rs (se 1 (by rfl) ⟨122471, by rfl⟩) R244943
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) R74047
theorem R33575 : Reach 33575 := rs (se 1 (by rfl) ⟨25181, by rfl⟩) R50363
theorem R33785 : Reach 33785 := rs (se 2 (by rfl) ⟨12669, by rfl⟩) R25339
theorem R35707 : Reach 35707 := rs (se 1 (by rfl) ⟨26780, by rfl⟩) R53561
theorem R168155 : Reach 168155 := rs (se 1 (by rfl) ⟨126116, by rfl⟩) R252233
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R169127 : Reach 169127 := rs (se 1 (by rfl) ⟨126845, by rfl⟩) R253691
theorem R824995 : Reach 824995 := rs (se 1 (by rfl) ⟨618746, by rfl⟩) R1237493
theorem R73979 : Reach 73979 := rs (se 1 (by rfl) ⟨55484, by rfl⟩) R110969
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R108863 : Reach 108863 := rs (se 1 (by rfl) ⟨81647, by rfl⟩) R163295
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) R40871
theorem R43807 : Reach 43807 := rs (se 1 (by rfl) ⟨32855, by rfl⟩) R65711
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R109673 : Reach 109673 := rs (se 2 (by rfl) ⟨41127, by rfl⟩) R82255
theorem R77759 : Reach 77759 := rs (se 1 (by rfl) ⟨58319, by rfl⟩) R116639
theorem R46583 : Reach 46583 := rs (se 1 (by rfl) ⟨34937, by rfl⟩) R69875
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R80297 : Reach 80297 := rs (se 2 (by rfl) ⟨30111, by rfl⟩) R60223
theorem R47969 : Reach 47969 := rs (se 2 (by rfl) ⟨17988, by rfl⟩) R35977
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R48671 : Reach 48671 := rs (se 1 (by rfl) ⟨36503, by rfl⟩) R73007
theorem R81755 : Reach 81755 := rs (se 1 (by rfl) ⟨61316, by rfl⟩) R122633
theorem R49247 : Reach 49247 := rs (se 1 (by rfl) ⟨36935, by rfl⟩) R73871
theorem R49427 : Reach 49427 := rs (se 1 (by rfl) ⟨37070, by rfl⟩) R74141
theorem R49643 : Reach 49643 := rs (se 1 (by rfl) ⟨37232, by rfl⟩) R74465
theorem R50489 : Reach 50489 := rs (se 2 (by rfl) ⟨18933, by rfl⟩) R37867
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R51047 : Reach 51047 := rs (se 1 (by rfl) ⟨38285, by rfl⟩) R76571
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R20251 : Reach 20251 := rs (se 1 (by rfl) ⟨15188, by rfl⟩) R30377
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R22175 : Reach 22175 := rs (se 1 (by rfl) ⟨16631, by rfl⟩) R33263
theorem R22631 : Reach 22631 := rs (se 1 (by rfl) ⟨16973, by rfl⟩) R33947
theorem R22735 : Reach 22735 := rs (se 1 (by rfl) ⟨17051, by rfl⟩) R34103
theorem R23291 : Reach 23291 := rs (se 1 (by rfl) ⟨17468, by rfl⟩) R34937
theorem R155519 : Reach 155519 := rs (se 1 (by rfl) ⟨116639, by rfl⟩) R233279
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R57469 : Reach 57469 := rs (se 3 (by rfl) ⟨10775, by rfl⟩) R21551
theorem R25087 : Reach 25087 := rs (se 1 (by rfl) ⟨18815, by rfl⟩) R37631
theorem R60371 : Reach 60371 := rs (se 1 (by rfl) ⟨45278, by rfl⟩) R90557
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R30185 : Reach 30185 := rs (se 2 (by rfl) ⟨11319, by rfl⟩) R22639
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R30473 : Reach 30473 := rs (se 2 (by rfl) ⟨11427, by rfl⟩) R22855
theorem R30503 : Reach 30503 := rs (se 1 (by rfl) ⟨22877, by rfl⟩) R45755
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R31625 : Reach 31625 := rs (se 2 (by rfl) ⟨11859, by rfl⟩) R23719
theorem R32507 : Reach 32507 := rs (se 1 (by rfl) ⟨24380, by rfl⟩) R48761
theorem R32831 : Reach 32831 := rs (se 1 (by rfl) ⟨24623, by rfl⟩) R49247
theorem R32951 : Reach 32951 := rs (se 1 (by rfl) ⟨24713, by rfl⟩) R49427
theorem R65819 : Reach 65819 := rs (se 1 (by rfl) ⟨49364, by rfl⟩) R98729
theorem R33095 : Reach 33095 := rs (se 1 (by rfl) ⟨24821, by rfl⟩) R49643
theorem R33449 : Reach 33449 := rs (se 2 (by rfl) ⟨12543, by rfl⟩) R25087
theorem R33659 : Reach 33659 := rs (se 1 (by rfl) ⟨25244, by rfl⟩) R50489
theorem R34031 : Reach 34031 := rs (se 1 (by rfl) ⟨25523, by rfl⟩) R51047
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R103679 : Reach 103679 := rs (se 1 (by rfl) ⟨77759, by rfl⟩) R155519
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R72575 : Reach 72575 := rs (se 1 (by rfl) ⟨54431, by rfl⟩) R108863
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R40247 : Reach 40247 := rs (se 1 (by rfl) ⟨30185, by rfl⟩) R60371
theorem R73115 : Reach 73115 := rs (se 1 (by rfl) ⟨54836, by rfl⟩) R109673
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R76625 : Reach 76625 := rs (se 2 (by rfl) ⟨28734, by rfl⟩) R57469
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R112103 : Reach 112103 := rs (se 1 (by rfl) ⟨84077, by rfl⟩) R168155
theorem R112751 : Reach 112751 := rs (se 1 (by rfl) ⟨84563, by rfl⟩) R169127
theorem R47609 : Reach 47609 := rs (se 2 (by rfl) ⟨17853, by rfl⟩) R35707
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R49319 : Reach 49319 := rs (se 1 (by rfl) ⟨36989, by rfl⟩) R73979
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R1099993 : Reach 1099993 := rs (se 2 (by rfl) ⟨412497, by rfl⟩) R824995
theorem R51839 : Reach 51839 := rs (se 1 (by rfl) ⟨38879, by rfl⟩) R77759
theorem R20123 : Reach 20123 := rs (se 1 (by rfl) ⟨15092, by rfl⟩) R30185
theorem R20315 : Reach 20315 := rs (se 1 (by rfl) ⟨15236, by rfl⟩) R30473
theorem R53095 : Reach 53095 := rs (se 1 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R20335 : Reach 20335 := rs (se 1 (by rfl) ⟨15251, by rfl⟩) R30503
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R53531 : Reach 53531 := rs (se 1 (by rfl) ⟨40148, by rfl⟩) R80297
theorem R21083 : Reach 21083 := rs (se 1 (by rfl) ⟨15812, by rfl⟩) R31625
theorem R1299077 : Reach 1299077 := rs (se 4 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R21671 : Reach 21671 := rs (se 1 (by rfl) ⟨16253, by rfl⟩) R32507
theorem R54503 : Reach 54503 := rs (se 1 (by rfl) ⟨40877, by rfl⟩) R81755
theorem R22383 : Reach 22383 := rs (se 1 (by rfl) ⟨16787, by rfl⟩) R33575
theorem R22523 : Reach 22523 := rs (se 1 (by rfl) ⟨16892, by rfl⟩) R33785
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R58409 : Reach 58409 := rs (se 2 (by rfl) ⟨21903, by rfl⟩) R43807
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R31055 : Reach 31055 := rs (se 1 (by rfl) ⟨23291, by rfl⟩) R46583
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R31979 : Reach 31979 := rs (se 1 (by rfl) ⟨23984, by rfl⟩) R47969
theorem R32447 : Reach 32447 := rs (se 1 (by rfl) ⟨24335, by rfl⟩) R48671
theorem R32879 : Reach 32879 := rs (se 1 (by rfl) ⟨24659, by rfl⟩) R49319
theorem R34559 : Reach 34559 := rs (se 1 (by rfl) ⟨25919, by rfl⟩) R51839
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R35687 : Reach 35687 := rs (se 1 (by rfl) ⟨26765, by rfl⟩) R53531
theorem R36335 : Reach 36335 := rs (se 1 (by rfl) ⟨27251, by rfl⟩) R54503
theorem R69119 : Reach 69119 := rs (se 1 (by rfl) ⟨51839, by rfl⟩) R103679
theorem R70793 : Reach 70793 := rs (se 2 (by rfl) ⟨26547, by rfl⟩) R53095
theorem R38939 : Reach 38939 := rs (se 1 (by rfl) ⟨29204, by rfl⟩) R58409
theorem R39163 : Reach 39163 := rs (se 1 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R74735 : Reach 74735 := rs (se 1 (by rfl) ⟨56051, by rfl⟩) R112103
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R75167 : Reach 75167 := rs (se 1 (by rfl) ⟨56375, by rfl⟩) R112751
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) R65819
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R866051 : Reach 866051 := rs (se 1 (by rfl) ⟨649538, by rfl⟩) R1299077
theorem R48383 : Reach 48383 := rs (se 1 (by rfl) ⟨36287, by rfl⟩) R72575
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R48743 : Reach 48743 := rs (se 1 (by rfl) ⟨36557, by rfl⟩) R73115
theorem R51083 : Reach 51083 := rs (se 1 (by rfl) ⟨38312, by rfl⟩) R76625
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R20703 : Reach 20703 := rs (se 1 (by rfl) ⟨15527, by rfl⟩) R31055
theorem R21319 : Reach 21319 := rs (se 1 (by rfl) ⟨15989, by rfl⟩) R31979
theorem R21631 : Reach 21631 := rs (se 1 (by rfl) ⟨16223, by rfl⟩) R32447
theorem R21887 : Reach 21887 := rs (se 1 (by rfl) ⟨16415, by rfl⟩) R32831
theorem R21967 : Reach 21967 := rs (se 1 (by rfl) ⟨16475, by rfl⟩) R32951
theorem R22063 : Reach 22063 := rs (se 1 (by rfl) ⟨16547, by rfl⟩) R33095
theorem R22299 : Reach 22299 := rs (se 1 (by rfl) ⟨16724, by rfl⟩) R33449
theorem R22439 : Reach 22439 := rs (se 1 (by rfl) ⟨16829, by rfl⟩) R33659
theorem R22687 : Reach 22687 := rs (se 1 (by rfl) ⟨17015, by rfl⟩) R34031
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R1466657 : Reach 1466657 := rs (se 2 (by rfl) ⟨549996, by rfl⟩) R1099993
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R26831 : Reach 26831 := rs (se 1 (by rfl) ⟨20123, by rfl⟩) R40247
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R31739 : Reach 31739 := rs (se 1 (by rfl) ⟨23804, by rfl⟩) R47609
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R34055 : Reach 34055 := rs (se 1 (by rfl) ⟨25541, by rfl⟩) R51083
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) R38939
theorem R71549 : Reach 71549 := rs (se 3 (by rfl) ⟨13415, by rfl⟩) R26831
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R46079 : Reach 46079 := rs (se 1 (by rfl) ⟨34559, by rfl⟩) R69119
theorem R47195 : Reach 47195 := rs (se 1 (by rfl) ⟨35396, by rfl⟩) R70793
theorem R49823 : Reach 49823 := rs (se 1 (by rfl) ⟨37367, by rfl⟩) R74735
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R50111 : Reach 50111 := rs (se 1 (by rfl) ⟨37583, by rfl⟩) R75167
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R52217 : Reach 52217 := rs (se 2 (by rfl) ⟨19581, by rfl⟩) R39163
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R577367 : Reach 577367 := rs (se 1 (by rfl) ⟨433025, by rfl⟩) R866051
theorem R21159 : Reach 21159 := rs (se 1 (by rfl) ⟨15869, by rfl⟩) R31739
theorem R21919 : Reach 21919 := rs (se 1 (by rfl) ⟨16439, by rfl⟩) R32879
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R87677 : Reach 87677 := rs (se 3 (by rfl) ⟨16439, by rfl⟩) R32879
theorem R23039 : Reach 23039 := rs (se 1 (by rfl) ⟨17279, by rfl⟩) R34559
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R23791 : Reach 23791 := rs (se 1 (by rfl) ⟨17843, by rfl⟩) R35687
theorem R24223 : Reach 24223 := rs (se 1 (by rfl) ⟨18167, by rfl⟩) R36335
theorem R977771 : Reach 977771 := rs (se 1 (by rfl) ⟨733328, by rfl⟩) R1466657
theorem R224167 : Reach 224167 := rs (se 1 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R28841 : Reach 28841 := rs (se 2 (by rfl) ⟨10815, by rfl⟩) R21631
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) R48439
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R32255 : Reach 32255 := rs (se 1 (by rfl) ⟨24191, by rfl⟩) R48383
theorem R32495 : Reach 32495 := rs (se 1 (by rfl) ⟨24371, by rfl⟩) R48743
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R33215 : Reach 33215 := rs (se 1 (by rfl) ⟨24911, by rfl⟩) R49823
theorem R33407 : Reach 33407 := rs (se 1 (by rfl) ⟨25055, by rfl⟩) R50111
theorem R34811 : Reach 34811 := rs (se 1 (by rfl) ⟨26108, by rfl⟩) R52217
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R298889 : Reach 298889 := rs (se 2 (by rfl) ⟨112083, by rfl⟩) R224167
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R43679 : Reach 43679 := rs (se 1 (by rfl) ⟨32759, by rfl⟩) R65519
theorem R76909 : Reach 76909 := rs (se 3 (by rfl) ⟨14420, by rfl⟩) R28841
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R47699 : Reach 47699 := rs (se 1 (by rfl) ⟨35774, by rfl⟩) R71549
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R21503 : Reach 21503 := rs (se 1 (by rfl) ⟨16127, by rfl⟩) R32255
theorem R21663 : Reach 21663 := rs (se 1 (by rfl) ⟨16247, by rfl⟩) R32495
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R22703 : Reach 22703 := rs (se 1 (by rfl) ⟨17027, by rfl⟩) R34055
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R384911 : Reach 384911 := rs (se 1 (by rfl) ⟨288683, by rfl⟩) R577367
theorem R58451 : Reach 58451 := rs (se 1 (by rfl) ⟨43838, by rfl⟩) R87677
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R651847 : Reach 651847 := rs (se 1 (by rfl) ⟨488885, by rfl⟩) R977771
theorem R30719 : Reach 30719 := rs (se 1 (by rfl) ⟨23039, by rfl⟩) R46079
theorem R31463 : Reach 31463 := rs (se 1 (by rfl) ⟨23597, by rfl⟩) R47195
theorem R31721 : Reach 31721 := rs (se 2 (by rfl) ⟨11895, by rfl⟩) R23791
theorem R32297 : Reach 32297 := rs (se 2 (by rfl) ⟨12111, by rfl⟩) R24223
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) R58451
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R199259 : Reach 199259 := rs (se 1 (by rfl) ⟨149444, by rfl⟩) R298889
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R102545 : Reach 102545 := rs (se 2 (by rfl) ⟨38454, by rfl⟩) R76909
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R209405 : Reach 209405 := rs (se 3 (by rfl) ⟨39263, by rfl⟩) R78527
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R114817 : Reach 114817 := rs (se 2 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R869129 : Reach 869129 := rs (se 2 (by rfl) ⟨325923, by rfl⟩) R651847
theorem R116477 : Reach 116477 := rs (se 3 (by rfl) ⟨21839, by rfl⟩) R43679
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R20479 : Reach 20479 := rs (se 1 (by rfl) ⟨15359, by rfl⟩) R30719
theorem R20975 : Reach 20975 := rs (se 1 (by rfl) ⟨15731, by rfl⟩) R31463
theorem R21147 : Reach 21147 := rs (se 1 (by rfl) ⟨15860, by rfl⟩) R31721
theorem R21531 : Reach 21531 := rs (se 1 (by rfl) ⟨16148, by rfl⟩) R32297
theorem R22143 : Reach 22143 := rs (se 1 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R22271 : Reach 22271 := rs (se 1 (by rfl) ⟨16703, by rfl⟩) R33407
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R88573 : Reach 88573 := rs (se 3 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R23207 : Reach 23207 := rs (se 1 (by rfl) ⟨17405, by rfl⟩) R34811
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) R21503
theorem R354293 : Reach 354293 := rs (se 5 (by rfl) ⟨16607, by rfl⟩) R33215
theorem R92299 : Reach 92299 := rs (se 1 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R256607 : Reach 256607 := rs (se 1 (by rfl) ⟨192455, by rfl⟩) R384911
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R31799 : Reach 31799 := rs (se 1 (by rfl) ⟨23849, by rfl⟩) R47699
theorem R132839 : Reach 132839 := rs (se 1 (by rfl) ⟨99629, by rfl⟩) R199259
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R68363 : Reach 68363 := rs (se 1 (by rfl) ⟨51272, by rfl⟩) R102545
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R37543 : Reach 37543 := rs (se 1 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R38227 : Reach 38227 := rs (se 1 (by rfl) ⟨28670, by rfl⟩) R57341
theorem R236195 : Reach 236195 := rs (se 1 (by rfl) ⟨177146, by rfl⟩) R354293
theorem R171071 : Reach 171071 := rs (se 1 (by rfl) ⟨128303, by rfl⟩) R256607
theorem R139603 : Reach 139603 := rs (se 1 (by rfl) ⟨104702, by rfl⟩) R209405
theorem R74479 : Reach 74479 := rs (se 1 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R77651 : Reach 77651 := rs (se 1 (by rfl) ⟨58238, by rfl⟩) R116477
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R118097 : Reach 118097 := rs (se 2 (by rfl) ⟨44286, by rfl⟩) R88573
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R21199 : Reach 21199 := rs (se 1 (by rfl) ⟨15899, by rfl⟩) R31799
theorem R153089 : Reach 153089 := rs (se 2 (by rfl) ⟨57408, by rfl⟩) R114817
theorem R579419 : Reach 579419 := rs (se 1 (by rfl) ⟨434564, by rfl⟩) R869129
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R123065 : Reach 123065 := rs (se 2 (by rfl) ⟨46149, by rfl⟩) R92299
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R99305 : Reach 99305 := rs (se 2 (by rfl) ⟨37239, by rfl⟩) R74479
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R102059 : Reach 102059 := rs (se 1 (by rfl) ⟨76544, by rfl⟩) R153089
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R45575 : Reach 45575 := rs (se 1 (by rfl) ⟨34181, by rfl⟩) R68363
theorem R78731 : Reach 78731 := rs (se 1 (by rfl) ⟨59048, by rfl⟩) R118097
theorem R114047 : Reach 114047 := rs (se 1 (by rfl) ⟨85535, by rfl⟩) R171071
theorem R82043 : Reach 82043 := rs (se 1 (by rfl) ⟨61532, by rfl⟩) R123065
theorem R50057 : Reach 50057 := rs (se 2 (by rfl) ⟨18771, by rfl⟩) R37543
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R50969 : Reach 50969 := rs (se 2 (by rfl) ⟨19113, by rfl⟩) R38227
theorem R51767 : Reach 51767 := rs (se 1 (by rfl) ⟨38825, by rfl⟩) R77651
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R186137 : Reach 186137 := rs (se 2 (by rfl) ⟨69801, by rfl⟩) R139603
theorem R88559 : Reach 88559 := rs (se 1 (by rfl) ⟨66419, by rfl⟩) R132839
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R386279 : Reach 386279 := rs (se 1 (by rfl) ⟨289709, by rfl⟩) R579419
theorem R157463 : Reach 157463 := rs (se 1 (by rfl) ⟨118097, by rfl⟩) R236195
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R33371 : Reach 33371 := rs (se 1 (by rfl) ⟨25028, by rfl⟩) R50057
theorem R66203 : Reach 66203 := rs (se 1 (by rfl) ⟨49652, by rfl⟩) R99305
theorem R33979 : Reach 33979 := rs (se 1 (by rfl) ⟨25484, by rfl⟩) R50969
theorem R34511 : Reach 34511 := rs (se 1 (by rfl) ⟨25883, by rfl⟩) R51767
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R68039 : Reach 68039 := rs (se 1 (by rfl) ⟨51029, by rfl⟩) R102059
theorem R104975 : Reach 104975 := rs (se 1 (by rfl) ⟨78731, by rfl⟩) R157463
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R76031 : Reach 76031 := rs (se 1 (by rfl) ⟨57023, by rfl⟩) R114047
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R52487 : Reach 52487 := rs (se 1 (by rfl) ⟨39365, by rfl⟩) R78731
theorem R54695 : Reach 54695 := rs (se 1 (by rfl) ⟨41021, by rfl⟩) R82043
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R124091 : Reach 124091 := rs (se 1 (by rfl) ⟨93068, by rfl⟩) R186137
theorem R59039 : Reach 59039 := rs (se 1 (by rfl) ⟨44279, by rfl⟩) R88559
theorem R257519 : Reach 257519 := rs (se 1 (by rfl) ⟨193139, by rfl⟩) R386279
theorem R30383 : Reach 30383 := rs (se 1 (by rfl) ⟨22787, by rfl⟩) R45575
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R34991 : Reach 34991 := rs (se 1 (by rfl) ⟨26243, by rfl⟩) R52487
theorem R36463 : Reach 36463 := rs (se 1 (by rfl) ⟨27347, by rfl⟩) R54695
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R69983 : Reach 69983 := rs (se 1 (by rfl) ⟨52487, by rfl⟩) R104975
theorem R39359 : Reach 39359 := rs (se 1 (by rfl) ⟨29519, by rfl⟩) R59039
theorem R171679 : Reach 171679 := rs (se 1 (by rfl) ⟨128759, by rfl⟩) R257519
theorem R44135 : Reach 44135 := rs (se 1 (by rfl) ⟨33101, by rfl⟩) R66203
theorem R45305 : Reach 45305 := rs (se 2 (by rfl) ⟨16989, by rfl⟩) R33979
theorem R45359 : Reach 45359 := rs (se 1 (by rfl) ⟨34019, by rfl⟩) R68039
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R82727 : Reach 82727 := rs (se 1 (by rfl) ⟨62045, by rfl⟩) R124091
theorem R50687 : Reach 50687 := rs (se 1 (by rfl) ⟨38015, by rfl⟩) R76031
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R20255 : Reach 20255 := rs (se 1 (by rfl) ⟨15191, by rfl⟩) R30383
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R22247 : Reach 22247 := rs (se 1 (by rfl) ⟨16685, by rfl⟩) R33371
theorem R23007 : Reach 23007 := rs (se 1 (by rfl) ⟨17255, by rfl⟩) R34511
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R33791 : Reach 33791 := rs (se 1 (by rfl) ⟨25343, by rfl⟩) R50687
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R78367 : Reach 78367 := rs (se 1 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R46655 : Reach 46655 := rs (se 1 (by rfl) ⟨34991, by rfl⟩) R69983
theorem R245149 : Reach 245149 := rs (se 3 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R48617 : Reach 48617 := rs (se 2 (by rfl) ⟨18231, by rfl⟩) R36463
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R55151 : Reach 55151 := rs (se 1 (by rfl) ⟨41363, by rfl⟩) R82727
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R23327 : Reach 23327 := rs (se 1 (by rfl) ⟨17495, by rfl⟩) R34991
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R26239 : Reach 26239 := rs (se 1 (by rfl) ⟨19679, by rfl⟩) R39359
theorem R29423 : Reach 29423 := rs (se 1 (by rfl) ⟨22067, by rfl⟩) R44135
theorem R30203 : Reach 30203 := rs (se 1 (by rfl) ⟨22652, by rfl⟩) R45305
theorem R30239 : Reach 30239 := rs (se 1 (by rfl) ⟨22679, by rfl⟩) R45359
theorem R228905 : Reach 228905 := rs (se 2 (by rfl) ⟨85839, by rfl⟩) R171679
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R34985 : Reach 34985 := rs (se 2 (by rfl) ⟨13119, by rfl⟩) R26239
theorem R36767 : Reach 36767 := rs (se 1 (by rfl) ⟨27575, by rfl⟩) R55151
theorem R104489 : Reach 104489 := rs (se 2 (by rfl) ⟨39183, by rfl⟩) R78367
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R109471 : Reach 109471 := rs (se 1 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R78461 : Reach 78461 := rs (se 3 (by rfl) ⟨14711, by rfl⟩) R29423
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R20135 : Reach 20135 := rs (se 1 (by rfl) ⟨15101, by rfl⟩) R30203
theorem R20159 : Reach 20159 := rs (se 1 (by rfl) ⟨15119, by rfl⟩) R30239
theorem R152603 : Reach 152603 := rs (se 1 (by rfl) ⟨114452, by rfl⟩) R228905
theorem R22527 : Reach 22527 := rs (se 1 (by rfl) ⟨16895, by rfl⟩) R33791
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R58927 : Reach 58927 := rs (se 1 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R1307461 : Reach 1307461 := rs (se 4 (by rfl) ⟨122574, by rfl⟩) R245149
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R31103 : Reach 31103 := rs (se 1 (by rfl) ⟨23327, by rfl⟩) R46655
theorem R32411 : Reach 32411 := rs (se 1 (by rfl) ⟨24308, by rfl⟩) R48617
theorem R101735 : Reach 101735 := rs (se 1 (by rfl) ⟨76301, by rfl⟩) R152603
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R69659 : Reach 69659 := rs (se 1 (by rfl) ⟨52244, by rfl⟩) R104489
theorem R1743281 : Reach 1743281 := rs (se 2 (by rfl) ⟨653730, by rfl⟩) R1307461
theorem R78569 : Reach 78569 := rs (se 2 (by rfl) ⟨29463, by rfl⟩) R58927
theorem R145961 : Reach 145961 := rs (se 2 (by rfl) ⟨54735, by rfl⟩) R109471
theorem R52307 : Reach 52307 := rs (se 1 (by rfl) ⟨39230, by rfl⟩) R78461
theorem R20735 : Reach 20735 := rs (se 1 (by rfl) ⟨15551, by rfl⟩) R31103
theorem R53693 : Reach 53693 := rs (se 3 (by rfl) ⟨10067, by rfl⟩) R20135
theorem R21607 : Reach 21607 := rs (se 1 (by rfl) ⟨16205, by rfl⟩) R32411
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R55039 : Reach 55039 := rs (se 1 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R23323 : Reach 23323 := rs (se 1 (by rfl) ⟨17492, by rfl⟩) R34985
theorem R24511 : Reach 24511 := rs (se 1 (by rfl) ⟨18383, by rfl⟩) R36767
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) R46363
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R34871 : Reach 34871 := rs (se 1 (by rfl) ⟨26153, by rfl⟩) R52307
theorem R67823 : Reach 67823 := rs (se 1 (by rfl) ⟨50867, by rfl⟩) R101735
theorem R35795 : Reach 35795 := rs (se 1 (by rfl) ⟨26846, by rfl⟩) R53693
theorem R73385 : Reach 73385 := rs (se 2 (by rfl) ⟨27519, by rfl⟩) R55039
theorem R46439 : Reach 46439 := rs (se 1 (by rfl) ⟨34829, by rfl⟩) R69659
theorem R1162187 : Reach 1162187 := rs (se 1 (by rfl) ⟨871640, by rfl⟩) R1743281
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R52379 : Reach 52379 := rs (se 1 (by rfl) ⟨39284, by rfl⟩) R78569
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R31097 : Reach 31097 := rs (se 2 (by rfl) ⟨11661, by rfl⟩) R23323
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R97307 : Reach 97307 := rs (se 1 (by rfl) ⟨72980, by rfl⟩) R145961
theorem R32681 : Reach 32681 := rs (se 2 (by rfl) ⟨12255, by rfl⟩) R24511
theorem R34919 : Reach 34919 := rs (se 1 (by rfl) ⟨26189, by rfl⟩) R52379
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R45215 : Reach 45215 := rs (se 1 (by rfl) ⟨33911, by rfl⟩) R67823
theorem R48923 : Reach 48923 := rs (se 1 (by rfl) ⟨36692, by rfl⟩) R73385
theorem R20731 : Reach 20731 := rs (se 1 (by rfl) ⟨15548, by rfl⟩) R31097
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R774791 : Reach 774791 := rs (se 1 (by rfl) ⟨581093, by rfl⟩) R1162187
theorem R21787 : Reach 21787 := rs (se 1 (by rfl) ⟨16340, by rfl⟩) R32681
theorem R23247 : Reach 23247 := rs (se 1 (by rfl) ⟨17435, by rfl⟩) R34871
theorem R23863 : Reach 23863 := rs (se 1 (by rfl) ⟨17897, by rfl⟩) R35795
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R30959 : Reach 30959 := rs (se 1 (by rfl) ⟨23219, by rfl⟩) R46439
theorem R64871 : Reach 64871 := rs (se 1 (by rfl) ⟨48653, by rfl⟩) R97307
theorem R762533 : Reach 762533 := rs (se 4 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R43247 : Reach 43247 := rs (se 1 (by rfl) ⟨32435, by rfl⟩) R64871
theorem R113359 : Reach 113359 := rs (se 1 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R115433 : Reach 115433 := rs (se 2 (by rfl) ⟨43287, by rfl⟩) R86575
theorem R20639 : Reach 20639 := rs (se 1 (by rfl) ⟨15479, by rfl⟩) R30959
theorem R23279 : Reach 23279 := rs (se 1 (by rfl) ⟨17459, by rfl⟩) R34919
theorem R516527 : Reach 516527 := rs (se 1 (by rfl) ⟨387395, by rfl⟩) R774791
theorem R27641 : Reach 27641 := rs (se 2 (by rfl) ⟨10365, by rfl⟩) R20731
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R30143 : Reach 30143 := rs (se 1 (by rfl) ⟨22607, by rfl⟩) R45215
theorem R31817 : Reach 31817 := rs (se 2 (by rfl) ⟨11931, by rfl⟩) R23863
theorem R32615 : Reach 32615 := rs (se 1 (by rfl) ⟨24461, by rfl⟩) R48923
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R73709 : Reach 73709 := rs (se 3 (by rfl) ⟨13820, by rfl⟩) R27641
theorem R76955 : Reach 76955 := rs (se 1 (by rfl) ⟨57716, by rfl⟩) R115433
theorem R344351 : Reach 344351 := rs (se 1 (by rfl) ⟨258263, by rfl⟩) R516527
theorem R508355 : Reach 508355 := rs (se 1 (by rfl) ⟨381266, by rfl⟩) R762533
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) R31817
theorem R151145 : Reach 151145 := rs (se 2 (by rfl) ⟨56679, by rfl⟩) R113359
theorem R20095 : Reach 20095 := rs (se 1 (by rfl) ⟨15071, by rfl⟩) R30143
theorem R21211 : Reach 21211 := rs (se 1 (by rfl) ⟨15908, by rfl⟩) R31817
theorem R21743 : Reach 21743 := rs (se 1 (by rfl) ⟨16307, by rfl⟩) R32615
theorem R28831 : Reach 28831 := rs (se 1 (by rfl) ⟨21623, by rfl⟩) R43247
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R229567 : Reach 229567 := rs (se 1 (by rfl) ⟨172175, by rfl⟩) R344351
theorem R100763 : Reach 100763 := rs (se 1 (by rfl) ⟨75572, by rfl⟩) R151145
theorem R38441 : Reach 38441 := rs (se 2 (by rfl) ⟨14415, by rfl⟩) R28831
theorem R205213 : Reach 205213 := rs (se 3 (by rfl) ⟨38477, by rfl⟩) R76955
theorem R338903 : Reach 338903 := rs (se 1 (by rfl) ⟨254177, by rfl⟩) R508355
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R49139 : Reach 49139 := rs (se 1 (by rfl) ⟨36854, by rfl⟩) R73709
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R67175 : Reach 67175 := rs (se 1 (by rfl) ⟨50381, by rfl⟩) R100763
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R306089 : Reach 306089 := rs (se 2 (by rfl) ⟨114783, by rfl⟩) R229567
theorem R273617 : Reach 273617 := rs (se 2 (by rfl) ⟨102606, by rfl⟩) R205213
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R25627 : Reach 25627 := rs (se 1 (by rfl) ⟨19220, by rfl⟩) R38441
theorem R225935 : Reach 225935 := rs (se 1 (by rfl) ⟨169451, by rfl⟩) R338903
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R32759 : Reach 32759 := rs (se 1 (by rfl) ⟨24569, by rfl⟩) R49139
theorem R34169 : Reach 34169 := rs (se 2 (by rfl) ⟨12813, by rfl⟩) R25627
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R204059 : Reach 204059 := rs (se 1 (by rfl) ⟨153044, by rfl⟩) R306089
theorem R44783 : Reach 44783 := rs (se 1 (by rfl) ⟨33587, by rfl⟩) R67175
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R182411 : Reach 182411 := rs (se 1 (by rfl) ⟨136808, by rfl⟩) R273617
theorem R150623 : Reach 150623 := rs (se 1 (by rfl) ⟨112967, by rfl⟩) R225935
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R21839 : Reach 21839 := rs (se 1 (by rfl) ⟨16379, by rfl⟩) R32759
theorem R100415 : Reach 100415 := rs (se 1 (by rfl) ⟨75311, by rfl⟩) R150623
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R136039 : Reach 136039 := rs (se 1 (by rfl) ⟨102029, by rfl⟩) R204059
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R145435 : Reach 145435 := rs (se 1 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R22779 : Reach 22779 := rs (se 1 (by rfl) ⟨17084, by rfl⟩) R34169
theorem R121607 : Reach 121607 := rs (se 1 (by rfl) ⟨91205, by rfl⟩) R182411
theorem R29855 : Reach 29855 := rs (se 1 (by rfl) ⟨22391, by rfl⟩) R44783
theorem R66943 : Reach 66943 := rs (se 1 (by rfl) ⟨50207, by rfl⟩) R100415
theorem R79613 : Reach 79613 := rs (se 3 (by rfl) ⟨14927, by rfl⟩) R29855
theorem R81071 : Reach 81071 := rs (se 1 (by rfl) ⟨60803, by rfl⟩) R121607
theorem R181385 : Reach 181385 := rs (se 2 (by rfl) ⟨68019, by rfl⟩) R136039
theorem R51455 : Reach 51455 := rs (se 1 (by rfl) ⟨38591, by rfl⟩) R77183
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R193913 : Reach 193913 := rs (se 2 (by rfl) ⟨72717, by rfl⟩) R145435
theorem R34303 : Reach 34303 := rs (se 1 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R137213 : Reach 137213 := rs (se 3 (by rfl) ⟨25727, by rfl⟩) R51455
theorem R53075 : Reach 53075 := rs (se 1 (by rfl) ⟨39806, by rfl⟩) R79613
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R54047 : Reach 54047 := rs (se 1 (by rfl) ⟨40535, by rfl⟩) R81071
theorem R120923 : Reach 120923 := rs (se 1 (by rfl) ⟨90692, by rfl⟩) R181385
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) R66943
theorem R129275 : Reach 129275 := rs (se 1 (by rfl) ⟨96956, by rfl⟩) R193913
theorem R35383 : Reach 35383 := rs (se 1 (by rfl) ⟨26537, by rfl⟩) R53075
theorem R36031 : Reach 36031 := rs (se 1 (by rfl) ⟨27023, by rfl⟩) R54047
theorem R45737 : Reach 45737 := rs (se 2 (by rfl) ⟨17151, by rfl⟩) R34303
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R80615 : Reach 80615 := rs (se 1 (by rfl) ⟨60461, by rfl⟩) R120923
theorem R86183 : Reach 86183 := rs (se 1 (by rfl) ⟨64637, by rfl⟩) R129275
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R91475 : Reach 91475 := rs (se 1 (by rfl) ⟨68606, by rfl⟩) R137213
theorem R79339 : Reach 79339 := rs (se 1 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R47177 : Reach 47177 := rs (se 2 (by rfl) ⟨17691, by rfl⟩) R35383
theorem R48041 : Reach 48041 := rs (se 2 (by rfl) ⟨18015, by rfl⟩) R36031
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R53743 : Reach 53743 := rs (se 1 (by rfl) ⟨40307, by rfl⟩) R80615
theorem R57455 : Reach 57455 := rs (se 1 (by rfl) ⟨43091, by rfl⟩) R86183
theorem R60983 : Reach 60983 := rs (se 1 (by rfl) ⟨45737, by rfl⟩) R91475
theorem R30491 : Reach 30491 := rs (se 1 (by rfl) ⟨22868, by rfl⟩) R45737
theorem R35311 : Reach 35311 := rs (se 1 (by rfl) ⟨26483, by rfl⟩) R52967
theorem R38303 : Reach 38303 := rs (se 1 (by rfl) ⟨28727, by rfl⟩) R57455
theorem R71657 : Reach 71657 := rs (se 2 (by rfl) ⟨26871, by rfl⟩) R53743
theorem R105785 : Reach 105785 := rs (se 2 (by rfl) ⟨39669, by rfl⟩) R79339
theorem R40655 : Reach 40655 := rs (se 1 (by rfl) ⟨30491, by rfl⟩) R60983
theorem R20327 : Reach 20327 := rs (se 1 (by rfl) ⟨15245, by rfl⟩) R30491
theorem R31451 : Reach 31451 := rs (se 1 (by rfl) ⟨23588, by rfl⟩) R47177
theorem R32027 : Reach 32027 := rs (se 1 (by rfl) ⟨24020, by rfl⟩) R48041
theorem R70523 : Reach 70523 := rs (se 1 (by rfl) ⟨52892, by rfl⟩) R105785
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) R35311
theorem R47771 : Reach 47771 := rs (se 1 (by rfl) ⟨35828, by rfl⟩) R71657
theorem R20967 : Reach 20967 := rs (se 1 (by rfl) ⟨15725, by rfl⟩) R31451
theorem R21351 : Reach 21351 := rs (se 1 (by rfl) ⟨16013, by rfl⟩) R32027
theorem R25535 : Reach 25535 := rs (se 1 (by rfl) ⟨19151, by rfl⟩) R38303
theorem R27103 : Reach 27103 := rs (se 1 (by rfl) ⟨20327, by rfl⟩) R40655
theorem R68093 : Reach 68093 := rs (se 3 (by rfl) ⟨12767, by rfl⟩) R25535
theorem R36137 : Reach 36137 := rs (se 2 (by rfl) ⟨13551, by rfl⟩) R27103
theorem R47015 : Reach 47015 := rs (se 1 (by rfl) ⟨35261, by rfl⟩) R70523
theorem R125549 : Reach 125549 := rs (se 3 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R31847 : Reach 31847 := rs (se 1 (by rfl) ⟨23885, by rfl⟩) R47771
theorem R45395 : Reach 45395 := rs (se 1 (by rfl) ⟨34046, by rfl⟩) R68093
theorem R83699 : Reach 83699 := rs (se 1 (by rfl) ⟨62774, by rfl⟩) R125549
theorem R21231 : Reach 21231 := rs (se 1 (by rfl) ⟨15923, by rfl⟩) R31847
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) R36137
theorem R31343 : Reach 31343 := rs (se 1 (by rfl) ⟨23507, by rfl⟩) R47015
theorem R20895 : Reach 20895 := rs (se 1 (by rfl) ⟨15671, by rfl⟩) R31343
theorem R55799 : Reach 55799 := rs (se 1 (by rfl) ⟨41849, by rfl⟩) R83699
theorem R30263 : Reach 30263 := rs (se 1 (by rfl) ⟨22697, by rfl⟩) R45395
theorem R64243 : Reach 64243 := rs (se 1 (by rfl) ⟨48182, by rfl⟩) R96365
theorem R37199 : Reach 37199 := rs (se 1 (by rfl) ⟨27899, by rfl⟩) R55799
theorem R85657 : Reach 85657 := rs (se 2 (by rfl) ⟨32121, by rfl⟩) R64243
theorem R20175 : Reach 20175 := rs (se 1 (by rfl) ⟨15131, by rfl⟩) R30263
theorem R114209 : Reach 114209 := rs (se 2 (by rfl) ⟨42828, by rfl⟩) R85657
theorem R24799 : Reach 24799 := rs (se 1 (by rfl) ⟨18599, by rfl⟩) R37199
theorem R33065 : Reach 33065 := rs (se 2 (by rfl) ⟨12399, by rfl⟩) R24799
theorem R76139 : Reach 76139 := rs (se 1 (by rfl) ⟨57104, by rfl⟩) R114209
theorem R50759 : Reach 50759 := rs (se 1 (by rfl) ⟨38069, by rfl⟩) R76139
theorem R22043 : Reach 22043 := rs (se 1 (by rfl) ⟨16532, by rfl⟩) R33065
theorem R33839 : Reach 33839 := rs (se 1 (by rfl) ⟨25379, by rfl⟩) R50759
theorem R22559 : Reach 22559 := rs (se 1 (by rfl) ⟨16919, by rfl⟩) R33839

theorem C0 (j : ℕ) (h1 : 10000 ≤ j) (h2 : j ≤ 10699) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R20001
  · exact R20003
  · exact R20005
  · exact R20007
  · exact R20009
  · exact R20011
  · exact R20013
  · exact R20015
  · exact R20017
  · exact R20019
  · exact R20021
  · exact R20023
  · exact R20025
  · exact R20027
  · exact R20029
  · exact R20031
  · exact R20033
  · exact R20035
  · exact R20037
  · exact R20039
  · exact R20041
  · exact R20043
  · exact R20045
  · exact R20047
  · exact R20049
  · exact R20051
  · exact R20053
  · exact R20055
  · exact R20057
  · exact R20059
  · exact R20061
  · exact R20063
  · exact R20065
  · exact R20067
  · exact R20069
  · exact R20071
  · exact R20073
  · exact R20075
  · exact R20077
  · exact R20079
  · exact R20081
  · exact R20083
  · exact R20085
  · exact R20087
  · exact R20089
  · exact R20091
  · exact R20093
  · exact R20095
  · exact R20097
  · exact R20099
  · exact R20101
  · exact R20103
  · exact R20105
  · exact R20107
  · exact R20109
  · exact R20111
  · exact R20113
  · exact R20115
  · exact R20117
  · exact R20119
  · exact R20121
  · exact R20123
  · exact R20125
  · exact R20127
  · exact R20129
  · exact R20131
  · exact R20133
  · exact R20135
  · exact R20137
  · exact R20139
  · exact R20141
  · exact R20143
  · exact R20145
  · exact R20147
  · exact R20149
  · exact R20151
  · exact R20153
  · exact R20155
  · exact R20157
  · exact R20159
  · exact R20161
  · exact R20163
  · exact R20165
  · exact R20167
  · exact R20169
  · exact R20171
  · exact R20173
  · exact R20175
  · exact R20177
  · exact R20179
  · exact R20181
  · exact R20183
  · exact R20185
  · exact R20187
  · exact R20189
  · exact R20191
  · exact R20193
  · exact R20195
  · exact R20197
  · exact R20199
  · exact R20201
  · exact R20203
  · exact R20205
  · exact R20207
  · exact R20209
  · exact R20211
  · exact R20213
  · exact R20215
  · exact R20217
  · exact R20219
  · exact R20221
  · exact R20223
  · exact R20225
  · exact R20227
  · exact R20229
  · exact R20231
  · exact R20233
  · exact R20235
  · exact R20237
  · exact R20239
  · exact R20241
  · exact R20243
  · exact R20245
  · exact R20247
  · exact R20249
  · exact R20251
  · exact R20253
  · exact R20255
  · exact R20257
  · exact R20259
  · exact R20261
  · exact R20263
  · exact R20265
  · exact R20267
  · exact R20269
  · exact R20271
  · exact R20273
  · exact R20275
  · exact R20277
  · exact R20279
  · exact R20281
  · exact R20283
  · exact R20285
  · exact R20287
  · exact R20289
  · exact R20291
  · exact R20293
  · exact R20295
  · exact R20297
  · exact R20299
  · exact R20301
  · exact R20303
  · exact R20305
  · exact R20307
  · exact R20309
  · exact R20311
  · exact R20313
  · exact R20315
  · exact R20317
  · exact R20319
  · exact R20321
  · exact R20323
  · exact R20325
  · exact R20327
  · exact R20329
  · exact R20331
  · exact R20333
  · exact R20335
  · exact R20337
  · exact R20339
  · exact R20341
  · exact R20343
  · exact R20345
  · exact R20347
  · exact R20349
  · exact R20351
  · exact R20353
  · exact R20355
  · exact R20357
  · exact R20359
  · exact R20361
  · exact R20363
  · exact R20365
  · exact R20367
  · exact R20369
  · exact R20371
  · exact R20373
  · exact R20375
  · exact R20377
  · exact R20379
  · exact R20381
  · exact R20383
  · exact R20385
  · exact R20387
  · exact R20389
  · exact R20391
  · exact R20393
  · exact R20395
  · exact R20397
  · exact R20399
  · exact R20401
  · exact R20403
  · exact R20405
  · exact R20407
  · exact R20409
  · exact R20411
  · exact R20413
  · exact R20415
  · exact R20417
  · exact R20419
  · exact R20421
  · exact R20423
  · exact R20425
  · exact R20427
  · exact R20429
  · exact R20431
  · exact R20433
  · exact R20435
  · exact R20437
  · exact R20439
  · exact R20441
  · exact R20443
  · exact R20445
  · exact R20447
  · exact R20449
  · exact R20451
  · exact R20453
  · exact R20455
  · exact R20457
  · exact R20459
  · exact R20461
  · exact R20463
  · exact R20465
  · exact R20467
  · exact R20469
  · exact R20471
  · exact R20473
  · exact R20475
  · exact R20477
  · exact R20479
  · exact R20481
  · exact R20483
  · exact R20485
  · exact R20487
  · exact R20489
  · exact R20491
  · exact R20493
  · exact R20495
  · exact R20497
  · exact R20499
  · exact R20501
  · exact R20503
  · exact R20505
  · exact R20507
  · exact R20509
  · exact R20511
  · exact R20513
  · exact R20515
  · exact R20517
  · exact R20519
  · exact R20521
  · exact R20523
  · exact R20525
  · exact R20527
  · exact R20529
  · exact R20531
  · exact R20533
  · exact R20535
  · exact R20537
  · exact R20539
  · exact R20541
  · exact R20543
  · exact R20545
  · exact R20547
  · exact R20549
  · exact R20551
  · exact R20553
  · exact R20555
  · exact R20557
  · exact R20559
  · exact R20561
  · exact R20563
  · exact R20565
  · exact R20567
  · exact R20569
  · exact R20571
  · exact R20573
  · exact R20575
  · exact R20577
  · exact R20579
  · exact R20581
  · exact R20583
  · exact R20585
  · exact R20587
  · exact R20589
  · exact R20591
  · exact R20593
  · exact R20595
  · exact R20597
  · exact R20599
  · exact R20601
  · exact R20603
  · exact R20605
  · exact R20607
  · exact R20609
  · exact R20611
  · exact R20613
  · exact R20615
  · exact R20617
  · exact R20619
  · exact R20621
  · exact R20623
  · exact R20625
  · exact R20627
  · exact R20629
  · exact R20631
  · exact R20633
  · exact R20635
  · exact R20637
  · exact R20639
  · exact R20641
  · exact R20643
  · exact R20645
  · exact R20647
  · exact R20649
  · exact R20651
  · exact R20653
  · exact R20655
  · exact R20657
  · exact R20659
  · exact R20661
  · exact R20663
  · exact R20665
  · exact R20667
  · exact R20669
  · exact R20671
  · exact R20673
  · exact R20675
  · exact R20677
  · exact R20679
  · exact R20681
  · exact R20683
  · exact R20685
  · exact R20687
  · exact R20689
  · exact R20691
  · exact R20693
  · exact R20695
  · exact R20697
  · exact R20699
  · exact R20701
  · exact R20703
  · exact R20705
  · exact R20707
  · exact R20709
  · exact R20711
  · exact R20713
  · exact R20715
  · exact R20717
  · exact R20719
  · exact R20721
  · exact R20723
  · exact R20725
  · exact R20727
  · exact R20729
  · exact R20731
  · exact R20733
  · exact R20735
  · exact R20737
  · exact R20739
  · exact R20741
  · exact R20743
  · exact R20745
  · exact R20747
  · exact R20749
  · exact R20751
  · exact R20753
  · exact R20755
  · exact R20757
  · exact R20759
  · exact R20761
  · exact R20763
  · exact R20765
  · exact R20767
  · exact R20769
  · exact R20771
  · exact R20773
  · exact R20775
  · exact R20777
  · exact R20779
  · exact R20781
  · exact R20783
  · exact R20785
  · exact R20787
  · exact R20789
  · exact R20791
  · exact R20793
  · exact R20795
  · exact R20797
  · exact R20799
  · exact R20801
  · exact R20803
  · exact R20805
  · exact R20807
  · exact R20809
  · exact R20811
  · exact R20813
  · exact R20815
  · exact R20817
  · exact R20819
  · exact R20821
  · exact R20823
  · exact R20825
  · exact R20827
  · exact R20829
  · exact R20831
  · exact R20833
  · exact R20835
  · exact R20837
  · exact R20839
  · exact R20841
  · exact R20843
  · exact R20845
  · exact R20847
  · exact R20849
  · exact R20851
  · exact R20853
  · exact R20855
  · exact R20857
  · exact R20859
  · exact R20861
  · exact R20863
  · exact R20865
  · exact R20867
  · exact R20869
  · exact R20871
  · exact R20873
  · exact R20875
  · exact R20877
  · exact R20879
  · exact R20881
  · exact R20883
  · exact R20885
  · exact R20887
  · exact R20889
  · exact R20891
  · exact R20893
  · exact R20895
  · exact R20897
  · exact R20899
  · exact R20901
  · exact R20903
  · exact R20905
  · exact R20907
  · exact R20909
  · exact R20911
  · exact R20913
  · exact R20915
  · exact R20917
  · exact R20919
  · exact R20921
  · exact R20923
  · exact R20925
  · exact R20927
  · exact R20929
  · exact R20931
  · exact R20933
  · exact R20935
  · exact R20937
  · exact R20939
  · exact R20941
  · exact R20943
  · exact R20945
  · exact R20947
  · exact R20949
  · exact R20951
  · exact R20953
  · exact R20955
  · exact R20957
  · exact R20959
  · exact R20961
  · exact R20963
  · exact R20965
  · exact R20967
  · exact R20969
  · exact R20971
  · exact R20973
  · exact R20975
  · exact R20977
  · exact R20979
  · exact R20981
  · exact R20983
  · exact R20985
  · exact R20987
  · exact R20989
  · exact R20991
  · exact R20993
  · exact R20995
  · exact R20997
  · exact R20999
  · exact R21001
  · exact R21003
  · exact R21005
  · exact R21007
  · exact R21009
  · exact R21011
  · exact R21013
  · exact R21015
  · exact R21017
  · exact R21019
  · exact R21021
  · exact R21023
  · exact R21025
  · exact R21027
  · exact R21029
  · exact R21031
  · exact R21033
  · exact R21035
  · exact R21037
  · exact R21039
  · exact R21041
  · exact R21043
  · exact R21045
  · exact R21047
  · exact R21049
  · exact R21051
  · exact R21053
  · exact R21055
  · exact R21057
  · exact R21059
  · exact R21061
  · exact R21063
  · exact R21065
  · exact R21067
  · exact R21069
  · exact R21071
  · exact R21073
  · exact R21075
  · exact R21077
  · exact R21079
  · exact R21081
  · exact R21083
  · exact R21085
  · exact R21087
  · exact R21089
  · exact R21091
  · exact R21093
  · exact R21095
  · exact R21097
  · exact R21099
  · exact R21101
  · exact R21103
  · exact R21105
  · exact R21107
  · exact R21109
  · exact R21111
  · exact R21113
  · exact R21115
  · exact R21117
  · exact R21119
  · exact R21121
  · exact R21123
  · exact R21125
  · exact R21127
  · exact R21129
  · exact R21131
  · exact R21133
  · exact R21135
  · exact R21137
  · exact R21139
  · exact R21141
  · exact R21143
  · exact R21145
  · exact R21147
  · exact R21149
  · exact R21151
  · exact R21153
  · exact R21155
  · exact R21157
  · exact R21159
  · exact R21161
  · exact R21163
  · exact R21165
  · exact R21167
  · exact R21169
  · exact R21171
  · exact R21173
  · exact R21175
  · exact R21177
  · exact R21179
  · exact R21181
  · exact R21183
  · exact R21185
  · exact R21187
  · exact R21189
  · exact R21191
  · exact R21193
  · exact R21195
  · exact R21197
  · exact R21199
  · exact R21201
  · exact R21203
  · exact R21205
  · exact R21207
  · exact R21209
  · exact R21211
  · exact R21213
  · exact R21215
  · exact R21217
  · exact R21219
  · exact R21221
  · exact R21223
  · exact R21225
  · exact R21227
  · exact R21229
  · exact R21231
  · exact R21233
  · exact R21235
  · exact R21237
  · exact R21239
  · exact R21241
  · exact R21243
  · exact R21245
  · exact R21247
  · exact R21249
  · exact R21251
  · exact R21253
  · exact R21255
  · exact R21257
  · exact R21259
  · exact R21261
  · exact R21263
  · exact R21265
  · exact R21267
  · exact R21269
  · exact R21271
  · exact R21273
  · exact R21275
  · exact R21277
  · exact R21279
  · exact R21281
  · exact R21283
  · exact R21285
  · exact R21287
  · exact R21289
  · exact R21291
  · exact R21293
  · exact R21295
  · exact R21297
  · exact R21299
  · exact R21301
  · exact R21303
  · exact R21305
  · exact R21307
  · exact R21309
  · exact R21311
  · exact R21313
  · exact R21315
  · exact R21317
  · exact R21319
  · exact R21321
  · exact R21323
  · exact R21325
  · exact R21327
  · exact R21329
  · exact R21331
  · exact R21333
  · exact R21335
  · exact R21337
  · exact R21339
  · exact R21341
  · exact R21343
  · exact R21345
  · exact R21347
  · exact R21349
  · exact R21351
  · exact R21353
  · exact R21355
  · exact R21357
  · exact R21359
  · exact R21361
  · exact R21363
  · exact R21365
  · exact R21367
  · exact R21369
  · exact R21371
  · exact R21373
  · exact R21375
  · exact R21377
  · exact R21379
  · exact R21381
  · exact R21383
  · exact R21385
  · exact R21387
  · exact R21389
  · exact R21391
  · exact R21393
  · exact R21395
  · exact R21397
  · exact R21399

theorem C1 (j : ℕ) (h1 : 10700 ≤ j) (h2 : j ≤ 11399) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R21401
  · exact R21403
  · exact R21405
  · exact R21407
  · exact R21409
  · exact R21411
  · exact R21413
  · exact R21415
  · exact R21417
  · exact R21419
  · exact R21421
  · exact R21423
  · exact R21425
  · exact R21427
  · exact R21429
  · exact R21431
  · exact R21433
  · exact R21435
  · exact R21437
  · exact R21439
  · exact R21441
  · exact R21443
  · exact R21445
  · exact R21447
  · exact R21449
  · exact R21451
  · exact R21453
  · exact R21455
  · exact R21457
  · exact R21459
  · exact R21461
  · exact R21463
  · exact R21465
  · exact R21467
  · exact R21469
  · exact R21471
  · exact R21473
  · exact R21475
  · exact R21477
  · exact R21479
  · exact R21481
  · exact R21483
  · exact R21485
  · exact R21487
  · exact R21489
  · exact R21491
  · exact R21493
  · exact R21495
  · exact R21497
  · exact R21499
  · exact R21501
  · exact R21503
  · exact R21505
  · exact R21507
  · exact R21509
  · exact R21511
  · exact R21513
  · exact R21515
  · exact R21517
  · exact R21519
  · exact R21521
  · exact R21523
  · exact R21525
  · exact R21527
  · exact R21529
  · exact R21531
  · exact R21533
  · exact R21535
  · exact R21537
  · exact R21539
  · exact R21541
  · exact R21543
  · exact R21545
  · exact R21547
  · exact R21549
  · exact R21551
  · exact R21553
  · exact R21555
  · exact R21557
  · exact R21559
  · exact R21561
  · exact R21563
  · exact R21565
  · exact R21567
  · exact R21569
  · exact R21571
  · exact R21573
  · exact R21575
  · exact R21577
  · exact R21579
  · exact R21581
  · exact R21583
  · exact R21585
  · exact R21587
  · exact R21589
  · exact R21591
  · exact R21593
  · exact R21595
  · exact R21597
  · exact R21599
  · exact R21601
  · exact R21603
  · exact R21605
  · exact R21607
  · exact R21609
  · exact R21611
  · exact R21613
  · exact R21615
  · exact R21617
  · exact R21619
  · exact R21621
  · exact R21623
  · exact R21625
  · exact R21627
  · exact R21629
  · exact R21631
  · exact R21633
  · exact R21635
  · exact R21637
  · exact R21639
  · exact R21641
  · exact R21643
  · exact R21645
  · exact R21647
  · exact R21649
  · exact R21651
  · exact R21653
  · exact R21655
  · exact R21657
  · exact R21659
  · exact R21661
  · exact R21663
  · exact R21665
  · exact R21667
  · exact R21669
  · exact R21671
  · exact R21673
  · exact R21675
  · exact R21677
  · exact R21679
  · exact R21681
  · exact R21683
  · exact R21685
  · exact R21687
  · exact R21689
  · exact R21691
  · exact R21693
  · exact R21695
  · exact R21697
  · exact R21699
  · exact R21701
  · exact R21703
  · exact R21705
  · exact R21707
  · exact R21709
  · exact R21711
  · exact R21713
  · exact R21715
  · exact R21717
  · exact R21719
  · exact R21721
  · exact R21723
  · exact R21725
  · exact R21727
  · exact R21729
  · exact R21731
  · exact R21733
  · exact R21735
  · exact R21737
  · exact R21739
  · exact R21741
  · exact R21743
  · exact R21745
  · exact R21747
  · exact R21749
  · exact R21751
  · exact R21753
  · exact R21755
  · exact R21757
  · exact R21759
  · exact R21761
  · exact R21763
  · exact R21765
  · exact R21767
  · exact R21769
  · exact R21771
  · exact R21773
  · exact R21775
  · exact R21777
  · exact R21779
  · exact R21781
  · exact R21783
  · exact R21785
  · exact R21787
  · exact R21789
  · exact R21791
  · exact R21793
  · exact R21795
  · exact R21797
  · exact R21799
  · exact R21801
  · exact R21803
  · exact R21805
  · exact R21807
  · exact R21809
  · exact R21811
  · exact R21813
  · exact R21815
  · exact R21817
  · exact R21819
  · exact R21821
  · exact R21823
  · exact R21825
  · exact R21827
  · exact R21829
  · exact R21831
  · exact R21833
  · exact R21835
  · exact R21837
  · exact R21839
  · exact R21841
  · exact R21843
  · exact R21845
  · exact R21847
  · exact R21849
  · exact R21851
  · exact R21853
  · exact R21855
  · exact R21857
  · exact R21859
  · exact R21861
  · exact R21863
  · exact R21865
  · exact R21867
  · exact R21869
  · exact R21871
  · exact R21873
  · exact R21875
  · exact R21877
  · exact R21879
  · exact R21881
  · exact R21883
  · exact R21885
  · exact R21887
  · exact R21889
  · exact R21891
  · exact R21893
  · exact R21895
  · exact R21897
  · exact R21899
  · exact R21901
  · exact R21903
  · exact R21905
  · exact R21907
  · exact R21909
  · exact R21911
  · exact R21913
  · exact R21915
  · exact R21917
  · exact R21919
  · exact R21921
  · exact R21923
  · exact R21925
  · exact R21927
  · exact R21929
  · exact R21931
  · exact R21933
  · exact R21935
  · exact R21937
  · exact R21939
  · exact R21941
  · exact R21943
  · exact R21945
  · exact R21947
  · exact R21949
  · exact R21951
  · exact R21953
  · exact R21955
  · exact R21957
  · exact R21959
  · exact R21961
  · exact R21963
  · exact R21965
  · exact R21967
  · exact R21969
  · exact R21971
  · exact R21973
  · exact R21975
  · exact R21977
  · exact R21979
  · exact R21981
  · exact R21983
  · exact R21985
  · exact R21987
  · exact R21989
  · exact R21991
  · exact R21993
  · exact R21995
  · exact R21997
  · exact R21999
  · exact R22001
  · exact R22003
  · exact R22005
  · exact R22007
  · exact R22009
  · exact R22011
  · exact R22013
  · exact R22015
  · exact R22017
  · exact R22019
  · exact R22021
  · exact R22023
  · exact R22025
  · exact R22027
  · exact R22029
  · exact R22031
  · exact R22033
  · exact R22035
  · exact R22037
  · exact R22039
  · exact R22041
  · exact R22043
  · exact R22045
  · exact R22047
  · exact R22049
  · exact R22051
  · exact R22053
  · exact R22055
  · exact R22057
  · exact R22059
  · exact R22061
  · exact R22063
  · exact R22065
  · exact R22067
  · exact R22069
  · exact R22071
  · exact R22073
  · exact R22075
  · exact R22077
  · exact R22079
  · exact R22081
  · exact R22083
  · exact R22085
  · exact R22087
  · exact R22089
  · exact R22091
  · exact R22093
  · exact R22095
  · exact R22097
  · exact R22099
  · exact R22101
  · exact R22103
  · exact R22105
  · exact R22107
  · exact R22109
  · exact R22111
  · exact R22113
  · exact R22115
  · exact R22117
  · exact R22119
  · exact R22121
  · exact R22123
  · exact R22125
  · exact R22127
  · exact R22129
  · exact R22131
  · exact R22133
  · exact R22135
  · exact R22137
  · exact R22139
  · exact R22141
  · exact R22143
  · exact R22145
  · exact R22147
  · exact R22149
  · exact R22151
  · exact R22153
  · exact R22155
  · exact R22157
  · exact R22159
  · exact R22161
  · exact R22163
  · exact R22165
  · exact R22167
  · exact R22169
  · exact R22171
  · exact R22173
  · exact R22175
  · exact R22177
  · exact R22179
  · exact R22181
  · exact R22183
  · exact R22185
  · exact R22187
  · exact R22189
  · exact R22191
  · exact R22193
  · exact R22195
  · exact R22197
  · exact R22199
  · exact R22201
  · exact R22203
  · exact R22205
  · exact R22207
  · exact R22209
  · exact R22211
  · exact R22213
  · exact R22215
  · exact R22217
  · exact R22219
  · exact R22221
  · exact R22223
  · exact R22225
  · exact R22227
  · exact R22229
  · exact R22231
  · exact R22233
  · exact R22235
  · exact R22237
  · exact R22239
  · exact R22241
  · exact R22243
  · exact R22245
  · exact R22247
  · exact R22249
  · exact R22251
  · exact R22253
  · exact R22255
  · exact R22257
  · exact R22259
  · exact R22261
  · exact R22263
  · exact R22265
  · exact R22267
  · exact R22269
  · exact R22271
  · exact R22273
  · exact R22275
  · exact R22277
  · exact R22279
  · exact R22281
  · exact R22283
  · exact R22285
  · exact R22287
  · exact R22289
  · exact R22291
  · exact R22293
  · exact R22295
  · exact R22297
  · exact R22299
  · exact R22301
  · exact R22303
  · exact R22305
  · exact R22307
  · exact R22309
  · exact R22311
  · exact R22313
  · exact R22315
  · exact R22317
  · exact R22319
  · exact R22321
  · exact R22323
  · exact R22325
  · exact R22327
  · exact R22329
  · exact R22331
  · exact R22333
  · exact R22335
  · exact R22337
  · exact R22339
  · exact R22341
  · exact R22343
  · exact R22345
  · exact R22347
  · exact R22349
  · exact R22351
  · exact R22353
  · exact R22355
  · exact R22357
  · exact R22359
  · exact R22361
  · exact R22363
  · exact R22365
  · exact R22367
  · exact R22369
  · exact R22371
  · exact R22373
  · exact R22375
  · exact R22377
  · exact R22379
  · exact R22381
  · exact R22383
  · exact R22385
  · exact R22387
  · exact R22389
  · exact R22391
  · exact R22393
  · exact R22395
  · exact R22397
  · exact R22399
  · exact R22401
  · exact R22403
  · exact R22405
  · exact R22407
  · exact R22409
  · exact R22411
  · exact R22413
  · exact R22415
  · exact R22417
  · exact R22419
  · exact R22421
  · exact R22423
  · exact R22425
  · exact R22427
  · exact R22429
  · exact R22431
  · exact R22433
  · exact R22435
  · exact R22437
  · exact R22439
  · exact R22441
  · exact R22443
  · exact R22445
  · exact R22447
  · exact R22449
  · exact R22451
  · exact R22453
  · exact R22455
  · exact R22457
  · exact R22459
  · exact R22461
  · exact R22463
  · exact R22465
  · exact R22467
  · exact R22469
  · exact R22471
  · exact R22473
  · exact R22475
  · exact R22477
  · exact R22479
  · exact R22481
  · exact R22483
  · exact R22485
  · exact R22487
  · exact R22489
  · exact R22491
  · exact R22493
  · exact R22495
  · exact R22497
  · exact R22499
  · exact R22501
  · exact R22503
  · exact R22505
  · exact R22507
  · exact R22509
  · exact R22511
  · exact R22513
  · exact R22515
  · exact R22517
  · exact R22519
  · exact R22521
  · exact R22523
  · exact R22525
  · exact R22527
  · exact R22529
  · exact R22531
  · exact R22533
  · exact R22535
  · exact R22537
  · exact R22539
  · exact R22541
  · exact R22543
  · exact R22545
  · exact R22547
  · exact R22549
  · exact R22551
  · exact R22553
  · exact R22555
  · exact R22557
  · exact R22559
  · exact R22561
  · exact R22563
  · exact R22565
  · exact R22567
  · exact R22569
  · exact R22571
  · exact R22573
  · exact R22575
  · exact R22577
  · exact R22579
  · exact R22581
  · exact R22583
  · exact R22585
  · exact R22587
  · exact R22589
  · exact R22591
  · exact R22593
  · exact R22595
  · exact R22597
  · exact R22599
  · exact R22601
  · exact R22603
  · exact R22605
  · exact R22607
  · exact R22609
  · exact R22611
  · exact R22613
  · exact R22615
  · exact R22617
  · exact R22619
  · exact R22621
  · exact R22623
  · exact R22625
  · exact R22627
  · exact R22629
  · exact R22631
  · exact R22633
  · exact R22635
  · exact R22637
  · exact R22639
  · exact R22641
  · exact R22643
  · exact R22645
  · exact R22647
  · exact R22649
  · exact R22651
  · exact R22653
  · exact R22655
  · exact R22657
  · exact R22659
  · exact R22661
  · exact R22663
  · exact R22665
  · exact R22667
  · exact R22669
  · exact R22671
  · exact R22673
  · exact R22675
  · exact R22677
  · exact R22679
  · exact R22681
  · exact R22683
  · exact R22685
  · exact R22687
  · exact R22689
  · exact R22691
  · exact R22693
  · exact R22695
  · exact R22697
  · exact R22699
  · exact R22701
  · exact R22703
  · exact R22705
  · exact R22707
  · exact R22709
  · exact R22711
  · exact R22713
  · exact R22715
  · exact R22717
  · exact R22719
  · exact R22721
  · exact R22723
  · exact R22725
  · exact R22727
  · exact R22729
  · exact R22731
  · exact R22733
  · exact R22735
  · exact R22737
  · exact R22739
  · exact R22741
  · exact R22743
  · exact R22745
  · exact R22747
  · exact R22749
  · exact R22751
  · exact R22753
  · exact R22755
  · exact R22757
  · exact R22759
  · exact R22761
  · exact R22763
  · exact R22765
  · exact R22767
  · exact R22769
  · exact R22771
  · exact R22773
  · exact R22775
  · exact R22777
  · exact R22779
  · exact R22781
  · exact R22783
  · exact R22785
  · exact R22787
  · exact R22789
  · exact R22791
  · exact R22793
  · exact R22795
  · exact R22797
  · exact R22799

theorem C2 (j : ℕ) (h1 : 11400 ≤ j) (h2 : j ≤ 11749) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R22801
  · exact R22803
  · exact R22805
  · exact R22807
  · exact R22809
  · exact R22811
  · exact R22813
  · exact R22815
  · exact R22817
  · exact R22819
  · exact R22821
  · exact R22823
  · exact R22825
  · exact R22827
  · exact R22829
  · exact R22831
  · exact R22833
  · exact R22835
  · exact R22837
  · exact R22839
  · exact R22841
  · exact R22843
  · exact R22845
  · exact R22847
  · exact R22849
  · exact R22851
  · exact R22853
  · exact R22855
  · exact R22857
  · exact R22859
  · exact R22861
  · exact R22863
  · exact R22865
  · exact R22867
  · exact R22869
  · exact R22871
  · exact R22873
  · exact R22875
  · exact R22877
  · exact R22879
  · exact R22881
  · exact R22883
  · exact R22885
  · exact R22887
  · exact R22889
  · exact R22891
  · exact R22893
  · exact R22895
  · exact R22897
  · exact R22899
  · exact R22901
  · exact R22903
  · exact R22905
  · exact R22907
  · exact R22909
  · exact R22911
  · exact R22913
  · exact R22915
  · exact R22917
  · exact R22919
  · exact R22921
  · exact R22923
  · exact R22925
  · exact R22927
  · exact R22929
  · exact R22931
  · exact R22933
  · exact R22935
  · exact R22937
  · exact R22939
  · exact R22941
  · exact R22943
  · exact R22945
  · exact R22947
  · exact R22949
  · exact R22951
  · exact R22953
  · exact R22955
  · exact R22957
  · exact R22959
  · exact R22961
  · exact R22963
  · exact R22965
  · exact R22967
  · exact R22969
  · exact R22971
  · exact R22973
  · exact R22975
  · exact R22977
  · exact R22979
  · exact R22981
  · exact R22983
  · exact R22985
  · exact R22987
  · exact R22989
  · exact R22991
  · exact R22993
  · exact R22995
  · exact R22997
  · exact R22999
  · exact R23001
  · exact R23003
  · exact R23005
  · exact R23007
  · exact R23009
  · exact R23011
  · exact R23013
  · exact R23015
  · exact R23017
  · exact R23019
  · exact R23021
  · exact R23023
  · exact R23025
  · exact R23027
  · exact R23029
  · exact R23031
  · exact R23033
  · exact R23035
  · exact R23037
  · exact R23039
  · exact R23041
  · exact R23043
  · exact R23045
  · exact R23047
  · exact R23049
  · exact R23051
  · exact R23053
  · exact R23055
  · exact R23057
  · exact R23059
  · exact R23061
  · exact R23063
  · exact R23065
  · exact R23067
  · exact R23069
  · exact R23071
  · exact R23073
  · exact R23075
  · exact R23077
  · exact R23079
  · exact R23081
  · exact R23083
  · exact R23085
  · exact R23087
  · exact R23089
  · exact R23091
  · exact R23093
  · exact R23095
  · exact R23097
  · exact R23099
  · exact R23101
  · exact R23103
  · exact R23105
  · exact R23107
  · exact R23109
  · exact R23111
  · exact R23113
  · exact R23115
  · exact R23117
  · exact R23119
  · exact R23121
  · exact R23123
  · exact R23125
  · exact R23127
  · exact R23129
  · exact R23131
  · exact R23133
  · exact R23135
  · exact R23137
  · exact R23139
  · exact R23141
  · exact R23143
  · exact R23145
  · exact R23147
  · exact R23149
  · exact R23151
  · exact R23153
  · exact R23155
  · exact R23157
  · exact R23159
  · exact R23161
  · exact R23163
  · exact R23165
  · exact R23167
  · exact R23169
  · exact R23171
  · exact R23173
  · exact R23175
  · exact R23177
  · exact R23179
  · exact R23181
  · exact R23183
  · exact R23185
  · exact R23187
  · exact R23189
  · exact R23191
  · exact R23193
  · exact R23195
  · exact R23197
  · exact R23199
  · exact R23201
  · exact R23203
  · exact R23205
  · exact R23207
  · exact R23209
  · exact R23211
  · exact R23213
  · exact R23215
  · exact R23217
  · exact R23219
  · exact R23221
  · exact R23223
  · exact R23225
  · exact R23227
  · exact R23229
  · exact R23231
  · exact R23233
  · exact R23235
  · exact R23237
  · exact R23239
  · exact R23241
  · exact R23243
  · exact R23245
  · exact R23247
  · exact R23249
  · exact R23251
  · exact R23253
  · exact R23255
  · exact R23257
  · exact R23259
  · exact R23261
  · exact R23263
  · exact R23265
  · exact R23267
  · exact R23269
  · exact R23271
  · exact R23273
  · exact R23275
  · exact R23277
  · exact R23279
  · exact R23281
  · exact R23283
  · exact R23285
  · exact R23287
  · exact R23289
  · exact R23291
  · exact R23293
  · exact R23295
  · exact R23297
  · exact R23299
  · exact R23301
  · exact R23303
  · exact R23305
  · exact R23307
  · exact R23309
  · exact R23311
  · exact R23313
  · exact R23315
  · exact R23317
  · exact R23319
  · exact R23321
  · exact R23323
  · exact R23325
  · exact R23327
  · exact R23329
  · exact R23331
  · exact R23333
  · exact R23335
  · exact R23337
  · exact R23339
  · exact R23341
  · exact R23343
  · exact R23345
  · exact R23347
  · exact R23349
  · exact R23351
  · exact R23353
  · exact R23355
  · exact R23357
  · exact R23359
  · exact R23361
  · exact R23363
  · exact R23365
  · exact R23367
  · exact R23369
  · exact R23371
  · exact R23373
  · exact R23375
  · exact R23377
  · exact R23379
  · exact R23381
  · exact R23383
  · exact R23385
  · exact R23387
  · exact R23389
  · exact R23391
  · exact R23393
  · exact R23395
  · exact R23397
  · exact R23399
  · exact R23401
  · exact R23403
  · exact R23405
  · exact R23407
  · exact R23409
  · exact R23411
  · exact R23413
  · exact R23415
  · exact R23417
  · exact R23419
  · exact R23421
  · exact R23423
  · exact R23425
  · exact R23427
  · exact R23429
  · exact R23431
  · exact R23433
  · exact R23435
  · exact R23437
  · exact R23439
  · exact R23441
  · exact R23443
  · exact R23445
  · exact R23447
  · exact R23449
  · exact R23451
  · exact R23453
  · exact R23455
  · exact R23457
  · exact R23459
  · exact R23461
  · exact R23463
  · exact R23465
  · exact R23467
  · exact R23469
  · exact R23471
  · exact R23473
  · exact R23475
  · exact R23477
  · exact R23479
  · exact R23481
  · exact R23483
  · exact R23485
  · exact R23487
  · exact R23489
  · exact R23491
  · exact R23493
  · exact R23495
  · exact R23497
  · exact R23499

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 23500) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 20001 with hlo | hlo
  · exact syracuse_reaches_one_below_20001 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 10700 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 11400 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
