-- Prove2me | solution 1 for syracuse_descends_range_1403521_1405521
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:13:54.464759+00:00
-- url     : https://prove2.me/submissions/90f94b1c-8a91-4f72-9aa6-3c0300e819bf

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


theorem B1581061 : Blo 1403521 1581061 := bbase (se 4 (by rfl) ⟨148224, by rfl⟩ : syracuseStep 1581061 = 296449) (by norm_num)
theorem B2105357 : Blo 1403521 2105357 := bbase (se 3 (by rfl) ⟨394754, by rfl⟩ : syracuseStep 2105357 = 789509) (by norm_num)
theorem B2105381 : Blo 1403521 2105381 := bbase (se 4 (by rfl) ⟨197379, by rfl⟩ : syracuseStep 2105381 = 394759) (by norm_num)
theorem B2998309 : Blo 1403521 2998309 := bbase (se 4 (by rfl) ⟨281091, by rfl⟩ : syracuseStep 2998309 = 562183) (by norm_num)
theorem B3162149 : Blo 1403521 3162149 := bbase (se 4 (by rfl) ⟨296451, by rfl⟩ : syracuseStep 3162149 = 592903) (by norm_num)
theorem B1581097 : Blo 1403521 1581097 := bbase (se 2 (by rfl) ⟨592911, by rfl⟩ : syracuseStep 1581097 = 1185823) (by norm_num)
theorem B3555373 : Blo 1403521 3555373 := bbase (se 3 (by rfl) ⟨666632, by rfl⟩ : syracuseStep 3555373 = 1333265) (by norm_num)
theorem B1499185 : Blo 1403521 1499185 := bbase (se 2 (by rfl) ⟨562194, by rfl⟩ : syracuseStep 1499185 = 1124389) (by norm_num)
theorem B1777717 : Blo 1403521 1777717 := bbase (se 5 (by rfl) ⟨83330, by rfl⟩ : syracuseStep 1777717 = 166661) (by norm_num)
theorem B2105405 : Blo 1403521 2105405 := bbase (se 3 (by rfl) ⟨394763, by rfl⟩ : syracuseStep 2105405 = 789527) (by norm_num)
theorem B1581133 : Blo 1403521 1581133 := bbase (se 3 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 1581133 = 592925) (by norm_num)
theorem B2105429 : Blo 1403521 2105429 := bbase (se 8 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 2105429 = 24673) (by norm_num)
theorem B6406229 : Blo 1403521 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B1687645 : Blo 1403521 1687645 := bbase (se 3 (by rfl) ⟨316433, by rfl⟩ : syracuseStep 1687645 = 632867) (by norm_num)
theorem B2105453 : Blo 1403521 2105453 := bbase (se 3 (by rfl) ⟨394772, by rfl⟩ : syracuseStep 2105453 = 789545) (by norm_num)
theorem B3162221 : Blo 1403521 3162221 := bbase (se 3 (by rfl) ⟨592916, by rfl⟩ : syracuseStep 3162221 = 1185833) (by norm_num)
theorem B1581169 : Blo 1403521 1581169 := bbase (se 2 (by rfl) ⟨592938, by rfl⟩ : syracuseStep 1581169 = 1185877) (by norm_num)
theorem B1499257 : Blo 1403521 1499257 := bbase (se 2 (by rfl) ⟨562221, by rfl⟩ : syracuseStep 1499257 = 1124443) (by norm_num)
theorem B2105477 : Blo 1403521 2105477 := bbase (se 4 (by rfl) ⟨197388, by rfl⟩ : syracuseStep 2105477 = 394777) (by norm_num)
theorem B1581205 : Blo 1403521 1581205 := bbase (se 6 (by rfl) ⟨37059, by rfl⟩ : syracuseStep 1581205 = 74119) (by norm_num)
theorem B2105501 : Blo 1403521 2105501 := bbase (se 3 (by rfl) ⟨394781, by rfl⟩ : syracuseStep 2105501 = 789563) (by norm_num)
theorem B3555485 : Blo 1403521 3555485 := bbase (se 3 (by rfl) ⟨666653, by rfl⟩ : syracuseStep 3555485 = 1333307) (by norm_num)
theorem B1999021 : Blo 1403521 1999021 := bbase (se 3 (by rfl) ⟨374816, by rfl⟩ : syracuseStep 1999021 = 749633) (by norm_num)
theorem B2105525 : Blo 1403521 2105525 := bbase (se 5 (by rfl) ⟨98696, by rfl⟩ : syracuseStep 2105525 = 197393) (by norm_num)
theorem B3162293 : Blo 1403521 3162293 := bbase (se 5 (by rfl) ⟨148232, by rfl⟩ : syracuseStep 3162293 = 296465) (by norm_num)
theorem B1851589 : Blo 1403521 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B2105549 : Blo 1403521 2105549 := bbase (se 3 (by rfl) ⟨394790, by rfl⟩ : syracuseStep 2105549 = 789581) (by norm_num)
theorem B16007381 : Blo 1403521 16007381 := bbase (se 7 (by rfl) ⟨187586, by rfl⟩ : syracuseStep 16007381 = 375173) (by norm_num)
theorem B1777889 : Blo 1403521 1777889 := bbase (se 2 (by rfl) ⟨666708, by rfl⟩ : syracuseStep 1777889 = 1333417) (by norm_num)
theorem B2105573 : Blo 1403521 2105573 := bbase (se 4 (by rfl) ⟨197397, by rfl⟩ : syracuseStep 2105573 = 394795) (by norm_num)
theorem B4743413 : Blo 1403521 4743413 := bbase (se 5 (by rfl) ⟨222347, by rfl⟩ : syracuseStep 4743413 = 444695) (by norm_num)
theorem B2105597 : Blo 1403521 2105597 := bbase (se 3 (by rfl) ⟨394799, by rfl⟩ : syracuseStep 2105597 = 789599) (by norm_num)
theorem B3162365 : Blo 1403521 3162365 := bbase (se 3 (by rfl) ⟨592943, by rfl⟩ : syracuseStep 3162365 = 1185887) (by norm_num)
theorem B1925381 : Blo 1403521 1925381 := bbase (se 4 (by rfl) ⟨180504, by rfl⟩ : syracuseStep 1925381 = 361009) (by norm_num)
theorem B2105621 : Blo 1403521 2105621 := bbase (se 6 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 2105621 = 98701) (by norm_num)
theorem B3997973 : Blo 1403521 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B6750485 : Blo 1403521 6750485 := bbase (se 6 (by rfl) ⟨158214, by rfl⟩ : syracuseStep 6750485 = 316429) (by norm_num)
theorem B1777945 : Blo 1403521 1777945 := bbase (se 2 (by rfl) ⟨666729, by rfl⟩ : syracuseStep 1777945 = 1333459) (by norm_num)
theorem B2105645 : Blo 1403521 2105645 := bbase (se 3 (by rfl) ⟨394808, by rfl⟩ : syracuseStep 2105645 = 789617) (by norm_num)
theorem B1442113 : Blo 1403521 1442113 := bbase (se 2 (by rfl) ⟨540792, by rfl⟩ : syracuseStep 1442113 = 1081585) (by norm_num)
theorem B2105669 : Blo 1403521 2105669 := bbase (se 4 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 2105669 = 394813) (by norm_num)
theorem B12165461 : Blo 1403521 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B2105693 : Blo 1403521 2105693 := bbase (se 3 (by rfl) ⟨394817, by rfl⟩ : syracuseStep 2105693 = 789635) (by norm_num)
theorem B3555677 : Blo 1403521 3555677 := bbase (se 3 (by rfl) ⟨666689, by rfl⟩ : syracuseStep 3555677 = 1333379) (by norm_num)
theorem B2105717 : Blo 1403521 2105717 := bbase (se 5 (by rfl) ⟨98705, by rfl⟩ : syracuseStep 2105717 = 197411) (by norm_num)
theorem B1778041 : Blo 1403521 1778041 := bbase (se 2 (by rfl) ⟨666765, by rfl⟩ : syracuseStep 1778041 = 1333531) (by norm_num)
theorem B1999237 : Blo 1403521 1999237 := bbase (se 4 (by rfl) ⟨187428, by rfl⟩ : syracuseStep 1999237 = 374857) (by norm_num)
theorem B2105741 : Blo 1403521 2105741 := bbase (se 3 (by rfl) ⟨394826, by rfl⟩ : syracuseStep 2105741 = 789653) (by norm_num)
theorem B2105765 : Blo 1403521 2105765 := bbase (se 4 (by rfl) ⟨197415, by rfl⟩ : syracuseStep 2105765 = 394831) (by norm_num)
theorem B2105789 : Blo 1403521 2105789 := bbase (se 3 (by rfl) ⟨394835, by rfl⟩ : syracuseStep 2105789 = 789671) (by norm_num)
theorem B6668741 : Blo 1403521 6668741 := bbase (se 4 (by rfl) ⟨625194, by rfl⟩ : syracuseStep 6668741 = 1250389) (by norm_num)
theorem B3203525 : Blo 1403521 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B2105813 : Blo 1403521 2105813 := bbase (se 7 (by rfl) ⟨24677, by rfl⟩ : syracuseStep 2105813 = 49355) (by norm_num)
theorem B6406613 : Blo 1403521 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B2105837 : Blo 1403521 2105837 := bbase (se 3 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 2105837 = 789689) (by norm_num)
theorem B1499629 : Blo 1403521 1499629 := bbase (se 3 (by rfl) ⟨281180, by rfl⟩ : syracuseStep 1499629 = 562361) (by norm_num)
theorem B2105861 : Blo 1403521 2105861 := bbase (se 4 (by rfl) ⟨197424, by rfl⟩ : syracuseStep 2105861 = 394849) (by norm_num)
theorem B4497925 : Blo 1403521 4497925 := bbase (se 4 (by rfl) ⟨421680, by rfl⟩ : syracuseStep 4497925 = 843361) (by norm_num)
theorem B3203597 : Blo 1403521 3203597 := bbase (se 3 (by rfl) ⟨600674, by rfl⟩ : syracuseStep 3203597 = 1201349) (by norm_num)
theorem B25960981 : Blo 1403521 25960981 := bbase (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) (by norm_num)
theorem B2105885 : Blo 1403521 2105885 := bbase (se 3 (by rfl) ⟨394853, by rfl⟩ : syracuseStep 2105885 = 789707) (by norm_num)
theorem B1778213 : Blo 1403521 1778213 := bbase (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) (by norm_num)
theorem B2105909 : Blo 1403521 2105909 := bbase (se 5 (by rfl) ⟨98714, by rfl⟩ : syracuseStep 2105909 = 197429) (by norm_num)
theorem B2531893 : Blo 1403521 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B1688125 : Blo 1403521 1688125 := bbase (se 3 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 1688125 = 633047) (by norm_num)
theorem B2105933 : Blo 1403521 2105933 := bbase (se 3 (by rfl) ⟨394862, by rfl⟩ : syracuseStep 2105933 = 789725) (by norm_num)
theorem B1778269 : Blo 1403521 1778269 := bbase (se 3 (by rfl) ⟨333425, by rfl⟩ : syracuseStep 1778269 = 666851) (by norm_num)
theorem B2105957 : Blo 1403521 2105957 := bbase (se 4 (by rfl) ⟨197433, by rfl⟩ : syracuseStep 2105957 = 394867) (by norm_num)
theorem B2105981 : Blo 1403521 2105981 := bbase (se 3 (by rfl) ⟨394871, by rfl⟩ : syracuseStep 2105981 = 789743) (by norm_num)
theorem B2106005 : Blo 1403521 2106005 := bbase (se 6 (by rfl) ⟨49359, by rfl⟩ : syracuseStep 2106005 = 98719) (by norm_num)
theorem B2106029 : Blo 1403521 2106029 := bbase (se 3 (by rfl) ⟨394880, by rfl⟩ : syracuseStep 2106029 = 789761) (by norm_num)
theorem B3556021 : Blo 1403521 3556021 := bbase (se 5 (by rfl) ⟨166688, by rfl⟩ : syracuseStep 3556021 = 333377) (by norm_num)
theorem B1778365 : Blo 1403521 1778365 := bbase (se 3 (by rfl) ⟨333443, by rfl⟩ : syracuseStep 1778365 = 666887) (by norm_num)
theorem B2106053 : Blo 1403521 2106053 := bbase (se 4 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 2106053 = 394885) (by norm_num)
theorem B2106077 : Blo 1403521 2106077 := bbase (se 3 (by rfl) ⟨394889, by rfl⟩ : syracuseStep 2106077 = 789779) (by norm_num)
theorem B2106101 : Blo 1403521 2106101 := bbase (se 5 (by rfl) ⟨98723, by rfl⟩ : syracuseStep 2106101 = 197447) (by norm_num)
theorem B1999613 : Blo 1403521 1999613 := bbase (se 3 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 1999613 = 749855) (by norm_num)
theorem B4498181 : Blo 1403521 4498181 := bbase (se 4 (by rfl) ⟨421704, by rfl⟩ : syracuseStep 4498181 = 843409) (by norm_num)
theorem B2106125 : Blo 1403521 2106125 := bbase (se 3 (by rfl) ⟨394898, by rfl⟩ : syracuseStep 2106125 = 789797) (by norm_num)
theorem B9003797 : Blo 1403521 9003797 := bbase (se 6 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 9003797 = 422053) (by norm_num)
theorem B2106149 : Blo 1403521 2106149 := bbase (se 4 (by rfl) ⟨197451, by rfl⟩ : syracuseStep 2106149 = 394903) (by norm_num)
theorem B5694245 : Blo 1403521 5694245 := bbase (se 4 (by rfl) ⟨533835, by rfl⟩ : syracuseStep 5694245 = 1067671) (by norm_num)
theorem B3556133 : Blo 1403521 3556133 := bbase (se 4 (by rfl) ⟨333387, by rfl⟩ : syracuseStep 3556133 = 666775) (by norm_num)
theorem B2106173 : Blo 1403521 2106173 := bbase (se 3 (by rfl) ⟨394907, by rfl⟩ : syracuseStep 2106173 = 789815) (by norm_num)
theorem B2106197 : Blo 1403521 2106197 := bbase (se 9 (by rfl) ⟨6170, by rfl⟩ : syracuseStep 2106197 = 12341) (by norm_num)
theorem B1500005 : Blo 1403521 1500005 := bbase (se 4 (by rfl) ⟨140625, by rfl⟩ : syracuseStep 1500005 = 281251) (by norm_num)
theorem B1778537 : Blo 1403521 1778537 := bbase (se 2 (by rfl) ⟨666951, by rfl⟩ : syracuseStep 1778537 = 1333903) (by norm_num)
theorem B2106221 : Blo 1403521 2106221 := bbase (se 3 (by rfl) ⟨394916, by rfl⟩ : syracuseStep 2106221 = 789833) (by norm_num)
theorem B2106245 : Blo 1403521 2106245 := bbase (se 4 (by rfl) ⟨197460, by rfl⟩ : syracuseStep 2106245 = 394921) (by norm_num)
theorem B2106269 : Blo 1403521 2106269 := bbase (se 3 (by rfl) ⟨394925, by rfl⟩ : syracuseStep 2106269 = 789851) (by norm_num)
theorem B2999197 : Blo 1403521 2999197 := bbase (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) (by norm_num)
theorem B1778593 : Blo 1403521 1778593 := bbase (se 2 (by rfl) ⟨666972, by rfl⟩ : syracuseStep 1778593 = 1333945) (by norm_num)
theorem B1500077 : Blo 1403521 1500077 := bbase (se 3 (by rfl) ⟨281264, by rfl⟩ : syracuseStep 1500077 = 562529) (by norm_num)
theorem B2106293 : Blo 1403521 2106293 := bbase (se 5 (by rfl) ⟨98732, by rfl⟩ : syracuseStep 2106293 = 197465) (by norm_num)
theorem B2368453 : Blo 1403521 2368453 := bbase (se 4 (by rfl) ⟨222042, by rfl⟩ : syracuseStep 2368453 = 444085) (by norm_num)
theorem B5333957 : Blo 1403521 5333957 := bbase (se 4 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 5333957 = 1000117) (by norm_num)
theorem B2106317 : Blo 1403521 2106317 := bbase (se 3 (by rfl) ⟨394934, by rfl⟩ : syracuseStep 2106317 = 789869) (by norm_num)
theorem B7111637 : Blo 1403521 7111637 := bbase (se 7 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 7111637 = 166679) (by norm_num)
theorem B2106341 : Blo 1403521 2106341 := bbase (se 4 (by rfl) ⟨197469, by rfl⟩ : syracuseStep 2106341 = 394939) (by norm_num)
theorem B3556325 : Blo 1403521 3556325 := bbase (se 4 (by rfl) ⟨333405, by rfl⟩ : syracuseStep 3556325 = 666811) (by norm_num)
theorem B2106365 : Blo 1403521 2106365 := bbase (se 3 (by rfl) ⟨394943, by rfl⟩ : syracuseStep 2106365 = 789887) (by norm_num)
theorem B1778689 : Blo 1403521 1778689 := bbase (se 2 (by rfl) ⟨667008, by rfl⟩ : syracuseStep 1778689 = 1334017) (by norm_num)
theorem B2106389 : Blo 1403521 2106389 := bbase (se 6 (by rfl) ⟨49368, by rfl⟩ : syracuseStep 2106389 = 98737) (by norm_num)
theorem B2368541 : Blo 1403521 2368541 := bbase (se 3 (by rfl) ⟨444101, by rfl⟩ : syracuseStep 2368541 = 888203) (by norm_num)
theorem B2704421 : Blo 1403521 2704421 := bbase (se 4 (by rfl) ⟨253539, by rfl⟩ : syracuseStep 2704421 = 507079) (by norm_num)
theorem B2106413 : Blo 1403521 2106413 := bbase (se 3 (by rfl) ⟨394952, by rfl⟩ : syracuseStep 2106413 = 789905) (by norm_num)
theorem B2106437 : Blo 1403521 2106437 := bbase (se 4 (by rfl) ⟨197478, by rfl⟩ : syracuseStep 2106437 = 394957) (by norm_num)
theorem B2106461 : Blo 1403521 2106461 := bbase (se 3 (by rfl) ⟨394961, by rfl⟩ : syracuseStep 2106461 = 789923) (by norm_num)
theorem B1500265 : Blo 1403521 1500265 := bbase (se 2 (by rfl) ⟨562599, by rfl⟩ : syracuseStep 1500265 = 1125199) (by norm_num)
theorem B2106485 : Blo 1403521 2106485 := bbase (se 5 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 2106485 = 197483) (by norm_num)
theorem B2106509 : Blo 1403521 2106509 := bbase (se 3 (by rfl) ⟨394970, by rfl⟩ : syracuseStep 2106509 = 789941) (by norm_num)
theorem B8537237 : Blo 1403521 8537237 := bbase (se 6 (by rfl) ⟨200091, by rfl⟩ : syracuseStep 8537237 = 400183) (by norm_num)
theorem B2368669 : Blo 1403521 2368669 := bbase (se 3 (by rfl) ⟨444125, by rfl⟩ : syracuseStep 2368669 = 888251) (by norm_num)
theorem B5129381 : Blo 1403521 5129381 := bbase (se 4 (by rfl) ⟨480879, by rfl⟩ : syracuseStep 5129381 = 961759) (by norm_num)
theorem B2106533 : Blo 1403521 2106533 := bbase (se 4 (by rfl) ⟨197487, by rfl⟩ : syracuseStep 2106533 = 394975) (by norm_num)
theorem B1778861 : Blo 1403521 1778861 := bbase (se 3 (by rfl) ⟨333536, by rfl⟩ : syracuseStep 1778861 = 667073) (by norm_num)
theorem B2106557 : Blo 1403521 2106557 := bbase (se 3 (by rfl) ⟨394979, by rfl⟩ : syracuseStep 2106557 = 789959) (by norm_num)
theorem B2106581 : Blo 1403521 2106581 := bbase (se 7 (by rfl) ⟨24686, by rfl⟩ : syracuseStep 2106581 = 49373) (by norm_num)
theorem B5334245 : Blo 1403521 5334245 := bbase (se 4 (by rfl) ⟨500085, by rfl⟩ : syracuseStep 5334245 = 1000171) (by norm_num)
theorem B2106605 : Blo 1403521 2106605 := bbase (se 3 (by rfl) ⟨394988, by rfl⟩ : syracuseStep 2106605 = 789977) (by norm_num)
theorem B2368757 : Blo 1403521 2368757 := bbase (se 5 (by rfl) ⟨111035, by rfl⟩ : syracuseStep 2368757 = 222071) (by norm_num)
theorem B2106629 : Blo 1403521 2106629 := bbase (se 4 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 2106629 = 394993) (by norm_num)
theorem B2106653 : Blo 1403521 2106653 := bbase (se 3 (by rfl) ⟨394997, by rfl⟩ : syracuseStep 2106653 = 789995) (by norm_num)
theorem B1500449 : Blo 1403521 1500449 := bbase (se 2 (by rfl) ⟨562668, by rfl⟩ : syracuseStep 1500449 = 1125337) (by norm_num)
theorem B2106677 : Blo 1403521 2106677 := bbase (se 5 (by rfl) ⟨98750, by rfl⟩ : syracuseStep 2106677 = 197501) (by norm_num)
theorem B3556669 : Blo 1403521 3556669 := bbase (se 3 (by rfl) ⟨666875, by rfl⟩ : syracuseStep 3556669 = 1333751) (by norm_num)
theorem B2778437 : Blo 1403521 2778437 := bbase (se 4 (by rfl) ⟨260478, by rfl⟩ : syracuseStep 2778437 = 520957) (by norm_num)
theorem B2106701 : Blo 1403521 2106701 := bbase (se 3 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 2106701 = 790013) (by norm_num)
theorem B26994005 : Blo 1403521 26994005 := bbase (se 12 (by rfl) ⟨9885, by rfl⟩ : syracuseStep 26994005 = 19771) (by norm_num)
theorem B2532701 : Blo 1403521 2532701 := bbase (se 3 (by rfl) ⟨474881, by rfl⟩ : syracuseStep 2532701 = 949763) (by norm_num)
theorem B2106725 : Blo 1403521 2106725 := bbase (se 4 (by rfl) ⟨197505, by rfl⟩ : syracuseStep 2106725 = 395011) (by norm_num)
theorem B2368885 : Blo 1403521 2368885 := bbase (se 5 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 2368885 = 222083) (by norm_num)
theorem B2106749 : Blo 1403521 2106749 := bbase (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) (by norm_num)
theorem B2999693 : Blo 1403521 2999693 := bbase (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) (by norm_num)
theorem B2106773 : Blo 1403521 2106773 := bbase (se 6 (by rfl) ⟨49377, by rfl⟩ : syracuseStep 2106773 = 98755) (by norm_num)
theorem B2106797 : Blo 1403521 2106797 := bbase (se 3 (by rfl) ⟨395024, by rfl⟩ : syracuseStep 2106797 = 790049) (by norm_num)
theorem B3556781 : Blo 1403521 3556781 := bbase (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) (by norm_num)
theorem B2106821 : Blo 1403521 2106821 := bbase (se 4 (by rfl) ⟨197514, by rfl⟩ : syracuseStep 2106821 = 395029) (by norm_num)
theorem B2368973 : Blo 1403521 2368973 := bbase (se 3 (by rfl) ⟨444182, by rfl⟩ : syracuseStep 2368973 = 888365) (by norm_num)
theorem B2106845 : Blo 1403521 2106845 := bbase (se 3 (by rfl) ⟨395033, by rfl⟩ : syracuseStep 2106845 = 790067) (by norm_num)
theorem B3204581 : Blo 1403521 3204581 := bbase (se 4 (by rfl) ⟨300429, by rfl⟩ : syracuseStep 3204581 = 600859) (by norm_num)
theorem B2164205 : Blo 1403521 2164205 := bbase (se 3 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 2164205 = 811577) (by norm_num)
theorem B2106869 : Blo 1403521 2106869 := bbase (se 5 (by rfl) ⟨98759, by rfl⟩ : syracuseStep 2106869 = 197519) (by norm_num)
theorem B2106893 : Blo 1403521 2106893 := bbase (se 3 (by rfl) ⟨395042, by rfl⟩ : syracuseStep 2106893 = 790085) (by norm_num)
theorem B2106917 : Blo 1403521 2106917 := bbase (se 4 (by rfl) ⟨197523, by rfl⟩ : syracuseStep 2106917 = 395047) (by norm_num)
theorem B2106941 : Blo 1403521 2106941 := bbase (se 3 (by rfl) ⟨395051, by rfl⟩ : syracuseStep 2106941 = 790103) (by norm_num)
theorem B2369101 : Blo 1403521 2369101 := bbase (se 3 (by rfl) ⟨444206, by rfl⟩ : syracuseStep 2369101 = 888413) (by norm_num)
theorem B2106965 : Blo 1403521 2106965 := bbase (se 8 (by rfl) ⟨12345, by rfl⟩ : syracuseStep 2106965 = 24691) (by norm_num)
theorem B2106989 : Blo 1403521 2106989 := bbase (se 3 (by rfl) ⟨395060, by rfl⟩ : syracuseStep 2106989 = 790121) (by norm_num)
theorem B3556973 : Blo 1403521 3556973 := bbase (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) (by norm_num)
theorem B2107013 : Blo 1403521 2107013 := bbase (se 4 (by rfl) ⟨197532, by rfl⟩ : syracuseStep 2107013 = 395065) (by norm_num)
theorem B2107037 : Blo 1403521 2107037 := bbase (se 3 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 2107037 = 790139) (by norm_num)
theorem B2369189 : Blo 1403521 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B2107061 : Blo 1403521 2107061 := bbase (se 5 (by rfl) ⟨98768, by rfl⟩ : syracuseStep 2107061 = 197537) (by norm_num)
theorem B2164429 : Blo 1403521 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B2107085 : Blo 1403521 2107085 := bbase (se 3 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 2107085 = 790157) (by norm_num)
theorem B2107109 : Blo 1403521 2107109 := bbase (se 4 (by rfl) ⟨197541, by rfl⟩ : syracuseStep 2107109 = 395083) (by norm_num)
theorem B10397429 : Blo 1403521 10397429 := bbase (se 5 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 10397429 = 974759) (by norm_num)
theorem B2107133 : Blo 1403521 2107133 := bbase (se 3 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 2107133 = 790175) (by norm_num)
theorem B2107157 : Blo 1403521 2107157 := bbase (se 6 (by rfl) ⟨49386, by rfl⟩ : syracuseStep 2107157 = 98773) (by norm_num)
theorem B2369317 : Blo 1403521 2369317 := bbase (se 4 (by rfl) ⟨222123, by rfl⟩ : syracuseStep 2369317 = 444247) (by norm_num)
theorem B2107181 : Blo 1403521 2107181 := bbase (se 3 (by rfl) ⟨395096, by rfl⟩ : syracuseStep 2107181 = 790193) (by norm_num)
theorem B3999557 : Blo 1403521 3999557 := bbase (se 4 (by rfl) ⟨374958, by rfl⟩ : syracuseStep 3999557 = 749917) (by norm_num)
theorem B2107205 : Blo 1403521 2107205 := bbase (se 4 (by rfl) ⟨197550, by rfl⟩ : syracuseStep 2107205 = 395101) (by norm_num)
theorem B3376981 : Blo 1403521 3376981 := bbase (se 9 (by rfl) ⟨9893, by rfl⟩ : syracuseStep 3376981 = 19787) (by norm_num)
theorem B2107229 : Blo 1403521 2107229 := bbase (se 3 (by rfl) ⟨395105, by rfl⟩ : syracuseStep 2107229 = 790211) (by norm_num)
theorem B2107253 : Blo 1403521 2107253 := bbase (se 5 (by rfl) ⟨98777, by rfl⟩ : syracuseStep 2107253 = 197555) (by norm_num)
theorem B2369405 : Blo 1403521 2369405 := bbase (se 3 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 2369405 = 888527) (by norm_num)
theorem B2107277 : Blo 1403521 2107277 := bbase (se 3 (by rfl) ⟨395114, by rfl⟩ : syracuseStep 2107277 = 790229) (by norm_num)
theorem B4736933 : Blo 1403521 4736933 := bbase (se 4 (by rfl) ⟨444087, by rfl⟩ : syracuseStep 4736933 = 888175) (by norm_num)
theorem B2107301 : Blo 1403521 2107301 := bbase (se 4 (by rfl) ⟨197559, by rfl⟩ : syracuseStep 2107301 = 395119) (by norm_num)
theorem B2107325 : Blo 1403521 2107325 := bbase (se 3 (by rfl) ⟨395123, by rfl⟩ : syracuseStep 2107325 = 790247) (by norm_num)
theorem B3557317 : Blo 1403521 3557317 := bbase (se 4 (by rfl) ⟨333498, by rfl⟩ : syracuseStep 3557317 = 666997) (by norm_num)
theorem B2107349 : Blo 1403521 2107349 := bbase (se 7 (by rfl) ⟨24695, by rfl⟩ : syracuseStep 2107349 = 49391) (by norm_num)
theorem B2107373 : Blo 1403521 2107373 := bbase (se 3 (by rfl) ⟨395132, by rfl⟩ : syracuseStep 2107373 = 790265) (by norm_num)
theorem B2369533 : Blo 1403521 2369533 := bbase (se 3 (by rfl) ⟨444287, by rfl⟩ : syracuseStep 2369533 = 888575) (by norm_num)
theorem B2107397 : Blo 1403521 2107397 := bbase (se 4 (by rfl) ⟨197568, by rfl⟩ : syracuseStep 2107397 = 395137) (by norm_num)
theorem B12003349 : Blo 1403521 12003349 := bbase (se 6 (by rfl) ⟨281328, by rfl⟩ : syracuseStep 12003349 = 562657) (by norm_num)
theorem B2107421 : Blo 1403521 2107421 := bbase (se 3 (by rfl) ⟨395141, by rfl⟩ : syracuseStep 2107421 = 790283) (by norm_num)
theorem B2107445 : Blo 1403521 2107445 := bbase (se 5 (by rfl) ⟨98786, by rfl⟩ : syracuseStep 2107445 = 197573) (by norm_num)
theorem B3557429 : Blo 1403521 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B2107469 : Blo 1403521 2107469 := bbase (se 3 (by rfl) ⟨395150, by rfl⟩ : syracuseStep 2107469 = 790301) (by norm_num)
theorem B2369621 : Blo 1403521 2369621 := bbase (se 8 (by rfl) ⟨13884, by rfl⟩ : syracuseStep 2369621 = 27769) (by norm_num)
theorem B2107493 : Blo 1403521 2107493 := bbase (se 4 (by rfl) ⟨197577, by rfl⟩ : syracuseStep 2107493 = 395155) (by norm_num)
theorem B2107517 : Blo 1403521 2107517 := bbase (se 3 (by rfl) ⟨395159, by rfl⟩ : syracuseStep 2107517 = 790319) (by norm_num)
theorem B2001037 : Blo 1403521 2001037 := bbase (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) (by norm_num)
theorem B2107541 : Blo 1403521 2107541 := bbase (se 6 (by rfl) ⟨49395, by rfl⟩ : syracuseStep 2107541 = 98791) (by norm_num)
theorem B2107565 : Blo 1403521 2107565 := bbase (se 3 (by rfl) ⟨395168, by rfl⟩ : syracuseStep 2107565 = 790337) (by norm_num)
theorem B2107589 : Blo 1403521 2107589 := bbase (se 4 (by rfl) ⟨197586, by rfl⟩ : syracuseStep 2107589 = 395173) (by norm_num)
theorem B2369749 : Blo 1403521 2369749 := bbase (se 7 (by rfl) ⟨27770, by rfl⟩ : syracuseStep 2369749 = 55541) (by norm_num)
theorem B5998805 : Blo 1403521 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B2107613 : Blo 1403521 2107613 := bbase (se 3 (by rfl) ⟨395177, by rfl⟩ : syracuseStep 2107613 = 790355) (by norm_num)
theorem B2664677 : Blo 1403521 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B7112933 : Blo 1403521 7112933 := bbase (se 4 (by rfl) ⟨666837, by rfl⟩ : syracuseStep 7112933 = 1333675) (by norm_num)
theorem B3000557 : Blo 1403521 3000557 := bbase (se 3 (by rfl) ⟨562604, by rfl⟩ : syracuseStep 3000557 = 1125209) (by norm_num)
theorem B2107637 : Blo 1403521 2107637 := bbase (se 5 (by rfl) ⟨98795, by rfl⟩ : syracuseStep 2107637 = 197591) (by norm_num)
theorem B3557621 : Blo 1403521 3557621 := bbase (se 5 (by rfl) ⟨166763, by rfl⟩ : syracuseStep 3557621 = 333527) (by norm_num)
theorem B2107661 : Blo 1403521 2107661 := bbase (se 3 (by rfl) ⟨395186, by rfl⟩ : syracuseStep 2107661 = 790373) (by norm_num)
theorem B2107685 : Blo 1403521 2107685 := bbase (se 4 (by rfl) ⟨197595, by rfl⟩ : syracuseStep 2107685 = 395191) (by norm_num)
theorem B2369837 : Blo 1403521 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B2107709 : Blo 1403521 2107709 := bbase (se 3 (by rfl) ⟨395195, by rfl⟩ : syracuseStep 2107709 = 790391) (by norm_num)
theorem B4737365 : Blo 1403521 4737365 := bbase (se 10 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 4737365 = 13879) (by norm_num)
theorem B2107733 : Blo 1403521 2107733 := bbase (se 10 (by rfl) ⟨3087, by rfl⟩ : syracuseStep 2107733 = 6175) (by norm_num)
theorem B2107757 : Blo 1403521 2107757 := bbase (se 3 (by rfl) ⟨395204, by rfl⟩ : syracuseStep 2107757 = 790409) (by norm_num)
theorem B2664829 : Blo 1403521 2664829 := bbase (se 3 (by rfl) ⟨499655, by rfl⟩ : syracuseStep 2664829 = 999311) (by norm_num)
theorem B3000701 : Blo 1403521 3000701 := bbase (se 3 (by rfl) ⟨562631, by rfl⟩ : syracuseStep 3000701 = 1125263) (by norm_num)
theorem B2107781 : Blo 1403521 2107781 := bbase (se 4 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 2107781 = 395209) (by norm_num)
theorem B5335429 : Blo 1403521 5335429 := bbase (se 4 (by rfl) ⟨500196, by rfl⟩ : syracuseStep 5335429 = 1000393) (by norm_num)
theorem B2107805 : Blo 1403521 2107805 := bbase (se 3 (by rfl) ⟨395213, by rfl⟩ : syracuseStep 2107805 = 790427) (by norm_num)
theorem B2369965 : Blo 1403521 2369965 := bbase (se 3 (by rfl) ⟨444368, by rfl⟩ : syracuseStep 2369965 = 888737) (by norm_num)
theorem B2107829 : Blo 1403521 2107829 := bbase (se 5 (by rfl) ⟨98804, by rfl⟩ : syracuseStep 2107829 = 197609) (by norm_num)
theorem B2107853 : Blo 1403521 2107853 := bbase (se 3 (by rfl) ⟨395222, by rfl⟩ : syracuseStep 2107853 = 790445) (by norm_num)
theorem B4000229 : Blo 1403521 4000229 := bbase (se 4 (by rfl) ⟨375021, by rfl⟩ : syracuseStep 4000229 = 750043) (by norm_num)
theorem B2107877 : Blo 1403521 2107877 := bbase (se 4 (by rfl) ⟨197613, by rfl⟩ : syracuseStep 2107877 = 395227) (by norm_num)
theorem B2107901 : Blo 1403521 2107901 := bbase (se 3 (by rfl) ⟨395231, by rfl⟩ : syracuseStep 2107901 = 790463) (by norm_num)
theorem B2370053 : Blo 1403521 2370053 := bbase (se 4 (by rfl) ⟨222192, by rfl⟩ : syracuseStep 2370053 = 444385) (by norm_num)
theorem B2107925 : Blo 1403521 2107925 := bbase (se 6 (by rfl) ⟨49404, by rfl⟩ : syracuseStep 2107925 = 98809) (by norm_num)
theorem B2107949 : Blo 1403521 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B2107973 : Blo 1403521 2107973 := bbase (se 4 (by rfl) ⟨197622, by rfl⟩ : syracuseStep 2107973 = 395245) (by norm_num)
theorem B2107997 : Blo 1403521 2107997 := bbase (se 3 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 2107997 = 790499) (by norm_num)
theorem B2108021 : Blo 1403521 2108021 := bbase (se 5 (by rfl) ⟨98813, by rfl⟩ : syracuseStep 2108021 = 197627) (by norm_num)
theorem B2370181 : Blo 1403521 2370181 := bbase (se 4 (by rfl) ⟨222204, by rfl⟩ : syracuseStep 2370181 = 444409) (by norm_num)
theorem B2108045 : Blo 1403521 2108045 := bbase (se 3 (by rfl) ⟨395258, by rfl⟩ : syracuseStep 2108045 = 790517) (by norm_num)
theorem B2108069 : Blo 1403521 2108069 := bbase (se 4 (by rfl) ⟨197631, by rfl⟩ : syracuseStep 2108069 = 395263) (by norm_num)
theorem B2665133 : Blo 1403521 2665133 := bbase (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) (by norm_num)
theorem B5335733 : Blo 1403521 5335733 := bbase (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) (by norm_num)
theorem B2108093 : Blo 1403521 2108093 := bbase (se 3 (by rfl) ⟨395267, by rfl⟩ : syracuseStep 2108093 = 790535) (by norm_num)
theorem B2108117 : Blo 1403521 2108117 := bbase (se 7 (by rfl) ⟨24704, by rfl⟩ : syracuseStep 2108117 = 49409) (by norm_num)
theorem B2370269 : Blo 1403521 2370269 := bbase (se 3 (by rfl) ⟨444425, by rfl⟩ : syracuseStep 2370269 = 888851) (by norm_num)
theorem B2108141 : Blo 1403521 2108141 := bbase (se 3 (by rfl) ⟨395276, by rfl⟩ : syracuseStep 2108141 = 790553) (by norm_num)
theorem B4737797 : Blo 1403521 4737797 := bbase (se 4 (by rfl) ⟨444168, by rfl⟩ : syracuseStep 4737797 = 888337) (by norm_num)
theorem B2108165 : Blo 1403521 2108165 := bbase (se 4 (by rfl) ⟨197640, by rfl⟩ : syracuseStep 2108165 = 395281) (by norm_num)
theorem B2108189 : Blo 1403521 2108189 := bbase (se 3 (by rfl) ⟨395285, by rfl⟩ : syracuseStep 2108189 = 790571) (by norm_num)
theorem B2108213 : Blo 1403521 2108213 := bbase (se 5 (by rfl) ⟨98822, by rfl⟩ : syracuseStep 2108213 = 197645) (by norm_num)
theorem B2108237 : Blo 1403521 2108237 := bbase (se 3 (by rfl) ⟨395294, by rfl⟩ : syracuseStep 2108237 = 790589) (by norm_num)
theorem B2370397 : Blo 1403521 2370397 := bbase (se 3 (by rfl) ⟨444449, by rfl⟩ : syracuseStep 2370397 = 888899) (by norm_num)
theorem B2108261 : Blo 1403521 2108261 := bbase (se 4 (by rfl) ⟨197649, by rfl⟩ : syracuseStep 2108261 = 395299) (by norm_num)
theorem B2845549 : Blo 1403521 2845549 := bbase (se 3 (by rfl) ⟨533540, by rfl⟩ : syracuseStep 2845549 = 1067081) (by norm_num)
theorem B13495157 : Blo 1403521 13495157 := bbase (se 5 (by rfl) ⟨632585, by rfl⟩ : syracuseStep 13495157 = 1265171) (by norm_num)
theorem B4000661 : Blo 1403521 4000661 := bbase (se 6 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 4000661 = 187531) (by norm_num)
theorem B2370485 : Blo 1403521 2370485 := bbase (se 5 (by rfl) ⟨111116, by rfl⟩ : syracuseStep 2370485 = 222233) (by norm_num)
theorem B6753269 : Blo 1403521 6753269 := bbase (se 5 (by rfl) ⟨316559, by rfl⟩ : syracuseStep 6753269 = 633119) (by norm_num)
theorem B2370613 : Blo 1403521 2370613 := bbase (se 5 (by rfl) ⟨111122, by rfl⟩ : syracuseStep 2370613 = 222245) (by norm_num)
theorem B5696581 : Blo 1403521 5696581 := bbase (se 4 (by rfl) ⟨534054, by rfl⟩ : syracuseStep 5696581 = 1068109) (by norm_num)
theorem B3001445 : Blo 1403521 3001445 := bbase (se 4 (by rfl) ⟨281385, by rfl⟩ : syracuseStep 3001445 = 562771) (by norm_num)
theorem B1600645 : Blo 1403521 1600645 := bbase (se 4 (by rfl) ⟨150060, by rfl⟩ : syracuseStep 1600645 = 300121) (by norm_num)
theorem B2370701 : Blo 1403521 2370701 := bbase (se 3 (by rfl) ⟨444506, by rfl⟩ : syracuseStep 2370701 = 889013) (by norm_num)
theorem B4738229 : Blo 1403521 4738229 := bbase (se 5 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 4738229 = 444209) (by norm_num)
theorem B2370829 : Blo 1403521 2370829 := bbase (se 3 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 2370829 = 889061) (by norm_num)
theorem B2436389 : Blo 1403521 2436389 := bbase (se 4 (by rfl) ⟨228411, by rfl⟩ : syracuseStep 2436389 = 456823) (by norm_num)
theorem B3042613 : Blo 1403521 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B2370917 : Blo 1403521 2370917 := bbase (se 4 (by rfl) ⟨222273, by rfl⟩ : syracuseStep 2370917 = 444547) (by norm_num)
theorem B2665885 : Blo 1403521 2665885 := bbase (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) (by norm_num)
theorem B4500949 : Blo 1403521 4500949 := bbase (se 7 (by rfl) ⟨52745, by rfl⟩ : syracuseStep 4500949 = 105491) (by norm_num)
theorem B2371045 : Blo 1403521 2371045 := bbase (se 4 (by rfl) ⟨222285, by rfl⟩ : syracuseStep 2371045 = 444571) (by norm_num)
theorem B1687549 : Blo 1403521 1687549 := bbase (se 3 (by rfl) ⟨316415, by rfl⟩ : syracuseStep 1687549 = 632831) (by norm_num)
theorem B7114229 : Blo 1403521 7114229 := bbase (se 5 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 7114229 = 666959) (by norm_num)
theorem B2666029 : Blo 1403521 2666029 := bbase (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) (by norm_num)
theorem B2371133 : Blo 1403521 2371133 := bbase (se 3 (by rfl) ⟨444587, by rfl⟩ : syracuseStep 2371133 = 889175) (by norm_num)
theorem B4738661 : Blo 1403521 4738661 := bbase (se 4 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 4738661 = 888499) (by norm_num)
theorem B11382389 : Blo 1403521 11382389 := bbase (se 5 (by rfl) ⟨533549, by rfl⟩ : syracuseStep 11382389 = 1067099) (by norm_num)
theorem B4001413 : Blo 1403521 4001413 := bbase (se 4 (by rfl) ⟨375132, by rfl⟩ : syracuseStep 4001413 = 750265) (by norm_num)
theorem B2371261 : Blo 1403521 2371261 := bbase (se 3 (by rfl) ⟨444611, by rfl⟩ : syracuseStep 2371261 = 889223) (by norm_num)
theorem B2666189 : Blo 1403521 2666189 := bbase (se 3 (by rfl) ⟨499910, by rfl⟩ : syracuseStep 2666189 = 999821) (by norm_num)
theorem B1519349 : Blo 1403521 1519349 := bbase (se 5 (by rfl) ⟨71219, by rfl⟩ : syracuseStep 1519349 = 142439) (by norm_num)
theorem B2371349 : Blo 1403521 2371349 := bbase (se 6 (by rfl) ⟨55578, by rfl⟩ : syracuseStep 2371349 = 111157) (by norm_num)
theorem B3247933 : Blo 1403521 3247933 := bbase (se 3 (by rfl) ⟨608987, by rfl⟩ : syracuseStep 3247933 = 1217975) (by norm_num)
theorem B2666333 : Blo 1403521 2666333 := bbase (se 3 (by rfl) ⟨499937, by rfl⟩ : syracuseStep 2666333 = 999875) (by norm_num)
theorem B7106453 : Blo 1403521 7106453 := bbase (se 6 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 7106453 = 333115) (by norm_num)
theorem B2371477 : Blo 1403521 2371477 := bbase (se 6 (by rfl) ⟨55581, by rfl⟩ : syracuseStep 2371477 = 111163) (by norm_num)
theorem B6000581 : Blo 1403521 6000581 := bbase (se 4 (by rfl) ⟨562554, by rfl⟩ : syracuseStep 6000581 = 1125109) (by norm_num)
theorem B3157973 : Blo 1403521 3157973 := bbase (se 7 (by rfl) ⟨37007, by rfl⟩ : syracuseStep 3157973 = 74015) (by norm_num)
theorem B12005333 : Blo 1403521 12005333 := bbase (se 7 (by rfl) ⟨140687, by rfl⟩ : syracuseStep 12005333 = 281375) (by norm_num)
theorem B2846693 : Blo 1403521 2846693 := bbase (se 4 (by rfl) ⟨266877, by rfl⟩ : syracuseStep 2846693 = 533755) (by norm_num)
theorem B2371565 : Blo 1403521 2371565 := bbase (se 3 (by rfl) ⟨444668, by rfl⟩ : syracuseStep 2371565 = 889337) (by norm_num)
theorem B4739093 : Blo 1403521 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B3158045 : Blo 1403521 3158045 := bbase (se 3 (by rfl) ⟨592133, by rfl⟩ : syracuseStep 3158045 = 1184267) (by norm_num)
theorem B3158117 : Blo 1403521 3158117 := bbase (se 4 (by rfl) ⟨296073, by rfl⟩ : syracuseStep 3158117 = 592147) (by norm_num)
theorem B2371693 : Blo 1403521 2371693 := bbase (se 3 (by rfl) ⟨444692, by rfl⟩ : syracuseStep 2371693 = 889385) (by norm_num)
theorem B2666621 : Blo 1403521 2666621 := bbase (se 3 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 2666621 = 999983) (by norm_num)
theorem B3158189 : Blo 1403521 3158189 := bbase (se 3 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 3158189 = 1184321) (by norm_num)
theorem B2371781 : Blo 1403521 2371781 := bbase (se 4 (by rfl) ⟨222354, by rfl⟩ : syracuseStep 2371781 = 444709) (by norm_num)
theorem B10809557 : Blo 1403521 10809557 := bbase (se 7 (by rfl) ⟨126674, by rfl⟩ : syracuseStep 10809557 = 253349) (by norm_num)
theorem B3158261 : Blo 1403521 3158261 := bbase (se 5 (by rfl) ⟨148043, by rfl⟩ : syracuseStep 3158261 = 296087) (by norm_num)
theorem B2666773 : Blo 1403521 2666773 := bbase (se 6 (by rfl) ⟨62502, by rfl⟩ : syracuseStep 2666773 = 125005) (by norm_num)
theorem B3158333 : Blo 1403521 3158333 := bbase (se 3 (by rfl) ⟨592187, by rfl⟩ : syracuseStep 3158333 = 1184375) (by norm_num)
theorem B6746485 : Blo 1403521 6746485 := bbase (se 5 (by rfl) ⟨316241, by rfl⟩ : syracuseStep 6746485 = 632483) (by norm_num)
theorem B3158405 : Blo 1403521 3158405 := bbase (se 4 (by rfl) ⟨296100, by rfl⟩ : syracuseStep 3158405 = 592201) (by norm_num)
theorem B2249117 : Blo 1403521 2249117 := bbase (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) (by norm_num)
theorem B4739525 : Blo 1403521 4739525 := bbase (se 4 (by rfl) ⟨444330, by rfl⟩ : syracuseStep 4739525 = 888661) (by norm_num)
theorem B3158477 : Blo 1403521 3158477 := bbase (se 3 (by rfl) ⟨592214, by rfl⟩ : syracuseStep 3158477 = 1184429) (by norm_num)
theorem B3158549 : Blo 1403521 3158549 := bbase (se 6 (by rfl) ⟨74028, by rfl⟩ : syracuseStep 3158549 = 148057) (by norm_num)
theorem B5403173 : Blo 1403521 5403173 := bbase (se 4 (by rfl) ⟨506547, by rfl⟩ : syracuseStep 5403173 = 1013095) (by norm_num)
theorem B2667077 : Blo 1403521 2667077 := bbase (se 4 (by rfl) ⟨250038, by rfl⟩ : syracuseStep 2667077 = 500077) (by norm_num)
theorem B3158621 : Blo 1403521 3158621 := bbase (se 3 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 3158621 = 1184483) (by norm_num)
theorem B2249309 : Blo 1403521 2249309 := bbase (se 3 (by rfl) ⟨421745, by rfl⟩ : syracuseStep 2249309 = 843491) (by norm_num)
theorem B6402725 : Blo 1403521 6402725 := bbase (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) (by norm_num)
theorem B3158693 : Blo 1403521 3158693 := bbase (se 4 (by rfl) ⟨296127, by rfl⟩ : syracuseStep 3158693 = 592255) (by norm_num)
theorem B6410917 : Blo 1403521 6410917 := bbase (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) (by norm_num)
theorem B3158765 : Blo 1403521 3158765 := bbase (se 3 (by rfl) ⟨592268, by rfl⟩ : syracuseStep 3158765 = 1184537) (by norm_num)
theorem B3158837 : Blo 1403521 3158837 := bbase (se 5 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 3158837 = 296141) (by norm_num)
theorem B4739957 : Blo 1403521 4739957 := bbase (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) (by norm_num)
theorem B3158909 : Blo 1403521 3158909 := bbase (se 3 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 3158909 = 1184591) (by norm_num)
theorem B1602433 : Blo 1403521 1602433 := bbase (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) (by norm_num)
theorem B6001573 : Blo 1403521 6001573 := bbase (se 4 (by rfl) ⟨562647, by rfl⟩ : syracuseStep 6001573 = 1125295) (by norm_num)
theorem B1602473 : Blo 1403521 1602473 := bbase (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) (by norm_num)
theorem B3158981 : Blo 1403521 3158981 := bbase (se 4 (by rfl) ⟨296154, by rfl⟩ : syracuseStep 3158981 = 592309) (by norm_num)
theorem B3159053 : Blo 1403521 3159053 := bbase (se 3 (by rfl) ⟨592322, by rfl⟩ : syracuseStep 3159053 = 1184645) (by norm_num)
theorem B1733713 : Blo 1403521 1733713 := bbase (se 2 (by rfl) ⟨650142, by rfl⟩ : syracuseStep 1733713 = 1300285) (by norm_num)
theorem B3159125 : Blo 1403521 3159125 := bbase (se 8 (by rfl) ⟨18510, by rfl⟩ : syracuseStep 3159125 = 37021) (by norm_num)
theorem B5330069 : Blo 1403521 5330069 := bbase (se 6 (by rfl) ⟨124923, by rfl⟩ : syracuseStep 5330069 = 249847) (by norm_num)
theorem B3159197 : Blo 1403521 3159197 := bbase (se 3 (by rfl) ⟨592349, by rfl⟩ : syracuseStep 3159197 = 1184699) (by norm_num)
theorem B7107749 : Blo 1403521 7107749 := bbase (se 4 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 7107749 = 1332703) (by norm_num)
theorem B3798197 : Blo 1403521 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B3159269 : Blo 1403521 3159269 := bbase (se 4 (by rfl) ⟨296181, by rfl⟩ : syracuseStep 3159269 = 592363) (by norm_num)
theorem B4560101 : Blo 1403521 4560101 := bbase (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) (by norm_num)
theorem B4740389 : Blo 1403521 4740389 := bbase (se 4 (by rfl) ⟨444411, by rfl⟩ : syracuseStep 4740389 = 888823) (by norm_num)
theorem B3159341 : Blo 1403521 3159341 := bbase (se 3 (by rfl) ⟨592376, by rfl⟩ : syracuseStep 3159341 = 1184753) (by norm_num)
theorem B2667829 : Blo 1403521 2667829 := bbase (se 5 (by rfl) ⟨125054, by rfl⟩ : syracuseStep 2667829 = 250109) (by norm_num)
theorem B3372349 : Blo 1403521 3372349 := bbase (se 3 (by rfl) ⟨632315, by rfl⟩ : syracuseStep 3372349 = 1264631) (by norm_num)
theorem B3159413 : Blo 1403521 3159413 := bbase (se 5 (by rfl) ⟨148097, by rfl⟩ : syracuseStep 3159413 = 296195) (by norm_num)
theorem B4871573 : Blo 1403521 4871573 := bbase (se 6 (by rfl) ⟨114177, by rfl⟩ : syracuseStep 4871573 = 228355) (by norm_num)
theorem B3372445 : Blo 1403521 3372445 := bbase (se 3 (by rfl) ⟨632333, by rfl⟩ : syracuseStep 3372445 = 1264667) (by norm_num)
theorem B5330357 : Blo 1403521 5330357 := bbase (se 5 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 5330357 = 499721) (by norm_num)
theorem B3159485 : Blo 1403521 3159485 := bbase (se 3 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 3159485 = 1184807) (by norm_num)
theorem B2667973 : Blo 1403521 2667973 := bbase (se 4 (by rfl) ⟨250122, by rfl⟩ : syracuseStep 2667973 = 500245) (by norm_num)
theorem B38426069 : Blo 1403521 38426069 := bbase (se 7 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 38426069 = 900611) (by norm_num)
theorem B3159557 : Blo 1403521 3159557 := bbase (se 4 (by rfl) ⟨296208, by rfl⟩ : syracuseStep 3159557 = 592417) (by norm_num)
theorem B3552781 : Blo 1403521 3552781 := bbase (se 3 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 3552781 = 1332293) (by norm_num)
theorem B3159629 : Blo 1403521 3159629 := bbase (se 3 (by rfl) ⟨592430, by rfl⟩ : syracuseStep 3159629 = 1184861) (by norm_num)
theorem B73021013 : Blo 1403521 73021013 := bbase (se 8 (by rfl) ⟨427857, by rfl⟩ : syracuseStep 73021013 = 855715) (by norm_num)
theorem B3372637 : Blo 1403521 3372637 := bbase (se 3 (by rfl) ⟨632369, by rfl⟩ : syracuseStep 3372637 = 1264739) (by norm_num)
theorem B2668133 : Blo 1403521 2668133 := bbase (se 4 (by rfl) ⟨250137, by rfl⟩ : syracuseStep 2668133 = 500275) (by norm_num)
theorem B3552893 : Blo 1403521 3552893 := bbase (se 3 (by rfl) ⟨666167, by rfl⟩ : syracuseStep 3552893 = 1332335) (by norm_num)
theorem B3159701 : Blo 1403521 3159701 := bbase (se 6 (by rfl) ⟨74055, by rfl⟩ : syracuseStep 3159701 = 148111) (by norm_num)
theorem B4740821 : Blo 1403521 4740821 := bbase (se 7 (by rfl) ⟨55556, by rfl⟩ : syracuseStep 4740821 = 111113) (by norm_num)
theorem B3159773 : Blo 1403521 3159773 := bbase (se 3 (by rfl) ⟨592457, by rfl⟩ : syracuseStep 3159773 = 1184915) (by norm_num)
theorem B2668277 : Blo 1403521 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B3159845 : Blo 1403521 3159845 := bbase (se 4 (by rfl) ⟨296235, by rfl⟩ : syracuseStep 3159845 = 592471) (by norm_num)
theorem B4331317 : Blo 1403521 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B3553085 : Blo 1403521 3553085 := bbase (se 3 (by rfl) ⟨666203, by rfl⟩ : syracuseStep 3553085 = 1332407) (by norm_num)
theorem B3159917 : Blo 1403521 3159917 := bbase (se 3 (by rfl) ⟨592484, by rfl⟩ : syracuseStep 3159917 = 1184969) (by norm_num)
theorem B1423217 : Blo 1403521 1423217 := bbase (se 2 (by rfl) ⟨533706, by rfl⟩ : syracuseStep 1423217 = 1067413) (by norm_num)
theorem B1423229 : Blo 1403521 1423229 := bbase (se 3 (by rfl) ⟨266855, by rfl⟩ : syracuseStep 1423229 = 533711) (by norm_num)
theorem B11384725 : Blo 1403521 11384725 := bbase (se 6 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 11384725 = 533659) (by norm_num)
theorem B3372965 : Blo 1403521 3372965 := bbase (se 4 (by rfl) ⟨316215, by rfl⟩ : syracuseStep 3372965 = 632431) (by norm_num)
theorem B3159989 : Blo 1403521 3159989 := bbase (se 5 (by rfl) ⟨148124, by rfl⟩ : syracuseStep 3159989 = 296249) (by norm_num)
theorem B3651533 : Blo 1403521 3651533 := bbase (se 3 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 3651533 = 1369325) (by norm_num)
theorem B1578973 : Blo 1403521 1578973 := bbase (se 3 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 1578973 = 592115) (by norm_num)
theorem B3160061 : Blo 1403521 3160061 := bbase (se 3 (by rfl) ⟨592511, by rfl⟩ : syracuseStep 3160061 = 1185023) (by norm_num)
theorem B1579009 : Blo 1403521 1579009 := bbase (se 2 (by rfl) ⟨592128, by rfl⟩ : syracuseStep 1579009 = 1184257) (by norm_num)
theorem B2250757 : Blo 1403521 2250757 := bbase (se 4 (by rfl) ⟨211008, by rfl⟩ : syracuseStep 2250757 = 422017) (by norm_num)
theorem B1579045 : Blo 1403521 1579045 := bbase (se 4 (by rfl) ⟨148035, by rfl⟩ : syracuseStep 1579045 = 296071) (by norm_num)
theorem B3160133 : Blo 1403521 3160133 := bbase (se 4 (by rfl) ⟨296262, by rfl⟩ : syracuseStep 3160133 = 592525) (by norm_num)
theorem B1579081 : Blo 1403521 1579081 := bbase (se 2 (by rfl) ⟨592155, by rfl⟩ : syracuseStep 1579081 = 1184311) (by norm_num)
theorem B8992853 : Blo 1403521 8992853 := bbase (se 8 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 8992853 = 105385) (by norm_num)
theorem B1579117 : Blo 1403521 1579117 := bbase (se 3 (by rfl) ⟨296084, by rfl⟩ : syracuseStep 1579117 = 592169) (by norm_num)
theorem B4741253 : Blo 1403521 4741253 := bbase (se 4 (by rfl) ⟨444492, by rfl⟩ : syracuseStep 4741253 = 888985) (by norm_num)
theorem B3160205 : Blo 1403521 3160205 := bbase (se 3 (by rfl) ⟨592538, by rfl⟩ : syracuseStep 3160205 = 1185077) (by norm_num)
theorem B1579153 : Blo 1403521 1579153 := bbase (se 2 (by rfl) ⟨592182, by rfl⟩ : syracuseStep 1579153 = 1184365) (by norm_num)
theorem B3553429 : Blo 1403521 3553429 := bbase (se 6 (by rfl) ⟨83283, by rfl⟩ : syracuseStep 3553429 = 166567) (by norm_num)
theorem B1579189 : Blo 1403521 1579189 := bbase (se 5 (by rfl) ⟨74024, by rfl⟩ : syracuseStep 1579189 = 148049) (by norm_num)
theorem B1898677 : Blo 1403521 1898677 := bbase (se 5 (by rfl) ⟨89000, by rfl⟩ : syracuseStep 1898677 = 178001) (by norm_num)
theorem B3160277 : Blo 1403521 3160277 := bbase (se 7 (by rfl) ⟨37034, by rfl⟩ : syracuseStep 3160277 = 74069) (by norm_num)
theorem B1579225 : Blo 1403521 1579225 := bbase (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) (by norm_num)
theorem B1423577 : Blo 1403521 1423577 := bbase (se 2 (by rfl) ⟨533841, by rfl⟩ : syracuseStep 1423577 = 1067683) (by norm_num)
theorem B4806901 : Blo 1403521 4806901 := bbase (se 5 (by rfl) ⟨225323, by rfl⟩ : syracuseStep 4806901 = 450647) (by norm_num)
theorem B1579261 : Blo 1403521 1579261 := bbase (se 3 (by rfl) ⟨296111, by rfl⟩ : syracuseStep 1579261 = 592223) (by norm_num)
theorem B5691653 : Blo 1403521 5691653 := bbase (se 4 (by rfl) ⟨533592, by rfl⟩ : syracuseStep 5691653 = 1067185) (by norm_num)
theorem B3553541 : Blo 1403521 3553541 := bbase (se 4 (by rfl) ⟨333144, by rfl⟩ : syracuseStep 3553541 = 666289) (by norm_num)
theorem B3160349 : Blo 1403521 3160349 := bbase (se 3 (by rfl) ⟨592565, by rfl⟩ : syracuseStep 3160349 = 1185131) (by norm_num)
theorem B1579297 : Blo 1403521 1579297 := bbase (se 2 (by rfl) ⟨592236, by rfl⟩ : syracuseStep 1579297 = 1184473) (by norm_num)
theorem B1579333 : Blo 1403521 1579333 := bbase (se 4 (by rfl) ⟨148062, by rfl⟩ : syracuseStep 1579333 = 296125) (by norm_num)
theorem B3602765 : Blo 1403521 3602765 := bbase (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) (by norm_num)
theorem B3373397 : Blo 1403521 3373397 := bbase (se 10 (by rfl) ⟨4941, by rfl⟩ : syracuseStep 3373397 = 9883) (by norm_num)
theorem B3160421 : Blo 1403521 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B1579369 : Blo 1403521 1579369 := bbase (se 2 (by rfl) ⟨592263, by rfl⟩ : syracuseStep 1579369 = 1184527) (by norm_num)
theorem B1579405 : Blo 1403521 1579405 := bbase (se 3 (by rfl) ⟨296138, by rfl⟩ : syracuseStep 1579405 = 592277) (by norm_num)
theorem B1898893 : Blo 1403521 1898893 := bbase (se 3 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 1898893 = 712085) (by norm_num)
theorem B3160493 : Blo 1403521 3160493 := bbase (se 3 (by rfl) ⟨592592, by rfl⟩ : syracuseStep 3160493 = 1185185) (by norm_num)
theorem B1579441 : Blo 1403521 1579441 := bbase (se 2 (by rfl) ⟨592290, by rfl⟩ : syracuseStep 1579441 = 1184581) (by norm_num)
theorem B7109045 : Blo 1403521 7109045 := bbase (se 5 (by rfl) ⟨333236, by rfl⟩ : syracuseStep 7109045 = 666473) (by norm_num)
theorem B3553733 : Blo 1403521 3553733 := bbase (se 4 (by rfl) ⟨333162, by rfl⟩ : syracuseStep 3553733 = 666325) (by norm_num)
theorem B1423813 : Blo 1403521 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B1710533 : Blo 1403521 1710533 := bbase (se 4 (by rfl) ⟨160362, by rfl⟩ : syracuseStep 1710533 = 320725) (by norm_num)
theorem B1579477 : Blo 1403521 1579477 := bbase (se 7 (by rfl) ⟨18509, by rfl⟩ : syracuseStep 1579477 = 37019) (by norm_num)
theorem B3160565 : Blo 1403521 3160565 := bbase (se 5 (by rfl) ⟨148151, by rfl⟩ : syracuseStep 3160565 = 296303) (by norm_num)
theorem B1579513 : Blo 1403521 1579513 := bbase (se 2 (by rfl) ⟨592317, by rfl⟩ : syracuseStep 1579513 = 1184635) (by norm_num)
theorem B1579549 : Blo 1403521 1579549 := bbase (se 3 (by rfl) ⟨296165, by rfl⟩ : syracuseStep 1579549 = 592331) (by norm_num)
theorem B3201589 : Blo 1403521 3201589 := bbase (se 5 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 3201589 = 300149) (by norm_num)
theorem B4741685 : Blo 1403521 4741685 := bbase (se 5 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 4741685 = 444533) (by norm_num)
theorem B3160637 : Blo 1403521 3160637 := bbase (se 3 (by rfl) ⟨592619, by rfl⟩ : syracuseStep 3160637 = 1185239) (by norm_num)
theorem B1579585 : Blo 1403521 1579585 := bbase (se 2 (by rfl) ⟨592344, by rfl⟩ : syracuseStep 1579585 = 1184689) (by norm_num)
theorem B5691973 : Blo 1403521 5691973 := bbase (se 4 (by rfl) ⟨533622, by rfl⟩ : syracuseStep 5691973 = 1067245) (by norm_num)
theorem B1710661 : Blo 1403521 1710661 := bbase (se 4 (by rfl) ⟨160374, by rfl⟩ : syracuseStep 1710661 = 320749) (by norm_num)
theorem B5331541 : Blo 1403521 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B1579621 : Blo 1403521 1579621 := bbase (se 4 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 1579621 = 296179) (by norm_num)
theorem B3160709 : Blo 1403521 3160709 := bbase (se 4 (by rfl) ⟨296316, by rfl⟩ : syracuseStep 3160709 = 592633) (by norm_num)
theorem B1579657 : Blo 1403521 1579657 := bbase (se 2 (by rfl) ⟨592371, by rfl⟩ : syracuseStep 1579657 = 1184743) (by norm_num)
theorem B2054813 : Blo 1403521 2054813 := bbase (se 3 (by rfl) ⟨385277, by rfl⟩ : syracuseStep 2054813 = 770555) (by norm_num)
theorem B3373733 : Blo 1403521 3373733 := bbase (se 4 (by rfl) ⟨316287, by rfl⟩ : syracuseStep 3373733 = 632575) (by norm_num)
theorem B1579693 : Blo 1403521 1579693 := bbase (se 3 (by rfl) ⟨296192, by rfl⟩ : syracuseStep 1579693 = 592385) (by norm_num)
theorem B3160781 : Blo 1403521 3160781 := bbase (se 3 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 3160781 = 1185293) (by norm_num)
theorem B1579729 : Blo 1403521 1579729 := bbase (se 2 (by rfl) ⟨592398, by rfl⟩ : syracuseStep 1579729 = 1184797) (by norm_num)
theorem B1579765 : Blo 1403521 1579765 := bbase (se 5 (by rfl) ⟨74051, by rfl⟩ : syracuseStep 1579765 = 148103) (by norm_num)
theorem B1424125 : Blo 1403521 1424125 := bbase (se 3 (by rfl) ⟨267023, by rfl⟩ : syracuseStep 1424125 = 534047) (by norm_num)
theorem B3160853 : Blo 1403521 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B1579801 : Blo 1403521 1579801 := bbase (se 2 (by rfl) ⟨592425, by rfl⟩ : syracuseStep 1579801 = 1184851) (by norm_num)
theorem B3554077 : Blo 1403521 3554077 := bbase (se 3 (by rfl) ⟨666389, by rfl⟩ : syracuseStep 3554077 = 1332779) (by norm_num)
theorem B1776421 : Blo 1403521 1776421 := bbase (se 4 (by rfl) ⟨166539, by rfl⟩ : syracuseStep 1776421 = 333079) (by norm_num)
theorem B1579837 : Blo 1403521 1579837 := bbase (se 3 (by rfl) ⟨296219, by rfl⟩ : syracuseStep 1579837 = 592439) (by norm_num)
theorem B3160925 : Blo 1403521 3160925 := bbase (se 3 (by rfl) ⟨592673, by rfl⟩ : syracuseStep 3160925 = 1185347) (by norm_num)
theorem B1579873 : Blo 1403521 1579873 := bbase (se 2 (by rfl) ⟨592452, by rfl⟩ : syracuseStep 1579873 = 1184905) (by norm_num)
theorem B5331845 : Blo 1403521 5331845 := bbase (se 4 (by rfl) ⟨499860, by rfl⟩ : syracuseStep 5331845 = 999721) (by norm_num)
theorem B1579909 : Blo 1403521 1579909 := bbase (se 4 (by rfl) ⟨148116, by rfl⟩ : syracuseStep 1579909 = 296233) (by norm_num)
theorem B3554189 : Blo 1403521 3554189 := bbase (se 3 (by rfl) ⟨666410, by rfl⟩ : syracuseStep 3554189 = 1332821) (by norm_num)
theorem B10255253 : Blo 1403521 10255253 := bbase (se 6 (by rfl) ⟨240357, by rfl⟩ : syracuseStep 10255253 = 480715) (by norm_num)
theorem B10673045 : Blo 1403521 10673045 := bbase (se 6 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 10673045 = 500299) (by norm_num)
theorem B3160997 : Blo 1403521 3160997 := bbase (se 4 (by rfl) ⟨296343, by rfl⟩ : syracuseStep 3160997 = 592687) (by norm_num)
theorem B1579945 : Blo 1403521 1579945 := bbase (se 2 (by rfl) ⟨592479, by rfl⟩ : syracuseStep 1579945 = 1184959) (by norm_num)
theorem B1579981 : Blo 1403521 1579981 := bbase (se 3 (by rfl) ⟨296246, by rfl⟩ : syracuseStep 1579981 = 592493) (by norm_num)
theorem B1776593 : Blo 1403521 1776593 := bbase (se 2 (by rfl) ⟨666222, by rfl⟩ : syracuseStep 1776593 = 1332445) (by norm_num)
theorem B4742117 : Blo 1403521 4742117 := bbase (se 4 (by rfl) ⟨444573, by rfl⟩ : syracuseStep 4742117 = 889147) (by norm_num)
theorem B1711081 : Blo 1403521 1711081 := bbase (se 2 (by rfl) ⟨641655, by rfl⟩ : syracuseStep 1711081 = 1283311) (by norm_num)
theorem B3161069 : Blo 1403521 3161069 := bbase (se 3 (by rfl) ⟨592700, by rfl⟩ : syracuseStep 3161069 = 1185401) (by norm_num)
theorem B1580017 : Blo 1403521 1580017 := bbase (se 2 (by rfl) ⟨592506, by rfl⟩ : syracuseStep 1580017 = 1185013) (by norm_num)
theorem B1776649 : Blo 1403521 1776649 := bbase (se 2 (by rfl) ⟨666243, by rfl⟩ : syracuseStep 1776649 = 1332487) (by norm_num)
theorem B1580053 : Blo 1403521 1580053 := bbase (se 6 (by rfl) ⟨37032, by rfl⟩ : syracuseStep 1580053 = 74065) (by norm_num)
theorem B3161141 : Blo 1403521 3161141 := bbase (se 5 (by rfl) ⟨148178, by rfl⟩ : syracuseStep 3161141 = 296357) (by norm_num)
theorem B1580089 : Blo 1403521 1580089 := bbase (se 2 (by rfl) ⟨592533, by rfl⟩ : syracuseStep 1580089 = 1185067) (by norm_num)
theorem B3554381 : Blo 1403521 3554381 := bbase (se 3 (by rfl) ⟨666446, by rfl⟩ : syracuseStep 3554381 = 1332893) (by norm_num)
theorem B22772821 : Blo 1403521 22772821 := bbase (se 8 (by rfl) ⟨133434, by rfl⟩ : syracuseStep 22772821 = 266869) (by norm_num)
theorem B1580125 : Blo 1403521 1580125 := bbase (se 3 (by rfl) ⟨296273, by rfl⟩ : syracuseStep 1580125 = 592547) (by norm_num)
theorem B1776745 : Blo 1403521 1776745 := bbase (se 2 (by rfl) ⟨666279, by rfl⟩ : syracuseStep 1776745 = 1332559) (by norm_num)
theorem B3161213 : Blo 1403521 3161213 := bbase (se 3 (by rfl) ⟨592727, by rfl⟩ : syracuseStep 3161213 = 1185455) (by norm_num)
theorem B1580161 : Blo 1403521 1580161 := bbase (se 2 (by rfl) ⟨592560, by rfl⟩ : syracuseStep 1580161 = 1185121) (by norm_num)
theorem B5061781 : Blo 1403521 5061781 := bbase (se 6 (by rfl) ⟨118635, by rfl⟩ : syracuseStep 5061781 = 237271) (by norm_num)
theorem B1580197 : Blo 1403521 1580197 := bbase (se 4 (by rfl) ⟨148143, by rfl⟩ : syracuseStep 1580197 = 296287) (by norm_num)
theorem B3161285 : Blo 1403521 3161285 := bbase (se 4 (by rfl) ⟨296370, by rfl⟩ : syracuseStep 3161285 = 592741) (by norm_num)
theorem B1580233 : Blo 1403521 1580233 := bbase (se 2 (by rfl) ⟨592587, by rfl⟩ : syracuseStep 1580233 = 1185175) (by norm_num)
theorem B1580269 : Blo 1403521 1580269 := bbase (se 3 (by rfl) ⟨296300, by rfl⟩ : syracuseStep 1580269 = 592601) (by norm_num)
theorem B3161357 : Blo 1403521 3161357 := bbase (se 3 (by rfl) ⟨592754, by rfl⟩ : syracuseStep 3161357 = 1185509) (by norm_num)
theorem B1580305 : Blo 1403521 1580305 := bbase (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) (by norm_num)
theorem B1776917 : Blo 1403521 1776917 := bbase (se 6 (by rfl) ⟨41646, by rfl⟩ : syracuseStep 1776917 = 83293) (by norm_num)
theorem B10665269 : Blo 1403521 10665269 := bbase (se 5 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 10665269 = 999869) (by norm_num)
theorem B1580341 : Blo 1403521 1580341 := bbase (se 5 (by rfl) ⟨74078, by rfl⟩ : syracuseStep 1580341 = 148157) (by norm_num)
theorem B1776973 : Blo 1403521 1776973 := bbase (se 3 (by rfl) ⟨333182, by rfl⟩ : syracuseStep 1776973 = 666365) (by norm_num)
theorem B1711441 : Blo 1403521 1711441 := bbase (se 2 (by rfl) ⟨641790, by rfl⟩ : syracuseStep 1711441 = 1283581) (by norm_num)
theorem B3161429 : Blo 1403521 3161429 := bbase (se 11 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 3161429 = 4631) (by norm_num)
theorem B1580377 : Blo 1403521 1580377 := bbase (se 2 (by rfl) ⟨592641, by rfl⟩ : syracuseStep 1580377 = 1185283) (by norm_num)
theorem B9125237 : Blo 1403521 9125237 := bbase (se 5 (by rfl) ⟨427745, by rfl⟩ : syracuseStep 9125237 = 855491) (by norm_num)
theorem B1580413 : Blo 1403521 1580413 := bbase (se 3 (by rfl) ⟨296327, by rfl⟩ : syracuseStep 1580413 = 592655) (by norm_num)
theorem B4742549 : Blo 1403521 4742549 := bbase (se 6 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 4742549 = 222307) (by norm_num)
theorem B3161501 : Blo 1403521 3161501 := bbase (se 3 (by rfl) ⟨592781, by rfl⟩ : syracuseStep 3161501 = 1185563) (by norm_num)
theorem B1580449 : Blo 1403521 1580449 := bbase (se 2 (by rfl) ⟨592668, by rfl⟩ : syracuseStep 1580449 = 1185337) (by norm_num)
theorem B3554725 : Blo 1403521 3554725 := bbase (se 4 (by rfl) ⟨333255, by rfl⟩ : syracuseStep 3554725 = 666511) (by norm_num)
theorem B1686953 : Blo 1403521 1686953 := bbase (se 2 (by rfl) ⟨632607, by rfl⟩ : syracuseStep 1686953 = 1265215) (by norm_num)
theorem B1777069 : Blo 1403521 1777069 := bbase (se 3 (by rfl) ⟨333200, by rfl⟩ : syracuseStep 1777069 = 666401) (by norm_num)
theorem B1580485 : Blo 1403521 1580485 := bbase (se 4 (by rfl) ⟨148170, by rfl⟩ : syracuseStep 1580485 = 296341) (by norm_num)
theorem B3161573 : Blo 1403521 3161573 := bbase (se 4 (by rfl) ⟨296397, by rfl⟩ : syracuseStep 3161573 = 592795) (by norm_num)
theorem B1580521 : Blo 1403521 1580521 := bbase (se 2 (by rfl) ⟨592695, by rfl⟩ : syracuseStep 1580521 = 1185391) (by norm_num)
theorem B1580557 : Blo 1403521 1580557 := bbase (se 3 (by rfl) ⟨296354, by rfl⟩ : syracuseStep 1580557 = 592709) (by norm_num)
theorem B3554837 : Blo 1403521 3554837 := bbase (se 6 (by rfl) ⟨83316, by rfl⟩ : syracuseStep 3554837 = 166633) (by norm_num)
theorem B3161645 : Blo 1403521 3161645 := bbase (se 3 (by rfl) ⟨592808, by rfl⟩ : syracuseStep 3161645 = 1185617) (by norm_num)
theorem B1580593 : Blo 1403521 1580593 := bbase (se 2 (by rfl) ⟨592722, by rfl⟩ : syracuseStep 1580593 = 1185445) (by norm_num)
theorem B1580629 : Blo 1403521 1580629 := bbase (se 8 (by rfl) ⟨9261, by rfl⟩ : syracuseStep 1580629 = 18523) (by norm_num)
theorem B1777241 : Blo 1403521 1777241 := bbase (se 2 (by rfl) ⟨666465, by rfl⟩ : syracuseStep 1777241 = 1332931) (by norm_num)
theorem B3161717 : Blo 1403521 3161717 := bbase (se 5 (by rfl) ⟨148205, by rfl⟩ : syracuseStep 3161717 = 296411) (by norm_num)
theorem B1580665 : Blo 1403521 1580665 := bbase (se 2 (by rfl) ⟨592749, by rfl⟩ : syracuseStep 1580665 = 1185499) (by norm_num)
theorem B1777297 : Blo 1403521 1777297 := bbase (se 2 (by rfl) ⟨666486, by rfl⟩ : syracuseStep 1777297 = 1332973) (by norm_num)
theorem B1580701 : Blo 1403521 1580701 := bbase (se 3 (by rfl) ⟨296381, by rfl⟩ : syracuseStep 1580701 = 592763) (by norm_num)
theorem B3161789 : Blo 1403521 3161789 := bbase (se 3 (by rfl) ⟨592835, by rfl⟩ : syracuseStep 3161789 = 1185671) (by norm_num)
theorem B1580737 : Blo 1403521 1580737 := bbase (se 2 (by rfl) ⟨592776, by rfl⟩ : syracuseStep 1580737 = 1185553) (by norm_num)
theorem B7110341 : Blo 1403521 7110341 := bbase (se 4 (by rfl) ⟨666594, by rfl⟩ : syracuseStep 7110341 = 1333189) (by norm_num)
theorem B3374789 : Blo 1403521 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B1687241 : Blo 1403521 1687241 := bbase (se 2 (by rfl) ⟨632715, by rfl⟩ : syracuseStep 1687241 = 1265431) (by norm_num)
theorem B3555029 : Blo 1403521 3555029 := bbase (se 7 (by rfl) ⟨41660, by rfl⟩ : syracuseStep 3555029 = 83321) (by norm_num)
theorem B1580773 : Blo 1403521 1580773 := bbase (se 4 (by rfl) ⟨148197, by rfl⟩ : syracuseStep 1580773 = 296395) (by norm_num)
theorem B1777393 : Blo 1403521 1777393 := bbase (se 2 (by rfl) ⟨666522, by rfl⟩ : syracuseStep 1777393 = 1333045) (by norm_num)
theorem B7995125 : Blo 1403521 7995125 := bbase (se 5 (by rfl) ⟨374771, by rfl⟩ : syracuseStep 7995125 = 749543) (by norm_num)
theorem B3161861 : Blo 1403521 3161861 := bbase (se 4 (by rfl) ⟨296424, by rfl⟩ : syracuseStep 3161861 = 592849) (by norm_num)
theorem B1580809 : Blo 1403521 1580809 := bbase (se 2 (by rfl) ⟨592803, by rfl⟩ : syracuseStep 1580809 = 1185607) (by norm_num)
theorem B1580845 : Blo 1403521 1580845 := bbase (se 3 (by rfl) ⟨296408, by rfl⟩ : syracuseStep 1580845 = 592817) (by norm_num)
theorem B4742981 : Blo 1403521 4742981 := bbase (se 4 (by rfl) ⟨444654, by rfl⟩ : syracuseStep 4742981 = 889309) (by norm_num)
theorem B3161933 : Blo 1403521 3161933 := bbase (se 3 (by rfl) ⟨592862, by rfl⟩ : syracuseStep 3161933 = 1185725) (by norm_num)
theorem B1580881 : Blo 1403521 1580881 := bbase (se 2 (by rfl) ⟨592830, by rfl⟩ : syracuseStep 1580881 = 1185661) (by norm_num)
theorem B1998685 : Blo 1403521 1998685 := bbase (se 3 (by rfl) ⟨374753, by rfl⟩ : syracuseStep 1998685 = 749507) (by norm_num)
theorem B1687405 : Blo 1403521 1687405 := bbase (se 3 (by rfl) ⟨316388, by rfl⟩ : syracuseStep 1687405 = 632777) (by norm_num)
theorem B1580917 : Blo 1403521 1580917 := bbase (se 5 (by rfl) ⟨74105, by rfl⟩ : syracuseStep 1580917 = 148211) (by norm_num)
theorem B1687433 : Blo 1403521 1687433 := bbase (se 2 (by rfl) ⟨632787, by rfl⟩ : syracuseStep 1687433 = 1265575) (by norm_num)
theorem B3162005 : Blo 1403521 3162005 := bbase (se 6 (by rfl) ⟨74109, by rfl⟩ : syracuseStep 3162005 = 148219) (by norm_num)
theorem B1580953 : Blo 1403521 1580953 := bbase (se 2 (by rfl) ⟨592857, by rfl⟩ : syracuseStep 1580953 = 1185715) (by norm_num)
theorem B1777565 : Blo 1403521 1777565 := bbase (se 3 (by rfl) ⟨333293, by rfl⟩ : syracuseStep 1777565 = 666587) (by norm_num)
theorem B1580989 : Blo 1403521 1580989 := bbase (se 3 (by rfl) ⟨296435, by rfl⟩ : syracuseStep 1580989 = 592871) (by norm_num)
theorem B2105285 : Blo 1403521 2105285 := bbase (se 4 (by rfl) ⟨197370, by rfl⟩ : syracuseStep 2105285 = 394741) (by norm_num)
theorem B1777621 : Blo 1403521 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B2105309 : Blo 1403521 2105309 := bbase (se 3 (by rfl) ⟨394745, by rfl⟩ : syracuseStep 2105309 = 789491) (by norm_num)
theorem B3162077 : Blo 1403521 3162077 := bbase (se 3 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 3162077 = 1185779) (by norm_num)
theorem B1581025 : Blo 1403521 1581025 := bbase (se 2 (by rfl) ⟨592884, by rfl⟩ : syracuseStep 1581025 = 1185769) (by norm_num)
theorem B2105333 : Blo 1403521 2105333 := bbase (se 5 (by rfl) ⟨98687, by rfl⟩ : syracuseStep 2105333 = 197375) (by norm_num)
theorem B2105345 : Blo 1403521 2105345 := bstep (se 2 (by rfl) ⟨789504, by rfl⟩ : syracuseStep 2105345 = 1579009) B1579009
theorem B2105363 : Blo 1403521 2105363 := bstep (se 1 (by rfl) ⟨1579022, by rfl⟩ : syracuseStep 2105363 = 3158045) B3158045
theorem B2105393 : Blo 1403521 2105393 := bstep (se 2 (by rfl) ⟨789522, by rfl⟩ : syracuseStep 2105393 = 1579045) B1579045
theorem B3997745 : Blo 1403521 3997745 := bstep (se 2 (by rfl) ⟨1499154, by rfl⟩ : syracuseStep 3997745 = 2998309) B2998309
theorem B1998913 : Blo 1403521 1998913 := bstep (se 2 (by rfl) ⟨749592, by rfl⟩ : syracuseStep 1998913 = 1499185) B1499185
theorem B2105411 : Blo 1403521 2105411 := bstep (se 1 (by rfl) ⟨1579058, by rfl⟩ : syracuseStep 2105411 = 3158117) B3158117
theorem B2105441 : Blo 1403521 2105441 := bstep (se 2 (by rfl) ⟨789540, by rfl⟩ : syracuseStep 2105441 = 1579081) B1579081
theorem B2105459 : Blo 1403521 2105459 := bstep (se 1 (by rfl) ⟨1579094, by rfl⟩ : syracuseStep 2105459 = 3158189) B3158189
theorem B1581187 : Blo 1403521 1581187 := bstep (se 1 (by rfl) ⟨1185890, by rfl⟩ : syracuseStep 1581187 = 2371781) B2371781
theorem B2105489 : Blo 1403521 2105489 := bstep (se 2 (by rfl) ⟨789558, by rfl⟩ : syracuseStep 2105489 = 1579117) B1579117
theorem B3162257 : Blo 1403521 3162257 := bstep (se 2 (by rfl) ⟨1185846, by rfl⟩ : syracuseStep 3162257 = 2371693) B2371693
theorem B1999009 : Blo 1403521 1999009 := bstep (se 2 (by rfl) ⟨749628, by rfl⟩ : syracuseStep 1999009 = 1499257) B1499257
theorem B2105507 : Blo 1403521 2105507 := bstep (se 1 (by rfl) ⟨1579130, by rfl⟩ : syracuseStep 2105507 = 3158261) B3158261
theorem B3162275 : Blo 1403521 3162275 := bstep (se 1 (by rfl) ⟨2371706, by rfl⟩ : syracuseStep 3162275 = 4743413) B4743413
theorem B2105537 : Blo 1403521 2105537 := bstep (se 2 (by rfl) ⟨789576, by rfl⟩ : syracuseStep 2105537 = 1579153) B1579153
theorem B2105555 : Blo 1403521 2105555 := bstep (se 1 (by rfl) ⟨1579166, by rfl⟩ : syracuseStep 2105555 = 3158333) B3158333
theorem B72982741 : Blo 1403521 72982741 := bstep (se 7 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 72982741 = 1710533) B1710533
theorem B8110307 : Blo 1403521 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B2105585 : Blo 1403521 2105585 := bstep (se 2 (by rfl) ⟨789594, by rfl⟩ : syracuseStep 2105585 = 1579189) B1579189
theorem B2531569 : Blo 1403521 2531569 := bstep (se 2 (by rfl) ⟨949338, by rfl⟩ : syracuseStep 2531569 = 1898677) B1898677
theorem B2105603 : Blo 1403521 2105603 := bstep (se 1 (by rfl) ⟨1579202, by rfl⟩ : syracuseStep 2105603 = 3158405) B3158405
theorem B1499411 : Blo 1403521 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B2105633 : Blo 1403521 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B2105651 : Blo 1403521 2105651 := bstep (se 1 (by rfl) ⟨1579238, by rfl⟩ : syracuseStep 2105651 = 3158477) B3158477
theorem B7110989 : Blo 1403521 7110989 := bstep (se 3 (by rfl) ⟨1333310, by rfl⟩ : syracuseStep 7110989 = 2666621) B2666621
theorem B2105681 : Blo 1403521 2105681 := bstep (se 2 (by rfl) ⟨789630, by rfl⟩ : syracuseStep 2105681 = 1579261) B1579261
theorem B2105699 : Blo 1403521 2105699 := bstep (se 1 (by rfl) ⟨1579274, by rfl⟩ : syracuseStep 2105699 = 3158549) B3158549
theorem B3555697 : Blo 1403521 3555697 := bstep (se 2 (by rfl) ⟨1333386, by rfl⟩ : syracuseStep 3555697 = 2666773) B2666773
theorem B2105729 : Blo 1403521 2105729 := bstep (se 2 (by rfl) ⟨789648, by rfl⟩ : syracuseStep 2105729 = 1579297) B1579297
theorem B1778051 : Blo 1403521 1778051 := bstep (se 1 (by rfl) ⟨1333538, by rfl⟩ : syracuseStep 1778051 = 2667077) B2667077
theorem B2105747 : Blo 1403521 2105747 := bstep (se 1 (by rfl) ⟨1579310, by rfl⟩ : syracuseStep 2105747 = 3158621) B3158621
theorem B2105777 : Blo 1403521 2105777 := bstep (se 2 (by rfl) ⟨789666, by rfl⟩ : syracuseStep 2105777 = 1579333) B1579333
theorem B4268483 : Blo 1403521 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B2105795 : Blo 1403521 2105795 := bstep (se 1 (by rfl) ⟨1579346, by rfl⟩ : syracuseStep 2105795 = 3158693) B3158693
theorem B4743629 : Blo 1403521 4743629 := bstep (se 3 (by rfl) ⟨889430, by rfl⟩ : syracuseStep 4743629 = 1778861) B1778861
theorem B2105825 : Blo 1403521 2105825 := bstep (se 2 (by rfl) ⟨789684, by rfl⟩ : syracuseStep 2105825 = 1579369) B1579369
theorem B8995313 : Blo 1403521 8995313 := bstep (se 2 (by rfl) ⟨3373242, by rfl⟩ : syracuseStep 8995313 = 6746485) B6746485
theorem B2105843 : Blo 1403521 2105843 := bstep (se 1 (by rfl) ⟨1579382, by rfl⟩ : syracuseStep 2105843 = 3158765) B3158765
theorem B2998787 : Blo 1403521 2998787 := bstep (se 1 (by rfl) ⟨2249090, by rfl⟩ : syracuseStep 2998787 = 4498181) B4498181
theorem B2105873 : Blo 1403521 2105873 := bstep (se 2 (by rfl) ⟨789702, by rfl⟩ : syracuseStep 2105873 = 1579405) B1579405
theorem B2105891 : Blo 1403521 2105891 := bstep (se 1 (by rfl) ⟨1579418, by rfl⟩ : syracuseStep 2105891 = 3158837) B3158837
theorem B2105921 : Blo 1403521 2105921 := bstep (se 2 (by rfl) ⟨789720, by rfl⟩ : syracuseStep 2105921 = 1579441) B1579441
theorem B2105939 : Blo 1403521 2105939 := bstep (se 1 (by rfl) ⟨1579454, by rfl⟩ : syracuseStep 2105939 = 3158909) B3158909
theorem B2105969 : Blo 1403521 2105969 := bstep (se 2 (by rfl) ⟨789738, by rfl⟩ : syracuseStep 2105969 = 1579477) B1579477
theorem B2105987 : Blo 1403521 2105987 := bstep (se 1 (by rfl) ⟨1579490, by rfl⟩ : syracuseStep 2105987 = 3158981) B3158981
theorem B3555971 : Blo 1403521 3555971 := bstep (se 1 (by rfl) ⟨2666978, by rfl⟩ : syracuseStep 3555971 = 5333957) B5333957
theorem B1999505 : Blo 1403521 1999505 := bstep (se 2 (by rfl) ⟨749814, by rfl⟩ : syracuseStep 1999505 = 1499629) B1499629
theorem B2106017 : Blo 1403521 2106017 := bstep (se 2 (by rfl) ⟨789756, by rfl⟩ : syracuseStep 2106017 = 1579513) B1579513
theorem B5997233 : Blo 1403521 5997233 := bstep (se 2 (by rfl) ⟨2248962, by rfl⟩ : syracuseStep 5997233 = 4497925) B4497925
theorem B2106035 : Blo 1403521 2106035 := bstep (se 1 (by rfl) ⟨1579526, by rfl⟩ : syracuseStep 2106035 = 3159053) B3159053
theorem B1802947 : Blo 1403521 1802947 := bstep (se 1 (by rfl) ⟨1352210, by rfl⟩ : syracuseStep 1802947 = 2704421) B2704421
theorem B2106065 : Blo 1403521 2106065 := bstep (se 2 (by rfl) ⟨789774, by rfl⟩ : syracuseStep 2106065 = 1579549) B1579549
theorem B2106083 : Blo 1403521 2106083 := bstep (se 1 (by rfl) ⟨1579562, by rfl⟩ : syracuseStep 2106083 = 3159125) B3159125
theorem B4268785 : Blo 1403521 4268785 := bstep (se 2 (by rfl) ⟨1600794, by rfl⟩ : syracuseStep 4268785 = 3201589) B3201589
theorem B3375857 : Blo 1403521 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B2106113 : Blo 1403521 2106113 := bstep (se 2 (by rfl) ⟨789792, by rfl⟩ : syracuseStep 2106113 = 1579585) B1579585
theorem B2106131 : Blo 1403521 2106131 := bstep (se 1 (by rfl) ⟨1579598, by rfl⟩ : syracuseStep 2106131 = 3159197) B3159197
theorem B2532131 : Blo 1403521 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B2106161 : Blo 1403521 2106161 := bstep (se 2 (by rfl) ⟨789810, by rfl⟩ : syracuseStep 2106161 = 1579621) B1579621
theorem B2106179 : Blo 1403521 2106179 := bstep (se 1 (by rfl) ⟨1579634, by rfl⟩ : syracuseStep 2106179 = 3159269) B3159269
theorem B3040067 : Blo 1403521 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B3556163 : Blo 1403521 3556163 := bstep (se 1 (by rfl) ⟨2667122, by rfl⟩ : syracuseStep 3556163 = 5334245) B5334245
theorem B2106209 : Blo 1403521 2106209 := bstep (se 2 (by rfl) ⟨789828, by rfl⟩ : syracuseStep 2106209 = 1579657) B1579657
theorem B2106227 : Blo 1403521 2106227 := bstep (se 1 (by rfl) ⟨1579670, by rfl⟩ : syracuseStep 2106227 = 3159341) B3159341
theorem B1852291 : Blo 1403521 1852291 := bstep (se 1 (by rfl) ⟨1389218, by rfl⟩ : syracuseStep 1852291 = 2778437) B2778437
theorem B2106257 : Blo 1403521 2106257 := bstep (se 2 (by rfl) ⟨789846, by rfl⟩ : syracuseStep 2106257 = 1579693) B1579693
theorem B1688467 : Blo 1403521 1688467 := bstep (se 1 (by rfl) ⟨1266350, by rfl⟩ : syracuseStep 1688467 = 2532701) B2532701
theorem B2106275 : Blo 1403521 2106275 := bstep (se 1 (by rfl) ⟨1579706, by rfl⟩ : syracuseStep 2106275 = 3159413) B3159413
theorem B2106305 : Blo 1403521 2106305 := bstep (se 2 (by rfl) ⟨789864, by rfl⟩ : syracuseStep 2106305 = 1579729) B1579729
theorem B2106323 : Blo 1403521 2106323 := bstep (se 1 (by rfl) ⟨1579742, by rfl⟩ : syracuseStep 2106323 = 3159485) B3159485
theorem B25617379 : Blo 1403521 25617379 := bstep (se 1 (by rfl) ⟨19213034, by rfl⟩ : syracuseStep 25617379 = 38426069) B38426069
theorem B2106353 : Blo 1403521 2106353 := bstep (se 2 (by rfl) ⟨789882, by rfl⟩ : syracuseStep 2106353 = 1579765) B1579765
theorem B2106371 : Blo 1403521 2106371 := bstep (se 1 (by rfl) ⟨1579778, by rfl⟩ : syracuseStep 2106371 = 3159557) B3159557
theorem B2106401 : Blo 1403521 2106401 := bstep (se 2 (by rfl) ⟨789900, by rfl⟩ : syracuseStep 2106401 = 1579801) B1579801
theorem B2368561 : Blo 1403521 2368561 := bstep (se 2 (by rfl) ⟨888210, by rfl⟩ : syracuseStep 2368561 = 1776421) B1776421
theorem B2106419 : Blo 1403521 2106419 := bstep (se 1 (by rfl) ⟨1579814, by rfl⟩ : syracuseStep 2106419 = 3159629) B3159629
theorem B1778755 : Blo 1403521 1778755 := bstep (se 1 (by rfl) ⟨1334066, by rfl⟩ : syracuseStep 1778755 = 2668133) B2668133
theorem B2106449 : Blo 1403521 2106449 := bstep (se 2 (by rfl) ⟨789918, by rfl⟩ : syracuseStep 2106449 = 1579837) B1579837
theorem B2368595 : Blo 1403521 2368595 := bstep (se 1 (by rfl) ⟨1776446, by rfl⟩ : syracuseStep 2368595 = 3552893) B3552893
theorem B2106467 : Blo 1403521 2106467 := bstep (se 1 (by rfl) ⟨1579850, by rfl⟩ : syracuseStep 2106467 = 3159701) B3159701
theorem B4498541 : Blo 1403521 4498541 := bstep (se 3 (by rfl) ⟨843476, by rfl⟩ : syracuseStep 4498541 = 1686953) B1686953
theorem B2106497 : Blo 1403521 2106497 := bstep (se 2 (by rfl) ⟨789936, by rfl⟩ : syracuseStep 2106497 = 1579873) B1579873
theorem B2106515 : Blo 1403521 2106515 := bstep (se 1 (by rfl) ⟨1579886, by rfl⟩ : syracuseStep 2106515 = 3159773) B3159773
theorem B6931619 : Blo 1403521 6931619 := bstep (se 1 (by rfl) ⟨5198714, by rfl⟩ : syracuseStep 6931619 = 10397429) B10397429
theorem B1778851 : Blo 1403521 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B2106545 : Blo 1403521 2106545 := bstep (se 2 (by rfl) ⟨789954, by rfl⟩ : syracuseStep 2106545 = 1579909) B1579909
theorem B2106563 : Blo 1403521 2106563 := bstep (se 1 (by rfl) ⟨1579922, by rfl⟩ : syracuseStep 2106563 = 3159845) B3159845
theorem B2368723 : Blo 1403521 2368723 := bstep (se 1 (by rfl) ⟨1776542, by rfl⟩ : syracuseStep 2368723 = 3553085) B3553085
theorem B2106593 : Blo 1403521 2106593 := bstep (se 2 (by rfl) ⟨789972, by rfl⟩ : syracuseStep 2106593 = 1579945) B1579945
theorem B2106611 : Blo 1403521 2106611 := bstep (se 1 (by rfl) ⟨1579958, by rfl⟩ : syracuseStep 2106611 = 3159917) B3159917
theorem B8545549 : Blo 1403521 8545549 := bstep (se 3 (by rfl) ⟨1602290, by rfl⟩ : syracuseStep 8545549 = 3204581) B3204581
theorem B2106641 : Blo 1403521 2106641 := bstep (se 2 (by rfl) ⟨789990, by rfl⟩ : syracuseStep 2106641 = 1579981) B1579981
theorem B2106659 : Blo 1403521 2106659 := bstep (se 1 (by rfl) ⟨1579994, by rfl⟩ : syracuseStep 2106659 = 3159989) B3159989
theorem B2434355 : Blo 1403521 2434355 := bstep (se 1 (by rfl) ⟨1825766, by rfl⟩ : syracuseStep 2434355 = 3651533) B3651533
theorem B2106689 : Blo 1403521 2106689 := bstep (se 2 (by rfl) ⟨790008, by rfl⟩ : syracuseStep 2106689 = 1580017) B1580017
theorem B7595333 : Blo 1403521 7595333 := bstep (se 4 (by rfl) ⟨712062, by rfl⟩ : syracuseStep 7595333 = 1424125) B1424125
theorem B2106707 : Blo 1403521 2106707 := bstep (se 1 (by rfl) ⟨1580030, by rfl⟩ : syracuseStep 2106707 = 3160061) B3160061
theorem B2368865 : Blo 1403521 2368865 := bstep (se 2 (by rfl) ⟨888324, by rfl⟩ : syracuseStep 2368865 = 1776649) B1776649
theorem B2106737 : Blo 1403521 2106737 := bstep (se 2 (by rfl) ⟨790026, by rfl⟩ : syracuseStep 2106737 = 1580053) B1580053
theorem B2106755 : Blo 1403521 2106755 := bstep (se 1 (by rfl) ⟨1580066, by rfl⟩ : syracuseStep 2106755 = 3160133) B3160133
theorem B2106785 : Blo 1403521 2106785 := bstep (se 2 (by rfl) ⟨790044, by rfl⟩ : syracuseStep 2106785 = 1580089) B1580089
theorem B7595441 : Blo 1403521 7595441 := bstep (se 2 (by rfl) ⟨2848290, by rfl⟩ : syracuseStep 7595441 = 5696581) B5696581
theorem B2106803 : Blo 1403521 2106803 := bstep (se 1 (by rfl) ⟨1580102, by rfl⟩ : syracuseStep 2106803 = 3160205) B3160205
theorem B2106833 : Blo 1403521 2106833 := bstep (se 2 (by rfl) ⟨790062, by rfl⟩ : syracuseStep 2106833 = 1580125) B1580125
theorem B2368993 : Blo 1403521 2368993 := bstep (se 2 (by rfl) ⟨888372, by rfl⟩ : syracuseStep 2368993 = 1776745) B1776745
theorem B3999203 : Blo 1403521 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B2106851 : Blo 1403521 2106851 := bstep (se 1 (by rfl) ⟨1580138, by rfl⟩ : syracuseStep 2106851 = 3160277) B3160277
theorem B2000371 : Blo 1403521 2000371 := bstep (se 1 (by rfl) ⟨1500278, by rfl⟩ : syracuseStep 2000371 = 3000557) B3000557
theorem B2106881 : Blo 1403521 2106881 := bstep (se 2 (by rfl) ⟨790080, by rfl⟩ : syracuseStep 2106881 = 1580161) B1580161
theorem B3794435 : Blo 1403521 3794435 := bstep (se 1 (by rfl) ⟨2845826, by rfl⟩ : syracuseStep 3794435 = 5691653) B5691653
theorem B2369027 : Blo 1403521 2369027 := bstep (se 1 (by rfl) ⟨1776770, by rfl⟩ : syracuseStep 2369027 = 3553541) B3553541
theorem B2106899 : Blo 1403521 2106899 := bstep (se 1 (by rfl) ⟨1580174, by rfl⟩ : syracuseStep 2106899 = 3160349) B3160349
theorem B2106929 : Blo 1403521 2106929 := bstep (se 2 (by rfl) ⟨790098, by rfl⟩ : syracuseStep 2106929 = 1580197) B1580197
theorem B2106947 : Blo 1403521 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B5998157 : Blo 1403521 5998157 := bstep (se 3 (by rfl) ⟨1124654, by rfl⟩ : syracuseStep 5998157 = 2249309) B2249309
theorem B2000467 : Blo 1403521 2000467 := bstep (se 1 (by rfl) ⟨1500350, by rfl⟩ : syracuseStep 2000467 = 3000701) B3000701
theorem B2106977 : Blo 1403521 2106977 := bstep (se 2 (by rfl) ⟨790116, by rfl⟩ : syracuseStep 2106977 = 1580233) B1580233
theorem B2106995 : Blo 1403521 2106995 := bstep (se 1 (by rfl) ⟨1580246, by rfl⟩ : syracuseStep 2106995 = 3160493) B3160493
theorem B2369155 : Blo 1403521 2369155 := bstep (se 1 (by rfl) ⟨1776866, by rfl⟩ : syracuseStep 2369155 = 3553733) B3553733
theorem B2107025 : Blo 1403521 2107025 := bstep (se 2 (by rfl) ⟨790134, by rfl⟩ : syracuseStep 2107025 = 1580269) B1580269
theorem B2107043 : Blo 1403521 2107043 := bstep (se 1 (by rfl) ⟨1580282, by rfl⟩ : syracuseStep 2107043 = 3160565) B3160565
theorem B2107073 : Blo 1403521 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B2107091 : Blo 1403521 2107091 := bstep (se 1 (by rfl) ⟨1580318, by rfl⟩ : syracuseStep 2107091 = 3160637) B3160637
theorem B2107121 : Blo 1403521 2107121 := bstep (se 2 (by rfl) ⟨790170, by rfl⟩ : syracuseStep 2107121 = 1580341) B1580341
theorem B3557105 : Blo 1403521 3557105 := bstep (se 2 (by rfl) ⟨1333914, by rfl⟩ : syracuseStep 3557105 = 2667829) B2667829
theorem B4056817 : Blo 1403521 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B2107139 : Blo 1403521 2107139 := bstep (se 1 (by rfl) ⟨1580354, by rfl⟩ : syracuseStep 2107139 = 3160709) B3160709
theorem B2369297 : Blo 1403521 2369297 := bstep (se 2 (by rfl) ⟨888486, by rfl⟩ : syracuseStep 2369297 = 1776973) B1776973
theorem B2107169 : Blo 1403521 2107169 := bstep (se 2 (by rfl) ⟨790188, by rfl⟩ : syracuseStep 2107169 = 1580377) B1580377
theorem B3557155 : Blo 1403521 3557155 := bstep (se 1 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 3557155 = 5335733) B5335733
theorem B2107187 : Blo 1403521 2107187 := bstep (se 1 (by rfl) ⟨1580390, by rfl⟩ : syracuseStep 2107187 = 3160781) B3160781
theorem B2107217 : Blo 1403521 2107217 := bstep (se 2 (by rfl) ⟨790206, by rfl⟩ : syracuseStep 2107217 = 1580413) B1580413
theorem B2107235 : Blo 1403521 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B4499309 : Blo 1403521 4499309 := bstep (se 3 (by rfl) ⟨843620, by rfl⟩ : syracuseStep 4499309 = 1687241) B1687241
theorem B2107265 : Blo 1403521 2107265 := bstep (se 2 (by rfl) ⟨790224, by rfl⟩ : syracuseStep 2107265 = 1580449) B1580449
theorem B2369425 : Blo 1403521 2369425 := bstep (se 2 (by rfl) ⟨888534, by rfl⟩ : syracuseStep 2369425 = 1777069) B1777069
theorem B2107283 : Blo 1403521 2107283 := bstep (se 1 (by rfl) ⟨1580462, by rfl⟩ : syracuseStep 2107283 = 3160925) B3160925
theorem B8996771 : Blo 1403521 8996771 := bstep (se 1 (by rfl) ⟨6747578, by rfl⟩ : syracuseStep 8996771 = 13495157) B13495157
theorem B2107313 : Blo 1403521 2107313 := bstep (se 2 (by rfl) ⟨790242, by rfl⟩ : syracuseStep 2107313 = 1580485) B1580485
theorem B3557297 : Blo 1403521 3557297 := bstep (se 2 (by rfl) ⟨1333986, by rfl⟩ : syracuseStep 3557297 = 2667973) B2667973
theorem B2369459 : Blo 1403521 2369459 := bstep (se 1 (by rfl) ⟨1777094, by rfl⟩ : syracuseStep 2369459 = 3554189) B3554189
theorem B2107331 : Blo 1403521 2107331 := bstep (se 1 (by rfl) ⟨1580498, by rfl⟩ : syracuseStep 2107331 = 3160997) B3160997
theorem B2107361 : Blo 1403521 2107361 := bstep (se 2 (by rfl) ⟨790260, by rfl⟩ : syracuseStep 2107361 = 1580521) B1580521
theorem B2107379 : Blo 1403521 2107379 := bstep (se 1 (by rfl) ⟨1580534, by rfl⟩ : syracuseStep 2107379 = 3161069) B3161069
theorem B8546309 : Blo 1403521 8546309 := bstep (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) B1602433
theorem B4737041 : Blo 1403521 4737041 := bstep (se 2 (by rfl) ⟨1776390, by rfl⟩ : syracuseStep 4737041 = 3552781) B3552781
theorem B2107409 : Blo 1403521 2107409 := bstep (se 2 (by rfl) ⟨790278, by rfl⟩ : syracuseStep 2107409 = 1580557) B1580557
theorem B2107427 : Blo 1403521 2107427 := bstep (se 1 (by rfl) ⟨1580570, by rfl⟩ : syracuseStep 2107427 = 3161141) B3161141
theorem B2369587 : Blo 1403521 2369587 := bstep (se 1 (by rfl) ⟨1777190, by rfl⟩ : syracuseStep 2369587 = 3554381) B3554381
theorem B2107457 : Blo 1403521 2107457 := bstep (se 2 (by rfl) ⟨790296, by rfl⟩ : syracuseStep 2107457 = 1580593) B1580593
theorem B2000963 : Blo 1403521 2000963 := bstep (se 1 (by rfl) ⟨1500722, by rfl⟩ : syracuseStep 2000963 = 3001445) B3001445
theorem B10127429 : Blo 1403521 10127429 := bstep (se 4 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 10127429 = 1898893) B1898893
theorem B2107475 : Blo 1403521 2107475 := bstep (se 1 (by rfl) ⟨1580606, by rfl⟩ : syracuseStep 2107475 = 3161213) B3161213
theorem B2107505 : Blo 1403521 2107505 := bstep (se 2 (by rfl) ⟨790314, by rfl⟩ : syracuseStep 2107505 = 1580629) B1580629
theorem B2107523 : Blo 1403521 2107523 := bstep (se 1 (by rfl) ⟨1580642, by rfl⟩ : syracuseStep 2107523 = 3161285) B3161285
theorem B2107553 : Blo 1403521 2107553 := bstep (se 2 (by rfl) ⟨790332, by rfl⟩ : syracuseStep 2107553 = 1580665) B1580665
theorem B5335217 : Blo 1403521 5335217 := bstep (se 2 (by rfl) ⟨2000706, by rfl⟩ : syracuseStep 5335217 = 4001413) B4001413
theorem B2107571 : Blo 1403521 2107571 := bstep (se 1 (by rfl) ⟨1580678, by rfl⟩ : syracuseStep 2107571 = 3161357) B3161357
theorem B2369729 : Blo 1403521 2369729 := bstep (se 2 (by rfl) ⟨888648, by rfl⟩ : syracuseStep 2369729 = 1777297) B1777297
theorem B1624259 : Blo 1403521 1624259 := bstep (se 1 (by rfl) ⟨1218194, by rfl⟩ : syracuseStep 1624259 = 2436389) B2436389
theorem B2107601 : Blo 1403521 2107601 := bstep (se 2 (by rfl) ⟨790350, by rfl⟩ : syracuseStep 2107601 = 1580701) B1580701
theorem B2107619 : Blo 1403521 2107619 := bstep (se 1 (by rfl) ⟨1580714, by rfl⟩ : syracuseStep 2107619 = 3161429) B3161429
theorem B2107649 : Blo 1403521 2107649 := bstep (se 2 (by rfl) ⟨790368, by rfl⟩ : syracuseStep 2107649 = 1580737) B1580737
theorem B4000013 : Blo 1403521 4000013 := bstep (se 3 (by rfl) ⟨750002, by rfl⟩ : syracuseStep 4000013 = 1500005) B1500005
theorem B2885905 : Blo 1403521 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B2107667 : Blo 1403521 2107667 := bstep (se 1 (by rfl) ⟨1580750, by rfl⟩ : syracuseStep 2107667 = 3161501) B3161501
theorem B3795245 : Blo 1403521 3795245 := bstep (se 3 (by rfl) ⟨711608, by rfl⟩ : syracuseStep 3795245 = 1423217) B1423217
theorem B2107697 : Blo 1403521 2107697 := bstep (se 2 (by rfl) ⟨790386, by rfl⟩ : syracuseStep 2107697 = 1580773) B1580773
theorem B2369857 : Blo 1403521 2369857 := bstep (se 2 (by rfl) ⟨888696, by rfl⟩ : syracuseStep 2369857 = 1777393) B1777393
theorem B2107715 : Blo 1403521 2107715 := bstep (se 1 (by rfl) ⟨1580786, by rfl⟩ : syracuseStep 2107715 = 3161573) B3161573
theorem B3795277 : Blo 1403521 3795277 := bstep (se 3 (by rfl) ⟨711614, by rfl⟩ : syracuseStep 3795277 = 1423229) B1423229
theorem B2107745 : Blo 1403521 2107745 := bstep (se 2 (by rfl) ⟨790404, by rfl⟩ : syracuseStep 2107745 = 1580809) B1580809
theorem B2369891 : Blo 1403521 2369891 := bstep (se 1 (by rfl) ⟨1777418, by rfl⟩ : syracuseStep 2369891 = 3554837) B3554837
theorem B4499821 : Blo 1403521 4499821 := bstep (se 3 (by rfl) ⟨843716, by rfl⟩ : syracuseStep 4499821 = 1687433) B1687433
theorem B2107763 : Blo 1403521 2107763 := bstep (se 1 (by rfl) ⟨1580822, by rfl⟩ : syracuseStep 2107763 = 3161645) B3161645
theorem B27347341 : Blo 1403521 27347341 := bstep (se 3 (by rfl) ⟨5127626, by rfl⟩ : syracuseStep 27347341 = 10255253) B10255253
theorem B2107793 : Blo 1403521 2107793 := bstep (se 2 (by rfl) ⟨790422, by rfl⟩ : syracuseStep 2107793 = 1580845) B1580845
theorem B7588259 : Blo 1403521 7588259 := bstep (se 1 (by rfl) ⟨5691194, by rfl⟩ : syracuseStep 7588259 = 11382389) B11382389
theorem B2107811 : Blo 1403521 2107811 := bstep (se 1 (by rfl) ⟨1580858, by rfl⟩ : syracuseStep 2107811 = 3161717) B3161717
theorem B2107841 : Blo 1403521 2107841 := bstep (se 2 (by rfl) ⟨790440, by rfl⟩ : syracuseStep 2107841 = 1580881) B1580881
theorem B4000205 : Blo 1403521 4000205 := bstep (se 3 (by rfl) ⟨750038, by rfl⟩ : syracuseStep 4000205 = 1500077) B1500077
theorem B2664913 : Blo 1403521 2664913 := bstep (se 2 (by rfl) ⟨999342, by rfl⟩ : syracuseStep 2664913 = 1998685) B1998685
theorem B2107859 : Blo 1403521 2107859 := bstep (se 1 (by rfl) ⟨1580894, by rfl⟩ : syracuseStep 2107859 = 3161789) B3161789
theorem B2370019 : Blo 1403521 2370019 := bstep (se 1 (by rfl) ⟨1777514, by rfl⟩ : syracuseStep 2370019 = 3555029) B3555029
theorem B2107889 : Blo 1403521 2107889 := bstep (se 2 (by rfl) ⟨790458, by rfl⟩ : syracuseStep 2107889 = 1580917) B1580917
theorem B2107907 : Blo 1403521 2107907 := bstep (se 1 (by rfl) ⟨1580930, by rfl⟩ : syracuseStep 2107907 = 3161861) B3161861
theorem B16001549 : Blo 1403521 16001549 := bstep (se 3 (by rfl) ⟨3000290, by rfl⟩ : syracuseStep 16001549 = 6000581) B6000581
theorem B2107937 : Blo 1403521 2107937 := bstep (se 2 (by rfl) ⟨790476, by rfl⟩ : syracuseStep 2107937 = 1580953) B1580953
theorem B4737581 : Blo 1403521 4737581 := bstep (se 3 (by rfl) ⟨888296, by rfl⟩ : syracuseStep 4737581 = 1776593) B1776593
theorem B2107955 : Blo 1403521 2107955 := bstep (se 1 (by rfl) ⟨1580966, by rfl⟩ : syracuseStep 2107955 = 3161933) B3161933
theorem B16206389 : Blo 1403521 16206389 := bstep (se 5 (by rfl) ⟨759674, by rfl⟩ : syracuseStep 16206389 = 1519349) B1519349
theorem B2107985 : Blo 1403521 2107985 := bstep (se 2 (by rfl) ⟨790494, by rfl⟩ : syracuseStep 2107985 = 1580989) B1580989
theorem B4737635 : Blo 1403521 4737635 := bstep (se 1 (by rfl) ⟨3553226, by rfl⟩ : syracuseStep 4737635 = 7106453) B7106453
theorem B2108003 : Blo 1403521 2108003 := bstep (se 1 (by rfl) ⟨1581002, by rfl⟩ : syracuseStep 2108003 = 3162005) B3162005
theorem B2370161 : Blo 1403521 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B2108033 : Blo 1403521 2108033 := bstep (se 2 (by rfl) ⟨790512, by rfl⟩ : syracuseStep 2108033 = 1581025) B1581025
theorem B1403523 : Blo 1403521 1403523 := bstep (se 1 (by rfl) ⟨1052642, by rfl⟩ : syracuseStep 1403523 = 2105285) B2105285
theorem B1403539 : Blo 1403521 1403539 := bstep (se 1 (by rfl) ⟨1052654, by rfl⟩ : syracuseStep 1403539 = 2105309) B2105309
theorem B2108051 : Blo 1403521 2108051 := bstep (se 1 (by rfl) ⟨1581038, by rfl⟩ : syracuseStep 2108051 = 3162077) B3162077
theorem B1403555 : Blo 1403521 1403555 := bstep (se 1 (by rfl) ⟨1052666, by rfl⟩ : syracuseStep 1403555 = 2105333) B2105333
theorem B3001009 : Blo 1403521 3001009 := bstep (se 2 (by rfl) ⟨1125378, by rfl⟩ : syracuseStep 3001009 = 2250757) B2250757
theorem B2108081 : Blo 1403521 2108081 := bstep (se 2 (by rfl) ⟨790530, by rfl⟩ : syracuseStep 2108081 = 1581061) B1581061
theorem B1403571 : Blo 1403521 1403571 := bstep (se 1 (by rfl) ⟨1052678, by rfl⟩ : syracuseStep 1403571 = 2105357) B2105357
theorem B1403587 : Blo 1403521 1403587 := bstep (se 1 (by rfl) ⟨1052690, by rfl⟩ : syracuseStep 1403587 = 2105381) B2105381
theorem B2108099 : Blo 1403521 2108099 := bstep (se 1 (by rfl) ⟨1581074, by rfl⟩ : syracuseStep 2108099 = 3162149) B3162149
theorem B1403603 : Blo 1403521 1403603 := bstep (se 1 (by rfl) ⟨1052702, by rfl⟩ : syracuseStep 1403603 = 2105405) B2105405
theorem B2108129 : Blo 1403521 2108129 := bstep (se 2 (by rfl) ⟨790548, by rfl⟩ : syracuseStep 2108129 = 1581097) B1581097
theorem B1403619 : Blo 1403521 1403619 := bstep (se 1 (by rfl) ⟨1052714, by rfl⟩ : syracuseStep 1403619 = 2105429) B2105429
theorem B4270819 : Blo 1403521 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B2370289 : Blo 1403521 2370289 := bstep (se 2 (by rfl) ⟨888858, by rfl⟩ : syracuseStep 2370289 = 1777717) B1777717
theorem B1403635 : Blo 1403521 1403635 := bstep (se 1 (by rfl) ⟨1052726, by rfl⟩ : syracuseStep 1403635 = 2105453) B2105453
theorem B2108147 : Blo 1403521 2108147 := bstep (se 1 (by rfl) ⟨1581110, by rfl⟩ : syracuseStep 2108147 = 3162221) B3162221
theorem B1403651 : Blo 1403521 1403651 := bstep (se 1 (by rfl) ⟨1052738, by rfl⟩ : syracuseStep 1403651 = 2105477) B2105477
theorem B2108177 : Blo 1403521 2108177 := bstep (se 2 (by rfl) ⟨790566, by rfl⟩ : syracuseStep 2108177 = 1581133) B1581133
theorem B1403667 : Blo 1403521 1403667 := bstep (se 1 (by rfl) ⟨1052750, by rfl⟩ : syracuseStep 1403667 = 2105501) B2105501
theorem B2370323 : Blo 1403521 2370323 := bstep (se 1 (by rfl) ⟨1777742, by rfl⟩ : syracuseStep 2370323 = 3555485) B3555485
theorem B1403683 : Blo 1403521 1403683 := bstep (se 1 (by rfl) ⟨1052762, by rfl⟩ : syracuseStep 1403683 = 2105525) B2105525
theorem B2108195 : Blo 1403521 2108195 := bstep (se 1 (by rfl) ⟨1581146, by rfl⟩ : syracuseStep 2108195 = 3162293) B3162293
theorem B1403699 : Blo 1403521 1403699 := bstep (se 1 (by rfl) ⟨1052774, by rfl⟩ : syracuseStep 1403699 = 2105549) B2105549
theorem B2108225 : Blo 1403521 2108225 := bstep (se 2 (by rfl) ⟨790584, by rfl⟩ : syracuseStep 2108225 = 1581169) B1581169
theorem B1403715 : Blo 1403521 1403715 := bstep (se 1 (by rfl) ⟨1052786, by rfl⟩ : syracuseStep 1403715 = 2105573) B2105573
theorem B1403731 : Blo 1403521 1403731 := bstep (se 1 (by rfl) ⟨1052798, by rfl⟩ : syracuseStep 1403731 = 2105597) B2105597
theorem B2108243 : Blo 1403521 2108243 := bstep (se 1 (by rfl) ⟨1581182, by rfl⟩ : syracuseStep 2108243 = 3162365) B3162365
theorem B1403747 : Blo 1403521 1403747 := bstep (se 1 (by rfl) ⟨1052810, by rfl⟩ : syracuseStep 1403747 = 2105621) B2105621
theorem B2665315 : Blo 1403521 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B4500323 : Blo 1403521 4500323 := bstep (se 1 (by rfl) ⟨3375242, by rfl⟩ : syracuseStep 4500323 = 6750485) B6750485
theorem B4737905 : Blo 1403521 4737905 := bstep (se 2 (by rfl) ⟨1776714, by rfl⟩ : syracuseStep 4737905 = 3553429) B3553429
theorem B1403763 : Blo 1403521 1403763 := bstep (se 1 (by rfl) ⟨1052822, by rfl⟩ : syracuseStep 1403763 = 2105645) B2105645
theorem B2108273 : Blo 1403521 2108273 := bstep (se 2 (by rfl) ⟨790602, by rfl⟩ : syracuseStep 2108273 = 1581205) B1581205
theorem B1403779 : Blo 1403521 1403779 := bstep (se 1 (by rfl) ⟨1052834, by rfl⟩ : syracuseStep 1403779 = 2105669) B2105669
theorem B2665361 : Blo 1403521 2665361 := bstep (se 2 (by rfl) ⟨999510, by rfl⟩ : syracuseStep 2665361 = 1999021) B1999021
theorem B1403795 : Blo 1403521 1403795 := bstep (se 1 (by rfl) ⟨1052846, by rfl⟩ : syracuseStep 1403795 = 2105693) B2105693
theorem B2370451 : Blo 1403521 2370451 := bstep (se 1 (by rfl) ⟨1777838, by rfl⟩ : syracuseStep 2370451 = 3555677) B3555677
theorem B1403811 : Blo 1403521 1403811 := bstep (se 1 (by rfl) ⟨1052858, by rfl⟩ : syracuseStep 1403811 = 2105717) B2105717
theorem B1403827 : Blo 1403521 1403827 := bstep (se 1 (by rfl) ⟨1052870, by rfl⟩ : syracuseStep 1403827 = 2105741) B2105741
theorem B1403843 : Blo 1403521 1403843 := bstep (se 1 (by rfl) ⟨1052882, by rfl⟩ : syracuseStep 1403843 = 2105765) B2105765
theorem B1403859 : Blo 1403521 1403859 := bstep (se 1 (by rfl) ⟨1052894, by rfl⟩ : syracuseStep 1403859 = 2105789) B2105789
theorem B1403875 : Blo 1403521 1403875 := bstep (se 1 (by rfl) ⟨1052906, by rfl⟩ : syracuseStep 1403875 = 2105813) B2105813
theorem B4271075 : Blo 1403521 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B6409201 : Blo 1403521 6409201 := bstep (se 2 (by rfl) ⟨2403450, by rfl⟩ : syracuseStep 6409201 = 4806901) B4806901
theorem B1403891 : Blo 1403521 1403891 := bstep (se 1 (by rfl) ⟨1052918, by rfl⟩ : syracuseStep 1403891 = 2105837) B2105837
theorem B1403907 : Blo 1403521 1403907 := bstep (se 1 (by rfl) ⟨1052930, by rfl⟩ : syracuseStep 1403907 = 2105861) B2105861
theorem B1403923 : Blo 1403521 1403923 := bstep (se 1 (by rfl) ⟨1052942, by rfl⟩ : syracuseStep 1403923 = 2105885) B2105885
theorem B2370593 : Blo 1403521 2370593 := bstep (se 2 (by rfl) ⟨888972, by rfl⟩ : syracuseStep 2370593 = 1777945) B1777945
theorem B1403939 : Blo 1403521 1403939 := bstep (se 1 (by rfl) ⟨1052954, by rfl⟩ : syracuseStep 1403939 = 2105909) B2105909
theorem B1403955 : Blo 1403521 1403955 := bstep (se 1 (by rfl) ⟨1052966, by rfl⟩ : syracuseStep 1403955 = 2105933) B2105933
theorem B1403971 : Blo 1403521 1403971 := bstep (se 1 (by rfl) ⟨1052978, by rfl⟩ : syracuseStep 1403971 = 2105957) B2105957
theorem B1403987 : Blo 1403521 1403987 := bstep (se 1 (by rfl) ⟨1052990, by rfl⟩ : syracuseStep 1403987 = 2105981) B2105981
theorem B1404003 : Blo 1403521 1404003 := bstep (se 1 (by rfl) ⟨1053002, by rfl⟩ : syracuseStep 1404003 = 2106005) B2106005
theorem B1404019 : Blo 1403521 1404019 := bstep (se 1 (by rfl) ⟨1053014, by rfl⟩ : syracuseStep 1404019 = 2106029) B2106029
theorem B1404035 : Blo 1403521 1404035 := bstep (se 1 (by rfl) ⟨1053026, by rfl⟩ : syracuseStep 1404035 = 2106053) B2106053
theorem B1404051 : Blo 1403521 1404051 := bstep (se 1 (by rfl) ⟨1053038, by rfl⟩ : syracuseStep 1404051 = 2106077) B2106077
theorem B2370721 : Blo 1403521 2370721 := bstep (se 2 (by rfl) ⟨889020, by rfl⟩ : syracuseStep 2370721 = 1778041) B1778041
theorem B1404067 : Blo 1403521 1404067 := bstep (se 1 (by rfl) ⟨1053050, by rfl⟩ : syracuseStep 1404067 = 2106101) B2106101
theorem B2665649 : Blo 1403521 2665649 := bstep (se 2 (by rfl) ⟨999618, by rfl⟩ : syracuseStep 2665649 = 1999237) B1999237
theorem B7113905 : Blo 1403521 7113905 := bstep (se 2 (by rfl) ⟨2667714, by rfl⟩ : syracuseStep 7113905 = 5335429) B5335429
theorem B1404083 : Blo 1403521 1404083 := bstep (se 1 (by rfl) ⟨1053062, by rfl⟩ : syracuseStep 1404083 = 2106125) B2106125
theorem B1404099 : Blo 1403521 1404099 := bstep (se 1 (by rfl) ⟨1053074, by rfl⟩ : syracuseStep 1404099 = 2106149) B2106149
theorem B3796163 : Blo 1403521 3796163 := bstep (se 1 (by rfl) ⟨2847122, by rfl⟩ : syracuseStep 3796163 = 5694245) B5694245
theorem B2370755 : Blo 1403521 2370755 := bstep (se 1 (by rfl) ⟨1778066, by rfl⟩ : syracuseStep 2370755 = 3556133) B3556133
theorem B1404115 : Blo 1403521 1404115 := bstep (se 1 (by rfl) ⟨1053086, by rfl⟩ : syracuseStep 1404115 = 2106173) B2106173
theorem B1404131 : Blo 1403521 1404131 := bstep (se 1 (by rfl) ⟨1053098, by rfl⟩ : syracuseStep 1404131 = 2106197) B2106197
theorem B3796205 : Blo 1403521 3796205 := bstep (se 3 (by rfl) ⟨711788, by rfl⟩ : syracuseStep 3796205 = 1423577) B1423577
theorem B1404147 : Blo 1403521 1404147 := bstep (se 1 (by rfl) ⟨1053110, by rfl⟩ : syracuseStep 1404147 = 2106221) B2106221
theorem B1404163 : Blo 1403521 1404163 := bstep (se 1 (by rfl) ⟨1053122, by rfl⟩ : syracuseStep 1404163 = 2106245) B2106245
theorem B7105805 : Blo 1403521 7105805 := bstep (se 3 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 7105805 = 2664677) B2664677
theorem B1404179 : Blo 1403521 1404179 := bstep (se 1 (by rfl) ⟨1053134, by rfl⟩ : syracuseStep 1404179 = 2106269) B2106269
theorem B1404195 : Blo 1403521 1404195 := bstep (se 1 (by rfl) ⟨1053146, by rfl⟩ : syracuseStep 1404195 = 2106293) B2106293
theorem B1404211 : Blo 1403521 1404211 := bstep (se 1 (by rfl) ⟨1053158, by rfl⟩ : syracuseStep 1404211 = 2106317) B2106317
theorem B1404227 : Blo 1403521 1404227 := bstep (se 1 (by rfl) ⟨1053170, by rfl⟩ : syracuseStep 1404227 = 2106341) B2106341
theorem B2370883 : Blo 1403521 2370883 := bstep (se 1 (by rfl) ⟨1778162, by rfl⟩ : syracuseStep 2370883 = 3556325) B3556325
theorem B1404243 : Blo 1403521 1404243 := bstep (se 1 (by rfl) ⟨1053182, by rfl⟩ : syracuseStep 1404243 = 2106365) B2106365
theorem B1404259 : Blo 1403521 1404259 := bstep (se 1 (by rfl) ⟨1053194, by rfl⟩ : syracuseStep 1404259 = 2106389) B2106389
theorem B34614641 : Blo 1403521 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B1404275 : Blo 1403521 1404275 := bstep (se 1 (by rfl) ⟨1053206, by rfl⟩ : syracuseStep 1404275 = 2106413) B2106413
theorem B1404291 : Blo 1403521 1404291 := bstep (se 1 (by rfl) ⟨1053218, by rfl⟩ : syracuseStep 1404291 = 2106437) B2106437
theorem B4738445 : Blo 1403521 4738445 := bstep (se 3 (by rfl) ⟨888458, by rfl⟩ : syracuseStep 4738445 = 1776917) B1776917
theorem B1404307 : Blo 1403521 1404307 := bstep (se 1 (by rfl) ⟨1053230, by rfl⟩ : syracuseStep 1404307 = 2106461) B2106461
theorem B1404323 : Blo 1403521 1404323 := bstep (se 1 (by rfl) ⟨1053242, by rfl⟩ : syracuseStep 1404323 = 2106485) B2106485
theorem B4001197 : Blo 1403521 4001197 := bstep (se 3 (by rfl) ⟨750224, by rfl⟩ : syracuseStep 4001197 = 1500449) B1500449
theorem B7589297 : Blo 1403521 7589297 := bstep (se 2 (by rfl) ⟨2845986, by rfl⟩ : syracuseStep 7589297 = 5691973) B5691973
theorem B2280881 : Blo 1403521 2280881 := bstep (se 2 (by rfl) ⟨855330, by rfl⟩ : syracuseStep 2280881 = 1710661) B1710661
theorem B1404339 : Blo 1403521 1404339 := bstep (se 1 (by rfl) ⟨1053254, by rfl⟩ : syracuseStep 1404339 = 2106509) B2106509
theorem B4738499 : Blo 1403521 4738499 := bstep (se 1 (by rfl) ⟨3553874, by rfl⟩ : syracuseStep 4738499 = 7107749) B7107749
theorem B3419587 : Blo 1403521 3419587 := bstep (se 1 (by rfl) ⟨2564690, by rfl⟩ : syracuseStep 3419587 = 5129381) B5129381
theorem B1404355 : Blo 1403521 1404355 := bstep (se 1 (by rfl) ⟨1053266, by rfl⟩ : syracuseStep 1404355 = 2106533) B2106533
theorem B2371025 : Blo 1403521 2371025 := bstep (se 2 (by rfl) ⟨889134, by rfl⟩ : syracuseStep 2371025 = 1778269) B1778269
theorem B1404371 : Blo 1403521 1404371 := bstep (se 1 (by rfl) ⟨1053278, by rfl⟩ : syracuseStep 1404371 = 2106557) B2106557
theorem B1404387 : Blo 1403521 1404387 := bstep (se 1 (by rfl) ⟨1053290, by rfl⟩ : syracuseStep 1404387 = 2106581) B2106581
theorem B1404403 : Blo 1403521 1404403 := bstep (se 1 (by rfl) ⟨1053302, by rfl⟩ : syracuseStep 1404403 = 2106605) B2106605
theorem B1404419 : Blo 1403521 1404419 := bstep (se 1 (by rfl) ⟨1053314, by rfl⟩ : syracuseStep 1404419 = 2106629) B2106629
theorem B1404435 : Blo 1403521 1404435 := bstep (se 1 (by rfl) ⟨1053326, by rfl⟩ : syracuseStep 1404435 = 2106653) B2106653
theorem B1404451 : Blo 1403521 1404451 := bstep (se 1 (by rfl) ⟨1053338, by rfl⟩ : syracuseStep 1404451 = 2106677) B2106677
theorem B8547889 : Blo 1403521 8547889 := bstep (se 2 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 8547889 = 6410917) B6410917
theorem B1404467 : Blo 1403521 1404467 := bstep (se 1 (by rfl) ⟨1053350, by rfl⟩ : syracuseStep 1404467 = 2106701) B2106701
theorem B1404483 : Blo 1403521 1404483 := bstep (se 1 (by rfl) ⟨1053362, by rfl⟩ : syracuseStep 1404483 = 2106725) B2106725
theorem B2371153 : Blo 1403521 2371153 := bstep (se 2 (by rfl) ⟨889182, by rfl⟩ : syracuseStep 2371153 = 1778365) B1778365
theorem B1404499 : Blo 1403521 1404499 := bstep (se 1 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 1404499 = 2106749) B2106749
theorem B1404515 : Blo 1403521 1404515 := bstep (se 1 (by rfl) ⟨1053386, by rfl⟩ : syracuseStep 1404515 = 2106773) B2106773
theorem B3247715 : Blo 1403521 3247715 := bstep (se 1 (by rfl) ⟨2435786, by rfl⟩ : syracuseStep 3247715 = 4871573) B4871573
theorem B1404531 : Blo 1403521 1404531 := bstep (se 1 (by rfl) ⟨1053398, by rfl⟩ : syracuseStep 1404531 = 2106797) B2106797
theorem B2371187 : Blo 1403521 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B1404547 : Blo 1403521 1404547 := bstep (se 1 (by rfl) ⟨1053410, by rfl⟩ : syracuseStep 1404547 = 2106821) B2106821
theorem B24333965 : Blo 1403521 24333965 := bstep (se 3 (by rfl) ⟨4562618, by rfl⟩ : syracuseStep 24333965 = 9125237) B9125237
theorem B1404563 : Blo 1403521 1404563 := bstep (se 1 (by rfl) ⟨1053422, by rfl⟩ : syracuseStep 1404563 = 2106845) B2106845
theorem B1404579 : Blo 1403521 1404579 := bstep (se 1 (by rfl) ⟨1053434, by rfl⟩ : syracuseStep 1404579 = 2106869) B2106869
theorem B1404595 : Blo 1403521 1404595 := bstep (se 1 (by rfl) ⟨1053446, by rfl⟩ : syracuseStep 1404595 = 2106893) B2106893
theorem B1404611 : Blo 1403521 1404611 := bstep (se 1 (by rfl) ⟨1053458, by rfl⟩ : syracuseStep 1404611 = 2106917) B2106917
theorem B9875141 : Blo 1403521 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B7999181 : Blo 1403521 7999181 := bstep (se 3 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 7999181 = 2999693) B2999693
theorem B4738769 : Blo 1403521 4738769 := bstep (se 2 (by rfl) ⟨1777038, by rfl⟩ : syracuseStep 4738769 = 3554077) B3554077
theorem B1404627 : Blo 1403521 1404627 := bstep (se 1 (by rfl) ⟨1053470, by rfl⟩ : syracuseStep 1404627 = 2106941) B2106941
theorem B1404643 : Blo 1403521 1404643 := bstep (se 1 (by rfl) ⟨1053482, by rfl⟩ : syracuseStep 1404643 = 2106965) B2106965
theorem B48680675 : Blo 1403521 48680675 := bstep (se 1 (by rfl) ⟨36510506, by rfl⟩ : syracuseStep 48680675 = 73021013) B73021013
theorem B1404659 : Blo 1403521 1404659 := bstep (se 1 (by rfl) ⟨1053494, by rfl⟩ : syracuseStep 1404659 = 2106989) B2106989
theorem B2371315 : Blo 1403521 2371315 := bstep (se 1 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 2371315 = 3556973) B3556973
theorem B1404675 : Blo 1403521 1404675 := bstep (se 1 (by rfl) ⟨1053506, by rfl⟩ : syracuseStep 1404675 = 2107013) B2107013
theorem B1404691 : Blo 1403521 1404691 := bstep (se 1 (by rfl) ⟨1053518, by rfl⟩ : syracuseStep 1404691 = 2107037) B2107037
theorem B1404707 : Blo 1403521 1404707 := bstep (se 1 (by rfl) ⟨1053530, by rfl⟩ : syracuseStep 1404707 = 2107061) B2107061
theorem B1404723 : Blo 1403521 1404723 := bstep (se 1 (by rfl) ⟨1053542, by rfl⟩ : syracuseStep 1404723 = 2107085) B2107085
theorem B1404739 : Blo 1403521 1404739 := bstep (se 1 (by rfl) ⟨1053554, by rfl⟩ : syracuseStep 1404739 = 2107109) B2107109
theorem B1404755 : Blo 1403521 1404755 := bstep (se 1 (by rfl) ⟨1053566, by rfl⟩ : syracuseStep 1404755 = 2107133) B2107133
theorem B1404771 : Blo 1403521 1404771 := bstep (se 1 (by rfl) ⟨1053578, by rfl⟩ : syracuseStep 1404771 = 2107157) B2107157
theorem B1404787 : Blo 1403521 1404787 := bstep (se 1 (by rfl) ⟨1053590, by rfl⟩ : syracuseStep 1404787 = 2107181) B2107181
theorem B2371457 : Blo 1403521 2371457 := bstep (se 2 (by rfl) ⟨889296, by rfl⟩ : syracuseStep 2371457 = 1778593) B1778593
theorem B2666371 : Blo 1403521 2666371 := bstep (se 1 (by rfl) ⟨1999778, by rfl⟩ : syracuseStep 2666371 = 3999557) B3999557
theorem B1404803 : Blo 1403521 1404803 := bstep (se 1 (by rfl) ⟨1053602, by rfl⟩ : syracuseStep 1404803 = 2107205) B2107205
theorem B1404819 : Blo 1403521 1404819 := bstep (se 1 (by rfl) ⟨1053614, by rfl⟩ : syracuseStep 1404819 = 2107229) B2107229
theorem B1404835 : Blo 1403521 1404835 := bstep (se 1 (by rfl) ⟨1053626, by rfl⟩ : syracuseStep 1404835 = 2107253) B2107253
theorem B3157937 : Blo 1403521 3157937 := bstep (se 2 (by rfl) ⟨1184226, by rfl⟩ : syracuseStep 3157937 = 2368453) B2368453
theorem B1404851 : Blo 1403521 1404851 := bstep (se 1 (by rfl) ⟨1053638, by rfl⟩ : syracuseStep 1404851 = 2107277) B2107277
theorem B3157955 : Blo 1403521 3157955 := bstep (se 1 (by rfl) ⟨2368466, by rfl⟩ : syracuseStep 3157955 = 4736933) B4736933
theorem B2248643 : Blo 1403521 2248643 := bstep (se 1 (by rfl) ⟨1686482, by rfl⟩ : syracuseStep 2248643 = 3372965) B3372965
theorem B1404867 : Blo 1403521 1404867 := bstep (se 1 (by rfl) ⟨1053650, by rfl⟩ : syracuseStep 1404867 = 2107301) B2107301
theorem B5771213 : Blo 1403521 5771213 := bstep (se 3 (by rfl) ⟨1082102, by rfl⟩ : syracuseStep 5771213 = 2164205) B2164205
theorem B1404883 : Blo 1403521 1404883 := bstep (se 1 (by rfl) ⟨1053662, by rfl⟩ : syracuseStep 1404883 = 2107325) B2107325
theorem B2281441 : Blo 1403521 2281441 := bstep (se 2 (by rfl) ⟨855540, by rfl⟩ : syracuseStep 2281441 = 1711081) B1711081
theorem B1404899 : Blo 1403521 1404899 := bstep (se 1 (by rfl) ⟨1053674, by rfl⟩ : syracuseStep 1404899 = 2107349) B2107349
theorem B1404915 : Blo 1403521 1404915 := bstep (se 1 (by rfl) ⟨1053686, by rfl⟩ : syracuseStep 1404915 = 2107373) B2107373
theorem B2371585 : Blo 1403521 2371585 := bstep (se 2 (by rfl) ⟨889344, by rfl⟩ : syracuseStep 2371585 = 1778689) B1778689
theorem B1404931 : Blo 1403521 1404931 := bstep (se 1 (by rfl) ⟨1053698, by rfl⟩ : syracuseStep 1404931 = 2107397) B2107397
theorem B1404947 : Blo 1403521 1404947 := bstep (se 1 (by rfl) ⟨1053710, by rfl⟩ : syracuseStep 1404947 = 2107421) B2107421
theorem B1404963 : Blo 1403521 1404963 := bstep (se 1 (by rfl) ⟨1053722, by rfl⟩ : syracuseStep 1404963 = 2107445) B2107445
theorem B2371619 : Blo 1403521 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B1404979 : Blo 1403521 1404979 := bstep (se 1 (by rfl) ⟨1053734, by rfl⟩ : syracuseStep 1404979 = 2107469) B2107469
theorem B1404995 : Blo 1403521 1404995 := bstep (se 1 (by rfl) ⟨1053746, by rfl⟩ : syracuseStep 1404995 = 2107493) B2107493
theorem B1405011 : Blo 1403521 1405011 := bstep (se 1 (by rfl) ⟨1053758, by rfl⟩ : syracuseStep 1405011 = 2107517) B2107517
theorem B1405027 : Blo 1403521 1405027 := bstep (se 1 (by rfl) ⟨1053770, by rfl⟩ : syracuseStep 1405027 = 2107541) B2107541
theorem B30363761 : Blo 1403521 30363761 := bstep (se 2 (by rfl) ⟨11386410, by rfl⟩ : syracuseStep 30363761 = 22772821) B22772821
theorem B1405043 : Blo 1403521 1405043 := bstep (se 1 (by rfl) ⟨1053782, by rfl⟩ : syracuseStep 1405043 = 2107565) B2107565
theorem B1405059 : Blo 1403521 1405059 := bstep (se 1 (by rfl) ⟨1053794, by rfl⟩ : syracuseStep 1405059 = 2107589) B2107589
theorem B1405075 : Blo 1403521 1405075 := bstep (se 1 (by rfl) ⟨1053806, by rfl⟩ : syracuseStep 1405075 = 2107613) B2107613
theorem B1405091 : Blo 1403521 1405091 := bstep (se 1 (by rfl) ⟨1053818, by rfl⟩ : syracuseStep 1405091 = 2107637) B2107637
theorem B2371747 : Blo 1403521 2371747 := bstep (se 1 (by rfl) ⟨1778810, by rfl⟩ : syracuseStep 2371747 = 3557621) B3557621
theorem B2134193 : Blo 1403521 2134193 := bstep (se 2 (by rfl) ⟨800322, by rfl⟩ : syracuseStep 2134193 = 1600645) B1600645
theorem B1405107 : Blo 1403521 1405107 := bstep (se 1 (by rfl) ⟨1053830, by rfl⟩ : syracuseStep 1405107 = 2107661) B2107661
theorem B1405123 : Blo 1403521 1405123 := bstep (se 1 (by rfl) ⟨1053842, by rfl⟩ : syracuseStep 1405123 = 2107685) B2107685
theorem B3158225 : Blo 1403521 3158225 := bstep (se 2 (by rfl) ⟨1184334, by rfl⟩ : syracuseStep 3158225 = 2368669) B2368669
theorem B1405139 : Blo 1403521 1405139 := bstep (se 1 (by rfl) ⟨1053854, by rfl⟩ : syracuseStep 1405139 = 2107709) B2107709
theorem B3158243 : Blo 1403521 3158243 := bstep (se 1 (by rfl) ⟨2368682, by rfl⟩ : syracuseStep 3158243 = 4737365) B4737365
theorem B2248931 : Blo 1403521 2248931 := bstep (se 1 (by rfl) ⟨1686698, by rfl⟩ : syracuseStep 2248931 = 3373397) B3373397
theorem B1405155 : Blo 1403521 1405155 := bstep (se 1 (by rfl) ⟨1053866, by rfl⟩ : syracuseStep 1405155 = 2107733) B2107733
theorem B4739309 : Blo 1403521 4739309 := bstep (se 3 (by rfl) ⟨888620, by rfl⟩ : syracuseStep 4739309 = 1777241) B1777241
theorem B1405171 : Blo 1403521 1405171 := bstep (se 1 (by rfl) ⟨1053878, by rfl⟩ : syracuseStep 1405171 = 2107757) B2107757
theorem B1405187 : Blo 1403521 1405187 := bstep (se 1 (by rfl) ⟨1053890, by rfl⟩ : syracuseStep 1405187 = 2107781) B2107781
theorem B1405203 : Blo 1403521 1405203 := bstep (se 1 (by rfl) ⟨1053902, by rfl⟩ : syracuseStep 1405203 = 2107805) B2107805
theorem B4739363 : Blo 1403521 4739363 := bstep (se 1 (by rfl) ⟨3554522, by rfl⟩ : syracuseStep 4739363 = 7109045) B7109045
theorem B1405219 : Blo 1403521 1405219 := bstep (se 1 (by rfl) ⟨1053914, by rfl⟩ : syracuseStep 1405219 = 2107829) B2107829
theorem B1405235 : Blo 1403521 1405235 := bstep (se 1 (by rfl) ⟨1053926, by rfl⟩ : syracuseStep 1405235 = 2107853) B2107853
theorem B2666819 : Blo 1403521 2666819 := bstep (se 1 (by rfl) ⟨2000114, by rfl⟩ : syracuseStep 2666819 = 4000229) B4000229
theorem B1405251 : Blo 1403521 1405251 := bstep (se 1 (by rfl) ⟨1053938, by rfl⟩ : syracuseStep 1405251 = 2107877) B2107877
theorem B1405267 : Blo 1403521 1405267 := bstep (se 1 (by rfl) ⟨1053950, by rfl⟩ : syracuseStep 1405267 = 2107901) B2107901
theorem B1405283 : Blo 1403521 1405283 := bstep (se 1 (by rfl) ⟨1053962, by rfl⟩ : syracuseStep 1405283 = 2107925) B2107925
theorem B1405299 : Blo 1403521 1405299 := bstep (se 1 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 1405299 = 2107949) B2107949
theorem B1405315 : Blo 1403521 1405315 := bstep (se 1 (by rfl) ⟨1053986, by rfl⟩ : syracuseStep 1405315 = 2107973) B2107973
theorem B1405331 : Blo 1403521 1405331 := bstep (se 1 (by rfl) ⟨1053998, by rfl⟩ : syracuseStep 1405331 = 2107997) B2107997
theorem B1405347 : Blo 1403521 1405347 := bstep (se 1 (by rfl) ⟨1054010, by rfl⟩ : syracuseStep 1405347 = 2108021) B2108021
theorem B1405363 : Blo 1403521 1405363 := bstep (se 1 (by rfl) ⟨1054022, by rfl⟩ : syracuseStep 1405363 = 2108045) B2108045
theorem B17093045 : Blo 1403521 17093045 := bstep (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) B1602473
theorem B2281921 : Blo 1403521 2281921 := bstep (se 2 (by rfl) ⟨855720, by rfl⟩ : syracuseStep 2281921 = 1711441) B1711441
theorem B2249155 : Blo 1403521 2249155 := bstep (se 1 (by rfl) ⟨1686866, by rfl⟩ : syracuseStep 2249155 = 3373733) B3373733
theorem B1405379 : Blo 1403521 1405379 := bstep (se 1 (by rfl) ⟨1054034, by rfl⟩ : syracuseStep 1405379 = 2108069) B2108069
theorem B1405395 : Blo 1403521 1405395 := bstep (se 1 (by rfl) ⟨1054046, by rfl⟩ : syracuseStep 1405395 = 2108093) B2108093
theorem B1405411 : Blo 1403521 1405411 := bstep (se 1 (by rfl) ⟨1054058, by rfl⟩ : syracuseStep 1405411 = 2108117) B2108117
theorem B3158513 : Blo 1403521 3158513 := bstep (se 2 (by rfl) ⟨1184442, by rfl⟩ : syracuseStep 3158513 = 2368885) B2368885
theorem B1405427 : Blo 1403521 1405427 := bstep (se 1 (by rfl) ⟨1054070, by rfl⟩ : syracuseStep 1405427 = 2108141) B2108141
theorem B3158531 : Blo 1403521 3158531 := bstep (se 1 (by rfl) ⟨2368898, by rfl⟩ : syracuseStep 3158531 = 4737797) B4737797
theorem B1405443 : Blo 1403521 1405443 := bstep (se 1 (by rfl) ⟨1054082, by rfl⟩ : syracuseStep 1405443 = 2108165) B2108165
theorem B8999437 : Blo 1403521 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B1405459 : Blo 1403521 1405459 := bstep (se 1 (by rfl) ⟨1054094, by rfl⟩ : syracuseStep 1405459 = 2108189) B2108189
theorem B1405475 : Blo 1403521 1405475 := bstep (se 1 (by rfl) ⟨1054106, by rfl⟩ : syracuseStep 1405475 = 2108213) B2108213
theorem B4739633 : Blo 1403521 4739633 := bstep (se 2 (by rfl) ⟨1777362, by rfl⟩ : syracuseStep 4739633 = 3554725) B3554725
theorem B1405491 : Blo 1403521 1405491 := bstep (se 1 (by rfl) ⟨1054118, by rfl⟩ : syracuseStep 1405491 = 2108237) B2108237
theorem B1405507 : Blo 1403521 1405507 := bstep (se 1 (by rfl) ⟨1054130, by rfl⟩ : syracuseStep 1405507 = 2108261) B2108261
theorem B15176261 : Blo 1403521 15176261 := bstep (se 4 (by rfl) ⟨1422774, by rfl⟩ : syracuseStep 15176261 = 2845549) B2845549
theorem B2667107 : Blo 1403521 2667107 := bstep (se 1 (by rfl) ⟨2000330, by rfl⟩ : syracuseStep 2667107 = 4000661) B4000661
theorem B7115363 : Blo 1403521 7115363 := bstep (se 1 (by rfl) ⟨5336522, by rfl⟩ : syracuseStep 7115363 = 10673045) B10673045
theorem B6001265 : Blo 1403521 6001265 := bstep (se 2 (by rfl) ⟨2250474, by rfl⟩ : syracuseStep 6001265 = 4500949) B4500949
theorem B4502179 : Blo 1403521 4502179 := bstep (se 1 (by rfl) ⟨3376634, by rfl⟩ : syracuseStep 4502179 = 6753269) B6753269
theorem B3158801 : Blo 1403521 3158801 := bstep (se 2 (by rfl) ⟨1184550, by rfl⟩ : syracuseStep 3158801 = 2369101) B2369101
theorem B3158819 : Blo 1403521 3158819 := bstep (se 1 (by rfl) ⟨2369114, by rfl⟩ : syracuseStep 3158819 = 4738229) B4738229
theorem B15995717 : Blo 1403521 15995717 := bstep (se 4 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 15995717 = 2999197) B2999197
theorem B3159089 : Blo 1403521 3159089 := bstep (se 2 (by rfl) ⟨1184658, by rfl⟩ : syracuseStep 3159089 = 2369317) B2369317
theorem B3159107 : Blo 1403521 3159107 := bstep (se 1 (by rfl) ⟨2369330, by rfl⟩ : syracuseStep 3159107 = 4738661) B4738661
theorem B4740173 : Blo 1403521 4740173 := bstep (se 3 (by rfl) ⟨888782, by rfl⟩ : syracuseStep 4740173 = 1777565) B1777565
theorem B4330577 : Blo 1403521 4330577 := bstep (se 2 (by rfl) ⟨1623966, by rfl⟩ : syracuseStep 4330577 = 3247933) B3247933
theorem B4502641 : Blo 1403521 4502641 := bstep (se 2 (by rfl) ⟨1688490, by rfl⟩ : syracuseStep 4502641 = 3376981) B3376981
theorem B4740227 : Blo 1403521 4740227 := bstep (se 1 (by rfl) ⟨3555170, by rfl⟩ : syracuseStep 4740227 = 7110341) B7110341
theorem B2249873 : Blo 1403521 2249873 := bstep (se 2 (by rfl) ⟨843702, by rfl⟩ : syracuseStep 2249873 = 1687405) B1687405
theorem B5330083 : Blo 1403521 5330083 := bstep (se 1 (by rfl) ⟨3997562, by rfl⟩ : syracuseStep 5330083 = 7995125) B7995125
theorem B1897795 : Blo 1403521 1897795 := bstep (se 1 (by rfl) ⟨1423346, by rfl⟩ : syracuseStep 1897795 = 2846693) B2846693
theorem B3159377 : Blo 1403521 3159377 := bstep (se 2 (by rfl) ⟨1184766, by rfl⟩ : syracuseStep 3159377 = 2369533) B2369533
theorem B2250065 : Blo 1403521 2250065 := bstep (se 2 (by rfl) ⟨843774, by rfl⟩ : syracuseStep 2250065 = 1687549) B1687549
theorem B3159395 : Blo 1403521 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B16004465 : Blo 1403521 16004465 := bstep (se 2 (by rfl) ⟨6001674, by rfl⟩ : syracuseStep 16004465 = 12003349) B12003349
theorem B4740497 : Blo 1403521 4740497 := bstep (se 2 (by rfl) ⟨1777686, by rfl⟩ : syracuseStep 4740497 = 3555373) B3555373
theorem B2250193 : Blo 1403521 2250193 := bstep (se 2 (by rfl) ⟨843822, by rfl⟩ : syracuseStep 2250193 = 1687645) B1687645
theorem B7206371 : Blo 1403521 7206371 := bstep (se 1 (by rfl) ⟨5404778, by rfl⟩ : syracuseStep 7206371 = 10809557) B10809557
theorem B10671587 : Blo 1403521 10671587 := bstep (se 1 (by rfl) ⟨8003690, by rfl⟩ : syracuseStep 10671587 = 16007381) B16007381
theorem B2668049 : Blo 1403521 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B3159665 : Blo 1403521 3159665 := bstep (se 2 (by rfl) ⟨1184874, by rfl⟩ : syracuseStep 3159665 = 2369749) B2369749
theorem B3159683 : Blo 1403521 3159683 := bstep (se 1 (by rfl) ⟨2369762, by rfl⟩ : syracuseStep 3159683 = 4739525) B4739525
theorem B2135683 : Blo 1403521 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B2135731 : Blo 1403521 2135731 := bstep (se 1 (by rfl) ⟨1601798, by rfl⟩ : syracuseStep 2135731 = 3203597) B3203597
theorem B9246469 : Blo 1403521 9246469 := bstep (se 4 (by rfl) ⟨866856, by rfl⟩ : syracuseStep 9246469 = 1733713) B1733713
theorem B3553105 : Blo 1403521 3553105 := bstep (se 2 (by rfl) ⟨1332414, by rfl⟩ : syracuseStep 3553105 = 2664829) B2664829
theorem B6002531 : Blo 1403521 6002531 := bstep (se 1 (by rfl) ⟨4501898, by rfl⟩ : syracuseStep 6002531 = 9003797) B9003797
theorem B8001413 : Blo 1403521 8001413 := bstep (se 4 (by rfl) ⟨750132, by rfl⟩ : syracuseStep 8001413 = 1500265) B1500265
theorem B3159953 : Blo 1403521 3159953 := bstep (se 2 (by rfl) ⟨1184982, by rfl⟩ : syracuseStep 3159953 = 2369965) B2369965
theorem B3159971 : Blo 1403521 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B4741037 : Blo 1403521 4741037 := bstep (se 3 (by rfl) ⟨888944, by rfl⟩ : syracuseStep 4741037 = 1777889) B1777889
theorem B1898417 : Blo 1403521 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B4741091 : Blo 1403521 4741091 := bstep (se 1 (by rfl) ⟨3555818, by rfl⟩ : syracuseStep 4741091 = 7111637) B7111637
theorem B5134349 : Blo 1403521 5134349 := bstep (se 3 (by rfl) ⟨962690, by rfl⟩ : syracuseStep 5134349 = 1925381) B1925381
theorem B1579027 : Blo 1403521 1579027 := bstep (se 1 (by rfl) ⟨1184270, by rfl⟩ : syracuseStep 1579027 = 2368541) B2368541
theorem B2250833 : Blo 1403521 2250833 := bstep (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) B1688125
theorem B5691491 : Blo 1403521 5691491 := bstep (se 1 (by rfl) ⟨4268618, by rfl⟩ : syracuseStep 5691491 = 8537237) B8537237
theorem B3553379 : Blo 1403521 3553379 := bstep (se 1 (by rfl) ⟨2665034, by rfl⟩ : syracuseStep 3553379 = 5330069) B5330069
theorem B7108721 : Blo 1403521 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B1579171 : Blo 1403521 1579171 := bstep (se 1 (by rfl) ⟨1184378, by rfl⟩ : syracuseStep 1579171 = 2368757) B2368757
theorem B3160241 : Blo 1403521 3160241 := bstep (se 2 (by rfl) ⟨1185090, by rfl⟩ : syracuseStep 3160241 = 2370181) B2370181
theorem B3160259 : Blo 1403521 3160259 := bstep (se 1 (by rfl) ⟨2370194, by rfl⟩ : syracuseStep 3160259 = 4740389) B4740389
theorem B9607373 : Blo 1403521 9607373 := bstep (se 3 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 9607373 = 3602765) B3602765
theorem B17996003 : Blo 1403521 17996003 := bstep (se 1 (by rfl) ⟨13497002, by rfl⟩ : syracuseStep 17996003 = 26994005) B26994005
theorem B4741361 : Blo 1403521 4741361 := bstep (se 2 (by rfl) ⟨1778010, by rfl⟩ : syracuseStep 4741361 = 3556021) B3556021
theorem B3553571 : Blo 1403521 3553571 := bstep (se 1 (by rfl) ⟨2665178, by rfl⟩ : syracuseStep 3553571 = 5330357) B5330357
theorem B1579315 : Blo 1403521 1579315 := bstep (se 1 (by rfl) ⟨1184486, by rfl⟩ : syracuseStep 1579315 = 2368973) B2368973
theorem B1579459 : Blo 1403521 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B3160529 : Blo 1403521 3160529 := bstep (se 2 (by rfl) ⟨1185198, by rfl⟩ : syracuseStep 3160529 = 2370397) B2370397
theorem B3160547 : Blo 1403521 3160547 := bstep (se 1 (by rfl) ⟨2370410, by rfl⟩ : syracuseStep 3160547 = 4740821) B4740821
theorem B17783309 : Blo 1403521 17783309 := bstep (se 3 (by rfl) ⟨3334370, by rfl⟩ : syracuseStep 17783309 = 6668741) B6668741
theorem B8002097 : Blo 1403521 8002097 := bstep (se 2 (by rfl) ⟨3000786, by rfl⟩ : syracuseStep 8002097 = 6001573) B6001573
theorem B1579603 : Blo 1403521 1579603 := bstep (se 1 (by rfl) ⟨1184702, by rfl⟩ : syracuseStep 1579603 = 2369405) B2369405
theorem B5995235 : Blo 1403521 5995235 := bstep (se 1 (by rfl) ⟨4496426, by rfl⟩ : syracuseStep 5995235 = 8992853) B8992853
theorem B1579747 : Blo 1403521 1579747 := bstep (se 1 (by rfl) ⟨1184810, by rfl⟩ : syracuseStep 1579747 = 2369621) B2369621
theorem B3160817 : Blo 1403521 3160817 := bstep (se 2 (by rfl) ⟨1185306, by rfl⟩ : syracuseStep 3160817 = 2370613) B2370613
theorem B3160835 : Blo 1403521 3160835 := bstep (se 1 (by rfl) ⟨2370626, by rfl⟩ : syracuseStep 3160835 = 4741253) B4741253
theorem B14408461 : Blo 1403521 14408461 := bstep (se 3 (by rfl) ⟨2701586, by rfl⟩ : syracuseStep 14408461 = 5403173) B5403173
theorem B4741901 : Blo 1403521 4741901 := bstep (se 3 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 4741901 = 1778213) B1778213
theorem B4741955 : Blo 1403521 4741955 := bstep (se 1 (by rfl) ⟨3556466, by rfl⟩ : syracuseStep 4741955 = 7112933) B7112933
theorem B6749041 : Blo 1403521 6749041 := bstep (se 2 (by rfl) ⟨2530890, by rfl⟩ : syracuseStep 6749041 = 5061781) B5061781
theorem B1579891 : Blo 1403521 1579891 := bstep (se 1 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 1579891 = 2369837) B2369837
theorem B1580035 : Blo 1403521 1580035 := bstep (se 1 (by rfl) ⟨1185026, by rfl⟩ : syracuseStep 1580035 = 2370053) B2370053
theorem B7691269 : Blo 1403521 7691269 := bstep (se 4 (by rfl) ⟨721056, by rfl⟩ : syracuseStep 7691269 = 1442113) B1442113
theorem B3161105 : Blo 1403521 3161105 := bstep (se 2 (by rfl) ⟨1185414, by rfl⟩ : syracuseStep 3161105 = 2370829) B2370829
theorem B3161123 : Blo 1403521 3161123 := bstep (se 1 (by rfl) ⟨2370842, by rfl⟩ : syracuseStep 3161123 = 4741685) B4741685
theorem B5479501 : Blo 1403521 5479501 := bstep (se 3 (by rfl) ⟨1027406, by rfl⟩ : syracuseStep 5479501 = 2054813) B2054813
theorem B4496465 : Blo 1403521 4496465 := bstep (se 2 (by rfl) ⟨1686174, by rfl⟩ : syracuseStep 4496465 = 3372349) B3372349
theorem B4742225 : Blo 1403521 4742225 := bstep (se 2 (by rfl) ⟨1778334, by rfl⟩ : syracuseStep 4742225 = 3556669) B3556669
theorem B1776755 : Blo 1403521 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B1580179 : Blo 1403521 1580179 := bstep (se 1 (by rfl) ⟨1185134, by rfl⟩ : syracuseStep 1580179 = 2370269) B2370269
theorem B4496593 : Blo 1403521 4496593 := bstep (se 2 (by rfl) ⟨1686222, by rfl⟩ : syracuseStep 4496593 = 3372445) B3372445
theorem B3554513 : Blo 1403521 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B3554563 : Blo 1403521 3554563 := bstep (se 1 (by rfl) ⟨2665922, by rfl⟩ : syracuseStep 3554563 = 5331845) B5331845
theorem B1580323 : Blo 1403521 1580323 := bstep (se 1 (by rfl) ⟨1185242, by rfl⟩ : syracuseStep 1580323 = 2370485) B2370485
theorem B3161393 : Blo 1403521 3161393 := bstep (se 2 (by rfl) ⟨1185522, by rfl⟩ : syracuseStep 3161393 = 2371045) B2371045
theorem B3161411 : Blo 1403521 3161411 := bstep (se 1 (by rfl) ⟨2371058, by rfl⟩ : syracuseStep 3161411 = 4742117) B4742117
theorem B5332301 : Blo 1403521 5332301 := bstep (se 3 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 5332301 = 1999613) B1999613
theorem B3554705 : Blo 1403521 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B1580467 : Blo 1403521 1580467 := bstep (se 1 (by rfl) ⟨1185350, by rfl⟩ : syracuseStep 1580467 = 2370701) B2370701
theorem B4496849 : Blo 1403521 4496849 := bstep (se 2 (by rfl) ⟨1686318, by rfl⟩ : syracuseStep 4496849 = 3372637) B3372637
theorem B7110179 : Blo 1403521 7110179 := bstep (se 1 (by rfl) ⟨5332634, by rfl⟩ : syracuseStep 7110179 = 10665269) B10665269
theorem B1580611 : Blo 1403521 1580611 := bstep (se 1 (by rfl) ⟨1185458, by rfl⟩ : syracuseStep 1580611 = 2370917) B2370917
theorem B3161681 : Blo 1403521 3161681 := bstep (se 2 (by rfl) ⟨1185630, by rfl⟩ : syracuseStep 3161681 = 2371261) B2371261
theorem B3161699 : Blo 1403521 3161699 := bstep (se 1 (by rfl) ⟨2371274, by rfl⟩ : syracuseStep 3161699 = 4742549) B4742549
theorem B4742765 : Blo 1403521 4742765 := bstep (se 3 (by rfl) ⟨889268, by rfl⟩ : syracuseStep 4742765 = 1778537) B1778537
theorem B4742819 : Blo 1403521 4742819 := bstep (se 1 (by rfl) ⟨3557114, by rfl⟩ : syracuseStep 4742819 = 7114229) B7114229
theorem B1580755 : Blo 1403521 1580755 := bstep (se 1 (by rfl) ⟨1185566, by rfl⟩ : syracuseStep 1580755 = 2371133) B2371133
theorem B5775089 : Blo 1403521 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B1777459 : Blo 1403521 1777459 := bstep (se 1 (by rfl) ⟨1333094, by rfl⟩ : syracuseStep 1777459 = 2666189) B2666189
theorem B1580899 : Blo 1403521 1580899 := bstep (se 1 (by rfl) ⟨1185674, by rfl⟩ : syracuseStep 1580899 = 2371349) B2371349
theorem B15179633 : Blo 1403521 15179633 := bstep (se 2 (by rfl) ⟨5692362, by rfl⟩ : syracuseStep 15179633 = 11384725) B11384725
theorem B3161969 : Blo 1403521 3161969 := bstep (se 2 (by rfl) ⟨1185738, by rfl⟩ : syracuseStep 3161969 = 2371477) B2371477
theorem B3161987 : Blo 1403521 3161987 := bstep (se 1 (by rfl) ⟨2371490, by rfl⟩ : syracuseStep 3161987 = 4742981) B4742981
theorem B1777555 : Blo 1403521 1777555 := bstep (se 1 (by rfl) ⟨1333166, by rfl⟩ : syracuseStep 1777555 = 2666333) B2666333
theorem B4743089 : Blo 1403521 4743089 := bstep (se 2 (by rfl) ⟨1778658, by rfl⟩ : syracuseStep 4743089 = 3557317) B3557317
theorem B2105297 : Blo 1403521 2105297 := bstep (se 2 (by rfl) ⟨789486, by rfl⟩ : syracuseStep 2105297 = 1578973) B1578973
theorem B2105315 : Blo 1403521 2105315 := bstep (se 1 (by rfl) ⟨1578986, by rfl⟩ : syracuseStep 2105315 = 3157973) B3157973
theorem B8003555 : Blo 1403521 8003555 := bstep (se 1 (by rfl) ⟨6002666, by rfl⟩ : syracuseStep 8003555 = 12005333) B12005333
theorem B1581043 : Blo 1403521 1581043 := bstep (se 1 (by rfl) ⟨1185782, by rfl⟩ : syracuseStep 1581043 = 2371565) B2371565
theorem B3162113 : Blo 1403521 3162113 := bstep (se 2 (by rfl) ⟨1185792, by rfl⟩ : syracuseStep 3162113 = 2371585) B2371585
theorem B1581079 : Blo 1403521 1581079 := bstep (se 1 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 1581079 = 2371619) B2371619
theorem B2105369 : Blo 1403521 2105369 := bstep (se 2 (by rfl) ⟨789513, by rfl⟩ : syracuseStep 2105369 = 1579027) B1579027
theorem B20242507 : Blo 1403521 20242507 := bstep (se 1 (by rfl) ⟨15181880, by rfl⟩ : syracuseStep 20242507 = 30363761) B30363761
theorem B2105483 : Blo 1403521 2105483 := bstep (se 1 (by rfl) ⟨1579112, by rfl⟩ : syracuseStep 2105483 = 3158225) B3158225
theorem B2105495 : Blo 1403521 2105495 := bstep (se 1 (by rfl) ⟨1579121, by rfl⟩ : syracuseStep 2105495 = 3158243) B3158243
theorem B1777879 : Blo 1403521 1777879 := bstep (se 1 (by rfl) ⟨1333409, by rfl⟩ : syracuseStep 1777879 = 2666819) B2666819
theorem B2105561 : Blo 1403521 2105561 := bstep (se 2 (by rfl) ⟨789585, by rfl⟩ : syracuseStep 2105561 = 1579171) B1579171
theorem B3162329 : Blo 1403521 3162329 := bstep (se 2 (by rfl) ⟨1185873, by rfl⟩ : syracuseStep 3162329 = 2371747) B2371747
theorem B3162419 : Blo 1403521 3162419 := bstep (se 1 (by rfl) ⟨2371814, by rfl⟩ : syracuseStep 3162419 = 4743629) B4743629
theorem B3375425 : Blo 1403521 3375425 := bstep (se 2 (by rfl) ⟨1265784, by rfl⟩ : syracuseStep 3375425 = 2531569) B2531569
theorem B2105675 : Blo 1403521 2105675 := bstep (se 1 (by rfl) ⟨1579256, by rfl⟩ : syracuseStep 2105675 = 3158513) B3158513
theorem B5996875 : Blo 1403521 5996875 := bstep (se 1 (by rfl) ⟨4497656, by rfl⟩ : syracuseStep 5996875 = 8995313) B8995313
theorem B2105687 : Blo 1403521 2105687 := bstep (se 1 (by rfl) ⟨1579265, by rfl⟩ : syracuseStep 2105687 = 3158531) B3158531
theorem B10117507 : Blo 1403521 10117507 := bstep (se 1 (by rfl) ⟨7588130, by rfl⟩ : syracuseStep 10117507 = 15176261) B15176261
theorem B4743575 : Blo 1403521 4743575 := bstep (se 1 (by rfl) ⟨3557681, by rfl⟩ : syracuseStep 4743575 = 7115363) B7115363
theorem B2105753 : Blo 1403521 2105753 := bstep (se 2 (by rfl) ⟨789657, by rfl⟩ : syracuseStep 2105753 = 1579315) B1579315
theorem B3998155 : Blo 1403521 3998155 := bstep (se 1 (by rfl) ⟨2998616, by rfl⟩ : syracuseStep 3998155 = 5997233) B5997233
theorem B2105867 : Blo 1403521 2105867 := bstep (se 1 (by rfl) ⟨1579400, by rfl⟩ : syracuseStep 2105867 = 3158801) B3158801
theorem B36463121 : Blo 1403521 36463121 := bstep (se 2 (by rfl) ⟨13673670, by rfl⟩ : syracuseStep 36463121 = 27347341) B27347341
theorem B2105879 : Blo 1403521 2105879 := bstep (se 1 (by rfl) ⟨1579409, by rfl⟩ : syracuseStep 2105879 = 3158819) B3158819
theorem B1688087 : Blo 1403521 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B2105945 : Blo 1403521 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B2998873 : Blo 1403521 2998873 := bstep (se 2 (by rfl) ⟨1124577, by rfl⟩ : syracuseStep 2998873 = 2249155) B2249155
theorem B5997149 : Blo 1403521 5997149 := bstep (se 3 (by rfl) ⟨1124465, by rfl⟩ : syracuseStep 5997149 = 2248931) B2248931
theorem B21627485 : Blo 1403521 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B2106059 : Blo 1403521 2106059 := bstep (se 1 (by rfl) ⟨1579544, by rfl⟩ : syracuseStep 2106059 = 3159089) B3159089
theorem B2106071 : Blo 1403521 2106071 := bstep (se 1 (by rfl) ⟨1579553, by rfl⟩ : syracuseStep 2106071 = 3159107) B3159107
theorem B3998429 : Blo 1403521 3998429 := bstep (se 3 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 3998429 = 1499411) B1499411
theorem B2999027 : Blo 1403521 2999027 := bstep (se 1 (by rfl) ⟨2249270, by rfl⟩ : syracuseStep 2999027 = 4498541) B4498541
theorem B1499915 : Blo 1403521 1499915 := bstep (se 1 (by rfl) ⟨1124936, by rfl⟩ : syracuseStep 1499915 = 2249873) B2249873
theorem B4621079 : Blo 1403521 4621079 := bstep (se 1 (by rfl) ⟨3465809, by rfl⟩ : syracuseStep 4621079 = 6931619) B6931619
theorem B2106137 : Blo 1403521 2106137 := bstep (se 2 (by rfl) ⟨789801, by rfl⟩ : syracuseStep 2106137 = 1579603) B1579603
theorem B5063555 : Blo 1403521 5063555 := bstep (se 1 (by rfl) ⟨3797666, by rfl⟩ : syracuseStep 5063555 = 7595333) B7595333
theorem B2106251 : Blo 1403521 2106251 := bstep (se 1 (by rfl) ⟨1579688, by rfl⟩ : syracuseStep 2106251 = 3159377) B3159377
theorem B1500043 : Blo 1403521 1500043 := bstep (se 1 (by rfl) ⟨1125032, by rfl⟩ : syracuseStep 1500043 = 2250065) B2250065
theorem B2106263 : Blo 1403521 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B5063627 : Blo 1403521 5063627 := bstep (se 1 (by rfl) ⟨3797720, by rfl⟩ : syracuseStep 5063627 = 7595441) B7595441
theorem B2106329 : Blo 1403521 2106329 := bstep (se 2 (by rfl) ⟨789873, by rfl⟩ : syracuseStep 2106329 = 1579747) B1579747
theorem B5694425 : Blo 1403521 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B1778699 : Blo 1403521 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B3998771 : Blo 1403521 3998771 := bstep (se 1 (by rfl) ⟨2999078, by rfl⟩ : syracuseStep 3998771 = 5998157) B5998157
theorem B2106443 : Blo 1403521 2106443 := bstep (se 1 (by rfl) ⟨1579832, by rfl⟩ : syracuseStep 2106443 = 3159665) B3159665
theorem B2106455 : Blo 1403521 2106455 := bstep (se 1 (by rfl) ⟨1579841, by rfl⟩ : syracuseStep 2106455 = 3159683) B3159683
theorem B45581453 : Blo 1403521 45581453 := bstep (se 3 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 45581453 = 17093045) B17093045
theorem B2106521 : Blo 1403521 2106521 := bstep (se 2 (by rfl) ⟨789945, by rfl⟩ : syracuseStep 2106521 = 1579891) B1579891
theorem B10667213 : Blo 1403521 10667213 := bstep (se 3 (by rfl) ⟨2000102, by rfl⟩ : syracuseStep 10667213 = 4000205) B4000205
theorem B2999539 : Blo 1403521 2999539 := bstep (se 1 (by rfl) ⟨2249654, by rfl⟩ : syracuseStep 2999539 = 4499309) B4499309
theorem B5334275 : Blo 1403521 5334275 := bstep (se 1 (by rfl) ⟨4000706, by rfl⟩ : syracuseStep 5334275 = 8001413) B8001413
theorem B2106635 : Blo 1403521 2106635 := bstep (se 1 (by rfl) ⟨1579976, by rfl⟩ : syracuseStep 2106635 = 3159953) B3159953
theorem B2106647 : Blo 1403521 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B8545601 : Blo 1403521 8545601 := bstep (se 2 (by rfl) ⟨3204600, by rfl⟩ : syracuseStep 8545601 = 6409201) B6409201
theorem B2106713 : Blo 1403521 2106713 := bstep (se 2 (by rfl) ⟨790017, by rfl⟩ : syracuseStep 2106713 = 1580035) B1580035
theorem B7996765 : Blo 1403521 7996765 := bstep (se 3 (by rfl) ⟨1499393, by rfl⟩ : syracuseStep 7996765 = 2998787) B2998787
theorem B6751619 : Blo 1403521 6751619 := bstep (se 1 (by rfl) ⟨5063714, by rfl⟩ : syracuseStep 6751619 = 10127429) B10127429
theorem B3794327 : Blo 1403521 3794327 := bstep (se 1 (by rfl) ⟨2845745, by rfl⟩ : syracuseStep 3794327 = 5691491) B5691491
theorem B2368919 : Blo 1403521 2368919 := bstep (se 1 (by rfl) ⟨1776689, by rfl⟩ : syracuseStep 2368919 = 3553379) B3553379
theorem B2106827 : Blo 1403521 2106827 := bstep (se 1 (by rfl) ⟨1580120, by rfl⟩ : syracuseStep 2106827 = 3160241) B3160241
theorem B3556811 : Blo 1403521 3556811 := bstep (se 1 (by rfl) ⟨2667608, by rfl⟩ : syracuseStep 3556811 = 5335217) B5335217
theorem B2106839 : Blo 1403521 2106839 := bstep (se 1 (by rfl) ⟨1580129, by rfl⟩ : syracuseStep 2106839 = 3160259) B3160259
theorem B2369047 : Blo 1403521 2369047 := bstep (se 1 (by rfl) ⟨1776785, by rfl⟩ : syracuseStep 2369047 = 3553571) B3553571
theorem B2106905 : Blo 1403521 2106905 := bstep (se 2 (by rfl) ⟨790089, by rfl⟩ : syracuseStep 2106905 = 1580179) B1580179
theorem B7112285 : Blo 1403521 7112285 := bstep (se 3 (by rfl) ⟨1333553, by rfl⟩ : syracuseStep 7112285 = 2667107) B2667107
theorem B2107019 : Blo 1403521 2107019 := bstep (se 1 (by rfl) ⟨1580264, by rfl⟩ : syracuseStep 2107019 = 3160529) B3160529
theorem B2107031 : Blo 1403521 2107031 := bstep (se 1 (by rfl) ⟨1580273, by rfl⟩ : syracuseStep 2107031 = 3160547) B3160547
theorem B10667699 : Blo 1403521 10667699 := bstep (se 1 (by rfl) ⟨8000774, by rfl⟩ : syracuseStep 10667699 = 16001549) B16001549
theorem B5334731 : Blo 1403521 5334731 := bstep (se 1 (by rfl) ⟨4001048, by rfl⟩ : syracuseStep 5334731 = 8002097) B8002097
theorem B2107097 : Blo 1403521 2107097 := bstep (se 2 (by rfl) ⟨790161, by rfl⟩ : syracuseStep 2107097 = 1580323) B1580323
theorem B2107211 : Blo 1403521 2107211 := bstep (se 1 (by rfl) ⟨1580408, by rfl⟩ : syracuseStep 2107211 = 3160817) B3160817
theorem B2107223 : Blo 1403521 2107223 := bstep (se 1 (by rfl) ⟨1580417, by rfl⟩ : syracuseStep 2107223 = 3160835) B3160835
theorem B5334929 : Blo 1403521 5334929 := bstep (se 2 (by rfl) ⟨2000598, by rfl⟩ : syracuseStep 5334929 = 4001197) B4001197
theorem B3000215 : Blo 1403521 3000215 := bstep (se 1 (by rfl) ⟨2250161, by rfl⟩ : syracuseStep 3000215 = 4500323) B4500323
theorem B2107289 : Blo 1403521 2107289 := bstep (se 2 (by rfl) ⟨790233, by rfl⟩ : syracuseStep 2107289 = 1580467) B1580467
theorem B3000257 : Blo 1403521 3000257 := bstep (se 2 (by rfl) ⟨1125096, by rfl⟩ : syracuseStep 3000257 = 2250193) B2250193
theorem B2107403 : Blo 1403521 2107403 := bstep (se 1 (by rfl) ⟨1580552, by rfl⟩ : syracuseStep 2107403 = 3161105) B3161105
theorem B2107415 : Blo 1403521 2107415 := bstep (se 1 (by rfl) ⟨1580561, by rfl⟩ : syracuseStep 2107415 = 3161123) B3161123
theorem B11397185 : Blo 1403521 11397185 := bstep (se 2 (by rfl) ⟨4273944, by rfl⟩ : syracuseStep 11397185 = 8547889) B8547889
theorem B2107481 : Blo 1403521 2107481 := bstep (se 2 (by rfl) ⟨790305, by rfl⟩ : syracuseStep 2107481 = 1580611) B1580611
theorem B2369675 : Blo 1403521 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B4737203 : Blo 1403521 4737203 := bstep (se 1 (by rfl) ⟨3552902, by rfl⟩ : syracuseStep 4737203 = 7105805) B7105805
theorem B2107595 : Blo 1403521 2107595 := bstep (se 1 (by rfl) ⟨1580696, by rfl⟩ : syracuseStep 2107595 = 3161393) B3161393
theorem B2107607 : Blo 1403521 2107607 := bstep (se 1 (by rfl) ⟨1580705, by rfl⟩ : syracuseStep 2107607 = 3161411) B3161411
theorem B2369803 : Blo 1403521 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B2107673 : Blo 1403521 2107673 := bstep (se 2 (by rfl) ⟨790377, by rfl⟩ : syracuseStep 2107673 = 1580755) B1580755
theorem B5409089 : Blo 1403521 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B2107787 : Blo 1403521 2107787 := bstep (se 1 (by rfl) ⟨1580840, by rfl⟩ : syracuseStep 2107787 = 3161681) B3161681
theorem B2165143 : Blo 1403521 2165143 := bstep (se 1 (by rfl) ⟨1623857, by rfl⟩ : syracuseStep 2165143 = 3247715) B3247715
theorem B2107799 : Blo 1403521 2107799 := bstep (se 1 (by rfl) ⟨1580849, by rfl⟩ : syracuseStep 2107799 = 3161699) B3161699
theorem B2369945 : Blo 1403521 2369945 := bstep (se 2 (by rfl) ⟨888729, by rfl⟩ : syracuseStep 2369945 = 1777459) B1777459
theorem B16222643 : Blo 1403521 16222643 := bstep (se 1 (by rfl) ⟨12166982, by rfl⟩ : syracuseStep 16222643 = 24333965) B24333965
theorem B4737473 : Blo 1403521 4737473 := bstep (se 2 (by rfl) ⟨1776552, by rfl⟩ : syracuseStep 4737473 = 3553105) B3553105
theorem B2107865 : Blo 1403521 2107865 := bstep (se 2 (by rfl) ⟨790449, by rfl⟩ : syracuseStep 2107865 = 1580899) B1580899
theorem B2370073 : Blo 1403521 2370073 := bstep (se 2 (by rfl) ⟨888777, by rfl⟩ : syracuseStep 2370073 = 1777555) B1777555
theorem B10119755 : Blo 1403521 10119755 := bstep (se 1 (by rfl) ⟨7589816, by rfl⟩ : syracuseStep 10119755 = 15179633) B15179633
theorem B2107979 : Blo 1403521 2107979 := bstep (se 1 (by rfl) ⟨1580984, by rfl⟩ : syracuseStep 2107979 = 3161969) B3161969
theorem B2107991 : Blo 1403521 2107991 := bstep (se 1 (by rfl) ⟨1580993, by rfl⟩ : syracuseStep 2107991 = 3161987) B3161987
theorem B3041921 : Blo 1403521 3041921 := bstep (se 2 (by rfl) ⟨1140720, by rfl⟩ : syracuseStep 3041921 = 2281441) B2281441
theorem B1403531 : Blo 1403521 1403531 := bstep (se 1 (by rfl) ⟨1052648, by rfl⟩ : syracuseStep 1403531 = 2105297) B2105297
theorem B1403543 : Blo 1403521 1403543 := bstep (se 1 (by rfl) ⟨1052657, by rfl⟩ : syracuseStep 1403543 = 2105315) B2105315
theorem B5335703 : Blo 1403521 5335703 := bstep (se 1 (by rfl) ⟨4001777, by rfl⟩ : syracuseStep 5335703 = 8003555) B8003555
theorem B2108057 : Blo 1403521 2108057 := bstep (se 2 (by rfl) ⟨790521, by rfl⟩ : syracuseStep 2108057 = 1581043) B1581043
theorem B1403563 : Blo 1403521 1403563 := bstep (se 1 (by rfl) ⟨1052672, by rfl⟩ : syracuseStep 1403563 = 2105345) B2105345
theorem B1403575 : Blo 1403521 1403575 := bstep (se 1 (by rfl) ⟨1052681, by rfl⟩ : syracuseStep 1403575 = 2105363) B2105363
theorem B1403595 : Blo 1403521 1403595 := bstep (se 1 (by rfl) ⟨1052696, by rfl⟩ : syracuseStep 1403595 = 2105393) B2105393
theorem B2665163 : Blo 1403521 2665163 := bstep (se 1 (by rfl) ⟨1998872, by rfl⟩ : syracuseStep 2665163 = 3997745) B3997745
theorem B1403607 : Blo 1403521 1403607 := bstep (se 1 (by rfl) ⟨1052705, by rfl⟩ : syracuseStep 1403607 = 2105411) B2105411
theorem B1403627 : Blo 1403521 1403627 := bstep (se 1 (by rfl) ⟨1052720, by rfl⟩ : syracuseStep 1403627 = 2105441) B2105441
theorem B1403639 : Blo 1403521 1403639 := bstep (se 1 (by rfl) ⟨1052729, by rfl⟩ : syracuseStep 1403639 = 2105459) B2105459
theorem B2665217 : Blo 1403521 2665217 := bstep (se 2 (by rfl) ⟨999456, by rfl⟩ : syracuseStep 2665217 = 1998913) B1998913
theorem B1403659 : Blo 1403521 1403659 := bstep (se 1 (by rfl) ⟨1052744, by rfl⟩ : syracuseStep 1403659 = 2105489) B2105489
theorem B2108171 : Blo 1403521 2108171 := bstep (se 1 (by rfl) ⟨1581128, by rfl⟩ : syracuseStep 2108171 = 3162257) B3162257
theorem B1403671 : Blo 1403521 1403671 := bstep (se 1 (by rfl) ⟨1052753, by rfl⟩ : syracuseStep 1403671 = 2105507) B2105507
theorem B2108183 : Blo 1403521 2108183 := bstep (se 1 (by rfl) ⟨1581137, by rfl⟩ : syracuseStep 2108183 = 3162275) B3162275
theorem B1403691 : Blo 1403521 1403691 := bstep (se 1 (by rfl) ⟨1052768, by rfl⟩ : syracuseStep 1403691 = 2105537) B2105537
theorem B1403703 : Blo 1403521 1403703 := bstep (se 1 (by rfl) ⟨1052777, by rfl⟩ : syracuseStep 1403703 = 2105555) B2105555
theorem B1403723 : Blo 1403521 1403723 := bstep (se 1 (by rfl) ⟨1052792, by rfl⟩ : syracuseStep 1403723 = 2105585) B2105585
theorem B1403735 : Blo 1403521 1403735 := bstep (se 1 (by rfl) ⟨1052801, by rfl⟩ : syracuseStep 1403735 = 2105603) B2105603
theorem B2108249 : Blo 1403521 2108249 := bstep (se 2 (by rfl) ⟨790593, by rfl⟩ : syracuseStep 2108249 = 1581187) B1581187
theorem B5335901 : Blo 1403521 5335901 := bstep (se 3 (by rfl) ⟨1000481, by rfl⟩ : syracuseStep 5335901 = 2000963) B2000963
theorem B1403755 : Blo 1403521 1403755 := bstep (se 1 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 1403755 = 2105633) B2105633
theorem B1403767 : Blo 1403521 1403767 := bstep (se 1 (by rfl) ⟨1052825, by rfl⟩ : syracuseStep 1403767 = 2105651) B2105651
theorem B1403787 : Blo 1403521 1403787 := bstep (se 1 (by rfl) ⟨1052840, by rfl⟩ : syracuseStep 1403787 = 2105681) B2105681
theorem B1403799 : Blo 1403521 1403799 := bstep (se 1 (by rfl) ⟨1052849, by rfl⟩ : syracuseStep 1403799 = 2105699) B2105699
theorem B1403819 : Blo 1403521 1403819 := bstep (se 1 (by rfl) ⟨1052864, by rfl⟩ : syracuseStep 1403819 = 2105729) B2105729
theorem B1403831 : Blo 1403521 1403831 := bstep (se 1 (by rfl) ⟨1052873, by rfl⟩ : syracuseStep 1403831 = 2105747) B2105747
theorem B1403851 : Blo 1403521 1403851 := bstep (se 1 (by rfl) ⟨1052888, by rfl⟩ : syracuseStep 1403851 = 2105777) B2105777
theorem B2845655 : Blo 1403521 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B1403863 : Blo 1403521 1403863 := bstep (se 1 (by rfl) ⟨1052897, by rfl⟩ : syracuseStep 1403863 = 2105795) B2105795
theorem B4738013 : Blo 1403521 4738013 := bstep (se 3 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 4738013 = 1776755) B1776755
theorem B1403883 : Blo 1403521 1403883 := bstep (se 1 (by rfl) ⟨1052912, by rfl⟩ : syracuseStep 1403883 = 2105825) B2105825
theorem B1403895 : Blo 1403521 1403895 := bstep (se 1 (by rfl) ⟨1052921, by rfl⟩ : syracuseStep 1403895 = 2105843) B2105843
theorem B1403915 : Blo 1403521 1403915 := bstep (se 1 (by rfl) ⟨1052936, by rfl⟩ : syracuseStep 1403915 = 2105873) B2105873
theorem B1403927 : Blo 1403521 1403927 := bstep (se 1 (by rfl) ⟨1052945, by rfl⟩ : syracuseStep 1403927 = 2105891) B2105891
theorem B1403947 : Blo 1403521 1403947 := bstep (se 1 (by rfl) ⟨1052960, by rfl⟩ : syracuseStep 1403947 = 2105921) B2105921
theorem B1403959 : Blo 1403521 1403959 := bstep (se 1 (by rfl) ⟨1052969, by rfl⟩ : syracuseStep 1403959 = 2105939) B2105939
theorem B1403979 : Blo 1403521 1403979 := bstep (se 1 (by rfl) ⟨1052984, by rfl⟩ : syracuseStep 1403979 = 2105969) B2105969
theorem B4000843 : Blo 1403521 4000843 := bstep (se 1 (by rfl) ⟨3000632, by rfl⟩ : syracuseStep 4000843 = 6001265) B6001265
theorem B1403991 : Blo 1403521 1403991 := bstep (se 1 (by rfl) ⟨1052993, by rfl⟩ : syracuseStep 1403991 = 2105987) B2105987
theorem B2370647 : Blo 1403521 2370647 := bstep (se 1 (by rfl) ⟨1777985, by rfl⟩ : syracuseStep 2370647 = 3555971) B3555971
theorem B10669157 : Blo 1403521 10669157 := bstep (se 4 (by rfl) ⟨1000233, by rfl⟩ : syracuseStep 10669157 = 2000467) B2000467
theorem B1404011 : Blo 1403521 1404011 := bstep (se 1 (by rfl) ⟨1053008, by rfl⟩ : syracuseStep 1404011 = 2106017) B2106017
theorem B1404023 : Blo 1403521 1404023 := bstep (se 1 (by rfl) ⟨1053017, by rfl⟩ : syracuseStep 1404023 = 2106035) B2106035
theorem B1404043 : Blo 1403521 1404043 := bstep (se 1 (by rfl) ⟨1053032, by rfl⟩ : syracuseStep 1404043 = 2106065) B2106065
theorem B5999761 : Blo 1403521 5999761 := bstep (se 2 (by rfl) ⟨2249910, by rfl⟩ : syracuseStep 5999761 = 4499821) B4499821
theorem B1404055 : Blo 1403521 1404055 := bstep (se 1 (by rfl) ⟨1053041, by rfl⟩ : syracuseStep 1404055 = 2106083) B2106083
theorem B1404075 : Blo 1403521 1404075 := bstep (se 1 (by rfl) ⟨1053056, by rfl⟩ : syracuseStep 1404075 = 2106113) B2106113
theorem B1404087 : Blo 1403521 1404087 := bstep (se 1 (by rfl) ⟨1053065, by rfl⟩ : syracuseStep 1404087 = 2106131) B2106131
theorem B1404107 : Blo 1403521 1404107 := bstep (se 1 (by rfl) ⟨1053080, by rfl⟩ : syracuseStep 1404107 = 2106161) B2106161
theorem B1404119 : Blo 1403521 1404119 := bstep (se 1 (by rfl) ⟨1053089, by rfl⟩ : syracuseStep 1404119 = 2106179) B2106179
theorem B2026711 : Blo 1403521 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B2370775 : Blo 1403521 2370775 := bstep (se 1 (by rfl) ⟨1778081, by rfl⟩ : syracuseStep 2370775 = 3556163) B3556163
theorem B1404139 : Blo 1403521 1404139 := bstep (se 1 (by rfl) ⟨1053104, by rfl⟩ : syracuseStep 1404139 = 2106209) B2106209
theorem B1404151 : Blo 1403521 1404151 := bstep (se 1 (by rfl) ⟨1053113, by rfl⟩ : syracuseStep 1404151 = 2106227) B2106227
theorem B1404171 : Blo 1403521 1404171 := bstep (se 1 (by rfl) ⟨1053128, by rfl⟩ : syracuseStep 1404171 = 2106257) B2106257
theorem B1404183 : Blo 1403521 1404183 := bstep (se 1 (by rfl) ⟨1053137, by rfl⟩ : syracuseStep 1404183 = 2106275) B2106275
theorem B1404203 : Blo 1403521 1404203 := bstep (se 1 (by rfl) ⟨1053152, by rfl⟩ : syracuseStep 1404203 = 2106305) B2106305
theorem B1404215 : Blo 1403521 1404215 := bstep (se 1 (by rfl) ⟨1053161, by rfl⟩ : syracuseStep 1404215 = 2106323) B2106323
theorem B1404235 : Blo 1403521 1404235 := bstep (se 1 (by rfl) ⟨1053176, by rfl⟩ : syracuseStep 1404235 = 2106353) B2106353
theorem B1404247 : Blo 1403521 1404247 := bstep (se 1 (by rfl) ⟨1053185, by rfl⟩ : syracuseStep 1404247 = 2106371) B2106371
theorem B1404267 : Blo 1403521 1404267 := bstep (se 1 (by rfl) ⟨1053200, by rfl⟩ : syracuseStep 1404267 = 2106401) B2106401
theorem B1404279 : Blo 1403521 1404279 := bstep (se 1 (by rfl) ⟨1053209, by rfl⟩ : syracuseStep 1404279 = 2106419) B2106419
theorem B1404299 : Blo 1403521 1404299 := bstep (se 1 (by rfl) ⟨1053224, by rfl⟩ : syracuseStep 1404299 = 2106449) B2106449
theorem B2887051 : Blo 1403521 2887051 := bstep (se 1 (by rfl) ⟨2165288, by rfl⟩ : syracuseStep 2887051 = 4330577) B4330577
theorem B1404311 : Blo 1403521 1404311 := bstep (se 1 (by rfl) ⟨1053233, by rfl⟩ : syracuseStep 1404311 = 2106467) B2106467
theorem B1404331 : Blo 1403521 1404331 := bstep (se 1 (by rfl) ⟨1053248, by rfl⟩ : syracuseStep 1404331 = 2106497) B2106497
theorem B1404343 : Blo 1403521 1404343 := bstep (se 1 (by rfl) ⟨1053257, by rfl⟩ : syracuseStep 1404343 = 2106515) B2106515
theorem B1404363 : Blo 1403521 1404363 := bstep (se 1 (by rfl) ⟨1053272, by rfl⟩ : syracuseStep 1404363 = 2106545) B2106545
theorem B1404375 : Blo 1403521 1404375 := bstep (se 1 (by rfl) ⟨1053281, by rfl⟩ : syracuseStep 1404375 = 2106563) B2106563
theorem B1404395 : Blo 1403521 1404395 := bstep (se 1 (by rfl) ⟨1053296, by rfl⟩ : syracuseStep 1404395 = 2106593) B2106593
theorem B1404407 : Blo 1403521 1404407 := bstep (se 1 (by rfl) ⟨1053305, by rfl⟩ : syracuseStep 1404407 = 2106611) B2106611
theorem B10661381 : Blo 1403521 10661381 := bstep (se 4 (by rfl) ⟨999504, by rfl⟩ : syracuseStep 10661381 = 1999009) B1999009
theorem B1404427 : Blo 1403521 1404427 := bstep (se 1 (by rfl) ⟨1053320, by rfl⟩ : syracuseStep 1404427 = 2106641) B2106641
theorem B1404439 : Blo 1403521 1404439 := bstep (se 1 (by rfl) ⟨1053329, by rfl⟩ : syracuseStep 1404439 = 2106659) B2106659
theorem B1404459 : Blo 1403521 1404459 := bstep (se 1 (by rfl) ⟨1053344, by rfl⟩ : syracuseStep 1404459 = 2106689) B2106689
theorem B1404471 : Blo 1403521 1404471 := bstep (se 1 (by rfl) ⟨1053353, by rfl⟩ : syracuseStep 1404471 = 2106707) B2106707
theorem B4001345 : Blo 1403521 4001345 := bstep (se 2 (by rfl) ⟨1500504, by rfl⟩ : syracuseStep 4001345 = 3001009) B3001009
theorem B1404491 : Blo 1403521 1404491 := bstep (se 1 (by rfl) ⟨1053368, by rfl⟩ : syracuseStep 1404491 = 2106737) B2106737
theorem B10669643 : Blo 1403521 10669643 := bstep (se 1 (by rfl) ⟨8002232, by rfl⟩ : syracuseStep 10669643 = 16004465) B16004465
theorem B1404503 : Blo 1403521 1404503 := bstep (se 1 (by rfl) ⟨1053377, by rfl⟩ : syracuseStep 1404503 = 2106755) B2106755
theorem B2403929 : Blo 1403521 2403929 := bstep (se 2 (by rfl) ⟨901473, by rfl⟩ : syracuseStep 2403929 = 1802947) B1802947
theorem B1404523 : Blo 1403521 1404523 := bstep (se 1 (by rfl) ⟨1053392, by rfl⟩ : syracuseStep 1404523 = 2106785) B2106785
theorem B1404535 : Blo 1403521 1404535 := bstep (se 1 (by rfl) ⟨1053401, by rfl⟩ : syracuseStep 1404535 = 2106803) B2106803
theorem B1404555 : Blo 1403521 1404555 := bstep (se 1 (by rfl) ⟨1053416, by rfl⟩ : syracuseStep 1404555 = 2106833) B2106833
theorem B4804247 : Blo 1403521 4804247 := bstep (se 1 (by rfl) ⟨3603185, by rfl⟩ : syracuseStep 4804247 = 7206371) B7206371
theorem B2666135 : Blo 1403521 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B1404567 : Blo 1403521 1404567 := bstep (se 1 (by rfl) ⟨1053425, by rfl⟩ : syracuseStep 1404567 = 2106851) B2106851
theorem B7114391 : Blo 1403521 7114391 := bstep (se 1 (by rfl) ⟨5335793, by rfl⟩ : syracuseStep 7114391 = 10671587) B10671587
theorem B1404587 : Blo 1403521 1404587 := bstep (se 1 (by rfl) ⟨1053440, by rfl⟩ : syracuseStep 1404587 = 2106881) B2106881
theorem B1404599 : Blo 1403521 1404599 := bstep (se 1 (by rfl) ⟨1053449, by rfl⟩ : syracuseStep 1404599 = 2106899) B2106899
theorem B1404619 : Blo 1403521 1404619 := bstep (se 1 (by rfl) ⟨1053464, by rfl⟩ : syracuseStep 1404619 = 2106929) B2106929
theorem B1404631 : Blo 1403521 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B1404651 : Blo 1403521 1404651 := bstep (se 1 (by rfl) ⟨1053488, by rfl⟩ : syracuseStep 1404651 = 2106977) B2106977
theorem B1404663 : Blo 1403521 1404663 := bstep (se 1 (by rfl) ⟨1053497, by rfl⟩ : syracuseStep 1404663 = 2106995) B2106995
theorem B1404683 : Blo 1403521 1404683 := bstep (se 1 (by rfl) ⟨1053512, by rfl⟩ : syracuseStep 1404683 = 2107025) B2107025
theorem B1404695 : Blo 1403521 1404695 := bstep (se 1 (by rfl) ⟨1053521, by rfl⟩ : syracuseStep 1404695 = 2107043) B2107043
theorem B1404715 : Blo 1403521 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B1404727 : Blo 1403521 1404727 := bstep (se 1 (by rfl) ⟨1053545, by rfl⟩ : syracuseStep 1404727 = 2107091) B2107091
theorem B8998721 : Blo 1403521 8998721 := bstep (se 2 (by rfl) ⟨3374520, by rfl⟩ : syracuseStep 8998721 = 6749041) B6749041
theorem B1404747 : Blo 1403521 1404747 := bstep (se 1 (by rfl) ⟨1053560, by rfl⟩ : syracuseStep 1404747 = 2107121) B2107121
theorem B2371403 : Blo 1403521 2371403 := bstep (se 1 (by rfl) ⟨1778552, by rfl⟩ : syracuseStep 2371403 = 3557105) B3557105
theorem B1404759 : Blo 1403521 1404759 := bstep (se 1 (by rfl) ⟨1053569, by rfl⟩ : syracuseStep 1404759 = 2107139) B2107139
theorem B1404779 : Blo 1403521 1404779 := bstep (se 1 (by rfl) ⟨1053584, by rfl⟩ : syracuseStep 1404779 = 2107169) B2107169
theorem B1404791 : Blo 1403521 1404791 := bstep (se 1 (by rfl) ⟨1053593, by rfl⟩ : syracuseStep 1404791 = 2107187) B2107187
theorem B1404811 : Blo 1403521 1404811 := bstep (se 1 (by rfl) ⟨1053608, by rfl⟩ : syracuseStep 1404811 = 2107217) B2107217
theorem B1404823 : Blo 1403521 1404823 := bstep (se 1 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 1404823 = 2107235) B2107235
theorem B4001687 : Blo 1403521 4001687 := bstep (se 1 (by rfl) ⟨3001265, by rfl⟩ : syracuseStep 4001687 = 6002531) B6002531
theorem B1404843 : Blo 1403521 1404843 := bstep (se 1 (by rfl) ⟨1053632, by rfl⟩ : syracuseStep 1404843 = 2107265) B2107265
theorem B1404855 : Blo 1403521 1404855 := bstep (se 1 (by rfl) ⟨1053641, by rfl⟩ : syracuseStep 1404855 = 2107283) B2107283
theorem B1404875 : Blo 1403521 1404875 := bstep (se 1 (by rfl) ⟨1053656, by rfl⟩ : syracuseStep 1404875 = 2107313) B2107313
theorem B2371531 : Blo 1403521 2371531 := bstep (se 1 (by rfl) ⟨1778648, by rfl⟩ : syracuseStep 2371531 = 3557297) B3557297
theorem B1404887 : Blo 1403521 1404887 := bstep (se 1 (by rfl) ⟨1053665, by rfl⟩ : syracuseStep 1404887 = 2107331) B2107331
theorem B34156505 : Blo 1403521 34156505 := bstep (se 2 (by rfl) ⟨12808689, by rfl⟩ : syracuseStep 34156505 = 25617379) B25617379
theorem B1404907 : Blo 1403521 1404907 := bstep (se 1 (by rfl) ⟨1053680, by rfl⟩ : syracuseStep 1404907 = 2107361) B2107361
theorem B1404919 : Blo 1403521 1404919 := bstep (se 1 (by rfl) ⟨1053689, by rfl⟩ : syracuseStep 1404919 = 2107379) B2107379
theorem B5697539 : Blo 1403521 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B3158027 : Blo 1403521 3158027 := bstep (se 1 (by rfl) ⟨2368520, by rfl⟩ : syracuseStep 3158027 = 4737041) B4737041
theorem B1404939 : Blo 1403521 1404939 := bstep (se 1 (by rfl) ⟨1053704, by rfl⟩ : syracuseStep 1404939 = 2107409) B2107409
theorem B1404951 : Blo 1403521 1404951 := bstep (se 1 (by rfl) ⟨1053713, by rfl⟩ : syracuseStep 1404951 = 2107427) B2107427
theorem B1404971 : Blo 1403521 1404971 := bstep (se 1 (by rfl) ⟨1053728, by rfl⟩ : syracuseStep 1404971 = 2107457) B2107457
theorem B1404983 : Blo 1403521 1404983 := bstep (se 1 (by rfl) ⟨1053737, by rfl⟩ : syracuseStep 1404983 = 2107475) B2107475
theorem B3158081 : Blo 1403521 3158081 := bstep (se 2 (by rfl) ⟨1184280, by rfl⟩ : syracuseStep 3158081 = 2368561) B2368561
theorem B76845125 : Blo 1403521 76845125 := bstep (se 4 (by rfl) ⟨7204230, by rfl⟩ : syracuseStep 76845125 = 14408461) B14408461
theorem B4739147 : Blo 1403521 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B1405003 : Blo 1403521 1405003 := bstep (se 1 (by rfl) ⟨1053752, by rfl⟩ : syracuseStep 1405003 = 2107505) B2107505
theorem B1405015 : Blo 1403521 1405015 := bstep (se 1 (by rfl) ⟨1053761, by rfl⟩ : syracuseStep 1405015 = 2107523) B2107523
theorem B2371673 : Blo 1403521 2371673 := bstep (se 2 (by rfl) ⟨889377, by rfl⟩ : syracuseStep 2371673 = 1778755) B1778755
theorem B1405035 : Blo 1403521 1405035 := bstep (se 1 (by rfl) ⟨1053776, by rfl⟩ : syracuseStep 1405035 = 2107553) B2107553
theorem B1405047 : Blo 1403521 1405047 := bstep (se 1 (by rfl) ⟨1053785, by rfl⟩ : syracuseStep 1405047 = 2107571) B2107571
theorem B1405067 : Blo 1403521 1405067 := bstep (se 1 (by rfl) ⟨1053800, by rfl⟩ : syracuseStep 1405067 = 2107601) B2107601
theorem B11997335 : Blo 1403521 11997335 := bstep (se 1 (by rfl) ⟨8998001, by rfl⟩ : syracuseStep 11997335 = 17996003) B17996003
theorem B1405079 : Blo 1403521 1405079 := bstep (se 1 (by rfl) ⟨1053809, by rfl⟩ : syracuseStep 1405079 = 2107619) B2107619
theorem B1405099 : Blo 1403521 1405099 := bstep (se 1 (by rfl) ⟨1053824, by rfl⟩ : syracuseStep 1405099 = 2107649) B2107649
theorem B2666675 : Blo 1403521 2666675 := bstep (se 1 (by rfl) ⟨2000006, by rfl⟩ : syracuseStep 2666675 = 4000013) B4000013
theorem B1405111 : Blo 1403521 1405111 := bstep (se 1 (by rfl) ⟨1053833, by rfl⟩ : syracuseStep 1405111 = 2107667) B2107667
theorem B1405131 : Blo 1403521 1405131 := bstep (se 1 (by rfl) ⟨1053848, by rfl⟩ : syracuseStep 1405131 = 2107697) B2107697
theorem B1405143 : Blo 1403521 1405143 := bstep (se 1 (by rfl) ⟨1053857, by rfl⟩ : syracuseStep 1405143 = 2107715) B2107715
theorem B7106777 : Blo 1403521 7106777 := bstep (se 2 (by rfl) ⟨2665041, by rfl⟩ : syracuseStep 7106777 = 5330083) B5330083
theorem B2371801 : Blo 1403521 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B1405163 : Blo 1403521 1405163 := bstep (se 1 (by rfl) ⟨1053872, by rfl⟩ : syracuseStep 1405163 = 2107745) B2107745
theorem B1405175 : Blo 1403521 1405175 := bstep (se 1 (by rfl) ⟨1053881, by rfl⟩ : syracuseStep 1405175 = 2107763) B2107763
theorem B1405195 : Blo 1403521 1405195 := bstep (se 1 (by rfl) ⟨1053896, by rfl⟩ : syracuseStep 1405195 = 2107793) B2107793
theorem B5058839 : Blo 1403521 5058839 := bstep (se 1 (by rfl) ⟨3794129, by rfl⟩ : syracuseStep 5058839 = 7588259) B7588259
theorem B1405207 : Blo 1403521 1405207 := bstep (se 1 (by rfl) ⟨1053905, by rfl⟩ : syracuseStep 1405207 = 2107811) B2107811
theorem B3158297 : Blo 1403521 3158297 := bstep (se 2 (by rfl) ⟨1184361, by rfl⟩ : syracuseStep 3158297 = 2368723) B2368723
theorem B1405227 : Blo 1403521 1405227 := bstep (se 1 (by rfl) ⟨1053920, by rfl⟩ : syracuseStep 1405227 = 2107841) B2107841
theorem B1405239 : Blo 1403521 1405239 := bstep (se 1 (by rfl) ⟨1053929, by rfl⟩ : syracuseStep 1405239 = 2107859) B2107859
theorem B1405259 : Blo 1403521 1405259 := bstep (se 1 (by rfl) ⟨1053944, by rfl⟩ : syracuseStep 1405259 = 2107889) B2107889
theorem B1405271 : Blo 1403521 1405271 := bstep (se 1 (by rfl) ⟨1053953, by rfl⟩ : syracuseStep 1405271 = 2107907) B2107907
theorem B4739417 : Blo 1403521 4739417 := bstep (se 2 (by rfl) ⟨1777281, by rfl⟩ : syracuseStep 4739417 = 3554563) B3554563
theorem B10121573 : Blo 1403521 10121573 := bstep (se 4 (by rfl) ⟨948897, by rfl⟩ : syracuseStep 10121573 = 1897795) B1897795
theorem B1405291 : Blo 1403521 1405291 := bstep (se 1 (by rfl) ⟨1053968, by rfl⟩ : syracuseStep 1405291 = 2107937) B2107937
theorem B3158387 : Blo 1403521 3158387 := bstep (se 1 (by rfl) ⟨2368790, by rfl⟩ : syracuseStep 3158387 = 4737581) B4737581
theorem B1405303 : Blo 1403521 1405303 := bstep (se 1 (by rfl) ⟨1053977, by rfl⟩ : syracuseStep 1405303 = 2107955) B2107955
theorem B1405323 : Blo 1403521 1405323 := bstep (se 1 (by rfl) ⟨1053992, by rfl⟩ : syracuseStep 1405323 = 2107985) B2107985
theorem B3158423 : Blo 1403521 3158423 := bstep (se 1 (by rfl) ⟨2368817, by rfl⟩ : syracuseStep 3158423 = 4737635) B4737635
theorem B1405335 : Blo 1403521 1405335 := bstep (se 1 (by rfl) ⟨1054001, by rfl⟩ : syracuseStep 1405335 = 2108003) B2108003
theorem B1405355 : Blo 1403521 1405355 := bstep (se 1 (by rfl) ⟨1054016, by rfl⟩ : syracuseStep 1405355 = 2108033) B2108033
theorem B1405367 : Blo 1403521 1405367 := bstep (se 1 (by rfl) ⟨1054025, by rfl⟩ : syracuseStep 1405367 = 2108051) B2108051
theorem B1405387 : Blo 1403521 1405387 := bstep (se 1 (by rfl) ⟨1054040, by rfl⟩ : syracuseStep 1405387 = 2108081) B2108081
theorem B1405399 : Blo 1403521 1405399 := bstep (se 1 (by rfl) ⟨1054049, by rfl⟩ : syracuseStep 1405399 = 2108099) B2108099
theorem B1405419 : Blo 1403521 1405419 := bstep (se 1 (by rfl) ⟨1054064, by rfl⟩ : syracuseStep 1405419 = 2108129) B2108129
theorem B1405431 : Blo 1403521 1405431 := bstep (se 1 (by rfl) ⟨1054073, by rfl⟩ : syracuseStep 1405431 = 2108147) B2108147
theorem B1405451 : Blo 1403521 1405451 := bstep (se 1 (by rfl) ⟨1054088, by rfl⟩ : syracuseStep 1405451 = 2108177) B2108177
theorem B1405463 : Blo 1403521 1405463 := bstep (se 1 (by rfl) ⟨1054097, by rfl⟩ : syracuseStep 1405463 = 2108195) B2108195
theorem B1405483 : Blo 1403521 1405483 := bstep (se 1 (by rfl) ⟨1054112, by rfl⟩ : syracuseStep 1405483 = 2108225) B2108225
theorem B1405495 : Blo 1403521 1405495 := bstep (se 1 (by rfl) ⟨1054121, by rfl⟩ : syracuseStep 1405495 = 2108243) B2108243
theorem B3158603 : Blo 1403521 3158603 := bstep (se 1 (by rfl) ⟨2368952, by rfl⟩ : syracuseStep 3158603 = 4737905) B4737905
theorem B1405515 : Blo 1403521 1405515 := bstep (se 1 (by rfl) ⟨1054136, by rfl⟩ : syracuseStep 1405515 = 2108273) B2108273
theorem B4559449 : Blo 1403521 4559449 := bstep (se 2 (by rfl) ⟨1709793, by rfl⟩ : syracuseStep 4559449 = 3419587) B3419587
theorem B3158657 : Blo 1403521 3158657 := bstep (se 2 (by rfl) ⟨1184496, by rfl⟩ : syracuseStep 3158657 = 2368993) B2368993
theorem B2847383 : Blo 1403521 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B2667161 : Blo 1403521 2667161 := bstep (se 2 (by rfl) ⟨1000185, by rfl⟩ : syracuseStep 2667161 = 2000371) B2000371
theorem B3158873 : Blo 1403521 3158873 := bstep (se 2 (by rfl) ⟨1184577, by rfl⟩ : syracuseStep 3158873 = 2369155) B2369155
theorem B2847577 : Blo 1403521 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B2847641 : Blo 1403521 2847641 := bstep (se 2 (by rfl) ⟨1067865, by rfl⟩ : syracuseStep 2847641 = 2135731) B2135731
theorem B3158963 : Blo 1403521 3158963 := bstep (se 1 (by rfl) ⟨2369222, by rfl⟩ : syracuseStep 3158963 = 4738445) B4738445
theorem B5059531 : Blo 1403521 5059531 := bstep (se 1 (by rfl) ⟨3794648, by rfl⟩ : syracuseStep 5059531 = 7589297) B7589297
theorem B1520587 : Blo 1403521 1520587 := bstep (se 1 (by rfl) ⟨1140440, by rfl⟩ : syracuseStep 1520587 = 2280881) B2280881
theorem B3158999 : Blo 1403521 3158999 := bstep (se 1 (by rfl) ⟨2369249, by rfl⟩ : syracuseStep 3158999 = 4738499) B4738499
theorem B12170245 : Blo 1403521 12170245 := bstep (se 4 (by rfl) ⟨1140960, by rfl⟩ : syracuseStep 12170245 = 2281921) B2281921
theorem B4740119 : Blo 1403521 4740119 := bstep (se 1 (by rfl) ⟨3555089, by rfl⟩ : syracuseStep 4740119 = 7110179) B7110179
theorem B23991389 : Blo 1403521 23991389 := bstep (se 3 (by rfl) ⟨4498385, by rfl⟩ : syracuseStep 23991389 = 8996771) B8996771
theorem B6583427 : Blo 1403521 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B3159179 : Blo 1403521 3159179 := bstep (se 1 (by rfl) ⟨2369384, by rfl⟩ : syracuseStep 3159179 = 4738769) B4738769
theorem B32453783 : Blo 1403521 32453783 := bstep (se 1 (by rfl) ⟨24340337, by rfl⟩ : syracuseStep 32453783 = 48680675) B48680675
theorem B61600949 : Blo 1403521 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B3159233 : Blo 1403521 3159233 := bstep (se 2 (by rfl) ⟨1184712, by rfl⟩ : syracuseStep 3159233 = 2369425) B2369425
theorem B3847475 : Blo 1403521 3847475 := bstep (se 1 (by rfl) ⟨2885606, by rfl⟩ : syracuseStep 3847475 = 5771213) B5771213
theorem B3159449 : Blo 1403521 3159449 := bstep (se 2 (by rfl) ⟨1184793, by rfl⟩ : syracuseStep 3159449 = 2369587) B2369587
theorem B3159539 : Blo 1403521 3159539 := bstep (se 1 (by rfl) ⟨2369654, by rfl⟩ : syracuseStep 3159539 = 4739309) B4739309
theorem B3159575 : Blo 1403521 3159575 := bstep (se 1 (by rfl) ⟨2369681, by rfl⟩ : syracuseStep 3159575 = 4739363) B4739363
theorem B4740659 : Blo 1403521 4740659 := bstep (se 1 (by rfl) ⟨3555494, by rfl⟩ : syracuseStep 4740659 = 7110989) B7110989
theorem B97310321 : Blo 1403521 97310321 := bstep (se 2 (by rfl) ⟨36491370, by rfl⟩ : syracuseStep 97310321 = 72982741) B72982741
theorem B3847873 : Blo 1403521 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B3159755 : Blo 1403521 3159755 := bstep (se 1 (by rfl) ⟨2369816, by rfl⟩ : syracuseStep 3159755 = 4739633) B4739633
theorem B3159809 : Blo 1403521 3159809 := bstep (se 2 (by rfl) ⟨1184928, by rfl⟩ : syracuseStep 3159809 = 2369857) B2369857
theorem B5060369 : Blo 1403521 5060369 := bstep (se 2 (by rfl) ⟨1897638, by rfl⟩ : syracuseStep 5060369 = 3795277) B3795277
theorem B7108397 : Blo 1403521 7108397 := bstep (se 3 (by rfl) ⟨1332824, by rfl⟩ : syracuseStep 7108397 = 2665649) B2665649
theorem B4740929 : Blo 1403521 4740929 := bstep (se 2 (by rfl) ⟨1777848, by rfl⟩ : syracuseStep 4740929 = 3555697) B3555697
theorem B4331357 : Blo 1403521 4331357 := bstep (se 3 (by rfl) ⟨812129, by rfl⟩ : syracuseStep 4331357 = 1624259) B1624259
theorem B25966453 : Blo 1403521 25966453 := bstep (se 5 (by rfl) ⟨1217177, by rfl⟩ : syracuseStep 25966453 = 2434355) B2434355
theorem B10663811 : Blo 1403521 10663811 := bstep (se 1 (by rfl) ⟨7997858, by rfl⟩ : syracuseStep 10663811 = 15995717) B15995717
theorem B3553217 : Blo 1403521 3553217 := bstep (se 2 (by rfl) ⟨1332456, by rfl⟩ : syracuseStep 3553217 = 2664913) B2664913
theorem B10123213 : Blo 1403521 10123213 := bstep (se 3 (by rfl) ⟨1898102, by rfl⟩ : syracuseStep 10123213 = 3796205) B3796205
theorem B3160025 : Blo 1403521 3160025 := bstep (se 2 (by rfl) ⟨1185009, by rfl⟩ : syracuseStep 3160025 = 2370019) B2370019
theorem B11999249 : Blo 1403521 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B3160115 : Blo 1403521 3160115 := bstep (se 1 (by rfl) ⟨2370086, by rfl⟩ : syracuseStep 3160115 = 4740173) B4740173
theorem B1579063 : Blo 1403521 1579063 := bstep (se 1 (by rfl) ⟨1184297, by rfl⟩ : syracuseStep 1579063 = 2368595) B2368595
theorem B3160151 : Blo 1403521 3160151 := bstep (se 1 (by rfl) ⟨2370113, by rfl⟩ : syracuseStep 3160151 = 4740227) B4740227
theorem B24008885 : Blo 1403521 24008885 := bstep (se 5 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 24008885 = 2250833) B2250833
theorem B6002905 : Blo 1403521 6002905 := bstep (se 2 (by rfl) ⟨2251089, by rfl⟩ : syracuseStep 6002905 = 4502179) B4502179
theorem B1579243 : Blo 1403521 1579243 := bstep (se 1 (by rfl) ⟨1184432, by rfl⟩ : syracuseStep 1579243 = 2368865) B2368865
theorem B3160331 : Blo 1403521 3160331 := bstep (se 1 (by rfl) ⟨2370248, by rfl⟩ : syracuseStep 3160331 = 4740497) B4740497
theorem B5691713 : Blo 1403521 5691713 := bstep (se 2 (by rfl) ⟨2134392, by rfl⟩ : syracuseStep 5691713 = 4268785) B4268785
theorem B3160385 : Blo 1403521 3160385 := bstep (se 2 (by rfl) ⟨1185144, by rfl⟩ : syracuseStep 3160385 = 2370289) B2370289
theorem B2529623 : Blo 1403521 2529623 := bstep (se 1 (by rfl) ⟨1897217, by rfl⟩ : syracuseStep 2529623 = 3794435) B3794435
theorem B1579351 : Blo 1403521 1579351 := bstep (se 1 (by rfl) ⟨1184513, by rfl⟩ : syracuseStep 1579351 = 2369027) B2369027
theorem B4741469 : Blo 1403521 4741469 := bstep (se 3 (by rfl) ⟨889025, by rfl⟩ : syracuseStep 4741469 = 1778051) B1778051
theorem B3553753 : Blo 1403521 3553753 := bstep (se 2 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 3553753 = 2665315) B2665315
theorem B1579531 : Blo 1403521 1579531 := bstep (se 1 (by rfl) ⟨1184648, by rfl⟩ : syracuseStep 1579531 = 2369297) B2369297
theorem B3160601 : Blo 1403521 3160601 := bstep (se 2 (by rfl) ⟨1185225, by rfl⟩ : syracuseStep 3160601 = 2370451) B2370451
theorem B2251289 : Blo 1403521 2251289 := bstep (se 2 (by rfl) ⟨844233, by rfl⟩ : syracuseStep 2251289 = 1688467) B1688467
theorem B3160691 : Blo 1403521 3160691 := bstep (se 1 (by rfl) ⟨2370518, by rfl⟩ : syracuseStep 3160691 = 4741037) B4741037
theorem B1579639 : Blo 1403521 1579639 := bstep (se 1 (by rfl) ⟨1184729, by rfl⟩ : syracuseStep 1579639 = 2369459) B2369459
theorem B3160727 : Blo 1403521 3160727 := bstep (se 1 (by rfl) ⟨2370545, by rfl⟩ : syracuseStep 3160727 = 4741091) B4741091
theorem B10255025 : Blo 1403521 10255025 := bstep (se 2 (by rfl) ⟨3845634, by rfl⟩ : syracuseStep 10255025 = 7691269) B7691269
theorem B3422899 : Blo 1403521 3422899 := bstep (se 1 (by rfl) ⟨2567174, by rfl⟩ : syracuseStep 3422899 = 5134349) B5134349
theorem B47422157 : Blo 1403521 47422157 := bstep (se 3 (by rfl) ⟨8891654, by rfl⟩ : syracuseStep 47422157 = 17783309) B17783309
theorem B7306001 : Blo 1403521 7306001 := bstep (se 2 (by rfl) ⟨2739750, by rfl⟩ : syracuseStep 7306001 = 5479501) B5479501
theorem B1579819 : Blo 1403521 1579819 := bstep (se 1 (by rfl) ⟨1184864, by rfl⟩ : syracuseStep 1579819 = 2369729) B2369729
theorem B6404915 : Blo 1403521 6404915 := bstep (se 1 (by rfl) ⟨4803686, by rfl⟩ : syracuseStep 6404915 = 9607373) B9607373
theorem B6003521 : Blo 1403521 6003521 := bstep (se 2 (by rfl) ⟨2251320, by rfl⟩ : syracuseStep 6003521 = 4502641) B4502641
theorem B3160907 : Blo 1403521 3160907 := bstep (se 1 (by rfl) ⟨2370680, by rfl⟩ : syracuseStep 3160907 = 4741361) B4741361
theorem B2530163 : Blo 1403521 2530163 := bstep (se 1 (by rfl) ⟨1897622, by rfl⟩ : syracuseStep 2530163 = 3795245) B3795245
theorem B3160961 : Blo 1403521 3160961 := bstep (se 2 (by rfl) ⟨1185360, by rfl⟩ : syracuseStep 3160961 = 2370721) B2370721
theorem B1579927 : Blo 1403521 1579927 := bstep (se 1 (by rfl) ⟨1184945, by rfl⟩ : syracuseStep 1579927 = 2369891) B2369891
theorem B5995457 : Blo 1403521 5995457 := bstep (se 2 (by rfl) ⟨2248296, by rfl⟩ : syracuseStep 5995457 = 4496593) B4496593
theorem B11394065 : Blo 1403521 11394065 := bstep (se 2 (by rfl) ⟨4272774, by rfl⟩ : syracuseStep 11394065 = 8545549) B8545549
theorem B10804259 : Blo 1403521 10804259 := bstep (se 1 (by rfl) ⟨8103194, by rfl⟩ : syracuseStep 10804259 = 16206389) B16206389
theorem B5332013 : Blo 1403521 5332013 := bstep (se 3 (by rfl) ⟨999752, by rfl⟩ : syracuseStep 5332013 = 1999505) B1999505
theorem B1580107 : Blo 1403521 1580107 := bstep (se 1 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 1580107 = 2370161) B2370161
theorem B3161177 : Blo 1403521 3161177 := bstep (se 2 (by rfl) ⟨1185441, by rfl⟩ : syracuseStep 3161177 = 2370883) B2370883
theorem B3996823 : Blo 1403521 3996823 := bstep (se 1 (by rfl) ⟨2997617, by rfl⟩ : syracuseStep 3996823 = 5995235) B5995235
theorem B3161267 : Blo 1403521 3161267 := bstep (se 1 (by rfl) ⟨2370950, by rfl⟩ : syracuseStep 3161267 = 4741901) B4741901
theorem B22764725 : Blo 1403521 22764725 := bstep (se 5 (by rfl) ⟨1067096, by rfl⟩ : syracuseStep 22764725 = 2134193) B2134193
theorem B1580215 : Blo 1403521 1580215 := bstep (se 1 (by rfl) ⟨1185161, by rfl⟩ : syracuseStep 1580215 = 2370323) B2370323
theorem B3161303 : Blo 1403521 3161303 := bstep (se 1 (by rfl) ⟨2370977, by rfl⟩ : syracuseStep 3161303 = 4741955) B4741955
theorem B1776907 : Blo 1403521 1776907 := bstep (se 1 (by rfl) ⟨1332680, by rfl⟩ : syracuseStep 1776907 = 2665361) B2665361
theorem B9002285 : Blo 1403521 9002285 := bstep (se 3 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 9002285 = 3375857) B3375857
theorem B9878885 : Blo 1403521 9878885 := bstep (se 4 (by rfl) ⟨926145, by rfl⟩ : syracuseStep 9878885 = 1852291) B1852291
theorem B1580395 : Blo 1403521 1580395 := bstep (se 1 (by rfl) ⟨1185296, by rfl⟩ : syracuseStep 1580395 = 2370593) B2370593
theorem B2997643 : Blo 1403521 2997643 := bstep (se 1 (by rfl) ⟨2248232, by rfl⟩ : syracuseStep 2997643 = 4496465) B4496465
theorem B3161483 : Blo 1403521 3161483 := bstep (se 1 (by rfl) ⟨2371112, by rfl⟩ : syracuseStep 3161483 = 4742225) B4742225
theorem B3161537 : Blo 1403521 3161537 := bstep (se 2 (by rfl) ⟨1185576, by rfl⟩ : syracuseStep 3161537 = 2371153) B2371153
theorem B4742603 : Blo 1403521 4742603 := bstep (se 1 (by rfl) ⟨3556952, by rfl⟩ : syracuseStep 4742603 = 7113905) B7113905
theorem B2530775 : Blo 1403521 2530775 := bstep (se 1 (by rfl) ⟨1898081, by rfl⟩ : syracuseStep 2530775 = 3796163) B3796163
theorem B1580503 : Blo 1403521 1580503 := bstep (se 1 (by rfl) ⟨1185377, by rfl⟩ : syracuseStep 1580503 = 2370755) B2370755
theorem B3554867 : Blo 1403521 3554867 := bstep (se 1 (by rfl) ⟨2666150, by rfl⟩ : syracuseStep 3554867 = 5332301) B5332301
theorem B23076427 : Blo 1403521 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B2997899 : Blo 1403521 2997899 := bstep (se 1 (by rfl) ⟨2248424, by rfl⟩ : syracuseStep 2997899 = 4496849) B4496849
theorem B1580683 : Blo 1403521 1580683 := bstep (se 1 (by rfl) ⟨1185512, by rfl⟩ : syracuseStep 1580683 = 2371025) B2371025
theorem B3161753 : Blo 1403521 3161753 := bstep (se 2 (by rfl) ⟨1185657, by rfl⟩ : syracuseStep 3161753 = 2371315) B2371315
theorem B12328625 : Blo 1403521 12328625 := bstep (se 2 (by rfl) ⟨4623234, by rfl⟩ : syracuseStep 12328625 = 9246469) B9246469
theorem B4742873 : Blo 1403521 4742873 := bstep (se 2 (by rfl) ⟨1778577, by rfl⟩ : syracuseStep 4742873 = 3557155) B3557155
theorem B3161843 : Blo 1403521 3161843 := bstep (se 1 (by rfl) ⟨2371382, by rfl⟩ : syracuseStep 3161843 = 4742765) B4742765
theorem B1580791 : Blo 1403521 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B3161879 : Blo 1403521 3161879 := bstep (se 1 (by rfl) ⟨2371409, by rfl⟩ : syracuseStep 3161879 = 4742819) B4742819
theorem B5062445 : Blo 1403521 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B5332787 : Blo 1403521 5332787 := bstep (se 1 (by rfl) ⟨3999590, by rfl⟩ : syracuseStep 5332787 = 7999181) B7999181
theorem B3555161 : Blo 1403521 3555161 := bstep (se 2 (by rfl) ⟨1333185, by rfl⟩ : syracuseStep 3555161 = 2666371) B2666371
theorem B1580971 : Blo 1403521 1580971 := bstep (se 1 (by rfl) ⟨1185728, by rfl⟩ : syracuseStep 1580971 = 2371457) B2371457
theorem B2105291 : Blo 1403521 2105291 := bstep (se 1 (by rfl) ⟨1578968, by rfl⟩ : syracuseStep 2105291 = 3157937) B3157937
theorem B3162059 : Blo 1403521 3162059 := bstep (se 1 (by rfl) ⟨2371544, by rfl⟩ : syracuseStep 3162059 = 4743089) B4743089
theorem B2105303 : Blo 1403521 2105303 := bstep (se 1 (by rfl) ⟨1578977, by rfl⟩ : syracuseStep 2105303 = 3157955) B3157955
theorem B1499095 : Blo 1403521 1499095 := bstep (se 1 (by rfl) ⟨1124321, by rfl⟩ : syracuseStep 1499095 = 2248643) B2248643
theorem B2105351 : Blo 1403521 2105351 := bstep (se 1 (by rfl) ⟨1579013, by rfl⟩ : syracuseStep 2105351 = 3158027) B3158027
theorem B4743197 : Blo 1403521 4743197 := bstep (se 3 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 4743197 = 1778699) B1778699
theorem B2105387 : Blo 1403521 2105387 := bstep (se 1 (by rfl) ⟨1579040, by rfl⟩ : syracuseStep 2105387 = 3158081) B3158081
theorem B30384173 : Blo 1403521 30384173 := bstep (se 3 (by rfl) ⟨5697032, by rfl⟩ : syracuseStep 30384173 = 11394065) B11394065
theorem B1581115 : Blo 1403521 1581115 := bstep (se 1 (by rfl) ⟨1185836, by rfl⟩ : syracuseStep 1581115 = 2371673) B2371673
theorem B2105417 : Blo 1403521 2105417 := bstep (se 2 (by rfl) ⟨789531, by rfl⟩ : syracuseStep 2105417 = 1579063) B1579063
theorem B1777783 : Blo 1403521 1777783 := bstep (se 1 (by rfl) ⟨1333337, by rfl⟩ : syracuseStep 1777783 = 2666675) B2666675
theorem B2105531 : Blo 1403521 2105531 := bstep (se 1 (by rfl) ⟨1579148, by rfl⟩ : syracuseStep 2105531 = 3158297) B3158297
theorem B2105591 : Blo 1403521 2105591 := bstep (se 1 (by rfl) ⟨1579193, by rfl⟩ : syracuseStep 2105591 = 3158387) B3158387
theorem B2105615 : Blo 1403521 2105615 := bstep (se 1 (by rfl) ⟨1579211, by rfl⟩ : syracuseStep 2105615 = 3158423) B3158423
theorem B3162383 : Blo 1403521 3162383 := bstep (se 1 (by rfl) ⟨2371787, by rfl⟩ : syracuseStep 3162383 = 4743575) B4743575
theorem B8003873 : Blo 1403521 8003873 := bstep (se 2 (by rfl) ⟨3001452, by rfl⟩ : syracuseStep 8003873 = 6002905) B6002905
theorem B3162401 : Blo 1403521 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B2105657 : Blo 1403521 2105657 := bstep (se 2 (by rfl) ⟨789621, by rfl⟩ : syracuseStep 2105657 = 1579243) B1579243
theorem B2105735 : Blo 1403521 2105735 := bstep (se 1 (by rfl) ⟨1579301, by rfl⟩ : syracuseStep 2105735 = 3158603) B3158603
theorem B3998099 : Blo 1403521 3998099 := bstep (se 1 (by rfl) ⟨2998574, by rfl⟩ : syracuseStep 3998099 = 5997149) B5997149
theorem B14418323 : Blo 1403521 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B2105771 : Blo 1403521 2105771 := bstep (se 1 (by rfl) ⟨1579328, by rfl⟩ : syracuseStep 2105771 = 3158657) B3158657
theorem B7995833 : Blo 1403521 7995833 := bstep (se 2 (by rfl) ⟨2998437, by rfl⟩ : syracuseStep 7995833 = 5996875) B5996875
theorem B1778107 : Blo 1403521 1778107 := bstep (se 1 (by rfl) ⟨1333580, by rfl⟩ : syracuseStep 1778107 = 2667161) B2667161
theorem B2105801 : Blo 1403521 2105801 := bstep (se 2 (by rfl) ⟨789675, by rfl⟩ : syracuseStep 2105801 = 1579351) B1579351
theorem B1999351 : Blo 1403521 1999351 := bstep (se 1 (by rfl) ⟨1499513, by rfl⟩ : syracuseStep 1999351 = 2999027) B2999027
theorem B3080719 : Blo 1403521 3080719 := bstep (se 1 (by rfl) ⟨2310539, by rfl⟩ : syracuseStep 3080719 = 4621079) B4621079
theorem B2105915 : Blo 1403521 2105915 := bstep (se 1 (by rfl) ⟨1579436, by rfl⟩ : syracuseStep 2105915 = 3158873) B3158873
theorem B3375703 : Blo 1403521 3375703 := bstep (se 1 (by rfl) ⟨2531777, by rfl⟩ : syracuseStep 3375703 = 5063555) B5063555
theorem B2105975 : Blo 1403521 2105975 := bstep (se 1 (by rfl) ⟨1579481, by rfl⟩ : syracuseStep 2105975 = 3158963) B3158963
theorem B3375751 : Blo 1403521 3375751 := bstep (se 1 (by rfl) ⟨2531813, by rfl⟩ : syracuseStep 3375751 = 5063627) B5063627
theorem B2105999 : Blo 1403521 2105999 := bstep (se 1 (by rfl) ⟨1579499, by rfl⟩ : syracuseStep 2105999 = 3158999) B3158999
theorem B2106041 : Blo 1403521 2106041 := bstep (se 2 (by rfl) ⟨789765, by rfl⟩ : syracuseStep 2106041 = 1579531) B1579531
theorem B2106119 : Blo 1403521 2106119 := bstep (se 1 (by rfl) ⟨1579589, by rfl⟩ : syracuseStep 2106119 = 3159179) B3159179
theorem B21635855 : Blo 1403521 21635855 := bstep (se 1 (by rfl) ⟨16226891, by rfl⟩ : syracuseStep 21635855 = 32453783) B32453783
theorem B6079265 : Blo 1403521 6079265 := bstep (se 2 (by rfl) ⟨2279724, by rfl⟩ : syracuseStep 6079265 = 4559449) B4559449
theorem B3998497 : Blo 1403521 3998497 := bstep (se 2 (by rfl) ⟨1499436, by rfl⟩ : syracuseStep 3998497 = 2998873) B2998873
theorem B41067299 : Blo 1403521 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B2106155 : Blo 1403521 2106155 := bstep (se 1 (by rfl) ⟨1579616, by rfl⟩ : syracuseStep 2106155 = 3159233) B3159233
theorem B7111475 : Blo 1403521 7111475 := bstep (se 1 (by rfl) ⟨5333606, by rfl⟩ : syracuseStep 7111475 = 10667213) B10667213
theorem B2106185 : Blo 1403521 2106185 := bstep (se 2 (by rfl) ⟨789819, by rfl⟩ : syracuseStep 2106185 = 1579639) B1579639
theorem B3556183 : Blo 1403521 3556183 := bstep (se 1 (by rfl) ⟨2667137, by rfl⟩ : syracuseStep 3556183 = 5334275) B5334275
theorem B2564983 : Blo 1403521 2564983 := bstep (se 1 (by rfl) ⟨1923737, by rfl⟩ : syracuseStep 2564983 = 3847475) B3847475
theorem B4563865 : Blo 1403521 4563865 := bstep (se 2 (by rfl) ⟨1711449, by rfl⟩ : syracuseStep 4563865 = 3422899) B3422899
theorem B2106299 : Blo 1403521 2106299 := bstep (se 1 (by rfl) ⟨1579724, by rfl⟩ : syracuseStep 2106299 = 3159449) B3159449
theorem B2106359 : Blo 1403521 2106359 := bstep (se 1 (by rfl) ⟨1579769, by rfl⟩ : syracuseStep 2106359 = 3159539) B3159539
theorem B2106383 : Blo 1403521 2106383 := bstep (se 1 (by rfl) ⟨1579787, by rfl⟩ : syracuseStep 2106383 = 3159575) B3159575
theorem B2106425 : Blo 1403521 2106425 := bstep (se 2 (by rfl) ⟨789909, by rfl⟩ : syracuseStep 2106425 = 1579819) B1579819
theorem B64873547 : Blo 1403521 64873547 := bstep (se 1 (by rfl) ⟨48655160, by rfl⟩ : syracuseStep 64873547 = 97310321) B97310321
theorem B7111799 : Blo 1403521 7111799 := bstep (se 1 (by rfl) ⟨5333849, by rfl⟩ : syracuseStep 7111799 = 10667699) B10667699
theorem B2106503 : Blo 1403521 2106503 := bstep (se 1 (by rfl) ⟨1579877, by rfl⟩ : syracuseStep 2106503 = 3159755) B3159755
theorem B3556487 : Blo 1403521 3556487 := bstep (se 1 (by rfl) ⟨2667365, by rfl⟩ : syracuseStep 3556487 = 5334731) B5334731
theorem B2106539 : Blo 1403521 2106539 := bstep (se 1 (by rfl) ⟨1579904, by rfl⟩ : syracuseStep 2106539 = 3159809) B3159809
theorem B2000057 : Blo 1403521 2000057 := bstep (se 2 (by rfl) ⟨750021, by rfl⟩ : syracuseStep 2000057 = 1500043) B1500043
theorem B2106569 : Blo 1403521 2106569 := bstep (se 2 (by rfl) ⟨789963, by rfl⟩ : syracuseStep 2106569 = 1579927) B1579927
theorem B3556619 : Blo 1403521 3556619 := bstep (se 1 (by rfl) ⟨2667464, by rfl⟩ : syracuseStep 3556619 = 5334929) B5334929
theorem B2000143 : Blo 1403521 2000143 := bstep (se 1 (by rfl) ⟨1500107, by rfl⟩ : syracuseStep 2000143 = 3000215) B3000215
theorem B2368811 : Blo 1403521 2368811 := bstep (se 1 (by rfl) ⟨1776608, by rfl⟩ : syracuseStep 2368811 = 3553217) B3553217
theorem B2000171 : Blo 1403521 2000171 := bstep (se 1 (by rfl) ⟨1500128, by rfl⟩ : syracuseStep 2000171 = 3000257) B3000257
theorem B2106683 : Blo 1403521 2106683 := bstep (se 1 (by rfl) ⟨1580012, by rfl⟩ : syracuseStep 2106683 = 3160025) B3160025
theorem B2106743 : Blo 1403521 2106743 := bstep (se 1 (by rfl) ⟨1580057, by rfl⟩ : syracuseStep 2106743 = 3160115) B3160115
theorem B2106767 : Blo 1403521 2106767 := bstep (se 1 (by rfl) ⟨1580075, by rfl⟩ : syracuseStep 2106767 = 3160151) B3160151
theorem B2106809 : Blo 1403521 2106809 := bstep (se 2 (by rfl) ⟨790053, by rfl⟩ : syracuseStep 2106809 = 1580107) B1580107
theorem B5334457 : Blo 1403521 5334457 := bstep (se 2 (by rfl) ⟨2000421, by rfl⟩ : syracuseStep 5334457 = 4000843) B4000843
theorem B2106887 : Blo 1403521 2106887 := bstep (se 1 (by rfl) ⟨1580165, by rfl⟩ : syracuseStep 2106887 = 3160331) B3160331
theorem B2106923 : Blo 1403521 2106923 := bstep (se 1 (by rfl) ⟨1580192, by rfl⟩ : syracuseStep 2106923 = 3160385) B3160385
theorem B3606059 : Blo 1403521 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B2106953 : Blo 1403521 2106953 := bstep (se 2 (by rfl) ⟨790107, by rfl⟩ : syracuseStep 2106953 = 1580215) B1580215
theorem B10815095 : Blo 1403521 10815095 := bstep (se 1 (by rfl) ⟨8111321, by rfl⟩ : syracuseStep 10815095 = 16222643) B16222643
theorem B3999385 : Blo 1403521 3999385 := bstep (se 2 (by rfl) ⟨1499769, by rfl⟩ : syracuseStep 3999385 = 2999539) B2999539
theorem B8111789 : Blo 1403521 8111789 := bstep (se 3 (by rfl) ⟨1520960, by rfl⟩ : syracuseStep 8111789 = 3041921) B3041921
theorem B2369209 : Blo 1403521 2369209 := bstep (se 2 (by rfl) ⟨888453, by rfl⟩ : syracuseStep 2369209 = 1776907) B1776907
theorem B2107067 : Blo 1403521 2107067 := bstep (se 1 (by rfl) ⟨1580300, by rfl⟩ : syracuseStep 2107067 = 3160601) B3160601
theorem B1500859 : Blo 1403521 1500859 := bstep (se 1 (by rfl) ⟨1125644, by rfl⟩ : syracuseStep 1500859 = 2251289) B2251289
theorem B2107127 : Blo 1403521 2107127 := bstep (se 1 (by rfl) ⟨1580345, by rfl⟩ : syracuseStep 2107127 = 3160691) B3160691
theorem B2107151 : Blo 1403521 2107151 := bstep (se 1 (by rfl) ⟨1580363, by rfl⟩ : syracuseStep 2107151 = 3160727) B3160727
theorem B3557135 : Blo 1403521 3557135 := bstep (se 1 (by rfl) ⟨2667851, by rfl⟩ : syracuseStep 3557135 = 5335703) B5335703
theorem B2107193 : Blo 1403521 2107193 := bstep (se 2 (by rfl) ⟨790197, by rfl⟩ : syracuseStep 2107193 = 1580395) B1580395
theorem B4269943 : Blo 1403521 4269943 := bstep (se 1 (by rfl) ⟨3202457, by rfl⟩ : syracuseStep 4269943 = 6404915) B6404915
theorem B2107271 : Blo 1403521 2107271 := bstep (se 1 (by rfl) ⟨1580453, by rfl⟩ : syracuseStep 2107271 = 3160907) B3160907
theorem B3557267 : Blo 1403521 3557267 := bstep (se 1 (by rfl) ⟨2667950, by rfl⟩ : syracuseStep 3557267 = 5335901) B5335901
theorem B2107307 : Blo 1403521 2107307 := bstep (se 1 (by rfl) ⟨1580480, by rfl⟩ : syracuseStep 2107307 = 3160961) B3160961
theorem B2107337 : Blo 1403521 2107337 := bstep (se 2 (by rfl) ⟨790251, by rfl⟩ : syracuseStep 2107337 = 1580503) B1580503
theorem B7202839 : Blo 1403521 7202839 := bstep (se 1 (by rfl) ⟨5402129, by rfl⟩ : syracuseStep 7202839 = 10804259) B10804259
theorem B3999773 : Blo 1403521 3999773 := bstep (se 3 (by rfl) ⟨749957, by rfl⟩ : syracuseStep 3999773 = 1499915) B1499915
theorem B2107451 : Blo 1403521 2107451 := bstep (se 1 (by rfl) ⟨1580588, by rfl⟩ : syracuseStep 2107451 = 3161177) B3161177
theorem B7112771 : Blo 1403521 7112771 := bstep (se 1 (by rfl) ⟨5334578, by rfl⟩ : syracuseStep 7112771 = 10669157) B10669157
theorem B2107511 : Blo 1403521 2107511 := bstep (se 1 (by rfl) ⟨1580633, by rfl⟩ : syracuseStep 2107511 = 3161267) B3161267
theorem B2107535 : Blo 1403521 2107535 := bstep (se 1 (by rfl) ⟨1580651, by rfl⟩ : syracuseStep 2107535 = 3161303) B3161303
theorem B2107577 : Blo 1403521 2107577 := bstep (se 2 (by rfl) ⟨790341, by rfl⟩ : syracuseStep 2107577 = 1580683) B1580683
theorem B5130497 : Blo 1403521 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B2107655 : Blo 1403521 2107655 := bstep (se 1 (by rfl) ⟨1580741, by rfl⟩ : syracuseStep 2107655 = 3161483) B3161483
theorem B2107691 : Blo 1403521 2107691 := bstep (se 1 (by rfl) ⟨1580768, by rfl⟩ : syracuseStep 2107691 = 3161537) B3161537
theorem B2107721 : Blo 1403521 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B2369911 : Blo 1403521 2369911 := bstep (se 1 (by rfl) ⟨1777433, by rfl⟩ : syracuseStep 2369911 = 3554867) B3554867
theorem B7113095 : Blo 1403521 7113095 := bstep (se 1 (by rfl) ⟨5334821, by rfl⟩ : syracuseStep 7113095 = 10669643) B10669643
theorem B2107835 : Blo 1403521 2107835 := bstep (se 1 (by rfl) ⟨1580876, by rfl⟩ : syracuseStep 2107835 = 3161753) B3161753
theorem B8219083 : Blo 1403521 8219083 := bstep (se 1 (by rfl) ⟨6164312, by rfl⟩ : syracuseStep 8219083 = 12328625) B12328625
theorem B34621937 : Blo 1403521 34621937 := bstep (se 2 (by rfl) ⟨12983226, by rfl⟩ : syracuseStep 34621937 = 25966453) B25966453
theorem B2107895 : Blo 1403521 2107895 := bstep (se 1 (by rfl) ⟨1580921, by rfl⟩ : syracuseStep 2107895 = 3161843) B3161843
theorem B2107919 : Blo 1403521 2107919 := bstep (se 1 (by rfl) ⟨1580939, by rfl⟩ : syracuseStep 2107919 = 3161879) B3161879
theorem B5999147 : Blo 1403521 5999147 := bstep (se 1 (by rfl) ⟨4499360, by rfl⟩ : syracuseStep 5999147 = 8998721) B8998721
theorem B2107961 : Blo 1403521 2107961 := bstep (se 2 (by rfl) ⟨790485, by rfl⟩ : syracuseStep 2107961 = 1580971) B1580971
theorem B2370107 : Blo 1403521 2370107 := bstep (se 1 (by rfl) ⟨1777580, by rfl⟩ : syracuseStep 2370107 = 3555161) B3555161
theorem B1403527 : Blo 1403521 1403527 := bstep (se 1 (by rfl) ⟨1052645, by rfl⟩ : syracuseStep 1403527 = 2105291) B2105291
theorem B2108039 : Blo 1403521 2108039 := bstep (se 1 (by rfl) ⟨1581029, by rfl⟩ : syracuseStep 2108039 = 3162059) B3162059
theorem B1403535 : Blo 1403521 1403535 := bstep (se 1 (by rfl) ⟨1052651, by rfl⟩ : syracuseStep 1403535 = 2105303) B2105303
theorem B2108075 : Blo 1403521 2108075 := bstep (se 1 (by rfl) ⟨1581056, by rfl⟩ : syracuseStep 2108075 = 3162113) B3162113
theorem B1403579 : Blo 1403521 1403579 := bstep (se 1 (by rfl) ⟨1052684, by rfl⟩ : syracuseStep 1403579 = 2105369) B2105369
theorem B2108105 : Blo 1403521 2108105 := bstep (se 2 (by rfl) ⟨790539, by rfl⟩ : syracuseStep 2108105 = 1581079) B1581079
theorem B1403655 : Blo 1403521 1403655 := bstep (se 1 (by rfl) ⟨1052741, by rfl⟩ : syracuseStep 1403655 = 2105483) B2105483
theorem B1403663 : Blo 1403521 1403663 := bstep (se 1 (by rfl) ⟨1052747, by rfl⟩ : syracuseStep 1403663 = 2105495) B2105495
theorem B7998223 : Blo 1403521 7998223 := bstep (se 1 (by rfl) ⟨5998667, by rfl⟩ : syracuseStep 7998223 = 11997335) B11997335
theorem B1403707 : Blo 1403521 1403707 := bstep (se 1 (by rfl) ⟨1052780, by rfl⟩ : syracuseStep 1403707 = 2105561) B2105561
theorem B4737851 : Blo 1403521 4737851 := bstep (se 1 (by rfl) ⟨3553388, by rfl⟩ : syracuseStep 4737851 = 7106777) B7106777
theorem B2108219 : Blo 1403521 2108219 := bstep (se 1 (by rfl) ⟨1581164, by rfl⟩ : syracuseStep 2108219 = 3162329) B3162329
theorem B2108279 : Blo 1403521 2108279 := bstep (se 1 (by rfl) ⟨1581209, by rfl⟩ : syracuseStep 2108279 = 3162419) B3162419
theorem B1403783 : Blo 1403521 1403783 := bstep (se 1 (by rfl) ⟨1052837, by rfl⟩ : syracuseStep 1403783 = 2105675) B2105675
theorem B1403791 : Blo 1403521 1403791 := bstep (se 1 (by rfl) ⟨1052843, by rfl⟩ : syracuseStep 1403791 = 2105687) B2105687
theorem B1403835 : Blo 1403521 1403835 := bstep (se 1 (by rfl) ⟨1052876, by rfl⟩ : syracuseStep 1403835 = 2105753) B2105753
theorem B2370505 : Blo 1403521 2370505 := bstep (se 2 (by rfl) ⟨888939, by rfl⟩ : syracuseStep 2370505 = 1777879) B1777879
theorem B1403911 : Blo 1403521 1403911 := bstep (se 1 (by rfl) ⟨1052933, by rfl⟩ : syracuseStep 1403911 = 2105867) B2105867
theorem B24308747 : Blo 1403521 24308747 := bstep (se 1 (by rfl) ⟨18231560, by rfl⟩ : syracuseStep 24308747 = 36463121) B36463121
theorem B1403919 : Blo 1403521 1403919 := bstep (se 1 (by rfl) ⟨1052939, by rfl⟩ : syracuseStep 1403919 = 2105879) B2105879
theorem B1403963 : Blo 1403521 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B1404039 : Blo 1403521 1404039 := bstep (se 1 (by rfl) ⟨1053029, by rfl⟩ : syracuseStep 1404039 = 2106059) B2106059
theorem B1404047 : Blo 1403521 1404047 := bstep (se 1 (by rfl) ⟨1053035, by rfl⟩ : syracuseStep 1404047 = 2106071) B2106071
theorem B2665619 : Blo 1403521 2665619 := bstep (se 1 (by rfl) ⟨1999214, by rfl⟩ : syracuseStep 2665619 = 3998429) B3998429
theorem B1404091 : Blo 1403521 1404091 := bstep (se 1 (by rfl) ⟨1053068, by rfl⟩ : syracuseStep 1404091 = 2106137) B2106137
theorem B2886857 : Blo 1403521 2886857 := bstep (se 2 (by rfl) ⟨1082571, by rfl⟩ : syracuseStep 2886857 = 2165143) B2165143
theorem B1404167 : Blo 1403521 1404167 := bstep (se 1 (by rfl) ⟨1053125, by rfl⟩ : syracuseStep 1404167 = 2106251) B2106251
theorem B1404175 : Blo 1403521 1404175 := bstep (se 1 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 1404175 = 2106263) B2106263
theorem B4738337 : Blo 1403521 4738337 := bstep (se 2 (by rfl) ⟨1776876, by rfl⟩ : syracuseStep 4738337 = 3553753) B3553753
theorem B1404219 : Blo 1403521 1404219 := bstep (se 1 (by rfl) ⟨1053164, by rfl⟩ : syracuseStep 1404219 = 2106329) B2106329
theorem B3796283 : Blo 1403521 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B2665847 : Blo 1403521 2665847 := bstep (se 1 (by rfl) ⟨1999385, by rfl⟩ : syracuseStep 2665847 = 3998771) B3998771
theorem B1404295 : Blo 1403521 1404295 := bstep (se 1 (by rfl) ⟨1053221, by rfl⟩ : syracuseStep 1404295 = 2106443) B2106443
theorem B1404303 : Blo 1403521 1404303 := bstep (se 1 (by rfl) ⟨1053227, by rfl⟩ : syracuseStep 1404303 = 2106455) B2106455
theorem B15994259 : Blo 1403521 15994259 := bstep (se 1 (by rfl) ⟨11995694, by rfl⟩ : syracuseStep 15994259 = 23991389) B23991389
theorem B30387635 : Blo 1403521 30387635 := bstep (se 1 (by rfl) ⟨22790726, by rfl⟩ : syracuseStep 30387635 = 45581453) B45581453
theorem B1404347 : Blo 1403521 1404347 := bstep (se 1 (by rfl) ⟨1053260, by rfl⟩ : syracuseStep 1404347 = 2106521) B2106521
theorem B1404423 : Blo 1403521 1404423 := bstep (se 1 (by rfl) ⟨1053317, by rfl⟩ : syracuseStep 1404423 = 2106635) B2106635
theorem B1404431 : Blo 1403521 1404431 := bstep (se 1 (by rfl) ⟨1053323, by rfl⟩ : syracuseStep 1404431 = 2106647) B2106647
theorem B5697067 : Blo 1403521 5697067 := bstep (se 1 (by rfl) ⟨4272800, by rfl⟩ : syracuseStep 5697067 = 8545601) B8545601
theorem B1404475 : Blo 1403521 1404475 := bstep (se 1 (by rfl) ⟨1053356, by rfl⟩ : syracuseStep 1404475 = 2106713) B2106713
theorem B4501079 : Blo 1403521 4501079 := bstep (se 1 (by rfl) ⟨3375809, by rfl⟩ : syracuseStep 4501079 = 6751619) B6751619
theorem B1404551 : Blo 1403521 1404551 := bstep (se 1 (by rfl) ⟨1053413, by rfl⟩ : syracuseStep 1404551 = 2106827) B2106827
theorem B2371207 : Blo 1403521 2371207 := bstep (se 1 (by rfl) ⟨1778405, by rfl⟩ : syracuseStep 2371207 = 3556811) B3556811
theorem B1404559 : Blo 1403521 1404559 := bstep (se 1 (by rfl) ⟨1053419, by rfl⟩ : syracuseStep 1404559 = 2106839) B2106839
theorem B1404603 : Blo 1403521 1404603 := bstep (se 1 (by rfl) ⟨1053452, by rfl⟩ : syracuseStep 1404603 = 2106905) B2106905
theorem B1404679 : Blo 1403521 1404679 := bstep (se 1 (by rfl) ⟨1053509, by rfl⟩ : syracuseStep 1404679 = 2107019) B2107019
theorem B1404687 : Blo 1403521 1404687 := bstep (se 1 (by rfl) ⟨1053515, by rfl⟩ : syracuseStep 1404687 = 2107031) B2107031
theorem B3796769 : Blo 1403521 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B1404731 : Blo 1403521 1404731 := bstep (se 1 (by rfl) ⟨1053548, by rfl⟩ : syracuseStep 1404731 = 2107097) B2107097
theorem B4738931 : Blo 1403521 4738931 := bstep (se 1 (by rfl) ⟨3554198, by rfl⟩ : syracuseStep 4738931 = 7108397) B7108397
theorem B1404807 : Blo 1403521 1404807 := bstep (se 1 (by rfl) ⟨1053605, by rfl⟩ : syracuseStep 1404807 = 2107211) B2107211
theorem B1404815 : Blo 1403521 1404815 := bstep (se 1 (by rfl) ⟨1053611, by rfl⟩ : syracuseStep 1404815 = 2107223) B2107223
theorem B2887571 : Blo 1403521 2887571 := bstep (se 1 (by rfl) ⟨2165678, by rfl⟩ : syracuseStep 2887571 = 4331357) B4331357
theorem B6746041 : Blo 1403521 6746041 := bstep (se 2 (by rfl) ⟨2529765, by rfl⟩ : syracuseStep 6746041 = 5059531) B5059531
theorem B2027449 : Blo 1403521 2027449 := bstep (se 2 (by rfl) ⟨760293, by rfl⟩ : syracuseStep 2027449 = 1520587) B1520587
theorem B1404859 : Blo 1403521 1404859 := bstep (se 1 (by rfl) ⟨1053644, by rfl⟩ : syracuseStep 1404859 = 2107289) B2107289
theorem B1404935 : Blo 1403521 1404935 := bstep (se 1 (by rfl) ⟨1053701, by rfl⟩ : syracuseStep 1404935 = 2107403) B2107403
theorem B7999499 : Blo 1403521 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B1404943 : Blo 1403521 1404943 := bstep (se 1 (by rfl) ⟨1053707, by rfl⟩ : syracuseStep 1404943 = 2107415) B2107415
theorem B7598123 : Blo 1403521 7598123 := bstep (se 1 (by rfl) ⟨5698592, by rfl⟩ : syracuseStep 7598123 = 11397185) B11397185
theorem B1404987 : Blo 1403521 1404987 := bstep (se 1 (by rfl) ⟨1053740, by rfl⟩ : syracuseStep 1404987 = 2107481) B2107481
theorem B4501565 : Blo 1403521 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B3158135 : Blo 1403521 3158135 := bstep (se 1 (by rfl) ⟨2368601, by rfl⟩ : syracuseStep 3158135 = 4737203) B4737203
theorem B1405063 : Blo 1403521 1405063 := bstep (se 1 (by rfl) ⟨1053797, by rfl⟩ : syracuseStep 1405063 = 2107595) B2107595
theorem B1405071 : Blo 1403521 1405071 := bstep (se 1 (by rfl) ⟨1053803, by rfl⟩ : syracuseStep 1405071 = 2107607) B2107607
theorem B1405115 : Blo 1403521 1405115 := bstep (se 1 (by rfl) ⟨1053836, by rfl⟩ : syracuseStep 1405115 = 2107673) B2107673
theorem B7999681 : Blo 1403521 7999681 := bstep (se 2 (by rfl) ⟨2999880, by rfl⟩ : syracuseStep 7999681 = 5999761) B5999761
theorem B5329097 : Blo 1403521 5329097 := bstep (se 2 (by rfl) ⟨1998411, by rfl⟩ : syracuseStep 5329097 = 3996823) B3996823
theorem B6410477 : Blo 1403521 6410477 := bstep (se 3 (by rfl) ⟨1201964, by rfl⟩ : syracuseStep 6410477 = 2403929) B2403929
theorem B1405191 : Blo 1403521 1405191 := bstep (se 1 (by rfl) ⟨1053893, by rfl⟩ : syracuseStep 1405191 = 2107787) B2107787
theorem B1405199 : Blo 1403521 1405199 := bstep (se 1 (by rfl) ⟨1053899, by rfl⟩ : syracuseStep 1405199 = 2107799) B2107799
theorem B3158315 : Blo 1403521 3158315 := bstep (se 1 (by rfl) ⟨2368736, by rfl⟩ : syracuseStep 3158315 = 4737473) B4737473
theorem B1405243 : Blo 1403521 1405243 := bstep (se 1 (by rfl) ⟨1053932, by rfl⟩ : syracuseStep 1405243 = 2107865) B2107865
theorem B6746503 : Blo 1403521 6746503 := bstep (se 1 (by rfl) ⟨5059877, by rfl⟩ : syracuseStep 6746503 = 10119755) B10119755
theorem B1405319 : Blo 1403521 1405319 := bstep (se 1 (by rfl) ⟨1053989, by rfl⟩ : syracuseStep 1405319 = 2107979) B2107979
theorem B1405327 : Blo 1403521 1405327 := bstep (se 1 (by rfl) ⟨1053995, by rfl⟩ : syracuseStep 1405327 = 2107991) B2107991
theorem B1405371 : Blo 1403521 1405371 := bstep (se 1 (by rfl) ⟨1054028, by rfl⟩ : syracuseStep 1405371 = 2108057) B2108057
theorem B6836683 : Blo 1403521 6836683 := bstep (se 1 (by rfl) ⟨5127512, by rfl⟩ : syracuseStep 6836683 = 10255025) B10255025
theorem B10662353 : Blo 1403521 10662353 := bstep (se 2 (by rfl) ⟨3998382, by rfl⟩ : syracuseStep 10662353 = 7996765) B7996765
theorem B1405447 : Blo 1403521 1405447 := bstep (se 1 (by rfl) ⟨1054085, by rfl⟩ : syracuseStep 1405447 = 2108171) B2108171
theorem B4870667 : Blo 1403521 4870667 := bstep (se 1 (by rfl) ⟨3653000, by rfl⟩ : syracuseStep 4870667 = 7306001) B7306001
theorem B1405455 : Blo 1403521 1405455 := bstep (se 1 (by rfl) ⟨1054091, by rfl⟩ : syracuseStep 1405455 = 2108183) B2108183
theorem B7107101 : Blo 1403521 7107101 := bstep (se 3 (by rfl) ⟨1332581, by rfl⟩ : syracuseStep 7107101 = 2665163) B2665163
theorem B4002347 : Blo 1403521 4002347 := bstep (se 1 (by rfl) ⟨3001760, by rfl⟩ : syracuseStep 4002347 = 6003521) B6003521
theorem B1405499 : Blo 1403521 1405499 := bstep (se 1 (by rfl) ⟨1054124, by rfl⟩ : syracuseStep 1405499 = 2108249) B2108249
theorem B1897103 : Blo 1403521 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B3158675 : Blo 1403521 3158675 := bstep (se 1 (by rfl) ⟨2369006, by rfl⟩ : syracuseStep 3158675 = 4738013) B4738013
theorem B3158729 : Blo 1403521 3158729 := bstep (se 2 (by rfl) ⟨1184523, by rfl⟩ : syracuseStep 3158729 = 2369047) B2369047
theorem B15176483 : Blo 1403521 15176483 := bstep (se 1 (by rfl) ⟨11382362, by rfl⟩ : syracuseStep 15176483 = 22764725) B22764725
theorem B6001523 : Blo 1403521 6001523 := bstep (se 1 (by rfl) ⟨4501142, by rfl⟩ : syracuseStep 6001523 = 9002285) B9002285
theorem B6747101 : Blo 1403521 6747101 := bstep (se 3 (by rfl) ⟨1265081, by rfl⟩ : syracuseStep 6747101 = 2530163) B2530163
theorem B7107587 : Blo 1403521 7107587 := bstep (se 1 (by rfl) ⟨5330690, by rfl⟩ : syracuseStep 7107587 = 10661381) B10661381
theorem B2667563 : Blo 1403521 2667563 := bstep (se 1 (by rfl) ⟨2000672, by rfl⟩ : syracuseStep 2667563 = 4001345) B4001345
theorem B2667791 : Blo 1403521 2667791 := bstep (se 1 (by rfl) ⟨2000843, by rfl⟩ : syracuseStep 2667791 = 4001687) B4001687
theorem B13497617 : Blo 1403521 13497617 := bstep (se 2 (by rfl) ⟨5061606, by rfl⟩ : syracuseStep 13497617 = 10123213) B10123213
theorem B22771003 : Blo 1403521 22771003 := bstep (se 1 (by rfl) ⟨17078252, by rfl⟩ : syracuseStep 22771003 = 34156505) B34156505
theorem B3798359 : Blo 1403521 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B51230083 : Blo 1403521 51230083 := bstep (se 1 (by rfl) ⟨38422562, by rfl⟩ : syracuseStep 51230083 = 76845125) B76845125
theorem B3159431 : Blo 1403521 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B26990009 : Blo 1403521 26990009 := bstep (se 2 (by rfl) ⟨10121253, by rfl⟩ : syracuseStep 26990009 = 20242507) B20242507
theorem B3372559 : Blo 1403521 3372559 := bstep (se 1 (by rfl) ⟨2529419, by rfl⟩ : syracuseStep 3372559 = 5058839) B5058839
theorem B2250283 : Blo 1403521 2250283 := bstep (se 1 (by rfl) ⟨1687712, by rfl⟩ : syracuseStep 2250283 = 3375425) B3375425
theorem B3159611 : Blo 1403521 3159611 := bstep (se 1 (by rfl) ⟨2369708, by rfl⟩ : syracuseStep 3159611 = 4739417) B4739417
theorem B6747715 : Blo 1403521 6747715 := bstep (se 1 (by rfl) ⟨5060786, by rfl⟩ : syracuseStep 6747715 = 10121573) B10121573
theorem B3159737 : Blo 1403521 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B1898255 : Blo 1403521 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B13490009 : Blo 1403521 13490009 := bstep (se 2 (by rfl) ⟨5058753, by rfl⟩ : syracuseStep 13490009 = 10117507) B10117507
theorem B5330873 : Blo 1403521 5330873 := bstep (se 2 (by rfl) ⟨1999077, by rfl⟩ : syracuseStep 5330873 = 3998155) B3998155
theorem B3160079 : Blo 1403521 3160079 := bstep (se 1 (by rfl) ⟨2370059, by rfl⟩ : syracuseStep 3160079 = 4740119) B4740119
theorem B3160097 : Blo 1403521 3160097 := bstep (se 2 (by rfl) ⟨1185036, by rfl⟩ : syracuseStep 3160097 = 2370073) B2370073
theorem B4388951 : Blo 1403521 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B15177901 : Blo 1403521 15177901 := bstep (se 3 (by rfl) ⟨2845856, by rfl⟩ : syracuseStep 15177901 = 5691713) B5691713
theorem B2529551 : Blo 1403521 2529551 := bstep (se 1 (by rfl) ⟨1897163, by rfl⟩ : syracuseStep 2529551 = 3794327) B3794327
theorem B1579279 : Blo 1403521 1579279 := bstep (se 1 (by rfl) ⟨1184459, by rfl⟩ : syracuseStep 1579279 = 2368919) B2368919
theorem B3160439 : Blo 1403521 3160439 := bstep (se 1 (by rfl) ⟨2370329, by rfl⟩ : syracuseStep 3160439 = 4740659) B4740659
theorem B4741523 : Blo 1403521 4741523 := bstep (se 1 (by rfl) ⟨3556142, by rfl⟩ : syracuseStep 4741523 = 7112285) B7112285
theorem B3373579 : Blo 1403521 3373579 := bstep (se 1 (by rfl) ⟨2530184, by rfl⟩ : syracuseStep 3373579 = 5060369) B5060369
theorem B3160619 : Blo 1403521 3160619 := bstep (se 1 (by rfl) ⟨2370464, by rfl⟩ : syracuseStep 3160619 = 4740929) B4740929
theorem B6748733 : Blo 1403521 6748733 := bstep (se 3 (by rfl) ⟨1265387, by rfl⟩ : syracuseStep 6748733 = 2530775) B2530775
theorem B7109207 : Blo 1403521 7109207 := bstep (se 1 (by rfl) ⟨5331905, by rfl⟩ : syracuseStep 7109207 = 10663811) B10663811
theorem B16226993 : Blo 1403521 16226993 := bstep (se 2 (by rfl) ⟨6085122, by rfl⟩ : syracuseStep 16226993 = 12170245) B12170245
theorem B1579783 : Blo 1403521 1579783 := bstep (se 1 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 1579783 = 2369675) B2369675
theorem B16005923 : Blo 1403521 16005923 := bstep (se 1 (by rfl) ⟨12004442, by rfl⟩ : syracuseStep 16005923 = 24008885) B24008885
theorem B1686415 : Blo 1403521 1686415 := bstep (se 1 (by rfl) ⟨1264811, by rfl⟩ : syracuseStep 1686415 = 2529623) B2529623
theorem B3160979 : Blo 1403521 3160979 := bstep (se 1 (by rfl) ⟨2370734, by rfl⟩ : syracuseStep 3160979 = 4741469) B4741469
theorem B1579963 : Blo 1403521 1579963 := bstep (se 1 (by rfl) ⟨1184972, by rfl⟩ : syracuseStep 1579963 = 2369945) B2369945
theorem B2702281 : Blo 1403521 2702281 := bstep (se 2 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 2702281 = 2026711) B2026711
theorem B3161033 : Blo 1403521 3161033 := bstep (se 2 (by rfl) ⟨1185387, by rfl⟩ : syracuseStep 3161033 = 2370775) B2370775
theorem B7109693 : Blo 1403521 7109693 := bstep (se 3 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 7109693 = 2666135) B2666135
theorem B1776811 : Blo 1403521 1776811 := bstep (se 1 (by rfl) ⟨1332608, by rfl⟩ : syracuseStep 1776811 = 2665217) B2665217
theorem B3996857 : Blo 1403521 3996857 := bstep (se 2 (by rfl) ⟨1498821, by rfl⟩ : syracuseStep 3996857 = 2997643) B2997643
theorem B3849401 : Blo 1403521 3849401 := bstep (se 2 (by rfl) ⟨1443525, by rfl⟩ : syracuseStep 3849401 = 2887051) B2887051
theorem B126459085 : Blo 1403521 126459085 := bstep (se 3 (by rfl) ⟨23711078, by rfl⟩ : syracuseStep 126459085 = 47422157) B47422157
theorem B3996971 : Blo 1403521 3996971 := bstep (se 1 (by rfl) ⟨2997728, by rfl⟩ : syracuseStep 3996971 = 5995457) B5995457
theorem B3554675 : Blo 1403521 3554675 := bstep (se 1 (by rfl) ⟨2666006, by rfl⟩ : syracuseStep 3554675 = 5332013) B5332013
theorem B1580431 : Blo 1403521 1580431 := bstep (se 1 (by rfl) ⟨1185323, by rfl⟩ : syracuseStep 1580431 = 2370647) B2370647
theorem B30768569 : Blo 1403521 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B6585923 : Blo 1403521 6585923 := bstep (se 1 (by rfl) ⟨4939442, by rfl⟩ : syracuseStep 6585923 = 9878885) B9878885
theorem B3161735 : Blo 1403521 3161735 := bstep (se 1 (by rfl) ⟨2371301, by rfl⟩ : syracuseStep 3161735 = 4742603) B4742603
theorem B7593709 : Blo 1403521 7593709 := bstep (se 3 (by rfl) ⟨1423820, by rfl⟩ : syracuseStep 7593709 = 2847641) B2847641
theorem B1998599 : Blo 1403521 1998599 := bstep (se 1 (by rfl) ⟨1498949, by rfl⟩ : syracuseStep 1998599 = 2997899) B2997899
theorem B3202831 : Blo 1403521 3202831 := bstep (se 1 (by rfl) ⟨2402123, by rfl⟩ : syracuseStep 3202831 = 4804247) B4804247
theorem B4742927 : Blo 1403521 4742927 := bstep (se 1 (by rfl) ⟨3557195, by rfl⟩ : syracuseStep 4742927 = 7114391) B7114391
theorem B3161915 : Blo 1403521 3161915 := bstep (se 1 (by rfl) ⟨2371436, by rfl⟩ : syracuseStep 3161915 = 4742873) B4742873
theorem B3374963 : Blo 1403521 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B3555191 : Blo 1403521 3555191 := bstep (se 1 (by rfl) ⟨2666393, by rfl⟩ : syracuseStep 3555191 = 5332787) B5332787
theorem B1580935 : Blo 1403521 1580935 := bstep (se 1 (by rfl) ⟨1185701, by rfl⟩ : syracuseStep 1580935 = 2371403) B2371403
theorem B3162041 : Blo 1403521 3162041 := bstep (se 2 (by rfl) ⟨1185765, by rfl⟩ : syracuseStep 3162041 = 2371531) B2371531
theorem B1998793 : Blo 1403521 1998793 := bstep (se 2 (by rfl) ⟨749547, by rfl⟩ : syracuseStep 1998793 = 1499095) B1499095
theorem B5332999 : Blo 1403521 5332999 := bstep (se 1 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 5332999 = 7999499) B7999499
theorem B3162131 : Blo 1403521 3162131 := bstep (se 1 (by rfl) ⟨2371598, by rfl⟩ : syracuseStep 3162131 = 4743197) B4743197
theorem B2105423 : Blo 1403521 2105423 := bstep (se 1 (by rfl) ⟨1579067, by rfl⟩ : syracuseStep 2105423 = 3158135) B3158135
theorem B2105543 : Blo 1403521 2105543 := bstep (se 1 (by rfl) ⟨1579157, by rfl⟩ : syracuseStep 2105543 = 3158315) B3158315
theorem B10666241 : Blo 1403521 10666241 := bstep (se 2 (by rfl) ⟨3999840, by rfl⟩ : syracuseStep 10666241 = 7999681) B7999681
theorem B2105705 : Blo 1403521 2105705 := bstep (se 2 (by rfl) ⟨789639, by rfl⟩ : syracuseStep 2105705 = 1579279) B1579279
theorem B2105783 : Blo 1403521 2105783 := bstep (se 1 (by rfl) ⟨1579337, by rfl⟩ : syracuseStep 2105783 = 3158675) B3158675
theorem B2105819 : Blo 1403521 2105819 := bstep (se 1 (by rfl) ⟨1579364, by rfl⟩ : syracuseStep 2105819 = 3158729) B3158729
theorem B5333485 : Blo 1403521 5333485 := bstep (se 3 (by rfl) ⟨1000028, by rfl⟩ : syracuseStep 5333485 = 2000057) B2000057
theorem B8995337 : Blo 1403521 8995337 := bstep (se 2 (by rfl) ⟨3373251, by rfl⟩ : syracuseStep 8995337 = 6746503) B6746503
theorem B10117655 : Blo 1403521 10117655 := bstep (se 1 (by rfl) ⟨7588241, by rfl⟩ : syracuseStep 10117655 = 15176483) B15176483
theorem B27378199 : Blo 1403521 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B4498067 : Blo 1403521 4498067 := bstep (se 1 (by rfl) ⟨3373550, by rfl⟩ : syracuseStep 4498067 = 6747101) B6747101
theorem B13681325 : Blo 1403521 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B4498105 : Blo 1403521 4498105 := bstep (se 2 (by rfl) ⟨1686789, by rfl⟩ : syracuseStep 4498105 = 3373579) B3373579
theorem B1778375 : Blo 1403521 1778375 := bstep (se 1 (by rfl) ⟨1333781, by rfl⟩ : syracuseStep 1778375 = 2667563) B2667563
theorem B5333789 : Blo 1403521 5333789 := bstep (se 3 (by rfl) ⟨1000085, by rfl⟩ : syracuseStep 5333789 = 2000171) B2000171
theorem B1778527 : Blo 1403521 1778527 := bstep (se 1 (by rfl) ⟨1333895, by rfl⟩ : syracuseStep 1778527 = 2667791) B2667791
theorem B2532239 : Blo 1403521 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B2106287 : Blo 1403521 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B8004581 : Blo 1403521 8004581 := bstep (se 4 (by rfl) ⟨750429, by rfl⟩ : syracuseStep 8004581 = 1500859) B1500859
theorem B2106377 : Blo 1403521 2106377 := bstep (se 2 (by rfl) ⟨789891, by rfl⟩ : syracuseStep 2106377 = 1579783) B1579783
theorem B2106407 : Blo 1403521 2106407 := bstep (se 1 (by rfl) ⟨1579805, by rfl⟩ : syracuseStep 2106407 = 3159611) B3159611
theorem B7210063 : Blo 1403521 7210063 := bstep (se 1 (by rfl) ⟨5407547, by rfl⟩ : syracuseStep 7210063 = 10815095) B10815095
theorem B5407859 : Blo 1403521 5407859 := bstep (se 1 (by rfl) ⟨4055894, by rfl⟩ : syracuseStep 5407859 = 8111789) B8111789
theorem B2106491 : Blo 1403521 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B2106617 : Blo 1403521 2106617 := bstep (se 2 (by rfl) ⟨789981, by rfl⟩ : syracuseStep 2106617 = 1579963) B1579963
theorem B2106719 : Blo 1403521 2106719 := bstep (se 1 (by rfl) ⟨1580039, by rfl⟩ : syracuseStep 2106719 = 3160079) B3160079
theorem B2106731 : Blo 1403521 2106731 := bstep (se 1 (by rfl) ⟨1580048, by rfl⟩ : syracuseStep 2106731 = 3160097) B3160097
theorem B2925967 : Blo 1403521 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B2369081 : Blo 1403521 2369081 := bstep (se 2 (by rfl) ⟨888405, by rfl⟩ : syracuseStep 2369081 = 1776811) B1776811
theorem B2106959 : Blo 1403521 2106959 := bstep (se 1 (by rfl) ⟨1580219, by rfl⟩ : syracuseStep 2106959 = 3160439) B3160439
theorem B3999431 : Blo 1403521 3999431 := bstep (se 1 (by rfl) ⟨2999573, by rfl⟩ : syracuseStep 3999431 = 5999147) B5999147
theorem B2107079 : Blo 1403521 2107079 := bstep (se 1 (by rfl) ⟨1580309, by rfl⟩ : syracuseStep 2107079 = 3160619) B3160619
theorem B4499155 : Blo 1403521 4499155 := bstep (se 1 (by rfl) ⟨3374366, by rfl⟩ : syracuseStep 4499155 = 6748733) B6748733
theorem B30361337 : Blo 1403521 30361337 := bstep (se 2 (by rfl) ⟨11385501, by rfl⟩ : syracuseStep 30361337 = 22771003) B22771003
theorem B68306777 : Blo 1403521 68306777 := bstep (se 2 (by rfl) ⟨25615041, by rfl⟩ : syracuseStep 68306777 = 51230083) B51230083
theorem B2107241 : Blo 1403521 2107241 := bstep (se 2 (by rfl) ⟨790215, by rfl⟩ : syracuseStep 2107241 = 1580431) B1580431
theorem B7112609 : Blo 1403521 7112609 := bstep (se 2 (by rfl) ⟨2667228, by rfl⟩ : syracuseStep 7112609 = 5334457) B5334457
theorem B2107319 : Blo 1403521 2107319 := bstep (se 1 (by rfl) ⟨1580489, by rfl⟩ : syracuseStep 2107319 = 3160979) B3160979
theorem B2107355 : Blo 1403521 2107355 := bstep (se 1 (by rfl) ⟨1580516, by rfl⟩ : syracuseStep 2107355 = 3161033) B3161033
theorem B16205831 : Blo 1403521 16205831 := bstep (se 1 (by rfl) ⟨12154373, by rfl⟩ : syracuseStep 16205831 = 24308747) B24308747
theorem B3000377 : Blo 1403521 3000377 := bstep (se 2 (by rfl) ⟨1125141, by rfl⟩ : syracuseStep 3000377 = 2250283) B2250283
theorem B7596089 : Blo 1403521 7596089 := bstep (se 2 (by rfl) ⟨2848533, by rfl⟩ : syracuseStep 7596089 = 5697067) B5697067
theorem B8996953 : Blo 1403521 8996953 := bstep (se 2 (by rfl) ⟨3373857, by rfl⟩ : syracuseStep 8996953 = 6747715) B6747715
theorem B2664571 : Blo 1403521 2664571 := bstep (se 1 (by rfl) ⟨1998428, by rfl⟩ : syracuseStep 2664571 = 3996857) B3996857
theorem B2566267 : Blo 1403521 2566267 := bstep (se 1 (by rfl) ⟨1924700, by rfl⟩ : syracuseStep 2566267 = 3849401) B3849401
theorem B2664647 : Blo 1403521 2664647 := bstep (se 1 (by rfl) ⟨1998485, by rfl⟩ : syracuseStep 2664647 = 3996971) B3996971
theorem B2369783 : Blo 1403521 2369783 := bstep (se 1 (by rfl) ⟨1777337, by rfl⟩ : syracuseStep 2369783 = 3554675) B3554675
theorem B4270441 : Blo 1403521 4270441 := bstep (se 2 (by rfl) ⟨1601415, by rfl⟩ : syracuseStep 4270441 = 3202831) B3202831
theorem B3000719 : Blo 1403521 3000719 := bstep (se 1 (by rfl) ⟨2250539, by rfl⟩ : syracuseStep 3000719 = 4501079) B4501079
theorem B2107823 : Blo 1403521 2107823 := bstep (se 1 (by rfl) ⟨1580867, by rfl⟩ : syracuseStep 2107823 = 3161735) B3161735
theorem B2107913 : Blo 1403521 2107913 := bstep (se 2 (by rfl) ⟨790467, by rfl⟩ : syracuseStep 2107913 = 1580935) B1580935
theorem B2107943 : Blo 1403521 2107943 := bstep (se 1 (by rfl) ⟨1580957, by rfl⟩ : syracuseStep 2107943 = 3161915) B3161915
theorem B2370127 : Blo 1403521 2370127 := bstep (se 1 (by rfl) ⟨1777595, by rfl⟩ : syracuseStep 2370127 = 3555191) B3555191
theorem B2665057 : Blo 1403521 2665057 := bstep (se 2 (by rfl) ⟨999396, by rfl⟩ : syracuseStep 2665057 = 1998793) B1998793
theorem B2108027 : Blo 1403521 2108027 := bstep (se 1 (by rfl) ⟨1581020, by rfl⟩ : syracuseStep 2108027 = 3162041) B3162041
theorem B1403567 : Blo 1403521 1403567 := bstep (se 1 (by rfl) ⟨1052675, by rfl⟩ : syracuseStep 1403567 = 2105351) B2105351
theorem B1403591 : Blo 1403521 1403591 := bstep (se 1 (by rfl) ⟨1052693, by rfl⟩ : syracuseStep 1403591 = 2105387) B2105387
theorem B5065415 : Blo 1403521 5065415 := bstep (se 1 (by rfl) ⟨3799061, by rfl⟩ : syracuseStep 5065415 = 7598123) B7598123
theorem B9603785 : Blo 1403521 9603785 := bstep (se 2 (by rfl) ⟨3601419, by rfl⟩ : syracuseStep 9603785 = 7202839) B7202839
theorem B3001043 : Blo 1403521 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B1403611 : Blo 1403521 1403611 := bstep (se 1 (by rfl) ⟨1052708, by rfl⟩ : syracuseStep 1403611 = 2105417) B2105417
theorem B2108153 : Blo 1403521 2108153 := bstep (se 2 (by rfl) ⟨790557, by rfl⟩ : syracuseStep 2108153 = 1581115) B1581115
theorem B1403687 : Blo 1403521 1403687 := bstep (se 1 (by rfl) ⟨1052765, by rfl⟩ : syracuseStep 1403687 = 2105531) B2105531
theorem B2370377 : Blo 1403521 2370377 := bstep (se 2 (by rfl) ⟨888891, by rfl⟩ : syracuseStep 2370377 = 1777783) B1777783
theorem B1403727 : Blo 1403521 1403727 := bstep (se 1 (by rfl) ⟨1052795, by rfl⟩ : syracuseStep 1403727 = 2105591) B2105591
theorem B1403743 : Blo 1403521 1403743 := bstep (se 1 (by rfl) ⟨1052807, by rfl⟩ : syracuseStep 1403743 = 2105615) B2105615
theorem B2108255 : Blo 1403521 2108255 := bstep (se 1 (by rfl) ⟨1581191, by rfl⟩ : syracuseStep 2108255 = 3162383) B3162383
theorem B5335915 : Blo 1403521 5335915 := bstep (se 1 (by rfl) ⟨4001936, by rfl⟩ : syracuseStep 5335915 = 8003873) B8003873
theorem B2108267 : Blo 1403521 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B1403771 : Blo 1403521 1403771 := bstep (se 1 (by rfl) ⟨1052828, by rfl⟩ : syracuseStep 1403771 = 2105657) B2105657
theorem B20237201 : Blo 1403521 20237201 := bstep (se 2 (by rfl) ⟨7588950, by rfl⟩ : syracuseStep 20237201 = 15177901) B15177901
theorem B1403823 : Blo 1403521 1403823 := bstep (se 1 (by rfl) ⟨1052867, by rfl⟩ : syracuseStep 1403823 = 2105735) B2105735
theorem B2665399 : Blo 1403521 2665399 := bstep (se 1 (by rfl) ⟨1999049, by rfl⟩ : syracuseStep 2665399 = 3998099) B3998099
theorem B9612215 : Blo 1403521 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B1403847 : Blo 1403521 1403847 := bstep (se 1 (by rfl) ⟨1052885, by rfl⟩ : syracuseStep 1403847 = 2105771) B2105771
theorem B1403867 : Blo 1403521 1403867 := bstep (se 1 (by rfl) ⟨1052900, by rfl⟩ : syracuseStep 1403867 = 2105801) B2105801
theorem B4738067 : Blo 1403521 4738067 := bstep (se 1 (by rfl) ⟨3553550, by rfl⟩ : syracuseStep 4738067 = 7107101) B7107101
theorem B1403943 : Blo 1403521 1403943 := bstep (se 1 (by rfl) ⟨1052957, by rfl⟩ : syracuseStep 1403943 = 2105915) B2105915
theorem B1403983 : Blo 1403521 1403983 := bstep (se 1 (by rfl) ⟨1052987, by rfl⟩ : syracuseStep 1403983 = 2105975) B2105975
theorem B1403999 : Blo 1403521 1403999 := bstep (se 1 (by rfl) ⟨1052999, by rfl⟩ : syracuseStep 1403999 = 2105999) B2105999
theorem B1404027 : Blo 1403521 1404027 := bstep (se 1 (by rfl) ⟨1053020, by rfl⟩ : syracuseStep 1404027 = 2106041) B2106041
theorem B1404079 : Blo 1403521 1404079 := bstep (se 1 (by rfl) ⟨1053059, by rfl⟩ : syracuseStep 1404079 = 2106119) B2106119
theorem B1404103 : Blo 1403521 1404103 := bstep (se 1 (by rfl) ⟨1053077, by rfl⟩ : syracuseStep 1404103 = 2106155) B2106155
theorem B1404123 : Blo 1403521 1404123 := bstep (se 1 (by rfl) ⟨1053092, by rfl⟩ : syracuseStep 1404123 = 2106185) B2106185
theorem B4001015 : Blo 1403521 4001015 := bstep (se 1 (by rfl) ⟨3000761, by rfl⟩ : syracuseStep 4001015 = 6001523) B6001523
theorem B2370809 : Blo 1403521 2370809 := bstep (se 2 (by rfl) ⟨889053, by rfl⟩ : syracuseStep 2370809 = 1778107) B1778107
theorem B1404199 : Blo 1403521 1404199 := bstep (se 1 (by rfl) ⟨1053149, by rfl⟩ : syracuseStep 1404199 = 2106299) B2106299
theorem B2665801 : Blo 1403521 2665801 := bstep (se 2 (by rfl) ⟨999675, by rfl⟩ : syracuseStep 2665801 = 1999351) B1999351
theorem B1404239 : Blo 1403521 1404239 := bstep (se 1 (by rfl) ⟨1053179, by rfl⟩ : syracuseStep 1404239 = 2106359) B2106359
theorem B4738391 : Blo 1403521 4738391 := bstep (se 1 (by rfl) ⟨3553793, by rfl⟩ : syracuseStep 4738391 = 7107587) B7107587
theorem B1404255 : Blo 1403521 1404255 := bstep (se 1 (by rfl) ⟨1053191, by rfl⟩ : syracuseStep 1404255 = 2106383) B2106383
theorem B1404283 : Blo 1403521 1404283 := bstep (se 1 (by rfl) ⟨1053212, by rfl⟩ : syracuseStep 1404283 = 2106425) B2106425
theorem B43249031 : Blo 1403521 43249031 := bstep (se 1 (by rfl) ⟨32436773, by rfl⟩ : syracuseStep 43249031 = 64873547) B64873547
theorem B1404335 : Blo 1403521 1404335 := bstep (se 1 (by rfl) ⟨1053251, by rfl⟩ : syracuseStep 1404335 = 2106503) B2106503
theorem B2370991 : Blo 1403521 2370991 := bstep (se 1 (by rfl) ⟨1778243, by rfl⟩ : syracuseStep 2370991 = 3556487) B3556487
theorem B1404359 : Blo 1403521 1404359 := bstep (se 1 (by rfl) ⟨1053269, by rfl⟩ : syracuseStep 1404359 = 2106539) B2106539
theorem B4500937 : Blo 1403521 4500937 := bstep (se 2 (by rfl) ⟨1687851, by rfl⟩ : syracuseStep 4500937 = 3375703) B3375703
theorem B1404379 : Blo 1403521 1404379 := bstep (se 1 (by rfl) ⟨1053284, by rfl⟩ : syracuseStep 1404379 = 2106569) B2106569
theorem B2371079 : Blo 1403521 2371079 := bstep (se 1 (by rfl) ⟨1778309, by rfl⟩ : syracuseStep 2371079 = 3556619) B3556619
theorem B4501001 : Blo 1403521 4501001 := bstep (se 2 (by rfl) ⟨1687875, by rfl⟩ : syracuseStep 4501001 = 3375751) B3375751
theorem B1404455 : Blo 1403521 1404455 := bstep (se 1 (by rfl) ⟨1053341, by rfl⟩ : syracuseStep 1404455 = 2106683) B2106683
theorem B1404495 : Blo 1403521 1404495 := bstep (se 1 (by rfl) ⟨1053371, by rfl⟩ : syracuseStep 1404495 = 2106743) B2106743
theorem B1404511 : Blo 1403521 1404511 := bstep (se 1 (by rfl) ⟨1053383, by rfl⟩ : syracuseStep 1404511 = 2106767) B2106767
theorem B17993339 : Blo 1403521 17993339 := bstep (se 1 (by rfl) ⟨13495004, by rfl⟩ : syracuseStep 17993339 = 26990009) B26990009
theorem B1404539 : Blo 1403521 1404539 := bstep (se 1 (by rfl) ⟨1053404, by rfl⟩ : syracuseStep 1404539 = 2106809) B2106809
theorem B1404591 : Blo 1403521 1404591 := bstep (se 1 (by rfl) ⟨1053443, by rfl⟩ : syracuseStep 1404591 = 2106887) B2106887
theorem B1404615 : Blo 1403521 1404615 := bstep (se 1 (by rfl) ⟨1053461, by rfl⟩ : syracuseStep 1404615 = 2106923) B2106923
theorem B2404039 : Blo 1403521 2404039 := bstep (se 1 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 2404039 = 3606059) B3606059
theorem B1404635 : Blo 1403521 1404635 := bstep (se 1 (by rfl) ⟨1053476, by rfl⟩ : syracuseStep 1404635 = 2106953) B2106953
theorem B1404711 : Blo 1403521 1404711 := bstep (se 1 (by rfl) ⟨1053533, by rfl⟩ : syracuseStep 1404711 = 2107067) B2107067
theorem B3419977 : Blo 1403521 3419977 := bstep (se 2 (by rfl) ⟨1282491, by rfl⟩ : syracuseStep 3419977 = 2564983) B2564983
theorem B1404751 : Blo 1403521 1404751 := bstep (se 1 (by rfl) ⟨1053563, by rfl⟩ : syracuseStep 1404751 = 2107127) B2107127
theorem B1404767 : Blo 1403521 1404767 := bstep (se 1 (by rfl) ⟨1053575, by rfl⟩ : syracuseStep 1404767 = 2107151) B2107151
theorem B2371423 : Blo 1403521 2371423 := bstep (se 1 (by rfl) ⟨1778567, by rfl⟩ : syracuseStep 2371423 = 3557135) B3557135
theorem B2248553 : Blo 1403521 2248553 := bstep (se 2 (by rfl) ⟨843207, by rfl⟩ : syracuseStep 2248553 = 1686415) B1686415
theorem B1404795 : Blo 1403521 1404795 := bstep (se 1 (by rfl) ⟨1053596, by rfl⟩ : syracuseStep 1404795 = 2107193) B2107193
theorem B1404847 : Blo 1403521 1404847 := bstep (se 1 (by rfl) ⟨1053635, by rfl⟩ : syracuseStep 1404847 = 2107271) B2107271
theorem B2371511 : Blo 1403521 2371511 := bstep (se 1 (by rfl) ⟨1778633, by rfl⟩ : syracuseStep 2371511 = 3557267) B3557267
theorem B1404871 : Blo 1403521 1404871 := bstep (se 1 (by rfl) ⟨1053653, by rfl⟩ : syracuseStep 1404871 = 2107307) B2107307
theorem B1404891 : Blo 1403521 1404891 := bstep (se 1 (by rfl) ⟨1053668, by rfl⟩ : syracuseStep 1404891 = 2107337) B2107337
theorem B2666515 : Blo 1403521 2666515 := bstep (se 1 (by rfl) ⟨1999886, by rfl⟩ : syracuseStep 2666515 = 3999773) B3999773
theorem B12988445 : Blo 1403521 12988445 := bstep (se 3 (by rfl) ⟨2435333, by rfl⟩ : syracuseStep 12988445 = 4870667) B4870667
theorem B1404967 : Blo 1403521 1404967 := bstep (se 1 (by rfl) ⟨1053725, by rfl⟩ : syracuseStep 1404967 = 2107451) B2107451
theorem B1405007 : Blo 1403521 1405007 := bstep (se 1 (by rfl) ⟨1053755, by rfl⟩ : syracuseStep 1405007 = 2107511) B2107511
theorem B1405023 : Blo 1403521 1405023 := bstep (se 1 (by rfl) ⟨1053767, by rfl⟩ : syracuseStep 1405023 = 2107535) B2107535
theorem B1405051 : Blo 1403521 1405051 := bstep (se 1 (by rfl) ⟨1053788, by rfl⟩ : syracuseStep 1405051 = 2107577) B2107577
theorem B1405103 : Blo 1403521 1405103 := bstep (se 1 (by rfl) ⟨1053827, by rfl⟩ : syracuseStep 1405103 = 2107655) B2107655
theorem B1405127 : Blo 1403521 1405127 := bstep (se 1 (by rfl) ⟨1053845, by rfl⟩ : syracuseStep 1405127 = 2107691) B2107691
theorem B1405147 : Blo 1403521 1405147 := bstep (se 1 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 1405147 = 2107721) B2107721
theorem B168612113 : Blo 1403521 168612113 := bstep (se 2 (by rfl) ⟨63229542, by rfl⟩ : syracuseStep 168612113 = 126459085) B126459085
theorem B1405223 : Blo 1403521 1405223 := bstep (se 1 (by rfl) ⟨1053917, by rfl⟩ : syracuseStep 1405223 = 2107835) B2107835
theorem B23081291 : Blo 1403521 23081291 := bstep (se 1 (by rfl) ⟨17310968, by rfl⟩ : syracuseStep 23081291 = 34621937) B34621937
theorem B1405263 : Blo 1403521 1405263 := bstep (se 1 (by rfl) ⟨1053947, by rfl⟩ : syracuseStep 1405263 = 2107895) B2107895
theorem B1405279 : Blo 1403521 1405279 := bstep (se 1 (by rfl) ⟨1053959, by rfl⟩ : syracuseStep 1405279 = 2107919) B2107919
theorem B2666857 : Blo 1403521 2666857 := bstep (se 2 (by rfl) ⟨1000071, by rfl⟩ : syracuseStep 2666857 = 2000143) B2000143
theorem B1405307 : Blo 1403521 1405307 := bstep (se 1 (by rfl) ⟨1053980, by rfl⟩ : syracuseStep 1405307 = 2107961) B2107961
theorem B5058941 : Blo 1403521 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B4739471 : Blo 1403521 4739471 := bstep (se 1 (by rfl) ⟨3554603, by rfl⟩ : syracuseStep 4739471 = 7109207) B7109207
theorem B1405359 : Blo 1403521 1405359 := bstep (se 1 (by rfl) ⟨1054019, by rfl⟩ : syracuseStep 1405359 = 2108039) B2108039
theorem B1405383 : Blo 1403521 1405383 := bstep (se 1 (by rfl) ⟨1054037, by rfl⟩ : syracuseStep 1405383 = 2108075) B2108075
theorem B10817995 : Blo 1403521 10817995 := bstep (se 1 (by rfl) ⟨8113496, by rfl⟩ : syracuseStep 10817995 = 16226993) B16226993
theorem B1405403 : Blo 1403521 1405403 := bstep (se 1 (by rfl) ⟨1054052, by rfl⟩ : syracuseStep 1405403 = 2108105) B2108105
theorem B10670615 : Blo 1403521 10670615 := bstep (se 1 (by rfl) ⟨8002961, by rfl⟩ : syracuseStep 10670615 = 16005923) B16005923
theorem B3158567 : Blo 1403521 3158567 := bstep (se 1 (by rfl) ⟨2368925, by rfl⟩ : syracuseStep 3158567 = 4737851) B4737851
theorem B1405479 : Blo 1403521 1405479 := bstep (se 1 (by rfl) ⟨1054109, by rfl⟩ : syracuseStep 1405479 = 2108219) B2108219
theorem B1405519 : Blo 1403521 1405519 := bstep (se 1 (by rfl) ⟨1054139, by rfl⟩ : syracuseStep 1405519 = 2108279) B2108279
theorem B5329597 : Blo 1403521 5329597 := bstep (se 3 (by rfl) ⟨999299, by rfl⟩ : syracuseStep 5329597 = 1998599) B1998599
theorem B4739795 : Blo 1403521 4739795 := bstep (se 1 (by rfl) ⟨3554846, by rfl⟩ : syracuseStep 4739795 = 7109693) B7109693
theorem B3158891 : Blo 1403521 3158891 := bstep (se 1 (by rfl) ⟨2369168, by rfl⟩ : syracuseStep 3158891 = 4738337) B4738337
theorem B3158945 : Blo 1403521 3158945 := bstep (se 2 (by rfl) ⟨1184604, by rfl⟩ : syracuseStep 3158945 = 2369209) B2369209
theorem B10662839 : Blo 1403521 10662839 := bstep (se 1 (by rfl) ⟨7997129, by rfl⟩ : syracuseStep 10662839 = 15994259) B15994259
theorem B3159287 : Blo 1403521 3159287 := bstep (se 1 (by rfl) ⟨2369465, by rfl⟩ : syracuseStep 3159287 = 4738931) B4738931
theorem B2249975 : Blo 1403521 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B20256115 : Blo 1403521 20256115 := bstep (se 1 (by rfl) ⟨15192086, by rfl⟩ : syracuseStep 20256115 = 30384173) B30384173
theorem B17986981 : Blo 1403521 17986981 := bstep (se 4 (by rfl) ⟨1686279, by rfl⟩ : syracuseStep 17986981 = 3372559) B3372559
theorem B16430501 : Blo 1403521 16430501 := bstep (se 4 (by rfl) ⟨1540359, by rfl⟩ : syracuseStep 16430501 = 3080719) B3080719
theorem B3552731 : Blo 1403521 3552731 := bstep (se 1 (by rfl) ⟨2664548, by rfl⟩ : syracuseStep 3552731 = 5329097) B5329097
theorem B4273651 : Blo 1403521 4273651 := bstep (se 1 (by rfl) ⟨3205238, by rfl⟩ : syracuseStep 4273651 = 6410477) B6410477
theorem B5330555 : Blo 1403521 5330555 := bstep (se 1 (by rfl) ⟨3997916, by rfl⟩ : syracuseStep 5330555 = 7995833) B7995833
theorem B7108235 : Blo 1403521 7108235 := bstep (se 1 (by rfl) ⟨5331176, by rfl⟩ : syracuseStep 7108235 = 10662353) B10662353
theorem B2668231 : Blo 1403521 2668231 := bstep (se 1 (by rfl) ⟨2001173, by rfl⟩ : syracuseStep 2668231 = 4002347) B4002347
theorem B3159881 : Blo 1403521 3159881 := bstep (se 2 (by rfl) ⟨1184955, by rfl⟩ : syracuseStep 3159881 = 2369911) B2369911
theorem B14423903 : Blo 1403521 14423903 := bstep (se 1 (by rfl) ⟨10817927, by rfl⟩ : syracuseStep 14423903 = 21635855) B21635855
theorem B4052843 : Blo 1403521 4052843 := bstep (se 1 (by rfl) ⟨3039632, by rfl⟩ : syracuseStep 4052843 = 6079265) B6079265
theorem B4740983 : Blo 1403521 4740983 := bstep (se 1 (by rfl) ⟨3555737, by rfl⟩ : syracuseStep 4740983 = 7111475) B7111475
theorem B9115577 : Blo 1403521 9115577 := bstep (se 2 (by rfl) ⟨3418341, by rfl⟩ : syracuseStep 9115577 = 6836683) B6836683
theorem B10958777 : Blo 1403521 10958777 := bstep (se 2 (by rfl) ⟨4109541, by rfl⟩ : syracuseStep 10958777 = 8219083) B8219083
theorem B35993645 : Blo 1403521 35993645 := bstep (se 3 (by rfl) ⟨6748808, by rfl⟩ : syracuseStep 35993645 = 13497617) B13497617
theorem B4741199 : Blo 1403521 4741199 := bstep (se 1 (by rfl) ⟨3555899, by rfl⟩ : syracuseStep 4741199 = 7111799) B7111799
theorem B1579207 : Blo 1403521 1579207 := bstep (se 1 (by rfl) ⟨1184405, by rfl⟩ : syracuseStep 1579207 = 2368811) B2368811
theorem B10664297 : Blo 1403521 10664297 := bstep (se 2 (by rfl) ⟨3999111, by rfl⟩ : syracuseStep 10664297 = 7998223) B7998223
theorem B5331329 : Blo 1403521 5331329 := bstep (se 2 (by rfl) ⟨1999248, by rfl⟩ : syracuseStep 5331329 = 3998497) B3998497
theorem B4741577 : Blo 1403521 4741577 := bstep (se 2 (by rfl) ⟨1778091, by rfl⟩ : syracuseStep 4741577 = 3556183) B3556183
theorem B6085153 : Blo 1403521 6085153 := bstep (se 2 (by rfl) ⟨2281932, by rfl⟩ : syracuseStep 6085153 = 4563865) B4563865
theorem B8993339 : Blo 1403521 8993339 := bstep (se 1 (by rfl) ⟨6745004, by rfl⟩ : syracuseStep 8993339 = 13490009) B13490009
theorem B3603041 : Blo 1403521 3603041 := bstep (se 2 (by rfl) ⟨1351140, by rfl⟩ : syracuseStep 3603041 = 2702281) B2702281
theorem B3160673 : Blo 1403521 3160673 := bstep (se 2 (by rfl) ⟨1185252, by rfl⟩ : syracuseStep 3160673 = 2370505) B2370505
theorem B3553915 : Blo 1403521 3553915 := bstep (se 1 (by rfl) ⟨2665436, by rfl⟩ : syracuseStep 3553915 = 5330873) B5330873
theorem B4741847 : Blo 1403521 4741847 := bstep (se 1 (by rfl) ⟨3556385, by rfl⟩ : syracuseStep 4741847 = 7112771) B7112771
theorem B1686367 : Blo 1403521 1686367 := bstep (se 1 (by rfl) ⟨1264775, by rfl⟩ : syracuseStep 1686367 = 2529551) B2529551
theorem B4742063 : Blo 1403521 4742063 := bstep (se 1 (by rfl) ⟨3556547, by rfl⟩ : syracuseStep 4742063 = 7113095) B7113095
theorem B3161015 : Blo 1403521 3161015 := bstep (se 1 (by rfl) ⟨2370761, by rfl⟩ : syracuseStep 3161015 = 4741523) B4741523
theorem B1580071 : Blo 1403521 1580071 := bstep (se 1 (by rfl) ⟨1185053, by rfl⟩ : syracuseStep 1580071 = 2370107) B2370107
theorem B5062013 : Blo 1403521 5062013 := bstep (se 3 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 5062013 = 1898255) B1898255
theorem B1777079 : Blo 1403521 1777079 := bstep (se 1 (by rfl) ⟨1332809, by rfl⟩ : syracuseStep 1777079 = 2665619) B2665619
theorem B1924571 : Blo 1403521 1924571 := bstep (se 1 (by rfl) ⟨1443428, by rfl⟩ : syracuseStep 1924571 = 2886857) B2886857
theorem B3161609 : Blo 1403521 3161609 := bstep (se 2 (by rfl) ⟨1185603, by rfl⟩ : syracuseStep 3161609 = 2371207) B2371207
theorem B5332513 : Blo 1403521 5332513 := bstep (se 2 (by rfl) ⟨1999692, by rfl⟩ : syracuseStep 5332513 = 3999385) B3999385
theorem B2530855 : Blo 1403521 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B1777231 : Blo 1403521 1777231 := bstep (se 1 (by rfl) ⟨1332923, by rfl⟩ : syracuseStep 1777231 = 2665847) B2665847
theorem B20258423 : Blo 1403521 20258423 := bstep (se 1 (by rfl) ⟨15193817, by rfl⟩ : syracuseStep 20258423 = 30387635) B30387635
theorem B20512379 : Blo 1403521 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B10124945 : Blo 1403521 10124945 := bstep (se 2 (by rfl) ⟨3796854, by rfl⟩ : syracuseStep 10124945 = 7593709) B7593709
theorem B4390615 : Blo 1403521 4390615 := bstep (se 1 (by rfl) ⟨3292961, by rfl⟩ : syracuseStep 4390615 = 6585923) B6585923
theorem B5693257 : Blo 1403521 5693257 := bstep (se 2 (by rfl) ⟨2134971, by rfl⟩ : syracuseStep 5693257 = 4269943) B4269943
theorem B3161951 : Blo 1403521 3161951 := bstep (se 1 (by rfl) ⟨2371463, by rfl⟩ : syracuseStep 3161951 = 4742927) B4742927
theorem B2531179 : Blo 1403521 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B8994721 : Blo 1403521 8994721 := bstep (se 2 (by rfl) ⟨3373020, by rfl⟩ : syracuseStep 8994721 = 6746041) B6746041
theorem B2703265 : Blo 1403521 2703265 := bstep (se 2 (by rfl) ⟨1013724, by rfl⟩ : syracuseStep 2703265 = 2027449) B2027449
theorem B1925047 : Blo 1403521 1925047 := bstep (se 1 (by rfl) ⟨1443785, by rfl⟩ : syracuseStep 1925047 = 2887571) B2887571
theorem B7110665 : Blo 1403521 7110665 := bstep (se 2 (by rfl) ⟨2666499, by rfl⟩ : syracuseStep 7110665 = 5332999) B5332999
theorem B3555353 : Blo 1403521 3555353 := bstep (se 2 (by rfl) ⟨1333257, by rfl⟩ : syracuseStep 3555353 = 2666515) B2666515
theorem B34635853 : Blo 1403521 34635853 := bstep (se 3 (by rfl) ⟨6494222, by rfl⟩ : syracuseStep 34635853 = 12988445) B12988445
theorem B7110827 : Blo 1403521 7110827 := bstep (se 1 (by rfl) ⟨5333120, by rfl⟩ : syracuseStep 7110827 = 10666241) B10666241
theorem B2105609 : Blo 1403521 2105609 := bstep (se 2 (by rfl) ⟨789603, by rfl⟩ : syracuseStep 2105609 = 1579207) B1579207
theorem B5996891 : Blo 1403521 5996891 := bstep (se 1 (by rfl) ⟨4497668, by rfl⟩ : syracuseStep 5996891 = 8995337) B8995337
theorem B2105711 : Blo 1403521 2105711 := bstep (se 1 (by rfl) ⟨1579283, by rfl⟩ : syracuseStep 2105711 = 3158567) B3158567
theorem B2998711 : Blo 1403521 2998711 := bstep (se 1 (by rfl) ⟨2249033, by rfl⟩ : syracuseStep 2998711 = 4498067) B4498067
theorem B5693921 : Blo 1403521 5693921 := bstep (se 2 (by rfl) ⟨2135220, by rfl⟩ : syracuseStep 5693921 = 4270441) B4270441
theorem B3555809 : Blo 1403521 3555809 := bstep (se 2 (by rfl) ⟨1333428, by rfl⟩ : syracuseStep 3555809 = 2666857) B2666857
theorem B3555859 : Blo 1403521 3555859 := bstep (se 1 (by rfl) ⟨2666894, by rfl⟩ : syracuseStep 3555859 = 5333789) B5333789
theorem B2105927 : Blo 1403521 2105927 := bstep (se 1 (by rfl) ⟨1579445, by rfl⟩ : syracuseStep 2105927 = 3158891) B3158891
theorem B1688159 : Blo 1403521 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B2105963 : Blo 1403521 2105963 := bstep (se 1 (by rfl) ⟨1579472, by rfl⟩ : syracuseStep 2105963 = 3158945) B3158945
theorem B7111313 : Blo 1403521 7111313 := bstep (se 2 (by rfl) ⟨2666742, by rfl⟩ : syracuseStep 7111313 = 5333485) B5333485
theorem B36504265 : Blo 1403521 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B3605239 : Blo 1403521 3605239 := bstep (se 1 (by rfl) ⟨2703929, by rfl⟩ : syracuseStep 3605239 = 5407859) B5407859
theorem B2106191 : Blo 1403521 2106191 := bstep (se 1 (by rfl) ⟨1579643, by rfl⟩ : syracuseStep 2106191 = 3159287) B3159287
theorem B5997473 : Blo 1403521 5997473 := bstep (se 2 (by rfl) ⟨2249052, by rfl⟩ : syracuseStep 5997473 = 4498105) B4498105
theorem B10953667 : Blo 1403521 10953667 := bstep (se 1 (by rfl) ⟨8215250, by rfl⟩ : syracuseStep 10953667 = 16430501) B16430501
theorem B2368487 : Blo 1403521 2368487 := bstep (se 1 (by rfl) ⟨1776365, by rfl⟩ : syracuseStep 2368487 = 3552731) B3552731
theorem B2106587 : Blo 1403521 2106587 := bstep (se 1 (by rfl) ⟨1579940, by rfl⟩ : syracuseStep 2106587 = 3159881) B3159881
theorem B23995763 : Blo 1403521 23995763 := bstep (se 1 (by rfl) ⟨17996822, by rfl⟩ : syracuseStep 23995763 = 35993645) B35993645
theorem B2000251 : Blo 1403521 2000251 := bstep (se 1 (by rfl) ⟨1500188, by rfl⟩ : syracuseStep 2000251 = 3000377) B3000377
theorem B5064059 : Blo 1403521 5064059 := bstep (se 1 (by rfl) ⟨3798044, by rfl⟩ : syracuseStep 5064059 = 7596089) B7596089
theorem B2106761 : Blo 1403521 2106761 := bstep (se 2 (by rfl) ⟨790035, by rfl⟩ : syracuseStep 2106761 = 1580071) B1580071
theorem B2000479 : Blo 1403521 2000479 := bstep (se 1 (by rfl) ⟨1500359, by rfl⟩ : syracuseStep 2000479 = 3000719) B3000719
theorem B2402027 : Blo 1403521 2402027 := bstep (se 1 (by rfl) ⟨1801520, by rfl⟩ : syracuseStep 2402027 = 3603041) B3603041
theorem B2107115 : Blo 1403521 2107115 := bstep (se 1 (by rfl) ⟨1580336, by rfl⟩ : syracuseStep 2107115 = 3160673) B3160673
theorem B3376943 : Blo 1403521 3376943 := bstep (se 1 (by rfl) ⟨2532707, by rfl⟩ : syracuseStep 3376943 = 5065415) B5065415
theorem B2000695 : Blo 1403521 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B3901289 : Blo 1403521 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B6408143 : Blo 1403521 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B2107343 : Blo 1403521 2107343 := bstep (se 1 (by rfl) ⟨1580507, by rfl⟩ : syracuseStep 2107343 = 3161015) B3161015
theorem B2369641 : Blo 1403521 2369641 := bstep (se 2 (by rfl) ⟨888615, by rfl⟩ : syracuseStep 2369641 = 1777231) B1777231
theorem B3205385 : Blo 1403521 3205385 := bstep (se 2 (by rfl) ⟨1202019, by rfl⟩ : syracuseStep 3205385 = 2404039) B2404039
theorem B3557641 : Blo 1403521 3557641 := bstep (se 2 (by rfl) ⟨1334115, by rfl⟩ : syracuseStep 3557641 = 2668231) B2668231
theorem B5998873 : Blo 1403521 5998873 := bstep (se 2 (by rfl) ⟨2249577, by rfl⟩ : syracuseStep 5998873 = 4499155) B4499155
theorem B10266917 : Blo 1403521 10266917 := bstep (se 4 (by rfl) ⟨962523, by rfl⟩ : syracuseStep 10266917 = 1925047) B1925047
theorem B3000667 : Blo 1403521 3000667 := bstep (se 1 (by rfl) ⟨2250500, by rfl⟩ : syracuseStep 3000667 = 4501001) B4501001
theorem B2107739 : Blo 1403521 2107739 := bstep (se 1 (by rfl) ⟨1580804, by rfl⟩ : syracuseStep 2107739 = 3161609) B3161609
theorem B13674919 : Blo 1403521 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B11995559 : Blo 1403521 11995559 := bstep (se 1 (by rfl) ⟨8996669, by rfl⟩ : syracuseStep 11995559 = 17993339) B17993339
theorem B2107967 : Blo 1403521 2107967 := bstep (se 1 (by rfl) ⟨1580975, by rfl⟩ : syracuseStep 2107967 = 3161951) B3161951
theorem B2108087 : Blo 1403521 2108087 := bstep (se 1 (by rfl) ⟨1581065, by rfl⟩ : syracuseStep 2108087 = 3162131) B3162131
theorem B1403615 : Blo 1403521 1403615 := bstep (se 1 (by rfl) ⟨1052711, by rfl⟩ : syracuseStep 1403615 = 2105423) B2105423
theorem B11995937 : Blo 1403521 11995937 := bstep (se 2 (by rfl) ⟨4498476, by rfl⟩ : syracuseStep 11995937 = 8996953) B8996953
theorem B1403695 : Blo 1403521 1403695 := bstep (se 1 (by rfl) ⟨1052771, by rfl⟩ : syracuseStep 1403695 = 2105543) B2105543
theorem B15387527 : Blo 1403521 15387527 := bstep (se 1 (by rfl) ⟨11540645, by rfl⟩ : syracuseStep 15387527 = 23081291) B23081291
theorem B1403803 : Blo 1403521 1403803 := bstep (se 1 (by rfl) ⟨1052852, by rfl⟩ : syracuseStep 1403803 = 2105705) B2105705
theorem B1403855 : Blo 1403521 1403855 := bstep (se 1 (by rfl) ⟨1052891, by rfl⟩ : syracuseStep 1403855 = 2105783) B2105783
theorem B1403879 : Blo 1403521 1403879 := bstep (se 1 (by rfl) ⟨1052909, by rfl⟩ : syracuseStep 1403879 = 2105819) B2105819
theorem B6745103 : Blo 1403521 6745103 := bstep (se 1 (by rfl) ⟨5058827, by rfl⟩ : syracuseStep 6745103 = 10117655) B10117655
theorem B7113743 : Blo 1403521 7113743 := bstep (se 1 (by rfl) ⟨5335307, by rfl⟩ : syracuseStep 7113743 = 10670615) B10670615
theorem B9120883 : Blo 1403521 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B1404191 : Blo 1403521 1404191 := bstep (se 1 (by rfl) ⟨1053143, by rfl⟩ : syracuseStep 1404191 = 2106287) B2106287
theorem B5999933 : Blo 1403521 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B5336387 : Blo 1403521 5336387 := bstep (se 1 (by rfl) ⟨4002290, by rfl⟩ : syracuseStep 5336387 = 8004581) B8004581
theorem B1404251 : Blo 1403521 1404251 := bstep (se 1 (by rfl) ⟨1053188, by rfl⟩ : syracuseStep 1404251 = 2106377) B2106377
theorem B1404271 : Blo 1403521 1404271 := bstep (se 1 (by rfl) ⟨1053203, by rfl⟩ : syracuseStep 1404271 = 2106407) B2106407
theorem B8113537 : Blo 1403521 8113537 := bstep (se 2 (by rfl) ⟨3042576, by rfl⟩ : syracuseStep 8113537 = 6085153) B6085153
theorem B1404327 : Blo 1403521 1404327 := bstep (se 1 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 1404327 = 2106491) B2106491
theorem B4738553 : Blo 1403521 4738553 := bstep (se 2 (by rfl) ⟨1776957, by rfl⟩ : syracuseStep 4738553 = 3553915) B3553915
theorem B1404411 : Blo 1403521 1404411 := bstep (se 1 (by rfl) ⟨1053308, by rfl⟩ : syracuseStep 1404411 = 2106617) B2106617
theorem B1404479 : Blo 1403521 1404479 := bstep (se 1 (by rfl) ⟨1053359, by rfl⟩ : syracuseStep 1404479 = 2106719) B2106719
theorem B1404487 : Blo 1403521 1404487 := bstep (se 1 (by rfl) ⟨1053365, by rfl⟩ : syracuseStep 1404487 = 2106731) B2106731
theorem B7106129 : Blo 1403521 7106129 := bstep (se 2 (by rfl) ⟨2664798, by rfl⟩ : syracuseStep 7106129 = 5329597) B5329597
theorem B1404639 : Blo 1403521 1404639 := bstep (se 1 (by rfl) ⟨1053479, by rfl⟩ : syracuseStep 1404639 = 2106959) B2106959
theorem B4738823 : Blo 1403521 4738823 := bstep (se 1 (by rfl) ⟨3554117, by rfl⟩ : syracuseStep 4738823 = 7108235) B7108235
theorem B2248489 : Blo 1403521 2248489 := bstep (se 2 (by rfl) ⟨843183, by rfl⟩ : syracuseStep 2248489 = 1686367) B1686367
theorem B2371369 : Blo 1403521 2371369 := bstep (se 2 (by rfl) ⟨889263, by rfl⟩ : syracuseStep 2371369 = 1778527) B1778527
theorem B2666287 : Blo 1403521 2666287 := bstep (se 1 (by rfl) ⟨1999715, by rfl⟩ : syracuseStep 2666287 = 3999431) B3999431
theorem B1404719 : Blo 1403521 1404719 := bstep (se 1 (by rfl) ⟨1053539, by rfl⟩ : syracuseStep 1404719 = 2107079) B2107079
theorem B7114553 : Blo 1403521 7114553 := bstep (se 2 (by rfl) ⟨2667957, by rfl⟩ : syracuseStep 7114553 = 5335915) B5335915
theorem B4738877 : Blo 1403521 4738877 := bstep (se 3 (by rfl) ⟨888539, by rfl⟩ : syracuseStep 4738877 = 1777079) B1777079
theorem B1404827 : Blo 1403521 1404827 := bstep (se 1 (by rfl) ⟨1053620, by rfl⟩ : syracuseStep 1404827 = 2107241) B2107241
theorem B5132189 : Blo 1403521 5132189 := bstep (se 3 (by rfl) ⟨962285, by rfl⟩ : syracuseStep 5132189 = 1924571) B1924571
theorem B1404879 : Blo 1403521 1404879 := bstep (se 1 (by rfl) ⟨1053659, by rfl⟩ : syracuseStep 1404879 = 2107319) B2107319
theorem B1404903 : Blo 1403521 1404903 := bstep (se 1 (by rfl) ⟨1053677, by rfl⟩ : syracuseStep 1404903 = 2107355) B2107355
theorem B9613417 : Blo 1403521 9613417 := bstep (se 2 (by rfl) ⟨3605031, by rfl⟩ : syracuseStep 9613417 = 7210063) B7210063
theorem B1405215 : Blo 1403521 1405215 := bstep (se 1 (by rfl) ⟨1053911, by rfl⟩ : syracuseStep 1405215 = 2107823) B2107823
theorem B1405275 : Blo 1403521 1405275 := bstep (se 1 (by rfl) ⟨1053956, by rfl⟩ : syracuseStep 1405275 = 2107913) B2107913
theorem B1405295 : Blo 1403521 1405295 := bstep (se 1 (by rfl) ⟨1053971, by rfl⟩ : syracuseStep 1405295 = 2107943) B2107943
theorem B1405351 : Blo 1403521 1405351 := bstep (se 1 (by rfl) ⟨1054013, by rfl⟩ : syracuseStep 1405351 = 2108027) B2108027
theorem B6402523 : Blo 1403521 6402523 := bstep (se 1 (by rfl) ⟨4801892, by rfl⟩ : syracuseStep 6402523 = 9603785) B9603785
theorem B1405435 : Blo 1403521 1405435 := bstep (se 1 (by rfl) ⟨1054076, by rfl⟩ : syracuseStep 1405435 = 2108153) B2108153
theorem B23982641 : Blo 1403521 23982641 := bstep (se 2 (by rfl) ⟨8993490, by rfl⟩ : syracuseStep 23982641 = 17986981) B17986981
theorem B1405503 : Blo 1403521 1405503 := bstep (se 1 (by rfl) ⟨1054127, by rfl⟩ : syracuseStep 1405503 = 2108255) B2108255
theorem B1405511 : Blo 1403521 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B6001249 : Blo 1403521 6001249 := bstep (se 2 (by rfl) ⟨2250468, by rfl⟩ : syracuseStep 6001249 = 4500937) B4500937
theorem B5698201 : Blo 1403521 5698201 := bstep (se 2 (by rfl) ⟨2136825, by rfl⟩ : syracuseStep 5698201 = 4273651) B4273651
theorem B3158711 : Blo 1403521 3158711 := bstep (se 1 (by rfl) ⟨2369033, by rfl⟩ : syracuseStep 3158711 = 4738067) B4738067
theorem B2667343 : Blo 1403521 2667343 := bstep (se 1 (by rfl) ⟨2000507, by rfl⟩ : syracuseStep 2667343 = 4001015) B4001015
theorem B3158927 : Blo 1403521 3158927 := bstep (se 1 (by rfl) ⟨2369195, by rfl⟩ : syracuseStep 3158927 = 4738391) B4738391
theorem B28832687 : Blo 1403521 28832687 := bstep (se 1 (by rfl) ⟨21624515, by rfl⟩ : syracuseStep 28832687 = 43249031) B43249031
theorem B5854153 : Blo 1403521 5854153 := bstep (se 2 (by rfl) ⟨2195307, by rfl⟩ : syracuseStep 5854153 = 4390615) B4390615
theorem B13505615 : Blo 1403521 13505615 := bstep (se 1 (by rfl) ⟨10129211, by rfl⟩ : syracuseStep 13505615 = 20258423) B20258423
theorem B7591009 : Blo 1403521 7591009 := bstep (se 2 (by rfl) ⟨2846628, by rfl⟩ : syracuseStep 7591009 = 5693257) B5693257
theorem B4559969 : Blo 1403521 4559969 := bstep (se 2 (by rfl) ⟨1709988, by rfl⟩ : syracuseStep 4559969 = 3419977) B3419977
theorem B3552761 : Blo 1403521 3552761 := bstep (se 2 (by rfl) ⟨1332285, by rfl⟩ : syracuseStep 3552761 = 2664571) B2664571
theorem B3159647 : Blo 1403521 3159647 := bstep (se 1 (by rfl) ⟨2369735, by rfl⟩ : syracuseStep 3159647 = 4739471) B4739471
theorem B3159863 : Blo 1403521 3159863 := bstep (se 1 (by rfl) ⟨2369897, by rfl⟩ : syracuseStep 3159863 = 4739795) B4739795
theorem B14423993 : Blo 1403521 14423993 := bstep (se 2 (by rfl) ⟨5408997, by rfl⟩ : syracuseStep 14423993 = 10817995) B10817995
theorem B7108559 : Blo 1403521 7108559 := bstep (se 1 (by rfl) ⟨5331419, by rfl⟩ : syracuseStep 7108559 = 10662839) B10662839
theorem B57669653 : Blo 1403521 57669653 := bstep (se 6 (by rfl) ⟨1351632, by rfl⟩ : syracuseStep 57669653 = 2703265) B2703265
theorem B449632301 : Blo 1403521 449632301 := bstep (se 3 (by rfl) ⟨84306056, by rfl⟩ : syracuseStep 449632301 = 168612113) B168612113
theorem B3160169 : Blo 1403521 3160169 := bstep (se 2 (by rfl) ⟨1185063, by rfl⟩ : syracuseStep 3160169 = 2370127) B2370127
theorem B3553409 : Blo 1403521 3553409 := bstep (se 2 (by rfl) ⟨1332528, by rfl⟩ : syracuseStep 3553409 = 2665057) B2665057
theorem B13490509 : Blo 1403521 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B1579387 : Blo 1403521 1579387 := bstep (se 1 (by rfl) ⟨1184540, by rfl⟩ : syracuseStep 1579387 = 2369081) B2369081
theorem B3553703 : Blo 1403521 3553703 := bstep (se 1 (by rfl) ⟨2665277, by rfl⟩ : syracuseStep 3553703 = 5330555) B5330555
theorem B20240891 : Blo 1403521 20240891 := bstep (se 1 (by rfl) ⟨15180668, by rfl⟩ : syracuseStep 20240891 = 30361337) B30361337
theorem B45537851 : Blo 1403521 45537851 := bstep (se 1 (by rfl) ⟨34153388, by rfl⟩ : syracuseStep 45537851 = 68306777) B68306777
theorem B9615935 : Blo 1403521 9615935 := bstep (se 1 (by rfl) ⟨7211951, by rfl⟩ : syracuseStep 9615935 = 14423903) B14423903
theorem B2701895 : Blo 1403521 2701895 := bstep (se 1 (by rfl) ⟨2026421, by rfl⟩ : syracuseStep 2701895 = 4052843) B4052843
theorem B3553865 : Blo 1403521 3553865 := bstep (se 2 (by rfl) ⟨1332699, by rfl⟩ : syracuseStep 3553865 = 2665399) B2665399
theorem B3160655 : Blo 1403521 3160655 := bstep (se 1 (by rfl) ⟨2370491, by rfl⟩ : syracuseStep 3160655 = 4740983) B4740983
theorem B4741739 : Blo 1403521 4741739 := bstep (se 1 (by rfl) ⟨3556304, by rfl⟩ : syracuseStep 4741739 = 7112609) B7112609
theorem B6077051 : Blo 1403521 6077051 := bstep (se 1 (by rfl) ⟨4557788, by rfl⟩ : syracuseStep 6077051 = 9115577) B9115577
theorem B7305851 : Blo 1403521 7305851 := bstep (se 1 (by rfl) ⟨5479388, by rfl⟩ : syracuseStep 7305851 = 10958777) B10958777
theorem B10803887 : Blo 1403521 10803887 := bstep (se 1 (by rfl) ⟨8102915, by rfl⟩ : syracuseStep 10803887 = 16205831) B16205831
theorem B3160799 : Blo 1403521 3160799 := bstep (se 1 (by rfl) ⟨2370599, by rfl⟩ : syracuseStep 3160799 = 4741199) B4741199
theorem B1776431 : Blo 1403521 1776431 := bstep (se 1 (by rfl) ⟨1332323, by rfl⟩ : syracuseStep 1776431 = 2664647) B2664647
theorem B1579855 : Blo 1403521 1579855 := bstep (se 1 (by rfl) ⟨1184891, by rfl⟩ : syracuseStep 1579855 = 2369783) B2369783
theorem B7109531 : Blo 1403521 7109531 := bstep (se 1 (by rfl) ⟨5332148, by rfl⟩ : syracuseStep 7109531 = 10664297) B10664297
theorem B3554219 : Blo 1403521 3554219 := bstep (se 1 (by rfl) ⟨2665664, by rfl⟩ : syracuseStep 3554219 = 5331329) B5331329
theorem B3161051 : Blo 1403521 3161051 := bstep (se 1 (by rfl) ⟨2370788, by rfl⟩ : syracuseStep 3161051 = 4741577) B4741577
theorem B5995559 : Blo 1403521 5995559 := bstep (se 1 (by rfl) ⟨4496669, by rfl⟩ : syracuseStep 5995559 = 8993339) B8993339
theorem B3554401 : Blo 1403521 3554401 := bstep (se 2 (by rfl) ⟨1332900, by rfl⟩ : syracuseStep 3554401 = 2665801) B2665801
theorem B3161231 : Blo 1403521 3161231 := bstep (se 1 (by rfl) ⟨2370923, by rfl⟩ : syracuseStep 3161231 = 4741847) B4741847
theorem B27008153 : Blo 1403521 27008153 := bstep (se 2 (by rfl) ⟨10128057, by rfl⟩ : syracuseStep 27008153 = 20256115) B20256115
theorem B4742333 : Blo 1403521 4742333 := bstep (se 3 (by rfl) ⟨889187, by rfl⟩ : syracuseStep 4742333 = 1778375) B1778375
theorem B1580251 : Blo 1403521 1580251 := bstep (se 1 (by rfl) ⟨1185188, by rfl⟩ : syracuseStep 1580251 = 2370377) B2370377
theorem B13499621 : Blo 1403521 13499621 := bstep (se 4 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 13499621 = 2531179) B2531179
theorem B3161321 : Blo 1403521 3161321 := bstep (se 2 (by rfl) ⟨1185495, by rfl⟩ : syracuseStep 3161321 = 2370991) B2370991
theorem B13491467 : Blo 1403521 13491467 := bstep (se 1 (by rfl) ⟨10118600, by rfl⟩ : syracuseStep 13491467 = 20237201) B20237201
theorem B3161375 : Blo 1403521 3161375 := bstep (se 1 (by rfl) ⟨2371031, by rfl⟩ : syracuseStep 3161375 = 4742063) B4742063
theorem B7110017 : Blo 1403521 7110017 := bstep (se 2 (by rfl) ⟨2666256, by rfl⟩ : syracuseStep 7110017 = 5332513) B5332513
theorem B3374473 : Blo 1403521 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B1580539 : Blo 1403521 1580539 := bstep (se 1 (by rfl) ⟨1185404, by rfl⟩ : syracuseStep 1580539 = 2370809) B2370809
theorem B3374675 : Blo 1403521 3374675 := bstep (se 1 (by rfl) ⟨2531006, by rfl⟩ : syracuseStep 3374675 = 5062013) B5062013
theorem B1580719 : Blo 1403521 1580719 := bstep (se 1 (by rfl) ⟨1185539, by rfl⟩ : syracuseStep 1580719 = 2371079) B2371079
theorem B6749963 : Blo 1403521 6749963 := bstep (se 1 (by rfl) ⟨5062472, by rfl⟩ : syracuseStep 6749963 = 10124945) B10124945
theorem B3161897 : Blo 1403521 3161897 := bstep (se 2 (by rfl) ⟨1185711, by rfl⟩ : syracuseStep 3161897 = 2371423) B2371423
theorem B11992961 : Blo 1403521 11992961 := bstep (se 2 (by rfl) ⟨4497360, by rfl⟩ : syracuseStep 11992961 = 8994721) B8994721
theorem B54747029 : Blo 1403521 54747029 := bstep (se 6 (by rfl) ⟨1283133, by rfl⟩ : syracuseStep 54747029 = 2566267) B2566267
theorem B1499035 : Blo 1403521 1499035 := bstep (se 1 (by rfl) ⟨1124276, by rfl⟩ : syracuseStep 1499035 = 2248553) B2248553
theorem B1581007 : Blo 1403521 1581007 := bstep (se 1 (by rfl) ⟨1185755, by rfl⟩ : syracuseStep 1581007 = 2371511) B2371511
theorem B3997927 : Blo 1403521 3997927 := bstep (se 1 (by rfl) ⟨2998445, by rfl⟩ : syracuseStep 3997927 = 5996891) B5996891
theorem B4743521 : Blo 1403521 4743521 := bstep (se 2 (by rfl) ⟨1778820, by rfl⟩ : syracuseStep 4743521 = 3557641) B3557641
theorem B2105807 : Blo 1403521 2105807 := bstep (se 1 (by rfl) ⟨1579355, by rfl⟩ : syracuseStep 2105807 = 3158711) B3158711
theorem B2105849 : Blo 1403521 2105849 := bstep (se 2 (by rfl) ⟨789693, by rfl⟩ : syracuseStep 2105849 = 1579387) B1579387
theorem B3998281 : Blo 1403521 3998281 := bstep (se 2 (by rfl) ⟨1499355, by rfl⟩ : syracuseStep 3998281 = 2998711) B2998711
theorem B2105951 : Blo 1403521 2105951 := bstep (se 1 (by rfl) ⟨1579463, by rfl⟩ : syracuseStep 2105951 = 3158927) B3158927
theorem B3998315 : Blo 1403521 3998315 := bstep (se 1 (by rfl) ⟨2998736, by rfl⟩ : syracuseStep 3998315 = 5997473) B5997473
theorem B8536697 : Blo 1403521 8536697 := bstep (se 2 (by rfl) ⟨3201261, by rfl⟩ : syracuseStep 8536697 = 6402523) B6402523
theorem B9003743 : Blo 1403521 9003743 := bstep (se 1 (by rfl) ⟨6752807, by rfl⟩ : syracuseStep 9003743 = 13505615) B13505615
theorem B3039979 : Blo 1403521 3039979 := bstep (se 1 (by rfl) ⟨2279984, by rfl⟩ : syracuseStep 3039979 = 4559969) B4559969
theorem B27378445 : Blo 1403521 27378445 := bstep (se 3 (by rfl) ⟨5133458, by rfl⟩ : syracuseStep 27378445 = 10266917) B10266917
theorem B2368507 : Blo 1403521 2368507 := bstep (se 1 (by rfl) ⟨1776380, by rfl⟩ : syracuseStep 2368507 = 3552761) B3552761
theorem B2106431 : Blo 1403521 2106431 := bstep (se 1 (by rfl) ⟨1579823, by rfl⟩ : syracuseStep 2106431 = 3159647) B3159647
theorem B2106473 : Blo 1403521 2106473 := bstep (se 2 (by rfl) ⟨789927, by rfl⟩ : syracuseStep 2106473 = 1579855) B1579855
theorem B3556457 : Blo 1403521 3556457 := bstep (se 2 (by rfl) ⟨1333671, by rfl⟩ : syracuseStep 3556457 = 2667343) B2667343
theorem B2106575 : Blo 1403521 2106575 := bstep (se 1 (by rfl) ⟨1579931, by rfl⟩ : syracuseStep 2106575 = 3159863) B3159863
theorem B38446435 : Blo 1403521 38446435 := bstep (se 1 (by rfl) ⟨28834826, by rfl⟩ : syracuseStep 38446435 = 57669653) B57669653
theorem B2106779 : Blo 1403521 2106779 := bstep (se 1 (by rfl) ⟨1580084, by rfl⟩ : syracuseStep 2106779 = 3160169) B3160169
theorem B2368939 : Blo 1403521 2368939 := bstep (se 1 (by rfl) ⟨1776704, by rfl⟩ : syracuseStep 2368939 = 3553409) B3553409
theorem B25642493 : Blo 1403521 25642493 := bstep (se 3 (by rfl) ⟨4807967, by rfl⟩ : syracuseStep 25642493 = 9615935) B9615935
theorem B2369135 : Blo 1403521 2369135 := bstep (se 1 (by rfl) ⟨1776851, by rfl⟩ : syracuseStep 2369135 = 3553703) B3553703
theorem B7997039 : Blo 1403521 7997039 := bstep (se 1 (by rfl) ⟨5997779, by rfl⟩ : syracuseStep 7997039 = 11995559) B11995559
theorem B2107001 : Blo 1403521 2107001 := bstep (se 2 (by rfl) ⟨790125, by rfl⟩ : syracuseStep 2107001 = 1580251) B1580251
theorem B13493927 : Blo 1403521 13493927 := bstep (se 1 (by rfl) ⟨10120445, by rfl⟩ : syracuseStep 13493927 = 20240891) B20240891
theorem B2369243 : Blo 1403521 2369243 := bstep (se 1 (by rfl) ⟨1776932, by rfl⟩ : syracuseStep 2369243 = 3553865) B3553865
theorem B2107103 : Blo 1403521 2107103 := bstep (se 1 (by rfl) ⟨1580327, by rfl⟩ : syracuseStep 2107103 = 3160655) B3160655
theorem B7202591 : Blo 1403521 7202591 := bstep (se 1 (by rfl) ⟨5401943, by rfl⟩ : syracuseStep 7202591 = 10803887) B10803887
theorem B2107199 : Blo 1403521 2107199 := bstep (se 1 (by rfl) ⟨1580399, by rfl⟩ : syracuseStep 2107199 = 3160799) B3160799
theorem B4499297 : Blo 1403521 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B7997291 : Blo 1403521 7997291 := bstep (se 1 (by rfl) ⟨5997968, by rfl⟩ : syracuseStep 7997291 = 11995937) B11995937
theorem B2369479 : Blo 1403521 2369479 := bstep (se 1 (by rfl) ⟨1777109, by rfl⟩ : syracuseStep 2369479 = 3554219) B3554219
theorem B2107367 : Blo 1403521 2107367 := bstep (se 1 (by rfl) ⟨1580525, by rfl⟩ : syracuseStep 2107367 = 3161051) B3161051
theorem B2107385 : Blo 1403521 2107385 := bstep (se 2 (by rfl) ⟨790269, by rfl⟩ : syracuseStep 2107385 = 1580539) B1580539
theorem B2107487 : Blo 1403521 2107487 := bstep (se 1 (by rfl) ⟨1580615, by rfl⟩ : syracuseStep 2107487 = 3161231) B3161231
theorem B4737149 : Blo 1403521 4737149 := bstep (se 3 (by rfl) ⟨888215, by rfl⟩ : syracuseStep 4737149 = 1776431) B1776431
theorem B2107547 : Blo 1403521 2107547 := bstep (se 1 (by rfl) ⟨1580660, by rfl⟩ : syracuseStep 2107547 = 3161321) B3161321
theorem B2107583 : Blo 1403521 2107583 := bstep (se 1 (by rfl) ⟨1580687, by rfl⟩ : syracuseStep 2107583 = 3161375) B3161375
theorem B3999955 : Blo 1403521 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B3557591 : Blo 1403521 3557591 := bstep (se 1 (by rfl) ⟨2668193, by rfl⟩ : syracuseStep 3557591 = 5336387) B5336387
theorem B2107625 : Blo 1403521 2107625 := bstep (se 2 (by rfl) ⟨790359, by rfl⟩ : syracuseStep 2107625 = 1580719) B1580719
theorem B4737419 : Blo 1403521 4737419 := bstep (se 1 (by rfl) ⟨3553064, by rfl⟩ : syracuseStep 4737419 = 7106129) B7106129
theorem B145992077 : Blo 1403521 145992077 := bstep (se 3 (by rfl) ⟨27373514, by rfl⟩ : syracuseStep 145992077 = 54747029) B54747029
theorem B4499975 : Blo 1403521 4499975 := bstep (se 1 (by rfl) ⟨3374981, by rfl⟩ : syracuseStep 4499975 = 6749963) B6749963
theorem B2107931 : Blo 1403521 2107931 := bstep (se 1 (by rfl) ⟨1580948, by rfl⟩ : syracuseStep 2107931 = 3161897) B3161897
theorem B2108009 : Blo 1403521 2108009 := bstep (se 2 (by rfl) ⟨790503, by rfl⟩ : syracuseStep 2108009 = 1581007) B1581007
theorem B2370235 : Blo 1403521 2370235 := bstep (se 1 (by rfl) ⟨1777676, by rfl⟩ : syracuseStep 2370235 = 3555353) B3555353
theorem B46181137 : Blo 1403521 46181137 := bstep (se 2 (by rfl) ⟨17317926, by rfl⟩ : syracuseStep 46181137 = 34635853) B34635853
theorem B1403739 : Blo 1403521 1403739 := bstep (se 1 (by rfl) ⟨1052804, by rfl⟩ : syracuseStep 1403739 = 2105609) B2105609
theorem B1403807 : Blo 1403521 1403807 := bstep (se 1 (by rfl) ⟨1052855, by rfl⟩ : syracuseStep 1403807 = 2105711) B2105711
theorem B3795947 : Blo 1403521 3795947 := bstep (se 1 (by rfl) ⟨2846960, by rfl⟩ : syracuseStep 3795947 = 5693921) B5693921
theorem B2370539 : Blo 1403521 2370539 := bstep (se 1 (by rfl) ⟨1777904, by rfl⟩ : syracuseStep 2370539 = 3555809) B3555809
theorem B7998497 : Blo 1403521 7998497 := bstep (se 2 (by rfl) ⟨2999436, by rfl⟩ : syracuseStep 7998497 = 5998873) B5998873
theorem B1403951 : Blo 1403521 1403951 := bstep (se 1 (by rfl) ⟨1052963, by rfl⟩ : syracuseStep 1403951 = 2105927) B2105927
theorem B1403975 : Blo 1403521 1403975 := bstep (se 1 (by rfl) ⟨1052981, by rfl⟩ : syracuseStep 1403975 = 2105963) B2105963
theorem B4000889 : Blo 1403521 4000889 := bstep (se 2 (by rfl) ⟨1500333, by rfl⟩ : syracuseStep 4000889 = 3000667) B3000667
theorem B1404127 : Blo 1403521 1404127 := bstep (se 1 (by rfl) ⟨1053095, by rfl⟩ : syracuseStep 1404127 = 2106191) B2106191
theorem B19221791 : Blo 1403521 19221791 := bstep (se 1 (by rfl) ⟨14416343, by rfl⟩ : syracuseStep 19221791 = 28832687) B28832687
theorem B1404391 : Blo 1403521 1404391 := bstep (se 1 (by rfl) ⟨1053293, by rfl⟩ : syracuseStep 1404391 = 2106587) B2106587
theorem B7597601 : Blo 1403521 7597601 := bstep (se 2 (by rfl) ⟨2849100, by rfl⟩ : syracuseStep 7597601 = 5698201) B5698201
theorem B1404507 : Blo 1403521 1404507 := bstep (se 1 (by rfl) ⟨1053380, by rfl⟩ : syracuseStep 1404507 = 2106761) B2106761
theorem B48672353 : Blo 1403521 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B13504157 : Blo 1403521 13504157 := bstep (se 3 (by rfl) ⟨2532029, by rfl⟩ : syracuseStep 13504157 = 5064059) B5064059
theorem B1601351 : Blo 1403521 1601351 := bstep (se 1 (by rfl) ⟨1201013, by rfl⟩ : syracuseStep 1601351 = 2402027) B2402027
theorem B1404743 : Blo 1403521 1404743 := bstep (se 1 (by rfl) ⟨1053557, by rfl⟩ : syracuseStep 1404743 = 2107115) B2107115
theorem B4739039 : Blo 1403521 4739039 := bstep (se 1 (by rfl) ⟨3554279, by rfl⟩ : syracuseStep 4739039 = 7108559) B7108559
theorem B4272095 : Blo 1403521 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B1404895 : Blo 1403521 1404895 := bstep (se 1 (by rfl) ⟨1053671, by rfl⟩ : syracuseStep 1404895 = 2107343) B2107343
theorem B10121345 : Blo 1403521 10121345 := bstep (se 2 (by rfl) ⟨3795504, by rfl⟩ : syracuseStep 10121345 = 7591009) B7591009
theorem B4739201 : Blo 1403521 4739201 := bstep (se 2 (by rfl) ⟨1777200, by rfl⟩ : syracuseStep 4739201 = 3554401) B3554401
theorem B12161177 : Blo 1403521 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B7205053 : Blo 1403521 7205053 := bstep (se 3 (by rfl) ⟨1350947, by rfl⟩ : syracuseStep 7205053 = 2701895) B2701895
theorem B1405159 : Blo 1403521 1405159 := bstep (se 1 (by rfl) ⟨1053869, by rfl⟩ : syracuseStep 1405159 = 2107739) B2107739
theorem B4501757 : Blo 1403521 4501757 := bstep (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) B1688159
theorem B1405311 : Blo 1403521 1405311 := bstep (se 1 (by rfl) ⟨1053983, by rfl⟩ : syracuseStep 1405311 = 2107967) B2107967
theorem B4051367 : Blo 1403521 4051367 := bstep (se 1 (by rfl) ⟨3038525, by rfl⟩ : syracuseStep 4051367 = 6077051) B6077051
theorem B4870567 : Blo 1403521 4870567 := bstep (se 1 (by rfl) ⟨3652925, by rfl⟩ : syracuseStep 4870567 = 7305851) B7305851
theorem B1405391 : Blo 1403521 1405391 := bstep (se 1 (by rfl) ⟨1054043, by rfl⟩ : syracuseStep 1405391 = 2108087) B2108087
theorem B2667001 : Blo 1403521 2667001 := bstep (se 2 (by rfl) ⟨1000125, by rfl⟩ : syracuseStep 2667001 = 2000251) B2000251
theorem B10818049 : Blo 1403521 10818049 := bstep (se 2 (by rfl) ⟨4056768, by rfl⟩ : syracuseStep 10818049 = 8113537) B8113537
theorem B4739687 : Blo 1403521 4739687 := bstep (se 1 (by rfl) ⟨3554765, by rfl⟩ : syracuseStep 4739687 = 7109531) B7109531
theorem B2667305 : Blo 1403521 2667305 := bstep (se 2 (by rfl) ⟨1000239, by rfl⟩ : syracuseStep 2667305 = 2000479) B2000479
theorem B8999747 : Blo 1403521 8999747 := bstep (se 1 (by rfl) ⟨6749810, by rfl⟩ : syracuseStep 8999747 = 13499621) B13499621
theorem B4740011 : Blo 1403521 4740011 := bstep (se 1 (by rfl) ⟨3555008, by rfl⟩ : syracuseStep 4740011 = 7110017) B7110017
theorem B3159035 : Blo 1403521 3159035 := bstep (se 1 (by rfl) ⟨2369276, by rfl⟩ : syracuseStep 3159035 = 4738553) B4738553
theorem B2249783 : Blo 1403521 2249783 := bstep (se 1 (by rfl) ⟨1687337, by rfl⟩ : syracuseStep 2249783 = 3374675) B3374675
theorem B2667593 : Blo 1403521 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B3159215 : Blo 1403521 3159215 := bstep (se 1 (by rfl) ⟨2369411, by rfl⟩ : syracuseStep 3159215 = 4738823) B4738823
theorem B3159251 : Blo 1403521 3159251 := bstep (se 1 (by rfl) ⟨2369438, by rfl⟩ : syracuseStep 3159251 = 4738877) B4738877
theorem B3421459 : Blo 1403521 3421459 := bstep (se 1 (by rfl) ⟨2566094, by rfl⟩ : syracuseStep 3421459 = 5132189) B5132189
theorem B4740443 : Blo 1403521 4740443 := bstep (se 1 (by rfl) ⟨3555332, by rfl⟩ : syracuseStep 4740443 = 7110665) B7110665
theorem B4740551 : Blo 1403521 4740551 := bstep (se 1 (by rfl) ⟨3555413, by rfl⟩ : syracuseStep 4740551 = 7110827) B7110827
theorem B1199019469 : Blo 1403521 1199019469 := bstep (se 3 (by rfl) ⟨224816150, by rfl⟩ : syracuseStep 1199019469 = 449632301) B449632301
theorem B3159521 : Blo 1403521 3159521 := bstep (se 2 (by rfl) ⟨1184820, by rfl⟩ : syracuseStep 3159521 = 2369641) B2369641
theorem B12817889 : Blo 1403521 12817889 := bstep (se 2 (by rfl) ⟨4806708, by rfl⟩ : syracuseStep 12817889 = 9613417) B9613417
theorem B15988427 : Blo 1403521 15988427 := bstep (se 1 (by rfl) ⟨11991320, by rfl⟩ : syracuseStep 15988427 = 23982641) B23982641
theorem B4740875 : Blo 1403521 4740875 := bstep (se 1 (by rfl) ⟨3555656, by rfl⟩ : syracuseStep 4740875 = 7111313) B7111313
theorem B17987345 : Blo 1403521 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B18233225 : Blo 1403521 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B1578991 : Blo 1403521 1578991 := bstep (se 1 (by rfl) ⟨1184243, by rfl⟩ : syracuseStep 1578991 = 2368487) B2368487
theorem B4741145 : Blo 1403521 4741145 := bstep (se 2 (by rfl) ⟨1777929, by rfl⟩ : syracuseStep 4741145 = 3555859) B3555859
theorem B8001665 : Blo 1403521 8001665 := bstep (se 2 (by rfl) ⟨3000624, by rfl⟩ : syracuseStep 8001665 = 6001249) B6001249
theorem B15997175 : Blo 1403521 15997175 := bstep (se 1 (by rfl) ⟨11997881, by rfl⟩ : syracuseStep 15997175 = 23995763) B23995763
theorem B4806985 : Blo 1403521 4806985 := bstep (se 2 (by rfl) ⟨1802619, by rfl⟩ : syracuseStep 4806985 = 3605239) B3605239
theorem B41613749 : Blo 1403521 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B2251295 : Blo 1403521 2251295 := bstep (se 1 (by rfl) ⟨1688471, by rfl⟩ : syracuseStep 2251295 = 3376943) B3376943
theorem B14604889 : Blo 1403521 14604889 := bstep (se 2 (by rfl) ⟨5476833, by rfl⟩ : syracuseStep 14604889 = 10953667) B10953667
theorem B7805537 : Blo 1403521 7805537 := bstep (se 2 (by rfl) ⟨2927076, by rfl⟩ : syracuseStep 7805537 = 5854153) B5854153
theorem B9615995 : Blo 1403521 9615995 := bstep (se 1 (by rfl) ⟨7211996, by rfl⟩ : syracuseStep 9615995 = 14423993) B14423993
theorem B2136923 : Blo 1403521 2136923 := bstep (se 1 (by rfl) ⟨1602692, by rfl⟩ : syracuseStep 2136923 = 3205385) B3205385
theorem B30358567 : Blo 1403521 30358567 := bstep (se 1 (by rfl) ⟨22768925, by rfl⟩ : syracuseStep 30358567 = 45537851) B45537851
theorem B3161159 : Blo 1403521 3161159 := bstep (se 1 (by rfl) ⟨2370869, by rfl⟩ : syracuseStep 3161159 = 4741739) B4741739
theorem B4496735 : Blo 1403521 4496735 := bstep (se 1 (by rfl) ⟨3372551, by rfl⟩ : syracuseStep 4496735 = 6745103) B6745103
theorem B4742495 : Blo 1403521 4742495 := bstep (se 1 (by rfl) ⟨3556871, by rfl⟩ : syracuseStep 4742495 = 7113743) B7113743
theorem B3997039 : Blo 1403521 3997039 := bstep (se 1 (by rfl) ⟨2997779, by rfl⟩ : syracuseStep 3997039 = 5995559) B5995559
theorem B18005435 : Blo 1403521 18005435 := bstep (se 1 (by rfl) ⟨13504076, by rfl⟩ : syracuseStep 18005435 = 27008153) B27008153
theorem B3161555 : Blo 1403521 3161555 := bstep (se 1 (by rfl) ⟨2371166, by rfl⟩ : syracuseStep 3161555 = 4742333) B4742333
theorem B8994311 : Blo 1403521 8994311 := bstep (se 1 (by rfl) ⟨6745733, by rfl⟩ : syracuseStep 8994311 = 13491467) B13491467
theorem B41033405 : Blo 1403521 41033405 := bstep (se 3 (by rfl) ⟨7693763, by rfl⟩ : syracuseStep 41033405 = 15387527) B15387527
theorem B2997985 : Blo 1403521 2997985 := bstep (se 2 (by rfl) ⟨1124244, by rfl⟩ : syracuseStep 2997985 = 2248489) B2248489
theorem B3161825 : Blo 1403521 3161825 := bstep (se 2 (by rfl) ⟨1185684, by rfl⟩ : syracuseStep 3161825 = 2371369) B2371369
theorem B3555049 : Blo 1403521 3555049 := bstep (se 2 (by rfl) ⟨1333143, by rfl⟩ : syracuseStep 3555049 = 2666287) B2666287
theorem B1998713 : Blo 1403521 1998713 := bstep (se 2 (by rfl) ⟨749517, by rfl⟩ : syracuseStep 1998713 = 1499035) B1499035
theorem B4743035 : Blo 1403521 4743035 := bstep (se 1 (by rfl) ⟨3557276, by rfl⟩ : syracuseStep 4743035 = 7114553) B7114553
theorem B7995307 : Blo 1403521 7995307 := bstep (se 1 (by rfl) ⟨5996480, by rfl⟩ : syracuseStep 7995307 = 11992961) B11992961
theorem B3162347 : Blo 1403521 3162347 := bstep (se 1 (by rfl) ⟨2371760, by rfl⟩ : syracuseStep 3162347 = 4743521) B4743521
theorem B5333273 : Blo 1403521 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B1778203 : Blo 1403521 1778203 := bstep (se 1 (by rfl) ⟨1333652, by rfl⟩ : syracuseStep 1778203 = 2667305) B2667305
theorem B3556001 : Blo 1403521 3556001 := bstep (se 2 (by rfl) ⟨1333500, by rfl⟩ : syracuseStep 3556001 = 2667001) B2667001
theorem B2106023 : Blo 1403521 2106023 := bstep (se 1 (by rfl) ⟨1579517, by rfl⟩ : syracuseStep 2106023 = 3159035) B3159035
theorem B1499855 : Blo 1403521 1499855 := bstep (se 1 (by rfl) ⟨1124891, by rfl⟩ : syracuseStep 1499855 = 2249783) B2249783
theorem B51258109 : Blo 1403521 51258109 := bstep (se 3 (by rfl) ⟨9610895, by rfl⟩ : syracuseStep 51258109 = 19221791) B19221791
theorem B2106143 : Blo 1403521 2106143 := bstep (se 1 (by rfl) ⟨1579607, by rfl⟩ : syracuseStep 2106143 = 3159215) B3159215
theorem B19473185 : Blo 1403521 19473185 := bstep (se 2 (by rfl) ⟨7302444, by rfl⟩ : syracuseStep 19473185 = 14604889) B14604889
theorem B2106167 : Blo 1403521 2106167 := bstep (se 1 (by rfl) ⟨1579625, by rfl⟩ : syracuseStep 2106167 = 3159251) B3159251
theorem B2106347 : Blo 1403521 2106347 := bstep (se 1 (by rfl) ⟨1579760, by rfl⟩ : syracuseStep 2106347 = 3159521) B3159521
theorem B8545259 : Blo 1403521 8545259 := bstep (se 1 (by rfl) ⟨6408944, by rfl⟩ : syracuseStep 8545259 = 12817889) B12817889
theorem B36504593 : Blo 1403521 36504593 := bstep (se 2 (by rfl) ⟨13689222, by rfl⟩ : syracuseStep 36504593 = 27378445) B27378445
theorem B8995951 : Blo 1403521 8995951 := bstep (se 1 (by rfl) ⟨6746963, by rfl⟩ : syracuseStep 8995951 = 13493927) B13493927
theorem B10658951 : Blo 1403521 10658951 := bstep (se 1 (by rfl) ⟨7994213, by rfl⟩ : syracuseStep 10658951 = 15988427) B15988427
theorem B4801727 : Blo 1403521 4801727 := bstep (se 1 (by rfl) ⟨3601295, by rfl⟩ : syracuseStep 4801727 = 7202591) B7202591
theorem B2999531 : Blo 1403521 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B40478089 : Blo 1403521 40478089 := bstep (se 2 (by rfl) ⟨15179283, by rfl⟩ : syracuseStep 40478089 = 30358567) B30358567
theorem B5334443 : Blo 1403521 5334443 := bstep (se 1 (by rfl) ⟨4000832, by rfl⟩ : syracuseStep 5334443 = 8001665) B8001665
theorem B1500863 : Blo 1403521 1500863 := bstep (se 1 (by rfl) ⟨1125647, by rfl⟩ : syracuseStep 1500863 = 2251295) B2251295
theorem B5203691 : Blo 1403521 5203691 := bstep (se 1 (by rfl) ⟨3902768, by rfl⟩ : syracuseStep 5203691 = 7805537) B7805537
theorem B109422413 : Blo 1403521 109422413 := bstep (se 3 (by rfl) ⟨20516702, by rfl⟩ : syracuseStep 109422413 = 41033405) B41033405
theorem B2107439 : Blo 1403521 2107439 := bstep (se 1 (by rfl) ⟨1580579, by rfl⟩ : syracuseStep 2107439 = 3161159) B3161159
theorem B12003623 : Blo 1403521 12003623 := bstep (se 1 (by rfl) ⟨9002717, by rfl⟩ : syracuseStep 12003623 = 18005435) B18005435
theorem B2107703 : Blo 1403521 2107703 := bstep (se 1 (by rfl) ⟨1580777, by rfl⟩ : syracuseStep 2107703 = 3161555) B3161555
theorem B5065067 : Blo 1403521 5065067 := bstep (se 1 (by rfl) ⟨3798800, by rfl⟩ : syracuseStep 5065067 = 7597601) B7597601
theorem B2107883 : Blo 1403521 2107883 := bstep (se 1 (by rfl) ⟨1580912, by rfl⟩ : syracuseStep 2107883 = 3161825) B3161825
theorem B10660409 : Blo 1403521 10660409 := bstep (se 2 (by rfl) ⟨3997653, by rfl⟩ : syracuseStep 10660409 = 7995307) B7995307
theorem B7113581 : Blo 1403521 7113581 := bstep (se 3 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 7113581 = 2667593) B2667593
theorem B68324309 : Blo 1403521 68324309 := bstep (se 7 (by rfl) ⟨800675, by rfl⟩ : syracuseStep 68324309 = 1601351) B1601351
theorem B1403871 : Blo 1403521 1403871 := bstep (se 1 (by rfl) ⟨1052903, by rfl⟩ : syracuseStep 1403871 = 2105807) B2105807
theorem B1403899 : Blo 1403521 1403899 := bstep (se 1 (by rfl) ⟨1052924, by rfl⟩ : syracuseStep 1403899 = 2105849) B2105849
theorem B1403967 : Blo 1403521 1403967 := bstep (se 1 (by rfl) ⟨1052975, by rfl⟩ : syracuseStep 1403967 = 2105951) B2105951
theorem B2665543 : Blo 1403521 2665543 := bstep (se 1 (by rfl) ⟨1999157, by rfl⟩ : syracuseStep 2665543 = 3998315) B3998315
theorem B6409313 : Blo 1403521 6409313 := bstep (se 2 (by rfl) ⟨2403492, by rfl⟩ : syracuseStep 6409313 = 4806985) B4806985
theorem B5999831 : Blo 1403521 5999831 := bstep (se 1 (by rfl) ⟨4499873, by rfl⟩ : syracuseStep 5999831 = 8999747) B8999747
theorem B12004685 : Blo 1403521 12004685 := bstep (se 3 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 12004685 = 4501757) B4501757
theorem B1404287 : Blo 1403521 1404287 := bstep (se 1 (by rfl) ⟨1053215, by rfl⟩ : syracuseStep 1404287 = 2106431) B2106431
theorem B1404315 : Blo 1403521 1404315 := bstep (se 1 (by rfl) ⟨1053236, by rfl⟩ : syracuseStep 1404315 = 2106473) B2106473
theorem B2370971 : Blo 1403521 2370971 := bstep (se 1 (by rfl) ⟨1778228, by rfl⟩ : syracuseStep 2370971 = 3556457) B3556457
theorem B1404383 : Blo 1403521 1404383 := bstep (se 1 (by rfl) ⟨1053287, by rfl⟩ : syracuseStep 1404383 = 2106575) B2106575
theorem B1404519 : Blo 1403521 1404519 := bstep (se 1 (by rfl) ⟨1053389, by rfl⟩ : syracuseStep 1404519 = 2106779) B2106779
theorem B61574849 : Blo 1403521 61574849 := bstep (se 2 (by rfl) ⟨23090568, by rfl⟩ : syracuseStep 61574849 = 46181137) B46181137
theorem B1404667 : Blo 1403521 1404667 := bstep (se 1 (by rfl) ⟨1053500, by rfl⟩ : syracuseStep 1404667 = 2107001) B2107001
theorem B1404735 : Blo 1403521 1404735 := bstep (se 1 (by rfl) ⟨1053551, by rfl⟩ : syracuseStep 1404735 = 2107103) B2107103
theorem B1404799 : Blo 1403521 1404799 := bstep (se 1 (by rfl) ⟨1053599, by rfl⟩ : syracuseStep 1404799 = 2107199) B2107199
theorem B1404911 : Blo 1403521 1404911 := bstep (se 1 (by rfl) ⟨1053683, by rfl⟩ : syracuseStep 1404911 = 2107367) B2107367
theorem B3158009 : Blo 1403521 3158009 := bstep (se 2 (by rfl) ⟨1184253, by rfl⟩ : syracuseStep 3158009 = 2368507) B2368507
theorem B1404923 : Blo 1403521 1404923 := bstep (se 1 (by rfl) ⟨1053692, by rfl⟩ : syracuseStep 1404923 = 2107385) B2107385
theorem B1404991 : Blo 1403521 1404991 := bstep (se 1 (by rfl) ⟨1053743, by rfl⟩ : syracuseStep 1404991 = 2107487) B2107487
theorem B3158099 : Blo 1403521 3158099 := bstep (se 1 (by rfl) ⟨2368574, by rfl⟩ : syracuseStep 3158099 = 4737149) B4737149
theorem B18247781 : Blo 1403521 18247781 := bstep (se 4 (by rfl) ⟨1710729, by rfl⟩ : syracuseStep 18247781 = 3421459) B3421459
theorem B1405031 : Blo 1403521 1405031 := bstep (se 1 (by rfl) ⟨1053773, by rfl⟩ : syracuseStep 1405031 = 2107547) B2107547
theorem B1405055 : Blo 1403521 1405055 := bstep (se 1 (by rfl) ⟨1053791, by rfl⟩ : syracuseStep 1405055 = 2107583) B2107583
theorem B2371727 : Blo 1403521 2371727 := bstep (se 1 (by rfl) ⟨1778795, by rfl⟩ : syracuseStep 2371727 = 3557591) B3557591
theorem B1405083 : Blo 1403521 1405083 := bstep (se 1 (by rfl) ⟨1053812, by rfl⟩ : syracuseStep 1405083 = 2107625) B2107625
theorem B3158279 : Blo 1403521 3158279 := bstep (se 1 (by rfl) ⟨2368709, by rfl⟩ : syracuseStep 3158279 = 4737419) B4737419
theorem B27742499 : Blo 1403521 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B1405287 : Blo 1403521 1405287 := bstep (se 1 (by rfl) ⟨1053965, by rfl⟩ : syracuseStep 1405287 = 2107931) B2107931
theorem B1405339 : Blo 1403521 1405339 := bstep (se 1 (by rfl) ⟨1054004, by rfl⟩ : syracuseStep 1405339 = 2108009) B2108009
theorem B6410663 : Blo 1403521 6410663 := bstep (se 1 (by rfl) ⟨4807997, by rfl⟩ : syracuseStep 6410663 = 9615995) B9615995
theorem B51261913 : Blo 1403521 51261913 := bstep (se 2 (by rfl) ⟨19223217, by rfl⟩ : syracuseStep 51261913 = 38446435) B38446435
theorem B5329385 : Blo 1403521 5329385 := bstep (se 2 (by rfl) ⟨1998519, by rfl⟩ : syracuseStep 5329385 = 3997039) B3997039
theorem B3158585 : Blo 1403521 3158585 := bstep (se 2 (by rfl) ⟨1184469, by rfl⟩ : syracuseStep 3158585 = 2368939) B2368939
theorem B2667259 : Blo 1403521 2667259 := bstep (se 1 (by rfl) ⟨2000444, by rfl⟩ : syracuseStep 2667259 = 4000889) B4000889
theorem B4740065 : Blo 1403521 4740065 := bstep (se 2 (by rfl) ⟨1777524, by rfl⟩ : syracuseStep 4740065 = 3555049) B3555049
theorem B5329901 : Blo 1403521 5329901 := bstep (se 3 (by rfl) ⟨999356, by rfl⟩ : syracuseStep 5329901 = 1998713) B1998713
theorem B3159305 : Blo 1403521 3159305 := bstep (se 2 (by rfl) ⟨1184739, by rfl⟩ : syracuseStep 3159305 = 2369479) B2369479
theorem B3159359 : Blo 1403521 3159359 := bstep (se 1 (by rfl) ⟨2369519, by rfl⟩ : syracuseStep 3159359 = 4739039) B4739039
theorem B2848063 : Blo 1403521 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B6747563 : Blo 1403521 6747563 := bstep (se 1 (by rfl) ⟨5060672, by rfl⟩ : syracuseStep 6747563 = 10121345) B10121345
theorem B3159467 : Blo 1403521 3159467 := bstep (se 1 (by rfl) ⟨2369600, by rfl⟩ : syracuseStep 3159467 = 4739201) B4739201
theorem B8107451 : Blo 1403521 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B9606737 : Blo 1403521 9606737 := bstep (se 2 (by rfl) ⟨3602526, by rfl⟩ : syracuseStep 9606737 = 7205053) B7205053
theorem B2700911 : Blo 1403521 2700911 := bstep (se 1 (by rfl) ⟨2025683, by rfl⟩ : syracuseStep 2700911 = 4051367) B4051367
theorem B5330569 : Blo 1403521 5330569 := bstep (se 2 (by rfl) ⟨1998963, by rfl⟩ : syracuseStep 5330569 = 3997927) B3997927
theorem B3159791 : Blo 1403521 3159791 := bstep (se 1 (by rfl) ⟨2369843, by rfl⟩ : syracuseStep 3159791 = 4739687) B4739687
theorem B5691131 : Blo 1403521 5691131 := bstep (se 1 (by rfl) ⟨4268348, by rfl⟩ : syracuseStep 5691131 = 8536697) B8536697
theorem B6002495 : Blo 1403521 6002495 := bstep (se 1 (by rfl) ⟨4501871, by rfl⟩ : syracuseStep 6002495 = 9003743) B9003743
theorem B6494089 : Blo 1403521 6494089 := bstep (se 2 (by rfl) ⟨2435283, by rfl⟩ : syracuseStep 6494089 = 4870567) B4870567
theorem B3160007 : Blo 1403521 3160007 := bstep (se 1 (by rfl) ⟨2370005, by rfl⟩ : syracuseStep 3160007 = 4740011) B4740011
theorem B14424065 : Blo 1403521 14424065 := bstep (se 2 (by rfl) ⟨5409024, by rfl⟩ : syracuseStep 14424065 = 10818049) B10818049
theorem B5331041 : Blo 1403521 5331041 := bstep (se 2 (by rfl) ⟨1999140, by rfl⟩ : syracuseStep 5331041 = 3998281) B3998281
theorem B3160295 : Blo 1403521 3160295 := bstep (se 1 (by rfl) ⟨2370221, by rfl⟩ : syracuseStep 3160295 = 4740443) B4740443
theorem B3160313 : Blo 1403521 3160313 := bstep (se 2 (by rfl) ⟨1185117, by rfl⟩ : syracuseStep 3160313 = 2370235) B2370235
theorem B3160367 : Blo 1403521 3160367 := bstep (se 1 (by rfl) ⟨2370275, by rfl⟩ : syracuseStep 3160367 = 4740551) B4740551
theorem B4053305 : Blo 1403521 4053305 := bstep (se 2 (by rfl) ⟨1519989, by rfl⟩ : syracuseStep 4053305 = 3039979) B3039979
theorem B17094995 : Blo 1403521 17094995 := bstep (se 1 (by rfl) ⟨12821246, by rfl⟩ : syracuseStep 17094995 = 25642493) B25642493
theorem B1579423 : Blo 1403521 1579423 := bstep (se 1 (by rfl) ⟨1184567, by rfl⟩ : syracuseStep 1579423 = 2369135) B2369135
theorem B5331359 : Blo 1403521 5331359 := bstep (se 1 (by rfl) ⟨3998519, by rfl⟩ : syracuseStep 5331359 = 7997039) B7997039
theorem B1579495 : Blo 1403521 1579495 := bstep (se 1 (by rfl) ⟨1184621, by rfl⟩ : syracuseStep 1579495 = 2369243) B2369243
theorem B3160583 : Blo 1403521 3160583 := bstep (se 1 (by rfl) ⟨2370437, by rfl⟩ : syracuseStep 3160583 = 4740875) B4740875
theorem B11991563 : Blo 1403521 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B5331527 : Blo 1403521 5331527 := bstep (se 1 (by rfl) ⟨3998645, by rfl⟩ : syracuseStep 5331527 = 7997291) B7997291
theorem B12155483 : Blo 1403521 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B3160763 : Blo 1403521 3160763 := bstep (se 1 (by rfl) ⟨2370572, by rfl⟩ : syracuseStep 3160763 = 4741145) B4741145
theorem B11999933 : Blo 1403521 11999933 := bstep (se 3 (by rfl) ⟨2249987, by rfl⟩ : syracuseStep 11999933 = 4499975) B4499975
theorem B10664783 : Blo 1403521 10664783 := bstep (se 1 (by rfl) ⟨7998587, by rfl⟩ : syracuseStep 10664783 = 15997175) B15997175
theorem B97328051 : Blo 1403521 97328051 := bstep (se 1 (by rfl) ⟨72996038, by rfl⟩ : syracuseStep 97328051 = 145992077) B145992077
theorem B1424615 : Blo 1403521 1424615 := bstep (se 1 (by rfl) ⟨1068461, by rfl⟩ : syracuseStep 1424615 = 2136923) B2136923
theorem B1598692625 : Blo 1403521 1598692625 := bstep (se 2 (by rfl) ⟨599509734, by rfl⟩ : syracuseStep 1598692625 = 1199019469) B1199019469
theorem B2530631 : Blo 1403521 2530631 := bstep (se 1 (by rfl) ⟨1897973, by rfl⟩ : syracuseStep 2530631 = 3795947) B3795947
theorem B1580359 : Blo 1403521 1580359 := bstep (se 1 (by rfl) ⟨1185269, by rfl⟩ : syracuseStep 1580359 = 2370539) B2370539
theorem B5332331 : Blo 1403521 5332331 := bstep (se 1 (by rfl) ⟨3999248, by rfl⟩ : syracuseStep 5332331 = 7998497) B7998497
theorem B2997823 : Blo 1403521 2997823 := bstep (se 1 (by rfl) ⟨2248367, by rfl⟩ : syracuseStep 2997823 = 4496735) B4496735
theorem B3161663 : Blo 1403521 3161663 := bstep (se 1 (by rfl) ⟨2371247, by rfl⟩ : syracuseStep 3161663 = 4742495) B4742495
theorem B3997313 : Blo 1403521 3997313 := bstep (se 2 (by rfl) ⟨1498992, by rfl⟩ : syracuseStep 3997313 = 2997985) B2997985
theorem B5996207 : Blo 1403521 5996207 := bstep (se 1 (by rfl) ⟨4497155, by rfl⟩ : syracuseStep 5996207 = 8994311) B8994311
theorem B32448235 : Blo 1403521 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B9002771 : Blo 1403521 9002771 := bstep (se 1 (by rfl) ⟨6752078, by rfl⟩ : syracuseStep 9002771 = 13504157) B13504157
theorem B3162023 : Blo 1403521 3162023 := bstep (se 1 (by rfl) ⟨2371517, by rfl⟩ : syracuseStep 3162023 = 4743035) B4743035
theorem B2105321 : Blo 1403521 2105321 := bstep (se 2 (by rfl) ⟨789495, by rfl⟩ : syracuseStep 2105321 = 1578991) B1578991
theorem B2105399 : Blo 1403521 2105399 := bstep (se 1 (by rfl) ⟨1579049, by rfl⟩ : syracuseStep 2105399 = 3158099) B3158099
theorem B12165187 : Blo 1403521 12165187 := bstep (se 1 (by rfl) ⟨9123890, by rfl⟩ : syracuseStep 12165187 = 18247781) B18247781
theorem B1581151 : Blo 1403521 1581151 := bstep (se 1 (by rfl) ⟨1185863, by rfl⟩ : syracuseStep 1581151 = 2371727) B2371727
theorem B2105519 : Blo 1403521 2105519 := bstep (se 1 (by rfl) ⟨1579139, by rfl⟩ : syracuseStep 2105519 = 3158279) B3158279
theorem B3555515 : Blo 1403521 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B2105723 : Blo 1403521 2105723 := bstep (se 1 (by rfl) ⟨1579292, by rfl⟩ : syracuseStep 2105723 = 3158585) B3158585
theorem B12804605 : Blo 1403521 12804605 := bstep (se 3 (by rfl) ⟨2400863, by rfl⟩ : syracuseStep 12804605 = 4801727) B4801727
theorem B2105897 : Blo 1403521 2105897 := bstep (se 2 (by rfl) ⟨789711, by rfl⟩ : syracuseStep 2105897 = 1579423) B1579423
theorem B2105993 : Blo 1403521 2105993 := bstep (se 2 (by rfl) ⟨789747, by rfl⟩ : syracuseStep 2105993 = 1579495) B1579495
theorem B2106203 : Blo 1403521 2106203 := bstep (se 1 (by rfl) ⟨1579652, by rfl⟩ : syracuseStep 2106203 = 3159305) B3159305
theorem B2106239 : Blo 1403521 2106239 := bstep (se 1 (by rfl) ⟨1579679, by rfl⟩ : syracuseStep 2106239 = 3159359) B3159359
theorem B4498375 : Blo 1403521 4498375 := bstep (se 1 (by rfl) ⟨3373781, by rfl⟩ : syracuseStep 4498375 = 6747563) B6747563
theorem B2106311 : Blo 1403521 2106311 := bstep (se 1 (by rfl) ⟨1579733, by rfl⟩ : syracuseStep 2106311 = 3159467) B3159467
theorem B3556295 : Blo 1403521 3556295 := bstep (se 1 (by rfl) ⟨2667221, by rfl⟩ : syracuseStep 3556295 = 5334443) B5334443
theorem B3556345 : Blo 1403521 3556345 := bstep (se 2 (by rfl) ⟨1333629, by rfl⟩ : syracuseStep 3556345 = 2667259) B2667259
theorem B2106527 : Blo 1403521 2106527 := bstep (se 1 (by rfl) ⟨1579895, by rfl⟩ : syracuseStep 2106527 = 3159791) B3159791
theorem B3794087 : Blo 1403521 3794087 := bstep (se 1 (by rfl) ⟨2845565, by rfl⟩ : syracuseStep 3794087 = 5691131) B5691131
theorem B2106671 : Blo 1403521 2106671 := bstep (se 1 (by rfl) ⟨1580003, by rfl⟩ : syracuseStep 2106671 = 3160007) B3160007
theorem B11994601 : Blo 1403521 11994601 := bstep (se 2 (by rfl) ⟨4497975, by rfl⟩ : syracuseStep 11994601 = 8995951) B8995951
theorem B2106863 : Blo 1403521 2106863 := bstep (se 1 (by rfl) ⟨1580147, by rfl⟩ : syracuseStep 2106863 = 3160295) B3160295
theorem B2106875 : Blo 1403521 2106875 := bstep (se 1 (by rfl) ⟨1580156, by rfl⟩ : syracuseStep 2106875 = 3160313) B3160313
theorem B2106911 : Blo 1403521 2106911 := bstep (se 1 (by rfl) ⟨1580183, by rfl⟩ : syracuseStep 2106911 = 3160367) B3160367
theorem B11396663 : Blo 1403521 11396663 := bstep (se 1 (by rfl) ⟨8547497, by rfl⟩ : syracuseStep 11396663 = 17094995) B17094995
theorem B3376711 : Blo 1403521 3376711 := bstep (se 1 (by rfl) ⟨2532533, by rfl⟩ : syracuseStep 3376711 = 5065067) B5065067
theorem B7202429 : Blo 1403521 7202429 := bstep (se 3 (by rfl) ⟨1350455, by rfl⟩ : syracuseStep 7202429 = 2700911) B2700911
theorem B2107055 : Blo 1403521 2107055 := bstep (se 1 (by rfl) ⟨1580291, by rfl⟩ : syracuseStep 2107055 = 3160583) B3160583
theorem B8103655 : Blo 1403521 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B2107145 : Blo 1403521 2107145 := bstep (se 2 (by rfl) ⟨790179, by rfl⟩ : syracuseStep 2107145 = 1580359) B1580359
theorem B2107175 : Blo 1403521 2107175 := bstep (se 1 (by rfl) ⟨1580381, by rfl⟩ : syracuseStep 2107175 = 3160763) B3160763
theorem B53970785 : Blo 1403521 53970785 := bstep (se 2 (by rfl) ⟨20239044, by rfl⟩ : syracuseStep 53970785 = 40478089) B40478089
theorem B3999613 : Blo 1403521 3999613 := bstep (se 3 (by rfl) ⟨749927, by rfl⟩ : syracuseStep 3999613 = 1499855) B1499855
theorem B45549539 : Blo 1403521 45549539 := bstep (se 1 (by rfl) ⟨34162154, by rfl⟩ : syracuseStep 45549539 = 68324309) B68324309
theorem B3999887 : Blo 1403521 3999887 := bstep (se 1 (by rfl) ⟨2999915, by rfl⟩ : syracuseStep 3999887 = 5999831) B5999831
theorem B43264313 : Blo 1403521 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B2107775 : Blo 1403521 2107775 := bstep (se 1 (by rfl) ⟨1580831, by rfl⟩ : syracuseStep 2107775 = 3161663) B3161663
theorem B2664875 : Blo 1403521 2664875 := bstep (se 1 (by rfl) ⟨1998656, by rfl⟩ : syracuseStep 2664875 = 3997313) B3997313
theorem B2108015 : Blo 1403521 2108015 := bstep (se 1 (by rfl) ⟨1581011, by rfl⟩ : syracuseStep 2108015 = 3162023) B3162023
theorem B1403547 : Blo 1403521 1403547 := bstep (se 1 (by rfl) ⟨1052660, by rfl⟩ : syracuseStep 1403547 = 2105321) B2105321
theorem B2108231 : Blo 1403521 2108231 := bstep (se 1 (by rfl) ⟨1581173, by rfl⟩ : syracuseStep 2108231 = 3162347) B3162347
theorem B2370667 : Blo 1403521 2370667 := bstep (se 1 (by rfl) ⟨1778000, by rfl⟩ : syracuseStep 2370667 = 3556001) B3556001
theorem B1404015 : Blo 1403521 1404015 := bstep (se 1 (by rfl) ⟨1053011, by rfl⟩ : syracuseStep 1404015 = 2106023) B2106023
theorem B1404095 : Blo 1403521 1404095 := bstep (se 1 (by rfl) ⟨1053071, by rfl⟩ : syracuseStep 1404095 = 2106143) B2106143
theorem B1404111 : Blo 1403521 1404111 := bstep (se 1 (by rfl) ⟨1053083, by rfl⟩ : syracuseStep 1404111 = 2106167) B2106167
theorem B7998749 : Blo 1403521 7998749 := bstep (se 3 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 7998749 = 2999531) B2999531
theorem B68349217 : Blo 1403521 68349217 := bstep (se 2 (by rfl) ⟨25630956, by rfl⟩ : syracuseStep 68349217 = 51261913) B51261913
theorem B1404231 : Blo 1403521 1404231 := bstep (se 1 (by rfl) ⟨1053173, by rfl⟩ : syracuseStep 1404231 = 2106347) B2106347
theorem B5696839 : Blo 1403521 5696839 := bstep (se 1 (by rfl) ⟨4272629, by rfl⟩ : syracuseStep 5696839 = 8545259) B8545259
theorem B2370937 : Blo 1403521 2370937 := bstep (se 2 (by rfl) ⟨889101, by rfl⟩ : syracuseStep 2370937 = 1778203) B1778203
theorem B7105967 : Blo 1403521 7105967 := bstep (se 1 (by rfl) ⟨5329475, by rfl⟩ : syracuseStep 7105967 = 10658951) B10658951
theorem B3469127 : Blo 1403521 3469127 := bstep (se 1 (by rfl) ⟨2601845, by rfl⟩ : syracuseStep 3469127 = 5203691) B5203691
theorem B4001663 : Blo 1403521 4001663 := bstep (se 1 (by rfl) ⟨3001247, by rfl⟩ : syracuseStep 4001663 = 6002495) B6002495
theorem B1404959 : Blo 1403521 1404959 := bstep (se 1 (by rfl) ⟨1053719, by rfl⟩ : syracuseStep 1404959 = 2107439) B2107439
theorem B1405135 : Blo 1403521 1405135 := bstep (se 1 (by rfl) ⟨1053851, by rfl⟩ : syracuseStep 1405135 = 2107703) B2107703
theorem B1405255 : Blo 1403521 1405255 := bstep (se 1 (by rfl) ⟨1053941, by rfl⟩ : syracuseStep 1405255 = 2107883) B2107883
theorem B7106939 : Blo 1403521 7106939 := bstep (se 1 (by rfl) ⟨5330204, by rfl⟩ : syracuseStep 7106939 = 10660409) B10660409
theorem B3797417 : Blo 1403521 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B7999955 : Blo 1403521 7999955 := bstep (se 1 (by rfl) ⟨5999966, by rfl⟩ : syracuseStep 7999955 = 11999933) B11999933
theorem B4002301 : Blo 1403521 4002301 := bstep (se 3 (by rfl) ⟨750431, by rfl⟩ : syracuseStep 4002301 = 1500863) B1500863
theorem B64885367 : Blo 1403521 64885367 := bstep (se 1 (by rfl) ⟨48664025, by rfl⟩ : syracuseStep 64885367 = 97328051) B97328051
theorem B4272875 : Blo 1403521 4272875 := bstep (se 1 (by rfl) ⟨3204656, by rfl⟩ : syracuseStep 4272875 = 6409313) B6409313
theorem B7107425 : Blo 1403521 7107425 := bstep (se 2 (by rfl) ⟨2665284, by rfl⟩ : syracuseStep 7107425 = 5330569) B5330569
theorem B6001847 : Blo 1403521 6001847 := bstep (se 1 (by rfl) ⟨4501385, by rfl⟩ : syracuseStep 6001847 = 9002771) B9002771
theorem B18494999 : Blo 1403521 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B4273775 : Blo 1403521 4273775 := bstep (se 1 (by rfl) ⟨3205331, by rfl⟩ : syracuseStep 4273775 = 6410663) B6410663
theorem B3552923 : Blo 1403521 3552923 := bstep (se 1 (by rfl) ⟨2664692, by rfl⟩ : syracuseStep 3552923 = 5329385) B5329385
theorem B12982123 : Blo 1403521 12982123 := bstep (se 1 (by rfl) ⟨9736592, by rfl⟩ : syracuseStep 12982123 = 19473185) B19473185
theorem B3798973 : Blo 1403521 3798973 := bstep (se 3 (by rfl) ⟨712307, by rfl⟩ : syracuseStep 3798973 = 1424615) B1424615
theorem B3160043 : Blo 1403521 3160043 := bstep (se 1 (by rfl) ⟨2370032, by rfl⟩ : syracuseStep 3160043 = 4740065) B4740065
theorem B3553267 : Blo 1403521 3553267 := bstep (se 1 (by rfl) ⟨2664950, by rfl⟩ : syracuseStep 3553267 = 5329901) B5329901
theorem B24336395 : Blo 1403521 24336395 := bstep (se 1 (by rfl) ⟨18252296, by rfl⟩ : syracuseStep 24336395 = 36504593) B36504593
theorem B5404967 : Blo 1403521 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B68344145 : Blo 1403521 68344145 := bstep (se 2 (by rfl) ⟨25629054, by rfl⟩ : syracuseStep 68344145 = 51258109) B51258109
theorem B6404491 : Blo 1403521 6404491 := bstep (se 1 (by rfl) ⟨4803368, by rfl⟩ : syracuseStep 6404491 = 9606737) B9606737
theorem B72948275 : Blo 1403521 72948275 := bstep (se 1 (by rfl) ⟨54711206, by rfl⟩ : syracuseStep 72948275 = 109422413) B109422413
theorem B9616043 : Blo 1403521 9616043 := bstep (se 1 (by rfl) ⟨7212032, by rfl⟩ : syracuseStep 9616043 = 14424065) B14424065
theorem B3554027 : Blo 1403521 3554027 := bstep (se 1 (by rfl) ⟨2665520, by rfl⟩ : syracuseStep 3554027 = 5331041) B5331041
theorem B3554057 : Blo 1403521 3554057 := bstep (se 2 (by rfl) ⟨1332771, by rfl⟩ : syracuseStep 3554057 = 2665543) B2665543
theorem B8002415 : Blo 1403521 8002415 := bstep (se 1 (by rfl) ⟨6001811, by rfl⟩ : syracuseStep 8002415 = 12003623) B12003623
theorem B2702203 : Blo 1403521 2702203 := bstep (se 1 (by rfl) ⟨2026652, by rfl⟩ : syracuseStep 2702203 = 4053305) B4053305
theorem B3554239 : Blo 1403521 3554239 := bstep (se 1 (by rfl) ⟨2665679, by rfl⟩ : syracuseStep 3554239 = 5331359) B5331359
theorem B7994375 : Blo 1403521 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B3554351 : Blo 1403521 3554351 := bstep (se 1 (by rfl) ⟨2665763, by rfl⟩ : syracuseStep 3554351 = 5331527) B5331527
theorem B15989885 : Blo 1403521 15989885 := bstep (se 3 (by rfl) ⟨2998103, by rfl⟩ : syracuseStep 15989885 = 5996207) B5996207
theorem B7109855 : Blo 1403521 7109855 := bstep (se 1 (by rfl) ⟨5332391, by rfl⟩ : syracuseStep 7109855 = 10664783) B10664783
theorem B4742387 : Blo 1403521 4742387 := bstep (se 1 (by rfl) ⟨3556790, by rfl⟩ : syracuseStep 4742387 = 7113581) B7113581
theorem B3997097 : Blo 1403521 3997097 := bstep (se 2 (by rfl) ⟨1498911, by rfl⟩ : syracuseStep 3997097 = 2997823) B2997823
theorem B1065795083 : Blo 1403521 1065795083 := bstep (se 1 (by rfl) ⟨799346312, by rfl⟩ : syracuseStep 1065795083 = 1598692625) B1598692625
theorem B1687087 : Blo 1403521 1687087 := bstep (se 1 (by rfl) ⟨1265315, by rfl⟩ : syracuseStep 1687087 = 2530631) B2530631
theorem B8003123 : Blo 1403521 8003123 := bstep (se 1 (by rfl) ⟨6002342, by rfl⟩ : syracuseStep 8003123 = 12004685) B12004685
theorem B3554887 : Blo 1403521 3554887 := bstep (se 1 (by rfl) ⟨2666165, by rfl⟩ : syracuseStep 3554887 = 5332331) B5332331
theorem B1580647 : Blo 1403521 1580647 := bstep (se 1 (by rfl) ⟨1185485, by rfl⟩ : syracuseStep 1580647 = 2370971) B2370971
theorem B41049899 : Blo 1403521 41049899 := bstep (se 1 (by rfl) ⟨30787424, by rfl⟩ : syracuseStep 41049899 = 61574849) B61574849
theorem B8658785 : Blo 1403521 8658785 := bstep (se 2 (by rfl) ⟨3247044, by rfl⟩ : syracuseStep 8658785 = 6494089) B6494089
theorem B2105339 : Blo 1403521 2105339 := bstep (se 1 (by rfl) ⟨1579004, by rfl⟩ : syracuseStep 2105339 = 3158009) B3158009
theorem B16220249 : Blo 1403521 16220249 := bstep (se 2 (by rfl) ⟨6082593, by rfl⟩ : syracuseStep 16220249 = 12165187) B12165187
theorem B2531611 : Blo 1403521 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B5333303 : Blo 1403521 5333303 := bstep (se 1 (by rfl) ⟨3999977, by rfl⟩ : syracuseStep 5333303 = 7999955) B7999955
theorem B8536403 : Blo 1403521 8536403 := bstep (se 1 (by rfl) ⟨6402302, by rfl⟩ : syracuseStep 8536403 = 12804605) B12804605
theorem B12329999 : Blo 1403521 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B4801619 : Blo 1403521 4801619 := bstep (se 1 (by rfl) ⟨3601214, by rfl⟩ : syracuseStep 4801619 = 7202429) B7202429
theorem B2368615 : Blo 1403521 2368615 := bstep (se 1 (by rfl) ⟨1776461, by rfl⟩ : syracuseStep 2368615 = 3552923) B3552923
theorem B35980523 : Blo 1403521 35980523 := bstep (se 1 (by rfl) ⟨26985392, by rfl⟩ : syracuseStep 35980523 = 53970785) B53970785
theorem B5997833 : Blo 1403521 5997833 := bstep (se 2 (by rfl) ⟨2249187, by rfl⟩ : syracuseStep 5997833 = 4498375) B4498375
theorem B2106695 : Blo 1403521 2106695 := bstep (se 1 (by rfl) ⟨1580021, by rfl⟩ : syracuseStep 2106695 = 3160043) B3160043
theorem B7595785 : Blo 1403521 7595785 := bstep (se 2 (by rfl) ⟨2848419, by rfl⟩ : syracuseStep 7595785 = 5696839) B5696839
theorem B25642781 : Blo 1403521 25642781 := bstep (se 3 (by rfl) ⟨4808021, by rfl⟩ : syracuseStep 25642781 = 9616043) B9616043
theorem B2369351 : Blo 1403521 2369351 := bstep (se 1 (by rfl) ⟨1777013, by rfl⟩ : syracuseStep 2369351 = 3554027) B3554027
theorem B2369371 : Blo 1403521 2369371 := bstep (se 1 (by rfl) ⟨1777028, by rfl⟩ : syracuseStep 2369371 = 3554057) B3554057
theorem B5334943 : Blo 1403521 5334943 := bstep (se 1 (by rfl) ⟨4001207, by rfl⟩ : syracuseStep 5334943 = 8002415) B8002415
theorem B15992801 : Blo 1403521 15992801 := bstep (se 2 (by rfl) ⟨5997300, by rfl⟩ : syracuseStep 15992801 = 11994601) B11994601
theorem B2369567 : Blo 1403521 2369567 := bstep (se 1 (by rfl) ⟨1777175, by rfl⟩ : syracuseStep 2369567 = 3554351) B3554351
theorem B10659923 : Blo 1403521 10659923 := bstep (se 1 (by rfl) ⟨7994942, by rfl⟩ : syracuseStep 10659923 = 15989885) B15989885
theorem B2107529 : Blo 1403521 2107529 := bstep (se 2 (by rfl) ⟨790323, by rfl⟩ : syracuseStep 2107529 = 1580647) B1580647
theorem B9251005 : Blo 1403521 9251005 := bstep (se 3 (by rfl) ⟨1734563, by rfl⟩ : syracuseStep 9251005 = 3469127) B3469127
theorem B2664731 : Blo 1403521 2664731 := bstep (se 1 (by rfl) ⟨1998548, by rfl⟩ : syracuseStep 2664731 = 3997097) B3997097
theorem B4737311 : Blo 1403521 4737311 := bstep (se 1 (by rfl) ⟨3552983, by rfl⟩ : syracuseStep 4737311 = 7105967) B7105967
theorem B5335415 : Blo 1403521 5335415 := bstep (se 1 (by rfl) ⟨4001561, by rfl⟩ : syracuseStep 5335415 = 8003123) B8003123
theorem B5065297 : Blo 1403521 5065297 := bstep (se 2 (by rfl) ⟨1899486, by rfl⟩ : syracuseStep 5065297 = 3798973) B3798973
theorem B4737689 : Blo 1403521 4737689 := bstep (se 2 (by rfl) ⟨1776633, by rfl⟩ : syracuseStep 4737689 = 3553267) B3553267
theorem B1403559 : Blo 1403521 1403559 := bstep (se 1 (by rfl) ⟨1052669, by rfl⟩ : syracuseStep 1403559 = 2105339) B2105339
theorem B1403599 : Blo 1403521 1403599 := bstep (se 1 (by rfl) ⟨1052699, by rfl⟩ : syracuseStep 1403599 = 2105399) B2105399
theorem B1403679 : Blo 1403521 1403679 := bstep (se 1 (by rfl) ⟨1052759, by rfl⟩ : syracuseStep 1403679 = 2105519) B2105519
theorem B2370343 : Blo 1403521 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B2108201 : Blo 1403521 2108201 := bstep (se 2 (by rfl) ⟨790575, by rfl⟩ : syracuseStep 2108201 = 1581151) B1581151
theorem B8997797 : Blo 1403521 8997797 := bstep (se 4 (by rfl) ⟨843543, by rfl⟩ : syracuseStep 8997797 = 1687087) B1687087
theorem B1403815 : Blo 1403521 1403815 := bstep (se 1 (by rfl) ⟨1052861, by rfl⟩ : syracuseStep 1403815 = 2105723) B2105723
theorem B4737959 : Blo 1403521 4737959 := bstep (se 1 (by rfl) ⟨3553469, by rfl⟩ : syracuseStep 4737959 = 7106939) B7106939
theorem B1403931 : Blo 1403521 1403931 := bstep (se 1 (by rfl) ⟨1052948, by rfl⟩ : syracuseStep 1403931 = 2105897) B2105897
theorem B18009125 : Blo 1403521 18009125 := bstep (se 4 (by rfl) ⟨1688355, by rfl⟩ : syracuseStep 18009125 = 3376711) B3376711
theorem B43256911 : Blo 1403521 43256911 := bstep (se 1 (by rfl) ⟨32442683, by rfl⟩ : syracuseStep 43256911 = 64885367) B64885367
theorem B1403995 : Blo 1403521 1403995 := bstep (se 1 (by rfl) ⟨1052996, by rfl⟩ : syracuseStep 1403995 = 2105993) B2105993
theorem B1404135 : Blo 1403521 1404135 := bstep (se 1 (by rfl) ⟨1053101, by rfl⟩ : syracuseStep 1404135 = 2106203) B2106203
theorem B4738283 : Blo 1403521 4738283 := bstep (se 1 (by rfl) ⟨3553712, by rfl⟩ : syracuseStep 4738283 = 7107425) B7107425
theorem B1404159 : Blo 1403521 1404159 := bstep (se 1 (by rfl) ⟨1053119, by rfl⟩ : syracuseStep 1404159 = 2106239) B2106239
theorem B1404207 : Blo 1403521 1404207 := bstep (se 1 (by rfl) ⟨1053155, by rfl⟩ : syracuseStep 1404207 = 2106311) B2106311
theorem B2370863 : Blo 1403521 2370863 := bstep (se 1 (by rfl) ⟨1778147, by rfl⟩ : syracuseStep 2370863 = 3556295) B3556295
theorem B5336401 : Blo 1403521 5336401 := bstep (se 2 (by rfl) ⟨2001150, by rfl⟩ : syracuseStep 5336401 = 4002301) B4002301
theorem B1404351 : Blo 1403521 1404351 := bstep (se 1 (by rfl) ⟨1053263, by rfl⟩ : syracuseStep 1404351 = 2106527) B2106527
theorem B4001231 : Blo 1403521 4001231 := bstep (se 1 (by rfl) ⟨3000923, by rfl⟩ : syracuseStep 4001231 = 6001847) B6001847
theorem B1404447 : Blo 1403521 1404447 := bstep (se 1 (by rfl) ⟨1053335, by rfl⟩ : syracuseStep 1404447 = 2106671) B2106671
theorem B1404575 : Blo 1403521 1404575 := bstep (se 1 (by rfl) ⟨1053431, by rfl⟩ : syracuseStep 1404575 = 2106863) B2106863
theorem B1404583 : Blo 1403521 1404583 := bstep (se 1 (by rfl) ⟨1053437, by rfl⟩ : syracuseStep 1404583 = 2106875) B2106875
theorem B1404607 : Blo 1403521 1404607 := bstep (se 1 (by rfl) ⟨1053455, by rfl⟩ : syracuseStep 1404607 = 2106911) B2106911
theorem B7597775 : Blo 1403521 7597775 := bstep (se 1 (by rfl) ⟨5698331, by rfl⟩ : syracuseStep 7597775 = 11396663) B11396663
theorem B1404703 : Blo 1403521 1404703 := bstep (se 1 (by rfl) ⟨1053527, by rfl⟩ : syracuseStep 1404703 = 2107055) B2107055
theorem B1404763 : Blo 1403521 1404763 := bstep (se 1 (by rfl) ⟨1053572, by rfl⟩ : syracuseStep 1404763 = 2107145) B2107145
theorem B1404783 : Blo 1403521 1404783 := bstep (se 1 (by rfl) ⟨1053587, by rfl⟩ : syracuseStep 1404783 = 2107175) B2107175
theorem B4738985 : Blo 1403521 4738985 := bstep (se 2 (by rfl) ⟨1777119, by rfl⟩ : syracuseStep 4738985 = 3554239) B3554239
theorem B16224263 : Blo 1403521 16224263 := bstep (se 1 (by rfl) ⟨12168197, by rfl⟩ : syracuseStep 16224263 = 24336395) B24336395
theorem B2666591 : Blo 1403521 2666591 := bstep (se 1 (by rfl) ⟨1999943, by rfl⟩ : syracuseStep 2666591 = 3999887) B3999887
theorem B1405183 : Blo 1403521 1405183 := bstep (se 1 (by rfl) ⟨1053887, by rfl⟩ : syracuseStep 1405183 = 2107775) B2107775
theorem B48632183 : Blo 1403521 48632183 := bstep (se 1 (by rfl) ⟨36474137, by rfl⟩ : syracuseStep 48632183 = 72948275) B72948275
theorem B91132289 : Blo 1403521 91132289 := bstep (se 2 (by rfl) ⟨34174608, by rfl⟩ : syracuseStep 91132289 = 68349217) B68349217
theorem B1405343 : Blo 1403521 1405343 := bstep (se 1 (by rfl) ⟨1054007, by rfl⟩ : syracuseStep 1405343 = 2108015) B2108015
theorem B1405487 : Blo 1403521 1405487 := bstep (se 1 (by rfl) ⟨1054115, by rfl⟩ : syracuseStep 1405487 = 2108231) B2108231
theorem B5329583 : Blo 1403521 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B34157285 : Blo 1403521 34157285 := bstep (se 4 (by rfl) ⟨3202245, by rfl⟩ : syracuseStep 34157285 = 6404491) B6404491
theorem B4739849 : Blo 1403521 4739849 := bstep (se 2 (by rfl) ⟨1777443, by rfl⟩ : syracuseStep 4739849 = 3554887) B3554887
theorem B4739903 : Blo 1403521 4739903 := bstep (se 1 (by rfl) ⟨3554927, by rfl⟩ : syracuseStep 4739903 = 7109855) B7109855
theorem B23090093 : Blo 1403521 23090093 := bstep (se 3 (by rfl) ⟨4329392, by rfl⟩ : syracuseStep 23090093 = 8658785) B8658785
theorem B10671101 : Blo 1403521 10671101 := bstep (se 3 (by rfl) ⟨2000831, by rfl⟩ : syracuseStep 10671101 = 4001663) B4001663
theorem B710530055 : Blo 1403521 710530055 := bstep (se 1 (by rfl) ⟨532897541, by rfl⟩ : syracuseStep 710530055 = 1065795083) B1065795083
theorem B27366599 : Blo 1403521 27366599 := bstep (se 1 (by rfl) ⟨20524949, by rfl⟩ : syracuseStep 27366599 = 41049899) B41049899
theorem B2848583 : Blo 1403521 2848583 := bstep (se 1 (by rfl) ⟨2136437, by rfl⟩ : syracuseStep 2848583 = 4272875) B4272875
theorem B2529391 : Blo 1403521 2529391 := bstep (se 1 (by rfl) ⟨1897043, by rfl⟩ : syracuseStep 2529391 = 3794087) B3794087
theorem B2849183 : Blo 1403521 2849183 := bstep (se 1 (by rfl) ⟨2136887, by rfl⟩ : syracuseStep 2849183 = 4273775) B4273775
theorem B43219493 : Blo 1403521 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B30366359 : Blo 1403521 30366359 := bstep (se 1 (by rfl) ⟨22774769, by rfl⟩ : syracuseStep 30366359 = 45549539) B45549539
theorem B4741793 : Blo 1403521 4741793 := bstep (se 2 (by rfl) ⟨1778172, by rfl⟩ : syracuseStep 4741793 = 3556345) B3556345
theorem B3160889 : Blo 1403521 3160889 := bstep (se 2 (by rfl) ⟨1185333, by rfl⟩ : syracuseStep 3160889 = 2370667) B2370667
theorem B3603311 : Blo 1403521 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B28842875 : Blo 1403521 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B45562763 : Blo 1403521 45562763 := bstep (se 1 (by rfl) ⟨34172072, by rfl⟩ : syracuseStep 45562763 = 68344145) B68344145
theorem B1776583 : Blo 1403521 1776583 := bstep (se 1 (by rfl) ⟨1332437, by rfl⟩ : syracuseStep 1776583 = 2664875) B2664875
theorem B3161249 : Blo 1403521 3161249 := bstep (se 2 (by rfl) ⟨1185468, by rfl⟩ : syracuseStep 3161249 = 2370937) B2370937
theorem B3161591 : Blo 1403521 3161591 := bstep (se 1 (by rfl) ⟨2371193, by rfl⟩ : syracuseStep 3161591 = 4742387) B4742387
theorem B5332499 : Blo 1403521 5332499 := bstep (se 1 (by rfl) ⟨3999374, by rfl⟩ : syracuseStep 5332499 = 7998749) B7998749
theorem B17309497 : Blo 1403521 17309497 := bstep (se 2 (by rfl) ⟨6491061, by rfl⟩ : syracuseStep 17309497 = 12982123) B12982123
theorem B5332817 : Blo 1403521 5332817 := bstep (se 2 (by rfl) ⟨1999806, by rfl⟩ : syracuseStep 5332817 = 3999613) B3999613
theorem B57646997 : Blo 1403521 57646997 := bstep (se 6 (by rfl) ⟨1351101, by rfl⟩ : syracuseStep 57646997 = 2702203) B2702203
theorem B10813499 : Blo 1403521 10813499 := bstep (se 1 (by rfl) ⟨8110124, by rfl⟩ : syracuseStep 10813499 = 16220249) B16220249
theorem B1777727 : Blo 1403521 1777727 := bstep (se 1 (by rfl) ⟨1333295, by rfl⟩ : syracuseStep 1777727 = 2666591) B2666591
theorem B3555535 : Blo 1403521 3555535 := bstep (se 1 (by rfl) ⟨2666651, by rfl⟩ : syracuseStep 3555535 = 5333303) B5333303
theorem B12804317 : Blo 1403521 12804317 := bstep (se 3 (by rfl) ⟨2400809, by rfl⟩ : syracuseStep 12804317 = 4801619) B4801619
theorem B3375481 : Blo 1403521 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B15393395 : Blo 1403521 15393395 := bstep (se 1 (by rfl) ⟨11545046, by rfl⟩ : syracuseStep 15393395 = 23090093) B23090093
theorem B473686703 : Blo 1403521 473686703 := bstep (se 1 (by rfl) ⟨355265027, by rfl⟩ : syracuseStep 473686703 = 710530055) B710530055
theorem B18244399 : Blo 1403521 18244399 := bstep (se 1 (by rfl) ⟨13683299, by rfl⟩ : syracuseStep 18244399 = 27366599) B27366599
theorem B23987015 : Blo 1403521 23987015 := bstep (se 1 (by rfl) ⟨17990261, by rfl⟩ : syracuseStep 23987015 = 35980523) B35980523
theorem B3998555 : Blo 1403521 3998555 := bstep (se 1 (by rfl) ⟨2998916, by rfl⟩ : syracuseStep 3998555 = 5997833) B5997833
theorem B2368777 : Blo 1403521 2368777 := bstep (se 2 (by rfl) ⟨888291, by rfl⟩ : syracuseStep 2368777 = 1776583) B1776583
theorem B3556943 : Blo 1403521 3556943 := bstep (se 1 (by rfl) ⟨2667707, by rfl⟩ : syracuseStep 3556943 = 5335415) B5335415
theorem B28812995 : Blo 1403521 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B20244239 : Blo 1403521 20244239 := bstep (se 1 (by rfl) ⟨15183179, by rfl⟩ : syracuseStep 20244239 = 30366359) B30366359
theorem B2107259 : Blo 1403521 2107259 := bstep (se 1 (by rfl) ⟨1580444, by rfl⟩ : syracuseStep 2107259 = 3160889) B3160889
theorem B2402207 : Blo 1403521 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B19228583 : Blo 1403521 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B5998531 : Blo 1403521 5998531 := bstep (se 1 (by rfl) ⟨4498898, by rfl⟩ : syracuseStep 5998531 = 8997797) B8997797
theorem B2107499 : Blo 1403521 2107499 := bstep (se 1 (by rfl) ⟨1580624, by rfl⟩ : syracuseStep 2107499 = 3161249) B3161249
theorem B2107727 : Blo 1403521 2107727 := bstep (se 1 (by rfl) ⟨1580795, by rfl⟩ : syracuseStep 2107727 = 3161591) B3161591
theorem B10127713 : Blo 1403521 10127713 := bstep (se 2 (by rfl) ⟨3797892, by rfl⟩ : syracuseStep 10127713 = 7595785) B7595785
theorem B23079329 : Blo 1403521 23079329 := bstep (se 2 (by rfl) ⟨8654748, by rfl⟩ : syracuseStep 23079329 = 17309497) B17309497
theorem B5065183 : Blo 1403521 5065183 := bstep (se 1 (by rfl) ⟨3798887, by rfl⟩ : syracuseStep 5065183 = 7597775) B7597775
theorem B7113257 : Blo 1403521 7113257 := bstep (se 2 (by rfl) ⟨2667471, by rfl⟩ : syracuseStep 7113257 = 5334943) B5334943
theorem B38431331 : Blo 1403521 38431331 := bstep (se 1 (by rfl) ⟨28823498, by rfl⟩ : syracuseStep 38431331 = 57646997) B57646997
theorem B10816175 : Blo 1403521 10816175 := bstep (se 1 (by rfl) ⟨8112131, by rfl⟩ : syracuseStep 10816175 = 16224263) B16224263
theorem B60754859 : Blo 1403521 60754859 := bstep (se 1 (by rfl) ⟨45566144, by rfl⟩ : syracuseStep 60754859 = 91132289) B91132289
theorem B7114067 : Blo 1403521 7114067 := bstep (se 1 (by rfl) ⟨5335550, by rfl⟩ : syracuseStep 7114067 = 10671101) B10671101
theorem B8219999 : Blo 1403521 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B1404463 : Blo 1403521 1404463 := bstep (se 1 (by rfl) ⟨1053347, by rfl⟩ : syracuseStep 1404463 = 2106695) B2106695
theorem B10661867 : Blo 1403521 10661867 := bstep (se 1 (by rfl) ⟨7996400, by rfl⟩ : syracuseStep 10661867 = 15992801) B15992801
theorem B7106615 : Blo 1403521 7106615 := bstep (se 1 (by rfl) ⟨5329961, by rfl⟩ : syracuseStep 7106615 = 10659923) B10659923
theorem B1405019 : Blo 1403521 1405019 := bstep (se 1 (by rfl) ⟨1053764, by rfl⟩ : syracuseStep 1405019 = 2107529) B2107529
theorem B57675881 : Blo 1403521 57675881 := bstep (se 2 (by rfl) ⟨21628455, by rfl⟩ : syracuseStep 57675881 = 43256911) B43256911
theorem B3158153 : Blo 1403521 3158153 := bstep (se 2 (by rfl) ⟨1184307, by rfl⟩ : syracuseStep 3158153 = 2368615) B2368615
theorem B3158207 : Blo 1403521 3158207 := bstep (se 1 (by rfl) ⟨2368655, by rfl⟩ : syracuseStep 3158207 = 4737311) B4737311
theorem B3158459 : Blo 1403521 3158459 := bstep (se 1 (by rfl) ⟨2368844, by rfl⟩ : syracuseStep 3158459 = 4737689) B4737689
theorem B7115201 : Blo 1403521 7115201 := bstep (se 2 (by rfl) ⟨2668200, by rfl⟩ : syracuseStep 7115201 = 5336401) B5336401
theorem B1405467 : Blo 1403521 1405467 := bstep (se 1 (by rfl) ⟨1054100, by rfl⟩ : syracuseStep 1405467 = 2108201) B2108201
theorem B3158639 : Blo 1403521 3158639 := bstep (se 1 (by rfl) ⟨2368979, by rfl⟩ : syracuseStep 3158639 = 4737959) B4737959
theorem B12006083 : Blo 1403521 12006083 := bstep (se 1 (by rfl) ⟨9004562, by rfl⟩ : syracuseStep 12006083 = 18009125) B18009125
theorem B3158855 : Blo 1403521 3158855 := bstep (se 1 (by rfl) ⟨2369141, by rfl⟩ : syracuseStep 3158855 = 4738283) B4738283
theorem B2667487 : Blo 1403521 2667487 := bstep (se 1 (by rfl) ⟨2000615, by rfl⟩ : syracuseStep 2667487 = 4001231) B4001231
theorem B3159161 : Blo 1403521 3159161 := bstep (se 2 (by rfl) ⟨1184685, by rfl⟩ : syracuseStep 3159161 = 2369371) B2369371
theorem B3159323 : Blo 1403521 3159323 := bstep (se 1 (by rfl) ⟨2369492, by rfl⟩ : syracuseStep 3159323 = 4738985) B4738985
theorem B3372521 : Blo 1403521 3372521 := bstep (se 2 (by rfl) ⟨1264695, by rfl⟩ : syracuseStep 3372521 = 2529391) B2529391
theorem B5690935 : Blo 1403521 5690935 := bstep (se 1 (by rfl) ⟨4268201, by rfl⟩ : syracuseStep 5690935 = 8536403) B8536403
theorem B32421455 : Blo 1403521 32421455 := bstep (se 1 (by rfl) ⟨24316091, by rfl⟩ : syracuseStep 32421455 = 48632183) B48632183
theorem B12334673 : Blo 1403521 12334673 := bstep (se 2 (by rfl) ⟨4625502, by rfl⟩ : syracuseStep 12334673 = 9251005) B9251005
theorem B27014917 : Blo 1403521 27014917 := bstep (se 4 (by rfl) ⟨2532648, by rfl⟩ : syracuseStep 27014917 = 5065297) B5065297
theorem B3553055 : Blo 1403521 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B22771523 : Blo 1403521 22771523 := bstep (se 1 (by rfl) ⟨17078642, by rfl⟩ : syracuseStep 22771523 = 34157285) B34157285
theorem B3159899 : Blo 1403521 3159899 := bstep (se 1 (by rfl) ⟨2369924, by rfl⟩ : syracuseStep 3159899 = 4739849) B4739849
theorem B3159935 : Blo 1403521 3159935 := bstep (se 1 (by rfl) ⟨2369951, by rfl⟩ : syracuseStep 3159935 = 4739903) B4739903
theorem B3160457 : Blo 1403521 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B17095187 : Blo 1403521 17095187 := bstep (se 1 (by rfl) ⟨12821390, by rfl⟩ : syracuseStep 17095187 = 25642781) B25642781
theorem B1579567 : Blo 1403521 1579567 := bstep (se 1 (by rfl) ⟨1184675, by rfl⟩ : syracuseStep 1579567 = 2369351) B2369351
theorem B1899055 : Blo 1403521 1899055 := bstep (se 1 (by rfl) ⟨1424291, by rfl⟩ : syracuseStep 1899055 = 2848583) B2848583
theorem B1579711 : Blo 1403521 1579711 := bstep (se 1 (by rfl) ⟨1184783, by rfl⟩ : syracuseStep 1579711 = 2369567) B2369567
theorem B1776487 : Blo 1403521 1776487 := bstep (se 1 (by rfl) ⟨1332365, by rfl⟩ : syracuseStep 1776487 = 2664731) B2664731
theorem B1899455 : Blo 1403521 1899455 := bstep (se 1 (by rfl) ⟨1424591, by rfl⟩ : syracuseStep 1899455 = 2849183) B2849183
theorem B3161195 : Blo 1403521 3161195 := bstep (se 1 (by rfl) ⟨2370896, by rfl⟩ : syracuseStep 3161195 = 4741793) B4741793
theorem B30375175 : Blo 1403521 30375175 := bstep (se 1 (by rfl) ⟨22781381, by rfl⟩ : syracuseStep 30375175 = 45562763) B45562763
theorem B1580575 : Blo 1403521 1580575 := bstep (se 1 (by rfl) ⟨1185431, by rfl⟩ : syracuseStep 1580575 = 2370863) B2370863
theorem B3554999 : Blo 1403521 3554999 := bstep (se 1 (by rfl) ⟨2666249, by rfl⟩ : syracuseStep 3554999 = 5332499) B5332499
theorem B3555211 : Blo 1403521 3555211 := bstep (se 1 (by rfl) ⟨2666408, by rfl⟩ : syracuseStep 3555211 = 5332817) B5332817
theorem B7208999 : Blo 1403521 7208999 := bstep (se 1 (by rfl) ⟨5406749, by rfl⟩ : syracuseStep 7208999 = 10813499) B10813499
theorem B2105435 : Blo 1403521 2105435 := bstep (se 1 (by rfl) ⟨1579076, by rfl⟩ : syracuseStep 2105435 = 3158153) B3158153
theorem B2105471 : Blo 1403521 2105471 := bstep (se 1 (by rfl) ⟨1579103, by rfl⟩ : syracuseStep 2105471 = 3158207) B3158207
theorem B8536211 : Blo 1403521 8536211 := bstep (se 1 (by rfl) ⟨6402158, by rfl⟩ : syracuseStep 8536211 = 12804317) B12804317
theorem B2105639 : Blo 1403521 2105639 := bstep (se 1 (by rfl) ⟨1579229, by rfl⟩ : syracuseStep 2105639 = 3158459) B3158459
theorem B4743467 : Blo 1403521 4743467 := bstep (se 1 (by rfl) ⟨3557600, by rfl⟩ : syracuseStep 4743467 = 7115201) B7115201
theorem B2105759 : Blo 1403521 2105759 := bstep (se 1 (by rfl) ⟨1579319, by rfl⟩ : syracuseStep 2105759 = 3158639) B3158639
theorem B8004055 : Blo 1403521 8004055 := bstep (se 1 (by rfl) ⟨6003041, by rfl⟩ : syracuseStep 8004055 = 12006083) B12006083
theorem B15991343 : Blo 1403521 15991343 := bstep (se 1 (by rfl) ⟨11993507, by rfl⟩ : syracuseStep 15991343 = 23987015) B23987015
theorem B2105903 : Blo 1403521 2105903 := bstep (se 1 (by rfl) ⟨1579427, by rfl⟩ : syracuseStep 2105903 = 3158855) B3158855
theorem B2106089 : Blo 1403521 2106089 := bstep (se 2 (by rfl) ⟨789783, by rfl⟩ : syracuseStep 2106089 = 1579567) B1579567
theorem B2532073 : Blo 1403521 2532073 := bstep (se 2 (by rfl) ⟨949527, by rfl⟩ : syracuseStep 2532073 = 1899055) B1899055
theorem B2106107 : Blo 1403521 2106107 := bstep (se 1 (by rfl) ⟨1579580, by rfl⟩ : syracuseStep 2106107 = 3159161) B3159161
theorem B2106215 : Blo 1403521 2106215 := bstep (se 1 (by rfl) ⟨1579661, by rfl⟩ : syracuseStep 2106215 = 3159323) B3159323
theorem B2106281 : Blo 1403521 2106281 := bstep (se 2 (by rfl) ⟨789855, by rfl⟩ : syracuseStep 2106281 = 1579711) B1579711
theorem B2368649 : Blo 1403521 2368649 := bstep (se 2 (by rfl) ⟨888243, by rfl⟩ : syracuseStep 2368649 = 1776487) B1776487
theorem B2368703 : Blo 1403521 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B15181015 : Blo 1403521 15181015 := bstep (se 1 (by rfl) ⟨11385761, by rfl⟩ : syracuseStep 15181015 = 22771523) B22771523
theorem B2106599 : Blo 1403521 2106599 := bstep (se 1 (by rfl) ⟨1579949, by rfl⟩ : syracuseStep 2106599 = 3159899) B3159899
theorem B2106623 : Blo 1403521 2106623 := bstep (se 1 (by rfl) ⟨1579967, by rfl⟩ : syracuseStep 2106623 = 3159935) B3159935
theorem B3556649 : Blo 1403521 3556649 := bstep (se 2 (by rfl) ⟨1333743, by rfl⟩ : syracuseStep 3556649 = 2667487) B2667487
theorem B2106971 : Blo 1403521 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B15386219 : Blo 1403521 15386219 := bstep (se 1 (by rfl) ⟨11539664, by rfl⟩ : syracuseStep 15386219 = 23079329) B23079329
theorem B11396791 : Blo 1403521 11396791 := bstep (se 1 (by rfl) ⟨8547593, by rfl⟩ : syracuseStep 11396791 = 17095187) B17095187
theorem B7210783 : Blo 1403521 7210783 := bstep (se 1 (by rfl) ⟨5408087, by rfl⟩ : syracuseStep 7210783 = 10816175) B10816175
theorem B40503239 : Blo 1403521 40503239 := bstep (se 1 (by rfl) ⟨30377429, by rfl⟩ : syracuseStep 40503239 = 60754859) B60754859
theorem B2107433 : Blo 1403521 2107433 := bstep (se 2 (by rfl) ⟨790287, by rfl⟩ : syracuseStep 2107433 = 1580575) B1580575
theorem B2107463 : Blo 1403521 2107463 := bstep (se 1 (by rfl) ⟨1580597, by rfl⟩ : syracuseStep 2107463 = 3161195) B3161195
theorem B7587913 : Blo 1403521 7587913 := bstep (se 2 (by rfl) ⟨2845467, by rfl⟩ : syracuseStep 7587913 = 5690935) B5690935
theorem B2369999 : Blo 1403521 2369999 := bstep (se 1 (by rfl) ⟨1777499, by rfl⟩ : syracuseStep 2369999 = 3554999) B3554999
theorem B5065213 : Blo 1403521 5065213 := bstep (se 3 (by rfl) ⟨949727, by rfl⟩ : syracuseStep 5065213 = 1899455) B1899455
theorem B7998041 : Blo 1403521 7998041 := bstep (se 2 (by rfl) ⟨2999265, by rfl⟩ : syracuseStep 7998041 = 5998531) B5998531
theorem B4737743 : Blo 1403521 4737743 := bstep (se 1 (by rfl) ⟨3553307, by rfl⟩ : syracuseStep 4737743 = 7106615) B7106615
theorem B13503617 : Blo 1403521 13503617 := bstep (se 2 (by rfl) ⟨5063856, by rfl⟩ : syracuseStep 13503617 = 10127713) B10127713
theorem B4500641 : Blo 1403521 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B2665703 : Blo 1403521 2665703 := bstep (se 1 (by rfl) ⟨1999277, by rfl⟩ : syracuseStep 2665703 = 3998555) B3998555
theorem B6753577 : Blo 1403521 6753577 := bstep (se 2 (by rfl) ⟨2532591, by rfl⟩ : syracuseStep 6753577 = 5065183) B5065183
theorem B21614303 : Blo 1403521 21614303 := bstep (se 1 (by rfl) ⟨16210727, by rfl⟩ : syracuseStep 21614303 = 32421455) B32421455
theorem B2371295 : Blo 1403521 2371295 := bstep (se 1 (by rfl) ⟨1778471, by rfl⟩ : syracuseStep 2371295 = 3556943) B3556943
theorem B24325865 : Blo 1403521 24325865 := bstep (se 2 (by rfl) ⟨9122199, by rfl⟩ : syracuseStep 24325865 = 18244399) B18244399
theorem B13496159 : Blo 1403521 13496159 := bstep (se 1 (by rfl) ⟨10122119, by rfl⟩ : syracuseStep 13496159 = 20244239) B20244239
theorem B1404839 : Blo 1403521 1404839 := bstep (se 1 (by rfl) ⟨1053629, by rfl⟩ : syracuseStep 1404839 = 2107259) B2107259
theorem B1601471 : Blo 1403521 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B1404999 : Blo 1403521 1404999 := bstep (se 1 (by rfl) ⟨1053749, by rfl⟩ : syracuseStep 1404999 = 2107499) B2107499
theorem B1405151 : Blo 1403521 1405151 := bstep (se 1 (by rfl) ⟨1053863, by rfl⟩ : syracuseStep 1405151 = 2107727) B2107727
theorem B3158369 : Blo 1403521 3158369 := bstep (se 2 (by rfl) ⟨1184388, by rfl⟩ : syracuseStep 3158369 = 2368777) B2368777
theorem B25620887 : Blo 1403521 25620887 := bstep (se 1 (by rfl) ⟨19215665, by rfl⟩ : syracuseStep 25620887 = 38431331) B38431331
theorem B4740281 : Blo 1403521 4740281 := bstep (se 2 (by rfl) ⟨1777605, by rfl⟩ : syracuseStep 4740281 = 3555211) B3555211
theorem B7107911 : Blo 1403521 7107911 := bstep (se 1 (by rfl) ⟨5330933, by rfl⟩ : syracuseStep 7107911 = 10661867) B10661867
theorem B38450587 : Blo 1403521 38450587 := bstep (se 1 (by rfl) ⟨28837940, by rfl⟩ : syracuseStep 38450587 = 57675881) B57675881
theorem B4740605 : Blo 1403521 4740605 := bstep (se 3 (by rfl) ⟨888863, by rfl⟩ : syracuseStep 4740605 = 1777727) B1777727
theorem B4740713 : Blo 1403521 4740713 := bstep (se 2 (by rfl) ⟨1777767, by rfl⟩ : syracuseStep 4740713 = 3555535) B3555535
theorem B10262263 : Blo 1403521 10262263 := bstep (se 1 (by rfl) ⟨7696697, by rfl⟩ : syracuseStep 10262263 = 15393395) B15393395
theorem B315791135 : Blo 1403521 315791135 := bstep (se 1 (by rfl) ⟨236843351, by rfl⟩ : syracuseStep 315791135 = 473686703) B473686703
theorem B21919997 : Blo 1403521 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B8223115 : Blo 1403521 8223115 := bstep (se 1 (by rfl) ⟨6167336, by rfl⟩ : syracuseStep 8223115 = 12334673) B12334673
theorem B19208663 : Blo 1403521 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B8993389 : Blo 1403521 8993389 := bstep (se 3 (by rfl) ⟨1686260, by rfl⟩ : syracuseStep 8993389 = 3372521) B3372521
theorem B12819055 : Blo 1403521 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B40500233 : Blo 1403521 40500233 := bstep (se 2 (by rfl) ⟨15187587, by rfl⟩ : syracuseStep 40500233 = 30375175) B30375175
theorem B4742171 : Blo 1403521 4742171 := bstep (se 1 (by rfl) ⟨3556628, by rfl⟩ : syracuseStep 4742171 = 7113257) B7113257
theorem B4742711 : Blo 1403521 4742711 := bstep (se 1 (by rfl) ⟨3557033, by rfl⟩ : syracuseStep 4742711 = 7114067) B7114067
theorem B36019889 : Blo 1403521 36019889 := bstep (se 2 (by rfl) ⟨13507458, by rfl⟩ : syracuseStep 36019889 = 27014917) B27014917
theorem B10117217 : Blo 1403521 10117217 := bstep (se 2 (by rfl) ⟨3793956, by rfl⟩ : syracuseStep 10117217 = 7587913) B7587913
theorem B3162311 : Blo 1403521 3162311 := bstep (se 1 (by rfl) ⟨2371733, by rfl⟩ : syracuseStep 3162311 = 4743467) B4743467
theorem B2105579 : Blo 1403521 2105579 := bstep (se 1 (by rfl) ⟨1579184, by rfl⟩ : syracuseStep 2105579 = 3158369) B3158369
theorem B17080591 : Blo 1403521 17080591 := bstep (se 1 (by rfl) ⟨12810443, by rfl⟩ : syracuseStep 17080591 = 25620887) B25620887
theorem B12001709 : Blo 1403521 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B3376097 : Blo 1403521 3376097 := bstep (se 2 (by rfl) ⟨1266036, by rfl⟩ : syracuseStep 3376097 = 2532073) B2532073
theorem B10257479 : Blo 1403521 10257479 := bstep (se 1 (by rfl) ⟨7693109, by rfl⟩ : syracuseStep 10257479 = 15386219) B15386219
theorem B210527423 : Blo 1403521 210527423 := bstep (se 1 (by rfl) ⟨157895567, by rfl⟩ : syracuseStep 210527423 = 315791135) B315791135
theorem B27002159 : Blo 1403521 27002159 := bstep (se 1 (by rfl) ⟨20251619, by rfl⟩ : syracuseStep 27002159 = 40503239) B40503239
theorem B12805775 : Blo 1403521 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B9004769 : Blo 1403521 9004769 := bstep (se 2 (by rfl) ⟨3376788, by rfl⟩ : syracuseStep 9004769 = 6753577) B6753577
theorem B51267449 : Blo 1403521 51267449 := bstep (se 2 (by rfl) ⟨19225293, by rfl⟩ : syracuseStep 51267449 = 38450587) B38450587
theorem B13683017 : Blo 1403521 13683017 := bstep (se 2 (by rfl) ⟨5131131, by rfl⟩ : syracuseStep 13683017 = 10262263) B10262263
theorem B24013259 : Blo 1403521 24013259 := bstep (se 1 (by rfl) ⟨18009944, by rfl⟩ : syracuseStep 24013259 = 36019889) B36019889
theorem B4270589 : Blo 1403521 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B8997439 : Blo 1403521 8997439 := bstep (se 1 (by rfl) ⟨6748079, by rfl⟩ : syracuseStep 8997439 = 13496159) B13496159
theorem B1403623 : Blo 1403521 1403623 := bstep (se 1 (by rfl) ⟨1052717, by rfl⟩ : syracuseStep 1403623 = 2105435) B2105435
theorem B1403647 : Blo 1403521 1403647 := bstep (se 1 (by rfl) ⟨1052735, by rfl⟩ : syracuseStep 1403647 = 2105471) B2105471
theorem B1403759 : Blo 1403521 1403759 := bstep (se 1 (by rfl) ⟨1052819, by rfl⟩ : syracuseStep 1403759 = 2105639) B2105639
theorem B1403839 : Blo 1403521 1403839 := bstep (se 1 (by rfl) ⟨1052879, by rfl⟩ : syracuseStep 1403839 = 2105759) B2105759
theorem B10660895 : Blo 1403521 10660895 := bstep (se 1 (by rfl) ⟨7995671, by rfl⟩ : syracuseStep 10660895 = 15991343) B15991343
theorem B1403935 : Blo 1403521 1403935 := bstep (se 1 (by rfl) ⟨1052951, by rfl⟩ : syracuseStep 1403935 = 2105903) B2105903
theorem B1404059 : Blo 1403521 1404059 := bstep (se 1 (by rfl) ⟨1053044, by rfl⟩ : syracuseStep 1404059 = 2106089) B2106089
theorem B1404071 : Blo 1403521 1404071 := bstep (se 1 (by rfl) ⟨1053053, by rfl⟩ : syracuseStep 1404071 = 2106107) B2106107
theorem B10964153 : Blo 1403521 10964153 := bstep (se 2 (by rfl) ⟨4111557, by rfl⟩ : syracuseStep 10964153 = 8223115) B8223115
theorem B1404143 : Blo 1403521 1404143 := bstep (se 1 (by rfl) ⟨1053107, by rfl⟩ : syracuseStep 1404143 = 2106215) B2106215
theorem B1404187 : Blo 1403521 1404187 := bstep (se 1 (by rfl) ⟨1053140, by rfl⟩ : syracuseStep 1404187 = 2106281) B2106281
theorem B58453325 : Blo 1403521 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B6753617 : Blo 1403521 6753617 := bstep (se 2 (by rfl) ⟨2532606, by rfl⟩ : syracuseStep 6753617 = 5065213) B5065213
theorem B17092073 : Blo 1403521 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B1404399 : Blo 1403521 1404399 := bstep (se 1 (by rfl) ⟨1053299, by rfl⟩ : syracuseStep 1404399 = 2106599) B2106599
theorem B1404415 : Blo 1403521 1404415 := bstep (se 1 (by rfl) ⟨1053311, by rfl⟩ : syracuseStep 1404415 = 2106623) B2106623
theorem B2371099 : Blo 1403521 2371099 := bstep (se 1 (by rfl) ⟨1778324, by rfl⟩ : syracuseStep 2371099 = 3556649) B3556649
theorem B4738607 : Blo 1403521 4738607 := bstep (se 1 (by rfl) ⟨3553955, by rfl⟩ : syracuseStep 4738607 = 7107911) B7107911
theorem B1404647 : Blo 1403521 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B1404955 : Blo 1403521 1404955 := bstep (se 1 (by rfl) ⟨1053716, by rfl⟩ : syracuseStep 1404955 = 2107433) B2107433
theorem B1404975 : Blo 1403521 1404975 := bstep (se 1 (by rfl) ⟨1053731, by rfl⟩ : syracuseStep 1404975 = 2107463) B2107463
theorem B3158495 : Blo 1403521 3158495 := bstep (se 1 (by rfl) ⟨2368871, by rfl⟩ : syracuseStep 3158495 = 4737743) B4737743
theorem B9614377 : Blo 1403521 9614377 := bstep (se 2 (by rfl) ⟨3605391, by rfl⟩ : syracuseStep 9614377 = 7210783) B7210783
theorem B16217243 : Blo 1403521 16217243 := bstep (se 1 (by rfl) ⟨12162932, by rfl⟩ : syracuseStep 16217243 = 24325865) B24325865
theorem B4805999 : Blo 1403521 4805999 := bstep (se 1 (by rfl) ⟨3604499, by rfl⟩ : syracuseStep 4805999 = 7208999) B7208999
theorem B5690807 : Blo 1403521 5690807 := bstep (se 1 (by rfl) ⟨4268105, by rfl⟩ : syracuseStep 5690807 = 8536211) B8536211
theorem B10672073 : Blo 1403521 10672073 := bstep (se 2 (by rfl) ⟨4002027, by rfl⟩ : syracuseStep 10672073 = 8004055) B8004055
theorem B1579099 : Blo 1403521 1579099 := bstep (se 1 (by rfl) ⟨1184324, by rfl⟩ : syracuseStep 1579099 = 2368649) B2368649
theorem B3160187 : Blo 1403521 3160187 := bstep (se 1 (by rfl) ⟨2370140, by rfl⟩ : syracuseStep 3160187 = 4740281) B4740281
theorem B1579135 : Blo 1403521 1579135 := bstep (se 1 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 1579135 = 2368703) B2368703
theorem B11991185 : Blo 1403521 11991185 := bstep (se 2 (by rfl) ⟨4496694, by rfl⟩ : syracuseStep 11991185 = 8993389) B8993389
theorem B3160403 : Blo 1403521 3160403 := bstep (se 1 (by rfl) ⟨2370302, by rfl⟩ : syracuseStep 3160403 = 4740605) B4740605
theorem B3160475 : Blo 1403521 3160475 := bstep (se 1 (by rfl) ⟨2370356, by rfl⟩ : syracuseStep 3160475 = 4740713) B4740713
theorem B20241353 : Blo 1403521 20241353 := bstep (se 2 (by rfl) ⟨7590507, by rfl⟩ : syracuseStep 20241353 = 15181015) B15181015
theorem B1579999 : Blo 1403521 1579999 := bstep (se 1 (by rfl) ⟨1184999, by rfl⟩ : syracuseStep 1579999 = 2369999) B2369999
theorem B5332027 : Blo 1403521 5332027 := bstep (se 1 (by rfl) ⟨3999020, by rfl⟩ : syracuseStep 5332027 = 7998041) B7998041
theorem B27000155 : Blo 1403521 27000155 := bstep (se 1 (by rfl) ⟨20250116, by rfl⟩ : syracuseStep 27000155 = 40500233) B40500233
theorem B3161447 : Blo 1403521 3161447 := bstep (se 1 (by rfl) ⟨2371085, by rfl⟩ : syracuseStep 3161447 = 4742171) B4742171
theorem B9002411 : Blo 1403521 9002411 := bstep (se 1 (by rfl) ⟨6751808, by rfl⟩ : syracuseStep 9002411 = 13503617) B13503617
theorem B1777135 : Blo 1403521 1777135 := bstep (se 1 (by rfl) ⟨1332851, by rfl⟩ : syracuseStep 1777135 = 2665703) B2665703
theorem B15195721 : Blo 1403521 15195721 := bstep (se 2 (by rfl) ⟨5698395, by rfl⟩ : syracuseStep 15195721 = 11396791) B11396791
theorem B3161807 : Blo 1403521 3161807 := bstep (se 1 (by rfl) ⟨2371355, by rfl⟩ : syracuseStep 3161807 = 4742711) B4742711
theorem B14409535 : Blo 1403521 14409535 := bstep (se 1 (by rfl) ⟨10807151, by rfl⟩ : syracuseStep 14409535 = 21614303) B21614303
theorem B1580863 : Blo 1403521 1580863 := bstep (se 1 (by rfl) ⟨1185647, by rfl⟩ : syracuseStep 1580863 = 2371295) B2371295
theorem B2105465 : Blo 1403521 2105465 := bstep (se 2 (by rfl) ⟨789549, by rfl⟩ : syracuseStep 2105465 = 1579099) B1579099
theorem B2105513 : Blo 1403521 2105513 := bstep (se 2 (by rfl) ⟨789567, by rfl⟩ : syracuseStep 2105513 = 1579135) B1579135
theorem B2105663 : Blo 1403521 2105663 := bstep (se 1 (by rfl) ⟨1579247, by rfl⟩ : syracuseStep 2105663 = 3158495) B3158495
theorem B22774121 : Blo 1403521 22774121 := bstep (se 2 (by rfl) ⟨8540295, by rfl⟩ : syracuseStep 22774121 = 17080591) B17080591
theorem B3203999 : Blo 1403521 3203999 := bstep (se 1 (by rfl) ⟨2402999, by rfl⟩ : syracuseStep 3203999 = 4805999) B4805999
theorem B3793871 : Blo 1403521 3793871 := bstep (se 1 (by rfl) ⟨2845403, by rfl⟩ : syracuseStep 3793871 = 5690807) B5690807
theorem B8537183 : Blo 1403521 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B2106665 : Blo 1403521 2106665 := bstep (se 2 (by rfl) ⟨789999, by rfl⟩ : syracuseStep 2106665 = 1579999) B1579999
theorem B2106791 : Blo 1403521 2106791 := bstep (se 1 (by rfl) ⟨1580093, by rfl⟩ : syracuseStep 2106791 = 3160187) B3160187
theorem B2106935 : Blo 1403521 2106935 := bstep (se 1 (by rfl) ⟨1580201, by rfl⟩ : syracuseStep 2106935 = 3160403) B3160403
theorem B2106983 : Blo 1403521 2106983 := bstep (se 1 (by rfl) ⟨1580237, by rfl⟩ : syracuseStep 2106983 = 3160475) B3160475
theorem B16008839 : Blo 1403521 16008839 := bstep (se 1 (by rfl) ⟨12006629, by rfl⟩ : syracuseStep 16008839 = 24013259) B24013259
theorem B13494235 : Blo 1403521 13494235 := bstep (se 1 (by rfl) ⟨10120676, by rfl⟩ : syracuseStep 13494235 = 20241353) B20241353
theorem B2369513 : Blo 1403521 2369513 := bstep (se 2 (by rfl) ⟨888567, by rfl⟩ : syracuseStep 2369513 = 1777135) B1777135
theorem B20260961 : Blo 1403521 20260961 := bstep (se 2 (by rfl) ⟨7597860, by rfl⟩ : syracuseStep 20260961 = 15195721) B15195721
theorem B7309435 : Blo 1403521 7309435 := bstep (se 1 (by rfl) ⟨5482076, by rfl⟩ : syracuseStep 7309435 = 10964153) B10964153
theorem B18000103 : Blo 1403521 18000103 := bstep (se 1 (by rfl) ⟨13500077, by rfl⟩ : syracuseStep 18000103 = 27000155) B27000155
theorem B2107631 : Blo 1403521 2107631 := bstep (se 1 (by rfl) ⟨1580723, by rfl⟩ : syracuseStep 2107631 = 3161447) B3161447
theorem B19212713 : Blo 1403521 19212713 := bstep (se 2 (by rfl) ⟨7204767, by rfl⟩ : syracuseStep 19212713 = 14409535) B14409535
theorem B2107817 : Blo 1403521 2107817 := bstep (se 2 (by rfl) ⟨790431, by rfl⟩ : syracuseStep 2107817 = 1580863) B1580863
theorem B2107871 : Blo 1403521 2107871 := bstep (se 1 (by rfl) ⟨1580903, by rfl⟩ : syracuseStep 2107871 = 3161807) B3161807
theorem B6744811 : Blo 1403521 6744811 := bstep (se 1 (by rfl) ⟨5058608, by rfl⟩ : syracuseStep 6744811 = 10117217) B10117217
theorem B2108207 : Blo 1403521 2108207 := bstep (se 1 (by rfl) ⟨1581155, by rfl⟩ : syracuseStep 2108207 = 3162311) B3162311
theorem B1403719 : Blo 1403521 1403719 := bstep (se 1 (by rfl) ⟨1052789, by rfl⟩ : syracuseStep 1403719 = 2105579) B2105579
theorem B11996585 : Blo 1403521 11996585 := bstep (se 2 (by rfl) ⟨4498719, by rfl⟩ : syracuseStep 11996585 = 8997439) B8997439
theorem B18001439 : Blo 1403521 18001439 := bstep (se 1 (by rfl) ⟨13501079, by rfl⟩ : syracuseStep 18001439 = 27002159) B27002159
theorem B7114715 : Blo 1403521 7114715 := bstep (se 1 (by rfl) ⟨5336036, by rfl⟩ : syracuseStep 7114715 = 10672073) B10672073
theorem B9122011 : Blo 1403521 9122011 := bstep (se 1 (by rfl) ⟨6841508, by rfl⟩ : syracuseStep 9122011 = 13683017) B13683017
theorem B2847059 : Blo 1403521 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B7107263 : Blo 1403521 7107263 := bstep (se 1 (by rfl) ⟨5330447, by rfl⟩ : syracuseStep 7107263 = 10660895) B10660895
theorem B4502411 : Blo 1403521 4502411 := bstep (se 1 (by rfl) ⟨3376808, by rfl⟩ : syracuseStep 4502411 = 6753617) B6753617
theorem B6001607 : Blo 1403521 6001607 := bstep (se 1 (by rfl) ⟨4501205, by rfl⟩ : syracuseStep 6001607 = 9002411) B9002411
theorem B136713197 : Blo 1403521 136713197 := bstep (se 3 (by rfl) ⟨25633724, by rfl⟩ : syracuseStep 136713197 = 51267449) B51267449
theorem B3159071 : Blo 1403521 3159071 := bstep (se 1 (by rfl) ⟨2369303, by rfl⟩ : syracuseStep 3159071 = 4738607) B4738607
theorem B8001139 : Blo 1403521 8001139 := bstep (se 1 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 8001139 = 12001709) B12001709
theorem B2250731 : Blo 1403521 2250731 := bstep (se 1 (by rfl) ⟨1688048, by rfl⟩ : syracuseStep 2250731 = 3376097) B3376097
theorem B6838319 : Blo 1403521 6838319 := bstep (se 1 (by rfl) ⟨5128739, by rfl⟩ : syracuseStep 6838319 = 10257479) B10257479
theorem B10811495 : Blo 1403521 10811495 := bstep (se 1 (by rfl) ⟨8108621, by rfl⟩ : syracuseStep 10811495 = 16217243) B16217243
theorem B140351615 : Blo 1403521 140351615 := bstep (se 1 (by rfl) ⟨105263711, by rfl⟩ : syracuseStep 140351615 = 210527423) B210527423
theorem B6003179 : Blo 1403521 6003179 := bstep (se 1 (by rfl) ⟨4502384, by rfl⟩ : syracuseStep 6003179 = 9004769) B9004769
theorem B12819169 : Blo 1403521 12819169 := bstep (se 2 (by rfl) ⟨4807188, by rfl⟩ : syracuseStep 12819169 = 9614377) B9614377
theorem B7109369 : Blo 1403521 7109369 := bstep (se 2 (by rfl) ⟨2666013, by rfl⟩ : syracuseStep 7109369 = 5332027) B5332027
theorem B7994123 : Blo 1403521 7994123 := bstep (se 1 (by rfl) ⟨5995592, by rfl⟩ : syracuseStep 7994123 = 11991185) B11991185
theorem B3161465 : Blo 1403521 3161465 := bstep (se 2 (by rfl) ⟨1185549, by rfl⟩ : syracuseStep 3161465 = 2371099) B2371099
theorem B38968883 : Blo 1403521 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B11394715 : Blo 1403521 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B2106047 : Blo 1403521 2106047 := bstep (se 1 (by rfl) ⟨1579535, by rfl⟩ : syracuseStep 2106047 = 3159071) B3159071
theorem B1500487 : Blo 1403521 1500487 := bstep (se 1 (by rfl) ⟨1125365, by rfl⟩ : syracuseStep 1500487 = 2250731) B2250731
theorem B10668185 : Blo 1403521 10668185 := bstep (se 2 (by rfl) ⟨4000569, by rfl⟩ : syracuseStep 10668185 = 8001139) B8001139
theorem B2107643 : Blo 1403521 2107643 := bstep (se 1 (by rfl) ⟨1580732, by rfl⟩ : syracuseStep 2107643 = 3161465) B3161465
theorem B7997723 : Blo 1403521 7997723 := bstep (se 1 (by rfl) ⟨5998292, by rfl⟩ : syracuseStep 7997723 = 11996585) B11996585
theorem B25979255 : Blo 1403521 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B17992313 : Blo 1403521 17992313 := bstep (se 2 (by rfl) ⟨6747117, by rfl⟩ : syracuseStep 17992313 = 13494235) B13494235
theorem B1403643 : Blo 1403521 1403643 := bstep (se 1 (by rfl) ⟨1052732, by rfl⟩ : syracuseStep 1403643 = 2105465) B2105465
theorem B1403675 : Blo 1403521 1403675 := bstep (se 1 (by rfl) ⟨1052756, by rfl⟩ : syracuseStep 1403675 = 2105513) B2105513
theorem B1403775 : Blo 1403521 1403775 := bstep (se 1 (by rfl) ⟨1052831, by rfl⟩ : syracuseStep 1403775 = 2105663) B2105663
theorem B15182747 : Blo 1403521 15182747 := bstep (se 1 (by rfl) ⟨11387060, by rfl⟩ : syracuseStep 15182747 = 22774121) B22774121
theorem B28830653 : Blo 1403521 28830653 := bstep (se 3 (by rfl) ⟨5405747, by rfl⟩ : syracuseStep 28830653 = 10811495) B10811495
theorem B4738175 : Blo 1403521 4738175 := bstep (se 1 (by rfl) ⟨3553631, by rfl⟩ : syracuseStep 4738175 = 7107263) B7107263
theorem B3001607 : Blo 1403521 3001607 := bstep (se 1 (by rfl) ⟨2251205, by rfl⟩ : syracuseStep 3001607 = 4502411) B4502411
theorem B4001071 : Blo 1403521 4001071 := bstep (se 1 (by rfl) ⟨3000803, by rfl⟩ : syracuseStep 4001071 = 6001607) B6001607
theorem B1404443 : Blo 1403521 1404443 := bstep (se 1 (by rfl) ⟨1053332, by rfl⟩ : syracuseStep 1404443 = 2106665) B2106665
theorem B1404527 : Blo 1403521 1404527 := bstep (se 1 (by rfl) ⟨1053395, by rfl⟩ : syracuseStep 1404527 = 2106791) B2106791
theorem B17092225 : Blo 1403521 17092225 := bstep (se 2 (by rfl) ⟨6409584, by rfl⟩ : syracuseStep 17092225 = 12819169) B12819169
theorem B1404623 : Blo 1403521 1404623 := bstep (se 1 (by rfl) ⟨1053467, by rfl⟩ : syracuseStep 1404623 = 2106935) B2106935
theorem B1404655 : Blo 1403521 1404655 := bstep (se 1 (by rfl) ⟨1053491, by rfl⟩ : syracuseStep 1404655 = 2106983) B2106983
theorem B4558879 : Blo 1403521 4558879 := bstep (se 1 (by rfl) ⟨3419159, by rfl⟩ : syracuseStep 4558879 = 6838319) B6838319
theorem B1405087 : Blo 1403521 1405087 := bstep (se 1 (by rfl) ⟨1053815, by rfl⟩ : syracuseStep 1405087 = 2107631) B2107631
theorem B12808475 : Blo 1403521 12808475 := bstep (se 1 (by rfl) ⟨9606356, by rfl⟩ : syracuseStep 12808475 = 19212713) B19212713
theorem B1405211 : Blo 1403521 1405211 := bstep (se 1 (by rfl) ⟨1053908, by rfl⟩ : syracuseStep 1405211 = 2107817) B2107817
theorem B1405247 : Blo 1403521 1405247 := bstep (se 1 (by rfl) ⟨1053935, by rfl⟩ : syracuseStep 1405247 = 2107871) B2107871
theorem B4002119 : Blo 1403521 4002119 := bstep (se 1 (by rfl) ⟨3001589, by rfl⟩ : syracuseStep 4002119 = 6003179) B6003179
theorem B4739579 : Blo 1403521 4739579 := bstep (se 1 (by rfl) ⟨3554684, by rfl⟩ : syracuseStep 4739579 = 7109369) B7109369
theorem B5329415 : Blo 1403521 5329415 := bstep (se 1 (by rfl) ⟨3997061, by rfl⟩ : syracuseStep 5329415 = 7994123) B7994123
theorem B1405471 : Blo 1403521 1405471 := bstep (se 1 (by rfl) ⟨1054103, by rfl⟩ : syracuseStep 1405471 = 2108207) B2108207
theorem B15192953 : Blo 1403521 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B9745913 : Blo 1403521 9745913 := bstep (se 2 (by rfl) ⟨3654717, by rfl⟩ : syracuseStep 9745913 = 7309435) B7309435
theorem B1898039 : Blo 1403521 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B24000137 : Blo 1403521 24000137 := bstep (se 2 (by rfl) ⟨9000051, by rfl⟩ : syracuseStep 24000137 = 18000103) B18000103
theorem B2135999 : Blo 1403521 2135999 := bstep (se 1 (by rfl) ⟨1601999, by rfl⟩ : syracuseStep 2135999 = 3203999) B3203999
theorem B2529247 : Blo 1403521 2529247 := bstep (se 1 (by rfl) ⟨1896935, by rfl⟩ : syracuseStep 2529247 = 3793871) B3793871
theorem B91142131 : Blo 1403521 91142131 := bstep (se 1 (by rfl) ⟨68356598, by rfl⟩ : syracuseStep 91142131 = 136713197) B136713197
theorem B5691455 : Blo 1403521 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B8993081 : Blo 1403521 8993081 := bstep (se 2 (by rfl) ⟨3372405, by rfl⟩ : syracuseStep 8993081 = 6744811) B6744811
theorem B10672559 : Blo 1403521 10672559 := bstep (se 1 (by rfl) ⟨8004419, by rfl⟩ : syracuseStep 10672559 = 16008839) B16008839
theorem B48650725 : Blo 1403521 48650725 := bstep (se 4 (by rfl) ⟨4561005, by rfl⟩ : syracuseStep 48650725 = 9122011) B9122011
theorem B1579675 : Blo 1403521 1579675 := bstep (se 1 (by rfl) ⟨1184756, by rfl⟩ : syracuseStep 1579675 = 2369513) B2369513
theorem B13507307 : Blo 1403521 13507307 := bstep (se 1 (by rfl) ⟨10130480, by rfl⟩ : syracuseStep 13507307 = 20260961) B20260961
theorem B93567743 : Blo 1403521 93567743 := bstep (se 1 (by rfl) ⟨70175807, by rfl⟩ : syracuseStep 93567743 = 140351615) B140351615
theorem B12000959 : Blo 1403521 12000959 := bstep (se 1 (by rfl) ⟨9000719, by rfl⟩ : syracuseStep 12000959 = 18001439) B18001439
theorem B4743143 : Blo 1403521 4743143 := bstep (se 1 (by rfl) ⟨3557357, by rfl⟩ : syracuseStep 4743143 = 7114715) B7114715
theorem B6078505 : Blo 1403521 6078505 := bstep (se 2 (by rfl) ⟨2279439, by rfl⟩ : syracuseStep 6078505 = 4558879) B4558879
theorem B2106233 : Blo 1403521 2106233 := bstep (se 2 (by rfl) ⟨789837, by rfl⟩ : syracuseStep 2106233 = 1579675) B1579675
theorem B16000091 : Blo 1403521 16000091 := bstep (se 1 (by rfl) ⟨12000068, by rfl⟩ : syracuseStep 16000091 = 24000137) B24000137
theorem B3794303 : Blo 1403521 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B7112123 : Blo 1403521 7112123 := bstep (se 1 (by rfl) ⟨5334092, by rfl⟩ : syracuseStep 7112123 = 10668185) B10668185
theorem B17319503 : Blo 1403521 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B5334761 : Blo 1403521 5334761 := bstep (se 2 (by rfl) ⟨2000535, by rfl⟩ : syracuseStep 5334761 = 4001071) B4001071
theorem B11994875 : Blo 1403521 11994875 := bstep (se 1 (by rfl) ⟨8996156, by rfl⟩ : syracuseStep 11994875 = 17992313) B17992313
theorem B9004871 : Blo 1403521 9004871 := bstep (se 1 (by rfl) ⟨6753653, by rfl⟩ : syracuseStep 9004871 = 13507307) B13507307
theorem B19220435 : Blo 1403521 19220435 := bstep (se 1 (by rfl) ⟨14415326, by rfl⟩ : syracuseStep 19220435 = 28830653) B28830653
theorem B2001071 : Blo 1403521 2001071 := bstep (se 1 (by rfl) ⟨1500803, by rfl⟩ : syracuseStep 2001071 = 3001607) B3001607
theorem B121522841 : Blo 1403521 121522841 := bstep (se 2 (by rfl) ⟨45571065, by rfl⟩ : syracuseStep 121522841 = 91142131) B91142131
theorem B8538983 : Blo 1403521 8538983 := bstep (se 1 (by rfl) ⟨6404237, by rfl⟩ : syracuseStep 8538983 = 12808475) B12808475
theorem B1404031 : Blo 1403521 1404031 := bstep (se 1 (by rfl) ⟨1053023, by rfl⟩ : syracuseStep 1404031 = 2106047) B2106047
theorem B10128635 : Blo 1403521 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B25989101 : Blo 1403521 25989101 := bstep (se 3 (by rfl) ⟨4872956, by rfl⟩ : syracuseStep 25989101 = 9745913) B9745913
theorem B1405095 : Blo 1403521 1405095 := bstep (se 1 (by rfl) ⟨1053821, by rfl⟩ : syracuseStep 1405095 = 2107643) B2107643
theorem B7115039 : Blo 1403521 7115039 := bstep (se 1 (by rfl) ⟨5336279, by rfl⟩ : syracuseStep 7115039 = 10672559) B10672559
theorem B62378495 : Blo 1403521 62378495 := bstep (se 1 (by rfl) ⟨46783871, by rfl⟩ : syracuseStep 62378495 = 93567743) B93567743
theorem B10121831 : Blo 1403521 10121831 := bstep (se 1 (by rfl) ⟨7591373, by rfl⟩ : syracuseStep 10121831 = 15182747) B15182747
theorem B3158783 : Blo 1403521 3158783 := bstep (se 1 (by rfl) ⟨2369087, by rfl⟩ : syracuseStep 3158783 = 4738175) B4738175
theorem B8000639 : Blo 1403521 8000639 := bstep (se 1 (by rfl) ⟨6000479, by rfl⟩ : syracuseStep 8000639 = 12000959) B12000959
theorem B259470533 : Blo 1403521 259470533 := bstep (se 4 (by rfl) ⟨24325362, by rfl⟩ : syracuseStep 259470533 = 48650725) B48650725
theorem B3372329 : Blo 1403521 3372329 := bstep (se 2 (by rfl) ⟨1264623, by rfl⟩ : syracuseStep 3372329 = 2529247) B2529247
theorem B2668079 : Blo 1403521 2668079 := bstep (se 1 (by rfl) ⟨2001059, by rfl⟩ : syracuseStep 2668079 = 4002119) B4002119
theorem B3159719 : Blo 1403521 3159719 := bstep (se 1 (by rfl) ⟨2369789, by rfl⟩ : syracuseStep 3159719 = 4739579) B4739579
theorem B3552943 : Blo 1403521 3552943 := bstep (se 1 (by rfl) ⟨2664707, by rfl⟩ : syracuseStep 3552943 = 5329415) B5329415
theorem B1423999 : Blo 1403521 1423999 := bstep (se 1 (by rfl) ⟨1067999, by rfl⟩ : syracuseStep 1423999 = 2135999) B2135999
theorem B5061437 : Blo 1403521 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B5331815 : Blo 1403521 5331815 := bstep (se 1 (by rfl) ⟨3998861, by rfl⟩ : syracuseStep 5331815 = 7997723) B7997723
theorem B5995387 : Blo 1403521 5995387 := bstep (se 1 (by rfl) ⟨4496540, by rfl⟩ : syracuseStep 5995387 = 8993081) B8993081
theorem B8002597 : Blo 1403521 8002597 := bstep (se 4 (by rfl) ⟨750243, by rfl⟩ : syracuseStep 8002597 = 1500487) B1500487
theorem B22789633 : Blo 1403521 22789633 := bstep (se 2 (by rfl) ⟨8546112, by rfl⟩ : syracuseStep 22789633 = 17092225) B17092225
theorem B3162095 : Blo 1403521 3162095 := bstep (se 1 (by rfl) ⟨2371571, by rfl⟩ : syracuseStep 3162095 = 4743143) B4743143
theorem B4743359 : Blo 1403521 4743359 := bstep (se 1 (by rfl) ⟨3557519, by rfl⟩ : syracuseStep 4743359 = 7115039) B7115039
theorem B2105855 : Blo 1403521 2105855 := bstep (se 1 (by rfl) ⟨1579391, by rfl⟩ : syracuseStep 2105855 = 3158783) B3158783
theorem B7594661 : Blo 1403521 7594661 := bstep (se 4 (by rfl) ⟨711999, by rfl⟩ : syracuseStep 7594661 = 1423999) B1423999
theorem B10666727 : Blo 1403521 10666727 := bstep (se 1 (by rfl) ⟨8000045, by rfl⟩ : syracuseStep 10666727 = 16000091) B16000091
theorem B5333759 : Blo 1403521 5333759 := bstep (se 1 (by rfl) ⟨4000319, by rfl⟩ : syracuseStep 5333759 = 8000639) B8000639
theorem B10118141 : Blo 1403521 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B2106479 : Blo 1403521 2106479 := bstep (se 1 (by rfl) ⟨1579859, by rfl⟩ : syracuseStep 2106479 = 3159719) B3159719
theorem B3556507 : Blo 1403521 3556507 := bstep (se 1 (by rfl) ⟨2667380, by rfl⟩ : syracuseStep 3556507 = 5334761) B5334761
theorem B7996583 : Blo 1403521 7996583 := bstep (se 1 (by rfl) ⟨5997437, by rfl⟩ : syracuseStep 7996583 = 11994875) B11994875
theorem B12813623 : Blo 1403521 12813623 := bstep (se 1 (by rfl) ⟨9610217, by rfl⟩ : syracuseStep 12813623 = 19220435) B19220435
theorem B30386177 : Blo 1403521 30386177 := bstep (se 2 (by rfl) ⟨11394816, by rfl⟩ : syracuseStep 30386177 = 22789633) B22789633
theorem B6752423 : Blo 1403521 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B4737257 : Blo 1403521 4737257 := bstep (se 2 (by rfl) ⟨1776471, by rfl⟩ : syracuseStep 4737257 = 3552943) B3552943
theorem B2108063 : Blo 1403521 2108063 := bstep (se 1 (by rfl) ⟨1581047, by rfl⟩ : syracuseStep 2108063 = 3162095) B3162095
theorem B8104673 : Blo 1403521 8104673 := bstep (se 2 (by rfl) ⟨3039252, by rfl⟩ : syracuseStep 8104673 = 6078505) B6078505
theorem B41585663 : Blo 1403521 41585663 := bstep (se 1 (by rfl) ⟨31189247, by rfl⟩ : syracuseStep 41585663 = 62378495) B62378495
theorem B5336189 : Blo 1403521 5336189 := bstep (se 3 (by rfl) ⟨1000535, by rfl⟩ : syracuseStep 5336189 = 2001071) B2001071
theorem B1404155 : Blo 1403521 1404155 := bstep (se 1 (by rfl) ⟨1053116, by rfl⟩ : syracuseStep 1404155 = 2106233) B2106233
theorem B2248219 : Blo 1403521 2248219 := bstep (se 1 (by rfl) ⟨1686164, by rfl⟩ : syracuseStep 2248219 = 3372329) B3372329
theorem B11546335 : Blo 1403521 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B10670129 : Blo 1403521 10670129 := bstep (se 2 (by rfl) ⟨4001298, by rfl⟩ : syracuseStep 10670129 = 8002597) B8002597
theorem B7114877 : Blo 1403521 7114877 := bstep (se 3 (by rfl) ⟨1334039, by rfl⟩ : syracuseStep 7114877 = 2668079) B2668079
theorem B81015227 : Blo 1403521 81015227 := bstep (se 1 (by rfl) ⟨60761420, by rfl⟩ : syracuseStep 81015227 = 121522841) B121522841
theorem B6747887 : Blo 1403521 6747887 := bstep (se 1 (by rfl) ⟨5060915, by rfl⟩ : syracuseStep 6747887 = 10121831) B10121831
theorem B172980355 : Blo 1403521 172980355 := bstep (se 1 (by rfl) ⟨129735266, by rfl⟩ : syracuseStep 172980355 = 259470533) B259470533
theorem B4741415 : Blo 1403521 4741415 := bstep (se 1 (by rfl) ⟨3556061, by rfl⟩ : syracuseStep 4741415 = 7112123) B7112123
theorem B7993849 : Blo 1403521 7993849 := bstep (se 2 (by rfl) ⟨2997693, by rfl⟩ : syracuseStep 7993849 = 5995387) B5995387
theorem B6003247 : Blo 1403521 6003247 := bstep (se 1 (by rfl) ⟨4502435, by rfl⟩ : syracuseStep 6003247 = 9004871) B9004871
theorem B3374291 : Blo 1403521 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B5692655 : Blo 1403521 5692655 := bstep (se 1 (by rfl) ⟨4269491, by rfl⟩ : syracuseStep 5692655 = 8538983) B8538983
theorem B3554543 : Blo 1403521 3554543 := bstep (se 1 (by rfl) ⟨2665907, by rfl⟩ : syracuseStep 3554543 = 5331815) B5331815
theorem B17326067 : Blo 1403521 17326067 := bstep (se 1 (by rfl) ⟨12994550, by rfl⟩ : syracuseStep 17326067 = 25989101) B25989101
theorem B4743251 : Blo 1403521 4743251 := bstep (se 1 (by rfl) ⟨3557438, by rfl⟩ : syracuseStep 4743251 = 7114877) B7114877
theorem B3162239 : Blo 1403521 3162239 := bstep (se 1 (by rfl) ⟨2371679, by rfl⟩ : syracuseStep 3162239 = 4743359) B4743359
theorem B54010151 : Blo 1403521 54010151 := bstep (se 1 (by rfl) ⟨40507613, by rfl⟩ : syracuseStep 54010151 = 81015227) B81015227
theorem B18006461 : Blo 1403521 18006461 := bstep (se 3 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 18006461 = 6752423) B6752423
theorem B5063107 : Blo 1403521 5063107 := bstep (se 1 (by rfl) ⟨3797330, by rfl⟩ : syracuseStep 5063107 = 7594661) B7594661
theorem B7111151 : Blo 1403521 7111151 := bstep (se 1 (by rfl) ⟨5333363, by rfl⟩ : syracuseStep 7111151 = 10666727) B10666727
theorem B3555839 : Blo 1403521 3555839 := bstep (se 1 (by rfl) ⟨2666879, by rfl⟩ : syracuseStep 3555839 = 5333759) B5333759
theorem B10658465 : Blo 1403521 10658465 := bstep (se 2 (by rfl) ⟨3996924, by rfl⟩ : syracuseStep 10658465 = 7993849) B7993849
theorem B8004329 : Blo 1403521 8004329 := bstep (se 2 (by rfl) ⟨3001623, by rfl⟩ : syracuseStep 8004329 = 6003247) B6003247
theorem B4498591 : Blo 1403521 4498591 := bstep (se 1 (by rfl) ⟨3373943, by rfl⟩ : syracuseStep 4498591 = 6747887) B6747887
theorem B3557459 : Blo 1403521 3557459 := bstep (se 1 (by rfl) ⟨2668094, by rfl⟩ : syracuseStep 3557459 = 5336189) B5336189
theorem B3795103 : Blo 1403521 3795103 := bstep (se 1 (by rfl) ⟨2846327, by rfl⟩ : syracuseStep 3795103 = 5692655) B5692655
theorem B2369695 : Blo 1403521 2369695 := bstep (se 1 (by rfl) ⟨1777271, by rfl⟩ : syracuseStep 2369695 = 3554543) B3554543
theorem B15395113 : Blo 1403521 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B7113419 : Blo 1403521 7113419 := bstep (se 1 (by rfl) ⟨5335064, by rfl⟩ : syracuseStep 7113419 = 10670129) B10670129
theorem B230640473 : Blo 1403521 230640473 := bstep (se 2 (by rfl) ⟨86490177, by rfl⟩ : syracuseStep 230640473 = 172980355) B172980355
theorem B1403903 : Blo 1403521 1403903 := bstep (se 1 (by rfl) ⟨1052927, by rfl⟩ : syracuseStep 1403903 = 2105855) B2105855
theorem B6745427 : Blo 1403521 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B1404319 : Blo 1403521 1404319 := bstep (se 1 (by rfl) ⟨1053239, by rfl⟩ : syracuseStep 1404319 = 2106479) B2106479
theorem B3158171 : Blo 1403521 3158171 := bstep (se 1 (by rfl) ⟨2368628, by rfl⟩ : syracuseStep 3158171 = 4737257) B4737257
theorem B1405375 : Blo 1403521 1405375 := bstep (se 1 (by rfl) ⟨1054031, by rfl⟩ : syracuseStep 1405375 = 2108063) B2108063
theorem B5403115 : Blo 1403521 5403115 := bstep (se 1 (by rfl) ⟨4052336, by rfl⟩ : syracuseStep 5403115 = 8104673) B8104673
theorem B2249527 : Blo 1403521 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B11990501 : Blo 1403521 11990501 := bstep (se 4 (by rfl) ⟨1124109, by rfl⟩ : syracuseStep 11990501 = 2248219) B2248219
theorem B5331055 : Blo 1403521 5331055 := bstep (se 1 (by rfl) ⟨3998291, by rfl⟩ : syracuseStep 5331055 = 7996583) B7996583
theorem B8542415 : Blo 1403521 8542415 := bstep (se 1 (by rfl) ⟨6406811, by rfl⟩ : syracuseStep 8542415 = 12813623) B12813623
theorem B20257451 : Blo 1403521 20257451 := bstep (se 1 (by rfl) ⟨15193088, by rfl⟩ : syracuseStep 20257451 = 30386177) B30386177
theorem B3160943 : Blo 1403521 3160943 := bstep (se 1 (by rfl) ⟨2370707, by rfl⟩ : syracuseStep 3160943 = 4741415) B4741415
theorem B4742009 : Blo 1403521 4742009 := bstep (se 2 (by rfl) ⟨1778253, by rfl⟩ : syracuseStep 4742009 = 3556507) B3556507
theorem B46202845 : Blo 1403521 46202845 := bstep (se 3 (by rfl) ⟨8663033, by rfl⟩ : syracuseStep 46202845 = 17326067) B17326067
theorem B110895101 : Blo 1403521 110895101 := bstep (se 3 (by rfl) ⟨20792831, by rfl⟩ : syracuseStep 110895101 = 41585663) B41585663
theorem B3162167 : Blo 1403521 3162167 := bstep (se 1 (by rfl) ⟨2371625, by rfl⟩ : syracuseStep 3162167 = 4743251) B4743251
theorem B2105447 : Blo 1403521 2105447 := bstep (se 1 (by rfl) ⟨1579085, by rfl⟩ : syracuseStep 2105447 = 3158171) B3158171
theorem B6750809 : Blo 1403521 6750809 := bstep (se 2 (by rfl) ⟨2531553, by rfl⟩ : syracuseStep 6750809 = 5063107) B5063107
theorem B2999369 : Blo 1403521 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B5694943 : Blo 1403521 5694943 := bstep (se 1 (by rfl) ⟨4271207, by rfl⟩ : syracuseStep 5694943 = 8542415) B8542415
theorem B5998121 : Blo 1403521 5998121 := bstep (se 2 (by rfl) ⟨2249295, by rfl⟩ : syracuseStep 5998121 = 4498591) B4498591
theorem B2107295 : Blo 1403521 2107295 := bstep (se 1 (by rfl) ⟨1580471, by rfl⟩ : syracuseStep 2107295 = 3160943) B3160943
theorem B2108159 : Blo 1403521 2108159 := bstep (se 1 (by rfl) ⟨1581119, by rfl⟩ : syracuseStep 2108159 = 3162239) B3162239
theorem B36006767 : Blo 1403521 36006767 := bstep (se 1 (by rfl) ⟨27005075, by rfl⟩ : syracuseStep 36006767 = 54010151) B54010151
theorem B12004307 : Blo 1403521 12004307 := bstep (se 1 (by rfl) ⟨9003230, by rfl⟩ : syracuseStep 12004307 = 18006461) B18006461
theorem B2370559 : Blo 1403521 2370559 := bstep (se 1 (by rfl) ⟨1777919, by rfl⟩ : syracuseStep 2370559 = 3555839) B3555839
theorem B7105643 : Blo 1403521 7105643 := bstep (se 1 (by rfl) ⟨5329232, by rfl⟩ : syracuseStep 7105643 = 10658465) B10658465
theorem B5336219 : Blo 1403521 5336219 := bstep (se 1 (by rfl) ⟨4002164, by rfl⟩ : syracuseStep 5336219 = 8004329) B8004329
theorem B7204153 : Blo 1403521 7204153 := bstep (se 2 (by rfl) ⟨2701557, by rfl⟩ : syracuseStep 7204153 = 5403115) B5403115
theorem B2371639 : Blo 1403521 2371639 := bstep (se 1 (by rfl) ⟨1778729, by rfl⟩ : syracuseStep 2371639 = 3557459) B3557459
theorem B13504967 : Blo 1403521 13504967 := bstep (se 1 (by rfl) ⟨10128725, by rfl⟩ : syracuseStep 13504967 = 20257451) B20257451
theorem B153760315 : Blo 1403521 153760315 := bstep (se 1 (by rfl) ⟨115320236, by rfl⟩ : syracuseStep 153760315 = 230640473) B230640473
theorem B73930067 : Blo 1403521 73930067 := bstep (se 1 (by rfl) ⟨55447550, by rfl⟩ : syracuseStep 73930067 = 110895101) B110895101
theorem B7108073 : Blo 1403521 7108073 := bstep (se 2 (by rfl) ⟨2665527, by rfl⟩ : syracuseStep 7108073 = 5331055) B5331055
theorem B3159593 : Blo 1403521 3159593 := bstep (se 2 (by rfl) ⟨1184847, by rfl⟩ : syracuseStep 3159593 = 2369695) B2369695
theorem B4740767 : Blo 1403521 4740767 := bstep (se 1 (by rfl) ⟨3555575, by rfl⟩ : syracuseStep 4740767 = 7111151) B7111151
theorem B20526817 : Blo 1403521 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B20240549 : Blo 1403521 20240549 := bstep (se 4 (by rfl) ⟨1897551, by rfl⟩ : syracuseStep 20240549 = 3795103) B3795103
theorem B7993667 : Blo 1403521 7993667 := bstep (se 1 (by rfl) ⟨5995250, by rfl⟩ : syracuseStep 7993667 = 11990501) B11990501
theorem B4742279 : Blo 1403521 4742279 := bstep (se 1 (by rfl) ⟨3556709, by rfl⟩ : syracuseStep 4742279 = 7113419) B7113419
theorem B3161339 : Blo 1403521 3161339 := bstep (se 1 (by rfl) ⟨2371004, by rfl⟩ : syracuseStep 3161339 = 4742009) B4742009
theorem B4496951 : Blo 1403521 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B61603793 : Blo 1403521 61603793 := bstep (se 2 (by rfl) ⟨23101422, by rfl⟩ : syracuseStep 61603793 = 46202845) B46202845
theorem B3162185 : Blo 1403521 3162185 := bstep (se 2 (by rfl) ⟨1185819, by rfl⟩ : syracuseStep 3162185 = 2371639) B2371639
theorem B9003311 : Blo 1403521 9003311 := bstep (se 1 (by rfl) ⟨6752483, by rfl⟩ : syracuseStep 9003311 = 13504967) B13504967
theorem B1999579 : Blo 1403521 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B205013753 : Blo 1403521 205013753 := bstep (se 2 (by rfl) ⟨76880157, by rfl⟩ : syracuseStep 205013753 = 153760315) B153760315
theorem B3998747 : Blo 1403521 3998747 := bstep (se 1 (by rfl) ⟨2999060, by rfl⟩ : syracuseStep 3998747 = 5998121) B5998121
theorem B2106395 : Blo 1403521 2106395 := bstep (se 1 (by rfl) ⟨1579796, by rfl⟩ : syracuseStep 2106395 = 3159593) B3159593
theorem B13493699 : Blo 1403521 13493699 := bstep (se 1 (by rfl) ⟨10120274, by rfl⟩ : syracuseStep 13493699 = 20240549) B20240549
theorem B24004511 : Blo 1403521 24004511 := bstep (se 1 (by rfl) ⟨18003383, by rfl⟩ : syracuseStep 24004511 = 36006767) B36006767
theorem B4737095 : Blo 1403521 4737095 := bstep (se 1 (by rfl) ⟨3552821, by rfl⟩ : syracuseStep 4737095 = 7105643) B7105643
theorem B3557479 : Blo 1403521 3557479 := bstep (se 1 (by rfl) ⟨2668109, by rfl⟩ : syracuseStep 3557479 = 5336219) B5336219
theorem B2107559 : Blo 1403521 2107559 := bstep (se 1 (by rfl) ⟨1580669, by rfl⟩ : syracuseStep 2107559 = 3161339) B3161339
theorem B41069195 : Blo 1403521 41069195 := bstep (se 1 (by rfl) ⟨30801896, by rfl⟩ : syracuseStep 41069195 = 61603793) B61603793
theorem B2108111 : Blo 1403521 2108111 := bstep (se 1 (by rfl) ⟨1581083, by rfl⟩ : syracuseStep 2108111 = 3162167) B3162167
theorem B1403631 : Blo 1403521 1403631 := bstep (se 1 (by rfl) ⟨1052723, by rfl⟩ : syracuseStep 1403631 = 2105447) B2105447
theorem B4500539 : Blo 1403521 4500539 := bstep (se 1 (by rfl) ⟨3375404, by rfl⟩ : syracuseStep 4500539 = 6750809) B6750809
theorem B49286711 : Blo 1403521 49286711 := bstep (se 1 (by rfl) ⟨36965033, by rfl⟩ : syracuseStep 49286711 = 73930067) B73930067
theorem B4738715 : Blo 1403521 4738715 := bstep (se 1 (by rfl) ⟨3554036, by rfl⟩ : syracuseStep 4738715 = 7108073) B7108073
theorem B1404863 : Blo 1403521 1404863 := bstep (se 1 (by rfl) ⟨1053647, by rfl⟩ : syracuseStep 1404863 = 2107295) B2107295
theorem B5329111 : Blo 1403521 5329111 := bstep (se 1 (by rfl) ⟨3996833, by rfl⟩ : syracuseStep 5329111 = 7993667) B7993667
theorem B9605537 : Blo 1403521 9605537 := bstep (se 2 (by rfl) ⟨3602076, by rfl⟩ : syracuseStep 9605537 = 7204153) B7204153
theorem B1405439 : Blo 1403521 1405439 := bstep (se 1 (by rfl) ⟨1054079, by rfl⟩ : syracuseStep 1405439 = 2108159) B2108159
theorem B3160511 : Blo 1403521 3160511 := bstep (se 1 (by rfl) ⟨2370383, by rfl⟩ : syracuseStep 3160511 = 4740767) B4740767
theorem B3160745 : Blo 1403521 3160745 := bstep (se 2 (by rfl) ⟨1185279, by rfl⟩ : syracuseStep 3160745 = 2370559) B2370559
theorem B7593257 : Blo 1403521 7593257 := bstep (se 2 (by rfl) ⟨2847471, by rfl⟩ : syracuseStep 7593257 = 5694943) B5694943
theorem B8002871 : Blo 1403521 8002871 := bstep (se 1 (by rfl) ⟨6002153, by rfl⟩ : syracuseStep 8002871 = 12004307) B12004307
theorem B3161519 : Blo 1403521 3161519 := bstep (se 1 (by rfl) ⟨2371139, by rfl⟩ : syracuseStep 3161519 = 4742279) B4742279
theorem B27369089 : Blo 1403521 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B2997967 : Blo 1403521 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B4743305 : Blo 1403521 4743305 := bstep (se 2 (by rfl) ⟨1778739, by rfl⟩ : syracuseStep 4743305 = 3557479) B3557479
theorem B136675835 : Blo 1403521 136675835 := bstep (se 1 (by rfl) ⟨102506876, by rfl⟩ : syracuseStep 136675835 = 205013753) B205013753
theorem B8995799 : Blo 1403521 8995799 := bstep (se 1 (by rfl) ⟨6746849, by rfl⟩ : syracuseStep 8995799 = 13493699) B13493699
theorem B2107007 : Blo 1403521 2107007 := bstep (se 1 (by rfl) ⟨1580255, by rfl⟩ : syracuseStep 2107007 = 3160511) B3160511
theorem B27379463 : Blo 1403521 27379463 := bstep (se 1 (by rfl) ⟨20534597, by rfl⟩ : syracuseStep 27379463 = 41069195) B41069195
theorem B2107163 : Blo 1403521 2107163 := bstep (se 1 (by rfl) ⟨1580372, by rfl⟩ : syracuseStep 2107163 = 3160745) B3160745
theorem B3000359 : Blo 1403521 3000359 := bstep (se 1 (by rfl) ⟨2250269, by rfl⟩ : syracuseStep 3000359 = 4500539) B4500539
theorem B5335247 : Blo 1403521 5335247 := bstep (se 1 (by rfl) ⟨4001435, by rfl⟩ : syracuseStep 5335247 = 8002871) B8002871
theorem B2107679 : Blo 1403521 2107679 := bstep (se 1 (by rfl) ⟨1580759, by rfl⟩ : syracuseStep 2107679 = 3161519) B3161519
theorem B18246059 : Blo 1403521 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B2108123 : Blo 1403521 2108123 := bstep (se 1 (by rfl) ⟨1581092, by rfl⟩ : syracuseStep 2108123 = 3162185) B3162185
theorem B7105481 : Blo 1403521 7105481 := bstep (se 2 (by rfl) ⟨2664555, by rfl⟩ : syracuseStep 7105481 = 5329111) B5329111
theorem B1404263 : Blo 1403521 1404263 := bstep (se 1 (by rfl) ⟨1053197, by rfl⟩ : syracuseStep 1404263 = 2106395) B2106395
theorem B2666105 : Blo 1403521 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B16003007 : Blo 1403521 16003007 := bstep (se 1 (by rfl) ⟨12002255, by rfl⟩ : syracuseStep 16003007 = 24004511) B24004511
theorem B3158063 : Blo 1403521 3158063 := bstep (se 1 (by rfl) ⟨2368547, by rfl⟩ : syracuseStep 3158063 = 4737095) B4737095
theorem B1405039 : Blo 1403521 1405039 := bstep (se 1 (by rfl) ⟨1053779, by rfl⟩ : syracuseStep 1405039 = 2107559) B2107559
theorem B1405407 : Blo 1403521 1405407 := bstep (se 1 (by rfl) ⟨1054055, by rfl⟩ : syracuseStep 1405407 = 2108111) B2108111
theorem B3159143 : Blo 1403521 3159143 := bstep (se 1 (by rfl) ⟨2369357, by rfl⟩ : syracuseStep 3159143 = 4738715) B4738715
theorem B10663325 : Blo 1403521 10663325 := bstep (se 3 (by rfl) ⟨1999373, by rfl⟩ : syracuseStep 10663325 = 3998747) B3998747
theorem B6002207 : Blo 1403521 6002207 := bstep (se 1 (by rfl) ⟨4501655, by rfl⟩ : syracuseStep 6002207 = 9003311) B9003311
theorem B6403691 : Blo 1403521 6403691 := bstep (se 1 (by rfl) ⟨4802768, by rfl⟩ : syracuseStep 6403691 = 9605537) B9605537
theorem B5062171 : Blo 1403521 5062171 := bstep (se 1 (by rfl) ⟨3796628, by rfl⟩ : syracuseStep 5062171 = 7593257) B7593257
theorem B3997289 : Blo 1403521 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B32857807 : Blo 1403521 32857807 := bstep (se 1 (by rfl) ⟨24643355, by rfl⟩ : syracuseStep 32857807 = 49286711) B49286711
theorem B2105375 : Blo 1403521 2105375 := bstep (se 1 (by rfl) ⟨1579031, by rfl⟩ : syracuseStep 2105375 = 3158063) B3158063
theorem B3162203 : Blo 1403521 3162203 := bstep (se 1 (by rfl) ⟨2371652, by rfl⟩ : syracuseStep 3162203 = 4743305) B4743305
theorem B5997199 : Blo 1403521 5997199 := bstep (se 1 (by rfl) ⟨4497899, by rfl⟩ : syracuseStep 5997199 = 8995799) B8995799
theorem B2106095 : Blo 1403521 2106095 := bstep (se 1 (by rfl) ⟨1579571, by rfl⟩ : syracuseStep 2106095 = 3159143) B3159143
theorem B4269127 : Blo 1403521 4269127 := bstep (se 1 (by rfl) ⟨3201845, by rfl⟩ : syracuseStep 4269127 = 6403691) B6403691
theorem B3556831 : Blo 1403521 3556831 := bstep (se 1 (by rfl) ⟨2667623, by rfl⟩ : syracuseStep 3556831 = 5335247) B5335247
theorem B10659437 : Blo 1403521 10659437 := bstep (se 3 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 10659437 = 3997289) B3997289
theorem B4736987 : Blo 1403521 4736987 := bstep (se 1 (by rfl) ⟨3552740, by rfl⟩ : syracuseStep 4736987 = 7105481) B7105481
theorem B10668671 : Blo 1403521 10668671 := bstep (se 1 (by rfl) ⟨8001503, by rfl⟩ : syracuseStep 10668671 = 16003007) B16003007
theorem B4001471 : Blo 1403521 4001471 := bstep (se 1 (by rfl) ⟨3001103, by rfl⟩ : syracuseStep 4001471 = 6002207) B6002207
theorem B1404671 : Blo 1403521 1404671 := bstep (se 1 (by rfl) ⟨1053503, by rfl⟩ : syracuseStep 1404671 = 2107007) B2107007
theorem B1404775 : Blo 1403521 1404775 := bstep (se 1 (by rfl) ⟨1053581, by rfl⟩ : syracuseStep 1404775 = 2107163) B2107163
theorem B1405119 : Blo 1403521 1405119 := bstep (se 1 (by rfl) ⟨1053839, by rfl⟩ : syracuseStep 1405119 = 2107679) B2107679
theorem B1405415 : Blo 1403521 1405415 := bstep (se 1 (by rfl) ⟨1054061, by rfl⟩ : syracuseStep 1405415 = 2108123) B2108123
theorem B73011901 : Blo 1403521 73011901 := bstep (se 3 (by rfl) ⟨13689731, by rfl⟩ : syracuseStep 73011901 = 27379463) B27379463
theorem B8000957 : Blo 1403521 8000957 := bstep (se 3 (by rfl) ⟨1500179, by rfl⟩ : syracuseStep 8000957 = 3000359) B3000359
theorem B91117223 : Blo 1403521 91117223 := bstep (se 1 (by rfl) ⟨68337917, by rfl⟩ : syracuseStep 91117223 = 136675835) B136675835
theorem B7108883 : Blo 1403521 7108883 := bstep (se 1 (by rfl) ⟨5331662, by rfl⟩ : syracuseStep 7108883 = 10663325) B10663325
theorem B12164039 : Blo 1403521 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B6749561 : Blo 1403521 6749561 := bstep (se 2 (by rfl) ⟨2531085, by rfl⟩ : syracuseStep 6749561 = 5062171) B5062171
theorem B43810409 : Blo 1403521 43810409 := bstep (se 2 (by rfl) ⟨16428903, by rfl⟩ : syracuseStep 43810409 = 32857807) B32857807
theorem B1777403 : Blo 1403521 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B7996265 : Blo 1403521 7996265 := bstep (se 2 (by rfl) ⟨2998599, by rfl⟩ : syracuseStep 7996265 = 5997199) B5997199
theorem B5333971 : Blo 1403521 5333971 := bstep (se 1 (by rfl) ⟨4000478, by rfl⟩ : syracuseStep 5333971 = 8000957) B8000957
theorem B60744815 : Blo 1403521 60744815 := bstep (se 1 (by rfl) ⟨45558611, by rfl⟩ : syracuseStep 60744815 = 91117223) B91117223
theorem B116827757 : Blo 1403521 116827757 := bstep (se 3 (by rfl) ⟨21905204, by rfl⟩ : syracuseStep 116827757 = 43810409) B43810409
theorem B7112447 : Blo 1403521 7112447 := bstep (se 1 (by rfl) ⟨5334335, by rfl⟩ : syracuseStep 7112447 = 10668671) B10668671
theorem B4499707 : Blo 1403521 4499707 := bstep (se 1 (by rfl) ⟨3374780, by rfl⟩ : syracuseStep 4499707 = 6749561) B6749561
theorem B1403583 : Blo 1403521 1403583 := bstep (se 1 (by rfl) ⟨1052687, by rfl⟩ : syracuseStep 1403583 = 2105375) B2105375
theorem B2108135 : Blo 1403521 2108135 := bstep (se 1 (by rfl) ⟨1581101, by rfl⟩ : syracuseStep 2108135 = 3162203) B3162203
theorem B1404063 : Blo 1403521 1404063 := bstep (se 1 (by rfl) ⟨1053047, by rfl⟩ : syracuseStep 1404063 = 2106095) B2106095
theorem B97349201 : Blo 1403521 97349201 := bstep (se 2 (by rfl) ⟨36505950, by rfl⟩ : syracuseStep 97349201 = 73011901) B73011901
theorem B7106291 : Blo 1403521 7106291 := bstep (se 1 (by rfl) ⟨5329718, by rfl⟩ : syracuseStep 7106291 = 10659437) B10659437
theorem B3157991 : Blo 1403521 3157991 := bstep (se 1 (by rfl) ⟨2368493, by rfl⟩ : syracuseStep 3157991 = 4736987) B4736987
theorem B4739255 : Blo 1403521 4739255 := bstep (se 1 (by rfl) ⟨3554441, by rfl⟩ : syracuseStep 4739255 = 7108883) B7108883
theorem B4739741 : Blo 1403521 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B2667647 : Blo 1403521 2667647 := bstep (se 1 (by rfl) ⟨2000735, by rfl⟩ : syracuseStep 2667647 = 4001471) B4001471
theorem B5692169 : Blo 1403521 5692169 := bstep (se 2 (by rfl) ⟨2134563, by rfl⟩ : syracuseStep 5692169 = 4269127) B4269127
theorem B4742441 : Blo 1403521 4742441 := bstep (se 2 (by rfl) ⟨1778415, by rfl⟩ : syracuseStep 4742441 = 3556831) B3556831
theorem B8109359 : Blo 1403521 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B1778431 : Blo 1403521 1778431 := bstep (se 1 (by rfl) ⟨1333823, by rfl⟩ : syracuseStep 1778431 = 2667647) B2667647
theorem B7111961 : Blo 1403521 7111961 := bstep (se 2 (by rfl) ⟨2666985, by rfl⟩ : syracuseStep 7111961 = 5333971) B5333971
theorem B3794779 : Blo 1403521 3794779 := bstep (se 1 (by rfl) ⟨2846084, by rfl⟩ : syracuseStep 3794779 = 5692169) B5692169
theorem B64899467 : Blo 1403521 64899467 := bstep (se 1 (by rfl) ⟨48674600, by rfl⟩ : syracuseStep 64899467 = 97349201) B97349201
theorem B4737527 : Blo 1403521 4737527 := bstep (se 1 (by rfl) ⟨3553145, by rfl⟩ : syracuseStep 4737527 = 7106291) B7106291
theorem B5999609 : Blo 1403521 5999609 := bstep (se 2 (by rfl) ⟨2249853, by rfl⟩ : syracuseStep 5999609 = 4499707) B4499707
theorem B40496543 : Blo 1403521 40496543 := bstep (se 1 (by rfl) ⟨30372407, by rfl⟩ : syracuseStep 40496543 = 60744815) B60744815
theorem B77885171 : Blo 1403521 77885171 := bstep (se 1 (by rfl) ⟨58413878, by rfl⟩ : syracuseStep 77885171 = 116827757) B116827757
theorem B1405423 : Blo 1403521 1405423 := bstep (se 1 (by rfl) ⟨1054067, by rfl⟩ : syracuseStep 1405423 = 2108135) B2108135
theorem B3159503 : Blo 1403521 3159503 := bstep (se 1 (by rfl) ⟨2369627, by rfl⟩ : syracuseStep 3159503 = 4739255) B4739255
theorem B3159827 : Blo 1403521 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B5330843 : Blo 1403521 5330843 := bstep (se 1 (by rfl) ⟨3998132, by rfl⟩ : syracuseStep 5330843 = 7996265) B7996265
theorem B4741631 : Blo 1403521 4741631 := bstep (se 1 (by rfl) ⟨3556223, by rfl⟩ : syracuseStep 4741631 = 7112447) B7112447
theorem B3161627 : Blo 1403521 3161627 := bstep (se 1 (by rfl) ⟨2371220, by rfl⟩ : syracuseStep 3161627 = 4742441) B4742441
theorem B5406239 : Blo 1403521 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B2105327 : Blo 1403521 2105327 := bstep (se 1 (by rfl) ⟨1578995, by rfl⟩ : syracuseStep 2105327 = 3157991) B3157991
theorem B2106335 : Blo 1403521 2106335 := bstep (se 1 (by rfl) ⟨1579751, by rfl⟩ : syracuseStep 2106335 = 3159503) B3159503
theorem B2106551 : Blo 1403521 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B3999739 : Blo 1403521 3999739 := bstep (se 1 (by rfl) ⟨2999804, by rfl⟩ : syracuseStep 3999739 = 5999609) B5999609
theorem B2107751 : Blo 1403521 2107751 := bstep (se 1 (by rfl) ⟨1580813, by rfl⟩ : syracuseStep 2107751 = 3161627) B3161627
theorem B51923447 : Blo 1403521 51923447 := bstep (se 1 (by rfl) ⟨38942585, by rfl⟩ : syracuseStep 51923447 = 77885171) B77885171
theorem B1403551 : Blo 1403521 1403551 := bstep (se 1 (by rfl) ⟨1052663, by rfl⟩ : syracuseStep 1403551 = 2105327) B2105327
theorem B2371241 : Blo 1403521 2371241 := bstep (se 2 (by rfl) ⟨889215, by rfl⟩ : syracuseStep 2371241 = 1778431) B1778431
theorem B43266311 : Blo 1403521 43266311 := bstep (se 1 (by rfl) ⟨32449733, by rfl⟩ : syracuseStep 43266311 = 64899467) B64899467
theorem B3158351 : Blo 1403521 3158351 := bstep (se 1 (by rfl) ⟨2368763, by rfl⟩ : syracuseStep 3158351 = 4737527) B4737527
theorem B26997695 : Blo 1403521 26997695 := bstep (se 1 (by rfl) ⟨20248271, by rfl⟩ : syracuseStep 26997695 = 40496543) B40496543
theorem B5059705 : Blo 1403521 5059705 := bstep (se 2 (by rfl) ⟨1897389, by rfl⟩ : syracuseStep 5059705 = 3794779) B3794779
theorem B4741307 : Blo 1403521 4741307 := bstep (se 1 (by rfl) ⟨3555980, by rfl⟩ : syracuseStep 4741307 = 7111961) B7111961
theorem B3553895 : Blo 1403521 3553895 := bstep (se 1 (by rfl) ⟨2665421, by rfl⟩ : syracuseStep 3553895 = 5330843) B5330843
theorem B3161087 : Blo 1403521 3161087 := bstep (se 1 (by rfl) ⟨2370815, by rfl⟩ : syracuseStep 3161087 = 4741631) B4741631
theorem B3604159 : Blo 1403521 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B28844207 : Blo 1403521 28844207 := bstep (se 1 (by rfl) ⟨21633155, by rfl⟩ : syracuseStep 28844207 = 43266311) B43266311
theorem B2105567 : Blo 1403521 2105567 := bstep (se 1 (by rfl) ⟨1579175, by rfl⟩ : syracuseStep 2105567 = 3158351) B3158351
theorem B17998463 : Blo 1403521 17998463 := bstep (se 1 (by rfl) ⟨13498847, by rfl⟩ : syracuseStep 17998463 = 26997695) B26997695
theorem B2369263 : Blo 1403521 2369263 := bstep (se 1 (by rfl) ⟨1776947, by rfl⟩ : syracuseStep 2369263 = 3553895) B3553895
theorem B2107391 : Blo 1403521 2107391 := bstep (se 1 (by rfl) ⟨1580543, by rfl⟩ : syracuseStep 2107391 = 3161087) B3161087
theorem B1404223 : Blo 1403521 1404223 := bstep (se 1 (by rfl) ⟨1053167, by rfl⟩ : syracuseStep 1404223 = 2106335) B2106335
theorem B1404367 : Blo 1403521 1404367 := bstep (se 1 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 1404367 = 2106551) B2106551
theorem B19222181 : Blo 1403521 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B6746273 : Blo 1403521 6746273 := bstep (se 2 (by rfl) ⟨2529852, by rfl⟩ : syracuseStep 6746273 = 5059705) B5059705
theorem B1405167 : Blo 1403521 1405167 := bstep (se 1 (by rfl) ⟨1053875, by rfl⟩ : syracuseStep 1405167 = 2107751) B2107751
theorem B34615631 : Blo 1403521 34615631 := bstep (se 1 (by rfl) ⟨25961723, by rfl⟩ : syracuseStep 34615631 = 51923447) B51923447
theorem B3160871 : Blo 1403521 3160871 := bstep (se 1 (by rfl) ⟨2370653, by rfl⟩ : syracuseStep 3160871 = 4741307) B4741307
theorem B1580827 : Blo 1403521 1580827 := bstep (se 1 (by rfl) ⟨1185620, by rfl⟩ : syracuseStep 1580827 = 2371241) B2371241
theorem B5332985 : Blo 1403521 5332985 := bstep (se 2 (by rfl) ⟨1999869, by rfl⟩ : syracuseStep 5332985 = 3999739) B3999739
theorem B4497515 : Blo 1403521 4497515 := bstep (se 1 (by rfl) ⟨3373136, by rfl⟩ : syracuseStep 4497515 = 6746273) B6746273
theorem B92308349 : Blo 1403521 92308349 := bstep (se 3 (by rfl) ⟨17307815, by rfl⟩ : syracuseStep 92308349 = 34615631) B34615631
theorem B2107247 : Blo 1403521 2107247 := bstep (se 1 (by rfl) ⟨1580435, by rfl⟩ : syracuseStep 2107247 = 3160871) B3160871
theorem B2107769 : Blo 1403521 2107769 := bstep (se 2 (by rfl) ⟨790413, by rfl⟩ : syracuseStep 2107769 = 1580827) B1580827
theorem B12814787 : Blo 1403521 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B19229471 : Blo 1403521 19229471 := bstep (se 1 (by rfl) ⟨14422103, by rfl⟩ : syracuseStep 19229471 = 28844207) B28844207
theorem B1403711 : Blo 1403521 1403711 := bstep (se 1 (by rfl) ⟨1052783, by rfl⟩ : syracuseStep 1403711 = 2105567) B2105567
theorem B1404927 : Blo 1403521 1404927 := bstep (se 1 (by rfl) ⟨1053695, by rfl⟩ : syracuseStep 1404927 = 2107391) B2107391
theorem B3555323 : Blo 1403521 3555323 := bstep (se 1 (by rfl) ⟨2666492, by rfl⟩ : syracuseStep 3555323 = 5332985) B5332985
theorem B3159017 : Blo 1403521 3159017 := bstep (se 2 (by rfl) ⟨1184631, by rfl⟩ : syracuseStep 3159017 = 2369263) B2369263
theorem B11998975 : Blo 1403521 11998975 := bstep (se 1 (by rfl) ⟨8999231, by rfl⟩ : syracuseStep 11998975 = 17998463) B17998463
theorem B2998343 : Blo 1403521 2998343 := bstep (se 1 (by rfl) ⟨2248757, by rfl⟩ : syracuseStep 2998343 = 4497515) B4497515
theorem B61538899 : Blo 1403521 61538899 := bstep (se 1 (by rfl) ⟨46154174, by rfl⟩ : syracuseStep 61538899 = 92308349) B92308349
theorem B2106011 : Blo 1403521 2106011 := bstep (se 1 (by rfl) ⟨1579508, by rfl⟩ : syracuseStep 2106011 = 3159017) B3159017
theorem B2370215 : Blo 1403521 2370215 := bstep (se 1 (by rfl) ⟨1777661, by rfl⟩ : syracuseStep 2370215 = 3555323) B3555323
theorem B34172765 : Blo 1403521 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B1404831 : Blo 1403521 1404831 := bstep (se 1 (by rfl) ⟨1053623, by rfl⟩ : syracuseStep 1404831 = 2107247) B2107247
theorem B1405179 : Blo 1403521 1405179 := bstep (se 1 (by rfl) ⟨1053884, by rfl⟩ : syracuseStep 1405179 = 2107769) B2107769
theorem B12819647 : Blo 1403521 12819647 := bstep (se 1 (by rfl) ⟨9614735, by rfl⟩ : syracuseStep 12819647 = 19229471) B19229471
theorem B15998633 : Blo 1403521 15998633 := bstep (se 2 (by rfl) ⟨5999487, by rfl⟩ : syracuseStep 15998633 = 11998975) B11998975
theorem B7995581 : Blo 1403521 7995581 := bstep (se 3 (by rfl) ⟨1499171, by rfl⟩ : syracuseStep 7995581 = 2998343) B2998343
theorem B82051865 : Blo 1403521 82051865 := bstep (se 2 (by rfl) ⟨30769449, by rfl⟩ : syracuseStep 82051865 = 61538899) B61538899
theorem B8546431 : Blo 1403521 8546431 := bstep (se 1 (by rfl) ⟨6409823, by rfl⟩ : syracuseStep 8546431 = 12819647) B12819647
theorem B1404007 : Blo 1403521 1404007 := bstep (se 1 (by rfl) ⟨1053005, by rfl⟩ : syracuseStep 1404007 = 2106011) B2106011
theorem B1580143 : Blo 1403521 1580143 := bstep (se 1 (by rfl) ⟨1185107, by rfl⟩ : syracuseStep 1580143 = 2370215) B2370215
theorem B10665755 : Blo 1403521 10665755 := bstep (se 1 (by rfl) ⟨7999316, by rfl⟩ : syracuseStep 10665755 = 15998633) B15998633
theorem B22781843 : Blo 1403521 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B11395241 : Blo 1403521 11395241 := bstep (se 2 (by rfl) ⟨4273215, by rfl⟩ : syracuseStep 11395241 = 8546431) B8546431
theorem B2106857 : Blo 1403521 2106857 := bstep (se 2 (by rfl) ⟨790071, by rfl⟩ : syracuseStep 2106857 = 1580143) B1580143
theorem B54701243 : Blo 1403521 54701243 := bstep (se 1 (by rfl) ⟨41025932, by rfl⟩ : syracuseStep 54701243 = 82051865) B82051865
theorem B5330387 : Blo 1403521 5330387 := bstep (se 1 (by rfl) ⟨3997790, by rfl⟩ : syracuseStep 5330387 = 7995581) B7995581
theorem B7110503 : Blo 1403521 7110503 := bstep (se 1 (by rfl) ⟨5332877, by rfl⟩ : syracuseStep 7110503 = 10665755) B10665755
theorem B15187895 : Blo 1403521 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B7596827 : Blo 1403521 7596827 := bstep (se 1 (by rfl) ⟨5697620, by rfl⟩ : syracuseStep 7596827 = 11395241) B11395241
theorem B1404571 : Blo 1403521 1404571 := bstep (se 1 (by rfl) ⟨1053428, by rfl⟩ : syracuseStep 1404571 = 2106857) B2106857
theorem B36467495 : Blo 1403521 36467495 := bstep (se 1 (by rfl) ⟨27350621, by rfl⟩ : syracuseStep 36467495 = 54701243) B54701243
theorem B4740335 : Blo 1403521 4740335 := bstep (se 1 (by rfl) ⟨3555251, by rfl⟩ : syracuseStep 4740335 = 7110503) B7110503
theorem B3553591 : Blo 1403521 3553591 := bstep (se 1 (by rfl) ⟨2665193, by rfl⟩ : syracuseStep 3553591 = 5330387) B5330387
theorem B10125263 : Blo 1403521 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B5064551 : Blo 1403521 5064551 := bstep (se 1 (by rfl) ⟨3798413, by rfl⟩ : syracuseStep 5064551 = 7596827) B7596827
theorem B4738121 : Blo 1403521 4738121 := bstep (se 2 (by rfl) ⟨1776795, by rfl⟩ : syracuseStep 4738121 = 3553591) B3553591
theorem B24311663 : Blo 1403521 24311663 := bstep (se 1 (by rfl) ⟨18233747, by rfl⟩ : syracuseStep 24311663 = 36467495) B36467495
theorem B3160223 : Blo 1403521 3160223 := bstep (se 1 (by rfl) ⟨2370167, by rfl⟩ : syracuseStep 3160223 = 4740335) B4740335
theorem B27000701 : Blo 1403521 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B3376367 : Blo 1403521 3376367 := bstep (se 1 (by rfl) ⟨2532275, by rfl⟩ : syracuseStep 3376367 = 5064551) B5064551
theorem B2106815 : Blo 1403521 2106815 := bstep (se 1 (by rfl) ⟨1580111, by rfl⟩ : syracuseStep 2106815 = 3160223) B3160223
theorem B18000467 : Blo 1403521 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B16207775 : Blo 1403521 16207775 := bstep (se 1 (by rfl) ⟨12155831, by rfl⟩ : syracuseStep 16207775 = 24311663) B24311663
theorem B3158747 : Blo 1403521 3158747 := bstep (se 1 (by rfl) ⟨2369060, by rfl⟩ : syracuseStep 3158747 = 4738121) B4738121
theorem B2105831 : Blo 1403521 2105831 := bstep (se 1 (by rfl) ⟨1579373, by rfl⟩ : syracuseStep 2105831 = 3158747) B3158747
theorem B1404543 : Blo 1403521 1404543 := bstep (se 1 (by rfl) ⟨1053407, by rfl⟩ : syracuseStep 1404543 = 2106815) B2106815
theorem B2250911 : Blo 1403521 2250911 := bstep (se 1 (by rfl) ⟨1688183, by rfl⟩ : syracuseStep 2250911 = 3376367) B3376367
theorem B12000311 : Blo 1403521 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B10805183 : Blo 1403521 10805183 := bstep (se 1 (by rfl) ⟨8103887, by rfl⟩ : syracuseStep 10805183 = 16207775) B16207775
theorem B1500607 : Blo 1403521 1500607 := bstep (se 1 (by rfl) ⟨1125455, by rfl⟩ : syracuseStep 1500607 = 2250911) B2250911
theorem B7203455 : Blo 1403521 7203455 := bstep (se 1 (by rfl) ⟨5402591, by rfl⟩ : syracuseStep 7203455 = 10805183) B10805183
theorem B1403887 : Blo 1403521 1403887 := bstep (se 1 (by rfl) ⟨1052915, by rfl⟩ : syracuseStep 1403887 = 2105831) B2105831
theorem B8000207 : Blo 1403521 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B5333471 : Blo 1403521 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B4802303 : Blo 1403521 4802303 := bstep (se 1 (by rfl) ⟨3601727, by rfl⟩ : syracuseStep 4802303 = 7203455) B7203455
theorem B2000809 : Blo 1403521 2000809 := bstep (se 2 (by rfl) ⟨750303, by rfl⟩ : syracuseStep 2000809 = 1500607) B1500607
theorem B3555647 : Blo 1403521 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B2667745 : Blo 1403521 2667745 := bstep (se 2 (by rfl) ⟨1000404, by rfl⟩ : syracuseStep 2667745 = 2000809) B2000809
theorem B3201535 : Blo 1403521 3201535 := bstep (se 1 (by rfl) ⟨2401151, by rfl⟩ : syracuseStep 3201535 = 4802303) B4802303
theorem B4268713 : Blo 1403521 4268713 := bstep (se 2 (by rfl) ⟨1600767, by rfl⟩ : syracuseStep 4268713 = 3201535) B3201535
theorem B3556993 : Blo 1403521 3556993 := bstep (se 2 (by rfl) ⟨1333872, by rfl⟩ : syracuseStep 3556993 = 2667745) B2667745
theorem B2370431 : Blo 1403521 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B5691617 : Blo 1403521 5691617 := bstep (se 2 (by rfl) ⟨2134356, by rfl⟩ : syracuseStep 5691617 = 4268713) B4268713
theorem B1580287 : Blo 1403521 1580287 := bstep (se 1 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 1580287 = 2370431) B2370431
theorem B4742657 : Blo 1403521 4742657 := bstep (se 2 (by rfl) ⟨1778496, by rfl⟩ : syracuseStep 4742657 = 3556993) B3556993
theorem B3794411 : Blo 1403521 3794411 := bstep (se 1 (by rfl) ⟨2845808, by rfl⟩ : syracuseStep 3794411 = 5691617) B5691617
theorem B2107049 : Blo 1403521 2107049 := bstep (se 2 (by rfl) ⟨790143, by rfl⟩ : syracuseStep 2107049 = 1580287) B1580287
theorem B3161771 : Blo 1403521 3161771 := bstep (se 1 (by rfl) ⟨2371328, by rfl⟩ : syracuseStep 3161771 = 4742657) B4742657
theorem B10118429 : Blo 1403521 10118429 := bstep (se 3 (by rfl) ⟨1897205, by rfl⟩ : syracuseStep 10118429 = 3794411) B3794411
theorem B2107847 : Blo 1403521 2107847 := bstep (se 1 (by rfl) ⟨1580885, by rfl⟩ : syracuseStep 2107847 = 3161771) B3161771
theorem B1404699 : Blo 1403521 1404699 := bstep (se 1 (by rfl) ⟨1053524, by rfl⟩ : syracuseStep 1404699 = 2107049) B2107049
theorem B6745619 : Blo 1403521 6745619 := bstep (se 1 (by rfl) ⟨5059214, by rfl⟩ : syracuseStep 6745619 = 10118429) B10118429
theorem B1405231 : Blo 1403521 1405231 := bstep (se 1 (by rfl) ⟨1053923, by rfl⟩ : syracuseStep 1405231 = 2107847) B2107847
theorem B17988317 : Blo 1403521 17988317 := bstep (se 3 (by rfl) ⟨3372809, by rfl⟩ : syracuseStep 17988317 = 6745619) B6745619
theorem B11992211 : Blo 1403521 11992211 := bstep (se 1 (by rfl) ⟨8994158, by rfl⟩ : syracuseStep 11992211 = 17988317) B17988317
theorem B7994807 : Blo 1403521 7994807 := bstep (se 1 (by rfl) ⟨5996105, by rfl⟩ : syracuseStep 7994807 = 11992211) B11992211
theorem B5329871 : Blo 1403521 5329871 := bstep (se 1 (by rfl) ⟨3997403, by rfl⟩ : syracuseStep 5329871 = 7994807) B7994807
theorem B3553247 : Blo 1403521 3553247 := bstep (se 1 (by rfl) ⟨2664935, by rfl⟩ : syracuseStep 3553247 = 5329871) B5329871
theorem B2368831 : Blo 1403521 2368831 := bstep (se 1 (by rfl) ⟨1776623, by rfl⟩ : syracuseStep 2368831 = 3553247) B3553247
theorem B3158441 : Blo 1403521 3158441 := bstep (se 2 (by rfl) ⟨1184415, by rfl⟩ : syracuseStep 3158441 = 2368831) B2368831
theorem B2105627 : Blo 1403521 2105627 := bstep (se 1 (by rfl) ⟨1579220, by rfl⟩ : syracuseStep 2105627 = 3158441) B3158441
theorem B1403751 : Blo 1403521 1403751 := bstep (se 1 (by rfl) ⟨1052813, by rfl⟩ : syracuseStep 1403751 = 2105627) B2105627

theorem C0 (j : ℕ) (h1 : 350880 ≤ j) (h2 : j ≤ 351379) : Blo 1403521 (4 * j + 3) := by
  interval_cases j
  · exact B1403523
  · exact B1403527
  · exact B1403531
  · exact B1403535
  · exact B1403539
  · exact B1403543
  · exact B1403547
  · exact B1403551
  · exact B1403555
  · exact B1403559
  · exact B1403563
  · exact B1403567
  · exact B1403571
  · exact B1403575
  · exact B1403579
  · exact B1403583
  · exact B1403587
  · exact B1403591
  · exact B1403595
  · exact B1403599
  · exact B1403603
  · exact B1403607
  · exact B1403611
  · exact B1403615
  · exact B1403619
  · exact B1403623
  · exact B1403627
  · exact B1403631
  · exact B1403635
  · exact B1403639
  · exact B1403643
  · exact B1403647
  · exact B1403651
  · exact B1403655
  · exact B1403659
  · exact B1403663
  · exact B1403667
  · exact B1403671
  · exact B1403675
  · exact B1403679
  · exact B1403683
  · exact B1403687
  · exact B1403691
  · exact B1403695
  · exact B1403699
  · exact B1403703
  · exact B1403707
  · exact B1403711
  · exact B1403715
  · exact B1403719
  · exact B1403723
  · exact B1403727
  · exact B1403731
  · exact B1403735
  · exact B1403739
  · exact B1403743
  · exact B1403747
  · exact B1403751
  · exact B1403755
  · exact B1403759
  · exact B1403763
  · exact B1403767
  · exact B1403771
  · exact B1403775
  · exact B1403779
  · exact B1403783
  · exact B1403787
  · exact B1403791
  · exact B1403795
  · exact B1403799
  · exact B1403803
  · exact B1403807
  · exact B1403811
  · exact B1403815
  · exact B1403819
  · exact B1403823
  · exact B1403827
  · exact B1403831
  · exact B1403835
  · exact B1403839
  · exact B1403843
  · exact B1403847
  · exact B1403851
  · exact B1403855
  · exact B1403859
  · exact B1403863
  · exact B1403867
  · exact B1403871
  · exact B1403875
  · exact B1403879
  · exact B1403883
  · exact B1403887
  · exact B1403891
  · exact B1403895
  · exact B1403899
  · exact B1403903
  · exact B1403907
  · exact B1403911
  · exact B1403915
  · exact B1403919
  · exact B1403923
  · exact B1403927
  · exact B1403931
  · exact B1403935
  · exact B1403939
  · exact B1403943
  · exact B1403947
  · exact B1403951
  · exact B1403955
  · exact B1403959
  · exact B1403963
  · exact B1403967
  · exact B1403971
  · exact B1403975
  · exact B1403979
  · exact B1403983
  · exact B1403987
  · exact B1403991
  · exact B1403995
  · exact B1403999
  · exact B1404003
  · exact B1404007
  · exact B1404011
  · exact B1404015
  · exact B1404019
  · exact B1404023
  · exact B1404027
  · exact B1404031
  · exact B1404035
  · exact B1404039
  · exact B1404043
  · exact B1404047
  · exact B1404051
  · exact B1404055
  · exact B1404059
  · exact B1404063
  · exact B1404067
  · exact B1404071
  · exact B1404075
  · exact B1404079
  · exact B1404083
  · exact B1404087
  · exact B1404091
  · exact B1404095
  · exact B1404099
  · exact B1404103
  · exact B1404107
  · exact B1404111
  · exact B1404115
  · exact B1404119
  · exact B1404123
  · exact B1404127
  · exact B1404131
  · exact B1404135
  · exact B1404139
  · exact B1404143
  · exact B1404147
  · exact B1404151
  · exact B1404155
  · exact B1404159
  · exact B1404163
  · exact B1404167
  · exact B1404171
  · exact B1404175
  · exact B1404179
  · exact B1404183
  · exact B1404187
  · exact B1404191
  · exact B1404195
  · exact B1404199
  · exact B1404203
  · exact B1404207
  · exact B1404211
  · exact B1404215
  · exact B1404219
  · exact B1404223
  · exact B1404227
  · exact B1404231
  · exact B1404235
  · exact B1404239
  · exact B1404243
  · exact B1404247
  · exact B1404251
  · exact B1404255
  · exact B1404259
  · exact B1404263
  · exact B1404267
  · exact B1404271
  · exact B1404275
  · exact B1404279
  · exact B1404283
  · exact B1404287
  · exact B1404291
  · exact B1404295
  · exact B1404299
  · exact B1404303
  · exact B1404307
  · exact B1404311
  · exact B1404315
  · exact B1404319
  · exact B1404323
  · exact B1404327
  · exact B1404331
  · exact B1404335
  · exact B1404339
  · exact B1404343
  · exact B1404347
  · exact B1404351
  · exact B1404355
  · exact B1404359
  · exact B1404363
  · exact B1404367
  · exact B1404371
  · exact B1404375
  · exact B1404379
  · exact B1404383
  · exact B1404387
  · exact B1404391
  · exact B1404395
  · exact B1404399
  · exact B1404403
  · exact B1404407
  · exact B1404411
  · exact B1404415
  · exact B1404419
  · exact B1404423
  · exact B1404427
  · exact B1404431
  · exact B1404435
  · exact B1404439
  · exact B1404443
  · exact B1404447
  · exact B1404451
  · exact B1404455
  · exact B1404459
  · exact B1404463
  · exact B1404467
  · exact B1404471
  · exact B1404475
  · exact B1404479
  · exact B1404483
  · exact B1404487
  · exact B1404491
  · exact B1404495
  · exact B1404499
  · exact B1404503
  · exact B1404507
  · exact B1404511
  · exact B1404515
  · exact B1404519
  · exact B1404523
  · exact B1404527
  · exact B1404531
  · exact B1404535
  · exact B1404539
  · exact B1404543
  · exact B1404547
  · exact B1404551
  · exact B1404555
  · exact B1404559
  · exact B1404563
  · exact B1404567
  · exact B1404571
  · exact B1404575
  · exact B1404579
  · exact B1404583
  · exact B1404587
  · exact B1404591
  · exact B1404595
  · exact B1404599
  · exact B1404603
  · exact B1404607
  · exact B1404611
  · exact B1404615
  · exact B1404619
  · exact B1404623
  · exact B1404627
  · exact B1404631
  · exact B1404635
  · exact B1404639
  · exact B1404643
  · exact B1404647
  · exact B1404651
  · exact B1404655
  · exact B1404659
  · exact B1404663
  · exact B1404667
  · exact B1404671
  · exact B1404675
  · exact B1404679
  · exact B1404683
  · exact B1404687
  · exact B1404691
  · exact B1404695
  · exact B1404699
  · exact B1404703
  · exact B1404707
  · exact B1404711
  · exact B1404715
  · exact B1404719
  · exact B1404723
  · exact B1404727
  · exact B1404731
  · exact B1404735
  · exact B1404739
  · exact B1404743
  · exact B1404747
  · exact B1404751
  · exact B1404755
  · exact B1404759
  · exact B1404763
  · exact B1404767
  · exact B1404771
  · exact B1404775
  · exact B1404779
  · exact B1404783
  · exact B1404787
  · exact B1404791
  · exact B1404795
  · exact B1404799
  · exact B1404803
  · exact B1404807
  · exact B1404811
  · exact B1404815
  · exact B1404819
  · exact B1404823
  · exact B1404827
  · exact B1404831
  · exact B1404835
  · exact B1404839
  · exact B1404843
  · exact B1404847
  · exact B1404851
  · exact B1404855
  · exact B1404859
  · exact B1404863
  · exact B1404867
  · exact B1404871
  · exact B1404875
  · exact B1404879
  · exact B1404883
  · exact B1404887
  · exact B1404891
  · exact B1404895
  · exact B1404899
  · exact B1404903
  · exact B1404907
  · exact B1404911
  · exact B1404915
  · exact B1404919
  · exact B1404923
  · exact B1404927
  · exact B1404931
  · exact B1404935
  · exact B1404939
  · exact B1404943
  · exact B1404947
  · exact B1404951
  · exact B1404955
  · exact B1404959
  · exact B1404963
  · exact B1404967
  · exact B1404971
  · exact B1404975
  · exact B1404979
  · exact B1404983
  · exact B1404987
  · exact B1404991
  · exact B1404995
  · exact B1404999
  · exact B1405003
  · exact B1405007
  · exact B1405011
  · exact B1405015
  · exact B1405019
  · exact B1405023
  · exact B1405027
  · exact B1405031
  · exact B1405035
  · exact B1405039
  · exact B1405043
  · exact B1405047
  · exact B1405051
  · exact B1405055
  · exact B1405059
  · exact B1405063
  · exact B1405067
  · exact B1405071
  · exact B1405075
  · exact B1405079
  · exact B1405083
  · exact B1405087
  · exact B1405091
  · exact B1405095
  · exact B1405099
  · exact B1405103
  · exact B1405107
  · exact B1405111
  · exact B1405115
  · exact B1405119
  · exact B1405123
  · exact B1405127
  · exact B1405131
  · exact B1405135
  · exact B1405139
  · exact B1405143
  · exact B1405147
  · exact B1405151
  · exact B1405155
  · exact B1405159
  · exact B1405163
  · exact B1405167
  · exact B1405171
  · exact B1405175
  · exact B1405179
  · exact B1405183
  · exact B1405187
  · exact B1405191
  · exact B1405195
  · exact B1405199
  · exact B1405203
  · exact B1405207
  · exact B1405211
  · exact B1405215
  · exact B1405219
  · exact B1405223
  · exact B1405227
  · exact B1405231
  · exact B1405235
  · exact B1405239
  · exact B1405243
  · exact B1405247
  · exact B1405251
  · exact B1405255
  · exact B1405259
  · exact B1405263
  · exact B1405267
  · exact B1405271
  · exact B1405275
  · exact B1405279
  · exact B1405283
  · exact B1405287
  · exact B1405291
  · exact B1405295
  · exact B1405299
  · exact B1405303
  · exact B1405307
  · exact B1405311
  · exact B1405315
  · exact B1405319
  · exact B1405323
  · exact B1405327
  · exact B1405331
  · exact B1405335
  · exact B1405339
  · exact B1405343
  · exact B1405347
  · exact B1405351
  · exact B1405355
  · exact B1405359
  · exact B1405363
  · exact B1405367
  · exact B1405371
  · exact B1405375
  · exact B1405379
  · exact B1405383
  · exact B1405387
  · exact B1405391
  · exact B1405395
  · exact B1405399
  · exact B1405403
  · exact B1405407
  · exact B1405411
  · exact B1405415
  · exact B1405419
  · exact B1405423
  · exact B1405427
  · exact B1405431
  · exact B1405435
  · exact B1405439
  · exact B1405443
  · exact B1405447
  · exact B1405451
  · exact B1405455
  · exact B1405459
  · exact B1405463
  · exact B1405467
  · exact B1405471
  · exact B1405475
  · exact B1405479
  · exact B1405483
  · exact B1405487
  · exact B1405491
  · exact B1405495
  · exact B1405499
  · exact B1405503
  · exact B1405507
  · exact B1405511
  · exact B1405515
  · exact B1405519

theorem solution (m : ℕ) (hlo : 1403521 ≤ m) (hhi : m ≤ 1405521) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 350880 ≤ j := by omega
    have hj2 : j ≤ 351379 := by omega
    have hb : Blo 1403521 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
