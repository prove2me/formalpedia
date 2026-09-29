-- Prove2me | solution 1 for syracuse_descends_range_1474557_1476557
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:14:13.046163+00:00
-- url     : https://prove2.me/submissions/85108246-8643-41c4-875d-a2efcda3e3c5

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


theorem B2211845 : Blo 1474557 2211845 := bbase (se 4 (by rfl) ⟨207360, by rfl⟩ : syracuseStep 2211845 = 414721) (by norm_num)
theorem B25198613 : Blo 1474557 25198613 := bbase (se 6 (by rfl) ⟨590592, by rfl⟩ : syracuseStep 25198613 = 1181185) (by norm_num)
theorem B2211869 : Blo 1474557 2211869 := bbase (se 3 (by rfl) ⟨414725, by rfl⟩ : syracuseStep 2211869 = 829451) (by norm_num)
theorem B3317813 : Blo 1474557 3317813 := bbase (se 5 (by rfl) ⟨155522, by rfl⟩ : syracuseStep 3317813 = 311045) (by norm_num)
theorem B2211893 : Blo 1474557 2211893 := bbase (se 5 (by rfl) ⟨103682, by rfl⟩ : syracuseStep 2211893 = 207365) (by norm_num)
theorem B4202549 : Blo 1474557 4202549 := bbase (se 5 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 4202549 = 393989) (by norm_num)
theorem B3547189 : Blo 1474557 3547189 := bbase (se 5 (by rfl) ⟨166274, by rfl⟩ : syracuseStep 3547189 = 332549) (by norm_num)
theorem B2211917 : Blo 1474557 2211917 := bbase (se 3 (by rfl) ⟨414734, by rfl⟩ : syracuseStep 2211917 = 829469) (by norm_num)
theorem B3735629 : Blo 1474557 3735629 := bbase (se 3 (by rfl) ⟨700430, by rfl⟩ : syracuseStep 3735629 = 1400861) (by norm_num)
theorem B2211941 : Blo 1474557 2211941 := bbase (se 4 (by rfl) ⟨207369, by rfl⟩ : syracuseStep 2211941 = 414739) (by norm_num)
theorem B4259957 : Blo 1474557 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B3317885 : Blo 1474557 3317885 := bbase (se 3 (by rfl) ⟨622103, by rfl⟩ : syracuseStep 3317885 = 1244207) (by norm_num)
theorem B2211965 : Blo 1474557 2211965 := bbase (se 3 (by rfl) ⟨414743, by rfl⟩ : syracuseStep 2211965 = 829487) (by norm_num)
theorem B2490493 : Blo 1474557 2490493 := bbase (se 3 (by rfl) ⟨466967, by rfl⟩ : syracuseStep 2490493 = 933935) (by norm_num)
theorem B2211989 : Blo 1474557 2211989 := bbase (se 6 (by rfl) ⟨51843, by rfl⟩ : syracuseStep 2211989 = 103687) (by norm_num)
theorem B2212013 : Blo 1474557 2212013 := bbase (se 3 (by rfl) ⟨414752, by rfl⟩ : syracuseStep 2212013 = 829505) (by norm_num)
theorem B1867961 : Blo 1474557 1867961 := bbase (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) (by norm_num)
theorem B3317957 : Blo 1474557 3317957 := bbase (se 4 (by rfl) ⟨311058, by rfl⟩ : syracuseStep 3317957 = 622117) (by norm_num)
theorem B2212037 : Blo 1474557 2212037 := bbase (se 4 (by rfl) ⟨207378, by rfl⟩ : syracuseStep 2212037 = 414757) (by norm_num)
theorem B2490581 : Blo 1474557 2490581 := bbase (se 7 (by rfl) ⟨29186, by rfl⟩ : syracuseStep 2490581 = 58373) (by norm_num)
theorem B2212061 : Blo 1474557 2212061 := bbase (se 3 (by rfl) ⟨414761, by rfl⟩ : syracuseStep 2212061 = 829523) (by norm_num)
theorem B1868017 : Blo 1474557 1868017 := bbase (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) (by norm_num)
theorem B7086325 : Blo 1474557 7086325 := bbase (se 5 (by rfl) ⟨332171, by rfl⟩ : syracuseStep 7086325 = 664343) (by norm_num)
theorem B2212085 : Blo 1474557 2212085 := bbase (se 5 (by rfl) ⟨103691, by rfl⟩ : syracuseStep 2212085 = 207383) (by norm_num)
theorem B3318029 : Blo 1474557 3318029 := bbase (se 3 (by rfl) ⟨622130, by rfl⟩ : syracuseStep 3318029 = 1244261) (by norm_num)
theorem B2212109 : Blo 1474557 2212109 := bbase (se 3 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 2212109 = 829541) (by norm_num)
theorem B3735821 : Blo 1474557 3735821 := bbase (se 3 (by rfl) ⟨700466, by rfl⟩ : syracuseStep 3735821 = 1400933) (by norm_num)
theorem B4981013 : Blo 1474557 4981013 := bbase (se 6 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 4981013 = 233485) (by norm_num)
theorem B3547421 : Blo 1474557 3547421 := bbase (se 3 (by rfl) ⟨665141, by rfl⟩ : syracuseStep 3547421 = 1330283) (by norm_num)
theorem B2212133 : Blo 1474557 2212133 := bbase (se 4 (by rfl) ⟨207387, by rfl⟩ : syracuseStep 2212133 = 414775) (by norm_num)
theorem B2801965 : Blo 1474557 2801965 := bbase (se 3 (by rfl) ⟨525368, by rfl⟩ : syracuseStep 2801965 = 1050737) (by norm_num)
theorem B2212157 : Blo 1474557 2212157 := bbase (se 3 (by rfl) ⟨414779, by rfl⟩ : syracuseStep 2212157 = 829559) (by norm_num)
theorem B3547469 : Blo 1474557 3547469 := bbase (se 3 (by rfl) ⟨665150, by rfl⟩ : syracuseStep 3547469 = 1330301) (by norm_num)
theorem B1868113 : Blo 1474557 1868113 := bbase (se 2 (by rfl) ⟨700542, by rfl⟩ : syracuseStep 1868113 = 1401085) (by norm_num)
theorem B3318101 : Blo 1474557 3318101 := bbase (se 10 (by rfl) ⟨4860, by rfl⟩ : syracuseStep 3318101 = 9721) (by norm_num)
theorem B2212181 : Blo 1474557 2212181 := bbase (se 10 (by rfl) ⟨3240, by rfl⟩ : syracuseStep 2212181 = 6481) (by norm_num)
theorem B2490709 : Blo 1474557 2490709 := bbase (se 10 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 2490709 = 7297) (by norm_num)
theorem B2212205 : Blo 1474557 2212205 := bbase (se 3 (by rfl) ⟨414788, by rfl⟩ : syracuseStep 2212205 = 829577) (by norm_num)
theorem B5603701 : Blo 1474557 5603701 := bbase (se 5 (by rfl) ⟨262673, by rfl⟩ : syracuseStep 5603701 = 525347) (by norm_num)
theorem B2212229 : Blo 1474557 2212229 := bbase (se 4 (by rfl) ⟨207396, by rfl⟩ : syracuseStep 2212229 = 414793) (by norm_num)
theorem B3318173 : Blo 1474557 3318173 := bbase (se 3 (by rfl) ⟨622157, by rfl⟩ : syracuseStep 3318173 = 1244315) (by norm_num)
theorem B2212253 : Blo 1474557 2212253 := bbase (se 3 (by rfl) ⟨414797, by rfl⟩ : syracuseStep 2212253 = 829595) (by norm_num)
theorem B2523557 : Blo 1474557 2523557 := bbase (se 4 (by rfl) ⟨236583, by rfl⟩ : syracuseStep 2523557 = 473167) (by norm_num)
theorem B2490797 : Blo 1474557 2490797 := bbase (se 3 (by rfl) ⟨467024, by rfl⟩ : syracuseStep 2490797 = 934049) (by norm_num)
theorem B2130349 : Blo 1474557 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B2212277 : Blo 1474557 2212277 := bbase (se 5 (by rfl) ⟨103700, by rfl⟩ : syracuseStep 2212277 = 207401) (by norm_num)
theorem B2802109 : Blo 1474557 2802109 := bbase (se 3 (by rfl) ⟨525395, by rfl⟩ : syracuseStep 2802109 = 1050791) (by norm_num)
theorem B2212301 : Blo 1474557 2212301 := bbase (se 3 (by rfl) ⟨414806, by rfl⟩ : syracuseStep 2212301 = 829613) (by norm_num)
theorem B1892821 : Blo 1474557 1892821 := bbase (se 7 (by rfl) ⟨22181, by rfl⟩ : syracuseStep 1892821 = 44363) (by norm_num)
theorem B5317093 : Blo 1474557 5317093 := bbase (se 4 (by rfl) ⟨498477, by rfl⟩ : syracuseStep 5317093 = 996955) (by norm_num)
theorem B3318245 : Blo 1474557 3318245 := bbase (se 4 (by rfl) ⟨311085, by rfl⟩ : syracuseStep 3318245 = 622171) (by norm_num)
theorem B2212325 : Blo 1474557 2212325 := bbase (se 4 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 2212325 = 414811) (by norm_num)
theorem B5980661 : Blo 1474557 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B2212349 : Blo 1474557 2212349 := bbase (se 3 (by rfl) ⟨414815, by rfl⟩ : syracuseStep 2212349 = 829631) (by norm_num)
theorem B1868285 : Blo 1474557 1868285 := bbase (se 3 (by rfl) ⟨350303, by rfl⟩ : syracuseStep 1868285 = 700607) (by norm_num)
theorem B2212373 : Blo 1474557 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B3031589 : Blo 1474557 3031589 := bbase (se 4 (by rfl) ⟨284211, by rfl⟩ : syracuseStep 3031589 = 568423) (by norm_num)
theorem B3318317 : Blo 1474557 3318317 := bbase (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) (by norm_num)
theorem B2212397 : Blo 1474557 2212397 := bbase (se 3 (by rfl) ⟨414824, by rfl⟩ : syracuseStep 2212397 = 829649) (by norm_num)
theorem B2490925 : Blo 1474557 2490925 := bbase (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) (by norm_num)
theorem B1868341 : Blo 1474557 1868341 := bbase (se 5 (by rfl) ⟨87578, by rfl⟩ : syracuseStep 1868341 = 175157) (by norm_num)
theorem B2212421 : Blo 1474557 2212421 := bbase (se 4 (by rfl) ⟨207414, by rfl⟩ : syracuseStep 2212421 = 414829) (by norm_num)
theorem B2212445 : Blo 1474557 2212445 := bbase (se 3 (by rfl) ⟨414833, by rfl⟩ : syracuseStep 2212445 = 829667) (by norm_num)
theorem B2802269 : Blo 1474557 2802269 := bbase (se 3 (by rfl) ⟨525425, by rfl⟩ : syracuseStep 2802269 = 1050851) (by norm_num)
theorem B3736165 : Blo 1474557 3736165 := bbase (se 4 (by rfl) ⟨350265, by rfl⟩ : syracuseStep 3736165 = 700531) (by norm_num)
theorem B3318389 : Blo 1474557 3318389 := bbase (se 5 (by rfl) ⟨155549, by rfl⟩ : syracuseStep 3318389 = 311099) (by norm_num)
theorem B2212469 : Blo 1474557 2212469 := bbase (se 5 (by rfl) ⟨103709, by rfl⟩ : syracuseStep 2212469 = 207419) (by norm_num)
theorem B2491013 : Blo 1474557 2491013 := bbase (se 4 (by rfl) ⟨233532, by rfl⟩ : syracuseStep 2491013 = 467065) (by norm_num)
theorem B2212493 : Blo 1474557 2212493 := bbase (se 3 (by rfl) ⟨414842, by rfl⟩ : syracuseStep 2212493 = 829685) (by norm_num)
theorem B3195541 : Blo 1474557 3195541 := bbase (se 6 (by rfl) ⟨74895, by rfl⟩ : syracuseStep 3195541 = 149791) (by norm_num)
theorem B1868437 : Blo 1474557 1868437 := bbase (se 6 (by rfl) ⟨43791, by rfl⟩ : syracuseStep 1868437 = 87583) (by norm_num)
theorem B2212517 : Blo 1474557 2212517 := bbase (se 4 (by rfl) ⟨207423, by rfl⟩ : syracuseStep 2212517 = 414847) (by norm_num)
theorem B5604005 : Blo 1474557 5604005 := bbase (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) (by norm_num)
theorem B3318461 : Blo 1474557 3318461 := bbase (se 3 (by rfl) ⟨622211, by rfl⟩ : syracuseStep 3318461 = 1244423) (by norm_num)
theorem B2212541 : Blo 1474557 2212541 := bbase (se 3 (by rfl) ⟨414851, by rfl⟩ : syracuseStep 2212541 = 829703) (by norm_num)
theorem B4981445 : Blo 1474557 4981445 := bbase (se 4 (by rfl) ⟨467010, by rfl⟩ : syracuseStep 4981445 = 934021) (by norm_num)
theorem B2212565 : Blo 1474557 2212565 := bbase (se 7 (by rfl) ⟨25928, by rfl⟩ : syracuseStep 2212565 = 51857) (by norm_num)
theorem B3736277 : Blo 1474557 3736277 := bbase (se 7 (by rfl) ⟨43784, by rfl⟩ : syracuseStep 3736277 = 87569) (by norm_num)
theorem B2212589 : Blo 1474557 2212589 := bbase (se 3 (by rfl) ⟨414860, by rfl⟩ : syracuseStep 2212589 = 829721) (by norm_num)
theorem B2802413 : Blo 1474557 2802413 := bbase (se 3 (by rfl) ⟨525452, by rfl⟩ : syracuseStep 2802413 = 1050905) (by norm_num)
theorem B3318533 : Blo 1474557 3318533 := bbase (se 4 (by rfl) ⟨311112, by rfl⟩ : syracuseStep 3318533 = 622225) (by norm_num)
theorem B2212613 : Blo 1474557 2212613 := bbase (se 4 (by rfl) ⟨207432, by rfl⟩ : syracuseStep 2212613 = 414865) (by norm_num)
theorem B2491141 : Blo 1474557 2491141 := bbase (se 4 (by rfl) ⟨233544, by rfl⟩ : syracuseStep 2491141 = 467089) (by norm_num)
theorem B2212637 : Blo 1474557 2212637 := bbase (se 3 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 2212637 = 829739) (by norm_num)
theorem B3195677 : Blo 1474557 3195677 := bbase (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) (by norm_num)
theorem B2212661 : Blo 1474557 2212661 := bbase (se 5 (by rfl) ⟨103718, by rfl⟩ : syracuseStep 2212661 = 207437) (by norm_num)
theorem B7471925 : Blo 1474557 7471925 := bbase (se 5 (by rfl) ⟨350246, by rfl⟩ : syracuseStep 7471925 = 700493) (by norm_num)
theorem B1868609 : Blo 1474557 1868609 := bbase (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) (by norm_num)
theorem B3318605 : Blo 1474557 3318605 := bbase (se 3 (by rfl) ⟨622238, by rfl⟩ : syracuseStep 3318605 = 1244477) (by norm_num)
theorem B2212685 : Blo 1474557 2212685 := bbase (se 3 (by rfl) ⟨414878, by rfl⟩ : syracuseStep 2212685 = 829757) (by norm_num)
theorem B2491229 : Blo 1474557 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B2212709 : Blo 1474557 2212709 := bbase (se 4 (by rfl) ⟨207441, by rfl⟩ : syracuseStep 2212709 = 414883) (by norm_num)
theorem B1868665 : Blo 1474557 1868665 := bbase (se 2 (by rfl) ⟨700749, by rfl⟩ : syracuseStep 1868665 = 1401499) (by norm_num)
theorem B2212733 : Blo 1474557 2212733 := bbase (se 3 (by rfl) ⟨414887, by rfl⟩ : syracuseStep 2212733 = 829775) (by norm_num)
theorem B3318677 : Blo 1474557 3318677 := bbase (se 6 (by rfl) ⟨77781, by rfl⟩ : syracuseStep 3318677 = 155563) (by norm_num)
theorem B2212757 : Blo 1474557 2212757 := bbase (se 6 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 2212757 = 103723) (by norm_num)
theorem B3736469 : Blo 1474557 3736469 := bbase (se 6 (by rfl) ⟨87573, by rfl⟩ : syracuseStep 3736469 = 175147) (by norm_num)
theorem B2212781 : Blo 1474557 2212781 := bbase (se 3 (by rfl) ⟨414896, by rfl⟩ : syracuseStep 2212781 = 829793) (by norm_num)
theorem B2212805 : Blo 1474557 2212805 := bbase (se 4 (by rfl) ⟨207450, by rfl⟩ : syracuseStep 2212805 = 414901) (by norm_num)
theorem B1868761 : Blo 1474557 1868761 := bbase (se 2 (by rfl) ⟨700785, by rfl⟩ : syracuseStep 1868761 = 1401571) (by norm_num)
theorem B3318749 : Blo 1474557 3318749 := bbase (se 3 (by rfl) ⟨622265, by rfl⟩ : syracuseStep 3318749 = 1244531) (by norm_num)
theorem B2212829 : Blo 1474557 2212829 := bbase (se 3 (by rfl) ⟨414905, by rfl⟩ : syracuseStep 2212829 = 829811) (by norm_num)
theorem B2491357 : Blo 1474557 2491357 := bbase (se 3 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 2491357 = 934259) (by norm_num)
theorem B2212853 : Blo 1474557 2212853 := bbase (se 5 (by rfl) ⟨103727, by rfl⟩ : syracuseStep 2212853 = 207455) (by norm_num)
theorem B2212877 : Blo 1474557 2212877 := bbase (se 3 (by rfl) ⟨414914, by rfl⟩ : syracuseStep 2212877 = 829829) (by norm_num)
theorem B2802701 : Blo 1474557 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B3318821 : Blo 1474557 3318821 := bbase (se 4 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 3318821 = 622279) (by norm_num)
theorem B2212901 : Blo 1474557 2212901 := bbase (se 4 (by rfl) ⟨207459, by rfl⟩ : syracuseStep 2212901 = 414919) (by norm_num)
theorem B2491445 : Blo 1474557 2491445 := bbase (se 5 (by rfl) ⟨116786, by rfl⟩ : syracuseStep 2491445 = 233573) (by norm_num)
theorem B2212925 : Blo 1474557 2212925 := bbase (se 3 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 2212925 = 829847) (by norm_num)
theorem B1867789 : Blo 1474557 1867789 := bbase (se 3 (by rfl) ⟨350210, by rfl⟩ : syracuseStep 1867789 = 700421) (by norm_num)
theorem B2212949 : Blo 1474557 2212949 := bbase (se 8 (by rfl) ⟨12966, by rfl⟩ : syracuseStep 2212949 = 25933) (by norm_num)
theorem B3318893 : Blo 1474557 3318893 := bbase (se 3 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 3318893 = 1244585) (by norm_num)
theorem B2212973 : Blo 1474557 2212973 := bbase (se 3 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 2212973 = 829865) (by norm_num)
theorem B4981877 : Blo 1474557 4981877 := bbase (se 5 (by rfl) ⟨233525, by rfl⟩ : syracuseStep 4981877 = 467051) (by norm_num)
theorem B2212997 : Blo 1474557 2212997 := bbase (se 4 (by rfl) ⟨207468, by rfl⟩ : syracuseStep 2212997 = 414937) (by norm_num)
theorem B2213021 : Blo 1474557 2213021 := bbase (se 3 (by rfl) ⟨414941, by rfl⟩ : syracuseStep 2213021 = 829883) (by norm_num)
theorem B2802853 : Blo 1474557 2802853 := bbase (se 4 (by rfl) ⟨262767, by rfl⟩ : syracuseStep 2802853 = 525535) (by norm_num)
theorem B3318965 : Blo 1474557 3318965 := bbase (se 5 (by rfl) ⟨155576, by rfl⟩ : syracuseStep 3318965 = 311153) (by norm_num)
theorem B2213045 : Blo 1474557 2213045 := bbase (se 5 (by rfl) ⟨103736, by rfl⟩ : syracuseStep 2213045 = 207473) (by norm_num)
theorem B2491573 : Blo 1474557 2491573 := bbase (se 5 (by rfl) ⟨116792, by rfl⟩ : syracuseStep 2491573 = 233585) (by norm_num)
theorem B2213069 : Blo 1474557 2213069 := bbase (se 3 (by rfl) ⟨414950, by rfl⟩ : syracuseStep 2213069 = 829901) (by norm_num)
theorem B4203733 : Blo 1474557 4203733 := bbase (se 7 (by rfl) ⟨49262, by rfl⟩ : syracuseStep 4203733 = 98525) (by norm_num)
theorem B2213093 : Blo 1474557 2213093 := bbase (se 4 (by rfl) ⟨207477, by rfl⟩ : syracuseStep 2213093 = 414955) (by norm_num)
theorem B3736813 : Blo 1474557 3736813 := bbase (se 3 (by rfl) ⟨700652, by rfl⟩ : syracuseStep 3736813 = 1401305) (by norm_num)
theorem B3319037 : Blo 1474557 3319037 := bbase (se 3 (by rfl) ⟨622319, by rfl⟩ : syracuseStep 3319037 = 1244639) (by norm_num)
theorem B2213117 : Blo 1474557 2213117 := bbase (se 3 (by rfl) ⟨414959, by rfl⟩ : syracuseStep 2213117 = 829919) (by norm_num)
theorem B2491661 : Blo 1474557 2491661 := bbase (se 3 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 2491661 = 934373) (by norm_num)
theorem B2213141 : Blo 1474557 2213141 := bbase (se 6 (by rfl) ⟨51870, by rfl⟩ : syracuseStep 2213141 = 103741) (by norm_num)
theorem B3196189 : Blo 1474557 3196189 := bbase (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) (by norm_num)
theorem B2213165 : Blo 1474557 2213165 := bbase (se 3 (by rfl) ⟨414968, by rfl⟩ : syracuseStep 2213165 = 829937) (by norm_num)
theorem B3319109 : Blo 1474557 3319109 := bbase (se 4 (by rfl) ⟨311166, by rfl⟩ : syracuseStep 3319109 = 622333) (by norm_num)
theorem B2213189 : Blo 1474557 2213189 := bbase (se 4 (by rfl) ⟨207486, by rfl⟩ : syracuseStep 2213189 = 414973) (by norm_num)
theorem B7972181 : Blo 1474557 7972181 := bbase (se 12 (by rfl) ⟨2919, by rfl⟩ : syracuseStep 7972181 = 5839) (by norm_num)
theorem B2213213 : Blo 1474557 2213213 := bbase (se 3 (by rfl) ⟨414977, by rfl⟩ : syracuseStep 2213213 = 829955) (by norm_num)
theorem B3736925 : Blo 1474557 3736925 := bbase (se 3 (by rfl) ⟨700673, by rfl⟩ : syracuseStep 3736925 = 1401347) (by norm_num)
theorem B2213237 : Blo 1474557 2213237 := bbase (se 5 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 2213237 = 207491) (by norm_num)
theorem B4203893 : Blo 1474557 4203893 := bbase (se 5 (by rfl) ⟨197057, by rfl⟩ : syracuseStep 4203893 = 394115) (by norm_num)
theorem B3319181 : Blo 1474557 3319181 := bbase (se 3 (by rfl) ⟨622346, by rfl⟩ : syracuseStep 3319181 = 1244693) (by norm_num)
theorem B2213261 : Blo 1474557 2213261 := bbase (se 3 (by rfl) ⟨414986, by rfl⟩ : syracuseStep 2213261 = 829973) (by norm_num)
theorem B5047717 : Blo 1474557 5047717 := bbase (se 4 (by rfl) ⟨473223, by rfl⟩ : syracuseStep 5047717 = 946447) (by norm_num)
theorem B2213285 : Blo 1474557 2213285 := bbase (se 4 (by rfl) ⟨207495, by rfl⟩ : syracuseStep 2213285 = 414991) (by norm_num)
theorem B2213309 : Blo 1474557 2213309 := bbase (se 3 (by rfl) ⟨414995, by rfl⟩ : syracuseStep 2213309 = 829991) (by norm_num)
theorem B3319253 : Blo 1474557 3319253 := bbase (se 7 (by rfl) ⟨38897, by rfl⟩ : syracuseStep 3319253 = 77795) (by norm_num)
theorem B2213333 : Blo 1474557 2213333 := bbase (se 7 (by rfl) ⟨25937, by rfl⟩ : syracuseStep 2213333 = 51875) (by norm_num)
theorem B2213357 : Blo 1474557 2213357 := bbase (se 3 (by rfl) ⟨415004, by rfl⟩ : syracuseStep 2213357 = 830009) (by norm_num)
theorem B2213381 : Blo 1474557 2213381 := bbase (se 4 (by rfl) ⟨207504, by rfl⟩ : syracuseStep 2213381 = 415009) (by norm_num)
theorem B3319325 : Blo 1474557 3319325 := bbase (se 3 (by rfl) ⟨622373, by rfl⟩ : syracuseStep 3319325 = 1244747) (by norm_num)
theorem B2213405 : Blo 1474557 2213405 := bbase (se 3 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 2213405 = 830027) (by norm_num)
theorem B3737117 : Blo 1474557 3737117 := bbase (se 3 (by rfl) ⟨700709, by rfl⟩ : syracuseStep 3737117 = 1401419) (by norm_num)
theorem B6727205 : Blo 1474557 6727205 := bbase (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) (by norm_num)
theorem B4982309 : Blo 1474557 4982309 := bbase (se 4 (by rfl) ⟨467091, by rfl⟩ : syracuseStep 4982309 = 934183) (by norm_num)
theorem B2213429 : Blo 1474557 2213429 := bbase (se 5 (by rfl) ⟨103754, by rfl⟩ : syracuseStep 2213429 = 207509) (by norm_num)
theorem B2213453 : Blo 1474557 2213453 := bbase (se 3 (by rfl) ⟨415022, by rfl⟩ : syracuseStep 2213453 = 830045) (by norm_num)
theorem B3319397 : Blo 1474557 3319397 := bbase (se 4 (by rfl) ⟨311193, by rfl⟩ : syracuseStep 3319397 = 622387) (by norm_num)
theorem B2213477 : Blo 1474557 2213477 := bbase (se 4 (by rfl) ⟨207513, by rfl⟩ : syracuseStep 2213477 = 415027) (by norm_num)
theorem B4204133 : Blo 1474557 4204133 := bbase (se 4 (by rfl) ⟨394137, by rfl⟩ : syracuseStep 4204133 = 788275) (by norm_num)
theorem B9455221 : Blo 1474557 9455221 := bbase (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) (by norm_num)
theorem B1894001 : Blo 1474557 1894001 := bbase (se 2 (by rfl) ⟨710250, by rfl⟩ : syracuseStep 1894001 = 1420501) (by norm_num)
theorem B2213501 : Blo 1474557 2213501 := bbase (se 3 (by rfl) ⟨415031, by rfl⟩ : syracuseStep 2213501 = 830063) (by norm_num)
theorem B5113477 : Blo 1474557 5113477 := bbase (se 4 (by rfl) ⟨479388, by rfl⟩ : syracuseStep 5113477 = 958777) (by norm_num)
theorem B2991757 : Blo 1474557 2991757 := bbase (se 3 (by rfl) ⟨560954, by rfl⟩ : syracuseStep 2991757 = 1121909) (by norm_num)
theorem B2213525 : Blo 1474557 2213525 := bbase (se 6 (by rfl) ⟨51879, by rfl⟩ : syracuseStep 2213525 = 103759) (by norm_num)
theorem B3319469 : Blo 1474557 3319469 := bbase (se 3 (by rfl) ⟨622400, by rfl⟩ : syracuseStep 3319469 = 1244801) (by norm_num)
theorem B2213549 : Blo 1474557 2213549 := bbase (se 3 (by rfl) ⟨415040, by rfl⟩ : syracuseStep 2213549 = 830081) (by norm_num)
theorem B6727349 : Blo 1474557 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B2213573 : Blo 1474557 2213573 := bbase (se 4 (by rfl) ⟨207522, by rfl⟩ : syracuseStep 2213573 = 415045) (by norm_num)
theorem B2213597 : Blo 1474557 2213597 := bbase (se 3 (by rfl) ⟨415049, by rfl⟩ : syracuseStep 2213597 = 830099) (by norm_num)
theorem B4548325 : Blo 1474557 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B3319541 : Blo 1474557 3319541 := bbase (se 5 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 3319541 = 311207) (by norm_num)
theorem B5981941 : Blo 1474557 5981941 := bbase (se 5 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 5981941 = 560807) (by norm_num)
theorem B2213621 : Blo 1474557 2213621 := bbase (se 5 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 2213621 = 207527) (by norm_num)
theorem B2213645 : Blo 1474557 2213645 := bbase (se 3 (by rfl) ⟨415058, by rfl⟩ : syracuseStep 2213645 = 830117) (by norm_num)
theorem B2213669 : Blo 1474557 2213669 := bbase (se 4 (by rfl) ⟨207531, by rfl⟩ : syracuseStep 2213669 = 415063) (by norm_num)
theorem B4204325 : Blo 1474557 4204325 := bbase (se 4 (by rfl) ⟨394155, by rfl⟩ : syracuseStep 4204325 = 788311) (by norm_num)
theorem B3319613 : Blo 1474557 3319613 := bbase (se 3 (by rfl) ⟨622427, by rfl⟩ : syracuseStep 3319613 = 1244855) (by norm_num)
theorem B2213693 : Blo 1474557 2213693 := bbase (se 3 (by rfl) ⟨415067, by rfl⟩ : syracuseStep 2213693 = 830135) (by norm_num)
theorem B2213717 : Blo 1474557 2213717 := bbase (se 9 (by rfl) ⟨6485, by rfl⟩ : syracuseStep 2213717 = 12971) (by norm_num)
theorem B2213741 : Blo 1474557 2213741 := bbase (se 3 (by rfl) ⟨415076, by rfl⟩ : syracuseStep 2213741 = 830153) (by norm_num)
theorem B3737461 : Blo 1474557 3737461 := bbase (se 5 (by rfl) ⟨175193, by rfl⟩ : syracuseStep 3737461 = 350387) (by norm_num)
theorem B3319685 : Blo 1474557 3319685 := bbase (se 4 (by rfl) ⟨311220, by rfl⟩ : syracuseStep 3319685 = 622441) (by norm_num)
theorem B2213765 : Blo 1474557 2213765 := bbase (se 4 (by rfl) ⟨207540, by rfl⟩ : syracuseStep 2213765 = 415081) (by norm_num)
theorem B2213789 : Blo 1474557 2213789 := bbase (se 3 (by rfl) ⟨415085, by rfl⟩ : syracuseStep 2213789 = 830171) (by norm_num)
theorem B2213813 : Blo 1474557 2213813 := bbase (se 5 (by rfl) ⟨103772, by rfl⟩ : syracuseStep 2213813 = 207545) (by norm_num)
theorem B1574845 : Blo 1474557 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B6301637 : Blo 1474557 6301637 := bbase (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) (by norm_num)
theorem B3319757 : Blo 1474557 3319757 := bbase (se 3 (by rfl) ⟨622454, by rfl⟩ : syracuseStep 3319757 = 1244909) (by norm_num)
theorem B2213837 : Blo 1474557 2213837 := bbase (se 3 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 2213837 = 830189) (by norm_num)
theorem B4982741 : Blo 1474557 4982741 := bbase (se 7 (by rfl) ⟨58391, by rfl⟩ : syracuseStep 4982741 = 116783) (by norm_num)
theorem B2213861 : Blo 1474557 2213861 := bbase (se 4 (by rfl) ⟨207549, by rfl⟩ : syracuseStep 2213861 = 415099) (by norm_num)
theorem B2213885 : Blo 1474557 2213885 := bbase (se 3 (by rfl) ⟨415103, by rfl⟩ : syracuseStep 2213885 = 830207) (by norm_num)
theorem B3319829 : Blo 1474557 3319829 := bbase (se 6 (by rfl) ⟨77808, by rfl⟩ : syracuseStep 3319829 = 155617) (by norm_num)
theorem B2213909 : Blo 1474557 2213909 := bbase (se 6 (by rfl) ⟨51888, by rfl⟩ : syracuseStep 2213909 = 103777) (by norm_num)
theorem B2213933 : Blo 1474557 2213933 := bbase (se 3 (by rfl) ⟨415112, by rfl⟩ : syracuseStep 2213933 = 830225) (by norm_num)
theorem B1574965 : Blo 1474557 1574965 := bbase (se 5 (by rfl) ⟨73826, by rfl⟩ : syracuseStep 1574965 = 147653) (by norm_num)
theorem B5679173 : Blo 1474557 5679173 := bbase (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) (by norm_num)
theorem B2213957 : Blo 1474557 2213957 := bbase (se 4 (by rfl) ⟨207558, by rfl⟩ : syracuseStep 2213957 = 415117) (by norm_num)
theorem B7473221 : Blo 1474557 7473221 := bbase (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) (by norm_num)
theorem B3319901 : Blo 1474557 3319901 := bbase (se 3 (by rfl) ⟨622481, by rfl⟩ : syracuseStep 3319901 = 1244963) (by norm_num)
theorem B2213981 : Blo 1474557 2213981 := bbase (se 3 (by rfl) ⟨415121, by rfl⟩ : syracuseStep 2213981 = 830243) (by norm_num)
theorem B2214005 : Blo 1474557 2214005 := bbase (se 5 (by rfl) ⟨103781, by rfl⟩ : syracuseStep 2214005 = 207563) (by norm_num)
theorem B2214029 : Blo 1474557 2214029 := bbase (se 3 (by rfl) ⟨415130, by rfl⟩ : syracuseStep 2214029 = 830261) (by norm_num)
theorem B3319973 : Blo 1474557 3319973 := bbase (se 4 (by rfl) ⟨311247, by rfl⟩ : syracuseStep 3319973 = 622495) (by norm_num)
theorem B2214053 : Blo 1474557 2214053 := bbase (se 4 (by rfl) ⟨207567, by rfl⟩ : syracuseStep 2214053 = 415135) (by norm_num)
theorem B2214077 : Blo 1474557 2214077 := bbase (se 3 (by rfl) ⟨415139, by rfl⟩ : syracuseStep 2214077 = 830279) (by norm_num)
theorem B2214101 : Blo 1474557 2214101 := bbase (se 7 (by rfl) ⟨25946, by rfl⟩ : syracuseStep 2214101 = 51893) (by norm_num)
theorem B3320045 : Blo 1474557 3320045 := bbase (se 3 (by rfl) ⟨622508, by rfl⟩ : syracuseStep 3320045 = 1245017) (by norm_num)
theorem B2214125 : Blo 1474557 2214125 := bbase (se 3 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 2214125 = 830297) (by norm_num)
theorem B11962613 : Blo 1474557 11962613 := bbase (se 5 (by rfl) ⟨560747, by rfl⟩ : syracuseStep 11962613 = 1121495) (by norm_num)
theorem B2214149 : Blo 1474557 2214149 := bbase (se 4 (by rfl) ⟨207576, by rfl⟩ : syracuseStep 2214149 = 415153) (by norm_num)
theorem B2214173 : Blo 1474557 2214173 := bbase (se 3 (by rfl) ⟨415157, by rfl⟩ : syracuseStep 2214173 = 830315) (by norm_num)
theorem B1681705 : Blo 1474557 1681705 := bbase (se 2 (by rfl) ⟨630639, by rfl⟩ : syracuseStep 1681705 = 1261279) (by norm_num)
theorem B1575217 : Blo 1474557 1575217 := bbase (se 2 (by rfl) ⟨590706, by rfl⟩ : syracuseStep 1575217 = 1181413) (by norm_num)
theorem B1575221 : Blo 1474557 1575221 := bbase (se 5 (by rfl) ⟨73838, by rfl⟩ : syracuseStep 1575221 = 147677) (by norm_num)
theorem B3320117 : Blo 1474557 3320117 := bbase (se 5 (by rfl) ⟨155630, by rfl⟩ : syracuseStep 3320117 = 311261) (by norm_num)
theorem B2214197 : Blo 1474557 2214197 := bbase (se 5 (by rfl) ⟨103790, by rfl⟩ : syracuseStep 2214197 = 207581) (by norm_num)
theorem B2214221 : Blo 1474557 2214221 := bbase (se 3 (by rfl) ⟨415166, by rfl⟩ : syracuseStep 2214221 = 830333) (by norm_num)
theorem B20195669 : Blo 1474557 20195669 := bbase (se 10 (by rfl) ⟨29583, by rfl⟩ : syracuseStep 20195669 = 59167) (by norm_num)
theorem B2214245 : Blo 1474557 2214245 := bbase (se 4 (by rfl) ⟨207585, by rfl⟩ : syracuseStep 2214245 = 415171) (by norm_num)
theorem B3320189 : Blo 1474557 3320189 := bbase (se 3 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 3320189 = 1245071) (by norm_num)
theorem B2214269 : Blo 1474557 2214269 := bbase (se 3 (by rfl) ⟨415175, by rfl⟩ : syracuseStep 2214269 = 830351) (by norm_num)
theorem B4983173 : Blo 1474557 4983173 := bbase (se 4 (by rfl) ⟨467172, by rfl⟩ : syracuseStep 4983173 = 934345) (by norm_num)
theorem B2214293 : Blo 1474557 2214293 := bbase (se 6 (by rfl) ⟨51897, by rfl⟩ : syracuseStep 2214293 = 103795) (by norm_num)
theorem B2214317 : Blo 1474557 2214317 := bbase (se 3 (by rfl) ⟨415184, by rfl⟩ : syracuseStep 2214317 = 830369) (by norm_num)
theorem B3320261 : Blo 1474557 3320261 := bbase (se 4 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 3320261 = 622549) (by norm_num)
theorem B2214341 : Blo 1474557 2214341 := bbase (se 4 (by rfl) ⟨207594, by rfl⟩ : syracuseStep 2214341 = 415189) (by norm_num)
theorem B2214365 : Blo 1474557 2214365 := bbase (se 3 (by rfl) ⟨415193, by rfl⟩ : syracuseStep 2214365 = 830387) (by norm_num)
theorem B7465445 : Blo 1474557 7465445 := bbase (se 4 (by rfl) ⟨699885, by rfl⟩ : syracuseStep 7465445 = 1399771) (by norm_num)
theorem B2214389 : Blo 1474557 2214389 := bbase (se 5 (by rfl) ⟨103799, by rfl⟩ : syracuseStep 2214389 = 207599) (by norm_num)
theorem B3320333 : Blo 1474557 3320333 := bbase (se 3 (by rfl) ⟨622562, by rfl⟩ : syracuseStep 3320333 = 1245125) (by norm_num)
theorem B2214413 : Blo 1474557 2214413 := bbase (se 3 (by rfl) ⟨415202, by rfl⟩ : syracuseStep 2214413 = 830405) (by norm_num)
theorem B1772057 : Blo 1474557 1772057 := bbase (se 2 (by rfl) ⟨664521, by rfl⟩ : syracuseStep 1772057 = 1329043) (by norm_num)
theorem B2214437 : Blo 1474557 2214437 := bbase (se 4 (by rfl) ⟨207603, by rfl⟩ : syracuseStep 2214437 = 415207) (by norm_num)
theorem B2214461 : Blo 1474557 2214461 := bbase (se 3 (by rfl) ⟨415211, by rfl⟩ : syracuseStep 2214461 = 830423) (by norm_num)
theorem B3320405 : Blo 1474557 3320405 := bbase (se 8 (by rfl) ⟨19455, by rfl⟩ : syracuseStep 3320405 = 38911) (by norm_num)
theorem B2214485 : Blo 1474557 2214485 := bbase (se 8 (by rfl) ⟨12975, by rfl⟩ : syracuseStep 2214485 = 25951) (by norm_num)
theorem B2214509 : Blo 1474557 2214509 := bbase (se 3 (by rfl) ⟨415220, by rfl⟩ : syracuseStep 2214509 = 830441) (by norm_num)
theorem B14174837 : Blo 1474557 14174837 := bbase (se 5 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 14174837 = 1328891) (by norm_num)
theorem B2214533 : Blo 1474557 2214533 := bbase (se 4 (by rfl) ⟨207612, by rfl⟩ : syracuseStep 2214533 = 415225) (by norm_num)
theorem B3320477 : Blo 1474557 3320477 := bbase (se 3 (by rfl) ⟨622589, by rfl⟩ : syracuseStep 3320477 = 1245179) (by norm_num)
theorem B2214557 : Blo 1474557 2214557 := bbase (se 3 (by rfl) ⟨415229, by rfl⟩ : syracuseStep 2214557 = 830459) (by norm_num)
theorem B2214581 : Blo 1474557 2214581 := bbase (se 5 (by rfl) ⟨103808, by rfl⟩ : syracuseStep 2214581 = 207617) (by norm_num)
theorem B1796809 : Blo 1474557 1796809 := bbase (se 2 (by rfl) ⟨673803, by rfl⟩ : syracuseStep 1796809 = 1347607) (by norm_num)
theorem B2214605 : Blo 1474557 2214605 := bbase (se 3 (by rfl) ⟨415238, by rfl⟩ : syracuseStep 2214605 = 830477) (by norm_num)
theorem B3320549 : Blo 1474557 3320549 := bbase (se 4 (by rfl) ⟨311301, by rfl⟩ : syracuseStep 3320549 = 622603) (by norm_num)
theorem B2214629 : Blo 1474557 2214629 := bbase (se 4 (by rfl) ⟨207621, by rfl⟩ : syracuseStep 2214629 = 415243) (by norm_num)
theorem B5606117 : Blo 1474557 5606117 := bbase (se 4 (by rfl) ⟨525573, by rfl⟩ : syracuseStep 5606117 = 1051147) (by norm_num)
theorem B2214653 : Blo 1474557 2214653 := bbase (se 3 (by rfl) ⟨415247, by rfl⟩ : syracuseStep 2214653 = 830495) (by norm_num)
theorem B2214677 : Blo 1474557 2214677 := bbase (se 6 (by rfl) ⟨51906, by rfl⟩ : syracuseStep 2214677 = 103813) (by norm_num)
theorem B3320621 : Blo 1474557 3320621 := bbase (se 3 (by rfl) ⟨622616, by rfl⟩ : syracuseStep 3320621 = 1245233) (by norm_num)
theorem B2214701 : Blo 1474557 2214701 := bbase (se 3 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 2214701 = 830513) (by norm_num)
theorem B2362165 : Blo 1474557 2362165 := bbase (se 5 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 2362165 = 221453) (by norm_num)
theorem B2214725 : Blo 1474557 2214725 := bbase (se 4 (by rfl) ⟨207630, by rfl⟩ : syracuseStep 2214725 = 415261) (by norm_num)
theorem B2214749 : Blo 1474557 2214749 := bbase (se 3 (by rfl) ⟨415265, by rfl⟩ : syracuseStep 2214749 = 830531) (by norm_num)
theorem B1772389 : Blo 1474557 1772389 := bbase (se 4 (by rfl) ⟨166161, by rfl⟩ : syracuseStep 1772389 = 332323) (by norm_num)
theorem B1575785 : Blo 1474557 1575785 := bbase (se 2 (by rfl) ⟨590919, by rfl⟩ : syracuseStep 1575785 = 1181839) (by norm_num)
theorem B3320693 : Blo 1474557 3320693 := bbase (se 5 (by rfl) ⟨155657, by rfl⟩ : syracuseStep 3320693 = 311315) (by norm_num)
theorem B11209589 : Blo 1474557 11209589 := bbase (se 5 (by rfl) ⟨525449, by rfl⟩ : syracuseStep 11209589 = 1050899) (by norm_num)
theorem B2214773 : Blo 1474557 2214773 := bbase (se 5 (by rfl) ⟨103817, by rfl⟩ : syracuseStep 2214773 = 207635) (by norm_num)
theorem B2214797 : Blo 1474557 2214797 := bbase (se 3 (by rfl) ⟨415274, by rfl⟩ : syracuseStep 2214797 = 830549) (by norm_num)
theorem B2214821 : Blo 1474557 2214821 := bbase (se 4 (by rfl) ⟨207639, by rfl⟩ : syracuseStep 2214821 = 415279) (by norm_num)
theorem B3320765 : Blo 1474557 3320765 := bbase (se 3 (by rfl) ⟨622643, by rfl⟩ : syracuseStep 3320765 = 1245287) (by norm_num)
theorem B2100181 : Blo 1474557 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B3320837 : Blo 1474557 3320837 := bbase (se 4 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 3320837 = 622657) (by norm_num)
theorem B1575973 : Blo 1474557 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B3320909 : Blo 1474557 3320909 := bbase (se 3 (by rfl) ⟨622670, by rfl⟩ : syracuseStep 3320909 = 1245341) (by norm_num)
theorem B1797233 : Blo 1474557 1797233 := bbase (se 2 (by rfl) ⟨673962, by rfl⟩ : syracuseStep 1797233 = 1347925) (by norm_num)
theorem B3320981 : Blo 1474557 3320981 := bbase (se 6 (by rfl) ⟨77835, by rfl⟩ : syracuseStep 3320981 = 155671) (by norm_num)
theorem B4730021 : Blo 1474557 4730021 := bbase (se 4 (by rfl) ⟨443439, by rfl⟩ : syracuseStep 4730021 = 886879) (by norm_num)
theorem B3321053 : Blo 1474557 3321053 := bbase (se 3 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 3321053 = 1245395) (by norm_num)
theorem B2362621 : Blo 1474557 2362621 := bbase (se 3 (by rfl) ⟨442991, by rfl⟩ : syracuseStep 2362621 = 885983) (by norm_num)
theorem B11201813 : Blo 1474557 11201813 := bbase (se 6 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 11201813 = 525085) (by norm_num)
theorem B1682713 : Blo 1474557 1682713 := bbase (se 2 (by rfl) ⟨631017, by rfl⟩ : syracuseStep 1682713 = 1262035) (by norm_num)
theorem B3321125 : Blo 1474557 3321125 := bbase (se 4 (by rfl) ⟨311355, by rfl⟩ : syracuseStep 3321125 = 622711) (by norm_num)
theorem B7474517 : Blo 1474557 7474517 := bbase (se 11 (by rfl) ⟨5474, by rfl⟩ : syracuseStep 7474517 = 10949) (by norm_num)
theorem B3321197 : Blo 1474557 3321197 := bbase (se 3 (by rfl) ⟨622724, by rfl⟩ : syracuseStep 3321197 = 1245449) (by norm_num)
theorem B2157949 : Blo 1474557 2157949 := bbase (se 3 (by rfl) ⟨404615, by rfl⟩ : syracuseStep 2157949 = 809231) (by norm_num)
theorem B3321269 : Blo 1474557 3321269 := bbase (se 5 (by rfl) ⟨155684, by rfl⟩ : syracuseStep 3321269 = 311369) (by norm_num)
theorem B3321341 : Blo 1474557 3321341 := bbase (se 3 (by rfl) ⟨622751, by rfl⟩ : syracuseStep 3321341 = 1245503) (by norm_num)
theorem B1773085 : Blo 1474557 1773085 := bbase (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) (by norm_num)
theorem B2100773 : Blo 1474557 2100773 := bbase (se 4 (by rfl) ⟨196947, by rfl⟩ : syracuseStep 2100773 = 393895) (by norm_num)
theorem B3788333 : Blo 1474557 3788333 := bbase (se 3 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 3788333 = 1420625) (by norm_num)
theorem B3321413 : Blo 1474557 3321413 := bbase (se 4 (by rfl) ⟨311382, by rfl⟩ : syracuseStep 3321413 = 622765) (by norm_num)
theorem B1773133 : Blo 1474557 1773133 := bbase (se 3 (by rfl) ⟨332462, by rfl⟩ : syracuseStep 1773133 = 664925) (by norm_num)
theorem B2100853 : Blo 1474557 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B3321485 : Blo 1474557 3321485 := bbase (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) (by norm_num)
theorem B6303413 : Blo 1474557 6303413 := bbase (se 5 (by rfl) ⟨295472, by rfl⟩ : syracuseStep 6303413 = 590945) (by norm_num)
theorem B1994429 : Blo 1474557 1994429 := bbase (se 3 (by rfl) ⟨373955, by rfl⟩ : syracuseStep 1994429 = 747911) (by norm_num)
theorem B3321557 : Blo 1474557 3321557 := bbase (se 7 (by rfl) ⟨38924, by rfl⟩ : syracuseStep 3321557 = 77849) (by norm_num)
theorem B2559709 : Blo 1474557 2559709 := bbase (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) (by norm_num)
theorem B2100973 : Blo 1474557 2100973 := bbase (se 3 (by rfl) ⟨393932, by rfl⟩ : syracuseStep 2100973 = 787865) (by norm_num)
theorem B7466741 : Blo 1474557 7466741 := bbase (se 5 (by rfl) ⟨350003, by rfl⟩ : syracuseStep 7466741 = 700007) (by norm_num)
theorem B3321629 : Blo 1474557 3321629 := bbase (se 3 (by rfl) ⟨622805, by rfl⟩ : syracuseStep 3321629 = 1245611) (by norm_num)
theorem B2101069 : Blo 1474557 2101069 := bbase (se 3 (by rfl) ⟨393950, by rfl⟩ : syracuseStep 2101069 = 787901) (by norm_num)
theorem B1822549 : Blo 1474557 1822549 := bbase (se 9 (by rfl) ⟨5339, by rfl⟩ : syracuseStep 1822549 = 10679) (by norm_num)
theorem B3321701 : Blo 1474557 3321701 := bbase (se 4 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 3321701 = 622819) (by norm_num)
theorem B3149725 : Blo 1474557 3149725 := bbase (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) (by norm_num)
theorem B2363293 : Blo 1474557 2363293 := bbase (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) (by norm_num)
theorem B6303653 : Blo 1474557 6303653 := bbase (se 4 (by rfl) ⟨590967, by rfl⟩ : syracuseStep 6303653 = 1181935) (by norm_num)
theorem B3321773 : Blo 1474557 3321773 := bbase (se 3 (by rfl) ⟨622832, by rfl⟩ : syracuseStep 3321773 = 1245665) (by norm_num)
theorem B3321845 : Blo 1474557 3321845 := bbase (se 5 (by rfl) ⟨155711, by rfl⟩ : syracuseStep 3321845 = 311423) (by norm_num)
theorem B1658893 : Blo 1474557 1658893 := bbase (se 3 (by rfl) ⟨311042, by rfl⟩ : syracuseStep 1658893 = 622085) (by norm_num)
theorem B5754901 : Blo 1474557 5754901 := bbase (se 6 (by rfl) ⟨134880, by rfl⟩ : syracuseStep 5754901 = 269761) (by norm_num)
theorem B5836837 : Blo 1474557 5836837 := bbase (se 4 (by rfl) ⟨547203, by rfl⟩ : syracuseStep 5836837 = 1094407) (by norm_num)
theorem B1658929 : Blo 1474557 1658929 := bbase (se 2 (by rfl) ⟨622098, by rfl⟩ : syracuseStep 1658929 = 1244197) (by norm_num)
theorem B4976693 : Blo 1474557 4976693 := bbase (se 5 (by rfl) ⟨233282, by rfl⟩ : syracuseStep 4976693 = 466565) (by norm_num)
theorem B3321917 : Blo 1474557 3321917 := bbase (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) (by norm_num)
theorem B1658965 : Blo 1474557 1658965 := bbase (se 8 (by rfl) ⟨9720, by rfl⟩ : syracuseStep 1658965 = 19441) (by norm_num)
theorem B1659001 : Blo 1474557 1659001 := bbase (se 2 (by rfl) ⟨622125, by rfl⟩ : syracuseStep 1659001 = 1244251) (by norm_num)
theorem B3321989 : Blo 1474557 3321989 := bbase (se 4 (by rfl) ⟨311436, by rfl⟩ : syracuseStep 3321989 = 622873) (by norm_num)
theorem B1495181 : Blo 1474557 1495181 := bbase (se 3 (by rfl) ⟨280346, by rfl⟩ : syracuseStep 1495181 = 560693) (by norm_num)
theorem B1659037 : Blo 1474557 1659037 := bbase (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) (by norm_num)
theorem B1659073 : Blo 1474557 1659073 := bbase (se 2 (by rfl) ⟨622152, by rfl⟩ : syracuseStep 1659073 = 1244305) (by norm_num)
theorem B3322061 : Blo 1474557 3322061 := bbase (se 3 (by rfl) ⟨622886, by rfl⟩ : syracuseStep 3322061 = 1245773) (by norm_num)
theorem B1659109 : Blo 1474557 1659109 := bbase (se 4 (by rfl) ⟨155541, by rfl⟩ : syracuseStep 1659109 = 311083) (by norm_num)
theorem B1659145 : Blo 1474557 1659145 := bbase (se 2 (by rfl) ⟨622179, by rfl⟩ : syracuseStep 1659145 = 1244359) (by norm_num)
theorem B3543317 : Blo 1474557 3543317 := bbase (se 6 (by rfl) ⟨83046, by rfl⟩ : syracuseStep 3543317 = 166093) (by norm_num)
theorem B4485397 : Blo 1474557 4485397 := bbase (se 6 (by rfl) ⟨105126, by rfl⟩ : syracuseStep 4485397 = 210253) (by norm_num)
theorem B3322133 : Blo 1474557 3322133 := bbase (se 6 (by rfl) ⟨77862, by rfl⟩ : syracuseStep 3322133 = 155725) (by norm_num)
theorem B2658589 : Blo 1474557 2658589 := bbase (se 3 (by rfl) ⟨498485, by rfl⟩ : syracuseStep 2658589 = 996971) (by norm_num)
theorem B1659181 : Blo 1474557 1659181 := bbase (se 3 (by rfl) ⟨311096, by rfl⟩ : syracuseStep 1659181 = 622193) (by norm_num)
theorem B2101565 : Blo 1474557 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B2363717 : Blo 1474557 2363717 := bbase (se 4 (by rfl) ⟨221598, by rfl⟩ : syracuseStep 2363717 = 443197) (by norm_num)
theorem B1659217 : Blo 1474557 1659217 := bbase (se 2 (by rfl) ⟨622206, by rfl⟩ : syracuseStep 1659217 = 1244413) (by norm_num)
theorem B3322205 : Blo 1474557 3322205 := bbase (se 3 (by rfl) ⟨622913, by rfl⟩ : syracuseStep 3322205 = 1245827) (by norm_num)
theorem B1659253 : Blo 1474557 1659253 := bbase (se 5 (by rfl) ⟨77777, by rfl⟩ : syracuseStep 1659253 = 155555) (by norm_num)
theorem B1659289 : Blo 1474557 1659289 := bbase (se 2 (by rfl) ⟨622233, by rfl⟩ : syracuseStep 1659289 = 1244467) (by norm_num)
theorem B1659325 : Blo 1474557 1659325 := bbase (se 3 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 1659325 = 622247) (by norm_num)
theorem B2658757 : Blo 1474557 2658757 := bbase (se 4 (by rfl) ⟨249258, by rfl⟩ : syracuseStep 2658757 = 498517) (by norm_num)
theorem B5681621 : Blo 1474557 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B3543517 : Blo 1474557 3543517 := bbase (se 3 (by rfl) ⟨664409, by rfl⟩ : syracuseStep 3543517 = 1328819) (by norm_num)
theorem B1659361 : Blo 1474557 1659361 := bbase (se 2 (by rfl) ⟨622260, by rfl⟩ : syracuseStep 1659361 = 1244521) (by norm_num)
theorem B4977125 : Blo 1474557 4977125 := bbase (se 4 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 4977125 = 933211) (by norm_num)
theorem B1659397 : Blo 1474557 1659397 := bbase (se 4 (by rfl) ⟨155568, by rfl⟩ : syracuseStep 1659397 = 311137) (by norm_num)
theorem B1659433 : Blo 1474557 1659433 := bbase (se 2 (by rfl) ⟨622287, by rfl⟩ : syracuseStep 1659433 = 1244575) (by norm_num)
theorem B15340085 : Blo 1474557 15340085 := bbase (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) (by norm_num)
theorem B5599813 : Blo 1474557 5599813 := bbase (se 4 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 5599813 = 1049965) (by norm_num)
theorem B1659469 : Blo 1474557 1659469 := bbase (se 3 (by rfl) ⟨311150, by rfl⟩ : syracuseStep 1659469 = 622301) (by norm_num)
theorem B3986005 : Blo 1474557 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B2364005 : Blo 1474557 2364005 := bbase (se 4 (by rfl) ⟨221625, by rfl⟩ : syracuseStep 2364005 = 443251) (by norm_num)
theorem B1659505 : Blo 1474557 1659505 := bbase (se 2 (by rfl) ⟨622314, by rfl⟩ : syracuseStep 1659505 = 1244629) (by norm_num)
theorem B1659541 : Blo 1474557 1659541 := bbase (se 6 (by rfl) ⟨38895, by rfl⟩ : syracuseStep 1659541 = 77791) (by norm_num)
theorem B8401589 : Blo 1474557 8401589 := bbase (se 5 (by rfl) ⟨393824, by rfl⟩ : syracuseStep 8401589 = 787649) (by norm_num)
theorem B1659577 : Blo 1474557 1659577 := bbase (se 2 (by rfl) ⟨622341, by rfl⟩ : syracuseStep 1659577 = 1244683) (by norm_num)
theorem B1659613 : Blo 1474557 1659613 := bbase (se 3 (by rfl) ⟨311177, by rfl⟩ : syracuseStep 1659613 = 622355) (by norm_num)
theorem B1659649 : Blo 1474557 1659649 := bbase (se 2 (by rfl) ⟨622368, by rfl⟩ : syracuseStep 1659649 = 1244737) (by norm_num)
theorem B5321477 : Blo 1474557 5321477 := bbase (se 4 (by rfl) ⟨498888, by rfl⟩ : syracuseStep 5321477 = 997777) (by norm_num)
theorem B3150613 : Blo 1474557 3150613 := bbase (se 6 (by rfl) ⟨73842, by rfl⟩ : syracuseStep 3150613 = 147685) (by norm_num)
theorem B1659685 : Blo 1474557 1659685 := bbase (se 4 (by rfl) ⟨155595, by rfl⟩ : syracuseStep 1659685 = 311191) (by norm_num)
theorem B1659721 : Blo 1474557 1659721 := bbase (se 2 (by rfl) ⟨622395, by rfl⟩ : syracuseStep 1659721 = 1244791) (by norm_num)
theorem B2102117 : Blo 1474557 2102117 := bbase (se 4 (by rfl) ⟨197073, by rfl⟩ : syracuseStep 2102117 = 394147) (by norm_num)
theorem B1659757 : Blo 1474557 1659757 := bbase (se 3 (by rfl) ⟨311204, by rfl⟩ : syracuseStep 1659757 = 622409) (by norm_num)
theorem B5600117 : Blo 1474557 5600117 := bbase (se 5 (by rfl) ⟨262505, by rfl⟩ : syracuseStep 5600117 = 525011) (by norm_num)
theorem B3150733 : Blo 1474557 3150733 := bbase (se 3 (by rfl) ⟨590762, by rfl⟩ : syracuseStep 3150733 = 1181525) (by norm_num)
theorem B1659793 : Blo 1474557 1659793 := bbase (se 2 (by rfl) ⟨622422, by rfl⟩ : syracuseStep 1659793 = 1244845) (by norm_num)
theorem B4977557 : Blo 1474557 4977557 := bbase (se 6 (by rfl) ⟨116661, by rfl⟩ : syracuseStep 4977557 = 233323) (by norm_num)
theorem B1659829 : Blo 1474557 1659829 := bbase (se 5 (by rfl) ⟨77804, by rfl⟩ : syracuseStep 1659829 = 155609) (by norm_num)
theorem B1659865 : Blo 1474557 1659865 := bbase (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) (by norm_num)
theorem B1659901 : Blo 1474557 1659901 := bbase (se 3 (by rfl) ⟨311231, by rfl⟩ : syracuseStep 1659901 = 622463) (by norm_num)
theorem B7468037 : Blo 1474557 7468037 := bbase (se 4 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 7468037 = 1400257) (by norm_num)
theorem B2659333 : Blo 1474557 2659333 := bbase (se 4 (by rfl) ⟨249312, by rfl⟩ : syracuseStep 2659333 = 498625) (by norm_num)
theorem B1659937 : Blo 1474557 1659937 := bbase (se 2 (by rfl) ⟨622476, by rfl⟩ : syracuseStep 1659937 = 1244953) (by norm_num)
theorem B1659973 : Blo 1474557 1659973 := bbase (se 4 (by rfl) ⟨155622, by rfl⟩ : syracuseStep 1659973 = 311245) (by norm_num)
theorem B7189573 : Blo 1474557 7189573 := bbase (se 4 (by rfl) ⟨674022, by rfl⟩ : syracuseStep 7189573 = 1348045) (by norm_num)
theorem B3732581 : Blo 1474557 3732581 := bbase (se 4 (by rfl) ⟨349929, by rfl⟩ : syracuseStep 3732581 = 699859) (by norm_num)
theorem B1660009 : Blo 1474557 1660009 := bbase (se 2 (by rfl) ⟨622503, by rfl⟩ : syracuseStep 1660009 = 1245007) (by norm_num)
theorem B3150989 : Blo 1474557 3150989 := bbase (se 3 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 3150989 = 1181621) (by norm_num)
theorem B1660045 : Blo 1474557 1660045 := bbase (se 3 (by rfl) ⟨311258, by rfl⟩ : syracuseStep 1660045 = 622517) (by norm_num)
theorem B1660081 : Blo 1474557 1660081 := bbase (se 2 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 1660081 = 1245061) (by norm_num)
theorem B1660117 : Blo 1474557 1660117 := bbase (se 7 (by rfl) ⟨19454, by rfl⟩ : syracuseStep 1660117 = 38909) (by norm_num)
theorem B1660153 : Blo 1474557 1660153 := bbase (se 2 (by rfl) ⟨622557, by rfl⟩ : syracuseStep 1660153 = 1245115) (by norm_num)
theorem B4199701 : Blo 1474557 4199701 := bbase (se 6 (by rfl) ⟨98430, by rfl⟩ : syracuseStep 4199701 = 196861) (by norm_num)
theorem B1496341 : Blo 1474557 1496341 := bbase (se 6 (by rfl) ⟨35070, by rfl⟩ : syracuseStep 1496341 = 70141) (by norm_num)
theorem B1660189 : Blo 1474557 1660189 := bbase (se 3 (by rfl) ⟨311285, by rfl⟩ : syracuseStep 1660189 = 622571) (by norm_num)
theorem B5985589 : Blo 1474557 5985589 := bbase (se 5 (by rfl) ⟨280574, by rfl⟩ : syracuseStep 5985589 = 561149) (by norm_num)
theorem B1660225 : Blo 1474557 1660225 := bbase (se 2 (by rfl) ⟨622584, by rfl⟩ : syracuseStep 1660225 = 1245169) (by norm_num)
theorem B4977989 : Blo 1474557 4977989 := bbase (se 4 (by rfl) ⟨466686, by rfl⟩ : syracuseStep 4977989 = 933373) (by norm_num)
theorem B1660261 : Blo 1474557 1660261 := bbase (se 4 (by rfl) ⟨155649, by rfl⟩ : syracuseStep 1660261 = 311299) (by norm_num)
theorem B13464949 : Blo 1474557 13464949 := bbase (se 5 (by rfl) ⟨631169, by rfl⟩ : syracuseStep 13464949 = 1262339) (by norm_num)
theorem B2364805 : Blo 1474557 2364805 := bbase (se 4 (by rfl) ⟨221700, by rfl⟩ : syracuseStep 2364805 = 443401) (by norm_num)
theorem B1660297 : Blo 1474557 1660297 := bbase (se 2 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 1660297 = 1245223) (by norm_num)
theorem B1660333 : Blo 1474557 1660333 := bbase (se 3 (by rfl) ⟨311312, by rfl⟩ : syracuseStep 1660333 = 622625) (by norm_num)
theorem B3732925 : Blo 1474557 3732925 := bbase (se 3 (by rfl) ⟨699923, by rfl⟩ : syracuseStep 3732925 = 1399847) (by norm_num)
theorem B1660369 : Blo 1474557 1660369 := bbase (se 2 (by rfl) ⟨622638, by rfl⟩ : syracuseStep 1660369 = 1245277) (by norm_num)
theorem B1660405 : Blo 1474557 1660405 := bbase (se 5 (by rfl) ⟨77831, by rfl⟩ : syracuseStep 1660405 = 155663) (by norm_num)
theorem B2242061 : Blo 1474557 2242061 := bbase (se 3 (by rfl) ⟨420386, by rfl⟩ : syracuseStep 2242061 = 840773) (by norm_num)
theorem B1660441 : Blo 1474557 1660441 := bbase (se 2 (by rfl) ⟨622665, by rfl⟩ : syracuseStep 1660441 = 1245331) (by norm_num)
theorem B3733037 : Blo 1474557 3733037 := bbase (se 3 (by rfl) ⟨699944, by rfl⟩ : syracuseStep 3733037 = 1399889) (by norm_num)
theorem B1660477 : Blo 1474557 1660477 := bbase (se 3 (by rfl) ⟨311339, by rfl⟩ : syracuseStep 1660477 = 622679) (by norm_num)
theorem B15963733 : Blo 1474557 15963733 := bbase (se 8 (by rfl) ⟨93537, by rfl⟩ : syracuseStep 15963733 = 187075) (by norm_num)
theorem B1660513 : Blo 1474557 1660513 := bbase (se 2 (by rfl) ⟨622692, by rfl⟩ : syracuseStep 1660513 = 1245385) (by norm_num)
theorem B12949109 : Blo 1474557 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B1660549 : Blo 1474557 1660549 := bbase (se 4 (by rfl) ⟨155676, by rfl⟩ : syracuseStep 1660549 = 311353) (by norm_num)
theorem B2659973 : Blo 1474557 2659973 := bbase (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) (by norm_num)
theorem B1660585 : Blo 1474557 1660585 := bbase (se 2 (by rfl) ⟨622719, by rfl⟩ : syracuseStep 1660585 = 1245439) (by norm_num)
theorem B7673525 : Blo 1474557 7673525 := bbase (se 5 (by rfl) ⟨359696, by rfl⟩ : syracuseStep 7673525 = 719393) (by norm_num)
theorem B1660621 : Blo 1474557 1660621 := bbase (se 3 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 1660621 = 622733) (by norm_num)
theorem B3733229 : Blo 1474557 3733229 := bbase (se 3 (by rfl) ⟨699980, by rfl⟩ : syracuseStep 3733229 = 1399961) (by norm_num)
theorem B1660657 : Blo 1474557 1660657 := bbase (se 2 (by rfl) ⟨622746, by rfl⟩ : syracuseStep 1660657 = 1245493) (by norm_num)
theorem B4978421 : Blo 1474557 4978421 := bbase (se 5 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 4978421 = 466727) (by norm_num)
theorem B1660693 : Blo 1474557 1660693 := bbase (se 6 (by rfl) ⟨38922, by rfl⟩ : syracuseStep 1660693 = 77845) (by norm_num)
theorem B7567141 : Blo 1474557 7567141 := bbase (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) (by norm_num)
theorem B2660141 : Blo 1474557 2660141 := bbase (se 3 (by rfl) ⟨498776, by rfl⟩ : syracuseStep 2660141 = 997553) (by norm_num)
theorem B1660729 : Blo 1474557 1660729 := bbase (se 2 (by rfl) ⟨622773, by rfl⟩ : syracuseStep 1660729 = 1245547) (by norm_num)
theorem B1660765 : Blo 1474557 1660765 := bbase (se 3 (by rfl) ⟨311393, by rfl⟩ : syracuseStep 1660765 = 622787) (by norm_num)
theorem B1660801 : Blo 1474557 1660801 := bbase (se 2 (by rfl) ⟨622800, by rfl⟩ : syracuseStep 1660801 = 1245601) (by norm_num)
theorem B1660837 : Blo 1474557 1660837 := bbase (se 4 (by rfl) ⟨155703, by rfl⟩ : syracuseStep 1660837 = 311407) (by norm_num)
theorem B1660873 : Blo 1474557 1660873 := bbase (se 2 (by rfl) ⟨622827, by rfl⟩ : syracuseStep 1660873 = 1245655) (by norm_num)
theorem B1660909 : Blo 1474557 1660909 := bbase (se 3 (by rfl) ⟨311420, by rfl⟩ : syracuseStep 1660909 = 622841) (by norm_num)
theorem B3545093 : Blo 1474557 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B3151877 : Blo 1474557 3151877 := bbase (se 4 (by rfl) ⟨295488, by rfl⟩ : syracuseStep 3151877 = 590977) (by norm_num)
theorem B2488333 : Blo 1474557 2488333 := bbase (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) (by norm_num)
theorem B1660945 : Blo 1474557 1660945 := bbase (se 2 (by rfl) ⟨622854, by rfl⟩ : syracuseStep 1660945 = 1245709) (by norm_num)
theorem B10631189 : Blo 1474557 10631189 := bbase (se 6 (by rfl) ⟨249168, by rfl⟩ : syracuseStep 10631189 = 498337) (by norm_num)
theorem B7976981 : Blo 1474557 7976981 := bbase (se 6 (by rfl) ⟨186960, by rfl⟩ : syracuseStep 7976981 = 373921) (by norm_num)
theorem B1660981 : Blo 1474557 1660981 := bbase (se 5 (by rfl) ⟨77858, by rfl⟩ : syracuseStep 1660981 = 155717) (by norm_num)
theorem B3733573 : Blo 1474557 3733573 := bbase (se 4 (by rfl) ⟨350022, by rfl⟩ : syracuseStep 3733573 = 700045) (by norm_num)
theorem B1661017 : Blo 1474557 1661017 := bbase (se 2 (by rfl) ⟨622881, by rfl⟩ : syracuseStep 1661017 = 1245763) (by norm_num)
theorem B2488421 : Blo 1474557 2488421 := bbase (se 4 (by rfl) ⟨233289, by rfl⟩ : syracuseStep 2488421 = 466579) (by norm_num)
theorem B10090613 : Blo 1474557 10090613 := bbase (se 5 (by rfl) ⟨472997, by rfl⟩ : syracuseStep 10090613 = 945995) (by norm_num)
theorem B1661053 : Blo 1474557 1661053 := bbase (se 3 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 1661053 = 622895) (by norm_num)
theorem B25540757 : Blo 1474557 25540757 := bbase (se 6 (by rfl) ⟨598611, by rfl⟩ : syracuseStep 25540757 = 1197223) (by norm_num)
theorem B6305941 : Blo 1474557 6305941 := bbase (se 6 (by rfl) ⟨147795, by rfl⟩ : syracuseStep 6305941 = 295591) (by norm_num)
theorem B1661089 : Blo 1474557 1661089 := bbase (se 2 (by rfl) ⟨622908, by rfl⟩ : syracuseStep 1661089 = 1245817) (by norm_num)
theorem B4978853 : Blo 1474557 4978853 := bbase (se 4 (by rfl) ⟨466767, by rfl⟩ : syracuseStep 4978853 = 933535) (by norm_num)
theorem B3733685 : Blo 1474557 3733685 := bbase (se 5 (by rfl) ⟨175016, by rfl⟩ : syracuseStep 3733685 = 350033) (by norm_num)
theorem B1661125 : Blo 1474557 1661125 := bbase (se 4 (by rfl) ⟨155730, by rfl⟩ : syracuseStep 1661125 = 311461) (by norm_num)
theorem B2488549 : Blo 1474557 2488549 := bbase (se 4 (by rfl) ⟨233301, by rfl⟩ : syracuseStep 2488549 = 466603) (by norm_num)
theorem B3152117 : Blo 1474557 3152117 := bbase (se 5 (by rfl) ⟨147755, by rfl⟩ : syracuseStep 3152117 = 295511) (by norm_num)
theorem B7469333 : Blo 1474557 7469333 := bbase (se 6 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 7469333 = 350125) (by norm_num)
theorem B2488637 : Blo 1474557 2488637 := bbase (se 3 (by rfl) ⟨466619, by rfl⟩ : syracuseStep 2488637 = 933239) (by norm_num)
theorem B3733877 : Blo 1474557 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B2800021 : Blo 1474557 2800021 := bbase (se 6 (by rfl) ⟨65625, by rfl⟩ : syracuseStep 2800021 = 131251) (by norm_num)
theorem B12614069 : Blo 1474557 12614069 := bbase (se 5 (by rfl) ⟨591284, by rfl⟩ : syracuseStep 12614069 = 1182569) (by norm_num)
theorem B2488765 : Blo 1474557 2488765 := bbase (se 3 (by rfl) ⟨466643, by rfl⟩ : syracuseStep 2488765 = 933287) (by norm_num)
theorem B4725253 : Blo 1474557 4725253 := bbase (se 4 (by rfl) ⟨442992, by rfl⟩ : syracuseStep 4725253 = 885985) (by norm_num)
theorem B2488853 : Blo 1474557 2488853 := bbase (se 6 (by rfl) ⟨58332, by rfl⟩ : syracuseStep 2488853 = 116665) (by norm_num)
theorem B2800165 : Blo 1474557 2800165 := bbase (se 4 (by rfl) ⟨262515, by rfl⟩ : syracuseStep 2800165 = 525031) (by norm_num)
theorem B4979285 : Blo 1474557 4979285 := bbase (se 8 (by rfl) ⟨29175, by rfl⟩ : syracuseStep 4979285 = 58351) (by norm_num)
theorem B1866341 : Blo 1474557 1866341 := bbase (se 4 (by rfl) ⟨174969, by rfl⟩ : syracuseStep 1866341 = 349939) (by norm_num)
theorem B2488981 : Blo 1474557 2488981 := bbase (se 6 (by rfl) ⟨58335, by rfl⟩ : syracuseStep 2488981 = 116671) (by norm_num)
theorem B1866397 : Blo 1474557 1866397 := bbase (se 3 (by rfl) ⟨349949, by rfl⟩ : syracuseStep 1866397 = 699899) (by norm_num)
theorem B7977653 : Blo 1474557 7977653 := bbase (se 5 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 7977653 = 747905) (by norm_num)
theorem B2800325 : Blo 1474557 2800325 := bbase (se 4 (by rfl) ⟨262530, by rfl⟩ : syracuseStep 2800325 = 525061) (by norm_num)
theorem B3734221 : Blo 1474557 3734221 := bbase (se 3 (by rfl) ⟨700166, by rfl⟩ : syracuseStep 3734221 = 1400333) (by norm_num)
theorem B2489069 : Blo 1474557 2489069 := bbase (se 3 (by rfl) ⟨466700, by rfl⟩ : syracuseStep 2489069 = 933401) (by norm_num)
theorem B3152621 : Blo 1474557 3152621 := bbase (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) (by norm_num)
theorem B3152629 : Blo 1474557 3152629 := bbase (se 5 (by rfl) ⟨147779, by rfl⟩ : syracuseStep 3152629 = 295559) (by norm_num)
theorem B1866493 : Blo 1474557 1866493 := bbase (se 3 (by rfl) ⟨349967, by rfl⟩ : syracuseStep 1866493 = 699935) (by norm_num)
theorem B16800533 : Blo 1474557 16800533 := bbase (se 6 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 16800533 = 787525) (by norm_num)
theorem B3734333 : Blo 1474557 3734333 := bbase (se 3 (by rfl) ⟨700187, by rfl⟩ : syracuseStep 3734333 = 1400375) (by norm_num)
theorem B1596245 : Blo 1474557 1596245 := bbase (se 9 (by rfl) ⟨4676, by rfl⟩ : syracuseStep 1596245 = 9353) (by norm_num)
theorem B2800469 : Blo 1474557 2800469 := bbase (se 9 (by rfl) ⟨8204, by rfl⟩ : syracuseStep 2800469 = 16409) (by norm_num)
theorem B2489197 : Blo 1474557 2489197 := bbase (se 3 (by rfl) ⟨466724, by rfl⟩ : syracuseStep 2489197 = 933449) (by norm_num)
theorem B7093109 : Blo 1474557 7093109 := bbase (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) (by norm_num)
theorem B1866665 : Blo 1474557 1866665 := bbase (se 2 (by rfl) ⟨699999, by rfl⟩ : syracuseStep 1866665 = 1399999) (by norm_num)
theorem B5602229 : Blo 1474557 5602229 := bbase (se 5 (by rfl) ⟨262604, by rfl⟩ : syracuseStep 5602229 = 525209) (by norm_num)
theorem B2489285 : Blo 1474557 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B4488149 : Blo 1474557 4488149 := bbase (se 7 (by rfl) ⟨52595, by rfl⟩ : syracuseStep 4488149 = 105191) (by norm_num)
theorem B1866721 : Blo 1474557 1866721 := bbase (se 2 (by rfl) ⟨700020, by rfl⟩ : syracuseStep 1866721 = 1400041) (by norm_num)
theorem B3734525 : Blo 1474557 3734525 := bbase (se 3 (by rfl) ⟨700223, by rfl⟩ : syracuseStep 3734525 = 1400447) (by norm_num)
theorem B4979717 : Blo 1474557 4979717 := bbase (se 4 (by rfl) ⟨466848, by rfl⟩ : syracuseStep 4979717 = 933697) (by norm_num)
theorem B3365909 : Blo 1474557 3365909 := bbase (se 6 (by rfl) ⟨78888, by rfl⟩ : syracuseStep 3365909 = 157777) (by norm_num)
theorem B1866817 : Blo 1474557 1866817 := bbase (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) (by norm_num)
theorem B2489413 : Blo 1474557 2489413 := bbase (se 4 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 2489413 = 466765) (by norm_num)
theorem B2800757 : Blo 1474557 2800757 := bbase (se 5 (by rfl) ⟨131285, by rfl⟩ : syracuseStep 2800757 = 262571) (by norm_num)
theorem B2489501 : Blo 1474557 2489501 := bbase (se 3 (by rfl) ⟨466781, by rfl⟩ : syracuseStep 2489501 = 933563) (by norm_num)
theorem B5602517 : Blo 1474557 5602517 := bbase (se 7 (by rfl) ⟨65654, by rfl⟩ : syracuseStep 5602517 = 131309) (by norm_num)
theorem B1866989 : Blo 1474557 1866989 := bbase (se 3 (by rfl) ⟨350060, by rfl⟩ : syracuseStep 1866989 = 700121) (by norm_num)
theorem B2800909 : Blo 1474557 2800909 := bbase (se 3 (by rfl) ⟨525170, by rfl⟩ : syracuseStep 2800909 = 1050341) (by norm_num)
theorem B2489629 : Blo 1474557 2489629 := bbase (se 3 (by rfl) ⟨466805, by rfl⟩ : syracuseStep 2489629 = 933611) (by norm_num)
theorem B1867045 : Blo 1474557 1867045 := bbase (se 4 (by rfl) ⟨175035, by rfl⟩ : syracuseStep 1867045 = 350071) (by norm_num)
theorem B2694485 : Blo 1474557 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B3734869 : Blo 1474557 3734869 := bbase (se 11 (by rfl) ⟨2735, by rfl⟩ : syracuseStep 3734869 = 5471) (by norm_num)
theorem B2489717 : Blo 1474557 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B1867141 : Blo 1474557 1867141 := bbase (se 4 (by rfl) ⟨175044, by rfl⟩ : syracuseStep 1867141 = 350089) (by norm_num)
theorem B3546517 : Blo 1474557 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B1891765 : Blo 1474557 1891765 := bbase (se 5 (by rfl) ⟨88676, by rfl⟩ : syracuseStep 1891765 = 177353) (by norm_num)
theorem B4980149 : Blo 1474557 4980149 := bbase (se 5 (by rfl) ⟨233444, by rfl⟩ : syracuseStep 4980149 = 466889) (by norm_num)
theorem B3734981 : Blo 1474557 3734981 := bbase (se 4 (by rfl) ⟨350154, by rfl⟩ : syracuseStep 3734981 = 700309) (by norm_num)
theorem B4259285 : Blo 1474557 4259285 := bbase (se 7 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 4259285 = 99827) (by norm_num)
theorem B2489845 : Blo 1474557 2489845 := bbase (se 5 (by rfl) ⟨116711, by rfl⟩ : syracuseStep 2489845 = 233423) (by norm_num)
theorem B7470629 : Blo 1474557 7470629 := bbase (se 4 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 7470629 = 1400743) (by norm_num)
theorem B1867313 : Blo 1474557 1867313 := bbase (se 2 (by rfl) ⟨700242, by rfl⟩ : syracuseStep 1867313 = 1400485) (by norm_num)
theorem B2801213 : Blo 1474557 2801213 := bbase (se 3 (by rfl) ⟨525227, by rfl⟩ : syracuseStep 2801213 = 1050455) (by norm_num)
theorem B2489933 : Blo 1474557 2489933 := bbase (se 3 (by rfl) ⟨466862, by rfl⟩ : syracuseStep 2489933 = 933725) (by norm_num)
theorem B1867369 : Blo 1474557 1867369 := bbase (se 2 (by rfl) ⟨700263, by rfl⟩ : syracuseStep 1867369 = 1400527) (by norm_num)
theorem B3735173 : Blo 1474557 3735173 := bbase (se 4 (by rfl) ⟨350172, by rfl⟩ : syracuseStep 3735173 = 700345) (by norm_num)
theorem B1867465 : Blo 1474557 1867465 := bbase (se 2 (by rfl) ⟨700299, by rfl⟩ : syracuseStep 1867465 = 1400599) (by norm_num)
theorem B2490061 : Blo 1474557 2490061 := bbase (se 3 (by rfl) ⟨466886, by rfl⟩ : syracuseStep 2490061 = 933773) (by norm_num)
theorem B2490149 : Blo 1474557 2490149 := bbase (se 4 (by rfl) ⟨233451, by rfl⟩ : syracuseStep 2490149 = 466903) (by norm_num)
theorem B1892165 : Blo 1474557 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B4726613 : Blo 1474557 4726613 := bbase (se 9 (by rfl) ⟨13847, by rfl⟩ : syracuseStep 4726613 = 27695) (by norm_num)
theorem B4980581 : Blo 1474557 4980581 := bbase (se 4 (by rfl) ⟨466929, by rfl⟩ : syracuseStep 4980581 = 933859) (by norm_num)
theorem B1867637 : Blo 1474557 1867637 := bbase (se 5 (by rfl) ⟨87545, by rfl⟩ : syracuseStep 1867637 = 175091) (by norm_num)
theorem B2490277 : Blo 1474557 2490277 := bbase (se 4 (by rfl) ⟨233463, by rfl⟩ : syracuseStep 2490277 = 466927) (by norm_num)
theorem B3366821 : Blo 1474557 3366821 := bbase (se 4 (by rfl) ⟨315639, by rfl⟩ : syracuseStep 3366821 = 631279) (by norm_num)
theorem B1867693 : Blo 1474557 1867693 := bbase (se 3 (by rfl) ⟨350192, by rfl⟩ : syracuseStep 1867693 = 700385) (by norm_num)
theorem B3735517 : Blo 1474557 3735517 := bbase (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) (by norm_num)
theorem B2490365 : Blo 1474557 2490365 := bbase (se 3 (by rfl) ⟨466943, by rfl⟩ : syracuseStep 2490365 = 933887) (by norm_num)
theorem B1474563 : Blo 1474557 1474563 := bstep (se 1 (by rfl) ⟨1105922, by rfl⟩ : syracuseStep 1474563 = 2211845) B2211845
theorem B9453581 : Blo 1474557 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B3317777 : Blo 1474557 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B2211857 : Blo 1474557 2211857 := bstep (se 2 (by rfl) ⟨829446, by rfl⟩ : syracuseStep 2211857 = 1658893) B1658893
theorem B1474579 : Blo 1474557 1474579 := bstep (se 1 (by rfl) ⟨1105934, by rfl⟩ : syracuseStep 1474579 = 2211869) B2211869
theorem B8405005 : Blo 1474557 8405005 := bstep (se 3 (by rfl) ⟨1575938, by rfl⟩ : syracuseStep 8405005 = 3151877) B3151877
theorem B2490385 : Blo 1474557 2490385 := bstep (se 2 (by rfl) ⟨933894, by rfl⟩ : syracuseStep 2490385 = 1867789) B1867789
theorem B3317795 : Blo 1474557 3317795 := bstep (se 1 (by rfl) ⟨2488346, by rfl⟩ : syracuseStep 3317795 = 4976693) B4976693
theorem B2211875 : Blo 1474557 2211875 := bstep (se 1 (by rfl) ⟨1658906, by rfl⟩ : syracuseStep 2211875 = 3317813) B3317813
theorem B1474595 : Blo 1474557 1474595 := bstep (se 1 (by rfl) ⟨1105946, by rfl⟩ : syracuseStep 1474595 = 2211893) B2211893
theorem B2801699 : Blo 1474557 2801699 := bstep (se 1 (by rfl) ⟨2101274, by rfl⟩ : syracuseStep 2801699 = 4202549) B4202549
theorem B7782449 : Blo 1474557 7782449 := bstep (se 2 (by rfl) ⟨2918418, by rfl⟩ : syracuseStep 7782449 = 5836837) B5836837
theorem B1474611 : Blo 1474557 1474611 := bstep (se 1 (by rfl) ⟨1105958, by rfl⟩ : syracuseStep 1474611 = 2211917) B2211917
theorem B2490419 : Blo 1474557 2490419 := bstep (se 1 (by rfl) ⟨1867814, by rfl⟩ : syracuseStep 2490419 = 3735629) B3735629
theorem B2211905 : Blo 1474557 2211905 := bstep (se 2 (by rfl) ⟨829464, by rfl⟩ : syracuseStep 2211905 = 1658929) B1658929
theorem B1474627 : Blo 1474557 1474627 := bstep (se 1 (by rfl) ⟨1105970, by rfl⟩ : syracuseStep 1474627 = 2211941) B2211941
theorem B2211923 : Blo 1474557 2211923 := bstep (se 1 (by rfl) ⟨1658942, by rfl⟩ : syracuseStep 2211923 = 3317885) B3317885
theorem B1474643 : Blo 1474557 1474643 := bstep (se 1 (by rfl) ⟨1105982, by rfl⟩ : syracuseStep 1474643 = 2211965) B2211965
theorem B1474659 : Blo 1474557 1474659 := bstep (se 1 (by rfl) ⟨1105994, by rfl⟩ : syracuseStep 1474659 = 2211989) B2211989
theorem B2211953 : Blo 1474557 2211953 := bstep (se 2 (by rfl) ⟨829482, by rfl⟩ : syracuseStep 2211953 = 1658965) B1658965
theorem B1474675 : Blo 1474557 1474675 := bstep (se 1 (by rfl) ⟨1106006, by rfl⟩ : syracuseStep 1474675 = 2212013) B2212013
theorem B2211971 : Blo 1474557 2211971 := bstep (se 1 (by rfl) ⟨1658978, by rfl⟩ : syracuseStep 2211971 = 3317957) B3317957
theorem B1474691 : Blo 1474557 1474691 := bstep (se 1 (by rfl) ⟨1106018, by rfl⟩ : syracuseStep 1474691 = 2212037) B2212037
theorem B1474707 : Blo 1474557 1474707 := bstep (se 1 (by rfl) ⟨1106030, by rfl⟩ : syracuseStep 1474707 = 2212061) B2212061
theorem B2212001 : Blo 1474557 2212001 := bstep (se 2 (by rfl) ⟨829500, by rfl⟩ : syracuseStep 2212001 = 1659001) B1659001
theorem B1474723 : Blo 1474557 1474723 := bstep (se 1 (by rfl) ⟨1106042, by rfl⟩ : syracuseStep 1474723 = 2212085) B2212085
theorem B2212019 : Blo 1474557 2212019 := bstep (se 1 (by rfl) ⟨1659014, by rfl⟩ : syracuseStep 2212019 = 3318029) B3318029
theorem B1474739 : Blo 1474557 1474739 := bstep (se 1 (by rfl) ⟨1106054, by rfl⟩ : syracuseStep 1474739 = 2212109) B2212109
theorem B2490547 : Blo 1474557 2490547 := bstep (se 1 (by rfl) ⟨1867910, by rfl⟩ : syracuseStep 2490547 = 3735821) B3735821
theorem B1474755 : Blo 1474557 1474755 := bstep (se 1 (by rfl) ⟨1106066, by rfl⟩ : syracuseStep 1474755 = 2212133) B2212133
theorem B2212049 : Blo 1474557 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B1474771 : Blo 1474557 1474771 := bstep (se 1 (by rfl) ⟨1106078, by rfl⟩ : syracuseStep 1474771 = 2212157) B2212157
theorem B2212067 : Blo 1474557 2212067 := bstep (se 1 (by rfl) ⟨1659050, by rfl⟩ : syracuseStep 2212067 = 3318101) B3318101
theorem B1474787 : Blo 1474557 1474787 := bstep (se 1 (by rfl) ⟨1106090, by rfl⟩ : syracuseStep 1474787 = 2212181) B2212181
theorem B1474803 : Blo 1474557 1474803 := bstep (se 1 (by rfl) ⟨1106102, by rfl⟩ : syracuseStep 1474803 = 2212205) B2212205
theorem B2212097 : Blo 1474557 2212097 := bstep (se 2 (by rfl) ⟨829536, by rfl⟩ : syracuseStep 2212097 = 1659073) B1659073
theorem B1474819 : Blo 1474557 1474819 := bstep (se 1 (by rfl) ⟨1106114, by rfl⟩ : syracuseStep 1474819 = 2212229) B2212229
theorem B2212115 : Blo 1474557 2212115 := bstep (se 1 (by rfl) ⟨1659086, by rfl⟩ : syracuseStep 2212115 = 3318173) B3318173
theorem B1474835 : Blo 1474557 1474835 := bstep (se 1 (by rfl) ⟨1106126, by rfl⟩ : syracuseStep 1474835 = 2212253) B2212253
theorem B1474851 : Blo 1474557 1474851 := bstep (se 1 (by rfl) ⟨1106138, by rfl⟩ : syracuseStep 1474851 = 2212277) B2212277
theorem B4792621 : Blo 1474557 4792621 := bstep (se 3 (by rfl) ⟨898616, by rfl⟩ : syracuseStep 4792621 = 1797233) B1797233
theorem B3318065 : Blo 1474557 3318065 := bstep (se 2 (by rfl) ⟨1244274, by rfl⟩ : syracuseStep 3318065 = 2488549) B2488549
theorem B2212145 : Blo 1474557 2212145 := bstep (se 2 (by rfl) ⟨829554, by rfl⟩ : syracuseStep 2212145 = 1659109) B1659109
theorem B1474867 : Blo 1474557 1474867 := bstep (se 1 (by rfl) ⟨1106150, by rfl⟩ : syracuseStep 1474867 = 2212301) B2212301
theorem B2490689 : Blo 1474557 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B3318083 : Blo 1474557 3318083 := bstep (se 1 (by rfl) ⟨2488562, by rfl⟩ : syracuseStep 3318083 = 4977125) B4977125
theorem B2212163 : Blo 1474557 2212163 := bstep (se 1 (by rfl) ⟨1659122, by rfl⟩ : syracuseStep 2212163 = 3318245) B3318245
theorem B1474883 : Blo 1474557 1474883 := bstep (se 1 (by rfl) ⟨1106162, by rfl⟩ : syracuseStep 1474883 = 2212325) B2212325
theorem B1474899 : Blo 1474557 1474899 := bstep (se 1 (by rfl) ⟨1106174, by rfl⟩ : syracuseStep 1474899 = 2212349) B2212349
theorem B2212193 : Blo 1474557 2212193 := bstep (se 2 (by rfl) ⟨829572, by rfl⟩ : syracuseStep 2212193 = 1659145) B1659145
theorem B1474915 : Blo 1474557 1474915 := bstep (se 1 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 1474915 = 2212373) B2212373
theorem B5980529 : Blo 1474557 5980529 := bstep (se 2 (by rfl) ⟨2242698, by rfl⟩ : syracuseStep 5980529 = 4485397) B4485397
theorem B2212211 : Blo 1474557 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B1474931 : Blo 1474557 1474931 := bstep (se 1 (by rfl) ⟨1106198, by rfl⟩ : syracuseStep 1474931 = 2212397) B2212397
theorem B1474947 : Blo 1474557 1474947 := bstep (se 1 (by rfl) ⟨1106210, by rfl⟩ : syracuseStep 1474947 = 2212421) B2212421
theorem B2212241 : Blo 1474557 2212241 := bstep (se 2 (by rfl) ⟨829590, by rfl⟩ : syracuseStep 2212241 = 1659181) B1659181
theorem B1474963 : Blo 1474557 1474963 := bstep (se 1 (by rfl) ⟨1106222, by rfl⟩ : syracuseStep 1474963 = 2212445) B2212445
theorem B3735953 : Blo 1474557 3735953 := bstep (se 2 (by rfl) ⟨1400982, by rfl⟩ : syracuseStep 3735953 = 2801965) B2801965
theorem B1868179 : Blo 1474557 1868179 := bstep (se 1 (by rfl) ⟨1401134, by rfl⟩ : syracuseStep 1868179 = 2802269) B2802269
theorem B2212259 : Blo 1474557 2212259 := bstep (se 1 (by rfl) ⟨1659194, by rfl⟩ : syracuseStep 2212259 = 3318389) B3318389
theorem B1474979 : Blo 1474557 1474979 := bstep (se 1 (by rfl) ⟨1106234, by rfl⟩ : syracuseStep 1474979 = 2212469) B2212469
theorem B1474995 : Blo 1474557 1474995 := bstep (se 1 (by rfl) ⟨1106246, by rfl⟩ : syracuseStep 1474995 = 2212493) B2212493
theorem B2212289 : Blo 1474557 2212289 := bstep (se 2 (by rfl) ⟨829608, by rfl⟩ : syracuseStep 2212289 = 1659217) B1659217
theorem B1475011 : Blo 1474557 1475011 := bstep (se 1 (by rfl) ⟨1106258, by rfl⟩ : syracuseStep 1475011 = 2212517) B2212517
theorem B3736003 : Blo 1474557 3736003 := bstep (se 1 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 3736003 = 5604005) B5604005
theorem B2490817 : Blo 1474557 2490817 := bstep (se 2 (by rfl) ⟨934056, by rfl⟩ : syracuseStep 2490817 = 1868113) B1868113
theorem B2212307 : Blo 1474557 2212307 := bstep (se 1 (by rfl) ⟨1659230, by rfl⟩ : syracuseStep 2212307 = 3318461) B3318461
theorem B1475027 : Blo 1474557 1475027 := bstep (se 1 (by rfl) ⟨1106270, by rfl⟩ : syracuseStep 1475027 = 2212541) B2212541
theorem B1475043 : Blo 1474557 1475043 := bstep (se 1 (by rfl) ⟨1106282, by rfl⟩ : syracuseStep 1475043 = 2212565) B2212565
theorem B2490851 : Blo 1474557 2490851 := bstep (se 1 (by rfl) ⟨1868138, by rfl⟩ : syracuseStep 2490851 = 3736277) B3736277
theorem B4981229 : Blo 1474557 4981229 := bstep (se 3 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 4981229 = 1867961) B1867961
theorem B2212337 : Blo 1474557 2212337 := bstep (se 2 (by rfl) ⟨829626, by rfl⟩ : syracuseStep 2212337 = 1659253) B1659253
theorem B7471601 : Blo 1474557 7471601 := bstep (se 2 (by rfl) ⟨2801850, by rfl⟩ : syracuseStep 7471601 = 5603701) B5603701
theorem B1475059 : Blo 1474557 1475059 := bstep (se 1 (by rfl) ⟨1106294, by rfl⟩ : syracuseStep 1475059 = 2212589) B2212589
theorem B1868275 : Blo 1474557 1868275 := bstep (se 1 (by rfl) ⟨1401206, by rfl⟩ : syracuseStep 1868275 = 2802413) B2802413
theorem B2212355 : Blo 1474557 2212355 := bstep (se 1 (by rfl) ⟨1659266, by rfl⟩ : syracuseStep 2212355 = 3318533) B3318533
theorem B1475075 : Blo 1474557 1475075 := bstep (se 1 (by rfl) ⟨1106306, by rfl⟩ : syracuseStep 1475075 = 2212613) B2212613
theorem B3547651 : Blo 1474557 3547651 := bstep (se 1 (by rfl) ⟨2660738, by rfl⟩ : syracuseStep 3547651 = 5321477) B5321477
theorem B1475091 : Blo 1474557 1475091 := bstep (se 1 (by rfl) ⟨1106318, by rfl⟩ : syracuseStep 1475091 = 2212637) B2212637
theorem B2212385 : Blo 1474557 2212385 := bstep (se 2 (by rfl) ⟨829644, by rfl⟩ : syracuseStep 2212385 = 1659289) B1659289
theorem B1475107 : Blo 1474557 1475107 := bstep (se 1 (by rfl) ⟨1106330, by rfl⟩ : syracuseStep 1475107 = 2212661) B2212661
theorem B4981283 : Blo 1474557 4981283 := bstep (se 1 (by rfl) ⟨3735962, by rfl⟩ : syracuseStep 4981283 = 7471925) B7471925
theorem B2212403 : Blo 1474557 2212403 := bstep (se 1 (by rfl) ⟨1659302, by rfl⟩ : syracuseStep 2212403 = 3318605) B3318605
theorem B1475123 : Blo 1474557 1475123 := bstep (se 1 (by rfl) ⟨1106342, by rfl⟩ : syracuseStep 1475123 = 2212685) B2212685
theorem B163627573 : Blo 1474557 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B1475139 : Blo 1474557 1475139 := bstep (se 1 (by rfl) ⟨1106354, by rfl⟩ : syracuseStep 1475139 = 2212709) B2212709
theorem B3318353 : Blo 1474557 3318353 := bstep (se 2 (by rfl) ⟨1244382, by rfl⟩ : syracuseStep 3318353 = 2488765) B2488765
theorem B2212433 : Blo 1474557 2212433 := bstep (se 2 (by rfl) ⟨829662, by rfl⟩ : syracuseStep 2212433 = 1659325) B1659325
theorem B1475155 : Blo 1474557 1475155 := bstep (se 1 (by rfl) ⟨1106366, by rfl⟩ : syracuseStep 1475155 = 2212733) B2212733
theorem B3736145 : Blo 1474557 3736145 := bstep (se 2 (by rfl) ⟨1401054, by rfl⟩ : syracuseStep 3736145 = 2802109) B2802109
theorem B3318371 : Blo 1474557 3318371 := bstep (se 1 (by rfl) ⟨2488778, by rfl⟩ : syracuseStep 3318371 = 4977557) B4977557
theorem B2212451 : Blo 1474557 2212451 := bstep (se 1 (by rfl) ⟨1659338, by rfl⟩ : syracuseStep 2212451 = 3318677) B3318677
theorem B1475171 : Blo 1474557 1475171 := bstep (se 1 (by rfl) ⟨1106378, by rfl⟩ : syracuseStep 1475171 = 2212757) B2212757
theorem B2490979 : Blo 1474557 2490979 := bstep (se 1 (by rfl) ⟨1868234, by rfl⟩ : syracuseStep 2490979 = 3736469) B3736469
theorem B2523761 : Blo 1474557 2523761 := bstep (se 2 (by rfl) ⟨946410, by rfl⟩ : syracuseStep 2523761 = 1892821) B1892821
theorem B1475187 : Blo 1474557 1475187 := bstep (se 1 (by rfl) ⟨1106390, by rfl⟩ : syracuseStep 1475187 = 2212781) B2212781
theorem B2212481 : Blo 1474557 2212481 := bstep (se 2 (by rfl) ⟨829680, by rfl⟩ : syracuseStep 2212481 = 1659361) B1659361
theorem B1475203 : Blo 1474557 1475203 := bstep (se 1 (by rfl) ⟨1106402, by rfl⟩ : syracuseStep 1475203 = 2212805) B2212805
theorem B31900301 : Blo 1474557 31900301 := bstep (se 3 (by rfl) ⟨5981306, by rfl⟩ : syracuseStep 31900301 = 11962613) B11962613
theorem B2212499 : Blo 1474557 2212499 := bstep (se 1 (by rfl) ⟨1659374, by rfl⟩ : syracuseStep 2212499 = 3318749) B3318749
theorem B1475219 : Blo 1474557 1475219 := bstep (se 1 (by rfl) ⟨1106414, by rfl⟩ : syracuseStep 1475219 = 2212829) B2212829
theorem B1475235 : Blo 1474557 1475235 := bstep (se 1 (by rfl) ⟨1106426, by rfl⟩ : syracuseStep 1475235 = 2212853) B2212853
theorem B6300337 : Blo 1474557 6300337 := bstep (se 2 (by rfl) ⟨2362626, by rfl⟩ : syracuseStep 6300337 = 4725253) B4725253
theorem B2212529 : Blo 1474557 2212529 := bstep (se 2 (by rfl) ⟨829698, by rfl⟩ : syracuseStep 2212529 = 1659397) B1659397
theorem B1475251 : Blo 1474557 1475251 := bstep (se 1 (by rfl) ⟨1106438, by rfl⟩ : syracuseStep 1475251 = 2212877) B2212877
theorem B2212547 : Blo 1474557 2212547 := bstep (se 1 (by rfl) ⟨1659410, by rfl⟩ : syracuseStep 2212547 = 3318821) B3318821
theorem B1475267 : Blo 1474557 1475267 := bstep (se 1 (by rfl) ⟨1106450, by rfl⟩ : syracuseStep 1475267 = 2212901) B2212901
theorem B1475283 : Blo 1474557 1475283 := bstep (se 1 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 1475283 = 2212925) B2212925
theorem B2212577 : Blo 1474557 2212577 := bstep (se 2 (by rfl) ⟨829716, by rfl⟩ : syracuseStep 2212577 = 1659433) B1659433
theorem B1475299 : Blo 1474557 1475299 := bstep (se 1 (by rfl) ⟨1106474, by rfl⟩ : syracuseStep 1475299 = 2212949) B2212949
theorem B2491121 : Blo 1474557 2491121 := bstep (se 2 (by rfl) ⟨934170, by rfl⟩ : syracuseStep 2491121 = 1868341) B1868341
theorem B2212595 : Blo 1474557 2212595 := bstep (se 1 (by rfl) ⟨1659446, by rfl⟩ : syracuseStep 2212595 = 3318893) B3318893
theorem B1475315 : Blo 1474557 1475315 := bstep (se 1 (by rfl) ⟨1106486, by rfl⟩ : syracuseStep 1475315 = 2212973) B2212973
theorem B1475331 : Blo 1474557 1475331 := bstep (se 1 (by rfl) ⟨1106498, by rfl⟩ : syracuseStep 1475331 = 2212997) B2212997
theorem B2212625 : Blo 1474557 2212625 := bstep (se 2 (by rfl) ⟨829734, by rfl⟩ : syracuseStep 2212625 = 1659469) B1659469
theorem B1475347 : Blo 1474557 1475347 := bstep (se 1 (by rfl) ⟨1106510, by rfl⟩ : syracuseStep 1475347 = 2213021) B2213021
theorem B2212643 : Blo 1474557 2212643 := bstep (se 1 (by rfl) ⟨1659482, by rfl⟩ : syracuseStep 2212643 = 3318965) B3318965
theorem B1475363 : Blo 1474557 1475363 := bstep (se 1 (by rfl) ⟨1106522, by rfl⟩ : syracuseStep 1475363 = 2213045) B2213045
theorem B4981553 : Blo 1474557 4981553 := bstep (se 2 (by rfl) ⟨1868082, by rfl⟩ : syracuseStep 4981553 = 3736165) B3736165
theorem B1475379 : Blo 1474557 1475379 := bstep (se 1 (by rfl) ⟨1106534, by rfl⟩ : syracuseStep 1475379 = 2213069) B2213069
theorem B2212673 : Blo 1474557 2212673 := bstep (se 2 (by rfl) ⟨829752, by rfl⟩ : syracuseStep 2212673 = 1659505) B1659505
theorem B1475395 : Blo 1474557 1475395 := bstep (se 1 (by rfl) ⟨1106546, by rfl⟩ : syracuseStep 1475395 = 2213093) B2213093
theorem B5604173 : Blo 1474557 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B2212691 : Blo 1474557 2212691 := bstep (se 1 (by rfl) ⟨1659518, by rfl⟩ : syracuseStep 2212691 = 3319037) B3319037
theorem B1475411 : Blo 1474557 1475411 := bstep (se 1 (by rfl) ⟨1106558, by rfl⟩ : syracuseStep 1475411 = 2213117) B2213117
theorem B1475427 : Blo 1474557 1475427 := bstep (se 1 (by rfl) ⟨1106570, by rfl⟩ : syracuseStep 1475427 = 2213141) B2213141
theorem B3318641 : Blo 1474557 3318641 := bstep (se 2 (by rfl) ⟨1244490, by rfl⟩ : syracuseStep 3318641 = 2488981) B2488981
theorem B2212721 : Blo 1474557 2212721 := bstep (se 2 (by rfl) ⟨829770, by rfl⟩ : syracuseStep 2212721 = 1659541) B1659541
theorem B1475443 : Blo 1474557 1475443 := bstep (se 1 (by rfl) ⟨1106582, by rfl⟩ : syracuseStep 1475443 = 2213165) B2213165
theorem B4260721 : Blo 1474557 4260721 := bstep (se 2 (by rfl) ⟨1597770, by rfl⟩ : syracuseStep 4260721 = 3195541) B3195541
theorem B2491249 : Blo 1474557 2491249 := bstep (se 2 (by rfl) ⟨934218, by rfl⟩ : syracuseStep 2491249 = 1868437) B1868437
theorem B3318659 : Blo 1474557 3318659 := bstep (se 1 (by rfl) ⟨2488994, by rfl⟩ : syracuseStep 3318659 = 4977989) B4977989
theorem B2212739 : Blo 1474557 2212739 := bstep (se 1 (by rfl) ⟨1659554, by rfl⟩ : syracuseStep 2212739 = 3319109) B3319109
theorem B1475459 : Blo 1474557 1475459 := bstep (se 1 (by rfl) ⟨1106594, by rfl⟩ : syracuseStep 1475459 = 2213189) B2213189
theorem B53855117 : Blo 1474557 53855117 := bstep (se 3 (by rfl) ⟨10097834, by rfl⟩ : syracuseStep 53855117 = 20195669) B20195669
theorem B1475475 : Blo 1474557 1475475 := bstep (se 1 (by rfl) ⟨1106606, by rfl⟩ : syracuseStep 1475475 = 2213213) B2213213
theorem B2491283 : Blo 1474557 2491283 := bstep (se 1 (by rfl) ⟨1868462, by rfl⟩ : syracuseStep 2491283 = 3736925) B3736925
theorem B2212769 : Blo 1474557 2212769 := bstep (se 2 (by rfl) ⟨829788, by rfl⟩ : syracuseStep 2212769 = 1659577) B1659577
theorem B1475491 : Blo 1474557 1475491 := bstep (se 1 (by rfl) ⟨1106618, by rfl⟩ : syracuseStep 1475491 = 2213237) B2213237
theorem B2802595 : Blo 1474557 2802595 := bstep (se 1 (by rfl) ⟨2101946, by rfl⟩ : syracuseStep 2802595 = 4203893) B4203893
theorem B2212787 : Blo 1474557 2212787 := bstep (se 1 (by rfl) ⟨1659590, by rfl⟩ : syracuseStep 2212787 = 3319181) B3319181
theorem B1475507 : Blo 1474557 1475507 := bstep (se 1 (by rfl) ⟨1106630, by rfl⟩ : syracuseStep 1475507 = 2213261) B2213261
theorem B1475523 : Blo 1474557 1475523 := bstep (se 1 (by rfl) ⟨1106642, by rfl⟩ : syracuseStep 1475523 = 2213285) B2213285
theorem B2212817 : Blo 1474557 2212817 := bstep (se 2 (by rfl) ⟨829806, by rfl⟩ : syracuseStep 2212817 = 1659613) B1659613
theorem B1475539 : Blo 1474557 1475539 := bstep (se 1 (by rfl) ⟨1106654, by rfl⟩ : syracuseStep 1475539 = 2213309) B2213309
theorem B2212835 : Blo 1474557 2212835 := bstep (se 1 (by rfl) ⟨1659626, by rfl⟩ : syracuseStep 2212835 = 3319253) B3319253
theorem B1475555 : Blo 1474557 1475555 := bstep (se 1 (by rfl) ⟨1106666, by rfl⟩ : syracuseStep 1475555 = 2213333) B2213333
theorem B4203505 : Blo 1474557 4203505 := bstep (se 2 (by rfl) ⟨1576314, by rfl⟩ : syracuseStep 4203505 = 3152629) B3152629
theorem B1475571 : Blo 1474557 1475571 := bstep (se 1 (by rfl) ⟨1106678, by rfl⟩ : syracuseStep 1475571 = 2213357) B2213357
theorem B2212865 : Blo 1474557 2212865 := bstep (se 2 (by rfl) ⟨829824, by rfl⟩ : syracuseStep 2212865 = 1659649) B1659649
theorem B1475587 : Blo 1474557 1475587 := bstep (se 1 (by rfl) ⟨1106690, by rfl⟩ : syracuseStep 1475587 = 2213381) B2213381
theorem B2212883 : Blo 1474557 2212883 := bstep (se 1 (by rfl) ⟨1659662, by rfl⟩ : syracuseStep 2212883 = 3319325) B3319325
theorem B1475603 : Blo 1474557 1475603 := bstep (se 1 (by rfl) ⟨1106702, by rfl⟩ : syracuseStep 1475603 = 2213405) B2213405
theorem B2491411 : Blo 1474557 2491411 := bstep (se 1 (by rfl) ⟨1868558, by rfl⟩ : syracuseStep 2491411 = 3737117) B3737117
theorem B1475619 : Blo 1474557 1475619 := bstep (se 1 (by rfl) ⟨1106714, by rfl⟩ : syracuseStep 1475619 = 2213429) B2213429
theorem B2212913 : Blo 1474557 2212913 := bstep (se 2 (by rfl) ⟨829842, by rfl⟩ : syracuseStep 2212913 = 1659685) B1659685
theorem B1475635 : Blo 1474557 1475635 := bstep (se 1 (by rfl) ⟨1106726, by rfl⟩ : syracuseStep 1475635 = 2213453) B2213453
theorem B2212931 : Blo 1474557 2212931 := bstep (se 1 (by rfl) ⟨1659698, by rfl⟩ : syracuseStep 2212931 = 3319397) B3319397
theorem B1475651 : Blo 1474557 1475651 := bstep (se 1 (by rfl) ⟨1106738, by rfl⟩ : syracuseStep 1475651 = 2213477) B2213477
theorem B2802755 : Blo 1474557 2802755 := bstep (se 1 (by rfl) ⟨2102066, by rfl⟩ : syracuseStep 2802755 = 4204133) B4204133
theorem B1475667 : Blo 1474557 1475667 := bstep (se 1 (by rfl) ⟨1106750, by rfl⟩ : syracuseStep 1475667 = 2213501) B2213501
theorem B2212961 : Blo 1474557 2212961 := bstep (se 2 (by rfl) ⟨829860, by rfl⟩ : syracuseStep 2212961 = 1659721) B1659721
theorem B1475683 : Blo 1474557 1475683 := bstep (se 1 (by rfl) ⟨1106762, by rfl⟩ : syracuseStep 1475683 = 2213525) B2213525
theorem B2212979 : Blo 1474557 2212979 := bstep (se 1 (by rfl) ⟨1659734, by rfl⟩ : syracuseStep 2212979 = 3319469) B3319469
theorem B1475699 : Blo 1474557 1475699 := bstep (se 1 (by rfl) ⟨1106774, by rfl⟩ : syracuseStep 1475699 = 2213549) B2213549
theorem B1475715 : Blo 1474557 1475715 := bstep (se 1 (by rfl) ⟨1106786, by rfl⟩ : syracuseStep 1475715 = 2213573) B2213573
theorem B3318929 : Blo 1474557 3318929 := bstep (se 2 (by rfl) ⟨1244598, by rfl⟩ : syracuseStep 3318929 = 2489197) B2489197
theorem B2213009 : Blo 1474557 2213009 := bstep (se 2 (by rfl) ⟨829878, by rfl⟩ : syracuseStep 2213009 = 1659757) B1659757
theorem B1475731 : Blo 1474557 1475731 := bstep (se 1 (by rfl) ⟨1106798, by rfl⟩ : syracuseStep 1475731 = 2213597) B2213597
theorem B2491553 : Blo 1474557 2491553 := bstep (se 2 (by rfl) ⟨934332, by rfl⟩ : syracuseStep 2491553 = 1868665) B1868665
theorem B3318947 : Blo 1474557 3318947 := bstep (se 1 (by rfl) ⟨2489210, by rfl⟩ : syracuseStep 3318947 = 4978421) B4978421
theorem B2213027 : Blo 1474557 2213027 := bstep (se 1 (by rfl) ⟨1659770, by rfl⟩ : syracuseStep 2213027 = 3319541) B3319541
theorem B1475747 : Blo 1474557 1475747 := bstep (se 1 (by rfl) ⟨1106810, by rfl⟩ : syracuseStep 1475747 = 2213621) B2213621
theorem B1475763 : Blo 1474557 1475763 := bstep (se 1 (by rfl) ⟨1106822, by rfl⟩ : syracuseStep 1475763 = 2213645) B2213645
theorem B2213057 : Blo 1474557 2213057 := bstep (se 2 (by rfl) ⟨829896, by rfl⟩ : syracuseStep 2213057 = 1659793) B1659793
theorem B1475779 : Blo 1474557 1475779 := bstep (se 1 (by rfl) ⟨1106834, by rfl⟩ : syracuseStep 1475779 = 2213669) B2213669
theorem B2213075 : Blo 1474557 2213075 := bstep (se 1 (by rfl) ⟨1659806, by rfl⟩ : syracuseStep 2213075 = 3319613) B3319613
theorem B1475795 : Blo 1474557 1475795 := bstep (se 1 (by rfl) ⟨1106846, by rfl⟩ : syracuseStep 1475795 = 2213693) B2213693
theorem B1475811 : Blo 1474557 1475811 := bstep (se 1 (by rfl) ⟨1106858, by rfl⟩ : syracuseStep 1475811 = 2213717) B2213717
theorem B2213105 : Blo 1474557 2213105 := bstep (se 2 (by rfl) ⟨829914, by rfl⟩ : syracuseStep 2213105 = 1659829) B1659829
theorem B1475827 : Blo 1474557 1475827 := bstep (se 1 (by rfl) ⟨1106870, by rfl⟩ : syracuseStep 1475827 = 2213741) B2213741
theorem B2213123 : Blo 1474557 2213123 := bstep (se 1 (by rfl) ⟨1659842, by rfl⟩ : syracuseStep 2213123 = 3319685) B3319685
theorem B1475843 : Blo 1474557 1475843 := bstep (se 1 (by rfl) ⟨1106882, by rfl⟩ : syracuseStep 1475843 = 2213765) B2213765
theorem B1475859 : Blo 1474557 1475859 := bstep (se 1 (by rfl) ⟨1106894, by rfl⟩ : syracuseStep 1475859 = 2213789) B2213789
theorem B2213153 : Blo 1474557 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B1475875 : Blo 1474557 1475875 := bstep (se 1 (by rfl) ⟨1106906, by rfl⟩ : syracuseStep 1475875 = 2213813) B2213813
theorem B2491681 : Blo 1474557 2491681 := bstep (se 2 (by rfl) ⟨934380, by rfl⟩ : syracuseStep 2491681 = 1868761) B1868761
theorem B2213171 : Blo 1474557 2213171 := bstep (se 1 (by rfl) ⟨1659878, by rfl⟩ : syracuseStep 2213171 = 3319757) B3319757
theorem B1475891 : Blo 1474557 1475891 := bstep (se 1 (by rfl) ⟨1106918, by rfl⟩ : syracuseStep 1475891 = 2213837) B2213837
theorem B1475907 : Blo 1474557 1475907 := bstep (se 1 (by rfl) ⟨1106930, by rfl⟩ : syracuseStep 1475907 = 2213861) B2213861
theorem B4982093 : Blo 1474557 4982093 := bstep (se 3 (by rfl) ⟨934142, by rfl⟩ : syracuseStep 4982093 = 1868285) B1868285
theorem B2213201 : Blo 1474557 2213201 := bstep (se 2 (by rfl) ⟨829950, by rfl⟩ : syracuseStep 2213201 = 1659901) B1659901
theorem B1475923 : Blo 1474557 1475923 := bstep (se 1 (by rfl) ⟨1106942, by rfl⟩ : syracuseStep 1475923 = 2213885) B2213885
theorem B7087459 : Blo 1474557 7087459 := bstep (se 1 (by rfl) ⟨5315594, by rfl⟩ : syracuseStep 7087459 = 10631189) B10631189
theorem B2213219 : Blo 1474557 2213219 := bstep (se 1 (by rfl) ⟨1659914, by rfl⟩ : syracuseStep 2213219 = 3319829) B3319829
theorem B5317987 : Blo 1474557 5317987 := bstep (se 1 (by rfl) ⟨3988490, by rfl⟩ : syracuseStep 5317987 = 7976981) B7976981
theorem B1475939 : Blo 1474557 1475939 := bstep (se 1 (by rfl) ⟨1106954, by rfl⟩ : syracuseStep 1475939 = 2213909) B2213909
theorem B1475955 : Blo 1474557 1475955 := bstep (se 1 (by rfl) ⟨1106966, by rfl⟩ : syracuseStep 1475955 = 2213933) B2213933
theorem B2213249 : Blo 1474557 2213249 := bstep (se 2 (by rfl) ⟨829968, by rfl⟩ : syracuseStep 2213249 = 1659937) B1659937
theorem B3786115 : Blo 1474557 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B1475971 : Blo 1474557 1475971 := bstep (se 1 (by rfl) ⟨1106978, by rfl⟩ : syracuseStep 1475971 = 2213957) B2213957
theorem B4982147 : Blo 1474557 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B2213267 : Blo 1474557 2213267 := bstep (se 1 (by rfl) ⟨1659950, by rfl⟩ : syracuseStep 2213267 = 3319901) B3319901
theorem B1475987 : Blo 1474557 1475987 := bstep (se 1 (by rfl) ⟨1106990, by rfl⟩ : syracuseStep 1475987 = 2213981) B2213981
theorem B1476003 : Blo 1474557 1476003 := bstep (se 1 (by rfl) ⟨1107002, by rfl⟩ : syracuseStep 1476003 = 2214005) B2214005
theorem B3319217 : Blo 1474557 3319217 := bstep (se 2 (by rfl) ⟨1244706, by rfl⟩ : syracuseStep 3319217 = 2489413) B2489413
theorem B2213297 : Blo 1474557 2213297 := bstep (se 2 (by rfl) ⟨829986, by rfl⟩ : syracuseStep 2213297 = 1659973) B1659973
theorem B9586097 : Blo 1474557 9586097 := bstep (se 2 (by rfl) ⟨3594786, by rfl⟩ : syracuseStep 9586097 = 7189573) B7189573
theorem B1476019 : Blo 1474557 1476019 := bstep (se 1 (by rfl) ⟨1107014, by rfl⟩ : syracuseStep 1476019 = 2214029) B2214029
theorem B3319235 : Blo 1474557 3319235 := bstep (se 1 (by rfl) ⟨2489426, by rfl⟩ : syracuseStep 3319235 = 4978853) B4978853
theorem B2213315 : Blo 1474557 2213315 := bstep (se 1 (by rfl) ⟨1659986, by rfl⟩ : syracuseStep 2213315 = 3319973) B3319973
theorem B1476035 : Blo 1474557 1476035 := bstep (se 1 (by rfl) ⟨1107026, by rfl⟩ : syracuseStep 1476035 = 2214053) B2214053
theorem B1476051 : Blo 1474557 1476051 := bstep (se 1 (by rfl) ⟨1107038, by rfl⟩ : syracuseStep 1476051 = 2214077) B2214077
theorem B2213345 : Blo 1474557 2213345 := bstep (se 2 (by rfl) ⟨830004, by rfl⟩ : syracuseStep 2213345 = 1660009) B1660009
theorem B1476067 : Blo 1474557 1476067 := bstep (se 1 (by rfl) ⟨1107050, by rfl⟩ : syracuseStep 1476067 = 2214101) B2214101
theorem B2213363 : Blo 1474557 2213363 := bstep (se 1 (by rfl) ⟨1660022, by rfl⟩ : syracuseStep 2213363 = 3320045) B3320045
theorem B1476083 : Blo 1474557 1476083 := bstep (se 1 (by rfl) ⟨1107062, by rfl⟩ : syracuseStep 1476083 = 2214125) B2214125
theorem B1476099 : Blo 1474557 1476099 := bstep (se 1 (by rfl) ⟨1107074, by rfl⟩ : syracuseStep 1476099 = 2214149) B2214149
theorem B2213393 : Blo 1474557 2213393 := bstep (se 2 (by rfl) ⟨830022, by rfl⟩ : syracuseStep 2213393 = 1660045) B1660045
theorem B1476115 : Blo 1474557 1476115 := bstep (se 1 (by rfl) ⟨1107086, by rfl⟩ : syracuseStep 1476115 = 2214173) B2214173
theorem B2213411 : Blo 1474557 2213411 := bstep (se 1 (by rfl) ⟨1660058, by rfl⟩ : syracuseStep 2213411 = 3320117) B3320117
theorem B1476131 : Blo 1474557 1476131 := bstep (se 1 (by rfl) ⟨1107098, by rfl⟩ : syracuseStep 1476131 = 2214197) B2214197
theorem B1476147 : Blo 1474557 1476147 := bstep (se 1 (by rfl) ⟨1107110, by rfl⟩ : syracuseStep 1476147 = 2214221) B2214221
theorem B3737137 : Blo 1474557 3737137 := bstep (se 2 (by rfl) ⟨1401426, by rfl⟩ : syracuseStep 3737137 = 2802853) B2802853
theorem B2213441 : Blo 1474557 2213441 := bstep (se 2 (by rfl) ⟨830040, by rfl⟩ : syracuseStep 2213441 = 1660081) B1660081
theorem B1476163 : Blo 1474557 1476163 := bstep (se 1 (by rfl) ⟨1107122, by rfl⟩ : syracuseStep 1476163 = 2214245) B2214245
theorem B2213459 : Blo 1474557 2213459 := bstep (se 1 (by rfl) ⟨1660094, by rfl⟩ : syracuseStep 2213459 = 3320189) B3320189
theorem B1476179 : Blo 1474557 1476179 := bstep (se 1 (by rfl) ⟨1107134, by rfl⟩ : syracuseStep 1476179 = 2214269) B2214269
theorem B1476195 : Blo 1474557 1476195 := bstep (se 1 (by rfl) ⟨1107146, by rfl⟩ : syracuseStep 1476195 = 2214293) B2214293
theorem B2213489 : Blo 1474557 2213489 := bstep (se 2 (by rfl) ⟨830058, by rfl⟩ : syracuseStep 2213489 = 1660117) B1660117
theorem B5604977 : Blo 1474557 5604977 := bstep (se 2 (by rfl) ⟨2101866, by rfl⟩ : syracuseStep 5604977 = 4203733) B4203733
theorem B1476211 : Blo 1474557 1476211 := bstep (se 1 (by rfl) ⟨1107158, by rfl⟩ : syracuseStep 1476211 = 2214317) B2214317
theorem B2213507 : Blo 1474557 2213507 := bstep (se 1 (by rfl) ⟨1660130, by rfl⟩ : syracuseStep 2213507 = 3320261) B3320261
theorem B1476227 : Blo 1474557 1476227 := bstep (se 1 (by rfl) ⟨1107170, by rfl⟩ : syracuseStep 1476227 = 2214341) B2214341
theorem B4982417 : Blo 1474557 4982417 := bstep (se 2 (by rfl) ⟨1868406, by rfl⟩ : syracuseStep 4982417 = 3736813) B3736813
theorem B1476243 : Blo 1474557 1476243 := bstep (se 1 (by rfl) ⟨1107182, by rfl⟩ : syracuseStep 1476243 = 2214365) B2214365
theorem B2213537 : Blo 1474557 2213537 := bstep (se 2 (by rfl) ⟨830076, by rfl⟩ : syracuseStep 2213537 = 1660153) B1660153
theorem B1476259 : Blo 1474557 1476259 := bstep (se 1 (by rfl) ⟨1107194, by rfl⟩ : syracuseStep 1476259 = 2214389) B2214389
theorem B2213555 : Blo 1474557 2213555 := bstep (se 1 (by rfl) ⟨1660166, by rfl⟩ : syracuseStep 2213555 = 3320333) B3320333
theorem B1476275 : Blo 1474557 1476275 := bstep (se 1 (by rfl) ⟨1107206, by rfl⟩ : syracuseStep 1476275 = 2214413) B2214413
theorem B1476291 : Blo 1474557 1476291 := bstep (se 1 (by rfl) ⟨1107218, by rfl⟩ : syracuseStep 1476291 = 2214437) B2214437
theorem B3319505 : Blo 1474557 3319505 := bstep (se 2 (by rfl) ⟨1244814, by rfl⟩ : syracuseStep 3319505 = 2489629) B2489629
theorem B2213585 : Blo 1474557 2213585 := bstep (se 2 (by rfl) ⟨830094, by rfl⟩ : syracuseStep 2213585 = 1660189) B1660189
theorem B1476307 : Blo 1474557 1476307 := bstep (se 1 (by rfl) ⟨1107230, by rfl⟩ : syracuseStep 1476307 = 2214461) B2214461
theorem B4261585 : Blo 1474557 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B3319523 : Blo 1474557 3319523 := bstep (se 1 (by rfl) ⟨2489642, by rfl⟩ : syracuseStep 3319523 = 4979285) B4979285
theorem B2213603 : Blo 1474557 2213603 := bstep (se 1 (by rfl) ⟨1660202, by rfl⟩ : syracuseStep 2213603 = 3320405) B3320405
theorem B1476323 : Blo 1474557 1476323 := bstep (se 1 (by rfl) ⟨1107242, by rfl⟩ : syracuseStep 1476323 = 2214485) B2214485
theorem B7980785 : Blo 1474557 7980785 := bstep (se 2 (by rfl) ⟨2992794, by rfl⟩ : syracuseStep 7980785 = 5985589) B5985589
theorem B1476339 : Blo 1474557 1476339 := bstep (se 1 (by rfl) ⟨1107254, by rfl⟩ : syracuseStep 1476339 = 2214509) B2214509
theorem B2213633 : Blo 1474557 2213633 := bstep (se 2 (by rfl) ⟨830112, by rfl⟩ : syracuseStep 2213633 = 1660225) B1660225
theorem B1476355 : Blo 1474557 1476355 := bstep (se 1 (by rfl) ⟨1107266, by rfl⟩ : syracuseStep 1476355 = 2214533) B2214533
theorem B2213651 : Blo 1474557 2213651 := bstep (se 1 (by rfl) ⟨1660238, by rfl⟩ : syracuseStep 2213651 = 3320477) B3320477
theorem B1476371 : Blo 1474557 1476371 := bstep (se 1 (by rfl) ⟨1107278, by rfl⟩ : syracuseStep 1476371 = 2214557) B2214557
theorem B5318435 : Blo 1474557 5318435 := bstep (se 1 (by rfl) ⟨3988826, by rfl⟩ : syracuseStep 5318435 = 7977653) B7977653
theorem B1476387 : Blo 1474557 1476387 := bstep (se 1 (by rfl) ⟨1107290, by rfl⟩ : syracuseStep 1476387 = 2214581) B2214581
theorem B2213681 : Blo 1474557 2213681 := bstep (se 2 (by rfl) ⟨830130, by rfl⟩ : syracuseStep 2213681 = 1660261) B1660261
theorem B1476403 : Blo 1474557 1476403 := bstep (se 1 (by rfl) ⟨1107302, by rfl⟩ : syracuseStep 1476403 = 2214605) B2214605
theorem B2213699 : Blo 1474557 2213699 := bstep (se 1 (by rfl) ⟨1660274, by rfl⟩ : syracuseStep 2213699 = 3320549) B3320549
theorem B1476419 : Blo 1474557 1476419 := bstep (se 1 (by rfl) ⟨1107314, by rfl⟩ : syracuseStep 1476419 = 2214629) B2214629
theorem B3737411 : Blo 1474557 3737411 := bstep (se 1 (by rfl) ⟨2803058, by rfl⟩ : syracuseStep 3737411 = 5606117) B5606117
theorem B5318477 : Blo 1474557 5318477 := bstep (se 3 (by rfl) ⟨997214, by rfl⟩ : syracuseStep 5318477 = 1994429) B1994429
theorem B1476435 : Blo 1474557 1476435 := bstep (se 1 (by rfl) ⟨1107326, by rfl⟩ : syracuseStep 1476435 = 2214653) B2214653
theorem B2213729 : Blo 1474557 2213729 := bstep (se 2 (by rfl) ⟨830148, by rfl⟩ : syracuseStep 2213729 = 1660297) B1660297
theorem B11200355 : Blo 1474557 11200355 := bstep (se 1 (by rfl) ⟨8400266, by rfl⟩ : syracuseStep 11200355 = 16800533) B16800533
theorem B1476451 : Blo 1474557 1476451 := bstep (se 1 (by rfl) ⟨1107338, by rfl⟩ : syracuseStep 1476451 = 2214677) B2214677
theorem B4728689 : Blo 1474557 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B2213747 : Blo 1474557 2213747 := bstep (se 1 (by rfl) ⟨1660310, by rfl⟩ : syracuseStep 2213747 = 3320621) B3320621
theorem B1476467 : Blo 1474557 1476467 := bstep (se 1 (by rfl) ⟨1107350, by rfl⟩ : syracuseStep 1476467 = 2214701) B2214701
theorem B1476483 : Blo 1474557 1476483 := bstep (se 1 (by rfl) ⟨1107362, by rfl⟩ : syracuseStep 1476483 = 2214725) B2214725
theorem B2213777 : Blo 1474557 2213777 := bstep (se 2 (by rfl) ⟨830166, by rfl⟩ : syracuseStep 2213777 = 1660333) B1660333
theorem B1476499 : Blo 1474557 1476499 := bstep (se 1 (by rfl) ⟨1107374, by rfl⟩ : syracuseStep 1476499 = 2214749) B2214749
theorem B2213795 : Blo 1474557 2213795 := bstep (se 1 (by rfl) ⟨1660346, by rfl⟩ : syracuseStep 2213795 = 3320693) B3320693
theorem B4728739 : Blo 1474557 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B7473059 : Blo 1474557 7473059 := bstep (se 1 (by rfl) ⟨5604794, by rfl⟩ : syracuseStep 7473059 = 11209589) B11209589
theorem B1476515 : Blo 1474557 1476515 := bstep (se 1 (by rfl) ⟨1107386, by rfl⟩ : syracuseStep 1476515 = 2214773) B2214773
theorem B1476531 : Blo 1474557 1476531 := bstep (se 1 (by rfl) ⟨1107398, by rfl⟩ : syracuseStep 1476531 = 2214797) B2214797
theorem B2213825 : Blo 1474557 2213825 := bstep (se 2 (by rfl) ⟨830184, by rfl⟩ : syracuseStep 2213825 = 1660369) B1660369
theorem B1476547 : Blo 1474557 1476547 := bstep (se 1 (by rfl) ⟨1107410, by rfl⟩ : syracuseStep 1476547 = 2214821) B2214821
theorem B8406989 : Blo 1474557 8406989 := bstep (se 3 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 8406989 = 3152621) B3152621
theorem B2213843 : Blo 1474557 2213843 := bstep (se 1 (by rfl) ⟨1660382, by rfl⟩ : syracuseStep 2213843 = 3320765) B3320765
theorem B2992099 : Blo 1474557 2992099 := bstep (se 1 (by rfl) ⟨2244074, by rfl⟩ : syracuseStep 2992099 = 4488149) B4488149
theorem B3319793 : Blo 1474557 3319793 := bstep (se 2 (by rfl) ⟨1244922, by rfl⟩ : syracuseStep 3319793 = 2489845) B2489845
theorem B2213873 : Blo 1474557 2213873 := bstep (se 2 (by rfl) ⟨830202, by rfl⟩ : syracuseStep 2213873 = 1660405) B1660405
theorem B3319811 : Blo 1474557 3319811 := bstep (se 1 (by rfl) ⟨2489858, by rfl⟩ : syracuseStep 3319811 = 4979717) B4979717
theorem B2213891 : Blo 1474557 2213891 := bstep (se 1 (by rfl) ⟨1660418, by rfl⟩ : syracuseStep 2213891 = 3320837) B3320837
theorem B2213921 : Blo 1474557 2213921 := bstep (se 2 (by rfl) ⟨830220, by rfl⟩ : syracuseStep 2213921 = 1660441) B1660441
theorem B2213939 : Blo 1474557 2213939 := bstep (se 1 (by rfl) ⟨1660454, by rfl⟩ : syracuseStep 2213939 = 3320909) B3320909
theorem B8521805 : Blo 1474557 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B2213969 : Blo 1474557 2213969 := bstep (se 2 (by rfl) ⟨830238, by rfl⟩ : syracuseStep 2213969 = 1660477) B1660477
theorem B2213987 : Blo 1474557 2213987 := bstep (se 1 (by rfl) ⟨1660490, by rfl⟩ : syracuseStep 2213987 = 3320981) B3320981
theorem B21284977 : Blo 1474557 21284977 := bstep (se 2 (by rfl) ⟨7981866, by rfl⟩ : syracuseStep 21284977 = 15963733) B15963733
theorem B2214017 : Blo 1474557 2214017 := bstep (se 2 (by rfl) ⟨830256, by rfl⟩ : syracuseStep 2214017 = 1660513) B1660513
theorem B2214035 : Blo 1474557 2214035 := bstep (se 1 (by rfl) ⟨1660526, by rfl⟩ : syracuseStep 2214035 = 3321053) B3321053
theorem B4982957 : Blo 1474557 4982957 := bstep (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) B1868609
theorem B6817969 : Blo 1474557 6817969 := bstep (se 2 (by rfl) ⟨2556738, by rfl⟩ : syracuseStep 6817969 = 5113477) B5113477
theorem B2214065 : Blo 1474557 2214065 := bstep (se 2 (by rfl) ⟨830274, by rfl⟩ : syracuseStep 2214065 = 1660549) B1660549
theorem B2214083 : Blo 1474557 2214083 := bstep (se 1 (by rfl) ⟨1660562, by rfl⟩ : syracuseStep 2214083 = 3321125) B3321125
theorem B2214113 : Blo 1474557 2214113 := bstep (se 2 (by rfl) ⟨830292, by rfl⟩ : syracuseStep 2214113 = 1660585) B1660585
theorem B1796323 : Blo 1474557 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B4983011 : Blo 1474557 4983011 := bstep (se 1 (by rfl) ⟨3737258, by rfl⟩ : syracuseStep 4983011 = 7474517) B7474517
theorem B2214131 : Blo 1474557 2214131 := bstep (se 1 (by rfl) ⟨1660598, by rfl⟩ : syracuseStep 2214131 = 3321197) B3321197
theorem B5605645 : Blo 1474557 5605645 := bstep (se 3 (by rfl) ⟨1051058, by rfl⟩ : syracuseStep 5605645 = 2102117) B2102117
theorem B3320081 : Blo 1474557 3320081 := bstep (se 2 (by rfl) ⟨1245030, by rfl⟩ : syracuseStep 3320081 = 2490061) B2490061
theorem B2214161 : Blo 1474557 2214161 := bstep (se 2 (by rfl) ⟨830310, by rfl⟩ : syracuseStep 2214161 = 1660621) B1660621
theorem B3320099 : Blo 1474557 3320099 := bstep (se 1 (by rfl) ⟨2490074, by rfl⟩ : syracuseStep 3320099 = 4980149) B4980149
theorem B2214179 : Blo 1474557 2214179 := bstep (se 1 (by rfl) ⟨1660634, by rfl⟩ : syracuseStep 2214179 = 3321269) B3321269
theorem B6064433 : Blo 1474557 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B2214209 : Blo 1474557 2214209 := bstep (se 2 (by rfl) ⟨830328, by rfl⟩ : syracuseStep 2214209 = 1660657) B1660657
theorem B8399173 : Blo 1474557 8399173 := bstep (se 4 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 8399173 = 1574845) B1574845
theorem B2214227 : Blo 1474557 2214227 := bstep (se 1 (by rfl) ⟨1660670, by rfl⟩ : syracuseStep 2214227 = 3321341) B3321341
theorem B2214257 : Blo 1474557 2214257 := bstep (se 2 (by rfl) ⟨830346, by rfl⟩ : syracuseStep 2214257 = 1660693) B1660693
theorem B2525555 : Blo 1474557 2525555 := bstep (se 1 (by rfl) ⟨1894166, by rfl⟩ : syracuseStep 2525555 = 3788333) B3788333
theorem B2214275 : Blo 1474557 2214275 := bstep (se 1 (by rfl) ⟨1660706, by rfl⟩ : syracuseStep 2214275 = 3321413) B3321413
theorem B2214305 : Blo 1474557 2214305 := bstep (se 2 (by rfl) ⟨830364, by rfl⟩ : syracuseStep 2214305 = 1660729) B1660729
theorem B2214323 : Blo 1474557 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B2214353 : Blo 1474557 2214353 := bstep (se 2 (by rfl) ⟨830382, by rfl⟩ : syracuseStep 2214353 = 1660765) B1660765
theorem B2214371 : Blo 1474557 2214371 := bstep (se 1 (by rfl) ⟨1660778, by rfl⟩ : syracuseStep 2214371 = 3321557) B3321557
theorem B4983281 : Blo 1474557 4983281 := bstep (se 2 (by rfl) ⟨1868730, by rfl⟩ : syracuseStep 4983281 = 3737461) B3737461
theorem B2214401 : Blo 1474557 2214401 := bstep (se 2 (by rfl) ⟨830400, by rfl⟩ : syracuseStep 2214401 = 1660801) B1660801
theorem B2214419 : Blo 1474557 2214419 := bstep (se 1 (by rfl) ⟨1660814, by rfl⟩ : syracuseStep 2214419 = 3321629) B3321629
theorem B3320369 : Blo 1474557 3320369 := bstep (se 2 (by rfl) ⟨1245138, by rfl⟩ : syracuseStep 3320369 = 2490277) B2490277
theorem B2214449 : Blo 1474557 2214449 := bstep (se 2 (by rfl) ⟨830418, by rfl⟩ : syracuseStep 2214449 = 1660837) B1660837
theorem B3320387 : Blo 1474557 3320387 := bstep (se 1 (by rfl) ⟨2490290, by rfl⟩ : syracuseStep 3320387 = 4980581) B4980581
theorem B2214467 : Blo 1474557 2214467 := bstep (se 1 (by rfl) ⟨1660850, by rfl⟩ : syracuseStep 2214467 = 3321701) B3321701
theorem B2214497 : Blo 1474557 2214497 := bstep (se 2 (by rfl) ⟨830436, by rfl⟩ : syracuseStep 2214497 = 1660873) B1660873
theorem B2214515 : Blo 1474557 2214515 := bstep (se 1 (by rfl) ⟨1660886, by rfl⟩ : syracuseStep 2214515 = 3321773) B3321773
theorem B2214545 : Blo 1474557 2214545 := bstep (se 2 (by rfl) ⟨830454, by rfl⟩ : syracuseStep 2214545 = 1660909) B1660909
theorem B2214563 : Blo 1474557 2214563 := bstep (se 1 (by rfl) ⟨1660922, by rfl⟩ : syracuseStep 2214563 = 3321845) B3321845
theorem B2214593 : Blo 1474557 2214593 := bstep (se 2 (by rfl) ⟨830472, by rfl⟩ : syracuseStep 2214593 = 1660945) B1660945
theorem B7473869 : Blo 1474557 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B2214611 : Blo 1474557 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B2099953 : Blo 1474557 2099953 := bstep (se 2 (by rfl) ⟨787482, by rfl⟩ : syracuseStep 2099953 = 1574965) B1574965
theorem B4729585 : Blo 1474557 4729585 := bstep (se 2 (by rfl) ⟨1773594, by rfl⟩ : syracuseStep 4729585 = 3547189) B3547189
theorem B2214641 : Blo 1474557 2214641 := bstep (se 2 (by rfl) ⟨830490, by rfl⟩ : syracuseStep 2214641 = 1660981) B1660981
theorem B2214659 : Blo 1474557 2214659 := bstep (se 1 (by rfl) ⟨1660994, by rfl⟩ : syracuseStep 2214659 = 3321989) B3321989
theorem B2214689 : Blo 1474557 2214689 := bstep (se 2 (by rfl) ⟨830508, by rfl⟩ : syracuseStep 2214689 = 1661017) B1661017
theorem B2214707 : Blo 1474557 2214707 := bstep (se 1 (by rfl) ⟨1661030, by rfl⟩ : syracuseStep 2214707 = 3322061) B3322061
theorem B3320657 : Blo 1474557 3320657 := bstep (se 2 (by rfl) ⟨1245246, by rfl⟩ : syracuseStep 3320657 = 2490493) B2490493
theorem B2214737 : Blo 1474557 2214737 := bstep (se 2 (by rfl) ⟨830526, by rfl⟩ : syracuseStep 2214737 = 1661053) B1661053
theorem B2362211 : Blo 1474557 2362211 := bstep (se 1 (by rfl) ⟨1771658, by rfl⟩ : syracuseStep 2362211 = 3543317) B3543317
theorem B3320675 : Blo 1474557 3320675 := bstep (se 1 (by rfl) ⟨2490506, by rfl⟩ : syracuseStep 3320675 = 4981013) B4981013
theorem B2214755 : Blo 1474557 2214755 := bstep (se 1 (by rfl) ⟨1661066, by rfl⟩ : syracuseStep 2214755 = 3322133) B3322133
theorem B8407921 : Blo 1474557 8407921 := bstep (se 2 (by rfl) ⟨3152970, by rfl⟩ : syracuseStep 8407921 = 6305941) B6305941
theorem B2214785 : Blo 1474557 2214785 := bstep (se 2 (by rfl) ⟨830544, by rfl⟩ : syracuseStep 2214785 = 1661089) B1661089
theorem B1575811 : Blo 1474557 1575811 := bstep (se 1 (by rfl) ⟨1181858, by rfl⟩ : syracuseStep 1575811 = 2363717) B2363717
theorem B2214803 : Blo 1474557 2214803 := bstep (se 1 (by rfl) ⟨1661102, by rfl⟩ : syracuseStep 2214803 = 3322205) B3322205
theorem B2214833 : Blo 1474557 2214833 := bstep (se 2 (by rfl) ⟨830562, by rfl⟩ : syracuseStep 2214833 = 1661125) B1661125
theorem B1682371 : Blo 1474557 1682371 := bstep (se 1 (by rfl) ⟨1261778, by rfl⟩ : syracuseStep 1682371 = 2523557) B2523557
theorem B9448433 : Blo 1474557 9448433 := bstep (se 2 (by rfl) ⟨3543162, by rfl⟩ : syracuseStep 9448433 = 7086325) B7086325
theorem B9456709 : Blo 1474557 9456709 := bstep (se 4 (by rfl) ⟨886566, by rfl⟩ : syracuseStep 9456709 = 1773133) B1773133
theorem B3320945 : Blo 1474557 3320945 := bstep (se 2 (by rfl) ⟨1245354, by rfl⟩ : syracuseStep 3320945 = 2490709) B2490709
theorem B3320963 : Blo 1474557 3320963 := bstep (se 1 (by rfl) ⟨2490722, by rfl⟩ : syracuseStep 3320963 = 4981445) B4981445
theorem B7089457 : Blo 1474557 7089457 := bstep (se 2 (by rfl) ⟨2658546, by rfl⟩ : syracuseStep 7089457 = 5317093) B5317093
theorem B3321233 : Blo 1474557 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B3321251 : Blo 1474557 3321251 := bstep (se 1 (by rfl) ⟨2490938, by rfl⟩ : syracuseStep 3321251 = 4981877) B4981877
theorem B7466417 : Blo 1474557 7466417 := bstep (se 2 (by rfl) ⟨2799906, by rfl⟩ : syracuseStep 7466417 = 5599813) B5599813
theorem B2100659 : Blo 1474557 2100659 := bstep (se 1 (by rfl) ⟨1575494, by rfl⟩ : syracuseStep 2100659 = 3150989) B3150989
theorem B17026613 : Blo 1474557 17026613 := bstep (se 5 (by rfl) ⟨798122, by rfl⟩ : syracuseStep 17026613 = 1596245) B1596245
theorem B2395745 : Blo 1474557 2395745 := bstep (se 2 (by rfl) ⟨898404, by rfl⟩ : syracuseStep 2395745 = 1796809) B1796809
theorem B3321521 : Blo 1474557 3321521 := bstep (se 2 (by rfl) ⟨1245570, by rfl⟩ : syracuseStep 3321521 = 2491141) B2491141
theorem B1494707 : Blo 1474557 1494707 := bstep (se 1 (by rfl) ⟨1121030, by rfl⟩ : syracuseStep 1494707 = 2242061) B2242061
theorem B4484803 : Blo 1474557 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B3321539 : Blo 1474557 3321539 := bstep (se 1 (by rfl) ⟨2491154, by rfl⟩ : syracuseStep 3321539 = 4982309) B4982309
theorem B4484899 : Blo 1474557 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B5115683 : Blo 1474557 5115683 := bstep (se 1 (by rfl) ⟨3836762, by rfl⟩ : syracuseStep 5115683 = 7673525) B7673525
theorem B2363185 : Blo 1474557 2363185 := bstep (se 2 (by rfl) ⟨886194, by rfl⟩ : syracuseStep 2363185 = 1772389) B1772389
theorem B1773427 : Blo 1474557 1773427 := bstep (se 1 (by rfl) ⟨1330070, by rfl⟩ : syracuseStep 1773427 = 2660141) B2660141
theorem B15150989 : Blo 1474557 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B3321809 : Blo 1474557 3321809 := bstep (se 2 (by rfl) ⟨1245678, by rfl⟩ : syracuseStep 3321809 = 2491357) B2491357
theorem B3321827 : Blo 1474557 3321827 := bstep (se 1 (by rfl) ⟨2491370, by rfl⟩ : syracuseStep 3321827 = 4982741) B4982741
theorem B2101297 : Blo 1474557 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B1658947 : Blo 1474557 1658947 := bstep (se 1 (by rfl) ⟨1244210, by rfl⟩ : syracuseStep 1658947 = 2488421) B2488421
theorem B17027171 : Blo 1474557 17027171 := bstep (se 1 (by rfl) ⟨12770378, by rfl⟩ : syracuseStep 17027171 = 25540757) B25540757
theorem B8974469 : Blo 1474557 8974469 := bstep (se 4 (by rfl) ⟨841356, by rfl⟩ : syracuseStep 8974469 = 1682713) B1682713
theorem B2101411 : Blo 1474557 2101411 := bstep (se 1 (by rfl) ⟨1576058, by rfl⟩ : syracuseStep 2101411 = 3152117) B3152117
theorem B1659091 : Blo 1474557 1659091 := bstep (se 1 (by rfl) ⟨1244318, by rfl⟩ : syracuseStep 1659091 = 2488637) B2488637
theorem B3322097 : Blo 1474557 3322097 := bstep (se 2 (by rfl) ⟨1245786, by rfl⟩ : syracuseStep 3322097 = 2491573) B2491573
theorem B3322115 : Blo 1474557 3322115 := bstep (se 1 (by rfl) ⟨2491586, by rfl⟩ : syracuseStep 3322115 = 4983173) B4983173
theorem B8401157 : Blo 1474557 8401157 := bstep (se 4 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 8401157 = 1575217) B1575217
theorem B4976909 : Blo 1474557 4976909 := bstep (se 3 (by rfl) ⟨933170, by rfl⟩ : syracuseStep 4976909 = 1866341) B1866341
theorem B6304013 : Blo 1474557 6304013 := bstep (se 3 (by rfl) ⟨1182002, by rfl⟩ : syracuseStep 6304013 = 2364005) B2364005
theorem B8409379 : Blo 1474557 8409379 := bstep (se 1 (by rfl) ⟨6307034, by rfl⟩ : syracuseStep 8409379 = 12614069) B12614069
theorem B5050669 : Blo 1474557 5050669 := bstep (se 3 (by rfl) ⟨947000, by rfl⟩ : syracuseStep 5050669 = 1894001) B1894001
theorem B4976963 : Blo 1474557 4976963 := bstep (se 1 (by rfl) ⟨3732722, by rfl⟩ : syracuseStep 4976963 = 7465445) B7465445
theorem B3150161 : Blo 1474557 3150161 := bstep (se 2 (by rfl) ⟨1181310, by rfl⟩ : syracuseStep 3150161 = 2362621) B2362621
theorem B1659235 : Blo 1474557 1659235 := bstep (se 1 (by rfl) ⟨1244426, by rfl⟩ : syracuseStep 1659235 = 2488853) B2488853
theorem B5599601 : Blo 1474557 5599601 := bstep (se 2 (by rfl) ⟨2099850, by rfl⟩ : syracuseStep 5599601 = 4199701) B4199701
theorem B1995121 : Blo 1474557 1995121 := bstep (se 2 (by rfl) ⟨748170, by rfl⟩ : syracuseStep 1995121 = 1496341) B1496341
theorem B9449891 : Blo 1474557 9449891 := bstep (se 1 (by rfl) ⟨7087418, by rfl⟩ : syracuseStep 9449891 = 14174837) B14174837
theorem B17953265 : Blo 1474557 17953265 := bstep (se 2 (by rfl) ⟨6732474, by rfl⟩ : syracuseStep 17953265 = 13464949) B13464949
theorem B1659379 : Blo 1474557 1659379 := bstep (se 1 (by rfl) ⟨1244534, by rfl⟩ : syracuseStep 1659379 = 2489069) B2489069
theorem B6730289 : Blo 1474557 6730289 := bstep (se 2 (by rfl) ⟨2523858, by rfl⟩ : syracuseStep 6730289 = 5047717) B5047717
theorem B4977233 : Blo 1474557 4977233 := bstep (se 2 (by rfl) ⟨1866462, by rfl⟩ : syracuseStep 4977233 = 3732925) B3732925
theorem B1659523 : Blo 1474557 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B12612293 : Blo 1474557 12612293 := bstep (se 4 (by rfl) ⟨1182402, by rfl⟩ : syracuseStep 12612293 = 2364805) B2364805
theorem B2364113 : Blo 1474557 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B11211533 : Blo 1474557 11211533 := bstep (se 3 (by rfl) ⟨2102162, by rfl⟩ : syracuseStep 11211533 = 4204325) B4204325
theorem B1659667 : Blo 1474557 1659667 := bstep (se 1 (by rfl) ⟨1244750, by rfl⟩ : syracuseStep 1659667 = 2489501) B2489501
theorem B7467875 : Blo 1474557 7467875 := bstep (se 1 (by rfl) ⟨5600906, by rfl⟩ : syracuseStep 7467875 = 11201813) B11201813
theorem B1659811 : Blo 1474557 1659811 := bstep (se 1 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 1659811 = 2489717) B2489717
theorem B3412945 : Blo 1474557 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B7975921 : Blo 1474557 7975921 := bstep (se 2 (by rfl) ⟨2990970, by rfl⟩ : syracuseStep 7975921 = 5981941) B5981941
theorem B10089521 : Blo 1474557 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B1659955 : Blo 1474557 1659955 := bstep (se 1 (by rfl) ⟨1244966, by rfl⟩ : syracuseStep 1659955 = 2489933) B2489933
theorem B4977773 : Blo 1474557 4977773 := bstep (se 3 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 4977773 = 1866665) B1866665
theorem B2430065 : Blo 1474557 2430065 := bstep (se 2 (by rfl) ⟨911274, by rfl⟩ : syracuseStep 2430065 = 1822549) B1822549
theorem B4977827 : Blo 1474557 4977827 := bstep (se 1 (by rfl) ⟨3733370, by rfl⟩ : syracuseStep 4977827 = 7466741) B7466741
theorem B1660099 : Blo 1474557 1660099 := bstep (se 1 (by rfl) ⟨1245074, by rfl⟩ : syracuseStep 1660099 = 2490149) B2490149
theorem B4199633 : Blo 1474557 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B3151057 : Blo 1474557 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B3151075 : Blo 1474557 3151075 := bstep (se 1 (by rfl) ⟨2363306, by rfl⟩ : syracuseStep 3151075 = 4726613) B4726613
theorem B1660243 : Blo 1474557 1660243 := bstep (se 1 (by rfl) ⟨1245182, by rfl⟩ : syracuseStep 1660243 = 2490365) B2490365
theorem B16799075 : Blo 1474557 16799075 := bstep (se 1 (by rfl) ⟨12599306, by rfl⟩ : syracuseStep 16799075 = 25198613) B25198613
theorem B7673201 : Blo 1474557 7673201 := bstep (se 2 (by rfl) ⟨2877450, by rfl⟩ : syracuseStep 7673201 = 5754901) B5754901
theorem B4978097 : Blo 1474557 4978097 := bstep (se 2 (by rfl) ⟨1866786, by rfl⟩ : syracuseStep 4978097 = 3733573) B3733573
theorem B1660387 : Blo 1474557 1660387 := bstep (se 1 (by rfl) ⟨1245290, by rfl⟩ : syracuseStep 1660387 = 2490581) B2490581
theorem B2364947 : Blo 1474557 2364947 := bstep (se 1 (by rfl) ⟨1773710, by rfl⟩ : syracuseStep 2364947 = 3547421) B3547421
theorem B2364979 : Blo 1474557 2364979 := bstep (se 1 (by rfl) ⟨1773734, by rfl⟩ : syracuseStep 2364979 = 3547469) B3547469
theorem B1660531 : Blo 1474557 1660531 := bstep (se 1 (by rfl) ⟨1245398, by rfl⟩ : syracuseStep 1660531 = 2490797) B2490797
theorem B26908301 : Blo 1474557 26908301 := bstep (se 3 (by rfl) ⟨5045306, by rfl⟩ : syracuseStep 26908301 = 10090613) B10090613
theorem B7468685 : Blo 1474557 7468685 := bstep (se 3 (by rfl) ⟨1400378, by rfl⟩ : syracuseStep 7468685 = 2800757) B2800757
theorem B3987107 : Blo 1474557 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B2021059 : Blo 1474557 2021059 := bstep (se 1 (by rfl) ⟨1515794, by rfl⟩ : syracuseStep 2021059 = 3031589) B3031589
theorem B3987149 : Blo 1474557 3987149 := bstep (se 3 (by rfl) ⟨747590, by rfl⟩ : syracuseStep 3987149 = 1495181) B1495181
theorem B1660675 : Blo 1474557 1660675 := bstep (se 1 (by rfl) ⟨1245506, by rfl⟩ : syracuseStep 1660675 = 2491013) B2491013
theorem B5601059 : Blo 1474557 5601059 := bstep (se 1 (by rfl) ⟨4200794, by rfl⟩ : syracuseStep 5601059 = 8401589) B8401589
theorem B3733361 : Blo 1474557 3733361 := bstep (se 2 (by rfl) ⟨1400010, by rfl⟩ : syracuseStep 3733361 = 2800021) B2800021
theorem B2840465 : Blo 1474557 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1660819 : Blo 1474557 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B3733411 : Blo 1474557 3733411 := bstep (se 1 (by rfl) ⟨2800058, by rfl⟩ : syracuseStep 3733411 = 5600117) B5600117
theorem B3545009 : Blo 1474557 3545009 := bstep (se 2 (by rfl) ⟨1329378, by rfl⟩ : syracuseStep 3545009 = 2658757) B2658757
theorem B4978637 : Blo 1474557 4978637 := bstep (se 3 (by rfl) ⟨933494, by rfl⟩ : syracuseStep 4978637 = 1866989) B1866989
theorem B4978691 : Blo 1474557 4978691 := bstep (se 1 (by rfl) ⟨3734018, by rfl⟩ : syracuseStep 4978691 = 7468037) B7468037
theorem B1660963 : Blo 1474557 1660963 := bstep (se 1 (by rfl) ⟨1245722, by rfl⟩ : syracuseStep 1660963 = 2491445) B2491445
theorem B3733553 : Blo 1474557 3733553 := bstep (se 2 (by rfl) ⟨1400082, by rfl⟩ : syracuseStep 3733553 = 2800165) B2800165
theorem B20183093 : Blo 1474557 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B2488387 : Blo 1474557 2488387 := bstep (se 1 (by rfl) ⟨1866290, by rfl⟩ : syracuseStep 2488387 = 3732581) B3732581
theorem B5314673 : Blo 1474557 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B4200589 : Blo 1474557 4200589 := bstep (se 3 (by rfl) ⟨787610, by rfl⟩ : syracuseStep 4200589 = 1575221) B1575221
theorem B1661107 : Blo 1474557 1661107 := bstep (se 1 (by rfl) ⟨1245830, by rfl⟩ : syracuseStep 1661107 = 2491661) B2491661
theorem B2488529 : Blo 1474557 2488529 := bstep (se 2 (by rfl) ⟨933198, by rfl⟩ : syracuseStep 2488529 = 1866397) B1866397
theorem B5314787 : Blo 1474557 5314787 := bstep (se 1 (by rfl) ⟨3986090, by rfl⟩ : syracuseStep 5314787 = 7972181) B7972181
theorem B4978961 : Blo 1474557 4978961 := bstep (se 2 (by rfl) ⟨1867110, by rfl⟩ : syracuseStep 4978961 = 3734221) B3734221
theorem B2488657 : Blo 1474557 2488657 := bstep (se 2 (by rfl) ⟨933246, by rfl⟩ : syracuseStep 2488657 = 1866493) B1866493
theorem B4200817 : Blo 1474557 4200817 := bstep (se 2 (by rfl) ⟨1575306, by rfl⟩ : syracuseStep 4200817 = 3150613) B3150613
theorem B2488691 : Blo 1474557 2488691 := bstep (se 1 (by rfl) ⟨1866518, by rfl⟩ : syracuseStep 2488691 = 3733037) B3733037
theorem B8632739 : Blo 1474557 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B2488819 : Blo 1474557 2488819 := bstep (se 1 (by rfl) ⟨1866614, by rfl⟩ : syracuseStep 2488819 = 3733229) B3733229
theorem B4200977 : Blo 1474557 4200977 := bstep (se 2 (by rfl) ⟨1575366, by rfl⟩ : syracuseStep 4200977 = 3150733) B3150733
theorem B45439541 : Blo 1474557 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B2800241 : Blo 1474557 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B2488961 : Blo 1474557 2488961 := bstep (se 2 (by rfl) ⟨933360, by rfl⟩ : syracuseStep 2488961 = 1866721) B1866721
theorem B4201091 : Blo 1474557 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B3545777 : Blo 1474557 3545777 := bstep (se 2 (by rfl) ⟨1329666, by rfl⟩ : syracuseStep 3545777 = 2659333) B2659333
theorem B4725485 : Blo 1474557 4725485 := bstep (se 3 (by rfl) ⟨886028, by rfl⟩ : syracuseStep 4725485 = 1772057) B1772057
theorem B2489089 : Blo 1474557 2489089 := bstep (se 2 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 2489089 = 1866817) B1866817
theorem B5602061 : Blo 1474557 5602061 := bstep (se 3 (by rfl) ⟨1050386, by rfl⟩ : syracuseStep 5602061 = 2100773) B2100773
theorem B2489123 : Blo 1474557 2489123 := bstep (se 1 (by rfl) ⟨1866842, by rfl⟩ : syracuseStep 2489123 = 3733685) B3733685
theorem B4979501 : Blo 1474557 4979501 := bstep (se 3 (by rfl) ⟨933656, by rfl⟩ : syracuseStep 4979501 = 1867313) B1867313
theorem B14179141 : Blo 1474557 14179141 := bstep (se 4 (by rfl) ⟨1329294, by rfl⟩ : syracuseStep 14179141 = 2658589) B2658589
theorem B4979555 : Blo 1474557 4979555 := bstep (se 1 (by rfl) ⟨3734666, by rfl⟩ : syracuseStep 4979555 = 7469333) B7469333
theorem B8969093 : Blo 1474557 8969093 := bstep (se 4 (by rfl) ⟨840852, by rfl⟩ : syracuseStep 8969093 = 1681705) B1681705
theorem B2489251 : Blo 1474557 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B12598213 : Blo 1474557 12598213 := bstep (se 4 (by rfl) ⟨1181082, by rfl⟩ : syracuseStep 12598213 = 2362165) B2362165
theorem B7093261 : Blo 1474557 7093261 := bstep (se 3 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 7093261 = 2659973) B2659973
theorem B3734545 : Blo 1474557 3734545 := bstep (se 2 (by rfl) ⟨1400454, by rfl⟩ : syracuseStep 3734545 = 2800909) B2800909
theorem B2489393 : Blo 1474557 2489393 := bstep (se 2 (by rfl) ⟨933522, by rfl⟩ : syracuseStep 2489393 = 1867045) B1867045
theorem B11205701 : Blo 1474557 11205701 := bstep (se 4 (by rfl) ⟨1050534, by rfl⟩ : syracuseStep 11205701 = 2101069) B2101069
theorem B4979825 : Blo 1474557 4979825 := bstep (se 2 (by rfl) ⟨1867434, by rfl⟩ : syracuseStep 4979825 = 3734869) B3734869
theorem B1866883 : Blo 1474557 1866883 := bstep (se 1 (by rfl) ⟨1400162, by rfl⟩ : syracuseStep 1866883 = 2800325) B2800325
theorem B2489521 : Blo 1474557 2489521 := bstep (se 2 (by rfl) ⟨933570, by rfl⟩ : syracuseStep 2489521 = 1867141) B1867141
theorem B2489555 : Blo 1474557 2489555 := bstep (se 1 (by rfl) ⟨1867166, by rfl⟩ : syracuseStep 2489555 = 3734333) B3734333
theorem B1866979 : Blo 1474557 1866979 := bstep (se 1 (by rfl) ⟨1400234, by rfl⟩ : syracuseStep 1866979 = 2800469) B2800469
theorem B2522353 : Blo 1474557 2522353 := bstep (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) B1891765
theorem B3734819 : Blo 1474557 3734819 := bstep (se 1 (by rfl) ⟨2801114, by rfl⟩ : syracuseStep 3734819 = 5602229) B5602229
theorem B11509061 : Blo 1474557 11509061 := bstep (se 4 (by rfl) ⟨1078974, by rfl⟩ : syracuseStep 11509061 = 2157949) B2157949
theorem B2489683 : Blo 1474557 2489683 := bstep (se 1 (by rfl) ⟨1867262, by rfl⟩ : syracuseStep 2489683 = 3734525) B3734525
theorem B2243939 : Blo 1474557 2243939 := bstep (se 1 (by rfl) ⟨1682954, by rfl⟩ : syracuseStep 2243939 = 3365909) B3365909
theorem B3153347 : Blo 1474557 3153347 := bstep (se 1 (by rfl) ⟨2365010, by rfl⟩ : syracuseStep 3153347 = 4730021) B4730021
theorem B2489825 : Blo 1474557 2489825 := bstep (se 2 (by rfl) ⟨933684, by rfl⟩ : syracuseStep 2489825 = 1867369) B1867369
theorem B3735011 : Blo 1474557 3735011 := bstep (se 1 (by rfl) ⟨2801258, by rfl⟩ : syracuseStep 3735011 = 5602517) B5602517
theorem B2801137 : Blo 1474557 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B12606961 : Blo 1474557 12606961 := bstep (se 2 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 12606961 = 9455221) B9455221
theorem B3989009 : Blo 1474557 3989009 := bstep (se 2 (by rfl) ⟨1495878, by rfl⟩ : syracuseStep 3989009 = 2991757) B2991757
theorem B45432373 : Blo 1474557 45432373 := bstep (se 5 (by rfl) ⟨2129642, by rfl⟩ : syracuseStep 45432373 = 4259285) B4259285
theorem B2489953 : Blo 1474557 2489953 := bstep (se 2 (by rfl) ⟨933732, by rfl⟩ : syracuseStep 2489953 = 1867465) B1867465
theorem B4202093 : Blo 1474557 4202093 := bstep (se 3 (by rfl) ⟨787892, by rfl⟩ : syracuseStep 4202093 = 1575785) B1575785
theorem B2489987 : Blo 1474557 2489987 := bstep (se 1 (by rfl) ⟨1867490, by rfl⟩ : syracuseStep 2489987 = 3734981) B3734981
theorem B4980365 : Blo 1474557 4980365 := bstep (se 3 (by rfl) ⟨933818, by rfl⟩ : syracuseStep 4980365 = 1867637) B1867637
theorem B2801297 : Blo 1474557 2801297 := bstep (se 2 (by rfl) ⟨1050486, by rfl⟩ : syracuseStep 2801297 = 2100973) B2100973
theorem B4980419 : Blo 1474557 4980419 := bstep (se 1 (by rfl) ⟨3735314, by rfl⟩ : syracuseStep 4980419 = 7470629) B7470629
theorem B1867475 : Blo 1474557 1867475 := bstep (se 1 (by rfl) ⟨1400606, by rfl⟩ : syracuseStep 1867475 = 2801213) B2801213
theorem B2490115 : Blo 1474557 2490115 := bstep (se 1 (by rfl) ⟨1867586, by rfl⟩ : syracuseStep 2490115 = 3735173) B3735173
theorem B4202275 : Blo 1474557 4202275 := bstep (se 1 (by rfl) ⟨3151706, by rfl⟩ : syracuseStep 4202275 = 6303413) B6303413
theorem B18898757 : Blo 1474557 18898757 := bstep (se 4 (by rfl) ⟨1771758, by rfl⟩ : syracuseStep 18898757 = 3543517) B3543517
theorem B2490257 : Blo 1474557 2490257 := bstep (se 2 (by rfl) ⟨933846, by rfl⟩ : syracuseStep 2490257 = 1867693) B1867693
theorem B4202435 : Blo 1474557 4202435 := bstep (se 1 (by rfl) ⟨3151826, by rfl⟩ : syracuseStep 4202435 = 6303653) B6303653
theorem B2244547 : Blo 1474557 2244547 := bstep (se 1 (by rfl) ⟨1683410, by rfl⟩ : syracuseStep 2244547 = 3366821) B3366821
theorem B4980689 : Blo 1474557 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B2211851 : Blo 1474557 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B1474571 : Blo 1474557 1474571 := bstep (se 1 (by rfl) ⟨1105928, by rfl⟩ : syracuseStep 1474571 = 2211857) B2211857
theorem B11206673 : Blo 1474557 11206673 := bstep (se 2 (by rfl) ⟨4202502, by rfl⟩ : syracuseStep 11206673 = 8405005) B8405005
theorem B2211863 : Blo 1474557 2211863 := bstep (se 1 (by rfl) ⟨1658897, by rfl⟩ : syracuseStep 2211863 = 3317795) B3317795
theorem B1474583 : Blo 1474557 1474583 := bstep (se 1 (by rfl) ⟨1105937, by rfl⟩ : syracuseStep 1474583 = 2211875) B2211875
theorem B1867799 : Blo 1474557 1867799 := bstep (se 1 (by rfl) ⟨1400849, by rfl⟩ : syracuseStep 1867799 = 2801699) B2801699
theorem B1474603 : Blo 1474557 1474603 := bstep (se 1 (by rfl) ⟨1105952, by rfl⟩ : syracuseStep 1474603 = 2211905) B2211905
theorem B1474615 : Blo 1474557 1474615 := bstep (se 1 (by rfl) ⟨1105961, by rfl⟩ : syracuseStep 1474615 = 2211923) B2211923
theorem B2801729 : Blo 1474557 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B37830725 : Blo 1474557 37830725 := bstep (se 4 (by rfl) ⟨3546630, by rfl⟩ : syracuseStep 37830725 = 7093261) B7093261
theorem B1474635 : Blo 1474557 1474635 := bstep (se 1 (by rfl) ⟨1105976, by rfl⟩ : syracuseStep 1474635 = 2211953) B2211953
theorem B1474647 : Blo 1474557 1474647 := bstep (se 1 (by rfl) ⟨1105985, by rfl⟩ : syracuseStep 1474647 = 2211971) B2211971
theorem B3317849 : Blo 1474557 3317849 := bstep (se 2 (by rfl) ⟨1244193, by rfl⟩ : syracuseStep 3317849 = 2488387) B2488387
theorem B2211929 : Blo 1474557 2211929 := bstep (se 2 (by rfl) ⟨829473, by rfl⟩ : syracuseStep 2211929 = 1658947) B1658947
theorem B1474667 : Blo 1474557 1474667 := bstep (se 1 (by rfl) ⟨1106000, by rfl⟩ : syracuseStep 1474667 = 2212001) B2212001
theorem B1474679 : Blo 1474557 1474679 := bstep (se 1 (by rfl) ⟨1106009, by rfl⟩ : syracuseStep 1474679 = 2212019) B2212019
theorem B1474699 : Blo 1474557 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B1474711 : Blo 1474557 1474711 := bstep (se 1 (by rfl) ⟨1106033, by rfl⟩ : syracuseStep 1474711 = 2212067) B2212067
theorem B1474731 : Blo 1474557 1474731 := bstep (se 1 (by rfl) ⟨1106048, by rfl⟩ : syracuseStep 1474731 = 2212097) B2212097
theorem B3317939 : Blo 1474557 3317939 := bstep (se 1 (by rfl) ⟨2488454, by rfl⟩ : syracuseStep 3317939 = 4976909) B4976909
theorem B4202675 : Blo 1474557 4202675 := bstep (se 1 (by rfl) ⟨3152006, by rfl⟩ : syracuseStep 4202675 = 6304013) B6304013
theorem B1474743 : Blo 1474557 1474743 := bstep (se 1 (by rfl) ⟨1106057, by rfl⟩ : syracuseStep 1474743 = 2212115) B2212115
theorem B2212043 : Blo 1474557 2212043 := bstep (se 1 (by rfl) ⟨1659032, by rfl⟩ : syracuseStep 2212043 = 3318065) B3318065
theorem B1474763 : Blo 1474557 1474763 := bstep (se 1 (by rfl) ⟨1106072, by rfl⟩ : syracuseStep 1474763 = 2212145) B2212145
theorem B22724813 : Blo 1474557 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B3317975 : Blo 1474557 3317975 := bstep (se 1 (by rfl) ⟨2488481, by rfl⟩ : syracuseStep 3317975 = 4976963) B4976963
theorem B2212055 : Blo 1474557 2212055 := bstep (se 1 (by rfl) ⟨1659041, by rfl⟩ : syracuseStep 2212055 = 3318083) B3318083
theorem B1474775 : Blo 1474557 1474775 := bstep (se 1 (by rfl) ⟨1106081, by rfl⟩ : syracuseStep 1474775 = 2212163) B2212163
theorem B2801881 : Blo 1474557 2801881 := bstep (se 2 (by rfl) ⟨1050705, by rfl⟩ : syracuseStep 2801881 = 2101411) B2101411
theorem B1474795 : Blo 1474557 1474795 := bstep (se 1 (by rfl) ⟨1106096, by rfl⟩ : syracuseStep 1474795 = 2212193) B2212193
theorem B1474807 : Blo 1474557 1474807 := bstep (se 1 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 1474807 = 2212211) B2212211
theorem B1474827 : Blo 1474557 1474827 := bstep (se 1 (by rfl) ⟨1106120, by rfl⟩ : syracuseStep 1474827 = 2212241) B2212241
theorem B2490635 : Blo 1474557 2490635 := bstep (se 1 (by rfl) ⟨1867976, by rfl⟩ : syracuseStep 2490635 = 3735953) B3735953
theorem B1474839 : Blo 1474557 1474839 := bstep (se 1 (by rfl) ⟨1106129, by rfl⟩ : syracuseStep 1474839 = 2212259) B2212259
theorem B6299927 : Blo 1474557 6299927 := bstep (se 1 (by rfl) ⟨4724945, by rfl⟩ : syracuseStep 6299927 = 9449891) B9449891
theorem B2212121 : Blo 1474557 2212121 := bstep (se 2 (by rfl) ⟨829545, by rfl⟩ : syracuseStep 2212121 = 1659091) B1659091
theorem B1474859 : Blo 1474557 1474859 := bstep (se 1 (by rfl) ⟨1106144, by rfl⟩ : syracuseStep 1474859 = 2212289) B2212289
theorem B1474871 : Blo 1474557 1474871 := bstep (se 1 (by rfl) ⟨1106153, by rfl⟩ : syracuseStep 1474871 = 2212307) B2212307
theorem B1474891 : Blo 1474557 1474891 := bstep (se 1 (by rfl) ⟨1106168, by rfl⟩ : syracuseStep 1474891 = 2212337) B2212337
theorem B4981067 : Blo 1474557 4981067 := bstep (se 1 (by rfl) ⟨3735800, by rfl⟩ : syracuseStep 4981067 = 7471601) B7471601
theorem B11968843 : Blo 1474557 11968843 := bstep (se 1 (by rfl) ⟨8976632, by rfl⟩ : syracuseStep 11968843 = 17953265) B17953265
theorem B1474903 : Blo 1474557 1474903 := bstep (se 1 (by rfl) ⟨1106177, by rfl⟩ : syracuseStep 1474903 = 2212355) B2212355
theorem B1474923 : Blo 1474557 1474923 := bstep (se 1 (by rfl) ⟨1106192, by rfl⟩ : syracuseStep 1474923 = 2212385) B2212385
theorem B1474935 : Blo 1474557 1474935 := bstep (se 1 (by rfl) ⟨1106201, by rfl⟩ : syracuseStep 1474935 = 2212403) B2212403
theorem B3318155 : Blo 1474557 3318155 := bstep (se 1 (by rfl) ⟨2488616, by rfl⟩ : syracuseStep 3318155 = 4977233) B4977233
theorem B2212235 : Blo 1474557 2212235 := bstep (se 1 (by rfl) ⟨1659176, by rfl⟩ : syracuseStep 2212235 = 3318353) B3318353
theorem B1474955 : Blo 1474557 1474955 := bstep (se 1 (by rfl) ⟨1106216, by rfl⟩ : syracuseStep 1474955 = 2212433) B2212433
theorem B2490763 : Blo 1474557 2490763 := bstep (se 1 (by rfl) ⟨1868072, by rfl⟩ : syracuseStep 2490763 = 3736145) B3736145
theorem B6390161 : Blo 1474557 6390161 := bstep (se 2 (by rfl) ⟨2396310, by rfl⟩ : syracuseStep 6390161 = 4792621) B4792621
theorem B6734225 : Blo 1474557 6734225 := bstep (se 2 (by rfl) ⟨2525334, by rfl⟩ : syracuseStep 6734225 = 5050669) B5050669
theorem B2212247 : Blo 1474557 2212247 := bstep (se 1 (by rfl) ⟨1659185, by rfl⟩ : syracuseStep 2212247 = 3318371) B3318371
theorem B1474967 : Blo 1474557 1474967 := bstep (se 1 (by rfl) ⟨1106225, by rfl⟩ : syracuseStep 1474967 = 2212451) B2212451
theorem B1474987 : Blo 1474557 1474987 := bstep (se 1 (by rfl) ⟨1106240, by rfl⟩ : syracuseStep 1474987 = 2212481) B2212481
theorem B11198897 : Blo 1474557 11198897 := bstep (se 2 (by rfl) ⟨4199586, by rfl⟩ : syracuseStep 11198897 = 8399173) B8399173
theorem B21266867 : Blo 1474557 21266867 := bstep (se 1 (by rfl) ⟨15950150, by rfl⟩ : syracuseStep 21266867 = 31900301) B31900301
theorem B1474999 : Blo 1474557 1474999 := bstep (se 1 (by rfl) ⟨1106249, by rfl⟩ : syracuseStep 1474999 = 2212499) B2212499
theorem B3318209 : Blo 1474557 3318209 := bstep (se 2 (by rfl) ⟨1244328, by rfl⟩ : syracuseStep 3318209 = 2488657) B2488657
theorem B1475019 : Blo 1474557 1475019 := bstep (se 1 (by rfl) ⟨1106264, by rfl⟩ : syracuseStep 1475019 = 2212529) B2212529
theorem B1475031 : Blo 1474557 1475031 := bstep (se 1 (by rfl) ⟨1106273, by rfl⟩ : syracuseStep 1475031 = 2212547) B2212547
theorem B2212313 : Blo 1474557 2212313 := bstep (se 2 (by rfl) ⟨829617, by rfl⟩ : syracuseStep 2212313 = 1659235) B1659235
theorem B1475051 : Blo 1474557 1475051 := bstep (se 1 (by rfl) ⟨1106288, by rfl⟩ : syracuseStep 1475051 = 2212577) B2212577
theorem B1475063 : Blo 1474557 1475063 := bstep (se 1 (by rfl) ⟨1106297, by rfl⟩ : syracuseStep 1475063 = 2212595) B2212595
theorem B1475083 : Blo 1474557 1475083 := bstep (se 1 (by rfl) ⟨1106312, by rfl⟩ : syracuseStep 1475083 = 2212625) B2212625
theorem B1475095 : Blo 1474557 1475095 := bstep (se 1 (by rfl) ⟨1106321, by rfl⟩ : syracuseStep 1475095 = 2212643) B2212643
theorem B2490905 : Blo 1474557 2490905 := bstep (se 2 (by rfl) ⟨934089, by rfl⟩ : syracuseStep 2490905 = 1868179) B1868179
theorem B1475115 : Blo 1474557 1475115 := bstep (se 1 (by rfl) ⟨1106336, by rfl⟩ : syracuseStep 1475115 = 2212673) B2212673
theorem B3736115 : Blo 1474557 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B1475127 : Blo 1474557 1475127 := bstep (se 1 (by rfl) ⟨1106345, by rfl⟩ : syracuseStep 1475127 = 2212691) B2212691
theorem B2212427 : Blo 1474557 2212427 := bstep (se 1 (by rfl) ⟨1659320, by rfl⟩ : syracuseStep 2212427 = 3318641) B3318641
theorem B1475147 : Blo 1474557 1475147 := bstep (se 1 (by rfl) ⟨1106360, by rfl⟩ : syracuseStep 1475147 = 2212721) B2212721
theorem B2212439 : Blo 1474557 2212439 := bstep (se 1 (by rfl) ⟨1659329, by rfl⟩ : syracuseStep 2212439 = 3318659) B3318659
theorem B1475159 : Blo 1474557 1475159 := bstep (se 1 (by rfl) ⟨1106369, by rfl⟩ : syracuseStep 1475159 = 2212739) B2212739
theorem B4981337 : Blo 1474557 4981337 := bstep (se 2 (by rfl) ⟨1868001, by rfl⟩ : syracuseStep 4981337 = 3736003) B3736003
theorem B1475179 : Blo 1474557 1475179 := bstep (se 1 (by rfl) ⟨1106384, by rfl⟩ : syracuseStep 1475179 = 2212769) B2212769
theorem B1475191 : Blo 1474557 1475191 := bstep (se 1 (by rfl) ⟨1106393, by rfl⟩ : syracuseStep 1475191 = 2212787) B2212787
theorem B1475211 : Blo 1474557 1475211 := bstep (se 1 (by rfl) ⟨1106408, by rfl⟩ : syracuseStep 1475211 = 2212817) B2212817
theorem B1475223 : Blo 1474557 1475223 := bstep (se 1 (by rfl) ⟨1106417, by rfl⟩ : syracuseStep 1475223 = 2212835) B2212835
theorem B3318425 : Blo 1474557 3318425 := bstep (se 2 (by rfl) ⟨1244409, by rfl⟩ : syracuseStep 3318425 = 2488819) B2488819
theorem B2212505 : Blo 1474557 2212505 := bstep (se 2 (by rfl) ⟨829689, by rfl⟩ : syracuseStep 2212505 = 1659379) B1659379
theorem B2491033 : Blo 1474557 2491033 := bstep (se 2 (by rfl) ⟨934137, by rfl⟩ : syracuseStep 2491033 = 1868275) B1868275
theorem B1475243 : Blo 1474557 1475243 := bstep (se 1 (by rfl) ⟨1106432, by rfl⟩ : syracuseStep 1475243 = 2212865) B2212865
theorem B1475255 : Blo 1474557 1475255 := bstep (se 1 (by rfl) ⟨1106441, by rfl⟩ : syracuseStep 1475255 = 2212883) B2212883
theorem B6726347 : Blo 1474557 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B1475275 : Blo 1474557 1475275 := bstep (se 1 (by rfl) ⟨1106456, by rfl⟩ : syracuseStep 1475275 = 2212913) B2212913
theorem B1475287 : Blo 1474557 1475287 := bstep (se 1 (by rfl) ⟨1106465, by rfl⟩ : syracuseStep 1475287 = 2212931) B2212931
theorem B1868503 : Blo 1474557 1868503 := bstep (se 1 (by rfl) ⟨1401377, by rfl⟩ : syracuseStep 1868503 = 2802755) B2802755
theorem B1475307 : Blo 1474557 1475307 := bstep (se 1 (by rfl) ⟨1106480, by rfl⟩ : syracuseStep 1475307 = 2212961) B2212961
theorem B218170097 : Blo 1474557 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B3318515 : Blo 1474557 3318515 := bstep (se 1 (by rfl) ⟨2488886, by rfl⟩ : syracuseStep 3318515 = 4977773) B4977773
theorem B1475319 : Blo 1474557 1475319 := bstep (se 1 (by rfl) ⟨1106489, by rfl⟩ : syracuseStep 1475319 = 2212979) B2212979
theorem B2212619 : Blo 1474557 2212619 := bstep (se 1 (by rfl) ⟨1659464, by rfl⟩ : syracuseStep 2212619 = 3318929) B3318929
theorem B1475339 : Blo 1474557 1475339 := bstep (se 1 (by rfl) ⟨1106504, by rfl⟩ : syracuseStep 1475339 = 2213009) B2213009
theorem B3318551 : Blo 1474557 3318551 := bstep (se 1 (by rfl) ⟨2488913, by rfl⟩ : syracuseStep 3318551 = 4977827) B4977827
theorem B2212631 : Blo 1474557 2212631 := bstep (se 1 (by rfl) ⟨1659473, by rfl⟩ : syracuseStep 2212631 = 3318947) B3318947
theorem B1475351 : Blo 1474557 1475351 := bstep (se 1 (by rfl) ⟨1106513, by rfl⟩ : syracuseStep 1475351 = 2213027) B2213027
theorem B1475371 : Blo 1474557 1475371 := bstep (se 1 (by rfl) ⟨1106528, by rfl⟩ : syracuseStep 1475371 = 2213057) B2213057
theorem B1475383 : Blo 1474557 1475383 := bstep (se 1 (by rfl) ⟨1106537, by rfl⟩ : syracuseStep 1475383 = 2213075) B2213075
theorem B1475403 : Blo 1474557 1475403 := bstep (se 1 (by rfl) ⟨1106552, by rfl⟩ : syracuseStep 1475403 = 2213105) B2213105
theorem B1475415 : Blo 1474557 1475415 := bstep (se 1 (by rfl) ⟨1106561, by rfl⟩ : syracuseStep 1475415 = 2213123) B2213123
theorem B2212697 : Blo 1474557 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1475435 : Blo 1474557 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B1475447 : Blo 1474557 1475447 := bstep (se 1 (by rfl) ⟨1106585, by rfl⟩ : syracuseStep 1475447 = 2213171) B2213171
theorem B1475467 : Blo 1474557 1475467 := bstep (se 1 (by rfl) ⟨1106600, by rfl⟩ : syracuseStep 1475467 = 2213201) B2213201
theorem B11199383 : Blo 1474557 11199383 := bstep (se 1 (by rfl) ⟨8399537, by rfl⟩ : syracuseStep 11199383 = 16799075) B16799075
theorem B1475479 : Blo 1474557 1475479 := bstep (se 1 (by rfl) ⟨1106609, by rfl⟩ : syracuseStep 1475479 = 2213219) B2213219
theorem B1475499 : Blo 1474557 1475499 := bstep (se 1 (by rfl) ⟨1106624, by rfl⟩ : syracuseStep 1475499 = 2213249) B2213249
theorem B1475511 : Blo 1474557 1475511 := bstep (se 1 (by rfl) ⟨1106633, by rfl⟩ : syracuseStep 1475511 = 2213267) B2213267
theorem B3318731 : Blo 1474557 3318731 := bstep (se 1 (by rfl) ⟨2489048, by rfl⟩ : syracuseStep 3318731 = 4978097) B4978097
theorem B2212811 : Blo 1474557 2212811 := bstep (se 1 (by rfl) ⟨1659608, by rfl⟩ : syracuseStep 2212811 = 3319217) B3319217
theorem B1475531 : Blo 1474557 1475531 := bstep (se 1 (by rfl) ⟨1106648, by rfl⟩ : syracuseStep 1475531 = 2213297) B2213297
theorem B6390731 : Blo 1474557 6390731 := bstep (se 1 (by rfl) ⟨4793048, by rfl⟩ : syracuseStep 6390731 = 9586097) B9586097
theorem B2212823 : Blo 1474557 2212823 := bstep (se 1 (by rfl) ⟨1659617, by rfl⟩ : syracuseStep 2212823 = 3319235) B3319235
theorem B1475543 : Blo 1474557 1475543 := bstep (se 1 (by rfl) ⟨1106657, by rfl⟩ : syracuseStep 1475543 = 2213315) B2213315
theorem B1475563 : Blo 1474557 1475563 := bstep (se 1 (by rfl) ⟨1106672, by rfl⟩ : syracuseStep 1475563 = 2213345) B2213345
theorem B1475575 : Blo 1474557 1475575 := bstep (se 1 (by rfl) ⟨1106681, by rfl⟩ : syracuseStep 1475575 = 2213363) B2213363
theorem B3318785 : Blo 1474557 3318785 := bstep (se 2 (by rfl) ⟨1244544, by rfl⟩ : syracuseStep 3318785 = 2489089) B2489089
theorem B1475595 : Blo 1474557 1475595 := bstep (se 1 (by rfl) ⟨1106696, by rfl⟩ : syracuseStep 1475595 = 2213393) B2213393
theorem B1475607 : Blo 1474557 1475607 := bstep (se 1 (by rfl) ⟨1106705, by rfl⟩ : syracuseStep 1475607 = 2213411) B2213411
theorem B2212889 : Blo 1474557 2212889 := bstep (se 2 (by rfl) ⟨829833, by rfl⟩ : syracuseStep 2212889 = 1659667) B1659667
theorem B1475627 : Blo 1474557 1475627 := bstep (se 1 (by rfl) ⟨1106720, by rfl⟩ : syracuseStep 1475627 = 2213441) B2213441
theorem B1475639 : Blo 1474557 1475639 := bstep (se 1 (by rfl) ⟨1106729, by rfl⟩ : syracuseStep 1475639 = 2213459) B2213459
theorem B1475659 : Blo 1474557 1475659 := bstep (se 1 (by rfl) ⟨1106744, by rfl⟩ : syracuseStep 1475659 = 2213489) B2213489
theorem B3736651 : Blo 1474557 3736651 := bstep (se 1 (by rfl) ⟨2802488, by rfl⟩ : syracuseStep 3736651 = 5604977) B5604977
theorem B1475671 : Blo 1474557 1475671 := bstep (se 1 (by rfl) ⟨1106753, by rfl⟩ : syracuseStep 1475671 = 2213507) B2213507
theorem B1475691 : Blo 1474557 1475691 := bstep (se 1 (by rfl) ⟨1106768, by rfl⟩ : syracuseStep 1475691 = 2213537) B2213537
theorem B1475703 : Blo 1474557 1475703 := bstep (se 1 (by rfl) ⟨1106777, by rfl⟩ : syracuseStep 1475703 = 2213555) B2213555
theorem B2213003 : Blo 1474557 2213003 := bstep (se 1 (by rfl) ⟨1659752, by rfl⟩ : syracuseStep 2213003 = 3319505) B3319505
theorem B1475723 : Blo 1474557 1475723 := bstep (se 1 (by rfl) ⟨1106792, by rfl⟩ : syracuseStep 1475723 = 2213585) B2213585
theorem B2213015 : Blo 1474557 2213015 := bstep (se 1 (by rfl) ⟨1659761, by rfl⟩ : syracuseStep 2213015 = 3319523) B3319523
theorem B1475735 : Blo 1474557 1475735 := bstep (se 1 (by rfl) ⟨1106801, by rfl⟩ : syracuseStep 1475735 = 2213603) B2213603
theorem B1475755 : Blo 1474557 1475755 := bstep (se 1 (by rfl) ⟨1106816, by rfl⟩ : syracuseStep 1475755 = 2213633) B2213633
theorem B26920117 : Blo 1474557 26920117 := bstep (se 5 (by rfl) ⟨1261880, by rfl⟩ : syracuseStep 26920117 = 2523761) B2523761
theorem B1475767 : Blo 1474557 1475767 := bstep (se 1 (by rfl) ⟨1106825, by rfl⟩ : syracuseStep 1475767 = 2213651) B2213651
theorem B1475787 : Blo 1474557 1475787 := bstep (se 1 (by rfl) ⟨1106840, by rfl⟩ : syracuseStep 1475787 = 2213681) B2213681
theorem B1475799 : Blo 1474557 1475799 := bstep (se 1 (by rfl) ⟨1106849, by rfl⟩ : syracuseStep 1475799 = 2213699) B2213699
theorem B2491607 : Blo 1474557 2491607 := bstep (se 1 (by rfl) ⟨1868705, by rfl⟩ : syracuseStep 2491607 = 3737411) B3737411
theorem B3319001 : Blo 1474557 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B2213081 : Blo 1474557 2213081 := bstep (se 2 (by rfl) ⟨829905, by rfl⟩ : syracuseStep 2213081 = 1659811) B1659811
theorem B3736793 : Blo 1474557 3736793 := bstep (se 2 (by rfl) ⟨1401297, by rfl⟩ : syracuseStep 3736793 = 2802595) B2802595
theorem B1475819 : Blo 1474557 1475819 := bstep (se 1 (by rfl) ⟨1106864, by rfl⟩ : syracuseStep 1475819 = 2213729) B2213729
theorem B1475831 : Blo 1474557 1475831 := bstep (se 1 (by rfl) ⟨1106873, by rfl⟩ : syracuseStep 1475831 = 2213747) B2213747
theorem B1475851 : Blo 1474557 1475851 := bstep (se 1 (by rfl) ⟨1106888, by rfl⟩ : syracuseStep 1475851 = 2213777) B2213777
theorem B1475863 : Blo 1474557 1475863 := bstep (se 1 (by rfl) ⟨1106897, by rfl⟩ : syracuseStep 1475863 = 2213795) B2213795
theorem B4982039 : Blo 1474557 4982039 := bstep (se 1 (by rfl) ⟨3736529, by rfl⟩ : syracuseStep 4982039 = 7473059) B7473059
theorem B1475883 : Blo 1474557 1475883 := bstep (se 1 (by rfl) ⟨1106912, by rfl⟩ : syracuseStep 1475883 = 2213825) B2213825
theorem B3319091 : Blo 1474557 3319091 := bstep (se 1 (by rfl) ⟨2489318, by rfl⟩ : syracuseStep 3319091 = 4978637) B4978637
theorem B5604659 : Blo 1474557 5604659 := bstep (se 1 (by rfl) ⟨4203494, by rfl⟩ : syracuseStep 5604659 = 8406989) B8406989
theorem B1475895 : Blo 1474557 1475895 := bstep (se 1 (by rfl) ⟨1106921, by rfl⟩ : syracuseStep 1475895 = 2213843) B2213843
theorem B10634561 : Blo 1474557 10634561 := bstep (se 2 (by rfl) ⟨3987960, by rfl⟩ : syracuseStep 10634561 = 7975921) B7975921
theorem B5604673 : Blo 1474557 5604673 := bstep (se 2 (by rfl) ⟨2101752, by rfl⟩ : syracuseStep 5604673 = 4203505) B4203505
theorem B2213195 : Blo 1474557 2213195 := bstep (se 1 (by rfl) ⟨1659896, by rfl⟩ : syracuseStep 2213195 = 3319793) B3319793
theorem B1475915 : Blo 1474557 1475915 := bstep (se 1 (by rfl) ⟨1106936, by rfl⟩ : syracuseStep 1475915 = 2213873) B2213873
theorem B3319127 : Blo 1474557 3319127 := bstep (se 1 (by rfl) ⟨2489345, by rfl⟩ : syracuseStep 3319127 = 4978691) B4978691
theorem B2213207 : Blo 1474557 2213207 := bstep (se 1 (by rfl) ⟨1659905, by rfl⟩ : syracuseStep 2213207 = 3319811) B3319811
theorem B1475927 : Blo 1474557 1475927 := bstep (se 1 (by rfl) ⟨1106945, by rfl⟩ : syracuseStep 1475927 = 2213891) B2213891
theorem B1475947 : Blo 1474557 1475947 := bstep (se 1 (by rfl) ⟨1106960, by rfl⟩ : syracuseStep 1475947 = 2213921) B2213921
theorem B1475959 : Blo 1474557 1475959 := bstep (se 1 (by rfl) ⟨1106969, by rfl⟩ : syracuseStep 1475959 = 2213939) B2213939
theorem B1475979 : Blo 1474557 1475979 := bstep (se 1 (by rfl) ⟨1106984, by rfl⟩ : syracuseStep 1475979 = 2213969) B2213969
theorem B1475991 : Blo 1474557 1475991 := bstep (se 1 (by rfl) ⟨1106993, by rfl⟩ : syracuseStep 1475991 = 2213987) B2213987
theorem B2213273 : Blo 1474557 2213273 := bstep (se 2 (by rfl) ⟨829977, by rfl⟩ : syracuseStep 2213273 = 1659955) B1659955
theorem B1476011 : Blo 1474557 1476011 := bstep (se 1 (by rfl) ⟨1107008, by rfl⟩ : syracuseStep 1476011 = 2214017) B2214017
theorem B12608945 : Blo 1474557 12608945 := bstep (se 2 (by rfl) ⟨4728354, by rfl⟩ : syracuseStep 12608945 = 9456709) B9456709
theorem B1476023 : Blo 1474557 1476023 := bstep (se 1 (by rfl) ⟨1107017, by rfl⟩ : syracuseStep 1476023 = 2214035) B2214035
theorem B1476043 : Blo 1474557 1476043 := bstep (se 1 (by rfl) ⟨1107032, by rfl⟩ : syracuseStep 1476043 = 2214065) B2214065
theorem B1476055 : Blo 1474557 1476055 := bstep (se 1 (by rfl) ⟨1107041, by rfl⟩ : syracuseStep 1476055 = 2214083) B2214083
theorem B1476075 : Blo 1474557 1476075 := bstep (se 1 (by rfl) ⟨1107056, by rfl⟩ : syracuseStep 1476075 = 2214113) B2214113
theorem B1476087 : Blo 1474557 1476087 := bstep (se 1 (by rfl) ⟨1107065, by rfl⟩ : syracuseStep 1476087 = 2214131) B2214131
theorem B3319307 : Blo 1474557 3319307 := bstep (se 1 (by rfl) ⟨2489480, by rfl⟩ : syracuseStep 3319307 = 4978961) B4978961
theorem B2213387 : Blo 1474557 2213387 := bstep (se 1 (by rfl) ⟨1660040, by rfl⟩ : syracuseStep 2213387 = 3320081) B3320081
theorem B1476107 : Blo 1474557 1476107 := bstep (se 1 (by rfl) ⟨1107080, by rfl⟩ : syracuseStep 1476107 = 2214161) B2214161
theorem B2213399 : Blo 1474557 2213399 := bstep (se 1 (by rfl) ⟨1660049, by rfl⟩ : syracuseStep 2213399 = 3320099) B3320099
theorem B1476119 : Blo 1474557 1476119 := bstep (se 1 (by rfl) ⟨1107089, by rfl⟩ : syracuseStep 1476119 = 2214179) B2214179
theorem B1476139 : Blo 1474557 1476139 := bstep (se 1 (by rfl) ⟨1107104, by rfl⟩ : syracuseStep 1476139 = 2214209) B2214209
theorem B1476151 : Blo 1474557 1476151 := bstep (se 1 (by rfl) ⟨1107113, by rfl⟩ : syracuseStep 1476151 = 2214227) B2214227
theorem B3319361 : Blo 1474557 3319361 := bstep (se 2 (by rfl) ⟨1244760, by rfl⟩ : syracuseStep 3319361 = 2489521) B2489521
theorem B1476171 : Blo 1474557 1476171 := bstep (se 1 (by rfl) ⟨1107128, by rfl⟩ : syracuseStep 1476171 = 2214257) B2214257
theorem B1476183 : Blo 1474557 1476183 := bstep (se 1 (by rfl) ⟨1107137, by rfl⟩ : syracuseStep 1476183 = 2214275) B2214275
theorem B2213465 : Blo 1474557 2213465 := bstep (se 2 (by rfl) ⟨830049, by rfl⟩ : syracuseStep 2213465 = 1660099) B1660099
theorem B1476203 : Blo 1474557 1476203 := bstep (se 1 (by rfl) ⟨1107152, by rfl⟩ : syracuseStep 1476203 = 2214305) B2214305
theorem B1476215 : Blo 1474557 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B1476235 : Blo 1474557 1476235 := bstep (se 1 (by rfl) ⟨1107176, by rfl⟩ : syracuseStep 1476235 = 2214353) B2214353
theorem B1476247 : Blo 1474557 1476247 := bstep (se 1 (by rfl) ⟨1107185, by rfl⟩ : syracuseStep 1476247 = 2214371) B2214371
theorem B1476267 : Blo 1474557 1476267 := bstep (se 1 (by rfl) ⟨1107200, by rfl⟩ : syracuseStep 1476267 = 2214401) B2214401
theorem B1476279 : Blo 1474557 1476279 := bstep (se 1 (by rfl) ⟨1107209, by rfl⟩ : syracuseStep 1476279 = 2214419) B2214419
theorem B2213579 : Blo 1474557 2213579 := bstep (se 1 (by rfl) ⟨1660184, by rfl⟩ : syracuseStep 2213579 = 3320369) B3320369
theorem B1476299 : Blo 1474557 1476299 := bstep (se 1 (by rfl) ⟨1107224, by rfl⟩ : syracuseStep 1476299 = 2214449) B2214449
theorem B2213591 : Blo 1474557 2213591 := bstep (se 1 (by rfl) ⟨1660193, by rfl⟩ : syracuseStep 2213591 = 3320387) B3320387
theorem B1476311 : Blo 1474557 1476311 := bstep (se 1 (by rfl) ⟨1107233, by rfl⟩ : syracuseStep 1476311 = 2214467) B2214467
theorem B1476331 : Blo 1474557 1476331 := bstep (se 1 (by rfl) ⟨1107248, by rfl⟩ : syracuseStep 1476331 = 2214497) B2214497
theorem B1476343 : Blo 1474557 1476343 := bstep (se 1 (by rfl) ⟨1107257, by rfl⟩ : syracuseStep 1476343 = 2214515) B2214515
theorem B1476363 : Blo 1474557 1476363 := bstep (se 1 (by rfl) ⟨1107272, by rfl⟩ : syracuseStep 1476363 = 2214545) B2214545
theorem B1476375 : Blo 1474557 1476375 := bstep (se 1 (by rfl) ⟨1107281, by rfl⟩ : syracuseStep 1476375 = 2214563) B2214563
theorem B3319577 : Blo 1474557 3319577 := bstep (se 2 (by rfl) ⟨1244841, by rfl⟩ : syracuseStep 3319577 = 2489683) B2489683
theorem B2213657 : Blo 1474557 2213657 := bstep (se 2 (by rfl) ⟨830121, by rfl⟩ : syracuseStep 2213657 = 1660243) B1660243
theorem B1476395 : Blo 1474557 1476395 := bstep (se 1 (by rfl) ⟨1107296, by rfl⟩ : syracuseStep 1476395 = 2214593) B2214593
theorem B4982579 : Blo 1474557 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B1476407 : Blo 1474557 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1476427 : Blo 1474557 1476427 := bstep (se 1 (by rfl) ⟨1107320, by rfl⟩ : syracuseStep 1476427 = 2214641) B2214641
theorem B1476439 : Blo 1474557 1476439 := bstep (se 1 (by rfl) ⟨1107329, by rfl⟩ : syracuseStep 1476439 = 2214659) B2214659
theorem B5048153 : Blo 1474557 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B1476459 : Blo 1474557 1476459 := bstep (se 1 (by rfl) ⟨1107344, by rfl⟩ : syracuseStep 1476459 = 2214689) B2214689
theorem B3319667 : Blo 1474557 3319667 := bstep (se 1 (by rfl) ⟨2489750, by rfl⟩ : syracuseStep 3319667 = 4979501) B4979501
theorem B1476471 : Blo 1474557 1476471 := bstep (se 1 (by rfl) ⟨1107353, by rfl⟩ : syracuseStep 1476471 = 2214707) B2214707
theorem B2213771 : Blo 1474557 2213771 := bstep (se 1 (by rfl) ⟨1660328, by rfl⟩ : syracuseStep 2213771 = 3320657) B3320657
theorem B1476491 : Blo 1474557 1476491 := bstep (se 1 (by rfl) ⟨1107368, by rfl⟩ : syracuseStep 1476491 = 2214737) B2214737
theorem B1574807 : Blo 1474557 1574807 := bstep (se 1 (by rfl) ⟨1181105, by rfl⟩ : syracuseStep 1574807 = 2362211) B2362211
theorem B3319703 : Blo 1474557 3319703 := bstep (se 1 (by rfl) ⟨2489777, by rfl⟩ : syracuseStep 3319703 = 4979555) B4979555
theorem B2213783 : Blo 1474557 2213783 := bstep (se 1 (by rfl) ⟨1660337, by rfl⟩ : syracuseStep 2213783 = 3320675) B3320675
theorem B1476503 : Blo 1474557 1476503 := bstep (se 1 (by rfl) ⟨1107377, by rfl⟩ : syracuseStep 1476503 = 2214755) B2214755
theorem B1476523 : Blo 1474557 1476523 := bstep (se 1 (by rfl) ⟨1107392, by rfl⟩ : syracuseStep 1476523 = 2214785) B2214785
theorem B1476535 : Blo 1474557 1476535 := bstep (se 1 (by rfl) ⟨1107401, by rfl⟩ : syracuseStep 1476535 = 2214803) B2214803
theorem B1476555 : Blo 1474557 1476555 := bstep (se 1 (by rfl) ⟨1107416, by rfl⟩ : syracuseStep 1476555 = 2214833) B2214833
theorem B2213849 : Blo 1474557 2213849 := bstep (se 2 (by rfl) ⟨830193, by rfl⟩ : syracuseStep 2213849 = 1660387) B1660387
theorem B4982849 : Blo 1474557 4982849 := bstep (se 2 (by rfl) ⟨1868568, by rfl⟩ : syracuseStep 4982849 = 3737137) B3737137
theorem B3319883 : Blo 1474557 3319883 := bstep (se 1 (by rfl) ⟨2489912, by rfl⟩ : syracuseStep 3319883 = 4979825) B4979825
theorem B2213963 : Blo 1474557 2213963 := bstep (se 1 (by rfl) ⟨1660472, by rfl⟩ : syracuseStep 2213963 = 3320945) B3320945
theorem B2213975 : Blo 1474557 2213975 := bstep (se 1 (by rfl) ⟨1660481, by rfl⟩ : syracuseStep 2213975 = 3320963) B3320963
theorem B3319937 : Blo 1474557 3319937 := bstep (se 2 (by rfl) ⟨1244976, by rfl⟩ : syracuseStep 3319937 = 2489953) B2489953
theorem B2214041 : Blo 1474557 2214041 := bstep (se 2 (by rfl) ⟨830265, by rfl⟩ : syracuseStep 2214041 = 1660531) B1660531
theorem B2214155 : Blo 1474557 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B2214167 : Blo 1474557 2214167 := bstep (se 1 (by rfl) ⟨1660625, by rfl⟩ : syracuseStep 2214167 = 3321251) B3321251
theorem B3320153 : Blo 1474557 3320153 := bstep (se 2 (by rfl) ⟨1245057, by rfl⟩ : syracuseStep 3320153 = 2490115) B2490115
theorem B2214233 : Blo 1474557 2214233 := bstep (se 2 (by rfl) ⟨830337, by rfl⟩ : syracuseStep 2214233 = 1660675) B1660675
theorem B11970917 : Blo 1474557 11970917 := bstep (se 4 (by rfl) ⟨1122273, by rfl⟩ : syracuseStep 11970917 = 2244547) B2244547
theorem B3320243 : Blo 1474557 3320243 := bstep (se 1 (by rfl) ⟨2490182, by rfl⟩ : syracuseStep 3320243 = 4980365) B4980365
theorem B2214347 : Blo 1474557 2214347 := bstep (se 1 (by rfl) ⟨1660760, by rfl⟩ : syracuseStep 2214347 = 3321521) B3321521
theorem B3320279 : Blo 1474557 3320279 := bstep (se 1 (by rfl) ⟨2490209, by rfl⟩ : syracuseStep 3320279 = 4980419) B4980419
theorem B2214359 : Blo 1474557 2214359 := bstep (se 1 (by rfl) ⟨1660769, by rfl⟩ : syracuseStep 2214359 = 3321539) B3321539
theorem B3410455 : Blo 1474557 3410455 := bstep (se 1 (by rfl) ⟨2557841, by rfl⟩ : syracuseStep 3410455 = 5115683) B5115683
theorem B2214425 : Blo 1474557 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B3320459 : Blo 1474557 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B2214539 : Blo 1474557 2214539 := bstep (se 1 (by rfl) ⟨1660904, by rfl⟩ : syracuseStep 2214539 = 3321809) B3321809
theorem B2214551 : Blo 1474557 2214551 := bstep (se 1 (by rfl) ⟨1660913, by rfl⟩ : syracuseStep 2214551 = 3321827) B3321827
theorem B6302387 : Blo 1474557 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B3320513 : Blo 1474557 3320513 := bstep (se 2 (by rfl) ⟨1245192, by rfl⟩ : syracuseStep 3320513 = 2490385) B2490385
theorem B2214617 : Blo 1474557 2214617 := bstep (se 2 (by rfl) ⟨830481, by rfl⟩ : syracuseStep 2214617 = 1660963) B1660963
theorem B5982979 : Blo 1474557 5982979 := bstep (se 1 (by rfl) ⟨4487234, by rfl⟩ : syracuseStep 5982979 = 8974469) B8974469
theorem B28379969 : Blo 1474557 28379969 := bstep (se 2 (by rfl) ⟨10642488, by rfl⟩ : syracuseStep 28379969 = 21284977) B21284977
theorem B2214731 : Blo 1474557 2214731 := bstep (se 1 (by rfl) ⟨1661048, by rfl⟩ : syracuseStep 2214731 = 3322097) B3322097
theorem B2214743 : Blo 1474557 2214743 := bstep (se 1 (by rfl) ⟨1661057, by rfl⟩ : syracuseStep 2214743 = 3322115) B3322115
theorem B2100107 : Blo 1474557 2100107 := bstep (se 1 (by rfl) ⟨1575080, by rfl⟩ : syracuseStep 2100107 = 3150161) B3150161
theorem B3320729 : Blo 1474557 3320729 := bstep (se 2 (by rfl) ⟨1245273, by rfl⟩ : syracuseStep 3320729 = 2490547) B2490547
theorem B2214809 : Blo 1474557 2214809 := bstep (se 2 (by rfl) ⟨830553, by rfl⟩ : syracuseStep 2214809 = 1661107) B1661107
theorem B2395097 : Blo 1474557 2395097 := bstep (se 2 (by rfl) ⟨898161, by rfl⟩ : syracuseStep 2395097 = 1796323) B1796323
theorem B3320819 : Blo 1474557 3320819 := bstep (se 1 (by rfl) ⟨2490614, by rfl⟩ : syracuseStep 3320819 = 4981229) B4981229
theorem B7474193 : Blo 1474557 7474193 := bstep (se 2 (by rfl) ⟨2802822, by rfl⟩ : syracuseStep 7474193 = 5605645) B5605645
theorem B3320855 : Blo 1474557 3320855 := bstep (se 1 (by rfl) ⟨2490641, by rfl⟩ : syracuseStep 3320855 = 4981283) B4981283
theorem B8408195 : Blo 1474557 8408195 := bstep (se 1 (by rfl) ⟨6306146, by rfl⟩ : syracuseStep 8408195 = 12612293) B12612293
theorem B7474355 : Blo 1474557 7474355 := bstep (se 1 (by rfl) ⟨5605766, by rfl⟩ : syracuseStep 7474355 = 11211533) B11211533
theorem B83012789 : Blo 1474557 83012789 := bstep (se 5 (by rfl) ⟨3891224, by rfl⟩ : syracuseStep 83012789 = 7782449) B7782449
theorem B3321035 : Blo 1474557 3321035 := bstep (se 1 (by rfl) ⟨2490776, by rfl⟩ : syracuseStep 3321035 = 4981553) B4981553
theorem B3321089 : Blo 1474557 3321089 := bstep (se 2 (by rfl) ⟨1245408, by rfl⟩ : syracuseStep 3321089 = 2490817) B2490817
theorem B4730201 : Blo 1474557 4730201 := bstep (se 2 (by rfl) ⟨1773825, by rfl⟩ : syracuseStep 4730201 = 3547651) B3547651
theorem B3321305 : Blo 1474557 3321305 := bstep (se 2 (by rfl) ⟨1245489, by rfl⟩ : syracuseStep 3321305 = 2490979) B2490979
theorem B30690829 : Blo 1474557 30690829 := bstep (se 3 (by rfl) ⟨5754530, by rfl⟩ : syracuseStep 30690829 = 11509061) B11509061
theorem B3321395 : Blo 1474557 3321395 := bstep (se 1 (by rfl) ⟨2491046, by rfl⟩ : syracuseStep 3321395 = 4982093) B4982093
theorem B8400449 : Blo 1474557 8400449 := bstep (se 2 (by rfl) ⟨3150168, by rfl⟩ : syracuseStep 8400449 = 6300337) B6300337
theorem B5115467 : Blo 1474557 5115467 := bstep (se 1 (by rfl) ⟨3836600, by rfl⟩ : syracuseStep 5115467 = 7673201) B7673201
theorem B3321431 : Blo 1474557 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B5983837 : Blo 1474557 5983837 := bstep (se 3 (by rfl) ⟨1121969, by rfl⟩ : syracuseStep 5983837 = 2243939) B2243939
theorem B1576631 : Blo 1474557 1576631 := bstep (se 1 (by rfl) ⟨1182473, by rfl⟩ : syracuseStep 1576631 = 2364947) B2364947
theorem B3321611 : Blo 1474557 3321611 := bstep (se 1 (by rfl) ⟨2491208, by rfl⟩ : syracuseStep 3321611 = 4982417) B4982417
theorem B2658071 : Blo 1474557 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B5680961 : Blo 1474557 5680961 := bstep (se 2 (by rfl) ⟨2130360, by rfl⟩ : syracuseStep 5680961 = 4260721) B4260721
theorem B11210561 : Blo 1474557 11210561 := bstep (se 2 (by rfl) ⟨4203960, by rfl⟩ : syracuseStep 11210561 = 8407921) B8407921
theorem B3321665 : Blo 1474557 3321665 := bstep (se 2 (by rfl) ⟨1245624, by rfl⟩ : syracuseStep 3321665 = 2491249) B2491249
theorem B5320523 : Blo 1474557 5320523 := bstep (se 1 (by rfl) ⟨3990392, by rfl⟩ : syracuseStep 5320523 = 7980785) B7980785
theorem B2101081 : Blo 1474557 2101081 := bstep (se 2 (by rfl) ⟨787905, by rfl⟩ : syracuseStep 2101081 = 1575811) B1575811
theorem B7466903 : Blo 1474557 7466903 := bstep (se 1 (by rfl) ⟨5600177, by rfl⟩ : syracuseStep 7466903 = 11200355) B11200355
theorem B16797617 : Blo 1474557 16797617 := bstep (se 2 (by rfl) ⟨6299106, by rfl⟩ : syracuseStep 16797617 = 12598213) B12598213
theorem B4550593 : Blo 1474557 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B2363339 : Blo 1474557 2363339 := bstep (se 1 (by rfl) ⟨1772504, by rfl⟩ : syracuseStep 2363339 = 3545009) B3545009
theorem B3321881 : Blo 1474557 3321881 := bstep (se 2 (by rfl) ⟨1245705, by rfl⟩ : syracuseStep 3321881 = 2491411) B2491411
theorem B13455395 : Blo 1474557 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B3543115 : Blo 1474557 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B3321971 : Blo 1474557 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B1659019 : Blo 1474557 1659019 := bstep (se 1 (by rfl) ⟨1244264, by rfl⟩ : syracuseStep 1659019 = 2488529) B2488529
theorem B3543191 : Blo 1474557 3543191 := bstep (se 1 (by rfl) ⟨2657393, by rfl⟩ : syracuseStep 3543191 = 5314787) B5314787
theorem B3322007 : Blo 1474557 3322007 := bstep (se 1 (by rfl) ⟨2491505, by rfl⟩ : syracuseStep 3322007 = 4983011) B4983011
theorem B4042955 : Blo 1474557 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B1659127 : Blo 1474557 1659127 := bstep (se 1 (by rfl) ⟨1244345, by rfl⟩ : syracuseStep 1659127 = 2488691) B2488691
theorem B1683703 : Blo 1474557 1683703 := bstep (se 1 (by rfl) ⟨1262777, by rfl⟩ : syracuseStep 1683703 = 2525555) B2525555
theorem B5755159 : Blo 1474557 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B3363137 : Blo 1474557 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B3322187 : Blo 1474557 3322187 := bstep (se 1 (by rfl) ⟨2491640, by rfl⟩ : syracuseStep 3322187 = 4983281) B4983281
theorem B3322241 : Blo 1474557 3322241 := bstep (se 2 (by rfl) ⟨1245840, by rfl⟩ : syracuseStep 3322241 = 2491681) B2491681
theorem B1659307 : Blo 1474557 1659307 := bstep (se 1 (by rfl) ⟨1244480, by rfl⟩ : syracuseStep 1659307 = 2488961) B2488961
theorem B2363851 : Blo 1474557 2363851 := bstep (se 1 (by rfl) ⟨1772888, by rfl⟩ : syracuseStep 2363851 = 3545777) B3545777
theorem B9449945 : Blo 1474557 9449945 := bstep (se 2 (by rfl) ⟨3543729, by rfl⟩ : syracuseStep 9449945 = 7087459) B7087459
theorem B7090649 : Blo 1474557 7090649 := bstep (se 2 (by rfl) ⟨2658993, by rfl⟩ : syracuseStep 7090649 = 5317987) B5317987
theorem B3985885 : Blo 1474557 3985885 := bstep (se 3 (by rfl) ⟨747353, by rfl⟩ : syracuseStep 3985885 = 1494707) B1494707
theorem B3150323 : Blo 1474557 3150323 := bstep (se 1 (by rfl) ⟨2362742, by rfl⟩ : syracuseStep 3150323 = 4725485) B4725485
theorem B1659415 : Blo 1474557 1659415 := bstep (se 1 (by rfl) ⟨1244561, by rfl⟩ : syracuseStep 1659415 = 2489123) B2489123
theorem B6304301 : Blo 1474557 6304301 := bstep (se 3 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 6304301 = 2364113) B2364113
theorem B1659595 : Blo 1474557 1659595 := bstep (se 1 (by rfl) ⟨1244696, by rfl⟩ : syracuseStep 1659595 = 2489393) B2489393
theorem B60576497 : Blo 1474557 60576497 := bstep (se 2 (by rfl) ⟨22716186, by rfl⟩ : syracuseStep 60576497 = 45432373) B45432373
theorem B1659703 : Blo 1474557 1659703 := bstep (se 1 (by rfl) ⟨1244777, by rfl⟩ : syracuseStep 1659703 = 2489555) B2489555
theorem B5682113 : Blo 1474557 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B4977611 : Blo 1474557 4977611 := bstep (se 1 (by rfl) ⟨3733208, by rfl⟩ : syracuseStep 4977611 = 7466417) B7466417
theorem B2102231 : Blo 1474557 2102231 := bstep (se 1 (by rfl) ⟨1576673, by rfl⟩ : syracuseStep 2102231 = 3153347) B3153347
theorem B1659883 : Blo 1474557 1659883 := bstep (se 1 (by rfl) ⟨1244912, by rfl⟩ : syracuseStep 1659883 = 2489825) B2489825
theorem B2659339 : Blo 1474557 2659339 := bstep (se 1 (by rfl) ⟨1994504, by rfl⟩ : syracuseStep 2659339 = 3989009) B3989009
theorem B11351075 : Blo 1474557 11351075 := bstep (se 1 (by rfl) ⟨8513306, by rfl⟩ : syracuseStep 11351075 = 17026613) B17026613
theorem B7574573 : Blo 1474557 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B3150913 : Blo 1474557 3150913 := bstep (se 2 (by rfl) ⟨1181592, by rfl⟩ : syracuseStep 3150913 = 2363185) B2363185
theorem B1659991 : Blo 1474557 1659991 := bstep (se 1 (by rfl) ⟨1244993, by rfl⟩ : syracuseStep 1659991 = 2489987) B2489987
theorem B2364569 : Blo 1474557 2364569 := bstep (se 2 (by rfl) ⟨886713, by rfl⟩ : syracuseStep 2364569 = 1773427) B1773427
theorem B4977881 : Blo 1474557 4977881 := bstep (se 2 (by rfl) ⟨1866705, by rfl⟩ : syracuseStep 4977881 = 3733411) B3733411
theorem B6304985 : Blo 1474557 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B1660171 : Blo 1474557 1660171 := bstep (se 1 (by rfl) ⟨1245128, by rfl⟩ : syracuseStep 1660171 = 2490257) B2490257
theorem B1660279 : Blo 1474557 1660279 := bstep (se 1 (by rfl) ⟨1245209, by rfl⟩ : syracuseStep 1660279 = 2490419) B2490419
theorem B11351447 : Blo 1474557 11351447 := bstep (se 1 (by rfl) ⟨8513585, by rfl⟩ : syracuseStep 11351447 = 17027171) B17027171
theorem B5600771 : Blo 1474557 5600771 := bstep (se 1 (by rfl) ⟨4200578, by rfl⟩ : syracuseStep 5600771 = 8401157) B8401157
theorem B5600785 : Blo 1474557 5600785 := bstep (se 2 (by rfl) ⟨2100294, by rfl⟩ : syracuseStep 5600785 = 4200589) B4200589
theorem B1660459 : Blo 1474557 1660459 := bstep (se 1 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 1660459 = 2490689) B2490689
theorem B9090625 : Blo 1474557 9090625 := bstep (se 2 (by rfl) ⟨3408984, by rfl⟩ : syracuseStep 9090625 = 6817969) B6817969
theorem B3733067 : Blo 1474557 3733067 := bstep (se 1 (by rfl) ⟨2799800, by rfl⟩ : syracuseStep 3733067 = 5599601) B5599601
theorem B3987019 : Blo 1474557 3987019 := bstep (se 1 (by rfl) ⟨2990264, by rfl⟩ : syracuseStep 3987019 = 5980529) B5980529
theorem B1660567 : Blo 1474557 1660567 := bstep (se 1 (by rfl) ⟨1245425, by rfl⟩ : syracuseStep 1660567 = 2490851) B2490851
theorem B4486859 : Blo 1474557 4486859 := bstep (se 1 (by rfl) ⟨3365144, by rfl⟩ : syracuseStep 4486859 = 6730289) B6730289
theorem B11212505 : Blo 1474557 11212505 := bstep (se 2 (by rfl) ⟨4204689, by rfl⟩ : syracuseStep 11212505 = 8409379) B8409379
theorem B5601089 : Blo 1474557 5601089 := bstep (se 2 (by rfl) ⟨2100408, by rfl⟩ : syracuseStep 5601089 = 4200817) B4200817
theorem B1660747 : Blo 1474557 1660747 := bstep (se 1 (by rfl) ⟨1245560, by rfl⟩ : syracuseStep 1660747 = 2491121) B2491121
theorem B4978583 : Blo 1474557 4978583 := bstep (se 1 (by rfl) ⟨3733937, by rfl⟩ : syracuseStep 4978583 = 7467875) B7467875
theorem B35903411 : Blo 1474557 35903411 := bstep (se 1 (by rfl) ⟨26927558, by rfl⟩ : syracuseStep 35903411 = 53855117) B53855117
theorem B1660855 : Blo 1474557 1660855 := bstep (se 1 (by rfl) ⟨1245641, by rfl⟩ : syracuseStep 1660855 = 2491283) B2491283
theorem B1620043 : Blo 1474557 1620043 := bstep (se 1 (by rfl) ⟨1215032, by rfl⟩ : syracuseStep 1620043 = 2430065) B2430065
theorem B1661035 : Blo 1474557 1661035 := bstep (se 1 (by rfl) ⟨1245776, by rfl⟩ : syracuseStep 1661035 = 2491553) B2491553
theorem B2799755 : Blo 1474557 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B2799937 : Blo 1474557 2799937 := bstep (se 2 (by rfl) ⟨1049976, by rfl⟩ : syracuseStep 2799937 = 2099953) B2099953
theorem B6306113 : Blo 1474557 6306113 := bstep (se 2 (by rfl) ⟨2364792, by rfl⟩ : syracuseStep 6306113 = 4729585) B4729585
theorem B18905521 : Blo 1474557 18905521 := bstep (se 2 (by rfl) ⟨7089570, by rfl⟩ : syracuseStep 18905521 = 14179141) B14179141
theorem B17938867 : Blo 1474557 17938867 := bstep (se 1 (by rfl) ⟨13454150, by rfl⟩ : syracuseStep 17938867 = 26908301) B26908301
theorem B4979123 : Blo 1474557 4979123 := bstep (se 1 (by rfl) ⟨3734342, by rfl⟩ : syracuseStep 4979123 = 7468685) B7468685
theorem B5601757 : Blo 1474557 5601757 := bstep (se 3 (by rfl) ⟨1050329, by rfl⟩ : syracuseStep 5601757 = 2100659) B2100659
theorem B3734039 : Blo 1474557 3734039 := bstep (se 1 (by rfl) ⟨2800529, by rfl⟩ : syracuseStep 3734039 = 5601059) B5601059
theorem B3545623 : Blo 1474557 3545623 := bstep (se 1 (by rfl) ⟨2659217, by rfl⟩ : syracuseStep 3545623 = 5318435) B5318435
theorem B3545651 : Blo 1474557 3545651 := bstep (se 1 (by rfl) ⟨2659238, by rfl⟩ : syracuseStep 3545651 = 5318477) B5318477
theorem B2488907 : Blo 1474557 2488907 := bstep (se 1 (by rfl) ⟨1866680, by rfl⟩ : syracuseStep 2488907 = 3733361) B3733361
theorem B3152459 : Blo 1474557 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B2243161 : Blo 1474557 2243161 := bstep (se 2 (by rfl) ⟨841185, by rfl⟩ : syracuseStep 2243161 = 1682371) B1682371
theorem B4979393 : Blo 1474557 4979393 := bstep (se 2 (by rfl) ⟨1867272, by rfl⟩ : syracuseStep 4979393 = 3734545) B3734545
theorem B2489035 : Blo 1474557 2489035 := bstep (se 1 (by rfl) ⟨1866776, by rfl⟩ : syracuseStep 2489035 = 3733553) B3733553
theorem B2489177 : Blo 1474557 2489177 := bstep (se 2 (by rfl) ⟨933441, by rfl⟩ : syracuseStep 2489177 = 1866883) B1866883
theorem B23919461 : Blo 1474557 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B4201409 : Blo 1474557 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B2489305 : Blo 1474557 2489305 := bstep (se 2 (by rfl) ⟨933489, by rfl⟩ : syracuseStep 2489305 = 1866979) B1866979
theorem B4201433 : Blo 1474557 4201433 := bstep (se 2 (by rfl) ⟨1575537, by rfl⟩ : syracuseStep 4201433 = 3151075) B3151075
theorem B2800651 : Blo 1474557 2800651 := bstep (se 1 (by rfl) ⟨2100488, by rfl⟩ : syracuseStep 2800651 = 4200977) B4200977
theorem B30293027 : Blo 1474557 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B9452609 : Blo 1474557 9452609 := bstep (se 2 (by rfl) ⟨3544728, by rfl⟩ : syracuseStep 9452609 = 7089457) B7089457
theorem B1866827 : Blo 1474557 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B2800727 : Blo 1474557 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B3734707 : Blo 1474557 3734707 := bstep (se 1 (by rfl) ⟨2801030, by rfl⟩ : syracuseStep 3734707 = 5602061) B5602061
theorem B10632397 : Blo 1474557 10632397 := bstep (se 3 (by rfl) ⟨1993574, by rfl⟩ : syracuseStep 10632397 = 3987149) B3987149
theorem B4979933 : Blo 1474557 4979933 := bstep (se 3 (by rfl) ⟨933737, by rfl⟩ : syracuseStep 4979933 = 1867475) B1867475
theorem B5979395 : Blo 1474557 5979395 := bstep (se 1 (by rfl) ⟨4484546, by rfl⟩ : syracuseStep 5979395 = 8969093) B8969093
theorem B10640645 : Blo 1474557 10640645 := bstep (se 4 (by rfl) ⟨997560, by rfl⟩ : syracuseStep 10640645 = 1995121) B1995121
theorem B3734849 : Blo 1474557 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B16809281 : Blo 1474557 16809281 := bstep (se 2 (by rfl) ⟨6303480, by rfl⟩ : syracuseStep 16809281 = 12606961) B12606961
theorem B6298955 : Blo 1474557 6298955 := bstep (se 1 (by rfl) ⟨4724216, by rfl⟩ : syracuseStep 6298955 = 9448433) B9448433
theorem B7470467 : Blo 1474557 7470467 := bstep (se 1 (by rfl) ⟨5602850, by rfl⟩ : syracuseStep 7470467 = 11205701) B11205701
theorem B3153305 : Blo 1474557 3153305 := bstep (se 2 (by rfl) ⟨1182489, by rfl⟩ : syracuseStep 3153305 = 2364979) B2364979
theorem B2489879 : Blo 1474557 2489879 := bstep (se 1 (by rfl) ⟨1867409, by rfl⟩ : syracuseStep 2489879 = 3734819) B3734819
theorem B5979737 : Blo 1474557 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B2694745 : Blo 1474557 2694745 := bstep (se 2 (by rfl) ⟨1010529, by rfl⟩ : syracuseStep 2694745 = 2021059) B2021059
theorem B2490007 : Blo 1474557 2490007 := bstep (se 1 (by rfl) ⟨1867505, by rfl⟩ : syracuseStep 2490007 = 3735011) B3735011
theorem B40402637 : Blo 1474557 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B5603033 : Blo 1474557 5603033 := bstep (se 2 (by rfl) ⟨2101137, by rfl⟩ : syracuseStep 5603033 = 4202275) B4202275
theorem B1597163 : Blo 1474557 1597163 := bstep (se 1 (by rfl) ⟨1197872, by rfl⟩ : syracuseStep 1597163 = 2395745) B2395745
theorem B2801395 : Blo 1474557 2801395 := bstep (se 1 (by rfl) ⟨2101046, by rfl⟩ : syracuseStep 2801395 = 4202093) B4202093
theorem B1867531 : Blo 1474557 1867531 := bstep (se 1 (by rfl) ⟨1400648, by rfl⟩ : syracuseStep 1867531 = 2801297) B2801297
theorem B12599171 : Blo 1474557 12599171 := bstep (se 1 (by rfl) ⟨9449378, by rfl⟩ : syracuseStep 12599171 = 18898757) B18898757
theorem B2801623 : Blo 1474557 2801623 := bstep (se 1 (by rfl) ⟨2101217, by rfl⟩ : syracuseStep 2801623 = 4202435) B4202435
theorem B3989465 : Blo 1474557 3989465 := bstep (se 2 (by rfl) ⟨1496049, by rfl⟩ : syracuseStep 3989465 = 2992099) B2992099
theorem B1474567 : Blo 1474557 1474567 := bstep (se 1 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 1474567 = 2211851) B2211851
theorem B7471115 : Blo 1474557 7471115 := bstep (se 1 (by rfl) ⟨5603336, by rfl⟩ : syracuseStep 7471115 = 11206673) B11206673
theorem B1474575 : Blo 1474557 1474575 := bstep (se 1 (by rfl) ⟨1105931, by rfl⟩ : syracuseStep 1474575 = 2211863) B2211863
theorem B8970263 : Blo 1474557 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B2211899 : Blo 1474557 2211899 := bstep (se 1 (by rfl) ⟨1658924, by rfl⟩ : syracuseStep 2211899 = 3317849) B3317849
theorem B1474619 : Blo 1474557 1474619 := bstep (se 1 (by rfl) ⟨1105964, by rfl⟩ : syracuseStep 1474619 = 2211929) B2211929
theorem B4980797 : Blo 1474557 4980797 := bstep (se 3 (by rfl) ⟨933899, by rfl⟩ : syracuseStep 4980797 = 1867799) B1867799
theorem B163684421 : Blo 1474557 163684421 := bstep (se 4 (by rfl) ⟨15345414, by rfl⟩ : syracuseStep 163684421 = 30690829) B30690829
theorem B30269533 : Blo 1474557 30269533 := bstep (se 3 (by rfl) ⟨5675537, by rfl⟩ : syracuseStep 30269533 = 11351075) B11351075
theorem B2211959 : Blo 1474557 2211959 := bstep (se 1 (by rfl) ⟨1658969, by rfl⟩ : syracuseStep 2211959 = 3317939) B3317939
theorem B2801783 : Blo 1474557 2801783 := bstep (se 1 (by rfl) ⟨2101337, by rfl⟩ : syracuseStep 2801783 = 4202675) B4202675
theorem B1474695 : Blo 1474557 1474695 := bstep (se 1 (by rfl) ⟨1106021, by rfl⟩ : syracuseStep 1474695 = 2212043) B2212043
theorem B2695303 : Blo 1474557 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B2211983 : Blo 1474557 2211983 := bstep (se 1 (by rfl) ⟨1658987, by rfl⟩ : syracuseStep 2211983 = 3317975) B3317975
theorem B1474703 : Blo 1474557 1474703 := bstep (se 1 (by rfl) ⟨1106027, by rfl⟩ : syracuseStep 1474703 = 2212055) B2212055
theorem B7471277 : Blo 1474557 7471277 := bstep (se 3 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 7471277 = 2801729) B2801729
theorem B2212025 : Blo 1474557 2212025 := bstep (se 2 (by rfl) ⟨829509, by rfl⟩ : syracuseStep 2212025 = 1659019) B1659019
theorem B1474747 : Blo 1474557 1474747 := bstep (se 1 (by rfl) ⟨1106060, by rfl⟩ : syracuseStep 1474747 = 2212121) B2212121
theorem B2212103 : Blo 1474557 2212103 := bstep (se 1 (by rfl) ⟨1659077, by rfl⟩ : syracuseStep 2212103 = 3318155) B3318155
theorem B1474823 : Blo 1474557 1474823 := bstep (se 1 (by rfl) ⟨1106117, by rfl⟩ : syracuseStep 1474823 = 2212235) B2212235
theorem B4260107 : Blo 1474557 4260107 := bstep (se 1 (by rfl) ⟨3195080, by rfl⟩ : syracuseStep 4260107 = 6390161) B6390161
theorem B1474831 : Blo 1474557 1474831 := bstep (se 1 (by rfl) ⟨1106123, by rfl⟩ : syracuseStep 1474831 = 2212247) B2212247
theorem B3735841 : Blo 1474557 3735841 := bstep (se 2 (by rfl) ⟨1400940, by rfl⟩ : syracuseStep 3735841 = 2801881) B2801881
theorem B2212139 : Blo 1474557 2212139 := bstep (se 1 (by rfl) ⟨1659104, by rfl⟩ : syracuseStep 2212139 = 3318209) B3318209
theorem B1474875 : Blo 1474557 1474875 := bstep (se 1 (by rfl) ⟨1106156, by rfl⟩ : syracuseStep 1474875 = 2212313) B2212313
theorem B6299963 : Blo 1474557 6299963 := bstep (se 1 (by rfl) ⟨4724972, by rfl⟩ : syracuseStep 6299963 = 9449945) B9449945
theorem B4727099 : Blo 1474557 4727099 := bstep (se 1 (by rfl) ⟨3545324, by rfl⟩ : syracuseStep 4727099 = 7090649) B7090649
theorem B2212169 : Blo 1474557 2212169 := bstep (se 2 (by rfl) ⟨829563, by rfl⟩ : syracuseStep 2212169 = 1659127) B1659127
theorem B4202867 : Blo 1474557 4202867 := bstep (se 1 (by rfl) ⟨3152150, by rfl⟩ : syracuseStep 4202867 = 6304301) B6304301
theorem B2490743 : Blo 1474557 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B1474951 : Blo 1474557 1474951 := bstep (se 1 (by rfl) ⟨1106213, by rfl⟩ : syracuseStep 1474951 = 2212427) B2212427
theorem B1474959 : Blo 1474557 1474959 := bstep (se 1 (by rfl) ⟨1106219, by rfl⟩ : syracuseStep 1474959 = 2212439) B2212439
theorem B15958457 : Blo 1474557 15958457 := bstep (se 2 (by rfl) ⟨5984421, by rfl⟩ : syracuseStep 15958457 = 11968843) B11968843
theorem B2212283 : Blo 1474557 2212283 := bstep (se 1 (by rfl) ⟨1659212, by rfl⟩ : syracuseStep 2212283 = 3318425) B3318425
theorem B1475003 : Blo 1474557 1475003 := bstep (se 1 (by rfl) ⟨1106252, by rfl⟩ : syracuseStep 1475003 = 2212505) B2212505
theorem B2212343 : Blo 1474557 2212343 := bstep (se 1 (by rfl) ⟨1659257, by rfl⟩ : syracuseStep 2212343 = 3318515) B3318515
theorem B1475079 : Blo 1474557 1475079 := bstep (se 1 (by rfl) ⟨1106309, by rfl⟩ : syracuseStep 1475079 = 2212619) B2212619
theorem B2212367 : Blo 1474557 2212367 := bstep (se 1 (by rfl) ⟨1659275, by rfl⟩ : syracuseStep 2212367 = 3318551) B3318551
theorem B1475087 : Blo 1474557 1475087 := bstep (se 1 (by rfl) ⟨1106315, by rfl⟩ : syracuseStep 1475087 = 2212631) B2212631
theorem B2212409 : Blo 1474557 2212409 := bstep (se 2 (by rfl) ⟨829653, by rfl⟩ : syracuseStep 2212409 = 1659307) B1659307
theorem B1475131 : Blo 1474557 1475131 := bstep (se 1 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 1475131 = 2212697) B2212697
theorem B25207361 : Blo 1474557 25207361 := bstep (se 2 (by rfl) ⟨9452760, by rfl⟩ : syracuseStep 25207361 = 18905521) B18905521
theorem B3318407 : Blo 1474557 3318407 := bstep (se 1 (by rfl) ⟨2488805, by rfl⟩ : syracuseStep 3318407 = 4977611) B4977611
theorem B2212487 : Blo 1474557 2212487 := bstep (se 1 (by rfl) ⟨1659365, by rfl⟩ : syracuseStep 2212487 = 3318731) B3318731
theorem B1475207 : Blo 1474557 1475207 := bstep (se 1 (by rfl) ⟨1106405, by rfl⟩ : syracuseStep 1475207 = 2212811) B2212811
theorem B4260487 : Blo 1474557 4260487 := bstep (se 1 (by rfl) ⟨3195365, by rfl⟩ : syracuseStep 4260487 = 6390731) B6390731
theorem B1475215 : Blo 1474557 1475215 := bstep (se 1 (by rfl) ⟨1106411, by rfl⟩ : syracuseStep 1475215 = 2212823) B2212823
theorem B2212523 : Blo 1474557 2212523 := bstep (se 1 (by rfl) ⟨1659392, by rfl⟩ : syracuseStep 2212523 = 3318785) B3318785
theorem B1475259 : Blo 1474557 1475259 := bstep (se 1 (by rfl) ⟨1106444, by rfl⟩ : syracuseStep 1475259 = 2212889) B2212889
theorem B2212553 : Blo 1474557 2212553 := bstep (se 2 (by rfl) ⟨829707, by rfl⟩ : syracuseStep 2212553 = 1659415) B1659415
theorem B4547273 : Blo 1474557 4547273 := bstep (se 2 (by rfl) ⟨1705227, by rfl⟩ : syracuseStep 4547273 = 3410455) B3410455
theorem B4727497 : Blo 1474557 4727497 := bstep (se 2 (by rfl) ⟨1772811, by rfl⟩ : syracuseStep 4727497 = 3545623) B3545623
theorem B1475335 : Blo 1474557 1475335 := bstep (se 1 (by rfl) ⟨1106501, by rfl⟩ : syracuseStep 1475335 = 2213003) B2213003
theorem B1475343 : Blo 1474557 1475343 := bstep (se 1 (by rfl) ⟨1106507, by rfl⟩ : syracuseStep 1475343 = 2213015) B2213015
theorem B2990881 : Blo 1474557 2990881 := bstep (se 2 (by rfl) ⟨1121580, by rfl⟩ : syracuseStep 2990881 = 2243161) B2243161
theorem B3318587 : Blo 1474557 3318587 := bstep (se 1 (by rfl) ⟨2488940, by rfl⟩ : syracuseStep 3318587 = 4977881) B4977881
theorem B2212667 : Blo 1474557 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B1475387 : Blo 1474557 1475387 := bstep (se 1 (by rfl) ⟨1106540, by rfl⟩ : syracuseStep 1475387 = 2213081) B2213081
theorem B4203323 : Blo 1474557 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B2491195 : Blo 1474557 2491195 := bstep (se 1 (by rfl) ⟨1868396, by rfl⟩ : syracuseStep 2491195 = 3736793) B3736793
theorem B2212727 : Blo 1474557 2212727 := bstep (se 1 (by rfl) ⟨1659545, by rfl⟩ : syracuseStep 2212727 = 3319091) B3319091
theorem B3736439 : Blo 1474557 3736439 := bstep (se 1 (by rfl) ⟨2802329, by rfl⟩ : syracuseStep 3736439 = 5604659) B5604659
theorem B1475463 : Blo 1474557 1475463 := bstep (se 1 (by rfl) ⟨1106597, by rfl⟩ : syracuseStep 1475463 = 2213195) B2213195
theorem B2212751 : Blo 1474557 2212751 := bstep (se 1 (by rfl) ⟨1659563, by rfl⟩ : syracuseStep 2212751 = 3319127) B3319127
theorem B1475471 : Blo 1474557 1475471 := bstep (se 1 (by rfl) ⟨1106603, by rfl⟩ : syracuseStep 1475471 = 2213207) B2213207
theorem B3318713 : Blo 1474557 3318713 := bstep (se 2 (by rfl) ⟨1244517, by rfl⟩ : syracuseStep 3318713 = 2489035) B2489035
theorem B2212793 : Blo 1474557 2212793 := bstep (se 2 (by rfl) ⟨829797, by rfl⟩ : syracuseStep 2212793 = 1659595) B1659595
theorem B1475515 : Blo 1474557 1475515 := bstep (se 1 (by rfl) ⟨1106636, by rfl⟩ : syracuseStep 1475515 = 2213273) B2213273
theorem B2491337 : Blo 1474557 2491337 := bstep (se 2 (by rfl) ⟨934251, by rfl⟩ : syracuseStep 2491337 = 1868503) B1868503
theorem B8405963 : Blo 1474557 8405963 := bstep (se 1 (by rfl) ⟨6304472, by rfl⟩ : syracuseStep 8405963 = 12608945) B12608945
theorem B2212871 : Blo 1474557 2212871 := bstep (se 1 (by rfl) ⟨1659653, by rfl⟩ : syracuseStep 2212871 = 3319307) B3319307
theorem B1475591 : Blo 1474557 1475591 := bstep (se 1 (by rfl) ⟨1106693, by rfl⟩ : syracuseStep 1475591 = 2213387) B2213387
theorem B1475599 : Blo 1474557 1475599 := bstep (se 1 (by rfl) ⟨1106699, by rfl⟩ : syracuseStep 1475599 = 2213399) B2213399
theorem B2212907 : Blo 1474557 2212907 := bstep (se 1 (by rfl) ⟨1659680, by rfl⟩ : syracuseStep 2212907 = 3319361) B3319361
theorem B17957933 : Blo 1474557 17957933 := bstep (se 3 (by rfl) ⟨3367112, by rfl⟩ : syracuseStep 17957933 = 6734225) B6734225
theorem B1475643 : Blo 1474557 1475643 := bstep (se 1 (by rfl) ⟨1106732, by rfl⟩ : syracuseStep 1475643 = 2213465) B2213465
theorem B2212937 : Blo 1474557 2212937 := bstep (se 2 (by rfl) ⟨829851, by rfl⟩ : syracuseStep 2212937 = 1659703) B1659703
theorem B2991239 : Blo 1474557 2991239 := bstep (se 1 (by rfl) ⟨2243429, by rfl⟩ : syracuseStep 2991239 = 4486859) B4486859
theorem B1475719 : Blo 1474557 1475719 := bstep (se 1 (by rfl) ⟨1106789, by rfl⟩ : syracuseStep 1475719 = 2213579) B2213579
theorem B1475727 : Blo 1474557 1475727 := bstep (se 1 (by rfl) ⟨1106795, by rfl⟩ : syracuseStep 1475727 = 2213591) B2213591
theorem B2213051 : Blo 1474557 2213051 := bstep (se 1 (by rfl) ⟨1659788, by rfl⟩ : syracuseStep 2213051 = 3319577) B3319577
theorem B1475771 : Blo 1474557 1475771 := bstep (se 1 (by rfl) ⟨1106828, by rfl⟩ : syracuseStep 1475771 = 2213657) B2213657
theorem B2213111 : Blo 1474557 2213111 := bstep (se 1 (by rfl) ⟨1659833, by rfl⟩ : syracuseStep 2213111 = 3319667) B3319667
theorem B1475847 : Blo 1474557 1475847 := bstep (se 1 (by rfl) ⟨1106885, by rfl⟩ : syracuseStep 1475847 = 2213771) B2213771
theorem B3319055 : Blo 1474557 3319055 := bstep (se 1 (by rfl) ⟨2489291, by rfl⟩ : syracuseStep 3319055 = 4978583) B4978583
theorem B2213135 : Blo 1474557 2213135 := bstep (se 1 (by rfl) ⟨1659851, by rfl⟩ : syracuseStep 2213135 = 3319703) B3319703
theorem B1475855 : Blo 1474557 1475855 := bstep (se 1 (by rfl) ⟨1106891, by rfl⟩ : syracuseStep 1475855 = 2213783) B2213783
theorem B3319073 : Blo 1474557 3319073 := bstep (se 2 (by rfl) ⟨1244652, by rfl⟩ : syracuseStep 3319073 = 2489305) B2489305
theorem B2213177 : Blo 1474557 2213177 := bstep (se 2 (by rfl) ⟨829941, by rfl⟩ : syracuseStep 2213177 = 1659883) B1659883
theorem B1475899 : Blo 1474557 1475899 := bstep (se 1 (by rfl) ⟨1106924, by rfl⟩ : syracuseStep 1475899 = 2213849) B2213849
theorem B2213255 : Blo 1474557 2213255 := bstep (se 1 (by rfl) ⟨1659941, by rfl⟩ : syracuseStep 2213255 = 3319883) B3319883
theorem B1475975 : Blo 1474557 1475975 := bstep (se 1 (by rfl) ⟨1106981, by rfl⟩ : syracuseStep 1475975 = 2213963) B2213963
theorem B1475983 : Blo 1474557 1475983 := bstep (se 1 (by rfl) ⟨1106987, by rfl⟩ : syracuseStep 1475983 = 2213975) B2213975
theorem B2213291 : Blo 1474557 2213291 := bstep (se 1 (by rfl) ⟨1659968, by rfl⟩ : syracuseStep 2213291 = 3319937) B3319937
theorem B4982201 : Blo 1474557 4982201 := bstep (se 2 (by rfl) ⟨1868325, by rfl⟩ : syracuseStep 4982201 = 3736651) B3736651
theorem B1476027 : Blo 1474557 1476027 := bstep (se 1 (by rfl) ⟨1107020, by rfl⟩ : syracuseStep 1476027 = 2214041) B2214041
theorem B2213321 : Blo 1474557 2213321 := bstep (se 2 (by rfl) ⟨829995, by rfl⟩ : syracuseStep 2213321 = 1659991) B1659991
theorem B9455069 : Blo 1474557 9455069 := bstep (se 3 (by rfl) ⟨1772825, by rfl⟩ : syracuseStep 9455069 = 3545651) B3545651
theorem B1476103 : Blo 1474557 1476103 := bstep (se 1 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 1476103 = 2214155) B2214155
theorem B1476111 : Blo 1474557 1476111 := bstep (se 1 (by rfl) ⟨1107083, by rfl⟩ : syracuseStep 1476111 = 2214167) B2214167
theorem B4204075 : Blo 1474557 4204075 := bstep (se 1 (by rfl) ⟨3153056, by rfl⟩ : syracuseStep 4204075 = 6306113) B6306113
theorem B2213435 : Blo 1474557 2213435 := bstep (se 1 (by rfl) ⟨1660076, by rfl⟩ : syracuseStep 2213435 = 3320153) B3320153
theorem B1476155 : Blo 1474557 1476155 := bstep (se 1 (by rfl) ⟨1107116, by rfl⟩ : syracuseStep 1476155 = 2214233) B2214233
theorem B7980611 : Blo 1474557 7980611 := bstep (se 1 (by rfl) ⟨5985458, by rfl⟩ : syracuseStep 7980611 = 11970917) B11970917
theorem B3319415 : Blo 1474557 3319415 := bstep (se 1 (by rfl) ⟨2489561, by rfl⟩ : syracuseStep 3319415 = 4979123) B4979123
theorem B2213495 : Blo 1474557 2213495 := bstep (se 1 (by rfl) ⟨1660121, by rfl⟩ : syracuseStep 2213495 = 3320243) B3320243
theorem B1476231 : Blo 1474557 1476231 := bstep (se 1 (by rfl) ⟨1107173, by rfl⟩ : syracuseStep 1476231 = 2214347) B2214347
theorem B2213519 : Blo 1474557 2213519 := bstep (se 1 (by rfl) ⟨1660139, by rfl⟩ : syracuseStep 2213519 = 3320279) B3320279
theorem B1476239 : Blo 1474557 1476239 := bstep (se 1 (by rfl) ⟨1107179, by rfl⟩ : syracuseStep 1476239 = 2214359) B2214359
theorem B2213561 : Blo 1474557 2213561 := bstep (se 2 (by rfl) ⟨830085, by rfl⟩ : syracuseStep 2213561 = 1660171) B1660171
theorem B1476283 : Blo 1474557 1476283 := bstep (se 1 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 1476283 = 2214425) B2214425
theorem B7472897 : Blo 1474557 7472897 := bstep (se 2 (by rfl) ⟨2802336, by rfl⟩ : syracuseStep 7472897 = 5604673) B5604673
theorem B2213639 : Blo 1474557 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B1476359 : Blo 1474557 1476359 := bstep (se 1 (by rfl) ⟨1107269, by rfl⟩ : syracuseStep 1476359 = 2214539) B2214539
theorem B1476367 : Blo 1474557 1476367 := bstep (se 1 (by rfl) ⟨1107275, by rfl⟩ : syracuseStep 1476367 = 2214551) B2214551
theorem B3319595 : Blo 1474557 3319595 := bstep (se 1 (by rfl) ⟨2489696, by rfl⟩ : syracuseStep 3319595 = 4979393) B4979393
theorem B2213675 : Blo 1474557 2213675 := bstep (se 1 (by rfl) ⟨1660256, by rfl⟩ : syracuseStep 2213675 = 3320513) B3320513
theorem B1476411 : Blo 1474557 1476411 := bstep (se 1 (by rfl) ⟨1107308, by rfl⟩ : syracuseStep 1476411 = 2214617) B2214617
theorem B4204349 : Blo 1474557 4204349 := bstep (se 3 (by rfl) ⟨788315, by rfl⟩ : syracuseStep 4204349 = 1576631) B1576631
theorem B2213705 : Blo 1474557 2213705 := bstep (se 2 (by rfl) ⟨830139, by rfl⟩ : syracuseStep 2213705 = 1660279) B1660279
theorem B1476487 : Blo 1474557 1476487 := bstep (se 1 (by rfl) ⟨1107365, by rfl⟩ : syracuseStep 1476487 = 2214731) B2214731
theorem B1476495 : Blo 1474557 1476495 := bstep (se 1 (by rfl) ⟨1107371, by rfl⟩ : syracuseStep 1476495 = 2214743) B2214743
theorem B2213819 : Blo 1474557 2213819 := bstep (se 1 (by rfl) ⟨1660364, by rfl⟩ : syracuseStep 2213819 = 3320729) B3320729
theorem B1476539 : Blo 1474557 1476539 := bstep (se 1 (by rfl) ⟨1107404, by rfl⟩ : syracuseStep 1476539 = 2214809) B2214809
theorem B2213879 : Blo 1474557 2213879 := bstep (se 1 (by rfl) ⟨1660409, by rfl⟩ : syracuseStep 2213879 = 3320819) B3320819
theorem B4982795 : Blo 1474557 4982795 := bstep (se 1 (by rfl) ⟨3737096, by rfl⟩ : syracuseStep 4982795 = 7474193) B7474193
theorem B2213903 : Blo 1474557 2213903 := bstep (se 1 (by rfl) ⟨1660427, by rfl⟩ : syracuseStep 2213903 = 3320855) B3320855
theorem B20195351 : Blo 1474557 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B6301739 : Blo 1474557 6301739 := bstep (se 1 (by rfl) ⟨4726304, by rfl⟩ : syracuseStep 6301739 = 9452609) B9452609
theorem B2213945 : Blo 1474557 2213945 := bstep (se 2 (by rfl) ⟨830229, by rfl⟩ : syracuseStep 2213945 = 1660459) B1660459
theorem B5605463 : Blo 1474557 5605463 := bstep (se 1 (by rfl) ⟨4204097, by rfl⟩ : syracuseStep 5605463 = 8408195) B8408195
theorem B4982903 : Blo 1474557 4982903 := bstep (se 1 (by rfl) ⟨3737177, by rfl⟩ : syracuseStep 4982903 = 7474355) B7474355
theorem B2214023 : Blo 1474557 2214023 := bstep (se 1 (by rfl) ⟨1660517, by rfl⟩ : syracuseStep 2214023 = 3321035) B3321035
theorem B3319955 : Blo 1474557 3319955 := bstep (se 1 (by rfl) ⟨2489966, by rfl⟩ : syracuseStep 3319955 = 4979933) B4979933
theorem B2214059 : Blo 1474557 2214059 := bstep (se 1 (by rfl) ⟨1660544, by rfl⟩ : syracuseStep 2214059 = 3321089) B3321089
theorem B3320009 : Blo 1474557 3320009 := bstep (se 2 (by rfl) ⟨1245003, by rfl⟩ : syracuseStep 3320009 = 2490007) B2490007
theorem B2214089 : Blo 1474557 2214089 := bstep (se 2 (by rfl) ⟨830283, by rfl⟩ : syracuseStep 2214089 = 1660567) B1660567
theorem B2214203 : Blo 1474557 2214203 := bstep (se 1 (by rfl) ⟨1660652, by rfl⟩ : syracuseStep 2214203 = 3321305) B3321305
theorem B2214263 : Blo 1474557 2214263 := bstep (se 1 (by rfl) ⟨1660697, by rfl⟩ : syracuseStep 2214263 = 3321395) B3321395
theorem B3410311 : Blo 1474557 3410311 := bstep (se 1 (by rfl) ⟨2557733, by rfl⟩ : syracuseStep 3410311 = 5115467) B5115467
theorem B2214287 : Blo 1474557 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B2214329 : Blo 1474557 2214329 := bstep (se 2 (by rfl) ⟨830373, by rfl⟩ : syracuseStep 2214329 = 1660747) B1660747
theorem B2214407 : Blo 1474557 2214407 := bstep (se 1 (by rfl) ⟨1660805, by rfl⟩ : syracuseStep 2214407 = 3321611) B3321611
theorem B1772047 : Blo 1474557 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B3787307 : Blo 1474557 3787307 := bstep (se 1 (by rfl) ⟨2840480, by rfl⟩ : syracuseStep 3787307 = 5680961) B5680961
theorem B7473707 : Blo 1474557 7473707 := bstep (se 1 (by rfl) ⟨5605280, by rfl⟩ : syracuseStep 7473707 = 11210561) B11210561
theorem B2214443 : Blo 1474557 2214443 := bstep (se 1 (by rfl) ⟨1660832, by rfl⟩ : syracuseStep 2214443 = 3321665) B3321665
theorem B5605949 : Blo 1474557 5605949 := bstep (se 3 (by rfl) ⟨1051115, by rfl⟩ : syracuseStep 5605949 = 2102231) B2102231
theorem B2214473 : Blo 1474557 2214473 := bstep (se 2 (by rfl) ⟨830427, by rfl⟩ : syracuseStep 2214473 = 1660855) B1660855
theorem B8399447 : Blo 1474557 8399447 := bstep (se 1 (by rfl) ⟨6299585, by rfl⟩ : syracuseStep 8399447 = 12599171) B12599171
theorem B1575559 : Blo 1474557 1575559 := bstep (se 1 (by rfl) ⟨1181669, by rfl⟩ : syracuseStep 1575559 = 2363339) B2363339
theorem B2214587 : Blo 1474557 2214587 := bstep (se 1 (by rfl) ⟨1660940, by rfl⟩ : syracuseStep 2214587 = 3321881) B3321881
theorem B2214647 : Blo 1474557 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B2362127 : Blo 1474557 2362127 := bstep (se 1 (by rfl) ⟨1771595, by rfl⟩ : syracuseStep 2362127 = 3543191) B3543191
theorem B2214671 : Blo 1474557 2214671 := bstep (se 1 (by rfl) ⟨1661003, by rfl⟩ : syracuseStep 2214671 = 3322007) B3322007
theorem B2214713 : Blo 1474557 2214713 := bstep (se 2 (by rfl) ⟨830517, by rfl⟩ : syracuseStep 2214713 = 1661035) B1661035
theorem B3320711 : Blo 1474557 3320711 := bstep (se 1 (by rfl) ⟨2490533, by rfl⟩ : syracuseStep 3320711 = 4981067) B4981067
theorem B2214791 : Blo 1474557 2214791 := bstep (se 1 (by rfl) ⟨1661093, by rfl⟩ : syracuseStep 2214791 = 3322187) B3322187
theorem B2214827 : Blo 1474557 2214827 := bstep (se 1 (by rfl) ⟨1661120, by rfl⟩ : syracuseStep 2214827 = 3322241) B3322241
theorem B7465931 : Blo 1474557 7465931 := bstep (se 1 (by rfl) ⟨5599448, by rfl⟩ : syracuseStep 7465931 = 11198897) B11198897
theorem B2100215 : Blo 1474557 2100215 := bstep (se 1 (by rfl) ⟨1575161, by rfl⟩ : syracuseStep 2100215 = 3150323) B3150323
theorem B3320891 : Blo 1474557 3320891 := bstep (se 1 (by rfl) ⟨2490668, by rfl⟩ : syracuseStep 3320891 = 4981337) B4981337
theorem B4484231 : Blo 1474557 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B221367437 : Blo 1474557 221367437 := bstep (se 3 (by rfl) ⟨41506394, by rfl⟩ : syracuseStep 221367437 = 83012789) B83012789
theorem B3321017 : Blo 1474557 3321017 := bstep (se 2 (by rfl) ⟨1245381, by rfl⟩ : syracuseStep 3321017 = 2490763) B2490763
theorem B60599501 : Blo 1474557 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B7466255 : Blo 1474557 7466255 := bstep (se 1 (by rfl) ⟨5599691, by rfl⟩ : syracuseStep 7466255 = 11199383) B11199383
theorem B3788075 : Blo 1474557 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B5049715 : Blo 1474557 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B1576379 : Blo 1474557 1576379 := bstep (se 1 (by rfl) ⟨1182284, by rfl⟩ : syracuseStep 1576379 = 2364569) B2364569
theorem B3321359 : Blo 1474557 3321359 := bstep (se 1 (by rfl) ⟨2491019, by rfl⟩ : syracuseStep 3321359 = 4982039) B4982039
theorem B3321377 : Blo 1474557 3321377 := bstep (se 2 (by rfl) ⟨1245516, by rfl⟩ : syracuseStep 3321377 = 2491033) B2491033
theorem B7089707 : Blo 1474557 7089707 := bstep (se 1 (by rfl) ⟨5317280, by rfl⟩ : syracuseStep 7089707 = 10634561) B10634561
theorem B7475003 : Blo 1474557 7475003 := bstep (se 1 (by rfl) ⟨5606252, by rfl⟩ : syracuseStep 7475003 = 11212505) B11212505
theorem B3321719 : Blo 1474557 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B3321899 : Blo 1474557 3321899 := bstep (se 1 (by rfl) ⟨2491424, by rfl⟩ : syracuseStep 3321899 = 4982849) B4982849
theorem B35893489 : Blo 1474557 35893489 := bstep (se 2 (by rfl) ⟨13460058, by rfl⟩ : syracuseStep 35893489 = 26920117) B26920117
theorem B14176529 : Blo 1474557 14176529 := bstep (se 2 (by rfl) ⟨5316198, by rfl⟩ : syracuseStep 14176529 = 10632397) B10632397
theorem B1659271 : Blo 1474557 1659271 := bstep (se 1 (by rfl) ⟨1244453, by rfl⟩ : syracuseStep 1659271 = 2488907) B2488907
theorem B2101639 : Blo 1474557 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B16806365 : Blo 1474557 16806365 := bstep (se 3 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 16806365 = 6302387) B6302387
theorem B18919979 : Blo 1474557 18919979 := bstep (se 1 (by rfl) ⟨14189984, by rfl⟩ : syracuseStep 18919979 = 28379969) B28379969
theorem B1659451 : Blo 1474557 1659451 := bstep (se 1 (by rfl) ⟨1244588, by rfl⟩ : syracuseStep 1659451 = 2489177) B2489177
theorem B15946307 : Blo 1474557 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B7467713 : Blo 1474557 7467713 := bstep (se 2 (by rfl) ⟨2800392, by rfl⟩ : syracuseStep 7467713 = 5600785) B5600785
theorem B12120833 : Blo 1474557 12120833 := bstep (se 2 (by rfl) ⟨4545312, by rfl⟩ : syracuseStep 12120833 = 9090625) B9090625
theorem B3592993 : Blo 1474557 3592993 := bstep (se 2 (by rfl) ⟨1347372, by rfl⟩ : syracuseStep 3592993 = 2694745) B2694745
theorem B3986263 : Blo 1474557 3986263 := bstep (se 1 (by rfl) ⟨2989697, by rfl⟩ : syracuseStep 3986263 = 5979395) B5979395
theorem B4199303 : Blo 1474557 4199303 := bstep (se 1 (by rfl) ⟨3149477, by rfl⟩ : syracuseStep 4199303 = 6298955) B6298955
theorem B2102203 : Blo 1474557 2102203 := bstep (se 1 (by rfl) ⟨1576652, by rfl⟩ : syracuseStep 2102203 = 3153305) B3153305
theorem B1659919 : Blo 1474557 1659919 := bstep (se 1 (by rfl) ⟨1244939, by rfl⟩ : syracuseStep 1659919 = 2489879) B2489879
theorem B5600285 : Blo 1474557 5600285 := bstep (se 3 (by rfl) ⟨1050053, by rfl⟩ : syracuseStep 5600285 = 2100107) B2100107
theorem B5600299 : Blo 1474557 5600299 := bstep (se 1 (by rfl) ⟨4200224, by rfl⟩ : syracuseStep 5600299 = 8400449) B8400449
theorem B3986491 : Blo 1474557 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B4199485 : Blo 1474557 4199485 := bstep (se 3 (by rfl) ⟨787403, by rfl⟩ : syracuseStep 4199485 = 1574807) B1574807
theorem B17036405 : Blo 1474557 17036405 := bstep (se 5 (by rfl) ⟨798581, by rfl⟩ : syracuseStep 17036405 = 1597163) B1597163
theorem B11203757 : Blo 1474557 11203757 := bstep (se 3 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 11203757 = 4201409) B4201409
theorem B6067457 : Blo 1474557 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B4977935 : Blo 1474557 4977935 := bstep (se 1 (by rfl) ⟨3733451, by rfl⟩ : syracuseStep 4977935 = 7466903) B7466903
theorem B2659643 : Blo 1474557 2659643 := bstep (se 1 (by rfl) ⟨1994732, by rfl⟩ : syracuseStep 2659643 = 3989465) B3989465
theorem B25220483 : Blo 1474557 25220483 := bstep (se 1 (by rfl) ⟨18915362, by rfl⟩ : syracuseStep 25220483 = 37830725) B37830725
theorem B4724153 : Blo 1474557 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B1660423 : Blo 1474557 1660423 := bstep (se 1 (by rfl) ⟨1245317, by rfl⟩ : syracuseStep 1660423 = 2490635) B2490635
theorem B4199951 : Blo 1474557 4199951 := bstep (se 1 (by rfl) ⟨3149963, by rfl⟩ : syracuseStep 4199951 = 6299927) B6299927
theorem B4978205 : Blo 1474557 4978205 := bstep (se 3 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 4978205 = 1866827) B1866827
theorem B2242091 : Blo 1474557 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B14177911 : Blo 1474557 14177911 := bstep (se 1 (by rfl) ⟨10633433, by rfl⟩ : syracuseStep 14177911 = 21266867) B21266867
theorem B1660603 : Blo 1474557 1660603 := bstep (se 1 (by rfl) ⟨1245452, by rfl⟩ : syracuseStep 1660603 = 2490905) B2490905
theorem B7673545 : Blo 1474557 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B8640229 : Blo 1474557 8640229 := bstep (se 4 (by rfl) ⟨810021, by rfl⟩ : syracuseStep 8640229 = 1620043) B1620043
theorem B3733249 : Blo 1474557 3733249 := bstep (se 2 (by rfl) ⟨1399968, by rfl⟩ : syracuseStep 3733249 = 2799937) B2799937
theorem B31913797 : Blo 1474557 31913797 := bstep (se 4 (by rfl) ⟨2991918, by rfl⟩ : syracuseStep 31913797 = 5983837) B5983837
theorem B145446731 : Blo 1474557 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B40384331 : Blo 1474557 40384331 := bstep (se 1 (by rfl) ⟨30288248, by rfl⟩ : syracuseStep 40384331 = 60576497) B60576497
theorem B23918489 : Blo 1474557 23918489 := bstep (se 2 (by rfl) ⟨8969433, by rfl⟩ : syracuseStep 23918489 = 17938867) B17938867
theorem B3151801 : Blo 1474557 3151801 := bstep (se 2 (by rfl) ⟨1181925, by rfl⟩ : syracuseStep 3151801 = 2363851) B2363851
theorem B5314513 : Blo 1474557 5314513 := bstep (se 2 (by rfl) ⟨1992942, by rfl⟩ : syracuseStep 5314513 = 3985885) B3985885
theorem B7469009 : Blo 1474557 7469009 := bstep (se 2 (by rfl) ⟨2800878, by rfl⟩ : syracuseStep 7469009 = 5601757) B5601757
theorem B2244937 : Blo 1474557 2244937 := bstep (se 2 (by rfl) ⟨841851, by rfl⟩ : syracuseStep 2244937 = 1683703) B1683703
theorem B1661071 : Blo 1474557 1661071 := bstep (se 1 (by rfl) ⟨1245803, by rfl⟩ : syracuseStep 1661071 = 2491607) B2491607
theorem B7567631 : Blo 1474557 7567631 := bstep (se 1 (by rfl) ⟨5675723, by rfl⟩ : syracuseStep 7567631 = 11351447) B11351447
theorem B3733847 : Blo 1474557 3733847 := bstep (se 1 (by rfl) ⟨2800385, by rfl⟩ : syracuseStep 3733847 = 5600771) B5600771
theorem B7977305 : Blo 1474557 7977305 := bstep (se 2 (by rfl) ⟨2991489, by rfl⟩ : syracuseStep 7977305 = 5982979) B5982979
theorem B2488711 : Blo 1474557 2488711 := bstep (se 1 (by rfl) ⟨1866533, by rfl⟩ : syracuseStep 2488711 = 3733067) B3733067
theorem B3734059 : Blo 1474557 3734059 := bstep (se 1 (by rfl) ⟨2800544, by rfl⟩ : syracuseStep 3734059 = 5601089) B5601089
theorem B3365435 : Blo 1474557 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B23935607 : Blo 1474557 23935607 := bstep (se 1 (by rfl) ⟨17951705, by rfl⟩ : syracuseStep 23935607 = 35903411) B35903411
theorem B3734201 : Blo 1474557 3734201 := bstep (se 2 (by rfl) ⟨1400325, by rfl⟩ : syracuseStep 3734201 = 2800651) B2800651
theorem B3545785 : Blo 1474557 3545785 := bstep (se 2 (by rfl) ⟨1329669, by rfl⟩ : syracuseStep 3545785 = 2659339) B2659339
theorem B4201217 : Blo 1474557 4201217 := bstep (se 2 (by rfl) ⟨1575456, by rfl⟩ : syracuseStep 4201217 = 3150913) B3150913
theorem B1866503 : Blo 1474557 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B4979609 : Blo 1474557 4979609 := bstep (se 2 (by rfl) ⟨1867353, by rfl⟩ : syracuseStep 4979609 = 3734707) B3734707
theorem B2489359 : Blo 1474557 2489359 := bstep (se 1 (by rfl) ⟨1867019, by rfl⟩ : syracuseStep 2489359 = 3734039) B3734039
theorem B1596731 : Blo 1474557 1596731 := bstep (se 1 (by rfl) ⟨1197548, by rfl⟩ : syracuseStep 1596731 = 2395097) B2395097
theorem B2800955 : Blo 1474557 2800955 := bstep (se 1 (by rfl) ⟨2100716, by rfl⟩ : syracuseStep 2800955 = 4201433) B4201433
theorem B1867151 : Blo 1474557 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B5316025 : Blo 1474557 5316025 := bstep (se 2 (by rfl) ⟨1993509, by rfl⟩ : syracuseStep 5316025 = 3987019) B3987019
theorem B7093763 : Blo 1474557 7093763 := bstep (se 1 (by rfl) ⟨5320322, by rfl⟩ : syracuseStep 7093763 = 10640645) B10640645
theorem B14188061 : Blo 1474557 14188061 := bstep (se 3 (by rfl) ⟨2660261, by rfl⟩ : syracuseStep 14188061 = 5320523) B5320523
theorem B2489899 : Blo 1474557 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B11206187 : Blo 1474557 11206187 := bstep (se 1 (by rfl) ⟨8404640, by rfl⟩ : syracuseStep 11206187 = 16809281) B16809281
theorem B3153467 : Blo 1474557 3153467 := bstep (se 1 (by rfl) ⟨2365100, by rfl⟩ : syracuseStep 3153467 = 4730201) B4730201
theorem B4980311 : Blo 1474557 4980311 := bstep (se 1 (by rfl) ⟨3735233, by rfl⟩ : syracuseStep 4980311 = 7470467) B7470467
theorem B3735193 : Blo 1474557 3735193 := bstep (se 2 (by rfl) ⟨1400697, by rfl⟩ : syracuseStep 3735193 = 2801395) B2801395
theorem B2490041 : Blo 1474557 2490041 := bstep (se 2 (by rfl) ⟨933765, by rfl⟩ : syracuseStep 2490041 = 1867531) B1867531
theorem B2801441 : Blo 1474557 2801441 := bstep (se 2 (by rfl) ⟨1050540, by rfl⟩ : syracuseStep 2801441 = 2101081) B2101081
theorem B26935091 : Blo 1474557 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B3735355 : Blo 1474557 3735355 := bstep (se 1 (by rfl) ⟨2801516, by rfl⟩ : syracuseStep 3735355 = 5603033) B5603033
theorem B3735497 : Blo 1474557 3735497 := bstep (se 2 (by rfl) ⟨1400811, by rfl⟩ : syracuseStep 3735497 = 2801623) B2801623
theorem B11198411 : Blo 1474557 11198411 := bstep (se 1 (by rfl) ⟨8398808, by rfl⟩ : syracuseStep 11198411 = 16797617) B16797617
theorem B4980743 : Blo 1474557 4980743 := bstep (se 1 (by rfl) ⟨3735557, by rfl⟩ : syracuseStep 4980743 = 7471115) B7471115
theorem B5980175 : Blo 1474557 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B1474599 : Blo 1474557 1474599 := bstep (se 1 (by rfl) ⟨1105949, by rfl⟩ : syracuseStep 1474599 = 2211899) B2211899
theorem B1474639 : Blo 1474557 1474639 := bstep (se 1 (by rfl) ⟨1105979, by rfl⟩ : syracuseStep 1474639 = 2211959) B2211959
theorem B1867855 : Blo 1474557 1867855 := bstep (se 1 (by rfl) ⟨1400891, by rfl⟩ : syracuseStep 1867855 = 2801783) B2801783
theorem B1474655 : Blo 1474557 1474655 := bstep (se 1 (by rfl) ⟨1105991, by rfl⟩ : syracuseStep 1474655 = 2211983) B2211983
theorem B4980851 : Blo 1474557 4980851 := bstep (se 1 (by rfl) ⟨3735638, by rfl⟩ : syracuseStep 4980851 = 7471277) B7471277
theorem B1474683 : Blo 1474557 1474683 := bstep (se 1 (by rfl) ⟨1106012, by rfl⟩ : syracuseStep 1474683 = 2212025) B2212025
theorem B1474735 : Blo 1474557 1474735 := bstep (se 1 (by rfl) ⟨1106051, by rfl⟩ : syracuseStep 1474735 = 2212103) B2212103
theorem B1474759 : Blo 1474557 1474759 := bstep (se 1 (by rfl) ⟨1106069, by rfl⟩ : syracuseStep 1474759 = 2212139) B2212139
theorem B1474779 : Blo 1474557 1474779 := bstep (se 1 (by rfl) ⟨1106084, by rfl⟩ : syracuseStep 1474779 = 2212169) B2212169
theorem B1474855 : Blo 1474557 1474855 := bstep (se 1 (by rfl) ⟨1106141, by rfl⟩ : syracuseStep 1474855 = 2212283) B2212283
theorem B47857985 : Blo 1474557 47857985 := bstep (se 2 (by rfl) ⟨17946744, by rfl⟩ : syracuseStep 47857985 = 35893489) B35893489
theorem B1474895 : Blo 1474557 1474895 := bstep (se 1 (by rfl) ⟨1106171, by rfl⟩ : syracuseStep 1474895 = 2212343) B2212343
theorem B1474911 : Blo 1474557 1474911 := bstep (se 1 (by rfl) ⟨1106183, by rfl⟩ : syracuseStep 1474911 = 2212367) B2212367
theorem B1474939 : Blo 1474557 1474939 := bstep (se 1 (by rfl) ⟨1106204, by rfl⟩ : syracuseStep 1474939 = 2212409) B2212409
theorem B4981121 : Blo 1474557 4981121 := bstep (se 2 (by rfl) ⟨1867920, by rfl⟩ : syracuseStep 4981121 = 3735841) B3735841
theorem B2212271 : Blo 1474557 2212271 := bstep (se 1 (by rfl) ⟨1659203, by rfl⟩ : syracuseStep 2212271 = 3318407) B3318407
theorem B1474991 : Blo 1474557 1474991 := bstep (se 1 (by rfl) ⟨1106243, by rfl⟩ : syracuseStep 1474991 = 2212487) B2212487
theorem B1475015 : Blo 1474557 1475015 := bstep (se 1 (by rfl) ⟨1106261, by rfl⟩ : syracuseStep 1475015 = 2212523) B2212523
theorem B1475035 : Blo 1474557 1475035 := bstep (se 1 (by rfl) ⟨1106276, by rfl⟩ : syracuseStep 1475035 = 2212553) B2212553
theorem B3318281 : Blo 1474557 3318281 := bstep (se 2 (by rfl) ⟨1244355, by rfl⟩ : syracuseStep 3318281 = 2488711) B2488711
theorem B2212361 : Blo 1474557 2212361 := bstep (se 2 (by rfl) ⟨829635, by rfl⟩ : syracuseStep 2212361 = 1659271) B1659271
theorem B4547081 : Blo 1474557 4547081 := bstep (se 2 (by rfl) ⟨1705155, by rfl⟩ : syracuseStep 4547081 = 3410311) B3410311
theorem B2802185 : Blo 1474557 2802185 := bstep (se 2 (by rfl) ⟨1050819, by rfl⟩ : syracuseStep 2802185 = 2101639) B2101639
theorem B2212391 : Blo 1474557 2212391 := bstep (se 1 (by rfl) ⟨1659293, by rfl⟩ : syracuseStep 2212391 = 3318587) B3318587
theorem B1475111 : Blo 1474557 1475111 := bstep (se 1 (by rfl) ⟨1106333, by rfl⟩ : syracuseStep 1475111 = 2212667) B2212667
theorem B2802215 : Blo 1474557 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B1475151 : Blo 1474557 1475151 := bstep (se 1 (by rfl) ⟨1106363, by rfl⟩ : syracuseStep 1475151 = 2212727) B2212727
theorem B2490959 : Blo 1474557 2490959 := bstep (se 1 (by rfl) ⟨1868219, by rfl⟩ : syracuseStep 2490959 = 3736439) B3736439
theorem B1475167 : Blo 1474557 1475167 := bstep (se 1 (by rfl) ⟨1106375, by rfl⟩ : syracuseStep 1475167 = 2212751) B2212751
theorem B2212475 : Blo 1474557 2212475 := bstep (se 1 (by rfl) ⟨1659356, by rfl⟩ : syracuseStep 2212475 = 3318713) B3318713
theorem B1475195 : Blo 1474557 1475195 := bstep (se 1 (by rfl) ⟨1106396, by rfl⟩ : syracuseStep 1475195 = 2212793) B2212793
theorem B5603975 : Blo 1474557 5603975 := bstep (se 1 (by rfl) ⟨4202981, by rfl⟩ : syracuseStep 5603975 = 8405963) B8405963
theorem B1475247 : Blo 1474557 1475247 := bstep (se 1 (by rfl) ⟨1106435, by rfl⟩ : syracuseStep 1475247 = 2212871) B2212871
theorem B1475271 : Blo 1474557 1475271 := bstep (se 1 (by rfl) ⟨1106453, by rfl⟩ : syracuseStep 1475271 = 2212907) B2212907
theorem B1475291 : Blo 1474557 1475291 := bstep (se 1 (by rfl) ⟨1106468, by rfl⟩ : syracuseStep 1475291 = 2212937) B2212937
theorem B2212601 : Blo 1474557 2212601 := bstep (se 2 (by rfl) ⟨829725, by rfl⟩ : syracuseStep 2212601 = 1659451) B1659451
theorem B1475367 : Blo 1474557 1475367 := bstep (se 1 (by rfl) ⟨1106525, by rfl⟩ : syracuseStep 1475367 = 2213051) B2213051
theorem B1475407 : Blo 1474557 1475407 := bstep (se 1 (by rfl) ⟨1106555, by rfl⟩ : syracuseStep 1475407 = 2213111) B2213111
theorem B3318623 : Blo 1474557 3318623 := bstep (se 1 (by rfl) ⟨2488967, by rfl⟩ : syracuseStep 3318623 = 4977935) B4977935
theorem B2212703 : Blo 1474557 2212703 := bstep (se 1 (by rfl) ⟨1659527, by rfl⟩ : syracuseStep 2212703 = 3319055) B3319055
theorem B1475423 : Blo 1474557 1475423 := bstep (se 1 (by rfl) ⟨1106567, by rfl⟩ : syracuseStep 1475423 = 2213135) B2213135
theorem B2212715 : Blo 1474557 2212715 := bstep (se 1 (by rfl) ⟨1659536, by rfl⟩ : syracuseStep 2212715 = 3319073) B3319073
theorem B1475451 : Blo 1474557 1475451 := bstep (se 1 (by rfl) ⟨1106588, by rfl⟩ : syracuseStep 1475451 = 2213177) B2213177
theorem B1475503 : Blo 1474557 1475503 := bstep (se 1 (by rfl) ⟨1106627, by rfl⟩ : syracuseStep 1475503 = 2213255) B2213255
theorem B1475527 : Blo 1474557 1475527 := bstep (se 1 (by rfl) ⟨1106645, by rfl⟩ : syracuseStep 1475527 = 2213291) B2213291
theorem B1475547 : Blo 1474557 1475547 := bstep (se 1 (by rfl) ⟨1106660, by rfl⟩ : syracuseStep 1475547 = 2213321) B2213321
theorem B11207645 : Blo 1474557 11207645 := bstep (se 3 (by rfl) ⟨2101433, by rfl⟩ : syracuseStep 11207645 = 4202867) B4202867
theorem B3318803 : Blo 1474557 3318803 := bstep (se 1 (by rfl) ⟨2489102, by rfl⟩ : syracuseStep 3318803 = 4978205) B4978205
theorem B1475623 : Blo 1474557 1475623 := bstep (se 1 (by rfl) ⟨1106717, by rfl⟩ : syracuseStep 1475623 = 2213435) B2213435
theorem B2212943 : Blo 1474557 2212943 := bstep (se 1 (by rfl) ⟨1659707, by rfl⟩ : syracuseStep 2212943 = 3319415) B3319415
theorem B1475663 : Blo 1474557 1475663 := bstep (se 1 (by rfl) ⟨1106747, by rfl⟩ : syracuseStep 1475663 = 2213495) B2213495
theorem B1475679 : Blo 1474557 1475679 := bstep (se 1 (by rfl) ⟨1106759, by rfl⟩ : syracuseStep 1475679 = 2213519) B2213519
theorem B1475707 : Blo 1474557 1475707 := bstep (se 1 (by rfl) ⟨1106780, by rfl⟩ : syracuseStep 1475707 = 2213561) B2213561
theorem B4203677 : Blo 1474557 4203677 := bstep (se 3 (by rfl) ⟨788189, by rfl⟩ : syracuseStep 4203677 = 1576379) B1576379
theorem B4981931 : Blo 1474557 4981931 := bstep (se 1 (by rfl) ⟨3736448, by rfl⟩ : syracuseStep 4981931 = 7472897) B7472897
theorem B1475759 : Blo 1474557 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B2213063 : Blo 1474557 2213063 := bstep (se 1 (by rfl) ⟨1659797, by rfl⟩ : syracuseStep 2213063 = 3319595) B3319595
theorem B1475783 : Blo 1474557 1475783 := bstep (se 1 (by rfl) ⟨1106837, by rfl⟩ : syracuseStep 1475783 = 2213675) B2213675
theorem B2802899 : Blo 1474557 2802899 := bstep (se 1 (by rfl) ⟨2102174, by rfl⟩ : syracuseStep 2802899 = 4204349) B4204349
theorem B1475803 : Blo 1474557 1475803 := bstep (se 1 (by rfl) ⟨1106852, by rfl⟩ : syracuseStep 1475803 = 2213705) B2213705
theorem B2802937 : Blo 1474557 2802937 := bstep (se 2 (by rfl) ⟨1051101, by rfl⟩ : syracuseStep 2802937 = 2102203) B2102203
theorem B1475879 : Blo 1474557 1475879 := bstep (se 1 (by rfl) ⟨1106909, by rfl⟩ : syracuseStep 1475879 = 2213819) B2213819
theorem B1475919 : Blo 1474557 1475919 := bstep (se 1 (by rfl) ⟨1106939, by rfl⟩ : syracuseStep 1475919 = 2213879) B2213879
theorem B1475935 : Blo 1474557 1475935 := bstep (se 1 (by rfl) ⟨1106951, by rfl⟩ : syracuseStep 1475935 = 2213903) B2213903
theorem B3319145 : Blo 1474557 3319145 := bstep (se 2 (by rfl) ⟨1244679, by rfl⟩ : syracuseStep 3319145 = 2489359) B2489359
theorem B2213225 : Blo 1474557 2213225 := bstep (se 2 (by rfl) ⟨829959, by rfl⟩ : syracuseStep 2213225 = 1659919) B1659919
theorem B11199869 : Blo 1474557 11199869 := bstep (se 3 (by rfl) ⟨2099975, by rfl⟩ : syracuseStep 11199869 = 4199951) B4199951
theorem B1475963 : Blo 1474557 1475963 := bstep (se 1 (by rfl) ⟨1106972, by rfl⟩ : syracuseStep 1475963 = 2213945) B2213945
theorem B3736975 : Blo 1474557 3736975 := bstep (se 1 (by rfl) ⟨2802731, by rfl⟩ : syracuseStep 3736975 = 5605463) B5605463
theorem B1476015 : Blo 1474557 1476015 := bstep (se 1 (by rfl) ⟨1107011, by rfl⟩ : syracuseStep 1476015 = 2214023) B2214023
theorem B2213303 : Blo 1474557 2213303 := bstep (se 1 (by rfl) ⟨1659977, by rfl⟩ : syracuseStep 2213303 = 3319955) B3319955
theorem B1476039 : Blo 1474557 1476039 := bstep (se 1 (by rfl) ⟨1107029, by rfl⟩ : syracuseStep 1476039 = 2214059) B2214059
theorem B2213339 : Blo 1474557 2213339 := bstep (se 1 (by rfl) ⟨1660004, by rfl⟩ : syracuseStep 2213339 = 3320009) B3320009
theorem B1476059 : Blo 1474557 1476059 := bstep (se 1 (by rfl) ⟨1107044, by rfl⟩ : syracuseStep 1476059 = 2214089) B2214089
theorem B1476135 : Blo 1474557 1476135 := bstep (se 1 (by rfl) ⟨1107101, by rfl⟩ : syracuseStep 1476135 = 2214203) B2214203
theorem B1476175 : Blo 1474557 1476175 := bstep (se 1 (by rfl) ⟨1107131, by rfl⟩ : syracuseStep 1476175 = 2214263) B2214263
theorem B1476191 : Blo 1474557 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B1476219 : Blo 1474557 1476219 := bstep (se 1 (by rfl) ⟨1107164, by rfl⟩ : syracuseStep 1476219 = 2214329) B2214329
theorem B1476271 : Blo 1474557 1476271 := bstep (se 1 (by rfl) ⟨1107203, by rfl⟩ : syracuseStep 1476271 = 2214407) B2214407
theorem B2524871 : Blo 1474557 2524871 := bstep (se 1 (by rfl) ⟨1893653, by rfl⟩ : syracuseStep 2524871 = 3787307) B3787307
theorem B4982471 : Blo 1474557 4982471 := bstep (se 1 (by rfl) ⟨3736853, by rfl⟩ : syracuseStep 4982471 = 7473707) B7473707
theorem B1476295 : Blo 1474557 1476295 := bstep (se 1 (by rfl) ⟨1107221, by rfl⟩ : syracuseStep 1476295 = 2214443) B2214443
theorem B3737299 : Blo 1474557 3737299 := bstep (se 1 (by rfl) ⟨2802974, by rfl⟩ : syracuseStep 3737299 = 5605949) B5605949
theorem B1476315 : Blo 1474557 1476315 := bstep (se 1 (by rfl) ⟨1107236, by rfl⟩ : syracuseStep 1476315 = 2214473) B2214473
theorem B21260069 : Blo 1474557 21260069 := bstep (se 4 (by rfl) ⟨1993131, by rfl⟩ : syracuseStep 21260069 = 3986263) B3986263
theorem B1476391 : Blo 1474557 1476391 := bstep (se 1 (by rfl) ⟨1107293, by rfl⟩ : syracuseStep 1476391 = 2214587) B2214587
theorem B1476431 : Blo 1474557 1476431 := bstep (se 1 (by rfl) ⟨1107323, by rfl⟩ : syracuseStep 1476431 = 2214647) B2214647
theorem B1476447 : Blo 1474557 1476447 := bstep (se 1 (by rfl) ⟨1107335, by rfl⟩ : syracuseStep 1476447 = 2214671) B2214671
theorem B12126061 : Blo 1474557 12126061 := bstep (se 3 (by rfl) ⟨2273636, by rfl⟩ : syracuseStep 12126061 = 4547273) B4547273
theorem B1476475 : Blo 1474557 1476475 := bstep (se 1 (by rfl) ⟨1107356, by rfl⟩ : syracuseStep 1476475 = 2214713) B2214713
theorem B7088033 : Blo 1474557 7088033 := bstep (se 2 (by rfl) ⟨2658012, by rfl⟩ : syracuseStep 7088033 = 5316025) B5316025
theorem B2213807 : Blo 1474557 2213807 := bstep (se 1 (by rfl) ⟨1660355, by rfl⟩ : syracuseStep 2213807 = 3320711) B3320711
theorem B1476527 : Blo 1474557 1476527 := bstep (se 1 (by rfl) ⟨1107395, by rfl⟩ : syracuseStep 1476527 = 2214791) B2214791
theorem B3319739 : Blo 1474557 3319739 := bstep (se 1 (by rfl) ⟨2489804, by rfl⟩ : syracuseStep 3319739 = 4979609) B4979609
theorem B1476551 : Blo 1474557 1476551 := bstep (se 1 (by rfl) ⟨1107413, by rfl⟩ : syracuseStep 1476551 = 2214827) B2214827
theorem B2213897 : Blo 1474557 2213897 := bstep (se 2 (by rfl) ⟨830211, by rfl⟩ : syracuseStep 2213897 = 1660423) B1660423
theorem B2213927 : Blo 1474557 2213927 := bstep (se 1 (by rfl) ⟨1660445, by rfl⟩ : syracuseStep 2213927 = 3320891) B3320891
theorem B3319865 : Blo 1474557 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B5605433 : Blo 1474557 5605433 := bstep (se 2 (by rfl) ⟨2102037, by rfl⟩ : syracuseStep 5605433 = 4204075) B4204075
theorem B2214011 : Blo 1474557 2214011 := bstep (se 1 (by rfl) ⟨1660508, by rfl⟩ : syracuseStep 2214011 = 3321017) B3321017
theorem B2525383 : Blo 1474557 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B2214137 : Blo 1474557 2214137 := bstep (se 2 (by rfl) ⟨830301, by rfl⟩ : syracuseStep 2214137 = 1660603) B1660603
theorem B11520305 : Blo 1474557 11520305 := bstep (se 2 (by rfl) ⟨4320114, by rfl⟩ : syracuseStep 11520305 = 8640229) B8640229
theorem B4729175 : Blo 1474557 4729175 := bstep (se 1 (by rfl) ⟨3546881, by rfl⟩ : syracuseStep 4729175 = 7093763) B7093763
theorem B2214239 : Blo 1474557 2214239 := bstep (se 1 (by rfl) ⟨1660679, by rfl⟩ : syracuseStep 2214239 = 3321359) B3321359
theorem B2214251 : Blo 1474557 2214251 := bstep (se 1 (by rfl) ⟨1660688, by rfl⟩ : syracuseStep 2214251 = 3321377) B3321377
theorem B3320207 : Blo 1474557 3320207 := bstep (se 1 (by rfl) ⟨2490155, by rfl⟩ : syracuseStep 3320207 = 4980311) B4980311
theorem B42551729 : Blo 1474557 42551729 := bstep (se 2 (by rfl) ⟨15956898, by rfl⟩ : syracuseStep 42551729 = 31913797) B31913797
theorem B4983335 : Blo 1474557 4983335 := bstep (se 1 (by rfl) ⟨3737501, by rfl⟩ : syracuseStep 4983335 = 7475003) B7475003
theorem B2214479 : Blo 1474557 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B7465607 : Blo 1474557 7465607 := bstep (se 1 (by rfl) ⟨5599205, by rfl⟩ : syracuseStep 7465607 = 11198411) B11198411
theorem B2214599 : Blo 1474557 2214599 := bstep (se 1 (by rfl) ⟨1660949, by rfl⟩ : syracuseStep 2214599 = 3321899) B3321899
theorem B3320531 : Blo 1474557 3320531 := bstep (se 1 (by rfl) ⟨2490398, by rfl⟩ : syracuseStep 3320531 = 4980797) B4980797
theorem B2214761 : Blo 1474557 2214761 := bstep (se 2 (by rfl) ⟨830535, by rfl⟩ : syracuseStep 2214761 = 1661071) B1661071
theorem B16804907 : Blo 1474557 16804907 := bstep (se 1 (by rfl) ⟨12603680, by rfl⟩ : syracuseStep 16804907 = 25207361) B25207361
theorem B2993249 : Blo 1474557 2993249 := bstep (se 2 (by rfl) ⟨1122468, by rfl⟩ : syracuseStep 2993249 = 2244937) B2244937
theorem B8080555 : Blo 1474557 8080555 := bstep (se 1 (by rfl) ⟨6060416, by rfl⟩ : syracuseStep 8080555 = 12120833) B12120833
theorem B11971955 : Blo 1474557 11971955 := bstep (se 1 (by rfl) ⟨8978966, by rfl⟩ : syracuseStep 11971955 = 17957933) B17957933
theorem B11357603 : Blo 1474557 11357603 := bstep (se 1 (by rfl) ⟨8518202, by rfl⟩ : syracuseStep 11357603 = 17036405) B17036405
theorem B1994159 : Blo 1474557 1994159 := bstep (se 1 (by rfl) ⟨1495619, by rfl⟩ : syracuseStep 1994159 = 2991239) B2991239
theorem B2100745 : Blo 1474557 2100745 := bstep (se 2 (by rfl) ⟨787779, by rfl⟩ : syracuseStep 2100745 = 1575559) B1575559
theorem B5680649 : Blo 1474557 5680649 := bstep (se 2 (by rfl) ⟨2130243, by rfl⟩ : syracuseStep 5680649 = 4260487) B4260487
theorem B1773095 : Blo 1474557 1773095 := bstep (se 1 (by rfl) ⟨1329821, by rfl⟩ : syracuseStep 1773095 = 2659643) B2659643
theorem B16813655 : Blo 1474557 16813655 := bstep (se 1 (by rfl) ⟨12610241, by rfl⟩ : syracuseStep 16813655 = 25220483) B25220483
theorem B6303329 : Blo 1474557 6303329 := bstep (se 2 (by rfl) ⟨2363748, by rfl⟩ : syracuseStep 6303329 = 4727497) B4727497
theorem B3149435 : Blo 1474557 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B3321467 : Blo 1474557 3321467 := bstep (se 1 (by rfl) ⟨2491100, by rfl⟩ : syracuseStep 3321467 = 4982201) B4982201
theorem B18910853 : Blo 1474557 18910853 := bstep (se 4 (by rfl) ⟨1772892, by rfl⟩ : syracuseStep 18910853 = 3545785) B3545785
theorem B6303379 : Blo 1474557 6303379 := bstep (se 1 (by rfl) ⟨4727534, by rfl⟩ : syracuseStep 6303379 = 9455069) B9455069
theorem B3321593 : Blo 1474557 3321593 := bstep (se 2 (by rfl) ⟨1245597, by rfl⟩ : syracuseStep 3321593 = 2491195) B2491195
theorem B96964487 : Blo 1474557 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B26922887 : Blo 1474557 26922887 := bstep (se 1 (by rfl) ⟨20192165, by rfl⟩ : syracuseStep 26922887 = 40384331) B40384331
theorem B15945659 : Blo 1474557 15945659 := bstep (se 1 (by rfl) ⟨11959244, by rfl⟩ : syracuseStep 15945659 = 23918489) B23918489
theorem B3321863 : Blo 1474557 3321863 := bstep (se 1 (by rfl) ⟨2491397, by rfl⟩ : syracuseStep 3321863 = 4982795) B4982795
theorem B13463567 : Blo 1474557 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B7467065 : Blo 1474557 7467065 := bstep (se 2 (by rfl) ⟨2800149, by rfl⟩ : syracuseStep 7467065 = 5600299) B5600299
theorem B3321935 : Blo 1474557 3321935 := bstep (se 1 (by rfl) ⟨2491451, by rfl⟩ : syracuseStep 3321935 = 4982903) B4982903
theorem B5599313 : Blo 1474557 5599313 := bstep (se 2 (by rfl) ⟨2099742, by rfl⟩ : syracuseStep 5599313 = 4199485) B4199485
theorem B5599631 : Blo 1474557 5599631 := bstep (se 1 (by rfl) ⟨4199723, by rfl⟩ : syracuseStep 5599631 = 8399447) B8399447
theorem B4977287 : Blo 1474557 4977287 := bstep (se 1 (by rfl) ⟨3732965, by rfl⟩ : syracuseStep 4977287 = 7465931) B7465931
theorem B4977341 : Blo 1474557 4977341 := bstep (se 3 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 4977341 = 1866503) B1866503
theorem B40399667 : Blo 1474557 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B18903881 : Blo 1474557 18903881 := bstep (se 2 (by rfl) ⟨7088955, by rfl⟩ : syracuseStep 18903881 = 14177911) B14177911
theorem B4977503 : Blo 1474557 4977503 := bstep (se 1 (by rfl) ⟨3733127, by rfl⟩ : syracuseStep 4977503 = 7466255) B7466255
theorem B4977665 : Blo 1474557 4977665 := bstep (se 2 (by rfl) ⟨1866624, by rfl⟩ : syracuseStep 4977665 = 3733249) B3733249
theorem B9458707 : Blo 1474557 9458707 := bstep (se 1 (by rfl) ⟨7094030, by rfl⟩ : syracuseStep 9458707 = 14188061) B14188061
theorem B2102311 : Blo 1474557 2102311 := bstep (se 1 (by rfl) ⟨1576733, by rfl⟩ : syracuseStep 2102311 = 3153467) B3153467
theorem B1660027 : Blo 1474557 1660027 := bstep (se 1 (by rfl) ⟨1245020, by rfl⟩ : syracuseStep 1660027 = 2490041) B2490041
theorem B5600573 : Blo 1474557 5600573 := bstep (se 3 (by rfl) ⟨1050107, by rfl⟩ : syracuseStep 5600573 = 2100215) B2100215
theorem B109122947 : Blo 1474557 109122947 := bstep (se 1 (by rfl) ⟨81842210, by rfl⟩ : syracuseStep 109122947 = 163684421) B163684421
theorem B9450917 : Blo 1474557 9450917 := bstep (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) B1772047
theorem B40359377 : Blo 1474557 40359377 := bstep (se 2 (by rfl) ⟨15134766, by rfl⟩ : syracuseStep 40359377 = 30269533) B30269533
theorem B2840071 : Blo 1474557 2840071 := bstep (se 1 (by rfl) ⟨2130053, by rfl⟩ : syracuseStep 2840071 = 4260107) B4260107
theorem B3593737 : Blo 1474557 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B9451019 : Blo 1474557 9451019 := bstep (se 1 (by rfl) ⟨7088264, by rfl⟩ : syracuseStep 9451019 = 14176529) B14176529
theorem B4199975 : Blo 1474557 4199975 := bstep (se 1 (by rfl) ⟨3149981, by rfl⟩ : syracuseStep 4199975 = 6299963) B6299963
theorem B3151399 : Blo 1474557 3151399 := bstep (se 1 (by rfl) ⟨2363549, by rfl⟩ : syracuseStep 3151399 = 4727099) B4727099
theorem B1660495 : Blo 1474557 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B10638971 : Blo 1474557 10638971 := bstep (se 1 (by rfl) ⟨7979228, by rfl⟩ : syracuseStep 10638971 = 15958457) B15958457
theorem B11204243 : Blo 1474557 11204243 := bstep (se 1 (by rfl) ⟨8403182, by rfl⟩ : syracuseStep 11204243 = 16806365) B16806365
theorem B12613319 : Blo 1474557 12613319 := bstep (se 1 (by rfl) ⟨9459989, by rfl⟩ : syracuseStep 12613319 = 18919979) B18919979
theorem B10630871 : Blo 1474557 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B4978475 : Blo 1474557 4978475 := bstep (se 1 (by rfl) ⟨3733856, by rfl⟩ : syracuseStep 4978475 = 7467713) B7467713
theorem B2799535 : Blo 1474557 2799535 := bstep (se 1 (by rfl) ⟨2099651, by rfl⟩ : syracuseStep 2799535 = 4199303) B4199303
theorem B1660891 : Blo 1474557 1660891 := bstep (se 1 (by rfl) ⟨1245668, by rfl⟩ : syracuseStep 1660891 = 2491337) B2491337
theorem B3733523 : Blo 1474557 3733523 := bstep (se 1 (by rfl) ⟨2800142, by rfl⟩ : syracuseStep 3733523 = 5600285) B5600285
theorem B4978745 : Blo 1474557 4978745 := bstep (se 2 (by rfl) ⟨1867029, by rfl⟩ : syracuseStep 4978745 = 3734059) B3734059
theorem B7469171 : Blo 1474557 7469171 := bstep (se 1 (by rfl) ⟨5601878, by rfl⟩ : syracuseStep 7469171 = 11203757) B11203757
theorem B4257949 : Blo 1474557 4257949 := bstep (se 3 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 4257949 = 1596731) B1596731
theorem B4044971 : Blo 1474557 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B21272813 : Blo 1474557 21272813 := bstep (se 3 (by rfl) ⟨3988652, by rfl⟩ : syracuseStep 21272813 = 7977305) B7977305
theorem B4979069 : Blo 1474557 4979069 := bstep (se 3 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 4979069 = 1867151) B1867151
theorem B4790657 : Blo 1474557 4790657 := bstep (se 2 (by rfl) ⟨1796496, by rfl⟩ : syracuseStep 4790657 = 3592993) B3592993
theorem B3987841 : Blo 1474557 3987841 := bstep (se 2 (by rfl) ⟨1495440, by rfl⟩ : syracuseStep 3987841 = 2990881) B2990881
theorem B4979339 : Blo 1474557 4979339 := bstep (se 1 (by rfl) ⟨3734504, by rfl⟩ : syracuseStep 4979339 = 7469009) B7469009
theorem B4201159 : Blo 1474557 4201159 := bstep (se 1 (by rfl) ⟨3150869, by rfl⟩ : syracuseStep 4201159 = 6301739) B6301739
theorem B5315321 : Blo 1474557 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B5978909 : Blo 1474557 5978909 := bstep (se 3 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 5978909 = 2242091) B2242091
theorem B18905885 : Blo 1474557 18905885 := bstep (se 3 (by rfl) ⟨3544853, by rfl⟩ : syracuseStep 18905885 = 7089707) B7089707
theorem B21281629 : Blo 1474557 21281629 := bstep (se 3 (by rfl) ⟨3990305, by rfl⟩ : syracuseStep 21281629 = 7980611) B7980611
theorem B5045087 : Blo 1474557 5045087 := bstep (se 1 (by rfl) ⟨3783815, by rfl⟩ : syracuseStep 5045087 = 7567631) B7567631
theorem B2489231 : Blo 1474557 2489231 := bstep (se 1 (by rfl) ⟨1866923, by rfl⟩ : syracuseStep 2489231 = 3733847) B3733847
theorem B2243623 : Blo 1474557 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B15957071 : Blo 1474557 15957071 := bstep (se 1 (by rfl) ⟨11967803, by rfl⟩ : syracuseStep 15957071 = 23935607) B23935607
theorem B2489467 : Blo 1474557 2489467 := bstep (se 1 (by rfl) ⟨1867100, by rfl⟩ : syracuseStep 2489467 = 3734201) B3734201
theorem B6732953 : Blo 1474557 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B2800811 : Blo 1474557 2800811 := bstep (se 1 (by rfl) ⟨2100608, by rfl⟩ : syracuseStep 2800811 = 4201217) B4201217
theorem B6299005 : Blo 1474557 6299005 := bstep (se 3 (by rfl) ⟨1181063, by rfl⟩ : syracuseStep 6299005 = 2362127) B2362127
theorem B2989487 : Blo 1474557 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B147578291 : Blo 1474557 147578291 := bstep (se 1 (by rfl) ⟨110683718, by rfl⟩ : syracuseStep 147578291 = 221367437) B221367437
theorem B4980257 : Blo 1474557 4980257 := bstep (se 2 (by rfl) ⟨1867596, by rfl⟩ : syracuseStep 4980257 = 3735193) B3735193
theorem B1867303 : Blo 1474557 1867303 := bstep (se 1 (by rfl) ⟨1400477, by rfl⟩ : syracuseStep 1867303 = 2800955) B2800955
theorem B10231393 : Blo 1474557 10231393 := bstep (se 2 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 10231393 = 7673545) B7673545
theorem B7470791 : Blo 1474557 7470791 := bstep (se 1 (by rfl) ⟨5603093, by rfl⟩ : syracuseStep 7470791 = 11206187) B11206187
theorem B4980473 : Blo 1474557 4980473 := bstep (se 2 (by rfl) ⟨1867677, by rfl⟩ : syracuseStep 4980473 = 3735355) B3735355
theorem B1867627 : Blo 1474557 1867627 := bstep (se 1 (by rfl) ⟨1400720, by rfl⟩ : syracuseStep 1867627 = 2801441) B2801441
theorem B17956727 : Blo 1474557 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B4202401 : Blo 1474557 4202401 := bstep (se 2 (by rfl) ⟨1575900, by rfl⟩ : syracuseStep 4202401 = 3151801) B3151801
theorem B7086017 : Blo 1474557 7086017 := bstep (se 2 (by rfl) ⟨2657256, by rfl⟩ : syracuseStep 7086017 = 5314513) B5314513
theorem B2490331 : Blo 1474557 2490331 := bstep (se 1 (by rfl) ⟨1867748, by rfl⟩ : syracuseStep 2490331 = 3735497) B3735497
theorem B2490473 : Blo 1474557 2490473 := bstep (se 2 (by rfl) ⟨933927, by rfl⟩ : syracuseStep 2490473 = 1867855) B1867855
theorem B5677265 : Blo 1474557 5677265 := bstep (se 2 (by rfl) ⟨2128974, by rfl⟩ : syracuseStep 5677265 = 4257949) B4257949
theorem B3367177 : Blo 1474557 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B1474847 : Blo 1474557 1474847 := bstep (se 1 (by rfl) ⟨1106135, by rfl⟩ : syracuseStep 1474847 = 2212271) B2212271
theorem B2212187 : Blo 1474557 2212187 := bstep (se 1 (by rfl) ⟨1659140, by rfl⟩ : syracuseStep 2212187 = 3318281) B3318281
theorem B1474907 : Blo 1474557 1474907 := bstep (se 1 (by rfl) ⟨1106180, by rfl⟩ : syracuseStep 1474907 = 2212361) B2212361
theorem B3031387 : Blo 1474557 3031387 := bstep (se 1 (by rfl) ⟨2273540, by rfl⟩ : syracuseStep 3031387 = 4547081) B4547081
theorem B1868123 : Blo 1474557 1868123 := bstep (se 1 (by rfl) ⟨1401092, by rfl⟩ : syracuseStep 1868123 = 2802185) B2802185
theorem B1474927 : Blo 1474557 1474927 := bstep (se 1 (by rfl) ⟨1106195, by rfl⟩ : syracuseStep 1474927 = 2212391) B2212391
theorem B1474983 : Blo 1474557 1474983 := bstep (se 1 (by rfl) ⟨1106237, by rfl⟩ : syracuseStep 1474983 = 2212475) B2212475
theorem B3318191 : Blo 1474557 3318191 := bstep (se 1 (by rfl) ⟨2488643, by rfl⟩ : syracuseStep 3318191 = 4977287) B4977287
theorem B3318227 : Blo 1474557 3318227 := bstep (se 1 (by rfl) ⟨2488670, by rfl⟩ : syracuseStep 3318227 = 4977341) B4977341
theorem B1475067 : Blo 1474557 1475067 := bstep (se 1 (by rfl) ⟨1106300, by rfl⟩ : syracuseStep 1475067 = 2212601) B2212601
theorem B5317121 : Blo 1474557 5317121 := bstep (se 2 (by rfl) ⟨1993920, by rfl⟩ : syracuseStep 5317121 = 3987841) B3987841
theorem B3318335 : Blo 1474557 3318335 := bstep (se 1 (by rfl) ⟨2488751, by rfl⟩ : syracuseStep 3318335 = 4977503) B4977503
theorem B2212415 : Blo 1474557 2212415 := bstep (se 1 (by rfl) ⟨1659311, by rfl⟩ : syracuseStep 2212415 = 3318623) B3318623
theorem B1475135 : Blo 1474557 1475135 := bstep (se 1 (by rfl) ⟨1106351, by rfl⟩ : syracuseStep 1475135 = 2212703) B2212703
theorem B1475143 : Blo 1474557 1475143 := bstep (se 1 (by rfl) ⟨1106357, by rfl⟩ : syracuseStep 1475143 = 2212715) B2212715
theorem B7471763 : Blo 1474557 7471763 := bstep (se 1 (by rfl) ⟨5603822, by rfl⟩ : syracuseStep 7471763 = 11207645) B11207645
theorem B3318443 : Blo 1474557 3318443 := bstep (se 1 (by rfl) ⟨2488832, by rfl⟩ : syracuseStep 3318443 = 4977665) B4977665
theorem B2212535 : Blo 1474557 2212535 := bstep (se 1 (by rfl) ⟨1659401, by rfl⟩ : syracuseStep 2212535 = 3318803) B3318803
theorem B1475295 : Blo 1474557 1475295 := bstep (se 1 (by rfl) ⟨1106471, by rfl⟩ : syracuseStep 1475295 = 2212943) B2212943
theorem B2802451 : Blo 1474557 2802451 := bstep (se 1 (by rfl) ⟨2101838, by rfl⟩ : syracuseStep 2802451 = 4203677) B4203677
theorem B1475375 : Blo 1474557 1475375 := bstep (se 1 (by rfl) ⟨1106531, by rfl⟩ : syracuseStep 1475375 = 2213063) B2213063
theorem B1868599 : Blo 1474557 1868599 := bstep (se 1 (by rfl) ⟨1401449, by rfl⟩ : syracuseStep 1868599 = 2802899) B2802899
theorem B2212763 : Blo 1474557 2212763 := bstep (se 1 (by rfl) ⟨1659572, by rfl⟩ : syracuseStep 2212763 = 3319145) B3319145
theorem B1475483 : Blo 1474557 1475483 := bstep (se 1 (by rfl) ⟨1106612, by rfl⟩ : syracuseStep 1475483 = 2213225) B2213225
theorem B6300611 : Blo 1474557 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B1475535 : Blo 1474557 1475535 := bstep (se 1 (by rfl) ⟨1106651, by rfl⟩ : syracuseStep 1475535 = 2213303) B2213303
theorem B1475559 : Blo 1474557 1475559 := bstep (se 1 (by rfl) ⟨1106669, by rfl⟩ : syracuseStep 1475559 = 2213339) B2213339
theorem B6300679 : Blo 1474557 6300679 := bstep (se 1 (by rfl) ⟨4725509, by rfl⟩ : syracuseStep 6300679 = 9451019) B9451019
theorem B7971965 : Blo 1474557 7971965 := bstep (se 3 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 7971965 = 2989487) B2989487
theorem B5317757 : Blo 1474557 5317757 := bstep (se 3 (by rfl) ⟨997079, by rfl⟩ : syracuseStep 5317757 = 1994159) B1994159
theorem B7087247 : Blo 1474557 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B14173379 : Blo 1474557 14173379 := bstep (se 1 (by rfl) ⟨10630034, by rfl⟩ : syracuseStep 14173379 = 21260069) B21260069
theorem B3318983 : Blo 1474557 3318983 := bstep (se 1 (by rfl) ⟨2489237, by rfl⟩ : syracuseStep 3318983 = 4978475) B4978475
theorem B1475871 : Blo 1474557 1475871 := bstep (se 1 (by rfl) ⟨1106903, by rfl⟩ : syracuseStep 1475871 = 2213807) B2213807
theorem B2213159 : Blo 1474557 2213159 := bstep (se 1 (by rfl) ⟨1659869, by rfl⟩ : syracuseStep 2213159 = 3319739) B3319739
theorem B1475931 : Blo 1474557 1475931 := bstep (se 1 (by rfl) ⟨1106948, by rfl⟩ : syracuseStep 1475931 = 2213897) B2213897
theorem B15148397 : Blo 1474557 15148397 := bstep (se 3 (by rfl) ⟨2840324, by rfl⟩ : syracuseStep 15148397 = 5680649) B5680649
theorem B1475951 : Blo 1474557 1475951 := bstep (se 1 (by rfl) ⟨1106963, by rfl⟩ : syracuseStep 1475951 = 2213927) B2213927
theorem B3319163 : Blo 1474557 3319163 := bstep (se 1 (by rfl) ⟨2489372, by rfl⟩ : syracuseStep 3319163 = 4978745) B4978745
theorem B2213243 : Blo 1474557 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B3736955 : Blo 1474557 3736955 := bstep (se 1 (by rfl) ⟨2802716, by rfl⟩ : syracuseStep 3736955 = 5605433) B5605433
theorem B2991497 : Blo 1474557 2991497 := bstep (se 2 (by rfl) ⟨1121811, by rfl⟩ : syracuseStep 2991497 = 2243623) B2243623
theorem B2803081 : Blo 1474557 2803081 := bstep (se 2 (by rfl) ⟨1051155, by rfl⟩ : syracuseStep 2803081 = 2102311) B2102311
theorem B1476007 : Blo 1474557 1476007 := bstep (se 1 (by rfl) ⟨1107005, by rfl⟩ : syracuseStep 1476007 = 2214011) B2214011
theorem B4728253 : Blo 1474557 4728253 := bstep (se 3 (by rfl) ⟨886547, by rfl⟩ : syracuseStep 4728253 = 1773095) B1773095
theorem B7472573 : Blo 1474557 7472573 := bstep (se 3 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 7472573 = 2802215) B2802215
theorem B2696647 : Blo 1474557 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B14181875 : Blo 1474557 14181875 := bstep (se 1 (by rfl) ⟨10636406, by rfl⟩ : syracuseStep 14181875 = 21272813) B21272813
theorem B3319289 : Blo 1474557 3319289 := bstep (se 2 (by rfl) ⟨1244733, by rfl⟩ : syracuseStep 3319289 = 2489467) B2489467
theorem B2213369 : Blo 1474557 2213369 := bstep (se 2 (by rfl) ⟨830013, by rfl⟩ : syracuseStep 2213369 = 1660027) B1660027
theorem B1476091 : Blo 1474557 1476091 := bstep (se 1 (by rfl) ⟨1107068, by rfl⟩ : syracuseStep 1476091 = 2214137) B2214137
theorem B10774073 : Blo 1474557 10774073 := bstep (se 2 (by rfl) ⟨4040277, by rfl⟩ : syracuseStep 10774073 = 8080555) B8080555
theorem B1476159 : Blo 1474557 1476159 := bstep (se 1 (by rfl) ⟨1107119, by rfl⟩ : syracuseStep 1476159 = 2214239) B2214239
theorem B1476167 : Blo 1474557 1476167 := bstep (se 1 (by rfl) ⟨1107125, by rfl⟩ : syracuseStep 1476167 = 2214251) B2214251
theorem B3319379 : Blo 1474557 3319379 := bstep (se 1 (by rfl) ⟨2489534, by rfl⟩ : syracuseStep 3319379 = 4979069) B4979069
theorem B2213471 : Blo 1474557 2213471 := bstep (se 1 (by rfl) ⟨1660103, by rfl⟩ : syracuseStep 2213471 = 3320207) B3320207
theorem B3737249 : Blo 1474557 3737249 := bstep (se 2 (by rfl) ⟨1401468, by rfl⟩ : syracuseStep 3737249 = 2802937) B2802937
theorem B1476319 : Blo 1474557 1476319 := bstep (se 1 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 1476319 = 2214479) B2214479
theorem B3319559 : Blo 1474557 3319559 := bstep (se 1 (by rfl) ⟨2489669, by rfl⟩ : syracuseStep 3319559 = 4979339) B4979339
theorem B1476399 : Blo 1474557 1476399 := bstep (se 1 (by rfl) ⟨1107299, by rfl⟩ : syracuseStep 1476399 = 2214599) B2214599
theorem B2213687 : Blo 1474557 2213687 := bstep (se 1 (by rfl) ⟨1660265, by rfl⟩ : syracuseStep 2213687 = 3320531) B3320531
theorem B8398673 : Blo 1474557 8398673 := bstep (se 2 (by rfl) ⟨3149502, by rfl⟩ : syracuseStep 8398673 = 6299005) B6299005
theorem B4982633 : Blo 1474557 4982633 := bstep (se 2 (by rfl) ⟨1868487, by rfl⟩ : syracuseStep 4982633 = 3736975) B3736975
theorem B1476507 : Blo 1474557 1476507 := bstep (se 1 (by rfl) ⟨1107380, by rfl⟩ : syracuseStep 1476507 = 2214761) B2214761
theorem B14174189 : Blo 1474557 14174189 := bstep (se 3 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 14174189 = 5315321) B5315321
theorem B3786761 : Blo 1474557 3786761 := bstep (se 2 (by rfl) ⟨1420035, by rfl⟩ : syracuseStep 3786761 = 2840071) B2840071
theorem B2213993 : Blo 1474557 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B13641857 : Blo 1474557 13641857 := bstep (se 2 (by rfl) ⟨5115696, by rfl⟩ : syracuseStep 13641857 = 10231393) B10231393
theorem B7981303 : Blo 1474557 7981303 := bstep (se 1 (by rfl) ⟨5985977, by rfl⟩ : syracuseStep 7981303 = 11971955) B11971955
theorem B7571735 : Blo 1474557 7571735 := bstep (se 1 (by rfl) ⟨5678801, by rfl⟩ : syracuseStep 7571735 = 11357603) B11357603
theorem B4983065 : Blo 1474557 4983065 := bstep (se 2 (by rfl) ⟨1868649, by rfl⟩ : syracuseStep 4983065 = 3737299) B3737299
theorem B3320171 : Blo 1474557 3320171 := bstep (se 1 (by rfl) ⟨2490128, by rfl⟩ : syracuseStep 3320171 = 4980257) B4980257
theorem B11209103 : Blo 1474557 11209103 := bstep (se 1 (by rfl) ⟨8406827, by rfl⟩ : syracuseStep 11209103 = 16813655) B16813655
theorem B2099623 : Blo 1474557 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B2214311 : Blo 1474557 2214311 := bstep (se 1 (by rfl) ⟨1660733, by rfl⟩ : syracuseStep 2214311 = 3321467) B3321467
theorem B18901421 : Blo 1474557 18901421 := bstep (se 3 (by rfl) ⟨3544016, by rfl⟩ : syracuseStep 18901421 = 7088033) B7088033
theorem B3320315 : Blo 1474557 3320315 := bstep (se 1 (by rfl) ⟨2490236, by rfl⟩ : syracuseStep 3320315 = 4980473) B4980473
theorem B2214395 : Blo 1474557 2214395 := bstep (se 1 (by rfl) ⟨1660796, by rfl⟩ : syracuseStep 2214395 = 3321593) B3321593
theorem B11971151 : Blo 1474557 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B3320441 : Blo 1474557 3320441 := bstep (se 2 (by rfl) ⟨1245165, by rfl⟩ : syracuseStep 3320441 = 2490331) B2490331
theorem B2214521 : Blo 1474557 2214521 := bstep (se 2 (by rfl) ⟨830445, by rfl⟩ : syracuseStep 2214521 = 1660891) B1660891
theorem B3320495 : Blo 1474557 3320495 := bstep (se 1 (by rfl) ⟨2490371, by rfl⟩ : syracuseStep 3320495 = 4980743) B4980743
theorem B2214575 : Blo 1474557 2214575 := bstep (se 1 (by rfl) ⟨1660931, by rfl⟩ : syracuseStep 2214575 = 3321863) B3321863
theorem B2214623 : Blo 1474557 2214623 := bstep (se 1 (by rfl) ⟨1660967, by rfl⟩ : syracuseStep 2214623 = 3321935) B3321935
theorem B3320567 : Blo 1474557 3320567 := bstep (se 1 (by rfl) ⟨2490425, by rfl⟩ : syracuseStep 3320567 = 4980851) B4980851
theorem B3320747 : Blo 1474557 3320747 := bstep (se 1 (by rfl) ⟨2490560, by rfl⟩ : syracuseStep 3320747 = 4981121) B4981121
theorem B12602587 : Blo 1474557 12602587 := bstep (se 1 (by rfl) ⟨9451940, by rfl⟩ : syracuseStep 12602587 = 18903881) B18903881
theorem B3321287 : Blo 1474557 3321287 := bstep (se 1 (by rfl) ⟨2490965, by rfl⟩ : syracuseStep 3321287 = 4981931) B4981931
theorem B7466579 : Blo 1474557 7466579 := bstep (se 1 (by rfl) ⟨5599934, by rfl⟩ : syracuseStep 7466579 = 11199869) B11199869
theorem B72748631 : Blo 1474557 72748631 := bstep (se 1 (by rfl) ⟨54561473, by rfl⟩ : syracuseStep 72748631 = 109122947) B109122947
theorem B26906251 : Blo 1474557 26906251 := bstep (se 1 (by rfl) ⟨20179688, by rfl⟩ : syracuseStep 26906251 = 40359377) B40359377
theorem B12775085 : Blo 1474557 12775085 := bstep (se 3 (by rfl) ⟨2395328, by rfl⟩ : syracuseStep 12775085 = 4790657) B4790657
theorem B3321647 : Blo 1474557 3321647 := bstep (se 1 (by rfl) ⟨2491235, by rfl⟩ : syracuseStep 3321647 = 4982471) B4982471
theorem B8408879 : Blo 1474557 8408879 := bstep (se 1 (by rfl) ⟨6306659, by rfl⟩ : syracuseStep 8408879 = 12613319) B12613319
theorem B12611609 : Blo 1474557 12611609 := bstep (se 2 (by rfl) ⟨4729353, by rfl⟩ : syracuseStep 12611609 = 9458707) B9458707
theorem B3735983 : Blo 1474557 3735983 := bstep (se 1 (by rfl) ⟨2801987, by rfl⟩ : syracuseStep 3735983 = 5603975) B5603975
theorem B7680203 : Blo 1474557 7680203 := bstep (se 1 (by rfl) ⟨5760152, by rfl⟩ : syracuseStep 7680203 = 11520305) B11520305
theorem B3322223 : Blo 1474557 3322223 := bstep (se 1 (by rfl) ⟨2491667, by rfl⟩ : syracuseStep 3322223 = 4983335) B4983335
theorem B4977071 : Blo 1474557 4977071 := bstep (se 1 (by rfl) ⟨3732803, by rfl⟩ : syracuseStep 4977071 = 7465607) B7465607
theorem B3985939 : Blo 1474557 3985939 := bstep (se 1 (by rfl) ⟨2989454, by rfl⟩ : syracuseStep 3985939 = 5978909) B5978909
theorem B12603923 : Blo 1474557 12603923 := bstep (se 1 (by rfl) ⟨9452942, by rfl⟩ : syracuseStep 12603923 = 18905885) B18905885
theorem B3363391 : Blo 1474557 3363391 := bstep (se 1 (by rfl) ⟨2522543, by rfl⟩ : syracuseStep 3363391 = 5045087) B5045087
theorem B1659487 : Blo 1474557 1659487 := bstep (se 1 (by rfl) ⟨1244615, by rfl⟩ : syracuseStep 1659487 = 2489231) B2489231
theorem B11203271 : Blo 1474557 11203271 := bstep (se 1 (by rfl) ⟨8402453, by rfl⟩ : syracuseStep 11203271 = 16804907) B16804907
theorem B10638047 : Blo 1474557 10638047 := bstep (se 1 (by rfl) ⟨7978535, by rfl⟩ : syracuseStep 10638047 = 15957071) B15957071
theorem B1995499 : Blo 1474557 1995499 := bstep (se 1 (by rfl) ⟨1496624, by rfl⟩ : syracuseStep 1995499 = 2993249) B2993249
theorem B16168081 : Blo 1474557 16168081 := bstep (se 2 (by rfl) ⟨6063030, by rfl⟩ : syracuseStep 16168081 = 12126061) B12126061
theorem B3732713 : Blo 1474557 3732713 := bstep (se 2 (by rfl) ⟨1399767, by rfl⟩ : syracuseStep 3732713 = 2799535) B2799535
theorem B10630439 : Blo 1474557 10630439 := bstep (se 1 (by rfl) ⟨7972829, by rfl⟩ : syracuseStep 10630439 = 15945659) B15945659
theorem B4724011 : Blo 1474557 4724011 := bstep (se 1 (by rfl) ⟨3543008, by rfl⟩ : syracuseStep 4724011 = 7086017) B7086017
theorem B3986783 : Blo 1474557 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B8975711 : Blo 1474557 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B4978043 : Blo 1474557 4978043 := bstep (se 1 (by rfl) ⟨3733532, by rfl⟩ : syracuseStep 4978043 = 7467065) B7467065
theorem B3732875 : Blo 1474557 3732875 := bstep (se 1 (by rfl) ⟨2799656, by rfl⟩ : syracuseStep 3732875 = 5599313) B5599313
theorem B31905323 : Blo 1474557 31905323 := bstep (se 1 (by rfl) ⟨23928992, by rfl⟩ : syracuseStep 31905323 = 47857985) B47857985
theorem B3733087 : Blo 1474557 3733087 := bstep (se 1 (by rfl) ⟨2799815, by rfl⟩ : syracuseStep 3733087 = 5599631) B5599631
theorem B1660639 : Blo 1474557 1660639 := bstep (se 1 (by rfl) ⟨1245479, by rfl⟩ : syracuseStep 1660639 = 2490959) B2490959
theorem B26933111 : Blo 1474557 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B3733715 : Blo 1474557 3733715 := bstep (se 1 (by rfl) ⟨2800286, by rfl⟩ : syracuseStep 3733715 = 5600573) B5600573
theorem B5601545 : Blo 1474557 5601545 := bstep (se 2 (by rfl) ⟨2100579, by rfl⟩ : syracuseStep 5601545 = 4201159) B4201159
theorem B2799983 : Blo 1474557 2799983 := bstep (se 1 (by rfl) ⟨2099987, by rfl⟩ : syracuseStep 2799983 = 4199975) B4199975
theorem B7092647 : Blo 1474557 7092647 := bstep (se 1 (by rfl) ⟨5319485, by rfl⟩ : syracuseStep 7092647 = 10638971) B10638971
theorem B7469495 : Blo 1474557 7469495 := bstep (se 1 (by rfl) ⟨5602121, by rfl⟩ : syracuseStep 7469495 = 11204243) B11204243
theorem B28375505 : Blo 1474557 28375505 := bstep (se 2 (by rfl) ⟨10640814, by rfl⟩ : syracuseStep 28375505 = 21281629) B21281629
theorem B2489015 : Blo 1474557 2489015 := bstep (se 1 (by rfl) ⟨1866761, by rfl⟩ : syracuseStep 2489015 = 3733523) B3733523
theorem B4979447 : Blo 1474557 4979447 := bstep (se 1 (by rfl) ⟨3734585, by rfl⟩ : syracuseStep 4979447 = 7469171) B7469171
theorem B3152783 : Blo 1474557 3152783 := bstep (se 1 (by rfl) ⟨2364587, by rfl⟩ : syracuseStep 3152783 = 4729175) B4729175
theorem B28367819 : Blo 1474557 28367819 := bstep (se 1 (by rfl) ⟨21275864, by rfl⟩ : syracuseStep 28367819 = 42551729) B42551729
theorem B6732989 : Blo 1474557 6732989 := bstep (se 3 (by rfl) ⟨1262435, by rfl⟩ : syracuseStep 6732989 = 2524871) B2524871
theorem B2800993 : Blo 1474557 2800993 := bstep (se 2 (by rfl) ⟨1050372, by rfl⟩ : syracuseStep 2800993 = 2100745) B2100745
theorem B4791649 : Blo 1474557 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B2489737 : Blo 1474557 2489737 := bstep (se 2 (by rfl) ⟨933651, by rfl⟩ : syracuseStep 2489737 = 1867303) B1867303
theorem B4201865 : Blo 1474557 4201865 := bstep (se 2 (by rfl) ⟨1575699, by rfl⟩ : syracuseStep 4201865 = 3151399) B3151399
theorem B4488635 : Blo 1474557 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B1867207 : Blo 1474557 1867207 := bstep (se 1 (by rfl) ⟨1400405, by rfl⟩ : syracuseStep 1867207 = 2800811) B2800811
theorem B8404505 : Blo 1474557 8404505 := bstep (se 2 (by rfl) ⟨3151689, by rfl⟩ : syracuseStep 8404505 = 6303379) B6303379
theorem B98385527 : Blo 1474557 98385527 := bstep (se 1 (by rfl) ⟨73789145, by rfl⟩ : syracuseStep 98385527 = 147578291) B147578291
theorem B4202219 : Blo 1474557 4202219 := bstep (se 1 (by rfl) ⟨3151664, by rfl⟩ : syracuseStep 4202219 = 6303329) B6303329
theorem B12607235 : Blo 1474557 12607235 := bstep (se 1 (by rfl) ⟨9455426, by rfl⟩ : syracuseStep 12607235 = 18910853) B18910853
theorem B4980527 : Blo 1474557 4980527 := bstep (se 1 (by rfl) ⟨3735395, by rfl⟩ : syracuseStep 4980527 = 7470791) B7470791
theorem B2490169 : Blo 1474557 2490169 := bstep (se 2 (by rfl) ⟨933813, by rfl⟩ : syracuseStep 2490169 = 1867627) B1867627
theorem B5603201 : Blo 1474557 5603201 := bstep (se 2 (by rfl) ⟨2101200, by rfl⟩ : syracuseStep 5603201 = 4202401) B4202401
theorem B64642991 : Blo 1474557 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B17948591 : Blo 1474557 17948591 := bstep (se 1 (by rfl) ⟨13461443, by rfl⟩ : syracuseStep 17948591 = 26922887) B26922887
theorem B5120135 : Blo 1474557 5120135 := bstep (se 1 (by rfl) ⟨3840101, by rfl⟩ : syracuseStep 5120135 = 7680203) B7680203
theorem B3784843 : Blo 1474557 3784843 := bstep (se 1 (by rfl) ⟨2838632, by rfl⟩ : syracuseStep 3784843 = 5677265) B5677265
theorem B1474791 : Blo 1474557 1474791 := bstep (se 1 (by rfl) ⟨1106093, by rfl⟩ : syracuseStep 1474791 = 2212187) B2212187
theorem B3318047 : Blo 1474557 3318047 := bstep (se 1 (by rfl) ⟨2488535, by rfl⟩ : syracuseStep 3318047 = 4977071) B4977071
theorem B2212127 : Blo 1474557 2212127 := bstep (se 1 (by rfl) ⟨1659095, by rfl⟩ : syracuseStep 2212127 = 3318191) B3318191
theorem B2490655 : Blo 1474557 2490655 := bstep (se 1 (by rfl) ⟨1867991, by rfl⟩ : syracuseStep 2490655 = 3735983) B3735983
theorem B2212151 : Blo 1474557 2212151 := bstep (se 1 (by rfl) ⟨1659113, by rfl⟩ : syracuseStep 2212151 = 3318227) B3318227
theorem B10641737 : Blo 1474557 10641737 := bstep (se 2 (by rfl) ⟨3990651, by rfl⟩ : syracuseStep 10641737 = 7981303) B7981303
theorem B2212223 : Blo 1474557 2212223 := bstep (se 1 (by rfl) ⟨1659167, by rfl⟩ : syracuseStep 2212223 = 3318335) B3318335
theorem B1474943 : Blo 1474557 1474943 := bstep (se 1 (by rfl) ⟨1106207, by rfl⟩ : syracuseStep 1474943 = 2212415) B2212415
theorem B4981175 : Blo 1474557 4981175 := bstep (se 1 (by rfl) ⟨3735881, by rfl⟩ : syracuseStep 4981175 = 7471763) B7471763
theorem B2212295 : Blo 1474557 2212295 := bstep (se 1 (by rfl) ⟨1659221, by rfl⟩ : syracuseStep 2212295 = 3318443) B3318443
theorem B1475023 : Blo 1474557 1475023 := bstep (se 1 (by rfl) ⟨1106267, by rfl⟩ : syracuseStep 1475023 = 2212535) B2212535
theorem B1475175 : Blo 1474557 1475175 := bstep (se 1 (by rfl) ⟨1106381, by rfl⟩ : syracuseStep 1475175 = 2212763) B2212763
theorem B2212649 : Blo 1474557 2212649 := bstep (se 2 (by rfl) ⟨829743, by rfl⟩ : syracuseStep 2212649 = 1659487) B1659487
theorem B2212655 : Blo 1474557 2212655 := bstep (se 1 (by rfl) ⟨1659491, by rfl⟩ : syracuseStep 2212655 = 3318983) B3318983
theorem B7086959 : Blo 1474557 7086959 := bstep (se 1 (by rfl) ⟨5315219, by rfl⟩ : syracuseStep 7086959 = 10630439) B10630439
theorem B1475439 : Blo 1474557 1475439 := bstep (se 1 (by rfl) ⟨1106579, by rfl⟩ : syracuseStep 1475439 = 2213159) B2213159
theorem B4981661 : Blo 1474557 4981661 := bstep (se 3 (by rfl) ⟨934061, by rfl⟩ : syracuseStep 4981661 = 1868123) B1868123
theorem B3318695 : Blo 1474557 3318695 := bstep (se 1 (by rfl) ⟨2489021, by rfl⟩ : syracuseStep 3318695 = 4978043) B4978043
theorem B2212775 : Blo 1474557 2212775 := bstep (se 1 (by rfl) ⟨1659581, by rfl⟩ : syracuseStep 2212775 = 3319163) B3319163
theorem B1475495 : Blo 1474557 1475495 := bstep (se 1 (by rfl) ⟨1106621, by rfl⟩ : syracuseStep 1475495 = 2213243) B2213243
theorem B2491303 : Blo 1474557 2491303 := bstep (se 1 (by rfl) ⟨1868477, by rfl⟩ : syracuseStep 2491303 = 3736955) B3736955
theorem B4981715 : Blo 1474557 4981715 := bstep (se 1 (by rfl) ⟨3736286, by rfl⟩ : syracuseStep 4981715 = 7472573) B7472573
theorem B9454583 : Blo 1474557 9454583 := bstep (se 1 (by rfl) ⟨7090937, by rfl⟩ : syracuseStep 9454583 = 14181875) B14181875
theorem B2212859 : Blo 1474557 2212859 := bstep (se 1 (by rfl) ⟨1659644, by rfl⟩ : syracuseStep 2212859 = 3319289) B3319289
theorem B1475579 : Blo 1474557 1475579 := bstep (se 1 (by rfl) ⟨1106684, by rfl⟩ : syracuseStep 1475579 = 2213369) B2213369
theorem B3736601 : Blo 1474557 3736601 := bstep (se 2 (by rfl) ⟨1401225, by rfl⟩ : syracuseStep 3736601 = 2802451) B2802451
theorem B2212919 : Blo 1474557 2212919 := bstep (se 1 (by rfl) ⟨1659689, by rfl⟩ : syracuseStep 2212919 = 3319379) B3319379
theorem B1475647 : Blo 1474557 1475647 := bstep (se 1 (by rfl) ⟨1106735, by rfl⟩ : syracuseStep 1475647 = 2213471) B2213471
theorem B2491465 : Blo 1474557 2491465 := bstep (se 2 (by rfl) ⟨934299, by rfl⟩ : syracuseStep 2491465 = 1868599) B1868599
theorem B2491499 : Blo 1474557 2491499 := bstep (se 1 (by rfl) ⟨1868624, by rfl⟩ : syracuseStep 2491499 = 3737249) B3737249
theorem B11969693 : Blo 1474557 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B2213039 : Blo 1474557 2213039 := bstep (se 1 (by rfl) ⟨1659779, by rfl⟩ : syracuseStep 2213039 = 3319559) B3319559
theorem B1475791 : Blo 1474557 1475791 := bstep (se 1 (by rfl) ⟨1106843, by rfl⟩ : syracuseStep 1475791 = 2213687) B2213687
theorem B10642661 : Blo 1474557 10642661 := bstep (se 4 (by rfl) ⟨997749, by rfl⟩ : syracuseStep 10642661 = 1995499) B1995499
theorem B17958277 : Blo 1474557 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B1475995 : Blo 1474557 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B9094571 : Blo 1474557 9094571 := bstep (se 1 (by rfl) ⟨6820928, by rfl⟩ : syracuseStep 9094571 = 13641857) B13641857
theorem B31909301 : Blo 1474557 31909301 := bstep (se 5 (by rfl) ⟨1495748, by rfl⟩ : syracuseStep 31909301 = 2991497) B2991497
theorem B28730861 : Blo 1474557 28730861 := bstep (se 3 (by rfl) ⟨5387036, by rfl⟩ : syracuseStep 28730861 = 10774073) B10774073
theorem B5047823 : Blo 1474557 5047823 := bstep (se 1 (by rfl) ⟨3785867, by rfl⟩ : syracuseStep 5047823 = 7571735) B7571735
theorem B2213447 : Blo 1474557 2213447 := bstep (se 1 (by rfl) ⟨1660085, by rfl⟩ : syracuseStep 2213447 = 3320171) B3320171
theorem B7472735 : Blo 1474557 7472735 := bstep (se 1 (by rfl) ⟨5604551, by rfl⟩ : syracuseStep 7472735 = 11209103) B11209103
theorem B4728431 : Blo 1474557 4728431 := bstep (se 1 (by rfl) ⟨3546323, by rfl⟩ : syracuseStep 4728431 = 7092647) B7092647
theorem B1476207 : Blo 1474557 1476207 := bstep (se 1 (by rfl) ⟨1107155, by rfl⟩ : syracuseStep 1476207 = 2214311) B2214311
theorem B12600947 : Blo 1474557 12600947 := bstep (se 1 (by rfl) ⟨9450710, by rfl⟩ : syracuseStep 12600947 = 18901421) B18901421
theorem B16803449 : Blo 1474557 16803449 := bstep (se 2 (by rfl) ⟨6301293, by rfl⟩ : syracuseStep 16803449 = 12602587) B12602587
theorem B18917003 : Blo 1474557 18917003 := bstep (se 1 (by rfl) ⟨14187752, by rfl⟩ : syracuseStep 18917003 = 28375505) B28375505
theorem B2213543 : Blo 1474557 2213543 := bstep (se 1 (by rfl) ⟨1660157, by rfl⟩ : syracuseStep 2213543 = 3320315) B3320315
theorem B1476263 : Blo 1474557 1476263 := bstep (se 1 (by rfl) ⟨1107197, by rfl⟩ : syracuseStep 1476263 = 2214395) B2214395
theorem B7980767 : Blo 1474557 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B2213627 : Blo 1474557 2213627 := bstep (se 1 (by rfl) ⟨1660220, by rfl⟩ : syracuseStep 2213627 = 3320441) B3320441
theorem B1476347 : Blo 1474557 1476347 := bstep (se 1 (by rfl) ⟨1107260, by rfl⟩ : syracuseStep 1476347 = 2214521) B2214521
theorem B2213663 : Blo 1474557 2213663 := bstep (se 1 (by rfl) ⟨1660247, by rfl⟩ : syracuseStep 2213663 = 3320495) B3320495
theorem B1476383 : Blo 1474557 1476383 := bstep (se 1 (by rfl) ⟨1107287, by rfl⟩ : syracuseStep 1476383 = 2214575) B2214575
theorem B1476415 : Blo 1474557 1476415 := bstep (se 1 (by rfl) ⟨1107311, by rfl⟩ : syracuseStep 1476415 = 2214623) B2214623
theorem B3319631 : Blo 1474557 3319631 := bstep (se 1 (by rfl) ⟨2489723, by rfl⟩ : syracuseStep 3319631 = 4979447) B4979447
theorem B2213711 : Blo 1474557 2213711 := bstep (se 1 (by rfl) ⟨1660283, by rfl⟩ : syracuseStep 2213711 = 3320567) B3320567
theorem B3319649 : Blo 1474557 3319649 := bstep (se 2 (by rfl) ⟨1244868, by rfl⟩ : syracuseStep 3319649 = 2489737) B2489737
theorem B3737441 : Blo 1474557 3737441 := bstep (se 2 (by rfl) ⟨1401540, by rfl⟩ : syracuseStep 3737441 = 2803081) B2803081
theorem B2213831 : Blo 1474557 2213831 := bstep (se 1 (by rfl) ⟨1660373, by rfl⟩ : syracuseStep 2213831 = 3320747) B3320747
theorem B35875001 : Blo 1474557 35875001 := bstep (se 2 (by rfl) ⟨13453125, by rfl⟩ : syracuseStep 35875001 = 26906251) B26906251
theorem B2214185 : Blo 1474557 2214185 := bstep (se 2 (by rfl) ⟨830319, by rfl⟩ : syracuseStep 2214185 = 1660639) B1660639
theorem B2214191 : Blo 1474557 2214191 := bstep (se 1 (by rfl) ⟨1660643, by rfl⟩ : syracuseStep 2214191 = 3321287) B3321287
theorem B8407421 : Blo 1474557 8407421 := bstep (se 3 (by rfl) ⟨1576391, by rfl⟩ : syracuseStep 8407421 = 3152783) B3152783
theorem B48499087 : Blo 1474557 48499087 := bstep (se 1 (by rfl) ⟨36374315, by rfl⟩ : syracuseStep 48499087 = 72748631) B72748631
theorem B3320225 : Blo 1474557 3320225 := bstep (se 2 (by rfl) ⟨1245084, by rfl⟩ : syracuseStep 3320225 = 2490169) B2490169
theorem B3320351 : Blo 1474557 3320351 := bstep (se 1 (by rfl) ⟨2490263, by rfl⟩ : syracuseStep 3320351 = 4980527) B4980527
theorem B2214431 : Blo 1474557 2214431 := bstep (se 1 (by rfl) ⟨1660823, by rfl⟩ : syracuseStep 2214431 = 3321647) B3321647
theorem B5605919 : Blo 1474557 5605919 := bstep (se 1 (by rfl) ⟨4204439, by rfl⟩ : syracuseStep 5605919 = 8408879) B8408879
theorem B8407739 : Blo 1474557 8407739 := bstep (se 1 (by rfl) ⟨6305804, by rfl⟩ : syracuseStep 8407739 = 12611609) B12611609
theorem B2214815 : Blo 1474557 2214815 := bstep (se 1 (by rfl) ⟨1661111, by rfl⟩ : syracuseStep 2214815 = 3322223) B3322223
theorem B4484521 : Blo 1474557 4484521 := bstep (se 2 (by rfl) ⟨1681695, by rfl⟩ : syracuseStep 4484521 = 3363391) B3363391
theorem B9448919 : Blo 1474557 9448919 := bstep (se 1 (by rfl) ⟨7086689, by rfl⟩ : syracuseStep 9448919 = 14173379) B14173379
theorem B2657855 : Blo 1474557 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B5983807 : Blo 1474557 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B21270215 : Blo 1474557 21270215 := bstep (se 1 (by rfl) ⟨15952661, by rfl⟩ : syracuseStep 21270215 = 31905323) B31905323
theorem B5599115 : Blo 1474557 5599115 := bstep (se 1 (by rfl) ⟨4199336, by rfl⟩ : syracuseStep 5599115 = 8398673) B8398673
theorem B3321755 : Blo 1474557 3321755 := bstep (se 1 (by rfl) ⟨2491316, by rfl⟩ : syracuseStep 3321755 = 4982633) B4982633
theorem B9449459 : Blo 1474557 9449459 := bstep (se 1 (by rfl) ⟨7087094, by rfl⟩ : syracuseStep 9449459 = 14174189) B14174189
theorem B8400905 : Blo 1474557 8400905 := bstep (se 2 (by rfl) ⟨3150339, by rfl⟩ : syracuseStep 8400905 = 6300679) B6300679
theorem B3322043 : Blo 1474557 3322043 := bstep (se 1 (by rfl) ⟨2491532, by rfl⟩ : syracuseStep 3322043 = 4983065) B4983065
theorem B21557441 : Blo 1474557 21557441 := bstep (se 2 (by rfl) ⟨8084040, by rfl⟩ : syracuseStep 21557441 = 16168081) B16168081
theorem B262361405 : Blo 1474557 262361405 := bstep (se 3 (by rfl) ⟨49192763, by rfl⟩ : syracuseStep 262361405 = 98385527) B98385527
theorem B1659343 : Blo 1474557 1659343 := bstep (se 1 (by rfl) ⟨1244507, by rfl⟩ : syracuseStep 1659343 = 2489015) B2489015
theorem B16167397 : Blo 1474557 16167397 := bstep (se 4 (by rfl) ⟨1515693, by rfl⟩ : syracuseStep 16167397 = 3031387) B3031387
theorem B689525237 : Blo 1474557 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B6304337 : Blo 1474557 6304337 := bstep (se 2 (by rfl) ⟨2364126, by rfl⟩ : syracuseStep 6304337 = 4728253) B4728253
theorem B18911879 : Blo 1474557 18911879 := bstep (se 1 (by rfl) ⟨14183909, by rfl⟩ : syracuseStep 18911879 = 28367819) B28367819
theorem B4977449 : Blo 1474557 4977449 := bstep (se 2 (by rfl) ⟨1866543, by rfl⟩ : syracuseStep 4977449 = 3733087) B3733087
theorem B4977719 : Blo 1474557 4977719 := bstep (se 1 (by rfl) ⟨3733289, by rfl⟩ : syracuseStep 4977719 = 7466579) B7466579
theorem B8516723 : Blo 1474557 8516723 := bstep (se 1 (by rfl) ⟨6387542, by rfl⟩ : syracuseStep 8516723 = 12775085) B12775085
theorem B11965727 : Blo 1474557 11965727 := bstep (se 1 (by rfl) ⟨8974295, by rfl⟩ : syracuseStep 11965727 = 17948591) B17948591
theorem B10098029 : Blo 1474557 10098029 := bstep (se 3 (by rfl) ⟨1893380, by rfl⟩ : syracuseStep 10098029 = 3786761) B3786761
theorem B1660315 : Blo 1474557 1660315 := bstep (se 1 (by rfl) ⟨1245236, by rfl⟩ : syracuseStep 1660315 = 2490473) B2490473
theorem B8402615 : Blo 1474557 8402615 := bstep (se 1 (by rfl) ⟨6301961, by rfl⟩ : syracuseStep 8402615 = 12603923) B12603923
theorem B7468847 : Blo 1474557 7468847 := bstep (se 1 (by rfl) ⟨5601635, by rfl⟩ : syracuseStep 7468847 = 11203271) B11203271
theorem B7092031 : Blo 1474557 7092031 := bstep (se 1 (by rfl) ⟨5319023, by rfl⟩ : syracuseStep 7092031 = 10638047) B10638047
theorem B2799497 : Blo 1474557 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B4200407 : Blo 1474557 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B5314585 : Blo 1474557 5314585 := bstep (se 2 (by rfl) ⟨1992969, by rfl⟩ : syracuseStep 5314585 = 3985939) B3985939
theorem B5314643 : Blo 1474557 5314643 := bstep (se 1 (by rfl) ⟨3985982, by rfl⟩ : syracuseStep 5314643 = 7971965) B7971965
theorem B3545171 : Blo 1474557 3545171 := bstep (se 1 (by rfl) ⟨2658878, by rfl⟩ : syracuseStep 3545171 = 5317757) B5317757
theorem B4724831 : Blo 1474557 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B2488475 : Blo 1474557 2488475 := bstep (se 1 (by rfl) ⟨1866356, by rfl⟩ : syracuseStep 2488475 = 3732713) B3732713
theorem B10098931 : Blo 1474557 10098931 := bstep (se 1 (by rfl) ⟨7574198, by rfl⟩ : syracuseStep 10098931 = 15148397) B15148397
theorem B2488583 : Blo 1474557 2488583 := bstep (se 1 (by rfl) ⟨1866437, by rfl⟩ : syracuseStep 2488583 = 3732875) B3732875
theorem B17955407 : Blo 1474557 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B14178989 : Blo 1474557 14178989 := bstep (se 3 (by rfl) ⟨2658560, by rfl⟩ : syracuseStep 14178989 = 5317121) B5317121
theorem B2489143 : Blo 1474557 2489143 := bstep (se 1 (by rfl) ⟨1866857, by rfl⟩ : syracuseStep 2489143 = 3733715) B3733715
theorem B3734363 : Blo 1474557 3734363 := bstep (se 1 (by rfl) ⟨2800772, by rfl⟩ : syracuseStep 3734363 = 5601545) B5601545
theorem B1866655 : Blo 1474557 1866655 := bstep (se 1 (by rfl) ⟨1399991, by rfl⟩ : syracuseStep 1866655 = 2799983) B2799983
theorem B4979663 : Blo 1474557 4979663 := bstep (se 1 (by rfl) ⟨3734747, by rfl⟩ : syracuseStep 4979663 = 7469495) B7469495
theorem B6298681 : Blo 1474557 6298681 := bstep (se 2 (by rfl) ⟨2362005, by rfl⟩ : syracuseStep 6298681 = 4724011) B4724011
theorem B3734657 : Blo 1474557 3734657 := bstep (se 2 (by rfl) ⟨1400496, by rfl⟩ : syracuseStep 3734657 = 2800993) B2800993
theorem B6388865 : Blo 1474557 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B2489609 : Blo 1474557 2489609 := bstep (se 2 (by rfl) ⟨933603, by rfl⟩ : syracuseStep 2489609 = 1867207) B1867207
theorem B3595529 : Blo 1474557 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B4488659 : Blo 1474557 4488659 := bstep (se 1 (by rfl) ⟨3366494, by rfl⟩ : syracuseStep 4488659 = 6732989) B6732989
theorem B2801243 : Blo 1474557 2801243 := bstep (se 1 (by rfl) ⟨2100932, by rfl⟩ : syracuseStep 2801243 = 4201865) B4201865
theorem B5603003 : Blo 1474557 5603003 := bstep (se 1 (by rfl) ⟨4202252, by rfl⟩ : syracuseStep 5603003 = 8404505) B8404505
theorem B2801479 : Blo 1474557 2801479 := bstep (se 1 (by rfl) ⟨2101109, by rfl⟩ : syracuseStep 2801479 = 4202219) B4202219
theorem B8404823 : Blo 1474557 8404823 := bstep (se 1 (by rfl) ⟨6303617, by rfl⟩ : syracuseStep 8404823 = 12607235) B12607235
theorem B3735467 : Blo 1474557 3735467 := bstep (se 1 (by rfl) ⟨2801600, by rfl⟩ : syracuseStep 3735467 = 5603201) B5603201
theorem B7086113 : Blo 1474557 7086113 := bstep (se 2 (by rfl) ⟨2657292, by rfl⟩ : syracuseStep 7086113 = 5314585) B5314585
theorem B5046457 : Blo 1474557 5046457 := bstep (se 2 (by rfl) ⟨1892421, by rfl⟩ : syracuseStep 5046457 = 3784843) B3784843
theorem B2212031 : Blo 1474557 2212031 := bstep (se 1 (by rfl) ⟨1659023, by rfl⟩ : syracuseStep 2212031 = 3318047) B3318047
theorem B1474751 : Blo 1474557 1474751 := bstep (se 1 (by rfl) ⟨1106063, by rfl⟩ : syracuseStep 1474751 = 2212127) B2212127
theorem B1474767 : Blo 1474557 1474767 := bstep (se 1 (by rfl) ⟨1106075, by rfl⟩ : syracuseStep 1474767 = 2212151) B2212151
theorem B174907603 : Blo 1474557 174907603 := bstep (se 1 (by rfl) ⟨131180702, by rfl⟩ : syracuseStep 174907603 = 262361405) B262361405
theorem B12599549 : Blo 1474557 12599549 := bstep (se 3 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 12599549 = 4724831) B4724831
theorem B1474815 : Blo 1474557 1474815 := bstep (se 1 (by rfl) ⟨1106111, by rfl⟩ : syracuseStep 1474815 = 2212223) B2212223
theorem B1474863 : Blo 1474557 1474863 := bstep (se 1 (by rfl) ⟨1106147, by rfl⟩ : syracuseStep 1474863 = 2212295) B2212295
theorem B4202891 : Blo 1474557 4202891 := bstep (se 1 (by rfl) ⟨3152168, by rfl⟩ : syracuseStep 4202891 = 6304337) B6304337
theorem B12607919 : Blo 1474557 12607919 := bstep (se 1 (by rfl) ⟨9455939, by rfl⟩ : syracuseStep 12607919 = 18911879) B18911879
theorem B3318299 : Blo 1474557 3318299 := bstep (se 1 (by rfl) ⟨2488724, by rfl⟩ : syracuseStep 3318299 = 4977449) B4977449
theorem B1475099 : Blo 1474557 1475099 := bstep (se 1 (by rfl) ⟨1106324, by rfl⟩ : syracuseStep 1475099 = 2212649) B2212649
theorem B1475103 : Blo 1474557 1475103 := bstep (se 1 (by rfl) ⟨1106327, by rfl⟩ : syracuseStep 1475103 = 2212655) B2212655
theorem B2212457 : Blo 1474557 2212457 := bstep (se 2 (by rfl) ⟨829671, by rfl⟩ : syracuseStep 2212457 = 1659343) B1659343
theorem B2212463 : Blo 1474557 2212463 := bstep (se 1 (by rfl) ⟨1659347, by rfl⟩ : syracuseStep 2212463 = 3318695) B3318695
theorem B1475183 : Blo 1474557 1475183 := bstep (se 1 (by rfl) ⟨1106387, by rfl⟩ : syracuseStep 1475183 = 2212775) B2212775
theorem B1475239 : Blo 1474557 1475239 := bstep (se 1 (by rfl) ⟨1106429, by rfl⟩ : syracuseStep 1475239 = 2212859) B2212859
theorem B2491067 : Blo 1474557 2491067 := bstep (se 1 (by rfl) ⟨1868300, by rfl⟩ : syracuseStep 2491067 = 3736601) B3736601
theorem B3318479 : Blo 1474557 3318479 := bstep (se 1 (by rfl) ⟨2488859, by rfl⟩ : syracuseStep 3318479 = 4977719) B4977719
theorem B1475279 : Blo 1474557 1475279 := bstep (se 1 (by rfl) ⟨1106459, by rfl⟩ : syracuseStep 1475279 = 2212919) B2212919
theorem B7979795 : Blo 1474557 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B1475359 : Blo 1474557 1475359 := bstep (se 1 (by rfl) ⟨1106519, by rfl⟩ : syracuseStep 1475359 = 2213039) B2213039
theorem B7095107 : Blo 1474557 7095107 := bstep (se 1 (by rfl) ⟨5321330, by rfl⟩ : syracuseStep 7095107 = 10642661) B10642661
theorem B28377965 : Blo 1474557 28377965 := bstep (se 3 (by rfl) ⟨5320868, by rfl⟩ : syracuseStep 28377965 = 10641737) B10641737
theorem B6063047 : Blo 1474557 6063047 := bstep (se 1 (by rfl) ⟨4547285, by rfl⟩ : syracuseStep 6063047 = 9094571) B9094571
theorem B19153907 : Blo 1474557 19153907 := bstep (se 1 (by rfl) ⟨14365430, by rfl⟩ : syracuseStep 19153907 = 28730861) B28730861
theorem B1475631 : Blo 1474557 1475631 := bstep (se 1 (by rfl) ⟨1106723, by rfl⟩ : syracuseStep 1475631 = 2213447) B2213447
theorem B4981823 : Blo 1474557 4981823 := bstep (se 1 (by rfl) ⟨3736367, by rfl⟩ : syracuseStep 4981823 = 7472735) B7472735
theorem B3318857 : Blo 1474557 3318857 := bstep (se 2 (by rfl) ⟨1244571, by rfl⟩ : syracuseStep 3318857 = 2489143) B2489143
theorem B1475695 : Blo 1474557 1475695 := bstep (se 1 (by rfl) ⟨1106771, by rfl⟩ : syracuseStep 1475695 = 2213543) B2213543
theorem B1475751 : Blo 1474557 1475751 := bstep (se 1 (by rfl) ⟨1106813, by rfl⟩ : syracuseStep 1475751 = 2213627) B2213627
theorem B1475775 : Blo 1474557 1475775 := bstep (se 1 (by rfl) ⟨1106831, by rfl⟩ : syracuseStep 1475775 = 2213663) B2213663
theorem B2213087 : Blo 1474557 2213087 := bstep (se 1 (by rfl) ⟨1659815, by rfl⟩ : syracuseStep 2213087 = 3319631) B3319631
theorem B1475807 : Blo 1474557 1475807 := bstep (se 1 (by rfl) ⟨1106855, by rfl⟩ : syracuseStep 1475807 = 2213711) B2213711
theorem B2213099 : Blo 1474557 2213099 := bstep (se 1 (by rfl) ⟨1659824, by rfl⟩ : syracuseStep 2213099 = 3319649) B3319649
theorem B2491627 : Blo 1474557 2491627 := bstep (se 1 (by rfl) ⟨1868720, by rfl⟩ : syracuseStep 2491627 = 3737441) B3737441
theorem B1475887 : Blo 1474557 1475887 := bstep (se 1 (by rfl) ⟨1106915, by rfl⟩ : syracuseStep 1475887 = 2213831) B2213831
theorem B8398241 : Blo 1474557 8398241 := bstep (se 2 (by rfl) ⟨3149340, by rfl⟩ : syracuseStep 8398241 = 6298681) B6298681
theorem B1476123 : Blo 1474557 1476123 := bstep (se 1 (by rfl) ⟨1107092, by rfl⟩ : syracuseStep 1476123 = 2214185) B2214185
theorem B1476127 : Blo 1474557 1476127 := bstep (se 1 (by rfl) ⟨1107095, by rfl⟩ : syracuseStep 1476127 = 2214191) B2214191
theorem B5604947 : Blo 1474557 5604947 := bstep (se 1 (by rfl) ⟨4203710, by rfl⟩ : syracuseStep 5604947 = 8407421) B8407421
theorem B2213483 : Blo 1474557 2213483 := bstep (se 1 (by rfl) ⟨1660112, by rfl⟩ : syracuseStep 2213483 = 3320225) B3320225
theorem B2213567 : Blo 1474557 2213567 := bstep (se 1 (by rfl) ⟨1660175, by rfl⟩ : syracuseStep 2213567 = 3320351) B3320351
theorem B1476287 : Blo 1474557 1476287 := bstep (se 1 (by rfl) ⟨1107215, by rfl⟩ : syracuseStep 1476287 = 2214431) B2214431
theorem B3737279 : Blo 1474557 3737279 := bstep (se 1 (by rfl) ⟨2802959, by rfl⟩ : syracuseStep 3737279 = 5605919) B5605919
theorem B11970271 : Blo 1474557 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B5605159 : Blo 1474557 5605159 := bstep (se 1 (by rfl) ⟨4203869, by rfl⟩ : syracuseStep 5605159 = 8407739) B8407739
theorem B2213753 : Blo 1474557 2213753 := bstep (se 2 (by rfl) ⟨830157, by rfl⟩ : syracuseStep 2213753 = 1660315) B1660315
theorem B1476543 : Blo 1474557 1476543 := bstep (se 1 (by rfl) ⟨1107407, by rfl⟩ : syracuseStep 1476543 = 2214815) B2214815
theorem B3319775 : Blo 1474557 3319775 := bstep (se 1 (by rfl) ⟨2489831, by rfl⟩ : syracuseStep 3319775 = 4979663) B4979663
theorem B2992439 : Blo 1474557 2992439 := bstep (se 1 (by rfl) ⟨2244329, by rfl⟩ : syracuseStep 2992439 = 4488659) B4488659
theorem B1771903 : Blo 1474557 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B9456041 : Blo 1474557 9456041 := bstep (se 2 (by rfl) ⟨3546015, by rfl⟩ : syracuseStep 9456041 = 7092031) B7092031
theorem B2214503 : Blo 1474557 2214503 := bstep (se 1 (by rfl) ⟨1660877, by rfl⟩ : syracuseStep 2214503 = 3321755) B3321755
theorem B2214695 : Blo 1474557 2214695 := bstep (se 1 (by rfl) ⟨1661021, by rfl⟩ : syracuseStep 2214695 = 3322043) B3322043
theorem B14371627 : Blo 1474557 14371627 := bstep (se 1 (by rfl) ⟨10778720, by rfl⟩ : syracuseStep 14371627 = 21557441) B21557441
theorem B3320783 : Blo 1474557 3320783 := bstep (se 1 (by rfl) ⟨2490587, by rfl⟩ : syracuseStep 3320783 = 4981175) B4981175
theorem B22711261 : Blo 1474557 22711261 := bstep (se 3 (by rfl) ⟨4258361, by rfl⟩ : syracuseStep 22711261 = 8516723) B8516723
theorem B3320873 : Blo 1474557 3320873 := bstep (se 2 (by rfl) ⟨1245327, by rfl⟩ : syracuseStep 3320873 = 2490655) B2490655
theorem B3321107 : Blo 1474557 3321107 := bstep (se 1 (by rfl) ⟨2490830, by rfl⟩ : syracuseStep 3321107 = 4981661) B4981661
theorem B21556529 : Blo 1474557 21556529 := bstep (se 2 (by rfl) ⟨8083698, by rfl⟩ : syracuseStep 21556529 = 16167397) B16167397
theorem B3321143 : Blo 1474557 3321143 := bstep (se 1 (by rfl) ⟨2490857, by rfl⟩ : syracuseStep 3321143 = 4981715) B4981715
theorem B6303055 : Blo 1474557 6303055 := bstep (se 1 (by rfl) ⟨4727291, by rfl⟩ : syracuseStep 6303055 = 9454583) B9454583
theorem B8400631 : Blo 1474557 8400631 := bstep (se 1 (by rfl) ⟨6300473, by rfl⟩ : syracuseStep 8400631 = 12600947) B12600947
theorem B11202299 : Blo 1474557 11202299 := bstep (se 1 (by rfl) ⟨8401724, by rfl⟩ : syracuseStep 11202299 = 16803449) B16803449
theorem B12611335 : Blo 1474557 12611335 := bstep (se 1 (by rfl) ⟨9458501, by rfl⟩ : syracuseStep 12611335 = 18917003) B18917003
theorem B5320511 : Blo 1474557 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B3321737 : Blo 1474557 3321737 := bstep (se 2 (by rfl) ⟨1245651, by rfl⟩ : syracuseStep 3321737 = 2491303) B2491303
theorem B3543095 : Blo 1474557 3543095 := bstep (se 1 (by rfl) ⟨2657321, by rfl⟩ : syracuseStep 3543095 = 5314643) B5314643
theorem B2363447 : Blo 1474557 2363447 := bstep (se 1 (by rfl) ⟨1772585, by rfl⟩ : syracuseStep 2363447 = 3545171) B3545171
theorem B3321953 : Blo 1474557 3321953 := bstep (se 2 (by rfl) ⟨1245732, by rfl⟩ : syracuseStep 3321953 = 2491465) B2491465
theorem B1658983 : Blo 1474557 1658983 := bstep (se 1 (by rfl) ⟨1244237, by rfl⟩ : syracuseStep 1658983 = 2488475) B2488475
theorem B23916667 : Blo 1474557 23916667 := bstep (se 1 (by rfl) ⟨17937500, by rfl⟩ : syracuseStep 23916667 = 35875001) B35875001
theorem B1659055 : Blo 1474557 1659055 := bstep (se 1 (by rfl) ⟨1244291, by rfl⟩ : syracuseStep 1659055 = 2488583) B2488583
theorem B95777477 : Blo 1474557 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B1659739 : Blo 1474557 1659739 := bstep (se 1 (by rfl) ⟨1244804, by rfl⟩ : syracuseStep 1659739 = 2489609) B2489609
theorem B2397019 : Blo 1474557 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B3732743 : Blo 1474557 3732743 := bstep (se 1 (by rfl) ⟨2799557, by rfl⟩ : syracuseStep 3732743 = 5599115) B5599115
theorem B5600603 : Blo 1474557 5600603 := bstep (se 1 (by rfl) ⟨4200452, by rfl⟩ : syracuseStep 5600603 = 8400905) B8400905
theorem B3413423 : Blo 1474557 3413423 := bstep (se 1 (by rfl) ⟨2560067, by rfl⟩ : syracuseStep 3413423 = 5120135) B5120135
theorem B13465241 : Blo 1474557 13465241 := bstep (se 2 (by rfl) ⟨5049465, by rfl⟩ : syracuseStep 13465241 = 10098931) B10098931
theorem B64665449 : Blo 1474557 64665449 := bstep (se 2 (by rfl) ⟨24249543, by rfl⟩ : syracuseStep 64665449 = 48499087) B48499087
theorem B4724639 : Blo 1474557 4724639 := bstep (se 1 (by rfl) ⟨3543479, by rfl⟩ : syracuseStep 4724639 = 7086959) B7086959
theorem B1660999 : Blo 1474557 1660999 := bstep (se 1 (by rfl) ⟨1245749, by rfl⟩ : syracuseStep 1660999 = 2491499) B2491499
theorem B7977151 : Blo 1474557 7977151 := bstep (se 1 (by rfl) ⟨5982863, by rfl⟩ : syracuseStep 7977151 = 11965727) B11965727
theorem B6732019 : Blo 1474557 6732019 := bstep (se 1 (by rfl) ⟨5049014, by rfl⟩ : syracuseStep 6732019 = 10098029) B10098029
theorem B21272867 : Blo 1474557 21272867 := bstep (se 1 (by rfl) ⟨15954650, by rfl⟩ : syracuseStep 21272867 = 31909301) B31909301
theorem B3365215 : Blo 1474557 3365215 := bstep (se 1 (by rfl) ⟨2523911, by rfl⟩ : syracuseStep 3365215 = 5047823) B5047823
theorem B3152287 : Blo 1474557 3152287 := bstep (se 1 (by rfl) ⟨2364215, by rfl⟩ : syracuseStep 3152287 = 4728431) B4728431
theorem B5601743 : Blo 1474557 5601743 := bstep (se 1 (by rfl) ⟨4201307, by rfl⟩ : syracuseStep 5601743 = 8402615) B8402615
theorem B4979231 : Blo 1474557 4979231 := bstep (se 1 (by rfl) ⟨3734423, by rfl⟩ : syracuseStep 4979231 = 7468847) B7468847
theorem B2488873 : Blo 1474557 2488873 := bstep (se 2 (by rfl) ⟨933327, by rfl⟩ : syracuseStep 2488873 = 1866655) B1866655
theorem B1866331 : Blo 1474557 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B1838733965 : Blo 1474557 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B2800271 : Blo 1474557 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B7469981 : Blo 1474557 7469981 := bstep (se 3 (by rfl) ⟨1400621, by rfl⟩ : syracuseStep 7469981 = 2801243) B2801243
theorem B9452659 : Blo 1474557 9452659 := bstep (se 1 (by rfl) ⟨7089494, by rfl⟩ : syracuseStep 9452659 = 14178989) B14178989
theorem B5979361 : Blo 1474557 5979361 := bstep (se 2 (by rfl) ⟨2242260, by rfl⟩ : syracuseStep 5979361 = 4484521) B4484521
theorem B2489575 : Blo 1474557 2489575 := bstep (se 1 (by rfl) ⟨1867181, by rfl⟩ : syracuseStep 2489575 = 3734363) B3734363
theorem B7978409 : Blo 1474557 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B2489771 : Blo 1474557 2489771 := bstep (se 1 (by rfl) ⟨1867328, by rfl⟩ : syracuseStep 2489771 = 3734657) B3734657
theorem B4259243 : Blo 1474557 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B6299279 : Blo 1474557 6299279 := bstep (se 1 (by rfl) ⟨4724459, by rfl⟩ : syracuseStep 6299279 = 9448919) B9448919
theorem B3735305 : Blo 1474557 3735305 := bstep (se 2 (by rfl) ⟨1400739, by rfl⟩ : syracuseStep 3735305 = 2801479) B2801479
theorem B3735335 : Blo 1474557 3735335 := bstep (se 1 (by rfl) ⟨2801501, by rfl⟩ : syracuseStep 3735335 = 5603003) B5603003
theorem B14180143 : Blo 1474557 14180143 := bstep (se 1 (by rfl) ⟨10635107, by rfl⟩ : syracuseStep 14180143 = 21270215) B21270215
theorem B5603215 : Blo 1474557 5603215 := bstep (se 1 (by rfl) ⟨4202411, by rfl⟩ : syracuseStep 5603215 = 8404823) B8404823
theorem B2490311 : Blo 1474557 2490311 := bstep (se 1 (by rfl) ⟨1867733, by rfl⟩ : syracuseStep 2490311 = 3735467) B3735467
theorem B6299639 : Blo 1474557 6299639 := bstep (se 1 (by rfl) ⟨4724729, by rfl⟩ : syracuseStep 6299639 = 9449459) B9449459
theorem B1474687 : Blo 1474557 1474687 := bstep (se 1 (by rfl) ⟨1106015, by rfl⟩ : syracuseStep 1474687 = 2212031) B2212031
theorem B2211977 : Blo 1474557 2211977 := bstep (se 2 (by rfl) ⟨829491, by rfl⟩ : syracuseStep 2211977 = 1658983) B1658983
theorem B2212073 : Blo 1474557 2212073 := bstep (se 2 (by rfl) ⟨829527, by rfl⟩ : syracuseStep 2212073 = 1659055) B1659055
theorem B2801927 : Blo 1474557 2801927 := bstep (se 1 (by rfl) ⟨2101445, by rfl⟩ : syracuseStep 2801927 = 4202891) B4202891
theorem B233210137 : Blo 1474557 233210137 := bstep (se 2 (by rfl) ⟨87453801, by rfl⟩ : syracuseStep 233210137 = 174907603) B174907603
theorem B8405279 : Blo 1474557 8405279 := bstep (se 1 (by rfl) ⟨6303959, by rfl⟩ : syracuseStep 8405279 = 12607919) B12607919
theorem B2212199 : Blo 1474557 2212199 := bstep (se 1 (by rfl) ⟨1659149, by rfl⟩ : syracuseStep 2212199 = 3318299) B3318299
theorem B1474971 : Blo 1474557 1474971 := bstep (se 1 (by rfl) ⟨1106228, by rfl⟩ : syracuseStep 1474971 = 2212457) B2212457
theorem B1474975 : Blo 1474557 1474975 := bstep (se 1 (by rfl) ⟨1106231, by rfl⟩ : syracuseStep 1474975 = 2212463) B2212463
theorem B2212319 : Blo 1474557 2212319 := bstep (se 1 (by rfl) ⟨1659239, by rfl⟩ : syracuseStep 2212319 = 3318479) B3318479
theorem B2212571 : Blo 1474557 2212571 := bstep (se 1 (by rfl) ⟨1659428, by rfl⟩ : syracuseStep 2212571 = 3318857) B3318857
theorem B3318497 : Blo 1474557 3318497 := bstep (se 2 (by rfl) ⟨1244436, by rfl⟩ : syracuseStep 3318497 = 2488873) B2488873
theorem B1475391 : Blo 1474557 1475391 := bstep (se 1 (by rfl) ⟨1106543, by rfl⟩ : syracuseStep 1475391 = 2213087) B2213087
theorem B1475399 : Blo 1474557 1475399 := bstep (se 1 (by rfl) ⟨1106549, by rfl⟩ : syracuseStep 1475399 = 2213099) B2213099
theorem B19162169 : Blo 1474557 19162169 := bstep (se 2 (by rfl) ⟨7185813, by rfl⟩ : syracuseStep 19162169 = 14371627) B14371627
theorem B3736631 : Blo 1474557 3736631 := bstep (se 1 (by rfl) ⟨2802473, by rfl⟩ : syracuseStep 3736631 = 5604947) B5604947
theorem B1475655 : Blo 1474557 1475655 := bstep (se 1 (by rfl) ⟨1106741, by rfl⟩ : syracuseStep 1475655 = 2213483) B2213483
theorem B25216109 : Blo 1474557 25216109 := bstep (se 3 (by rfl) ⟨4728020, by rfl⟩ : syracuseStep 25216109 = 9456041) B9456041
theorem B2212985 : Blo 1474557 2212985 := bstep (se 2 (by rfl) ⟨829869, by rfl⟩ : syracuseStep 2212985 = 1659739) B1659739
theorem B3196025 : Blo 1474557 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B1475711 : Blo 1474557 1475711 := bstep (se 1 (by rfl) ⟨1106783, by rfl⟩ : syracuseStep 1475711 = 2213567) B2213567
theorem B2491519 : Blo 1474557 2491519 := bstep (se 1 (by rfl) ⟨1868639, by rfl⟩ : syracuseStep 2491519 = 3737279) B3737279
theorem B9102461 : Blo 1474557 9102461 := bstep (se 3 (by rfl) ⟨1706711, by rfl⟩ : syracuseStep 9102461 = 3413423) B3413423
theorem B1475835 : Blo 1474557 1475835 := bstep (se 1 (by rfl) ⟨1106876, by rfl⟩ : syracuseStep 1475835 = 2213753) B2213753
theorem B2213183 : Blo 1474557 2213183 := bstep (se 1 (by rfl) ⟨1659887, by rfl⟩ : syracuseStep 2213183 = 3319775) B3319775
theorem B14181911 : Blo 1474557 14181911 := bstep (se 1 (by rfl) ⟨10636433, by rfl⟩ : syracuseStep 14181911 = 21272867) B21272867
theorem B7972481 : Blo 1474557 7972481 := bstep (se 2 (by rfl) ⟨2989680, by rfl⟩ : syracuseStep 7972481 = 5979361) B5979361
theorem B3319433 : Blo 1474557 3319433 := bstep (se 2 (by rfl) ⟨1244787, by rfl⟩ : syracuseStep 3319433 = 2489575) B2489575
theorem B3319487 : Blo 1474557 3319487 := bstep (se 1 (by rfl) ⟨2489615, by rfl⟩ : syracuseStep 3319487 = 4979231) B4979231
theorem B1476335 : Blo 1474557 1476335 := bstep (se 1 (by rfl) ⟨1107251, by rfl⟩ : syracuseStep 1476335 = 2214503) B2214503
theorem B1476463 : Blo 1474557 1476463 := bstep (se 1 (by rfl) ⟨1107347, by rfl⟩ : syracuseStep 1476463 = 2214695) B2214695
theorem B2213855 : Blo 1474557 2213855 := bstep (se 1 (by rfl) ⟨1660391, by rfl⟩ : syracuseStep 2213855 = 3320783) B3320783
theorem B2213915 : Blo 1474557 2213915 := bstep (se 1 (by rfl) ⟨1660436, by rfl⟩ : syracuseStep 2213915 = 3320873) B3320873
theorem B16812197 : Blo 1474557 16812197 := bstep (se 4 (by rfl) ⟨1576143, by rfl⟩ : syracuseStep 16812197 = 3152287) B3152287
theorem B2214071 : Blo 1474557 2214071 := bstep (se 1 (by rfl) ⟨1660553, by rfl⟩ : syracuseStep 2214071 = 3321107) B3321107
theorem B14371019 : Blo 1474557 14371019 := bstep (se 1 (by rfl) ⟨10778264, by rfl⟩ : syracuseStep 14371019 = 21556529) B21556529
theorem B2214095 : Blo 1474557 2214095 := bstep (se 1 (by rfl) ⟨1660571, by rfl⟩ : syracuseStep 2214095 = 3321143) B3321143
theorem B5318939 : Blo 1474557 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B15960361 : Blo 1474557 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B11200841 : Blo 1474557 11200841 := bstep (se 2 (by rfl) ⟨4200315, by rfl⟩ : syracuseStep 11200841 = 8400631) B8400631
theorem B7473545 : Blo 1474557 7473545 := bstep (se 2 (by rfl) ⟨2802579, by rfl⟩ : syracuseStep 7473545 = 5605159) B5605159
theorem B2214491 : Blo 1474557 2214491 := bstep (se 1 (by rfl) ⟨1660868, by rfl⟩ : syracuseStep 2214491 = 3321737) B3321737
theorem B2362063 : Blo 1474557 2362063 := bstep (se 1 (by rfl) ⟨1771547, by rfl⟩ : syracuseStep 2362063 = 3543095) B3543095
theorem B1575631 : Blo 1474557 1575631 := bstep (se 1 (by rfl) ⟨1181723, by rfl⟩ : syracuseStep 1575631 = 2363447) B2363447
theorem B2214635 : Blo 1474557 2214635 := bstep (se 1 (by rfl) ⟨1660976, by rfl⟩ : syracuseStep 2214635 = 3321953) B3321953
theorem B2214665 : Blo 1474557 2214665 := bstep (se 2 (by rfl) ⟨830499, by rfl⟩ : syracuseStep 2214665 = 1660999) B1660999
theorem B8399699 : Blo 1474557 8399699 := bstep (se 1 (by rfl) ⟨6299774, by rfl⟩ : syracuseStep 8399699 = 12599549) B12599549
theorem B6728609 : Blo 1474557 6728609 := bstep (se 2 (by rfl) ⟨2523228, by rfl⟩ : syracuseStep 6728609 = 5046457) B5046457
theorem B10636201 : Blo 1474557 10636201 := bstep (se 2 (by rfl) ⟨3988575, by rfl⟩ : syracuseStep 10636201 = 7977151) B7977151
theorem B63851651 : Blo 1474557 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B2362537 : Blo 1474557 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B5319863 : Blo 1474557 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B4730071 : Blo 1474557 4730071 := bstep (se 1 (by rfl) ⟨3547553, by rfl⟩ : syracuseStep 4730071 = 7095107) B7095107
theorem B18918643 : Blo 1474557 18918643 := bstep (se 1 (by rfl) ⟨14188982, by rfl⟩ : syracuseStep 18918643 = 28377965) B28377965
theorem B4042031 : Blo 1474557 4042031 := bstep (se 1 (by rfl) ⟨3031523, by rfl⟩ : syracuseStep 4042031 = 6063047) B6063047
theorem B3321215 : Blo 1474557 3321215 := bstep (se 1 (by rfl) ⟨2490911, by rfl⟩ : syracuseStep 3321215 = 4981823) B4981823
theorem B5598827 : Blo 1474557 5598827 := bstep (se 1 (by rfl) ⟨4199120, by rfl⟩ : syracuseStep 5598827 = 8398241) B8398241
theorem B11357981 : Blo 1474557 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B43110299 : Blo 1474557 43110299 := bstep (se 1 (by rfl) ⟨32332724, by rfl⟩ : syracuseStep 43110299 = 64665449) B64665449
theorem B3149759 : Blo 1474557 3149759 := bstep (se 1 (by rfl) ⟨2362319, by rfl⟩ : syracuseStep 3149759 = 4724639) B4724639
theorem B30281681 : Blo 1474557 30281681 := bstep (se 2 (by rfl) ⟨11355630, by rfl⟩ : syracuseStep 30281681 = 22711261) B22711261
theorem B12603545 : Blo 1474557 12603545 := bstep (se 2 (by rfl) ⟨4726329, by rfl⟩ : syracuseStep 12603545 = 9452659) B9452659
theorem B1994959 : Blo 1474557 1994959 := bstep (se 1 (by rfl) ⟨1496219, by rfl⟩ : syracuseStep 1994959 = 2992439) B2992439
theorem B3322169 : Blo 1474557 3322169 := bstep (se 2 (by rfl) ⟨1245813, by rfl⟩ : syracuseStep 3322169 = 2491627) B2491627
theorem B7467389 : Blo 1474557 7467389 := bstep (se 3 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 7467389 = 2800271) B2800271
theorem B1225822643 : Blo 1474557 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B1659847 : Blo 1474557 1659847 := bstep (se 1 (by rfl) ⟨1244885, by rfl⟩ : syracuseStep 1659847 = 2489771) B2489771
theorem B16815113 : Blo 1474557 16815113 := bstep (se 2 (by rfl) ⟨6305667, by rfl⟩ : syracuseStep 16815113 = 12611335) B12611335
theorem B4199519 : Blo 1474557 4199519 := bstep (se 1 (by rfl) ⟨3149639, by rfl⟩ : syracuseStep 4199519 = 6299279) B6299279
theorem B7468199 : Blo 1474557 7468199 := bstep (se 1 (by rfl) ⟨5601149, by rfl⟩ : syracuseStep 7468199 = 11202299) B11202299
theorem B1660207 : Blo 1474557 1660207 := bstep (se 1 (by rfl) ⟨1245155, by rfl⟩ : syracuseStep 1660207 = 2490311) B2490311
theorem B4199759 : Blo 1474557 4199759 := bstep (se 1 (by rfl) ⟨3149819, by rfl⟩ : syracuseStep 4199759 = 6299639) B6299639
theorem B4724075 : Blo 1474557 4724075 := bstep (se 1 (by rfl) ⟨3543056, by rfl⟩ : syracuseStep 4724075 = 7086113) B7086113
theorem B31888889 : Blo 1474557 31888889 := bstep (se 2 (by rfl) ⟨11958333, by rfl⟩ : syracuseStep 31888889 = 23916667) B23916667
theorem B8976025 : Blo 1474557 8976025 := bstep (se 2 (by rfl) ⟨3366009, by rfl⟩ : syracuseStep 8976025 = 6732019) B6732019
theorem B1660711 : Blo 1474557 1660711 := bstep (se 1 (by rfl) ⟨1245533, by rfl⟩ : syracuseStep 1660711 = 2491067) B2491067
theorem B12769271 : Blo 1474557 12769271 := bstep (se 1 (by rfl) ⟨9576953, by rfl⟩ : syracuseStep 12769271 = 19153907) B19153907
theorem B2488441 : Blo 1474557 2488441 := bstep (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) B1866331
theorem B2488495 : Blo 1474557 2488495 := bstep (se 1 (by rfl) ⟨1866371, by rfl⟩ : syracuseStep 2488495 = 3732743) B3732743
theorem B3733735 : Blo 1474557 3733735 := bstep (se 1 (by rfl) ⟨2800301, by rfl⟩ : syracuseStep 3733735 = 5600603) B5600603
theorem B8976827 : Blo 1474557 8976827 := bstep (se 1 (by rfl) ⟨6732620, by rfl⟩ : syracuseStep 8976827 = 13465241) B13465241
theorem B3734495 : Blo 1474557 3734495 := bstep (se 1 (by rfl) ⟨2800871, by rfl⟩ : syracuseStep 3734495 = 5601743) B5601743
theorem B8404073 : Blo 1474557 8404073 := bstep (se 2 (by rfl) ⟨3151527, by rfl⟩ : syracuseStep 8404073 = 6303055) B6303055
theorem B17947813 : Blo 1474557 17947813 := bstep (se 4 (by rfl) ⟨1682607, by rfl⟩ : syracuseStep 17947813 = 3365215) B3365215
theorem B4979987 : Blo 1474557 4979987 := bstep (se 1 (by rfl) ⟨3734990, by rfl⟩ : syracuseStep 4979987 = 7469981) B7469981
theorem B18906857 : Blo 1474557 18906857 := bstep (se 2 (by rfl) ⟨7090071, by rfl⟩ : syracuseStep 18906857 = 14180143) B14180143
theorem B2490203 : Blo 1474557 2490203 := bstep (se 1 (by rfl) ⟨1867652, by rfl⟩ : syracuseStep 2490203 = 3735305) B3735305
theorem B7470953 : Blo 1474557 7470953 := bstep (se 2 (by rfl) ⟨2801607, by rfl⟩ : syracuseStep 7470953 = 5603215) B5603215
theorem B2490223 : Blo 1474557 2490223 := bstep (se 1 (by rfl) ⟨1867667, by rfl⟩ : syracuseStep 2490223 = 3735335) B3735335
theorem B3547007 : Blo 1474557 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B1474651 : Blo 1474557 1474651 := bstep (se 1 (by rfl) ⟨1105988, by rfl⟩ : syracuseStep 1474651 = 2211977) B2211977
theorem B1474715 : Blo 1474557 1474715 := bstep (se 1 (by rfl) ⟨1106036, by rfl⟩ : syracuseStep 1474715 = 2212073) B2212073
theorem B3317921 : Blo 1474557 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B1867951 : Blo 1474557 1867951 := bstep (se 1 (by rfl) ⟨1400963, by rfl⟩ : syracuseStep 1867951 = 2801927) B2801927
theorem B5603519 : Blo 1474557 5603519 := bstep (se 1 (by rfl) ⟨4202639, by rfl⟩ : syracuseStep 5603519 = 8405279) B8405279
theorem B3317993 : Blo 1474557 3317993 := bstep (se 2 (by rfl) ⟨1244247, by rfl⟩ : syracuseStep 3317993 = 2488495) B2488495
theorem B1474799 : Blo 1474557 1474799 := bstep (se 1 (by rfl) ⟨1106099, by rfl⟩ : syracuseStep 1474799 = 2212199) B2212199
theorem B1474879 : Blo 1474557 1474879 := bstep (se 1 (by rfl) ⟨1106159, by rfl⟩ : syracuseStep 1474879 = 2212319) B2212319
theorem B24273229 : Blo 1474557 24273229 := bstep (se 3 (by rfl) ⟨4551230, by rfl⟩ : syracuseStep 24273229 = 9102461) B9102461
theorem B1475047 : Blo 1474557 1475047 := bstep (se 1 (by rfl) ⟨1106285, by rfl⟩ : syracuseStep 1475047 = 2212571) B2212571
theorem B2212331 : Blo 1474557 2212331 := bstep (se 1 (by rfl) ⟨1659248, by rfl⟩ : syracuseStep 2212331 = 3318497) B3318497
theorem B43114997 : Blo 1474557 43114997 := bstep (se 5 (by rfl) ⟨2021015, by rfl⟩ : syracuseStep 43114997 = 4042031) B4042031
theorem B2491087 : Blo 1474557 2491087 := bstep (se 1 (by rfl) ⟨1868315, by rfl⟩ : syracuseStep 2491087 = 3736631) B3736631
theorem B16810739 : Blo 1474557 16810739 := bstep (se 1 (by rfl) ⟨12608054, by rfl⟩ : syracuseStep 16810739 = 25216109) B25216109
theorem B1475323 : Blo 1474557 1475323 := bstep (se 1 (by rfl) ⟨1106492, by rfl⟩ : syracuseStep 1475323 = 2212985) B2212985
theorem B2130683 : Blo 1474557 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B1475455 : Blo 1474557 1475455 := bstep (se 1 (by rfl) ⟨1106591, by rfl⟩ : syracuseStep 1475455 = 2213183) B2213183
theorem B12600197 : Blo 1474557 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B21259259 : Blo 1474557 21259259 := bstep (se 1 (by rfl) ⟨15944444, by rfl⟩ : syracuseStep 21259259 = 31888889) B31888889
theorem B9454607 : Blo 1474557 9454607 := bstep (se 1 (by rfl) ⟨7090955, by rfl⟩ : syracuseStep 9454607 = 14181911) B14181911
theorem B2212955 : Blo 1474557 2212955 := bstep (se 1 (by rfl) ⟨1659716, by rfl⟩ : syracuseStep 2212955 = 3319433) B3319433
theorem B2212991 : Blo 1474557 2212991 := bstep (se 1 (by rfl) ⟨1659743, by rfl⟩ : syracuseStep 2212991 = 3319487) B3319487
theorem B2213129 : Blo 1474557 2213129 := bstep (se 2 (by rfl) ⟨829923, by rfl⟩ : syracuseStep 2213129 = 1659847) B1659847
theorem B1475903 : Blo 1474557 1475903 := bstep (se 1 (by rfl) ⟨1106927, by rfl⟩ : syracuseStep 1475903 = 2213855) B2213855
theorem B8512847 : Blo 1474557 8512847 := bstep (se 1 (by rfl) ⟨6384635, by rfl⟩ : syracuseStep 8512847 = 12769271) B12769271
theorem B1475943 : Blo 1474557 1475943 := bstep (se 1 (by rfl) ⟨1106957, by rfl⟩ : syracuseStep 1475943 = 2213915) B2213915
theorem B11208131 : Blo 1474557 11208131 := bstep (se 1 (by rfl) ⟨8406098, by rfl⟩ : syracuseStep 11208131 = 16812197) B16812197
theorem B1476047 : Blo 1474557 1476047 := bstep (se 1 (by rfl) ⟨1107035, by rfl⟩ : syracuseStep 1476047 = 2214071) B2214071
theorem B1476063 : Blo 1474557 1476063 := bstep (se 1 (by rfl) ⟨1107047, by rfl⟩ : syracuseStep 1476063 = 2214095) B2214095
theorem B23930417 : Blo 1474557 23930417 := bstep (se 2 (by rfl) ⟨8973906, by rfl⟩ : syracuseStep 23930417 = 17947813) B17947813
theorem B4982363 : Blo 1474557 4982363 := bstep (se 1 (by rfl) ⟨3736772, by rfl⟩ : syracuseStep 4982363 = 7473545) B7473545
theorem B25224857 : Blo 1474557 25224857 := bstep (se 2 (by rfl) ⟨9459321, by rfl⟩ : syracuseStep 25224857 = 18918643) B18918643
theorem B1476327 : Blo 1474557 1476327 := bstep (se 1 (by rfl) ⟨1107245, by rfl⟩ : syracuseStep 1476327 = 2214491) B2214491
theorem B2213609 : Blo 1474557 2213609 := bstep (se 2 (by rfl) ⟨830103, by rfl⟩ : syracuseStep 2213609 = 1660207) B1660207
theorem B1476423 : Blo 1474557 1476423 := bstep (se 1 (by rfl) ⟨1107317, by rfl⟩ : syracuseStep 1476423 = 2214635) B2214635
theorem B1476443 : Blo 1474557 1476443 := bstep (se 1 (by rfl) ⟨1107332, by rfl⟩ : syracuseStep 1476443 = 2214665) B2214665
theorem B42567767 : Blo 1474557 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B3319991 : Blo 1474557 3319991 := bstep (se 1 (by rfl) ⟨2489993, by rfl⟩ : syracuseStep 3319991 = 4979987) B4979987
theorem B2214143 : Blo 1474557 2214143 := bstep (se 1 (by rfl) ⟨1660607, by rfl⟩ : syracuseStep 2214143 = 3321215) B3321215
theorem B2214281 : Blo 1474557 2214281 := bstep (se 2 (by rfl) ⟨830355, by rfl⟩ : syracuseStep 2214281 = 1660711) B1660711
theorem B3320297 : Blo 1474557 3320297 := bstep (se 2 (by rfl) ⟨1245111, by rfl⟩ : syracuseStep 3320297 = 2490223) B2490223
theorem B7571987 : Blo 1474557 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B28740199 : Blo 1474557 28740199 := bstep (se 1 (by rfl) ⟨21555149, by rfl⟩ : syracuseStep 28740199 = 43110299) B43110299
theorem B2099839 : Blo 1474557 2099839 := bstep (se 1 (by rfl) ⟨1574879, by rfl⟩ : syracuseStep 2099839 = 3149759) B3149759
theorem B20187787 : Blo 1474557 20187787 := bstep (se 1 (by rfl) ⟨15140840, by rfl⟩ : syracuseStep 20187787 = 30281681) B30281681
theorem B2214779 : Blo 1474557 2214779 := bstep (se 1 (by rfl) ⟨1661084, by rfl⟩ : syracuseStep 2214779 = 3322169) B3322169
theorem B310946849 : Blo 1474557 310946849 := bstep (se 2 (by rfl) ⟨116605068, by rfl⟩ : syracuseStep 310946849 = 233210137) B233210137
theorem B11210075 : Blo 1474557 11210075 := bstep (se 1 (by rfl) ⟨8407556, by rfl⟩ : syracuseStep 11210075 = 16815113) B16815113
theorem B12774779 : Blo 1474557 12774779 := bstep (se 1 (by rfl) ⟨9581084, by rfl⟩ : syracuseStep 12774779 = 19162169) B19162169
theorem B3149383 : Blo 1474557 3149383 := bstep (se 1 (by rfl) ⟨2362037, by rfl⟩ : syracuseStep 3149383 = 4724075) B4724075
theorem B3149417 : Blo 1474557 3149417 := bstep (se 2 (by rfl) ⟨1181031, by rfl⟩ : syracuseStep 3149417 = 2362063) B2362063
theorem B9580679 : Blo 1474557 9580679 := bstep (se 1 (by rfl) ⟨7185509, by rfl⟩ : syracuseStep 9580679 = 14371019) B14371019
theorem B3322025 : Blo 1474557 3322025 := bstep (se 2 (by rfl) ⟨1245759, by rfl⟩ : syracuseStep 3322025 = 2491519) B2491519
theorem B7467227 : Blo 1474557 7467227 := bstep (se 1 (by rfl) ⟨5600420, by rfl⟩ : syracuseStep 7467227 = 11200841) B11200841
theorem B5984551 : Blo 1474557 5984551 := bstep (se 1 (by rfl) ⟨4488413, by rfl⟩ : syracuseStep 5984551 = 8976827) B8976827
theorem B5599799 : Blo 1474557 5599799 := bstep (se 1 (by rfl) ⟨4199849, by rfl⟩ : syracuseStep 5599799 = 8399699) B8399699
theorem B4485739 : Blo 1474557 4485739 := bstep (se 1 (by rfl) ⟨3364304, by rfl⟩ : syracuseStep 4485739 = 6728609) B6728609
theorem B56726405 : Blo 1474557 56726405 := bstep (se 4 (by rfl) ⟨5318100, by rfl⟩ : syracuseStep 56726405 = 10636201) B10636201
theorem B3732551 : Blo 1474557 3732551 := bstep (se 1 (by rfl) ⟨2799413, by rfl⟩ : syracuseStep 3732551 = 5598827) B5598827
theorem B12604571 : Blo 1474557 12604571 := bstep (se 1 (by rfl) ⟨9453428, by rfl⟩ : syracuseStep 12604571 = 18906857) B18906857
theorem B1660135 : Blo 1474557 1660135 := bstep (se 1 (by rfl) ⟨1245101, by rfl⟩ : syracuseStep 1660135 = 2490203) B2490203
theorem B2364671 : Blo 1474557 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B8402363 : Blo 1474557 8402363 := bstep (se 1 (by rfl) ⟨6301772, by rfl⟩ : syracuseStep 8402363 = 12603545) B12603545
theorem B4978259 : Blo 1474557 4978259 := bstep (se 1 (by rfl) ⟨3733694, by rfl⟩ : syracuseStep 4978259 = 7467389) B7467389
theorem B2659945 : Blo 1474557 2659945 := bstep (se 2 (by rfl) ⟨997479, by rfl⟩ : syracuseStep 2659945 = 1994959) B1994959
theorem B817215095 : Blo 1474557 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B4978313 : Blo 1474557 4978313 := bstep (se 2 (by rfl) ⟨1866867, by rfl⟩ : syracuseStep 4978313 = 3733735) B3733735
theorem B21280481 : Blo 1474557 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B2799679 : Blo 1474557 2799679 := bstep (se 1 (by rfl) ⟨2099759, by rfl⟩ : syracuseStep 2799679 = 4199519) B4199519
theorem B4978799 : Blo 1474557 4978799 := bstep (se 1 (by rfl) ⟨3734099, by rfl⟩ : syracuseStep 4978799 = 7468199) B7468199
theorem B47872133 : Blo 1474557 47872133 := bstep (se 4 (by rfl) ⟨4488012, by rfl⟩ : syracuseStep 47872133 = 8976025) B8976025
theorem B2799839 : Blo 1474557 2799839 := bstep (se 1 (by rfl) ⟨2099879, by rfl⟩ : syracuseStep 2799839 = 4199759) B4199759
theorem B8403365 : Blo 1474557 8403365 := bstep (se 4 (by rfl) ⟨787815, by rfl⟩ : syracuseStep 8403365 = 1575631) B1575631
theorem B5314987 : Blo 1474557 5314987 := bstep (se 1 (by rfl) ⟨3986240, by rfl⟩ : syracuseStep 5314987 = 7972481) B7972481
theorem B3545959 : Blo 1474557 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B6306761 : Blo 1474557 6306761 := bstep (se 2 (by rfl) ⟨2365035, by rfl⟩ : syracuseStep 6306761 = 4730071) B4730071
theorem B2489663 : Blo 1474557 2489663 := bstep (se 1 (by rfl) ⟨1867247, by rfl⟩ : syracuseStep 2489663 = 3734495) B3734495
theorem B5602715 : Blo 1474557 5602715 := bstep (se 1 (by rfl) ⟨4202036, by rfl⟩ : syracuseStep 5602715 = 8404073) B8404073
theorem B3546575 : Blo 1474557 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B4980635 : Blo 1474557 4980635 := bstep (se 1 (by rfl) ⟨3735476, by rfl⟩ : syracuseStep 4980635 = 7470953) B7470953
theorem B2211947 : Blo 1474557 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B3735679 : Blo 1474557 3735679 := bstep (se 1 (by rfl) ⟨2801759, by rfl⟩ : syracuseStep 3735679 = 5603519) B5603519
theorem B2211995 : Blo 1474557 2211995 := bstep (se 1 (by rfl) ⟨1658996, by rfl⟩ : syracuseStep 2211995 = 3317993) B3317993
theorem B2490601 : Blo 1474557 2490601 := bstep (se 2 (by rfl) ⟨933975, by rfl⟩ : syracuseStep 2490601 = 1867951) B1867951
theorem B1474887 : Blo 1474557 1474887 := bstep (se 1 (by rfl) ⟨1106165, by rfl⟩ : syracuseStep 1474887 = 2212331) B2212331
theorem B7979401 : Blo 1474557 7979401 := bstep (se 2 (by rfl) ⟨2992275, by rfl⟩ : syracuseStep 7979401 = 5984551) B5984551
theorem B11207159 : Blo 1474557 11207159 := bstep (se 1 (by rfl) ⟨8405369, by rfl⟩ : syracuseStep 11207159 = 16810739) B16810739
theorem B14172839 : Blo 1474557 14172839 := bstep (se 1 (by rfl) ⟨10629629, by rfl⟩ : syracuseStep 14172839 = 21259259) B21259259
theorem B1475303 : Blo 1474557 1475303 := bstep (se 1 (by rfl) ⟨1106477, by rfl⟩ : syracuseStep 1475303 = 2212955) B2212955
theorem B1475327 : Blo 1474557 1475327 := bstep (se 1 (by rfl) ⟨1106495, by rfl⟩ : syracuseStep 1475327 = 2212991) B2212991
theorem B5980985 : Blo 1474557 5980985 := bstep (se 2 (by rfl) ⟨2242869, by rfl⟩ : syracuseStep 5980985 = 4485739) B4485739
theorem B1475419 : Blo 1474557 1475419 := bstep (se 1 (by rfl) ⟨1106564, by rfl⟩ : syracuseStep 1475419 = 2213129) B2213129
theorem B7472087 : Blo 1474557 7472087 := bstep (se 1 (by rfl) ⟨5604065, by rfl⟩ : syracuseStep 7472087 = 11208131) B11208131
theorem B3318839 : Blo 1474557 3318839 := bstep (se 1 (by rfl) ⟨2489129, by rfl⟩ : syracuseStep 3318839 = 4978259) B4978259
theorem B544810063 : Blo 1474557 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B3318875 : Blo 1474557 3318875 := bstep (se 1 (by rfl) ⟨2489156, by rfl⟩ : syracuseStep 3318875 = 4978313) B4978313
theorem B4727945 : Blo 1474557 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B1475739 : Blo 1474557 1475739 := bstep (se 1 (by rfl) ⟨1106804, by rfl⟩ : syracuseStep 1475739 = 2213609) B2213609
theorem B28378511 : Blo 1474557 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B3319199 : Blo 1474557 3319199 := bstep (se 1 (by rfl) ⟨2489399, by rfl⟩ : syracuseStep 3319199 = 4978799) B4978799
theorem B2213327 : Blo 1474557 2213327 := bstep (se 1 (by rfl) ⟨1659995, by rfl⟩ : syracuseStep 2213327 = 3319991) B3319991
theorem B1476095 : Blo 1474557 1476095 := bstep (se 1 (by rfl) ⟨1107071, by rfl⟩ : syracuseStep 1476095 = 2214143) B2214143
theorem B1476187 : Blo 1474557 1476187 := bstep (se 1 (by rfl) ⟨1107140, by rfl⟩ : syracuseStep 1476187 = 2214281) B2214281
theorem B2213513 : Blo 1474557 2213513 := bstep (se 2 (by rfl) ⟨830067, by rfl⟩ : syracuseStep 2213513 = 1660135) B1660135
theorem B2213531 : Blo 1474557 2213531 := bstep (se 1 (by rfl) ⟨1660148, by rfl⟩ : syracuseStep 2213531 = 3320297) B3320297
theorem B5047991 : Blo 1474557 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B1476519 : Blo 1474557 1476519 := bstep (se 1 (by rfl) ⟨1107389, by rfl⟩ : syracuseStep 1476519 = 2214779) B2214779
theorem B28346597 : Blo 1474557 28346597 := bstep (se 4 (by rfl) ⟨2657493, by rfl⟩ : syracuseStep 28346597 = 5314987) B5314987
theorem B7473383 : Blo 1474557 7473383 := bstep (se 1 (by rfl) ⟨5605037, by rfl⟩ : syracuseStep 7473383 = 11210075) B11210075
theorem B2099611 : Blo 1474557 2099611 := bstep (se 1 (by rfl) ⟨1574708, by rfl⟩ : syracuseStep 2099611 = 3149417) B3149417
theorem B3320423 : Blo 1474557 3320423 := bstep (se 1 (by rfl) ⟨2490317, by rfl⟩ : syracuseStep 3320423 = 4980635) B4980635
theorem B2214683 : Blo 1474557 2214683 := bstep (se 1 (by rfl) ⟨1661012, by rfl⟩ : syracuseStep 2214683 = 3322025) B3322025
theorem B8400131 : Blo 1474557 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B37817603 : Blo 1474557 37817603 := bstep (se 1 (by rfl) ⟨28363202, by rfl⟩ : syracuseStep 37817603 = 56726405) B56726405
theorem B6303071 : Blo 1474557 6303071 := bstep (se 1 (by rfl) ⟨4727303, by rfl⟩ : syracuseStep 6303071 = 9454607) B9454607
theorem B3321449 : Blo 1474557 3321449 := bstep (se 2 (by rfl) ⟨1245543, by rfl⟩ : syracuseStep 3321449 = 2491087) B2491087
theorem B15953611 : Blo 1474557 15953611 := bstep (se 1 (by rfl) ⟨11965208, by rfl⟩ : syracuseStep 15953611 = 23930417) B23930417
theorem B3321575 : Blo 1474557 3321575 := bstep (se 1 (by rfl) ⟨2491181, by rfl⟩ : syracuseStep 3321575 = 4982363) B4982363
theorem B5681821 : Blo 1474557 5681821 := bstep (se 3 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 5681821 = 2130683) B2130683
theorem B4199177 : Blo 1474557 4199177 := bstep (se 2 (by rfl) ⟨1574691, by rfl⟩ : syracuseStep 4199177 = 3149383) B3149383
theorem B1659775 : Blo 1474557 1659775 := bstep (se 1 (by rfl) ⟨1244831, by rfl⟩ : syracuseStep 1659775 = 2489663) B2489663
theorem B8516519 : Blo 1474557 8516519 := bstep (se 1 (by rfl) ⟨6387389, by rfl⟩ : syracuseStep 8516519 = 12774779) B12774779
theorem B2364383 : Blo 1474557 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B3732905 : Blo 1474557 3732905 := bstep (se 2 (by rfl) ⟨1399839, by rfl⟩ : syracuseStep 3732905 = 2799679) B2799679
theorem B6387119 : Blo 1474557 6387119 := bstep (se 1 (by rfl) ⟨4790339, by rfl⟩ : syracuseStep 6387119 = 9580679) B9580679
theorem B4978151 : Blo 1474557 4978151 := bstep (se 1 (by rfl) ⟨3733613, by rfl⟩ : syracuseStep 4978151 = 7467227) B7467227
theorem B28743331 : Blo 1474557 28743331 := bstep (se 1 (by rfl) ⟨21557498, by rfl⟩ : syracuseStep 28743331 = 43114997) B43114997
theorem B3733199 : Blo 1474557 3733199 := bstep (se 1 (by rfl) ⟨2799899, by rfl⟩ : syracuseStep 3733199 = 5599799) B5599799
theorem B32364305 : Blo 1474557 32364305 := bstep (se 2 (by rfl) ⟨12136614, by rfl⟩ : syracuseStep 32364305 = 24273229) B24273229
theorem B6305789 : Blo 1474557 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B2488367 : Blo 1474557 2488367 := bstep (se 1 (by rfl) ⟨1866275, by rfl⟩ : syracuseStep 2488367 = 3732551) B3732551
theorem B8403047 : Blo 1474557 8403047 := bstep (se 1 (by rfl) ⟨6302285, by rfl⟩ : syracuseStep 8403047 = 12604571) B12604571
theorem B38320265 : Blo 1474557 38320265 := bstep (se 2 (by rfl) ⟨14370099, by rfl⟩ : syracuseStep 38320265 = 28740199) B28740199
theorem B2799785 : Blo 1474557 2799785 := bstep (se 2 (by rfl) ⟨1049919, by rfl⟩ : syracuseStep 2799785 = 2099839) B2099839
theorem B26917049 : Blo 1474557 26917049 := bstep (se 2 (by rfl) ⟨10093893, by rfl⟩ : syracuseStep 26917049 = 20187787) B20187787
theorem B5675231 : Blo 1474557 5675231 := bstep (se 1 (by rfl) ⟨4256423, by rfl⟩ : syracuseStep 5675231 = 8512847) B8512847
theorem B5601575 : Blo 1474557 5601575 := bstep (se 1 (by rfl) ⟨4201181, by rfl⟩ : syracuseStep 5601575 = 8402363) B8402363
theorem B16816571 : Blo 1474557 16816571 := bstep (se 1 (by rfl) ⟨12612428, by rfl⟩ : syracuseStep 16816571 = 25224857) B25224857
theorem B14186987 : Blo 1474557 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B31914755 : Blo 1474557 31914755 := bstep (se 1 (by rfl) ⟨23936066, by rfl⟩ : syracuseStep 31914755 = 47872133) B47872133
theorem B1866559 : Blo 1474557 1866559 := bstep (se 1 (by rfl) ⟨1399919, by rfl⟩ : syracuseStep 1866559 = 2799839) B2799839
theorem B5602243 : Blo 1474557 5602243 := bstep (se 1 (by rfl) ⟨4201682, by rfl⟩ : syracuseStep 5602243 = 8403365) B8403365
theorem B207297899 : Blo 1474557 207297899 := bstep (se 1 (by rfl) ⟨155473424, by rfl⟩ : syracuseStep 207297899 = 310946849) B310946849
theorem B3546593 : Blo 1474557 3546593 := bstep (se 2 (by rfl) ⟨1329972, by rfl⟩ : syracuseStep 3546593 = 2659945) B2659945
theorem B3735143 : Blo 1474557 3735143 := bstep (se 1 (by rfl) ⟨2801357, by rfl⟩ : syracuseStep 3735143 = 5602715) B5602715
theorem B16818029 : Blo 1474557 16818029 := bstep (se 3 (by rfl) ⟨3153380, by rfl⟩ : syracuseStep 16818029 = 6306761) B6306761
theorem B1474631 : Blo 1474557 1474631 := bstep (se 1 (by rfl) ⟨1105973, by rfl⟩ : syracuseStep 1474631 = 2211947) B2211947
theorem B1474663 : Blo 1474557 1474663 := bstep (se 1 (by rfl) ⟨1105997, by rfl⟩ : syracuseStep 1474663 = 2211995) B2211995
theorem B4980905 : Blo 1474557 4980905 := bstep (se 2 (by rfl) ⟨1867839, by rfl⟩ : syracuseStep 4980905 = 3735679) B3735679
theorem B7471439 : Blo 1474557 7471439 := bstep (se 1 (by rfl) ⟨5603579, by rfl⟩ : syracuseStep 7471439 = 11207159) B11207159
theorem B71778797 : Blo 1474557 71778797 := bstep (se 3 (by rfl) ⟨13458524, by rfl⟩ : syracuseStep 71778797 = 26917049) B26917049
theorem B5677679 : Blo 1474557 5677679 := bstep (se 1 (by rfl) ⟨4258259, by rfl⟩ : syracuseStep 5677679 = 8516519) B8516519
theorem B4981391 : Blo 1474557 4981391 := bstep (se 1 (by rfl) ⟨3736043, by rfl⟩ : syracuseStep 4981391 = 7472087) B7472087
theorem B2212559 : Blo 1474557 2212559 := bstep (se 1 (by rfl) ⟨1659419, by rfl⟩ : syracuseStep 2212559 = 3318839) B3318839
theorem B2212583 : Blo 1474557 2212583 := bstep (se 1 (by rfl) ⟨1659437, by rfl⟩ : syracuseStep 2212583 = 3318875) B3318875
theorem B2212799 : Blo 1474557 2212799 := bstep (se 1 (by rfl) ⟨1659599, by rfl⟩ : syracuseStep 2212799 = 3319199) B3319199
theorem B1475551 : Blo 1474557 1475551 := bstep (se 1 (by rfl) ⟨1106663, by rfl⟩ : syracuseStep 1475551 = 2213327) B2213327
theorem B3318767 : Blo 1474557 3318767 := bstep (se 1 (by rfl) ⟨2489075, by rfl⟩ : syracuseStep 3318767 = 4978151) B4978151
theorem B1475675 : Blo 1474557 1475675 := bstep (se 1 (by rfl) ⟨1106756, by rfl⟩ : syracuseStep 1475675 = 2213513) B2213513
theorem B1475687 : Blo 1474557 1475687 := bstep (se 1 (by rfl) ⟨1106765, by rfl⟩ : syracuseStep 1475687 = 2213531) B2213531
theorem B2213033 : Blo 1474557 2213033 := bstep (se 2 (by rfl) ⟨829887, by rfl⟩ : syracuseStep 2213033 = 1659775) B1659775
theorem B4203859 : Blo 1474557 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B4982255 : Blo 1474557 4982255 := bstep (se 1 (by rfl) ⟨3736691, by rfl⟩ : syracuseStep 4982255 = 7473383) B7473383
theorem B2213615 : Blo 1474557 2213615 := bstep (se 1 (by rfl) ⟨1660211, by rfl⟩ : syracuseStep 2213615 = 3320423) B3320423
theorem B21276503 : Blo 1474557 21276503 := bstep (se 1 (by rfl) ⟨15957377, by rfl⟩ : syracuseStep 21276503 = 31914755) B31914755
theorem B1476455 : Blo 1474557 1476455 := bstep (se 1 (by rfl) ⟨1107341, by rfl⟩ : syracuseStep 1476455 = 2214683) B2214683
theorem B38324441 : Blo 1474557 38324441 := bstep (se 2 (by rfl) ⟨14371665, by rfl⟩ : syracuseStep 38324441 = 28743331) B28743331
theorem B2214299 : Blo 1474557 2214299 := bstep (se 1 (by rfl) ⟨1660724, by rfl⟩ : syracuseStep 2214299 = 3321449) B3321449
theorem B2214383 : Blo 1474557 2214383 := bstep (se 1 (by rfl) ⟨1660787, by rfl⟩ : syracuseStep 2214383 = 3321575) B3321575
theorem B3320801 : Blo 1474557 3320801 := bstep (se 2 (by rfl) ⟨1245300, by rfl⟩ : syracuseStep 3320801 = 2490601) B2490601
theorem B7466093 : Blo 1474557 7466093 := bstep (se 3 (by rfl) ⟨1399892, by rfl⟩ : syracuseStep 7466093 = 2799785) B2799785
theorem B9448559 : Blo 1474557 9448559 := bstep (se 1 (by rfl) ⟨7086419, by rfl⟩ : syracuseStep 9448559 = 14172839) B14172839
theorem B15133949 : Blo 1474557 15133949 := bstep (se 3 (by rfl) ⟨2837615, by rfl⟩ : syracuseStep 15133949 = 5675231) B5675231
theorem B1576255 : Blo 1474557 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B18919007 : Blo 1474557 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B1658911 : Blo 1474557 1658911 := bstep (se 1 (by rfl) ⟨1244183, by rfl⟩ : syracuseStep 1658911 = 2488367) B2488367
theorem B25546843 : Blo 1474557 25546843 := bstep (se 1 (by rfl) ⟨19160132, by rfl⟩ : syracuseStep 25546843 = 38320265) B38320265
theorem B726413417 : Blo 1474557 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B11211047 : Blo 1474557 11211047 := bstep (se 1 (by rfl) ⟨8408285, by rfl⟩ : syracuseStep 11211047 = 16816571) B16816571
theorem B9457991 : Blo 1474557 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B5600087 : Blo 1474557 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B25211735 : Blo 1474557 25211735 := bstep (se 1 (by rfl) ⟨18908801, by rfl⟩ : syracuseStep 25211735 = 37817603) B37817603
theorem B21271481 : Blo 1474557 21271481 := bstep (se 2 (by rfl) ⟨7976805, by rfl⟩ : syracuseStep 21271481 = 15953611) B15953611
theorem B2364395 : Blo 1474557 2364395 := bstep (se 1 (by rfl) ⟨1773296, by rfl⟩ : syracuseStep 2364395 = 3546593) B3546593
theorem B11212019 : Blo 1474557 11212019 := bstep (se 1 (by rfl) ⟨8409014, by rfl⟩ : syracuseStep 11212019 = 16818029) B16818029
theorem B2799451 : Blo 1474557 2799451 := bstep (se 1 (by rfl) ⟨2099588, by rfl⟩ : syracuseStep 2799451 = 4199177) B4199177
theorem B10639201 : Blo 1474557 10639201 := bstep (se 2 (by rfl) ⟨3989700, by rfl⟩ : syracuseStep 10639201 = 7979401) B7979401
theorem B3987323 : Blo 1474557 3987323 := bstep (se 1 (by rfl) ⟨2990492, by rfl⟩ : syracuseStep 3987323 = 5980985) B5980985
theorem B3151963 : Blo 1474557 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B7575761 : Blo 1474557 7575761 := bstep (se 2 (by rfl) ⟨2840910, by rfl⟩ : syracuseStep 7575761 = 5681821) B5681821
theorem B2488603 : Blo 1474557 2488603 := bstep (se 1 (by rfl) ⟨1866452, by rfl⟩ : syracuseStep 2488603 = 3732905) B3732905
theorem B4258079 : Blo 1474557 4258079 := bstep (se 1 (by rfl) ⟨3193559, by rfl⟩ : syracuseStep 4258079 = 6387119) B6387119
theorem B2488745 : Blo 1474557 2488745 := bstep (se 2 (by rfl) ⟨933279, by rfl⟩ : syracuseStep 2488745 = 1866559) B1866559
theorem B3365327 : Blo 1474557 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2488799 : Blo 1474557 2488799 := bstep (se 1 (by rfl) ⟨1866599, by rfl⟩ : syracuseStep 2488799 = 3733199) B3733199
theorem B21576203 : Blo 1474557 21576203 := bstep (se 1 (by rfl) ⟨16182152, by rfl⟩ : syracuseStep 21576203 = 32364305) B32364305
theorem B7469657 : Blo 1474557 7469657 := bstep (se 2 (by rfl) ⟨2801121, by rfl⟩ : syracuseStep 7469657 = 5602243) B5602243
theorem B5602031 : Blo 1474557 5602031 := bstep (se 1 (by rfl) ⟨4201523, by rfl⟩ : syracuseStep 5602031 = 8403047) B8403047
theorem B18897731 : Blo 1474557 18897731 := bstep (se 1 (by rfl) ⟨14173298, by rfl⟩ : syracuseStep 18897731 = 28346597) B28346597
theorem B3734383 : Blo 1474557 3734383 := bstep (se 1 (by rfl) ⟨2800787, by rfl⟩ : syracuseStep 3734383 = 5601575) B5601575
theorem B11197925 : Blo 1474557 11197925 := bstep (se 4 (by rfl) ⟨1049805, by rfl⟩ : syracuseStep 11197925 = 2099611) B2099611
theorem B4202047 : Blo 1474557 4202047 := bstep (se 1 (by rfl) ⟨3151535, by rfl⟩ : syracuseStep 4202047 = 6303071) B6303071
theorem B138198599 : Blo 1474557 138198599 := bstep (se 1 (by rfl) ⟨103648949, by rfl⟩ : syracuseStep 138198599 = 207297899) B207297899
theorem B2490095 : Blo 1474557 2490095 := bstep (se 1 (by rfl) ⟨1867571, by rfl⟩ : syracuseStep 2490095 = 3735143) B3735143
theorem B2211881 : Blo 1474557 2211881 := bstep (se 2 (by rfl) ⟨829455, by rfl⟩ : syracuseStep 2211881 = 1658911) B1658911
theorem B34062457 : Blo 1474557 34062457 := bstep (se 2 (by rfl) ⟨12773421, by rfl⟩ : syracuseStep 34062457 = 25546843) B25546843
theorem B4202617 : Blo 1474557 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B4980959 : Blo 1474557 4980959 := bstep (se 1 (by rfl) ⟨3735719, by rfl⟩ : syracuseStep 4980959 = 7471439) B7471439
theorem B3318137 : Blo 1474557 3318137 := bstep (se 2 (by rfl) ⟨1244301, by rfl⟩ : syracuseStep 3318137 = 2488603) B2488603
theorem B3785119 : Blo 1474557 3785119 := bstep (se 1 (by rfl) ⟨2838839, by rfl⟩ : syracuseStep 3785119 = 5677679) B5677679
theorem B1475039 : Blo 1474557 1475039 := bstep (se 1 (by rfl) ⟨1106279, by rfl⟩ : syracuseStep 1475039 = 2212559) B2212559
theorem B1475055 : Blo 1474557 1475055 := bstep (se 1 (by rfl) ⟨1106291, by rfl⟩ : syracuseStep 1475055 = 2212583) B2212583
theorem B14180987 : Blo 1474557 14180987 := bstep (se 1 (by rfl) ⟨10635740, by rfl⟩ : syracuseStep 14180987 = 21271481) B21271481
theorem B1475199 : Blo 1474557 1475199 := bstep (se 1 (by rfl) ⟨1106399, by rfl⟩ : syracuseStep 1475199 = 2212799) B2212799
theorem B2212511 : Blo 1474557 2212511 := bstep (se 1 (by rfl) ⟨1659383, by rfl⟩ : syracuseStep 2212511 = 3318767) B3318767
theorem B1475355 : Blo 1474557 1475355 := bstep (se 1 (by rfl) ⟨1106516, by rfl⟩ : syracuseStep 1475355 = 2213033) B2213033
theorem B1475743 : Blo 1474557 1475743 := bstep (se 1 (by rfl) ⟨1106807, by rfl⟩ : syracuseStep 1475743 = 2213615) B2213615
theorem B1476199 : Blo 1474557 1476199 := bstep (se 1 (by rfl) ⟨1107149, by rfl⟩ : syracuseStep 1476199 = 2214299) B2214299
theorem B1476255 : Blo 1474557 1476255 := bstep (se 1 (by rfl) ⟨1107191, by rfl⟩ : syracuseStep 1476255 = 2214383) B2214383
theorem B5605145 : Blo 1474557 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B2213867 : Blo 1474557 2213867 := bstep (se 1 (by rfl) ⟨1660400, by rfl⟩ : syracuseStep 2213867 = 3320801) B3320801
theorem B7465283 : Blo 1474557 7465283 := bstep (se 1 (by rfl) ⟨5598962, by rfl⟩ : syracuseStep 7465283 = 11197925) B11197925
theorem B3320603 : Blo 1474557 3320603 := bstep (se 1 (by rfl) ⟨2490452, by rfl⟩ : syracuseStep 3320603 = 4980905) B4980905
theorem B7474031 : Blo 1474557 7474031 := bstep (se 1 (by rfl) ⟨5605523, by rfl⟩ : syracuseStep 7474031 = 11211047) B11211047
theorem B47852531 : Blo 1474557 47852531 := bstep (se 1 (by rfl) ⟨35889398, by rfl⟩ : syracuseStep 47852531 = 71778797) B71778797
theorem B3320927 : Blo 1474557 3320927 := bstep (se 1 (by rfl) ⟨2490695, by rfl⟩ : syracuseStep 3320927 = 4981391) B4981391
theorem B7474679 : Blo 1474557 7474679 := bstep (se 1 (by rfl) ⟨5606009, by rfl⟩ : syracuseStep 7474679 = 11212019) B11212019
theorem B3321503 : Blo 1474557 3321503 := bstep (se 1 (by rfl) ⟨2491127, by rfl⟩ : syracuseStep 3321503 = 4982255) B4982255
theorem B14184335 : Blo 1474557 14184335 := bstep (se 1 (by rfl) ⟨10638251, by rfl⟩ : syracuseStep 14184335 = 21276503) B21276503
theorem B2658215 : Blo 1474557 2658215 := bstep (se 1 (by rfl) ⟨1993661, by rfl⟩ : syracuseStep 2658215 = 3987323) B3987323
theorem B5050507 : Blo 1474557 5050507 := bstep (se 1 (by rfl) ⟨3787880, by rfl⟩ : syracuseStep 5050507 = 7575761) B7575761
theorem B2838719 : Blo 1474557 2838719 := bstep (se 1 (by rfl) ⟨2129039, by rfl⟩ : syracuseStep 2838719 = 4258079) B4258079
theorem B1659163 : Blo 1474557 1659163 := bstep (se 1 (by rfl) ⟨1244372, by rfl⟩ : syracuseStep 1659163 = 2488745) B2488745
theorem B1659199 : Blo 1474557 1659199 := bstep (se 1 (by rfl) ⟨1244399, by rfl⟩ : syracuseStep 1659199 = 2488799) B2488799
theorem B2101673 : Blo 1474557 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B4977395 : Blo 1474557 4977395 := bstep (se 1 (by rfl) ⟨3733046, by rfl⟩ : syracuseStep 4977395 = 7466093) B7466093
theorem B10089299 : Blo 1474557 10089299 := bstep (se 1 (by rfl) ⟨7566974, by rfl⟩ : syracuseStep 10089299 = 15133949) B15133949
theorem B92132399 : Blo 1474557 92132399 := bstep (se 1 (by rfl) ⟨69099299, by rfl⟩ : syracuseStep 92132399 = 138198599) B138198599
theorem B12612671 : Blo 1474557 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B3732601 : Blo 1474557 3732601 := bstep (se 2 (by rfl) ⟨1399725, by rfl⟩ : syracuseStep 3732601 = 2799451) B2799451
theorem B14185601 : Blo 1474557 14185601 := bstep (se 2 (by rfl) ⟨5319600, by rfl⟩ : syracuseStep 14185601 = 10639201) B10639201
theorem B1660063 : Blo 1474557 1660063 := bstep (se 1 (by rfl) ⟨1245047, by rfl⟩ : syracuseStep 1660063 = 2490095) B2490095
theorem B6305053 : Blo 1474557 6305053 := bstep (se 3 (by rfl) ⟨1182197, by rfl⟩ : syracuseStep 6305053 = 2364395) B2364395
theorem B484275611 : Blo 1474557 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B6305327 : Blo 1474557 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B3733391 : Blo 1474557 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B16807823 : Blo 1474557 16807823 := bstep (se 1 (by rfl) ⟨12605867, by rfl⟩ : syracuseStep 16807823 = 25211735) B25211735
theorem B4979177 : Blo 1474557 4979177 := bstep (se 2 (by rfl) ⟨1867191, by rfl⟩ : syracuseStep 4979177 = 3734383) B3734383
theorem B25549627 : Blo 1474557 25549627 := bstep (se 1 (by rfl) ⟨19162220, by rfl⟩ : syracuseStep 25549627 = 38324441) B38324441
theorem B2243551 : Blo 1474557 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B14384135 : Blo 1474557 14384135 := bstep (se 1 (by rfl) ⟨10788101, by rfl⟩ : syracuseStep 14384135 = 21576203) B21576203
theorem B4979771 : Blo 1474557 4979771 := bstep (se 1 (by rfl) ⟨3734828, by rfl⟩ : syracuseStep 4979771 = 7469657) B7469657
theorem B3734687 : Blo 1474557 3734687 := bstep (se 1 (by rfl) ⟨2801015, by rfl⟩ : syracuseStep 3734687 = 5602031) B5602031
theorem B12598487 : Blo 1474557 12598487 := bstep (se 1 (by rfl) ⟨9448865, by rfl⟩ : syracuseStep 12598487 = 18897731) B18897731
theorem B6299039 : Blo 1474557 6299039 := bstep (se 1 (by rfl) ⟨4724279, by rfl⟩ : syracuseStep 6299039 = 9448559) B9448559
theorem B5602729 : Blo 1474557 5602729 := bstep (se 2 (by rfl) ⟨2101023, by rfl⟩ : syracuseStep 5602729 = 4202047) B4202047
theorem B1474587 : Blo 1474557 1474587 := bstep (se 1 (by rfl) ⟨1105940, by rfl⟩ : syracuseStep 1474587 = 2211881) B2211881
theorem B1892479 : Blo 1474557 1892479 := bstep (se 1 (by rfl) ⟨1419359, by rfl⟩ : syracuseStep 1892479 = 2838719) B2838719
theorem B45416609 : Blo 1474557 45416609 := bstep (se 2 (by rfl) ⟨17031228, by rfl⟩ : syracuseStep 45416609 = 34062457) B34062457
theorem B5603489 : Blo 1474557 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B6734009 : Blo 1474557 6734009 := bstep (se 2 (by rfl) ⟨2525253, by rfl⟩ : syracuseStep 6734009 = 5050507) B5050507
theorem B2212091 : Blo 1474557 2212091 := bstep (se 1 (by rfl) ⟨1659068, by rfl⟩ : syracuseStep 2212091 = 3318137) B3318137
theorem B2212217 : Blo 1474557 2212217 := bstep (se 2 (by rfl) ⟨829581, by rfl⟩ : syracuseStep 2212217 = 1659163) B1659163
theorem B2212265 : Blo 1474557 2212265 := bstep (se 2 (by rfl) ⟨829599, by rfl⟩ : syracuseStep 2212265 = 1659199) B1659199
theorem B9453991 : Blo 1474557 9453991 := bstep (se 1 (by rfl) ⟨7090493, by rfl⟩ : syracuseStep 9453991 = 14180987) B14180987
theorem B1475007 : Blo 1474557 1475007 := bstep (se 1 (by rfl) ⟨1106255, by rfl⟩ : syracuseStep 1475007 = 2212511) B2212511
theorem B3318263 : Blo 1474557 3318263 := bstep (se 1 (by rfl) ⟨2488697, by rfl⟩ : syracuseStep 3318263 = 4977395) B4977395
theorem B6726199 : Blo 1474557 6726199 := bstep (se 1 (by rfl) ⟨5044649, by rfl⟩ : syracuseStep 6726199 = 10089299) B10089299
theorem B4203551 : Blo 1474557 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B5604461 : Blo 1474557 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B3736763 : Blo 1474557 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B2991401 : Blo 1474557 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B1475911 : Blo 1474557 1475911 := bstep (se 1 (by rfl) ⟨1106933, by rfl⟩ : syracuseStep 1475911 = 2213867) B2213867
theorem B2213417 : Blo 1474557 2213417 := bstep (se 2 (by rfl) ⟨830031, by rfl⟩ : syracuseStep 2213417 = 1660063) B1660063
theorem B3319451 : Blo 1474557 3319451 := bstep (se 1 (by rfl) ⟨2489588, by rfl⟩ : syracuseStep 3319451 = 4979177) B4979177
theorem B8406737 : Blo 1474557 8406737 := bstep (se 2 (by rfl) ⟨3152526, by rfl⟩ : syracuseStep 8406737 = 6305053) B6305053
theorem B2213735 : Blo 1474557 2213735 := bstep (se 1 (by rfl) ⟨1660301, by rfl⟩ : syracuseStep 2213735 = 3320603) B3320603
theorem B4982687 : Blo 1474557 4982687 := bstep (se 1 (by rfl) ⟨3737015, by rfl⟩ : syracuseStep 4982687 = 7474031) B7474031
theorem B31901687 : Blo 1474557 31901687 := bstep (se 1 (by rfl) ⟨23926265, by rfl⟩ : syracuseStep 31901687 = 47852531) B47852531
theorem B3319847 : Blo 1474557 3319847 := bstep (se 1 (by rfl) ⟨2489885, by rfl⟩ : syracuseStep 3319847 = 4979771) B4979771
theorem B2213951 : Blo 1474557 2213951 := bstep (se 1 (by rfl) ⟨1660463, by rfl⟩ : syracuseStep 2213951 = 3320927) B3320927
theorem B8398991 : Blo 1474557 8398991 := bstep (se 1 (by rfl) ⟨6299243, by rfl⟩ : syracuseStep 8398991 = 12598487) B12598487
theorem B20187301 : Blo 1474557 20187301 := bstep (se 4 (by rfl) ⟨1892559, by rfl⟩ : syracuseStep 20187301 = 3785119) B3785119
theorem B4983119 : Blo 1474557 4983119 := bstep (se 1 (by rfl) ⟨3737339, by rfl⟩ : syracuseStep 4983119 = 7474679) B7474679
theorem B7088573 : Blo 1474557 7088573 := bstep (se 3 (by rfl) ⟨1329107, by rfl⟩ : syracuseStep 7088573 = 2658215) B2658215
theorem B2214335 : Blo 1474557 2214335 := bstep (se 1 (by rfl) ⟨1660751, by rfl⟩ : syracuseStep 2214335 = 3321503) B3321503
theorem B9456223 : Blo 1474557 9456223 := bstep (se 1 (by rfl) ⟨7092167, by rfl⟩ : syracuseStep 9456223 = 14184335) B14184335
theorem B3320639 : Blo 1474557 3320639 := bstep (se 1 (by rfl) ⟨2490479, by rfl⟩ : syracuseStep 3320639 = 4980959) B4980959
theorem B8408447 : Blo 1474557 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B9457067 : Blo 1474557 9457067 := bstep (se 1 (by rfl) ⟨7092800, by rfl⟩ : syracuseStep 9457067 = 14185601) B14185601
theorem B322850407 : Blo 1474557 322850407 := bstep (se 1 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 322850407 = 484275611) B484275611
theorem B34066169 : Blo 1474557 34066169 := bstep (se 2 (by rfl) ⟨12774813, by rfl⟩ : syracuseStep 34066169 = 25549627) B25549627
theorem B4976801 : Blo 1474557 4976801 := bstep (se 2 (by rfl) ⟨1866300, by rfl⟩ : syracuseStep 4976801 = 3732601) B3732601
theorem B4976855 : Blo 1474557 4976855 := bstep (se 1 (by rfl) ⟨3732641, by rfl⟩ : syracuseStep 4976855 = 7465283) B7465283
theorem B9589423 : Blo 1474557 9589423 := bstep (se 1 (by rfl) ⟨7192067, by rfl⟩ : syracuseStep 9589423 = 14384135) B14384135
theorem B4199359 : Blo 1474557 4199359 := bstep (se 1 (by rfl) ⟨3149519, by rfl⟩ : syracuseStep 4199359 = 6299039) B6299039
theorem B61421599 : Blo 1474557 61421599 := bstep (se 1 (by rfl) ⟨46066199, by rfl⟩ : syracuseStep 61421599 = 92132399) B92132399
theorem B2488927 : Blo 1474557 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B11205215 : Blo 1474557 11205215 := bstep (se 1 (by rfl) ⟨8403911, by rfl⟩ : syracuseStep 11205215 = 16807823) B16807823
theorem B7470305 : Blo 1474557 7470305 := bstep (se 2 (by rfl) ⟨2801364, by rfl⟩ : syracuseStep 7470305 = 5602729) B5602729
theorem B2489791 : Blo 1474557 2489791 := bstep (se 1 (by rfl) ⟨1867343, by rfl⟩ : syracuseStep 2489791 = 3734687) B3734687
theorem B81895465 : Blo 1474557 81895465 := bstep (se 2 (by rfl) ⟨30710799, by rfl⟩ : syracuseStep 81895465 = 61421599) B61421599
theorem B3317867 : Blo 1474557 3317867 := bstep (se 1 (by rfl) ⟨2488400, by rfl⟩ : syracuseStep 3317867 = 4976801) B4976801
theorem B30277739 : Blo 1474557 30277739 := bstep (se 1 (by rfl) ⟨22708304, by rfl⟩ : syracuseStep 30277739 = 45416609) B45416609
theorem B3735659 : Blo 1474557 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B3317903 : Blo 1474557 3317903 := bstep (se 1 (by rfl) ⟨2488427, by rfl⟩ : syracuseStep 3317903 = 4976855) B4976855
theorem B1474727 : Blo 1474557 1474727 := bstep (se 1 (by rfl) ⟨1106045, by rfl⟩ : syracuseStep 1474727 = 2212091) B2212091
theorem B2523305 : Blo 1474557 2523305 := bstep (se 2 (by rfl) ⟨946239, by rfl⟩ : syracuseStep 2523305 = 1892479) B1892479
theorem B1474811 : Blo 1474557 1474811 := bstep (se 1 (by rfl) ⟨1106108, by rfl⟩ : syracuseStep 1474811 = 2212217) B2212217
theorem B1474843 : Blo 1474557 1474843 := bstep (se 1 (by rfl) ⟨1106132, by rfl⟩ : syracuseStep 1474843 = 2212265) B2212265
theorem B2212175 : Blo 1474557 2212175 := bstep (se 1 (by rfl) ⟨1659131, by rfl⟩ : syracuseStep 2212175 = 3318263) B3318263
theorem B2802367 : Blo 1474557 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B3736307 : Blo 1474557 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B2491175 : Blo 1474557 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B3318569 : Blo 1474557 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B12608297 : Blo 1474557 12608297 := bstep (se 2 (by rfl) ⟨4728111, by rfl⟩ : syracuseStep 12608297 = 9456223) B9456223
theorem B1475611 : Blo 1474557 1475611 := bstep (se 1 (by rfl) ⟨1106708, by rfl⟩ : syracuseStep 1475611 = 2213417) B2213417
theorem B2212967 : Blo 1474557 2212967 := bstep (se 1 (by rfl) ⟨1659725, by rfl⟩ : syracuseStep 2212967 = 3319451) B3319451
theorem B5604491 : Blo 1474557 5604491 := bstep (se 1 (by rfl) ⟨4203368, by rfl⟩ : syracuseStep 5604491 = 8406737) B8406737
theorem B1475823 : Blo 1474557 1475823 := bstep (se 1 (by rfl) ⟨1106867, by rfl⟩ : syracuseStep 1475823 = 2213735) B2213735
theorem B21267791 : Blo 1474557 21267791 := bstep (se 1 (by rfl) ⟨15950843, by rfl⟩ : syracuseStep 21267791 = 31901687) B31901687
theorem B2213231 : Blo 1474557 2213231 := bstep (se 1 (by rfl) ⟨1659923, by rfl⟩ : syracuseStep 2213231 = 3319847) B3319847
theorem B1475967 : Blo 1474557 1475967 := bstep (se 1 (by rfl) ⟨1106975, by rfl⟩ : syracuseStep 1475967 = 2213951) B2213951
theorem B4489339 : Blo 1474557 4489339 := bstep (se 1 (by rfl) ⟨3367004, by rfl⟩ : syracuseStep 4489339 = 6734009) B6734009
theorem B1476223 : Blo 1474557 1476223 := bstep (se 1 (by rfl) ⟨1107167, by rfl⟩ : syracuseStep 1476223 = 2214335) B2214335
theorem B2213759 : Blo 1474557 2213759 := bstep (se 1 (by rfl) ⟨1660319, by rfl⟩ : syracuseStep 2213759 = 3320639) B3320639
theorem B3319721 : Blo 1474557 3319721 := bstep (se 2 (by rfl) ⟨1244895, by rfl⟩ : syracuseStep 3319721 = 2489791) B2489791
theorem B430467209 : Blo 1474557 430467209 := bstep (se 2 (by rfl) ⟨161425203, by rfl⟩ : syracuseStep 430467209 = 322850407) B322850407
theorem B5605631 : Blo 1474557 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B22710779 : Blo 1474557 22710779 := bstep (se 1 (by rfl) ⟨17033084, by rfl⟩ : syracuseStep 22710779 = 34066169) B34066169
theorem B1994267 : Blo 1474557 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B5599145 : Blo 1474557 5599145 := bstep (se 2 (by rfl) ⟨2099679, by rfl⟩ : syracuseStep 5599145 = 4199359) B4199359
theorem B3321791 : Blo 1474557 3321791 := bstep (se 1 (by rfl) ⟨2491343, by rfl⟩ : syracuseStep 3321791 = 4982687) B4982687
theorem B5599327 : Blo 1474557 5599327 := bstep (se 1 (by rfl) ⟨4199495, by rfl⟩ : syracuseStep 5599327 = 8398991) B8398991
theorem B3322079 : Blo 1474557 3322079 := bstep (se 1 (by rfl) ⟨2491559, by rfl⟩ : syracuseStep 3322079 = 4983119) B4983119
theorem B6304711 : Blo 1474557 6304711 := bstep (se 1 (by rfl) ⟨4728533, by rfl⟩ : syracuseStep 6304711 = 9457067) B9457067
theorem B26916401 : Blo 1474557 26916401 := bstep (se 2 (by rfl) ⟨10093650, by rfl⟩ : syracuseStep 26916401 = 20187301) B20187301
theorem B12605321 : Blo 1474557 12605321 := bstep (se 2 (by rfl) ⟨4726995, by rfl⟩ : syracuseStep 12605321 = 9453991) B9453991
theorem B8968265 : Blo 1474557 8968265 := bstep (se 2 (by rfl) ⟨3363099, by rfl⟩ : syracuseStep 8968265 = 6726199) B6726199
theorem B12785897 : Blo 1474557 12785897 := bstep (se 2 (by rfl) ⟨4794711, by rfl⟩ : syracuseStep 12785897 = 9589423) B9589423
theorem B4725715 : Blo 1474557 4725715 := bstep (se 1 (by rfl) ⟨3544286, by rfl⟩ : syracuseStep 4725715 = 7088573) B7088573
theorem B7470143 : Blo 1474557 7470143 := bstep (se 1 (by rfl) ⟨5602607, by rfl⟩ : syracuseStep 7470143 = 11205215) B11205215
theorem B4980203 : Blo 1474557 4980203 := bstep (se 1 (by rfl) ⟨3735152, by rfl⟩ : syracuseStep 4980203 = 7470305) B7470305
theorem B2211911 : Blo 1474557 2211911 := bstep (se 1 (by rfl) ⟨1658933, by rfl⟩ : syracuseStep 2211911 = 3317867) B3317867
theorem B20185159 : Blo 1474557 20185159 := bstep (se 1 (by rfl) ⟨15138869, by rfl⟩ : syracuseStep 20185159 = 30277739) B30277739
theorem B2490439 : Blo 1474557 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B2211935 : Blo 1474557 2211935 := bstep (se 1 (by rfl) ⟨1658951, by rfl⟩ : syracuseStep 2211935 = 3317903) B3317903
theorem B1474783 : Blo 1474557 1474783 := bstep (se 1 (by rfl) ⟨1106087, by rfl⟩ : syracuseStep 1474783 = 2212175) B2212175
theorem B2490871 : Blo 1474557 2490871 := bstep (se 1 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 2490871 = 3736307) B3736307
theorem B2212379 : Blo 1474557 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B8405531 : Blo 1474557 8405531 := bstep (se 1 (by rfl) ⟨6304148, by rfl⟩ : syracuseStep 8405531 = 12608297) B12608297
theorem B34095725 : Blo 1474557 34095725 := bstep (se 3 (by rfl) ⟨6392948, by rfl⟩ : syracuseStep 34095725 = 12785897) B12785897
theorem B1475311 : Blo 1474557 1475311 := bstep (se 1 (by rfl) ⟨1106483, by rfl⟩ : syracuseStep 1475311 = 2212967) B2212967
theorem B3736327 : Blo 1474557 3736327 := bstep (se 1 (by rfl) ⟨2802245, by rfl⟩ : syracuseStep 3736327 = 5604491) B5604491
theorem B1475487 : Blo 1474557 1475487 := bstep (se 1 (by rfl) ⟨1106615, by rfl⟩ : syracuseStep 1475487 = 2213231) B2213231
theorem B3736489 : Blo 1474557 3736489 := bstep (se 2 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 3736489 = 2802367) B2802367
theorem B1475839 : Blo 1474557 1475839 := bstep (se 1 (by rfl) ⟨1106879, by rfl⟩ : syracuseStep 1475839 = 2213759) B2213759
theorem B8406281 : Blo 1474557 8406281 := bstep (se 2 (by rfl) ⟨3152355, by rfl⟩ : syracuseStep 8406281 = 6304711) B6304711
theorem B6300953 : Blo 1474557 6300953 := bstep (se 2 (by rfl) ⟨2362857, by rfl⟩ : syracuseStep 6300953 = 4725715) B4725715
theorem B2213147 : Blo 1474557 2213147 := bstep (se 1 (by rfl) ⟨1659860, by rfl⟩ : syracuseStep 2213147 = 3319721) B3319721
theorem B5318045 : Blo 1474557 5318045 := bstep (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) B1994267
theorem B3737087 : Blo 1474557 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B15140519 : Blo 1474557 15140519 := bstep (se 1 (by rfl) ⟨11355389, by rfl⟩ : syracuseStep 15140519 = 22710779) B22710779
theorem B3320135 : Blo 1474557 3320135 := bstep (se 1 (by rfl) ⟨2490101, by rfl⟩ : syracuseStep 3320135 = 4980203) B4980203
theorem B2214527 : Blo 1474557 2214527 := bstep (se 1 (by rfl) ⟨1660895, by rfl⟩ : syracuseStep 2214527 = 3321791) B3321791
theorem B109193953 : Blo 1474557 109193953 := bstep (se 2 (by rfl) ⟨40947732, by rfl⟩ : syracuseStep 109193953 = 81895465) B81895465
theorem B1682203 : Blo 1474557 1682203 := bstep (se 1 (by rfl) ⟨1261652, by rfl⟩ : syracuseStep 1682203 = 2523305) B2523305
theorem B7465769 : Blo 1474557 7465769 := bstep (se 2 (by rfl) ⟨2799663, by rfl⟩ : syracuseStep 7465769 = 5599327) B5599327
theorem B2214719 : Blo 1474557 2214719 := bstep (se 1 (by rfl) ⟨1661039, by rfl⟩ : syracuseStep 2214719 = 3322079) B3322079
theorem B17944267 : Blo 1474557 17944267 := bstep (se 1 (by rfl) ⟨13458200, by rfl⟩ : syracuseStep 17944267 = 26916401) B26916401
theorem B286978139 : Blo 1474557 286978139 := bstep (se 1 (by rfl) ⟨215233604, by rfl⟩ : syracuseStep 286978139 = 430467209) B430467209
theorem B3732763 : Blo 1474557 3732763 := bstep (se 1 (by rfl) ⟨2799572, by rfl⟩ : syracuseStep 3732763 = 5599145) B5599145
theorem B5985785 : Blo 1474557 5985785 := bstep (se 2 (by rfl) ⟨2244669, by rfl⟩ : syracuseStep 5985785 = 4489339) B4489339
theorem B1660783 : Blo 1474557 1660783 := bstep (se 1 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 1660783 = 2491175) B2491175
theorem B14178527 : Blo 1474557 14178527 := bstep (se 1 (by rfl) ⟨10633895, by rfl⟩ : syracuseStep 14178527 = 21267791) B21267791
theorem B8403547 : Blo 1474557 8403547 := bstep (se 1 (by rfl) ⟨6302660, by rfl⟩ : syracuseStep 8403547 = 12605321) B12605321
theorem B5978843 : Blo 1474557 5978843 := bstep (se 1 (by rfl) ⟨4484132, by rfl⟩ : syracuseStep 5978843 = 8968265) B8968265
theorem B4980095 : Blo 1474557 4980095 := bstep (se 1 (by rfl) ⟨3735071, by rfl⟩ : syracuseStep 4980095 = 7470143) B7470143
theorem B1474607 : Blo 1474557 1474607 := bstep (se 1 (by rfl) ⟨1105955, by rfl⟩ : syracuseStep 1474607 = 2211911) B2211911
theorem B1474623 : Blo 1474557 1474623 := bstep (se 1 (by rfl) ⟨1105967, by rfl⟩ : syracuseStep 1474623 = 2211935) B2211935
theorem B1474919 : Blo 1474557 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B5603687 : Blo 1474557 5603687 := bstep (se 1 (by rfl) ⟨4202765, by rfl⟩ : syracuseStep 5603687 = 8405531) B8405531
theorem B5604187 : Blo 1474557 5604187 := bstep (se 1 (by rfl) ⟨4203140, by rfl⟩ : syracuseStep 5604187 = 8406281) B8406281
theorem B1475431 : Blo 1474557 1475431 := bstep (se 1 (by rfl) ⟨1106573, by rfl⟩ : syracuseStep 1475431 = 2213147) B2213147
theorem B2491391 : Blo 1474557 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B4981769 : Blo 1474557 4981769 := bstep (se 2 (by rfl) ⟨1868163, by rfl⟩ : syracuseStep 4981769 = 3736327) B3736327
theorem B10093679 : Blo 1474557 10093679 := bstep (se 1 (by rfl) ⟨7570259, by rfl⟩ : syracuseStep 10093679 = 15140519) B15140519
theorem B4981985 : Blo 1474557 4981985 := bstep (se 2 (by rfl) ⟨1868244, by rfl⟩ : syracuseStep 4981985 = 3736489) B3736489
theorem B2213423 : Blo 1474557 2213423 := bstep (se 1 (by rfl) ⟨1660067, by rfl⟩ : syracuseStep 2213423 = 3320135) B3320135
theorem B1476351 : Blo 1474557 1476351 := bstep (se 1 (by rfl) ⟨1107263, by rfl⟩ : syracuseStep 1476351 = 2214527) B2214527
theorem B1476479 : Blo 1474557 1476479 := bstep (se 1 (by rfl) ⟨1107359, by rfl⟩ : syracuseStep 1476479 = 2214719) B2214719
theorem B3320063 : Blo 1474557 3320063 := bstep (se 1 (by rfl) ⟨2490047, by rfl⟩ : syracuseStep 3320063 = 4980095) B4980095
theorem B2214377 : Blo 1474557 2214377 := bstep (se 2 (by rfl) ⟨830391, by rfl⟩ : syracuseStep 2214377 = 1660783) B1660783
theorem B191318759 : Blo 1474557 191318759 := bstep (se 1 (by rfl) ⟨143489069, by rfl⟩ : syracuseStep 191318759 = 286978139) B286978139
theorem B26913545 : Blo 1474557 26913545 := bstep (se 2 (by rfl) ⟨10092579, by rfl⟩ : syracuseStep 26913545 = 20185159) B20185159
theorem B3320585 : Blo 1474557 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B3321161 : Blo 1474557 3321161 := bstep (se 2 (by rfl) ⟨1245435, by rfl⟩ : syracuseStep 3321161 = 2490871) B2490871
theorem B145591937 : Blo 1474557 145591937 := bstep (se 2 (by rfl) ⟨54596976, by rfl⟩ : syracuseStep 145591937 = 109193953) B109193953
theorem B15962093 : Blo 1474557 15962093 := bstep (se 3 (by rfl) ⟨2992892, by rfl⟩ : syracuseStep 15962093 = 5985785) B5985785
theorem B4977017 : Blo 1474557 4977017 := bstep (se 2 (by rfl) ⟨1866381, by rfl⟩ : syracuseStep 4977017 = 3732763) B3732763
theorem B3985895 : Blo 1474557 3985895 := bstep (se 1 (by rfl) ⟨2989421, by rfl⟩ : syracuseStep 3985895 = 5978843) B5978843
theorem B4977179 : Blo 1474557 4977179 := bstep (se 1 (by rfl) ⟨3732884, by rfl⟩ : syracuseStep 4977179 = 7465769) B7465769
theorem B23925689 : Blo 1474557 23925689 := bstep (se 2 (by rfl) ⟨8972133, by rfl⟩ : syracuseStep 23925689 = 17944267) B17944267
theorem B22730483 : Blo 1474557 22730483 := bstep (se 1 (by rfl) ⟨17047862, by rfl⟩ : syracuseStep 22730483 = 34095725) B34095725
theorem B11204729 : Blo 1474557 11204729 := bstep (se 2 (by rfl) ⟨4201773, by rfl⟩ : syracuseStep 11204729 = 8403547) B8403547
theorem B4200635 : Blo 1474557 4200635 := bstep (se 1 (by rfl) ⟨3150476, by rfl⟩ : syracuseStep 4200635 = 6300953) B6300953
theorem B3545363 : Blo 1474557 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B2242937 : Blo 1474557 2242937 := bstep (se 2 (by rfl) ⟨841101, by rfl⟩ : syracuseStep 2242937 = 1682203) B1682203
theorem B9452351 : Blo 1474557 9452351 := bstep (se 1 (by rfl) ⟨7089263, by rfl⟩ : syracuseStep 9452351 = 14178527) B14178527
theorem B3735791 : Blo 1474557 3735791 := bstep (se 1 (by rfl) ⟨2801843, by rfl⟩ : syracuseStep 3735791 = 5603687) B5603687
theorem B3318011 : Blo 1474557 3318011 := bstep (se 1 (by rfl) ⟨2488508, by rfl⟩ : syracuseStep 3318011 = 4977017) B4977017
theorem B3318119 : Blo 1474557 3318119 := bstep (se 1 (by rfl) ⟨2488589, by rfl⟩ : syracuseStep 3318119 = 4977179) B4977179
theorem B15950459 : Blo 1474557 15950459 := bstep (se 1 (by rfl) ⟨11962844, by rfl⟩ : syracuseStep 15950459 = 23925689) B23925689
theorem B5981165 : Blo 1474557 5981165 := bstep (se 3 (by rfl) ⟨1121468, by rfl⟩ : syracuseStep 5981165 = 2242937) B2242937
theorem B1475615 : Blo 1474557 1475615 := bstep (se 1 (by rfl) ⟨1106711, by rfl⟩ : syracuseStep 1475615 = 2213423) B2213423
theorem B7472249 : Blo 1474557 7472249 := bstep (se 2 (by rfl) ⟨2802093, by rfl⟩ : syracuseStep 7472249 = 5604187) B5604187
theorem B2213375 : Blo 1474557 2213375 := bstep (se 1 (by rfl) ⟨1660031, by rfl⟩ : syracuseStep 2213375 = 3320063) B3320063
theorem B1476251 : Blo 1474557 1476251 := bstep (se 1 (by rfl) ⟨1107188, by rfl⟩ : syracuseStep 1476251 = 2214377) B2214377
theorem B17942363 : Blo 1474557 17942363 := bstep (se 1 (by rfl) ⟨13456772, by rfl⟩ : syracuseStep 17942363 = 26913545) B26913545
theorem B2213723 : Blo 1474557 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B6301567 : Blo 1474557 6301567 := bstep (se 1 (by rfl) ⟨4726175, by rfl⟩ : syracuseStep 6301567 = 9452351) B9452351
theorem B2214107 : Blo 1474557 2214107 := bstep (se 1 (by rfl) ⟨1660580, by rfl⟩ : syracuseStep 2214107 = 3321161) B3321161
theorem B97061291 : Blo 1474557 97061291 := bstep (se 1 (by rfl) ⟨72795968, by rfl⟩ : syracuseStep 97061291 = 145591937) B145591937
theorem B3321179 : Blo 1474557 3321179 := bstep (se 1 (by rfl) ⟨2490884, by rfl⟩ : syracuseStep 3321179 = 4981769) B4981769
theorem B6729119 : Blo 1474557 6729119 := bstep (se 1 (by rfl) ⟨5046839, by rfl⟩ : syracuseStep 6729119 = 10093679) B10093679
theorem B3321323 : Blo 1474557 3321323 := bstep (se 1 (by rfl) ⟨2490992, by rfl⟩ : syracuseStep 3321323 = 4981985) B4981985
theorem B10629053 : Blo 1474557 10629053 := bstep (se 3 (by rfl) ⟨1992947, by rfl⟩ : syracuseStep 10629053 = 3985895) B3985895
theorem B2363575 : Blo 1474557 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B127545839 : Blo 1474557 127545839 := bstep (se 1 (by rfl) ⟨95659379, by rfl⟩ : syracuseStep 127545839 = 191318759) B191318759
theorem B1660927 : Blo 1474557 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B15153655 : Blo 1474557 15153655 := bstep (se 1 (by rfl) ⟨11365241, by rfl⟩ : syracuseStep 15153655 = 22730483) B22730483
theorem B7469819 : Blo 1474557 7469819 := bstep (se 1 (by rfl) ⟨5602364, by rfl⟩ : syracuseStep 7469819 = 11204729) B11204729
theorem B2800423 : Blo 1474557 2800423 := bstep (se 1 (by rfl) ⟨2100317, by rfl⟩ : syracuseStep 2800423 = 4200635) B4200635
theorem B10641395 : Blo 1474557 10641395 := bstep (se 1 (by rfl) ⟨7981046, by rfl⟩ : syracuseStep 10641395 = 15962093) B15962093
theorem B2490527 : Blo 1474557 2490527 := bstep (se 1 (by rfl) ⟨1867895, by rfl⟩ : syracuseStep 2490527 = 3735791) B3735791
theorem B2212007 : Blo 1474557 2212007 := bstep (se 1 (by rfl) ⟨1659005, by rfl⟩ : syracuseStep 2212007 = 3318011) B3318011
theorem B2212079 : Blo 1474557 2212079 := bstep (se 1 (by rfl) ⟨1659059, by rfl⟩ : syracuseStep 2212079 = 3318119) B3318119
theorem B10633639 : Blo 1474557 10633639 := bstep (se 1 (by rfl) ⟨7975229, by rfl⟩ : syracuseStep 10633639 = 15950459) B15950459
theorem B7094263 : Blo 1474557 7094263 := bstep (se 1 (by rfl) ⟨5320697, by rfl⟩ : syracuseStep 7094263 = 10641395) B10641395
theorem B4981499 : Blo 1474557 4981499 := bstep (se 1 (by rfl) ⟨3736124, by rfl⟩ : syracuseStep 4981499 = 7472249) B7472249
theorem B1475583 : Blo 1474557 1475583 := bstep (se 1 (by rfl) ⟨1106687, by rfl⟩ : syracuseStep 1475583 = 2213375) B2213375
theorem B11961575 : Blo 1474557 11961575 := bstep (se 1 (by rfl) ⟨8971181, by rfl⟩ : syracuseStep 11961575 = 17942363) B17942363
theorem B1475815 : Blo 1474557 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B1476071 : Blo 1474557 1476071 := bstep (se 1 (by rfl) ⟨1107053, by rfl⟩ : syracuseStep 1476071 = 2214107) B2214107
theorem B2214119 : Blo 1474557 2214119 := bstep (se 1 (by rfl) ⟨1660589, by rfl⟩ : syracuseStep 2214119 = 3321179) B3321179
theorem B2214215 : Blo 1474557 2214215 := bstep (se 1 (by rfl) ⟨1660661, by rfl⟩ : syracuseStep 2214215 = 3321323) B3321323
theorem B2214569 : Blo 1474557 2214569 := bstep (se 2 (by rfl) ⟨830463, by rfl⟩ : syracuseStep 2214569 = 1660927) B1660927
theorem B20204873 : Blo 1474557 20204873 := bstep (se 2 (by rfl) ⟨7576827, by rfl⟩ : syracuseStep 20204873 = 15153655) B15153655
theorem B4486079 : Blo 1474557 4486079 := bstep (se 1 (by rfl) ⟨3364559, by rfl⟩ : syracuseStep 4486079 = 6729119) B6729119
theorem B8402089 : Blo 1474557 8402089 := bstep (se 2 (by rfl) ⟨3150783, by rfl⟩ : syracuseStep 8402089 = 6301567) B6301567
theorem B3151433 : Blo 1474557 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B85030559 : Blo 1474557 85030559 := bstep (se 1 (by rfl) ⟨63772919, by rfl⟩ : syracuseStep 85030559 = 127545839) B127545839
theorem B3987443 : Blo 1474557 3987443 := bstep (se 1 (by rfl) ⟨2990582, by rfl⟩ : syracuseStep 3987443 = 5981165) B5981165
theorem B3733897 : Blo 1474557 3733897 := bstep (se 2 (by rfl) ⟨1400211, by rfl⟩ : syracuseStep 3733897 = 2800423) B2800423
theorem B64707527 : Blo 1474557 64707527 := bstep (se 1 (by rfl) ⟨48530645, by rfl⟩ : syracuseStep 64707527 = 97061291) B97061291
theorem B4979879 : Blo 1474557 4979879 := bstep (se 1 (by rfl) ⟨3734909, by rfl⟩ : syracuseStep 4979879 = 7469819) B7469819
theorem B7086035 : Blo 1474557 7086035 := bstep (se 1 (by rfl) ⟨5314526, by rfl⟩ : syracuseStep 7086035 = 10629053) B10629053
theorem B1474671 : Blo 1474557 1474671 := bstep (se 1 (by rfl) ⟨1106003, by rfl⟩ : syracuseStep 1474671 = 2212007) B2212007
theorem B1474719 : Blo 1474557 1474719 := bstep (se 1 (by rfl) ⟨1106039, by rfl⟩ : syracuseStep 1474719 = 2212079) B2212079
theorem B2990719 : Blo 1474557 2990719 := bstep (se 1 (by rfl) ⟨2243039, by rfl⟩ : syracuseStep 2990719 = 4486079) B4486079
theorem B1476079 : Blo 1474557 1476079 := bstep (se 1 (by rfl) ⟨1107059, by rfl⟩ : syracuseStep 1476079 = 2214119) B2214119
theorem B1476143 : Blo 1474557 1476143 := bstep (se 1 (by rfl) ⟨1107107, by rfl⟩ : syracuseStep 1476143 = 2214215) B2214215
theorem B1476379 : Blo 1474557 1476379 := bstep (se 1 (by rfl) ⟨1107284, by rfl⟩ : syracuseStep 1476379 = 2214569) B2214569
theorem B3319919 : Blo 1474557 3319919 := bstep (se 1 (by rfl) ⟨2489939, by rfl⟩ : syracuseStep 3319919 = 4979879) B4979879
theorem B13469915 : Blo 1474557 13469915 := bstep (se 1 (by rfl) ⟨10102436, by rfl⟩ : syracuseStep 13469915 = 20204873) B20204873
theorem B3320999 : Blo 1474557 3320999 := bstep (se 1 (by rfl) ⟨2490749, by rfl⟩ : syracuseStep 3320999 = 4981499) B4981499
theorem B7974383 : Blo 1474557 7974383 := bstep (se 1 (by rfl) ⟨5980787, by rfl⟩ : syracuseStep 7974383 = 11961575) B11961575
theorem B2658295 : Blo 1474557 2658295 := bstep (se 1 (by rfl) ⟨1993721, by rfl⟩ : syracuseStep 2658295 = 3987443) B3987443
theorem B11202785 : Blo 1474557 11202785 := bstep (se 2 (by rfl) ⟨4201044, by rfl⟩ : syracuseStep 11202785 = 8402089) B8402089
theorem B4724023 : Blo 1474557 4724023 := bstep (se 1 (by rfl) ⟨3543017, by rfl⟩ : syracuseStep 4724023 = 7086035) B7086035
theorem B9459017 : Blo 1474557 9459017 := bstep (se 2 (by rfl) ⟨3547131, by rfl⟩ : syracuseStep 9459017 = 7094263) B7094263
theorem B1660351 : Blo 1474557 1660351 := bstep (se 1 (by rfl) ⟨1245263, by rfl⟩ : syracuseStep 1660351 = 2490527) B2490527
theorem B4978529 : Blo 1474557 4978529 := bstep (se 2 (by rfl) ⟨1866948, by rfl⟩ : syracuseStep 4978529 = 3733897) B3733897
theorem B14178185 : Blo 1474557 14178185 := bstep (se 2 (by rfl) ⟨5316819, by rfl⟩ : syracuseStep 14178185 = 10633639) B10633639
theorem B56687039 : Blo 1474557 56687039 := bstep (se 1 (by rfl) ⟨42515279, by rfl⟩ : syracuseStep 56687039 = 85030559) B85030559
theorem B8403821 : Blo 1474557 8403821 := bstep (se 3 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 8403821 = 3151433) B3151433
theorem B43138351 : Blo 1474557 43138351 := bstep (se 1 (by rfl) ⟨32353763, by rfl⟩ : syracuseStep 43138351 = 64707527) B64707527
theorem B3319019 : Blo 1474557 3319019 := bstep (se 1 (by rfl) ⟨2489264, by rfl⟩ : syracuseStep 3319019 = 4978529) B4978529
theorem B2213279 : Blo 1474557 2213279 := bstep (se 1 (by rfl) ⟨1659959, by rfl⟩ : syracuseStep 2213279 = 3319919) B3319919
theorem B8979943 : Blo 1474557 8979943 := bstep (se 1 (by rfl) ⟨6734957, by rfl⟩ : syracuseStep 8979943 = 13469915) B13469915
theorem B37791359 : Blo 1474557 37791359 := bstep (se 1 (by rfl) ⟨28343519, by rfl⟩ : syracuseStep 37791359 = 56687039) B56687039
theorem B2213801 : Blo 1474557 2213801 := bstep (se 2 (by rfl) ⟨830175, by rfl⟩ : syracuseStep 2213801 = 1660351) B1660351
theorem B2213999 : Blo 1474557 2213999 := bstep (se 1 (by rfl) ⟨1660499, by rfl⟩ : syracuseStep 2213999 = 3320999) B3320999
theorem B3544393 : Blo 1474557 3544393 := bstep (se 2 (by rfl) ⟨1329147, by rfl⟩ : syracuseStep 3544393 = 2658295) B2658295
theorem B7468523 : Blo 1474557 7468523 := bstep (se 1 (by rfl) ⟨5601392, by rfl⟩ : syracuseStep 7468523 = 11202785) B11202785
theorem B3987625 : Blo 1474557 3987625 := bstep (se 2 (by rfl) ⟨1495359, by rfl⟩ : syracuseStep 3987625 = 2990719) B2990719
theorem B6306011 : Blo 1474557 6306011 := bstep (se 1 (by rfl) ⟨4729508, by rfl⟩ : syracuseStep 6306011 = 9459017) B9459017
theorem B9452123 : Blo 1474557 9452123 := bstep (se 1 (by rfl) ⟨7089092, by rfl⟩ : syracuseStep 9452123 = 14178185) B14178185
theorem B21265021 : Blo 1474557 21265021 := bstep (se 3 (by rfl) ⟨3987191, by rfl⟩ : syracuseStep 21265021 = 7974383) B7974383
theorem B230071205 : Blo 1474557 230071205 := bstep (se 4 (by rfl) ⟨21569175, by rfl⟩ : syracuseStep 230071205 = 43138351) B43138351
theorem B6298697 : Blo 1474557 6298697 := bstep (se 2 (by rfl) ⟨2362011, by rfl⟩ : syracuseStep 6298697 = 4724023) B4724023
theorem B5602547 : Blo 1474557 5602547 := bstep (se 1 (by rfl) ⟨4201910, by rfl⟩ : syracuseStep 5602547 = 8403821) B8403821
theorem B5316833 : Blo 1474557 5316833 := bstep (se 2 (by rfl) ⟨1993812, by rfl⟩ : syracuseStep 5316833 = 3987625) B3987625
theorem B2212679 : Blo 1474557 2212679 := bstep (se 1 (by rfl) ⟨1659509, by rfl⟩ : syracuseStep 2212679 = 3319019) B3319019
theorem B28353361 : Blo 1474557 28353361 := bstep (se 2 (by rfl) ⟨10632510, by rfl⟩ : syracuseStep 28353361 = 21265021) B21265021
theorem B1475519 : Blo 1474557 1475519 := bstep (se 1 (by rfl) ⟨1106639, by rfl⟩ : syracuseStep 1475519 = 2213279) B2213279
theorem B1475867 : Blo 1474557 1475867 := bstep (se 1 (by rfl) ⟨1106900, by rfl⟩ : syracuseStep 1475867 = 2213801) B2213801
theorem B1475999 : Blo 1474557 1475999 := bstep (se 1 (by rfl) ⟨1106999, by rfl⟩ : syracuseStep 1475999 = 2213999) B2213999
theorem B4204007 : Blo 1474557 4204007 := bstep (se 1 (by rfl) ⟨3153005, by rfl⟩ : syracuseStep 4204007 = 6306011) B6306011
theorem B6301415 : Blo 1474557 6301415 := bstep (se 1 (by rfl) ⟨4726061, by rfl⟩ : syracuseStep 6301415 = 9452123) B9452123
theorem B153380803 : Blo 1474557 153380803 := bstep (se 1 (by rfl) ⟨115035602, by rfl⟩ : syracuseStep 153380803 = 230071205) B230071205
theorem B25194239 : Blo 1474557 25194239 := bstep (se 1 (by rfl) ⟨18895679, by rfl⟩ : syracuseStep 25194239 = 37791359) B37791359
theorem B11973257 : Blo 1474557 11973257 := bstep (se 2 (by rfl) ⟨4489971, by rfl⟩ : syracuseStep 11973257 = 8979943) B8979943
theorem B4199131 : Blo 1474557 4199131 := bstep (se 1 (by rfl) ⟨3149348, by rfl⟩ : syracuseStep 4199131 = 6298697) B6298697
theorem B4979015 : Blo 1474557 4979015 := bstep (se 1 (by rfl) ⟨3734261, by rfl⟩ : syracuseStep 4979015 = 7468523) B7468523
theorem B4725857 : Blo 1474557 4725857 := bstep (se 2 (by rfl) ⟨1772196, by rfl⟩ : syracuseStep 4725857 = 3544393) B3544393
theorem B3735031 : Blo 1474557 3735031 := bstep (se 1 (by rfl) ⟨2801273, by rfl⟩ : syracuseStep 3735031 = 5602547) B5602547
theorem B1475119 : Blo 1474557 1475119 := bstep (se 1 (by rfl) ⟨1106339, by rfl⟩ : syracuseStep 1475119 = 2212679) B2212679
theorem B2802671 : Blo 1474557 2802671 := bstep (se 1 (by rfl) ⟨2102003, by rfl⟩ : syracuseStep 2802671 = 4204007) B4204007
theorem B3319343 : Blo 1474557 3319343 := bstep (se 1 (by rfl) ⟨2489507, by rfl⟩ : syracuseStep 3319343 = 4979015) B4979015
theorem B16796159 : Blo 1474557 16796159 := bstep (se 1 (by rfl) ⟨12597119, by rfl⟩ : syracuseStep 16796159 = 25194239) B25194239
theorem B204507737 : Blo 1474557 204507737 := bstep (se 2 (by rfl) ⟨76690401, by rfl⟩ : syracuseStep 204507737 = 153380803) B153380803
theorem B7982171 : Blo 1474557 7982171 := bstep (se 1 (by rfl) ⟨5986628, by rfl⟩ : syracuseStep 7982171 = 11973257) B11973257
theorem B5598841 : Blo 1474557 5598841 := bstep (se 2 (by rfl) ⟨2099565, by rfl⟩ : syracuseStep 5598841 = 4199131) B4199131
theorem B3150571 : Blo 1474557 3150571 := bstep (se 1 (by rfl) ⟨2362928, by rfl⟩ : syracuseStep 3150571 = 4725857) B4725857
theorem B3544555 : Blo 1474557 3544555 := bstep (se 1 (by rfl) ⟨2658416, by rfl⟩ : syracuseStep 3544555 = 5316833) B5316833
theorem B37804481 : Blo 1474557 37804481 := bstep (se 2 (by rfl) ⟨14176680, by rfl⟩ : syracuseStep 37804481 = 28353361) B28353361
theorem B4200943 : Blo 1474557 4200943 := bstep (se 1 (by rfl) ⟨3150707, by rfl⟩ : syracuseStep 4200943 = 6301415) B6301415
theorem B4980041 : Blo 1474557 4980041 := bstep (se 2 (by rfl) ⟨1867515, by rfl⟩ : syracuseStep 4980041 = 3735031) B3735031
theorem B1868447 : Blo 1474557 1868447 := bstep (se 1 (by rfl) ⟨1401335, by rfl⟩ : syracuseStep 1868447 = 2802671) B2802671
theorem B2212895 : Blo 1474557 2212895 := bstep (se 1 (by rfl) ⟨1659671, by rfl⟩ : syracuseStep 2212895 = 3319343) B3319343
theorem B7465121 : Blo 1474557 7465121 := bstep (se 2 (by rfl) ⟨2799420, by rfl⟩ : syracuseStep 7465121 = 5598841) B5598841
theorem B3320027 : Blo 1474557 3320027 := bstep (se 1 (by rfl) ⟨2490020, by rfl⟩ : syracuseStep 3320027 = 4980041) B4980041
theorem B25202987 : Blo 1474557 25202987 := bstep (se 1 (by rfl) ⟨18902240, by rfl⟩ : syracuseStep 25202987 = 37804481) B37804481
theorem B5321447 : Blo 1474557 5321447 := bstep (se 1 (by rfl) ⟨3991085, by rfl⟩ : syracuseStep 5321447 = 7982171) B7982171
theorem B5601257 : Blo 1474557 5601257 := bstep (se 2 (by rfl) ⟨2100471, by rfl⟩ : syracuseStep 5601257 = 4200943) B4200943
theorem B4200761 : Blo 1474557 4200761 := bstep (se 2 (by rfl) ⟨1575285, by rfl⟩ : syracuseStep 4200761 = 3150571) B3150571
theorem B11197439 : Blo 1474557 11197439 := bstep (se 1 (by rfl) ⟨8398079, by rfl⟩ : syracuseStep 11197439 = 16796159) B16796159
theorem B136338491 : Blo 1474557 136338491 := bstep (se 1 (by rfl) ⟨102253868, by rfl⟩ : syracuseStep 136338491 = 204507737) B204507737
theorem B4726073 : Blo 1474557 4726073 := bstep (se 2 (by rfl) ⟨1772277, by rfl⟩ : syracuseStep 4726073 = 3544555) B3544555
theorem B363569309 : Blo 1474557 363569309 := bstep (se 3 (by rfl) ⟨68169245, by rfl⟩ : syracuseStep 363569309 = 136338491) B136338491
theorem B16801991 : Blo 1474557 16801991 := bstep (se 1 (by rfl) ⟨12601493, by rfl⟩ : syracuseStep 16801991 = 25202987) B25202987
theorem B3547631 : Blo 1474557 3547631 := bstep (se 1 (by rfl) ⟨2660723, by rfl⟩ : syracuseStep 3547631 = 5321447) B5321447
theorem B1475263 : Blo 1474557 1475263 := bstep (se 1 (by rfl) ⟨1106447, by rfl⟩ : syracuseStep 1475263 = 2212895) B2212895
theorem B2213351 : Blo 1474557 2213351 := bstep (se 1 (by rfl) ⟨1660013, by rfl⟩ : syracuseStep 2213351 = 3320027) B3320027
theorem B4982525 : Blo 1474557 4982525 := bstep (se 3 (by rfl) ⟨934223, by rfl⟩ : syracuseStep 4982525 = 1868447) B1868447
theorem B7464959 : Blo 1474557 7464959 := bstep (se 1 (by rfl) ⟨5598719, by rfl⟩ : syracuseStep 7464959 = 11197439) B11197439
theorem B12602861 : Blo 1474557 12602861 := bstep (se 3 (by rfl) ⟨2363036, by rfl⟩ : syracuseStep 12602861 = 4726073) B4726073
theorem B4976747 : Blo 1474557 4976747 := bstep (se 1 (by rfl) ⟨3732560, by rfl⟩ : syracuseStep 4976747 = 7465121) B7465121
theorem B3734171 : Blo 1474557 3734171 := bstep (se 1 (by rfl) ⟨2800628, by rfl⟩ : syracuseStep 3734171 = 5601257) B5601257
theorem B2800507 : Blo 1474557 2800507 := bstep (se 1 (by rfl) ⟨2100380, by rfl⟩ : syracuseStep 2800507 = 4200761) B4200761
theorem B3317831 : Blo 1474557 3317831 := bstep (se 1 (by rfl) ⟨2488373, by rfl⟩ : syracuseStep 3317831 = 4976747) B4976747
theorem B1475567 : Blo 1474557 1475567 := bstep (se 1 (by rfl) ⟨1106675, by rfl⟩ : syracuseStep 1475567 = 2213351) B2213351
theorem B242379539 : Blo 1474557 242379539 := bstep (se 1 (by rfl) ⟨181784654, by rfl⟩ : syracuseStep 242379539 = 363569309) B363569309
theorem B11201327 : Blo 1474557 11201327 := bstep (se 1 (by rfl) ⟨8400995, by rfl⟩ : syracuseStep 11201327 = 16801991) B16801991
theorem B3321683 : Blo 1474557 3321683 := bstep (se 1 (by rfl) ⟨2491262, by rfl⟩ : syracuseStep 3321683 = 4982525) B4982525
theorem B4976639 : Blo 1474557 4976639 := bstep (se 1 (by rfl) ⟨3732479, by rfl⟩ : syracuseStep 4976639 = 7464959) B7464959
theorem B8401907 : Blo 1474557 8401907 := bstep (se 1 (by rfl) ⟨6301430, by rfl⟩ : syracuseStep 8401907 = 12602861) B12602861
theorem B2365087 : Blo 1474557 2365087 := bstep (se 1 (by rfl) ⟨1773815, by rfl⟩ : syracuseStep 2365087 = 3547631) B3547631
theorem B3734009 : Blo 1474557 3734009 := bstep (se 2 (by rfl) ⟨1400253, by rfl⟩ : syracuseStep 3734009 = 2800507) B2800507
theorem B2489447 : Blo 1474557 2489447 := bstep (se 1 (by rfl) ⟨1867085, by rfl⟩ : syracuseStep 2489447 = 3734171) B3734171
theorem B2211887 : Blo 1474557 2211887 := bstep (se 1 (by rfl) ⟨1658915, by rfl⟩ : syracuseStep 2211887 = 3317831) B3317831
theorem B2214455 : Blo 1474557 2214455 := bstep (se 1 (by rfl) ⟨1660841, by rfl⟩ : syracuseStep 2214455 = 3321683) B3321683
theorem B7467551 : Blo 1474557 7467551 := bstep (se 1 (by rfl) ⟨5600663, by rfl⟩ : syracuseStep 7467551 = 11201327) B11201327
theorem B1659631 : Blo 1474557 1659631 := bstep (se 1 (by rfl) ⟨1244723, by rfl⟩ : syracuseStep 1659631 = 2489447) B2489447
theorem B3317759 : Blo 1474557 3317759 := bstep (se 1 (by rfl) ⟨2488319, by rfl⟩ : syracuseStep 3317759 = 4976639) B4976639
theorem B5601271 : Blo 1474557 5601271 := bstep (se 1 (by rfl) ⟨4200953, by rfl⟩ : syracuseStep 5601271 = 8401907) B8401907
theorem B2489339 : Blo 1474557 2489339 := bstep (se 1 (by rfl) ⟨1867004, by rfl⟩ : syracuseStep 2489339 = 3734009) B3734009
theorem B161586359 : Blo 1474557 161586359 := bstep (se 1 (by rfl) ⟨121189769, by rfl⟩ : syracuseStep 161586359 = 242379539) B242379539
theorem B3153449 : Blo 1474557 3153449 := bstep (se 2 (by rfl) ⟨1182543, by rfl⟩ : syracuseStep 3153449 = 2365087) B2365087
theorem B1474591 : Blo 1474557 1474591 := bstep (se 1 (by rfl) ⟨1105943, by rfl⟩ : syracuseStep 1474591 = 2211887) B2211887
theorem B2212841 : Blo 1474557 2212841 := bstep (se 2 (by rfl) ⟨829815, by rfl⟩ : syracuseStep 2212841 = 1659631) B1659631
theorem B1476303 : Blo 1474557 1476303 := bstep (se 1 (by rfl) ⟨1107227, by rfl⟩ : syracuseStep 1476303 = 2214455) B2214455
theorem B2211839 : Blo 1474557 2211839 := bstep (se 1 (by rfl) ⟨1658879, by rfl⟩ : syracuseStep 2211839 = 3317759) B3317759
theorem B8409197 : Blo 1474557 8409197 := bstep (se 3 (by rfl) ⟨1576724, by rfl⟩ : syracuseStep 8409197 = 3153449) B3153449
theorem B1659559 : Blo 1474557 1659559 := bstep (se 1 (by rfl) ⟨1244669, by rfl⟩ : syracuseStep 1659559 = 2489339) B2489339
theorem B7468361 : Blo 1474557 7468361 := bstep (se 2 (by rfl) ⟨2800635, by rfl⟩ : syracuseStep 7468361 = 5601271) B5601271
theorem B4978367 : Blo 1474557 4978367 := bstep (se 1 (by rfl) ⟨3733775, by rfl⟩ : syracuseStep 4978367 = 7467551) B7467551
theorem B107724239 : Blo 1474557 107724239 := bstep (se 1 (by rfl) ⟨80793179, by rfl⟩ : syracuseStep 107724239 = 161586359) B161586359
theorem B1475227 : Blo 1474557 1475227 := bstep (se 1 (by rfl) ⟨1106420, by rfl⟩ : syracuseStep 1475227 = 2212841) B2212841
theorem B2212745 : Blo 1474557 2212745 := bstep (se 2 (by rfl) ⟨829779, by rfl⟩ : syracuseStep 2212745 = 1659559) B1659559
theorem B3318911 : Blo 1474557 3318911 := bstep (se 1 (by rfl) ⟨2489183, by rfl⟩ : syracuseStep 3318911 = 4978367) B4978367
theorem B5606131 : Blo 1474557 5606131 := bstep (se 1 (by rfl) ⟨4204598, by rfl⟩ : syracuseStep 5606131 = 8409197) B8409197
theorem B71816159 : Blo 1474557 71816159 := bstep (se 1 (by rfl) ⟨53862119, by rfl⟩ : syracuseStep 71816159 = 107724239) B107724239
theorem B4978907 : Blo 1474557 4978907 := bstep (se 1 (by rfl) ⟨3734180, by rfl⟩ : syracuseStep 4978907 = 7468361) B7468361
theorem B1474559 : Blo 1474557 1474559 := bstep (se 1 (by rfl) ⟨1105919, by rfl⟩ : syracuseStep 1474559 = 2211839) B2211839
theorem B1475163 : Blo 1474557 1475163 := bstep (se 1 (by rfl) ⟨1106372, by rfl⟩ : syracuseStep 1475163 = 2212745) B2212745
theorem B2212607 : Blo 1474557 2212607 := bstep (se 1 (by rfl) ⟨1659455, by rfl⟩ : syracuseStep 2212607 = 3318911) B3318911
theorem B3319271 : Blo 1474557 3319271 := bstep (se 1 (by rfl) ⟨2489453, by rfl⟩ : syracuseStep 3319271 = 4978907) B4978907
theorem B47877439 : Blo 1474557 47877439 := bstep (se 1 (by rfl) ⟨35908079, by rfl⟩ : syracuseStep 47877439 = 71816159) B71816159
theorem B7474841 : Blo 1474557 7474841 := bstep (se 2 (by rfl) ⟨2803065, by rfl⟩ : syracuseStep 7474841 = 5606131) B5606131
theorem B1475071 : Blo 1474557 1475071 := bstep (se 1 (by rfl) ⟨1106303, by rfl⟩ : syracuseStep 1475071 = 2212607) B2212607
theorem B2212847 : Blo 1474557 2212847 := bstep (se 1 (by rfl) ⟨1659635, by rfl⟩ : syracuseStep 2212847 = 3319271) B3319271
theorem B4983227 : Blo 1474557 4983227 := bstep (se 1 (by rfl) ⟨3737420, by rfl⟩ : syracuseStep 4983227 = 7474841) B7474841
theorem B63836585 : Blo 1474557 63836585 := bstep (se 2 (by rfl) ⟨23938719, by rfl⟩ : syracuseStep 63836585 = 47877439) B47877439
theorem B42557723 : Blo 1474557 42557723 := bstep (se 1 (by rfl) ⟨31918292, by rfl⟩ : syracuseStep 42557723 = 63836585) B63836585
theorem B1475231 : Blo 1474557 1475231 := bstep (se 1 (by rfl) ⟨1106423, by rfl⟩ : syracuseStep 1475231 = 2212847) B2212847
theorem B3322151 : Blo 1474557 3322151 := bstep (se 1 (by rfl) ⟨2491613, by rfl⟩ : syracuseStep 3322151 = 4983227) B4983227
theorem B28371815 : Blo 1474557 28371815 := bstep (se 1 (by rfl) ⟨21278861, by rfl⟩ : syracuseStep 28371815 = 42557723) B42557723
theorem B2214767 : Blo 1474557 2214767 := bstep (se 1 (by rfl) ⟨1661075, by rfl⟩ : syracuseStep 2214767 = 3322151) B3322151
theorem B1476511 : Blo 1474557 1476511 := bstep (se 1 (by rfl) ⟨1107383, by rfl⟩ : syracuseStep 1476511 = 2214767) B2214767
theorem B18914543 : Blo 1474557 18914543 := bstep (se 1 (by rfl) ⟨14185907, by rfl⟩ : syracuseStep 18914543 = 28371815) B28371815
theorem B12609695 : Blo 1474557 12609695 := bstep (se 1 (by rfl) ⟨9457271, by rfl⟩ : syracuseStep 12609695 = 18914543) B18914543
theorem B8406463 : Blo 1474557 8406463 := bstep (se 1 (by rfl) ⟨6304847, by rfl⟩ : syracuseStep 8406463 = 12609695) B12609695
theorem B11208617 : Blo 1474557 11208617 := bstep (se 2 (by rfl) ⟨4203231, by rfl⟩ : syracuseStep 11208617 = 8406463) B8406463
theorem B7472411 : Blo 1474557 7472411 := bstep (se 1 (by rfl) ⟨5604308, by rfl⟩ : syracuseStep 7472411 = 11208617) B11208617
theorem B4981607 : Blo 1474557 4981607 := bstep (se 1 (by rfl) ⟨3736205, by rfl⟩ : syracuseStep 4981607 = 7472411) B7472411
theorem B3321071 : Blo 1474557 3321071 := bstep (se 1 (by rfl) ⟨2490803, by rfl⟩ : syracuseStep 3321071 = 4981607) B4981607
theorem B2214047 : Blo 1474557 2214047 := bstep (se 1 (by rfl) ⟨1660535, by rfl⟩ : syracuseStep 2214047 = 3321071) B3321071
theorem B1476031 : Blo 1474557 1476031 := bstep (se 1 (by rfl) ⟨1107023, by rfl⟩ : syracuseStep 1476031 = 2214047) B2214047

theorem C0 (j : ℕ) (h1 : 368639 ≤ j) (h2 : j ≤ 369138) : Blo 1474557 (4 * j + 3) := by
  interval_cases j
  · exact B1474559
  · exact B1474563
  · exact B1474567
  · exact B1474571
  · exact B1474575
  · exact B1474579
  · exact B1474583
  · exact B1474587
  · exact B1474591
  · exact B1474595
  · exact B1474599
  · exact B1474603
  · exact B1474607
  · exact B1474611
  · exact B1474615
  · exact B1474619
  · exact B1474623
  · exact B1474627
  · exact B1474631
  · exact B1474635
  · exact B1474639
  · exact B1474643
  · exact B1474647
  · exact B1474651
  · exact B1474655
  · exact B1474659
  · exact B1474663
  · exact B1474667
  · exact B1474671
  · exact B1474675
  · exact B1474679
  · exact B1474683
  · exact B1474687
  · exact B1474691
  · exact B1474695
  · exact B1474699
  · exact B1474703
  · exact B1474707
  · exact B1474711
  · exact B1474715
  · exact B1474719
  · exact B1474723
  · exact B1474727
  · exact B1474731
  · exact B1474735
  · exact B1474739
  · exact B1474743
  · exact B1474747
  · exact B1474751
  · exact B1474755
  · exact B1474759
  · exact B1474763
  · exact B1474767
  · exact B1474771
  · exact B1474775
  · exact B1474779
  · exact B1474783
  · exact B1474787
  · exact B1474791
  · exact B1474795
  · exact B1474799
  · exact B1474803
  · exact B1474807
  · exact B1474811
  · exact B1474815
  · exact B1474819
  · exact B1474823
  · exact B1474827
  · exact B1474831
  · exact B1474835
  · exact B1474839
  · exact B1474843
  · exact B1474847
  · exact B1474851
  · exact B1474855
  · exact B1474859
  · exact B1474863
  · exact B1474867
  · exact B1474871
  · exact B1474875
  · exact B1474879
  · exact B1474883
  · exact B1474887
  · exact B1474891
  · exact B1474895
  · exact B1474899
  · exact B1474903
  · exact B1474907
  · exact B1474911
  · exact B1474915
  · exact B1474919
  · exact B1474923
  · exact B1474927
  · exact B1474931
  · exact B1474935
  · exact B1474939
  · exact B1474943
  · exact B1474947
  · exact B1474951
  · exact B1474955
  · exact B1474959
  · exact B1474963
  · exact B1474967
  · exact B1474971
  · exact B1474975
  · exact B1474979
  · exact B1474983
  · exact B1474987
  · exact B1474991
  · exact B1474995
  · exact B1474999
  · exact B1475003
  · exact B1475007
  · exact B1475011
  · exact B1475015
  · exact B1475019
  · exact B1475023
  · exact B1475027
  · exact B1475031
  · exact B1475035
  · exact B1475039
  · exact B1475043
  · exact B1475047
  · exact B1475051
  · exact B1475055
  · exact B1475059
  · exact B1475063
  · exact B1475067
  · exact B1475071
  · exact B1475075
  · exact B1475079
  · exact B1475083
  · exact B1475087
  · exact B1475091
  · exact B1475095
  · exact B1475099
  · exact B1475103
  · exact B1475107
  · exact B1475111
  · exact B1475115
  · exact B1475119
  · exact B1475123
  · exact B1475127
  · exact B1475131
  · exact B1475135
  · exact B1475139
  · exact B1475143
  · exact B1475147
  · exact B1475151
  · exact B1475155
  · exact B1475159
  · exact B1475163
  · exact B1475167
  · exact B1475171
  · exact B1475175
  · exact B1475179
  · exact B1475183
  · exact B1475187
  · exact B1475191
  · exact B1475195
  · exact B1475199
  · exact B1475203
  · exact B1475207
  · exact B1475211
  · exact B1475215
  · exact B1475219
  · exact B1475223
  · exact B1475227
  · exact B1475231
  · exact B1475235
  · exact B1475239
  · exact B1475243
  · exact B1475247
  · exact B1475251
  · exact B1475255
  · exact B1475259
  · exact B1475263
  · exact B1475267
  · exact B1475271
  · exact B1475275
  · exact B1475279
  · exact B1475283
  · exact B1475287
  · exact B1475291
  · exact B1475295
  · exact B1475299
  · exact B1475303
  · exact B1475307
  · exact B1475311
  · exact B1475315
  · exact B1475319
  · exact B1475323
  · exact B1475327
  · exact B1475331
  · exact B1475335
  · exact B1475339
  · exact B1475343
  · exact B1475347
  · exact B1475351
  · exact B1475355
  · exact B1475359
  · exact B1475363
  · exact B1475367
  · exact B1475371
  · exact B1475375
  · exact B1475379
  · exact B1475383
  · exact B1475387
  · exact B1475391
  · exact B1475395
  · exact B1475399
  · exact B1475403
  · exact B1475407
  · exact B1475411
  · exact B1475415
  · exact B1475419
  · exact B1475423
  · exact B1475427
  · exact B1475431
  · exact B1475435
  · exact B1475439
  · exact B1475443
  · exact B1475447
  · exact B1475451
  · exact B1475455
  · exact B1475459
  · exact B1475463
  · exact B1475467
  · exact B1475471
  · exact B1475475
  · exact B1475479
  · exact B1475483
  · exact B1475487
  · exact B1475491
  · exact B1475495
  · exact B1475499
  · exact B1475503
  · exact B1475507
  · exact B1475511
  · exact B1475515
  · exact B1475519
  · exact B1475523
  · exact B1475527
  · exact B1475531
  · exact B1475535
  · exact B1475539
  · exact B1475543
  · exact B1475547
  · exact B1475551
  · exact B1475555
  · exact B1475559
  · exact B1475563
  · exact B1475567
  · exact B1475571
  · exact B1475575
  · exact B1475579
  · exact B1475583
  · exact B1475587
  · exact B1475591
  · exact B1475595
  · exact B1475599
  · exact B1475603
  · exact B1475607
  · exact B1475611
  · exact B1475615
  · exact B1475619
  · exact B1475623
  · exact B1475627
  · exact B1475631
  · exact B1475635
  · exact B1475639
  · exact B1475643
  · exact B1475647
  · exact B1475651
  · exact B1475655
  · exact B1475659
  · exact B1475663
  · exact B1475667
  · exact B1475671
  · exact B1475675
  · exact B1475679
  · exact B1475683
  · exact B1475687
  · exact B1475691
  · exact B1475695
  · exact B1475699
  · exact B1475703
  · exact B1475707
  · exact B1475711
  · exact B1475715
  · exact B1475719
  · exact B1475723
  · exact B1475727
  · exact B1475731
  · exact B1475735
  · exact B1475739
  · exact B1475743
  · exact B1475747
  · exact B1475751
  · exact B1475755
  · exact B1475759
  · exact B1475763
  · exact B1475767
  · exact B1475771
  · exact B1475775
  · exact B1475779
  · exact B1475783
  · exact B1475787
  · exact B1475791
  · exact B1475795
  · exact B1475799
  · exact B1475803
  · exact B1475807
  · exact B1475811
  · exact B1475815
  · exact B1475819
  · exact B1475823
  · exact B1475827
  · exact B1475831
  · exact B1475835
  · exact B1475839
  · exact B1475843
  · exact B1475847
  · exact B1475851
  · exact B1475855
  · exact B1475859
  · exact B1475863
  · exact B1475867
  · exact B1475871
  · exact B1475875
  · exact B1475879
  · exact B1475883
  · exact B1475887
  · exact B1475891
  · exact B1475895
  · exact B1475899
  · exact B1475903
  · exact B1475907
  · exact B1475911
  · exact B1475915
  · exact B1475919
  · exact B1475923
  · exact B1475927
  · exact B1475931
  · exact B1475935
  · exact B1475939
  · exact B1475943
  · exact B1475947
  · exact B1475951
  · exact B1475955
  · exact B1475959
  · exact B1475963
  · exact B1475967
  · exact B1475971
  · exact B1475975
  · exact B1475979
  · exact B1475983
  · exact B1475987
  · exact B1475991
  · exact B1475995
  · exact B1475999
  · exact B1476003
  · exact B1476007
  · exact B1476011
  · exact B1476015
  · exact B1476019
  · exact B1476023
  · exact B1476027
  · exact B1476031
  · exact B1476035
  · exact B1476039
  · exact B1476043
  · exact B1476047
  · exact B1476051
  · exact B1476055
  · exact B1476059
  · exact B1476063
  · exact B1476067
  · exact B1476071
  · exact B1476075
  · exact B1476079
  · exact B1476083
  · exact B1476087
  · exact B1476091
  · exact B1476095
  · exact B1476099
  · exact B1476103
  · exact B1476107
  · exact B1476111
  · exact B1476115
  · exact B1476119
  · exact B1476123
  · exact B1476127
  · exact B1476131
  · exact B1476135
  · exact B1476139
  · exact B1476143
  · exact B1476147
  · exact B1476151
  · exact B1476155
  · exact B1476159
  · exact B1476163
  · exact B1476167
  · exact B1476171
  · exact B1476175
  · exact B1476179
  · exact B1476183
  · exact B1476187
  · exact B1476191
  · exact B1476195
  · exact B1476199
  · exact B1476203
  · exact B1476207
  · exact B1476211
  · exact B1476215
  · exact B1476219
  · exact B1476223
  · exact B1476227
  · exact B1476231
  · exact B1476235
  · exact B1476239
  · exact B1476243
  · exact B1476247
  · exact B1476251
  · exact B1476255
  · exact B1476259
  · exact B1476263
  · exact B1476267
  · exact B1476271
  · exact B1476275
  · exact B1476279
  · exact B1476283
  · exact B1476287
  · exact B1476291
  · exact B1476295
  · exact B1476299
  · exact B1476303
  · exact B1476307
  · exact B1476311
  · exact B1476315
  · exact B1476319
  · exact B1476323
  · exact B1476327
  · exact B1476331
  · exact B1476335
  · exact B1476339
  · exact B1476343
  · exact B1476347
  · exact B1476351
  · exact B1476355
  · exact B1476359
  · exact B1476363
  · exact B1476367
  · exact B1476371
  · exact B1476375
  · exact B1476379
  · exact B1476383
  · exact B1476387
  · exact B1476391
  · exact B1476395
  · exact B1476399
  · exact B1476403
  · exact B1476407
  · exact B1476411
  · exact B1476415
  · exact B1476419
  · exact B1476423
  · exact B1476427
  · exact B1476431
  · exact B1476435
  · exact B1476439
  · exact B1476443
  · exact B1476447
  · exact B1476451
  · exact B1476455
  · exact B1476459
  · exact B1476463
  · exact B1476467
  · exact B1476471
  · exact B1476475
  · exact B1476479
  · exact B1476483
  · exact B1476487
  · exact B1476491
  · exact B1476495
  · exact B1476499
  · exact B1476503
  · exact B1476507
  · exact B1476511
  · exact B1476515
  · exact B1476519
  · exact B1476523
  · exact B1476527
  · exact B1476531
  · exact B1476535
  · exact B1476539
  · exact B1476543
  · exact B1476547
  · exact B1476551
  · exact B1476555

theorem solution (m : ℕ) (hlo : 1474557 ≤ m) (hhi : m ≤ 1476557) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 368639 ≤ j := by omega
    have hj2 : j ≤ 369138 := by omega
    have hb : Blo 1474557 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
