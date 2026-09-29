-- Prove2me | solution 1 for syracuse_descends_range_718322_722322
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:07.463286+00:00
-- url     : https://prove2.me/submissions/5ef8c751-2cc4-406a-84e8-1f6ca430e1f8

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


theorem B1212421 : Blo 718322 1212421 := bbase (se 4 (by rfl) ⟨113664, by rfl⟩ : syracuseStep 1212421 = 227329) (by norm_num)
theorem B1081349 : Blo 718322 1081349 := bbase (se 4 (by rfl) ⟨101376, by rfl⟩ : syracuseStep 1081349 = 202753) (by norm_num)
theorem B1081373 : Blo 718322 1081373 := bbase (se 3 (by rfl) ⟨202757, by rfl⟩ : syracuseStep 1081373 = 405515) (by norm_num)
theorem B2424869 : Blo 718322 2424869 := bbase (se 4 (by rfl) ⟨227331, by rfl⟩ : syracuseStep 2424869 = 454663) (by norm_num)
theorem B1081397 : Blo 718322 1081397 := bbase (se 5 (by rfl) ⟨50690, by rfl⟩ : syracuseStep 1081397 = 101381) (by norm_num)
theorem B1081421 : Blo 718322 1081421 := bbase (se 3 (by rfl) ⟨202766, by rfl⟩ : syracuseStep 1081421 = 405533) (by norm_num)
theorem B1212509 : Blo 718322 1212509 := bbase (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) (by norm_num)
theorem B1081445 : Blo 718322 1081445 := bbase (se 4 (by rfl) ⟨101385, by rfl⟩ : syracuseStep 1081445 = 202771) (by norm_num)
theorem B1081469 : Blo 718322 1081469 := bbase (se 3 (by rfl) ⟨202775, by rfl⟩ : syracuseStep 1081469 = 405551) (by norm_num)
theorem B1081493 : Blo 718322 1081493 := bbase (se 6 (by rfl) ⟨25347, by rfl⟩ : syracuseStep 1081493 = 50695) (by norm_num)
theorem B1081517 : Blo 718322 1081517 := bbase (se 3 (by rfl) ⟨202784, by rfl⟩ : syracuseStep 1081517 = 405569) (by norm_num)
theorem B1081541 : Blo 718322 1081541 := bbase (se 4 (by rfl) ⟨101394, by rfl⟩ : syracuseStep 1081541 = 202789) (by norm_num)
theorem B1212637 : Blo 718322 1212637 := bbase (se 3 (by rfl) ⟨227369, by rfl⟩ : syracuseStep 1212637 = 454739) (by norm_num)
theorem B1081565 : Blo 718322 1081565 := bbase (se 3 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 1081565 = 405587) (by norm_num)
theorem B1081589 : Blo 718322 1081589 := bbase (se 5 (by rfl) ⟨50699, by rfl⟩ : syracuseStep 1081589 = 101399) (by norm_num)
theorem B1081613 : Blo 718322 1081613 := bbase (se 3 (by rfl) ⟨202802, by rfl⟩ : syracuseStep 1081613 = 405605) (by norm_num)
theorem B1081637 : Blo 718322 1081637 := bbase (se 4 (by rfl) ⟨101403, by rfl⟩ : syracuseStep 1081637 = 202807) (by norm_num)
theorem B1212725 : Blo 718322 1212725 := bbase (se 5 (by rfl) ⟨56846, by rfl⟩ : syracuseStep 1212725 = 113693) (by norm_num)
theorem B3506485 : Blo 718322 3506485 := bbase (se 5 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 3506485 = 328733) (by norm_num)
theorem B1081661 : Blo 718322 1081661 := bbase (se 3 (by rfl) ⟨202811, by rfl⟩ : syracuseStep 1081661 = 405623) (by norm_num)
theorem B1081685 : Blo 718322 1081685 := bbase (se 10 (by rfl) ⟨1584, by rfl⟩ : syracuseStep 1081685 = 3169) (by norm_num)
theorem B1081709 : Blo 718322 1081709 := bbase (se 3 (by rfl) ⟨202820, by rfl⟩ : syracuseStep 1081709 = 405641) (by norm_num)
theorem B1081733 : Blo 718322 1081733 := bbase (se 4 (by rfl) ⟨101412, by rfl⟩ : syracuseStep 1081733 = 202825) (by norm_num)
theorem B13304213 : Blo 718322 13304213 := bbase (se 6 (by rfl) ⟨311817, by rfl⟩ : syracuseStep 13304213 = 623635) (by norm_num)
theorem B1081757 : Blo 718322 1081757 := bbase (se 3 (by rfl) ⟨202829, by rfl⟩ : syracuseStep 1081757 = 405659) (by norm_num)
theorem B1212853 : Blo 718322 1212853 := bbase (se 5 (by rfl) ⟨56852, by rfl⟩ : syracuseStep 1212853 = 113705) (by norm_num)
theorem B1081781 : Blo 718322 1081781 := bbase (se 5 (by rfl) ⟨50708, by rfl⟩ : syracuseStep 1081781 = 101417) (by norm_num)
theorem B1081805 : Blo 718322 1081805 := bbase (se 3 (by rfl) ⟨202838, by rfl⟩ : syracuseStep 1081805 = 405677) (by norm_num)
theorem B2425301 : Blo 718322 2425301 := bbase (se 7 (by rfl) ⟨28421, by rfl⟩ : syracuseStep 2425301 = 56843) (by norm_num)
theorem B1081829 : Blo 718322 1081829 := bbase (se 4 (by rfl) ⟨101421, by rfl⟩ : syracuseStep 1081829 = 202843) (by norm_num)
theorem B1081853 : Blo 718322 1081853 := bbase (se 3 (by rfl) ⟨202847, by rfl⟩ : syracuseStep 1081853 = 405695) (by norm_num)
theorem B1212941 : Blo 718322 1212941 := bbase (se 3 (by rfl) ⟨227426, by rfl⟩ : syracuseStep 1212941 = 454853) (by norm_num)
theorem B1081877 : Blo 718322 1081877 := bbase (se 6 (by rfl) ⟨25356, by rfl⟩ : syracuseStep 1081877 = 50713) (by norm_num)
theorem B1081901 : Blo 718322 1081901 := bbase (se 3 (by rfl) ⟨202856, by rfl⟩ : syracuseStep 1081901 = 405713) (by norm_num)
theorem B1081925 : Blo 718322 1081925 := bbase (se 4 (by rfl) ⟨101430, by rfl⟩ : syracuseStep 1081925 = 202861) (by norm_num)
theorem B1081949 : Blo 718322 1081949 := bbase (se 3 (by rfl) ⟨202865, by rfl⟩ : syracuseStep 1081949 = 405731) (by norm_num)
theorem B1081973 : Blo 718322 1081973 := bbase (se 5 (by rfl) ⟨50717, by rfl⟩ : syracuseStep 1081973 = 101435) (by norm_num)
theorem B1213069 : Blo 718322 1213069 := bbase (se 3 (by rfl) ⟨227450, by rfl⟩ : syracuseStep 1213069 = 454901) (by norm_num)
theorem B1081997 : Blo 718322 1081997 := bbase (se 3 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 1081997 = 405749) (by norm_num)
theorem B1082021 : Blo 718322 1082021 := bbase (se 4 (by rfl) ⟨101439, by rfl⟩ : syracuseStep 1082021 = 202879) (by norm_num)
theorem B3277493 : Blo 718322 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B1082045 : Blo 718322 1082045 := bbase (se 3 (by rfl) ⟨202883, by rfl⟩ : syracuseStep 1082045 = 405767) (by norm_num)
theorem B1082069 : Blo 718322 1082069 := bbase (se 7 (by rfl) ⟨12680, by rfl⟩ : syracuseStep 1082069 = 25361) (by norm_num)
theorem B1213157 : Blo 718322 1213157 := bbase (se 4 (by rfl) ⟨113733, by rfl⟩ : syracuseStep 1213157 = 227467) (by norm_num)
theorem B1082093 : Blo 718322 1082093 := bbase (se 3 (by rfl) ⟨202892, by rfl⟩ : syracuseStep 1082093 = 405785) (by norm_num)
theorem B1082117 : Blo 718322 1082117 := bbase (se 4 (by rfl) ⟨101448, by rfl⟩ : syracuseStep 1082117 = 202897) (by norm_num)
theorem B12321557 : Blo 718322 12321557 := bbase (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) (by norm_num)
theorem B1082141 : Blo 718322 1082141 := bbase (se 3 (by rfl) ⟨202901, by rfl⟩ : syracuseStep 1082141 = 405803) (by norm_num)
theorem B1082165 : Blo 718322 1082165 := bbase (se 5 (by rfl) ⟨50726, by rfl⟩ : syracuseStep 1082165 = 101453) (by norm_num)
theorem B1082189 : Blo 718322 1082189 := bbase (se 3 (by rfl) ⟨202910, by rfl⟩ : syracuseStep 1082189 = 405821) (by norm_num)
theorem B1213285 : Blo 718322 1213285 := bbase (se 4 (by rfl) ⟨113745, by rfl⟩ : syracuseStep 1213285 = 227491) (by norm_num)
theorem B1082213 : Blo 718322 1082213 := bbase (se 4 (by rfl) ⟨101457, by rfl⟩ : syracuseStep 1082213 = 202915) (by norm_num)
theorem B1540981 : Blo 718322 1540981 := bbase (se 5 (by rfl) ⟨72233, by rfl⟩ : syracuseStep 1540981 = 144467) (by norm_num)
theorem B1082237 : Blo 718322 1082237 := bbase (se 3 (by rfl) ⟨202919, by rfl⟩ : syracuseStep 1082237 = 405839) (by norm_num)
theorem B2425733 : Blo 718322 2425733 := bbase (se 4 (by rfl) ⟨227412, by rfl⟩ : syracuseStep 2425733 = 454825) (by norm_num)
theorem B1082261 : Blo 718322 1082261 := bbase (se 6 (by rfl) ⟨25365, by rfl⟩ : syracuseStep 1082261 = 50731) (by norm_num)
theorem B1082285 : Blo 718322 1082285 := bbase (se 3 (by rfl) ⟨202928, by rfl⟩ : syracuseStep 1082285 = 405857) (by norm_num)
theorem B1213373 : Blo 718322 1213373 := bbase (se 3 (by rfl) ⟨227507, by rfl⟩ : syracuseStep 1213373 = 455015) (by norm_num)
theorem B1082309 : Blo 718322 1082309 := bbase (se 4 (by rfl) ⟨101466, by rfl⟩ : syracuseStep 1082309 = 202933) (by norm_num)
theorem B2917333 : Blo 718322 2917333 := bbase (se 7 (by rfl) ⟨34187, by rfl⟩ : syracuseStep 2917333 = 68375) (by norm_num)
theorem B1082333 : Blo 718322 1082333 := bbase (se 3 (by rfl) ⟨202937, by rfl⟩ : syracuseStep 1082333 = 405875) (by norm_num)
theorem B1541101 : Blo 718322 1541101 := bbase (se 3 (by rfl) ⟨288956, by rfl⟩ : syracuseStep 1541101 = 577913) (by norm_num)
theorem B1082357 : Blo 718322 1082357 := bbase (se 5 (by rfl) ⟨50735, by rfl⟩ : syracuseStep 1082357 = 101471) (by norm_num)
theorem B1082381 : Blo 718322 1082381 := bbase (se 3 (by rfl) ⟨202946, by rfl⟩ : syracuseStep 1082381 = 405893) (by norm_num)
theorem B1082405 : Blo 718322 1082405 := bbase (se 4 (by rfl) ⟨101475, by rfl⟩ : syracuseStep 1082405 = 202951) (by norm_num)
theorem B1213501 : Blo 718322 1213501 := bbase (se 3 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 1213501 = 455063) (by norm_num)
theorem B1082429 : Blo 718322 1082429 := bbase (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) (by norm_num)
theorem B3638357 : Blo 718322 3638357 := bbase (se 8 (by rfl) ⟨21318, by rfl⟩ : syracuseStep 3638357 = 42637) (by norm_num)
theorem B1082453 : Blo 718322 1082453 := bbase (se 8 (by rfl) ⟨6342, by rfl⟩ : syracuseStep 1082453 = 12685) (by norm_num)
theorem B1082477 : Blo 718322 1082477 := bbase (se 3 (by rfl) ⟨202964, by rfl⟩ : syracuseStep 1082477 = 405929) (by norm_num)
theorem B4097141 : Blo 718322 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B1082501 : Blo 718322 1082501 := bbase (se 4 (by rfl) ⟨101484, by rfl⟩ : syracuseStep 1082501 = 202969) (by norm_num)
theorem B1213589 : Blo 718322 1213589 := bbase (se 6 (by rfl) ⟨28443, by rfl⟩ : syracuseStep 1213589 = 56887) (by norm_num)
theorem B1082525 : Blo 718322 1082525 := bbase (se 3 (by rfl) ⟨202973, by rfl⟩ : syracuseStep 1082525 = 405947) (by norm_num)
theorem B1082549 : Blo 718322 1082549 := bbase (se 5 (by rfl) ⟨50744, by rfl⟩ : syracuseStep 1082549 = 101489) (by norm_num)
theorem B1082573 : Blo 718322 1082573 := bbase (se 3 (by rfl) ⟨202982, by rfl⟩ : syracuseStep 1082573 = 405965) (by norm_num)
theorem B1082597 : Blo 718322 1082597 := bbase (se 4 (by rfl) ⟨101493, by rfl⟩ : syracuseStep 1082597 = 202987) (by norm_num)
theorem B1541357 : Blo 718322 1541357 := bbase (se 3 (by rfl) ⟨289004, by rfl⟩ : syracuseStep 1541357 = 578009) (by norm_num)
theorem B1082621 : Blo 718322 1082621 := bbase (se 3 (by rfl) ⟨202991, by rfl⟩ : syracuseStep 1082621 = 405983) (by norm_num)
theorem B1213717 : Blo 718322 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B1082645 : Blo 718322 1082645 := bbase (se 6 (by rfl) ⟨25374, by rfl⟩ : syracuseStep 1082645 = 50749) (by norm_num)
theorem B1082669 : Blo 718322 1082669 := bbase (se 3 (by rfl) ⟨203000, by rfl⟩ : syracuseStep 1082669 = 406001) (by norm_num)
theorem B2426165 : Blo 718322 2426165 := bbase (se 5 (by rfl) ⟨113726, by rfl⟩ : syracuseStep 2426165 = 227453) (by norm_num)
theorem B820541 : Blo 718322 820541 := bbase (se 3 (by rfl) ⟨153851, by rfl⟩ : syracuseStep 820541 = 307703) (by norm_num)
theorem B1082693 : Blo 718322 1082693 := bbase (se 4 (by rfl) ⟨101502, by rfl⟩ : syracuseStep 1082693 = 203005) (by norm_num)
theorem B1082717 : Blo 718322 1082717 := bbase (se 3 (by rfl) ⟨203009, by rfl⟩ : syracuseStep 1082717 = 406019) (by norm_num)
theorem B1213805 : Blo 718322 1213805 := bbase (se 3 (by rfl) ⟨227588, by rfl⟩ : syracuseStep 1213805 = 455177) (by norm_num)
theorem B1082741 : Blo 718322 1082741 := bbase (se 5 (by rfl) ⟨50753, by rfl⟩ : syracuseStep 1082741 = 101507) (by norm_num)
theorem B1082765 : Blo 718322 1082765 := bbase (se 3 (by rfl) ⟨203018, by rfl⟩ : syracuseStep 1082765 = 406037) (by norm_num)
theorem B1082789 : Blo 718322 1082789 := bbase (se 4 (by rfl) ⟨101511, by rfl⟩ : syracuseStep 1082789 = 203023) (by norm_num)
theorem B1082813 : Blo 718322 1082813 := bbase (se 3 (by rfl) ⟨203027, by rfl⟩ : syracuseStep 1082813 = 406055) (by norm_num)
theorem B1082837 : Blo 718322 1082837 := bbase (se 7 (by rfl) ⟨12689, by rfl⟩ : syracuseStep 1082837 = 25379) (by norm_num)
theorem B1213933 : Blo 718322 1213933 := bbase (se 3 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 1213933 = 455225) (by norm_num)
theorem B1082861 : Blo 718322 1082861 := bbase (se 3 (by rfl) ⟨203036, by rfl⟩ : syracuseStep 1082861 = 406073) (by norm_num)
theorem B1082885 : Blo 718322 1082885 := bbase (se 4 (by rfl) ⟨101520, by rfl⟩ : syracuseStep 1082885 = 203041) (by norm_num)
theorem B1082909 : Blo 718322 1082909 := bbase (se 3 (by rfl) ⟨203045, by rfl⟩ : syracuseStep 1082909 = 406091) (by norm_num)
theorem B1082933 : Blo 718322 1082933 := bbase (se 5 (by rfl) ⟨50762, by rfl⟩ : syracuseStep 1082933 = 101525) (by norm_num)
theorem B1214021 : Blo 718322 1214021 := bbase (se 4 (by rfl) ⟨113814, by rfl⟩ : syracuseStep 1214021 = 227629) (by norm_num)
theorem B1082957 : Blo 718322 1082957 := bbase (se 3 (by rfl) ⟨203054, by rfl⟩ : syracuseStep 1082957 = 406109) (by norm_num)
theorem B1082981 : Blo 718322 1082981 := bbase (se 4 (by rfl) ⟨101529, by rfl⟩ : syracuseStep 1082981 = 203059) (by norm_num)
theorem B1083005 : Blo 718322 1083005 := bbase (se 3 (by rfl) ⟨203063, by rfl⟩ : syracuseStep 1083005 = 406127) (by norm_num)
theorem B1083029 : Blo 718322 1083029 := bbase (se 6 (by rfl) ⟨25383, by rfl⟩ : syracuseStep 1083029 = 50767) (by norm_num)
theorem B1083053 : Blo 718322 1083053 := bbase (se 3 (by rfl) ⟨203072, by rfl⟩ : syracuseStep 1083053 = 406145) (by norm_num)
theorem B1640125 : Blo 718322 1640125 := bbase (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) (by norm_num)
theorem B1214149 : Blo 718322 1214149 := bbase (se 4 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 1214149 = 227653) (by norm_num)
theorem B1083077 : Blo 718322 1083077 := bbase (se 4 (by rfl) ⟨101538, by rfl⟩ : syracuseStep 1083077 = 203077) (by norm_num)
theorem B1083101 : Blo 718322 1083101 := bbase (se 3 (by rfl) ⟨203081, by rfl⟩ : syracuseStep 1083101 = 406163) (by norm_num)
theorem B2426597 : Blo 718322 2426597 := bbase (se 4 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 2426597 = 454987) (by norm_num)
theorem B1083125 : Blo 718322 1083125 := bbase (se 5 (by rfl) ⟨50771, by rfl⟩ : syracuseStep 1083125 = 101543) (by norm_num)
theorem B1083149 : Blo 718322 1083149 := bbase (se 3 (by rfl) ⟨203090, by rfl⟩ : syracuseStep 1083149 = 406181) (by norm_num)
theorem B1214237 : Blo 718322 1214237 := bbase (se 3 (by rfl) ⟨227669, by rfl⟩ : syracuseStep 1214237 = 455339) (by norm_num)
theorem B1083173 : Blo 718322 1083173 := bbase (se 4 (by rfl) ⟨101547, by rfl⟩ : syracuseStep 1083173 = 203095) (by norm_num)
theorem B5539637 : Blo 718322 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B1083197 : Blo 718322 1083197 := bbase (se 3 (by rfl) ⟨203099, by rfl⟩ : syracuseStep 1083197 = 406199) (by norm_num)
theorem B1083221 : Blo 718322 1083221 := bbase (se 9 (by rfl) ⟨3173, by rfl⟩ : syracuseStep 1083221 = 6347) (by norm_num)
theorem B1083245 : Blo 718322 1083245 := bbase (se 3 (by rfl) ⟨203108, by rfl⟩ : syracuseStep 1083245 = 406217) (by norm_num)
theorem B3901301 : Blo 718322 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B821125 : Blo 718322 821125 := bbase (se 4 (by rfl) ⟨76980, by rfl⟩ : syracuseStep 821125 = 153961) (by norm_num)
theorem B1083269 : Blo 718322 1083269 := bbase (se 4 (by rfl) ⟨101556, by rfl⟩ : syracuseStep 1083269 = 203113) (by norm_num)
theorem B1214365 : Blo 718322 1214365 := bbase (se 3 (by rfl) ⟨227693, by rfl⟩ : syracuseStep 1214365 = 455387) (by norm_num)
theorem B1083293 : Blo 718322 1083293 := bbase (se 3 (by rfl) ⟨203117, by rfl⟩ : syracuseStep 1083293 = 406235) (by norm_num)
theorem B1083317 : Blo 718322 1083317 := bbase (se 5 (by rfl) ⟨50780, by rfl⟩ : syracuseStep 1083317 = 101561) (by norm_num)
theorem B1083341 : Blo 718322 1083341 := bbase (se 3 (by rfl) ⟨203126, by rfl⟩ : syracuseStep 1083341 = 406253) (by norm_num)
theorem B1083365 : Blo 718322 1083365 := bbase (se 4 (by rfl) ⟨101565, by rfl⟩ : syracuseStep 1083365 = 203131) (by norm_num)
theorem B1214453 : Blo 718322 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B1083389 : Blo 718322 1083389 := bbase (se 3 (by rfl) ⟨203135, by rfl⟩ : syracuseStep 1083389 = 406271) (by norm_num)
theorem B1083413 : Blo 718322 1083413 := bbase (se 6 (by rfl) ⟨25392, by rfl⟩ : syracuseStep 1083413 = 50785) (by norm_num)
theorem B1083437 : Blo 718322 1083437 := bbase (se 3 (by rfl) ⟨203144, by rfl⟩ : syracuseStep 1083437 = 406289) (by norm_num)
theorem B1083461 : Blo 718322 1083461 := bbase (se 4 (by rfl) ⟨101574, by rfl⟩ : syracuseStep 1083461 = 203149) (by norm_num)
theorem B53413973 : Blo 718322 53413973 := bbase (se 8 (by rfl) ⟨312972, by rfl⟩ : syracuseStep 53413973 = 625945) (by norm_num)
theorem B1542245 : Blo 718322 1542245 := bbase (se 4 (by rfl) ⟨144585, by rfl⟩ : syracuseStep 1542245 = 289171) (by norm_num)
theorem B1214581 : Blo 718322 1214581 := bbase (se 5 (by rfl) ⟨56933, by rfl⟩ : syracuseStep 1214581 = 113867) (by norm_num)
theorem B2492549 : Blo 718322 2492549 := bbase (se 4 (by rfl) ⟨233676, by rfl⟩ : syracuseStep 2492549 = 467353) (by norm_num)
theorem B3082373 : Blo 718322 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B2427029 : Blo 718322 2427029 := bbase (se 6 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 2427029 = 113767) (by norm_num)
theorem B1214669 : Blo 718322 1214669 := bbase (se 3 (by rfl) ⟨227750, by rfl⟩ : syracuseStep 1214669 = 455501) (by norm_num)
theorem B1214797 : Blo 718322 1214797 := bbase (se 3 (by rfl) ⟨227774, by rfl⟩ : syracuseStep 1214797 = 455549) (by norm_num)
theorem B1542485 : Blo 718322 1542485 := bbase (se 10 (by rfl) ⟨2259, by rfl⟩ : syracuseStep 1542485 = 4519) (by norm_num)
theorem B3639653 : Blo 718322 3639653 := bbase (se 4 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 3639653 = 682435) (by norm_num)
theorem B1214885 : Blo 718322 1214885 := bbase (se 4 (by rfl) ⟨113895, by rfl⟩ : syracuseStep 1214885 = 227791) (by norm_num)
theorem B2591237 : Blo 718322 2591237 := bbase (se 4 (by rfl) ⟨242928, by rfl⟩ : syracuseStep 2591237 = 485857) (by norm_num)
theorem B1215013 : Blo 718322 1215013 := bbase (se 4 (by rfl) ⟨113907, by rfl⟩ : syracuseStep 1215013 = 227815) (by norm_num)
theorem B2427461 : Blo 718322 2427461 := bbase (se 4 (by rfl) ⟨227574, by rfl⟩ : syracuseStep 2427461 = 455149) (by norm_num)
theorem B1215101 : Blo 718322 1215101 := bbase (se 3 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 1215101 = 455663) (by norm_num)
theorem B822001 : Blo 718322 822001 := bbase (se 2 (by rfl) ⟨308250, by rfl⟩ : syracuseStep 822001 = 616501) (by norm_num)
theorem B1215229 : Blo 718322 1215229 := bbase (se 3 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 1215229 = 455711) (by norm_num)
theorem B1641293 : Blo 718322 1641293 := bbase (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) (by norm_num)
theorem B1215317 : Blo 718322 1215317 := bbase (se 9 (by rfl) ⟨3560, by rfl⟩ : syracuseStep 1215317 = 7121) (by norm_num)
theorem B1215445 : Blo 718322 1215445 := bbase (se 7 (by rfl) ⟨14243, by rfl⟩ : syracuseStep 1215445 = 28487) (by norm_num)
theorem B822253 : Blo 718322 822253 := bbase (se 3 (by rfl) ⟨154172, by rfl⟩ : syracuseStep 822253 = 308345) (by norm_num)
theorem B2427893 : Blo 718322 2427893 := bbase (se 5 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 2427893 = 227615) (by norm_num)
theorem B1215533 : Blo 718322 1215533 := bbase (se 3 (by rfl) ⟨227912, by rfl⟩ : syracuseStep 1215533 = 455825) (by norm_num)
theorem B1215661 : Blo 718322 1215661 := bbase (se 3 (by rfl) ⟨227936, by rfl⟩ : syracuseStep 1215661 = 455873) (by norm_num)
theorem B1215749 : Blo 718322 1215749 := bbase (se 4 (by rfl) ⟨113976, by rfl⟩ : syracuseStep 1215749 = 227953) (by norm_num)
theorem B4099349 : Blo 718322 4099349 := bbase (se 6 (by rfl) ⟨96078, by rfl⟩ : syracuseStep 4099349 = 192157) (by norm_num)
theorem B52596053 : Blo 718322 52596053 := bbase (se 11 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 52596053 = 77045) (by norm_num)
theorem B1215877 : Blo 718322 1215877 := bbase (se 4 (by rfl) ⟨113988, by rfl⟩ : syracuseStep 1215877 = 227977) (by norm_num)
theorem B1478045 : Blo 718322 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B2428325 : Blo 718322 2428325 := bbase (se 4 (by rfl) ⟨227655, by rfl⟩ : syracuseStep 2428325 = 455311) (by norm_num)
theorem B7769557 : Blo 718322 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B1215965 : Blo 718322 1215965 := bbase (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) (by norm_num)
theorem B1216093 : Blo 718322 1216093 := bbase (se 3 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 1216093 = 456035) (by norm_num)
theorem B3640949 : Blo 718322 3640949 := bbase (se 5 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 3640949 = 341339) (by norm_num)
theorem B1216181 : Blo 718322 1216181 := bbase (se 5 (by rfl) ⟨57008, by rfl⟩ : syracuseStep 1216181 = 114017) (by norm_num)
theorem B1216309 : Blo 718322 1216309 := bbase (se 5 (by rfl) ⟨57014, by rfl⟩ : syracuseStep 1216309 = 114029) (by norm_num)
theorem B986941 : Blo 718322 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B2428757 : Blo 718322 2428757 := bbase (se 9 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 2428757 = 14231) (by norm_num)
theorem B3084149 : Blo 718322 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B2527109 : Blo 718322 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B1216397 : Blo 718322 1216397 := bbase (se 3 (by rfl) ⟨228074, by rfl⟩ : syracuseStep 1216397 = 456149) (by norm_num)
theorem B823241 : Blo 718322 823241 := bbase (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) (by norm_num)
theorem B1216525 : Blo 718322 1216525 := bbase (se 3 (by rfl) ⟨228098, by rfl⟩ : syracuseStep 1216525 = 456197) (by norm_num)
theorem B1478741 : Blo 718322 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B1216613 : Blo 718322 1216613 := bbase (se 4 (by rfl) ⟨114057, by rfl⟩ : syracuseStep 1216613 = 228115) (by norm_num)
theorem B3084389 : Blo 718322 3084389 := bbase (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) (by norm_num)
theorem B921817 : Blo 718322 921817 := bbase (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) (by norm_num)
theorem B1216741 : Blo 718322 1216741 := bbase (se 4 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 1216741 = 228139) (by norm_num)
theorem B2429189 : Blo 718322 2429189 := bbase (se 4 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 2429189 = 455473) (by norm_num)
theorem B1216829 : Blo 718322 1216829 := bbase (se 3 (by rfl) ⟨228155, by rfl⟩ : syracuseStep 1216829 = 456311) (by norm_num)
theorem B1151405 : Blo 718322 1151405 := bbase (se 3 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 1151405 = 431777) (by norm_num)
theorem B1216957 : Blo 718322 1216957 := bbase (se 3 (by rfl) ⟨228179, by rfl⟩ : syracuseStep 1216957 = 456359) (by norm_num)
theorem B922093 : Blo 718322 922093 := bbase (se 3 (by rfl) ⟨172892, by rfl⟩ : syracuseStep 922093 = 345785) (by norm_num)
theorem B1151501 : Blo 718322 1151501 := bbase (se 3 (by rfl) ⟨215906, by rfl⟩ : syracuseStep 1151501 = 431813) (by norm_num)
theorem B1217045 : Blo 718322 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B1151533 : Blo 718322 1151533 := bbase (se 3 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 1151533 = 431825) (by norm_num)
theorem B1217173 : Blo 718322 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B2429621 : Blo 718322 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B1217261 : Blo 718322 1217261 := bbase (se 3 (by rfl) ⟨228236, by rfl⟩ : syracuseStep 1217261 = 456473) (by norm_num)
theorem B1217389 : Blo 718322 1217389 := bbase (se 3 (by rfl) ⟨228260, by rfl⟩ : syracuseStep 1217389 = 456521) (by norm_num)
theorem B3642245 : Blo 718322 3642245 := bbase (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) (by norm_num)
theorem B8426389 : Blo 718322 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B1217477 : Blo 718322 1217477 := bbase (se 4 (by rfl) ⟨114138, by rfl⟩ : syracuseStep 1217477 = 228277) (by norm_num)
theorem B1217605 : Blo 718322 1217605 := bbase (se 4 (by rfl) ⟨114150, by rfl⟩ : syracuseStep 1217605 = 228301) (by norm_num)
theorem B2430053 : Blo 718322 2430053 := bbase (se 4 (by rfl) ⟨227817, by rfl⟩ : syracuseStep 2430053 = 455635) (by norm_num)
theorem B1217693 : Blo 718322 1217693 := bbase (se 3 (by rfl) ⟨228317, by rfl⟩ : syracuseStep 1217693 = 456635) (by norm_num)
theorem B1217821 : Blo 718322 1217821 := bbase (se 3 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 1217821 = 456683) (by norm_num)
theorem B1217909 : Blo 718322 1217909 := bbase (se 5 (by rfl) ⟨57089, by rfl⟩ : syracuseStep 1217909 = 114179) (by norm_num)
theorem B1218037 : Blo 718322 1218037 := bbase (se 5 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 1218037 = 114191) (by norm_num)
theorem B1873405 : Blo 718322 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B2430485 : Blo 718322 2430485 := bbase (se 6 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 2430485 = 113929) (by norm_num)
theorem B1218125 : Blo 718322 1218125 := bbase (se 3 (by rfl) ⟨228398, by rfl⟩ : syracuseStep 1218125 = 456797) (by norm_num)
theorem B1316525 : Blo 718322 1316525 := bbase (se 3 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 1316525 = 493697) (by norm_num)
theorem B1218253 : Blo 718322 1218253 := bbase (se 3 (by rfl) ⟨228422, by rfl⟩ : syracuseStep 1218253 = 456845) (by norm_num)
theorem B1218341 : Blo 718322 1218341 := bbase (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) (by norm_num)
theorem B4626325 : Blo 718322 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B1218469 : Blo 718322 1218469 := bbase (se 4 (by rfl) ⟨114231, by rfl⟩ : syracuseStep 1218469 = 228463) (by norm_num)
theorem B2430917 : Blo 718322 2430917 := bbase (se 4 (by rfl) ⟨227898, by rfl⟩ : syracuseStep 2430917 = 455797) (by norm_num)
theorem B1218557 : Blo 718322 1218557 := bbase (se 3 (by rfl) ⟨228479, by rfl⟩ : syracuseStep 1218557 = 456959) (by norm_num)
theorem B923653 : Blo 718322 923653 := bbase (se 4 (by rfl) ⟨86592, by rfl⟩ : syracuseStep 923653 = 173185) (by norm_num)
theorem B1153045 : Blo 718322 1153045 := bbase (se 6 (by rfl) ⟨27024, by rfl⟩ : syracuseStep 1153045 = 54049) (by norm_num)
theorem B1316893 : Blo 718322 1316893 := bbase (se 3 (by rfl) ⟨246917, by rfl⟩ : syracuseStep 1316893 = 493835) (by norm_num)
theorem B1218685 : Blo 718322 1218685 := bbase (se 3 (by rfl) ⟨228503, by rfl⟩ : syracuseStep 1218685 = 457007) (by norm_num)
theorem B3643541 : Blo 718322 3643541 := bbase (se 6 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 3643541 = 170791) (by norm_num)
theorem B1218773 : Blo 718322 1218773 := bbase (se 7 (by rfl) ⟨14282, by rfl⟩ : syracuseStep 1218773 = 28565) (by norm_num)
theorem B5478677 : Blo 718322 5478677 := bbase (se 6 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 5478677 = 256813) (by norm_num)
theorem B1644877 : Blo 718322 1644877 := bbase (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) (by norm_num)
theorem B1218901 : Blo 718322 1218901 := bbase (se 10 (by rfl) ⟨1785, by rfl⟩ : syracuseStep 1218901 = 3571) (by norm_num)
theorem B2431349 : Blo 718322 2431349 := bbase (se 5 (by rfl) ⟨113969, by rfl⟩ : syracuseStep 2431349 = 227939) (by norm_num)
theorem B1153757 : Blo 718322 1153757 := bbase (se 3 (by rfl) ⟨216329, by rfl⟩ : syracuseStep 1153757 = 432659) (by norm_num)
theorem B2431781 : Blo 718322 2431781 := bbase (se 4 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 2431781 = 455959) (by norm_num)
theorem B2923381 : Blo 718322 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B728137 : Blo 718322 728137 := bbase (se 2 (by rfl) ⟨273051, by rfl⟩ : syracuseStep 728137 = 546103) (by norm_num)
theorem B2432213 : Blo 718322 2432213 := bbase (se 7 (by rfl) ⟨28502, by rfl⟩ : syracuseStep 2432213 = 57005) (by norm_num)
theorem B1023197 : Blo 718322 1023197 := bbase (se 3 (by rfl) ⟨191849, by rfl⟩ : syracuseStep 1023197 = 383699) (by norm_num)
theorem B728425 : Blo 718322 728425 := bbase (se 2 (by rfl) ⟨273159, by rfl⟩ : syracuseStep 728425 = 546319) (by norm_num)
theorem B1154429 : Blo 718322 1154429 := bbase (se 3 (by rfl) ⟨216455, by rfl⟩ : syracuseStep 1154429 = 432911) (by norm_num)
theorem B3644837 : Blo 718322 3644837 := bbase (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) (by norm_num)
theorem B1383925 : Blo 718322 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B1383941 : Blo 718322 1383941 := bbase (se 4 (by rfl) ⟨129744, by rfl⟩ : syracuseStep 1383941 = 259489) (by norm_num)
theorem B4562453 : Blo 718322 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B2367029 : Blo 718322 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B2432645 : Blo 718322 2432645 := bbase (se 4 (by rfl) ⟨228060, by rfl⟩ : syracuseStep 2432645 = 456121) (by norm_num)
theorem B2301605 : Blo 718322 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B2629397 : Blo 718322 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B6922037 : Blo 718322 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B1154941 : Blo 718322 1154941 := bbase (se 3 (by rfl) ⟨216551, by rfl⟩ : syracuseStep 1154941 = 433103) (by norm_num)
theorem B1023949 : Blo 718322 1023949 := bbase (se 3 (by rfl) ⟨191990, by rfl⟩ : syracuseStep 1023949 = 383981) (by norm_num)
theorem B1843181 : Blo 718322 1843181 := bbase (se 3 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 1843181 = 691193) (by norm_num)
theorem B2433077 : Blo 718322 2433077 := bbase (se 5 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 2433077 = 228101) (by norm_num)
theorem B729281 : Blo 718322 729281 := bbase (se 2 (by rfl) ⟨273480, by rfl⟩ : syracuseStep 729281 = 546961) (by norm_num)
theorem B1155397 : Blo 718322 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B1647013 : Blo 718322 1647013 := bbase (se 4 (by rfl) ⟨154407, by rfl⟩ : syracuseStep 1647013 = 308815) (by norm_num)
theorem B1647029 : Blo 718322 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B2433509 : Blo 718322 2433509 := bbase (se 4 (by rfl) ⟨228141, by rfl⟩ : syracuseStep 2433509 = 456283) (by norm_num)
theorem B2302501 : Blo 718322 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B3646133 : Blo 718322 3646133 := bbase (se 5 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 3646133 = 341825) (by norm_num)
theorem B5415605 : Blo 718322 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B1024741 : Blo 718322 1024741 := bbase (se 4 (by rfl) ⟨96069, by rfl⟩ : syracuseStep 1024741 = 192139) (by norm_num)
theorem B729937 : Blo 718322 729937 := bbase (se 2 (by rfl) ⟨273726, by rfl⟩ : syracuseStep 729937 = 547453) (by norm_num)
theorem B729953 : Blo 718322 729953 := bbase (se 2 (by rfl) ⟨273732, by rfl⟩ : syracuseStep 729953 = 547465) (by norm_num)
theorem B2433941 : Blo 718322 2433941 := bbase (se 6 (by rfl) ⟨57045, by rfl⟩ : syracuseStep 2433941 = 114091) (by norm_num)
theorem B2302901 : Blo 718322 2302901 := bbase (se 5 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 2302901 = 215897) (by norm_num)
theorem B1156069 : Blo 718322 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B2728997 : Blo 718322 2728997 := bbase (se 4 (by rfl) ⟨255843, by rfl⟩ : syracuseStep 2728997 = 511687) (by norm_num)
theorem B1025077 : Blo 718322 1025077 := bbase (se 5 (by rfl) ⟨48050, by rfl⟩ : syracuseStep 1025077 = 96101) (by norm_num)
theorem B730181 : Blo 718322 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B2598101 : Blo 718322 2598101 := bbase (se 7 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 2598101 = 60893) (by norm_num)
theorem B3122405 : Blo 718322 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B1025293 : Blo 718322 1025293 := bbase (se 3 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 1025293 = 384485) (by norm_num)
theorem B2729285 : Blo 718322 2729285 := bbase (se 4 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 2729285 = 511741) (by norm_num)
theorem B2434373 : Blo 718322 2434373 := bbase (se 4 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 2434373 = 456445) (by norm_num)
theorem B1156493 : Blo 718322 1156493 := bbase (se 3 (by rfl) ⟨216842, by rfl⟩ : syracuseStep 1156493 = 433685) (by norm_num)
theorem B2598389 : Blo 718322 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B730729 : Blo 718322 730729 := bbase (se 2 (by rfl) ⟨274023, by rfl⟩ : syracuseStep 730729 = 548047) (by norm_num)
theorem B1025669 : Blo 718322 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B2598533 : Blo 718322 2598533 := bbase (se 4 (by rfl) ⟨243612, by rfl⟩ : syracuseStep 2598533 = 487225) (by norm_num)
theorem B1156781 : Blo 718322 1156781 := bbase (se 3 (by rfl) ⟨216896, by rfl⟩ : syracuseStep 1156781 = 433793) (by norm_num)
theorem B2434805 : Blo 718322 2434805 := bbase (se 5 (by rfl) ⟨114131, by rfl⟩ : syracuseStep 2434805 = 228263) (by norm_num)
theorem B3647429 : Blo 718322 3647429 := bbase (se 4 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 3647429 = 683893) (by norm_num)
theorem B2435237 : Blo 718322 2435237 := bbase (se 4 (by rfl) ⟨228303, by rfl⟩ : syracuseStep 2435237 = 456607) (by norm_num)
theorem B1943765 : Blo 718322 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B731413 : Blo 718322 731413 := bbase (se 6 (by rfl) ⟨17142, by rfl⟩ : syracuseStep 731413 = 34285) (by norm_num)
theorem B1616237 : Blo 718322 1616237 := bbase (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) (by norm_num)
theorem B2107765 : Blo 718322 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B1616309 : Blo 718322 1616309 := bbase (se 5 (by rfl) ⟨75764, by rfl⟩ : syracuseStep 1616309 = 151529) (by norm_num)
theorem B2730469 : Blo 718322 2730469 := bbase (se 4 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 2730469 = 511963) (by norm_num)
theorem B1616381 : Blo 718322 1616381 := bbase (se 3 (by rfl) ⟨303071, by rfl⟩ : syracuseStep 1616381 = 606143) (by norm_num)
theorem B1616453 : Blo 718322 1616453 := bbase (se 4 (by rfl) ⟨151542, by rfl⟩ : syracuseStep 1616453 = 303085) (by norm_num)
theorem B2435669 : Blo 718322 2435669 := bbase (se 8 (by rfl) ⟨14271, by rfl⟩ : syracuseStep 2435669 = 28543) (by norm_num)
theorem B1616525 : Blo 718322 1616525 := bbase (se 3 (by rfl) ⟨303098, by rfl⟩ : syracuseStep 1616525 = 606197) (by norm_num)
theorem B1616597 : Blo 718322 1616597 := bbase (se 7 (by rfl) ⟨18944, by rfl⟩ : syracuseStep 1616597 = 37889) (by norm_num)
theorem B2730773 : Blo 718322 2730773 := bbase (se 6 (by rfl) ⟨64002, by rfl⟩ : syracuseStep 2730773 = 128005) (by norm_num)
theorem B1616669 : Blo 718322 1616669 := bbase (se 3 (by rfl) ⟨303125, by rfl⟩ : syracuseStep 1616669 = 606251) (by norm_num)
theorem B1616741 : Blo 718322 1616741 := bbase (se 4 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 1616741 = 303139) (by norm_num)
theorem B732029 : Blo 718322 732029 := bbase (se 3 (by rfl) ⟨137255, by rfl⟩ : syracuseStep 732029 = 274511) (by norm_num)
theorem B6138773 : Blo 718322 6138773 := bbase (se 6 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 6138773 = 287755) (by norm_num)
theorem B1616813 : Blo 718322 1616813 := bbase (se 3 (by rfl) ⟨303152, by rfl⟩ : syracuseStep 1616813 = 606305) (by norm_num)
theorem B1616885 : Blo 718322 1616885 := bbase (se 5 (by rfl) ⟨75791, by rfl⟩ : syracuseStep 1616885 = 151583) (by norm_num)
theorem B2436101 : Blo 718322 2436101 := bbase (se 4 (by rfl) ⟨228384, by rfl⟩ : syracuseStep 2436101 = 456769) (by norm_num)
theorem B1027093 : Blo 718322 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B1616957 : Blo 718322 1616957 := bbase (se 3 (by rfl) ⟨303179, by rfl⟩ : syracuseStep 1616957 = 606359) (by norm_num)
theorem B1846381 : Blo 718322 1846381 := bbase (se 3 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 1846381 = 692393) (by norm_num)
theorem B1617029 : Blo 718322 1617029 := bbase (se 4 (by rfl) ⟨151596, by rfl⟩ : syracuseStep 1617029 = 303193) (by norm_num)
theorem B1617101 : Blo 718322 1617101 := bbase (se 3 (by rfl) ⟨303206, by rfl⟩ : syracuseStep 1617101 = 606413) (by norm_num)
theorem B3648725 : Blo 718322 3648725 := bbase (se 7 (by rfl) ⟨42758, by rfl⟩ : syracuseStep 3648725 = 85517) (by norm_num)
theorem B1617173 : Blo 718322 1617173 := bbase (se 6 (by rfl) ⟨37902, by rfl⟩ : syracuseStep 1617173 = 75805) (by norm_num)
theorem B6663509 : Blo 718322 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B1617245 : Blo 718322 1617245 := bbase (se 3 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 1617245 = 606467) (by norm_num)
theorem B1617317 : Blo 718322 1617317 := bbase (se 4 (by rfl) ⟨151623, by rfl⟩ : syracuseStep 1617317 = 303247) (by norm_num)
theorem B863669 : Blo 718322 863669 := bbase (se 5 (by rfl) ⟨40484, by rfl⟩ : syracuseStep 863669 = 80969) (by norm_num)
theorem B2436533 : Blo 718322 2436533 := bbase (se 5 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 2436533 = 228425) (by norm_num)
theorem B863717 : Blo 718322 863717 := bbase (se 4 (by rfl) ⟨80973, by rfl⟩ : syracuseStep 863717 = 161947) (by norm_num)
theorem B1617389 : Blo 718322 1617389 := bbase (se 3 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 1617389 = 606521) (by norm_num)
theorem B1617461 : Blo 718322 1617461 := bbase (se 5 (by rfl) ⟨75818, by rfl⟩ : syracuseStep 1617461 = 151637) (by norm_num)
theorem B1027685 : Blo 718322 1027685 := bbase (se 4 (by rfl) ⟨96345, by rfl⟩ : syracuseStep 1027685 = 192691) (by norm_num)
theorem B1617533 : Blo 718322 1617533 := bbase (se 3 (by rfl) ⟨303287, by rfl⟩ : syracuseStep 1617533 = 606575) (by norm_num)
theorem B1027765 : Blo 718322 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B1617605 : Blo 718322 1617605 := bbase (se 4 (by rfl) ⟨151650, by rfl⟩ : syracuseStep 1617605 = 303301) (by norm_num)
theorem B1093349 : Blo 718322 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B1617677 : Blo 718322 1617677 := bbase (se 3 (by rfl) ⟨303314, by rfl⟩ : syracuseStep 1617677 = 606629) (by norm_num)
theorem B1027885 : Blo 718322 1027885 := bbase (se 3 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 1027885 = 385457) (by norm_num)
theorem B1617749 : Blo 718322 1617749 := bbase (se 9 (by rfl) ⟨4739, by rfl⟩ : syracuseStep 1617749 = 9479) (by norm_num)
theorem B2436965 : Blo 718322 2436965 := bbase (se 4 (by rfl) ⟨228465, by rfl⟩ : syracuseStep 2436965 = 456931) (by norm_num)
theorem B1027981 : Blo 718322 1027981 := bbase (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) (by norm_num)
theorem B1617821 : Blo 718322 1617821 := bbase (se 3 (by rfl) ⟨303341, by rfl⟩ : syracuseStep 1617821 = 606683) (by norm_num)
theorem B1617893 : Blo 718322 1617893 := bbase (se 4 (by rfl) ⟨151677, by rfl⟩ : syracuseStep 1617893 = 303355) (by norm_num)
theorem B3289061 : Blo 718322 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B864265 : Blo 718322 864265 := bbase (se 2 (by rfl) ⟨324099, by rfl⟩ : syracuseStep 864265 = 648199) (by norm_num)
theorem B1617965 : Blo 718322 1617965 := bbase (se 3 (by rfl) ⟨303368, by rfl⟩ : syracuseStep 1617965 = 606737) (by norm_num)
theorem B1618037 : Blo 718322 1618037 := bbase (se 5 (by rfl) ⟨75845, by rfl⟩ : syracuseStep 1618037 = 151691) (by norm_num)
theorem B1618109 : Blo 718322 1618109 := bbase (se 3 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 1618109 = 606791) (by norm_num)
theorem B1618181 : Blo 718322 1618181 := bbase (se 4 (by rfl) ⟨151704, by rfl⟩ : syracuseStep 1618181 = 303409) (by norm_num)
theorem B2437397 : Blo 718322 2437397 := bbase (se 6 (by rfl) ⟨57126, by rfl⟩ : syracuseStep 2437397 = 114253) (by norm_num)
theorem B1093933 : Blo 718322 1093933 := bbase (se 3 (by rfl) ⟨205112, by rfl⟩ : syracuseStep 1093933 = 410225) (by norm_num)
theorem B1618253 : Blo 718322 1618253 := bbase (se 3 (by rfl) ⟨303422, by rfl⟩ : syracuseStep 1618253 = 606845) (by norm_num)
theorem B1618325 : Blo 718322 1618325 := bbase (se 6 (by rfl) ⟨37929, by rfl⟩ : syracuseStep 1618325 = 75859) (by norm_num)
theorem B1618397 : Blo 718322 1618397 := bbase (se 3 (by rfl) ⟨303449, by rfl⟩ : syracuseStep 1618397 = 606899) (by norm_num)
theorem B3650021 : Blo 718322 3650021 := bbase (se 4 (by rfl) ⟨342189, by rfl⟩ : syracuseStep 3650021 = 684379) (by norm_num)
theorem B864745 : Blo 718322 864745 := bbase (se 2 (by rfl) ⟨324279, by rfl⟩ : syracuseStep 864745 = 648559) (by norm_num)
theorem B12497429 : Blo 718322 12497429 := bbase (se 6 (by rfl) ⟨292908, by rfl⟩ : syracuseStep 12497429 = 585817) (by norm_num)
theorem B1618469 : Blo 718322 1618469 := bbase (se 4 (by rfl) ⟨151731, by rfl⟩ : syracuseStep 1618469 = 303463) (by norm_num)
theorem B1618541 : Blo 718322 1618541 := bbase (se 3 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 1618541 = 606953) (by norm_num)
theorem B2306693 : Blo 718322 2306693 := bbase (se 4 (by rfl) ⟨216252, by rfl⟩ : syracuseStep 2306693 = 432505) (by norm_num)
theorem B1618613 : Blo 718322 1618613 := bbase (se 5 (by rfl) ⟨75872, by rfl⟩ : syracuseStep 1618613 = 151745) (by norm_num)
theorem B2437829 : Blo 718322 2437829 := bbase (se 4 (by rfl) ⟨228546, by rfl⟩ : syracuseStep 2437829 = 457093) (by norm_num)
theorem B1618685 : Blo 718322 1618685 := bbase (se 3 (by rfl) ⟨303503, by rfl⟩ : syracuseStep 1618685 = 607007) (by norm_num)
theorem B2601733 : Blo 718322 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B1618757 : Blo 718322 1618757 := bbase (se 4 (by rfl) ⟨151758, by rfl⟩ : syracuseStep 1618757 = 303517) (by norm_num)
theorem B2732885 : Blo 718322 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B1618829 : Blo 718322 1618829 := bbase (se 3 (by rfl) ⟨303530, by rfl⟩ : syracuseStep 1618829 = 607061) (by norm_num)
theorem B1946533 : Blo 718322 1946533 := bbase (se 4 (by rfl) ⟨182487, by rfl⟩ : syracuseStep 1946533 = 364975) (by norm_num)
theorem B4109237 : Blo 718322 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B1618901 : Blo 718322 1618901 := bbase (se 7 (by rfl) ⟨18971, by rfl⟩ : syracuseStep 1618901 = 37943) (by norm_num)
theorem B1618973 : Blo 718322 1618973 := bbase (se 3 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 1618973 = 607115) (by norm_num)
theorem B7025717 : Blo 718322 7025717 := bbase (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) (by norm_num)
theorem B1619045 : Blo 718322 1619045 := bbase (se 4 (by rfl) ⟨151785, by rfl⟩ : syracuseStep 1619045 = 303571) (by norm_num)
theorem B2733173 : Blo 718322 2733173 := bbase (se 5 (by rfl) ⟨128117, by rfl⟩ : syracuseStep 2733173 = 256235) (by norm_num)
theorem B1094797 : Blo 718322 1094797 := bbase (se 3 (by rfl) ⟨205274, by rfl⟩ : syracuseStep 1094797 = 410549) (by norm_num)
theorem B1619117 : Blo 718322 1619117 := bbase (se 3 (by rfl) ⟨303584, by rfl⟩ : syracuseStep 1619117 = 607169) (by norm_num)
theorem B2602181 : Blo 718322 2602181 := bbase (se 4 (by rfl) ⟨243954, by rfl⟩ : syracuseStep 2602181 = 487909) (by norm_num)
theorem B767189 : Blo 718322 767189 := bbase (se 7 (by rfl) ⟨8990, by rfl⟩ : syracuseStep 767189 = 17981) (by norm_num)
theorem B1619189 : Blo 718322 1619189 := bbase (se 5 (by rfl) ⟨75899, by rfl⟩ : syracuseStep 1619189 = 151799) (by norm_num)
theorem B1619261 : Blo 718322 1619261 := bbase (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) (by norm_num)
theorem B865625 : Blo 718322 865625 := bbase (se 2 (by rfl) ⟨324609, by rfl⟩ : syracuseStep 865625 = 649219) (by norm_num)
theorem B1619333 : Blo 718322 1619333 := bbase (se 4 (by rfl) ⟨151812, by rfl⟩ : syracuseStep 1619333 = 303625) (by norm_num)
theorem B1619405 : Blo 718322 1619405 := bbase (se 3 (by rfl) ⟨303638, by rfl⟩ : syracuseStep 1619405 = 607277) (by norm_num)
theorem B865741 : Blo 718322 865741 := bbase (se 3 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 865741 = 324653) (by norm_num)
theorem B767441 : Blo 718322 767441 := bbase (se 2 (by rfl) ⟨287790, by rfl⟩ : syracuseStep 767441 = 575581) (by norm_num)
theorem B1095125 : Blo 718322 1095125 := bbase (se 7 (by rfl) ⟨12833, by rfl⟩ : syracuseStep 1095125 = 25667) (by norm_num)
theorem B2471381 : Blo 718322 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B1848845 : Blo 718322 1848845 := bbase (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) (by norm_num)
theorem B1619477 : Blo 718322 1619477 := bbase (se 6 (by rfl) ⟨37956, by rfl⟩ : syracuseStep 1619477 = 75913) (by norm_num)
theorem B1619549 : Blo 718322 1619549 := bbase (se 3 (by rfl) ⟨303665, by rfl⟩ : syracuseStep 1619549 = 607331) (by norm_num)
theorem B865937 : Blo 718322 865937 := bbase (se 2 (by rfl) ⟨324726, by rfl⟩ : syracuseStep 865937 = 649453) (by norm_num)
theorem B1619621 : Blo 718322 1619621 := bbase (se 4 (by rfl) ⟨151839, by rfl⟩ : syracuseStep 1619621 = 303679) (by norm_num)
theorem B2307781 : Blo 718322 2307781 := bbase (se 4 (by rfl) ⟨216354, by rfl⟩ : syracuseStep 2307781 = 432709) (by norm_num)
theorem B1947365 : Blo 718322 1947365 := bbase (se 4 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 1947365 = 365131) (by norm_num)
theorem B1619693 : Blo 718322 1619693 := bbase (se 3 (by rfl) ⟨303692, by rfl⟩ : syracuseStep 1619693 = 607385) (by norm_num)
theorem B3651317 : Blo 718322 3651317 := bbase (se 5 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 3651317 = 342311) (by norm_num)
theorem B1619765 : Blo 718322 1619765 := bbase (se 5 (by rfl) ⟨75926, by rfl⟩ : syracuseStep 1619765 = 151853) (by norm_num)
theorem B1619837 : Blo 718322 1619837 := bbase (se 3 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 1619837 = 607439) (by norm_num)
theorem B767885 : Blo 718322 767885 := bbase (se 3 (by rfl) ⟨143978, by rfl⟩ : syracuseStep 767885 = 287957) (by norm_num)
theorem B2045893 : Blo 718322 2045893 := bbase (se 4 (by rfl) ⟨191802, by rfl⟩ : syracuseStep 2045893 = 383605) (by norm_num)
theorem B1619909 : Blo 718322 1619909 := bbase (se 4 (by rfl) ⟨151866, by rfl⟩ : syracuseStep 1619909 = 303733) (by norm_num)
theorem B1619981 : Blo 718322 1619981 := bbase (se 3 (by rfl) ⟨303746, by rfl⟩ : syracuseStep 1619981 = 607493) (by norm_num)
theorem B1620053 : Blo 718322 1620053 := bbase (se 8 (by rfl) ⟨9492, by rfl⟩ : syracuseStep 1620053 = 18985) (by norm_num)
theorem B2046053 : Blo 718322 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B768133 : Blo 718322 768133 := bbase (se 4 (by rfl) ⟨72012, by rfl⟩ : syracuseStep 768133 = 144025) (by norm_num)
theorem B1620125 : Blo 718322 1620125 := bbase (se 3 (by rfl) ⟨303773, by rfl⟩ : syracuseStep 1620125 = 607547) (by norm_num)
theorem B866485 : Blo 718322 866485 := bbase (se 5 (by rfl) ⟨40616, by rfl⟩ : syracuseStep 866485 = 81233) (by norm_num)
theorem B1620197 : Blo 718322 1620197 := bbase (se 4 (by rfl) ⟨151893, by rfl⟩ : syracuseStep 1620197 = 303787) (by norm_num)
theorem B2734357 : Blo 718322 2734357 := bbase (se 6 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 2734357 = 128173) (by norm_num)
theorem B1620269 : Blo 718322 1620269 := bbase (se 3 (by rfl) ⟨303800, by rfl⟩ : syracuseStep 1620269 = 607601) (by norm_num)
theorem B866629 : Blo 718322 866629 := bbase (se 4 (by rfl) ⟨81246, by rfl⟩ : syracuseStep 866629 = 162493) (by norm_num)
theorem B2046293 : Blo 718322 2046293 := bbase (se 10 (by rfl) ⟨2997, by rfl⟩ : syracuseStep 2046293 = 5995) (by norm_num)
theorem B1620341 : Blo 718322 1620341 := bbase (se 5 (by rfl) ⟨75953, by rfl⟩ : syracuseStep 1620341 = 151907) (by norm_num)
theorem B1620413 : Blo 718322 1620413 := bbase (se 3 (by rfl) ⟨303827, by rfl⟩ : syracuseStep 1620413 = 607655) (by norm_num)
theorem B1096141 : Blo 718322 1096141 := bbase (se 3 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 1096141 = 411053) (by norm_num)
theorem B5257685 : Blo 718322 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B1849853 : Blo 718322 1849853 := bbase (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) (by norm_num)
theorem B1620485 : Blo 718322 1620485 := bbase (se 4 (by rfl) ⟨151920, by rfl⟩ : syracuseStep 1620485 = 303841) (by norm_num)
theorem B2046485 : Blo 718322 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B768577 : Blo 718322 768577 := bbase (se 2 (by rfl) ⟨288216, by rfl⟩ : syracuseStep 768577 = 576433) (by norm_num)
theorem B2734661 : Blo 718322 2734661 := bbase (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) (by norm_num)
theorem B1620557 : Blo 718322 1620557 := bbase (se 3 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 1620557 = 607709) (by norm_num)
theorem B768637 : Blo 718322 768637 := bbase (se 3 (by rfl) ⟨144119, by rfl⟩ : syracuseStep 768637 = 288239) (by norm_num)
theorem B1620629 : Blo 718322 1620629 := bbase (se 6 (by rfl) ⟨37983, by rfl⟩ : syracuseStep 1620629 = 75967) (by norm_num)
theorem B1620701 : Blo 718322 1620701 := bbase (se 3 (by rfl) ⟨303881, by rfl⟩ : syracuseStep 1620701 = 607763) (by norm_num)
theorem B1620773 : Blo 718322 1620773 := bbase (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) (by norm_num)
theorem B2308949 : Blo 718322 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B1620845 : Blo 718322 1620845 := bbase (se 3 (by rfl) ⟨303908, by rfl⟩ : syracuseStep 1620845 = 607817) (by norm_num)
theorem B1457021 : Blo 718322 1457021 := bbase (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) (by norm_num)
theorem B1096597 : Blo 718322 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B1620917 : Blo 718322 1620917 := bbase (se 5 (by rfl) ⟨75980, by rfl⟩ : syracuseStep 1620917 = 151961) (by norm_num)
theorem B768953 : Blo 718322 768953 := bbase (se 2 (by rfl) ⟨288357, by rfl⟩ : syracuseStep 768953 = 576715) (by norm_num)
theorem B1620989 : Blo 718322 1620989 := bbase (se 3 (by rfl) ⟨303935, by rfl⟩ : syracuseStep 1620989 = 607871) (by norm_num)
theorem B3652613 : Blo 718322 3652613 := bbase (se 4 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 3652613 = 684865) (by norm_num)
theorem B1621061 : Blo 718322 1621061 := bbase (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) (by norm_num)
theorem B1621133 : Blo 718322 1621133 := bbase (se 3 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 1621133 = 607925) (by norm_num)
theorem B1621205 : Blo 718322 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B1621277 : Blo 718322 1621277 := bbase (se 3 (by rfl) ⟨303989, by rfl⟩ : syracuseStep 1621277 = 607979) (by norm_num)
theorem B867677 : Blo 718322 867677 := bbase (se 3 (by rfl) ⟨162689, by rfl⟩ : syracuseStep 867677 = 325379) (by norm_num)
theorem B1621349 : Blo 718322 1621349 := bbase (se 4 (by rfl) ⟨152001, by rfl⟩ : syracuseStep 1621349 = 304003) (by norm_num)
theorem B769397 : Blo 718322 769397 := bbase (se 5 (by rfl) ⟨36065, by rfl⟩ : syracuseStep 769397 = 72131) (by norm_num)
theorem B1621421 : Blo 718322 1621421 := bbase (se 3 (by rfl) ⟨304016, by rfl⟩ : syracuseStep 1621421 = 608033) (by norm_num)
theorem B769457 : Blo 718322 769457 := bbase (se 2 (by rfl) ⟨288546, by rfl⟩ : syracuseStep 769457 = 577093) (by norm_num)
theorem B1621493 : Blo 718322 1621493 := bbase (se 5 (by rfl) ⟨76007, by rfl⟩ : syracuseStep 1621493 = 152015) (by norm_num)
theorem B5455349 : Blo 718322 5455349 := bbase (se 5 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 5455349 = 511439) (by norm_num)
theorem B2047477 : Blo 718322 2047477 := bbase (se 5 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 2047477 = 191951) (by norm_num)
theorem B769585 : Blo 718322 769585 := bbase (se 2 (by rfl) ⟨288594, by rfl⟩ : syracuseStep 769585 = 577189) (by norm_num)
theorem B1621565 : Blo 718322 1621565 := bbase (se 3 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 1621565 = 608087) (by norm_num)
theorem B1097309 : Blo 718322 1097309 := bbase (se 3 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 1097309 = 411491) (by norm_num)
theorem B1621637 : Blo 718322 1621637 := bbase (se 4 (by rfl) ⟨152028, by rfl⟩ : syracuseStep 1621637 = 304057) (by norm_num)
theorem B1621709 : Blo 718322 1621709 := bbase (se 3 (by rfl) ⟨304070, by rfl⟩ : syracuseStep 1621709 = 608141) (by norm_num)
theorem B1556221 : Blo 718322 1556221 := bbase (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) (by norm_num)
theorem B1818389 : Blo 718322 1818389 := bbase (se 6 (by rfl) ⟨42618, by rfl⟩ : syracuseStep 1818389 = 85237) (by norm_num)
theorem B1621781 : Blo 718322 1621781 := bbase (se 6 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 1621781 = 76021) (by norm_num)
theorem B1097557 : Blo 718322 1097557 := bbase (se 9 (by rfl) ⟨3215, by rfl⟩ : syracuseStep 1097557 = 6431) (by norm_num)
theorem B1621853 : Blo 718322 1621853 := bbase (se 3 (by rfl) ⟨304097, by rfl⟩ : syracuseStep 1621853 = 608195) (by norm_num)
theorem B1621925 : Blo 718322 1621925 := bbase (se 4 (by rfl) ⟨152055, by rfl⟩ : syracuseStep 1621925 = 304111) (by norm_num)
theorem B770029 : Blo 718322 770029 := bbase (se 3 (by rfl) ⟨144380, by rfl⟩ : syracuseStep 770029 = 288761) (by norm_num)
theorem B1621997 : Blo 718322 1621997 := bbase (se 3 (by rfl) ⟨304124, by rfl⟩ : syracuseStep 1621997 = 608249) (by norm_num)
theorem B1622069 : Blo 718322 1622069 := bbase (se 5 (by rfl) ⟨76034, by rfl⟩ : syracuseStep 1622069 = 152069) (by norm_num)
theorem B770149 : Blo 718322 770149 := bbase (se 4 (by rfl) ⟨72201, by rfl⟩ : syracuseStep 770149 = 144403) (by norm_num)
theorem B1818733 : Blo 718322 1818733 := bbase (se 3 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 1818733 = 682025) (by norm_num)
theorem B1622141 : Blo 718322 1622141 := bbase (se 3 (by rfl) ⟨304151, by rfl⟩ : syracuseStep 1622141 = 608303) (by norm_num)
theorem B8896661 : Blo 718322 8896661 := bbase (se 6 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 8896661 = 417031) (by norm_num)
theorem B1294517 : Blo 718322 1294517 := bbase (se 5 (by rfl) ⟨60680, by rfl⟩ : syracuseStep 1294517 = 121361) (by norm_num)
theorem B1622213 : Blo 718322 1622213 := bbase (se 4 (by rfl) ⟨152082, by rfl⟩ : syracuseStep 1622213 = 304165) (by norm_num)
theorem B1818845 : Blo 718322 1818845 := bbase (se 3 (by rfl) ⟨341033, by rfl⟩ : syracuseStep 1818845 = 682067) (by norm_num)
theorem B1622285 : Blo 718322 1622285 := bbase (se 3 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 1622285 = 608357) (by norm_num)
theorem B3653909 : Blo 718322 3653909 := bbase (se 6 (by rfl) ⟨85638, by rfl⟩ : syracuseStep 3653909 = 171277) (by norm_num)
theorem B1622357 : Blo 718322 1622357 := bbase (se 10 (by rfl) ⟨2376, by rfl⟩ : syracuseStep 1622357 = 4753) (by norm_num)
theorem B770401 : Blo 718322 770401 := bbase (se 2 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 770401 = 577801) (by norm_num)
theorem B770405 : Blo 718322 770405 := bbase (se 4 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 770405 = 144451) (by norm_num)
theorem B1819037 : Blo 718322 1819037 := bbase (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) (by norm_num)
theorem B1622429 : Blo 718322 1622429 := bbase (se 3 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 1622429 = 608411) (by norm_num)
theorem B1622501 : Blo 718322 1622501 := bbase (se 4 (by rfl) ⟨152109, by rfl⟩ : syracuseStep 1622501 = 304219) (by norm_num)
theorem B1622573 : Blo 718322 1622573 := bbase (se 3 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 1622573 = 608465) (by norm_num)
theorem B2048581 : Blo 718322 2048581 := bbase (se 4 (by rfl) ⟨192054, by rfl⟩ : syracuseStep 2048581 = 384109) (by norm_num)
theorem B3457637 : Blo 718322 3457637 := bbase (se 4 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 3457637 = 648307) (by norm_num)
theorem B1622645 : Blo 718322 1622645 := bbase (se 5 (by rfl) ⟨76061, by rfl⟩ : syracuseStep 1622645 = 152123) (by norm_num)
theorem B2736773 : Blo 718322 2736773 := bbase (se 4 (by rfl) ⟨256572, by rfl⟩ : syracuseStep 2736773 = 513145) (by norm_num)
theorem B2310805 : Blo 718322 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B1622717 : Blo 718322 1622717 := bbase (se 3 (by rfl) ⟨304259, by rfl⟩ : syracuseStep 1622717 = 608519) (by norm_num)
theorem B1819381 : Blo 718322 1819381 := bbase (se 5 (by rfl) ⟨85283, by rfl⟩ : syracuseStep 1819381 = 170567) (by norm_num)
theorem B1622789 : Blo 718322 1622789 := bbase (se 4 (by rfl) ⟨152136, by rfl⟩ : syracuseStep 1622789 = 304273) (by norm_num)
theorem B3457829 : Blo 718322 3457829 := bbase (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) (by norm_num)
theorem B1622861 : Blo 718322 1622861 := bbase (se 3 (by rfl) ⟨304286, by rfl⟩ : syracuseStep 1622861 = 608573) (by norm_num)
theorem B1819493 : Blo 718322 1819493 := bbase (se 4 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 1819493 = 341155) (by norm_num)
theorem B1622933 : Blo 718322 1622933 := bbase (se 6 (by rfl) ⟨38037, by rfl⟩ : syracuseStep 1622933 = 76075) (by norm_num)
theorem B770969 : Blo 718322 770969 := bbase (se 2 (by rfl) ⟨289113, by rfl⟩ : syracuseStep 770969 = 578227) (by norm_num)
theorem B2737061 : Blo 718322 2737061 := bbase (se 4 (by rfl) ⟨256599, by rfl⟩ : syracuseStep 2737061 = 513199) (by norm_num)
theorem B1623005 : Blo 718322 1623005 := bbase (se 3 (by rfl) ⟨304313, by rfl⟩ : syracuseStep 1623005 = 608627) (by norm_num)
theorem B1819685 : Blo 718322 1819685 := bbase (se 4 (by rfl) ⟨170595, by rfl⟩ : syracuseStep 1819685 = 341191) (by norm_num)
theorem B1623077 : Blo 718322 1623077 := bbase (se 4 (by rfl) ⟨152163, by rfl⟩ : syracuseStep 1623077 = 304327) (by norm_num)
theorem B771157 : Blo 718322 771157 := bbase (se 8 (by rfl) ⟨4518, by rfl⟩ : syracuseStep 771157 = 9037) (by norm_num)
theorem B1623149 : Blo 718322 1623149 := bbase (se 3 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 1623149 = 608681) (by norm_num)
theorem B3458213 : Blo 718322 3458213 := bbase (se 4 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 3458213 = 648415) (by norm_num)
theorem B2802869 : Blo 718322 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1623221 : Blo 718322 1623221 := bbase (se 5 (by rfl) ⟨76088, by rfl⟩ : syracuseStep 1623221 = 152177) (by norm_num)
theorem B1459453 : Blo 718322 1459453 := bbase (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) (by norm_num)
theorem B1623293 : Blo 718322 1623293 := bbase (se 3 (by rfl) ⟨304367, by rfl⟩ : syracuseStep 1623293 = 608735) (by norm_num)
theorem B1623365 : Blo 718322 1623365 := bbase (se 4 (by rfl) ⟨152190, by rfl⟩ : syracuseStep 1623365 = 304381) (by norm_num)
theorem B1820029 : Blo 718322 1820029 := bbase (se 3 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 1820029 = 682511) (by norm_num)
theorem B1623437 : Blo 718322 1623437 := bbase (se 3 (by rfl) ⟨304394, by rfl⟩ : syracuseStep 1623437 = 608789) (by norm_num)
theorem B1623509 : Blo 718322 1623509 := bbase (se 7 (by rfl) ⟨19025, by rfl⟩ : syracuseStep 1623509 = 38051) (by norm_num)
theorem B1820141 : Blo 718322 1820141 := bbase (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) (by norm_num)
theorem B738829 : Blo 718322 738829 := bbase (se 3 (by rfl) ⟨138530, by rfl⟩ : syracuseStep 738829 = 277061) (by norm_num)
theorem B1623581 : Blo 718322 1623581 := bbase (se 3 (by rfl) ⟨304421, by rfl⟩ : syracuseStep 1623581 = 608843) (by norm_num)
theorem B1230373 : Blo 718322 1230373 := bbase (se 4 (by rfl) ⟨115347, by rfl⟩ : syracuseStep 1230373 = 230695) (by norm_num)
theorem B3655205 : Blo 718322 3655205 := bbase (se 4 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 3655205 = 685351) (by norm_num)
theorem B1623653 : Blo 718322 1623653 := bbase (se 4 (by rfl) ⟨152217, by rfl⟩ : syracuseStep 1623653 = 304435) (by norm_num)
theorem B1296037 : Blo 718322 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B1820333 : Blo 718322 1820333 := bbase (se 3 (by rfl) ⟨341312, by rfl⟩ : syracuseStep 1820333 = 682625) (by norm_num)
theorem B1623725 : Blo 718322 1623725 := bbase (se 3 (by rfl) ⟨304448, by rfl⟩ : syracuseStep 1623725 = 608897) (by norm_num)
theorem B1623797 : Blo 718322 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B1623869 : Blo 718322 1623869 := bbase (se 3 (by rfl) ⟨304475, by rfl⟩ : syracuseStep 1623869 = 608951) (by norm_num)
theorem B1296253 : Blo 718322 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B1623941 : Blo 718322 1623941 := bbase (se 4 (by rfl) ⟨152244, by rfl⟩ : syracuseStep 1623941 = 304489) (by norm_num)
theorem B1624013 : Blo 718322 1624013 := bbase (se 3 (by rfl) ⟨304502, by rfl⟩ : syracuseStep 1624013 = 609005) (by norm_num)
theorem B2312165 : Blo 718322 2312165 := bbase (se 4 (by rfl) ⟨216765, by rfl⟩ : syracuseStep 2312165 = 433531) (by norm_num)
theorem B1820677 : Blo 718322 1820677 := bbase (se 4 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 1820677 = 341377) (by norm_num)
theorem B1624085 : Blo 718322 1624085 := bbase (se 6 (by rfl) ⟨38064, by rfl⟩ : syracuseStep 1624085 = 76129) (by norm_num)
theorem B2050085 : Blo 718322 2050085 := bbase (se 4 (by rfl) ⟨192195, by rfl⟩ : syracuseStep 2050085 = 384391) (by norm_num)
theorem B2738245 : Blo 718322 2738245 := bbase (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) (by norm_num)
theorem B11683925 : Blo 718322 11683925 := bbase (se 8 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 11683925 = 136921) (by norm_num)
theorem B1624157 : Blo 718322 1624157 := bbase (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) (by norm_num)
theorem B1820789 : Blo 718322 1820789 := bbase (se 5 (by rfl) ⟨85349, by rfl⟩ : syracuseStep 1820789 = 170699) (by norm_num)
theorem B1296541 : Blo 718322 1296541 := bbase (se 3 (by rfl) ⟨243101, by rfl⟩ : syracuseStep 1296541 = 486203) (by norm_num)
theorem B1624229 : Blo 718322 1624229 := bbase (se 4 (by rfl) ⟨152271, by rfl⟩ : syracuseStep 1624229 = 304543) (by norm_num)
theorem B1624301 : Blo 718322 1624301 := bbase (se 3 (by rfl) ⟨304556, by rfl⟩ : syracuseStep 1624301 = 609113) (by norm_num)
theorem B1820981 : Blo 718322 1820981 := bbase (se 5 (by rfl) ⟨85358, by rfl⟩ : syracuseStep 1820981 = 170717) (by norm_num)
theorem B1624373 : Blo 718322 1624373 := bbase (se 5 (by rfl) ⟨76142, by rfl⟩ : syracuseStep 1624373 = 152285) (by norm_num)
theorem B2738549 : Blo 718322 2738549 := bbase (se 5 (by rfl) ⟨128369, by rfl⟩ : syracuseStep 2738549 = 256739) (by norm_num)
theorem B1624445 : Blo 718322 1624445 := bbase (se 3 (by rfl) ⟨304583, by rfl⟩ : syracuseStep 1624445 = 609167) (by norm_num)
theorem B1624517 : Blo 718322 1624517 := bbase (se 4 (by rfl) ⟨152298, by rfl⟩ : syracuseStep 1624517 = 304597) (by norm_num)
theorem B1624589 : Blo 718322 1624589 := bbase (se 3 (by rfl) ⟨304610, by rfl⟩ : syracuseStep 1624589 = 609221) (by norm_num)
theorem B5556757 : Blo 718322 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B1624661 : Blo 718322 1624661 := bbase (se 8 (by rfl) ⟨9519, by rfl⟩ : syracuseStep 1624661 = 19039) (by norm_num)
theorem B1821325 : Blo 718322 1821325 := bbase (se 3 (by rfl) ⟨341498, by rfl⟩ : syracuseStep 1821325 = 682997) (by norm_num)
theorem B1624733 : Blo 718322 1624733 := bbase (se 3 (by rfl) ⟨304637, by rfl⟩ : syracuseStep 1624733 = 609275) (by norm_num)
theorem B1624805 : Blo 718322 1624805 := bbase (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) (by norm_num)
theorem B1821437 : Blo 718322 1821437 := bbase (se 3 (by rfl) ⟨341519, by rfl⟩ : syracuseStep 1821437 = 683039) (by norm_num)
theorem B13814549 : Blo 718322 13814549 := bbase (se 6 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 13814549 = 647557) (by norm_num)
theorem B6146837 : Blo 718322 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B1624877 : Blo 718322 1624877 := bbase (se 3 (by rfl) ⟨304664, by rfl⟩ : syracuseStep 1624877 = 609329) (by norm_num)
theorem B1297205 : Blo 718322 1297205 := bbase (se 5 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 1297205 = 121613) (by norm_num)
theorem B3656501 : Blo 718322 3656501 := bbase (se 5 (by rfl) ⟨171398, by rfl⟩ : syracuseStep 3656501 = 342797) (by norm_num)
theorem B1624949 : Blo 718322 1624949 := bbase (se 5 (by rfl) ⟨76169, by rfl⟩ : syracuseStep 1624949 = 152339) (by norm_num)
theorem B4606901 : Blo 718322 4606901 := bbase (se 5 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 4606901 = 431897) (by norm_num)
theorem B1821629 : Blo 718322 1821629 := bbase (se 3 (by rfl) ⟨341555, by rfl⟩ : syracuseStep 1821629 = 683111) (by norm_num)
theorem B1625021 : Blo 718322 1625021 := bbase (se 3 (by rfl) ⟨304691, by rfl⟩ : syracuseStep 1625021 = 609383) (by norm_num)
theorem B1625093 : Blo 718322 1625093 := bbase (se 4 (by rfl) ⟨152352, by rfl⟩ : syracuseStep 1625093 = 304705) (by norm_num)
theorem B1625165 : Blo 718322 1625165 := bbase (se 3 (by rfl) ⟨304718, by rfl⟩ : syracuseStep 1625165 = 609437) (by norm_num)
theorem B4148309 : Blo 718322 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B1821973 : Blo 718322 1821973 := bbase (se 6 (by rfl) ⟨42702, by rfl⟩ : syracuseStep 1821973 = 85405) (by norm_num)
theorem B1822085 : Blo 718322 1822085 := bbase (se 4 (by rfl) ⟨170820, by rfl⟩ : syracuseStep 1822085 = 341641) (by norm_num)
theorem B1822277 : Blo 718322 1822277 := bbase (se 4 (by rfl) ⟨170838, by rfl⟩ : syracuseStep 1822277 = 341677) (by norm_num)
theorem B1232453 : Blo 718322 1232453 := bbase (se 4 (by rfl) ⟨115542, by rfl⟩ : syracuseStep 1232453 = 231085) (by norm_num)
theorem B2051669 : Blo 718322 2051669 := bbase (se 8 (by rfl) ⟨12021, by rfl⟩ : syracuseStep 2051669 = 24043) (by norm_num)
theorem B1756829 : Blo 718322 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B1363709 : Blo 718322 1363709 := bbase (se 3 (by rfl) ⟨255695, by rfl⟩ : syracuseStep 1363709 = 511391) (by norm_num)
theorem B1363853 : Blo 718322 1363853 := bbase (se 3 (by rfl) ⟨255722, by rfl⟩ : syracuseStep 1363853 = 511445) (by norm_num)
theorem B1822621 : Blo 718322 1822621 := bbase (se 3 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 1822621 = 683483) (by norm_num)
theorem B1822733 : Blo 718322 1822733 := bbase (se 3 (by rfl) ⟨341762, by rfl⟩ : syracuseStep 1822733 = 683525) (by norm_num)
theorem B1364141 : Blo 718322 1364141 := bbase (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) (by norm_num)
theorem B1462469 : Blo 718322 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B1822925 : Blo 718322 1822925 := bbase (se 3 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 1822925 = 683597) (by norm_num)
theorem B1462501 : Blo 718322 1462501 := bbase (se 4 (by rfl) ⟨137109, by rfl⟩ : syracuseStep 1462501 = 274219) (by norm_num)
theorem B2052341 : Blo 718322 2052341 := bbase (se 5 (by rfl) ⟨96203, by rfl⟩ : syracuseStep 2052341 = 192407) (by norm_num)
theorem B12144917 : Blo 718322 12144917 := bbase (se 6 (by rfl) ⟨284646, by rfl⟩ : syracuseStep 12144917 = 569293) (by norm_num)
theorem B1364293 : Blo 718322 1364293 := bbase (se 4 (by rfl) ⟨127902, by rfl⟩ : syracuseStep 1364293 = 255805) (by norm_num)
theorem B2740661 : Blo 718322 2740661 := bbase (se 5 (by rfl) ⟨128468, by rfl⟩ : syracuseStep 2740661 = 256937) (by norm_num)
theorem B1823269 : Blo 718322 1823269 := bbase (se 4 (by rfl) ⟨170931, by rfl⟩ : syracuseStep 1823269 = 341863) (by norm_num)
theorem B1561141 : Blo 718322 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B1364597 : Blo 718322 1364597 := bbase (se 5 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 1364597 = 127931) (by norm_num)
theorem B1823381 : Blo 718322 1823381 := bbase (se 6 (by rfl) ⟨42735, by rfl⟩ : syracuseStep 1823381 = 85471) (by norm_num)
theorem B2052773 : Blo 718322 2052773 := bbase (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) (by norm_num)
theorem B1036973 : Blo 718322 1036973 := bbase (se 3 (by rfl) ⟨194432, by rfl⟩ : syracuseStep 1036973 = 388865) (by norm_num)
theorem B2740949 : Blo 718322 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B1299245 : Blo 718322 1299245 := bbase (se 3 (by rfl) ⟨243608, by rfl⟩ : syracuseStep 1299245 = 487217) (by norm_num)
theorem B1823573 : Blo 718322 1823573 := bbase (se 9 (by rfl) ⟨5342, by rfl⟩ : syracuseStep 1823573 = 10685) (by norm_num)
theorem B3069029 : Blo 718322 3069029 := bbase (se 4 (by rfl) ⟨287721, by rfl⟩ : syracuseStep 3069029 = 575443) (by norm_num)
theorem B1823917 : Blo 718322 1823917 := bbase (se 3 (by rfl) ⟨341984, by rfl⟩ : syracuseStep 1823917 = 683969) (by norm_num)
theorem B808141 : Blo 718322 808141 := bbase (se 3 (by rfl) ⟨151526, by rfl⟩ : syracuseStep 808141 = 303053) (by norm_num)
theorem B808177 : Blo 718322 808177 := bbase (se 2 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 808177 = 606133) (by norm_num)
theorem B6935797 : Blo 718322 6935797 := bbase (se 5 (by rfl) ⟨325115, by rfl⟩ : syracuseStep 6935797 = 650231) (by norm_num)
theorem B808213 : Blo 718322 808213 := bbase (se 6 (by rfl) ⟨18942, by rfl⟩ : syracuseStep 808213 = 37885) (by norm_num)
theorem B1824029 : Blo 718322 1824029 := bbase (se 3 (by rfl) ⟨342005, by rfl⟩ : syracuseStep 1824029 = 684011) (by norm_num)
theorem B1463597 : Blo 718322 1463597 := bbase (se 3 (by rfl) ⟨274424, by rfl⟩ : syracuseStep 1463597 = 548849) (by norm_num)
theorem B808249 : Blo 718322 808249 := bbase (se 2 (by rfl) ⟨303093, by rfl⟩ : syracuseStep 808249 = 606187) (by norm_num)
theorem B808285 : Blo 718322 808285 := bbase (se 3 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 808285 = 303107) (by norm_num)
theorem B1365349 : Blo 718322 1365349 := bbase (se 4 (by rfl) ⟨128001, by rfl⟩ : syracuseStep 1365349 = 256003) (by norm_num)
theorem B3462517 : Blo 718322 3462517 := bbase (se 5 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 3462517 = 324611) (by norm_num)
theorem B808321 : Blo 718322 808321 := bbase (se 2 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 808321 = 606241) (by norm_num)
theorem B2053525 : Blo 718322 2053525 := bbase (se 6 (by rfl) ⟨48129, by rfl⟩ : syracuseStep 2053525 = 96259) (by norm_num)
theorem B808357 : Blo 718322 808357 := bbase (se 4 (by rfl) ⟨75783, by rfl⟩ : syracuseStep 808357 = 151567) (by norm_num)
theorem B808393 : Blo 718322 808393 := bbase (se 2 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 808393 = 606295) (by norm_num)
theorem B1824221 : Blo 718322 1824221 := bbase (se 3 (by rfl) ⟨342041, by rfl⟩ : syracuseStep 1824221 = 684083) (by norm_num)
theorem B808429 : Blo 718322 808429 := bbase (se 3 (by rfl) ⟨151580, by rfl⟩ : syracuseStep 808429 = 303161) (by norm_num)
theorem B1365493 : Blo 718322 1365493 := bbase (se 5 (by rfl) ⟨64007, by rfl⟩ : syracuseStep 1365493 = 128015) (by norm_num)
theorem B808465 : Blo 718322 808465 := bbase (se 2 (by rfl) ⟨303174, by rfl⟩ : syracuseStep 808465 = 606349) (by norm_num)
theorem B808501 : Blo 718322 808501 := bbase (se 5 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 808501 = 75797) (by norm_num)
theorem B808537 : Blo 718322 808537 := bbase (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) (by norm_num)
theorem B808573 : Blo 718322 808573 := bbase (se 3 (by rfl) ⟨151607, by rfl⟩ : syracuseStep 808573 = 303215) (by norm_num)
theorem B1365653 : Blo 718322 1365653 := bbase (se 6 (by rfl) ⟨32007, by rfl⟩ : syracuseStep 1365653 = 64015) (by norm_num)
theorem B808609 : Blo 718322 808609 := bbase (se 2 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 808609 = 606457) (by norm_num)
theorem B808645 : Blo 718322 808645 := bbase (se 4 (by rfl) ⟨75810, by rfl⟩ : syracuseStep 808645 = 151621) (by norm_num)
theorem B1038037 : Blo 718322 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B808681 : Blo 718322 808681 := bbase (se 2 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 808681 = 606511) (by norm_num)
theorem B808717 : Blo 718322 808717 := bbase (se 3 (by rfl) ⟨151634, by rfl⟩ : syracuseStep 808717 = 303269) (by norm_num)
theorem B1365797 : Blo 718322 1365797 := bbase (se 4 (by rfl) ⟨128043, by rfl⟩ : syracuseStep 1365797 = 256087) (by norm_num)
theorem B808753 : Blo 718322 808753 := bbase (se 2 (by rfl) ⟨303282, by rfl⟩ : syracuseStep 808753 = 606565) (by norm_num)
theorem B1824565 : Blo 718322 1824565 := bbase (se 5 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 1824565 = 171053) (by norm_num)
theorem B808789 : Blo 718322 808789 := bbase (se 9 (by rfl) ⟨2369, by rfl⟩ : syracuseStep 808789 = 4739) (by norm_num)
theorem B2742133 : Blo 718322 2742133 := bbase (se 5 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 2742133 = 257075) (by norm_num)
theorem B808825 : Blo 718322 808825 := bbase (se 2 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 808825 = 606619) (by norm_num)
theorem B808861 : Blo 718322 808861 := bbase (se 3 (by rfl) ⟨151661, by rfl⟩ : syracuseStep 808861 = 303323) (by norm_num)
theorem B1824677 : Blo 718322 1824677 := bbase (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) (by norm_num)
theorem B808897 : Blo 718322 808897 := bbase (se 2 (by rfl) ⟨303336, by rfl⟩ : syracuseStep 808897 = 606673) (by norm_num)
theorem B2807765 : Blo 718322 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B808933 : Blo 718322 808933 := bbase (se 4 (by rfl) ⟨75837, by rfl⟩ : syracuseStep 808933 = 151675) (by norm_num)
theorem B808969 : Blo 718322 808969 := bbase (se 2 (by rfl) ⟨303363, by rfl⟩ : syracuseStep 808969 = 606727) (by norm_num)
theorem B809005 : Blo 718322 809005 := bbase (se 3 (by rfl) ⟨151688, by rfl⟩ : syracuseStep 809005 = 303377) (by norm_num)
theorem B1366085 : Blo 718322 1366085 := bbase (se 4 (by rfl) ⟨128070, by rfl⟩ : syracuseStep 1366085 = 256141) (by norm_num)
theorem B809041 : Blo 718322 809041 := bbase (se 2 (by rfl) ⟨303390, by rfl⟩ : syracuseStep 809041 = 606781) (by norm_num)
theorem B1824869 : Blo 718322 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B809077 : Blo 718322 809077 := bbase (se 5 (by rfl) ⟨37925, by rfl⟩ : syracuseStep 809077 = 75851) (by norm_num)
theorem B809113 : Blo 718322 809113 := bbase (se 2 (by rfl) ⟨303417, by rfl⟩ : syracuseStep 809113 = 606835) (by norm_num)
theorem B2742437 : Blo 718322 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B809149 : Blo 718322 809149 := bbase (se 3 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 809149 = 303431) (by norm_num)
theorem B1300693 : Blo 718322 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B1366237 : Blo 718322 1366237 := bbase (se 3 (by rfl) ⟨256169, by rfl⟩ : syracuseStep 1366237 = 512339) (by norm_num)
theorem B809185 : Blo 718322 809185 := bbase (se 2 (by rfl) ⟨303444, by rfl⟩ : syracuseStep 809185 = 606889) (by norm_num)
theorem B809221 : Blo 718322 809221 := bbase (se 4 (by rfl) ⟨75864, by rfl⟩ : syracuseStep 809221 = 151729) (by norm_num)
theorem B809257 : Blo 718322 809257 := bbase (se 2 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 809257 = 606943) (by norm_num)
theorem B1562941 : Blo 718322 1562941 := bbase (se 3 (by rfl) ⟨293051, by rfl⟩ : syracuseStep 1562941 = 586103) (by norm_num)
theorem B809293 : Blo 718322 809293 := bbase (se 3 (by rfl) ⟨151742, by rfl⟩ : syracuseStep 809293 = 303485) (by norm_num)
theorem B973141 : Blo 718322 973141 := bbase (se 10 (by rfl) ⟨1425, by rfl⟩ : syracuseStep 973141 = 2851) (by norm_num)
theorem B809329 : Blo 718322 809329 := bbase (se 2 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 809329 = 606997) (by norm_num)
theorem B809365 : Blo 718322 809365 := bbase (se 6 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 809365 = 37939) (by norm_num)
theorem B809401 : Blo 718322 809401 := bbase (se 2 (by rfl) ⟨303525, by rfl⟩ : syracuseStep 809401 = 607051) (by norm_num)
theorem B1825213 : Blo 718322 1825213 := bbase (se 3 (by rfl) ⟨342227, by rfl⟩ : syracuseStep 1825213 = 684455) (by norm_num)
theorem B6904277 : Blo 718322 6904277 := bbase (se 7 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 6904277 = 161819) (by norm_num)
theorem B809437 : Blo 718322 809437 := bbase (se 3 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 809437 = 303539) (by norm_num)
theorem B3955189 : Blo 718322 3955189 := bbase (se 5 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 3955189 = 370799) (by norm_num)
theorem B809473 : Blo 718322 809473 := bbase (se 2 (by rfl) ⟨303552, by rfl⟩ : syracuseStep 809473 = 607105) (by norm_num)
theorem B1366541 : Blo 718322 1366541 := bbase (se 3 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 1366541 = 512453) (by norm_num)
theorem B809509 : Blo 718322 809509 := bbase (se 4 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 809509 = 151783) (by norm_num)
theorem B1825325 : Blo 718322 1825325 := bbase (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) (by norm_num)
theorem B809545 : Blo 718322 809545 := bbase (se 2 (by rfl) ⟨303579, by rfl⟩ : syracuseStep 809545 = 607159) (by norm_num)
theorem B809581 : Blo 718322 809581 := bbase (se 3 (by rfl) ⟨151796, by rfl⟩ : syracuseStep 809581 = 303593) (by norm_num)
theorem B809617 : Blo 718322 809617 := bbase (se 2 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 809617 = 607213) (by norm_num)
theorem B809653 : Blo 718322 809653 := bbase (se 5 (by rfl) ⟨37952, by rfl⟩ : syracuseStep 809653 = 75905) (by norm_num)
theorem B809689 : Blo 718322 809689 := bbase (se 2 (by rfl) ⟨303633, by rfl⟩ : syracuseStep 809689 = 607267) (by norm_num)
theorem B1825517 : Blo 718322 1825517 := bbase (se 3 (by rfl) ⟨342284, by rfl⟩ : syracuseStep 1825517 = 684569) (by norm_num)
theorem B809725 : Blo 718322 809725 := bbase (se 3 (by rfl) ⟨151823, by rfl⟩ : syracuseStep 809725 = 303647) (by norm_num)
theorem B1727261 : Blo 718322 1727261 := bbase (se 3 (by rfl) ⟨323861, by rfl⟩ : syracuseStep 1727261 = 647723) (by norm_num)
theorem B809761 : Blo 718322 809761 := bbase (se 2 (by rfl) ⟨303660, by rfl⟩ : syracuseStep 809761 = 607321) (by norm_num)
theorem B809797 : Blo 718322 809797 := bbase (se 4 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 809797 = 151837) (by norm_num)
theorem B809833 : Blo 718322 809833 := bbase (se 2 (by rfl) ⟨303687, by rfl⟩ : syracuseStep 809833 = 607375) (by norm_num)
theorem B809869 : Blo 718322 809869 := bbase (se 3 (by rfl) ⟨151850, by rfl⟩ : syracuseStep 809869 = 303701) (by norm_num)
theorem B809905 : Blo 718322 809905 := bbase (se 2 (by rfl) ⟨303714, by rfl⟩ : syracuseStep 809905 = 607429) (by norm_num)
theorem B809941 : Blo 718322 809941 := bbase (se 7 (by rfl) ⟨9491, by rfl⟩ : syracuseStep 809941 = 18983) (by norm_num)
theorem B1727453 : Blo 718322 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B809977 : Blo 718322 809977 := bbase (se 2 (by rfl) ⟨303741, by rfl⟩ : syracuseStep 809977 = 607483) (by norm_num)
theorem B1301501 : Blo 718322 1301501 := bbase (se 3 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 1301501 = 488063) (by norm_num)
theorem B810013 : Blo 718322 810013 := bbase (se 3 (by rfl) ⟨151877, by rfl⟩ : syracuseStep 810013 = 303755) (by norm_num)
theorem B810049 : Blo 718322 810049 := bbase (se 2 (by rfl) ⟨303768, by rfl⟩ : syracuseStep 810049 = 607537) (by norm_num)
theorem B1825861 : Blo 718322 1825861 := bbase (se 4 (by rfl) ⟨171174, by rfl⟩ : syracuseStep 1825861 = 342349) (by norm_num)
theorem B1301573 : Blo 718322 1301573 := bbase (se 4 (by rfl) ⟨122022, by rfl⟩ : syracuseStep 1301573 = 244045) (by norm_num)
theorem B5463125 : Blo 718322 5463125 := bbase (se 8 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 5463125 = 64021) (by norm_num)
theorem B810085 : Blo 718322 810085 := bbase (se 4 (by rfl) ⟨75945, by rfl⟩ : syracuseStep 810085 = 151891) (by norm_num)
theorem B810121 : Blo 718322 810121 := bbase (se 2 (by rfl) ⟨303795, by rfl⟩ : syracuseStep 810121 = 607591) (by norm_num)
theorem B810157 : Blo 718322 810157 := bbase (se 3 (by rfl) ⟨151904, by rfl⟩ : syracuseStep 810157 = 303809) (by norm_num)
theorem B1825973 : Blo 718322 1825973 := bbase (se 5 (by rfl) ⟨85592, by rfl⟩ : syracuseStep 1825973 = 171185) (by norm_num)
theorem B810193 : Blo 718322 810193 := bbase (se 2 (by rfl) ⟨303822, by rfl⟩ : syracuseStep 810193 = 607645) (by norm_num)
theorem B810229 : Blo 718322 810229 := bbase (se 5 (by rfl) ⟨37979, by rfl⟩ : syracuseStep 810229 = 75959) (by norm_num)
theorem B1367293 : Blo 718322 1367293 := bbase (se 3 (by rfl) ⟨256367, by rfl⟩ : syracuseStep 1367293 = 512735) (by norm_num)
theorem B8215829 : Blo 718322 8215829 := bbase (se 6 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 8215829 = 385117) (by norm_num)
theorem B810265 : Blo 718322 810265 := bbase (se 2 (by rfl) ⟨303849, by rfl⟩ : syracuseStep 810265 = 607699) (by norm_num)
theorem B810301 : Blo 718322 810301 := bbase (se 3 (by rfl) ⟨151931, by rfl⟩ : syracuseStep 810301 = 303863) (by norm_num)
theorem B810337 : Blo 718322 810337 := bbase (se 2 (by rfl) ⟨303876, by rfl⟩ : syracuseStep 810337 = 607753) (by norm_num)
theorem B3169637 : Blo 718322 3169637 := bbase (se 4 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 3169637 = 594307) (by norm_num)
theorem B1826165 : Blo 718322 1826165 := bbase (se 5 (by rfl) ⟨85601, by rfl⟩ : syracuseStep 1826165 = 171203) (by norm_num)
theorem B810373 : Blo 718322 810373 := bbase (se 4 (by rfl) ⟨75972, by rfl⟩ : syracuseStep 810373 = 151945) (by norm_num)
theorem B1367437 : Blo 718322 1367437 := bbase (se 3 (by rfl) ⟨256394, by rfl⟩ : syracuseStep 1367437 = 512789) (by norm_num)
theorem B810409 : Blo 718322 810409 := bbase (se 2 (by rfl) ⟨303903, by rfl⟩ : syracuseStep 810409 = 607807) (by norm_num)
theorem B810445 : Blo 718322 810445 := bbase (se 3 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 810445 = 303917) (by norm_num)
theorem B810481 : Blo 718322 810481 := bbase (se 2 (by rfl) ⟨303930, by rfl⟩ : syracuseStep 810481 = 607861) (by norm_num)
theorem B810517 : Blo 718322 810517 := bbase (se 6 (by rfl) ⟨18996, by rfl⟩ : syracuseStep 810517 = 37993) (by norm_num)
theorem B1367597 : Blo 718322 1367597 := bbase (se 3 (by rfl) ⟨256424, by rfl⟩ : syracuseStep 1367597 = 512849) (by norm_num)
theorem B810553 : Blo 718322 810553 := bbase (se 2 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 810553 = 607915) (by norm_num)
theorem B810589 : Blo 718322 810589 := bbase (se 3 (by rfl) ⟨151985, by rfl⟩ : syracuseStep 810589 = 303971) (by norm_num)
theorem B810625 : Blo 718322 810625 := bbase (se 2 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 810625 = 607969) (by norm_num)
theorem B810661 : Blo 718322 810661 := bbase (se 4 (by rfl) ⟨75999, by rfl⟩ : syracuseStep 810661 = 151999) (by norm_num)
theorem B1040045 : Blo 718322 1040045 := bbase (se 3 (by rfl) ⟨195008, by rfl⟩ : syracuseStep 1040045 = 390017) (by norm_num)
theorem B1367741 : Blo 718322 1367741 := bbase (se 3 (by rfl) ⟨256451, by rfl⟩ : syracuseStep 1367741 = 512903) (by norm_num)
theorem B974525 : Blo 718322 974525 := bbase (se 3 (by rfl) ⟨182723, by rfl⟩ : syracuseStep 974525 = 365447) (by norm_num)
theorem B810697 : Blo 718322 810697 := bbase (se 2 (by rfl) ⟨304011, by rfl⟩ : syracuseStep 810697 = 608023) (by norm_num)
theorem B1826509 : Blo 718322 1826509 := bbase (se 3 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 1826509 = 684941) (by norm_num)
theorem B810733 : Blo 718322 810733 := bbase (se 3 (by rfl) ⟨152012, by rfl⟩ : syracuseStep 810733 = 304025) (by norm_num)
theorem B810769 : Blo 718322 810769 := bbase (se 2 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 810769 = 608077) (by norm_num)
theorem B810805 : Blo 718322 810805 := bbase (se 5 (by rfl) ⟨38006, by rfl⟩ : syracuseStep 810805 = 76013) (by norm_num)
theorem B1826621 : Blo 718322 1826621 := bbase (se 3 (by rfl) ⟨342491, by rfl⟩ : syracuseStep 1826621 = 684983) (by norm_num)
theorem B810841 : Blo 718322 810841 := bbase (se 2 (by rfl) ⟨304065, by rfl⟩ : syracuseStep 810841 = 608131) (by norm_num)
theorem B810877 : Blo 718322 810877 := bbase (se 3 (by rfl) ⟨152039, by rfl⟩ : syracuseStep 810877 = 304079) (by norm_num)
theorem B810913 : Blo 718322 810913 := bbase (se 2 (by rfl) ⟨304092, by rfl⟩ : syracuseStep 810913 = 608185) (by norm_num)
theorem B909245 : Blo 718322 909245 := bbase (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) (by norm_num)
theorem B810949 : Blo 718322 810949 := bbase (se 4 (by rfl) ⟨76026, by rfl⟩ : syracuseStep 810949 = 152053) (by norm_num)
theorem B1368029 : Blo 718322 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B810985 : Blo 718322 810985 := bbase (se 2 (by rfl) ⟨304119, by rfl⟩ : syracuseStep 810985 = 608239) (by norm_num)
theorem B909301 : Blo 718322 909301 := bbase (se 5 (by rfl) ⟨42623, by rfl⟩ : syracuseStep 909301 = 85247) (by norm_num)
theorem B1826813 : Blo 718322 1826813 := bbase (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) (by norm_num)
theorem B811021 : Blo 718322 811021 := bbase (se 3 (by rfl) ⟨152066, by rfl⟩ : syracuseStep 811021 = 304133) (by norm_num)
theorem B811057 : Blo 718322 811057 := bbase (se 2 (by rfl) ⟨304146, by rfl⟩ : syracuseStep 811057 = 608293) (by norm_num)
theorem B909397 : Blo 718322 909397 := bbase (se 8 (by rfl) ⟨5328, by rfl⟩ : syracuseStep 909397 = 10657) (by norm_num)
theorem B811093 : Blo 718322 811093 := bbase (se 8 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 811093 = 9505) (by norm_num)
theorem B1368181 : Blo 718322 1368181 := bbase (se 5 (by rfl) ⟨64133, by rfl⟩ : syracuseStep 1368181 = 128267) (by norm_num)
theorem B811129 : Blo 718322 811129 := bbase (se 2 (by rfl) ⟨304173, by rfl⟩ : syracuseStep 811129 = 608347) (by norm_num)
theorem B876701 : Blo 718322 876701 := bbase (se 3 (by rfl) ⟨164381, by rfl⟩ : syracuseStep 876701 = 328763) (by norm_num)
theorem B811165 : Blo 718322 811165 := bbase (se 3 (by rfl) ⟨152093, by rfl⟩ : syracuseStep 811165 = 304187) (by norm_num)
theorem B2056373 : Blo 718322 2056373 := bbase (se 5 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 2056373 = 192785) (by norm_num)
theorem B811201 : Blo 718322 811201 := bbase (se 2 (by rfl) ⟨304200, by rfl⟩ : syracuseStep 811201 = 608401) (by norm_num)
theorem B811237 : Blo 718322 811237 := bbase (se 4 (by rfl) ⟨76053, by rfl⟩ : syracuseStep 811237 = 152107) (by norm_num)
theorem B909569 : Blo 718322 909569 := bbase (se 2 (by rfl) ⟨341088, by rfl⟩ : syracuseStep 909569 = 682177) (by norm_num)
theorem B811273 : Blo 718322 811273 := bbase (se 2 (by rfl) ⟨304227, by rfl⟩ : syracuseStep 811273 = 608455) (by norm_num)
theorem B811309 : Blo 718322 811309 := bbase (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) (by norm_num)
theorem B909625 : Blo 718322 909625 := bbase (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) (by norm_num)
theorem B3072325 : Blo 718322 3072325 := bbase (se 4 (by rfl) ⟨288030, by rfl⟩ : syracuseStep 3072325 = 576061) (by norm_num)
theorem B811345 : Blo 718322 811345 := bbase (se 2 (by rfl) ⟨304254, by rfl⟩ : syracuseStep 811345 = 608509) (by norm_num)
theorem B1827157 : Blo 718322 1827157 := bbase (se 10 (by rfl) ⟨2676, by rfl⟩ : syracuseStep 1827157 = 5353) (by norm_num)
theorem B811381 : Blo 718322 811381 := bbase (se 5 (by rfl) ⟨38033, by rfl⟩ : syracuseStep 811381 = 76067) (by norm_num)
theorem B909721 : Blo 718322 909721 := bbase (se 2 (by rfl) ⟨341145, by rfl⟩ : syracuseStep 909721 = 682291) (by norm_num)
theorem B811417 : Blo 718322 811417 := bbase (se 2 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 811417 = 608563) (by norm_num)
theorem B1368485 : Blo 718322 1368485 := bbase (se 4 (by rfl) ⟨128295, by rfl⟩ : syracuseStep 1368485 = 256591) (by norm_num)
theorem B811453 : Blo 718322 811453 := bbase (se 3 (by rfl) ⟨152147, by rfl⟩ : syracuseStep 811453 = 304295) (by norm_num)
theorem B1827269 : Blo 718322 1827269 := bbase (se 4 (by rfl) ⟨171306, by rfl⟩ : syracuseStep 1827269 = 342613) (by norm_num)
theorem B4612565 : Blo 718322 4612565 := bbase (se 7 (by rfl) ⟨54053, by rfl⟩ : syracuseStep 4612565 = 108107) (by norm_num)
theorem B811489 : Blo 718322 811489 := bbase (se 2 (by rfl) ⟨304308, by rfl⟩ : syracuseStep 811489 = 608617) (by norm_num)
theorem B1729021 : Blo 718322 1729021 := bbase (se 3 (by rfl) ⟨324191, by rfl⟩ : syracuseStep 1729021 = 648383) (by norm_num)
theorem B811525 : Blo 718322 811525 := bbase (se 4 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 811525 = 152161) (by norm_num)
theorem B811561 : Blo 718322 811561 := bbase (se 2 (by rfl) ⟨304335, by rfl⟩ : syracuseStep 811561 = 608671) (by norm_num)
theorem B909893 : Blo 718322 909893 := bbase (se 4 (by rfl) ⟨85302, by rfl⟩ : syracuseStep 909893 = 170605) (by norm_num)
theorem B811597 : Blo 718322 811597 := bbase (se 3 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 811597 = 304349) (by norm_num)
theorem B811633 : Blo 718322 811633 := bbase (se 2 (by rfl) ⟨304362, by rfl⟩ : syracuseStep 811633 = 608725) (by norm_num)
theorem B909949 : Blo 718322 909949 := bbase (se 3 (by rfl) ⟨170615, by rfl⟩ : syracuseStep 909949 = 341231) (by norm_num)
theorem B1827461 : Blo 718322 1827461 := bbase (se 4 (by rfl) ⟨171324, by rfl⟩ : syracuseStep 1827461 = 342649) (by norm_num)
theorem B811669 : Blo 718322 811669 := bbase (se 6 (by rfl) ⟨19023, by rfl⟩ : syracuseStep 811669 = 38047) (by norm_num)
theorem B811705 : Blo 718322 811705 := bbase (se 2 (by rfl) ⟨304389, by rfl⟩ : syracuseStep 811705 = 608779) (by norm_num)
theorem B910045 : Blo 718322 910045 := bbase (se 3 (by rfl) ⟨170633, by rfl⟩ : syracuseStep 910045 = 341267) (by norm_num)
theorem B811741 : Blo 718322 811741 := bbase (se 3 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 811741 = 304403) (by norm_num)
theorem B811777 : Blo 718322 811777 := bbase (se 2 (by rfl) ⟨304416, by rfl⟩ : syracuseStep 811777 = 608833) (by norm_num)
theorem B811813 : Blo 718322 811813 := bbase (se 4 (by rfl) ⟨76107, by rfl⟩ : syracuseStep 811813 = 152215) (by norm_num)
theorem B811849 : Blo 718322 811849 := bbase (se 2 (by rfl) ⟨304443, by rfl⟩ : syracuseStep 811849 = 608887) (by norm_num)
theorem B811885 : Blo 718322 811885 := bbase (se 3 (by rfl) ⟨152228, by rfl⟩ : syracuseStep 811885 = 304457) (by norm_num)
theorem B910217 : Blo 718322 910217 := bbase (se 2 (by rfl) ⟨341331, by rfl⟩ : syracuseStep 910217 = 682663) (by norm_num)
theorem B811921 : Blo 718322 811921 := bbase (se 2 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 811921 = 608941) (by norm_num)
theorem B811957 : Blo 718322 811957 := bbase (se 5 (by rfl) ⟨38060, by rfl⟩ : syracuseStep 811957 = 76121) (by norm_num)
theorem B910273 : Blo 718322 910273 := bbase (se 2 (by rfl) ⟨341352, by rfl⟩ : syracuseStep 910273 = 682705) (by norm_num)
theorem B811993 : Blo 718322 811993 := bbase (se 2 (by rfl) ⟨304497, by rfl⟩ : syracuseStep 811993 = 608995) (by norm_num)
theorem B1827805 : Blo 718322 1827805 := bbase (se 3 (by rfl) ⟨342713, by rfl⟩ : syracuseStep 1827805 = 685427) (by norm_num)
theorem B812029 : Blo 718322 812029 := bbase (se 3 (by rfl) ⟨152255, by rfl⟩ : syracuseStep 812029 = 304511) (by norm_num)
theorem B910369 : Blo 718322 910369 := bbase (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) (by norm_num)
theorem B812065 : Blo 718322 812065 := bbase (se 2 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 812065 = 609049) (by norm_num)
theorem B812101 : Blo 718322 812101 := bbase (se 4 (by rfl) ⟨76134, by rfl⟩ : syracuseStep 812101 = 152269) (by norm_num)
theorem B1827917 : Blo 718322 1827917 := bbase (se 3 (by rfl) ⟨342734, by rfl⟩ : syracuseStep 1827917 = 685469) (by norm_num)
theorem B1729637 : Blo 718322 1729637 := bbase (se 4 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 1729637 = 324307) (by norm_num)
theorem B812137 : Blo 718322 812137 := bbase (se 2 (by rfl) ⟨304551, by rfl⟩ : syracuseStep 812137 = 609103) (by norm_num)
theorem B812173 : Blo 718322 812173 := bbase (se 3 (by rfl) ⟨152282, by rfl⟩ : syracuseStep 812173 = 304565) (by norm_num)
theorem B1369237 : Blo 718322 1369237 := bbase (se 6 (by rfl) ⟨32091, by rfl⟩ : syracuseStep 1369237 = 64183) (by norm_num)
theorem B812209 : Blo 718322 812209 := bbase (se 2 (by rfl) ⟨304578, by rfl⟩ : syracuseStep 812209 = 609157) (by norm_num)
theorem B910541 : Blo 718322 910541 := bbase (se 3 (by rfl) ⟨170726, by rfl⟩ : syracuseStep 910541 = 341453) (by norm_num)
theorem B812245 : Blo 718322 812245 := bbase (se 7 (by rfl) ⟨9518, by rfl⟩ : syracuseStep 812245 = 19037) (by norm_num)
theorem B812281 : Blo 718322 812281 := bbase (se 2 (by rfl) ⟨304605, by rfl⟩ : syracuseStep 812281 = 609211) (by norm_num)
theorem B910597 : Blo 718322 910597 := bbase (se 4 (by rfl) ⟨85368, by rfl⟩ : syracuseStep 910597 = 170737) (by norm_num)
theorem B1828109 : Blo 718322 1828109 := bbase (se 3 (by rfl) ⟨342770, by rfl⟩ : syracuseStep 1828109 = 685541) (by norm_num)
theorem B779549 : Blo 718322 779549 := bbase (se 3 (by rfl) ⟨146165, by rfl⟩ : syracuseStep 779549 = 292331) (by norm_num)
theorem B812317 : Blo 718322 812317 := bbase (se 3 (by rfl) ⟨152309, by rfl⟩ : syracuseStep 812317 = 304619) (by norm_num)
theorem B1369381 : Blo 718322 1369381 := bbase (se 4 (by rfl) ⟨128379, by rfl⟩ : syracuseStep 1369381 = 256759) (by norm_num)
theorem B812353 : Blo 718322 812353 := bbase (se 2 (by rfl) ⟨304632, by rfl⟩ : syracuseStep 812353 = 609265) (by norm_num)
theorem B910693 : Blo 718322 910693 := bbase (se 4 (by rfl) ⟨85377, by rfl⟩ : syracuseStep 910693 = 170755) (by norm_num)
theorem B812389 : Blo 718322 812389 := bbase (se 4 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 812389 = 152323) (by norm_num)
theorem B812425 : Blo 718322 812425 := bbase (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) (by norm_num)
theorem B812461 : Blo 718322 812461 := bbase (se 3 (by rfl) ⟨152336, by rfl⟩ : syracuseStep 812461 = 304673) (by norm_num)
theorem B1369541 : Blo 718322 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B812497 : Blo 718322 812497 := bbase (se 2 (by rfl) ⟨304686, by rfl⟩ : syracuseStep 812497 = 609373) (by norm_num)
theorem B812533 : Blo 718322 812533 := bbase (se 5 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 812533 = 76175) (by norm_num)
theorem B1664509 : Blo 718322 1664509 := bbase (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) (by norm_num)
theorem B910865 : Blo 718322 910865 := bbase (se 2 (by rfl) ⟨341574, by rfl⟩ : syracuseStep 910865 = 683149) (by norm_num)
theorem B812569 : Blo 718322 812569 := bbase (se 2 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 812569 = 609427) (by norm_num)
theorem B812605 : Blo 718322 812605 := bbase (se 3 (by rfl) ⟨152363, by rfl⟩ : syracuseStep 812605 = 304727) (by norm_num)
theorem B910921 : Blo 718322 910921 := bbase (se 2 (by rfl) ⟨341595, by rfl⟩ : syracuseStep 910921 = 683191) (by norm_num)
theorem B1369685 : Blo 718322 1369685 := bbase (se 8 (by rfl) ⟨8025, by rfl⟩ : syracuseStep 1369685 = 16051) (by norm_num)
theorem B3466901 : Blo 718322 3466901 := bbase (se 6 (by rfl) ⟨81255, by rfl⟩ : syracuseStep 3466901 = 162511) (by norm_num)
theorem B911017 : Blo 718322 911017 := bbase (se 2 (by rfl) ⟨341631, by rfl⟩ : syracuseStep 911017 = 683263) (by norm_num)
theorem B911189 : Blo 718322 911189 := bbase (se 9 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 911189 = 5339) (by norm_num)
theorem B1730413 : Blo 718322 1730413 := bbase (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) (by norm_num)
theorem B1369973 : Blo 718322 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B911245 : Blo 718322 911245 := bbase (se 3 (by rfl) ⟨170858, by rfl⟩ : syracuseStep 911245 = 341717) (by norm_num)
theorem B911341 : Blo 718322 911341 := bbase (se 3 (by rfl) ⟨170876, by rfl⟩ : syracuseStep 911341 = 341753) (by norm_num)
theorem B3893237 : Blo 718322 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B1370125 : Blo 718322 1370125 := bbase (se 3 (by rfl) ⟨256898, by rfl⟩ : syracuseStep 1370125 = 513797) (by norm_num)
theorem B911513 : Blo 718322 911513 := bbase (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) (by norm_num)
theorem B911569 : Blo 718322 911569 := bbase (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) (by norm_num)
theorem B878801 : Blo 718322 878801 := bbase (se 2 (by rfl) ⟨329550, by rfl⟩ : syracuseStep 878801 = 659101) (by norm_num)
theorem B911665 : Blo 718322 911665 := bbase (se 2 (by rfl) ⟨341874, by rfl⟩ : syracuseStep 911665 = 683749) (by norm_num)
theorem B1370429 : Blo 718322 1370429 := bbase (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) (by norm_num)
theorem B911837 : Blo 718322 911837 := bbase (se 3 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 911837 = 341939) (by norm_num)
theorem B911893 : Blo 718322 911893 := bbase (se 6 (by rfl) ⟨21372, by rfl⟩ : syracuseStep 911893 = 42745) (by norm_num)
theorem B1731125 : Blo 718322 1731125 := bbase (se 5 (by rfl) ⟨81146, by rfl⟩ : syracuseStep 1731125 = 162293) (by norm_num)
theorem B911989 : Blo 718322 911989 := bbase (se 5 (by rfl) ⟨42749, by rfl⟩ : syracuseStep 911989 = 85499) (by norm_num)
theorem B1108661 : Blo 718322 1108661 := bbase (se 5 (by rfl) ⟨51968, by rfl⟩ : syracuseStep 1108661 = 103937) (by norm_num)
theorem B912161 : Blo 718322 912161 := bbase (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) (by norm_num)
theorem B912217 : Blo 718322 912217 := bbase (se 2 (by rfl) ⟨342081, by rfl⟩ : syracuseStep 912217 = 684163) (by norm_num)
theorem B912313 : Blo 718322 912313 := bbase (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) (by norm_num)
theorem B1534925 : Blo 718322 1534925 := bbase (se 3 (by rfl) ⟨287798, by rfl⟩ : syracuseStep 1534925 = 575597) (by norm_num)
theorem B1371181 : Blo 718322 1371181 := bbase (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) (by norm_num)
theorem B1535069 : Blo 718322 1535069 := bbase (se 3 (by rfl) ⟨287825, by rfl⟩ : syracuseStep 1535069 = 575651) (by norm_num)
theorem B912485 : Blo 718322 912485 := bbase (se 4 (by rfl) ⟨85545, by rfl⟩ : syracuseStep 912485 = 171091) (by norm_num)
theorem B912541 : Blo 718322 912541 := bbase (se 3 (by rfl) ⟨171101, by rfl⟩ : syracuseStep 912541 = 342203) (by norm_num)
theorem B1731797 : Blo 718322 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B3075317 : Blo 718322 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B912637 : Blo 718322 912637 := bbase (se 3 (by rfl) ⟨171119, by rfl⟩ : syracuseStep 912637 = 342239) (by norm_num)
theorem B912809 : Blo 718322 912809 := bbase (se 2 (by rfl) ⟨342303, by rfl⟩ : syracuseStep 912809 = 684607) (by norm_num)
theorem B1535429 : Blo 718322 1535429 := bbase (se 4 (by rfl) ⟨143946, by rfl⟩ : syracuseStep 1535429 = 287893) (by norm_num)
theorem B912865 : Blo 718322 912865 := bbase (se 2 (by rfl) ⟨342324, by rfl⟩ : syracuseStep 912865 = 684649) (by norm_num)
theorem B912961 : Blo 718322 912961 := bbase (se 2 (by rfl) ⟨342360, by rfl⟩ : syracuseStep 912961 = 684721) (by norm_num)
theorem B913133 : Blo 718322 913133 := bbase (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) (by norm_num)
theorem B913189 : Blo 718322 913189 := bbase (se 4 (by rfl) ⟨85611, by rfl⟩ : syracuseStep 913189 = 171223) (by norm_num)
theorem B913285 : Blo 718322 913285 := bbase (se 4 (by rfl) ⟨85620, by rfl⟩ : syracuseStep 913285 = 171241) (by norm_num)
theorem B913457 : Blo 718322 913457 := bbase (se 2 (by rfl) ⟨342546, by rfl⟩ : syracuseStep 913457 = 685093) (by norm_num)
theorem B913513 : Blo 718322 913513 := bbase (se 2 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 913513 = 685135) (by norm_num)
theorem B913609 : Blo 718322 913609 := bbase (se 2 (by rfl) ⟨342603, by rfl⟩ : syracuseStep 913609 = 685207) (by norm_num)
theorem B3076325 : Blo 718322 3076325 := bbase (se 4 (by rfl) ⟨288405, by rfl⟩ : syracuseStep 3076325 = 576811) (by norm_num)
theorem B1077485 : Blo 718322 1077485 := bbase (se 3 (by rfl) ⟨202028, by rfl⟩ : syracuseStep 1077485 = 404057) (by norm_num)
theorem B1077509 : Blo 718322 1077509 := bbase (se 4 (by rfl) ⟨101016, by rfl⟩ : syracuseStep 1077509 = 202033) (by norm_num)
theorem B1077533 : Blo 718322 1077533 := bbase (se 3 (by rfl) ⟨202037, by rfl⟩ : syracuseStep 1077533 = 404075) (by norm_num)
theorem B1077557 : Blo 718322 1077557 := bbase (se 5 (by rfl) ⟨50510, by rfl⟩ : syracuseStep 1077557 = 101021) (by norm_num)
theorem B1536317 : Blo 718322 1536317 := bbase (se 3 (by rfl) ⟨288059, by rfl⟩ : syracuseStep 1536317 = 576119) (by norm_num)
theorem B1077581 : Blo 718322 1077581 := bbase (se 3 (by rfl) ⟨202046, by rfl⟩ : syracuseStep 1077581 = 404093) (by norm_num)
theorem B1077605 : Blo 718322 1077605 := bbase (se 4 (by rfl) ⟨101025, by rfl⟩ : syracuseStep 1077605 = 202051) (by norm_num)
theorem B913781 : Blo 718322 913781 := bbase (se 5 (by rfl) ⟨42833, by rfl⟩ : syracuseStep 913781 = 85667) (by norm_num)
theorem B1077629 : Blo 718322 1077629 := bbase (se 3 (by rfl) ⟨202055, by rfl⟩ : syracuseStep 1077629 = 404111) (by norm_num)
theorem B1077653 : Blo 718322 1077653 := bbase (se 6 (by rfl) ⟨25257, by rfl⟩ : syracuseStep 1077653 = 50515) (by norm_num)
theorem B1077677 : Blo 718322 1077677 := bbase (se 3 (by rfl) ⟨202064, by rfl⟩ : syracuseStep 1077677 = 404129) (by norm_num)
theorem B913837 : Blo 718322 913837 := bbase (se 3 (by rfl) ⟨171344, by rfl⟩ : syracuseStep 913837 = 342689) (by norm_num)
theorem B1077701 : Blo 718322 1077701 := bbase (se 4 (by rfl) ⟨101034, by rfl⟩ : syracuseStep 1077701 = 202069) (by norm_num)
theorem B1077725 : Blo 718322 1077725 := bbase (se 3 (by rfl) ⟨202073, by rfl⟩ : syracuseStep 1077725 = 404147) (by norm_num)
theorem B1077749 : Blo 718322 1077749 := bbase (se 5 (by rfl) ⟨50519, by rfl⟩ : syracuseStep 1077749 = 101039) (by norm_num)
theorem B1077773 : Blo 718322 1077773 := bbase (se 3 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 1077773 = 404165) (by norm_num)
theorem B913933 : Blo 718322 913933 := bbase (se 3 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 913933 = 342725) (by norm_num)
theorem B1077797 : Blo 718322 1077797 := bbase (se 4 (by rfl) ⟨101043, by rfl⟩ : syracuseStep 1077797 = 202087) (by norm_num)
theorem B1536565 : Blo 718322 1536565 := bbase (se 5 (by rfl) ⟨72026, by rfl⟩ : syracuseStep 1536565 = 144053) (by norm_num)
theorem B1077821 : Blo 718322 1077821 := bbase (se 3 (by rfl) ⟨202091, by rfl⟩ : syracuseStep 1077821 = 404183) (by norm_num)
theorem B1077845 : Blo 718322 1077845 := bbase (se 8 (by rfl) ⟨6315, by rfl⟩ : syracuseStep 1077845 = 12631) (by norm_num)
theorem B1077869 : Blo 718322 1077869 := bbase (se 3 (by rfl) ⟨202100, by rfl⟩ : syracuseStep 1077869 = 404201) (by norm_num)
theorem B1077893 : Blo 718322 1077893 := bbase (se 4 (by rfl) ⟨101052, by rfl⟩ : syracuseStep 1077893 = 202105) (by norm_num)
theorem B1077917 : Blo 718322 1077917 := bbase (se 3 (by rfl) ⟨202109, by rfl⟩ : syracuseStep 1077917 = 404219) (by norm_num)
theorem B1077941 : Blo 718322 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B914105 : Blo 718322 914105 := bbase (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) (by norm_num)
theorem B1077965 : Blo 718322 1077965 := bbase (se 3 (by rfl) ⟨202118, by rfl⟩ : syracuseStep 1077965 = 404237) (by norm_num)
theorem B1077989 : Blo 718322 1077989 := bbase (se 4 (by rfl) ⟨101061, by rfl⟩ : syracuseStep 1077989 = 202123) (by norm_num)
theorem B914161 : Blo 718322 914161 := bbase (se 2 (by rfl) ⟨342810, by rfl⟩ : syracuseStep 914161 = 685621) (by norm_num)
theorem B1078013 : Blo 718322 1078013 := bbase (se 3 (by rfl) ⟨202127, by rfl⟩ : syracuseStep 1078013 = 404255) (by norm_num)
theorem B1078037 : Blo 718322 1078037 := bbase (se 6 (by rfl) ⟨25266, by rfl⟩ : syracuseStep 1078037 = 50533) (by norm_num)
theorem B1078061 : Blo 718322 1078061 := bbase (se 3 (by rfl) ⟨202136, by rfl⟩ : syracuseStep 1078061 = 404273) (by norm_num)
theorem B1078085 : Blo 718322 1078085 := bbase (se 4 (by rfl) ⟨101070, by rfl⟩ : syracuseStep 1078085 = 202141) (by norm_num)
theorem B1078109 : Blo 718322 1078109 := bbase (se 3 (by rfl) ⟨202145, by rfl⟩ : syracuseStep 1078109 = 404291) (by norm_num)
theorem B1078133 : Blo 718322 1078133 := bbase (se 5 (by rfl) ⟨50537, by rfl⟩ : syracuseStep 1078133 = 101075) (by norm_num)
theorem B1078157 : Blo 718322 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B1078181 : Blo 718322 1078181 := bbase (se 4 (by rfl) ⟨101079, by rfl⟩ : syracuseStep 1078181 = 202159) (by norm_num)
theorem B2192293 : Blo 718322 2192293 := bbase (se 4 (by rfl) ⟨205527, by rfl⟩ : syracuseStep 2192293 = 411055) (by norm_num)
theorem B1733557 : Blo 718322 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B1078205 : Blo 718322 1078205 := bbase (se 3 (by rfl) ⟨202163, by rfl⟩ : syracuseStep 1078205 = 404327) (by norm_num)
theorem B750541 : Blo 718322 750541 := bbase (se 3 (by rfl) ⟨140726, by rfl⟩ : syracuseStep 750541 = 281453) (by norm_num)
theorem B1078229 : Blo 718322 1078229 := bbase (se 7 (by rfl) ⟨12635, by rfl⟩ : syracuseStep 1078229 = 25271) (by norm_num)
theorem B1078253 : Blo 718322 1078253 := bbase (se 3 (by rfl) ⟨202172, by rfl⟩ : syracuseStep 1078253 = 404345) (by norm_num)
theorem B1078277 : Blo 718322 1078277 := bbase (se 4 (by rfl) ⟨101088, by rfl⟩ : syracuseStep 1078277 = 202177) (by norm_num)
theorem B1078301 : Blo 718322 1078301 := bbase (se 3 (by rfl) ⟨202181, by rfl⟩ : syracuseStep 1078301 = 404363) (by norm_num)
theorem B1537069 : Blo 718322 1537069 := bbase (se 3 (by rfl) ⟨288200, by rfl⟩ : syracuseStep 1537069 = 576401) (by norm_num)
theorem B1078325 : Blo 718322 1078325 := bbase (se 5 (by rfl) ⟨50546, by rfl⟩ : syracuseStep 1078325 = 101093) (by norm_num)
theorem B1078349 : Blo 718322 1078349 := bbase (se 3 (by rfl) ⟨202190, by rfl⟩ : syracuseStep 1078349 = 404381) (by norm_num)
theorem B1078373 : Blo 718322 1078373 := bbase (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) (by norm_num)
theorem B5534837 : Blo 718322 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B1078397 : Blo 718322 1078397 := bbase (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) (by norm_num)
theorem B1078421 : Blo 718322 1078421 := bbase (se 6 (by rfl) ⟨25275, by rfl⟩ : syracuseStep 1078421 = 50551) (by norm_num)
theorem B1078445 : Blo 718322 1078445 := bbase (se 3 (by rfl) ⟨202208, by rfl⟩ : syracuseStep 1078445 = 404417) (by norm_num)
theorem B1078469 : Blo 718322 1078469 := bbase (se 4 (by rfl) ⟨101106, by rfl⟩ : syracuseStep 1078469 = 202213) (by norm_num)
theorem B1078493 : Blo 718322 1078493 := bbase (se 3 (by rfl) ⟨202217, by rfl⟩ : syracuseStep 1078493 = 404435) (by norm_num)
theorem B1078517 : Blo 718322 1078517 := bbase (se 5 (by rfl) ⟨50555, by rfl⟩ : syracuseStep 1078517 = 101111) (by norm_num)
theorem B1078541 : Blo 718322 1078541 := bbase (se 3 (by rfl) ⟨202226, by rfl⟩ : syracuseStep 1078541 = 404453) (by norm_num)
theorem B1078565 : Blo 718322 1078565 := bbase (se 4 (by rfl) ⟨101115, by rfl⟩ : syracuseStep 1078565 = 202231) (by norm_num)
theorem B1078589 : Blo 718322 1078589 := bbase (se 3 (by rfl) ⟨202235, by rfl⟩ : syracuseStep 1078589 = 404471) (by norm_num)
theorem B1078613 : Blo 718322 1078613 := bbase (se 13 (by rfl) ⟨197, by rfl⟩ : syracuseStep 1078613 = 395) (by norm_num)
theorem B1078637 : Blo 718322 1078637 := bbase (se 3 (by rfl) ⟨202244, by rfl⟩ : syracuseStep 1078637 = 404489) (by norm_num)
theorem B1078661 : Blo 718322 1078661 := bbase (se 4 (by rfl) ⟨101124, by rfl⟩ : syracuseStep 1078661 = 202249) (by norm_num)
theorem B1078685 : Blo 718322 1078685 := bbase (se 3 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 1078685 = 404507) (by norm_num)
theorem B1078709 : Blo 718322 1078709 := bbase (se 5 (by rfl) ⟨50564, by rfl⟩ : syracuseStep 1078709 = 101129) (by norm_num)
theorem B1078733 : Blo 718322 1078733 := bbase (se 3 (by rfl) ⟨202262, by rfl⟩ : syracuseStep 1078733 = 404525) (by norm_num)
theorem B1078757 : Blo 718322 1078757 := bbase (se 4 (by rfl) ⟨101133, by rfl⟩ : syracuseStep 1078757 = 202267) (by norm_num)
theorem B1078781 : Blo 718322 1078781 := bbase (se 3 (by rfl) ⟨202271, by rfl⟩ : syracuseStep 1078781 = 404543) (by norm_num)
theorem B1078805 : Blo 718322 1078805 := bbase (se 6 (by rfl) ⟨25284, by rfl⟩ : syracuseStep 1078805 = 50569) (by norm_num)
theorem B1734173 : Blo 718322 1734173 := bbase (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) (by norm_num)
theorem B1078829 : Blo 718322 1078829 := bbase (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) (by norm_num)
theorem B1078853 : Blo 718322 1078853 := bbase (se 4 (by rfl) ⟨101142, by rfl⟩ : syracuseStep 1078853 = 202285) (by norm_num)
theorem B1078877 : Blo 718322 1078877 := bbase (se 3 (by rfl) ⟨202289, by rfl⟩ : syracuseStep 1078877 = 404579) (by norm_num)
theorem B1078901 : Blo 718322 1078901 := bbase (se 5 (by rfl) ⟨50573, by rfl⟩ : syracuseStep 1078901 = 101147) (by norm_num)
theorem B1078925 : Blo 718322 1078925 := bbase (se 3 (by rfl) ⟨202298, by rfl⟩ : syracuseStep 1078925 = 404597) (by norm_num)
theorem B1078949 : Blo 718322 1078949 := bbase (se 4 (by rfl) ⟨101151, by rfl⟩ : syracuseStep 1078949 = 202303) (by norm_num)
theorem B1078973 : Blo 718322 1078973 := bbase (se 3 (by rfl) ⟨202307, by rfl⟩ : syracuseStep 1078973 = 404615) (by norm_num)
theorem B1078997 : Blo 718322 1078997 := bbase (se 7 (by rfl) ⟨12644, by rfl⟩ : syracuseStep 1078997 = 25289) (by norm_num)
theorem B1079021 : Blo 718322 1079021 := bbase (se 3 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 1079021 = 404633) (by norm_num)
theorem B1079045 : Blo 718322 1079045 := bbase (se 4 (by rfl) ⟨101160, by rfl⟩ : syracuseStep 1079045 = 202321) (by norm_num)
theorem B1079069 : Blo 718322 1079069 := bbase (se 3 (by rfl) ⟨202325, by rfl⟩ : syracuseStep 1079069 = 404651) (by norm_num)
theorem B1079093 : Blo 718322 1079093 := bbase (se 5 (by rfl) ⟨50582, by rfl⟩ : syracuseStep 1079093 = 101165) (by norm_num)
theorem B1079117 : Blo 718322 1079117 := bbase (se 3 (by rfl) ⟨202334, by rfl⟩ : syracuseStep 1079117 = 404669) (by norm_num)
theorem B3700565 : Blo 718322 3700565 := bbase (se 9 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 3700565 = 21683) (by norm_num)
theorem B1079141 : Blo 718322 1079141 := bbase (se 4 (by rfl) ⟨101169, by rfl⟩ : syracuseStep 1079141 = 202339) (by norm_num)
theorem B1079165 : Blo 718322 1079165 := bbase (se 3 (by rfl) ⟨202343, by rfl⟩ : syracuseStep 1079165 = 404687) (by norm_num)
theorem B1079189 : Blo 718322 1079189 := bbase (se 6 (by rfl) ⟨25293, by rfl⟩ : syracuseStep 1079189 = 50587) (by norm_num)
theorem B1537957 : Blo 718322 1537957 := bbase (se 4 (by rfl) ⟨144183, by rfl⟩ : syracuseStep 1537957 = 288367) (by norm_num)
theorem B1079213 : Blo 718322 1079213 := bbase (se 3 (by rfl) ⟨202352, by rfl⟩ : syracuseStep 1079213 = 404705) (by norm_num)
theorem B1079237 : Blo 718322 1079237 := bbase (se 4 (by rfl) ⟨101178, by rfl⟩ : syracuseStep 1079237 = 202357) (by norm_num)
theorem B3078101 : Blo 718322 3078101 := bbase (se 7 (by rfl) ⟨36071, by rfl⟩ : syracuseStep 3078101 = 72143) (by norm_num)
theorem B1079261 : Blo 718322 1079261 := bbase (se 3 (by rfl) ⟨202361, by rfl⟩ : syracuseStep 1079261 = 404723) (by norm_num)
theorem B1079285 : Blo 718322 1079285 := bbase (se 5 (by rfl) ⟨50591, by rfl⟩ : syracuseStep 1079285 = 101183) (by norm_num)
theorem B1079309 : Blo 718322 1079309 := bbase (se 3 (by rfl) ⟨202370, by rfl⟩ : syracuseStep 1079309 = 404741) (by norm_num)
theorem B4093973 : Blo 718322 4093973 := bbase (se 6 (by rfl) ⟨95952, by rfl⟩ : syracuseStep 4093973 = 191905) (by norm_num)
theorem B1079333 : Blo 718322 1079333 := bbase (se 4 (by rfl) ⟨101187, by rfl⟩ : syracuseStep 1079333 = 202375) (by norm_num)
theorem B4388917 : Blo 718322 4388917 := bbase (se 5 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 4388917 = 411461) (by norm_num)
theorem B1079357 : Blo 718322 1079357 := bbase (se 3 (by rfl) ⟨202379, by rfl⟩ : syracuseStep 1079357 = 404759) (by norm_num)
theorem B1079381 : Blo 718322 1079381 := bbase (se 8 (by rfl) ⟨6324, by rfl⟩ : syracuseStep 1079381 = 12649) (by norm_num)
theorem B1079405 : Blo 718322 1079405 := bbase (se 3 (by rfl) ⟨202388, by rfl⟩ : syracuseStep 1079405 = 404777) (by norm_num)
theorem B1079429 : Blo 718322 1079429 := bbase (se 4 (by rfl) ⟨101196, by rfl⟩ : syracuseStep 1079429 = 202393) (by norm_num)
theorem B1079453 : Blo 718322 1079453 := bbase (se 3 (by rfl) ⟨202397, by rfl⟩ : syracuseStep 1079453 = 404795) (by norm_num)
theorem B1079477 : Blo 718322 1079477 := bbase (se 5 (by rfl) ⟨50600, by rfl⟩ : syracuseStep 1079477 = 101201) (by norm_num)
theorem B1079501 : Blo 718322 1079501 := bbase (se 3 (by rfl) ⟨202406, by rfl⟩ : syracuseStep 1079501 = 404813) (by norm_num)
theorem B1079525 : Blo 718322 1079525 := bbase (se 4 (by rfl) ⟨101205, by rfl⟩ : syracuseStep 1079525 = 202411) (by norm_num)
theorem B1079549 : Blo 718322 1079549 := bbase (se 3 (by rfl) ⟨202415, by rfl⟩ : syracuseStep 1079549 = 404831) (by norm_num)
theorem B1079573 : Blo 718322 1079573 := bbase (se 6 (by rfl) ⟨25302, by rfl⟩ : syracuseStep 1079573 = 50605) (by norm_num)
theorem B1734941 : Blo 718322 1734941 := bbase (se 3 (by rfl) ⟨325301, by rfl⟩ : syracuseStep 1734941 = 650603) (by norm_num)
theorem B1734949 : Blo 718322 1734949 := bbase (se 4 (by rfl) ⟨162651, by rfl⟩ : syracuseStep 1734949 = 325303) (by norm_num)
theorem B1079597 : Blo 718322 1079597 := bbase (se 3 (by rfl) ⟨202424, by rfl⟩ : syracuseStep 1079597 = 404849) (by norm_num)
theorem B1079621 : Blo 718322 1079621 := bbase (se 4 (by rfl) ⟨101214, by rfl⟩ : syracuseStep 1079621 = 202429) (by norm_num)
theorem B1079645 : Blo 718322 1079645 := bbase (se 3 (by rfl) ⟨202433, by rfl⟩ : syracuseStep 1079645 = 404867) (by norm_num)
theorem B1079669 : Blo 718322 1079669 := bbase (se 5 (by rfl) ⟨50609, by rfl⟩ : syracuseStep 1079669 = 101219) (by norm_num)
theorem B1079693 : Blo 718322 1079693 := bbase (se 3 (by rfl) ⟨202442, by rfl⟩ : syracuseStep 1079693 = 404885) (by norm_num)
theorem B1538453 : Blo 718322 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B1079717 : Blo 718322 1079717 := bbase (se 4 (by rfl) ⟨101223, by rfl⟩ : syracuseStep 1079717 = 202447) (by norm_num)
theorem B1079741 : Blo 718322 1079741 := bbase (se 3 (by rfl) ⟨202451, by rfl⟩ : syracuseStep 1079741 = 404903) (by norm_num)
theorem B1079765 : Blo 718322 1079765 := bbase (se 7 (by rfl) ⟨12653, by rfl⟩ : syracuseStep 1079765 = 25307) (by norm_num)
theorem B1079789 : Blo 718322 1079789 := bbase (se 3 (by rfl) ⟨202460, by rfl⟩ : syracuseStep 1079789 = 404921) (by norm_num)
theorem B1079813 : Blo 718322 1079813 := bbase (se 4 (by rfl) ⟨101232, by rfl⟩ : syracuseStep 1079813 = 202465) (by norm_num)
theorem B1079837 : Blo 718322 1079837 := bbase (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) (by norm_num)
theorem B1079861 : Blo 718322 1079861 := bbase (se 5 (by rfl) ⟨50618, by rfl⟩ : syracuseStep 1079861 = 101237) (by norm_num)
theorem B1079885 : Blo 718322 1079885 := bbase (se 3 (by rfl) ⟨202478, by rfl⟩ : syracuseStep 1079885 = 404957) (by norm_num)
theorem B1079909 : Blo 718322 1079909 := bbase (se 4 (by rfl) ⟨101241, by rfl⟩ : syracuseStep 1079909 = 202483) (by norm_num)
theorem B1079933 : Blo 718322 1079933 := bbase (se 3 (by rfl) ⟨202487, by rfl⟩ : syracuseStep 1079933 = 404975) (by norm_num)
theorem B1079957 : Blo 718322 1079957 := bbase (se 6 (by rfl) ⟨25311, by rfl⟩ : syracuseStep 1079957 = 50623) (by norm_num)
theorem B1079981 : Blo 718322 1079981 := bbase (se 3 (by rfl) ⟨202496, by rfl⟩ : syracuseStep 1079981 = 404993) (by norm_num)
theorem B5470901 : Blo 718322 5470901 := bbase (se 5 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 5470901 = 512897) (by norm_num)
theorem B1080005 : Blo 718322 1080005 := bbase (se 4 (by rfl) ⟨101250, by rfl⟩ : syracuseStep 1080005 = 202501) (by norm_num)
theorem B1080029 : Blo 718322 1080029 := bbase (se 3 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 1080029 = 405011) (by norm_num)
theorem B1080053 : Blo 718322 1080053 := bbase (se 5 (by rfl) ⟨50627, by rfl⟩ : syracuseStep 1080053 = 101255) (by norm_num)
theorem B1080077 : Blo 718322 1080077 := bbase (se 3 (by rfl) ⟨202514, by rfl⟩ : syracuseStep 1080077 = 405029) (by norm_num)
theorem B1080101 : Blo 718322 1080101 := bbase (se 4 (by rfl) ⟨101259, by rfl⟩ : syracuseStep 1080101 = 202519) (by norm_num)
theorem B1080125 : Blo 718322 1080125 := bbase (se 3 (by rfl) ⟨202523, by rfl⟩ : syracuseStep 1080125 = 405047) (by norm_num)
theorem B1080149 : Blo 718322 1080149 := bbase (se 9 (by rfl) ⟨3164, by rfl⟩ : syracuseStep 1080149 = 6329) (by norm_num)
theorem B1080173 : Blo 718322 1080173 := bbase (se 3 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 1080173 = 405065) (by norm_num)
theorem B1080197 : Blo 718322 1080197 := bbase (se 4 (by rfl) ⟨101268, by rfl⟩ : syracuseStep 1080197 = 202537) (by norm_num)
theorem B1080221 : Blo 718322 1080221 := bbase (se 3 (by rfl) ⟨202541, by rfl⟩ : syracuseStep 1080221 = 405083) (by norm_num)
theorem B1080245 : Blo 718322 1080245 := bbase (se 5 (by rfl) ⟨50636, by rfl⟩ : syracuseStep 1080245 = 101273) (by norm_num)
theorem B1080269 : Blo 718322 1080269 := bbase (se 3 (by rfl) ⟨202550, by rfl⟩ : syracuseStep 1080269 = 405101) (by norm_num)
theorem B1080293 : Blo 718322 1080293 := bbase (se 4 (by rfl) ⟨101277, by rfl⟩ : syracuseStep 1080293 = 202555) (by norm_num)
theorem B1407989 : Blo 718322 1407989 := bbase (se 5 (by rfl) ⟨65999, by rfl⟩ : syracuseStep 1407989 = 131999) (by norm_num)
theorem B1080317 : Blo 718322 1080317 := bbase (se 3 (by rfl) ⟨202559, by rfl⟩ : syracuseStep 1080317 = 405119) (by norm_num)
theorem B1080341 : Blo 718322 1080341 := bbase (se 6 (by rfl) ⟨25320, by rfl⟩ : syracuseStep 1080341 = 50641) (by norm_num)
theorem B1080365 : Blo 718322 1080365 := bbase (se 3 (by rfl) ⟨202568, by rfl⟩ : syracuseStep 1080365 = 405137) (by norm_num)
theorem B1080389 : Blo 718322 1080389 := bbase (se 4 (by rfl) ⟨101286, by rfl⟩ : syracuseStep 1080389 = 202573) (by norm_num)
theorem B1080413 : Blo 718322 1080413 := bbase (se 3 (by rfl) ⟨202577, by rfl⟩ : syracuseStep 1080413 = 405155) (by norm_num)
theorem B1080437 : Blo 718322 1080437 := bbase (se 5 (by rfl) ⟨50645, by rfl⟩ : syracuseStep 1080437 = 101291) (by norm_num)
theorem B1080461 : Blo 718322 1080461 := bbase (se 3 (by rfl) ⟨202586, by rfl⟩ : syracuseStep 1080461 = 405173) (by norm_num)
theorem B1080485 : Blo 718322 1080485 := bbase (se 4 (by rfl) ⟨101295, by rfl⟩ : syracuseStep 1080485 = 202591) (by norm_num)
theorem B4095157 : Blo 718322 4095157 := bbase (se 5 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 4095157 = 383921) (by norm_num)
theorem B1080509 : Blo 718322 1080509 := bbase (se 3 (by rfl) ⟨202595, by rfl⟩ : syracuseStep 1080509 = 405191) (by norm_num)
theorem B1080533 : Blo 718322 1080533 := bbase (se 7 (by rfl) ⟨12662, by rfl⟩ : syracuseStep 1080533 = 25325) (by norm_num)
theorem B1080557 : Blo 718322 1080557 := bbase (se 3 (by rfl) ⟨202604, by rfl⟩ : syracuseStep 1080557 = 405209) (by norm_num)
theorem B1080581 : Blo 718322 1080581 := bbase (se 4 (by rfl) ⟨101304, by rfl⟩ : syracuseStep 1080581 = 202609) (by norm_num)
theorem B1539341 : Blo 718322 1539341 := bbase (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) (by norm_num)
theorem B1080605 : Blo 718322 1080605 := bbase (se 3 (by rfl) ⟨202613, by rfl⟩ : syracuseStep 1080605 = 405227) (by norm_num)
theorem B1080629 : Blo 718322 1080629 := bbase (se 5 (by rfl) ⟨50654, by rfl⟩ : syracuseStep 1080629 = 101309) (by norm_num)
theorem B1080653 : Blo 718322 1080653 := bbase (se 3 (by rfl) ⟨202622, by rfl⟩ : syracuseStep 1080653 = 405245) (by norm_num)
theorem B1080677 : Blo 718322 1080677 := bbase (se 4 (by rfl) ⟨101313, by rfl⟩ : syracuseStep 1080677 = 202627) (by norm_num)
theorem B1080701 : Blo 718322 1080701 := bbase (se 3 (by rfl) ⟨202631, by rfl⟩ : syracuseStep 1080701 = 405263) (by norm_num)
theorem B1539461 : Blo 718322 1539461 := bbase (se 4 (by rfl) ⟨144324, by rfl⟩ : syracuseStep 1539461 = 288649) (by norm_num)
theorem B1080725 : Blo 718322 1080725 := bbase (se 6 (by rfl) ⟨25329, by rfl⟩ : syracuseStep 1080725 = 50659) (by norm_num)
theorem B1080749 : Blo 718322 1080749 := bbase (se 3 (by rfl) ⟨202640, by rfl⟩ : syracuseStep 1080749 = 405281) (by norm_num)
theorem B1080773 : Blo 718322 1080773 := bbase (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) (by norm_num)
theorem B1080797 : Blo 718322 1080797 := bbase (se 3 (by rfl) ⟨202649, by rfl⟩ : syracuseStep 1080797 = 405299) (by norm_num)
theorem B1080821 : Blo 718322 1080821 := bbase (se 5 (by rfl) ⟨50663, by rfl⟩ : syracuseStep 1080821 = 101327) (by norm_num)
theorem B1080845 : Blo 718322 1080845 := bbase (se 3 (by rfl) ⟨202658, by rfl⟩ : syracuseStep 1080845 = 405317) (by norm_num)
theorem B1080869 : Blo 718322 1080869 := bbase (se 4 (by rfl) ⟨101331, by rfl⟩ : syracuseStep 1080869 = 202663) (by norm_num)
theorem B1080893 : Blo 718322 1080893 := bbase (se 3 (by rfl) ⟨202667, by rfl⟩ : syracuseStep 1080893 = 405335) (by norm_num)
theorem B1080917 : Blo 718322 1080917 := bbase (se 8 (by rfl) ⟨6333, by rfl⟩ : syracuseStep 1080917 = 12667) (by norm_num)
theorem B1080941 : Blo 718322 1080941 := bbase (se 3 (by rfl) ⟨202676, by rfl⟩ : syracuseStep 1080941 = 405353) (by norm_num)
theorem B2424437 : Blo 718322 2424437 := bbase (se 5 (by rfl) ⟨113645, by rfl⟩ : syracuseStep 2424437 = 227291) (by norm_num)
theorem B1080965 : Blo 718322 1080965 := bbase (se 4 (by rfl) ⟨101340, by rfl⟩ : syracuseStep 1080965 = 202681) (by norm_num)
theorem B1080989 : Blo 718322 1080989 := bbase (se 3 (by rfl) ⟨202685, by rfl⟩ : syracuseStep 1080989 = 405371) (by norm_num)
theorem B1081013 : Blo 718322 1081013 := bbase (se 5 (by rfl) ⟨50672, by rfl⟩ : syracuseStep 1081013 = 101345) (by norm_num)
theorem B1081037 : Blo 718322 1081037 := bbase (se 3 (by rfl) ⟨202694, by rfl⟩ : syracuseStep 1081037 = 405389) (by norm_num)
theorem B1081061 : Blo 718322 1081061 := bbase (se 4 (by rfl) ⟨101349, by rfl⟩ : syracuseStep 1081061 = 202699) (by norm_num)
theorem B1081085 : Blo 718322 1081085 := bbase (se 3 (by rfl) ⟨202703, by rfl⟩ : syracuseStep 1081085 = 405407) (by norm_num)
theorem B1081109 : Blo 718322 1081109 := bbase (se 6 (by rfl) ⟨25338, by rfl⟩ : syracuseStep 1081109 = 50677) (by norm_num)
theorem B1212205 : Blo 718322 1212205 := bbase (se 3 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 1212205 = 454577) (by norm_num)
theorem B1081133 : Blo 718322 1081133 := bbase (se 3 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 1081133 = 405425) (by norm_num)
theorem B2817845 : Blo 718322 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B3637061 : Blo 718322 3637061 := bbase (se 4 (by rfl) ⟨340974, by rfl⟩ : syracuseStep 3637061 = 681949) (by norm_num)
theorem B1081157 : Blo 718322 1081157 := bbase (se 4 (by rfl) ⟨101358, by rfl⟩ : syracuseStep 1081157 = 202717) (by norm_num)
theorem B3702613 : Blo 718322 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B1081181 : Blo 718322 1081181 := bbase (se 3 (by rfl) ⟨202721, by rfl⟩ : syracuseStep 1081181 = 405443) (by norm_num)
theorem B1081205 : Blo 718322 1081205 := bbase (se 5 (by rfl) ⟨50681, by rfl⟩ : syracuseStep 1081205 = 101363) (by norm_num)
theorem B1212293 : Blo 718322 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B1081229 : Blo 718322 1081229 := bbase (se 3 (by rfl) ⟨202730, by rfl⟩ : syracuseStep 1081229 = 405461) (by norm_num)
theorem B1081253 : Blo 718322 1081253 := bbase (se 4 (by rfl) ⟨101367, by rfl⟩ : syracuseStep 1081253 = 202735) (by norm_num)
theorem B1081277 : Blo 718322 1081277 := bbase (se 3 (by rfl) ⟨202739, by rfl⟩ : syracuseStep 1081277 = 405479) (by norm_num)
theorem B1081301 : Blo 718322 1081301 := bbase (se 7 (by rfl) ⟨12671, by rfl⟩ : syracuseStep 1081301 = 25343) (by norm_num)
theorem B1081325 : Blo 718322 1081325 := bbase (se 3 (by rfl) ⟨202748, by rfl⟩ : syracuseStep 1081325 = 405497) (by norm_num)
theorem B1540093 : Blo 718322 1540093 := bbase (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) (by norm_num)
theorem B720899 : Blo 718322 720899 := bstep (se 1 (by rfl) ⟨540674, by rfl⟩ : syracuseStep 720899 = 1081349) B1081349
theorem B1081361 : Blo 718322 1081361 := bstep (se 2 (by rfl) ⟨405510, by rfl⟩ : syracuseStep 1081361 = 811021) B811021
theorem B720915 : Blo 718322 720915 := bstep (se 1 (by rfl) ⟨540686, by rfl⟩ : syracuseStep 720915 = 1081373) B1081373
theorem B1081379 : Blo 718322 1081379 := bstep (se 1 (by rfl) ⟨811034, by rfl⟩ : syracuseStep 1081379 = 1622069) B1622069
theorem B720931 : Blo 718322 720931 := bstep (se 1 (by rfl) ⟨540698, by rfl⟩ : syracuseStep 720931 = 1081397) B1081397
theorem B720947 : Blo 718322 720947 := bstep (se 1 (by rfl) ⟨540710, by rfl⟩ : syracuseStep 720947 = 1081421) B1081421
theorem B1081409 : Blo 718322 1081409 := bstep (se 2 (by rfl) ⟨405528, by rfl⟩ : syracuseStep 1081409 = 811057) B811057
theorem B720963 : Blo 718322 720963 := bstep (se 1 (by rfl) ⟨540722, by rfl⟩ : syracuseStep 720963 = 1081445) B1081445
theorem B1081427 : Blo 718322 1081427 := bstep (se 1 (by rfl) ⟨811070, by rfl⟩ : syracuseStep 1081427 = 1622141) B1622141
theorem B720979 : Blo 718322 720979 := bstep (se 1 (by rfl) ⟨540734, by rfl⟩ : syracuseStep 720979 = 1081469) B1081469
theorem B720995 : Blo 718322 720995 := bstep (se 1 (by rfl) ⟨540746, by rfl⟩ : syracuseStep 720995 = 1081493) B1081493
theorem B5931107 : Blo 718322 5931107 := bstep (se 1 (by rfl) ⟨4448330, by rfl⟩ : syracuseStep 5931107 = 8896661) B8896661
theorem B1212529 : Blo 718322 1212529 := bstep (se 2 (by rfl) ⟨454698, by rfl⟩ : syracuseStep 1212529 = 909397) B909397
theorem B1081457 : Blo 718322 1081457 := bstep (se 2 (by rfl) ⟨405546, by rfl⟩ : syracuseStep 1081457 = 811093) B811093
theorem B721011 : Blo 718322 721011 := bstep (se 1 (by rfl) ⟨540758, by rfl⟩ : syracuseStep 721011 = 1081517) B1081517
theorem B1081475 : Blo 718322 1081475 := bstep (se 1 (by rfl) ⟨811106, by rfl⟩ : syracuseStep 1081475 = 1622213) B1622213
theorem B721027 : Blo 718322 721027 := bstep (se 1 (by rfl) ⟨540770, by rfl⟩ : syracuseStep 721027 = 1081541) B1081541
theorem B2424977 : Blo 718322 2424977 := bstep (se 2 (by rfl) ⟨909366, by rfl⟩ : syracuseStep 2424977 = 1818733) B1818733
theorem B1212563 : Blo 718322 1212563 := bstep (se 1 (by rfl) ⟨909422, by rfl⟩ : syracuseStep 1212563 = 1818845) B1818845
theorem B721043 : Blo 718322 721043 := bstep (se 1 (by rfl) ⟨540782, by rfl⟩ : syracuseStep 721043 = 1081565) B1081565
theorem B1081505 : Blo 718322 1081505 := bstep (se 2 (by rfl) ⟨405564, by rfl⟩ : syracuseStep 1081505 = 811129) B811129
theorem B721059 : Blo 718322 721059 := bstep (se 1 (by rfl) ⟨540794, by rfl⟩ : syracuseStep 721059 = 1081589) B1081589
theorem B1081523 : Blo 718322 1081523 := bstep (se 1 (by rfl) ⟨811142, by rfl⟩ : syracuseStep 1081523 = 1622285) B1622285
theorem B721075 : Blo 718322 721075 := bstep (se 1 (by rfl) ⟨540806, by rfl⟩ : syracuseStep 721075 = 1081613) B1081613
theorem B721091 : Blo 718322 721091 := bstep (se 1 (by rfl) ⟨540818, by rfl⟩ : syracuseStep 721091 = 1081637) B1081637
theorem B1081553 : Blo 718322 1081553 := bstep (se 2 (by rfl) ⟨405582, by rfl⟩ : syracuseStep 1081553 = 811165) B811165
theorem B721107 : Blo 718322 721107 := bstep (se 1 (by rfl) ⟨540830, by rfl⟩ : syracuseStep 721107 = 1081661) B1081661
theorem B1081571 : Blo 718322 1081571 := bstep (se 1 (by rfl) ⟨811178, by rfl⟩ : syracuseStep 1081571 = 1622357) B1622357
theorem B721123 : Blo 718322 721123 := bstep (se 1 (by rfl) ⟨540842, by rfl⟩ : syracuseStep 721123 = 1081685) B1081685
theorem B721139 : Blo 718322 721139 := bstep (se 1 (by rfl) ⟨540854, by rfl⟩ : syracuseStep 721139 = 1081709) B1081709
theorem B1081601 : Blo 718322 1081601 := bstep (se 2 (by rfl) ⟨405600, by rfl⟩ : syracuseStep 1081601 = 811201) B811201
theorem B721155 : Blo 718322 721155 := bstep (se 1 (by rfl) ⟨540866, by rfl⟩ : syracuseStep 721155 = 1081733) B1081733
theorem B1212691 : Blo 718322 1212691 := bstep (se 1 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 1212691 = 1819037) B1819037
theorem B1081619 : Blo 718322 1081619 := bstep (se 1 (by rfl) ⟨811214, by rfl⟩ : syracuseStep 1081619 = 1622429) B1622429
theorem B721171 : Blo 718322 721171 := bstep (se 1 (by rfl) ⟨540878, by rfl⟩ : syracuseStep 721171 = 1081757) B1081757
theorem B721187 : Blo 718322 721187 := bstep (se 1 (by rfl) ⟨540890, by rfl⟩ : syracuseStep 721187 = 1081781) B1081781
theorem B1081649 : Blo 718322 1081649 := bstep (se 2 (by rfl) ⟨405618, by rfl⟩ : syracuseStep 1081649 = 811237) B811237
theorem B721203 : Blo 718322 721203 := bstep (se 1 (by rfl) ⟨540902, by rfl⟩ : syracuseStep 721203 = 1081805) B1081805
theorem B1081667 : Blo 718322 1081667 := bstep (se 1 (by rfl) ⟨811250, by rfl⟩ : syracuseStep 1081667 = 1622501) B1622501
theorem B721219 : Blo 718322 721219 := bstep (se 1 (by rfl) ⟨540914, by rfl⟩ : syracuseStep 721219 = 1081829) B1081829
theorem B721235 : Blo 718322 721235 := bstep (se 1 (by rfl) ⟨540926, by rfl⟩ : syracuseStep 721235 = 1081853) B1081853
theorem B1081697 : Blo 718322 1081697 := bstep (se 2 (by rfl) ⟨405636, by rfl⟩ : syracuseStep 1081697 = 811273) B811273
theorem B721251 : Blo 718322 721251 := bstep (se 1 (by rfl) ⟨540938, by rfl⟩ : syracuseStep 721251 = 1081877) B1081877
theorem B1081715 : Blo 718322 1081715 := bstep (se 1 (by rfl) ⟨811286, by rfl⟩ : syracuseStep 1081715 = 1622573) B1622573
theorem B721267 : Blo 718322 721267 := bstep (se 1 (by rfl) ⟨540950, by rfl⟩ : syracuseStep 721267 = 1081901) B1081901
theorem B721283 : Blo 718322 721283 := bstep (se 1 (by rfl) ⟨540962, by rfl⟩ : syracuseStep 721283 = 1081925) B1081925
theorem B1081745 : Blo 718322 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B721299 : Blo 718322 721299 := bstep (se 1 (by rfl) ⟨540974, by rfl⟩ : syracuseStep 721299 = 1081949) B1081949
theorem B1212833 : Blo 718322 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B721315 : Blo 718322 721315 := bstep (se 1 (by rfl) ⟨540986, by rfl⟩ : syracuseStep 721315 = 1081973) B1081973
theorem B1081763 : Blo 718322 1081763 := bstep (se 1 (by rfl) ⟨811322, by rfl⟩ : syracuseStep 1081763 = 1622645) B1622645
theorem B4096433 : Blo 718322 4096433 := bstep (se 2 (by rfl) ⟨1536162, by rfl⟩ : syracuseStep 4096433 = 3072325) B3072325
theorem B1540529 : Blo 718322 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B721331 : Blo 718322 721331 := bstep (se 1 (by rfl) ⟨540998, by rfl⟩ : syracuseStep 721331 = 1081997) B1081997
theorem B1081793 : Blo 718322 1081793 := bstep (se 2 (by rfl) ⟨405672, by rfl⟩ : syracuseStep 1081793 = 811345) B811345
theorem B721347 : Blo 718322 721347 := bstep (se 1 (by rfl) ⟨541010, by rfl⟩ : syracuseStep 721347 = 1082021) B1082021
theorem B3637709 : Blo 718322 3637709 := bstep (se 3 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 3637709 = 1364141) B1364141
theorem B1081811 : Blo 718322 1081811 := bstep (se 1 (by rfl) ⟨811358, by rfl⟩ : syracuseStep 1081811 = 1622717) B1622717
theorem B721363 : Blo 718322 721363 := bstep (se 1 (by rfl) ⟨541022, by rfl⟩ : syracuseStep 721363 = 1082045) B1082045
theorem B721379 : Blo 718322 721379 := bstep (se 1 (by rfl) ⟨541034, by rfl⟩ : syracuseStep 721379 = 1082069) B1082069
theorem B1081841 : Blo 718322 1081841 := bstep (se 2 (by rfl) ⟨405690, by rfl⟩ : syracuseStep 1081841 = 811381) B811381
theorem B721395 : Blo 718322 721395 := bstep (se 1 (by rfl) ⟨541046, by rfl⟩ : syracuseStep 721395 = 1082093) B1082093
theorem B1081859 : Blo 718322 1081859 := bstep (se 1 (by rfl) ⟨811394, by rfl⟩ : syracuseStep 1081859 = 1622789) B1622789
theorem B721411 : Blo 718322 721411 := bstep (se 1 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 721411 = 1082117) B1082117
theorem B3899917 : Blo 718322 3899917 := bstep (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) B1462469
theorem B721427 : Blo 718322 721427 := bstep (se 1 (by rfl) ⟨541070, by rfl⟩ : syracuseStep 721427 = 1082141) B1082141
theorem B1212961 : Blo 718322 1212961 := bstep (se 2 (by rfl) ⟨454860, by rfl⟩ : syracuseStep 1212961 = 909721) B909721
theorem B1081889 : Blo 718322 1081889 := bstep (se 2 (by rfl) ⟨405708, by rfl⟩ : syracuseStep 1081889 = 811417) B811417
theorem B721443 : Blo 718322 721443 := bstep (se 1 (by rfl) ⟨541082, by rfl⟩ : syracuseStep 721443 = 1082165) B1082165
theorem B2196017 : Blo 718322 2196017 := bstep (se 2 (by rfl) ⟨823506, by rfl⟩ : syracuseStep 2196017 = 1647013) B1647013
theorem B1081907 : Blo 718322 1081907 := bstep (se 1 (by rfl) ⟨811430, by rfl⟩ : syracuseStep 1081907 = 1622861) B1622861
theorem B721459 : Blo 718322 721459 := bstep (se 1 (by rfl) ⟨541094, by rfl⟩ : syracuseStep 721459 = 1082189) B1082189
theorem B1212995 : Blo 718322 1212995 := bstep (se 1 (by rfl) ⟨909746, by rfl⟩ : syracuseStep 1212995 = 1819493) B1819493
theorem B721475 : Blo 718322 721475 := bstep (se 1 (by rfl) ⟨541106, by rfl⟩ : syracuseStep 721475 = 1082213) B1082213
theorem B1081937 : Blo 718322 1081937 := bstep (se 2 (by rfl) ⟨405726, by rfl⟩ : syracuseStep 1081937 = 811453) B811453
theorem B721491 : Blo 718322 721491 := bstep (se 1 (by rfl) ⟨541118, by rfl⟩ : syracuseStep 721491 = 1082237) B1082237
theorem B1081955 : Blo 718322 1081955 := bstep (se 1 (by rfl) ⟨811466, by rfl⟩ : syracuseStep 1081955 = 1622933) B1622933
theorem B721507 : Blo 718322 721507 := bstep (se 1 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 721507 = 1082261) B1082261
theorem B721523 : Blo 718322 721523 := bstep (se 1 (by rfl) ⟨541142, by rfl⟩ : syracuseStep 721523 = 1082285) B1082285
theorem B1081985 : Blo 718322 1081985 := bstep (se 2 (by rfl) ⟨405744, by rfl⟩ : syracuseStep 1081985 = 811489) B811489
theorem B721539 : Blo 718322 721539 := bstep (se 1 (by rfl) ⟨541154, by rfl⟩ : syracuseStep 721539 = 1082309) B1082309
theorem B1082003 : Blo 718322 1082003 := bstep (se 1 (by rfl) ⟨811502, by rfl⟩ : syracuseStep 1082003 = 1623005) B1623005
theorem B721555 : Blo 718322 721555 := bstep (se 1 (by rfl) ⟨541166, by rfl⟩ : syracuseStep 721555 = 1082333) B1082333
theorem B721571 : Blo 718322 721571 := bstep (se 1 (by rfl) ⟨541178, by rfl⟩ : syracuseStep 721571 = 1082357) B1082357
theorem B2425517 : Blo 718322 2425517 := bstep (se 3 (by rfl) ⟨454784, by rfl⟩ : syracuseStep 2425517 = 909569) B909569
theorem B1082033 : Blo 718322 1082033 := bstep (se 2 (by rfl) ⟨405762, by rfl⟩ : syracuseStep 1082033 = 811525) B811525
theorem B721587 : Blo 718322 721587 := bstep (se 1 (by rfl) ⟨541190, by rfl⟩ : syracuseStep 721587 = 1082381) B1082381
theorem B1213123 : Blo 718322 1213123 := bstep (se 1 (by rfl) ⟨909842, by rfl⟩ : syracuseStep 1213123 = 1819685) B1819685
theorem B1082051 : Blo 718322 1082051 := bstep (se 1 (by rfl) ⟨811538, by rfl⟩ : syracuseStep 1082051 = 1623077) B1623077
theorem B721603 : Blo 718322 721603 := bstep (se 1 (by rfl) ⟨541202, by rfl⟩ : syracuseStep 721603 = 1082405) B1082405
theorem B721619 : Blo 718322 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B1082081 : Blo 718322 1082081 := bstep (se 2 (by rfl) ⟨405780, by rfl⟩ : syracuseStep 1082081 = 811561) B811561
theorem B2425571 : Blo 718322 2425571 := bstep (se 1 (by rfl) ⟨1819178, by rfl⟩ : syracuseStep 2425571 = 3638357) B3638357
theorem B721635 : Blo 718322 721635 := bstep (se 1 (by rfl) ⟨541226, by rfl⟩ : syracuseStep 721635 = 1082453) B1082453
theorem B1082099 : Blo 718322 1082099 := bstep (se 1 (by rfl) ⟨811574, by rfl⟩ : syracuseStep 1082099 = 1623149) B1623149
theorem B721651 : Blo 718322 721651 := bstep (se 1 (by rfl) ⟨541238, by rfl⟩ : syracuseStep 721651 = 1082477) B1082477
theorem B721667 : Blo 718322 721667 := bstep (se 1 (by rfl) ⟨541250, by rfl⟩ : syracuseStep 721667 = 1082501) B1082501
theorem B1082129 : Blo 718322 1082129 := bstep (se 2 (by rfl) ⟨405798, by rfl⟩ : syracuseStep 1082129 = 811597) B811597
theorem B721683 : Blo 718322 721683 := bstep (se 1 (by rfl) ⟨541262, by rfl⟩ : syracuseStep 721683 = 1082525) B1082525
theorem B1868579 : Blo 718322 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1082147 : Blo 718322 1082147 := bstep (se 1 (by rfl) ⟨811610, by rfl⟩ : syracuseStep 1082147 = 1623221) B1623221
theorem B721699 : Blo 718322 721699 := bstep (se 1 (by rfl) ⟨541274, by rfl⟩ : syracuseStep 721699 = 1082549) B1082549
theorem B721715 : Blo 718322 721715 := bstep (se 1 (by rfl) ⟨541286, by rfl⟩ : syracuseStep 721715 = 1082573) B1082573
theorem B1082177 : Blo 718322 1082177 := bstep (se 2 (by rfl) ⟨405816, by rfl⟩ : syracuseStep 1082177 = 811633) B811633
theorem B721731 : Blo 718322 721731 := bstep (se 1 (by rfl) ⟨541298, by rfl⟩ : syracuseStep 721731 = 1082597) B1082597
theorem B1213265 : Blo 718322 1213265 := bstep (se 2 (by rfl) ⟨454974, by rfl⟩ : syracuseStep 1213265 = 909949) B909949
theorem B1082195 : Blo 718322 1082195 := bstep (se 1 (by rfl) ⟨811646, by rfl⟩ : syracuseStep 1082195 = 1623293) B1623293
theorem B721747 : Blo 718322 721747 := bstep (se 1 (by rfl) ⟨541310, by rfl⟩ : syracuseStep 721747 = 1082621) B1082621
theorem B721763 : Blo 718322 721763 := bstep (se 1 (by rfl) ⟨541322, by rfl⟩ : syracuseStep 721763 = 1082645) B1082645
theorem B3081073 : Blo 718322 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B1082225 : Blo 718322 1082225 := bstep (se 2 (by rfl) ⟨405834, by rfl⟩ : syracuseStep 1082225 = 811669) B811669
theorem B721779 : Blo 718322 721779 := bstep (se 1 (by rfl) ⟨541334, by rfl⟩ : syracuseStep 721779 = 1082669) B1082669
theorem B1082243 : Blo 718322 1082243 := bstep (se 1 (by rfl) ⟨811682, by rfl⟩ : syracuseStep 1082243 = 1623365) B1623365
theorem B721795 : Blo 718322 721795 := bstep (se 1 (by rfl) ⟨541346, by rfl⟩ : syracuseStep 721795 = 1082693) B1082693
theorem B721811 : Blo 718322 721811 := bstep (se 1 (by rfl) ⟨541358, by rfl⟩ : syracuseStep 721811 = 1082717) B1082717
theorem B1082273 : Blo 718322 1082273 := bstep (se 2 (by rfl) ⟨405852, by rfl⟩ : syracuseStep 1082273 = 811705) B811705
theorem B721827 : Blo 718322 721827 := bstep (se 1 (by rfl) ⟨541370, by rfl⟩ : syracuseStep 721827 = 1082741) B1082741
theorem B1082291 : Blo 718322 1082291 := bstep (se 1 (by rfl) ⟨811718, by rfl⟩ : syracuseStep 1082291 = 1623437) B1623437
theorem B721843 : Blo 718322 721843 := bstep (se 1 (by rfl) ⟨541382, by rfl⟩ : syracuseStep 721843 = 1082765) B1082765
theorem B721859 : Blo 718322 721859 := bstep (se 1 (by rfl) ⟨541394, by rfl⟩ : syracuseStep 721859 = 1082789) B1082789
theorem B1213393 : Blo 718322 1213393 := bstep (se 2 (by rfl) ⟨455022, by rfl⟩ : syracuseStep 1213393 = 910045) B910045
theorem B1082321 : Blo 718322 1082321 := bstep (se 2 (by rfl) ⟨405870, by rfl⟩ : syracuseStep 1082321 = 811741) B811741
theorem B721875 : Blo 718322 721875 := bstep (se 1 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 721875 = 1082813) B1082813
theorem B1082339 : Blo 718322 1082339 := bstep (se 1 (by rfl) ⟨811754, by rfl⟩ : syracuseStep 1082339 = 1623509) B1623509
theorem B721891 : Blo 718322 721891 := bstep (se 1 (by rfl) ⟨541418, by rfl⟩ : syracuseStep 721891 = 1082837) B1082837
theorem B2425841 : Blo 718322 2425841 := bstep (se 2 (by rfl) ⟨909690, by rfl⟩ : syracuseStep 2425841 = 1819381) B1819381
theorem B1213427 : Blo 718322 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B721907 : Blo 718322 721907 := bstep (se 1 (by rfl) ⟨541430, by rfl⟩ : syracuseStep 721907 = 1082861) B1082861
theorem B1082369 : Blo 718322 1082369 := bstep (se 2 (by rfl) ⟨405888, by rfl⟩ : syracuseStep 1082369 = 811777) B811777
theorem B721923 : Blo 718322 721923 := bstep (se 1 (by rfl) ⟨541442, by rfl⟩ : syracuseStep 721923 = 1082885) B1082885
theorem B1082387 : Blo 718322 1082387 := bstep (se 1 (by rfl) ⟨811790, by rfl⟩ : syracuseStep 1082387 = 1623581) B1623581
theorem B721939 : Blo 718322 721939 := bstep (se 1 (by rfl) ⟨541454, by rfl⟩ : syracuseStep 721939 = 1082909) B1082909
theorem B721955 : Blo 718322 721955 := bstep (se 1 (by rfl) ⟨541466, by rfl⟩ : syracuseStep 721955 = 1082933) B1082933
theorem B1082417 : Blo 718322 1082417 := bstep (se 2 (by rfl) ⟨405906, by rfl⟩ : syracuseStep 1082417 = 811813) B811813
theorem B721971 : Blo 718322 721971 := bstep (se 1 (by rfl) ⟨541478, by rfl⟩ : syracuseStep 721971 = 1082957) B1082957
theorem B1082435 : Blo 718322 1082435 := bstep (se 1 (by rfl) ⟨811826, by rfl⟩ : syracuseStep 1082435 = 1623653) B1623653
theorem B721987 : Blo 718322 721987 := bstep (se 1 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 721987 = 1082981) B1082981
theorem B722003 : Blo 718322 722003 := bstep (se 1 (by rfl) ⟨541502, by rfl⟩ : syracuseStep 722003 = 1083005) B1083005
theorem B1082465 : Blo 718322 1082465 := bstep (se 2 (by rfl) ⟨405924, by rfl⟩ : syracuseStep 1082465 = 811849) B811849
theorem B722019 : Blo 718322 722019 := bstep (se 1 (by rfl) ⟨541514, by rfl⟩ : syracuseStep 722019 = 1083029) B1083029
theorem B1213555 : Blo 718322 1213555 := bstep (se 1 (by rfl) ⟨910166, by rfl⟩ : syracuseStep 1213555 = 1820333) B1820333
theorem B1082483 : Blo 718322 1082483 := bstep (se 1 (by rfl) ⟨811862, by rfl⟩ : syracuseStep 1082483 = 1623725) B1623725
theorem B722035 : Blo 718322 722035 := bstep (se 1 (by rfl) ⟨541526, by rfl⟩ : syracuseStep 722035 = 1083053) B1083053
theorem B722051 : Blo 718322 722051 := bstep (se 1 (by rfl) ⟨541538, by rfl⟩ : syracuseStep 722051 = 1083077) B1083077
theorem B4392077 : Blo 718322 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B1082513 : Blo 718322 1082513 := bstep (se 2 (by rfl) ⟨405942, by rfl⟩ : syracuseStep 1082513 = 811885) B811885
theorem B722067 : Blo 718322 722067 := bstep (se 1 (by rfl) ⟨541550, by rfl⟩ : syracuseStep 722067 = 1083101) B1083101
theorem B1082531 : Blo 718322 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B722083 : Blo 718322 722083 := bstep (se 1 (by rfl) ⟨541562, by rfl⟩ : syracuseStep 722083 = 1083125) B1083125
theorem B722099 : Blo 718322 722099 := bstep (se 1 (by rfl) ⟨541574, by rfl⟩ : syracuseStep 722099 = 1083149) B1083149
theorem B1082561 : Blo 718322 1082561 := bstep (se 2 (by rfl) ⟨405960, by rfl⟩ : syracuseStep 1082561 = 811921) B811921
theorem B722115 : Blo 718322 722115 := bstep (se 1 (by rfl) ⟨541586, by rfl⟩ : syracuseStep 722115 = 1083173) B1083173
theorem B1082579 : Blo 718322 1082579 := bstep (se 1 (by rfl) ⟨811934, by rfl⟩ : syracuseStep 1082579 = 1623869) B1623869
theorem B722131 : Blo 718322 722131 := bstep (se 1 (by rfl) ⟨541598, by rfl⟩ : syracuseStep 722131 = 1083197) B1083197
theorem B722147 : Blo 718322 722147 := bstep (se 1 (by rfl) ⟨541610, by rfl⟩ : syracuseStep 722147 = 1083221) B1083221
theorem B1082609 : Blo 718322 1082609 := bstep (se 2 (by rfl) ⟨405978, by rfl⟩ : syracuseStep 1082609 = 811957) B811957
theorem B722163 : Blo 718322 722163 := bstep (se 1 (by rfl) ⟨541622, by rfl⟩ : syracuseStep 722163 = 1083245) B1083245
theorem B1213697 : Blo 718322 1213697 := bstep (se 2 (by rfl) ⟨455136, by rfl⟩ : syracuseStep 1213697 = 910273) B910273
theorem B1082627 : Blo 718322 1082627 := bstep (se 1 (by rfl) ⟨811970, by rfl⟩ : syracuseStep 1082627 = 1623941) B1623941
theorem B722179 : Blo 718322 722179 := bstep (se 1 (by rfl) ⟨541634, by rfl⟩ : syracuseStep 722179 = 1083269) B1083269
theorem B722195 : Blo 718322 722195 := bstep (se 1 (by rfl) ⟨541646, by rfl⟩ : syracuseStep 722195 = 1083293) B1083293
theorem B1082657 : Blo 718322 1082657 := bstep (se 2 (by rfl) ⟨405996, by rfl⟩ : syracuseStep 1082657 = 811993) B811993
theorem B722211 : Blo 718322 722211 := bstep (se 1 (by rfl) ⟨541658, by rfl⟩ : syracuseStep 722211 = 1083317) B1083317
theorem B1541425 : Blo 718322 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B1082675 : Blo 718322 1082675 := bstep (se 1 (by rfl) ⟨812006, by rfl⟩ : syracuseStep 1082675 = 1624013) B1624013
theorem B722227 : Blo 718322 722227 := bstep (se 1 (by rfl) ⟨541670, by rfl⟩ : syracuseStep 722227 = 1083341) B1083341
theorem B1541443 : Blo 718322 1541443 := bstep (se 1 (by rfl) ⟨1156082, by rfl⟩ : syracuseStep 1541443 = 2312165) B2312165
theorem B722243 : Blo 718322 722243 := bstep (se 1 (by rfl) ⟨541682, by rfl⟩ : syracuseStep 722243 = 1083365) B1083365
theorem B1082705 : Blo 718322 1082705 := bstep (se 2 (by rfl) ⟨406014, by rfl⟩ : syracuseStep 1082705 = 812029) B812029
theorem B722259 : Blo 718322 722259 := bstep (se 1 (by rfl) ⟨541694, by rfl⟩ : syracuseStep 722259 = 1083389) B1083389
theorem B1082723 : Blo 718322 1082723 := bstep (se 1 (by rfl) ⟨812042, by rfl⟩ : syracuseStep 1082723 = 1624085) B1624085
theorem B722275 : Blo 718322 722275 := bstep (se 1 (by rfl) ⟨541706, by rfl⟩ : syracuseStep 722275 = 1083413) B1083413
theorem B722291 : Blo 718322 722291 := bstep (se 1 (by rfl) ⟨541718, by rfl⟩ : syracuseStep 722291 = 1083437) B1083437
theorem B1213825 : Blo 718322 1213825 := bstep (se 2 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 1213825 = 910369) B910369
theorem B1082753 : Blo 718322 1082753 := bstep (se 2 (by rfl) ⟨406032, by rfl⟩ : syracuseStep 1082753 = 812065) B812065
theorem B722307 : Blo 718322 722307 := bstep (se 1 (by rfl) ⟨541730, by rfl⟩ : syracuseStep 722307 = 1083461) B1083461
theorem B33326477 : Blo 718322 33326477 := bstep (se 3 (by rfl) ⟨6248714, by rfl⟩ : syracuseStep 33326477 = 12497429) B12497429
theorem B1082771 : Blo 718322 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B1213859 : Blo 718322 1213859 := bstep (se 1 (by rfl) ⟨910394, by rfl⟩ : syracuseStep 1213859 = 1820789) B1820789
theorem B1082801 : Blo 718322 1082801 := bstep (se 2 (by rfl) ⟨406050, by rfl⟩ : syracuseStep 1082801 = 812101) B812101
theorem B1082819 : Blo 718322 1082819 := bstep (se 1 (by rfl) ⟨812114, by rfl⟩ : syracuseStep 1082819 = 1624229) B1624229
theorem B3900869 : Blo 718322 3900869 := bstep (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) B731413
theorem B1082849 : Blo 718322 1082849 := bstep (se 2 (by rfl) ⟨406068, by rfl⟩ : syracuseStep 1082849 = 812137) B812137
theorem B1082867 : Blo 718322 1082867 := bstep (se 1 (by rfl) ⟨812150, by rfl⟩ : syracuseStep 1082867 = 1624301) B1624301
theorem B2426381 : Blo 718322 2426381 := bstep (se 3 (by rfl) ⟨454946, by rfl⟩ : syracuseStep 2426381 = 909893) B909893
theorem B1082897 : Blo 718322 1082897 := bstep (se 2 (by rfl) ⟨406086, by rfl⟩ : syracuseStep 1082897 = 812173) B812173
theorem B1213987 : Blo 718322 1213987 := bstep (se 1 (by rfl) ⟨910490, by rfl⟩ : syracuseStep 1213987 = 1820981) B1820981
theorem B1082915 : Blo 718322 1082915 := bstep (se 1 (by rfl) ⟨812186, by rfl⟩ : syracuseStep 1082915 = 1624373) B1624373
theorem B1082945 : Blo 718322 1082945 := bstep (se 2 (by rfl) ⟨406104, by rfl⟩ : syracuseStep 1082945 = 812209) B812209
theorem B2426435 : Blo 718322 2426435 := bstep (se 1 (by rfl) ⟨1819826, by rfl⟩ : syracuseStep 2426435 = 3639653) B3639653
theorem B1082963 : Blo 718322 1082963 := bstep (se 1 (by rfl) ⟨812222, by rfl⟩ : syracuseStep 1082963 = 1624445) B1624445
theorem B1082993 : Blo 718322 1082993 := bstep (se 2 (by rfl) ⟨406122, by rfl⟩ : syracuseStep 1082993 = 812245) B812245
theorem B1083011 : Blo 718322 1083011 := bstep (se 1 (by rfl) ⟨812258, by rfl⟩ : syracuseStep 1083011 = 1624517) B1624517
theorem B1083041 : Blo 718322 1083041 := bstep (se 2 (by rfl) ⟨406140, by rfl⟩ : syracuseStep 1083041 = 812281) B812281
theorem B1214129 : Blo 718322 1214129 := bstep (se 2 (by rfl) ⟨455298, by rfl⟩ : syracuseStep 1214129 = 910597) B910597
theorem B1083059 : Blo 718322 1083059 := bstep (se 1 (by rfl) ⟨812294, by rfl⟩ : syracuseStep 1083059 = 1624589) B1624589
theorem B4622021 : Blo 718322 4622021 := bstep (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) B866629
theorem B1083089 : Blo 718322 1083089 := bstep (se 2 (by rfl) ⟨406158, by rfl⟩ : syracuseStep 1083089 = 812317) B812317
theorem B1083107 : Blo 718322 1083107 := bstep (se 1 (by rfl) ⟨812330, by rfl⟩ : syracuseStep 1083107 = 1624661) B1624661
theorem B1083137 : Blo 718322 1083137 := bstep (se 2 (by rfl) ⟨406176, by rfl⟩ : syracuseStep 1083137 = 812353) B812353
theorem B1083155 : Blo 718322 1083155 := bstep (se 1 (by rfl) ⟨812366, by rfl⟩ : syracuseStep 1083155 = 1624733) B1624733
theorem B1214257 : Blo 718322 1214257 := bstep (se 2 (by rfl) ⟨455346, by rfl⟩ : syracuseStep 1214257 = 910693) B910693
theorem B1083185 : Blo 718322 1083185 := bstep (se 2 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 1083185 = 812389) B812389
theorem B1083203 : Blo 718322 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B2426705 : Blo 718322 2426705 := bstep (se 2 (by rfl) ⟨910014, by rfl⟩ : syracuseStep 2426705 = 1820029) B1820029
theorem B1214291 : Blo 718322 1214291 := bstep (se 1 (by rfl) ⟨910718, by rfl⟩ : syracuseStep 1214291 = 1821437) B1821437
theorem B1083233 : Blo 718322 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B9209699 : Blo 718322 9209699 := bstep (se 1 (by rfl) ⟨6907274, by rfl⟩ : syracuseStep 9209699 = 13814549) B13814549
theorem B4097891 : Blo 718322 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B1083251 : Blo 718322 1083251 := bstep (se 1 (by rfl) ⟨812438, by rfl⟩ : syracuseStep 1083251 = 1624877) B1624877
theorem B1083281 : Blo 718322 1083281 := bstep (se 2 (by rfl) ⟨406230, by rfl⟩ : syracuseStep 1083281 = 812461) B812461
theorem B1083299 : Blo 718322 1083299 := bstep (se 1 (by rfl) ⟨812474, by rfl⟩ : syracuseStep 1083299 = 1624949) B1624949
theorem B1083329 : Blo 718322 1083329 := bstep (se 2 (by rfl) ⟨406248, by rfl⟩ : syracuseStep 1083329 = 812497) B812497
theorem B11241413 : Blo 718322 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B1214419 : Blo 718322 1214419 := bstep (se 1 (by rfl) ⟨910814, by rfl⟩ : syracuseStep 1214419 = 1821629) B1821629
theorem B1083347 : Blo 718322 1083347 := bstep (se 1 (by rfl) ⟨812510, by rfl⟩ : syracuseStep 1083347 = 1625021) B1625021
theorem B1083377 : Blo 718322 1083377 := bstep (se 2 (by rfl) ⟨406266, by rfl⟩ : syracuseStep 1083377 = 812533) B812533
theorem B1083395 : Blo 718322 1083395 := bstep (se 1 (by rfl) ⟨812546, by rfl⟩ : syracuseStep 1083395 = 1625093) B1625093
theorem B985105 : Blo 718322 985105 := bstep (se 2 (by rfl) ⟨369414, by rfl⟩ : syracuseStep 985105 = 738829) B738829
theorem B1083425 : Blo 718322 1083425 := bstep (se 2 (by rfl) ⟨406284, by rfl⟩ : syracuseStep 1083425 = 812569) B812569
theorem B1640497 : Blo 718322 1640497 := bstep (se 2 (by rfl) ⟨615186, by rfl⟩ : syracuseStep 1640497 = 1230373) B1230373
theorem B1083443 : Blo 718322 1083443 := bstep (se 1 (by rfl) ⟨812582, by rfl⟩ : syracuseStep 1083443 = 1625165) B1625165
theorem B1083473 : Blo 718322 1083473 := bstep (se 2 (by rfl) ⟨406302, by rfl⟩ : syracuseStep 1083473 = 812605) B812605
theorem B1214561 : Blo 718322 1214561 := bstep (se 2 (by rfl) ⟨455460, by rfl⟩ : syracuseStep 1214561 = 910921) B910921
theorem B9373877 : Blo 718322 9373877 := bstep (se 5 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 9373877 = 878801) B878801
theorem B1214689 : Blo 718322 1214689 := bstep (se 2 (by rfl) ⟨455508, by rfl⟩ : syracuseStep 1214689 = 911017) B911017
theorem B35064035 : Blo 718322 35064035 := bstep (se 1 (by rfl) ⟨26298026, by rfl⟩ : syracuseStep 35064035 = 52596053) B52596053
theorem B1214723 : Blo 718322 1214723 := bstep (se 1 (by rfl) ⟨911042, by rfl⟩ : syracuseStep 1214723 = 1822085) B1822085
theorem B2427245 : Blo 718322 2427245 := bstep (se 3 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 2427245 = 910217) B910217
theorem B1214851 : Blo 718322 1214851 := bstep (se 1 (by rfl) ⟨911138, by rfl⟩ : syracuseStep 1214851 = 1822277) B1822277
theorem B821635 : Blo 718322 821635 := bstep (se 1 (by rfl) ⟨616226, by rfl⟩ : syracuseStep 821635 = 1232453) B1232453
theorem B2427299 : Blo 718322 2427299 := bstep (se 1 (by rfl) ⟨1820474, by rfl⟩ : syracuseStep 2427299 = 3640949) B3640949
theorem B1214993 : Blo 718322 1214993 := bstep (se 2 (by rfl) ⟨455622, by rfl⟩ : syracuseStep 1214993 = 911245) B911245
theorem B4917829 : Blo 718322 4917829 := bstep (se 4 (by rfl) ⟨461046, by rfl⟩ : syracuseStep 4917829 = 922093) B922093
theorem B1215121 : Blo 718322 1215121 := bstep (se 2 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 1215121 = 911341) B911341
theorem B2427569 : Blo 718322 2427569 := bstep (se 2 (by rfl) ⟨910338, by rfl⟩ : syracuseStep 2427569 = 1820677) B1820677
theorem B1215155 : Blo 718322 1215155 := bstep (se 1 (by rfl) ⟨911366, by rfl⟩ : syracuseStep 1215155 = 1822733) B1822733
theorem B1215283 : Blo 718322 1215283 := bstep (se 1 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 1215283 = 1822925) B1822925
theorem B8096611 : Blo 718322 8096611 := bstep (se 1 (by rfl) ⟨6072458, by rfl⟩ : syracuseStep 8096611 = 12144917) B12144917
theorem B1215425 : Blo 718322 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B1215553 : Blo 718322 1215553 := bstep (se 2 (by rfl) ⟨455832, by rfl⟩ : syracuseStep 1215553 = 911665) B911665
theorem B1215587 : Blo 718322 1215587 := bstep (se 1 (by rfl) ⟨911690, by rfl⟩ : syracuseStep 1215587 = 1823381) B1823381
theorem B2428109 : Blo 718322 2428109 := bstep (se 3 (by rfl) ⟨455270, by rfl⟩ : syracuseStep 2428109 = 910541) B910541
theorem B1215715 : Blo 718322 1215715 := bstep (se 1 (by rfl) ⟨911786, by rfl⟩ : syracuseStep 1215715 = 1823573) B1823573
theorem B2428163 : Blo 718322 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B3640625 : Blo 718322 3640625 := bstep (se 2 (by rfl) ⟨1365234, by rfl⟩ : syracuseStep 3640625 = 2730469) B2730469
theorem B1215857 : Blo 718322 1215857 := bstep (se 2 (by rfl) ⟨455946, by rfl⟩ : syracuseStep 1215857 = 911893) B911893
theorem B7409009 : Blo 718322 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B1215985 : Blo 718322 1215985 := bstep (se 2 (by rfl) ⟨455994, by rfl⟩ : syracuseStep 1215985 = 911989) B911989
theorem B2428433 : Blo 718322 2428433 := bstep (se 2 (by rfl) ⟨910662, by rfl⟩ : syracuseStep 2428433 = 1821325) B1821325
theorem B1216019 : Blo 718322 1216019 := bstep (se 1 (by rfl) ⟨912014, by rfl⟩ : syracuseStep 1216019 = 1824029) B1824029
theorem B1216147 : Blo 718322 1216147 := bstep (se 1 (by rfl) ⟨912110, by rfl⟩ : syracuseStep 1216147 = 1824221) B1824221
theorem B1216289 : Blo 718322 1216289 := bstep (se 2 (by rfl) ⟨456108, by rfl⟩ : syracuseStep 1216289 = 912217) B912217
theorem B2920333 : Blo 718322 2920333 := bstep (se 3 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 2920333 = 1095125) B1095125
theorem B1216417 : Blo 718322 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B1216451 : Blo 718322 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B1871843 : Blo 718322 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B2428973 : Blo 718322 2428973 := bstep (se 3 (by rfl) ⟨455432, by rfl⟩ : syracuseStep 2428973 = 910865) B910865
theorem B1216579 : Blo 718322 1216579 := bstep (se 1 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 1216579 = 1824869) B1824869
theorem B2429027 : Blo 718322 2429027 := bstep (se 1 (by rfl) ⟨1821770, by rfl⟩ : syracuseStep 2429027 = 3643541) B3643541
theorem B2461841 : Blo 718322 2461841 := bstep (se 2 (by rfl) ⟨923190, by rfl⟩ : syracuseStep 2461841 = 1846381) B1846381
theorem B1216721 : Blo 718322 1216721 := bstep (se 2 (by rfl) ⟨456270, by rfl⟩ : syracuseStep 1216721 = 912541) B912541
theorem B1216849 : Blo 718322 1216849 := bstep (se 2 (by rfl) ⟨456318, by rfl⟩ : syracuseStep 1216849 = 912637) B912637
theorem B2429297 : Blo 718322 2429297 := bstep (se 2 (by rfl) ⟨910986, by rfl⟩ : syracuseStep 2429297 = 1821973) B1821973
theorem B1216883 : Blo 718322 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B3084749 : Blo 718322 3084749 := bstep (se 3 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 3084749 = 1156781) B1156781
theorem B1217011 : Blo 718322 1217011 := bstep (se 1 (by rfl) ⟨912758, by rfl⟩ : syracuseStep 1217011 = 1825517) B1825517
theorem B1151507 : Blo 718322 1151507 := bstep (se 1 (by rfl) ⟨863630, by rfl⟩ : syracuseStep 1151507 = 1727261) B1727261
theorem B10359409 : Blo 718322 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B1217153 : Blo 718322 1217153 := bstep (se 2 (by rfl) ⟨456432, by rfl⟩ : syracuseStep 1217153 = 912865) B912865
theorem B3642083 : Blo 718322 3642083 := bstep (se 1 (by rfl) ⟨2731562, by rfl⟩ : syracuseStep 3642083 = 5463125) B5463125
theorem B1217281 : Blo 718322 1217281 := bstep (se 2 (by rfl) ⟨456480, by rfl⟩ : syracuseStep 1217281 = 912961) B912961
theorem B1217315 : Blo 718322 1217315 := bstep (se 1 (by rfl) ⟨912986, by rfl⟩ : syracuseStep 1217315 = 1825973) B1825973
theorem B5477219 : Blo 718322 5477219 := bstep (se 1 (by rfl) ⟨4107914, by rfl⟩ : syracuseStep 5477219 = 8215829) B8215829
theorem B2429837 : Blo 718322 2429837 := bstep (se 3 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 2429837 = 911189) B911189
theorem B1217443 : Blo 718322 1217443 := bstep (se 1 (by rfl) ⟨913082, by rfl⟩ : syracuseStep 1217443 = 1826165) B1826165
theorem B2429891 : Blo 718322 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B922627 : Blo 718322 922627 := bstep (se 1 (by rfl) ⟨691970, by rfl⟩ : syracuseStep 922627 = 1383941) B1383941
theorem B1217585 : Blo 718322 1217585 := bstep (se 2 (by rfl) ⟨456594, by rfl⟩ : syracuseStep 1217585 = 913189) B913189
theorem B1315921 : Blo 718322 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B1217713 : Blo 718322 1217713 := bstep (se 2 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 1217713 = 913285) B913285
theorem B2430161 : Blo 718322 2430161 := bstep (se 2 (by rfl) ⟨911310, by rfl⟩ : syracuseStep 2430161 = 1822621) B1822621
theorem B1217747 : Blo 718322 1217747 := bstep (se 1 (by rfl) ⟨913310, by rfl⟩ : syracuseStep 1217747 = 1826621) B1826621
theorem B1217875 : Blo 718322 1217875 := bstep (se 1 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 1217875 = 1826813) B1826813
theorem B1152353 : Blo 718322 1152353 := bstep (se 2 (by rfl) ⟨432132, by rfl⟩ : syracuseStep 1152353 = 864265) B864265
theorem B1218017 : Blo 718322 1218017 := bstep (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) B913513
theorem B3642893 : Blo 718322 3642893 := bstep (se 3 (by rfl) ⟨683042, by rfl⟩ : syracuseStep 3642893 = 1366085) B1366085
theorem B1218145 : Blo 718322 1218145 := bstep (se 2 (by rfl) ⟨456804, by rfl⟩ : syracuseStep 1218145 = 913609) B913609
theorem B1218179 : Blo 718322 1218179 := bstep (se 1 (by rfl) ⟨913634, by rfl⟩ : syracuseStep 1218179 = 1827269) B1827269
theorem B2430701 : Blo 718322 2430701 := bstep (se 3 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 2430701 = 911513) B911513
theorem B1218307 : Blo 718322 1218307 := bstep (se 1 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 1218307 = 1827461) B1827461
theorem B3610403 : Blo 718322 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B2430755 : Blo 718322 2430755 := bstep (se 1 (by rfl) ⟨1823066, by rfl⟩ : syracuseStep 2430755 = 3646133) B3646133
theorem B1218449 : Blo 718322 1218449 := bstep (se 2 (by rfl) ⟨456918, by rfl⟩ : syracuseStep 1218449 = 913837) B913837
theorem B1218577 : Blo 718322 1218577 := bstep (se 2 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 1218577 = 913933) B913933
theorem B2431025 : Blo 718322 2431025 := bstep (se 2 (by rfl) ⟨911634, by rfl⟩ : syracuseStep 2431025 = 1823269) B1823269
theorem B1218611 : Blo 718322 1218611 := bstep (se 1 (by rfl) ⟨913958, by rfl⟩ : syracuseStep 1218611 = 1827917) B1827917
theorem B1153091 : Blo 718322 1153091 := bstep (se 1 (by rfl) ⟨864818, by rfl⟩ : syracuseStep 1153091 = 1729637) B1729637
theorem B1218739 : Blo 718322 1218739 := bstep (se 1 (by rfl) ⟨914054, by rfl⟩ : syracuseStep 1218739 = 1828109) B1828109
theorem B1218881 : Blo 718322 1218881 := bstep (se 2 (by rfl) ⟨457080, by rfl⟩ : syracuseStep 1218881 = 914161) B914161
theorem B2923057 : Blo 718322 2923057 := bstep (se 2 (by rfl) ⟨1096146, by rfl⟩ : syracuseStep 2923057 = 2192293) B2192293
theorem B2595377 : Blo 718322 2595377 := bstep (se 2 (by rfl) ⟨973266, by rfl⟩ : syracuseStep 2595377 = 1946533) B1946533
theorem B2431565 : Blo 718322 2431565 := bstep (se 3 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 2431565 = 911837) B911837
theorem B2431619 : Blo 718322 2431619 := bstep (se 1 (by rfl) ⟨1823714, by rfl⟩ : syracuseStep 2431619 = 3647429) B3647429
theorem B2595491 : Blo 718322 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B2431889 : Blo 718322 2431889 := bstep (se 2 (by rfl) ⟨911958, by rfl⟩ : syracuseStep 2431889 = 1823917) B1823917
theorem B9247729 : Blo 718322 9247729 := bstep (se 2 (by rfl) ⟨3467898, by rfl⟩ : syracuseStep 9247729 = 6935797) B6935797
theorem B1154083 : Blo 718322 1154083 := bstep (se 1 (by rfl) ⟨865562, by rfl⟩ : syracuseStep 1154083 = 1731125) B1731125
theorem B2956429 : Blo 718322 2956429 := bstep (se 3 (by rfl) ⟨554330, by rfl⟩ : syracuseStep 2956429 = 1108661) B1108661
theorem B1154321 : Blo 718322 1154321 := bstep (se 2 (by rfl) ⟨432870, by rfl⟩ : syracuseStep 1154321 = 865741) B865741
theorem B1023283 : Blo 718322 1023283 := bstep (se 1 (by rfl) ⟨767462, by rfl⟩ : syracuseStep 1023283 = 1534925) B1534925
theorem B2497873 : Blo 718322 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B2432429 : Blo 718322 2432429 := bstep (se 3 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 2432429 = 912161) B912161
theorem B1154531 : Blo 718322 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B2432483 : Blo 718322 2432483 := bstep (se 1 (by rfl) ⟨1824362, by rfl⟩ : syracuseStep 2432483 = 3648725) B3648725
theorem B1384049 : Blo 718322 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B1023619 : Blo 718322 1023619 := bstep (se 1 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 1023619 = 1535429) B1535429
theorem B2432753 : Blo 718322 2432753 := bstep (se 2 (by rfl) ⟨912282, by rfl⟩ : syracuseStep 2432753 = 1824565) B1824565
theorem B728899 : Blo 718322 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B6168433 : Blo 718322 6168433 := bstep (se 2 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 6168433 = 4626325) B4626325
theorem B2727857 : Blo 718322 2727857 := bstep (se 2 (by rfl) ⟨1022946, by rfl⟩ : syracuseStep 2727857 = 2045893) B2045893
theorem B1024177 : Blo 718322 1024177 := bstep (se 2 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 1024177 = 768133) B768133
theorem B1024211 : Blo 718322 1024211 := bstep (se 1 (by rfl) ⟨768158, by rfl⟩ : syracuseStep 1024211 = 1536317) B1536317
theorem B1155313 : Blo 718322 1155313 := bstep (se 2 (by rfl) ⟨433242, by rfl⟩ : syracuseStep 1155313 = 866485) B866485
theorem B2433293 : Blo 718322 2433293 := bstep (se 3 (by rfl) ⟨456242, by rfl⟩ : syracuseStep 2433293 = 912485) B912485
theorem B2433347 : Blo 718322 2433347 := bstep (se 1 (by rfl) ⟨1825010, by rfl⟩ : syracuseStep 2433347 = 3650021) B3650021
theorem B3645809 : Blo 718322 3645809 := bstep (se 2 (by rfl) ⟨1367178, by rfl⟩ : syracuseStep 3645809 = 2734357) B2734357
theorem B2728525 : Blo 718322 2728525 := bstep (se 3 (by rfl) ⟨511598, by rfl⟩ : syracuseStep 2728525 = 1023197) B1023197
theorem B2433617 : Blo 718322 2433617 := bstep (se 2 (by rfl) ⟨912606, by rfl⟩ : syracuseStep 2433617 = 1825213) B1825213
theorem B1024769 : Blo 718322 1024769 := bstep (se 2 (by rfl) ⟨384288, by rfl⟩ : syracuseStep 1024769 = 768577) B768577
theorem B1024849 : Blo 718322 1024849 := bstep (se 2 (by rfl) ⟨384318, by rfl⟩ : syracuseStep 1024849 = 768637) B768637
theorem B1647587 : Blo 718322 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B1156115 : Blo 718322 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B3941453 : Blo 718322 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B2434157 : Blo 718322 2434157 := bstep (se 3 (by rfl) ⟨456404, by rfl⟩ : syracuseStep 2434157 = 912809) B912809
theorem B2303117 : Blo 718322 2303117 := bstep (se 3 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 2303117 = 863669) B863669
theorem B2434211 : Blo 718322 2434211 := bstep (se 1 (by rfl) ⟨1825658, by rfl⟩ : syracuseStep 2434211 = 3651317) B3651317
theorem B2467043 : Blo 718322 2467043 := bstep (se 1 (by rfl) ⟨1850282, by rfl⟩ : syracuseStep 2467043 = 3700565) B3700565
theorem B2303245 : Blo 718322 2303245 := bstep (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) B863717
theorem B7808309 : Blo 718322 7808309 := bstep (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) B732029
theorem B2729315 : Blo 718322 2729315 := bstep (se 1 (by rfl) ⟨2046986, by rfl⟩ : syracuseStep 2729315 = 4093973) B4093973
theorem B12166541 : Blo 718322 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B2434481 : Blo 718322 2434481 := bstep (se 2 (by rfl) ⟨912930, by rfl⟩ : syracuseStep 2434481 = 1825861) B1825861
theorem B1156627 : Blo 718322 1156627 := bstep (se 1 (by rfl) ⟨867470, by rfl⟩ : syracuseStep 1156627 = 1734941) B1734941
theorem B1025635 : Blo 718322 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B3647267 : Blo 718322 3647267 := bstep (se 1 (by rfl) ⟨2735450, by rfl⟩ : syracuseStep 3647267 = 5470901) B5470901
theorem B2598733 : Blo 718322 2598733 := bstep (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) B974525
theorem B2435021 : Blo 718322 2435021 := bstep (se 3 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 2435021 = 913133) B913133
theorem B2729969 : Blo 718322 2729969 := bstep (se 2 (by rfl) ⟨1023738, by rfl⟩ : syracuseStep 2729969 = 2047477) B2047477
theorem B1845233 : Blo 718322 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B2435075 : Blo 718322 2435075 := bstep (se 1 (by rfl) ⟨1826306, by rfl⟩ : syracuseStep 2435075 = 3652613) B3652613
theorem B1026113 : Blo 718322 1026113 := bstep (se 2 (by rfl) ⟨384792, by rfl⟩ : syracuseStep 1026113 = 769585) B769585
theorem B5482565 : Blo 718322 5482565 := bstep (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) B1027981
theorem B1026227 : Blo 718322 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B1026307 : Blo 718322 1026307 := bstep (se 1 (by rfl) ⟨769730, by rfl⟩ : syracuseStep 1026307 = 1539461) B1539461
theorem B2435345 : Blo 718322 2435345 := bstep (se 2 (by rfl) ⟨913254, by rfl⟩ : syracuseStep 2435345 = 1826509) B1826509
theorem B2074961 : Blo 718322 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B1616273 : Blo 718322 1616273 := bstep (se 2 (by rfl) ⟨606102, by rfl⟩ : syracuseStep 1616273 = 1212205) B1212205
theorem B731539 : Blo 718322 731539 := bstep (se 1 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 731539 = 1097309) B1097309
theorem B1616291 : Blo 718322 1616291 := bstep (se 1 (by rfl) ⟨1212218, by rfl⟩ : syracuseStep 1616291 = 2424437) B2424437
theorem B1878563 : Blo 718322 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B4106821 : Blo 718322 4106821 := bstep (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) B770029
theorem B3648077 : Blo 718322 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B1616561 : Blo 718322 1616561 := bstep (se 2 (by rfl) ⟨606210, by rfl⟩ : syracuseStep 1616561 = 1212421) B1212421
theorem B1616579 : Blo 718322 1616579 := bstep (se 1 (by rfl) ⟨1212434, by rfl⟩ : syracuseStep 1616579 = 2424869) B2424869
theorem B863011 : Blo 718322 863011 := bstep (se 1 (by rfl) ⟨647258, by rfl⟩ : syracuseStep 863011 = 1294517) B1294517
theorem B2435885 : Blo 718322 2435885 := bstep (se 3 (by rfl) ⟨456728, by rfl⟩ : syracuseStep 2435885 = 913457) B913457
theorem B1026865 : Blo 718322 1026865 := bstep (se 2 (by rfl) ⟨385074, by rfl⟩ : syracuseStep 1026865 = 770149) B770149
theorem B2435939 : Blo 718322 2435939 := bstep (se 1 (by rfl) ⟨1826954, by rfl⟩ : syracuseStep 2435939 = 3653909) B3653909
theorem B1616849 : Blo 718322 1616849 := bstep (se 2 (by rfl) ⟨606318, by rfl⟩ : syracuseStep 1616849 = 1212637) B1212637
theorem B1616867 : Blo 718322 1616867 := bstep (se 1 (by rfl) ⟨1212650, by rfl⟩ : syracuseStep 1616867 = 2425301) B2425301
theorem B2305091 : Blo 718322 2305091 := bstep (se 1 (by rfl) ⟨1728818, by rfl⟩ : syracuseStep 2305091 = 3457637) B3457637
theorem B2337869 : Blo 718322 2337869 := bstep (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) B876701
theorem B2436209 : Blo 718322 2436209 := bstep (se 2 (by rfl) ⟨913578, by rfl⟩ : syracuseStep 2436209 = 1827157) B1827157
theorem B1944749 : Blo 718322 1944749 := bstep (se 3 (by rfl) ⟨364640, by rfl⟩ : syracuseStep 1944749 = 729281) B729281
theorem B2305219 : Blo 718322 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B1617137 : Blo 718322 1617137 := bstep (se 2 (by rfl) ⟨606426, by rfl⟩ : syracuseStep 1617137 = 1212853) B1212853
theorem B1617155 : Blo 718322 1617155 := bstep (se 1 (by rfl) ⟨1212866, by rfl⟩ : syracuseStep 1617155 = 2425733) B2425733
theorem B2305361 : Blo 718322 2305361 := bstep (se 2 (by rfl) ⟨864510, by rfl⟩ : syracuseStep 2305361 = 1729021) B1729021
theorem B2731427 : Blo 718322 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B2731441 : Blo 718322 2731441 := bstep (se 2 (by rfl) ⟨1024290, by rfl⟩ : syracuseStep 2731441 = 2048581) B2048581
theorem B2305475 : Blo 718322 2305475 := bstep (se 1 (by rfl) ⟨1729106, by rfl⟩ : syracuseStep 2305475 = 3458213) B3458213
theorem B1027571 : Blo 718322 1027571 := bstep (se 1 (by rfl) ⟨770678, by rfl⟩ : syracuseStep 1027571 = 1541357) B1541357
theorem B1617425 : Blo 718322 1617425 := bstep (se 2 (by rfl) ⟨606534, by rfl⟩ : syracuseStep 1617425 = 1213069) B1213069
theorem B1617443 : Blo 718322 1617443 := bstep (se 1 (by rfl) ⟨1213082, by rfl⟩ : syracuseStep 1617443 = 2426165) B2426165
theorem B15773237 : Blo 718322 15773237 := bstep (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) B1478741
theorem B2436749 : Blo 718322 2436749 := bstep (se 3 (by rfl) ⟨456890, by rfl⟩ : syracuseStep 2436749 = 913781) B913781
theorem B2436803 : Blo 718322 2436803 := bstep (se 1 (by rfl) ⟨1827602, by rfl⟩ : syracuseStep 2436803 = 3655205) B3655205
theorem B1617713 : Blo 718322 1617713 := bstep (se 2 (by rfl) ⟨606642, by rfl⟩ : syracuseStep 1617713 = 1213285) B1213285
theorem B1617731 : Blo 718322 1617731 := bstep (se 1 (by rfl) ⟨1213298, by rfl⟩ : syracuseStep 1617731 = 2426597) B2426597
theorem B2600867 : Blo 718322 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B2437073 : Blo 718322 2437073 := bstep (se 2 (by rfl) ⟨913902, by rfl⟩ : syracuseStep 2437073 = 1827805) B1827805
theorem B1618001 : Blo 718322 1618001 := bstep (se 2 (by rfl) ⟨606750, by rfl⟩ : syracuseStep 1618001 = 1213501) B1213501
theorem B1618019 : Blo 718322 1618019 := bstep (se 1 (by rfl) ⟨1213514, by rfl⟩ : syracuseStep 1618019 = 2427029) B2427029
theorem B1028209 : Blo 718322 1028209 := bstep (se 2 (by rfl) ⟨385578, by rfl⟩ : syracuseStep 1028209 = 771157) B771157
theorem B9253061 : Blo 718322 9253061 := bstep (se 4 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 9253061 = 1734949) B1734949
theorem B1028323 : Blo 718322 1028323 := bstep (se 1 (by rfl) ⟨771242, by rfl⟩ : syracuseStep 1028323 = 1542485) B1542485
theorem B8335685 : Blo 718322 8335685 := bstep (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) B1562941
theorem B1945937 : Blo 718322 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B1618289 : Blo 718322 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B1618307 : Blo 718322 1618307 := bstep (se 1 (by rfl) ⟨1213730, by rfl⟩ : syracuseStep 1618307 = 2427461) B2427461
theorem B5190085 : Blo 718322 5190085 := bstep (se 4 (by rfl) ⟨486570, by rfl⟩ : syracuseStep 5190085 = 973141) B973141
theorem B2765261 : Blo 718322 2765261 := bstep (se 3 (by rfl) ⟨518486, by rfl⟩ : syracuseStep 2765261 = 1036973) B1036973
theorem B2437613 : Blo 718322 2437613 := bstep (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) B914105
theorem B4108805 : Blo 718322 4108805 := bstep (se 4 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 4108805 = 770401) B770401
theorem B864803 : Blo 718322 864803 := bstep (se 1 (by rfl) ⟨648602, by rfl⟩ : syracuseStep 864803 = 1297205) B1297205
theorem B2437667 : Blo 718322 2437667 := bstep (se 1 (by rfl) ⟨1828250, by rfl⟩ : syracuseStep 2437667 = 3656501) B3656501
theorem B1094195 : Blo 718322 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B1618577 : Blo 718322 1618577 := bstep (se 2 (by rfl) ⟨606966, by rfl⟩ : syracuseStep 1618577 = 1213933) B1213933
theorem B1618595 : Blo 718322 1618595 := bstep (se 1 (by rfl) ⟨1213946, by rfl⟩ : syracuseStep 1618595 = 2427893) B2427893
theorem B2765539 : Blo 718322 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B2732899 : Blo 718322 2732899 := bstep (se 1 (by rfl) ⟨2049674, by rfl⟩ : syracuseStep 2732899 = 4099349) B4099349
theorem B1618865 : Blo 718322 1618865 := bstep (se 2 (by rfl) ⟨607074, by rfl⟩ : syracuseStep 1618865 = 1214149) B1214149
theorem B1618883 : Blo 718322 1618883 := bstep (se 1 (by rfl) ⟨1214162, by rfl⟩ : syracuseStep 1618883 = 2428325) B2428325
theorem B2307217 : Blo 718322 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B1094833 : Blo 718322 1094833 := bstep (se 2 (by rfl) ⟨410562, by rfl⟩ : syracuseStep 1094833 = 821125) B821125
theorem B1619153 : Blo 718322 1619153 := bstep (se 2 (by rfl) ⟨607182, by rfl⟩ : syracuseStep 1619153 = 1214365) B1214365
theorem B1619171 : Blo 718322 1619171 := bstep (se 1 (by rfl) ⟨1214378, by rfl⟩ : syracuseStep 1619171 = 2428757) B2428757
theorem B1684739 : Blo 718322 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B3650993 : Blo 718322 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B1619441 : Blo 718322 1619441 := bstep (se 2 (by rfl) ⟨607290, by rfl⟩ : syracuseStep 1619441 = 1214581) B1214581
theorem B1619459 : Blo 718322 1619459 := bstep (se 1 (by rfl) ⟨1214594, by rfl⟩ : syracuseStep 1619459 = 2429189) B2429189
theorem B1947149 : Blo 718322 1947149 := bstep (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) B730181
theorem B767603 : Blo 718322 767603 := bstep (se 1 (by rfl) ⟨575702, by rfl⟩ : syracuseStep 767603 = 1151405) B1151405
theorem B1619729 : Blo 718322 1619729 := bstep (se 2 (by rfl) ⟨607398, by rfl⟩ : syracuseStep 1619729 = 1214797) B1214797
theorem B1619747 : Blo 718322 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B2045837 : Blo 718322 2045837 := bstep (se 3 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 2045837 = 767189) B767189
theorem B1620017 : Blo 718322 1620017 := bstep (se 2 (by rfl) ⟨607506, by rfl⟩ : syracuseStep 1620017 = 1215013) B1215013
theorem B2046019 : Blo 718322 2046019 := bstep (se 1 (by rfl) ⟨1534514, by rfl⟩ : syracuseStep 2046019 = 3069029) B3069029
theorem B1620035 : Blo 718322 1620035 := bstep (se 1 (by rfl) ⟨1215026, by rfl⟩ : syracuseStep 1620035 = 2430053) B2430053
theorem B2078797 : Blo 718322 2078797 := bstep (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) B779549
theorem B2308333 : Blo 718322 2308333 := bstep (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) B865625
theorem B1096001 : Blo 718322 1096001 := bstep (se 2 (by rfl) ⟨411000, by rfl⟩ : syracuseStep 1096001 = 822001) B822001
theorem B1620305 : Blo 718322 1620305 := bstep (se 2 (by rfl) ⟨607614, by rfl⟩ : syracuseStep 1620305 = 1215229) B1215229
theorem B1620323 : Blo 718322 1620323 := bstep (se 1 (by rfl) ⟨1215242, by rfl⟩ : syracuseStep 1620323 = 2430485) B2430485
theorem B2046509 : Blo 718322 2046509 := bstep (se 3 (by rfl) ⟨383720, by rfl⟩ : syracuseStep 2046509 = 767441) B767441
theorem B1620593 : Blo 718322 1620593 := bstep (se 2 (by rfl) ⟨607722, by rfl⟩ : syracuseStep 1620593 = 1215445) B1215445
theorem B1620611 : Blo 718322 1620611 := bstep (se 1 (by rfl) ⟨1215458, by rfl⟩ : syracuseStep 1620611 = 2430917) B2430917
theorem B1096337 : Blo 718322 1096337 := bstep (se 2 (by rfl) ⟨411126, by rfl⟩ : syracuseStep 1096337 = 822253) B822253
theorem B3652451 : Blo 718322 3652451 := bstep (se 1 (by rfl) ⟨2739338, by rfl⟩ : syracuseStep 3652451 = 5478677) B5478677
theorem B1620881 : Blo 718322 1620881 := bstep (se 2 (by rfl) ⟨607830, by rfl⟩ : syracuseStep 1620881 = 1215661) B1215661
theorem B1620899 : Blo 718322 1620899 := bstep (se 1 (by rfl) ⟨1215674, by rfl⟩ : syracuseStep 1620899 = 2431349) B2431349
theorem B4602851 : Blo 718322 4602851 := bstep (se 1 (by rfl) ⟨3452138, by rfl⟩ : syracuseStep 4602851 = 6904277) B6904277
theorem B2735117 : Blo 718322 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B2309165 : Blo 718322 2309165 := bstep (se 3 (by rfl) ⟨432968, by rfl⟩ : syracuseStep 2309165 = 865937) B865937
theorem B769171 : Blo 718322 769171 := bstep (se 1 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 769171 = 1153757) B1153757
theorem B1621169 : Blo 718322 1621169 := bstep (se 2 (by rfl) ⟨607938, by rfl⟩ : syracuseStep 1621169 = 1215877) B1215877
theorem B1621187 : Blo 718322 1621187 := bstep (se 1 (by rfl) ⟨1215890, by rfl⟩ : syracuseStep 1621187 = 2431781) B2431781
theorem B867667 : Blo 718322 867667 := bstep (se 1 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 867667 = 1301501) B1301501
theorem B867715 : Blo 718322 867715 := bstep (se 1 (by rfl) ⟨650786, by rfl⟩ : syracuseStep 867715 = 1301573) B1301573
theorem B5848517 : Blo 718322 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B1621457 : Blo 718322 1621457 := bstep (se 2 (by rfl) ⟨608046, by rfl⟩ : syracuseStep 1621457 = 1216093) B1216093
theorem B1621475 : Blo 718322 1621475 := bstep (se 1 (by rfl) ⟨1216106, by rfl⟩ : syracuseStep 1621475 = 2432213) B2432213
theorem B2113091 : Blo 718322 2113091 := bstep (se 1 (by rfl) ⟨1584818, by rfl⟩ : syracuseStep 2113091 = 3169637) B3169637
theorem B769619 : Blo 718322 769619 := bstep (se 1 (by rfl) ⟨577214, by rfl⟩ : syracuseStep 769619 = 1154429) B1154429
theorem B3653261 : Blo 718322 3653261 := bstep (se 3 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 3653261 = 1369973) B1369973
theorem B2047693 : Blo 718322 2047693 := bstep (se 3 (by rfl) ⟨383942, by rfl⟩ : syracuseStep 2047693 = 767885) B767885
theorem B1621745 : Blo 718322 1621745 := bstep (se 2 (by rfl) ⟨608154, by rfl⟩ : syracuseStep 1621745 = 1216309) B1216309
theorem B1621763 : Blo 718322 1621763 := bstep (se 1 (by rfl) ⟨1216322, by rfl⟩ : syracuseStep 1621763 = 2432645) B2432645
theorem B1752931 : Blo 718322 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B1228787 : Blo 718322 1228787 := bstep (se 1 (by rfl) ⟨921590, by rfl⟩ : syracuseStep 1228787 = 1843181) B1843181
theorem B1622033 : Blo 718322 1622033 := bstep (se 2 (by rfl) ⟨608262, by rfl⟩ : syracuseStep 1622033 = 1216525) B1216525
theorem B1622051 : Blo 718322 1622051 := bstep (se 1 (by rfl) ⟨1216538, by rfl⟩ : syracuseStep 1622051 = 2433077) B2433077
theorem B4112653 : Blo 718322 4112653 := bstep (se 3 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 4112653 = 1542245) B1542245
theorem B1229089 : Blo 718322 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B1622321 : Blo 718322 1622321 := bstep (se 2 (by rfl) ⟨608370, by rfl⟩ : syracuseStep 1622321 = 1216741) B1216741
theorem B1950001 : Blo 718322 1950001 := bstep (se 2 (by rfl) ⟨731250, by rfl⟩ : syracuseStep 1950001 = 1462501) B1462501
theorem B1622339 : Blo 718322 1622339 := bstep (se 1 (by rfl) ⟨1216754, by rfl⟩ : syracuseStep 1622339 = 2433509) B2433509
theorem B1458577 : Blo 718322 1458577 := bstep (se 2 (by rfl) ⟨546966, by rfl⟩ : syracuseStep 1458577 = 1093933) B1093933
theorem B1819057 : Blo 718322 1819057 := bstep (se 2 (by rfl) ⟨682146, by rfl⟩ : syracuseStep 1819057 = 1364293) B1364293
theorem B1622609 : Blo 718322 1622609 := bstep (se 2 (by rfl) ⟨608478, by rfl⟩ : syracuseStep 1622609 = 1216957) B1216957
theorem B1622627 : Blo 718322 1622627 := bstep (se 1 (by rfl) ⟨1216970, by rfl⟩ : syracuseStep 1622627 = 2433941) B2433941
theorem B1819331 : Blo 718322 1819331 := bstep (se 1 (by rfl) ⟨1364498, by rfl⟩ : syracuseStep 1819331 = 2728997) B2728997
theorem B2048753 : Blo 718322 2048753 := bstep (se 2 (by rfl) ⟨768282, by rfl⟩ : syracuseStep 2048753 = 1536565) B1536565
theorem B2081521 : Blo 718322 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B2081603 : Blo 718322 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B1622897 : Blo 718322 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B1819523 : Blo 718322 1819523 := bstep (se 1 (by rfl) ⟨1364642, by rfl⟩ : syracuseStep 1819523 = 2729285) B2729285
theorem B1622915 : Blo 718322 1622915 := bstep (se 1 (by rfl) ⟨1217186, by rfl⟩ : syracuseStep 1622915 = 2434373) B2434373
theorem B770995 : Blo 718322 770995 := bstep (se 1 (by rfl) ⟨578246, by rfl⟩ : syracuseStep 770995 = 1156493) B1156493
theorem B2311267 : Blo 718322 2311267 := bstep (se 1 (by rfl) ⟨1733450, by rfl⟩ : syracuseStep 2311267 = 3466901) B3466901
theorem B1623185 : Blo 718322 1623185 := bstep (se 2 (by rfl) ⟨608694, by rfl⟩ : syracuseStep 1623185 = 1217389) B1217389
theorem B1623203 : Blo 718322 1623203 := bstep (se 1 (by rfl) ⟨1217402, by rfl⟩ : syracuseStep 1623203 = 2434805) B2434805
theorem B2311409 : Blo 718322 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B1000721 : Blo 718322 1000721 := bstep (se 2 (by rfl) ⟨375270, by rfl⟩ : syracuseStep 1000721 = 750541) B750541
theorem B5457293 : Blo 718322 5457293 := bstep (se 3 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 5457293 = 2046485) B2046485
theorem B2049425 : Blo 718322 2049425 := bstep (se 2 (by rfl) ⟨768534, by rfl⟩ : syracuseStep 2049425 = 1537069) B1537069
theorem B1623473 : Blo 718322 1623473 := bstep (se 2 (by rfl) ⟨608802, by rfl⟩ : syracuseStep 1623473 = 1217605) B1217605
theorem B1623491 : Blo 718322 1623491 := bstep (se 1 (by rfl) ⟨1217618, by rfl⟩ : syracuseStep 1623491 = 2435237) B2435237
theorem B1295843 : Blo 718322 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B1459729 : Blo 718322 1459729 := bstep (se 2 (by rfl) ⟨547398, by rfl⟩ : syracuseStep 1459729 = 1094797) B1094797
theorem B1623761 : Blo 718322 1623761 := bstep (se 2 (by rfl) ⟨608910, by rfl⟩ : syracuseStep 1623761 = 1217821) B1217821
theorem B1623779 : Blo 718322 1623779 := bstep (se 1 (by rfl) ⟨1217834, by rfl⟩ : syracuseStep 1623779 = 2435669) B2435669
theorem B1820465 : Blo 718322 1820465 := bstep (se 2 (by rfl) ⟨682674, by rfl⟩ : syracuseStep 1820465 = 1365349) B1365349
theorem B14042933 : Blo 718322 14042933 := bstep (se 5 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 14042933 = 1316525) B1316525
theorem B1820515 : Blo 718322 1820515 := bstep (se 1 (by rfl) ⟨1365386, by rfl⟩ : syracuseStep 1820515 = 2730773) B2730773
theorem B2738033 : Blo 718322 2738033 := bstep (se 2 (by rfl) ⟨1026762, by rfl⟩ : syracuseStep 2738033 = 2053525) B2053525
theorem B1820657 : Blo 718322 1820657 := bstep (se 2 (by rfl) ⟨682746, by rfl⟩ : syracuseStep 1820657 = 1365493) B1365493
theorem B1624049 : Blo 718322 1624049 := bstep (se 2 (by rfl) ⟨609018, by rfl⟩ : syracuseStep 1624049 = 1218037) B1218037
theorem B1624067 : Blo 718322 1624067 := bstep (se 1 (by rfl) ⟨1218050, by rfl⟩ : syracuseStep 1624067 = 2436101) B2436101
theorem B2050211 : Blo 718322 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B4442339 : Blo 718322 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B1624337 : Blo 718322 1624337 := bstep (se 2 (by rfl) ⟨609126, by rfl⟩ : syracuseStep 1624337 = 1218253) B1218253
theorem B1624355 : Blo 718322 1624355 := bstep (se 1 (by rfl) ⟨1218266, by rfl⟩ : syracuseStep 1624355 = 2436533) B2436533
theorem B2050541 : Blo 718322 2050541 := bstep (se 3 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 2050541 = 768953) B768953
theorem B3656177 : Blo 718322 3656177 := bstep (se 2 (by rfl) ⟨1371066, by rfl⟩ : syracuseStep 3656177 = 2742133) B2742133
theorem B2050609 : Blo 718322 2050609 := bstep (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) B1537957
theorem B1624625 : Blo 718322 1624625 := bstep (se 2 (by rfl) ⟨609234, by rfl⟩ : syracuseStep 1624625 = 1218469) B1218469
theorem B1624643 : Blo 718322 1624643 := bstep (se 1 (by rfl) ⟨1218482, by rfl⟩ : syracuseStep 1624643 = 2436965) B2436965
theorem B4606541 : Blo 718322 4606541 := bstep (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) B1727453
theorem B1231537 : Blo 718322 1231537 := bstep (se 2 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 1231537 = 923653) B923653
theorem B1755857 : Blo 718322 1755857 := bstep (se 2 (by rfl) ⟨658446, by rfl⟩ : syracuseStep 1755857 = 1316893) B1316893
theorem B5851889 : Blo 718322 5851889 := bstep (se 2 (by rfl) ⟨2194458, by rfl⟩ : syracuseStep 5851889 = 4388917) B4388917
theorem B2050883 : Blo 718322 2050883 := bstep (se 1 (by rfl) ⟨1538162, by rfl⟩ : syracuseStep 2050883 = 3076325) B3076325
theorem B1624913 : Blo 718322 1624913 := bstep (se 2 (by rfl) ⟨609342, by rfl⟩ : syracuseStep 1624913 = 1218685) B1218685
theorem B1624931 : Blo 718322 1624931 := bstep (se 1 (by rfl) ⟨1218698, by rfl⟩ : syracuseStep 1624931 = 2437397) B2437397
theorem B1821649 : Blo 718322 1821649 := bstep (se 2 (by rfl) ⟨683118, by rfl⟩ : syracuseStep 1821649 = 1366237) B1366237
theorem B1625201 : Blo 718322 1625201 := bstep (se 2 (by rfl) ⟨609450, by rfl⟩ : syracuseStep 1625201 = 1218901) B1218901
theorem B1625219 : Blo 718322 1625219 := bstep (se 1 (by rfl) ⟨1218914, by rfl⟩ : syracuseStep 1625219 = 2437829) B2437829
theorem B1821923 : Blo 718322 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B1461521 : Blo 718322 1461521 := bstep (se 2 (by rfl) ⟨548070, by rfl⟩ : syracuseStep 1461521 = 1096141) B1096141
theorem B2739491 : Blo 718322 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B3689891 : Blo 718322 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B1822115 : Blo 718322 1822115 := bstep (se 1 (by rfl) ⟨1366586, by rfl⟩ : syracuseStep 1822115 = 2733173) B2733173
theorem B2313805 : Blo 718322 2313805 := bstep (se 3 (by rfl) ⟨433838, by rfl⟩ : syracuseStep 2313805 = 867677) B867677
theorem B2051725 : Blo 718322 2051725 := bstep (se 3 (by rfl) ⟨384698, by rfl⟩ : syracuseStep 2051725 = 769397) B769397
theorem B1232563 : Blo 718322 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B7786165 : Blo 718322 7786165 := bstep (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) B729953
theorem B2051885 : Blo 718322 2051885 := bstep (se 3 (by rfl) ⟨384728, by rfl⟩ : syracuseStep 2051885 = 769457) B769457
theorem B1298243 : Blo 718322 1298243 := bstep (se 1 (by rfl) ⟨973682, by rfl⟩ : syracuseStep 1298243 = 1947365) B1947365
theorem B2052067 : Blo 718322 2052067 := bstep (se 1 (by rfl) ⟨1539050, by rfl⟩ : syracuseStep 2052067 = 3078101) B3078101
theorem B1364035 : Blo 718322 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B970849 : Blo 718322 970849 := bstep (se 2 (by rfl) ⟨364068, by rfl⟩ : syracuseStep 970849 = 728137) B728137
theorem B6312077 : Blo 718322 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B1364195 : Blo 718322 1364195 := bstep (se 1 (by rfl) ⟨1023146, by rfl⟩ : syracuseStep 1364195 = 2046293) B2046293
theorem B5460209 : Blo 718322 5460209 := bstep (se 2 (by rfl) ⟨2047578, by rfl⟩ : syracuseStep 5460209 = 4095157) B4095157
theorem B2740493 : Blo 718322 2740493 := bstep (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) B1027685
theorem B1823057 : Blo 718322 1823057 := bstep (se 2 (by rfl) ⟨683646, by rfl⟩ : syracuseStep 1823057 = 1367293) B1367293
theorem B1233235 : Blo 718322 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B1823107 : Blo 718322 1823107 := bstep (se 1 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 1823107 = 2734661) B2734661
theorem B5853637 : Blo 718322 5853637 := bstep (se 4 (by rfl) ⟨548778, by rfl⟩ : syracuseStep 5853637 = 1097557) B1097557
theorem B2773453 : Blo 718322 2773453 := bstep (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) B1040045
theorem B971233 : Blo 718322 971233 := bstep (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) B728425
theorem B1823249 : Blo 718322 1823249 := bstep (se 2 (by rfl) ⟨683718, by rfl⟩ : syracuseStep 1823249 = 1367437) B1367437
theorem B971347 : Blo 718322 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B938659 : Blo 718322 938659 := bstep (se 1 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 938659 = 1407989) B1407989
theorem B4936817 : Blo 718322 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B808195 : Blo 718322 808195 := bstep (se 1 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 808195 = 1212293) B1212293
theorem B1365265 : Blo 718322 1365265 := bstep (se 2 (by rfl) ⟨511974, by rfl⟩ : syracuseStep 1365265 = 1023949) B1023949
theorem B2053457 : Blo 718322 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B808339 : Blo 718322 808339 := bstep (se 1 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 808339 = 1212509) B1212509
theorem B1824241 : Blo 718322 1824241 := bstep (se 2 (by rfl) ⟨684090, by rfl⟩ : syracuseStep 1824241 = 1368181) B1368181
theorem B808483 : Blo 718322 808483 := bstep (se 1 (by rfl) ⟨606362, by rfl⟩ : syracuseStep 808483 = 1212725) B1212725
theorem B8869475 : Blo 718322 8869475 := bstep (se 1 (by rfl) ⟨6652106, by rfl⟩ : syracuseStep 8869475 = 13304213) B13304213
theorem B808627 : Blo 718322 808627 := bstep (se 1 (by rfl) ⟨606470, by rfl⟩ : syracuseStep 808627 = 1212941) B1212941
theorem B4675313 : Blo 718322 4675313 := bstep (se 2 (by rfl) ⟨1753242, by rfl⟩ : syracuseStep 4675313 = 3506485) B3506485
theorem B1824515 : Blo 718322 1824515 := bstep (se 1 (by rfl) ⟨1368386, by rfl⟩ : syracuseStep 1824515 = 2736773) B2736773
theorem B2184995 : Blo 718322 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B808771 : Blo 718322 808771 := bstep (se 1 (by rfl) ⟨606578, by rfl⟩ : syracuseStep 808771 = 1213157) B1213157
theorem B8214371 : Blo 718322 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B1824707 : Blo 718322 1824707 := bstep (se 1 (by rfl) ⟨1368530, by rfl⟩ : syracuseStep 1824707 = 2737061) B2737061
theorem B808915 : Blo 718322 808915 := bstep (se 1 (by rfl) ⟨606686, by rfl⟩ : syracuseStep 808915 = 1213373) B1213373
theorem B3070001 : Blo 718322 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B809059 : Blo 718322 809059 := bstep (se 1 (by rfl) ⟨606794, by rfl⟩ : syracuseStep 809059 = 1213589) B1213589
theorem B809203 : Blo 718322 809203 := bstep (se 1 (by rfl) ⟨606902, by rfl⟩ : syracuseStep 809203 = 1213805) B1213805
theorem B2054413 : Blo 718322 2054413 := bstep (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) B770405
theorem B1366321 : Blo 718322 1366321 := bstep (se 2 (by rfl) ⟨512370, by rfl⟩ : syracuseStep 1366321 = 1024741) B1024741
theorem B809347 : Blo 718322 809347 := bstep (se 1 (by rfl) ⟨607010, by rfl⟩ : syracuseStep 809347 = 1214021) B1214021
theorem B2054641 : Blo 718322 2054641 := bstep (se 2 (by rfl) ⟨770490, by rfl⟩ : syracuseStep 2054641 = 1540981) B1540981
theorem B809491 : Blo 718322 809491 := bstep (se 1 (by rfl) ⟨607118, by rfl⟩ : syracuseStep 809491 = 1214237) B1214237
theorem B3889777 : Blo 718322 3889777 := bstep (se 2 (by rfl) ⟨1458666, by rfl⟩ : syracuseStep 3889777 = 2917333) B2917333
theorem B2054801 : Blo 718322 2054801 := bstep (se 2 (by rfl) ⟨770550, by rfl⟩ : syracuseStep 2054801 = 1541101) B1541101
theorem B809635 : Blo 718322 809635 := bstep (se 1 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 809635 = 1214453) B1214453
theorem B1366723 : Blo 718322 1366723 := bstep (se 1 (by rfl) ⟨1025042, by rfl⟩ : syracuseStep 1366723 = 2050085) B2050085
theorem B3070669 : Blo 718322 3070669 := bstep (se 3 (by rfl) ⟨575750, by rfl⟩ : syracuseStep 3070669 = 1151501) B1151501
theorem B7789283 : Blo 718322 7789283 := bstep (se 1 (by rfl) ⟨5841962, by rfl⟩ : syracuseStep 7789283 = 11683925) B11683925
theorem B35609315 : Blo 718322 35609315 := bstep (se 1 (by rfl) ⟨26706986, by rfl⟩ : syracuseStep 35609315 = 53413973) B53413973
theorem B1366769 : Blo 718322 1366769 := bstep (se 2 (by rfl) ⟨512538, by rfl⟩ : syracuseStep 1366769 = 1025077) B1025077
theorem B1661699 : Blo 718322 1661699 := bstep (se 1 (by rfl) ⟨1246274, by rfl⟩ : syracuseStep 1661699 = 2492549) B2492549
theorem B2054915 : Blo 718322 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B809779 : Blo 718322 809779 := bstep (se 1 (by rfl) ⟨607334, by rfl⟩ : syracuseStep 809779 = 1214669) B1214669
theorem B1825649 : Blo 718322 1825649 := bstep (se 2 (by rfl) ⟨684618, by rfl⟩ : syracuseStep 1825649 = 1369237) B1369237
theorem B1825699 : Blo 718322 1825699 := bstep (se 1 (by rfl) ⟨1369274, by rfl⟩ : syracuseStep 1825699 = 2738549) B2738549
theorem B809923 : Blo 718322 809923 := bstep (se 1 (by rfl) ⟨607442, by rfl⟩ : syracuseStep 809923 = 1214885) B1214885
theorem B1727491 : Blo 718322 1727491 := bstep (se 1 (by rfl) ⟨1295618, by rfl⟩ : syracuseStep 1727491 = 2591237) B2591237
theorem B1367057 : Blo 718322 1367057 := bstep (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) B1025293
theorem B1825841 : Blo 718322 1825841 := bstep (se 2 (by rfl) ⟨684690, by rfl⟩ : syracuseStep 1825841 = 1369381) B1369381
theorem B810067 : Blo 718322 810067 := bstep (se 1 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 810067 = 1215101) B1215101
theorem B810211 : Blo 718322 810211 := bstep (se 1 (by rfl) ⟨607658, by rfl⟩ : syracuseStep 810211 = 1215317) B1215317
theorem B3071267 : Blo 718322 3071267 := bstep (se 1 (by rfl) ⟨2303450, by rfl⟩ : syracuseStep 3071267 = 4606901) B4606901
theorem B2219345 : Blo 718322 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B810355 : Blo 718322 810355 := bstep (se 1 (by rfl) ⟨607766, by rfl⟩ : syracuseStep 810355 = 1215533) B1215533
theorem B3464653 : Blo 718322 3464653 := bstep (se 3 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 3464653 = 1299245) B1299245
theorem B974305 : Blo 718322 974305 := bstep (se 2 (by rfl) ⟨365364, by rfl⟩ : syracuseStep 974305 = 730729) B730729
theorem B810499 : Blo 718322 810499 := bstep (se 1 (by rfl) ⟨607874, by rfl⟩ : syracuseStep 810499 = 1215749) B1215749
theorem B1728049 : Blo 718322 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B2186833 : Blo 718322 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B810643 : Blo 718322 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B1367779 : Blo 718322 1367779 := bstep (se 1 (by rfl) ⟨1025834, by rfl⟩ : syracuseStep 1367779 = 2051669) B2051669
theorem B2055917 : Blo 718322 2055917 := bstep (se 3 (by rfl) ⟨385484, by rfl⟩ : syracuseStep 2055917 = 770969) B770969
theorem B810787 : Blo 718322 810787 := bstep (se 1 (by rfl) ⟨608090, by rfl⟩ : syracuseStep 810787 = 1216181) B1216181
theorem B909139 : Blo 718322 909139 := bstep (se 1 (by rfl) ⟨681854, by rfl⟩ : syracuseStep 909139 = 1363709) B1363709
theorem B4611973 : Blo 718322 4611973 := bstep (se 4 (by rfl) ⟨432372, by rfl⟩ : syracuseStep 4611973 = 864745) B864745
theorem B2056099 : Blo 718322 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B909235 : Blo 718322 909235 := bstep (se 1 (by rfl) ⟨681926, by rfl⟩ : syracuseStep 909235 = 1363853) B1363853
theorem B810931 : Blo 718322 810931 := bstep (se 1 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 810931 = 1216397) B1216397
theorem B1826833 : Blo 718322 1826833 := bstep (se 2 (by rfl) ⟨685062, by rfl⟩ : syracuseStep 1826833 = 1370125) B1370125
theorem B811075 : Blo 718322 811075 := bstep (se 1 (by rfl) ⟨608306, by rfl⟩ : syracuseStep 811075 = 1216613) B1216613
theorem B2056259 : Blo 718322 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B18735245 : Blo 718322 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B1368227 : Blo 718322 1368227 := bstep (se 1 (by rfl) ⟨1026170, by rfl⟩ : syracuseStep 1368227 = 2052341) B2052341
theorem B1728721 : Blo 718322 1728721 := bstep (se 2 (by rfl) ⟨648270, by rfl⟩ : syracuseStep 1728721 = 1296541) B1296541
theorem B811219 : Blo 718322 811219 := bstep (se 1 (by rfl) ⟨608414, by rfl⟩ : syracuseStep 811219 = 1216829) B1216829
theorem B1827107 : Blo 718322 1827107 := bstep (se 1 (by rfl) ⟨1370330, by rfl⟩ : syracuseStep 1827107 = 2740661) B2740661
theorem B811363 : Blo 718322 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B909731 : Blo 718322 909731 := bstep (se 1 (by rfl) ⟨682298, by rfl⟩ : syracuseStep 909731 = 1364597) B1364597
theorem B1368515 : Blo 718322 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B1827299 : Blo 718322 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B811507 : Blo 718322 811507 := bstep (se 1 (by rfl) ⟨608630, by rfl⟩ : syracuseStep 811507 = 1217261) B1217261
theorem B811651 : Blo 718322 811651 := bstep (se 1 (by rfl) ⟨608738, by rfl⟩ : syracuseStep 811651 = 1217477) B1217477
theorem B811795 : Blo 718322 811795 := bstep (se 1 (by rfl) ⟨608846, by rfl⟩ : syracuseStep 811795 = 1217693) B1217693
theorem B2188109 : Blo 718322 2188109 := bstep (se 3 (by rfl) ⟨410270, by rfl⟩ : syracuseStep 2188109 = 820541) B820541
theorem B975731 : Blo 718322 975731 := bstep (se 1 (by rfl) ⟨731798, by rfl⟩ : syracuseStep 975731 = 1463597) B1463597
theorem B811939 : Blo 718322 811939 := bstep (se 1 (by rfl) ⟨608954, by rfl⟩ : syracuseStep 811939 = 1217909) B1217909
theorem B812083 : Blo 718322 812083 := bstep (se 1 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 812083 = 1218125) B1218125
theorem B910435 : Blo 718322 910435 := bstep (se 1 (by rfl) ⟨682826, by rfl⟩ : syracuseStep 910435 = 1365653) B1365653
theorem B910531 : Blo 718322 910531 := bstep (se 1 (by rfl) ⟨682898, by rfl⟩ : syracuseStep 910531 = 1365797) B1365797
theorem B812227 : Blo 718322 812227 := bstep (se 1 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 812227 = 1218341) B1218341
theorem B812371 : Blo 718322 812371 := bstep (se 1 (by rfl) ⟨609278, by rfl⟩ : syracuseStep 812371 = 1218557) B1218557
theorem B1369457 : Blo 718322 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B1828241 : Blo 718322 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B1828291 : Blo 718322 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B812515 : Blo 718322 812515 := bstep (se 1 (by rfl) ⟨609386, by rfl⟩ : syracuseStep 812515 = 1218773) B1218773
theorem B911027 : Blo 718322 911027 := bstep (se 1 (by rfl) ⟨683270, by rfl⟩ : syracuseStep 911027 = 1366541) B1366541
theorem B3892997 : Blo 718322 3892997 := bstep (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) B729937
theorem B15591365 : Blo 718322 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B14772365 : Blo 718322 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B1370353 : Blo 718322 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B911731 : Blo 718322 911731 := bstep (se 1 (by rfl) ⟨683798, by rfl⟩ : syracuseStep 911731 = 1367597) B1367597
theorem B1370513 : Blo 718322 1370513 := bstep (se 2 (by rfl) ⟨513942, by rfl⟩ : syracuseStep 1370513 = 1027885) B1027885
theorem B1534403 : Blo 718322 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B911827 : Blo 718322 911827 := bstep (se 1 (by rfl) ⟨683870, by rfl⟩ : syracuseStep 911827 = 1367741) B1367741
theorem B4614691 : Blo 718322 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B1370915 : Blo 718322 1370915 := bstep (se 1 (by rfl) ⟨1028186, by rfl⟩ : syracuseStep 1370915 = 2056373) B2056373
theorem B912323 : Blo 718322 912323 := bstep (se 1 (by rfl) ⟨684242, by rfl⟩ : syracuseStep 912323 = 1368485) B1368485
theorem B3075043 : Blo 718322 3075043 := bstep (se 1 (by rfl) ⟨2306282, by rfl⟩ : syracuseStep 3075043 = 4612565) B4612565
theorem B1535267 : Blo 718322 1535267 := bstep (se 1 (by rfl) ⟨1151450, by rfl⟩ : syracuseStep 1535267 = 2302901) B2302901
theorem B1535377 : Blo 718322 1535377 := bstep (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) B1151533
theorem B1732067 : Blo 718322 1732067 := bstep (se 1 (by rfl) ⟨1299050, by rfl⟩ : syracuseStep 1732067 = 2598101) B2598101
theorem B913027 : Blo 718322 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B1732259 : Blo 718322 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B3468977 : Blo 718322 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B913123 : Blo 718322 913123 := bstep (se 1 (by rfl) ⟨684842, by rfl⟩ : syracuseStep 913123 = 1369685) B1369685
theorem B1732355 : Blo 718322 1732355 := bstep (se 1 (by rfl) ⟨1299266, by rfl⟩ : syracuseStep 1732355 = 2598533) B2598533
theorem B11235185 : Blo 718322 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B913619 : Blo 718322 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B1077491 : Blo 718322 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B1077521 : Blo 718322 1077521 := bstep (se 2 (by rfl) ⟨404070, by rfl⟩ : syracuseStep 1077521 = 808141) B808141
theorem B1077539 : Blo 718322 1077539 := bstep (se 1 (by rfl) ⟨808154, by rfl⟩ : syracuseStep 1077539 = 1616309) B1616309
theorem B1077569 : Blo 718322 1077569 := bstep (se 2 (by rfl) ⟨404088, by rfl⟩ : syracuseStep 1077569 = 808177) B808177
theorem B1077587 : Blo 718322 1077587 := bstep (se 1 (by rfl) ⟨808190, by rfl⟩ : syracuseStep 1077587 = 1616381) B1616381
theorem B1077617 : Blo 718322 1077617 := bstep (se 2 (by rfl) ⟨404106, by rfl⟩ : syracuseStep 1077617 = 808213) B808213
theorem B1077635 : Blo 718322 1077635 := bstep (se 1 (by rfl) ⟨808226, by rfl⟩ : syracuseStep 1077635 = 1616453) B1616453
theorem B1077665 : Blo 718322 1077665 := bstep (se 2 (by rfl) ⟨404124, by rfl⟩ : syracuseStep 1077665 = 808249) B808249
theorem B1077683 : Blo 718322 1077683 := bstep (se 1 (by rfl) ⟨808262, by rfl⟩ : syracuseStep 1077683 = 1616525) B1616525
theorem B1077713 : Blo 718322 1077713 := bstep (se 2 (by rfl) ⟨404142, by rfl⟩ : syracuseStep 1077713 = 808285) B808285
theorem B1077731 : Blo 718322 1077731 := bstep (se 1 (by rfl) ⟨808298, by rfl⟩ : syracuseStep 1077731 = 1616597) B1616597
theorem B4616689 : Blo 718322 4616689 := bstep (se 2 (by rfl) ⟨1731258, by rfl⟩ : syracuseStep 4616689 = 3462517) B3462517
theorem B1077761 : Blo 718322 1077761 := bstep (se 2 (by rfl) ⟨404160, by rfl⟩ : syracuseStep 1077761 = 808321) B808321
theorem B1077779 : Blo 718322 1077779 := bstep (se 1 (by rfl) ⟨808334, by rfl⟩ : syracuseStep 1077779 = 1616669) B1616669
theorem B1077809 : Blo 718322 1077809 := bstep (se 2 (by rfl) ⟨404178, by rfl⟩ : syracuseStep 1077809 = 808357) B808357
theorem B1077827 : Blo 718322 1077827 := bstep (se 1 (by rfl) ⟨808370, by rfl⟩ : syracuseStep 1077827 = 1616741) B1616741
theorem B1077857 : Blo 718322 1077857 := bstep (se 2 (by rfl) ⟨404196, by rfl⟩ : syracuseStep 1077857 = 808393) B808393
theorem B4092515 : Blo 718322 4092515 := bstep (se 1 (by rfl) ⟨3069386, by rfl⟩ : syracuseStep 4092515 = 6138773) B6138773
theorem B1077875 : Blo 718322 1077875 := bstep (se 1 (by rfl) ⟨808406, by rfl⟩ : syracuseStep 1077875 = 1616813) B1616813
theorem B1077905 : Blo 718322 1077905 := bstep (se 2 (by rfl) ⟨404214, by rfl⟩ : syracuseStep 1077905 = 808429) B808429
theorem B1077923 : Blo 718322 1077923 := bstep (se 1 (by rfl) ⟨808442, by rfl⟩ : syracuseStep 1077923 = 1616885) B1616885
theorem B1077953 : Blo 718322 1077953 := bstep (se 2 (by rfl) ⟨404232, by rfl⟩ : syracuseStep 1077953 = 808465) B808465
theorem B1077971 : Blo 718322 1077971 := bstep (se 1 (by rfl) ⟨808478, by rfl⟩ : syracuseStep 1077971 = 1616957) B1616957
theorem B1078001 : Blo 718322 1078001 := bstep (se 2 (by rfl) ⟨404250, by rfl⟩ : syracuseStep 1078001 = 808501) B808501
theorem B1078019 : Blo 718322 1078019 := bstep (se 1 (by rfl) ⟨808514, by rfl⟩ : syracuseStep 1078019 = 1617029) B1617029
theorem B1078049 : Blo 718322 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B1078067 : Blo 718322 1078067 := bstep (se 1 (by rfl) ⟨808550, by rfl⟩ : syracuseStep 1078067 = 1617101) B1617101
theorem B1078097 : Blo 718322 1078097 := bstep (se 2 (by rfl) ⟨404286, by rfl⟩ : syracuseStep 1078097 = 808573) B808573
theorem B1078115 : Blo 718322 1078115 := bstep (se 1 (by rfl) ⟨808586, by rfl⟩ : syracuseStep 1078115 = 1617173) B1617173
theorem B1078145 : Blo 718322 1078145 := bstep (se 2 (by rfl) ⟨404304, by rfl⟩ : syracuseStep 1078145 = 808609) B808609
theorem B1078163 : Blo 718322 1078163 := bstep (se 1 (by rfl) ⟨808622, by rfl⟩ : syracuseStep 1078163 = 1617245) B1617245
theorem B1078193 : Blo 718322 1078193 := bstep (se 2 (by rfl) ⟨404322, by rfl⟩ : syracuseStep 1078193 = 808645) B808645
theorem B3077041 : Blo 718322 3077041 := bstep (se 2 (by rfl) ⟨1153890, by rfl⟩ : syracuseStep 3077041 = 2307781) B2307781
theorem B1078211 : Blo 718322 1078211 := bstep (se 1 (by rfl) ⟨808658, by rfl⟩ : syracuseStep 1078211 = 1617317) B1617317
theorem B1078241 : Blo 718322 1078241 := bstep (se 2 (by rfl) ⟨404340, by rfl⟩ : syracuseStep 1078241 = 808681) B808681
theorem B1078259 : Blo 718322 1078259 := bstep (se 1 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 1078259 = 1617389) B1617389
theorem B1078289 : Blo 718322 1078289 := bstep (se 2 (by rfl) ⟨404358, by rfl⟩ : syracuseStep 1078289 = 808717) B808717
theorem B1078307 : Blo 718322 1078307 := bstep (se 1 (by rfl) ⟨808730, by rfl⟩ : syracuseStep 1078307 = 1617461) B1617461
theorem B1078337 : Blo 718322 1078337 := bstep (se 2 (by rfl) ⟨404376, by rfl⟩ : syracuseStep 1078337 = 808753) B808753
theorem B1078355 : Blo 718322 1078355 := bstep (se 1 (by rfl) ⟨808766, by rfl⟩ : syracuseStep 1078355 = 1617533) B1617533
theorem B1078385 : Blo 718322 1078385 := bstep (se 2 (by rfl) ⟨404394, by rfl⟩ : syracuseStep 1078385 = 808789) B808789
theorem B1078403 : Blo 718322 1078403 := bstep (se 1 (by rfl) ⟨808802, by rfl⟩ : syracuseStep 1078403 = 1617605) B1617605
theorem B1078433 : Blo 718322 1078433 := bstep (se 2 (by rfl) ⟨404412, by rfl⟩ : syracuseStep 1078433 = 808825) B808825
theorem B1078451 : Blo 718322 1078451 := bstep (se 1 (by rfl) ⟨808838, by rfl⟩ : syracuseStep 1078451 = 1617677) B1617677
theorem B1078481 : Blo 718322 1078481 := bstep (se 2 (by rfl) ⟨404430, by rfl⟩ : syracuseStep 1078481 = 808861) B808861
theorem B1078499 : Blo 718322 1078499 := bstep (se 1 (by rfl) ⟨808874, by rfl⟩ : syracuseStep 1078499 = 1617749) B1617749
theorem B1078529 : Blo 718322 1078529 := bstep (se 2 (by rfl) ⟨404448, by rfl⟩ : syracuseStep 1078529 = 808897) B808897
theorem B1078547 : Blo 718322 1078547 := bstep (se 1 (by rfl) ⟨808910, by rfl⟩ : syracuseStep 1078547 = 1617821) B1617821
theorem B1078577 : Blo 718322 1078577 := bstep (se 2 (by rfl) ⟨404466, by rfl⟩ : syracuseStep 1078577 = 808933) B808933
theorem B1078595 : Blo 718322 1078595 := bstep (se 1 (by rfl) ⟨808946, by rfl⟩ : syracuseStep 1078595 = 1617893) B1617893
theorem B2192707 : Blo 718322 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B1078625 : Blo 718322 1078625 := bstep (se 2 (by rfl) ⟨404484, by rfl⟩ : syracuseStep 1078625 = 808969) B808969
theorem B1537393 : Blo 718322 1537393 := bstep (se 2 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 1537393 = 1153045) B1153045
theorem B1078643 : Blo 718322 1078643 := bstep (se 1 (by rfl) ⟨808982, by rfl⟩ : syracuseStep 1078643 = 1617965) B1617965
theorem B1078673 : Blo 718322 1078673 := bstep (se 2 (by rfl) ⟨404502, by rfl⟩ : syracuseStep 1078673 = 809005) B809005
theorem B1078691 : Blo 718322 1078691 := bstep (se 1 (by rfl) ⟨809018, by rfl⟩ : syracuseStep 1078691 = 1618037) B1618037
theorem B1078721 : Blo 718322 1078721 := bstep (se 2 (by rfl) ⟨404520, by rfl⟩ : syracuseStep 1078721 = 809041) B809041
theorem B1078739 : Blo 718322 1078739 := bstep (se 1 (by rfl) ⟨809054, by rfl⟩ : syracuseStep 1078739 = 1618109) B1618109
theorem B1078769 : Blo 718322 1078769 := bstep (se 2 (by rfl) ⟨404538, by rfl⟩ : syracuseStep 1078769 = 809077) B809077
theorem B718323 : Blo 718322 718323 := bstep (se 1 (by rfl) ⟨538742, by rfl⟩ : syracuseStep 718323 = 1077485) B1077485
theorem B718339 : Blo 718322 718339 := bstep (se 1 (by rfl) ⟨538754, by rfl⟩ : syracuseStep 718339 = 1077509) B1077509
theorem B1078787 : Blo 718322 1078787 := bstep (se 1 (by rfl) ⟨809090, by rfl⟩ : syracuseStep 1078787 = 1618181) B1618181
theorem B718355 : Blo 718322 718355 := bstep (se 1 (by rfl) ⟨538766, by rfl⟩ : syracuseStep 718355 = 1077533) B1077533
theorem B1078817 : Blo 718322 1078817 := bstep (se 2 (by rfl) ⟨404556, by rfl⟩ : syracuseStep 1078817 = 809113) B809113
theorem B718371 : Blo 718322 718371 := bstep (se 1 (by rfl) ⟨538778, by rfl⟩ : syracuseStep 718371 = 1077557) B1077557
theorem B718387 : Blo 718322 718387 := bstep (se 1 (by rfl) ⟨538790, by rfl⟩ : syracuseStep 718387 = 1077581) B1077581
theorem B1078835 : Blo 718322 1078835 := bstep (se 1 (by rfl) ⟨809126, by rfl⟩ : syracuseStep 1078835 = 1618253) B1618253
theorem B718403 : Blo 718322 718403 := bstep (se 1 (by rfl) ⟨538802, by rfl⟩ : syracuseStep 718403 = 1077605) B1077605
theorem B4093517 : Blo 718322 4093517 := bstep (se 3 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 4093517 = 1535069) B1535069
theorem B1078865 : Blo 718322 1078865 := bstep (se 2 (by rfl) ⟨404574, by rfl⟩ : syracuseStep 1078865 = 809149) B809149
theorem B718419 : Blo 718322 718419 := bstep (se 1 (by rfl) ⟨538814, by rfl⟩ : syracuseStep 718419 = 1077629) B1077629
theorem B718435 : Blo 718322 718435 := bstep (se 1 (by rfl) ⟨538826, by rfl⟩ : syracuseStep 718435 = 1077653) B1077653
theorem B1078883 : Blo 718322 1078883 := bstep (se 1 (by rfl) ⟨809162, by rfl⟩ : syracuseStep 1078883 = 1618325) B1618325
theorem B1734257 : Blo 718322 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B718451 : Blo 718322 718451 := bstep (se 1 (by rfl) ⟨538838, by rfl⟩ : syracuseStep 718451 = 1077677) B1077677
theorem B1078913 : Blo 718322 1078913 := bstep (se 2 (by rfl) ⟨404592, by rfl⟩ : syracuseStep 1078913 = 809185) B809185
theorem B718467 : Blo 718322 718467 := bstep (se 1 (by rfl) ⟨538850, by rfl⟩ : syracuseStep 718467 = 1077701) B1077701
theorem B718483 : Blo 718322 718483 := bstep (se 1 (by rfl) ⟨538862, by rfl⟩ : syracuseStep 718483 = 1077725) B1077725
theorem B1078931 : Blo 718322 1078931 := bstep (se 1 (by rfl) ⟨809198, by rfl⟩ : syracuseStep 1078931 = 1618397) B1618397
theorem B718499 : Blo 718322 718499 := bstep (se 1 (by rfl) ⟨538874, by rfl⟩ : syracuseStep 718499 = 1077749) B1077749
theorem B1078961 : Blo 718322 1078961 := bstep (se 2 (by rfl) ⟨404610, by rfl⟩ : syracuseStep 1078961 = 809221) B809221
theorem B718515 : Blo 718322 718515 := bstep (se 1 (by rfl) ⟨538886, by rfl⟩ : syracuseStep 718515 = 1077773) B1077773
theorem B718531 : Blo 718322 718531 := bstep (se 1 (by rfl) ⟨538898, by rfl⟩ : syracuseStep 718531 = 1077797) B1077797
theorem B1078979 : Blo 718322 1078979 := bstep (se 1 (by rfl) ⟨809234, by rfl⟩ : syracuseStep 1078979 = 1618469) B1618469
theorem B718547 : Blo 718322 718547 := bstep (se 1 (by rfl) ⟨538910, by rfl⟩ : syracuseStep 718547 = 1077821) B1077821
theorem B1079009 : Blo 718322 1079009 := bstep (se 2 (by rfl) ⟨404628, by rfl⟩ : syracuseStep 1079009 = 809257) B809257
theorem B718563 : Blo 718322 718563 := bstep (se 1 (by rfl) ⟨538922, by rfl⟩ : syracuseStep 718563 = 1077845) B1077845
theorem B718579 : Blo 718322 718579 := bstep (se 1 (by rfl) ⟨538934, by rfl⟩ : syracuseStep 718579 = 1077869) B1077869
theorem B1079027 : Blo 718322 1079027 := bstep (se 1 (by rfl) ⟨809270, by rfl⟩ : syracuseStep 1079027 = 1618541) B1618541
theorem B718595 : Blo 718322 718595 := bstep (se 1 (by rfl) ⟨538946, by rfl⟩ : syracuseStep 718595 = 1077893) B1077893
theorem B1537795 : Blo 718322 1537795 := bstep (se 1 (by rfl) ⟨1153346, by rfl⟩ : syracuseStep 1537795 = 2306693) B2306693
theorem B1079057 : Blo 718322 1079057 := bstep (se 2 (by rfl) ⟨404646, by rfl⟩ : syracuseStep 1079057 = 809293) B809293
theorem B2193169 : Blo 718322 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B718611 : Blo 718322 718611 := bstep (se 1 (by rfl) ⟨538958, by rfl⟩ : syracuseStep 718611 = 1077917) B1077917
theorem B718627 : Blo 718322 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B1079075 : Blo 718322 1079075 := bstep (se 1 (by rfl) ⟨809306, by rfl⟩ : syracuseStep 1079075 = 1618613) B1618613
theorem B718643 : Blo 718322 718643 := bstep (se 1 (by rfl) ⟨538982, by rfl⟩ : syracuseStep 718643 = 1077965) B1077965
theorem B1079105 : Blo 718322 1079105 := bstep (se 2 (by rfl) ⟨404664, by rfl⟩ : syracuseStep 1079105 = 809329) B809329
theorem B718659 : Blo 718322 718659 := bstep (se 1 (by rfl) ⟨538994, by rfl⟩ : syracuseStep 718659 = 1077989) B1077989
theorem B718675 : Blo 718322 718675 := bstep (se 1 (by rfl) ⟨539006, by rfl⟩ : syracuseStep 718675 = 1078013) B1078013
theorem B1079123 : Blo 718322 1079123 := bstep (se 1 (by rfl) ⟨809342, by rfl⟩ : syracuseStep 1079123 = 1618685) B1618685
theorem B718691 : Blo 718322 718691 := bstep (se 1 (by rfl) ⟨539018, by rfl⟩ : syracuseStep 718691 = 1078037) B1078037
theorem B1079153 : Blo 718322 1079153 := bstep (se 2 (by rfl) ⟨404682, by rfl⟩ : syracuseStep 1079153 = 809365) B809365
theorem B718707 : Blo 718322 718707 := bstep (se 1 (by rfl) ⟨539030, by rfl⟩ : syracuseStep 718707 = 1078061) B1078061
theorem B718723 : Blo 718322 718723 := bstep (se 1 (by rfl) ⟨539042, by rfl⟩ : syracuseStep 718723 = 1078085) B1078085
theorem B1079171 : Blo 718322 1079171 := bstep (se 1 (by rfl) ⟨809378, by rfl⟩ : syracuseStep 1079171 = 1618757) B1618757
theorem B718739 : Blo 718322 718739 := bstep (se 1 (by rfl) ⟨539054, by rfl⟩ : syracuseStep 718739 = 1078109) B1078109
theorem B1079201 : Blo 718322 1079201 := bstep (se 2 (by rfl) ⟨404700, by rfl⟩ : syracuseStep 1079201 = 809401) B809401
theorem B718755 : Blo 718322 718755 := bstep (se 1 (by rfl) ⟨539066, by rfl⟩ : syracuseStep 718755 = 1078133) B1078133
theorem B718771 : Blo 718322 718771 := bstep (se 1 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 718771 = 1078157) B1078157
theorem B1079219 : Blo 718322 1079219 := bstep (se 1 (by rfl) ⟨809414, by rfl⟩ : syracuseStep 1079219 = 1618829) B1618829
theorem B718787 : Blo 718322 718787 := bstep (se 1 (by rfl) ⟨539090, by rfl⟩ : syracuseStep 718787 = 1078181) B1078181
theorem B1079249 : Blo 718322 1079249 := bstep (se 2 (by rfl) ⟨404718, by rfl⟩ : syracuseStep 1079249 = 809437) B809437
theorem B718803 : Blo 718322 718803 := bstep (se 1 (by rfl) ⟨539102, by rfl⟩ : syracuseStep 718803 = 1078205) B1078205
theorem B718819 : Blo 718322 718819 := bstep (se 1 (by rfl) ⟨539114, by rfl⟩ : syracuseStep 718819 = 1078229) B1078229
theorem B1079267 : Blo 718322 1079267 := bstep (se 1 (by rfl) ⟨809450, by rfl⟩ : syracuseStep 1079267 = 1618901) B1618901
theorem B5273585 : Blo 718322 5273585 := bstep (se 2 (by rfl) ⟨1977594, by rfl⟩ : syracuseStep 5273585 = 3955189) B3955189
theorem B718835 : Blo 718322 718835 := bstep (se 1 (by rfl) ⟨539126, by rfl⟩ : syracuseStep 718835 = 1078253) B1078253
theorem B1079297 : Blo 718322 1079297 := bstep (se 2 (by rfl) ⟨404736, by rfl⟩ : syracuseStep 1079297 = 809473) B809473
theorem B718851 : Blo 718322 718851 := bstep (se 1 (by rfl) ⟨539138, by rfl⟩ : syracuseStep 718851 = 1078277) B1078277
theorem B718867 : Blo 718322 718867 := bstep (se 1 (by rfl) ⟨539150, by rfl⟩ : syracuseStep 718867 = 1078301) B1078301
theorem B1079315 : Blo 718322 1079315 := bstep (se 1 (by rfl) ⟨809486, by rfl⟩ : syracuseStep 1079315 = 1618973) B1618973
theorem B718883 : Blo 718322 718883 := bstep (se 1 (by rfl) ⟨539162, by rfl⟩ : syracuseStep 718883 = 1078325) B1078325
theorem B1079345 : Blo 718322 1079345 := bstep (se 2 (by rfl) ⟨404754, by rfl⟩ : syracuseStep 1079345 = 809509) B809509
theorem B718899 : Blo 718322 718899 := bstep (se 1 (by rfl) ⟨539174, by rfl⟩ : syracuseStep 718899 = 1078349) B1078349
theorem B718915 : Blo 718322 718915 := bstep (se 1 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 718915 = 1078373) B1078373
theorem B1079363 : Blo 718322 1079363 := bstep (se 1 (by rfl) ⟨809522, by rfl⟩ : syracuseStep 1079363 = 1619045) B1619045
theorem B718931 : Blo 718322 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B1079393 : Blo 718322 1079393 := bstep (se 2 (by rfl) ⟨404772, by rfl⟩ : syracuseStep 1079393 = 809545) B809545
theorem B718947 : Blo 718322 718947 := bstep (se 1 (by rfl) ⟨539210, by rfl⟩ : syracuseStep 718947 = 1078421) B1078421
theorem B718963 : Blo 718322 718963 := bstep (se 1 (by rfl) ⟨539222, by rfl⟩ : syracuseStep 718963 = 1078445) B1078445
theorem B1079411 : Blo 718322 1079411 := bstep (se 1 (by rfl) ⟨809558, by rfl⟩ : syracuseStep 1079411 = 1619117) B1619117
theorem B718979 : Blo 718322 718979 := bstep (se 1 (by rfl) ⟨539234, by rfl⟩ : syracuseStep 718979 = 1078469) B1078469
theorem B1734787 : Blo 718322 1734787 := bstep (se 1 (by rfl) ⟨1301090, by rfl⟩ : syracuseStep 1734787 = 2602181) B2602181
theorem B1079441 : Blo 718322 1079441 := bstep (se 2 (by rfl) ⟨404790, by rfl⟩ : syracuseStep 1079441 = 809581) B809581
theorem B718995 : Blo 718322 718995 := bstep (se 1 (by rfl) ⟨539246, by rfl⟩ : syracuseStep 718995 = 1078493) B1078493
theorem B719011 : Blo 718322 719011 := bstep (se 1 (by rfl) ⟨539258, by rfl⟩ : syracuseStep 719011 = 1078517) B1078517
theorem B1079459 : Blo 718322 1079459 := bstep (se 1 (by rfl) ⟨809594, by rfl⟩ : syracuseStep 1079459 = 1619189) B1619189
theorem B719027 : Blo 718322 719027 := bstep (se 1 (by rfl) ⟨539270, by rfl⟩ : syracuseStep 719027 = 1078541) B1078541
theorem B1079489 : Blo 718322 1079489 := bstep (se 2 (by rfl) ⟨404808, by rfl⟩ : syracuseStep 1079489 = 809617) B809617
theorem B719043 : Blo 718322 719043 := bstep (se 1 (by rfl) ⟨539282, by rfl⟩ : syracuseStep 719043 = 1078565) B1078565
theorem B719059 : Blo 718322 719059 := bstep (se 1 (by rfl) ⟨539294, by rfl⟩ : syracuseStep 719059 = 1078589) B1078589
theorem B1079507 : Blo 718322 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B719075 : Blo 718322 719075 := bstep (se 1 (by rfl) ⟨539306, by rfl⟩ : syracuseStep 719075 = 1078613) B1078613
theorem B1079537 : Blo 718322 1079537 := bstep (se 2 (by rfl) ⟨404826, by rfl⟩ : syracuseStep 1079537 = 809653) B809653
theorem B719091 : Blo 718322 719091 := bstep (se 1 (by rfl) ⟨539318, by rfl⟩ : syracuseStep 719091 = 1078637) B1078637
theorem B719107 : Blo 718322 719107 := bstep (se 1 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 719107 = 1078661) B1078661
theorem B1079555 : Blo 718322 1079555 := bstep (se 1 (by rfl) ⟨809666, by rfl⟩ : syracuseStep 1079555 = 1619333) B1619333
theorem B719123 : Blo 718322 719123 := bstep (se 1 (by rfl) ⟨539342, by rfl⟩ : syracuseStep 719123 = 1078685) B1078685
theorem B1079585 : Blo 718322 1079585 := bstep (se 2 (by rfl) ⟨404844, by rfl⟩ : syracuseStep 1079585 = 809689) B809689
theorem B719139 : Blo 718322 719139 := bstep (se 1 (by rfl) ⟨539354, by rfl⟩ : syracuseStep 719139 = 1078709) B1078709
theorem B719155 : Blo 718322 719155 := bstep (se 1 (by rfl) ⟨539366, by rfl⟩ : syracuseStep 719155 = 1078733) B1078733
theorem B1079603 : Blo 718322 1079603 := bstep (se 1 (by rfl) ⟨809702, by rfl⟩ : syracuseStep 1079603 = 1619405) B1619405
theorem B719171 : Blo 718322 719171 := bstep (se 1 (by rfl) ⟨539378, by rfl⟩ : syracuseStep 719171 = 1078757) B1078757
theorem B1079633 : Blo 718322 1079633 := bstep (se 2 (by rfl) ⟨404862, by rfl⟩ : syracuseStep 1079633 = 809725) B809725
theorem B719187 : Blo 718322 719187 := bstep (se 1 (by rfl) ⟨539390, by rfl⟩ : syracuseStep 719187 = 1078781) B1078781
theorem B719203 : Blo 718322 719203 := bstep (se 1 (by rfl) ⟨539402, by rfl⟩ : syracuseStep 719203 = 1078805) B1078805
theorem B1079651 : Blo 718322 1079651 := bstep (se 1 (by rfl) ⟨809738, by rfl⟩ : syracuseStep 1079651 = 1619477) B1619477
theorem B719219 : Blo 718322 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B1079681 : Blo 718322 1079681 := bstep (se 2 (by rfl) ⟨404880, by rfl⟩ : syracuseStep 1079681 = 809761) B809761
theorem B719235 : Blo 718322 719235 := bstep (se 1 (by rfl) ⟨539426, by rfl⟩ : syracuseStep 719235 = 1078853) B1078853
theorem B719251 : Blo 718322 719251 := bstep (se 1 (by rfl) ⟨539438, by rfl⟩ : syracuseStep 719251 = 1078877) B1078877
theorem B1079699 : Blo 718322 1079699 := bstep (se 1 (by rfl) ⟨809774, by rfl⟩ : syracuseStep 1079699 = 1619549) B1619549
theorem B719267 : Blo 718322 719267 := bstep (se 1 (by rfl) ⟨539450, by rfl⟩ : syracuseStep 719267 = 1078901) B1078901
theorem B1079729 : Blo 718322 1079729 := bstep (se 2 (by rfl) ⟨404898, by rfl⟩ : syracuseStep 1079729 = 809797) B809797
theorem B719283 : Blo 718322 719283 := bstep (se 1 (by rfl) ⟨539462, by rfl⟩ : syracuseStep 719283 = 1078925) B1078925
theorem B719299 : Blo 718322 719299 := bstep (se 1 (by rfl) ⟨539474, by rfl⟩ : syracuseStep 719299 = 1078949) B1078949
theorem B1079747 : Blo 718322 1079747 := bstep (se 1 (by rfl) ⟨809810, by rfl⟩ : syracuseStep 1079747 = 1619621) B1619621
theorem B719315 : Blo 718322 719315 := bstep (se 1 (by rfl) ⟨539486, by rfl⟩ : syracuseStep 719315 = 1078973) B1078973
theorem B1079777 : Blo 718322 1079777 := bstep (se 2 (by rfl) ⟨404916, by rfl⟩ : syracuseStep 1079777 = 809833) B809833
theorem B719331 : Blo 718322 719331 := bstep (se 1 (by rfl) ⟨539498, by rfl⟩ : syracuseStep 719331 = 1078997) B1078997
theorem B719347 : Blo 718322 719347 := bstep (se 1 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 719347 = 1079021) B1079021
theorem B1079795 : Blo 718322 1079795 := bstep (se 1 (by rfl) ⟨809846, by rfl⟩ : syracuseStep 1079795 = 1619693) B1619693
theorem B719363 : Blo 718322 719363 := bstep (se 1 (by rfl) ⟨539522, by rfl⟩ : syracuseStep 719363 = 1079045) B1079045
theorem B1079825 : Blo 718322 1079825 := bstep (se 2 (by rfl) ⟨404934, by rfl⟩ : syracuseStep 1079825 = 809869) B809869
theorem B719379 : Blo 718322 719379 := bstep (se 1 (by rfl) ⟨539534, by rfl⟩ : syracuseStep 719379 = 1079069) B1079069
theorem B719395 : Blo 718322 719395 := bstep (se 1 (by rfl) ⟨539546, by rfl⟩ : syracuseStep 719395 = 1079093) B1079093
theorem B1079843 : Blo 718322 1079843 := bstep (se 1 (by rfl) ⟨809882, by rfl⟩ : syracuseStep 1079843 = 1619765) B1619765
theorem B719411 : Blo 718322 719411 := bstep (se 1 (by rfl) ⟨539558, by rfl⟩ : syracuseStep 719411 = 1079117) B1079117
theorem B1079873 : Blo 718322 1079873 := bstep (se 2 (by rfl) ⟨404952, by rfl⟩ : syracuseStep 1079873 = 809905) B809905
theorem B719427 : Blo 718322 719427 := bstep (se 1 (by rfl) ⟨539570, by rfl⟩ : syracuseStep 719427 = 1079141) B1079141
theorem B719443 : Blo 718322 719443 := bstep (se 1 (by rfl) ⟨539582, by rfl⟩ : syracuseStep 719443 = 1079165) B1079165
theorem B1079891 : Blo 718322 1079891 := bstep (se 1 (by rfl) ⟨809918, by rfl⟩ : syracuseStep 1079891 = 1619837) B1619837
theorem B719459 : Blo 718322 719459 := bstep (se 1 (by rfl) ⟨539594, by rfl⟩ : syracuseStep 719459 = 1079189) B1079189
theorem B1079921 : Blo 718322 1079921 := bstep (se 2 (by rfl) ⟨404970, by rfl⟩ : syracuseStep 1079921 = 809941) B809941
theorem B719475 : Blo 718322 719475 := bstep (se 1 (by rfl) ⟨539606, by rfl⟩ : syracuseStep 719475 = 1079213) B1079213
theorem B719491 : Blo 718322 719491 := bstep (se 1 (by rfl) ⟨539618, by rfl⟩ : syracuseStep 719491 = 1079237) B1079237
theorem B1079939 : Blo 718322 1079939 := bstep (se 1 (by rfl) ⟨809954, by rfl⟩ : syracuseStep 1079939 = 1619909) B1619909
theorem B719507 : Blo 718322 719507 := bstep (se 1 (by rfl) ⟨539630, by rfl⟩ : syracuseStep 719507 = 1079261) B1079261
theorem B1079969 : Blo 718322 1079969 := bstep (se 2 (by rfl) ⟨404988, by rfl⟩ : syracuseStep 1079969 = 809977) B809977
theorem B719523 : Blo 718322 719523 := bstep (se 1 (by rfl) ⟨539642, by rfl⟩ : syracuseStep 719523 = 1079285) B1079285
theorem B719539 : Blo 718322 719539 := bstep (se 1 (by rfl) ⟨539654, by rfl⟩ : syracuseStep 719539 = 1079309) B1079309
theorem B1079987 : Blo 718322 1079987 := bstep (se 1 (by rfl) ⟨809990, by rfl⟩ : syracuseStep 1079987 = 1619981) B1619981
theorem B719555 : Blo 718322 719555 := bstep (se 1 (by rfl) ⟨539666, by rfl⟩ : syracuseStep 719555 = 1079333) B1079333
theorem B1080017 : Blo 718322 1080017 := bstep (se 2 (by rfl) ⟨405006, by rfl⟩ : syracuseStep 1080017 = 810013) B810013
theorem B719571 : Blo 718322 719571 := bstep (se 1 (by rfl) ⟨539678, by rfl⟩ : syracuseStep 719571 = 1079357) B1079357
theorem B719587 : Blo 718322 719587 := bstep (se 1 (by rfl) ⟨539690, by rfl⟩ : syracuseStep 719587 = 1079381) B1079381
theorem B1080035 : Blo 718322 1080035 := bstep (se 1 (by rfl) ⟨810026, by rfl⟩ : syracuseStep 1080035 = 1620053) B1620053
theorem B719603 : Blo 718322 719603 := bstep (se 1 (by rfl) ⟨539702, by rfl⟩ : syracuseStep 719603 = 1079405) B1079405
theorem B1080065 : Blo 718322 1080065 := bstep (se 2 (by rfl) ⟨405024, by rfl⟩ : syracuseStep 1080065 = 810049) B810049
theorem B719619 : Blo 718322 719619 := bstep (se 1 (by rfl) ⟨539714, by rfl⟩ : syracuseStep 719619 = 1079429) B1079429
theorem B719635 : Blo 718322 719635 := bstep (se 1 (by rfl) ⟨539726, by rfl⟩ : syracuseStep 719635 = 1079453) B1079453
theorem B1080083 : Blo 718322 1080083 := bstep (se 1 (by rfl) ⟨810062, by rfl⟩ : syracuseStep 1080083 = 1620125) B1620125
theorem B719651 : Blo 718322 719651 := bstep (se 1 (by rfl) ⟨539738, by rfl⟩ : syracuseStep 719651 = 1079477) B1079477
theorem B1080113 : Blo 718322 1080113 := bstep (se 2 (by rfl) ⟨405042, by rfl⟩ : syracuseStep 1080113 = 810085) B810085
theorem B719667 : Blo 718322 719667 := bstep (se 1 (by rfl) ⟨539750, by rfl⟩ : syracuseStep 719667 = 1079501) B1079501
theorem B719683 : Blo 718322 719683 := bstep (se 1 (by rfl) ⟨539762, by rfl⟩ : syracuseStep 719683 = 1079525) B1079525
theorem B1080131 : Blo 718322 1080131 := bstep (se 1 (by rfl) ⟨810098, by rfl⟩ : syracuseStep 1080131 = 1620197) B1620197
theorem B719699 : Blo 718322 719699 := bstep (se 1 (by rfl) ⟨539774, by rfl⟩ : syracuseStep 719699 = 1079549) B1079549
theorem B1080161 : Blo 718322 1080161 := bstep (se 2 (by rfl) ⟨405060, by rfl⟩ : syracuseStep 1080161 = 810121) B810121
theorem B719715 : Blo 718322 719715 := bstep (se 1 (by rfl) ⟨539786, by rfl⟩ : syracuseStep 719715 = 1079573) B1079573
theorem B719731 : Blo 718322 719731 := bstep (se 1 (by rfl) ⟨539798, by rfl⟩ : syracuseStep 719731 = 1079597) B1079597
theorem B1080179 : Blo 718322 1080179 := bstep (se 1 (by rfl) ⟨810134, by rfl⟩ : syracuseStep 1080179 = 1620269) B1620269
theorem B719747 : Blo 718322 719747 := bstep (se 1 (by rfl) ⟨539810, by rfl⟩ : syracuseStep 719747 = 1079621) B1079621
theorem B1080209 : Blo 718322 1080209 := bstep (se 2 (by rfl) ⟨405078, by rfl⟩ : syracuseStep 1080209 = 810157) B810157
theorem B719763 : Blo 718322 719763 := bstep (se 1 (by rfl) ⟨539822, by rfl⟩ : syracuseStep 719763 = 1079645) B1079645
theorem B719779 : Blo 718322 719779 := bstep (se 1 (by rfl) ⟨539834, by rfl⟩ : syracuseStep 719779 = 1079669) B1079669
theorem B1080227 : Blo 718322 1080227 := bstep (se 1 (by rfl) ⟨810170, by rfl⟩ : syracuseStep 1080227 = 1620341) B1620341
theorem B719795 : Blo 718322 719795 := bstep (se 1 (by rfl) ⟨539846, by rfl⟩ : syracuseStep 719795 = 1079693) B1079693
theorem B1080257 : Blo 718322 1080257 := bstep (se 2 (by rfl) ⟨405096, by rfl⟩ : syracuseStep 1080257 = 810193) B810193
theorem B719811 : Blo 718322 719811 := bstep (se 1 (by rfl) ⟨539858, by rfl⟩ : syracuseStep 719811 = 1079717) B1079717
theorem B719827 : Blo 718322 719827 := bstep (se 1 (by rfl) ⟨539870, by rfl⟩ : syracuseStep 719827 = 1079741) B1079741
theorem B1080275 : Blo 718322 1080275 := bstep (se 1 (by rfl) ⟨810206, by rfl⟩ : syracuseStep 1080275 = 1620413) B1620413
theorem B3505123 : Blo 718322 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B719843 : Blo 718322 719843 := bstep (se 1 (by rfl) ⟨539882, by rfl⟩ : syracuseStep 719843 = 1079765) B1079765
theorem B1080305 : Blo 718322 1080305 := bstep (se 2 (by rfl) ⟨405114, by rfl⟩ : syracuseStep 1080305 = 810229) B810229
theorem B719859 : Blo 718322 719859 := bstep (se 1 (by rfl) ⟨539894, by rfl⟩ : syracuseStep 719859 = 1079789) B1079789
theorem B719875 : Blo 718322 719875 := bstep (se 1 (by rfl) ⟨539906, by rfl⟩ : syracuseStep 719875 = 1079813) B1079813
theorem B1080323 : Blo 718322 1080323 := bstep (se 1 (by rfl) ⟨810242, by rfl⟩ : syracuseStep 1080323 = 1620485) B1620485
theorem B719891 : Blo 718322 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B1080353 : Blo 718322 1080353 := bstep (se 2 (by rfl) ⟨405132, by rfl⟩ : syracuseStep 1080353 = 810265) B810265
theorem B719907 : Blo 718322 719907 := bstep (se 1 (by rfl) ⟨539930, by rfl⟩ : syracuseStep 719907 = 1079861) B1079861
theorem B719923 : Blo 718322 719923 := bstep (se 1 (by rfl) ⟨539942, by rfl⟩ : syracuseStep 719923 = 1079885) B1079885
theorem B1080371 : Blo 718322 1080371 := bstep (se 1 (by rfl) ⟨810278, by rfl⟩ : syracuseStep 1080371 = 1620557) B1620557
theorem B719939 : Blo 718322 719939 := bstep (se 1 (by rfl) ⟨539954, by rfl⟩ : syracuseStep 719939 = 1079909) B1079909
theorem B4684877 : Blo 718322 4684877 := bstep (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) B1756829
theorem B1080401 : Blo 718322 1080401 := bstep (se 2 (by rfl) ⟨405150, by rfl⟩ : syracuseStep 1080401 = 810301) B810301
theorem B719955 : Blo 718322 719955 := bstep (se 1 (by rfl) ⟨539966, by rfl⟩ : syracuseStep 719955 = 1079933) B1079933
theorem B719971 : Blo 718322 719971 := bstep (se 1 (by rfl) ⟨539978, by rfl⟩ : syracuseStep 719971 = 1079957) B1079957
theorem B1080419 : Blo 718322 1080419 := bstep (se 1 (by rfl) ⟨810314, by rfl⟩ : syracuseStep 1080419 = 1620629) B1620629
theorem B719987 : Blo 718322 719987 := bstep (se 1 (by rfl) ⟨539990, by rfl⟩ : syracuseStep 719987 = 1079981) B1079981
theorem B1080449 : Blo 718322 1080449 := bstep (se 2 (by rfl) ⟨405168, by rfl⟩ : syracuseStep 1080449 = 810337) B810337
theorem B720003 : Blo 718322 720003 := bstep (se 1 (by rfl) ⟨540002, by rfl⟩ : syracuseStep 720003 = 1080005) B1080005
theorem B720019 : Blo 718322 720019 := bstep (se 1 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 720019 = 1080029) B1080029
theorem B1080467 : Blo 718322 1080467 := bstep (se 1 (by rfl) ⟨810350, by rfl⟩ : syracuseStep 1080467 = 1620701) B1620701
theorem B720035 : Blo 718322 720035 := bstep (se 1 (by rfl) ⟨540026, by rfl⟩ : syracuseStep 720035 = 1080053) B1080053
theorem B1080497 : Blo 718322 1080497 := bstep (se 2 (by rfl) ⟨405186, by rfl⟩ : syracuseStep 1080497 = 810373) B810373
theorem B720051 : Blo 718322 720051 := bstep (se 1 (by rfl) ⟨540038, by rfl⟩ : syracuseStep 720051 = 1080077) B1080077
theorem B720067 : Blo 718322 720067 := bstep (se 1 (by rfl) ⟨540050, by rfl⟩ : syracuseStep 720067 = 1080101) B1080101
theorem B1080515 : Blo 718322 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B720083 : Blo 718322 720083 := bstep (se 1 (by rfl) ⟨540062, by rfl⟩ : syracuseStep 720083 = 1080125) B1080125
theorem B1080545 : Blo 718322 1080545 := bstep (se 2 (by rfl) ⟨405204, by rfl⟩ : syracuseStep 1080545 = 810409) B810409
theorem B720099 : Blo 718322 720099 := bstep (se 1 (by rfl) ⟨540074, by rfl⟩ : syracuseStep 720099 = 1080149) B1080149
theorem B1539299 : Blo 718322 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B720115 : Blo 718322 720115 := bstep (se 1 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 720115 = 1080173) B1080173
theorem B1080563 : Blo 718322 1080563 := bstep (se 1 (by rfl) ⟨810422, by rfl⟩ : syracuseStep 1080563 = 1620845) B1620845
theorem B720131 : Blo 718322 720131 := bstep (se 1 (by rfl) ⟨540098, by rfl⟩ : syracuseStep 720131 = 1080197) B1080197
theorem B1080593 : Blo 718322 1080593 := bstep (se 2 (by rfl) ⟨405222, by rfl⟩ : syracuseStep 1080593 = 810445) B810445
theorem B720147 : Blo 718322 720147 := bstep (se 1 (by rfl) ⟨540110, by rfl⟩ : syracuseStep 720147 = 1080221) B1080221
theorem B720163 : Blo 718322 720163 := bstep (se 1 (by rfl) ⟨540122, by rfl⟩ : syracuseStep 720163 = 1080245) B1080245
theorem B1080611 : Blo 718322 1080611 := bstep (se 1 (by rfl) ⟨810458, by rfl⟩ : syracuseStep 1080611 = 1620917) B1620917
theorem B720179 : Blo 718322 720179 := bstep (se 1 (by rfl) ⟨540134, by rfl⟩ : syracuseStep 720179 = 1080269) B1080269
theorem B1080641 : Blo 718322 1080641 := bstep (se 2 (by rfl) ⟨405240, by rfl⟩ : syracuseStep 1080641 = 810481) B810481
theorem B720195 : Blo 718322 720195 := bstep (se 1 (by rfl) ⟨540146, by rfl⟩ : syracuseStep 720195 = 1080293) B1080293
theorem B6913349 : Blo 718322 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B6159685 : Blo 718322 6159685 := bstep (se 4 (by rfl) ⟨577470, by rfl⟩ : syracuseStep 6159685 = 1154941) B1154941
theorem B720211 : Blo 718322 720211 := bstep (se 1 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 720211 = 1080317) B1080317
theorem B1080659 : Blo 718322 1080659 := bstep (se 1 (by rfl) ⟨810494, by rfl⟩ : syracuseStep 1080659 = 1620989) B1620989
theorem B720227 : Blo 718322 720227 := bstep (se 1 (by rfl) ⟨540170, by rfl⟩ : syracuseStep 720227 = 1080341) B1080341
theorem B1080689 : Blo 718322 1080689 := bstep (se 2 (by rfl) ⟨405258, by rfl⟩ : syracuseStep 1080689 = 810517) B810517
theorem B720243 : Blo 718322 720243 := bstep (se 1 (by rfl) ⟨540182, by rfl⟩ : syracuseStep 720243 = 1080365) B1080365
theorem B720259 : Blo 718322 720259 := bstep (se 1 (by rfl) ⟨540194, by rfl⟩ : syracuseStep 720259 = 1080389) B1080389
theorem B1080707 : Blo 718322 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B720275 : Blo 718322 720275 := bstep (se 1 (by rfl) ⟨540206, by rfl⟩ : syracuseStep 720275 = 1080413) B1080413
theorem B1080737 : Blo 718322 1080737 := bstep (se 2 (by rfl) ⟨405276, by rfl⟩ : syracuseStep 1080737 = 810553) B810553
theorem B720291 : Blo 718322 720291 := bstep (se 1 (by rfl) ⟨540218, by rfl⟩ : syracuseStep 720291 = 1080437) B1080437
theorem B720307 : Blo 718322 720307 := bstep (se 1 (by rfl) ⟨540230, by rfl⟩ : syracuseStep 720307 = 1080461) B1080461
theorem B1080755 : Blo 718322 1080755 := bstep (se 1 (by rfl) ⟨810566, by rfl⟩ : syracuseStep 1080755 = 1621133) B1621133
theorem B720323 : Blo 718322 720323 := bstep (se 1 (by rfl) ⟨540242, by rfl⟩ : syracuseStep 720323 = 1080485) B1080485
theorem B1080785 : Blo 718322 1080785 := bstep (se 2 (by rfl) ⟨405294, by rfl⟩ : syracuseStep 1080785 = 810589) B810589
theorem B720339 : Blo 718322 720339 := bstep (se 1 (by rfl) ⟨540254, by rfl⟩ : syracuseStep 720339 = 1080509) B1080509
theorem B720355 : Blo 718322 720355 := bstep (se 1 (by rfl) ⟨540266, by rfl⟩ : syracuseStep 720355 = 1080533) B1080533
theorem B1080803 : Blo 718322 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B720371 : Blo 718322 720371 := bstep (se 1 (by rfl) ⟨540278, by rfl⟩ : syracuseStep 720371 = 1080557) B1080557
theorem B1080833 : Blo 718322 1080833 := bstep (se 2 (by rfl) ⟨405312, by rfl⟩ : syracuseStep 1080833 = 810625) B810625
theorem B720387 : Blo 718322 720387 := bstep (se 1 (by rfl) ⟨540290, by rfl⟩ : syracuseStep 720387 = 1080581) B1080581
theorem B720403 : Blo 718322 720403 := bstep (se 1 (by rfl) ⟨540302, by rfl⟩ : syracuseStep 720403 = 1080605) B1080605
theorem B1080851 : Blo 718322 1080851 := bstep (se 1 (by rfl) ⟨810638, by rfl⟩ : syracuseStep 1080851 = 1621277) B1621277
theorem B720419 : Blo 718322 720419 := bstep (se 1 (by rfl) ⟨540314, by rfl⟩ : syracuseStep 720419 = 1080629) B1080629
theorem B1080881 : Blo 718322 1080881 := bstep (se 2 (by rfl) ⟨405330, by rfl⟩ : syracuseStep 1080881 = 810661) B810661
theorem B720435 : Blo 718322 720435 := bstep (se 1 (by rfl) ⟨540326, by rfl⟩ : syracuseStep 720435 = 1080653) B1080653
theorem B720451 : Blo 718322 720451 := bstep (se 1 (by rfl) ⟨540338, by rfl⟩ : syracuseStep 720451 = 1080677) B1080677
theorem B1080899 : Blo 718322 1080899 := bstep (se 1 (by rfl) ⟨810674, by rfl⟩ : syracuseStep 1080899 = 1621349) B1621349
theorem B720467 : Blo 718322 720467 := bstep (se 1 (by rfl) ⟨540350, by rfl⟩ : syracuseStep 720467 = 1080701) B1080701
theorem B1080929 : Blo 718322 1080929 := bstep (se 2 (by rfl) ⟨405348, by rfl⟩ : syracuseStep 1080929 = 810697) B810697
theorem B720483 : Blo 718322 720483 := bstep (se 1 (by rfl) ⟨540362, by rfl⟩ : syracuseStep 720483 = 1080725) B1080725
theorem B720499 : Blo 718322 720499 := bstep (se 1 (by rfl) ⟨540374, by rfl⟩ : syracuseStep 720499 = 1080749) B1080749
theorem B1080947 : Blo 718322 1080947 := bstep (se 1 (by rfl) ⟨810710, by rfl⟩ : syracuseStep 1080947 = 1621421) B1621421
theorem B720515 : Blo 718322 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B1080977 : Blo 718322 1080977 := bstep (se 2 (by rfl) ⟨405366, by rfl⟩ : syracuseStep 1080977 = 810733) B810733
theorem B720531 : Blo 718322 720531 := bstep (se 1 (by rfl) ⟨540398, by rfl⟩ : syracuseStep 720531 = 1080797) B1080797
theorem B3636899 : Blo 718322 3636899 := bstep (se 1 (by rfl) ⟨2727674, by rfl⟩ : syracuseStep 3636899 = 5455349) B5455349
theorem B720547 : Blo 718322 720547 := bstep (se 1 (by rfl) ⟨540410, by rfl⟩ : syracuseStep 720547 = 1080821) B1080821
theorem B1080995 : Blo 718322 1080995 := bstep (se 1 (by rfl) ⟨810746, by rfl⟩ : syracuseStep 1080995 = 1621493) B1621493
theorem B720563 : Blo 718322 720563 := bstep (se 1 (by rfl) ⟨540422, by rfl⟩ : syracuseStep 720563 = 1080845) B1080845
theorem B1081025 : Blo 718322 1081025 := bstep (se 2 (by rfl) ⟨405384, by rfl⟩ : syracuseStep 1081025 = 810769) B810769
theorem B720579 : Blo 718322 720579 := bstep (se 1 (by rfl) ⟨540434, by rfl⟩ : syracuseStep 720579 = 1080869) B1080869
theorem B720595 : Blo 718322 720595 := bstep (se 1 (by rfl) ⟨540446, by rfl⟩ : syracuseStep 720595 = 1080893) B1080893
theorem B1081043 : Blo 718322 1081043 := bstep (se 1 (by rfl) ⟨810782, by rfl⟩ : syracuseStep 1081043 = 1621565) B1621565
theorem B720611 : Blo 718322 720611 := bstep (se 1 (by rfl) ⟨540458, by rfl⟩ : syracuseStep 720611 = 1080917) B1080917
theorem B1081073 : Blo 718322 1081073 := bstep (se 2 (by rfl) ⟨405402, by rfl⟩ : syracuseStep 1081073 = 810805) B810805
theorem B720627 : Blo 718322 720627 := bstep (se 1 (by rfl) ⟨540470, by rfl⟩ : syracuseStep 720627 = 1080941) B1080941
theorem B720643 : Blo 718322 720643 := bstep (se 1 (by rfl) ⟨540482, by rfl⟩ : syracuseStep 720643 = 1080965) B1080965
theorem B1081091 : Blo 718322 1081091 := bstep (se 1 (by rfl) ⟨810818, by rfl⟩ : syracuseStep 1081091 = 1621637) B1621637
theorem B720659 : Blo 718322 720659 := bstep (se 1 (by rfl) ⟨540494, by rfl⟩ : syracuseStep 720659 = 1080989) B1080989
theorem B1081121 : Blo 718322 1081121 := bstep (se 2 (by rfl) ⟨405420, by rfl⟩ : syracuseStep 1081121 = 810841) B810841
theorem B720675 : Blo 718322 720675 := bstep (se 1 (by rfl) ⟨540506, by rfl⟩ : syracuseStep 720675 = 1081013) B1081013
theorem B720691 : Blo 718322 720691 := bstep (se 1 (by rfl) ⟨540518, by rfl⟩ : syracuseStep 720691 = 1081037) B1081037
theorem B1081139 : Blo 718322 1081139 := bstep (se 1 (by rfl) ⟨810854, by rfl⟩ : syracuseStep 1081139 = 1621709) B1621709
theorem B720707 : Blo 718322 720707 := bstep (se 1 (by rfl) ⟨540530, by rfl⟩ : syracuseStep 720707 = 1081061) B1081061
theorem B2424653 : Blo 718322 2424653 := bstep (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) B909245
theorem B1081169 : Blo 718322 1081169 := bstep (se 2 (by rfl) ⟨405438, by rfl⟩ : syracuseStep 1081169 = 810877) B810877
theorem B720723 : Blo 718322 720723 := bstep (se 1 (by rfl) ⟨540542, by rfl⟩ : syracuseStep 720723 = 1081085) B1081085
theorem B1212259 : Blo 718322 1212259 := bstep (se 1 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 1212259 = 1818389) B1818389
theorem B720739 : Blo 718322 720739 := bstep (se 1 (by rfl) ⟨540554, by rfl⟩ : syracuseStep 720739 = 1081109) B1081109
theorem B1081187 : Blo 718322 1081187 := bstep (se 1 (by rfl) ⟨810890, by rfl⟩ : syracuseStep 1081187 = 1621781) B1621781
theorem B2195309 : Blo 718322 2195309 := bstep (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) B823241
theorem B720755 : Blo 718322 720755 := bstep (se 1 (by rfl) ⟨540566, by rfl⟩ : syracuseStep 720755 = 1081133) B1081133
theorem B1081217 : Blo 718322 1081217 := bstep (se 2 (by rfl) ⟨405456, by rfl⟩ : syracuseStep 1081217 = 810913) B810913
theorem B2424707 : Blo 718322 2424707 := bstep (se 1 (by rfl) ⟨1818530, by rfl⟩ : syracuseStep 2424707 = 3637061) B3637061
theorem B720771 : Blo 718322 720771 := bstep (se 1 (by rfl) ⟨540578, by rfl⟩ : syracuseStep 720771 = 1081157) B1081157
theorem B720787 : Blo 718322 720787 := bstep (se 1 (by rfl) ⟨540590, by rfl⟩ : syracuseStep 720787 = 1081181) B1081181
theorem B1081235 : Blo 718322 1081235 := bstep (se 1 (by rfl) ⟨810926, by rfl⟩ : syracuseStep 1081235 = 1621853) B1621853
theorem B720803 : Blo 718322 720803 := bstep (se 1 (by rfl) ⟨540602, by rfl⟩ : syracuseStep 720803 = 1081205) B1081205
theorem B1081265 : Blo 718322 1081265 := bstep (se 2 (by rfl) ⟨405474, by rfl⟩ : syracuseStep 1081265 = 810949) B810949
theorem B720819 : Blo 718322 720819 := bstep (se 1 (by rfl) ⟨540614, by rfl⟩ : syracuseStep 720819 = 1081229) B1081229
theorem B720835 : Blo 718322 720835 := bstep (se 1 (by rfl) ⟨540626, by rfl⟩ : syracuseStep 720835 = 1081253) B1081253
theorem B1081283 : Blo 718322 1081283 := bstep (se 1 (by rfl) ⟨810962, by rfl⟩ : syracuseStep 1081283 = 1621925) B1621925
theorem B720851 : Blo 718322 720851 := bstep (se 1 (by rfl) ⟨540638, by rfl⟩ : syracuseStep 720851 = 1081277) B1081277
theorem B1081313 : Blo 718322 1081313 := bstep (se 2 (by rfl) ⟨405492, by rfl⟩ : syracuseStep 1081313 = 810985) B810985
theorem B720867 : Blo 718322 720867 := bstep (se 1 (by rfl) ⟨540650, by rfl⟩ : syracuseStep 720867 = 1081301) B1081301
theorem B1212401 : Blo 718322 1212401 := bstep (se 2 (by rfl) ⟨454650, by rfl⟩ : syracuseStep 1212401 = 909301) B909301
theorem B720883 : Blo 718322 720883 := bstep (se 1 (by rfl) ⟨540662, by rfl⟩ : syracuseStep 720883 = 1081325) B1081325
theorem B1081331 : Blo 718322 1081331 := bstep (se 1 (by rfl) ⟨810998, by rfl⟩ : syracuseStep 1081331 = 1621997) B1621997
theorem B1081355 : Blo 718322 1081355 := bstep (se 1 (by rfl) ⟨811016, by rfl⟩ : syracuseStep 1081355 = 1622033) B1622033
theorem B720907 : Blo 718322 720907 := bstep (se 1 (by rfl) ⟨540680, by rfl⟩ : syracuseStep 720907 = 1081361) B1081361
theorem B1081367 : Blo 718322 1081367 := bstep (se 1 (by rfl) ⟨811025, by rfl⟩ : syracuseStep 1081367 = 1622051) B1622051
theorem B720919 : Blo 718322 720919 := bstep (se 1 (by rfl) ⟨540689, by rfl⟩ : syracuseStep 720919 = 1081379) B1081379
theorem B720939 : Blo 718322 720939 := bstep (se 1 (by rfl) ⟨540704, by rfl⟩ : syracuseStep 720939 = 1081409) B1081409
theorem B720951 : Blo 718322 720951 := bstep (se 1 (by rfl) ⟨540713, by rfl⟩ : syracuseStep 720951 = 1081427) B1081427
theorem B720971 : Blo 718322 720971 := bstep (se 1 (by rfl) ⟨540728, by rfl⟩ : syracuseStep 720971 = 1081457) B1081457
theorem B720983 : Blo 718322 720983 := bstep (se 1 (by rfl) ⟨540737, by rfl⟩ : syracuseStep 720983 = 1081475) B1081475
theorem B1081433 : Blo 718322 1081433 := bstep (se 2 (by rfl) ⟨405537, by rfl⟩ : syracuseStep 1081433 = 811075) B811075
theorem B721003 : Blo 718322 721003 := bstep (se 1 (by rfl) ⟨540752, by rfl⟩ : syracuseStep 721003 = 1081505) B1081505
theorem B721015 : Blo 718322 721015 := bstep (se 1 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 721015 = 1081523) B1081523
theorem B721035 : Blo 718322 721035 := bstep (se 1 (by rfl) ⟨540776, by rfl⟩ : syracuseStep 721035 = 1081553) B1081553
theorem B721047 : Blo 718322 721047 := bstep (se 1 (by rfl) ⟨540785, by rfl⟩ : syracuseStep 721047 = 1081571) B1081571
theorem B721067 : Blo 718322 721067 := bstep (se 1 (by rfl) ⟨540800, by rfl⟩ : syracuseStep 721067 = 1081601) B1081601
theorem B721079 : Blo 718322 721079 := bstep (se 1 (by rfl) ⟨540809, by rfl⟩ : syracuseStep 721079 = 1081619) B1081619
theorem B1081547 : Blo 718322 1081547 := bstep (se 1 (by rfl) ⟨811160, by rfl⟩ : syracuseStep 1081547 = 1622321) B1622321
theorem B721099 : Blo 718322 721099 := bstep (se 1 (by rfl) ⟨540824, by rfl⟩ : syracuseStep 721099 = 1081649) B1081649
theorem B1081559 : Blo 718322 1081559 := bstep (se 1 (by rfl) ⟨811169, by rfl⟩ : syracuseStep 1081559 = 1622339) B1622339
theorem B721111 : Blo 718322 721111 := bstep (se 1 (by rfl) ⟨540833, by rfl⟩ : syracuseStep 721111 = 1081667) B1081667
theorem B721131 : Blo 718322 721131 := bstep (se 1 (by rfl) ⟨540848, by rfl⟩ : syracuseStep 721131 = 1081697) B1081697
theorem B721143 : Blo 718322 721143 := bstep (se 1 (by rfl) ⟨540857, by rfl⟩ : syracuseStep 721143 = 1081715) B1081715
theorem B721163 : Blo 718322 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B721175 : Blo 718322 721175 := bstep (se 1 (by rfl) ⟨540881, by rfl⟩ : syracuseStep 721175 = 1081763) B1081763
theorem B1081625 : Blo 718322 1081625 := bstep (se 2 (by rfl) ⟨405609, by rfl⟩ : syracuseStep 1081625 = 811219) B811219
theorem B721195 : Blo 718322 721195 := bstep (se 1 (by rfl) ⟨540896, by rfl⟩ : syracuseStep 721195 = 1081793) B1081793
theorem B2425139 : Blo 718322 2425139 := bstep (se 1 (by rfl) ⟨1818854, by rfl⟩ : syracuseStep 2425139 = 3637709) B3637709
theorem B721207 : Blo 718322 721207 := bstep (se 1 (by rfl) ⟨540905, by rfl⟩ : syracuseStep 721207 = 1081811) B1081811
theorem B721227 : Blo 718322 721227 := bstep (se 1 (by rfl) ⟨540920, by rfl⟩ : syracuseStep 721227 = 1081841) B1081841
theorem B721239 : Blo 718322 721239 := bstep (se 1 (by rfl) ⟨540929, by rfl⟩ : syracuseStep 721239 = 1081859) B1081859
theorem B721259 : Blo 718322 721259 := bstep (se 1 (by rfl) ⟨540944, by rfl⟩ : syracuseStep 721259 = 1081889) B1081889
theorem B721271 : Blo 718322 721271 := bstep (se 1 (by rfl) ⟨540953, by rfl⟩ : syracuseStep 721271 = 1081907) B1081907
theorem B1638785 : Blo 718322 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B1081739 : Blo 718322 1081739 := bstep (se 1 (by rfl) ⟨811304, by rfl⟩ : syracuseStep 1081739 = 1622609) B1622609
theorem B721291 : Blo 718322 721291 := bstep (se 1 (by rfl) ⟨540968, by rfl⟩ : syracuseStep 721291 = 1081937) B1081937
theorem B1081751 : Blo 718322 1081751 := bstep (se 1 (by rfl) ⟨811313, by rfl⟩ : syracuseStep 1081751 = 1622627) B1622627
theorem B721303 : Blo 718322 721303 := bstep (se 1 (by rfl) ⟨540977, by rfl⟩ : syracuseStep 721303 = 1081955) B1081955
theorem B721323 : Blo 718322 721323 := bstep (se 1 (by rfl) ⟨540992, by rfl⟩ : syracuseStep 721323 = 1081985) B1081985
theorem B721335 : Blo 718322 721335 := bstep (se 1 (by rfl) ⟨541001, by rfl⟩ : syracuseStep 721335 = 1082003) B1082003
theorem B721355 : Blo 718322 721355 := bstep (se 1 (by rfl) ⟨541016, by rfl⟩ : syracuseStep 721355 = 1082033) B1082033
theorem B1212887 : Blo 718322 1212887 := bstep (se 1 (by rfl) ⟨909665, by rfl⟩ : syracuseStep 1212887 = 1819331) B1819331
theorem B1081817 : Blo 718322 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B721367 : Blo 718322 721367 := bstep (se 1 (by rfl) ⟨541025, by rfl⟩ : syracuseStep 721367 = 1082051) B1082051
theorem B721387 : Blo 718322 721387 := bstep (se 1 (by rfl) ⟨541040, by rfl⟩ : syracuseStep 721387 = 1082081) B1082081
theorem B721399 : Blo 718322 721399 := bstep (se 1 (by rfl) ⟨541049, by rfl⟩ : syracuseStep 721399 = 1082099) B1082099
theorem B721419 : Blo 718322 721419 := bstep (se 1 (by rfl) ⟨541064, by rfl⟩ : syracuseStep 721419 = 1082129) B1082129
theorem B1245719 : Blo 718322 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B721431 : Blo 718322 721431 := bstep (se 1 (by rfl) ⟨541073, by rfl⟩ : syracuseStep 721431 = 1082147) B1082147
theorem B721451 : Blo 718322 721451 := bstep (se 1 (by rfl) ⟨541088, by rfl⟩ : syracuseStep 721451 = 1082177) B1082177
theorem B721463 : Blo 718322 721463 := bstep (se 1 (by rfl) ⟨541097, by rfl⟩ : syracuseStep 721463 = 1082195) B1082195
theorem B2425409 : Blo 718322 2425409 := bstep (se 2 (by rfl) ⟨909528, by rfl⟩ : syracuseStep 2425409 = 1819057) B1819057
theorem B1081931 : Blo 718322 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B721483 : Blo 718322 721483 := bstep (se 1 (by rfl) ⟨541112, by rfl⟩ : syracuseStep 721483 = 1082225) B1082225
theorem B1213015 : Blo 718322 1213015 := bstep (se 1 (by rfl) ⟨909761, by rfl⟩ : syracuseStep 1213015 = 1819523) B1819523
theorem B1081943 : Blo 718322 1081943 := bstep (se 1 (by rfl) ⟨811457, by rfl⟩ : syracuseStep 1081943 = 1622915) B1622915
theorem B721495 : Blo 718322 721495 := bstep (se 1 (by rfl) ⟨541121, by rfl⟩ : syracuseStep 721495 = 1082243) B1082243
theorem B721515 : Blo 718322 721515 := bstep (se 1 (by rfl) ⟨541136, by rfl⟩ : syracuseStep 721515 = 1082273) B1082273
theorem B721527 : Blo 718322 721527 := bstep (se 1 (by rfl) ⟨541145, by rfl⟩ : syracuseStep 721527 = 1082291) B1082291
theorem B721547 : Blo 718322 721547 := bstep (se 1 (by rfl) ⟨541160, by rfl⟩ : syracuseStep 721547 = 1082321) B1082321
theorem B721559 : Blo 718322 721559 := bstep (se 1 (by rfl) ⟨541169, by rfl⟩ : syracuseStep 721559 = 1082339) B1082339
theorem B1082009 : Blo 718322 1082009 := bstep (se 2 (by rfl) ⟨405753, by rfl⟩ : syracuseStep 1082009 = 811507) B811507
theorem B721579 : Blo 718322 721579 := bstep (se 1 (by rfl) ⟨541184, by rfl⟩ : syracuseStep 721579 = 1082369) B1082369
theorem B721591 : Blo 718322 721591 := bstep (se 1 (by rfl) ⟨541193, by rfl⟩ : syracuseStep 721591 = 1082387) B1082387
theorem B721611 : Blo 718322 721611 := bstep (se 1 (by rfl) ⟨541208, by rfl⟩ : syracuseStep 721611 = 1082417) B1082417
theorem B721623 : Blo 718322 721623 := bstep (se 1 (by rfl) ⟨541217, by rfl⟩ : syracuseStep 721623 = 1082435) B1082435
theorem B721643 : Blo 718322 721643 := bstep (se 1 (by rfl) ⟨541232, by rfl⟩ : syracuseStep 721643 = 1082465) B1082465
theorem B721655 : Blo 718322 721655 := bstep (se 1 (by rfl) ⟨541241, by rfl⟩ : syracuseStep 721655 = 1082483) B1082483
theorem B1082123 : Blo 718322 1082123 := bstep (se 1 (by rfl) ⟨811592, by rfl⟩ : syracuseStep 1082123 = 1623185) B1623185
theorem B721675 : Blo 718322 721675 := bstep (se 1 (by rfl) ⟨541256, by rfl⟩ : syracuseStep 721675 = 1082513) B1082513
theorem B3638033 : Blo 718322 3638033 := bstep (se 2 (by rfl) ⟨1364262, by rfl⟩ : syracuseStep 3638033 = 2728525) B2728525
theorem B1082135 : Blo 718322 1082135 := bstep (se 1 (by rfl) ⟨811601, by rfl⟩ : syracuseStep 1082135 = 1623203) B1623203
theorem B721687 : Blo 718322 721687 := bstep (se 1 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 721687 = 1082531) B1082531
theorem B721707 : Blo 718322 721707 := bstep (se 1 (by rfl) ⟨541280, by rfl⟩ : syracuseStep 721707 = 1082561) B1082561
theorem B721719 : Blo 718322 721719 := bstep (se 1 (by rfl) ⟨541289, by rfl⟩ : syracuseStep 721719 = 1082579) B1082579
theorem B1540939 : Blo 718322 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B721739 : Blo 718322 721739 := bstep (se 1 (by rfl) ⟨541304, by rfl⟩ : syracuseStep 721739 = 1082609) B1082609
theorem B721751 : Blo 718322 721751 := bstep (se 1 (by rfl) ⟨541313, by rfl⟩ : syracuseStep 721751 = 1082627) B1082627
theorem B1082201 : Blo 718322 1082201 := bstep (se 2 (by rfl) ⟨405825, by rfl⟩ : syracuseStep 1082201 = 811651) B811651
theorem B721771 : Blo 718322 721771 := bstep (se 1 (by rfl) ⟨541328, by rfl⟩ : syracuseStep 721771 = 1082657) B1082657
theorem B721783 : Blo 718322 721783 := bstep (se 1 (by rfl) ⟨541337, by rfl⟩ : syracuseStep 721783 = 1082675) B1082675
theorem B721803 : Blo 718322 721803 := bstep (se 1 (by rfl) ⟨541352, by rfl⟩ : syracuseStep 721803 = 1082705) B1082705
theorem B721815 : Blo 718322 721815 := bstep (se 1 (by rfl) ⟨541361, by rfl⟩ : syracuseStep 721815 = 1082723) B1082723
theorem B721835 : Blo 718322 721835 := bstep (se 1 (by rfl) ⟨541376, by rfl⟩ : syracuseStep 721835 = 1082753) B1082753
theorem B3638195 : Blo 718322 3638195 := bstep (se 1 (by rfl) ⟨2728646, by rfl⟩ : syracuseStep 3638195 = 5457293) B5457293
theorem B22217651 : Blo 718322 22217651 := bstep (se 1 (by rfl) ⟨16663238, by rfl⟩ : syracuseStep 22217651 = 33326477) B33326477
theorem B721847 : Blo 718322 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B1082315 : Blo 718322 1082315 := bstep (se 1 (by rfl) ⟨811736, by rfl⟩ : syracuseStep 1082315 = 1623473) B1623473
theorem B721867 : Blo 718322 721867 := bstep (se 1 (by rfl) ⟨541400, by rfl⟩ : syracuseStep 721867 = 1082801) B1082801
theorem B1082327 : Blo 718322 1082327 := bstep (se 1 (by rfl) ⟨811745, by rfl⟩ : syracuseStep 1082327 = 1623491) B1623491
theorem B721879 : Blo 718322 721879 := bstep (se 1 (by rfl) ⟨541409, by rfl⟩ : syracuseStep 721879 = 1082819) B1082819
theorem B721899 : Blo 718322 721899 := bstep (se 1 (by rfl) ⟨541424, by rfl⟩ : syracuseStep 721899 = 1082849) B1082849
theorem B721911 : Blo 718322 721911 := bstep (se 1 (by rfl) ⟨541433, by rfl⟩ : syracuseStep 721911 = 1082867) B1082867
theorem B721931 : Blo 718322 721931 := bstep (se 1 (by rfl) ⟨541448, by rfl⟩ : syracuseStep 721931 = 1082897) B1082897
theorem B721943 : Blo 718322 721943 := bstep (se 1 (by rfl) ⟨541457, by rfl⟩ : syracuseStep 721943 = 1082915) B1082915
theorem B1082393 : Blo 718322 1082393 := bstep (se 2 (by rfl) ⟨405897, by rfl⟩ : syracuseStep 1082393 = 811795) B811795
theorem B721963 : Blo 718322 721963 := bstep (se 1 (by rfl) ⟨541472, by rfl⟩ : syracuseStep 721963 = 1082945) B1082945
theorem B721975 : Blo 718322 721975 := bstep (se 1 (by rfl) ⟨541481, by rfl⟩ : syracuseStep 721975 = 1082963) B1082963
theorem B721995 : Blo 718322 721995 := bstep (se 1 (by rfl) ⟨541496, by rfl⟩ : syracuseStep 721995 = 1082993) B1082993
theorem B722007 : Blo 718322 722007 := bstep (se 1 (by rfl) ⟨541505, by rfl⟩ : syracuseStep 722007 = 1083011) B1083011
theorem B2425949 : Blo 718322 2425949 := bstep (se 3 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 2425949 = 909731) B909731
theorem B722027 : Blo 718322 722027 := bstep (se 1 (by rfl) ⟨541520, by rfl⟩ : syracuseStep 722027 = 1083041) B1083041
theorem B722039 : Blo 718322 722039 := bstep (se 1 (by rfl) ⟨541529, by rfl⟩ : syracuseStep 722039 = 1083059) B1083059
theorem B3081347 : Blo 718322 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B1082507 : Blo 718322 1082507 := bstep (se 1 (by rfl) ⟨811880, by rfl⟩ : syracuseStep 1082507 = 1623761) B1623761
theorem B722059 : Blo 718322 722059 := bstep (se 1 (by rfl) ⟨541544, by rfl⟩ : syracuseStep 722059 = 1083089) B1083089
theorem B1082519 : Blo 718322 1082519 := bstep (se 1 (by rfl) ⟨811889, by rfl⟩ : syracuseStep 1082519 = 1623779) B1623779
theorem B722071 : Blo 718322 722071 := bstep (se 1 (by rfl) ⟨541553, by rfl⟩ : syracuseStep 722071 = 1083107) B1083107
theorem B722091 : Blo 718322 722091 := bstep (se 1 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 722091 = 1083137) B1083137
theorem B722103 : Blo 718322 722103 := bstep (se 1 (by rfl) ⟨541577, by rfl⟩ : syracuseStep 722103 = 1083155) B1083155
theorem B1213643 : Blo 718322 1213643 := bstep (se 1 (by rfl) ⟨910232, by rfl⟩ : syracuseStep 1213643 = 1820465) B1820465
theorem B722123 : Blo 718322 722123 := bstep (se 1 (by rfl) ⟨541592, by rfl⟩ : syracuseStep 722123 = 1083185) B1083185
theorem B722135 : Blo 718322 722135 := bstep (se 1 (by rfl) ⟨541601, by rfl⟩ : syracuseStep 722135 = 1083203) B1083203
theorem B1082585 : Blo 718322 1082585 := bstep (se 2 (by rfl) ⟨405969, by rfl⟩ : syracuseStep 1082585 = 811939) B811939
theorem B722155 : Blo 718322 722155 := bstep (se 1 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 722155 = 1083233) B1083233
theorem B722167 : Blo 718322 722167 := bstep (se 1 (by rfl) ⟨541625, by rfl⟩ : syracuseStep 722167 = 1083251) B1083251
theorem B6161669 : Blo 718322 6161669 := bstep (se 4 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 6161669 = 1155313) B1155313
theorem B722187 : Blo 718322 722187 := bstep (se 1 (by rfl) ⟨541640, by rfl⟩ : syracuseStep 722187 = 1083281) B1083281
theorem B722199 : Blo 718322 722199 := bstep (se 1 (by rfl) ⟨541649, by rfl⟩ : syracuseStep 722199 = 1083299) B1083299
theorem B722219 : Blo 718322 722219 := bstep (se 1 (by rfl) ⟨541664, by rfl⟩ : syracuseStep 722219 = 1083329) B1083329
theorem B722231 : Blo 718322 722231 := bstep (se 1 (by rfl) ⟨541673, by rfl⟩ : syracuseStep 722231 = 1083347) B1083347
theorem B1213771 : Blo 718322 1213771 := bstep (se 1 (by rfl) ⟨910328, by rfl⟩ : syracuseStep 1213771 = 1820657) B1820657
theorem B1082699 : Blo 718322 1082699 := bstep (se 1 (by rfl) ⟨812024, by rfl⟩ : syracuseStep 1082699 = 1624049) B1624049
theorem B722251 : Blo 718322 722251 := bstep (se 1 (by rfl) ⟨541688, by rfl⟩ : syracuseStep 722251 = 1083377) B1083377
theorem B1082711 : Blo 718322 1082711 := bstep (se 1 (by rfl) ⟨812033, by rfl⟩ : syracuseStep 1082711 = 1624067) B1624067
theorem B722263 : Blo 718322 722263 := bstep (se 1 (by rfl) ⟨541697, by rfl⟩ : syracuseStep 722263 = 1083395) B1083395
theorem B722283 : Blo 718322 722283 := bstep (se 1 (by rfl) ⟨541712, by rfl⟩ : syracuseStep 722283 = 1083425) B1083425
theorem B722295 : Blo 718322 722295 := bstep (se 1 (by rfl) ⟨541721, by rfl⟩ : syracuseStep 722295 = 1083443) B1083443
theorem B722315 : Blo 718322 722315 := bstep (se 1 (by rfl) ⟨541736, by rfl⟩ : syracuseStep 722315 = 1083473) B1083473
theorem B1082777 : Blo 718322 1082777 := bstep (se 2 (by rfl) ⟨406041, by rfl⟩ : syracuseStep 1082777 = 812083) B812083
theorem B1213913 : Blo 718322 1213913 := bstep (se 2 (by rfl) ⟨455217, by rfl⟩ : syracuseStep 1213913 = 910435) B910435
theorem B3081689 : Blo 718322 3081689 := bstep (se 2 (by rfl) ⟨1155633, by rfl⟩ : syracuseStep 3081689 = 2311267) B2311267
theorem B1082891 : Blo 718322 1082891 := bstep (se 1 (by rfl) ⟨812168, by rfl⟩ : syracuseStep 1082891 = 1624337) B1624337
theorem B1082903 : Blo 718322 1082903 := bstep (se 1 (by rfl) ⟨812177, by rfl⟩ : syracuseStep 1082903 = 1624355) B1624355
theorem B1214041 : Blo 718322 1214041 := bstep (se 2 (by rfl) ⟨455265, by rfl⟩ : syracuseStep 1214041 = 910531) B910531
theorem B1082969 : Blo 718322 1082969 := bstep (se 2 (by rfl) ⟨406113, by rfl⟩ : syracuseStep 1082969 = 812227) B812227
theorem B1083083 : Blo 718322 1083083 := bstep (se 1 (by rfl) ⟨812312, by rfl⟩ : syracuseStep 1083083 = 1624625) B1624625
theorem B1083095 : Blo 718322 1083095 := bstep (se 1 (by rfl) ⟨812321, by rfl⟩ : syracuseStep 1083095 = 1624643) B1624643
theorem B1083161 : Blo 718322 1083161 := bstep (se 2 (by rfl) ⟨406185, by rfl⟩ : syracuseStep 1083161 = 812371) B812371
theorem B3901259 : Blo 718322 3901259 := bstep (se 1 (by rfl) ⟨2925944, by rfl⟩ : syracuseStep 3901259 = 5851889) B5851889
theorem B1083275 : Blo 718322 1083275 := bstep (se 1 (by rfl) ⟨812456, by rfl⟩ : syracuseStep 1083275 = 1624913) B1624913
theorem B1083287 : Blo 718322 1083287 := bstep (se 1 (by rfl) ⟨812465, by rfl⟩ : syracuseStep 1083287 = 1624931) B1624931
theorem B1083353 : Blo 718322 1083353 := bstep (se 2 (by rfl) ⟨406257, by rfl⟩ : syracuseStep 1083353 = 812515) B812515
theorem B1542169 : Blo 718322 1542169 := bstep (se 2 (by rfl) ⟨578313, by rfl⟩ : syracuseStep 1542169 = 1156627) B1156627
theorem B1083467 : Blo 718322 1083467 := bstep (se 1 (by rfl) ⟨812600, by rfl⟩ : syracuseStep 1083467 = 1625201) B1625201
theorem B1083479 : Blo 718322 1083479 := bstep (se 1 (by rfl) ⟨812609, by rfl⟩ : syracuseStep 1083479 = 1625219) B1625219
theorem B1214615 : Blo 718322 1214615 := bstep (se 1 (by rfl) ⟨910961, by rfl⟩ : syracuseStep 1214615 = 1821923) B1821923
theorem B2427083 : Blo 718322 2427083 := bstep (se 1 (by rfl) ⟨1820312, by rfl⟩ : syracuseStep 2427083 = 3640625) B3640625
theorem B2459927 : Blo 718322 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B1214743 : Blo 718322 1214743 := bstep (se 1 (by rfl) ⟨911057, by rfl⟩ : syracuseStep 1214743 = 1822115) B1822115
theorem B2427353 : Blo 718322 2427353 := bstep (se 2 (by rfl) ⟨910257, by rfl⟩ : syracuseStep 2427353 = 1820515) B1820515
theorem B4393565 : Blo 718322 4393565 := bstep (se 3 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 4393565 = 1647587) B1647587
theorem B1641227 : Blo 718322 1641227 := bstep (se 1 (by rfl) ⟨1230920, by rfl⟩ : syracuseStep 1641227 = 2461841) B2461841
theorem B3640139 : Blo 718322 3640139 := bstep (se 1 (by rfl) ⟨2730104, by rfl⟩ : syracuseStep 3640139 = 5460209) B5460209
theorem B1215371 : Blo 718322 1215371 := bstep (se 1 (by rfl) ⟨911528, by rfl⟩ : syracuseStep 1215371 = 1823057) B1823057
theorem B1215499 : Blo 718322 1215499 := bstep (se 1 (by rfl) ⟨911624, by rfl⟩ : syracuseStep 1215499 = 1823249) B1823249
theorem B2428055 : Blo 718322 2428055 := bstep (se 1 (by rfl) ⟨1821041, by rfl⟩ : syracuseStep 2428055 = 3642083) B3642083
theorem B1215641 : Blo 718322 1215641 := bstep (se 2 (by rfl) ⟨455865, by rfl⟩ : syracuseStep 1215641 = 911731) B911731
theorem B1215769 : Blo 718322 1215769 := bstep (se 2 (by rfl) ⟨455913, by rfl⟩ : syracuseStep 1215769 = 911827) B911827
theorem B6557105 : Blo 718322 6557105 := bstep (se 2 (by rfl) ⟨2458914, by rfl⟩ : syracuseStep 6557105 = 4917829) B4917829
theorem B5475761 : Blo 718322 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B1642049 : Blo 718322 1642049 := bstep (se 2 (by rfl) ⟨615768, by rfl⟩ : syracuseStep 1642049 = 1231537) B1231537
theorem B2428595 : Blo 718322 2428595 := bstep (se 1 (by rfl) ⟨1821446, by rfl⟩ : syracuseStep 2428595 = 3642893) B3642893
theorem B1150681 : Blo 718322 1150681 := bstep (se 2 (by rfl) ⟨431505, by rfl⟩ : syracuseStep 1150681 = 863011) B863011
theorem B3116875 : Blo 718322 3116875 := bstep (se 1 (by rfl) ⟨2337656, by rfl⟩ : syracuseStep 3116875 = 4675313) B4675313
theorem B1216343 : Blo 718322 1216343 := bstep (se 1 (by rfl) ⟨912257, by rfl⟩ : syracuseStep 1216343 = 1824515) B1824515
theorem B5476247 : Blo 718322 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B2428865 : Blo 718322 2428865 := bstep (se 2 (by rfl) ⟨910824, by rfl⟩ : syracuseStep 2428865 = 1821649) B1821649
theorem B1216471 : Blo 718322 1216471 := bstep (se 1 (by rfl) ⟨912353, by rfl⟩ : syracuseStep 1216471 = 1824707) B1824707
theorem B4100057 : Blo 718322 4100057 := bstep (se 2 (by rfl) ⟨1537521, by rfl⟩ : syracuseStep 4100057 = 3075043) B3075043
theorem B4624685 : Blo 718322 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B2429405 : Blo 718322 2429405 := bstep (se 3 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 2429405 = 911027) B911027
theorem B3641921 : Blo 718322 3641921 := bstep (se 2 (by rfl) ⟨1365720, by rfl⟩ : syracuseStep 3641921 = 2731441) B2731441
theorem B1217099 : Blo 718322 1217099 := bstep (se 1 (by rfl) ⟨912824, by rfl⟩ : syracuseStep 1217099 = 1825649) B1825649
theorem B1217227 : Blo 718322 1217227 := bstep (se 1 (by rfl) ⟨912920, by rfl⟩ : syracuseStep 1217227 = 1825841) B1825841
theorem B3085073 : Blo 718322 3085073 := bstep (se 2 (by rfl) ⟨1156902, by rfl⟩ : syracuseStep 3085073 = 2313805) B2313805
theorem B1217369 : Blo 718322 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B1479563 : Blo 718322 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B1643417 : Blo 718322 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B1217497 : Blo 718322 1217497 := bstep (se 2 (by rfl) ⟨456561, by rfl⟩ : syracuseStep 1217497 = 913123) B913123
theorem B922699 : Blo 718322 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B12490163 : Blo 718322 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B1218071 : Blo 718322 1218071 := bstep (se 1 (by rfl) ⟨913553, by rfl⟩ : syracuseStep 1218071 = 1827107) B1827107
theorem B2430539 : Blo 718322 2430539 := bstep (se 1 (by rfl) ⟨1822904, by rfl⟩ : syracuseStep 2430539 = 3645809) B3645809
theorem B1218199 : Blo 718322 1218199 := bstep (se 1 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 1218199 = 1827299) B1827299
theorem B1644313 : Blo 718322 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B2430809 : Blo 718322 2430809 := bstep (se 2 (by rfl) ⟨911553, by rfl⟩ : syracuseStep 2430809 = 1823107) B1823107
theorem B6920113 : Blo 718322 6920113 := bstep (se 2 (by rfl) ⟨2595042, by rfl⟩ : syracuseStep 6920113 = 5190085) B5190085
theorem B7804849 : Blo 718322 7804849 := bstep (se 2 (by rfl) ⟨2926818, by rfl⟩ : syracuseStep 7804849 = 5853637) B5853637
theorem B2627635 : Blo 718322 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B1644695 : Blo 718322 1644695 := bstep (se 1 (by rfl) ⟨1233521, by rfl⟩ : syracuseStep 1644695 = 2467043) B2467043
theorem B1251545 : Blo 718322 1251545 := bstep (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) B938659
theorem B1218827 : Blo 718322 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B3643865 : Blo 718322 3643865 := bstep (se 2 (by rfl) ⟨1366449, by rfl⟩ : syracuseStep 3643865 = 2732899) B2732899
theorem B2595331 : Blo 718322 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B2431511 : Blo 718322 2431511 := bstep (se 1 (by rfl) ⟨1823633, by rfl⟩ : syracuseStep 2431511 = 3647267) B3647267
theorem B4102721 : Blo 718322 4102721 := bstep (se 2 (by rfl) ⟨1538520, by rfl⟩ : syracuseStep 4102721 = 3077041) B3077041
theorem B10394243 : Blo 718322 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B1383307 : Blo 718322 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B2432051 : Blo 718322 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B2923609 : Blo 718322 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B2432321 : Blo 718322 2432321 := bstep (se 2 (by rfl) ⟨912120, by rfl⟩ : syracuseStep 2432321 = 1824241) B1824241
theorem B4627813 : Blo 718322 4627813 := bstep (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) B867715
theorem B1023511 : Blo 718322 1023511 := bstep (se 1 (by rfl) ⟨767633, by rfl⟩ : syracuseStep 1023511 = 1535267) B1535267
theorem B1154711 : Blo 718322 1154711 := bstep (se 1 (by rfl) ⟨866033, by rfl⟩ : syracuseStep 1154711 = 1732067) B1732067
theorem B2924225 : Blo 718322 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B1154839 : Blo 718322 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B1154903 : Blo 718322 1154903 := bstep (se 1 (by rfl) ⟨866177, by rfl⟩ : syracuseStep 1154903 = 1732355) B1732355
theorem B2432861 : Blo 718322 2432861 := bstep (se 3 (by rfl) ⟨456161, by rfl⟩ : syracuseStep 2432861 = 912323) B912323
theorem B3645485 : Blo 718322 3645485 := bstep (se 3 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 3645485 = 1367057) B1367057
theorem B2728025 : Blo 718322 2728025 := bstep (se 2 (by rfl) ⟨1023009, by rfl⟩ : syracuseStep 2728025 = 2046019) B2046019
theorem B6168707 : Blo 718322 6168707 := bstep (se 1 (by rfl) ⟨4626530, by rfl⟩ : syracuseStep 6168707 = 9253061) B9253061
theorem B6234317 : Blo 718322 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B1843507 : Blo 718322 1843507 := bstep (se 1 (by rfl) ⟨1382630, by rfl⟩ : syracuseStep 1843507 = 2765261) B2765261
theorem B729463 : Blo 718322 729463 := bstep (se 1 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 729463 = 1094195) B1094195
theorem B2728343 : Blo 718322 2728343 := bstep (se 1 (by rfl) ⟨2046257, by rfl⟩ : syracuseStep 2728343 = 4092515) B4092515
theorem B5186369 : Blo 718322 5186369 := bstep (se 2 (by rfl) ⟨1944888, by rfl⟩ : syracuseStep 5186369 = 3889777) B3889777
theorem B1123159 : Blo 718322 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B2433995 : Blo 718322 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B2729011 : Blo 718322 2729011 := bstep (se 1 (by rfl) ⟨2046758, by rfl⟩ : syracuseStep 2729011 = 4093517) B4093517
theorem B2434265 : Blo 718322 2434265 := bstep (se 2 (by rfl) ⟨912849, by rfl⟩ : syracuseStep 2434265 = 1825699) B1825699
theorem B12330305 : Blo 718322 12330305 := bstep (se 2 (by rfl) ⟨4623864, by rfl⟩ : syracuseStep 12330305 = 9247729) B9247729
theorem B3515723 : Blo 718322 3515723 := bstep (se 1 (by rfl) ⟨2636792, by rfl⟩ : syracuseStep 3515723 = 5273585) B5273585
theorem B2303321 : Blo 718322 2303321 := bstep (se 2 (by rfl) ⟨863745, by rfl⟩ : syracuseStep 2303321 = 1727491) B1727491
theorem B3941905 : Blo 718322 3941905 := bstep (se 2 (by rfl) ⟨1478214, by rfl⟩ : syracuseStep 3941905 = 2956429) B2956429
theorem B1025561 : Blo 718322 1025561 := bstep (se 2 (by rfl) ⟨384585, by rfl⟩ : syracuseStep 1025561 = 769171) B769171
theorem B730667 : Blo 718322 730667 := bstep (se 1 (by rfl) ⟨548000, by rfl⟩ : syracuseStep 730667 = 1096001) B1096001
theorem B730891 : Blo 718322 730891 := bstep (se 1 (by rfl) ⟨548168, by rfl⟩ : syracuseStep 730891 = 1096337) B1096337
theorem B1156889 : Blo 718322 1156889 := bstep (se 2 (by rfl) ⟨433833, by rfl⟩ : syracuseStep 1156889 = 867667) B867667
theorem B9348965 : Blo 718322 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B2434967 : Blo 718322 2434967 := bstep (se 1 (by rfl) ⟨1826225, by rfl⟩ : syracuseStep 2434967 = 3652451) B3652451
theorem B20719637 : Blo 718322 20719637 := bstep (se 6 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 20719637 = 971233) B971233
theorem B3123251 : Blo 718322 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B2304065 : Blo 718322 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B1026199 : Blo 718322 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B2730257 : Blo 718322 2730257 := bstep (se 2 (by rfl) ⟨1023846, by rfl⟩ : syracuseStep 2730257 = 2047693) B2047693
theorem B2435507 : Blo 718322 2435507 := bstep (se 1 (by rfl) ⟨1826630, by rfl⟩ : syracuseStep 2435507 = 3653261) B3653261
theorem B1616345 : Blo 718322 1616345 := bstep (se 2 (by rfl) ⟨606129, by rfl⟩ : syracuseStep 1616345 = 1212259) B1212259
theorem B1616435 : Blo 718322 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B1616471 : Blo 718322 1616471 := bstep (se 1 (by rfl) ⟨1212353, by rfl⟩ : syracuseStep 1616471 = 2424707) B2424707
theorem B4991581 : Blo 718322 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B2435777 : Blo 718322 2435777 := bstep (se 2 (by rfl) ⟨913416, by rfl⟩ : syracuseStep 2435777 = 1826833) B1826833
theorem B5253893 : Blo 718322 5253893 := bstep (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) B985105
theorem B1616651 : Blo 718322 1616651 := bstep (se 1 (by rfl) ⟨1212488, by rfl⟩ : syracuseStep 1616651 = 2424977) B2424977
theorem B1616705 : Blo 718322 1616705 := bstep (se 2 (by rfl) ⟨606264, by rfl⟩ : syracuseStep 1616705 = 1212529) B1212529
theorem B2730955 : Blo 718322 2730955 := bstep (se 1 (by rfl) ⟨2048216, by rfl⟩ : syracuseStep 2730955 = 4096433) B4096433
theorem B1027019 : Blo 718322 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B5483537 : Blo 718322 5483537 := bstep (se 2 (by rfl) ⟨2056326, by rfl⟩ : syracuseStep 5483537 = 4112653) B4112653
theorem B1616921 : Blo 718322 1616921 := bstep (se 2 (by rfl) ⟨606345, by rfl⟩ : syracuseStep 1616921 = 1212691) B1212691
theorem B1617011 : Blo 718322 1617011 := bstep (se 1 (by rfl) ⟨1212758, by rfl⟩ : syracuseStep 1617011 = 2425517) B2425517
theorem B1617047 : Blo 718322 1617047 := bstep (se 1 (by rfl) ⟨1212785, by rfl⟩ : syracuseStep 1617047 = 2425571) B2425571
theorem B1387735 : Blo 718322 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B2731229 : Blo 718322 2731229 := bstep (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) B1024211
theorem B2436317 : Blo 718322 2436317 := bstep (se 3 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 2436317 = 913619) B913619
theorem B1617227 : Blo 718322 1617227 := bstep (se 1 (by rfl) ⟨1212920, by rfl⟩ : syracuseStep 1617227 = 2425841) B2425841
theorem B1617281 : Blo 718322 1617281 := bstep (se 2 (by rfl) ⟨606480, by rfl⟩ : syracuseStep 1617281 = 1212961) B1212961
theorem B1617497 : Blo 718322 1617497 := bstep (se 2 (by rfl) ⟨606561, by rfl⟩ : syracuseStep 1617497 = 1213123) B1213123
theorem B2600579 : Blo 718322 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B1617587 : Blo 718322 1617587 := bstep (se 1 (by rfl) ⟨1213190, by rfl⟩ : syracuseStep 1617587 = 2426381) B2426381
theorem B1617623 : Blo 718322 1617623 := bstep (se 1 (by rfl) ⟨1213217, by rfl⟩ : syracuseStep 1617623 = 2426435) B2426435
theorem B9219845 : Blo 718322 9219845 := bstep (se 4 (by rfl) ⟨864360, by rfl⟩ : syracuseStep 9219845 = 1728721) B1728721
theorem B4108097 : Blo 718322 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B3649373 : Blo 718322 3649373 := bstep (se 3 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 3649373 = 1368515) B1368515
theorem B1617803 : Blo 718322 1617803 := bstep (se 1 (by rfl) ⟨1213352, by rfl⟩ : syracuseStep 1617803 = 2426705) B2426705
theorem B6139799 : Blo 718322 6139799 := bstep (se 1 (by rfl) ⟨4604849, by rfl⟩ : syracuseStep 6139799 = 9209699) B9209699
theorem B2731927 : Blo 718322 2731927 := bstep (se 1 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 2731927 = 4097891) B4097891
theorem B1027993 : Blo 718322 1027993 := bstep (se 2 (by rfl) ⟨385497, by rfl⟩ : syracuseStep 1027993 = 770995) B770995
theorem B1617857 : Blo 718322 1617857 := bstep (se 2 (by rfl) ⟨606696, by rfl⟩ : syracuseStep 1617857 = 1213393) B1213393
theorem B2306141 : Blo 718322 2306141 := bstep (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) B864803
theorem B2961559 : Blo 718322 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B23376023 : Blo 718322 23376023 := bstep (se 1 (by rfl) ⟨17532017, by rfl⟩ : syracuseStep 23376023 = 35064035) B35064035
theorem B1618073 : Blo 718322 1618073 := bstep (se 2 (by rfl) ⟨606777, by rfl⟩ : syracuseStep 1618073 = 1213555) B1213555
theorem B1618163 : Blo 718322 1618163 := bstep (se 1 (by rfl) ⟨1213622, by rfl⟩ : syracuseStep 1618163 = 2427245) B2427245
theorem B10400005 : Blo 718322 10400005 := bstep (se 4 (by rfl) ⟨975000, by rfl⟩ : syracuseStep 10400005 = 1950001) B1950001
theorem B1618199 : Blo 718322 1618199 := bstep (se 1 (by rfl) ⟨1213649, by rfl⟩ : syracuseStep 1618199 = 2427299) B2427299
theorem B2437451 : Blo 718322 2437451 := bstep (se 1 (by rfl) ⟨1828088, by rfl⟩ : syracuseStep 2437451 = 3656177) B3656177
theorem B1618379 : Blo 718322 1618379 := bstep (se 1 (by rfl) ⟨1213784, by rfl⟩ : syracuseStep 1618379 = 2427569) B2427569
theorem B1618433 : Blo 718322 1618433 := bstep (se 2 (by rfl) ⟨606912, by rfl⟩ : syracuseStep 1618433 = 1213825) B1213825
theorem B2437721 : Blo 718322 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B2732717 : Blo 718322 2732717 := bstep (se 3 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 2732717 = 1024769) B1024769
theorem B1946305 : Blo 718322 1946305 := bstep (se 2 (by rfl) ⟨729864, by rfl⟩ : syracuseStep 1946305 = 1459729) B1459729
theorem B1618649 : Blo 718322 1618649 := bstep (se 2 (by rfl) ⟨606993, by rfl⟩ : syracuseStep 1618649 = 1213987) B1213987
theorem B7779077 : Blo 718322 7779077 := bstep (se 4 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 7779077 = 1458577) B1458577
theorem B1618739 : Blo 718322 1618739 := bstep (se 1 (by rfl) ⟨1214054, by rfl⟩ : syracuseStep 1618739 = 2428109) B2428109
theorem B1618775 : Blo 718322 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B1618955 : Blo 718322 1618955 := bstep (se 1 (by rfl) ⟨1214216, by rfl⟩ : syracuseStep 1618955 = 2428433) B2428433
theorem B1619009 : Blo 718322 1619009 := bstep (se 2 (by rfl) ⟨607128, by rfl⟩ : syracuseStep 1619009 = 1214257) B1214257
theorem B865495 : Blo 718322 865495 := bstep (se 1 (by rfl) ⟨649121, by rfl⟩ : syracuseStep 865495 = 1298243) B1298243
theorem B1619225 : Blo 718322 1619225 := bstep (se 2 (by rfl) ⟨607209, by rfl⟩ : syracuseStep 1619225 = 1214419) B1214419
theorem B1619315 : Blo 718322 1619315 := bstep (se 1 (by rfl) ⟨1214486, by rfl⟩ : syracuseStep 1619315 = 2428973) B2428973
theorem B1619351 : Blo 718322 1619351 := bstep (se 1 (by rfl) ⟨1214513, by rfl⟩ : syracuseStep 1619351 = 2429027) B2429027
theorem B4208051 : Blo 718322 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B1619531 : Blo 718322 1619531 := bstep (se 1 (by rfl) ⟨1214648, by rfl⟩ : syracuseStep 1619531 = 2429297) B2429297
theorem B1619585 : Blo 718322 1619585 := bstep (se 2 (by rfl) ⟨607344, by rfl⟩ : syracuseStep 1619585 = 1214689) B1214689
theorem B11712205 : Blo 718322 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B1619801 : Blo 718322 1619801 := bstep (se 2 (by rfl) ⟨607425, by rfl⟩ : syracuseStep 1619801 = 1214851) B1214851
theorem B3651479 : Blo 718322 3651479 := bstep (se 1 (by rfl) ⟨2738609, by rfl⟩ : syracuseStep 3651479 = 5477219) B5477219
theorem B1619891 : Blo 718322 1619891 := bstep (se 1 (by rfl) ⟨1214918, by rfl⟩ : syracuseStep 1619891 = 2429837) B2429837
theorem B1619927 : Blo 718322 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B2668589 : Blo 718322 2668589 := bstep (se 3 (by rfl) ⟨500360, by rfl⟩ : syracuseStep 2668589 = 1000721) B1000721
theorem B2734145 : Blo 718322 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B3291211 : Blo 718322 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B1620107 : Blo 718322 1620107 := bstep (se 1 (by rfl) ⟨1215080, by rfl⟩ : syracuseStep 1620107 = 2430161) B2430161
theorem B1620161 : Blo 718322 1620161 := bstep (se 2 (by rfl) ⟨607560, by rfl⟩ : syracuseStep 1620161 = 1215121) B1215121
theorem B5912983 : Blo 718322 5912983 := bstep (se 1 (by rfl) ⟨4434737, by rfl⟩ : syracuseStep 5912983 = 8869475) B8869475
theorem B1620377 : Blo 718322 1620377 := bstep (se 2 (by rfl) ⟨607641, by rfl⟩ : syracuseStep 1620377 = 1215283) B1215283
theorem B10795481 : Blo 718322 10795481 := bstep (se 2 (by rfl) ⟨4048305, by rfl⟩ : syracuseStep 10795481 = 8096611) B8096611
theorem B1620467 : Blo 718322 1620467 := bstep (se 1 (by rfl) ⟨1215350, by rfl⟩ : syracuseStep 1620467 = 2430701) B2430701
theorem B2406935 : Blo 718322 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B1620503 : Blo 718322 1620503 := bstep (se 1 (by rfl) ⟨1215377, by rfl⟩ : syracuseStep 1620503 = 2430755) B2430755
theorem B3455581 : Blo 718322 3455581 := bstep (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) B1295843
theorem B1620683 : Blo 718322 1620683 := bstep (se 1 (by rfl) ⟨1215512, by rfl⟩ : syracuseStep 1620683 = 2431025) B2431025
theorem B768727 : Blo 718322 768727 := bstep (se 1 (by rfl) ⟨576545, by rfl⟩ : syracuseStep 768727 = 1153091) B1153091
theorem B1620737 : Blo 718322 1620737 := bstep (se 2 (by rfl) ⟨607776, by rfl⟩ : syracuseStep 1620737 = 1215553) B1215553
theorem B1620953 : Blo 718322 1620953 := bstep (se 2 (by rfl) ⟨607857, by rfl⟩ : syracuseStep 1620953 = 1215715) B1215715
theorem B2046941 : Blo 718322 2046941 := bstep (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) B767603
theorem B1621043 : Blo 718322 1621043 := bstep (se 1 (by rfl) ⟨1215782, by rfl⟩ : syracuseStep 1621043 = 2431565) B2431565
theorem B1621079 : Blo 718322 1621079 := bstep (se 1 (by rfl) ⟨1215809, by rfl⟩ : syracuseStep 1621079 = 2431619) B2431619
theorem B5192855 : Blo 718322 5192855 := bstep (se 1 (by rfl) ⟨3894641, by rfl⟩ : syracuseStep 5192855 = 7789283) B7789283
theorem B2047169 : Blo 718322 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B1621259 : Blo 718322 1621259 := bstep (se 1 (by rfl) ⟨1215944, by rfl⟩ : syracuseStep 1621259 = 2431889) B2431889
theorem B1621313 : Blo 718322 1621313 := bstep (se 2 (by rfl) ⟨607992, by rfl⟩ : syracuseStep 1621313 = 1215985) B1215985
theorem B769547 : Blo 718322 769547 := bstep (se 1 (by rfl) ⟨577160, by rfl⟩ : syracuseStep 769547 = 1154321) B1154321
theorem B2735633 : Blo 718322 2735633 := bstep (se 2 (by rfl) ⟨1025862, by rfl⟩ : syracuseStep 2735633 = 2051725) B2051725
theorem B2047511 : Blo 718322 2047511 := bstep (se 1 (by rfl) ⟨1535633, by rfl⟩ : syracuseStep 2047511 = 3071267) B3071267
theorem B1621529 : Blo 718322 1621529 := bstep (se 2 (by rfl) ⟨608073, by rfl⟩ : syracuseStep 1621529 = 1216147) B1216147
theorem B1621619 : Blo 718322 1621619 := bstep (se 1 (by rfl) ⟨1216214, by rfl⟩ : syracuseStep 1621619 = 2432429) B2432429
theorem B1621655 : Blo 718322 1621655 := bstep (se 1 (by rfl) ⟨1216241, by rfl⟩ : syracuseStep 1621655 = 2432483) B2432483
theorem B1621835 : Blo 718322 1621835 := bstep (se 1 (by rfl) ⟨1216376, by rfl⟩ : syracuseStep 1621835 = 2432753) B2432753
theorem B18693989 : Blo 718322 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B1621889 : Blo 718322 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B1818571 : Blo 718322 1818571 := bstep (se 1 (by rfl) ⟨1363928, by rfl⟩ : syracuseStep 1818571 = 2727857) B2727857
theorem B2736089 : Blo 718322 2736089 := bstep (se 2 (by rfl) ⟨1026033, by rfl⟩ : syracuseStep 2736089 = 2052067) B2052067
theorem B1818713 : Blo 718322 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1622105 : Blo 718322 1622105 := bstep (se 2 (by rfl) ⟨608289, by rfl⟩ : syracuseStep 1622105 = 1216579) B1216579
theorem B1294465 : Blo 718322 1294465 := bstep (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) B970849
theorem B2736301 : Blo 718322 2736301 := bstep (se 3 (by rfl) ⟨513056, by rfl⟩ : syracuseStep 2736301 = 1026113) B1026113
theorem B1622195 : Blo 718322 1622195 := bstep (se 1 (by rfl) ⟨1216646, by rfl⟩ : syracuseStep 1622195 = 2433293) B2433293
theorem B1622231 : Blo 718322 1622231 := bstep (se 1 (by rfl) ⟨1216673, by rfl⟩ : syracuseStep 1622231 = 2433347) B2433347
theorem B1622411 : Blo 718322 1622411 := bstep (se 1 (by rfl) ⟨1216808, by rfl⟩ : syracuseStep 1622411 = 2433617) B2433617
theorem B1622465 : Blo 718322 1622465 := bstep (se 2 (by rfl) ⟨608424, by rfl⟩ : syracuseStep 1622465 = 1216849) B1216849
theorem B2736605 : Blo 718322 2736605 := bstep (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) B1026227
theorem B1458739 : Blo 718322 1458739 := bstep (se 1 (by rfl) ⟨1094054, by rfl⟩ : syracuseStep 1458739 = 2188109) B2188109
theorem B1622681 : Blo 718322 1622681 := bstep (se 2 (by rfl) ⟨608505, by rfl⟩ : syracuseStep 1622681 = 1217011) B1217011
theorem B770743 : Blo 718322 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B1622771 : Blo 718322 1622771 := bstep (se 1 (by rfl) ⟨1217078, by rfl⟩ : syracuseStep 1622771 = 2434157) B2434157
theorem B1622807 : Blo 718322 1622807 := bstep (se 1 (by rfl) ⟨1217105, by rfl⟩ : syracuseStep 1622807 = 2434211) B2434211
theorem B1295129 : Blo 718322 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B13812545 : Blo 718322 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B1819543 : Blo 718322 1819543 := bstep (se 1 (by rfl) ⟨1364657, by rfl⟩ : syracuseStep 1819543 = 2729315) B2729315
theorem B8111027 : Blo 718322 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B1622987 : Blo 718322 1622987 := bstep (se 1 (by rfl) ⟨1217240, by rfl⟩ : syracuseStep 1622987 = 2434481) B2434481
theorem B3687385 : Blo 718322 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B1623041 : Blo 718322 1623041 := bstep (se 2 (by rfl) ⟨608640, by rfl⟩ : syracuseStep 1623041 = 1217281) B1217281
theorem B1623257 : Blo 718322 1623257 := bstep (se 2 (by rfl) ⟨608721, by rfl⟩ : syracuseStep 1623257 = 1217443) B1217443
theorem B1623347 : Blo 718322 1623347 := bstep (se 1 (by rfl) ⟨1217510, by rfl⟩ : syracuseStep 1623347 = 2435021) B2435021
theorem B1819979 : Blo 718322 1819979 := bstep (se 1 (by rfl) ⟨1364984, by rfl⟩ : syracuseStep 1819979 = 2729969) B2729969
theorem B1230155 : Blo 718322 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B1623383 : Blo 718322 1623383 := bstep (se 1 (by rfl) ⟨1217537, by rfl⟩ : syracuseStep 1623383 = 2435075) B2435075
theorem B1230169 : Blo 718322 1230169 := bstep (se 2 (by rfl) ⟨461313, by rfl⟩ : syracuseStep 1230169 = 922627) B922627
theorem B3655043 : Blo 718322 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B9848243 : Blo 718322 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B1754561 : Blo 718322 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B1623563 : Blo 718322 1623563 := bstep (se 1 (by rfl) ⟨1217672, by rfl⟩ : syracuseStep 1623563 = 2435345) B2435345
theorem B1459777 : Blo 718322 1459777 := bstep (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) B1094833
theorem B1623617 : Blo 718322 1623617 := bstep (se 2 (by rfl) ⟨608856, by rfl⟩ : syracuseStep 1623617 = 1217713) B1217713
theorem B1820353 : Blo 718322 1820353 := bstep (se 2 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 1820353 = 1365265) B1365265
theorem B1623833 : Blo 718322 1623833 := bstep (se 2 (by rfl) ⟨608937, by rfl⟩ : syracuseStep 1623833 = 1217875) B1217875
theorem B2049857 : Blo 718322 2049857 := bstep (se 2 (by rfl) ⟨768696, by rfl⟩ : syracuseStep 2049857 = 1537393) B1537393
theorem B1623923 : Blo 718322 1623923 := bstep (se 1 (by rfl) ⟨1217942, by rfl⟩ : syracuseStep 1623923 = 2435885) B2435885
theorem B1623959 : Blo 718322 1623959 := bstep (se 1 (by rfl) ⟨1217969, by rfl⟩ : syracuseStep 1623959 = 2435939) B2435939
theorem B1624139 : Blo 718322 1624139 := bstep (se 1 (by rfl) ⟨1218104, by rfl⟩ : syracuseStep 1624139 = 2436209) B2436209
theorem B1296499 : Blo 718322 1296499 := bstep (se 1 (by rfl) ⟨972374, by rfl⟩ : syracuseStep 1296499 = 1944749) B1944749
theorem B1624193 : Blo 718322 1624193 := bstep (se 2 (by rfl) ⟨609072, by rfl⟩ : syracuseStep 1624193 = 1218145) B1218145
theorem B1820951 : Blo 718322 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B2050393 : Blo 718322 2050393 := bstep (se 2 (by rfl) ⟨768897, by rfl⟩ : syracuseStep 2050393 = 1537795) B1537795
theorem B1624409 : Blo 718322 1624409 := bstep (se 2 (by rfl) ⟨609153, by rfl⟩ : syracuseStep 1624409 = 1218307) B1218307
theorem B1624499 : Blo 718322 1624499 := bstep (se 1 (by rfl) ⟨1218374, by rfl⟩ : syracuseStep 1624499 = 2436749) B2436749
theorem B2312651 : Blo 718322 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B1624535 : Blo 718322 1624535 := bstep (se 1 (by rfl) ⟨1218401, by rfl⟩ : syracuseStep 1624535 = 2436803) B2436803
theorem B7490123 : Blo 718322 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B1624715 : Blo 718322 1624715 := bstep (se 1 (by rfl) ⟨1218536, by rfl⟩ : syracuseStep 1624715 = 2437073) B2437073
theorem B1624769 : Blo 718322 1624769 := bstep (se 2 (by rfl) ⟨609288, by rfl⟩ : syracuseStep 1624769 = 1218577) B1218577
theorem B2771729 : Blo 718322 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B2313049 : Blo 718322 2313049 := bstep (se 2 (by rfl) ⟨867393, by rfl⟩ : syracuseStep 2313049 = 1734787) B1734787
theorem B5557123 : Blo 718322 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B1297291 : Blo 718322 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B1624985 : Blo 718322 1624985 := bstep (se 2 (by rfl) ⟨609369, by rfl⟩ : syracuseStep 1624985 = 1218739) B1218739
theorem B1625075 : Blo 718322 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B2739203 : Blo 718322 2739203 := bstep (se 1 (by rfl) ⟨2054402, by rfl⟩ : syracuseStep 2739203 = 4108805) B4108805
theorem B2739217 : Blo 718322 2739217 := bstep (se 2 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 2739217 = 2054413) B2054413
theorem B1625111 : Blo 718322 1625111 := bstep (se 1 (by rfl) ⟨1218833, by rfl⟩ : syracuseStep 1625111 = 2437667) B2437667
theorem B1821761 : Blo 718322 1821761 := bstep (se 2 (by rfl) ⟨683160, by rfl⟩ : syracuseStep 1821761 = 1366321) B1366321
theorem B2739521 : Blo 718322 2739521 := bstep (se 2 (by rfl) ⟨1027320, by rfl⟩ : syracuseStep 2739521 = 2054641) B2054641
theorem B1822297 : Blo 718322 1822297 := bstep (se 2 (by rfl) ⟨683361, by rfl⟩ : syracuseStep 1822297 = 1366723) B1366723
theorem B1298099 : Blo 718322 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B10407797 : Blo 718322 10407797 := bstep (se 5 (by rfl) ⟨487865, by rfl⟩ : syracuseStep 10407797 = 975731) B975731
theorem B1363891 : Blo 718322 1363891 := bstep (se 1 (by rfl) ⟨1022918, by rfl⟩ : syracuseStep 1363891 = 2045837) B2045837
theorem B2740189 : Blo 718322 2740189 := bstep (se 3 (by rfl) ⟨513785, by rfl⟩ : syracuseStep 2740189 = 1027571) B1027571
theorem B2052317 : Blo 718322 2052317 := bstep (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) B769619
theorem B3887461 : Blo 718322 3887461 := bstep (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) B728899
theorem B1364339 : Blo 718322 1364339 := bstep (se 1 (by rfl) ⟨1023254, by rfl⟩ : syracuseStep 1364339 = 2046509) B2046509
theorem B1364377 : Blo 718322 1364377 := bstep (se 2 (by rfl) ⟨511641, by rfl⟩ : syracuseStep 1364377 = 1023283) B1023283
theorem B8212913 : Blo 718322 8212913 := bstep (se 2 (by rfl) ⟨3079842, by rfl⟩ : syracuseStep 8212913 = 6159685) B6159685
theorem B3330497 : Blo 718322 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B1299073 : Blo 718322 1299073 := bstep (se 2 (by rfl) ⟨487152, by rfl⟩ : syracuseStep 1299073 = 974305) B974305
theorem B3068567 : Blo 718322 3068567 := bstep (se 1 (by rfl) ⟨2301425, by rfl⟩ : syracuseStep 3068567 = 4602851) B4602851
theorem B1823411 : Blo 718322 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1364825 : Blo 718322 1364825 := bstep (se 2 (by rfl) ⟨511809, by rfl⟩ : syracuseStep 1364825 = 1023619) B1023619
theorem B4608899 : Blo 718322 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B1823705 : Blo 718322 1823705 := bstep (se 2 (by rfl) ⟨683889, by rfl⟩ : syracuseStep 1823705 = 1367779) B1367779
theorem B6935645 : Blo 718322 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B6149297 : Blo 718322 6149297 := bstep (se 2 (by rfl) ⟨2305986, by rfl⟩ : syracuseStep 6149297 = 4611973) B4611973
theorem B2741465 : Blo 718322 2741465 := bstep (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) B2056099
theorem B1463539 : Blo 718322 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B808267 : Blo 718322 808267 := bstep (se 1 (by rfl) ⟨606200, by rfl⟩ : syracuseStep 808267 = 1212401) B1212401
theorem B3954071 : Blo 718322 3954071 := bstep (se 1 (by rfl) ⟨2965553, by rfl⟩ : syracuseStep 3954071 = 5931107) B5931107
theorem B808375 : Blo 718322 808375 := bstep (se 1 (by rfl) ⟨606281, by rfl⟩ : syracuseStep 808375 = 1212563) B1212563
theorem B1365569 : Blo 718322 1365569 := bstep (se 2 (by rfl) ⟨512088, by rfl⟩ : syracuseStep 1365569 = 1024177) B1024177
theorem B808555 : Blo 718322 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B1464011 : Blo 718322 1464011 := bstep (se 1 (by rfl) ⟨1098008, by rfl⟩ : syracuseStep 1464011 = 2196017) B2196017
theorem B808663 : Blo 718322 808663 := bstep (se 1 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 808663 = 1212995) B1212995
theorem B1365835 : Blo 718322 1365835 := bstep (se 1 (by rfl) ⟨1024376, by rfl⟩ : syracuseStep 1365835 = 2048753) B2048753
theorem B808843 : Blo 718322 808843 := bstep (se 1 (by rfl) ⟨606632, by rfl⟩ : syracuseStep 808843 = 1213265) B1213265
theorem B808951 : Blo 718322 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B5199889 : Blo 718322 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B809131 : Blo 718322 809131 := bstep (se 1 (by rfl) ⟨606848, by rfl⟩ : syracuseStep 809131 = 1213697) B1213697
theorem B1366283 : Blo 718322 1366283 := bstep (se 1 (by rfl) ⟨1024712, by rfl⟩ : syracuseStep 1366283 = 2049425) B2049425
theorem B809239 : Blo 718322 809239 := bstep (se 1 (by rfl) ⟨606929, by rfl⟩ : syracuseStep 809239 = 1213859) B1213859
theorem B1366465 : Blo 718322 1366465 := bstep (se 2 (by rfl) ⟨512424, by rfl⟩ : syracuseStep 1366465 = 1024849) B1024849
theorem B809419 : Blo 718322 809419 := bstep (se 1 (by rfl) ⟨607064, by rfl⟩ : syracuseStep 809419 = 1214129) B1214129
theorem B9361955 : Blo 718322 9361955 := bstep (se 1 (by rfl) ⟨7021466, by rfl⟩ : syracuseStep 9361955 = 14042933) B14042933
theorem B809527 : Blo 718322 809527 := bstep (se 1 (by rfl) ⟨607145, by rfl⟩ : syracuseStep 809527 = 1214291) B1214291
theorem B1825355 : Blo 718322 1825355 := bstep (se 1 (by rfl) ⟨1369016, by rfl⟩ : syracuseStep 1825355 = 2738033) B2738033
theorem B7494275 : Blo 718322 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B3070685 : Blo 718322 3070685 := bstep (se 3 (by rfl) ⟨575753, by rfl⟩ : syracuseStep 3070685 = 1151507) B1151507
theorem B809707 : Blo 718322 809707 := bstep (se 1 (by rfl) ⟨607280, by rfl⟩ : syracuseStep 809707 = 1214561) B1214561
theorem B1366807 : Blo 718322 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B6249251 : Blo 718322 6249251 := bstep (se 1 (by rfl) ⟨4686938, by rfl⟩ : syracuseStep 6249251 = 9373877) B9373877
theorem B809815 : Blo 718322 809815 := bstep (se 1 (by rfl) ⟨607361, by rfl⟩ : syracuseStep 809815 = 1214723) B1214723
theorem B1367027 : Blo 718322 1367027 := bstep (se 1 (by rfl) ⟨1025270, by rfl⟩ : syracuseStep 1367027 = 2050541) B2050541
theorem B809995 : Blo 718322 809995 := bstep (se 1 (by rfl) ⟨607496, by rfl⟩ : syracuseStep 809995 = 1214993) B1214993
theorem B3070993 : Blo 718322 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B3071027 : Blo 718322 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B2055233 : Blo 718322 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B2055257 : Blo 718322 2055257 := bstep (se 2 (by rfl) ⟨770721, by rfl⟩ : syracuseStep 2055257 = 1541443) B1541443
theorem B810103 : Blo 718322 810103 := bstep (se 1 (by rfl) ⟨607577, by rfl⟩ : syracuseStep 810103 = 1215155) B1215155
theorem B1367255 : Blo 718322 1367255 := bstep (se 1 (by rfl) ⟨1025441, by rfl⟩ : syracuseStep 1367255 = 2050883) B2050883
theorem B810283 : Blo 718322 810283 := bstep (se 1 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 810283 = 1215425) B1215425
theorem B810391 : Blo 718322 810391 := bstep (se 1 (by rfl) ⟨607793, by rfl⟩ : syracuseStep 810391 = 1215587) B1215587
theorem B1367513 : Blo 718322 1367513 := bstep (se 2 (by rfl) ⟨512817, by rfl⟩ : syracuseStep 1367513 = 1025635) B1025635
theorem B1826327 : Blo 718322 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B810571 : Blo 718322 810571 := bstep (se 1 (by rfl) ⟨607928, by rfl⟩ : syracuseStep 810571 = 1215857) B1215857
theorem B810679 : Blo 718322 810679 := bstep (se 1 (by rfl) ⟨608009, by rfl⟩ : syracuseStep 810679 = 1216019) B1216019
theorem B810859 : Blo 718322 810859 := bstep (se 1 (by rfl) ⟨608144, by rfl⟩ : syracuseStep 810859 = 1216289) B1216289
theorem B1367923 : Blo 718322 1367923 := bstep (se 1 (by rfl) ⟨1025942, by rfl⟩ : syracuseStep 1367923 = 2051885) B2051885
theorem B810967 : Blo 718322 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B2187329 : Blo 718322 2187329 := bstep (se 2 (by rfl) ⟨820248, by rfl⟩ : syracuseStep 2187329 = 1640497) B1640497
theorem B811147 : Blo 718322 811147 := bstep (se 1 (by rfl) ⟨608360, by rfl⟩ : syracuseStep 811147 = 1216721) B1216721
theorem B909463 : Blo 718322 909463 := bstep (se 1 (by rfl) ⟨682097, by rfl⟩ : syracuseStep 909463 = 1364195) B1364195
theorem B1826995 : Blo 718322 1826995 := bstep (se 1 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 1826995 = 2740493) B2740493
theorem B811255 : Blo 718322 811255 := bstep (se 1 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 811255 = 1216883) B1216883
theorem B2056499 : Blo 718322 2056499 := bstep (se 1 (by rfl) ⟨1542374, by rfl⟩ : syracuseStep 2056499 = 3084749) B3084749
theorem B1827137 : Blo 718322 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B1368409 : Blo 718322 1368409 := bstep (se 2 (by rfl) ⟨513153, by rfl⟩ : syracuseStep 1368409 = 1026307) B1026307
theorem B811435 : Blo 718322 811435 := bstep (se 1 (by rfl) ⟨608576, by rfl⟩ : syracuseStep 811435 = 1217153) B1217153
theorem B811543 : Blo 718322 811543 := bstep (se 1 (by rfl) ⟨608657, by rfl⟩ : syracuseStep 811543 = 1217315) B1217315
theorem B975385 : Blo 718322 975385 := bstep (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) B731539
theorem B811723 : Blo 718322 811723 := bstep (se 1 (by rfl) ⟨608792, by rfl⟩ : syracuseStep 811723 = 1217585) B1217585
theorem B6152921 : Blo 718322 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B811831 : Blo 718322 811831 := bstep (se 1 (by rfl) ⟨608873, by rfl⟩ : syracuseStep 811831 = 1217747) B1217747
theorem B1368971 : Blo 718322 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B3072941 : Blo 718322 3072941 := bstep (se 3 (by rfl) ⟨576176, by rfl⟩ : syracuseStep 3072941 = 1152353) B1152353
theorem B819191 : Blo 718322 819191 := bstep (se 1 (by rfl) ⟨614393, by rfl⟩ : syracuseStep 819191 = 1228787) B1228787
theorem B812011 : Blo 718322 812011 := bstep (se 1 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 812011 = 1218017) B1218017
theorem B1369153 : Blo 718322 1369153 := bstep (se 2 (by rfl) ⟨513432, by rfl⟩ : syracuseStep 1369153 = 1026865) B1026865
theorem B812119 : Blo 718322 812119 := bstep (se 1 (by rfl) ⟨609089, by rfl⟩ : syracuseStep 812119 = 1218179) B1218179
theorem B11101445 : Blo 718322 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B812299 : Blo 718322 812299 := bstep (se 1 (by rfl) ⟨609224, by rfl⟩ : syracuseStep 812299 = 1218449) B1218449
theorem B812407 : Blo 718322 812407 := bstep (se 1 (by rfl) ⟨609305, by rfl⟩ : syracuseStep 812407 = 1218611) B1218611
theorem B812587 : Blo 718322 812587 := bstep (se 1 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 812587 = 1218881) B1218881
theorem B3073625 : Blo 718322 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B1730251 : Blo 718322 1730251 := bstep (se 1 (by rfl) ⟨1297688, by rfl⟩ : syracuseStep 1730251 = 2595377) B2595377
theorem B1369867 : Blo 718322 1369867 := bstep (se 1 (by rfl) ⟨1027400, by rfl⟩ : syracuseStep 1369867 = 2054801) B2054801
theorem B1730327 : Blo 718322 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B911179 : Blo 718322 911179 := bstep (se 1 (by rfl) ⟨683384, by rfl⟩ : syracuseStep 911179 = 1366769) B1366769
theorem B1107799 : Blo 718322 1107799 := bstep (se 1 (by rfl) ⟨830849, by rfl⟩ : syracuseStep 1107799 = 1661699) B1661699
theorem B1369943 : Blo 718322 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B5826653 : Blo 718322 5826653 := bstep (se 3 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 5826653 = 2184995) B2184995
theorem B10381553 : Blo 718322 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B1370611 : Blo 718322 1370611 := bstep (se 1 (by rfl) ⟨1027958, by rfl⟩ : syracuseStep 1370611 = 2055917) B2055917
theorem B3893777 : Blo 718322 3893777 := bstep (se 2 (by rfl) ⟨1460166, by rfl⟩ : syracuseStep 3893777 = 2920333) B2920333
theorem B1370839 : Blo 718322 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B912151 : Blo 718322 912151 := bstep (se 1 (by rfl) ⟨684113, by rfl⟩ : syracuseStep 912151 = 1368227) B1368227
theorem B8186669 : Blo 718322 8186669 := bstep (se 3 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 8186669 = 3070001) B3070001
theorem B1370945 : Blo 718322 1370945 := bstep (se 2 (by rfl) ⟨514104, by rfl⟩ : syracuseStep 1370945 = 1028209) B1028209
theorem B1371097 : Blo 718322 1371097 := bstep (se 2 (by rfl) ⟨514161, by rfl⟩ : syracuseStep 1371097 = 1028323) B1028323
theorem B3697937 : Blo 718322 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B6155585 : Blo 718322 6155585 := bstep (se 2 (by rfl) ⟨2308344, by rfl⟩ : syracuseStep 6155585 = 4616689) B4616689
theorem B1535411 : Blo 718322 1535411 := bstep (se 1 (by rfl) ⟨1151558, by rfl⟩ : syracuseStep 1535411 = 2303117) B2303117
theorem B5205539 : Blo 718322 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B912971 : Blo 718322 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B4091741 : Blo 718322 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B5009501 : Blo 718322 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B3076289 : Blo 718322 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B1077515 : Blo 718322 1077515 := bstep (se 1 (by rfl) ⟨808136, by rfl⟩ : syracuseStep 1077515 = 1616273) B1616273
theorem B913675 : Blo 718322 913675 := bstep (se 1 (by rfl) ⟨685256, by rfl⟩ : syracuseStep 913675 = 1370513) B1370513
theorem B1077527 : Blo 718322 1077527 := bstep (se 1 (by rfl) ⟨808145, by rfl⟩ : syracuseStep 1077527 = 1616291) B1616291
theorem B1077593 : Blo 718322 1077593 := bstep (se 2 (by rfl) ⟨404097, by rfl⟩ : syracuseStep 1077593 = 808195) B808195
theorem B1077707 : Blo 718322 1077707 := bstep (se 1 (by rfl) ⟨808280, by rfl⟩ : syracuseStep 1077707 = 1616561) B1616561
theorem B1077719 : Blo 718322 1077719 := bstep (se 1 (by rfl) ⟨808289, by rfl⟩ : syracuseStep 1077719 = 1616579) B1616579
theorem B913943 : Blo 718322 913943 := bstep (se 1 (by rfl) ⟨685457, by rfl⟩ : syracuseStep 913943 = 1370915) B1370915
theorem B1077785 : Blo 718322 1077785 := bstep (se 2 (by rfl) ⟨404169, by rfl⟩ : syracuseStep 1077785 = 808339) B808339
theorem B4682285 : Blo 718322 4682285 := bstep (se 3 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 4682285 = 1755857) B1755857
theorem B94958173 : Blo 718322 94958173 := bstep (se 3 (by rfl) ⟨17804657, by rfl⟩ : syracuseStep 94958173 = 35609315) B35609315
theorem B1077899 : Blo 718322 1077899 := bstep (se 1 (by rfl) ⟨808424, by rfl⟩ : syracuseStep 1077899 = 1616849) B1616849
theorem B1077911 : Blo 718322 1077911 := bstep (se 1 (by rfl) ⟨808433, by rfl⟩ : syracuseStep 1077911 = 1616867) B1616867
theorem B1536727 : Blo 718322 1536727 := bstep (se 1 (by rfl) ⟨1152545, by rfl⟩ : syracuseStep 1536727 = 2305091) B2305091
theorem B1077977 : Blo 718322 1077977 := bstep (se 2 (by rfl) ⟨404241, by rfl⟩ : syracuseStep 1077977 = 808483) B808483
theorem B1078091 : Blo 718322 1078091 := bstep (se 1 (by rfl) ⟨808568, by rfl⟩ : syracuseStep 1078091 = 1617137) B1617137
theorem B1078103 : Blo 718322 1078103 := bstep (se 1 (by rfl) ⟨808577, by rfl⟩ : syracuseStep 1078103 = 1617155) B1617155
theorem B1536907 : Blo 718322 1536907 := bstep (se 1 (by rfl) ⟨1152680, by rfl⟩ : syracuseStep 1536907 = 2305361) B2305361
theorem B1078169 : Blo 718322 1078169 := bstep (se 2 (by rfl) ⟨404313, by rfl⟩ : syracuseStep 1078169 = 808627) B808627
theorem B1536983 : Blo 718322 1536983 := bstep (se 1 (by rfl) ⟨1152737, by rfl⟩ : syracuseStep 1536983 = 2305475) B2305475
theorem B1078283 : Blo 718322 1078283 := bstep (se 1 (by rfl) ⟨808712, by rfl⟩ : syracuseStep 1078283 = 1617425) B1617425
theorem B1078295 : Blo 718322 1078295 := bstep (se 1 (by rfl) ⟨808721, by rfl⟩ : syracuseStep 1078295 = 1617443) B1617443
theorem B10515491 : Blo 718322 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B1078361 : Blo 718322 1078361 := bstep (se 2 (by rfl) ⟨404385, by rfl⟩ : syracuseStep 1078361 = 808771) B808771
theorem B1078475 : Blo 718322 1078475 := bstep (se 1 (by rfl) ⟨808856, by rfl⟩ : syracuseStep 1078475 = 1617713) B1617713
theorem B1078487 : Blo 718322 1078487 := bstep (se 1 (by rfl) ⟨808865, by rfl⟩ : syracuseStep 1078487 = 1617731) B1617731
theorem B1078553 : Blo 718322 1078553 := bstep (se 2 (by rfl) ⟨404457, by rfl⟩ : syracuseStep 1078553 = 808915) B808915
theorem B1078667 : Blo 718322 1078667 := bstep (se 1 (by rfl) ⟨809000, by rfl⟩ : syracuseStep 1078667 = 1618001) B1618001
theorem B17528213 : Blo 718322 17528213 := bstep (se 6 (by rfl) ⟨410817, by rfl⟩ : syracuseStep 17528213 = 821635) B821635
theorem B1078679 : Blo 718322 1078679 := bstep (se 1 (by rfl) ⟨809009, by rfl⟩ : syracuseStep 1078679 = 1618019) B1618019
theorem B1078745 : Blo 718322 1078745 := bstep (se 2 (by rfl) ⟨404529, by rfl⟩ : syracuseStep 1078745 = 809059) B809059
theorem B718327 : Blo 718322 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B718347 : Blo 718322 718347 := bstep (se 1 (by rfl) ⟨538760, by rfl⟩ : syracuseStep 718347 = 1077521) B1077521
theorem B718359 : Blo 718322 718359 := bstep (se 1 (by rfl) ⟨538769, by rfl⟩ : syracuseStep 718359 = 1077539) B1077539
theorem B718379 : Blo 718322 718379 := bstep (se 1 (by rfl) ⟨538784, by rfl⟩ : syracuseStep 718379 = 1077569) B1077569
theorem B718391 : Blo 718322 718391 := bstep (se 1 (by rfl) ⟨538793, by rfl⟩ : syracuseStep 718391 = 1077587) B1077587
theorem B718411 : Blo 718322 718411 := bstep (se 1 (by rfl) ⟨538808, by rfl⟩ : syracuseStep 718411 = 1077617) B1077617
theorem B1078859 : Blo 718322 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B718423 : Blo 718322 718423 := bstep (se 1 (by rfl) ⟨538817, by rfl⟩ : syracuseStep 718423 = 1077635) B1077635
theorem B1078871 : Blo 718322 1078871 := bstep (se 1 (by rfl) ⟨809153, by rfl⟩ : syracuseStep 1078871 = 1618307) B1618307
theorem B718443 : Blo 718322 718443 := bstep (se 1 (by rfl) ⟨538832, by rfl⟩ : syracuseStep 718443 = 1077665) B1077665
theorem B718455 : Blo 718322 718455 := bstep (se 1 (by rfl) ⟨538841, by rfl⟩ : syracuseStep 718455 = 1077683) B1077683
theorem B718475 : Blo 718322 718475 := bstep (se 1 (by rfl) ⟨538856, by rfl⟩ : syracuseStep 718475 = 1077713) B1077713
theorem B3077777 : Blo 718322 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B718487 : Blo 718322 718487 := bstep (se 1 (by rfl) ⟨538865, by rfl⟩ : syracuseStep 718487 = 1077731) B1077731
theorem B1078937 : Blo 718322 1078937 := bstep (se 2 (by rfl) ⟨404601, by rfl⟩ : syracuseStep 1078937 = 809203) B809203
theorem B718507 : Blo 718322 718507 := bstep (se 1 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 718507 = 1077761) B1077761
theorem B718519 : Blo 718322 718519 := bstep (se 1 (by rfl) ⟨538889, by rfl⟩ : syracuseStep 718519 = 1077779) B1077779
theorem B718539 : Blo 718322 718539 := bstep (se 1 (by rfl) ⟨538904, by rfl⟩ : syracuseStep 718539 = 1077809) B1077809
theorem B718551 : Blo 718322 718551 := bstep (se 1 (by rfl) ⟨538913, by rfl⟩ : syracuseStep 718551 = 1077827) B1077827
theorem B718571 : Blo 718322 718571 := bstep (se 1 (by rfl) ⟨538928, by rfl⟩ : syracuseStep 718571 = 1077857) B1077857
theorem B718583 : Blo 718322 718583 := bstep (se 1 (by rfl) ⟨538937, by rfl⟩ : syracuseStep 718583 = 1077875) B1077875
theorem B718603 : Blo 718322 718603 := bstep (se 1 (by rfl) ⟨538952, by rfl⟩ : syracuseStep 718603 = 1077905) B1077905
theorem B1079051 : Blo 718322 1079051 := bstep (se 1 (by rfl) ⟨809288, by rfl⟩ : syracuseStep 1079051 = 1618577) B1618577
theorem B718615 : Blo 718322 718615 := bstep (se 1 (by rfl) ⟨538961, by rfl⟩ : syracuseStep 718615 = 1077923) B1077923
theorem B1079063 : Blo 718322 1079063 := bstep (se 1 (by rfl) ⟨809297, by rfl⟩ : syracuseStep 1079063 = 1618595) B1618595
theorem B718635 : Blo 718322 718635 := bstep (se 1 (by rfl) ⟨538976, by rfl⟩ : syracuseStep 718635 = 1077953) B1077953
theorem B718647 : Blo 718322 718647 := bstep (se 1 (by rfl) ⟨538985, by rfl⟩ : syracuseStep 718647 = 1077971) B1077971
theorem B718667 : Blo 718322 718667 := bstep (se 1 (by rfl) ⟨539000, by rfl⟩ : syracuseStep 718667 = 1078001) B1078001
theorem B718679 : Blo 718322 718679 := bstep (se 1 (by rfl) ⟨539009, by rfl⟩ : syracuseStep 718679 = 1078019) B1078019
theorem B1079129 : Blo 718322 1079129 := bstep (se 2 (by rfl) ⟨404673, by rfl⟩ : syracuseStep 1079129 = 809347) B809347
theorem B718699 : Blo 718322 718699 := bstep (se 1 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 718699 = 1078049) B1078049
theorem B718711 : Blo 718322 718711 := bstep (se 1 (by rfl) ⟨539033, by rfl⟩ : syracuseStep 718711 = 1078067) B1078067
theorem B718731 : Blo 718322 718731 := bstep (se 1 (by rfl) ⟨539048, by rfl⟩ : syracuseStep 718731 = 1078097) B1078097
theorem B718743 : Blo 718322 718743 := bstep (se 1 (by rfl) ⟨539057, by rfl⟩ : syracuseStep 718743 = 1078115) B1078115
theorem B718763 : Blo 718322 718763 := bstep (se 1 (by rfl) ⟨539072, by rfl⟩ : syracuseStep 718763 = 1078145) B1078145
theorem B718775 : Blo 718322 718775 := bstep (se 1 (by rfl) ⟨539081, by rfl⟩ : syracuseStep 718775 = 1078163) B1078163
theorem B718795 : Blo 718322 718795 := bstep (se 1 (by rfl) ⟨539096, by rfl⟩ : syracuseStep 718795 = 1078193) B1078193
theorem B1079243 : Blo 718322 1079243 := bstep (se 1 (by rfl) ⟨809432, by rfl⟩ : syracuseStep 1079243 = 1618865) B1618865
theorem B718807 : Blo 718322 718807 := bstep (se 1 (by rfl) ⟨539105, by rfl⟩ : syracuseStep 718807 = 1078211) B1078211
theorem B1079255 : Blo 718322 1079255 := bstep (se 1 (by rfl) ⟨809441, by rfl⟩ : syracuseStep 1079255 = 1618883) B1618883
theorem B718827 : Blo 718322 718827 := bstep (se 1 (by rfl) ⟨539120, by rfl⟩ : syracuseStep 718827 = 1078241) B1078241
theorem B718839 : Blo 718322 718839 := bstep (se 1 (by rfl) ⟨539129, by rfl⟩ : syracuseStep 718839 = 1078259) B1078259
theorem B718859 : Blo 718322 718859 := bstep (se 1 (by rfl) ⟨539144, by rfl⟩ : syracuseStep 718859 = 1078289) B1078289
theorem B718871 : Blo 718322 718871 := bstep (se 1 (by rfl) ⟨539153, by rfl⟩ : syracuseStep 718871 = 1078307) B1078307
theorem B1079321 : Blo 718322 1079321 := bstep (se 2 (by rfl) ⟨404745, by rfl⟩ : syracuseStep 1079321 = 809491) B809491
theorem B718891 : Blo 718322 718891 := bstep (se 1 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 718891 = 1078337) B1078337
theorem B3897389 : Blo 718322 3897389 := bstep (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) B1461521
theorem B718903 : Blo 718322 718903 := bstep (se 1 (by rfl) ⟨539177, by rfl⟩ : syracuseStep 718903 = 1078355) B1078355
theorem B3897409 : Blo 718322 3897409 := bstep (se 2 (by rfl) ⟨1461528, by rfl⟩ : syracuseStep 3897409 = 2923057) B2923057
theorem B718923 : Blo 718322 718923 := bstep (se 1 (by rfl) ⟨539192, by rfl⟩ : syracuseStep 718923 = 1078385) B1078385
theorem B718935 : Blo 718322 718935 := bstep (se 1 (by rfl) ⟨539201, by rfl⟩ : syracuseStep 718935 = 1078403) B1078403
theorem B718955 : Blo 718322 718955 := bstep (se 1 (by rfl) ⟨539216, by rfl⟩ : syracuseStep 718955 = 1078433) B1078433
theorem B718967 : Blo 718322 718967 := bstep (se 1 (by rfl) ⟨539225, by rfl⟩ : syracuseStep 718967 = 1078451) B1078451
theorem B718987 : Blo 718322 718987 := bstep (se 1 (by rfl) ⟨539240, by rfl⟩ : syracuseStep 718987 = 1078481) B1078481
theorem B1079435 : Blo 718322 1079435 := bstep (se 1 (by rfl) ⟨809576, by rfl⟩ : syracuseStep 1079435 = 1619153) B1619153
theorem B718999 : Blo 718322 718999 := bstep (se 1 (by rfl) ⟨539249, by rfl⟩ : syracuseStep 718999 = 1078499) B1078499
theorem B1079447 : Blo 718322 1079447 := bstep (se 1 (by rfl) ⟨809585, by rfl⟩ : syracuseStep 1079447 = 1619171) B1619171
theorem B719019 : Blo 718322 719019 := bstep (se 1 (by rfl) ⟨539264, by rfl⟩ : syracuseStep 719019 = 1078529) B1078529
theorem B719031 : Blo 718322 719031 := bstep (se 1 (by rfl) ⟨539273, by rfl⟩ : syracuseStep 719031 = 1078547) B1078547
theorem B719051 : Blo 718322 719051 := bstep (se 1 (by rfl) ⟨539288, by rfl⟩ : syracuseStep 719051 = 1078577) B1078577
theorem B719063 : Blo 718322 719063 := bstep (se 1 (by rfl) ⟨539297, by rfl⟩ : syracuseStep 719063 = 1078595) B1078595
theorem B1079513 : Blo 718322 1079513 := bstep (se 2 (by rfl) ⟨404817, by rfl⟩ : syracuseStep 1079513 = 809635) B809635
theorem B719083 : Blo 718322 719083 := bstep (se 1 (by rfl) ⟨539312, by rfl⟩ : syracuseStep 719083 = 1078625) B1078625
theorem B719095 : Blo 718322 719095 := bstep (se 1 (by rfl) ⟨539321, by rfl⟩ : syracuseStep 719095 = 1078643) B1078643
theorem B719115 : Blo 718322 719115 := bstep (se 1 (by rfl) ⟨539336, by rfl⟩ : syracuseStep 719115 = 1078673) B1078673
theorem B4094225 : Blo 718322 4094225 := bstep (se 2 (by rfl) ⟨1535334, by rfl⟩ : syracuseStep 4094225 = 3070669) B3070669
theorem B719127 : Blo 718322 719127 := bstep (se 1 (by rfl) ⟨539345, by rfl⟩ : syracuseStep 719127 = 1078691) B1078691
theorem B719147 : Blo 718322 719147 := bstep (se 1 (by rfl) ⟨539360, by rfl⟩ : syracuseStep 719147 = 1078721) B1078721
theorem B19757357 : Blo 718322 19757357 := bstep (se 3 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 19757357 = 7409009) B7409009
theorem B719159 : Blo 718322 719159 := bstep (se 1 (by rfl) ⟨539369, by rfl⟩ : syracuseStep 719159 = 1078739) B1078739
theorem B719179 : Blo 718322 719179 := bstep (se 1 (by rfl) ⟨539384, by rfl⟩ : syracuseStep 719179 = 1078769) B1078769
theorem B1079627 : Blo 718322 1079627 := bstep (se 1 (by rfl) ⟨809720, by rfl⟩ : syracuseStep 1079627 = 1619441) B1619441
theorem B719191 : Blo 718322 719191 := bstep (se 1 (by rfl) ⟨539393, by rfl⟩ : syracuseStep 719191 = 1078787) B1078787
theorem B1079639 : Blo 718322 1079639 := bstep (se 1 (by rfl) ⟨809729, by rfl⟩ : syracuseStep 1079639 = 1619459) B1619459
theorem B719211 : Blo 718322 719211 := bstep (se 1 (by rfl) ⟨539408, by rfl⟩ : syracuseStep 719211 = 1078817) B1078817
theorem B719223 : Blo 718322 719223 := bstep (se 1 (by rfl) ⟨539417, by rfl⟩ : syracuseStep 719223 = 1078835) B1078835
theorem B719243 : Blo 718322 719243 := bstep (se 1 (by rfl) ⟨539432, by rfl⟩ : syracuseStep 719243 = 1078865) B1078865
theorem B719255 : Blo 718322 719255 := bstep (se 1 (by rfl) ⟨539441, by rfl⟩ : syracuseStep 719255 = 1078883) B1078883
theorem B1079705 : Blo 718322 1079705 := bstep (se 2 (by rfl) ⟨404889, by rfl⟩ : syracuseStep 1079705 = 809779) B809779
theorem B719275 : Blo 718322 719275 := bstep (se 1 (by rfl) ⟨539456, by rfl⟩ : syracuseStep 719275 = 1078913) B1078913
theorem B719287 : Blo 718322 719287 := bstep (se 1 (by rfl) ⟨539465, by rfl⟩ : syracuseStep 719287 = 1078931) B1078931
theorem B719307 : Blo 718322 719307 := bstep (se 1 (by rfl) ⟨539480, by rfl⟩ : syracuseStep 719307 = 1078961) B1078961
theorem B719319 : Blo 718322 719319 := bstep (se 1 (by rfl) ⟨539489, by rfl⟩ : syracuseStep 719319 = 1078979) B1078979
theorem B719339 : Blo 718322 719339 := bstep (se 1 (by rfl) ⟨539504, by rfl⟩ : syracuseStep 719339 = 1079009) B1079009
theorem B719351 : Blo 718322 719351 := bstep (se 1 (by rfl) ⟨539513, by rfl⟩ : syracuseStep 719351 = 1079027) B1079027
theorem B719371 : Blo 718322 719371 := bstep (se 1 (by rfl) ⟨539528, by rfl⟩ : syracuseStep 719371 = 1079057) B1079057
theorem B1079819 : Blo 718322 1079819 := bstep (se 1 (by rfl) ⟨809864, by rfl⟩ : syracuseStep 1079819 = 1619729) B1619729
theorem B719383 : Blo 718322 719383 := bstep (se 1 (by rfl) ⟨539537, by rfl⟩ : syracuseStep 719383 = 1079075) B1079075
theorem B1079831 : Blo 718322 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B719403 : Blo 718322 719403 := bstep (se 1 (by rfl) ⟨539552, by rfl⟩ : syracuseStep 719403 = 1079105) B1079105
theorem B719415 : Blo 718322 719415 := bstep (se 1 (by rfl) ⟨539561, by rfl⟩ : syracuseStep 719415 = 1079123) B1079123
theorem B719435 : Blo 718322 719435 := bstep (se 1 (by rfl) ⟨539576, by rfl⟩ : syracuseStep 719435 = 1079153) B1079153
theorem B719447 : Blo 718322 719447 := bstep (se 1 (by rfl) ⟨539585, by rfl⟩ : syracuseStep 719447 = 1079171) B1079171
theorem B1079897 : Blo 718322 1079897 := bstep (se 2 (by rfl) ⟨404961, by rfl⟩ : syracuseStep 1079897 = 809923) B809923
theorem B3078749 : Blo 718322 3078749 := bstep (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) B1154531
theorem B719467 : Blo 718322 719467 := bstep (se 1 (by rfl) ⟨539600, by rfl⟩ : syracuseStep 719467 = 1079201) B1079201
theorem B719479 : Blo 718322 719479 := bstep (se 1 (by rfl) ⟨539609, by rfl⟩ : syracuseStep 719479 = 1079219) B1079219
theorem B719499 : Blo 718322 719499 := bstep (se 1 (by rfl) ⟨539624, by rfl⟩ : syracuseStep 719499 = 1079249) B1079249
theorem B719511 : Blo 718322 719511 := bstep (se 1 (by rfl) ⟨539633, by rfl⟩ : syracuseStep 719511 = 1079267) B1079267
theorem B719531 : Blo 718322 719531 := bstep (se 1 (by rfl) ⟨539648, by rfl⟩ : syracuseStep 719531 = 1079297) B1079297
theorem B719543 : Blo 718322 719543 := bstep (se 1 (by rfl) ⟨539657, by rfl⟩ : syracuseStep 719543 = 1079315) B1079315
theorem B719563 : Blo 718322 719563 := bstep (se 1 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 719563 = 1079345) B1079345
theorem B1080011 : Blo 718322 1080011 := bstep (se 1 (by rfl) ⟨810008, by rfl⟩ : syracuseStep 1080011 = 1620017) B1620017
theorem B719575 : Blo 718322 719575 := bstep (se 1 (by rfl) ⟨539681, by rfl⟩ : syracuseStep 719575 = 1079363) B1079363
theorem B1080023 : Blo 718322 1080023 := bstep (se 1 (by rfl) ⟨810017, by rfl⟩ : syracuseStep 1080023 = 1620035) B1620035
theorem B1538777 : Blo 718322 1538777 := bstep (se 2 (by rfl) ⟨577041, by rfl⟩ : syracuseStep 1538777 = 1154083) B1154083
theorem B719595 : Blo 718322 719595 := bstep (se 1 (by rfl) ⟨539696, by rfl⟩ : syracuseStep 719595 = 1079393) B1079393
theorem B719607 : Blo 718322 719607 := bstep (se 1 (by rfl) ⟨539705, by rfl⟩ : syracuseStep 719607 = 1079411) B1079411
theorem B719627 : Blo 718322 719627 := bstep (se 1 (by rfl) ⟨539720, by rfl⟩ : syracuseStep 719627 = 1079441) B1079441
theorem B719639 : Blo 718322 719639 := bstep (se 1 (by rfl) ⟨539729, by rfl⟩ : syracuseStep 719639 = 1079459) B1079459
theorem B1080089 : Blo 718322 1080089 := bstep (se 2 (by rfl) ⟨405033, by rfl⟩ : syracuseStep 1080089 = 810067) B810067
theorem B719659 : Blo 718322 719659 := bstep (se 1 (by rfl) ⟨539744, by rfl⟩ : syracuseStep 719659 = 1079489) B1079489
theorem B719671 : Blo 718322 719671 := bstep (se 1 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 719671 = 1079507) B1079507
theorem B719691 : Blo 718322 719691 := bstep (se 1 (by rfl) ⟨539768, by rfl⟩ : syracuseStep 719691 = 1079537) B1079537
theorem B719703 : Blo 718322 719703 := bstep (se 1 (by rfl) ⟨539777, by rfl⟩ : syracuseStep 719703 = 1079555) B1079555
theorem B719723 : Blo 718322 719723 := bstep (se 1 (by rfl) ⟨539792, by rfl⟩ : syracuseStep 719723 = 1079585) B1079585
theorem B719735 : Blo 718322 719735 := bstep (se 1 (by rfl) ⟨539801, by rfl⟩ : syracuseStep 719735 = 1079603) B1079603
theorem B719755 : Blo 718322 719755 := bstep (se 1 (by rfl) ⟨539816, by rfl⟩ : syracuseStep 719755 = 1079633) B1079633
theorem B1080203 : Blo 718322 1080203 := bstep (se 1 (by rfl) ⟨810152, by rfl⟩ : syracuseStep 1080203 = 1620305) B1620305
theorem B719767 : Blo 718322 719767 := bstep (se 1 (by rfl) ⟨539825, by rfl⟩ : syracuseStep 719767 = 1079651) B1079651
theorem B1080215 : Blo 718322 1080215 := bstep (se 1 (by rfl) ⟨810161, by rfl⟩ : syracuseStep 1080215 = 1620323) B1620323
theorem B719787 : Blo 718322 719787 := bstep (se 1 (by rfl) ⟨539840, by rfl⟩ : syracuseStep 719787 = 1079681) B1079681
theorem B719799 : Blo 718322 719799 := bstep (se 1 (by rfl) ⟨539849, by rfl⟩ : syracuseStep 719799 = 1079699) B1079699
theorem B719819 : Blo 718322 719819 := bstep (se 1 (by rfl) ⟨539864, by rfl⟩ : syracuseStep 719819 = 1079729) B1079729
theorem B719831 : Blo 718322 719831 := bstep (se 1 (by rfl) ⟨539873, by rfl⟩ : syracuseStep 719831 = 1079747) B1079747
theorem B1080281 : Blo 718322 1080281 := bstep (se 2 (by rfl) ⟨405105, by rfl⟩ : syracuseStep 1080281 = 810211) B810211
theorem B719851 : Blo 718322 719851 := bstep (se 1 (by rfl) ⟨539888, by rfl⟩ : syracuseStep 719851 = 1079777) B1079777
theorem B719863 : Blo 718322 719863 := bstep (se 1 (by rfl) ⟨539897, by rfl⟩ : syracuseStep 719863 = 1079795) B1079795
theorem B719883 : Blo 718322 719883 := bstep (se 1 (by rfl) ⟨539912, by rfl⟩ : syracuseStep 719883 = 1079825) B1079825
theorem B719895 : Blo 718322 719895 := bstep (se 1 (by rfl) ⟨539921, by rfl⟩ : syracuseStep 719895 = 1079843) B1079843
theorem B719915 : Blo 718322 719915 := bstep (se 1 (by rfl) ⟨539936, by rfl⟩ : syracuseStep 719915 = 1079873) B1079873
theorem B719927 : Blo 718322 719927 := bstep (se 1 (by rfl) ⟨539945, by rfl⟩ : syracuseStep 719927 = 1079891) B1079891
theorem B13859909 : Blo 718322 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B719947 : Blo 718322 719947 := bstep (se 1 (by rfl) ⟨539960, by rfl⟩ : syracuseStep 719947 = 1079921) B1079921
theorem B1080395 : Blo 718322 1080395 := bstep (se 1 (by rfl) ⟨810296, by rfl⟩ : syracuseStep 1080395 = 1620593) B1620593
theorem B719959 : Blo 718322 719959 := bstep (se 1 (by rfl) ⟨539969, by rfl⟩ : syracuseStep 719959 = 1079939) B1079939
theorem B1080407 : Blo 718322 1080407 := bstep (se 1 (by rfl) ⟨810305, by rfl⟩ : syracuseStep 1080407 = 1620611) B1620611
theorem B719979 : Blo 718322 719979 := bstep (se 1 (by rfl) ⟨539984, by rfl⟩ : syracuseStep 719979 = 1079969) B1079969
theorem B719991 : Blo 718322 719991 := bstep (se 1 (by rfl) ⟨539993, by rfl⟩ : syracuseStep 719991 = 1079987) B1079987
theorem B720011 : Blo 718322 720011 := bstep (se 1 (by rfl) ⟨540008, by rfl⟩ : syracuseStep 720011 = 1080017) B1080017
theorem B720023 : Blo 718322 720023 := bstep (se 1 (by rfl) ⟨540017, by rfl⟩ : syracuseStep 720023 = 1080035) B1080035
theorem B1080473 : Blo 718322 1080473 := bstep (se 2 (by rfl) ⟨405177, by rfl⟩ : syracuseStep 1080473 = 810355) B810355
theorem B720043 : Blo 718322 720043 := bstep (se 1 (by rfl) ⟨540032, by rfl⟩ : syracuseStep 720043 = 1080065) B1080065
theorem B720055 : Blo 718322 720055 := bstep (se 1 (by rfl) ⟨540041, by rfl⟩ : syracuseStep 720055 = 1080083) B1080083
theorem B720075 : Blo 718322 720075 := bstep (se 1 (by rfl) ⟨540056, by rfl⟩ : syracuseStep 720075 = 1080113) B1080113
theorem B720087 : Blo 718322 720087 := bstep (se 1 (by rfl) ⟨540065, by rfl⟩ : syracuseStep 720087 = 1080131) B1080131
theorem B720107 : Blo 718322 720107 := bstep (se 1 (by rfl) ⟨540080, by rfl⟩ : syracuseStep 720107 = 1080161) B1080161
theorem B720119 : Blo 718322 720119 := bstep (se 1 (by rfl) ⟨540089, by rfl⟩ : syracuseStep 720119 = 1080179) B1080179
theorem B720139 : Blo 718322 720139 := bstep (se 1 (by rfl) ⟨540104, by rfl⟩ : syracuseStep 720139 = 1080209) B1080209
theorem B1080587 : Blo 718322 1080587 := bstep (se 1 (by rfl) ⟨810440, by rfl⟩ : syracuseStep 1080587 = 1620881) B1620881
theorem B4619537 : Blo 718322 4619537 := bstep (se 2 (by rfl) ⟨1732326, by rfl⟩ : syracuseStep 4619537 = 3464653) B3464653
theorem B720151 : Blo 718322 720151 := bstep (se 1 (by rfl) ⟨540113, by rfl⟩ : syracuseStep 720151 = 1080227) B1080227
theorem B1080599 : Blo 718322 1080599 := bstep (se 1 (by rfl) ⟨810449, by rfl⟩ : syracuseStep 1080599 = 1620899) B1620899
theorem B720171 : Blo 718322 720171 := bstep (se 1 (by rfl) ⟨540128, by rfl⟩ : syracuseStep 720171 = 1080257) B1080257
theorem B720183 : Blo 718322 720183 := bstep (se 1 (by rfl) ⟨540137, by rfl⟩ : syracuseStep 720183 = 1080275) B1080275
theorem B720203 : Blo 718322 720203 := bstep (se 1 (by rfl) ⟨540152, by rfl⟩ : syracuseStep 720203 = 1080305) B1080305
theorem B720215 : Blo 718322 720215 := bstep (se 1 (by rfl) ⟨540161, by rfl⟩ : syracuseStep 720215 = 1080323) B1080323
theorem B1080665 : Blo 718322 1080665 := bstep (se 2 (by rfl) ⟨405249, by rfl⟩ : syracuseStep 1080665 = 810499) B810499
theorem B720235 : Blo 718322 720235 := bstep (se 1 (by rfl) ⟨540176, by rfl⟩ : syracuseStep 720235 = 1080353) B1080353
theorem B1539443 : Blo 718322 1539443 := bstep (se 1 (by rfl) ⟨1154582, by rfl⟩ : syracuseStep 1539443 = 2309165) B2309165
theorem B720247 : Blo 718322 720247 := bstep (se 1 (by rfl) ⟨540185, by rfl⟩ : syracuseStep 720247 = 1080371) B1080371
theorem B720267 : Blo 718322 720267 := bstep (se 1 (by rfl) ⟨540200, by rfl⟩ : syracuseStep 720267 = 1080401) B1080401
theorem B720279 : Blo 718322 720279 := bstep (se 1 (by rfl) ⟨540209, by rfl⟩ : syracuseStep 720279 = 1080419) B1080419
theorem B720299 : Blo 718322 720299 := bstep (se 1 (by rfl) ⟨540224, by rfl⟩ : syracuseStep 720299 = 1080449) B1080449
theorem B720311 : Blo 718322 720311 := bstep (se 1 (by rfl) ⟨540233, by rfl⟩ : syracuseStep 720311 = 1080467) B1080467
theorem B2915777 : Blo 718322 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B720331 : Blo 718322 720331 := bstep (se 1 (by rfl) ⟨540248, by rfl⟩ : syracuseStep 720331 = 1080497) B1080497
theorem B1080779 : Blo 718322 1080779 := bstep (se 1 (by rfl) ⟨810584, by rfl⟩ : syracuseStep 1080779 = 1621169) B1621169
theorem B720343 : Blo 718322 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B1080791 : Blo 718322 1080791 := bstep (se 1 (by rfl) ⟨810593, by rfl⟩ : syracuseStep 1080791 = 1621187) B1621187
theorem B720363 : Blo 718322 720363 := bstep (se 1 (by rfl) ⟨540272, by rfl⟩ : syracuseStep 720363 = 1080545) B1080545
theorem B720375 : Blo 718322 720375 := bstep (se 1 (by rfl) ⟨540281, by rfl⟩ : syracuseStep 720375 = 1080563) B1080563
theorem B720395 : Blo 718322 720395 := bstep (se 1 (by rfl) ⟨540296, by rfl⟩ : syracuseStep 720395 = 1080593) B1080593
theorem B720407 : Blo 718322 720407 := bstep (se 1 (by rfl) ⟨540305, by rfl⟩ : syracuseStep 720407 = 1080611) B1080611
theorem B1080857 : Blo 718322 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B720427 : Blo 718322 720427 := bstep (se 1 (by rfl) ⟨540320, by rfl⟩ : syracuseStep 720427 = 1080641) B1080641
theorem B720439 : Blo 718322 720439 := bstep (se 1 (by rfl) ⟨540329, by rfl⟩ : syracuseStep 720439 = 1080659) B1080659
theorem B720459 : Blo 718322 720459 := bstep (se 1 (by rfl) ⟨540344, by rfl⟩ : syracuseStep 720459 = 1080689) B1080689
theorem B720471 : Blo 718322 720471 := bstep (se 1 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 720471 = 1080707) B1080707
theorem B720491 : Blo 718322 720491 := bstep (se 1 (by rfl) ⟨540368, by rfl⟩ : syracuseStep 720491 = 1080737) B1080737
theorem B720503 : Blo 718322 720503 := bstep (se 1 (by rfl) ⟨540377, by rfl⟩ : syracuseStep 720503 = 1080755) B1080755
theorem B3899011 : Blo 718322 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B720523 : Blo 718322 720523 := bstep (se 1 (by rfl) ⟨540392, by rfl⟩ : syracuseStep 720523 = 1080785) B1080785
theorem B1080971 : Blo 718322 1080971 := bstep (se 1 (by rfl) ⟨810728, by rfl⟩ : syracuseStep 1080971 = 1621457) B1621457
theorem B720535 : Blo 718322 720535 := bstep (se 1 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 720535 = 1080803) B1080803
theorem B1080983 : Blo 718322 1080983 := bstep (se 1 (by rfl) ⟨810737, by rfl⟩ : syracuseStep 1080983 = 1621475) B1621475
theorem B720555 : Blo 718322 720555 := bstep (se 1 (by rfl) ⟨540416, by rfl⟩ : syracuseStep 720555 = 1080833) B1080833
theorem B720567 : Blo 718322 720567 := bstep (se 1 (by rfl) ⟨540425, by rfl⟩ : syracuseStep 720567 = 1080851) B1080851
theorem B720587 : Blo 718322 720587 := bstep (se 1 (by rfl) ⟨540440, by rfl⟩ : syracuseStep 720587 = 1080881) B1080881
theorem B720599 : Blo 718322 720599 := bstep (se 1 (by rfl) ⟨540449, by rfl⟩ : syracuseStep 720599 = 1080899) B1080899
theorem B1408727 : Blo 718322 1408727 := bstep (se 1 (by rfl) ⟨1056545, by rfl⟩ : syracuseStep 1408727 = 2113091) B2113091
theorem B1081049 : Blo 718322 1081049 := bstep (se 2 (by rfl) ⟨405393, by rfl⟩ : syracuseStep 1081049 = 810787) B810787
theorem B720619 : Blo 718322 720619 := bstep (se 1 (by rfl) ⟨540464, by rfl⟩ : syracuseStep 720619 = 1080929) B1080929
theorem B720631 : Blo 718322 720631 := bstep (se 1 (by rfl) ⟨540473, by rfl⟩ : syracuseStep 720631 = 1080947) B1080947
theorem B720651 : Blo 718322 720651 := bstep (se 1 (by rfl) ⟨540488, by rfl⟩ : syracuseStep 720651 = 1080977) B1080977
theorem B2424599 : Blo 718322 2424599 := bstep (se 1 (by rfl) ⟨1818449, by rfl⟩ : syracuseStep 2424599 = 3636899) B3636899
theorem B720663 : Blo 718322 720663 := bstep (se 1 (by rfl) ⟨540497, by rfl⟩ : syracuseStep 720663 = 1080995) B1080995
theorem B1212185 : Blo 718322 1212185 := bstep (se 2 (by rfl) ⟨454569, by rfl⟩ : syracuseStep 1212185 = 909139) B909139
theorem B720683 : Blo 718322 720683 := bstep (se 1 (by rfl) ⟨540512, by rfl⟩ : syracuseStep 720683 = 1081025) B1081025
theorem B720695 : Blo 718322 720695 := bstep (se 1 (by rfl) ⟨540521, by rfl⟩ : syracuseStep 720695 = 1081043) B1081043
theorem B8224577 : Blo 718322 8224577 := bstep (se 2 (by rfl) ⟨3084216, by rfl⟩ : syracuseStep 8224577 = 6168433) B6168433
theorem B720715 : Blo 718322 720715 := bstep (se 1 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 720715 = 1081073) B1081073
theorem B1081163 : Blo 718322 1081163 := bstep (se 1 (by rfl) ⟨810872, by rfl⟩ : syracuseStep 1081163 = 1621745) B1621745
theorem B720727 : Blo 718322 720727 := bstep (se 1 (by rfl) ⟨540545, by rfl⟩ : syracuseStep 720727 = 1081091) B1081091
theorem B1081175 : Blo 718322 1081175 := bstep (se 1 (by rfl) ⟨810881, by rfl⟩ : syracuseStep 1081175 = 1621763) B1621763
theorem B720747 : Blo 718322 720747 := bstep (se 1 (by rfl) ⟨540560, by rfl⟩ : syracuseStep 720747 = 1081121) B1081121
theorem B720759 : Blo 718322 720759 := bstep (se 1 (by rfl) ⟨540569, by rfl⟩ : syracuseStep 720759 = 1081139) B1081139
theorem B720779 : Blo 718322 720779 := bstep (se 1 (by rfl) ⟨540584, by rfl⟩ : syracuseStep 720779 = 1081169) B1081169
theorem B720791 : Blo 718322 720791 := bstep (se 1 (by rfl) ⟨540593, by rfl⟩ : syracuseStep 720791 = 1081187) B1081187
theorem B1212313 : Blo 718322 1212313 := bstep (se 2 (by rfl) ⟨454617, by rfl⟩ : syracuseStep 1212313 = 909235) B909235
theorem B1081241 : Blo 718322 1081241 := bstep (se 2 (by rfl) ⟨405465, by rfl⟩ : syracuseStep 1081241 = 810931) B810931
theorem B720811 : Blo 718322 720811 := bstep (se 1 (by rfl) ⟨540608, by rfl⟩ : syracuseStep 720811 = 1081217) B1081217
theorem B720823 : Blo 718322 720823 := bstep (se 1 (by rfl) ⟨540617, by rfl⟩ : syracuseStep 720823 = 1081235) B1081235
theorem B720843 : Blo 718322 720843 := bstep (se 1 (by rfl) ⟨540632, by rfl⟩ : syracuseStep 720843 = 1081265) B1081265
theorem B720855 : Blo 718322 720855 := bstep (se 1 (by rfl) ⟨540641, by rfl⟩ : syracuseStep 720855 = 1081283) B1081283
theorem B720875 : Blo 718322 720875 := bstep (se 1 (by rfl) ⟨540656, by rfl⟩ : syracuseStep 720875 = 1081313) B1081313
theorem B720887 : Blo 718322 720887 := bstep (se 1 (by rfl) ⟨540665, by rfl⟩ : syracuseStep 720887 = 1081331) B1081331
theorem B720903 : Blo 718322 720903 := bstep (se 1 (by rfl) ⟨540677, by rfl⟩ : syracuseStep 720903 = 1081355) B1081355
theorem B720911 : Blo 718322 720911 := bstep (se 1 (by rfl) ⟨540683, by rfl⟩ : syracuseStep 720911 = 1081367) B1081367
theorem B1212475 : Blo 718322 1212475 := bstep (se 1 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 1212475 = 1818713) B1818713
theorem B1081403 : Blo 718322 1081403 := bstep (se 1 (by rfl) ⟨811052, by rfl⟩ : syracuseStep 1081403 = 1622105) B1622105
theorem B720955 : Blo 718322 720955 := bstep (se 1 (by rfl) ⟨540716, by rfl⟩ : syracuseStep 720955 = 1081433) B1081433
theorem B1081463 : Blo 718322 1081463 := bstep (se 1 (by rfl) ⟨811097, by rfl⟩ : syracuseStep 1081463 = 1622195) B1622195
theorem B721031 : Blo 718322 721031 := bstep (se 1 (by rfl) ⟨540773, by rfl⟩ : syracuseStep 721031 = 1081547) B1081547
theorem B1081487 : Blo 718322 1081487 := bstep (se 1 (by rfl) ⟨811115, by rfl⟩ : syracuseStep 1081487 = 1622231) B1622231
theorem B721039 : Blo 718322 721039 := bstep (se 1 (by rfl) ⟨540779, by rfl⟩ : syracuseStep 721039 = 1081559) B1081559
theorem B1081529 : Blo 718322 1081529 := bstep (se 2 (by rfl) ⟨405573, by rfl⟩ : syracuseStep 1081529 = 811147) B811147
theorem B721083 : Blo 718322 721083 := bstep (se 1 (by rfl) ⟨540812, by rfl⟩ : syracuseStep 721083 = 1081625) B1081625
theorem B1212617 : Blo 718322 1212617 := bstep (se 2 (by rfl) ⟨454731, by rfl⟩ : syracuseStep 1212617 = 909463) B909463
theorem B1081607 : Blo 718322 1081607 := bstep (se 1 (by rfl) ⟨811205, by rfl⟩ : syracuseStep 1081607 = 1622411) B1622411
theorem B721159 : Blo 718322 721159 := bstep (se 1 (by rfl) ⟨540869, by rfl⟩ : syracuseStep 721159 = 1081739) B1081739
theorem B721167 : Blo 718322 721167 := bstep (se 1 (by rfl) ⟨540875, by rfl⟩ : syracuseStep 721167 = 1081751) B1081751
theorem B1081643 : Blo 718322 1081643 := bstep (se 1 (by rfl) ⟨811232, by rfl⟩ : syracuseStep 1081643 = 1622465) B1622465
theorem B721211 : Blo 718322 721211 := bstep (se 1 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 721211 = 1081817) B1081817
theorem B1081673 : Blo 718322 1081673 := bstep (se 2 (by rfl) ⟨405627, by rfl⟩ : syracuseStep 1081673 = 811255) B811255
theorem B721287 : Blo 718322 721287 := bstep (se 1 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 721287 = 1081931) B1081931
theorem B721295 : Blo 718322 721295 := bstep (se 1 (by rfl) ⟨540971, by rfl⟩ : syracuseStep 721295 = 1081943) B1081943
theorem B2458009 : Blo 718322 2458009 := bstep (se 2 (by rfl) ⟨921753, by rfl⟩ : syracuseStep 2458009 = 1843507) B1843507
theorem B1081787 : Blo 718322 1081787 := bstep (se 1 (by rfl) ⟨811340, by rfl⟩ : syracuseStep 1081787 = 1622681) B1622681
theorem B721339 : Blo 718322 721339 := bstep (se 1 (by rfl) ⟨541004, by rfl⟩ : syracuseStep 721339 = 1082009) B1082009
theorem B1081847 : Blo 718322 1081847 := bstep (se 1 (by rfl) ⟨811385, by rfl⟩ : syracuseStep 1081847 = 1622771) B1622771
theorem B721415 : Blo 718322 721415 := bstep (se 1 (by rfl) ⟨541061, by rfl⟩ : syracuseStep 721415 = 1082123) B1082123
theorem B2425355 : Blo 718322 2425355 := bstep (se 1 (by rfl) ⟨1819016, by rfl⟩ : syracuseStep 2425355 = 3638033) B3638033
theorem B1081871 : Blo 718322 1081871 := bstep (se 1 (by rfl) ⟨811403, by rfl⟩ : syracuseStep 1081871 = 1622807) B1622807
theorem B721423 : Blo 718322 721423 := bstep (se 1 (by rfl) ⟨541067, by rfl⟩ : syracuseStep 721423 = 1082135) B1082135
theorem B9208363 : Blo 718322 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B1081913 : Blo 718322 1081913 := bstep (se 2 (by rfl) ⟨405717, by rfl⟩ : syracuseStep 1081913 = 811435) B811435
theorem B721467 : Blo 718322 721467 := bstep (se 1 (by rfl) ⟨541100, by rfl⟩ : syracuseStep 721467 = 1082201) B1082201
theorem B5472845 : Blo 718322 5472845 := bstep (se 3 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 5472845 = 2052317) B2052317
theorem B2425463 : Blo 718322 2425463 := bstep (se 1 (by rfl) ⟨1819097, by rfl⟩ : syracuseStep 2425463 = 3638195) B3638195
theorem B14811767 : Blo 718322 14811767 := bstep (se 1 (by rfl) ⟨11108825, by rfl⟩ : syracuseStep 14811767 = 22217651) B22217651
theorem B1081991 : Blo 718322 1081991 := bstep (se 1 (by rfl) ⟨811493, by rfl⟩ : syracuseStep 1081991 = 1622987) B1622987
theorem B721543 : Blo 718322 721543 := bstep (se 1 (by rfl) ⟨541157, by rfl⟩ : syracuseStep 721543 = 1082315) B1082315
theorem B721551 : Blo 718322 721551 := bstep (se 1 (by rfl) ⟨541163, by rfl⟩ : syracuseStep 721551 = 1082327) B1082327
theorem B1082027 : Blo 718322 1082027 := bstep (se 1 (by rfl) ⟨811520, by rfl⟩ : syracuseStep 1082027 = 1623041) B1623041
theorem B23331509 : Blo 718322 23331509 := bstep (se 5 (by rfl) ⟨1093664, by rfl⟩ : syracuseStep 23331509 = 2187329) B2187329
theorem B721595 : Blo 718322 721595 := bstep (se 1 (by rfl) ⟨541196, by rfl⟩ : syracuseStep 721595 = 1082393) B1082393
theorem B1082057 : Blo 718322 1082057 := bstep (se 2 (by rfl) ⟨405771, by rfl⟩ : syracuseStep 1082057 = 811543) B811543
theorem B721671 : Blo 718322 721671 := bstep (se 1 (by rfl) ⟨541253, by rfl⟩ : syracuseStep 721671 = 1082507) B1082507
theorem B721679 : Blo 718322 721679 := bstep (se 1 (by rfl) ⟨541259, by rfl⟩ : syracuseStep 721679 = 1082519) B1082519
theorem B1082171 : Blo 718322 1082171 := bstep (se 1 (by rfl) ⟨811628, by rfl⟩ : syracuseStep 1082171 = 1623257) B1623257
theorem B721723 : Blo 718322 721723 := bstep (se 1 (by rfl) ⟨541292, by rfl⟩ : syracuseStep 721723 = 1082585) B1082585
theorem B1082231 : Blo 718322 1082231 := bstep (se 1 (by rfl) ⟨811673, by rfl⟩ : syracuseStep 1082231 = 1623347) B1623347
theorem B1213319 : Blo 718322 1213319 := bstep (se 1 (by rfl) ⟨909989, by rfl⟩ : syracuseStep 1213319 = 1819979) B1819979
theorem B820103 : Blo 718322 820103 := bstep (se 1 (by rfl) ⟨615077, by rfl⟩ : syracuseStep 820103 = 1230155) B1230155
theorem B721799 : Blo 718322 721799 := bstep (se 1 (by rfl) ⟨541349, by rfl⟩ : syracuseStep 721799 = 1082699) B1082699
theorem B1082255 : Blo 718322 1082255 := bstep (se 1 (by rfl) ⟨811691, by rfl⟩ : syracuseStep 1082255 = 1623383) B1623383
theorem B721807 : Blo 718322 721807 := bstep (se 1 (by rfl) ⟨541355, by rfl⟩ : syracuseStep 721807 = 1082711) B1082711
theorem B1082297 : Blo 718322 1082297 := bstep (se 2 (by rfl) ⟨405861, by rfl⟩ : syracuseStep 1082297 = 811723) B811723
theorem B721851 : Blo 718322 721851 := bstep (se 1 (by rfl) ⟨541388, by rfl⟩ : syracuseStep 721851 = 1082777) B1082777
theorem B1082375 : Blo 718322 1082375 := bstep (se 1 (by rfl) ⟨811781, by rfl⟩ : syracuseStep 1082375 = 1623563) B1623563
theorem B721927 : Blo 718322 721927 := bstep (se 1 (by rfl) ⟨541445, by rfl⟩ : syracuseStep 721927 = 1082891) B1082891
theorem B721935 : Blo 718322 721935 := bstep (se 1 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 721935 = 1082903) B1082903
theorem B1082411 : Blo 718322 1082411 := bstep (se 1 (by rfl) ⟨811808, by rfl⟩ : syracuseStep 1082411 = 1623617) B1623617
theorem B721979 : Blo 718322 721979 := bstep (se 1 (by rfl) ⟨541484, by rfl⟩ : syracuseStep 721979 = 1082969) B1082969
theorem B1082441 : Blo 718322 1082441 := bstep (se 2 (by rfl) ⟨405915, by rfl⟩ : syracuseStep 1082441 = 811831) B811831
theorem B722055 : Blo 718322 722055 := bstep (se 1 (by rfl) ⟨541541, by rfl⟩ : syracuseStep 722055 = 1083083) B1083083
theorem B722063 : Blo 718322 722063 := bstep (se 1 (by rfl) ⟨541547, by rfl⟩ : syracuseStep 722063 = 1083095) B1083095
theorem B8881325 : Blo 718322 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B1082555 : Blo 718322 1082555 := bstep (se 1 (by rfl) ⟨811916, by rfl⟩ : syracuseStep 1082555 = 1623833) B1623833
theorem B722107 : Blo 718322 722107 := bstep (se 1 (by rfl) ⟨541580, by rfl⟩ : syracuseStep 722107 = 1083161) B1083161
theorem B2426057 : Blo 718322 2426057 := bstep (se 2 (by rfl) ⟨909771, by rfl⟩ : syracuseStep 2426057 = 1819543) B1819543
theorem B1082615 : Blo 718322 1082615 := bstep (se 1 (by rfl) ⟨811961, by rfl⟩ : syracuseStep 1082615 = 1623923) B1623923
theorem B722183 : Blo 718322 722183 := bstep (se 1 (by rfl) ⟨541637, by rfl⟩ : syracuseStep 722183 = 1083275) B1083275
theorem B1082639 : Blo 718322 1082639 := bstep (se 1 (by rfl) ⟨811979, by rfl⟩ : syracuseStep 1082639 = 1623959) B1623959
theorem B722191 : Blo 718322 722191 := bstep (se 1 (by rfl) ⟨541643, by rfl⟩ : syracuseStep 722191 = 1083287) B1083287
theorem B4916513 : Blo 718322 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B1082681 : Blo 718322 1082681 := bstep (se 2 (by rfl) ⟨406005, by rfl⟩ : syracuseStep 1082681 = 812011) B812011
theorem B722235 : Blo 718322 722235 := bstep (se 1 (by rfl) ⟨541676, by rfl⟩ : syracuseStep 722235 = 1083353) B1083353
theorem B1082759 : Blo 718322 1082759 := bstep (se 1 (by rfl) ⟨812069, by rfl⟩ : syracuseStep 1082759 = 1624139) B1624139
theorem B722311 : Blo 718322 722311 := bstep (se 1 (by rfl) ⟨541733, by rfl⟩ : syracuseStep 722311 = 1083467) B1083467
theorem B722319 : Blo 718322 722319 := bstep (se 1 (by rfl) ⟨541739, by rfl⟩ : syracuseStep 722319 = 1083479) B1083479
theorem B3638681 : Blo 718322 3638681 := bstep (se 2 (by rfl) ⟨1364505, by rfl⟩ : syracuseStep 3638681 = 2729011) B2729011
theorem B1082795 : Blo 718322 1082795 := bstep (se 1 (by rfl) ⟨812096, by rfl⟩ : syracuseStep 1082795 = 1624193) B1624193
theorem B1082825 : Blo 718322 1082825 := bstep (se 2 (by rfl) ⟨406059, by rfl⟩ : syracuseStep 1082825 = 812119) B812119
theorem B1213967 : Blo 718322 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B1082939 : Blo 718322 1082939 := bstep (se 1 (by rfl) ⟨812204, by rfl⟩ : syracuseStep 1082939 = 1624409) B1624409
theorem B1082999 : Blo 718322 1082999 := bstep (se 1 (by rfl) ⟨812249, by rfl⟩ : syracuseStep 1082999 = 1624499) B1624499
theorem B1541767 : Blo 718322 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B1083023 : Blo 718322 1083023 := bstep (se 1 (by rfl) ⟨812267, by rfl⟩ : syracuseStep 1083023 = 1624535) B1624535
theorem B1083065 : Blo 718322 1083065 := bstep (se 2 (by rfl) ⟨406149, by rfl⟩ : syracuseStep 1083065 = 812299) B812299
theorem B1083143 : Blo 718322 1083143 := bstep (se 1 (by rfl) ⟨812357, by rfl⟩ : syracuseStep 1083143 = 1624715) B1624715
theorem B1640225 : Blo 718322 1640225 := bstep (se 2 (by rfl) ⟨615084, by rfl⟩ : syracuseStep 1640225 = 1230169) B1230169
theorem B1083179 : Blo 718322 1083179 := bstep (se 1 (by rfl) ⟨812384, by rfl⟩ : syracuseStep 1083179 = 1624769) B1624769
theorem B1083209 : Blo 718322 1083209 := bstep (se 2 (by rfl) ⟨406203, by rfl⟩ : syracuseStep 1083209 = 812407) B812407
theorem B2426759 : Blo 718322 2426759 := bstep (se 1 (by rfl) ⟨1820069, by rfl⟩ : syracuseStep 2426759 = 3640139) B3640139
theorem B1083323 : Blo 718322 1083323 := bstep (se 1 (by rfl) ⟨812492, by rfl⟩ : syracuseStep 1083323 = 1624985) B1624985
theorem B1083383 : Blo 718322 1083383 := bstep (se 1 (by rfl) ⟨812537, by rfl⟩ : syracuseStep 1083383 = 1625075) B1625075
theorem B1083407 : Blo 718322 1083407 := bstep (se 1 (by rfl) ⟨812555, by rfl⟩ : syracuseStep 1083407 = 1625111) B1625111
theorem B1214507 : Blo 718322 1214507 := bstep (se 1 (by rfl) ⟨910880, by rfl⟩ : syracuseStep 1214507 = 1821761) B1821761
theorem B1083449 : Blo 718322 1083449 := bstep (se 2 (by rfl) ⟨406293, by rfl⟩ : syracuseStep 1083449 = 812587) B812587
theorem B2427137 : Blo 718322 2427137 := bstep (se 2 (by rfl) ⟨910176, by rfl⟩ : syracuseStep 2427137 = 1820353) B1820353
theorem B1214905 : Blo 718322 1214905 := bstep (se 2 (by rfl) ⟨455589, by rfl⟩ : syracuseStep 1214905 = 911179) B911179
theorem B21629405 : Blo 718322 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B3083123 : Blo 718322 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B5475275 : Blo 718322 5475275 := bstep (se 1 (by rfl) ⟨4106456, by rfl⟩ : syracuseStep 5475275 = 8212913) B8212913
theorem B2427947 : Blo 718322 2427947 := bstep (se 1 (by rfl) ⟨1820960, by rfl⟩ : syracuseStep 2427947 = 3641921) B3641921
theorem B1215607 : Blo 718322 1215607 := bstep (se 1 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 1215607 = 1823411) B1823411
theorem B986375 : Blo 718322 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B1215803 : Blo 718322 1215803 := bstep (se 1 (by rfl) ⟨911852, by rfl⟩ : syracuseStep 1215803 = 1823705) B1823705
theorem B4623763 : Blo 718322 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B4099531 : Blo 718322 4099531 := bstep (se 1 (by rfl) ⟨3074648, by rfl⟩ : syracuseStep 4099531 = 6149297) B6149297
theorem B6655441 : Blo 718322 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B8326775 : Blo 718322 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B1216201 : Blo 718322 1216201 := bstep (se 2 (by rfl) ⟨456075, by rfl⟩ : syracuseStep 1216201 = 912151) B912151
theorem B3084065 : Blo 718322 3084065 := bstep (se 2 (by rfl) ⟨1156524, by rfl⟩ : syracuseStep 3084065 = 2313049) B2313049
theorem B240422741 : Blo 718322 240422741 := bstep (se 9 (by rfl) ⟨704363, by rfl⟩ : syracuseStep 240422741 = 1408727) B1408727
theorem B7409497 : Blo 718322 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B3641273 : Blo 718322 3641273 := bstep (se 2 (by rfl) ⟨1365477, by rfl⟩ : syracuseStep 3641273 = 2730955) B2730955
theorem B2429243 : Blo 718322 2429243 := bstep (se 1 (by rfl) ⟨1821932, by rfl⟩ : syracuseStep 2429243 = 3643865) B3643865
theorem B1216903 : Blo 718322 1216903 := bstep (se 1 (by rfl) ⟨912677, by rfl⟩ : syracuseStep 1216903 = 1825355) B1825355
theorem B4166167 : Blo 718322 4166167 := bstep (se 1 (by rfl) ⟨3124625, by rfl⟩ : syracuseStep 4166167 = 6249251) B6249251
theorem B7377637 : Blo 718322 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B3085037 : Blo 718322 3085037 := bstep (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) B1156889
theorem B2429729 : Blo 718322 2429729 := bstep (se 2 (by rfl) ⟨911148, by rfl⟩ : syracuseStep 2429729 = 1822297) B1822297
theorem B1217551 : Blo 718322 1217551 := bstep (se 1 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 1217551 = 1826327) B1826327
theorem B3642569 : Blo 718322 3642569 := bstep (se 2 (by rfl) ⟨1365963, by rfl⟩ : syracuseStep 3642569 = 2731927) B2731927
theorem B2430323 : Blo 718322 2430323 := bstep (se 1 (by rfl) ⟨1822742, by rfl⟩ : syracuseStep 2430323 = 3645485) B3645485
theorem B1218091 : Blo 718322 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B13866673 : Blo 718322 13866673 := bstep (se 2 (by rfl) ⟨5200002, by rfl⟩ : syracuseStep 13866673 = 10400005) B10400005
theorem B1218233 : Blo 718322 1218233 := bstep (se 2 (by rfl) ⟨456837, by rfl⟩ : syracuseStep 1218233 = 913675) B913675
theorem B5183281 : Blo 718322 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B4101947 : Blo 718322 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B6559805 : Blo 718322 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B2595073 : Blo 718322 2595073 := bstep (se 2 (by rfl) ⟨973152, by rfl⟩ : syracuseStep 2595073 = 1946305) B1946305
theorem B6232643 : Blo 718322 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B6921035 : Blo 718322 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B2595851 : Blo 718322 2595851 := bstep (se 1 (by rfl) ⟨1946888, by rfl⟩ : syracuseStep 2595851 = 3893777) B3893777
theorem B4103405 : Blo 718322 4103405 := bstep (se 3 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 4103405 = 1538777) B1538777
theorem B2465291 : Blo 718322 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B4103723 : Blo 718322 4103723 := bstep (se 1 (by rfl) ⟨3077792, by rfl⟩ : syracuseStep 4103723 = 6155585) B6155585
theorem B1023607 : Blo 718322 1023607 := bstep (se 1 (by rfl) ⟨767705, by rfl⟩ : syracuseStep 1023607 = 1535411) B1535411
theorem B2727827 : Blo 718322 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B2432915 : Blo 718322 2432915 := bstep (se 1 (by rfl) ⟨1824686, by rfl⟩ : syracuseStep 2432915 = 3649373) B3649373
theorem B5480621 : Blo 718322 5480621 := bstep (se 3 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 5480621 = 2055233) B2055233
theorem B3121523 : Blo 718322 3121523 := bstep (se 1 (by rfl) ⟨2341142, by rfl⟩ : syracuseStep 3121523 = 4682285) B4682285
theorem B5186051 : Blo 718322 5186051 := bstep (se 1 (by rfl) ⟨3889538, by rfl⟩ : syracuseStep 5186051 = 7779077) B7779077
theorem B1024655 : Blo 718322 1024655 := bstep (se 1 (by rfl) ⟨768491, by rfl⟩ : syracuseStep 1024655 = 1536983) B1536983
theorem B1024969 : Blo 718322 1024969 := bstep (se 2 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 1024969 = 768727) B768727
theorem B4105181 : Blo 718322 4105181 := bstep (se 3 (by rfl) ⟨769721, by rfl⟩ : syracuseStep 4105181 = 1539443) B1539443
theorem B2434319 : Blo 718322 2434319 := bstep (se 1 (by rfl) ⟨1825739, by rfl⟩ : syracuseStep 2434319 = 3651479) B3651479
theorem B1779059 : Blo 718322 1779059 := bstep (se 1 (by rfl) ⟨1334294, by rfl⟩ : syracuseStep 1779059 = 2668589) B2668589
theorem B2598259 : Blo 718322 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B2729483 : Blo 718322 2729483 := bstep (se 1 (by rfl) ⟨2047112, by rfl⟩ : syracuseStep 2729483 = 4094225) B4094225
theorem B2434589 : Blo 718322 2434589 := bstep (se 3 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 2434589 = 912971) B912971
theorem B5908261 : Blo 718322 5908261 := bstep (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) B1107799
theorem B6170417 : Blo 718322 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B1943851 : Blo 718322 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B1616399 : Blo 718322 1616399 := bstep (se 1 (by rfl) ⟨1212299, by rfl⟩ : syracuseStep 1616399 = 2424599) B2424599
theorem B1616417 : Blo 718322 1616417 := bstep (se 2 (by rfl) ⟨606156, by rfl⟩ : syracuseStep 1616417 = 1212313) B1212313
theorem B5483051 : Blo 718322 5483051 := bstep (se 1 (by rfl) ⟨4112288, by rfl⟩ : syracuseStep 5483051 = 8224577) B8224577
theorem B12462659 : Blo 718322 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B1616759 : Blo 718322 1616759 := bstep (se 1 (by rfl) ⟨1212569, by rfl⟩ : syracuseStep 1616759 = 2425139) B2425139
theorem B3648401 : Blo 718322 3648401 := bstep (se 2 (by rfl) ⟨1368150, by rfl⟩ : syracuseStep 3648401 = 2736301) B2736301
theorem B2435993 : Blo 718322 2435993 := bstep (se 2 (by rfl) ⟨913497, by rfl⟩ : syracuseStep 2435993 = 1826995) B1826995
theorem B1092523 : Blo 718322 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B1616939 : Blo 718322 1616939 := bstep (se 1 (by rfl) ⟨1212704, by rfl⟩ : syracuseStep 1616939 = 2425409) B2425409
theorem B1617299 : Blo 718322 1617299 := bstep (se 1 (by rfl) ⟨1212974, by rfl⟩ : syracuseStep 1617299 = 2425949) B2425949
theorem B1944985 : Blo 718322 1944985 := bstep (se 2 (by rfl) ⟨729369, by rfl⟩ : syracuseStep 1944985 = 1458739) B1458739
theorem B1617353 : Blo 718322 1617353 := bstep (se 2 (by rfl) ⟨606507, by rfl⟩ : syracuseStep 1617353 = 1213015) B1213015
theorem B4107779 : Blo 718322 4107779 := bstep (se 1 (by rfl) ⟨3080834, by rfl⟩ : syracuseStep 4107779 = 6161669) B6161669
theorem B1027657 : Blo 718322 1027657 := bstep (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) B770743
theorem B2436695 : Blo 718322 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B6565495 : Blo 718322 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B2600839 : Blo 718322 2600839 := bstep (se 1 (by rfl) ⟨1950629, by rfl⟩ : syracuseStep 2600839 = 3901259) B3901259
theorem B3321917 : Blo 718322 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B2437181 : Blo 718322 2437181 := bstep (se 3 (by rfl) ⟨456971, by rfl⟩ : syracuseStep 2437181 = 913943) B913943
theorem B1618055 : Blo 718322 1618055 := bstep (se 1 (by rfl) ⟨1213541, by rfl⟩ : syracuseStep 1618055 = 2427083) B2427083
theorem B1618235 : Blo 718322 1618235 := bstep (se 1 (by rfl) ⟨1213676, by rfl⟩ : syracuseStep 1618235 = 2427353) B2427353
theorem B4993415 : Blo 718322 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B2929043 : Blo 718322 2929043 := bstep (se 1 (by rfl) ⟨2196782, by rfl⟩ : syracuseStep 2929043 = 4393565) B4393565
theorem B1618361 : Blo 718322 1618361 := bstep (se 2 (by rfl) ⟨606885, by rfl⟩ : syracuseStep 1618361 = 1213771) B1213771
theorem B1847819 : Blo 718322 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B5255873 : Blo 718322 5255873 := bstep (se 2 (by rfl) ⟨1970952, by rfl⟩ : syracuseStep 5255873 = 3941905) B3941905
theorem B3453677 : Blo 718322 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B1946369 : Blo 718322 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B1618703 : Blo 718322 1618703 := bstep (se 1 (by rfl) ⟨1214027, by rfl⟩ : syracuseStep 1618703 = 2428055) B2428055
theorem B1618721 : Blo 718322 1618721 := bstep (se 2 (by rfl) ⟨607020, by rfl⟩ : syracuseStep 1618721 = 1214041) B1214041
theorem B31535909 : Blo 718322 31535909 := bstep (se 4 (by rfl) ⟨2956491, by rfl⟩ : syracuseStep 31535909 = 5912983) B5912983
theorem B2307001 : Blo 718322 2307001 := bstep (se 2 (by rfl) ⟨865125, by rfl⟩ : syracuseStep 2307001 = 1730251) B1730251
theorem B4371403 : Blo 718322 4371403 := bstep (se 1 (by rfl) ⟨3278552, by rfl⟩ : syracuseStep 4371403 = 6557105) B6557105
theorem B3650507 : Blo 718322 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B1094699 : Blo 718322 1094699 := bstep (se 1 (by rfl) ⟨821024, by rfl⟩ : syracuseStep 1094699 = 1642049) B1642049
theorem B1619063 : Blo 718322 1619063 := bstep (se 1 (by rfl) ⟨1214297, by rfl⟩ : syracuseStep 1619063 = 2428595) B2428595
theorem B865399 : Blo 718322 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B3650831 : Blo 718322 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B1619243 : Blo 718322 1619243 := bstep (se 1 (by rfl) ⟨1214432, by rfl⟩ : syracuseStep 1619243 = 2428865) B2428865
theorem B2733371 : Blo 718322 2733371 := bstep (se 1 (by rfl) ⟨2050028, by rfl⟩ : syracuseStep 2733371 = 4100057) B4100057
theorem B13841765 : Blo 718322 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B1619603 : Blo 718322 1619603 := bstep (se 1 (by rfl) ⟨1214702, by rfl⟩ : syracuseStep 1619603 = 2429405) B2429405
theorem B1619657 : Blo 718322 1619657 := bstep (se 2 (by rfl) ⟨607371, by rfl⟩ : syracuseStep 1619657 = 1214743) B1214743
theorem B2045711 : Blo 718322 2045711 := bstep (se 1 (by rfl) ⟨1534283, by rfl⟩ : syracuseStep 2045711 = 3068567) B3068567
theorem B2733857 : Blo 718322 2733857 := bstep (se 2 (by rfl) ⟨1025196, by rfl⟩ : syracuseStep 2733857 = 2050393) B2050393
theorem B1095611 : Blo 718322 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B6142189 : Blo 718322 6142189 := bstep (se 3 (by rfl) ⟨1151660, by rfl⟩ : syracuseStep 6142189 = 2303321) B2303321
theorem B2636047 : Blo 718322 2636047 := bstep (se 1 (by rfl) ⟨1977035, by rfl⟩ : syracuseStep 2636047 = 3954071) B3954071
theorem B1620359 : Blo 718322 1620359 := bstep (se 1 (by rfl) ⟨1215269, by rfl⟩ : syracuseStep 1620359 = 2430539) B2430539
theorem B1620539 : Blo 718322 1620539 := bstep (se 1 (by rfl) ⟨1215404, by rfl⟩ : syracuseStep 1620539 = 2430809) B2430809
theorem B1620665 : Blo 718322 1620665 := bstep (se 2 (by rfl) ⟨607749, by rfl⟩ : syracuseStep 1620665 = 1215499) B1215499
theorem B3652289 : Blo 718322 3652289 := bstep (se 2 (by rfl) ⟨1369608, by rfl⟩ : syracuseStep 3652289 = 2739217) B2739217
theorem B2734829 : Blo 718322 2734829 := bstep (se 3 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 2734829 = 1025561) B1025561
theorem B1096463 : Blo 718322 1096463 := bstep (se 1 (by rfl) ⟨822347, by rfl⟩ : syracuseStep 1096463 = 1644695) B1644695
theorem B1948445 : Blo 718322 1948445 := bstep (se 3 (by rfl) ⟨365333, by rfl⟩ : syracuseStep 1948445 = 730667) B730667
theorem B1621007 : Blo 718322 1621007 := bstep (se 1 (by rfl) ⟨1215755, by rfl⟩ : syracuseStep 1621007 = 2431511) B2431511
theorem B6241303 : Blo 718322 6241303 := bstep (se 1 (by rfl) ⟨4680977, by rfl⟩ : syracuseStep 6241303 = 9361955) B9361955
theorem B1621025 : Blo 718322 1621025 := bstep (se 2 (by rfl) ⟨607884, by rfl⟩ : syracuseStep 1621025 = 1215769) B1215769
theorem B2735147 : Blo 718322 2735147 := bstep (se 1 (by rfl) ⟨2051360, by rfl⟩ : syracuseStep 2735147 = 4102721) B4102721
theorem B4996183 : Blo 718322 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B6929495 : Blo 718322 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B2047123 : Blo 718322 2047123 := bstep (se 1 (by rfl) ⟨1535342, by rfl⟩ : syracuseStep 2047123 = 3070685) B3070685
theorem B2047351 : Blo 718322 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B1621367 : Blo 718322 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B1621547 : Blo 718322 1621547 := bstep (se 1 (by rfl) ⟨1216160, by rfl⟩ : syracuseStep 1621547 = 2432321) B2432321
theorem B769807 : Blo 718322 769807 := bstep (se 1 (by rfl) ⟨577355, by rfl⟩ : syracuseStep 769807 = 1154711) B1154711
theorem B1949483 : Blo 718322 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B1621907 : Blo 718322 1621907 := bstep (se 1 (by rfl) ⟨1216430, by rfl⟩ : syracuseStep 1621907 = 2432861) B2432861
theorem B1818521 : Blo 718322 1818521 := bstep (se 2 (by rfl) ⟨681945, by rfl⟩ : syracuseStep 1818521 = 1363891) B1363891
theorem B1621961 : Blo 718322 1621961 := bstep (se 2 (by rfl) ⟨608235, by rfl⟩ : syracuseStep 1621961 = 1216471) B1216471
theorem B3653585 : Blo 718322 3653585 := bstep (se 2 (by rfl) ⟨1370094, by rfl⟩ : syracuseStep 3653585 = 2740189) B2740189
theorem B1818683 : Blo 718322 1818683 := bstep (se 1 (by rfl) ⟨1364012, by rfl⟩ : syracuseStep 1818683 = 2728025) B2728025
theorem B4112471 : Blo 718322 4112471 := bstep (se 1 (by rfl) ⟨3084353, by rfl⟩ : syracuseStep 4112471 = 6168707) B6168707
theorem B6144173 : Blo 718322 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B3948745 : Blo 718322 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B1818895 : Blo 718322 1818895 := bstep (se 1 (by rfl) ⟨1364171, by rfl⟩ : syracuseStep 1818895 = 2728343) B2728343
theorem B1819169 : Blo 718322 1819169 := bstep (se 2 (by rfl) ⟨682188, by rfl⟩ : syracuseStep 1819169 = 1364377) B1364377
theorem B3457579 : Blo 718322 3457579 := bstep (se 1 (by rfl) ⟨2593184, by rfl⟩ : syracuseStep 3457579 = 5186369) B5186369
theorem B2048627 : Blo 718322 2048627 := bstep (se 1 (by rfl) ⟨1536470, by rfl⟩ : syracuseStep 2048627 = 3072941) B3072941
theorem B1622663 : Blo 718322 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B1622843 : Blo 718322 1622843 := bstep (se 1 (by rfl) ⟨1217132, by rfl⟩ : syracuseStep 1622843 = 2434265) B2434265
theorem B2343815 : Blo 718322 2343815 := bstep (se 1 (by rfl) ⟨1757861, by rfl⟩ : syracuseStep 2343815 = 3515723) B3515723
theorem B1622969 : Blo 718322 1622969 := bstep (se 2 (by rfl) ⟨608613, by rfl⟩ : syracuseStep 1622969 = 1217227) B1217227
theorem B2048969 : Blo 718322 2048969 := bstep (se 2 (by rfl) ⟨768363, by rfl⟩ : syracuseStep 2048969 = 1536727) B1536727
theorem B2049083 : Blo 718322 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B2049209 : Blo 718322 2049209 := bstep (se 2 (by rfl) ⟨768453, by rfl⟩ : syracuseStep 2049209 = 1536907) B1536907
theorem B1623311 : Blo 718322 1623311 := bstep (se 1 (by rfl) ⟨1217483, by rfl⟩ : syracuseStep 1623311 = 2434967) B2434967
theorem B1623329 : Blo 718322 1623329 := bstep (se 2 (by rfl) ⟨608748, by rfl⟩ : syracuseStep 1623329 = 1217497) B1217497
theorem B13813091 : Blo 718322 13813091 := bstep (se 1 (by rfl) ⟨10359818, by rfl⟩ : syracuseStep 13813091 = 20719637) B20719637
theorem B2082167 : Blo 718322 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B3884435 : Blo 718322 3884435 := bstep (se 1 (by rfl) ⟨2913326, by rfl⟩ : syracuseStep 3884435 = 5826653) B5826653
theorem B1230265 : Blo 718322 1230265 := bstep (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) B922699
theorem B1820171 : Blo 718322 1820171 := bstep (se 1 (by rfl) ⟨1365128, by rfl⟩ : syracuseStep 1820171 = 2730257) B2730257
theorem B8209997 : Blo 718322 8209997 := bstep (se 3 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 8209997 = 3078749) B3078749
theorem B1623671 : Blo 718322 1623671 := bstep (se 1 (by rfl) ⟨1217753, by rfl⟩ : syracuseStep 1623671 = 2435507) B2435507
theorem B1951385 : Blo 718322 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B1623851 : Blo 718322 1623851 := bstep (se 1 (by rfl) ⟨1217888, by rfl⟩ : syracuseStep 1623851 = 2435777) B2435777
theorem B5457779 : Blo 718322 5457779 := bstep (se 1 (by rfl) ⟨4093334, by rfl⟩ : syracuseStep 5457779 = 8186669) B8186669
theorem B3655691 : Blo 718322 3655691 := bstep (se 1 (by rfl) ⟨2741768, by rfl⟩ : syracuseStep 3655691 = 5483537) B5483537
theorem B4376605 : Blo 718322 4376605 := bstep (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) B1641227
theorem B1820819 : Blo 718322 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B1624211 : Blo 718322 1624211 := bstep (se 1 (by rfl) ⟨1218158, by rfl⟩ : syracuseStep 1624211 = 2436317) B2436317
theorem B3655853 : Blo 718322 3655853 := bstep (se 3 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 3655853 = 1370945) B1370945
theorem B1624265 : Blo 718322 1624265 := bstep (se 2 (by rfl) ⟨609099, by rfl⟩ : syracuseStep 1624265 = 1218199) B1218199
theorem B15616273 : Blo 718322 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B1821113 : Blo 718322 1821113 := bstep (se 2 (by rfl) ⟨682917, by rfl⟩ : syracuseStep 1821113 = 1365835) B1365835
theorem B6146563 : Blo 718322 6146563 := bstep (se 1 (by rfl) ⟨4609922, by rfl⟩ : syracuseStep 6146563 = 9219845) B9219845
theorem B2738717 : Blo 718322 2738717 := bstep (se 3 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 2738717 = 1027019) B1027019
theorem B2738731 : Blo 718322 2738731 := bstep (se 1 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 2738731 = 4108097) B4108097
theorem B9226817 : Blo 718322 9226817 := bstep (se 2 (by rfl) ⟨3460056, by rfl⟩ : syracuseStep 9226817 = 6920113) B6920113
theorem B10406465 : Blo 718322 10406465 := bstep (se 2 (by rfl) ⟨3902424, by rfl⟩ : syracuseStep 10406465 = 7804849) B7804849
theorem B6933185 : Blo 718322 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B5196545 : Blo 718322 5196545 := bstep (se 2 (by rfl) ⟨1948704, by rfl⟩ : syracuseStep 5196545 = 3897409) B3897409
theorem B15584015 : Blo 718322 15584015 := bstep (se 1 (by rfl) ⟨11688011, by rfl⟩ : syracuseStep 15584015 = 23376023) B23376023
theorem B2050859 : Blo 718322 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B1624967 : Blo 718322 1624967 := bstep (se 1 (by rfl) ⟨1218725, by rfl⟩ : syracuseStep 1624967 = 2437451) B2437451
theorem B1625147 : Blo 718322 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B1821811 : Blo 718322 1821811 := bstep (se 1 (by rfl) ⟨1366358, by rfl⟩ : syracuseStep 1821811 = 2732717) B2732717
theorem B1821953 : Blo 718322 1821953 := bstep (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) B1366465
theorem B4607441 : Blo 718322 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B11685475 : Blo 718322 11685475 := bstep (se 1 (by rfl) ⟨8764106, by rfl⟩ : syracuseStep 11685475 = 17528213) B17528213
theorem B2805367 : Blo 718322 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B1822409 : Blo 718322 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B2051851 : Blo 718322 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B2052125 : Blo 718322 2052125 := bstep (se 3 (by rfl) ⟨384773, by rfl⟩ : syracuseStep 2052125 = 769547) B769547
theorem B1822763 : Blo 718322 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B7196987 : Blo 718322 7196987 := bstep (se 1 (by rfl) ⟨5397740, by rfl⟩ : syracuseStep 7196987 = 10795481) B10795481
theorem B1364627 : Blo 718322 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B1364681 : Blo 718322 1364681 := bstep (se 2 (by rfl) ⟨511755, by rfl⟩ : syracuseStep 1364681 = 1023511) B1023511
theorem B3461903 : Blo 718322 3461903 := bstep (se 1 (by rfl) ⟨2596427, by rfl⟩ : syracuseStep 3461903 = 5192855) B5192855
theorem B1364779 : Blo 718322 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B5198681 : Blo 718322 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B1823755 : Blo 718322 1823755 := bstep (se 1 (by rfl) ⟨1367816, by rfl⟩ : syracuseStep 1823755 = 2735633) B2735633
theorem B1365007 : Blo 718322 1365007 := bstep (se 1 (by rfl) ⟨1023755, by rfl⟩ : syracuseStep 1365007 = 2047511) B2047511
theorem B1823897 : Blo 718322 1823897 := bstep (se 2 (by rfl) ⟨683961, by rfl⟩ : syracuseStep 1823897 = 1367923) B1367923
theorem B808123 : Blo 718322 808123 := bstep (se 1 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 808123 = 1212185) B1212185
theorem B1824059 : Blo 718322 1824059 := bstep (se 1 (by rfl) ⟨1368044, by rfl⟩ : syracuseStep 1824059 = 2736089) B2736089
theorem B2184509 : Blo 718322 2184509 := bstep (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) B819191
theorem B1725953 : Blo 718322 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B808591 : Blo 718322 808591 := bstep (se 1 (by rfl) ⟨606443, by rfl⟩ : syracuseStep 808591 = 1212887) B1212887
theorem B1824403 : Blo 718322 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B17553125 : Blo 718322 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B1824545 : Blo 718322 1824545 := bstep (se 2 (by rfl) ⟨684204, by rfl⟩ : syracuseStep 1824545 = 1368409) B1368409
theorem B972617 : Blo 718322 972617 := bstep (se 2 (by rfl) ⟨364731, by rfl⟩ : syracuseStep 972617 = 729463) B729463
theorem B2054231 : Blo 718322 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B809095 : Blo 718322 809095 := bstep (se 1 (by rfl) ⟨606821, by rfl⟩ : syracuseStep 809095 = 1213643) B1213643
theorem B809275 : Blo 718322 809275 := bstep (se 1 (by rfl) ⟨606956, by rfl⟩ : syracuseStep 809275 = 1213913) B1213913
theorem B2054459 : Blo 718322 2054459 := bstep (se 1 (by rfl) ⟨1540844, by rfl⟩ : syracuseStep 2054459 = 3081689) B3081689
theorem B2054585 : Blo 718322 2054585 := bstep (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) B1540939
theorem B1497545 : Blo 718322 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B1366571 : Blo 718322 1366571 := bstep (se 1 (by rfl) ⟨1024928, by rfl⟩ : syracuseStep 1366571 = 2049857) B2049857
theorem B1825537 : Blo 718322 1825537 := bstep (se 2 (by rfl) ⟨684576, by rfl⟩ : syracuseStep 1825537 = 1369153) B1369153
theorem B809743 : Blo 718322 809743 := bstep (se 1 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 809743 = 1214615) B1214615
theorem B810247 : Blo 718322 810247 := bstep (se 1 (by rfl) ⟨607685, by rfl⟩ : syracuseStep 810247 = 1215371) B1215371
theorem B1826135 : Blo 718322 1826135 := bstep (se 1 (by rfl) ⟨1369601, by rfl⟩ : syracuseStep 1826135 = 2739203) B2739203
theorem B810427 : Blo 718322 810427 := bstep (se 1 (by rfl) ⟨607820, by rfl⟩ : syracuseStep 810427 = 1215641) B1215641
theorem B1826347 : Blo 718322 1826347 := bstep (se 1 (by rfl) ⟨1369760, by rfl⟩ : syracuseStep 1826347 = 2739521) B2739521
theorem B1826489 : Blo 718322 1826489 := bstep (se 2 (by rfl) ⟨684933, by rfl⟩ : syracuseStep 1826489 = 1369867) B1369867
theorem B974521 : Blo 718322 974521 := bstep (se 2 (by rfl) ⟨365445, by rfl⟩ : syracuseStep 974521 = 730891) B730891
theorem B810895 : Blo 718322 810895 := bstep (se 1 (by rfl) ⟨608171, by rfl⟩ : syracuseStep 810895 = 1216343) B1216343
theorem B6938531 : Blo 718322 6938531 := bstep (se 1 (by rfl) ⟨5203898, by rfl⟩ : syracuseStep 6938531 = 10407797) B10407797
theorem B2056225 : Blo 718322 2056225 := bstep (se 2 (by rfl) ⟨771084, by rfl⟩ : syracuseStep 2056225 = 1542169) B1542169
theorem B5202053 : Blo 718322 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B1728665 : Blo 718322 1728665 := bstep (se 2 (by rfl) ⟨648249, by rfl⟩ : syracuseStep 1728665 = 1296499) B1296499
theorem B1368265 : Blo 718322 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B909559 : Blo 718322 909559 := bstep (se 1 (by rfl) ⟨682169, by rfl⟩ : syracuseStep 909559 = 1364339) B1364339
theorem B811399 : Blo 718322 811399 := bstep (se 1 (by rfl) ⟨608549, by rfl⟩ : syracuseStep 811399 = 1217099) B1217099
theorem B2056715 : Blo 718322 2056715 := bstep (se 1 (by rfl) ⟨1542536, by rfl⟩ : syracuseStep 2056715 = 3085073) B3085073
theorem B909883 : Blo 718322 909883 := bstep (se 1 (by rfl) ⟨682412, by rfl⟩ : syracuseStep 909883 = 1364825) B1364825
theorem B811579 : Blo 718322 811579 := bstep (se 1 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 811579 = 1217369) B1217369
theorem B3072599 : Blo 718322 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B1827481 : Blo 718322 1827481 := bstep (se 2 (by rfl) ⟨685305, by rfl⟩ : syracuseStep 1827481 = 1370611) B1370611
theorem B1827643 : Blo 718322 1827643 := bstep (se 1 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 1827643 = 2741465) B2741465
theorem B1827785 : Blo 718322 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B812047 : Blo 718322 812047 := bstep (se 1 (by rfl) ⟨609035, by rfl⟩ : syracuseStep 812047 = 1218071) B1218071
theorem B910379 : Blo 718322 910379 := bstep (se 1 (by rfl) ⟨682784, by rfl⟩ : syracuseStep 910379 = 1365569) B1365569
theorem B976007 : Blo 718322 976007 := bstep (se 1 (by rfl) ⟨732005, by rfl⟩ : syracuseStep 976007 = 1464011) B1464011
theorem B4678829 : Blo 718322 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1729721 : Blo 718322 1729721 := bstep (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) B1297291
theorem B1828129 : Blo 718322 1828129 := bstep (se 2 (by rfl) ⟨685548, by rfl⟩ : syracuseStep 1828129 = 1371097) B1371097
theorem B910855 : Blo 718322 910855 := bstep (se 1 (by rfl) ⟨683141, by rfl⟩ : syracuseStep 910855 = 1366283) B1366283
theorem B812551 : Blo 718322 812551 := bstep (se 1 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 812551 = 1218827) B1218827
theorem B911351 : Blo 718322 911351 := bstep (se 1 (by rfl) ⟨683513, by rfl⟩ : syracuseStep 911351 = 1367027) B1367027
theorem B1370171 : Blo 718322 1370171 := bstep (se 1 (by rfl) ⟨1027628, by rfl⟩ : syracuseStep 1370171 = 2055257) B2055257
theorem B4614205 : Blo 718322 4614205 := bstep (se 3 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 4614205 = 1730327) B1730327
theorem B911503 : Blo 718322 911503 := bstep (se 1 (by rfl) ⟨683627, by rfl⟩ : syracuseStep 911503 = 1367255) B1367255
theorem B1534241 : Blo 718322 1534241 := bstep (se 2 (by rfl) ⟨575340, by rfl⟩ : syracuseStep 1534241 = 1150681) B1150681
theorem B911675 : Blo 718322 911675 := bstep (se 1 (by rfl) ⟨683756, by rfl⟩ : syracuseStep 911675 = 1367513) B1367513
theorem B4155833 : Blo 718322 4155833 := bstep (se 2 (by rfl) ⟨1558437, by rfl⟩ : syracuseStep 4155833 = 3116875) B3116875
theorem B1370657 : Blo 718322 1370657 := bstep (se 2 (by rfl) ⟨513996, by rfl⟩ : syracuseStep 1370657 = 1027993) B1027993
theorem B4156211 : Blo 718322 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B1370999 : Blo 718322 1370999 := bstep (se 1 (by rfl) ⟨1028249, by rfl⟩ : syracuseStep 1370999 = 2056499) B2056499
theorem B3337453 : Blo 718322 3337453 := bstep (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) B1251545
theorem B912647 : Blo 718322 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B126610897 : Blo 718322 126610897 := bstep (se 2 (by rfl) ⟨47479086, by rfl⟩ : syracuseStep 126610897 = 94958173) B94958173
theorem B1732097 : Blo 718322 1732097 := bstep (se 2 (by rfl) ⟨649536, by rfl⟩ : syracuseStep 1732097 = 1299073) B1299073
theorem B7400963 : Blo 718322 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B8220203 : Blo 718322 8220203 := bstep (se 1 (by rfl) ⟨6165152, by rfl⟩ : syracuseStep 8220203 = 12330305) B12330305
theorem B4615973 : Blo 718322 4615973 := bstep (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) B865495
theorem B7401253 : Blo 718322 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B913295 : Blo 718322 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B1077563 : Blo 718322 1077563 := bstep (se 1 (by rfl) ⟨808172, by rfl⟩ : syracuseStep 1077563 = 1616345) B1616345
theorem B1077623 : Blo 718322 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B1077647 : Blo 718322 1077647 := bstep (se 1 (by rfl) ⟨808235, by rfl⟩ : syracuseStep 1077647 = 1616471) B1616471
theorem B1077689 : Blo 718322 1077689 := bstep (se 2 (by rfl) ⟨404133, by rfl⟩ : syracuseStep 1077689 = 808267) B808267
theorem B3502595 : Blo 718322 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B1077767 : Blo 718322 1077767 := bstep (se 1 (by rfl) ⟨808325, by rfl⟩ : syracuseStep 1077767 = 1616651) B1616651
theorem B1077803 : Blo 718322 1077803 := bstep (se 1 (by rfl) ⟨808352, by rfl⟩ : syracuseStep 1077803 = 1616705) B1616705
theorem B1077833 : Blo 718322 1077833 := bstep (se 2 (by rfl) ⟨404187, by rfl⟩ : syracuseStep 1077833 = 808375) B808375
theorem B1077947 : Blo 718322 1077947 := bstep (se 1 (by rfl) ⟨808460, by rfl⟩ : syracuseStep 1077947 = 1616921) B1616921
theorem B1078007 : Blo 718322 1078007 := bstep (se 1 (by rfl) ⟨808505, by rfl⟩ : syracuseStep 1078007 = 1617011) B1617011
theorem B1078031 : Blo 718322 1078031 := bstep (se 1 (by rfl) ⟨808523, by rfl⟩ : syracuseStep 1078031 = 1617047) B1617047
theorem B1078073 : Blo 718322 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B1078151 : Blo 718322 1078151 := bstep (se 1 (by rfl) ⟨808613, by rfl⟩ : syracuseStep 1078151 = 1617227) B1617227
theorem B1078187 : Blo 718322 1078187 := bstep (se 1 (by rfl) ⟨808640, by rfl⟩ : syracuseStep 1078187 = 1617281) B1617281
theorem B1078217 : Blo 718322 1078217 := bstep (se 2 (by rfl) ⟨404331, by rfl⟩ : syracuseStep 1078217 = 808663) B808663
theorem B3470359 : Blo 718322 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B2192417 : Blo 718322 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B1078331 : Blo 718322 1078331 := bstep (se 1 (by rfl) ⟨808748, by rfl⟩ : syracuseStep 1078331 = 1617497) B1617497
theorem B1733719 : Blo 718322 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B1078391 : Blo 718322 1078391 := bstep (se 1 (by rfl) ⟨808793, by rfl⟩ : syracuseStep 1078391 = 1617587) B1617587
theorem B1078415 : Blo 718322 1078415 := bstep (se 1 (by rfl) ⟨808811, by rfl⟩ : syracuseStep 1078415 = 1617623) B1617623
theorem B1078457 : Blo 718322 1078457 := bstep (se 2 (by rfl) ⟨404421, by rfl⟩ : syracuseStep 1078457 = 808843) B808843
theorem B1078535 : Blo 718322 1078535 := bstep (se 1 (by rfl) ⟨808901, by rfl⟩ : syracuseStep 1078535 = 1617803) B1617803
theorem B4093199 : Blo 718322 4093199 := bstep (se 1 (by rfl) ⟨3069899, by rfl⟩ : syracuseStep 4093199 = 6139799) B6139799
theorem B1078571 : Blo 718322 1078571 := bstep (se 1 (by rfl) ⟨808928, by rfl⟩ : syracuseStep 1078571 = 1617857) B1617857
theorem B1078601 : Blo 718322 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B1537427 : Blo 718322 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B3339667 : Blo 718322 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B3503513 : Blo 718322 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B1078715 : Blo 718322 1078715 := bstep (se 1 (by rfl) ⟨809036, by rfl⟩ : syracuseStep 1078715 = 1618073) B1618073
theorem B1078775 : Blo 718322 1078775 := bstep (se 1 (by rfl) ⟨809081, by rfl⟩ : syracuseStep 1078775 = 1618163) B1618163
theorem B718343 : Blo 718322 718343 := bstep (se 1 (by rfl) ⟨538757, by rfl⟩ : syracuseStep 718343 = 1077515) B1077515
theorem B718351 : Blo 718322 718351 := bstep (se 1 (by rfl) ⟨538763, by rfl⟩ : syracuseStep 718351 = 1077527) B1077527
theorem B1078799 : Blo 718322 1078799 := bstep (se 1 (by rfl) ⟨809099, by rfl⟩ : syracuseStep 1078799 = 1618199) B1618199
theorem B1078841 : Blo 718322 1078841 := bstep (se 2 (by rfl) ⟨404565, by rfl⟩ : syracuseStep 1078841 = 809131) B809131
theorem B718395 : Blo 718322 718395 := bstep (se 1 (by rfl) ⟨538796, by rfl⟩ : syracuseStep 718395 = 1077593) B1077593
theorem B718471 : Blo 718322 718471 := bstep (se 1 (by rfl) ⟨538853, by rfl⟩ : syracuseStep 718471 = 1077707) B1077707
theorem B1078919 : Blo 718322 1078919 := bstep (se 1 (by rfl) ⟨809189, by rfl⟩ : syracuseStep 1078919 = 1618379) B1618379
theorem B718479 : Blo 718322 718479 := bstep (se 1 (by rfl) ⟨538859, by rfl⟩ : syracuseStep 718479 = 1077719) B1077719
theorem B1078955 : Blo 718322 1078955 := bstep (se 1 (by rfl) ⟨809216, by rfl⟩ : syracuseStep 1078955 = 1618433) B1618433
theorem B718523 : Blo 718322 718523 := bstep (se 1 (by rfl) ⟨538892, by rfl⟩ : syracuseStep 718523 = 1077785) B1077785
theorem B1078985 : Blo 718322 1078985 := bstep (se 2 (by rfl) ⟨404619, by rfl⟩ : syracuseStep 1078985 = 809239) B809239
theorem B718599 : Blo 718322 718599 := bstep (se 1 (by rfl) ⟨538949, by rfl⟩ : syracuseStep 718599 = 1077899) B1077899
theorem B718607 : Blo 718322 718607 := bstep (se 1 (by rfl) ⟨538955, by rfl⟩ : syracuseStep 718607 = 1077911) B1077911
theorem B718651 : Blo 718322 718651 := bstep (se 1 (by rfl) ⟨538988, by rfl⟩ : syracuseStep 718651 = 1077977) B1077977
theorem B1079099 : Blo 718322 1079099 := bstep (se 1 (by rfl) ⟨809324, by rfl⟩ : syracuseStep 1079099 = 1618649) B1618649
theorem B1079159 : Blo 718322 1079159 := bstep (se 1 (by rfl) ⟨809369, by rfl⟩ : syracuseStep 1079159 = 1618739) B1618739
theorem B718727 : Blo 718322 718727 := bstep (se 1 (by rfl) ⟨539045, by rfl⟩ : syracuseStep 718727 = 1078091) B1078091
theorem B718735 : Blo 718322 718735 := bstep (se 1 (by rfl) ⟨539051, by rfl⟩ : syracuseStep 718735 = 1078103) B1078103
theorem B1079183 : Blo 718322 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1079225 : Blo 718322 1079225 := bstep (se 2 (by rfl) ⟨404709, by rfl⟩ : syracuseStep 1079225 = 809419) B809419
theorem B718779 : Blo 718322 718779 := bstep (se 1 (by rfl) ⟨539084, by rfl⟩ : syracuseStep 718779 = 1078169) B1078169
theorem B718855 : Blo 718322 718855 := bstep (se 1 (by rfl) ⟨539141, by rfl⟩ : syracuseStep 718855 = 1078283) B1078283
theorem B1079303 : Blo 718322 1079303 := bstep (se 1 (by rfl) ⟨809477, by rfl⟩ : syracuseStep 1079303 = 1618955) B1618955
theorem B718863 : Blo 718322 718863 := bstep (se 1 (by rfl) ⟨539147, by rfl⟩ : syracuseStep 718863 = 1078295) B1078295
theorem B7010327 : Blo 718322 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B1079339 : Blo 718322 1079339 := bstep (se 1 (by rfl) ⟨809504, by rfl⟩ : syracuseStep 1079339 = 1619009) B1619009
theorem B718907 : Blo 718322 718907 := bstep (se 1 (by rfl) ⟨539180, by rfl⟩ : syracuseStep 718907 = 1078361) B1078361
theorem B1079369 : Blo 718322 1079369 := bstep (se 2 (by rfl) ⟨404763, by rfl⟩ : syracuseStep 1079369 = 809527) B809527
theorem B718983 : Blo 718322 718983 := bstep (se 1 (by rfl) ⟨539237, by rfl⟩ : syracuseStep 718983 = 1078475) B1078475
theorem B718991 : Blo 718322 718991 := bstep (se 1 (by rfl) ⟨539243, by rfl⟩ : syracuseStep 718991 = 1078487) B1078487
theorem B719035 : Blo 718322 719035 := bstep (se 1 (by rfl) ⟨539276, by rfl⟩ : syracuseStep 719035 = 1078553) B1078553
theorem B1079483 : Blo 718322 1079483 := bstep (se 1 (by rfl) ⟨809612, by rfl⟩ : syracuseStep 1079483 = 1619225) B1619225
theorem B1079543 : Blo 718322 1079543 := bstep (se 1 (by rfl) ⟨809657, by rfl⟩ : syracuseStep 1079543 = 1619315) B1619315
theorem B719111 : Blo 718322 719111 := bstep (se 1 (by rfl) ⟨539333, by rfl⟩ : syracuseStep 719111 = 1078667) B1078667
theorem B719119 : Blo 718322 719119 := bstep (se 1 (by rfl) ⟨539339, by rfl⟩ : syracuseStep 719119 = 1078679) B1078679
theorem B1079567 : Blo 718322 1079567 := bstep (se 1 (by rfl) ⟨809675, by rfl⟩ : syracuseStep 1079567 = 1619351) B1619351
theorem B1079609 : Blo 718322 1079609 := bstep (se 2 (by rfl) ⟨404853, by rfl⟩ : syracuseStep 1079609 = 809707) B809707
theorem B719163 : Blo 718322 719163 := bstep (se 1 (by rfl) ⟨539372, by rfl⟩ : syracuseStep 719163 = 1078745) B1078745
theorem B719239 : Blo 718322 719239 := bstep (se 1 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 719239 = 1078859) B1078859
theorem B1079687 : Blo 718322 1079687 := bstep (se 1 (by rfl) ⟨809765, by rfl⟩ : syracuseStep 1079687 = 1619531) B1619531
theorem B719247 : Blo 718322 719247 := bstep (se 1 (by rfl) ⟨539435, by rfl⟩ : syracuseStep 719247 = 1078871) B1078871
theorem B1079723 : Blo 718322 1079723 := bstep (se 1 (by rfl) ⟨809792, by rfl⟩ : syracuseStep 1079723 = 1619585) B1619585
theorem B719291 : Blo 718322 719291 := bstep (se 1 (by rfl) ⟨539468, by rfl⟩ : syracuseStep 719291 = 1078937) B1078937
theorem B1079753 : Blo 718322 1079753 := bstep (se 2 (by rfl) ⟨404907, by rfl⟩ : syracuseStep 1079753 = 809815) B809815
theorem B719367 : Blo 718322 719367 := bstep (se 1 (by rfl) ⟨539525, by rfl⟩ : syracuseStep 719367 = 1079051) B1079051
theorem B719375 : Blo 718322 719375 := bstep (se 1 (by rfl) ⟨539531, by rfl⟩ : syracuseStep 719375 = 1079063) B1079063
theorem B719419 : Blo 718322 719419 := bstep (se 1 (by rfl) ⟨539564, by rfl⟩ : syracuseStep 719419 = 1079129) B1079129
theorem B1079867 : Blo 718322 1079867 := bstep (se 1 (by rfl) ⟨809900, by rfl⟩ : syracuseStep 1079867 = 1619801) B1619801
theorem B1079927 : Blo 718322 1079927 := bstep (se 1 (by rfl) ⟨809945, by rfl⟩ : syracuseStep 1079927 = 1619891) B1619891
theorem B719495 : Blo 718322 719495 := bstep (se 1 (by rfl) ⟨539621, by rfl⟩ : syracuseStep 719495 = 1079243) B1079243
theorem B719503 : Blo 718322 719503 := bstep (se 1 (by rfl) ⟨539627, by rfl⟩ : syracuseStep 719503 = 1079255) B1079255
theorem B1079951 : Blo 718322 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B1079993 : Blo 718322 1079993 := bstep (se 2 (by rfl) ⟨404997, by rfl⟩ : syracuseStep 1079993 = 809995) B809995
theorem B719547 : Blo 718322 719547 := bstep (se 1 (by rfl) ⟨539660, by rfl⟩ : syracuseStep 719547 = 1079321) B1079321
theorem B4094657 : Blo 718322 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B719623 : Blo 718322 719623 := bstep (se 1 (by rfl) ⟨539717, by rfl⟩ : syracuseStep 719623 = 1079435) B1079435
theorem B1080071 : Blo 718322 1080071 := bstep (se 1 (by rfl) ⟨810053, by rfl⟩ : syracuseStep 1080071 = 1620107) B1620107
theorem B719631 : Blo 718322 719631 := bstep (se 1 (by rfl) ⟨539723, by rfl⟩ : syracuseStep 719631 = 1079447) B1079447
theorem B3898145 : Blo 718322 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B1080107 : Blo 718322 1080107 := bstep (se 1 (by rfl) ⟨810080, by rfl⟩ : syracuseStep 1080107 = 1620161) B1620161
theorem B719675 : Blo 718322 719675 := bstep (se 1 (by rfl) ⟨539756, by rfl⟩ : syracuseStep 719675 = 1079513) B1079513
theorem B1080137 : Blo 718322 1080137 := bstep (se 2 (by rfl) ⟨405051, by rfl⟩ : syracuseStep 1080137 = 810103) B810103
theorem B13171571 : Blo 718322 13171571 := bstep (se 1 (by rfl) ⟨9878678, by rfl⟩ : syracuseStep 13171571 = 19757357) B19757357
theorem B719751 : Blo 718322 719751 := bstep (se 1 (by rfl) ⟨539813, by rfl⟩ : syracuseStep 719751 = 1079627) B1079627
theorem B719759 : Blo 718322 719759 := bstep (se 1 (by rfl) ⟨539819, by rfl⟩ : syracuseStep 719759 = 1079639) B1079639
theorem B719803 : Blo 718322 719803 := bstep (se 1 (by rfl) ⟨539852, by rfl⟩ : syracuseStep 719803 = 1079705) B1079705
theorem B1080251 : Blo 718322 1080251 := bstep (se 1 (by rfl) ⟨810188, by rfl⟩ : syracuseStep 1080251 = 1620377) B1620377
theorem B1080311 : Blo 718322 1080311 := bstep (se 1 (by rfl) ⟨810233, by rfl⟩ : syracuseStep 1080311 = 1620467) B1620467
theorem B719879 : Blo 718322 719879 := bstep (se 1 (by rfl) ⟨539909, by rfl⟩ : syracuseStep 719879 = 1079819) B1079819
theorem B1604623 : Blo 718322 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B719887 : Blo 718322 719887 := bstep (se 1 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 719887 = 1079831) B1079831
theorem B1080335 : Blo 718322 1080335 := bstep (se 1 (by rfl) ⟨810251, by rfl⟩ : syracuseStep 1080335 = 1620503) B1620503
theorem B1080377 : Blo 718322 1080377 := bstep (se 2 (by rfl) ⟨405141, by rfl⟩ : syracuseStep 1080377 = 810283) B810283
theorem B719931 : Blo 718322 719931 := bstep (se 1 (by rfl) ⟨539948, by rfl⟩ : syracuseStep 719931 = 1079897) B1079897
theorem B720007 : Blo 718322 720007 := bstep (se 1 (by rfl) ⟨540005, by rfl⟩ : syracuseStep 720007 = 1080011) B1080011
theorem B1080455 : Blo 718322 1080455 := bstep (se 1 (by rfl) ⟨810341, by rfl⟩ : syracuseStep 1080455 = 1620683) B1620683
theorem B720015 : Blo 718322 720015 := bstep (se 1 (by rfl) ⟨540011, by rfl⟩ : syracuseStep 720015 = 1080023) B1080023
theorem B1080491 : Blo 718322 1080491 := bstep (se 1 (by rfl) ⟨810368, by rfl⟩ : syracuseStep 1080491 = 1620737) B1620737
theorem B720059 : Blo 718322 720059 := bstep (se 1 (by rfl) ⟨540044, by rfl⟩ : syracuseStep 720059 = 1080089) B1080089
theorem B1080521 : Blo 718322 1080521 := bstep (se 2 (by rfl) ⟨405195, by rfl⟩ : syracuseStep 1080521 = 810391) B810391
theorem B720135 : Blo 718322 720135 := bstep (se 1 (by rfl) ⟨540101, by rfl⟩ : syracuseStep 720135 = 1080203) B1080203
theorem B720143 : Blo 718322 720143 := bstep (se 1 (by rfl) ⟨540107, by rfl⟩ : syracuseStep 720143 = 1080215) B1080215
theorem B720187 : Blo 718322 720187 := bstep (se 1 (by rfl) ⟨540140, by rfl⟩ : syracuseStep 720187 = 1080281) B1080281
theorem B1080635 : Blo 718322 1080635 := bstep (se 1 (by rfl) ⟨810476, by rfl⟩ : syracuseStep 1080635 = 1620953) B1620953
theorem B1080695 : Blo 718322 1080695 := bstep (se 1 (by rfl) ⟨810521, by rfl⟩ : syracuseStep 1080695 = 1621043) B1621043
theorem B9239939 : Blo 718322 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B720263 : Blo 718322 720263 := bstep (se 1 (by rfl) ⟨540197, by rfl⟩ : syracuseStep 720263 = 1080395) B1080395
theorem B720271 : Blo 718322 720271 := bstep (se 1 (by rfl) ⟨540203, by rfl⟩ : syracuseStep 720271 = 1080407) B1080407
theorem B1080719 : Blo 718322 1080719 := bstep (se 1 (by rfl) ⟨810539, by rfl⟩ : syracuseStep 1080719 = 1621079) B1621079
theorem B1080761 : Blo 718322 1080761 := bstep (se 2 (by rfl) ⟨405285, by rfl⟩ : syracuseStep 1080761 = 810571) B810571
theorem B720315 : Blo 718322 720315 := bstep (se 1 (by rfl) ⟨540236, by rfl⟩ : syracuseStep 720315 = 1080473) B1080473
theorem B720391 : Blo 718322 720391 := bstep (se 1 (by rfl) ⟨540293, by rfl⟩ : syracuseStep 720391 = 1080587) B1080587
theorem B1080839 : Blo 718322 1080839 := bstep (se 1 (by rfl) ⟨810629, by rfl⟩ : syracuseStep 1080839 = 1621259) B1621259
theorem B3079691 : Blo 718322 3079691 := bstep (se 1 (by rfl) ⟨2309768, by rfl⟩ : syracuseStep 3079691 = 4619537) B4619537
theorem B720399 : Blo 718322 720399 := bstep (se 1 (by rfl) ⟨540299, by rfl⟩ : syracuseStep 720399 = 1080599) B1080599
theorem B1080875 : Blo 718322 1080875 := bstep (se 1 (by rfl) ⟨810656, by rfl⟩ : syracuseStep 1080875 = 1621313) B1621313
theorem B720443 : Blo 718322 720443 := bstep (se 1 (by rfl) ⟨540332, by rfl⟩ : syracuseStep 720443 = 1080665) B1080665
theorem B3079741 : Blo 718322 3079741 := bstep (se 3 (by rfl) ⟨577451, by rfl⟩ : syracuseStep 3079741 = 1154903) B1154903
theorem B1080905 : Blo 718322 1080905 := bstep (se 2 (by rfl) ⟨405339, by rfl⟩ : syracuseStep 1080905 = 810679) B810679
theorem B720519 : Blo 718322 720519 := bstep (se 1 (by rfl) ⟨540389, by rfl⟩ : syracuseStep 720519 = 1080779) B1080779
theorem B720527 : Blo 718322 720527 := bstep (se 1 (by rfl) ⟨540395, by rfl⟩ : syracuseStep 720527 = 1080791) B1080791
theorem B720571 : Blo 718322 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B1081019 : Blo 718322 1081019 := bstep (se 1 (by rfl) ⟨810764, by rfl⟩ : syracuseStep 1081019 = 1621529) B1621529
theorem B1539785 : Blo 718322 1539785 := bstep (se 2 (by rfl) ⟨577419, by rfl⟩ : syracuseStep 1539785 = 1154839) B1154839
theorem B1081079 : Blo 718322 1081079 := bstep (se 1 (by rfl) ⟨810809, by rfl⟩ : syracuseStep 1081079 = 1621619) B1621619
theorem B720647 : Blo 718322 720647 := bstep (se 1 (by rfl) ⟨540485, by rfl⟩ : syracuseStep 720647 = 1080971) B1080971
theorem B720655 : Blo 718322 720655 := bstep (se 1 (by rfl) ⟨540491, by rfl⟩ : syracuseStep 720655 = 1080983) B1080983
theorem B1081103 : Blo 718322 1081103 := bstep (se 1 (by rfl) ⟨810827, by rfl⟩ : syracuseStep 1081103 = 1621655) B1621655
theorem B1081145 : Blo 718322 1081145 := bstep (se 2 (by rfl) ⟨405429, by rfl⟩ : syracuseStep 1081145 = 810859) B810859
theorem B720699 : Blo 718322 720699 := bstep (se 1 (by rfl) ⟨540524, by rfl⟩ : syracuseStep 720699 = 1081049) B1081049
theorem B720775 : Blo 718322 720775 := bstep (se 1 (by rfl) ⟨540581, by rfl⟩ : syracuseStep 720775 = 1081163) B1081163
theorem B1081223 : Blo 718322 1081223 := bstep (se 1 (by rfl) ⟨810917, by rfl⟩ : syracuseStep 1081223 = 1621835) B1621835
theorem B720783 : Blo 718322 720783 := bstep (se 1 (by rfl) ⟨540587, by rfl⟩ : syracuseStep 720783 = 1081175) B1081175
theorem B1081259 : Blo 718322 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B2424761 : Blo 718322 2424761 := bstep (se 2 (by rfl) ⟨909285, by rfl⟩ : syracuseStep 2424761 = 1818571) B1818571
theorem B720827 : Blo 718322 720827 := bstep (se 1 (by rfl) ⟨540620, by rfl⟩ : syracuseStep 720827 = 1081241) B1081241
theorem B1081289 : Blo 718322 1081289 := bstep (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) B810967
theorem B1212455 : Blo 718322 1212455 := bstep (se 1 (by rfl) ⟨909341, by rfl⟩ : syracuseStep 1212455 = 1818683) B1818683
theorem B720935 : Blo 718322 720935 := bstep (se 1 (by rfl) ⟨540701, by rfl⟩ : syracuseStep 720935 = 1081403) B1081403
theorem B720975 : Blo 718322 720975 := bstep (se 1 (by rfl) ⟨540731, by rfl⟩ : syracuseStep 720975 = 1081463) B1081463
theorem B720991 : Blo 718322 720991 := bstep (se 1 (by rfl) ⟨540743, by rfl⟩ : syracuseStep 720991 = 1081487) B1081487
theorem B4096115 : Blo 718322 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B721019 : Blo 718322 721019 := bstep (se 1 (by rfl) ⟨540764, by rfl⟩ : syracuseStep 721019 = 1081529) B1081529
theorem B721071 : Blo 718322 721071 := bstep (se 1 (by rfl) ⟨540803, by rfl⟩ : syracuseStep 721071 = 1081607) B1081607
theorem B721095 : Blo 718322 721095 := bstep (se 1 (by rfl) ⟨540821, by rfl⟩ : syracuseStep 721095 = 1081643) B1081643
theorem B721115 : Blo 718322 721115 := bstep (se 1 (by rfl) ⟨540836, by rfl⟩ : syracuseStep 721115 = 1081673) B1081673
theorem B721191 : Blo 718322 721191 := bstep (se 1 (by rfl) ⟨540893, by rfl⟩ : syracuseStep 721191 = 1081787) B1081787
theorem B1212745 : Blo 718322 1212745 := bstep (se 2 (by rfl) ⟨454779, by rfl⟩ : syracuseStep 1212745 = 909559) B909559
theorem B721231 : Blo 718322 721231 := bstep (se 1 (by rfl) ⟨540923, by rfl⟩ : syracuseStep 721231 = 1081847) B1081847
theorem B721247 : Blo 718322 721247 := bstep (se 1 (by rfl) ⟨540935, by rfl⟩ : syracuseStep 721247 = 1081871) B1081871
theorem B2425193 : Blo 718322 2425193 := bstep (se 2 (by rfl) ⟨909447, by rfl⟩ : syracuseStep 2425193 = 1818895) B1818895
theorem B1212779 : Blo 718322 1212779 := bstep (se 1 (by rfl) ⟨909584, by rfl⟩ : syracuseStep 1212779 = 1819169) B1819169
theorem B721275 : Blo 718322 721275 := bstep (se 1 (by rfl) ⟨540956, by rfl⟩ : syracuseStep 721275 = 1081913) B1081913
theorem B1081775 : Blo 718322 1081775 := bstep (se 1 (by rfl) ⟨811331, by rfl⟩ : syracuseStep 1081775 = 1622663) B1622663
theorem B721327 : Blo 718322 721327 := bstep (se 1 (by rfl) ⟨540995, by rfl⟩ : syracuseStep 721327 = 1081991) B1081991
theorem B721351 : Blo 718322 721351 := bstep (se 1 (by rfl) ⟨541013, by rfl⟩ : syracuseStep 721351 = 1082027) B1082027
theorem B721371 : Blo 718322 721371 := bstep (se 1 (by rfl) ⟨541028, by rfl⟩ : syracuseStep 721371 = 1082057) B1082057
theorem B1081865 : Blo 718322 1081865 := bstep (se 2 (by rfl) ⟨405699, by rfl⟩ : syracuseStep 1081865 = 811399) B811399
theorem B3277345 : Blo 718322 3277345 := bstep (se 2 (by rfl) ⟨1229004, by rfl⟩ : syracuseStep 3277345 = 2458009) B2458009
theorem B1081895 : Blo 718322 1081895 := bstep (se 1 (by rfl) ⟨811421, by rfl⟩ : syracuseStep 1081895 = 1622843) B1622843
theorem B721447 : Blo 718322 721447 := bstep (se 1 (by rfl) ⟨541085, by rfl⟩ : syracuseStep 721447 = 1082171) B1082171
theorem B721487 : Blo 718322 721487 := bstep (se 1 (by rfl) ⟨541115, by rfl⟩ : syracuseStep 721487 = 1082231) B1082231
theorem B721503 : Blo 718322 721503 := bstep (se 1 (by rfl) ⟨541127, by rfl⟩ : syracuseStep 721503 = 1082255) B1082255
theorem B1081979 : Blo 718322 1081979 := bstep (se 1 (by rfl) ⟨811484, by rfl⟩ : syracuseStep 1081979 = 1622969) B1622969
theorem B721531 : Blo 718322 721531 := bstep (se 1 (by rfl) ⟨541148, by rfl⟩ : syracuseStep 721531 = 1082297) B1082297
theorem B721583 : Blo 718322 721583 := bstep (se 1 (by rfl) ⟨541187, by rfl⟩ : syracuseStep 721583 = 1082375) B1082375
theorem B721607 : Blo 718322 721607 := bstep (se 1 (by rfl) ⟨541205, by rfl⟩ : syracuseStep 721607 = 1082411) B1082411
theorem B721627 : Blo 718322 721627 := bstep (se 1 (by rfl) ⟨541220, by rfl⟩ : syracuseStep 721627 = 1082441) B1082441
theorem B1213177 : Blo 718322 1213177 := bstep (se 2 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 1213177 = 909883) B909883
theorem B1082105 : Blo 718322 1082105 := bstep (se 2 (by rfl) ⟨405789, by rfl⟩ : syracuseStep 1082105 = 811579) B811579
theorem B721703 : Blo 718322 721703 := bstep (se 1 (by rfl) ⟨541277, by rfl⟩ : syracuseStep 721703 = 1082555) B1082555
theorem B721743 : Blo 718322 721743 := bstep (se 1 (by rfl) ⟨541307, by rfl⟩ : syracuseStep 721743 = 1082615) B1082615
theorem B1082207 : Blo 718322 1082207 := bstep (se 1 (by rfl) ⟨811655, by rfl⟩ : syracuseStep 1082207 = 1623311) B1623311
theorem B721759 : Blo 718322 721759 := bstep (se 1 (by rfl) ⟨541319, by rfl⟩ : syracuseStep 721759 = 1082639) B1082639
theorem B3277675 : Blo 718322 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B1082219 : Blo 718322 1082219 := bstep (se 1 (by rfl) ⟨811664, by rfl⟩ : syracuseStep 1082219 = 1623329) B1623329
theorem B721787 : Blo 718322 721787 := bstep (se 1 (by rfl) ⟨541340, by rfl⟩ : syracuseStep 721787 = 1082681) B1082681
theorem B9208727 : Blo 718322 9208727 := bstep (se 1 (by rfl) ⟨6906545, by rfl⟩ : syracuseStep 9208727 = 13813091) B13813091
theorem B721839 : Blo 718322 721839 := bstep (se 1 (by rfl) ⟨541379, by rfl⟩ : syracuseStep 721839 = 1082759) B1082759
theorem B2589623 : Blo 718322 2589623 := bstep (se 1 (by rfl) ⟨1942217, by rfl⟩ : syracuseStep 2589623 = 3884435) B3884435
theorem B2425787 : Blo 718322 2425787 := bstep (se 1 (by rfl) ⟨1819340, by rfl⟩ : syracuseStep 2425787 = 3638681) B3638681
theorem B721863 : Blo 718322 721863 := bstep (se 1 (by rfl) ⟨541397, by rfl⟩ : syracuseStep 721863 = 1082795) B1082795
theorem B721883 : Blo 718322 721883 := bstep (se 1 (by rfl) ⟨541412, by rfl⟩ : syracuseStep 721883 = 1082825) B1082825
theorem B1213447 : Blo 718322 1213447 := bstep (se 1 (by rfl) ⟨910085, by rfl⟩ : syracuseStep 1213447 = 1820171) B1820171
theorem B721959 : Blo 718322 721959 := bstep (se 1 (by rfl) ⟨541469, by rfl⟩ : syracuseStep 721959 = 1082939) B1082939
theorem B5473331 : Blo 718322 5473331 := bstep (se 1 (by rfl) ⟨4104998, by rfl⟩ : syracuseStep 5473331 = 8209997) B8209997
theorem B1082447 : Blo 718322 1082447 := bstep (se 1 (by rfl) ⟨811835, by rfl⟩ : syracuseStep 1082447 = 1623671) B1623671
theorem B721999 : Blo 718322 721999 := bstep (se 1 (by rfl) ⟨541499, by rfl⟩ : syracuseStep 721999 = 1082999) B1082999
theorem B722015 : Blo 718322 722015 := bstep (se 1 (by rfl) ⟨541511, by rfl⟩ : syracuseStep 722015 = 1083023) B1083023
theorem B722043 : Blo 718322 722043 := bstep (se 1 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 722043 = 1083065) B1083065
theorem B722095 : Blo 718322 722095 := bstep (se 1 (by rfl) ⟨541571, by rfl⟩ : syracuseStep 722095 = 1083143) B1083143
theorem B1082567 : Blo 718322 1082567 := bstep (se 1 (by rfl) ⟨811925, by rfl⟩ : syracuseStep 1082567 = 1623851) B1623851
theorem B722119 : Blo 718322 722119 := bstep (se 1 (by rfl) ⟨541589, by rfl⟩ : syracuseStep 722119 = 1083179) B1083179
theorem B722139 : Blo 718322 722139 := bstep (se 1 (by rfl) ⟨541604, by rfl⟩ : syracuseStep 722139 = 1083209) B1083209
theorem B3638519 : Blo 718322 3638519 := bstep (se 1 (by rfl) ⟨2728889, by rfl⟩ : syracuseStep 3638519 = 5457779) B5457779
theorem B722215 : Blo 718322 722215 := bstep (se 1 (by rfl) ⟨541661, by rfl⟩ : syracuseStep 722215 = 1083323) B1083323
theorem B722255 : Blo 718322 722255 := bstep (se 1 (by rfl) ⟨541691, by rfl⟩ : syracuseStep 722255 = 1083383) B1083383
theorem B722271 : Blo 718322 722271 := bstep (se 1 (by rfl) ⟨541703, by rfl⟩ : syracuseStep 722271 = 1083407) B1083407
theorem B1082729 : Blo 718322 1082729 := bstep (se 2 (by rfl) ⟨406023, by rfl⟩ : syracuseStep 1082729 = 812047) B812047
theorem B722299 : Blo 718322 722299 := bstep (se 1 (by rfl) ⟨541724, by rfl⟩ : syracuseStep 722299 = 1083449) B1083449
theorem B14058917 : Blo 718322 14058917 := bstep (se 4 (by rfl) ⟨1318023, by rfl⟩ : syracuseStep 14058917 = 2636047) B2636047
theorem B1213879 : Blo 718322 1213879 := bstep (se 1 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 1213879 = 1820819) B1820819
theorem B1082807 : Blo 718322 1082807 := bstep (se 1 (by rfl) ⟨812105, by rfl⟩ : syracuseStep 1082807 = 1624211) B1624211
theorem B1082843 : Blo 718322 1082843 := bstep (se 1 (by rfl) ⟨812132, by rfl⟩ : syracuseStep 1082843 = 1624265) B1624265
theorem B1214075 : Blo 718322 1214075 := bstep (se 1 (by rfl) ⟨910556, by rfl⟩ : syracuseStep 1214075 = 1821113) B1821113
theorem B14419603 : Blo 718322 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B3639005 : Blo 718322 3639005 := bstep (se 3 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 3639005 = 1364627) B1364627
theorem B4622123 : Blo 718322 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B10389343 : Blo 718322 10389343 := bstep (se 1 (by rfl) ⟨7792007, by rfl⟩ : syracuseStep 10389343 = 15584015) B15584015
theorem B1640353 : Blo 718322 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B1083311 : Blo 718322 1083311 := bstep (se 1 (by rfl) ⟨812483, by rfl⟩ : syracuseStep 1083311 = 1624967) B1624967
theorem B1214473 : Blo 718322 1214473 := bstep (se 2 (by rfl) ⟨455427, by rfl⟩ : syracuseStep 1214473 = 910855) B910855
theorem B1083401 : Blo 718322 1083401 := bstep (se 2 (by rfl) ⟨406275, by rfl⟩ : syracuseStep 1083401 = 812551) B812551
theorem B1083431 : Blo 718322 1083431 := bstep (se 1 (by rfl) ⟨812573, by rfl⟩ : syracuseStep 1083431 = 1625147) B1625147
theorem B1214635 : Blo 718322 1214635 := bstep (se 1 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 1214635 = 1821953) B1821953
theorem B1214939 : Blo 718322 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B2427515 : Blo 718322 2427515 := bstep (se 1 (by rfl) ⟨1820636, by rfl⟩ : syracuseStep 2427515 = 3641273) B3641273
theorem B1215175 : Blo 718322 1215175 := bstep (se 1 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 1215175 = 1822763) B1822763
theorem B5835473 : Blo 718322 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B2427677 : Blo 718322 2427677 := bstep (se 3 (by rfl) ⟨455189, by rfl⟩ : syracuseStep 2427677 = 910379) B910379
theorem B2919197 : Blo 718322 2919197 := bstep (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) B1094699
theorem B1215337 : Blo 718322 1215337 := bstep (se 2 (by rfl) ⟨455751, by rfl⟩ : syracuseStep 1215337 = 911503) B911503
theorem B2591801 : Blo 718322 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B8195417 : Blo 718322 8195417 := bstep (se 2 (by rfl) ⟨3073281, by rfl⟩ : syracuseStep 8195417 = 6146563) B6146563
theorem B1215931 : Blo 718322 1215931 := bstep (se 1 (by rfl) ⟨911948, by rfl⟩ : syracuseStep 1215931 = 1823897) B1823897
theorem B2428379 : Blo 718322 2428379 := bstep (se 1 (by rfl) ⟨1821284, by rfl⟩ : syracuseStep 2428379 = 3642569) B3642569
theorem B1216039 : Blo 718322 1216039 := bstep (se 1 (by rfl) ⟨912029, by rfl⟩ : syracuseStep 1216039 = 1824059) B1824059
theorem B4099805 : Blo 718322 4099805 := bstep (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) B1537427
theorem B11702083 : Blo 718322 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B1216363 : Blo 718322 1216363 := bstep (se 1 (by rfl) ⟨912272, by rfl⟩ : syracuseStep 1216363 = 1824545) B1824545
theorem B2429081 : Blo 718322 2429081 := bstep (se 2 (by rfl) ⟨910905, by rfl⟩ : syracuseStep 2429081 = 1821811) B1821811
theorem B6165017 : Blo 718322 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B2593313 : Blo 718322 2593313 := bstep (se 2 (by rfl) ⟨972492, by rfl⟩ : syracuseStep 2593313 = 1944985) B1944985
theorem B3740489 : Blo 718322 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B8753993 : Blo 718322 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B1217423 : Blo 718322 1217423 := bstep (se 1 (by rfl) ⟨913067, by rfl⟩ : syracuseStep 1217423 = 1826135) B1826135
theorem B1643527 : Blo 718322 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B9868337 : Blo 718322 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B1217659 : Blo 718322 1217659 := bstep (se 1 (by rfl) ⟨913244, by rfl⟩ : syracuseStep 1217659 = 1826489) B1826489
theorem B4625687 : Blo 718322 4625687 := bstep (se 1 (by rfl) ⟨3469265, by rfl⟩ : syracuseStep 4625687 = 6938531) B6938531
theorem B2430269 : Blo 718322 2430269 := bstep (se 3 (by rfl) ⟨455675, by rfl⟩ : syracuseStep 2430269 = 911351) B911351
theorem B1152443 : Blo 718322 1152443 := bstep (se 1 (by rfl) ⟨864332, by rfl⟩ : syracuseStep 1152443 = 1728665) B1728665
theorem B1218523 : Blo 718322 1218523 := bstep (se 1 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 1218523 = 1827785) B1827785
theorem B3119219 : Blo 718322 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B2431133 : Blo 718322 2431133 := bstep (se 3 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 2431133 = 911675) B911675
theorem B1186039 : Blo 718322 1186039 := bstep (se 1 (by rfl) ⟨889529, by rfl⟩ : syracuseStep 1186039 = 1779059) B1779059
theorem B9836849 : Blo 718322 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B11082221 : Blo 718322 11082221 := bstep (se 3 (by rfl) ⟨2077916, by rfl⟩ : syracuseStep 11082221 = 4155833) B4155833
theorem B2431673 : Blo 718322 2431673 := bstep (se 2 (by rfl) ⟨911877, by rfl⟩ : syracuseStep 2431673 = 1823755) B1823755
theorem B4627145 : Blo 718322 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B3644189 : Blo 718322 3644189 := bstep (se 3 (by rfl) ⟨683285, by rfl⟩ : syracuseStep 3644189 = 1366571) B1366571
theorem B1153865 : Blo 718322 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B2432267 : Blo 718322 2432267 := bstep (se 1 (by rfl) ⟨1824200, by rfl⟩ : syracuseStep 2432267 = 3648401) B3648401
theorem B2923901 : Blo 718322 2923901 := bstep (se 3 (by rfl) ⟨548231, by rfl⟩ : syracuseStep 2923901 = 1096463) B1096463
theorem B10395053 : Blo 718322 10395053 := bstep (se 3 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 10395053 = 3898145) B3898145
theorem B2432537 : Blo 718322 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B18488897 : Blo 718322 18488897 := bstep (se 2 (by rfl) ⟨6933336, by rfl⟩ : syracuseStep 18488897 = 13866673) B13866673
theorem B1154731 : Blo 718322 1154731 := bstep (se 1 (by rfl) ⟨866048, by rfl⟩ : syracuseStep 1154731 = 1732097) B1732097
theorem B5480135 : Blo 718322 5480135 := bstep (se 1 (by rfl) ⟨4110101, by rfl⟩ : syracuseStep 5480135 = 8220203) B8220203
theorem B2335063 : Blo 718322 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B2302451 : Blo 718322 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B2433671 : Blo 718322 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B2630333 : Blo 718322 2630333 := bstep (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) B986375
theorem B2433725 : Blo 718322 2433725 := bstep (se 3 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 2433725 = 912647) B912647
theorem B2728799 : Blo 718322 2728799 := bstep (se 1 (by rfl) ⟨2046599, by rfl⟩ : syracuseStep 2728799 = 4093199) B4093199
theorem B2433887 : Blo 718322 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B2335675 : Blo 718322 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B2434049 : Blo 718322 2434049 := bstep (se 2 (by rfl) ⟨912768, by rfl⟩ : syracuseStep 2434049 = 1825537) B1825537
theorem B2139497 : Blo 718322 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B4105637 : Blo 718322 4105637 := bstep (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) B769807
theorem B6661577 : Blo 718322 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B2729497 : Blo 718322 2729497 := bstep (se 2 (by rfl) ⟨1023561, by rfl⟩ : syracuseStep 2729497 = 2047123) B2047123
theorem B2729771 : Blo 718322 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B2434859 : Blo 718322 2434859 := bstep (se 1 (by rfl) ⟨1826144, by rfl⟩ : syracuseStep 2434859 = 3652289) B3652289
theorem B2729801 : Blo 718322 2729801 := bstep (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) B2047351
theorem B2435129 : Blo 718322 2435129 := bstep (se 2 (by rfl) ⟨913173, by rfl⟩ : syracuseStep 2435129 = 1826347) B1826347
theorem B4106321 : Blo 718322 4106321 := bstep (se 2 (by rfl) ⟨1539870, by rfl⟩ : syracuseStep 4106321 = 3079741) B3079741
theorem B2435453 : Blo 718322 2435453 := bstep (se 3 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 2435453 = 913295) B913295
theorem B1026523 : Blo 718322 1026523 := bstep (se 1 (by rfl) ⟨769892, by rfl⟩ : syracuseStep 1026523 = 1539785) B1539785
theorem B1616507 : Blo 718322 1616507 := bstep (se 1 (by rfl) ⟨1212380, by rfl⟩ : syracuseStep 1616507 = 2424761) B2424761
theorem B2435723 : Blo 718322 2435723 := bstep (se 1 (by rfl) ⟨1826792, by rfl⟩ : syracuseStep 2435723 = 3653585) B3653585
theorem B1616633 : Blo 718322 1616633 := bstep (se 2 (by rfl) ⟨606237, by rfl⟩ : syracuseStep 1616633 = 1212475) B1212475
theorem B1616903 : Blo 718322 1616903 := bstep (se 1 (by rfl) ⟨1212677, by rfl⟩ : syracuseStep 1616903 = 2425355) B2425355
theorem B3648563 : Blo 718322 3648563 := bstep (se 1 (by rfl) ⟨2736422, by rfl⟩ : syracuseStep 3648563 = 5472845) B5472845
theorem B1616975 : Blo 718322 1616975 := bstep (se 1 (by rfl) ⟨1212731, by rfl⟩ : syracuseStep 1616975 = 2425463) B2425463
theorem B9874511 : Blo 718322 9874511 := bstep (se 1 (by rfl) ⟨7405883, by rfl⟩ : syracuseStep 9874511 = 14811767) B14811767
theorem B1617371 : Blo 718322 1617371 := bstep (se 1 (by rfl) ⟨1213028, by rfl⟩ : syracuseStep 1617371 = 2426057) B2426057
theorem B2436641 : Blo 718322 2436641 := bstep (se 2 (by rfl) ⟨913740, by rfl⟩ : syracuseStep 2436641 = 1827481) B1827481
theorem B1388111 : Blo 718322 1388111 := bstep (se 1 (by rfl) ⟨1041083, by rfl⟩ : syracuseStep 1388111 = 2082167) B2082167
theorem B2436857 : Blo 718322 2436857 := bstep (se 2 (by rfl) ⟨913821, by rfl⟩ : syracuseStep 2436857 = 1827643) B1827643
theorem B1093483 : Blo 718322 1093483 := bstep (se 1 (by rfl) ⟨820112, by rfl⟩ : syracuseStep 1093483 = 1640225) B1640225
theorem B1617839 : Blo 718322 1617839 := bstep (se 1 (by rfl) ⟨1213379, by rfl⟩ : syracuseStep 1617839 = 2426759) B2426759
theorem B2437127 : Blo 718322 2437127 := bstep (se 1 (by rfl) ⟨1827845, by rfl⟩ : syracuseStep 2437127 = 3655691) B3655691
theorem B4927517 : Blo 718322 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B2437235 : Blo 718322 2437235 := bstep (se 1 (by rfl) ⟨1827926, by rfl⟩ : syracuseStep 2437235 = 3655853) B3655853
theorem B1618091 : Blo 718322 1618091 := bstep (se 1 (by rfl) ⟨1213568, by rfl⟩ : syracuseStep 1618091 = 2427137) B2427137
theorem B2732413 : Blo 718322 2732413 := bstep (se 3 (by rfl) ⟨512327, by rfl⟩ : syracuseStep 2732413 = 1024655) B1024655
theorem B2437505 : Blo 718322 2437505 := bstep (se 2 (by rfl) ⟨914064, by rfl⟩ : syracuseStep 2437505 = 1828129) B1828129
theorem B3650183 : Blo 718322 3650183 := bstep (se 1 (by rfl) ⟨2737637, by rfl⟩ : syracuseStep 3650183 = 5475275) B5475275
theorem B5190317 : Blo 718322 5190317 := bstep (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) B1946369
theorem B1618631 : Blo 718322 1618631 := bstep (se 1 (by rfl) ⟨1213973, by rfl⟩ : syracuseStep 1618631 = 2427947) B2427947
theorem B7877681 : Blo 718322 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B5551183 : Blo 718322 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B160281827 : Blo 718322 160281827 := bstep (se 1 (by rfl) ⟨120211370, by rfl⟩ : syracuseStep 160281827 = 240422741) B240422741
theorem B4797991 : Blo 718322 4797991 := bstep (se 1 (by rfl) ⟨3598493, by rfl⟩ : syracuseStep 4797991 = 7196987) B7196987
theorem B1619495 : Blo 718322 1619495 := bstep (se 1 (by rfl) ⟨1214621, by rfl⟩ : syracuseStep 1619495 = 2429243) B2429243
theorem B2602685 : Blo 718322 2602685 := bstep (se 3 (by rfl) ⟨488003, by rfl⟩ : syracuseStep 2602685 = 976007) B976007
theorem B20821697 : Blo 718322 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B2307935 : Blo 718322 2307935 := bstep (se 1 (by rfl) ⟨1730951, by rfl⟩ : syracuseStep 2307935 = 3461903) B3461903
theorem B1619819 : Blo 718322 1619819 := bstep (se 1 (by rfl) ⟨1214864, by rfl⟩ : syracuseStep 1619819 = 2429729) B2429729
theorem B1619873 : Blo 718322 1619873 := bstep (se 2 (by rfl) ⟨607452, by rfl⟩ : syracuseStep 1619873 = 1214905) B1214905
theorem B3651641 : Blo 718322 3651641 := bstep (se 2 (by rfl) ⟨1369365, by rfl⟩ : syracuseStep 3651641 = 2738731) B2738731
theorem B1620215 : Blo 718322 1620215 := bstep (se 1 (by rfl) ⟨1215161, by rfl⟩ : syracuseStep 1620215 = 2430323) B2430323
theorem B2734631 : Blo 718322 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B1456697 : Blo 718322 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B4373203 : Blo 718322 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B1620809 : Blo 718322 1620809 := bstep (se 2 (by rfl) ⟨607803, by rfl⟩ : syracuseStep 1620809 = 1215607) B1215607
theorem B998363 : Blo 718322 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B15580633 : Blo 718322 15580633 := bstep (se 2 (by rfl) ⟨5842737, by rfl⟩ : syracuseStep 15580633 = 11685475) B11685475
theorem B2735603 : Blo 718322 2735603 := bstep (se 1 (by rfl) ⟨2051702, by rfl⟩ : syracuseStep 2735603 = 4103405) B4103405
theorem B1621601 : Blo 718322 1621601 := bstep (se 2 (by rfl) ⟨608100, by rfl⟩ : syracuseStep 1621601 = 1216201) B1216201
theorem B2735801 : Blo 718322 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B2735815 : Blo 718322 2735815 := bstep (se 1 (by rfl) ⟨2051861, by rfl⟩ : syracuseStep 2735815 = 4103723) B4103723
theorem B9879329 : Blo 718322 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B1621943 : Blo 718322 1621943 := bstep (se 1 (by rfl) ⟨1216457, by rfl⟩ : syracuseStep 1621943 = 2432915) B2432915
theorem B1818551 : Blo 718322 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B3653747 : Blo 718322 3653747 := bstep (se 1 (by rfl) ⟨2740310, by rfl⟩ : syracuseStep 3653747 = 5480621) B5480621
theorem B2081015 : Blo 718322 2081015 := bstep (se 1 (by rfl) ⟨1560761, by rfl⟩ : syracuseStep 2081015 = 3121523) B3121523
theorem B3457367 : Blo 718322 3457367 := bstep (se 1 (by rfl) ⟨2593025, by rfl⟩ : syracuseStep 3457367 = 5186051) B5186051
theorem B2048399 : Blo 718322 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B1622537 : Blo 718322 1622537 := bstep (se 2 (by rfl) ⟨608451, by rfl⟩ : syracuseStep 1622537 = 1216903) B1216903
theorem B2736787 : Blo 718322 2736787 := bstep (se 1 (by rfl) ⟨2052590, by rfl⟩ : syracuseStep 2736787 = 4105181) B4105181
theorem B5554889 : Blo 718322 5554889 := bstep (se 2 (by rfl) ⟨2083083, by rfl⟩ : syracuseStep 5554889 = 4166167) B4166167
theorem B1622879 : Blo 718322 1622879 := bstep (se 1 (by rfl) ⟨1217159, by rfl⟩ : syracuseStep 1622879 = 2434319) B2434319
theorem B1819655 : Blo 718322 1819655 := bstep (se 1 (by rfl) ⟨1364741, by rfl⟩ : syracuseStep 1819655 = 2729483) B2729483
theorem B1623059 : Blo 718322 1623059 := bstep (se 1 (by rfl) ⟨1217294, by rfl⟩ : syracuseStep 1623059 = 2434589) B2434589
theorem B1819705 : Blo 718322 1819705 := bstep (se 2 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 1819705 = 1364779) B1364779
theorem B4113611 : Blo 718322 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B1820009 : Blo 718322 1820009 := bstep (se 2 (by rfl) ⟨682503, by rfl⟩ : syracuseStep 1820009 = 1365007) B1365007
theorem B1623401 : Blo 718322 1623401 := bstep (se 2 (by rfl) ⟨608775, by rfl⟩ : syracuseStep 1623401 = 1217551) B1217551
theorem B2311625 : Blo 718322 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B3655367 : Blo 718322 3655367 := bstep (se 1 (by rfl) ⟨2741525, by rfl⟩ : syracuseStep 3655367 = 5483051) B5483051
theorem B8308439 : Blo 718322 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B2770807 : Blo 718322 2770807 := bstep (se 1 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 2770807 = 4156211) B4156211
theorem B1623995 : Blo 718322 1623995 := bstep (se 1 (by rfl) ⟨1217996, by rfl⟩ : syracuseStep 1623995 = 2435993) B2435993
theorem B1624121 : Blo 718322 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B4933975 : Blo 718322 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B2738519 : Blo 718322 2738519 := bstep (se 1 (by rfl) ⟨2053889, by rfl⟩ : syracuseStep 2738519 = 4107779) B4107779
theorem B1624463 : Blo 718322 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B2214611 : Blo 718322 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B1624787 : Blo 718322 1624787 := bstep (se 1 (by rfl) ⟨1218590, by rfl⟩ : syracuseStep 1624787 = 2437181) B2437181
theorem B3328943 : Blo 718322 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B1952695 : Blo 718322 1952695 := bstep (se 1 (by rfl) ⟨1464521, by rfl⟩ : syracuseStep 1952695 = 2929043) B2929043
theorem B3460097 : Blo 718322 3460097 := bstep (se 2 (by rfl) ⟨1297536, by rfl⟩ : syracuseStep 3460097 = 2595073) B2595073
theorem B21023939 : Blo 718322 21023939 := bstep (se 1 (by rfl) ⟨15767954, by rfl⟩ : syracuseStep 21023939 = 31535909) B31535909
theorem B5459237 : Blo 718322 5459237 := bstep (se 4 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 5459237 = 1023607) B1023607
theorem B1461611 : Blo 718322 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B10374581 : Blo 718322 10374581 := bstep (se 5 (by rfl) ⟨486308, by rfl⟩ : syracuseStep 10374581 = 972617) B972617
theorem B1822247 : Blo 718322 1822247 := bstep (se 1 (by rfl) ⟨1366685, by rfl⟩ : syracuseStep 1822247 = 2733371) B2733371
theorem B9227843 : Blo 718322 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B1363807 : Blo 718322 1363807 := bstep (se 1 (by rfl) ⟨1022855, by rfl⟩ : syracuseStep 1363807 = 2045711) B2045711
theorem B1822571 : Blo 718322 1822571 := bstep (se 1 (by rfl) ⟨1366928, by rfl⟩ : syracuseStep 1822571 = 2733857) B2733857
theorem B4673551 : Blo 718322 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B1823219 : Blo 718322 1823219 := bstep (se 1 (by rfl) ⟨1367414, by rfl⟩ : syracuseStep 1823219 = 2734829) B2734829
theorem B1298963 : Blo 718322 1298963 := bstep (se 1 (by rfl) ⟨974222, by rfl⟩ : syracuseStep 1298963 = 1948445) B1948445
theorem B11686517 : Blo 718322 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B1823431 : Blo 718322 1823431 := bstep (se 1 (by rfl) ⟨1367573, by rfl⟩ : syracuseStep 1823431 = 2735147) B2735147
theorem B1299361 : Blo 718322 1299361 := bstep (se 2 (by rfl) ⟨487260, by rfl⟩ : syracuseStep 1299361 = 974521) B974521
theorem B2053127 : Blo 718322 2053127 := bstep (se 1 (by rfl) ⟨1539845, by rfl⟩ : syracuseStep 2053127 = 3079691) B3079691
theorem B1299655 : Blo 718322 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B2741633 : Blo 718322 2741633 := bstep (se 2 (by rfl) ⟨1028112, by rfl⟩ : syracuseStep 2741633 = 2056225) B2056225
theorem B2741647 : Blo 718322 2741647 := bstep (se 1 (by rfl) ⟨2056235, by rfl⟩ : syracuseStep 2741647 = 4112471) B4112471
theorem B808411 : Blo 718322 808411 := bstep (se 1 (by rfl) ⟨606308, by rfl⟩ : syracuseStep 808411 = 1212617) B1212617
theorem B5264993 : Blo 718322 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B1824353 : Blo 718322 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B1365751 : Blo 718322 1365751 := bstep (se 1 (by rfl) ⟨1024313, by rfl⟩ : syracuseStep 1365751 = 2048627) B2048627
theorem B15554339 : Blo 718322 15554339 := bstep (se 1 (by rfl) ⟨11665754, by rfl⟩ : syracuseStep 15554339 = 23331509) B23331509
theorem B808879 : Blo 718322 808879 := bstep (se 1 (by rfl) ⟨606659, by rfl⟩ : syracuseStep 808879 = 1213319) B1213319
theorem B1562543 : Blo 718322 1562543 := bstep (se 1 (by rfl) ⟨1171907, by rfl⟩ : syracuseStep 1562543 = 2343815) B2343815
theorem B1365979 : Blo 718322 1365979 := bstep (se 1 (by rfl) ⟨1024484, by rfl⟩ : syracuseStep 1365979 = 2048969) B2048969
theorem B1366055 : Blo 718322 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B12277817 : Blo 718322 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B4610105 : Blo 718322 4610105 := bstep (se 2 (by rfl) ⟨1728789, by rfl⟩ : syracuseStep 4610105 = 3457579) B3457579
theorem B5920883 : Blo 718322 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B1366139 : Blo 718322 1366139 := bstep (se 1 (by rfl) ⟨1024604, by rfl⟩ : syracuseStep 1366139 = 2049209) B2049209
theorem B809311 : Blo 718322 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B1366625 : Blo 718322 1366625 := bstep (se 2 (by rfl) ⟨512484, by rfl⟩ : syracuseStep 1366625 = 1024969) B1024969
theorem B809671 : Blo 718322 809671 := bstep (se 1 (by rfl) ⟨607253, by rfl⟩ : syracuseStep 809671 = 1214507) B1214507
theorem B1825811 : Blo 718322 1825811 := bstep (se 1 (by rfl) ⟨1369358, by rfl⟩ : syracuseStep 1825811 = 2738717) B2738717
theorem B6151211 : Blo 718322 6151211 := bstep (se 1 (by rfl) ⟨4613408, by rfl⟩ : syracuseStep 6151211 = 9226817) B9226817
theorem B6937643 : Blo 718322 6937643 := bstep (se 1 (by rfl) ⟨5203232, by rfl⟩ : syracuseStep 6937643 = 10406465) B10406465
theorem B3464345 : Blo 718322 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B3464363 : Blo 718322 3464363 := bstep (se 1 (by rfl) ⟨2598272, by rfl⟩ : syracuseStep 3464363 = 5196545) B5196545
theorem B2055689 : Blo 718322 2055689 := bstep (se 2 (by rfl) ⟨770883, by rfl⟩ : syracuseStep 2055689 = 1541767) B1541767
theorem B810535 : Blo 718322 810535 := bstep (se 1 (by rfl) ⟨607901, by rfl⟩ : syracuseStep 810535 = 1215803) B1215803
theorem B3071627 : Blo 718322 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B2186941 : Blo 718322 2186941 := bstep (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) B820103
theorem B2056043 : Blo 718322 2056043 := bstep (se 1 (by rfl) ⟨1542032, by rfl⟩ : syracuseStep 2056043 = 3084065) B3084065
theorem B1368083 : Blo 718322 1368083 := bstep (se 1 (by rfl) ⟨1026062, by rfl⟩ : syracuseStep 1368083 = 2052125) B2052125
theorem B6152273 : Blo 718322 6152273 := bstep (se 2 (by rfl) ⟨2307102, by rfl⟩ : syracuseStep 6152273 = 4614205) B4614205
theorem B909787 : Blo 718322 909787 := bstep (se 1 (by rfl) ⟨682340, by rfl⟩ : syracuseStep 909787 = 1364681) B1364681
theorem B4612589 : Blo 718322 4612589 := bstep (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) B1729721
theorem B2056691 : Blo 718322 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B3465787 : Blo 718322 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B5825357 : Blo 718322 5825357 := bstep (se 3 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 5825357 = 2184509) B2184509
theorem B812155 : Blo 718322 812155 := bstep (se 1 (by rfl) ⟨609116, by rfl⟩ : syracuseStep 812155 = 1218233) B1218233
theorem B1369487 : Blo 718322 1369487 := bstep (se 1 (by rfl) ⟨1027115, by rfl⟩ : syracuseStep 1369487 = 2054231) B2054231
theorem B1369639 : Blo 718322 1369639 := bstep (se 1 (by rfl) ⟨1027229, by rfl⟩ : syracuseStep 1369639 = 2054459) B2054459
theorem B1369723 : Blo 718322 1369723 := bstep (se 1 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 1369723 = 2054585) B2054585
theorem B4449937 : Blo 718322 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B4155095 : Blo 718322 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B5203693 : Blo 718322 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B4614023 : Blo 718322 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B5466041 : Blo 718322 5466041 := bstep (se 2 (by rfl) ⟨2049765, by rfl⟩ : syracuseStep 5466041 = 4099531) B4099531
theorem B8873921 : Blo 718322 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B168814529 : Blo 718322 168814529 := bstep (se 2 (by rfl) ⟨63305448, by rfl⟩ : syracuseStep 168814529 = 126610897) B126610897
theorem B1730567 : Blo 718322 1730567 := bstep (se 1 (by rfl) ⟨1297925, by rfl⟩ : syracuseStep 1730567 = 2595851) B2595851
theorem B1370209 : Blo 718322 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B3467785 : Blo 718322 3467785 := bstep (se 2 (by rfl) ⟨1300419, by rfl⟩ : syracuseStep 3467785 = 2600839) B2600839
theorem B18410165 : Blo 718322 18410165 := bstep (se 5 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 18410165 = 1725953) B1725953
theorem B3468035 : Blo 718322 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B1371143 : Blo 718322 1371143 := bstep (se 1 (by rfl) ⟨1028357, by rfl⟩ : syracuseStep 1371143 = 2056715) B2056715
theorem B4091309 : Blo 718322 4091309 := bstep (se 3 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 4091309 = 1534241) B1534241
theorem B3076001 : Blo 718322 3076001 := bstep (se 2 (by rfl) ⟨1153500, by rfl⟩ : syracuseStep 3076001 = 2307001) B2307001
theorem B5828537 : Blo 718322 5828537 := bstep (se 2 (by rfl) ⟨2185701, by rfl⟩ : syracuseStep 5828537 = 4371403) B4371403
theorem B913447 : Blo 718322 913447 := bstep (se 1 (by rfl) ⟨685085, by rfl⟩ : syracuseStep 913447 = 1370171) B1370171
theorem B1077497 : Blo 718322 1077497 := bstep (se 2 (by rfl) ⟨404061, by rfl⟩ : syracuseStep 1077497 = 808123) B808123
theorem B1077599 : Blo 718322 1077599 := bstep (se 1 (by rfl) ⟨808199, by rfl⟩ : syracuseStep 1077599 = 1616399) B1616399
theorem B1077611 : Blo 718322 1077611 := bstep (se 1 (by rfl) ⟨808208, by rfl⟩ : syracuseStep 1077611 = 1616417) B1616417
theorem B913771 : Blo 718322 913771 := bstep (se 1 (by rfl) ⟨685328, by rfl⟩ : syracuseStep 913771 = 1370657) B1370657
theorem B4452889 : Blo 718322 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B1077839 : Blo 718322 1077839 := bstep (se 1 (by rfl) ⟨808379, by rfl⟩ : syracuseStep 1077839 = 1616759) B1616759
theorem B913999 : Blo 718322 913999 := bstep (se 1 (by rfl) ⟨685499, by rfl⟩ : syracuseStep 913999 = 1370999) B1370999
theorem B1077959 : Blo 718322 1077959 := bstep (se 1 (by rfl) ⟨808469, by rfl⟩ : syracuseStep 1077959 = 1616939) B1616939
theorem B5468957 : Blo 718322 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B1078121 : Blo 718322 1078121 := bstep (se 2 (by rfl) ⟨404295, by rfl⟩ : syracuseStep 1078121 = 808591) B808591
theorem B1078199 : Blo 718322 1078199 := bstep (se 1 (by rfl) ⟨808649, by rfl⟩ : syracuseStep 1078199 = 1617299) B1617299
theorem B1078235 : Blo 718322 1078235 := bstep (se 1 (by rfl) ⟨808676, by rfl⟩ : syracuseStep 1078235 = 1617353) B1617353
theorem B8221661 : Blo 718322 8221661 := bstep (se 3 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 8221661 = 3083123) B3083123
theorem B6911041 : Blo 718322 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B3077315 : Blo 718322 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B1078703 : Blo 718322 1078703 := bstep (se 1 (by rfl) ⟨809027, by rfl⟩ : syracuseStep 1078703 = 1618055) B1618055
theorem B1078793 : Blo 718322 1078793 := bstep (se 2 (by rfl) ⟨404547, by rfl⟩ : syracuseStep 1078793 = 809095) B809095
theorem B718375 : Blo 718322 718375 := bstep (se 1 (by rfl) ⟨538781, by rfl⟩ : syracuseStep 718375 = 1077563) B1077563
theorem B1078823 : Blo 718322 1078823 := bstep (se 1 (by rfl) ⟨809117, by rfl⟩ : syracuseStep 1078823 = 1618235) B1618235
theorem B718415 : Blo 718322 718415 := bstep (se 1 (by rfl) ⟨538811, by rfl⟩ : syracuseStep 718415 = 1077623) B1077623
theorem B718431 : Blo 718322 718431 := bstep (se 1 (by rfl) ⟨538823, by rfl⟩ : syracuseStep 718431 = 1077647) B1077647
theorem B718459 : Blo 718322 718459 := bstep (se 1 (by rfl) ⟨538844, by rfl⟩ : syracuseStep 718459 = 1077689) B1077689
theorem B1078907 : Blo 718322 1078907 := bstep (se 1 (by rfl) ⟨809180, by rfl⟩ : syracuseStep 1078907 = 1618361) B1618361
theorem B8189585 : Blo 718322 8189585 := bstep (se 2 (by rfl) ⟨3071094, by rfl⟩ : syracuseStep 8189585 = 6142189) B6142189
theorem B718511 : Blo 718322 718511 := bstep (se 1 (by rfl) ⟨538883, by rfl⟩ : syracuseStep 718511 = 1077767) B1077767
theorem B718535 : Blo 718322 718535 := bstep (se 1 (by rfl) ⟨538901, by rfl⟩ : syracuseStep 718535 = 1077803) B1077803
theorem B718555 : Blo 718322 718555 := bstep (se 1 (by rfl) ⟨538916, by rfl⟩ : syracuseStep 718555 = 1077833) B1077833
theorem B1079033 : Blo 718322 1079033 := bstep (se 2 (by rfl) ⟨404637, by rfl⟩ : syracuseStep 1079033 = 809275) B809275
theorem B718631 : Blo 718322 718631 := bstep (se 1 (by rfl) ⟨538973, by rfl⟩ : syracuseStep 718631 = 1077947) B1077947
theorem B3503915 : Blo 718322 3503915 := bstep (se 1 (by rfl) ⟨2627936, by rfl⟩ : syracuseStep 3503915 = 5255873) B5255873
theorem B718671 : Blo 718322 718671 := bstep (se 1 (by rfl) ⟨539003, by rfl⟩ : syracuseStep 718671 = 1078007) B1078007
theorem B718687 : Blo 718322 718687 := bstep (se 1 (by rfl) ⟨539015, by rfl⟩ : syracuseStep 718687 = 1078031) B1078031
theorem B1079135 : Blo 718322 1079135 := bstep (se 1 (by rfl) ⟨809351, by rfl⟩ : syracuseStep 1079135 = 1618703) B1618703
theorem B1079147 : Blo 718322 1079147 := bstep (se 1 (by rfl) ⟨809360, by rfl⟩ : syracuseStep 1079147 = 1618721) B1618721
theorem B718715 : Blo 718322 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B718767 : Blo 718322 718767 := bstep (se 1 (by rfl) ⟨539075, by rfl⟩ : syracuseStep 718767 = 1078151) B1078151
theorem B718791 : Blo 718322 718791 := bstep (se 1 (by rfl) ⟨539093, by rfl⟩ : syracuseStep 718791 = 1078187) B1078187
theorem B718811 : Blo 718322 718811 := bstep (se 1 (by rfl) ⟨539108, by rfl⟩ : syracuseStep 718811 = 1078217) B1078217
theorem B718887 : Blo 718322 718887 := bstep (se 1 (by rfl) ⟨539165, by rfl⟩ : syracuseStep 718887 = 1078331) B1078331
theorem B718927 : Blo 718322 718927 := bstep (se 1 (by rfl) ⟨539195, by rfl⟩ : syracuseStep 718927 = 1078391) B1078391
theorem B1079375 : Blo 718322 1079375 := bstep (se 1 (by rfl) ⟨809531, by rfl⟩ : syracuseStep 1079375 = 1619063) B1619063
theorem B718943 : Blo 718322 718943 := bstep (se 1 (by rfl) ⟨539207, by rfl⟩ : syracuseStep 718943 = 1078415) B1078415
theorem B718971 : Blo 718322 718971 := bstep (se 1 (by rfl) ⟨539228, by rfl⟩ : syracuseStep 718971 = 1078457) B1078457
theorem B719023 : Blo 718322 719023 := bstep (se 1 (by rfl) ⟨539267, by rfl⟩ : syracuseStep 719023 = 1078535) B1078535
theorem B719047 : Blo 718322 719047 := bstep (se 1 (by rfl) ⟨539285, by rfl⟩ : syracuseStep 719047 = 1078571) B1078571
theorem B1079495 : Blo 718322 1079495 := bstep (se 1 (by rfl) ⟨809621, by rfl⟩ : syracuseStep 1079495 = 1619243) B1619243
theorem B719067 : Blo 718322 719067 := bstep (se 1 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 719067 = 1078601) B1078601
theorem B719143 : Blo 718322 719143 := bstep (se 1 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 719143 = 1078715) B1078715
theorem B719183 : Blo 718322 719183 := bstep (se 1 (by rfl) ⟨539387, by rfl⟩ : syracuseStep 719183 = 1078775) B1078775
theorem B719199 : Blo 718322 719199 := bstep (se 1 (by rfl) ⟨539399, by rfl⟩ : syracuseStep 719199 = 1078799) B1078799
theorem B1079657 : Blo 718322 1079657 := bstep (se 2 (by rfl) ⟨404871, by rfl⟩ : syracuseStep 1079657 = 809743) B809743
theorem B719227 : Blo 718322 719227 := bstep (se 1 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 719227 = 1078841) B1078841
theorem B719279 : Blo 718322 719279 := bstep (se 1 (by rfl) ⟨539459, by rfl⟩ : syracuseStep 719279 = 1078919) B1078919
theorem B1079735 : Blo 718322 1079735 := bstep (se 1 (by rfl) ⟨809801, by rfl⟩ : syracuseStep 1079735 = 1619603) B1619603
theorem B719303 : Blo 718322 719303 := bstep (se 1 (by rfl) ⟨539477, by rfl⟩ : syracuseStep 719303 = 1078955) B1078955
theorem B719323 : Blo 718322 719323 := bstep (se 1 (by rfl) ⟨539492, by rfl⟩ : syracuseStep 719323 = 1078985) B1078985
theorem B1079771 : Blo 718322 1079771 := bstep (se 1 (by rfl) ⟨809828, by rfl⟩ : syracuseStep 1079771 = 1619657) B1619657
theorem B719399 : Blo 718322 719399 := bstep (se 1 (by rfl) ⟨539549, by rfl⟩ : syracuseStep 719399 = 1079099) B1079099
theorem B719439 : Blo 718322 719439 := bstep (se 1 (by rfl) ⟨539579, by rfl⟩ : syracuseStep 719439 = 1079159) B1079159
theorem B719455 : Blo 718322 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B719483 : Blo 718322 719483 := bstep (se 1 (by rfl) ⟨539612, by rfl⟩ : syracuseStep 719483 = 1079225) B1079225
theorem B719535 : Blo 718322 719535 := bstep (se 1 (by rfl) ⟨539651, by rfl⟩ : syracuseStep 719535 = 1079303) B1079303
theorem B719559 : Blo 718322 719559 := bstep (se 1 (by rfl) ⟨539669, by rfl⟩ : syracuseStep 719559 = 1079339) B1079339
theorem B8321737 : Blo 718322 8321737 := bstep (se 2 (by rfl) ⟨3120651, by rfl⟩ : syracuseStep 8321737 = 6241303) B6241303
theorem B719579 : Blo 718322 719579 := bstep (se 1 (by rfl) ⟨539684, by rfl⟩ : syracuseStep 719579 = 1079369) B1079369
theorem B719655 : Blo 718322 719655 := bstep (se 1 (by rfl) ⟨539741, by rfl⟩ : syracuseStep 719655 = 1079483) B1079483
theorem B719695 : Blo 718322 719695 := bstep (se 1 (by rfl) ⟨539771, by rfl⟩ : syracuseStep 719695 = 1079543) B1079543
theorem B719711 : Blo 718322 719711 := bstep (se 1 (by rfl) ⟨539783, by rfl⟩ : syracuseStep 719711 = 1079567) B1079567
theorem B719739 : Blo 718322 719739 := bstep (se 1 (by rfl) ⟨539804, by rfl⟩ : syracuseStep 719739 = 1079609) B1079609
theorem B719791 : Blo 718322 719791 := bstep (se 1 (by rfl) ⟨539843, by rfl⟩ : syracuseStep 719791 = 1079687) B1079687
theorem B1080239 : Blo 718322 1080239 := bstep (se 1 (by rfl) ⟨810179, by rfl⟩ : syracuseStep 1080239 = 1620359) B1620359
theorem B719815 : Blo 718322 719815 := bstep (se 1 (by rfl) ⟨539861, by rfl⟩ : syracuseStep 719815 = 1079723) B1079723
theorem B719835 : Blo 718322 719835 := bstep (se 1 (by rfl) ⟨539876, by rfl⟩ : syracuseStep 719835 = 1079753) B1079753
theorem B1080329 : Blo 718322 1080329 := bstep (se 2 (by rfl) ⟨405123, by rfl⟩ : syracuseStep 1080329 = 810247) B810247
theorem B719911 : Blo 718322 719911 := bstep (se 1 (by rfl) ⟨539933, by rfl⟩ : syracuseStep 719911 = 1079867) B1079867
theorem B1080359 : Blo 718322 1080359 := bstep (se 1 (by rfl) ⟨810269, by rfl⟩ : syracuseStep 1080359 = 1620539) B1620539
theorem B719951 : Blo 718322 719951 := bstep (se 1 (by rfl) ⟨539963, by rfl⟩ : syracuseStep 719951 = 1079927) B1079927
theorem B719967 : Blo 718322 719967 := bstep (se 1 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 719967 = 1079951) B1079951
theorem B719995 : Blo 718322 719995 := bstep (se 1 (by rfl) ⟨539996, by rfl⟩ : syracuseStep 719995 = 1079993) B1079993
theorem B1080443 : Blo 718322 1080443 := bstep (se 1 (by rfl) ⟨810332, by rfl⟩ : syracuseStep 1080443 = 1620665) B1620665
theorem B720047 : Blo 718322 720047 := bstep (se 1 (by rfl) ⟨540035, by rfl⟩ : syracuseStep 720047 = 1080071) B1080071
theorem B720071 : Blo 718322 720071 := bstep (se 1 (by rfl) ⟨540053, by rfl⟩ : syracuseStep 720071 = 1080107) B1080107
theorem B720091 : Blo 718322 720091 := bstep (se 1 (by rfl) ⟨540068, by rfl⟩ : syracuseStep 720091 = 1080137) B1080137
theorem B8781047 : Blo 718322 8781047 := bstep (se 1 (by rfl) ⟨6585785, by rfl⟩ : syracuseStep 8781047 = 13171571) B13171571
theorem B1080569 : Blo 718322 1080569 := bstep (se 2 (by rfl) ⟨405213, by rfl⟩ : syracuseStep 1080569 = 810427) B810427
theorem B720167 : Blo 718322 720167 := bstep (se 1 (by rfl) ⟨540125, by rfl⟩ : syracuseStep 720167 = 1080251) B1080251
theorem B720207 : Blo 718322 720207 := bstep (se 1 (by rfl) ⟨540155, by rfl⟩ : syracuseStep 720207 = 1080311) B1080311
theorem B720223 : Blo 718322 720223 := bstep (se 1 (by rfl) ⟨540167, by rfl⟩ : syracuseStep 720223 = 1080335) B1080335
theorem B1080671 : Blo 718322 1080671 := bstep (se 1 (by rfl) ⟨810503, by rfl⟩ : syracuseStep 1080671 = 1621007) B1621007
theorem B1080683 : Blo 718322 1080683 := bstep (se 1 (by rfl) ⟨810512, by rfl⟩ : syracuseStep 1080683 = 1621025) B1621025
theorem B720251 : Blo 718322 720251 := bstep (se 1 (by rfl) ⟨540188, by rfl⟩ : syracuseStep 720251 = 1080377) B1080377
theorem B4619663 : Blo 718322 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B720303 : Blo 718322 720303 := bstep (se 1 (by rfl) ⟨540227, by rfl⟩ : syracuseStep 720303 = 1080455) B1080455
theorem B720327 : Blo 718322 720327 := bstep (se 1 (by rfl) ⟨540245, by rfl⟩ : syracuseStep 720327 = 1080491) B1080491
theorem B720347 : Blo 718322 720347 := bstep (se 1 (by rfl) ⟨540260, by rfl⟩ : syracuseStep 720347 = 1080521) B1080521
theorem B720423 : Blo 718322 720423 := bstep (se 1 (by rfl) ⟨540317, by rfl⟩ : syracuseStep 720423 = 1080635) B1080635
theorem B720463 : Blo 718322 720463 := bstep (se 1 (by rfl) ⟨540347, by rfl⟩ : syracuseStep 720463 = 1080695) B1080695
theorem B1080911 : Blo 718322 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B6159959 : Blo 718322 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B720479 : Blo 718322 720479 := bstep (se 1 (by rfl) ⟨540359, by rfl⟩ : syracuseStep 720479 = 1080719) B1080719
theorem B720507 : Blo 718322 720507 := bstep (se 1 (by rfl) ⟨540380, by rfl⟩ : syracuseStep 720507 = 1080761) B1080761
theorem B720559 : Blo 718322 720559 := bstep (se 1 (by rfl) ⟨540419, by rfl⟩ : syracuseStep 720559 = 1080839) B1080839
theorem B720583 : Blo 718322 720583 := bstep (se 1 (by rfl) ⟨540437, by rfl⟩ : syracuseStep 720583 = 1080875) B1080875
theorem B1081031 : Blo 718322 1081031 := bstep (se 1 (by rfl) ⟨810773, by rfl⟩ : syracuseStep 1081031 = 1621547) B1621547
theorem B720603 : Blo 718322 720603 := bstep (se 1 (by rfl) ⟨540452, by rfl⟩ : syracuseStep 720603 = 1080905) B1080905
theorem B720679 : Blo 718322 720679 := bstep (se 1 (by rfl) ⟨540509, by rfl⟩ : syracuseStep 720679 = 1081019) B1081019
theorem B720719 : Blo 718322 720719 := bstep (se 1 (by rfl) ⟨540539, by rfl⟩ : syracuseStep 720719 = 1081079) B1081079
theorem B720735 : Blo 718322 720735 := bstep (se 1 (by rfl) ⟨540551, by rfl⟩ : syracuseStep 720735 = 1081103) B1081103
theorem B1081193 : Blo 718322 1081193 := bstep (se 2 (by rfl) ⟨405447, by rfl⟩ : syracuseStep 1081193 = 810895) B810895
theorem B720763 : Blo 718322 720763 := bstep (se 1 (by rfl) ⟨540572, by rfl⟩ : syracuseStep 720763 = 1081145) B1081145
theorem B720815 : Blo 718322 720815 := bstep (se 1 (by rfl) ⟨540611, by rfl⟩ : syracuseStep 720815 = 1081223) B1081223
theorem B1081271 : Blo 718322 1081271 := bstep (se 1 (by rfl) ⟨810953, by rfl⟩ : syracuseStep 1081271 = 1621907) B1621907
theorem B1212347 : Blo 718322 1212347 := bstep (se 1 (by rfl) ⟨909260, by rfl⟩ : syracuseStep 1212347 = 1818521) B1818521
theorem B720839 : Blo 718322 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B720859 : Blo 718322 720859 := bstep (se 1 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 720859 = 1081289) B1081289
theorem B1081307 : Blo 718322 1081307 := bstep (se 1 (by rfl) ⟨810980, by rfl⟩ : syracuseStep 1081307 = 1621961) B1621961
theorem B721183 : Blo 718322 721183 := bstep (se 1 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 721183 = 1081775) B1081775
theorem B1081691 : Blo 718322 1081691 := bstep (se 1 (by rfl) ⟨811268, by rfl⟩ : syracuseStep 1081691 = 1622537) B1622537
theorem B721243 : Blo 718322 721243 := bstep (se 1 (by rfl) ⟨540932, by rfl⟩ : syracuseStep 721243 = 1081865) B1081865
theorem B721263 : Blo 718322 721263 := bstep (se 1 (by rfl) ⟨540947, by rfl⟩ : syracuseStep 721263 = 1081895) B1081895
theorem B721319 : Blo 718322 721319 := bstep (se 1 (by rfl) ⟨540989, by rfl⟩ : syracuseStep 721319 = 1081979) B1081979
theorem B3113417 : Blo 718322 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B3703259 : Blo 718322 3703259 := bstep (se 1 (by rfl) ⟨2777444, by rfl⟩ : syracuseStep 3703259 = 5554889) B5554889
theorem B721403 : Blo 718322 721403 := bstep (se 1 (by rfl) ⟨541052, by rfl⟩ : syracuseStep 721403 = 1082105) B1082105
theorem B1081919 : Blo 718322 1081919 := bstep (se 1 (by rfl) ⟨811439, by rfl⟩ : syracuseStep 1081919 = 1622879) B1622879
theorem B721471 : Blo 718322 721471 := bstep (se 1 (by rfl) ⟨541103, by rfl⟩ : syracuseStep 721471 = 1082207) B1082207
theorem B721479 : Blo 718322 721479 := bstep (se 1 (by rfl) ⟨541109, by rfl⟩ : syracuseStep 721479 = 1082219) B1082219
theorem B1213049 : Blo 718322 1213049 := bstep (se 2 (by rfl) ⟨454893, by rfl⟩ : syracuseStep 1213049 = 909787) B909787
theorem B1213103 : Blo 718322 1213103 := bstep (se 1 (by rfl) ⟨909827, by rfl⟩ : syracuseStep 1213103 = 1819655) B1819655
theorem B1082039 : Blo 718322 1082039 := bstep (se 1 (by rfl) ⟨811529, by rfl⟩ : syracuseStep 1082039 = 1623059) B1623059
theorem B721631 : Blo 718322 721631 := bstep (se 1 (by rfl) ⟨541223, by rfl⟩ : syracuseStep 721631 = 1082447) B1082447
theorem B4621049 : Blo 718322 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B721711 : Blo 718322 721711 := bstep (se 1 (by rfl) ⟨541283, by rfl⟩ : syracuseStep 721711 = 1082567) B1082567
theorem B2425679 : Blo 718322 2425679 := bstep (se 1 (by rfl) ⟨1819259, by rfl⟩ : syracuseStep 2425679 = 3638519) B3638519
theorem B1213339 : Blo 718322 1213339 := bstep (se 1 (by rfl) ⟨910004, by rfl⟩ : syracuseStep 1213339 = 1820009) B1820009
theorem B1082267 : Blo 718322 1082267 := bstep (se 1 (by rfl) ⟨811700, by rfl⟩ : syracuseStep 1082267 = 1623401) B1623401
theorem B721819 : Blo 718322 721819 := bstep (se 1 (by rfl) ⟨541364, by rfl⟩ : syracuseStep 721819 = 1082729) B1082729
theorem B9372611 : Blo 718322 9372611 := bstep (se 1 (by rfl) ⟨7029458, by rfl⟩ : syracuseStep 9372611 = 14058917) B14058917
theorem B721871 : Blo 718322 721871 := bstep (se 1 (by rfl) ⟨541403, by rfl⟩ : syracuseStep 721871 = 1082807) B1082807
theorem B721895 : Blo 718322 721895 := bstep (se 1 (by rfl) ⟨541421, by rfl⟩ : syracuseStep 721895 = 1082843) B1082843
theorem B5538959 : Blo 718322 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B2426003 : Blo 718322 2426003 := bstep (se 1 (by rfl) ⟨1819502, by rfl⟩ : syracuseStep 2426003 = 3639005) B3639005
theorem B3081415 : Blo 718322 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B3114233 : Blo 718322 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B722207 : Blo 718322 722207 := bstep (se 1 (by rfl) ⟨541655, by rfl⟩ : syracuseStep 722207 = 1083311) B1083311
theorem B6325541 : Blo 718322 6325541 := bstep (se 4 (by rfl) ⟨593019, by rfl⟩ : syracuseStep 6325541 = 1186039) B1186039
theorem B1082663 : Blo 718322 1082663 := bstep (se 1 (by rfl) ⟨811997, by rfl⟩ : syracuseStep 1082663 = 1623995) B1623995
theorem B722267 : Blo 718322 722267 := bstep (se 1 (by rfl) ⟨541700, by rfl⟩ : syracuseStep 722267 = 1083401) B1083401
theorem B722287 : Blo 718322 722287 := bstep (se 1 (by rfl) ⟨541715, by rfl⟩ : syracuseStep 722287 = 1083431) B1083431
theorem B1082747 : Blo 718322 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B2426273 : Blo 718322 2426273 := bstep (se 2 (by rfl) ⟨909852, by rfl⟩ : syracuseStep 2426273 = 1819705) B1819705
theorem B1082873 : Blo 718322 1082873 := bstep (se 2 (by rfl) ⟨406077, by rfl⟩ : syracuseStep 1082873 = 812155) B812155
theorem B1082975 : Blo 718322 1082975 := bstep (se 1 (by rfl) ⟨812231, by rfl⟩ : syracuseStep 1082975 = 1624463) B1624463
theorem B1476407 : Blo 718322 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1083191 : Blo 718322 1083191 := bstep (se 1 (by rfl) ⟨812393, by rfl⟩ : syracuseStep 1083191 = 1624787) B1624787
theorem B3639329 : Blo 718322 3639329 := bstep (se 2 (by rfl) ⟨1364748, by rfl⟩ : syracuseStep 3639329 = 2729497) B2729497
theorem B5933249 : Blo 718322 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B3639491 : Blo 718322 3639491 := bstep (se 1 (by rfl) ⟨2729618, by rfl⟩ : syracuseStep 3639491 = 5459237) B5459237
theorem B6916387 : Blo 718322 6916387 := bstep (se 1 (by rfl) ⟨5187290, by rfl⟩ : syracuseStep 6916387 = 10374581) B10374581
theorem B1214831 : Blo 718322 1214831 := bstep (se 1 (by rfl) ⟨911123, by rfl⟩ : syracuseStep 1214831 = 1822247) B1822247
theorem B5474789 : Blo 718322 5474789 := bstep (se 4 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 5474789 = 1026523) B1026523
theorem B1215047 : Blo 718322 1215047 := bstep (se 1 (by rfl) ⟨911285, by rfl⟩ : syracuseStep 1215047 = 1822571) B1822571
theorem B1215479 : Blo 718322 1215479 := bstep (se 1 (by rfl) ⟨911609, by rfl⟩ : syracuseStep 1215479 = 1823219) B1823219
theorem B2493659 : Blo 718322 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B5835995 : Blo 718322 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B4623713 : Blo 718322 4623713 := bstep (se 2 (by rfl) ⟨1733892, by rfl⟩ : syracuseStep 4623713 = 3467785) B3467785
theorem B3083791 : Blo 718322 3083791 := bstep (se 1 (by rfl) ⟨2312843, by rfl⟩ : syracuseStep 3083791 = 4625687) B4625687
theorem B3509995 : Blo 718322 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B1216235 : Blo 718322 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B6164333 : Blo 718322 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B2429459 : Blo 718322 2429459 := bstep (se 1 (by rfl) ⟨1822094, by rfl⟩ : syracuseStep 2429459 = 3644189) B3644189
theorem B11080253 : Blo 718322 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B1217207 : Blo 718322 1217207 := bstep (se 1 (by rfl) ⟨912905, by rfl⟩ : syracuseStep 1217207 = 1825811) B1825811
theorem B4100807 : Blo 718322 4100807 := bstep (se 1 (by rfl) ⟨3075605, by rfl⟩ : syracuseStep 4100807 = 6151211) B6151211
theorem B4625095 : Blo 718322 4625095 := bstep (se 1 (by rfl) ⟨3468821, by rfl⟩ : syracuseStep 4625095 = 6937643) B6937643
theorem B12325931 : Blo 718322 12325931 := bstep (se 1 (by rfl) ⟨9244448, by rfl⟩ : syracuseStep 12325931 = 18488897) B18488897
theorem B15602777 : Blo 718322 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B23663789 : Blo 718322 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B6231401 : Blo 718322 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B1217929 : Blo 718322 1217929 := bstep (se 2 (by rfl) ⟨456723, by rfl⟩ : syracuseStep 1217929 = 913447) B913447
theorem B4101515 : Blo 718322 4101515 := bstep (se 1 (by rfl) ⟨3076136, by rfl⟩ : syracuseStep 4101515 = 6152273) B6152273
theorem B1218361 : Blo 718322 1218361 := bstep (se 2 (by rfl) ⟨456885, by rfl⟩ : syracuseStep 1218361 = 913771) B913771
theorem B3643217 : Blo 718322 3643217 := bstep (se 2 (by rfl) ⟨1366206, by rfl⟩ : syracuseStep 3643217 = 2732413) B2732413
theorem B5937185 : Blo 718322 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B1218665 : Blo 718322 1218665 := bstep (se 2 (by rfl) ⟨456999, by rfl⟩ : syracuseStep 1218665 = 913999) B913999
theorem B2431241 : Blo 718322 2431241 := bstep (se 2 (by rfl) ⟨911715, by rfl⟩ : syracuseStep 2431241 = 1823431) B1823431
theorem B3644027 : Blo 718322 3644027 := bstep (se 1 (by rfl) ⟨2733020, by rfl⟩ : syracuseStep 3644027 = 5466041) B5466041
theorem B1153711 : Blo 718322 1153711 := bstep (se 1 (by rfl) ⟨865283, by rfl⟩ : syracuseStep 1153711 = 1730567) B1730567
theorem B9214721 : Blo 718322 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B9248093 : Blo 718322 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B2432375 : Blo 718322 2432375 := bstep (se 1 (by rfl) ⟨1824281, by rfl⟩ : syracuseStep 2432375 = 3648563) B3648563
theorem B6397321 : Blo 718322 6397321 := bstep (se 2 (by rfl) ⟨2398995, by rfl⟩ : syracuseStep 6397321 = 4797991) B4797991
theorem B2727539 : Blo 718322 2727539 := bstep (se 1 (by rfl) ⟨2045654, by rfl⟩ : syracuseStep 2727539 = 4091309) B4091309
theorem B2662301 : Blo 718322 2662301 := bstep (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) B998363
theorem B3285011 : Blo 718322 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B2433455 : Blo 718322 2433455 := bstep (se 1 (by rfl) ⟨1825091, by rfl⟩ : syracuseStep 2433455 = 3650183) B3650183
theorem B3645971 : Blo 718322 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B5481107 : Blo 718322 5481107 := bstep (se 1 (by rfl) ⟨4110830, by rfl⟩ : syracuseStep 5481107 = 8221661) B8221661
theorem B5251787 : Blo 718322 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B2335943 : Blo 718322 2335943 := bstep (se 1 (by rfl) ⟨1751957, by rfl⟩ : syracuseStep 2335943 = 3503915) B3503915
theorem B2434427 : Blo 718322 2434427 := bstep (se 1 (by rfl) ⟨1825820, by rfl⟩ : syracuseStep 2434427 = 3651641) B3651641
theorem B3647753 : Blo 718322 3647753 := bstep (se 2 (by rfl) ⟨1367907, by rfl⟩ : syracuseStep 3647753 = 2735815) B2735815
theorem B4106639 : Blo 718322 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B2730743 : Blo 718322 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B2435831 : Blo 718322 2435831 := bstep (se 1 (by rfl) ⟨1826873, by rfl⟩ : syracuseStep 2435831 = 3653747) B3653747
theorem B1387343 : Blo 718322 1387343 := bstep (se 1 (by rfl) ⟨1040507, by rfl⟩ : syracuseStep 1387343 = 2081015) B2081015
theorem B2304911 : Blo 718322 2304911 := bstep (se 1 (by rfl) ⟨1728683, by rfl⟩ : syracuseStep 2304911 = 3457367) B3457367
theorem B1616795 : Blo 718322 1616795 := bstep (se 1 (by rfl) ⟨1212596, by rfl⟩ : syracuseStep 1616795 = 2425193) B2425193
theorem B1616993 : Blo 718322 1616993 := bstep (se 2 (by rfl) ⟨606372, by rfl⟩ : syracuseStep 1616993 = 1212745) B1212745
theorem B6139151 : Blo 718322 6139151 := bstep (se 1 (by rfl) ⟨4604363, by rfl⟩ : syracuseStep 6139151 = 9208727) B9208727
theorem B1617191 : Blo 718322 1617191 := bstep (se 1 (by rfl) ⟨1212893, by rfl⟩ : syracuseStep 1617191 = 2425787) B2425787
theorem B3648887 : Blo 718322 3648887 := bstep (se 1 (by rfl) ⟨2736665, by rfl⟩ : syracuseStep 3648887 = 5473331) B5473331
theorem B4369793 : Blo 718322 4369793 := bstep (se 2 (by rfl) ⟨1638672, by rfl⟩ : syracuseStep 4369793 = 3277345) B3277345
theorem B3649049 : Blo 718322 3649049 := bstep (se 2 (by rfl) ⟨1368393, by rfl⟩ : syracuseStep 3649049 = 2736787) B2736787
theorem B1617569 : Blo 718322 1617569 := bstep (se 2 (by rfl) ⟨606588, by rfl⟩ : syracuseStep 1617569 = 1213177) B1213177
theorem B2436911 : Blo 718322 2436911 := bstep (se 1 (by rfl) ⟨1827683, by rfl⟩ : syracuseStep 2436911 = 3655367) B3655367
theorem B5484509 : Blo 718322 5484509 := bstep (se 3 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 5484509 = 2056691) B2056691
theorem B1617929 : Blo 718322 1617929 := bstep (se 2 (by rfl) ⟨606723, by rfl⟩ : syracuseStep 1617929 = 1213447) B1213447
theorem B1618343 : Blo 718322 1618343 := bstep (se 1 (by rfl) ⟨1213757, by rfl⟩ : syracuseStep 1618343 = 2427515) B2427515
theorem B1618451 : Blo 718322 1618451 := bstep (se 1 (by rfl) ⟨1213838, by rfl⟩ : syracuseStep 1618451 = 2427677) B2427677
theorem B1618505 : Blo 718322 1618505 := bstep (se 2 (by rfl) ⟨606939, by rfl⟩ : syracuseStep 1618505 = 1213879) B1213879
theorem B2306731 : Blo 718322 2306731 := bstep (se 1 (by rfl) ⟨1730048, by rfl⟩ : syracuseStep 2306731 = 3460097) B3460097
theorem B1618919 : Blo 718322 1618919 := bstep (se 1 (by rfl) ⟨1214189, by rfl⟩ : syracuseStep 1618919 = 2428379) B2428379
theorem B2733203 : Blo 718322 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B1619297 : Blo 718322 1619297 := bstep (se 2 (by rfl) ⟨607236, by rfl⟩ : syracuseStep 1619297 = 1214473) B1214473
theorem B1619387 : Blo 718322 1619387 := bstep (se 1 (by rfl) ⟨1214540, by rfl⟩ : syracuseStep 1619387 = 2429081) B2429081
theorem B1619513 : Blo 718322 1619513 := bstep (se 2 (by rfl) ⟨607317, by rfl⟩ : syracuseStep 1619513 = 1214635) B1214635
theorem B4110011 : Blo 718322 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B1620179 : Blo 718322 1620179 := bstep (se 1 (by rfl) ⟨1215134, by rfl⟩ : syracuseStep 1620179 = 2430269) B2430269
theorem B1620233 : Blo 718322 1620233 := bstep (se 2 (by rfl) ⟨607587, by rfl⟩ : syracuseStep 1620233 = 1215175) B1215175
theorem B768295 : Blo 718322 768295 := bstep (se 1 (by rfl) ⟨576221, by rfl⟩ : syracuseStep 768295 = 1152443) B1152443
theorem B3651965 : Blo 718322 3651965 := bstep (se 3 (by rfl) ⟨684743, by rfl⟩ : syracuseStep 3651965 = 1369487) B1369487
theorem B1620449 : Blo 718322 1620449 := bstep (se 2 (by rfl) ⟨607668, by rfl⟩ : syracuseStep 1620449 = 1215337) B1215337
theorem B10369559 : Blo 718322 10369559 := bstep (se 1 (by rfl) ⟨7777169, by rfl⟩ : syracuseStep 10369559 = 15554339) B15554339
theorem B2603593 : Blo 718322 2603593 := bstep (se 2 (by rfl) ⟨976347, by rfl⟩ : syracuseStep 2603593 = 1952695) B1952695
theorem B3947255 : Blo 718322 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B2079479 : Blo 718322 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B1620755 : Blo 718322 1620755 := bstep (se 1 (by rfl) ⟨1215566, by rfl⟩ : syracuseStep 1620755 = 2431133) B2431133
theorem B7388147 : Blo 718322 7388147 := bstep (se 1 (by rfl) ⟨5541110, by rfl⟩ : syracuseStep 7388147 = 11082221) B11082221
theorem B1621115 : Blo 718322 1621115 := bstep (se 1 (by rfl) ⟨1215836, by rfl⟩ : syracuseStep 1621115 = 2431673) B2431673
theorem B17480933 : Blo 718322 17480933 := bstep (se 4 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 17480933 = 3277675) B3277675
theorem B1621241 : Blo 718322 1621241 := bstep (se 2 (by rfl) ⟨607965, by rfl⟩ : syracuseStep 1621241 = 1215931) B1215931
theorem B1621385 : Blo 718322 1621385 := bstep (se 2 (by rfl) ⟨608019, by rfl⟩ : syracuseStep 1621385 = 1216039) B1216039
theorem B2309563 : Blo 718322 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B2309575 : Blo 718322 2309575 := bstep (se 1 (by rfl) ⟨1732181, by rfl⟩ : syracuseStep 2309575 = 3464363) B3464363
theorem B1621511 : Blo 718322 1621511 := bstep (se 1 (by rfl) ⟨1216133, by rfl⟩ : syracuseStep 1621511 = 2432267) B2432267
theorem B1949267 : Blo 718322 1949267 := bstep (se 1 (by rfl) ⟨1461950, by rfl⟩ : syracuseStep 1949267 = 2923901) B2923901
theorem B6930035 : Blo 718322 6930035 := bstep (se 1 (by rfl) ⟨5197526, by rfl⟩ : syracuseStep 6930035 = 10395053) B10395053
theorem B1621691 : Blo 718322 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B12304061 : Blo 718322 12304061 := bstep (se 3 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 12304061 = 4614023) B4614023
theorem B2047751 : Blo 718322 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B1818409 : Blo 718322 1818409 := bstep (se 2 (by rfl) ⟨681903, by rfl⟩ : syracuseStep 1818409 = 1363807) B1363807
theorem B3653423 : Blo 718322 3653423 := bstep (se 1 (by rfl) ⟨2740067, by rfl⟩ : syracuseStep 3653423 = 5480135) B5480135
theorem B1621817 : Blo 718322 1621817 := bstep (se 2 (by rfl) ⟨608181, by rfl⟩ : syracuseStep 1621817 = 1216363) B1216363
theorem B29606309 : Blo 718322 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B1622447 : Blo 718322 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B1753555 : Blo 718322 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B1622483 : Blo 718322 1622483 := bstep (se 1 (by rfl) ⟨1216862, by rfl⟩ : syracuseStep 1622483 = 2433725) B2433725
theorem B3883571 : Blo 718322 3883571 := bstep (se 1 (by rfl) ⟨2912678, by rfl⟩ : syracuseStep 3883571 = 5825357) B5825357
theorem B1819199 : Blo 718322 1819199 := bstep (se 1 (by rfl) ⟨1364399, by rfl⟩ : syracuseStep 1819199 = 2728799) B2728799
theorem B1622591 : Blo 718322 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B1622699 : Blo 718322 1622699 := bstep (se 1 (by rfl) ⟨1217024, by rfl⟩ : syracuseStep 1622699 = 2434049) B2434049
theorem B26231597 : Blo 718322 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B1426331 : Blo 718322 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B2737091 : Blo 718322 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B4441051 : Blo 718322 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B6931493 : Blo 718322 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B1819847 : Blo 718322 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B1623239 : Blo 718322 1623239 := bstep (se 1 (by rfl) ⟨1217429, by rfl⟩ : syracuseStep 1623239 = 2434859) B2434859
theorem B1819867 : Blo 718322 1819867 := bstep (se 1 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 1819867 = 2729801) B2729801
theorem B112543019 : Blo 718322 112543019 := bstep (se 1 (by rfl) ⟨84407264, by rfl⟩ : syracuseStep 112543019 = 168814529) B168814529
theorem B1623419 : Blo 718322 1623419 := bstep (se 1 (by rfl) ⟨1217564, by rfl⟩ : syracuseStep 1623419 = 2435129) B2435129
theorem B2737547 : Blo 718322 2737547 := bstep (se 1 (by rfl) ⟨2053160, by rfl⟩ : syracuseStep 2737547 = 4106321) B4106321
theorem B1623545 : Blo 718322 1623545 := bstep (se 2 (by rfl) ⟨608829, by rfl⟩ : syracuseStep 1623545 = 1217659) B1217659
theorem B1623635 : Blo 718322 1623635 := bstep (se 1 (by rfl) ⟨1217726, by rfl⟩ : syracuseStep 1623635 = 2435453) B2435453
theorem B1623815 : Blo 718322 1623815 := bstep (se 1 (by rfl) ⟨1217861, by rfl⟩ : syracuseStep 1623815 = 2435723) B2435723
theorem B12273443 : Blo 718322 12273443 := bstep (se 1 (by rfl) ⟨9205082, by rfl⟩ : syracuseStep 12273443 = 18410165) B18410165
theorem B3655529 : Blo 718322 3655529 := bstep (se 2 (by rfl) ⟨1370823, by rfl⟩ : syracuseStep 3655529 = 2741647) B2741647
theorem B12339053 : Blo 718322 12339053 := bstep (se 3 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 12339053 = 4627145) B4627145
theorem B7784525 : Blo 718322 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B1821001 : Blo 718322 1821001 := bstep (se 2 (by rfl) ⟨682875, by rfl⟩ : syracuseStep 1821001 = 1365751) B1365751
theorem B1624427 : Blo 718322 1624427 := bstep (se 1 (by rfl) ⟨1218320, by rfl⟩ : syracuseStep 1624427 = 2436641) B2436641
theorem B1624571 : Blo 718322 1624571 := bstep (se 1 (by rfl) ⟨1218428, by rfl⟩ : syracuseStep 1624571 = 2436857) B2436857
theorem B2050667 : Blo 718322 2050667 := bstep (se 1 (by rfl) ⟨1538000, by rfl⟩ : syracuseStep 2050667 = 3076001) B3076001
theorem B1821305 : Blo 718322 1821305 := bstep (se 2 (by rfl) ⟨682989, by rfl⟩ : syracuseStep 1821305 = 1365979) B1365979
theorem B1624697 : Blo 718322 1624697 := bstep (se 2 (by rfl) ⟨609261, by rfl⟩ : syracuseStep 1624697 = 1218523) B1218523
theorem B3885691 : Blo 718322 3885691 := bstep (se 1 (by rfl) ⟨2914268, by rfl⟩ : syracuseStep 3885691 = 5828537) B5828537
theorem B1624751 : Blo 718322 1624751 := bstep (se 1 (by rfl) ⟨1218563, by rfl⟩ : syracuseStep 1624751 = 2437127) B2437127
theorem B1624823 : Blo 718322 1624823 := bstep (se 1 (by rfl) ⟨1218617, by rfl⟩ : syracuseStep 1624823 = 2437235) B2437235
theorem B1625003 : Blo 718322 1625003 := bstep (se 1 (by rfl) ⟨1218752, by rfl⟩ : syracuseStep 1625003 = 2437505) B2437505
theorem B3460211 : Blo 718322 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B2051543 : Blo 718322 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B11095649 : Blo 718322 11095649 := bstep (se 2 (by rfl) ⟨4160868, by rfl⟩ : syracuseStep 11095649 = 8321737) B8321737
theorem B5459723 : Blo 718322 5459723 := bstep (se 1 (by rfl) ⟨4094792, by rfl⟩ : syracuseStep 5459723 = 8189585) B8189585
theorem B13881131 : Blo 718322 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B1823087 : Blo 718322 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B971131 : Blo 718322 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B35508725 : Blo 718322 35508725 := bstep (se 5 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 35508725 = 3328943) B3328943
theorem B5854031 : Blo 718322 5854031 := bstep (se 1 (by rfl) ⟨4390523, by rfl⟩ : syracuseStep 5854031 = 8781047) B8781047
theorem B1823735 : Blo 718322 1823735 := bstep (se 1 (by rfl) ⟨1367801, by rfl⟩ : syracuseStep 1823735 = 2735603) B2735603
theorem B1823867 : Blo 718322 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B808231 : Blo 718322 808231 := bstep (se 1 (by rfl) ⟨606173, by rfl⟩ : syracuseStep 808231 = 1212347) B1212347
theorem B808303 : Blo 718322 808303 := bstep (se 1 (by rfl) ⟨606227, by rfl⟩ : syracuseStep 808303 = 1212455) B1212455
theorem B808519 : Blo 718322 808519 := bstep (se 1 (by rfl) ⟨606389, by rfl⟩ : syracuseStep 808519 = 1212779) B1212779
theorem B1365599 : Blo 718322 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B1726415 : Blo 718322 1726415 := bstep (se 1 (by rfl) ⟨1294811, by rfl⟩ : syracuseStep 1726415 = 2589623) B2589623
theorem B2742407 : Blo 718322 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B809383 : Blo 718322 809383 := bstep (se 1 (by rfl) ⟨607037, by rfl⟩ : syracuseStep 809383 = 1214075) B1214075
theorem B3463901 : Blo 718322 3463901 := bstep (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) B1298963
theorem B1825679 : Blo 718322 1825679 := bstep (se 1 (by rfl) ⟨1369259, by rfl⟩ : syracuseStep 1825679 = 2738519) B2738519
theorem B809959 : Blo 718322 809959 := bstep (se 1 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 809959 = 1214939) B1214939
theorem B3890315 : Blo 718322 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B1727867 : Blo 718322 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B1826185 : Blo 718322 1826185 := bstep (se 2 (by rfl) ⟨684819, by rfl⟩ : syracuseStep 1826185 = 1369639) B1369639
theorem B14015959 : Blo 718322 14015959 := bstep (se 1 (by rfl) ⟨10511969, by rfl⟩ : syracuseStep 14015959 = 21023939) B21023939
theorem B1826297 : Blo 718322 1826297 := bstep (se 2 (by rfl) ⟨684861, by rfl⟩ : syracuseStep 1826297 = 1369723) B1369723
theorem B5463611 : Blo 718322 5463611 := bstep (se 1 (by rfl) ⟨4097708, by rfl⟩ : syracuseStep 5463611 = 8195417) B8195417
theorem B6151895 : Blo 718322 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B13852457 : Blo 718322 13852457 := bstep (se 2 (by rfl) ⟨5194671, by rfl⟩ : syracuseStep 13852457 = 10389343) B10389343
theorem B3694409 : Blo 718322 3694409 := bstep (se 2 (by rfl) ⟨1385403, by rfl⟩ : syracuseStep 3694409 = 2770807) B2770807
theorem B2187137 : Blo 718322 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B1826945 : Blo 718322 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B1728875 : Blo 718322 1728875 := bstep (se 1 (by rfl) ⟨1296656, by rfl⟩ : syracuseStep 1728875 = 2593313) B2593313
theorem B7791011 : Blo 718322 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B6578633 : Blo 718322 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B811615 : Blo 718322 811615 := bstep (se 1 (by rfl) ⟨608711, by rfl⟩ : syracuseStep 811615 = 1217423) B1217423
theorem B1368751 : Blo 718322 1368751 := bstep (se 1 (by rfl) ⟨1026563, by rfl⟩ : syracuseStep 1368751 = 2053127) B2053127
theorem B6578891 : Blo 718322 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B1827755 : Blo 718322 1827755 := bstep (se 1 (by rfl) ⟨1370816, by rfl⟩ : syracuseStep 1827755 = 2741633) B2741633
theorem B1041695 : Blo 718322 1041695 := bstep (se 1 (by rfl) ⟨781271, by rfl⟩ : syracuseStep 1041695 = 1562543) B1562543
theorem B910703 : Blo 718322 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B8185211 : Blo 718322 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B3073403 : Blo 718322 3073403 := bstep (se 1 (by rfl) ⟨2305052, by rfl⟩ : syracuseStep 3073403 = 4610105) B4610105
theorem B910759 : Blo 718322 910759 := bstep (se 1 (by rfl) ⟨683069, by rfl⟩ : syracuseStep 910759 = 1366139) B1366139
theorem B911083 : Blo 718322 911083 := bstep (se 1 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 911083 = 1366625) B1366625
theorem B1370459 : Blo 718322 1370459 := bstep (se 1 (by rfl) ⟨1027844, by rfl⟩ : syracuseStep 1370459 = 2055689) B2055689
theorem B1370695 : Blo 718322 1370695 := bstep (se 1 (by rfl) ⟨1028021, by rfl⟩ : syracuseStep 1370695 = 2056043) B2056043
theorem B912055 : Blo 718322 912055 := bstep (se 1 (by rfl) ⟨684041, by rfl⟩ : syracuseStep 912055 = 1368083) B1368083
theorem B3075059 : Blo 718322 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B1534967 : Blo 718322 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B1732481 : Blo 718322 1732481 := bstep (se 2 (by rfl) ⟨649680, by rfl⟩ : syracuseStep 1732481 = 1299361) B1299361
theorem B2191369 : Blo 718322 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B1077671 : Blo 718322 1077671 := bstep (se 1 (by rfl) ⟨808253, by rfl⟩ : syracuseStep 1077671 = 1616507) B1616507
theorem B1077755 : Blo 718322 1077755 := bstep (se 1 (by rfl) ⟨808316, by rfl⟩ : syracuseStep 1077755 = 1616633) B1616633
theorem B1077881 : Blo 718322 1077881 := bstep (se 2 (by rfl) ⟨404205, by rfl⟩ : syracuseStep 1077881 = 808411) B808411
theorem B1077935 : Blo 718322 1077935 := bstep (se 1 (by rfl) ⟨808451, by rfl⟩ : syracuseStep 1077935 = 1616903) B1616903
theorem B914095 : Blo 718322 914095 := bstep (se 1 (by rfl) ⟨685571, by rfl⟩ : syracuseStep 914095 = 1371143) B1371143
theorem B1077983 : Blo 718322 1077983 := bstep (se 1 (by rfl) ⟨808487, by rfl⟩ : syracuseStep 1077983 = 1616975) B1616975
theorem B6583007 : Blo 718322 6583007 := bstep (se 1 (by rfl) ⟨4937255, by rfl⟩ : syracuseStep 6583007 = 9874511) B9874511
theorem B3076973 : Blo 718322 3076973 := bstep (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) B1153865
theorem B1078247 : Blo 718322 1078247 := bstep (se 1 (by rfl) ⟨808685, by rfl⟩ : syracuseStep 1078247 = 1617371) B1617371
theorem B1078505 : Blo 718322 1078505 := bstep (se 2 (by rfl) ⟨404439, by rfl⟩ : syracuseStep 1078505 = 808879) B808879
theorem B1078559 : Blo 718322 1078559 := bstep (se 1 (by rfl) ⟨808919, by rfl⟩ : syracuseStep 1078559 = 1617839) B1617839
theorem B1078727 : Blo 718322 1078727 := bstep (se 1 (by rfl) ⟨809045, by rfl⟩ : syracuseStep 1078727 = 1618091) B1618091
theorem B718331 : Blo 718322 718331 := bstep (se 1 (by rfl) ⟨538748, by rfl⟩ : syracuseStep 718331 = 1077497) B1077497
theorem B718399 : Blo 718322 718399 := bstep (se 1 (by rfl) ⟨538799, by rfl⟩ : syracuseStep 718399 = 1077599) B1077599
theorem B718407 : Blo 718322 718407 := bstep (se 1 (by rfl) ⟨538805, by rfl⟩ : syracuseStep 718407 = 1077611) B1077611
theorem B718559 : Blo 718322 718559 := bstep (se 1 (by rfl) ⟨538919, by rfl⟩ : syracuseStep 718559 = 1077839) B1077839
theorem B1079081 : Blo 718322 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B718639 : Blo 718322 718639 := bstep (se 1 (by rfl) ⟨538979, by rfl⟩ : syracuseStep 718639 = 1077959) B1077959
theorem B1079087 : Blo 718322 1079087 := bstep (se 1 (by rfl) ⟨809315, by rfl⟩ : syracuseStep 1079087 = 1618631) B1618631
theorem B718747 : Blo 718322 718747 := bstep (se 1 (by rfl) ⟨539060, by rfl⟩ : syracuseStep 718747 = 1078121) B1078121
theorem B718799 : Blo 718322 718799 := bstep (se 1 (by rfl) ⟨539099, by rfl⟩ : syracuseStep 718799 = 1078199) B1078199
theorem B718823 : Blo 718322 718823 := bstep (se 1 (by rfl) ⟨539117, by rfl⟩ : syracuseStep 718823 = 1078235) B1078235
theorem B76904549 : Blo 718322 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B106854551 : Blo 718322 106854551 := bstep (se 1 (by rfl) ⟨80140913, by rfl⟩ : syracuseStep 106854551 = 160281827) B160281827
theorem B1079561 : Blo 718322 1079561 := bstep (se 2 (by rfl) ⟨404835, by rfl⟩ : syracuseStep 1079561 = 809671) B809671
theorem B5830937 : Blo 718322 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B3897629 : Blo 718322 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B719135 : Blo 718322 719135 := bstep (se 1 (by rfl) ⟨539351, by rfl⟩ : syracuseStep 719135 = 1078703) B1078703
theorem B719195 : Blo 718322 719195 := bstep (se 1 (by rfl) ⟨539396, by rfl⟩ : syracuseStep 719195 = 1078793) B1078793
theorem B719215 : Blo 718322 719215 := bstep (se 1 (by rfl) ⟨539411, by rfl⟩ : syracuseStep 719215 = 1078823) B1078823
theorem B1079663 : Blo 718322 1079663 := bstep (se 1 (by rfl) ⟨809747, by rfl⟩ : syracuseStep 1079663 = 1619495) B1619495
theorem B719271 : Blo 718322 719271 := bstep (se 1 (by rfl) ⟨539453, by rfl⟩ : syracuseStep 719271 = 1078907) B1078907
theorem B1735123 : Blo 718322 1735123 := bstep (se 1 (by rfl) ⟨1301342, by rfl⟩ : syracuseStep 1735123 = 2602685) B2602685
theorem B719355 : Blo 718322 719355 := bstep (se 1 (by rfl) ⟨539516, by rfl⟩ : syracuseStep 719355 = 1079033) B1079033
theorem B719423 : Blo 718322 719423 := bstep (se 1 (by rfl) ⟨539567, by rfl⟩ : syracuseStep 719423 = 1079135) B1079135
theorem B1538623 : Blo 718322 1538623 := bstep (se 1 (by rfl) ⟨1153967, by rfl⟩ : syracuseStep 1538623 = 2307935) B2307935
theorem B27753029 : Blo 718322 27753029 := bstep (se 4 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 27753029 = 5203693) B5203693
theorem B719431 : Blo 718322 719431 := bstep (se 1 (by rfl) ⟨539573, by rfl⟩ : syracuseStep 719431 = 1079147) B1079147
theorem B1079879 : Blo 718322 1079879 := bstep (se 1 (by rfl) ⟨809909, by rfl⟩ : syracuseStep 1079879 = 1619819) B1619819
theorem B1079915 : Blo 718322 1079915 := bstep (se 1 (by rfl) ⟨809936, by rfl⟩ : syracuseStep 1079915 = 1619873) B1619873
theorem B719583 : Blo 718322 719583 := bstep (se 1 (by rfl) ⟨539687, by rfl⟩ : syracuseStep 719583 = 1079375) B1079375
theorem B719663 : Blo 718322 719663 := bstep (se 1 (by rfl) ⟨539747, by rfl⟩ : syracuseStep 719663 = 1079495) B1079495
theorem B1080143 : Blo 718322 1080143 := bstep (se 1 (by rfl) ⟨810107, by rfl⟩ : syracuseStep 1080143 = 1620215) B1620215
theorem B3701629 : Blo 718322 3701629 := bstep (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) B1388111
theorem B719771 : Blo 718322 719771 := bstep (se 1 (by rfl) ⟨539828, by rfl⟩ : syracuseStep 719771 = 1079657) B1079657
theorem B719823 : Blo 718322 719823 := bstep (se 1 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 719823 = 1079735) B1079735
theorem B719847 : Blo 718322 719847 := bstep (se 1 (by rfl) ⟨539885, by rfl⟩ : syracuseStep 719847 = 1079771) B1079771
theorem B1080539 : Blo 718322 1080539 := bstep (se 1 (by rfl) ⟨810404, by rfl⟩ : syracuseStep 1080539 = 1620809) B1620809
theorem B5831909 : Blo 718322 5831909 := bstep (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) B1093483
theorem B720159 : Blo 718322 720159 := bstep (se 1 (by rfl) ⟨540119, by rfl⟩ : syracuseStep 720159 = 1080239) B1080239
theorem B20774177 : Blo 718322 20774177 := bstep (se 2 (by rfl) ⟨7790316, by rfl⟩ : syracuseStep 20774177 = 15580633) B15580633
theorem B720219 : Blo 718322 720219 := bstep (se 1 (by rfl) ⟨540164, by rfl⟩ : syracuseStep 720219 = 1080329) B1080329
theorem B720239 : Blo 718322 720239 := bstep (se 1 (by rfl) ⟨540179, by rfl⟩ : syracuseStep 720239 = 1080359) B1080359
theorem B1080713 : Blo 718322 1080713 := bstep (se 2 (by rfl) ⟨405267, by rfl⟩ : syracuseStep 1080713 = 810535) B810535
theorem B720295 : Blo 718322 720295 := bstep (se 1 (by rfl) ⟨540221, by rfl⟩ : syracuseStep 720295 = 1080443) B1080443
theorem B720379 : Blo 718322 720379 := bstep (se 1 (by rfl) ⟨540284, by rfl⟩ : syracuseStep 720379 = 1080569) B1080569
theorem B1539641 : Blo 718322 1539641 := bstep (se 2 (by rfl) ⟨577365, by rfl⟩ : syracuseStep 1539641 = 1154731) B1154731
theorem B720447 : Blo 718322 720447 := bstep (se 1 (by rfl) ⟨540335, by rfl⟩ : syracuseStep 720447 = 1080671) B1080671
theorem B720455 : Blo 718322 720455 := bstep (se 1 (by rfl) ⟨540341, by rfl⟩ : syracuseStep 720455 = 1080683) B1080683
theorem B2915921 : Blo 718322 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B3079775 : Blo 718322 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B720607 : Blo 718322 720607 := bstep (se 1 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 720607 = 1080911) B1080911
theorem B1081067 : Blo 718322 1081067 := bstep (se 1 (by rfl) ⟨810800, by rfl⟩ : syracuseStep 1081067 = 1621601) B1621601
theorem B720687 : Blo 718322 720687 := bstep (se 1 (by rfl) ⟨540515, by rfl⟩ : syracuseStep 720687 = 1081031) B1081031
theorem B6586219 : Blo 718322 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B720795 : Blo 718322 720795 := bstep (se 1 (by rfl) ⟨540596, by rfl⟩ : syracuseStep 720795 = 1081193) B1081193
theorem B1212367 : Blo 718322 1212367 := bstep (se 1 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 1212367 = 1818551) B1818551
theorem B720847 : Blo 718322 720847 := bstep (se 1 (by rfl) ⟨540635, by rfl⟩ : syracuseStep 720847 = 1081271) B1081271
theorem B1081295 : Blo 718322 1081295 := bstep (se 1 (by rfl) ⟨810971, by rfl⟩ : syracuseStep 1081295 = 1621943) B1621943
theorem B720871 : Blo 718322 720871 := bstep (se 1 (by rfl) ⟨540653, by rfl⟩ : syracuseStep 720871 = 1081307) B1081307
theorem B721127 : Blo 718322 721127 := bstep (se 1 (by rfl) ⟨540845, by rfl⟩ : syracuseStep 721127 = 1081691) B1081691
theorem B1081631 : Blo 718322 1081631 := bstep (se 1 (by rfl) ⟨811223, by rfl⟩ : syracuseStep 1081631 = 1622447) B1622447
theorem B1081655 : Blo 718322 1081655 := bstep (se 1 (by rfl) ⟨811241, by rfl⟩ : syracuseStep 1081655 = 1622483) B1622483
theorem B2589047 : Blo 718322 2589047 := bstep (se 1 (by rfl) ⟨1941785, by rfl⟩ : syracuseStep 2589047 = 3883571) B3883571
theorem B1212799 : Blo 718322 1212799 := bstep (se 1 (by rfl) ⟨909599, by rfl⟩ : syracuseStep 1212799 = 1819199) B1819199
theorem B1081727 : Blo 718322 1081727 := bstep (se 1 (by rfl) ⟨811295, by rfl⟩ : syracuseStep 1081727 = 1622591) B1622591
theorem B721279 : Blo 718322 721279 := bstep (se 1 (by rfl) ⟨540959, by rfl⟩ : syracuseStep 721279 = 1081919) B1081919
theorem B1081799 : Blo 718322 1081799 := bstep (se 1 (by rfl) ⟨811349, by rfl⟩ : syracuseStep 1081799 = 1622699) B1622699
theorem B721359 : Blo 718322 721359 := bstep (se 1 (by rfl) ⟨541019, by rfl⟩ : syracuseStep 721359 = 1082039) B1082039
theorem B3080699 : Blo 718322 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B950887 : Blo 718322 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B721511 : Blo 718322 721511 := bstep (se 1 (by rfl) ⟨541133, by rfl⟩ : syracuseStep 721511 = 1082267) B1082267
theorem B4620995 : Blo 718322 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B1082153 : Blo 718322 1082153 := bstep (se 2 (by rfl) ⟨405807, by rfl⟩ : syracuseStep 1082153 = 811615) B811615
theorem B1213231 : Blo 718322 1213231 := bstep (se 1 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 1213231 = 1819847) B1819847
theorem B1082159 : Blo 718322 1082159 := bstep (se 1 (by rfl) ⟨811619, by rfl⟩ : syracuseStep 1082159 = 1623239) B1623239
theorem B721775 : Blo 718322 721775 := bstep (se 1 (by rfl) ⟨541331, by rfl⟩ : syracuseStep 721775 = 1082663) B1082663
theorem B1082279 : Blo 718322 1082279 := bstep (se 1 (by rfl) ⟨811709, by rfl⟩ : syracuseStep 1082279 = 1623419) B1623419
theorem B721831 : Blo 718322 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B1082363 : Blo 718322 1082363 := bstep (se 1 (by rfl) ⟨811772, by rfl⟩ : syracuseStep 1082363 = 1623545) B1623545
theorem B721915 : Blo 718322 721915 := bstep (se 1 (by rfl) ⟨541436, by rfl⟩ : syracuseStep 721915 = 1082873) B1082873
theorem B1082423 : Blo 718322 1082423 := bstep (se 1 (by rfl) ⟨811817, by rfl⟩ : syracuseStep 1082423 = 1623635) B1623635
theorem B721983 : Blo 718322 721983 := bstep (se 1 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 721983 = 1082975) B1082975
theorem B1082543 : Blo 718322 1082543 := bstep (se 1 (by rfl) ⟨811907, by rfl⟩ : syracuseStep 1082543 = 1623815) B1623815
theorem B722127 : Blo 718322 722127 := bstep (se 1 (by rfl) ⟨541595, by rfl⟩ : syracuseStep 722127 = 1083191) B1083191
theorem B8226035 : Blo 718322 8226035 := bstep (se 1 (by rfl) ⟨6169526, by rfl⟩ : syracuseStep 8226035 = 12339053) B12339053
theorem B2426219 : Blo 718322 2426219 := bstep (se 1 (by rfl) ⟨1819664, by rfl⟩ : syracuseStep 2426219 = 3639329) B3639329
theorem B2426327 : Blo 718322 2426327 := bstep (se 1 (by rfl) ⟨1819745, by rfl⟩ : syracuseStep 2426327 = 3639491) B3639491
theorem B4097573 : Blo 718322 4097573 := bstep (se 4 (by rfl) ⟨384147, by rfl⟩ : syracuseStep 4097573 = 768295) B768295
theorem B1082951 : Blo 718322 1082951 := bstep (se 1 (by rfl) ⟨812213, by rfl⟩ : syracuseStep 1082951 = 1624427) B1624427
theorem B2426489 : Blo 718322 2426489 := bstep (se 2 (by rfl) ⟨909933, by rfl⟩ : syracuseStep 2426489 = 1819867) B1819867
theorem B1083047 : Blo 718322 1083047 := bstep (se 1 (by rfl) ⟨812285, by rfl⟩ : syracuseStep 1083047 = 1624571) B1624571
theorem B1214203 : Blo 718322 1214203 := bstep (se 1 (by rfl) ⟨910652, by rfl⟩ : syracuseStep 1214203 = 1821305) B1821305
theorem B1083131 : Blo 718322 1083131 := bstep (se 1 (by rfl) ⟨812348, by rfl⟩ : syracuseStep 1083131 = 1624697) B1624697
theorem B1083167 : Blo 718322 1083167 := bstep (se 1 (by rfl) ⟨812375, by rfl⟩ : syracuseStep 1083167 = 1624751) B1624751
theorem B1083215 : Blo 718322 1083215 := bstep (se 1 (by rfl) ⟨812411, by rfl⟩ : syracuseStep 1083215 = 1624823) B1624823
theorem B1214345 : Blo 718322 1214345 := bstep (se 2 (by rfl) ⟨455379, by rfl⟩ : syracuseStep 1214345 = 910759) B910759
theorem B1083335 : Blo 718322 1083335 := bstep (se 1 (by rfl) ⟨812501, by rfl⟩ : syracuseStep 1083335 = 1625003) B1625003
theorem B3082475 : Blo 718322 3082475 := bstep (se 1 (by rfl) ⟨2311856, by rfl⟩ : syracuseStep 3082475 = 4623713) B4623713
theorem B1214777 : Blo 718322 1214777 := bstep (se 2 (by rfl) ⟨455541, by rfl⟩ : syracuseStep 1214777 = 911083) B911083
theorem B3639815 : Blo 718322 3639815 := bstep (se 1 (by rfl) ⟨2729861, by rfl⟩ : syracuseStep 3639815 = 5459723) B5459723
theorem B1215391 : Blo 718322 1215391 := bstep (se 1 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 1215391 = 1823087) B1823087
theorem B11111413 : Blo 718322 11111413 := bstep (se 5 (by rfl) ⟨520847, by rfl⟩ : syracuseStep 11111413 = 1041695) B1041695
theorem B2428001 : Blo 718322 2428001 := bstep (se 2 (by rfl) ⟨910500, by rfl⟩ : syracuseStep 2428001 = 1821001) B1821001
theorem B3902687 : Blo 718322 3902687 := bstep (se 1 (by rfl) ⟨2927015, by rfl⟩ : syracuseStep 3902687 = 5854031) B5854031
theorem B1215823 : Blo 718322 1215823 := bstep (se 1 (by rfl) ⟨911867, by rfl⟩ : syracuseStep 1215823 = 1823735) B1823735
theorem B1215911 : Blo 718322 1215911 := bstep (se 1 (by rfl) ⟨911933, by rfl⟩ : syracuseStep 1215911 = 1823867) B1823867
theorem B5180921 : Blo 718322 5180921 := bstep (se 2 (by rfl) ⟨1942845, by rfl⟩ : syracuseStep 5180921 = 3885691) B3885691
theorem B1216073 : Blo 718322 1216073 := bstep (se 2 (by rfl) ⟨456027, by rfl⟩ : syracuseStep 1216073 = 912055) B912055
theorem B2428541 : Blo 718322 2428541 := bstep (se 3 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 2428541 = 910703) B910703
theorem B2428811 : Blo 718322 2428811 := bstep (se 1 (by rfl) ⟨1821608, by rfl⟩ : syracuseStep 2428811 = 3643217) B3643217
theorem B1150943 : Blo 718322 1150943 := bstep (se 1 (by rfl) ⟨863207, by rfl⟩ : syracuseStep 1150943 = 1726415) B1726415
theorem B3641597 : Blo 718322 3641597 := bstep (se 3 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 3641597 = 1365599) B1365599
theorem B2429351 : Blo 718322 2429351 := bstep (se 1 (by rfl) ⟨1822013, by rfl⟩ : syracuseStep 2429351 = 3644027) B3644027
theorem B1217119 : Blo 718322 1217119 := bstep (se 1 (by rfl) ⟨912839, by rfl⟩ : syracuseStep 1217119 = 1825679) B1825679
theorem B2593543 : Blo 718322 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B3937085 : Blo 718322 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B6165395 : Blo 718322 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B1151911 : Blo 718322 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B1217531 : Blo 718322 1217531 := bstep (se 1 (by rfl) ⟨913148, by rfl⟩ : syracuseStep 1217531 = 1826297) B1826297
theorem B3642407 : Blo 718322 3642407 := bstep (se 1 (by rfl) ⟨2731805, by rfl⟩ : syracuseStep 3642407 = 5463611) B5463611
theorem B4101263 : Blo 718322 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B2462939 : Blo 718322 2462939 := bstep (se 1 (by rfl) ⟨1847204, by rfl⟩ : syracuseStep 2462939 = 3694409) B3694409
theorem B1774867 : Blo 718322 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B2921825 : Blo 718322 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B1217963 : Blo 718322 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B15832493 : Blo 718322 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B2430647 : Blo 718322 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B1218503 : Blo 718322 1218503 := bstep (se 1 (by rfl) ⟨913877, by rfl⟩ : syracuseStep 1218503 = 1827755) B1827755
theorem B1218793 : Blo 718322 1218793 := bstep (se 2 (by rfl) ⟨457047, by rfl⟩ : syracuseStep 1218793 = 914095) B914095
theorem B6166793 : Blo 718322 6166793 := bstep (se 2 (by rfl) ⟨2312547, by rfl⟩ : syracuseStep 6166793 = 4625095) B4625095
theorem B2431835 : Blo 718322 2431835 := bstep (se 1 (by rfl) ⟨1823876, by rfl⟩ : syracuseStep 2431835 = 3647753) B3647753
theorem B924895 : Blo 718322 924895 := bstep (se 1 (by rfl) ⟨693671, by rfl⟩ : syracuseStep 924895 = 1387343) B1387343
theorem B1023311 : Blo 718322 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B2432591 : Blo 718322 2432591 := bstep (se 1 (by rfl) ⟨1824443, by rfl⟩ : syracuseStep 2432591 = 3648887) B3648887
theorem B2432699 : Blo 718322 2432699 := bstep (se 1 (by rfl) ⟨1824524, by rfl⟩ : syracuseStep 2432699 = 3649049) B3649049
theorem B74751781 : Blo 718322 74751781 := bstep (se 4 (by rfl) ⟨7007979, by rfl⟩ : syracuseStep 74751781 = 14015959) B14015959
theorem B1154987 : Blo 718322 1154987 := bstep (se 1 (by rfl) ⟨866240, by rfl⟩ : syracuseStep 1154987 = 1732481) B1732481
theorem B2598419 : Blo 718322 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B2434643 : Blo 718322 2434643 := bstep (se 1 (by rfl) ⟨1825982, by rfl⟩ : syracuseStep 2434643 = 3651965) B3651965
theorem B2631503 : Blo 718322 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B1386319 : Blo 718322 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B8529761 : Blo 718322 8529761 := bstep (se 2 (by rfl) ⟨3198660, by rfl⟩ : syracuseStep 8529761 = 6397321) B6397321
theorem B2434913 : Blo 718322 2434913 := bstep (se 2 (by rfl) ⟨913092, by rfl⟩ : syracuseStep 2434913 = 1826185) B1826185
theorem B4925431 : Blo 718322 4925431 := bstep (se 1 (by rfl) ⟨3694073, by rfl⟩ : syracuseStep 4925431 = 7388147) B7388147
theorem B1026427 : Blo 718322 1026427 := bstep (se 1 (by rfl) ⟨769820, by rfl⟩ : syracuseStep 1026427 = 1539641) B1539641
theorem B1943947 : Blo 718322 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B8202707 : Blo 718322 8202707 := bstep (se 1 (by rfl) ⟨6152030, by rfl⟩ : syracuseStep 8202707 = 12304061) B12304061
theorem B2435615 : Blo 718322 2435615 := bstep (se 1 (by rfl) ⟨1826711, by rfl⟩ : syracuseStep 2435615 = 3653423) B3653423
theorem B1616489 : Blo 718322 1616489 := bstep (se 2 (by rfl) ⟨606183, by rfl⟩ : syracuseStep 1616489 = 1212367) B1212367
theorem B19737539 : Blo 718322 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B2468839 : Blo 718322 2468839 := bstep (se 1 (by rfl) ⟨1851629, by rfl⟩ : syracuseStep 2468839 = 3703259) B3703259
theorem B1617119 : Blo 718322 1617119 := bstep (se 1 (by rfl) ⟨1212839, by rfl⟩ : syracuseStep 1617119 = 2425679) B2425679
theorem B2338073 : Blo 718322 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B1617335 : Blo 718322 1617335 := bstep (se 1 (by rfl) ⟨1213001, by rfl⟩ : syracuseStep 1617335 = 2426003) B2426003
theorem B2076155 : Blo 718322 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B1617515 : Blo 718322 1617515 := bstep (se 1 (by rfl) ⟨1213136, by rfl⟩ : syracuseStep 1617515 = 2426273) B2426273
theorem B8302445 : Blo 718322 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B1617785 : Blo 718322 1617785 := bstep (se 2 (by rfl) ⟨606669, by rfl⟩ : syracuseStep 1617785 = 1213339) B1213339
theorem B2437019 : Blo 718322 2437019 := bstep (se 1 (by rfl) ⟨1827764, by rfl⟩ : syracuseStep 2437019 = 3655529) B3655529
theorem B5189683 : Blo 718322 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B4108553 : Blo 718322 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B3649859 : Blo 718322 3649859 := bstep (se 1 (by rfl) ⟨2737394, by rfl⟩ : syracuseStep 3649859 = 5474789) B5474789
theorem B2306807 : Blo 718322 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B9254087 : Blo 718322 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B4109555 : Blo 718322 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B23672483 : Blo 718322 23672483 := bstep (se 1 (by rfl) ⟨17754362, by rfl⟩ : syracuseStep 23672483 = 35508725) B35508725
theorem B1619639 : Blo 718322 1619639 := bstep (se 1 (by rfl) ⟨1214729, by rfl⟩ : syracuseStep 1619639 = 2429459) B2429459
theorem B9221849 : Blo 718322 9221849 := bstep (se 2 (by rfl) ⟨3458193, by rfl⟩ : syracuseStep 9221849 = 6916387) B6916387
theorem B2733871 : Blo 718322 2733871 := bstep (se 1 (by rfl) ⟨2050403, by rfl⟩ : syracuseStep 2733871 = 4100807) B4100807
theorem B10401851 : Blo 718322 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B15775859 : Blo 718322 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B2734343 : Blo 718322 2734343 := bstep (se 1 (by rfl) ⟨2050757, by rfl⟩ : syracuseStep 2734343 = 4101515) B4101515
theorem B1620827 : Blo 718322 1620827 := bstep (se 1 (by rfl) ⟨1215620, by rfl⟩ : syracuseStep 1620827 = 2431241) B2431241
theorem B2309267 : Blo 718322 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B6143147 : Blo 718322 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B4111721 : Blo 718322 4111721 := bstep (se 2 (by rfl) ⟨1541895, by rfl⟩ : syracuseStep 4111721 = 3083791) B3083791
theorem B1621583 : Blo 718322 1621583 := bstep (se 1 (by rfl) ⟨1216187, by rfl⟩ : syracuseStep 1621583 = 2432375) B2432375
theorem B1818359 : Blo 718322 1818359 := bstep (se 1 (by rfl) ⟨1363769, by rfl⟩ : syracuseStep 1818359 = 2727539) B2727539
theorem B1458091 : Blo 718322 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B5194007 : Blo 718322 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B1622303 : Blo 718322 1622303 := bstep (se 1 (by rfl) ⟨1216727, by rfl⟩ : syracuseStep 1622303 = 2433455) B2433455
theorem B3654071 : Blo 718322 3654071 := bstep (se 1 (by rfl) ⟨2740553, by rfl⟩ : syracuseStep 3654071 = 5481107) B5481107
theorem B1294841 : Blo 718322 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B1557295 : Blo 718322 1557295 := bstep (se 1 (by rfl) ⟨1167971, by rfl⟩ : syracuseStep 1557295 = 2335943) B2335943
theorem B3654557 : Blo 718322 3654557 := bstep (se 3 (by rfl) ⟨685229, by rfl⟩ : syracuseStep 3654557 = 1370459) B1370459
theorem B5456807 : Blo 718322 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B2048935 : Blo 718322 2048935 := bstep (se 1 (by rfl) ⟨1536701, by rfl⟩ : syracuseStep 2048935 = 3073403) B3073403
theorem B1622951 : Blo 718322 1622951 := bstep (se 1 (by rfl) ⟨1217213, by rfl⟩ : syracuseStep 1622951 = 2434427) B2434427
theorem B2737759 : Blo 718322 2737759 := bstep (se 1 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 2737759 = 4106639) B4106639
theorem B1820495 : Blo 718322 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B1623887 : Blo 718322 1623887 := bstep (se 1 (by rfl) ⟨1217915, by rfl⟩ : syracuseStep 1623887 = 2435831) B2435831
theorem B1623905 : Blo 718322 1623905 := bstep (se 2 (by rfl) ⟨608964, by rfl⟩ : syracuseStep 1623905 = 1217929) B1217929
theorem B2050039 : Blo 718322 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B1624481 : Blo 718322 1624481 := bstep (se 2 (by rfl) ⟨609180, by rfl⟩ : syracuseStep 1624481 = 1218361) B1218361
theorem B1624607 : Blo 718322 1624607 := bstep (se 1 (by rfl) ⟨1218455, by rfl⟩ : syracuseStep 1624607 = 2436911) B2436911
theorem B3656339 : Blo 718322 3656339 := bstep (se 1 (by rfl) ⟨2742254, by rfl⟩ : syracuseStep 3656339 = 5484509) B5484509
theorem B2051315 : Blo 718322 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B2313497 : Blo 718322 2313497 := bstep (se 2 (by rfl) ⟨867561, by rfl⟩ : syracuseStep 2313497 = 1735123) B1735123
theorem B2051497 : Blo 718322 2051497 := bstep (se 2 (by rfl) ⟨769311, by rfl⟩ : syracuseStep 2051497 = 1538623) B1538623
theorem B1822135 : Blo 718322 1822135 := bstep (se 1 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 1822135 = 2733203) B2733203
theorem B11652781 : Blo 718322 11652781 := bstep (se 3 (by rfl) ⟨2184896, by rfl⟩ : syracuseStep 11652781 = 4369793) B4369793
theorem B2740007 : Blo 718322 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B4935505 : Blo 718322 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B51269699 : Blo 718322 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B3887291 : Blo 718322 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B18502019 : Blo 718322 18502019 := bstep (se 1 (by rfl) ⟨13876514, by rfl⟩ : syracuseStep 18502019 = 27753029) B27753029
theorem B11653955 : Blo 718322 11653955 := bstep (se 1 (by rfl) ⟨8740466, by rfl⟩ : syracuseStep 11653955 = 17480933) B17480933
theorem B3887939 : Blo 718322 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B13849451 : Blo 718322 13849451 := bstep (se 1 (by rfl) ⟨10387088, by rfl⟩ : syracuseStep 13849451 = 20774177) B20774177
theorem B1299511 : Blo 718322 1299511 := bstep (se 1 (by rfl) ⟨974633, by rfl⟩ : syracuseStep 1299511 = 1949267) B1949267
theorem B2053183 : Blo 718322 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B1365167 : Blo 718322 1365167 := bstep (se 1 (by rfl) ⟨1023875, by rfl⟩ : syracuseStep 1365167 = 2047751) B2047751
theorem B808699 : Blo 718322 808699 := bstep (se 1 (by rfl) ⟨606524, by rfl⟩ : syracuseStep 808699 = 1213049) B1213049
theorem B808735 : Blo 718322 808735 := bstep (se 1 (by rfl) ⟨606551, by rfl⟩ : syracuseStep 808735 = 1213103) B1213103
theorem B17487731 : Blo 718322 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B1824727 : Blo 718322 1824727 := bstep (se 1 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 1824727 = 2737091) B2737091
theorem B3692639 : Blo 718322 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B4217027 : Blo 718322 4217027 := bstep (se 1 (by rfl) ⟨3162770, by rfl⟩ : syracuseStep 4217027 = 6325541) B6325541
theorem B75028679 : Blo 718322 75028679 := bstep (se 1 (by rfl) ⟨56271509, by rfl⟩ : syracuseStep 75028679 = 112543019) B112543019
theorem B1825001 : Blo 718322 1825001 := bstep (se 2 (by rfl) ⟨684375, by rfl⟩ : syracuseStep 1825001 = 1368751) B1368751
theorem B1825031 : Blo 718322 1825031 := bstep (se 1 (by rfl) ⟨1368773, by rfl⟩ : syracuseStep 1825031 = 2737547) B2737547
theorem B4610333 : Blo 718322 4610333 := bstep (se 3 (by rfl) ⟨864437, by rfl⟩ : syracuseStep 4610333 = 1728875) B1728875
theorem B8182295 : Blo 718322 8182295 := bstep (se 1 (by rfl) ⟨6136721, by rfl⟩ : syracuseStep 8182295 = 12273443) B12273443
theorem B3955499 : Blo 718322 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B29547341 : Blo 718322 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B809887 : Blo 718322 809887 := bstep (se 1 (by rfl) ⟨607415, by rfl⟩ : syracuseStep 809887 = 1214831) B1214831
theorem B810031 : Blo 718322 810031 := bstep (se 1 (by rfl) ⟨607523, by rfl⟩ : syracuseStep 810031 = 1215047) B1215047
theorem B1367111 : Blo 718322 1367111 := bstep (se 1 (by rfl) ⟨1025333, by rfl⟩ : syracuseStep 1367111 = 2050667) B2050667
theorem B810319 : Blo 718322 810319 := bstep (se 1 (by rfl) ⟨607739, by rfl⟩ : syracuseStep 810319 = 1215479) B1215479
theorem B1662439 : Blo 718322 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B3890663 : Blo 718322 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B1367695 : Blo 718322 1367695 := bstep (se 1 (by rfl) ⟨1025771, by rfl⟩ : syracuseStep 1367695 = 2051543) B2051543
theorem B7397099 : Blo 718322 7397099 := bstep (se 1 (by rfl) ⟨5547824, by rfl⟩ : syracuseStep 7397099 = 11095649) B11095649
theorem B810823 : Blo 718322 810823 := bstep (se 1 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 810823 = 1216235) B1216235
theorem B24993629 : Blo 718322 24993629 := bstep (se 3 (by rfl) ⟨4686305, by rfl⟩ : syracuseStep 24993629 = 9372611) B9372611
theorem B811471 : Blo 718322 811471 := bstep (se 1 (by rfl) ⟨608603, by rfl⟩ : syracuseStep 811471 = 1217207) B1217207
theorem B8217287 : Blo 718322 8217287 := bstep (se 1 (by rfl) ⟨6162965, by rfl⟩ : syracuseStep 8217287 = 12325931) B12325931
theorem B1827593 : Blo 718322 1827593 := bstep (se 2 (by rfl) ⟨685347, by rfl⟩ : syracuseStep 1827593 = 1370695) B1370695
theorem B4154267 : Blo 718322 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B812443 : Blo 718322 812443 := bstep (se 1 (by rfl) ⟨609332, by rfl⟩ : syracuseStep 812443 = 1218665) B1218665
theorem B1828271 : Blo 718322 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B4679993 : Blo 718322 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B23685605 : Blo 718322 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B9234971 : Blo 718322 9234971 := bstep (se 1 (by rfl) ⟨6926228, by rfl⟩ : syracuseStep 9234971 = 13852457) B13852457
theorem B2190007 : Blo 718322 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B4385755 : Blo 718322 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B3501191 : Blo 718322 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B4385927 : Blo 718322 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B3075641 : Blo 718322 3075641 := bstep (se 2 (by rfl) ⟨1153365, by rfl⟩ : syracuseStep 3075641 = 2306731) B2306731
theorem B1077641 : Blo 718322 1077641 := bstep (se 2 (by rfl) ⟨404115, by rfl⟩ : syracuseStep 1077641 = 808231) B808231
theorem B1077737 : Blo 718322 1077737 := bstep (se 2 (by rfl) ⟨404151, by rfl⟩ : syracuseStep 1077737 = 808303) B808303
theorem B1536607 : Blo 718322 1536607 := bstep (se 1 (by rfl) ⟨1152455, by rfl⟩ : syracuseStep 1536607 = 2304911) B2304911
theorem B1077863 : Blo 718322 1077863 := bstep (se 1 (by rfl) ⟨808397, by rfl⟩ : syracuseStep 1077863 = 1616795) B1616795
theorem B1077995 : Blo 718322 1077995 := bstep (se 1 (by rfl) ⟨808496, by rfl⟩ : syracuseStep 1077995 = 1616993) B1616993
theorem B1078025 : Blo 718322 1078025 := bstep (se 2 (by rfl) ⟨404259, by rfl⟩ : syracuseStep 1078025 = 808519) B808519
theorem B4092767 : Blo 718322 4092767 := bstep (se 1 (by rfl) ⟨3069575, by rfl⟩ : syracuseStep 4092767 = 6139151) B6139151
theorem B1078127 : Blo 718322 1078127 := bstep (se 1 (by rfl) ⟨808595, by rfl⟩ : syracuseStep 1078127 = 1617191) B1617191
theorem B1078379 : Blo 718322 1078379 := bstep (se 1 (by rfl) ⟨808784, by rfl⟩ : syracuseStep 1078379 = 1617569) B1617569
theorem B1078619 : Blo 718322 1078619 := bstep (se 1 (by rfl) ⟨808964, by rfl⟩ : syracuseStep 1078619 = 1617929) B1617929
theorem B718447 : Blo 718322 718447 := bstep (se 1 (by rfl) ⟨538835, by rfl⟩ : syracuseStep 718447 = 1077671) B1077671
theorem B1078895 : Blo 718322 1078895 := bstep (se 1 (by rfl) ⟨809171, by rfl⟩ : syracuseStep 1078895 = 1618343) B1618343
theorem B718503 : Blo 718322 718503 := bstep (se 1 (by rfl) ⟨538877, by rfl⟩ : syracuseStep 718503 = 1077755) B1077755
theorem B1078967 : Blo 718322 1078967 := bstep (se 1 (by rfl) ⟨809225, by rfl⟩ : syracuseStep 1078967 = 1618451) B1618451
theorem B1079003 : Blo 718322 1079003 := bstep (se 1 (by rfl) ⟨809252, by rfl⟩ : syracuseStep 1079003 = 1618505) B1618505
theorem B718587 : Blo 718322 718587 := bstep (se 1 (by rfl) ⟨538940, by rfl⟩ : syracuseStep 718587 = 1077881) B1077881
theorem B718623 : Blo 718322 718623 := bstep (se 1 (by rfl) ⟨538967, by rfl⟩ : syracuseStep 718623 = 1077935) B1077935
theorem B718655 : Blo 718322 718655 := bstep (se 1 (by rfl) ⟨538991, by rfl⟩ : syracuseStep 718655 = 1077983) B1077983
theorem B4388671 : Blo 718322 4388671 := bstep (se 1 (by rfl) ⟨3291503, by rfl⟩ : syracuseStep 4388671 = 6583007) B6583007
theorem B1079177 : Blo 718322 1079177 := bstep (se 2 (by rfl) ⟨404691, by rfl⟩ : syracuseStep 1079177 = 809383) B809383
theorem B718831 : Blo 718322 718831 := bstep (se 1 (by rfl) ⟨539123, by rfl⟩ : syracuseStep 718831 = 1078247) B1078247
theorem B1079279 : Blo 718322 1079279 := bstep (se 1 (by rfl) ⟨809459, by rfl⟩ : syracuseStep 1079279 = 1618919) B1618919
theorem B3471457 : Blo 718322 3471457 := bstep (se 2 (by rfl) ⟨1301796, by rfl⟩ : syracuseStep 3471457 = 2603593) B2603593
theorem B719003 : Blo 718322 719003 := bstep (se 1 (by rfl) ⟨539252, by rfl⟩ : syracuseStep 719003 = 1078505) B1078505
theorem B719039 : Blo 718322 719039 := bstep (se 1 (by rfl) ⟨539279, by rfl⟩ : syracuseStep 719039 = 1078559) B1078559
theorem B1538281 : Blo 718322 1538281 := bstep (se 2 (by rfl) ⟨576855, by rfl⟩ : syracuseStep 1538281 = 1153711) B1153711
theorem B1079531 : Blo 718322 1079531 := bstep (se 1 (by rfl) ⟨809648, by rfl⟩ : syracuseStep 1079531 = 1619297) B1619297
theorem B1079591 : Blo 718322 1079591 := bstep (se 1 (by rfl) ⟨809693, by rfl⟩ : syracuseStep 1079591 = 1619387) B1619387
theorem B719151 : Blo 718322 719151 := bstep (se 1 (by rfl) ⟨539363, by rfl⟩ : syracuseStep 719151 = 1078727) B1078727
theorem B1079675 : Blo 718322 1079675 := bstep (se 1 (by rfl) ⟨809756, by rfl⟩ : syracuseStep 1079675 = 1619513) B1619513
theorem B719387 : Blo 718322 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B719391 : Blo 718322 719391 := bstep (se 1 (by rfl) ⟨539543, by rfl⟩ : syracuseStep 719391 = 1079087) B1079087
theorem B1079945 : Blo 718322 1079945 := bstep (se 2 (by rfl) ⟨404979, by rfl⟩ : syracuseStep 1079945 = 809959) B809959
theorem B71236367 : Blo 718322 71236367 := bstep (se 1 (by rfl) ⟨53427275, by rfl⟩ : syracuseStep 71236367 = 106854551) B106854551
theorem B1080119 : Blo 718322 1080119 := bstep (se 1 (by rfl) ⟨810089, by rfl⟩ : syracuseStep 1080119 = 1620179) B1620179
theorem B719707 : Blo 718322 719707 := bstep (se 1 (by rfl) ⟨539780, by rfl⟩ : syracuseStep 719707 = 1079561) B1079561
theorem B1080155 : Blo 718322 1080155 := bstep (se 1 (by rfl) ⟨810116, by rfl⟩ : syracuseStep 1080155 = 1620233) B1620233
theorem B719775 : Blo 718322 719775 := bstep (se 1 (by rfl) ⟨539831, by rfl⟩ : syracuseStep 719775 = 1079663) B1079663
theorem B1080299 : Blo 718322 1080299 := bstep (se 1 (by rfl) ⟨810224, by rfl⟩ : syracuseStep 1080299 = 1620449) B1620449
theorem B6913039 : Blo 718322 6913039 := bstep (se 1 (by rfl) ⟨5184779, by rfl⟩ : syracuseStep 6913039 = 10369559) B10369559
theorem B719919 : Blo 718322 719919 := bstep (se 1 (by rfl) ⟨539939, by rfl⟩ : syracuseStep 719919 = 1079879) B1079879
theorem B719943 : Blo 718322 719943 := bstep (se 1 (by rfl) ⟨539957, by rfl⟩ : syracuseStep 719943 = 1079915) B1079915
theorem B1080503 : Blo 718322 1080503 := bstep (se 1 (by rfl) ⟨810377, by rfl⟩ : syracuseStep 1080503 = 1620755) B1620755
theorem B720095 : Blo 718322 720095 := bstep (se 1 (by rfl) ⟨540071, by rfl⟩ : syracuseStep 720095 = 1080143) B1080143
theorem B3079417 : Blo 718322 3079417 := bstep (se 2 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 3079417 = 2309563) B2309563
theorem B3079433 : Blo 718322 3079433 := bstep (se 2 (by rfl) ⟨1154787, by rfl⟩ : syracuseStep 3079433 = 2309575) B2309575
theorem B1080743 : Blo 718322 1080743 := bstep (se 1 (by rfl) ⟨810557, by rfl⟩ : syracuseStep 1080743 = 1621115) B1621115
theorem B720359 : Blo 718322 720359 := bstep (se 1 (by rfl) ⟨540269, by rfl⟩ : syracuseStep 720359 = 1080539) B1080539
theorem B1080827 : Blo 718322 1080827 := bstep (se 1 (by rfl) ⟨810620, by rfl⟩ : syracuseStep 1080827 = 1621241) B1621241
theorem B720475 : Blo 718322 720475 := bstep (se 1 (by rfl) ⟨540356, by rfl⟩ : syracuseStep 720475 = 1080713) B1080713
theorem B1080923 : Blo 718322 1080923 := bstep (se 1 (by rfl) ⟨810692, by rfl⟩ : syracuseStep 1080923 = 1621385) B1621385
theorem B1081007 : Blo 718322 1081007 := bstep (se 1 (by rfl) ⟨810755, by rfl⟩ : syracuseStep 1081007 = 1621511) B1621511
theorem B2424545 : Blo 718322 2424545 := bstep (se 2 (by rfl) ⟨909204, by rfl⟩ : syracuseStep 2424545 = 1818409) B1818409
theorem B4620023 : Blo 718322 4620023 := bstep (se 1 (by rfl) ⟨3465017, by rfl⟩ : syracuseStep 4620023 = 6930035) B6930035
theorem B1081127 : Blo 718322 1081127 := bstep (se 1 (by rfl) ⟨810845, by rfl⟩ : syracuseStep 1081127 = 1621691) B1621691
theorem B8781625 : Blo 718322 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B720711 : Blo 718322 720711 := bstep (se 1 (by rfl) ⟨540533, by rfl⟩ : syracuseStep 720711 = 1081067) B1081067
theorem B1081211 : Blo 718322 1081211 := bstep (se 1 (by rfl) ⟨810908, by rfl⟩ : syracuseStep 1081211 = 1621817) B1621817
theorem B720863 : Blo 718322 720863 := bstep (se 1 (by rfl) ⟨540647, by rfl⟩ : syracuseStep 720863 = 1081295) B1081295
theorem B1081535 : Blo 718322 1081535 := bstep (se 1 (by rfl) ⟨811151, by rfl⟩ : syracuseStep 1081535 = 1622303) B1622303
theorem B721087 : Blo 718322 721087 := bstep (se 1 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 721087 = 1081631) B1081631
theorem B721103 : Blo 718322 721103 := bstep (se 1 (by rfl) ⟨540827, by rfl⟩ : syracuseStep 721103 = 1081655) B1081655
theorem B721151 : Blo 718322 721151 := bstep (se 1 (by rfl) ⟨540863, by rfl⟩ : syracuseStep 721151 = 1081727) B1081727
theorem B721199 : Blo 718322 721199 := bstep (se 1 (by rfl) ⟨540899, by rfl⟩ : syracuseStep 721199 = 1081799) B1081799
theorem B3080663 : Blo 718322 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B721435 : Blo 718322 721435 := bstep (se 1 (by rfl) ⟨541076, by rfl⟩ : syracuseStep 721435 = 1082153) B1082153
theorem B721439 : Blo 718322 721439 := bstep (se 1 (by rfl) ⟨541079, by rfl⟩ : syracuseStep 721439 = 1082159) B1082159
theorem B1081961 : Blo 718322 1081961 := bstep (se 2 (by rfl) ⟨405735, by rfl⟩ : syracuseStep 1081961 = 811471) B811471
theorem B3637871 : Blo 718322 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B1081967 : Blo 718322 1081967 := bstep (se 1 (by rfl) ⟨811475, by rfl⟩ : syracuseStep 1081967 = 1622951) B1622951
theorem B721519 : Blo 718322 721519 := bstep (se 1 (by rfl) ⟨541139, by rfl⟩ : syracuseStep 721519 = 1082279) B1082279
theorem B721575 : Blo 718322 721575 := bstep (se 1 (by rfl) ⟨541181, by rfl⟩ : syracuseStep 721575 = 1082363) B1082363
theorem B721615 : Blo 718322 721615 := bstep (se 1 (by rfl) ⟨541211, by rfl⟩ : syracuseStep 721615 = 1082423) B1082423
theorem B721695 : Blo 718322 721695 := bstep (se 1 (by rfl) ⟨541271, by rfl⟩ : syracuseStep 721695 = 1082543) B1082543
theorem B721967 : Blo 718322 721967 := bstep (se 1 (by rfl) ⟨541475, by rfl⟩ : syracuseStep 721967 = 1082951) B1082951
theorem B722031 : Blo 718322 722031 := bstep (se 1 (by rfl) ⟨541523, by rfl⟩ : syracuseStep 722031 = 1083047) B1083047
theorem B722087 : Blo 718322 722087 := bstep (se 1 (by rfl) ⟨541565, by rfl⟩ : syracuseStep 722087 = 1083131) B1083131
theorem B722111 : Blo 718322 722111 := bstep (se 1 (by rfl) ⟨541583, by rfl⟩ : syracuseStep 722111 = 1083167) B1083167
theorem B1213663 : Blo 718322 1213663 := bstep (se 1 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 1213663 = 1820495) B1820495
theorem B1082591 : Blo 718322 1082591 := bstep (se 1 (by rfl) ⟨811943, by rfl⟩ : syracuseStep 1082591 = 1623887) B1623887
theorem B722143 : Blo 718322 722143 := bstep (se 1 (by rfl) ⟨541607, by rfl⟩ : syracuseStep 722143 = 1083215) B1083215
theorem B1082603 : Blo 718322 1082603 := bstep (se 1 (by rfl) ⟨811952, by rfl⟩ : syracuseStep 1082603 = 1623905) B1623905
theorem B722223 : Blo 718322 722223 := bstep (se 1 (by rfl) ⟨541667, by rfl⟩ : syracuseStep 722223 = 1083335) B1083335
theorem B1082987 : Blo 718322 1082987 := bstep (se 1 (by rfl) ⟨812240, by rfl⟩ : syracuseStep 1082987 = 1624481) B1624481
theorem B2426543 : Blo 718322 2426543 := bstep (se 1 (by rfl) ⟨1819907, by rfl⟩ : syracuseStep 2426543 = 3639815) B3639815
theorem B1083071 : Blo 718322 1083071 := bstep (se 1 (by rfl) ⟨812303, by rfl⟩ : syracuseStep 1083071 = 1624607) B1624607
theorem B1083257 : Blo 718322 1083257 := bstep (se 2 (by rfl) ⟨406221, by rfl⟩ : syracuseStep 1083257 = 812443) B812443
theorem B1542331 : Blo 718322 1542331 := bstep (se 1 (by rfl) ⟨1156748, by rfl⟩ : syracuseStep 1542331 = 2313497) B2313497
theorem B11078045 : Blo 718322 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B2591527 : Blo 718322 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B2427731 : Blo 718322 2427731 := bstep (se 1 (by rfl) ⟨1820798, by rfl⟩ : syracuseStep 2427731 = 3641597) B3641597
theorem B2591929 : Blo 718322 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B2624723 : Blo 718322 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B7769303 : Blo 718322 7769303 := bstep (se 1 (by rfl) ⟨5826977, by rfl⟩ : syracuseStep 7769303 = 11653955) B11653955
theorem B2428271 : Blo 718322 2428271 := bstep (se 1 (by rfl) ⟨1821203, by rfl⟩ : syracuseStep 2428271 = 3642407) B3642407
theorem B1641959 : Blo 718322 1641959 := bstep (se 1 (by rfl) ⟨1231469, by rfl⟩ : syracuseStep 1641959 = 2462939) B2462939
theorem B10554995 : Blo 718322 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B14815217 : Blo 718322 14815217 := bstep (se 2 (by rfl) ⟨5555706, by rfl⟩ : syracuseStep 14815217 = 11111413) B11111413
theorem B2461759 : Blo 718322 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B1216667 : Blo 718322 1216667 := bstep (se 1 (by rfl) ⟨912500, by rfl⟩ : syracuseStep 1216667 = 1825001) B1825001
theorem B1216687 : Blo 718322 1216687 := bstep (se 1 (by rfl) ⟨912515, by rfl⟩ : syracuseStep 1216687 = 1825031) B1825031
theorem B19698227 : Blo 718322 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B2429513 : Blo 718322 2429513 := bstep (se 2 (by rfl) ⟨911067, by rfl⟩ : syracuseStep 2429513 = 1822135) B1822135
theorem B15537041 : Blo 718322 15537041 := bstep (se 2 (by rfl) ⟨5826390, by rfl⟩ : syracuseStep 15537041 = 11652781) B11652781
theorem B2593775 : Blo 718322 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B6919577 : Blo 718322 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B5478191 : Blo 718322 5478191 := bstep (se 1 (by rfl) ⟨4108643, by rfl⟩ : syracuseStep 5478191 = 8217287) B8217287
theorem B1218395 : Blo 718322 1218395 := bstep (se 1 (by rfl) ⟨913796, by rfl⟩ : syracuseStep 1218395 = 1827593) B1827593
theorem B11245405 : Blo 718322 11245405 := bstep (se 3 (by rfl) ⟨2108513, by rfl⟩ : syracuseStep 11245405 = 4217027) B4217027
theorem B1218847 : Blo 718322 1218847 := bstep (se 1 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 1218847 = 1828271) B1828271
theorem B3119995 : Blo 718322 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B2366489 : Blo 718322 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B2923951 : Blo 718322 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B1384103 : Blo 718322 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B3645161 : Blo 718322 3645161 := bstep (se 2 (by rfl) ⟨1366935, by rfl⟩ : syracuseStep 3645161 = 2733871) B2733871
theorem B2432969 : Blo 718322 2432969 := bstep (se 2 (by rfl) ⟨912363, by rfl⟩ : syracuseStep 2432969 = 1824727) B1824727
theorem B4628609 : Blo 718322 4628609 := bstep (se 2 (by rfl) ⟨1735728, by rfl⟩ : syracuseStep 4628609 = 3471457) B3471457
theorem B2433239 : Blo 718322 2433239 := bstep (se 1 (by rfl) ⟨1824929, by rfl⟩ : syracuseStep 2433239 = 3649859) B3649859
theorem B2728511 : Blo 718322 2728511 := bstep (se 1 (by rfl) ⟨2046383, by rfl⟩ : syracuseStep 2728511 = 4092767) B4092767
theorem B6169391 : Blo 718322 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B2728829 : Blo 718322 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B9217385 : Blo 718322 9217385 := bstep (se 2 (by rfl) ⟨3456519, by rfl⟩ : syracuseStep 9217385 = 6913039) B6913039
theorem B4105889 : Blo 718322 4105889 := bstep (se 2 (by rfl) ⟨1539708, by rfl⟩ : syracuseStep 4105889 = 3079417) B3079417
theorem B23406245 : Blo 718322 23406245 := bstep (se 4 (by rfl) ⟨2194335, by rfl⟩ : syracuseStep 23406245 = 4388671) B4388671
theorem B47490911 : Blo 718322 47490911 := bstep (se 1 (by rfl) ⟨35618183, by rfl⟩ : syracuseStep 47490911 = 71236367) B71236367
theorem B11708833 : Blo 718322 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B1616363 : Blo 718322 1616363 := bstep (se 1 (by rfl) ⟨1212272, by rfl⟩ : syracuseStep 1616363 = 2424545) B2424545
theorem B1944121 : Blo 718322 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B136719197 : Blo 718322 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B2436047 : Blo 718322 2436047 := bstep (se 1 (by rfl) ⟨1827035, by rfl⟩ : syracuseStep 2436047 = 3654071) B3654071
theorem B863227 : Blo 718322 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B1617065 : Blo 718322 1617065 := bstep (se 2 (by rfl) ⟨606399, by rfl⟩ : syracuseStep 1617065 = 1212799) B1212799
theorem B2436371 : Blo 718322 2436371 := bstep (se 1 (by rfl) ⟨1827278, by rfl⟩ : syracuseStep 2436371 = 3654557) B3654557
theorem B5484023 : Blo 718322 5484023 := bstep (se 1 (by rfl) ⟨4113017, by rfl⟩ : syracuseStep 5484023 = 8226035) B8226035
theorem B1617479 : Blo 718322 1617479 := bstep (se 1 (by rfl) ⟨1213109, by rfl⟩ : syracuseStep 1617479 = 2426219) B2426219
theorem B1617551 : Blo 718322 1617551 := bstep (se 1 (by rfl) ⟨1213163, by rfl⟩ : syracuseStep 1617551 = 2426327) B2426327
theorem B2731715 : Blo 718322 2731715 := bstep (se 1 (by rfl) ⟨2048786, by rfl⟩ : syracuseStep 2731715 = 4097573) B4097573
theorem B1617641 : Blo 718322 1617641 := bstep (se 2 (by rfl) ⟨606615, by rfl⟩ : syracuseStep 1617641 = 1213231) B1213231
theorem B1617659 : Blo 718322 1617659 := bstep (se 1 (by rfl) ⟨1213244, by rfl⟩ : syracuseStep 1617659 = 2426489) B2426489
theorem B8204165 : Blo 718322 8204165 := bstep (se 4 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 8204165 = 1538281) B1538281
theorem B2731913 : Blo 718322 2731913 := bstep (se 2 (by rfl) ⟨1024467, by rfl⟩ : syracuseStep 2731913 = 2048935) B2048935
theorem B2437559 : Blo 718322 2437559 := bstep (se 1 (by rfl) ⟨1828169, by rfl⟩ : syracuseStep 2437559 = 3656339) B3656339
theorem B1618667 : Blo 718322 1618667 := bstep (se 1 (by rfl) ⟨1214000, by rfl⟩ : syracuseStep 1618667 = 2428001) B2428001
theorem B3650345 : Blo 718322 3650345 := bstep (se 2 (by rfl) ⟨1368879, by rfl⟩ : syracuseStep 3650345 = 2737759) B2737759
theorem B2601791 : Blo 718322 2601791 := bstep (se 1 (by rfl) ⟨1951343, by rfl⟩ : syracuseStep 2601791 = 3902687) B3902687
theorem B10367837 : Blo 718322 10367837 := bstep (se 3 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 10367837 = 3887939) B3887939
theorem B1618937 : Blo 718322 1618937 := bstep (se 2 (by rfl) ⟨607101, by rfl⟩ : syracuseStep 1618937 = 1214203) B1214203
theorem B3453947 : Blo 718322 3453947 := bstep (se 1 (by rfl) ⟨2590460, by rfl⟩ : syracuseStep 3453947 = 5180921) B5180921
theorem B1619027 : Blo 718322 1619027 := bstep (se 1 (by rfl) ⟨1214270, by rfl⟩ : syracuseStep 1619027 = 2428541) B2428541
theorem B1848425 : Blo 718322 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B1619207 : Blo 718322 1619207 := bstep (se 1 (by rfl) ⟨1214405, by rfl⟩ : syracuseStep 1619207 = 2428811) B2428811
theorem B6567241 : Blo 718322 6567241 := bstep (se 2 (by rfl) ⟨2462715, by rfl⟩ : syracuseStep 6567241 = 4925431) B4925431
theorem B2733385 : Blo 718322 2733385 := bstep (se 2 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 2733385 = 2050039) B2050039
theorem B12334679 : Blo 718322 12334679 := bstep (se 1 (by rfl) ⟨9251009, by rfl⟩ : syracuseStep 12334679 = 18502019) B18502019
theorem B1619567 : Blo 718322 1619567 := bstep (se 1 (by rfl) ⟨1214675, by rfl⟩ : syracuseStep 1619567 = 2429351) B2429351
theorem B4110263 : Blo 718322 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B2734175 : Blo 718322 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B1947883 : Blo 718322 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B11680037 : Blo 718322 11680037 := bstep (se 4 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 11680037 = 2190007) B2190007
theorem B1620431 : Blo 718322 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B1620521 : Blo 718322 1620521 := bstep (se 2 (by rfl) ⟨607695, by rfl⟩ : syracuseStep 1620521 = 1215391) B1215391
theorem B5847673 : Blo 718322 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B3291785 : Blo 718322 3291785 := bstep (se 2 (by rfl) ⟨1234419, by rfl⟩ : syracuseStep 3291785 = 2468839) B2468839
theorem B50019119 : Blo 718322 50019119 := bstep (se 1 (by rfl) ⟨37514339, by rfl⟩ : syracuseStep 50019119 = 75028679) B75028679
theorem B4111195 : Blo 718322 4111195 := bstep (se 1 (by rfl) ⟨3083396, by rfl⟩ : syracuseStep 4111195 = 6166793) B6166793
theorem B8305573 : Blo 718322 8305573 := bstep (se 4 (by rfl) ⟨778647, by rfl⟩ : syracuseStep 8305573 = 1557295) B1557295
theorem B5454863 : Blo 718322 5454863 := bstep (se 1 (by rfl) ⟨4091147, by rfl⟩ : syracuseStep 5454863 = 8182295) B8182295
theorem B1621097 : Blo 718322 1621097 := bstep (se 2 (by rfl) ⟨607911, by rfl⟩ : syracuseStep 1621097 = 1215823) B1215823
theorem B2636999 : Blo 718322 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B2735329 : Blo 718322 2735329 := bstep (se 2 (by rfl) ⟨1025748, by rfl⟩ : syracuseStep 2735329 = 2051497) B2051497
theorem B1621223 : Blo 718322 1621223 := bstep (se 1 (by rfl) ⟨1215917, by rfl⟩ : syracuseStep 1621223 = 2431835) B2431835
theorem B6143525 : Blo 718322 6143525 := bstep (se 4 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 6143525 = 1151911) B1151911
theorem B1621727 : Blo 718322 1621727 := bstep (se 1 (by rfl) ⟨1216295, by rfl⟩ : syracuseStep 1621727 = 2432591) B2432591
theorem B1621799 : Blo 718322 1621799 := bstep (se 1 (by rfl) ⟨1216349, by rfl⟩ : syracuseStep 1621799 = 2432699) B2432699
theorem B4931399 : Blo 718322 4931399 := bstep (se 1 (by rfl) ⟨3698549, by rfl⟩ : syracuseStep 4931399 = 7397099) B7397099
theorem B16662419 : Blo 718322 16662419 := bstep (se 1 (by rfl) ⟨12496814, by rfl⟩ : syracuseStep 16662419 = 24993629) B24993629
theorem B769991 : Blo 718322 769991 := bstep (se 1 (by rfl) ⟨577493, by rfl⟩ : syracuseStep 769991 = 1154987) B1154987
theorem B2048809 : Blo 718322 2048809 := bstep (se 2 (by rfl) ⟨768303, by rfl⟩ : syracuseStep 2048809 = 1536607) B1536607
theorem B1622825 : Blo 718322 1622825 := bstep (se 2 (by rfl) ⟨608559, by rfl⟩ : syracuseStep 1622825 = 1217119) B1217119
theorem B3458057 : Blo 718322 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B1623095 : Blo 718322 1623095 := bstep (se 1 (by rfl) ⟨1217321, by rfl⟩ : syracuseStep 1623095 = 2434643) B2434643
theorem B1754335 : Blo 718322 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B5686507 : Blo 718322 5686507 := bstep (se 1 (by rfl) ⟨4264880, by rfl⟩ : syracuseStep 5686507 = 8529761) B8529761
theorem B1623275 : Blo 718322 1623275 := bstep (se 1 (by rfl) ⟨1217456, by rfl⟩ : syracuseStep 1623275 = 2434913) B2434913
theorem B2737577 : Blo 718322 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B1623743 : Blo 718322 1623743 := bstep (se 1 (by rfl) ⟨1217807, by rfl⟩ : syracuseStep 1623743 = 2435615) B2435615
theorem B13158359 : Blo 718322 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B1558715 : Blo 718322 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B2050427 : Blo 718322 2050427 := bstep (se 1 (by rfl) ⟨1537820, by rfl⟩ : syracuseStep 2050427 = 3075641) B3075641
theorem B1624679 : Blo 718322 1624679 := bstep (se 1 (by rfl) ⟨1218509, by rfl⟩ : syracuseStep 1624679 = 2437019) B2437019
theorem B2739035 : Blo 718322 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B1625057 : Blo 718322 1625057 := bstep (se 2 (by rfl) ⟨609396, by rfl⟩ : syracuseStep 1625057 = 1218793) B1218793
theorem B2739703 : Blo 718322 2739703 := bstep (se 1 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 2739703 = 4109555) B4109555
theorem B15781655 : Blo 718322 15781655 := bstep (se 1 (by rfl) ⟨11836241, by rfl⟩ : syracuseStep 15781655 = 23672483) B23672483
theorem B6147899 : Blo 718322 6147899 := bstep (se 1 (by rfl) ⟨4610924, by rfl⟩ : syracuseStep 6147899 = 9221849) B9221849
theorem B6934567 : Blo 718322 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B1822895 : Blo 718322 1822895 := bstep (se 1 (by rfl) ⟨1367171, by rfl⟩ : syracuseStep 1822895 = 2734343) B2734343
theorem B1233193 : Blo 718322 1233193 := bstep (se 2 (by rfl) ⟨462447, by rfl⟩ : syracuseStep 1233193 = 924895) B924895
theorem B2216585 : Blo 718322 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B2052955 : Blo 718322 2052955 := bstep (se 1 (by rfl) ⟨1539716, by rfl⟩ : syracuseStep 2052955 = 3079433) B3079433
theorem B1823593 : Blo 718322 1823593 := bstep (se 2 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 1823593 = 1367695) B1367695
theorem B2741147 : Blo 718322 2741147 := bstep (se 1 (by rfl) ⟨2055860, by rfl⟩ : syracuseStep 2741147 = 4111721) B4111721
theorem B99669041 : Blo 718322 99669041 := bstep (se 2 (by rfl) ⟨37375890, by rfl⟩ : syracuseStep 99669041 = 74751781) B74751781
theorem B3069181 : Blo 718322 3069181 := bstep (se 3 (by rfl) ⟨575471, by rfl⟩ : syracuseStep 3069181 = 1150943) B1150943
theorem B3462671 : Blo 718322 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B1726031 : Blo 718322 1726031 := bstep (se 1 (by rfl) ⟨1294523, by rfl⟩ : syracuseStep 1726031 = 2589047) B2589047
theorem B2053799 : Blo 718322 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B1267849 : Blo 718322 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B809563 : Blo 718322 809563 := bstep (se 1 (by rfl) ⟨607172, by rfl⟩ : syracuseStep 809563 = 1214345) B1214345
theorem B2054983 : Blo 718322 2054983 := bstep (se 1 (by rfl) ⟨1541237, by rfl⟩ : syracuseStep 2054983 = 3082475) B3082475
theorem B809851 : Blo 718322 809851 := bstep (se 1 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 809851 = 1214777) B1214777
theorem B1367543 : Blo 718322 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B810607 : Blo 718322 810607 := bstep (se 1 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 810607 = 1215911) B1215911
theorem B810715 : Blo 718322 810715 := bstep (se 1 (by rfl) ⟨608036, by rfl⟩ : syracuseStep 810715 = 1216073) B1216073
theorem B1826671 : Blo 718322 1826671 := bstep (se 1 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 1826671 = 2740007) B2740007
theorem B1368569 : Blo 718322 1368569 := bstep (se 2 (by rfl) ⟨513213, by rfl⟩ : syracuseStep 1368569 = 1026427) B1026427
theorem B9232967 : Blo 718322 9232967 := bstep (se 1 (by rfl) ⟨6924725, by rfl⟩ : syracuseStep 9232967 = 13849451) B13849451
theorem B811687 : Blo 718322 811687 := bstep (se 1 (by rfl) ⟨608765, by rfl⟩ : syracuseStep 811687 = 1217531) B1217531
theorem B910111 : Blo 718322 910111 := bstep (se 1 (by rfl) ⟨682583, by rfl⟩ : syracuseStep 910111 = 1365167) B1365167
theorem B811975 : Blo 718322 811975 := bstep (se 1 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 811975 = 1217963) B1217963
theorem B11658487 : Blo 718322 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B812335 : Blo 718322 812335 := bstep (se 1 (by rfl) ⟨609251, by rfl⟩ : syracuseStep 812335 = 1218503) B1218503
theorem B3073555 : Blo 718322 3073555 := bstep (se 1 (by rfl) ⟨2305166, by rfl⟩ : syracuseStep 3073555 = 4610333) B4610333
theorem B911407 : Blo 718322 911407 := bstep (se 1 (by rfl) ⟨683555, by rfl⟩ : syracuseStep 911407 = 1367111) B1367111
theorem B6580673 : Blo 718322 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B1732279 : Blo 718322 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B1732681 : Blo 718322 1732681 := bstep (se 2 (by rfl) ⟨649755, by rfl⟩ : syracuseStep 1732681 = 1299511) B1299511
theorem B5468471 : Blo 718322 5468471 := bstep (se 1 (by rfl) ⟨4101353, by rfl⟩ : syracuseStep 5468471 = 8202707) B8202707
theorem B15790403 : Blo 718322 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B6156647 : Blo 718322 6156647 := bstep (se 1 (by rfl) ⟨4617485, by rfl⟩ : syracuseStep 6156647 = 9234971) B9234971
theorem B1077659 : Blo 718322 1077659 := bstep (se 1 (by rfl) ⟨808244, by rfl⟩ : syracuseStep 1077659 = 1616489) B1616489
theorem B1078079 : Blo 718322 1078079 := bstep (se 1 (by rfl) ⟨808559, by rfl⟩ : syracuseStep 1078079 = 1617119) B1617119
theorem B1078223 : Blo 718322 1078223 := bstep (se 1 (by rfl) ⟨808667, by rfl⟩ : syracuseStep 1078223 = 1617335) B1617335
theorem B1078265 : Blo 718322 1078265 := bstep (se 2 (by rfl) ⟨404349, by rfl⟩ : syracuseStep 1078265 = 808699) B808699
theorem B1078313 : Blo 718322 1078313 := bstep (se 2 (by rfl) ⟨404367, by rfl⟩ : syracuseStep 1078313 = 808735) B808735
theorem B1078343 : Blo 718322 1078343 := bstep (se 1 (by rfl) ⟨808757, by rfl⟩ : syracuseStep 1078343 = 1617515) B1617515
theorem B5534963 : Blo 718322 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B1078523 : Blo 718322 1078523 := bstep (se 1 (by rfl) ⟨808892, by rfl⟩ : syracuseStep 1078523 = 1617785) B1617785
theorem B718427 : Blo 718322 718427 := bstep (se 1 (by rfl) ⟨538820, by rfl⟩ : syracuseStep 718427 = 1077641) B1077641
theorem B718491 : Blo 718322 718491 := bstep (se 1 (by rfl) ⟨538868, by rfl⟩ : syracuseStep 718491 = 1077737) B1077737
theorem B9336509 : Blo 718322 9336509 := bstep (se 3 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 9336509 = 3501191) B3501191
theorem B6158045 : Blo 718322 6158045 := bstep (se 3 (by rfl) ⟨1154633, by rfl⟩ : syracuseStep 6158045 = 2309267) B2309267
theorem B718575 : Blo 718322 718575 := bstep (se 1 (by rfl) ⟨538931, by rfl⟩ : syracuseStep 718575 = 1077863) B1077863
theorem B718663 : Blo 718322 718663 := bstep (se 1 (by rfl) ⟨538997, by rfl⟩ : syracuseStep 718663 = 1077995) B1077995
theorem B1537871 : Blo 718322 1537871 := bstep (se 1 (by rfl) ⟨1153403, by rfl⟩ : syracuseStep 1537871 = 2306807) B2306807
theorem B718683 : Blo 718322 718683 := bstep (se 1 (by rfl) ⟨539012, by rfl⟩ : syracuseStep 718683 = 1078025) B1078025
theorem B718751 : Blo 718322 718751 := bstep (se 1 (by rfl) ⟨539063, by rfl⟩ : syracuseStep 718751 = 1078127) B1078127
theorem B718919 : Blo 718322 718919 := bstep (se 1 (by rfl) ⟨539189, by rfl⟩ : syracuseStep 718919 = 1078379) B1078379
theorem B719079 : Blo 718322 719079 := bstep (se 1 (by rfl) ⟨539309, by rfl⟩ : syracuseStep 719079 = 1078619) B1078619
theorem B719263 : Blo 718322 719263 := bstep (se 1 (by rfl) ⟨539447, by rfl⟩ : syracuseStep 719263 = 1078895) B1078895
theorem B719311 : Blo 718322 719311 := bstep (se 1 (by rfl) ⟨539483, by rfl⟩ : syracuseStep 719311 = 1078967) B1078967
theorem B1079759 : Blo 718322 1079759 := bstep (se 1 (by rfl) ⟨809819, by rfl⟩ : syracuseStep 1079759 = 1619639) B1619639
theorem B719335 : Blo 718322 719335 := bstep (se 1 (by rfl) ⟨539501, by rfl⟩ : syracuseStep 719335 = 1079003) B1079003
theorem B1079849 : Blo 718322 1079849 := bstep (se 2 (by rfl) ⟨404943, by rfl⟩ : syracuseStep 1079849 = 809887) B809887
theorem B719451 : Blo 718322 719451 := bstep (se 1 (by rfl) ⟨539588, by rfl⟩ : syracuseStep 719451 = 1079177) B1079177
theorem B719519 : Blo 718322 719519 := bstep (se 1 (by rfl) ⟨539639, by rfl⟩ : syracuseStep 719519 = 1079279) B1079279
theorem B1080041 : Blo 718322 1080041 := bstep (se 2 (by rfl) ⟨405015, by rfl⟩ : syracuseStep 1080041 = 810031) B810031
theorem B10517239 : Blo 718322 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B719687 : Blo 718322 719687 := bstep (se 1 (by rfl) ⟨539765, by rfl⟩ : syracuseStep 719687 = 1079531) B1079531
theorem B719727 : Blo 718322 719727 := bstep (se 1 (by rfl) ⟨539795, by rfl⟩ : syracuseStep 719727 = 1079591) B1079591
theorem B719783 : Blo 718322 719783 := bstep (se 1 (by rfl) ⟨539837, by rfl⟩ : syracuseStep 719783 = 1079675) B1079675
theorem B719963 : Blo 718322 719963 := bstep (se 1 (by rfl) ⟨539972, by rfl⟩ : syracuseStep 719963 = 1079945) B1079945
theorem B1080425 : Blo 718322 1080425 := bstep (se 2 (by rfl) ⟨405159, by rfl⟩ : syracuseStep 1080425 = 810319) B810319
theorem B720079 : Blo 718322 720079 := bstep (se 1 (by rfl) ⟨540059, by rfl⟩ : syracuseStep 720079 = 1080119) B1080119
theorem B720103 : Blo 718322 720103 := bstep (se 1 (by rfl) ⟨540077, by rfl⟩ : syracuseStep 720103 = 1080155) B1080155
theorem B1080551 : Blo 718322 1080551 := bstep (se 1 (by rfl) ⟨810413, by rfl⟩ : syracuseStep 1080551 = 1620827) B1620827
theorem B720199 : Blo 718322 720199 := bstep (se 1 (by rfl) ⟨540149, by rfl⟩ : syracuseStep 720199 = 1080299) B1080299
theorem B4095431 : Blo 718322 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B720335 : Blo 718322 720335 := bstep (se 1 (by rfl) ⟨540251, by rfl⟩ : syracuseStep 720335 = 1080503) B1080503
theorem B720495 : Blo 718322 720495 := bstep (se 1 (by rfl) ⟨540371, by rfl⟩ : syracuseStep 720495 = 1080743) B1080743
theorem B720551 : Blo 718322 720551 := bstep (se 1 (by rfl) ⟨540413, by rfl⟩ : syracuseStep 720551 = 1080827) B1080827
theorem B1081055 : Blo 718322 1081055 := bstep (se 1 (by rfl) ⟨810791, by rfl⟩ : syracuseStep 1081055 = 1621583) B1621583
theorem B720615 : Blo 718322 720615 := bstep (se 1 (by rfl) ⟨540461, by rfl⟩ : syracuseStep 720615 = 1080923) B1080923
theorem B1081097 : Blo 718322 1081097 := bstep (se 2 (by rfl) ⟨405411, by rfl⟩ : syracuseStep 1081097 = 810823) B810823
theorem B720671 : Blo 718322 720671 := bstep (se 1 (by rfl) ⟨540503, by rfl⟩ : syracuseStep 720671 = 1081007) B1081007
theorem B1212239 : Blo 718322 1212239 := bstep (se 1 (by rfl) ⟨909179, by rfl⟩ : syracuseStep 1212239 = 1818359) B1818359
theorem B3080015 : Blo 718322 3080015 := bstep (se 1 (by rfl) ⟨2310011, by rfl⟩ : syracuseStep 3080015 = 4620023) B4620023
theorem B720751 : Blo 718322 720751 := bstep (se 1 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 720751 = 1081127) B1081127
theorem B720807 : Blo 718322 720807 := bstep (se 1 (by rfl) ⟨540605, by rfl⟩ : syracuseStep 720807 = 1081211) B1081211
theorem B721023 : Blo 718322 721023 := bstep (se 1 (by rfl) ⟨540767, by rfl⟩ : syracuseStep 721023 = 1081535) B1081535
theorem B9240965 : Blo 718322 9240965 := bstep (se 4 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 9240965 = 1732681) B1732681
theorem B721307 : Blo 718322 721307 := bstep (se 1 (by rfl) ⟨540980, by rfl⟩ : syracuseStep 721307 = 1081961) B1081961
theorem B721311 : Blo 718322 721311 := bstep (se 1 (by rfl) ⟨540983, by rfl⟩ : syracuseStep 721311 = 1081967) B1081967
theorem B2425247 : Blo 718322 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B1081883 : Blo 718322 1081883 := bstep (se 1 (by rfl) ⟨811412, by rfl⟩ : syracuseStep 1081883 = 1622825) B1622825
theorem B1082063 : Blo 718322 1082063 := bstep (se 1 (by rfl) ⟨811547, by rfl⟩ : syracuseStep 1082063 = 1623095) B1623095
theorem B721727 : Blo 718322 721727 := bstep (se 1 (by rfl) ⟨541295, by rfl⟩ : syracuseStep 721727 = 1082591) B1082591
theorem B1082183 : Blo 718322 1082183 := bstep (se 1 (by rfl) ⟨811637, by rfl⟩ : syracuseStep 1082183 = 1623275) B1623275
theorem B721735 : Blo 718322 721735 := bstep (se 1 (by rfl) ⟨541301, by rfl⟩ : syracuseStep 721735 = 1082603) B1082603
theorem B1082249 : Blo 718322 1082249 := bstep (se 2 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 1082249 = 811687) B811687
theorem B1213481 : Blo 718322 1213481 := bstep (se 2 (by rfl) ⟨455055, by rfl⟩ : syracuseStep 1213481 = 910111) B910111
theorem B721991 : Blo 718322 721991 := bstep (se 1 (by rfl) ⟨541493, by rfl⟩ : syracuseStep 721991 = 1082987) B1082987
theorem B1082495 : Blo 718322 1082495 := bstep (se 1 (by rfl) ⟨811871, by rfl⟩ : syracuseStep 1082495 = 1623743) B1623743
theorem B722047 : Blo 718322 722047 := bstep (se 1 (by rfl) ⟨541535, by rfl⟩ : syracuseStep 722047 = 1083071) B1083071
theorem B722171 : Blo 718322 722171 := bstep (se 1 (by rfl) ⟨541628, by rfl⟩ : syracuseStep 722171 = 1083257) B1083257
theorem B1082633 : Blo 718322 1082633 := bstep (se 2 (by rfl) ⟨405987, by rfl⟩ : syracuseStep 1082633 = 811975) B811975
theorem B1083113 : Blo 718322 1083113 := bstep (se 2 (by rfl) ⟨406167, by rfl⟩ : syracuseStep 1083113 = 812335) B812335
theorem B1083119 : Blo 718322 1083119 := bstep (se 1 (by rfl) ⟨812339, by rfl⟩ : syracuseStep 1083119 = 1624679) B1624679
theorem B1083371 : Blo 718322 1083371 := bstep (se 1 (by rfl) ⟨812528, by rfl⟩ : syracuseStep 1083371 = 1625057) B1625057
theorem B4098073 : Blo 718322 4098073 := bstep (se 2 (by rfl) ⟨1536777, by rfl⟩ : syracuseStep 4098073 = 3073555) B3073555
theorem B5179535 : Blo 718322 5179535 := bstep (se 1 (by rfl) ⟨3884651, by rfl⟩ : syracuseStep 5179535 = 7769303) B7769303
theorem B10521103 : Blo 718322 10521103 := bstep (se 1 (by rfl) ⟨7890827, by rfl⟩ : syracuseStep 10521103 = 15781655) B15781655
theorem B4098599 : Blo 718322 4098599 := bstep (se 1 (by rfl) ⟨3073949, by rfl⟩ : syracuseStep 4098599 = 6147899) B6147899
theorem B1215209 : Blo 718322 1215209 := bstep (se 2 (by rfl) ⟨455703, by rfl⟩ : syracuseStep 1215209 = 911407) B911407
theorem B1215263 : Blo 718322 1215263 := bstep (se 1 (by rfl) ⟨911447, by rfl⟩ : syracuseStep 1215263 = 1822895) B1822895
theorem B10358027 : Blo 718322 10358027 := bstep (se 1 (by rfl) ⟨7768520, by rfl⟩ : syracuseStep 10358027 = 15537041) B15537041
theorem B2592161 : Blo 718322 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B1150687 : Blo 718322 1150687 := bstep (se 1 (by rfl) ⟨863015, by rfl⟩ : syracuseStep 1150687 = 1726031) B1726031
theorem B1577659 : Blo 718322 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B4100989 : Blo 718322 4100989 := bstep (se 3 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 4100989 = 1537871) B1537871
theorem B922735 : Blo 718322 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B2430107 : Blo 718322 2430107 := bstep (se 1 (by rfl) ⟨1822580, by rfl⟩ : syracuseStep 2430107 = 3645161) B3645161
theorem B9246089 : Blo 718322 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B3085739 : Blo 718322 3085739 := bstep (se 1 (by rfl) ⟨2314304, by rfl⟩ : syracuseStep 3085739 = 4628609) B4628609
theorem B1644257 : Blo 718322 1644257 := bstep (se 2 (by rfl) ⟨616596, by rfl⟩ : syracuseStep 1644257 = 1233193) B1233193
theorem B15604163 : Blo 718322 15604163 := bstep (se 1 (by rfl) ⟨11703122, by rfl⟩ : syracuseStep 15604163 = 23406245) B23406245
theorem B2431457 : Blo 718322 2431457 := bstep (se 2 (by rfl) ⟨911796, by rfl⟩ : syracuseStep 2431457 = 1823593) B1823593
theorem B31660607 : Blo 718322 31660607 := bstep (se 1 (by rfl) ⟨23745455, by rfl⟩ : syracuseStep 31660607 = 47490911) B47490911
theorem B8756321 : Blo 718322 8756321 := bstep (se 2 (by rfl) ⟨3283620, by rfl⟩ : syracuseStep 8756321 = 6567241) B6567241
theorem B3644513 : Blo 718322 3644513 := bstep (se 2 (by rfl) ⟨1366692, by rfl⟩ : syracuseStep 3644513 = 2733385) B2733385
theorem B3645647 : Blo 718322 3645647 := bstep (se 1 (by rfl) ⟨2734235, by rfl⟩ : syracuseStep 3645647 = 5468471) B5468471
theorem B10526935 : Blo 718322 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B4104431 : Blo 718322 4104431 := bstep (se 1 (by rfl) ⟨3078323, by rfl⟩ : syracuseStep 4104431 = 6156647) B6156647
theorem B2597177 : Blo 718322 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B2433563 : Blo 718322 2433563 := bstep (se 1 (by rfl) ⟨1825172, by rfl⟩ : syracuseStep 2433563 = 3650345) B3650345
theorem B2302631 : Blo 718322 2302631 := bstep (se 1 (by rfl) ⟨1726973, by rfl⟩ : syracuseStep 2302631 = 3453947) B3453947
theorem B5481593 : Blo 718322 5481593 := bstep (se 2 (by rfl) ⟨2055597, by rfl⟩ : syracuseStep 5481593 = 4111195) B4111195
theorem B4105363 : Blo 718322 4105363 := bstep (se 1 (by rfl) ⟨3079022, by rfl⟩ : syracuseStep 4105363 = 6158045) B6158045
theorem B3646781 : Blo 718322 3646781 := bstep (se 3 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 3646781 = 1367543) B1367543
theorem B3647105 : Blo 718322 3647105 := bstep (se 2 (by rfl) ⟨1367664, by rfl⟩ : syracuseStep 3647105 = 2735329) B2735329
theorem B13150397 : Blo 718322 13150397 := bstep (se 3 (by rfl) ⟨2465699, by rfl⟩ : syracuseStep 13150397 = 4931399) B4931399
theorem B2730287 : Blo 718322 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B2435561 : Blo 718322 2435561 := bstep (se 2 (by rfl) ⟨913335, by rfl⟩ : syracuseStep 2435561 = 1826671) B1826671
theorem B6761861 : Blo 718322 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B2731745 : Blo 718322 2731745 := bstep (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) B2048809
theorem B1617695 : Blo 718322 1617695 := bstep (se 1 (by rfl) ⟨1213271, by rfl⟩ : syracuseStep 1617695 = 2426543) B2426543
theorem B7385363 : Blo 718322 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B1618217 : Blo 718322 1618217 := bstep (se 2 (by rfl) ⟨606831, by rfl⟩ : syracuseStep 1618217 = 1213663) B1213663
theorem B2339113 : Blo 718322 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B7582009 : Blo 718322 7582009 := bstep (se 2 (by rfl) ⟨2843253, by rfl⟩ : syracuseStep 7582009 = 5686507) B5686507
theorem B15544649 : Blo 718322 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B5910893 : Blo 718322 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B1618487 : Blo 718322 1618487 := bstep (se 1 (by rfl) ⟨1213865, by rfl⟩ : syracuseStep 1618487 = 2427731) B2427731
theorem B16626293 : Blo 718322 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B1749815 : Blo 718322 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B1618847 : Blo 718322 1618847 := bstep (se 1 (by rfl) ⟨1214135, by rfl⟩ : syracuseStep 1618847 = 2428271) B2428271
theorem B1094639 : Blo 718322 1094639 := bstep (se 1 (by rfl) ⟨820979, by rfl⟩ : syracuseStep 1094639 = 1641959) B1641959
theorem B9876811 : Blo 718322 9876811 := bstep (se 1 (by rfl) ⟨7407608, by rfl⟩ : syracuseStep 9876811 = 14815217) B14815217
theorem B9221485 : Blo 718322 9221485 := bstep (se 3 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 9221485 = 3458057) B3458057
theorem B4929133 : Blo 718322 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B1619675 : Blo 718322 1619675 := bstep (se 1 (by rfl) ⟨1214756, by rfl⟩ : syracuseStep 1619675 = 2429513) B2429513
theorem B15611777 : Blo 718322 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B2308447 : Blo 718322 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B3455369 : Blo 718322 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B3652127 : Blo 718322 3652127 := bstep (se 1 (by rfl) ⟨2739095, by rfl⟩ : syracuseStep 3652127 = 5478191) B5478191
theorem B3455905 : Blo 718322 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B3652937 : Blo 718322 3652937 := bstep (se 2 (by rfl) ⟨1369851, by rfl⟩ : syracuseStep 3652937 = 2739703) B2739703
theorem B2309705 : Blo 718322 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B1621979 : Blo 718322 1621979 := bstep (se 1 (by rfl) ⟨1216484, by rfl⟩ : syracuseStep 1621979 = 2432969) B2432969
theorem B4603877 : Blo 718322 4603877 := bstep (se 4 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 4603877 = 863227) B863227
theorem B1622159 : Blo 718322 1622159 := bstep (se 1 (by rfl) ⟨1216619, by rfl⟩ : syracuseStep 1622159 = 2433239) B2433239
theorem B1622249 : Blo 718322 1622249 := bstep (se 2 (by rfl) ⟨608343, by rfl⟩ : syracuseStep 1622249 = 1216687) B1216687
theorem B1819007 : Blo 718322 1819007 := bstep (se 1 (by rfl) ⟨1364255, by rfl⟩ : syracuseStep 1819007 = 2728511) B2728511
theorem B4112927 : Blo 718322 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B1819219 : Blo 718322 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B6144923 : Blo 718322 6144923 := bstep (se 1 (by rfl) ⟨4608692, by rfl⟩ : syracuseStep 6144923 = 9217385) B9217385
theorem B2737259 : Blo 718322 2737259 := bstep (se 1 (by rfl) ⟨2052944, by rfl⟩ : syracuseStep 2737259 = 4105889) B4105889
theorem B2737273 : Blo 718322 2737273 := bstep (se 2 (by rfl) ⟨1026477, by rfl⟩ : syracuseStep 2737273 = 2052955) B2052955
theorem B91146131 : Blo 718322 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B1624031 : Blo 718322 1624031 := bstep (se 1 (by rfl) ⟨1218023, by rfl⟩ : syracuseStep 1624031 = 2436047) B2436047
theorem B1624247 : Blo 718322 1624247 := bstep (se 1 (by rfl) ⟨1218185, by rfl⟩ : syracuseStep 1624247 = 2436371) B2436371
theorem B3656015 : Blo 718322 3656015 := bstep (se 1 (by rfl) ⟨2742011, by rfl⟩ : syracuseStep 3656015 = 5484023) B5484023
theorem B14993873 : Blo 718322 14993873 := bstep (se 2 (by rfl) ⟨5622702, by rfl⟩ : syracuseStep 14993873 = 11245405) B11245405
theorem B1821143 : Blo 718322 1821143 := bstep (se 1 (by rfl) ⟨1365857, by rfl⟩ : syracuseStep 1821143 = 2731715) B2731715
theorem B1821275 : Blo 718322 1821275 := bstep (se 1 (by rfl) ⟨1365956, by rfl⟩ : syracuseStep 1821275 = 2731913) B2731913
theorem B1625039 : Blo 718322 1625039 := bstep (se 1 (by rfl) ⟨1218779, by rfl⟩ : syracuseStep 1625039 = 2437559) B2437559
theorem B1625129 : Blo 718322 1625129 := bstep (se 2 (by rfl) ⟨609423, by rfl⟩ : syracuseStep 1625129 = 1218847) B1218847
theorem B3689975 : Blo 718322 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B2739977 : Blo 718322 2739977 := bstep (se 2 (by rfl) ⟨1027491, by rfl⟩ : syracuseStep 2739977 = 2054983) B2054983
theorem B2740175 : Blo 718322 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B1822783 : Blo 718322 1822783 := bstep (se 1 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 1822783 = 2734175) B2734175
theorem B7786691 : Blo 718322 7786691 := bstep (se 1 (by rfl) ⟨5840018, by rfl⟩ : syracuseStep 7786691 = 11680037) B11680037
theorem B33346079 : Blo 718322 33346079 := bstep (se 1 (by rfl) ⟨25009559, by rfl⟩ : syracuseStep 33346079 = 50019119) B50019119
theorem B1757999 : Blo 718322 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B2053309 : Blo 718322 2053309 := bstep (se 3 (by rfl) ⟨384995, by rfl⟩ : syracuseStep 2053309 = 769991) B769991
theorem B808159 : Blo 718322 808159 := bstep (se 1 (by rfl) ⟨606119, by rfl⟩ : syracuseStep 808159 = 1212239) B1212239
theorem B2053343 : Blo 718322 2053343 := bstep (se 1 (by rfl) ⟨1540007, by rfl⟩ : syracuseStep 2053343 = 3080015) B3080015
theorem B2053775 : Blo 718322 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B13129381 : Blo 718322 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B1825051 : Blo 718322 1825051 := bstep (se 1 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 1825051 = 2737577) B2737577
theorem B8772239 : Blo 718322 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B1366951 : Blo 718322 1366951 := bstep (se 1 (by rfl) ⟨1025213, by rfl⟩ : syracuseStep 1366951 = 2050427) B2050427
theorem B1826023 : Blo 718322 1826023 := bstep (se 1 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 1826023 = 2739035) B2739035
theorem B811111 : Blo 718322 811111 := bstep (se 1 (by rfl) ⟨608333, by rfl⟩ : syracuseStep 811111 = 1216667) B1216667
theorem B2056441 : Blo 718322 2056441 := bstep (se 2 (by rfl) ⟨771165, by rfl⟩ : syracuseStep 2056441 = 1542331) B1542331
theorem B13132151 : Blo 718322 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B1827431 : Blo 718322 1827431 := bstep (se 1 (by rfl) ⟨1370573, by rfl⟩ : syracuseStep 1827431 = 2741147) B2741147
theorem B1729183 : Blo 718322 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B66446027 : Blo 718322 66446027 := bstep (se 1 (by rfl) ⟨49834520, by rfl⟩ : syracuseStep 66446027 = 99669041) B99669041
theorem B4613051 : Blo 718322 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B1369199 : Blo 718322 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B812263 : Blo 718322 812263 := bstep (se 1 (by rfl) ⟨609197, by rfl⟩ : syracuseStep 812263 = 1218395) B1218395
theorem B912379 : Blo 718322 912379 := bstep (se 1 (by rfl) ⟨684284, by rfl⟩ : syracuseStep 912379 = 1368569) B1368569
theorem B6155311 : Blo 718322 6155311 := bstep (se 1 (by rfl) ⟨4616483, by rfl⟩ : syracuseStep 6155311 = 9232967) B9232967
theorem B4387115 : Blo 718322 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B1077575 : Blo 718322 1077575 := bstep (se 1 (by rfl) ⟨808181, by rfl⟩ : syracuseStep 1077575 = 1616363) B1616363
theorem B4092241 : Blo 718322 4092241 := bstep (se 2 (by rfl) ⟨1534590, by rfl⟩ : syracuseStep 4092241 = 3069181) B3069181
theorem B1078043 : Blo 718322 1078043 := bstep (se 1 (by rfl) ⟨808532, by rfl⟩ : syracuseStep 1078043 = 1617065) B1617065
theorem B1078319 : Blo 718322 1078319 := bstep (se 1 (by rfl) ⟨808739, by rfl⟩ : syracuseStep 1078319 = 1617479) B1617479
theorem B1078367 : Blo 718322 1078367 := bstep (se 1 (by rfl) ⟨808775, by rfl⟩ : syracuseStep 1078367 = 1617551) B1617551
theorem B1078427 : Blo 718322 1078427 := bstep (se 1 (by rfl) ⟨808820, by rfl⟩ : syracuseStep 1078427 = 1617641) B1617641
theorem B1078439 : Blo 718322 1078439 := bstep (se 1 (by rfl) ⟨808829, by rfl⟩ : syracuseStep 1078439 = 1617659) B1617659
theorem B5469443 : Blo 718322 5469443 := bstep (se 1 (by rfl) ⟨4102082, by rfl⟩ : syracuseStep 5469443 = 8204165) B8204165
theorem B718439 : Blo 718322 718439 := bstep (se 1 (by rfl) ⟨538829, by rfl⟩ : syracuseStep 718439 = 1077659) B1077659
theorem B1079111 : Blo 718322 1079111 := bstep (se 1 (by rfl) ⟨809333, by rfl⟩ : syracuseStep 1079111 = 1618667) B1618667
theorem B718719 : Blo 718322 718719 := bstep (se 1 (by rfl) ⟨539039, by rfl⟩ : syracuseStep 718719 = 1078079) B1078079
theorem B1734527 : Blo 718322 1734527 := bstep (se 1 (by rfl) ⟨1300895, by rfl⟩ : syracuseStep 1734527 = 2601791) B2601791
theorem B6911891 : Blo 718322 6911891 := bstep (se 1 (by rfl) ⟨5183918, by rfl⟩ : syracuseStep 6911891 = 10367837) B10367837
theorem B718815 : Blo 718322 718815 := bstep (se 1 (by rfl) ⟨539111, by rfl⟩ : syracuseStep 718815 = 1078223) B1078223
theorem B718843 : Blo 718322 718843 := bstep (se 1 (by rfl) ⟨539132, by rfl⟩ : syracuseStep 718843 = 1078265) B1078265
theorem B1079291 : Blo 718322 1079291 := bstep (se 1 (by rfl) ⟨809468, by rfl⟩ : syracuseStep 1079291 = 1618937) B1618937
theorem B718875 : Blo 718322 718875 := bstep (se 1 (by rfl) ⟨539156, by rfl⟩ : syracuseStep 718875 = 1078313) B1078313
theorem B718895 : Blo 718322 718895 := bstep (se 1 (by rfl) ⟨539171, by rfl⟩ : syracuseStep 718895 = 1078343) B1078343
theorem B1079351 : Blo 718322 1079351 := bstep (se 1 (by rfl) ⟨809513, by rfl⟩ : syracuseStep 1079351 = 1619027) B1619027
theorem B1079417 : Blo 718322 1079417 := bstep (se 2 (by rfl) ⟨404781, by rfl⟩ : syracuseStep 1079417 = 809563) B809563
theorem B7796897 : Blo 718322 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B719015 : Blo 718322 719015 := bstep (se 1 (by rfl) ⟨539261, by rfl⟩ : syracuseStep 719015 = 1078523) B1078523
theorem B1079471 : Blo 718322 1079471 := bstep (se 1 (by rfl) ⟨809603, by rfl⟩ : syracuseStep 1079471 = 1619207) B1619207
theorem B14022985 : Blo 718322 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B8223119 : Blo 718322 8223119 := bstep (se 1 (by rfl) ⟨6167339, by rfl⟩ : syracuseStep 8223119 = 12334679) B12334679
theorem B1079711 : Blo 718322 1079711 := bstep (se 1 (by rfl) ⟨809783, by rfl⟩ : syracuseStep 1079711 = 1619567) B1619567
theorem B6224339 : Blo 718322 6224339 := bstep (se 1 (by rfl) ⟨4668254, by rfl⟩ : syracuseStep 6224339 = 9336509) B9336509
theorem B1079801 : Blo 718322 1079801 := bstep (se 2 (by rfl) ⟨404925, by rfl⟩ : syracuseStep 1079801 = 809851) B809851
theorem B4159993 : Blo 718322 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B11074097 : Blo 718322 11074097 := bstep (se 2 (by rfl) ⟨4152786, by rfl⟩ : syracuseStep 11074097 = 8305573) B8305573
theorem B28146653 : Blo 718322 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B719839 : Blo 718322 719839 := bstep (se 1 (by rfl) ⟨539879, by rfl⟩ : syracuseStep 719839 = 1079759) B1079759
theorem B1080287 : Blo 718322 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B719899 : Blo 718322 719899 := bstep (se 1 (by rfl) ⟨539924, by rfl⟩ : syracuseStep 719899 = 1079849) B1079849
theorem B1080347 : Blo 718322 1080347 := bstep (se 1 (by rfl) ⟨810260, by rfl⟩ : syracuseStep 1080347 = 1620521) B1620521
theorem B2194523 : Blo 718322 2194523 := bstep (se 1 (by rfl) ⟨1645892, by rfl⟩ : syracuseStep 2194523 = 3291785) B3291785
theorem B720027 : Blo 718322 720027 := bstep (se 1 (by rfl) ⟨540020, by rfl⟩ : syracuseStep 720027 = 1080041) B1080041
theorem B3898601 : Blo 718322 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B3636575 : Blo 718322 3636575 := bstep (se 1 (by rfl) ⟨2727431, by rfl⟩ : syracuseStep 3636575 = 5454863) B5454863
theorem B720283 : Blo 718322 720283 := bstep (se 1 (by rfl) ⟨540212, by rfl⟩ : syracuseStep 720283 = 1080425) B1080425
theorem B1080731 : Blo 718322 1080731 := bstep (se 1 (by rfl) ⟨810548, by rfl⟩ : syracuseStep 1080731 = 1621097) B1621097
theorem B1080809 : Blo 718322 1080809 := bstep (se 2 (by rfl) ⟨405303, by rfl⟩ : syracuseStep 1080809 = 810607) B810607
theorem B720367 : Blo 718322 720367 := bstep (se 1 (by rfl) ⟨540275, by rfl⟩ : syracuseStep 720367 = 1080551) B1080551
theorem B1080815 : Blo 718322 1080815 := bstep (se 1 (by rfl) ⟨810611, by rfl⟩ : syracuseStep 1080815 = 1621223) B1621223
theorem B1080953 : Blo 718322 1080953 := bstep (se 2 (by rfl) ⟨405357, by rfl⟩ : syracuseStep 1080953 = 810715) B810715
theorem B4095683 : Blo 718322 4095683 := bstep (se 1 (by rfl) ⟨3071762, by rfl⟩ : syracuseStep 4095683 = 6143525) B6143525
theorem B720703 : Blo 718322 720703 := bstep (se 1 (by rfl) ⟨540527, by rfl⟩ : syracuseStep 720703 = 1081055) B1081055
theorem B1081151 : Blo 718322 1081151 := bstep (se 1 (by rfl) ⟨810863, by rfl⟩ : syracuseStep 1081151 = 1621727) B1621727
theorem B720731 : Blo 718322 720731 := bstep (se 1 (by rfl) ⟨540548, by rfl⟩ : syracuseStep 720731 = 1081097) B1081097
theorem B1081199 : Blo 718322 1081199 := bstep (se 1 (by rfl) ⟨810899, by rfl⟩ : syracuseStep 1081199 = 1621799) B1621799
theorem B11108279 : Blo 718322 11108279 := bstep (se 1 (by rfl) ⟨8331209, by rfl⟩ : syracuseStep 11108279 = 16662419) B16662419
theorem B1081439 : Blo 718322 1081439 := bstep (se 1 (by rfl) ⟨811079, by rfl⟩ : syracuseStep 1081439 = 1622159) B1622159
theorem B1081481 : Blo 718322 1081481 := bstep (se 2 (by rfl) ⟨405555, by rfl⟩ : syracuseStep 1081481 = 811111) B811111
theorem B1081499 : Blo 718322 1081499 := bstep (se 1 (by rfl) ⟨811124, by rfl⟩ : syracuseStep 1081499 = 1622249) B1622249
theorem B1212671 : Blo 718322 1212671 := bstep (se 1 (by rfl) ⟨909503, by rfl⟩ : syracuseStep 1212671 = 1819007) B1819007
theorem B6160643 : Blo 718322 6160643 := bstep (se 1 (by rfl) ⟨4620482, by rfl⟩ : syracuseStep 6160643 = 9240965) B9240965
theorem B721255 : Blo 718322 721255 := bstep (se 1 (by rfl) ⟨540941, by rfl⟩ : syracuseStep 721255 = 1081883) B1081883
theorem B721375 : Blo 718322 721375 := bstep (se 1 (by rfl) ⟨541031, by rfl⟩ : syracuseStep 721375 = 1082063) B1082063
theorem B721455 : Blo 718322 721455 := bstep (se 1 (by rfl) ⟨541091, by rfl⟩ : syracuseStep 721455 = 1082183) B1082183
theorem B721499 : Blo 718322 721499 := bstep (se 1 (by rfl) ⟨541124, by rfl⟩ : syracuseStep 721499 = 1082249) B1082249
theorem B4096615 : Blo 718322 4096615 := bstep (se 1 (by rfl) ⟨3072461, by rfl⟩ : syracuseStep 4096615 = 6144923) B6144923
theorem B721663 : Blo 718322 721663 := bstep (se 1 (by rfl) ⟨541247, by rfl⟩ : syracuseStep 721663 = 1082495) B1082495
theorem B2425625 : Blo 718322 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B721755 : Blo 718322 721755 := bstep (se 1 (by rfl) ⟨541316, by rfl⟩ : syracuseStep 721755 = 1082633) B1082633
theorem B41452397 : Blo 718322 41452397 := bstep (se 3 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 41452397 = 15544649) B15544649
theorem B722075 : Blo 718322 722075 := bstep (se 1 (by rfl) ⟨541556, by rfl⟩ : syracuseStep 722075 = 1083113) B1083113
theorem B722079 : Blo 718322 722079 := bstep (se 1 (by rfl) ⟨541559, by rfl⟩ : syracuseStep 722079 = 1083119) B1083119
theorem B1082687 : Blo 718322 1082687 := bstep (se 1 (by rfl) ⟨812015, by rfl⟩ : syracuseStep 1082687 = 1624031) B1624031
theorem B722247 : Blo 718322 722247 := bstep (se 1 (by rfl) ⟨541685, by rfl⟩ : syracuseStep 722247 = 1083371) B1083371
theorem B1082831 : Blo 718322 1082831 := bstep (se 1 (by rfl) ⟨812123, by rfl⟩ : syracuseStep 1082831 = 1624247) B1624247
theorem B5473817 : Blo 718322 5473817 := bstep (se 2 (by rfl) ⟨2052681, by rfl⟩ : syracuseStep 5473817 = 4105363) B4105363
theorem B1083017 : Blo 718322 1083017 := bstep (se 2 (by rfl) ⟨406131, by rfl⟩ : syracuseStep 1083017 = 812263) B812263
theorem B9995915 : Blo 718322 9995915 := bstep (se 1 (by rfl) ⟨7496936, by rfl⟩ : syracuseStep 9995915 = 14993873) B14993873
theorem B1214095 : Blo 718322 1214095 := bstep (se 1 (by rfl) ⟨910571, by rfl⟩ : syracuseStep 1214095 = 1821143) B1821143
theorem B1214183 : Blo 718322 1214183 := bstep (se 1 (by rfl) ⟨910637, by rfl⟩ : syracuseStep 1214183 = 1821275) B1821275
theorem B1083359 : Blo 718322 1083359 := bstep (se 1 (by rfl) ⟨812519, by rfl⟩ : syracuseStep 1083359 = 1625039) B1625039
theorem B1083419 : Blo 718322 1083419 := bstep (se 1 (by rfl) ⟨812564, by rfl⟩ : syracuseStep 1083419 = 1625129) B1625129
theorem B2459983 : Blo 718322 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B2919037 : Blo 718322 2919037 := bstep (se 3 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 2919037 = 1094639) B1094639
theorem B14028137 : Blo 718322 14028137 := bstep (se 2 (by rfl) ⟨5260551, by rfl⟩ : syracuseStep 14028137 = 10521103) B10521103
theorem B6164059 : Blo 718322 6164059 := bstep (se 1 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 6164059 = 9246089) B9246089
theorem B1216505 : Blo 718322 1216505 := bstep (se 2 (by rfl) ⟨456189, by rfl⟩ : syracuseStep 1216505 = 912379) B912379
theorem B5476733 : Blo 718322 5476733 := bstep (se 3 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 5476733 = 2053775) B2053775
theorem B21107071 : Blo 718322 21107071 := bstep (se 1 (by rfl) ⟨15830303, by rfl⟩ : syracuseStep 21107071 = 31660607) B31660607
theorem B2429675 : Blo 718322 2429675 := bstep (se 1 (by rfl) ⟨1822256, by rfl⟩ : syracuseStep 2429675 = 3644513) B3644513
theorem B2430377 : Blo 718322 2430377 := bstep (se 2 (by rfl) ⟨911391, by rfl⟩ : syracuseStep 2430377 = 1822783) B1822783
theorem B2430431 : Blo 718322 2430431 := bstep (se 1 (by rfl) ⟨1822823, by rfl⟩ : syracuseStep 2430431 = 3645647) B3645647
theorem B8754767 : Blo 718322 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B3118817 : Blo 718322 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B1218287 : Blo 718322 1218287 := bstep (se 1 (by rfl) ⟨913715, by rfl⟩ : syracuseStep 1218287 = 1827431) B1827431
theorem B35067725 : Blo 718322 35067725 := bstep (se 3 (by rfl) ⟨6575198, by rfl⟩ : syracuseStep 35067725 = 13150397) B13150397
theorem B2431187 : Blo 718322 2431187 := bstep (se 1 (by rfl) ⟨1823390, by rfl⟩ : syracuseStep 2431187 = 3646781) B3646781
theorem B2103545 : Blo 718322 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B2431403 : Blo 718322 2431403 := bstep (se 1 (by rfl) ⟨1823552, by rfl⟩ : syracuseStep 2431403 = 3647105) B3647105
theorem B29530925 : Blo 718322 29530925 := bstep (se 3 (by rfl) ⟨5537048, by rfl⟩ : syracuseStep 29530925 = 11074097) B11074097
theorem B12295313 : Blo 718322 12295313 := bstep (se 2 (by rfl) ⟨4610742, by rfl⟩ : syracuseStep 12295313 = 9221485) B9221485
theorem B17505841 : Blo 718322 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B4923575 : Blo 718322 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B2924743 : Blo 718322 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B3940595 : Blo 718322 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B2433401 : Blo 718322 2433401 := bstep (se 2 (by rfl) ⟨912525, by rfl⟩ : syracuseStep 2433401 = 1825051) B1825051
theorem B11084195 : Blo 718322 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B5546657 : Blo 718322 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B3646295 : Blo 718322 3646295 := bstep (se 1 (by rfl) ⟨2734721, by rfl⟩ : syracuseStep 3646295 = 5469443) B5469443
theorem B1156351 : Blo 718322 1156351 := bstep (se 1 (by rfl) ⟨867263, by rfl⟩ : syracuseStep 1156351 = 1734527) B1734527
theorem B2303579 : Blo 718322 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B5482079 : Blo 718322 5482079 := bstep (se 1 (by rfl) ⟨4111559, by rfl⟩ : syracuseStep 5482079 = 8223119) B8223119
theorem B2434697 : Blo 718322 2434697 := bstep (se 2 (by rfl) ⟨913011, by rfl⟩ : syracuseStep 2434697 = 1826023) B1826023
theorem B2434751 : Blo 718322 2434751 := bstep (se 1 (by rfl) ⟨1826063, by rfl⟩ : syracuseStep 2434751 = 3652127) B3652127
theorem B2599067 : Blo 718322 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B2435291 : Blo 718322 2435291 := bstep (se 1 (by rfl) ⟨1826468, by rfl⟩ : syracuseStep 2435291 = 3652937) B3652937
theorem B2730455 : Blo 718322 2730455 := bstep (se 1 (by rfl) ⟨2047841, by rfl⟩ : syracuseStep 2730455 = 4095683) B4095683
theorem B1616831 : Blo 718322 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B14035913 : Blo 718322 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B2305577 : Blo 718322 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B60764087 : Blo 718322 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B3453023 : Blo 718322 3453023 := bstep (se 1 (by rfl) ⟨2589767, by rfl⟩ : syracuseStep 3453023 = 5179535) B5179535
theorem B3649697 : Blo 718322 3649697 := bstep (se 2 (by rfl) ⟨1368636, by rfl⟩ : syracuseStep 3649697 = 2737273) B2737273
theorem B2437343 : Blo 718322 2437343 := bstep (se 1 (by rfl) ⟨1828007, by rfl⟩ : syracuseStep 2437343 = 3656015) B3656015
theorem B2732399 : Blo 718322 2732399 := bstep (se 1 (by rfl) ⟨2049299, by rfl⟩ : syracuseStep 2732399 = 4098599) B4098599
theorem B5191127 : Blo 718322 5191127 := bstep (se 1 (by rfl) ⟨3893345, by rfl⟩ : syracuseStep 5191127 = 7786691) B7786691
theorem B22230719 : Blo 718322 22230719 := bstep (se 1 (by rfl) ⟨16673039, by rfl⟩ : syracuseStep 22230719 = 33346079) B33346079
theorem B1620071 : Blo 718322 1620071 := bstep (se 1 (by rfl) ⟨1215053, by rfl⟩ : syracuseStep 1620071 = 2430107) B2430107
theorem B8207081 : Blo 718322 8207081 := bstep (se 2 (by rfl) ⟨3077655, by rfl⟩ : syracuseStep 8207081 = 6155311) B6155311
theorem B10402775 : Blo 718322 10402775 := bstep (se 1 (by rfl) ⟨7802081, by rfl⟩ : syracuseStep 10402775 = 15604163) B15604163
theorem B1620971 : Blo 718322 1620971 := bstep (se 1 (by rfl) ⟨1215728, by rfl⟩ : syracuseStep 1620971 = 2431457) B2431457
theorem B5848159 : Blo 718322 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B2736287 : Blo 718322 2736287 := bstep (se 1 (by rfl) ⟨2052215, by rfl⟩ : syracuseStep 2736287 = 4104431) B4104431
theorem B1622375 : Blo 718322 1622375 := bstep (se 1 (by rfl) ⟨1216781, by rfl⟩ : syracuseStep 1622375 = 2433563) B2433563
theorem B10109345 : Blo 718322 10109345 := bstep (se 2 (by rfl) ⟨3791004, by rfl⟩ : syracuseStep 10109345 = 7582009) B7582009
theorem B5456321 : Blo 718322 5456321 := bstep (se 2 (by rfl) ⟨2046120, by rfl⟩ : syracuseStep 5456321 = 4092241) B4092241
theorem B3654395 : Blo 718322 3654395 := bstep (se 1 (by rfl) ⟨2740796, by rfl⟩ : syracuseStep 3654395 = 5481593) B5481593
theorem B1230313 : Blo 718322 1230313 := bstep (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) B922735
theorem B1820191 : Blo 718322 1820191 := bstep (se 1 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 1820191 = 2730287) B2730287
theorem B2737745 : Blo 718322 2737745 := bstep (se 2 (by rfl) ⟨1026654, by rfl⟩ : syracuseStep 2737745 = 2053309) B2053309
theorem B1623707 : Blo 718322 1623707 := bstep (se 1 (by rfl) ⟨1217780, by rfl⟩ : syracuseStep 1623707 = 2435561) B2435561
theorem B6572177 : Blo 718322 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B4507907 : Blo 718322 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B1821163 : Blo 718322 1821163 := bstep (se 1 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 1821163 = 2731745) B2731745
theorem B23350189 : Blo 718322 23350189 := bstep (se 3 (by rfl) ⟨4378160, by rfl⟩ : syracuseStep 23350189 = 8756321) B8756321
theorem B18697313 : Blo 718322 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B1166543 : Blo 718322 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B4607873 : Blo 718322 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B1822601 : Blo 718322 1822601 := bstep (se 2 (by rfl) ⟨683475, by rfl⟩ : syracuseStep 1822601 = 1366951) B1366951
theorem B10407851 : Blo 718322 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B4607927 : Blo 718322 4607927 := bstep (se 1 (by rfl) ⟨3455945, by rfl⟩ : syracuseStep 4607927 = 6911891) B6911891
theorem B5197931 : Blo 718322 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B4149559 : Blo 718322 4149559 := bstep (se 1 (by rfl) ⟨3112169, by rfl⟩ : syracuseStep 4149559 = 6224339) B6224339
theorem B18764435 : Blo 718322 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B1463015 : Blo 718322 1463015 := bstep (se 1 (by rfl) ⟨1097261, by rfl⟩ : syracuseStep 1463015 = 2194523) B2194523
theorem B3069251 : Blo 718322 3069251 := bstep (se 1 (by rfl) ⟨2301938, by rfl⟩ : syracuseStep 3069251 = 4603877) B4603877
theorem B2741921 : Blo 718322 2741921 := bstep (se 2 (by rfl) ⟨1028220, by rfl⟩ : syracuseStep 2741921 = 2056441) B2056441
theorem B2741951 : Blo 718322 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B808987 : Blo 718322 808987 := bstep (se 1 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 808987 = 1213481) B1213481
theorem B1824839 : Blo 718322 1824839 := bstep (se 1 (by rfl) ⟨1368629, by rfl⟩ : syracuseStep 1824839 = 2737259) B2737259
theorem B810139 : Blo 718322 810139 := bstep (se 1 (by rfl) ⟨607604, by rfl⟩ : syracuseStep 810139 = 1215209) B1215209
theorem B810175 : Blo 718322 810175 := bstep (se 1 (by rfl) ⟨607631, by rfl⟩ : syracuseStep 810175 = 1215263) B1215263
theorem B6905351 : Blo 718322 6905351 := bstep (se 1 (by rfl) ⟨5179013, by rfl⟩ : syracuseStep 6905351 = 10358027) B10358027
theorem B1728107 : Blo 718322 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B1826651 : Blo 718322 1826651 := bstep (se 1 (by rfl) ⟨1369988, by rfl⟩ : syracuseStep 1826651 = 2739977) B2739977
theorem B1826783 : Blo 718322 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B5464097 : Blo 718322 5464097 := bstep (se 2 (by rfl) ⟨2049036, by rfl⟩ : syracuseStep 5464097 = 4098073) B4098073
theorem B1171999 : Blo 718322 1171999 := bstep (se 1 (by rfl) ⟨878999, by rfl⟩ : syracuseStep 1171999 = 1757999) B1757999
theorem B1368895 : Blo 718322 1368895 := bstep (se 1 (by rfl) ⟨1026671, by rfl⟩ : syracuseStep 1368895 = 2053343) B2053343
theorem B2057159 : Blo 718322 2057159 := bstep (se 1 (by rfl) ⟨1542869, by rfl⟩ : syracuseStep 2057159 = 3085739) B3085739
theorem B4384685 : Blo 718322 4384685 := bstep (se 3 (by rfl) ⟨822128, by rfl⟩ : syracuseStep 4384685 = 1644257) B1644257
theorem B1534249 : Blo 718322 1534249 := bstep (se 2 (by rfl) ⟨575343, by rfl⟩ : syracuseStep 1534249 = 1150687) B1150687
theorem B1731451 : Blo 718322 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B1535087 : Blo 718322 1535087 := bstep (se 1 (by rfl) ⟨1151315, by rfl⟩ : syracuseStep 1535087 = 2302631) B2302631
theorem B44297351 : Blo 718322 44297351 := bstep (se 1 (by rfl) ⟨33223013, by rfl⟩ : syracuseStep 44297351 = 66446027) B66446027
theorem B3075367 : Blo 718322 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B912799 : Blo 718322 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B5467985 : Blo 718322 5467985 := bstep (se 2 (by rfl) ⟨2050494, by rfl⟩ : syracuseStep 5467985 = 4100989) B4100989
theorem B1077545 : Blo 718322 1077545 := bstep (se 2 (by rfl) ⟨404079, by rfl⟩ : syracuseStep 1077545 = 808159) B808159
theorem B13169081 : Blo 718322 13169081 := bstep (se 2 (by rfl) ⟨4938405, by rfl⟩ : syracuseStep 13169081 = 9876811) B9876811
theorem B1078463 : Blo 718322 1078463 := bstep (se 1 (by rfl) ⟨808847, by rfl⟩ : syracuseStep 1078463 = 1617695) B1617695
theorem B1078811 : Blo 718322 1078811 := bstep (se 1 (by rfl) ⟨809108, by rfl⟩ : syracuseStep 1078811 = 1618217) B1618217
theorem B718383 : Blo 718322 718383 := bstep (se 1 (by rfl) ⟨538787, by rfl⟩ : syracuseStep 718383 = 1077575) B1077575
theorem B1078991 : Blo 718322 1078991 := bstep (se 1 (by rfl) ⟨809243, by rfl⟩ : syracuseStep 1078991 = 1618487) B1618487
theorem B3077929 : Blo 718322 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B718695 : Blo 718322 718695 := bstep (se 1 (by rfl) ⟨539021, by rfl⟩ : syracuseStep 718695 = 1078043) B1078043
theorem B1079231 : Blo 718322 1079231 := bstep (se 1 (by rfl) ⟨809423, by rfl⟩ : syracuseStep 1079231 = 1618847) B1618847
theorem B718879 : Blo 718322 718879 := bstep (se 1 (by rfl) ⟨539159, by rfl⟩ : syracuseStep 718879 = 1078319) B1078319
theorem B718911 : Blo 718322 718911 := bstep (se 1 (by rfl) ⟨539183, by rfl⟩ : syracuseStep 718911 = 1078367) B1078367
theorem B718951 : Blo 718322 718951 := bstep (se 1 (by rfl) ⟨539213, by rfl⟩ : syracuseStep 718951 = 1078427) B1078427
theorem B718959 : Blo 718322 718959 := bstep (se 1 (by rfl) ⟨539219, by rfl⟩ : syracuseStep 718959 = 1078439) B1078439
theorem B1079783 : Blo 718322 1079783 := bstep (se 1 (by rfl) ⟨809837, by rfl⟩ : syracuseStep 1079783 = 1619675) B1619675
theorem B719407 : Blo 718322 719407 := bstep (se 1 (by rfl) ⟨539555, by rfl⟩ : syracuseStep 719407 = 1079111) B1079111
theorem B719527 : Blo 718322 719527 := bstep (se 1 (by rfl) ⟨539645, by rfl⟩ : syracuseStep 719527 = 1079291) B1079291
theorem B719567 : Blo 718322 719567 := bstep (se 1 (by rfl) ⟨539675, by rfl⟩ : syracuseStep 719567 = 1079351) B1079351
theorem B719611 : Blo 718322 719611 := bstep (se 1 (by rfl) ⟨539708, by rfl⟩ : syracuseStep 719611 = 1079417) B1079417
theorem B719647 : Blo 718322 719647 := bstep (se 1 (by rfl) ⟨539735, by rfl⟩ : syracuseStep 719647 = 1079471) B1079471
theorem B719807 : Blo 718322 719807 := bstep (se 1 (by rfl) ⟨539855, by rfl⟩ : syracuseStep 719807 = 1079711) B1079711
theorem B719867 : Blo 718322 719867 := bstep (se 1 (by rfl) ⟨539900, by rfl⟩ : syracuseStep 719867 = 1079801) B1079801
theorem B720191 : Blo 718322 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B720231 : Blo 718322 720231 := bstep (se 1 (by rfl) ⟨540173, by rfl⟩ : syracuseStep 720231 = 1080347) B1080347
theorem B2424383 : Blo 718322 2424383 := bstep (se 1 (by rfl) ⟨1818287, by rfl⟩ : syracuseStep 2424383 = 3636575) B3636575
theorem B720487 : Blo 718322 720487 := bstep (se 1 (by rfl) ⟨540365, by rfl⟩ : syracuseStep 720487 = 1080731) B1080731
theorem B720539 : Blo 718322 720539 := bstep (se 1 (by rfl) ⟨540404, by rfl⟩ : syracuseStep 720539 = 1080809) B1080809
theorem B720543 : Blo 718322 720543 := bstep (se 1 (by rfl) ⟨540407, by rfl⟩ : syracuseStep 720543 = 1080815) B1080815
theorem B1539803 : Blo 718322 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B720635 : Blo 718322 720635 := bstep (se 1 (by rfl) ⟨540476, by rfl⟩ : syracuseStep 720635 = 1080953) B1080953
theorem B720767 : Blo 718322 720767 := bstep (se 1 (by rfl) ⟨540575, by rfl⟩ : syracuseStep 720767 = 1081151) B1081151
theorem B720799 : Blo 718322 720799 := bstep (se 1 (by rfl) ⟨540599, by rfl⟩ : syracuseStep 720799 = 1081199) B1081199
theorem B7405519 : Blo 718322 7405519 := bstep (se 1 (by rfl) ⟨5554139, by rfl⟩ : syracuseStep 7405519 = 11108279) B11108279
theorem B1081319 : Blo 718322 1081319 := bstep (se 1 (by rfl) ⟨810989, by rfl⟩ : syracuseStep 1081319 = 1621979) B1621979
theorem B720959 : Blo 718322 720959 := bstep (se 1 (by rfl) ⟨540719, by rfl⟩ : syracuseStep 720959 = 1081439) B1081439
theorem B720987 : Blo 718322 720987 := bstep (se 1 (by rfl) ⟨540740, by rfl⟩ : syracuseStep 720987 = 1081481) B1081481
theorem B720999 : Blo 718322 720999 := bstep (se 1 (by rfl) ⟨540749, by rfl⟩ : syracuseStep 720999 = 1081499) B1081499
theorem B1081583 : Blo 718322 1081583 := bstep (se 1 (by rfl) ⟨811187, by rfl⟩ : syracuseStep 1081583 = 1622375) B1622375
theorem B3899657 : Blo 718322 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B3637547 : Blo 718322 3637547 := bstep (se 1 (by rfl) ⟨2728160, by rfl⟩ : syracuseStep 3637547 = 5456321) B5456321
theorem B721791 : Blo 718322 721791 := bstep (se 1 (by rfl) ⟨541343, by rfl⟩ : syracuseStep 721791 = 1082687) B1082687
theorem B721887 : Blo 718322 721887 := bstep (se 1 (by rfl) ⟨541415, by rfl⟩ : syracuseStep 721887 = 1082831) B1082831
theorem B722011 : Blo 718322 722011 := bstep (se 1 (by rfl) ⟨541508, by rfl⟩ : syracuseStep 722011 = 1083017) B1083017
theorem B1082471 : Blo 718322 1082471 := bstep (se 1 (by rfl) ⟨811853, by rfl⟩ : syracuseStep 1082471 = 1623707) B1623707
theorem B722239 : Blo 718322 722239 := bstep (se 1 (by rfl) ⟨541679, by rfl⟩ : syracuseStep 722239 = 1083359) B1083359
theorem B722279 : Blo 718322 722279 := bstep (se 1 (by rfl) ⟨541709, by rfl⟩ : syracuseStep 722279 = 1083419) B1083419
theorem B1541801 : Blo 718322 1541801 := bstep (se 2 (by rfl) ⟨578175, by rfl⟩ : syracuseStep 1541801 = 1156351) B1156351
theorem B1640417 : Blo 718322 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B2426921 : Blo 718322 2426921 := bstep (se 2 (by rfl) ⟨910095, by rfl⟩ : syracuseStep 2426921 = 1820191) B1820191
theorem B1215067 : Blo 718322 1215067 := bstep (se 1 (by rfl) ⟨911300, by rfl⟩ : syracuseStep 1215067 = 1822601) B1822601
theorem B3279977 : Blo 718322 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B2428217 : Blo 718322 2428217 := bstep (se 2 (by rfl) ⟨910581, by rfl⟩ : syracuseStep 2428217 = 1821163) B1821163
theorem B5836511 : Blo 718322 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B31133585 : Blo 718322 31133585 := bstep (se 2 (by rfl) ⟨11675094, by rfl⟩ : syracuseStep 31133585 = 23350189) B23350189
theorem B1216559 : Blo 718322 1216559 := bstep (se 1 (by rfl) ⟨912419, by rfl⟩ : syracuseStep 1216559 = 1824839) B1824839
theorem B4100489 : Blo 718322 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B1217065 : Blo 718322 1217065 := bstep (se 2 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 1217065 = 912799) B912799
theorem B8196875 : Blo 718322 8196875 := bstep (se 1 (by rfl) ⟨6147656, by rfl⟩ : syracuseStep 8196875 = 12295313) B12295313
theorem B1152071 : Blo 718322 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B1217767 : Blo 718322 1217767 := bstep (se 1 (by rfl) ⟨913325, by rfl⟩ : syracuseStep 1217767 = 1826651) B1826651
theorem B1217855 : Blo 718322 1217855 := bstep (se 1 (by rfl) ⟨913391, by rfl⟩ : syracuseStep 1217855 = 1826783) B1826783
theorem B3642731 : Blo 718322 3642731 := bstep (se 1 (by rfl) ⟨2732048, by rfl⟩ : syracuseStep 3642731 = 5464097) B5464097
theorem B3282383 : Blo 718322 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B2627063 : Blo 718322 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B2430863 : Blo 718322 2430863 := bstep (se 1 (by rfl) ⟨1823147, by rfl⟩ : syracuseStep 2430863 = 3646295) B3646295
theorem B2923123 : Blo 718322 2923123 := bstep (se 1 (by rfl) ⟨2192342, by rfl⟩ : syracuseStep 2923123 = 4384685) B4384685
theorem B1023391 : Blo 718322 1023391 := bstep (se 1 (by rfl) ⟨767543, by rfl⟩ : syracuseStep 1023391 = 1535087) B1535087
theorem B29531567 : Blo 718322 29531567 := bstep (se 1 (by rfl) ⟨22148675, by rfl⟩ : syracuseStep 29531567 = 44297351) B44297351
theorem B4103905 : Blo 718322 4103905 := bstep (se 2 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 4103905 = 3077929) B3077929
theorem B3645323 : Blo 718322 3645323 := bstep (se 1 (by rfl) ⟨2733992, by rfl⟩ : syracuseStep 3645323 = 5467985) B5467985
theorem B40509391 : Blo 718322 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B2302015 : Blo 718322 2302015 := bstep (se 1 (by rfl) ⟨1726511, by rfl⟩ : syracuseStep 2302015 = 3453023) B3453023
theorem B2433131 : Blo 718322 2433131 := bstep (se 1 (by rfl) ⟨1824848, by rfl⟩ : syracuseStep 2433131 = 3649697) B3649697
theorem B14820479 : Blo 718322 14820479 := bstep (se 1 (by rfl) ⟨11115359, by rfl⟩ : syracuseStep 14820479 = 22230719) B22230719
theorem B23341121 : Blo 718322 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B1616255 : Blo 718322 1616255 := bstep (se 1 (by rfl) ⟨1212191, by rfl⟩ : syracuseStep 1616255 = 2424383) B2424383
theorem B1026535 : Blo 718322 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B9874025 : Blo 718322 9874025 := bstep (se 2 (by rfl) ⟨3702759, by rfl⟩ : syracuseStep 9874025 = 7405519) B7405519
theorem B4107095 : Blo 718322 4107095 := bstep (se 1 (by rfl) ⟨3080321, by rfl⟩ : syracuseStep 4107095 = 6160643) B6160643
theorem B2436263 : Blo 718322 2436263 := bstep (se 1 (by rfl) ⟨1827197, by rfl⟩ : syracuseStep 2436263 = 3654395) B3654395
theorem B1617083 : Blo 718322 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B27634931 : Blo 718322 27634931 := bstep (se 1 (by rfl) ⟨20726198, by rfl⟩ : syracuseStep 27634931 = 41452397) B41452397
theorem B3649211 : Blo 718322 3649211 := bstep (se 1 (by rfl) ⟨2736908, by rfl⟩ : syracuseStep 3649211 = 5473817) B5473817
theorem B6663943 : Blo 718322 6663943 := bstep (se 1 (by rfl) ⟨4997957, by rfl⟩ : syracuseStep 6663943 = 9995915) B9995915
theorem B14791085 : Blo 718322 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B12464875 : Blo 718322 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B1618793 : Blo 718322 1618793 := bstep (se 2 (by rfl) ⟨607047, by rfl⟩ : syracuseStep 1618793 = 1214095) B1214095
theorem B9352091 : Blo 718322 9352091 := bstep (se 1 (by rfl) ⟨7014068, by rfl⟩ : syracuseStep 9352091 = 14028137) B14028137
theorem B3651155 : Blo 718322 3651155 := bstep (se 1 (by rfl) ⟨2738366, by rfl⟩ : syracuseStep 3651155 = 5476733) B5476733
theorem B2045665 : Blo 718322 2045665 := bstep (se 2 (by rfl) ⟨767124, by rfl⟩ : syracuseStep 2045665 = 1534249) B1534249
theorem B1619783 : Blo 718322 1619783 := bstep (se 1 (by rfl) ⟨1214837, by rfl⟩ : syracuseStep 1619783 = 2429675) B2429675
theorem B2046167 : Blo 718322 2046167 := bstep (se 1 (by rfl) ⟨1534625, by rfl⟩ : syracuseStep 2046167 = 3069251) B3069251
theorem B1620251 : Blo 718322 1620251 := bstep (se 1 (by rfl) ⟨1215188, by rfl⟩ : syracuseStep 1620251 = 2430377) B2430377
theorem B1620287 : Blo 718322 1620287 := bstep (se 1 (by rfl) ⟨1215215, by rfl⟩ : syracuseStep 1620287 = 2430431) B2430431
theorem B2079211 : Blo 718322 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B2308601 : Blo 718322 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B23378483 : Blo 718322 23378483 := bstep (se 1 (by rfl) ⟨17533862, by rfl⟩ : syracuseStep 23378483 = 35067725) B35067725
theorem B1620791 : Blo 718322 1620791 := bstep (se 1 (by rfl) ⟨1215593, by rfl⟩ : syracuseStep 1620791 = 2431187) B2431187
theorem B1620935 : Blo 718322 1620935 := bstep (se 1 (by rfl) ⟨1215701, by rfl⟩ : syracuseStep 1620935 = 2431403) B2431403
theorem B4603567 : Blo 718322 4603567 := bstep (se 1 (by rfl) ⟨3452675, by rfl⟩ : syracuseStep 4603567 = 6905351) B6905351
theorem B1622267 : Blo 718322 1622267 := bstep (se 1 (by rfl) ⟨1216700, by rfl⟩ : syracuseStep 1622267 = 2433401) B2433401
theorem B7389463 : Blo 718322 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B6930845 : Blo 718322 6930845 := bstep (se 3 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 6930845 = 2599067) B2599067
theorem B3654719 : Blo 718322 3654719 := bstep (se 1 (by rfl) ⟨2741039, by rfl⟩ : syracuseStep 3654719 = 5482079) B5482079
theorem B1623131 : Blo 718322 1623131 := bstep (se 1 (by rfl) ⟨1217348, by rfl⟩ : syracuseStep 1623131 = 2434697) B2434697
theorem B1623167 : Blo 718322 1623167 := bstep (se 1 (by rfl) ⟨1217375, by rfl⟩ : syracuseStep 1623167 = 2434751) B2434751
theorem B1623527 : Blo 718322 1623527 := bstep (se 1 (by rfl) ⟨1217645, by rfl⟩ : syracuseStep 1623527 = 2435291) B2435291
theorem B1820303 : Blo 718322 1820303 := bstep (se 1 (by rfl) ⟨1365227, by rfl⟩ : syracuseStep 1820303 = 2730455) B2730455
theorem B9357275 : Blo 718322 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B1624895 : Blo 718322 1624895 := bstep (se 1 (by rfl) ⟨1218671, by rfl⟩ : syracuseStep 1624895 = 2437343) B2437343
theorem B1821599 : Blo 718322 1821599 := bstep (se 1 (by rfl) ⟨1366199, by rfl⟩ : syracuseStep 1821599 = 2732399) B2732399
theorem B3460751 : Blo 718322 3460751 := bstep (se 1 (by rfl) ⟨2595563, by rfl⟩ : syracuseStep 3460751 = 5191127) B5191127
theorem B6935183 : Blo 718322 6935183 := bstep (se 1 (by rfl) ⟨5201387, by rfl⟩ : syracuseStep 6935183 = 10402775) B10402775
theorem B1824191 : Blo 718322 1824191 := bstep (se 1 (by rfl) ⟨1368143, by rfl⟩ : syracuseStep 1824191 = 2736287) B2736287
theorem B808447 : Blo 718322 808447 := bstep (se 1 (by rfl) ⟨606335, by rfl⟩ : syracuseStep 808447 = 1212671) B1212671
theorem B5462153 : Blo 718322 5462153 := bstep (se 2 (by rfl) ⟨2048307, by rfl⟩ : syracuseStep 5462153 = 4096615) B4096615
theorem B1825163 : Blo 718322 1825163 := bstep (se 1 (by rfl) ⟨1368872, by rfl⟩ : syracuseStep 1825163 = 2737745) B2737745
theorem B1825193 : Blo 718322 1825193 := bstep (se 2 (by rfl) ⟨684447, by rfl⟩ : syracuseStep 1825193 = 1368895) B1368895
theorem B26958253 : Blo 718322 26958253 := bstep (se 3 (by rfl) ⟨5054672, by rfl⟩ : syracuseStep 26958253 = 10109345) B10109345
theorem B35117549 : Blo 718322 35117549 := bstep (se 3 (by rfl) ⟨6584540, by rfl⟩ : syracuseStep 35117549 = 13169081) B13169081
theorem B809455 : Blo 718322 809455 := bstep (se 1 (by rfl) ⟨607091, by rfl⟩ : syracuseStep 809455 = 1214183) B1214183
theorem B4381451 : Blo 718322 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B777695 : Blo 718322 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B3071915 : Blo 718322 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B6938567 : Blo 718322 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B3071951 : Blo 718322 3071951 := bstep (se 1 (by rfl) ⟨2303963, by rfl⟩ : syracuseStep 3071951 = 4607927) B4607927
theorem B811003 : Blo 718322 811003 := bstep (se 1 (by rfl) ⟨608252, by rfl⟩ : syracuseStep 811003 = 1216505) B1216505
theorem B3465287 : Blo 718322 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B6250661 : Blo 718322 6250661 := bstep (se 4 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 6250661 = 1171999) B1171999
theorem B12509623 : Blo 718322 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B975343 : Blo 718322 975343 := bstep (se 1 (by rfl) ⟨731507, by rfl⟩ : syracuseStep 975343 = 1463015) B1463015
theorem B3892049 : Blo 718322 3892049 := bstep (se 2 (by rfl) ⟨1459518, by rfl⟩ : syracuseStep 3892049 = 2919037) B2919037
theorem B1827947 : Blo 718322 1827947 := bstep (se 1 (by rfl) ⟨1370960, by rfl⟩ : syracuseStep 1827947 = 2741921) B2741921
theorem B1827967 : Blo 718322 1827967 := bstep (se 1 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 1827967 = 2741951) B2741951
theorem B812191 : Blo 718322 812191 := bstep (se 1 (by rfl) ⟨609143, by rfl⟩ : syracuseStep 812191 = 1218287) B1218287
theorem B1402363 : Blo 718322 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B19687283 : Blo 718322 19687283 := bstep (se 1 (by rfl) ⟨14765462, by rfl⟩ : syracuseStep 19687283 = 29530925) B29530925
theorem B8218745 : Blo 718322 8218745 := bstep (se 2 (by rfl) ⟨3082029, by rfl⟩ : syracuseStep 8218745 = 6164059) B6164059
theorem B5532745 : Blo 718322 5532745 := bstep (se 2 (by rfl) ⟨2074779, by rfl⟩ : syracuseStep 5532745 = 4149559) B4149559
theorem B28142761 : Blo 718322 28142761 := bstep (se 2 (by rfl) ⟨10553535, by rfl⟩ : syracuseStep 28142761 = 21107071) B21107071
theorem B1371439 : Blo 718322 1371439 := bstep (se 1 (by rfl) ⟨1028579, by rfl⟩ : syracuseStep 1371439 = 2057159) B2057159
theorem B12021085 : Blo 718322 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B1535719 : Blo 718322 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B1077887 : Blo 718322 1077887 := bstep (se 1 (by rfl) ⟨808415, by rfl⟩ : syracuseStep 1077887 = 1616831) B1616831
theorem B1537051 : Blo 718322 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B1078649 : Blo 718322 1078649 := bstep (se 2 (by rfl) ⟨404493, by rfl⟩ : syracuseStep 1078649 = 808987) B808987
theorem B718363 : Blo 718322 718363 := bstep (se 1 (by rfl) ⟨538772, by rfl⟩ : syracuseStep 718363 = 1077545) B1077545
theorem B718975 : Blo 718322 718975 := bstep (se 1 (by rfl) ⟨539231, by rfl⟩ : syracuseStep 718975 = 1078463) B1078463
theorem B719207 : Blo 718322 719207 := bstep (se 1 (by rfl) ⟨539405, by rfl⟩ : syracuseStep 719207 = 1078811) B1078811
theorem B719327 : Blo 718322 719327 := bstep (se 1 (by rfl) ⟨539495, by rfl⟩ : syracuseStep 719327 = 1078991) B1078991
theorem B719487 : Blo 718322 719487 := bstep (se 1 (by rfl) ⟨539615, by rfl⟩ : syracuseStep 719487 = 1079231) B1079231
theorem B1080047 : Blo 718322 1080047 := bstep (se 1 (by rfl) ⟨810035, by rfl⟩ : syracuseStep 1080047 = 1620071) B1620071
theorem B7797545 : Blo 718322 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B1080185 : Blo 718322 1080185 := bstep (se 2 (by rfl) ⟨405069, by rfl⟩ : syracuseStep 1080185 = 810139) B810139
theorem B1080233 : Blo 718322 1080233 := bstep (se 2 (by rfl) ⟨405087, by rfl⟩ : syracuseStep 1080233 = 810175) B810175
theorem B719855 : Blo 718322 719855 := bstep (se 1 (by rfl) ⟨539891, by rfl⟩ : syracuseStep 719855 = 1079783) B1079783
theorem B5471387 : Blo 718322 5471387 := bstep (se 1 (by rfl) ⟨4103540, by rfl⟩ : syracuseStep 5471387 = 8207081) B8207081
theorem B1080647 : Blo 718322 1080647 := bstep (se 1 (by rfl) ⟨810485, by rfl⟩ : syracuseStep 1080647 = 1620971) B1620971
theorem B720879 : Blo 718322 720879 := bstep (se 1 (by rfl) ⟨540659, by rfl⟩ : syracuseStep 720879 = 1081319) B1081319
theorem B721055 : Blo 718322 721055 := bstep (se 1 (by rfl) ⟨540791, by rfl⟩ : syracuseStep 721055 = 1081583) B1081583
theorem B1081511 : Blo 718322 1081511 := bstep (se 1 (by rfl) ⟨811133, by rfl⟩ : syracuseStep 1081511 = 1622267) B1622267
theorem B2425031 : Blo 718322 2425031 := bstep (se 1 (by rfl) ⟨1818773, by rfl⟩ : syracuseStep 2425031 = 3637547) B3637547
theorem B4620563 : Blo 718322 4620563 := bstep (se 1 (by rfl) ⟨3465422, by rfl⟩ : syracuseStep 4620563 = 6930845) B6930845
theorem B1082087 : Blo 718322 1082087 := bstep (se 1 (by rfl) ⟨811565, by rfl⟩ : syracuseStep 1082087 = 1623131) B1623131
theorem B721647 : Blo 718322 721647 := bstep (se 1 (by rfl) ⟨541235, by rfl⟩ : syracuseStep 721647 = 1082471) B1082471
theorem B1082111 : Blo 718322 1082111 := bstep (se 1 (by rfl) ⟨811583, by rfl⟩ : syracuseStep 1082111 = 1623167) B1623167
theorem B1082351 : Blo 718322 1082351 := bstep (se 1 (by rfl) ⟨811763, by rfl⟩ : syracuseStep 1082351 = 1623527) B1623527
theorem B1213535 : Blo 718322 1213535 := bstep (se 1 (by rfl) ⟨910151, by rfl⟩ : syracuseStep 1213535 = 1820303) B1820303
theorem B1082921 : Blo 718322 1082921 := bstep (se 2 (by rfl) ⟨406095, by rfl⟩ : syracuseStep 1082921 = 812191) B812191
theorem B1083263 : Blo 718322 1083263 := bstep (se 1 (by rfl) ⟨812447, by rfl⟩ : syracuseStep 1083263 = 1624895) B1624895
theorem B1214399 : Blo 718322 1214399 := bstep (se 1 (by rfl) ⟨910799, by rfl⟩ : syracuseStep 1214399 = 1821599) B1821599
theorem B1869817 : Blo 718322 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B66717989 : Blo 718322 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B4623455 : Blo 718322 4623455 := bstep (se 1 (by rfl) ⟨3467591, by rfl⟩ : syracuseStep 4623455 = 6935183) B6935183
theorem B2428487 : Blo 718322 2428487 := bstep (se 1 (by rfl) ⟨1821365, by rfl⟩ : syracuseStep 2428487 = 3642731) B3642731
theorem B1216127 : Blo 718322 1216127 := bstep (se 1 (by rfl) ⟨912095, by rfl⟩ : syracuseStep 1216127 = 1824191) B1824191
theorem B3641435 : Blo 718322 3641435 := bstep (se 1 (by rfl) ⟨2731076, by rfl⟩ : syracuseStep 3641435 = 5462153) B5462153
theorem B7376993 : Blo 718322 7376993 := bstep (se 2 (by rfl) ⟨2766372, by rfl⟩ : syracuseStep 7376993 = 5532745) B5532745
theorem B37523681 : Blo 718322 37523681 := bstep (se 2 (by rfl) ⟨14071380, by rfl⟩ : syracuseStep 37523681 = 28142761) B28142761
theorem B1216775 : Blo 718322 1216775 := bstep (se 1 (by rfl) ⟨912581, by rfl⟩ : syracuseStep 1216775 = 1825163) B1825163
theorem B1216795 : Blo 718322 1216795 := bstep (se 1 (by rfl) ⟨912596, by rfl⟩ : syracuseStep 1216795 = 1825193) B1825193
theorem B16028113 : Blo 718322 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B2920967 : Blo 718322 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B8885257 : Blo 718322 8885257 := bstep (se 2 (by rfl) ⟨3331971, by rfl⟩ : syracuseStep 8885257 = 6663943) B6663943
theorem B2430215 : Blo 718322 2430215 := bstep (se 1 (by rfl) ⟨1822661, by rfl⟩ : syracuseStep 2430215 = 3645323) B3645323
theorem B4625711 : Blo 718322 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B4167107 : Blo 718322 4167107 := bstep (se 1 (by rfl) ⟨3125330, by rfl⟩ : syracuseStep 4167107 = 6250661) B6250661
theorem B2594699 : Blo 718322 2594699 := bstep (se 1 (by rfl) ⟨1946024, by rfl⟩ : syracuseStep 2594699 = 3892049) B3892049
theorem B1218631 : Blo 718322 1218631 := bstep (se 1 (by rfl) ⟨913973, by rfl⟩ : syracuseStep 1218631 = 1827947) B1827947
theorem B16619833 : Blo 718322 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B5479163 : Blo 718322 5479163 := bstep (se 1 (by rfl) ⟨4109372, by rfl⟩ : syracuseStep 5479163 = 8218745) B8218745
theorem B18423287 : Blo 718322 18423287 := bstep (se 1 (by rfl) ⟨13817465, by rfl⟩ : syracuseStep 18423287 = 27634931) B27634931
theorem B2727553 : Blo 718322 2727553 := bstep (se 2 (by rfl) ⟨1022832, by rfl⟩ : syracuseStep 2727553 = 2045665) B2045665
theorem B2432807 : Blo 718322 2432807 := bstep (se 1 (by rfl) ⟨1824605, by rfl⟩ : syracuseStep 2432807 = 3649211) B3649211
theorem B6234727 : Blo 718322 6234727 := bstep (se 1 (by rfl) ⟨4676045, by rfl⟩ : syracuseStep 6234727 = 9352091) B9352091
theorem B2434103 : Blo 718322 2434103 := bstep (se 1 (by rfl) ⟨1825577, by rfl⟩ : syracuseStep 2434103 = 3651155) B3651155
theorem B2073853 : Blo 718322 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B3647591 : Blo 718322 3647591 := bstep (se 1 (by rfl) ⟨2735693, by rfl⟩ : syracuseStep 3647591 = 5471387) B5471387
theorem B6138089 : Blo 718322 6138089 := bstep (se 2 (by rfl) ⟨2301783, by rfl⟩ : syracuseStep 6138089 = 4603567) B4603567
theorem B54012521 : Blo 718322 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B2599771 : Blo 718322 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B2436479 : Blo 718322 2436479 := bstep (se 1 (by rfl) ⟨1827359, by rfl⟩ : syracuseStep 2436479 = 3654719) B3654719
theorem B6238183 : Blo 718322 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B1617947 : Blo 718322 1617947 := bstep (se 1 (by rfl) ⟨1213460, by rfl⟩ : syracuseStep 1617947 = 2426921) B2426921
theorem B2437289 : Blo 718322 2437289 := bstep (se 2 (by rfl) ⟨913983, by rfl⟩ : syracuseStep 2437289 = 1827967) B1827967
theorem B1618811 : Blo 718322 1618811 := bstep (se 1 (by rfl) ⟨1214108, by rfl⟩ : syracuseStep 1618811 = 2428217) B2428217
theorem B2307167 : Blo 718322 2307167 := bstep (se 1 (by rfl) ⟨1730375, by rfl⟩ : syracuseStep 2307167 = 3460751) B3460751
theorem B20755723 : Blo 718322 20755723 := bstep (se 1 (by rfl) ⟨15566792, by rfl⟩ : syracuseStep 20755723 = 31133585) B31133585
theorem B2733659 : Blo 718322 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B768047 : Blo 718322 768047 := bstep (se 1 (by rfl) ⟨576035, by rfl⟩ : syracuseStep 768047 = 1152071) B1152071
theorem B1620089 : Blo 718322 1620089 := bstep (se 2 (by rfl) ⟨607533, by rfl⟩ : syracuseStep 1620089 = 1215067) B1215067
theorem B1751375 : Blo 718322 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B1620575 : Blo 718322 1620575 := bstep (se 1 (by rfl) ⟨1215431, by rfl⟩ : syracuseStep 1620575 = 2430863) B2430863
theorem B23411699 : Blo 718322 23411699 := bstep (se 1 (by rfl) ⟨17558774, by rfl⟩ : syracuseStep 23411699 = 35117549) B35117549
theorem B4111469 : Blo 718322 4111469 := bstep (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) B1541801
theorem B2047625 : Blo 718322 2047625 := bstep (se 2 (by rfl) ⟨767859, by rfl⟩ : syracuseStep 2047625 = 1535719) B1535719
theorem B4374445 : Blo 718322 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B2047943 : Blo 718322 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B2047967 : Blo 718322 2047967 := bstep (se 1 (by rfl) ⟨1535975, by rfl⟩ : syracuseStep 2047967 = 3071951) B3071951
theorem B2310191 : Blo 718322 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B1622087 : Blo 718322 1622087 := bstep (se 1 (by rfl) ⟨1216565, by rfl⟩ : syracuseStep 1622087 = 2433131) B2433131
theorem B1622753 : Blo 718322 1622753 := bstep (se 2 (by rfl) ⟨608532, by rfl⟩ : syracuseStep 1622753 = 1217065) B1217065
theorem B9880319 : Blo 718322 9880319 := bstep (se 1 (by rfl) ⟨7410239, by rfl⟩ : syracuseStep 9880319 = 14820479) B14820479
theorem B13124855 : Blo 718322 13124855 := bstep (se 1 (by rfl) ⟨9843641, by rfl⟩ : syracuseStep 13124855 = 19687283) B19687283
theorem B2049401 : Blo 718322 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B1623689 : Blo 718322 1623689 := bstep (se 2 (by rfl) ⟨608883, by rfl⟩ : syracuseStep 1623689 = 1217767) B1217767
theorem B2738063 : Blo 718322 2738063 := bstep (se 1 (by rfl) ⟨2053547, by rfl⟩ : syracuseStep 2738063 = 4107095) B4107095
theorem B1624175 : Blo 718322 1624175 := bstep (se 1 (by rfl) ⟨1218131, by rfl⟩ : syracuseStep 1624175 = 2436263) B2436263
theorem B2772281 : Blo 718322 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B1364111 : Blo 718322 1364111 := bstep (se 1 (by rfl) ⟨1023083, by rfl⟩ : syracuseStep 1364111 = 2046167) B2046167
theorem B15585655 : Blo 718322 15585655 := bstep (se 1 (by rfl) ⟨11689241, by rfl⟩ : syracuseStep 15585655 = 23378483) B23378483
theorem B5198363 : Blo 718322 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B1364521 : Blo 718322 1364521 := bstep (se 2 (by rfl) ⟨511695, by rfl⟩ : syracuseStep 1364521 = 1023391) B1023391
theorem B3069353 : Blo 718322 3069353 := bstep (se 2 (by rfl) ⟨1151007, by rfl⟩ : syracuseStep 3069353 = 2302015) B2302015
theorem B9852617 : Blo 718322 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B1300457 : Blo 718322 1300457 := bstep (se 2 (by rfl) ⟨487671, by rfl⟩ : syracuseStep 1300457 = 975343) B975343
theorem B2186651 : Blo 718322 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B3891007 : Blo 718322 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B811039 : Blo 718322 811039 := bstep (se 1 (by rfl) ⟨608279, by rfl⟩ : syracuseStep 811039 = 1216559) B1216559
theorem B5464583 : Blo 718322 5464583 := bstep (se 1 (by rfl) ⟨4098437, by rfl⟩ : syracuseStep 5464583 = 8196875) B8196875
theorem B1368713 : Blo 718322 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B811903 : Blo 718322 811903 := bstep (se 1 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 811903 = 1217855) B1217855
theorem B2188255 : Blo 718322 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B1828585 : Blo 718322 1828585 := bstep (se 2 (by rfl) ⟨685719, by rfl⟩ : syracuseStep 1828585 = 1371439) B1371439
theorem B19687711 : Blo 718322 19687711 := bstep (se 1 (by rfl) ⟨14765783, by rfl⟩ : syracuseStep 19687711 = 29531567) B29531567
theorem B6156269 : Blo 718322 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B15560747 : Blo 718322 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B1077503 : Blo 718322 1077503 := bstep (se 1 (by rfl) ⟨808127, by rfl⟩ : syracuseStep 1077503 = 1616255) B1616255
theorem B6582683 : Blo 718322 6582683 := bstep (se 1 (by rfl) ⟨4937012, by rfl⟩ : syracuseStep 6582683 = 9874025) B9874025
theorem B1077929 : Blo 718322 1077929 := bstep (se 2 (by rfl) ⟨404223, by rfl⟩ : syracuseStep 1077929 = 808447) B808447
theorem B1078055 : Blo 718322 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B9860723 : Blo 718322 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B718591 : Blo 718322 718591 := bstep (se 1 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 718591 = 1077887) B1077887
theorem B35944337 : Blo 718322 35944337 := bstep (se 2 (by rfl) ⟨13479126, by rfl⟩ : syracuseStep 35944337 = 26958253) B26958253
theorem B1079195 : Blo 718322 1079195 := bstep (se 1 (by rfl) ⟨809396, by rfl⟩ : syracuseStep 1079195 = 1618793) B1618793
theorem B1079273 : Blo 718322 1079273 := bstep (se 2 (by rfl) ⟨404727, by rfl⟩ : syracuseStep 1079273 = 809455) B809455
theorem B3897497 : Blo 718322 3897497 := bstep (se 2 (by rfl) ⟨1461561, by rfl⟩ : syracuseStep 3897497 = 2923123) B2923123
theorem B719099 : Blo 718322 719099 := bstep (se 1 (by rfl) ⟨539324, by rfl⟩ : syracuseStep 719099 = 1078649) B1078649
theorem B1079855 : Blo 718322 1079855 := bstep (se 1 (by rfl) ⟨809891, by rfl⟩ : syracuseStep 1079855 = 1619783) B1619783
theorem B1080167 : Blo 718322 1080167 := bstep (se 1 (by rfl) ⟨810125, by rfl⟩ : syracuseStep 1080167 = 1620251) B1620251
theorem B1080191 : Blo 718322 1080191 := bstep (se 1 (by rfl) ⟨810143, by rfl⟩ : syracuseStep 1080191 = 1620287) B1620287
theorem B720031 : Blo 718322 720031 := bstep (se 1 (by rfl) ⟨540023, by rfl⟩ : syracuseStep 720031 = 1080047) B1080047
theorem B1080527 : Blo 718322 1080527 := bstep (se 1 (by rfl) ⟨810395, by rfl⟩ : syracuseStep 1080527 = 1620791) B1620791
theorem B720123 : Blo 718322 720123 := bstep (se 1 (by rfl) ⟨540092, by rfl⟩ : syracuseStep 720123 = 1080185) B1080185
theorem B720155 : Blo 718322 720155 := bstep (se 1 (by rfl) ⟨540116, by rfl⟩ : syracuseStep 720155 = 1080233) B1080233
theorem B1080623 : Blo 718322 1080623 := bstep (se 1 (by rfl) ⟨810467, by rfl⟩ : syracuseStep 1080623 = 1620935) B1620935
theorem B720431 : Blo 718322 720431 := bstep (se 1 (by rfl) ⟨540323, by rfl⟩ : syracuseStep 720431 = 1080647) B1080647
theorem B5471873 : Blo 718322 5471873 := bstep (se 2 (by rfl) ⟨2051952, by rfl⟩ : syracuseStep 5471873 = 4103905) B4103905
theorem B1081337 : Blo 718322 1081337 := bstep (se 2 (by rfl) ⟨405501, by rfl⟩ : syracuseStep 1081337 = 811003) B811003
theorem B1540127 : Blo 718322 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B1081385 : Blo 718322 1081385 := bstep (se 2 (by rfl) ⟨405519, by rfl⟩ : syracuseStep 1081385 = 811039) B811039
theorem B1081391 : Blo 718322 1081391 := bstep (se 1 (by rfl) ⟨811043, by rfl⟩ : syracuseStep 1081391 = 1622087) B1622087
theorem B721007 : Blo 718322 721007 := bstep (se 1 (by rfl) ⟨540755, by rfl⟩ : syracuseStep 721007 = 1081511) B1081511
theorem B3080375 : Blo 718322 3080375 := bstep (se 1 (by rfl) ⟨2310281, by rfl⟩ : syracuseStep 3080375 = 4620563) B4620563
theorem B1081835 : Blo 718322 1081835 := bstep (se 1 (by rfl) ⟨811376, by rfl⟩ : syracuseStep 1081835 = 1622753) B1622753
theorem B721391 : Blo 718322 721391 := bstep (se 1 (by rfl) ⟨541043, by rfl⟩ : syracuseStep 721391 = 1082087) B1082087
theorem B8192501 : Blo 718322 8192501 := bstep (se 5 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 8192501 = 768047) B768047
theorem B721407 : Blo 718322 721407 := bstep (se 1 (by rfl) ⟨541055, by rfl⟩ : syracuseStep 721407 = 1082111) B1082111
theorem B6586879 : Blo 718322 6586879 := bstep (se 1 (by rfl) ⟨4940159, by rfl⟩ : syracuseStep 6586879 = 9880319) B9880319
theorem B721567 : Blo 718322 721567 := bstep (se 1 (by rfl) ⟨541175, by rfl⟩ : syracuseStep 721567 = 1082351) B1082351
theorem B8749903 : Blo 718322 8749903 := bstep (se 1 (by rfl) ⟨6562427, by rfl⟩ : syracuseStep 8749903 = 13124855) B13124855
theorem B721947 : Blo 718322 721947 := bstep (se 1 (by rfl) ⟨541460, by rfl⟩ : syracuseStep 721947 = 1082921) B1082921
theorem B1082459 : Blo 718322 1082459 := bstep (se 1 (by rfl) ⟨811844, by rfl⟩ : syracuseStep 1082459 = 1623689) B1623689
theorem B1082537 : Blo 718322 1082537 := bstep (se 2 (by rfl) ⟨405951, by rfl⟩ : syracuseStep 1082537 = 811903) B811903
theorem B722175 : Blo 718322 722175 := bstep (se 1 (by rfl) ⟨541631, by rfl⟩ : syracuseStep 722175 = 1083263) B1083263
theorem B2917673 : Blo 718322 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B1082783 : Blo 718322 1082783 := bstep (se 1 (by rfl) ⟨812087, by rfl⟩ : syracuseStep 1082783 = 1624175) B1624175
theorem B3082303 : Blo 718322 3082303 := bstep (se 1 (by rfl) ⟨2311727, by rfl⟩ : syracuseStep 3082303 = 4623455) B4623455
theorem B2493089 : Blo 718322 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B2427623 : Blo 718322 2427623 := bstep (se 1 (by rfl) ⟨1820717, by rfl⟩ : syracuseStep 2427623 = 3641435) B3641435
theorem B4917995 : Blo 718322 4917995 := bstep (se 1 (by rfl) ⟨3688496, by rfl⟩ : syracuseStep 4917995 = 7376993) B7376993
theorem B26250281 : Blo 718322 26250281 := bstep (se 2 (by rfl) ⟨9843855, by rfl⟩ : syracuseStep 26250281 = 19687711) B19687711
theorem B3083807 : Blo 718322 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B95851565 : Blo 718322 95851565 := bstep (se 3 (by rfl) ⟨17972168, by rfl⟩ : syracuseStep 95851565 = 35944337) B35944337
theorem B47388037 : Blo 718322 47388037 := bstep (se 4 (by rfl) ⟨4442628, by rfl⟩ : syracuseStep 47388037 = 8885257) B8885257
theorem B3643055 : Blo 718322 3643055 := bstep (se 1 (by rfl) ⟨2732291, by rfl⟩ : syracuseStep 3643055 = 5464583) B5464583
theorem B20780873 : Blo 718322 20780873 := bstep (se 2 (by rfl) ⟨7792827, by rfl⟩ : syracuseStep 20780873 = 15585655) B15585655
theorem B21370817 : Blo 718322 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B2431727 : Blo 718322 2431727 := bstep (se 1 (by rfl) ⟨1823795, by rfl⟩ : syracuseStep 2431727 = 3647591) B3647591
theorem B4104179 : Blo 718322 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B22159777 : Blo 718322 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B2598331 : Blo 718322 2598331 := bstep (se 1 (by rfl) ⟨1948748, by rfl⟩ : syracuseStep 2598331 = 3897497) B3897497
theorem B15607799 : Blo 718322 15607799 := bstep (se 1 (by rfl) ⟨11705849, by rfl⟩ : syracuseStep 15607799 = 23411699) B23411699
theorem B5188009 : Blo 718322 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B3647915 : Blo 718322 3647915 := bstep (se 1 (by rfl) ⟨2735936, by rfl⟩ : syracuseStep 3647915 = 5471873) B5471873
theorem B1616687 : Blo 718322 1616687 := bstep (se 1 (by rfl) ⟨1212515, by rfl⟩ : syracuseStep 1616687 = 2425031) B2425031
theorem B44478659 : Blo 718322 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B1848187 : Blo 718322 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B2438113 : Blo 718322 2438113 := bstep (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) B1828585
theorem B1618991 : Blo 718322 1618991 := bstep (se 1 (by rfl) ⟨1214243, by rfl⟩ : syracuseStep 1618991 = 2428487) B2428487
theorem B25015787 : Blo 718322 25015787 := bstep (se 1 (by rfl) ⟨18761840, by rfl⟩ : syracuseStep 25015787 = 37523681) B37523681
theorem B1947311 : Blo 718322 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B1620143 : Blo 718322 1620143 := bstep (se 1 (by rfl) ⟨1215107, by rfl⟩ : syracuseStep 1620143 = 2430215) B2430215
theorem B2046235 : Blo 718322 2046235 := bstep (se 1 (by rfl) ⟨1534676, by rfl⟩ : syracuseStep 2046235 = 3069353) B3069353
theorem B6568411 : Blo 718322 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B866971 : Blo 718322 866971 := bstep (se 1 (by rfl) ⟨650228, by rfl⟩ : syracuseStep 866971 = 1300457) B1300457
theorem B3652775 : Blo 718322 3652775 := bstep (se 1 (by rfl) ⟨2739581, by rfl⟩ : syracuseStep 3652775 = 5479163) B5479163
theorem B1457767 : Blo 718322 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B1621871 : Blo 718322 1621871 := bstep (se 1 (by rfl) ⟨1216403, by rfl⟩ : syracuseStep 1621871 = 2432807) B2432807
theorem B1622393 : Blo 718322 1622393 := bstep (se 2 (by rfl) ⟨608397, by rfl⟩ : syracuseStep 1622393 = 1216795) B1216795
theorem B1622735 : Blo 718322 1622735 := bstep (se 1 (by rfl) ⟨1217051, by rfl⟩ : syracuseStep 1622735 = 2434103) B2434103
theorem B1819361 : Blo 718322 1819361 := bstep (se 2 (by rfl) ⟨682260, by rfl⟩ : syracuseStep 1819361 = 1364521) B1364521
theorem B11060549 : Blo 718322 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B27674297 : Blo 718322 27674297 := bstep (se 2 (by rfl) ⟨10377861, by rfl⟩ : syracuseStep 27674297 = 20755723) B20755723
theorem B1624319 : Blo 718322 1624319 := bstep (se 1 (by rfl) ⟨1218239, by rfl⟩ : syracuseStep 1624319 = 2436479) B2436479
theorem B10373831 : Blo 718322 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B1624841 : Blo 718322 1624841 := bstep (se 2 (by rfl) ⟨609315, by rfl⟩ : syracuseStep 1624841 = 1218631) B1218631
theorem B1624859 : Blo 718322 1624859 := bstep (se 1 (by rfl) ⟨1218644, by rfl⟩ : syracuseStep 1624859 = 2437289) B2437289
theorem B1822439 : Blo 718322 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B6573815 : Blo 718322 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B1167583 : Blo 718322 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B2740979 : Blo 718322 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B1365083 : Blo 718322 1365083 := bstep (se 1 (by rfl) ⟨1023812, by rfl⟩ : syracuseStep 1365083 = 2047625) B2047625
theorem B5461181 : Blo 718322 5461181 := bstep (se 3 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 5461181 = 2047943) B2047943
theorem B1365311 : Blo 718322 1365311 := bstep (se 1 (by rfl) ⟨1023983, by rfl⟩ : syracuseStep 1365311 = 2047967) B2047967
theorem B809023 : Blo 718322 809023 := bstep (se 1 (by rfl) ⟨606767, by rfl⟩ : syracuseStep 809023 = 1213535) B1213535
theorem B8312969 : Blo 718322 8312969 := bstep (se 2 (by rfl) ⟨3117363, by rfl⟩ : syracuseStep 8312969 = 6234727) B6234727
theorem B1825375 : Blo 718322 1825375 := bstep (se 1 (by rfl) ⟨1369031, by rfl⟩ : syracuseStep 1825375 = 2738063) B2738063
theorem B809599 : Blo 718322 809599 := bstep (se 1 (by rfl) ⟨607199, by rfl⟩ : syracuseStep 809599 = 1214399) B1214399
theorem B810751 : Blo 718322 810751 := bstep (se 1 (by rfl) ⟨608063, by rfl⟩ : syracuseStep 810751 = 1216127) B1216127
theorem B909407 : Blo 718322 909407 := bstep (se 1 (by rfl) ⟨682055, by rfl⟩ : syracuseStep 909407 = 1364111) B1364111
theorem B811183 : Blo 718322 811183 := bstep (se 1 (by rfl) ⟨608387, by rfl⟩ : syracuseStep 811183 = 1216775) B1216775
theorem B3465575 : Blo 718322 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B2778071 : Blo 718322 2778071 := bstep (se 1 (by rfl) ⟨2083553, by rfl⟩ : syracuseStep 2778071 = 4167107) B4167107
theorem B5465069 : Blo 718322 5465069 := bstep (se 3 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 5465069 = 2049401) B2049401
theorem B3466361 : Blo 718322 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B1729799 : Blo 718322 1729799 := bstep (se 1 (by rfl) ⟨1297349, by rfl⟩ : syracuseStep 1729799 = 2594699) B2594699
theorem B12282191 : Blo 718322 12282191 := bstep (se 1 (by rfl) ⟨9211643, by rfl⟩ : syracuseStep 12282191 = 18423287) B18423287
theorem B8317577 : Blo 718322 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B912475 : Blo 718322 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B4092059 : Blo 718322 4092059 := bstep (se 1 (by rfl) ⟨3069044, by rfl⟩ : syracuseStep 4092059 = 6138089) B6138089
theorem B36008347 : Blo 718322 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B1078631 : Blo 718322 1078631 := bstep (se 1 (by rfl) ⟨808973, by rfl⟩ : syracuseStep 1078631 = 1617947) B1617947
theorem B718335 : Blo 718322 718335 := bstep (se 1 (by rfl) ⟨538751, by rfl⟩ : syracuseStep 718335 = 1077503) B1077503
theorem B4388455 : Blo 718322 4388455 := bstep (se 1 (by rfl) ⟨3291341, by rfl⟩ : syracuseStep 4388455 = 6582683) B6582683
theorem B718619 : Blo 718322 718619 := bstep (se 1 (by rfl) ⟨538964, by rfl⟩ : syracuseStep 718619 = 1077929) B1077929
theorem B718703 : Blo 718322 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B1079207 : Blo 718322 1079207 := bstep (se 1 (by rfl) ⟨809405, by rfl⟩ : syracuseStep 1079207 = 1618811) B1618811
theorem B1538111 : Blo 718322 1538111 := bstep (se 1 (by rfl) ⟨1153583, by rfl⟩ : syracuseStep 1538111 = 2307167) B2307167
theorem B719463 : Blo 718322 719463 := bstep (se 1 (by rfl) ⟨539597, by rfl⟩ : syracuseStep 719463 = 1079195) B1079195
theorem B719515 : Blo 718322 719515 := bstep (se 1 (by rfl) ⟨539636, by rfl⟩ : syracuseStep 719515 = 1079273) B1079273
theorem B1080059 : Blo 718322 1080059 := bstep (se 1 (by rfl) ⟨810044, by rfl⟩ : syracuseStep 1080059 = 1620089) B1620089
theorem B719903 : Blo 718322 719903 := bstep (se 1 (by rfl) ⟨539927, by rfl⟩ : syracuseStep 719903 = 1079855) B1079855
theorem B1080383 : Blo 718322 1080383 := bstep (se 1 (by rfl) ⟨810287, by rfl⟩ : syracuseStep 1080383 = 1620575) B1620575
theorem B720111 : Blo 718322 720111 := bstep (se 1 (by rfl) ⟨540083, by rfl⟩ : syracuseStep 720111 = 1080167) B1080167
theorem B720127 : Blo 718322 720127 := bstep (se 1 (by rfl) ⟨540095, by rfl⟩ : syracuseStep 720127 = 1080191) B1080191
theorem B720351 : Blo 718322 720351 := bstep (se 1 (by rfl) ⟨540263, by rfl⟩ : syracuseStep 720351 = 1080527) B1080527
theorem B3636737 : Blo 718322 3636737 := bstep (se 2 (by rfl) ⟨1363776, by rfl⟩ : syracuseStep 3636737 = 2727553) B2727553
theorem B720415 : Blo 718322 720415 := bstep (se 1 (by rfl) ⟨540311, by rfl⟩ : syracuseStep 720415 = 1080623) B1080623
theorem B5832593 : Blo 718322 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B720891 : Blo 718322 720891 := bstep (se 1 (by rfl) ⟨540668, by rfl⟩ : syracuseStep 720891 = 1081337) B1081337
theorem B720923 : Blo 718322 720923 := bstep (se 1 (by rfl) ⟨540692, by rfl⟩ : syracuseStep 720923 = 1081385) B1081385
theorem B720927 : Blo 718322 720927 := bstep (se 1 (by rfl) ⟨540695, by rfl⟩ : syracuseStep 720927 = 1081391) B1081391
theorem B1081577 : Blo 718322 1081577 := bstep (se 2 (by rfl) ⟨405591, by rfl⟩ : syracuseStep 1081577 = 811183) B811183
theorem B1081595 : Blo 718322 1081595 := bstep (se 1 (by rfl) ⟨811196, by rfl⟩ : syracuseStep 1081595 = 1622393) B1622393
theorem B2425085 : Blo 718322 2425085 := bstep (se 3 (by rfl) ⟨454703, by rfl⟩ : syracuseStep 2425085 = 909407) B909407
theorem B721223 : Blo 718322 721223 := bstep (se 1 (by rfl) ⟨540917, by rfl⟩ : syracuseStep 721223 = 1081835) B1081835
theorem B1081823 : Blo 718322 1081823 := bstep (se 1 (by rfl) ⟨811367, by rfl⟩ : syracuseStep 1081823 = 1622735) B1622735
theorem B1212907 : Blo 718322 1212907 := bstep (se 1 (by rfl) ⟨909680, by rfl⟩ : syracuseStep 1212907 = 1819361) B1819361
theorem B8782505 : Blo 718322 8782505 := bstep (se 2 (by rfl) ⟨3293439, by rfl⟩ : syracuseStep 8782505 = 6586879) B6586879
theorem B721639 : Blo 718322 721639 := bstep (se 1 (by rfl) ⟨541229, by rfl⟩ : syracuseStep 721639 = 1082459) B1082459
theorem B721691 : Blo 718322 721691 := bstep (se 1 (by rfl) ⟨541268, by rfl⟩ : syracuseStep 721691 = 1082537) B1082537
theorem B7373699 : Blo 718322 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B721855 : Blo 718322 721855 := bstep (se 1 (by rfl) ⟨541391, by rfl⟩ : syracuseStep 721855 = 1082783) B1082783
theorem B11666537 : Blo 718322 11666537 := bstep (se 2 (by rfl) ⟨4374951, by rfl⟩ : syracuseStep 11666537 = 8749903) B8749903
theorem B18449531 : Blo 718322 18449531 := bstep (se 1 (by rfl) ⟨13837148, by rfl⟩ : syracuseStep 18449531 = 27674297) B27674297
theorem B1082879 : Blo 718322 1082879 := bstep (se 1 (by rfl) ⟨812159, by rfl⟩ : syracuseStep 1082879 = 1624319) B1624319
theorem B6915887 : Blo 718322 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B3278663 : Blo 718322 3278663 := bstep (se 1 (by rfl) ⟨2458997, by rfl⟩ : syracuseStep 3278663 = 4917995) B4917995
theorem B1083227 : Blo 718322 1083227 := bstep (se 1 (by rfl) ⟨812420, by rfl⟩ : syracuseStep 1083227 = 1624841) B1624841
theorem B1083239 : Blo 718322 1083239 := bstep (se 1 (by rfl) ⟨812429, by rfl⟩ : syracuseStep 1083239 = 1624859) B1624859
theorem B17500187 : Blo 718322 17500187 := bstep (se 1 (by rfl) ⟨13125140, by rfl⟩ : syracuseStep 17500187 = 26250281) B26250281
theorem B1214959 : Blo 718322 1214959 := bstep (se 1 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 1214959 = 1822439) B1822439
theorem B7408189 : Blo 718322 7408189 := bstep (se 3 (by rfl) ⟨1389035, by rfl⟩ : syracuseStep 7408189 = 2778071) B2778071
theorem B9243629 : Blo 718322 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B6917345 : Blo 718322 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B63901043 : Blo 718322 63901043 := bstep (se 1 (by rfl) ⟨47925782, by rfl⟩ : syracuseStep 63901043 = 95851565) B95851565
theorem B3640787 : Blo 718322 3640787 := bstep (se 1 (by rfl) ⟨2730590, by rfl⟩ : syracuseStep 3640787 = 5461181) B5461181
theorem B2428703 : Blo 718322 2428703 := bstep (se 1 (by rfl) ⟨1821527, by rfl⟩ : syracuseStep 2428703 = 3643055) B3643055
theorem B5541979 : Blo 718322 5541979 := bstep (se 1 (by rfl) ⟨4156484, by rfl⟩ : syracuseStep 5541979 = 8312969) B8312969
theorem B1216633 : Blo 718322 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B56988845 : Blo 718322 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B48011129 : Blo 718322 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B3643379 : Blo 718322 3643379 := bstep (se 1 (by rfl) ⟨2732534, by rfl⟩ : syracuseStep 3643379 = 5465069) B5465069
theorem B1153199 : Blo 718322 1153199 := bstep (se 1 (by rfl) ⟨864899, by rfl⟩ : syracuseStep 1153199 = 1729799) B1729799
theorem B2464249 : Blo 718322 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B3250817 : Blo 718322 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B2431943 : Blo 718322 2431943 := bstep (se 1 (by rfl) ⟨1823957, by rfl⟩ : syracuseStep 2431943 = 3647915) B3647915
theorem B63184049 : Blo 718322 63184049 := bstep (se 2 (by rfl) ⟨23694018, by rfl⟩ : syracuseStep 63184049 = 47388037) B47388037
theorem B2728039 : Blo 718322 2728039 := bstep (se 1 (by rfl) ⟨2046029, by rfl⟩ : syracuseStep 2728039 = 4092059) B4092059
theorem B2728313 : Blo 718322 2728313 := bstep (se 2 (by rfl) ⟨1023117, by rfl⟩ : syracuseStep 2728313 = 2046235) B2046235
theorem B8757881 : Blo 718322 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B2433833 : Blo 718322 2433833 := bstep (se 2 (by rfl) ⟨912687, by rfl⟩ : syracuseStep 2433833 = 1825375) B1825375
theorem B1155961 : Blo 718322 1155961 := bstep (se 2 (by rfl) ⟨433485, by rfl⟩ : syracuseStep 1155961 = 866971) B866971
theorem B1025407 : Blo 718322 1025407 := bstep (se 1 (by rfl) ⟨769055, by rfl⟩ : syracuseStep 1025407 = 1538111) B1538111
theorem B2435183 : Blo 718322 2435183 := bstep (se 1 (by rfl) ⟨1826387, by rfl⟩ : syracuseStep 2435183 = 3652775) B3652775
theorem B1943689 : Blo 718322 1943689 := bstep (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) B1457767
theorem B1026751 : Blo 718322 1026751 := bstep (se 1 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 1026751 = 1540127) B1540127
theorem B1945115 : Blo 718322 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B1618415 : Blo 718322 1618415 := bstep (se 1 (by rfl) ⟨1213811, by rfl⟩ : syracuseStep 1618415 = 2427623) B2427623
theorem B4109737 : Blo 718322 4109737 := bstep (se 2 (by rfl) ⟨1541151, by rfl⟩ : syracuseStep 4109737 = 3082303) B3082303
theorem B1621151 : Blo 718322 1621151 := bstep (se 1 (by rfl) ⟨1215863, by rfl⟩ : syracuseStep 1621151 = 2431727) B2431727
theorem B2736119 : Blo 718322 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B2310383 : Blo 718322 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B1556777 : Blo 718322 1556777 := bstep (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) B1167583
theorem B10405199 : Blo 718322 10405199 := bstep (se 1 (by rfl) ⟨7803899, by rfl⟩ : syracuseStep 10405199 = 15607799) B15607799
theorem B5851273 : Blo 718322 5851273 := bstep (se 2 (by rfl) ⟨2194227, by rfl⟩ : syracuseStep 5851273 = 4388455) B4388455
theorem B1298207 : Blo 718322 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B3888395 : Blo 718322 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B2053583 : Blo 718322 2053583 := bstep (se 1 (by rfl) ⟨1540187, by rfl⟩ : syracuseStep 2053583 = 3080375) B3080375
theorem B5461667 : Blo 718322 5461667 := bstep (se 1 (by rfl) ⟨4096250, by rfl⟩ : syracuseStep 5461667 = 8192501) B8192501
theorem B29546369 : Blo 718322 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B1662059 : Blo 718322 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B3464441 : Blo 718322 3464441 := bstep (se 2 (by rfl) ⟨1299165, by rfl⟩ : syracuseStep 3464441 = 2598331) B2598331
theorem B2055871 : Blo 718322 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B4382543 : Blo 718322 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B1827319 : Blo 718322 1827319 := bstep (se 1 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 1827319 = 2740979) B2740979
theorem B910055 : Blo 718322 910055 := bstep (se 1 (by rfl) ⟨682541, by rfl⟩ : syracuseStep 910055 = 1365083) B1365083
theorem B910207 : Blo 718322 910207 := bstep (se 1 (by rfl) ⟨682655, by rfl⟩ : syracuseStep 910207 = 1365311) B1365311
theorem B13853915 : Blo 718322 13853915 := bstep (se 1 (by rfl) ⟨10390436, by rfl⟩ : syracuseStep 13853915 = 20780873) B20780873
theorem B8188127 : Blo 718322 8188127 := bstep (se 1 (by rfl) ⟨6141095, by rfl⟩ : syracuseStep 8188127 = 12282191) B12282191
theorem B22180205 : Blo 718322 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B1077791 : Blo 718322 1077791 := bstep (se 1 (by rfl) ⟨808343, by rfl⟩ : syracuseStep 1077791 = 1616687) B1616687
theorem B1078697 : Blo 718322 1078697 := bstep (se 2 (by rfl) ⟨404511, by rfl⟩ : syracuseStep 1078697 = 809023) B809023
theorem B29652439 : Blo 718322 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B1079327 : Blo 718322 1079327 := bstep (se 1 (by rfl) ⟨809495, by rfl⟩ : syracuseStep 1079327 = 1618991) B1618991
theorem B1079465 : Blo 718322 1079465 := bstep (se 2 (by rfl) ⟨404799, by rfl⟩ : syracuseStep 1079465 = 809599) B809599
theorem B719087 : Blo 718322 719087 := bstep (se 1 (by rfl) ⟨539315, by rfl⟩ : syracuseStep 719087 = 1078631) B1078631
theorem B16677191 : Blo 718322 16677191 := bstep (se 1 (by rfl) ⟨12507893, by rfl⟩ : syracuseStep 16677191 = 25015787) B25015787
theorem B719471 : Blo 718322 719471 := bstep (se 1 (by rfl) ⟨539603, by rfl⟩ : syracuseStep 719471 = 1079207) B1079207
theorem B1080095 : Blo 718322 1080095 := bstep (se 1 (by rfl) ⟨810071, by rfl⟩ : syracuseStep 1080095 = 1620143) B1620143
theorem B720039 : Blo 718322 720039 := bstep (se 1 (by rfl) ⟨540029, by rfl⟩ : syracuseStep 720039 = 1080059) B1080059
theorem B720255 : Blo 718322 720255 := bstep (se 1 (by rfl) ⟨540191, by rfl⟩ : syracuseStep 720255 = 1080383) B1080383
theorem B1081001 : Blo 718322 1081001 := bstep (se 2 (by rfl) ⟨405375, by rfl⟩ : syracuseStep 1081001 = 810751) B810751
theorem B2424491 : Blo 718322 2424491 := bstep (se 1 (by rfl) ⟨1818368, by rfl⟩ : syracuseStep 2424491 = 3636737) B3636737
theorem B1081247 : Blo 718322 1081247 := bstep (se 1 (by rfl) ⟨810935, by rfl⟩ : syracuseStep 1081247 = 1621871) B1621871
theorem B3637385 : Blo 718322 3637385 := bstep (se 2 (by rfl) ⟨1364019, by rfl⟩ : syracuseStep 3637385 = 2728039) B2728039
theorem B721051 : Blo 718322 721051 := bstep (se 1 (by rfl) ⟨540788, by rfl⟩ : syracuseStep 721051 = 1081577) B1081577
theorem B721063 : Blo 718322 721063 := bstep (se 1 (by rfl) ⟨540797, by rfl⟩ : syracuseStep 721063 = 1081595) B1081595
theorem B721215 : Blo 718322 721215 := bstep (se 1 (by rfl) ⟨540911, by rfl⟩ : syracuseStep 721215 = 1081823) B1081823
theorem B4915799 : Blo 718322 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B6161021 : Blo 718322 6161021 := bstep (se 3 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 6161021 = 2310383) B2310383
theorem B721919 : Blo 718322 721919 := bstep (se 1 (by rfl) ⟨541439, by rfl⟩ : syracuseStep 721919 = 1082879) B1082879
theorem B1541281 : Blo 718322 1541281 := bstep (se 2 (by rfl) ⟨577980, by rfl⟩ : syracuseStep 1541281 = 1155961) B1155961
theorem B1213609 : Blo 718322 1213609 := bstep (se 2 (by rfl) ⟨455103, by rfl⟩ : syracuseStep 1213609 = 910207) B910207
theorem B722151 : Blo 718322 722151 := bstep (se 1 (by rfl) ⟨541613, by rfl⟩ : syracuseStep 722151 = 1083227) B1083227
theorem B722159 : Blo 718322 722159 := bstep (se 1 (by rfl) ⟨541619, by rfl⟩ : syracuseStep 722159 = 1083239) B1083239
theorem B11666791 : Blo 718322 11666791 := bstep (se 1 (by rfl) ⟨8750093, by rfl⟩ : syracuseStep 11666791 = 17500187) B17500187
theorem B2426813 : Blo 718322 2426813 := bstep (se 3 (by rfl) ⟨455027, by rfl⟩ : syracuseStep 2426813 = 910055) B910055
theorem B6162419 : Blo 718322 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B42600695 : Blo 718322 42600695 := bstep (se 1 (by rfl) ⟨31950521, by rfl⟩ : syracuseStep 42600695 = 63901043) B63901043
theorem B2427191 : Blo 718322 2427191 := bstep (se 1 (by rfl) ⟨1820393, by rfl⟩ : syracuseStep 2427191 = 3640787) B3640787
theorem B2591585 : Blo 718322 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B7801697 : Blo 718322 7801697 := bstep (se 2 (by rfl) ⟨2925636, by rfl⟩ : syracuseStep 7801697 = 5851273) B5851273
theorem B2592263 : Blo 718322 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B3641111 : Blo 718322 3641111 := bstep (se 1 (by rfl) ⟨2730833, by rfl⟩ : syracuseStep 3641111 = 5461667) B5461667
theorem B19697579 : Blo 718322 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B2428919 : Blo 718322 2428919 := bstep (se 1 (by rfl) ⟨1821689, by rfl⟩ : syracuseStep 2428919 = 3643379) B3643379
theorem B2167211 : Blo 718322 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B5838587 : Blo 718322 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B44472509 : Blo 718322 44472509 := bstep (se 3 (by rfl) ⟨8338595, by rfl⟩ : syracuseStep 44472509 = 16677191) B16677191
theorem B5479649 : Blo 718322 5479649 := bstep (se 2 (by rfl) ⟨2054868, by rfl⟩ : syracuseStep 5479649 = 4109737) B4109737
theorem B14786803 : Blo 718322 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B4432157 : Blo 718322 4432157 := bstep (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) B1662059
theorem B3285665 : Blo 718322 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B1616327 : Blo 718322 1616327 := bstep (se 1 (by rfl) ⟨1212245, by rfl⟩ : syracuseStep 1616327 = 2424491) B2424491
theorem B1616723 : Blo 718322 1616723 := bstep (se 1 (by rfl) ⟨1212542, by rfl⟩ : syracuseStep 1616723 = 2425085) B2425085
theorem B1617209 : Blo 718322 1617209 := bstep (se 2 (by rfl) ⟨606453, by rfl⟩ : syracuseStep 1617209 = 1212907) B1212907
theorem B2436425 : Blo 718322 2436425 := bstep (se 2 (by rfl) ⟨913659, by rfl⟩ : syracuseStep 2436425 = 1827319) B1827319
theorem B7777691 : Blo 718322 7777691 := bstep (se 1 (by rfl) ⟨5833268, by rfl⟩ : syracuseStep 7777691 = 11666537) B11666537
theorem B12299687 : Blo 718322 12299687 := bstep (se 1 (by rfl) ⟨9224765, by rfl⟩ : syracuseStep 12299687 = 18449531) B18449531
theorem B1619135 : Blo 718322 1619135 := bstep (se 1 (by rfl) ⟨1214351, by rfl⟩ : syracuseStep 1619135 = 2428703) B2428703
theorem B1619945 : Blo 718322 1619945 := bstep (se 2 (by rfl) ⟨607479, by rfl⟩ : syracuseStep 1619945 = 1214959) B1214959
theorem B9877585 : Blo 718322 9877585 := bstep (se 2 (by rfl) ⟨3704094, by rfl⟩ : syracuseStep 9877585 = 7408189) B7408189
theorem B37992563 : Blo 718322 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B768799 : Blo 718322 768799 := bstep (se 1 (by rfl) ⟨576599, by rfl⟩ : syracuseStep 768799 = 1153199) B1153199
theorem B1621295 : Blo 718322 1621295 := bstep (se 1 (by rfl) ⟨1215971, by rfl⟩ : syracuseStep 1621295 = 2431943) B2431943
theorem B42122699 : Blo 718322 42122699 := bstep (se 1 (by rfl) ⟨31592024, by rfl⟩ : syracuseStep 42122699 = 63184049) B63184049
theorem B2309627 : Blo 718322 2309627 := bstep (se 1 (by rfl) ⟨1732220, by rfl⟩ : syracuseStep 2309627 = 3464441) B3464441
theorem B7389305 : Blo 718322 7389305 := bstep (se 2 (by rfl) ⟨2770989, by rfl⟩ : syracuseStep 7389305 = 5541979) B5541979
theorem B1622177 : Blo 718322 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B1818875 : Blo 718322 1818875 := bstep (se 1 (by rfl) ⟨1364156, by rfl⟩ : syracuseStep 1818875 = 2728313) B2728313
theorem B1622555 : Blo 718322 1622555 := bstep (se 1 (by rfl) ⟨1216916, by rfl⟩ : syracuseStep 1622555 = 2433833) B2433833
theorem B1623455 : Blo 718322 1623455 := bstep (se 1 (by rfl) ⟨1217591, by rfl⟩ : syracuseStep 1623455 = 2435183) B2435183
theorem B39536585 : Blo 718322 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B1296743 : Blo 718322 1296743 := bstep (se 1 (by rfl) ⟨972557, by rfl⟩ : syracuseStep 1296743 = 1945115) B1945115
theorem B5458751 : Blo 718322 5458751 := bstep (se 1 (by rfl) ⟨4094063, by rfl⟩ : syracuseStep 5458751 = 8188127) B8188127
theorem B3461885 : Blo 718322 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B11686781 : Blo 718322 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B2741161 : Blo 718322 2741161 := bstep (se 2 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 2741161 = 2055871) B2055871
theorem B1824079 : Blo 718322 1824079 := bstep (se 1 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 1824079 = 2736119) B2736119
theorem B5855003 : Blo 718322 5855003 := bstep (se 1 (by rfl) ⟨4391252, by rfl⟩ : syracuseStep 5855003 = 8782505) B8782505
theorem B4151405 : Blo 718322 4151405 := bstep (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) B1556777
theorem B6936799 : Blo 718322 6936799 := bstep (se 1 (by rfl) ⟨5202599, by rfl⟩ : syracuseStep 6936799 = 10405199) B10405199
theorem B4610591 : Blo 718322 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B2185775 : Blo 718322 2185775 := bstep (se 1 (by rfl) ⟨1639331, by rfl⟩ : syracuseStep 2185775 = 3278663) B3278663
theorem B1367209 : Blo 718322 1367209 := bstep (se 2 (by rfl) ⟨512703, by rfl⟩ : syracuseStep 1367209 = 1025407) B1025407
theorem B4611563 : Blo 718322 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B1369001 : Blo 718322 1369001 := bstep (se 2 (by rfl) ⟨513375, by rfl⟩ : syracuseStep 1369001 = 1026751) B1026751
theorem B1369055 : Blo 718322 1369055 := bstep (se 1 (by rfl) ⟨1026791, by rfl⟩ : syracuseStep 1369055 = 2053583) B2053583
theorem B32007419 : Blo 718322 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B9235943 : Blo 718322 9235943 := bstep (se 1 (by rfl) ⟨6926957, by rfl⟩ : syracuseStep 9235943 = 13853915) B13853915
theorem B1078943 : Blo 718322 1078943 := bstep (se 1 (by rfl) ⟨809207, by rfl⟩ : syracuseStep 1078943 = 1618415) B1618415
theorem B718527 : Blo 718322 718527 := bstep (se 1 (by rfl) ⟨538895, by rfl⟩ : syracuseStep 718527 = 1077791) B1077791
theorem B719131 : Blo 718322 719131 := bstep (se 1 (by rfl) ⟨539348, by rfl⟩ : syracuseStep 719131 = 1078697) B1078697
theorem B719551 : Blo 718322 719551 := bstep (se 1 (by rfl) ⟨539663, by rfl⟩ : syracuseStep 719551 = 1079327) B1079327
theorem B719643 : Blo 718322 719643 := bstep (se 1 (by rfl) ⟨539732, by rfl⟩ : syracuseStep 719643 = 1079465) B1079465
theorem B720063 : Blo 718322 720063 := bstep (se 1 (by rfl) ⟨540047, by rfl⟩ : syracuseStep 720063 = 1080095) B1080095
theorem B1080767 : Blo 718322 1080767 := bstep (se 1 (by rfl) ⟨810575, by rfl⟩ : syracuseStep 1080767 = 1621151) B1621151
theorem B720667 : Blo 718322 720667 := bstep (se 1 (by rfl) ⟨540500, by rfl⟩ : syracuseStep 720667 = 1081001) B1081001
theorem B720831 : Blo 718322 720831 := bstep (se 1 (by rfl) ⟨540623, by rfl⟩ : syracuseStep 720831 = 1081247) B1081247
theorem B2424923 : Blo 718322 2424923 := bstep (se 1 (by rfl) ⟨1818692, by rfl⟩ : syracuseStep 2424923 = 3637385) B3637385
theorem B1081451 : Blo 718322 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B1212583 : Blo 718322 1212583 := bstep (se 1 (by rfl) ⟨909437, by rfl⟩ : syracuseStep 1212583 = 1818875) B1818875
theorem B1081703 : Blo 718322 1081703 := bstep (se 1 (by rfl) ⟨811277, by rfl⟩ : syracuseStep 1081703 = 1622555) B1622555
theorem B3277199 : Blo 718322 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B1082303 : Blo 718322 1082303 := bstep (se 1 (by rfl) ⟨811727, by rfl⟩ : syracuseStep 1082303 = 1623455) B1623455
theorem B3639167 : Blo 718322 3639167 := bstep (se 1 (by rfl) ⟨2729375, by rfl⟩ : syracuseStep 3639167 = 5458751) B5458751
theorem B2427407 : Blo 718322 2427407 := bstep (se 1 (by rfl) ⟨1820555, by rfl⟩ : syracuseStep 2427407 = 3641111) B3641111
theorem B1444807 : Blo 718322 1444807 := bstep (se 1 (by rfl) ⟨1083605, by rfl⟩ : syracuseStep 1444807 = 2167211) B2167211
theorem B3903335 : Blo 718322 3903335 := bstep (se 1 (by rfl) ⟨2927501, by rfl⟩ : syracuseStep 3903335 = 5855003) B5855003
theorem B2954771 : Blo 718322 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B21338279 : Blo 718322 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B2432105 : Blo 718322 2432105 := bstep (se 2 (by rfl) ⟨912039, by rfl⟩ : syracuseStep 2432105 = 1824079) B1824079
theorem B5185127 : Blo 718322 5185127 := bstep (se 1 (by rfl) ⟨3888845, by rfl⟩ : syracuseStep 5185127 = 7777691) B7777691
theorem B8199791 : Blo 718322 8199791 := bstep (se 1 (by rfl) ⟨6149843, by rfl⟩ : syracuseStep 8199791 = 12299687) B12299687
theorem B9249065 : Blo 718322 9249065 := bstep (se 2 (by rfl) ⟨3468399, by rfl⟩ : syracuseStep 9249065 = 6936799) B6936799
theorem B1025065 : Blo 718322 1025065 := bstep (se 2 (by rfl) ⟨384399, by rfl⟩ : syracuseStep 1025065 = 768799) B768799
theorem B4926203 : Blo 718322 4926203 := bstep (se 1 (by rfl) ⟨3694652, by rfl⟩ : syracuseStep 4926203 = 7389305) B7389305
theorem B4107347 : Blo 718322 4107347 := bstep (se 1 (by rfl) ⟨3080510, by rfl⟩ : syracuseStep 4107347 = 6161021) B6161021
theorem B1617875 : Blo 718322 1617875 := bstep (se 1 (by rfl) ⟨1213406, by rfl⟩ : syracuseStep 1617875 = 2426813) B2426813
theorem B26357723 : Blo 718322 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B4108279 : Blo 718322 4108279 := bstep (se 1 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 4108279 = 6162419) B6162419
theorem B1618127 : Blo 718322 1618127 := bstep (se 1 (by rfl) ⟨1213595, by rfl⟩ : syracuseStep 1618127 = 2427191) B2427191
theorem B1618145 : Blo 718322 1618145 := bstep (se 2 (by rfl) ⟨606804, by rfl⟩ : syracuseStep 1618145 = 1213609) B1213609
theorem B3650669 : Blo 718322 3650669 := bstep (se 3 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 3650669 = 1369001) B1369001
theorem B1619279 : Blo 718322 1619279 := bstep (se 1 (by rfl) ⟨1214459, by rfl⟩ : syracuseStep 1619279 = 2428919) B2428919
theorem B2307923 : Blo 718322 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B2767603 : Blo 718322 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B1457183 : Blo 718322 1457183 := bstep (se 1 (by rfl) ⟨1092887, by rfl⟩ : syracuseStep 1457183 = 2185775) B2185775
theorem B3653099 : Blo 718322 3653099 := bstep (se 1 (by rfl) ⟨2739824, by rfl⟩ : syracuseStep 3653099 = 5479649) B5479649
theorem B3457981 : Blo 718322 3457981 := bstep (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) B1296743
theorem B3654881 : Blo 718322 3654881 := bstep (se 2 (by rfl) ⟨1370580, by rfl⟩ : syracuseStep 3654881 = 2741161) B2741161
theorem B1624283 : Blo 718322 1624283 := bstep (se 1 (by rfl) ⟨1218212, by rfl⟩ : syracuseStep 1624283 = 2436425) B2436425
theorem B1822945 : Blo 718322 1822945 := bstep (se 2 (by rfl) ⟨683604, by rfl⟩ : syracuseStep 1822945 = 1367209) B1367209
theorem B19715737 : Blo 718322 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B2055041 : Blo 718322 2055041 := bstep (se 2 (by rfl) ⟨770640, by rfl⟩ : syracuseStep 2055041 = 1541281) B1541281
theorem B15555721 : Blo 718322 15555721 := bstep (se 2 (by rfl) ⟨5833395, by rfl⟩ : syracuseStep 15555721 = 11666791) B11666791
theorem B1727723 : Blo 718322 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B5201131 : Blo 718322 5201131 := bstep (se 1 (by rfl) ⟨3900848, by rfl⟩ : syracuseStep 5201131 = 7801697) B7801697
theorem B1728175 : Blo 718322 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B13131719 : Blo 718322 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B7791187 : Blo 718322 7791187 := bstep (se 1 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 7791187 = 11686781) B11686781
theorem B3892391 : Blo 718322 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B29648339 : Blo 718322 29648339 := bstep (se 1 (by rfl) ⟨22236254, by rfl⟩ : syracuseStep 29648339 = 44472509) B44472509
theorem B3073727 : Blo 718322 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B3074375 : Blo 718322 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B2190443 : Blo 718322 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B113601853 : Blo 718322 113601853 := bstep (se 3 (by rfl) ⟨21300347, by rfl⟩ : syracuseStep 113601853 = 42600695) B42600695
theorem B912703 : Blo 718322 912703 := bstep (se 1 (by rfl) ⟨684527, by rfl⟩ : syracuseStep 912703 = 1369055) B1369055
theorem B1077551 : Blo 718322 1077551 := bstep (se 1 (by rfl) ⟨808163, by rfl⟩ : syracuseStep 1077551 = 1616327) B1616327
theorem B1077815 : Blo 718322 1077815 := bstep (se 1 (by rfl) ⟨808361, by rfl⟩ : syracuseStep 1077815 = 1616723) B1616723
theorem B1078139 : Blo 718322 1078139 := bstep (se 1 (by rfl) ⟨808604, by rfl⟩ : syracuseStep 1078139 = 1617209) B1617209
theorem B6157295 : Blo 718322 6157295 := bstep (se 1 (by rfl) ⟨4617971, by rfl⟩ : syracuseStep 6157295 = 9235943) B9235943
theorem B13170113 : Blo 718322 13170113 := bstep (se 2 (by rfl) ⟨4938792, by rfl⟩ : syracuseStep 13170113 = 9877585) B9877585
theorem B1079423 : Blo 718322 1079423 := bstep (se 1 (by rfl) ⟨809567, by rfl⟩ : syracuseStep 1079423 = 1619135) B1619135
theorem B719295 : Blo 718322 719295 := bstep (se 1 (by rfl) ⟨539471, by rfl⟩ : syracuseStep 719295 = 1078943) B1078943
theorem B1079963 : Blo 718322 1079963 := bstep (se 1 (by rfl) ⟨809972, by rfl⟩ : syracuseStep 1079963 = 1619945) B1619945
theorem B25328375 : Blo 718322 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B1080863 : Blo 718322 1080863 := bstep (se 1 (by rfl) ⟨810647, by rfl⟩ : syracuseStep 1080863 = 1621295) B1621295
theorem B720511 : Blo 718322 720511 := bstep (se 1 (by rfl) ⟨540383, by rfl⟩ : syracuseStep 720511 = 1080767) B1080767
theorem B28081799 : Blo 718322 28081799 := bstep (se 1 (by rfl) ⟨21061349, by rfl⟩ : syracuseStep 28081799 = 42122699) B42122699
theorem B1539751 : Blo 718322 1539751 := bstep (se 1 (by rfl) ⟨1154813, by rfl⟩ : syracuseStep 1539751 = 2309627) B2309627
theorem B720967 : Blo 718322 720967 := bstep (se 1 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 720967 = 1081451) B1081451
theorem B721135 : Blo 718322 721135 := bstep (se 1 (by rfl) ⟨540851, by rfl⟩ : syracuseStep 721135 = 1081703) B1081703
theorem B721535 : Blo 718322 721535 := bstep (se 1 (by rfl) ⟨541151, by rfl⟩ : syracuseStep 721535 = 1082303) B1082303
theorem B10388249 : Blo 718322 10388249 := bstep (se 2 (by rfl) ⟨3895593, by rfl⟩ : syracuseStep 10388249 = 7791187) B7791187
theorem B2426111 : Blo 718322 2426111 := bstep (se 1 (by rfl) ⟨1819583, by rfl⟩ : syracuseStep 2426111 = 3639167) B3639167
theorem B1082855 : Blo 718322 1082855 := bstep (se 1 (by rfl) ⟨812141, by rfl⟩ : syracuseStep 1082855 = 1624283) B1624283
theorem B1969847 : Blo 718322 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B14225519 : Blo 718322 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B1216937 : Blo 718322 1216937 := bstep (se 2 (by rfl) ⟨456351, by rfl⟩ : syracuseStep 1216937 = 912703) B912703
theorem B1151815 : Blo 718322 1151815 := bstep (se 1 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 1151815 = 1727723) B1727723
theorem B7705637 : Blo 718322 7705637 := bstep (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) B1444807
theorem B8754479 : Blo 718322 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B5477705 : Blo 718322 5477705 := bstep (se 2 (by rfl) ⟨2054139, by rfl⟩ : syracuseStep 5477705 = 4108279) B4108279
theorem B6166043 : Blo 718322 6166043 := bstep (se 1 (by rfl) ⟨4624532, by rfl⟩ : syracuseStep 6166043 = 9249065) B9249065
theorem B2430593 : Blo 718322 2430593 := bstep (se 2 (by rfl) ⟨911472, by rfl⟩ : syracuseStep 2430593 = 1822945) B1822945
theorem B2594927 : Blo 718322 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B8198333 : Blo 718322 8198333 := bstep (se 3 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 8198333 = 3074375) B3074375
theorem B19765559 : Blo 718322 19765559 := bstep (se 1 (by rfl) ⟨14824169, by rfl⟩ : syracuseStep 19765559 = 29648339) B29648339
theorem B3284135 : Blo 718322 3284135 := bstep (se 1 (by rfl) ⟨2463101, by rfl⟩ : syracuseStep 3284135 = 4926203) B4926203
theorem B26287649 : Blo 718322 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B17571815 : Blo 718322 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B5841181 : Blo 718322 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B4104863 : Blo 718322 4104863 := bstep (se 1 (by rfl) ⟨3078647, by rfl⟩ : syracuseStep 4104863 = 6157295) B6157295
theorem B2433779 : Blo 718322 2433779 := bstep (se 1 (by rfl) ⟨1825334, by rfl⟩ : syracuseStep 2433779 = 3650669) B3650669
theorem B16885583 : Blo 718322 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B2304233 : Blo 718322 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B2435399 : Blo 718322 2435399 := bstep (se 1 (by rfl) ⟨1826549, by rfl⟩ : syracuseStep 2435399 = 3653099) B3653099
theorem B18721199 : Blo 718322 18721199 := bstep (se 1 (by rfl) ⟨14040899, by rfl⟩ : syracuseStep 18721199 = 28081799) B28081799
theorem B1616615 : Blo 718322 1616615 := bstep (se 1 (by rfl) ⟨1212461, by rfl⟩ : syracuseStep 1616615 = 2424923) B2424923
theorem B1616777 : Blo 718322 1616777 := bstep (se 2 (by rfl) ⟨606291, by rfl⟩ : syracuseStep 1616777 = 1212583) B1212583
theorem B2436587 : Blo 718322 2436587 := bstep (se 1 (by rfl) ⟨1827440, by rfl⟩ : syracuseStep 2436587 = 3654881) B3654881
theorem B1618271 : Blo 718322 1618271 := bstep (se 1 (by rfl) ⟨1213703, by rfl⟩ : syracuseStep 1618271 = 2427407) B2427407
theorem B2602223 : Blo 718322 2602223 := bstep (se 1 (by rfl) ⟨1951667, by rfl⟩ : syracuseStep 2602223 = 3903335) B3903335
theorem B151469137 : Blo 718322 151469137 := bstep (se 2 (by rfl) ⟨56800926, by rfl⟩ : syracuseStep 151469137 = 113601853) B113601853
theorem B1621403 : Blo 718322 1621403 := bstep (se 1 (by rfl) ⟨1216052, by rfl⟩ : syracuseStep 1621403 = 2432105) B2432105
theorem B3456751 : Blo 718322 3456751 := bstep (se 1 (by rfl) ⟨2592563, by rfl⟩ : syracuseStep 3456751 = 5185127) B5185127
theorem B2049151 : Blo 718322 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B2738231 : Blo 718322 2738231 := bstep (se 1 (by rfl) ⟨2053673, by rfl⟩ : syracuseStep 2738231 = 4107347) B4107347
theorem B3690137 : Blo 718322 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B6934841 : Blo 718322 6934841 := bstep (se 2 (by rfl) ⟨2600565, by rfl⟩ : syracuseStep 6934841 = 5201131) B5201131
theorem B971455 : Blo 718322 971455 := bstep (se 1 (by rfl) ⟨728591, by rfl⟩ : syracuseStep 971455 = 1457183) B1457183
theorem B2053001 : Blo 718322 2053001 := bstep (se 2 (by rfl) ⟨769875, by rfl⟩ : syracuseStep 2053001 = 1539751) B1539751
theorem B8739197 : Blo 718322 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B4610641 : Blo 718322 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B1370027 : Blo 718322 1370027 := bstep (se 1 (by rfl) ⟨1027520, by rfl⟩ : syracuseStep 1370027 = 2055041) B2055041
theorem B5466527 : Blo 718322 5466527 := bstep (se 1 (by rfl) ⟨4099895, by rfl⟩ : syracuseStep 5466527 = 8199791) B8199791
theorem B5467013 : Blo 718322 5467013 := bstep (se 4 (by rfl) ⟨512532, by rfl⟩ : syracuseStep 5467013 = 1025065) B1025065
theorem B1078583 : Blo 718322 1078583 := bstep (se 1 (by rfl) ⟨808937, by rfl⟩ : syracuseStep 1078583 = 1617875) B1617875
theorem B1078751 : Blo 718322 1078751 := bstep (se 1 (by rfl) ⟨809063, by rfl⟩ : syracuseStep 1078751 = 1618127) B1618127
theorem B1078763 : Blo 718322 1078763 := bstep (se 1 (by rfl) ⟨809072, by rfl⟩ : syracuseStep 1078763 = 1618145) B1618145
theorem B718367 : Blo 718322 718367 := bstep (se 1 (by rfl) ⟨538775, by rfl⟩ : syracuseStep 718367 = 1077551) B1077551
theorem B718543 : Blo 718322 718543 := bstep (se 1 (by rfl) ⟨538907, by rfl⟩ : syracuseStep 718543 = 1077815) B1077815
theorem B718759 : Blo 718322 718759 := bstep (se 1 (by rfl) ⟨539069, by rfl⟩ : syracuseStep 718759 = 1078139) B1078139
theorem B1079519 : Blo 718322 1079519 := bstep (se 1 (by rfl) ⟨809639, by rfl⟩ : syracuseStep 1079519 = 1619279) B1619279
theorem B8780075 : Blo 718322 8780075 := bstep (se 1 (by rfl) ⟨6585056, by rfl⟩ : syracuseStep 8780075 = 13170113) B13170113
theorem B1538615 : Blo 718322 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B719615 : Blo 718322 719615 := bstep (se 1 (by rfl) ⟨539711, by rfl⟩ : syracuseStep 719615 = 1079423) B1079423
theorem B20740961 : Blo 718322 20740961 := bstep (se 2 (by rfl) ⟨7777860, by rfl⟩ : syracuseStep 20740961 = 15555721) B15555721
theorem B719975 : Blo 718322 719975 := bstep (se 1 (by rfl) ⟨539981, by rfl⟩ : syracuseStep 719975 = 1079963) B1079963
theorem B720575 : Blo 718322 720575 := bstep (se 1 (by rfl) ⟨540431, by rfl⟩ : syracuseStep 720575 = 1080863) B1080863
theorem B721903 : Blo 718322 721903 := bstep (se 1 (by rfl) ⟨541427, by rfl⟩ : syracuseStep 721903 = 1082855) B1082855
theorem B2460091 : Blo 718322 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B1313231 : Blo 718322 1313231 := bstep (se 1 (by rfl) ⟨984923, by rfl⟩ : syracuseStep 1313231 = 1969847) B1969847
theorem B4623227 : Blo 718322 4623227 := bstep (se 1 (by rfl) ⟨3467420, by rfl⟩ : syracuseStep 4623227 = 6934841) B6934841
theorem B5836319 : Blo 718322 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B6919805 : Blo 718322 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B4102973 : Blo 718322 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B3644351 : Blo 718322 3644351 := bstep (se 1 (by rfl) ⟨2733263, by rfl⟩ : syracuseStep 3644351 = 5466527) B5466527
theorem B3644675 : Blo 718322 3644675 := bstep (se 1 (by rfl) ⟨2733506, by rfl⟩ : syracuseStep 3644675 = 5467013) B5467013
theorem B201958849 : Blo 718322 201958849 := bstep (se 2 (by rfl) ⟨75734568, by rfl⟩ : syracuseStep 201958849 = 151469137) B151469137
theorem B6925499 : Blo 718322 6925499 := bstep (se 1 (by rfl) ⟨5194124, by rfl⟩ : syracuseStep 6925499 = 10388249) B10388249
theorem B1617407 : Blo 718322 1617407 := bstep (se 1 (by rfl) ⟨1213055, by rfl⟩ : syracuseStep 1617407 = 2426111) B2426111
theorem B2732201 : Blo 718322 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B9483679 : Blo 718322 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B3651803 : Blo 718322 3651803 := bstep (se 1 (by rfl) ⟨2738852, by rfl⟩ : syracuseStep 3651803 = 5477705) B5477705
theorem B4110695 : Blo 718322 4110695 := bstep (se 1 (by rfl) ⟨3083021, by rfl⟩ : syracuseStep 4110695 = 6166043) B6166043
theorem B1620395 : Blo 718322 1620395 := bstep (se 1 (by rfl) ⟨1215296, by rfl⟩ : syracuseStep 1620395 = 2430593) B2430593
theorem B11714543 : Blo 718322 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B2736575 : Blo 718322 2736575 := bstep (se 1 (by rfl) ⟨2052431, by rfl⟩ : syracuseStep 2736575 = 4104863) B4104863
theorem B1622519 : Blo 718322 1622519 := bstep (se 1 (by rfl) ⟨1216889, by rfl⟩ : syracuseStep 1622519 = 2433779) B2433779
theorem B52708157 : Blo 718322 52708157 := bstep (se 3 (by rfl) ⟨9882779, by rfl⟩ : syracuseStep 52708157 = 19765559) B19765559
theorem B1295273 : Blo 718322 1295273 := bstep (se 2 (by rfl) ⟨485727, by rfl⟩ : syracuseStep 1295273 = 971455) B971455
theorem B11257055 : Blo 718322 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B1623599 : Blo 718322 1623599 := bstep (se 1 (by rfl) ⟨1217699, by rfl⟩ : syracuseStep 1623599 = 2435399) B2435399
theorem B1624391 : Blo 718322 1624391 := bstep (se 1 (by rfl) ⟨1218293, by rfl⟩ : syracuseStep 1624391 = 2436587) B2436587
theorem B6147521 : Blo 718322 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B5853383 : Blo 718322 5853383 := bstep (se 1 (by rfl) ⟨4390037, by rfl⟩ : syracuseStep 5853383 = 8780075) B8780075
theorem B4609001 : Blo 718322 4609001 := bstep (se 2 (by rfl) ⟨1728375, by rfl⟩ : syracuseStep 4609001 = 3456751) B3456751
theorem B7788241 : Blo 718322 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B1825487 : Blo 718322 1825487 := bstep (se 1 (by rfl) ⟨1369115, by rfl⟩ : syracuseStep 1825487 = 2738231) B2738231
theorem B811291 : Blo 718322 811291 := bstep (se 1 (by rfl) ⟨608468, by rfl⟩ : syracuseStep 811291 = 1216937) B1216937
theorem B1368667 : Blo 718322 1368667 := bstep (se 1 (by rfl) ⟨1026500, by rfl⟩ : syracuseStep 1368667 = 2053001) B2053001
theorem B5137091 : Blo 718322 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B5465555 : Blo 718322 5465555 := bstep (se 1 (by rfl) ⟨4099166, by rfl⟩ : syracuseStep 5465555 = 8198333) B8198333
theorem B5826131 : Blo 718322 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B2189423 : Blo 718322 2189423 := bstep (se 1 (by rfl) ⟨1642067, by rfl⟩ : syracuseStep 2189423 = 3284135) B3284135
theorem B17525099 : Blo 718322 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B1535753 : Blo 718322 1535753 := bstep (se 2 (by rfl) ⟨575907, by rfl⟩ : syracuseStep 1535753 = 1151815) B1151815
theorem B913351 : Blo 718322 913351 := bstep (se 1 (by rfl) ⟨685013, by rfl⟩ : syracuseStep 913351 = 1370027) B1370027
theorem B1536155 : Blo 718322 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B12480799 : Blo 718322 12480799 := bstep (se 1 (by rfl) ⟨9360599, by rfl⟩ : syracuseStep 12480799 = 18721199) B18721199
theorem B1077743 : Blo 718322 1077743 := bstep (se 1 (by rfl) ⟨808307, by rfl⟩ : syracuseStep 1077743 = 1616615) B1616615
theorem B1077851 : Blo 718322 1077851 := bstep (se 1 (by rfl) ⟨808388, by rfl⟩ : syracuseStep 1077851 = 1616777) B1616777
theorem B1078847 : Blo 718322 1078847 := bstep (se 1 (by rfl) ⟨809135, by rfl⟩ : syracuseStep 1078847 = 1618271) B1618271
theorem B1734815 : Blo 718322 1734815 := bstep (se 1 (by rfl) ⟨1301111, by rfl⟩ : syracuseStep 1734815 = 2602223) B2602223
theorem B719055 : Blo 718322 719055 := bstep (se 1 (by rfl) ⟨539291, by rfl⟩ : syracuseStep 719055 = 1078583) B1078583
theorem B719167 : Blo 718322 719167 := bstep (se 1 (by rfl) ⟨539375, by rfl⟩ : syracuseStep 719167 = 1078751) B1078751
theorem B719175 : Blo 718322 719175 := bstep (se 1 (by rfl) ⟨539381, by rfl⟩ : syracuseStep 719175 = 1078763) B1078763
theorem B719679 : Blo 718322 719679 := bstep (se 1 (by rfl) ⟨539759, by rfl⟩ : syracuseStep 719679 = 1079519) B1079519
theorem B13827307 : Blo 718322 13827307 := bstep (se 1 (by rfl) ⟨10370480, by rfl⟩ : syracuseStep 13827307 = 20740961) B20740961
theorem B1080935 : Blo 718322 1080935 := bstep (se 1 (by rfl) ⟨810701, by rfl⟩ : syracuseStep 1080935 = 1621403) B1621403
theorem B1081679 : Blo 718322 1081679 := bstep (se 1 (by rfl) ⟨811259, by rfl⟩ : syracuseStep 1081679 = 1622519) B1622519
theorem B1081721 : Blo 718322 1081721 := bstep (se 2 (by rfl) ⟨405645, by rfl⟩ : syracuseStep 1081721 = 811291) B811291
theorem B7504703 : Blo 718322 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B1082399 : Blo 718322 1082399 := bstep (se 1 (by rfl) ⟨811799, by rfl⟩ : syracuseStep 1082399 = 1623599) B1623599
theorem B1082927 : Blo 718322 1082927 := bstep (se 1 (by rfl) ⟨812195, by rfl⟩ : syracuseStep 1082927 = 1624391) B1624391
theorem B3082151 : Blo 718322 3082151 := bstep (se 1 (by rfl) ⟨2311613, by rfl⟩ : syracuseStep 3082151 = 4623227) B4623227
theorem B4098347 : Blo 718322 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B3902255 : Blo 718322 3902255 := bstep (se 1 (by rfl) ⟨2926691, by rfl⟩ : syracuseStep 3902255 = 5853383) B5853383
theorem B3280121 : Blo 718322 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B1216991 : Blo 718322 1216991 := bstep (se 1 (by rfl) ⟨912743, by rfl⟩ : syracuseStep 1216991 = 1825487) B1825487
theorem B2429567 : Blo 718322 2429567 := bstep (se 1 (by rfl) ⟨1822175, by rfl⟩ : syracuseStep 2429567 = 3644351) B3644351
theorem B2429783 : Blo 718322 2429783 := bstep (se 1 (by rfl) ⟨1822337, by rfl⟩ : syracuseStep 2429783 = 3644675) B3644675
theorem B1217801 : Blo 718322 1217801 := bstep (se 2 (by rfl) ⟨456675, by rfl⟩ : syracuseStep 1217801 = 913351) B913351
theorem B4626173 : Blo 718322 4626173 := bstep (se 3 (by rfl) ⟨867407, by rfl⟩ : syracuseStep 4626173 = 1734815) B1734815
theorem B3643703 : Blo 718322 3643703 := bstep (se 1 (by rfl) ⟨2732777, by rfl⟩ : syracuseStep 3643703 = 5465555) B5465555
theorem B1023835 : Blo 718322 1023835 := bstep (se 1 (by rfl) ⟨767876, by rfl⟩ : syracuseStep 1023835 = 1535753) B1535753
theorem B1024103 : Blo 718322 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B2434535 : Blo 718322 2434535 := bstep (se 1 (by rfl) ⟨1825901, by rfl⟩ : syracuseStep 2434535 = 3651803) B3651803
theorem B7809695 : Blo 718322 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B35138771 : Blo 718322 35138771 := bstep (se 1 (by rfl) ⟨26354078, by rfl⟩ : syracuseStep 35138771 = 52708157) B52708157
theorem B863515 : Blo 718322 863515 := bstep (se 1 (by rfl) ⟨647636, by rfl⟩ : syracuseStep 863515 = 1295273) B1295273
theorem B2735315 : Blo 718322 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B3424727 : Blo 718322 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B3884087 : Blo 718322 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B1459615 : Blo 718322 1459615 := bstep (se 1 (by rfl) ⟨1094711, by rfl⟩ : syracuseStep 1459615 = 2189423) B2189423
theorem B11683399 : Blo 718322 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B50579621 : Blo 718322 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B1821467 : Blo 718322 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B2740463 : Blo 718322 2740463 := bstep (se 1 (by rfl) ⟨2055347, by rfl⟩ : syracuseStep 2740463 = 4110695) B4110695
theorem B18436409 : Blo 718322 18436409 := bstep (se 2 (by rfl) ⟨6913653, by rfl⟩ : syracuseStep 18436409 = 13827307) B13827307
theorem B1824383 : Blo 718322 1824383 := bstep (se 1 (by rfl) ⟨1368287, by rfl⟩ : syracuseStep 1824383 = 2736575) B2736575
theorem B1824889 : Blo 718322 1824889 := bstep (se 2 (by rfl) ⟨684333, by rfl⟩ : syracuseStep 1824889 = 1368667) B1368667
theorem B269278465 : Blo 718322 269278465 := bstep (se 2 (by rfl) ⟨100979424, by rfl⟩ : syracuseStep 269278465 = 201958849) B201958849
theorem B3890879 : Blo 718322 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B3072667 : Blo 718322 3072667 := bstep (se 1 (by rfl) ⟨2304500, by rfl⟩ : syracuseStep 3072667 = 4609001) B4609001
theorem B4613203 : Blo 718322 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B16641065 : Blo 718322 16641065 := bstep (se 2 (by rfl) ⟨6240399, by rfl⟩ : syracuseStep 16641065 = 12480799) B12480799
theorem B3501949 : Blo 718322 3501949 := bstep (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) B1313231
theorem B4616999 : Blo 718322 4616999 := bstep (se 1 (by rfl) ⟨3462749, by rfl⟩ : syracuseStep 4616999 = 6925499) B6925499
theorem B10384321 : Blo 718322 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B1078271 : Blo 718322 1078271 := bstep (se 1 (by rfl) ⟨808703, by rfl⟩ : syracuseStep 1078271 = 1617407) B1617407
theorem B718495 : Blo 718322 718495 := bstep (se 1 (by rfl) ⟨538871, by rfl⟩ : syracuseStep 718495 = 1077743) B1077743
theorem B718567 : Blo 718322 718567 := bstep (se 1 (by rfl) ⟨538925, by rfl⟩ : syracuseStep 718567 = 1077851) B1077851
theorem B719231 : Blo 718322 719231 := bstep (se 1 (by rfl) ⟨539423, by rfl⟩ : syracuseStep 719231 = 1078847) B1078847
theorem B1080263 : Blo 718322 1080263 := bstep (se 1 (by rfl) ⟨810197, by rfl⟩ : syracuseStep 1080263 = 1620395) B1620395
theorem B720623 : Blo 718322 720623 := bstep (se 1 (by rfl) ⟨540467, by rfl⟩ : syracuseStep 720623 = 1080935) B1080935
theorem B721119 : Blo 718322 721119 := bstep (se 1 (by rfl) ⟨540839, by rfl⟩ : syracuseStep 721119 = 1081679) B1081679
theorem B721147 : Blo 718322 721147 := bstep (se 1 (by rfl) ⟨540860, by rfl⟩ : syracuseStep 721147 = 1081721) B1081721
theorem B721599 : Blo 718322 721599 := bstep (se 1 (by rfl) ⟨541199, by rfl⟩ : syracuseStep 721599 = 1082399) B1082399
theorem B2589391 : Blo 718322 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B4096889 : Blo 718322 4096889 := bstep (se 2 (by rfl) ⟨1536333, by rfl⟩ : syracuseStep 4096889 = 3072667) B3072667
theorem B721951 : Blo 718322 721951 := bstep (se 1 (by rfl) ⟨541463, by rfl⟩ : syracuseStep 721951 = 1082927) B1082927
theorem B33719747 : Blo 718322 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B1214311 : Blo 718322 1214311 := bstep (se 1 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 1214311 = 1821467) B1821467
theorem B12290939 : Blo 718322 12290939 := bstep (se 1 (by rfl) ⟨9218204, by rfl⟩ : syracuseStep 12290939 = 18436409) B18436409
theorem B1216255 : Blo 718322 1216255 := bstep (se 1 (by rfl) ⟨912191, by rfl⟩ : syracuseStep 1216255 = 1824383) B1824383
theorem B3084115 : Blo 718322 3084115 := bstep (se 1 (by rfl) ⟨2313086, by rfl⟩ : syracuseStep 3084115 = 4626173) B4626173
theorem B2429135 : Blo 718322 2429135 := bstep (se 1 (by rfl) ⟨1821851, by rfl⟩ : syracuseStep 2429135 = 3643703) B3643703
theorem B1151353 : Blo 718322 1151353 := bstep (se 2 (by rfl) ⟨431757, by rfl⟩ : syracuseStep 1151353 = 863515) B863515
theorem B2593919 : Blo 718322 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B44376173 : Blo 718322 44376173 := bstep (se 3 (by rfl) ⟨8320532, by rfl⟩ : syracuseStep 44376173 = 16641065) B16641065
theorem B2433185 : Blo 718322 2433185 := bstep (se 2 (by rfl) ⟨912444, by rfl⟩ : syracuseStep 2433185 = 1824889) B1824889
theorem B2730941 : Blo 718322 2730941 := bstep (se 3 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 2730941 = 1024103) B1024103
theorem B2732231 : Blo 718322 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B2601503 : Blo 718322 2601503 := bstep (se 1 (by rfl) ⟨1951127, by rfl⟩ : syracuseStep 2601503 = 3902255) B3902255
theorem B1946153 : Blo 718322 1946153 := bstep (se 2 (by rfl) ⟨729807, by rfl⟩ : syracuseStep 1946153 = 1459615) B1459615
theorem B15577865 : Blo 718322 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B1619711 : Blo 718322 1619711 := bstep (se 1 (by rfl) ⟨1214783, by rfl⟩ : syracuseStep 1619711 = 2429567) B2429567
theorem B1619855 : Blo 718322 1619855 := bstep (se 1 (by rfl) ⟨1214891, by rfl⟩ : syracuseStep 1619855 = 2429783) B2429783
theorem B4669265 : Blo 718322 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B1623023 : Blo 718322 1623023 := bstep (se 1 (by rfl) ⟨1217267, by rfl⟩ : syracuseStep 1623023 = 2434535) B2434535
theorem B13845761 : Blo 718322 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B1823543 : Blo 718322 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B1365113 : Blo 718322 1365113 := bstep (se 2 (by rfl) ⟨511917, by rfl⟩ : syracuseStep 1365113 = 1023835) B1023835
theorem B5003135 : Blo 718322 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B9132605 : Blo 718322 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B2054767 : Blo 718322 2054767 := bstep (se 1 (by rfl) ⟨1541075, by rfl⟩ : syracuseStep 2054767 = 3082151) B3082151
theorem B6150937 : Blo 718322 6150937 := bstep (se 2 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 6150937 = 4613203) B4613203
theorem B2186747 : Blo 718322 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B1826975 : Blo 718322 1826975 := bstep (se 1 (by rfl) ⟨1370231, by rfl⟩ : syracuseStep 1826975 = 2740463) B2740463
theorem B811327 : Blo 718322 811327 := bstep (se 1 (by rfl) ⟨608495, by rfl⟩ : syracuseStep 811327 = 1216991) B1216991
theorem B811867 : Blo 718322 811867 := bstep (se 1 (by rfl) ⟨608900, by rfl⟩ : syracuseStep 811867 = 1217801) B1217801
theorem B5206463 : Blo 718322 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B23425847 : Blo 718322 23425847 := bstep (se 1 (by rfl) ⟨17569385, by rfl⟩ : syracuseStep 23425847 = 35138771) B35138771
theorem B3077999 : Blo 718322 3077999 := bstep (se 1 (by rfl) ⟨2308499, by rfl⟩ : syracuseStep 3077999 = 4616999) B4616999
theorem B718847 : Blo 718322 718847 := bstep (se 1 (by rfl) ⟨539135, by rfl⟩ : syracuseStep 718847 = 1078271) B1078271
theorem B359037953 : Blo 718322 359037953 := bstep (se 2 (by rfl) ⟨134639232, by rfl⟩ : syracuseStep 359037953 = 269278465) B269278465
theorem B720175 : Blo 718322 720175 := bstep (se 1 (by rfl) ⟨540131, by rfl⟩ : syracuseStep 720175 = 1080263) B1080263
theorem B1081769 : Blo 718322 1081769 := bstep (se 2 (by rfl) ⟨405663, by rfl⟩ : syracuseStep 1081769 = 811327) B811327
theorem B1082015 : Blo 718322 1082015 := bstep (se 1 (by rfl) ⟨811511, by rfl⟩ : syracuseStep 1082015 = 1623023) B1623023
theorem B1082489 : Blo 718322 1082489 := bstep (se 2 (by rfl) ⟨405933, by rfl⟩ : syracuseStep 1082489 = 811867) B811867
theorem B8193959 : Blo 718322 8193959 := bstep (se 1 (by rfl) ⟨6145469, by rfl⟩ : syracuseStep 8193959 = 12290939) B12290939
theorem B3640301 : Blo 718322 3640301 := bstep (se 3 (by rfl) ⟨682556, by rfl⟩ : syracuseStep 3640301 = 1365113) B1365113
theorem B1215695 : Blo 718322 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B89919325 : Blo 718322 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B1217983 : Blo 718322 1217983 := bstep (se 1 (by rfl) ⟨913487, by rfl⟩ : syracuseStep 1217983 = 1826975) B1826975
theorem B8201249 : Blo 718322 8201249 := bstep (se 2 (by rfl) ⟨3075468, by rfl⟩ : syracuseStep 8201249 = 6150937) B6150937
theorem B2731259 : Blo 718322 2731259 := bstep (se 1 (by rfl) ⟨2048444, by rfl⟩ : syracuseStep 2731259 = 4096889) B4096889
theorem B5189741 : Blo 718322 5189741 := bstep (se 3 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 5189741 = 1946153) B1946153
theorem B6140549 : Blo 718322 6140549 := bstep (se 4 (by rfl) ⟨575676, by rfl⟩ : syracuseStep 6140549 = 1151353) B1151353
theorem B1619081 : Blo 718322 1619081 := bstep (se 2 (by rfl) ⟨607155, by rfl⟩ : syracuseStep 1619081 = 1214311) B1214311
theorem B1619423 : Blo 718322 1619423 := bstep (se 1 (by rfl) ⟨1214567, by rfl⟩ : syracuseStep 1619423 = 2429135) B2429135
theorem B13810085 : Blo 718322 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B1457831 : Blo 718322 1457831 := bstep (se 1 (by rfl) ⟨1093373, by rfl⟩ : syracuseStep 1457831 = 2186747) B2186747
theorem B1621673 : Blo 718322 1621673 := bstep (se 2 (by rfl) ⟨608127, by rfl⟩ : syracuseStep 1621673 = 1216255) B1216255
theorem B4112153 : Blo 718322 4112153 := bstep (se 2 (by rfl) ⟨1542057, by rfl⟩ : syracuseStep 4112153 = 3084115) B3084115
theorem B1622123 : Blo 718322 1622123 := bstep (se 1 (by rfl) ⟨1216592, by rfl⟩ : syracuseStep 1622123 = 2433185) B2433185
theorem B1820627 : Blo 718322 1820627 := bstep (se 1 (by rfl) ⟨1365470, by rfl⟩ : syracuseStep 1820627 = 2730941) B2730941
theorem B1821487 : Blo 718322 1821487 := bstep (se 1 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 1821487 = 2732231) B2732231
theorem B15617231 : Blo 718322 15617231 := bstep (se 1 (by rfl) ⟨11712923, by rfl⟩ : syracuseStep 15617231 = 23425847) B23425847
theorem B2739689 : Blo 718322 2739689 := bstep (se 2 (by rfl) ⟨1027383, by rfl⟩ : syracuseStep 2739689 = 2054767) B2054767
theorem B2051999 : Blo 718322 2051999 := bstep (se 1 (by rfl) ⟨1538999, by rfl⟩ : syracuseStep 2051999 = 3077999) B3077999
theorem B239358635 : Blo 718322 239358635 := bstep (se 1 (by rfl) ⟨179518976, by rfl⟩ : syracuseStep 239358635 = 359037953) B359037953
theorem B9230507 : Blo 718322 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B1729279 : Blo 718322 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B3335423 : Blo 718322 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B6088403 : Blo 718322 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B29584115 : Blo 718322 29584115 := bstep (se 1 (by rfl) ⟨22188086, by rfl⟩ : syracuseStep 29584115 = 44376173) B44376173
theorem B3470975 : Blo 718322 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B1734335 : Blo 718322 1734335 := bstep (se 1 (by rfl) ⟨1300751, by rfl⟩ : syracuseStep 1734335 = 2601503) B2601503
theorem B10385243 : Blo 718322 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B1079807 : Blo 718322 1079807 := bstep (se 1 (by rfl) ⟨809855, by rfl⟩ : syracuseStep 1079807 = 1619711) B1619711
theorem B1079903 : Blo 718322 1079903 := bstep (se 1 (by rfl) ⟨809927, by rfl⟩ : syracuseStep 1079903 = 1619855) B1619855
theorem B3112843 : Blo 718322 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B1081415 : Blo 718322 1081415 := bstep (se 1 (by rfl) ⟨811061, by rfl⟩ : syracuseStep 1081415 = 1622123) B1622123
theorem B721179 : Blo 718322 721179 := bstep (se 1 (by rfl) ⟨540884, by rfl⟩ : syracuseStep 721179 = 1081769) B1081769
theorem B721343 : Blo 718322 721343 := bstep (se 1 (by rfl) ⟨541007, by rfl⟩ : syracuseStep 721343 = 1082015) B1082015
theorem B721659 : Blo 718322 721659 := bstep (se 1 (by rfl) ⟨541244, by rfl⟩ : syracuseStep 721659 = 1082489) B1082489
theorem B1213751 : Blo 718322 1213751 := bstep (se 1 (by rfl) ⟨910313, by rfl⟩ : syracuseStep 1213751 = 1820627) B1820627
theorem B2426867 : Blo 718322 2426867 := bstep (se 1 (by rfl) ⟨1820150, by rfl⟩ : syracuseStep 2426867 = 3640301) B3640301
theorem B2428649 : Blo 718322 2428649 := bstep (se 2 (by rfl) ⟨910743, by rfl⟩ : syracuseStep 2428649 = 1821487) B1821487
theorem B1156223 : Blo 718322 1156223 := bstep (se 1 (by rfl) ⟨867167, by rfl⟩ : syracuseStep 1156223 = 1734335) B1734335
theorem B6923495 : Blo 718322 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B479569733 : Blo 718322 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B8894461 : Blo 718322 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B9222821 : Blo 718322 9222821 := bstep (se 4 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 9222821 = 1729279) B1729279
theorem B16235741 : Blo 718322 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B1623977 : Blo 718322 1623977 := bstep (se 2 (by rfl) ⟨608991, by rfl⟩ : syracuseStep 1623977 = 1217983) B1217983
theorem B1820839 : Blo 718322 1820839 := bstep (se 1 (by rfl) ⟨1365629, by rfl⟩ : syracuseStep 1820839 = 2731259) B2731259
theorem B3459827 : Blo 718322 3459827 := bstep (se 1 (by rfl) ⟨2594870, by rfl⟩ : syracuseStep 3459827 = 5189741) B5189741
theorem B2313983 : Blo 718322 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B971887 : Blo 718322 971887 := bstep (se 1 (by rfl) ⟨728915, by rfl⟩ : syracuseStep 971887 = 1457831) B1457831
theorem B4150457 : Blo 718322 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B2741435 : Blo 718322 2741435 := bstep (se 1 (by rfl) ⟨2056076, by rfl⟩ : syracuseStep 2741435 = 4112153) B4112153
theorem B5462639 : Blo 718322 5462639 := bstep (se 1 (by rfl) ⟨4096979, by rfl⟩ : syracuseStep 5462639 = 8193959) B8193959
theorem B810463 : Blo 718322 810463 := bstep (se 1 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 810463 = 1215695) B1215695
theorem B10411487 : Blo 718322 10411487 := bstep (se 1 (by rfl) ⟨7808615, by rfl⟩ : syracuseStep 10411487 = 15617231) B15617231
theorem B1826459 : Blo 718322 1826459 := bstep (se 1 (by rfl) ⟨1369844, by rfl⟩ : syracuseStep 1826459 = 2739689) B2739689
theorem B1367999 : Blo 718322 1367999 := bstep (se 1 (by rfl) ⟨1025999, by rfl⟩ : syracuseStep 1367999 = 2051999) B2051999
theorem B159572423 : Blo 718322 159572423 := bstep (se 1 (by rfl) ⟨119679317, by rfl⟩ : syracuseStep 159572423 = 239358635) B239358635
theorem B6153671 : Blo 718322 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B5467499 : Blo 718322 5467499 := bstep (se 1 (by rfl) ⟨4100624, by rfl⟩ : syracuseStep 5467499 = 8201249) B8201249
theorem B19722743 : Blo 718322 19722743 := bstep (se 1 (by rfl) ⟨14792057, by rfl⟩ : syracuseStep 19722743 = 29584115) B29584115
theorem B4093699 : Blo 718322 4093699 := bstep (se 1 (by rfl) ⟨3070274, by rfl⟩ : syracuseStep 4093699 = 6140549) B6140549
theorem B1079387 : Blo 718322 1079387 := bstep (se 1 (by rfl) ⟨809540, by rfl⟩ : syracuseStep 1079387 = 1619081) B1619081
theorem B1079615 : Blo 718322 1079615 := bstep (se 1 (by rfl) ⟨809711, by rfl⟩ : syracuseStep 1079615 = 1619423) B1619423
theorem B9206723 : Blo 718322 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B719871 : Blo 718322 719871 := bstep (se 1 (by rfl) ⟨539903, by rfl⟩ : syracuseStep 719871 = 1079807) B1079807
theorem B719935 : Blo 718322 719935 := bstep (se 1 (by rfl) ⟨539951, by rfl⟩ : syracuseStep 719935 = 1079903) B1079903
theorem B1081115 : Blo 718322 1081115 := bstep (se 1 (by rfl) ⟨810836, by rfl⟩ : syracuseStep 1081115 = 1621673) B1621673
theorem B720943 : Blo 718322 720943 := bstep (se 1 (by rfl) ⟨540707, by rfl⟩ : syracuseStep 720943 = 1081415) B1081415
theorem B1082651 : Blo 718322 1082651 := bstep (se 1 (by rfl) ⟨811988, by rfl⟩ : syracuseStep 1082651 = 1623977) B1623977
theorem B1542655 : Blo 718322 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B2427785 : Blo 718322 2427785 := bstep (se 2 (by rfl) ⟨910419, by rfl⟩ : syracuseStep 2427785 = 1820839) B1820839
theorem B3641759 : Blo 718322 3641759 := bstep (se 1 (by rfl) ⟨2731319, by rfl⟩ : syracuseStep 3641759 = 5462639) B5462639
theorem B1217639 : Blo 718322 1217639 := bstep (se 1 (by rfl) ⟨913229, by rfl⟩ : syracuseStep 1217639 = 1826459) B1826459
theorem B4102447 : Blo 718322 4102447 := bstep (se 1 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 4102447 = 6153671) B6153671
theorem B3644999 : Blo 718322 3644999 := bstep (se 1 (by rfl) ⟨2733749, by rfl⟩ : syracuseStep 3644999 = 5467499) B5467499
theorem B13148495 : Blo 718322 13148495 := bstep (se 1 (by rfl) ⟨9861371, by rfl⟩ : syracuseStep 13148495 = 19722743) B19722743
theorem B43295309 : Blo 718322 43295309 := bstep (se 3 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 43295309 = 16235741) B16235741
theorem B6137815 : Blo 718322 6137815 := bstep (se 1 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 6137815 = 9206723) B9206723
theorem B1617911 : Blo 718322 1617911 := bstep (se 1 (by rfl) ⟨1213433, by rfl⟩ : syracuseStep 1617911 = 2426867) B2426867
theorem B2306551 : Blo 718322 2306551 := bstep (se 1 (by rfl) ⟨1729913, by rfl⟩ : syracuseStep 2306551 = 3459827) B3459827
theorem B1619099 : Blo 718322 1619099 := bstep (se 1 (by rfl) ⟨1214324, by rfl⟩ : syracuseStep 1619099 = 2428649) B2428649
theorem B18462653 : Blo 718322 18462653 := bstep (se 3 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 18462653 = 6923495) B6923495
theorem B2766971 : Blo 718322 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B106381615 : Blo 718322 106381615 := bstep (se 1 (by rfl) ⟨79786211, by rfl⟩ : syracuseStep 106381615 = 159572423) B159572423
theorem B770815 : Blo 718322 770815 := bstep (se 1 (by rfl) ⟨578111, by rfl⟩ : syracuseStep 770815 = 1156223) B1156223
theorem B1295849 : Blo 718322 1295849 := bstep (se 2 (by rfl) ⟨485943, by rfl⟩ : syracuseStep 1295849 = 971887) B971887
theorem B5458265 : Blo 718322 5458265 := bstep (se 2 (by rfl) ⟨2046849, by rfl⟩ : syracuseStep 5458265 = 4093699) B4093699
theorem B6148547 : Blo 718322 6148547 := bstep (se 1 (by rfl) ⟨4611410, by rfl⟩ : syracuseStep 6148547 = 9222821) B9222821
theorem B809167 : Blo 718322 809167 := bstep (se 1 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 809167 = 1213751) B1213751
theorem B1827623 : Blo 718322 1827623 := bstep (se 1 (by rfl) ⟨1370717, by rfl⟩ : syracuseStep 1827623 = 2741435) B2741435
theorem B6940991 : Blo 718322 6940991 := bstep (se 1 (by rfl) ⟨5205743, by rfl⟩ : syracuseStep 6940991 = 10411487) B10411487
theorem B911999 : Blo 718322 911999 := bstep (se 1 (by rfl) ⟨683999, by rfl⟩ : syracuseStep 911999 = 1367999) B1367999
theorem B319713155 : Blo 718322 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B11859281 : Blo 718322 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B719591 : Blo 718322 719591 := bstep (se 1 (by rfl) ⟨539693, by rfl⟩ : syracuseStep 719591 = 1079387) B1079387
theorem B719743 : Blo 718322 719743 := bstep (se 1 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 719743 = 1079615) B1079615
theorem B1080617 : Blo 718322 1080617 := bstep (se 2 (by rfl) ⟨405231, by rfl⟩ : syracuseStep 1080617 = 810463) B810463
theorem B720743 : Blo 718322 720743 := bstep (se 1 (by rfl) ⟨540557, by rfl⟩ : syracuseStep 720743 = 1081115) B1081115
theorem B721767 : Blo 718322 721767 := bstep (se 1 (by rfl) ⟨541325, by rfl⟩ : syracuseStep 721767 = 1082651) B1082651
theorem B3638843 : Blo 718322 3638843 := bstep (se 1 (by rfl) ⟨2729132, by rfl⟩ : syracuseStep 3638843 = 5458265) B5458265
theorem B8227493 : Blo 718322 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B2427839 : Blo 718322 2427839 := bstep (se 1 (by rfl) ⟨1820879, by rfl⟩ : syracuseStep 2427839 = 3641759) B3641759
theorem B4099031 : Blo 718322 4099031 := bstep (se 1 (by rfl) ⟨3074273, by rfl⟩ : syracuseStep 4099031 = 6148547) B6148547
theorem B2429999 : Blo 718322 2429999 := bstep (se 1 (by rfl) ⟨1822499, by rfl⟩ : syracuseStep 2429999 = 3644999) B3644999
theorem B7378589 : Blo 718322 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B1218415 : Blo 718322 1218415 := bstep (se 1 (by rfl) ⟨913811, by rfl⟩ : syracuseStep 1218415 = 1827623) B1827623
theorem B4627327 : Blo 718322 4627327 := bstep (se 1 (by rfl) ⟨3470495, by rfl⟩ : syracuseStep 4627327 = 6940991) B6940991
theorem B2431997 : Blo 718322 2431997 := bstep (se 3 (by rfl) ⟨455999, by rfl⟩ : syracuseStep 2431997 = 911999) B911999
theorem B7906187 : Blo 718322 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B1618523 : Blo 718322 1618523 := bstep (se 1 (by rfl) ⟨1213892, by rfl⟩ : syracuseStep 1618523 = 2427785) B2427785
theorem B3455597 : Blo 718322 3455597 := bstep (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) B1295849
theorem B4111013 : Blo 718322 4111013 := bstep (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) B770815
theorem B8765663 : Blo 718322 8765663 := bstep (se 1 (by rfl) ⟨6574247, by rfl⟩ : syracuseStep 8765663 = 13148495) B13148495
theorem B213142103 : Blo 718322 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B12308435 : Blo 718322 12308435 := bstep (se 1 (by rfl) ⟨9231326, by rfl⟩ : syracuseStep 12308435 = 18462653) B18462653
theorem B141842153 : Blo 718322 141842153 := bstep (se 2 (by rfl) ⟨53190807, by rfl⟩ : syracuseStep 141842153 = 106381615) B106381615
theorem B8183753 : Blo 718322 8183753 := bstep (se 2 (by rfl) ⟨3068907, by rfl⟩ : syracuseStep 8183753 = 6137815) B6137815
theorem B811759 : Blo 718322 811759 := bstep (se 1 (by rfl) ⟨608819, by rfl⟩ : syracuseStep 811759 = 1217639) B1217639
theorem B28863539 : Blo 718322 28863539 := bstep (se 1 (by rfl) ⟨21647654, by rfl⟩ : syracuseStep 28863539 = 43295309) B43295309
theorem B3075401 : Blo 718322 3075401 := bstep (se 2 (by rfl) ⟨1153275, by rfl⟩ : syracuseStep 3075401 = 2306551) B2306551
theorem B1078607 : Blo 718322 1078607 := bstep (se 1 (by rfl) ⟨808955, by rfl⟩ : syracuseStep 1078607 = 1617911) B1617911
theorem B1078889 : Blo 718322 1078889 := bstep (se 2 (by rfl) ⟨404583, by rfl⟩ : syracuseStep 1078889 = 809167) B809167
theorem B5469929 : Blo 718322 5469929 := bstep (se 2 (by rfl) ⟨2051223, by rfl⟩ : syracuseStep 5469929 = 4102447) B4102447
theorem B1079399 : Blo 718322 1079399 := bstep (se 1 (by rfl) ⟨809549, by rfl⟩ : syracuseStep 1079399 = 1619099) B1619099
theorem B720411 : Blo 718322 720411 := bstep (se 1 (by rfl) ⟨540308, by rfl⟩ : syracuseStep 720411 = 1080617) B1080617
theorem B1082345 : Blo 718322 1082345 := bstep (se 2 (by rfl) ⟨405879, by rfl⟩ : syracuseStep 1082345 = 811759) B811759
theorem B2425895 : Blo 718322 2425895 := bstep (se 1 (by rfl) ⟨1819421, by rfl⟩ : syracuseStep 2425895 = 3638843) B3638843
theorem B4919059 : Blo 718322 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B19242359 : Blo 718322 19242359 := bstep (se 1 (by rfl) ⟨14431769, by rfl⟩ : syracuseStep 19242359 = 28863539) B28863539
theorem B3646619 : Blo 718322 3646619 := bstep (se 1 (by rfl) ⟨2734964, by rfl⟩ : syracuseStep 3646619 = 5469929) B5469929
theorem B6169769 : Blo 718322 6169769 := bstep (se 2 (by rfl) ⟨2313663, by rfl⟩ : syracuseStep 6169769 = 4627327) B4627327
theorem B2303731 : Blo 718322 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B23375101 : Blo 718322 23375101 := bstep (se 3 (by rfl) ⟨4382831, by rfl⟩ : syracuseStep 23375101 = 8765663) B8765663
theorem B142094735 : Blo 718322 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B5484995 : Blo 718322 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B1618559 : Blo 718322 1618559 := bstep (se 1 (by rfl) ⟨1213919, by rfl⟩ : syracuseStep 1618559 = 2427839) B2427839
theorem B2732687 : Blo 718322 2732687 := bstep (se 1 (by rfl) ⟨2049515, by rfl⟩ : syracuseStep 2732687 = 4099031) B4099031
theorem B8205623 : Blo 718322 8205623 := bstep (se 1 (by rfl) ⟨6154217, by rfl⟩ : syracuseStep 8205623 = 12308435) B12308435
theorem B1619999 : Blo 718322 1619999 := bstep (se 1 (by rfl) ⟨1214999, by rfl⟩ : syracuseStep 1619999 = 2429999) B2429999
theorem B1621331 : Blo 718322 1621331 := bstep (se 1 (by rfl) ⟨1215998, by rfl⟩ : syracuseStep 1621331 = 2431997) B2431997
theorem B5455835 : Blo 718322 5455835 := bstep (se 1 (by rfl) ⟨4091876, by rfl⟩ : syracuseStep 5455835 = 8183753) B8183753
theorem B2050267 : Blo 718322 2050267 := bstep (se 1 (by rfl) ⟨1537700, by rfl⟩ : syracuseStep 2050267 = 3075401) B3075401
theorem B1624553 : Blo 718322 1624553 := bstep (se 2 (by rfl) ⟨609207, by rfl⟩ : syracuseStep 1624553 = 1218415) B1218415
theorem B2740675 : Blo 718322 2740675 := bstep (se 1 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 2740675 = 4111013) B4111013
theorem B94561435 : Blo 718322 94561435 := bstep (se 1 (by rfl) ⟨70921076, by rfl⟩ : syracuseStep 94561435 = 141842153) B141842153
theorem B5270791 : Blo 718322 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B1079015 : Blo 718322 1079015 := bstep (se 1 (by rfl) ⟨809261, by rfl⟩ : syracuseStep 1079015 = 1618523) B1618523
theorem B719071 : Blo 718322 719071 := bstep (se 1 (by rfl) ⟨539303, by rfl⟩ : syracuseStep 719071 = 1078607) B1078607
theorem B719259 : Blo 718322 719259 := bstep (se 1 (by rfl) ⟨539444, by rfl⟩ : syracuseStep 719259 = 1078889) B1078889
theorem B719599 : Blo 718322 719599 := bstep (se 1 (by rfl) ⟨539699, by rfl⟩ : syracuseStep 719599 = 1079399) B1079399
theorem B721563 : Blo 718322 721563 := bstep (se 1 (by rfl) ⟨541172, by rfl⟩ : syracuseStep 721563 = 1082345) B1082345
theorem B1083035 : Blo 718322 1083035 := bstep (se 1 (by rfl) ⟨812276, by rfl⟩ : syracuseStep 1083035 = 1624553) B1624553
theorem B31166801 : Blo 718322 31166801 := bstep (se 2 (by rfl) ⟨11687550, by rfl⟩ : syracuseStep 31166801 = 23375101) B23375101
theorem B6558745 : Blo 718322 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B2431079 : Blo 718322 2431079 := bstep (se 1 (by rfl) ⟨1823309, by rfl⟩ : syracuseStep 2431079 = 3646619) B3646619
theorem B1617263 : Blo 718322 1617263 := bstep (se 1 (by rfl) ⟨1212947, by rfl⟩ : syracuseStep 1617263 = 2425895) B2425895
theorem B2733689 : Blo 718322 2733689 := bstep (se 2 (by rfl) ⟨1025133, by rfl⟩ : syracuseStep 2733689 = 2050267) B2050267
theorem B7027721 : Blo 718322 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B12828239 : Blo 718322 12828239 := bstep (se 1 (by rfl) ⟨9621179, by rfl⟩ : syracuseStep 12828239 = 19242359) B19242359
theorem B3654233 : Blo 718322 3654233 := bstep (se 2 (by rfl) ⟨1370337, by rfl⟩ : syracuseStep 3654233 = 2740675) B2740675
theorem B4113179 : Blo 718322 4113179 := bstep (se 1 (by rfl) ⟨3084884, by rfl⟩ : syracuseStep 4113179 = 6169769) B6169769
theorem B3656663 : Blo 718322 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B1821791 : Blo 718322 1821791 := bstep (se 1 (by rfl) ⟨1366343, by rfl⟩ : syracuseStep 1821791 = 2732687) B2732687
theorem B504327653 : Blo 718322 504327653 := bstep (se 4 (by rfl) ⟨47280717, by rfl⟩ : syracuseStep 504327653 = 94561435) B94561435
theorem B94729823 : Blo 718322 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B1079039 : Blo 718322 1079039 := bstep (se 1 (by rfl) ⟨809279, by rfl⟩ : syracuseStep 1079039 = 1618559) B1618559
theorem B5470415 : Blo 718322 5470415 := bstep (se 1 (by rfl) ⟨4102811, by rfl⟩ : syracuseStep 5470415 = 8205623) B8205623
theorem B719343 : Blo 718322 719343 := bstep (se 1 (by rfl) ⟨539507, by rfl⟩ : syracuseStep 719343 = 1079015) B1079015
theorem B12286565 : Blo 718322 12286565 := bstep (se 4 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 12286565 = 2303731) B2303731
theorem B1079999 : Blo 718322 1079999 := bstep (se 1 (by rfl) ⟨809999, by rfl⟩ : syracuseStep 1079999 = 1619999) B1619999
theorem B1080887 : Blo 718322 1080887 := bstep (se 1 (by rfl) ⟨810665, by rfl⟩ : syracuseStep 1080887 = 1621331) B1621331
theorem B3637223 : Blo 718322 3637223 := bstep (se 1 (by rfl) ⟨2727917, by rfl⟩ : syracuseStep 3637223 = 5455835) B5455835
theorem B722023 : Blo 718322 722023 := bstep (se 1 (by rfl) ⟨541517, by rfl⟩ : syracuseStep 722023 = 1083035) B1083035
theorem B1214527 : Blo 718322 1214527 := bstep (se 1 (by rfl) ⟨910895, by rfl⟩ : syracuseStep 1214527 = 1821791) B1821791
theorem B20777867 : Blo 718322 20777867 := bstep (se 1 (by rfl) ⟨15583400, by rfl⟩ : syracuseStep 20777867 = 31166801) B31166801
theorem B63153215 : Blo 718322 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B3646943 : Blo 718322 3646943 := bstep (se 1 (by rfl) ⟨2735207, by rfl⟩ : syracuseStep 3646943 = 5470415) B5470415
theorem B2436155 : Blo 718322 2436155 := bstep (se 1 (by rfl) ⟨1827116, by rfl⟩ : syracuseStep 2436155 = 3654233) B3654233
theorem B2437775 : Blo 718322 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B1620719 : Blo 718322 1620719 := bstep (se 1 (by rfl) ⟨1215539, by rfl⟩ : syracuseStep 1620719 = 2431079) B2431079
theorem B336218435 : Blo 718322 336218435 := bstep (se 1 (by rfl) ⟨252163826, by rfl⟩ : syracuseStep 336218435 = 504327653) B504327653
theorem B1822459 : Blo 718322 1822459 := bstep (se 1 (by rfl) ⟨1366844, by rfl⟩ : syracuseStep 1822459 = 2733689) B2733689
theorem B2742119 : Blo 718322 2742119 := bstep (se 1 (by rfl) ⟨2056589, by rfl⟩ : syracuseStep 2742119 = 4113179) B4113179
theorem B8744993 : Blo 718322 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B1078175 : Blo 718322 1078175 := bstep (se 1 (by rfl) ⟨808631, by rfl⟩ : syracuseStep 1078175 = 1617263) B1617263
theorem B719359 : Blo 718322 719359 := bstep (se 1 (by rfl) ⟨539519, by rfl⟩ : syracuseStep 719359 = 1079039) B1079039
theorem B8191043 : Blo 718322 8191043 := bstep (se 1 (by rfl) ⟨6143282, by rfl⟩ : syracuseStep 8191043 = 12286565) B12286565
theorem B719999 : Blo 718322 719999 := bstep (se 1 (by rfl) ⟨539999, by rfl⟩ : syracuseStep 719999 = 1079999) B1079999
theorem B4685147 : Blo 718322 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B720591 : Blo 718322 720591 := bstep (se 1 (by rfl) ⟨540443, by rfl⟩ : syracuseStep 720591 = 1080887) B1080887
theorem B8552159 : Blo 718322 8552159 := bstep (se 1 (by rfl) ⟨6414119, by rfl⟩ : syracuseStep 8552159 = 12828239) B12828239
theorem B2424815 : Blo 718322 2424815 := bstep (se 1 (by rfl) ⟨1818611, by rfl⟩ : syracuseStep 2424815 = 3637223) B3637223
theorem B2429945 : Blo 718322 2429945 := bstep (se 2 (by rfl) ⟨911229, by rfl⟩ : syracuseStep 2429945 = 1822459) B1822459
theorem B2431295 : Blo 718322 2431295 := bstep (se 1 (by rfl) ⟨1823471, by rfl⟩ : syracuseStep 2431295 = 3646943) B3646943
theorem B3123431 : Blo 718322 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B1616543 : Blo 718322 1616543 := bstep (se 1 (by rfl) ⟨1212407, by rfl⟩ : syracuseStep 1616543 = 2424815) B2424815
theorem B224145623 : Blo 718322 224145623 := bstep (se 1 (by rfl) ⟨168109217, by rfl⟩ : syracuseStep 224145623 = 336218435) B336218435
theorem B1619369 : Blo 718322 1619369 := bstep (se 2 (by rfl) ⟨607263, by rfl⟩ : syracuseStep 1619369 = 1214527) B1214527
theorem B1624103 : Blo 718322 1624103 := bstep (se 1 (by rfl) ⟨1218077, by rfl⟩ : syracuseStep 1624103 = 2436155) B2436155
theorem B1625183 : Blo 718322 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B5460695 : Blo 718322 5460695 := bstep (se 1 (by rfl) ⟨4095521, by rfl⟩ : syracuseStep 5460695 = 8191043) B8191043
theorem B13851911 : Blo 718322 13851911 := bstep (se 1 (by rfl) ⟨10388933, by rfl⟩ : syracuseStep 13851911 = 20777867) B20777867
theorem B1828079 : Blo 718322 1828079 := bstep (se 1 (by rfl) ⟨1371059, by rfl⟩ : syracuseStep 1828079 = 2742119) B2742119
theorem B42102143 : Blo 718322 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B5829995 : Blo 718322 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B718783 : Blo 718322 718783 := bstep (se 1 (by rfl) ⟨539087, by rfl⟩ : syracuseStep 718783 = 1078175) B1078175
theorem B1080479 : Blo 718322 1080479 := bstep (se 1 (by rfl) ⟨810359, by rfl⟩ : syracuseStep 1080479 = 1620719) B1620719
theorem B5701439 : Blo 718322 5701439 := bstep (se 1 (by rfl) ⟨4276079, by rfl⟩ : syracuseStep 5701439 = 8552159) B8552159
theorem B1082735 : Blo 718322 1082735 := bstep (se 1 (by rfl) ⟨812051, by rfl⟩ : syracuseStep 1082735 = 1624103) B1624103
theorem B1083455 : Blo 718322 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B3640463 : Blo 718322 3640463 := bstep (se 1 (by rfl) ⟨2730347, by rfl⟩ : syracuseStep 3640463 = 5460695) B5460695
theorem B1218719 : Blo 718322 1218719 := bstep (se 1 (by rfl) ⟨914039, by rfl⟩ : syracuseStep 1218719 = 1828079) B1828079
theorem B149430415 : Blo 718322 149430415 := bstep (se 1 (by rfl) ⟨112072811, by rfl⟩ : syracuseStep 149430415 = 224145623) B224145623
theorem B1619963 : Blo 718322 1619963 := bstep (se 1 (by rfl) ⟨1214972, by rfl⟩ : syracuseStep 1619963 = 2429945) B2429945
theorem B15546653 : Blo 718322 15546653 := bstep (se 3 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 15546653 = 5829995) B5829995
theorem B1620863 : Blo 718322 1620863 := bstep (se 1 (by rfl) ⟨1215647, by rfl⟩ : syracuseStep 1620863 = 2431295) B2431295
theorem B2082287 : Blo 718322 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B28068095 : Blo 718322 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B9234607 : Blo 718322 9234607 := bstep (se 1 (by rfl) ⟨6925955, by rfl⟩ : syracuseStep 9234607 = 13851911) B13851911
theorem B1077695 : Blo 718322 1077695 := bstep (se 1 (by rfl) ⟨808271, by rfl⟩ : syracuseStep 1077695 = 1616543) B1616543
theorem B1079579 : Blo 718322 1079579 := bstep (se 1 (by rfl) ⟨809684, by rfl⟩ : syracuseStep 1079579 = 1619369) B1619369
theorem B720319 : Blo 718322 720319 := bstep (se 1 (by rfl) ⟨540239, by rfl⟩ : syracuseStep 720319 = 1080479) B1080479
theorem B15203837 : Blo 718322 15203837 := bstep (se 3 (by rfl) ⟨2850719, by rfl⟩ : syracuseStep 15203837 = 5701439) B5701439
theorem B721823 : Blo 718322 721823 := bstep (se 1 (by rfl) ⟨541367, by rfl⟩ : syracuseStep 721823 = 1082735) B1082735
theorem B722303 : Blo 718322 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B18712063 : Blo 718322 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B2426975 : Blo 718322 2426975 := bstep (se 1 (by rfl) ⟨1820231, by rfl⟩ : syracuseStep 2426975 = 3640463) B3640463
theorem B10364435 : Blo 718322 10364435 := bstep (se 1 (by rfl) ⟨7773326, by rfl⟩ : syracuseStep 10364435 = 15546653) B15546653
theorem B10135891 : Blo 718322 10135891 := bstep (se 1 (by rfl) ⟨7601918, by rfl⟩ : syracuseStep 10135891 = 15203837) B15203837
theorem B199240553 : Blo 718322 199240553 := bstep (se 2 (by rfl) ⟨74715207, by rfl⟩ : syracuseStep 199240553 = 149430415) B149430415
theorem B1388191 : Blo 718322 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B12312809 : Blo 718322 12312809 := bstep (se 2 (by rfl) ⟨4617303, by rfl⟩ : syracuseStep 12312809 = 9234607) B9234607
theorem B812479 : Blo 718322 812479 := bstep (se 1 (by rfl) ⟨609359, by rfl⟩ : syracuseStep 812479 = 1218719) B1218719
theorem B718463 : Blo 718322 718463 := bstep (se 1 (by rfl) ⟨538847, by rfl⟩ : syracuseStep 718463 = 1077695) B1077695
theorem B1079975 : Blo 718322 1079975 := bstep (se 1 (by rfl) ⟨809981, by rfl⟩ : syracuseStep 1079975 = 1619963) B1619963
theorem B719719 : Blo 718322 719719 := bstep (se 1 (by rfl) ⟨539789, by rfl⟩ : syracuseStep 719719 = 1079579) B1079579
theorem B1080575 : Blo 718322 1080575 := bstep (se 1 (by rfl) ⟨810431, by rfl⟩ : syracuseStep 1080575 = 1620863) B1620863
theorem B1083305 : Blo 718322 1083305 := bstep (se 2 (by rfl) ⟨406239, by rfl⟩ : syracuseStep 1083305 = 812479) B812479
theorem B1617983 : Blo 718322 1617983 := bstep (se 1 (by rfl) ⟨1213487, by rfl⟩ : syracuseStep 1617983 = 2426975) B2426975
theorem B24949417 : Blo 718322 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B13514521 : Blo 718322 13514521 := bstep (se 2 (by rfl) ⟨5067945, by rfl⟩ : syracuseStep 13514521 = 10135891) B10135891
theorem B1850921 : Blo 718322 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B8208539 : Blo 718322 8208539 := bstep (se 1 (by rfl) ⟨6156404, by rfl⟩ : syracuseStep 8208539 = 12312809) B12312809
theorem B132827035 : Blo 718322 132827035 := bstep (se 1 (by rfl) ⟨99620276, by rfl⟩ : syracuseStep 132827035 = 199240553) B199240553
theorem B6909623 : Blo 718322 6909623 := bstep (se 1 (by rfl) ⟨5182217, by rfl⟩ : syracuseStep 6909623 = 10364435) B10364435
theorem B719983 : Blo 718322 719983 := bstep (se 1 (by rfl) ⟨539987, by rfl⟩ : syracuseStep 719983 = 1079975) B1079975
theorem B720383 : Blo 718322 720383 := bstep (se 1 (by rfl) ⟨540287, by rfl⟩ : syracuseStep 720383 = 1080575) B1080575
theorem B5472359 : Blo 718322 5472359 := bstep (se 1 (by rfl) ⟨4104269, by rfl⟩ : syracuseStep 5472359 = 8208539) B8208539
theorem B722203 : Blo 718322 722203 := bstep (se 1 (by rfl) ⟨541652, by rfl⟩ : syracuseStep 722203 = 1083305) B1083305
theorem B33265889 : Blo 718322 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B4606415 : Blo 718322 4606415 := bstep (se 1 (by rfl) ⟨3454811, by rfl⟩ : syracuseStep 4606415 = 6909623) B6909623
theorem B1233947 : Blo 718322 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B177102713 : Blo 718322 177102713 := bstep (se 2 (by rfl) ⟨66413517, by rfl⟩ : syracuseStep 177102713 = 132827035) B132827035
theorem B18019361 : Blo 718322 18019361 := bstep (se 2 (by rfl) ⟨6757260, by rfl⟩ : syracuseStep 18019361 = 13514521) B13514521
theorem B1078655 : Blo 718322 1078655 := bstep (se 1 (by rfl) ⟨808991, by rfl⟩ : syracuseStep 1078655 = 1617983) B1617983
theorem B822631 : Blo 718322 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B118068475 : Blo 718322 118068475 := bstep (se 1 (by rfl) ⟨88551356, by rfl⟩ : syracuseStep 118068475 = 177102713) B177102713
theorem B3648239 : Blo 718322 3648239 := bstep (se 1 (by rfl) ⟨2736179, by rfl⟩ : syracuseStep 3648239 = 5472359) B5472359
theorem B12012907 : Blo 718322 12012907 := bstep (se 1 (by rfl) ⟨9009680, by rfl⟩ : syracuseStep 12012907 = 18019361) B18019361
theorem B3070943 : Blo 718322 3070943 := bstep (se 1 (by rfl) ⟨2303207, by rfl⟩ : syracuseStep 3070943 = 4606415) B4606415
theorem B22177259 : Blo 718322 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B719103 : Blo 718322 719103 := bstep (se 1 (by rfl) ⟨539327, by rfl⟩ : syracuseStep 719103 = 1078655) B1078655
theorem B14784839 : Blo 718322 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B157424633 : Blo 718322 157424633 := bstep (se 2 (by rfl) ⟨59034237, by rfl⟩ : syracuseStep 157424633 = 118068475) B118068475
theorem B2432159 : Blo 718322 2432159 := bstep (se 1 (by rfl) ⟨1824119, by rfl⟩ : syracuseStep 2432159 = 3648239) B3648239
theorem B1096841 : Blo 718322 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B2047295 : Blo 718322 2047295 := bstep (se 1 (by rfl) ⟨1535471, by rfl⟩ : syracuseStep 2047295 = 3070943) B3070943
theorem B16017209 : Blo 718322 16017209 := bstep (se 2 (by rfl) ⟨6006453, by rfl⟩ : syracuseStep 16017209 = 12012907) B12012907
theorem B2924909 : Blo 718322 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B1621439 : Blo 718322 1621439 := bstep (se 1 (by rfl) ⟨1216079, by rfl⟩ : syracuseStep 1621439 = 2432159) B2432159
theorem B1364863 : Blo 718322 1364863 := bstep (se 1 (by rfl) ⟨1023647, by rfl⟩ : syracuseStep 1364863 = 2047295) B2047295
theorem B9856559 : Blo 718322 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B104949755 : Blo 718322 104949755 := bstep (se 1 (by rfl) ⟨78712316, by rfl⟩ : syracuseStep 104949755 = 157424633) B157424633
theorem B10678139 : Blo 718322 10678139 := bstep (se 1 (by rfl) ⟨8008604, by rfl⟩ : syracuseStep 10678139 = 16017209) B16017209
theorem B69966503 : Blo 718322 69966503 := bstep (se 1 (by rfl) ⟨52474877, by rfl⟩ : syracuseStep 69966503 = 104949755) B104949755
theorem B7118759 : Blo 718322 7118759 := bstep (se 1 (by rfl) ⟨5339069, by rfl⟩ : syracuseStep 7118759 = 10678139) B10678139
theorem B1949939 : Blo 718322 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B6571039 : Blo 718322 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B1819817 : Blo 718322 1819817 := bstep (se 2 (by rfl) ⟨682431, by rfl⟩ : syracuseStep 1819817 = 1364863) B1364863
theorem B1080959 : Blo 718322 1080959 := bstep (se 1 (by rfl) ⟨810719, by rfl⟩ : syracuseStep 1080959 = 1621439) B1621439
theorem B1213211 : Blo 718322 1213211 := bstep (se 1 (by rfl) ⟨909908, by rfl⟩ : syracuseStep 1213211 = 1819817) B1819817
theorem B18983357 : Blo 718322 18983357 := bstep (se 3 (by rfl) ⟨3559379, by rfl⟩ : syracuseStep 18983357 = 7118759) B7118759
theorem B8761385 : Blo 718322 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B46644335 : Blo 718322 46644335 := bstep (se 1 (by rfl) ⟨34983251, by rfl⟩ : syracuseStep 46644335 = 69966503) B69966503
theorem B1299959 : Blo 718322 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B720639 : Blo 718322 720639 := bstep (se 1 (by rfl) ⟨540479, by rfl⟩ : syracuseStep 720639 = 1080959) B1080959
theorem B12655571 : Blo 718322 12655571 := bstep (se 1 (by rfl) ⟨9491678, by rfl⟩ : syracuseStep 12655571 = 18983357) B18983357
theorem B5840923 : Blo 718322 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B866639 : Blo 718322 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B808807 : Blo 718322 808807 := bstep (se 1 (by rfl) ⟨606605, by rfl⟩ : syracuseStep 808807 = 1213211) B1213211
theorem B31096223 : Blo 718322 31096223 := bstep (se 1 (by rfl) ⟨23322167, by rfl⟩ : syracuseStep 31096223 = 46644335) B46644335
theorem B2311037 : Blo 718322 2311037 := bstep (se 3 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 2311037 = 866639) B866639
theorem B134992757 : Blo 718322 134992757 := bstep (se 5 (by rfl) ⟨6327785, by rfl⟩ : syracuseStep 134992757 = 12655571) B12655571
theorem B20730815 : Blo 718322 20730815 := bstep (se 1 (by rfl) ⟨15548111, by rfl⟩ : syracuseStep 20730815 = 31096223) B31096223
theorem B7787897 : Blo 718322 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B1078409 : Blo 718322 1078409 := bstep (se 2 (by rfl) ⟨404403, by rfl⟩ : syracuseStep 1078409 = 808807) B808807
theorem B1540691 : Blo 718322 1540691 := bstep (se 1 (by rfl) ⟨1155518, by rfl⟩ : syracuseStep 1540691 = 2311037) B2311037
theorem B89995171 : Blo 718322 89995171 := bstep (se 1 (by rfl) ⟨67496378, by rfl⟩ : syracuseStep 89995171 = 134992757) B134992757
theorem B5191931 : Blo 718322 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B13820543 : Blo 718322 13820543 := bstep (se 1 (by rfl) ⟨10365407, by rfl⟩ : syracuseStep 13820543 = 20730815) B20730815
theorem B718939 : Blo 718322 718939 := bstep (se 1 (by rfl) ⟨539204, by rfl⟩ : syracuseStep 718939 = 1078409) B1078409
theorem B9213695 : Blo 718322 9213695 := bstep (se 1 (by rfl) ⟨6910271, by rfl⟩ : syracuseStep 9213695 = 13820543) B13820543
theorem B1027127 : Blo 718322 1027127 := bstep (se 1 (by rfl) ⟨770345, by rfl⟩ : syracuseStep 1027127 = 1540691) B1540691
theorem B3461287 : Blo 718322 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B119993561 : Blo 718322 119993561 := bstep (se 2 (by rfl) ⟨44997585, by rfl⟩ : syracuseStep 119993561 = 89995171) B89995171
theorem B79995707 : Blo 718322 79995707 := bstep (se 1 (by rfl) ⟨59996780, by rfl⟩ : syracuseStep 79995707 = 119993561) B119993561
theorem B6142463 : Blo 718322 6142463 := bstep (se 1 (by rfl) ⟨4606847, by rfl⟩ : syracuseStep 6142463 = 9213695) B9213695
theorem B2739005 : Blo 718322 2739005 := bstep (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) B1027127
theorem B4615049 : Blo 718322 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B53330471 : Blo 718322 53330471 := bstep (se 1 (by rfl) ⟨39997853, by rfl⟩ : syracuseStep 53330471 = 79995707) B79995707
theorem B1826003 : Blo 718322 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B3076699 : Blo 718322 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B4094975 : Blo 718322 4094975 := bstep (se 1 (by rfl) ⟨3071231, by rfl⟩ : syracuseStep 4094975 = 6142463) B6142463
theorem B35553647 : Blo 718322 35553647 := bstep (se 1 (by rfl) ⟨26665235, by rfl⟩ : syracuseStep 35553647 = 53330471) B53330471
theorem B1217335 : Blo 718322 1217335 := bstep (se 1 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 1217335 = 1826003) B1826003
theorem B4102265 : Blo 718322 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B2729983 : Blo 718322 2729983 := bstep (se 1 (by rfl) ⟨2047487, by rfl⟩ : syracuseStep 2729983 = 4094975) B4094975
theorem B3639977 : Blo 718322 3639977 := bstep (se 2 (by rfl) ⟨1364991, by rfl⟩ : syracuseStep 3639977 = 2729983) B2729983
theorem B23702431 : Blo 718322 23702431 := bstep (se 1 (by rfl) ⟨17776823, by rfl⟩ : syracuseStep 23702431 = 35553647) B35553647
theorem B2734843 : Blo 718322 2734843 := bstep (se 1 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 2734843 = 4102265) B4102265
theorem B1623113 : Blo 718322 1623113 := bstep (se 2 (by rfl) ⟨608667, by rfl⟩ : syracuseStep 1623113 = 1217335) B1217335
theorem B1082075 : Blo 718322 1082075 := bstep (se 1 (by rfl) ⟨811556, by rfl⟩ : syracuseStep 1082075 = 1623113) B1623113
theorem B2426651 : Blo 718322 2426651 := bstep (se 1 (by rfl) ⟨1819988, by rfl⟩ : syracuseStep 2426651 = 3639977) B3639977
theorem B3646457 : Blo 718322 3646457 := bstep (se 2 (by rfl) ⟨1367421, by rfl⟩ : syracuseStep 3646457 = 2734843) B2734843
theorem B31603241 : Blo 718322 31603241 := bstep (se 2 (by rfl) ⟨11851215, by rfl⟩ : syracuseStep 31603241 = 23702431) B23702431
theorem B721383 : Blo 718322 721383 := bstep (se 1 (by rfl) ⟨541037, by rfl⟩ : syracuseStep 721383 = 1082075) B1082075
theorem B2430971 : Blo 718322 2430971 := bstep (se 1 (by rfl) ⟨1823228, by rfl⟩ : syracuseStep 2430971 = 3646457) B3646457
theorem B1617767 : Blo 718322 1617767 := bstep (se 1 (by rfl) ⟨1213325, by rfl⟩ : syracuseStep 1617767 = 2426651) B2426651
theorem B84275309 : Blo 718322 84275309 := bstep (se 3 (by rfl) ⟨15801620, by rfl⟩ : syracuseStep 84275309 = 31603241) B31603241
theorem B1620647 : Blo 718322 1620647 := bstep (se 1 (by rfl) ⟨1215485, by rfl⟩ : syracuseStep 1620647 = 2430971) B2430971
theorem B56183539 : Blo 718322 56183539 := bstep (se 1 (by rfl) ⟨42137654, by rfl⟩ : syracuseStep 56183539 = 84275309) B84275309
theorem B1078511 : Blo 718322 1078511 := bstep (se 1 (by rfl) ⟨808883, by rfl⟩ : syracuseStep 1078511 = 1617767) B1617767
theorem B74911385 : Blo 718322 74911385 := bstep (se 2 (by rfl) ⟨28091769, by rfl⟩ : syracuseStep 74911385 = 56183539) B56183539
theorem B719007 : Blo 718322 719007 := bstep (se 1 (by rfl) ⟨539255, by rfl⟩ : syracuseStep 719007 = 1078511) B1078511
theorem B1080431 : Blo 718322 1080431 := bstep (se 1 (by rfl) ⟨810323, by rfl⟩ : syracuseStep 1080431 = 1620647) B1620647
theorem B49940923 : Blo 718322 49940923 := bstep (se 1 (by rfl) ⟨37455692, by rfl⟩ : syracuseStep 49940923 = 74911385) B74911385
theorem B720287 : Blo 718322 720287 := bstep (se 1 (by rfl) ⟨540215, by rfl⟩ : syracuseStep 720287 = 1080431) B1080431
theorem B66587897 : Blo 718322 66587897 := bstep (se 2 (by rfl) ⟨24970461, by rfl⟩ : syracuseStep 66587897 = 49940923) B49940923
theorem B44391931 : Blo 718322 44391931 := bstep (se 1 (by rfl) ⟨33293948, by rfl⟩ : syracuseStep 44391931 = 66587897) B66587897
theorem B236756965 : Blo 718322 236756965 := bstep (se 4 (by rfl) ⟨22195965, by rfl⟩ : syracuseStep 236756965 = 44391931) B44391931
theorem B315675953 : Blo 718322 315675953 := bstep (se 2 (by rfl) ⟨118378482, by rfl⟩ : syracuseStep 315675953 = 236756965) B236756965
theorem B210450635 : Blo 718322 210450635 := bstep (se 1 (by rfl) ⟨157837976, by rfl⟩ : syracuseStep 210450635 = 315675953) B315675953
theorem B140300423 : Blo 718322 140300423 := bstep (se 1 (by rfl) ⟨105225317, by rfl⟩ : syracuseStep 140300423 = 210450635) B210450635
theorem B93533615 : Blo 718322 93533615 := bstep (se 1 (by rfl) ⟨70150211, by rfl⟩ : syracuseStep 93533615 = 140300423) B140300423
theorem B62355743 : Blo 718322 62355743 := bstep (se 1 (by rfl) ⟨46766807, by rfl⟩ : syracuseStep 62355743 = 93533615) B93533615
theorem B41570495 : Blo 718322 41570495 := bstep (se 1 (by rfl) ⟨31177871, by rfl⟩ : syracuseStep 41570495 = 62355743) B62355743
theorem B27713663 : Blo 718322 27713663 := bstep (se 1 (by rfl) ⟨20785247, by rfl⟩ : syracuseStep 27713663 = 41570495) B41570495
theorem B18475775 : Blo 718322 18475775 := bstep (se 1 (by rfl) ⟨13856831, by rfl⟩ : syracuseStep 18475775 = 27713663) B27713663
theorem B12317183 : Blo 718322 12317183 := bstep (se 1 (by rfl) ⟨9237887, by rfl⟩ : syracuseStep 12317183 = 18475775) B18475775
theorem B8211455 : Blo 718322 8211455 := bstep (se 1 (by rfl) ⟨6158591, by rfl⟩ : syracuseStep 8211455 = 12317183) B12317183
theorem B5474303 : Blo 718322 5474303 := bstep (se 1 (by rfl) ⟨4105727, by rfl⟩ : syracuseStep 5474303 = 8211455) B8211455
theorem B3649535 : Blo 718322 3649535 := bstep (se 1 (by rfl) ⟨2737151, by rfl⟩ : syracuseStep 3649535 = 5474303) B5474303
theorem B2433023 : Blo 718322 2433023 := bstep (se 1 (by rfl) ⟨1824767, by rfl⟩ : syracuseStep 2433023 = 3649535) B3649535
theorem B1622015 : Blo 718322 1622015 := bstep (se 1 (by rfl) ⟨1216511, by rfl⟩ : syracuseStep 1622015 = 2433023) B2433023
theorem B1081343 : Blo 718322 1081343 := bstep (se 1 (by rfl) ⟨811007, by rfl⟩ : syracuseStep 1081343 = 1622015) B1622015
theorem B720895 : Blo 718322 720895 := bstep (se 1 (by rfl) ⟨540671, by rfl⟩ : syracuseStep 720895 = 1081343) B1081343

theorem C0 (j : ℕ) (h1 : 179580 ≤ j) (h2 : j ≤ 180279) : Blo 718322 (4 * j + 3) := by
  interval_cases j
  · exact B718323
  · exact B718327
  · exact B718331
  · exact B718335
  · exact B718339
  · exact B718343
  · exact B718347
  · exact B718351
  · exact B718355
  · exact B718359
  · exact B718363
  · exact B718367
  · exact B718371
  · exact B718375
  · exact B718379
  · exact B718383
  · exact B718387
  · exact B718391
  · exact B718395
  · exact B718399
  · exact B718403
  · exact B718407
  · exact B718411
  · exact B718415
  · exact B718419
  · exact B718423
  · exact B718427
  · exact B718431
  · exact B718435
  · exact B718439
  · exact B718443
  · exact B718447
  · exact B718451
  · exact B718455
  · exact B718459
  · exact B718463
  · exact B718467
  · exact B718471
  · exact B718475
  · exact B718479
  · exact B718483
  · exact B718487
  · exact B718491
  · exact B718495
  · exact B718499
  · exact B718503
  · exact B718507
  · exact B718511
  · exact B718515
  · exact B718519
  · exact B718523
  · exact B718527
  · exact B718531
  · exact B718535
  · exact B718539
  · exact B718543
  · exact B718547
  · exact B718551
  · exact B718555
  · exact B718559
  · exact B718563
  · exact B718567
  · exact B718571
  · exact B718575
  · exact B718579
  · exact B718583
  · exact B718587
  · exact B718591
  · exact B718595
  · exact B718599
  · exact B718603
  · exact B718607
  · exact B718611
  · exact B718615
  · exact B718619
  · exact B718623
  · exact B718627
  · exact B718631
  · exact B718635
  · exact B718639
  · exact B718643
  · exact B718647
  · exact B718651
  · exact B718655
  · exact B718659
  · exact B718663
  · exact B718667
  · exact B718671
  · exact B718675
  · exact B718679
  · exact B718683
  · exact B718687
  · exact B718691
  · exact B718695
  · exact B718699
  · exact B718703
  · exact B718707
  · exact B718711
  · exact B718715
  · exact B718719
  · exact B718723
  · exact B718727
  · exact B718731
  · exact B718735
  · exact B718739
  · exact B718743
  · exact B718747
  · exact B718751
  · exact B718755
  · exact B718759
  · exact B718763
  · exact B718767
  · exact B718771
  · exact B718775
  · exact B718779
  · exact B718783
  · exact B718787
  · exact B718791
  · exact B718795
  · exact B718799
  · exact B718803
  · exact B718807
  · exact B718811
  · exact B718815
  · exact B718819
  · exact B718823
  · exact B718827
  · exact B718831
  · exact B718835
  · exact B718839
  · exact B718843
  · exact B718847
  · exact B718851
  · exact B718855
  · exact B718859
  · exact B718863
  · exact B718867
  · exact B718871
  · exact B718875
  · exact B718879
  · exact B718883
  · exact B718887
  · exact B718891
  · exact B718895
  · exact B718899
  · exact B718903
  · exact B718907
  · exact B718911
  · exact B718915
  · exact B718919
  · exact B718923
  · exact B718927
  · exact B718931
  · exact B718935
  · exact B718939
  · exact B718943
  · exact B718947
  · exact B718951
  · exact B718955
  · exact B718959
  · exact B718963
  · exact B718967
  · exact B718971
  · exact B718975
  · exact B718979
  · exact B718983
  · exact B718987
  · exact B718991
  · exact B718995
  · exact B718999
  · exact B719003
  · exact B719007
  · exact B719011
  · exact B719015
  · exact B719019
  · exact B719023
  · exact B719027
  · exact B719031
  · exact B719035
  · exact B719039
  · exact B719043
  · exact B719047
  · exact B719051
  · exact B719055
  · exact B719059
  · exact B719063
  · exact B719067
  · exact B719071
  · exact B719075
  · exact B719079
  · exact B719083
  · exact B719087
  · exact B719091
  · exact B719095
  · exact B719099
  · exact B719103
  · exact B719107
  · exact B719111
  · exact B719115
  · exact B719119
  · exact B719123
  · exact B719127
  · exact B719131
  · exact B719135
  · exact B719139
  · exact B719143
  · exact B719147
  · exact B719151
  · exact B719155
  · exact B719159
  · exact B719163
  · exact B719167
  · exact B719171
  · exact B719175
  · exact B719179
  · exact B719183
  · exact B719187
  · exact B719191
  · exact B719195
  · exact B719199
  · exact B719203
  · exact B719207
  · exact B719211
  · exact B719215
  · exact B719219
  · exact B719223
  · exact B719227
  · exact B719231
  · exact B719235
  · exact B719239
  · exact B719243
  · exact B719247
  · exact B719251
  · exact B719255
  · exact B719259
  · exact B719263
  · exact B719267
  · exact B719271
  · exact B719275
  · exact B719279
  · exact B719283
  · exact B719287
  · exact B719291
  · exact B719295
  · exact B719299
  · exact B719303
  · exact B719307
  · exact B719311
  · exact B719315
  · exact B719319
  · exact B719323
  · exact B719327
  · exact B719331
  · exact B719335
  · exact B719339
  · exact B719343
  · exact B719347
  · exact B719351
  · exact B719355
  · exact B719359
  · exact B719363
  · exact B719367
  · exact B719371
  · exact B719375
  · exact B719379
  · exact B719383
  · exact B719387
  · exact B719391
  · exact B719395
  · exact B719399
  · exact B719403
  · exact B719407
  · exact B719411
  · exact B719415
  · exact B719419
  · exact B719423
  · exact B719427
  · exact B719431
  · exact B719435
  · exact B719439
  · exact B719443
  · exact B719447
  · exact B719451
  · exact B719455
  · exact B719459
  · exact B719463
  · exact B719467
  · exact B719471
  · exact B719475
  · exact B719479
  · exact B719483
  · exact B719487
  · exact B719491
  · exact B719495
  · exact B719499
  · exact B719503
  · exact B719507
  · exact B719511
  · exact B719515
  · exact B719519
  · exact B719523
  · exact B719527
  · exact B719531
  · exact B719535
  · exact B719539
  · exact B719543
  · exact B719547
  · exact B719551
  · exact B719555
  · exact B719559
  · exact B719563
  · exact B719567
  · exact B719571
  · exact B719575
  · exact B719579
  · exact B719583
  · exact B719587
  · exact B719591
  · exact B719595
  · exact B719599
  · exact B719603
  · exact B719607
  · exact B719611
  · exact B719615
  · exact B719619
  · exact B719623
  · exact B719627
  · exact B719631
  · exact B719635
  · exact B719639
  · exact B719643
  · exact B719647
  · exact B719651
  · exact B719655
  · exact B719659
  · exact B719663
  · exact B719667
  · exact B719671
  · exact B719675
  · exact B719679
  · exact B719683
  · exact B719687
  · exact B719691
  · exact B719695
  · exact B719699
  · exact B719703
  · exact B719707
  · exact B719711
  · exact B719715
  · exact B719719
  · exact B719723
  · exact B719727
  · exact B719731
  · exact B719735
  · exact B719739
  · exact B719743
  · exact B719747
  · exact B719751
  · exact B719755
  · exact B719759
  · exact B719763
  · exact B719767
  · exact B719771
  · exact B719775
  · exact B719779
  · exact B719783
  · exact B719787
  · exact B719791
  · exact B719795
  · exact B719799
  · exact B719803
  · exact B719807
  · exact B719811
  · exact B719815
  · exact B719819
  · exact B719823
  · exact B719827
  · exact B719831
  · exact B719835
  · exact B719839
  · exact B719843
  · exact B719847
  · exact B719851
  · exact B719855
  · exact B719859
  · exact B719863
  · exact B719867
  · exact B719871
  · exact B719875
  · exact B719879
  · exact B719883
  · exact B719887
  · exact B719891
  · exact B719895
  · exact B719899
  · exact B719903
  · exact B719907
  · exact B719911
  · exact B719915
  · exact B719919
  · exact B719923
  · exact B719927
  · exact B719931
  · exact B719935
  · exact B719939
  · exact B719943
  · exact B719947
  · exact B719951
  · exact B719955
  · exact B719959
  · exact B719963
  · exact B719967
  · exact B719971
  · exact B719975
  · exact B719979
  · exact B719983
  · exact B719987
  · exact B719991
  · exact B719995
  · exact B719999
  · exact B720003
  · exact B720007
  · exact B720011
  · exact B720015
  · exact B720019
  · exact B720023
  · exact B720027
  · exact B720031
  · exact B720035
  · exact B720039
  · exact B720043
  · exact B720047
  · exact B720051
  · exact B720055
  · exact B720059
  · exact B720063
  · exact B720067
  · exact B720071
  · exact B720075
  · exact B720079
  · exact B720083
  · exact B720087
  · exact B720091
  · exact B720095
  · exact B720099
  · exact B720103
  · exact B720107
  · exact B720111
  · exact B720115
  · exact B720119
  · exact B720123
  · exact B720127
  · exact B720131
  · exact B720135
  · exact B720139
  · exact B720143
  · exact B720147
  · exact B720151
  · exact B720155
  · exact B720159
  · exact B720163
  · exact B720167
  · exact B720171
  · exact B720175
  · exact B720179
  · exact B720183
  · exact B720187
  · exact B720191
  · exact B720195
  · exact B720199
  · exact B720203
  · exact B720207
  · exact B720211
  · exact B720215
  · exact B720219
  · exact B720223
  · exact B720227
  · exact B720231
  · exact B720235
  · exact B720239
  · exact B720243
  · exact B720247
  · exact B720251
  · exact B720255
  · exact B720259
  · exact B720263
  · exact B720267
  · exact B720271
  · exact B720275
  · exact B720279
  · exact B720283
  · exact B720287
  · exact B720291
  · exact B720295
  · exact B720299
  · exact B720303
  · exact B720307
  · exact B720311
  · exact B720315
  · exact B720319
  · exact B720323
  · exact B720327
  · exact B720331
  · exact B720335
  · exact B720339
  · exact B720343
  · exact B720347
  · exact B720351
  · exact B720355
  · exact B720359
  · exact B720363
  · exact B720367
  · exact B720371
  · exact B720375
  · exact B720379
  · exact B720383
  · exact B720387
  · exact B720391
  · exact B720395
  · exact B720399
  · exact B720403
  · exact B720407
  · exact B720411
  · exact B720415
  · exact B720419
  · exact B720423
  · exact B720427
  · exact B720431
  · exact B720435
  · exact B720439
  · exact B720443
  · exact B720447
  · exact B720451
  · exact B720455
  · exact B720459
  · exact B720463
  · exact B720467
  · exact B720471
  · exact B720475
  · exact B720479
  · exact B720483
  · exact B720487
  · exact B720491
  · exact B720495
  · exact B720499
  · exact B720503
  · exact B720507
  · exact B720511
  · exact B720515
  · exact B720519
  · exact B720523
  · exact B720527
  · exact B720531
  · exact B720535
  · exact B720539
  · exact B720543
  · exact B720547
  · exact B720551
  · exact B720555
  · exact B720559
  · exact B720563
  · exact B720567
  · exact B720571
  · exact B720575
  · exact B720579
  · exact B720583
  · exact B720587
  · exact B720591
  · exact B720595
  · exact B720599
  · exact B720603
  · exact B720607
  · exact B720611
  · exact B720615
  · exact B720619
  · exact B720623
  · exact B720627
  · exact B720631
  · exact B720635
  · exact B720639
  · exact B720643
  · exact B720647
  · exact B720651
  · exact B720655
  · exact B720659
  · exact B720663
  · exact B720667
  · exact B720671
  · exact B720675
  · exact B720679
  · exact B720683
  · exact B720687
  · exact B720691
  · exact B720695
  · exact B720699
  · exact B720703
  · exact B720707
  · exact B720711
  · exact B720715
  · exact B720719
  · exact B720723
  · exact B720727
  · exact B720731
  · exact B720735
  · exact B720739
  · exact B720743
  · exact B720747
  · exact B720751
  · exact B720755
  · exact B720759
  · exact B720763
  · exact B720767
  · exact B720771
  · exact B720775
  · exact B720779
  · exact B720783
  · exact B720787
  · exact B720791
  · exact B720795
  · exact B720799
  · exact B720803
  · exact B720807
  · exact B720811
  · exact B720815
  · exact B720819
  · exact B720823
  · exact B720827
  · exact B720831
  · exact B720835
  · exact B720839
  · exact B720843
  · exact B720847
  · exact B720851
  · exact B720855
  · exact B720859
  · exact B720863
  · exact B720867
  · exact B720871
  · exact B720875
  · exact B720879
  · exact B720883
  · exact B720887
  · exact B720891
  · exact B720895
  · exact B720899
  · exact B720903
  · exact B720907
  · exact B720911
  · exact B720915
  · exact B720919
  · exact B720923
  · exact B720927
  · exact B720931
  · exact B720935
  · exact B720939
  · exact B720943
  · exact B720947
  · exact B720951
  · exact B720955
  · exact B720959
  · exact B720963
  · exact B720967
  · exact B720971
  · exact B720975
  · exact B720979
  · exact B720983
  · exact B720987
  · exact B720991
  · exact B720995
  · exact B720999
  · exact B721003
  · exact B721007
  · exact B721011
  · exact B721015
  · exact B721019
  · exact B721023
  · exact B721027
  · exact B721031
  · exact B721035
  · exact B721039
  · exact B721043
  · exact B721047
  · exact B721051
  · exact B721055
  · exact B721059
  · exact B721063
  · exact B721067
  · exact B721071
  · exact B721075
  · exact B721079
  · exact B721083
  · exact B721087
  · exact B721091
  · exact B721095
  · exact B721099
  · exact B721103
  · exact B721107
  · exact B721111
  · exact B721115
  · exact B721119

theorem C1 (j : ℕ) (h1 : 180280 ≤ j) (h2 : j ≤ 180579) : Blo 718322 (4 * j + 3) := by
  interval_cases j
  · exact B721123
  · exact B721127
  · exact B721131
  · exact B721135
  · exact B721139
  · exact B721143
  · exact B721147
  · exact B721151
  · exact B721155
  · exact B721159
  · exact B721163
  · exact B721167
  · exact B721171
  · exact B721175
  · exact B721179
  · exact B721183
  · exact B721187
  · exact B721191
  · exact B721195
  · exact B721199
  · exact B721203
  · exact B721207
  · exact B721211
  · exact B721215
  · exact B721219
  · exact B721223
  · exact B721227
  · exact B721231
  · exact B721235
  · exact B721239
  · exact B721243
  · exact B721247
  · exact B721251
  · exact B721255
  · exact B721259
  · exact B721263
  · exact B721267
  · exact B721271
  · exact B721275
  · exact B721279
  · exact B721283
  · exact B721287
  · exact B721291
  · exact B721295
  · exact B721299
  · exact B721303
  · exact B721307
  · exact B721311
  · exact B721315
  · exact B721319
  · exact B721323
  · exact B721327
  · exact B721331
  · exact B721335
  · exact B721339
  · exact B721343
  · exact B721347
  · exact B721351
  · exact B721355
  · exact B721359
  · exact B721363
  · exact B721367
  · exact B721371
  · exact B721375
  · exact B721379
  · exact B721383
  · exact B721387
  · exact B721391
  · exact B721395
  · exact B721399
  · exact B721403
  · exact B721407
  · exact B721411
  · exact B721415
  · exact B721419
  · exact B721423
  · exact B721427
  · exact B721431
  · exact B721435
  · exact B721439
  · exact B721443
  · exact B721447
  · exact B721451
  · exact B721455
  · exact B721459
  · exact B721463
  · exact B721467
  · exact B721471
  · exact B721475
  · exact B721479
  · exact B721483
  · exact B721487
  · exact B721491
  · exact B721495
  · exact B721499
  · exact B721503
  · exact B721507
  · exact B721511
  · exact B721515
  · exact B721519
  · exact B721523
  · exact B721527
  · exact B721531
  · exact B721535
  · exact B721539
  · exact B721543
  · exact B721547
  · exact B721551
  · exact B721555
  · exact B721559
  · exact B721563
  · exact B721567
  · exact B721571
  · exact B721575
  · exact B721579
  · exact B721583
  · exact B721587
  · exact B721591
  · exact B721595
  · exact B721599
  · exact B721603
  · exact B721607
  · exact B721611
  · exact B721615
  · exact B721619
  · exact B721623
  · exact B721627
  · exact B721631
  · exact B721635
  · exact B721639
  · exact B721643
  · exact B721647
  · exact B721651
  · exact B721655
  · exact B721659
  · exact B721663
  · exact B721667
  · exact B721671
  · exact B721675
  · exact B721679
  · exact B721683
  · exact B721687
  · exact B721691
  · exact B721695
  · exact B721699
  · exact B721703
  · exact B721707
  · exact B721711
  · exact B721715
  · exact B721719
  · exact B721723
  · exact B721727
  · exact B721731
  · exact B721735
  · exact B721739
  · exact B721743
  · exact B721747
  · exact B721751
  · exact B721755
  · exact B721759
  · exact B721763
  · exact B721767
  · exact B721771
  · exact B721775
  · exact B721779
  · exact B721783
  · exact B721787
  · exact B721791
  · exact B721795
  · exact B721799
  · exact B721803
  · exact B721807
  · exact B721811
  · exact B721815
  · exact B721819
  · exact B721823
  · exact B721827
  · exact B721831
  · exact B721835
  · exact B721839
  · exact B721843
  · exact B721847
  · exact B721851
  · exact B721855
  · exact B721859
  · exact B721863
  · exact B721867
  · exact B721871
  · exact B721875
  · exact B721879
  · exact B721883
  · exact B721887
  · exact B721891
  · exact B721895
  · exact B721899
  · exact B721903
  · exact B721907
  · exact B721911
  · exact B721915
  · exact B721919
  · exact B721923
  · exact B721927
  · exact B721931
  · exact B721935
  · exact B721939
  · exact B721943
  · exact B721947
  · exact B721951
  · exact B721955
  · exact B721959
  · exact B721963
  · exact B721967
  · exact B721971
  · exact B721975
  · exact B721979
  · exact B721983
  · exact B721987
  · exact B721991
  · exact B721995
  · exact B721999
  · exact B722003
  · exact B722007
  · exact B722011
  · exact B722015
  · exact B722019
  · exact B722023
  · exact B722027
  · exact B722031
  · exact B722035
  · exact B722039
  · exact B722043
  · exact B722047
  · exact B722051
  · exact B722055
  · exact B722059
  · exact B722063
  · exact B722067
  · exact B722071
  · exact B722075
  · exact B722079
  · exact B722083
  · exact B722087
  · exact B722091
  · exact B722095
  · exact B722099
  · exact B722103
  · exact B722107
  · exact B722111
  · exact B722115
  · exact B722119
  · exact B722123
  · exact B722127
  · exact B722131
  · exact B722135
  · exact B722139
  · exact B722143
  · exact B722147
  · exact B722151
  · exact B722155
  · exact B722159
  · exact B722163
  · exact B722167
  · exact B722171
  · exact B722175
  · exact B722179
  · exact B722183
  · exact B722187
  · exact B722191
  · exact B722195
  · exact B722199
  · exact B722203
  · exact B722207
  · exact B722211
  · exact B722215
  · exact B722219
  · exact B722223
  · exact B722227
  · exact B722231
  · exact B722235
  · exact B722239
  · exact B722243
  · exact B722247
  · exact B722251
  · exact B722255
  · exact B722259
  · exact B722263
  · exact B722267
  · exact B722271
  · exact B722275
  · exact B722279
  · exact B722283
  · exact B722287
  · exact B722291
  · exact B722295
  · exact B722299
  · exact B722303
  · exact B722307
  · exact B722311
  · exact B722315
  · exact B722319

theorem solution (m : ℕ) (hlo : 718322 ≤ m) (hhi : m ≤ 722322) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 179580 ≤ j := by omega
    have hj2 : j ≤ 180579 := by omega
    have hb : Blo 718322 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 180280 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
