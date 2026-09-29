-- Prove2me | solution 1 for syracuse_descends_range_806344_810344
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:41.8742+00:00
-- url     : https://prove2.me/submissions/88808cc8-b058-4eaf-b671-7c7ee13e0aa2

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


theorem B1212437 : Blo 806344 1212437 := bbase (se 6 (by rfl) ⟨28416, by rfl⟩ : syracuseStep 1212437 = 56833) (by norm_num)
theorem B1212461 : Blo 806344 1212461 := bbase (se 3 (by rfl) ⟨227336, by rfl⟩ : syracuseStep 1212461 = 454673) (by norm_num)
theorem B1212485 : Blo 806344 1212485 := bbase (se 4 (by rfl) ⟨113670, by rfl⟩ : syracuseStep 1212485 = 227341) (by norm_num)
theorem B29491285 : Blo 806344 29491285 := bbase (se 8 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 29491285 = 345601) (by norm_num)
theorem B1212509 : Blo 806344 1212509 := bbase (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) (by norm_num)
theorem B1212533 : Blo 806344 1212533 := bbase (se 5 (by rfl) ⟨56837, by rfl⟩ : syracuseStep 1212533 = 113675) (by norm_num)
theorem B3113093 : Blo 806344 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B1212557 : Blo 806344 1212557 := bbase (se 3 (by rfl) ⟨227354, by rfl⟩ : syracuseStep 1212557 = 454709) (by norm_num)
theorem B1212581 : Blo 806344 1212581 := bbase (se 4 (by rfl) ⟨113679, by rfl⟩ : syracuseStep 1212581 = 227359) (by norm_num)
theorem B1212605 : Blo 806344 1212605 := bbase (se 3 (by rfl) ⟨227363, by rfl⟩ : syracuseStep 1212605 = 454727) (by norm_num)
theorem B1212629 : Blo 806344 1212629 := bbase (se 7 (by rfl) ⟨14210, by rfl⟩ : syracuseStep 1212629 = 28421) (by norm_num)
theorem B1212653 : Blo 806344 1212653 := bbase (se 3 (by rfl) ⟨227372, by rfl⟩ : syracuseStep 1212653 = 454745) (by norm_num)
theorem B1212677 : Blo 806344 1212677 := bbase (se 4 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 1212677 = 227377) (by norm_num)
theorem B2457877 : Blo 806344 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B1212701 : Blo 806344 1212701 := bbase (se 3 (by rfl) ⟨227381, by rfl⟩ : syracuseStep 1212701 = 454763) (by norm_num)
theorem B1212725 : Blo 806344 1212725 := bbase (se 5 (by rfl) ⟨56846, by rfl⟩ : syracuseStep 1212725 = 113693) (by norm_num)
theorem B1212749 : Blo 806344 1212749 := bbase (se 3 (by rfl) ⟨227390, by rfl⟩ : syracuseStep 1212749 = 454781) (by norm_num)
theorem B1212773 : Blo 806344 1212773 := bbase (se 4 (by rfl) ⟨113697, by rfl⟩ : syracuseStep 1212773 = 227395) (by norm_num)
theorem B2457973 : Blo 806344 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B1212797 : Blo 806344 1212797 := bbase (se 3 (by rfl) ⟨227399, by rfl⟩ : syracuseStep 1212797 = 454799) (by norm_num)
theorem B1212821 : Blo 806344 1212821 := bbase (se 6 (by rfl) ⟨28425, by rfl⟩ : syracuseStep 1212821 = 56851) (by norm_num)
theorem B1212845 : Blo 806344 1212845 := bbase (se 3 (by rfl) ⟨227408, by rfl⟩ : syracuseStep 1212845 = 454817) (by norm_num)
theorem B1212869 : Blo 806344 1212869 := bbase (se 4 (by rfl) ⟨113706, by rfl⟩ : syracuseStep 1212869 = 227413) (by norm_num)
theorem B1212893 : Blo 806344 1212893 := bbase (se 3 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 1212893 = 454835) (by norm_num)
theorem B1638893 : Blo 806344 1638893 := bbase (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) (by norm_num)
theorem B1212917 : Blo 806344 1212917 := bbase (se 5 (by rfl) ⟨56855, by rfl⟩ : syracuseStep 1212917 = 113711) (by norm_num)
theorem B1049093 : Blo 806344 1049093 := bbase (se 4 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 1049093 = 196705) (by norm_num)
theorem B1212941 : Blo 806344 1212941 := bbase (se 3 (by rfl) ⟨227426, by rfl⟩ : syracuseStep 1212941 = 454853) (by norm_num)
theorem B1212965 : Blo 806344 1212965 := bbase (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) (by norm_num)
theorem B1212989 : Blo 806344 1212989 := bbase (se 3 (by rfl) ⟨227435, by rfl⟩ : syracuseStep 1212989 = 454871) (by norm_num)
theorem B1213013 : Blo 806344 1213013 := bbase (se 8 (by rfl) ⟨7107, by rfl⟩ : syracuseStep 1213013 = 14215) (by norm_num)
theorem B1213037 : Blo 806344 1213037 := bbase (se 3 (by rfl) ⟨227444, by rfl⟩ : syracuseStep 1213037 = 454889) (by norm_num)
theorem B1213061 : Blo 806344 1213061 := bbase (se 4 (by rfl) ⟨113724, by rfl⟩ : syracuseStep 1213061 = 227449) (by norm_num)
theorem B1311373 : Blo 806344 1311373 := bbase (se 3 (by rfl) ⟨245882, by rfl⟩ : syracuseStep 1311373 = 491765) (by norm_num)
theorem B1213085 : Blo 806344 1213085 := bbase (se 3 (by rfl) ⟨227453, by rfl⟩ : syracuseStep 1213085 = 454907) (by norm_num)
theorem B1213109 : Blo 806344 1213109 := bbase (se 5 (by rfl) ⟨56864, by rfl⟩ : syracuseStep 1213109 = 113729) (by norm_num)
theorem B5833397 : Blo 806344 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B1213133 : Blo 806344 1213133 := bbase (se 3 (by rfl) ⟨227462, by rfl⟩ : syracuseStep 1213133 = 454925) (by norm_num)
theorem B1213157 : Blo 806344 1213157 := bbase (se 4 (by rfl) ⟨113733, by rfl⟩ : syracuseStep 1213157 = 227467) (by norm_num)
theorem B1213181 : Blo 806344 1213181 := bbase (se 3 (by rfl) ⟨227471, by rfl⟩ : syracuseStep 1213181 = 454943) (by norm_num)
theorem B1213205 : Blo 806344 1213205 := bbase (se 6 (by rfl) ⟨28434, by rfl⟩ : syracuseStep 1213205 = 56869) (by norm_num)
theorem B1213229 : Blo 806344 1213229 := bbase (se 3 (by rfl) ⟨227480, by rfl⟩ : syracuseStep 1213229 = 454961) (by norm_num)
theorem B1213253 : Blo 806344 1213253 := bbase (se 4 (by rfl) ⟨113742, by rfl⟩ : syracuseStep 1213253 = 227485) (by norm_num)
theorem B1213277 : Blo 806344 1213277 := bbase (se 3 (by rfl) ⟨227489, by rfl⟩ : syracuseStep 1213277 = 454979) (by norm_num)
theorem B1213301 : Blo 806344 1213301 := bbase (se 5 (by rfl) ⟨56873, by rfl⟩ : syracuseStep 1213301 = 113747) (by norm_num)
theorem B1213325 : Blo 806344 1213325 := bbase (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) (by norm_num)
theorem B1213349 : Blo 806344 1213349 := bbase (se 4 (by rfl) ⟨113751, by rfl⟩ : syracuseStep 1213349 = 227503) (by norm_num)
theorem B1213373 : Blo 806344 1213373 := bbase (se 3 (by rfl) ⟨227507, by rfl⟩ : syracuseStep 1213373 = 455015) (by norm_num)
theorem B1213397 : Blo 806344 1213397 := bbase (se 7 (by rfl) ⟨14219, by rfl⟩ : syracuseStep 1213397 = 28439) (by norm_num)
theorem B2917333 : Blo 806344 2917333 := bbase (se 7 (by rfl) ⟨34187, by rfl⟩ : syracuseStep 2917333 = 68375) (by norm_num)
theorem B1213421 : Blo 806344 1213421 := bbase (se 3 (by rfl) ⟨227516, by rfl⟩ : syracuseStep 1213421 = 455033) (by norm_num)
theorem B1213445 : Blo 806344 1213445 := bbase (se 4 (by rfl) ⟨113760, by rfl⟩ : syracuseStep 1213445 = 227521) (by norm_num)
theorem B1213469 : Blo 806344 1213469 := bbase (se 3 (by rfl) ⟨227525, by rfl⟩ : syracuseStep 1213469 = 455051) (by norm_num)
theorem B1213493 : Blo 806344 1213493 := bbase (se 5 (by rfl) ⟨56882, by rfl⟩ : syracuseStep 1213493 = 113765) (by norm_num)
theorem B1213517 : Blo 806344 1213517 := bbase (se 3 (by rfl) ⟨227534, by rfl⟩ : syracuseStep 1213517 = 455069) (by norm_num)
theorem B1213541 : Blo 806344 1213541 := bbase (se 4 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 1213541 = 227539) (by norm_num)
theorem B4097141 : Blo 806344 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B1213565 : Blo 806344 1213565 := bbase (se 3 (by rfl) ⟨227543, by rfl⟩ : syracuseStep 1213565 = 455087) (by norm_num)
theorem B1213589 : Blo 806344 1213589 := bbase (se 6 (by rfl) ⟨28443, by rfl⟩ : syracuseStep 1213589 = 56887) (by norm_num)
theorem B1213613 : Blo 806344 1213613 := bbase (se 3 (by rfl) ⟨227552, by rfl⟩ : syracuseStep 1213613 = 455105) (by norm_num)
theorem B1213637 : Blo 806344 1213637 := bbase (se 4 (by rfl) ⟨113778, by rfl⟩ : syracuseStep 1213637 = 227557) (by norm_num)
theorem B1213661 : Blo 806344 1213661 := bbase (se 3 (by rfl) ⟨227561, by rfl⟩ : syracuseStep 1213661 = 455123) (by norm_num)
theorem B1148141 : Blo 806344 1148141 := bbase (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) (by norm_num)
theorem B1213685 : Blo 806344 1213685 := bbase (se 5 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 1213685 = 113783) (by norm_num)
theorem B1213709 : Blo 806344 1213709 := bbase (se 3 (by rfl) ⟨227570, by rfl⟩ : syracuseStep 1213709 = 455141) (by norm_num)
theorem B1213733 : Blo 806344 1213733 := bbase (se 4 (by rfl) ⟨113787, by rfl⟩ : syracuseStep 1213733 = 227575) (by norm_num)
theorem B1213757 : Blo 806344 1213757 := bbase (se 3 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 1213757 = 455159) (by norm_num)
theorem B1213781 : Blo 806344 1213781 := bbase (se 12 (by rfl) ⟨444, by rfl⟩ : syracuseStep 1213781 = 889) (by norm_num)
theorem B1213805 : Blo 806344 1213805 := bbase (se 3 (by rfl) ⟨227588, by rfl⟩ : syracuseStep 1213805 = 455177) (by norm_num)
theorem B1213829 : Blo 806344 1213829 := bbase (se 4 (by rfl) ⟨113796, by rfl⟩ : syracuseStep 1213829 = 227593) (by norm_num)
theorem B1213853 : Blo 806344 1213853 := bbase (se 3 (by rfl) ⟨227597, by rfl⟩ : syracuseStep 1213853 = 455195) (by norm_num)
theorem B1213877 : Blo 806344 1213877 := bbase (se 5 (by rfl) ⟨56900, by rfl⟩ : syracuseStep 1213877 = 113801) (by norm_num)
theorem B1213901 : Blo 806344 1213901 := bbase (se 3 (by rfl) ⟨227606, by rfl⟩ : syracuseStep 1213901 = 455213) (by norm_num)
theorem B1213925 : Blo 806344 1213925 := bbase (se 4 (by rfl) ⟨113805, by rfl⟩ : syracuseStep 1213925 = 227611) (by norm_num)
theorem B1476085 : Blo 806344 1476085 := bbase (se 5 (by rfl) ⟨69191, by rfl⟩ : syracuseStep 1476085 = 138383) (by norm_num)
theorem B1213949 : Blo 806344 1213949 := bbase (se 3 (by rfl) ⟨227615, by rfl⟩ : syracuseStep 1213949 = 455231) (by norm_num)
theorem B1213973 : Blo 806344 1213973 := bbase (se 6 (by rfl) ⟨28452, by rfl⟩ : syracuseStep 1213973 = 56905) (by norm_num)
theorem B1213997 : Blo 806344 1213997 := bbase (se 3 (by rfl) ⟨227624, by rfl⟩ : syracuseStep 1213997 = 455249) (by norm_num)
theorem B1214021 : Blo 806344 1214021 := bbase (se 4 (by rfl) ⟨113814, by rfl⟩ : syracuseStep 1214021 = 227629) (by norm_num)
theorem B1214045 : Blo 806344 1214045 := bbase (se 3 (by rfl) ⟨227633, by rfl⟩ : syracuseStep 1214045 = 455267) (by norm_num)
theorem B1214069 : Blo 806344 1214069 := bbase (se 5 (by rfl) ⟨56909, by rfl⟩ : syracuseStep 1214069 = 113819) (by norm_num)
theorem B1214093 : Blo 806344 1214093 := bbase (se 3 (by rfl) ⟨227642, by rfl⟩ : syracuseStep 1214093 = 455285) (by norm_num)
theorem B1214117 : Blo 806344 1214117 := bbase (se 4 (by rfl) ⟨113823, by rfl⟩ : syracuseStep 1214117 = 227647) (by norm_num)
theorem B1640125 : Blo 806344 1640125 := bbase (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) (by norm_num)
theorem B1214141 : Blo 806344 1214141 := bbase (se 3 (by rfl) ⟨227651, by rfl⟩ : syracuseStep 1214141 = 455303) (by norm_num)
theorem B1214165 : Blo 806344 1214165 := bbase (se 7 (by rfl) ⟨14228, by rfl⟩ : syracuseStep 1214165 = 28457) (by norm_num)
theorem B1214189 : Blo 806344 1214189 := bbase (se 3 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 1214189 = 455321) (by norm_num)
theorem B1214213 : Blo 806344 1214213 := bbase (se 4 (by rfl) ⟨113832, by rfl⟩ : syracuseStep 1214213 = 227665) (by norm_num)
theorem B1214237 : Blo 806344 1214237 := bbase (se 3 (by rfl) ⟨227669, by rfl⟩ : syracuseStep 1214237 = 455339) (by norm_num)
theorem B1214261 : Blo 806344 1214261 := bbase (se 5 (by rfl) ⟨56918, by rfl⟩ : syracuseStep 1214261 = 113837) (by norm_num)
theorem B5539637 : Blo 806344 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B1214285 : Blo 806344 1214285 := bbase (se 3 (by rfl) ⟨227678, by rfl⟩ : syracuseStep 1214285 = 455357) (by norm_num)
theorem B2328421 : Blo 806344 2328421 := bbase (se 4 (by rfl) ⟨218289, by rfl⟩ : syracuseStep 2328421 = 436579) (by norm_num)
theorem B1214309 : Blo 806344 1214309 := bbase (se 4 (by rfl) ⟨113841, by rfl⟩ : syracuseStep 1214309 = 227683) (by norm_num)
theorem B2721653 : Blo 806344 2721653 := bbase (se 5 (by rfl) ⟨127577, by rfl⟩ : syracuseStep 2721653 = 255155) (by norm_num)
theorem B1214333 : Blo 806344 1214333 := bbase (se 3 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 1214333 = 455375) (by norm_num)
theorem B1214357 : Blo 806344 1214357 := bbase (se 6 (by rfl) ⟨28461, by rfl⟩ : syracuseStep 1214357 = 56923) (by norm_num)
theorem B1214381 : Blo 806344 1214381 := bbase (se 3 (by rfl) ⟨227696, by rfl⟩ : syracuseStep 1214381 = 455393) (by norm_num)
theorem B1214405 : Blo 806344 1214405 := bbase (se 4 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 1214405 = 227701) (by norm_num)
theorem B1214429 : Blo 806344 1214429 := bbase (se 3 (by rfl) ⟨227705, by rfl⟩ : syracuseStep 1214429 = 455411) (by norm_num)
theorem B1214453 : Blo 806344 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B1214477 : Blo 806344 1214477 := bbase (se 3 (by rfl) ⟨227714, by rfl⟩ : syracuseStep 1214477 = 455429) (by norm_num)
theorem B985105 : Blo 806344 985105 := bbase (se 2 (by rfl) ⟨369414, by rfl⟩ : syracuseStep 985105 = 738829) (by norm_num)
theorem B1214501 : Blo 806344 1214501 := bbase (se 4 (by rfl) ⟨113859, by rfl⟩ : syracuseStep 1214501 = 227719) (by norm_num)
theorem B1214525 : Blo 806344 1214525 := bbase (se 3 (by rfl) ⟨227723, by rfl⟩ : syracuseStep 1214525 = 455447) (by norm_num)
theorem B1214549 : Blo 806344 1214549 := bbase (se 8 (by rfl) ⟨7116, by rfl⟩ : syracuseStep 1214549 = 14233) (by norm_num)
theorem B1214573 : Blo 806344 1214573 := bbase (se 3 (by rfl) ⟨227732, by rfl⟩ : syracuseStep 1214573 = 455465) (by norm_num)
theorem B6228085 : Blo 806344 6228085 := bbase (se 5 (by rfl) ⟨291941, by rfl⟩ : syracuseStep 6228085 = 583883) (by norm_num)
theorem B1214597 : Blo 806344 1214597 := bbase (se 4 (by rfl) ⟨113868, by rfl⟩ : syracuseStep 1214597 = 227737) (by norm_num)
theorem B1214621 : Blo 806344 1214621 := bbase (se 3 (by rfl) ⟨227741, by rfl⟩ : syracuseStep 1214621 = 455483) (by norm_num)
theorem B1214645 : Blo 806344 1214645 := bbase (se 5 (by rfl) ⟨56936, by rfl⟩ : syracuseStep 1214645 = 113873) (by norm_num)
theorem B1214669 : Blo 806344 1214669 := bbase (se 3 (by rfl) ⟨227750, by rfl⟩ : syracuseStep 1214669 = 455501) (by norm_num)
theorem B17500373 : Blo 806344 17500373 := bbase (se 7 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 17500373 = 410165) (by norm_num)
theorem B1214693 : Blo 806344 1214693 := bbase (se 4 (by rfl) ⟨113877, by rfl⟩ : syracuseStep 1214693 = 227755) (by norm_num)
theorem B1214717 : Blo 806344 1214717 := bbase (se 3 (by rfl) ⟨227759, by rfl⟩ : syracuseStep 1214717 = 455519) (by norm_num)
theorem B1214741 : Blo 806344 1214741 := bbase (se 6 (by rfl) ⟨28470, by rfl⟩ : syracuseStep 1214741 = 56941) (by norm_num)
theorem B2722085 : Blo 806344 2722085 := bbase (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) (by norm_num)
theorem B1214765 : Blo 806344 1214765 := bbase (se 3 (by rfl) ⟨227768, by rfl⟩ : syracuseStep 1214765 = 455537) (by norm_num)
theorem B1214789 : Blo 806344 1214789 := bbase (se 4 (by rfl) ⟨113886, by rfl⟩ : syracuseStep 1214789 = 227773) (by norm_num)
theorem B1214813 : Blo 806344 1214813 := bbase (se 3 (by rfl) ⟨227777, by rfl⟩ : syracuseStep 1214813 = 455555) (by norm_num)
theorem B1214837 : Blo 806344 1214837 := bbase (se 5 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 1214837 = 113891) (by norm_num)
theorem B4098437 : Blo 806344 4098437 := bbase (se 4 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 4098437 = 768457) (by norm_num)
theorem B1214861 : Blo 806344 1214861 := bbase (se 3 (by rfl) ⟨227786, by rfl⟩ : syracuseStep 1214861 = 455573) (by norm_num)
theorem B1214885 : Blo 806344 1214885 := bbase (se 4 (by rfl) ⟨113895, by rfl⟩ : syracuseStep 1214885 = 227791) (by norm_num)
theorem B887213 : Blo 806344 887213 := bbase (se 3 (by rfl) ⟨166352, by rfl⟩ : syracuseStep 887213 = 332705) (by norm_num)
theorem B1214909 : Blo 806344 1214909 := bbase (se 3 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 1214909 = 455591) (by norm_num)
theorem B1214933 : Blo 806344 1214933 := bbase (se 7 (by rfl) ⟨14237, by rfl⟩ : syracuseStep 1214933 = 28475) (by norm_num)
theorem B1214957 : Blo 806344 1214957 := bbase (se 3 (by rfl) ⟨227804, by rfl⟩ : syracuseStep 1214957 = 455609) (by norm_num)
theorem B1214981 : Blo 806344 1214981 := bbase (se 4 (by rfl) ⟨113904, by rfl⟩ : syracuseStep 1214981 = 227809) (by norm_num)
theorem B920089 : Blo 806344 920089 := bbase (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) (by norm_num)
theorem B1215005 : Blo 806344 1215005 := bbase (se 3 (by rfl) ⟨227813, by rfl⟩ : syracuseStep 1215005 = 455627) (by norm_num)
theorem B6916661 : Blo 806344 6916661 := bbase (se 5 (by rfl) ⟨324218, by rfl⟩ : syracuseStep 6916661 = 648437) (by norm_num)
theorem B1215029 : Blo 806344 1215029 := bbase (se 5 (by rfl) ⟨56954, by rfl⟩ : syracuseStep 1215029 = 113909) (by norm_num)
theorem B1215053 : Blo 806344 1215053 := bbase (se 3 (by rfl) ⟨227822, by rfl⟩ : syracuseStep 1215053 = 455645) (by norm_num)
theorem B1215077 : Blo 806344 1215077 := bbase (se 4 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 1215077 = 227827) (by norm_num)
theorem B1149565 : Blo 806344 1149565 := bbase (se 3 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 1149565 = 431087) (by norm_num)
theorem B1215101 : Blo 806344 1215101 := bbase (se 3 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 1215101 = 455663) (by norm_num)
theorem B1215125 : Blo 806344 1215125 := bbase (se 6 (by rfl) ⟨28479, by rfl⟩ : syracuseStep 1215125 = 56959) (by norm_num)
theorem B1215149 : Blo 806344 1215149 := bbase (se 3 (by rfl) ⟨227840, by rfl⟩ : syracuseStep 1215149 = 455681) (by norm_num)
theorem B1215173 : Blo 806344 1215173 := bbase (se 4 (by rfl) ⟨113922, by rfl⟩ : syracuseStep 1215173 = 227845) (by norm_num)
theorem B2722517 : Blo 806344 2722517 := bbase (se 7 (by rfl) ⟨31904, by rfl⟩ : syracuseStep 2722517 = 63809) (by norm_num)
theorem B1215197 : Blo 806344 1215197 := bbase (se 3 (by rfl) ⟨227849, by rfl⟩ : syracuseStep 1215197 = 455699) (by norm_num)
theorem B1215221 : Blo 806344 1215221 := bbase (se 5 (by rfl) ⟨56963, by rfl⟩ : syracuseStep 1215221 = 113927) (by norm_num)
theorem B1215245 : Blo 806344 1215245 := bbase (se 3 (by rfl) ⟨227858, by rfl⟩ : syracuseStep 1215245 = 455717) (by norm_num)
theorem B2296613 : Blo 806344 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B1215269 : Blo 806344 1215269 := bbase (se 4 (by rfl) ⟨113931, by rfl⟩ : syracuseStep 1215269 = 227863) (by norm_num)
theorem B1215293 : Blo 806344 1215293 := bbase (se 3 (by rfl) ⟨227867, by rfl⟩ : syracuseStep 1215293 = 455735) (by norm_num)
theorem B1215317 : Blo 806344 1215317 := bbase (se 9 (by rfl) ⟨3560, by rfl⟩ : syracuseStep 1215317 = 7121) (by norm_num)
theorem B1215341 : Blo 806344 1215341 := bbase (se 3 (by rfl) ⟨227876, by rfl⟩ : syracuseStep 1215341 = 455753) (by norm_num)
theorem B1215365 : Blo 806344 1215365 := bbase (se 4 (by rfl) ⟨113940, by rfl⟩ : syracuseStep 1215365 = 227881) (by norm_num)
theorem B1215389 : Blo 806344 1215389 := bbase (se 3 (by rfl) ⟨227885, by rfl⟩ : syracuseStep 1215389 = 455771) (by norm_num)
theorem B1215413 : Blo 806344 1215413 := bbase (se 5 (by rfl) ⟨56972, by rfl⟩ : syracuseStep 1215413 = 113945) (by norm_num)
theorem B986041 : Blo 806344 986041 := bbase (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) (by norm_num)
theorem B1215437 : Blo 806344 1215437 := bbase (se 3 (by rfl) ⟨227894, by rfl⟩ : syracuseStep 1215437 = 455789) (by norm_num)
theorem B1215461 : Blo 806344 1215461 := bbase (se 4 (by rfl) ⟨113949, by rfl⟩ : syracuseStep 1215461 = 227899) (by norm_num)
theorem B1215485 : Blo 806344 1215485 := bbase (se 3 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 1215485 = 455807) (by norm_num)
theorem B1215509 : Blo 806344 1215509 := bbase (se 6 (by rfl) ⟨28488, by rfl⟩ : syracuseStep 1215509 = 56977) (by norm_num)
theorem B2722949 : Blo 806344 2722949 := bbase (se 4 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 2722949 = 510553) (by norm_num)
theorem B1150157 : Blo 806344 1150157 := bbase (se 3 (by rfl) ⟨215654, by rfl⟩ : syracuseStep 1150157 = 431309) (by norm_num)
theorem B2592005 : Blo 806344 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B1150237 : Blo 806344 1150237 := bbase (se 3 (by rfl) ⟨215669, by rfl⟩ : syracuseStep 1150237 = 431339) (by norm_num)
theorem B1051969 : Blo 806344 1051969 := bbase (se 2 (by rfl) ⟨394488, by rfl⟩ : syracuseStep 1051969 = 788977) (by norm_num)
theorem B920965 : Blo 806344 920965 := bbase (se 4 (by rfl) ⟨86340, by rfl⟩ : syracuseStep 920965 = 172681) (by norm_num)
theorem B1150357 : Blo 806344 1150357 := bbase (se 6 (by rfl) ⟨26961, by rfl⟩ : syracuseStep 1150357 = 53923) (by norm_num)
theorem B1478045 : Blo 806344 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B4656565 : Blo 806344 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B2297285 : Blo 806344 2297285 := bbase (se 4 (by rfl) ⟨215370, by rfl⟩ : syracuseStep 2297285 = 430741) (by norm_num)
theorem B1641941 : Blo 806344 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B1150453 : Blo 806344 1150453 := bbase (se 5 (by rfl) ⟨53927, by rfl⟩ : syracuseStep 1150453 = 107855) (by norm_num)
theorem B2723381 : Blo 806344 2723381 := bbase (se 5 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 2723381 = 255317) (by norm_num)
theorem B4099733 : Blo 806344 4099733 := bbase (se 6 (by rfl) ⟨96087, by rfl⟩ : syracuseStep 4099733 = 192175) (by norm_num)
theorem B3444389 : Blo 806344 3444389 := bbase (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) (by norm_num)
theorem B921385 : Blo 806344 921385 := bbase (se 2 (by rfl) ⟨345519, by rfl⟩ : syracuseStep 921385 = 691039) (by norm_num)
theorem B2297717 : Blo 806344 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B2527109 : Blo 806344 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B2723813 : Blo 806344 2723813 := bbase (se 4 (by rfl) ⟨255357, by rfl⟩ : syracuseStep 2723813 = 510715) (by norm_num)
theorem B1150949 : Blo 806344 1150949 := bbase (se 4 (by rfl) ⟨107901, by rfl⟩ : syracuseStep 1150949 = 215803) (by norm_num)
theorem B2101277 : Blo 806344 2101277 := bbase (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) (by norm_num)
theorem B2101349 : Blo 806344 2101349 := bbase (se 4 (by rfl) ⟨197001, by rfl⟩ : syracuseStep 2101349 = 394003) (by norm_num)
theorem B6131861 : Blo 806344 6131861 := bbase (se 6 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 6131861 = 287431) (by norm_num)
theorem B2592917 : Blo 806344 2592917 := bbase (se 6 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 2592917 = 121543) (by norm_num)
theorem B8392949 : Blo 806344 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B2724245 : Blo 806344 2724245 := bbase (se 6 (by rfl) ⟨63849, by rfl⟩ : syracuseStep 2724245 = 127699) (by norm_num)
theorem B1151501 : Blo 806344 1151501 := bbase (se 3 (by rfl) ⟨215906, by rfl⟩ : syracuseStep 1151501 = 431813) (by norm_num)
theorem B11637269 : Blo 806344 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B1053281 : Blo 806344 1053281 := bbase (se 2 (by rfl) ⟨394980, by rfl⟩ : syracuseStep 1053281 = 789961) (by norm_num)
theorem B2298469 : Blo 806344 2298469 := bbase (se 4 (by rfl) ⟨215481, by rfl⟩ : syracuseStep 2298469 = 430963) (by norm_num)
theorem B922237 : Blo 806344 922237 := bbase (se 3 (by rfl) ⟨172919, by rfl⟩ : syracuseStep 922237 = 345839) (by norm_num)
theorem B1020701 : Blo 806344 1020701 := bbase (se 3 (by rfl) ⟨191381, by rfl⟩ : syracuseStep 1020701 = 382763) (by norm_num)
theorem B2724677 : Blo 806344 2724677 := bbase (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) (by norm_num)
theorem B1020757 : Blo 806344 1020757 := bbase (se 9 (by rfl) ⟨2990, by rfl⟩ : syracuseStep 1020757 = 5981) (by norm_num)
theorem B1381277 : Blo 806344 1381277 := bbase (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) (by norm_num)
theorem B4101029 : Blo 806344 4101029 := bbase (se 4 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 4101029 = 768943) (by norm_num)
theorem B1020853 : Blo 806344 1020853 := bbase (se 5 (by rfl) ⟨47852, by rfl⟩ : syracuseStep 1020853 = 95705) (by norm_num)
theorem B1021025 : Blo 806344 1021025 := bbase (se 2 (by rfl) ⟨382884, by rfl⟩ : syracuseStep 1021025 = 765769) (by norm_num)
theorem B1021081 : Blo 806344 1021081 := bbase (se 2 (by rfl) ⟨382905, by rfl⟩ : syracuseStep 1021081 = 765811) (by norm_num)
theorem B2725109 : Blo 806344 2725109 := bbase (se 5 (by rfl) ⟨127739, by rfl⟩ : syracuseStep 2725109 = 255479) (by norm_num)
theorem B1021177 : Blo 806344 1021177 := bbase (se 2 (by rfl) ⟨382941, by rfl⟩ : syracuseStep 1021177 = 765883) (by norm_num)
theorem B1152253 : Blo 806344 1152253 := bbase (se 3 (by rfl) ⟨216047, by rfl⟩ : syracuseStep 1152253 = 432095) (by norm_num)
theorem B3446165 : Blo 806344 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B1938853 : Blo 806344 1938853 := bbase (se 4 (by rfl) ⟨181767, by rfl⟩ : syracuseStep 1938853 = 363535) (by norm_num)
theorem B1021349 : Blo 806344 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B2594261 : Blo 806344 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B1021405 : Blo 806344 1021405 := bbase (se 3 (by rfl) ⟨191513, by rfl⟩ : syracuseStep 1021405 = 383027) (by norm_num)
theorem B1021501 : Blo 806344 1021501 := bbase (se 3 (by rfl) ⟨191531, by rfl⟩ : syracuseStep 1021501 = 383063) (by norm_num)
theorem B1119853 : Blo 806344 1119853 := bbase (se 3 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 1119853 = 419945) (by norm_num)
theorem B2725541 : Blo 806344 2725541 := bbase (se 4 (by rfl) ⟨255519, by rfl⟩ : syracuseStep 2725541 = 511039) (by norm_num)
theorem B1021673 : Blo 806344 1021673 := bbase (se 2 (by rfl) ⟨383127, by rfl⟩ : syracuseStep 1021673 = 766255) (by norm_num)
theorem B1021729 : Blo 806344 1021729 := bbase (se 2 (by rfl) ⟨383148, by rfl⟩ : syracuseStep 1021729 = 766297) (by norm_num)
theorem B1382213 : Blo 806344 1382213 := bbase (se 4 (by rfl) ⟨129582, by rfl⟩ : syracuseStep 1382213 = 259165) (by norm_num)
theorem B1939277 : Blo 806344 1939277 := bbase (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) (by norm_num)
theorem B1021825 : Blo 806344 1021825 := bbase (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) (by norm_num)
theorem B13277141 : Blo 806344 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B1153045 : Blo 806344 1153045 := bbase (se 6 (by rfl) ⟨27024, by rfl⟩ : syracuseStep 1153045 = 54049) (by norm_num)
theorem B1021997 : Blo 806344 1021997 := bbase (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) (by norm_num)
theorem B2725973 : Blo 806344 2725973 := bbase (se 8 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 2725973 = 31945) (by norm_num)
theorem B1022053 : Blo 806344 1022053 := bbase (se 4 (by rfl) ⟨95817, by rfl⟩ : syracuseStep 1022053 = 191635) (by norm_num)
theorem B1939565 : Blo 806344 1939565 := bbase (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) (by norm_num)
theorem B4102325 : Blo 806344 4102325 := bbase (se 5 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 4102325 = 384593) (by norm_num)
theorem B1022149 : Blo 806344 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B1841437 : Blo 806344 1841437 := bbase (se 3 (by rfl) ⟨345269, by rfl⟩ : syracuseStep 1841437 = 690539) (by norm_num)
theorem B17733973 : Blo 806344 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B1153381 : Blo 806344 1153381 := bbase (se 4 (by rfl) ⟨108129, by rfl⟩ : syracuseStep 1153381 = 216259) (by norm_num)
theorem B1022321 : Blo 806344 1022321 := bbase (se 2 (by rfl) ⟨383370, by rfl⟩ : syracuseStep 1022321 = 766741) (by norm_num)
theorem B3447157 : Blo 806344 3447157 := bbase (se 5 (by rfl) ⟨161585, by rfl⟩ : syracuseStep 3447157 = 323171) (by norm_num)
theorem B1382789 : Blo 806344 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B1841557 : Blo 806344 1841557 := bbase (se 6 (by rfl) ⟨43161, by rfl⟩ : syracuseStep 1841557 = 86323) (by norm_num)
theorem B1022377 : Blo 806344 1022377 := bbase (se 2 (by rfl) ⟨383391, by rfl⟩ : syracuseStep 1022377 = 766783) (by norm_num)
theorem B2726405 : Blo 806344 2726405 := bbase (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) (by norm_num)
theorem B1022473 : Blo 806344 1022473 := bbase (se 2 (by rfl) ⟨383427, by rfl⟩ : syracuseStep 1022473 = 766855) (by norm_num)
theorem B1153597 : Blo 806344 1153597 := bbase (se 3 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 1153597 = 432599) (by norm_num)
theorem B4659797 : Blo 806344 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B1022645 : Blo 806344 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B4365013 : Blo 806344 4365013 := bbase (se 7 (by rfl) ⟨51152, by rfl⟩ : syracuseStep 4365013 = 102305) (by norm_num)
theorem B1022701 : Blo 806344 1022701 := bbase (se 3 (by rfl) ⟨191756, by rfl⟩ : syracuseStep 1022701 = 383513) (by norm_num)
theorem B1022797 : Blo 806344 1022797 := bbase (se 3 (by rfl) ⟨191774, by rfl⟩ : syracuseStep 1022797 = 383549) (by norm_num)
theorem B2595685 : Blo 806344 2595685 := bbase (se 4 (by rfl) ⟨243345, by rfl⟩ : syracuseStep 2595685 = 486691) (by norm_num)
theorem B2726837 : Blo 806344 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B1842149 : Blo 806344 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B1022969 : Blo 806344 1022969 := bbase (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) (by norm_num)
theorem B1023025 : Blo 806344 1023025 := bbase (se 2 (by rfl) ⟨383634, by rfl⟩ : syracuseStep 1023025 = 767269) (by norm_num)
theorem B1023121 : Blo 806344 1023121 := bbase (se 2 (by rfl) ⟨383670, by rfl⟩ : syracuseStep 1023121 = 767341) (by norm_num)
theorem B1383637 : Blo 806344 1383637 := bbase (se 7 (by rfl) ⟨16214, by rfl⟩ : syracuseStep 1383637 = 32429) (by norm_num)
theorem B1023293 : Blo 806344 1023293 := bbase (se 3 (by rfl) ⟨191867, by rfl⟩ : syracuseStep 1023293 = 383735) (by norm_num)
theorem B2727269 : Blo 806344 2727269 := bbase (se 4 (by rfl) ⟨255681, by rfl⟩ : syracuseStep 2727269 = 511363) (by norm_num)
theorem B1023349 : Blo 806344 1023349 := bbase (se 5 (by rfl) ⟨47969, by rfl⟩ : syracuseStep 1023349 = 95939) (by norm_num)
theorem B2301317 : Blo 806344 2301317 := bbase (se 4 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 2301317 = 431497) (by norm_num)
theorem B1023445 : Blo 806344 1023445 := bbase (se 7 (by rfl) ⟨11993, by rfl⟩ : syracuseStep 1023445 = 23987) (by norm_num)
theorem B2334197 : Blo 806344 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1383925 : Blo 806344 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B2367029 : Blo 806344 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B1023617 : Blo 806344 1023617 := bbase (se 2 (by rfl) ⟨383856, by rfl⟩ : syracuseStep 1023617 = 767713) (by norm_num)
theorem B1023673 : Blo 806344 1023673 := bbase (se 2 (by rfl) ⟨383877, by rfl⟩ : syracuseStep 1023673 = 767755) (by norm_num)
theorem B2727701 : Blo 806344 2727701 := bbase (se 6 (by rfl) ⟨63930, by rfl⟩ : syracuseStep 2727701 = 127861) (by norm_num)
theorem B2629397 : Blo 806344 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B1023769 : Blo 806344 1023769 := bbase (se 2 (by rfl) ⟨383913, by rfl⟩ : syracuseStep 1023769 = 767827) (by norm_num)
theorem B1023941 : Blo 806344 1023941 := bbase (se 4 (by rfl) ⟨95994, by rfl⟩ : syracuseStep 1023941 = 191989) (by norm_num)
theorem B1023997 : Blo 806344 1023997 := bbase (se 3 (by rfl) ⟨191999, by rfl⟩ : syracuseStep 1023997 = 383999) (by norm_num)
theorem B1024093 : Blo 806344 1024093 := bbase (se 3 (by rfl) ⟨192017, by rfl⟩ : syracuseStep 1024093 = 384035) (by norm_num)
theorem B2728133 : Blo 806344 2728133 := bbase (se 4 (by rfl) ⟨255762, by rfl⟩ : syracuseStep 2728133 = 511525) (by norm_num)
theorem B1024265 : Blo 806344 1024265 := bbase (se 2 (by rfl) ⟨384099, by rfl⟩ : syracuseStep 1024265 = 768199) (by norm_num)
theorem B1024321 : Blo 806344 1024321 := bbase (se 2 (by rfl) ⟨384120, by rfl⟩ : syracuseStep 1024321 = 768241) (by norm_num)
theorem B1024417 : Blo 806344 1024417 := bbase (se 2 (by rfl) ⟨384156, by rfl⟩ : syracuseStep 1024417 = 768313) (by norm_num)
theorem B2302501 : Blo 806344 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B1024589 : Blo 806344 1024589 := bbase (se 3 (by rfl) ⟨192110, by rfl⟩ : syracuseStep 1024589 = 384221) (by norm_num)
theorem B2728565 : Blo 806344 2728565 := bbase (se 5 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 2728565 = 255803) (by norm_num)
theorem B1024645 : Blo 806344 1024645 := bbase (se 4 (by rfl) ⟨96060, by rfl⟩ : syracuseStep 1024645 = 192121) (by norm_num)
theorem B2302661 : Blo 806344 2302661 := bbase (se 4 (by rfl) ⟨215874, by rfl⟩ : syracuseStep 2302661 = 431749) (by norm_num)
theorem B1024741 : Blo 806344 1024741 := bbase (se 4 (by rfl) ⟨96069, by rfl⟩ : syracuseStep 1024741 = 192139) (by norm_num)
theorem B1024913 : Blo 806344 1024913 := bbase (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) (by norm_num)
theorem B2302901 : Blo 806344 2302901 := bbase (se 5 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 2302901 = 215897) (by norm_num)
theorem B1024969 : Blo 806344 1024969 := bbase (se 2 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 1024969 = 768727) (by norm_num)
theorem B2728997 : Blo 806344 2728997 := bbase (se 4 (by rfl) ⟨255843, by rfl⟩ : syracuseStep 2728997 = 511687) (by norm_num)
theorem B1025065 : Blo 806344 1025065 := bbase (se 2 (by rfl) ⟨384399, by rfl⟩ : syracuseStep 1025065 = 768799) (by norm_num)
theorem B2303093 : Blo 806344 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B1942717 : Blo 806344 1942717 := bbase (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) (by norm_num)
theorem B1025237 : Blo 806344 1025237 := bbase (se 7 (by rfl) ⟨12014, by rfl⟩ : syracuseStep 1025237 = 24029) (by norm_num)
theorem B861401 : Blo 806344 861401 := bbase (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) (by norm_num)
theorem B1090789 : Blo 806344 1090789 := bbase (se 4 (by rfl) ⟨102261, by rfl⟩ : syracuseStep 1090789 = 204523) (by norm_num)
theorem B1025293 : Blo 806344 1025293 := bbase (se 3 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 1025293 = 384485) (by norm_num)
theorem B2041109 : Blo 806344 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B861473 : Blo 806344 861473 := bbase (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) (by norm_num)
theorem B1025389 : Blo 806344 1025389 := bbase (se 3 (by rfl) ⟨192260, by rfl⟩ : syracuseStep 1025389 = 384521) (by norm_num)
theorem B3876245 : Blo 806344 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B6235541 : Blo 806344 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B2041301 : Blo 806344 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B2729429 : Blo 806344 2729429 := bbase (se 7 (by rfl) ⟨31985, by rfl⟩ : syracuseStep 2729429 = 63971) (by norm_num)
theorem B861661 : Blo 806344 861661 := bbase (se 3 (by rfl) ⟨161561, by rfl⟩ : syracuseStep 861661 = 323123) (by norm_num)
theorem B1025561 : Blo 806344 1025561 := bbase (se 2 (by rfl) ⟨384585, by rfl⟩ : syracuseStep 1025561 = 769171) (by norm_num)
theorem B861845 : Blo 806344 861845 := bbase (se 6 (by rfl) ⟨20199, by rfl⟩ : syracuseStep 861845 = 40399) (by norm_num)
theorem B2041645 : Blo 806344 2041645 := bbase (se 3 (by rfl) ⟨382808, by rfl⟩ : syracuseStep 2041645 = 765617) (by norm_num)
theorem B1943389 : Blo 806344 1943389 := bbase (se 3 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 1943389 = 728771) (by norm_num)
theorem B2729861 : Blo 806344 2729861 := bbase (se 4 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 2729861 = 511849) (by norm_num)
theorem B2041757 : Blo 806344 2041757 := bbase (se 3 (by rfl) ⟨382829, by rfl⟩ : syracuseStep 2041757 = 765659) (by norm_num)
theorem B1943621 : Blo 806344 1943621 := bbase (se 4 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 1943621 = 364429) (by norm_num)
theorem B2304085 : Blo 806344 2304085 := bbase (se 8 (by rfl) ⟨13500, by rfl⟩ : syracuseStep 2304085 = 27001) (by norm_num)
theorem B2041949 : Blo 806344 2041949 := bbase (se 3 (by rfl) ⟨382865, by rfl⟩ : syracuseStep 2041949 = 765731) (by norm_num)
theorem B5187701 : Blo 806344 5187701 := bbase (se 5 (by rfl) ⟨243173, by rfl⟩ : syracuseStep 5187701 = 486347) (by norm_num)
theorem B1943765 : Blo 806344 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B1943813 : Blo 806344 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B2074901 : Blo 806344 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B2730293 : Blo 806344 2730293 := bbase (se 5 (by rfl) ⟨127982, by rfl⟩ : syracuseStep 2730293 = 255965) (by norm_num)
theorem B862597 : Blo 806344 862597 := bbase (se 4 (by rfl) ⟨80868, by rfl⟩ : syracuseStep 862597 = 161737) (by norm_num)
theorem B1091989 : Blo 806344 1091989 := bbase (se 6 (by rfl) ⟨25593, by rfl⟩ : syracuseStep 1091989 = 51187) (by norm_num)
theorem B2042293 : Blo 806344 2042293 := bbase (se 5 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 2042293 = 191465) (by norm_num)
theorem B862669 : Blo 806344 862669 := bbase (se 3 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 862669 = 323501) (by norm_num)
theorem B2042405 : Blo 806344 2042405 := bbase (se 4 (by rfl) ⟨191475, by rfl⟩ : syracuseStep 2042405 = 382951) (by norm_num)
theorem B1944101 : Blo 806344 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B862849 : Blo 806344 862849 := bbase (se 2 (by rfl) ⟨323568, by rfl⟩ : syracuseStep 862849 = 647137) (by norm_num)
theorem B2042597 : Blo 806344 2042597 := bbase (se 4 (by rfl) ⟨191493, by rfl⟩ : syracuseStep 2042597 = 382987) (by norm_num)
theorem B2730725 : Blo 806344 2730725 := bbase (se 4 (by rfl) ⟨256005, by rfl⟩ : syracuseStep 2730725 = 512011) (by norm_num)
theorem B2796373 : Blo 806344 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B2042941 : Blo 806344 2042941 := bbase (se 3 (by rfl) ⟨383051, by rfl⟩ : syracuseStep 2042941 = 766103) (by norm_num)
theorem B863293 : Blo 806344 863293 := bbase (se 3 (by rfl) ⟨161867, by rfl⟩ : syracuseStep 863293 = 323735) (by norm_num)
theorem B2370629 : Blo 806344 2370629 := bbase (se 4 (by rfl) ⟨222246, by rfl⟩ : syracuseStep 2370629 = 444493) (by norm_num)
theorem B2731157 : Blo 806344 2731157 := bbase (se 6 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 2731157 = 128023) (by norm_num)
theorem B2305189 : Blo 806344 2305189 := bbase (se 4 (by rfl) ⟨216111, by rfl⟩ : syracuseStep 2305189 = 432223) (by norm_num)
theorem B2043053 : Blo 806344 2043053 := bbase (se 3 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 2043053 = 766145) (by norm_num)
theorem B863417 : Blo 806344 863417 := bbase (se 2 (by rfl) ⟨323781, by rfl⟩ : syracuseStep 863417 = 647563) (by norm_num)
theorem B3452165 : Blo 806344 3452165 := bbase (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) (by norm_num)
theorem B4599125 : Blo 806344 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B2043245 : Blo 806344 2043245 := bbase (se 3 (by rfl) ⟨383108, by rfl⟩ : syracuseStep 2043245 = 766217) (by norm_num)
theorem B863669 : Blo 806344 863669 := bbase (se 5 (by rfl) ⟨40484, by rfl⟩ : syracuseStep 863669 = 80969) (by norm_num)
theorem B3452453 : Blo 806344 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B2731589 : Blo 806344 2731589 := bbase (se 4 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 2731589 = 512173) (by norm_num)
theorem B4140725 : Blo 806344 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B2043589 : Blo 806344 2043589 := bbase (se 4 (by rfl) ⟨191586, by rfl⟩ : syracuseStep 2043589 = 383173) (by norm_num)
theorem B6139637 : Blo 806344 6139637 := bbase (se 5 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 6139637 = 575591) (by norm_num)
theorem B1814309 : Blo 806344 1814309 := bbase (se 4 (by rfl) ⟨170091, by rfl⟩ : syracuseStep 1814309 = 340183) (by norm_num)
theorem B2043701 : Blo 806344 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B1453925 : Blo 806344 1453925 := bbase (se 4 (by rfl) ⟨136305, by rfl⟩ : syracuseStep 1453925 = 272611) (by norm_num)
theorem B3321701 : Blo 806344 3321701 := bbase (se 4 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 3321701 = 622819) (by norm_num)
theorem B1814381 : Blo 806344 1814381 := bbase (se 3 (by rfl) ⟨340196, by rfl⟩ : syracuseStep 1814381 = 680393) (by norm_num)
theorem B864113 : Blo 806344 864113 := bbase (se 2 (by rfl) ⟨324042, by rfl⟩ : syracuseStep 864113 = 648085) (by norm_num)
theorem B4665205 : Blo 806344 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B1814453 : Blo 806344 1814453 := bbase (se 5 (by rfl) ⟨85052, by rfl⟩ : syracuseStep 1814453 = 170105) (by norm_num)
theorem B2043893 : Blo 806344 2043893 := bbase (se 5 (by rfl) ⟨95807, by rfl⟩ : syracuseStep 2043893 = 191615) (by norm_num)
theorem B2732021 : Blo 806344 2732021 := bbase (se 5 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 2732021 = 256127) (by norm_num)
theorem B1814525 : Blo 806344 1814525 := bbase (se 3 (by rfl) ⟨340223, by rfl⟩ : syracuseStep 1814525 = 680447) (by norm_num)
theorem B1814597 : Blo 806344 1814597 := bbase (se 4 (by rfl) ⟨170118, by rfl⟩ : syracuseStep 1814597 = 340237) (by norm_num)
theorem B864361 : Blo 806344 864361 := bbase (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) (by norm_num)
theorem B1454213 : Blo 806344 1454213 := bbase (se 4 (by rfl) ⟨136332, by rfl⟩ : syracuseStep 1454213 = 272665) (by norm_num)
theorem B1814669 : Blo 806344 1814669 := bbase (se 3 (by rfl) ⟨340250, by rfl⟩ : syracuseStep 1814669 = 680501) (by norm_num)
theorem B1814741 : Blo 806344 1814741 := bbase (se 7 (by rfl) ⟨21266, by rfl⟩ : syracuseStep 1814741 = 42533) (by norm_num)
theorem B3453205 : Blo 806344 3453205 := bbase (se 6 (by rfl) ⟨80934, by rfl⟩ : syracuseStep 3453205 = 161869) (by norm_num)
theorem B1814813 : Blo 806344 1814813 := bbase (se 3 (by rfl) ⟨340277, by rfl⟩ : syracuseStep 1814813 = 680555) (by norm_num)
theorem B1847621 : Blo 806344 1847621 := bbase (se 4 (by rfl) ⟨173214, by rfl⟩ : syracuseStep 1847621 = 346429) (by norm_num)
theorem B2044237 : Blo 806344 2044237 := bbase (se 3 (by rfl) ⟨383294, by rfl⟩ : syracuseStep 2044237 = 766589) (by norm_num)
theorem B1454429 : Blo 806344 1454429 := bbase (se 3 (by rfl) ⟨272705, by rfl⟩ : syracuseStep 1454429 = 545411) (by norm_num)
theorem B1814885 : Blo 806344 1814885 := bbase (se 4 (by rfl) ⟨170145, by rfl⟩ : syracuseStep 1814885 = 340291) (by norm_num)
theorem B2732453 : Blo 806344 2732453 := bbase (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) (by norm_num)
theorem B1814957 : Blo 806344 1814957 := bbase (se 3 (by rfl) ⟨340304, by rfl⟩ : syracuseStep 1814957 = 680609) (by norm_num)
theorem B2044349 : Blo 806344 2044349 := bbase (se 3 (by rfl) ⟨383315, by rfl⟩ : syracuseStep 2044349 = 766631) (by norm_num)
theorem B1815029 : Blo 806344 1815029 := bbase (se 5 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 1815029 = 170159) (by norm_num)
theorem B864805 : Blo 806344 864805 := bbase (se 4 (by rfl) ⟨81075, by rfl⟩ : syracuseStep 864805 = 162151) (by norm_num)
theorem B1815101 : Blo 806344 1815101 := bbase (se 3 (by rfl) ⟨340331, by rfl⟩ : syracuseStep 1815101 = 680663) (by norm_num)
theorem B864865 : Blo 806344 864865 := bbase (se 2 (by rfl) ⟨324324, by rfl⟩ : syracuseStep 864865 = 648649) (by norm_num)
theorem B2044541 : Blo 806344 2044541 := bbase (se 3 (by rfl) ⟨383351, by rfl⟩ : syracuseStep 2044541 = 766703) (by norm_num)
theorem B1815173 : Blo 806344 1815173 := bbase (se 4 (by rfl) ⟨170172, by rfl⟩ : syracuseStep 1815173 = 340345) (by norm_num)
theorem B2306693 : Blo 806344 2306693 := bbase (se 4 (by rfl) ⟨216252, by rfl⟩ : syracuseStep 2306693 = 432505) (by norm_num)
theorem B1815245 : Blo 806344 1815245 := bbase (se 3 (by rfl) ⟨340358, by rfl⟩ : syracuseStep 1815245 = 680717) (by norm_num)
theorem B1815317 : Blo 806344 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B2732885 : Blo 806344 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B1815389 : Blo 806344 1815389 := bbase (se 3 (by rfl) ⟨340385, by rfl⟩ : syracuseStep 1815389 = 680771) (by norm_num)
theorem B2274149 : Blo 806344 2274149 := bbase (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) (by norm_num)
theorem B2077589 : Blo 806344 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B865181 : Blo 806344 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B1815461 : Blo 806344 1815461 := bbase (se 4 (by rfl) ⟨170199, by rfl⟩ : syracuseStep 1815461 = 340399) (by norm_num)
theorem B1946533 : Blo 806344 1946533 := bbase (se 4 (by rfl) ⟨182487, by rfl⟩ : syracuseStep 1946533 = 364975) (by norm_num)
theorem B6894517 : Blo 806344 6894517 := bbase (se 5 (by rfl) ⟨323180, by rfl⟩ : syracuseStep 6894517 = 646361) (by norm_num)
theorem B2044885 : Blo 806344 2044885 := bbase (se 7 (by rfl) ⟨23963, by rfl⟩ : syracuseStep 2044885 = 47927) (by norm_num)
theorem B2077661 : Blo 806344 2077661 := bbase (se 3 (by rfl) ⟨389561, by rfl⟩ : syracuseStep 2077661 = 779123) (by norm_num)
theorem B1815533 : Blo 806344 1815533 := bbase (se 3 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 1815533 = 680825) (by norm_num)
theorem B3453941 : Blo 806344 3453941 := bbase (se 5 (by rfl) ⟨161903, by rfl⟩ : syracuseStep 3453941 = 323807) (by norm_num)
theorem B832501 : Blo 806344 832501 := bbase (se 5 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 832501 = 78047) (by norm_num)
theorem B1815605 : Blo 806344 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B2044997 : Blo 806344 2044997 := bbase (se 4 (by rfl) ⟨191718, by rfl⟩ : syracuseStep 2044997 = 383437) (by norm_num)
theorem B1815677 : Blo 806344 1815677 := bbase (se 3 (by rfl) ⟨340439, by rfl⟩ : syracuseStep 1815677 = 680879) (by norm_num)
theorem B1455293 : Blo 806344 1455293 := bbase (se 3 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 1455293 = 545735) (by norm_num)
theorem B1815749 : Blo 806344 1815749 := bbase (se 4 (by rfl) ⟨170226, by rfl⟩ : syracuseStep 1815749 = 340453) (by norm_num)
theorem B2045189 : Blo 806344 2045189 := bbase (se 4 (by rfl) ⟨191736, by rfl⟩ : syracuseStep 2045189 = 383473) (by norm_num)
theorem B2733317 : Blo 806344 2733317 := bbase (se 4 (by rfl) ⟨256248, by rfl⟩ : syracuseStep 2733317 = 512497) (by norm_num)
theorem B1815821 : Blo 806344 1815821 := bbase (se 3 (by rfl) ⟨340466, by rfl⟩ : syracuseStep 1815821 = 680933) (by norm_num)
theorem B1094941 : Blo 806344 1094941 := bbase (se 3 (by rfl) ⟨205301, by rfl⟩ : syracuseStep 1094941 = 410603) (by norm_num)
theorem B1815893 : Blo 806344 1815893 := bbase (se 13 (by rfl) ⟨332, by rfl⟩ : syracuseStep 1815893 = 665) (by norm_num)
theorem B1291621 : Blo 806344 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B1815965 : Blo 806344 1815965 := bbase (se 3 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 1815965 = 680987) (by norm_num)
theorem B1455517 : Blo 806344 1455517 := bbase (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) (by norm_num)
theorem B1095125 : Blo 806344 1095125 := bbase (se 7 (by rfl) ⟨12833, by rfl⟩ : syracuseStep 1095125 = 25667) (by norm_num)
theorem B1816037 : Blo 806344 1816037 := bbase (se 4 (by rfl) ⟨170253, by rfl⟩ : syracuseStep 1816037 = 340507) (by norm_num)
theorem B2078245 : Blo 806344 2078245 := bbase (se 4 (by rfl) ⟨194835, by rfl⟩ : syracuseStep 2078245 = 389671) (by norm_num)
theorem B1816109 : Blo 806344 1816109 := bbase (se 3 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 1816109 = 681041) (by norm_num)
theorem B6207029 : Blo 806344 6207029 := bbase (se 5 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 6207029 = 581909) (by norm_num)
theorem B2045533 : Blo 806344 2045533 := bbase (se 3 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 2045533 = 767075) (by norm_num)
theorem B1291877 : Blo 806344 1291877 := bbase (se 4 (by rfl) ⟨121113, by rfl⟩ : syracuseStep 1291877 = 242227) (by norm_num)
theorem B1816181 : Blo 806344 1816181 := bbase (se 5 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 1816181 = 170267) (by norm_num)
theorem B2733749 : Blo 806344 2733749 := bbase (se 5 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 2733749 = 256289) (by norm_num)
theorem B1816253 : Blo 806344 1816253 := bbase (se 3 (by rfl) ⟨340547, by rfl⟩ : syracuseStep 1816253 = 681095) (by norm_num)
theorem B2045645 : Blo 806344 2045645 := bbase (se 3 (by rfl) ⟨383558, by rfl⟩ : syracuseStep 2045645 = 767117) (by norm_num)
theorem B1816325 : Blo 806344 1816325 := bbase (se 4 (by rfl) ⟨170280, by rfl⟩ : syracuseStep 1816325 = 340561) (by norm_num)
theorem B1292069 : Blo 806344 1292069 := bbase (se 4 (by rfl) ⟨121131, by rfl⟩ : syracuseStep 1292069 = 242263) (by norm_num)
theorem B3684149 : Blo 806344 3684149 := bbase (se 5 (by rfl) ⟨172694, by rfl⟩ : syracuseStep 3684149 = 345389) (by norm_num)
theorem B1816397 : Blo 806344 1816397 := bbase (se 3 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 1816397 = 681149) (by norm_num)
theorem B2045837 : Blo 806344 2045837 := bbase (se 3 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 2045837 = 767189) (by norm_num)
theorem B1816469 : Blo 806344 1816469 := bbase (se 6 (by rfl) ⟨42573, by rfl⟩ : syracuseStep 1816469 = 85147) (by norm_num)
theorem B5191573 : Blo 806344 5191573 := bbase (se 6 (by rfl) ⟨121677, by rfl⟩ : syracuseStep 5191573 = 243355) (by norm_num)
theorem B1816541 : Blo 806344 1816541 := bbase (se 3 (by rfl) ⟨340601, by rfl⟩ : syracuseStep 1816541 = 681203) (by norm_num)
theorem B1816613 : Blo 806344 1816613 := bbase (se 4 (by rfl) ⟨170307, by rfl⟩ : syracuseStep 1816613 = 340615) (by norm_num)
theorem B2734181 : Blo 806344 2734181 := bbase (se 4 (by rfl) ⟨256329, by rfl⟩ : syracuseStep 2734181 = 512659) (by norm_num)
theorem B1816685 : Blo 806344 1816685 := bbase (se 3 (by rfl) ⟨340628, by rfl⟩ : syracuseStep 1816685 = 681257) (by norm_num)
theorem B1816757 : Blo 806344 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B2046181 : Blo 806344 2046181 := bbase (se 4 (by rfl) ⟨191829, by rfl⟩ : syracuseStep 2046181 = 383659) (by norm_num)
theorem B1816829 : Blo 806344 1816829 := bbase (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) (by norm_num)
theorem B1816901 : Blo 806344 1816901 := bbase (se 4 (by rfl) ⟨170334, by rfl⟩ : syracuseStep 1816901 = 340669) (by norm_num)
theorem B2046293 : Blo 806344 2046293 := bbase (se 10 (by rfl) ⟨2997, by rfl⟩ : syracuseStep 2046293 = 5995) (by norm_num)
theorem B1227125 : Blo 806344 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B1816973 : Blo 806344 1816973 := bbase (se 3 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 1816973 = 681365) (by norm_num)
theorem B1817045 : Blo 806344 1817045 := bbase (se 7 (by rfl) ⟨21293, by rfl⟩ : syracuseStep 1817045 = 42587) (by norm_num)
theorem B2046485 : Blo 806344 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B2734613 : Blo 806344 2734613 := bbase (se 6 (by rfl) ⟨64092, by rfl⟩ : syracuseStep 2734613 = 128185) (by norm_num)
theorem B1817117 : Blo 806344 1817117 := bbase (se 3 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 1817117 = 681419) (by norm_num)
theorem B1817189 : Blo 806344 1817189 := bbase (se 4 (by rfl) ⟨170361, by rfl⟩ : syracuseStep 1817189 = 340723) (by norm_num)
theorem B1817261 : Blo 806344 1817261 := bbase (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) (by norm_num)
theorem B1293005 : Blo 806344 1293005 := bbase (se 3 (by rfl) ⟨242438, by rfl⟩ : syracuseStep 1293005 = 484877) (by norm_num)
theorem B1817333 : Blo 806344 1817333 := bbase (se 5 (by rfl) ⟨85187, by rfl⟩ : syracuseStep 1817333 = 170375) (by norm_num)
theorem B1817405 : Blo 806344 1817405 := bbase (se 3 (by rfl) ⟨340763, by rfl⟩ : syracuseStep 1817405 = 681527) (by norm_num)
theorem B2046829 : Blo 806344 2046829 := bbase (se 3 (by rfl) ⟨383780, by rfl⟩ : syracuseStep 2046829 = 767561) (by norm_num)
theorem B6896501 : Blo 806344 6896501 := bbase (se 5 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 6896501 = 646547) (by norm_num)
theorem B1817477 : Blo 806344 1817477 := bbase (se 4 (by rfl) ⟨170388, by rfl⟩ : syracuseStep 1817477 = 340777) (by norm_num)
theorem B1817549 : Blo 806344 1817549 := bbase (se 3 (by rfl) ⟨340790, by rfl⟩ : syracuseStep 1817549 = 681581) (by norm_num)
theorem B18889685 : Blo 806344 18889685 := bbase (se 7 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 18889685 = 442727) (by norm_num)
theorem B2046941 : Blo 806344 2046941 := bbase (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) (by norm_num)
theorem B2767877 : Blo 806344 2767877 := bbase (se 4 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 2767877 = 518977) (by norm_num)
theorem B1817621 : Blo 806344 1817621 := bbase (se 6 (by rfl) ⟨42600, by rfl⟩ : syracuseStep 1817621 = 85201) (by norm_num)
theorem B1293389 : Blo 806344 1293389 := bbase (se 3 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 1293389 = 485021) (by norm_num)
theorem B1817693 : Blo 806344 1817693 := bbase (se 3 (by rfl) ⟨340817, by rfl⟩ : syracuseStep 1817693 = 681635) (by norm_num)
theorem B1227917 : Blo 806344 1227917 := bbase (se 3 (by rfl) ⟨230234, by rfl⟩ : syracuseStep 1227917 = 460469) (by norm_num)
theorem B2047133 : Blo 806344 2047133 := bbase (se 3 (by rfl) ⟨383837, by rfl⟩ : syracuseStep 2047133 = 767675) (by norm_num)
theorem B1817765 : Blo 806344 1817765 := bbase (se 4 (by rfl) ⟨170415, by rfl⟩ : syracuseStep 1817765 = 340831) (by norm_num)
theorem B1293517 : Blo 806344 1293517 := bbase (se 3 (by rfl) ⟨242534, by rfl⟩ : syracuseStep 1293517 = 485069) (by norm_num)
theorem B1817837 : Blo 806344 1817837 := bbase (se 3 (by rfl) ⟨340844, by rfl⟩ : syracuseStep 1817837 = 681689) (by norm_num)
theorem B1817909 : Blo 806344 1817909 := bbase (se 5 (by rfl) ⟨85214, by rfl⟩ : syracuseStep 1817909 = 170429) (by norm_num)
theorem B5815637 : Blo 806344 5815637 := bbase (se 11 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 5815637 = 8519) (by norm_num)
theorem B1817981 : Blo 806344 1817981 := bbase (se 3 (by rfl) ⟨340871, by rfl⟩ : syracuseStep 1817981 = 681743) (by norm_num)
theorem B1818053 : Blo 806344 1818053 := bbase (se 4 (by rfl) ⟨170442, by rfl⟩ : syracuseStep 1818053 = 340885) (by norm_num)
theorem B2047477 : Blo 806344 2047477 := bbase (se 5 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 2047477 = 191951) (by norm_num)
theorem B1818125 : Blo 806344 1818125 := bbase (se 3 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 1818125 = 681797) (by norm_num)
theorem B3063365 : Blo 806344 3063365 := bbase (se 4 (by rfl) ⟨287190, by rfl⟩ : syracuseStep 3063365 = 574381) (by norm_num)
theorem B1818197 : Blo 806344 1818197 := bbase (se 8 (by rfl) ⟨10653, by rfl⟩ : syracuseStep 1818197 = 21307) (by norm_num)
theorem B2047589 : Blo 806344 2047589 := bbase (se 4 (by rfl) ⟨191961, by rfl⟩ : syracuseStep 2047589 = 383923) (by norm_num)
theorem B1818269 : Blo 806344 1818269 := bbase (se 3 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 1818269 = 681851) (by norm_num)
theorem B1818341 : Blo 806344 1818341 := bbase (se 4 (by rfl) ⟨170469, by rfl⟩ : syracuseStep 1818341 = 340939) (by norm_num)
theorem B1556221 : Blo 806344 1556221 := bbase (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) (by norm_num)
theorem B2047781 : Blo 806344 2047781 := bbase (se 4 (by rfl) ⟨191979, by rfl⟩ : syracuseStep 2047781 = 383959) (by norm_num)
theorem B1818413 : Blo 806344 1818413 := bbase (se 3 (by rfl) ⟨340952, by rfl⟩ : syracuseStep 1818413 = 681905) (by norm_num)
theorem B3063653 : Blo 806344 3063653 := bbase (se 4 (by rfl) ⟨287217, by rfl⟩ : syracuseStep 3063653 = 574435) (by norm_num)
theorem B1818485 : Blo 806344 1818485 := bbase (se 5 (by rfl) ⟨85241, by rfl⟩ : syracuseStep 1818485 = 170483) (by norm_num)
theorem B3882917 : Blo 806344 3882917 := bbase (se 4 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 3882917 = 728047) (by norm_num)
theorem B1818557 : Blo 806344 1818557 := bbase (se 3 (by rfl) ⟨340979, by rfl⟩ : syracuseStep 1818557 = 681959) (by norm_num)
theorem B1818629 : Blo 806344 1818629 := bbase (se 4 (by rfl) ⟨170496, by rfl⟩ : syracuseStep 1818629 = 340993) (by norm_num)
theorem B1458205 : Blo 806344 1458205 := bbase (se 3 (by rfl) ⟨273413, by rfl⟩ : syracuseStep 1458205 = 546827) (by norm_num)
theorem B1818701 : Blo 806344 1818701 := bbase (se 3 (by rfl) ⟨341006, by rfl⟩ : syracuseStep 1818701 = 682013) (by norm_num)
theorem B3686485 : Blo 806344 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B2048125 : Blo 806344 2048125 := bbase (se 3 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 2048125 = 768047) (by norm_num)
theorem B1818773 : Blo 806344 1818773 := bbase (se 6 (by rfl) ⟨42627, by rfl⟩ : syracuseStep 1818773 = 85255) (by norm_num)
theorem B1294517 : Blo 806344 1294517 := bbase (se 5 (by rfl) ⟨60680, by rfl⟩ : syracuseStep 1294517 = 121361) (by norm_num)
theorem B3457237 : Blo 806344 3457237 := bbase (se 7 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 3457237 = 81029) (by norm_num)
theorem B1818845 : Blo 806344 1818845 := bbase (se 3 (by rfl) ⟨341033, by rfl⟩ : syracuseStep 1818845 = 682067) (by norm_num)
theorem B2048237 : Blo 806344 2048237 := bbase (se 3 (by rfl) ⟨384044, by rfl⟩ : syracuseStep 2048237 = 768089) (by norm_num)
theorem B1818917 : Blo 806344 1818917 := bbase (se 4 (by rfl) ⟨170523, by rfl⟩ : syracuseStep 1818917 = 341047) (by norm_num)
theorem B1294645 : Blo 806344 1294645 := bbase (se 5 (by rfl) ⟨60686, by rfl⟩ : syracuseStep 1294645 = 121373) (by norm_num)
theorem B1818989 : Blo 806344 1818989 := bbase (se 3 (by rfl) ⟨341060, by rfl⟩ : syracuseStep 1818989 = 682121) (by norm_num)
theorem B2048429 : Blo 806344 2048429 := bbase (se 3 (by rfl) ⟨384080, by rfl⟩ : syracuseStep 2048429 = 768161) (by norm_num)
theorem B1819061 : Blo 806344 1819061 := bbase (se 5 (by rfl) ⟨85268, by rfl⟩ : syracuseStep 1819061 = 170537) (by norm_num)
theorem B1229261 : Blo 806344 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B1819133 : Blo 806344 1819133 := bbase (se 3 (by rfl) ⟨341087, by rfl⟩ : syracuseStep 1819133 = 682175) (by norm_num)
theorem B934417 : Blo 806344 934417 := bbase (se 2 (by rfl) ⟨350406, by rfl⟩ : syracuseStep 934417 = 700813) (by norm_num)
theorem B3883589 : Blo 806344 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B1819205 : Blo 806344 1819205 := bbase (se 4 (by rfl) ⟨170550, by rfl⟩ : syracuseStep 1819205 = 341101) (by norm_num)
theorem B3326581 : Blo 806344 3326581 := bbase (se 5 (by rfl) ⟨155933, by rfl⟩ : syracuseStep 3326581 = 311867) (by norm_num)
theorem B1819277 : Blo 806344 1819277 := bbase (se 3 (by rfl) ⟨341114, by rfl⟩ : syracuseStep 1819277 = 682229) (by norm_num)
theorem B1295029 : Blo 806344 1295029 := bbase (se 5 (by rfl) ⟨60704, by rfl⟩ : syracuseStep 1295029 = 121409) (by norm_num)
theorem B1819349 : Blo 806344 1819349 := bbase (se 7 (by rfl) ⟨21320, by rfl⟩ : syracuseStep 1819349 = 42641) (by norm_num)
theorem B2048773 : Blo 806344 2048773 := bbase (se 4 (by rfl) ⟨192072, by rfl⟩ : syracuseStep 2048773 = 384145) (by norm_num)
theorem B1819421 : Blo 806344 1819421 := bbase (se 3 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 1819421 = 682283) (by norm_num)
theorem B1819493 : Blo 806344 1819493 := bbase (se 4 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 1819493 = 341155) (by norm_num)
theorem B2048885 : Blo 806344 2048885 := bbase (se 5 (by rfl) ⟨96041, by rfl⟩ : syracuseStep 2048885 = 192083) (by norm_num)
theorem B1360813 : Blo 806344 1360813 := bbase (se 3 (by rfl) ⟨255152, by rfl⟩ : syracuseStep 1360813 = 510305) (by norm_num)
theorem B1819565 : Blo 806344 1819565 := bbase (se 3 (by rfl) ⟨341168, by rfl⟩ : syracuseStep 1819565 = 682337) (by norm_num)
theorem B1295285 : Blo 806344 1295285 := bbase (se 5 (by rfl) ⟨60716, by rfl⟩ : syracuseStep 1295285 = 121433) (by norm_num)
theorem B1819637 : Blo 806344 1819637 := bbase (se 5 (by rfl) ⟨85295, by rfl⟩ : syracuseStep 1819637 = 170591) (by norm_num)
theorem B1360901 : Blo 806344 1360901 := bbase (se 4 (by rfl) ⟨127584, by rfl⟩ : syracuseStep 1360901 = 255169) (by norm_num)
theorem B3064837 : Blo 806344 3064837 := bbase (se 4 (by rfl) ⟨287328, by rfl⟩ : syracuseStep 3064837 = 574657) (by norm_num)
theorem B2049077 : Blo 806344 2049077 := bbase (se 5 (by rfl) ⟨96050, by rfl⟩ : syracuseStep 2049077 = 192101) (by norm_num)
theorem B1819709 : Blo 806344 1819709 := bbase (se 3 (by rfl) ⟨341195, by rfl⟩ : syracuseStep 1819709 = 682391) (by norm_num)
theorem B1361029 : Blo 806344 1361029 := bbase (se 4 (by rfl) ⟨127596, by rfl⟩ : syracuseStep 1361029 = 255193) (by norm_num)
theorem B1819781 : Blo 806344 1819781 := bbase (se 4 (by rfl) ⟨170604, by rfl⟩ : syracuseStep 1819781 = 341209) (by norm_num)
theorem B1819853 : Blo 806344 1819853 := bbase (se 3 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 1819853 = 682445) (by norm_num)
theorem B1361117 : Blo 806344 1361117 := bbase (se 3 (by rfl) ⟨255209, by rfl⟩ : syracuseStep 1361117 = 510419) (by norm_num)
theorem B1819925 : Blo 806344 1819925 := bbase (se 6 (by rfl) ⟨42654, by rfl⟩ : syracuseStep 1819925 = 85309) (by norm_num)
theorem B3065141 : Blo 806344 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B2770229 : Blo 806344 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B1361245 : Blo 806344 1361245 := bbase (se 3 (by rfl) ⟨255233, by rfl⟩ : syracuseStep 1361245 = 510467) (by norm_num)
theorem B1819997 : Blo 806344 1819997 := bbase (se 3 (by rfl) ⟨341249, by rfl⟩ : syracuseStep 1819997 = 682499) (by norm_num)
theorem B2049421 : Blo 806344 2049421 := bbase (se 3 (by rfl) ⟨384266, by rfl⟩ : syracuseStep 2049421 = 768533) (by norm_num)
theorem B1459613 : Blo 806344 1459613 := bbase (se 3 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 1459613 = 547355) (by norm_num)
theorem B1820069 : Blo 806344 1820069 := bbase (se 4 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 1820069 = 341263) (by norm_num)
theorem B1361333 : Blo 806344 1361333 := bbase (se 5 (by rfl) ⟨63812, by rfl⟩ : syracuseStep 1361333 = 127625) (by norm_num)
theorem B1459669 : Blo 806344 1459669 := bbase (se 7 (by rfl) ⟨17105, by rfl⟩ : syracuseStep 1459669 = 34211) (by norm_num)
theorem B1820141 : Blo 806344 1820141 := bbase (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) (by norm_num)
theorem B2049533 : Blo 806344 2049533 := bbase (se 3 (by rfl) ⟨384287, by rfl⟩ : syracuseStep 2049533 = 768575) (by norm_num)
theorem B1361461 : Blo 806344 1361461 := bbase (se 5 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 1361461 = 127637) (by norm_num)
theorem B1820213 : Blo 806344 1820213 := bbase (se 5 (by rfl) ⟨85322, by rfl⟩ : syracuseStep 1820213 = 170645) (by norm_num)
theorem B30721621 : Blo 806344 30721621 := bbase (se 8 (by rfl) ⟨180009, by rfl⟩ : syracuseStep 30721621 = 360019) (by norm_num)
theorem B1820285 : Blo 806344 1820285 := bbase (se 3 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 1820285 = 682607) (by norm_num)
theorem B1361549 : Blo 806344 1361549 := bbase (se 3 (by rfl) ⟨255290, by rfl⟩ : syracuseStep 1361549 = 510581) (by norm_num)
theorem B2049725 : Blo 806344 2049725 := bbase (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) (by norm_num)
theorem B1820357 : Blo 806344 1820357 := bbase (se 4 (by rfl) ⟨170658, by rfl⟩ : syracuseStep 1820357 = 341317) (by norm_num)
theorem B1361677 : Blo 806344 1361677 := bbase (se 3 (by rfl) ⟨255314, by rfl⟩ : syracuseStep 1361677 = 510629) (by norm_num)
theorem B1820429 : Blo 806344 1820429 := bbase (se 3 (by rfl) ⟨341330, by rfl⟩ : syracuseStep 1820429 = 682661) (by norm_num)
theorem B1296157 : Blo 806344 1296157 := bbase (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) (by norm_num)
theorem B1820501 : Blo 806344 1820501 := bbase (se 9 (by rfl) ⟨5333, by rfl⟩ : syracuseStep 1820501 = 10667) (by norm_num)
theorem B1361765 : Blo 806344 1361765 := bbase (se 4 (by rfl) ⟨127665, by rfl⟩ : syracuseStep 1361765 = 255331) (by norm_num)
theorem B1296253 : Blo 806344 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B1820573 : Blo 806344 1820573 := bbase (se 3 (by rfl) ⟨341357, by rfl⟩ : syracuseStep 1820573 = 682715) (by norm_num)
theorem B1361893 : Blo 806344 1361893 := bbase (se 4 (by rfl) ⟨127677, by rfl⟩ : syracuseStep 1361893 = 255355) (by norm_num)
theorem B1820645 : Blo 806344 1820645 := bbase (se 4 (by rfl) ⟨170685, by rfl⟩ : syracuseStep 1820645 = 341371) (by norm_num)
theorem B2050069 : Blo 806344 2050069 := bbase (se 6 (by rfl) ⟨48048, by rfl⟩ : syracuseStep 2050069 = 96097) (by norm_num)
theorem B1296413 : Blo 806344 1296413 := bbase (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) (by norm_num)
theorem B1820717 : Blo 806344 1820717 := bbase (se 3 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 1820717 = 682769) (by norm_num)
theorem B1361981 : Blo 806344 1361981 := bbase (se 3 (by rfl) ⟨255371, by rfl⟩ : syracuseStep 1361981 = 510743) (by norm_num)
theorem B1722485 : Blo 806344 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B1820789 : Blo 806344 1820789 := bbase (se 5 (by rfl) ⟨85349, by rfl⟩ : syracuseStep 1820789 = 170699) (by norm_num)
theorem B4376693 : Blo 806344 4376693 := bbase (se 5 (by rfl) ⟨205157, by rfl⟩ : syracuseStep 4376693 = 410315) (by norm_num)
theorem B2050181 : Blo 806344 2050181 := bbase (se 4 (by rfl) ⟨192204, by rfl⟩ : syracuseStep 2050181 = 384409) (by norm_num)
theorem B1231013 : Blo 806344 1231013 := bbase (se 4 (by rfl) ⟨115407, by rfl⟩ : syracuseStep 1231013 = 230815) (by norm_num)
theorem B1362109 : Blo 806344 1362109 := bbase (se 3 (by rfl) ⟨255395, by rfl⟩ : syracuseStep 1362109 = 510791) (by norm_num)
theorem B1820861 : Blo 806344 1820861 := bbase (se 3 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 1820861 = 682823) (by norm_num)
theorem B968965 : Blo 806344 968965 := bbase (se 4 (by rfl) ⟨90840, by rfl⟩ : syracuseStep 968965 = 181681) (by norm_num)
theorem B1820933 : Blo 806344 1820933 := bbase (se 4 (by rfl) ⟨170712, by rfl⟩ : syracuseStep 1820933 = 341425) (by norm_num)
theorem B1362197 : Blo 806344 1362197 := bbase (se 6 (by rfl) ⟨31926, by rfl⟩ : syracuseStep 1362197 = 63853) (by norm_num)
theorem B2050373 : Blo 806344 2050373 := bbase (se 4 (by rfl) ⟨192222, by rfl⟩ : syracuseStep 2050373 = 384445) (by norm_num)
theorem B1821005 : Blo 806344 1821005 := bbase (se 3 (by rfl) ⟨341438, by rfl⟩ : syracuseStep 1821005 = 682877) (by norm_num)
theorem B1362325 : Blo 806344 1362325 := bbase (se 6 (by rfl) ⟨31929, by rfl⟩ : syracuseStep 1362325 = 63859) (by norm_num)
theorem B1821077 : Blo 806344 1821077 := bbase (se 6 (by rfl) ⟨42681, by rfl⟩ : syracuseStep 1821077 = 85363) (by norm_num)
theorem B1821149 : Blo 806344 1821149 := bbase (se 3 (by rfl) ⟨341465, by rfl⟩ : syracuseStep 1821149 = 682931) (by norm_num)
theorem B1362413 : Blo 806344 1362413 := bbase (se 3 (by rfl) ⟨255452, by rfl⟩ : syracuseStep 1362413 = 510905) (by norm_num)
theorem B1821221 : Blo 806344 1821221 := bbase (se 4 (by rfl) ⟨170739, by rfl⟩ : syracuseStep 1821221 = 341479) (by norm_num)
theorem B1362541 : Blo 806344 1362541 := bbase (se 3 (by rfl) ⟨255476, by rfl⟩ : syracuseStep 1362541 = 510953) (by norm_num)
theorem B1821293 : Blo 806344 1821293 := bbase (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) (by norm_num)
theorem B2050717 : Blo 806344 2050717 := bbase (se 3 (by rfl) ⟨384509, by rfl⟩ : syracuseStep 2050717 = 769019) (by norm_num)
theorem B1821365 : Blo 806344 1821365 := bbase (se 5 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 1821365 = 170753) (by norm_num)
theorem B1362629 : Blo 806344 1362629 := bbase (se 4 (by rfl) ⟨127746, by rfl⟩ : syracuseStep 1362629 = 255493) (by norm_num)
theorem B1821437 : Blo 806344 1821437 := bbase (se 3 (by rfl) ⟨341519, by rfl⟩ : syracuseStep 1821437 = 683039) (by norm_num)
theorem B2050829 : Blo 806344 2050829 := bbase (se 3 (by rfl) ⟨384530, by rfl⟩ : syracuseStep 2050829 = 769061) (by norm_num)
theorem B1362757 : Blo 806344 1362757 := bbase (se 4 (by rfl) ⟨127758, by rfl⟩ : syracuseStep 1362757 = 255517) (by norm_num)
theorem B1821509 : Blo 806344 1821509 := bbase (se 4 (by rfl) ⟨170766, by rfl⟩ : syracuseStep 1821509 = 341533) (by norm_num)
theorem B1821581 : Blo 806344 1821581 := bbase (se 3 (by rfl) ⟨341546, by rfl⟩ : syracuseStep 1821581 = 683093) (by norm_num)
theorem B1362845 : Blo 806344 1362845 := bbase (se 3 (by rfl) ⟨255533, by rfl⟩ : syracuseStep 1362845 = 511067) (by norm_num)
theorem B3492773 : Blo 806344 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B1264589 : Blo 806344 1264589 := bbase (se 3 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 1264589 = 474221) (by norm_num)
theorem B2051021 : Blo 806344 2051021 := bbase (se 3 (by rfl) ⟨384566, by rfl⟩ : syracuseStep 2051021 = 769133) (by norm_num)
theorem B1723349 : Blo 806344 1723349 := bbase (se 7 (by rfl) ⟨20195, by rfl⟩ : syracuseStep 1723349 = 40391) (by norm_num)
theorem B1821653 : Blo 806344 1821653 := bbase (se 7 (by rfl) ⟨21347, by rfl⟩ : syracuseStep 1821653 = 42695) (by norm_num)
theorem B1362973 : Blo 806344 1362973 := bbase (se 3 (by rfl) ⟨255557, by rfl⟩ : syracuseStep 1362973 = 511115) (by norm_num)
theorem B1821725 : Blo 806344 1821725 := bbase (se 3 (by rfl) ⟨341573, by rfl⟩ : syracuseStep 1821725 = 683147) (by norm_num)
theorem B1723493 : Blo 806344 1723493 := bbase (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) (by norm_num)
theorem B1821797 : Blo 806344 1821797 := bbase (se 4 (by rfl) ⟨170793, by rfl⟩ : syracuseStep 1821797 = 341587) (by norm_num)
theorem B1363061 : Blo 806344 1363061 := bbase (se 5 (by rfl) ⟨63893, by rfl⟩ : syracuseStep 1363061 = 127787) (by norm_num)
theorem B1297541 : Blo 806344 1297541 := bbase (se 4 (by rfl) ⟨121644, by rfl⟩ : syracuseStep 1297541 = 243289) (by norm_num)
theorem B3460229 : Blo 806344 3460229 := bbase (se 4 (by rfl) ⟨324396, by rfl⟩ : syracuseStep 3460229 = 648793) (by norm_num)
theorem B1821869 : Blo 806344 1821869 := bbase (se 3 (by rfl) ⟨341600, by rfl⟩ : syracuseStep 1821869 = 683201) (by norm_num)
theorem B4082885 : Blo 806344 4082885 := bbase (se 4 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 4082885 = 765541) (by norm_num)
theorem B4607189 : Blo 806344 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B1363189 : Blo 806344 1363189 := bbase (se 5 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 1363189 = 127799) (by norm_num)
theorem B1821941 : Blo 806344 1821941 := bbase (se 5 (by rfl) ⟨85403, by rfl⟩ : syracuseStep 1821941 = 170807) (by norm_num)
theorem B2182421 : Blo 806344 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B1822013 : Blo 806344 1822013 := bbase (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) (by norm_num)
theorem B970061 : Blo 806344 970061 := bbase (se 3 (by rfl) ⟨181886, by rfl⟩ : syracuseStep 970061 = 363773) (by norm_num)
theorem B1363277 : Blo 806344 1363277 := bbase (se 3 (by rfl) ⟨255614, by rfl⟩ : syracuseStep 1363277 = 511229) (by norm_num)
theorem B6147413 : Blo 806344 6147413 := bbase (se 11 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 6147413 = 9005) (by norm_num)
theorem B3067253 : Blo 806344 3067253 := bbase (se 5 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 3067253 = 287555) (by norm_num)
theorem B1822085 : Blo 806344 1822085 := bbase (se 4 (by rfl) ⟨170820, by rfl⟩ : syracuseStep 1822085 = 341641) (by norm_num)
theorem B1363405 : Blo 806344 1363405 := bbase (se 3 (by rfl) ⟨255638, by rfl⟩ : syracuseStep 1363405 = 511277) (by norm_num)
theorem B1822157 : Blo 806344 1822157 := bbase (se 3 (by rfl) ⟨341654, by rfl⟩ : syracuseStep 1822157 = 683309) (by norm_num)
theorem B1822229 : Blo 806344 1822229 := bbase (se 6 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 1822229 = 85417) (by norm_num)
theorem B1363493 : Blo 806344 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B1822301 : Blo 806344 1822301 := bbase (se 3 (by rfl) ⟨341681, by rfl⟩ : syracuseStep 1822301 = 683363) (by norm_num)
theorem B1166981 : Blo 806344 1166981 := bbase (se 4 (by rfl) ⟨109404, by rfl⟩ : syracuseStep 1166981 = 218809) (by norm_num)
theorem B3067541 : Blo 806344 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B1363621 : Blo 806344 1363621 := bbase (se 4 (by rfl) ⟨127839, by rfl⟩ : syracuseStep 1363621 = 255679) (by norm_num)
theorem B1822373 : Blo 806344 1822373 := bbase (se 4 (by rfl) ⟨170847, by rfl⟩ : syracuseStep 1822373 = 341695) (by norm_num)
theorem B7786165 : Blo 806344 7786165 := bbase (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) (by norm_num)
theorem B2182853 : Blo 806344 2182853 := bbase (se 4 (by rfl) ⟨204642, by rfl⟩ : syracuseStep 2182853 = 409285) (by norm_num)
theorem B1822445 : Blo 806344 1822445 := bbase (se 3 (by rfl) ⟨341708, by rfl⟩ : syracuseStep 1822445 = 683417) (by norm_num)
theorem B1363709 : Blo 806344 1363709 := bbase (se 3 (by rfl) ⟨255695, by rfl⟩ : syracuseStep 1363709 = 511391) (by norm_num)
theorem B1822517 : Blo 806344 1822517 := bbase (se 5 (by rfl) ⟨85430, by rfl⟩ : syracuseStep 1822517 = 170861) (by norm_num)
theorem B1724237 : Blo 806344 1724237 := bbase (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) (by norm_num)
theorem B1363837 : Blo 806344 1363837 := bbase (se 3 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 1363837 = 511439) (by norm_num)
theorem B1822589 : Blo 806344 1822589 := bbase (se 3 (by rfl) ⟨341735, by rfl⟩ : syracuseStep 1822589 = 683471) (by norm_num)
theorem B1822661 : Blo 806344 1822661 := bbase (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) (by norm_num)
theorem B1363925 : Blo 806344 1363925 := bbase (se 7 (by rfl) ⟨15983, by rfl⟩ : syracuseStep 1363925 = 31967) (by norm_num)
theorem B970753 : Blo 806344 970753 := bbase (se 2 (by rfl) ⟨364032, by rfl⟩ : syracuseStep 970753 = 728065) (by norm_num)
theorem B1822733 : Blo 806344 1822733 := bbase (se 3 (by rfl) ⟨341762, by rfl⟩ : syracuseStep 1822733 = 683525) (by norm_num)
theorem B9195605 : Blo 806344 9195605 := bbase (se 8 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 9195605 = 107761) (by norm_num)
theorem B1364053 : Blo 806344 1364053 := bbase (se 8 (by rfl) ⟨7992, by rfl⟩ : syracuseStep 1364053 = 15985) (by norm_num)
theorem B1822805 : Blo 806344 1822805 := bbase (se 8 (by rfl) ⟨10680, by rfl⟩ : syracuseStep 1822805 = 21361) (by norm_num)
theorem B970849 : Blo 806344 970849 := bbase (se 2 (by rfl) ⟨364068, by rfl⟩ : syracuseStep 970849 = 728137) (by norm_num)
theorem B3461237 : Blo 806344 3461237 := bbase (se 5 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 3461237 = 324491) (by norm_num)
theorem B1822877 : Blo 806344 1822877 := bbase (se 3 (by rfl) ⟨341789, by rfl⟩ : syracuseStep 1822877 = 683579) (by norm_num)
theorem B1364141 : Blo 806344 1364141 := bbase (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) (by norm_num)
theorem B1822949 : Blo 806344 1822949 := bbase (se 4 (by rfl) ⟨170901, by rfl⟩ : syracuseStep 1822949 = 341803) (by norm_num)
theorem B1364269 : Blo 806344 1364269 := bbase (se 3 (by rfl) ⟨255800, by rfl⟩ : syracuseStep 1364269 = 511601) (by norm_num)
theorem B1823021 : Blo 806344 1823021 := bbase (se 3 (by rfl) ⟨341816, by rfl⟩ : syracuseStep 1823021 = 683633) (by norm_num)
theorem B4608373 : Blo 806344 4608373 := bbase (se 5 (by rfl) ⟨216017, by rfl⟩ : syracuseStep 4608373 = 432035) (by norm_num)
theorem B1823093 : Blo 806344 1823093 := bbase (se 5 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 1823093 = 170915) (by norm_num)
theorem B1364357 : Blo 806344 1364357 := bbase (se 4 (by rfl) ⟨127908, by rfl⟩ : syracuseStep 1364357 = 255817) (by norm_num)
theorem B1823165 : Blo 806344 1823165 := bbase (se 3 (by rfl) ⟨341843, by rfl⟩ : syracuseStep 1823165 = 683687) (by norm_num)
theorem B4084181 : Blo 806344 4084181 := bbase (se 7 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 4084181 = 95723) (by norm_num)
theorem B971233 : Blo 806344 971233 := bbase (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) (by norm_num)
theorem B1364485 : Blo 806344 1364485 := bbase (se 4 (by rfl) ⟨127920, by rfl⟩ : syracuseStep 1364485 = 255841) (by norm_num)
theorem B1823237 : Blo 806344 1823237 := bbase (se 4 (by rfl) ⟨170928, by rfl⟩ : syracuseStep 1823237 = 341857) (by norm_num)
theorem B1724989 : Blo 806344 1724989 := bbase (se 3 (by rfl) ⟨323435, by rfl⟩ : syracuseStep 1724989 = 646871) (by norm_num)
theorem B1364573 : Blo 806344 1364573 := bbase (se 3 (by rfl) ⟨255857, by rfl⟩ : syracuseStep 1364573 = 511715) (by norm_num)
theorem B1725133 : Blo 806344 1725133 := bbase (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) (by norm_num)
theorem B1364701 : Blo 806344 1364701 := bbase (se 3 (by rfl) ⟨255881, by rfl⟩ : syracuseStep 1364701 = 511763) (by norm_num)
theorem B3068725 : Blo 806344 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B1364789 : Blo 806344 1364789 := bbase (se 5 (by rfl) ⟨63974, by rfl⟩ : syracuseStep 1364789 = 127949) (by norm_num)
theorem B1364917 : Blo 806344 1364917 := bbase (se 5 (by rfl) ⟨63980, by rfl⟩ : syracuseStep 1364917 = 127961) (by norm_num)
theorem B1365005 : Blo 806344 1365005 := bbase (se 3 (by rfl) ⟨255938, by rfl⟩ : syracuseStep 1365005 = 511877) (by norm_num)
theorem B1725509 : Blo 806344 1725509 := bbase (se 4 (by rfl) ⟨161766, by rfl⟩ : syracuseStep 1725509 = 323533) (by norm_num)
theorem B3069029 : Blo 806344 3069029 := bbase (se 4 (by rfl) ⟨287721, by rfl⟩ : syracuseStep 3069029 = 575443) (by norm_num)
theorem B1365133 : Blo 806344 1365133 := bbase (se 3 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 1365133 = 511925) (by norm_num)
theorem B1365221 : Blo 806344 1365221 := bbase (se 4 (by rfl) ⟨127989, by rfl⟩ : syracuseStep 1365221 = 255979) (by norm_num)
theorem B1365349 : Blo 806344 1365349 := bbase (se 4 (by rfl) ⟨128001, by rfl⟩ : syracuseStep 1365349 = 256003) (by norm_num)
theorem B1725877 : Blo 806344 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B1365437 : Blo 806344 1365437 := bbase (se 3 (by rfl) ⟨256019, by rfl⟩ : syracuseStep 1365437 = 512039) (by norm_num)
theorem B972281 : Blo 806344 972281 := bbase (se 2 (by rfl) ⟨364605, by rfl⟩ : syracuseStep 972281 = 729211) (by norm_num)
theorem B1365565 : Blo 806344 1365565 := bbase (se 3 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 1365565 = 512087) (by norm_num)
theorem B1365653 : Blo 806344 1365653 := bbase (se 6 (by rfl) ⟨32007, by rfl⟩ : syracuseStep 1365653 = 64015) (by norm_num)
theorem B4085477 : Blo 806344 4085477 := bbase (se 4 (by rfl) ⟨383013, by rfl⟩ : syracuseStep 4085477 = 766027) (by norm_num)
theorem B1365781 : Blo 806344 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B972589 : Blo 806344 972589 := bbase (se 3 (by rfl) ⟨182360, by rfl⟩ : syracuseStep 972589 = 364721) (by norm_num)
theorem B972617 : Blo 806344 972617 := bbase (se 2 (by rfl) ⟨364731, by rfl⟩ : syracuseStep 972617 = 729463) (by norm_num)
theorem B1365869 : Blo 806344 1365869 := bbase (se 3 (by rfl) ⟨256100, by rfl⟩ : syracuseStep 1365869 = 512201) (by norm_num)
theorem B907141 : Blo 806344 907141 := bbase (se 4 (by rfl) ⟨85044, by rfl⟩ : syracuseStep 907141 = 170089) (by norm_num)
theorem B907177 : Blo 806344 907177 := bbase (se 2 (by rfl) ⟨340191, by rfl⟩ : syracuseStep 907177 = 680383) (by norm_num)
theorem B907213 : Blo 806344 907213 := bbase (se 3 (by rfl) ⟨170102, by rfl⟩ : syracuseStep 907213 = 340205) (by norm_num)
theorem B1365997 : Blo 806344 1365997 := bbase (se 3 (by rfl) ⟨256124, by rfl⟩ : syracuseStep 1365997 = 512249) (by norm_num)
theorem B907249 : Blo 806344 907249 := bbase (se 2 (by rfl) ⟨340218, by rfl⟩ : syracuseStep 907249 = 680437) (by norm_num)
theorem B907285 : Blo 806344 907285 := bbase (se 6 (by rfl) ⟨21264, by rfl⟩ : syracuseStep 907285 = 42529) (by norm_num)
theorem B907321 : Blo 806344 907321 := bbase (se 2 (by rfl) ⟨340245, by rfl⟩ : syracuseStep 907321 = 680491) (by norm_num)
theorem B1366085 : Blo 806344 1366085 := bbase (se 4 (by rfl) ⟨128070, by rfl⟩ : syracuseStep 1366085 = 256141) (by norm_num)
theorem B1038425 : Blo 806344 1038425 := bbase (se 2 (by rfl) ⟨389409, by rfl⟩ : syracuseStep 1038425 = 778819) (by norm_num)
theorem B907357 : Blo 806344 907357 := bbase (se 3 (by rfl) ⟨170129, by rfl⟩ : syracuseStep 907357 = 340259) (by norm_num)
theorem B907393 : Blo 806344 907393 := bbase (se 2 (by rfl) ⟨340272, by rfl⟩ : syracuseStep 907393 = 680545) (by norm_num)
theorem B907429 : Blo 806344 907429 := bbase (se 4 (by rfl) ⟨85071, by rfl⟩ : syracuseStep 907429 = 170143) (by norm_num)
theorem B1038529 : Blo 806344 1038529 := bbase (se 2 (by rfl) ⟨389448, by rfl⟩ : syracuseStep 1038529 = 778897) (by norm_num)
theorem B1366213 : Blo 806344 1366213 := bbase (se 4 (by rfl) ⟨128082, by rfl⟩ : syracuseStep 1366213 = 256165) (by norm_num)
theorem B907465 : Blo 806344 907465 := bbase (se 2 (by rfl) ⟨340299, by rfl⟩ : syracuseStep 907465 = 680599) (by norm_num)
theorem B907501 : Blo 806344 907501 := bbase (se 3 (by rfl) ⟨170156, by rfl⟩ : syracuseStep 907501 = 340313) (by norm_num)
theorem B907537 : Blo 806344 907537 := bbase (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) (by norm_num)
theorem B1366301 : Blo 806344 1366301 := bbase (se 3 (by rfl) ⟨256181, by rfl⟩ : syracuseStep 1366301 = 512363) (by norm_num)
theorem B907573 : Blo 806344 907573 := bbase (se 5 (by rfl) ⟨42542, by rfl⟩ : syracuseStep 907573 = 85085) (by norm_num)
theorem B4610357 : Blo 806344 4610357 := bbase (se 5 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 4610357 = 432221) (by norm_num)
theorem B973117 : Blo 806344 973117 := bbase (se 3 (by rfl) ⟨182459, by rfl⟩ : syracuseStep 973117 = 364919) (by norm_num)
theorem B10377557 : Blo 806344 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B907609 : Blo 806344 907609 := bbase (se 2 (by rfl) ⟨340353, by rfl⟩ : syracuseStep 907609 = 680707) (by norm_num)
theorem B907645 : Blo 806344 907645 := bbase (se 3 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 907645 = 340367) (by norm_num)
theorem B7756181 : Blo 806344 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B1366429 : Blo 806344 1366429 := bbase (se 3 (by rfl) ⟨256205, by rfl⟩ : syracuseStep 1366429 = 512411) (by norm_num)
theorem B907681 : Blo 806344 907681 := bbase (se 2 (by rfl) ⟨340380, by rfl⟩ : syracuseStep 907681 = 680761) (by norm_num)
theorem B907717 : Blo 806344 907717 := bbase (se 4 (by rfl) ⟨85098, by rfl⟩ : syracuseStep 907717 = 170197) (by norm_num)
theorem B907753 : Blo 806344 907753 := bbase (se 2 (by rfl) ⟨340407, by rfl⟩ : syracuseStep 907753 = 680815) (by norm_num)
theorem B1366517 : Blo 806344 1366517 := bbase (se 5 (by rfl) ⟨64055, by rfl⟩ : syracuseStep 1366517 = 128111) (by norm_num)
theorem B907789 : Blo 806344 907789 := bbase (se 3 (by rfl) ⟨170210, by rfl⟩ : syracuseStep 907789 = 340421) (by norm_num)
theorem B907825 : Blo 806344 907825 := bbase (se 2 (by rfl) ⟨340434, by rfl⟩ : syracuseStep 907825 = 680869) (by norm_num)
theorem B907861 : Blo 806344 907861 := bbase (se 8 (by rfl) ⟨5319, by rfl⟩ : syracuseStep 907861 = 10639) (by norm_num)
theorem B1366645 : Blo 806344 1366645 := bbase (se 5 (by rfl) ⟨64061, by rfl⟩ : syracuseStep 1366645 = 128123) (by norm_num)
theorem B907897 : Blo 806344 907897 := bbase (se 2 (by rfl) ⟨340461, by rfl⟩ : syracuseStep 907897 = 680923) (by norm_num)
theorem B907933 : Blo 806344 907933 := bbase (se 3 (by rfl) ⟨170237, by rfl⟩ : syracuseStep 907933 = 340475) (by norm_num)
theorem B907969 : Blo 806344 907969 := bbase (se 2 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 907969 = 680977) (by norm_num)
theorem B1366733 : Blo 806344 1366733 := bbase (se 3 (by rfl) ⟨256262, by rfl⟩ : syracuseStep 1366733 = 512525) (by norm_num)
theorem B908005 : Blo 806344 908005 := bbase (se 4 (by rfl) ⟨85125, by rfl⟩ : syracuseStep 908005 = 170251) (by norm_num)
theorem B908041 : Blo 806344 908041 := bbase (se 2 (by rfl) ⟨340515, by rfl⟩ : syracuseStep 908041 = 681031) (by norm_num)
theorem B908077 : Blo 806344 908077 := bbase (se 3 (by rfl) ⟨170264, by rfl⟩ : syracuseStep 908077 = 340529) (by norm_num)
theorem B1366861 : Blo 806344 1366861 := bbase (se 3 (by rfl) ⟨256286, by rfl⟩ : syracuseStep 1366861 = 512573) (by norm_num)
theorem B908113 : Blo 806344 908113 := bbase (se 2 (by rfl) ⟨340542, by rfl⟩ : syracuseStep 908113 = 681085) (by norm_num)
theorem B908149 : Blo 806344 908149 := bbase (se 5 (by rfl) ⟨42569, by rfl⟩ : syracuseStep 908149 = 85139) (by norm_num)
theorem B1727381 : Blo 806344 1727381 := bbase (se 6 (by rfl) ⟨40485, by rfl⟩ : syracuseStep 1727381 = 80971) (by norm_num)
theorem B908185 : Blo 806344 908185 := bbase (se 2 (by rfl) ⟨340569, by rfl⟩ : syracuseStep 908185 = 681139) (by norm_num)
theorem B1366949 : Blo 806344 1366949 := bbase (se 4 (by rfl) ⟨128151, by rfl⟩ : syracuseStep 1366949 = 256303) (by norm_num)
theorem B908221 : Blo 806344 908221 := bbase (se 3 (by rfl) ⟨170291, by rfl⟩ : syracuseStep 908221 = 340583) (by norm_num)
theorem B908257 : Blo 806344 908257 := bbase (se 2 (by rfl) ⟨340596, by rfl⟩ : syracuseStep 908257 = 681193) (by norm_num)
theorem B4086773 : Blo 806344 4086773 := bbase (se 5 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 4086773 = 383135) (by norm_num)
theorem B908293 : Blo 806344 908293 := bbase (se 4 (by rfl) ⟨85152, by rfl⟩ : syracuseStep 908293 = 170305) (by norm_num)
theorem B1530893 : Blo 806344 1530893 := bbase (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) (by norm_num)
theorem B1727525 : Blo 806344 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B1367077 : Blo 806344 1367077 := bbase (se 4 (by rfl) ⟨128163, by rfl⟩ : syracuseStep 1367077 = 256327) (by norm_num)
theorem B908329 : Blo 806344 908329 := bbase (se 2 (by rfl) ⟨340623, by rfl⟩ : syracuseStep 908329 = 681247) (by norm_num)
theorem B908365 : Blo 806344 908365 := bbase (se 3 (by rfl) ⟨170318, by rfl⟩ : syracuseStep 908365 = 340637) (by norm_num)
theorem B908401 : Blo 806344 908401 := bbase (se 2 (by rfl) ⟨340650, by rfl⟩ : syracuseStep 908401 = 681301) (by norm_num)
theorem B1367165 : Blo 806344 1367165 := bbase (se 3 (by rfl) ⟨256343, by rfl⟩ : syracuseStep 1367165 = 512687) (by norm_num)
theorem B908437 : Blo 806344 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B1531037 : Blo 806344 1531037 := bbase (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) (by norm_num)
theorem B3071141 : Blo 806344 3071141 := bbase (se 4 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 3071141 = 575839) (by norm_num)
theorem B908473 : Blo 806344 908473 := bbase (se 2 (by rfl) ⟨340677, by rfl⟩ : syracuseStep 908473 = 681355) (by norm_num)
theorem B908509 : Blo 806344 908509 := bbase (se 3 (by rfl) ⟨170345, by rfl⟩ : syracuseStep 908509 = 340691) (by norm_num)
theorem B1039585 : Blo 806344 1039585 := bbase (se 2 (by rfl) ⟨389844, by rfl⟩ : syracuseStep 1039585 = 779689) (by norm_num)
theorem B7888117 : Blo 806344 7888117 := bbase (se 5 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 7888117 = 739511) (by norm_num)
theorem B1367293 : Blo 806344 1367293 := bbase (se 3 (by rfl) ⟨256367, by rfl⟩ : syracuseStep 1367293 = 512735) (by norm_num)
theorem B908545 : Blo 806344 908545 := bbase (se 2 (by rfl) ⟨340704, by rfl⟩ : syracuseStep 908545 = 681409) (by norm_num)
theorem B908581 : Blo 806344 908581 := bbase (se 4 (by rfl) ⟨85179, by rfl⟩ : syracuseStep 908581 = 170359) (by norm_num)
theorem B908617 : Blo 806344 908617 := bbase (se 2 (by rfl) ⟨340731, by rfl⟩ : syracuseStep 908617 = 681463) (by norm_num)
theorem B1367381 : Blo 806344 1367381 := bbase (se 11 (by rfl) ⟨1001, by rfl⟩ : syracuseStep 1367381 = 2003) (by norm_num)
theorem B908653 : Blo 806344 908653 := bbase (se 3 (by rfl) ⟨170372, by rfl⟩ : syracuseStep 908653 = 340745) (by norm_num)
theorem B1727885 : Blo 806344 1727885 := bbase (se 3 (by rfl) ⟨323978, by rfl⟩ : syracuseStep 1727885 = 647957) (by norm_num)
theorem B908689 : Blo 806344 908689 := bbase (se 2 (by rfl) ⟨340758, by rfl⟩ : syracuseStep 908689 = 681517) (by norm_num)
theorem B10345877 : Blo 806344 10345877 := bbase (se 6 (by rfl) ⟨242481, by rfl⟩ : syracuseStep 10345877 = 484963) (by norm_num)
theorem B908725 : Blo 806344 908725 := bbase (se 5 (by rfl) ⟨42596, by rfl⟩ : syracuseStep 908725 = 85193) (by norm_num)
theorem B1531325 : Blo 806344 1531325 := bbase (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) (by norm_num)
theorem B3071429 : Blo 806344 3071429 := bbase (se 4 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 3071429 = 575893) (by norm_num)
theorem B908761 : Blo 806344 908761 := bbase (se 2 (by rfl) ⟨340785, by rfl⟩ : syracuseStep 908761 = 681571) (by norm_num)
theorem B908797 : Blo 806344 908797 := bbase (se 3 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 908797 = 340799) (by norm_num)
theorem B908833 : Blo 806344 908833 := bbase (se 2 (by rfl) ⟨340812, by rfl⟩ : syracuseStep 908833 = 681625) (by norm_num)
theorem B908869 : Blo 806344 908869 := bbase (se 4 (by rfl) ⟨85206, by rfl⟩ : syracuseStep 908869 = 170413) (by norm_num)
theorem B1531477 : Blo 806344 1531477 := bbase (se 8 (by rfl) ⟨8973, by rfl⟩ : syracuseStep 1531477 = 17947) (by norm_num)
theorem B908905 : Blo 806344 908905 := bbase (se 2 (by rfl) ⟨340839, by rfl⟩ : syracuseStep 908905 = 681679) (by norm_num)
theorem B908941 : Blo 806344 908941 := bbase (se 3 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 908941 = 340853) (by norm_num)
theorem B908977 : Blo 806344 908977 := bbase (se 2 (by rfl) ⟨340866, by rfl⟩ : syracuseStep 908977 = 681733) (by norm_num)
theorem B1892045 : Blo 806344 1892045 := bbase (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) (by norm_num)
theorem B909013 : Blo 806344 909013 := bbase (se 7 (by rfl) ⟨10652, by rfl⟩ : syracuseStep 909013 = 21305) (by norm_num)
theorem B909049 : Blo 806344 909049 := bbase (se 2 (by rfl) ⟨340893, by rfl⟩ : syracuseStep 909049 = 681787) (by norm_num)
theorem B909085 : Blo 806344 909085 := bbase (se 3 (by rfl) ⟨170453, by rfl⟩ : syracuseStep 909085 = 340907) (by norm_num)
theorem B909121 : Blo 806344 909121 := bbase (se 2 (by rfl) ⟨340920, by rfl⟩ : syracuseStep 909121 = 681841) (by norm_num)
theorem B4972373 : Blo 806344 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B909157 : Blo 806344 909157 := bbase (se 4 (by rfl) ⟨85233, by rfl⟩ : syracuseStep 909157 = 170467) (by norm_num)
theorem B1531781 : Blo 806344 1531781 := bbase (se 4 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 1531781 = 287209) (by norm_num)
theorem B909193 : Blo 806344 909193 := bbase (se 2 (by rfl) ⟨340947, by rfl⟩ : syracuseStep 909193 = 681895) (by norm_num)
theorem B909229 : Blo 806344 909229 := bbase (se 3 (by rfl) ⟨170480, by rfl⟩ : syracuseStep 909229 = 340961) (by norm_num)
theorem B3694517 : Blo 806344 3694517 := bbase (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) (by norm_num)
theorem B909265 : Blo 806344 909265 := bbase (se 2 (by rfl) ⟨340974, by rfl⟩ : syracuseStep 909265 = 681949) (by norm_num)
theorem B909301 : Blo 806344 909301 := bbase (se 5 (by rfl) ⟨42623, by rfl⟩ : syracuseStep 909301 = 85247) (by norm_num)
theorem B909337 : Blo 806344 909337 := bbase (se 2 (by rfl) ⟨341001, by rfl⟩ : syracuseStep 909337 = 682003) (by norm_num)
theorem B909373 : Blo 806344 909373 := bbase (se 3 (by rfl) ⟨170507, by rfl⟩ : syracuseStep 909373 = 341015) (by norm_num)
theorem B909409 : Blo 806344 909409 := bbase (se 2 (by rfl) ⟨341028, by rfl⟩ : syracuseStep 909409 = 682057) (by norm_num)
theorem B909445 : Blo 806344 909445 := bbase (se 4 (by rfl) ⟨85260, by rfl⟩ : syracuseStep 909445 = 170521) (by norm_num)
theorem B909481 : Blo 806344 909481 := bbase (se 2 (by rfl) ⟨341055, by rfl⟩ : syracuseStep 909481 = 682111) (by norm_num)
theorem B909517 : Blo 806344 909517 := bbase (se 3 (by rfl) ⟨170534, by rfl⟩ : syracuseStep 909517 = 341069) (by norm_num)
theorem B909553 : Blo 806344 909553 := bbase (se 2 (by rfl) ⟨341082, by rfl⟩ : syracuseStep 909553 = 682165) (by norm_num)
theorem B4088069 : Blo 806344 4088069 := bbase (se 4 (by rfl) ⟨383256, by rfl⟩ : syracuseStep 4088069 = 766513) (by norm_num)
theorem B1728773 : Blo 806344 1728773 := bbase (se 4 (by rfl) ⟨162072, by rfl⟩ : syracuseStep 1728773 = 324145) (by norm_num)
theorem B909589 : Blo 806344 909589 := bbase (se 6 (by rfl) ⟨21318, by rfl⟩ : syracuseStep 909589 = 42637) (by norm_num)
theorem B909625 : Blo 806344 909625 := bbase (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) (by norm_num)
theorem B4251973 : Blo 806344 4251973 := bbase (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) (by norm_num)
theorem B909661 : Blo 806344 909661 := bbase (se 3 (by rfl) ⟨170561, by rfl⟩ : syracuseStep 909661 = 341123) (by norm_num)
theorem B909697 : Blo 806344 909697 := bbase (se 2 (by rfl) ⟨341136, by rfl⟩ : syracuseStep 909697 = 682273) (by norm_num)
theorem B909733 : Blo 806344 909733 := bbase (se 4 (by rfl) ⟨85287, by rfl⟩ : syracuseStep 909733 = 170575) (by norm_num)
theorem B909769 : Blo 806344 909769 := bbase (se 2 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 909769 = 682327) (by norm_num)
theorem B4612565 : Blo 806344 4612565 := bbase (se 7 (by rfl) ⟨54053, by rfl⟩ : syracuseStep 4612565 = 108107) (by norm_num)
theorem B909805 : Blo 806344 909805 := bbase (se 3 (by rfl) ⟨170588, by rfl⟩ : syracuseStep 909805 = 341177) (by norm_num)
theorem B1729021 : Blo 806344 1729021 := bbase (se 3 (by rfl) ⟨324191, by rfl⟩ : syracuseStep 1729021 = 648383) (by norm_num)
theorem B909841 : Blo 806344 909841 := bbase (se 2 (by rfl) ⟨341190, by rfl⟩ : syracuseStep 909841 = 682381) (by norm_num)
theorem B909877 : Blo 806344 909877 := bbase (se 5 (by rfl) ⟨42650, by rfl⟩ : syracuseStep 909877 = 85301) (by norm_num)
theorem B909913 : Blo 806344 909913 := bbase (se 2 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 909913 = 682435) (by norm_num)
theorem B3072613 : Blo 806344 3072613 := bbase (se 4 (by rfl) ⟨288057, by rfl⟩ : syracuseStep 3072613 = 576115) (by norm_num)
theorem B1532533 : Blo 806344 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B909949 : Blo 806344 909949 := bbase (se 3 (by rfl) ⟨170615, by rfl⟩ : syracuseStep 909949 = 341231) (by norm_num)
theorem B909985 : Blo 806344 909985 := bbase (se 2 (by rfl) ⟨341244, by rfl⟩ : syracuseStep 909985 = 682489) (by norm_num)
theorem B1401517 : Blo 806344 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B910021 : Blo 806344 910021 := bbase (se 4 (by rfl) ⟨85314, by rfl⟩ : syracuseStep 910021 = 170629) (by norm_num)
theorem B910057 : Blo 806344 910057 := bbase (se 2 (by rfl) ⟨341271, by rfl⟩ : syracuseStep 910057 = 682543) (by norm_num)
theorem B1532677 : Blo 806344 1532677 := bbase (se 4 (by rfl) ⟨143688, by rfl⟩ : syracuseStep 1532677 = 287377) (by norm_num)
theorem B910093 : Blo 806344 910093 := bbase (se 3 (by rfl) ⟨170642, by rfl⟩ : syracuseStep 910093 = 341285) (by norm_num)
theorem B910129 : Blo 806344 910129 := bbase (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) (by norm_num)
theorem B19653461 : Blo 806344 19653461 := bbase (se 9 (by rfl) ⟨57578, by rfl⟩ : syracuseStep 19653461 = 115157) (by norm_num)
theorem B910165 : Blo 806344 910165 := bbase (se 9 (by rfl) ⟨2666, by rfl⟩ : syracuseStep 910165 = 5333) (by norm_num)
theorem B2909029 : Blo 806344 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B910201 : Blo 806344 910201 := bbase (se 2 (by rfl) ⟨341325, by rfl⟩ : syracuseStep 910201 = 682651) (by norm_num)
theorem B3072917 : Blo 806344 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B910237 : Blo 806344 910237 := bbase (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) (by norm_num)
theorem B1532837 : Blo 806344 1532837 := bbase (se 4 (by rfl) ⟨143703, by rfl⟩ : syracuseStep 1532837 = 287407) (by norm_num)
theorem B910273 : Blo 806344 910273 := bbase (se 2 (by rfl) ⟨341352, by rfl⟩ : syracuseStep 910273 = 682705) (by norm_num)
theorem B910309 : Blo 806344 910309 := bbase (se 4 (by rfl) ⟨85341, by rfl⟩ : syracuseStep 910309 = 170683) (by norm_num)
theorem B1729525 : Blo 806344 1729525 := bbase (se 5 (by rfl) ⟨81071, by rfl⟩ : syracuseStep 1729525 = 162143) (by norm_num)
theorem B2909189 : Blo 806344 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B910345 : Blo 806344 910345 := bbase (se 2 (by rfl) ⟨341379, by rfl⟩ : syracuseStep 910345 = 682759) (by norm_num)
theorem B910381 : Blo 806344 910381 := bbase (se 3 (by rfl) ⟨170696, by rfl⟩ : syracuseStep 910381 = 341393) (by norm_num)
theorem B1532981 : Blo 806344 1532981 := bbase (se 5 (by rfl) ⟨71858, by rfl⟩ : syracuseStep 1532981 = 143717) (by norm_num)
theorem B910417 : Blo 806344 910417 := bbase (se 2 (by rfl) ⟨341406, by rfl⟩ : syracuseStep 910417 = 682813) (by norm_num)
theorem B910453 : Blo 806344 910453 := bbase (se 5 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 910453 = 85355) (by norm_num)
theorem B910489 : Blo 806344 910489 := bbase (se 2 (by rfl) ⟨341433, by rfl⟩ : syracuseStep 910489 = 682867) (by norm_num)
theorem B910525 : Blo 806344 910525 := bbase (se 3 (by rfl) ⟨170723, by rfl⟩ : syracuseStep 910525 = 341447) (by norm_num)
theorem B910561 : Blo 806344 910561 := bbase (se 2 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 910561 = 682921) (by norm_num)
theorem B910597 : Blo 806344 910597 := bbase (se 4 (by rfl) ⟨85368, by rfl⟩ : syracuseStep 910597 = 170737) (by norm_num)
theorem B910633 : Blo 806344 910633 := bbase (se 2 (by rfl) ⟨341487, by rfl⟩ : syracuseStep 910633 = 682975) (by norm_num)
theorem B910669 : Blo 806344 910669 := bbase (se 3 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 910669 = 341501) (by norm_num)
theorem B1533269 : Blo 806344 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B910705 : Blo 806344 910705 := bbase (se 2 (by rfl) ⟨341514, by rfl⟩ : syracuseStep 910705 = 683029) (by norm_num)
theorem B910741 : Blo 806344 910741 := bbase (se 6 (by rfl) ⟨21345, by rfl⟩ : syracuseStep 910741 = 42691) (by norm_num)
theorem B910777 : Blo 806344 910777 := bbase (se 2 (by rfl) ⟨341541, by rfl⟩ : syracuseStep 910777 = 683083) (by norm_num)
theorem B910813 : Blo 806344 910813 := bbase (se 3 (by rfl) ⟨170777, by rfl⟩ : syracuseStep 910813 = 341555) (by norm_num)
theorem B1533421 : Blo 806344 1533421 := bbase (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) (by norm_num)
theorem B910849 : Blo 806344 910849 := bbase (se 2 (by rfl) ⟨341568, by rfl⟩ : syracuseStep 910849 = 683137) (by norm_num)
theorem B4089365 : Blo 806344 4089365 := bbase (se 6 (by rfl) ⟨95844, by rfl⟩ : syracuseStep 4089365 = 191689) (by norm_num)
theorem B910885 : Blo 806344 910885 := bbase (se 4 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 910885 = 170791) (by norm_num)
theorem B4154933 : Blo 806344 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B910921 : Blo 806344 910921 := bbase (se 2 (by rfl) ⟨341595, by rfl⟩ : syracuseStep 910921 = 683191) (by norm_num)
theorem B910957 : Blo 806344 910957 := bbase (se 3 (by rfl) ⟨170804, by rfl⟩ : syracuseStep 910957 = 341609) (by norm_num)
theorem B3892853 : Blo 806344 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B910993 : Blo 806344 910993 := bbase (se 2 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 910993 = 683245) (by norm_num)
theorem B1107613 : Blo 806344 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B911029 : Blo 806344 911029 := bbase (se 5 (by rfl) ⟨42704, by rfl⟩ : syracuseStep 911029 = 85409) (by norm_num)
theorem B3106517 : Blo 806344 3106517 := bbase (se 7 (by rfl) ⟨36404, by rfl⟩ : syracuseStep 3106517 = 72809) (by norm_num)
theorem B911065 : Blo 806344 911065 := bbase (se 2 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 911065 = 683299) (by norm_num)
theorem B911101 : Blo 806344 911101 := bbase (se 3 (by rfl) ⟨170831, by rfl⟩ : syracuseStep 911101 = 341663) (by norm_num)
theorem B1533725 : Blo 806344 1533725 := bbase (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) (by norm_num)
theorem B911137 : Blo 806344 911137 := bbase (se 2 (by rfl) ⟨341676, by rfl⟩ : syracuseStep 911137 = 683353) (by norm_num)
theorem B911173 : Blo 806344 911173 := bbase (se 4 (by rfl) ⟨85422, by rfl⟩ : syracuseStep 911173 = 170845) (by norm_num)
theorem B911209 : Blo 806344 911209 := bbase (se 2 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 911209 = 683407) (by norm_num)
theorem B1730413 : Blo 806344 1730413 := bbase (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) (by norm_num)
theorem B911245 : Blo 806344 911245 := bbase (se 3 (by rfl) ⟨170858, by rfl⟩ : syracuseStep 911245 = 341717) (by norm_num)
theorem B911281 : Blo 806344 911281 := bbase (se 2 (by rfl) ⟨341730, by rfl⟩ : syracuseStep 911281 = 683461) (by norm_num)
theorem B911317 : Blo 806344 911317 := bbase (se 7 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 911317 = 21359) (by norm_num)
theorem B3893237 : Blo 806344 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B911353 : Blo 806344 911353 := bbase (se 2 (by rfl) ⟨341757, by rfl⟩ : syracuseStep 911353 = 683515) (by norm_num)
theorem B911389 : Blo 806344 911389 := bbase (se 3 (by rfl) ⟨170885, by rfl⟩ : syracuseStep 911389 = 341771) (by norm_num)
theorem B911425 : Blo 806344 911425 := bbase (se 2 (by rfl) ⟨341784, by rfl⟩ : syracuseStep 911425 = 683569) (by norm_num)
theorem B911461 : Blo 806344 911461 := bbase (se 4 (by rfl) ⟨85449, by rfl⟩ : syracuseStep 911461 = 170899) (by norm_num)
theorem B911497 : Blo 806344 911497 := bbase (se 2 (by rfl) ⟨341811, by rfl⟩ : syracuseStep 911497 = 683623) (by norm_num)
theorem B911533 : Blo 806344 911533 := bbase (se 3 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 911533 = 341825) (by norm_num)
theorem B911569 : Blo 806344 911569 := bbase (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) (by norm_num)
theorem B911605 : Blo 806344 911605 := bbase (se 5 (by rfl) ⟨42731, by rfl⟩ : syracuseStep 911605 = 85463) (by norm_num)
theorem B1534477 : Blo 806344 1534477 := bbase (se 3 (by rfl) ⟨287714, by rfl⟩ : syracuseStep 1534477 = 575429) (by norm_num)
theorem B1534621 : Blo 806344 1534621 := bbase (se 3 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 1534621 = 575483) (by norm_num)
theorem B6908597 : Blo 806344 6908597 := bbase (se 5 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 6908597 = 647681) (by norm_num)
theorem B4090661 : Blo 806344 4090661 := bbase (se 4 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 4090661 = 766999) (by norm_num)
theorem B1534781 : Blo 806344 1534781 := bbase (se 3 (by rfl) ⟨287771, by rfl⟩ : syracuseStep 1534781 = 575543) (by norm_num)
theorem B1534925 : Blo 806344 1534925 := bbase (se 3 (by rfl) ⟨287798, by rfl⟩ : syracuseStep 1534925 = 575597) (by norm_num)
theorem B3075029 : Blo 806344 3075029 := bbase (se 7 (by rfl) ⟨36035, by rfl⟩ : syracuseStep 3075029 = 72071) (by norm_num)
theorem B2190293 : Blo 806344 2190293 := bbase (se 7 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 2190293 = 51335) (by norm_num)
theorem B1535213 : Blo 806344 1535213 := bbase (se 3 (by rfl) ⟨287852, by rfl⟩ : syracuseStep 1535213 = 575705) (by norm_num)
theorem B3075317 : Blo 806344 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B6548789 : Blo 806344 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B1535365 : Blo 806344 1535365 := bbase (se 4 (by rfl) ⟨143940, by rfl⟩ : syracuseStep 1535365 = 287881) (by norm_num)
theorem B1535669 : Blo 806344 1535669 := bbase (se 5 (by rfl) ⟨71984, by rfl⟩ : syracuseStep 1535669 = 143969) (by norm_num)
theorem B945929 : Blo 806344 945929 := bbase (se 2 (by rfl) ⟨354723, by rfl⟩ : syracuseStep 945929 = 709447) (by norm_num)
theorem B4091957 : Blo 806344 4091957 := bbase (se 5 (by rfl) ⟨191810, by rfl⟩ : syracuseStep 4091957 = 383621) (by norm_num)
theorem B3076501 : Blo 806344 3076501 := bbase (se 6 (by rfl) ⟨72105, by rfl⟩ : syracuseStep 3076501 = 144211) (by norm_num)
theorem B1536421 : Blo 806344 1536421 := bbase (se 4 (by rfl) ⟨144039, by rfl⟩ : syracuseStep 1536421 = 288079) (by norm_num)
theorem B2585125 : Blo 806344 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B6124085 : Blo 806344 6124085 := bbase (se 5 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 6124085 = 574133) (by norm_num)
theorem B1536565 : Blo 806344 1536565 := bbase (se 5 (by rfl) ⟨72026, by rfl⟩ : syracuseStep 1536565 = 144053) (by norm_num)
theorem B2585189 : Blo 806344 2585189 := bbase (se 4 (by rfl) ⟨242361, by rfl⟩ : syracuseStep 2585189 = 484723) (by norm_num)
theorem B1536725 : Blo 806344 1536725 := bbase (se 7 (by rfl) ⟨18008, by rfl⟩ : syracuseStep 1536725 = 36017) (by norm_num)
theorem B1536869 : Blo 806344 1536869 := bbase (se 4 (by rfl) ⟨144081, by rfl⟩ : syracuseStep 1536869 = 288163) (by norm_num)
theorem B16610197 : Blo 806344 16610197 := bbase (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) (by norm_num)
theorem B1537157 : Blo 806344 1537157 := bbase (se 4 (by rfl) ⟨144108, by rfl⟩ : syracuseStep 1537157 = 288217) (by norm_num)
theorem B1209533 : Blo 806344 1209533 := bbase (se 3 (by rfl) ⟨226787, by rfl⟩ : syracuseStep 1209533 = 453575) (by norm_num)
theorem B1209557 : Blo 806344 1209557 := bbase (se 7 (by rfl) ⟨14174, by rfl⟩ : syracuseStep 1209557 = 28349) (by norm_num)
theorem B1209581 : Blo 806344 1209581 := bbase (se 3 (by rfl) ⟨226796, by rfl⟩ : syracuseStep 1209581 = 453593) (by norm_num)
theorem B1209605 : Blo 806344 1209605 := bbase (se 4 (by rfl) ⟨113400, by rfl⟩ : syracuseStep 1209605 = 226801) (by norm_num)
theorem B1209629 : Blo 806344 1209629 := bbase (se 3 (by rfl) ⟨226805, by rfl⟩ : syracuseStep 1209629 = 453611) (by norm_num)
theorem B1537309 : Blo 806344 1537309 := bbase (se 3 (by rfl) ⟨288245, by rfl⟩ : syracuseStep 1537309 = 576491) (by norm_num)
theorem B1209653 : Blo 806344 1209653 := bbase (se 5 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 1209653 = 113405) (by norm_num)
theorem B4093253 : Blo 806344 4093253 := bbase (se 4 (by rfl) ⟨383742, by rfl⟩ : syracuseStep 4093253 = 767485) (by norm_num)
theorem B1209677 : Blo 806344 1209677 := bbase (se 3 (by rfl) ⟨226814, by rfl⟩ : syracuseStep 1209677 = 453629) (by norm_num)
theorem B1209701 : Blo 806344 1209701 := bbase (se 4 (by rfl) ⟨113409, by rfl⟩ : syracuseStep 1209701 = 226819) (by norm_num)
theorem B1209725 : Blo 806344 1209725 := bbase (se 3 (by rfl) ⟨226823, by rfl⟩ : syracuseStep 1209725 = 453647) (by norm_num)
theorem B1209749 : Blo 806344 1209749 := bbase (se 6 (by rfl) ⟨28353, by rfl⟩ : syracuseStep 1209749 = 56707) (by norm_num)
theorem B1209773 : Blo 806344 1209773 := bbase (se 3 (by rfl) ⟨226832, by rfl⟩ : syracuseStep 1209773 = 453665) (by norm_num)
theorem B1209797 : Blo 806344 1209797 := bbase (se 4 (by rfl) ⟨113418, by rfl⟩ : syracuseStep 1209797 = 226837) (by norm_num)
theorem B1209821 : Blo 806344 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B1209845 : Blo 806344 1209845 := bbase (se 5 (by rfl) ⟨56711, by rfl⟩ : syracuseStep 1209845 = 113423) (by norm_num)
theorem B1209869 : Blo 806344 1209869 := bbase (se 3 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 1209869 = 453701) (by norm_num)
theorem B1209893 : Blo 806344 1209893 := bbase (se 4 (by rfl) ⟨113427, by rfl⟩ : syracuseStep 1209893 = 226855) (by norm_num)
theorem B5174837 : Blo 806344 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B1209917 : Blo 806344 1209917 := bbase (se 3 (by rfl) ⟨226859, by rfl⟩ : syracuseStep 1209917 = 453719) (by norm_num)
theorem B1537613 : Blo 806344 1537613 := bbase (se 3 (by rfl) ⟨288302, by rfl⟩ : syracuseStep 1537613 = 576605) (by norm_num)
theorem B1209941 : Blo 806344 1209941 := bbase (se 8 (by rfl) ⟨7089, by rfl⟩ : syracuseStep 1209941 = 14179) (by norm_num)
theorem B1209965 : Blo 806344 1209965 := bbase (se 3 (by rfl) ⟨226868, by rfl⟩ : syracuseStep 1209965 = 453737) (by norm_num)
theorem B3929717 : Blo 806344 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B1209989 : Blo 806344 1209989 := bbase (se 4 (by rfl) ⟨113436, by rfl⟩ : syracuseStep 1209989 = 226873) (by norm_num)
theorem B1210013 : Blo 806344 1210013 := bbase (se 3 (by rfl) ⟨226877, by rfl⟩ : syracuseStep 1210013 = 453755) (by norm_num)
theorem B1210037 : Blo 806344 1210037 := bbase (se 5 (by rfl) ⟨56720, by rfl⟩ : syracuseStep 1210037 = 113441) (by norm_num)
theorem B1210061 : Blo 806344 1210061 := bbase (se 3 (by rfl) ⟨226886, by rfl⟩ : syracuseStep 1210061 = 453773) (by norm_num)
theorem B1210085 : Blo 806344 1210085 := bbase (se 4 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 1210085 = 226891) (by norm_num)
theorem B1210109 : Blo 806344 1210109 := bbase (se 3 (by rfl) ⟨226895, by rfl⟩ : syracuseStep 1210109 = 453791) (by norm_num)
theorem B1210133 : Blo 806344 1210133 := bbase (se 6 (by rfl) ⟨28362, by rfl⟩ : syracuseStep 1210133 = 56725) (by norm_num)
theorem B1210157 : Blo 806344 1210157 := bbase (se 3 (by rfl) ⟨226904, by rfl⟩ : syracuseStep 1210157 = 453809) (by norm_num)
theorem B1210181 : Blo 806344 1210181 := bbase (se 4 (by rfl) ⟨113454, by rfl⟩ : syracuseStep 1210181 = 226909) (by norm_num)
theorem B1210205 : Blo 806344 1210205 := bbase (se 3 (by rfl) ⟨226913, by rfl⟩ : syracuseStep 1210205 = 453827) (by norm_num)
theorem B1210229 : Blo 806344 1210229 := bbase (se 5 (by rfl) ⟨56729, by rfl⟩ : syracuseStep 1210229 = 113459) (by norm_num)
theorem B1210253 : Blo 806344 1210253 := bbase (se 3 (by rfl) ⟨226922, by rfl⟩ : syracuseStep 1210253 = 453845) (by norm_num)
theorem B1210277 : Blo 806344 1210277 := bbase (se 4 (by rfl) ⟨113463, by rfl⟩ : syracuseStep 1210277 = 226927) (by norm_num)
theorem B948137 : Blo 806344 948137 := bbase (se 2 (by rfl) ⟨355551, by rfl⟩ : syracuseStep 948137 = 711103) (by norm_num)
theorem B1210301 : Blo 806344 1210301 := bbase (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) (by norm_num)
theorem B2947013 : Blo 806344 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B1210325 : Blo 806344 1210325 := bbase (se 7 (by rfl) ⟨14183, by rfl⟩ : syracuseStep 1210325 = 28367) (by norm_num)
theorem B1210349 : Blo 806344 1210349 := bbase (se 3 (by rfl) ⟨226940, by rfl⟩ : syracuseStep 1210349 = 453881) (by norm_num)
theorem B1210373 : Blo 806344 1210373 := bbase (se 4 (by rfl) ⟨113472, by rfl⟩ : syracuseStep 1210373 = 226945) (by norm_num)
theorem B1210397 : Blo 806344 1210397 := bbase (se 3 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 1210397 = 453899) (by norm_num)
theorem B1210421 : Blo 806344 1210421 := bbase (se 5 (by rfl) ⟨56738, by rfl⟩ : syracuseStep 1210421 = 113477) (by norm_num)
theorem B1964101 : Blo 806344 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B1210445 : Blo 806344 1210445 := bbase (se 3 (by rfl) ⟨226958, by rfl⟩ : syracuseStep 1210445 = 453917) (by norm_num)
theorem B1210469 : Blo 806344 1210469 := bbase (se 4 (by rfl) ⟨113481, by rfl⟩ : syracuseStep 1210469 = 226963) (by norm_num)
theorem B1210493 : Blo 806344 1210493 := bbase (se 3 (by rfl) ⟨226967, by rfl⟩ : syracuseStep 1210493 = 453935) (by norm_num)
theorem B1210517 : Blo 806344 1210517 := bbase (se 6 (by rfl) ⟨28371, by rfl⟩ : syracuseStep 1210517 = 56743) (by norm_num)
theorem B1210541 : Blo 806344 1210541 := bbase (se 3 (by rfl) ⟨226976, by rfl⟩ : syracuseStep 1210541 = 453953) (by norm_num)
theorem B1210565 : Blo 806344 1210565 := bbase (se 4 (by rfl) ⟨113490, by rfl⟩ : syracuseStep 1210565 = 226981) (by norm_num)
theorem B1210589 : Blo 806344 1210589 := bbase (se 3 (by rfl) ⟨226985, by rfl⟩ : syracuseStep 1210589 = 453971) (by norm_num)
theorem B1210613 : Blo 806344 1210613 := bbase (se 5 (by rfl) ⟨56747, by rfl⟩ : syracuseStep 1210613 = 113495) (by norm_num)
theorem B1210637 : Blo 806344 1210637 := bbase (se 3 (by rfl) ⟨226994, by rfl⟩ : syracuseStep 1210637 = 453989) (by norm_num)
theorem B1210661 : Blo 806344 1210661 := bbase (se 4 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 1210661 = 226999) (by norm_num)
theorem B1210685 : Blo 806344 1210685 := bbase (se 3 (by rfl) ⟨227003, by rfl⟩ : syracuseStep 1210685 = 454007) (by norm_num)
theorem B1538365 : Blo 806344 1538365 := bbase (se 3 (by rfl) ⟨288443, by rfl⟩ : syracuseStep 1538365 = 576887) (by norm_num)
theorem B1210709 : Blo 806344 1210709 := bbase (se 10 (by rfl) ⟨1773, by rfl⟩ : syracuseStep 1210709 = 3547) (by norm_num)
theorem B3275093 : Blo 806344 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B1210733 : Blo 806344 1210733 := bbase (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) (by norm_num)
theorem B1210757 : Blo 806344 1210757 := bbase (se 4 (by rfl) ⟨113508, by rfl⟩ : syracuseStep 1210757 = 227017) (by norm_num)
theorem B817561 : Blo 806344 817561 := bbase (se 2 (by rfl) ⟨306585, by rfl⟩ : syracuseStep 817561 = 613171) (by norm_num)
theorem B1210781 : Blo 806344 1210781 := bbase (se 3 (by rfl) ⟨227021, by rfl⟩ : syracuseStep 1210781 = 454043) (by norm_num)
theorem B1210805 : Blo 806344 1210805 := bbase (se 5 (by rfl) ⟨56756, by rfl⟩ : syracuseStep 1210805 = 113513) (by norm_num)
theorem B817597 : Blo 806344 817597 := bbase (se 3 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 817597 = 306599) (by norm_num)
theorem B1210829 : Blo 806344 1210829 := bbase (se 3 (by rfl) ⟨227030, by rfl⟩ : syracuseStep 1210829 = 454061) (by norm_num)
theorem B3275221 : Blo 806344 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B1210853 : Blo 806344 1210853 := bbase (se 4 (by rfl) ⟨113517, by rfl⟩ : syracuseStep 1210853 = 227035) (by norm_num)
theorem B1210877 : Blo 806344 1210877 := bbase (se 3 (by rfl) ⟨227039, by rfl⟩ : syracuseStep 1210877 = 454079) (by norm_num)
theorem B1210901 : Blo 806344 1210901 := bbase (se 6 (by rfl) ⟨28380, by rfl⟩ : syracuseStep 1210901 = 56761) (by norm_num)
theorem B1210925 : Blo 806344 1210925 := bbase (se 3 (by rfl) ⟨227048, by rfl⟩ : syracuseStep 1210925 = 454097) (by norm_num)
theorem B1210949 : Blo 806344 1210949 := bbase (se 4 (by rfl) ⟨113526, by rfl⟩ : syracuseStep 1210949 = 227053) (by norm_num)
theorem B4094549 : Blo 806344 4094549 := bbase (se 8 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 4094549 = 47983) (by norm_num)
theorem B1210973 : Blo 806344 1210973 := bbase (se 3 (by rfl) ⟨227057, by rfl⟩ : syracuseStep 1210973 = 454115) (by norm_num)
theorem B1210997 : Blo 806344 1210997 := bbase (se 5 (by rfl) ⟨56765, by rfl⟩ : syracuseStep 1210997 = 113531) (by norm_num)
theorem B1211021 : Blo 806344 1211021 := bbase (se 3 (by rfl) ⟨227066, by rfl⟩ : syracuseStep 1211021 = 454133) (by norm_num)
theorem B948893 : Blo 806344 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B1211045 : Blo 806344 1211045 := bbase (se 4 (by rfl) ⟨113535, by rfl⟩ : syracuseStep 1211045 = 227071) (by norm_num)
theorem B1211069 : Blo 806344 1211069 := bbase (se 3 (by rfl) ⟨227075, by rfl⟩ : syracuseStep 1211069 = 454151) (by norm_num)
theorem B1473221 : Blo 806344 1473221 := bbase (se 4 (by rfl) ⟨138114, by rfl⟩ : syracuseStep 1473221 = 276229) (by norm_num)
theorem B1211093 : Blo 806344 1211093 := bbase (se 7 (by rfl) ⟨14192, by rfl⟩ : syracuseStep 1211093 = 28385) (by norm_num)
theorem B1211117 : Blo 806344 1211117 := bbase (se 3 (by rfl) ⟨227084, by rfl⟩ : syracuseStep 1211117 = 454169) (by norm_num)
theorem B1211141 : Blo 806344 1211141 := bbase (se 4 (by rfl) ⟨113544, by rfl⟩ : syracuseStep 1211141 = 227089) (by norm_num)
theorem B1211165 : Blo 806344 1211165 := bbase (se 3 (by rfl) ⟨227093, by rfl⟩ : syracuseStep 1211165 = 454187) (by norm_num)
theorem B1211189 : Blo 806344 1211189 := bbase (se 5 (by rfl) ⟨56774, by rfl⟩ : syracuseStep 1211189 = 113549) (by norm_num)
theorem B1211213 : Blo 806344 1211213 := bbase (se 3 (by rfl) ⟨227102, by rfl⟩ : syracuseStep 1211213 = 454205) (by norm_num)
theorem B1211237 : Blo 806344 1211237 := bbase (se 4 (by rfl) ⟨113553, by rfl⟩ : syracuseStep 1211237 = 227107) (by norm_num)
theorem B1211261 : Blo 806344 1211261 := bbase (se 3 (by rfl) ⟨227111, by rfl⟩ : syracuseStep 1211261 = 454223) (by norm_num)
theorem B1211285 : Blo 806344 1211285 := bbase (se 6 (by rfl) ⟨28389, by rfl⟩ : syracuseStep 1211285 = 56779) (by norm_num)
theorem B1211309 : Blo 806344 1211309 := bbase (se 3 (by rfl) ⟨227120, by rfl⟩ : syracuseStep 1211309 = 454241) (by norm_num)
theorem B1211333 : Blo 806344 1211333 := bbase (se 4 (by rfl) ⟨113562, by rfl⟩ : syracuseStep 1211333 = 227125) (by norm_num)
theorem B1211357 : Blo 806344 1211357 := bbase (se 3 (by rfl) ⟨227129, by rfl⟩ : syracuseStep 1211357 = 454259) (by norm_num)
theorem B818149 : Blo 806344 818149 := bbase (se 4 (by rfl) ⟨76701, by rfl⟩ : syracuseStep 818149 = 153403) (by norm_num)
theorem B1211381 : Blo 806344 1211381 := bbase (se 5 (by rfl) ⟨56783, by rfl⟩ : syracuseStep 1211381 = 113567) (by norm_num)
theorem B1211405 : Blo 806344 1211405 := bbase (se 3 (by rfl) ⟨227138, by rfl⟩ : syracuseStep 1211405 = 454277) (by norm_num)
theorem B1211429 : Blo 806344 1211429 := bbase (se 4 (by rfl) ⟨113571, by rfl⟩ : syracuseStep 1211429 = 227143) (by norm_num)
theorem B1211453 : Blo 806344 1211453 := bbase (se 3 (by rfl) ⟨227147, by rfl⟩ : syracuseStep 1211453 = 454295) (by norm_num)
theorem B1211477 : Blo 806344 1211477 := bbase (se 8 (by rfl) ⟨7098, by rfl⟩ : syracuseStep 1211477 = 14197) (by norm_num)
theorem B1211501 : Blo 806344 1211501 := bbase (se 3 (by rfl) ⟨227156, by rfl⟩ : syracuseStep 1211501 = 454313) (by norm_num)
theorem B1211525 : Blo 806344 1211525 := bbase (se 4 (by rfl) ⟨113580, by rfl⟩ : syracuseStep 1211525 = 227161) (by norm_num)
theorem B1211549 : Blo 806344 1211549 := bbase (se 3 (by rfl) ⟨227165, by rfl⟩ : syracuseStep 1211549 = 454331) (by norm_num)
theorem B1211573 : Blo 806344 1211573 := bbase (se 5 (by rfl) ⟨56792, by rfl⟩ : syracuseStep 1211573 = 113585) (by norm_num)
theorem B1211597 : Blo 806344 1211597 := bbase (se 3 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 1211597 = 454349) (by norm_num)
theorem B1211621 : Blo 806344 1211621 := bbase (se 4 (by rfl) ⟨113589, by rfl⟩ : syracuseStep 1211621 = 227179) (by norm_num)
theorem B1211645 : Blo 806344 1211645 := bbase (se 3 (by rfl) ⟨227183, by rfl⟩ : syracuseStep 1211645 = 454367) (by norm_num)
theorem B1211669 : Blo 806344 1211669 := bbase (se 6 (by rfl) ⟨28398, by rfl⟩ : syracuseStep 1211669 = 56797) (by norm_num)
theorem B1211693 : Blo 806344 1211693 := bbase (se 3 (by rfl) ⟨227192, by rfl⟩ : syracuseStep 1211693 = 454385) (by norm_num)
theorem B1211717 : Blo 806344 1211717 := bbase (se 4 (by rfl) ⟨113598, by rfl⟩ : syracuseStep 1211717 = 227197) (by norm_num)
theorem B1211741 : Blo 806344 1211741 := bbase (se 3 (by rfl) ⟨227201, by rfl⟩ : syracuseStep 1211741 = 454403) (by norm_num)
theorem B1211765 : Blo 806344 1211765 := bbase (se 5 (by rfl) ⟨56801, by rfl⟩ : syracuseStep 1211765 = 113603) (by norm_num)
theorem B1211789 : Blo 806344 1211789 := bbase (se 3 (by rfl) ⟨227210, by rfl⟩ : syracuseStep 1211789 = 454421) (by norm_num)
theorem B1211813 : Blo 806344 1211813 := bbase (se 4 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 1211813 = 227215) (by norm_num)
theorem B1211837 : Blo 806344 1211837 := bbase (se 3 (by rfl) ⟨227219, by rfl⟩ : syracuseStep 1211837 = 454439) (by norm_num)
theorem B1211861 : Blo 806344 1211861 := bbase (se 7 (by rfl) ⟨14201, by rfl⟩ : syracuseStep 1211861 = 28403) (by norm_num)
theorem B1211885 : Blo 806344 1211885 := bbase (se 3 (by rfl) ⟨227228, by rfl⟩ : syracuseStep 1211885 = 454457) (by norm_num)
theorem B1211909 : Blo 806344 1211909 := bbase (se 4 (by rfl) ⟨113616, by rfl⟩ : syracuseStep 1211909 = 227233) (by norm_num)
theorem B1211933 : Blo 806344 1211933 := bbase (se 3 (by rfl) ⟨227237, by rfl⟩ : syracuseStep 1211933 = 454475) (by norm_num)
theorem B2588213 : Blo 806344 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B1211957 : Blo 806344 1211957 := bbase (se 5 (by rfl) ⟨56810, by rfl⟩ : syracuseStep 1211957 = 113621) (by norm_num)
theorem B1211981 : Blo 806344 1211981 := bbase (se 3 (by rfl) ⟨227246, by rfl⟩ : syracuseStep 1211981 = 454493) (by norm_num)
theorem B1212005 : Blo 806344 1212005 := bbase (se 4 (by rfl) ⟨113625, by rfl⟩ : syracuseStep 1212005 = 227251) (by norm_num)
theorem B1212029 : Blo 806344 1212029 := bbase (se 3 (by rfl) ⟨227255, by rfl⟩ : syracuseStep 1212029 = 454511) (by norm_num)
theorem B1212053 : Blo 806344 1212053 := bbase (se 6 (by rfl) ⟨28407, by rfl⟩ : syracuseStep 1212053 = 56815) (by norm_num)
theorem B1212077 : Blo 806344 1212077 := bbase (se 3 (by rfl) ⟨227264, by rfl⟩ : syracuseStep 1212077 = 454529) (by norm_num)
theorem B1212101 : Blo 806344 1212101 := bbase (se 4 (by rfl) ⟨113634, by rfl⟩ : syracuseStep 1212101 = 227269) (by norm_num)
theorem B1212125 : Blo 806344 1212125 := bbase (se 3 (by rfl) ⟨227273, by rfl⟩ : syracuseStep 1212125 = 454547) (by norm_num)
theorem B1212149 : Blo 806344 1212149 := bbase (se 5 (by rfl) ⟨56819, by rfl⟩ : syracuseStep 1212149 = 113639) (by norm_num)
theorem B1212173 : Blo 806344 1212173 := bbase (se 3 (by rfl) ⟨227282, by rfl⟩ : syracuseStep 1212173 = 454565) (by norm_num)
theorem B1212197 : Blo 806344 1212197 := bbase (se 4 (by rfl) ⟨113643, by rfl⟩ : syracuseStep 1212197 = 227287) (by norm_num)
theorem B1212221 : Blo 806344 1212221 := bbase (se 3 (by rfl) ⟨227291, by rfl⟩ : syracuseStep 1212221 = 454583) (by norm_num)
theorem B1212245 : Blo 806344 1212245 := bbase (se 9 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 1212245 = 7103) (by norm_num)
theorem B6225749 : Blo 806344 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B4095845 : Blo 806344 4095845 := bbase (se 4 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 4095845 = 767971) (by norm_num)
theorem B1212269 : Blo 806344 1212269 := bbase (se 3 (by rfl) ⟨227300, by rfl⟩ : syracuseStep 1212269 = 454601) (by norm_num)
theorem B819065 : Blo 806344 819065 := bbase (se 2 (by rfl) ⟨307149, by rfl⟩ : syracuseStep 819065 = 614299) (by norm_num)
theorem B1212293 : Blo 806344 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B1212317 : Blo 806344 1212317 := bbase (se 3 (by rfl) ⟨227309, by rfl⟩ : syracuseStep 1212317 = 454619) (by norm_num)
theorem B1212341 : Blo 806344 1212341 := bbase (se 5 (by rfl) ⟨56828, by rfl⟩ : syracuseStep 1212341 = 113657) (by norm_num)
theorem B1212365 : Blo 806344 1212365 := bbase (se 3 (by rfl) ⟨227318, by rfl⟩ : syracuseStep 1212365 = 454637) (by norm_num)
theorem B1212389 : Blo 806344 1212389 := bbase (se 4 (by rfl) ⟨113661, by rfl⟩ : syracuseStep 1212389 = 227323) (by norm_num)
theorem B1212413 : Blo 806344 1212413 := bbase (se 3 (by rfl) ⟨227327, by rfl⟩ : syracuseStep 1212413 = 454655) (by norm_num)
theorem B1212419 : Blo 806344 1212419 := bstep (se 1 (by rfl) ⟨909314, by rfl⟩ : syracuseStep 1212419 = 1818629) B1818629
theorem B1212449 : Blo 806344 1212449 := bstep (se 2 (by rfl) ⟨454668, by rfl⟩ : syracuseStep 1212449 = 909337) B909337
theorem B1212467 : Blo 806344 1212467 := bstep (se 1 (by rfl) ⟨909350, by rfl⟩ : syracuseStep 1212467 = 1818701) B1818701
theorem B1212497 : Blo 806344 1212497 := bstep (se 2 (by rfl) ⟨454686, by rfl⟩ : syracuseStep 1212497 = 909373) B909373
theorem B1212515 : Blo 806344 1212515 := bstep (se 1 (by rfl) ⟨909386, by rfl⟩ : syracuseStep 1212515 = 1818773) B1818773
theorem B39321713 : Blo 806344 39321713 := bstep (se 2 (by rfl) ⟨14745642, by rfl⟩ : syracuseStep 39321713 = 29491285) B29491285
theorem B4915313 : Blo 806344 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B1212545 : Blo 806344 1212545 := bstep (se 2 (by rfl) ⟨454704, by rfl⟩ : syracuseStep 1212545 = 909409) B909409
theorem B1212563 : Blo 806344 1212563 := bstep (se 1 (by rfl) ⟨909422, by rfl⟩ : syracuseStep 1212563 = 1818845) B1818845
theorem B1212593 : Blo 806344 1212593 := bstep (se 2 (by rfl) ⟨454722, by rfl⟩ : syracuseStep 1212593 = 909445) B909445
theorem B1212611 : Blo 806344 1212611 := bstep (se 1 (by rfl) ⟨909458, by rfl⟩ : syracuseStep 1212611 = 1818917) B1818917
theorem B1212641 : Blo 806344 1212641 := bstep (se 2 (by rfl) ⟨454740, by rfl⟩ : syracuseStep 1212641 = 909481) B909481
theorem B1212659 : Blo 806344 1212659 := bstep (se 1 (by rfl) ⟨909494, by rfl⟩ : syracuseStep 1212659 = 1818989) B1818989
theorem B1212689 : Blo 806344 1212689 := bstep (se 2 (by rfl) ⟨454758, by rfl⟩ : syracuseStep 1212689 = 909517) B909517
theorem B1212707 : Blo 806344 1212707 := bstep (se 1 (by rfl) ⟨909530, by rfl⟩ : syracuseStep 1212707 = 1819061) B1819061
theorem B1212737 : Blo 806344 1212737 := bstep (se 2 (by rfl) ⟨454776, by rfl⟩ : syracuseStep 1212737 = 909553) B909553
theorem B1212755 : Blo 806344 1212755 := bstep (se 1 (by rfl) ⟨909566, by rfl⟩ : syracuseStep 1212755 = 1819133) B1819133
theorem B3277169 : Blo 806344 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B1212785 : Blo 806344 1212785 := bstep (se 2 (by rfl) ⟨454794, by rfl⟩ : syracuseStep 1212785 = 909589) B909589
theorem B2589059 : Blo 806344 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B1212803 : Blo 806344 1212803 := bstep (se 1 (by rfl) ⟨909602, by rfl⟩ : syracuseStep 1212803 = 1819205) B1819205
theorem B1212833 : Blo 806344 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B5669297 : Blo 806344 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B1212851 : Blo 806344 1212851 := bstep (se 1 (by rfl) ⟨909638, by rfl⟩ : syracuseStep 1212851 = 1819277) B1819277
theorem B1212881 : Blo 806344 1212881 := bstep (se 2 (by rfl) ⟨454830, by rfl⟩ : syracuseStep 1212881 = 909661) B909661
theorem B1212899 : Blo 806344 1212899 := bstep (se 1 (by rfl) ⟨909674, by rfl⟩ : syracuseStep 1212899 = 1819349) B1819349
theorem B3277297 : Blo 806344 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B1212929 : Blo 806344 1212929 := bstep (se 2 (by rfl) ⟨454848, by rfl⟩ : syracuseStep 1212929 = 909697) B909697
theorem B1212947 : Blo 806344 1212947 := bstep (se 1 (by rfl) ⟨909710, by rfl⟩ : syracuseStep 1212947 = 1819421) B1819421
theorem B1212977 : Blo 806344 1212977 := bstep (se 2 (by rfl) ⟨454866, by rfl⟩ : syracuseStep 1212977 = 909733) B909733
theorem B1212995 : Blo 806344 1212995 := bstep (se 1 (by rfl) ⟨909746, by rfl⟩ : syracuseStep 1212995 = 1819493) B1819493
theorem B1213025 : Blo 806344 1213025 := bstep (se 2 (by rfl) ⟨454884, by rfl⟩ : syracuseStep 1213025 = 909769) B909769
theorem B1213043 : Blo 806344 1213043 := bstep (se 1 (by rfl) ⟨909782, by rfl⟩ : syracuseStep 1213043 = 1819565) B1819565
theorem B1213073 : Blo 806344 1213073 := bstep (se 2 (by rfl) ⟨454902, by rfl⟩ : syracuseStep 1213073 = 909805) B909805
theorem B1213091 : Blo 806344 1213091 := bstep (se 1 (by rfl) ⟨909818, by rfl⟩ : syracuseStep 1213091 = 1819637) B1819637
theorem B1213121 : Blo 806344 1213121 := bstep (se 2 (by rfl) ⟨454920, by rfl⟩ : syracuseStep 1213121 = 909841) B909841
theorem B1213139 : Blo 806344 1213139 := bstep (se 1 (by rfl) ⟨909854, by rfl⟩ : syracuseStep 1213139 = 1819709) B1819709
theorem B1213169 : Blo 806344 1213169 := bstep (se 2 (by rfl) ⟨454938, by rfl⟩ : syracuseStep 1213169 = 909877) B909877
theorem B1213187 : Blo 806344 1213187 := bstep (se 1 (by rfl) ⟨909890, by rfl⟩ : syracuseStep 1213187 = 1819781) B1819781
theorem B1213217 : Blo 806344 1213217 := bstep (se 2 (by rfl) ⟨454956, by rfl⟩ : syracuseStep 1213217 = 909913) B909913
theorem B4096817 : Blo 806344 4096817 := bstep (se 2 (by rfl) ⟨1536306, by rfl⟩ : syracuseStep 4096817 = 3072613) B3072613
theorem B1213235 : Blo 806344 1213235 := bstep (se 1 (by rfl) ⟨909926, by rfl⟩ : syracuseStep 1213235 = 1819853) B1819853
theorem B1213265 : Blo 806344 1213265 := bstep (se 2 (by rfl) ⟨454974, by rfl⟩ : syracuseStep 1213265 = 909949) B909949
theorem B1213283 : Blo 806344 1213283 := bstep (se 1 (by rfl) ⟨909962, by rfl⟩ : syracuseStep 1213283 = 1819925) B1819925
theorem B1213313 : Blo 806344 1213313 := bstep (se 2 (by rfl) ⟨454992, by rfl⟩ : syracuseStep 1213313 = 909985) B909985
theorem B1868689 : Blo 806344 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1213331 : Blo 806344 1213331 := bstep (se 1 (by rfl) ⟨909998, by rfl⟩ : syracuseStep 1213331 = 1819997) B1819997
theorem B1213361 : Blo 806344 1213361 := bstep (se 2 (by rfl) ⟨455010, by rfl⟩ : syracuseStep 1213361 = 910021) B910021
theorem B11076533 : Blo 806344 11076533 := bstep (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) B1038425
theorem B1213379 : Blo 806344 1213379 := bstep (se 1 (by rfl) ⟨910034, by rfl⟩ : syracuseStep 1213379 = 1820069) B1820069
theorem B1213409 : Blo 806344 1213409 := bstep (se 2 (by rfl) ⟨455028, by rfl⟩ : syracuseStep 1213409 = 910057) B910057
theorem B1213427 : Blo 806344 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B1213457 : Blo 806344 1213457 := bstep (se 2 (by rfl) ⟨455046, by rfl⟩ : syracuseStep 1213457 = 910093) B910093
theorem B1213475 : Blo 806344 1213475 := bstep (se 1 (by rfl) ⟨910106, by rfl⟩ : syracuseStep 1213475 = 1820213) B1820213
theorem B1213505 : Blo 806344 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B1213523 : Blo 806344 1213523 := bstep (se 1 (by rfl) ⟨910142, by rfl⟩ : syracuseStep 1213523 = 1820285) B1820285
theorem B1213553 : Blo 806344 1213553 := bstep (se 2 (by rfl) ⟨455082, by rfl⟩ : syracuseStep 1213553 = 910165) B910165
theorem B1213571 : Blo 806344 1213571 := bstep (se 1 (by rfl) ⟨910178, by rfl⟩ : syracuseStep 1213571 = 1820357) B1820357
theorem B1213601 : Blo 806344 1213601 := bstep (se 2 (by rfl) ⟨455100, by rfl⟩ : syracuseStep 1213601 = 910201) B910201
theorem B1213619 : Blo 806344 1213619 := bstep (se 1 (by rfl) ⟨910214, by rfl⟩ : syracuseStep 1213619 = 1820429) B1820429
theorem B3278029 : Blo 806344 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B1213649 : Blo 806344 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B1213667 : Blo 806344 1213667 := bstep (se 1 (by rfl) ⟨910250, by rfl⟩ : syracuseStep 1213667 = 1820501) B1820501
theorem B1213697 : Blo 806344 1213697 := bstep (se 2 (by rfl) ⟨455136, by rfl⟩ : syracuseStep 1213697 = 910273) B910273
theorem B1213715 : Blo 806344 1213715 := bstep (se 1 (by rfl) ⟨910286, by rfl⟩ : syracuseStep 1213715 = 1820573) B1820573
theorem B1213745 : Blo 806344 1213745 := bstep (se 2 (by rfl) ⟨455154, by rfl⟩ : syracuseStep 1213745 = 910309) B910309
theorem B1213763 : Blo 806344 1213763 := bstep (se 1 (by rfl) ⟨910322, by rfl⟩ : syracuseStep 1213763 = 1820645) B1820645
theorem B1213793 : Blo 806344 1213793 := bstep (se 2 (by rfl) ⟨455172, by rfl⟩ : syracuseStep 1213793 = 910345) B910345
theorem B1213811 : Blo 806344 1213811 := bstep (se 1 (by rfl) ⟨910358, by rfl⟩ : syracuseStep 1213811 = 1820717) B1820717
theorem B1213841 : Blo 806344 1213841 := bstep (se 2 (by rfl) ⟨455190, by rfl⟩ : syracuseStep 1213841 = 910381) B910381
theorem B1213859 : Blo 806344 1213859 := bstep (se 1 (by rfl) ⟨910394, by rfl⟩ : syracuseStep 1213859 = 1820789) B1820789
theorem B2917795 : Blo 806344 2917795 := bstep (se 1 (by rfl) ⟨2188346, by rfl⟩ : syracuseStep 2917795 = 4376693) B4376693
theorem B1213889 : Blo 806344 1213889 := bstep (se 2 (by rfl) ⟨455208, by rfl⟩ : syracuseStep 1213889 = 910417) B910417
theorem B820675 : Blo 806344 820675 := bstep (se 1 (by rfl) ⟨615506, by rfl⟩ : syracuseStep 820675 = 1231013) B1231013
theorem B1213907 : Blo 806344 1213907 := bstep (se 1 (by rfl) ⟨910430, by rfl⟩ : syracuseStep 1213907 = 1820861) B1820861
theorem B11666915 : Blo 806344 11666915 := bstep (se 1 (by rfl) ⟨8750186, by rfl⟩ : syracuseStep 11666915 = 17500373) B17500373
theorem B1213937 : Blo 806344 1213937 := bstep (se 2 (by rfl) ⟨455226, by rfl⟩ : syracuseStep 1213937 = 910453) B910453
theorem B1213955 : Blo 806344 1213955 := bstep (se 1 (by rfl) ⟨910466, by rfl⟩ : syracuseStep 1213955 = 1820933) B1820933
theorem B1213985 : Blo 806344 1213985 := bstep (se 2 (by rfl) ⟨455244, by rfl⟩ : syracuseStep 1213985 = 910489) B910489
theorem B1214003 : Blo 806344 1214003 := bstep (se 1 (by rfl) ⟨910502, by rfl⟩ : syracuseStep 1214003 = 1821005) B1821005
theorem B2590289 : Blo 806344 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B1214033 : Blo 806344 1214033 := bstep (se 2 (by rfl) ⟨455262, by rfl⟩ : syracuseStep 1214033 = 910525) B910525
theorem B1214051 : Blo 806344 1214051 := bstep (se 1 (by rfl) ⟨910538, by rfl⟩ : syracuseStep 1214051 = 1821077) B1821077
theorem B1214081 : Blo 806344 1214081 := bstep (se 2 (by rfl) ⟨455280, by rfl⟩ : syracuseStep 1214081 = 910561) B910561
theorem B1214099 : Blo 806344 1214099 := bstep (se 1 (by rfl) ⟨910574, by rfl⟩ : syracuseStep 1214099 = 1821149) B1821149
theorem B1214129 : Blo 806344 1214129 := bstep (se 2 (by rfl) ⟨455298, by rfl⟩ : syracuseStep 1214129 = 910597) B910597
theorem B1214147 : Blo 806344 1214147 := bstep (se 1 (by rfl) ⟨910610, by rfl⟩ : syracuseStep 1214147 = 1821221) B1821221
theorem B1214177 : Blo 806344 1214177 := bstep (se 2 (by rfl) ⟨455316, by rfl⟩ : syracuseStep 1214177 = 910633) B910633
theorem B1214195 : Blo 806344 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B1214225 : Blo 806344 1214225 := bstep (se 2 (by rfl) ⟨455334, by rfl⟩ : syracuseStep 1214225 = 910669) B910669
theorem B1214243 : Blo 806344 1214243 := bstep (se 1 (by rfl) ⟨910682, by rfl⟩ : syracuseStep 1214243 = 1821365) B1821365
theorem B1214273 : Blo 806344 1214273 := bstep (se 2 (by rfl) ⟨455352, by rfl⟩ : syracuseStep 1214273 = 910705) B910705
theorem B1214291 : Blo 806344 1214291 := bstep (se 1 (by rfl) ⟨910718, by rfl⟩ : syracuseStep 1214291 = 1821437) B1821437
theorem B1214321 : Blo 806344 1214321 := bstep (se 2 (by rfl) ⟨455370, by rfl⟩ : syracuseStep 1214321 = 910741) B910741
theorem B1214339 : Blo 806344 1214339 := bstep (se 1 (by rfl) ⟨910754, by rfl⟩ : syracuseStep 1214339 = 1821509) B1821509
theorem B1214369 : Blo 806344 1214369 := bstep (se 2 (by rfl) ⟨455388, by rfl⟩ : syracuseStep 1214369 = 910777) B910777
theorem B1214387 : Blo 806344 1214387 := bstep (se 1 (by rfl) ⟨910790, by rfl⟩ : syracuseStep 1214387 = 1821581) B1821581
theorem B2328515 : Blo 806344 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B1214417 : Blo 806344 1214417 := bstep (se 2 (by rfl) ⟨455406, by rfl⟩ : syracuseStep 1214417 = 910813) B910813
theorem B1148899 : Blo 806344 1148899 := bstep (se 1 (by rfl) ⟨861674, by rfl⟩ : syracuseStep 1148899 = 1723349) B1723349
theorem B1214435 : Blo 806344 1214435 := bstep (se 1 (by rfl) ⟨910826, by rfl⟩ : syracuseStep 1214435 = 1821653) B1821653
theorem B1968113 : Blo 806344 1968113 := bstep (se 2 (by rfl) ⟨738042, by rfl⟩ : syracuseStep 1968113 = 1476085) B1476085
theorem B1214465 : Blo 806344 1214465 := bstep (se 2 (by rfl) ⟨455424, by rfl⟩ : syracuseStep 1214465 = 910849) B910849
theorem B1214483 : Blo 806344 1214483 := bstep (se 1 (by rfl) ⟨910862, by rfl⟩ : syracuseStep 1214483 = 1821725) B1821725
theorem B1214513 : Blo 806344 1214513 := bstep (se 2 (by rfl) ⟨455442, by rfl⟩ : syracuseStep 1214513 = 910885) B910885
theorem B1148995 : Blo 806344 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B1214531 : Blo 806344 1214531 := bstep (se 1 (by rfl) ⟨910898, by rfl⟩ : syracuseStep 1214531 = 1821797) B1821797
theorem B2721869 : Blo 806344 2721869 := bstep (se 3 (by rfl) ⟨510350, by rfl⟩ : syracuseStep 2721869 = 1020701) B1020701
theorem B1214561 : Blo 806344 1214561 := bstep (se 2 (by rfl) ⟨455460, by rfl⟩ : syracuseStep 1214561 = 910921) B910921
theorem B40962161 : Blo 806344 40962161 := bstep (se 2 (by rfl) ⟨15360810, by rfl⟩ : syracuseStep 40962161 = 30721621) B30721621
theorem B1214579 : Blo 806344 1214579 := bstep (se 1 (by rfl) ⟨910934, by rfl⟩ : syracuseStep 1214579 = 1821869) B1821869
theorem B2721923 : Blo 806344 2721923 := bstep (se 1 (by rfl) ⟨2041442, by rfl⟩ : syracuseStep 2721923 = 4082885) B4082885
theorem B1214609 : Blo 806344 1214609 := bstep (se 2 (by rfl) ⟨455478, by rfl⟩ : syracuseStep 1214609 = 910957) B910957
theorem B1214627 : Blo 806344 1214627 := bstep (se 1 (by rfl) ⟨910970, by rfl⟩ : syracuseStep 1214627 = 1821941) B1821941
theorem B1214657 : Blo 806344 1214657 := bstep (se 2 (by rfl) ⟨455496, by rfl⟩ : syracuseStep 1214657 = 910993) B910993
theorem B1214675 : Blo 806344 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B4098275 : Blo 806344 4098275 := bstep (se 1 (by rfl) ⟨3073706, by rfl⟩ : syracuseStep 4098275 = 6147413) B6147413
theorem B1214705 : Blo 806344 1214705 := bstep (se 2 (by rfl) ⟨455514, by rfl⟩ : syracuseStep 1214705 = 911029) B911029
theorem B1214723 : Blo 806344 1214723 := bstep (se 1 (by rfl) ⟨911042, by rfl⟩ : syracuseStep 1214723 = 1822085) B1822085
theorem B1214753 : Blo 806344 1214753 := bstep (se 2 (by rfl) ⟨455532, by rfl⟩ : syracuseStep 1214753 = 911065) B911065
theorem B1214771 : Blo 806344 1214771 := bstep (se 1 (by rfl) ⟨911078, by rfl⟩ : syracuseStep 1214771 = 1822157) B1822157
theorem B4360517 : Blo 806344 4360517 := bstep (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) B817597
theorem B1214801 : Blo 806344 1214801 := bstep (se 2 (by rfl) ⟨455550, by rfl⟩ : syracuseStep 1214801 = 911101) B911101
theorem B1214819 : Blo 806344 1214819 := bstep (se 1 (by rfl) ⟨911114, by rfl⟩ : syracuseStep 1214819 = 1822229) B1822229
theorem B1214849 : Blo 806344 1214849 := bstep (se 2 (by rfl) ⟨455568, by rfl⟩ : syracuseStep 1214849 = 911137) B911137
theorem B5540237 : Blo 806344 5540237 := bstep (se 3 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 5540237 = 2077589) B2077589
theorem B2722193 : Blo 806344 2722193 := bstep (se 2 (by rfl) ⟨1020822, by rfl⟩ : syracuseStep 2722193 = 2041645) B2041645
theorem B1214867 : Blo 806344 1214867 := bstep (se 1 (by rfl) ⟨911150, by rfl⟩ : syracuseStep 1214867 = 1822301) B1822301
theorem B1214897 : Blo 806344 1214897 := bstep (se 2 (by rfl) ⟨455586, by rfl⟩ : syracuseStep 1214897 = 911173) B911173
theorem B2296259 : Blo 806344 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B1214915 : Blo 806344 1214915 := bstep (se 1 (by rfl) ⟨911186, by rfl⟩ : syracuseStep 1214915 = 1822373) B1822373
theorem B2591185 : Blo 806344 2591185 := bstep (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) B1943389
theorem B1214945 : Blo 806344 1214945 := bstep (se 2 (by rfl) ⟨455604, by rfl⟩ : syracuseStep 1214945 = 911209) B911209
theorem B1214963 : Blo 806344 1214963 := bstep (se 1 (by rfl) ⟨911222, by rfl⟩ : syracuseStep 1214963 = 1822445) B1822445
theorem B1214993 : Blo 806344 1214993 := bstep (se 2 (by rfl) ⟨455622, by rfl⟩ : syracuseStep 1214993 = 911245) B911245
theorem B1215011 : Blo 806344 1215011 := bstep (se 1 (by rfl) ⟨911258, by rfl⟩ : syracuseStep 1215011 = 1822517) B1822517
theorem B1149491 : Blo 806344 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B1215041 : Blo 806344 1215041 := bstep (se 2 (by rfl) ⟨455640, by rfl⟩ : syracuseStep 1215041 = 911281) B911281
theorem B5540429 : Blo 806344 5540429 := bstep (se 3 (by rfl) ⟨1038830, by rfl⟩ : syracuseStep 5540429 = 2077661) B2077661
theorem B1215059 : Blo 806344 1215059 := bstep (se 1 (by rfl) ⟨911294, by rfl⟩ : syracuseStep 1215059 = 1822589) B1822589
theorem B1215089 : Blo 806344 1215089 := bstep (se 2 (by rfl) ⟨455658, by rfl⟩ : syracuseStep 1215089 = 911317) B911317
theorem B1215107 : Blo 806344 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B1215137 : Blo 806344 1215137 := bstep (se 2 (by rfl) ⟨455676, by rfl⟩ : syracuseStep 1215137 = 911353) B911353
theorem B1215155 : Blo 806344 1215155 := bstep (se 1 (by rfl) ⟨911366, by rfl⟩ : syracuseStep 1215155 = 1822733) B1822733
theorem B1215185 : Blo 806344 1215185 := bstep (se 2 (by rfl) ⟨455694, by rfl⟩ : syracuseStep 1215185 = 911389) B911389
theorem B6130403 : Blo 806344 6130403 := bstep (se 1 (by rfl) ⟨4597802, by rfl⟩ : syracuseStep 6130403 = 9195605) B9195605
theorem B1215203 : Blo 806344 1215203 := bstep (se 1 (by rfl) ⟨911402, by rfl⟩ : syracuseStep 1215203 = 1822805) B1822805
theorem B1215233 : Blo 806344 1215233 := bstep (se 2 (by rfl) ⟨455712, by rfl⟩ : syracuseStep 1215233 = 911425) B911425
theorem B4983557 : Blo 806344 4983557 := bstep (se 4 (by rfl) ⟨467208, by rfl⟩ : syracuseStep 4983557 = 934417) B934417
theorem B1215251 : Blo 806344 1215251 := bstep (se 1 (by rfl) ⟨911438, by rfl⟩ : syracuseStep 1215251 = 1822877) B1822877
theorem B1215281 : Blo 806344 1215281 := bstep (se 2 (by rfl) ⟨455730, by rfl⟩ : syracuseStep 1215281 = 911461) B911461
theorem B1215299 : Blo 806344 1215299 := bstep (se 1 (by rfl) ⟨911474, by rfl⟩ : syracuseStep 1215299 = 1822949) B1822949
theorem B1215329 : Blo 806344 1215329 := bstep (se 2 (by rfl) ⟨455748, by rfl⟩ : syracuseStep 1215329 = 911497) B911497
theorem B1215347 : Blo 806344 1215347 := bstep (se 1 (by rfl) ⟨911510, by rfl⟩ : syracuseStep 1215347 = 1823021) B1823021
theorem B1215377 : Blo 806344 1215377 := bstep (se 2 (by rfl) ⟨455766, by rfl⟩ : syracuseStep 1215377 = 911533) B911533
theorem B1215395 : Blo 806344 1215395 := bstep (se 1 (by rfl) ⟨911546, by rfl⟩ : syracuseStep 1215395 = 1823093) B1823093
theorem B2722733 : Blo 806344 2722733 := bstep (se 3 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 2722733 = 1021025) B1021025
theorem B1215425 : Blo 806344 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B1215443 : Blo 806344 1215443 := bstep (se 1 (by rfl) ⟨911582, by rfl⟩ : syracuseStep 1215443 = 1823165) B1823165
theorem B2722787 : Blo 806344 2722787 := bstep (se 1 (by rfl) ⟨2042090, by rfl⟩ : syracuseStep 2722787 = 4084181) B4084181
theorem B1215473 : Blo 806344 1215473 := bstep (se 2 (by rfl) ⟨455802, by rfl⟩ : syracuseStep 1215473 = 911605) B911605
theorem B1215491 : Blo 806344 1215491 := bstep (se 1 (by rfl) ⟨911618, by rfl⟩ : syracuseStep 1215491 = 1823237) B1823237
theorem B4099085 : Blo 806344 4099085 := bstep (se 3 (by rfl) ⟨768578, by rfl⟩ : syracuseStep 4099085 = 1537157) B1537157
theorem B1150129 : Blo 806344 1150129 := bstep (se 2 (by rfl) ⟨431298, by rfl⟩ : syracuseStep 1150129 = 862597) B862597
theorem B2297069 : Blo 806344 2297069 := bstep (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) B861401
theorem B2723057 : Blo 806344 2723057 := bstep (se 2 (by rfl) ⟨1021146, by rfl⟩ : syracuseStep 2723057 = 2042293) B2042293
theorem B920851 : Blo 806344 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B2297261 : Blo 806344 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B1150465 : Blo 806344 1150465 := bstep (se 2 (by rfl) ⟨431424, by rfl⟩ : syracuseStep 1150465 = 862849) B862849
theorem B2723597 : Blo 806344 2723597 := bstep (se 3 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 2723597 = 1021349) B1021349
theorem B2723651 : Blo 806344 2723651 := bstep (se 1 (by rfl) ⟨2042738, by rfl⟩ : syracuseStep 2723651 = 4085477) B4085477
theorem B921475 : Blo 806344 921475 := bstep (se 1 (by rfl) ⟨691106, by rfl⟩ : syracuseStep 921475 = 1382213) B1382213
theorem B2920333 : Blo 806344 2920333 := bstep (se 3 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 2920333 = 1095125) B1095125
theorem B1314721 : Blo 806344 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B8851427 : Blo 806344 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B2592749 : Blo 806344 2592749 := bstep (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) B972281
theorem B2723921 : Blo 806344 2723921 := bstep (se 2 (by rfl) ⟨1021470, by rfl⟩ : syracuseStep 2723921 = 2042941) B2042941
theorem B1151057 : Blo 806344 1151057 := bstep (se 2 (by rfl) ⟨431646, by rfl⟩ : syracuseStep 1151057 = 863293) B863293
theorem B11079821 : Blo 806344 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B6918371 : Blo 806344 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B2298253 : Blo 806344 2298253 := bstep (se 3 (by rfl) ⟨430922, by rfl⟩ : syracuseStep 2298253 = 861845) B861845
theorem B14913989 : Blo 806344 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B1151587 : Blo 806344 1151587 := bstep (se 1 (by rfl) ⟨863690, by rfl⟩ : syracuseStep 1151587 = 1727381) B1727381
theorem B2724461 : Blo 806344 2724461 := bstep (se 3 (by rfl) ⟨510836, by rfl⟩ : syracuseStep 2724461 = 1021673) B1021673
theorem B2724515 : Blo 806344 2724515 := bstep (se 1 (by rfl) ⟨2043386, by rfl⟩ : syracuseStep 2724515 = 4086773) B4086773
theorem B1020595 : Blo 806344 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B3445517 : Blo 806344 3445517 := bstep (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) B1292069
theorem B1020691 : Blo 806344 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B2724785 : Blo 806344 2724785 := bstep (se 2 (by rfl) ⟨1021794, by rfl⟩ : syracuseStep 2724785 = 2043589) B2043589
theorem B1151923 : Blo 806344 1151923 := bstep (se 1 (by rfl) ⟨863942, by rfl⟩ : syracuseStep 1151923 = 1727885) B1727885
theorem B2528365 : Blo 806344 2528365 := bstep (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) B948137
theorem B3314915 : Blo 806344 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B1021187 : Blo 806344 1021187 := bstep (se 1 (by rfl) ⟨765890, by rfl⟩ : syracuseStep 1021187 = 1531781) B1531781
theorem B2463011 : Blo 806344 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B2725325 : Blo 806344 2725325 := bstep (se 3 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 2725325 = 1021997) B1021997
theorem B1152481 : Blo 806344 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B2725379 : Blo 806344 2725379 := bstep (se 1 (by rfl) ⟨2044034, by rfl⟩ : syracuseStep 2725379 = 4088069) B4088069
theorem B1152515 : Blo 806344 1152515 := bstep (se 1 (by rfl) ⟨864386, by rfl⟩ : syracuseStep 1152515 = 1728773) B1728773
theorem B4593293 : Blo 806344 4593293 := bstep (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) B1722485
theorem B2725649 : Blo 806344 2725649 := bstep (se 2 (by rfl) ⟨1022118, by rfl⟩ : syracuseStep 2725649 = 2044237) B2044237
theorem B4102001 : Blo 806344 4102001 := bstep (se 2 (by rfl) ⟨1538250, by rfl⟩ : syracuseStep 4102001 = 3076501) B3076501
theorem B1021891 : Blo 806344 1021891 := bstep (se 1 (by rfl) ⟨766418, by rfl⟩ : syracuseStep 1021891 = 1532837) B1532837
theorem B1939459 : Blo 806344 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B1021987 : Blo 806344 1021987 := bstep (se 1 (by rfl) ⟨766490, by rfl⟩ : syracuseStep 1021987 = 1532981) B1532981
theorem B3446833 : Blo 806344 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B1153073 : Blo 806344 1153073 := bstep (se 2 (by rfl) ⟨432402, by rfl⟩ : syracuseStep 1153073 = 864805) B864805
theorem B2299985 : Blo 806344 2299985 := bstep (se 2 (by rfl) ⟨862494, by rfl⟩ : syracuseStep 2299985 = 1724989) B1724989
theorem B1153153 : Blo 806344 1153153 := bstep (se 2 (by rfl) ⟨432432, by rfl⟩ : syracuseStep 1153153 = 864865) B864865
theorem B2300177 : Blo 806344 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B2726189 : Blo 806344 2726189 := bstep (se 3 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 2726189 = 1022321) B1022321
theorem B2726243 : Blo 806344 2726243 := bstep (se 1 (by rfl) ⟨2044682, by rfl⟩ : syracuseStep 2726243 = 4089365) B4089365
theorem B2595235 : Blo 806344 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B2365901 : Blo 806344 2365901 := bstep (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) B887213
theorem B1022483 : Blo 806344 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B2595377 : Blo 806344 2595377 := bstep (se 2 (by rfl) ⟨973266, by rfl⟩ : syracuseStep 2595377 = 1946533) B1946533
theorem B2726513 : Blo 806344 2726513 := bstep (se 2 (by rfl) ⟨1022442, by rfl⟩ : syracuseStep 2726513 = 2044885) B2044885
theorem B2595491 : Blo 806344 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B5184269 : Blo 806344 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B5839685 : Blo 806344 5839685 := bstep (se 4 (by rfl) ⟨547470, by rfl⟩ : syracuseStep 5839685 = 1094941) B1094941
theorem B2530381 : Blo 806344 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B2727053 : Blo 806344 2727053 := bstep (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) B1022645
theorem B2727107 : Blo 806344 2727107 := bstep (se 1 (by rfl) ⟨2045330, by rfl⟩ : syracuseStep 2727107 = 4090661) B4090661
theorem B1940689 : Blo 806344 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B1023187 : Blo 806344 1023187 := bstep (se 1 (by rfl) ⟨767390, by rfl⟩ : syracuseStep 1023187 = 1534781) B1534781
theorem B2301169 : Blo 806344 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B1023283 : Blo 806344 1023283 := bstep (se 1 (by rfl) ⟨767462, by rfl⟩ : syracuseStep 1023283 = 1534925) B1534925
theorem B1580419 : Blo 806344 1580419 := bstep (se 1 (by rfl) ⟨1185314, by rfl⟩ : syracuseStep 1580419 = 2370629) B2370629
theorem B2727377 : Blo 806344 2727377 := bstep (se 2 (by rfl) ⟨1022766, by rfl⟩ : syracuseStep 2727377 = 2045533) B2045533
theorem B2301443 : Blo 806344 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B2301635 : Blo 806344 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B1023779 : Blo 806344 1023779 := bstep (se 1 (by rfl) ⟨767834, by rfl⟩ : syracuseStep 1023779 = 1535669) B1535669
theorem B4595525 : Blo 806344 4595525 := bstep (se 4 (by rfl) ⟨430830, by rfl⟩ : syracuseStep 4595525 = 861661) B861661
theorem B6922097 : Blo 806344 6922097 := bstep (se 2 (by rfl) ⟨2595786, by rfl⟩ : syracuseStep 6922097 = 5191573) B5191573
theorem B6135749 : Blo 806344 6135749 := bstep (se 4 (by rfl) ⟨575226, by rfl⟩ : syracuseStep 6135749 = 1150453) B1150453
theorem B2727917 : Blo 806344 2727917 := bstep (se 3 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 2727917 = 1022969) B1022969
theorem B2727971 : Blo 806344 2727971 := bstep (se 1 (by rfl) ⟨2045978, by rfl⟩ : syracuseStep 2727971 = 4091957) B4091957
theorem B1384705 : Blo 806344 1384705 := bstep (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) B1038529
theorem B2728241 : Blo 806344 2728241 := bstep (se 2 (by rfl) ⟨1023090, by rfl⟩ : syracuseStep 2728241 = 2046181) B2046181
theorem B1024483 : Blo 806344 1024483 := bstep (se 1 (by rfl) ⟨768362, by rfl⟩ : syracuseStep 1024483 = 1536725) B1536725
theorem B2302445 : Blo 806344 2302445 := bstep (se 3 (by rfl) ⟨431708, by rfl⟩ : syracuseStep 2302445 = 863417) B863417
theorem B4596209 : Blo 806344 4596209 := bstep (se 2 (by rfl) ⟨1723578, by rfl⟩ : syracuseStep 4596209 = 3447157) B3447157
theorem B1090081 : Blo 806344 1090081 := bstep (se 2 (by rfl) ⟨408780, by rfl⟩ : syracuseStep 1090081 = 817561) B817561
theorem B1516099 : Blo 806344 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B1024579 : Blo 806344 1024579 := bstep (se 1 (by rfl) ⟨768434, by rfl⟩ : syracuseStep 1024579 = 1536869) B1536869
theorem B5972549 : Blo 806344 5972549 := bstep (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) B1119853
theorem B4366961 : Blo 806344 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B2302627 : Blo 806344 2302627 := bstep (se 1 (by rfl) ⟨1726970, by rfl⟩ : syracuseStep 2302627 = 3453941) B3453941
theorem B5907269 : Blo 806344 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B2728781 : Blo 806344 2728781 := bstep (se 3 (by rfl) ⟨511646, by rfl⟩ : syracuseStep 2728781 = 1023293) B1023293
theorem B2728835 : Blo 806344 2728835 := bstep (se 1 (by rfl) ⟨2046626, by rfl⟩ : syracuseStep 2728835 = 4093253) B4093253
theorem B4138019 : Blo 806344 4138019 := bstep (se 1 (by rfl) ⟨3103514, by rfl⟩ : syracuseStep 4138019 = 6207029) B6207029
theorem B3449891 : Blo 806344 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B1025075 : Blo 806344 1025075 := bstep (se 1 (by rfl) ⟨768806, by rfl⟩ : syracuseStep 1025075 = 1537613) B1537613
theorem B861251 : Blo 806344 861251 := bstep (se 1 (by rfl) ⟨645938, by rfl⟩ : syracuseStep 861251 = 1291877) B1291877
theorem B3941453 : Blo 806344 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B2303117 : Blo 806344 2303117 := bstep (se 3 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 2303117 = 863669) B863669
theorem B2729105 : Blo 806344 2729105 := bstep (se 2 (by rfl) ⟨1023414, by rfl⟩ : syracuseStep 2729105 = 2046829) B2046829
theorem B1090865 : Blo 806344 1090865 := bstep (se 2 (by rfl) ⟨409074, by rfl⟩ : syracuseStep 1090865 = 818149) B818149
theorem B1844849 : Blo 806344 1844849 := bstep (se 2 (by rfl) ⟨691818, by rfl⟩ : syracuseStep 1844849 = 1383637) B1383637
theorem B1386113 : Blo 806344 1386113 := bstep (se 2 (by rfl) ⟨519792, by rfl⟩ : syracuseStep 1386113 = 1039585) B1039585
theorem B2729645 : Blo 806344 2729645 := bstep (se 3 (by rfl) ⟨511808, by rfl⟩ : syracuseStep 2729645 = 1023617) B1023617
theorem B2729699 : Blo 806344 2729699 := bstep (se 1 (by rfl) ⟨2047274, by rfl⟩ : syracuseStep 2729699 = 4094549) B4094549
theorem B862003 : Blo 806344 862003 := bstep (se 1 (by rfl) ⟨646502, by rfl⟩ : syracuseStep 862003 = 1293005) B1293005
theorem B4597667 : Blo 806344 4597667 := bstep (se 1 (by rfl) ⟨3448250, by rfl⟩ : syracuseStep 4597667 = 6896501) B6896501
theorem B12593123 : Blo 806344 12593123 := bstep (se 1 (by rfl) ⟨9444842, by rfl⟩ : syracuseStep 12593123 = 18889685) B18889685
theorem B2729969 : Blo 806344 2729969 := bstep (se 2 (by rfl) ⟨1023738, by rfl⟩ : syracuseStep 2729969 = 2047477) B2047477
theorem B1845233 : Blo 806344 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B1845251 : Blo 806344 1845251 := bstep (se 1 (by rfl) ⟨1383938, by rfl⟩ : syracuseStep 1845251 = 2767877) B2767877
theorem B20719637 : Blo 806344 20719637 := bstep (se 6 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 20719637 = 971233) B971233
theorem B862259 : Blo 806344 862259 := bstep (se 1 (by rfl) ⟨646694, by rfl⟩ : syracuseStep 862259 = 1293389) B1293389
theorem B2041969 : Blo 806344 2041969 := bstep (se 2 (by rfl) ⟨765738, by rfl⟩ : syracuseStep 2041969 = 1531477) B1531477
theorem B3877091 : Blo 806344 3877091 := bstep (se 1 (by rfl) ⟨2907818, by rfl⟩ : syracuseStep 3877091 = 5815637) B5815637
theorem B2304301 : Blo 806344 2304301 := bstep (se 3 (by rfl) ⟨432056, by rfl⟩ : syracuseStep 2304301 = 864113) B864113
theorem B2074961 : Blo 806344 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B2042243 : Blo 806344 2042243 := bstep (se 1 (by rfl) ⟨1531682, by rfl⟩ : syracuseStep 2042243 = 3063365) B3063365
theorem B2730509 : Blo 806344 2730509 := bstep (se 3 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 2730509 = 1023941) B1023941
theorem B2042435 : Blo 806344 2042435 := bstep (se 1 (by rfl) ⟨1531826, by rfl⟩ : syracuseStep 2042435 = 3063653) B3063653
theorem B2730563 : Blo 806344 2730563 := bstep (se 1 (by rfl) ⟨2047922, by rfl⟩ : syracuseStep 2730563 = 4095845) B4095845
theorem B2075395 : Blo 806344 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B5253893 : Blo 806344 5253893 := bstep (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) B985105
theorem B863011 : Blo 806344 863011 := bstep (se 1 (by rfl) ⟨647258, by rfl⟩ : syracuseStep 863011 = 1294517) B1294517
theorem B7777093 : Blo 806344 7777093 := bstep (se 4 (by rfl) ⟨729102, by rfl⟩ : syracuseStep 7777093 = 1458205) B1458205
theorem B2730833 : Blo 806344 2730833 := bstep (se 2 (by rfl) ⟨1024062, by rfl⟩ : syracuseStep 2730833 = 2048125) B2048125
theorem B1092595 : Blo 806344 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B3877901 : Blo 806344 3877901 := bstep (se 3 (by rfl) ⟨727106, by rfl⟩ : syracuseStep 3877901 = 1454213) B1454213
theorem B2305361 : Blo 806344 2305361 := bstep (se 2 (by rfl) ⟨864510, by rfl⟩ : syracuseStep 2305361 = 1729021) B1729021
theorem B2731373 : Blo 806344 2731373 := bstep (se 3 (by rfl) ⟨512132, by rfl⟩ : syracuseStep 2731373 = 1024265) B1024265
theorem B2731427 : Blo 806344 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B2043377 : Blo 806344 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B4435441 : Blo 806344 4435441 := bstep (se 2 (by rfl) ⟨1663290, by rfl⟩ : syracuseStep 4435441 = 3326581) B3326581
theorem B4926989 : Blo 806344 4926989 := bstep (se 3 (by rfl) ⟨923810, by rfl⟩ : syracuseStep 4926989 = 1847621) B1847621
theorem B2043427 : Blo 806344 2043427 := bstep (se 1 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 2043427 = 3065141) B3065141
theorem B1846819 : Blo 806344 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B2043569 : Blo 806344 2043569 := bstep (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) B1532677
theorem B2731697 : Blo 806344 2731697 := bstep (se 2 (by rfl) ⟨1024386, by rfl⟩ : syracuseStep 2731697 = 2048773) B2048773
theorem B3878705 : Blo 806344 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B1814417 : Blo 806344 1814417 := bstep (se 2 (by rfl) ⟨680406, by rfl⟩ : syracuseStep 1814417 = 1360813) B1360813
theorem B1814435 : Blo 806344 1814435 := bstep (se 1 (by rfl) ⟨1360826, by rfl⟩ : syracuseStep 1814435 = 2721653) B2721653
theorem B2306033 : Blo 806344 2306033 := bstep (se 2 (by rfl) ⟨864762, by rfl⟩ : syracuseStep 2306033 = 1729525) B1729525
theorem B864275 : Blo 806344 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B1814705 : Blo 806344 1814705 := bstep (se 2 (by rfl) ⟨680514, by rfl⟩ : syracuseStep 1814705 = 1361029) B1361029
theorem B1814723 : Blo 806344 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B2732237 : Blo 806344 2732237 := bstep (se 3 (by rfl) ⟨512294, by rfl⟩ : syracuseStep 2732237 = 1024589) B1024589
theorem B2732291 : Blo 806344 2732291 := bstep (se 1 (by rfl) ⟨2049218, by rfl⟩ : syracuseStep 2732291 = 4098437) B4098437
theorem B5189957 : Blo 806344 5189957 := bstep (se 4 (by rfl) ⟨486558, by rfl⟩ : syracuseStep 5189957 = 973117) B973117
theorem B1814993 : Blo 806344 1814993 := bstep (se 2 (by rfl) ⟨680622, by rfl⟩ : syracuseStep 1814993 = 1361245) B1361245
theorem B1815011 : Blo 806344 1815011 := bstep (se 1 (by rfl) ⟨1361258, by rfl⟩ : syracuseStep 1815011 = 2722517) B2722517
theorem B2732561 : Blo 806344 2732561 := bstep (se 2 (by rfl) ⟨1024710, by rfl⟩ : syracuseStep 2732561 = 2049421) B2049421
theorem B1946225 : Blo 806344 1946225 := bstep (se 2 (by rfl) ⟨729834, by rfl⟩ : syracuseStep 1946225 = 1459669) B1459669
theorem B2044561 : Blo 806344 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B1815281 : Blo 806344 1815281 := bstep (se 2 (by rfl) ⟨680730, by rfl⟩ : syracuseStep 1815281 = 1361461) B1361461
theorem B1815299 : Blo 806344 1815299 := bstep (se 1 (by rfl) ⟨1361474, by rfl⟩ : syracuseStep 1815299 = 2722949) B2722949
theorem B865027 : Blo 806344 865027 := bstep (se 1 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 865027 = 1297541) B1297541
theorem B2306819 : Blo 806344 2306819 := bstep (se 1 (by rfl) ⟨1730114, by rfl⟩ : syracuseStep 2306819 = 3460229) B3460229
theorem B2044835 : Blo 806344 2044835 := bstep (se 1 (by rfl) ⟨1533626, by rfl⟩ : syracuseStep 2044835 = 3067253) B3067253
theorem B1094627 : Blo 806344 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B1815569 : Blo 806344 1815569 := bstep (se 2 (by rfl) ⟨680838, by rfl⟩ : syracuseStep 1815569 = 1361677) B1361677
theorem B1815587 : Blo 806344 1815587 := bstep (se 1 (by rfl) ⟨1361690, by rfl⟩ : syracuseStep 1815587 = 2723381) B2723381
theorem B2733101 : Blo 806344 2733101 := bstep (se 3 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 2733101 = 1024913) B1024913
theorem B4600901 : Blo 806344 4600901 := bstep (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) B862669
theorem B2307149 : Blo 806344 2307149 := bstep (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) B865181
theorem B2045027 : Blo 806344 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B2733155 : Blo 806344 2733155 := bstep (se 1 (by rfl) ⟨2049866, by rfl⟩ : syracuseStep 2733155 = 4099733) B4099733
theorem B1455235 : Blo 806344 1455235 := bstep (se 1 (by rfl) ⟨1091426, by rfl⟩ : syracuseStep 1455235 = 2182853) B2182853
theorem B3454093 : Blo 806344 3454093 := bstep (se 3 (by rfl) ⟨647642, by rfl⟩ : syracuseStep 3454093 = 1295285) B1295285
theorem B2307217 : Blo 806344 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B1684739 : Blo 806344 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B19674389 : Blo 806344 19674389 := bstep (se 6 (by rfl) ⟨461118, by rfl⟩ : syracuseStep 19674389 = 922237) B922237
theorem B1815857 : Blo 806344 1815857 := bstep (se 2 (by rfl) ⟨680946, by rfl⟩ : syracuseStep 1815857 = 1361893) B1361893
theorem B1815875 : Blo 806344 1815875 := bstep (se 1 (by rfl) ⟨1361906, by rfl⟩ : syracuseStep 1815875 = 2723813) B2723813
theorem B2733425 : Blo 806344 2733425 := bstep (se 2 (by rfl) ⟨1025034, by rfl⟩ : syracuseStep 2733425 = 2050069) B2050069
theorem B2307491 : Blo 806344 2307491 := bstep (se 1 (by rfl) ⟨1730618, by rfl⟩ : syracuseStep 2307491 = 3461237) B3461237
theorem B8304113 : Blo 806344 8304113 := bstep (se 2 (by rfl) ⟨3114042, by rfl⟩ : syracuseStep 8304113 = 6228085) B6228085
theorem B4601357 : Blo 806344 4601357 := bstep (se 3 (by rfl) ⟨862754, by rfl⟩ : syracuseStep 4601357 = 1725509) B1725509
theorem B1816145 : Blo 806344 1816145 := bstep (se 2 (by rfl) ⟨681054, by rfl⟩ : syracuseStep 1816145 = 1362109) B1362109
theorem B1816163 : Blo 806344 1816163 := bstep (se 1 (by rfl) ⟨1362122, by rfl⟩ : syracuseStep 1816163 = 2724245) B2724245
theorem B6141581 : Blo 806344 6141581 := bstep (se 3 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 6141581 = 2303093) B2303093
theorem B3880781 : Blo 806344 3880781 := bstep (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) B1455293
theorem B1816433 : Blo 806344 1816433 := bstep (se 2 (by rfl) ⟨681162, by rfl⟩ : syracuseStep 1816433 = 1362325) B1362325
theorem B1455985 : Blo 806344 1455985 := bstep (se 2 (by rfl) ⟨545994, by rfl⟩ : syracuseStep 1455985 = 1091989) B1091989
theorem B1816451 : Blo 806344 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B2733965 : Blo 806344 2733965 := bstep (se 3 (by rfl) ⟨512618, by rfl⟩ : syracuseStep 2733965 = 1025237) B1025237
theorem B2734019 : Blo 806344 2734019 := bstep (se 1 (by rfl) ⟨2050514, by rfl⟩ : syracuseStep 2734019 = 4101029) B4101029
theorem B3061709 : Blo 806344 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B2045969 : Blo 806344 2045969 := bstep (se 2 (by rfl) ⟨767238, by rfl⟩ : syracuseStep 2045969 = 1534477) B1534477
theorem B2046019 : Blo 806344 2046019 := bstep (se 1 (by rfl) ⟨1534514, by rfl⟩ : syracuseStep 2046019 = 3069029) B3069029
theorem B6993989 : Blo 806344 6993989 := bstep (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) B1311373
theorem B1816721 : Blo 806344 1816721 := bstep (se 2 (by rfl) ⟨681270, by rfl⟩ : syracuseStep 1816721 = 1362541) B1362541
theorem B1816739 : Blo 806344 1816739 := bstep (se 1 (by rfl) ⟨1362554, by rfl⟩ : syracuseStep 1816739 = 2725109) B2725109
theorem B2046161 : Blo 806344 2046161 := bstep (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) B1534621
theorem B2734289 : Blo 806344 2734289 := bstep (se 2 (by rfl) ⟨1025358, by rfl⟩ : syracuseStep 2734289 = 2050717) B2050717
theorem B9189773 : Blo 806344 9189773 := bstep (se 3 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 9189773 = 3446165) B3446165
theorem B1817009 : Blo 806344 1817009 := bstep (se 2 (by rfl) ⟨681378, by rfl⟩ : syracuseStep 1817009 = 1362757) B1362757
theorem B1817027 : Blo 806344 1817027 := bstep (se 1 (by rfl) ⟨1362770, by rfl⟩ : syracuseStep 1817027 = 2725541) B2725541
theorem B1292851 : Blo 806344 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B1817297 : Blo 806344 1817297 := bstep (se 2 (by rfl) ⟨681486, by rfl⟩ : syracuseStep 1817297 = 1362973) B1362973
theorem B1817315 : Blo 806344 1817315 := bstep (se 1 (by rfl) ⟨1362986, by rfl⟩ : syracuseStep 1817315 = 2725973) B2725973
theorem B2734829 : Blo 806344 2734829 := bstep (se 3 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 2734829 = 1025561) B1025561
theorem B2734883 : Blo 806344 2734883 := bstep (se 1 (by rfl) ⟨2051162, by rfl⟩ : syracuseStep 2734883 = 4102325) B4102325
theorem B1817585 : Blo 806344 1817585 := bstep (se 2 (by rfl) ⟨681594, by rfl⟩ : syracuseStep 1817585 = 1363189) B1363189
theorem B1817603 : Blo 806344 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B1227953 : Blo 806344 1227953 := bstep (se 2 (by rfl) ⟨460482, by rfl⟩ : syracuseStep 1227953 = 920965) B920965
theorem B2047153 : Blo 806344 2047153 := bstep (se 2 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 2047153 = 1535365) B1535365
theorem B6208753 : Blo 806344 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B1817873 : Blo 806344 1817873 := bstep (se 2 (by rfl) ⟨681702, by rfl⟩ : syracuseStep 1817873 = 1363405) B1363405
theorem B1817891 : Blo 806344 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B2047427 : Blo 806344 2047427 := bstep (se 1 (by rfl) ⟨1535570, by rfl⟩ : syracuseStep 2047427 = 3071141) B3071141
theorem B1818161 : Blo 806344 1818161 := bstep (se 2 (by rfl) ⟨681810, by rfl⟩ : syracuseStep 1818161 = 1363621) B1363621
theorem B1818179 : Blo 806344 1818179 := bstep (se 1 (by rfl) ⟨1363634, by rfl⟩ : syracuseStep 1818179 = 2727269) B2727269
theorem B6897251 : Blo 806344 6897251 := bstep (se 1 (by rfl) ⟨5172938, by rfl⟩ : syracuseStep 6897251 = 10345877) B10345877
theorem B2047619 : Blo 806344 2047619 := bstep (se 1 (by rfl) ⟨1535714, by rfl⟩ : syracuseStep 2047619 = 3071429) B3071429
theorem B1556131 : Blo 806344 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B1261363 : Blo 806344 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B1818449 : Blo 806344 1818449 := bstep (se 2 (by rfl) ⟨681918, by rfl⟩ : syracuseStep 1818449 = 1363837) B1363837
theorem B1818467 : Blo 806344 1818467 := bstep (se 1 (by rfl) ⟨1363850, by rfl⟩ : syracuseStep 1818467 = 2727701) B2727701
theorem B1752931 : Blo 806344 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B4440005 : Blo 806344 4440005 := bstep (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) B832501
theorem B1294337 : Blo 806344 1294337 := bstep (se 2 (by rfl) ⟨485376, by rfl⟩ : syracuseStep 1294337 = 970753) B970753
theorem B11190325 : Blo 806344 11190325 := bstep (se 5 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 11190325 = 1049093) B1049093
theorem B1818737 : Blo 806344 1818737 := bstep (se 2 (by rfl) ⟨682026, by rfl⟩ : syracuseStep 1818737 = 1364053) B1364053
theorem B1294465 : Blo 806344 1294465 := bstep (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) B970849
theorem B1818755 : Blo 806344 1818755 := bstep (se 1 (by rfl) ⟨1364066, by rfl⟩ : syracuseStep 1818755 = 2728133) B2728133
theorem B4604273 : Blo 806344 4604273 := bstep (se 2 (by rfl) ⟨1726602, by rfl⟩ : syracuseStep 4604273 = 3453205) B3453205
theorem B1819025 : Blo 806344 1819025 := bstep (se 2 (by rfl) ⟨682134, by rfl⟩ : syracuseStep 1819025 = 1364269) B1364269
theorem B1819043 : Blo 806344 1819043 := bstep (se 1 (by rfl) ⟨1364282, by rfl⟩ : syracuseStep 1819043 = 2728565) B2728565
theorem B6144497 : Blo 806344 6144497 := bstep (se 2 (by rfl) ⟨2304186, by rfl⟩ : syracuseStep 6144497 = 4608373) B4608373
theorem B2048561 : Blo 806344 2048561 := bstep (se 2 (by rfl) ⟨768210, by rfl⟩ : syracuseStep 2048561 = 1536421) B1536421
theorem B2048611 : Blo 806344 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B1819313 : Blo 806344 1819313 := bstep (se 2 (by rfl) ⟨682242, by rfl⟩ : syracuseStep 1819313 = 1364485) B1364485
theorem B1819331 : Blo 806344 1819331 := bstep (se 1 (by rfl) ⟨1364498, by rfl⟩ : syracuseStep 1819331 = 2728997) B2728997
theorem B2048753 : Blo 806344 2048753 := bstep (se 2 (by rfl) ⟨768282, by rfl⟩ : syracuseStep 2048753 = 1536565) B1536565
theorem B3064625 : Blo 806344 3064625 := bstep (se 2 (by rfl) ⟨1149234, by rfl⟩ : syracuseStep 3064625 = 2298469) B2298469
theorem B1360739 : Blo 806344 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B8733581 : Blo 806344 8733581 := bstep (se 3 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 8733581 = 3275093) B3275093
theorem B1819601 : Blo 806344 1819601 := bstep (se 2 (by rfl) ⟨682350, by rfl⟩ : syracuseStep 1819601 = 1364701) B1364701
theorem B1360867 : Blo 806344 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B1819619 : Blo 806344 1819619 := bstep (se 1 (by rfl) ⟨1364714, by rfl⟩ : syracuseStep 1819619 = 2729429) B2729429
theorem B3687437 : Blo 806344 3687437 := bstep (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) B1382789
theorem B1361009 : Blo 806344 1361009 := bstep (se 2 (by rfl) ⟨510378, by rfl⟩ : syracuseStep 1361009 = 1020757) B1020757
theorem B5817541 : Blo 806344 5817541 := bstep (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) B1090789
theorem B1361137 : Blo 806344 1361137 := bstep (se 2 (by rfl) ⟨510426, by rfl⟩ : syracuseStep 1361137 = 1020853) B1020853
theorem B9192689 : Blo 806344 9192689 := bstep (se 2 (by rfl) ⟨3447258, by rfl⟩ : syracuseStep 9192689 = 6894517) B6894517
theorem B1819889 : Blo 806344 1819889 := bstep (se 2 (by rfl) ⟨682458, by rfl⟩ : syracuseStep 1819889 = 1364917) B1364917
theorem B1819907 : Blo 806344 1819907 := bstep (se 1 (by rfl) ⟨1364930, by rfl⟩ : syracuseStep 1819907 = 2729861) B2729861
theorem B1361171 : Blo 806344 1361171 := bstep (se 1 (by rfl) ⟨1020878, by rfl⟩ : syracuseStep 1361171 = 2041757) B2041757
theorem B1295747 : Blo 806344 1295747 := bstep (se 1 (by rfl) ⟨971810, by rfl⟩ : syracuseStep 1295747 = 1943621) B1943621
theorem B1361299 : Blo 806344 1361299 := bstep (se 1 (by rfl) ⟨1020974, by rfl⟩ : syracuseStep 1361299 = 2041949) B2041949
theorem B3458467 : Blo 806344 3458467 := bstep (se 1 (by rfl) ⟨2593850, by rfl⟩ : syracuseStep 3458467 = 5187701) B5187701
theorem B1295843 : Blo 806344 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B1295875 : Blo 806344 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B1820177 : Blo 806344 1820177 := bstep (se 2 (by rfl) ⟨682566, by rfl⟩ : syracuseStep 1820177 = 1365133) B1365133
theorem B1361441 : Blo 806344 1361441 := bstep (se 2 (by rfl) ⟨510540, by rfl⟩ : syracuseStep 1361441 = 1021081) B1021081
theorem B1820195 : Blo 806344 1820195 := bstep (se 1 (by rfl) ⟨1365146, by rfl⟩ : syracuseStep 1820195 = 2730293) B2730293
theorem B1361569 : Blo 806344 1361569 := bstep (se 2 (by rfl) ⟨510588, by rfl⟩ : syracuseStep 1361569 = 1021177) B1021177
theorem B1361603 : Blo 806344 1361603 := bstep (se 1 (by rfl) ⟨1021202, by rfl⟩ : syracuseStep 1361603 = 2042405) B2042405
theorem B2049745 : Blo 806344 2049745 := bstep (se 2 (by rfl) ⟨768654, by rfl⟩ : syracuseStep 2049745 = 1537309) B1537309
theorem B4605731 : Blo 806344 4605731 := bstep (se 1 (by rfl) ⟨3454298, by rfl⟩ : syracuseStep 4605731 = 6908597) B6908597
theorem B1722161 : Blo 806344 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B1820465 : Blo 806344 1820465 := bstep (se 2 (by rfl) ⟨682674, by rfl⟩ : syracuseStep 1820465 = 1365349) B1365349
theorem B1361731 : Blo 806344 1361731 := bstep (se 1 (by rfl) ⟨1021298, by rfl⟩ : syracuseStep 1361731 = 2042597) B2042597
theorem B1820483 : Blo 806344 1820483 := bstep (se 1 (by rfl) ⟨1365362, by rfl⟩ : syracuseStep 1820483 = 2730725) B2730725
theorem B1361873 : Blo 806344 1361873 := bstep (se 2 (by rfl) ⟨510702, by rfl⟩ : syracuseStep 1361873 = 1021405) B1021405
theorem B2050019 : Blo 806344 2050019 := bstep (se 1 (by rfl) ⟨1537514, by rfl⟩ : syracuseStep 2050019 = 3075029) B3075029
theorem B1460195 : Blo 806344 1460195 := bstep (se 1 (by rfl) ⟨1095146, by rfl⟩ : syracuseStep 1460195 = 2190293) B2190293
theorem B2770993 : Blo 806344 2770993 := bstep (se 2 (by rfl) ⟨1039122, by rfl⟩ : syracuseStep 2770993 = 2078245) B2078245
theorem B1362001 : Blo 806344 1362001 := bstep (se 2 (by rfl) ⟨510750, by rfl⟩ : syracuseStep 1362001 = 1021501) B1021501
theorem B1820753 : Blo 806344 1820753 := bstep (se 2 (by rfl) ⟨682782, by rfl⟩ : syracuseStep 1820753 = 1365565) B1365565
theorem B1820771 : Blo 806344 1820771 := bstep (se 1 (by rfl) ⟨1365578, by rfl⟩ : syracuseStep 1820771 = 2731157) B2731157
theorem B1362035 : Blo 806344 1362035 := bstep (se 1 (by rfl) ⟨1021526, by rfl⟩ : syracuseStep 1362035 = 2043053) B2043053
theorem B2050211 : Blo 806344 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B3066083 : Blo 806344 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B1362163 : Blo 806344 1362163 := bstep (se 1 (by rfl) ⟨1021622, by rfl⟩ : syracuseStep 1362163 = 2043245) B2043245
theorem B1821041 : Blo 806344 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B1362305 : Blo 806344 1362305 := bstep (se 2 (by rfl) ⟨510864, by rfl⟩ : syracuseStep 1362305 = 1021729) B1021729
theorem B1821059 : Blo 806344 1821059 := bstep (se 1 (by rfl) ⟨1365794, by rfl⟩ : syracuseStep 1821059 = 2731589) B2731589
theorem B1296785 : Blo 806344 1296785 := bstep (se 2 (by rfl) ⟨486294, by rfl⟩ : syracuseStep 1296785 = 972589) B972589
theorem B1362433 : Blo 806344 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B1362467 : Blo 806344 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B969283 : Blo 806344 969283 := bstep (se 1 (by rfl) ⟨726962, by rfl⟩ : syracuseStep 969283 = 1453925) B1453925
theorem B2214467 : Blo 806344 2214467 := bstep (se 1 (by rfl) ⟨1660850, by rfl⟩ : syracuseStep 2214467 = 3321701) B3321701
theorem B1821329 : Blo 806344 1821329 := bstep (se 2 (by rfl) ⟨682998, by rfl⟩ : syracuseStep 1821329 = 1365997) B1365997
theorem B1362595 : Blo 806344 1362595 := bstep (se 1 (by rfl) ⟨1021946, by rfl⟩ : syracuseStep 1362595 = 2043893) B2043893
theorem B1821347 : Blo 806344 1821347 := bstep (se 1 (by rfl) ⟨1366010, by rfl⟩ : syracuseStep 1821347 = 2732021) B2732021
theorem B4606733 : Blo 806344 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B1362737 : Blo 806344 1362737 := bstep (se 2 (by rfl) ⟨511026, by rfl⟩ : syracuseStep 1362737 = 1022053) B1022053
theorem B969619 : Blo 806344 969619 := bstep (se 1 (by rfl) ⟨727214, by rfl⟩ : syracuseStep 969619 = 1454429) B1454429
theorem B1362865 : Blo 806344 1362865 := bstep (se 2 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 1362865 = 1022149) B1022149
theorem B1821617 : Blo 806344 1821617 := bstep (se 2 (by rfl) ⟨683106, by rfl⟩ : syracuseStep 1821617 = 1366213) B1366213
theorem B1821635 : Blo 806344 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B1362899 : Blo 806344 1362899 := bstep (se 1 (by rfl) ⟨1022174, by rfl⟩ : syracuseStep 1362899 = 2044349) B2044349
theorem B4082723 : Blo 806344 4082723 := bstep (se 1 (by rfl) ⟨3062042, by rfl⟩ : syracuseStep 4082723 = 6124085) B6124085
theorem B1723459 : Blo 806344 1723459 := bstep (se 1 (by rfl) ⟨1292594, by rfl⟩ : syracuseStep 1723459 = 2585189) B2585189
theorem B2051153 : Blo 806344 2051153 := bstep (se 2 (by rfl) ⟨769182, by rfl⟩ : syracuseStep 2051153 = 1538365) B1538365
theorem B1363027 : Blo 806344 1363027 := bstep (se 1 (by rfl) ⟨1022270, by rfl⟩ : syracuseStep 1363027 = 2044541) B2044541
theorem B23645297 : Blo 806344 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B3067085 : Blo 806344 3067085 := bstep (se 3 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 3067085 = 1150157) B1150157
theorem B1821905 : Blo 806344 1821905 := bstep (se 2 (by rfl) ⟨683214, by rfl⟩ : syracuseStep 1821905 = 1366429) B1366429
theorem B1363169 : Blo 806344 1363169 := bstep (se 2 (by rfl) ⟨511188, by rfl⟩ : syracuseStep 1363169 = 1022377) B1022377
theorem B1821923 : Blo 806344 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B1363297 : Blo 806344 1363297 := bstep (se 2 (by rfl) ⟨511236, by rfl⟩ : syracuseStep 1363297 = 1022473) B1022473
theorem B1363331 : Blo 806344 1363331 := bstep (se 1 (by rfl) ⟨1022498, by rfl⟩ : syracuseStep 1363331 = 2044997) B2044997
theorem B5819789 : Blo 806344 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B10374581 : Blo 806344 10374581 := bstep (se 5 (by rfl) ⟨486308, by rfl⟩ : syracuseStep 10374581 = 972617) B972617
theorem B806355 : Blo 806344 806355 := bstep (se 1 (by rfl) ⟨604766, by rfl⟩ : syracuseStep 806355 = 1209533) B1209533
theorem B806371 : Blo 806344 806371 := bstep (se 1 (by rfl) ⟨604778, by rfl⟩ : syracuseStep 806371 = 1209557) B1209557
theorem B1822193 : Blo 806344 1822193 := bstep (se 2 (by rfl) ⟨683322, by rfl⟩ : syracuseStep 1822193 = 1366645) B1366645
theorem B806387 : Blo 806344 806387 := bstep (se 1 (by rfl) ⟨604790, by rfl⟩ : syracuseStep 806387 = 1209581) B1209581
theorem B806403 : Blo 806344 806403 := bstep (se 1 (by rfl) ⟨604802, by rfl⟩ : syracuseStep 806403 = 1209605) B1209605
theorem B1363459 : Blo 806344 1363459 := bstep (se 1 (by rfl) ⟨1022594, by rfl⟩ : syracuseStep 1363459 = 2045189) B2045189
theorem B1822211 : Blo 806344 1822211 := bstep (se 1 (by rfl) ⟨1366658, by rfl⟩ : syracuseStep 1822211 = 2733317) B2733317
theorem B806419 : Blo 806344 806419 := bstep (se 1 (by rfl) ⟨604814, by rfl⟩ : syracuseStep 806419 = 1209629) B1209629
theorem B806435 : Blo 806344 806435 := bstep (se 1 (by rfl) ⟨604826, by rfl⟩ : syracuseStep 806435 = 1209653) B1209653
theorem B806451 : Blo 806344 806451 := bstep (se 1 (by rfl) ⟨604838, by rfl⟩ : syracuseStep 806451 = 1209677) B1209677
theorem B806467 : Blo 806344 806467 := bstep (se 1 (by rfl) ⟨604850, by rfl⟩ : syracuseStep 806467 = 1209701) B1209701
theorem B806483 : Blo 806344 806483 := bstep (se 1 (by rfl) ⟨604862, by rfl⟩ : syracuseStep 806483 = 1209725) B1209725
theorem B806499 : Blo 806344 806499 := bstep (se 1 (by rfl) ⟨604874, by rfl⟩ : syracuseStep 806499 = 1209749) B1209749
theorem B5820017 : Blo 806344 5820017 := bstep (se 2 (by rfl) ⟨2182506, by rfl⟩ : syracuseStep 5820017 = 4365013) B4365013
theorem B806515 : Blo 806344 806515 := bstep (se 1 (by rfl) ⟨604886, by rfl⟩ : syracuseStep 806515 = 1209773) B1209773
theorem B806531 : Blo 806344 806531 := bstep (se 1 (by rfl) ⟨604898, by rfl⟩ : syracuseStep 806531 = 1209797) B1209797
theorem B1363601 : Blo 806344 1363601 := bstep (se 2 (by rfl) ⟨511350, by rfl⟩ : syracuseStep 1363601 = 1022701) B1022701
theorem B806547 : Blo 806344 806547 := bstep (se 1 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 806547 = 1209821) B1209821
theorem B806563 : Blo 806344 806563 := bstep (se 1 (by rfl) ⟨604922, by rfl⟩ : syracuseStep 806563 = 1209845) B1209845
theorem B806579 : Blo 806344 806579 := bstep (se 1 (by rfl) ⟨604934, by rfl⟩ : syracuseStep 806579 = 1209869) B1209869
theorem B806595 : Blo 806344 806595 := bstep (se 1 (by rfl) ⟨604946, by rfl⟩ : syracuseStep 806595 = 1209893) B1209893
theorem B806611 : Blo 806344 806611 := bstep (se 1 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 806611 = 1209917) B1209917
theorem B806627 : Blo 806344 806627 := bstep (se 1 (by rfl) ⟨604970, by rfl⟩ : syracuseStep 806627 = 1209941) B1209941
theorem B806643 : Blo 806344 806643 := bstep (se 1 (by rfl) ⟨604982, by rfl⟩ : syracuseStep 806643 = 1209965) B1209965
theorem B806659 : Blo 806344 806659 := bstep (se 1 (by rfl) ⟨604994, by rfl⟩ : syracuseStep 806659 = 1209989) B1209989
theorem B1363729 : Blo 806344 1363729 := bstep (se 2 (by rfl) ⟨511398, by rfl⟩ : syracuseStep 1363729 = 1022797) B1022797
theorem B1822481 : Blo 806344 1822481 := bstep (se 2 (by rfl) ⟨683430, by rfl⟩ : syracuseStep 1822481 = 1366861) B1366861
theorem B806675 : Blo 806344 806675 := bstep (se 1 (by rfl) ⟨605006, by rfl⟩ : syracuseStep 806675 = 1210013) B1210013
theorem B806691 : Blo 806344 806691 := bstep (se 1 (by rfl) ⟨605018, by rfl⟩ : syracuseStep 806691 = 1210037) B1210037
theorem B1822499 : Blo 806344 1822499 := bstep (se 1 (by rfl) ⟨1366874, by rfl⟩ : syracuseStep 1822499 = 2733749) B2733749
theorem B3460913 : Blo 806344 3460913 := bstep (se 2 (by rfl) ⟨1297842, by rfl⟩ : syracuseStep 3460913 = 2595685) B2595685
theorem B806707 : Blo 806344 806707 := bstep (se 1 (by rfl) ⟨605030, by rfl⟩ : syracuseStep 806707 = 1210061) B1210061
theorem B1363763 : Blo 806344 1363763 := bstep (se 1 (by rfl) ⟨1022822, by rfl⟩ : syracuseStep 1363763 = 2045645) B2045645
theorem B806723 : Blo 806344 806723 := bstep (se 1 (by rfl) ⟨605042, by rfl⟩ : syracuseStep 806723 = 1210085) B1210085
theorem B4083533 : Blo 806344 4083533 := bstep (se 3 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 4083533 = 1531325) B1531325
theorem B806739 : Blo 806344 806739 := bstep (se 1 (by rfl) ⟨605054, by rfl⟩ : syracuseStep 806739 = 1210109) B1210109
theorem B806755 : Blo 806344 806755 := bstep (se 1 (by rfl) ⟨605066, by rfl⟩ : syracuseStep 806755 = 1210133) B1210133
theorem B806771 : Blo 806344 806771 := bstep (se 1 (by rfl) ⟨605078, by rfl⟩ : syracuseStep 806771 = 1210157) B1210157
theorem B806787 : Blo 806344 806787 := bstep (se 1 (by rfl) ⟨605090, by rfl⟩ : syracuseStep 806787 = 1210181) B1210181
theorem B806803 : Blo 806344 806803 := bstep (se 1 (by rfl) ⟨605102, by rfl⟩ : syracuseStep 806803 = 1210205) B1210205
theorem B806819 : Blo 806344 806819 := bstep (se 1 (by rfl) ⟨605114, by rfl⟩ : syracuseStep 806819 = 1210229) B1210229
theorem B806835 : Blo 806344 806835 := bstep (se 1 (by rfl) ⟨605126, by rfl⟩ : syracuseStep 806835 = 1210253) B1210253
theorem B1363891 : Blo 806344 1363891 := bstep (se 1 (by rfl) ⟨1022918, by rfl⟩ : syracuseStep 1363891 = 2045837) B2045837
theorem B806851 : Blo 806344 806851 := bstep (se 1 (by rfl) ⟨605138, by rfl⟩ : syracuseStep 806851 = 1210277) B1210277
theorem B806867 : Blo 806344 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B806883 : Blo 806344 806883 := bstep (se 1 (by rfl) ⟨605162, by rfl⟩ : syracuseStep 806883 = 1210325) B1210325
theorem B806899 : Blo 806344 806899 := bstep (se 1 (by rfl) ⟨605174, by rfl⟩ : syracuseStep 806899 = 1210349) B1210349
theorem B806915 : Blo 806344 806915 := bstep (se 1 (by rfl) ⟨605186, by rfl⟩ : syracuseStep 806915 = 1210373) B1210373
theorem B806931 : Blo 806344 806931 := bstep (se 1 (by rfl) ⟨605198, by rfl⟩ : syracuseStep 806931 = 1210397) B1210397
theorem B806947 : Blo 806344 806947 := bstep (se 1 (by rfl) ⟨605210, by rfl⟩ : syracuseStep 806947 = 1210421) B1210421
theorem B1822769 : Blo 806344 1822769 := bstep (se 2 (by rfl) ⟨683538, by rfl⟩ : syracuseStep 1822769 = 1367077) B1367077
theorem B806963 : Blo 806344 806963 := bstep (se 1 (by rfl) ⟨605222, by rfl⟩ : syracuseStep 806963 = 1210445) B1210445
theorem B1364033 : Blo 806344 1364033 := bstep (se 2 (by rfl) ⟨511512, by rfl⟩ : syracuseStep 1364033 = 1023025) B1023025
theorem B806979 : Blo 806344 806979 := bstep (se 1 (by rfl) ⟨605234, by rfl⟩ : syracuseStep 806979 = 1210469) B1210469
theorem B1822787 : Blo 806344 1822787 := bstep (se 1 (by rfl) ⟨1367090, by rfl⟩ : syracuseStep 1822787 = 2734181) B2734181
theorem B806995 : Blo 806344 806995 := bstep (se 1 (by rfl) ⟨605246, by rfl⟩ : syracuseStep 806995 = 1210493) B1210493
theorem B807011 : Blo 806344 807011 := bstep (se 1 (by rfl) ⟨605258, by rfl⟩ : syracuseStep 807011 = 1210517) B1210517
theorem B807027 : Blo 806344 807027 := bstep (se 1 (by rfl) ⟨605270, by rfl⟩ : syracuseStep 807027 = 1210541) B1210541
theorem B807043 : Blo 806344 807043 := bstep (se 1 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 807043 = 1210565) B1210565
theorem B6312077 : Blo 806344 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B807059 : Blo 806344 807059 := bstep (se 1 (by rfl) ⟨605294, by rfl⟩ : syracuseStep 807059 = 1210589) B1210589
theorem B807075 : Blo 806344 807075 := bstep (se 1 (by rfl) ⟨605306, by rfl⟩ : syracuseStep 807075 = 1210613) B1210613
theorem B807091 : Blo 806344 807091 := bstep (se 1 (by rfl) ⟨605318, by rfl⟩ : syracuseStep 807091 = 1210637) B1210637
theorem B1364161 : Blo 806344 1364161 := bstep (se 2 (by rfl) ⟨511560, by rfl⟩ : syracuseStep 1364161 = 1023121) B1023121
theorem B807107 : Blo 806344 807107 := bstep (se 1 (by rfl) ⟨605330, by rfl⟩ : syracuseStep 807107 = 1210661) B1210661
theorem B807123 : Blo 806344 807123 := bstep (se 1 (by rfl) ⟨605342, by rfl⟩ : syracuseStep 807123 = 1210685) B1210685
theorem B807139 : Blo 806344 807139 := bstep (se 1 (by rfl) ⟨605354, by rfl⟩ : syracuseStep 807139 = 1210709) B1210709
theorem B1364195 : Blo 806344 1364195 := bstep (se 1 (by rfl) ⟨1023146, by rfl⟩ : syracuseStep 1364195 = 2046293) B2046293
theorem B807155 : Blo 806344 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B807171 : Blo 806344 807171 := bstep (se 1 (by rfl) ⟨605378, by rfl⟩ : syracuseStep 807171 = 1210757) B1210757
theorem B1724689 : Blo 806344 1724689 := bstep (se 2 (by rfl) ⟨646758, by rfl⟩ : syracuseStep 1724689 = 1293517) B1293517
theorem B807187 : Blo 806344 807187 := bstep (se 1 (by rfl) ⟨605390, by rfl⟩ : syracuseStep 807187 = 1210781) B1210781
theorem B807203 : Blo 806344 807203 := bstep (se 1 (by rfl) ⟨605402, by rfl⟩ : syracuseStep 807203 = 1210805) B1210805
theorem B807219 : Blo 806344 807219 := bstep (se 1 (by rfl) ⟨605414, by rfl⟩ : syracuseStep 807219 = 1210829) B1210829
theorem B807235 : Blo 806344 807235 := bstep (se 1 (by rfl) ⟨605426, by rfl⟩ : syracuseStep 807235 = 1210853) B1210853
theorem B1823057 : Blo 806344 1823057 := bstep (se 2 (by rfl) ⟨683646, by rfl⟩ : syracuseStep 1823057 = 1367293) B1367293
theorem B807251 : Blo 806344 807251 := bstep (se 1 (by rfl) ⟨605438, by rfl⟩ : syracuseStep 807251 = 1210877) B1210877
theorem B807267 : Blo 806344 807267 := bstep (se 1 (by rfl) ⟨605450, by rfl⟩ : syracuseStep 807267 = 1210901) B1210901
theorem B1364323 : Blo 806344 1364323 := bstep (se 1 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 1364323 = 2046485) B2046485
theorem B1823075 : Blo 806344 1823075 := bstep (se 1 (by rfl) ⟨1367306, by rfl⟩ : syracuseStep 1823075 = 2734613) B2734613
theorem B807283 : Blo 806344 807283 := bstep (se 1 (by rfl) ⟨605462, by rfl⟩ : syracuseStep 807283 = 1210925) B1210925
theorem B807299 : Blo 806344 807299 := bstep (se 1 (by rfl) ⟨605474, by rfl⟩ : syracuseStep 807299 = 1210949) B1210949
theorem B807315 : Blo 806344 807315 := bstep (se 1 (by rfl) ⟨605486, by rfl⟩ : syracuseStep 807315 = 1210973) B1210973
theorem B807331 : Blo 806344 807331 := bstep (se 1 (by rfl) ⟨605498, by rfl⟩ : syracuseStep 807331 = 1210997) B1210997
theorem B807347 : Blo 806344 807347 := bstep (se 1 (by rfl) ⟨605510, by rfl⟩ : syracuseStep 807347 = 1211021) B1211021
theorem B807363 : Blo 806344 807363 := bstep (se 1 (by rfl) ⟨605522, by rfl⟩ : syracuseStep 807363 = 1211045) B1211045
theorem B807379 : Blo 806344 807379 := bstep (se 1 (by rfl) ⟨605534, by rfl⟩ : syracuseStep 807379 = 1211069) B1211069
theorem B807395 : Blo 806344 807395 := bstep (se 1 (by rfl) ⟨605546, by rfl⟩ : syracuseStep 807395 = 1211093) B1211093
theorem B1364465 : Blo 806344 1364465 := bstep (se 2 (by rfl) ⟨511674, by rfl⟩ : syracuseStep 1364465 = 1023349) B1023349
theorem B807411 : Blo 806344 807411 := bstep (se 1 (by rfl) ⟨605558, by rfl⟩ : syracuseStep 807411 = 1211117) B1211117
theorem B807427 : Blo 806344 807427 := bstep (se 1 (by rfl) ⟨605570, by rfl⟩ : syracuseStep 807427 = 1211141) B1211141
theorem B807443 : Blo 806344 807443 := bstep (se 1 (by rfl) ⟨605582, by rfl⟩ : syracuseStep 807443 = 1211165) B1211165
theorem B807459 : Blo 806344 807459 := bstep (se 1 (by rfl) ⟨605594, by rfl⟩ : syracuseStep 807459 = 1211189) B1211189
theorem B807475 : Blo 806344 807475 := bstep (se 1 (by rfl) ⟨605606, by rfl⟩ : syracuseStep 807475 = 1211213) B1211213
theorem B807491 : Blo 806344 807491 := bstep (se 1 (by rfl) ⟨605618, by rfl⟩ : syracuseStep 807491 = 1211237) B1211237
theorem B807507 : Blo 806344 807507 := bstep (se 1 (by rfl) ⟨605630, by rfl⟩ : syracuseStep 807507 = 1211261) B1211261
theorem B807523 : Blo 806344 807523 := bstep (se 1 (by rfl) ⟨605642, by rfl⟩ : syracuseStep 807523 = 1211285) B1211285
theorem B1364593 : Blo 806344 1364593 := bstep (se 2 (by rfl) ⟨511722, by rfl⟩ : syracuseStep 1364593 = 1023445) B1023445
theorem B807539 : Blo 806344 807539 := bstep (se 1 (by rfl) ⟨605654, by rfl⟩ : syracuseStep 807539 = 1211309) B1211309
theorem B807555 : Blo 806344 807555 := bstep (se 1 (by rfl) ⟨605666, by rfl⟩ : syracuseStep 807555 = 1211333) B1211333
theorem B807571 : Blo 806344 807571 := bstep (se 1 (by rfl) ⟨605678, by rfl⟩ : syracuseStep 807571 = 1211357) B1211357
theorem B1364627 : Blo 806344 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B807587 : Blo 806344 807587 := bstep (se 1 (by rfl) ⟨605690, by rfl⟩ : syracuseStep 807587 = 1211381) B1211381
theorem B807603 : Blo 806344 807603 := bstep (se 1 (by rfl) ⟨605702, by rfl⟩ : syracuseStep 807603 = 1211405) B1211405
theorem B807619 : Blo 806344 807619 := bstep (se 1 (by rfl) ⟨605714, by rfl⟩ : syracuseStep 807619 = 1211429) B1211429
theorem B807635 : Blo 806344 807635 := bstep (se 1 (by rfl) ⟨605726, by rfl⟩ : syracuseStep 807635 = 1211453) B1211453
theorem B807651 : Blo 806344 807651 := bstep (se 1 (by rfl) ⟨605738, by rfl⟩ : syracuseStep 807651 = 1211477) B1211477
theorem B807667 : Blo 806344 807667 := bstep (se 1 (by rfl) ⟨605750, by rfl⟩ : syracuseStep 807667 = 1211501) B1211501
theorem B807683 : Blo 806344 807683 := bstep (se 1 (by rfl) ⟨605762, by rfl⟩ : syracuseStep 807683 = 1211525) B1211525
theorem B807699 : Blo 806344 807699 := bstep (se 1 (by rfl) ⟨605774, by rfl⟩ : syracuseStep 807699 = 1211549) B1211549
theorem B1364755 : Blo 806344 1364755 := bstep (se 1 (by rfl) ⟨1023566, by rfl⟩ : syracuseStep 1364755 = 2047133) B2047133
theorem B807715 : Blo 806344 807715 := bstep (se 1 (by rfl) ⟨605786, by rfl⟩ : syracuseStep 807715 = 1211573) B1211573
theorem B807731 : Blo 806344 807731 := bstep (se 1 (by rfl) ⟨605798, by rfl⟩ : syracuseStep 807731 = 1211597) B1211597
theorem B807747 : Blo 806344 807747 := bstep (se 1 (by rfl) ⟨605810, by rfl⟩ : syracuseStep 807747 = 1211621) B1211621
theorem B807763 : Blo 806344 807763 := bstep (se 1 (by rfl) ⟨605822, by rfl⟩ : syracuseStep 807763 = 1211645) B1211645
theorem B807779 : Blo 806344 807779 := bstep (se 1 (by rfl) ⟨605834, by rfl⟩ : syracuseStep 807779 = 1211669) B1211669
theorem B807795 : Blo 806344 807795 := bstep (se 1 (by rfl) ⟨605846, by rfl⟩ : syracuseStep 807795 = 1211693) B1211693
theorem B807811 : Blo 806344 807811 := bstep (se 1 (by rfl) ⟨605858, by rfl⟩ : syracuseStep 807811 = 1211717) B1211717
theorem B807827 : Blo 806344 807827 := bstep (se 1 (by rfl) ⟨605870, by rfl⟩ : syracuseStep 807827 = 1211741) B1211741
theorem B1364897 : Blo 806344 1364897 := bstep (se 2 (by rfl) ⟨511836, by rfl⟩ : syracuseStep 1364897 = 1023673) B1023673
theorem B807843 : Blo 806344 807843 := bstep (se 1 (by rfl) ⟨605882, by rfl⟩ : syracuseStep 807843 = 1211765) B1211765
theorem B807859 : Blo 806344 807859 := bstep (se 1 (by rfl) ⟨605894, by rfl⟩ : syracuseStep 807859 = 1211789) B1211789
theorem B807875 : Blo 806344 807875 := bstep (se 1 (by rfl) ⟨605906, by rfl⟩ : syracuseStep 807875 = 1211813) B1211813
theorem B807891 : Blo 806344 807891 := bstep (se 1 (by rfl) ⟨605918, by rfl⟩ : syracuseStep 807891 = 1211837) B1211837
theorem B807907 : Blo 806344 807907 := bstep (se 1 (by rfl) ⟨605930, by rfl⟩ : syracuseStep 807907 = 1211861) B1211861
theorem B2184173 : Blo 806344 2184173 := bstep (se 3 (by rfl) ⟨409532, by rfl⟩ : syracuseStep 2184173 = 819065) B819065
theorem B807923 : Blo 806344 807923 := bstep (se 1 (by rfl) ⟨605942, by rfl⟩ : syracuseStep 807923 = 1211885) B1211885
theorem B807939 : Blo 806344 807939 := bstep (se 1 (by rfl) ⟨605954, by rfl⟩ : syracuseStep 807939 = 1211909) B1211909
theorem B807955 : Blo 806344 807955 := bstep (se 1 (by rfl) ⟨605966, by rfl⟩ : syracuseStep 807955 = 1211933) B1211933
theorem B1365025 : Blo 806344 1365025 := bstep (se 2 (by rfl) ⟨511884, by rfl⟩ : syracuseStep 1365025 = 1023769) B1023769
theorem B1725475 : Blo 806344 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B807971 : Blo 806344 807971 := bstep (se 1 (by rfl) ⟨605978, by rfl⟩ : syracuseStep 807971 = 1211957) B1211957
theorem B807987 : Blo 806344 807987 := bstep (se 1 (by rfl) ⟨605990, by rfl⟩ : syracuseStep 807987 = 1211981) B1211981
theorem B808003 : Blo 806344 808003 := bstep (se 1 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 808003 = 1212005) B1212005
theorem B1365059 : Blo 806344 1365059 := bstep (se 1 (by rfl) ⟨1023794, by rfl⟩ : syracuseStep 1365059 = 2047589) B2047589
theorem B808019 : Blo 806344 808019 := bstep (se 1 (by rfl) ⟨606014, by rfl⟩ : syracuseStep 808019 = 1212029) B1212029
theorem B808035 : Blo 806344 808035 := bstep (se 1 (by rfl) ⟨606026, by rfl⟩ : syracuseStep 808035 = 1212053) B1212053
theorem B808051 : Blo 806344 808051 := bstep (se 1 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 808051 = 1212077) B1212077
theorem B808067 : Blo 806344 808067 := bstep (se 1 (by rfl) ⟨606050, by rfl⟩ : syracuseStep 808067 = 1212101) B1212101
theorem B808083 : Blo 806344 808083 := bstep (se 1 (by rfl) ⟨606062, by rfl⟩ : syracuseStep 808083 = 1212125) B1212125
theorem B808099 : Blo 806344 808099 := bstep (se 1 (by rfl) ⟨606074, by rfl⟩ : syracuseStep 808099 = 1212149) B1212149
theorem B808115 : Blo 806344 808115 := bstep (se 1 (by rfl) ⟨606086, by rfl⟩ : syracuseStep 808115 = 1212173) B1212173
theorem B808131 : Blo 806344 808131 := bstep (se 1 (by rfl) ⟨606098, by rfl⟩ : syracuseStep 808131 = 1212197) B1212197
theorem B1365187 : Blo 806344 1365187 := bstep (se 1 (by rfl) ⟨1023890, by rfl⟩ : syracuseStep 1365187 = 2047781) B2047781
theorem B808147 : Blo 806344 808147 := bstep (se 1 (by rfl) ⟨606110, by rfl⟩ : syracuseStep 808147 = 1212221) B1212221
theorem B808163 : Blo 806344 808163 := bstep (se 1 (by rfl) ⟨606122, by rfl⟩ : syracuseStep 808163 = 1212245) B1212245
theorem B4150499 : Blo 806344 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B808179 : Blo 806344 808179 := bstep (se 1 (by rfl) ⟨606134, by rfl⟩ : syracuseStep 808179 = 1212269) B1212269
theorem B808195 : Blo 806344 808195 := bstep (se 1 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 808195 = 1212293) B1212293
theorem B3069197 : Blo 806344 3069197 := bstep (se 3 (by rfl) ⟨575474, by rfl⟩ : syracuseStep 3069197 = 1150949) B1150949
theorem B808211 : Blo 806344 808211 := bstep (se 1 (by rfl) ⟨606158, by rfl⟩ : syracuseStep 808211 = 1212317) B1212317
theorem B808227 : Blo 806344 808227 := bstep (se 1 (by rfl) ⟨606170, by rfl⟩ : syracuseStep 808227 = 1212341) B1212341
theorem B808243 : Blo 806344 808243 := bstep (se 1 (by rfl) ⟨606182, by rfl⟩ : syracuseStep 808243 = 1212365) B1212365
theorem B808259 : Blo 806344 808259 := bstep (se 1 (by rfl) ⟨606194, by rfl⟩ : syracuseStep 808259 = 1212389) B1212389
theorem B1365329 : Blo 806344 1365329 := bstep (se 2 (by rfl) ⟨511998, by rfl⟩ : syracuseStep 1365329 = 1023997) B1023997
theorem B808275 : Blo 806344 808275 := bstep (se 1 (by rfl) ⟨606206, by rfl⟩ : syracuseStep 808275 = 1212413) B1212413
theorem B808291 : Blo 806344 808291 := bstep (se 1 (by rfl) ⟨606218, by rfl⟩ : syracuseStep 808291 = 1212437) B1212437
theorem B808307 : Blo 806344 808307 := bstep (se 1 (by rfl) ⟨606230, by rfl⟩ : syracuseStep 808307 = 1212461) B1212461
theorem B808323 : Blo 806344 808323 := bstep (se 1 (by rfl) ⟨606242, by rfl⟩ : syracuseStep 808323 = 1212485) B1212485
theorem B808339 : Blo 806344 808339 := bstep (se 1 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 808339 = 1212509) B1212509
theorem B808355 : Blo 806344 808355 := bstep (se 1 (by rfl) ⟨606266, by rfl⟩ : syracuseStep 808355 = 1212533) B1212533
theorem B808371 : Blo 806344 808371 := bstep (se 1 (by rfl) ⟨606278, by rfl⟩ : syracuseStep 808371 = 1212557) B1212557
theorem B808387 : Blo 806344 808387 := bstep (se 1 (by rfl) ⟨606290, by rfl⟩ : syracuseStep 808387 = 1212581) B1212581
theorem B1365457 : Blo 806344 1365457 := bstep (se 2 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 1365457 = 1024093) B1024093
theorem B808403 : Blo 806344 808403 := bstep (se 1 (by rfl) ⟨606302, by rfl⟩ : syracuseStep 808403 = 1212605) B1212605
theorem B808419 : Blo 806344 808419 := bstep (se 1 (by rfl) ⟨606314, by rfl⟩ : syracuseStep 808419 = 1212629) B1212629
theorem B808435 : Blo 806344 808435 := bstep (se 1 (by rfl) ⟨606326, by rfl⟩ : syracuseStep 808435 = 1212653) B1212653
theorem B1365491 : Blo 806344 1365491 := bstep (se 1 (by rfl) ⟨1024118, by rfl⟩ : syracuseStep 1365491 = 2048237) B2048237
theorem B808451 : Blo 806344 808451 := bstep (se 1 (by rfl) ⟨606338, by rfl⟩ : syracuseStep 808451 = 1212677) B1212677
theorem B808467 : Blo 806344 808467 := bstep (se 1 (by rfl) ⟨606350, by rfl⟩ : syracuseStep 808467 = 1212701) B1212701
theorem B808483 : Blo 806344 808483 := bstep (se 1 (by rfl) ⟨606362, by rfl⟩ : syracuseStep 808483 = 1212725) B1212725
theorem B808499 : Blo 806344 808499 := bstep (se 1 (by rfl) ⟨606374, by rfl⟩ : syracuseStep 808499 = 1212749) B1212749
theorem B808515 : Blo 806344 808515 := bstep (se 1 (by rfl) ⟨606386, by rfl⟩ : syracuseStep 808515 = 1212773) B1212773
theorem B808531 : Blo 806344 808531 := bstep (se 1 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 808531 = 1212797) B1212797
theorem B808547 : Blo 806344 808547 := bstep (se 1 (by rfl) ⟨606410, by rfl⟩ : syracuseStep 808547 = 1212821) B1212821
theorem B4609649 : Blo 806344 4609649 := bstep (se 2 (by rfl) ⟨1728618, by rfl⟩ : syracuseStep 4609649 = 3457237) B3457237
theorem B808563 : Blo 806344 808563 := bstep (se 1 (by rfl) ⟨606422, by rfl⟩ : syracuseStep 808563 = 1212845) B1212845
theorem B1365619 : Blo 806344 1365619 := bstep (se 1 (by rfl) ⟨1024214, by rfl⟩ : syracuseStep 1365619 = 2048429) B2048429
theorem B808579 : Blo 806344 808579 := bstep (se 1 (by rfl) ⟨606434, by rfl⟩ : syracuseStep 808579 = 1212869) B1212869
theorem B808595 : Blo 806344 808595 := bstep (se 1 (by rfl) ⟨606446, by rfl⟩ : syracuseStep 808595 = 1212893) B1212893
theorem B808611 : Blo 806344 808611 := bstep (se 1 (by rfl) ⟨606458, by rfl⟩ : syracuseStep 808611 = 1212917) B1212917
theorem B808627 : Blo 806344 808627 := bstep (se 1 (by rfl) ⟨606470, by rfl⟩ : syracuseStep 808627 = 1212941) B1212941
theorem B808643 : Blo 806344 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B808659 : Blo 806344 808659 := bstep (se 1 (by rfl) ⟨606494, by rfl⟩ : syracuseStep 808659 = 1212989) B1212989
theorem B808675 : Blo 806344 808675 := bstep (se 1 (by rfl) ⟨606506, by rfl⟩ : syracuseStep 808675 = 1213013) B1213013
theorem B1726193 : Blo 806344 1726193 := bstep (se 2 (by rfl) ⟨647322, by rfl⟩ : syracuseStep 1726193 = 1294645) B1294645
theorem B808691 : Blo 806344 808691 := bstep (se 1 (by rfl) ⟨606518, by rfl⟩ : syracuseStep 808691 = 1213037) B1213037
theorem B1365761 : Blo 806344 1365761 := bstep (se 2 (by rfl) ⟨512160, by rfl⟩ : syracuseStep 1365761 = 1024321) B1024321
theorem B808707 : Blo 806344 808707 := bstep (se 1 (by rfl) ⟨606530, by rfl⟩ : syracuseStep 808707 = 1213061) B1213061
theorem B808723 : Blo 806344 808723 := bstep (se 1 (by rfl) ⟨606542, by rfl⟩ : syracuseStep 808723 = 1213085) B1213085
theorem B808739 : Blo 806344 808739 := bstep (se 1 (by rfl) ⟨606554, by rfl⟩ : syracuseStep 808739 = 1213109) B1213109
theorem B3888931 : Blo 806344 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B808755 : Blo 806344 808755 := bstep (se 1 (by rfl) ⟨606566, by rfl⟩ : syracuseStep 808755 = 1213133) B1213133
theorem B808771 : Blo 806344 808771 := bstep (se 1 (by rfl) ⟨606578, by rfl⟩ : syracuseStep 808771 = 1213157) B1213157
theorem B808787 : Blo 806344 808787 := bstep (se 1 (by rfl) ⟨606590, by rfl⟩ : syracuseStep 808787 = 1213181) B1213181
theorem B808803 : Blo 806344 808803 := bstep (se 1 (by rfl) ⟨606602, by rfl⟩ : syracuseStep 808803 = 1213205) B1213205
theorem B808819 : Blo 806344 808819 := bstep (se 1 (by rfl) ⟨606614, by rfl⟩ : syracuseStep 808819 = 1213229) B1213229
theorem B1365889 : Blo 806344 1365889 := bstep (se 2 (by rfl) ⟨512208, by rfl⟩ : syracuseStep 1365889 = 1024417) B1024417
theorem B808835 : Blo 806344 808835 := bstep (se 1 (by rfl) ⟨606626, by rfl⟩ : syracuseStep 808835 = 1213253) B1213253
theorem B808851 : Blo 806344 808851 := bstep (se 1 (by rfl) ⟨606638, by rfl⟩ : syracuseStep 808851 = 1213277) B1213277
theorem B808867 : Blo 806344 808867 := bstep (se 1 (by rfl) ⟨606650, by rfl⟩ : syracuseStep 808867 = 1213301) B1213301
theorem B1365923 : Blo 806344 1365923 := bstep (se 1 (by rfl) ⟨1024442, by rfl⟩ : syracuseStep 1365923 = 2048885) B2048885
theorem B808883 : Blo 806344 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B808899 : Blo 806344 808899 := bstep (se 1 (by rfl) ⟨606674, by rfl⟩ : syracuseStep 808899 = 1213349) B1213349
theorem B808915 : Blo 806344 808915 := bstep (se 1 (by rfl) ⟨606686, by rfl⟩ : syracuseStep 808915 = 1213373) B1213373
theorem B808931 : Blo 806344 808931 := bstep (se 1 (by rfl) ⟨606698, by rfl⟩ : syracuseStep 808931 = 1213397) B1213397
theorem B808947 : Blo 806344 808947 := bstep (se 1 (by rfl) ⟨606710, by rfl⟩ : syracuseStep 808947 = 1213421) B1213421
theorem B907267 : Blo 806344 907267 := bstep (se 1 (by rfl) ⟨680450, by rfl⟩ : syracuseStep 907267 = 1360901) B1360901
theorem B808963 : Blo 806344 808963 := bstep (se 1 (by rfl) ⟨606722, by rfl⟩ : syracuseStep 808963 = 1213445) B1213445
theorem B808979 : Blo 806344 808979 := bstep (se 1 (by rfl) ⟨606734, by rfl⟩ : syracuseStep 808979 = 1213469) B1213469
theorem B808995 : Blo 806344 808995 := bstep (se 1 (by rfl) ⟨606746, by rfl⟩ : syracuseStep 808995 = 1213493) B1213493
theorem B1366051 : Blo 806344 1366051 := bstep (se 1 (by rfl) ⟨1024538, by rfl⟩ : syracuseStep 1366051 = 2049077) B2049077
theorem B3070001 : Blo 806344 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B809011 : Blo 806344 809011 := bstep (se 1 (by rfl) ⟨606758, by rfl⟩ : syracuseStep 809011 = 1213517) B1213517
theorem B809027 : Blo 806344 809027 := bstep (se 1 (by rfl) ⟨606770, by rfl⟩ : syracuseStep 809027 = 1213541) B1213541
theorem B809043 : Blo 806344 809043 := bstep (se 1 (by rfl) ⟨606782, by rfl⟩ : syracuseStep 809043 = 1213565) B1213565
theorem B809059 : Blo 806344 809059 := bstep (se 1 (by rfl) ⟨606794, by rfl⟩ : syracuseStep 809059 = 1213589) B1213589
theorem B809075 : Blo 806344 809075 := bstep (se 1 (by rfl) ⟨606806, by rfl⟩ : syracuseStep 809075 = 1213613) B1213613
theorem B809091 : Blo 806344 809091 := bstep (se 1 (by rfl) ⟨606818, by rfl⟩ : syracuseStep 809091 = 1213637) B1213637
theorem B907411 : Blo 806344 907411 := bstep (se 1 (by rfl) ⟨680558, by rfl⟩ : syracuseStep 907411 = 1361117) B1361117
theorem B809107 : Blo 806344 809107 := bstep (se 1 (by rfl) ⟨606830, by rfl⟩ : syracuseStep 809107 = 1213661) B1213661
theorem B809123 : Blo 806344 809123 := bstep (se 1 (by rfl) ⟨606842, by rfl⟩ : syracuseStep 809123 = 1213685) B1213685
theorem B1366193 : Blo 806344 1366193 := bstep (se 2 (by rfl) ⟨512322, by rfl⟩ : syracuseStep 1366193 = 1024645) B1024645
theorem B809139 : Blo 806344 809139 := bstep (se 1 (by rfl) ⟨606854, by rfl⟩ : syracuseStep 809139 = 1213709) B1213709
theorem B809155 : Blo 806344 809155 := bstep (se 1 (by rfl) ⟨606866, by rfl⟩ : syracuseStep 809155 = 1213733) B1213733
theorem B809171 : Blo 806344 809171 := bstep (se 1 (by rfl) ⟨606878, by rfl⟩ : syracuseStep 809171 = 1213757) B1213757
theorem B809187 : Blo 806344 809187 := bstep (se 1 (by rfl) ⟨606890, by rfl⟩ : syracuseStep 809187 = 1213781) B1213781
theorem B1726705 : Blo 806344 1726705 := bstep (se 2 (by rfl) ⟨647514, by rfl⟩ : syracuseStep 1726705 = 1295029) B1295029
theorem B809203 : Blo 806344 809203 := bstep (se 1 (by rfl) ⟨606902, by rfl⟩ : syracuseStep 809203 = 1213805) B1213805
theorem B809219 : Blo 806344 809219 := bstep (se 1 (by rfl) ⟨606914, by rfl⟩ : syracuseStep 809219 = 1213829) B1213829
theorem B809235 : Blo 806344 809235 := bstep (se 1 (by rfl) ⟨606926, by rfl⟩ : syracuseStep 809235 = 1213853) B1213853
theorem B973075 : Blo 806344 973075 := bstep (se 1 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 973075 = 1459613) B1459613
theorem B907555 : Blo 806344 907555 := bstep (se 1 (by rfl) ⟨680666, by rfl⟩ : syracuseStep 907555 = 1361333) B1361333
theorem B809251 : Blo 806344 809251 := bstep (se 1 (by rfl) ⟨606938, by rfl⟩ : syracuseStep 809251 = 1213877) B1213877
theorem B1366321 : Blo 806344 1366321 := bstep (se 2 (by rfl) ⟨512370, by rfl⟩ : syracuseStep 1366321 = 1024741) B1024741
theorem B809267 : Blo 806344 809267 := bstep (se 1 (by rfl) ⟨606950, by rfl⟩ : syracuseStep 809267 = 1213901) B1213901
theorem B809283 : Blo 806344 809283 := bstep (se 1 (by rfl) ⟨606962, by rfl⟩ : syracuseStep 809283 = 1213925) B1213925
theorem B809299 : Blo 806344 809299 := bstep (se 1 (by rfl) ⟨606974, by rfl⟩ : syracuseStep 809299 = 1213949) B1213949
theorem B1366355 : Blo 806344 1366355 := bstep (se 1 (by rfl) ⟨1024766, by rfl⟩ : syracuseStep 1366355 = 2049533) B2049533
theorem B809315 : Blo 806344 809315 := bstep (se 1 (by rfl) ⟨606986, by rfl⟩ : syracuseStep 809315 = 1213973) B1213973
theorem B809331 : Blo 806344 809331 := bstep (se 1 (by rfl) ⟨606998, by rfl⟩ : syracuseStep 809331 = 1213997) B1213997
theorem B809347 : Blo 806344 809347 := bstep (se 1 (by rfl) ⟨607010, by rfl⟩ : syracuseStep 809347 = 1214021) B1214021
theorem B809363 : Blo 806344 809363 := bstep (se 1 (by rfl) ⟨607022, by rfl⟩ : syracuseStep 809363 = 1214045) B1214045
theorem B809379 : Blo 806344 809379 := bstep (se 1 (by rfl) ⟨607034, by rfl⟩ : syracuseStep 809379 = 1214069) B1214069
theorem B907699 : Blo 806344 907699 := bstep (se 1 (by rfl) ⟨680774, by rfl⟩ : syracuseStep 907699 = 1361549) B1361549
theorem B809395 : Blo 806344 809395 := bstep (se 1 (by rfl) ⟨607046, by rfl⟩ : syracuseStep 809395 = 1214093) B1214093
theorem B809411 : Blo 806344 809411 := bstep (se 1 (by rfl) ⟨607058, by rfl⟩ : syracuseStep 809411 = 1214117) B1214117
theorem B809427 : Blo 806344 809427 := bstep (se 1 (by rfl) ⟨607070, by rfl⟩ : syracuseStep 809427 = 1214141) B1214141
theorem B1366483 : Blo 806344 1366483 := bstep (se 1 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 1366483 = 2049725) B2049725
theorem B809443 : Blo 806344 809443 := bstep (se 1 (by rfl) ⟨607082, by rfl⟩ : syracuseStep 809443 = 1214165) B1214165
theorem B809459 : Blo 806344 809459 := bstep (se 1 (by rfl) ⟨607094, by rfl⟩ : syracuseStep 809459 = 1214189) B1214189
theorem B809475 : Blo 806344 809475 := bstep (se 1 (by rfl) ⟨607106, by rfl⟩ : syracuseStep 809475 = 1214213) B1214213
theorem B809491 : Blo 806344 809491 := bstep (se 1 (by rfl) ⟨607118, by rfl⟩ : syracuseStep 809491 = 1214237) B1214237
theorem B809507 : Blo 806344 809507 := bstep (se 1 (by rfl) ⟨607130, by rfl⟩ : syracuseStep 809507 = 1214261) B1214261
theorem B809523 : Blo 806344 809523 := bstep (se 1 (by rfl) ⟨607142, by rfl⟩ : syracuseStep 809523 = 1214285) B1214285
theorem B907843 : Blo 806344 907843 := bstep (se 1 (by rfl) ⟨680882, by rfl⟩ : syracuseStep 907843 = 1361765) B1361765
theorem B809539 : Blo 806344 809539 := bstep (se 1 (by rfl) ⟨607154, by rfl⟩ : syracuseStep 809539 = 1214309) B1214309
theorem B809555 : Blo 806344 809555 := bstep (se 1 (by rfl) ⟨607166, by rfl⟩ : syracuseStep 809555 = 1214333) B1214333
theorem B1366625 : Blo 806344 1366625 := bstep (se 2 (by rfl) ⟨512484, by rfl⟩ : syracuseStep 1366625 = 1024969) B1024969
theorem B809571 : Blo 806344 809571 := bstep (se 1 (by rfl) ⟨607178, by rfl⟩ : syracuseStep 809571 = 1214357) B1214357
theorem B3889777 : Blo 806344 3889777 := bstep (se 2 (by rfl) ⟨1458666, by rfl⟩ : syracuseStep 3889777 = 2917333) B2917333
theorem B809587 : Blo 806344 809587 := bstep (se 1 (by rfl) ⟨607190, by rfl⟩ : syracuseStep 809587 = 1214381) B1214381
theorem B809603 : Blo 806344 809603 := bstep (se 1 (by rfl) ⟨607202, by rfl⟩ : syracuseStep 809603 = 1214405) B1214405
theorem B809619 : Blo 806344 809619 := bstep (se 1 (by rfl) ⟨607214, by rfl⟩ : syracuseStep 809619 = 1214429) B1214429
theorem B809635 : Blo 806344 809635 := bstep (se 1 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 809635 = 1214453) B1214453
theorem B4086449 : Blo 806344 4086449 := bstep (se 2 (by rfl) ⟨1532418, by rfl⟩ : syracuseStep 4086449 = 3064837) B3064837
theorem B809651 : Blo 806344 809651 := bstep (se 1 (by rfl) ⟨607238, by rfl⟩ : syracuseStep 809651 = 1214477) B1214477
theorem B809667 : Blo 806344 809667 := bstep (se 1 (by rfl) ⟨607250, by rfl⟩ : syracuseStep 809667 = 1214501) B1214501
theorem B5167813 : Blo 806344 5167813 := bstep (se 4 (by rfl) ⟨484482, by rfl⟩ : syracuseStep 5167813 = 968965) B968965
theorem B3070669 : Blo 806344 3070669 := bstep (se 3 (by rfl) ⟨575750, by rfl⟩ : syracuseStep 3070669 = 1151501) B1151501
theorem B907987 : Blo 806344 907987 := bstep (se 1 (by rfl) ⟨680990, by rfl⟩ : syracuseStep 907987 = 1361981) B1361981
theorem B809683 : Blo 806344 809683 := bstep (se 1 (by rfl) ⟨607262, by rfl⟩ : syracuseStep 809683 = 1214525) B1214525
theorem B1366753 : Blo 806344 1366753 := bstep (se 2 (by rfl) ⟨512532, by rfl⟩ : syracuseStep 1366753 = 1025065) B1025065
theorem B809699 : Blo 806344 809699 := bstep (se 1 (by rfl) ⟨607274, by rfl⟩ : syracuseStep 809699 = 1214549) B1214549
theorem B809715 : Blo 806344 809715 := bstep (se 1 (by rfl) ⟨607286, by rfl⟩ : syracuseStep 809715 = 1214573) B1214573
theorem B809731 : Blo 806344 809731 := bstep (se 1 (by rfl) ⟨607298, by rfl⟩ : syracuseStep 809731 = 1214597) B1214597
theorem B1366787 : Blo 806344 1366787 := bstep (se 1 (by rfl) ⟨1025090, by rfl⟩ : syracuseStep 1366787 = 2050181) B2050181
theorem B809747 : Blo 806344 809747 := bstep (se 1 (by rfl) ⟨607310, by rfl⟩ : syracuseStep 809747 = 1214621) B1214621
theorem B809763 : Blo 806344 809763 := bstep (se 1 (by rfl) ⟨607322, by rfl⟩ : syracuseStep 809763 = 1214645) B1214645
theorem B809779 : Blo 806344 809779 := bstep (se 1 (by rfl) ⟨607334, by rfl⟩ : syracuseStep 809779 = 1214669) B1214669
theorem B809795 : Blo 806344 809795 := bstep (se 1 (by rfl) ⟨607346, by rfl⟩ : syracuseStep 809795 = 1214693) B1214693
theorem B9820997 : Blo 806344 9820997 := bstep (se 4 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 9820997 = 1841437) B1841437
theorem B809811 : Blo 806344 809811 := bstep (se 1 (by rfl) ⟨607358, by rfl⟩ : syracuseStep 809811 = 1214717) B1214717
theorem B908131 : Blo 806344 908131 := bstep (se 1 (by rfl) ⟨681098, by rfl⟩ : syracuseStep 908131 = 1362197) B1362197
theorem B809827 : Blo 806344 809827 := bstep (se 1 (by rfl) ⟨607370, by rfl⟩ : syracuseStep 809827 = 1214741) B1214741
theorem B809843 : Blo 806344 809843 := bstep (se 1 (by rfl) ⟨607382, by rfl⟩ : syracuseStep 809843 = 1214765) B1214765
theorem B809859 : Blo 806344 809859 := bstep (se 1 (by rfl) ⟨607394, by rfl⟩ : syracuseStep 809859 = 1214789) B1214789
theorem B1366915 : Blo 806344 1366915 := bstep (se 1 (by rfl) ⟨1025186, by rfl⟩ : syracuseStep 1366915 = 2050373) B2050373
theorem B809875 : Blo 806344 809875 := bstep (se 1 (by rfl) ⟨607406, by rfl⟩ : syracuseStep 809875 = 1214813) B1214813
theorem B809891 : Blo 806344 809891 := bstep (se 1 (by rfl) ⟨607418, by rfl⟩ : syracuseStep 809891 = 1214837) B1214837
theorem B2808749 : Blo 806344 2808749 := bstep (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) B1053281
theorem B809907 : Blo 806344 809907 := bstep (se 1 (by rfl) ⟨607430, by rfl⟩ : syracuseStep 809907 = 1214861) B1214861
theorem B809923 : Blo 806344 809923 := bstep (se 1 (by rfl) ⟨607442, by rfl⟩ : syracuseStep 809923 = 1214885) B1214885
theorem B809939 : Blo 806344 809939 := bstep (se 1 (by rfl) ⟨607454, by rfl⟩ : syracuseStep 809939 = 1214909) B1214909
theorem B809955 : Blo 806344 809955 := bstep (se 1 (by rfl) ⟨607466, by rfl⟩ : syracuseStep 809955 = 1214933) B1214933
theorem B908275 : Blo 806344 908275 := bstep (se 1 (by rfl) ⟨681206, by rfl⟩ : syracuseStep 908275 = 1362413) B1362413
theorem B809971 : Blo 806344 809971 := bstep (se 1 (by rfl) ⟨607478, by rfl⟩ : syracuseStep 809971 = 1214957) B1214957
theorem B809987 : Blo 806344 809987 := bstep (se 1 (by rfl) ⟨607490, by rfl⟩ : syracuseStep 809987 = 1214981) B1214981
theorem B1367057 : Blo 806344 1367057 := bstep (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) B1025293
theorem B810003 : Blo 806344 810003 := bstep (se 1 (by rfl) ⟨607502, by rfl⟩ : syracuseStep 810003 = 1215005) B1215005
theorem B4611107 : Blo 806344 4611107 := bstep (se 1 (by rfl) ⟨3458330, by rfl⟩ : syracuseStep 4611107 = 6916661) B6916661
theorem B810019 : Blo 806344 810019 := bstep (se 1 (by rfl) ⟨607514, by rfl⟩ : syracuseStep 810019 = 1215029) B1215029
theorem B810035 : Blo 806344 810035 := bstep (se 1 (by rfl) ⟨607526, by rfl⟩ : syracuseStep 810035 = 1215053) B1215053
theorem B810051 : Blo 806344 810051 := bstep (se 1 (by rfl) ⟨607538, by rfl⟩ : syracuseStep 810051 = 1215077) B1215077
theorem B810067 : Blo 806344 810067 := bstep (se 1 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 810067 = 1215101) B1215101
theorem B810083 : Blo 806344 810083 := bstep (se 1 (by rfl) ⟨607562, by rfl⟩ : syracuseStep 810083 = 1215125) B1215125
theorem B810099 : Blo 806344 810099 := bstep (se 1 (by rfl) ⟨607574, by rfl⟩ : syracuseStep 810099 = 1215149) B1215149
theorem B908419 : Blo 806344 908419 := bstep (se 1 (by rfl) ⟨681314, by rfl⟩ : syracuseStep 908419 = 1362629) B1362629
theorem B810115 : Blo 806344 810115 := bstep (se 1 (by rfl) ⟨607586, by rfl⟩ : syracuseStep 810115 = 1215173) B1215173
theorem B1367185 : Blo 806344 1367185 := bstep (se 2 (by rfl) ⟨512694, by rfl⟩ : syracuseStep 1367185 = 1025389) B1025389
theorem B810131 : Blo 806344 810131 := bstep (se 1 (by rfl) ⟨607598, by rfl⟩ : syracuseStep 810131 = 1215197) B1215197
theorem B810147 : Blo 806344 810147 := bstep (se 1 (by rfl) ⟨607610, by rfl⟩ : syracuseStep 810147 = 1215221) B1215221
theorem B810163 : Blo 806344 810163 := bstep (se 1 (by rfl) ⟨607622, by rfl⟩ : syracuseStep 810163 = 1215245) B1215245
theorem B1367219 : Blo 806344 1367219 := bstep (se 1 (by rfl) ⟨1025414, by rfl⟩ : syracuseStep 1367219 = 2050829) B2050829
theorem B1531075 : Blo 806344 1531075 := bstep (se 1 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 1531075 = 2296613) B2296613
theorem B810179 : Blo 806344 810179 := bstep (se 1 (by rfl) ⟨607634, by rfl⟩ : syracuseStep 810179 = 1215269) B1215269
theorem B810195 : Blo 806344 810195 := bstep (se 1 (by rfl) ⟨607646, by rfl⟩ : syracuseStep 810195 = 1215293) B1215293
theorem B810211 : Blo 806344 810211 := bstep (se 1 (by rfl) ⟨607658, by rfl⟩ : syracuseStep 810211 = 1215317) B1215317
theorem B810227 : Blo 806344 810227 := bstep (se 1 (by rfl) ⟨607670, by rfl⟩ : syracuseStep 810227 = 1215341) B1215341
theorem B810243 : Blo 806344 810243 := bstep (se 1 (by rfl) ⟨607682, by rfl⟩ : syracuseStep 810243 = 1215365) B1215365
theorem B908563 : Blo 806344 908563 := bstep (se 1 (by rfl) ⟨681422, by rfl⟩ : syracuseStep 908563 = 1362845) B1362845
theorem B810259 : Blo 806344 810259 := bstep (se 1 (by rfl) ⟨607694, by rfl⟩ : syracuseStep 810259 = 1215389) B1215389
theorem B810275 : Blo 806344 810275 := bstep (se 1 (by rfl) ⟨607706, by rfl⟩ : syracuseStep 810275 = 1215413) B1215413
theorem B843059 : Blo 806344 843059 := bstep (se 1 (by rfl) ⟨632294, by rfl⟩ : syracuseStep 843059 = 1264589) B1264589
theorem B1367347 : Blo 806344 1367347 := bstep (se 1 (by rfl) ⟨1025510, by rfl⟩ : syracuseStep 1367347 = 2051021) B2051021
theorem B810291 : Blo 806344 810291 := bstep (se 1 (by rfl) ⟨607718, by rfl⟩ : syracuseStep 810291 = 1215437) B1215437
theorem B810307 : Blo 806344 810307 := bstep (se 1 (by rfl) ⟨607730, by rfl⟩ : syracuseStep 810307 = 1215461) B1215461
theorem B810323 : Blo 806344 810323 := bstep (se 1 (by rfl) ⟨607742, by rfl⟩ : syracuseStep 810323 = 1215485) B1215485
theorem B810339 : Blo 806344 810339 := bstep (se 1 (by rfl) ⟨607754, by rfl⟩ : syracuseStep 810339 = 1215509) B1215509
theorem B908707 : Blo 806344 908707 := bstep (se 1 (by rfl) ⟨681530, by rfl⟩ : syracuseStep 908707 = 1363061) B1363061
theorem B3071459 : Blo 806344 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B908851 : Blo 806344 908851 := bstep (se 1 (by rfl) ⟨681638, by rfl⟩ : syracuseStep 908851 = 1363277) B1363277
theorem B2186833 : Blo 806344 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B1531523 : Blo 806344 1531523 := bstep (se 1 (by rfl) ⟨1148642, by rfl⟩ : syracuseStep 1531523 = 2297285) B2297285
theorem B908995 : Blo 806344 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B1728209 : Blo 806344 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B3104561 : Blo 806344 3104561 := bstep (se 2 (by rfl) ⟨1164210, by rfl⟩ : syracuseStep 3104561 = 2328421) B2328421
theorem B909139 : Blo 806344 909139 := bstep (se 1 (by rfl) ⟨681854, by rfl⟩ : syracuseStep 909139 = 1363709) B1363709
theorem B1531811 : Blo 806344 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B909283 : Blo 806344 909283 := bstep (se 1 (by rfl) ⟨681962, by rfl⟩ : syracuseStep 909283 = 1363925) B1363925
theorem B1400851 : Blo 806344 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B1400899 : Blo 806344 1400899 := bstep (se 1 (by rfl) ⟨1050674, by rfl⟩ : syracuseStep 1400899 = 2101349) B2101349
theorem B4087907 : Blo 806344 4087907 := bstep (se 1 (by rfl) ⟨3065930, by rfl⟩ : syracuseStep 4087907 = 6131861) B6131861
theorem B1728611 : Blo 806344 1728611 := bstep (se 1 (by rfl) ⟨1296458, by rfl⟩ : syracuseStep 1728611 = 2592917) B2592917
theorem B3072113 : Blo 806344 3072113 := bstep (se 2 (by rfl) ⟨1152042, by rfl⟩ : syracuseStep 3072113 = 2304085) B2304085
theorem B909427 : Blo 806344 909427 := bstep (se 1 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 909427 = 1364141) B1364141
theorem B4907141 : Blo 806344 4907141 := bstep (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) B920089
theorem B5595299 : Blo 806344 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B909571 : Blo 806344 909571 := bstep (se 1 (by rfl) ⟨682178, by rfl⟩ : syracuseStep 909571 = 1364357) B1364357
theorem B7758179 : Blo 806344 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B909715 : Blo 806344 909715 := bstep (se 1 (by rfl) ⟨682286, by rfl⟩ : syracuseStep 909715 = 1364573) B1364573
theorem B909859 : Blo 806344 909859 := bstep (se 1 (by rfl) ⟨682394, by rfl⟩ : syracuseStep 909859 = 1364789) B1364789
theorem B910003 : Blo 806344 910003 := bstep (se 1 (by rfl) ⟨682502, by rfl⟩ : syracuseStep 910003 = 1365005) B1365005
theorem B910147 : Blo 806344 910147 := bstep (se 1 (by rfl) ⟨682610, by rfl⟩ : syracuseStep 910147 = 1365221) B1365221
theorem B1532753 : Blo 806344 1532753 := bstep (se 2 (by rfl) ⟨574782, by rfl⟩ : syracuseStep 1532753 = 1149565) B1149565
theorem B4088717 : Blo 806344 4088717 := bstep (se 3 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 4088717 = 1533269) B1533269
theorem B910291 : Blo 806344 910291 := bstep (se 1 (by rfl) ⟨682718, by rfl⟩ : syracuseStep 910291 = 1365437) B1365437
theorem B1729507 : Blo 806344 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B910435 : Blo 806344 910435 := bstep (se 1 (by rfl) ⟨682826, by rfl⟩ : syracuseStep 910435 = 1365653) B1365653
theorem B910579 : Blo 806344 910579 := bstep (se 1 (by rfl) ⟨682934, by rfl⟩ : syracuseStep 910579 = 1365869) B1365869
theorem B910723 : Blo 806344 910723 := bstep (se 1 (by rfl) ⟨683042, by rfl⟩ : syracuseStep 910723 = 1366085) B1366085
theorem B910867 : Blo 806344 910867 := bstep (se 1 (by rfl) ⟨683150, by rfl⟩ : syracuseStep 910867 = 1366301) B1366301
theorem B3073571 : Blo 806344 3073571 := bstep (se 1 (by rfl) ⟨2305178, by rfl⟩ : syracuseStep 3073571 = 4610357) B4610357
theorem B3073585 : Blo 806344 3073585 := bstep (se 2 (by rfl) ⟨1152594, by rfl⟩ : syracuseStep 3073585 = 2305189) B2305189
theorem B5170787 : Blo 806344 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B911011 : Blo 806344 911011 := bstep (se 1 (by rfl) ⟨683258, by rfl⟩ : syracuseStep 911011 = 1366517) B1366517
theorem B1533649 : Blo 806344 1533649 := bstep (se 2 (by rfl) ⟨575118, by rfl⟩ : syracuseStep 1533649 = 1150237) B1150237
theorem B3106531 : Blo 806344 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B1402625 : Blo 806344 1402625 := bstep (se 2 (by rfl) ⟨525984, by rfl⟩ : syracuseStep 1402625 = 1051969) B1051969
theorem B911155 : Blo 806344 911155 := bstep (se 1 (by rfl) ⟨683366, by rfl⟩ : syracuseStep 911155 = 1366733) B1366733
theorem B1533809 : Blo 806344 1533809 := bstep (se 2 (by rfl) ⟨575178, by rfl⟩ : syracuseStep 1533809 = 1150357) B1150357
theorem B8284045 : Blo 806344 8284045 := bstep (se 3 (by rfl) ⟨1553258, by rfl⟩ : syracuseStep 8284045 = 3106517) B3106517
theorem B911299 : Blo 806344 911299 := bstep (se 1 (by rfl) ⟨683474, by rfl⟩ : syracuseStep 911299 = 1366949) B1366949
theorem B911443 : Blo 806344 911443 := bstep (se 1 (by rfl) ⟨683582, by rfl⟩ : syracuseStep 911443 = 1367165) B1367165
theorem B14772365 : Blo 806344 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B911587 : Blo 806344 911587 := bstep (se 1 (by rfl) ⟨683690, by rfl⟩ : syracuseStep 911587 = 1367381) B1367381
theorem B10381553 : Blo 806344 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B1534211 : Blo 806344 1534211 := bstep (se 1 (by rfl) ⟨1150658, by rfl⟩ : syracuseStep 1534211 = 2301317) B2301317
theorem B6220273 : Blo 806344 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B5172173 : Blo 806344 5172173 := bstep (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) B1939565
theorem B3075043 : Blo 806344 3075043 := bstep (se 1 (by rfl) ⟨2306282, by rfl⟩ : syracuseStep 3075043 = 4612565) B4612565
theorem B1535107 : Blo 806344 1535107 := bstep (se 1 (by rfl) ⟨1151330, by rfl⟩ : syracuseStep 1535107 = 2302661) B2302661
theorem B13102307 : Blo 806344 13102307 := bstep (se 1 (by rfl) ⟨9826730, by rfl⟩ : syracuseStep 13102307 = 19653461) B19653461
theorem B1535267 : Blo 806344 1535267 := bstep (se 1 (by rfl) ⟨1151450, by rfl⟩ : syracuseStep 1535267 = 2302901) B2302901
theorem B5533069 : Blo 806344 5533069 := bstep (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) B2074901
theorem B2584163 : Blo 806344 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B4157027 : Blo 806344 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B3272333 : Blo 806344 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B4091633 : Blo 806344 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B22146929 : Blo 806344 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B1536337 : Blo 806344 1536337 := bstep (se 2 (by rfl) ⟨576126, by rfl⟩ : syracuseStep 1536337 = 1152253) B1152253
theorem B2585137 : Blo 806344 2585137 := bstep (se 2 (by rfl) ⟨969426, by rfl⟩ : syracuseStep 2585137 = 1938853) B1938853
theorem B4093091 : Blo 806344 4093091 := bstep (se 1 (by rfl) ⟨3069818, by rfl⟩ : syracuseStep 4093091 = 6139637) B6139637
theorem B1209521 : Blo 806344 1209521 := bstep (se 2 (by rfl) ⟨453570, by rfl⟩ : syracuseStep 1209521 = 907141) B907141
theorem B1209539 : Blo 806344 1209539 := bstep (se 1 (by rfl) ⟨907154, by rfl⟩ : syracuseStep 1209539 = 1814309) B1814309
theorem B1209569 : Blo 806344 1209569 := bstep (se 2 (by rfl) ⟨453588, by rfl⟩ : syracuseStep 1209569 = 907177) B907177
theorem B1209587 : Blo 806344 1209587 := bstep (se 1 (by rfl) ⟨907190, by rfl⟩ : syracuseStep 1209587 = 1814381) B1814381
theorem B4912397 : Blo 806344 4912397 := bstep (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) B1842149
theorem B1209617 : Blo 806344 1209617 := bstep (se 2 (by rfl) ⟨453606, by rfl⟩ : syracuseStep 1209617 = 907213) B907213
theorem B1209635 : Blo 806344 1209635 := bstep (se 1 (by rfl) ⟨907226, by rfl⟩ : syracuseStep 1209635 = 1814453) B1814453
theorem B1209665 : Blo 806344 1209665 := bstep (se 2 (by rfl) ⟨453624, by rfl⟩ : syracuseStep 1209665 = 907249) B907249
theorem B1209683 : Blo 806344 1209683 := bstep (se 1 (by rfl) ⟨907262, by rfl⟩ : syracuseStep 1209683 = 1814525) B1814525
theorem B1209713 : Blo 806344 1209713 := bstep (se 2 (by rfl) ⟨453642, by rfl⟩ : syracuseStep 1209713 = 907285) B907285
theorem B1537393 : Blo 806344 1537393 := bstep (se 2 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 1537393 = 1153045) B1153045
theorem B1209731 : Blo 806344 1209731 := bstep (se 1 (by rfl) ⟨907298, by rfl⟩ : syracuseStep 1209731 = 1814597) B1814597
theorem B1209761 : Blo 806344 1209761 := bstep (se 2 (by rfl) ⟨453660, by rfl⟩ : syracuseStep 1209761 = 907321) B907321
theorem B2618801 : Blo 806344 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B1209779 : Blo 806344 1209779 := bstep (se 1 (by rfl) ⟨907334, by rfl⟩ : syracuseStep 1209779 = 1814669) B1814669
theorem B1209809 : Blo 806344 1209809 := bstep (se 2 (by rfl) ⟨453678, by rfl⟩ : syracuseStep 1209809 = 907357) B907357
theorem B1209827 : Blo 806344 1209827 := bstep (se 1 (by rfl) ⟨907370, by rfl⟩ : syracuseStep 1209827 = 1814741) B1814741
theorem B1209857 : Blo 806344 1209857 := bstep (se 2 (by rfl) ⟨453696, by rfl⟩ : syracuseStep 1209857 = 907393) B907393
theorem B1209875 : Blo 806344 1209875 := bstep (se 1 (by rfl) ⟨907406, by rfl⟩ : syracuseStep 1209875 = 1814813) B1814813
theorem B1209905 : Blo 806344 1209905 := bstep (se 2 (by rfl) ⟨453714, by rfl⟩ : syracuseStep 1209905 = 907429) B907429
theorem B1209923 : Blo 806344 1209923 := bstep (se 1 (by rfl) ⟨907442, by rfl⟩ : syracuseStep 1209923 = 1814885) B1814885
theorem B1209953 : Blo 806344 1209953 := bstep (se 2 (by rfl) ⟨453732, by rfl⟩ : syracuseStep 1209953 = 907465) B907465
theorem B1209971 : Blo 806344 1209971 := bstep (se 1 (by rfl) ⟨907478, by rfl⟩ : syracuseStep 1209971 = 1814957) B1814957
theorem B1210001 : Blo 806344 1210001 := bstep (se 2 (by rfl) ⟨453750, by rfl⟩ : syracuseStep 1210001 = 907501) B907501
theorem B1210019 : Blo 806344 1210019 := bstep (se 1 (by rfl) ⟨907514, by rfl⟩ : syracuseStep 1210019 = 1815029) B1815029
theorem B1210049 : Blo 806344 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B3274445 : Blo 806344 3274445 := bstep (se 3 (by rfl) ⟨613958, by rfl⟩ : syracuseStep 3274445 = 1227917) B1227917
theorem B1210067 : Blo 806344 1210067 := bstep (se 1 (by rfl) ⟨907550, by rfl⟩ : syracuseStep 1210067 = 1815101) B1815101
theorem B1210097 : Blo 806344 1210097 := bstep (se 2 (by rfl) ⟨453786, by rfl⟩ : syracuseStep 1210097 = 907573) B907573
theorem B1210115 : Blo 806344 1210115 := bstep (se 1 (by rfl) ⟨907586, by rfl⟩ : syracuseStep 1210115 = 1815173) B1815173
theorem B1537795 : Blo 806344 1537795 := bstep (se 1 (by rfl) ⟨1153346, by rfl⟩ : syracuseStep 1537795 = 2306693) B2306693
theorem B1210145 : Blo 806344 1210145 := bstep (se 2 (by rfl) ⟨453804, by rfl⟩ : syracuseStep 1210145 = 907609) B907609
theorem B1537841 : Blo 806344 1537841 := bstep (se 2 (by rfl) ⟨576690, by rfl⟩ : syracuseStep 1537841 = 1153381) B1153381
theorem B1210163 : Blo 806344 1210163 := bstep (se 1 (by rfl) ⟨907622, by rfl⟩ : syracuseStep 1210163 = 1815245) B1815245
theorem B1210193 : Blo 806344 1210193 := bstep (se 2 (by rfl) ⟨453822, by rfl⟩ : syracuseStep 1210193 = 907645) B907645
theorem B1210211 : Blo 806344 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B2455409 : Blo 806344 2455409 := bstep (se 2 (by rfl) ⟨920778, by rfl⟩ : syracuseStep 2455409 = 1841557) B1841557
theorem B1210241 : Blo 806344 1210241 := bstep (se 2 (by rfl) ⟨453840, by rfl⟩ : syracuseStep 1210241 = 907681) B907681
theorem B1210259 : Blo 806344 1210259 := bstep (se 1 (by rfl) ⟨907694, by rfl⟩ : syracuseStep 1210259 = 1815389) B1815389
theorem B1210289 : Blo 806344 1210289 := bstep (se 2 (by rfl) ⟨453858, by rfl⟩ : syracuseStep 1210289 = 907717) B907717
theorem B1210307 : Blo 806344 1210307 := bstep (se 1 (by rfl) ⟨907730, by rfl⟩ : syracuseStep 1210307 = 1815461) B1815461
theorem B4093901 : Blo 806344 4093901 := bstep (se 3 (by rfl) ⟨767606, by rfl⟩ : syracuseStep 4093901 = 1535213) B1535213
theorem B1210337 : Blo 806344 1210337 := bstep (se 2 (by rfl) ⟨453876, by rfl⟩ : syracuseStep 1210337 = 907753) B907753
theorem B1210355 : Blo 806344 1210355 := bstep (se 1 (by rfl) ⟨907766, by rfl⟩ : syracuseStep 1210355 = 1815533) B1815533
theorem B6912013 : Blo 806344 6912013 := bstep (se 3 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 6912013 = 2592005) B2592005
theorem B1210385 : Blo 806344 1210385 := bstep (se 2 (by rfl) ⟨453894, by rfl⟩ : syracuseStep 1210385 = 907789) B907789
theorem B1210403 : Blo 806344 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B1210433 : Blo 806344 1210433 := bstep (se 2 (by rfl) ⟨453912, by rfl⟩ : syracuseStep 1210433 = 907825) B907825
theorem B1538129 : Blo 806344 1538129 := bstep (se 2 (by rfl) ⟨576798, by rfl⟩ : syracuseStep 1538129 = 1153597) B1153597
theorem B1210451 : Blo 806344 1210451 := bstep (se 1 (by rfl) ⟨907838, by rfl⟩ : syracuseStep 1210451 = 1815677) B1815677
theorem B1210481 : Blo 806344 1210481 := bstep (se 2 (by rfl) ⟨453930, by rfl⟩ : syracuseStep 1210481 = 907861) B907861
theorem B1210499 : Blo 806344 1210499 := bstep (se 1 (by rfl) ⟨907874, by rfl⟩ : syracuseStep 1210499 = 1815749) B1815749
theorem B17463437 : Blo 806344 17463437 := bstep (se 3 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 17463437 = 6548789) B6548789
theorem B1210529 : Blo 806344 1210529 := bstep (se 2 (by rfl) ⟨453948, by rfl⟩ : syracuseStep 1210529 = 907897) B907897
theorem B1210547 : Blo 806344 1210547 := bstep (se 1 (by rfl) ⟨907910, by rfl⟩ : syracuseStep 1210547 = 1815821) B1815821
theorem B2586829 : Blo 806344 2586829 := bstep (se 3 (by rfl) ⟨485030, by rfl⟩ : syracuseStep 2586829 = 970061) B970061
theorem B1210577 : Blo 806344 1210577 := bstep (se 2 (by rfl) ⟨453966, by rfl⟩ : syracuseStep 1210577 = 907933) B907933
theorem B1210595 : Blo 806344 1210595 := bstep (se 1 (by rfl) ⟨907946, by rfl⟩ : syracuseStep 1210595 = 1815893) B1815893
theorem B1210625 : Blo 806344 1210625 := bstep (se 2 (by rfl) ⟨453984, by rfl⟩ : syracuseStep 1210625 = 907969) B907969
theorem B1210643 : Blo 806344 1210643 := bstep (se 1 (by rfl) ⟨907982, by rfl⟩ : syracuseStep 1210643 = 1815965) B1815965
theorem B1210673 : Blo 806344 1210673 := bstep (se 2 (by rfl) ⟨454002, by rfl⟩ : syracuseStep 1210673 = 908005) B908005
theorem B1210691 : Blo 806344 1210691 := bstep (se 1 (by rfl) ⟨908018, by rfl⟩ : syracuseStep 1210691 = 1816037) B1816037
theorem B1210721 : Blo 806344 1210721 := bstep (se 2 (by rfl) ⟨454020, by rfl⟩ : syracuseStep 1210721 = 908041) B908041
theorem B1210739 : Blo 806344 1210739 := bstep (se 1 (by rfl) ⟨908054, by rfl⟩ : syracuseStep 1210739 = 1816109) B1816109
theorem B1210769 : Blo 806344 1210769 := bstep (se 2 (by rfl) ⟨454038, by rfl⟩ : syracuseStep 1210769 = 908077) B908077
theorem B2619811 : Blo 806344 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B1210787 : Blo 806344 1210787 := bstep (se 1 (by rfl) ⟨908090, by rfl⟩ : syracuseStep 1210787 = 1816181) B1816181
theorem B1210817 : Blo 806344 1210817 := bstep (se 2 (by rfl) ⟨454056, by rfl⟩ : syracuseStep 1210817 = 908113) B908113
theorem B1210835 : Blo 806344 1210835 := bstep (se 1 (by rfl) ⟨908126, by rfl⟩ : syracuseStep 1210835 = 1816253) B1816253
theorem B1210865 : Blo 806344 1210865 := bstep (se 2 (by rfl) ⟨454074, by rfl⟩ : syracuseStep 1210865 = 908149) B908149
theorem B1210883 : Blo 806344 1210883 := bstep (se 1 (by rfl) ⟨908162, by rfl⟩ : syracuseStep 1210883 = 1816325) B1816325
theorem B1210913 : Blo 806344 1210913 := bstep (se 2 (by rfl) ⟨454092, by rfl⟩ : syracuseStep 1210913 = 908185) B908185
theorem B2456099 : Blo 806344 2456099 := bstep (se 1 (by rfl) ⟨1842074, by rfl⟩ : syracuseStep 2456099 = 3684149) B3684149
theorem B1210931 : Blo 806344 1210931 := bstep (se 1 (by rfl) ⟨908198, by rfl⟩ : syracuseStep 1210931 = 1816397) B1816397
theorem B1210961 : Blo 806344 1210961 := bstep (se 2 (by rfl) ⟨454110, by rfl⟩ : syracuseStep 1210961 = 908221) B908221
theorem B1210979 : Blo 806344 1210979 := bstep (se 1 (by rfl) ⟨908234, by rfl⟩ : syracuseStep 1210979 = 1816469) B1816469
theorem B1211009 : Blo 806344 1211009 := bstep (se 2 (by rfl) ⟨454128, by rfl⟩ : syracuseStep 1211009 = 908257) B908257
theorem B1964675 : Blo 806344 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B1211027 : Blo 806344 1211027 := bstep (se 1 (by rfl) ⟨908270, by rfl⟩ : syracuseStep 1211027 = 1816541) B1816541
theorem B1211057 : Blo 806344 1211057 := bstep (se 2 (by rfl) ⟨454146, by rfl⟩ : syracuseStep 1211057 = 908293) B908293
theorem B1211075 : Blo 806344 1211075 := bstep (se 1 (by rfl) ⟨908306, by rfl⟩ : syracuseStep 1211075 = 1816613) B1816613
theorem B1211105 : Blo 806344 1211105 := bstep (se 2 (by rfl) ⟨454164, by rfl⟩ : syracuseStep 1211105 = 908329) B908329
theorem B1211123 : Blo 806344 1211123 := bstep (se 1 (by rfl) ⟨908342, by rfl⟩ : syracuseStep 1211123 = 1816685) B1816685
theorem B1211153 : Blo 806344 1211153 := bstep (se 2 (by rfl) ⟨454182, by rfl⟩ : syracuseStep 1211153 = 908365) B908365
theorem B1211171 : Blo 806344 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B1211201 : Blo 806344 1211201 := bstep (se 2 (by rfl) ⟨454200, by rfl⟩ : syracuseStep 1211201 = 908401) B908401
theorem B1211219 : Blo 806344 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B1211249 : Blo 806344 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B1211267 : Blo 806344 1211267 := bstep (se 1 (by rfl) ⟨908450, by rfl⟩ : syracuseStep 1211267 = 1816901) B1816901
theorem B4914053 : Blo 806344 4914053 := bstep (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) B921385
theorem B1211297 : Blo 806344 1211297 := bstep (se 2 (by rfl) ⟨454236, by rfl⟩ : syracuseStep 1211297 = 908473) B908473
theorem B1211315 : Blo 806344 1211315 := bstep (se 1 (by rfl) ⟨908486, by rfl⟩ : syracuseStep 1211315 = 1816973) B1816973
theorem B1211345 : Blo 806344 1211345 := bstep (se 2 (by rfl) ⟨454254, by rfl⟩ : syracuseStep 1211345 = 908509) B908509
theorem B1211363 : Blo 806344 1211363 := bstep (se 1 (by rfl) ⟨908522, by rfl⟩ : syracuseStep 1211363 = 1817045) B1817045
theorem B10517489 : Blo 806344 10517489 := bstep (se 2 (by rfl) ⟨3944058, by rfl⟩ : syracuseStep 10517489 = 7888117) B7888117
theorem B1211393 : Blo 806344 1211393 := bstep (se 2 (by rfl) ⟨454272, by rfl⟩ : syracuseStep 1211393 = 908545) B908545
theorem B3111949 : Blo 806344 3111949 := bstep (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) B1166981
theorem B1211411 : Blo 806344 1211411 := bstep (se 1 (by rfl) ⟨908558, by rfl⟩ : syracuseStep 1211411 = 1817117) B1817117
theorem B1211441 : Blo 806344 1211441 := bstep (se 2 (by rfl) ⟨454290, by rfl⟩ : syracuseStep 1211441 = 908581) B908581
theorem B1211459 : Blo 806344 1211459 := bstep (se 1 (by rfl) ⟨908594, by rfl⟩ : syracuseStep 1211459 = 1817189) B1817189
theorem B1211489 : Blo 806344 1211489 := bstep (se 2 (by rfl) ⟨454308, by rfl⟩ : syracuseStep 1211489 = 908617) B908617
theorem B1211507 : Blo 806344 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B982147 : Blo 806344 982147 := bstep (se 1 (by rfl) ⟨736610, by rfl⟩ : syracuseStep 982147 = 1473221) B1473221
theorem B11041933 : Blo 806344 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B1211537 : Blo 806344 1211537 := bstep (se 2 (by rfl) ⟨454326, by rfl⟩ : syracuseStep 1211537 = 908653) B908653
theorem B1211555 : Blo 806344 1211555 := bstep (se 1 (by rfl) ⟨908666, by rfl⟩ : syracuseStep 1211555 = 1817333) B1817333
theorem B1211585 : Blo 806344 1211585 := bstep (se 2 (by rfl) ⟨454344, by rfl⟩ : syracuseStep 1211585 = 908689) B908689
theorem B1211603 : Blo 806344 1211603 := bstep (se 1 (by rfl) ⟨908702, by rfl⟩ : syracuseStep 1211603 = 1817405) B1817405
theorem B1211633 : Blo 806344 1211633 := bstep (se 2 (by rfl) ⟨454362, by rfl⟩ : syracuseStep 1211633 = 908725) B908725
theorem B1211651 : Blo 806344 1211651 := bstep (se 1 (by rfl) ⟨908738, by rfl⟩ : syracuseStep 1211651 = 1817477) B1817477
theorem B1211681 : Blo 806344 1211681 := bstep (se 2 (by rfl) ⟨454380, by rfl⟩ : syracuseStep 1211681 = 908761) B908761
theorem B1211699 : Blo 806344 1211699 := bstep (se 1 (by rfl) ⟨908774, by rfl⟩ : syracuseStep 1211699 = 1817549) B1817549
theorem B6913349 : Blo 806344 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B1211729 : Blo 806344 1211729 := bstep (se 2 (by rfl) ⟨454398, by rfl⟩ : syracuseStep 1211729 = 908797) B908797
theorem B1211747 : Blo 806344 1211747 := bstep (se 1 (by rfl) ⟨908810, by rfl⟩ : syracuseStep 1211747 = 1817621) B1817621
theorem B2522477 : Blo 806344 2522477 := bstep (se 3 (by rfl) ⟨472964, by rfl⟩ : syracuseStep 2522477 = 945929) B945929
theorem B1211777 : Blo 806344 1211777 := bstep (se 2 (by rfl) ⟨454416, by rfl⟩ : syracuseStep 1211777 = 908833) B908833
theorem B1211795 : Blo 806344 1211795 := bstep (se 1 (by rfl) ⟨908846, by rfl⟩ : syracuseStep 1211795 = 1817693) B1817693
theorem B1211825 : Blo 806344 1211825 := bstep (se 2 (by rfl) ⟨454434, by rfl⟩ : syracuseStep 1211825 = 908869) B908869
theorem B1211843 : Blo 806344 1211843 := bstep (se 1 (by rfl) ⟨908882, by rfl⟩ : syracuseStep 1211843 = 1817765) B1817765
theorem B1211873 : Blo 806344 1211873 := bstep (se 2 (by rfl) ⟨454452, by rfl⟩ : syracuseStep 1211873 = 908905) B908905
theorem B1211891 : Blo 806344 1211891 := bstep (se 1 (by rfl) ⟨908918, by rfl⟩ : syracuseStep 1211891 = 1817837) B1817837
theorem B1211921 : Blo 806344 1211921 := bstep (se 2 (by rfl) ⟨454470, by rfl⟩ : syracuseStep 1211921 = 908941) B908941
theorem B1211939 : Blo 806344 1211939 := bstep (se 1 (by rfl) ⟨908954, by rfl⟩ : syracuseStep 1211939 = 1817909) B1817909
theorem B1211969 : Blo 806344 1211969 := bstep (se 2 (by rfl) ⟨454488, by rfl⟩ : syracuseStep 1211969 = 908977) B908977
theorem B1211987 : Blo 806344 1211987 := bstep (se 1 (by rfl) ⟨908990, by rfl⟩ : syracuseStep 1211987 = 1817981) B1817981
theorem B1212017 : Blo 806344 1212017 := bstep (se 2 (by rfl) ⟨454506, by rfl⟩ : syracuseStep 1212017 = 909013) B909013
theorem B1212035 : Blo 806344 1212035 := bstep (se 1 (by rfl) ⟨909026, by rfl⟩ : syracuseStep 1212035 = 1818053) B1818053
theorem B1212065 : Blo 806344 1212065 := bstep (se 2 (by rfl) ⟨454524, by rfl⟩ : syracuseStep 1212065 = 909049) B909049
theorem B1212083 : Blo 806344 1212083 := bstep (se 1 (by rfl) ⟨909062, by rfl⟩ : syracuseStep 1212083 = 1818125) B1818125
theorem B1212113 : Blo 806344 1212113 := bstep (se 2 (by rfl) ⟨454542, by rfl⟩ : syracuseStep 1212113 = 909085) B909085
theorem B1212131 : Blo 806344 1212131 := bstep (se 1 (by rfl) ⟨909098, by rfl⟩ : syracuseStep 1212131 = 1818197) B1818197
theorem B1212161 : Blo 806344 1212161 := bstep (se 2 (by rfl) ⟨454560, by rfl⟩ : syracuseStep 1212161 = 909121) B909121
theorem B1212179 : Blo 806344 1212179 := bstep (se 1 (by rfl) ⟨909134, by rfl⟩ : syracuseStep 1212179 = 1818269) B1818269
theorem B1212209 : Blo 806344 1212209 := bstep (se 2 (by rfl) ⟨454578, by rfl⟩ : syracuseStep 1212209 = 909157) B909157
theorem B1212227 : Blo 806344 1212227 := bstep (se 1 (by rfl) ⟨909170, by rfl⟩ : syracuseStep 1212227 = 1818341) B1818341
theorem B1212257 : Blo 806344 1212257 := bstep (se 2 (by rfl) ⟨454596, by rfl⟩ : syracuseStep 1212257 = 909193) B909193
theorem B1212275 : Blo 806344 1212275 := bstep (se 1 (by rfl) ⟨909206, by rfl⟩ : syracuseStep 1212275 = 1818413) B1818413
theorem B1212305 : Blo 806344 1212305 := bstep (se 2 (by rfl) ⟨454614, by rfl⟩ : syracuseStep 1212305 = 909229) B909229
theorem B1212323 : Blo 806344 1212323 := bstep (se 1 (by rfl) ⟨909242, by rfl⟩ : syracuseStep 1212323 = 1818485) B1818485
theorem B1212353 : Blo 806344 1212353 := bstep (se 2 (by rfl) ⟨454632, by rfl⟩ : syracuseStep 1212353 = 909265) B909265
theorem B2588611 : Blo 806344 2588611 := bstep (se 1 (by rfl) ⟨1941458, by rfl⟩ : syracuseStep 2588611 = 3882917) B3882917
theorem B1212371 : Blo 806344 1212371 := bstep (se 1 (by rfl) ⟨909278, by rfl⟩ : syracuseStep 1212371 = 1818557) B1818557
theorem B1212401 : Blo 806344 1212401 := bstep (se 2 (by rfl) ⟨454650, by rfl⟩ : syracuseStep 1212401 = 909301) B909301
theorem B1867801 : Blo 806344 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B26214475 : Blo 806344 26214475 := bstep (se 1 (by rfl) ⟨19660856, by rfl⟩ : syracuseStep 26214475 = 39321713) B39321713
theorem B3276875 : Blo 806344 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B1212491 : Blo 806344 1212491 := bstep (se 1 (by rfl) ⟨909368, by rfl⟩ : syracuseStep 1212491 = 1818737) B1818737
theorem B1212503 : Blo 806344 1212503 := bstep (se 1 (by rfl) ⟨909377, by rfl⟩ : syracuseStep 1212503 = 1818755) B1818755
theorem B1867865 : Blo 806344 1867865 := bstep (se 2 (by rfl) ⟨700449, by rfl⟩ : syracuseStep 1867865 = 1400899) B1400899
theorem B1212569 : Blo 806344 1212569 := bstep (se 2 (by rfl) ⟨454713, by rfl⟩ : syracuseStep 1212569 = 909427) B909427
theorem B1212683 : Blo 806344 1212683 := bstep (se 1 (by rfl) ⟨909512, by rfl⟩ : syracuseStep 1212683 = 1819025) B1819025
theorem B1212695 : Blo 806344 1212695 := bstep (se 1 (by rfl) ⟨909521, by rfl⟩ : syracuseStep 1212695 = 1819043) B1819043
theorem B4096331 : Blo 806344 4096331 := bstep (se 1 (by rfl) ⟨3072248, by rfl⟩ : syracuseStep 4096331 = 6144497) B6144497
theorem B1212761 : Blo 806344 1212761 := bstep (se 2 (by rfl) ⟨454785, by rfl⟩ : syracuseStep 1212761 = 909571) B909571
theorem B6127973 : Blo 806344 6127973 := bstep (se 4 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 6127973 = 1148995) B1148995
theorem B1212875 : Blo 806344 1212875 := bstep (se 1 (by rfl) ⟨909656, by rfl⟩ : syracuseStep 1212875 = 1819313) B1819313
theorem B1212887 : Blo 806344 1212887 := bstep (se 1 (by rfl) ⟨909665, by rfl⟩ : syracuseStep 1212887 = 1819331) B1819331
theorem B1212953 : Blo 806344 1212953 := bstep (se 2 (by rfl) ⟨454857, by rfl⟩ : syracuseStep 1212953 = 909715) B909715
theorem B1213067 : Blo 806344 1213067 := bstep (se 1 (by rfl) ⟨909800, by rfl⟩ : syracuseStep 1213067 = 1819601) B1819601
theorem B1213079 : Blo 806344 1213079 := bstep (se 1 (by rfl) ⟨909809, by rfl⟩ : syracuseStep 1213079 = 1819619) B1819619
theorem B2458291 : Blo 806344 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B1213145 : Blo 806344 1213145 := bstep (se 2 (by rfl) ⟨454929, by rfl⟩ : syracuseStep 1213145 = 909859) B909859
theorem B6128459 : Blo 806344 6128459 := bstep (se 1 (by rfl) ⟨4596344, by rfl⟩ : syracuseStep 6128459 = 9192689) B9192689
theorem B1213259 : Blo 806344 1213259 := bstep (se 1 (by rfl) ⟨909944, by rfl⟩ : syracuseStep 1213259 = 1819889) B1819889
theorem B1213271 : Blo 806344 1213271 := bstep (se 1 (by rfl) ⟨909953, by rfl⟩ : syracuseStep 1213271 = 1819907) B1819907
theorem B1213337 : Blo 806344 1213337 := bstep (se 2 (by rfl) ⟨455001, by rfl⟩ : syracuseStep 1213337 = 910003) B910003
theorem B1213451 : Blo 806344 1213451 := bstep (se 1 (by rfl) ⟨910088, by rfl⟩ : syracuseStep 1213451 = 1820177) B1820177
theorem B1213463 : Blo 806344 1213463 := bstep (se 1 (by rfl) ⟨910097, by rfl⟩ : syracuseStep 1213463 = 1820195) B1820195
theorem B1213529 : Blo 806344 1213529 := bstep (se 2 (by rfl) ⟨455073, by rfl⟩ : syracuseStep 1213529 = 910147) B910147
theorem B1148107 : Blo 806344 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B1213643 : Blo 806344 1213643 := bstep (se 1 (by rfl) ⟨910232, by rfl⟩ : syracuseStep 1213643 = 1820465) B1820465
theorem B1213655 : Blo 806344 1213655 := bstep (se 1 (by rfl) ⟨910241, by rfl⟩ : syracuseStep 1213655 = 1820483) B1820483
theorem B1213721 : Blo 806344 1213721 := bstep (se 2 (by rfl) ⟨455145, by rfl⟩ : syracuseStep 1213721 = 910291) B910291
theorem B1312075 : Blo 806344 1312075 := bstep (se 1 (by rfl) ⟨984056, by rfl⟩ : syracuseStep 1312075 = 1968113) B1968113
theorem B1213835 : Blo 806344 1213835 := bstep (se 1 (by rfl) ⟨910376, by rfl⟩ : syracuseStep 1213835 = 1820753) B1820753
theorem B1213847 : Blo 806344 1213847 := bstep (se 1 (by rfl) ⟨910385, by rfl⟩ : syracuseStep 1213847 = 1820771) B1820771
theorem B1213913 : Blo 806344 1213913 := bstep (se 2 (by rfl) ⟨455217, by rfl⟩ : syracuseStep 1213913 = 910435) B910435
theorem B15926797 : Blo 806344 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B1214027 : Blo 806344 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B1214039 : Blo 806344 1214039 := bstep (se 1 (by rfl) ⟨910529, by rfl⟩ : syracuseStep 1214039 = 1821059) B1821059
theorem B1214105 : Blo 806344 1214105 := bstep (se 2 (by rfl) ⟨455289, by rfl⟩ : syracuseStep 1214105 = 910579) B910579
theorem B1476311 : Blo 806344 1476311 := bstep (se 1 (by rfl) ⟨1107233, by rfl⟩ : syracuseStep 1476311 = 2214467) B2214467
theorem B1214219 : Blo 806344 1214219 := bstep (se 1 (by rfl) ⟨910664, by rfl⟩ : syracuseStep 1214219 = 1821329) B1821329
theorem B1214231 : Blo 806344 1214231 := bstep (se 1 (by rfl) ⟨910673, by rfl⟩ : syracuseStep 1214231 = 1821347) B1821347
theorem B1214297 : Blo 806344 1214297 := bstep (se 2 (by rfl) ⟨455361, by rfl⟩ : syracuseStep 1214297 = 910723) B910723
theorem B1214411 : Blo 806344 1214411 := bstep (se 1 (by rfl) ⟨910808, by rfl⟩ : syracuseStep 1214411 = 1821617) B1821617
theorem B1214423 : Blo 806344 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B2721815 : Blo 806344 2721815 := bstep (se 1 (by rfl) ⟨2041361, by rfl⟩ : syracuseStep 2721815 = 4082723) B4082723
theorem B1214489 : Blo 806344 1214489 := bstep (se 2 (by rfl) ⟨455433, by rfl⟩ : syracuseStep 1214489 = 910867) B910867
theorem B4098113 : Blo 806344 4098113 := bstep (se 2 (by rfl) ⟨1536792, by rfl⟩ : syracuseStep 4098113 = 3073585) B3073585
theorem B15763531 : Blo 806344 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B1214603 : Blo 806344 1214603 := bstep (se 1 (by rfl) ⟨910952, by rfl⟩ : syracuseStep 1214603 = 1821905) B1821905
theorem B1214615 : Blo 806344 1214615 := bstep (se 1 (by rfl) ⟨910961, by rfl⟩ : syracuseStep 1214615 = 1821923) B1821923
theorem B1214681 : Blo 806344 1214681 := bstep (se 2 (by rfl) ⟨455505, by rfl⟩ : syracuseStep 1214681 = 911011) B911011
theorem B6916387 : Blo 806344 6916387 := bstep (se 1 (by rfl) ⟨5187290, by rfl⟩ : syracuseStep 6916387 = 10374581) B10374581
theorem B1214795 : Blo 806344 1214795 := bstep (se 1 (by rfl) ⟨911096, by rfl⟩ : syracuseStep 1214795 = 1822193) B1822193
theorem B1214807 : Blo 806344 1214807 := bstep (se 1 (by rfl) ⟨911105, by rfl⟩ : syracuseStep 1214807 = 1822211) B1822211
theorem B1149337 : Blo 806344 1149337 := bstep (se 2 (by rfl) ⟨431001, by rfl⟩ : syracuseStep 1149337 = 862003) B862003
theorem B1214873 : Blo 806344 1214873 := bstep (se 2 (by rfl) ⟨455577, by rfl⟩ : syracuseStep 1214873 = 911155) B911155
theorem B1214987 : Blo 806344 1214987 := bstep (se 1 (by rfl) ⟨911240, by rfl⟩ : syracuseStep 1214987 = 1822481) B1822481
theorem B11045393 : Blo 806344 11045393 := bstep (se 2 (by rfl) ⟨4142022, by rfl⟩ : syracuseStep 11045393 = 8284045) B8284045
theorem B1214999 : Blo 806344 1214999 := bstep (se 1 (by rfl) ⟨911249, by rfl⟩ : syracuseStep 1214999 = 1822499) B1822499
theorem B2722355 : Blo 806344 2722355 := bstep (se 1 (by rfl) ⟨2041766, by rfl⟩ : syracuseStep 2722355 = 4083533) B4083533
theorem B1215065 : Blo 806344 1215065 := bstep (se 2 (by rfl) ⟨455649, by rfl⟩ : syracuseStep 1215065 = 911299) B911299
theorem B2919005 : Blo 806344 2919005 := bstep (se 3 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 2919005 = 1094627) B1094627
theorem B5900951 : Blo 806344 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B1215179 : Blo 806344 1215179 := bstep (se 1 (by rfl) ⟨911384, by rfl⟩ : syracuseStep 1215179 = 1822769) B1822769
theorem B1215191 : Blo 806344 1215191 := bstep (se 1 (by rfl) ⟨911393, by rfl⟩ : syracuseStep 1215191 = 1822787) B1822787
theorem B1215257 : Blo 806344 1215257 := bstep (se 2 (by rfl) ⟨455721, by rfl⟩ : syracuseStep 1215257 = 911443) B911443
theorem B2722625 : Blo 806344 2722625 := bstep (se 2 (by rfl) ⟨1020984, by rfl⟩ : syracuseStep 2722625 = 2041969) B2041969
theorem B2296669 : Blo 806344 2296669 := bstep (se 3 (by rfl) ⟨430625, by rfl⟩ : syracuseStep 2296669 = 861251) B861251
theorem B1215371 : Blo 806344 1215371 := bstep (se 1 (by rfl) ⟨911528, by rfl⟩ : syracuseStep 1215371 = 1823057) B1823057
theorem B1215383 : Blo 806344 1215383 := bstep (se 1 (by rfl) ⟨911537, by rfl⟩ : syracuseStep 1215383 = 1823075) B1823075
theorem B1215449 : Blo 806344 1215449 := bstep (se 2 (by rfl) ⟨455793, by rfl⟩ : syracuseStep 1215449 = 911587) B911587
theorem B2297011 : Blo 806344 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B8293697 : Blo 806344 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B2723165 : Blo 806344 2723165 := bstep (se 3 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 2723165 = 1021187) B1021187
theorem B1642007 : Blo 806344 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B1150681 : Blo 806344 1150681 := bstep (se 2 (by rfl) ⟨431505, by rfl⟩ : syracuseStep 1150681 = 863011) B863011
theorem B1150795 : Blo 806344 1150795 := bstep (se 1 (by rfl) ⟨863096, by rfl⟩ : syracuseStep 1150795 = 1726193) B1726193
theorem B4100057 : Blo 806344 4100057 := bstep (se 2 (by rfl) ⟨1537521, by rfl⟩ : syracuseStep 4100057 = 3075043) B3075043
theorem B2297945 : Blo 806344 2297945 := bstep (se 2 (by rfl) ⟨861729, by rfl⟩ : syracuseStep 2297945 = 1723459) B1723459
theorem B1577267 : Blo 806344 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B2724299 : Blo 806344 2724299 := bstep (se 1 (by rfl) ⟨2043224, by rfl⟩ : syracuseStep 2724299 = 4086449) B4086449
theorem B7377425 : Blo 806344 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B2724569 : Blo 806344 2724569 := bstep (se 2 (by rfl) ⟨1021713, by rfl⟩ : syracuseStep 2724569 = 2043427) B2043427
theorem B9966341 : Blo 806344 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B1021015 : Blo 806344 1021015 := bstep (se 1 (by rfl) ⟨765761, by rfl⟩ : syracuseStep 1021015 = 1531523) B1531523
theorem B1152139 : Blo 806344 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B2069707 : Blo 806344 2069707 := bstep (se 1 (by rfl) ⟨1552280, by rfl⟩ : syracuseStep 2069707 = 3104561) B3104561
theorem B2725271 : Blo 806344 2725271 := bstep (se 1 (by rfl) ⟨2043953, by rfl⟩ : syracuseStep 2725271 = 4087907) B4087907
theorem B1152407 : Blo 806344 1152407 := bstep (se 1 (by rfl) ⟨864305, by rfl⟩ : syracuseStep 1152407 = 1728611) B1728611
theorem B2299357 : Blo 806344 2299357 := bstep (se 3 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 2299357 = 862259) B862259
theorem B4101677 : Blo 806344 4101677 := bstep (se 3 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 4101677 = 1538129) B1538129
theorem B2299585 : Blo 806344 2299585 := bstep (se 2 (by rfl) ⟨862344, by rfl⟩ : syracuseStep 2299585 = 1724689) B1724689
theorem B3938179 : Blo 806344 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B1021835 : Blo 806344 1021835 := bstep (se 1 (by rfl) ⟨766376, by rfl⟩ : syracuseStep 1021835 = 1532753) B1532753
theorem B2725811 : Blo 806344 2725811 := bstep (se 1 (by rfl) ⟨2044358, by rfl⟩ : syracuseStep 2725811 = 4088717) B4088717
theorem B2758679 : Blo 806344 2758679 := bstep (se 1 (by rfl) ⟨2069009, by rfl⟩ : syracuseStep 2758679 = 4138019) B4138019
theorem B2299927 : Blo 806344 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B6133805 : Blo 806344 6133805 := bstep (se 3 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 6133805 = 2300177) B2300177
theorem B2627635 : Blo 806344 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B3446849 : Blo 806344 3446849 := bstep (se 2 (by rfl) ⟨1292568, by rfl⟩ : syracuseStep 3446849 = 2585137) B2585137
theorem B2726081 : Blo 806344 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B1153369 : Blo 806344 1153369 := bstep (se 2 (by rfl) ⟨432513, by rfl⟩ : syracuseStep 1153369 = 865027) B865027
theorem B3447191 : Blo 806344 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B1022539 : Blo 806344 1022539 := bstep (se 1 (by rfl) ⟨766904, by rfl⟩ : syracuseStep 1022539 = 1533809) B1533809
theorem B8395415 : Blo 806344 8395415 := bstep (se 1 (by rfl) ⟨6296561, by rfl⟩ : syracuseStep 8395415 = 12593123) B12593123
theorem B2300633 : Blo 806344 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B2726621 : Blo 806344 2726621 := bstep (se 3 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 2726621 = 1022483) B1022483
theorem B6921035 : Blo 806344 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B1022807 : Blo 806344 1022807 := bstep (se 1 (by rfl) ⟨767105, by rfl⟩ : syracuseStep 1022807 = 1534211) B1534211
theorem B1383307 : Blo 806344 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B3448115 : Blo 806344 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B1023511 : Blo 806344 1023511 := bstep (se 1 (by rfl) ⟨767633, by rfl⟩ : syracuseStep 1023511 = 1535267) B1535267
theorem B3284659 : Blo 806344 3284659 := bstep (se 1 (by rfl) ⟨2463494, by rfl⟩ : syracuseStep 3284659 = 4926989) B4926989
theorem B5185241 : Blo 806344 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B2727755 : Blo 806344 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B9216017 : Blo 806344 9216017 := bstep (se 2 (by rfl) ⟨3456006, by rfl⟩ : syracuseStep 9216017 = 6912013) B6912013
theorem B53157941 : Blo 806344 53157941 := bstep (se 5 (by rfl) ⟨2491778, by rfl⟩ : syracuseStep 53157941 = 4983557) B4983557
theorem B4595777 : Blo 806344 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B2728025 : Blo 806344 2728025 := bstep (se 2 (by rfl) ⟨1023009, by rfl⟩ : syracuseStep 2728025 = 2046019) B2046019
theorem B3449105 : Blo 806344 3449105 := bstep (se 2 (by rfl) ⟨1293414, by rfl⟩ : syracuseStep 3449105 = 2586829) B2586829
theorem B2302273 : Blo 806344 2302273 := bstep (se 2 (by rfl) ⟨863352, by rfl⟩ : syracuseStep 2302273 = 1726705) B1726705
theorem B2728727 : Blo 806344 2728727 := bstep (se 1 (by rfl) ⟨2046545, by rfl⟩ : syracuseStep 2728727 = 4093091) B4093091
theorem B5186369 : Blo 806344 5186369 := bstep (se 2 (by rfl) ⟨1944888, by rfl⟩ : syracuseStep 5186369 = 3889777) B3889777
theorem B1123159 : Blo 806344 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B13116259 : Blo 806344 13116259 := bstep (se 1 (by rfl) ⟨9837194, by rfl⟩ : syracuseStep 13116259 = 19674389) B19674389
theorem B6890417 : Blo 806344 6890417 := bstep (se 2 (by rfl) ⟨2583906, by rfl⟩ : syracuseStep 6890417 = 5167813) B5167813
theorem B1745867 : Blo 806344 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B1025227 : Blo 806344 1025227 := bstep (se 1 (by rfl) ⟨768920, by rfl⟩ : syracuseStep 1025227 = 1537841) B1537841
theorem B2041139 : Blo 806344 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B2729267 : Blo 806344 2729267 := bstep (se 1 (by rfl) ⟨2046950, by rfl⟩ : syracuseStep 2729267 = 4093901) B4093901
theorem B4662659 : Blo 806344 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B11642291 : Blo 806344 11642291 := bstep (se 1 (by rfl) ⟨8731718, by rfl⟩ : syracuseStep 11642291 = 17463437) B17463437
theorem B14722577 : Blo 806344 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B2729537 : Blo 806344 2729537 := bstep (se 2 (by rfl) ⟨1023576, by rfl⟩ : syracuseStep 2729537 = 2047153) B2047153
theorem B2041433 : Blo 806344 2041433 := bstep (se 2 (by rfl) ⟨765537, by rfl⟩ : syracuseStep 2041433 = 1531075) B1531075
theorem B6891101 : Blo 806344 6891101 := bstep (se 3 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 6891101 = 2584163) B2584163
theorem B8726221 : Blo 806344 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B2107225 : Blo 806344 2107225 := bstep (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) B1580419
theorem B6137693 : Blo 806344 6137693 := bstep (se 3 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 6137693 = 2301635) B2301635
theorem B9348965 : Blo 806344 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B2730077 : Blo 806344 2730077 := bstep (se 3 (by rfl) ⟨511889, by rfl⟩ : syracuseStep 2730077 = 1023779) B1023779
theorem B2074841 : Blo 806344 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B1681651 : Blo 806344 1681651 := bstep (se 1 (by rfl) ⟨1261238, by rfl⟩ : syracuseStep 1681651 = 2522477) B2522477
theorem B4598167 : Blo 806344 4598167 := bstep (se 1 (by rfl) ⟨3448625, by rfl⟩ : syracuseStep 4598167 = 6897251) B6897251
theorem B1681817 : Blo 806344 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B3451481 : Blo 806344 3451481 := bstep (se 2 (by rfl) ⟨1294305, by rfl⟩ : syracuseStep 3451481 = 2588611) B2588611
theorem B2960003 : Blo 806344 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B3451565 : Blo 806344 3451565 := bstep (se 3 (by rfl) ⟨647168, by rfl⟩ : syracuseStep 3451565 = 1294337) B1294337
theorem B14920433 : Blo 806344 14920433 := bstep (se 2 (by rfl) ⟨5595162, by rfl⟩ : syracuseStep 14920433 = 11190325) B11190325
theorem B9218933 : Blo 806344 9218933 := bstep (se 5 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 9218933 = 864275) B864275
theorem B3779531 : Blo 806344 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B1846273 : Blo 806344 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B2043083 : Blo 806344 2043083 := bstep (se 1 (by rfl) ⟨1532312, by rfl⟩ : syracuseStep 2043083 = 3064625) B3064625
theorem B2731211 : Blo 806344 2731211 := bstep (se 1 (by rfl) ⟨2048408, by rfl⟩ : syracuseStep 2731211 = 4096817) B4096817
theorem B7384355 : Blo 806344 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B4369729 : Blo 806344 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B2731481 : Blo 806344 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B863831 : Blo 806344 863831 := bstep (se 1 (by rfl) ⟨647873, by rfl⟩ : syracuseStep 863831 = 1295747) B1295747
theorem B7777943 : Blo 806344 7777943 := bstep (se 1 (by rfl) ⟨5833457, by rfl⟩ : syracuseStep 7777943 = 11666915) B11666915
theorem B1552343 : Blo 806344 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B1814489 : Blo 806344 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B2306009 : Blo 806344 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B1814579 : Blo 806344 1814579 := bstep (se 1 (by rfl) ⟨1360934, by rfl⟩ : syracuseStep 1814579 = 2721869) B2721869
theorem B27308107 : Blo 806344 27308107 := bstep (se 1 (by rfl) ⟨20481080, by rfl⟩ : syracuseStep 27308107 = 40962161) B40962161
theorem B1814615 : Blo 806344 1814615 := bstep (se 1 (by rfl) ⟨1360961, by rfl⟩ : syracuseStep 1814615 = 2721923) B2721923
theorem B2732183 : Blo 806344 2732183 := bstep (se 1 (by rfl) ⟨2049137, by rfl⟩ : syracuseStep 2732183 = 4098275) B4098275
theorem B2044055 : Blo 806344 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B1814795 : Blo 806344 1814795 := bstep (se 1 (by rfl) ⟨1361096, by rfl⟩ : syracuseStep 1814795 = 2722193) B2722193
theorem B864523 : Blo 806344 864523 := bstep (se 1 (by rfl) ⟨648392, by rfl⟩ : syracuseStep 864523 = 1296785) B1296785
theorem B4370705 : Blo 806344 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B5189933 : Blo 806344 5189933 := bstep (se 3 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 5189933 = 1946225) B1946225
theorem B1814849 : Blo 806344 1814849 := bstep (se 2 (by rfl) ⟨680568, by rfl⟩ : syracuseStep 1814849 = 1361137) B1361137
theorem B59683189 : Blo 806344 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B1815065 : Blo 806344 1815065 := bstep (se 2 (by rfl) ⟨680649, by rfl⟩ : syracuseStep 1815065 = 1361299) B1361299
theorem B1094233 : Blo 806344 1094233 := bstep (se 2 (by rfl) ⟨410337, by rfl⟩ : syracuseStep 1094233 = 820675) B820675
theorem B1815155 : Blo 806344 1815155 := bstep (se 1 (by rfl) ⟨1361366, by rfl⟩ : syracuseStep 1815155 = 2722733) B2722733
theorem B1815191 : Blo 806344 1815191 := bstep (se 1 (by rfl) ⟨1361393, by rfl⟩ : syracuseStep 1815191 = 2722787) B2722787
theorem B2732723 : Blo 806344 2732723 := bstep (se 1 (by rfl) ⟨2049542, by rfl⟩ : syracuseStep 2732723 = 4099085) B4099085
theorem B2044723 : Blo 806344 2044723 := bstep (se 1 (by rfl) ⟨1533542, by rfl⟩ : syracuseStep 2044723 = 3067085) B3067085
theorem B1815371 : Blo 806344 1815371 := bstep (se 1 (by rfl) ⟨1361528, by rfl⟩ : syracuseStep 1815371 = 2723057) B2723057
theorem B1815425 : Blo 806344 1815425 := bstep (se 2 (by rfl) ⟨680784, by rfl⟩ : syracuseStep 1815425 = 1361569) B1361569
theorem B3879859 : Blo 806344 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B2044865 : Blo 806344 2044865 := bstep (se 2 (by rfl) ⟨766824, by rfl⟩ : syracuseStep 2044865 = 1533649) B1533649
theorem B2732993 : Blo 806344 2732993 := bstep (se 2 (by rfl) ⟨1024872, by rfl⟩ : syracuseStep 2732993 = 2049745) B2049745
theorem B1815641 : Blo 806344 1815641 := bstep (se 2 (by rfl) ⟨680865, by rfl⟩ : syracuseStep 1815641 = 1361731) B1361731
theorem B1815731 : Blo 806344 1815731 := bstep (se 1 (by rfl) ⟨1361798, by rfl⟩ : syracuseStep 1815731 = 2723597) B2723597
theorem B2307275 : Blo 806344 2307275 := bstep (se 1 (by rfl) ⟨1730456, by rfl⟩ : syracuseStep 2307275 = 3460913) B3460913
theorem B1815767 : Blo 806344 1815767 := bstep (se 1 (by rfl) ⟨1361825, by rfl⟩ : syracuseStep 1815767 = 2723651) B2723651
theorem B1815947 : Blo 806344 1815947 := bstep (se 1 (by rfl) ⟨1361960, by rfl⟩ : syracuseStep 1815947 = 2723921) B2723921
theorem B4208051 : Blo 806344 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B7386547 : Blo 806344 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B1816001 : Blo 806344 1816001 := bstep (se 2 (by rfl) ⟨681000, by rfl⟩ : syracuseStep 1816001 = 1362001) B1362001
theorem B2733533 : Blo 806344 2733533 := bstep (se 3 (by rfl) ⟨512537, by rfl⟩ : syracuseStep 2733533 = 1025075) B1025075
theorem B5813765 : Blo 806344 5813765 := bstep (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) B1090081
theorem B9942659 : Blo 806344 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B1816217 : Blo 806344 1816217 := bstep (se 2 (by rfl) ⟨681081, by rfl⟩ : syracuseStep 1816217 = 1362163) B1362163
theorem B1816307 : Blo 806344 1816307 := bstep (se 1 (by rfl) ⟨1362230, by rfl⟩ : syracuseStep 1816307 = 2724461) B2724461
theorem B1816343 : Blo 806344 1816343 := bstep (se 1 (by rfl) ⟨1362257, by rfl⟩ : syracuseStep 1816343 = 2724515) B2724515
theorem B3454913 : Blo 806344 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B1816523 : Blo 806344 1816523 := bstep (se 1 (by rfl) ⟨1362392, by rfl⟩ : syracuseStep 1816523 = 2724785) B2724785
theorem B1456115 : Blo 806344 1456115 := bstep (se 1 (by rfl) ⟨1092086, by rfl⟩ : syracuseStep 1456115 = 2184173) B2184173
theorem B1816577 : Blo 806344 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B1292377 : Blo 806344 1292377 := bstep (se 2 (by rfl) ⟨484641, by rfl⟩ : syracuseStep 1292377 = 969283) B969283
theorem B2209943 : Blo 806344 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B2046131 : Blo 806344 2046131 := bstep (se 1 (by rfl) ⟨1534598, by rfl⟩ : syracuseStep 2046131 = 3069197) B3069197
theorem B1816793 : Blo 806344 1816793 := bstep (se 2 (by rfl) ⟨681297, by rfl⟩ : syracuseStep 1816793 = 1362595) B1362595
theorem B1816883 : Blo 806344 1816883 := bstep (se 1 (by rfl) ⟨1362662, by rfl⟩ : syracuseStep 1816883 = 2725325) B2725325
theorem B1816919 : Blo 806344 1816919 := bstep (se 1 (by rfl) ⟨1362689, by rfl⟩ : syracuseStep 1816919 = 2725379) B2725379
theorem B2767193 : Blo 806344 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B10369457 : Blo 806344 10369457 := bstep (se 2 (by rfl) ⟨3888546, by rfl⟩ : syracuseStep 10369457 = 7777093) B7777093
theorem B3062195 : Blo 806344 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B1817099 : Blo 806344 1817099 := bstep (se 1 (by rfl) ⟨1362824, by rfl⟩ : syracuseStep 1817099 = 2725649) B2725649
theorem B1292825 : Blo 806344 1292825 := bstep (se 2 (by rfl) ⟨484809, by rfl⟩ : syracuseStep 1292825 = 969619) B969619
theorem B1817153 : Blo 806344 1817153 := bstep (se 2 (by rfl) ⟨681432, by rfl⟩ : syracuseStep 1817153 = 1362865) B1362865
theorem B2734667 : Blo 806344 2734667 := bstep (se 1 (by rfl) ⟨2051000, by rfl⟩ : syracuseStep 2734667 = 4102001) B4102001
theorem B3455581 : Blo 806344 3455581 := bstep (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) B1295843
theorem B1456793 : Blo 806344 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B2046667 : Blo 806344 2046667 := bstep (se 1 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 2046667 = 3070001) B3070001
theorem B1817369 : Blo 806344 1817369 := bstep (se 2 (by rfl) ⟨681513, by rfl⟩ : syracuseStep 1817369 = 1363027) B1363027
theorem B2046809 : Blo 806344 2046809 := bstep (se 2 (by rfl) ⟨767553, by rfl⟩ : syracuseStep 2046809 = 1535107) B1535107
theorem B1817459 : Blo 806344 1817459 := bstep (se 1 (by rfl) ⟨1363094, by rfl⟩ : syracuseStep 1817459 = 2726189) B2726189
theorem B1817495 : Blo 806344 1817495 := bstep (se 1 (by rfl) ⟨1363121, by rfl⟩ : syracuseStep 1817495 = 2726243) B2726243
theorem B1817675 : Blo 806344 1817675 := bstep (se 1 (by rfl) ⟨1363256, by rfl⟩ : syracuseStep 1817675 = 2726513) B2726513
theorem B1817729 : Blo 806344 1817729 := bstep (se 2 (by rfl) ⟨681648, by rfl⟩ : syracuseStep 1817729 = 1363297) B1363297
theorem B3456179 : Blo 806344 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B1817945 : Blo 806344 1817945 := bstep (se 2 (by rfl) ⟨681729, by rfl⟩ : syracuseStep 1817945 = 1363459) B1363459
theorem B1818035 : Blo 806344 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B1818071 : Blo 806344 1818071 := bstep (se 1 (by rfl) ⟨1363553, by rfl⟩ : syracuseStep 1818071 = 2727107) B2727107
theorem B1818251 : Blo 806344 1818251 := bstep (se 1 (by rfl) ⟨1363688, by rfl⟩ : syracuseStep 1818251 = 2727377) B2727377
theorem B2047639 : Blo 806344 2047639 := bstep (se 1 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 2047639 = 3071459) B3071459
theorem B1818305 : Blo 806344 1818305 := bstep (se 2 (by rfl) ⟨681864, by rfl⟩ : syracuseStep 1818305 = 1363729) B1363729
theorem B1752961 : Blo 806344 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B3063683 : Blo 806344 3063683 := bstep (se 1 (by rfl) ⟨2297762, by rfl⟩ : syracuseStep 3063683 = 4595525) B4595525
theorem B1818521 : Blo 806344 1818521 := bstep (se 2 (by rfl) ⟨681945, by rfl⟩ : syracuseStep 1818521 = 1363891) B1363891
theorem B1818611 : Blo 806344 1818611 := bstep (se 1 (by rfl) ⟨1363958, by rfl⟩ : syracuseStep 1818611 = 2727917) B2727917
theorem B1818647 : Blo 806344 1818647 := bstep (se 1 (by rfl) ⟨1363985, by rfl⟩ : syracuseStep 1818647 = 2727971) B2727971
theorem B16597061 : Blo 806344 16597061 := bstep (se 4 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 16597061 = 3111949) B3111949
theorem B2048075 : Blo 806344 2048075 := bstep (se 1 (by rfl) ⟨1536056, by rfl⟩ : syracuseStep 2048075 = 3072113) B3072113
theorem B1818827 : Blo 806344 1818827 := bstep (se 1 (by rfl) ⟨1364120, by rfl⟩ : syracuseStep 1818827 = 2728241) B2728241
theorem B1818881 : Blo 806344 1818881 := bstep (se 2 (by rfl) ⟨682080, by rfl⟩ : syracuseStep 1818881 = 1364161) B1364161
theorem B3064139 : Blo 806344 3064139 := bstep (se 1 (by rfl) ⟨2298104, by rfl⟩ : syracuseStep 3064139 = 4596209) B4596209
theorem B2048449 : Blo 806344 2048449 := bstep (se 2 (by rfl) ⟨768168, by rfl⟩ : syracuseStep 2048449 = 1536337) B1536337
theorem B1819097 : Blo 806344 1819097 := bstep (se 2 (by rfl) ⟨682161, by rfl⟩ : syracuseStep 1819097 = 1364323) B1364323
theorem B3064337 : Blo 806344 3064337 := bstep (se 2 (by rfl) ⟨1149126, by rfl⟩ : syracuseStep 3064337 = 2298253) B2298253
theorem B1819187 : Blo 806344 1819187 := bstep (se 1 (by rfl) ⟨1364390, by rfl⟩ : syracuseStep 1819187 = 2728781) B2728781
theorem B1819223 : Blo 806344 1819223 := bstep (se 1 (by rfl) ⟨1364417, by rfl⟩ : syracuseStep 1819223 = 2728835) B2728835
theorem B1819403 : Blo 806344 1819403 := bstep (se 1 (by rfl) ⟨1364552, by rfl⟩ : syracuseStep 1819403 = 2729105) B2729105
theorem B1819457 : Blo 806344 1819457 := bstep (se 2 (by rfl) ⟨682296, by rfl⟩ : syracuseStep 1819457 = 1364593) B1364593
theorem B1360793 : Blo 806344 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B2049047 : Blo 806344 2049047 := bstep (se 1 (by rfl) ⟨1536785, by rfl⟩ : syracuseStep 2049047 = 3073571) B3073571
theorem B1360921 : Blo 806344 1360921 := bstep (se 2 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 1360921 = 1020691) B1020691
theorem B1819673 : Blo 806344 1819673 := bstep (se 2 (by rfl) ⟨682377, by rfl⟩ : syracuseStep 1819673 = 1364755) B1364755
theorem B1229899 : Blo 806344 1229899 := bstep (se 1 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 1229899 = 1844849) B1844849
theorem B1819763 : Blo 806344 1819763 := bstep (se 1 (by rfl) ⟨1364822, by rfl⟩ : syracuseStep 1819763 = 2729645) B2729645
theorem B1819799 : Blo 806344 1819799 := bstep (se 1 (by rfl) ⟨1364849, by rfl⟩ : syracuseStep 1819799 = 2729699) B2729699
theorem B935083 : Blo 806344 935083 := bstep (se 1 (by rfl) ⟨701312, by rfl⟩ : syracuseStep 935083 = 1402625) B1402625
theorem B3065111 : Blo 806344 3065111 := bstep (se 1 (by rfl) ⟨2298833, by rfl⟩ : syracuseStep 3065111 = 4597667) B4597667
theorem B1819979 : Blo 806344 1819979 := bstep (se 1 (by rfl) ⟨1364984, by rfl⟩ : syracuseStep 1819979 = 2729969) B2729969
theorem B1230155 : Blo 806344 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B1230167 : Blo 806344 1230167 := bstep (se 1 (by rfl) ⟨922625, by rfl⟩ : syracuseStep 1230167 = 1845251) B1845251
theorem B13813091 : Blo 806344 13813091 := bstep (se 1 (by rfl) ⟨10359818, by rfl⟩ : syracuseStep 13813091 = 20719637) B20719637
theorem B1820033 : Blo 806344 1820033 := bstep (se 2 (by rfl) ⟨682512, by rfl⟩ : syracuseStep 1820033 = 1365025) B1365025
theorem B9848243 : Blo 806344 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B3065309 : Blo 806344 3065309 := bstep (se 3 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 3065309 = 1149491) B1149491
theorem B4605457 : Blo 806344 4605457 := bstep (se 2 (by rfl) ⟨1727046, by rfl⟩ : syracuseStep 4605457 = 3454093) B3454093
theorem B1361495 : Blo 806344 1361495 := bstep (se 1 (by rfl) ⟨1021121, by rfl⟩ : syracuseStep 1361495 = 2042243) B2042243
theorem B1820249 : Blo 806344 1820249 := bstep (se 2 (by rfl) ⟨682593, by rfl⟩ : syracuseStep 1820249 = 1365187) B1365187
theorem B1820339 : Blo 806344 1820339 := bstep (se 1 (by rfl) ⟨1365254, by rfl⟩ : syracuseStep 1820339 = 2730509) B2730509
theorem B1361623 : Blo 806344 1361623 := bstep (se 1 (by rfl) ⟨1021217, by rfl⟩ : syracuseStep 1361623 = 2042435) B2042435
theorem B1820375 : Blo 806344 1820375 := bstep (se 1 (by rfl) ⟨1365281, by rfl⟩ : syracuseStep 1820375 = 2730563) B2730563
theorem B2049857 : Blo 806344 2049857 := bstep (se 2 (by rfl) ⟨768696, by rfl⟩ : syracuseStep 2049857 = 1537393) B1537393
theorem B1820555 : Blo 806344 1820555 := bstep (se 1 (by rfl) ⟨1365416, by rfl⟩ : syracuseStep 1820555 = 2730833) B2730833
theorem B1820609 : Blo 806344 1820609 := bstep (se 2 (by rfl) ⟨682728, by rfl⟩ : syracuseStep 1820609 = 1365457) B1365457
theorem B8734871 : Blo 806344 8734871 := bstep (se 1 (by rfl) ⟨6551153, by rfl⟩ : syracuseStep 8734871 = 13102307) B13102307
theorem B1820825 : Blo 806344 1820825 := bstep (se 2 (by rfl) ⟨682809, by rfl⟩ : syracuseStep 1820825 = 1365619) B1365619
theorem B1820915 : Blo 806344 1820915 := bstep (se 1 (by rfl) ⟨1365686, by rfl⟩ : syracuseStep 1820915 = 2731373) B2731373
theorem B1820951 : Blo 806344 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B1362251 : Blo 806344 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B2050393 : Blo 806344 2050393 := bstep (se 2 (by rfl) ⟨768897, by rfl⟩ : syracuseStep 2050393 = 1537795) B1537795
theorem B2771351 : Blo 806344 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B1362379 : Blo 806344 1362379 := bstep (se 1 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 1362379 = 2043569) B2043569
theorem B1821131 : Blo 806344 1821131 := bstep (se 1 (by rfl) ⟨1365848, by rfl⟩ : syracuseStep 1821131 = 2731697) B2731697
theorem B7489997 : Blo 806344 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B1821185 : Blo 806344 1821185 := bstep (se 2 (by rfl) ⟨682944, by rfl⟩ : syracuseStep 1821185 = 1365889) B1365889
theorem B14764619 : Blo 806344 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B1362521 : Blo 806344 1362521 := bstep (se 2 (by rfl) ⟨510945, by rfl⟩ : syracuseStep 1362521 = 1021891) B1021891
theorem B1362649 : Blo 806344 1362649 := bstep (se 2 (by rfl) ⟨510993, by rfl⟩ : syracuseStep 1362649 = 1021987) B1021987
theorem B1821401 : Blo 806344 1821401 := bstep (se 2 (by rfl) ⟨683025, by rfl⟩ : syracuseStep 1821401 = 1366051) B1366051
theorem B1821491 : Blo 806344 1821491 := bstep (se 1 (by rfl) ⟨1366118, by rfl⟩ : syracuseStep 1821491 = 2732237) B2732237
theorem B1821527 : Blo 806344 1821527 := bstep (se 1 (by rfl) ⟨1366145, by rfl⟩ : syracuseStep 1821527 = 2732291) B2732291
theorem B9849701 : Blo 806344 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B3459971 : Blo 806344 3459971 := bstep (se 1 (by rfl) ⟨2594978, by rfl⟩ : syracuseStep 3459971 = 5189957) B5189957
theorem B1821707 : Blo 806344 1821707 := bstep (se 1 (by rfl) ⟨1366280, by rfl⟩ : syracuseStep 1821707 = 2732561) B2732561
theorem B1297433 : Blo 806344 1297433 := bstep (se 2 (by rfl) ⟨486537, by rfl⟩ : syracuseStep 1297433 = 973075) B973075
theorem B1821761 : Blo 806344 1821761 := bstep (se 2 (by rfl) ⟨683160, by rfl⟩ : syracuseStep 1821761 = 1366321) B1366321
theorem B3493081 : Blo 806344 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B3460313 : Blo 806344 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B1363223 : Blo 806344 1363223 := bstep (se 1 (by rfl) ⟨1022417, by rfl⟩ : syracuseStep 1363223 = 2044835) B2044835
theorem B1821977 : Blo 806344 1821977 := bstep (se 2 (by rfl) ⟨683241, by rfl⟩ : syracuseStep 1821977 = 1366483) B1366483
theorem B1822067 : Blo 806344 1822067 := bstep (se 1 (by rfl) ⟨1366550, by rfl⟩ : syracuseStep 1822067 = 2733101) B2733101
theorem B3067267 : Blo 806344 3067267 := bstep (se 1 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 3067267 = 4600901) B4600901
theorem B1363351 : Blo 806344 1363351 := bstep (se 1 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 1363351 = 2045027) B2045027
theorem B1822103 : Blo 806344 1822103 := bstep (se 1 (by rfl) ⟨1366577, by rfl⟩ : syracuseStep 1822103 = 2733155) B2733155
theorem B1723801 : Blo 806344 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B806347 : Blo 806344 806347 := bstep (se 1 (by rfl) ⟨604760, by rfl⟩ : syracuseStep 806347 = 1209521) B1209521
theorem B806359 : Blo 806344 806359 := bstep (se 1 (by rfl) ⟨604769, by rfl⟩ : syracuseStep 806359 = 1209539) B1209539
theorem B2248157 : Blo 806344 2248157 := bstep (se 3 (by rfl) ⟨421529, by rfl⟩ : syracuseStep 2248157 = 843059) B843059
theorem B806379 : Blo 806344 806379 := bstep (se 1 (by rfl) ⟨604784, by rfl⟩ : syracuseStep 806379 = 1209569) B1209569
theorem B806391 : Blo 806344 806391 := bstep (se 1 (by rfl) ⟨604793, by rfl⟩ : syracuseStep 806391 = 1209587) B1209587
theorem B806411 : Blo 806344 806411 := bstep (se 1 (by rfl) ⟨604808, by rfl⟩ : syracuseStep 806411 = 1209617) B1209617
theorem B806423 : Blo 806344 806423 := bstep (se 1 (by rfl) ⟨604817, by rfl⟩ : syracuseStep 806423 = 1209635) B1209635
theorem B806443 : Blo 806344 806443 := bstep (se 1 (by rfl) ⟨604832, by rfl⟩ : syracuseStep 806443 = 1209665) B1209665
theorem B806455 : Blo 806344 806455 := bstep (se 1 (by rfl) ⟨604841, by rfl⟩ : syracuseStep 806455 = 1209683) B1209683
theorem B806475 : Blo 806344 806475 := bstep (se 1 (by rfl) ⟨604856, by rfl⟩ : syracuseStep 806475 = 1209713) B1209713
theorem B1822283 : Blo 806344 1822283 := bstep (se 1 (by rfl) ⟨1366712, by rfl⟩ : syracuseStep 1822283 = 2733425) B2733425
theorem B806487 : Blo 806344 806487 := bstep (se 1 (by rfl) ⟨604865, by rfl⟩ : syracuseStep 806487 = 1209731) B1209731
theorem B806507 : Blo 806344 806507 := bstep (se 1 (by rfl) ⟨604880, by rfl⟩ : syracuseStep 806507 = 1209761) B1209761
theorem B806519 : Blo 806344 806519 := bstep (se 1 (by rfl) ⟨604889, by rfl⟩ : syracuseStep 806519 = 1209779) B1209779
theorem B1822337 : Blo 806344 1822337 := bstep (se 2 (by rfl) ⟨683376, by rfl⟩ : syracuseStep 1822337 = 1366753) B1366753
theorem B806539 : Blo 806344 806539 := bstep (se 1 (by rfl) ⟨604904, by rfl⟩ : syracuseStep 806539 = 1209809) B1209809
theorem B806551 : Blo 806344 806551 := bstep (se 1 (by rfl) ⟨604913, by rfl⟩ : syracuseStep 806551 = 1209827) B1209827
theorem B806571 : Blo 806344 806571 := bstep (se 1 (by rfl) ⟨604928, by rfl⟩ : syracuseStep 806571 = 1209857) B1209857
theorem B3067571 : Blo 806344 3067571 := bstep (se 1 (by rfl) ⟨2300678, by rfl⟩ : syracuseStep 3067571 = 4601357) B4601357
theorem B806583 : Blo 806344 806583 := bstep (se 1 (by rfl) ⟨604937, by rfl⟩ : syracuseStep 806583 = 1209875) B1209875
theorem B806603 : Blo 806344 806603 := bstep (se 1 (by rfl) ⟨604952, by rfl⟩ : syracuseStep 806603 = 1209905) B1209905
theorem B806615 : Blo 806344 806615 := bstep (se 1 (by rfl) ⟨604961, by rfl⟩ : syracuseStep 806615 = 1209923) B1209923
theorem B806635 : Blo 806344 806635 := bstep (se 1 (by rfl) ⟨604976, by rfl⟩ : syracuseStep 806635 = 1209953) B1209953
theorem B806647 : Blo 806344 806647 := bstep (se 1 (by rfl) ⟨604985, by rfl⟩ : syracuseStep 806647 = 1209971) B1209971
theorem B806667 : Blo 806344 806667 := bstep (se 1 (by rfl) ⟨605000, by rfl⟩ : syracuseStep 806667 = 1210001) B1210001
theorem B806679 : Blo 806344 806679 := bstep (se 1 (by rfl) ⟨605009, by rfl⟩ : syracuseStep 806679 = 1210019) B1210019
theorem B806699 : Blo 806344 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B2182963 : Blo 806344 2182963 := bstep (se 1 (by rfl) ⟨1637222, by rfl⟩ : syracuseStep 2182963 = 3274445) B3274445
theorem B806711 : Blo 806344 806711 := bstep (se 1 (by rfl) ⟨605033, by rfl⟩ : syracuseStep 806711 = 1210067) B1210067
theorem B806731 : Blo 806344 806731 := bstep (se 1 (by rfl) ⟨605048, by rfl⟩ : syracuseStep 806731 = 1210097) B1210097
theorem B806743 : Blo 806344 806743 := bstep (se 1 (by rfl) ⟨605057, by rfl⟩ : syracuseStep 806743 = 1210115) B1210115
theorem B1822553 : Blo 806344 1822553 := bstep (se 2 (by rfl) ⟨683457, by rfl⟩ : syracuseStep 1822553 = 1366915) B1366915
theorem B16568165 : Blo 806344 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B806763 : Blo 806344 806763 := bstep (se 1 (by rfl) ⟨605072, by rfl⟩ : syracuseStep 806763 = 1210145) B1210145
theorem B806775 : Blo 806344 806775 := bstep (se 1 (by rfl) ⟨605081, by rfl⟩ : syracuseStep 806775 = 1210163) B1210163
theorem B806795 : Blo 806344 806795 := bstep (se 1 (by rfl) ⟨605096, by rfl⟩ : syracuseStep 806795 = 1210193) B1210193
theorem B806807 : Blo 806344 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B806827 : Blo 806344 806827 := bstep (se 1 (by rfl) ⟨605120, by rfl⟩ : syracuseStep 806827 = 1210241) B1210241
theorem B1822643 : Blo 806344 1822643 := bstep (se 1 (by rfl) ⟨1366982, by rfl⟩ : syracuseStep 1822643 = 2733965) B2733965
theorem B806839 : Blo 806344 806839 := bstep (se 1 (by rfl) ⟨605129, by rfl⟩ : syracuseStep 806839 = 1210259) B1210259
theorem B806859 : Blo 806344 806859 := bstep (se 1 (by rfl) ⟨605144, by rfl⟩ : syracuseStep 806859 = 1210289) B1210289
theorem B806871 : Blo 806344 806871 := bstep (se 1 (by rfl) ⟨605153, by rfl⟩ : syracuseStep 806871 = 1210307) B1210307
theorem B1822679 : Blo 806344 1822679 := bstep (se 1 (by rfl) ⟨1367009, by rfl⟩ : syracuseStep 1822679 = 2734019) B2734019
theorem B806891 : Blo 806344 806891 := bstep (se 1 (by rfl) ⟨605168, by rfl⟩ : syracuseStep 806891 = 1210337) B1210337
theorem B806903 : Blo 806344 806903 := bstep (se 1 (by rfl) ⟨605177, by rfl⟩ : syracuseStep 806903 = 1210355) B1210355
theorem B806923 : Blo 806344 806923 := bstep (se 1 (by rfl) ⟨605192, by rfl⟩ : syracuseStep 806923 = 1210385) B1210385
theorem B1363979 : Blo 806344 1363979 := bstep (se 1 (by rfl) ⟨1022984, by rfl⟩ : syracuseStep 1363979 = 2045969) B2045969
theorem B806935 : Blo 806344 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B806955 : Blo 806344 806955 := bstep (se 1 (by rfl) ⟨605216, by rfl⟩ : syracuseStep 806955 = 1210433) B1210433
theorem B806967 : Blo 806344 806967 := bstep (se 1 (by rfl) ⟨605225, by rfl⟩ : syracuseStep 806967 = 1210451) B1210451
theorem B806987 : Blo 806344 806987 := bstep (se 1 (by rfl) ⟨605240, by rfl⟩ : syracuseStep 806987 = 1210481) B1210481
theorem B806999 : Blo 806344 806999 := bstep (se 1 (by rfl) ⟨605249, by rfl⟩ : syracuseStep 806999 = 1210499) B1210499
theorem B807019 : Blo 806344 807019 := bstep (se 1 (by rfl) ⟨605264, by rfl⟩ : syracuseStep 807019 = 1210529) B1210529
theorem B807031 : Blo 806344 807031 := bstep (se 1 (by rfl) ⟨605273, by rfl⟩ : syracuseStep 807031 = 1210547) B1210547
theorem B807051 : Blo 806344 807051 := bstep (se 1 (by rfl) ⟨605288, by rfl⟩ : syracuseStep 807051 = 1210577) B1210577
theorem B1364107 : Blo 806344 1364107 := bstep (se 1 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 1364107 = 2046161) B2046161
theorem B1822859 : Blo 806344 1822859 := bstep (se 1 (by rfl) ⟨1367144, by rfl⟩ : syracuseStep 1822859 = 2734289) B2734289
theorem B807063 : Blo 806344 807063 := bstep (se 1 (by rfl) ⟨605297, by rfl⟩ : syracuseStep 807063 = 1210595) B1210595
theorem B807083 : Blo 806344 807083 := bstep (se 1 (by rfl) ⟨605312, by rfl⟩ : syracuseStep 807083 = 1210625) B1210625
theorem B807095 : Blo 806344 807095 := bstep (se 1 (by rfl) ⟨605321, by rfl⟩ : syracuseStep 807095 = 1210643) B1210643
theorem B1822913 : Blo 806344 1822913 := bstep (se 2 (by rfl) ⟨683592, by rfl⟩ : syracuseStep 1822913 = 1367185) B1367185
theorem B807115 : Blo 806344 807115 := bstep (se 1 (by rfl) ⟨605336, by rfl⟩ : syracuseStep 807115 = 1210673) B1210673
theorem B807127 : Blo 806344 807127 := bstep (se 1 (by rfl) ⟨605345, by rfl⟩ : syracuseStep 807127 = 1210691) B1210691
theorem B807147 : Blo 806344 807147 := bstep (se 1 (by rfl) ⟨605360, by rfl⟩ : syracuseStep 807147 = 1210721) B1210721
theorem B807159 : Blo 806344 807159 := bstep (se 1 (by rfl) ⟨605369, by rfl⟩ : syracuseStep 807159 = 1210739) B1210739
theorem B807179 : Blo 806344 807179 := bstep (se 1 (by rfl) ⟨605384, by rfl⟩ : syracuseStep 807179 = 1210769) B1210769
theorem B807191 : Blo 806344 807191 := bstep (se 1 (by rfl) ⟨605393, by rfl⟩ : syracuseStep 807191 = 1210787) B1210787
theorem B1364249 : Blo 806344 1364249 := bstep (se 2 (by rfl) ⟨511593, by rfl⟩ : syracuseStep 1364249 = 1023187) B1023187
theorem B807211 : Blo 806344 807211 := bstep (se 1 (by rfl) ⟨605408, by rfl⟩ : syracuseStep 807211 = 1210817) B1210817
theorem B15520045 : Blo 806344 15520045 := bstep (se 3 (by rfl) ⟨2910008, by rfl⟩ : syracuseStep 15520045 = 5820017) B5820017
theorem B807223 : Blo 806344 807223 := bstep (se 1 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 807223 = 1210835) B1210835
theorem B8278337 : Blo 806344 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B3068225 : Blo 806344 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B807243 : Blo 806344 807243 := bstep (se 1 (by rfl) ⟨605432, by rfl⟩ : syracuseStep 807243 = 1210865) B1210865
theorem B807255 : Blo 806344 807255 := bstep (se 1 (by rfl) ⟨605441, by rfl⟩ : syracuseStep 807255 = 1210883) B1210883
theorem B807275 : Blo 806344 807275 := bstep (se 1 (by rfl) ⟨605456, by rfl⟩ : syracuseStep 807275 = 1210913) B1210913
theorem B807287 : Blo 806344 807287 := bstep (se 1 (by rfl) ⟨605465, by rfl⟩ : syracuseStep 807287 = 1210931) B1210931
theorem B807307 : Blo 806344 807307 := bstep (se 1 (by rfl) ⟨605480, by rfl⟩ : syracuseStep 807307 = 1210961) B1210961
theorem B807319 : Blo 806344 807319 := bstep (se 1 (by rfl) ⟨605489, by rfl⟩ : syracuseStep 807319 = 1210979) B1210979
theorem B1364377 : Blo 806344 1364377 := bstep (se 2 (by rfl) ⟨511641, by rfl⟩ : syracuseStep 1364377 = 1023283) B1023283
theorem B1823129 : Blo 806344 1823129 := bstep (se 2 (by rfl) ⟨683673, by rfl⟩ : syracuseStep 1823129 = 1367347) B1367347
theorem B807339 : Blo 806344 807339 := bstep (se 1 (by rfl) ⟨605504, by rfl⟩ : syracuseStep 807339 = 1211009) B1211009
theorem B807351 : Blo 806344 807351 := bstep (se 1 (by rfl) ⟨605513, by rfl⟩ : syracuseStep 807351 = 1211027) B1211027
theorem B807371 : Blo 806344 807371 := bstep (se 1 (by rfl) ⟨605528, by rfl⟩ : syracuseStep 807371 = 1211057) B1211057
theorem B807383 : Blo 806344 807383 := bstep (se 1 (by rfl) ⟨605537, by rfl⟩ : syracuseStep 807383 = 1211075) B1211075
theorem B807403 : Blo 806344 807403 := bstep (se 1 (by rfl) ⟨605552, by rfl⟩ : syracuseStep 807403 = 1211105) B1211105
theorem B1823219 : Blo 806344 1823219 := bstep (se 1 (by rfl) ⟨1367414, by rfl⟩ : syracuseStep 1823219 = 2734829) B2734829
theorem B807415 : Blo 806344 807415 := bstep (se 1 (by rfl) ⟨605561, by rfl⟩ : syracuseStep 807415 = 1211123) B1211123
theorem B807435 : Blo 806344 807435 := bstep (se 1 (by rfl) ⟨605576, by rfl⟩ : syracuseStep 807435 = 1211153) B1211153
theorem B807447 : Blo 806344 807447 := bstep (se 1 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 807447 = 1211171) B1211171
theorem B1823255 : Blo 806344 1823255 := bstep (se 1 (by rfl) ⟨1367441, by rfl⟩ : syracuseStep 1823255 = 2734883) B2734883
theorem B807467 : Blo 806344 807467 := bstep (se 1 (by rfl) ⟨605600, by rfl⟩ : syracuseStep 807467 = 1211201) B1211201
theorem B807479 : Blo 806344 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B807499 : Blo 806344 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B807511 : Blo 806344 807511 := bstep (se 1 (by rfl) ⟨605633, by rfl⟩ : syracuseStep 807511 = 1211267) B1211267
theorem B807531 : Blo 806344 807531 := bstep (se 1 (by rfl) ⟨605648, by rfl⟩ : syracuseStep 807531 = 1211297) B1211297
theorem B807543 : Blo 806344 807543 := bstep (se 1 (by rfl) ⟨605657, by rfl⟩ : syracuseStep 807543 = 1211315) B1211315
theorem B807563 : Blo 806344 807563 := bstep (se 1 (by rfl) ⟨605672, by rfl⟩ : syracuseStep 807563 = 1211345) B1211345
theorem B807575 : Blo 806344 807575 := bstep (se 1 (by rfl) ⟨605681, by rfl⟩ : syracuseStep 807575 = 1211363) B1211363
theorem B807595 : Blo 806344 807595 := bstep (se 1 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 807595 = 1211393) B1211393
theorem B807607 : Blo 806344 807607 := bstep (se 1 (by rfl) ⟨605705, by rfl⟩ : syracuseStep 807607 = 1211411) B1211411
theorem B807627 : Blo 806344 807627 := bstep (se 1 (by rfl) ⟨605720, by rfl⟩ : syracuseStep 807627 = 1211441) B1211441
theorem B807639 : Blo 806344 807639 := bstep (se 1 (by rfl) ⟨605729, by rfl⟩ : syracuseStep 807639 = 1211459) B1211459
theorem B807659 : Blo 806344 807659 := bstep (se 1 (by rfl) ⟨605744, by rfl⟩ : syracuseStep 807659 = 1211489) B1211489
theorem B807671 : Blo 806344 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B807691 : Blo 806344 807691 := bstep (se 1 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 807691 = 1211537) B1211537
theorem B807703 : Blo 806344 807703 := bstep (se 1 (by rfl) ⟨605777, by rfl⟩ : syracuseStep 807703 = 1211555) B1211555
theorem B807723 : Blo 806344 807723 := bstep (se 1 (by rfl) ⟨605792, by rfl⟩ : syracuseStep 807723 = 1211585) B1211585
theorem B10343213 : Blo 806344 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B807735 : Blo 806344 807735 := bstep (se 1 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 807735 = 1211603) B1211603
theorem B807755 : Blo 806344 807755 := bstep (se 1 (by rfl) ⟨605816, by rfl⟩ : syracuseStep 807755 = 1211633) B1211633
theorem B807767 : Blo 806344 807767 := bstep (se 1 (by rfl) ⟨605825, by rfl⟩ : syracuseStep 807767 = 1211651) B1211651
theorem B807787 : Blo 806344 807787 := bstep (se 1 (by rfl) ⟨605840, by rfl⟩ : syracuseStep 807787 = 1211681) B1211681
theorem B807799 : Blo 806344 807799 := bstep (se 1 (by rfl) ⟨605849, by rfl⟩ : syracuseStep 807799 = 1211699) B1211699
theorem B4608899 : Blo 806344 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B807819 : Blo 806344 807819 := bstep (se 1 (by rfl) ⟨605864, by rfl⟩ : syracuseStep 807819 = 1211729) B1211729
theorem B807831 : Blo 806344 807831 := bstep (se 1 (by rfl) ⟨605873, by rfl⟩ : syracuseStep 807831 = 1211747) B1211747
theorem B807851 : Blo 806344 807851 := bstep (se 1 (by rfl) ⟨605888, by rfl⟩ : syracuseStep 807851 = 1211777) B1211777
theorem B807863 : Blo 806344 807863 := bstep (se 1 (by rfl) ⟨605897, by rfl⟩ : syracuseStep 807863 = 1211795) B1211795
theorem B807883 : Blo 806344 807883 := bstep (se 1 (by rfl) ⟨605912, by rfl⟩ : syracuseStep 807883 = 1211825) B1211825
theorem B807895 : Blo 806344 807895 := bstep (se 1 (by rfl) ⟨605921, by rfl⟩ : syracuseStep 807895 = 1211843) B1211843
theorem B1364951 : Blo 806344 1364951 := bstep (se 1 (by rfl) ⟨1023713, by rfl⟩ : syracuseStep 1364951 = 2047427) B2047427
theorem B807915 : Blo 806344 807915 := bstep (se 1 (by rfl) ⟨605936, by rfl⟩ : syracuseStep 807915 = 1211873) B1211873
theorem B807927 : Blo 806344 807927 := bstep (se 1 (by rfl) ⟨605945, by rfl⟩ : syracuseStep 807927 = 1211891) B1211891
theorem B807947 : Blo 806344 807947 := bstep (se 1 (by rfl) ⟨605960, by rfl⟩ : syracuseStep 807947 = 1211921) B1211921
theorem B807959 : Blo 806344 807959 := bstep (se 1 (by rfl) ⟨605969, by rfl⟩ : syracuseStep 807959 = 1211939) B1211939
theorem B807979 : Blo 806344 807979 := bstep (se 1 (by rfl) ⟨605984, by rfl⟩ : syracuseStep 807979 = 1211969) B1211969
theorem B807991 : Blo 806344 807991 := bstep (se 1 (by rfl) ⟨605993, by rfl⟩ : syracuseStep 807991 = 1211987) B1211987
theorem B808011 : Blo 806344 808011 := bstep (se 1 (by rfl) ⟨606008, by rfl⟩ : syracuseStep 808011 = 1212017) B1212017
theorem B808023 : Blo 806344 808023 := bstep (se 1 (by rfl) ⟨606017, by rfl⟩ : syracuseStep 808023 = 1212035) B1212035
theorem B1365079 : Blo 806344 1365079 := bstep (se 1 (by rfl) ⟨1023809, by rfl⟩ : syracuseStep 1365079 = 2047619) B2047619
theorem B4084829 : Blo 806344 4084829 := bstep (se 3 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 4084829 = 1531811) B1531811
theorem B808043 : Blo 806344 808043 := bstep (se 1 (by rfl) ⟨606032, by rfl⟩ : syracuseStep 808043 = 1212065) B1212065
theorem B808055 : Blo 806344 808055 := bstep (se 1 (by rfl) ⟨606041, by rfl⟩ : syracuseStep 808055 = 1212083) B1212083
theorem B808075 : Blo 806344 808075 := bstep (se 1 (by rfl) ⟨606056, by rfl⟩ : syracuseStep 808075 = 1212113) B1212113
theorem B808087 : Blo 806344 808087 := bstep (se 1 (by rfl) ⟨606065, by rfl⟩ : syracuseStep 808087 = 1212131) B1212131
theorem B808107 : Blo 806344 808107 := bstep (se 1 (by rfl) ⟨606080, by rfl⟩ : syracuseStep 808107 = 1212161) B1212161
theorem B808119 : Blo 806344 808119 := bstep (se 1 (by rfl) ⟨606089, by rfl⟩ : syracuseStep 808119 = 1212179) B1212179
theorem B808139 : Blo 806344 808139 := bstep (se 1 (by rfl) ⟨606104, by rfl⟩ : syracuseStep 808139 = 1212209) B1212209
theorem B808151 : Blo 806344 808151 := bstep (se 1 (by rfl) ⟨606113, by rfl⟩ : syracuseStep 808151 = 1212227) B1212227
theorem B808171 : Blo 806344 808171 := bstep (se 1 (by rfl) ⟨606128, by rfl⟩ : syracuseStep 808171 = 1212257) B1212257
theorem B808183 : Blo 806344 808183 := bstep (se 1 (by rfl) ⟨606137, by rfl⟩ : syracuseStep 808183 = 1212275) B1212275
theorem B808203 : Blo 806344 808203 := bstep (se 1 (by rfl) ⟨606152, by rfl⟩ : syracuseStep 808203 = 1212305) B1212305
theorem B808215 : Blo 806344 808215 := bstep (se 1 (by rfl) ⟨606161, by rfl⟩ : syracuseStep 808215 = 1212323) B1212323
theorem B808235 : Blo 806344 808235 := bstep (se 1 (by rfl) ⟨606176, by rfl⟩ : syracuseStep 808235 = 1212353) B1212353
theorem B808247 : Blo 806344 808247 := bstep (se 1 (by rfl) ⟨606185, by rfl⟩ : syracuseStep 808247 = 1212371) B1212371
theorem B808267 : Blo 806344 808267 := bstep (se 1 (by rfl) ⟨606200, by rfl⟩ : syracuseStep 808267 = 1212401) B1212401
theorem B808279 : Blo 806344 808279 := bstep (se 1 (by rfl) ⟨606209, by rfl⟩ : syracuseStep 808279 = 1212419) B1212419
theorem B808299 : Blo 806344 808299 := bstep (se 1 (by rfl) ⟨606224, by rfl⟩ : syracuseStep 808299 = 1212449) B1212449
theorem B808311 : Blo 806344 808311 := bstep (se 1 (by rfl) ⟨606233, by rfl⟩ : syracuseStep 808311 = 1212467) B1212467
theorem B808331 : Blo 806344 808331 := bstep (se 1 (by rfl) ⟨606248, by rfl⟩ : syracuseStep 808331 = 1212497) B1212497
theorem B808343 : Blo 806344 808343 := bstep (se 1 (by rfl) ⟨606257, by rfl⟩ : syracuseStep 808343 = 1212515) B1212515
theorem B808363 : Blo 806344 808363 := bstep (se 1 (by rfl) ⟨606272, by rfl⟩ : syracuseStep 808363 = 1212545) B1212545
theorem B808375 : Blo 806344 808375 := bstep (se 1 (by rfl) ⟨606281, by rfl⟩ : syracuseStep 808375 = 1212563) B1212563
theorem B808395 : Blo 806344 808395 := bstep (se 1 (by rfl) ⟨606296, by rfl⟩ : syracuseStep 808395 = 1212593) B1212593
theorem B808407 : Blo 806344 808407 := bstep (se 1 (by rfl) ⟨606305, by rfl⟩ : syracuseStep 808407 = 1212611) B1212611
theorem B808427 : Blo 806344 808427 := bstep (se 1 (by rfl) ⟨606320, by rfl⟩ : syracuseStep 808427 = 1212641) B1212641
theorem B808439 : Blo 806344 808439 := bstep (se 1 (by rfl) ⟨606329, by rfl⟩ : syracuseStep 808439 = 1212659) B1212659
theorem B1725953 : Blo 806344 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B808459 : Blo 806344 808459 := bstep (se 1 (by rfl) ⟨606344, by rfl⟩ : syracuseStep 808459 = 1212689) B1212689
theorem B808471 : Blo 806344 808471 := bstep (se 1 (by rfl) ⟨606353, by rfl⟩ : syracuseStep 808471 = 1212707) B1212707
theorem B808491 : Blo 806344 808491 := bstep (se 1 (by rfl) ⟨606368, by rfl⟩ : syracuseStep 808491 = 1212737) B1212737
theorem B3069485 : Blo 806344 3069485 := bstep (se 3 (by rfl) ⟨575528, by rfl⟩ : syracuseStep 3069485 = 1151057) B1151057
theorem B808503 : Blo 806344 808503 := bstep (se 1 (by rfl) ⟨606377, by rfl⟩ : syracuseStep 808503 = 1212755) B1212755
theorem B2184779 : Blo 806344 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B3069515 : Blo 806344 3069515 := bstep (se 1 (by rfl) ⟨2302136, by rfl⟩ : syracuseStep 3069515 = 4604273) B4604273
theorem B808523 : Blo 806344 808523 := bstep (se 1 (by rfl) ⟨606392, by rfl⟩ : syracuseStep 808523 = 1212785) B1212785
theorem B1726039 : Blo 806344 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B808535 : Blo 806344 808535 := bstep (se 1 (by rfl) ⟨606401, by rfl⟩ : syracuseStep 808535 = 1212803) B1212803
theorem B808555 : Blo 806344 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B808567 : Blo 806344 808567 := bstep (se 1 (by rfl) ⟨606425, by rfl⟩ : syracuseStep 808567 = 1212851) B1212851
theorem B808587 : Blo 806344 808587 := bstep (se 1 (by rfl) ⟨606440, by rfl⟩ : syracuseStep 808587 = 1212881) B1212881
theorem B808599 : Blo 806344 808599 := bstep (se 1 (by rfl) ⟨606449, by rfl⟩ : syracuseStep 808599 = 1212899) B1212899
theorem B808619 : Blo 806344 808619 := bstep (se 1 (by rfl) ⟨606464, by rfl⟩ : syracuseStep 808619 = 1212929) B1212929
theorem B808631 : Blo 806344 808631 := bstep (se 1 (by rfl) ⟨606473, by rfl⟩ : syracuseStep 808631 = 1212947) B1212947
theorem B808651 : Blo 806344 808651 := bstep (se 1 (by rfl) ⟨606488, by rfl⟩ : syracuseStep 808651 = 1212977) B1212977
theorem B1365707 : Blo 806344 1365707 := bstep (se 1 (by rfl) ⟨1024280, by rfl⟩ : syracuseStep 1365707 = 2048561) B2048561
theorem B808663 : Blo 806344 808663 := bstep (se 1 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 808663 = 1212995) B1212995
theorem B808683 : Blo 806344 808683 := bstep (se 1 (by rfl) ⟨606512, by rfl⟩ : syracuseStep 808683 = 1213025) B1213025
theorem B808695 : Blo 806344 808695 := bstep (se 1 (by rfl) ⟨606521, by rfl⟩ : syracuseStep 808695 = 1213043) B1213043
theorem B808715 : Blo 806344 808715 := bstep (se 1 (by rfl) ⟨606536, by rfl⟩ : syracuseStep 808715 = 1213073) B1213073
theorem B808727 : Blo 806344 808727 := bstep (se 1 (by rfl) ⟨606545, by rfl⟩ : syracuseStep 808727 = 1213091) B1213091
theorem B808747 : Blo 806344 808747 := bstep (se 1 (by rfl) ⟨606560, by rfl⟩ : syracuseStep 808747 = 1213121) B1213121
theorem B808759 : Blo 806344 808759 := bstep (se 1 (by rfl) ⟨606569, by rfl⟩ : syracuseStep 808759 = 1213139) B1213139
theorem B808779 : Blo 806344 808779 := bstep (se 1 (by rfl) ⟨606584, by rfl⟩ : syracuseStep 808779 = 1213169) B1213169
theorem B1365835 : Blo 806344 1365835 := bstep (se 1 (by rfl) ⟨1024376, by rfl⟩ : syracuseStep 1365835 = 2048753) B2048753
theorem B808791 : Blo 806344 808791 := bstep (se 1 (by rfl) ⟨606593, by rfl⟩ : syracuseStep 808791 = 1213187) B1213187
theorem B808811 : Blo 806344 808811 := bstep (se 1 (by rfl) ⟨606608, by rfl⟩ : syracuseStep 808811 = 1213217) B1213217
theorem B808823 : Blo 806344 808823 := bstep (se 1 (by rfl) ⟨606617, by rfl⟩ : syracuseStep 808823 = 1213235) B1213235
theorem B808843 : Blo 806344 808843 := bstep (se 1 (by rfl) ⟨606632, by rfl⟩ : syracuseStep 808843 = 1213265) B1213265
theorem B907159 : Blo 806344 907159 := bstep (se 1 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 907159 = 1360739) B1360739
theorem B808855 : Blo 806344 808855 := bstep (se 1 (by rfl) ⟨606641, by rfl⟩ : syracuseStep 808855 = 1213283) B1213283
theorem B808875 : Blo 806344 808875 := bstep (se 1 (by rfl) ⟨606656, by rfl⟩ : syracuseStep 808875 = 1213313) B1213313
theorem B5822387 : Blo 806344 5822387 := bstep (se 1 (by rfl) ⟨4366790, by rfl⟩ : syracuseStep 5822387 = 8733581) B8733581
theorem B808887 : Blo 806344 808887 := bstep (se 1 (by rfl) ⟨606665, by rfl⟩ : syracuseStep 808887 = 1213331) B1213331
theorem B808907 : Blo 806344 808907 := bstep (se 1 (by rfl) ⟨606680, by rfl⟩ : syracuseStep 808907 = 1213361) B1213361
theorem B808919 : Blo 806344 808919 := bstep (se 1 (by rfl) ⟨606689, by rfl⟩ : syracuseStep 808919 = 1213379) B1213379
theorem B1365977 : Blo 806344 1365977 := bstep (se 2 (by rfl) ⟨512241, by rfl⟩ : syracuseStep 1365977 = 1024483) B1024483
theorem B808939 : Blo 806344 808939 := bstep (se 1 (by rfl) ⟨606704, by rfl⟩ : syracuseStep 808939 = 1213409) B1213409
theorem B808951 : Blo 806344 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B808971 : Blo 806344 808971 := bstep (se 1 (by rfl) ⟨606728, by rfl⟩ : syracuseStep 808971 = 1213457) B1213457
theorem B808983 : Blo 806344 808983 := bstep (se 1 (by rfl) ⟨606737, by rfl⟩ : syracuseStep 808983 = 1213475) B1213475
theorem B809003 : Blo 806344 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B809015 : Blo 806344 809015 := bstep (se 1 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 809015 = 1213523) B1213523
theorem B907339 : Blo 806344 907339 := bstep (se 1 (by rfl) ⟨680504, by rfl⟩ : syracuseStep 907339 = 1361009) B1361009
theorem B809035 : Blo 806344 809035 := bstep (se 1 (by rfl) ⟨606776, by rfl⟩ : syracuseStep 809035 = 1213553) B1213553
theorem B809047 : Blo 806344 809047 := bstep (se 1 (by rfl) ⟨606785, by rfl⟩ : syracuseStep 809047 = 1213571) B1213571
theorem B1366105 : Blo 806344 1366105 := bstep (se 2 (by rfl) ⟨512289, by rfl⟩ : syracuseStep 1366105 = 1024579) B1024579
theorem B2021465 : Blo 806344 2021465 := bstep (se 2 (by rfl) ⟨758049, by rfl⟩ : syracuseStep 2021465 = 1516099) B1516099
theorem B809067 : Blo 806344 809067 := bstep (se 1 (by rfl) ⟨606800, by rfl⟩ : syracuseStep 809067 = 1213601) B1213601
theorem B809079 : Blo 806344 809079 := bstep (se 1 (by rfl) ⟨606809, by rfl⟩ : syracuseStep 809079 = 1213619) B1213619
theorem B809099 : Blo 806344 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B809111 : Blo 806344 809111 := bstep (se 1 (by rfl) ⟨606833, by rfl⟩ : syracuseStep 809111 = 1213667) B1213667
theorem B809131 : Blo 806344 809131 := bstep (se 1 (by rfl) ⟨606848, by rfl⟩ : syracuseStep 809131 = 1213697) B1213697
theorem B907447 : Blo 806344 907447 := bstep (se 1 (by rfl) ⟨680585, by rfl⟩ : syracuseStep 907447 = 1361171) B1361171
theorem B809143 : Blo 806344 809143 := bstep (se 1 (by rfl) ⟨606857, by rfl⟩ : syracuseStep 809143 = 1213715) B1213715
theorem B809163 : Blo 806344 809163 := bstep (se 1 (by rfl) ⟨606872, by rfl⟩ : syracuseStep 809163 = 1213745) B1213745
theorem B809175 : Blo 806344 809175 := bstep (se 1 (by rfl) ⟨606881, by rfl⟩ : syracuseStep 809175 = 1213763) B1213763
theorem B3070169 : Blo 806344 3070169 := bstep (se 2 (by rfl) ⟨1151313, by rfl⟩ : syracuseStep 3070169 = 2302627) B2302627
theorem B809195 : Blo 806344 809195 := bstep (se 1 (by rfl) ⟨606896, by rfl⟩ : syracuseStep 809195 = 1213793) B1213793
theorem B809207 : Blo 806344 809207 := bstep (se 1 (by rfl) ⟨606905, by rfl⟩ : syracuseStep 809207 = 1213811) B1213811
theorem B809227 : Blo 806344 809227 := bstep (se 1 (by rfl) ⟨606920, by rfl⟩ : syracuseStep 809227 = 1213841) B1213841
theorem B809239 : Blo 806344 809239 := bstep (se 1 (by rfl) ⟨606929, by rfl⟩ : syracuseStep 809239 = 1213859) B1213859
theorem B809259 : Blo 806344 809259 := bstep (se 1 (by rfl) ⟨606944, by rfl⟩ : syracuseStep 809259 = 1213889) B1213889
theorem B809271 : Blo 806344 809271 := bstep (se 1 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 809271 = 1213907) B1213907
theorem B809291 : Blo 806344 809291 := bstep (se 1 (by rfl) ⟨606968, by rfl⟩ : syracuseStep 809291 = 1213937) B1213937
theorem B809303 : Blo 806344 809303 := bstep (se 1 (by rfl) ⟨606977, by rfl⟩ : syracuseStep 809303 = 1213955) B1213955
theorem B907627 : Blo 806344 907627 := bstep (se 1 (by rfl) ⟨680720, by rfl⟩ : syracuseStep 907627 = 1361441) B1361441
theorem B809323 : Blo 806344 809323 := bstep (se 1 (by rfl) ⟨606992, by rfl⟩ : syracuseStep 809323 = 1213985) B1213985
theorem B809335 : Blo 806344 809335 := bstep (se 1 (by rfl) ⟨607001, by rfl⟩ : syracuseStep 809335 = 1214003) B1214003
theorem B1726859 : Blo 806344 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B809355 : Blo 806344 809355 := bstep (se 1 (by rfl) ⟨607016, by rfl⟩ : syracuseStep 809355 = 1214033) B1214033
theorem B809367 : Blo 806344 809367 := bstep (se 1 (by rfl) ⟨607025, by rfl⟩ : syracuseStep 809367 = 1214051) B1214051
theorem B809387 : Blo 806344 809387 := bstep (se 1 (by rfl) ⟨607040, by rfl⟩ : syracuseStep 809387 = 1214081) B1214081
theorem B809399 : Blo 806344 809399 := bstep (se 1 (by rfl) ⟨607049, by rfl⟩ : syracuseStep 809399 = 1214099) B1214099
theorem B809419 : Blo 806344 809419 := bstep (se 1 (by rfl) ⟨607064, by rfl⟩ : syracuseStep 809419 = 1214129) B1214129
theorem B907735 : Blo 806344 907735 := bstep (se 1 (by rfl) ⟨680801, by rfl⟩ : syracuseStep 907735 = 1361603) B1361603
theorem B809431 : Blo 806344 809431 := bstep (se 1 (by rfl) ⟨607073, by rfl⟩ : syracuseStep 809431 = 1214147) B1214147
theorem B809451 : Blo 806344 809451 := bstep (se 1 (by rfl) ⟨607088, by rfl⟩ : syracuseStep 809451 = 1214177) B1214177
theorem B809463 : Blo 806344 809463 := bstep (se 1 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 809463 = 1214195) B1214195
theorem B809483 : Blo 806344 809483 := bstep (se 1 (by rfl) ⟨607112, by rfl⟩ : syracuseStep 809483 = 1214225) B1214225
theorem B3070487 : Blo 806344 3070487 := bstep (se 1 (by rfl) ⟨2302865, by rfl⟩ : syracuseStep 3070487 = 4605731) B4605731
theorem B809495 : Blo 806344 809495 := bstep (se 1 (by rfl) ⟨607121, by rfl⟩ : syracuseStep 809495 = 1214243) B1214243
theorem B809515 : Blo 806344 809515 := bstep (se 1 (by rfl) ⟨607136, by rfl⟩ : syracuseStep 809515 = 1214273) B1214273
theorem B809527 : Blo 806344 809527 := bstep (se 1 (by rfl) ⟨607145, by rfl⟩ : syracuseStep 809527 = 1214291) B1214291
theorem B809547 : Blo 806344 809547 := bstep (se 1 (by rfl) ⟨607160, by rfl⟩ : syracuseStep 809547 = 1214321) B1214321
theorem B809559 : Blo 806344 809559 := bstep (se 1 (by rfl) ⟨607169, by rfl⟩ : syracuseStep 809559 = 1214339) B1214339
theorem B809579 : Blo 806344 809579 := bstep (se 1 (by rfl) ⟨607184, by rfl⟩ : syracuseStep 809579 = 1214369) B1214369
theorem B809591 : Blo 806344 809591 := bstep (se 1 (by rfl) ⟨607193, by rfl⟩ : syracuseStep 809591 = 1214387) B1214387
theorem B907915 : Blo 806344 907915 := bstep (se 1 (by rfl) ⟨680936, by rfl⟩ : syracuseStep 907915 = 1361873) B1361873
theorem B809611 : Blo 806344 809611 := bstep (se 1 (by rfl) ⟨607208, by rfl⟩ : syracuseStep 809611 = 1214417) B1214417
theorem B809623 : Blo 806344 809623 := bstep (se 1 (by rfl) ⟨607217, by rfl⟩ : syracuseStep 809623 = 1214435) B1214435
theorem B1366679 : Blo 806344 1366679 := bstep (se 1 (by rfl) ⟨1025009, by rfl⟩ : syracuseStep 1366679 = 2050019) B2050019
theorem B973463 : Blo 806344 973463 := bstep (se 1 (by rfl) ⟨730097, by rfl⟩ : syracuseStep 973463 = 1460195) B1460195
theorem B809643 : Blo 806344 809643 := bstep (se 1 (by rfl) ⟨607232, by rfl⟩ : syracuseStep 809643 = 1214465) B1214465
theorem B809655 : Blo 806344 809655 := bstep (se 1 (by rfl) ⟨607241, by rfl⟩ : syracuseStep 809655 = 1214483) B1214483
theorem B809675 : Blo 806344 809675 := bstep (se 1 (by rfl) ⟨607256, by rfl⟩ : syracuseStep 809675 = 1214513) B1214513
theorem B809687 : Blo 806344 809687 := bstep (se 1 (by rfl) ⟨607265, by rfl⟩ : syracuseStep 809687 = 1214531) B1214531
theorem B809707 : Blo 806344 809707 := bstep (se 1 (by rfl) ⟨607280, by rfl⟩ : syracuseStep 809707 = 1214561) B1214561
theorem B908023 : Blo 806344 908023 := bstep (se 1 (by rfl) ⟨681017, by rfl⟩ : syracuseStep 908023 = 1362035) B1362035
theorem B809719 : Blo 806344 809719 := bstep (se 1 (by rfl) ⟨607289, by rfl⟩ : syracuseStep 809719 = 1214579) B1214579
theorem B809739 : Blo 806344 809739 := bstep (se 1 (by rfl) ⟨607304, by rfl⟩ : syracuseStep 809739 = 1214609) B1214609
theorem B809751 : Blo 806344 809751 := bstep (se 1 (by rfl) ⟨607313, by rfl⟩ : syracuseStep 809751 = 1214627) B1214627
theorem B1366807 : Blo 806344 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B809771 : Blo 806344 809771 := bstep (se 1 (by rfl) ⟨607328, by rfl⟩ : syracuseStep 809771 = 1214657) B1214657
theorem B809783 : Blo 806344 809783 := bstep (se 1 (by rfl) ⟨607337, by rfl⟩ : syracuseStep 809783 = 1214675) B1214675
theorem B809803 : Blo 806344 809803 := bstep (se 1 (by rfl) ⟨607352, by rfl⟩ : syracuseStep 809803 = 1214705) B1214705
theorem B809815 : Blo 806344 809815 := bstep (se 1 (by rfl) ⟨607361, by rfl⟩ : syracuseStep 809815 = 1214723) B1214723
theorem B809835 : Blo 806344 809835 := bstep (se 1 (by rfl) ⟨607376, by rfl⟩ : syracuseStep 809835 = 1214753) B1214753
theorem B809847 : Blo 806344 809847 := bstep (se 1 (by rfl) ⟨607385, by rfl⟩ : syracuseStep 809847 = 1214771) B1214771
theorem B2907011 : Blo 806344 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B809867 : Blo 806344 809867 := bstep (se 1 (by rfl) ⟨607400, by rfl⟩ : syracuseStep 809867 = 1214801) B1214801
theorem B809879 : Blo 806344 809879 := bstep (se 1 (by rfl) ⟨607409, by rfl⟩ : syracuseStep 809879 = 1214819) B1214819
theorem B908203 : Blo 806344 908203 := bstep (se 1 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 908203 = 1362305) B1362305
theorem B809899 : Blo 806344 809899 := bstep (se 1 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 809899 = 1214849) B1214849
theorem B7756721 : Blo 806344 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B3693491 : Blo 806344 3693491 := bstep (se 1 (by rfl) ⟨2770118, by rfl⟩ : syracuseStep 3693491 = 5540237) B5540237
theorem B809911 : Blo 806344 809911 := bstep (se 1 (by rfl) ⟨607433, by rfl⟩ : syracuseStep 809911 = 1214867) B1214867
theorem B809931 : Blo 806344 809931 := bstep (se 1 (by rfl) ⟨607448, by rfl⟩ : syracuseStep 809931 = 1214897) B1214897
theorem B1530839 : Blo 806344 1530839 := bstep (se 1 (by rfl) ⟨1148129, by rfl⟩ : syracuseStep 1530839 = 2296259) B2296259
theorem B809943 : Blo 806344 809943 := bstep (se 1 (by rfl) ⟨607457, by rfl⟩ : syracuseStep 809943 = 1214915) B1214915
theorem B809963 : Blo 806344 809963 := bstep (se 1 (by rfl) ⟨607472, by rfl⟩ : syracuseStep 809963 = 1214945) B1214945
theorem B809975 : Blo 806344 809975 := bstep (se 1 (by rfl) ⟨607481, by rfl⟩ : syracuseStep 809975 = 1214963) B1214963
theorem B809995 : Blo 806344 809995 := bstep (se 1 (by rfl) ⟨607496, by rfl⟩ : syracuseStep 809995 = 1214993) B1214993
theorem B908311 : Blo 806344 908311 := bstep (se 1 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 908311 = 1362467) B1362467
theorem B810007 : Blo 806344 810007 := bstep (se 1 (by rfl) ⟨607505, by rfl⟩ : syracuseStep 810007 = 1215011) B1215011
theorem B810027 : Blo 806344 810027 := bstep (se 1 (by rfl) ⟨607520, by rfl⟩ : syracuseStep 810027 = 1215041) B1215041
theorem B3693619 : Blo 806344 3693619 := bstep (se 1 (by rfl) ⟨2770214, by rfl⟩ : syracuseStep 3693619 = 5540429) B5540429
theorem B810039 : Blo 806344 810039 := bstep (se 1 (by rfl) ⟨607529, by rfl⟩ : syracuseStep 810039 = 1215059) B1215059
theorem B810059 : Blo 806344 810059 := bstep (se 1 (by rfl) ⟨607544, by rfl⟩ : syracuseStep 810059 = 1215089) B1215089
theorem B810071 : Blo 806344 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B810091 : Blo 806344 810091 := bstep (se 1 (by rfl) ⟨607568, by rfl⟩ : syracuseStep 810091 = 1215137) B1215137
theorem B810103 : Blo 806344 810103 := bstep (se 1 (by rfl) ⟨607577, by rfl⟩ : syracuseStep 810103 = 1215155) B1215155
theorem B810123 : Blo 806344 810123 := bstep (se 1 (by rfl) ⟨607592, by rfl⟩ : syracuseStep 810123 = 1215185) B1215185
theorem B4086935 : Blo 806344 4086935 := bstep (se 1 (by rfl) ⟨3065201, by rfl⟩ : syracuseStep 4086935 = 6130403) B6130403
theorem B810135 : Blo 806344 810135 := bstep (se 1 (by rfl) ⟨607601, by rfl⟩ : syracuseStep 810135 = 1215203) B1215203
theorem B810155 : Blo 806344 810155 := bstep (se 1 (by rfl) ⟨607616, by rfl⟩ : syracuseStep 810155 = 1215233) B1215233
theorem B3071155 : Blo 806344 3071155 := bstep (se 1 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 3071155 = 4606733) B4606733
theorem B810167 : Blo 806344 810167 := bstep (se 1 (by rfl) ⟨607625, by rfl⟩ : syracuseStep 810167 = 1215251) B1215251
theorem B908491 : Blo 806344 908491 := bstep (se 1 (by rfl) ⟨681368, by rfl⟩ : syracuseStep 908491 = 1362737) B1362737
theorem B810187 : Blo 806344 810187 := bstep (se 1 (by rfl) ⟨607640, by rfl⟩ : syracuseStep 810187 = 1215281) B1215281
theorem B810199 : Blo 806344 810199 := bstep (se 1 (by rfl) ⟨607649, by rfl⟩ : syracuseStep 810199 = 1215299) B1215299
theorem B3890393 : Blo 806344 3890393 := bstep (se 2 (by rfl) ⟨1458897, by rfl⟩ : syracuseStep 3890393 = 2917795) B2917795
theorem B4611289 : Blo 806344 4611289 := bstep (se 2 (by rfl) ⟨1729233, by rfl⟩ : syracuseStep 4611289 = 3458467) B3458467
theorem B810219 : Blo 806344 810219 := bstep (se 1 (by rfl) ⟨607664, by rfl⟩ : syracuseStep 810219 = 1215329) B1215329
theorem B810231 : Blo 806344 810231 := bstep (se 1 (by rfl) ⟨607673, by rfl⟩ : syracuseStep 810231 = 1215347) B1215347
theorem B810251 : Blo 806344 810251 := bstep (se 1 (by rfl) ⟨607688, by rfl⟩ : syracuseStep 810251 = 1215377) B1215377
theorem B810263 : Blo 806344 810263 := bstep (se 1 (by rfl) ⟨607697, by rfl⟩ : syracuseStep 810263 = 1215395) B1215395
theorem B810283 : Blo 806344 810283 := bstep (se 1 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 810283 = 1215425) B1215425
theorem B908599 : Blo 806344 908599 := bstep (se 1 (by rfl) ⟨681449, by rfl⟩ : syracuseStep 908599 = 1362899) B1362899
theorem B810295 : Blo 806344 810295 := bstep (se 1 (by rfl) ⟨607721, by rfl⟩ : syracuseStep 810295 = 1215443) B1215443
theorem B810315 : Blo 806344 810315 := bstep (se 1 (by rfl) ⟨607736, by rfl⟩ : syracuseStep 810315 = 1215473) B1215473
theorem B810327 : Blo 806344 810327 := bstep (se 1 (by rfl) ⟨607745, by rfl⟩ : syracuseStep 810327 = 1215491) B1215491
theorem B1727833 : Blo 806344 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B1367435 : Blo 806344 1367435 := bstep (se 1 (by rfl) ⟨1025576, by rfl⟩ : syracuseStep 1367435 = 2051153) B2051153
theorem B908779 : Blo 806344 908779 := bstep (se 1 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 908779 = 1363169) B1363169
theorem B1531379 : Blo 806344 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B908887 : Blo 806344 908887 := bstep (se 1 (by rfl) ⟨681665, by rfl⟩ : syracuseStep 908887 = 1363331) B1363331
theorem B909067 : Blo 806344 909067 := bstep (se 1 (by rfl) ⟨681800, by rfl⟩ : syracuseStep 909067 = 1363601) B1363601
theorem B909175 : Blo 806344 909175 := bstep (se 1 (by rfl) ⟨681881, by rfl⟩ : syracuseStep 909175 = 1363763) B1363763
theorem B1531865 : Blo 806344 1531865 := bstep (se 2 (by rfl) ⟨574449, by rfl⟩ : syracuseStep 1531865 = 1148899) B1148899
theorem B909355 : Blo 806344 909355 := bstep (se 1 (by rfl) ⟨682016, by rfl⟩ : syracuseStep 909355 = 1364033) B1364033
theorem B3694657 : Blo 806344 3694657 := bstep (se 2 (by rfl) ⟨1385496, by rfl⟩ : syracuseStep 3694657 = 2770993) B2770993
theorem B909463 : Blo 806344 909463 := bstep (se 1 (by rfl) ⟨682097, by rfl⟩ : syracuseStep 909463 = 1364195) B1364195
theorem B4612247 : Blo 806344 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B909643 : Blo 806344 909643 := bstep (se 1 (by rfl) ⟨682232, by rfl⟩ : syracuseStep 909643 = 1364465) B1364465
theorem B3072401 : Blo 806344 3072401 := bstep (se 2 (by rfl) ⟨1152150, by rfl⟩ : syracuseStep 3072401 = 2304301) B2304301
theorem B909751 : Blo 806344 909751 := bstep (se 1 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 909751 = 1364627) B1364627
theorem B11067997 : Blo 806344 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B909931 : Blo 806344 909931 := bstep (se 1 (by rfl) ⟨682448, by rfl⟩ : syracuseStep 909931 = 1364897) B1364897
theorem B910039 : Blo 806344 910039 := bstep (se 1 (by rfl) ⟨682529, by rfl⟩ : syracuseStep 910039 = 1365059) B1365059
theorem B2908973 : Blo 806344 2908973 := bstep (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) B1090865
theorem B910219 : Blo 806344 910219 := bstep (se 1 (by rfl) ⟨682664, by rfl⟩ : syracuseStep 910219 = 1365329) B1365329
theorem B910327 : Blo 806344 910327 := bstep (se 1 (by rfl) ⟨682745, by rfl⟩ : syracuseStep 910327 = 1365491) B1365491
theorem B3073099 : Blo 806344 3073099 := bstep (se 1 (by rfl) ⟨2304824, by rfl⟩ : syracuseStep 3073099 = 4609649) B4609649
theorem B910507 : Blo 806344 910507 := bstep (se 1 (by rfl) ⟨682880, by rfl⟩ : syracuseStep 910507 = 1365761) B1365761
theorem B910615 : Blo 806344 910615 := bstep (se 1 (by rfl) ⟨682961, by rfl⟩ : syracuseStep 910615 = 1365923) B1365923
theorem B3073373 : Blo 806344 3073373 := bstep (se 3 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 3073373 = 1152515) B1152515
theorem B1533323 : Blo 806344 1533323 := bstep (se 1 (by rfl) ⟨1149992, by rfl⟩ : syracuseStep 1533323 = 2299985) B2299985
theorem B910795 : Blo 806344 910795 := bstep (se 1 (by rfl) ⟨683096, by rfl⟩ : syracuseStep 910795 = 1366193) B1366193
theorem B910903 : Blo 806344 910903 := bstep (se 1 (by rfl) ⟨683177, by rfl⟩ : syracuseStep 910903 = 1366355) B1366355
theorem B1533505 : Blo 806344 1533505 := bstep (se 2 (by rfl) ⟨575064, by rfl⟩ : syracuseStep 1533505 = 1150129) B1150129
theorem B3696301 : Blo 806344 3696301 := bstep (se 3 (by rfl) ⟨693056, by rfl⟩ : syracuseStep 3696301 = 1386113) B1386113
theorem B1730251 : Blo 806344 1730251 := bstep (se 1 (by rfl) ⟨1297688, by rfl⟩ : syracuseStep 1730251 = 2595377) B2595377
theorem B911083 : Blo 806344 911083 := bstep (se 1 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 911083 = 1366625) B1366625
theorem B1730327 : Blo 806344 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B911191 : Blo 806344 911191 := bstep (se 1 (by rfl) ⟨683393, by rfl⟩ : syracuseStep 911191 = 1366787) B1366787
theorem B6547331 : Blo 806344 6547331 := bstep (se 1 (by rfl) ⟨4910498, by rfl⟩ : syracuseStep 6547331 = 9820997) B9820997
theorem B3893123 : Blo 806344 3893123 := bstep (se 1 (by rfl) ⟨2919842, by rfl⟩ : syracuseStep 3893123 = 5839685) B5839685
theorem B1533953 : Blo 806344 1533953 := bstep (se 2 (by rfl) ⟨575232, by rfl⟩ : syracuseStep 1533953 = 1150465) B1150465
theorem B911371 : Blo 806344 911371 := bstep (se 1 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 911371 = 1367057) B1367057
theorem B3074071 : Blo 806344 3074071 := bstep (se 1 (by rfl) ⟨2305553, by rfl⟩ : syracuseStep 3074071 = 4611107) B4611107
theorem B911479 : Blo 806344 911479 := bstep (se 1 (by rfl) ⟨683609, by rfl⟩ : syracuseStep 911479 = 1367219) B1367219
theorem B1534295 : Blo 806344 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B3893777 : Blo 806344 3893777 := bstep (se 2 (by rfl) ⟨1460166, by rfl⟩ : syracuseStep 3893777 = 2920333) B2920333
theorem B4614731 : Blo 806344 4614731 := bstep (se 1 (by rfl) ⟨3461048, by rfl⟩ : syracuseStep 4614731 = 6922097) B6922097
theorem B4090499 : Blo 806344 4090499 := bstep (se 1 (by rfl) ⟨3067874, by rfl⟩ : syracuseStep 4090499 = 6135749) B6135749
theorem B3271427 : Blo 806344 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B3074861 : Blo 806344 3074861 := bstep (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) B1153073
theorem B5172119 : Blo 806344 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B1534963 : Blo 806344 1534963 := bstep (se 1 (by rfl) ⟨1151222, by rfl⟩ : syracuseStep 1534963 = 2302445) B2302445
theorem B2911307 : Blo 806344 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B7761253 : Blo 806344 7761253 := bstep (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) B1455235
theorem B1535411 : Blo 806344 1535411 := bstep (se 1 (by rfl) ⟨1151558, by rfl⟩ : syracuseStep 1535411 = 2303117) B2303117
theorem B1535449 : Blo 806344 1535449 := bstep (se 2 (by rfl) ⟨575793, by rfl⟩ : syracuseStep 1535449 = 1151587) B1151587
theorem B10350341 : Blo 806344 10350341 := bstep (se 4 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 10350341 = 1940689) B1940689
theorem B1535897 : Blo 806344 1535897 := bstep (se 2 (by rfl) ⟨575961, by rfl⟩ : syracuseStep 1535897 = 1151923) B1151923
theorem B4911205 : Blo 806344 4911205 := bstep (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) B920851
theorem B3371153 : Blo 806344 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B2584727 : Blo 806344 2584727 := bstep (se 1 (by rfl) ⟨1938545, by rfl⟩ : syracuseStep 2584727 = 3877091) B3877091
theorem B3076289 : Blo 806344 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B3502595 : Blo 806344 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B1536641 : Blo 806344 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B2585267 : Blo 806344 2585267 := bstep (se 1 (by rfl) ⟨1938950, by rfl⟩ : syracuseStep 2585267 = 3877901) B3877901
theorem B1536907 : Blo 806344 1536907 := bstep (se 1 (by rfl) ⟨1152680, by rfl⟩ : syracuseStep 1536907 = 2305361) B2305361
theorem B23655685 : Blo 806344 23655685 := bstep (se 4 (by rfl) ⟨2217720, by rfl⟩ : syracuseStep 23655685 = 4435441) B4435441
theorem B1209611 : Blo 806344 1209611 := bstep (se 1 (by rfl) ⟨907208, by rfl⟩ : syracuseStep 1209611 = 1814417) B1814417
theorem B1209623 : Blo 806344 1209623 := bstep (se 1 (by rfl) ⟨907217, by rfl⟩ : syracuseStep 1209623 = 1814435) B1814435
theorem B1537355 : Blo 806344 1537355 := bstep (se 1 (by rfl) ⟨1153016, by rfl⟩ : syracuseStep 1537355 = 2306033) B2306033
theorem B1209689 : Blo 806344 1209689 := bstep (se 2 (by rfl) ⟨453633, by rfl⟩ : syracuseStep 1209689 = 907267) B907267
theorem B2585945 : Blo 806344 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B1209803 : Blo 806344 1209803 := bstep (se 1 (by rfl) ⟨907352, by rfl⟩ : syracuseStep 1209803 = 1814705) B1814705
theorem B1209815 : Blo 806344 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B1537537 : Blo 806344 1537537 := bstep (se 2 (by rfl) ⟨576576, by rfl⟩ : syracuseStep 1537537 = 1153153) B1153153
theorem B1209881 : Blo 806344 1209881 := bstep (se 2 (by rfl) ⟨453705, by rfl⟩ : syracuseStep 1209881 = 907411) B907411
theorem B1209995 : Blo 806344 1209995 := bstep (se 1 (by rfl) ⟨907496, by rfl⟩ : syracuseStep 1209995 = 1814993) B1814993
theorem B1210007 : Blo 806344 1210007 := bstep (se 1 (by rfl) ⟨907505, by rfl⟩ : syracuseStep 1210007 = 1815011) B1815011
theorem B1210073 : Blo 806344 1210073 := bstep (se 2 (by rfl) ⟨453777, by rfl⟩ : syracuseStep 1210073 = 907555) B907555
theorem B1210187 : Blo 806344 1210187 := bstep (se 1 (by rfl) ⟨907640, by rfl⟩ : syracuseStep 1210187 = 1815281) B1815281
theorem B1210199 : Blo 806344 1210199 := bstep (se 1 (by rfl) ⟨907649, by rfl⟩ : syracuseStep 1210199 = 1815299) B1815299
theorem B1537879 : Blo 806344 1537879 := bstep (se 1 (by rfl) ⟨1153409, by rfl⟩ : syracuseStep 1537879 = 2306819) B2306819
theorem B1210265 : Blo 806344 1210265 := bstep (se 2 (by rfl) ⟨453849, by rfl⟩ : syracuseStep 1210265 = 907699) B907699
theorem B1210379 : Blo 806344 1210379 := bstep (se 1 (by rfl) ⟨907784, by rfl⟩ : syracuseStep 1210379 = 1815569) B1815569
theorem B1210391 : Blo 806344 1210391 := bstep (se 1 (by rfl) ⟨907793, by rfl⟩ : syracuseStep 1210391 = 1815587) B1815587
theorem B1538099 : Blo 806344 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B1210457 : Blo 806344 1210457 := bstep (se 2 (by rfl) ⟨453921, by rfl⟩ : syracuseStep 1210457 = 907843) B907843
theorem B3274931 : Blo 806344 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B1210571 : Blo 806344 1210571 := bstep (se 1 (by rfl) ⟨907928, by rfl⟩ : syracuseStep 1210571 = 1815857) B1815857
theorem B1210583 : Blo 806344 1210583 := bstep (se 1 (by rfl) ⟨907937, by rfl⟩ : syracuseStep 1210583 = 1815875) B1815875
theorem B4094225 : Blo 806344 4094225 := bstep (se 2 (by rfl) ⟨1535334, by rfl⟩ : syracuseStep 4094225 = 3070669) B3070669
theorem B1538327 : Blo 806344 1538327 := bstep (se 1 (by rfl) ⟨1153745, by rfl⟩ : syracuseStep 1538327 = 2307491) B2307491
theorem B1210649 : Blo 806344 1210649 := bstep (se 2 (by rfl) ⟨453993, by rfl⟩ : syracuseStep 1210649 = 907987) B907987
theorem B5536075 : Blo 806344 5536075 := bstep (se 1 (by rfl) ⟨4152056, by rfl⟩ : syracuseStep 5536075 = 8304113) B8304113
theorem B1210763 : Blo 806344 1210763 := bstep (se 1 (by rfl) ⟨908072, by rfl⟩ : syracuseStep 1210763 = 1816145) B1816145
theorem B1210775 : Blo 806344 1210775 := bstep (se 1 (by rfl) ⟨908081, by rfl⟩ : syracuseStep 1210775 = 1816163) B1816163
theorem B4094387 : Blo 806344 4094387 := bstep (se 1 (by rfl) ⟨3070790, by rfl⟩ : syracuseStep 4094387 = 6141581) B6141581
theorem B6126029 : Blo 806344 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B1210841 : Blo 806344 1210841 := bstep (se 2 (by rfl) ⟨454065, by rfl⟩ : syracuseStep 1210841 = 908131) B908131
theorem B2587187 : Blo 806344 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B1210955 : Blo 806344 1210955 := bstep (se 1 (by rfl) ⟨908216, by rfl⟩ : syracuseStep 1210955 = 1816433) B1816433
theorem B1636939 : Blo 806344 1636939 := bstep (se 1 (by rfl) ⟨1227704, by rfl⟩ : syracuseStep 1636939 = 2455409) B2455409
theorem B1210967 : Blo 806344 1210967 := bstep (se 1 (by rfl) ⟨908225, by rfl⟩ : syracuseStep 1210967 = 1816451) B1816451
theorem B1211033 : Blo 806344 1211033 := bstep (se 2 (by rfl) ⟨454137, by rfl⟩ : syracuseStep 1211033 = 908275) B908275
theorem B1211147 : Blo 806344 1211147 := bstep (se 1 (by rfl) ⟨908360, by rfl⟩ : syracuseStep 1211147 = 1816721) B1816721
theorem B3373841 : Blo 806344 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B1211159 : Blo 806344 1211159 := bstep (se 1 (by rfl) ⟨908369, by rfl⟩ : syracuseStep 1211159 = 1816739) B1816739
theorem B1309529 : Blo 806344 1309529 := bstep (se 2 (by rfl) ⟨491073, by rfl⟩ : syracuseStep 1309529 = 982147) B982147
theorem B1211225 : Blo 806344 1211225 := bstep (se 2 (by rfl) ⟨454209, by rfl⟩ : syracuseStep 1211225 = 908419) B908419
theorem B6126515 : Blo 806344 6126515 := bstep (se 1 (by rfl) ⟨4594886, by rfl⟩ : syracuseStep 6126515 = 9189773) B9189773
theorem B1211339 : Blo 806344 1211339 := bstep (se 1 (by rfl) ⟨908504, by rfl⟩ : syracuseStep 1211339 = 1817009) B1817009
theorem B1211351 : Blo 806344 1211351 := bstep (se 1 (by rfl) ⟨908513, by rfl⟩ : syracuseStep 1211351 = 1817027) B1817027
theorem B1637399 : Blo 806344 1637399 := bstep (se 1 (by rfl) ⟨1228049, by rfl⟩ : syracuseStep 1637399 = 2456099) B2456099
theorem B1211417 : Blo 806344 1211417 := bstep (se 2 (by rfl) ⟨454281, by rfl⟩ : syracuseStep 1211417 = 908563) B908563
theorem B1309783 : Blo 806344 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B1211531 : Blo 806344 1211531 := bstep (se 1 (by rfl) ⟨908648, by rfl⟩ : syracuseStep 1211531 = 1817297) B1817297
theorem B1211543 : Blo 806344 1211543 := bstep (se 1 (by rfl) ⟨908657, by rfl⟩ : syracuseStep 1211543 = 1817315) B1817315
theorem B1211609 : Blo 806344 1211609 := bstep (se 2 (by rfl) ⟨454353, by rfl⟩ : syracuseStep 1211609 = 908707) B908707
theorem B3276035 : Blo 806344 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B7765253 : Blo 806344 7765253 := bstep (se 4 (by rfl) ⟨727992, by rfl⟩ : syracuseStep 7765253 = 1455985) B1455985
theorem B1211723 : Blo 806344 1211723 := bstep (se 1 (by rfl) ⟨908792, by rfl⟩ : syracuseStep 1211723 = 1817585) B1817585
theorem B7011659 : Blo 806344 7011659 := bstep (se 1 (by rfl) ⟨5258744, by rfl⟩ : syracuseStep 7011659 = 10517489) B10517489
theorem B1211735 : Blo 806344 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B4914533 : Blo 806344 4914533 := bstep (se 4 (by rfl) ⟨460737, by rfl⟩ : syracuseStep 4914533 = 921475) B921475
theorem B1211801 : Blo 806344 1211801 := bstep (se 2 (by rfl) ⟨454425, by rfl⟩ : syracuseStep 1211801 = 908851) B908851
theorem B2915777 : Blo 806344 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B818635 : Blo 806344 818635 := bstep (se 1 (by rfl) ⟨613976, by rfl⟩ : syracuseStep 818635 = 1227953) B1227953
theorem B1211915 : Blo 806344 1211915 := bstep (se 1 (by rfl) ⟨908936, by rfl⟩ : syracuseStep 1211915 = 1817873) B1817873
theorem B1211927 : Blo 806344 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B1211993 : Blo 806344 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B1212107 : Blo 806344 1212107 := bstep (se 1 (by rfl) ⟨909080, by rfl⟩ : syracuseStep 1212107 = 1818161) B1818161
theorem B1212119 : Blo 806344 1212119 := bstep (se 1 (by rfl) ⟨909089, by rfl⟩ : syracuseStep 1212119 = 1818179) B1818179
theorem B1212185 : Blo 806344 1212185 := bstep (se 2 (by rfl) ⟨454569, by rfl⟩ : syracuseStep 1212185 = 909139) B909139
theorem B1212299 : Blo 806344 1212299 := bstep (se 1 (by rfl) ⟨909224, by rfl⟩ : syracuseStep 1212299 = 1818449) B1818449
theorem B1212311 : Blo 806344 1212311 := bstep (se 1 (by rfl) ⟨909233, by rfl⟩ : syracuseStep 1212311 = 1818467) B1818467
theorem B6913997 : Blo 806344 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B1212377 : Blo 806344 1212377 := bstep (se 2 (by rfl) ⟨454641, by rfl⟩ : syracuseStep 1212377 = 909283) B909283
theorem B1212431 : Blo 806344 1212431 := bstep (se 1 (by rfl) ⟨909323, by rfl⟩ : syracuseStep 1212431 = 1818647) B1818647
theorem B2490401 : Blo 806344 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B1212473 : Blo 806344 1212473 := bstep (se 2 (by rfl) ⟨454677, by rfl⟩ : syracuseStep 1212473 = 909355) B909355
theorem B1212551 : Blo 806344 1212551 := bstep (se 1 (by rfl) ⟨909413, by rfl⟩ : syracuseStep 1212551 = 1818827) B1818827
theorem B1212587 : Blo 806344 1212587 := bstep (se 1 (by rfl) ⟨909440, by rfl⟩ : syracuseStep 1212587 = 1818881) B1818881
theorem B1212617 : Blo 806344 1212617 := bstep (se 2 (by rfl) ⟨454731, by rfl⟩ : syracuseStep 1212617 = 909463) B909463
theorem B4980973 : Blo 806344 4980973 := bstep (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) B1867865
theorem B1212731 : Blo 806344 1212731 := bstep (se 1 (by rfl) ⟨909548, by rfl⟩ : syracuseStep 1212731 = 1819097) B1819097
theorem B1212791 : Blo 806344 1212791 := bstep (se 1 (by rfl) ⟨909593, by rfl⟩ : syracuseStep 1212791 = 1819187) B1819187
theorem B1212815 : Blo 806344 1212815 := bstep (se 1 (by rfl) ⟨909611, by rfl⟩ : syracuseStep 1212815 = 1819223) B1819223
theorem B1212857 : Blo 806344 1212857 := bstep (se 2 (by rfl) ⟨454821, by rfl⟩ : syracuseStep 1212857 = 909643) B909643
theorem B1212935 : Blo 806344 1212935 := bstep (se 1 (by rfl) ⟨909701, by rfl⟩ : syracuseStep 1212935 = 1819403) B1819403
theorem B1212971 : Blo 806344 1212971 := bstep (se 1 (by rfl) ⟨909728, by rfl⟩ : syracuseStep 1212971 = 1819457) B1819457
theorem B1213001 : Blo 806344 1213001 := bstep (se 2 (by rfl) ⟨454875, by rfl⟩ : syracuseStep 1213001 = 909751) B909751
theorem B1213115 : Blo 806344 1213115 := bstep (se 1 (by rfl) ⟨909836, by rfl⟩ : syracuseStep 1213115 = 1819673) B1819673
theorem B1213175 : Blo 806344 1213175 := bstep (se 1 (by rfl) ⟨909881, by rfl⟩ : syracuseStep 1213175 = 1819763) B1819763
theorem B1213199 : Blo 806344 1213199 := bstep (se 1 (by rfl) ⟨909899, by rfl⟩ : syracuseStep 1213199 = 1819799) B1819799
theorem B1213241 : Blo 806344 1213241 := bstep (se 2 (by rfl) ⟨454965, by rfl⟩ : syracuseStep 1213241 = 909931) B909931
theorem B1213319 : Blo 806344 1213319 := bstep (se 1 (by rfl) ⟨909989, by rfl⟩ : syracuseStep 1213319 = 1819979) B1819979
theorem B820103 : Blo 806344 820103 := bstep (se 1 (by rfl) ⟨615077, by rfl⟩ : syracuseStep 820103 = 1230155) B1230155
theorem B9208727 : Blo 806344 9208727 := bstep (se 1 (by rfl) ⟨6906545, by rfl⟩ : syracuseStep 9208727 = 13813091) B13813091
theorem B3277721 : Blo 806344 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B1213355 : Blo 806344 1213355 := bstep (se 1 (by rfl) ⟨910016, by rfl⟩ : syracuseStep 1213355 = 1820033) B1820033
theorem B1213385 : Blo 806344 1213385 := bstep (se 2 (by rfl) ⟨455019, by rfl⟩ : syracuseStep 1213385 = 910039) B910039
theorem B1213499 : Blo 806344 1213499 := bstep (se 1 (by rfl) ⟨910124, by rfl⟩ : syracuseStep 1213499 = 1820249) B1820249
theorem B1213559 : Blo 806344 1213559 := bstep (se 1 (by rfl) ⟨910169, by rfl⟩ : syracuseStep 1213559 = 1820339) B1820339
theorem B1213583 : Blo 806344 1213583 := bstep (se 1 (by rfl) ⟨910187, by rfl⟩ : syracuseStep 1213583 = 1820375) B1820375
theorem B1213625 : Blo 806344 1213625 := bstep (se 2 (by rfl) ⟨455109, by rfl⟩ : syracuseStep 1213625 = 910219) B910219
theorem B1213703 : Blo 806344 1213703 := bstep (se 1 (by rfl) ⟨910277, by rfl⟩ : syracuseStep 1213703 = 1820555) B1820555
theorem B1213739 : Blo 806344 1213739 := bstep (se 1 (by rfl) ⟨910304, by rfl⟩ : syracuseStep 1213739 = 1820609) B1820609
theorem B1213769 : Blo 806344 1213769 := bstep (se 2 (by rfl) ⟨455163, by rfl⟩ : syracuseStep 1213769 = 910327) B910327
theorem B1639865 : Blo 806344 1639865 := bstep (se 2 (by rfl) ⟨614949, by rfl⟩ : syracuseStep 1639865 = 1229899) B1229899
theorem B4097465 : Blo 806344 4097465 := bstep (se 2 (by rfl) ⟨1536549, by rfl⟩ : syracuseStep 4097465 = 3073099) B3073099
theorem B1213883 : Blo 806344 1213883 := bstep (se 1 (by rfl) ⟨910412, by rfl⟩ : syracuseStep 1213883 = 1820825) B1820825
theorem B1213943 : Blo 806344 1213943 := bstep (se 1 (by rfl) ⟨910457, by rfl⟩ : syracuseStep 1213943 = 1820915) B1820915
theorem B1213967 : Blo 806344 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B1214009 : Blo 806344 1214009 := bstep (se 2 (by rfl) ⟨455253, by rfl⟩ : syracuseStep 1214009 = 910507) B910507
theorem B1214087 : Blo 806344 1214087 := bstep (se 1 (by rfl) ⟨910565, by rfl⟩ : syracuseStep 1214087 = 1821131) B1821131
theorem B1214123 : Blo 806344 1214123 := bstep (se 1 (by rfl) ⟨910592, by rfl⟩ : syracuseStep 1214123 = 1821185) B1821185
theorem B1214153 : Blo 806344 1214153 := bstep (se 2 (by rfl) ⟨455307, by rfl⟩ : syracuseStep 1214153 = 910615) B910615
theorem B1214267 : Blo 806344 1214267 := bstep (se 1 (by rfl) ⟨910700, by rfl⟩ : syracuseStep 1214267 = 1821401) B1821401
theorem B1214327 : Blo 806344 1214327 := bstep (se 1 (by rfl) ⟨910745, by rfl⟩ : syracuseStep 1214327 = 1821491) B1821491
theorem B1214351 : Blo 806344 1214351 := bstep (se 1 (by rfl) ⟨910763, by rfl⟩ : syracuseStep 1214351 = 1821527) B1821527
theorem B1214393 : Blo 806344 1214393 := bstep (se 2 (by rfl) ⟨455397, by rfl⟩ : syracuseStep 1214393 = 910795) B910795
theorem B1214471 : Blo 806344 1214471 := bstep (se 1 (by rfl) ⟨910853, by rfl⟩ : syracuseStep 1214471 = 1821707) B1821707
theorem B21235729 : Blo 806344 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1214507 : Blo 806344 1214507 := bstep (se 1 (by rfl) ⟨910880, by rfl⟩ : syracuseStep 1214507 = 1821761) B1821761
theorem B1214537 : Blo 806344 1214537 := bstep (se 2 (by rfl) ⟨455451, by rfl⟩ : syracuseStep 1214537 = 910903) B910903
theorem B1214651 : Blo 806344 1214651 := bstep (se 1 (by rfl) ⟨910988, by rfl⟩ : syracuseStep 1214651 = 1821977) B1821977
theorem B1214711 : Blo 806344 1214711 := bstep (se 1 (by rfl) ⟨911033, by rfl⟩ : syracuseStep 1214711 = 1822067) B1822067
theorem B1214735 : Blo 806344 1214735 := bstep (se 1 (by rfl) ⟨911051, by rfl⟩ : syracuseStep 1214735 = 1822103) B1822103
theorem B11634961 : Blo 806344 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B1214777 : Blo 806344 1214777 := bstep (se 2 (by rfl) ⟨455541, by rfl⟩ : syracuseStep 1214777 = 911083) B911083
theorem B1214855 : Blo 806344 1214855 := bstep (se 1 (by rfl) ⟨911141, by rfl⟩ : syracuseStep 1214855 = 1822283) B1822283
theorem B1214891 : Blo 806344 1214891 := bstep (se 1 (by rfl) ⟨911168, by rfl⟩ : syracuseStep 1214891 = 1822337) B1822337
theorem B1214921 : Blo 806344 1214921 := bstep (se 2 (by rfl) ⟨455595, by rfl⟩ : syracuseStep 1214921 = 911191) B911191
theorem B1215035 : Blo 806344 1215035 := bstep (se 1 (by rfl) ⟨911276, by rfl⟩ : syracuseStep 1215035 = 1822553) B1822553
theorem B11045443 : Blo 806344 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B1215095 : Blo 806344 1215095 := bstep (se 1 (by rfl) ⟨911321, by rfl⟩ : syracuseStep 1215095 = 1822643) B1822643
theorem B1215119 : Blo 806344 1215119 := bstep (se 1 (by rfl) ⟨911339, by rfl⟩ : syracuseStep 1215119 = 1822679) B1822679
theorem B1215161 : Blo 806344 1215161 := bstep (se 2 (by rfl) ⟨455685, by rfl⟩ : syracuseStep 1215161 = 911371) B911371
theorem B4098761 : Blo 806344 4098761 := bstep (se 2 (by rfl) ⟨1537035, by rfl⟩ : syracuseStep 4098761 = 3074071) B3074071
theorem B1215239 : Blo 806344 1215239 := bstep (se 1 (by rfl) ⟨911429, by rfl⟩ : syracuseStep 1215239 = 1822859) B1822859
theorem B1215275 : Blo 806344 1215275 := bstep (se 1 (by rfl) ⟨911456, by rfl⟩ : syracuseStep 1215275 = 1822913) B1822913
theorem B1215305 : Blo 806344 1215305 := bstep (se 2 (by rfl) ⟨455739, by rfl⟩ : syracuseStep 1215305 = 911479) B911479
theorem B1215419 : Blo 806344 1215419 := bstep (se 1 (by rfl) ⟨911564, by rfl⟩ : syracuseStep 1215419 = 1823129) B1823129
theorem B1215479 : Blo 806344 1215479 := bstep (se 1 (by rfl) ⟨911609, by rfl⟩ : syracuseStep 1215479 = 1823219) B1823219
theorem B4918283 : Blo 806344 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B1215503 : Blo 806344 1215503 := bstep (se 1 (by rfl) ⟨911627, by rfl⟩ : syracuseStep 1215503 = 1823255) B1823255
theorem B6130889 : Blo 806344 6130889 := bstep (se 2 (by rfl) ⟨2299083, by rfl⟩ : syracuseStep 6130889 = 4598167) B4598167
theorem B2723219 : Blo 806344 2723219 := bstep (se 1 (by rfl) ⟨2042414, by rfl⟩ : syracuseStep 2723219 = 4084829) B4084829
theorem B3280445 : Blo 806344 3280445 := bstep (se 3 (by rfl) ⟨615083, by rfl⟩ : syracuseStep 3280445 = 1230167) B1230167
theorem B2461697 : Blo 806344 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B1839119 : Blo 806344 1839119 := bstep (se 1 (by rfl) ⟨1379339, by rfl⟩ : syracuseStep 1839119 = 2758679) B2758679
theorem B2297899 : Blo 806344 2297899 := bstep (se 1 (by rfl) ⟨1723424, by rfl⟩ : syracuseStep 2297899 = 3446849) B3446849
theorem B1347643 : Blo 806344 1347643 := bstep (se 1 (by rfl) ⟨1010732, by rfl⟩ : syracuseStep 1347643 = 2021465) B2021465
theorem B2298127 : Blo 806344 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B4657441 : Blo 806344 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B2298401 : Blo 806344 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B1938007 : Blo 806344 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B2462327 : Blo 806344 2462327 := bstep (se 1 (by rfl) ⟨1846745, by rfl⟩ : syracuseStep 2462327 = 3693491) B3693491
theorem B7377637 : Blo 806344 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B2724623 : Blo 806344 2724623 := bstep (se 1 (by rfl) ⟨2043467, by rfl⟩ : syracuseStep 2724623 = 4086935) B4086935
theorem B2593595 : Blo 806344 2593595 := bstep (se 1 (by rfl) ⟨1945196, by rfl⟩ : syracuseStep 2593595 = 3890393) B3890393
theorem B2298743 : Blo 806344 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B1020919 : Blo 806344 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B2724893 : Blo 806344 2724893 := bstep (se 3 (by rfl) ⟨510917, by rfl⟩ : syracuseStep 2724893 = 1021835) B1021835
theorem B9213101 : Blo 806344 9213101 := bstep (se 3 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 9213101 = 3454913) B3454913
theorem B1021243 : Blo 806344 1021243 := bstep (se 1 (by rfl) ⟨765932, by rfl⟩ : syracuseStep 1021243 = 1531865) B1531865
theorem B36410809 : Blo 806344 36410809 := bstep (se 2 (by rfl) ⟨13654053, by rfl⟩ : syracuseStep 36410809 = 27308107) B27308107
theorem B2299403 : Blo 806344 2299403 := bstep (se 1 (by rfl) ⟨1724552, by rfl⟩ : syracuseStep 2299403 = 3449105) B3449105
theorem B19699301 : Blo 806344 19699301 := bstep (se 4 (by rfl) ⟨1846809, by rfl⟩ : syracuseStep 19699301 = 3693619) B3693619
theorem B1939315 : Blo 806344 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B4593611 : Blo 806344 4593611 := bstep (se 1 (by rfl) ⟨3445208, by rfl⟩ : syracuseStep 4593611 = 6890417) B6890417
theorem B4987109 : Blo 806344 4987109 := bstep (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) B935083
theorem B1022215 : Blo 806344 1022215 := bstep (se 1 (by rfl) ⟨766661, by rfl⟩ : syracuseStep 1022215 = 1533323) B1533323
theorem B4594067 : Blo 806344 4594067 := bstep (se 1 (by rfl) ⟨3445550, by rfl⟩ : syracuseStep 4594067 = 6891101) B6891101
theorem B2726297 : Blo 806344 2726297 := bstep (se 2 (by rfl) ⟨1022361, by rfl⟩ : syracuseStep 2726297 = 2044723) B2044723
theorem B6232643 : Blo 806344 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B4364887 : Blo 806344 4364887 := bstep (se 1 (by rfl) ⟨3273665, by rfl⟩ : syracuseStep 4364887 = 6547331) B6547331
theorem B2595415 : Blo 806344 2595415 := bstep (se 1 (by rfl) ⟨1946561, by rfl⟩ : syracuseStep 2595415 = 3893123) B3893123
theorem B1022635 : Blo 806344 1022635 := bstep (se 1 (by rfl) ⟨766976, by rfl⟩ : syracuseStep 1022635 = 1533953) B1533953
theorem B1383227 : Blo 806344 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B1022863 : Blo 806344 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B2759609 : Blo 806344 2759609 := bstep (se 2 (by rfl) ⟨1034853, by rfl⟩ : syracuseStep 2759609 = 2069707) B2069707
theorem B2595851 : Blo 806344 2595851 := bstep (se 1 (by rfl) ⟨1946888, by rfl⟩ : syracuseStep 2595851 = 3893777) B3893777
theorem B2300987 : Blo 806344 2300987 := bstep (se 1 (by rfl) ⟨1725740, by rfl⟩ : syracuseStep 2300987 = 3451481) B3451481
theorem B15735869 : Blo 806344 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B2595901 : Blo 806344 2595901 := bstep (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) B973463
theorem B2726999 : Blo 806344 2726999 := bstep (se 1 (by rfl) ⟨2045249, by rfl⟩ : syracuseStep 2726999 = 4090499) B4090499
theorem B1973335 : Blo 806344 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B2301043 : Blo 806344 2301043 := bstep (se 1 (by rfl) ⟨1725782, by rfl⟩ : syracuseStep 2301043 = 3451565) B3451565
theorem B3448079 : Blo 806344 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B2301385 : Blo 806344 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B4922903 : Blo 806344 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B2727485 : Blo 806344 2727485 := bstep (se 3 (by rfl) ⟨511403, by rfl⟩ : syracuseStep 2727485 = 1022807) B1022807
theorem B1023607 : Blo 806344 1023607 := bstep (se 1 (by rfl) ⟨767705, by rfl⟩ : syracuseStep 1023607 = 1535411) B1535411
theorem B5185295 : Blo 806344 5185295 := bstep (se 1 (by rfl) ⟨3888971, by rfl⟩ : syracuseStep 5185295 = 7777943) B7777943
theorem B5250905 : Blo 806344 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B1023931 : Blo 806344 1023931 := bstep (se 1 (by rfl) ⟨767948, by rfl⟩ : syracuseStep 1023931 = 1535897) B1535897
theorem B4366397 : Blo 806344 4366397 := bstep (se 3 (by rfl) ⟨818699, by rfl⟩ : syracuseStep 4366397 = 1637399) B1637399
theorem B2335063 : Blo 806344 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B1024427 : Blo 806344 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B7381433 : Blo 806344 7381433 := bstep (se 2 (by rfl) ⟨2768037, by rfl⟩ : syracuseStep 7381433 = 5536075) B5536075
theorem B1024903 : Blo 806344 1024903 := bstep (se 1 (by rfl) ⟨768677, by rfl⟩ : syracuseStep 1024903 = 1537355) B1537355
theorem B2728889 : Blo 806344 2728889 := bstep (se 2 (by rfl) ⟨1023333, by rfl⟩ : syracuseStep 2728889 = 2046667) B2046667
theorem B3875843 : Blo 806344 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B6628439 : Blo 806344 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B1025399 : Blo 806344 1025399 := bstep (se 1 (by rfl) ⟨769049, by rfl⟩ : syracuseStep 1025399 = 1538099) B1538099
theorem B1746377 : Blo 806344 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B2729483 : Blo 806344 2729483 := bstep (se 1 (by rfl) ⟨2047112, by rfl⟩ : syracuseStep 2729483 = 4094225) B4094225
theorem B1025551 : Blo 806344 1025551 := bstep (se 1 (by rfl) ⟨769163, by rfl⟩ : syracuseStep 1025551 = 1538327) B1538327
theorem B1844795 : Blo 806344 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B2303549 : Blo 806344 2303549 := bstep (se 3 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 2303549 = 863831) B863831
theorem B2041463 : Blo 806344 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B2729591 : Blo 806344 2729591 := bstep (se 1 (by rfl) ⟨2047193, by rfl⟩ : syracuseStep 2729591 = 4094387) B4094387
theorem B861883 : Blo 806344 861883 := bstep (se 1 (by rfl) ⟨646412, by rfl⟩ : syracuseStep 861883 = 1292825) B1292825
theorem B2303777 : Blo 806344 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B1091513 : Blo 806344 1091513 := bstep (se 2 (by rfl) ⟨409317, by rfl⟩ : syracuseStep 1091513 = 818635) B818635
theorem B2304119 : Blo 806344 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B2730185 : Blo 806344 2730185 := bstep (se 2 (by rfl) ⟨1023819, by rfl⟩ : syracuseStep 2730185 = 2047639) B2047639
theorem B1943851 : Blo 806344 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B2337281 : Blo 806344 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B4139581 : Blo 806344 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B2042455 : Blo 806344 2042455 := bstep (se 1 (by rfl) ⟨1531841, by rfl⟩ : syracuseStep 2042455 = 3063683) B3063683
theorem B4926209 : Blo 806344 4926209 := bstep (se 2 (by rfl) ⟨1847328, by rfl⟩ : syracuseStep 4926209 = 3694657) B3694657
theorem B2042759 : Blo 806344 2042759 := bstep (se 1 (by rfl) ⟨1532069, by rfl⟩ : syracuseStep 2042759 = 3064139) B3064139
theorem B2730887 : Blo 806344 2730887 := bstep (se 1 (by rfl) ⟨2048165, by rfl⟩ : syracuseStep 2730887 = 4096331) B4096331
theorem B2042891 : Blo 806344 2042891 := bstep (se 1 (by rfl) ⟨1532168, by rfl⟩ : syracuseStep 2042891 = 3064337) B3064337
theorem B8989741 : Blo 806344 8989741 := bstep (se 3 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 8989741 = 3371153) B3371153
theorem B2731265 : Blo 806344 2731265 := bstep (se 2 (by rfl) ⟨1024224, by rfl⟩ : syracuseStep 2731265 = 2048449) B2048449
theorem B14757329 : Blo 806344 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B2043407 : Blo 806344 2043407 := bstep (se 1 (by rfl) ⟨1532555, by rfl⟩ : syracuseStep 2043407 = 3065111) B3065111
theorem B6565495 : Blo 806344 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B2043539 : Blo 806344 2043539 := bstep (se 1 (by rfl) ⟨1532654, by rfl⟩ : syracuseStep 2043539 = 3065309) B3065309
theorem B1814543 : Blo 806344 1814543 := bstep (se 1 (by rfl) ⟨1360907, by rfl⟩ : syracuseStep 1814543 = 2721815) B2721815
theorem B1814561 : Blo 806344 1814561 := bstep (se 2 (by rfl) ⟨680460, by rfl⟩ : syracuseStep 1814561 = 1360921) B1360921
theorem B2732075 : Blo 806344 2732075 := bstep (se 1 (by rfl) ⟨2049056, by rfl⟩ : syracuseStep 2732075 = 4098113) B4098113
theorem B1847567 : Blo 806344 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B4993331 : Blo 806344 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B1814903 : Blo 806344 1814903 := bstep (se 1 (by rfl) ⟨1361177, by rfl⟩ : syracuseStep 1814903 = 2722355) B2722355
theorem B9843079 : Blo 806344 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B1946003 : Blo 806344 1946003 := bstep (se 1 (by rfl) ⟨1459502, by rfl⟩ : syracuseStep 1946003 = 2919005) B2919005
theorem B1749433 : Blo 806344 1749433 := bstep (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) B1312075
theorem B1815083 : Blo 806344 1815083 := bstep (se 1 (by rfl) ⟨1361312, by rfl⟩ : syracuseStep 1815083 = 2722625) B2722625
theorem B6566467 : Blo 806344 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B2306647 : Blo 806344 2306647 := bstep (se 1 (by rfl) ⟨1729985, by rfl⟩ : syracuseStep 2306647 = 3459971) B3459971
theorem B864955 : Blo 806344 864955 := bstep (se 1 (by rfl) ⟨648716, by rfl⟩ : syracuseStep 864955 = 1297433) B1297433
theorem B6140609 : Blo 806344 6140609 := bstep (se 2 (by rfl) ⟨2302728, by rfl⟩ : syracuseStep 6140609 = 4605457) B4605457
theorem B2044673 : Blo 806344 2044673 := bstep (se 2 (by rfl) ⟨766752, by rfl⟩ : syracuseStep 2044673 = 1533505) B1533505
theorem B2306875 : Blo 806344 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B4928401 : Blo 806344 4928401 := bstep (se 2 (by rfl) ⟨1848150, by rfl⟩ : syracuseStep 4928401 = 3696301) B3696301
theorem B1815443 : Blo 806344 1815443 := bstep (se 1 (by rfl) ⟨1361582, by rfl⟩ : syracuseStep 1815443 = 2723165) B2723165
theorem B2307001 : Blo 806344 2307001 := bstep (se 2 (by rfl) ⟨865125, by rfl⟩ : syracuseStep 2307001 = 1730251) B1730251
theorem B1815497 : Blo 806344 1815497 := bstep (se 2 (by rfl) ⟨680811, by rfl⟩ : syracuseStep 1815497 = 1361623) B1361623
theorem B1094671 : Blo 806344 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B2045047 : Blo 806344 2045047 := bstep (se 1 (by rfl) ⟨1533785, by rfl⟩ : syracuseStep 2045047 = 3067571) B3067571
theorem B2733371 : Blo 806344 2733371 := bstep (se 1 (by rfl) ⟨2050028, by rfl⟩ : syracuseStep 2733371 = 4100057) B4100057
theorem B21018041 : Blo 806344 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B5518891 : Blo 806344 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B2045483 : Blo 806344 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B1816199 : Blo 806344 1816199 := bstep (se 1 (by rfl) ⟨1362149, by rfl⟩ : syracuseStep 1816199 = 2724299) B2724299
theorem B9221849 : Blo 806344 9221849 := bstep (se 2 (by rfl) ⟨3458193, by rfl⟩ : syracuseStep 9221849 = 6916387) B6916387
theorem B2733857 : Blo 806344 2733857 := bstep (se 2 (by rfl) ⟨1025196, by rfl⟩ : syracuseStep 2733857 = 2050393) B2050393
theorem B1816379 : Blo 806344 1816379 := bstep (se 1 (by rfl) ⟨1362284, by rfl⟩ : syracuseStep 1816379 = 2724569) B2724569
theorem B6895475 : Blo 806344 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B16824181 : Blo 806344 16824181 := bstep (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) B1577267
theorem B1816505 : Blo 806344 1816505 := bstep (se 2 (by rfl) ⟨681189, by rfl⟩ : syracuseStep 1816505 = 1362379) B1362379
theorem B6895853 : Blo 806344 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B1816847 : Blo 806344 1816847 := bstep (se 1 (by rfl) ⟨1362635, by rfl⟩ : syracuseStep 1816847 = 2725271) B2725271
theorem B1816865 : Blo 806344 1816865 := bstep (se 2 (by rfl) ⟨681324, by rfl⟩ : syracuseStep 1816865 = 1362649) B1362649
theorem B2046323 : Blo 806344 2046323 := bstep (se 1 (by rfl) ⟨1534742, by rfl⟩ : syracuseStep 2046323 = 3069485) B3069485
theorem B2734451 : Blo 806344 2734451 := bstep (se 1 (by rfl) ⟨2050838, by rfl⟩ : syracuseStep 2734451 = 4101677) B4101677
theorem B2046343 : Blo 806344 2046343 := bstep (se 1 (by rfl) ⟨1534757, by rfl⟩ : syracuseStep 2046343 = 3069515) B3069515
theorem B3062225 : Blo 806344 3062225 := bstep (se 2 (by rfl) ⟨1148334, by rfl⟩ : syracuseStep 3062225 = 2296669) B2296669
theorem B1817207 : Blo 806344 1817207 := bstep (se 1 (by rfl) ⟨1362905, by rfl⟩ : syracuseStep 1817207 = 2725811) B2725811
theorem B3881591 : Blo 806344 3881591 := bstep (se 1 (by rfl) ⟨2911193, by rfl⟩ : syracuseStep 3881591 = 5822387) B5822387
theorem B2046617 : Blo 806344 2046617 := bstep (se 2 (by rfl) ⟨767481, by rfl⟩ : syracuseStep 2046617 = 1534963) B1534963
theorem B4602541 : Blo 806344 4602541 := bstep (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) B1725953
theorem B1817387 : Blo 806344 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B2046779 : Blo 806344 2046779 := bstep (se 1 (by rfl) ⟨1535084, by rfl⟩ : syracuseStep 2046779 = 3070169) B3070169
theorem B3062681 : Blo 806344 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B2046991 : Blo 806344 2046991 := bstep (se 1 (by rfl) ⟨1535243, by rfl⟩ : syracuseStep 2046991 = 3070487) B3070487
theorem B1817747 : Blo 806344 1817747 := bstep (se 1 (by rfl) ⟨1363310, by rfl⟩ : syracuseStep 1817747 = 2726621) B2726621
theorem B1817801 : Blo 806344 1817801 := bstep (se 2 (by rfl) ⟨681675, by rfl⟩ : syracuseStep 1817801 = 1363351) B1363351
theorem B2047265 : Blo 806344 2047265 := bstep (se 2 (by rfl) ⟨767724, by rfl⟩ : syracuseStep 2047265 = 1535449) B1535449
theorem B3456827 : Blo 806344 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B1818503 : Blo 806344 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B3882973 : Blo 806344 3882973 := bstep (se 3 (by rfl) ⟨728057, by rfl⟩ : syracuseStep 3882973 = 1456115) B1456115
theorem B6144011 : Blo 806344 6144011 := bstep (se 1 (by rfl) ⟨4608008, by rfl⟩ : syracuseStep 6144011 = 9216017) B9216017
theorem B35438627 : Blo 806344 35438627 := bstep (se 1 (by rfl) ⟨26578970, by rfl⟩ : syracuseStep 35438627 = 53157941) B53157941
theorem B3063851 : Blo 806344 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B1818683 : Blo 806344 1818683 := bstep (se 1 (by rfl) ⟨1364012, by rfl⟩ : syracuseStep 1818683 = 2728025) B2728025
theorem B1818809 : Blo 806344 1818809 := bstep (se 2 (by rfl) ⟨682053, by rfl⟩ : syracuseStep 1818809 = 1364107) B1364107
theorem B2048267 : Blo 806344 2048267 := bstep (se 1 (by rfl) ⟨1536200, by rfl⟩ : syracuseStep 2048267 = 3072401) B3072401
theorem B20693393 : Blo 806344 20693393 := bstep (se 2 (by rfl) ⟨7760022, by rfl⟩ : syracuseStep 20693393 = 15520045) B15520045
theorem B79577585 : Blo 806344 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B1819151 : Blo 806344 1819151 := bstep (se 1 (by rfl) ⟨1364363, by rfl⟩ : syracuseStep 1819151 = 2728727) B2728727
theorem B1819169 : Blo 806344 1819169 := bstep (se 2 (by rfl) ⟨682188, by rfl⟩ : syracuseStep 1819169 = 1364377) B1364377
theorem B3457579 : Blo 806344 3457579 := bstep (se 1 (by rfl) ⟨2593184, by rfl⟩ : syracuseStep 3457579 = 5186369) B5186369
theorem B1163911 : Blo 806344 1163911 := bstep (se 1 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 1163911 = 1745867) B1745867
theorem B1458977 : Blo 806344 1458977 := bstep (se 2 (by rfl) ⟨547116, by rfl⟩ : syracuseStep 1458977 = 1094233) B1094233
theorem B1360759 : Blo 806344 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B1819511 : Blo 806344 1819511 := bstep (se 1 (by rfl) ⟨1364633, by rfl⟩ : syracuseStep 1819511 = 2729267) B2729267
theorem B2048915 : Blo 806344 2048915 := bstep (se 1 (by rfl) ⟨1536686, by rfl⟩ : syracuseStep 2048915 = 3073373) B3073373
theorem B9815051 : Blo 806344 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B4604957 : Blo 806344 4604957 := bstep (se 3 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 4604957 = 1726859) B1726859
theorem B1819691 : Blo 806344 1819691 := bstep (se 1 (by rfl) ⟨1364768, by rfl⟩ : syracuseStep 1819691 = 2729537) B2729537
theorem B1360955 : Blo 806344 1360955 := bstep (se 1 (by rfl) ⟨1020716, by rfl⟩ : syracuseStep 1360955 = 2041433) B2041433
theorem B2049209 : Blo 806344 2049209 := bstep (se 2 (by rfl) ⟨768453, by rfl⟩ : syracuseStep 2049209 = 1536907) B1536907
theorem B1820051 : Blo 806344 1820051 := bstep (se 1 (by rfl) ⟨1365038, by rfl⟩ : syracuseStep 1820051 = 2730077) B2730077
theorem B1361353 : Blo 806344 1361353 := bstep (se 2 (by rfl) ⟨510507, by rfl⟩ : syracuseStep 1361353 = 1021015) B1021015
theorem B1820105 : Blo 806344 1820105 := bstep (se 2 (by rfl) ⟨682539, by rfl⟩ : syracuseStep 1820105 = 1365079) B1365079
theorem B6899165 : Blo 806344 6899165 := bstep (se 3 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 6899165 = 2587187) B2587187
theorem B31540913 : Blo 806344 31540913 := bstep (se 2 (by rfl) ⟨11827842, by rfl⟩ : syracuseStep 31540913 = 23655685) B23655685
theorem B9946955 : Blo 806344 9946955 := bstep (se 1 (by rfl) ⟨7460216, by rfl⟩ : syracuseStep 9946955 = 14920433) B14920433
theorem B2180951 : Blo 806344 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B2049907 : Blo 806344 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B9848729 : Blo 806344 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B6145955 : Blo 806344 6145955 := bstep (se 1 (by rfl) ⟨4609466, by rfl⟩ : syracuseStep 6145955 = 9218933) B9218933
theorem B3065809 : Blo 806344 3065809 := bstep (se 2 (by rfl) ⟨1149678, by rfl⟩ : syracuseStep 3065809 = 2299357) B2299357
theorem B2050049 : Blo 806344 2050049 := bstep (se 2 (by rfl) ⟨768768, by rfl⟩ : syracuseStep 2050049 = 1537537) B1537537
theorem B1362055 : Blo 806344 1362055 := bstep (se 1 (by rfl) ⟨1021541, by rfl⟩ : syracuseStep 1362055 = 2043083) B2043083
theorem B1820807 : Blo 806344 1820807 := bstep (se 1 (by rfl) ⟨1365605, by rfl⟩ : syracuseStep 1820807 = 2731211) B2731211
theorem B15747317 : Blo 806344 15747317 := bstep (se 5 (by rfl) ⟨738155, by rfl⟩ : syracuseStep 15747317 = 1476311) B1476311
theorem B3066113 : Blo 806344 3066113 := bstep (se 2 (by rfl) ⟨1149792, by rfl⟩ : syracuseStep 3066113 = 2299585) B2299585
theorem B1820987 : Blo 806344 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B1821113 : Blo 806344 1821113 := bstep (se 2 (by rfl) ⟨682917, by rfl⟩ : syracuseStep 1821113 = 1365835) B1365835
theorem B2050505 : Blo 806344 2050505 := bstep (se 2 (by rfl) ⟨768939, by rfl⟩ : syracuseStep 2050505 = 1537879) B1537879
theorem B6900227 : Blo 806344 6900227 := bstep (se 1 (by rfl) ⟨5175170, by rfl⟩ : syracuseStep 6900227 = 10350341) B10350341
theorem B4082237 : Blo 806344 4082237 := bstep (se 3 (by rfl) ⟨765419, by rfl⟩ : syracuseStep 4082237 = 1530839) B1530839
theorem B3066569 : Blo 806344 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B1723151 : Blo 806344 1723151 := bstep (se 1 (by rfl) ⟨1292363, by rfl⟩ : syracuseStep 1723151 = 2584727) B2584727
theorem B1362703 : Blo 806344 1362703 := bstep (se 1 (by rfl) ⟨1022027, by rfl⟩ : syracuseStep 1362703 = 2044055) B2044055
theorem B1821455 : Blo 806344 1821455 := bstep (se 1 (by rfl) ⟨1366091, by rfl⟩ : syracuseStep 1821455 = 2732183) B2732183
theorem B1723169 : Blo 806344 1723169 := bstep (se 2 (by rfl) ⟨646188, by rfl⟩ : syracuseStep 1723169 = 1292377) B1292377
theorem B1821473 : Blo 806344 1821473 := bstep (se 2 (by rfl) ⟨683052, by rfl⟩ : syracuseStep 1821473 = 1366105) B1366105
theorem B2050859 : Blo 806344 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B3459955 : Blo 806344 3459955 := bstep (se 1 (by rfl) ⟨2594966, by rfl⟩ : syracuseStep 3459955 = 5189933) B5189933
theorem B1723511 : Blo 806344 1723511 := bstep (se 1 (by rfl) ⟨1292633, by rfl⟩ : syracuseStep 1723511 = 2585267) B2585267
theorem B1821815 : Blo 806344 1821815 := bstep (se 1 (by rfl) ⟨1366361, by rfl⟩ : syracuseStep 1821815 = 2732723) B2732723
theorem B1363243 : Blo 806344 1363243 := bstep (se 1 (by rfl) ⟨1022432, by rfl⟩ : syracuseStep 1363243 = 2044865) B2044865
theorem B1821995 : Blo 806344 1821995 := bstep (se 1 (by rfl) ⟨1366496, by rfl⟩ : syracuseStep 1821995 = 2732993) B2732993
theorem B2182585 : Blo 806344 2182585 := bstep (se 2 (by rfl) ⟨818469, by rfl⟩ : syracuseStep 2182585 = 1636939) B1636939
theorem B1363385 : Blo 806344 1363385 := bstep (se 2 (by rfl) ⟨511269, by rfl⟩ : syracuseStep 1363385 = 1022539) B1022539
theorem B4607441 : Blo 806344 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B806407 : Blo 806344 806407 := bstep (se 1 (by rfl) ⟨604805, by rfl⟩ : syracuseStep 806407 = 1209611) B1209611
theorem B806415 : Blo 806344 806415 := bstep (se 1 (by rfl) ⟨604811, by rfl⟩ : syracuseStep 806415 = 1209623) B1209623
theorem B806459 : Blo 806344 806459 := bstep (se 1 (by rfl) ⟨604844, by rfl⟩ : syracuseStep 806459 = 1209689) B1209689
theorem B2805367 : Blo 806344 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B806535 : Blo 806344 806535 := bstep (se 1 (by rfl) ⟨604901, by rfl⟩ : syracuseStep 806535 = 1209803) B1209803
theorem B806543 : Blo 806344 806543 := bstep (se 1 (by rfl) ⟨604907, by rfl⟩ : syracuseStep 806543 = 1209815) B1209815
theorem B1822355 : Blo 806344 1822355 := bstep (se 1 (by rfl) ⟨1366766, by rfl⟩ : syracuseStep 1822355 = 2733533) B2733533
theorem B806587 : Blo 806344 806587 := bstep (se 1 (by rfl) ⟨604940, by rfl⟩ : syracuseStep 806587 = 1209881) B1209881
theorem B1822409 : Blo 806344 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B806663 : Blo 806344 806663 := bstep (se 1 (by rfl) ⟨604997, by rfl⟩ : syracuseStep 806663 = 1209995) B1209995
theorem B806671 : Blo 806344 806671 := bstep (se 1 (by rfl) ⟨605003, by rfl⟩ : syracuseStep 806671 = 1210007) B1210007
theorem B806715 : Blo 806344 806715 := bstep (se 1 (by rfl) ⟨605036, by rfl⟩ : syracuseStep 806715 = 1210073) B1210073
theorem B806791 : Blo 806344 806791 := bstep (se 1 (by rfl) ⟨605093, by rfl⟩ : syracuseStep 806791 = 1210187) B1210187
theorem B806799 : Blo 806344 806799 := bstep (se 1 (by rfl) ⟨605099, by rfl⟩ : syracuseStep 806799 = 1210199) B1210199
theorem B806843 : Blo 806344 806843 := bstep (se 1 (by rfl) ⟨605132, by rfl⟩ : syracuseStep 806843 = 1210265) B1210265
theorem B806919 : Blo 806344 806919 := bstep (se 1 (by rfl) ⟨605189, by rfl⟩ : syracuseStep 806919 = 1210379) B1210379
theorem B806927 : Blo 806344 806927 := bstep (se 1 (by rfl) ⟨605195, by rfl⟩ : syracuseStep 806927 = 1210391) B1210391
theorem B806971 : Blo 806344 806971 := bstep (se 1 (by rfl) ⟨605228, by rfl⟩ : syracuseStep 806971 = 1210457) B1210457
theorem B2183287 : Blo 806344 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B1364087 : Blo 806344 1364087 := bstep (se 1 (by rfl) ⟨1023065, by rfl⟩ : syracuseStep 1364087 = 2046131) B2046131
theorem B807047 : Blo 806344 807047 := bstep (se 1 (by rfl) ⟨605285, by rfl⟩ : syracuseStep 807047 = 1210571) B1210571
theorem B807055 : Blo 806344 807055 := bstep (se 1 (by rfl) ⟨605291, by rfl⟩ : syracuseStep 807055 = 1210583) B1210583
theorem B807099 : Blo 806344 807099 := bstep (se 1 (by rfl) ⟨605324, by rfl⟩ : syracuseStep 807099 = 1210649) B1210649
theorem B807175 : Blo 806344 807175 := bstep (se 1 (by rfl) ⟨605381, by rfl⟩ : syracuseStep 807175 = 1210763) B1210763
theorem B807183 : Blo 806344 807183 := bstep (se 1 (by rfl) ⟨605387, by rfl⟩ : syracuseStep 807183 = 1210775) B1210775
theorem B6148385 : Blo 806344 6148385 := bstep (se 2 (by rfl) ⟨2305644, by rfl⟩ : syracuseStep 6148385 = 4611289) B4611289
theorem B4084019 : Blo 806344 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B807227 : Blo 806344 807227 := bstep (se 1 (by rfl) ⟨605420, by rfl⟩ : syracuseStep 807227 = 1210841) B1210841
theorem B807303 : Blo 806344 807303 := bstep (se 1 (by rfl) ⟨605477, by rfl⟩ : syracuseStep 807303 = 1210955) B1210955
theorem B1823111 : Blo 806344 1823111 := bstep (se 1 (by rfl) ⟨1367333, by rfl⟩ : syracuseStep 1823111 = 2734667) B2734667
theorem B807311 : Blo 806344 807311 := bstep (se 1 (by rfl) ⟨605483, by rfl⟩ : syracuseStep 807311 = 1210967) B1210967
theorem B807355 : Blo 806344 807355 := bstep (se 1 (by rfl) ⟨605516, by rfl⟩ : syracuseStep 807355 = 1211033) B1211033
theorem B971195 : Blo 806344 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B807431 : Blo 806344 807431 := bstep (se 1 (by rfl) ⟨605573, by rfl⟩ : syracuseStep 807431 = 1211147) B1211147
theorem B2249227 : Blo 806344 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B807439 : Blo 806344 807439 := bstep (se 1 (by rfl) ⟨605579, by rfl⟩ : syracuseStep 807439 = 1211159) B1211159
theorem B873019 : Blo 806344 873019 := bstep (se 1 (by rfl) ⟨654764, by rfl⟩ : syracuseStep 873019 = 1309529) B1309529
theorem B807483 : Blo 806344 807483 := bstep (se 1 (by rfl) ⟨605612, by rfl⟩ : syracuseStep 807483 = 1211225) B1211225
theorem B1364539 : Blo 806344 1364539 := bstep (se 1 (by rfl) ⟨1023404, by rfl⟩ : syracuseStep 1364539 = 2046809) B2046809
theorem B4084343 : Blo 806344 4084343 := bstep (se 1 (by rfl) ⟨3063257, by rfl⟩ : syracuseStep 4084343 = 6126515) B6126515
theorem B807559 : Blo 806344 807559 := bstep (se 1 (by rfl) ⟨605669, by rfl⟩ : syracuseStep 807559 = 1211339) B1211339
theorem B807567 : Blo 806344 807567 := bstep (se 1 (by rfl) ⟨605675, by rfl⟩ : syracuseStep 807567 = 1211351) B1211351
theorem B807611 : Blo 806344 807611 := bstep (se 1 (by rfl) ⟨605708, by rfl⟩ : syracuseStep 807611 = 1211417) B1211417
theorem B1364681 : Blo 806344 1364681 := bstep (se 2 (by rfl) ⟨511755, by rfl⟩ : syracuseStep 1364681 = 1023511) B1023511
theorem B807687 : Blo 806344 807687 := bstep (se 1 (by rfl) ⟨605765, by rfl⟩ : syracuseStep 807687 = 1211531) B1211531
theorem B807695 : Blo 806344 807695 := bstep (se 1 (by rfl) ⟨605771, by rfl⟩ : syracuseStep 807695 = 1211543) B1211543
theorem B807739 : Blo 806344 807739 := bstep (se 1 (by rfl) ⟨605804, by rfl⟩ : syracuseStep 807739 = 1211609) B1211609
theorem B2184023 : Blo 806344 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B807815 : Blo 806344 807815 := bstep (se 1 (by rfl) ⟨605861, by rfl⟩ : syracuseStep 807815 = 1211723) B1211723
theorem B4674439 : Blo 806344 4674439 := bstep (se 1 (by rfl) ⟨3505829, by rfl⟩ : syracuseStep 4674439 = 7011659) B7011659
theorem B807823 : Blo 806344 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B4379545 : Blo 806344 4379545 := bstep (se 2 (by rfl) ⟨1642329, by rfl⟩ : syracuseStep 4379545 = 3284659) B3284659
theorem B807867 : Blo 806344 807867 := bstep (se 1 (by rfl) ⟨605900, by rfl⟩ : syracuseStep 807867 = 1211801) B1211801
theorem B807943 : Blo 806344 807943 := bstep (se 1 (by rfl) ⟨605957, by rfl⟩ : syracuseStep 807943 = 1211915) B1211915
theorem B807951 : Blo 806344 807951 := bstep (se 1 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 807951 = 1211927) B1211927
theorem B807995 : Blo 806344 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B808071 : Blo 806344 808071 := bstep (se 1 (by rfl) ⟨606053, by rfl⟩ : syracuseStep 808071 = 1212107) B1212107
theorem B808079 : Blo 806344 808079 := bstep (se 1 (by rfl) ⟨606059, by rfl⟩ : syracuseStep 808079 = 1212119) B1212119
theorem B808123 : Blo 806344 808123 := bstep (se 1 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 808123 = 1212185) B1212185
theorem B6149357 : Blo 806344 6149357 := bstep (se 3 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 6149357 = 2306009) B2306009
theorem B808199 : Blo 806344 808199 := bstep (se 1 (by rfl) ⟨606149, by rfl⟩ : syracuseStep 808199 = 1212299) B1212299
theorem B808207 : Blo 806344 808207 := bstep (se 1 (by rfl) ⟨606155, by rfl⟩ : syracuseStep 808207 = 1212311) B1212311
theorem B4609331 : Blo 806344 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B808251 : Blo 806344 808251 := bstep (se 1 (by rfl) ⟨606188, by rfl⟩ : syracuseStep 808251 = 1212377) B1212377
theorem B11064707 : Blo 806344 11064707 := bstep (se 1 (by rfl) ⟨8298530, by rfl⟩ : syracuseStep 11064707 = 16597061) B16597061
theorem B2184583 : Blo 806344 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B808327 : Blo 806344 808327 := bstep (se 1 (by rfl) ⟨606245, by rfl⟩ : syracuseStep 808327 = 1212491) B1212491
theorem B1365383 : Blo 806344 1365383 := bstep (se 1 (by rfl) ⟨1024037, by rfl⟩ : syracuseStep 1365383 = 2048075) B2048075
theorem B808335 : Blo 806344 808335 := bstep (se 1 (by rfl) ⟨606251, by rfl⟩ : syracuseStep 808335 = 1212503) B1212503
theorem B34952633 : Blo 806344 34952633 := bstep (se 2 (by rfl) ⟨13107237, by rfl⟩ : syracuseStep 34952633 = 26214475) B26214475
theorem B808379 : Blo 806344 808379 := bstep (se 1 (by rfl) ⟨606284, by rfl⟩ : syracuseStep 808379 = 1212569) B1212569
theorem B808455 : Blo 806344 808455 := bstep (se 1 (by rfl) ⟨606341, by rfl⟩ : syracuseStep 808455 = 1212683) B1212683
theorem B808463 : Blo 806344 808463 := bstep (se 1 (by rfl) ⟨606347, by rfl⟩ : syracuseStep 808463 = 1212695) B1212695
theorem B808507 : Blo 806344 808507 := bstep (se 1 (by rfl) ⟨606380, by rfl⟩ : syracuseStep 808507 = 1212761) B1212761
theorem B4085315 : Blo 806344 4085315 := bstep (se 1 (by rfl) ⟨3063986, by rfl⟩ : syracuseStep 4085315 = 6127973) B6127973
theorem B808583 : Blo 806344 808583 := bstep (se 1 (by rfl) ⟨606437, by rfl⟩ : syracuseStep 808583 = 1212875) B1212875
theorem B808591 : Blo 806344 808591 := bstep (se 1 (by rfl) ⟨606443, by rfl⟩ : syracuseStep 808591 = 1212887) B1212887
theorem B808635 : Blo 806344 808635 := bstep (se 1 (by rfl) ⟨606476, by rfl⟩ : syracuseStep 808635 = 1212953) B1212953
theorem B3069697 : Blo 806344 3069697 := bstep (se 2 (by rfl) ⟨1151136, by rfl⟩ : syracuseStep 3069697 = 2302273) B2302273
theorem B808711 : Blo 806344 808711 := bstep (se 1 (by rfl) ⟨606533, by rfl⟩ : syracuseStep 808711 = 1213067) B1213067
theorem B808719 : Blo 806344 808719 := bstep (se 1 (by rfl) ⟨606539, by rfl⟩ : syracuseStep 808719 = 1213079) B1213079
theorem B808763 : Blo 806344 808763 := bstep (se 1 (by rfl) ⟨606572, by rfl⟩ : syracuseStep 808763 = 1213145) B1213145
theorem B4085639 : Blo 806344 4085639 := bstep (se 1 (by rfl) ⟨3064229, by rfl⟩ : syracuseStep 4085639 = 6128459) B6128459
theorem B808839 : Blo 806344 808839 := bstep (se 1 (by rfl) ⟨606629, by rfl⟩ : syracuseStep 808839 = 1213259) B1213259
theorem B808847 : Blo 806344 808847 := bstep (se 1 (by rfl) ⟨606635, by rfl⟩ : syracuseStep 808847 = 1213271) B1213271
theorem B907195 : Blo 806344 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B808891 : Blo 806344 808891 := bstep (se 1 (by rfl) ⟨606668, by rfl⟩ : syracuseStep 808891 = 1213337) B1213337
theorem B808967 : Blo 806344 808967 := bstep (se 1 (by rfl) ⟨606725, by rfl⟩ : syracuseStep 808967 = 1213451) B1213451
theorem B808975 : Blo 806344 808975 := bstep (se 1 (by rfl) ⟨606731, by rfl⟩ : syracuseStep 808975 = 1213463) B1213463
theorem B1366031 : Blo 806344 1366031 := bstep (se 1 (by rfl) ⟨1024523, by rfl⟩ : syracuseStep 1366031 = 2049047) B2049047
theorem B809019 : Blo 806344 809019 := bstep (se 1 (by rfl) ⟨606764, by rfl⟩ : syracuseStep 809019 = 1213529) B1213529
theorem B809095 : Blo 806344 809095 := bstep (se 1 (by rfl) ⟨606821, by rfl⟩ : syracuseStep 809095 = 1213643) B1213643
theorem B809103 : Blo 806344 809103 := bstep (se 1 (by rfl) ⟨606827, by rfl⟩ : syracuseStep 809103 = 1213655) B1213655
theorem B809147 : Blo 806344 809147 := bstep (se 1 (by rfl) ⟨606860, by rfl⟩ : syracuseStep 809147 = 1213721) B1213721
theorem B809223 : Blo 806344 809223 := bstep (se 1 (by rfl) ⟨606917, by rfl⟩ : syracuseStep 809223 = 1213835) B1213835
theorem B809231 : Blo 806344 809231 := bstep (se 1 (by rfl) ⟨606923, by rfl⟩ : syracuseStep 809231 = 1213847) B1213847
theorem B809275 : Blo 806344 809275 := bstep (se 1 (by rfl) ⟨606956, by rfl⟩ : syracuseStep 809275 = 1213913) B1213913
theorem B809351 : Blo 806344 809351 := bstep (se 1 (by rfl) ⟨607013, by rfl⟩ : syracuseStep 809351 = 1214027) B1214027
theorem B907663 : Blo 806344 907663 := bstep (se 1 (by rfl) ⟨680747, by rfl⟩ : syracuseStep 907663 = 1361495) B1361495
theorem B809359 : Blo 806344 809359 := bstep (se 1 (by rfl) ⟨607019, by rfl⟩ : syracuseStep 809359 = 1214039) B1214039
theorem B809403 : Blo 806344 809403 := bstep (se 1 (by rfl) ⟨607052, by rfl⟩ : syracuseStep 809403 = 1214105) B1214105
theorem B1497545 : Blo 806344 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B17488345 : Blo 806344 17488345 := bstep (se 2 (by rfl) ⟨6558129, by rfl⟩ : syracuseStep 17488345 = 13116259) B13116259
theorem B809479 : Blo 806344 809479 := bstep (se 1 (by rfl) ⟨607109, by rfl⟩ : syracuseStep 809479 = 1214219) B1214219
theorem B809487 : Blo 806344 809487 := bstep (se 1 (by rfl) ⟨607115, by rfl⟩ : syracuseStep 809487 = 1214231) B1214231
theorem B1366571 : Blo 806344 1366571 := bstep (se 1 (by rfl) ⟨1024928, by rfl⟩ : syracuseStep 1366571 = 2049857) B2049857
theorem B809531 : Blo 806344 809531 := bstep (se 1 (by rfl) ⟨607148, by rfl⟩ : syracuseStep 809531 = 1214297) B1214297
theorem B8968805 : Blo 806344 8968805 := bstep (se 4 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 8968805 = 1681651) B1681651
theorem B809607 : Blo 806344 809607 := bstep (se 1 (by rfl) ⟨607205, by rfl⟩ : syracuseStep 809607 = 1214411) B1214411
theorem B809615 : Blo 806344 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B809659 : Blo 806344 809659 := bstep (se 1 (by rfl) ⟨607244, by rfl⟩ : syracuseStep 809659 = 1214489) B1214489
theorem B4610789 : Blo 806344 4610789 := bstep (se 4 (by rfl) ⟨432261, by rfl⟩ : syracuseStep 4610789 = 864523) B864523
theorem B809735 : Blo 806344 809735 := bstep (se 1 (by rfl) ⟨607301, by rfl⟩ : syracuseStep 809735 = 1214603) B1214603
theorem B5823247 : Blo 806344 5823247 := bstep (se 1 (by rfl) ⟨4367435, by rfl⟩ : syracuseStep 5823247 = 8734871) B8734871
theorem B809743 : Blo 806344 809743 := bstep (se 1 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 809743 = 1214615) B1214615
theorem B809787 : Blo 806344 809787 := bstep (se 1 (by rfl) ⟨607340, by rfl⟩ : syracuseStep 809787 = 1214681) B1214681
theorem B908167 : Blo 806344 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B809863 : Blo 806344 809863 := bstep (se 1 (by rfl) ⟨607397, by rfl⟩ : syracuseStep 809863 = 1214795) B1214795
theorem B809871 : Blo 806344 809871 := bstep (se 1 (by rfl) ⟨607403, by rfl⟩ : syracuseStep 809871 = 1214807) B1214807
theorem B1530809 : Blo 806344 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B809915 : Blo 806344 809915 := bstep (se 1 (by rfl) ⟨607436, by rfl⟩ : syracuseStep 809915 = 1214873) B1214873
theorem B1366969 : Blo 806344 1366969 := bstep (se 2 (by rfl) ⟨512613, by rfl⟩ : syracuseStep 1366969 = 1025227) B1025227
theorem B809991 : Blo 806344 809991 := bstep (se 1 (by rfl) ⟨607493, by rfl⟩ : syracuseStep 809991 = 1214987) B1214987
theorem B7363595 : Blo 806344 7363595 := bstep (se 1 (by rfl) ⟨5522696, by rfl⟩ : syracuseStep 7363595 = 11045393) B11045393
theorem B809999 : Blo 806344 809999 := bstep (se 1 (by rfl) ⟨607499, by rfl⟩ : syracuseStep 809999 = 1214999) B1214999
theorem B908347 : Blo 806344 908347 := bstep (se 1 (by rfl) ⟨681260, by rfl⟩ : syracuseStep 908347 = 1362521) B1362521
theorem B810043 : Blo 806344 810043 := bstep (se 1 (by rfl) ⟨607532, by rfl⟩ : syracuseStep 810043 = 1215065) B1215065
theorem B6151301 : Blo 806344 6151301 := bstep (se 4 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 6151301 = 1153369) B1153369
theorem B810119 : Blo 806344 810119 := bstep (se 1 (by rfl) ⟨607589, by rfl⟩ : syracuseStep 810119 = 1215179) B1215179
theorem B810127 : Blo 806344 810127 := bstep (se 1 (by rfl) ⟨607595, by rfl⟩ : syracuseStep 810127 = 1215191) B1215191
theorem B810171 : Blo 806344 810171 := bstep (se 1 (by rfl) ⟨607628, by rfl⟩ : syracuseStep 810171 = 1215257) B1215257
theorem B810247 : Blo 806344 810247 := bstep (se 1 (by rfl) ⟨607685, by rfl⟩ : syracuseStep 810247 = 1215371) B1215371
theorem B810255 : Blo 806344 810255 := bstep (se 1 (by rfl) ⟨607691, by rfl⟩ : syracuseStep 810255 = 1215383) B1215383
theorem B810299 : Blo 806344 810299 := bstep (se 1 (by rfl) ⟨607724, by rfl⟩ : syracuseStep 810299 = 1215449) B1215449
theorem B908815 : Blo 806344 908815 := bstep (se 1 (by rfl) ⟨681611, by rfl⟩ : syracuseStep 908815 = 1363223) B1363223
theorem B5529131 : Blo 806344 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B1498771 : Blo 806344 1498771 := bstep (se 1 (by rfl) ⟨1124078, by rfl⟩ : syracuseStep 1498771 = 2248157) B2248157
theorem B909319 : Blo 806344 909319 := bstep (se 1 (by rfl) ⟨681989, by rfl⟩ : syracuseStep 909319 = 1363979) B1363979
theorem B1531963 : Blo 806344 1531963 := bstep (se 1 (by rfl) ⟨1148972, by rfl⟩ : syracuseStep 1531963 = 2297945) B2297945
theorem B909499 : Blo 806344 909499 := bstep (se 1 (by rfl) ⟨682124, by rfl⟩ : syracuseStep 909499 = 1364249) B1364249
theorem B6644227 : Blo 806344 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1532449 : Blo 806344 1532449 := bstep (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) B1149337
theorem B3072599 : Blo 806344 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B909967 : Blo 806344 909967 := bstep (se 1 (by rfl) ⟨682475, by rfl⟩ : syracuseStep 909967 = 1364951) B1364951
theorem B3073085 : Blo 806344 3073085 := bstep (se 3 (by rfl) ⟨576203, by rfl⟩ : syracuseStep 3073085 = 1152407) B1152407
theorem B910471 : Blo 806344 910471 := bstep (se 1 (by rfl) ⟨682853, by rfl⟩ : syracuseStep 910471 = 1365707) B1365707
theorem B910651 : Blo 806344 910651 := bstep (se 1 (by rfl) ⟨682988, by rfl⟩ : syracuseStep 910651 = 1365977) B1365977
theorem B4089203 : Blo 806344 4089203 := bstep (se 1 (by rfl) ⟨3066902, by rfl⟩ : syracuseStep 4089203 = 6133805) B6133805
theorem B5826077 : Blo 806344 5826077 := bstep (se 3 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 5826077 = 2184779) B2184779
theorem B5826305 : Blo 806344 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B5596943 : Blo 806344 5596943 := bstep (se 1 (by rfl) ⟨4197707, by rfl⟩ : syracuseStep 5596943 = 8395415) B8395415
theorem B911119 : Blo 806344 911119 := bstep (se 1 (by rfl) ⟨683339, by rfl⟩ : syracuseStep 911119 = 1366679) B1366679
theorem B10348337 : Blo 806344 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B1533755 : Blo 806344 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B4089689 : Blo 806344 4089689 := bstep (se 2 (by rfl) ⟨1533633, by rfl⟩ : syracuseStep 4089689 = 3067267) B3067267
theorem B4614023 : Blo 806344 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B5171147 : Blo 806344 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B4614205 : Blo 806344 4614205 := bstep (se 3 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 4614205 = 1730327) B1730327
theorem B911623 : Blo 806344 911623 := bstep (se 1 (by rfl) ⟨683717, by rfl⟩ : syracuseStep 911623 = 1367435) B1367435
theorem B1534241 : Blo 806344 1534241 := bstep (se 2 (by rfl) ⟨575340, by rfl⟩ : syracuseStep 1534241 = 1150681) B1150681
theorem B2910617 : Blo 806344 2910617 := bstep (se 2 (by rfl) ⟨1091481, by rfl⟩ : syracuseStep 2910617 = 2182963) B2182963
theorem B1534393 : Blo 806344 1534393 := bstep (se 2 (by rfl) ⟨575397, by rfl⟩ : syracuseStep 1534393 = 1150795) B1150795
theorem B3074831 : Blo 806344 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B6548273 : Blo 806344 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B5893181 : Blo 806344 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B3108439 : Blo 806344 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B7761527 : Blo 806344 7761527 := bstep (se 1 (by rfl) ⟨5821145, by rfl⟩ : syracuseStep 7761527 = 11642291) B11642291
theorem B4484845 : Blo 806344 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B4091795 : Blo 806344 4091795 := bstep (se 1 (by rfl) ⟨3068846, by rfl⟩ : syracuseStep 4091795 = 6137693) B6137693
theorem B5173145 : Blo 806344 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B1536185 : Blo 806344 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B3076487 : Blo 806344 3076487 := bstep (se 1 (by rfl) ⟨2307365, by rfl⟩ : syracuseStep 3076487 = 4614731) B4614731
theorem B2519687 : Blo 806344 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B1209545 : Blo 806344 1209545 := bstep (se 2 (by rfl) ⟨453579, by rfl⟩ : syracuseStep 1209545 = 907159) B907159
theorem B1209659 : Blo 806344 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B1209719 : Blo 806344 1209719 := bstep (se 1 (by rfl) ⟨907289, by rfl⟩ : syracuseStep 1209719 = 1814579) B1814579
theorem B1209743 : Blo 806344 1209743 := bstep (se 1 (by rfl) ⟨907307, by rfl⟩ : syracuseStep 1209743 = 1814615) B1814615
theorem B3503513 : Blo 806344 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B1209785 : Blo 806344 1209785 := bstep (se 2 (by rfl) ⟨453669, by rfl⟩ : syracuseStep 1209785 = 907339) B907339
theorem B1209863 : Blo 806344 1209863 := bstep (se 1 (by rfl) ⟨907397, by rfl⟩ : syracuseStep 1209863 = 1814795) B1814795
theorem B2913803 : Blo 806344 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B7763485 : Blo 806344 7763485 := bstep (se 3 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 7763485 = 2911307) B2911307
theorem B1209899 : Blo 806344 1209899 := bstep (se 1 (by rfl) ⟨907424, by rfl⟩ : syracuseStep 1209899 = 1814849) B1814849
theorem B1209929 : Blo 806344 1209929 := bstep (se 2 (by rfl) ⟨453723, by rfl⟩ : syracuseStep 1209929 = 907447) B907447
theorem B1210043 : Blo 806344 1210043 := bstep (se 1 (by rfl) ⟨907532, by rfl⟩ : syracuseStep 1210043 = 1815065) B1815065
theorem B1210103 : Blo 806344 1210103 := bstep (se 1 (by rfl) ⟨907577, by rfl⟩ : syracuseStep 1210103 = 1815155) B1815155
theorem B1210127 : Blo 806344 1210127 := bstep (se 1 (by rfl) ⟨907595, by rfl⟩ : syracuseStep 1210127 = 1815191) B1815191
theorem B1210169 : Blo 806344 1210169 := bstep (se 2 (by rfl) ⟨453813, by rfl⟩ : syracuseStep 1210169 = 907627) B907627
theorem B1210247 : Blo 806344 1210247 := bstep (se 1 (by rfl) ⟨907685, by rfl⟩ : syracuseStep 1210247 = 1815371) B1815371
theorem B1210283 : Blo 806344 1210283 := bstep (se 1 (by rfl) ⟨907712, by rfl⟩ : syracuseStep 1210283 = 1815425) B1815425
theorem B1210313 : Blo 806344 1210313 := bstep (se 2 (by rfl) ⟨453867, by rfl⟩ : syracuseStep 1210313 = 907735) B907735
theorem B1210427 : Blo 806344 1210427 := bstep (se 1 (by rfl) ⟨907820, by rfl⟩ : syracuseStep 1210427 = 1815641) B1815641
theorem B1210487 : Blo 806344 1210487 := bstep (se 1 (by rfl) ⟨907865, by rfl⟩ : syracuseStep 1210487 = 1815731) B1815731
theorem B1538183 : Blo 806344 1538183 := bstep (se 1 (by rfl) ⟨1153637, by rfl⟩ : syracuseStep 1538183 = 2307275) B2307275
theorem B1210511 : Blo 806344 1210511 := bstep (se 1 (by rfl) ⟨907883, by rfl⟩ : syracuseStep 1210511 = 1815767) B1815767
theorem B1210553 : Blo 806344 1210553 := bstep (se 2 (by rfl) ⟨453957, by rfl⟩ : syracuseStep 1210553 = 907915) B907915
theorem B1210631 : Blo 806344 1210631 := bstep (se 1 (by rfl) ⟨907973, by rfl⟩ : syracuseStep 1210631 = 1815947) B1815947
theorem B13105421 : Blo 806344 13105421 := bstep (se 3 (by rfl) ⟨2457266, by rfl⟩ : syracuseStep 13105421 = 4914533) B4914533
theorem B1210667 : Blo 806344 1210667 := bstep (se 1 (by rfl) ⟨908000, by rfl⟩ : syracuseStep 1210667 = 1816001) B1816001
theorem B1210697 : Blo 806344 1210697 := bstep (se 2 (by rfl) ⟨454011, by rfl⟩ : syracuseStep 1210697 = 908023) B908023
theorem B1210811 : Blo 806344 1210811 := bstep (se 1 (by rfl) ⟨908108, by rfl⟩ : syracuseStep 1210811 = 1816217) B1816217
theorem B1210871 : Blo 806344 1210871 := bstep (se 1 (by rfl) ⟨908153, by rfl⟩ : syracuseStep 1210871 = 1816307) B1816307
theorem B1210895 : Blo 806344 1210895 := bstep (se 1 (by rfl) ⟨908171, by rfl⟩ : syracuseStep 1210895 = 1816343) B1816343
theorem B1210937 : Blo 806344 1210937 := bstep (se 2 (by rfl) ⟨454101, by rfl⟩ : syracuseStep 1210937 = 908203) B908203
theorem B1211015 : Blo 806344 1211015 := bstep (se 1 (by rfl) ⟨908261, by rfl⟩ : syracuseStep 1211015 = 1816523) B1816523
theorem B1211051 : Blo 806344 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B1211081 : Blo 806344 1211081 := bstep (se 2 (by rfl) ⟨454155, by rfl⟩ : syracuseStep 1211081 = 908311) B908311
theorem B1211195 : Blo 806344 1211195 := bstep (se 1 (by rfl) ⟨908396, by rfl⟩ : syracuseStep 1211195 = 1816793) B1816793
theorem B1211255 : Blo 806344 1211255 := bstep (se 1 (by rfl) ⟨908441, by rfl⟩ : syracuseStep 1211255 = 1816883) B1816883
theorem B1211279 : Blo 806344 1211279 := bstep (se 1 (by rfl) ⟨908459, by rfl⟩ : syracuseStep 1211279 = 1816919) B1816919
theorem B4094873 : Blo 806344 4094873 := bstep (se 2 (by rfl) ⟨1535577, by rfl⟩ : syracuseStep 4094873 = 3071155) B3071155
theorem B1211321 : Blo 806344 1211321 := bstep (se 2 (by rfl) ⟨454245, by rfl⟩ : syracuseStep 1211321 = 908491) B908491
theorem B6912971 : Blo 806344 6912971 := bstep (se 1 (by rfl) ⟨5184728, by rfl⟩ : syracuseStep 6912971 = 10369457) B10369457
theorem B1211399 : Blo 806344 1211399 := bstep (se 1 (by rfl) ⟨908549, by rfl⟩ : syracuseStep 1211399 = 1817099) B1817099
theorem B1211435 : Blo 806344 1211435 := bstep (se 1 (by rfl) ⟨908576, by rfl⟩ : syracuseStep 1211435 = 1817153) B1817153
theorem B1211465 : Blo 806344 1211465 := bstep (se 2 (by rfl) ⟨454299, by rfl⟩ : syracuseStep 1211465 = 908599) B908599
theorem B11238533 : Blo 806344 11238533 := bstep (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) B2107225
theorem B1211579 : Blo 806344 1211579 := bstep (se 1 (by rfl) ⟨908684, by rfl⟩ : syracuseStep 1211579 = 1817369) B1817369
theorem B1211639 : Blo 806344 1211639 := bstep (se 1 (by rfl) ⟨908729, by rfl⟩ : syracuseStep 1211639 = 1817459) B1817459
theorem B1211663 : Blo 806344 1211663 := bstep (se 1 (by rfl) ⟨908747, by rfl⟩ : syracuseStep 1211663 = 1817495) B1817495
theorem B1211705 : Blo 806344 1211705 := bstep (se 2 (by rfl) ⟨454389, by rfl⟩ : syracuseStep 1211705 = 908779) B908779
theorem B1211783 : Blo 806344 1211783 := bstep (se 1 (by rfl) ⟨908837, by rfl⟩ : syracuseStep 1211783 = 1817675) B1817675
theorem B1211819 : Blo 806344 1211819 := bstep (se 1 (by rfl) ⟨908864, by rfl⟩ : syracuseStep 1211819 = 1817729) B1817729
theorem B1211849 : Blo 806344 1211849 := bstep (se 2 (by rfl) ⟨454443, by rfl⟩ : syracuseStep 1211849 = 908887) B908887
theorem B5176835 : Blo 806344 5176835 := bstep (se 1 (by rfl) ⟨3882626, by rfl⟩ : syracuseStep 5176835 = 7765253) B7765253
theorem B1211963 : Blo 806344 1211963 := bstep (se 1 (by rfl) ⟨908972, by rfl⟩ : syracuseStep 1211963 = 1817945) B1817945
theorem B1212023 : Blo 806344 1212023 := bstep (se 1 (by rfl) ⟨909017, by rfl⟩ : syracuseStep 1212023 = 1818035) B1818035
theorem B1212047 : Blo 806344 1212047 := bstep (se 1 (by rfl) ⟨909035, by rfl⟩ : syracuseStep 1212047 = 1818071) B1818071
theorem B1212089 : Blo 806344 1212089 := bstep (se 2 (by rfl) ⟨454533, by rfl⟩ : syracuseStep 1212089 = 909067) B909067
theorem B1212167 : Blo 806344 1212167 := bstep (se 1 (by rfl) ⟨909125, by rfl⟩ : syracuseStep 1212167 = 1818251) B1818251
theorem B1212203 : Blo 806344 1212203 := bstep (se 1 (by rfl) ⟨909152, by rfl⟩ : syracuseStep 1212203 = 1818305) B1818305
theorem B1212233 : Blo 806344 1212233 := bstep (se 2 (by rfl) ⟨454587, by rfl⟩ : syracuseStep 1212233 = 909175) B909175
theorem B1212347 : Blo 806344 1212347 := bstep (se 1 (by rfl) ⟨909260, by rfl⟩ : syracuseStep 1212347 = 1818521) B1818521
theorem B1212407 : Blo 806344 1212407 := bstep (se 1 (by rfl) ⟨909305, by rfl⟩ : syracuseStep 1212407 = 1818611) B1818611
theorem B4096007 : Blo 806344 4096007 := bstep (se 1 (by rfl) ⟨3072005, by rfl⟩ : syracuseStep 4096007 = 6144011) B6144011
theorem B1212425 : Blo 806344 1212425 := bstep (se 2 (by rfl) ⟨454659, by rfl⟩ : syracuseStep 1212425 = 909319) B909319
theorem B23625751 : Blo 806344 23625751 := bstep (se 1 (by rfl) ⟨17719313, by rfl⟩ : syracuseStep 23625751 = 35438627) B35438627
theorem B1212455 : Blo 806344 1212455 := bstep (se 1 (by rfl) ⟨909341, by rfl⟩ : syracuseStep 1212455 = 1818683) B1818683
theorem B1212539 : Blo 806344 1212539 := bstep (se 1 (by rfl) ⟨909404, by rfl⟩ : syracuseStep 1212539 = 1818809) B1818809
theorem B1212665 : Blo 806344 1212665 := bstep (se 2 (by rfl) ⟨454749, by rfl⟩ : syracuseStep 1212665 = 909499) B909499
theorem B13795595 : Blo 806344 13795595 := bstep (se 1 (by rfl) ⟨10346696, by rfl⟩ : syracuseStep 13795595 = 20693393) B20693393
theorem B53051723 : Blo 806344 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B1212767 : Blo 806344 1212767 := bstep (se 1 (by rfl) ⟨909575, by rfl⟩ : syracuseStep 1212767 = 1819151) B1819151
theorem B1212779 : Blo 806344 1212779 := bstep (se 1 (by rfl) ⟨909584, by rfl⟩ : syracuseStep 1212779 = 1819169) B1819169
theorem B3113417 : Blo 806344 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B4096493 : Blo 806344 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B1213007 : Blo 806344 1213007 := bstep (se 1 (by rfl) ⟨909755, by rfl⟩ : syracuseStep 1213007 = 1819511) B1819511
theorem B1213127 : Blo 806344 1213127 := bstep (se 1 (by rfl) ⟨909845, by rfl⟩ : syracuseStep 1213127 = 1819691) B1819691
theorem B1213289 : Blo 806344 1213289 := bstep (se 2 (by rfl) ⟨454983, by rfl⟩ : syracuseStep 1213289 = 909967) B909967
theorem B1213367 : Blo 806344 1213367 := bstep (se 1 (by rfl) ⟨910025, by rfl⟩ : syracuseStep 1213367 = 1820051) B1820051
theorem B1213403 : Blo 806344 1213403 := bstep (se 1 (by rfl) ⟨910052, by rfl⟩ : syracuseStep 1213403 = 1820105) B1820105
theorem B2589853 : Blo 806344 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B4097303 : Blo 806344 4097303 := bstep (se 1 (by rfl) ⟨3072977, by rfl⟩ : syracuseStep 4097303 = 6145955) B6145955
theorem B1213871 : Blo 806344 1213871 := bstep (se 1 (by rfl) ⟨910403, by rfl⟩ : syracuseStep 1213871 = 1820807) B1820807
theorem B1213961 : Blo 806344 1213961 := bstep (se 2 (by rfl) ⟨455235, by rfl⟩ : syracuseStep 1213961 = 910471) B910471
theorem B1213991 : Blo 806344 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B1214075 : Blo 806344 1214075 := bstep (se 1 (by rfl) ⟨910556, by rfl⟩ : syracuseStep 1214075 = 1821113) B1821113
theorem B2721491 : Blo 806344 2721491 := bstep (se 1 (by rfl) ⟨2041118, by rfl⟩ : syracuseStep 2721491 = 4082237) B4082237
theorem B1214201 : Blo 806344 1214201 := bstep (se 2 (by rfl) ⟨455325, by rfl⟩ : syracuseStep 1214201 = 910651) B910651
theorem B1214303 : Blo 806344 1214303 := bstep (se 1 (by rfl) ⟨910727, by rfl⟩ : syracuseStep 1214303 = 1821455) B1821455
theorem B1148779 : Blo 806344 1148779 := bstep (se 1 (by rfl) ⟨861584, by rfl⟩ : syracuseStep 1148779 = 1723169) B1723169
theorem B1214315 : Blo 806344 1214315 := bstep (se 1 (by rfl) ⟨910736, by rfl⟩ : syracuseStep 1214315 = 1821473) B1821473
theorem B3278855 : Blo 806344 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B1149007 : Blo 806344 1149007 := bstep (se 1 (by rfl) ⟨861755, by rfl⟩ : syracuseStep 1149007 = 1723511) B1723511
theorem B1214543 : Blo 806344 1214543 := bstep (se 1 (by rfl) ⟨910907, by rfl⟩ : syracuseStep 1214543 = 1821815) B1821815
theorem B1214663 : Blo 806344 1214663 := bstep (se 1 (by rfl) ⟨910997, by rfl⟩ : syracuseStep 1214663 = 1821995) B1821995
theorem B1214825 : Blo 806344 1214825 := bstep (se 2 (by rfl) ⟨455559, by rfl⟩ : syracuseStep 1214825 = 911119) B911119
theorem B1214903 : Blo 806344 1214903 := bstep (se 1 (by rfl) ⟨911177, by rfl⟩ : syracuseStep 1214903 = 1822355) B1822355
theorem B1214939 : Blo 806344 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B1641131 : Blo 806344 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B28314305 : Blo 806344 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B11995877 : Blo 806344 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B4098923 : Blo 806344 4098923 := bstep (se 1 (by rfl) ⟨3074192, by rfl⟩ : syracuseStep 4098923 = 6148385) B6148385
theorem B2722679 : Blo 806344 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B1215407 : Blo 806344 1215407 := bstep (se 1 (by rfl) ⟨911555, by rfl⟩ : syracuseStep 1215407 = 1823111) B1823111
theorem B1215497 : Blo 806344 1215497 := bstep (se 2 (by rfl) ⟨455811, by rfl⟩ : syracuseStep 1215497 = 911623) B911623
theorem B2591801 : Blo 806344 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B2722895 : Blo 806344 2722895 := bstep (se 1 (by rfl) ⟨2042171, by rfl⟩ : syracuseStep 2722895 = 4084343) B4084343
theorem B1641551 : Blo 806344 1641551 := bstep (se 1 (by rfl) ⟨1231163, by rfl⟩ : syracuseStep 1641551 = 2462327) B2462327
theorem B2723273 : Blo 806344 2723273 := bstep (se 2 (by rfl) ⟨1021227, by rfl⟩ : syracuseStep 2723273 = 2042455) B2042455
theorem B4099571 : Blo 806344 4099571 := bstep (se 1 (by rfl) ⟨3074678, by rfl⟩ : syracuseStep 4099571 = 6149357) B6149357
theorem B7376471 : Blo 806344 7376471 := bstep (se 1 (by rfl) ⟨5532353, by rfl⟩ : syracuseStep 7376471 = 11064707) B11064707
theorem B23301755 : Blo 806344 23301755 := bstep (se 1 (by rfl) ⟨17476316, by rfl⟩ : syracuseStep 23301755 = 34952633) B34952633
theorem B2723543 : Blo 806344 2723543 := bstep (se 1 (by rfl) ⟨2042657, by rfl⟩ : syracuseStep 2723543 = 4085315) B4085315
theorem B2723759 : Blo 806344 2723759 := bstep (se 1 (by rfl) ⟨2042819, by rfl⟩ : syracuseStep 2723759 = 4085639) B4085639
theorem B4919453 : Blo 806344 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B922151 : Blo 806344 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1020539 : Blo 806344 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B1839739 : Blo 806344 1839739 := bstep (se 1 (by rfl) ⟨1379804, by rfl⟩ : syracuseStep 1839739 = 2759609) B2759609
theorem B10490579 : Blo 806344 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B4100867 : Blo 806344 4100867 := bstep (se 1 (by rfl) ⟨3075650, by rfl⟩ : syracuseStep 4100867 = 6151301) B6151301
theorem B3740489 : Blo 806344 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B8753993 : Blo 806344 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B2298719 : Blo 806344 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B4920955 : Blo 806344 4920955 := bstep (se 1 (by rfl) ⟨3690716, by rfl⟩ : syracuseStep 4920955 = 7381433) B7381433
theorem B2332577 : Blo 806344 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B8755289 : Blo 806344 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B2726135 : Blo 806344 2726135 := bstep (se 1 (by rfl) ⟨2044601, by rfl⟩ : syracuseStep 2726135 = 4089203) B4089203
theorem B1153273 : Blo 806344 1153273 := bstep (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) B864955
theorem B9836849 : Blo 806344 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B6232585 : Blo 806344 6232585 := bstep (se 2 (by rfl) ⟨2337219, by rfl⟩ : syracuseStep 6232585 = 4674439) B4674439
theorem B5839393 : Blo 806344 5839393 := bstep (se 2 (by rfl) ⟨2189772, by rfl⟩ : syracuseStep 5839393 = 4379545) B4379545
theorem B2726459 : Blo 806344 2726459 := bstep (se 1 (by rfl) ⟨2044844, by rfl⟩ : syracuseStep 2726459 = 4089689) B4089689
theorem B3447431 : Blo 806344 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B2726729 : Blo 806344 2726729 := bstep (se 2 (by rfl) ⟨1022523, by rfl⟩ : syracuseStep 2726729 = 2045047) B2045047
theorem B1940411 : Blo 806344 1940411 := bstep (se 1 (by rfl) ⟨1455308, by rfl⟩ : syracuseStep 1940411 = 2910617) B2910617
theorem B4365515 : Blo 806344 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B4595069 : Blo 806344 4595069 := bstep (se 3 (by rfl) ⟨861575, by rfl⟩ : syracuseStep 4595069 = 1723151) B1723151
theorem B9838219 : Blo 806344 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B2727863 : Blo 806344 2727863 := bstep (se 1 (by rfl) ⟨2045897, by rfl⟩ : syracuseStep 2727863 = 4091795) B4091795
theorem B3448763 : Blo 806344 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B19636253 : Blo 806344 19636253 := bstep (se 3 (by rfl) ⟨3681797, by rfl⟩ : syracuseStep 19636253 = 7363595) B7363595
theorem B1679791 : Blo 806344 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B2728457 : Blo 806344 2728457 := bstep (se 2 (by rfl) ⟨1023171, by rfl⟩ : syracuseStep 2728457 = 2046343) B2046343
theorem B6136721 : Blo 806344 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B2335675 : Blo 806344 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B4596709 : Blo 806344 4596709 := bstep (se 4 (by rfl) ⟨430941, by rfl⟩ : syracuseStep 4596709 = 861883) B861883
theorem B1942535 : Blo 806344 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B4596983 : Blo 806344 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B2729321 : Blo 806344 2729321 := bstep (se 2 (by rfl) ⟨1023495, by rfl⟩ : syracuseStep 2729321 = 2046991) B2046991
theorem B1025455 : Blo 806344 1025455 := bstep (se 1 (by rfl) ⟨769091, by rfl⟩ : syracuseStep 1025455 = 1538183) B1538183
theorem B2631113 : Blo 806344 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B4597235 : Blo 806344 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B2041483 : Blo 806344 2041483 := bstep (se 1 (by rfl) ⟨1531112, by rfl⟩ : syracuseStep 2041483 = 3062225) B3062225
theorem B2041787 : Blo 806344 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B2729915 : Blo 806344 2729915 := bstep (se 1 (by rfl) ⟨2047436, by rfl⟩ : syracuseStep 2729915 = 4094873) B4094873
theorem B3451223 : Blo 806344 3451223 := bstep (se 1 (by rfl) ⟨2588417, by rfl⟩ : syracuseStep 3451223 = 5176835) B5176835
theorem B2304551 : Blo 806344 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B2042567 : Blo 806344 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B2042617 : Blo 806344 2042617 := bstep (se 2 (by rfl) ⟨765981, by rfl⟩ : syracuseStep 2042617 = 1531963) B1531963
theorem B11643725 : Blo 806344 11643725 := bstep (se 3 (by rfl) ⟨2183198, by rfl⟩ : syracuseStep 11643725 = 4366397) B4366397
theorem B7187429 : Blo 806344 7187429 := bstep (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) B1347643
theorem B6139151 : Blo 806344 6139151 := bstep (se 1 (by rfl) ⟨4604363, by rfl⟩ : syracuseStep 6139151 = 9208727) B9208727
theorem B8858969 : Blo 806344 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B4926845 : Blo 806344 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B2043265 : Blo 806344 2043265 := bstep (se 2 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 2043265 = 1532449) B1532449
theorem B1551881 : Blo 806344 1551881 := bstep (se 2 (by rfl) ⟨581955, by rfl⟩ : syracuseStep 1551881 = 1163911) B1163911
theorem B2731643 : Blo 806344 2731643 := bstep (se 1 (by rfl) ⟨2048732, by rfl⟩ : syracuseStep 2731643 = 4097465) B4097465
theorem B4599443 : Blo 806344 4599443 := bstep (se 1 (by rfl) ⟨3449582, by rfl⟩ : syracuseStep 4599443 = 6899165) B6899165
theorem B5189341 : Blo 806344 5189341 := bstep (se 3 (by rfl) ⟨973001, by rfl⟩ : syracuseStep 5189341 = 1946003) B1946003
theorem B2731805 : Blo 806344 2731805 := bstep (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) B1024427
theorem B1814345 : Blo 806344 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B6631303 : Blo 806344 6631303 := bstep (se 1 (by rfl) ⟨4973477, by rfl⟩ : syracuseStep 6631303 = 9946955) B9946955
theorem B1453967 : Blo 806344 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B6565819 : Blo 806344 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B10498211 : Blo 806344 10498211 := bstep (se 1 (by rfl) ⟨7873658, by rfl⟩ : syracuseStep 10498211 = 15747317) B15747317
theorem B2044075 : Blo 806344 2044075 := bstep (se 1 (by rfl) ⟨1533056, by rfl⟩ : syracuseStep 2044075 = 3066113) B3066113
theorem B4600151 : Blo 806344 4600151 := bstep (se 1 (by rfl) ⟨3450113, by rfl⟩ : syracuseStep 4600151 = 6900227) B6900227
theorem B2044379 : Blo 806344 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B2732507 : Blo 806344 2732507 := bstep (se 1 (by rfl) ⟨2049380, by rfl⟩ : syracuseStep 2732507 = 4098761) B4098761
theorem B1815137 : Blo 806344 1815137 := bstep (se 2 (by rfl) ⟨680676, by rfl⟩ : syracuseStep 1815137 = 1361353) B1361353
theorem B1815479 : Blo 806344 1815479 := bstep (se 1 (by rfl) ⟨1361609, by rfl⟩ : syracuseStep 1815479 = 2723219) B2723219
theorem B2733209 : Blo 806344 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B1816073 : Blo 806344 1816073 := bstep (se 2 (by rfl) ⟨681027, by rfl⟩ : syracuseStep 1816073 = 1362055) B1362055
theorem B15513281 : Blo 806344 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B1816415 : Blo 806344 1816415 := bstep (se 1 (by rfl) ⟨1362311, by rfl⟩ : syracuseStep 1816415 = 2724623) B2724623
theorem B53262197 : Blo 806344 53262197 := bstep (se 5 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 53262197 = 4993331) B4993331
theorem B1456015 : Blo 806344 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B2045857 : Blo 806344 2045857 := bstep (se 2 (by rfl) ⟨767196, by rfl⟩ : syracuseStep 2045857 = 1534393) B1534393
theorem B1816595 : Blo 806344 1816595 := bstep (se 1 (by rfl) ⟨1362446, by rfl⟩ : syracuseStep 1816595 = 2724893) B2724893
theorem B5519441 : Blo 806344 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B14727257 : Blo 806344 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B6142067 : Blo 806344 6142067 := bstep (se 1 (by rfl) ⟨4606550, by rfl⟩ : syracuseStep 6142067 = 9213101) B9213101
theorem B2734397 : Blo 806344 2734397 := bstep (se 3 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 2734397 = 1025399) B1025399
theorem B1816937 : Blo 806344 1816937 := bstep (se 2 (by rfl) ⟨681351, by rfl⟩ : syracuseStep 1816937 = 1362703) B1362703
theorem B4372973 : Blo 806344 4372973 := bstep (se 3 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 4372973 = 1639865) B1639865
theorem B3062407 : Blo 806344 3062407 := bstep (se 1 (by rfl) ⟨2296805, by rfl⟩ : syracuseStep 3062407 = 4593611) B4593611
theorem B3324739 : Blo 806344 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B3062711 : Blo 806344 3062711 := bstep (se 1 (by rfl) ⟨2297033, by rfl⟩ : syracuseStep 3062711 = 4594067) B4594067
theorem B1817531 : Blo 806344 1817531 := bstep (se 1 (by rfl) ⟨1363148, by rfl⟩ : syracuseStep 1817531 = 2726297) B2726297
theorem B998363 : Blo 806344 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B1817657 : Blo 806344 1817657 := bstep (se 2 (by rfl) ⟨681621, by rfl⟩ : syracuseStep 1817657 = 1363243) B1363243
theorem B5979203 : Blo 806344 5979203 := bstep (se 1 (by rfl) ⟨4484402, by rfl⟩ : syracuseStep 5979203 = 8968805) B8968805
theorem B14925181 : Blo 806344 14925181 := bstep (se 3 (by rfl) ⟨2798471, by rfl⟩ : syracuseStep 14925181 = 5596943) B5596943
theorem B1817999 : Blo 806344 1817999 := bstep (se 1 (by rfl) ⟨1363499, by rfl⟩ : syracuseStep 1817999 = 2726999) B2726999
theorem B5979793 : Blo 806344 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B3686087 : Blo 806344 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B1818323 : Blo 806344 1818323 := bstep (se 1 (by rfl) ⟨1363742, by rfl⟩ : syracuseStep 1818323 = 2727485) B2727485
theorem B3456863 : Blo 806344 3456863 := bstep (se 1 (by rfl) ⟨2592647, by rfl⟩ : syracuseStep 3456863 = 5185295) B5185295
theorem B3063865 : Blo 806344 3063865 := bstep (se 2 (by rfl) ⟨1148949, by rfl⟩ : syracuseStep 3063865 = 2297899) B2297899
theorem B3064169 : Blo 806344 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B6209921 : Blo 806344 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B2048399 : Blo 806344 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B13124105 : Blo 806344 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B1819259 : Blo 806344 1819259 := bstep (se 1 (by rfl) ⟨1364444, by rfl⟩ : syracuseStep 1819259 = 2728889) B2728889
theorem B2048723 : Blo 806344 2048723 := bstep (se 1 (by rfl) ⟨1536542, by rfl⟩ : syracuseStep 2048723 = 3073085) B3073085
theorem B1164025 : Blo 806344 1164025 := bstep (se 2 (by rfl) ⟨436509, by rfl⟩ : syracuseStep 1164025 = 873019) B873019
theorem B1819385 : Blo 806344 1819385 := bstep (se 2 (by rfl) ⟨682269, by rfl⟩ : syracuseStep 1819385 = 1364539) B1364539
theorem B1164251 : Blo 806344 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B1819655 : Blo 806344 1819655 := bstep (se 1 (by rfl) ⟨1364741, by rfl⟩ : syracuseStep 1819655 = 2729483) B2729483
theorem B3884051 : Blo 806344 3884051 := bstep (se 1 (by rfl) ⟨2913038, by rfl⟩ : syracuseStep 3884051 = 5826077) B5826077
theorem B1360975 : Blo 806344 1360975 := bstep (se 1 (by rfl) ⟨1020731, by rfl⟩ : syracuseStep 1360975 = 2041463) B2041463
theorem B1819727 : Blo 806344 1819727 := bstep (se 1 (by rfl) ⟨1364795, by rfl⟩ : syracuseStep 1819727 = 2729591) B2729591
theorem B3884203 : Blo 806344 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B6571201 : Blo 806344 6571201 := bstep (se 2 (by rfl) ⟨2464200, by rfl⟩ : syracuseStep 6571201 = 4928401) B4928401
theorem B6898891 : Blo 806344 6898891 := bstep (se 1 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 6898891 = 10348337) B10348337
theorem B1361225 : Blo 806344 1361225 := bstep (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) B1020919
theorem B1459561 : Blo 806344 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B1820123 : Blo 806344 1820123 := bstep (se 1 (by rfl) ⟨1365092, by rfl⟩ : syracuseStep 1820123 = 2730185) B2730185
theorem B1558187 : Blo 806344 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B1361657 : Blo 806344 1361657 := bstep (se 2 (by rfl) ⟨510621, by rfl⟩ : syracuseStep 1361657 = 1021243) B1021243
theorem B2049887 : Blo 806344 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B48547745 : Blo 806344 48547745 := bstep (se 2 (by rfl) ⟨18205404, by rfl⟩ : syracuseStep 48547745 = 36410809) B36410809
theorem B1361839 : Blo 806344 1361839 := bstep (se 1 (by rfl) ⟨1021379, by rfl⟩ : syracuseStep 1361839 = 2042759) B2042759
theorem B1820591 : Blo 806344 1820591 := bstep (se 1 (by rfl) ⟨1365443, by rfl⟩ : syracuseStep 1820591 = 2730887) B2730887
theorem B1361927 : Blo 806344 1361927 := bstep (se 1 (by rfl) ⟨1021445, by rfl⟩ : syracuseStep 1361927 = 2042891) B2042891
theorem B7358521 : Blo 806344 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B1820843 : Blo 806344 1820843 := bstep (se 1 (by rfl) ⟨1365632, by rfl⟩ : syracuseStep 1820843 = 2731265) B2731265
theorem B1362271 : Blo 806344 1362271 := bstep (se 1 (by rfl) ⟨1021703, by rfl⟩ : syracuseStep 1362271 = 2043407) B2043407
theorem B1362359 : Blo 806344 1362359 := bstep (se 1 (by rfl) ⟨1021769, by rfl⟩ : syracuseStep 1362359 = 2043539) B2043539
theorem B22432241 : Blo 806344 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B52546229 : Blo 806344 52546229 := bstep (se 5 (by rfl) ⟨2463104, by rfl⟩ : syracuseStep 52546229 = 4926209) B4926209
theorem B1821383 : Blo 806344 1821383 := bstep (se 1 (by rfl) ⟨1366037, by rfl⟩ : syracuseStep 1821383 = 2732075) B2732075
theorem B2050991 : Blo 806344 2050991 := bstep (se 1 (by rfl) ⟨1538243, by rfl⟩ : syracuseStep 2050991 = 3076487) B3076487
theorem B1362953 : Blo 806344 1362953 := bstep (se 2 (by rfl) ⟨511107, by rfl⟩ : syracuseStep 1362953 = 1022215) B1022215
theorem B1363115 : Blo 806344 1363115 := bstep (se 1 (by rfl) ⟨1022336, by rfl⟩ : syracuseStep 1363115 = 2044673) B2044673
theorem B23317793 : Blo 806344 23317793 := bstep (se 2 (by rfl) ⟨8744172, by rfl⟩ : syracuseStep 23317793 = 17488345) B17488345
theorem B5819849 : Blo 806344 5819849 := bstep (se 2 (by rfl) ⟨2182443, by rfl⟩ : syracuseStep 5819849 = 4364887) B4364887
theorem B3460553 : Blo 806344 3460553 := bstep (se 2 (by rfl) ⟨1297707, by rfl⟩ : syracuseStep 3460553 = 2595415) B2595415
theorem B806363 : Blo 806344 806363 := bstep (se 1 (by rfl) ⟨604772, by rfl⟩ : syracuseStep 806363 = 1209545) B1209545
theorem B806439 : Blo 806344 806439 := bstep (se 1 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 806439 = 1209659) B1209659
theorem B1822247 : Blo 806344 1822247 := bstep (se 1 (by rfl) ⟨1366685, by rfl⟩ : syracuseStep 1822247 = 2733371) B2733371
theorem B1363513 : Blo 806344 1363513 := bstep (se 2 (by rfl) ⟨511317, by rfl⟩ : syracuseStep 1363513 = 1022635) B1022635
theorem B806479 : Blo 806344 806479 := bstep (se 1 (by rfl) ⟨604859, by rfl⟩ : syracuseStep 806479 = 1209719) B1209719
theorem B806495 : Blo 806344 806495 := bstep (se 1 (by rfl) ⟨604871, by rfl⟩ : syracuseStep 806495 = 1209743) B1209743
theorem B806523 : Blo 806344 806523 := bstep (se 1 (by rfl) ⟨604892, by rfl⟩ : syracuseStep 806523 = 1209785) B1209785
theorem B14012027 : Blo 806344 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B806575 : Blo 806344 806575 := bstep (se 1 (by rfl) ⟨604931, by rfl⟩ : syracuseStep 806575 = 1209863) B1209863
theorem B806599 : Blo 806344 806599 := bstep (se 1 (by rfl) ⟨604949, by rfl⟩ : syracuseStep 806599 = 1209899) B1209899
theorem B1363655 : Blo 806344 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B806619 : Blo 806344 806619 := bstep (se 1 (by rfl) ⟨604964, by rfl⟩ : syracuseStep 806619 = 1209929) B1209929
theorem B806695 : Blo 806344 806695 := bstep (se 1 (by rfl) ⟨605021, by rfl⟩ : syracuseStep 806695 = 1210043) B1210043
theorem B6147899 : Blo 806344 6147899 := bstep (se 1 (by rfl) ⟨4610924, by rfl⟩ : syracuseStep 6147899 = 9221849) B9221849
theorem B806735 : Blo 806344 806735 := bstep (se 1 (by rfl) ⟨605051, by rfl⟩ : syracuseStep 806735 = 1210103) B1210103
theorem B806751 : Blo 806344 806751 := bstep (se 1 (by rfl) ⟨605063, by rfl⟩ : syracuseStep 806751 = 1210127) B1210127
theorem B1363817 : Blo 806344 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B1822571 : Blo 806344 1822571 := bstep (se 1 (by rfl) ⟨1366928, by rfl⟩ : syracuseStep 1822571 = 2733857) B2733857
theorem B806779 : Blo 806344 806779 := bstep (se 1 (by rfl) ⟨605084, by rfl⟩ : syracuseStep 806779 = 1210169) B1210169
theorem B1822625 : Blo 806344 1822625 := bstep (se 2 (by rfl) ⟨683484, by rfl⟩ : syracuseStep 1822625 = 1366969) B1366969
theorem B806831 : Blo 806344 806831 := bstep (se 1 (by rfl) ⟨605123, by rfl⟩ : syracuseStep 806831 = 1210247) B1210247
theorem B806855 : Blo 806344 806855 := bstep (se 1 (by rfl) ⟨605141, by rfl⟩ : syracuseStep 806855 = 1210283) B1210283
theorem B806875 : Blo 806344 806875 := bstep (se 1 (by rfl) ⟨605156, by rfl⟩ : syracuseStep 806875 = 1210313) B1210313
theorem B806951 : Blo 806344 806951 := bstep (se 1 (by rfl) ⟨605213, by rfl⟩ : syracuseStep 806951 = 1210427) B1210427
theorem B13127741 : Blo 806344 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B806991 : Blo 806344 806991 := bstep (se 1 (by rfl) ⟨605243, by rfl⟩ : syracuseStep 806991 = 1210487) B1210487
theorem B3461201 : Blo 806344 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B807007 : Blo 806344 807007 := bstep (se 1 (by rfl) ⟨605255, by rfl⟩ : syracuseStep 807007 = 1210511) B1210511
theorem B807035 : Blo 806344 807035 := bstep (se 1 (by rfl) ⟨605276, by rfl⟩ : syracuseStep 807035 = 1210553) B1210553
theorem B3068057 : Blo 806344 3068057 := bstep (se 2 (by rfl) ⟨1150521, by rfl⟩ : syracuseStep 3068057 = 2301043) B2301043
theorem B807087 : Blo 806344 807087 := bstep (se 1 (by rfl) ⟨605315, by rfl⟩ : syracuseStep 807087 = 1210631) B1210631
theorem B8736947 : Blo 806344 8736947 := bstep (se 1 (by rfl) ⟨6552710, by rfl⟩ : syracuseStep 8736947 = 13105421) B13105421
theorem B807111 : Blo 806344 807111 := bstep (se 1 (by rfl) ⟨605333, by rfl⟩ : syracuseStep 807111 = 1210667) B1210667
theorem B807131 : Blo 806344 807131 := bstep (se 1 (by rfl) ⟨605348, by rfl⟩ : syracuseStep 807131 = 1210697) B1210697
theorem B1364215 : Blo 806344 1364215 := bstep (se 1 (by rfl) ⟨1023161, by rfl⟩ : syracuseStep 1364215 = 2046323) B2046323
theorem B1822967 : Blo 806344 1822967 := bstep (se 1 (by rfl) ⟨1367225, by rfl⟩ : syracuseStep 1822967 = 2734451) B2734451
theorem B807207 : Blo 806344 807207 := bstep (se 1 (by rfl) ⟨605405, by rfl⟩ : syracuseStep 807207 = 1210811) B1210811
theorem B807247 : Blo 806344 807247 := bstep (se 1 (by rfl) ⟨605435, by rfl⟩ : syracuseStep 807247 = 1210871) B1210871
theorem B807263 : Blo 806344 807263 := bstep (se 1 (by rfl) ⟨605447, by rfl⟩ : syracuseStep 807263 = 1210895) B1210895
theorem B807291 : Blo 806344 807291 := bstep (se 1 (by rfl) ⟨605468, by rfl⟩ : syracuseStep 807291 = 1210937) B1210937
theorem B807343 : Blo 806344 807343 := bstep (se 1 (by rfl) ⟨605507, by rfl⟩ : syracuseStep 807343 = 1211015) B1211015
theorem B1364411 : Blo 806344 1364411 := bstep (se 1 (by rfl) ⟨1023308, by rfl⟩ : syracuseStep 1364411 = 2046617) B2046617
theorem B807367 : Blo 806344 807367 := bstep (se 1 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 807367 = 1211051) B1211051
theorem B807387 : Blo 806344 807387 := bstep (se 1 (by rfl) ⟨605540, by rfl⟩ : syracuseStep 807387 = 1211081) B1211081
theorem B807463 : Blo 806344 807463 := bstep (se 1 (by rfl) ⟨605597, by rfl⟩ : syracuseStep 807463 = 1211195) B1211195
theorem B1364519 : Blo 806344 1364519 := bstep (se 1 (by rfl) ⟨1023389, by rfl⟩ : syracuseStep 1364519 = 2046779) B2046779
theorem B807503 : Blo 806344 807503 := bstep (se 1 (by rfl) ⟨605627, by rfl⟩ : syracuseStep 807503 = 1211255) B1211255
theorem B807519 : Blo 806344 807519 := bstep (se 1 (by rfl) ⟨605639, by rfl⟩ : syracuseStep 807519 = 1211279) B1211279
theorem B3068513 : Blo 806344 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B807547 : Blo 806344 807547 := bstep (se 1 (by rfl) ⟨605660, by rfl⟩ : syracuseStep 807547 = 1211321) B1211321
theorem B4608647 : Blo 806344 4608647 := bstep (se 1 (by rfl) ⟨3456485, by rfl⟩ : syracuseStep 4608647 = 6912971) B6912971
theorem B807599 : Blo 806344 807599 := bstep (se 1 (by rfl) ⟨605699, by rfl⟩ : syracuseStep 807599 = 1211399) B1211399
theorem B807623 : Blo 806344 807623 := bstep (se 1 (by rfl) ⟨605717, by rfl⟩ : syracuseStep 807623 = 1211435) B1211435
theorem B807643 : Blo 806344 807643 := bstep (se 1 (by rfl) ⟨605732, by rfl⟩ : syracuseStep 807643 = 1211465) B1211465
theorem B7492355 : Blo 806344 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B807719 : Blo 806344 807719 := bstep (se 1 (by rfl) ⟨605789, by rfl⟩ : syracuseStep 807719 = 1211579) B1211579
theorem B1364809 : Blo 806344 1364809 := bstep (se 2 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 1364809 = 1023607) B1023607
theorem B807759 : Blo 806344 807759 := bstep (se 1 (by rfl) ⟨605819, by rfl⟩ : syracuseStep 807759 = 1211639) B1211639
theorem B807775 : Blo 806344 807775 := bstep (se 1 (by rfl) ⟨605831, by rfl⟩ : syracuseStep 807775 = 1211663) B1211663
theorem B1364843 : Blo 806344 1364843 := bstep (se 1 (by rfl) ⟨1023632, by rfl⟩ : syracuseStep 1364843 = 2047265) B2047265
theorem B807803 : Blo 806344 807803 := bstep (se 1 (by rfl) ⟨605852, by rfl⟩ : syracuseStep 807803 = 1211705) B1211705
theorem B807855 : Blo 806344 807855 := bstep (se 1 (by rfl) ⟨605891, by rfl⟩ : syracuseStep 807855 = 1211783) B1211783
theorem B807879 : Blo 806344 807879 := bstep (se 1 (by rfl) ⟨605909, by rfl⟩ : syracuseStep 807879 = 1211819) B1211819
theorem B807899 : Blo 806344 807899 := bstep (se 1 (by rfl) ⟨605924, by rfl⟩ : syracuseStep 807899 = 1211849) B1211849
theorem B807975 : Blo 806344 807975 := bstep (se 1 (by rfl) ⟨605981, by rfl⟩ : syracuseStep 807975 = 1211963) B1211963
theorem B808015 : Blo 806344 808015 := bstep (se 1 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 808015 = 1212023) B1212023
theorem B808031 : Blo 806344 808031 := bstep (se 1 (by rfl) ⟨606023, by rfl⟩ : syracuseStep 808031 = 1212047) B1212047
theorem B808059 : Blo 806344 808059 := bstep (se 1 (by rfl) ⟨606044, by rfl⟩ : syracuseStep 808059 = 1212089) B1212089
theorem B808111 : Blo 806344 808111 := bstep (se 1 (by rfl) ⟨606083, by rfl⟩ : syracuseStep 808111 = 1212167) B1212167
theorem B808135 : Blo 806344 808135 := bstep (se 1 (by rfl) ⟨606101, by rfl⟩ : syracuseStep 808135 = 1212203) B1212203
theorem B808155 : Blo 806344 808155 := bstep (se 1 (by rfl) ⟨606116, by rfl⟩ : syracuseStep 808155 = 1212233) B1212233
theorem B1365241 : Blo 806344 1365241 := bstep (se 2 (by rfl) ⟨511965, by rfl⟩ : syracuseStep 1365241 = 1023931) B1023931
theorem B808231 : Blo 806344 808231 := bstep (se 1 (by rfl) ⟨606173, by rfl⟩ : syracuseStep 808231 = 1212347) B1212347
theorem B808271 : Blo 806344 808271 := bstep (se 1 (by rfl) ⟨606203, by rfl⟩ : syracuseStep 808271 = 1212407) B1212407
theorem B808287 : Blo 806344 808287 := bstep (se 1 (by rfl) ⟨606215, by rfl⟩ : syracuseStep 808287 = 1212431) B1212431
theorem B1660267 : Blo 806344 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B808315 : Blo 806344 808315 := bstep (se 1 (by rfl) ⟨606236, by rfl⟩ : syracuseStep 808315 = 1212473) B1212473
theorem B4904317 : Blo 806344 4904317 := bstep (se 3 (by rfl) ⟨919559, by rfl⟩ : syracuseStep 4904317 = 1839119) B1839119
theorem B808367 : Blo 806344 808367 := bstep (se 1 (by rfl) ⟨606275, by rfl⟩ : syracuseStep 808367 = 1212551) B1212551
theorem B808391 : Blo 806344 808391 := bstep (se 1 (by rfl) ⟨606293, by rfl⟩ : syracuseStep 808391 = 1212587) B1212587
theorem B808411 : Blo 806344 808411 := bstep (se 1 (by rfl) ⟨606308, by rfl⟩ : syracuseStep 808411 = 1212617) B1212617
theorem B1365511 : Blo 806344 1365511 := bstep (se 1 (by rfl) ⟨1024133, by rfl⟩ : syracuseStep 1365511 = 2048267) B2048267
theorem B808487 : Blo 806344 808487 := bstep (se 1 (by rfl) ⟨606365, by rfl⟩ : syracuseStep 808487 = 1212731) B1212731
theorem B808527 : Blo 806344 808527 := bstep (se 1 (by rfl) ⟨606395, by rfl⟩ : syracuseStep 808527 = 1212791) B1212791
theorem B808543 : Blo 806344 808543 := bstep (se 1 (by rfl) ⟨606407, by rfl⟩ : syracuseStep 808543 = 1212815) B1212815
theorem B808571 : Blo 806344 808571 := bstep (se 1 (by rfl) ⟨606428, by rfl⟩ : syracuseStep 808571 = 1212857) B1212857
theorem B6641297 : Blo 806344 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B808623 : Blo 806344 808623 := bstep (se 1 (by rfl) ⟨606467, by rfl⟩ : syracuseStep 808623 = 1212935) B1212935
theorem B808647 : Blo 806344 808647 := bstep (se 1 (by rfl) ⟨606485, by rfl⟩ : syracuseStep 808647 = 1212971) B1212971
theorem B808667 : Blo 806344 808667 := bstep (se 1 (by rfl) ⟨606500, by rfl⟩ : syracuseStep 808667 = 1213001) B1213001
theorem B808743 : Blo 806344 808743 := bstep (se 1 (by rfl) ⟨606557, by rfl⟩ : syracuseStep 808743 = 1213115) B1213115
theorem B808783 : Blo 806344 808783 := bstep (se 1 (by rfl) ⟨606587, by rfl⟩ : syracuseStep 808783 = 1213175) B1213175
theorem B808799 : Blo 806344 808799 := bstep (se 1 (by rfl) ⟨606599, by rfl⟩ : syracuseStep 808799 = 1213199) B1213199
theorem B808827 : Blo 806344 808827 := bstep (se 1 (by rfl) ⟨606620, by rfl⟩ : syracuseStep 808827 = 1213241) B1213241
theorem B808879 : Blo 806344 808879 := bstep (se 1 (by rfl) ⟨606659, by rfl⟩ : syracuseStep 808879 = 1213319) B1213319
theorem B1365943 : Blo 806344 1365943 := bstep (se 1 (by rfl) ⟨1024457, by rfl⟩ : syracuseStep 1365943 = 2048915) B2048915
theorem B2185147 : Blo 806344 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B808903 : Blo 806344 808903 := bstep (se 1 (by rfl) ⟨606677, by rfl⟩ : syracuseStep 808903 = 1213355) B1213355
theorem B808923 : Blo 806344 808923 := bstep (se 1 (by rfl) ⟨606692, by rfl⟩ : syracuseStep 808923 = 1213385) B1213385
theorem B3069971 : Blo 806344 3069971 := bstep (se 1 (by rfl) ⟨2302478, by rfl⟩ : syracuseStep 3069971 = 4604957) B4604957
theorem B907303 : Blo 806344 907303 := bstep (se 1 (by rfl) ⟨680477, by rfl⟩ : syracuseStep 907303 = 1360955) B1360955
theorem B808999 : Blo 806344 808999 := bstep (se 1 (by rfl) ⟨606749, by rfl⟩ : syracuseStep 808999 = 1213499) B1213499
theorem B4610105 : Blo 806344 4610105 := bstep (se 2 (by rfl) ⟨1728789, by rfl⟩ : syracuseStep 4610105 = 3457579) B3457579
theorem B809039 : Blo 806344 809039 := bstep (se 1 (by rfl) ⟨606779, by rfl⟩ : syracuseStep 809039 = 1213559) B1213559
theorem B809055 : Blo 806344 809055 := bstep (se 1 (by rfl) ⟨606791, by rfl⟩ : syracuseStep 809055 = 1213583) B1213583
theorem B809083 : Blo 806344 809083 := bstep (se 1 (by rfl) ⟨606812, by rfl⟩ : syracuseStep 809083 = 1213625) B1213625
theorem B1366139 : Blo 806344 1366139 := bstep (se 1 (by rfl) ⟨1024604, by rfl⟩ : syracuseStep 1366139 = 2049209) B2049209
theorem B809135 : Blo 806344 809135 := bstep (se 1 (by rfl) ⟨606851, by rfl⟩ : syracuseStep 809135 = 1213703) B1213703
theorem B809159 : Blo 806344 809159 := bstep (se 1 (by rfl) ⟨606869, by rfl⟩ : syracuseStep 809159 = 1213739) B1213739
theorem B809179 : Blo 806344 809179 := bstep (se 1 (by rfl) ⟨606884, by rfl⟩ : syracuseStep 809179 = 1213769) B1213769
theorem B809255 : Blo 806344 809255 := bstep (se 1 (by rfl) ⟨606941, by rfl⟩ : syracuseStep 809255 = 1213883) B1213883
theorem B809295 : Blo 806344 809295 := bstep (se 1 (by rfl) ⟨606971, by rfl⟩ : syracuseStep 809295 = 1213943) B1213943
theorem B809311 : Blo 806344 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B809339 : Blo 806344 809339 := bstep (se 1 (by rfl) ⟨607004, by rfl⟩ : syracuseStep 809339 = 1214009) B1214009
theorem B809391 : Blo 806344 809391 := bstep (se 1 (by rfl) ⟨607043, by rfl⟩ : syracuseStep 809391 = 1214087) B1214087
theorem B809415 : Blo 806344 809415 := bstep (se 1 (by rfl) ⟨607061, by rfl⟩ : syracuseStep 809415 = 1214123) B1214123
theorem B21027275 : Blo 806344 21027275 := bstep (se 1 (by rfl) ⟨15770456, by rfl⟩ : syracuseStep 21027275 = 31540913) B31540913
theorem B809435 : Blo 806344 809435 := bstep (se 1 (by rfl) ⟨607076, by rfl⟩ : syracuseStep 809435 = 1214153) B1214153
theorem B1366537 : Blo 806344 1366537 := bstep (se 2 (by rfl) ⟨512451, by rfl⟩ : syracuseStep 1366537 = 1024903) B1024903
theorem B809511 : Blo 806344 809511 := bstep (se 1 (by rfl) ⟨607133, by rfl⟩ : syracuseStep 809511 = 1214267) B1214267
theorem B809551 : Blo 806344 809551 := bstep (se 1 (by rfl) ⟨607163, by rfl⟩ : syracuseStep 809551 = 1214327) B1214327
theorem B809567 : Blo 806344 809567 := bstep (se 1 (by rfl) ⟨607175, by rfl⟩ : syracuseStep 809567 = 1214351) B1214351
theorem B809595 : Blo 806344 809595 := bstep (se 1 (by rfl) ⟨607196, by rfl⟩ : syracuseStep 809595 = 1214393) B1214393
theorem B1366699 : Blo 806344 1366699 := bstep (se 1 (by rfl) ⟨1025024, by rfl⟩ : syracuseStep 1366699 = 2050049) B2050049
theorem B809647 : Blo 806344 809647 := bstep (se 1 (by rfl) ⟨607235, by rfl⟩ : syracuseStep 809647 = 1214471) B1214471
theorem B809671 : Blo 806344 809671 := bstep (se 1 (by rfl) ⟨607253, by rfl⟩ : syracuseStep 809671 = 1214507) B1214507
theorem B809691 : Blo 806344 809691 := bstep (se 1 (by rfl) ⟨607268, by rfl⟩ : syracuseStep 809691 = 1214537) B1214537
theorem B809767 : Blo 806344 809767 := bstep (se 1 (by rfl) ⟨607325, by rfl⟩ : syracuseStep 809767 = 1214651) B1214651
theorem B809807 : Blo 806344 809807 := bstep (se 1 (by rfl) ⟨607355, by rfl⟩ : syracuseStep 809807 = 1214711) B1214711
theorem B809823 : Blo 806344 809823 := bstep (se 1 (by rfl) ⟨607367, by rfl⟩ : syracuseStep 809823 = 1214735) B1214735
theorem B809851 : Blo 806344 809851 := bstep (se 1 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 809851 = 1214777) B1214777
theorem B809903 : Blo 806344 809903 := bstep (se 1 (by rfl) ⟨607427, by rfl⟩ : syracuseStep 809903 = 1214855) B1214855
theorem B809927 : Blo 806344 809927 := bstep (se 1 (by rfl) ⟨607445, by rfl⟩ : syracuseStep 809927 = 1214891) B1214891
theorem B809947 : Blo 806344 809947 := bstep (se 1 (by rfl) ⟨607460, by rfl⟩ : syracuseStep 809947 = 1214921) B1214921
theorem B1367003 : Blo 806344 1367003 := bstep (se 1 (by rfl) ⟨1025252, by rfl⟩ : syracuseStep 1367003 = 2050505) B2050505
theorem B810023 : Blo 806344 810023 := bstep (se 1 (by rfl) ⟨607517, by rfl⟩ : syracuseStep 810023 = 1215035) B1215035
theorem B810063 : Blo 806344 810063 := bstep (se 1 (by rfl) ⟨607547, by rfl⟩ : syracuseStep 810063 = 1215095) B1215095
theorem B810079 : Blo 806344 810079 := bstep (se 1 (by rfl) ⟨607559, by rfl⟩ : syracuseStep 810079 = 1215119) B1215119
theorem B810107 : Blo 806344 810107 := bstep (se 1 (by rfl) ⟨607580, by rfl⟩ : syracuseStep 810107 = 1215161) B1215161
theorem B810159 : Blo 806344 810159 := bstep (se 1 (by rfl) ⟨607619, by rfl⟩ : syracuseStep 810159 = 1215239) B1215239
theorem B810183 : Blo 806344 810183 := bstep (se 1 (by rfl) ⟨607637, by rfl⟩ : syracuseStep 810183 = 1215275) B1215275
theorem B1367239 : Blo 806344 1367239 := bstep (se 1 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 1367239 = 2050859) B2050859
theorem B810203 : Blo 806344 810203 := bstep (se 1 (by rfl) ⟨607652, by rfl⟩ : syracuseStep 810203 = 1215305) B1215305
theorem B810279 : Blo 806344 810279 := bstep (se 1 (by rfl) ⟨607709, by rfl⟩ : syracuseStep 810279 = 1215419) B1215419
theorem B810319 : Blo 806344 810319 := bstep (se 1 (by rfl) ⟨607739, by rfl⟩ : syracuseStep 810319 = 1215479) B1215479
theorem B810335 : Blo 806344 810335 := bstep (se 1 (by rfl) ⟨607751, by rfl⟩ : syracuseStep 810335 = 1215503) B1215503
theorem B1367401 : Blo 806344 1367401 := bstep (se 2 (by rfl) ⟨512775, by rfl⟩ : syracuseStep 1367401 = 1025551) B1025551
theorem B3890605 : Blo 806344 3890605 := bstep (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) B1458977
theorem B4087259 : Blo 806344 4087259 := bstep (se 1 (by rfl) ⟨3065444, by rfl⟩ : syracuseStep 4087259 = 6130889) B6130889
theorem B908923 : Blo 806344 908923 := bstep (se 1 (by rfl) ⟨681692, by rfl⟩ : syracuseStep 908923 = 1363385) B1363385
theorem B3071627 : Blo 806344 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B2186941 : Blo 806344 2186941 := bstep (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) B820103
theorem B2186963 : Blo 806344 2186963 := bstep (se 1 (by rfl) ⟨1640222, by rfl⟩ : syracuseStep 2186963 = 3280445) B3280445
theorem B4087745 : Blo 806344 4087745 := bstep (se 2 (by rfl) ⟨1532904, by rfl⟩ : syracuseStep 4087745 = 3065809) B3065809
theorem B26173469 : Blo 806344 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B909391 : Blo 806344 909391 := bstep (se 1 (by rfl) ⟨682043, by rfl⟩ : syracuseStep 909391 = 1364087) B1364087
theorem B6152273 : Blo 806344 6152273 := bstep (se 2 (by rfl) ⟨2307102, by rfl⟩ : syracuseStep 6152273 = 4614205) B4614205
theorem B1532267 : Blo 806344 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B909787 : Blo 806344 909787 := bstep (se 1 (by rfl) ⟨682340, by rfl⟩ : syracuseStep 909787 = 1364681) B1364681
theorem B1729063 : Blo 806344 1729063 := bstep (se 1 (by rfl) ⟨1296797, by rfl⟩ : syracuseStep 1729063 = 2593595) B2593595
theorem B1532495 : Blo 806344 1532495 := bstep (se 1 (by rfl) ⟨1149371, by rfl⟩ : syracuseStep 1532495 = 2298743) B2298743
theorem B3072887 : Blo 806344 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B910255 : Blo 806344 910255 := bstep (se 1 (by rfl) ⟨682691, by rfl⟩ : syracuseStep 910255 = 1365383) B1365383
theorem B1532935 : Blo 806344 1532935 := bstep (se 1 (by rfl) ⟨1149701, by rfl⟩ : syracuseStep 1532935 = 2299403) B2299403
theorem B13132867 : Blo 806344 13132867 := bstep (se 1 (by rfl) ⟨9849650, by rfl⟩ : syracuseStep 13132867 = 19699301) B19699301
theorem B4613273 : Blo 806344 4613273 := bstep (se 2 (by rfl) ⟨1729977, by rfl⟩ : syracuseStep 4613273 = 3459955) B3459955
theorem B910687 : Blo 806344 910687 := bstep (se 1 (by rfl) ⟨683015, by rfl⟩ : syracuseStep 910687 = 1366031) B1366031
theorem B11986321 : Blo 806344 11986321 := bstep (se 2 (by rfl) ⟨4494870, by rfl⟩ : syracuseStep 11986321 = 8989741) B8989741
theorem B911047 : Blo 806344 911047 := bstep (se 1 (by rfl) ⟨683285, by rfl⟩ : syracuseStep 911047 = 1366571) B1366571
theorem B4155095 : Blo 806344 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B3073859 : Blo 806344 3073859 := bstep (se 1 (by rfl) ⟨2305394, by rfl⟩ : syracuseStep 3073859 = 4610789) B4610789
theorem B2910113 : Blo 806344 2910113 := bstep (se 2 (by rfl) ⟨1091292, by rfl⟩ : syracuseStep 2910113 = 2182585) B2182585
theorem B1730567 : Blo 806344 1730567 := bstep (se 1 (by rfl) ⟨1297925, by rfl⟩ : syracuseStep 1730567 = 2595851) B2595851
theorem B1533991 : Blo 806344 1533991 := bstep (se 1 (by rfl) ⟨1150493, by rfl⟩ : syracuseStep 1533991 = 2300987) B2300987
theorem B4090013 : Blo 806344 4090013 := bstep (se 3 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 4090013 = 1533755) B1533755
theorem B2910701 : Blo 806344 2910701 := bstep (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) B1091513
theorem B3500603 : Blo 806344 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B2911049 : Blo 806344 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B2583895 : Blo 806344 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B4418959 : Blo 806344 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B4091309 : Blo 806344 4091309 := bstep (se 3 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 4091309 = 1534241) B1534241
theorem B2584009 : Blo 806344 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B3075529 : Blo 806344 3075529 := bstep (se 2 (by rfl) ⟨1153323, by rfl⟩ : syracuseStep 3075529 = 2306647) B2306647
theorem B1535699 : Blo 806344 1535699 := bstep (se 1 (by rfl) ⟨1151774, by rfl⟩ : syracuseStep 1535699 = 2303549) B2303549
theorem B3075833 : Blo 806344 3075833 := bstep (se 2 (by rfl) ⟨1153437, by rfl⟩ : syracuseStep 3075833 = 2306875) B2306875
theorem B1535851 : Blo 806344 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B3076001 : Blo 806344 3076001 := bstep (se 2 (by rfl) ⟨1153500, by rfl⟩ : syracuseStep 3076001 = 2307001) B2307001
theorem B3076015 : Blo 806344 3076015 := bstep (se 1 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 3076015 = 4614023) B4614023
theorem B1536079 : Blo 806344 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B2912777 : Blo 806344 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B10351313 : Blo 806344 10351313 := bstep (se 2 (by rfl) ⟨3881742, by rfl⟩ : syracuseStep 10351313 = 7763485) B7763485
theorem B3928787 : Blo 806344 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B4092929 : Blo 806344 4092929 := bstep (se 2 (by rfl) ⟨1534848, by rfl⟩ : syracuseStep 4092929 = 3069697) B3069697
theorem B5174351 : Blo 806344 5174351 := bstep (se 1 (by rfl) ⟨3880763, by rfl⟩ : syracuseStep 5174351 = 7761527) B7761527
theorem B2585753 : Blo 806344 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B1209593 : Blo 806344 1209593 := bstep (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) B907195
theorem B1209695 : Blo 806344 1209695 := bstep (se 1 (by rfl) ⟨907271, by rfl⟩ : syracuseStep 1209695 = 1814543) B1814543
theorem B1209707 : Blo 806344 1209707 := bstep (se 1 (by rfl) ⟨907280, by rfl⟩ : syracuseStep 1209707 = 1814561) B1814561
theorem B1209935 : Blo 806344 1209935 := bstep (se 1 (by rfl) ⟨907451, by rfl⟩ : syracuseStep 1209935 = 1814903) B1814903
theorem B1210055 : Blo 806344 1210055 := bstep (se 1 (by rfl) ⟨907541, by rfl⟩ : syracuseStep 1210055 = 1815083) B1815083
theorem B16578341 : Blo 806344 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B4093739 : Blo 806344 4093739 := bstep (se 1 (by rfl) ⟨3070304, by rfl⟩ : syracuseStep 4093739 = 6140609) B6140609
theorem B1210217 : Blo 806344 1210217 := bstep (se 2 (by rfl) ⟨453831, by rfl⟩ : syracuseStep 1210217 = 907663) B907663
theorem B1210295 : Blo 806344 1210295 := bstep (se 1 (by rfl) ⟨907721, by rfl⟩ : syracuseStep 1210295 = 1815443) B1815443
theorem B1210331 : Blo 806344 1210331 := bstep (se 1 (by rfl) ⟨907748, by rfl⟩ : syracuseStep 1210331 = 1815497) B1815497
theorem B7764329 : Blo 806344 7764329 := bstep (se 2 (by rfl) ⟨2911623, by rfl⟩ : syracuseStep 7764329 = 5823247) B5823247
theorem B1210799 : Blo 806344 1210799 := bstep (se 1 (by rfl) ⟨908099, by rfl⟩ : syracuseStep 1210799 = 1816199) B1816199
theorem B1210889 : Blo 806344 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B1210919 : Blo 806344 1210919 := bstep (se 1 (by rfl) ⟨908189, by rfl⟩ : syracuseStep 1210919 = 1816379) B1816379
theorem B1211003 : Blo 806344 1211003 := bstep (se 1 (by rfl) ⟨908252, by rfl⟩ : syracuseStep 1211003 = 1816505) B1816505
theorem B1211129 : Blo 806344 1211129 := bstep (se 2 (by rfl) ⟨454173, by rfl⟩ : syracuseStep 1211129 = 908347) B908347
theorem B1211231 : Blo 806344 1211231 := bstep (se 1 (by rfl) ⟨908423, by rfl⟩ : syracuseStep 1211231 = 1816847) B1816847
theorem B1211243 : Blo 806344 1211243 := bstep (se 1 (by rfl) ⟨908432, by rfl⟩ : syracuseStep 1211243 = 1816865) B1816865
theorem B1211471 : Blo 806344 1211471 := bstep (se 1 (by rfl) ⟨908603, by rfl⟩ : syracuseStep 1211471 = 1817207) B1817207
theorem B2587727 : Blo 806344 2587727 := bstep (se 1 (by rfl) ⟨1940795, by rfl⟩ : syracuseStep 2587727 = 3881591) B3881591
theorem B1211591 : Blo 806344 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B1211753 : Blo 806344 1211753 := bstep (se 2 (by rfl) ⟨454407, by rfl⟩ : syracuseStep 1211753 = 908815) B908815
theorem B1211831 : Blo 806344 1211831 := bstep (se 1 (by rfl) ⟨908873, by rfl⟩ : syracuseStep 1211831 = 1817747) B1817747
theorem B1211867 : Blo 806344 1211867 := bstep (se 1 (by rfl) ⟨908900, by rfl⟩ : syracuseStep 1211867 = 1817801) B1817801
theorem B1998361 : Blo 806344 1998361 := bstep (se 2 (by rfl) ⟨749385, by rfl⟩ : syracuseStep 1998361 = 1498771) B1498771
theorem B1212335 : Blo 806344 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B5177297 : Blo 806344 5177297 := bstep (se 2 (by rfl) ⟨1941486, by rfl⟩ : syracuseStep 5177297 = 3882973) B3882973
theorem B69795917 : Blo 806344 69795917 := bstep (se 3 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 69795917 = 26173469) B26173469
theorem B1212521 : Blo 806344 1212521 := bstep (se 2 (by rfl) ⟨454695, by rfl⟩ : syracuseStep 1212521 = 909391) B909391
theorem B8749403 : Blo 806344 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B1212839 : Blo 806344 1212839 := bstep (se 1 (by rfl) ⟨909629, by rfl⟩ : syracuseStep 1212839 = 1819259) B1819259
theorem B1212923 : Blo 806344 1212923 := bstep (se 1 (by rfl) ⟨909692, by rfl⟩ : syracuseStep 1212923 = 1819385) B1819385
theorem B1213049 : Blo 806344 1213049 := bstep (se 2 (by rfl) ⟨454893, by rfl⟩ : syracuseStep 1213049 = 909787) B909787
theorem B1213103 : Blo 806344 1213103 := bstep (se 1 (by rfl) ⟨909827, by rfl⟩ : syracuseStep 1213103 = 1819655) B1819655
theorem B2589367 : Blo 806344 2589367 := bstep (se 1 (by rfl) ⟨1942025, by rfl⟩ : syracuseStep 2589367 = 3884051) B3884051
theorem B1213151 : Blo 806344 1213151 := bstep (se 1 (by rfl) ⟨909863, by rfl⟩ : syracuseStep 1213151 = 1819727) B1819727
theorem B1213415 : Blo 806344 1213415 := bstep (se 1 (by rfl) ⟨910061, by rfl⟩ : syracuseStep 1213415 = 1820123) B1820123
theorem B1213673 : Blo 806344 1213673 := bstep (se 2 (by rfl) ⟨455127, by rfl⟩ : syracuseStep 1213673 = 910255) B910255
theorem B3114233 : Blo 806344 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B1213727 : Blo 806344 1213727 := bstep (se 1 (by rfl) ⟨910295, by rfl⟩ : syracuseStep 1213727 = 1820591) B1820591
theorem B6128945 : Blo 806344 6128945 := bstep (se 2 (by rfl) ⟨2298354, by rfl⟩ : syracuseStep 6128945 = 4596709) B4596709
theorem B2459069 : Blo 806344 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B1213895 : Blo 806344 1213895 := bstep (se 1 (by rfl) ⟨910421, by rfl⟩ : syracuseStep 1213895 = 1820843) B1820843
theorem B5178937 : Blo 806344 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B2721437 : Blo 806344 2721437 := bstep (se 3 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 2721437 = 1020539) B1020539
theorem B35030819 : Blo 806344 35030819 := bstep (se 1 (by rfl) ⟨26273114, by rfl⟩ : syracuseStep 35030819 = 52546229) B52546229
theorem B1214249 : Blo 806344 1214249 := bstep (se 2 (by rfl) ⟨455343, by rfl⟩ : syracuseStep 1214249 = 910687) B910687
theorem B18876203 : Blo 806344 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B1214255 : Blo 806344 1214255 := bstep (se 1 (by rfl) ⟨910691, by rfl⟩ : syracuseStep 1214255 = 1821383) B1821383
theorem B7997251 : Blo 806344 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B2721977 : Blo 806344 2721977 := bstep (se 2 (by rfl) ⟨1020741, by rfl⟩ : syracuseStep 2721977 = 2041483) B2041483
theorem B6129917 : Blo 806344 6129917 := bstep (se 3 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 6129917 = 2298719) B2298719
theorem B1214729 : Blo 806344 1214729 := bstep (se 2 (by rfl) ⟨455523, by rfl⟩ : syracuseStep 1214729 = 911047) B911047
theorem B1214831 : Blo 806344 1214831 := bstep (se 1 (by rfl) ⟨911123, by rfl⟩ : syracuseStep 1214831 = 1822247) B1822247
theorem B4917647 : Blo 806344 4917647 := bstep (se 1 (by rfl) ⟨3688235, by rfl⟩ : syracuseStep 4917647 = 7376471) B7376471
theorem B15534503 : Blo 806344 15534503 := bstep (se 1 (by rfl) ⟨11650877, by rfl⟩ : syracuseStep 15534503 = 23301755) B23301755
theorem B9341351 : Blo 806344 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B4098599 : Blo 806344 4098599 := bstep (se 1 (by rfl) ⟨3073949, by rfl⟩ : syracuseStep 4098599 = 6147899) B6147899
theorem B1215047 : Blo 806344 1215047 := bstep (se 1 (by rfl) ⟨911285, by rfl⟩ : syracuseStep 1215047 = 1822571) B1822571
theorem B1215083 : Blo 806344 1215083 := bstep (se 1 (by rfl) ⟨911312, by rfl⟩ : syracuseStep 1215083 = 1822625) B1822625
theorem B8751827 : Blo 806344 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B3279635 : Blo 806344 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B1215311 : Blo 806344 1215311 := bstep (se 1 (by rfl) ⟨911483, by rfl⟩ : syracuseStep 1215311 = 1822967) B1822967
theorem B2493659 : Blo 806344 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B5835995 : Blo 806344 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B2723489 : Blo 806344 2723489 := bstep (se 2 (by rfl) ⟨1021308, by rfl⟩ : syracuseStep 2723489 = 2042617) B2042617
theorem B4427531 : Blo 806344 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B5836859 : Blo 806344 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B2298287 : Blo 806344 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B3445193 : Blo 806344 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B2724353 : Blo 806344 2724353 := bstep (se 2 (by rfl) ⟨1021632, by rfl⟩ : syracuseStep 2724353 = 2043265) B2043265
theorem B11080253 : Blo 806344 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B3445345 : Blo 806344 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B4100705 : Blo 806344 4100705 := bstep (se 2 (by rfl) ⟨1537764, by rfl⟩ : syracuseStep 4100705 = 3075529) B3075529
theorem B6919121 : Blo 806344 6919121 := bstep (se 2 (by rfl) ⟨2594670, by rfl⟩ : syracuseStep 6919121 = 5189341) B5189341
theorem B2724839 : Blo 806344 2724839 := bstep (se 1 (by rfl) ⟨2043629, by rfl⟩ : syracuseStep 2724839 = 4087259) B4087259
theorem B4101353 : Blo 806344 4101353 := bstep (se 2 (by rfl) ⟨1538007, by rfl⟩ : syracuseStep 4101353 = 3076015) B3076015
theorem B8754425 : Blo 806344 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B2299175 : Blo 806344 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B2725163 : Blo 806344 2725163 := bstep (se 1 (by rfl) ⟨2043872, by rfl⟩ : syracuseStep 2725163 = 4087745) B4087745
theorem B4101515 : Blo 806344 4101515 := bstep (se 1 (by rfl) ⟨3076136, by rfl⟩ : syracuseStep 4101515 = 6152273) B6152273
theorem B14718509 : Blo 806344 14718509 := bstep (se 3 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 14718509 = 5519441) B5519441
theorem B2725433 : Blo 806344 2725433 := bstep (se 2 (by rfl) ⟨1022037, by rfl⟩ : syracuseStep 2725433 = 2044075) B2044075
theorem B1021511 : Blo 806344 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B1021663 : Blo 806344 1021663 := bstep (se 1 (by rfl) ⟨766247, by rfl⟩ : syracuseStep 1021663 = 1532495) B1532495
theorem B1940075 : Blo 806344 1940075 := bstep (se 1 (by rfl) ⟨1455056, by rfl⟩ : syracuseStep 1940075 = 2910113) B2910113
theorem B1153711 : Blo 806344 1153711 := bstep (se 1 (by rfl) ⟨865283, by rfl⟩ : syracuseStep 1153711 = 1730567) B1730567
theorem B2726675 : Blo 806344 2726675 := bstep (se 1 (by rfl) ⟨2045006, by rfl⟩ : syracuseStep 2726675 = 4090013) B4090013
theorem B2300815 : Blo 806344 2300815 := bstep (se 1 (by rfl) ⟨1725611, by rfl⟩ : syracuseStep 2300815 = 3451223) B3451223
theorem B2333735 : Blo 806344 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B1940699 : Blo 806344 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B4791619 : Blo 806344 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B5905979 : Blo 806344 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B3284563 : Blo 806344 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B2727539 : Blo 806344 2727539 := bstep (se 1 (by rfl) ⟨2045654, by rfl⟩ : syracuseStep 2727539 = 4091309) B4091309
theorem B1941353 : Blo 806344 1941353 := bstep (se 2 (by rfl) ⟨728007, by rfl⟩ : syracuseStep 1941353 = 1456015) B1456015
theorem B2727809 : Blo 806344 2727809 := bstep (se 2 (by rfl) ⟨1022928, by rfl⟩ : syracuseStep 2727809 = 2045857) B2045857
theorem B2662301 : Blo 806344 2662301 := bstep (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) B998363
theorem B10657925 : Blo 806344 10657925 := bstep (se 4 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 10657925 = 1998361) B1998361
theorem B1941851 : Blo 806344 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B2728619 : Blo 806344 2728619 := bstep (se 1 (by rfl) ⟨2046464, by rfl⟩ : syracuseStep 2728619 = 4092929) B4092929
theorem B3449567 : Blo 806344 3449567 := bstep (se 1 (by rfl) ⟨2587175, by rfl⟩ : syracuseStep 3449567 = 5174351) B5174351
theorem B4432985 : Blo 806344 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B11052227 : Blo 806344 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B2729159 : Blo 806344 2729159 := bstep (se 1 (by rfl) ⟨2046869, by rfl⟩ : syracuseStep 2729159 = 4093739) B4093739
theorem B19900241 : Blo 806344 19900241 := bstep (se 2 (by rfl) ⟨7462590, by rfl⟩ : syracuseStep 19900241 = 14925181) B14925181
theorem B5187473 : Blo 806344 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B2041807 : Blo 806344 2041807 := bstep (se 1 (by rfl) ⟨1531355, by rfl⟩ : syracuseStep 2041807 = 3062711) B3062711
theorem B13117625 : Blo 806344 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B7973057 : Blo 806344 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B2304575 : Blo 806344 2304575 := bstep (se 1 (by rfl) ⟨1728431, by rfl⟩ : syracuseStep 2304575 = 3456863) B3456863
theorem B3451531 : Blo 806344 3451531 := bstep (se 1 (by rfl) ⟨2588648, by rfl⟩ : syracuseStep 3451531 = 5177297) B5177297
theorem B2730671 : Blo 806344 2730671 := bstep (se 1 (by rfl) ⟨2048003, by rfl⟩ : syracuseStep 2730671 = 4096007) B4096007
theorem B31501001 : Blo 806344 31501001 := bstep (se 2 (by rfl) ⟨11812875, by rfl⟩ : syracuseStep 31501001 = 23625751) B23625751
theorem B35367815 : Blo 806344 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B2042779 : Blo 806344 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B4139947 : Blo 806344 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B2730995 : Blo 806344 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B2239721 : Blo 806344 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B2305417 : Blo 806344 2305417 := bstep (se 2 (by rfl) ⟨864531, by rfl⟩ : syracuseStep 2305417 = 1729063) B1729063
theorem B2731535 : Blo 806344 2731535 := bstep (se 1 (by rfl) ⟨2048651, by rfl⟩ : syracuseStep 2731535 = 4097303) B4097303
theorem B1552033 : Blo 806344 1552033 := bstep (se 2 (by rfl) ⟨582012, by rfl⟩ : syracuseStep 1552033 = 1164025) B1164025
theorem B1814327 : Blo 806344 1814327 := bstep (se 1 (by rfl) ⟨1360745, by rfl⟩ : syracuseStep 1814327 = 2721491) B2721491
theorem B8302445 : Blo 806344 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B2043913 : Blo 806344 2043913 := bstep (se 2 (by rfl) ⟨766467, by rfl⟩ : syracuseStep 2043913 = 1532935) B1532935
theorem B17510489 : Blo 806344 17510489 := bstep (se 2 (by rfl) ⟨6566433, by rfl⟩ : syracuseStep 17510489 = 13132867) B13132867
theorem B1814633 : Blo 806344 1814633 := bstep (se 2 (by rfl) ⟨680487, by rfl⟩ : syracuseStep 1814633 = 1360975) B1360975
theorem B3453137 : Blo 806344 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B8761601 : Blo 806344 8761601 := bstep (se 2 (by rfl) ⟨3285600, by rfl⟩ : syracuseStep 8761601 = 6571201) B6571201
theorem B14954827 : Blo 806344 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B1094087 : Blo 806344 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B1946081 : Blo 806344 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B2732615 : Blo 806344 2732615 := bstep (se 1 (by rfl) ⟨2049461, by rfl⟩ : syracuseStep 2732615 = 4098923) B4098923
theorem B1815119 : Blo 806344 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B1815263 : Blo 806344 1815263 := bstep (se 1 (by rfl) ⟨1361447, by rfl⟩ : syracuseStep 1815263 = 2722895) B2722895
theorem B15545195 : Blo 806344 15545195 := bstep (se 1 (by rfl) ⟨11658896, by rfl⟩ : syracuseStep 15545195 = 23317793) B23317793
theorem B1815515 : Blo 806344 1815515 := bstep (se 1 (by rfl) ⟨1361636, by rfl⟩ : syracuseStep 1815515 = 2723273) B2723273
theorem B3879899 : Blo 806344 3879899 := bstep (se 1 (by rfl) ⟨2909924, by rfl⟩ : syracuseStep 3879899 = 5819849) B5819849
theorem B2307035 : Blo 806344 2307035 := bstep (se 1 (by rfl) ⟨1730276, by rfl⟩ : syracuseStep 2307035 = 3460553) B3460553
theorem B2733047 : Blo 806344 2733047 := bstep (se 1 (by rfl) ⟨2049785, by rfl⟩ : syracuseStep 2733047 = 4099571) B4099571
theorem B1815695 : Blo 806344 1815695 := bstep (se 1 (by rfl) ⟨1361771, by rfl⟩ : syracuseStep 1815695 = 2723543) B2723543
theorem B1815785 : Blo 806344 1815785 := bstep (se 2 (by rfl) ⟨680919, by rfl⟩ : syracuseStep 1815785 = 1361839) B1361839
theorem B1815839 : Blo 806344 1815839 := bstep (se 1 (by rfl) ⟨1361879, by rfl⟩ : syracuseStep 1815839 = 2723759) B2723759
theorem B2045321 : Blo 806344 2045321 := bstep (se 2 (by rfl) ⟨766995, by rfl⟩ : syracuseStep 2045321 = 1533991) B1533991
theorem B2307467 : Blo 806344 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B9811361 : Blo 806344 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B2045371 : Blo 806344 2045371 := bstep (se 1 (by rfl) ⟨1534028, by rfl⟩ : syracuseStep 2045371 = 3068057) B3068057
theorem B2045675 : Blo 806344 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B1816361 : Blo 806344 1816361 := bstep (se 2 (by rfl) ⟨681135, by rfl⟩ : syracuseStep 1816361 = 1362271) B1362271
theorem B6993719 : Blo 806344 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B2733911 : Blo 806344 2733911 := bstep (se 1 (by rfl) ⟨2050433, by rfl⟩ : syracuseStep 2733911 = 4100867) B4100867
theorem B4994903 : Blo 806344 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B2046647 : Blo 806344 2046647 := bstep (se 1 (by rfl) ⟨1534985, by rfl⟩ : syracuseStep 2046647 = 3069971) B3069971
theorem B1817423 : Blo 806344 1817423 := bstep (se 1 (by rfl) ⟨1363067, by rfl⟩ : syracuseStep 1817423 = 2726135) B2726135
theorem B1817639 : Blo 806344 1817639 := bstep (se 1 (by rfl) ⟨1363229, by rfl⟩ : syracuseStep 1817639 = 2726459) B2726459
theorem B1817819 : Blo 806344 1817819 := bstep (se 1 (by rfl) ⟨1363364, by rfl⟩ : syracuseStep 1817819 = 2726729) B2726729
theorem B1293607 : Blo 806344 1293607 := bstep (se 1 (by rfl) ⟨970205, by rfl⟩ : syracuseStep 1293607 = 1940411) B1940411
theorem B1818017 : Blo 806344 1818017 := bstep (se 2 (by rfl) ⟨681756, by rfl⟩ : syracuseStep 1818017 = 1363513) B1363513
theorem B3063379 : Blo 806344 3063379 := bstep (se 1 (by rfl) ⟨2297534, by rfl⟩ : syracuseStep 3063379 = 4595069) B4595069
theorem B2047751 : Blo 806344 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B1457975 : Blo 806344 1457975 := bstep (se 1 (by rfl) ⟨1093481, by rfl⟩ : syracuseStep 1457975 = 2186963) B2186963
theorem B2047801 : Blo 806344 2047801 := bstep (se 2 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 2047801 = 1535851) B1535851
theorem B1818575 : Blo 806344 1818575 := bstep (se 1 (by rfl) ⟨1363931, by rfl⟩ : syracuseStep 1818575 = 2727863) B2727863
theorem B13090835 : Blo 806344 13090835 := bstep (se 1 (by rfl) ⟨9818126, by rfl⟩ : syracuseStep 13090835 = 19636253) B19636253
theorem B2048105 : Blo 806344 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B1818953 : Blo 806344 1818953 := bstep (se 2 (by rfl) ⟨682107, by rfl⟩ : syracuseStep 1818953 = 1364215) B1364215
theorem B1818971 : Blo 806344 1818971 := bstep (se 1 (by rfl) ⟨1364228, by rfl⟩ : syracuseStep 1818971 = 2728457) B2728457
theorem B2048591 : Blo 806344 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B1295023 : Blo 806344 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B26231597 : Blo 806344 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B3064655 : Blo 806344 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B1819547 : Blo 806344 1819547 := bstep (se 1 (by rfl) ⟨1364660, by rfl⟩ : syracuseStep 1819547 = 2729321) B2729321
theorem B1754075 : Blo 806344 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B3064823 : Blo 806344 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B1819745 : Blo 806344 1819745 := bstep (se 2 (by rfl) ⟨682404, by rfl⟩ : syracuseStep 1819745 = 1364809) B1364809
theorem B2049239 : Blo 806344 2049239 := bstep (se 1 (by rfl) ⟨1536929, by rfl⟩ : syracuseStep 2049239 = 3073859) B3073859
theorem B1361191 : Blo 806344 1361191 := bstep (se 1 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 1361191 = 2041787) B2041787
theorem B1819943 : Blo 806344 1819943 := bstep (se 1 (by rfl) ⟨1364957, by rfl⟩ : syracuseStep 1819943 = 2729915) B2729915
theorem B6145469 : Blo 806344 6145469 := bstep (se 3 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 6145469 = 2304551) B2304551
theorem B1820321 : Blo 806344 1820321 := bstep (se 2 (by rfl) ⟨682620, by rfl⟩ : syracuseStep 1820321 = 1365241) B1365241
theorem B1361711 : Blo 806344 1361711 := bstep (se 1 (by rfl) ⟨1021283, by rfl⟩ : syracuseStep 1361711 = 2042567) B2042567
theorem B2213689 : Blo 806344 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B6539089 : Blo 806344 6539089 := bstep (se 2 (by rfl) ⟨2452158, by rfl⟩ : syracuseStep 6539089 = 4904317) B4904317
theorem B1820681 : Blo 806344 1820681 := bstep (se 2 (by rfl) ⟨682755, by rfl⟩ : syracuseStep 1820681 = 1365511) B1365511
theorem B1034587 : Blo 806344 1034587 := bstep (se 1 (by rfl) ⟨775940, by rfl⟩ : syracuseStep 1034587 = 1551881) B1551881
theorem B1821095 : Blo 806344 1821095 := bstep (se 1 (by rfl) ⟨1365821, by rfl⟩ : syracuseStep 1821095 = 2731643) B2731643
theorem B3066295 : Blo 806344 3066295 := bstep (se 1 (by rfl) ⟨2299721, by rfl⟩ : syracuseStep 3066295 = 4599443) B4599443
theorem B2050555 : Blo 806344 2050555 := bstep (se 1 (by rfl) ⟨1537916, by rfl⟩ : syracuseStep 2050555 = 3075833) B3075833
theorem B1821203 : Blo 806344 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B1821257 : Blo 806344 1821257 := bstep (se 2 (by rfl) ⟨682971, by rfl⟩ : syracuseStep 1821257 = 1365943) B1365943
theorem B969311 : Blo 806344 969311 := bstep (se 1 (by rfl) ⟨726983, by rfl⟩ : syracuseStep 969311 = 1453967) B1453967
theorem B2050667 : Blo 806344 2050667 := bstep (se 1 (by rfl) ⟨1538000, by rfl⟩ : syracuseStep 2050667 = 3076001) B3076001
theorem B6998807 : Blo 806344 6998807 := bstep (se 1 (by rfl) ⟨5249105, by rfl⟩ : syracuseStep 6998807 = 10498211) B10498211
theorem B4377469 : Blo 806344 4377469 := bstep (se 3 (by rfl) ⟨820775, by rfl⟩ : syracuseStep 4377469 = 1641551) B1641551
theorem B3066767 : Blo 806344 3066767 := bstep (se 1 (by rfl) ⟨2300075, by rfl⟩ : syracuseStep 3066767 = 4600151) B4600151
theorem B1362919 : Blo 806344 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B1821671 : Blo 806344 1821671 := bstep (se 1 (by rfl) ⟨1366253, by rfl⟩ : syracuseStep 1821671 = 2732507) B2732507
theorem B6900875 : Blo 806344 6900875 := bstep (se 1 (by rfl) ⟨5175656, by rfl⟩ : syracuseStep 6900875 = 10351313) B10351313
theorem B8310113 : Blo 806344 8310113 := bstep (se 2 (by rfl) ⟨3116292, by rfl⟩ : syracuseStep 8310113 = 6232585) B6232585
theorem B1822049 : Blo 806344 1822049 := bstep (se 2 (by rfl) ⟨683268, by rfl⟩ : syracuseStep 1822049 = 1366537) B1366537
theorem B7785857 : Blo 806344 7785857 := bstep (se 2 (by rfl) ⟨2919696, by rfl⟩ : syracuseStep 7785857 = 5839393) B5839393
theorem B1723835 : Blo 806344 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B1822139 : Blo 806344 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B806395 : Blo 806344 806395 := bstep (se 1 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 806395 = 1209593) B1209593
theorem B4083209 : Blo 806344 4083209 := bstep (se 2 (by rfl) ⟨1531203, by rfl⟩ : syracuseStep 4083209 = 3062407) B3062407
theorem B1822265 : Blo 806344 1822265 := bstep (se 2 (by rfl) ⟨683349, by rfl⟩ : syracuseStep 1822265 = 1366699) B1366699
theorem B806463 : Blo 806344 806463 := bstep (se 1 (by rfl) ⟨604847, by rfl⟩ : syracuseStep 806463 = 1209695) B1209695
theorem B806471 : Blo 806344 806471 := bstep (se 1 (by rfl) ⟨604853, by rfl⟩ : syracuseStep 806471 = 1209707) B1209707
theorem B806623 : Blo 806344 806623 := bstep (se 1 (by rfl) ⟨604967, by rfl⟩ : syracuseStep 806623 = 1209935) B1209935
theorem B10342187 : Blo 806344 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B806703 : Blo 806344 806703 := bstep (se 1 (by rfl) ⟨605027, by rfl⟩ : syracuseStep 806703 = 1210055) B1210055
theorem B806811 : Blo 806344 806811 := bstep (se 1 (by rfl) ⟨605108, by rfl⟩ : syracuseStep 806811 = 1210217) B1210217
theorem B35508131 : Blo 806344 35508131 := bstep (se 1 (by rfl) ⟨26631098, by rfl⟩ : syracuseStep 35508131 = 53262197) B53262197
theorem B806863 : Blo 806344 806863 := bstep (se 1 (by rfl) ⟨605147, by rfl⟩ : syracuseStep 806863 = 1210295) B1210295
theorem B806887 : Blo 806344 806887 := bstep (se 1 (by rfl) ⟨605165, by rfl⟩ : syracuseStep 806887 = 1210331) B1210331
theorem B9818171 : Blo 806344 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B1822931 : Blo 806344 1822931 := bstep (se 1 (by rfl) ⟨1367198, by rfl⟩ : syracuseStep 1822931 = 2734397) B2734397
theorem B1822985 : Blo 806344 1822985 := bstep (se 2 (by rfl) ⟨683619, by rfl⟩ : syracuseStep 1822985 = 1367239) B1367239
theorem B807199 : Blo 806344 807199 := bstep (se 1 (by rfl) ⟨605399, by rfl⟩ : syracuseStep 807199 = 1210799) B1210799
theorem B807259 : Blo 806344 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B807279 : Blo 806344 807279 := bstep (se 1 (by rfl) ⟨605459, by rfl⟩ : syracuseStep 807279 = 1210919) B1210919
theorem B807335 : Blo 806344 807335 := bstep (se 1 (by rfl) ⟨605501, by rfl⟩ : syracuseStep 807335 = 1211003) B1211003
theorem B1823201 : Blo 806344 1823201 := bstep (se 2 (by rfl) ⟨683700, by rfl⟩ : syracuseStep 1823201 = 1367401) B1367401
theorem B807419 : Blo 806344 807419 := bstep (se 1 (by rfl) ⟨605564, by rfl⟩ : syracuseStep 807419 = 1211129) B1211129
theorem B807487 : Blo 806344 807487 := bstep (se 1 (by rfl) ⟨605615, by rfl⟩ : syracuseStep 807487 = 1211231) B1211231
theorem B807495 : Blo 806344 807495 := bstep (se 1 (by rfl) ⟨605621, by rfl⟩ : syracuseStep 807495 = 1211243) B1211243
theorem B3986135 : Blo 806344 3986135 := bstep (se 1 (by rfl) ⟨2989601, by rfl⟩ : syracuseStep 3986135 = 5979203) B5979203
theorem B807647 : Blo 806344 807647 := bstep (se 1 (by rfl) ⟨605735, by rfl⟩ : syracuseStep 807647 = 1211471) B1211471
theorem B1725151 : Blo 806344 1725151 := bstep (se 1 (by rfl) ⟨1293863, by rfl⟩ : syracuseStep 1725151 = 2587727) B2587727
theorem B807727 : Blo 806344 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B807835 : Blo 806344 807835 := bstep (se 1 (by rfl) ⟨605876, by rfl⟩ : syracuseStep 807835 = 1211753) B1211753
theorem B807887 : Blo 806344 807887 := bstep (se 1 (by rfl) ⟨605915, by rfl⟩ : syracuseStep 807887 = 1211831) B1211831
theorem B807911 : Blo 806344 807911 := bstep (se 1 (by rfl) ⟨605933, by rfl⟩ : syracuseStep 807911 = 1211867) B1211867
theorem B808223 : Blo 806344 808223 := bstep (se 1 (by rfl) ⟨606167, by rfl⟩ : syracuseStep 808223 = 1212335) B1212335
theorem B808283 : Blo 806344 808283 := bstep (se 1 (by rfl) ⟨606212, by rfl⟩ : syracuseStep 808283 = 1212425) B1212425
theorem B808303 : Blo 806344 808303 := bstep (se 1 (by rfl) ⟨606227, by rfl⟩ : syracuseStep 808303 = 1212455) B1212455
theorem B4085153 : Blo 806344 4085153 := bstep (se 2 (by rfl) ⟨1531932, by rfl⟩ : syracuseStep 4085153 = 3063865) B3063865
theorem B808359 : Blo 806344 808359 := bstep (se 1 (by rfl) ⟨606269, by rfl⟩ : syracuseStep 808359 = 1212539) B1212539
theorem B808443 : Blo 806344 808443 := bstep (se 1 (by rfl) ⟨606332, by rfl⟩ : syracuseStep 808443 = 1212665) B1212665
theorem B9197063 : Blo 806344 9197063 := bstep (se 1 (by rfl) ⟨6897797, by rfl⟩ : syracuseStep 9197063 = 13795595) B13795595
theorem B808511 : Blo 806344 808511 := bstep (se 1 (by rfl) ⟨606383, by rfl⟩ : syracuseStep 808511 = 1212767) B1212767
theorem B808519 : Blo 806344 808519 := bstep (se 1 (by rfl) ⟨606389, by rfl⟩ : syracuseStep 808519 = 1212779) B1212779
theorem B1365599 : Blo 806344 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B808671 : Blo 806344 808671 := bstep (se 1 (by rfl) ⟨606503, by rfl⟩ : syracuseStep 808671 = 1213007) B1213007
theorem B808751 : Blo 806344 808751 := bstep (se 1 (by rfl) ⟨606563, by rfl⟩ : syracuseStep 808751 = 1213127) B1213127
theorem B1365815 : Blo 806344 1365815 := bstep (se 1 (by rfl) ⟨1024361, by rfl⟩ : syracuseStep 1365815 = 2048723) B2048723
theorem B808859 : Blo 806344 808859 := bstep (se 1 (by rfl) ⟨606644, by rfl⟩ : syracuseStep 808859 = 1213289) B1213289
theorem B808911 : Blo 806344 808911 := bstep (se 1 (by rfl) ⟨606683, by rfl⟩ : syracuseStep 808911 = 1213367) B1213367
theorem B808935 : Blo 806344 808935 := bstep (se 1 (by rfl) ⟨606701, by rfl⟩ : syracuseStep 808935 = 1213403) B1213403
theorem B907483 : Blo 806344 907483 := bstep (se 1 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 907483 = 1361225) B1361225
theorem B809247 : Blo 806344 809247 := bstep (se 1 (by rfl) ⟨606935, by rfl⟩ : syracuseStep 809247 = 1213871) B1213871
theorem B809307 : Blo 806344 809307 := bstep (se 1 (by rfl) ⟨606980, by rfl⟩ : syracuseStep 809307 = 1213961) B1213961
theorem B809327 : Blo 806344 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B809383 : Blo 806344 809383 := bstep (se 1 (by rfl) ⟨607037, by rfl⟩ : syracuseStep 809383 = 1214075) B1214075
theorem B1038791 : Blo 806344 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B907771 : Blo 806344 907771 := bstep (se 1 (by rfl) ⟨680828, by rfl⟩ : syracuseStep 907771 = 1361657) B1361657
theorem B809467 : Blo 806344 809467 := bstep (se 1 (by rfl) ⟨607100, by rfl⟩ : syracuseStep 809467 = 1214201) B1214201
theorem B809535 : Blo 806344 809535 := bstep (se 1 (by rfl) ⟨607151, by rfl⟩ : syracuseStep 809535 = 1214303) B1214303
theorem B1366591 : Blo 806344 1366591 := bstep (se 1 (by rfl) ⟨1024943, by rfl⟩ : syracuseStep 1366591 = 2049887) B2049887
theorem B809543 : Blo 806344 809543 := bstep (se 1 (by rfl) ⟨607157, by rfl⟩ : syracuseStep 809543 = 1214315) B1214315
theorem B32365163 : Blo 806344 32365163 := bstep (se 1 (by rfl) ⟨24273872, by rfl⟩ : syracuseStep 32365163 = 48547745) B48547745
theorem B907951 : Blo 806344 907951 := bstep (se 1 (by rfl) ⟨680963, by rfl⟩ : syracuseStep 907951 = 1361927) B1361927
theorem B2185903 : Blo 806344 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B809695 : Blo 806344 809695 := bstep (se 1 (by rfl) ⟨607271, by rfl⟩ : syracuseStep 809695 = 1214543) B1214543
theorem B809775 : Blo 806344 809775 := bstep (se 1 (by rfl) ⟨607331, by rfl⟩ : syracuseStep 809775 = 1214663) B1214663
theorem B809883 : Blo 806344 809883 := bstep (se 1 (by rfl) ⟨607412, by rfl⟩ : syracuseStep 809883 = 1214825) B1214825
theorem B9198521 : Blo 806344 9198521 := bstep (se 2 (by rfl) ⟨3449445, by rfl⟩ : syracuseStep 9198521 = 6898891) B6898891
theorem B908239 : Blo 806344 908239 := bstep (se 1 (by rfl) ⟨681179, by rfl⟩ : syracuseStep 908239 = 1362359) B1362359
theorem B809935 : Blo 806344 809935 := bstep (se 1 (by rfl) ⟨607451, by rfl⟩ : syracuseStep 809935 = 1214903) B1214903
theorem B809959 : Blo 806344 809959 := bstep (se 1 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 809959 = 1214939) B1214939
theorem B15981761 : Blo 806344 15981761 := bstep (se 2 (by rfl) ⟨5993160, by rfl⟩ : syracuseStep 15981761 = 11986321) B11986321
theorem B1367273 : Blo 806344 1367273 := bstep (se 2 (by rfl) ⟨512727, by rfl⟩ : syracuseStep 1367273 = 1025455) B1025455
theorem B1367327 : Blo 806344 1367327 := bstep (se 1 (by rfl) ⟨1025495, by rfl⟩ : syracuseStep 1367327 = 2050991) B2050991
theorem B810271 : Blo 806344 810271 := bstep (se 1 (by rfl) ⟨607703, by rfl⟩ : syracuseStep 810271 = 1215407) B1215407
theorem B908635 : Blo 806344 908635 := bstep (se 1 (by rfl) ⟨681476, by rfl⟩ : syracuseStep 908635 = 1362953) B1362953
theorem B810331 : Blo 806344 810331 := bstep (se 1 (by rfl) ⟨607748, by rfl⟩ : syracuseStep 810331 = 1215497) B1215497
theorem B1727867 : Blo 806344 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B908743 : Blo 806344 908743 := bstep (se 1 (by rfl) ⟨681557, by rfl⟩ : syracuseStep 908743 = 1363115) B1363115
theorem B909103 : Blo 806344 909103 := bstep (se 1 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 909103 = 1363655) B1363655
theorem B1531705 : Blo 806344 1531705 := bstep (se 2 (by rfl) ⟨574389, by rfl⟩ : syracuseStep 1531705 = 1148779) B1148779
theorem B909211 : Blo 806344 909211 := bstep (se 1 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 909211 = 1363817) B1363817
theorem B3104669 : Blo 806344 3104669 := bstep (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) B1164251
theorem B1532009 : Blo 806344 1532009 := bstep (se 2 (by rfl) ⟨574503, by rfl⟩ : syracuseStep 1532009 = 1149007) B1149007
theorem B5824631 : Blo 806344 5824631 := bstep (se 1 (by rfl) ⟨4368473, by rfl⟩ : syracuseStep 5824631 = 8736947) B8736947
theorem B909607 : Blo 806344 909607 := bstep (se 1 (by rfl) ⟨682205, by rfl⟩ : syracuseStep 909607 = 1364411) B1364411
theorem B909679 : Blo 806344 909679 := bstep (se 1 (by rfl) ⟨682259, by rfl⟩ : syracuseStep 909679 = 1364519) B1364519
theorem B3072431 : Blo 806344 3072431 := bstep (se 1 (by rfl) ⟨2304323, by rfl⟩ : syracuseStep 3072431 = 4608647) B4608647
theorem B909895 : Blo 806344 909895 := bstep (se 1 (by rfl) ⟨682421, by rfl⟩ : syracuseStep 909895 = 1364843) B1364843
theorem B3073403 : Blo 806344 3073403 := bstep (se 1 (by rfl) ⟨2305052, by rfl⟩ : syracuseStep 3073403 = 4610105) B4610105
theorem B910759 : Blo 806344 910759 := bstep (se 1 (by rfl) ⟨683069, by rfl⟩ : syracuseStep 910759 = 1366139) B1366139
theorem B14018183 : Blo 806344 14018183 := bstep (se 1 (by rfl) ⟨10513637, by rfl⟩ : syracuseStep 14018183 = 21027275) B21027275
theorem B5891945 : Blo 806344 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B911335 : Blo 806344 911335 := bstep (se 1 (by rfl) ⟨683501, by rfl⟩ : syracuseStep 911335 = 1367003) B1367003
theorem B2910343 : Blo 806344 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B6220205 : Blo 806344 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B8841737 : Blo 806344 8841737 := bstep (se 2 (by rfl) ⟨3315651, by rfl⟩ : syracuseStep 8841737 = 6631303) B6631303
theorem B4091147 : Blo 806344 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B3075515 : Blo 806344 3075515 := bstep (se 1 (by rfl) ⟨2306636, by rfl⟩ : syracuseStep 3075515 = 4613273) B4613273
theorem B2452985 : Blo 806344 2452985 := bstep (se 2 (by rfl) ⟨919869, by rfl⟩ : syracuseStep 2452985 = 1839739) B1839739
theorem B7761869 : Blo 806344 7761869 := bstep (se 3 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 7761869 = 2910701) B2910701
theorem B7762483 : Blo 806344 7762483 := bstep (se 1 (by rfl) ⟨5821862, by rfl⟩ : syracuseStep 7762483 = 11643725) B11643725
theorem B4092767 : Blo 806344 4092767 := bstep (se 1 (by rfl) ⟨3069575, by rfl⟩ : syracuseStep 4092767 = 6139151) B6139151
theorem B1209563 : Blo 806344 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B2913529 : Blo 806344 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B1209737 : Blo 806344 1209737 := bstep (se 2 (by rfl) ⟨453651, by rfl⟩ : syracuseStep 1209737 = 907303) B907303
theorem B1537697 : Blo 806344 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B1210091 : Blo 806344 1210091 := bstep (se 1 (by rfl) ⟨907568, by rfl⟩ : syracuseStep 1210091 = 1815137) B1815137
theorem B2619191 : Blo 806344 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B1210319 : Blo 806344 1210319 := bstep (se 1 (by rfl) ⟨907739, by rfl⟩ : syracuseStep 1210319 = 1815479) B1815479
theorem B26245093 : Blo 806344 26245093 := bstep (se 4 (by rfl) ⟨2460477, by rfl⟩ : syracuseStep 26245093 = 4920955) B4920955
theorem B1210715 : Blo 806344 1210715 := bstep (se 1 (by rfl) ⟨908036, by rfl⟩ : syracuseStep 1210715 = 1816073) B1816073
theorem B1210943 : Blo 806344 1210943 := bstep (se 1 (by rfl) ⟨908207, by rfl⟩ : syracuseStep 1210943 = 1816415) B1816415
theorem B1211063 : Blo 806344 1211063 := bstep (se 1 (by rfl) ⟨908297, by rfl⟩ : syracuseStep 1211063 = 1816595) B1816595
theorem B4094711 : Blo 806344 4094711 := bstep (se 1 (by rfl) ⟨3071033, by rfl⟩ : syracuseStep 4094711 = 6142067) B6142067
theorem B1211291 : Blo 806344 1211291 := bstep (se 1 (by rfl) ⟨908468, by rfl⟩ : syracuseStep 1211291 = 1816937) B1816937
theorem B5176219 : Blo 806344 5176219 := bstep (se 1 (by rfl) ⟨3882164, by rfl⟩ : syracuseStep 5176219 = 7764329) B7764329
theorem B2915315 : Blo 806344 2915315 := bstep (se 1 (by rfl) ⟨2186486, by rfl⟩ : syracuseStep 2915315 = 4372973) B4372973
theorem B4095197 : Blo 806344 4095197 := bstep (se 3 (by rfl) ⟨767849, by rfl⟩ : syracuseStep 4095197 = 1535699) B1535699
theorem B1211687 : Blo 806344 1211687 := bstep (se 1 (by rfl) ⟨908765, by rfl⟩ : syracuseStep 1211687 = 1817531) B1817531
theorem B1211771 : Blo 806344 1211771 := bstep (se 1 (by rfl) ⟨908828, by rfl⟩ : syracuseStep 1211771 = 1817657) B1817657
theorem B1211897 : Blo 806344 1211897 := bstep (se 2 (by rfl) ⟨454461, by rfl⟩ : syracuseStep 1211897 = 908923) B908923
theorem B2915921 : Blo 806344 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B1211999 : Blo 806344 1211999 := bstep (se 1 (by rfl) ⟨908999, by rfl⟩ : syracuseStep 1211999 = 1817999) B1817999
theorem B2457391 : Blo 806344 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B1212215 : Blo 806344 1212215 := bstep (se 1 (by rfl) ⟨909161, by rfl⟩ : syracuseStep 1212215 = 1818323) B1818323
theorem B46530611 : Blo 806344 46530611 := bstep (se 1 (by rfl) ⟨34897958, by rfl⟩ : syracuseStep 46530611 = 69795917) B69795917
theorem B1212635 : Blo 806344 1212635 := bstep (se 1 (by rfl) ⟨909476, by rfl⟩ : syracuseStep 1212635 = 1818953) B1818953
theorem B1212647 : Blo 806344 1212647 := bstep (se 1 (by rfl) ⟨909485, by rfl⟩ : syracuseStep 1212647 = 1818971) B1818971
theorem B5832935 : Blo 806344 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B1212809 : Blo 806344 1212809 := bstep (se 2 (by rfl) ⟨454803, by rfl⟩ : syracuseStep 1212809 = 909607) B909607
theorem B1212905 : Blo 806344 1212905 := bstep (se 2 (by rfl) ⟨454839, by rfl⟩ : syracuseStep 1212905 = 909679) B909679
theorem B1213031 : Blo 806344 1213031 := bstep (se 1 (by rfl) ⟨909773, by rfl⟩ : syracuseStep 1213031 = 1819547) B1819547
theorem B1213163 : Blo 806344 1213163 := bstep (se 1 (by rfl) ⟨909872, by rfl⟩ : syracuseStep 1213163 = 1819745) B1819745
theorem B1213193 : Blo 806344 1213193 := bstep (se 2 (by rfl) ⟨454947, by rfl⟩ : syracuseStep 1213193 = 909895) B909895
theorem B1213295 : Blo 806344 1213295 := bstep (se 1 (by rfl) ⟨909971, by rfl⟩ : syracuseStep 1213295 = 1819943) B1819943
theorem B5178269 : Blo 806344 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B1639379 : Blo 806344 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B4096979 : Blo 806344 4096979 := bstep (se 1 (by rfl) ⟨3072734, by rfl⟩ : syracuseStep 4096979 = 6145469) B6145469
theorem B1213547 : Blo 806344 1213547 := bstep (se 1 (by rfl) ⟨910160, by rfl⟩ : syracuseStep 1213547 = 1820321) B1820321
theorem B2917565 : Blo 806344 2917565 := bstep (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) B1094087
theorem B12584135 : Blo 806344 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B1213787 : Blo 806344 1213787 := bstep (se 1 (by rfl) ⟨910340, by rfl⟩ : syracuseStep 1213787 = 1820681) B1820681
theorem B3278431 : Blo 806344 3278431 := bstep (se 1 (by rfl) ⟨2458823, by rfl⟩ : syracuseStep 3278431 = 4917647) B4917647
theorem B10356335 : Blo 806344 10356335 := bstep (se 1 (by rfl) ⟨7767251, by rfl⟩ : syracuseStep 10356335 = 15534503) B15534503
theorem B6227567 : Blo 806344 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B1214063 : Blo 806344 1214063 := bstep (se 1 (by rfl) ⟨910547, by rfl⟩ : syracuseStep 1214063 = 1821095) B1821095
theorem B1214135 : Blo 806344 1214135 := bstep (se 1 (by rfl) ⟨910601, by rfl⟩ : syracuseStep 1214135 = 1821203) B1821203
theorem B1214171 : Blo 806344 1214171 := bstep (se 1 (by rfl) ⟨910628, by rfl⟩ : syracuseStep 1214171 = 1821257) B1821257
theorem B5834551 : Blo 806344 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B1214345 : Blo 806344 1214345 := bstep (se 2 (by rfl) ⟨455379, by rfl⟩ : syracuseStep 1214345 = 910759) B910759
theorem B1214447 : Blo 806344 1214447 := bstep (se 1 (by rfl) ⟨910835, by rfl⟩ : syracuseStep 1214447 = 1821671) B1821671
theorem B5540075 : Blo 806344 5540075 := bstep (se 1 (by rfl) ⟨4155056, by rfl⟩ : syracuseStep 5540075 = 8310113) B8310113
theorem B1214699 : Blo 806344 1214699 := bstep (se 1 (by rfl) ⟨911024, by rfl⟩ : syracuseStep 1214699 = 1822049) B1822049
theorem B1149223 : Blo 806344 1149223 := bstep (se 1 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 1149223 = 1723835) B1723835
theorem B1214759 : Blo 806344 1214759 := bstep (se 1 (by rfl) ⟨911069, by rfl⟩ : syracuseStep 1214759 = 1822139) B1822139
theorem B2722139 : Blo 806344 2722139 := bstep (se 1 (by rfl) ⟨2041604, by rfl⟩ : syracuseStep 2722139 = 4083209) B4083209
theorem B1214843 : Blo 806344 1214843 := bstep (se 1 (by rfl) ⟨911132, by rfl⟩ : syracuseStep 1214843 = 1822265) B1822265
theorem B2951585 : Blo 806344 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B8718785 : Blo 806344 8718785 := bstep (se 2 (by rfl) ⟨3269544, by rfl⟩ : syracuseStep 8718785 = 6539089) B6539089
theorem B2951687 : Blo 806344 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B2722409 : Blo 806344 2722409 := bstep (se 2 (by rfl) ⟨1020903, by rfl⟩ : syracuseStep 2722409 = 2041807) B2041807
theorem B1215113 : Blo 806344 1215113 := bstep (se 2 (by rfl) ⟨455667, by rfl⟩ : syracuseStep 1215113 = 911335) B911335
theorem B1215287 : Blo 806344 1215287 := bstep (se 1 (by rfl) ⟨911465, by rfl⟩ : syracuseStep 1215287 = 1822931) B1822931
theorem B1215323 : Blo 806344 1215323 := bstep (se 1 (by rfl) ⟨911492, by rfl⟩ : syracuseStep 1215323 = 1822985) B1822985
theorem B2296795 : Blo 806344 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B1215467 : Blo 806344 1215467 := bstep (se 1 (by rfl) ⟨911600, by rfl⟩ : syracuseStep 1215467 = 1823201) B1823201
theorem B1379449 : Blo 806344 1379449 := bstep (se 2 (by rfl) ⟨517293, by rfl⟩ : syracuseStep 1379449 = 1034587) B1034587
theorem B2657423 : Blo 806344 2657423 := bstep (se 1 (by rfl) ⟨1993067, by rfl⟩ : syracuseStep 2657423 = 3986135) B3986135
theorem B5836283 : Blo 806344 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B2723435 : Blo 806344 2723435 := bstep (se 1 (by rfl) ⟨2042576, by rfl⟩ : syracuseStep 2723435 = 4085153) B4085153
theorem B6131375 : Blo 806344 6131375 := bstep (se 1 (by rfl) ⟨4598531, by rfl⟩ : syracuseStep 6131375 = 9197063) B9197063
theorem B5836625 : Blo 806344 5836625 := bstep (se 2 (by rfl) ⟨2188734, by rfl⟩ : syracuseStep 5836625 = 4377469) B4377469
theorem B2723705 : Blo 806344 2723705 := bstep (se 2 (by rfl) ⟨1021389, by rfl⟩ : syracuseStep 2723705 = 2042779) B2042779
theorem B2724029 : Blo 806344 2724029 := bstep (se 3 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 2724029 = 1021511) B1021511
theorem B6132347 : Blo 806344 6132347 := bstep (se 1 (by rfl) ⟨4599260, by rfl⟩ : syracuseStep 6132347 = 9198521) B9198521
theorem B10654507 : Blo 806344 10654507 := bstep (se 1 (by rfl) ⟨7990880, by rfl⟩ : syracuseStep 10654507 = 15981761) B15981761
theorem B1151911 : Blo 806344 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B3937319 : Blo 806344 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B1774867 : Blo 806344 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B2725217 : Blo 806344 2725217 := bstep (se 2 (by rfl) ⟨1021956, by rfl⟩ : syracuseStep 2725217 = 2043913) B2043913
theorem B1021339 : Blo 806344 1021339 := bstep (se 1 (by rfl) ⟨766004, by rfl⟩ : syracuseStep 1021339 = 1532009) B1532009
theorem B2299711 : Blo 806344 2299711 := bstep (se 1 (by rfl) ⟨1724783, by rfl⟩ : syracuseStep 2299711 = 3449567) B3449567
theorem B2955323 : Blo 806344 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B4593793 : Blo 806344 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B2300201 : Blo 806344 2300201 := bstep (se 2 (by rfl) ⟨862575, by rfl⟩ : syracuseStep 2300201 = 1725151) B1725151
theorem B9345455 : Blo 806344 9345455 := bstep (se 1 (by rfl) ⟨7009091, by rfl⟩ : syracuseStep 9345455 = 14018183) B14018183
theorem B5315371 : Blo 806344 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B2727161 : Blo 806344 2727161 := bstep (se 2 (by rfl) ⟨1022685, by rfl⟩ : syracuseStep 2727161 = 2045371) B2045371
theorem B2727431 : Blo 806344 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B11673659 : Blo 806344 11673659 := bstep (se 1 (by rfl) ⟨8755244, by rfl⟩ : syracuseStep 11673659 = 17510489) B17510489
theorem B2302091 : Blo 806344 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B5841067 : Blo 806344 5841067 := bstep (se 1 (by rfl) ⟨4380800, by rfl⟩ : syracuseStep 5841067 = 8761601) B8761601
theorem B2728511 : Blo 806344 2728511 := bstep (se 1 (by rfl) ⟨2046383, by rfl⟩ : syracuseStep 2728511 = 4092767) B4092767
theorem B10363463 : Blo 806344 10363463 := bstep (se 1 (by rfl) ⟨7772597, by rfl⟩ : syracuseStep 10363463 = 15545195) B15545195
theorem B1025131 : Blo 806344 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B1746127 : Blo 806344 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B4662479 : Blo 806344 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B2729807 : Blo 806344 2729807 := bstep (se 1 (by rfl) ⟨2047355, by rfl⟩ : syracuseStep 2729807 = 4094711) B4094711
theorem B1943543 : Blo 806344 1943543 := bstep (se 1 (by rfl) ⟨1457657, by rfl⟩ : syracuseStep 1943543 = 2915315) B2915315
theorem B2730131 : Blo 806344 2730131 := bstep (se 1 (by rfl) ⟨2047598, by rfl⟩ : syracuseStep 2730131 = 4095197) B4095197
theorem B1943947 : Blo 806344 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B2042273 : Blo 806344 2042273 := bstep (se 2 (by rfl) ⟨765852, by rfl⟩ : syracuseStep 2042273 = 1531705) B1531705
theorem B2730401 : Blo 806344 2730401 := bstep (se 2 (by rfl) ⟨1023900, by rfl⟩ : syracuseStep 2730401 = 2047801) B2047801
theorem B8727223 : Blo 806344 8727223 := bstep (se 1 (by rfl) ⟨6545417, by rfl⟩ : syracuseStep 8727223 = 13090835) B13090835
theorem B2043103 : Blo 806344 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B2043215 : Blo 806344 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B2076155 : Blo 806344 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B3452489 : Blo 806344 3452489 := bstep (se 2 (by rfl) ⟨1294683, by rfl⟩ : syracuseStep 3452489 = 2589367) B2589367
theorem B1814291 : Blo 806344 1814291 := bstep (se 1 (by rfl) ⟨1360718, by rfl⟩ : syracuseStep 1814291 = 2721437) B2721437
theorem B1814651 : Blo 806344 1814651 := bstep (se 1 (by rfl) ⟨1360988, by rfl⟩ : syracuseStep 1814651 = 2721977) B2721977
theorem B2732399 : Blo 806344 2732399 := bstep (se 1 (by rfl) ⟨2049299, by rfl⟩ : syracuseStep 2732399 = 4098599) B4098599
theorem B1814921 : Blo 806344 1814921 := bstep (se 2 (by rfl) ⟨680595, by rfl⟩ : syracuseStep 1814921 = 1361191) B1361191
theorem B4665871 : Blo 806344 4665871 := bstep (se 1 (by rfl) ⟨3499403, by rfl⟩ : syracuseStep 4665871 = 6998807) B6998807
theorem B2044511 : Blo 806344 2044511 := bstep (se 1 (by rfl) ⟨1533383, by rfl⟩ : syracuseStep 2044511 = 3066767) B3066767
theorem B4600583 : Blo 806344 4600583 := bstep (se 1 (by rfl) ⟨3450437, by rfl⟩ : syracuseStep 4600583 = 6900875) B6900875
theorem B5190571 : Blo 806344 5190571 := bstep (se 1 (by rfl) ⟨3892928, by rfl⟩ : syracuseStep 5190571 = 7785857) B7785857
theorem B10663001 : Blo 806344 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B1815659 : Blo 806344 1815659 := bstep (se 1 (by rfl) ⟨1361744, by rfl⟩ : syracuseStep 1815659 = 2723489) B2723489
theorem B6894791 : Blo 806344 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B23672087 : Blo 806344 23672087 := bstep (se 1 (by rfl) ⟨17754065, by rfl⟩ : syracuseStep 23672087 = 35508131) B35508131
theorem B3880457 : Blo 806344 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B1816235 : Blo 806344 1816235 := bstep (se 1 (by rfl) ⟨1362176, by rfl⟩ : syracuseStep 1816235 = 2724353) B2724353
theorem B2733803 : Blo 806344 2733803 := bstep (se 1 (by rfl) ⟨2050352, by rfl⟩ : syracuseStep 2733803 = 4100705) B4100705
theorem B29472605 : Blo 806344 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B1816559 : Blo 806344 1816559 := bstep (se 1 (by rfl) ⟨1362419, by rfl⟩ : syracuseStep 1816559 = 2724839) B2724839
theorem B2734073 : Blo 806344 2734073 := bstep (se 2 (by rfl) ⟨1025277, by rfl⟩ : syracuseStep 2734073 = 2050555) B2050555
theorem B2734235 : Blo 806344 2734235 := bstep (se 1 (by rfl) ⟨2050676, by rfl⟩ : syracuseStep 2734235 = 4101353) B4101353
theorem B4602041 : Blo 806344 4602041 := bstep (se 2 (by rfl) ⟨1725765, by rfl⟩ : syracuseStep 4602041 = 3451531) B3451531
theorem B1816775 : Blo 806344 1816775 := bstep (se 1 (by rfl) ⟨1362581, by rfl⟩ : syracuseStep 1816775 = 2725163) B2725163
theorem B2734343 : Blo 806344 2734343 := bstep (se 1 (by rfl) ⟨2050757, by rfl⟩ : syracuseStep 2734343 = 4101515) B4101515
theorem B9812339 : Blo 806344 9812339 := bstep (se 1 (by rfl) ⟨7359254, by rfl⟩ : syracuseStep 9812339 = 14718509) B14718509
theorem B1816955 : Blo 806344 1816955 := bstep (se 1 (by rfl) ⟨1362716, by rfl⟩ : syracuseStep 1816955 = 2725433) B2725433
theorem B5519929 : Blo 806344 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B1817225 : Blo 806344 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B1293383 : Blo 806344 1293383 := bstep (se 1 (by rfl) ⟨970037, by rfl⟩ : syracuseStep 1293383 = 1940075) B1940075
theorem B21576775 : Blo 806344 21576775 := bstep (se 1 (by rfl) ⟨16182581, by rfl⟩ : syracuseStep 21576775 = 32365163) B32365163
theorem B1817783 : Blo 806344 1817783 := bstep (se 1 (by rfl) ⟨1363337, by rfl⟩ : syracuseStep 1817783 = 2726675) B2726675
theorem B1555823 : Blo 806344 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B1293799 : Blo 806344 1293799 := bstep (se 1 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 1293799 = 1940699) B1940699
theorem B13319741 : Blo 806344 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B15711853 : Blo 806344 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B1818359 : Blo 806344 1818359 := bstep (se 1 (by rfl) ⟨1363769, by rfl⟩ : syracuseStep 1818359 = 2727539) B2727539
theorem B1294235 : Blo 806344 1294235 := bstep (se 1 (by rfl) ⟨970676, by rfl⟩ : syracuseStep 1294235 = 1941353) B1941353
theorem B1818539 : Blo 806344 1818539 := bstep (se 1 (by rfl) ⟨1363904, by rfl⟩ : syracuseStep 1818539 = 2727809) B2727809
theorem B3883087 : Blo 806344 3883087 := bstep (se 1 (by rfl) ⟨2912315, by rfl⟩ : syracuseStep 3883087 = 5824631) B5824631
theorem B2048287 : Blo 806344 2048287 := bstep (se 1 (by rfl) ⟨1536215, by rfl⟩ : syracuseStep 2048287 = 3072431) B3072431
theorem B19939769 : Blo 806344 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B1819079 : Blo 806344 1819079 := bstep (se 1 (by rfl) ⟨1364309, by rfl⟩ : syracuseStep 1819079 = 2728619) B2728619
theorem B1819439 : Blo 806344 1819439 := bstep (se 1 (by rfl) ⟨1364579, by rfl⟩ : syracuseStep 1819439 = 2729159) B2729159
theorem B2048935 : Blo 806344 2048935 := bstep (se 1 (by rfl) ⟨1536701, by rfl⟩ : syracuseStep 2048935 = 3073403) B3073403
theorem B2770109 : Blo 806344 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B3458315 : Blo 806344 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B23577965 : Blo 806344 23577965 := bstep (se 3 (by rfl) ⟨4420868, by rfl⟩ : syracuseStep 23577965 = 8841737) B8841737
theorem B4146803 : Blo 806344 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B3884705 : Blo 806344 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B1820447 : Blo 806344 1820447 := bstep (se 1 (by rfl) ⟨1365335, by rfl⟩ : syracuseStep 1820447 = 2730671) B2730671
theorem B84002669 : Blo 806344 84002669 := bstep (se 3 (by rfl) ⟨15750500, by rfl⟩ : syracuseStep 84002669 = 31501001) B31501001
theorem B23578543 : Blo 806344 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B1820663 : Blo 806344 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B1493147 : Blo 806344 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B2050343 : Blo 806344 2050343 := bstep (se 1 (by rfl) ⟨1537757, by rfl⟩ : syracuseStep 2050343 = 3075515) B3075515
theorem B1362217 : Blo 806344 1362217 := bstep (se 2 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 1362217 = 1021663) B1021663
theorem B1821023 : Blo 806344 1821023 := bstep (se 1 (by rfl) ⟨1365767, by rfl⟩ : syracuseStep 1821023 = 2731535) B2731535
theorem B1297387 : Blo 806344 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B1821743 : Blo 806344 1821743 := bstep (se 1 (by rfl) ⟨1366307, by rfl⟩ : syracuseStep 1821743 = 2732615) B2732615
theorem B1822031 : Blo 806344 1822031 := bstep (se 1 (by rfl) ⟨1366523, by rfl⟩ : syracuseStep 1822031 = 2733047) B2733047
theorem B1822121 : Blo 806344 1822121 := bstep (se 2 (by rfl) ⟨683295, by rfl⟩ : syracuseStep 1822121 = 1366591) B1366591
theorem B806375 : Blo 806344 806375 := bstep (se 1 (by rfl) ⟨604781, by rfl⟩ : syracuseStep 806375 = 1209563) B1209563
theorem B8277509 : Blo 806344 8277509 := bstep (se 4 (by rfl) ⟨776016, by rfl⟩ : syracuseStep 8277509 = 1552033) B1552033
theorem B806491 : Blo 806344 806491 := bstep (se 1 (by rfl) ⟨604868, by rfl⟩ : syracuseStep 806491 = 1209737) B1209737
theorem B1363547 : Blo 806344 1363547 := bstep (se 1 (by rfl) ⟨1022660, by rfl⟩ : syracuseStep 1363547 = 2045321) B2045321
theorem B6540907 : Blo 806344 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B806727 : Blo 806344 806727 := bstep (se 1 (by rfl) ⟨605045, by rfl⟩ : syracuseStep 806727 = 1210091) B1210091
theorem B1363783 : Blo 806344 1363783 := bstep (se 1 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 1363783 = 2045675) B2045675
theorem B3067753 : Blo 806344 3067753 := bstep (se 2 (by rfl) ⟨1150407, by rfl⟩ : syracuseStep 3067753 = 2300815) B2300815
theorem B6901625 : Blo 806344 6901625 := bstep (se 2 (by rfl) ⟨2588109, by rfl⟩ : syracuseStep 6901625 = 5176219) B5176219
theorem B1822607 : Blo 806344 1822607 := bstep (se 1 (by rfl) ⟨1366955, by rfl⟩ : syracuseStep 1822607 = 2733911) B2733911
theorem B806879 : Blo 806344 806879 := bstep (se 1 (by rfl) ⟨605159, by rfl⟩ : syracuseStep 806879 = 1210319) B1210319
theorem B807143 : Blo 806344 807143 := bstep (se 1 (by rfl) ⟨605357, by rfl⟩ : syracuseStep 807143 = 1210715) B1210715
theorem B807295 : Blo 806344 807295 := bstep (se 1 (by rfl) ⟨605471, by rfl⟩ : syracuseStep 807295 = 1210943) B1210943
theorem B1724809 : Blo 806344 1724809 := bstep (se 2 (by rfl) ⟨646803, by rfl⟩ : syracuseStep 1724809 = 1293607) B1293607
theorem B807375 : Blo 806344 807375 := bstep (se 1 (by rfl) ⟨605531, by rfl⟩ : syracuseStep 807375 = 1211063) B1211063
theorem B1364431 : Blo 806344 1364431 := bstep (se 1 (by rfl) ⟨1023323, by rfl⟩ : syracuseStep 1364431 = 2046647) B2046647
theorem B807527 : Blo 806344 807527 := bstep (se 1 (by rfl) ⟨605645, by rfl⟩ : syracuseStep 807527 = 1211291) B1211291
theorem B4084505 : Blo 806344 4084505 := bstep (se 2 (by rfl) ⟨1531689, by rfl⟩ : syracuseStep 4084505 = 3063379) B3063379
theorem B4379417 : Blo 806344 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B807791 : Blo 806344 807791 := bstep (se 1 (by rfl) ⟨605843, by rfl⟩ : syracuseStep 807791 = 1211687) B1211687
theorem B807847 : Blo 806344 807847 := bstep (se 1 (by rfl) ⟨605885, by rfl⟩ : syracuseStep 807847 = 1211771) B1211771
theorem B807931 : Blo 806344 807931 := bstep (se 1 (by rfl) ⟨605948, by rfl⟩ : syracuseStep 807931 = 1211897) B1211897
theorem B807999 : Blo 806344 807999 := bstep (se 1 (by rfl) ⟨605999, by rfl⟩ : syracuseStep 807999 = 1211999) B1211999
theorem B8279117 : Blo 806344 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B1365167 : Blo 806344 1365167 := bstep (se 1 (by rfl) ⟨1023875, by rfl⟩ : syracuseStep 1365167 = 2047751) B2047751
theorem B808143 : Blo 806344 808143 := bstep (se 1 (by rfl) ⟨606107, by rfl⟩ : syracuseStep 808143 = 1212215) B1212215
theorem B971983 : Blo 806344 971983 := bstep (se 1 (by rfl) ⟨728987, by rfl⟩ : syracuseStep 971983 = 1457975) B1457975
theorem B1365403 : Blo 806344 1365403 := bstep (se 1 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 1365403 = 2048105) B2048105
theorem B808347 : Blo 806344 808347 := bstep (se 1 (by rfl) ⟨606260, by rfl⟩ : syracuseStep 808347 = 1212521) B1212521
theorem B808559 : Blo 806344 808559 := bstep (se 1 (by rfl) ⟨606419, by rfl⟩ : syracuseStep 808559 = 1212839) B1212839
theorem B808615 : Blo 806344 808615 := bstep (se 1 (by rfl) ⟨606461, by rfl⟩ : syracuseStep 808615 = 1212923) B1212923
theorem B1365727 : Blo 806344 1365727 := bstep (se 1 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 1365727 = 2048591) B2048591
theorem B808699 : Blo 806344 808699 := bstep (se 1 (by rfl) ⟨606524, by rfl⟩ : syracuseStep 808699 = 1213049) B1213049
theorem B808735 : Blo 806344 808735 := bstep (se 1 (by rfl) ⟨606551, by rfl⟩ : syracuseStep 808735 = 1213103) B1213103
theorem B808767 : Blo 806344 808767 := bstep (se 1 (by rfl) ⟨606575, by rfl⟩ : syracuseStep 808767 = 1213151) B1213151
theorem B17487731 : Blo 806344 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B1169383 : Blo 806344 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B808943 : Blo 806344 808943 := bstep (se 1 (by rfl) ⟨606707, by rfl⟩ : syracuseStep 808943 = 1213415) B1213415
theorem B1366159 : Blo 806344 1366159 := bstep (se 1 (by rfl) ⟨1024619, by rfl⟩ : syracuseStep 1366159 = 2049239) B2049239
theorem B809115 : Blo 806344 809115 := bstep (se 1 (by rfl) ⟨606836, by rfl⟩ : syracuseStep 809115 = 1213673) B1213673
theorem B809151 : Blo 806344 809151 := bstep (se 1 (by rfl) ⟨606863, by rfl⟩ : syracuseStep 809151 = 1213727) B1213727
theorem B4085963 : Blo 806344 4085963 := bstep (se 1 (by rfl) ⟨3064472, by rfl⟩ : syracuseStep 4085963 = 6128945) B6128945
theorem B1726697 : Blo 806344 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B809263 : Blo 806344 809263 := bstep (se 1 (by rfl) ⟨606947, by rfl⟩ : syracuseStep 809263 = 1213895) B1213895
theorem B23353879 : Blo 806344 23353879 := bstep (se 1 (by rfl) ⟨17515409, by rfl⟩ : syracuseStep 23353879 = 35030819) B35030819
theorem B809499 : Blo 806344 809499 := bstep (se 1 (by rfl) ⟨607124, by rfl⟩ : syracuseStep 809499 = 1214249) B1214249
theorem B907807 : Blo 806344 907807 := bstep (se 1 (by rfl) ⟨680855, by rfl⟩ : syracuseStep 907807 = 1361711) B1361711
theorem B809503 : Blo 806344 809503 := bstep (se 1 (by rfl) ⟨607127, by rfl⟩ : syracuseStep 809503 = 1214255) B1214255
theorem B29547341 : Blo 806344 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B4086611 : Blo 806344 4086611 := bstep (se 1 (by rfl) ⟨3064958, by rfl⟩ : syracuseStep 4086611 = 6129917) B6129917
theorem B809819 : Blo 806344 809819 := bstep (se 1 (by rfl) ⟨607364, by rfl⟩ : syracuseStep 809819 = 1214729) B1214729
theorem B809887 : Blo 806344 809887 := bstep (se 1 (by rfl) ⟨607415, by rfl⟩ : syracuseStep 809887 = 1214831) B1214831
theorem B810031 : Blo 806344 810031 := bstep (se 1 (by rfl) ⟨607523, by rfl⟩ : syracuseStep 810031 = 1215047) B1215047
theorem B810055 : Blo 806344 810055 := bstep (se 1 (by rfl) ⟨607541, by rfl⟩ : syracuseStep 810055 = 1215083) B1215083
theorem B1367111 : Blo 806344 1367111 := bstep (se 1 (by rfl) ⟨1025333, by rfl⟩ : syracuseStep 1367111 = 2050667) B2050667
theorem B2186423 : Blo 806344 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B810207 : Blo 806344 810207 := bstep (se 1 (by rfl) ⟨607655, by rfl⟩ : syracuseStep 810207 = 1215311) B1215311
theorem B6905249 : Blo 806344 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B1662439 : Blo 806344 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B3890663 : Blo 806344 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B6545447 : Blo 806344 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B3891239 : Blo 806344 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B1532191 : Blo 806344 1532191 := bstep (se 1 (by rfl) ⟨1149143, by rfl⟩ : syracuseStep 1532191 = 2298287) B2298287
theorem B4088393 : Blo 806344 4088393 := bstep (se 2 (by rfl) ⟨1533147, by rfl⟩ : syracuseStep 4088393 = 3066295) B3066295
theorem B4612747 : Blo 806344 4612747 := bstep (se 1 (by rfl) ⟨3459560, by rfl⟩ : syracuseStep 4612747 = 6919121) B6919121
theorem B1532783 : Blo 806344 1532783 := bstep (se 1 (by rfl) ⟨1149587, by rfl⟩ : syracuseStep 1532783 = 2299175) B2299175
theorem B6153245 : Blo 806344 6153245 := bstep (se 3 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 6153245 = 2307467) B2307467
theorem B910399 : Blo 806344 910399 := bstep (se 1 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 910399 = 1365599) B1365599
theorem B910543 : Blo 806344 910543 := bstep (se 1 (by rfl) ⟨682907, by rfl⟩ : syracuseStep 910543 = 1365815) B1365815
theorem B3073889 : Blo 806344 3073889 := bstep (se 2 (by rfl) ⟨1152708, by rfl⟩ : syracuseStep 3073889 = 2305417) B2305417
theorem B911515 : Blo 806344 911515 := bstep (se 1 (by rfl) ⟨683636, by rfl⟩ : syracuseStep 911515 = 1367273) B1367273
theorem B911551 : Blo 806344 911551 := bstep (se 1 (by rfl) ⟨683663, by rfl⟩ : syracuseStep 911551 = 1367327) B1367327
theorem B7105283 : Blo 806344 7105283 := bstep (se 1 (by rfl) ⟨5328962, by rfl⟩ : syracuseStep 7105283 = 10657925) B10657925
theorem B10349977 : Blo 806344 10349977 := bstep (se 2 (by rfl) ⟨3881241, by rfl⟩ : syracuseStep 10349977 = 7762483) B7762483
theorem B13266827 : Blo 806344 13266827 := bstep (se 1 (by rfl) ⟨9950120, by rfl⟩ : syracuseStep 13266827 = 19900241) B19900241
theorem B8745083 : Blo 806344 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B2584829 : Blo 806344 2584829 := bstep (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) B969311
theorem B25555301 : Blo 806344 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B1536383 : Blo 806344 1536383 := bstep (se 1 (by rfl) ⟨1152287, by rfl⟩ : syracuseStep 1536383 = 2304575) B2304575
theorem B1635323 : Blo 806344 1635323 := bstep (se 1 (by rfl) ⟨1226492, by rfl⟩ : syracuseStep 1635323 = 2452985) B2452985
theorem B1209551 : Blo 806344 1209551 := bstep (se 1 (by rfl) ⟨907163, by rfl⟩ : syracuseStep 1209551 = 1814327) B1814327
theorem B5534963 : Blo 806344 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B34993457 : Blo 806344 34993457 := bstep (se 2 (by rfl) ⟨13122546, by rfl⟩ : syracuseStep 34993457 = 26245093) B26245093
theorem B5174579 : Blo 806344 5174579 := bstep (se 1 (by rfl) ⟨3880934, by rfl⟩ : syracuseStep 5174579 = 7761869) B7761869
theorem B1209755 : Blo 806344 1209755 := bstep (se 1 (by rfl) ⟨907316, by rfl⟩ : syracuseStep 1209755 = 1814633) B1814633
theorem B1209977 : Blo 806344 1209977 := bstep (se 2 (by rfl) ⟨453741, by rfl⟩ : syracuseStep 1209977 = 907483) B907483
theorem B1210079 : Blo 806344 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B1210175 : Blo 806344 1210175 := bstep (se 1 (by rfl) ⟨907631, by rfl⟩ : syracuseStep 1210175 = 1815263) B1815263
theorem B1210343 : Blo 806344 1210343 := bstep (se 1 (by rfl) ⟨907757, by rfl⟩ : syracuseStep 1210343 = 1815515) B1815515
theorem B2586599 : Blo 806344 2586599 := bstep (se 1 (by rfl) ⟨1939949, by rfl⟩ : syracuseStep 2586599 = 3879899) B3879899
theorem B1538023 : Blo 806344 1538023 := bstep (se 1 (by rfl) ⟨1153517, by rfl⟩ : syracuseStep 1538023 = 2307035) B2307035
theorem B1210361 : Blo 806344 1210361 := bstep (se 2 (by rfl) ⟨453885, by rfl⟩ : syracuseStep 1210361 = 907771) B907771
theorem B1210463 : Blo 806344 1210463 := bstep (se 1 (by rfl) ⟨907847, by rfl⟩ : syracuseStep 1210463 = 1815695) B1815695
theorem B1210523 : Blo 806344 1210523 := bstep (se 1 (by rfl) ⟨907892, by rfl⟩ : syracuseStep 1210523 = 1815785) B1815785
theorem B1210559 : Blo 806344 1210559 := bstep (se 1 (by rfl) ⟨907919, by rfl⟩ : syracuseStep 1210559 = 1815839) B1815839
theorem B1210601 : Blo 806344 1210601 := bstep (se 2 (by rfl) ⟨453975, by rfl⟩ : syracuseStep 1210601 = 907951) B907951
theorem B2914537 : Blo 806344 2914537 := bstep (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) B2185903
theorem B1538281 : Blo 806344 1538281 := bstep (se 2 (by rfl) ⟨576855, by rfl⟩ : syracuseStep 1538281 = 1153711) B1153711
theorem B1210907 : Blo 806344 1210907 := bstep (se 1 (by rfl) ⟨908180, by rfl⟩ : syracuseStep 1210907 = 1816361) B1816361
theorem B1210985 : Blo 806344 1210985 := bstep (se 2 (by rfl) ⟨454119, by rfl⟩ : syracuseStep 1210985 = 908239) B908239
theorem B1211513 : Blo 806344 1211513 := bstep (se 2 (by rfl) ⟨454317, by rfl⟩ : syracuseStep 1211513 = 908635) B908635
theorem B1211615 : Blo 806344 1211615 := bstep (se 1 (by rfl) ⟨908711, by rfl⟩ : syracuseStep 1211615 = 1817423) B1817423
theorem B1211657 : Blo 806344 1211657 := bstep (se 2 (by rfl) ⟨454371, by rfl⟩ : syracuseStep 1211657 = 908743) B908743
theorem B1211759 : Blo 806344 1211759 := bstep (se 1 (by rfl) ⟨908819, by rfl⟩ : syracuseStep 1211759 = 1817639) B1817639
theorem B1211879 : Blo 806344 1211879 := bstep (se 1 (by rfl) ⟨908909, by rfl⟩ : syracuseStep 1211879 = 1817819) B1817819
theorem B1212011 : Blo 806344 1212011 := bstep (se 1 (by rfl) ⟨909008, by rfl⟩ : syracuseStep 1212011 = 1818017) B1818017
theorem B1212137 : Blo 806344 1212137 := bstep (se 2 (by rfl) ⟨454551, by rfl⟩ : syracuseStep 1212137 = 909103) B909103
theorem B3276521 : Blo 806344 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B1212281 : Blo 806344 1212281 := bstep (se 2 (by rfl) ⟨454605, by rfl⟩ : syracuseStep 1212281 = 909211) B909211
theorem B1212383 : Blo 806344 1212383 := bstep (se 1 (by rfl) ⟨909287, by rfl⟩ : syracuseStep 1212383 = 1818575) B1818575
theorem B5177449 : Blo 806344 5177449 := bstep (se 2 (by rfl) ⟨1941543, by rfl⟩ : syracuseStep 5177449 = 3883087) B3883087
theorem B1212719 : Blo 806344 1212719 := bstep (se 1 (by rfl) ⟨909539, by rfl⟩ : syracuseStep 1212719 = 1819079) B1819079
theorem B1212959 : Blo 806344 1212959 := bstep (se 1 (by rfl) ⟨909719, by rfl⟩ : syracuseStep 1212959 = 1819439) B1819439
theorem B8389423 : Blo 806344 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B2589803 : Blo 806344 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B1213631 : Blo 806344 1213631 := bstep (se 1 (by rfl) ⟨910223, by rfl⟩ : syracuseStep 1213631 = 1820447) B1820447
theorem B56001779 : Blo 806344 56001779 := bstep (se 1 (by rfl) ⟨42001334, by rfl⟩ : syracuseStep 56001779 = 84002669) B84002669
theorem B1213775 : Blo 806344 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B1213865 : Blo 806344 1213865 := bstep (se 2 (by rfl) ⟨455199, by rfl⟩ : syracuseStep 1213865 = 910399) B910399
theorem B1214015 : Blo 806344 1214015 := bstep (se 1 (by rfl) ⟨910511, by rfl⟩ : syracuseStep 1214015 = 1821023) B1821023
theorem B2328169 : Blo 806344 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B1214057 : Blo 806344 1214057 := bstep (se 2 (by rfl) ⟨455271, by rfl⟩ : syracuseStep 1214057 = 910543) B910543
theorem B1967723 : Blo 806344 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B1214495 : Blo 806344 1214495 := bstep (se 1 (by rfl) ⟨910871, by rfl⟩ : syracuseStep 1214495 = 1821743) B1821743
theorem B1214687 : Blo 806344 1214687 := bstep (se 1 (by rfl) ⟨911015, by rfl⟩ : syracuseStep 1214687 = 1822031) B1822031
theorem B1214747 : Blo 806344 1214747 := bstep (se 1 (by rfl) ⟨911060, by rfl⟩ : syracuseStep 1214747 = 1822121) B1822121
theorem B1215071 : Blo 806344 1215071 := bstep (se 1 (by rfl) ⟨911303, by rfl⟩ : syracuseStep 1215071 = 1822607) B1822607
theorem B4360861 : Blo 806344 4360861 := bstep (se 3 (by rfl) ⟨817661, by rfl⟩ : syracuseStep 4360861 = 1635323) B1635323
theorem B1215353 : Blo 806344 1215353 := bstep (se 2 (by rfl) ⟨455757, by rfl⟩ : syracuseStep 1215353 = 911515) B911515
theorem B1215401 : Blo 806344 1215401 := bstep (se 2 (by rfl) ⟨455775, by rfl⟩ : syracuseStep 1215401 = 911551) B911551
theorem B2591929 : Blo 806344 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B2723003 : Blo 806344 2723003 := bstep (se 1 (by rfl) ⟨2042252, by rfl⟩ : syracuseStep 2723003 = 4084505) B4084505
theorem B2919611 : Blo 806344 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B2624879 : Blo 806344 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B11636297 : Blo 806344 11636297 := bstep (se 2 (by rfl) ⟨4363611, by rfl⟩ : syracuseStep 11636297 = 8727223) B8727223
theorem B2723975 : Blo 806344 2723975 := bstep (se 1 (by rfl) ⟨2042981, by rfl⟩ : syracuseStep 2723975 = 4085963) B4085963
theorem B28348645 : Blo 806344 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B56824037 : Blo 806344 56824037 := bstep (se 4 (by rfl) ⟨5327253, by rfl⟩ : syracuseStep 56824037 = 10654507) B10654507
theorem B6230303 : Blo 806344 6230303 := bstep (se 1 (by rfl) ⟨4672727, by rfl⟩ : syracuseStep 6230303 = 9345455) B9345455
theorem B2724137 : Blo 806344 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B13799969 : Blo 806344 13799969 := bstep (se 2 (by rfl) ⟨5174988, by rfl⟩ : syracuseStep 13799969 = 10349977) B10349977
theorem B19698227 : Blo 806344 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B2724407 : Blo 806344 2724407 := bstep (se 1 (by rfl) ⟨2043305, by rfl⟩ : syracuseStep 2724407 = 4086611) B4086611
theorem B8721209 : Blo 806344 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B2593775 : Blo 806344 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B4363631 : Blo 806344 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B2594159 : Blo 806344 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B2725595 : Blo 806344 2725595 := bstep (se 1 (by rfl) ⟨2044196, by rfl⟩ : syracuseStep 2725595 = 4088393) B4088393
theorem B2299745 : Blo 806344 2299745 := bstep (se 2 (by rfl) ⟨862404, by rfl⟩ : syracuseStep 2299745 = 1724809) B1724809
theorem B4102163 : Blo 806344 4102163 := bstep (se 1 (by rfl) ⟨3076622, by rfl⟩ : syracuseStep 4102163 = 6153245) B6153245
theorem B5183909 : Blo 806344 5183909 := bstep (se 4 (by rfl) ⟨485991, by rfl⟩ : syracuseStep 5183909 = 971983) B971983
theorem B6920761 : Blo 806344 6920761 := bstep (se 2 (by rfl) ⟨2595285, by rfl⟩ : syracuseStep 6920761 = 5190571) B5190571
theorem B7871165 : Blo 806344 7871165 := bstep (se 3 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 7871165 = 2951687) B2951687
theorem B2366489 : Blo 806344 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B1384103 : Blo 806344 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B2301659 : Blo 806344 2301659 := bstep (se 1 (by rfl) ⟨1726244, by rfl⟩ : syracuseStep 2301659 = 3452489) B3452489
theorem B1024255 : Blo 806344 1024255 := bstep (se 1 (by rfl) ⟨768191, by rfl⟩ : syracuseStep 1024255 = 1536383) B1536383
theorem B7086461 : Blo 806344 7086461 := bstep (se 3 (by rfl) ⟨1328711, by rfl⟩ : syracuseStep 7086461 = 2657423) B2657423
theorem B31138505 : Blo 806344 31138505 := bstep (se 2 (by rfl) ⟨11676939, by rfl⟩ : syracuseStep 31138505 = 23353879) B23353879
theorem B4596527 : Blo 806344 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B3449719 : Blo 806344 3449719 := bstep (se 1 (by rfl) ⟨2587289, by rfl⟩ : syracuseStep 3449719 = 5174579) B5174579
theorem B862255 : Blo 806344 862255 := bstep (se 1 (by rfl) ⟨646691, by rfl⟩ : syracuseStep 862255 = 1293383) B1293383
theorem B20949137 : Blo 806344 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B862823 : Blo 806344 862823 := bstep (se 1 (by rfl) ⟨647117, by rfl⟩ : syracuseStep 862823 = 1294235) B1294235
theorem B2042921 : Blo 806344 2042921 := bstep (se 2 (by rfl) ⟨766095, by rfl⟩ : syracuseStep 2042921 = 1532191) B1532191
theorem B2731049 : Blo 806344 2731049 := bstep (se 2 (by rfl) ⟨1024143, by rfl⟩ : syracuseStep 2731049 = 2048287) B2048287
theorem B2731319 : Blo 806344 2731319 := bstep (se 1 (by rfl) ⟨2048489, by rfl⟩ : syracuseStep 2731319 = 4096979) B4096979
theorem B6892877 : Blo 806344 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B1945043 : Blo 806344 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B1846739 : Blo 806344 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B2305543 : Blo 806344 2305543 := bstep (se 1 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 2305543 = 3458315) B3458315
theorem B2764535 : Blo 806344 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B2731913 : Blo 806344 2731913 := bstep (se 2 (by rfl) ⟨1024467, by rfl⟩ : syracuseStep 2731913 = 2048935) B2048935
theorem B995431 : Blo 806344 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B1814759 : Blo 806344 1814759 := bstep (se 1 (by rfl) ⟨1361069, by rfl⟩ : syracuseStep 1814759 = 2722139) B2722139
theorem B5812523 : Blo 806344 5812523 := bstep (se 1 (by rfl) ⟨4359392, by rfl⟩ : syracuseStep 5812523 = 8718785) B8718785
theorem B1814939 : Blo 806344 1814939 := bstep (se 1 (by rfl) ⟨1361204, by rfl⟩ : syracuseStep 1814939 = 2722409) B2722409
theorem B4371241 : Blo 806344 4371241 := bstep (se 2 (by rfl) ⟨1639215, by rfl⟩ : syracuseStep 4371241 = 3278431) B3278431
theorem B1815623 : Blo 806344 1815623 := bstep (se 1 (by rfl) ⟨1361717, by rfl⟩ : syracuseStep 1815623 = 2723435) B2723435
theorem B7779401 : Blo 806344 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B13808717 : Blo 806344 13808717 := bstep (se 3 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 13808717 = 5178269) B5178269
theorem B4371677 : Blo 806344 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B31438057 : Blo 806344 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B1815803 : Blo 806344 1815803 := bstep (se 1 (by rfl) ⟨1361852, by rfl⟩ : syracuseStep 1815803 = 2723705) B2723705
theorem B4601083 : Blo 806344 4601083 := bstep (se 1 (by rfl) ⟨3450812, by rfl⟩ : syracuseStep 4601083 = 6901625) B6901625
theorem B1816019 : Blo 806344 1816019 := bstep (se 1 (by rfl) ⟨1362014, by rfl⟩ : syracuseStep 1816019 = 2724029) B2724029
theorem B1816289 : Blo 806344 1816289 := bstep (se 2 (by rfl) ⟨681108, by rfl⟩ : syracuseStep 1816289 = 1362217) B1362217
theorem B12433277 : Blo 806344 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B5519411 : Blo 806344 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B1816811 : Blo 806344 1816811 := bstep (se 1 (by rfl) ⟨1362608, by rfl⟩ : syracuseStep 1816811 = 2725217) B2725217
theorem B3062393 : Blo 806344 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B1457615 : Blo 806344 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B1818107 : Blo 806344 1818107 := bstep (se 1 (by rfl) ⟨1363580, by rfl⟩ : syracuseStep 1818107 = 2727161) B2727161
theorem B6143525 : Blo 806344 6143525 := bstep (se 4 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 6143525 = 1151911) B1151911
theorem B4603499 : Blo 806344 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B1818287 : Blo 806344 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B1818377 : Blo 806344 1818377 := bstep (se 2 (by rfl) ⟨681891, by rfl⟩ : syracuseStep 1818377 = 1363783) B1363783
theorem B7782439 : Blo 806344 7782439 := bstep (se 1 (by rfl) ⟨5836829, by rfl⟩ : syracuseStep 7782439 = 11673659) B11673659
theorem B7880861 : Blo 806344 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B1819007 : Blo 806344 1819007 := bstep (se 1 (by rfl) ⟨1364255, by rfl⟩ : syracuseStep 1819007 = 2728511) B2728511
theorem B1819241 : Blo 806344 1819241 := bstep (se 2 (by rfl) ⟨682215, by rfl⟩ : syracuseStep 1819241 = 1364431) B1364431
theorem B4604525 : Blo 806344 4604525 := bstep (se 3 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 4604525 = 1726697) B1726697
theorem B7357061 : Blo 806344 7357061 := bstep (se 4 (by rfl) ⟨689724, by rfl⟩ : syracuseStep 7357061 = 1379449) B1379449
theorem B1819871 : Blo 806344 1819871 := bstep (se 1 (by rfl) ⟨1364903, by rfl⟩ : syracuseStep 1819871 = 2729807) B2729807
theorem B2049259 : Blo 806344 2049259 := bstep (se 1 (by rfl) ⟨1536944, by rfl⟩ : syracuseStep 2049259 = 3073889) B3073889
theorem B1295695 : Blo 806344 1295695 := bstep (se 1 (by rfl) ⟨971771, by rfl⟩ : syracuseStep 1295695 = 1943543) B1943543
theorem B1820087 : Blo 806344 1820087 := bstep (se 1 (by rfl) ⟨1365065, by rfl⟩ : syracuseStep 1820087 = 2730131) B2730131
theorem B1361515 : Blo 806344 1361515 := bstep (se 1 (by rfl) ⟨1021136, by rfl⟩ : syracuseStep 1361515 = 2042273) B2042273
theorem B1820267 : Blo 806344 1820267 := bstep (se 1 (by rfl) ⟨1365200, by rfl⟩ : syracuseStep 1820267 = 2730401) B2730401
theorem B4736855 : Blo 806344 4736855 := bstep (se 1 (by rfl) ⟨3552641, by rfl⟩ : syracuseStep 4736855 = 7105283) B7105283
theorem B1361785 : Blo 806344 1361785 := bstep (se 2 (by rfl) ⟨510669, by rfl⟩ : syracuseStep 1361785 = 1021339) B1021339
theorem B1820537 : Blo 806344 1820537 := bstep (se 2 (by rfl) ⟨682701, by rfl⟩ : syracuseStep 1820537 = 1365403) B1365403
theorem B1362143 : Blo 806344 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B1820969 : Blo 806344 1820969 := bstep (se 2 (by rfl) ⟨682863, by rfl⟩ : syracuseStep 1820969 = 1365727) B1365727
theorem B3066281 : Blo 806344 3066281 := bstep (se 2 (by rfl) ⟨1149855, by rfl⟩ : syracuseStep 3066281 = 2299711) B2299711
theorem B2050697 : Blo 806344 2050697 := bstep (se 2 (by rfl) ⟨769011, by rfl⟩ : syracuseStep 2050697 = 1538023) B1538023
theorem B1559177 : Blo 806344 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B1821545 : Blo 806344 1821545 := bstep (se 2 (by rfl) ⟨683079, by rfl⟩ : syracuseStep 1821545 = 1366159) B1366159
theorem B1821599 : Blo 806344 1821599 := bstep (se 1 (by rfl) ⟨1366199, by rfl⟩ : syracuseStep 1821599 = 2732399) B2732399
theorem B3886049 : Blo 806344 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B2051041 : Blo 806344 2051041 := bstep (se 2 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 2051041 = 1538281) B1538281
theorem B1363007 : Blo 806344 1363007 := bstep (se 1 (by rfl) ⟨1022255, by rfl⟩ : syracuseStep 1363007 = 2044511) B2044511
theorem B3067055 : Blo 806344 3067055 := bstep (se 1 (by rfl) ⟨2300291, by rfl⟩ : syracuseStep 3067055 = 4600583) B4600583
theorem B7359905 : Blo 806344 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B806367 : Blo 806344 806367 := bstep (se 1 (by rfl) ⟨604775, by rfl⟩ : syracuseStep 806367 = 1209551) B1209551
theorem B3689975 : Blo 806344 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B15781391 : Blo 806344 15781391 := bstep (se 1 (by rfl) ⟨11836043, by rfl⟩ : syracuseStep 15781391 = 23672087) B23672087
theorem B806503 : Blo 806344 806503 := bstep (se 1 (by rfl) ⟨604877, by rfl⟩ : syracuseStep 806503 = 1209755) B1209755
theorem B806651 : Blo 806344 806651 := bstep (se 1 (by rfl) ⟨604988, by rfl⟩ : syracuseStep 806651 = 1209977) B1209977
theorem B806719 : Blo 806344 806719 := bstep (se 1 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 806719 = 1210079) B1210079
theorem B1822535 : Blo 806344 1822535 := bstep (se 1 (by rfl) ⟨1366901, by rfl⟩ : syracuseStep 1822535 = 2733803) B2733803
theorem B806783 : Blo 806344 806783 := bstep (se 1 (by rfl) ⟨605087, by rfl⟩ : syracuseStep 806783 = 1210175) B1210175
theorem B19648403 : Blo 806344 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B806895 : Blo 806344 806895 := bstep (se 1 (by rfl) ⟨605171, by rfl⟩ : syracuseStep 806895 = 1210343) B1210343
theorem B1724399 : Blo 806344 1724399 := bstep (se 1 (by rfl) ⟨1293299, by rfl⟩ : syracuseStep 1724399 = 2586599) B2586599
theorem B806907 : Blo 806344 806907 := bstep (se 1 (by rfl) ⟨605180, by rfl⟩ : syracuseStep 806907 = 1210361) B1210361
theorem B1822715 : Blo 806344 1822715 := bstep (se 1 (by rfl) ⟨1367036, by rfl⟩ : syracuseStep 1822715 = 2734073) B2734073
theorem B22073357 : Blo 806344 22073357 := bstep (se 3 (by rfl) ⟨4138754, by rfl⟩ : syracuseStep 22073357 = 8277509) B8277509
theorem B806975 : Blo 806344 806975 := bstep (se 1 (by rfl) ⟨605231, by rfl⟩ : syracuseStep 806975 = 1210463) B1210463
theorem B807015 : Blo 806344 807015 := bstep (se 1 (by rfl) ⟨605261, by rfl⟩ : syracuseStep 807015 = 1210523) B1210523
theorem B1822823 : Blo 806344 1822823 := bstep (se 1 (by rfl) ⟨1367117, by rfl⟩ : syracuseStep 1822823 = 2734235) B2734235
theorem B3068027 : Blo 806344 3068027 := bstep (se 1 (by rfl) ⟨2301020, by rfl⟩ : syracuseStep 3068027 = 4602041) B4602041
theorem B807039 : Blo 806344 807039 := bstep (se 1 (by rfl) ⟨605279, by rfl⟩ : syracuseStep 807039 = 1210559) B1210559
theorem B807067 : Blo 806344 807067 := bstep (se 1 (by rfl) ⟨605300, by rfl⟩ : syracuseStep 807067 = 1210601) B1210601
theorem B1822895 : Blo 806344 1822895 := bstep (se 1 (by rfl) ⟨1367171, by rfl⟩ : syracuseStep 1822895 = 2734343) B2734343
theorem B6541559 : Blo 806344 6541559 := bstep (se 1 (by rfl) ⟨4906169, by rfl⟩ : syracuseStep 6541559 = 9812339) B9812339
theorem B807271 : Blo 806344 807271 := bstep (se 1 (by rfl) ⟨605453, by rfl⟩ : syracuseStep 807271 = 1210907) B1210907
theorem B807323 : Blo 806344 807323 := bstep (se 1 (by rfl) ⟨605492, by rfl⟩ : syracuseStep 807323 = 1210985) B1210985
theorem B1725065 : Blo 806344 1725065 := bstep (se 2 (by rfl) ⟨646899, by rfl⟩ : syracuseStep 1725065 = 1293799) B1293799
theorem B2216585 : Blo 806344 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B807675 : Blo 806344 807675 := bstep (se 1 (by rfl) ⟨605756, by rfl⟩ : syracuseStep 807675 = 1211513) B1211513
theorem B807743 : Blo 806344 807743 := bstep (se 1 (by rfl) ⟨605807, by rfl⟩ : syracuseStep 807743 = 1211615) B1211615
theorem B807771 : Blo 806344 807771 := bstep (se 1 (by rfl) ⟨605828, by rfl⟩ : syracuseStep 807771 = 1211657) B1211657
theorem B807839 : Blo 806344 807839 := bstep (se 1 (by rfl) ⟨605879, by rfl⟩ : syracuseStep 807839 = 1211759) B1211759
theorem B1037215 : Blo 806344 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B807919 : Blo 806344 807919 := bstep (se 1 (by rfl) ⟨605939, by rfl⟩ : syracuseStep 807919 = 1211879) B1211879
theorem B808007 : Blo 806344 808007 := bstep (se 1 (by rfl) ⟨606005, by rfl⟩ : syracuseStep 808007 = 1212011) B1212011
theorem B808091 : Blo 806344 808091 := bstep (se 1 (by rfl) ⟨606068, by rfl⟩ : syracuseStep 808091 = 1212137) B1212137
theorem B2184347 : Blo 806344 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B808187 : Blo 806344 808187 := bstep (se 1 (by rfl) ⟨606140, by rfl⟩ : syracuseStep 808187 = 1212281) B1212281
theorem B808255 : Blo 806344 808255 := bstep (se 1 (by rfl) ⟨606191, by rfl⟩ : syracuseStep 808255 = 1212383) B1212383
theorem B31020407 : Blo 806344 31020407 := bstep (se 1 (by rfl) ⟨23265305, by rfl⟩ : syracuseStep 31020407 = 46530611) B46530611
theorem B808423 : Blo 806344 808423 := bstep (se 1 (by rfl) ⟨606317, by rfl⟩ : syracuseStep 808423 = 1212635) B1212635
theorem B808431 : Blo 806344 808431 := bstep (se 1 (by rfl) ⟨606323, by rfl⟩ : syracuseStep 808431 = 1212647) B1212647
theorem B3888623 : Blo 806344 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B7788089 : Blo 806344 7788089 := bstep (se 2 (by rfl) ⟨2920533, by rfl⟩ : syracuseStep 7788089 = 5841067) B5841067
theorem B808539 : Blo 806344 808539 := bstep (se 1 (by rfl) ⟨606404, by rfl⟩ : syracuseStep 808539 = 1212809) B1212809
theorem B13293179 : Blo 806344 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B808603 : Blo 806344 808603 := bstep (se 1 (by rfl) ⟨606452, by rfl⟩ : syracuseStep 808603 = 1212905) B1212905
theorem B808687 : Blo 806344 808687 := bstep (se 1 (by rfl) ⟨606515, by rfl⟩ : syracuseStep 808687 = 1213031) B1213031
theorem B808775 : Blo 806344 808775 := bstep (se 1 (by rfl) ⟨606581, by rfl⟩ : syracuseStep 808775 = 1213163) B1213163
theorem B808795 : Blo 806344 808795 := bstep (se 1 (by rfl) ⟨606596, by rfl⟩ : syracuseStep 808795 = 1213193) B1213193
theorem B808863 : Blo 806344 808863 := bstep (se 1 (by rfl) ⟨606647, by rfl⟩ : syracuseStep 808863 = 1213295) B1213295
theorem B809031 : Blo 806344 809031 := bstep (se 1 (by rfl) ⟨606773, by rfl⟩ : syracuseStep 809031 = 1213547) B1213547
theorem B6150329 : Blo 806344 6150329 := bstep (se 2 (by rfl) ⟨2306373, by rfl⟩ : syracuseStep 6150329 = 4612747) B4612747
theorem B809191 : Blo 806344 809191 := bstep (se 1 (by rfl) ⟨606893, by rfl⟩ : syracuseStep 809191 = 1213787) B1213787
theorem B15718643 : Blo 806344 15718643 := bstep (se 1 (by rfl) ⟨11788982, by rfl⟩ : syracuseStep 15718643 = 23577965) B23577965
theorem B809375 : Blo 806344 809375 := bstep (se 1 (by rfl) ⟨607031, by rfl⟩ : syracuseStep 809375 = 1214063) B1214063
theorem B6904223 : Blo 806344 6904223 := bstep (se 1 (by rfl) ⟨5178167, by rfl⟩ : syracuseStep 6904223 = 10356335) B10356335
theorem B4151711 : Blo 806344 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B809423 : Blo 806344 809423 := bstep (se 1 (by rfl) ⟨607067, by rfl⟩ : syracuseStep 809423 = 1214135) B1214135
theorem B809447 : Blo 806344 809447 := bstep (se 1 (by rfl) ⟨607085, by rfl⟩ : syracuseStep 809447 = 1214171) B1214171
theorem B809563 : Blo 806344 809563 := bstep (se 1 (by rfl) ⟨607172, by rfl⟩ : syracuseStep 809563 = 1214345) B1214345
theorem B809631 : Blo 806344 809631 := bstep (se 1 (by rfl) ⟨607223, by rfl⟩ : syracuseStep 809631 = 1214447) B1214447
theorem B1366841 : Blo 806344 1366841 := bstep (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) B1025131
theorem B3693383 : Blo 806344 3693383 := bstep (se 1 (by rfl) ⟨2770037, by rfl⟩ : syracuseStep 3693383 = 5540075) B5540075
theorem B809799 : Blo 806344 809799 := bstep (se 1 (by rfl) ⟨607349, by rfl⟩ : syracuseStep 809799 = 1214699) B1214699
theorem B809839 : Blo 806344 809839 := bstep (se 1 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 809839 = 1214759) B1214759
theorem B1366895 : Blo 806344 1366895 := bstep (se 1 (by rfl) ⟨1025171, by rfl⟩ : syracuseStep 1366895 = 2050343) B2050343
theorem B809895 : Blo 806344 809895 := bstep (se 1 (by rfl) ⟨607421, by rfl⟩ : syracuseStep 809895 = 1214843) B1214843
theorem B810075 : Blo 806344 810075 := bstep (se 1 (by rfl) ⟨607556, by rfl⟩ : syracuseStep 810075 = 1215113) B1215113
theorem B810191 : Blo 806344 810191 := bstep (se 1 (by rfl) ⟨607643, by rfl⟩ : syracuseStep 810191 = 1215287) B1215287
theorem B810215 : Blo 806344 810215 := bstep (se 1 (by rfl) ⟨607661, by rfl⟩ : syracuseStep 810215 = 1215323) B1215323
theorem B810311 : Blo 806344 810311 := bstep (se 1 (by rfl) ⟨607733, by rfl⟩ : syracuseStep 810311 = 1215467) B1215467
theorem B4087421 : Blo 806344 4087421 := bstep (se 3 (by rfl) ⟨766391, by rfl⟩ : syracuseStep 4087421 = 1532783) B1532783
theorem B3890855 : Blo 806344 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B909031 : Blo 806344 909031 := bstep (se 1 (by rfl) ⟨681773, by rfl⟩ : syracuseStep 909031 = 1363547) B1363547
theorem B4087583 : Blo 806344 4087583 := bstep (se 1 (by rfl) ⟨3065687, by rfl⟩ : syracuseStep 4087583 = 6131375) B6131375
theorem B3891083 : Blo 806344 3891083 := bstep (se 1 (by rfl) ⟨2918312, by rfl⟩ : syracuseStep 3891083 = 5836625) B5836625
theorem B1532297 : Blo 806344 1532297 := bstep (se 2 (by rfl) ⟨574611, by rfl⟩ : syracuseStep 1532297 = 1149223) B1149223
theorem B4088231 : Blo 806344 4088231 := bstep (se 1 (by rfl) ⟨3066173, by rfl⟩ : syracuseStep 4088231 = 6132347) B6132347
theorem B910111 : Blo 806344 910111 := bstep (se 1 (by rfl) ⟨682583, by rfl⟩ : syracuseStep 910111 = 1365167) B1365167
theorem B11658487 : Blo 806344 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B1729849 : Blo 806344 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B1533467 : Blo 806344 1533467 := bstep (se 1 (by rfl) ⟨1150100, by rfl⟩ : syracuseStep 1533467 = 2300201) B2300201
theorem B911407 : Blo 806344 911407 := bstep (se 1 (by rfl) ⟨683555, by rfl⟩ : syracuseStep 911407 = 1367111) B1367111
theorem B4090337 : Blo 806344 4090337 := bstep (se 2 (by rfl) ⟨1533876, by rfl⟩ : syracuseStep 4090337 = 3067753) B3067753
theorem B1534727 : Blo 806344 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B6908975 : Blo 806344 6908975 := bstep (se 1 (by rfl) ⟨5181731, by rfl⟩ : syracuseStep 6908975 = 10363463) B10363463
theorem B6221161 : Blo 806344 6221161 := bstep (se 2 (by rfl) ⟨2332935, by rfl⟩ : syracuseStep 6221161 = 4665871) B4665871
theorem B1209527 : Blo 806344 1209527 := bstep (se 1 (by rfl) ⟨907145, by rfl⟩ : syracuseStep 1209527 = 1814291) B1814291
theorem B8844551 : Blo 806344 8844551 := bstep (se 1 (by rfl) ⟨6633413, by rfl⟩ : syracuseStep 8844551 = 13266827) B13266827
theorem B1209767 : Blo 806344 1209767 := bstep (se 1 (by rfl) ⟨907325, by rfl⟩ : syracuseStep 1209767 = 1814651) B1814651
theorem B5830055 : Blo 806344 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B6125057 : Blo 806344 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B17036867 : Blo 806344 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B1209947 : Blo 806344 1209947 := bstep (se 1 (by rfl) ⟨907460, by rfl⟩ : syracuseStep 1209947 = 1814921) B1814921
theorem B1210409 : Blo 806344 1210409 := bstep (se 2 (by rfl) ⟨453903, by rfl⟩ : syracuseStep 1210409 = 907807) B907807
theorem B7108667 : Blo 806344 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B1210439 : Blo 806344 1210439 := bstep (se 1 (by rfl) ⟨907829, by rfl⟩ : syracuseStep 1210439 = 1815659) B1815659
theorem B23328971 : Blo 806344 23328971 := bstep (se 1 (by rfl) ⟨17496728, by rfl⟩ : syracuseStep 23328971 = 34993457) B34993457
theorem B2586971 : Blo 806344 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B1210823 : Blo 806344 1210823 := bstep (se 1 (by rfl) ⟨908117, by rfl⟩ : syracuseStep 1210823 = 1816235) B1816235
theorem B1211039 : Blo 806344 1211039 := bstep (se 1 (by rfl) ⟨908279, by rfl⟩ : syracuseStep 1211039 = 1816559) B1816559
theorem B28769033 : Blo 806344 28769033 := bstep (se 2 (by rfl) ⟨10788387, by rfl⟩ : syracuseStep 28769033 = 21576775) B21576775
theorem B1211183 : Blo 806344 1211183 := bstep (se 1 (by rfl) ⟨908387, by rfl⟩ : syracuseStep 1211183 = 1816775) B1816775
theorem B35519309 : Blo 806344 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B1211303 : Blo 806344 1211303 := bstep (se 1 (by rfl) ⟨908477, by rfl⟩ : syracuseStep 1211303 = 1816955) B1816955
theorem B1211483 : Blo 806344 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B1211855 : Blo 806344 1211855 := bstep (se 1 (by rfl) ⟨908891, by rfl⟩ : syracuseStep 1211855 = 1817783) B1817783
theorem B1212239 : Blo 806344 1212239 := bstep (se 1 (by rfl) ⟨909179, by rfl⟩ : syracuseStep 1212239 = 1818359) B1818359
theorem B1212359 : Blo 806344 1212359 := bstep (se 1 (by rfl) ⟨909269, by rfl⟩ : syracuseStep 1212359 = 1818539) B1818539
theorem B1212671 : Blo 806344 1212671 := bstep (se 1 (by rfl) ⟨909503, by rfl⟩ : syracuseStep 1212671 = 1819007) B1819007
theorem B1212827 : Blo 806344 1212827 := bstep (se 1 (by rfl) ⟨909620, by rfl⟩ : syracuseStep 1212827 = 1819241) B1819241
theorem B1213247 : Blo 806344 1213247 := bstep (se 1 (by rfl) ⟨909935, by rfl⟩ : syracuseStep 1213247 = 1819871) B1819871
theorem B1213391 : Blo 806344 1213391 := bstep (se 1 (by rfl) ⟨910043, by rfl⟩ : syracuseStep 1213391 = 1820087) B1820087
theorem B1213481 : Blo 806344 1213481 := bstep (se 2 (by rfl) ⟨455055, by rfl⟩ : syracuseStep 1213481 = 910111) B910111
theorem B1311815 : Blo 806344 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B1213511 : Blo 806344 1213511 := bstep (se 1 (by rfl) ⟨910133, by rfl⟩ : syracuseStep 1213511 = 1820267) B1820267
theorem B1213691 : Blo 806344 1213691 := bstep (se 1 (by rfl) ⟨910268, by rfl⟩ : syracuseStep 1213691 = 1820537) B1820537
theorem B1213979 : Blo 806344 1213979 := bstep (se 1 (by rfl) ⟨910484, by rfl⟩ : syracuseStep 1213979 = 1820969) B1820969
theorem B1214363 : Blo 806344 1214363 := bstep (se 1 (by rfl) ⟨910772, by rfl⟩ : syracuseStep 1214363 = 1821545) B1821545
theorem B1214399 : Blo 806344 1214399 := bstep (se 1 (by rfl) ⟨910799, by rfl⟩ : syracuseStep 1214399 = 1821599) B1821599
theorem B2590699 : Blo 806344 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B2459983 : Blo 806344 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B10520927 : Blo 806344 10520927 := bstep (se 1 (by rfl) ⟨7890695, by rfl⟩ : syracuseStep 10520927 = 15781391) B15781391
theorem B1215023 : Blo 806344 1215023 := bstep (se 1 (by rfl) ⟨911267, by rfl⟩ : syracuseStep 1215023 = 1822535) B1822535
theorem B1149599 : Blo 806344 1149599 := bstep (se 1 (by rfl) ⟨862199, by rfl⟩ : syracuseStep 1149599 = 1724399) B1724399
theorem B1215143 : Blo 806344 1215143 := bstep (se 1 (by rfl) ⟨911357, by rfl⟩ : syracuseStep 1215143 = 1822715) B1822715
theorem B1215209 : Blo 806344 1215209 := bstep (se 2 (by rfl) ⟨455703, by rfl⟩ : syracuseStep 1215209 = 911407) B911407
theorem B1215215 : Blo 806344 1215215 := bstep (se 1 (by rfl) ⟨911411, by rfl⟩ : syracuseStep 1215215 = 1822823) B1822823
theorem B1215263 : Blo 806344 1215263 := bstep (se 1 (by rfl) ⟨911447, by rfl⟩ : syracuseStep 1215263 = 1822895) B1822895
theorem B37882691 : Blo 806344 37882691 := bstep (se 1 (by rfl) ⟨28412018, by rfl⟩ : syracuseStep 37882691 = 56824037) B56824037
theorem B4361039 : Blo 806344 4361039 := bstep (se 1 (by rfl) ⟨3270779, by rfl⟩ : syracuseStep 4361039 = 6541559) B6541559
theorem B1150043 : Blo 806344 1150043 := bstep (se 1 (by rfl) ⟨862532, by rfl⟩ : syracuseStep 1150043 = 1725065) B1725065
theorem B20680271 : Blo 806344 20680271 := bstep (se 1 (by rfl) ⟨15510203, by rfl⟩ : syracuseStep 20680271 = 31020407) B31020407
theorem B2592415 : Blo 806344 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B4100219 : Blo 806344 4100219 := bstep (se 1 (by rfl) ⟨3075164, by rfl⟩ : syracuseStep 4100219 = 6150329) B6150329
theorem B5247443 : Blo 806344 5247443 := bstep (se 1 (by rfl) ⟨3935582, by rfl⟩ : syracuseStep 5247443 = 7871165) B7871165
theorem B8294881 : Blo 806344 8294881 := bstep (se 2 (by rfl) ⟨3110580, by rfl⟩ : syracuseStep 8294881 = 6221161) B6221161
theorem B2462255 : Blo 806344 2462255 := bstep (se 1 (by rfl) ⟨1846691, by rfl⟩ : syracuseStep 2462255 = 3693383) B3693383
theorem B1577659 : Blo 806344 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B604771093 : Blo 806344 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B2724947 : Blo 806344 2724947 := bstep (se 1 (by rfl) ⟨2043710, by rfl⟩ : syracuseStep 2724947 = 4087421) B4087421
theorem B922735 : Blo 806344 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B2593903 : Blo 806344 2593903 := bstep (se 1 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 2593903 = 3890855) B3890855
theorem B2725055 : Blo 806344 2725055 := bstep (se 1 (by rfl) ⟨2043791, by rfl⟩ : syracuseStep 2725055 = 4087583) B4087583
theorem B2725487 : Blo 806344 2725487 := bstep (se 1 (by rfl) ⟨2044115, by rfl⟩ : syracuseStep 2725487 = 4088231) B4088231
theorem B1022311 : Blo 806344 1022311 := bstep (se 1 (by rfl) ⟨766733, by rfl⟩ : syracuseStep 1022311 = 1533467) B1533467
theorem B1382953 : Blo 806344 1382953 := bstep (se 2 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 1382953 = 1037215) B1037215
theorem B13966091 : Blo 806344 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B2300861 : Blo 806344 2300861 := bstep (se 3 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 2300861 = 862823) B862823
theorem B41917409 : Blo 806344 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B2726891 : Blo 806344 2726891 := bstep (se 1 (by rfl) ⟨2045168, by rfl⟩ : syracuseStep 2726891 = 4090337) B4090337
theorem B6134777 : Blo 806344 6134777 := bstep (se 2 (by rfl) ⟨2300541, by rfl⟩ : syracuseStep 6134777 = 4601083) B4601083
theorem B4595251 : Blo 806344 4595251 := bstep (se 1 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 4595251 = 6892877) B6892877
theorem B3875015 : Blo 806344 3875015 := bstep (se 1 (by rfl) ⟨2906261, by rfl⟩ : syracuseStep 3875015 = 5812523) B5812523
theorem B5186267 : Blo 806344 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B4924637 : Blo 806344 4924637 := bstep (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) B1846739
theorem B3679607 : Blo 806344 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B2041595 : Blo 806344 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B19179355 : Blo 806344 19179355 := bstep (se 1 (by rfl) ⟨14384516, by rfl⟩ : syracuseStep 19179355 = 28769033) B28769033
theorem B58862285 : Blo 806344 58862285 := bstep (se 3 (by rfl) ⟨11036678, by rfl⟩ : syracuseStep 58862285 = 22073357) B22073357
theorem B5253907 : Blo 806344 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B4598693 : Blo 806344 4598693 := bstep (se 4 (by rfl) ⟨431127, by rfl⟩ : syracuseStep 4598693 = 862255) B862255
theorem B37334519 : Blo 806344 37334519 := bstep (se 1 (by rfl) ⟨28000889, by rfl⟩ : syracuseStep 37334519 = 56001779) B56001779
theorem B11185897 : Blo 806344 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B4599625 : Blo 806344 4599625 := bstep (se 2 (by rfl) ⟨1724859, by rfl⟩ : syracuseStep 4599625 = 3449719) B3449719
theorem B3157903 : Blo 806344 3157903 := bstep (se 1 (by rfl) ⟨2368427, by rfl⟩ : syracuseStep 3157903 = 4736855) B4736855
theorem B2044187 : Blo 806344 2044187 := bstep (se 1 (by rfl) ⟨1533140, by rfl⟩ : syracuseStep 2044187 = 3066281) B3066281
theorem B2732345 : Blo 806344 2732345 := bstep (se 2 (by rfl) ⟨1024629, by rfl⟩ : syracuseStep 2732345 = 2049259) B2049259
theorem B15544649 : Blo 806344 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B5910893 : Blo 806344 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B2306465 : Blo 806344 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B2044703 : Blo 806344 2044703 := bstep (se 1 (by rfl) ⟨1533527, by rfl⟩ : syracuseStep 2044703 = 3067055) B3067055
theorem B1815335 : Blo 806344 1815335 := bstep (se 1 (by rfl) ⟨1361501, by rfl⟩ : syracuseStep 1815335 = 2723003) B2723003
theorem B1815353 : Blo 806344 1815353 := bstep (se 2 (by rfl) ⟨680757, by rfl⟩ : syracuseStep 1815353 = 1361515) B1361515
theorem B1749919 : Blo 806344 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1815713 : Blo 806344 1815713 := bstep (se 2 (by rfl) ⟨680892, by rfl⟩ : syracuseStep 1815713 = 1361785) B1361785
theorem B2045351 : Blo 806344 2045351 := bstep (se 1 (by rfl) ⟨1534013, by rfl⟩ : syracuseStep 2045351 = 3068027) B3068027
theorem B1815983 : Blo 806344 1815983 := bstep (se 1 (by rfl) ⟨1361987, by rfl⟩ : syracuseStep 1815983 = 2723975) B2723975
theorem B1816091 : Blo 806344 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B1816271 : Blo 806344 1816271 := bstep (se 1 (by rfl) ⟨1362203, by rfl⟩ : syracuseStep 1816271 = 2724407) B2724407
theorem B5814139 : Blo 806344 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B1456231 : Blo 806344 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B5192059 : Blo 806344 5192059 := bstep (se 1 (by rfl) ⟨3894044, by rfl⟩ : syracuseStep 5192059 = 7788089) B7788089
theorem B8862119 : Blo 806344 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B1817063 : Blo 806344 1817063 := bstep (se 1 (by rfl) ⟨1362797, by rfl⟩ : syracuseStep 1817063 = 2725595) B2725595
theorem B2734721 : Blo 806344 2734721 := bstep (se 2 (by rfl) ⟨1025520, by rfl⟩ : syracuseStep 2734721 = 2051041) B2051041
theorem B2734775 : Blo 806344 2734775 := bstep (se 1 (by rfl) ⟨2051081, by rfl⟩ : syracuseStep 2734775 = 4102163) B4102163
theorem B3455905 : Blo 806344 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B4602815 : Blo 806344 4602815 := bstep (se 1 (by rfl) ⟨3452111, by rfl⟩ : syracuseStep 4602815 = 6904223) B6904223
theorem B2767807 : Blo 806344 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B3455939 : Blo 806344 3455939 := bstep (se 1 (by rfl) ⟨2591954, by rfl⟩ : syracuseStep 3455939 = 5183909) B5183909
theorem B1327241 : Blo 806344 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B20759003 : Blo 806344 20759003 := bstep (se 1 (by rfl) ⟨15569252, by rfl⟩ : syracuseStep 20759003 = 31138505) B31138505
theorem B3064351 : Blo 806344 3064351 := bstep (se 1 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 3064351 = 4596527) B4596527
theorem B1361947 : Blo 806344 1361947 := bstep (se 1 (by rfl) ⟨1021460, by rfl⟩ : syracuseStep 1361947 = 2042921) B2042921
theorem B1820699 : Blo 806344 1820699 := bstep (se 1 (by rfl) ⟨1365524, by rfl⟩ : syracuseStep 1820699 = 2731049) B2731049
theorem B4605983 : Blo 806344 4605983 := bstep (se 1 (by rfl) ⟨3454487, by rfl⟩ : syracuseStep 4605983 = 6908975) B6908975
theorem B1820879 : Blo 806344 1820879 := bstep (se 1 (by rfl) ⟨1365659, by rfl⟩ : syracuseStep 1820879 = 2731319) B2731319
theorem B1296695 : Blo 806344 1296695 := bstep (se 1 (by rfl) ⟨972521, by rfl⟩ : syracuseStep 1296695 = 1945043) B1945043
theorem B1821275 : Blo 806344 1821275 := bstep (se 1 (by rfl) ⟨1365956, by rfl⟩ : syracuseStep 1821275 = 2731913) B2731913
theorem B7785629 : Blo 806344 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B9227681 : Blo 806344 9227681 := bstep (se 2 (by rfl) ⟨3460380, by rfl⟩ : syracuseStep 9227681 = 6920761) B6920761
theorem B806351 : Blo 806344 806351 := bstep (se 1 (by rfl) ⟨604763, by rfl⟩ : syracuseStep 806351 = 1209527) B1209527
theorem B806511 : Blo 806344 806511 := bstep (se 1 (by rfl) ⟨604883, by rfl⟩ : syracuseStep 806511 = 1209767) B1209767
theorem B3886703 : Blo 806344 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B4083371 : Blo 806344 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B11357911 : Blo 806344 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B806631 : Blo 806344 806631 := bstep (se 1 (by rfl) ⟨604973, by rfl⟩ : syracuseStep 806631 = 1209947) B1209947
theorem B3886973 : Blo 806344 3886973 := bstep (se 3 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 3886973 = 1457615) B1457615
theorem B806939 : Blo 806344 806939 := bstep (se 1 (by rfl) ⟨605204, by rfl⟩ : syracuseStep 806939 = 1210409) B1210409
theorem B4739111 : Blo 806344 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B806959 : Blo 806344 806959 := bstep (se 1 (by rfl) ⟨605219, by rfl⟩ : syracuseStep 806959 = 1210439) B1210439
theorem B15552647 : Blo 806344 15552647 := bstep (se 1 (by rfl) ⟨11664485, by rfl⟩ : syracuseStep 15552647 = 23328971) B23328971
theorem B1724647 : Blo 806344 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B807215 : Blo 806344 807215 := bstep (se 1 (by rfl) ⟨605411, by rfl⟩ : syracuseStep 807215 = 1210823) B1210823
theorem B807359 : Blo 806344 807359 := bstep (se 1 (by rfl) ⟨605519, by rfl⟩ : syracuseStep 807359 = 1211039) B1211039
theorem B807455 : Blo 806344 807455 := bstep (se 1 (by rfl) ⟨605591, by rfl⟩ : syracuseStep 807455 = 1211183) B1211183
theorem B23679539 : Blo 806344 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B807535 : Blo 806344 807535 := bstep (se 1 (by rfl) ⟨605651, by rfl⟩ : syracuseStep 807535 = 1211303) B1211303
theorem B807655 : Blo 806344 807655 := bstep (se 1 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 807655 = 1211483) B1211483
theorem B807903 : Blo 806344 807903 := bstep (se 1 (by rfl) ⟨605927, by rfl⟩ : syracuseStep 807903 = 1211855) B1211855
theorem B10376221 : Blo 806344 10376221 := bstep (se 3 (by rfl) ⟨1945541, by rfl⟩ : syracuseStep 10376221 = 3891083) B3891083
theorem B3068999 : Blo 806344 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B808159 : Blo 806344 808159 := bstep (se 1 (by rfl) ⟨606119, by rfl⟩ : syracuseStep 808159 = 1212239) B1212239
theorem B808239 : Blo 806344 808239 := bstep (se 1 (by rfl) ⟨606179, by rfl⟩ : syracuseStep 808239 = 1212359) B1212359
theorem B10376585 : Blo 806344 10376585 := bstep (se 2 (by rfl) ⟨3891219, by rfl⟩ : syracuseStep 10376585 = 7782439) B7782439
theorem B6903265 : Blo 806344 6903265 := bstep (se 2 (by rfl) ⟨2588724, by rfl⟩ : syracuseStep 6903265 = 5177449) B5177449
theorem B808479 : Blo 806344 808479 := bstep (se 1 (by rfl) ⟨606359, by rfl⟩ : syracuseStep 808479 = 1212719) B1212719
theorem B1365673 : Blo 806344 1365673 := bstep (se 2 (by rfl) ⟨512127, by rfl⟩ : syracuseStep 1365673 = 1024255) B1024255
theorem B808639 : Blo 806344 808639 := bstep (se 1 (by rfl) ⟨606479, by rfl⟩ : syracuseStep 808639 = 1212959) B1212959
theorem B3069683 : Blo 806344 3069683 := bstep (se 1 (by rfl) ⟨2302262, by rfl⟩ : syracuseStep 3069683 = 4604525) B4604525
theorem B4904707 : Blo 806344 4904707 := bstep (se 1 (by rfl) ⟨3678530, by rfl⟩ : syracuseStep 4904707 = 7357061) B7357061
theorem B1726535 : Blo 806344 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B809087 : Blo 806344 809087 := bstep (se 1 (by rfl) ⟨606815, by rfl⟩ : syracuseStep 809087 = 1213631) B1213631
theorem B809183 : Blo 806344 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B809243 : Blo 806344 809243 := bstep (se 1 (by rfl) ⟨606932, by rfl⟩ : syracuseStep 809243 = 1213865) B1213865
theorem B18897229 : Blo 806344 18897229 := bstep (se 3 (by rfl) ⟨3543230, by rfl⟩ : syracuseStep 18897229 = 7086461) B7086461
theorem B4086125 : Blo 806344 4086125 := bstep (se 3 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 4086125 = 1532297) B1532297
theorem B809343 : Blo 806344 809343 := bstep (se 1 (by rfl) ⟨607007, by rfl⟩ : syracuseStep 809343 = 1214015) B1214015
theorem B809371 : Blo 806344 809371 := bstep (se 1 (by rfl) ⟨607028, by rfl⟩ : syracuseStep 809371 = 1214057) B1214057
theorem B809663 : Blo 806344 809663 := bstep (se 1 (by rfl) ⟨607247, by rfl⟩ : syracuseStep 809663 = 1214495) B1214495
theorem B908095 : Blo 806344 908095 := bstep (se 1 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 908095 = 1362143) B1362143
theorem B809791 : Blo 806344 809791 := bstep (se 1 (by rfl) ⟨607343, by rfl⟩ : syracuseStep 809791 = 1214687) B1214687
theorem B809831 : Blo 806344 809831 := bstep (se 1 (by rfl) ⟨607373, by rfl⟩ : syracuseStep 809831 = 1214747) B1214747
theorem B810047 : Blo 806344 810047 := bstep (se 1 (by rfl) ⟨607535, by rfl⟩ : syracuseStep 810047 = 1215071) B1215071
theorem B1367131 : Blo 806344 1367131 := bstep (se 1 (by rfl) ⟨1025348, by rfl⟩ : syracuseStep 1367131 = 2050697) B2050697
theorem B1039451 : Blo 806344 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B810235 : Blo 806344 810235 := bstep (se 1 (by rfl) ⟨607676, by rfl⟩ : syracuseStep 810235 = 1215353) B1215353
theorem B810267 : Blo 806344 810267 := bstep (se 1 (by rfl) ⟨607700, by rfl⟩ : syracuseStep 810267 = 1215401) B1215401
theorem B908671 : Blo 806344 908671 := bstep (se 1 (by rfl) ⟨681503, by rfl⟩ : syracuseStep 908671 = 1363007) B1363007
theorem B3104225 : Blo 806344 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B4906603 : Blo 806344 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B7757531 : Blo 806344 7757531 := bstep (se 1 (by rfl) ⟨5818148, by rfl⟩ : syracuseStep 7757531 = 11636297) B11636297
theorem B13098935 : Blo 806344 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B4153535 : Blo 806344 4153535 := bstep (se 1 (by rfl) ⟨3115151, by rfl⟩ : syracuseStep 4153535 = 6230303) B6230303
theorem B9199979 : Blo 806344 9199979 := bstep (se 1 (by rfl) ⟨6899984, by rfl⟩ : syracuseStep 9199979 = 13799969) B13799969
theorem B13132151 : Blo 806344 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B1729183 : Blo 806344 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B23257925 : Blo 806344 23257925 := bstep (se 4 (by rfl) ⟨2180430, by rfl⟩ : syracuseStep 23257925 = 4360861) B4360861
theorem B2909087 : Blo 806344 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B1729439 : Blo 806344 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B1533163 : Blo 806344 1533163 := bstep (se 1 (by rfl) ⟨1149872, by rfl⟩ : syracuseStep 1533163 = 2299745) B2299745
theorem B10479095 : Blo 806344 10479095 := bstep (se 1 (by rfl) ⟨7859321, by rfl⟩ : syracuseStep 10479095 = 15718643) B15718643
theorem B911227 : Blo 806344 911227 := bstep (se 1 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 911227 = 1366841) B1366841
theorem B911263 : Blo 806344 911263 := bstep (se 1 (by rfl) ⟨683447, by rfl⟩ : syracuseStep 911263 = 1366895) B1366895
theorem B3074057 : Blo 806344 3074057 := bstep (se 2 (by rfl) ⟨1152771, by rfl⟩ : syracuseStep 3074057 = 2305543) B2305543
theorem B1534439 : Blo 806344 1534439 := bstep (se 1 (by rfl) ⟨1150829, by rfl⟩ : syracuseStep 1534439 = 2301659) B2301659
theorem B5828321 : Blo 806344 5828321 := bstep (se 2 (by rfl) ⟨2185620, by rfl⟩ : syracuseStep 5828321 = 4371241) B4371241
theorem B6910373 : Blo 806344 6910373 := bstep (se 4 (by rfl) ⟨647847, by rfl⟩ : syracuseStep 6910373 = 1295695) B1295695
theorem B4092605 : Blo 806344 4092605 := bstep (se 3 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 4092605 = 1534727) B1534727
theorem B1209839 : Blo 806344 1209839 := bstep (se 1 (by rfl) ⟨907379, by rfl⟩ : syracuseStep 1209839 = 1814759) B1814759
theorem B1209959 : Blo 806344 1209959 := bstep (se 1 (by rfl) ⟨907469, by rfl⟩ : syracuseStep 1209959 = 1814939) B1814939
theorem B1210415 : Blo 806344 1210415 := bstep (se 1 (by rfl) ⟨907811, by rfl⟩ : syracuseStep 1210415 = 1815623) B1815623
theorem B9205811 : Blo 806344 9205811 := bstep (se 1 (by rfl) ⟨6904358, by rfl⟩ : syracuseStep 9205811 = 13808717) B13808717
theorem B2914451 : Blo 806344 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B1210535 : Blo 806344 1210535 := bstep (se 1 (by rfl) ⟨907901, by rfl⟩ : syracuseStep 1210535 = 1815803) B1815803
theorem B5896367 : Blo 806344 5896367 := bstep (se 1 (by rfl) ⟨4422275, by rfl⟩ : syracuseStep 5896367 = 8844551) B8844551
theorem B1210679 : Blo 806344 1210679 := bstep (se 1 (by rfl) ⟨908009, by rfl⟩ : syracuseStep 1210679 = 1816019) B1816019
theorem B1210859 : Blo 806344 1210859 := bstep (se 1 (by rfl) ⟨908144, by rfl⟩ : syracuseStep 1210859 = 1816289) B1816289
theorem B8288851 : Blo 806344 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B1211207 : Blo 806344 1211207 := bstep (se 1 (by rfl) ⟨908405, by rfl⟩ : syracuseStep 1211207 = 1816811) B1816811
theorem B7372093 : Blo 806344 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B1212041 : Blo 806344 1212041 := bstep (se 2 (by rfl) ⟨454515, by rfl⟩ : syracuseStep 1212041 = 909031) B909031
theorem B1212071 : Blo 806344 1212071 := bstep (se 1 (by rfl) ⟨909053, by rfl⟩ : syracuseStep 1212071 = 1818107) B1818107
theorem B4095683 : Blo 806344 4095683 := bstep (se 1 (by rfl) ⟨3071762, by rfl⟩ : syracuseStep 4095683 = 6143525) B6143525
theorem B1212191 : Blo 806344 1212191 := bstep (se 1 (by rfl) ⟨909143, by rfl⟩ : syracuseStep 1212191 = 1818287) B1818287
theorem B1212251 : Blo 806344 1212251 := bstep (se 1 (by rfl) ⟨909188, by rfl⟩ : syracuseStep 1212251 = 1818377) B1818377
theorem B884827 : Blo 806344 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B1213799 : Blo 806344 1213799 := bstep (se 1 (by rfl) ⟨910349, by rfl⟩ : syracuseStep 1213799 = 1820699) B1820699
theorem B1213919 : Blo 806344 1213919 := bstep (se 1 (by rfl) ⟨910439, by rfl⟩ : syracuseStep 1213919 = 1820879) B1820879
theorem B7013951 : Blo 806344 7013951 := bstep (se 1 (by rfl) ⟨5260463, by rfl⟩ : syracuseStep 7013951 = 10520927) B10520927
theorem B1214183 : Blo 806344 1214183 := bstep (se 1 (by rfl) ⟨910637, by rfl⟩ : syracuseStep 1214183 = 1821275) B1821275
theorem B2591135 : Blo 806344 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B2722247 : Blo 806344 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B1214969 : Blo 806344 1214969 := bstep (se 2 (by rfl) ⟨455613, by rfl⟩ : syracuseStep 1214969 = 911227) B911227
theorem B1215017 : Blo 806344 1215017 := bstep (se 2 (by rfl) ⟨455631, by rfl⟩ : syracuseStep 1215017 = 911263) B911263
theorem B2591315 : Blo 806344 2591315 := bstep (se 1 (by rfl) ⟨1943486, by rfl⟩ : syracuseStep 2591315 = 3886973) B3886973
theorem B1641503 : Blo 806344 1641503 := bstep (se 1 (by rfl) ⟨1231127, by rfl⟩ : syracuseStep 1641503 = 2462255) B2462255
theorem B3279977 : Blo 806344 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B6917723 : Blo 806344 6917723 := bstep (se 1 (by rfl) ⟨5188292, by rfl⟩ : syracuseStep 6917723 = 10376585) B10376585
theorem B1151023 : Blo 806344 1151023 := bstep (se 1 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 1151023 = 1726535) B1726535
theorem B2724083 : Blo 806344 2724083 := bstep (se 1 (by rfl) ⟨2043062, by rfl⟩ : syracuseStep 2724083 = 4086125) B4086125
theorem B9310727 : Blo 806344 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B15143881 : Blo 806344 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B14914529 : Blo 806344 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B2069483 : Blo 806344 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B6132833 : Blo 806344 6132833 := bstep (se 2 (by rfl) ⟨2299812, by rfl⟩ : syracuseStep 6132833 = 4599625) B4599625
theorem B6133319 : Blo 806344 6133319 := bstep (se 1 (by rfl) ⟨4599989, by rfl⟩ : syracuseStep 6133319 = 9199979) B9199979
theorem B8754767 : Blo 806344 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B2299529 : Blo 806344 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B15505283 : Blo 806344 15505283 := bstep (se 1 (by rfl) ⟨11628962, by rfl⟩ : syracuseStep 15505283 = 23257925) B23257925
theorem B1939391 : Blo 806344 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B1152959 : Blo 806344 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B3283091 : Blo 806344 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B2103545 : Blo 806344 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B6986063 : Blo 806344 6986063 := bstep (se 1 (by rfl) ⟨5239547, by rfl⟩ : syracuseStep 6986063 = 10479095) B10479095
theorem B2333225 : Blo 806344 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B13834961 : Blo 806344 13834961 := bstep (se 2 (by rfl) ⟨5188110, by rfl⟩ : syracuseStep 13834961 = 10376221) B10376221
theorem B1022959 : Blo 806344 1022959 := bstep (se 1 (by rfl) ⟨767219, by rfl⟩ : syracuseStep 1022959 = 1534439) B1534439
theorem B1941641 : Blo 806344 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B10363099 : Blo 806344 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B3940595 : Blo 806344 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B2728403 : Blo 806344 2728403 := bstep (se 1 (by rfl) ⟨2046302, by rfl⟩ : syracuseStep 2728403 = 4092605) B4092605
theorem B6922745 : Blo 806344 6922745 := bstep (se 2 (by rfl) ⟨2596029, by rfl⟩ : syracuseStep 6922745 = 5192059) B5192059
theorem B1843937 : Blo 806344 1843937 := bstep (se 2 (by rfl) ⟨691476, by rfl⟩ : syracuseStep 1843937 = 1382953) B1382953
theorem B11051801 : Blo 806344 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B6137207 : Blo 806344 6137207 := bstep (se 1 (by rfl) ⟨4602905, by rfl⟩ : syracuseStep 6137207 = 9205811) B9205811
theorem B1942967 : Blo 806344 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B5908079 : Blo 806344 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B15542189 : Blo 806344 15542189 := bstep (se 3 (by rfl) ⟨2914160, by rfl⟩ : syracuseStep 15542189 = 5828321) B5828321
theorem B2303959 : Blo 806344 2303959 := bstep (se 1 (by rfl) ⟨1727969, by rfl⟩ : syracuseStep 2303959 = 3455939) B3455939
theorem B2730455 : Blo 806344 2730455 := bstep (se 1 (by rfl) ⟨2047841, by rfl⟩ : syracuseStep 2730455 = 4095683) B4095683
theorem B13839335 : Blo 806344 13839335 := bstep (se 1 (by rfl) ⟨10379501, by rfl⟩ : syracuseStep 13839335 = 20759003) B20759003
theorem B2305577 : Blo 806344 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B2044217 : Blo 806344 2044217 := bstep (se 2 (by rfl) ⟨766581, by rfl⟩ : syracuseStep 2044217 = 1533163) B1533163
theorem B5190419 : Blo 806344 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B25572473 : Blo 806344 25572473 := bstep (se 2 (by rfl) ⟨9589677, by rfl⟩ : syracuseStep 25572473 = 19179355) B19179355
theorem B3454265 : Blo 806344 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B3159407 : Blo 806344 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1815929 : Blo 806344 1815929 := bstep (se 2 (by rfl) ⟨680973, by rfl⟩ : syracuseStep 1815929 = 1361947) B1361947
theorem B2733479 : Blo 806344 2733479 := bstep (se 1 (by rfl) ⟨2050109, by rfl⟩ : syracuseStep 2733479 = 4100219) B4100219
theorem B10368431 : Blo 806344 10368431 := bstep (se 1 (by rfl) ⟨7776323, by rfl⟩ : syracuseStep 10368431 = 15552647) B15552647
theorem B2045999 : Blo 806344 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B1816631 : Blo 806344 1816631 := bstep (se 1 (by rfl) ⟨1362473, by rfl⟩ : syracuseStep 1816631 = 2724947) B2724947
theorem B1816703 : Blo 806344 1816703 := bstep (se 1 (by rfl) ⟨1362527, by rfl⟩ : syracuseStep 1816703 = 2725055) B2725055
theorem B9812285 : Blo 806344 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B1816991 : Blo 806344 1816991 := bstep (se 1 (by rfl) ⟨1362743, by rfl⟩ : syracuseStep 1816991 = 2725487) B2725487
theorem B2046455 : Blo 806344 2046455 := bstep (se 1 (by rfl) ⟨1534841, by rfl⟩ : syracuseStep 2046455 = 3069683) B3069683
theorem B1817927 : Blo 806344 1817927 := bstep (se 1 (by rfl) ⟨1363445, by rfl⟩ : syracuseStep 1817927 = 2726891) B2726891
theorem B4210537 : Blo 806344 4210537 := bstep (se 2 (by rfl) ⟨1578951, by rfl⟩ : syracuseStep 4210537 = 3157903) B3157903
theorem B8732623 : Blo 806344 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B2769023 : Blo 806344 2769023 := bstep (se 1 (by rfl) ⟨2076767, by rfl⟩ : syracuseStep 2769023 = 4153535) B4153535
theorem B3457511 : Blo 806344 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B11059841 : Blo 806344 11059841 := bstep (se 2 (by rfl) ⟨4147440, by rfl⟩ : syracuseStep 11059841 = 8294881) B8294881
theorem B3457853 : Blo 806344 3457853 := bstep (se 3 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 3457853 = 1296695) B1296695
theorem B1361063 : Blo 806344 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B2049371 : Blo 806344 2049371 := bstep (se 1 (by rfl) ⟨1537028, by rfl⟩ : syracuseStep 2049371 = 3074057) B3074057
theorem B1230313 : Blo 806344 1230313 := bstep (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) B922735
theorem B3458537 : Blo 806344 3458537 := bstep (se 2 (by rfl) ⟨1296951, by rfl⟩ : syracuseStep 3458537 = 2593903) B2593903
theorem B3065597 : Blo 806344 3065597 := bstep (se 3 (by rfl) ⟨574799, by rfl⟩ : syracuseStep 3065597 = 1149599) B1149599
theorem B39241523 : Blo 806344 39241523 := bstep (se 1 (by rfl) ⟨29431142, by rfl⟩ : syracuseStep 39241523 = 58862285) B58862285
theorem B3065795 : Blo 806344 3065795 := bstep (se 1 (by rfl) ⟨2299346, by rfl⟩ : syracuseStep 3065795 = 4598693) B4598693
theorem B1820897 : Blo 806344 1820897 := bstep (se 2 (by rfl) ⟨682836, by rfl⟩ : syracuseStep 1820897 = 1365673) B1365673
theorem B24889679 : Blo 806344 24889679 := bstep (se 1 (by rfl) ⟨18667259, by rfl⟩ : syracuseStep 24889679 = 37334519) B37334519
theorem B6539609 : Blo 806344 6539609 := bstep (se 2 (by rfl) ⟨2452353, by rfl⟩ : syracuseStep 6539609 = 4904707) B4904707
theorem B7752185 : Blo 806344 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B1362791 : Blo 806344 1362791 := bstep (se 1 (by rfl) ⟨1022093, by rfl⟩ : syracuseStep 1362791 = 2044187) B2044187
theorem B1821563 : Blo 806344 1821563 := bstep (se 1 (by rfl) ⟨1366172, by rfl⟩ : syracuseStep 1821563 = 2732345) B2732345
theorem B3066781 : Blo 806344 3066781 := bstep (se 3 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 3066781 = 1150043) B1150043
theorem B2771869 : Blo 806344 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B4606915 : Blo 806344 4606915 := bstep (se 1 (by rfl) ⟨3455186, by rfl⟩ : syracuseStep 4606915 = 6910373) B6910373
theorem B1363081 : Blo 806344 1363081 := bstep (se 2 (by rfl) ⟨511155, by rfl⟩ : syracuseStep 1363081 = 1022311) B1022311
theorem B1363135 : Blo 806344 1363135 := bstep (se 1 (by rfl) ⟨1022351, by rfl⟩ : syracuseStep 1363135 = 2044703) B2044703
theorem B1363567 : Blo 806344 1363567 := bstep (se 1 (by rfl) ⟨1022675, by rfl⟩ : syracuseStep 1363567 = 2045351) B2045351
theorem B806559 : Blo 806344 806559 := bstep (se 1 (by rfl) ⟨604919, by rfl⟩ : syracuseStep 806559 = 1209839) B1209839
theorem B806639 : Blo 806344 806639 := bstep (se 1 (by rfl) ⟨604979, by rfl⟩ : syracuseStep 806639 = 1209959) B1209959
theorem B4607873 : Blo 806344 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B3690409 : Blo 806344 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B806943 : Blo 806344 806943 := bstep (se 1 (by rfl) ⟨605207, by rfl⟩ : syracuseStep 806943 = 1210415) B1210415
theorem B807023 : Blo 806344 807023 := bstep (se 1 (by rfl) ⟨605267, by rfl⟩ : syracuseStep 807023 = 1210535) B1210535
theorem B1822841 : Blo 806344 1822841 := bstep (se 2 (by rfl) ⟨683565, by rfl⟩ : syracuseStep 1822841 = 1367131) B1367131
theorem B807119 : Blo 806344 807119 := bstep (se 1 (by rfl) ⟨605339, by rfl⟩ : syracuseStep 807119 = 1210679) B1210679
theorem B807239 : Blo 806344 807239 := bstep (se 1 (by rfl) ⟨605429, by rfl⟩ : syracuseStep 807239 = 1210859) B1210859
theorem B1823147 : Blo 806344 1823147 := bstep (se 1 (by rfl) ⟨1367360, by rfl⟩ : syracuseStep 1823147 = 2734721) B2734721
theorem B1823183 : Blo 806344 1823183 := bstep (se 1 (by rfl) ⟨1367387, by rfl⟩ : syracuseStep 1823183 = 2734775) B2734775
theorem B807471 : Blo 806344 807471 := bstep (se 1 (by rfl) ⟨605603, by rfl⟩ : syracuseStep 807471 = 1211207) B1211207
theorem B3068543 : Blo 806344 3068543 := bstep (se 1 (by rfl) ⟨2301407, by rfl⟩ : syracuseStep 3068543 = 4602815) B4602815
theorem B6542137 : Blo 806344 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B808027 : Blo 806344 808027 := bstep (se 1 (by rfl) ⟨606020, by rfl⟩ : syracuseStep 808027 = 1212041) B1212041
theorem B808047 : Blo 806344 808047 := bstep (se 1 (by rfl) ⟨606035, by rfl⟩ : syracuseStep 808047 = 1212071) B1212071
theorem B808127 : Blo 806344 808127 := bstep (se 1 (by rfl) ⟨606095, by rfl⟩ : syracuseStep 808127 = 1212191) B1212191
theorem B808167 : Blo 806344 808167 := bstep (se 1 (by rfl) ⟨606125, by rfl⟩ : syracuseStep 808167 = 1212251) B1212251
theorem B808447 : Blo 806344 808447 := bstep (se 1 (by rfl) ⟨606335, by rfl⟩ : syracuseStep 808447 = 1212671) B1212671
theorem B808551 : Blo 806344 808551 := bstep (se 1 (by rfl) ⟨606413, by rfl⟩ : syracuseStep 808551 = 1212827) B1212827
theorem B808831 : Blo 806344 808831 := bstep (se 1 (by rfl) ⟨606623, by rfl⟩ : syracuseStep 808831 = 1213247) B1213247
theorem B808927 : Blo 806344 808927 := bstep (se 1 (by rfl) ⟨606695, by rfl⟩ : syracuseStep 808927 = 1213391) B1213391
theorem B808987 : Blo 806344 808987 := bstep (se 1 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 808987 = 1213481) B1213481
theorem B4085801 : Blo 806344 4085801 := bstep (se 2 (by rfl) ⟨1532175, by rfl⟩ : syracuseStep 4085801 = 3064351) B3064351
theorem B809007 : Blo 806344 809007 := bstep (se 1 (by rfl) ⟨606755, by rfl⟩ : syracuseStep 809007 = 1213511) B1213511
theorem B809127 : Blo 806344 809127 := bstep (se 1 (by rfl) ⟨606845, by rfl⟩ : syracuseStep 809127 = 1213691) B1213691
theorem B809319 : Blo 806344 809319 := bstep (se 1 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 809319 = 1213979) B1213979
theorem B809575 : Blo 806344 809575 := bstep (se 1 (by rfl) ⟨607181, by rfl⟩ : syracuseStep 809575 = 1214363) B1214363
theorem B809599 : Blo 806344 809599 := bstep (se 1 (by rfl) ⟨607199, by rfl⟩ : syracuseStep 809599 = 1214399) B1214399
theorem B3070655 : Blo 806344 3070655 := bstep (se 1 (by rfl) ⟨2302991, by rfl⟩ : syracuseStep 3070655 = 4605983) B4605983
theorem B810015 : Blo 806344 810015 := bstep (se 1 (by rfl) ⟨607511, by rfl⟩ : syracuseStep 810015 = 1215023) B1215023
theorem B810095 : Blo 806344 810095 := bstep (se 1 (by rfl) ⟨607571, by rfl⟩ : syracuseStep 810095 = 1215143) B1215143
theorem B810139 : Blo 806344 810139 := bstep (se 1 (by rfl) ⟨607604, by rfl⟩ : syracuseStep 810139 = 1215209) B1215209
theorem B810143 : Blo 806344 810143 := bstep (se 1 (by rfl) ⟨607607, by rfl⟩ : syracuseStep 810143 = 1215215) B1215215
theorem B810175 : Blo 806344 810175 := bstep (se 1 (by rfl) ⟨607631, by rfl⟩ : syracuseStep 810175 = 1215263) B1215263
theorem B25255127 : Blo 806344 25255127 := bstep (se 1 (by rfl) ⟨18941345, by rfl⟩ : syracuseStep 25255127 = 37882691) B37882691
theorem B2907359 : Blo 806344 2907359 := bstep (se 1 (by rfl) ⟨2180519, by rfl⟩ : syracuseStep 2907359 = 4361039) B4361039
theorem B6151787 : Blo 806344 6151787 := bstep (se 1 (by rfl) ⟨4613840, by rfl⟩ : syracuseStep 6151787 = 9227681) B9227681
theorem B13786847 : Blo 806344 13786847 := bstep (se 1 (by rfl) ⟨10340135, by rfl⟩ : syracuseStep 13786847 = 20680271) B20680271
theorem B3498173 : Blo 806344 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B3498295 : Blo 806344 3498295 := bstep (se 1 (by rfl) ⟨2623721, by rfl⟩ : syracuseStep 3498295 = 5247443) B5247443
theorem B15786359 : Blo 806344 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B7005209 : Blo 806344 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B3225445829 : Blo 806344 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B1533907 : Blo 806344 1533907 := bstep (se 1 (by rfl) ⟨1150430, by rfl⟩ : syracuseStep 1533907 = 2300861) B2300861
theorem B27944939 : Blo 806344 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B4089851 : Blo 806344 4089851 := bstep (se 1 (by rfl) ⟨3067388, by rfl⟩ : syracuseStep 4089851 = 6134777) B6134777
theorem B5171687 : Blo 806344 5171687 := bstep (se 1 (by rfl) ⟨3878765, by rfl⟩ : syracuseStep 5171687 = 7757531) B7757531
theorem B2583343 : Blo 806344 2583343 := bstep (se 1 (by rfl) ⟨1937507, by rfl⟩ : syracuseStep 2583343 = 3875015) B3875015
theorem B9204353 : Blo 806344 9204353 := bstep (se 2 (by rfl) ⟨3451632, by rfl⟩ : syracuseStep 9204353 = 6903265) B6903265
theorem B1537643 : Blo 806344 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B25196305 : Blo 806344 25196305 := bstep (se 2 (by rfl) ⟨9448614, by rfl⟩ : syracuseStep 25196305 = 18897229) B18897229
theorem B1210223 : Blo 806344 1210223 := bstep (se 1 (by rfl) ⟨907667, by rfl⟩ : syracuseStep 1210223 = 1815335) B1815335
theorem B1210235 : Blo 806344 1210235 := bstep (se 1 (by rfl) ⟨907676, by rfl⟩ : syracuseStep 1210235 = 1815353) B1815353
theorem B1210475 : Blo 806344 1210475 := bstep (se 1 (by rfl) ⟨907856, by rfl⟩ : syracuseStep 1210475 = 1815713) B1815713
theorem B13826213 : Blo 806344 13826213 := bstep (se 4 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 13826213 = 2592415) B2592415
theorem B1210655 : Blo 806344 1210655 := bstep (se 1 (by rfl) ⟨907991, by rfl⟩ : syracuseStep 1210655 = 1815983) B1815983
theorem B1210727 : Blo 806344 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B1210793 : Blo 806344 1210793 := bstep (se 2 (by rfl) ⟨454047, by rfl⟩ : syracuseStep 1210793 = 908095) B908095
theorem B1210847 : Blo 806344 1210847 := bstep (se 1 (by rfl) ⟨908135, by rfl⟩ : syracuseStep 1210847 = 1816271) B1816271
theorem B3930911 : Blo 806344 3930911 := bstep (se 1 (by rfl) ⟨2948183, by rfl⟩ : syracuseStep 3930911 = 5896367) B5896367
theorem B1211375 : Blo 806344 1211375 := bstep (se 1 (by rfl) ⟨908531, by rfl⟩ : syracuseStep 1211375 = 1817063) B1817063
theorem B9829457 : Blo 806344 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B1211561 : Blo 806344 1211561 := bstep (se 2 (by rfl) ⟨454335, by rfl⟩ : syracuseStep 1211561 = 908671) B908671
theorem B6127001 : Blo 806344 6127001 := bstep (se 2 (by rfl) ⟨2297625, by rfl⟩ : syracuseStep 6127001 = 4595251) B4595251
theorem B7373227 : Blo 806344 7373227 := bstep (se 1 (by rfl) ⟨5529920, by rfl⟩ : syracuseStep 7373227 = 11059841) B11059841
theorem B4719077 : Blo 806344 4719077 := bstep (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) B884827
theorem B1213931 : Blo 806344 1213931 := bstep (se 1 (by rfl) ⟨910448, by rfl⟩ : syracuseStep 1213931 = 1820897) B1820897
theorem B4359739 : Blo 806344 4359739 := bstep (se 1 (by rfl) ⟨3269804, by rfl⟩ : syracuseStep 4359739 = 6539609) B6539609
theorem B1214375 : Blo 806344 1214375 := bstep (se 1 (by rfl) ⟨910781, by rfl⟩ : syracuseStep 1214375 = 1821563) B1821563
theorem B1640417 : Blo 806344 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B18680557 : Blo 806344 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B1215227 : Blo 806344 1215227 := bstep (se 1 (by rfl) ⟨911420, by rfl⟩ : syracuseStep 1215227 = 1822841) B1822841
theorem B1215431 : Blo 806344 1215431 := bstep (se 1 (by rfl) ⟨911573, by rfl⟩ : syracuseStep 1215431 = 1823147) B1823147
theorem B1215455 : Blo 806344 1215455 := bstep (se 1 (by rfl) ⟨911591, by rfl⟩ : syracuseStep 1215455 = 1823183) B1823183
theorem B5836511 : Blo 806344 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B3444457 : Blo 806344 3444457 := bstep (se 2 (by rfl) ⟨1291671, by rfl⟩ : syracuseStep 3444457 = 2583343) B2583343
theorem B5181245 : Blo 806344 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B2723867 : Blo 806344 2723867 := bstep (se 1 (by rfl) ⟨2042900, by rfl⟩ : syracuseStep 2723867 = 4085801) B4085801
theorem B4657375 : Blo 806344 4657375 := bstep (se 1 (by rfl) ⟨3493031, by rfl⟩ : syracuseStep 4657375 = 6986063) B6986063
theorem B4100381 : Blo 806344 4100381 := bstep (se 3 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 4100381 = 1537643) B1537643
theorem B1938239 : Blo 806344 1938239 := bstep (se 1 (by rfl) ⟨1453679, by rfl⟩ : syracuseStep 1938239 = 2907359) B2907359
theorem B4101191 : Blo 806344 4101191 := bstep (se 1 (by rfl) ⟨3075893, by rfl⟩ : syracuseStep 4101191 = 6151787) B6151787
theorem B4920545 : Blo 806344 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B74519837 : Blo 806344 74519837 := bstep (se 3 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 74519837 = 27944939) B27944939
theorem B2332115 : Blo 806344 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B2627063 : Blo 806344 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B10524239 : Blo 806344 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B3938719 : Blo 806344 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B20191841 : Blo 806344 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B10361459 : Blo 806344 10361459 := bstep (se 1 (by rfl) ⟨7771094, by rfl⟩ : syracuseStep 10361459 = 15542189) B15542189
theorem B2726567 : Blo 806344 2726567 := bstep (se 1 (by rfl) ⟨2044925, by rfl⟩ : syracuseStep 2726567 = 4089851) B4089851
theorem B3447791 : Blo 806344 3447791 := bstep (se 1 (by rfl) ⟨2585843, by rfl⟩ : syracuseStep 3447791 = 5171687) B5171687
theorem B33595073 : Blo 806344 33595073 := bstep (se 2 (by rfl) ⟨12598152, by rfl⟩ : syracuseStep 33595073 = 25196305) B25196305
theorem B6136235 : Blo 806344 6136235 := bstep (se 1 (by rfl) ⟨4602176, by rfl⟩ : syracuseStep 6136235 = 9204353) B9204353
theorem B17048315 : Blo 806344 17048315 := bstep (se 1 (by rfl) ⟨12786236, by rfl⟩ : syracuseStep 17048315 = 25572473) B25572473
theorem B2302843 : Blo 806344 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B2106271 : Blo 806344 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B9217475 : Blo 806344 9217475 := bstep (se 1 (by rfl) ⟨6913106, by rfl⟩ : syracuseStep 9217475 = 13826213) B13826213
theorem B5614049 : Blo 806344 5614049 := bstep (se 2 (by rfl) ⟨2105268, by rfl⟩ : syracuseStep 5614049 = 4210537) B4210537
theorem B11643497 : Blo 806344 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B2305007 : Blo 806344 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B7384061 : Blo 806344 7384061 := bstep (se 3 (by rfl) ⟨1384511, by rfl⟩ : syracuseStep 7384061 = 2769023) B2769023
theorem B4664393 : Blo 806344 4664393 := bstep (se 2 (by rfl) ⟨1749147, by rfl⟩ : syracuseStep 4664393 = 3498295) B3498295
theorem B2305235 : Blo 806344 2305235 := bstep (se 1 (by rfl) ⟨1728926, by rfl⟩ : syracuseStep 2305235 = 3457853) B3457853
theorem B2305691 : Blo 806344 2305691 := bstep (se 1 (by rfl) ⟨1729268, by rfl⟩ : syracuseStep 2305691 = 3458537) B3458537
theorem B2043731 : Blo 806344 2043731 := bstep (se 1 (by rfl) ⟨1532798, by rfl⟩ : syracuseStep 2043731 = 3065597) B3065597
theorem B26161015 : Blo 806344 26161015 := bstep (se 1 (by rfl) ⟨19620761, by rfl⟩ : syracuseStep 26161015 = 39241523) B39241523
theorem B2043863 : Blo 806344 2043863 := bstep (se 1 (by rfl) ⟨1532897, by rfl⟩ : syracuseStep 2043863 = 3065795) B3065795
theorem B16593119 : Blo 806344 16593119 := bstep (se 1 (by rfl) ⟨12444839, by rfl⟩ : syracuseStep 16593119 = 24889679) B24889679
theorem B1814831 : Blo 806344 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B2045209 : Blo 806344 2045209 := bstep (se 2 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 2045209 = 1533907) B1533907
theorem B5518621 : Blo 806344 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B1816055 : Blo 806344 1816055 := bstep (se 1 (by rfl) ⟨1362041, by rfl⟩ : syracuseStep 1816055 = 2724083) B2724083
theorem B6207151 : Blo 806344 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B2045695 : Blo 806344 2045695 := bstep (se 1 (by rfl) ⟨1534271, by rfl⟩ : syracuseStep 2045695 = 3068543) B3068543
theorem B9943019 : Blo 806344 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B10336855 : Blo 806344 10336855 := bstep (se 1 (by rfl) ⟨7752641, by rfl⟩ : syracuseStep 10336855 = 15505283) B15505283
theorem B6142553 : Blo 806344 6142553 := bstep (se 2 (by rfl) ⟨2303457, by rfl⟩ : syracuseStep 6142553 = 4606915) B4606915
theorem B1292927 : Blo 806344 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B1817441 : Blo 806344 1817441 := bstep (se 2 (by rfl) ⟨681540, by rfl⟩ : syracuseStep 1817441 = 1363081) B1363081
theorem B1817513 : Blo 806344 1817513 := bstep (se 2 (by rfl) ⟨681567, by rfl⟩ : syracuseStep 1817513 = 1363135) B1363135
theorem B2047103 : Blo 806344 2047103 := bstep (se 1 (by rfl) ⟨1535327, by rfl⟩ : syracuseStep 2047103 = 3070655) B3070655
theorem B9223307 : Blo 806344 9223307 := bstep (se 1 (by rfl) ⟨6917480, by rfl⟩ : syracuseStep 9223307 = 13834961) B13834961
theorem B1818089 : Blo 806344 1818089 := bstep (se 2 (by rfl) ⟨681783, by rfl⟩ : syracuseStep 1818089 = 1363567) B1363567
theorem B9191231 : Blo 806344 9191231 := bstep (se 1 (by rfl) ⟨6893423, by rfl⟩ : syracuseStep 9191231 = 13786847) B13786847
theorem B1294427 : Blo 806344 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B1818935 : Blo 806344 1818935 := bstep (se 1 (by rfl) ⟨1364201, by rfl⟩ : syracuseStep 1818935 = 2728403) B2728403
theorem B1229291 : Blo 806344 1229291 := bstep (se 1 (by rfl) ⟨921968, by rfl⟩ : syracuseStep 1229291 = 1843937) B1843937
theorem B1820303 : Blo 806344 1820303 := bstep (se 1 (by rfl) ⟨1365227, by rfl⟩ : syracuseStep 1820303 = 2730455) B2730455
theorem B9226223 : Blo 806344 9226223 := bstep (se 1 (by rfl) ⟨6919667, by rfl⟩ : syracuseStep 9226223 = 13839335) B13839335
theorem B4377341 : Blo 806344 4377341 := bstep (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) B1641503
theorem B1362811 : Blo 806344 1362811 := bstep (se 1 (by rfl) ⟨1022108, by rfl⟩ : syracuseStep 1362811 = 2044217) B2044217
theorem B3460279 : Blo 806344 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B1822319 : Blo 806344 1822319 := bstep (se 1 (by rfl) ⟨1366739, by rfl⟩ : syracuseStep 1822319 = 2733479) B2733479
theorem B806815 : Blo 806344 806815 := bstep (se 1 (by rfl) ⟨605111, by rfl⟩ : syracuseStep 806815 = 1210223) B1210223
theorem B806823 : Blo 806344 806823 := bstep (se 1 (by rfl) ⟨605117, by rfl⟩ : syracuseStep 806823 = 1210235) B1210235
theorem B1363945 : Blo 806344 1363945 := bstep (se 2 (by rfl) ⟨511479, by rfl⟩ : syracuseStep 1363945 = 1022959) B1022959
theorem B1363999 : Blo 806344 1363999 := bstep (se 1 (by rfl) ⟨1022999, by rfl⟩ : syracuseStep 1363999 = 2045999) B2045999
theorem B806983 : Blo 806344 806983 := bstep (se 1 (by rfl) ⟨605237, by rfl⟩ : syracuseStep 806983 = 1210475) B1210475
theorem B807103 : Blo 806344 807103 := bstep (se 1 (by rfl) ⟨605327, by rfl⟩ : syracuseStep 807103 = 1210655) B1210655
theorem B6541523 : Blo 806344 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B807151 : Blo 806344 807151 := bstep (se 1 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 807151 = 1210727) B1210727
theorem B807195 : Blo 806344 807195 := bstep (se 1 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 807195 = 1210793) B1210793
theorem B807231 : Blo 806344 807231 := bstep (se 1 (by rfl) ⟨605423, by rfl⟩ : syracuseStep 807231 = 1210847) B1210847
theorem B1364303 : Blo 806344 1364303 := bstep (se 1 (by rfl) ⟨1023227, by rfl⟩ : syracuseStep 1364303 = 2046455) B2046455
theorem B807583 : Blo 806344 807583 := bstep (se 1 (by rfl) ⟨605687, by rfl⟩ : syracuseStep 807583 = 1211375) B1211375
theorem B807707 : Blo 806344 807707 := bstep (se 1 (by rfl) ⟨605780, by rfl⟩ : syracuseStep 807707 = 1211561) B1211561
theorem B4084667 : Blo 806344 4084667 := bstep (se 1 (by rfl) ⟨3063500, by rfl⟩ : syracuseStep 4084667 = 6127001) B6127001
theorem B13817465 : Blo 806344 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B907375 : Blo 806344 907375 := bstep (se 1 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 907375 = 1361063) B1361063
theorem B1366247 : Blo 806344 1366247 := bstep (se 1 (by rfl) ⟨1024685, by rfl⟩ : syracuseStep 1366247 = 2049371) B2049371
theorem B809199 : Blo 806344 809199 := bstep (se 1 (by rfl) ⟨606899, by rfl⟩ : syracuseStep 809199 = 1213799) B1213799
theorem B809279 : Blo 806344 809279 := bstep (se 1 (by rfl) ⟨606959, by rfl⟩ : syracuseStep 809279 = 1213919) B1213919
theorem B4675967 : Blo 806344 4675967 := bstep (se 1 (by rfl) ⟨3506975, by rfl⟩ : syracuseStep 4675967 = 7013951) B7013951
theorem B809455 : Blo 806344 809455 := bstep (se 1 (by rfl) ⟨607091, by rfl⟩ : syracuseStep 809455 = 1214183) B1214183
theorem B1727423 : Blo 806344 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B5168123 : Blo 806344 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B809979 : Blo 806344 809979 := bstep (se 1 (by rfl) ⟨607484, by rfl⟩ : syracuseStep 809979 = 1214969) B1214969
theorem B810011 : Blo 806344 810011 := bstep (se 1 (by rfl) ⟨607508, by rfl⟩ : syracuseStep 810011 = 1215017) B1215017
theorem B1727543 : Blo 806344 1727543 := bstep (se 1 (by rfl) ⟨1295657, by rfl⟩ : syracuseStep 1727543 = 2591315) B2591315
theorem B908527 : Blo 806344 908527 := bstep (se 1 (by rfl) ⟨681395, by rfl⟩ : syracuseStep 908527 = 1362791) B1362791
theorem B2186651 : Blo 806344 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B4611815 : Blo 806344 4611815 := bstep (se 1 (by rfl) ⟨3458861, by rfl⟩ : syracuseStep 4611815 = 6917723) B6917723
theorem B3071915 : Blo 806344 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B3071945 : Blo 806344 3071945 := bstep (se 2 (by rfl) ⟨1151979, by rfl⟩ : syracuseStep 3071945 = 2303959) B2303959
theorem B4088555 : Blo 806344 4088555 := bstep (se 1 (by rfl) ⟨3066416, by rfl⟩ : syracuseStep 4088555 = 6132833) B6132833
theorem B4088879 : Blo 806344 4088879 := bstep (se 1 (by rfl) ⟨3066659, by rfl⟩ : syracuseStep 4088879 = 6133319) B6133319
theorem B1533019 : Blo 806344 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B4089041 : Blo 806344 4089041 := bstep (se 2 (by rfl) ⟨1533390, by rfl⟩ : syracuseStep 4089041 = 3066781) B3066781
theorem B3695825 : Blo 806344 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B2188727 : Blo 806344 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B1402363 : Blo 806344 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B34891397 : Blo 806344 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B16836751 : Blo 806344 16836751 := bstep (se 1 (by rfl) ⟨12627563, by rfl⟩ : syracuseStep 16836751 = 25255127) B25255127
theorem B3074557 : Blo 806344 3074557 := bstep (se 3 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 3074557 = 1152959) B1152959
theorem B1534697 : Blo 806344 1534697 := bstep (se 2 (by rfl) ⟨575511, by rfl⟩ : syracuseStep 1534697 = 1151023) B1151023
theorem B4615163 : Blo 806344 4615163 := bstep (se 1 (by rfl) ⟨3461372, by rfl⟩ : syracuseStep 4615163 = 6922745) B6922745
theorem B7367867 : Blo 806344 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B4091471 : Blo 806344 4091471 := bstep (se 1 (by rfl) ⟨3068603, by rfl⟩ : syracuseStep 4091471 = 6137207) B6137207
theorem B2150297219 : Blo 806344 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B6221933 : Blo 806344 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B1537051 : Blo 806344 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B1210619 : Blo 806344 1210619 := bstep (se 1 (by rfl) ⟨907964, by rfl⟩ : syracuseStep 1210619 = 1815929) B1815929
theorem B6912287 : Blo 806344 6912287 := bstep (se 1 (by rfl) ⟨5184215, by rfl⟩ : syracuseStep 6912287 = 10368431) B10368431
theorem B1211087 : Blo 806344 1211087 := bstep (se 1 (by rfl) ⟨908315, by rfl⟩ : syracuseStep 1211087 = 1816631) B1816631
theorem B1211135 : Blo 806344 1211135 := bstep (se 1 (by rfl) ⟨908351, by rfl⟩ : syracuseStep 1211135 = 1816703) B1816703
theorem B1211327 : Blo 806344 1211327 := bstep (se 1 (by rfl) ⟨908495, by rfl⟩ : syracuseStep 1211327 = 1816991) B1816991
theorem B2620607 : Blo 806344 2620607 := bstep (se 1 (by rfl) ⟨1965455, by rfl⟩ : syracuseStep 2620607 = 3930911) B3930911
theorem B6552971 : Blo 806344 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B1211951 : Blo 806344 1211951 := bstep (se 1 (by rfl) ⟨908963, by rfl⟩ : syracuseStep 1211951 = 1817927) B1817927
theorem B1212623 : Blo 806344 1212623 := bstep (se 1 (by rfl) ⟨909467, by rfl⟩ : syracuseStep 1212623 = 1818935) B1818935
theorem B3146051 : Blo 806344 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B819527 : Blo 806344 819527 := bstep (se 1 (by rfl) ⟨614645, by rfl⟩ : syracuseStep 819527 = 1229291) B1229291
theorem B9830969 : Blo 806344 9830969 := bstep (se 2 (by rfl) ⟨3686613, by rfl⟩ : syracuseStep 9830969 = 7373227) B7373227
theorem B1213535 : Blo 806344 1213535 := bstep (se 1 (by rfl) ⟨910151, by rfl⟩ : syracuseStep 1213535 = 1820303) B1820303
theorem B1869817 : Blo 806344 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B1214879 : Blo 806344 1214879 := bstep (se 1 (by rfl) ⟨911159, by rfl⟩ : syracuseStep 1214879 = 1822319) B1822319
theorem B4361015 : Blo 806344 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B22449001 : Blo 806344 22449001 := bstep (se 2 (by rfl) ⟨8418375, by rfl⟩ : syracuseStep 22449001 = 16836751) B16836751
theorem B2723111 : Blo 806344 2723111 := bstep (se 1 (by rfl) ⟨2042333, by rfl⟩ : syracuseStep 2723111 = 4084667) B4084667
theorem B4099409 : Blo 806344 4099409 := bstep (se 2 (by rfl) ⟨1537278, by rfl⟩ : syracuseStep 4099409 = 3074557) B3074557
theorem B49679891 : Blo 806344 49679891 := bstep (se 1 (by rfl) ⟨37259918, by rfl⟩ : syracuseStep 49679891 = 74519837) B74519837
theorem B24907409 : Blo 806344 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B7016159 : Blo 806344 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B9211643 : Blo 806344 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B3117311 : Blo 806344 3117311 := bstep (se 1 (by rfl) ⟨2337983, by rfl⟩ : syracuseStep 3117311 = 4675967) B4675967
theorem B1151615 : Blo 806344 1151615 := bstep (se 1 (by rfl) ⟨863711, by rfl⟩ : syracuseStep 1151615 = 1727423) B1727423
theorem B2298527 : Blo 806344 2298527 := bstep (se 1 (by rfl) ⟨1723895, by rfl⟩ : syracuseStep 2298527 = 3447791) B3447791
theorem B3445415 : Blo 806344 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B1151695 : Blo 806344 1151695 := bstep (se 1 (by rfl) ⟨863771, by rfl⟩ : syracuseStep 1151695 = 1727543) B1727543
theorem B4592609 : Blo 806344 4592609 := bstep (se 2 (by rfl) ⟨1722228, by rfl⟩ : syracuseStep 4592609 = 3444457) B3444457
theorem B2725703 : Blo 806344 2725703 := bstep (se 1 (by rfl) ⟨2044277, by rfl⟩ : syracuseStep 2725703 = 4088555) B4088555
theorem B2725919 : Blo 806344 2725919 := bstep (se 1 (by rfl) ⟨2044439, by rfl⟩ : syracuseStep 2725919 = 4088879) B4088879
theorem B2726027 : Blo 806344 2726027 := bstep (se 1 (by rfl) ⟨2044520, by rfl⟩ : syracuseStep 2726027 = 4089041) B4089041
theorem B3742699 : Blo 806344 3742699 := bstep (se 1 (by rfl) ⟨2807024, by rfl⟩ : syracuseStep 3742699 = 5614049) B5614049
theorem B2726945 : Blo 806344 2726945 := bstep (se 2 (by rfl) ⟨1022604, by rfl⟩ : syracuseStep 2726945 = 2045209) B2045209
theorem B1023131 : Blo 806344 1023131 := bstep (se 1 (by rfl) ⟨767348, by rfl⟩ : syracuseStep 1023131 = 1534697) B1534697
theorem B11672909 : Blo 806344 11672909 := bstep (se 3 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 11672909 = 4377341) B4377341
theorem B4922707 : Blo 806344 4922707 := bstep (se 1 (by rfl) ⟨3692030, by rfl⟩ : syracuseStep 4922707 = 7384061) B7384061
theorem B2727593 : Blo 806344 2727593 := bstep (se 2 (by rfl) ⟨1022847, by rfl⟩ : syracuseStep 2727593 = 2045695) B2045695
theorem B2727647 : Blo 806344 2727647 := bstep (se 1 (by rfl) ⟨2045735, by rfl⟩ : syracuseStep 2727647 = 4091471) B4091471
theorem B6988285 : Blo 806344 6988285 := bstep (se 3 (by rfl) ⟨1310303, by rfl⟩ : syracuseStep 6988285 = 2620607) B2620607
theorem B5251625 : Blo 806344 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B6628679 : Blo 806344 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B4368647 : Blo 806344 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B3451805 : Blo 806344 3451805 := bstep (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) B1294427
theorem B2044025 : Blo 806344 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B5812985 : Blo 806344 5812985 := bstep (se 2 (by rfl) ⟨2179869, by rfl⟩ : syracuseStep 5812985 = 4359739) B4359739
theorem B3454163 : Blo 806344 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B1815911 : Blo 806344 1815911 := bstep (se 1 (by rfl) ⟨1361933, by rfl⟩ : syracuseStep 1815911 = 2723867) B2723867
theorem B2733587 : Blo 806344 2733587 := bstep (se 1 (by rfl) ⟨2050190, by rfl⟩ : syracuseStep 2733587 = 4100381) B4100381
theorem B1292159 : Blo 806344 1292159 := bstep (se 1 (by rfl) ⟨969119, by rfl⟩ : syracuseStep 1292159 = 1938239) B1938239
theorem B13121453 : Blo 806344 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B2734127 : Blo 806344 2734127 := bstep (se 1 (by rfl) ⟨2050595, by rfl⟩ : syracuseStep 2734127 = 4101191) B4101191
theorem B1554743 : Blo 806344 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B1751375 : Blo 806344 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B1817081 : Blo 806344 1817081 := bstep (se 2 (by rfl) ⟨681405, by rfl⟩ : syracuseStep 1817081 = 1362811) B1362811
theorem B1817711 : Blo 806344 1817711 := bstep (se 1 (by rfl) ⟨1363283, by rfl⟩ : syracuseStep 1817711 = 2726567) B2726567
theorem B1457767 : Blo 806344 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B22396715 : Blo 806344 22396715 := bstep (se 1 (by rfl) ⟨16797536, by rfl⟩ : syracuseStep 22396715 = 33595073) B33595073
theorem B34881353 : Blo 806344 34881353 := bstep (se 2 (by rfl) ⟨13080507, by rfl⟩ : syracuseStep 34881353 = 26161015) B26161015
theorem B4374445 : Blo 806344 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B2047943 : Blo 806344 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B2047963 : Blo 806344 2047963 := bstep (se 1 (by rfl) ⟨1535972, by rfl⟩ : syracuseStep 2047963 = 3071945) B3071945
theorem B1818593 : Blo 806344 1818593 := bstep (se 2 (by rfl) ⟨681972, by rfl⟩ : syracuseStep 1818593 = 1363945) B1363945
theorem B1818665 : Blo 806344 1818665 := bstep (se 2 (by rfl) ⟨681999, by rfl⟩ : syracuseStep 1818665 = 1363999) B1363999
theorem B6209833 : Blo 806344 6209833 := bstep (se 2 (by rfl) ⟨2328687, by rfl⟩ : syracuseStep 6209833 = 4657375) B4657375
theorem B1459151 : Blo 806344 1459151 := bstep (se 1 (by rfl) ⟨1094363, by rfl⟩ : syracuseStep 1459151 = 2188727) B2188727
theorem B6144983 : Blo 806344 6144983 := bstep (se 1 (by rfl) ⟨4608737, by rfl⟩ : syracuseStep 6144983 = 9217475) B9217475
theorem B2049401 : Blo 806344 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B7358161 : Blo 806344 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B8276201 : Blo 806344 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B1362487 : Blo 806344 1362487 := bstep (se 1 (by rfl) ⟨1021865, by rfl⟩ : syracuseStep 1362487 = 2043731) B2043731
theorem B1362575 : Blo 806344 1362575 := bstep (se 1 (by rfl) ⟨1021931, by rfl⟩ : syracuseStep 1362575 = 2043863) B2043863
theorem B4147955 : Blo 806344 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B11062079 : Blo 806344 11062079 := bstep (se 1 (by rfl) ⟨8296559, by rfl⟩ : syracuseStep 11062079 = 16593119) B16593119
theorem B13782473 : Blo 806344 13782473 := bstep (se 2 (by rfl) ⟨5168427, by rfl⟩ : syracuseStep 13782473 = 10336855) B10336855
theorem B807079 : Blo 806344 807079 := bstep (se 1 (by rfl) ⟨605309, by rfl⟩ : syracuseStep 807079 = 1210619) B1210619
theorem B4608191 : Blo 806344 4608191 := bstep (se 1 (by rfl) ⟨3456143, by rfl⟩ : syracuseStep 4608191 = 6912287) B6912287
theorem B5734125917 : Blo 806344 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B807391 : Blo 806344 807391 := bstep (se 1 (by rfl) ⟨605543, by rfl⟩ : syracuseStep 807391 = 1211087) B1211087
theorem B807423 : Blo 806344 807423 := bstep (se 1 (by rfl) ⟨605567, by rfl⟩ : syracuseStep 807423 = 1211135) B1211135
theorem B807551 : Blo 806344 807551 := bstep (se 1 (by rfl) ⟨605663, by rfl⟩ : syracuseStep 807551 = 1211327) B1211327
theorem B1364735 : Blo 806344 1364735 := bstep (se 1 (by rfl) ⟨1023551, by rfl⟩ : syracuseStep 1364735 = 2047103) B2047103
theorem B6148871 : Blo 806344 6148871 := bstep (se 1 (by rfl) ⟨4611653, by rfl⟩ : syracuseStep 6148871 = 9223307) B9223307
theorem B807967 : Blo 806344 807967 := bstep (se 1 (by rfl) ⟨605975, by rfl⟩ : syracuseStep 807967 = 1211951) B1211951
theorem B809287 : Blo 806344 809287 := bstep (se 1 (by rfl) ⟨606965, by rfl⟩ : syracuseStep 809287 = 1213931) B1213931
theorem B3070457 : Blo 806344 3070457 := bstep (se 2 (by rfl) ⟨1151421, by rfl⟩ : syracuseStep 3070457 = 2302843) B2302843
theorem B2808361 : Blo 806344 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B809583 : Blo 806344 809583 := bstep (se 1 (by rfl) ⟨607187, by rfl⟩ : syracuseStep 809583 = 1214375) B1214375
theorem B6150815 : Blo 806344 6150815 := bstep (se 1 (by rfl) ⟨4613111, by rfl⟩ : syracuseStep 6150815 = 9226223) B9226223
theorem B810151 : Blo 806344 810151 := bstep (se 1 (by rfl) ⟨607613, by rfl⟩ : syracuseStep 810151 = 1215227) B1215227
theorem B810287 : Blo 806344 810287 := bstep (se 1 (by rfl) ⟨607715, by rfl⟩ : syracuseStep 810287 = 1215431) B1215431
theorem B810303 : Blo 806344 810303 := bstep (se 1 (by rfl) ⟨607727, by rfl⟩ : syracuseStep 810303 = 1215455) B1215455
theorem B3891007 : Blo 806344 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B909535 : Blo 806344 909535 := bstep (se 1 (by rfl) ⟨682151, by rfl⟩ : syracuseStep 909535 = 1364303) B1364303
theorem B9855533 : Blo 806344 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B910831 : Blo 806344 910831 := bstep (se 1 (by rfl) ⟨683123, by rfl⟩ : syracuseStep 910831 = 1366247) B1366247
theorem B4613705 : Blo 806344 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B13461227 : Blo 806344 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B6907639 : Blo 806344 6907639 := bstep (se 1 (by rfl) ⟨5180729, by rfl⟩ : syracuseStep 6907639 = 10361459) B10361459
theorem B3074543 : Blo 806344 3074543 := bstep (se 1 (by rfl) ⟨2305907, by rfl⟩ : syracuseStep 3074543 = 4611815) B4611815
theorem B4090823 : Blo 806344 4090823 := bstep (se 1 (by rfl) ⟨3068117, by rfl⟩ : syracuseStep 4090823 = 6136235) B6136235
theorem B11365543 : Blo 806344 11365543 := bstep (se 1 (by rfl) ⟨8524157, by rfl⟩ : syracuseStep 11365543 = 17048315) B17048315
theorem B23260931 : Blo 806344 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B13791221 : Blo 806344 13791221 := bstep (se 5 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 13791221 = 1292927) B1292927
theorem B7762331 : Blo 806344 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B1536671 : Blo 806344 1536671 := bstep (se 1 (by rfl) ⟨1152503, by rfl⟩ : syracuseStep 1536671 = 2305007) B2305007
theorem B3076775 : Blo 806344 3076775 := bstep (se 1 (by rfl) ⟨2307581, by rfl⟩ : syracuseStep 3076775 = 4615163) B4615163
theorem B3109595 : Blo 806344 3109595 := bstep (se 1 (by rfl) ⟨2332196, by rfl⟩ : syracuseStep 3109595 = 4664393) B4664393
theorem B4911911 : Blo 806344 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B1536823 : Blo 806344 1536823 := bstep (se 1 (by rfl) ⟨1152617, by rfl⟩ : syracuseStep 1536823 = 2305235) B2305235
theorem B1537127 : Blo 806344 1537127 := bstep (se 1 (by rfl) ⟨1152845, by rfl⟩ : syracuseStep 1537127 = 2305691) B2305691
theorem B1209833 : Blo 806344 1209833 := bstep (se 2 (by rfl) ⟨453687, by rfl⟩ : syracuseStep 1209833 = 907375) B907375
theorem B1209887 : Blo 806344 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B1210703 : Blo 806344 1210703 := bstep (se 1 (by rfl) ⟨908027, by rfl⟩ : syracuseStep 1210703 = 1816055) B1816055
theorem B1211369 : Blo 806344 1211369 := bstep (se 2 (by rfl) ⟨454263, by rfl⟩ : syracuseStep 1211369 = 908527) B908527
theorem B4095035 : Blo 806344 4095035 := bstep (se 1 (by rfl) ⟨3071276, by rfl⟩ : syracuseStep 4095035 = 6142553) B6142553
theorem B1211627 : Blo 806344 1211627 := bstep (se 1 (by rfl) ⟨908720, by rfl⟩ : syracuseStep 1211627 = 1817441) B1817441
theorem B1211675 : Blo 806344 1211675 := bstep (se 1 (by rfl) ⟨908756, by rfl⟩ : syracuseStep 1211675 = 1817513) B1817513
theorem B1212059 : Blo 806344 1212059 := bstep (se 1 (by rfl) ⟨909044, by rfl⟩ : syracuseStep 1212059 = 1818089) B1818089
theorem B6127487 : Blo 806344 6127487 := bstep (se 1 (by rfl) ⟨4595615, by rfl⟩ : syracuseStep 6127487 = 9191231) B9191231
theorem B1212443 : Blo 806344 1212443 := bstep (se 1 (by rfl) ⟨909332, by rfl⟩ : syracuseStep 1212443 = 1818665) B1818665
theorem B1212713 : Blo 806344 1212713 := bstep (se 2 (by rfl) ⟨454767, by rfl⟩ : syracuseStep 1212713 = 909535) B909535
theorem B6553979 : Blo 806344 6553979 := bstep (se 1 (by rfl) ⟨4915484, by rfl⟩ : syracuseStep 6553979 = 9830969) B9830969
theorem B4096655 : Blo 806344 4096655 := bstep (se 1 (by rfl) ⟨3072491, by rfl⟩ : syracuseStep 4096655 = 6144983) B6144983
theorem B8389469 : Blo 806344 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B26281421 : Blo 806344 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B4097789 : Blo 806344 4097789 := bstep (se 3 (by rfl) ⟨768335, by rfl⟩ : syracuseStep 4097789 = 1536671) B1536671
theorem B7374719 : Blo 806344 7374719 := bstep (se 1 (by rfl) ⟨5531039, by rfl⟩ : syracuseStep 7374719 = 11062079) B11062079
theorem B1214441 : Blo 806344 1214441 := bstep (se 2 (by rfl) ⟨455415, by rfl⟩ : syracuseStep 1214441 = 910831) B910831
theorem B9210185 : Blo 806344 9210185 := bstep (se 2 (by rfl) ⟨3453819, by rfl⟩ : syracuseStep 9210185 = 6907639) B6907639
theorem B2493089 : Blo 806344 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B3822750611 : Blo 806344 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B2296943 : Blo 806344 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B4099247 : Blo 806344 4099247 := bstep (se 1 (by rfl) ⟨3074435, by rfl⟩ : syracuseStep 4099247 = 6148871) B6148871
theorem B4100543 : Blo 806344 4100543 := bstep (se 1 (by rfl) ⟨3075407, by rfl⟩ : syracuseStep 4100543 = 6150815) B6150815
theorem B2301203 : Blo 806344 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B2727215 : Blo 806344 2727215 := bstep (se 1 (by rfl) ⟨2045411, by rfl⟩ : syracuseStep 2727215 = 4090823) B4090823
theorem B33169013 : Blo 806344 33169013 := bstep (se 5 (by rfl) ⟨1554797, by rfl⟩ : syracuseStep 33169013 = 3109595) B3109595
theorem B15507287 : Blo 806344 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B2728349 : Blo 806344 2728349 := bstep (se 3 (by rfl) ⟨511565, by rfl⟩ : syracuseStep 2728349 = 1023131) B1023131
theorem B3875323 : Blo 806344 3875323 := bstep (se 1 (by rfl) ⟨2906492, by rfl⟩ : syracuseStep 3875323 = 5812985) B5812985
theorem B3744481 : Blo 806344 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B1024751 : Blo 806344 1024751 := bstep (se 1 (by rfl) ⟨768563, by rfl⟩ : syracuseStep 1024751 = 1537127) B1537127
theorem B2302775 : Blo 806344 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B861439 : Blo 806344 861439 := bstep (se 1 (by rfl) ⟨646079, by rfl⟩ : syracuseStep 861439 = 1292159) B1292159
theorem B4990265 : Blo 806344 4990265 := bstep (se 2 (by rfl) ⟨1871349, by rfl⟩ : syracuseStep 4990265 = 3742699) B3742699
theorem B6563609 : Blo 806344 6563609 := bstep (se 2 (by rfl) ⟨2461353, by rfl⟩ : syracuseStep 6563609 = 4922707) B4922707
theorem B2730023 : Blo 806344 2730023 := bstep (se 1 (by rfl) ⟨2047517, by rfl⟩ : syracuseStep 2730023 = 4095035) B4095035
theorem B1943689 : Blo 806344 1943689 := bstep (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) B1457767
theorem B5188009 : Blo 806344 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B2730617 : Blo 806344 2730617 := bstep (se 2 (by rfl) ⟨1023981, by rfl⟩ : syracuseStep 2730617 = 2047963) B2047963
theorem B9317713 : Blo 806344 9317713 := bstep (se 2 (by rfl) ⟨3494142, by rfl⟩ : syracuseStep 9317713 = 6988285) B6988285
theorem B5517467 : Blo 806344 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B2765303 : Blo 806344 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B1815407 : Blo 806344 1815407 := bstep (se 1 (by rfl) ⟨1361555, by rfl⟩ : syracuseStep 1815407 = 2723111) B2723111
theorem B2732939 : Blo 806344 2732939 := bstep (se 1 (by rfl) ⟨2049704, by rfl⟩ : syracuseStep 2732939 = 4099409) B4099409
theorem B9810881 : Blo 806344 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B9188315 : Blo 806344 9188315 := bstep (se 1 (by rfl) ⟨6891236, by rfl⟩ : syracuseStep 9188315 = 13782473) B13782473
theorem B6141095 : Blo 806344 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B2078207 : Blo 806344 2078207 := bstep (se 1 (by rfl) ⟨1558655, by rfl⟩ : syracuseStep 2078207 = 3117311) B3117311
theorem B3061739 : Blo 806344 3061739 := bstep (se 1 (by rfl) ⟨2296304, by rfl⟩ : syracuseStep 3061739 = 4592609) B4592609
theorem B1816649 : Blo 806344 1816649 := bstep (se 2 (by rfl) ⟨681243, by rfl⟩ : syracuseStep 1816649 = 1362487) B1362487
theorem B29932001 : Blo 806344 29932001 := bstep (se 2 (by rfl) ⟨11224500, by rfl⟩ : syracuseStep 29932001 = 22449001) B22449001
theorem B1817135 : Blo 806344 1817135 := bstep (se 1 (by rfl) ⟨1362851, by rfl⟩ : syracuseStep 1817135 = 2725703) B2725703
theorem B1817279 : Blo 806344 1817279 := bstep (se 1 (by rfl) ⟨1362959, by rfl⟩ : syracuseStep 1817279 = 2725919) B2725919
theorem B1817351 : Blo 806344 1817351 := bstep (se 1 (by rfl) ⟨1363013, by rfl⟩ : syracuseStep 1817351 = 2726027) B2726027
theorem B15154057 : Blo 806344 15154057 := bstep (se 2 (by rfl) ⟨5682771, by rfl⟩ : syracuseStep 15154057 = 11365543) B11365543
theorem B2046971 : Blo 806344 2046971 := bstep (se 1 (by rfl) ⟨1535228, by rfl⟩ : syracuseStep 2046971 = 3070457) B3070457
theorem B1817963 : Blo 806344 1817963 := bstep (se 1 (by rfl) ⟨1363472, by rfl⟩ : syracuseStep 1817963 = 2726945) B2726945
theorem B7781939 : Blo 806344 7781939 := bstep (se 1 (by rfl) ⟨5836454, by rfl⟩ : syracuseStep 7781939 = 11672909) B11672909
theorem B1818395 : Blo 806344 1818395 := bstep (se 1 (by rfl) ⟨1363796, by rfl⟩ : syracuseStep 1818395 = 2727593) B2727593
theorem B1818431 : Blo 806344 1818431 := bstep (se 1 (by rfl) ⟨1363823, by rfl⟩ : syracuseStep 1818431 = 2727647) B2727647
theorem B2049097 : Blo 806344 2049097 := bstep (se 2 (by rfl) ⟨768411, by rfl⟩ : syracuseStep 2049097 = 1536823) B1536823
theorem B2049695 : Blo 806344 2049695 := bstep (se 1 (by rfl) ⟨1537271, by rfl⟩ : syracuseStep 2049695 = 3074543) B3074543
theorem B9194147 : Blo 806344 9194147 := bstep (se 1 (by rfl) ⟨6895610, by rfl⟩ : syracuseStep 9194147 = 13791221) B13791221
theorem B1362683 : Blo 806344 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B2051183 : Blo 806344 2051183 := bstep (se 1 (by rfl) ⟨1538387, by rfl⟩ : syracuseStep 2051183 = 3076775) B3076775
theorem B806555 : Blo 806344 806555 := bstep (se 1 (by rfl) ⟨604916, by rfl⟩ : syracuseStep 806555 = 1209833) B1209833
theorem B1822391 : Blo 806344 1822391 := bstep (se 1 (by rfl) ⟨1366793, by rfl⟩ : syracuseStep 1822391 = 2733587) B2733587
theorem B806591 : Blo 806344 806591 := bstep (se 1 (by rfl) ⟨604943, by rfl⟩ : syracuseStep 806591 = 1209887) B1209887
theorem B1822751 : Blo 806344 1822751 := bstep (se 1 (by rfl) ⟨1367063, by rfl⟩ : syracuseStep 1822751 = 2734127) B2734127
theorem B1036495 : Blo 806344 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B807135 : Blo 806344 807135 := bstep (se 1 (by rfl) ⟨605351, by rfl⟩ : syracuseStep 807135 = 1210703) B1210703
theorem B1167583 : Blo 806344 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B807579 : Blo 806344 807579 := bstep (se 1 (by rfl) ⟨605684, by rfl⟩ : syracuseStep 807579 = 1211369) B1211369
theorem B807751 : Blo 806344 807751 := bstep (se 1 (by rfl) ⟨605813, by rfl⟩ : syracuseStep 807751 = 1211627) B1211627
theorem B807783 : Blo 806344 807783 := bstep (se 1 (by rfl) ⟨605837, by rfl⟩ : syracuseStep 807783 = 1211675) B1211675
theorem B808039 : Blo 806344 808039 := bstep (se 1 (by rfl) ⟨606029, by rfl⟩ : syracuseStep 808039 = 1212059) B1212059
theorem B14931143 : Blo 806344 14931143 := bstep (se 1 (by rfl) ⟨11198357, by rfl⟩ : syracuseStep 14931143 = 22396715) B22396715
theorem B23254235 : Blo 806344 23254235 := bstep (se 1 (by rfl) ⟨17440676, by rfl⟩ : syracuseStep 23254235 = 34881353) B34881353
theorem B4084991 : Blo 806344 4084991 := bstep (se 1 (by rfl) ⟨3063743, by rfl⟩ : syracuseStep 4084991 = 6127487) B6127487
theorem B1365295 : Blo 806344 1365295 := bstep (se 1 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 1365295 = 2047943) B2047943
theorem B808415 : Blo 806344 808415 := bstep (se 1 (by rfl) ⟨606311, by rfl⟩ : syracuseStep 808415 = 1212623) B1212623
theorem B8279777 : Blo 806344 8279777 := bstep (se 2 (by rfl) ⟨3104916, by rfl⟩ : syracuseStep 8279777 = 6209833) B6209833
theorem B972767 : Blo 806344 972767 := bstep (se 1 (by rfl) ⟨729575, by rfl⟩ : syracuseStep 972767 = 1459151) B1459151
theorem B809023 : Blo 806344 809023 := bstep (se 1 (by rfl) ⟨606767, by rfl⟩ : syracuseStep 809023 = 1213535) B1213535
theorem B1366267 : Blo 806344 1366267 := bstep (se 1 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 1366267 = 2049401) B2049401
theorem B809919 : Blo 806344 809919 := bstep (se 1 (by rfl) ⟨607439, by rfl⟩ : syracuseStep 809919 = 1214879) B1214879
theorem B3070973 : Blo 806344 3070973 := bstep (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) B1151615
theorem B908383 : Blo 806344 908383 := bstep (se 1 (by rfl) ⟨681287, by rfl⟩ : syracuseStep 908383 = 1362575) B1362575
theorem B2907343 : Blo 806344 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B33119927 : Blo 806344 33119927 := bstep (se 1 (by rfl) ⟨24839945, by rfl⟩ : syracuseStep 33119927 = 49679891) B49679891
theorem B16604939 : Blo 806344 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B4677439 : Blo 806344 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B3072127 : Blo 806344 3072127 := bstep (se 1 (by rfl) ⟨2304095, by rfl⟩ : syracuseStep 3072127 = 4608191) B4608191
theorem B1532351 : Blo 806344 1532351 := bstep (se 1 (by rfl) ⟨1149263, by rfl⟩ : syracuseStep 1532351 = 2298527) B2298527
theorem B909823 : Blo 806344 909823 := bstep (se 1 (by rfl) ⟨682367, by rfl⟩ : syracuseStep 909823 = 1364735) B1364735
theorem B8741621 : Blo 806344 8741621 := bstep (se 5 (by rfl) ⟨409763, by rfl⟩ : syracuseStep 8741621 = 819527) B819527
theorem B3501083 : Blo 806344 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B4419119 : Blo 806344 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B1535593 : Blo 806344 1535593 := bstep (se 2 (by rfl) ⟨575847, by rfl⟩ : syracuseStep 1535593 = 1151695) B1151695
theorem B3075803 : Blo 806344 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B8974151 : Blo 806344 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B2912431 : Blo 806344 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B5174887 : Blo 806344 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B3274607 : Blo 806344 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B1210607 : Blo 806344 1210607 := bstep (se 1 (by rfl) ⟨907955, by rfl⟩ : syracuseStep 1210607 = 1815911) B1815911
theorem B8747635 : Blo 806344 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B1211387 : Blo 806344 1211387 := bstep (se 1 (by rfl) ⟨908540, by rfl⟩ : syracuseStep 1211387 = 1817081) B1817081
theorem B1211807 : Blo 806344 1211807 := bstep (se 1 (by rfl) ⟨908855, by rfl⟩ : syracuseStep 1211807 = 1817711) B1817711
theorem B5832593 : Blo 806344 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B1212395 : Blo 806344 1212395 := bstep (se 1 (by rfl) ⟨909296, by rfl⟩ : syracuseStep 1212395 = 1818593) B1818593
theorem B4096169 : Blo 806344 4096169 := bstep (se 2 (by rfl) ⟨1536063, by rfl⟩ : syracuseStep 4096169 = 3072127) B3072127
theorem B1213097 : Blo 806344 1213097 := bstep (se 2 (by rfl) ⟨454911, by rfl⟩ : syracuseStep 1213097 = 909823) B909823
theorem B4916479 : Blo 806344 4916479 := bstep (se 1 (by rfl) ⟨3687359, by rfl⟩ : syracuseStep 4916479 = 7374719) B7374719
theorem B1148585 : Blo 806344 1148585 := bstep (se 2 (by rfl) ⟨430719, by rfl⟩ : syracuseStep 1148585 = 861439) B861439
theorem B6129431 : Blo 806344 6129431 := bstep (se 1 (by rfl) ⟨4597073, by rfl⟩ : syracuseStep 6129431 = 9194147) B9194147
theorem B2548500407 : Blo 806344 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B1214927 : Blo 806344 1214927 := bstep (se 1 (by rfl) ⟨911195, by rfl⟩ : syracuseStep 1214927 = 1822391) B1822391
theorem B1215167 : Blo 806344 1215167 := bstep (se 1 (by rfl) ⟨911375, by rfl⟩ : syracuseStep 1215167 = 1822751) B1822751
theorem B2591585 : Blo 806344 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B6917345 : Blo 806344 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B15502823 : Blo 806344 15502823 := bstep (se 1 (by rfl) ⟨11627117, by rfl⟩ : syracuseStep 15502823 = 23254235) B23254235
theorem B2723327 : Blo 806344 2723327 := bstep (se 1 (by rfl) ⟨2042495, by rfl⟩ : syracuseStep 2723327 = 4084991) B4084991
theorem B12423617 : Blo 806344 12423617 := bstep (se 2 (by rfl) ⟨4658856, by rfl⟩ : syracuseStep 12423617 = 9317713) B9317713
theorem B2594045 : Blo 806344 2594045 := bstep (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) B972767
theorem B1021567 : Blo 806344 1021567 := bstep (se 1 (by rfl) ⟨766175, by rfl⟩ : syracuseStep 1021567 = 1532351) B1532351
theorem B15505829 : Blo 806344 15505829 := bstep (se 4 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 15505829 = 2907343) B2907343
theorem B3678311 : Blo 806344 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B1843535 : Blo 806344 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1385471 : Blo 806344 1385471 := bstep (se 1 (by rfl) ⟨1039103, by rfl⟩ : syracuseStep 1385471 = 2078207) B2078207
theorem B2041159 : Blo 806344 2041159 := bstep (se 1 (by rfl) ⟨1530869, by rfl⟩ : syracuseStep 2041159 = 3061739) B3061739
theorem B5187959 : Blo 806344 5187959 := bstep (se 1 (by rfl) ⟨3890969, by rfl⟩ : syracuseStep 5187959 = 7781939) B7781939
theorem B6236585 : Blo 806344 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B4369319 : Blo 806344 4369319 := bstep (se 1 (by rfl) ⟨3276989, by rfl⟩ : syracuseStep 4369319 = 6553979) B6553979
theorem B2731103 : Blo 806344 2731103 := bstep (se 1 (by rfl) ⟨2048327, by rfl⟩ : syracuseStep 2731103 = 4096655) B4096655
theorem B4992641 : Blo 806344 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B2731859 : Blo 806344 2731859 := bstep (se 1 (by rfl) ⟨2048894, by rfl⟩ : syracuseStep 2731859 = 4097789) B4097789
theorem B2732129 : Blo 806344 2732129 := bstep (se 2 (by rfl) ⟨1024548, by rfl⟩ : syracuseStep 2732129 = 2049097) B2049097
theorem B6140123 : Blo 806344 6140123 := bstep (se 1 (by rfl) ⟨4605092, by rfl⟩ : syracuseStep 6140123 = 9210185) B9210185
theorem B2732669 : Blo 806344 2732669 := bstep (se 3 (by rfl) ⟨512375, by rfl⟩ : syracuseStep 2732669 = 1024751) B1024751
theorem B2732831 : Blo 806344 2732831 := bstep (se 1 (by rfl) ⟨2049623, by rfl⟩ : syracuseStep 2732831 = 4099247) B4099247
theorem B2733695 : Blo 806344 2733695 := bstep (se 1 (by rfl) ⟨2050271, by rfl⟩ : syracuseStep 2733695 = 4100543) B4100543
theorem B2047315 : Blo 806344 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B2047457 : Blo 806344 2047457 := bstep (se 2 (by rfl) ⟨767796, by rfl⟩ : syracuseStep 2047457 = 1535593) B1535593
theorem B1818143 : Blo 806344 1818143 := bstep (se 1 (by rfl) ⟨1363607, by rfl⟩ : syracuseStep 1818143 = 2727215) B2727215
theorem B10338191 : Blo 806344 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B3883241 : Blo 806344 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B1818899 : Blo 806344 1818899 := bstep (se 1 (by rfl) ⟨1364174, by rfl⟩ : syracuseStep 1818899 = 2728349) B2728349
theorem B1556777 : Blo 806344 1556777 := bstep (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) B1167583
theorem B3326843 : Blo 806344 3326843 := bstep (se 1 (by rfl) ⟨2495132, by rfl⟩ : syracuseStep 3326843 = 4990265) B4990265
theorem B4375739 : Blo 806344 4375739 := bstep (se 1 (by rfl) ⟨3281804, by rfl⟩ : syracuseStep 4375739 = 6563609) B6563609
theorem B1820015 : Blo 806344 1820015 := bstep (se 1 (by rfl) ⟨1365011, by rfl⟩ : syracuseStep 1820015 = 2730023) B2730023
theorem B1820393 : Blo 806344 1820393 := bstep (se 2 (by rfl) ⟨682647, by rfl⟩ : syracuseStep 1820393 = 1365295) B1365295
theorem B1820411 : Blo 806344 1820411 := bstep (se 1 (by rfl) ⟨1365308, by rfl⟩ : syracuseStep 1820411 = 2730617) B2730617
theorem B6899849 : Blo 806344 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B2050535 : Blo 806344 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B5982767 : Blo 806344 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B1821689 : Blo 806344 1821689 := bstep (se 2 (by rfl) ⟨683133, by rfl⟩ : syracuseStep 1821689 = 1366267) B1366267
theorem B1821959 : Blo 806344 1821959 := bstep (se 1 (by rfl) ⟨1366469, by rfl⟩ : syracuseStep 1821959 = 2732939) B2732939
theorem B6540587 : Blo 806344 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B20205409 : Blo 806344 20205409 := bstep (se 2 (by rfl) ⟨7577028, by rfl⟩ : syracuseStep 20205409 = 15154057) B15154057
theorem B2183071 : Blo 806344 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B807071 : Blo 806344 807071 := bstep (se 1 (by rfl) ⟨605303, by rfl⟩ : syracuseStep 807071 = 1210607) B1210607
theorem B807591 : Blo 806344 807591 := bstep (se 1 (by rfl) ⟨605693, by rfl⟩ : syracuseStep 807591 = 1211387) B1211387
theorem B1364647 : Blo 806344 1364647 := bstep (se 1 (by rfl) ⟨1023485, by rfl⟩ : syracuseStep 1364647 = 2046971) B2046971
theorem B807871 : Blo 806344 807871 := bstep (se 1 (by rfl) ⟨605903, by rfl⟩ : syracuseStep 807871 = 1211807) B1211807
theorem B3888395 : Blo 806344 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B808263 : Blo 806344 808263 := bstep (se 1 (by rfl) ⟨606197, by rfl⟩ : syracuseStep 808263 = 1212395) B1212395
theorem B808295 : Blo 806344 808295 := bstep (se 1 (by rfl) ⟨606221, by rfl⟩ : syracuseStep 808295 = 1212443) B1212443
theorem B808475 : Blo 806344 808475 := bstep (se 1 (by rfl) ⟨606356, by rfl⟩ : syracuseStep 808475 = 1212713) B1212713
theorem B5592979 : Blo 806344 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B5167097 : Blo 806344 5167097 := bstep (se 2 (by rfl) ⟨1937661, by rfl⟩ : syracuseStep 5167097 = 3875323) B3875323
theorem B17520947 : Blo 806344 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B5527973 : Blo 806344 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B1366463 : Blo 806344 1366463 := bstep (se 1 (by rfl) ⟨1024847, by rfl⟩ : syracuseStep 1366463 = 2049695) B2049695
theorem B809627 : Blo 806344 809627 := bstep (se 1 (by rfl) ⟨607220, by rfl⟩ : syracuseStep 809627 = 1214441) B1214441
theorem B1662059 : Blo 806344 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B908455 : Blo 806344 908455 := bstep (se 1 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 908455 = 1362683) B1362683
theorem B1531295 : Blo 806344 1531295 := bstep (se 1 (by rfl) ⟨1148471, by rfl⟩ : syracuseStep 1531295 = 2296943) B2296943
theorem B1367455 : Blo 806344 1367455 := bstep (se 1 (by rfl) ⟨1025591, by rfl⟩ : syracuseStep 1367455 = 2051183) B2051183
theorem B9954095 : Blo 806344 9954095 := bstep (se 1 (by rfl) ⟨7465571, by rfl⟩ : syracuseStep 9954095 = 14931143) B14931143
theorem B22079405 : Blo 806344 22079405 := bstep (se 3 (by rfl) ⟨4139888, by rfl⟩ : syracuseStep 22079405 = 8279777) B8279777
theorem B1534135 : Blo 806344 1534135 := bstep (se 1 (by rfl) ⟨1150601, by rfl⟩ : syracuseStep 1534135 = 2301203) B2301203
theorem B22112675 : Blo 806344 22112675 := bstep (se 1 (by rfl) ⟨16584506, by rfl⟩ : syracuseStep 22112675 = 33169013) B33169013
theorem B22079951 : Blo 806344 22079951 := bstep (se 1 (by rfl) ⟨16559963, by rfl⟩ : syracuseStep 22079951 = 33119927) B33119927
theorem B11069959 : Blo 806344 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B5827747 : Blo 806344 5827747 := bstep (se 1 (by rfl) ⟨4370810, by rfl⟩ : syracuseStep 5827747 = 8741621) B8741621
theorem B1535183 : Blo 806344 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B2946079 : Blo 806344 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B9336221 : Blo 806344 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B1210271 : Blo 806344 1210271 := bstep (se 1 (by rfl) ⟨907703, by rfl⟩ : syracuseStep 1210271 = 1815407) B1815407
theorem B6125543 : Blo 806344 6125543 := bstep (se 1 (by rfl) ⟨4594157, by rfl⟩ : syracuseStep 6125543 = 9188315) B9188315
theorem B4094063 : Blo 806344 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B11663513 : Blo 806344 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B1211099 : Blo 806344 1211099 := bstep (se 1 (by rfl) ⟨908324, by rfl⟩ : syracuseStep 1211099 = 1816649) B1816649
theorem B1211177 : Blo 806344 1211177 := bstep (se 2 (by rfl) ⟨454191, by rfl⟩ : syracuseStep 1211177 = 908383) B908383
theorem B19954667 : Blo 806344 19954667 := bstep (se 1 (by rfl) ⟨14966000, by rfl⟩ : syracuseStep 19954667 = 29932001) B29932001
theorem B1211423 : Blo 806344 1211423 := bstep (se 1 (by rfl) ⟨908567, by rfl⟩ : syracuseStep 1211423 = 1817135) B1817135
theorem B1211519 : Blo 806344 1211519 := bstep (se 1 (by rfl) ⟨908639, by rfl⟩ : syracuseStep 1211519 = 1817279) B1817279
theorem B1211567 : Blo 806344 1211567 := bstep (se 1 (by rfl) ⟨908675, by rfl⟩ : syracuseStep 1211567 = 1817351) B1817351
theorem B1211975 : Blo 806344 1211975 := bstep (se 1 (by rfl) ⟨908981, by rfl⟩ : syracuseStep 1211975 = 1817963) B1817963
theorem B1212263 : Blo 806344 1212263 := bstep (se 1 (by rfl) ⟨909197, by rfl⟩ : syracuseStep 1212263 = 1818395) B1818395
theorem B1212287 : Blo 806344 1212287 := bstep (se 1 (by rfl) ⟨909215, by rfl⟩ : syracuseStep 1212287 = 1818431) B1818431
theorem B1212599 : Blo 806344 1212599 := bstep (se 1 (by rfl) ⟨909449, by rfl⟩ : syracuseStep 1212599 = 1818899) B1818899
theorem B10355309 : Blo 806344 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B1213343 : Blo 806344 1213343 := bstep (se 1 (by rfl) ⟨910007, by rfl⟩ : syracuseStep 1213343 = 1820015) B1820015
theorem B1213595 : Blo 806344 1213595 := bstep (se 1 (by rfl) ⟨910196, by rfl⟩ : syracuseStep 1213595 = 1820393) B1820393
theorem B1213607 : Blo 806344 1213607 := bstep (se 1 (by rfl) ⟨910205, by rfl⟩ : syracuseStep 1213607 = 1820411) B1820411
theorem B6555305 : Blo 806344 6555305 := bstep (se 2 (by rfl) ⟨2458239, by rfl⟩ : syracuseStep 6555305 = 4916479) B4916479
theorem B2721545 : Blo 806344 2721545 := bstep (se 2 (by rfl) ⟨1020579, by rfl⟩ : syracuseStep 2721545 = 2041159) B2041159
theorem B1214459 : Blo 806344 1214459 := bstep (se 1 (by rfl) ⟨910844, by rfl⟩ : syracuseStep 1214459 = 1821689) B1821689
theorem B1214639 : Blo 806344 1214639 := bstep (se 1 (by rfl) ⟨910979, by rfl⟩ : syracuseStep 1214639 = 1821959) B1821959
theorem B4360391 : Blo 806344 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B11668637 : Blo 806344 11668637 := bstep (se 3 (by rfl) ⟨2187869, by rfl⟩ : syracuseStep 11668637 = 4375739) B4375739
theorem B2592263 : Blo 806344 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B3444731 : Blo 806344 3444731 := bstep (se 1 (by rfl) ⟨2583548, by rfl⟩ : syracuseStep 3444731 = 5167097) B5167097
theorem B7770329 : Blo 806344 7770329 := bstep (se 2 (by rfl) ⟨2913873, by rfl⟩ : syracuseStep 7770329 = 5827747) B5827747
theorem B1020863 : Blo 806344 1020863 := bstep (se 1 (by rfl) ⟨765647, by rfl⟩ : syracuseStep 1020863 = 1531295) B1531295
theorem B26940545 : Blo 806344 26940545 := bstep (se 2 (by rfl) ⟨10102704, by rfl⟩ : syracuseStep 26940545 = 20205409) B20205409
theorem B923647 : Blo 806344 923647 := bstep (se 1 (by rfl) ⟨692735, by rfl⟩ : syracuseStep 923647 = 1385471) B1385471
theorem B14719603 : Blo 806344 14719603 := bstep (se 1 (by rfl) ⟨11039702, by rfl⟩ : syracuseStep 14719603 = 22079405) B22079405
theorem B14719967 : Blo 806344 14719967 := bstep (se 1 (by rfl) ⟨11039975, by rfl⟩ : syracuseStep 14719967 = 22079951) B22079951
theorem B1023455 : Blo 806344 1023455 := bstep (se 1 (by rfl) ⟨767591, by rfl⟩ : syracuseStep 1023455 = 1535183) B1535183
theorem B4432157 : Blo 806344 4432157 := bstep (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) B1662059
theorem B106177013 : Blo 806344 106177013 := bstep (se 5 (by rfl) ⟨4977047, by rfl⟩ : syracuseStep 106177013 = 9954095) B9954095
theorem B2729375 : Blo 806344 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B7775675 : Blo 806344 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B2729753 : Blo 806344 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B6892127 : Blo 806344 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B2730779 : Blo 806344 2730779 := bstep (se 1 (by rfl) ⟨2048084, by rfl⟩ : syracuseStep 2730779 = 4096169) B4096169
theorem B1699000271 : Blo 806344 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B4599899 : Blo 806344 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B10335215 : Blo 806344 10335215 := bstep (se 1 (by rfl) ⟨7751411, by rfl⟩ : syracuseStep 10335215 = 15502823) B15502823
theorem B1815551 : Blo 806344 1815551 := bstep (se 1 (by rfl) ⟨1361663, by rfl⟩ : syracuseStep 1815551 = 2723327) B2723327
theorem B2045513 : Blo 806344 2045513 := bstep (se 2 (by rfl) ⟨767067, by rfl⟩ : syracuseStep 2045513 = 1534135) B1534135
theorem B14759945 : Blo 806344 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B11680631 : Blo 806344 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B10337219 : Blo 806344 10337219 := bstep (se 1 (by rfl) ⟨7752914, by rfl⟩ : syracuseStep 10337219 = 15505829) B15505829
theorem B3062893 : Blo 806344 3062893 := bstep (se 3 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 3062893 = 1148585) B1148585
theorem B1229023 : Blo 806344 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B1819529 : Blo 806344 1819529 := bstep (se 2 (by rfl) ⟨682323, by rfl⟩ : syracuseStep 1819529 = 1364647) B1364647
theorem B3458639 : Blo 806344 3458639 := bstep (se 1 (by rfl) ⟨2593979, by rfl⟩ : syracuseStep 3458639 = 5187959) B5187959
theorem B1820735 : Blo 806344 1820735 := bstep (se 1 (by rfl) ⟨1365551, by rfl⟩ : syracuseStep 1820735 = 2731103) B2731103
theorem B1362089 : Blo 806344 1362089 := bstep (se 2 (by rfl) ⟨510783, by rfl⟩ : syracuseStep 1362089 = 1021567) B1021567
theorem B3328427 : Blo 806344 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B7457305 : Blo 806344 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B1821239 : Blo 806344 1821239 := bstep (se 1 (by rfl) ⟨1365929, by rfl⟩ : syracuseStep 1821239 = 2731859) B2731859
theorem B1821419 : Blo 806344 1821419 := bstep (se 1 (by rfl) ⟨1366064, by rfl⟩ : syracuseStep 1821419 = 2732129) B2732129
theorem B1821779 : Blo 806344 1821779 := bstep (se 1 (by rfl) ⟨1366334, by rfl⟩ : syracuseStep 1821779 = 2732669) B2732669
theorem B1821887 : Blo 806344 1821887 := bstep (se 1 (by rfl) ⟨1366415, by rfl⟩ : syracuseStep 1821887 = 2732831) B2732831
theorem B1822463 : Blo 806344 1822463 := bstep (se 1 (by rfl) ⟨1366847, by rfl⟩ : syracuseStep 1822463 = 2733695) B2733695
theorem B806847 : Blo 806344 806847 := bstep (se 1 (by rfl) ⟨605135, by rfl⟩ : syracuseStep 806847 = 1210271) B1210271
theorem B4083695 : Blo 806344 4083695 := bstep (se 1 (by rfl) ⟨3062771, by rfl⟩ : syracuseStep 4083695 = 6125543) B6125543
theorem B807399 : Blo 806344 807399 := bstep (se 1 (by rfl) ⟨605549, by rfl⟩ : syracuseStep 807399 = 1211099) B1211099
theorem B807451 : Blo 806344 807451 := bstep (se 1 (by rfl) ⟨605588, by rfl⟩ : syracuseStep 807451 = 1211177) B1211177
theorem B1823273 : Blo 806344 1823273 := bstep (se 2 (by rfl) ⟨683727, by rfl⟩ : syracuseStep 1823273 = 1367455) B1367455
theorem B807615 : Blo 806344 807615 := bstep (se 1 (by rfl) ⟨605711, by rfl⟩ : syracuseStep 807615 = 1211423) B1211423
theorem B807679 : Blo 806344 807679 := bstep (se 1 (by rfl) ⟨605759, by rfl⟩ : syracuseStep 807679 = 1211519) B1211519
theorem B807711 : Blo 806344 807711 := bstep (se 1 (by rfl) ⟨605783, by rfl⟩ : syracuseStep 807711 = 1211567) B1211567
theorem B1364971 : Blo 806344 1364971 := bstep (se 1 (by rfl) ⟨1023728, by rfl⟩ : syracuseStep 1364971 = 2047457) B2047457
theorem B807983 : Blo 806344 807983 := bstep (se 1 (by rfl) ⟨605987, by rfl⟩ : syracuseStep 807983 = 1211975) B1211975
theorem B808175 : Blo 806344 808175 := bstep (se 1 (by rfl) ⟨606131, by rfl⟩ : syracuseStep 808175 = 1212263) B1212263
theorem B808191 : Blo 806344 808191 := bstep (se 1 (by rfl) ⟨606143, by rfl⟩ : syracuseStep 808191 = 1212287) B1212287
theorem B808731 : Blo 806344 808731 := bstep (se 1 (by rfl) ⟨606548, by rfl⟩ : syracuseStep 808731 = 1213097) B1213097
theorem B4151405 : Blo 806344 4151405 := bstep (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) B1556777
theorem B4086287 : Blo 806344 4086287 := bstep (se 1 (by rfl) ⟨3064715, by rfl⟩ : syracuseStep 4086287 = 6129431) B6129431
theorem B809951 : Blo 806344 809951 := bstep (se 1 (by rfl) ⟨607463, by rfl⟩ : syracuseStep 809951 = 1214927) B1214927
theorem B1367023 : Blo 806344 1367023 := bstep (se 1 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 1367023 = 2050535) B2050535
theorem B3988511 : Blo 806344 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B810111 : Blo 806344 810111 := bstep (se 1 (by rfl) ⟨607583, by rfl⟩ : syracuseStep 810111 = 1215167) B1215167
theorem B1727723 : Blo 806344 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B4611563 : Blo 806344 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B8871581 : Blo 806344 8871581 := bstep (se 3 (by rfl) ⟨1663421, by rfl⟩ : syracuseStep 8871581 = 3326843) B3326843
theorem B8282411 : Blo 806344 8282411 := bstep (se 1 (by rfl) ⟨6211808, by rfl⟩ : syracuseStep 8282411 = 12423617) B12423617
theorem B1729363 : Blo 806344 1729363 := bstep (se 1 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 1729363 = 2594045) B2594045
theorem B910975 : Blo 806344 910975 := bstep (se 1 (by rfl) ⟨683231, by rfl⟩ : syracuseStep 910975 = 1366463) B1366463
theorem B2910761 : Blo 806344 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B2452207 : Blo 806344 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B14741261 : Blo 806344 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B3928105 : Blo 806344 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B14741783 : Blo 806344 14741783 := bstep (se 1 (by rfl) ⟨11056337, by rfl⟩ : syracuseStep 14741783 = 22112675) B22112675
theorem B4157723 : Blo 806344 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B2912879 : Blo 806344 2912879 := bstep (se 1 (by rfl) ⟨2184659, by rfl⟩ : syracuseStep 2912879 = 4369319) B4369319
theorem B4093415 : Blo 806344 4093415 := bstep (se 1 (by rfl) ⟨3070061, by rfl⟩ : syracuseStep 4093415 = 6140123) B6140123
theorem B6224147 : Blo 806344 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B1211273 : Blo 806344 1211273 := bstep (se 2 (by rfl) ⟨454227, by rfl⟩ : syracuseStep 1211273 = 908455) B908455
theorem B13303111 : Blo 806344 13303111 := bstep (se 1 (by rfl) ⟨9977333, by rfl⟩ : syracuseStep 13303111 = 19954667) B19954667
theorem B1212095 : Blo 806344 1212095 := bstep (se 1 (by rfl) ⟨909071, by rfl⟩ : syracuseStep 1212095 = 1818143) B1818143
theorem B1213019 : Blo 806344 1213019 := bstep (se 1 (by rfl) ⟨909764, by rfl⟩ : syracuseStep 1213019 = 1819529) B1819529
theorem B6554789 : Blo 806344 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B1213823 : Blo 806344 1213823 := bstep (se 1 (by rfl) ⟨910367, by rfl⟩ : syracuseStep 1213823 = 1820735) B1820735
theorem B7767677 : Blo 806344 7767677 := bstep (se 3 (by rfl) ⟨1456439, by rfl⟩ : syracuseStep 7767677 = 2912879) B2912879
theorem B1214159 : Blo 806344 1214159 := bstep (se 1 (by rfl) ⟨910619, by rfl⟩ : syracuseStep 1214159 = 1821239) B1821239
theorem B1214279 : Blo 806344 1214279 := bstep (se 1 (by rfl) ⟨910709, by rfl⟩ : syracuseStep 1214279 = 1821419) B1821419
theorem B1214519 : Blo 806344 1214519 := bstep (se 1 (by rfl) ⟨910889, by rfl⟩ : syracuseStep 1214519 = 1821779) B1821779
theorem B1214591 : Blo 806344 1214591 := bstep (se 1 (by rfl) ⟨910943, by rfl⟩ : syracuseStep 1214591 = 1821887) B1821887
theorem B1214633 : Blo 806344 1214633 := bstep (se 2 (by rfl) ⟨455487, by rfl⟩ : syracuseStep 1214633 = 910975) B910975
theorem B2722301 : Blo 806344 2722301 := bstep (se 3 (by rfl) ⟨510431, by rfl⟩ : syracuseStep 2722301 = 1020863) B1020863
theorem B1214975 : Blo 806344 1214975 := bstep (se 1 (by rfl) ⟨911231, by rfl⟩ : syracuseStep 1214975 = 1822463) B1822463
theorem B2722463 : Blo 806344 2722463 := bstep (se 1 (by rfl) ⟨2041847, by rfl⟩ : syracuseStep 2722463 = 4083695) B4083695
theorem B2296487 : Blo 806344 2296487 := bstep (se 1 (by rfl) ⟨1722365, by rfl⟩ : syracuseStep 2296487 = 3444731) B3444731
theorem B5180219 : Blo 806344 5180219 := bstep (se 1 (by rfl) ⟨3885164, by rfl⟩ : syracuseStep 5180219 = 7770329) B7770329
theorem B1215515 : Blo 806344 1215515 := bstep (se 1 (by rfl) ⟨911636, by rfl⟩ : syracuseStep 1215515 = 1823273) B1823273
theorem B17960363 : Blo 806344 17960363 := bstep (se 1 (by rfl) ⟨13470272, by rfl⟩ : syracuseStep 17960363 = 26940545) B26940545
theorem B2724191 : Blo 806344 2724191 := bstep (se 1 (by rfl) ⟨2043143, by rfl⟩ : syracuseStep 2724191 = 4086287) B4086287
theorem B2659007 : Blo 806344 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B1151815 : Blo 806344 1151815 := bstep (se 1 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 1151815 = 1727723) B1727723
theorem B2954771 : Blo 806344 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B70784675 : Blo 806344 70784675 := bstep (se 1 (by rfl) ⟨53088506, by rfl⟩ : syracuseStep 70784675 = 106177013) B106177013
theorem B5183783 : Blo 806344 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B1940507 : Blo 806344 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B4594751 : Blo 806344 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B1132666847 : Blo 806344 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B6890143 : Blo 806344 6890143 := bstep (se 1 (by rfl) ⟨5167607, by rfl⟩ : syracuseStep 6890143 = 10335215) B10335215
theorem B2728943 : Blo 806344 2728943 := bstep (se 1 (by rfl) ⟨2046707, by rfl⟩ : syracuseStep 2728943 = 4093415) B4093415
theorem B2729213 : Blo 806344 2729213 := bstep (se 3 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 2729213 = 1023455) B1023455
theorem B9839963 : Blo 806344 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B17737481 : Blo 806344 17737481 := bstep (se 2 (by rfl) ⟨6651555, by rfl⟩ : syracuseStep 17737481 = 13303111) B13303111
theorem B6891479 : Blo 806344 6891479 := bstep (se 1 (by rfl) ⟨5168609, by rfl⟩ : syracuseStep 6891479 = 10337219) B10337219
theorem B2305759 : Blo 806344 2305759 := bstep (se 1 (by rfl) ⟨1729319, by rfl⟩ : syracuseStep 2305759 = 3458639) B3458639
theorem B2305817 : Blo 806344 2305817 := bstep (se 2 (by rfl) ⟨864681, by rfl⟩ : syracuseStep 2305817 = 1729363) B1729363
theorem B4370203 : Blo 806344 4370203 := bstep (se 1 (by rfl) ⟨3277652, by rfl⟩ : syracuseStep 4370203 = 6555305) B6555305
theorem B1814363 : Blo 806344 1814363 := bstep (se 1 (by rfl) ⟨1360772, by rfl⟩ : syracuseStep 1814363 = 2721545) B2721545
theorem B7779091 : Blo 806344 7779091 := bstep (se 1 (by rfl) ⟨5834318, by rfl⟩ : syracuseStep 7779091 = 11668637) B11668637
theorem B9943073 : Blo 806344 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B2767603 : Blo 806344 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B9813311 : Blo 806344 9813311 := bstep (se 1 (by rfl) ⟨7359983, by rfl⟩ : syracuseStep 9813311 = 14719967) B14719967
theorem B5914387 : Blo 806344 5914387 := bstep (se 1 (by rfl) ⟨4435790, by rfl⟩ : syracuseStep 5914387 = 8871581) B8871581
theorem B5521607 : Blo 806344 5521607 := bstep (se 1 (by rfl) ⟨4141205, by rfl⟩ : syracuseStep 5521607 = 8282411) B8282411
theorem B1819583 : Blo 806344 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B1819835 : Blo 806344 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B1819961 : Blo 806344 1819961 := bstep (se 2 (by rfl) ⟨682485, by rfl⟩ : syracuseStep 1819961 = 1364971) B1364971
theorem B1820519 : Blo 806344 1820519 := bstep (se 1 (by rfl) ⟨1365389, by rfl⟩ : syracuseStep 1820519 = 2730779) B2730779
theorem B1231529 : Blo 806344 1231529 := bstep (se 2 (by rfl) ⟨461823, by rfl⟩ : syracuseStep 1231529 = 923647) B923647
theorem B3066599 : Blo 806344 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B2771815 : Blo 806344 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B1363675 : Blo 806344 1363675 := bstep (se 1 (by rfl) ⟨1022756, by rfl⟩ : syracuseStep 1363675 = 2045513) B2045513
theorem B1822697 : Blo 806344 1822697 := bstep (se 2 (by rfl) ⟨683511, by rfl⟩ : syracuseStep 1822697 = 1367023) B1367023
theorem B4083857 : Blo 806344 4083857 := bstep (se 2 (by rfl) ⟨1531446, by rfl⟩ : syracuseStep 4083857 = 3062893) B3062893
theorem B4149431 : Blo 806344 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B7787087 : Blo 806344 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B807515 : Blo 806344 807515 := bstep (se 1 (by rfl) ⟨605636, by rfl⟩ : syracuseStep 807515 = 1211273) B1211273
theorem B808063 : Blo 806344 808063 := bstep (se 1 (by rfl) ⟨606047, by rfl⟩ : syracuseStep 808063 = 1212095) B1212095
theorem B808399 : Blo 806344 808399 := bstep (se 1 (by rfl) ⟨606299, by rfl⟩ : syracuseStep 808399 = 1212599) B1212599
theorem B6903539 : Blo 806344 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B808895 : Blo 806344 808895 := bstep (se 1 (by rfl) ⟨606671, by rfl⟩ : syracuseStep 808895 = 1213343) B1213343
theorem B809063 : Blo 806344 809063 := bstep (se 1 (by rfl) ⟨606797, by rfl⟩ : syracuseStep 809063 = 1213595) B1213595
theorem B809071 : Blo 806344 809071 := bstep (se 1 (by rfl) ⟨606803, by rfl⟩ : syracuseStep 809071 = 1213607) B1213607
theorem B809639 : Blo 806344 809639 := bstep (se 1 (by rfl) ⟨607229, by rfl⟩ : syracuseStep 809639 = 1214459) B1214459
theorem B908059 : Blo 806344 908059 := bstep (se 1 (by rfl) ⟨681044, by rfl⟩ : syracuseStep 908059 = 1362089) B1362089
theorem B809759 : Blo 806344 809759 := bstep (se 1 (by rfl) ⟨607319, by rfl⟩ : syracuseStep 809759 = 1214639) B1214639
theorem B2906927 : Blo 806344 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B2218951 : Blo 806344 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1728175 : Blo 806344 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B3269609 : Blo 806344 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B3074375 : Blo 806344 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B5237473 : Blo 806344 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B9827507 : Blo 806344 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B9827855 : Blo 806344 9827855 := bstep (se 1 (by rfl) ⟨7370891, by rfl⟩ : syracuseStep 9827855 = 14741783) B14741783
theorem B1210367 : Blo 806344 1210367 := bstep (se 1 (by rfl) ⟨907775, by rfl⟩ : syracuseStep 1210367 = 1815551) B1815551
theorem B19626137 : Blo 806344 19626137 := bstep (se 2 (by rfl) ⟨7359801, by rfl⟩ : syracuseStep 19626137 = 14719603) B14719603
theorem B1213055 : Blo 806344 1213055 := bstep (se 1 (by rfl) ⟨909791, by rfl⟩ : syracuseStep 1213055 = 1819583) B1819583
theorem B1213223 : Blo 806344 1213223 := bstep (se 1 (by rfl) ⟨909917, by rfl⟩ : syracuseStep 1213223 = 1819835) B1819835
theorem B1213307 : Blo 806344 1213307 := bstep (se 1 (by rfl) ⟨909980, by rfl⟩ : syracuseStep 1213307 = 1819961) B1819961
theorem B5178451 : Blo 806344 5178451 := bstep (se 1 (by rfl) ⟨3883838, by rfl⟩ : syracuseStep 5178451 = 7767677) B7767677
theorem B1213679 : Blo 806344 1213679 := bstep (se 1 (by rfl) ⟨910259, by rfl⟩ : syracuseStep 1213679 = 1820519) B1820519
theorem B1215131 : Blo 806344 1215131 := bstep (se 1 (by rfl) ⟨911348, by rfl⟩ : syracuseStep 1215131 = 1822697) B1822697
theorem B2722571 : Blo 806344 2722571 := bstep (se 1 (by rfl) ⟨2041928, by rfl⟩ : syracuseStep 2722571 = 4083857) B4083857
theorem B1772671 : Blo 806344 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B6983297 : Blo 806344 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B1969847 : Blo 806344 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B47189783 : Blo 806344 47189783 := bstep (se 1 (by rfl) ⟨35392337, by rfl⟩ : syracuseStep 47189783 = 70784675) B70784675
theorem B1937951 : Blo 806344 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B755111231 : Blo 806344 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B6559975 : Blo 806344 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B4594319 : Blo 806344 4594319 := bstep (se 1 (by rfl) ⟨3445739, by rfl⟩ : syracuseStep 4594319 = 6891479) B6891479
theorem B3284077 : Blo 806344 3284077 := bstep (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) B1231529
theorem B2958601 : Blo 806344 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B6628715 : Blo 806344 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B13084091 : Blo 806344 13084091 := bstep (se 1 (by rfl) ⟨9813068, by rfl⟩ : syracuseStep 13084091 = 19626137) B19626137
theorem B23307749 : Blo 806344 23307749 := bstep (se 4 (by rfl) ⟨2185101, by rfl⟩ : syracuseStep 23307749 = 4370203) B4370203
theorem B2304233 : Blo 806344 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B3681071 : Blo 806344 3681071 := bstep (se 1 (by rfl) ⟨2760803, by rfl⟩ : syracuseStep 3681071 = 5521607) B5521607
theorem B4369859 : Blo 806344 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B9186857 : Blo 806344 9186857 := bstep (se 2 (by rfl) ⟨3445071, by rfl⟩ : syracuseStep 9186857 = 6890143) B6890143
theorem B1814867 : Blo 806344 1814867 := bstep (se 1 (by rfl) ⟨1361150, by rfl⟩ : syracuseStep 1814867 = 2722301) B2722301
theorem B1814975 : Blo 806344 1814975 := bstep (se 1 (by rfl) ⟨1361231, by rfl⟩ : syracuseStep 1814975 = 2722463) B2722463
theorem B2044399 : Blo 806344 2044399 := bstep (se 1 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 2044399 = 3066599) B3066599
theorem B3453479 : Blo 806344 3453479 := bstep (se 1 (by rfl) ⟨2590109, by rfl⟩ : syracuseStep 3453479 = 5180219) B5180219
theorem B11973575 : Blo 806344 11973575 := bstep (se 1 (by rfl) ⟨8980181, by rfl⟩ : syracuseStep 11973575 = 17960363) B17960363
theorem B2766287 : Blo 806344 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B1816127 : Blo 806344 1816127 := bstep (se 1 (by rfl) ⟨1362095, by rfl⟩ : syracuseStep 1816127 = 2724191) B2724191
theorem B5191391 : Blo 806344 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B4602359 : Blo 806344 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B3455855 : Blo 806344 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B1293671 : Blo 806344 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B3063167 : Blo 806344 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B1818233 : Blo 806344 1818233 := bstep (se 2 (by rfl) ⟨681837, by rfl⟩ : syracuseStep 1818233 = 1363675) B1363675
theorem B2179739 : Blo 806344 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B1819295 : Blo 806344 1819295 := bstep (se 1 (by rfl) ⟨1364471, by rfl⟩ : syracuseStep 1819295 = 2728943) B2728943
theorem B1819475 : Blo 806344 1819475 := bstep (se 1 (by rfl) ⟨1364606, by rfl⟩ : syracuseStep 1819475 = 2729213) B2729213
theorem B10372121 : Blo 806344 10372121 := bstep (se 2 (by rfl) ⟨3889545, by rfl⟩ : syracuseStep 10372121 = 7779091) B7779091
theorem B2049583 : Blo 806344 2049583 := bstep (se 1 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 2049583 = 3074375) B3074375
theorem B3690137 : Blo 806344 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B806911 : Blo 806344 806911 := bstep (se 1 (by rfl) ⟨605183, by rfl⟩ : syracuseStep 806911 = 1210367) B1210367
theorem B6542207 : Blo 806344 6542207 := bstep (se 1 (by rfl) ⟨4906655, by rfl⟩ : syracuseStep 6542207 = 9813311) B9813311
theorem B7885849 : Blo 806344 7885849 := bstep (se 2 (by rfl) ⟨2957193, by rfl⟩ : syracuseStep 7885849 = 5914387) B5914387
theorem B808679 : Blo 806344 808679 := bstep (se 1 (by rfl) ⟨606509, by rfl⟩ : syracuseStep 808679 = 1213019) B1213019
theorem B809215 : Blo 806344 809215 := bstep (se 1 (by rfl) ⟨606911, by rfl⟩ : syracuseStep 809215 = 1213823) B1213823
theorem B809439 : Blo 806344 809439 := bstep (se 1 (by rfl) ⟨607079, by rfl⟩ : syracuseStep 809439 = 1214159) B1214159
theorem B809519 : Blo 806344 809519 := bstep (se 1 (by rfl) ⟨607139, by rfl⟩ : syracuseStep 809519 = 1214279) B1214279
theorem B809679 : Blo 806344 809679 := bstep (se 1 (by rfl) ⟨607259, by rfl⟩ : syracuseStep 809679 = 1214519) B1214519
theorem B809727 : Blo 806344 809727 := bstep (se 1 (by rfl) ⟨607295, by rfl⟩ : syracuseStep 809727 = 1214591) B1214591
theorem B809755 : Blo 806344 809755 := bstep (se 1 (by rfl) ⟨607316, by rfl⟩ : syracuseStep 809755 = 1214633) B1214633
theorem B809983 : Blo 806344 809983 := bstep (se 1 (by rfl) ⟨607487, by rfl⟩ : syracuseStep 809983 = 1214975) B1214975
theorem B1530991 : Blo 806344 1530991 := bstep (se 1 (by rfl) ⟨1148243, by rfl⟩ : syracuseStep 1530991 = 2296487) B2296487
theorem B810343 : Blo 806344 810343 := bstep (se 1 (by rfl) ⟨607757, by rfl⟩ : syracuseStep 810343 = 1215515) B1215515
theorem B26206685 : Blo 806344 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B3695753 : Blo 806344 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B3074345 : Blo 806344 3074345 := bstep (se 2 (by rfl) ⟨1152879, by rfl⟩ : syracuseStep 3074345 = 2305759) B2305759
theorem B1535753 : Blo 806344 1535753 := bstep (se 2 (by rfl) ⟨575907, by rfl⟩ : syracuseStep 1535753 = 1151815) B1151815
theorem B11824987 : Blo 806344 11824987 := bstep (se 1 (by rfl) ⟨8868740, by rfl⟩ : syracuseStep 11824987 = 17737481) B17737481
theorem B1537211 : Blo 806344 1537211 := bstep (se 1 (by rfl) ⟨1152908, by rfl⟩ : syracuseStep 1537211 = 2305817) B2305817
theorem B1209575 : Blo 806344 1209575 := bstep (se 1 (by rfl) ⟨907181, by rfl⟩ : syracuseStep 1209575 = 1814363) B1814363
theorem B6551903 : Blo 806344 6551903 := bstep (se 1 (by rfl) ⟨4913927, by rfl⟩ : syracuseStep 6551903 = 9827855) B9827855
theorem B1210745 : Blo 806344 1210745 := bstep (se 2 (by rfl) ⟨454029, by rfl⟩ : syracuseStep 1210745 = 908059) B908059
theorem B1212863 : Blo 806344 1212863 := bstep (se 1 (by rfl) ⟨909647, by rfl⟩ : syracuseStep 1212863 = 1819295) B1819295
theorem B1212983 : Blo 806344 1212983 := bstep (se 1 (by rfl) ⟨909737, by rfl⟩ : syracuseStep 1212983 = 1819475) B1819475
theorem B6914747 : Blo 806344 6914747 := bstep (se 1 (by rfl) ⟨5186060, by rfl⟩ : syracuseStep 6914747 = 10372121) B10372121
theorem B4655531 : Blo 806344 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B2460091 : Blo 806344 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B1313231 : Blo 806344 1313231 := bstep (se 1 (by rfl) ⟨984923, by rfl⟩ : syracuseStep 1313231 = 1969847) B1969847
theorem B31459855 : Blo 806344 31459855 := bstep (se 1 (by rfl) ⟨23594891, by rfl⟩ : syracuseStep 31459855 = 47189783) B47189783
theorem B4361471 : Blo 806344 4361471 := bstep (se 1 (by rfl) ⟨3271103, by rfl⟩ : syracuseStep 4361471 = 6542207) B6542207
theorem B2363561 : Blo 806344 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B15766649 : Blo 806344 15766649 := bstep (se 2 (by rfl) ⟨5912493, by rfl⟩ : syracuseStep 15766649 = 11824987) B11824987
theorem B17471123 : Blo 806344 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B2725865 : Blo 806344 2725865 := bstep (se 2 (by rfl) ⟨1022199, by rfl⟩ : syracuseStep 2725865 = 2044399) B2044399
theorem B8722727 : Blo 806344 8722727 := bstep (se 1 (by rfl) ⟨6542045, by rfl⟩ : syracuseStep 8722727 = 13084091) B13084091
theorem B15538499 : Blo 806344 15538499 := bstep (se 1 (by rfl) ⟨11653874, by rfl⟩ : syracuseStep 15538499 = 23307749) B23307749
theorem B1023835 : Blo 806344 1023835 := bstep (se 1 (by rfl) ⟨767876, by rfl⟩ : syracuseStep 1023835 = 1535753) B1535753
theorem B2302319 : Blo 806344 2302319 := bstep (se 1 (by rfl) ⟨1726739, by rfl⟩ : syracuseStep 2302319 = 3453479) B3453479
theorem B1024807 : Blo 806344 1024807 := bstep (se 1 (by rfl) ⟨768605, by rfl⟩ : syracuseStep 1024807 = 1537211) B1537211
theorem B3449789 : Blo 806344 3449789 := bstep (se 3 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 3449789 = 1293671) B1293671
theorem B1844191 : Blo 806344 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B2041321 : Blo 806344 2041321 := bstep (se 2 (by rfl) ⟨765495, by rfl⟩ : syracuseStep 2041321 = 1530991) B1530991
theorem B4367935 : Blo 806344 4367935 := bstep (se 1 (by rfl) ⟨3275951, by rfl⟩ : syracuseStep 4367935 = 6551903) B6551903
theorem B2303903 : Blo 806344 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B2042111 : Blo 806344 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B1453159 : Blo 806344 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B3944801 : Blo 806344 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B1815047 : Blo 806344 1815047 := bstep (se 1 (by rfl) ⟨1361285, by rfl⟩ : syracuseStep 1815047 = 2722571) B2722571
theorem B2732777 : Blo 806344 2732777 := bstep (se 2 (by rfl) ⟨1024791, by rfl⟩ : syracuseStep 2732777 = 2049583) B2049583
theorem B1291967 : Blo 806344 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B3062879 : Blo 806344 3062879 := bstep (se 1 (by rfl) ⟨2297159, by rfl⟩ : syracuseStep 3062879 = 4594319) B4594319
theorem B13843709 : Blo 806344 13843709 := bstep (se 3 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 13843709 = 5191391) B5191391
theorem B2049563 : Blo 806344 2049563 := bstep (se 1 (by rfl) ⟨1537172, by rfl⟩ : syracuseStep 2049563 = 3074345) B3074345
theorem B7982383 : Blo 806344 7982383 := bstep (se 1 (by rfl) ⟨5986787, by rfl⟩ : syracuseStep 7982383 = 11973575) B11973575
theorem B806383 : Blo 806344 806383 := bstep (se 1 (by rfl) ⟨604787, by rfl⟩ : syracuseStep 806383 = 1209575) B1209575
theorem B4378769 : Blo 806344 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B807163 : Blo 806344 807163 := bstep (se 1 (by rfl) ⟨605372, by rfl⟩ : syracuseStep 807163 = 1210745) B1210745
theorem B3068239 : Blo 806344 3068239 := bstep (se 1 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 3068239 = 4602359) B4602359
theorem B808703 : Blo 806344 808703 := bstep (se 1 (by rfl) ⟨606527, by rfl⟩ : syracuseStep 808703 = 1213055) B1213055
theorem B808815 : Blo 806344 808815 := bstep (se 1 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 808815 = 1213223) B1213223
theorem B808871 : Blo 806344 808871 := bstep (se 1 (by rfl) ⟨606653, by rfl⟩ : syracuseStep 808871 = 1213307) B1213307
theorem B809119 : Blo 806344 809119 := bstep (se 1 (by rfl) ⟨606839, by rfl⟩ : syracuseStep 809119 = 1213679) B1213679
theorem B6904601 : Blo 806344 6904601 := bstep (se 2 (by rfl) ⟨2589225, by rfl⟩ : syracuseStep 6904601 = 5178451) B5178451
theorem B810087 : Blo 806344 810087 := bstep (se 1 (by rfl) ⟨607565, by rfl⟩ : syracuseStep 810087 = 1215131) B1215131
theorem B9855341 : Blo 806344 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B503407487 : Blo 806344 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B4419143 : Blo 806344 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B10514465 : Blo 806344 10514465 := bstep (se 2 (by rfl) ⟨3942924, by rfl⟩ : syracuseStep 10514465 = 7885849) B7885849
theorem B1536155 : Blo 806344 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B2454047 : Blo 806344 2454047 := bstep (se 1 (by rfl) ⟨1840535, by rfl⟩ : syracuseStep 2454047 = 3681071) B3681071
theorem B2913239 : Blo 806344 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B6124571 : Blo 806344 6124571 := bstep (se 1 (by rfl) ⟨4593428, by rfl⟩ : syracuseStep 6124571 = 9186857) B9186857
theorem B1209911 : Blo 806344 1209911 := bstep (se 1 (by rfl) ⟨907433, by rfl⟩ : syracuseStep 1209911 = 1814867) B1814867
theorem B1209983 : Blo 806344 1209983 := bstep (se 1 (by rfl) ⟨907487, by rfl⟩ : syracuseStep 1209983 = 1814975) B1814975
theorem B8746633 : Blo 806344 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B1210751 : Blo 806344 1210751 := bstep (se 1 (by rfl) ⟨908063, by rfl⟩ : syracuseStep 1210751 = 1816127) B1816127
theorem B1212155 : Blo 806344 1212155 := bstep (se 1 (by rfl) ⟨909116, by rfl⟩ : syracuseStep 1212155 = 1818233) B1818233
theorem B10519469 : Blo 806344 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B2458921 : Blo 806344 2458921 := bstep (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) B1844191
theorem B2721761 : Blo 806344 2721761 := bstep (se 2 (by rfl) ⟨1020660, by rfl⟩ : syracuseStep 2721761 = 2041321) B2041321
theorem B2919179 : Blo 806344 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B1575707 : Blo 806344 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B3280121 : Blo 806344 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B41946473 : Blo 806344 41946473 := bstep (se 2 (by rfl) ⟨15729927, by rfl⟩ : syracuseStep 41946473 = 31459855) B31459855
theorem B10358999 : Blo 806344 10358999 := bstep (se 1 (by rfl) ⟨7769249, by rfl⟩ : syracuseStep 10358999 = 15538499) B15538499
theorem B2299859 : Blo 806344 2299859 := bstep (se 1 (by rfl) ⟨1724894, by rfl⟩ : syracuseStep 2299859 = 3449789) B3449789
theorem B1024103 : Blo 806344 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B1942159 : Blo 806344 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B861311 : Blo 806344 861311 := bstep (se 1 (by rfl) ⟨645983, by rfl⟩ : syracuseStep 861311 = 1291967) B1291967
theorem B2041919 : Blo 806344 2041919 := bstep (se 1 (by rfl) ⟨1531439, by rfl⟩ : syracuseStep 2041919 = 3062879) B3062879
theorem B11647415 : Blo 806344 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B1817243 : Blo 806344 1817243 := bstep (se 1 (by rfl) ⟨1362932, by rfl⟩ : syracuseStep 1817243 = 2725865) B2725865
theorem B5815151 : Blo 806344 5815151 := bstep (se 1 (by rfl) ⟨4361363, by rfl⟩ : syracuseStep 5815151 = 8722727) B8722727
theorem B4603067 : Blo 806344 4603067 := bstep (se 1 (by rfl) ⟨3452300, by rfl⟩ : syracuseStep 4603067 = 6904601) B6904601
theorem B6570227 : Blo 806344 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B7750181 : Blo 806344 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B1361407 : Blo 806344 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B1821851 : Blo 806344 1821851 := bstep (se 1 (by rfl) ⟨1366388, by rfl⟩ : syracuseStep 1821851 = 2732777) B2732777
theorem B4083047 : Blo 806344 4083047 := bstep (se 1 (by rfl) ⟨3062285, by rfl⟩ : syracuseStep 4083047 = 6124571) B6124571
theorem B46648709 : Blo 806344 46648709 := bstep (se 4 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 46648709 = 8746633) B8746633
theorem B806607 : Blo 806344 806607 := bstep (se 1 (by rfl) ⟨604955, by rfl⟩ : syracuseStep 806607 = 1209911) B1209911
theorem B806655 : Blo 806344 806655 := bstep (se 1 (by rfl) ⟨604991, by rfl⟩ : syracuseStep 806655 = 1209983) B1209983
theorem B807167 : Blo 806344 807167 := bstep (se 1 (by rfl) ⟨605375, by rfl⟩ : syracuseStep 807167 = 1210751) B1210751
theorem B9229139 : Blo 806344 9229139 := bstep (se 1 (by rfl) ⟨6921854, by rfl⟩ : syracuseStep 9229139 = 13843709) B13843709
theorem B1365113 : Blo 806344 1365113 := bstep (se 2 (by rfl) ⟨511917, by rfl⟩ : syracuseStep 1365113 = 1023835) B1023835
theorem B808103 : Blo 806344 808103 := bstep (se 1 (by rfl) ⟨606077, by rfl⟩ : syracuseStep 808103 = 1212155) B1212155
theorem B808575 : Blo 806344 808575 := bstep (se 1 (by rfl) ⟨606431, by rfl⟩ : syracuseStep 808575 = 1212863) B1212863
theorem B808655 : Blo 806344 808655 := bstep (se 1 (by rfl) ⟨606491, by rfl⟩ : syracuseStep 808655 = 1212983) B1212983
theorem B4609831 : Blo 806344 4609831 := bstep (se 1 (by rfl) ⟨3457373, by rfl⟩ : syracuseStep 4609831 = 6914747) B6914747
theorem B1366375 : Blo 806344 1366375 := bstep (se 1 (by rfl) ⟨1024781, by rfl⟩ : syracuseStep 1366375 = 2049563) B2049563
theorem B1366409 : Blo 806344 1366409 := bstep (se 2 (by rfl) ⟨512403, by rfl⟩ : syracuseStep 1366409 = 1024807) B1024807
theorem B3103687 : Blo 806344 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B5823913 : Blo 806344 5823913 := bstep (se 2 (by rfl) ⟨2183967, by rfl⟩ : syracuseStep 5823913 = 4367935) B4367935
theorem B2907647 : Blo 806344 2907647 := bstep (se 1 (by rfl) ⟨2180735, by rfl⟩ : syracuseStep 2907647 = 4361471) B4361471
theorem B10511099 : Blo 806344 10511099 := bstep (se 1 (by rfl) ⟨7883324, by rfl⟩ : syracuseStep 10511099 = 15766649) B15766649
theorem B10643177 : Blo 806344 10643177 := bstep (se 2 (by rfl) ⟨3991191, by rfl⟩ : syracuseStep 10643177 = 7982383) B7982383
theorem B1534879 : Blo 806344 1534879 := bstep (se 1 (by rfl) ⟨1151159, by rfl⟩ : syracuseStep 1534879 = 2302319) B2302319
theorem B4090985 : Blo 806344 4090985 := bstep (se 2 (by rfl) ⟨1534119, by rfl⟩ : syracuseStep 4090985 = 3068239) B3068239
theorem B335604991 : Blo 806344 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B3501949 : Blo 806344 3501949 := bstep (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) B1313231
theorem B1535935 : Blo 806344 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B2946095 : Blo 806344 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B7009643 : Blo 806344 7009643 := bstep (se 1 (by rfl) ⟨5257232, by rfl⟩ : syracuseStep 7009643 = 10514465) B10514465
theorem B1210031 : Blo 806344 1210031 := bstep (se 1 (by rfl) ⟨907523, by rfl⟩ : syracuseStep 1210031 = 1815047) B1815047
theorem B1636031 : Blo 806344 1636031 := bstep (se 1 (by rfl) ⟨1227023, by rfl⟩ : syracuseStep 1636031 = 2454047) B2454047
theorem B7012979 : Blo 806344 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B2589545 : Blo 806344 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B3278561 : Blo 806344 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B1214567 : Blo 806344 1214567 := bstep (se 1 (by rfl) ⟨910925, by rfl⟩ : syracuseStep 1214567 = 1821851) B1821851
theorem B2722031 : Blo 806344 2722031 := bstep (se 1 (by rfl) ⟨2041523, by rfl⟩ : syracuseStep 2722031 = 4083047) B4083047
theorem B31099139 : Blo 806344 31099139 := bstep (se 1 (by rfl) ⟨23324354, by rfl⟩ : syracuseStep 31099139 = 46648709) B46648709
theorem B2296829 : Blo 806344 2296829 := bstep (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) B861311
theorem B1938431 : Blo 806344 1938431 := bstep (se 1 (by rfl) ⟨1453823, by rfl⟩ : syracuseStep 1938431 = 2907647) B2907647
theorem B2727323 : Blo 806344 2727323 := bstep (se 1 (by rfl) ⟨2045492, by rfl⟩ : syracuseStep 2727323 = 4090985) B4090985
theorem B4201885 : Blo 806344 4201885 := bstep (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) B1575707
theorem B1090687 : Blo 806344 1090687 := bstep (se 1 (by rfl) ⟨818015, by rfl⟩ : syracuseStep 1090687 = 1636031) B1636031
theorem B4138249 : Blo 806344 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B3876767 : Blo 806344 3876767 := bstep (se 1 (by rfl) ⟨2907575, by rfl⟩ : syracuseStep 3876767 = 5815151) B5815151
theorem B2730941 : Blo 806344 2730941 := bstep (se 3 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 2730941 = 1024103) B1024103
theorem B1814507 : Blo 806344 1814507 := bstep (se 1 (by rfl) ⟨1360880, by rfl⟩ : syracuseStep 1814507 = 2721761) B2721761
theorem B1946119 : Blo 806344 1946119 := bstep (se 1 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 1946119 = 2919179) B2919179
theorem B1815209 : Blo 806344 1815209 := bstep (se 2 (by rfl) ⟨680703, by rfl⟩ : syracuseStep 1815209 = 1361407) B1361407
theorem B27964315 : Blo 806344 27964315 := bstep (se 1 (by rfl) ⟨20973236, by rfl⟩ : syracuseStep 27964315 = 41946473) B41946473
theorem B2046505 : Blo 806344 2046505 := bstep (se 2 (by rfl) ⟨767439, by rfl⟩ : syracuseStep 2046505 = 1534879) B1534879
theorem B4669265 : Blo 806344 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B2047913 : Blo 806344 2047913 := bstep (se 2 (by rfl) ⟨767967, by rfl⟩ : syracuseStep 2047913 = 1535935) B1535935
theorem B7095451 : Blo 806344 7095451 := bstep (se 1 (by rfl) ⟨5321588, by rfl⟩ : syracuseStep 7095451 = 10643177) B10643177
theorem B1361279 : Blo 806344 1361279 := bstep (se 1 (by rfl) ⟨1020959, by rfl⟩ : syracuseStep 1361279 = 2041919) B2041919
theorem B6146441 : Blo 806344 6146441 := bstep (se 2 (by rfl) ⟨2304915, by rfl⟩ : syracuseStep 6146441 = 4609831) B4609831
theorem B1821833 : Blo 806344 1821833 := bstep (se 2 (by rfl) ⟨683187, by rfl⟩ : syracuseStep 1821833 = 1366375) B1366375
theorem B4673095 : Blo 806344 4673095 := bstep (se 1 (by rfl) ⟨3504821, by rfl⟩ : syracuseStep 4673095 = 7009643) B7009643
theorem B806687 : Blo 806344 806687 := bstep (se 1 (by rfl) ⟨605015, by rfl⟩ : syracuseStep 806687 = 1210031) B1210031
theorem B3068711 : Blo 806344 3068711 := bstep (se 1 (by rfl) ⟨2301533, by rfl⟩ : syracuseStep 3068711 = 4603067) B4603067
theorem B4380151 : Blo 806344 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B20667149 : Blo 806344 20667149 := bstep (se 3 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 20667149 = 7750181) B7750181
theorem B2186747 : Blo 806344 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B6905999 : Blo 806344 6905999 := bstep (se 1 (by rfl) ⟨5179499, by rfl⟩ : syracuseStep 6905999 = 10358999) B10358999
theorem B6152759 : Blo 806344 6152759 := bstep (se 1 (by rfl) ⟨4614569, by rfl⟩ : syracuseStep 6152759 = 9229139) B9229139
theorem B910075 : Blo 806344 910075 := bstep (se 1 (by rfl) ⟨682556, by rfl⟩ : syracuseStep 910075 = 1365113) B1365113
theorem B1533239 : Blo 806344 1533239 := bstep (se 1 (by rfl) ⟨1149929, by rfl⟩ : syracuseStep 1533239 = 2299859) B2299859
theorem B910939 : Blo 806344 910939 := bstep (se 1 (by rfl) ⟨683204, by rfl⟩ : syracuseStep 910939 = 1366409) B1366409
theorem B447473321 : Blo 806344 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B7007399 : Blo 806344 7007399 := bstep (se 1 (by rfl) ⟨5255549, by rfl⟩ : syracuseStep 7007399 = 10511099) B10511099
theorem B31059773 : Blo 806344 31059773 := bstep (se 3 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 31059773 = 11647415) B11647415
theorem B1964063 : Blo 806344 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B1211495 : Blo 806344 1211495 := bstep (se 1 (by rfl) ⟨908621, by rfl⟩ : syracuseStep 1211495 = 1817243) B1817243
theorem B7765217 : Blo 806344 7765217 := bstep (se 2 (by rfl) ⟨2911956, by rfl⟩ : syracuseStep 7765217 = 5823913) B5823913
theorem B1213433 : Blo 806344 1213433 := bstep (se 2 (by rfl) ⟨455037, by rfl⟩ : syracuseStep 1213433 = 910075) B910075
theorem B4097627 : Blo 806344 4097627 := bstep (se 1 (by rfl) ⟨3073220, by rfl⟩ : syracuseStep 4097627 = 6146441) B6146441
theorem B1214555 : Blo 806344 1214555 := bstep (se 1 (by rfl) ⟨910916, by rfl⟩ : syracuseStep 1214555 = 1821833) B1821833
theorem B1214585 : Blo 806344 1214585 := bstep (se 2 (by rfl) ⟨455469, by rfl⟩ : syracuseStep 1214585 = 910939) B910939
theorem B4101839 : Blo 806344 4101839 := bstep (se 1 (by rfl) ⟨3076379, by rfl⟩ : syracuseStep 4101839 = 6152759) B6152759
theorem B2594825 : Blo 806344 2594825 := bstep (se 2 (by rfl) ⟨973059, by rfl⟩ : syracuseStep 2594825 = 1946119) B1946119
theorem B1022159 : Blo 806344 1022159 := bstep (se 1 (by rfl) ⟨766619, by rfl⟩ : syracuseStep 1022159 = 1533239) B1533239
theorem B5840201 : Blo 806344 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B2728673 : Blo 806344 2728673 := bstep (se 2 (by rfl) ⟨1023252, by rfl⟩ : syracuseStep 2728673 = 2046505) B2046505
theorem B1814687 : Blo 806344 1814687 := bstep (se 1 (by rfl) ⟨1361015, by rfl⟩ : syracuseStep 1814687 = 2722031) B2722031
theorem B1454249 : Blo 806344 1454249 := bstep (se 2 (by rfl) ⟨545343, by rfl⟩ : syracuseStep 1454249 = 1090687) B1090687
theorem B5517665 : Blo 806344 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B2045807 : Blo 806344 2045807 := bstep (se 1 (by rfl) ⟨1534355, by rfl⟩ : syracuseStep 2045807 = 3068711) B3068711
theorem B1292287 : Blo 806344 1292287 := bstep (se 1 (by rfl) ⟨969215, by rfl⟩ : syracuseStep 1292287 = 1938431) B1938431
theorem B13778099 : Blo 806344 13778099 := bstep (se 1 (by rfl) ⟨10333574, by rfl⟩ : syracuseStep 13778099 = 20667149) B20667149
theorem B1818215 : Blo 806344 1818215 := bstep (se 1 (by rfl) ⟨1363661, by rfl⟩ : syracuseStep 1818215 = 2727323) B2727323
theorem B1457831 : Blo 806344 1457831 := bstep (se 1 (by rfl) ⟨1093373, by rfl⟩ : syracuseStep 1457831 = 2186747) B2186747
theorem B4603999 : Blo 806344 4603999 := bstep (se 1 (by rfl) ⟨3452999, by rfl⟩ : syracuseStep 4603999 = 6905999) B6905999
theorem B1820627 : Blo 806344 1820627 := bstep (se 1 (by rfl) ⟨1365470, by rfl⟩ : syracuseStep 1820627 = 2730941) B2730941
theorem B4671599 : Blo 806344 4671599 := bstep (se 1 (by rfl) ⟨3503699, by rfl⟩ : syracuseStep 4671599 = 7007399) B7007399
theorem B24923173 : Blo 806344 24923173 := bstep (se 4 (by rfl) ⟨2336547, by rfl⟩ : syracuseStep 24923173 = 4673095) B4673095
theorem B807663 : Blo 806344 807663 := bstep (se 1 (by rfl) ⟨605747, by rfl⟩ : syracuseStep 807663 = 1211495) B1211495
theorem B1365275 : Blo 806344 1365275 := bstep (se 1 (by rfl) ⟨1023956, by rfl⟩ : syracuseStep 1365275 = 2047913) B2047913
theorem B4675319 : Blo 806344 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B1726363 : Blo 806344 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B907519 : Blo 806344 907519 := bstep (se 1 (by rfl) ⟨680639, by rfl⟩ : syracuseStep 907519 = 1361279) B1361279
theorem B809711 : Blo 806344 809711 := bstep (se 1 (by rfl) ⟨607283, by rfl⟩ : syracuseStep 809711 = 1214567) B1214567
theorem B20732759 : Blo 806344 20732759 := bstep (se 1 (by rfl) ⟨15549569, by rfl⟩ : syracuseStep 20732759 = 31099139) B31099139
theorem B9460601 : Blo 806344 9460601 := bstep (se 2 (by rfl) ⟨3547725, by rfl⟩ : syracuseStep 9460601 = 7095451) B7095451
theorem B1531219 : Blo 806344 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B8742829 : Blo 806344 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B298315547 : Blo 806344 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B37285753 : Blo 806344 37285753 := bstep (se 2 (by rfl) ⟨13982157, by rfl⟩ : syracuseStep 37285753 = 27964315) B27964315
theorem B2584511 : Blo 806344 2584511 := bstep (se 1 (by rfl) ⟨1938383, by rfl⟩ : syracuseStep 2584511 = 3876767) B3876767
theorem B22410053 : Blo 806344 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B20706515 : Blo 806344 20706515 := bstep (se 1 (by rfl) ⟨15529886, by rfl⟩ : syracuseStep 20706515 = 31059773) B31059773
theorem B1209671 : Blo 806344 1209671 := bstep (se 1 (by rfl) ⟨907253, by rfl⟩ : syracuseStep 1209671 = 1814507) B1814507
theorem B1210139 : Blo 806344 1210139 := bstep (se 1 (by rfl) ⟨907604, by rfl⟩ : syracuseStep 1210139 = 1815209) B1815209
theorem B1309375 : Blo 806344 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B5176811 : Blo 806344 5176811 := bstep (se 1 (by rfl) ⟨3882608, by rfl⟩ : syracuseStep 5176811 = 7765217) B7765217
theorem B3112843 : Blo 806344 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B1213751 : Blo 806344 1213751 := bstep (se 1 (by rfl) ⟨910313, by rfl⟩ : syracuseStep 1213751 = 1820627) B1820627
theorem B6983333 : Blo 806344 6983333 := bstep (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) B1309375
theorem B3116879 : Blo 806344 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B33230897 : Blo 806344 33230897 := bstep (se 2 (by rfl) ⟨12461586, by rfl⟩ : syracuseStep 33230897 = 24923173) B24923173
theorem B49714337 : Blo 806344 49714337 := bstep (se 2 (by rfl) ⟨18642876, by rfl⟩ : syracuseStep 49714337 = 37285753) B37285753
theorem B12457597 : Blo 806344 12457597 := bstep (se 3 (by rfl) ⟨2335799, by rfl⟩ : syracuseStep 12457597 = 4671599) B4671599
theorem B2725757 : Blo 806344 2725757 := bstep (se 3 (by rfl) ⟨511079, by rfl⟩ : syracuseStep 2725757 = 1022159) B1022159
theorem B198877031 : Blo 806344 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B3678443 : Blo 806344 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B13804343 : Blo 806344 13804343 := bstep (se 1 (by rfl) ⟨10353257, by rfl⟩ : syracuseStep 13804343 = 20706515) B20706515
theorem B15573869 : Blo 806344 15573869 := bstep (se 3 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 15573869 = 5840201) B5840201
theorem B2041625 : Blo 806344 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B9185399 : Blo 806344 9185399 := bstep (se 1 (by rfl) ⟨6889049, by rfl⟩ : syracuseStep 9185399 = 13778099) B13778099
theorem B3451207 : Blo 806344 3451207 := bstep (se 1 (by rfl) ⟨2588405, by rfl⟩ : syracuseStep 3451207 = 5176811) B5176811
theorem B6138665 : Blo 806344 6138665 := bstep (se 2 (by rfl) ⟨2301999, by rfl⟩ : syracuseStep 6138665 = 4603999) B4603999
theorem B2731751 : Blo 806344 2731751 := bstep (se 1 (by rfl) ⟨2048813, by rfl⟩ : syracuseStep 2731751 = 4097627) B4097627
theorem B2734559 : Blo 806344 2734559 := bstep (se 1 (by rfl) ⟨2050919, by rfl⟩ : syracuseStep 2734559 = 4101839) B4101839
theorem B6307067 : Blo 806344 6307067 := bstep (se 1 (by rfl) ⟨4730300, by rfl⟩ : syracuseStep 6307067 = 9460601) B9460601
theorem B1819115 : Blo 806344 1819115 := bstep (se 1 (by rfl) ⟨1364336, by rfl⟩ : syracuseStep 1819115 = 2728673) B2728673
theorem B1723007 : Blo 806344 1723007 := bstep (se 1 (by rfl) ⟨1292255, by rfl⟩ : syracuseStep 1723007 = 2584511) B2584511
theorem B1723049 : Blo 806344 1723049 := bstep (se 2 (by rfl) ⟨646143, by rfl⟩ : syracuseStep 1723049 = 1292287) B1292287
theorem B969499 : Blo 806344 969499 := bstep (se 1 (by rfl) ⟨727124, by rfl⟩ : syracuseStep 969499 = 1454249) B1454249
theorem B806447 : Blo 806344 806447 := bstep (se 1 (by rfl) ⟨604835, by rfl⟩ : syracuseStep 806447 = 1209671) B1209671
theorem B806759 : Blo 806344 806759 := bstep (se 1 (by rfl) ⟨605069, by rfl⟩ : syracuseStep 806759 = 1210139) B1210139
theorem B1363871 : Blo 806344 1363871 := bstep (se 1 (by rfl) ⟨1022903, by rfl⟩ : syracuseStep 1363871 = 2045807) B2045807
theorem B971887 : Blo 806344 971887 := bstep (se 1 (by rfl) ⟨728915, by rfl⟩ : syracuseStep 971887 = 1457831) B1457831
theorem B4150457 : Blo 806344 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B808955 : Blo 806344 808955 := bstep (se 1 (by rfl) ⟨606716, by rfl⟩ : syracuseStep 808955 = 1213433) B1213433
theorem B809703 : Blo 806344 809703 := bstep (se 1 (by rfl) ⟨607277, by rfl⟩ : syracuseStep 809703 = 1214555) B1214555
theorem B809723 : Blo 806344 809723 := bstep (se 1 (by rfl) ⟨607292, by rfl⟩ : syracuseStep 809723 = 1214585) B1214585
theorem B11657105 : Blo 806344 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B910183 : Blo 806344 910183 := bstep (se 1 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 910183 = 1365275) B1365275
theorem B1729883 : Blo 806344 1729883 := bstep (se 1 (by rfl) ⟨1297412, by rfl⟩ : syracuseStep 1729883 = 2594825) B2594825
theorem B13821839 : Blo 806344 13821839 := bstep (se 1 (by rfl) ⟨10366379, by rfl⟩ : syracuseStep 13821839 = 20732759) B20732759
theorem B1209791 : Blo 806344 1209791 := bstep (se 1 (by rfl) ⟨907343, by rfl⟩ : syracuseStep 1209791 = 1814687) B1814687
theorem B1210025 : Blo 806344 1210025 := bstep (se 2 (by rfl) ⟨453759, by rfl⟩ : syracuseStep 1210025 = 907519) B907519
theorem B14940035 : Blo 806344 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B9207269 : Blo 806344 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B1212143 : Blo 806344 1212143 := bstep (se 1 (by rfl) ⟨909107, by rfl⟩ : syracuseStep 1212143 = 1818215) B1818215
theorem B1212743 : Blo 806344 1212743 := bstep (se 1 (by rfl) ⟨909557, by rfl⟩ : syracuseStep 1212743 = 1819115) B1819115
theorem B1213577 : Blo 806344 1213577 := bstep (se 2 (by rfl) ⟨455091, by rfl⟩ : syracuseStep 1213577 = 910183) B910183
theorem B1148671 : Blo 806344 1148671 := bstep (se 1 (by rfl) ⟨861503, by rfl⟩ : syracuseStep 1148671 = 1723007) B1723007
theorem B1148699 : Blo 806344 1148699 := bstep (se 1 (by rfl) ⟨861524, by rfl⟩ : syracuseStep 1148699 = 1723049) B1723049
theorem B4655555 : Blo 806344 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B22153931 : Blo 806344 22153931 := bstep (se 1 (by rfl) ⟨16615448, by rfl⟩ : syracuseStep 22153931 = 33230897) B33230897
theorem B132584687 : Blo 806344 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B7771403 : Blo 806344 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B9214559 : Blo 806344 9214559 := bstep (se 1 (by rfl) ⟨6910919, by rfl⟩ : syracuseStep 9214559 = 13821839) B13821839
theorem B4204711 : Blo 806344 4204711 := bstep (se 1 (by rfl) ⟨3153533, by rfl⟩ : syracuseStep 4204711 = 6307067) B6307067
theorem B6138179 : Blo 806344 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B2077919 : Blo 806344 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B4601609 : Blo 806344 4601609 := bstep (se 2 (by rfl) ⟨1725603, by rfl⟩ : syracuseStep 4601609 = 3451207) B3451207
theorem B33142891 : Blo 806344 33142891 := bstep (se 1 (by rfl) ⟨24857168, by rfl⟩ : syracuseStep 33142891 = 49714337) B49714337
theorem B2766971 : Blo 806344 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B1817171 : Blo 806344 1817171 := bstep (se 1 (by rfl) ⟨1362878, by rfl⟩ : syracuseStep 1817171 = 2725757) B2725757
theorem B1361083 : Blo 806344 1361083 := bstep (se 1 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 1361083 = 2041625) B2041625
theorem B1295849 : Blo 806344 1295849 := bstep (se 2 (by rfl) ⟨485943, by rfl⟩ : syracuseStep 1295849 = 971887) B971887
theorem B1821167 : Blo 806344 1821167 := bstep (se 1 (by rfl) ⟨1365875, by rfl⟩ : syracuseStep 1821167 = 2731751) B2731751
theorem B806527 : Blo 806344 806527 := bstep (se 1 (by rfl) ⟨604895, by rfl⟩ : syracuseStep 806527 = 1209791) B1209791
theorem B806683 : Blo 806344 806683 := bstep (se 1 (by rfl) ⟨605012, by rfl⟩ : syracuseStep 806683 = 1210025) B1210025
theorem B1823039 : Blo 806344 1823039 := bstep (se 1 (by rfl) ⟨1367279, by rfl⟩ : syracuseStep 1823039 = 2734559) B2734559
theorem B808095 : Blo 806344 808095 := bstep (se 1 (by rfl) ⟨606071, by rfl⟩ : syracuseStep 808095 = 1212143) B1212143
theorem B809167 : Blo 806344 809167 := bstep (se 1 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 809167 = 1213751) B1213751
theorem B909247 : Blo 806344 909247 := bstep (se 1 (by rfl) ⟨681935, by rfl⟩ : syracuseStep 909247 = 1363871) B1363871
theorem B4613021 : Blo 806344 4613021 := bstep (se 3 (by rfl) ⟨864941, by rfl⟩ : syracuseStep 4613021 = 1729883) B1729883
theorem B5170661 : Blo 806344 5170661 := bstep (se 4 (by rfl) ⟨484749, by rfl⟩ : syracuseStep 5170661 = 969499) B969499
theorem B2452295 : Blo 806344 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B9202895 : Blo 806344 9202895 := bstep (se 1 (by rfl) ⟨6902171, by rfl⟩ : syracuseStep 9202895 = 13804343) B13804343
theorem B10382579 : Blo 806344 10382579 := bstep (se 1 (by rfl) ⟨7786934, by rfl⟩ : syracuseStep 10382579 = 15573869) B15573869
theorem B6123599 : Blo 806344 6123599 := bstep (se 1 (by rfl) ⟨4592699, by rfl⟩ : syracuseStep 6123599 = 9185399) B9185399
theorem B4092443 : Blo 806344 4092443 := bstep (se 1 (by rfl) ⟨3069332, by rfl⟩ : syracuseStep 4092443 = 6138665) B6138665
theorem B16610129 : Blo 806344 16610129 := bstep (se 2 (by rfl) ⟨6228798, by rfl⟩ : syracuseStep 16610129 = 12457597) B12457597
theorem B9960023 : Blo 806344 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B1214111 : Blo 806344 1214111 := bstep (se 1 (by rfl) ⟨910583, by rfl⟩ : syracuseStep 1214111 = 1821167) B1821167
theorem B1215359 : Blo 806344 1215359 := bstep (se 1 (by rfl) ⟨911519, by rfl⟩ : syracuseStep 1215359 = 1823039) B1823039
theorem B5606281 : Blo 806344 5606281 := bstep (se 2 (by rfl) ⟨2102355, by rfl⟩ : syracuseStep 5606281 = 4204711) B4204711
theorem B5180935 : Blo 806344 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B7378589 : Blo 806344 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B3447107 : Blo 806344 3447107 := bstep (se 1 (by rfl) ⟨2585330, by rfl⟩ : syracuseStep 3447107 = 5170661) B5170661
theorem B6135263 : Blo 806344 6135263 := bstep (se 1 (by rfl) ⟨4601447, by rfl⟩ : syracuseStep 6135263 = 9202895) B9202895
theorem B6921719 : Blo 806344 6921719 := bstep (se 1 (by rfl) ⟨5191289, by rfl⟩ : syracuseStep 6921719 = 10382579) B10382579
theorem B2728295 : Blo 806344 2728295 := bstep (se 1 (by rfl) ⟨2046221, by rfl⟩ : syracuseStep 2728295 = 4092443) B4092443
theorem B1385279 : Blo 806344 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B1814777 : Blo 806344 1814777 := bstep (se 2 (by rfl) ⟨680541, by rfl⟩ : syracuseStep 1814777 = 1361083) B1361083
theorem B88389791 : Blo 806344 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B3455597 : Blo 806344 3455597 := bstep (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) B1295849
theorem B6143039 : Blo 806344 6143039 := bstep (se 1 (by rfl) ⟨4607279, by rfl⟩ : syracuseStep 6143039 = 9214559) B9214559
theorem B3063197 : Blo 806344 3063197 := bstep (se 3 (by rfl) ⟨574349, by rfl⟩ : syracuseStep 3063197 = 1148699) B1148699
theorem B4082399 : Blo 806344 4082399 := bstep (se 1 (by rfl) ⟨3061799, by rfl⟩ : syracuseStep 4082399 = 6123599) B6123599
theorem B44190521 : Blo 806344 44190521 := bstep (se 2 (by rfl) ⟨16571445, by rfl⟩ : syracuseStep 44190521 = 33142891) B33142891
theorem B3067739 : Blo 806344 3067739 := bstep (se 1 (by rfl) ⟨2300804, by rfl⟩ : syracuseStep 3067739 = 4601609) B4601609
theorem B6640015 : Blo 806344 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B808495 : Blo 806344 808495 := bstep (se 1 (by rfl) ⟨606371, by rfl⟩ : syracuseStep 808495 = 1212743) B1212743
theorem B809051 : Blo 806344 809051 := bstep (se 1 (by rfl) ⟨606788, by rfl⟩ : syracuseStep 809051 = 1213577) B1213577
theorem B3103703 : Blo 806344 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B14769287 : Blo 806344 14769287 := bstep (se 1 (by rfl) ⟨11076965, by rfl⟩ : syracuseStep 14769287 = 22153931) B22153931
theorem B1531561 : Blo 806344 1531561 := bstep (se 2 (by rfl) ⟨574335, by rfl⟩ : syracuseStep 1531561 = 1148671) B1148671
theorem B3075347 : Blo 806344 3075347 := bstep (se 1 (by rfl) ⟨2306510, by rfl⟩ : syracuseStep 3075347 = 4613021) B4613021
theorem B4092119 : Blo 806344 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B1634863 : Blo 806344 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B11073419 : Blo 806344 11073419 := bstep (se 1 (by rfl) ⟨8305064, by rfl⟩ : syracuseStep 11073419 = 16610129) B16610129
theorem B1211447 : Blo 806344 1211447 := bstep (se 1 (by rfl) ⟨908585, by rfl⟩ : syracuseStep 1211447 = 1817171) B1817171
theorem B1212329 : Blo 806344 1212329 := bstep (se 2 (by rfl) ⟨454623, by rfl⟩ : syracuseStep 1212329 = 909247) B909247
theorem B2721599 : Blo 806344 2721599 := bstep (se 1 (by rfl) ⟨2041199, by rfl⟩ : syracuseStep 2721599 = 4082399) B4082399
theorem B29460347 : Blo 806344 29460347 := bstep (se 1 (by rfl) ⟨22095260, by rfl⟩ : syracuseStep 29460347 = 44190521) B44190521
theorem B4919059 : Blo 806344 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B7475041 : Blo 806344 7475041 := bstep (se 2 (by rfl) ⟨2803140, by rfl⟩ : syracuseStep 7475041 = 5606281) B5606281
theorem B2298071 : Blo 806344 2298071 := bstep (se 1 (by rfl) ⟨1723553, by rfl⟩ : syracuseStep 2298071 = 3447107) B3447107
theorem B2069135 : Blo 806344 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B8853353 : Blo 806344 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B923519 : Blo 806344 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B2728079 : Blo 806344 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B7382279 : Blo 806344 7382279 := bstep (se 1 (by rfl) ⟨5536709, by rfl⟩ : syracuseStep 7382279 = 11073419) B11073419
theorem B58926527 : Blo 806344 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B2303731 : Blo 806344 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B2042081 : Blo 806344 2042081 := bstep (se 2 (by rfl) ⟨765780, by rfl⟩ : syracuseStep 2042081 = 1531561) B1531561
theorem B2042131 : Blo 806344 2042131 := bstep (se 1 (by rfl) ⟨1531598, by rfl⟩ : syracuseStep 2042131 = 3063197) B3063197
theorem B2045159 : Blo 806344 2045159 := bstep (se 1 (by rfl) ⟨1533869, by rfl⟩ : syracuseStep 2045159 = 3067739) B3067739
theorem B9846191 : Blo 806344 9846191 := bstep (se 1 (by rfl) ⟨7384643, by rfl⟩ : syracuseStep 9846191 = 14769287) B14769287
theorem B1818863 : Blo 806344 1818863 := bstep (se 1 (by rfl) ⟨1364147, by rfl⟩ : syracuseStep 1818863 = 2728295) B2728295
theorem B2179817 : Blo 806344 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B2050231 : Blo 806344 2050231 := bstep (se 1 (by rfl) ⟨1537673, by rfl⟩ : syracuseStep 2050231 = 3075347) B3075347
theorem B807631 : Blo 806344 807631 := bstep (se 1 (by rfl) ⟨605723, by rfl⟩ : syracuseStep 807631 = 1211447) B1211447
theorem B808219 : Blo 806344 808219 := bstep (se 1 (by rfl) ⟨606164, by rfl⟩ : syracuseStep 808219 = 1212329) B1212329
theorem B809407 : Blo 806344 809407 := bstep (se 1 (by rfl) ⟨607055, by rfl⟩ : syracuseStep 809407 = 1214111) B1214111
theorem B810239 : Blo 806344 810239 := bstep (se 1 (by rfl) ⟨607679, by rfl⟩ : syracuseStep 810239 = 1215359) B1215359
theorem B6907913 : Blo 806344 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B4090175 : Blo 806344 4090175 := bstep (se 1 (by rfl) ⟨3067631, by rfl⟩ : syracuseStep 4090175 = 6135263) B6135263
theorem B4614479 : Blo 806344 4614479 := bstep (se 1 (by rfl) ⟨3460859, by rfl⟩ : syracuseStep 4614479 = 6921719) B6921719
theorem B1209851 : Blo 806344 1209851 := bstep (se 1 (by rfl) ⟨907388, by rfl⟩ : syracuseStep 1209851 = 1814777) B1814777
theorem B4095359 : Blo 806344 4095359 := bstep (se 1 (by rfl) ⟨3071519, by rfl⟩ : syracuseStep 4095359 = 6143039) B6143039
theorem B1212575 : Blo 806344 1212575 := bstep (se 1 (by rfl) ⟨909431, by rfl⟩ : syracuseStep 1212575 = 1818863) B1818863
theorem B2722841 : Blo 806344 2722841 := bstep (se 2 (by rfl) ⟨1021065, by rfl⟩ : syracuseStep 2722841 = 2042131) B2042131
theorem B1379423 : Blo 806344 1379423 := bstep (se 1 (by rfl) ⟨1034567, by rfl⟩ : syracuseStep 1379423 = 2069135) B2069135
theorem B5902235 : Blo 806344 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B2462717 : Blo 806344 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B6558745 : Blo 806344 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B9966721 : Blo 806344 9966721 := bstep (se 2 (by rfl) ⟨3737520, by rfl⟩ : syracuseStep 9966721 = 7475041) B7475041
theorem B2726783 : Blo 806344 2726783 := bstep (se 1 (by rfl) ⟨2045087, by rfl⟩ : syracuseStep 2726783 = 4090175) B4090175
theorem B2730239 : Blo 806344 2730239 := bstep (se 1 (by rfl) ⟨2047679, by rfl⟩ : syracuseStep 2730239 = 4095359) B4095359
theorem B6564127 : Blo 806344 6564127 := bstep (se 1 (by rfl) ⟨4923095, by rfl⟩ : syracuseStep 6564127 = 9846191) B9846191
theorem B1453211 : Blo 806344 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B1814399 : Blo 806344 1814399 := bstep (se 1 (by rfl) ⟨1360799, by rfl⟩ : syracuseStep 1814399 = 2721599) B2721599
theorem B19640231 : Blo 806344 19640231 := bstep (se 1 (by rfl) ⟨14730173, by rfl⟩ : syracuseStep 19640231 = 29460347) B29460347
theorem B2733641 : Blo 806344 2733641 := bstep (se 2 (by rfl) ⟨1025115, by rfl⟩ : syracuseStep 2733641 = 2050231) B2050231
theorem B1818719 : Blo 806344 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B4605275 : Blo 806344 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B1361387 : Blo 806344 1361387 := bstep (se 1 (by rfl) ⟨1021040, by rfl⟩ : syracuseStep 1361387 = 2042081) B2042081
theorem B1363439 : Blo 806344 1363439 := bstep (se 1 (by rfl) ⟨1022579, by rfl⟩ : syracuseStep 1363439 = 2045159) B2045159
theorem B806567 : Blo 806344 806567 := bstep (se 1 (by rfl) ⟨604925, by rfl⟩ : syracuseStep 806567 = 1209851) B1209851
theorem B3071641 : Blo 806344 3071641 := bstep (se 2 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 3071641 = 2303731) B2303731
theorem B1532047 : Blo 806344 1532047 := bstep (se 1 (by rfl) ⟨1149035, by rfl⟩ : syracuseStep 1532047 = 2298071) B2298071
theorem B19686077 : Blo 806344 19686077 := bstep (se 3 (by rfl) ⟨3691139, by rfl⟩ : syracuseStep 19686077 = 7382279) B7382279
theorem B39284351 : Blo 806344 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B3076319 : Blo 806344 3076319 := bstep (se 1 (by rfl) ⟨2307239, by rfl⟩ : syracuseStep 3076319 = 4614479) B4614479
theorem B1212479 : Blo 806344 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B919615 : Blo 806344 919615 := bstep (se 1 (by rfl) ⟨689711, by rfl⟩ : syracuseStep 919615 = 1379423) B1379423
theorem B3934823 : Blo 806344 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B8752169 : Blo 806344 8752169 := bstep (se 2 (by rfl) ⟨3282063, by rfl⟩ : syracuseStep 8752169 = 6564127) B6564127
theorem B1641811 : Blo 806344 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B26189567 : Blo 806344 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B2042729 : Blo 806344 2042729 := bstep (se 2 (by rfl) ⟨766023, by rfl⟩ : syracuseStep 2042729 = 1532047) B1532047
theorem B1815227 : Blo 806344 1815227 := bstep (se 1 (by rfl) ⟨1361420, by rfl⟩ : syracuseStep 1815227 = 2722841) B2722841
theorem B1817855 : Blo 806344 1817855 := bstep (se 1 (by rfl) ⟨1363391, by rfl⟩ : syracuseStep 1817855 = 2726783) B2726783
theorem B13124051 : Blo 806344 13124051 := bstep (se 1 (by rfl) ⟨9843038, by rfl⟩ : syracuseStep 13124051 = 19686077) B19686077
theorem B1820159 : Blo 806344 1820159 := bstep (se 1 (by rfl) ⟨1365119, by rfl⟩ : syracuseStep 1820159 = 2730239) B2730239
theorem B13288961 : Blo 806344 13288961 := bstep (se 2 (by rfl) ⟨4983360, by rfl⟩ : syracuseStep 13288961 = 9966721) B9966721
theorem B968807 : Blo 806344 968807 := bstep (se 1 (by rfl) ⟨726605, by rfl⟩ : syracuseStep 968807 = 1453211) B1453211
theorem B13093487 : Blo 806344 13093487 := bstep (se 1 (by rfl) ⟨9820115, by rfl⟩ : syracuseStep 13093487 = 19640231) B19640231
theorem B2050879 : Blo 806344 2050879 := bstep (se 1 (by rfl) ⟨1538159, by rfl⟩ : syracuseStep 2050879 = 3076319) B3076319
theorem B1822427 : Blo 806344 1822427 := bstep (se 1 (by rfl) ⟨1366820, by rfl⟩ : syracuseStep 1822427 = 2733641) B2733641
theorem B808383 : Blo 806344 808383 := bstep (se 1 (by rfl) ⟨606287, by rfl⟩ : syracuseStep 808383 = 1212575) B1212575
theorem B3070183 : Blo 806344 3070183 := bstep (se 1 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 3070183 = 4605275) B4605275
theorem B907591 : Blo 806344 907591 := bstep (se 1 (by rfl) ⟨680693, by rfl⟩ : syracuseStep 907591 = 1361387) B1361387
theorem B908959 : Blo 806344 908959 := bstep (se 1 (by rfl) ⟨681719, by rfl⟩ : syracuseStep 908959 = 1363439) B1363439
theorem B8744993 : Blo 806344 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B1209599 : Blo 806344 1209599 := bstep (se 1 (by rfl) ⟨907199, by rfl⟩ : syracuseStep 1209599 = 1814399) B1814399
theorem B4095521 : Blo 806344 4095521 := bstep (se 2 (by rfl) ⟨1535820, by rfl⟩ : syracuseStep 4095521 = 3071641) B3071641
theorem B8749367 : Blo 806344 8749367 := bstep (se 1 (by rfl) ⟨6562025, by rfl⟩ : syracuseStep 8749367 = 13124051) B13124051
theorem B1213439 : Blo 806344 1213439 := bstep (se 1 (by rfl) ⟨910079, by rfl⟩ : syracuseStep 1213439 = 1820159) B1820159
theorem B1214951 : Blo 806344 1214951 := bstep (se 1 (by rfl) ⟨911213, by rfl⟩ : syracuseStep 1214951 = 1822427) B1822427
theorem B10492861 : Blo 806344 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B23339117 : Blo 806344 23339117 := bstep (se 3 (by rfl) ⟨4376084, by rfl⟩ : syracuseStep 23339117 = 8752169) B8752169
theorem B2730347 : Blo 806344 2730347 := bstep (se 1 (by rfl) ⟨2047760, by rfl⟩ : syracuseStep 2730347 = 4095521) B4095521
theorem B8859307 : Blo 806344 8859307 := bstep (se 1 (by rfl) ⟨6644480, by rfl⟩ : syracuseStep 8859307 = 13288961) B13288961
theorem B8728991 : Blo 806344 8728991 := bstep (se 1 (by rfl) ⟨6546743, by rfl⟩ : syracuseStep 8728991 = 13093487) B13093487
theorem B1226153 : Blo 806344 1226153 := bstep (se 2 (by rfl) ⟨459807, by rfl⟩ : syracuseStep 1226153 = 919615) B919615
theorem B2734505 : Blo 806344 2734505 := bstep (se 2 (by rfl) ⟨1025439, by rfl⟩ : syracuseStep 2734505 = 2050879) B2050879
theorem B1361819 : Blo 806344 1361819 := bstep (se 1 (by rfl) ⟨1021364, by rfl⟩ : syracuseStep 1361819 = 2042729) B2042729
theorem B806399 : Blo 806344 806399 := bstep (se 1 (by rfl) ⟨604799, by rfl⟩ : syracuseStep 806399 = 1209599) B1209599
theorem B808319 : Blo 806344 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B2189081 : Blo 806344 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B17459711 : Blo 806344 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B2583485 : Blo 806344 2583485 := bstep (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) B968807
theorem B5829995 : Blo 806344 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B4093577 : Blo 806344 4093577 := bstep (se 2 (by rfl) ⟨1535091, by rfl⟩ : syracuseStep 4093577 = 3070183) B3070183
theorem B1210121 : Blo 806344 1210121 := bstep (se 2 (by rfl) ⟨453795, by rfl⟩ : syracuseStep 1210121 = 907591) B907591
theorem B1210151 : Blo 806344 1210151 := bstep (se 1 (by rfl) ⟨907613, by rfl⟩ : syracuseStep 1210151 = 1815227) B1815227
theorem B1211903 : Blo 806344 1211903 := bstep (se 1 (by rfl) ⟨908927, by rfl⟩ : syracuseStep 1211903 = 1817855) B1817855
theorem B1211945 : Blo 806344 1211945 := bstep (se 2 (by rfl) ⟨454479, by rfl⟩ : syracuseStep 1211945 = 908959) B908959
theorem B5832911 : Blo 806344 5832911 := bstep (se 1 (by rfl) ⟨4374683, by rfl⟩ : syracuseStep 5832911 = 8749367) B8749367
theorem B11639807 : Blo 806344 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B2729051 : Blo 806344 2729051 := bstep (se 1 (by rfl) ⟨2046788, by rfl⟩ : syracuseStep 2729051 = 4093577) B4093577
theorem B15546653 : Blo 806344 15546653 := bstep (se 3 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 15546653 = 5829995) B5829995
theorem B11812409 : Blo 806344 11812409 := bstep (se 2 (by rfl) ⟨4429653, by rfl⟩ : syracuseStep 11812409 = 8859307) B8859307
theorem B1459387 : Blo 806344 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B1820231 : Blo 806344 1820231 := bstep (se 1 (by rfl) ⟨1365173, by rfl⟩ : syracuseStep 1820231 = 2730347) B2730347
theorem B1722323 : Blo 806344 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B5819327 : Blo 806344 5819327 := bstep (se 1 (by rfl) ⟨4364495, by rfl⟩ : syracuseStep 5819327 = 8728991) B8728991
theorem B806747 : Blo 806344 806747 := bstep (se 1 (by rfl) ⟨605060, by rfl⟩ : syracuseStep 806747 = 1210121) B1210121
theorem B806767 : Blo 806344 806767 := bstep (se 1 (by rfl) ⟨605075, by rfl⟩ : syracuseStep 806767 = 1210151) B1210151
theorem B1823003 : Blo 806344 1823003 := bstep (se 1 (by rfl) ⟨1367252, by rfl⟩ : syracuseStep 1823003 = 2734505) B2734505
theorem B807935 : Blo 806344 807935 := bstep (se 1 (by rfl) ⟨605951, by rfl⟩ : syracuseStep 807935 = 1211903) B1211903
theorem B807963 : Blo 806344 807963 := bstep (se 1 (by rfl) ⟨605972, by rfl⟩ : syracuseStep 807963 = 1211945) B1211945
theorem B808959 : Blo 806344 808959 := bstep (se 1 (by rfl) ⟨606719, by rfl⟩ : syracuseStep 808959 = 1213439) B1213439
theorem B907879 : Blo 806344 907879 := bstep (se 1 (by rfl) ⟨680909, by rfl⟩ : syracuseStep 907879 = 1361819) B1361819
theorem B809967 : Blo 806344 809967 := bstep (se 1 (by rfl) ⟨607475, by rfl⟩ : syracuseStep 809967 = 1214951) B1214951
theorem B15559411 : Blo 806344 15559411 := bstep (se 1 (by rfl) ⟨11669558, by rfl⟩ : syracuseStep 15559411 = 23339117) B23339117
theorem B817435 : Blo 806344 817435 := bstep (se 1 (by rfl) ⟨613076, by rfl⟩ : syracuseStep 817435 = 1226153) B1226153
theorem B13990481 : Blo 806344 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B1213487 : Blo 806344 1213487 := bstep (se 1 (by rfl) ⟨910115, by rfl⟩ : syracuseStep 1213487 = 1820231) B1820231
theorem B4359653 : Blo 806344 4359653 := bstep (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) B817435
theorem B1215335 : Blo 806344 1215335 := bstep (se 1 (by rfl) ⟨911501, by rfl⟩ : syracuseStep 1215335 = 1823003) B1823003
theorem B20745881 : Blo 806344 20745881 := bstep (se 2 (by rfl) ⟨7779705, by rfl⟩ : syracuseStep 20745881 = 15559411) B15559411
theorem B4592861 : Blo 806344 4592861 := bstep (se 3 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 4592861 = 1722323) B1722323
theorem B10364435 : Blo 806344 10364435 := bstep (se 1 (by rfl) ⟨7773326, by rfl⟩ : syracuseStep 10364435 = 15546653) B15546653
theorem B7874939 : Blo 806344 7874939 := bstep (se 1 (by rfl) ⟨5906204, by rfl⟩ : syracuseStep 7874939 = 11812409) B11812409
theorem B3879551 : Blo 806344 3879551 := bstep (se 1 (by rfl) ⟨2909663, by rfl⟩ : syracuseStep 3879551 = 5819327) B5819327
theorem B1819367 : Blo 806344 1819367 := bstep (se 1 (by rfl) ⟨1364525, by rfl⟩ : syracuseStep 1819367 = 2729051) B2729051
theorem B7783397 : Blo 806344 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B9326987 : Blo 806344 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B3888607 : Blo 806344 3888607 := bstep (se 1 (by rfl) ⟨2916455, by rfl⟩ : syracuseStep 3888607 = 5832911) B5832911
theorem B7759871 : Blo 806344 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B1210505 : Blo 806344 1210505 := bstep (se 2 (by rfl) ⟨453939, by rfl⟩ : syracuseStep 1210505 = 907879) B907879
theorem B1212911 : Blo 806344 1212911 := bstep (se 1 (by rfl) ⟨909683, by rfl⟩ : syracuseStep 1212911 = 1819367) B1819367
theorem B13830587 : Blo 806344 13830587 := bstep (se 1 (by rfl) ⟨10372940, by rfl⟩ : syracuseStep 13830587 = 20745881) B20745881
theorem B5184809 : Blo 806344 5184809 := bstep (se 2 (by rfl) ⟨1944303, by rfl⟩ : syracuseStep 5184809 = 3888607) B3888607
theorem B5188931 : Blo 806344 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B3061907 : Blo 806344 3061907 := bstep (se 1 (by rfl) ⟨2296430, by rfl⟩ : syracuseStep 3061907 = 4592861) B4592861
theorem B807003 : Blo 806344 807003 := bstep (se 1 (by rfl) ⟨605252, by rfl⟩ : syracuseStep 807003 = 1210505) B1210505
theorem B808991 : Blo 806344 808991 := bstep (se 1 (by rfl) ⟨606743, by rfl⟩ : syracuseStep 808991 = 1213487) B1213487
theorem B2906435 : Blo 806344 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B810223 : Blo 806344 810223 := bstep (se 1 (by rfl) ⟨607667, by rfl⟩ : syracuseStep 810223 = 1215335) B1215335
theorem B6217991 : Blo 806344 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B20999837 : Blo 806344 20999837 := bstep (se 3 (by rfl) ⟨3937469, by rfl⟩ : syracuseStep 20999837 = 7874939) B7874939
theorem B6909623 : Blo 806344 6909623 := bstep (se 1 (by rfl) ⟨5182217, by rfl⟩ : syracuseStep 6909623 = 10364435) B10364435
theorem B5173247 : Blo 806344 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B2586367 : Blo 806344 2586367 := bstep (se 1 (by rfl) ⟨1939775, by rfl⟩ : syracuseStep 2586367 = 3879551) B3879551
theorem B1937623 : Blo 806344 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B3448489 : Blo 806344 3448489 := bstep (se 2 (by rfl) ⟨1293183, by rfl⟩ : syracuseStep 3448489 = 2586367) B2586367
theorem B13999891 : Blo 806344 13999891 := bstep (se 1 (by rfl) ⟨10499918, by rfl⟩ : syracuseStep 13999891 = 20999837) B20999837
theorem B3448831 : Blo 806344 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B2041271 : Blo 806344 2041271 := bstep (se 1 (by rfl) ⟨1530953, by rfl⟩ : syracuseStep 2041271 = 3061907) B3061907
theorem B9220391 : Blo 806344 9220391 := bstep (se 1 (by rfl) ⟨6915293, by rfl⟩ : syracuseStep 9220391 = 13830587) B13830587
theorem B3456539 : Blo 806344 3456539 := bstep (se 1 (by rfl) ⟨2592404, by rfl⟩ : syracuseStep 3456539 = 5184809) B5184809
theorem B4145327 : Blo 806344 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B3459287 : Blo 806344 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B4606415 : Blo 806344 4606415 := bstep (se 1 (by rfl) ⟨3454811, by rfl⟩ : syracuseStep 4606415 = 6909623) B6909623
theorem B808607 : Blo 806344 808607 := bstep (se 1 (by rfl) ⟨606455, by rfl⟩ : syracuseStep 808607 = 1212911) B1212911
theorem B4597985 : Blo 806344 4597985 := bstep (se 2 (by rfl) ⟨1724244, by rfl⟩ : syracuseStep 4597985 = 3448489) B3448489
theorem B2304359 : Blo 806344 2304359 := bstep (se 1 (by rfl) ⟨1728269, by rfl⟩ : syracuseStep 2304359 = 3456539) B3456539
theorem B4598441 : Blo 806344 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B2763551 : Blo 806344 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B9224765 : Blo 806344 9224765 := bstep (se 3 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 9224765 = 3459287) B3459287
theorem B1360847 : Blo 806344 1360847 := bstep (se 1 (by rfl) ⟨1020635, by rfl⟩ : syracuseStep 1360847 = 2041271) B2041271
theorem B6146927 : Blo 806344 6146927 := bstep (se 1 (by rfl) ⟨4610195, by rfl⟩ : syracuseStep 6146927 = 9220391) B9220391
theorem B18666521 : Blo 806344 18666521 := bstep (se 2 (by rfl) ⟨6999945, by rfl⟩ : syracuseStep 18666521 = 13999891) B13999891
theorem B3070943 : Blo 806344 3070943 := bstep (se 1 (by rfl) ⟨2303207, by rfl⟩ : syracuseStep 3070943 = 4606415) B4606415
theorem B2583497 : Blo 806344 2583497 := bstep (se 2 (by rfl) ⟨968811, by rfl⟩ : syracuseStep 2583497 = 1937623) B1937623
theorem B4097951 : Blo 806344 4097951 := bstep (se 1 (by rfl) ⟨3073463, by rfl⟩ : syracuseStep 4097951 = 6146927) B6146927
theorem B1842367 : Blo 806344 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B2047295 : Blo 806344 2047295 := bstep (se 1 (by rfl) ⟨1535471, by rfl⟩ : syracuseStep 2047295 = 3070943) B3070943
theorem B3065323 : Blo 806344 3065323 := bstep (se 1 (by rfl) ⟨2298992, by rfl⟩ : syracuseStep 3065323 = 4597985) B4597985
theorem B3065627 : Blo 806344 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B1722331 : Blo 806344 1722331 := bstep (se 1 (by rfl) ⟨1291748, by rfl⟩ : syracuseStep 1722331 = 2583497) B2583497
theorem B6149843 : Blo 806344 6149843 := bstep (se 1 (by rfl) ⟨4612382, by rfl⟩ : syracuseStep 6149843 = 9224765) B9224765
theorem B907231 : Blo 806344 907231 := bstep (se 1 (by rfl) ⟨680423, by rfl⟩ : syracuseStep 907231 = 1360847) B1360847
theorem B12444347 : Blo 806344 12444347 := bstep (se 1 (by rfl) ⟨9333260, by rfl⟩ : syracuseStep 12444347 = 18666521) B18666521
theorem B1536239 : Blo 806344 1536239 := bstep (se 1 (by rfl) ⟨1152179, by rfl⟩ : syracuseStep 1536239 = 2304359) B2304359
theorem B2296441 : Blo 806344 2296441 := bstep (se 2 (by rfl) ⟨861165, by rfl⟩ : syracuseStep 2296441 = 1722331) B1722331
theorem B4099895 : Blo 806344 4099895 := bstep (se 1 (by rfl) ⟨3074921, by rfl⟩ : syracuseStep 4099895 = 6149843) B6149843
theorem B8296231 : Blo 806344 8296231 := bstep (se 1 (by rfl) ⟨6222173, by rfl⟩ : syracuseStep 8296231 = 12444347) B12444347
theorem B1024159 : Blo 806344 1024159 := bstep (se 1 (by rfl) ⟨768119, by rfl⟩ : syracuseStep 1024159 = 1536239) B1536239
theorem B2043751 : Blo 806344 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B2731967 : Blo 806344 2731967 := bstep (se 1 (by rfl) ⟨2048975, by rfl⟩ : syracuseStep 2731967 = 4097951) B4097951
theorem B1364863 : Blo 806344 1364863 := bstep (se 1 (by rfl) ⟨1023647, by rfl⟩ : syracuseStep 1364863 = 2047295) B2047295
theorem B4087097 : Blo 806344 4087097 := bstep (se 2 (by rfl) ⟨1532661, by rfl⟩ : syracuseStep 4087097 = 3065323) B3065323
theorem B1209641 : Blo 806344 1209641 := bstep (se 2 (by rfl) ⟨453615, by rfl⟩ : syracuseStep 1209641 = 907231) B907231
theorem B2456489 : Blo 806344 2456489 := bstep (se 2 (by rfl) ⟨921183, by rfl⟩ : syracuseStep 2456489 = 1842367) B1842367
theorem B2724731 : Blo 806344 2724731 := bstep (se 1 (by rfl) ⟨2043548, by rfl⟩ : syracuseStep 2724731 = 4087097) B4087097
theorem B2725001 : Blo 806344 2725001 := bstep (se 2 (by rfl) ⟨1021875, by rfl⟩ : syracuseStep 2725001 = 2043751) B2043751
theorem B2733263 : Blo 806344 2733263 := bstep (se 1 (by rfl) ⟨2049947, by rfl⟩ : syracuseStep 2733263 = 4099895) B4099895
theorem B3061921 : Blo 806344 3061921 := bstep (se 2 (by rfl) ⟨1148220, by rfl⟩ : syracuseStep 3061921 = 2296441) B2296441
theorem B1819817 : Blo 806344 1819817 := bstep (se 2 (by rfl) ⟨682431, by rfl⟩ : syracuseStep 1819817 = 1364863) B1364863
theorem B11061641 : Blo 806344 11061641 := bstep (se 2 (by rfl) ⟨4148115, by rfl⟩ : syracuseStep 11061641 = 8296231) B8296231
theorem B1821311 : Blo 806344 1821311 := bstep (se 1 (by rfl) ⟨1365983, by rfl⟩ : syracuseStep 1821311 = 2731967) B2731967
theorem B806427 : Blo 806344 806427 := bstep (se 1 (by rfl) ⟨604820, by rfl⟩ : syracuseStep 806427 = 1209641) B1209641
theorem B1365545 : Blo 806344 1365545 := bstep (se 2 (by rfl) ⟨512079, by rfl⟩ : syracuseStep 1365545 = 1024159) B1024159
theorem B1637659 : Blo 806344 1637659 := bstep (se 1 (by rfl) ⟨1228244, by rfl⟩ : syracuseStep 1637659 = 2456489) B2456489
theorem B1213211 : Blo 806344 1213211 := bstep (se 1 (by rfl) ⟨909908, by rfl⟩ : syracuseStep 1213211 = 1819817) B1819817
theorem B1214207 : Blo 806344 1214207 := bstep (se 1 (by rfl) ⟨910655, by rfl⟩ : syracuseStep 1214207 = 1821311) B1821311
theorem B29497709 : Blo 806344 29497709 := bstep (se 3 (by rfl) ⟨5530820, by rfl⟩ : syracuseStep 29497709 = 11061641) B11061641
theorem B1816487 : Blo 806344 1816487 := bstep (se 1 (by rfl) ⟨1362365, by rfl⟩ : syracuseStep 1816487 = 2724731) B2724731
theorem B1816667 : Blo 806344 1816667 := bstep (se 1 (by rfl) ⟨1362500, by rfl⟩ : syracuseStep 1816667 = 2725001) B2725001
theorem B4082561 : Blo 806344 4082561 := bstep (se 2 (by rfl) ⟨1530960, by rfl⟩ : syracuseStep 4082561 = 3061921) B3061921
theorem B1822175 : Blo 806344 1822175 := bstep (se 1 (by rfl) ⟨1366631, by rfl⟩ : syracuseStep 1822175 = 2733263) B2733263
theorem B2183545 : Blo 806344 2183545 := bstep (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) B1637659
theorem B910363 : Blo 806344 910363 := bstep (se 1 (by rfl) ⟨682772, by rfl⟩ : syracuseStep 910363 = 1365545) B1365545
theorem B1213817 : Blo 806344 1213817 := bstep (se 2 (by rfl) ⟨455181, by rfl⟩ : syracuseStep 1213817 = 910363) B910363
theorem B2721707 : Blo 806344 2721707 := bstep (se 1 (by rfl) ⟨2041280, by rfl⟩ : syracuseStep 2721707 = 4082561) B4082561
theorem B1214783 : Blo 806344 1214783 := bstep (se 1 (by rfl) ⟨911087, by rfl⟩ : syracuseStep 1214783 = 1822175) B1822175
theorem B19665139 : Blo 806344 19665139 := bstep (se 1 (by rfl) ⟨14748854, by rfl⟩ : syracuseStep 19665139 = 29497709) B29497709
theorem B808807 : Blo 806344 808807 := bstep (se 1 (by rfl) ⟨606605, by rfl⟩ : syracuseStep 808807 = 1213211) B1213211
theorem B809471 : Blo 806344 809471 := bstep (se 1 (by rfl) ⟨607103, by rfl⟩ : syracuseStep 809471 = 1214207) B1214207
theorem B2911393 : Blo 806344 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B1210991 : Blo 806344 1210991 := bstep (se 1 (by rfl) ⟨908243, by rfl⟩ : syracuseStep 1210991 = 1816487) B1816487
theorem B1211111 : Blo 806344 1211111 := bstep (se 1 (by rfl) ⟨908333, by rfl⟩ : syracuseStep 1211111 = 1816667) B1816667
theorem B26220185 : Blo 806344 26220185 := bstep (se 2 (by rfl) ⟨9832569, by rfl⟩ : syracuseStep 26220185 = 19665139) B19665139
theorem B1814471 : Blo 806344 1814471 := bstep (se 1 (by rfl) ⟨1360853, by rfl⟩ : syracuseStep 1814471 = 2721707) B2721707
theorem B3881857 : Blo 806344 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B807327 : Blo 806344 807327 := bstep (se 1 (by rfl) ⟨605495, by rfl⟩ : syracuseStep 807327 = 1210991) B1210991
theorem B807407 : Blo 806344 807407 := bstep (se 1 (by rfl) ⟨605555, by rfl⟩ : syracuseStep 807407 = 1211111) B1211111
theorem B809211 : Blo 806344 809211 := bstep (se 1 (by rfl) ⟨606908, by rfl⟩ : syracuseStep 809211 = 1213817) B1213817
theorem B809855 : Blo 806344 809855 := bstep (se 1 (by rfl) ⟨607391, by rfl⟩ : syracuseStep 809855 = 1214783) B1214783
theorem B17480123 : Blo 806344 17480123 := bstep (se 1 (by rfl) ⟨13110092, by rfl⟩ : syracuseStep 17480123 = 26220185) B26220185
theorem B1209647 : Blo 806344 1209647 := bstep (se 1 (by rfl) ⟨907235, by rfl⟩ : syracuseStep 1209647 = 1814471) B1814471
theorem B5175809 : Blo 806344 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B3450539 : Blo 806344 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B806431 : Blo 806344 806431 := bstep (se 1 (by rfl) ⟨604823, by rfl⟩ : syracuseStep 806431 = 1209647) B1209647
theorem B11653415 : Blo 806344 11653415 := bstep (se 1 (by rfl) ⟨8740061, by rfl⟩ : syracuseStep 11653415 = 17480123) B17480123
theorem B7768943 : Blo 806344 7768943 := bstep (se 1 (by rfl) ⟨5826707, by rfl⟩ : syracuseStep 7768943 = 11653415) B11653415
theorem B9201437 : Blo 806344 9201437 := bstep (se 3 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 9201437 = 3450539) B3450539
theorem B5179295 : Blo 806344 5179295 := bstep (se 1 (by rfl) ⟨3884471, by rfl⟩ : syracuseStep 5179295 = 7768943) B7768943
theorem B6134291 : Blo 806344 6134291 := bstep (se 1 (by rfl) ⟨4600718, by rfl⟩ : syracuseStep 6134291 = 9201437) B9201437
theorem B3452863 : Blo 806344 3452863 := bstep (se 1 (by rfl) ⟨2589647, by rfl⟩ : syracuseStep 3452863 = 5179295) B5179295
theorem B4089527 : Blo 806344 4089527 := bstep (se 1 (by rfl) ⟨3067145, by rfl⟩ : syracuseStep 4089527 = 6134291) B6134291
theorem B2726351 : Blo 806344 2726351 := bstep (se 1 (by rfl) ⟨2044763, by rfl⟩ : syracuseStep 2726351 = 4089527) B4089527
theorem B4603817 : Blo 806344 4603817 := bstep (se 2 (by rfl) ⟨1726431, by rfl⟩ : syracuseStep 4603817 = 3452863) B3452863
theorem B1817567 : Blo 806344 1817567 := bstep (se 1 (by rfl) ⟨1363175, by rfl⟩ : syracuseStep 1817567 = 2726351) B2726351
theorem B3069211 : Blo 806344 3069211 := bstep (se 1 (by rfl) ⟨2301908, by rfl⟩ : syracuseStep 3069211 = 4603817) B4603817
theorem B4092281 : Blo 806344 4092281 := bstep (se 2 (by rfl) ⟨1534605, by rfl⟩ : syracuseStep 4092281 = 3069211) B3069211
theorem B1211711 : Blo 806344 1211711 := bstep (se 1 (by rfl) ⟨908783, by rfl⟩ : syracuseStep 1211711 = 1817567) B1817567
theorem B2728187 : Blo 806344 2728187 := bstep (se 1 (by rfl) ⟨2046140, by rfl⟩ : syracuseStep 2728187 = 4092281) B4092281
theorem B807807 : Blo 806344 807807 := bstep (se 1 (by rfl) ⟨605855, by rfl⟩ : syracuseStep 807807 = 1211711) B1211711
theorem B1818791 : Blo 806344 1818791 := bstep (se 1 (by rfl) ⟨1364093, by rfl⟩ : syracuseStep 1818791 = 2728187) B2728187
theorem B1212527 : Blo 806344 1212527 := bstep (se 1 (by rfl) ⟨909395, by rfl⟩ : syracuseStep 1212527 = 1818791) B1818791
theorem B808351 : Blo 806344 808351 := bstep (se 1 (by rfl) ⟨606263, by rfl⟩ : syracuseStep 808351 = 1212527) B1212527

theorem C0 (j : ℕ) (h1 : 201586 ≤ j) (h2 : j ≤ 202285) : Blo 806344 (4 * j + 3) := by
  interval_cases j
  · exact B806347
  · exact B806351
  · exact B806355
  · exact B806359
  · exact B806363
  · exact B806367
  · exact B806371
  · exact B806375
  · exact B806379
  · exact B806383
  · exact B806387
  · exact B806391
  · exact B806395
  · exact B806399
  · exact B806403
  · exact B806407
  · exact B806411
  · exact B806415
  · exact B806419
  · exact B806423
  · exact B806427
  · exact B806431
  · exact B806435
  · exact B806439
  · exact B806443
  · exact B806447
  · exact B806451
  · exact B806455
  · exact B806459
  · exact B806463
  · exact B806467
  · exact B806471
  · exact B806475
  · exact B806479
  · exact B806483
  · exact B806487
  · exact B806491
  · exact B806495
  · exact B806499
  · exact B806503
  · exact B806507
  · exact B806511
  · exact B806515
  · exact B806519
  · exact B806523
  · exact B806527
  · exact B806531
  · exact B806535
  · exact B806539
  · exact B806543
  · exact B806547
  · exact B806551
  · exact B806555
  · exact B806559
  · exact B806563
  · exact B806567
  · exact B806571
  · exact B806575
  · exact B806579
  · exact B806583
  · exact B806587
  · exact B806591
  · exact B806595
  · exact B806599
  · exact B806603
  · exact B806607
  · exact B806611
  · exact B806615
  · exact B806619
  · exact B806623
  · exact B806627
  · exact B806631
  · exact B806635
  · exact B806639
  · exact B806643
  · exact B806647
  · exact B806651
  · exact B806655
  · exact B806659
  · exact B806663
  · exact B806667
  · exact B806671
  · exact B806675
  · exact B806679
  · exact B806683
  · exact B806687
  · exact B806691
  · exact B806695
  · exact B806699
  · exact B806703
  · exact B806707
  · exact B806711
  · exact B806715
  · exact B806719
  · exact B806723
  · exact B806727
  · exact B806731
  · exact B806735
  · exact B806739
  · exact B806743
  · exact B806747
  · exact B806751
  · exact B806755
  · exact B806759
  · exact B806763
  · exact B806767
  · exact B806771
  · exact B806775
  · exact B806779
  · exact B806783
  · exact B806787
  · exact B806791
  · exact B806795
  · exact B806799
  · exact B806803
  · exact B806807
  · exact B806811
  · exact B806815
  · exact B806819
  · exact B806823
  · exact B806827
  · exact B806831
  · exact B806835
  · exact B806839
  · exact B806843
  · exact B806847
  · exact B806851
  · exact B806855
  · exact B806859
  · exact B806863
  · exact B806867
  · exact B806871
  · exact B806875
  · exact B806879
  · exact B806883
  · exact B806887
  · exact B806891
  · exact B806895
  · exact B806899
  · exact B806903
  · exact B806907
  · exact B806911
  · exact B806915
  · exact B806919
  · exact B806923
  · exact B806927
  · exact B806931
  · exact B806935
  · exact B806939
  · exact B806943
  · exact B806947
  · exact B806951
  · exact B806955
  · exact B806959
  · exact B806963
  · exact B806967
  · exact B806971
  · exact B806975
  · exact B806979
  · exact B806983
  · exact B806987
  · exact B806991
  · exact B806995
  · exact B806999
  · exact B807003
  · exact B807007
  · exact B807011
  · exact B807015
  · exact B807019
  · exact B807023
  · exact B807027
  · exact B807031
  · exact B807035
  · exact B807039
  · exact B807043
  · exact B807047
  · exact B807051
  · exact B807055
  · exact B807059
  · exact B807063
  · exact B807067
  · exact B807071
  · exact B807075
  · exact B807079
  · exact B807083
  · exact B807087
  · exact B807091
  · exact B807095
  · exact B807099
  · exact B807103
  · exact B807107
  · exact B807111
  · exact B807115
  · exact B807119
  · exact B807123
  · exact B807127
  · exact B807131
  · exact B807135
  · exact B807139
  · exact B807143
  · exact B807147
  · exact B807151
  · exact B807155
  · exact B807159
  · exact B807163
  · exact B807167
  · exact B807171
  · exact B807175
  · exact B807179
  · exact B807183
  · exact B807187
  · exact B807191
  · exact B807195
  · exact B807199
  · exact B807203
  · exact B807207
  · exact B807211
  · exact B807215
  · exact B807219
  · exact B807223
  · exact B807227
  · exact B807231
  · exact B807235
  · exact B807239
  · exact B807243
  · exact B807247
  · exact B807251
  · exact B807255
  · exact B807259
  · exact B807263
  · exact B807267
  · exact B807271
  · exact B807275
  · exact B807279
  · exact B807283
  · exact B807287
  · exact B807291
  · exact B807295
  · exact B807299
  · exact B807303
  · exact B807307
  · exact B807311
  · exact B807315
  · exact B807319
  · exact B807323
  · exact B807327
  · exact B807331
  · exact B807335
  · exact B807339
  · exact B807343
  · exact B807347
  · exact B807351
  · exact B807355
  · exact B807359
  · exact B807363
  · exact B807367
  · exact B807371
  · exact B807375
  · exact B807379
  · exact B807383
  · exact B807387
  · exact B807391
  · exact B807395
  · exact B807399
  · exact B807403
  · exact B807407
  · exact B807411
  · exact B807415
  · exact B807419
  · exact B807423
  · exact B807427
  · exact B807431
  · exact B807435
  · exact B807439
  · exact B807443
  · exact B807447
  · exact B807451
  · exact B807455
  · exact B807459
  · exact B807463
  · exact B807467
  · exact B807471
  · exact B807475
  · exact B807479
  · exact B807483
  · exact B807487
  · exact B807491
  · exact B807495
  · exact B807499
  · exact B807503
  · exact B807507
  · exact B807511
  · exact B807515
  · exact B807519
  · exact B807523
  · exact B807527
  · exact B807531
  · exact B807535
  · exact B807539
  · exact B807543
  · exact B807547
  · exact B807551
  · exact B807555
  · exact B807559
  · exact B807563
  · exact B807567
  · exact B807571
  · exact B807575
  · exact B807579
  · exact B807583
  · exact B807587
  · exact B807591
  · exact B807595
  · exact B807599
  · exact B807603
  · exact B807607
  · exact B807611
  · exact B807615
  · exact B807619
  · exact B807623
  · exact B807627
  · exact B807631
  · exact B807635
  · exact B807639
  · exact B807643
  · exact B807647
  · exact B807651
  · exact B807655
  · exact B807659
  · exact B807663
  · exact B807667
  · exact B807671
  · exact B807675
  · exact B807679
  · exact B807683
  · exact B807687
  · exact B807691
  · exact B807695
  · exact B807699
  · exact B807703
  · exact B807707
  · exact B807711
  · exact B807715
  · exact B807719
  · exact B807723
  · exact B807727
  · exact B807731
  · exact B807735
  · exact B807739
  · exact B807743
  · exact B807747
  · exact B807751
  · exact B807755
  · exact B807759
  · exact B807763
  · exact B807767
  · exact B807771
  · exact B807775
  · exact B807779
  · exact B807783
  · exact B807787
  · exact B807791
  · exact B807795
  · exact B807799
  · exact B807803
  · exact B807807
  · exact B807811
  · exact B807815
  · exact B807819
  · exact B807823
  · exact B807827
  · exact B807831
  · exact B807835
  · exact B807839
  · exact B807843
  · exact B807847
  · exact B807851
  · exact B807855
  · exact B807859
  · exact B807863
  · exact B807867
  · exact B807871
  · exact B807875
  · exact B807879
  · exact B807883
  · exact B807887
  · exact B807891
  · exact B807895
  · exact B807899
  · exact B807903
  · exact B807907
  · exact B807911
  · exact B807915
  · exact B807919
  · exact B807923
  · exact B807927
  · exact B807931
  · exact B807935
  · exact B807939
  · exact B807943
  · exact B807947
  · exact B807951
  · exact B807955
  · exact B807959
  · exact B807963
  · exact B807967
  · exact B807971
  · exact B807975
  · exact B807979
  · exact B807983
  · exact B807987
  · exact B807991
  · exact B807995
  · exact B807999
  · exact B808003
  · exact B808007
  · exact B808011
  · exact B808015
  · exact B808019
  · exact B808023
  · exact B808027
  · exact B808031
  · exact B808035
  · exact B808039
  · exact B808043
  · exact B808047
  · exact B808051
  · exact B808055
  · exact B808059
  · exact B808063
  · exact B808067
  · exact B808071
  · exact B808075
  · exact B808079
  · exact B808083
  · exact B808087
  · exact B808091
  · exact B808095
  · exact B808099
  · exact B808103
  · exact B808107
  · exact B808111
  · exact B808115
  · exact B808119
  · exact B808123
  · exact B808127
  · exact B808131
  · exact B808135
  · exact B808139
  · exact B808143
  · exact B808147
  · exact B808151
  · exact B808155
  · exact B808159
  · exact B808163
  · exact B808167
  · exact B808171
  · exact B808175
  · exact B808179
  · exact B808183
  · exact B808187
  · exact B808191
  · exact B808195
  · exact B808199
  · exact B808203
  · exact B808207
  · exact B808211
  · exact B808215
  · exact B808219
  · exact B808223
  · exact B808227
  · exact B808231
  · exact B808235
  · exact B808239
  · exact B808243
  · exact B808247
  · exact B808251
  · exact B808255
  · exact B808259
  · exact B808263
  · exact B808267
  · exact B808271
  · exact B808275
  · exact B808279
  · exact B808283
  · exact B808287
  · exact B808291
  · exact B808295
  · exact B808299
  · exact B808303
  · exact B808307
  · exact B808311
  · exact B808315
  · exact B808319
  · exact B808323
  · exact B808327
  · exact B808331
  · exact B808335
  · exact B808339
  · exact B808343
  · exact B808347
  · exact B808351
  · exact B808355
  · exact B808359
  · exact B808363
  · exact B808367
  · exact B808371
  · exact B808375
  · exact B808379
  · exact B808383
  · exact B808387
  · exact B808391
  · exact B808395
  · exact B808399
  · exact B808403
  · exact B808407
  · exact B808411
  · exact B808415
  · exact B808419
  · exact B808423
  · exact B808427
  · exact B808431
  · exact B808435
  · exact B808439
  · exact B808443
  · exact B808447
  · exact B808451
  · exact B808455
  · exact B808459
  · exact B808463
  · exact B808467
  · exact B808471
  · exact B808475
  · exact B808479
  · exact B808483
  · exact B808487
  · exact B808491
  · exact B808495
  · exact B808499
  · exact B808503
  · exact B808507
  · exact B808511
  · exact B808515
  · exact B808519
  · exact B808523
  · exact B808527
  · exact B808531
  · exact B808535
  · exact B808539
  · exact B808543
  · exact B808547
  · exact B808551
  · exact B808555
  · exact B808559
  · exact B808563
  · exact B808567
  · exact B808571
  · exact B808575
  · exact B808579
  · exact B808583
  · exact B808587
  · exact B808591
  · exact B808595
  · exact B808599
  · exact B808603
  · exact B808607
  · exact B808611
  · exact B808615
  · exact B808619
  · exact B808623
  · exact B808627
  · exact B808631
  · exact B808635
  · exact B808639
  · exact B808643
  · exact B808647
  · exact B808651
  · exact B808655
  · exact B808659
  · exact B808663
  · exact B808667
  · exact B808671
  · exact B808675
  · exact B808679
  · exact B808683
  · exact B808687
  · exact B808691
  · exact B808695
  · exact B808699
  · exact B808703
  · exact B808707
  · exact B808711
  · exact B808715
  · exact B808719
  · exact B808723
  · exact B808727
  · exact B808731
  · exact B808735
  · exact B808739
  · exact B808743
  · exact B808747
  · exact B808751
  · exact B808755
  · exact B808759
  · exact B808763
  · exact B808767
  · exact B808771
  · exact B808775
  · exact B808779
  · exact B808783
  · exact B808787
  · exact B808791
  · exact B808795
  · exact B808799
  · exact B808803
  · exact B808807
  · exact B808811
  · exact B808815
  · exact B808819
  · exact B808823
  · exact B808827
  · exact B808831
  · exact B808835
  · exact B808839
  · exact B808843
  · exact B808847
  · exact B808851
  · exact B808855
  · exact B808859
  · exact B808863
  · exact B808867
  · exact B808871
  · exact B808875
  · exact B808879
  · exact B808883
  · exact B808887
  · exact B808891
  · exact B808895
  · exact B808899
  · exact B808903
  · exact B808907
  · exact B808911
  · exact B808915
  · exact B808919
  · exact B808923
  · exact B808927
  · exact B808931
  · exact B808935
  · exact B808939
  · exact B808943
  · exact B808947
  · exact B808951
  · exact B808955
  · exact B808959
  · exact B808963
  · exact B808967
  · exact B808971
  · exact B808975
  · exact B808979
  · exact B808983
  · exact B808987
  · exact B808991
  · exact B808995
  · exact B808999
  · exact B809003
  · exact B809007
  · exact B809011
  · exact B809015
  · exact B809019
  · exact B809023
  · exact B809027
  · exact B809031
  · exact B809035
  · exact B809039
  · exact B809043
  · exact B809047
  · exact B809051
  · exact B809055
  · exact B809059
  · exact B809063
  · exact B809067
  · exact B809071
  · exact B809075
  · exact B809079
  · exact B809083
  · exact B809087
  · exact B809091
  · exact B809095
  · exact B809099
  · exact B809103
  · exact B809107
  · exact B809111
  · exact B809115
  · exact B809119
  · exact B809123
  · exact B809127
  · exact B809131
  · exact B809135
  · exact B809139
  · exact B809143

theorem C1 (j : ℕ) (h1 : 202286 ≤ j) (h2 : j ≤ 202585) : Blo 806344 (4 * j + 3) := by
  interval_cases j
  · exact B809147
  · exact B809151
  · exact B809155
  · exact B809159
  · exact B809163
  · exact B809167
  · exact B809171
  · exact B809175
  · exact B809179
  · exact B809183
  · exact B809187
  · exact B809191
  · exact B809195
  · exact B809199
  · exact B809203
  · exact B809207
  · exact B809211
  · exact B809215
  · exact B809219
  · exact B809223
  · exact B809227
  · exact B809231
  · exact B809235
  · exact B809239
  · exact B809243
  · exact B809247
  · exact B809251
  · exact B809255
  · exact B809259
  · exact B809263
  · exact B809267
  · exact B809271
  · exact B809275
  · exact B809279
  · exact B809283
  · exact B809287
  · exact B809291
  · exact B809295
  · exact B809299
  · exact B809303
  · exact B809307
  · exact B809311
  · exact B809315
  · exact B809319
  · exact B809323
  · exact B809327
  · exact B809331
  · exact B809335
  · exact B809339
  · exact B809343
  · exact B809347
  · exact B809351
  · exact B809355
  · exact B809359
  · exact B809363
  · exact B809367
  · exact B809371
  · exact B809375
  · exact B809379
  · exact B809383
  · exact B809387
  · exact B809391
  · exact B809395
  · exact B809399
  · exact B809403
  · exact B809407
  · exact B809411
  · exact B809415
  · exact B809419
  · exact B809423
  · exact B809427
  · exact B809431
  · exact B809435
  · exact B809439
  · exact B809443
  · exact B809447
  · exact B809451
  · exact B809455
  · exact B809459
  · exact B809463
  · exact B809467
  · exact B809471
  · exact B809475
  · exact B809479
  · exact B809483
  · exact B809487
  · exact B809491
  · exact B809495
  · exact B809499
  · exact B809503
  · exact B809507
  · exact B809511
  · exact B809515
  · exact B809519
  · exact B809523
  · exact B809527
  · exact B809531
  · exact B809535
  · exact B809539
  · exact B809543
  · exact B809547
  · exact B809551
  · exact B809555
  · exact B809559
  · exact B809563
  · exact B809567
  · exact B809571
  · exact B809575
  · exact B809579
  · exact B809583
  · exact B809587
  · exact B809591
  · exact B809595
  · exact B809599
  · exact B809603
  · exact B809607
  · exact B809611
  · exact B809615
  · exact B809619
  · exact B809623
  · exact B809627
  · exact B809631
  · exact B809635
  · exact B809639
  · exact B809643
  · exact B809647
  · exact B809651
  · exact B809655
  · exact B809659
  · exact B809663
  · exact B809667
  · exact B809671
  · exact B809675
  · exact B809679
  · exact B809683
  · exact B809687
  · exact B809691
  · exact B809695
  · exact B809699
  · exact B809703
  · exact B809707
  · exact B809711
  · exact B809715
  · exact B809719
  · exact B809723
  · exact B809727
  · exact B809731
  · exact B809735
  · exact B809739
  · exact B809743
  · exact B809747
  · exact B809751
  · exact B809755
  · exact B809759
  · exact B809763
  · exact B809767
  · exact B809771
  · exact B809775
  · exact B809779
  · exact B809783
  · exact B809787
  · exact B809791
  · exact B809795
  · exact B809799
  · exact B809803
  · exact B809807
  · exact B809811
  · exact B809815
  · exact B809819
  · exact B809823
  · exact B809827
  · exact B809831
  · exact B809835
  · exact B809839
  · exact B809843
  · exact B809847
  · exact B809851
  · exact B809855
  · exact B809859
  · exact B809863
  · exact B809867
  · exact B809871
  · exact B809875
  · exact B809879
  · exact B809883
  · exact B809887
  · exact B809891
  · exact B809895
  · exact B809899
  · exact B809903
  · exact B809907
  · exact B809911
  · exact B809915
  · exact B809919
  · exact B809923
  · exact B809927
  · exact B809931
  · exact B809935
  · exact B809939
  · exact B809943
  · exact B809947
  · exact B809951
  · exact B809955
  · exact B809959
  · exact B809963
  · exact B809967
  · exact B809971
  · exact B809975
  · exact B809979
  · exact B809983
  · exact B809987
  · exact B809991
  · exact B809995
  · exact B809999
  · exact B810003
  · exact B810007
  · exact B810011
  · exact B810015
  · exact B810019
  · exact B810023
  · exact B810027
  · exact B810031
  · exact B810035
  · exact B810039
  · exact B810043
  · exact B810047
  · exact B810051
  · exact B810055
  · exact B810059
  · exact B810063
  · exact B810067
  · exact B810071
  · exact B810075
  · exact B810079
  · exact B810083
  · exact B810087
  · exact B810091
  · exact B810095
  · exact B810099
  · exact B810103
  · exact B810107
  · exact B810111
  · exact B810115
  · exact B810119
  · exact B810123
  · exact B810127
  · exact B810131
  · exact B810135
  · exact B810139
  · exact B810143
  · exact B810147
  · exact B810151
  · exact B810155
  · exact B810159
  · exact B810163
  · exact B810167
  · exact B810171
  · exact B810175
  · exact B810179
  · exact B810183
  · exact B810187
  · exact B810191
  · exact B810195
  · exact B810199
  · exact B810203
  · exact B810207
  · exact B810211
  · exact B810215
  · exact B810219
  · exact B810223
  · exact B810227
  · exact B810231
  · exact B810235
  · exact B810239
  · exact B810243
  · exact B810247
  · exact B810251
  · exact B810255
  · exact B810259
  · exact B810263
  · exact B810267
  · exact B810271
  · exact B810275
  · exact B810279
  · exact B810283
  · exact B810287
  · exact B810291
  · exact B810295
  · exact B810299
  · exact B810303
  · exact B810307
  · exact B810311
  · exact B810315
  · exact B810319
  · exact B810323
  · exact B810327
  · exact B810331
  · exact B810335
  · exact B810339
  · exact B810343

theorem solution (m : ℕ) (hlo : 806344 ≤ m) (hhi : m ≤ 810344) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 201586 ≤ j := by omega
    have hj2 : j ≤ 202585 := by omega
    have hb : Blo 806344 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 202286 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
