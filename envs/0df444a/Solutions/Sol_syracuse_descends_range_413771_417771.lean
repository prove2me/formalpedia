-- Prove2me | solution 1 for syracuse_descends_range_413771_417771
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:51.187413+00:00
-- url     : https://prove2.me/submissions/9c5eb668-b51b-4b41-9d8e-952178837fc0

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


theorem B622613 : Blo 413771 622613 := bbase (se 6 (by rfl) ⟨14592, by rfl⟩ : syracuseStep 622613 = 29185) (by norm_num)
theorem B524333 : Blo 413771 524333 := bbase (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) (by norm_num)
theorem B622637 : Blo 413771 622637 := bbase (se 3 (by rfl) ⟨116744, by rfl⟩ : syracuseStep 622637 = 233489) (by norm_num)
theorem B786485 : Blo 413771 786485 := bbase (se 5 (by rfl) ⟨36866, by rfl⟩ : syracuseStep 786485 = 73733) (by norm_num)
theorem B622661 : Blo 413771 622661 := bbase (se 4 (by rfl) ⟨58374, by rfl⟩ : syracuseStep 622661 = 116749) (by norm_num)
theorem B622685 : Blo 413771 622685 := bbase (se 3 (by rfl) ⟨116753, by rfl⟩ : syracuseStep 622685 = 233507) (by norm_num)
theorem B524389 : Blo 413771 524389 := bbase (se 4 (by rfl) ⟨49161, by rfl⟩ : syracuseStep 524389 = 98323) (by norm_num)
theorem B622709 : Blo 413771 622709 := bbase (se 5 (by rfl) ⟨29189, by rfl⟩ : syracuseStep 622709 = 58379) (by norm_num)
theorem B622733 : Blo 413771 622733 := bbase (se 3 (by rfl) ⟨116762, by rfl⟩ : syracuseStep 622733 = 233525) (by norm_num)
theorem B3145877 : Blo 413771 3145877 := bbase (se 6 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 3145877 = 147463) (by norm_num)
theorem B622757 : Blo 413771 622757 := bbase (se 4 (by rfl) ⟨58383, by rfl⟩ : syracuseStep 622757 = 116767) (by norm_num)
theorem B622781 : Blo 413771 622781 := bbase (se 3 (by rfl) ⟨116771, by rfl⟩ : syracuseStep 622781 = 233543) (by norm_num)
theorem B524485 : Blo 413771 524485 := bbase (se 4 (by rfl) ⟨49170, by rfl⟩ : syracuseStep 524485 = 98341) (by norm_num)
theorem B622805 : Blo 413771 622805 := bbase (se 7 (by rfl) ⟨7298, by rfl⟩ : syracuseStep 622805 = 14597) (by norm_num)
theorem B1409237 : Blo 413771 1409237 := bbase (se 7 (by rfl) ⟨16514, by rfl⟩ : syracuseStep 1409237 = 33029) (by norm_num)
theorem B622829 : Blo 413771 622829 := bbase (se 3 (by rfl) ⟨116780, by rfl⟩ : syracuseStep 622829 = 233561) (by norm_num)
theorem B2097413 : Blo 413771 2097413 := bbase (se 4 (by rfl) ⟨196632, by rfl⟩ : syracuseStep 2097413 = 393265) (by norm_num)
theorem B622853 : Blo 413771 622853 := bbase (se 4 (by rfl) ⟨58392, by rfl⟩ : syracuseStep 622853 = 116785) (by norm_num)
theorem B622877 : Blo 413771 622877 := bbase (se 3 (by rfl) ⟨116789, by rfl⟩ : syracuseStep 622877 = 233579) (by norm_num)
theorem B622901 : Blo 413771 622901 := bbase (se 5 (by rfl) ⟨29198, by rfl⟩ : syracuseStep 622901 = 58397) (by norm_num)
theorem B1048909 : Blo 413771 1048909 := bbase (se 3 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 1048909 = 393341) (by norm_num)
theorem B622925 : Blo 413771 622925 := bbase (se 3 (by rfl) ⟨116798, by rfl⟩ : syracuseStep 622925 = 233597) (by norm_num)
theorem B2359637 : Blo 413771 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B786773 : Blo 413771 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B622949 : Blo 413771 622949 := bbase (se 4 (by rfl) ⟨58401, by rfl⟩ : syracuseStep 622949 = 116803) (by norm_num)
theorem B524657 : Blo 413771 524657 := bbase (se 2 (by rfl) ⟨196746, by rfl⟩ : syracuseStep 524657 = 393493) (by norm_num)
theorem B622973 : Blo 413771 622973 := bbase (se 3 (by rfl) ⟨116807, by rfl⟩ : syracuseStep 622973 = 233615) (by norm_num)
theorem B622997 : Blo 413771 622997 := bbase (se 6 (by rfl) ⟨14601, by rfl⟩ : syracuseStep 622997 = 29203) (by norm_num)
theorem B524713 : Blo 413771 524713 := bbase (se 2 (by rfl) ⟨196767, by rfl⟩ : syracuseStep 524713 = 393535) (by norm_num)
theorem B623021 : Blo 413771 623021 := bbase (se 3 (by rfl) ⟨116816, by rfl⟩ : syracuseStep 623021 = 233633) (by norm_num)
theorem B1049021 : Blo 413771 1049021 := bbase (se 3 (by rfl) ⟨196691, by rfl⟩ : syracuseStep 1049021 = 393383) (by norm_num)
theorem B885181 : Blo 413771 885181 := bbase (se 3 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 885181 = 331943) (by norm_num)
theorem B623045 : Blo 413771 623045 := bbase (se 4 (by rfl) ⟨58410, by rfl⟩ : syracuseStep 623045 = 116821) (by norm_num)
theorem B590285 : Blo 413771 590285 := bbase (se 3 (by rfl) ⟨110678, by rfl⟩ : syracuseStep 590285 = 221357) (by norm_num)
theorem B623069 : Blo 413771 623069 := bbase (se 3 (by rfl) ⟨116825, by rfl⟩ : syracuseStep 623069 = 233651) (by norm_num)
theorem B786925 : Blo 413771 786925 := bbase (se 3 (by rfl) ⟨147548, by rfl⟩ : syracuseStep 786925 = 295097) (by norm_num)
theorem B623093 : Blo 413771 623093 := bbase (se 5 (by rfl) ⟨29207, by rfl⟩ : syracuseStep 623093 = 58415) (by norm_num)
theorem B524809 : Blo 413771 524809 := bbase (se 2 (by rfl) ⟨196803, by rfl⟩ : syracuseStep 524809 = 393607) (by norm_num)
theorem B623117 : Blo 413771 623117 := bbase (se 3 (by rfl) ⟨116834, by rfl⟩ : syracuseStep 623117 = 233669) (by norm_num)
theorem B590365 : Blo 413771 590365 := bbase (se 3 (by rfl) ⟨110693, by rfl⟩ : syracuseStep 590365 = 221387) (by norm_num)
theorem B623141 : Blo 413771 623141 := bbase (se 4 (by rfl) ⟨58419, by rfl⟩ : syracuseStep 623141 = 116839) (by norm_num)
theorem B623165 : Blo 413771 623165 := bbase (se 3 (by rfl) ⟨116843, by rfl⟩ : syracuseStep 623165 = 233687) (by norm_num)
theorem B885325 : Blo 413771 885325 := bbase (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) (by norm_num)
theorem B623189 : Blo 413771 623189 := bbase (se 8 (by rfl) ⟨3651, by rfl⟩ : syracuseStep 623189 = 7303) (by norm_num)
theorem B623213 : Blo 413771 623213 := bbase (se 3 (by rfl) ⟨116852, by rfl⟩ : syracuseStep 623213 = 233705) (by norm_num)
theorem B1049213 : Blo 413771 1049213 := bbase (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) (by norm_num)
theorem B623237 : Blo 413771 623237 := bbase (se 4 (by rfl) ⟨58428, by rfl⟩ : syracuseStep 623237 = 116857) (by norm_num)
theorem B1409669 : Blo 413771 1409669 := bbase (se 4 (by rfl) ⟨132156, by rfl⟩ : syracuseStep 1409669 = 264313) (by norm_num)
theorem B590485 : Blo 413771 590485 := bbase (se 6 (by rfl) ⟨13839, by rfl⟩ : syracuseStep 590485 = 27679) (by norm_num)
theorem B623261 : Blo 413771 623261 := bbase (se 3 (by rfl) ⟨116861, by rfl⟩ : syracuseStep 623261 = 233723) (by norm_num)
theorem B524981 : Blo 413771 524981 := bbase (se 5 (by rfl) ⟨24608, by rfl⟩ : syracuseStep 524981 = 49217) (by norm_num)
theorem B623285 : Blo 413771 623285 := bbase (se 5 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 623285 = 58433) (by norm_num)
theorem B623309 : Blo 413771 623309 := bbase (se 3 (by rfl) ⟨116870, by rfl⟩ : syracuseStep 623309 = 233741) (by norm_num)
theorem B623333 : Blo 413771 623333 := bbase (se 4 (by rfl) ⟨58437, by rfl⟩ : syracuseStep 623333 = 116875) (by norm_num)
theorem B525037 : Blo 413771 525037 := bbase (se 3 (by rfl) ⟨98444, by rfl⟩ : syracuseStep 525037 = 196889) (by norm_num)
theorem B590581 : Blo 413771 590581 := bbase (se 5 (by rfl) ⟨27683, by rfl⟩ : syracuseStep 590581 = 55367) (by norm_num)
theorem B623357 : Blo 413771 623357 := bbase (se 3 (by rfl) ⟨116879, by rfl⟩ : syracuseStep 623357 = 233759) (by norm_num)
theorem B623381 : Blo 413771 623381 := bbase (se 6 (by rfl) ⟨14610, by rfl⟩ : syracuseStep 623381 = 29221) (by norm_num)
theorem B787229 : Blo 413771 787229 := bbase (se 3 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 787229 = 295211) (by norm_num)
theorem B623405 : Blo 413771 623405 := bbase (se 3 (by rfl) ⟨116888, by rfl⟩ : syracuseStep 623405 = 233777) (by norm_num)
theorem B623429 : Blo 413771 623429 := bbase (se 4 (by rfl) ⟨58446, by rfl⟩ : syracuseStep 623429 = 116893) (by norm_num)
theorem B525133 : Blo 413771 525133 := bbase (se 3 (by rfl) ⟨98462, by rfl⟩ : syracuseStep 525133 = 196925) (by norm_num)
theorem B623453 : Blo 413771 623453 := bbase (se 3 (by rfl) ⟨116897, by rfl⟩ : syracuseStep 623453 = 233795) (by norm_num)
theorem B623477 : Blo 413771 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B623501 : Blo 413771 623501 := bbase (se 3 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 623501 = 233813) (by norm_num)
theorem B623525 : Blo 413771 623525 := bbase (se 4 (by rfl) ⟨58455, by rfl⟩ : syracuseStep 623525 = 116911) (by norm_num)
theorem B623549 : Blo 413771 623549 := bbase (se 3 (by rfl) ⟨116915, by rfl⟩ : syracuseStep 623549 = 233831) (by norm_num)
theorem B885701 : Blo 413771 885701 := bbase (se 4 (by rfl) ⟨83034, by rfl⟩ : syracuseStep 885701 = 166069) (by norm_num)
theorem B1049557 : Blo 413771 1049557 := bbase (se 7 (by rfl) ⟨12299, by rfl⟩ : syracuseStep 1049557 = 24599) (by norm_num)
theorem B623573 : Blo 413771 623573 := bbase (se 7 (by rfl) ⟨7307, by rfl⟩ : syracuseStep 623573 = 14615) (by norm_num)
theorem B623597 : Blo 413771 623597 := bbase (se 3 (by rfl) ⟨116924, by rfl⟩ : syracuseStep 623597 = 233849) (by norm_num)
theorem B525305 : Blo 413771 525305 := bbase (se 2 (by rfl) ⟨196989, by rfl⟩ : syracuseStep 525305 = 393979) (by norm_num)
theorem B623621 : Blo 413771 623621 := bbase (se 4 (by rfl) ⟨58464, by rfl⟩ : syracuseStep 623621 = 116929) (by norm_num)
theorem B623645 : Blo 413771 623645 := bbase (se 3 (by rfl) ⟨116933, by rfl⟩ : syracuseStep 623645 = 233867) (by norm_num)
theorem B525361 : Blo 413771 525361 := bbase (se 2 (by rfl) ⟨197010, by rfl⟩ : syracuseStep 525361 = 394021) (by norm_num)
theorem B623669 : Blo 413771 623669 := bbase (se 5 (by rfl) ⟨29234, by rfl⟩ : syracuseStep 623669 = 58469) (by norm_num)
theorem B1049669 : Blo 413771 1049669 := bbase (se 4 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 1049669 = 196813) (by norm_num)
theorem B623693 : Blo 413771 623693 := bbase (se 3 (by rfl) ⟨116942, by rfl⟩ : syracuseStep 623693 = 233885) (by norm_num)
theorem B623717 : Blo 413771 623717 := bbase (se 4 (by rfl) ⟨58473, by rfl⟩ : syracuseStep 623717 = 116947) (by norm_num)
theorem B623741 : Blo 413771 623741 := bbase (se 3 (by rfl) ⟨116951, by rfl⟩ : syracuseStep 623741 = 233903) (by norm_num)
theorem B525457 : Blo 413771 525457 := bbase (se 2 (by rfl) ⟨197046, by rfl⟩ : syracuseStep 525457 = 394093) (by norm_num)
theorem B623765 : Blo 413771 623765 := bbase (se 6 (by rfl) ⟨14619, by rfl⟩ : syracuseStep 623765 = 29239) (by norm_num)
theorem B623789 : Blo 413771 623789 := bbase (se 3 (by rfl) ⟨116960, by rfl⟩ : syracuseStep 623789 = 233921) (by norm_num)
theorem B2655413 : Blo 413771 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B623813 : Blo 413771 623813 := bbase (se 4 (by rfl) ⟨58482, by rfl⟩ : syracuseStep 623813 = 116965) (by norm_num)
theorem B623837 : Blo 413771 623837 := bbase (se 3 (by rfl) ⟨116969, by rfl⟩ : syracuseStep 623837 = 233939) (by norm_num)
theorem B591077 : Blo 413771 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B623861 : Blo 413771 623861 := bbase (se 5 (by rfl) ⟨29243, by rfl⟩ : syracuseStep 623861 = 58487) (by norm_num)
theorem B1049861 : Blo 413771 1049861 := bbase (se 4 (by rfl) ⟨98424, by rfl⟩ : syracuseStep 1049861 = 196849) (by norm_num)
theorem B623885 : Blo 413771 623885 := bbase (se 3 (by rfl) ⟨116978, by rfl⟩ : syracuseStep 623885 = 233957) (by norm_num)
theorem B2983189 : Blo 413771 2983189 := bbase (se 6 (by rfl) ⟨69918, by rfl⟩ : syracuseStep 2983189 = 139837) (by norm_num)
theorem B1803541 : Blo 413771 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B623909 : Blo 413771 623909 := bbase (se 4 (by rfl) ⟨58491, by rfl⟩ : syracuseStep 623909 = 116983) (by norm_num)
theorem B886069 : Blo 413771 886069 := bbase (se 5 (by rfl) ⟨41534, by rfl⟩ : syracuseStep 886069 = 83069) (by norm_num)
theorem B525629 : Blo 413771 525629 := bbase (se 3 (by rfl) ⟨98555, by rfl⟩ : syracuseStep 525629 = 197111) (by norm_num)
theorem B623933 : Blo 413771 623933 := bbase (se 3 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 623933 = 233975) (by norm_num)
theorem B623957 : Blo 413771 623957 := bbase (se 12 (by rfl) ⟨228, by rfl⟩ : syracuseStep 623957 = 457) (by norm_num)
theorem B623981 : Blo 413771 623981 := bbase (se 3 (by rfl) ⟨116996, by rfl⟩ : syracuseStep 623981 = 233993) (by norm_num)
theorem B1574261 : Blo 413771 1574261 := bbase (se 5 (by rfl) ⟨73793, by rfl⟩ : syracuseStep 1574261 = 147587) (by norm_num)
theorem B525685 : Blo 413771 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B624005 : Blo 413771 624005 := bbase (se 4 (by rfl) ⟨58500, by rfl⟩ : syracuseStep 624005 = 117001) (by norm_num)
theorem B624029 : Blo 413771 624029 := bbase (se 3 (by rfl) ⟨117005, by rfl⟩ : syracuseStep 624029 = 234011) (by norm_num)
theorem B624053 : Blo 413771 624053 := bbase (se 5 (by rfl) ⟨29252, by rfl⟩ : syracuseStep 624053 = 58505) (by norm_num)
theorem B624077 : Blo 413771 624077 := bbase (se 3 (by rfl) ⟨117014, by rfl⟩ : syracuseStep 624077 = 234029) (by norm_num)
theorem B525781 : Blo 413771 525781 := bbase (se 7 (by rfl) ⟨6161, by rfl⟩ : syracuseStep 525781 = 12323) (by norm_num)
theorem B1705445 : Blo 413771 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B624101 : Blo 413771 624101 := bbase (se 4 (by rfl) ⟨58509, by rfl⟩ : syracuseStep 624101 = 117019) (by norm_num)
theorem B624125 : Blo 413771 624125 := bbase (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) (by norm_num)
theorem B787981 : Blo 413771 787981 := bbase (se 3 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 787981 = 295493) (by norm_num)
theorem B2098709 : Blo 413771 2098709 := bbase (se 6 (by rfl) ⟨49188, by rfl⟩ : syracuseStep 2098709 = 98377) (by norm_num)
theorem B624149 : Blo 413771 624149 := bbase (se 6 (by rfl) ⟨14628, by rfl⟩ : syracuseStep 624149 = 29257) (by norm_num)
theorem B2033189 : Blo 413771 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B624173 : Blo 413771 624173 := bbase (se 3 (by rfl) ⟨117032, by rfl⟩ : syracuseStep 624173 = 234065) (by norm_num)
theorem B624197 : Blo 413771 624197 := bbase (se 4 (by rfl) ⟨58518, by rfl⟩ : syracuseStep 624197 = 117037) (by norm_num)
theorem B1050205 : Blo 413771 1050205 := bbase (se 3 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 1050205 = 393827) (by norm_num)
theorem B624221 : Blo 413771 624221 := bbase (se 3 (by rfl) ⟨117041, by rfl⟩ : syracuseStep 624221 = 234083) (by norm_num)
theorem B624245 : Blo 413771 624245 := bbase (se 5 (by rfl) ⟨29261, by rfl⟩ : syracuseStep 624245 = 58523) (by norm_num)
theorem B525953 : Blo 413771 525953 := bbase (se 2 (by rfl) ⟨197232, by rfl⟩ : syracuseStep 525953 = 394465) (by norm_num)
theorem B624269 : Blo 413771 624269 := bbase (se 3 (by rfl) ⟨117050, by rfl⟩ : syracuseStep 624269 = 234101) (by norm_num)
theorem B1574549 : Blo 413771 1574549 := bbase (se 6 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 1574549 = 73807) (by norm_num)
theorem B788125 : Blo 413771 788125 := bbase (se 3 (by rfl) ⟨147773, by rfl⟩ : syracuseStep 788125 = 295547) (by norm_num)
theorem B624293 : Blo 413771 624293 := bbase (se 4 (by rfl) ⟨58527, by rfl⟩ : syracuseStep 624293 = 117055) (by norm_num)
theorem B526009 : Blo 413771 526009 := bbase (se 2 (by rfl) ⟨197253, by rfl⟩ : syracuseStep 526009 = 394507) (by norm_num)
theorem B624317 : Blo 413771 624317 := bbase (se 3 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 624317 = 234119) (by norm_num)
theorem B1050317 : Blo 413771 1050317 := bbase (se 3 (by rfl) ⟨196934, by rfl⟩ : syracuseStep 1050317 = 393869) (by norm_num)
theorem B624341 : Blo 413771 624341 := bbase (se 7 (by rfl) ⟨7316, by rfl⟩ : syracuseStep 624341 = 14633) (by norm_num)
theorem B624365 : Blo 413771 624365 := bbase (se 3 (by rfl) ⟨117068, by rfl⟩ : syracuseStep 624365 = 234137) (by norm_num)
theorem B624389 : Blo 413771 624389 := bbase (se 4 (by rfl) ⟨58536, by rfl⟩ : syracuseStep 624389 = 117073) (by norm_num)
theorem B591629 : Blo 413771 591629 := bbase (se 3 (by rfl) ⟨110930, by rfl⟩ : syracuseStep 591629 = 221861) (by norm_num)
theorem B526105 : Blo 413771 526105 := bbase (se 2 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 526105 = 394579) (by norm_num)
theorem B624413 : Blo 413771 624413 := bbase (se 3 (by rfl) ⟨117077, by rfl⟩ : syracuseStep 624413 = 234155) (by norm_num)
theorem B624437 : Blo 413771 624437 := bbase (se 5 (by rfl) ⟨29270, by rfl⟩ : syracuseStep 624437 = 58541) (by norm_num)
theorem B788285 : Blo 413771 788285 := bbase (se 3 (by rfl) ⟨147803, by rfl⟩ : syracuseStep 788285 = 295607) (by norm_num)
theorem B624461 : Blo 413771 624461 := bbase (se 3 (by rfl) ⟨117086, by rfl⟩ : syracuseStep 624461 = 234173) (by norm_num)
theorem B624485 : Blo 413771 624485 := bbase (se 4 (by rfl) ⟨58545, by rfl⟩ : syracuseStep 624485 = 117091) (by norm_num)
theorem B624509 : Blo 413771 624509 := bbase (se 3 (by rfl) ⟨117095, by rfl⟩ : syracuseStep 624509 = 234191) (by norm_num)
theorem B1181573 : Blo 413771 1181573 := bbase (se 4 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 1181573 = 221545) (by norm_num)
theorem B1050509 : Blo 413771 1050509 := bbase (se 3 (by rfl) ⟨196970, by rfl⟩ : syracuseStep 1050509 = 393941) (by norm_num)
theorem B624533 : Blo 413771 624533 := bbase (se 6 (by rfl) ⟨14637, by rfl⟩ : syracuseStep 624533 = 29275) (by norm_num)
theorem B624557 : Blo 413771 624557 := bbase (se 3 (by rfl) ⟨117104, by rfl⟩ : syracuseStep 624557 = 234209) (by norm_num)
theorem B526277 : Blo 413771 526277 := bbase (se 4 (by rfl) ⟨49338, by rfl⟩ : syracuseStep 526277 = 98677) (by norm_num)
theorem B624581 : Blo 413771 624581 := bbase (se 4 (by rfl) ⟨58554, by rfl⟩ : syracuseStep 624581 = 117109) (by norm_num)
theorem B788429 : Blo 413771 788429 := bbase (se 3 (by rfl) ⟨147830, by rfl⟩ : syracuseStep 788429 = 295661) (by norm_num)
theorem B624605 : Blo 413771 624605 := bbase (se 3 (by rfl) ⟨117113, by rfl⟩ : syracuseStep 624605 = 234227) (by norm_num)
theorem B624629 : Blo 413771 624629 := bbase (se 5 (by rfl) ⟨29279, by rfl⟩ : syracuseStep 624629 = 58559) (by norm_num)
theorem B526333 : Blo 413771 526333 := bbase (se 3 (by rfl) ⟨98687, by rfl⟩ : syracuseStep 526333 = 197375) (by norm_num)
theorem B624653 : Blo 413771 624653 := bbase (se 3 (by rfl) ⟨117122, by rfl⟩ : syracuseStep 624653 = 234245) (by norm_num)
theorem B3377173 : Blo 413771 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B624677 : Blo 413771 624677 := bbase (se 4 (by rfl) ⟨58563, by rfl⟩ : syracuseStep 624677 = 117127) (by norm_num)
theorem B624701 : Blo 413771 624701 := bbase (se 3 (by rfl) ⟨117131, by rfl⟩ : syracuseStep 624701 = 234263) (by norm_num)
theorem B624725 : Blo 413771 624725 := bbase (se 8 (by rfl) ⟨3660, by rfl⟩ : syracuseStep 624725 = 7321) (by norm_num)
theorem B526429 : Blo 413771 526429 := bbase (se 3 (by rfl) ⟨98705, by rfl⟩ : syracuseStep 526429 = 197411) (by norm_num)
theorem B624749 : Blo 413771 624749 := bbase (se 3 (by rfl) ⟨117140, by rfl⟩ : syracuseStep 624749 = 234281) (by norm_num)
theorem B624773 : Blo 413771 624773 := bbase (se 4 (by rfl) ⟨58572, by rfl⟩ : syracuseStep 624773 = 117145) (by norm_num)
theorem B624797 : Blo 413771 624797 := bbase (se 3 (by rfl) ⟨117149, by rfl⟩ : syracuseStep 624797 = 234299) (by norm_num)
theorem B624821 : Blo 413771 624821 := bbase (se 5 (by rfl) ⟨29288, by rfl⟩ : syracuseStep 624821 = 58577) (by norm_num)
theorem B624845 : Blo 413771 624845 := bbase (se 3 (by rfl) ⟨117158, by rfl⟩ : syracuseStep 624845 = 234317) (by norm_num)
theorem B1050853 : Blo 413771 1050853 := bbase (se 4 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 1050853 = 197035) (by norm_num)
theorem B624869 : Blo 413771 624869 := bbase (se 4 (by rfl) ⟨58581, by rfl⟩ : syracuseStep 624869 = 117163) (by norm_num)
theorem B788717 : Blo 413771 788717 := bbase (se 3 (by rfl) ⟨147884, by rfl⟩ : syracuseStep 788717 = 295769) (by norm_num)
theorem B624893 : Blo 413771 624893 := bbase (se 3 (by rfl) ⟨117167, by rfl⟩ : syracuseStep 624893 = 234335) (by norm_num)
theorem B526601 : Blo 413771 526601 := bbase (se 2 (by rfl) ⟨197475, by rfl⟩ : syracuseStep 526601 = 394951) (by norm_num)
theorem B559381 : Blo 413771 559381 := bbase (se 6 (by rfl) ⟨13110, by rfl⟩ : syracuseStep 559381 = 26221) (by norm_num)
theorem B624917 : Blo 413771 624917 := bbase (se 6 (by rfl) ⟨14646, by rfl⟩ : syracuseStep 624917 = 29293) (by norm_num)
theorem B624941 : Blo 413771 624941 := bbase (se 3 (by rfl) ⟨117176, by rfl⟩ : syracuseStep 624941 = 234353) (by norm_num)
theorem B526657 : Blo 413771 526657 := bbase (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) (by norm_num)
theorem B624965 : Blo 413771 624965 := bbase (se 4 (by rfl) ⟨58590, by rfl⟩ : syracuseStep 624965 = 117181) (by norm_num)
theorem B559445 : Blo 413771 559445 := bbase (se 10 (by rfl) ⟨819, by rfl⟩ : syracuseStep 559445 = 1639) (by norm_num)
theorem B1050965 : Blo 413771 1050965 := bbase (se 10 (by rfl) ⟨1539, by rfl⟩ : syracuseStep 1050965 = 3079) (by norm_num)
theorem B624989 : Blo 413771 624989 := bbase (se 3 (by rfl) ⟨117185, by rfl⟩ : syracuseStep 624989 = 234371) (by norm_num)
theorem B625013 : Blo 413771 625013 := bbase (se 5 (by rfl) ⟨29297, by rfl⟩ : syracuseStep 625013 = 58595) (by norm_num)
theorem B788869 : Blo 413771 788869 := bbase (se 4 (by rfl) ⟨73956, by rfl⟩ : syracuseStep 788869 = 147913) (by norm_num)
theorem B625037 : Blo 413771 625037 := bbase (se 3 (by rfl) ⟨117194, by rfl⟩ : syracuseStep 625037 = 234389) (by norm_num)
theorem B526753 : Blo 413771 526753 := bbase (se 2 (by rfl) ⟨197532, by rfl⟩ : syracuseStep 526753 = 395065) (by norm_num)
theorem B625061 : Blo 413771 625061 := bbase (se 4 (by rfl) ⟨58599, by rfl⟩ : syracuseStep 625061 = 117199) (by norm_num)
theorem B625085 : Blo 413771 625085 := bbase (se 3 (by rfl) ⟨117203, by rfl⟩ : syracuseStep 625085 = 234407) (by norm_num)
theorem B625109 : Blo 413771 625109 := bbase (se 7 (by rfl) ⟨7325, by rfl⟩ : syracuseStep 625109 = 14651) (by norm_num)
theorem B625133 : Blo 413771 625133 := bbase (se 3 (by rfl) ⟨117212, by rfl⟩ : syracuseStep 625133 = 234425) (by norm_num)
theorem B592381 : Blo 413771 592381 := bbase (se 3 (by rfl) ⟨111071, by rfl⟩ : syracuseStep 592381 = 222143) (by norm_num)
theorem B625157 : Blo 413771 625157 := bbase (se 4 (by rfl) ⟨58608, by rfl⟩ : syracuseStep 625157 = 117217) (by norm_num)
theorem B1051157 : Blo 413771 1051157 := bbase (se 6 (by rfl) ⟨24636, by rfl⟩ : syracuseStep 1051157 = 49273) (by norm_num)
theorem B625181 : Blo 413771 625181 := bbase (se 3 (by rfl) ⟨117221, by rfl⟩ : syracuseStep 625181 = 234443) (by norm_num)
theorem B625205 : Blo 413771 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B526925 : Blo 413771 526925 := bbase (se 3 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 526925 = 197597) (by norm_num)
theorem B625229 : Blo 413771 625229 := bbase (se 3 (by rfl) ⟨117230, by rfl⟩ : syracuseStep 625229 = 234461) (by norm_num)
theorem B625253 : Blo 413771 625253 := bbase (se 4 (by rfl) ⟨58617, by rfl⟩ : syracuseStep 625253 = 117235) (by norm_num)
theorem B625277 : Blo 413771 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B526981 : Blo 413771 526981 := bbase (se 4 (by rfl) ⟨49404, by rfl⟩ : syracuseStep 526981 = 98809) (by norm_num)
theorem B625301 : Blo 413771 625301 := bbase (se 6 (by rfl) ⟨14655, by rfl⟩ : syracuseStep 625301 = 29311) (by norm_num)
theorem B625325 : Blo 413771 625325 := bbase (se 3 (by rfl) ⟨117248, by rfl⟩ : syracuseStep 625325 = 234497) (by norm_num)
theorem B789173 : Blo 413771 789173 := bbase (se 5 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 789173 = 73985) (by norm_num)
theorem B625349 : Blo 413771 625349 := bbase (se 4 (by rfl) ⟨58626, by rfl⟩ : syracuseStep 625349 = 117253) (by norm_num)
theorem B625373 : Blo 413771 625373 := bbase (se 3 (by rfl) ⟨117257, by rfl⟩ : syracuseStep 625373 = 234515) (by norm_num)
theorem B527077 : Blo 413771 527077 := bbase (se 4 (by rfl) ⟨49413, by rfl⟩ : syracuseStep 527077 = 98827) (by norm_num)
theorem B625397 : Blo 413771 625397 := bbase (se 5 (by rfl) ⟨29315, by rfl⟩ : syracuseStep 625397 = 58631) (by norm_num)
theorem B625421 : Blo 413771 625421 := bbase (se 3 (by rfl) ⟨117266, by rfl⟩ : syracuseStep 625421 = 234533) (by norm_num)
theorem B887573 : Blo 413771 887573 := bbase (se 6 (by rfl) ⟨20802, by rfl⟩ : syracuseStep 887573 = 41605) (by norm_num)
theorem B2100005 : Blo 413771 2100005 := bbase (se 4 (by rfl) ⟨196875, by rfl⟩ : syracuseStep 2100005 = 393751) (by norm_num)
theorem B625445 : Blo 413771 625445 := bbase (se 4 (by rfl) ⟨58635, by rfl⟩ : syracuseStep 625445 = 117271) (by norm_num)
theorem B1575733 : Blo 413771 1575733 := bbase (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) (by norm_num)
theorem B625469 : Blo 413771 625469 := bbase (se 3 (by rfl) ⟨117275, by rfl⟩ : syracuseStep 625469 = 234551) (by norm_num)
theorem B625493 : Blo 413771 625493 := bbase (se 9 (by rfl) ⟨1832, by rfl⟩ : syracuseStep 625493 = 3665) (by norm_num)
theorem B1051501 : Blo 413771 1051501 := bbase (se 3 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 1051501 = 394313) (by norm_num)
theorem B625517 : Blo 413771 625517 := bbase (se 3 (by rfl) ⟨117284, by rfl⟩ : syracuseStep 625517 = 234569) (by norm_num)
theorem B625541 : Blo 413771 625541 := bbase (se 4 (by rfl) ⟨58644, by rfl⟩ : syracuseStep 625541 = 117289) (by norm_num)
theorem B527249 : Blo 413771 527249 := bbase (se 2 (by rfl) ⟨197718, by rfl⟩ : syracuseStep 527249 = 395437) (by norm_num)
theorem B560029 : Blo 413771 560029 := bbase (se 3 (by rfl) ⟨105005, by rfl⟩ : syracuseStep 560029 = 210011) (by norm_num)
theorem B625565 : Blo 413771 625565 := bbase (se 3 (by rfl) ⟨117293, by rfl⟩ : syracuseStep 625565 = 234587) (by norm_num)
theorem B887717 : Blo 413771 887717 := bbase (se 4 (by rfl) ⟨83223, by rfl⟩ : syracuseStep 887717 = 166447) (by norm_num)
theorem B625589 : Blo 413771 625589 := bbase (se 5 (by rfl) ⟨29324, by rfl⟩ : syracuseStep 625589 = 58649) (by norm_num)
theorem B527305 : Blo 413771 527305 := bbase (se 2 (by rfl) ⟨197739, by rfl⟩ : syracuseStep 527305 = 395479) (by norm_num)
theorem B625613 : Blo 413771 625613 := bbase (se 3 (by rfl) ⟨117302, by rfl⟩ : syracuseStep 625613 = 234605) (by norm_num)
theorem B1051613 : Blo 413771 1051613 := bbase (se 3 (by rfl) ⟨197177, by rfl⟩ : syracuseStep 1051613 = 394355) (by norm_num)
theorem B625637 : Blo 413771 625637 := bbase (se 4 (by rfl) ⟨58653, by rfl⟩ : syracuseStep 625637 = 117307) (by norm_num)
theorem B625661 : Blo 413771 625661 := bbase (se 3 (by rfl) ⟨117311, by rfl⟩ : syracuseStep 625661 = 234623) (by norm_num)
theorem B1772549 : Blo 413771 1772549 := bbase (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) (by norm_num)
theorem B625685 : Blo 413771 625685 := bbase (se 6 (by rfl) ⟨14664, by rfl⟩ : syracuseStep 625685 = 29329) (by norm_num)
theorem B1182757 : Blo 413771 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B527401 : Blo 413771 527401 := bbase (se 2 (by rfl) ⟨197775, by rfl⟩ : syracuseStep 527401 = 395551) (by norm_num)
theorem B625709 : Blo 413771 625709 := bbase (se 3 (by rfl) ⟨117320, by rfl⟩ : syracuseStep 625709 = 234641) (by norm_num)
theorem B560197 : Blo 413771 560197 := bbase (se 4 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 560197 = 105037) (by norm_num)
theorem B625733 : Blo 413771 625733 := bbase (se 4 (by rfl) ⟨58662, by rfl⟩ : syracuseStep 625733 = 117325) (by norm_num)
theorem B625757 : Blo 413771 625757 := bbase (se 3 (by rfl) ⟨117329, by rfl⟩ : syracuseStep 625757 = 234659) (by norm_num)
theorem B1576037 : Blo 413771 1576037 := bbase (se 4 (by rfl) ⟨147753, by rfl⟩ : syracuseStep 1576037 = 295507) (by norm_num)
theorem B625781 : Blo 413771 625781 := bbase (se 5 (by rfl) ⟨29333, by rfl⟩ : syracuseStep 625781 = 58667) (by norm_num)
theorem B625805 : Blo 413771 625805 := bbase (se 3 (by rfl) ⟨117338, by rfl⟩ : syracuseStep 625805 = 234677) (by norm_num)
theorem B1051805 : Blo 413771 1051805 := bbase (se 3 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 1051805 = 394427) (by norm_num)
theorem B625829 : Blo 413771 625829 := bbase (se 4 (by rfl) ⟨58671, by rfl⟩ : syracuseStep 625829 = 117343) (by norm_num)
theorem B625853 : Blo 413771 625853 := bbase (se 3 (by rfl) ⟨117347, by rfl⟩ : syracuseStep 625853 = 234695) (by norm_num)
theorem B1182917 : Blo 413771 1182917 := bbase (se 4 (by rfl) ⟨110898, by rfl⟩ : syracuseStep 1182917 = 221797) (by norm_num)
theorem B527573 : Blo 413771 527573 := bbase (se 7 (by rfl) ⟨6182, by rfl⟩ : syracuseStep 527573 = 12365) (by norm_num)
theorem B625877 : Blo 413771 625877 := bbase (se 7 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 625877 = 14669) (by norm_num)
theorem B625901 : Blo 413771 625901 := bbase (se 3 (by rfl) ⟨117356, by rfl⟩ : syracuseStep 625901 = 234713) (by norm_num)
theorem B625925 : Blo 413771 625925 := bbase (se 4 (by rfl) ⟨58680, by rfl⟩ : syracuseStep 625925 = 117361) (by norm_num)
theorem B888077 : Blo 413771 888077 := bbase (se 3 (by rfl) ⟨166514, by rfl⟩ : syracuseStep 888077 = 333029) (by norm_num)
theorem B527629 : Blo 413771 527629 := bbase (se 3 (by rfl) ⟨98930, by rfl⟩ : syracuseStep 527629 = 197861) (by norm_num)
theorem B593173 : Blo 413771 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B625949 : Blo 413771 625949 := bbase (se 3 (by rfl) ⟨117365, by rfl⟩ : syracuseStep 625949 = 234731) (by norm_num)
theorem B1772837 : Blo 413771 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B625973 : Blo 413771 625973 := bbase (se 5 (by rfl) ⟨29342, by rfl⟩ : syracuseStep 625973 = 58685) (by norm_num)
theorem B625997 : Blo 413771 625997 := bbase (se 3 (by rfl) ⟨117374, by rfl⟩ : syracuseStep 625997 = 234749) (by norm_num)
theorem B626021 : Blo 413771 626021 := bbase (se 4 (by rfl) ⟨58689, by rfl⟩ : syracuseStep 626021 = 117379) (by norm_num)
theorem B527725 : Blo 413771 527725 := bbase (se 3 (by rfl) ⟨98948, by rfl⟩ : syracuseStep 527725 = 197897) (by norm_num)
theorem B626045 : Blo 413771 626045 := bbase (se 3 (by rfl) ⟨117383, by rfl⟩ : syracuseStep 626045 = 234767) (by norm_num)
theorem B626069 : Blo 413771 626069 := bbase (se 6 (by rfl) ⟨14673, by rfl⟩ : syracuseStep 626069 = 29347) (by norm_num)
theorem B789925 : Blo 413771 789925 := bbase (se 4 (by rfl) ⟨74055, by rfl⟩ : syracuseStep 789925 = 148111) (by norm_num)
theorem B626093 : Blo 413771 626093 := bbase (se 3 (by rfl) ⟨117392, by rfl⟩ : syracuseStep 626093 = 234785) (by norm_num)
theorem B1183157 : Blo 413771 1183157 := bbase (se 5 (by rfl) ⟨55460, by rfl⟩ : syracuseStep 1183157 = 110921) (by norm_num)
theorem B626117 : Blo 413771 626117 := bbase (se 4 (by rfl) ⟨58698, by rfl⟩ : syracuseStep 626117 = 117397) (by norm_num)
theorem B626141 : Blo 413771 626141 := bbase (se 3 (by rfl) ⟨117401, by rfl⟩ : syracuseStep 626141 = 234803) (by norm_num)
theorem B1052149 : Blo 413771 1052149 := bbase (se 5 (by rfl) ⟨49319, by rfl⟩ : syracuseStep 1052149 = 98639) (by norm_num)
theorem B626165 : Blo 413771 626165 := bbase (se 5 (by rfl) ⟨29351, by rfl⟩ : syracuseStep 626165 = 58703) (by norm_num)
theorem B626189 : Blo 413771 626189 := bbase (se 3 (by rfl) ⟨117410, by rfl⟩ : syracuseStep 626189 = 234821) (by norm_num)
theorem B527897 : Blo 413771 527897 := bbase (se 2 (by rfl) ⟨197961, by rfl⟩ : syracuseStep 527897 = 395923) (by norm_num)
theorem B626213 : Blo 413771 626213 := bbase (se 4 (by rfl) ⟨58707, by rfl⟩ : syracuseStep 626213 = 117415) (by norm_num)
theorem B790069 : Blo 413771 790069 := bbase (se 5 (by rfl) ⟨37034, by rfl⟩ : syracuseStep 790069 = 74069) (by norm_num)
theorem B626237 : Blo 413771 626237 := bbase (se 3 (by rfl) ⟨117419, by rfl⟩ : syracuseStep 626237 = 234839) (by norm_num)
theorem B527953 : Blo 413771 527953 := bbase (se 2 (by rfl) ⟨197982, by rfl⟩ : syracuseStep 527953 = 395965) (by norm_num)
theorem B626261 : Blo 413771 626261 := bbase (se 8 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 626261 = 7339) (by norm_num)
theorem B1052261 : Blo 413771 1052261 := bbase (se 4 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 1052261 = 197299) (by norm_num)
theorem B593509 : Blo 413771 593509 := bbase (se 4 (by rfl) ⟨55641, by rfl⟩ : syracuseStep 593509 = 111283) (by norm_num)
theorem B626285 : Blo 413771 626285 := bbase (se 3 (by rfl) ⟨117428, by rfl⟩ : syracuseStep 626285 = 234857) (by norm_num)
theorem B1183349 : Blo 413771 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B626309 : Blo 413771 626309 := bbase (se 4 (by rfl) ⟨58716, by rfl⟩ : syracuseStep 626309 = 117433) (by norm_num)
theorem B626333 : Blo 413771 626333 := bbase (se 3 (by rfl) ⟨117437, by rfl⟩ : syracuseStep 626333 = 234875) (by norm_num)
theorem B528049 : Blo 413771 528049 := bbase (se 2 (by rfl) ⟨198018, by rfl⟩ : syracuseStep 528049 = 396037) (by norm_num)
theorem B626357 : Blo 413771 626357 := bbase (se 5 (by rfl) ⟨29360, by rfl⟩ : syracuseStep 626357 = 58721) (by norm_num)
theorem B626381 : Blo 413771 626381 := bbase (se 3 (by rfl) ⟨117446, by rfl⟩ : syracuseStep 626381 = 234893) (by norm_num)
theorem B790229 : Blo 413771 790229 := bbase (se 7 (by rfl) ⟨9260, by rfl⟩ : syracuseStep 790229 = 18521) (by norm_num)
theorem B626405 : Blo 413771 626405 := bbase (se 4 (by rfl) ⟨58725, by rfl⟩ : syracuseStep 626405 = 117451) (by norm_num)
theorem B626429 : Blo 413771 626429 := bbase (se 3 (by rfl) ⟨117455, by rfl⟩ : syracuseStep 626429 = 234911) (by norm_num)
theorem B626453 : Blo 413771 626453 := bbase (se 6 (by rfl) ⟨14682, by rfl⟩ : syracuseStep 626453 = 29365) (by norm_num)
theorem B1052453 : Blo 413771 1052453 := bbase (se 4 (by rfl) ⟨98667, by rfl⟩ : syracuseStep 1052453 = 197335) (by norm_num)
theorem B626477 : Blo 413771 626477 := bbase (se 3 (by rfl) ⟨117464, by rfl⟩ : syracuseStep 626477 = 234929) (by norm_num)
theorem B593725 : Blo 413771 593725 := bbase (se 3 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 593725 = 222647) (by norm_num)
theorem B626501 : Blo 413771 626501 := bbase (se 4 (by rfl) ⟨58734, by rfl⟩ : syracuseStep 626501 = 117469) (by norm_num)
theorem B528221 : Blo 413771 528221 := bbase (se 3 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 528221 = 198083) (by norm_num)
theorem B626525 : Blo 413771 626525 := bbase (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) (by norm_num)
theorem B790373 : Blo 413771 790373 := bbase (se 4 (by rfl) ⟨74097, by rfl⟩ : syracuseStep 790373 = 148195) (by norm_num)
theorem B626549 : Blo 413771 626549 := bbase (se 5 (by rfl) ⟨29369, by rfl⟩ : syracuseStep 626549 = 58739) (by norm_num)
theorem B626573 : Blo 413771 626573 := bbase (se 3 (by rfl) ⟨117482, by rfl⟩ : syracuseStep 626573 = 234965) (by norm_num)
theorem B528277 : Blo 413771 528277 := bbase (se 6 (by rfl) ⟨12381, by rfl⟩ : syracuseStep 528277 = 24763) (by norm_num)
theorem B4820885 : Blo 413771 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B626597 : Blo 413771 626597 := bbase (se 4 (by rfl) ⟨58743, by rfl⟩ : syracuseStep 626597 = 117487) (by norm_num)
theorem B626621 : Blo 413771 626621 := bbase (se 3 (by rfl) ⟨117491, by rfl⟩ : syracuseStep 626621 = 234983) (by norm_num)
theorem B626645 : Blo 413771 626645 := bbase (se 7 (by rfl) ⟨7343, by rfl⟩ : syracuseStep 626645 = 14687) (by norm_num)
theorem B528373 : Blo 413771 528373 := bbase (se 5 (by rfl) ⟨24767, by rfl⟩ : syracuseStep 528373 = 49535) (by norm_num)
theorem B1773589 : Blo 413771 1773589 := bbase (se 6 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 1773589 = 83137) (by norm_num)
theorem B2101301 : Blo 413771 2101301 := bbase (se 5 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 2101301 = 196997) (by norm_num)
theorem B1052797 : Blo 413771 1052797 := bbase (se 3 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 1052797 = 394799) (by norm_num)
theorem B888965 : Blo 413771 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B790661 : Blo 413771 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B528545 : Blo 413771 528545 := bbase (se 2 (by rfl) ⟨198204, by rfl⟩ : syracuseStep 528545 = 396409) (by norm_num)
theorem B594101 : Blo 413771 594101 := bbase (se 5 (by rfl) ⟨27848, by rfl⟩ : syracuseStep 594101 = 55697) (by norm_num)
theorem B528601 : Blo 413771 528601 := bbase (se 2 (by rfl) ⟨198225, by rfl⟩ : syracuseStep 528601 = 396451) (by norm_num)
theorem B1052909 : Blo 413771 1052909 := bbase (se 3 (by rfl) ⟨197420, by rfl⟩ : syracuseStep 1052909 = 394841) (by norm_num)
theorem B790813 : Blo 413771 790813 := bbase (se 3 (by rfl) ⟨148277, by rfl⟩ : syracuseStep 790813 = 296555) (by norm_num)
theorem B528697 : Blo 413771 528697 := bbase (se 2 (by rfl) ⟨198261, by rfl⟩ : syracuseStep 528697 = 396523) (by norm_num)
theorem B2003285 : Blo 413771 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B889213 : Blo 413771 889213 := bbase (se 3 (by rfl) ⟨166727, by rfl⟩ : syracuseStep 889213 = 333455) (by norm_num)
theorem B1053101 : Blo 413771 1053101 := bbase (se 3 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 1053101 = 394913) (by norm_num)
theorem B791117 : Blo 413771 791117 := bbase (se 3 (by rfl) ⟨148334, by rfl⟩ : syracuseStep 791117 = 296669) (by norm_num)
theorem B1184341 : Blo 413771 1184341 := bbase (se 8 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 1184341 = 13879) (by norm_num)
theorem B1217173 : Blo 413771 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B3609269 : Blo 413771 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B2003669 : Blo 413771 2003669 := bbase (se 7 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 2003669 = 46961) (by norm_num)
theorem B1774325 : Blo 413771 1774325 := bbase (se 5 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 1774325 = 166343) (by norm_num)
theorem B1053445 : Blo 413771 1053445 := bbase (se 4 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 1053445 = 197521) (by norm_num)
theorem B1053557 : Blo 413771 1053557 := bbase (se 5 (by rfl) ⟨49385, by rfl⟩ : syracuseStep 1053557 = 98771) (by norm_num)
theorem B889717 : Blo 413771 889717 := bbase (se 5 (by rfl) ⟨41705, by rfl⟩ : syracuseStep 889717 = 83411) (by norm_num)
theorem B562213 : Blo 413771 562213 := bbase (se 4 (by rfl) ⟨52707, by rfl⟩ : syracuseStep 562213 = 105415) (by norm_num)
theorem B1053749 : Blo 413771 1053749 := bbase (se 5 (by rfl) ⟨49394, by rfl⟩ : syracuseStep 1053749 = 98789) (by norm_num)
theorem B1578149 : Blo 413771 1578149 := bbase (se 4 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 1578149 = 295903) (by norm_num)
theorem B857357 : Blo 413771 857357 := bbase (se 3 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 857357 = 321509) (by norm_num)
theorem B791869 : Blo 413771 791869 := bbase (se 3 (by rfl) ⟨148475, by rfl⟩ : syracuseStep 791869 = 296951) (by norm_num)
theorem B2102597 : Blo 413771 2102597 := bbase (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) (by norm_num)
theorem B1054093 : Blo 413771 1054093 := bbase (se 3 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 1054093 = 395285) (by norm_num)
theorem B1578437 : Blo 413771 1578437 := bbase (se 4 (by rfl) ⟨147978, by rfl⟩ : syracuseStep 1578437 = 295957) (by norm_num)
theorem B792013 : Blo 413771 792013 := bbase (se 3 (by rfl) ⟨148502, by rfl⟩ : syracuseStep 792013 = 297005) (by norm_num)
theorem B1054205 : Blo 413771 1054205 := bbase (se 3 (by rfl) ⟨197663, by rfl⟩ : syracuseStep 1054205 = 395327) (by norm_num)
theorem B792173 : Blo 413771 792173 := bbase (se 3 (by rfl) ⟨148532, by rfl⟩ : syracuseStep 792173 = 297065) (by norm_num)
theorem B1185445 : Blo 413771 1185445 := bbase (se 4 (by rfl) ⟨111135, by rfl⟩ : syracuseStep 1185445 = 222271) (by norm_num)
theorem B1054397 : Blo 413771 1054397 := bbase (se 3 (by rfl) ⟨197699, by rfl⟩ : syracuseStep 1054397 = 395399) (by norm_num)
theorem B890605 : Blo 413771 890605 := bbase (se 3 (by rfl) ⟨166988, by rfl⟩ : syracuseStep 890605 = 333977) (by norm_num)
theorem B792317 : Blo 413771 792317 := bbase (se 3 (by rfl) ⟨148559, by rfl⟩ : syracuseStep 792317 = 297119) (by norm_num)
theorem B497669 : Blo 413771 497669 := bbase (se 4 (by rfl) ⟨46656, by rfl⟩ : syracuseStep 497669 = 93313) (by norm_num)
theorem B1054741 : Blo 413771 1054741 := bbase (se 6 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 1054741 = 49441) (by norm_num)
theorem B792605 : Blo 413771 792605 := bbase (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) (by norm_num)
theorem B759869 : Blo 413771 759869 := bbase (se 3 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 759869 = 284951) (by norm_num)
theorem B563269 : Blo 413771 563269 := bbase (se 4 (by rfl) ⟨52806, by rfl⟩ : syracuseStep 563269 = 105613) (by norm_num)
theorem B1054853 : Blo 413771 1054853 := bbase (se 4 (by rfl) ⟨98892, by rfl⟩ : syracuseStep 1054853 = 197785) (by norm_num)
theorem B1120405 : Blo 413771 1120405 := bbase (se 6 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 1120405 = 52519) (by norm_num)
theorem B792757 : Blo 413771 792757 := bbase (se 5 (by rfl) ⟨37160, by rfl⟩ : syracuseStep 792757 = 74321) (by norm_num)
theorem B891101 : Blo 413771 891101 := bbase (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) (by norm_num)
theorem B1055045 : Blo 413771 1055045 := bbase (se 4 (by rfl) ⟨98910, by rfl⟩ : syracuseStep 1055045 = 197821) (by norm_num)
theorem B793061 : Blo 413771 793061 := bbase (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) (by norm_num)
theorem B465493 : Blo 413771 465493 := bbase (se 8 (by rfl) ⟨2727, by rfl⟩ : syracuseStep 465493 = 5455) (by norm_num)
theorem B2103893 : Blo 413771 2103893 := bbase (se 8 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 2103893 = 24655) (by norm_num)
theorem B1579621 : Blo 413771 1579621 := bbase (se 4 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 1579621 = 296179) (by norm_num)
theorem B465529 : Blo 413771 465529 := bbase (se 2 (by rfl) ⟨174573, by rfl⟩ : syracuseStep 465529 = 349147) (by norm_num)
theorem B465565 : Blo 413771 465565 := bbase (se 3 (by rfl) ⟨87293, by rfl⟩ : syracuseStep 465565 = 174587) (by norm_num)
theorem B1055389 : Blo 413771 1055389 := bbase (se 3 (by rfl) ⟨197885, by rfl⟩ : syracuseStep 1055389 = 395771) (by norm_num)
theorem B3480245 : Blo 413771 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B498361 : Blo 413771 498361 := bbase (se 2 (by rfl) ⟨186885, by rfl⟩ : syracuseStep 498361 = 373771) (by norm_num)
theorem B465601 : Blo 413771 465601 := bbase (se 2 (by rfl) ⟨174600, by rfl⟩ : syracuseStep 465601 = 349201) (by norm_num)
theorem B465637 : Blo 413771 465637 := bbase (se 4 (by rfl) ⟨43653, by rfl⟩ : syracuseStep 465637 = 87307) (by norm_num)
theorem B465673 : Blo 413771 465673 := bbase (se 2 (by rfl) ⟨174627, by rfl⟩ : syracuseStep 465673 = 349255) (by norm_num)
theorem B1055501 : Blo 413771 1055501 := bbase (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) (by norm_num)
theorem B498457 : Blo 413771 498457 := bbase (se 2 (by rfl) ⟨186921, by rfl⟩ : syracuseStep 498457 = 373843) (by norm_num)
theorem B465709 : Blo 413771 465709 := bbase (se 3 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 465709 = 174641) (by norm_num)
theorem B465745 : Blo 413771 465745 := bbase (se 2 (by rfl) ⟨174654, by rfl⟩ : syracuseStep 465745 = 349309) (by norm_num)
theorem B465781 : Blo 413771 465781 := bbase (se 5 (by rfl) ⟨21833, by rfl⟩ : syracuseStep 465781 = 43667) (by norm_num)
theorem B1121141 : Blo 413771 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B1579925 : Blo 413771 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B465817 : Blo 413771 465817 := bbase (se 2 (by rfl) ⟨174681, by rfl⟩ : syracuseStep 465817 = 349363) (by norm_num)
theorem B465853 : Blo 413771 465853 := bbase (se 3 (by rfl) ⟨87347, by rfl⟩ : syracuseStep 465853 = 174695) (by norm_num)
theorem B1055693 : Blo 413771 1055693 := bbase (se 3 (by rfl) ⟨197942, by rfl⟩ : syracuseStep 1055693 = 395885) (by norm_num)
theorem B465889 : Blo 413771 465889 := bbase (se 2 (by rfl) ⟨174708, by rfl⟩ : syracuseStep 465889 = 349417) (by norm_num)
theorem B629741 : Blo 413771 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B465925 : Blo 413771 465925 := bbase (se 4 (by rfl) ⟨43680, by rfl⟩ : syracuseStep 465925 = 87361) (by norm_num)
theorem B629789 : Blo 413771 629789 := bbase (se 3 (by rfl) ⟨118085, by rfl⟩ : syracuseStep 629789 = 236171) (by norm_num)
theorem B465961 : Blo 413771 465961 := bbase (se 2 (by rfl) ⟨174735, by rfl⟩ : syracuseStep 465961 = 349471) (by norm_num)
theorem B465997 : Blo 413771 465997 := bbase (se 3 (by rfl) ⟨87374, by rfl⟩ : syracuseStep 465997 = 174749) (by norm_num)
theorem B891989 : Blo 413771 891989 := bbase (se 8 (by rfl) ⟨5226, by rfl⟩ : syracuseStep 891989 = 10453) (by norm_num)
theorem B466033 : Blo 413771 466033 := bbase (se 2 (by rfl) ⟨174762, by rfl⟩ : syracuseStep 466033 = 349525) (by norm_num)
theorem B1186949 : Blo 413771 1186949 := bbase (se 4 (by rfl) ⟨111276, by rfl⟩ : syracuseStep 1186949 = 222553) (by norm_num)
theorem B466069 : Blo 413771 466069 := bbase (se 6 (by rfl) ⟨10923, by rfl⟩ : syracuseStep 466069 = 21847) (by norm_num)
theorem B2694293 : Blo 413771 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B498841 : Blo 413771 498841 := bbase (se 2 (by rfl) ⟨187065, by rfl⟩ : syracuseStep 498841 = 374131) (by norm_num)
theorem B466105 : Blo 413771 466105 := bbase (se 2 (by rfl) ⟨174789, by rfl⟩ : syracuseStep 466105 = 349579) (by norm_num)
theorem B892109 : Blo 413771 892109 := bbase (se 3 (by rfl) ⟨167270, by rfl⟩ : syracuseStep 892109 = 334541) (by norm_num)
theorem B466141 : Blo 413771 466141 := bbase (se 3 (by rfl) ⟨87401, by rfl⟩ : syracuseStep 466141 = 174803) (by norm_num)
theorem B466177 : Blo 413771 466177 := bbase (se 2 (by rfl) ⟨174816, by rfl⟩ : syracuseStep 466177 = 349633) (by norm_num)
theorem B466213 : Blo 413771 466213 := bbase (se 4 (by rfl) ⟨43707, by rfl⟩ : syracuseStep 466213 = 87415) (by norm_num)
theorem B1056037 : Blo 413771 1056037 := bbase (se 4 (by rfl) ⟨99003, by rfl⟩ : syracuseStep 1056037 = 198007) (by norm_num)
theorem B466249 : Blo 413771 466249 := bbase (se 2 (by rfl) ⟨174843, by rfl⟩ : syracuseStep 466249 = 349687) (by norm_num)
theorem B466285 : Blo 413771 466285 := bbase (se 3 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 466285 = 174857) (by norm_num)
theorem B466321 : Blo 413771 466321 := bbase (se 2 (by rfl) ⟨174870, by rfl⟩ : syracuseStep 466321 = 349741) (by norm_num)
theorem B1056149 : Blo 413771 1056149 := bbase (se 6 (by rfl) ⟨24753, by rfl⟩ : syracuseStep 1056149 = 49507) (by norm_num)
theorem B1121701 : Blo 413771 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B466357 : Blo 413771 466357 := bbase (se 5 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 466357 = 43721) (by norm_num)
theorem B466393 : Blo 413771 466393 := bbase (se 2 (by rfl) ⟨174897, by rfl⟩ : syracuseStep 466393 = 349795) (by norm_num)
theorem B466429 : Blo 413771 466429 := bbase (se 3 (by rfl) ⟨87455, by rfl⟩ : syracuseStep 466429 = 174911) (by norm_num)
theorem B466465 : Blo 413771 466465 := bbase (se 2 (by rfl) ⟨174924, by rfl⟩ : syracuseStep 466465 = 349849) (by norm_num)
theorem B466501 : Blo 413771 466501 := bbase (se 4 (by rfl) ⟨43734, by rfl⟩ : syracuseStep 466501 = 87469) (by norm_num)
theorem B1056341 : Blo 413771 1056341 := bbase (se 8 (by rfl) ⟨6189, by rfl⟩ : syracuseStep 1056341 = 12379) (by norm_num)
theorem B466537 : Blo 413771 466537 := bbase (se 2 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 466537 = 349903) (by norm_num)
theorem B663149 : Blo 413771 663149 := bbase (se 3 (by rfl) ⟨124340, by rfl⟩ : syracuseStep 663149 = 248681) (by norm_num)
theorem B958061 : Blo 413771 958061 := bbase (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) (by norm_num)
theorem B466573 : Blo 413771 466573 := bbase (se 3 (by rfl) ⟨87482, by rfl⟩ : syracuseStep 466573 = 174965) (by norm_num)
theorem B466609 : Blo 413771 466609 := bbase (se 2 (by rfl) ⟨174978, by rfl⟩ : syracuseStep 466609 = 349957) (by norm_num)
theorem B466645 : Blo 413771 466645 := bbase (se 7 (by rfl) ⟨5468, by rfl⟩ : syracuseStep 466645 = 10937) (by norm_num)
theorem B3153653 : Blo 413771 3153653 := bbase (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) (by norm_num)
theorem B466681 : Blo 413771 466681 := bbase (se 2 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 466681 = 350011) (by norm_num)
theorem B466717 : Blo 413771 466717 := bbase (se 3 (by rfl) ⟨87509, by rfl⟩ : syracuseStep 466717 = 175019) (by norm_num)
theorem B466753 : Blo 413771 466753 := bbase (se 2 (by rfl) ⟨175032, by rfl⟩ : syracuseStep 466753 = 350065) (by norm_num)
theorem B466789 : Blo 413771 466789 := bbase (se 4 (by rfl) ⟨43761, by rfl⟩ : syracuseStep 466789 = 87523) (by norm_num)
theorem B2105189 : Blo 413771 2105189 := bbase (se 4 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 2105189 = 394723) (by norm_num)
theorem B466825 : Blo 413771 466825 := bbase (se 2 (by rfl) ⟨175059, by rfl⟩ : syracuseStep 466825 = 350119) (by norm_num)
theorem B2138021 : Blo 413771 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B466861 : Blo 413771 466861 := bbase (se 3 (by rfl) ⟨87536, by rfl⟩ : syracuseStep 466861 = 175073) (by norm_num)
theorem B1056685 : Blo 413771 1056685 := bbase (se 3 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 1056685 = 396257) (by norm_num)
theorem B466897 : Blo 413771 466897 := bbase (se 2 (by rfl) ⟨175086, by rfl⟩ : syracuseStep 466897 = 350173) (by norm_num)
theorem B1777621 : Blo 413771 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B663533 : Blo 413771 663533 := bbase (se 3 (by rfl) ⟨124412, by rfl⟩ : syracuseStep 663533 = 248825) (by norm_num)
theorem B466933 : Blo 413771 466933 := bbase (se 5 (by rfl) ⟨21887, by rfl⟩ : syracuseStep 466933 = 43775) (by norm_num)
theorem B1351669 : Blo 413771 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B466969 : Blo 413771 466969 := bbase (se 2 (by rfl) ⟨175113, by rfl⟩ : syracuseStep 466969 = 350227) (by norm_num)
theorem B1056797 : Blo 413771 1056797 := bbase (se 3 (by rfl) ⟨198149, by rfl⟩ : syracuseStep 1056797 = 396299) (by norm_num)
theorem B467005 : Blo 413771 467005 := bbase (se 3 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 467005 = 175127) (by norm_num)
theorem B467041 : Blo 413771 467041 := bbase (se 2 (by rfl) ⟨175140, by rfl⟩ : syracuseStep 467041 = 350281) (by norm_num)
theorem B663661 : Blo 413771 663661 := bbase (se 3 (by rfl) ⟨124436, by rfl⟩ : syracuseStep 663661 = 248873) (by norm_num)
theorem B467077 : Blo 413771 467077 := bbase (se 4 (by rfl) ⟨43788, by rfl⟩ : syracuseStep 467077 = 87577) (by norm_num)
theorem B467113 : Blo 413771 467113 := bbase (se 2 (by rfl) ⟨175167, by rfl⟩ : syracuseStep 467113 = 350335) (by norm_num)
theorem B499889 : Blo 413771 499889 := bbase (se 2 (by rfl) ⟨187458, by rfl⟩ : syracuseStep 499889 = 374917) (by norm_num)
theorem B467149 : Blo 413771 467149 := bbase (se 3 (by rfl) ⟨87590, by rfl⟩ : syracuseStep 467149 = 175181) (by norm_num)
theorem B2367701 : Blo 413771 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B1056989 : Blo 413771 1056989 := bbase (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) (by norm_num)
theorem B467185 : Blo 413771 467185 := bbase (se 2 (by rfl) ⟨175194, by rfl⟩ : syracuseStep 467185 = 350389) (by norm_num)
theorem B467221 : Blo 413771 467221 := bbase (se 6 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 467221 = 21901) (by norm_num)
theorem B467257 : Blo 413771 467257 := bbase (se 2 (by rfl) ⟨175221, by rfl⟩ : syracuseStep 467257 = 350443) (by norm_num)
theorem B12165461 : Blo 413771 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B467293 : Blo 413771 467293 := bbase (se 3 (by rfl) ⟨87617, by rfl⟩ : syracuseStep 467293 = 175235) (by norm_num)
theorem B467329 : Blo 413771 467329 := bbase (se 2 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 467329 = 350497) (by norm_num)
theorem B467365 : Blo 413771 467365 := bbase (se 4 (by rfl) ⟨43815, by rfl⟩ : syracuseStep 467365 = 87631) (by norm_num)
theorem B467401 : Blo 413771 467401 := bbase (se 2 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 467401 = 350551) (by norm_num)
theorem B500197 : Blo 413771 500197 := bbase (se 4 (by rfl) ⟨46893, by rfl⟩ : syracuseStep 500197 = 93787) (by norm_num)
theorem B467437 : Blo 413771 467437 := bbase (se 3 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 467437 = 175289) (by norm_num)
theorem B500225 : Blo 413771 500225 := bbase (se 2 (by rfl) ⟨187584, by rfl⟩ : syracuseStep 500225 = 375169) (by norm_num)
theorem B467473 : Blo 413771 467473 := bbase (se 2 (by rfl) ⟨175302, by rfl⟩ : syracuseStep 467473 = 350605) (by norm_num)
theorem B467509 : Blo 413771 467509 := bbase (se 5 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 467509 = 43829) (by norm_num)
theorem B1057333 : Blo 413771 1057333 := bbase (se 5 (by rfl) ⟨49562, by rfl⟩ : syracuseStep 1057333 = 99125) (by norm_num)
theorem B434761 : Blo 413771 434761 := bbase (se 2 (by rfl) ⟨163035, by rfl⟩ : syracuseStep 434761 = 326071) (by norm_num)
theorem B1679957 : Blo 413771 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B467545 : Blo 413771 467545 := bbase (se 2 (by rfl) ⟨175329, by rfl⟩ : syracuseStep 467545 = 350659) (by norm_num)
theorem B467581 : Blo 413771 467581 := bbase (se 3 (by rfl) ⟨87671, by rfl⟩ : syracuseStep 467581 = 175343) (by norm_num)
theorem B467617 : Blo 413771 467617 := bbase (se 2 (by rfl) ⟨175356, by rfl⟩ : syracuseStep 467617 = 350713) (by norm_num)
theorem B1057445 : Blo 413771 1057445 := bbase (se 4 (by rfl) ⟨99135, by rfl⟩ : syracuseStep 1057445 = 198271) (by norm_num)
theorem B1188533 : Blo 413771 1188533 := bbase (se 5 (by rfl) ⟨55712, by rfl⟩ : syracuseStep 1188533 = 111425) (by norm_num)
theorem B467653 : Blo 413771 467653 := bbase (se 4 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 467653 = 87685) (by norm_num)
theorem B467689 : Blo 413771 467689 := bbase (se 2 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 467689 = 350767) (by norm_num)
theorem B631541 : Blo 413771 631541 := bbase (se 5 (by rfl) ⟨29603, by rfl⟩ : syracuseStep 631541 = 59207) (by norm_num)
theorem B467725 : Blo 413771 467725 := bbase (se 3 (by rfl) ⟨87698, by rfl⟩ : syracuseStep 467725 = 175397) (by norm_num)
theorem B467761 : Blo 413771 467761 := bbase (se 2 (by rfl) ⟨175410, by rfl⟩ : syracuseStep 467761 = 350821) (by norm_num)
theorem B467797 : Blo 413771 467797 := bbase (se 9 (by rfl) ⟨1370, by rfl⟩ : syracuseStep 467797 = 2741) (by norm_num)
theorem B467833 : Blo 413771 467833 := bbase (se 2 (by rfl) ⟨175437, by rfl⟩ : syracuseStep 467833 = 350875) (by norm_num)
theorem B467869 : Blo 413771 467869 := bbase (se 3 (by rfl) ⟨87725, by rfl⟩ : syracuseStep 467869 = 175451) (by norm_num)
theorem B467905 : Blo 413771 467905 := bbase (se 2 (by rfl) ⟨175464, by rfl⟩ : syracuseStep 467905 = 350929) (by norm_num)
theorem B1582037 : Blo 413771 1582037 := bbase (se 7 (by rfl) ⟨18539, by rfl⟩ : syracuseStep 1582037 = 37079) (by norm_num)
theorem B467941 : Blo 413771 467941 := bbase (se 4 (by rfl) ⟨43869, by rfl⟩ : syracuseStep 467941 = 87739) (by norm_num)
theorem B500725 : Blo 413771 500725 := bbase (se 5 (by rfl) ⟨23471, by rfl⟩ : syracuseStep 500725 = 46943) (by norm_num)
theorem B467977 : Blo 413771 467977 := bbase (se 2 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 467977 = 350983) (by norm_num)
theorem B468013 : Blo 413771 468013 := bbase (se 3 (by rfl) ⟨87752, by rfl⟩ : syracuseStep 468013 = 175505) (by norm_num)
theorem B468049 : Blo 413771 468049 := bbase (se 2 (by rfl) ⟨175518, by rfl⟩ : syracuseStep 468049 = 351037) (by norm_num)
theorem B664661 : Blo 413771 664661 := bbase (se 8 (by rfl) ⟨3894, by rfl⟩ : syracuseStep 664661 = 7789) (by norm_num)
theorem B468085 : Blo 413771 468085 := bbase (se 5 (by rfl) ⟨21941, by rfl⟩ : syracuseStep 468085 = 43883) (by norm_num)
theorem B2106485 : Blo 413771 2106485 := bbase (se 5 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 2106485 = 197483) (by norm_num)
theorem B4007029 : Blo 413771 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B468121 : Blo 413771 468121 := bbase (se 2 (by rfl) ⟨175545, by rfl⟩ : syracuseStep 468121 = 351091) (by norm_num)
theorem B468157 : Blo 413771 468157 := bbase (se 3 (by rfl) ⟨87779, by rfl⟩ : syracuseStep 468157 = 175559) (by norm_num)
theorem B664789 : Blo 413771 664789 := bbase (se 7 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 664789 = 15581) (by norm_num)
theorem B1123541 : Blo 413771 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B468193 : Blo 413771 468193 := bbase (se 2 (by rfl) ⟨175572, by rfl⟩ : syracuseStep 468193 = 351145) (by norm_num)
theorem B1582325 : Blo 413771 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B468229 : Blo 413771 468229 := bbase (se 4 (by rfl) ⟨43896, by rfl⟩ : syracuseStep 468229 = 87793) (by norm_num)
theorem B468265 : Blo 413771 468265 := bbase (se 2 (by rfl) ⟨175599, by rfl⟩ : syracuseStep 468265 = 351199) (by norm_num)
theorem B468301 : Blo 413771 468301 := bbase (se 3 (by rfl) ⟨87806, by rfl⟩ : syracuseStep 468301 = 175613) (by norm_num)
theorem B1189205 : Blo 413771 1189205 := bbase (se 12 (by rfl) ⟨435, by rfl⟩ : syracuseStep 1189205 = 871) (by norm_num)
theorem B468337 : Blo 413771 468337 := bbase (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) (by norm_num)
theorem B2368885 : Blo 413771 2368885 := bbase (se 5 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 2368885 = 222083) (by norm_num)
theorem B468373 : Blo 413771 468373 := bbase (se 6 (by rfl) ⟨10977, by rfl⟩ : syracuseStep 468373 = 21955) (by norm_num)
theorem B468409 : Blo 413771 468409 := bbase (se 2 (by rfl) ⟨175653, by rfl⟩ : syracuseStep 468409 = 351307) (by norm_num)
theorem B468445 : Blo 413771 468445 := bbase (se 3 (by rfl) ⟨87833, by rfl⟩ : syracuseStep 468445 = 175667) (by norm_num)
theorem B468481 : Blo 413771 468481 := bbase (se 2 (by rfl) ⟨175680, by rfl⟩ : syracuseStep 468481 = 351361) (by norm_num)
theorem B468517 : Blo 413771 468517 := bbase (se 4 (by rfl) ⟨43923, by rfl⟩ : syracuseStep 468517 = 87847) (by norm_num)
theorem B468553 : Blo 413771 468553 := bbase (se 2 (by rfl) ⟨175707, by rfl⟩ : syracuseStep 468553 = 351415) (by norm_num)
theorem B665173 : Blo 413771 665173 := bbase (se 8 (by rfl) ⟨3897, by rfl⟩ : syracuseStep 665173 = 7795) (by norm_num)
theorem B1222229 : Blo 413771 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B468589 : Blo 413771 468589 := bbase (se 3 (by rfl) ⟨87860, by rfl⟩ : syracuseStep 468589 = 175721) (by norm_num)
theorem B468625 : Blo 413771 468625 := bbase (se 2 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 468625 = 351469) (by norm_num)
theorem B468661 : Blo 413771 468661 := bbase (se 5 (by rfl) ⟨21968, by rfl⟩ : syracuseStep 468661 = 43937) (by norm_num)
theorem B468697 : Blo 413771 468697 := bbase (se 2 (by rfl) ⟨175761, by rfl⟩ : syracuseStep 468697 = 351523) (by norm_num)
theorem B468733 : Blo 413771 468733 := bbase (se 3 (by rfl) ⟨87887, by rfl⟩ : syracuseStep 468733 = 175775) (by norm_num)
theorem B1189637 : Blo 413771 1189637 := bbase (se 4 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 1189637 = 223057) (by norm_num)
theorem B468769 : Blo 413771 468769 := bbase (se 2 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 468769 = 351577) (by norm_num)
theorem B468805 : Blo 413771 468805 := bbase (se 4 (by rfl) ⟨43950, by rfl⟩ : syracuseStep 468805 = 87901) (by norm_num)
theorem B665429 : Blo 413771 665429 := bbase (se 9 (by rfl) ⟨1949, by rfl⟩ : syracuseStep 665429 = 3899) (by norm_num)
theorem B468841 : Blo 413771 468841 := bbase (se 2 (by rfl) ⟨175815, by rfl⟩ : syracuseStep 468841 = 351631) (by norm_num)
theorem B468877 : Blo 413771 468877 := bbase (se 3 (by rfl) ⟨87914, by rfl⟩ : syracuseStep 468877 = 175829) (by norm_num)
theorem B468913 : Blo 413771 468913 := bbase (se 2 (by rfl) ⟨175842, by rfl⟩ : syracuseStep 468913 = 351685) (by norm_num)
theorem B468949 : Blo 413771 468949 := bbase (se 7 (by rfl) ⟨5495, by rfl⟩ : syracuseStep 468949 = 10991) (by norm_num)
theorem B698341 : Blo 413771 698341 := bbase (se 4 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 698341 = 130939) (by norm_num)
theorem B468985 : Blo 413771 468985 := bbase (se 2 (by rfl) ⟨175869, by rfl⟩ : syracuseStep 468985 = 351739) (by norm_num)
theorem B469021 : Blo 413771 469021 := bbase (se 3 (by rfl) ⟨87941, by rfl⟩ : syracuseStep 469021 = 175883) (by norm_num)
theorem B698429 : Blo 413771 698429 := bbase (se 3 (by rfl) ⟨130955, by rfl⟩ : syracuseStep 698429 = 261911) (by norm_num)
theorem B469057 : Blo 413771 469057 := bbase (se 2 (by rfl) ⟨175896, by rfl⟩ : syracuseStep 469057 = 351793) (by norm_num)
theorem B13674581 : Blo 413771 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B469093 : Blo 413771 469093 := bbase (se 4 (by rfl) ⟨43977, by rfl⟩ : syracuseStep 469093 = 87955) (by norm_num)
theorem B469129 : Blo 413771 469129 := bbase (se 2 (by rfl) ⟨175923, by rfl⟩ : syracuseStep 469129 = 351847) (by norm_num)
theorem B469165 : Blo 413771 469165 := bbase (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) (by norm_num)
theorem B3549365 : Blo 413771 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B698557 : Blo 413771 698557 := bbase (se 3 (by rfl) ⟨130979, by rfl⟩ : syracuseStep 698557 = 261959) (by norm_num)
theorem B469201 : Blo 413771 469201 := bbase (se 2 (by rfl) ⟨175950, by rfl⟩ : syracuseStep 469201 = 351901) (by norm_num)
theorem B469237 : Blo 413771 469237 := bbase (se 5 (by rfl) ⟨21995, by rfl⟩ : syracuseStep 469237 = 43991) (by norm_num)
theorem B698645 : Blo 413771 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B469273 : Blo 413771 469273 := bbase (se 2 (by rfl) ⟨175977, by rfl⟩ : syracuseStep 469273 = 351955) (by norm_num)
theorem B469309 : Blo 413771 469309 := bbase (se 3 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 469309 = 175991) (by norm_num)
theorem B469345 : Blo 413771 469345 := bbase (se 2 (by rfl) ⟨176004, by rfl⟩ : syracuseStep 469345 = 352009) (by norm_num)
theorem B2107781 : Blo 413771 2107781 := bbase (se 4 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 2107781 = 395209) (by norm_num)
theorem B469381 : Blo 413771 469381 := bbase (se 4 (by rfl) ⟨44004, by rfl⟩ : syracuseStep 469381 = 88009) (by norm_num)
theorem B698773 : Blo 413771 698773 := bbase (se 6 (by rfl) ⟨16377, by rfl⟩ : syracuseStep 698773 = 32755) (by norm_num)
theorem B1583509 : Blo 413771 1583509 := bbase (se 6 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 1583509 = 74227) (by norm_num)
theorem B469417 : Blo 413771 469417 := bbase (se 2 (by rfl) ⟨176031, by rfl⟩ : syracuseStep 469417 = 352063) (by norm_num)
theorem B469453 : Blo 413771 469453 := bbase (se 3 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 469453 = 176045) (by norm_num)
theorem B698861 : Blo 413771 698861 := bbase (se 3 (by rfl) ⟨131036, by rfl⟩ : syracuseStep 698861 = 262073) (by norm_num)
theorem B469489 : Blo 413771 469489 := bbase (se 2 (by rfl) ⟨176058, by rfl⟩ : syracuseStep 469489 = 352117) (by norm_num)
theorem B469525 : Blo 413771 469525 := bbase (se 6 (by rfl) ⟨11004, by rfl⟩ : syracuseStep 469525 = 22009) (by norm_num)
theorem B535081 : Blo 413771 535081 := bbase (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) (by norm_num)
theorem B469561 : Blo 413771 469561 := bbase (se 2 (by rfl) ⟨176085, by rfl⟩ : syracuseStep 469561 = 352171) (by norm_num)
theorem B469597 : Blo 413771 469597 := bbase (se 3 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 469597 = 176099) (by norm_num)
theorem B698989 : Blo 413771 698989 := bbase (se 3 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 698989 = 262121) (by norm_num)
theorem B469633 : Blo 413771 469633 := bbase (se 2 (by rfl) ⟨176112, by rfl⟩ : syracuseStep 469633 = 352225) (by norm_num)
theorem B469669 : Blo 413771 469669 := bbase (se 4 (by rfl) ⟨44031, by rfl⟩ : syracuseStep 469669 = 88063) (by norm_num)
theorem B666301 : Blo 413771 666301 := bbase (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) (by norm_num)
theorem B699077 : Blo 413771 699077 := bbase (se 4 (by rfl) ⟨65538, by rfl⟩ : syracuseStep 699077 = 131077) (by norm_num)
theorem B1583813 : Blo 413771 1583813 := bbase (se 4 (by rfl) ⟨148482, by rfl⟩ : syracuseStep 1583813 = 296965) (by norm_num)
theorem B469705 : Blo 413771 469705 := bbase (se 2 (by rfl) ⟨176139, by rfl⟩ : syracuseStep 469705 = 352279) (by norm_num)
theorem B469741 : Blo 413771 469741 := bbase (se 3 (by rfl) ⟨88076, by rfl⟩ : syracuseStep 469741 = 176153) (by norm_num)
theorem B469777 : Blo 413771 469777 := bbase (se 2 (by rfl) ⟨176166, by rfl⟩ : syracuseStep 469777 = 352333) (by norm_num)
theorem B666397 : Blo 413771 666397 := bbase (se 3 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 666397 = 249899) (by norm_num)
theorem B469813 : Blo 413771 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B699205 : Blo 413771 699205 := bbase (se 4 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 699205 = 131101) (by norm_num)
theorem B469849 : Blo 413771 469849 := bbase (se 2 (by rfl) ⟨176193, by rfl⟩ : syracuseStep 469849 = 352387) (by norm_num)
theorem B469885 : Blo 413771 469885 := bbase (se 3 (by rfl) ⟨88103, by rfl⟩ : syracuseStep 469885 = 176207) (by norm_num)
theorem B1780613 : Blo 413771 1780613 := bbase (se 4 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 1780613 = 333865) (by norm_num)
theorem B699293 : Blo 413771 699293 := bbase (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) (by norm_num)
theorem B469921 : Blo 413771 469921 := bbase (se 2 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 469921 = 352441) (by norm_num)
theorem B666557 : Blo 413771 666557 := bbase (se 3 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 666557 = 249959) (by norm_num)
theorem B469957 : Blo 413771 469957 := bbase (se 4 (by rfl) ⟨44058, by rfl⟩ : syracuseStep 469957 = 88117) (by norm_num)
theorem B469993 : Blo 413771 469993 := bbase (se 2 (by rfl) ⟨176247, by rfl⟩ : syracuseStep 469993 = 352495) (by norm_num)
theorem B1518581 : Blo 413771 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B699421 : Blo 413771 699421 := bbase (se 3 (by rfl) ⟨131141, by rfl⟩ : syracuseStep 699421 = 262283) (by norm_num)
theorem B699509 : Blo 413771 699509 := bbase (se 5 (by rfl) ⟨32789, by rfl⟩ : syracuseStep 699509 = 65579) (by norm_num)
theorem B994493 : Blo 413771 994493 := bbase (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) (by norm_num)
theorem B699637 : Blo 413771 699637 := bbase (se 5 (by rfl) ⟨32795, by rfl⟩ : syracuseStep 699637 = 65591) (by norm_num)
theorem B2370869 : Blo 413771 2370869 := bbase (se 5 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 2370869 = 222269) (by norm_num)
theorem B699725 : Blo 413771 699725 := bbase (se 3 (by rfl) ⟨131198, by rfl⟩ : syracuseStep 699725 = 262397) (by norm_num)
theorem B699853 : Blo 413771 699853 := bbase (se 3 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 699853 = 262445) (by norm_num)
theorem B1125845 : Blo 413771 1125845 := bbase (se 7 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 1125845 = 26387) (by norm_num)
theorem B994781 : Blo 413771 994781 := bbase (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) (by norm_num)
theorem B699941 : Blo 413771 699941 := bbase (se 4 (by rfl) ⟨65619, by rfl⟩ : syracuseStep 699941 = 131239) (by norm_num)
theorem B2109077 : Blo 413771 2109077 := bbase (se 6 (by rfl) ⟨49431, by rfl⟩ : syracuseStep 2109077 = 98863) (by norm_num)
theorem B700069 : Blo 413771 700069 := bbase (se 4 (by rfl) ⟨65631, by rfl⟩ : syracuseStep 700069 = 131263) (by norm_num)
theorem B700157 : Blo 413771 700157 := bbase (se 3 (by rfl) ⟨131279, by rfl⟩ : syracuseStep 700157 = 262559) (by norm_num)
theorem B1421077 : Blo 413771 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B3977045 : Blo 413771 3977045 := bbase (se 9 (by rfl) ⟨11651, by rfl⟩ : syracuseStep 3977045 = 23303) (by norm_num)
theorem B1781621 : Blo 413771 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B700285 : Blo 413771 700285 := bbase (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) (by norm_num)
theorem B700373 : Blo 413771 700373 := bbase (se 7 (by rfl) ⟨8207, by rfl⟩ : syracuseStep 700373 = 16415) (by norm_num)
theorem B667685 : Blo 413771 667685 := bbase (se 4 (by rfl) ⟨62595, by rfl⟩ : syracuseStep 667685 = 125191) (by norm_num)
theorem B700501 : Blo 413771 700501 := bbase (se 8 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 700501 = 8209) (by norm_num)
theorem B700589 : Blo 413771 700589 := bbase (se 3 (by rfl) ⟨131360, by rfl⟩ : syracuseStep 700589 = 262721) (by norm_num)
theorem B798925 : Blo 413771 798925 := bbase (se 3 (by rfl) ⟨149798, by rfl⟩ : syracuseStep 798925 = 299597) (by norm_num)
theorem B700717 : Blo 413771 700717 := bbase (se 3 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 700717 = 262769) (by norm_num)
theorem B700805 : Blo 413771 700805 := bbase (se 4 (by rfl) ⟨65700, by rfl⟩ : syracuseStep 700805 = 131401) (by norm_num)
theorem B799141 : Blo 413771 799141 := bbase (se 4 (by rfl) ⟨74919, by rfl⟩ : syracuseStep 799141 = 149839) (by norm_num)
theorem B700933 : Blo 413771 700933 := bbase (se 4 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 700933 = 131425) (by norm_num)
theorem B602653 : Blo 413771 602653 := bbase (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) (by norm_num)
theorem B668197 : Blo 413771 668197 := bbase (se 4 (by rfl) ⟨62643, by rfl⟩ : syracuseStep 668197 = 125287) (by norm_num)
theorem B701021 : Blo 413771 701021 := bbase (se 3 (by rfl) ⟨131441, by rfl⟩ : syracuseStep 701021 = 262883) (by norm_num)
theorem B701149 : Blo 413771 701149 := bbase (se 3 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 701149 = 262931) (by norm_num)
theorem B1585925 : Blo 413771 1585925 := bbase (se 4 (by rfl) ⟨148680, by rfl⟩ : syracuseStep 1585925 = 297361) (by norm_num)
theorem B897821 : Blo 413771 897821 := bbase (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) (by norm_num)
theorem B799541 : Blo 413771 799541 := bbase (se 5 (by rfl) ⟨37478, by rfl⟩ : syracuseStep 799541 = 74957) (by norm_num)
theorem B701237 : Blo 413771 701237 := bbase (se 5 (by rfl) ⟨32870, by rfl⟩ : syracuseStep 701237 = 65741) (by norm_num)
theorem B2110373 : Blo 413771 2110373 := bbase (se 4 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 2110373 = 395695) (by norm_num)
theorem B701365 : Blo 413771 701365 := bbase (se 5 (by rfl) ⟨32876, by rfl⟩ : syracuseStep 701365 = 65753) (by norm_num)
theorem B799741 : Blo 413771 799741 := bbase (se 3 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 799741 = 299903) (by norm_num)
theorem B701453 : Blo 413771 701453 := bbase (se 3 (by rfl) ⟨131522, by rfl⟩ : syracuseStep 701453 = 263045) (by norm_num)
theorem B1586213 : Blo 413771 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B701581 : Blo 413771 701581 := bbase (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) (by norm_num)
theorem B931013 : Blo 413771 931013 := bbase (se 4 (by rfl) ⟨87282, by rfl⟩ : syracuseStep 931013 = 174565) (by norm_num)
theorem B701669 : Blo 413771 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B931085 : Blo 413771 931085 := bbase (se 3 (by rfl) ⟨174578, by rfl⟩ : syracuseStep 931085 = 349157) (by norm_num)
theorem B931157 : Blo 413771 931157 := bbase (se 13 (by rfl) ⟨170, by rfl⟩ : syracuseStep 931157 = 341) (by norm_num)
theorem B701797 : Blo 413771 701797 := bbase (se 4 (by rfl) ⟨65793, by rfl⟩ : syracuseStep 701797 = 131587) (by norm_num)
theorem B931229 : Blo 413771 931229 := bbase (se 3 (by rfl) ⟨174605, by rfl⟩ : syracuseStep 931229 = 349211) (by norm_num)
theorem B701885 : Blo 413771 701885 := bbase (se 3 (by rfl) ⟨131603, by rfl⟩ : syracuseStep 701885 = 263207) (by norm_num)
theorem B2373077 : Blo 413771 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B931301 : Blo 413771 931301 := bbase (se 4 (by rfl) ⟨87309, by rfl⟩ : syracuseStep 931301 = 174619) (by norm_num)
theorem B931373 : Blo 413771 931373 := bbase (se 3 (by rfl) ⟨174632, by rfl⟩ : syracuseStep 931373 = 349265) (by norm_num)
theorem B702013 : Blo 413771 702013 := bbase (se 3 (by rfl) ⟨131627, by rfl⟩ : syracuseStep 702013 = 263255) (by norm_num)
theorem B6305365 : Blo 413771 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B1783397 : Blo 413771 1783397 := bbase (se 4 (by rfl) ⟨167193, by rfl⟩ : syracuseStep 1783397 = 334387) (by norm_num)
theorem B931445 : Blo 413771 931445 := bbase (se 5 (by rfl) ⟨43661, by rfl⟩ : syracuseStep 931445 = 87323) (by norm_num)
theorem B472717 : Blo 413771 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B702101 : Blo 413771 702101 := bbase (se 6 (by rfl) ⟨16455, by rfl⟩ : syracuseStep 702101 = 32911) (by norm_num)
theorem B472753 : Blo 413771 472753 := bbase (se 2 (by rfl) ⟨177282, by rfl⟩ : syracuseStep 472753 = 354565) (by norm_num)
theorem B931517 : Blo 413771 931517 := bbase (se 3 (by rfl) ⟨174659, by rfl⟩ : syracuseStep 931517 = 349319) (by norm_num)
theorem B964325 : Blo 413771 964325 := bbase (se 4 (by rfl) ⟨90405, by rfl⟩ : syracuseStep 964325 = 180811) (by norm_num)
theorem B2668277 : Blo 413771 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B931589 : Blo 413771 931589 := bbase (se 4 (by rfl) ⟨87336, by rfl⟩ : syracuseStep 931589 = 174673) (by norm_num)
theorem B702229 : Blo 413771 702229 := bbase (se 6 (by rfl) ⟨16458, by rfl⟩ : syracuseStep 702229 = 32917) (by norm_num)
theorem B931661 : Blo 413771 931661 := bbase (se 3 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 931661 = 349373) (by norm_num)
theorem B702317 : Blo 413771 702317 := bbase (se 3 (by rfl) ⟨131684, by rfl⟩ : syracuseStep 702317 = 263369) (by norm_num)
theorem B931733 : Blo 413771 931733 := bbase (se 6 (by rfl) ⟨21837, by rfl⟩ : syracuseStep 931733 = 43675) (by norm_num)
theorem B1062845 : Blo 413771 1062845 := bbase (se 3 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 1062845 = 398567) (by norm_num)
theorem B473045 : Blo 413771 473045 := bbase (se 7 (by rfl) ⟨5543, by rfl⟩ : syracuseStep 473045 = 11087) (by norm_num)
theorem B931805 : Blo 413771 931805 := bbase (se 3 (by rfl) ⟨174713, by rfl⟩ : syracuseStep 931805 = 349427) (by norm_num)
theorem B702445 : Blo 413771 702445 := bbase (se 3 (by rfl) ⟨131708, by rfl⟩ : syracuseStep 702445 = 263417) (by norm_num)
theorem B931877 : Blo 413771 931877 := bbase (se 4 (by rfl) ⟨87363, by rfl⟩ : syracuseStep 931877 = 174727) (by norm_num)
theorem B702533 : Blo 413771 702533 := bbase (se 4 (by rfl) ⟨65862, by rfl⟩ : syracuseStep 702533 = 131725) (by norm_num)
theorem B931949 : Blo 413771 931949 := bbase (se 3 (by rfl) ⟨174740, by rfl⟩ : syracuseStep 931949 = 349481) (by norm_num)
theorem B1128613 : Blo 413771 1128613 := bbase (se 4 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 1128613 = 211615) (by norm_num)
theorem B1816757 : Blo 413771 1816757 := bbase (se 5 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 1816757 = 170321) (by norm_num)
theorem B932021 : Blo 413771 932021 := bbase (se 5 (by rfl) ⟨43688, by rfl⟩ : syracuseStep 932021 = 87377) (by norm_num)
theorem B2111669 : Blo 413771 2111669 := bbase (se 5 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 2111669 = 197969) (by norm_num)
theorem B702661 : Blo 413771 702661 := bbase (se 4 (by rfl) ⟨65874, by rfl⟩ : syracuseStep 702661 = 131749) (by norm_num)
theorem B932093 : Blo 413771 932093 := bbase (se 3 (by rfl) ⟨174767, by rfl⟩ : syracuseStep 932093 = 349535) (by norm_num)
theorem B702749 : Blo 413771 702749 := bbase (se 3 (by rfl) ⟨131765, by rfl⟩ : syracuseStep 702749 = 263531) (by norm_num)
theorem B899381 : Blo 413771 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B932165 : Blo 413771 932165 := bbase (se 4 (by rfl) ⟨87390, by rfl⟩ : syracuseStep 932165 = 174781) (by norm_num)
theorem B538969 : Blo 413771 538969 := bbase (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) (by norm_num)
theorem B932237 : Blo 413771 932237 := bbase (se 3 (by rfl) ⟨174794, by rfl⟩ : syracuseStep 932237 = 349589) (by norm_num)
theorem B702877 : Blo 413771 702877 := bbase (se 3 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 702877 = 263579) (by norm_num)
theorem B1423813 : Blo 413771 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B932309 : Blo 413771 932309 := bbase (se 7 (by rfl) ⟨10925, by rfl⟩ : syracuseStep 932309 = 21851) (by norm_num)
theorem B702965 : Blo 413771 702965 := bbase (se 5 (by rfl) ⟨32951, by rfl⟩ : syracuseStep 702965 = 65903) (by norm_num)
theorem B932381 : Blo 413771 932381 := bbase (se 3 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 932381 = 349643) (by norm_num)
theorem B997933 : Blo 413771 997933 := bbase (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) (by norm_num)
theorem B932453 : Blo 413771 932453 := bbase (se 4 (by rfl) ⟨87417, by rfl⟩ : syracuseStep 932453 = 174835) (by norm_num)
theorem B703093 : Blo 413771 703093 := bbase (se 5 (by rfl) ⟨32957, by rfl⟩ : syracuseStep 703093 = 65915) (by norm_num)
theorem B506525 : Blo 413771 506525 := bbase (se 3 (by rfl) ⟨94973, by rfl⟩ : syracuseStep 506525 = 189947) (by norm_num)
theorem B932525 : Blo 413771 932525 := bbase (se 3 (by rfl) ⟨174848, by rfl⟩ : syracuseStep 932525 = 349697) (by norm_num)
theorem B703181 : Blo 413771 703181 := bbase (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) (by norm_num)
theorem B932597 : Blo 413771 932597 := bbase (se 5 (by rfl) ⟨43715, by rfl⟩ : syracuseStep 932597 = 87431) (by norm_num)
theorem B801565 : Blo 413771 801565 := bbase (se 3 (by rfl) ⟨150293, by rfl⟩ : syracuseStep 801565 = 300587) (by norm_num)
theorem B932669 : Blo 413771 932669 := bbase (se 3 (by rfl) ⟨174875, by rfl⟩ : syracuseStep 932669 = 349751) (by norm_num)
theorem B703309 : Blo 413771 703309 := bbase (se 3 (by rfl) ⟨131870, by rfl⟩ : syracuseStep 703309 = 263741) (by norm_num)
theorem B932741 : Blo 413771 932741 := bbase (se 4 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 932741 = 174889) (by norm_num)
theorem B703397 : Blo 413771 703397 := bbase (se 4 (by rfl) ⟨65943, by rfl⟩ : syracuseStep 703397 = 131887) (by norm_num)
theorem B932813 : Blo 413771 932813 := bbase (se 3 (by rfl) ⟨174902, by rfl⟩ : syracuseStep 932813 = 349805) (by norm_num)
theorem B932885 : Blo 413771 932885 := bbase (se 6 (by rfl) ⟨21864, by rfl⟩ : syracuseStep 932885 = 43729) (by norm_num)
theorem B703525 : Blo 413771 703525 := bbase (se 4 (by rfl) ⟨65955, by rfl⟩ : syracuseStep 703525 = 131911) (by norm_num)
theorem B932957 : Blo 413771 932957 := bbase (se 3 (by rfl) ⟨174929, by rfl⟩ : syracuseStep 932957 = 349859) (by norm_num)
theorem B703613 : Blo 413771 703613 := bbase (se 3 (by rfl) ⟨131927, by rfl⟩ : syracuseStep 703613 = 263855) (by norm_num)
theorem B933029 : Blo 413771 933029 := bbase (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) (by norm_num)
theorem B998605 : Blo 413771 998605 := bbase (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) (by norm_num)
theorem B933101 : Blo 413771 933101 := bbase (se 3 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 933101 = 349913) (by norm_num)
theorem B703741 : Blo 413771 703741 := bbase (se 3 (by rfl) ⟨131951, by rfl⟩ : syracuseStep 703741 = 263903) (by norm_num)
theorem B933173 : Blo 413771 933173 := bbase (se 5 (by rfl) ⟨43742, by rfl⟩ : syracuseStep 933173 = 87485) (by norm_num)
theorem B3161429 : Blo 413771 3161429 := bbase (se 11 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 3161429 = 4631) (by norm_num)
theorem B703829 : Blo 413771 703829 := bbase (se 11 (by rfl) ⟨515, by rfl⟩ : syracuseStep 703829 = 1031) (by norm_num)
theorem B933245 : Blo 413771 933245 := bbase (se 3 (by rfl) ⟨174983, by rfl⟩ : syracuseStep 933245 = 349967) (by norm_num)
theorem B638357 : Blo 413771 638357 := bbase (se 6 (by rfl) ⟨14961, by rfl⟩ : syracuseStep 638357 = 29923) (by norm_num)
theorem B998837 : Blo 413771 998837 := bbase (se 5 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 998837 = 93641) (by norm_num)
theorem B933317 : Blo 413771 933317 := bbase (se 4 (by rfl) ⟨87498, by rfl⟩ : syracuseStep 933317 = 174997) (by norm_num)
theorem B2112965 : Blo 413771 2112965 := bbase (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) (by norm_num)
theorem B1686997 : Blo 413771 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B703957 : Blo 413771 703957 := bbase (se 7 (by rfl) ⟨8249, by rfl⟩ : syracuseStep 703957 = 16499) (by norm_num)
theorem B933389 : Blo 413771 933389 := bbase (se 3 (by rfl) ⟨175010, by rfl⟩ : syracuseStep 933389 = 350021) (by norm_num)
theorem B474641 : Blo 413771 474641 := bbase (se 2 (by rfl) ⟨177990, by rfl⟩ : syracuseStep 474641 = 355981) (by norm_num)
theorem B704045 : Blo 413771 704045 := bbase (se 3 (by rfl) ⟨132008, by rfl⟩ : syracuseStep 704045 = 264017) (by norm_num)
theorem B998981 : Blo 413771 998981 := bbase (se 4 (by rfl) ⟨93654, by rfl⟩ : syracuseStep 998981 = 187309) (by norm_num)
theorem B441941 : Blo 413771 441941 := bbase (se 8 (by rfl) ⟨2589, by rfl⟩ : syracuseStep 441941 = 5179) (by norm_num)
theorem B933461 : Blo 413771 933461 := bbase (se 8 (by rfl) ⟨5469, by rfl⟩ : syracuseStep 933461 = 10939) (by norm_num)
theorem B999029 : Blo 413771 999029 := bbase (se 5 (by rfl) ⟨46829, by rfl⟩ : syracuseStep 999029 = 93659) (by norm_num)
theorem B933533 : Blo 413771 933533 := bbase (se 3 (by rfl) ⟨175037, by rfl⟩ : syracuseStep 933533 = 350075) (by norm_num)
theorem B704173 : Blo 413771 704173 := bbase (se 3 (by rfl) ⟨132032, by rfl⟩ : syracuseStep 704173 = 264065) (by norm_num)
theorem B933605 : Blo 413771 933605 := bbase (se 4 (by rfl) ⟨87525, by rfl⟩ : syracuseStep 933605 = 175051) (by norm_num)
theorem B704261 : Blo 413771 704261 := bbase (se 4 (by rfl) ⟨66024, by rfl⟩ : syracuseStep 704261 = 132049) (by norm_num)
theorem B933677 : Blo 413771 933677 := bbase (se 3 (by rfl) ⟨175064, by rfl⟩ : syracuseStep 933677 = 350129) (by norm_num)
theorem B933749 : Blo 413771 933749 := bbase (se 5 (by rfl) ⟨43769, by rfl⟩ : syracuseStep 933749 = 87539) (by norm_num)
theorem B704389 : Blo 413771 704389 := bbase (se 4 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 704389 = 132073) (by norm_num)
theorem B999317 : Blo 413771 999317 := bbase (se 6 (by rfl) ⟨23421, by rfl⟩ : syracuseStep 999317 = 46843) (by norm_num)
theorem B933821 : Blo 413771 933821 := bbase (se 3 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 933821 = 350183) (by norm_num)
theorem B704477 : Blo 413771 704477 := bbase (se 3 (by rfl) ⟨132089, by rfl⟩ : syracuseStep 704477 = 264179) (by norm_num)
theorem B933893 : Blo 413771 933893 := bbase (se 4 (by rfl) ⟨87552, by rfl⟩ : syracuseStep 933893 = 175105) (by norm_num)
theorem B933965 : Blo 413771 933965 := bbase (se 3 (by rfl) ⟨175118, by rfl⟩ : syracuseStep 933965 = 350237) (by norm_num)
theorem B704605 : Blo 413771 704605 := bbase (se 3 (by rfl) ⟨132113, by rfl⟩ : syracuseStep 704605 = 264227) (by norm_num)
theorem B508025 : Blo 413771 508025 := bbase (se 2 (by rfl) ⟨190509, by rfl⟩ : syracuseStep 508025 = 381019) (by norm_num)
theorem B934037 : Blo 413771 934037 := bbase (se 6 (by rfl) ⟨21891, by rfl⟩ : syracuseStep 934037 = 43783) (by norm_num)
theorem B704693 : Blo 413771 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B934109 : Blo 413771 934109 := bbase (se 3 (by rfl) ⟨175145, by rfl⟩ : syracuseStep 934109 = 350291) (by norm_num)
theorem B934181 : Blo 413771 934181 := bbase (se 4 (by rfl) ⟨87579, by rfl⟩ : syracuseStep 934181 = 175159) (by norm_num)
theorem B704821 : Blo 413771 704821 := bbase (se 5 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 704821 = 66077) (by norm_num)
theorem B1818949 : Blo 413771 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B442693 : Blo 413771 442693 := bbase (se 4 (by rfl) ⟨41502, by rfl⟩ : syracuseStep 442693 = 83005) (by norm_num)
theorem B934253 : Blo 413771 934253 := bbase (se 3 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 934253 = 350345) (by norm_num)
theorem B442765 : Blo 413771 442765 := bbase (se 3 (by rfl) ⟨83018, by rfl⟩ : syracuseStep 442765 = 166037) (by norm_num)
theorem B704909 : Blo 413771 704909 := bbase (se 3 (by rfl) ⟨132170, by rfl⟩ : syracuseStep 704909 = 264341) (by norm_num)
theorem B475553 : Blo 413771 475553 := bbase (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) (by norm_num)
theorem B934325 : Blo 413771 934325 := bbase (se 5 (by rfl) ⟨43796, by rfl⟩ : syracuseStep 934325 = 87593) (by norm_num)
theorem B934397 : Blo 413771 934397 := bbase (se 3 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 934397 = 350399) (by norm_num)
theorem B442945 : Blo 413771 442945 := bbase (se 2 (by rfl) ⟨166104, by rfl⟩ : syracuseStep 442945 = 332209) (by norm_num)
theorem B934469 : Blo 413771 934469 := bbase (se 4 (by rfl) ⟨87606, by rfl⟩ : syracuseStep 934469 = 175213) (by norm_num)
theorem B1688197 : Blo 413771 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B934541 : Blo 413771 934541 := bbase (se 3 (by rfl) ⟨175226, by rfl⟩ : syracuseStep 934541 = 350453) (by norm_num)
theorem B934613 : Blo 413771 934613 := bbase (se 7 (by rfl) ⟨10952, by rfl⟩ : syracuseStep 934613 = 21905) (by norm_num)
theorem B2114261 : Blo 413771 2114261 := bbase (se 7 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 2114261 = 49553) (by norm_num)
theorem B934685 : Blo 413771 934685 := bbase (se 3 (by rfl) ⟨175253, by rfl⟩ : syracuseStep 934685 = 350507) (by norm_num)
theorem B1491797 : Blo 413771 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B934757 : Blo 413771 934757 := bbase (se 4 (by rfl) ⟨87633, by rfl⟩ : syracuseStep 934757 = 175267) (by norm_num)
theorem B934829 : Blo 413771 934829 := bbase (se 3 (by rfl) ⟨175280, by rfl⟩ : syracuseStep 934829 = 350561) (by norm_num)
theorem B1262549 : Blo 413771 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B934901 : Blo 413771 934901 := bbase (se 5 (by rfl) ⟨43823, by rfl⟩ : syracuseStep 934901 = 87647) (by norm_num)
theorem B443389 : Blo 413771 443389 := bbase (se 3 (by rfl) ⟨83135, by rfl⟩ : syracuseStep 443389 = 166271) (by norm_num)
theorem B934973 : Blo 413771 934973 := bbase (se 3 (by rfl) ⟨175307, by rfl⟩ : syracuseStep 934973 = 350615) (by norm_num)
theorem B443513 : Blo 413771 443513 := bbase (se 2 (by rfl) ⟨166317, by rfl⟩ : syracuseStep 443513 = 332635) (by norm_num)
theorem B935045 : Blo 413771 935045 := bbase (se 4 (by rfl) ⟨87660, by rfl⟩ : syracuseStep 935045 = 175321) (by norm_num)
theorem B935117 : Blo 413771 935117 := bbase (se 3 (by rfl) ⟨175334, by rfl⟩ : syracuseStep 935117 = 350669) (by norm_num)
theorem B935189 : Blo 413771 935189 := bbase (se 6 (by rfl) ⟨21918, by rfl⟩ : syracuseStep 935189 = 43837) (by norm_num)
theorem B935261 : Blo 413771 935261 := bbase (se 3 (by rfl) ⟨175361, by rfl⟩ : syracuseStep 935261 = 350723) (by norm_num)
theorem B1328501 : Blo 413771 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B443765 : Blo 413771 443765 := bbase (se 5 (by rfl) ⟨20801, by rfl⟩ : syracuseStep 443765 = 41603) (by norm_num)
theorem B935333 : Blo 413771 935333 := bbase (se 4 (by rfl) ⟨87687, by rfl⟩ : syracuseStep 935333 = 175375) (by norm_num)
theorem B935405 : Blo 413771 935405 := bbase (se 3 (by rfl) ⟨175388, by rfl⟩ : syracuseStep 935405 = 350777) (by norm_num)
theorem B2672149 : Blo 413771 2672149 := bbase (se 6 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 2672149 = 125257) (by norm_num)
theorem B935477 : Blo 413771 935477 := bbase (se 5 (by rfl) ⟨43850, by rfl⟩ : syracuseStep 935477 = 87701) (by norm_num)
theorem B935549 : Blo 413771 935549 := bbase (se 3 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 935549 = 350831) (by norm_num)
theorem B935621 : Blo 413771 935621 := bbase (se 4 (by rfl) ⟨87714, by rfl⟩ : syracuseStep 935621 = 175429) (by norm_num)
theorem B14436053 : Blo 413771 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B935693 : Blo 413771 935693 := bbase (se 3 (by rfl) ⟨175442, by rfl⟩ : syracuseStep 935693 = 350885) (by norm_num)
theorem B444209 : Blo 413771 444209 := bbase (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) (by norm_num)
theorem B935765 : Blo 413771 935765 := bbase (se 9 (by rfl) ⟨2741, by rfl⟩ : syracuseStep 935765 = 5483) (by norm_num)
theorem B935837 : Blo 413771 935837 := bbase (se 3 (by rfl) ⟨175469, by rfl⟩ : syracuseStep 935837 = 350939) (by norm_num)
theorem B935909 : Blo 413771 935909 := bbase (se 4 (by rfl) ⟨87741, by rfl⟩ : syracuseStep 935909 = 175483) (by norm_num)
theorem B444457 : Blo 413771 444457 := bbase (se 2 (by rfl) ⟨166671, by rfl⟩ : syracuseStep 444457 = 333343) (by norm_num)
theorem B935981 : Blo 413771 935981 := bbase (se 3 (by rfl) ⟨175496, by rfl⟩ : syracuseStep 935981 = 350993) (by norm_num)
theorem B3557429 : Blo 413771 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B936053 : Blo 413771 936053 := bbase (se 5 (by rfl) ⟨43877, by rfl⟩ : syracuseStep 936053 = 87755) (by norm_num)
theorem B936125 : Blo 413771 936125 := bbase (se 3 (by rfl) ⟨175523, by rfl⟩ : syracuseStep 936125 = 351047) (by norm_num)
theorem B2017493 : Blo 413771 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B1427701 : Blo 413771 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B936197 : Blo 413771 936197 := bbase (se 4 (by rfl) ⟨87768, by rfl⟩ : syracuseStep 936197 = 175537) (by norm_num)
theorem B1001749 : Blo 413771 1001749 := bbase (se 6 (by rfl) ⟨23478, by rfl⟩ : syracuseStep 1001749 = 46957) (by norm_num)
theorem B936269 : Blo 413771 936269 := bbase (se 3 (by rfl) ⟨175550, by rfl⟩ : syracuseStep 936269 = 351101) (by norm_num)
theorem B936341 : Blo 413771 936341 := bbase (se 6 (by rfl) ⟨21945, by rfl⟩ : syracuseStep 936341 = 43891) (by norm_num)
theorem B936413 : Blo 413771 936413 := bbase (se 3 (by rfl) ⟨175577, by rfl⟩ : syracuseStep 936413 = 351155) (by norm_num)
theorem B444901 : Blo 413771 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B1493525 : Blo 413771 1493525 := bbase (se 6 (by rfl) ⟨35004, by rfl⟩ : syracuseStep 1493525 = 70009) (by norm_num)
theorem B444961 : Blo 413771 444961 := bbase (se 2 (by rfl) ⟨166860, by rfl⟩ : syracuseStep 444961 = 333721) (by norm_num)
theorem B936485 : Blo 413771 936485 := bbase (se 4 (by rfl) ⟨87795, by rfl⟩ : syracuseStep 936485 = 175591) (by norm_num)
theorem B936557 : Blo 413771 936557 := bbase (se 3 (by rfl) ⟨175604, by rfl⟩ : syracuseStep 936557 = 351209) (by norm_num)
theorem B936629 : Blo 413771 936629 := bbase (se 5 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 936629 = 87809) (by norm_num)
theorem B936701 : Blo 413771 936701 := bbase (se 3 (by rfl) ⟨175631, by rfl⟩ : syracuseStep 936701 = 351263) (by norm_num)
theorem B936773 : Blo 413771 936773 := bbase (se 4 (by rfl) ⟨87822, by rfl⟩ : syracuseStep 936773 = 175645) (by norm_num)
theorem B445277 : Blo 413771 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B1002365 : Blo 413771 1002365 := bbase (se 3 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 1002365 = 375887) (by norm_num)
theorem B936845 : Blo 413771 936845 := bbase (se 3 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 936845 = 351317) (by norm_num)
theorem B576437 : Blo 413771 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B936917 : Blo 413771 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B936989 : Blo 413771 936989 := bbase (se 3 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 936989 = 351371) (by norm_num)
theorem B1002565 : Blo 413771 1002565 := bbase (se 4 (by rfl) ⟨93990, by rfl⟩ : syracuseStep 1002565 = 187981) (by norm_num)
theorem B937061 : Blo 413771 937061 := bbase (se 4 (by rfl) ⟨87849, by rfl⟩ : syracuseStep 937061 = 175699) (by norm_num)
theorem B937133 : Blo 413771 937133 := bbase (se 3 (by rfl) ⟨175712, by rfl⟩ : syracuseStep 937133 = 351425) (by norm_num)
theorem B2837749 : Blo 413771 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B937205 : Blo 413771 937205 := bbase (se 5 (by rfl) ⟨43931, by rfl⟩ : syracuseStep 937205 = 87863) (by norm_num)
theorem B445721 : Blo 413771 445721 := bbase (se 2 (by rfl) ⟨167145, by rfl⟩ : syracuseStep 445721 = 334291) (by norm_num)
theorem B937277 : Blo 413771 937277 := bbase (se 3 (by rfl) ⟨175739, by rfl⟩ : syracuseStep 937277 = 351479) (by norm_num)
theorem B445781 : Blo 413771 445781 := bbase (se 11 (by rfl) ⟨326, by rfl⟩ : syracuseStep 445781 = 653) (by norm_num)
theorem B839005 : Blo 413771 839005 := bbase (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) (by norm_num)
theorem B937349 : Blo 413771 937349 := bbase (se 4 (by rfl) ⟨87876, by rfl⟩ : syracuseStep 937349 = 175753) (by norm_num)
theorem B937421 : Blo 413771 937421 := bbase (se 3 (by rfl) ⟨175766, by rfl⟩ : syracuseStep 937421 = 351533) (by norm_num)
theorem B445909 : Blo 413771 445909 := bbase (se 7 (by rfl) ⟨5225, by rfl⟩ : syracuseStep 445909 = 10451) (by norm_num)
theorem B937493 : Blo 413771 937493 := bbase (se 6 (by rfl) ⟨21972, by rfl⟩ : syracuseStep 937493 = 43945) (by norm_num)
theorem B937565 : Blo 413771 937565 := bbase (se 3 (by rfl) ⟨175793, by rfl⟩ : syracuseStep 937565 = 351587) (by norm_num)
theorem B937637 : Blo 413771 937637 := bbase (se 4 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 937637 = 175807) (by norm_num)
theorem B937709 : Blo 413771 937709 := bbase (se 3 (by rfl) ⟨175820, by rfl⟩ : syracuseStep 937709 = 351641) (by norm_num)
theorem B708349 : Blo 413771 708349 := bbase (se 3 (by rfl) ⟨132815, by rfl⟩ : syracuseStep 708349 = 265631) (by norm_num)
theorem B937781 : Blo 413771 937781 := bbase (se 5 (by rfl) ⟨43958, by rfl⟩ : syracuseStep 937781 = 87917) (by norm_num)
theorem B5820245 : Blo 413771 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B1003373 : Blo 413771 1003373 := bbase (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) (by norm_num)
theorem B937853 : Blo 413771 937853 := bbase (se 3 (by rfl) ⟨175847, by rfl⟩ : syracuseStep 937853 = 351695) (by norm_num)
theorem B937925 : Blo 413771 937925 := bbase (se 4 (by rfl) ⟨87930, by rfl⟩ : syracuseStep 937925 = 175861) (by norm_num)
theorem B1396709 : Blo 413771 1396709 := bbase (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) (by norm_num)
theorem B937997 : Blo 413771 937997 := bbase (se 3 (by rfl) ⟨175874, by rfl⟩ : syracuseStep 937997 = 351749) (by norm_num)
theorem B479305 : Blo 413771 479305 := bbase (se 2 (by rfl) ⟨179739, by rfl⟩ : syracuseStep 479305 = 359479) (by norm_num)
theorem B938069 : Blo 413771 938069 := bbase (se 8 (by rfl) ⟨5496, by rfl⟩ : syracuseStep 938069 = 10993) (by norm_num)
theorem B938141 : Blo 413771 938141 := bbase (se 3 (by rfl) ⟨175901, by rfl⟩ : syracuseStep 938141 = 351803) (by norm_num)
theorem B938213 : Blo 413771 938213 := bbase (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) (by norm_num)
theorem B938285 : Blo 413771 938285 := bbase (se 3 (by rfl) ⟨175928, by rfl⟩ : syracuseStep 938285 = 351857) (by norm_num)
theorem B938357 : Blo 413771 938357 := bbase (se 5 (by rfl) ⟨43985, by rfl⟩ : syracuseStep 938357 = 87971) (by norm_num)
theorem B840061 : Blo 413771 840061 := bbase (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) (by norm_num)
theorem B676237 : Blo 413771 676237 := bbase (se 3 (by rfl) ⟨126794, by rfl⟩ : syracuseStep 676237 = 253589) (by norm_num)
theorem B1397141 : Blo 413771 1397141 := bbase (se 6 (by rfl) ⟨32745, by rfl⟩ : syracuseStep 1397141 = 65491) (by norm_num)
theorem B938429 : Blo 413771 938429 := bbase (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) (by norm_num)
theorem B938501 : Blo 413771 938501 := bbase (se 4 (by rfl) ⟨87984, by rfl⟩ : syracuseStep 938501 = 175969) (by norm_num)
theorem B1921589 : Blo 413771 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B938573 : Blo 413771 938573 := bbase (se 3 (by rfl) ⟨175982, by rfl⟩ : syracuseStep 938573 = 351965) (by norm_num)
theorem B938645 : Blo 413771 938645 := bbase (se 6 (by rfl) ⟨21999, by rfl⟩ : syracuseStep 938645 = 43999) (by norm_num)
theorem B938717 : Blo 413771 938717 := bbase (se 3 (by rfl) ⟨176009, by rfl⟩ : syracuseStep 938717 = 352019) (by norm_num)
theorem B938789 : Blo 413771 938789 := bbase (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) (by norm_num)
theorem B1397573 : Blo 413771 1397573 := bbase (se 4 (by rfl) ⟨131022, by rfl⟩ : syracuseStep 1397573 = 262045) (by norm_num)
theorem B938861 : Blo 413771 938861 := bbase (se 3 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 938861 = 352073) (by norm_num)
theorem B938933 : Blo 413771 938933 := bbase (se 5 (by rfl) ⟨44012, by rfl⟩ : syracuseStep 938933 = 88025) (by norm_num)
theorem B939005 : Blo 413771 939005 := bbase (se 3 (by rfl) ⟨176063, by rfl⟩ : syracuseStep 939005 = 352127) (by norm_num)
theorem B1332293 : Blo 413771 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B939077 : Blo 413771 939077 := bbase (se 4 (by rfl) ⟨88038, by rfl⟩ : syracuseStep 939077 = 176077) (by norm_num)
theorem B939149 : Blo 413771 939149 := bbase (se 3 (by rfl) ⟨176090, by rfl⟩ : syracuseStep 939149 = 352181) (by norm_num)
theorem B939221 : Blo 413771 939221 := bbase (se 7 (by rfl) ⟨11006, by rfl⟩ : syracuseStep 939221 = 22013) (by norm_num)
theorem B1398005 : Blo 413771 1398005 := bbase (se 5 (by rfl) ⟨65531, by rfl⟩ : syracuseStep 1398005 = 131063) (by norm_num)
theorem B939293 : Blo 413771 939293 := bbase (se 3 (by rfl) ⟨176117, by rfl⟩ : syracuseStep 939293 = 352235) (by norm_num)
theorem B939365 : Blo 413771 939365 := bbase (se 4 (by rfl) ⟨88065, by rfl⟩ : syracuseStep 939365 = 176131) (by norm_num)
theorem B939437 : Blo 413771 939437 := bbase (se 3 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 939437 = 352289) (by norm_num)
theorem B2840021 : Blo 413771 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B939509 : Blo 413771 939509 := bbase (se 5 (by rfl) ⟨44039, by rfl⟩ : syracuseStep 939509 = 88079) (by norm_num)
theorem B939581 : Blo 413771 939581 := bbase (se 3 (by rfl) ⟨176171, by rfl⟩ : syracuseStep 939581 = 352343) (by norm_num)
theorem B3200629 : Blo 413771 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B1070725 : Blo 413771 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B939653 : Blo 413771 939653 := bbase (se 4 (by rfl) ⟨88092, by rfl⟩ : syracuseStep 939653 = 176185) (by norm_num)
theorem B1398437 : Blo 413771 1398437 := bbase (se 4 (by rfl) ⟨131103, by rfl⟩ : syracuseStep 1398437 = 262207) (by norm_num)
theorem B939725 : Blo 413771 939725 := bbase (se 3 (by rfl) ⟨176198, by rfl⟩ : syracuseStep 939725 = 352397) (by norm_num)
theorem B939797 : Blo 413771 939797 := bbase (se 6 (by rfl) ⟨22026, by rfl⟩ : syracuseStep 939797 = 44053) (by norm_num)
theorem B939869 : Blo 413771 939869 := bbase (se 3 (by rfl) ⟨176225, by rfl⟩ : syracuseStep 939869 = 352451) (by norm_num)
theorem B939941 : Blo 413771 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B1333205 : Blo 413771 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B1398869 : Blo 413771 1398869 := bbase (se 8 (by rfl) ⟨8196, by rfl⟩ : syracuseStep 1398869 = 16393) (by norm_num)
theorem B841853 : Blo 413771 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B3365333 : Blo 413771 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B1399301 : Blo 413771 1399301 := bbase (se 4 (by rfl) ⟨131184, by rfl⟩ : syracuseStep 1399301 = 262369) (by norm_num)
theorem B711197 : Blo 413771 711197 := bbase (se 3 (by rfl) ⟨133349, by rfl⟩ : syracuseStep 711197 = 266699) (by norm_num)
theorem B6085205 : Blo 413771 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B3005333 : Blo 413771 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B1399733 : Blo 413771 1399733 := bbase (se 5 (by rfl) ⟨65612, by rfl⟩ : syracuseStep 1399733 = 131225) (by norm_num)
theorem B3169205 : Blo 413771 3169205 := bbase (se 5 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 3169205 = 297113) (by norm_num)
theorem B1334549 : Blo 413771 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B843061 : Blo 413771 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B1400165 : Blo 413771 1400165 := bbase (se 4 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 1400165 = 262531) (by norm_num)
theorem B1400597 : Blo 413771 1400597 := bbase (se 6 (by rfl) ⟨32826, by rfl⟩ : syracuseStep 1400597 = 65653) (by norm_num)
theorem B745661 : Blo 413771 745661 := bbase (se 3 (by rfl) ⟨139811, by rfl⟩ : syracuseStep 745661 = 279623) (by norm_num)
theorem B1401029 : Blo 413771 1401029 := bbase (se 4 (by rfl) ⟨131346, by rfl⟩ : syracuseStep 1401029 = 262693) (by norm_num)
theorem B1401461 : Blo 413771 1401461 := bbase (se 5 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 1401461 = 131387) (by norm_num)
theorem B1335973 : Blo 413771 1335973 := bbase (se 4 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 1335973 = 250495) (by norm_num)
theorem B2253653 : Blo 413771 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B2253781 : Blo 413771 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B1401893 : Blo 413771 1401893 := bbase (se 4 (by rfl) ⟨131427, by rfl⟩ : syracuseStep 1401893 = 262855) (by norm_num)
theorem B844877 : Blo 413771 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B451681 : Blo 413771 451681 := bbase (se 2 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 451681 = 338761) (by norm_num)
theorem B1500389 : Blo 413771 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B1402325 : Blo 413771 1402325 := bbase (se 7 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 1402325 = 32867) (by norm_num)
theorem B419629 : Blo 413771 419629 := bbase (se 3 (by rfl) ⟨78680, by rfl⟩ : syracuseStep 419629 = 157361) (by norm_num)
theorem B419665 : Blo 413771 419665 := bbase (se 2 (by rfl) ⟨157374, by rfl⟩ : syracuseStep 419665 = 314749) (by norm_num)
theorem B747397 : Blo 413771 747397 := bbase (se 4 (by rfl) ⟨70068, by rfl⟩ : syracuseStep 747397 = 140137) (by norm_num)
theorem B1402757 : Blo 413771 1402757 := bbase (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) (by norm_num)
theorem B1337573 : Blo 413771 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B1403189 : Blo 413771 1403189 := bbase (se 5 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 1403189 = 131549) (by norm_num)
theorem B1993349 : Blo 413771 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B1501829 : Blo 413771 1501829 := bbase (se 4 (by rfl) ⟨140796, by rfl⟩ : syracuseStep 1501829 = 281593) (by norm_num)
theorem B748205 : Blo 413771 748205 := bbase (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) (by norm_num)
theorem B1403621 : Blo 413771 1403621 := bbase (se 4 (by rfl) ⟨131589, by rfl⟩ : syracuseStep 1403621 = 263179) (by norm_num)
theorem B846677 : Blo 413771 846677 := bbase (se 9 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 846677 = 4961) (by norm_num)
theorem B1600469 : Blo 413771 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B519313 : Blo 413771 519313 := bbase (se 2 (by rfl) ⟨194742, by rfl⟩ : syracuseStep 519313 = 389485) (by norm_num)
theorem B1404053 : Blo 413771 1404053 := bbase (se 6 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 1404053 = 65815) (by norm_num)
theorem B421133 : Blo 413771 421133 := bbase (se 3 (by rfl) ⟨78962, by rfl⟩ : syracuseStep 421133 = 157925) (by norm_num)
theorem B1994021 : Blo 413771 1994021 := bbase (se 4 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 1994021 = 373879) (by norm_num)
theorem B1011061 : Blo 413771 1011061 := bbase (se 5 (by rfl) ⟨47393, by rfl⟩ : syracuseStep 1011061 = 94787) (by norm_num)
theorem B1404485 : Blo 413771 1404485 := bbase (se 4 (by rfl) ⟨131670, by rfl⟩ : syracuseStep 1404485 = 263341) (by norm_num)
theorem B421741 : Blo 413771 421741 := bbase (se 3 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 421741 = 158153) (by norm_num)
theorem B1896373 : Blo 413771 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B1503157 : Blo 413771 1503157 := bbase (se 5 (by rfl) ⟨70460, by rfl⟩ : syracuseStep 1503157 = 140921) (by norm_num)
theorem B1404917 : Blo 413771 1404917 := bbase (se 5 (by rfl) ⟨65855, by rfl⟩ : syracuseStep 1404917 = 131711) (by norm_num)
theorem B1929205 : Blo 413771 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B946237 : Blo 413771 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B1011989 : Blo 413771 1011989 := bbase (se 6 (by rfl) ⟨23718, by rfl⟩ : syracuseStep 1011989 = 47437) (by norm_num)
theorem B1405349 : Blo 413771 1405349 := bbase (se 4 (by rfl) ⟨131751, by rfl⟩ : syracuseStep 1405349 = 263503) (by norm_num)
theorem B3535285 : Blo 413771 3535285 := bbase (se 5 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 3535285 = 331433) (by norm_num)
theorem B2126341 : Blo 413771 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B3600949 : Blo 413771 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B1504021 : Blo 413771 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B750389 : Blo 413771 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B1405781 : Blo 413771 1405781 := bbase (se 9 (by rfl) ⟨4118, by rfl⟩ : syracuseStep 1405781 = 8237) (by norm_num)
theorem B1504469 : Blo 413771 1504469 := bbase (se 7 (by rfl) ⟨17630, by rfl⟩ : syracuseStep 1504469 = 35261) (by norm_num)
theorem B1406213 : Blo 413771 1406213 := bbase (se 4 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 1406213 = 263665) (by norm_num)
theorem B1504597 : Blo 413771 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B750973 : Blo 413771 750973 := bbase (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) (by norm_num)
theorem B5338709 : Blo 413771 5338709 := bbase (se 8 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 5338709 = 62563) (by norm_num)
theorem B1406645 : Blo 413771 1406645 := bbase (se 5 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 1406645 = 131873) (by norm_num)
theorem B2094821 : Blo 413771 2094821 := bbase (se 4 (by rfl) ⟨196389, by rfl⟩ : syracuseStep 2094821 = 392779) (by norm_num)
theorem B1079021 : Blo 413771 1079021 := bbase (se 3 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 1079021 = 404633) (by norm_num)
theorem B5699413 : Blo 413771 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B948181 : Blo 413771 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B4716629 : Blo 413771 4716629 := bbase (se 8 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 4716629 = 55273) (by norm_num)
theorem B1407077 : Blo 413771 1407077 := bbase (se 4 (by rfl) ⟨131913, by rfl⟩ : syracuseStep 1407077 = 263827) (by norm_num)
theorem B1767541 : Blo 413771 1767541 := bbase (se 5 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 1767541 = 165707) (by norm_num)
theorem B620669 : Blo 413771 620669 := bbase (se 3 (by rfl) ⟨116375, by rfl⟩ : syracuseStep 620669 = 232751) (by norm_num)
theorem B620693 : Blo 413771 620693 := bbase (se 6 (by rfl) ⟨14547, by rfl⟩ : syracuseStep 620693 = 29095) (by norm_num)
theorem B620717 : Blo 413771 620717 := bbase (se 3 (by rfl) ⟨116384, by rfl⟩ : syracuseStep 620717 = 232769) (by norm_num)
theorem B620741 : Blo 413771 620741 := bbase (se 4 (by rfl) ⟨58194, by rfl⟩ : syracuseStep 620741 = 116389) (by norm_num)
theorem B620765 : Blo 413771 620765 := bbase (se 3 (by rfl) ⟨116393, by rfl⟩ : syracuseStep 620765 = 232787) (by norm_num)
theorem B620789 : Blo 413771 620789 := bbase (se 5 (by rfl) ⟨29099, by rfl⟩ : syracuseStep 620789 = 58199) (by norm_num)
theorem B620813 : Blo 413771 620813 := bbase (se 3 (by rfl) ⟨116402, by rfl⟩ : syracuseStep 620813 = 232805) (by norm_num)
theorem B620837 : Blo 413771 620837 := bbase (se 4 (by rfl) ⟨58203, by rfl⟩ : syracuseStep 620837 = 116407) (by norm_num)
theorem B620861 : Blo 413771 620861 := bbase (se 3 (by rfl) ⟨116411, by rfl⟩ : syracuseStep 620861 = 232823) (by norm_num)
theorem B620885 : Blo 413771 620885 := bbase (se 10 (by rfl) ⟨909, by rfl⟩ : syracuseStep 620885 = 1819) (by norm_num)
theorem B620909 : Blo 413771 620909 := bbase (se 3 (by rfl) ⟨116420, by rfl⟩ : syracuseStep 620909 = 232841) (by norm_num)
theorem B3537269 : Blo 413771 3537269 := bbase (se 5 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 3537269 = 331619) (by norm_num)
theorem B620933 : Blo 413771 620933 := bbase (se 4 (by rfl) ⟨58212, by rfl⟩ : syracuseStep 620933 = 116425) (by norm_num)
theorem B2521493 : Blo 413771 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B620957 : Blo 413771 620957 := bbase (se 3 (by rfl) ⟨116429, by rfl⟩ : syracuseStep 620957 = 232859) (by norm_num)
theorem B620981 : Blo 413771 620981 := bbase (se 5 (by rfl) ⟨29108, by rfl⟩ : syracuseStep 620981 = 58217) (by norm_num)
theorem B621005 : Blo 413771 621005 := bbase (se 3 (by rfl) ⟨116438, by rfl⟩ : syracuseStep 621005 = 232877) (by norm_num)
theorem B621029 : Blo 413771 621029 := bbase (se 4 (by rfl) ⟨58221, by rfl⟩ : syracuseStep 621029 = 116443) (by norm_num)
theorem B621053 : Blo 413771 621053 := bbase (se 3 (by rfl) ⟨116447, by rfl⟩ : syracuseStep 621053 = 232895) (by norm_num)
theorem B752141 : Blo 413771 752141 := bbase (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) (by norm_num)
theorem B621077 : Blo 413771 621077 := bbase (se 6 (by rfl) ⟨14556, by rfl⟩ : syracuseStep 621077 = 29113) (by norm_num)
theorem B1407509 : Blo 413771 1407509 := bbase (se 6 (by rfl) ⟨32988, by rfl⟩ : syracuseStep 1407509 = 65977) (by norm_num)
theorem B621101 : Blo 413771 621101 := bbase (se 3 (by rfl) ⟨116456, by rfl⟩ : syracuseStep 621101 = 232913) (by norm_num)
theorem B621125 : Blo 413771 621125 := bbase (se 4 (by rfl) ⟨58230, by rfl⟩ : syracuseStep 621125 = 116461) (by norm_num)
theorem B621149 : Blo 413771 621149 := bbase (se 3 (by rfl) ⟨116465, by rfl⟩ : syracuseStep 621149 = 232931) (by norm_num)
theorem B621173 : Blo 413771 621173 := bbase (se 5 (by rfl) ⟨29117, by rfl⟩ : syracuseStep 621173 = 58235) (by norm_num)
theorem B621197 : Blo 413771 621197 := bbase (se 3 (by rfl) ⟨116474, by rfl⟩ : syracuseStep 621197 = 232949) (by norm_num)
theorem B5307029 : Blo 413771 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B621221 : Blo 413771 621221 := bbase (se 4 (by rfl) ⟨58239, by rfl⟩ : syracuseStep 621221 = 116479) (by norm_num)
theorem B621245 : Blo 413771 621245 := bbase (se 3 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 621245 = 232967) (by norm_num)
theorem B621269 : Blo 413771 621269 := bbase (se 7 (by rfl) ⟨7280, by rfl⟩ : syracuseStep 621269 = 14561) (by norm_num)
theorem B621293 : Blo 413771 621293 := bbase (se 3 (by rfl) ⟨116492, by rfl⟩ : syracuseStep 621293 = 232985) (by norm_num)
theorem B621317 : Blo 413771 621317 := bbase (se 4 (by rfl) ⟨58248, by rfl⟩ : syracuseStep 621317 = 116497) (by norm_num)
theorem B621341 : Blo 413771 621341 := bbase (se 3 (by rfl) ⟨116501, by rfl⟩ : syracuseStep 621341 = 233003) (by norm_num)
theorem B621365 : Blo 413771 621365 := bbase (se 5 (by rfl) ⟨29126, by rfl⟩ : syracuseStep 621365 = 58253) (by norm_num)
theorem B621389 : Blo 413771 621389 := bbase (se 3 (by rfl) ⟨116510, by rfl⟩ : syracuseStep 621389 = 233021) (by norm_num)
theorem B621413 : Blo 413771 621413 := bbase (se 4 (by rfl) ⟨58257, by rfl⟩ : syracuseStep 621413 = 116515) (by norm_num)
theorem B621437 : Blo 413771 621437 := bbase (se 3 (by rfl) ⟨116519, by rfl⟩ : syracuseStep 621437 = 233039) (by norm_num)
theorem B621461 : Blo 413771 621461 := bbase (se 6 (by rfl) ⟨14565, by rfl⟩ : syracuseStep 621461 = 29131) (by norm_num)
theorem B621485 : Blo 413771 621485 := bbase (se 3 (by rfl) ⟨116528, by rfl⟩ : syracuseStep 621485 = 233057) (by norm_num)
theorem B621509 : Blo 413771 621509 := bbase (se 4 (by rfl) ⟨58266, by rfl⟩ : syracuseStep 621509 = 116533) (by norm_num)
theorem B1407941 : Blo 413771 1407941 := bbase (se 4 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 1407941 = 263989) (by norm_num)
theorem B752581 : Blo 413771 752581 := bbase (se 4 (by rfl) ⟨70554, by rfl⟩ : syracuseStep 752581 = 141109) (by norm_num)
theorem B621533 : Blo 413771 621533 := bbase (se 3 (by rfl) ⟨116537, by rfl⟩ : syracuseStep 621533 = 233075) (by norm_num)
theorem B2096117 : Blo 413771 2096117 := bbase (se 5 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 2096117 = 196511) (by norm_num)
theorem B621557 : Blo 413771 621557 := bbase (se 5 (by rfl) ⟨29135, by rfl⟩ : syracuseStep 621557 = 58271) (by norm_num)
theorem B1571845 : Blo 413771 1571845 := bbase (se 4 (by rfl) ⟨147360, by rfl⟩ : syracuseStep 1571845 = 294721) (by norm_num)
theorem B687109 : Blo 413771 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B752645 : Blo 413771 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B621581 : Blo 413771 621581 := bbase (se 3 (by rfl) ⟨116546, by rfl⟩ : syracuseStep 621581 = 233093) (by norm_num)
theorem B621605 : Blo 413771 621605 := bbase (se 4 (by rfl) ⟨58275, by rfl⟩ : syracuseStep 621605 = 116551) (by norm_num)
theorem B1047613 : Blo 413771 1047613 := bbase (se 3 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 1047613 = 392855) (by norm_num)
theorem B621629 : Blo 413771 621629 := bbase (se 3 (by rfl) ⟨116555, by rfl⟩ : syracuseStep 621629 = 233111) (by norm_num)
theorem B621653 : Blo 413771 621653 := bbase (se 8 (by rfl) ⟨3642, by rfl⟩ : syracuseStep 621653 = 7285) (by norm_num)
theorem B1178725 : Blo 413771 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B621677 : Blo 413771 621677 := bbase (se 3 (by rfl) ⟨116564, by rfl⟩ : syracuseStep 621677 = 233129) (by norm_num)
theorem B621701 : Blo 413771 621701 := bbase (se 4 (by rfl) ⟨58284, by rfl⟩ : syracuseStep 621701 = 116569) (by norm_num)
theorem B621725 : Blo 413771 621725 := bbase (se 3 (by rfl) ⟨116573, by rfl⟩ : syracuseStep 621725 = 233147) (by norm_num)
theorem B1047725 : Blo 413771 1047725 := bbase (se 3 (by rfl) ⟨196448, by rfl⟩ : syracuseStep 1047725 = 392897) (by norm_num)
theorem B621749 : Blo 413771 621749 := bbase (se 5 (by rfl) ⟨29144, by rfl⟩ : syracuseStep 621749 = 58289) (by norm_num)
theorem B621773 : Blo 413771 621773 := bbase (se 3 (by rfl) ⟨116582, by rfl⟩ : syracuseStep 621773 = 233165) (by norm_num)
theorem B621797 : Blo 413771 621797 := bbase (se 4 (by rfl) ⟨58293, by rfl⟩ : syracuseStep 621797 = 116587) (by norm_num)
theorem B621821 : Blo 413771 621821 := bbase (se 3 (by rfl) ⟨116591, by rfl⟩ : syracuseStep 621821 = 233183) (by norm_num)
theorem B621845 : Blo 413771 621845 := bbase (se 6 (by rfl) ⟨14574, by rfl⟩ : syracuseStep 621845 = 29149) (by norm_num)
theorem B621869 : Blo 413771 621869 := bbase (se 3 (by rfl) ⟨116600, by rfl⟩ : syracuseStep 621869 = 233201) (by norm_num)
theorem B1572149 : Blo 413771 1572149 := bbase (se 5 (by rfl) ⟨73694, by rfl⟩ : syracuseStep 1572149 = 147389) (by norm_num)
theorem B621893 : Blo 413771 621893 := bbase (se 4 (by rfl) ⟨58302, by rfl⟩ : syracuseStep 621893 = 116605) (by norm_num)
theorem B1604933 : Blo 413771 1604933 := bbase (se 4 (by rfl) ⟨150462, by rfl⟩ : syracuseStep 1604933 = 300925) (by norm_num)
theorem B621917 : Blo 413771 621917 := bbase (se 3 (by rfl) ⟨116609, by rfl⟩ : syracuseStep 621917 = 233219) (by norm_num)
theorem B1899877 : Blo 413771 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B1047917 : Blo 413771 1047917 := bbase (se 3 (by rfl) ⟨196484, by rfl⟩ : syracuseStep 1047917 = 392969) (by norm_num)
theorem B621941 : Blo 413771 621941 := bbase (se 5 (by rfl) ⟨29153, by rfl⟩ : syracuseStep 621941 = 58307) (by norm_num)
theorem B1408373 : Blo 413771 1408373 := bbase (se 5 (by rfl) ⟨66017, by rfl⟩ : syracuseStep 1408373 = 132035) (by norm_num)
theorem B621965 : Blo 413771 621965 := bbase (se 3 (by rfl) ⟨116618, by rfl⟩ : syracuseStep 621965 = 233237) (by norm_num)
theorem B523685 : Blo 413771 523685 := bbase (se 4 (by rfl) ⟨49095, by rfl⟩ : syracuseStep 523685 = 98191) (by norm_num)
theorem B621989 : Blo 413771 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B622013 : Blo 413771 622013 := bbase (se 3 (by rfl) ⟨116627, by rfl⟩ : syracuseStep 622013 = 233255) (by norm_num)
theorem B622037 : Blo 413771 622037 := bbase (se 7 (by rfl) ⟨7289, by rfl⟩ : syracuseStep 622037 = 14579) (by norm_num)
theorem B523741 : Blo 413771 523741 := bbase (se 3 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 523741 = 196403) (by norm_num)
theorem B622061 : Blo 413771 622061 := bbase (se 3 (by rfl) ⟨116636, by rfl⟩ : syracuseStep 622061 = 233273) (by norm_num)
theorem B622085 : Blo 413771 622085 := bbase (se 4 (by rfl) ⟨58320, by rfl⟩ : syracuseStep 622085 = 116641) (by norm_num)
theorem B622109 : Blo 413771 622109 := bbase (se 3 (by rfl) ⟨116645, by rfl⟩ : syracuseStep 622109 = 233291) (by norm_num)
theorem B622133 : Blo 413771 622133 := bbase (se 5 (by rfl) ⟨29162, by rfl⟩ : syracuseStep 622133 = 58325) (by norm_num)
theorem B523837 : Blo 413771 523837 := bbase (se 3 (by rfl) ⟨98219, by rfl⟩ : syracuseStep 523837 = 196439) (by norm_num)
theorem B622157 : Blo 413771 622157 := bbase (se 3 (by rfl) ⟨116654, by rfl⟩ : syracuseStep 622157 = 233309) (by norm_num)
theorem B622181 : Blo 413771 622181 := bbase (se 4 (by rfl) ⟨58329, by rfl⟩ : syracuseStep 622181 = 116659) (by norm_num)
theorem B786037 : Blo 413771 786037 := bbase (se 5 (by rfl) ⟨36845, by rfl⟩ : syracuseStep 786037 = 73691) (by norm_num)
theorem B622205 : Blo 413771 622205 := bbase (se 3 (by rfl) ⟨116663, by rfl⟩ : syracuseStep 622205 = 233327) (by norm_num)
theorem B622229 : Blo 413771 622229 := bbase (se 6 (by rfl) ⟨14583, by rfl⟩ : syracuseStep 622229 = 29167) (by norm_num)
theorem B622253 : Blo 413771 622253 := bbase (se 3 (by rfl) ⟨116672, by rfl⟩ : syracuseStep 622253 = 233345) (by norm_num)
theorem B1048261 : Blo 413771 1048261 := bbase (se 4 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 1048261 = 196549) (by norm_num)
theorem B622277 : Blo 413771 622277 := bbase (se 4 (by rfl) ⟨58338, by rfl⟩ : syracuseStep 622277 = 116677) (by norm_num)
theorem B884429 : Blo 413771 884429 := bbase (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) (by norm_num)
theorem B622301 : Blo 413771 622301 := bbase (se 3 (by rfl) ⟨116681, by rfl⟩ : syracuseStep 622301 = 233363) (by norm_num)
theorem B524009 : Blo 413771 524009 := bbase (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) (by norm_num)
theorem B622325 : Blo 413771 622325 := bbase (se 5 (by rfl) ⟨29171, by rfl⟩ : syracuseStep 622325 = 58343) (by norm_num)
theorem B786181 : Blo 413771 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B622349 : Blo 413771 622349 := bbase (se 3 (by rfl) ⟨116690, by rfl⟩ : syracuseStep 622349 = 233381) (by norm_num)
theorem B524065 : Blo 413771 524065 := bbase (se 2 (by rfl) ⟨196524, by rfl⟩ : syracuseStep 524065 = 393049) (by norm_num)
theorem B622373 : Blo 413771 622373 := bbase (se 4 (by rfl) ⟨58347, by rfl⟩ : syracuseStep 622373 = 116695) (by norm_num)
theorem B1408805 : Blo 413771 1408805 := bbase (se 4 (by rfl) ⟨132075, by rfl⟩ : syracuseStep 1408805 = 264151) (by norm_num)
theorem B1048373 : Blo 413771 1048373 := bbase (se 5 (by rfl) ⟨49142, by rfl⟩ : syracuseStep 1048373 = 98285) (by norm_num)
theorem B622397 : Blo 413771 622397 := bbase (se 3 (by rfl) ⟨116699, by rfl⟩ : syracuseStep 622397 = 233399) (by norm_num)
theorem B622421 : Blo 413771 622421 := bbase (se 9 (by rfl) ⟨1823, by rfl⟩ : syracuseStep 622421 = 3647) (by norm_num)
theorem B622445 : Blo 413771 622445 := bbase (se 3 (by rfl) ⟨116708, by rfl⟩ : syracuseStep 622445 = 233417) (by norm_num)
theorem B589693 : Blo 413771 589693 := bbase (se 3 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 589693 = 221135) (by norm_num)
theorem B524161 : Blo 413771 524161 := bbase (se 2 (by rfl) ⟨196560, by rfl⟩ : syracuseStep 524161 = 393121) (by norm_num)
theorem B622469 : Blo 413771 622469 := bbase (se 4 (by rfl) ⟨58356, by rfl⟩ : syracuseStep 622469 = 116713) (by norm_num)
theorem B622493 : Blo 413771 622493 := bbase (se 3 (by rfl) ⟨116717, by rfl⟩ : syracuseStep 622493 = 233435) (by norm_num)
theorem B786341 : Blo 413771 786341 := bbase (se 4 (by rfl) ⟨73719, by rfl⟩ : syracuseStep 786341 = 147439) (by norm_num)
theorem B622517 : Blo 413771 622517 := bbase (se 5 (by rfl) ⟨29180, by rfl⟩ : syracuseStep 622517 = 58361) (by norm_num)
theorem B622541 : Blo 413771 622541 := bbase (se 3 (by rfl) ⟨116726, by rfl⟩ : syracuseStep 622541 = 233453) (by norm_num)
theorem B622565 : Blo 413771 622565 := bbase (se 4 (by rfl) ⟨58365, by rfl⟩ : syracuseStep 622565 = 116731) (by norm_num)
theorem B1048565 : Blo 413771 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B622589 : Blo 413771 622589 := bbase (se 3 (by rfl) ⟨116735, by rfl⟩ : syracuseStep 622589 = 233471) (by norm_num)
theorem B622595 : Blo 413771 622595 := bstep (se 1 (by rfl) ⟨466946, by rfl⟩ : syracuseStep 622595 = 933893) B933893
theorem B622625 : Blo 413771 622625 := bstep (se 2 (by rfl) ⟨233484, by rfl⟩ : syracuseStep 622625 = 466969) B466969
theorem B524323 : Blo 413771 524323 := bstep (se 1 (by rfl) ⟨393242, by rfl⟩ : syracuseStep 524323 = 786485) B786485
theorem B622643 : Blo 413771 622643 := bstep (se 1 (by rfl) ⟨466982, by rfl⟩ : syracuseStep 622643 = 933965) B933965
theorem B622673 : Blo 413771 622673 := bstep (se 2 (by rfl) ⟨233502, by rfl⟩ : syracuseStep 622673 = 467005) B467005
theorem B2097251 : Blo 413771 2097251 := bstep (se 1 (by rfl) ⟨1572938, by rfl⟩ : syracuseStep 2097251 = 3145877) B3145877
theorem B622691 : Blo 413771 622691 := bstep (se 1 (by rfl) ⟨467018, by rfl⟩ : syracuseStep 622691 = 934037) B934037
theorem B622721 : Blo 413771 622721 := bstep (se 2 (by rfl) ⟨233520, by rfl⟩ : syracuseStep 622721 = 467041) B467041
theorem B884881 : Blo 413771 884881 := bstep (se 2 (by rfl) ⟨331830, by rfl⟩ : syracuseStep 884881 = 663661) B663661
theorem B622739 : Blo 413771 622739 := bstep (se 1 (by rfl) ⟨467054, by rfl⟩ : syracuseStep 622739 = 934109) B934109
theorem B622769 : Blo 413771 622769 := bstep (se 2 (by rfl) ⟨233538, by rfl⟩ : syracuseStep 622769 = 467077) B467077
theorem B622787 : Blo 413771 622787 := bstep (se 1 (by rfl) ⟨467090, by rfl⟩ : syracuseStep 622787 = 934181) B934181
theorem B622817 : Blo 413771 622817 := bstep (se 2 (by rfl) ⟨233556, by rfl⟩ : syracuseStep 622817 = 467113) B467113
theorem B1573091 : Blo 413771 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B622835 : Blo 413771 622835 := bstep (se 1 (by rfl) ⟨467126, by rfl⟩ : syracuseStep 622835 = 934253) B934253
theorem B622865 : Blo 413771 622865 := bstep (se 2 (by rfl) ⟨233574, by rfl⟩ : syracuseStep 622865 = 467149) B467149
theorem B622883 : Blo 413771 622883 := bstep (se 1 (by rfl) ⟨467162, by rfl⟩ : syracuseStep 622883 = 934325) B934325
theorem B622913 : Blo 413771 622913 := bstep (se 2 (by rfl) ⟨233592, by rfl⟩ : syracuseStep 622913 = 467185) B467185
theorem B622931 : Blo 413771 622931 := bstep (se 1 (by rfl) ⟨467198, by rfl⟩ : syracuseStep 622931 = 934397) B934397
theorem B622961 : Blo 413771 622961 := bstep (se 2 (by rfl) ⟨233610, by rfl⟩ : syracuseStep 622961 = 467221) B467221
theorem B622979 : Blo 413771 622979 := bstep (se 1 (by rfl) ⟨467234, by rfl⟩ : syracuseStep 622979 = 934469) B934469
theorem B623009 : Blo 413771 623009 := bstep (se 2 (by rfl) ⟨233628, by rfl⟩ : syracuseStep 623009 = 467257) B467257
theorem B1409453 : Blo 413771 1409453 := bstep (se 3 (by rfl) ⟨264272, by rfl⟩ : syracuseStep 1409453 = 528545) B528545
theorem B2425265 : Blo 413771 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B590257 : Blo 413771 590257 := bstep (se 2 (by rfl) ⟨221346, by rfl⟩ : syracuseStep 590257 = 442693) B442693
theorem B623027 : Blo 413771 623027 := bstep (se 1 (by rfl) ⟨467270, by rfl⟩ : syracuseStep 623027 = 934541) B934541
theorem B623057 : Blo 413771 623057 := bstep (se 2 (by rfl) ⟨233646, by rfl⟩ : syracuseStep 623057 = 467293) B467293
theorem B623075 : Blo 413771 623075 := bstep (se 1 (by rfl) ⟨467306, by rfl⟩ : syracuseStep 623075 = 934613) B934613
theorem B1409507 : Blo 413771 1409507 := bstep (se 1 (by rfl) ⟨1057130, by rfl⟩ : syracuseStep 1409507 = 2114261) B2114261
theorem B623105 : Blo 413771 623105 := bstep (se 2 (by rfl) ⟨233664, by rfl⟩ : syracuseStep 623105 = 467329) B467329
theorem B524819 : Blo 413771 524819 := bstep (se 1 (by rfl) ⟨393614, by rfl⟩ : syracuseStep 524819 = 787229) B787229
theorem B623123 : Blo 413771 623123 := bstep (se 1 (by rfl) ⟨467342, by rfl⟩ : syracuseStep 623123 = 934685) B934685
theorem B623153 : Blo 413771 623153 := bstep (se 2 (by rfl) ⟨233682, by rfl⟩ : syracuseStep 623153 = 467365) B467365
theorem B623171 : Blo 413771 623171 := bstep (se 1 (by rfl) ⟨467378, by rfl⟩ : syracuseStep 623171 = 934757) B934757
theorem B1180241 : Blo 413771 1180241 := bstep (se 2 (by rfl) ⟨442590, by rfl⟩ : syracuseStep 1180241 = 885181) B885181
theorem B623201 : Blo 413771 623201 := bstep (se 2 (by rfl) ⟨233700, by rfl⟩ : syracuseStep 623201 = 467401) B467401
theorem B623219 : Blo 413771 623219 := bstep (se 1 (by rfl) ⟨467414, by rfl⟩ : syracuseStep 623219 = 934829) B934829
theorem B1049233 : Blo 413771 1049233 := bstep (se 2 (by rfl) ⟨393462, by rfl⟩ : syracuseStep 1049233 = 786925) B786925
theorem B623249 : Blo 413771 623249 := bstep (se 2 (by rfl) ⟨233718, by rfl⟩ : syracuseStep 623249 = 467437) B467437
theorem B623267 : Blo 413771 623267 := bstep (se 1 (by rfl) ⟨467450, by rfl⟩ : syracuseStep 623267 = 934901) B934901
theorem B623297 : Blo 413771 623297 := bstep (se 2 (by rfl) ⟨233736, by rfl⟩ : syracuseStep 623297 = 467473) B467473
theorem B787153 : Blo 413771 787153 := bstep (se 2 (by rfl) ⟨295182, by rfl⟩ : syracuseStep 787153 = 590365) B590365
theorem B623315 : Blo 413771 623315 := bstep (se 1 (by rfl) ⟨467486, by rfl⟩ : syracuseStep 623315 = 934973) B934973
theorem B623345 : Blo 413771 623345 := bstep (se 2 (by rfl) ⟨233754, by rfl⟩ : syracuseStep 623345 = 467509) B467509
theorem B1409777 : Blo 413771 1409777 := bstep (se 2 (by rfl) ⟨528666, by rfl⟩ : syracuseStep 1409777 = 1057333) B1057333
theorem B590593 : Blo 413771 590593 := bstep (se 2 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 590593 = 442945) B442945
theorem B623363 : Blo 413771 623363 := bstep (se 1 (by rfl) ⟨467522, by rfl⟩ : syracuseStep 623363 = 935045) B935045
theorem B1180433 : Blo 413771 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B623393 : Blo 413771 623393 := bstep (se 2 (by rfl) ⟨233772, by rfl⟩ : syracuseStep 623393 = 467545) B467545
theorem B1770275 : Blo 413771 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B623411 : Blo 413771 623411 := bstep (se 1 (by rfl) ⟨467558, by rfl⟩ : syracuseStep 623411 = 935117) B935117
theorem B623441 : Blo 413771 623441 := bstep (se 2 (by rfl) ⟨233790, by rfl⟩ : syracuseStep 623441 = 467581) B467581
theorem B623459 : Blo 413771 623459 := bstep (se 1 (by rfl) ⟨467594, by rfl⟩ : syracuseStep 623459 = 935189) B935189
theorem B787313 : Blo 413771 787313 := bstep (se 2 (by rfl) ⟨295242, by rfl⟩ : syracuseStep 787313 = 590485) B590485
theorem B623489 : Blo 413771 623489 := bstep (se 2 (by rfl) ⟨233808, by rfl⟩ : syracuseStep 623489 = 467617) B467617
theorem B2098061 : Blo 413771 2098061 := bstep (se 3 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 2098061 = 786773) B786773
theorem B623507 : Blo 413771 623507 := bstep (se 1 (by rfl) ⟨467630, by rfl⟩ : syracuseStep 623507 = 935261) B935261
theorem B1049507 : Blo 413771 1049507 := bstep (se 1 (by rfl) ⟨787130, by rfl⟩ : syracuseStep 1049507 = 1574261) B1574261
theorem B885667 : Blo 413771 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B623537 : Blo 413771 623537 := bstep (se 2 (by rfl) ⟨233826, by rfl⟩ : syracuseStep 623537 = 467653) B467653
theorem B623555 : Blo 413771 623555 := bstep (se 1 (by rfl) ⟨467666, by rfl⟩ : syracuseStep 623555 = 935333) B935333
theorem B623585 : Blo 413771 623585 := bstep (se 2 (by rfl) ⟨233844, by rfl⟩ : syracuseStep 623585 = 467689) B467689
theorem B623603 : Blo 413771 623603 := bstep (se 1 (by rfl) ⟨467702, by rfl⟩ : syracuseStep 623603 = 935405) B935405
theorem B623633 : Blo 413771 623633 := bstep (se 2 (by rfl) ⟨233862, by rfl⟩ : syracuseStep 623633 = 467725) B467725
theorem B623651 : Blo 413771 623651 := bstep (se 1 (by rfl) ⟨467738, by rfl⟩ : syracuseStep 623651 = 935477) B935477
theorem B623681 : Blo 413771 623681 := bstep (se 2 (by rfl) ⟨233880, by rfl⟩ : syracuseStep 623681 = 467761) B467761
theorem B623699 : Blo 413771 623699 := bstep (se 1 (by rfl) ⟨467774, by rfl⟩ : syracuseStep 623699 = 935549) B935549
theorem B1049699 : Blo 413771 1049699 := bstep (se 1 (by rfl) ⟨787274, by rfl⟩ : syracuseStep 1049699 = 1574549) B1574549
theorem B623729 : Blo 413771 623729 := bstep (se 2 (by rfl) ⟨233898, by rfl⟩ : syracuseStep 623729 = 467797) B467797
theorem B623747 : Blo 413771 623747 := bstep (se 1 (by rfl) ⟨467810, by rfl⟩ : syracuseStep 623747 = 935621) B935621
theorem B623777 : Blo 413771 623777 := bstep (se 2 (by rfl) ⟨233916, by rfl⟩ : syracuseStep 623777 = 467833) B467833
theorem B623795 : Blo 413771 623795 := bstep (se 1 (by rfl) ⟨467846, by rfl⟩ : syracuseStep 623795 = 935693) B935693
theorem B1574093 : Blo 413771 1574093 := bstep (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) B590285
theorem B623825 : Blo 413771 623825 := bstep (se 2 (by rfl) ⟨233934, by rfl⟩ : syracuseStep 623825 = 467869) B467869
theorem B525523 : Blo 413771 525523 := bstep (se 1 (by rfl) ⟨394142, by rfl⟩ : syracuseStep 525523 = 788285) B788285
theorem B623843 : Blo 413771 623843 := bstep (se 1 (by rfl) ⟨467882, by rfl⟩ : syracuseStep 623843 = 935765) B935765
theorem B623873 : Blo 413771 623873 := bstep (se 2 (by rfl) ⟨233952, by rfl⟩ : syracuseStep 623873 = 467905) B467905
theorem B787715 : Blo 413771 787715 := bstep (se 1 (by rfl) ⟨590786, by rfl⟩ : syracuseStep 787715 = 1181573) B1181573
theorem B623891 : Blo 413771 623891 := bstep (se 1 (by rfl) ⟨467918, by rfl⟩ : syracuseStep 623891 = 935837) B935837
theorem B623921 : Blo 413771 623921 := bstep (se 2 (by rfl) ⟨233970, by rfl⟩ : syracuseStep 623921 = 467941) B467941
theorem B525619 : Blo 413771 525619 := bstep (se 1 (by rfl) ⟨394214, by rfl⟩ : syracuseStep 525619 = 788429) B788429
theorem B623939 : Blo 413771 623939 := bstep (se 1 (by rfl) ⟨467954, by rfl⟩ : syracuseStep 623939 = 935909) B935909
theorem B591185 : Blo 413771 591185 := bstep (se 2 (by rfl) ⟨221694, by rfl⟩ : syracuseStep 591185 = 443389) B443389
theorem B623969 : Blo 413771 623969 := bstep (se 2 (by rfl) ⟨233988, by rfl⟩ : syracuseStep 623969 = 467977) B467977
theorem B623987 : Blo 413771 623987 := bstep (se 1 (by rfl) ⟨467990, by rfl⟩ : syracuseStep 623987 = 935981) B935981
theorem B624017 : Blo 413771 624017 := bstep (se 2 (by rfl) ⟨234006, by rfl⟩ : syracuseStep 624017 = 468013) B468013
theorem B624035 : Blo 413771 624035 := bstep (se 1 (by rfl) ⟨468026, by rfl⟩ : syracuseStep 624035 = 936053) B936053
theorem B624065 : Blo 413771 624065 := bstep (se 2 (by rfl) ⟨234024, by rfl⟩ : syracuseStep 624065 = 468049) B468049
theorem B624083 : Blo 413771 624083 := bstep (se 1 (by rfl) ⟨468062, by rfl⟩ : syracuseStep 624083 = 936125) B936125
theorem B1344995 : Blo 413771 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B624113 : Blo 413771 624113 := bstep (se 2 (by rfl) ⟨234042, by rfl⟩ : syracuseStep 624113 = 468085) B468085
theorem B5342705 : Blo 413771 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B624131 : Blo 413771 624131 := bstep (se 1 (by rfl) ⟨468098, by rfl⟩ : syracuseStep 624131 = 936197) B936197
theorem B624161 : Blo 413771 624161 := bstep (se 2 (by rfl) ⟨234060, by rfl⟩ : syracuseStep 624161 = 468121) B468121
theorem B624179 : Blo 413771 624179 := bstep (se 1 (by rfl) ⟨468134, by rfl⟩ : syracuseStep 624179 = 936269) B936269
theorem B624209 : Blo 413771 624209 := bstep (se 2 (by rfl) ⟨234078, by rfl⟩ : syracuseStep 624209 = 468157) B468157
theorem B624227 : Blo 413771 624227 := bstep (se 1 (by rfl) ⟨468170, by rfl⟩ : syracuseStep 624227 = 936341) B936341
theorem B886385 : Blo 413771 886385 := bstep (se 2 (by rfl) ⟨332394, by rfl⟩ : syracuseStep 886385 = 664789) B664789
theorem B624257 : Blo 413771 624257 := bstep (se 2 (by rfl) ⟨234096, by rfl⟩ : syracuseStep 624257 = 468193) B468193
theorem B624275 : Blo 413771 624275 := bstep (se 1 (by rfl) ⟨468206, by rfl⟩ : syracuseStep 624275 = 936413) B936413
theorem B624305 : Blo 413771 624305 := bstep (se 2 (by rfl) ⟨234114, by rfl⟩ : syracuseStep 624305 = 468229) B468229
theorem B624323 : Blo 413771 624323 := bstep (se 1 (by rfl) ⟨468242, by rfl⟩ : syracuseStep 624323 = 936485) B936485
theorem B624353 : Blo 413771 624353 := bstep (se 2 (by rfl) ⟨234132, by rfl⟩ : syracuseStep 624353 = 468265) B468265
theorem B1181425 : Blo 413771 1181425 := bstep (se 2 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 1181425 = 886069) B886069
theorem B624371 : Blo 413771 624371 := bstep (se 1 (by rfl) ⟨468278, by rfl⟩ : syracuseStep 624371 = 936557) B936557
theorem B624401 : Blo 413771 624401 := bstep (se 2 (by rfl) ⟨234150, by rfl⟩ : syracuseStep 624401 = 468301) B468301
theorem B526115 : Blo 413771 526115 := bstep (se 1 (by rfl) ⟨394586, by rfl⟩ : syracuseStep 526115 = 789173) B789173
theorem B624419 : Blo 413771 624419 := bstep (se 1 (by rfl) ⟨468314, by rfl⟩ : syracuseStep 624419 = 936629) B936629
theorem B624449 : Blo 413771 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B624467 : Blo 413771 624467 := bstep (se 1 (by rfl) ⟨468350, by rfl⟩ : syracuseStep 624467 = 936701) B936701
theorem B591715 : Blo 413771 591715 := bstep (se 1 (by rfl) ⟨443786, by rfl⟩ : syracuseStep 591715 = 887573) B887573
theorem B624497 : Blo 413771 624497 := bstep (se 2 (by rfl) ⟨234186, by rfl⟩ : syracuseStep 624497 = 468373) B468373
theorem B624515 : Blo 413771 624515 := bstep (se 1 (by rfl) ⟨468386, by rfl⟩ : syracuseStep 624515 = 936773) B936773
theorem B624545 : Blo 413771 624545 := bstep (se 2 (by rfl) ⟨234204, by rfl⟩ : syracuseStep 624545 = 468409) B468409
theorem B624563 : Blo 413771 624563 := bstep (se 1 (by rfl) ⟨468422, by rfl⟩ : syracuseStep 624563 = 936845) B936845
theorem B624593 : Blo 413771 624593 := bstep (se 2 (by rfl) ⟨234222, by rfl⟩ : syracuseStep 624593 = 468445) B468445
theorem B624611 : Blo 413771 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B624641 : Blo 413771 624641 := bstep (se 2 (by rfl) ⟨234240, by rfl⟩ : syracuseStep 624641 = 468481) B468481
theorem B1181699 : Blo 413771 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B1050641 : Blo 413771 1050641 := bstep (se 2 (by rfl) ⟨393990, by rfl⟩ : syracuseStep 1050641 = 787981) B787981
theorem B624659 : Blo 413771 624659 := bstep (se 1 (by rfl) ⟨468494, by rfl⟩ : syracuseStep 624659 = 936989) B936989
theorem B9635861 : Blo 413771 9635861 := bstep (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) B451681
theorem B624689 : Blo 413771 624689 := bstep (se 2 (by rfl) ⟨234258, by rfl⟩ : syracuseStep 624689 = 468517) B468517
theorem B1050691 : Blo 413771 1050691 := bstep (se 1 (by rfl) ⟨788018, by rfl⟩ : syracuseStep 1050691 = 1576037) B1576037
theorem B624707 : Blo 413771 624707 := bstep (se 1 (by rfl) ⟨468530, by rfl⟩ : syracuseStep 624707 = 937061) B937061
theorem B2361413 : Blo 413771 2361413 := bstep (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) B442765
theorem B624737 : Blo 413771 624737 := bstep (se 2 (by rfl) ⟨234276, by rfl⟩ : syracuseStep 624737 = 468553) B468553
theorem B886897 : Blo 413771 886897 := bstep (se 2 (by rfl) ⟨332586, by rfl⟩ : syracuseStep 886897 = 665173) B665173
theorem B624755 : Blo 413771 624755 := bstep (se 1 (by rfl) ⟨468566, by rfl⟩ : syracuseStep 624755 = 937133) B937133
theorem B788611 : Blo 413771 788611 := bstep (se 1 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 788611 = 1182917) B1182917
theorem B2001037 : Blo 413771 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B624785 : Blo 413771 624785 := bstep (se 2 (by rfl) ⟨234294, by rfl⟩ : syracuseStep 624785 = 468589) B468589
theorem B624803 : Blo 413771 624803 := bstep (se 1 (by rfl) ⟨468602, by rfl⟩ : syracuseStep 624803 = 937205) B937205
theorem B592051 : Blo 413771 592051 := bstep (se 1 (by rfl) ⟨444038, by rfl⟩ : syracuseStep 592051 = 888077) B888077
theorem B624833 : Blo 413771 624833 := bstep (se 2 (by rfl) ⟨234312, by rfl⟩ : syracuseStep 624833 = 468625) B468625
theorem B1181891 : Blo 413771 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B1050833 : Blo 413771 1050833 := bstep (se 2 (by rfl) ⟨394062, by rfl⟩ : syracuseStep 1050833 = 788125) B788125
theorem B624851 : Blo 413771 624851 := bstep (se 1 (by rfl) ⟨468638, by rfl⟩ : syracuseStep 624851 = 937277) B937277
theorem B624881 : Blo 413771 624881 := bstep (se 2 (by rfl) ⟨234330, by rfl⟩ : syracuseStep 624881 = 468661) B468661
theorem B624899 : Blo 413771 624899 := bstep (se 1 (by rfl) ⟨468674, by rfl⟩ : syracuseStep 624899 = 937349) B937349
theorem B624929 : Blo 413771 624929 := bstep (se 2 (by rfl) ⟨234348, by rfl⟩ : syracuseStep 624929 = 468697) B468697
theorem B788771 : Blo 413771 788771 := bstep (se 1 (by rfl) ⟨591578, by rfl⟩ : syracuseStep 788771 = 1183157) B1183157
theorem B624947 : Blo 413771 624947 := bstep (se 1 (by rfl) ⟨468710, by rfl⟩ : syracuseStep 624947 = 937421) B937421
theorem B624977 : Blo 413771 624977 := bstep (se 2 (by rfl) ⟨234366, by rfl⟩ : syracuseStep 624977 = 468733) B468733
theorem B624995 : Blo 413771 624995 := bstep (se 1 (by rfl) ⟨468746, by rfl⟩ : syracuseStep 624995 = 937493) B937493
theorem B625025 : Blo 413771 625025 := bstep (se 2 (by rfl) ⟨234384, by rfl⟩ : syracuseStep 625025 = 468769) B468769
theorem B559505 : Blo 413771 559505 := bstep (se 2 (by rfl) ⟨209814, by rfl⟩ : syracuseStep 559505 = 419629) B419629
theorem B625043 : Blo 413771 625043 := bstep (se 1 (by rfl) ⟨468782, by rfl⟩ : syracuseStep 625043 = 937565) B937565
theorem B625073 : Blo 413771 625073 := bstep (se 2 (by rfl) ⟨234402, by rfl⟩ : syracuseStep 625073 = 468805) B468805
theorem B559553 : Blo 413771 559553 := bstep (se 2 (by rfl) ⟨209832, by rfl⟩ : syracuseStep 559553 = 419665) B419665
theorem B625091 : Blo 413771 625091 := bstep (se 1 (by rfl) ⟨468818, by rfl⟩ : syracuseStep 625091 = 937637) B937637
theorem B625121 : Blo 413771 625121 := bstep (se 2 (by rfl) ⟨234420, by rfl⟩ : syracuseStep 625121 = 468841) B468841
theorem B526819 : Blo 413771 526819 := bstep (se 1 (by rfl) ⟨395114, by rfl⟩ : syracuseStep 526819 = 790229) B790229
theorem B625139 : Blo 413771 625139 := bstep (se 1 (by rfl) ⟨468854, by rfl⟩ : syracuseStep 625139 = 937709) B937709
theorem B2361869 : Blo 413771 2361869 := bstep (se 3 (by rfl) ⟨442850, by rfl⟩ : syracuseStep 2361869 = 885701) B885701
theorem B625169 : Blo 413771 625169 := bstep (se 2 (by rfl) ⟨234438, by rfl⟩ : syracuseStep 625169 = 468877) B468877
theorem B625187 : Blo 413771 625187 := bstep (se 1 (by rfl) ⟨468890, by rfl⟩ : syracuseStep 625187 = 937781) B937781
theorem B625217 : Blo 413771 625217 := bstep (se 2 (by rfl) ⟨234456, by rfl⟩ : syracuseStep 625217 = 468913) B468913
theorem B526915 : Blo 413771 526915 := bstep (se 1 (by rfl) ⟨395186, by rfl⟩ : syracuseStep 526915 = 790373) B790373
theorem B625235 : Blo 413771 625235 := bstep (se 1 (by rfl) ⟨468926, by rfl⟩ : syracuseStep 625235 = 937853) B937853
theorem B3213923 : Blo 413771 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B625265 : Blo 413771 625265 := bstep (se 2 (by rfl) ⟨234474, by rfl⟩ : syracuseStep 625265 = 468949) B468949
theorem B625283 : Blo 413771 625283 := bstep (se 1 (by rfl) ⟨468962, by rfl⟩ : syracuseStep 625283 = 937925) B937925
theorem B625313 : Blo 413771 625313 := bstep (se 2 (by rfl) ⟨234492, by rfl⟩ : syracuseStep 625313 = 468985) B468985
theorem B625331 : Blo 413771 625331 := bstep (se 1 (by rfl) ⟨468998, by rfl⟩ : syracuseStep 625331 = 937997) B937997
theorem B11340485 : Blo 413771 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B625361 : Blo 413771 625361 := bstep (se 2 (by rfl) ⟨234510, by rfl⟩ : syracuseStep 625361 = 469021) B469021
theorem B592609 : Blo 413771 592609 := bstep (se 2 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 592609 = 444457) B444457
theorem B625379 : Blo 413771 625379 := bstep (se 1 (by rfl) ⟨469034, by rfl⟩ : syracuseStep 625379 = 938069) B938069
theorem B625409 : Blo 413771 625409 := bstep (se 2 (by rfl) ⟨234528, by rfl⟩ : syracuseStep 625409 = 469057) B469057
theorem B592643 : Blo 413771 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B625427 : Blo 413771 625427 := bstep (se 1 (by rfl) ⟨469070, by rfl⟩ : syracuseStep 625427 = 938141) B938141
theorem B625457 : Blo 413771 625457 := bstep (se 2 (by rfl) ⟨234546, by rfl⟩ : syracuseStep 625457 = 469093) B469093
theorem B625475 : Blo 413771 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B625505 : Blo 413771 625505 := bstep (se 2 (by rfl) ⟨234564, by rfl⟩ : syracuseStep 625505 = 469129) B469129
theorem B625523 : Blo 413771 625523 := bstep (se 1 (by rfl) ⟨469142, by rfl⟩ : syracuseStep 625523 = 938285) B938285
theorem B625553 : Blo 413771 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B625571 : Blo 413771 625571 := bstep (se 1 (by rfl) ⟨469178, by rfl⟩ : syracuseStep 625571 = 938357) B938357
theorem B625601 : Blo 413771 625601 := bstep (se 2 (by rfl) ⟨234600, by rfl⟩ : syracuseStep 625601 = 469201) B469201
theorem B625619 : Blo 413771 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B1182701 : Blo 413771 1182701 := bstep (se 3 (by rfl) ⟨221756, by rfl⟩ : syracuseStep 1182701 = 443513) B443513
theorem B625649 : Blo 413771 625649 := bstep (se 2 (by rfl) ⟨234618, by rfl⟩ : syracuseStep 625649 = 469237) B469237
theorem B1903601 : Blo 413771 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B625667 : Blo 413771 625667 := bstep (se 1 (by rfl) ⟨469250, by rfl⟩ : syracuseStep 625667 = 938501) B938501
theorem B625697 : Blo 413771 625697 := bstep (se 2 (by rfl) ⟨234636, by rfl⟩ : syracuseStep 625697 = 469273) B469273
theorem B1281059 : Blo 413771 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B527411 : Blo 413771 527411 := bstep (se 1 (by rfl) ⟨395558, by rfl⟩ : syracuseStep 527411 = 791117) B791117
theorem B625715 : Blo 413771 625715 := bstep (se 1 (by rfl) ⟨469286, by rfl⟩ : syracuseStep 625715 = 938573) B938573
theorem B625745 : Blo 413771 625745 := bstep (se 2 (by rfl) ⟨234654, by rfl⟩ : syracuseStep 625745 = 469309) B469309
theorem B625763 : Blo 413771 625763 := bstep (se 1 (by rfl) ⟨469322, by rfl⟩ : syracuseStep 625763 = 938645) B938645
theorem B625793 : Blo 413771 625793 := bstep (se 2 (by rfl) ⟨234672, by rfl⟩ : syracuseStep 625793 = 469345) B469345
theorem B625811 : Blo 413771 625811 := bstep (se 1 (by rfl) ⟨469358, by rfl⟩ : syracuseStep 625811 = 938717) B938717
theorem B1182883 : Blo 413771 1182883 := bstep (se 1 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 1182883 = 1774325) B1774325
theorem B1051825 : Blo 413771 1051825 := bstep (se 2 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 1051825 = 788869) B788869
theorem B625841 : Blo 413771 625841 := bstep (se 2 (by rfl) ⟨234690, by rfl⟩ : syracuseStep 625841 = 469381) B469381
theorem B625859 : Blo 413771 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B625889 : Blo 413771 625889 := bstep (se 2 (by rfl) ⟨234708, by rfl⟩ : syracuseStep 625889 = 469417) B469417
theorem B625907 : Blo 413771 625907 := bstep (se 1 (by rfl) ⟨469430, by rfl⟩ : syracuseStep 625907 = 938861) B938861
theorem B1576205 : Blo 413771 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B625937 : Blo 413771 625937 := bstep (se 2 (by rfl) ⟨234726, by rfl⟩ : syracuseStep 625937 = 469453) B469453
theorem B625955 : Blo 413771 625955 := bstep (se 1 (by rfl) ⟨469466, by rfl⟩ : syracuseStep 625955 = 938933) B938933
theorem B593201 : Blo 413771 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B625985 : Blo 413771 625985 := bstep (se 2 (by rfl) ⟨234744, by rfl⟩ : syracuseStep 625985 = 469489) B469489
theorem B789841 : Blo 413771 789841 := bstep (se 2 (by rfl) ⟨296190, by rfl⟩ : syracuseStep 789841 = 592381) B592381
theorem B626003 : Blo 413771 626003 := bstep (se 1 (by rfl) ⟨469502, by rfl⟩ : syracuseStep 626003 = 939005) B939005
theorem B626033 : Blo 413771 626033 := bstep (se 2 (by rfl) ⟨234762, by rfl⟩ : syracuseStep 626033 = 469525) B469525
theorem B593281 : Blo 413771 593281 := bstep (se 2 (by rfl) ⟨222480, by rfl⟩ : syracuseStep 593281 = 444961) B444961
theorem B626051 : Blo 413771 626051 := bstep (se 1 (by rfl) ⟨469538, by rfl⟩ : syracuseStep 626051 = 939077) B939077
theorem B626081 : Blo 413771 626081 := bstep (se 2 (by rfl) ⟨234780, by rfl⟩ : syracuseStep 626081 = 469561) B469561
theorem B626099 : Blo 413771 626099 := bstep (se 1 (by rfl) ⟨469574, by rfl⟩ : syracuseStep 626099 = 939149) B939149
theorem B1052099 : Blo 413771 1052099 := bstep (se 1 (by rfl) ⟨789074, by rfl⟩ : syracuseStep 1052099 = 1578149) B1578149
theorem B626129 : Blo 413771 626129 := bstep (se 2 (by rfl) ⟨234798, by rfl⟩ : syracuseStep 626129 = 469597) B469597
theorem B626147 : Blo 413771 626147 := bstep (se 1 (by rfl) ⟨469610, by rfl⟩ : syracuseStep 626147 = 939221) B939221
theorem B626177 : Blo 413771 626177 := bstep (se 2 (by rfl) ⟨234816, by rfl⟩ : syracuseStep 626177 = 469633) B469633
theorem B626195 : Blo 413771 626195 := bstep (se 1 (by rfl) ⟨469646, by rfl⟩ : syracuseStep 626195 = 939293) B939293
theorem B626225 : Blo 413771 626225 := bstep (se 2 (by rfl) ⟨234834, by rfl⟩ : syracuseStep 626225 = 469669) B469669
theorem B626243 : Blo 413771 626243 := bstep (se 1 (by rfl) ⟨469682, by rfl⟩ : syracuseStep 626243 = 939365) B939365
theorem B888401 : Blo 413771 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B626273 : Blo 413771 626273 := bstep (se 2 (by rfl) ⟨234852, by rfl⟩ : syracuseStep 626273 = 469705) B469705
theorem B626291 : Blo 413771 626291 := bstep (se 1 (by rfl) ⟨469718, by rfl⟩ : syracuseStep 626291 = 939437) B939437
theorem B1052291 : Blo 413771 1052291 := bstep (se 1 (by rfl) ⟨789218, by rfl⟩ : syracuseStep 1052291 = 1578437) B1578437
theorem B1183373 : Blo 413771 1183373 := bstep (se 3 (by rfl) ⟨221882, by rfl⟩ : syracuseStep 1183373 = 443765) B443765
theorem B626321 : Blo 413771 626321 := bstep (se 2 (by rfl) ⟨234870, by rfl⟩ : syracuseStep 626321 = 469741) B469741
theorem B626339 : Blo 413771 626339 := bstep (se 1 (by rfl) ⟨469754, by rfl⟩ : syracuseStep 626339 = 939509) B939509
theorem B626369 : Blo 413771 626369 := bstep (se 2 (by rfl) ⟨234888, by rfl⟩ : syracuseStep 626369 = 469777) B469777
theorem B626387 : Blo 413771 626387 := bstep (se 1 (by rfl) ⟨469790, by rfl⟩ : syracuseStep 626387 = 939581) B939581
theorem B2100977 : Blo 413771 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B626417 : Blo 413771 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B528115 : Blo 413771 528115 := bstep (se 1 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 528115 = 792173) B792173
theorem B626435 : Blo 413771 626435 := bstep (se 1 (by rfl) ⟨469826, by rfl⟩ : syracuseStep 626435 = 939653) B939653
theorem B626465 : Blo 413771 626465 := bstep (se 2 (by rfl) ⟨234924, by rfl⟩ : syracuseStep 626465 = 469849) B469849
theorem B626483 : Blo 413771 626483 := bstep (se 1 (by rfl) ⟨469862, by rfl⟩ : syracuseStep 626483 = 939725) B939725
theorem B626513 : Blo 413771 626513 := bstep (se 2 (by rfl) ⟨234942, by rfl⟩ : syracuseStep 626513 = 469885) B469885
theorem B528211 : Blo 413771 528211 := bstep (se 1 (by rfl) ⟨396158, by rfl⟩ : syracuseStep 528211 = 792317) B792317
theorem B626531 : Blo 413771 626531 := bstep (se 1 (by rfl) ⟨469898, by rfl⟩ : syracuseStep 626531 = 939797) B939797
theorem B626561 : Blo 413771 626561 := bstep (se 2 (by rfl) ⟨234960, by rfl⟩ : syracuseStep 626561 = 469921) B469921
theorem B626579 : Blo 413771 626579 := bstep (se 1 (by rfl) ⟨469934, by rfl⟩ : syracuseStep 626579 = 939869) B939869
theorem B626609 : Blo 413771 626609 := bstep (se 2 (by rfl) ⟨234978, by rfl⟩ : syracuseStep 626609 = 469957) B469957
theorem B626627 : Blo 413771 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B3149765 : Blo 413771 3149765 := bstep (se 4 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 3149765 = 590581) B590581
theorem B626657 : Blo 413771 626657 := bstep (se 2 (by rfl) ⟨234996, by rfl⟩ : syracuseStep 626657 = 469993) B469993
theorem B888803 : Blo 413771 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B1577009 : Blo 413771 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B594067 : Blo 413771 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B692417 : Blo 413771 692417 := bstep (se 2 (by rfl) ⟨259656, by rfl⟩ : syracuseStep 692417 = 519313) B519313
theorem B528707 : Blo 413771 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B790897 : Blo 413771 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B1053233 : Blo 413771 1053233 := bstep (se 2 (by rfl) ⟨394962, by rfl⟩ : syracuseStep 1053233 = 789925) B789925
theorem B1053283 : Blo 413771 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B2003555 : Blo 413771 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B594545 : Blo 413771 594545 := bstep (se 2 (by rfl) ⟨222954, by rfl⟩ : syracuseStep 594545 = 445909) B445909
theorem B1577677 : Blo 413771 1577677 := bstep (se 3 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 1577677 = 591629) B591629
theorem B594659 : Blo 413771 594659 := bstep (se 1 (by rfl) ⟨445994, by rfl⟩ : syracuseStep 594659 = 891989) B891989
theorem B1053425 : Blo 413771 1053425 := bstep (se 2 (by rfl) ⟨395034, by rfl⟩ : syracuseStep 1053425 = 790069) B790069
theorem B791299 : Blo 413771 791299 := bstep (se 1 (by rfl) ⟨593474, by rfl⟩ : syracuseStep 791299 = 1186949) B1186949
theorem B1184557 : Blo 413771 1184557 := bstep (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) B444209
theorem B791345 : Blo 413771 791345 := bstep (se 2 (by rfl) ⟨296754, by rfl⟩ : syracuseStep 791345 = 593509) B593509
theorem B594739 : Blo 413771 594739 := bstep (se 1 (by rfl) ⟨446054, by rfl⟩ : syracuseStep 594739 = 892109) B892109
theorem B889699 : Blo 413771 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B1774477 : Blo 413771 1774477 := bstep (se 3 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 1774477 = 665429) B665429
theorem B791633 : Blo 413771 791633 := bstep (se 2 (by rfl) ⟨296862, by rfl⟩ : syracuseStep 791633 = 593725) B593725
theorem B562321 : Blo 413771 562321 := bstep (se 2 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 562321 = 421741) B421741
theorem B2102435 : Blo 413771 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B2528497 : Blo 413771 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B2004209 : Blo 413771 2004209 := bstep (se 2 (by rfl) ⟨751578, by rfl⟩ : syracuseStep 2004209 = 1503157) B1503157
theorem B2364785 : Blo 413771 2364785 := bstep (se 2 (by rfl) ⟨886794, by rfl⟩ : syracuseStep 2364785 = 1773589) B1773589
theorem B497107 : Blo 413771 497107 := bstep (se 1 (by rfl) ⟨372830, by rfl⟩ : syracuseStep 497107 = 745661) B745661
theorem B1578467 : Blo 413771 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B1054417 : Blo 413771 1054417 := bstep (se 2 (by rfl) ⟨395406, by rfl⟩ : syracuseStep 1054417 = 790813) B790813
theorem B1119971 : Blo 413771 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B792355 : Blo 413771 792355 := bstep (se 1 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 792355 = 1188533) B1188533
theorem B1120081 : Blo 413771 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B1185617 : Blo 413771 1185617 := bstep (se 2 (by rfl) ⟨444606, by rfl⟩ : syracuseStep 1185617 = 889213) B889213
theorem B2103245 : Blo 413771 2103245 := bstep (se 3 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 2103245 = 788717) B788717
theorem B1054691 : Blo 413771 1054691 := bstep (se 1 (by rfl) ⟨791018, by rfl⟩ : syracuseStep 1054691 = 1582037) B1582037
theorem B890929 : Blo 413771 890929 := bstep (se 2 (by rfl) ⟨334098, by rfl⟩ : syracuseStep 890929 = 668197) B668197
theorem B1579121 : Blo 413771 1579121 := bstep (se 2 (by rfl) ⟨592170, by rfl⟩ : syracuseStep 1579121 = 1184341) B1184341
theorem B2398349 : Blo 413771 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B1054883 : Blo 413771 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B792803 : Blo 413771 792803 := bstep (se 1 (by rfl) ⟨594602, by rfl⟩ : syracuseStep 792803 = 1189205) B1189205
theorem B2005361 : Blo 413771 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B1186289 : Blo 413771 1186289 := bstep (se 2 (by rfl) ⟨444858, by rfl⟩ : syracuseStep 1186289 = 889717) B889717
theorem B793091 : Blo 413771 793091 := bstep (se 1 (by rfl) ⟨594818, by rfl⟩ : syracuseStep 793091 = 1189637) B1189637
theorem B465619 : Blo 413771 465619 := bstep (se 1 (by rfl) ⟨349214, by rfl⟩ : syracuseStep 465619 = 698429) B698429
theorem B9116387 : Blo 413771 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B2366243 : Blo 413771 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B465763 : Blo 413771 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B465907 : Blo 413771 465907 := bstep (se 1 (by rfl) ⟨349430, by rfl⟩ : syracuseStep 465907 = 698861) B698861
theorem B1055825 : Blo 413771 1055825 := bstep (se 2 (by rfl) ⟨395934, by rfl⟩ : syracuseStep 1055825 = 791869) B791869
theorem B2006129 : Blo 413771 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B498803 : Blo 413771 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B1055875 : Blo 413771 1055875 := bstep (se 1 (by rfl) ⟨791906, by rfl⟩ : syracuseStep 1055875 = 1583813) B1583813
theorem B466051 : Blo 413771 466051 := bstep (se 1 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 466051 = 699077) B699077
theorem B564451 : Blo 413771 564451 := bstep (se 1 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 564451 = 846677) B846677
theorem B1187075 : Blo 413771 1187075 := bstep (se 1 (by rfl) ⟨890306, by rfl⟩ : syracuseStep 1187075 = 1780613) B1780613
theorem B1056017 : Blo 413771 1056017 := bstep (se 2 (by rfl) ⟨396006, by rfl⟩ : syracuseStep 1056017 = 792013) B792013
theorem B466195 : Blo 413771 466195 := bstep (se 1 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 466195 = 699293) B699293
theorem B466339 : Blo 413771 466339 := bstep (se 1 (by rfl) ⟨349754, by rfl⟩ : syracuseStep 466339 = 699509) B699509
theorem B662995 : Blo 413771 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B4267505 : Blo 413771 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B630289 : Blo 413771 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B1580579 : Blo 413771 1580579 := bstep (se 1 (by rfl) ⟨1185434, by rfl⟩ : syracuseStep 1580579 = 2370869) B2370869
theorem B1580593 : Blo 413771 1580593 := bstep (se 2 (by rfl) ⟨592722, by rfl⟩ : syracuseStep 1580593 = 1185445) B1185445
theorem B466483 : Blo 413771 466483 := bstep (se 1 (by rfl) ⟨349862, by rfl⟩ : syracuseStep 466483 = 699725) B699725
theorem B630337 : Blo 413771 630337 := bstep (se 2 (by rfl) ⟨236376, by rfl⟩ : syracuseStep 630337 = 472753) B472753
theorem B1187405 : Blo 413771 1187405 := bstep (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) B445277
theorem B1187473 : Blo 413771 1187473 := bstep (se 2 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 1187473 = 890605) B890605
theorem B466627 : Blo 413771 466627 := bstep (se 1 (by rfl) ⟨349970, by rfl⟩ : syracuseStep 466627 = 699941) B699941
theorem B2367245 : Blo 413771 2367245 := bstep (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) B887717
theorem B466771 : Blo 413771 466771 := bstep (se 1 (by rfl) ⟨350078, by rfl⟩ : syracuseStep 466771 = 700157) B700157
theorem B1187747 : Blo 413771 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B1679309 : Blo 413771 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B466915 : Blo 413771 466915 := bstep (se 1 (by rfl) ⟨350186, by rfl⟩ : syracuseStep 466915 = 700373) B700373
theorem B1679437 : Blo 413771 1679437 := bstep (se 3 (by rfl) ⟨314894, by rfl⟩ : syracuseStep 1679437 = 629789) B629789
theorem B467059 : Blo 413771 467059 := bstep (se 1 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 467059 = 700589) B700589
theorem B1057009 : Blo 413771 1057009 := bstep (se 2 (by rfl) ⟨396378, by rfl⟩ : syracuseStep 1057009 = 792757) B792757
theorem B467203 : Blo 413771 467203 := bstep (se 1 (by rfl) ⟨350402, by rfl⟩ : syracuseStep 467203 = 700805) B700805
theorem B467347 : Blo 413771 467347 := bstep (se 1 (by rfl) ⟨350510, by rfl⟩ : syracuseStep 467347 = 701021) B701021
theorem B1057283 : Blo 413771 1057283 := bstep (se 1 (by rfl) ⟨792962, by rfl⟩ : syracuseStep 1057283 = 1585925) B1585925
theorem B598547 : Blo 413771 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B533027 : Blo 413771 533027 := bstep (se 1 (by rfl) ⟨399770, by rfl⟩ : syracuseStep 533027 = 799541) B799541
theorem B467491 : Blo 413771 467491 := bstep (se 1 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 467491 = 701237) B701237
theorem B467635 : Blo 413771 467635 := bstep (se 1 (by rfl) ⟨350726, by rfl⟩ : syracuseStep 467635 = 701453) B701453
theorem B1057475 : Blo 413771 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B1123021 : Blo 413771 1123021 := bstep (se 3 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 1123021 = 421133) B421133
theorem B1188589 : Blo 413771 1188589 := bstep (se 3 (by rfl) ⟨222860, by rfl⟩ : syracuseStep 1188589 = 445721) B445721
theorem B2106161 : Blo 413771 2106161 := bstep (se 2 (by rfl) ⟨789810, by rfl⟩ : syracuseStep 2106161 = 1579621) B1579621
theorem B467779 : Blo 413771 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B1188749 : Blo 413771 1188749 := bstep (se 3 (by rfl) ⟨222890, by rfl⟩ : syracuseStep 1188749 = 445781) B445781
theorem B664481 : Blo 413771 664481 := bstep (se 2 (by rfl) ⟨249180, by rfl⟩ : syracuseStep 664481 = 498361) B498361
theorem B467923 : Blo 413771 467923 := bstep (se 1 (by rfl) ⟨350942, by rfl⟩ : syracuseStep 467923 = 701885) B701885
theorem B1582051 : Blo 413771 1582051 := bstep (se 1 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 1582051 = 2373077) B2373077
theorem B664609 : Blo 413771 664609 := bstep (se 2 (by rfl) ⟨249228, by rfl⟩ : syracuseStep 664609 = 498457) B498457
theorem B1188931 : Blo 413771 1188931 := bstep (se 1 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 1188931 = 1783397) B1783397
theorem B468067 : Blo 413771 468067 := bstep (se 1 (by rfl) ⟨351050, by rfl⟩ : syracuseStep 468067 = 702101) B702101
theorem B1778851 : Blo 413771 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B468211 : Blo 413771 468211 := bstep (se 1 (by rfl) ⟨351158, by rfl⟩ : syracuseStep 468211 = 702317) B702317
theorem B468355 : Blo 413771 468355 := bstep (se 1 (by rfl) ⟨351266, by rfl⟩ : syracuseStep 468355 = 702533) B702533
theorem B468499 : Blo 413771 468499 := bstep (se 1 (by rfl) ⟨351374, by rfl⟩ : syracuseStep 468499 = 702749) B702749
theorem B1680995 : Blo 413771 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B3155597 : Blo 413771 3155597 := bstep (se 3 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 3155597 = 1183349) B1183349
theorem B468643 : Blo 413771 468643 := bstep (se 1 (by rfl) ⟨351482, by rfl⟩ : syracuseStep 468643 = 702965) B702965
theorem B501427 : Blo 413771 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B1124081 : Blo 413771 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B2533169 : Blo 413771 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B468787 : Blo 413771 468787 := bstep (se 1 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 468787 = 703181) B703181
theorem B468931 : Blo 413771 468931 := bstep (se 1 (by rfl) ⟨351698, by rfl⟩ : syracuseStep 468931 = 703397) B703397
theorem B698321 : Blo 413771 698321 := bstep (se 2 (by rfl) ⟨261870, by rfl⟩ : syracuseStep 698321 = 523741) B523741
theorem B501763 : Blo 413771 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B698449 : Blo 413771 698449 := bstep (se 2 (by rfl) ⟨261918, by rfl⟩ : syracuseStep 698449 = 523837) B523837
theorem B469075 : Blo 413771 469075 := bstep (se 1 (by rfl) ⟨351806, by rfl⟩ : syracuseStep 469075 = 703613) B703613
theorem B698483 : Blo 413771 698483 := bstep (se 1 (by rfl) ⟨523862, by rfl⟩ : syracuseStep 698483 = 1047725) B1047725
theorem B2107619 : Blo 413771 2107619 := bstep (se 1 (by rfl) ⟨1580714, by rfl⟩ : syracuseStep 2107619 = 3161429) B3161429
theorem B469219 : Blo 413771 469219 := bstep (se 1 (by rfl) ⟨351914, by rfl⟩ : syracuseStep 469219 = 703829) B703829
theorem B698611 : Blo 413771 698611 := bstep (se 1 (by rfl) ⟨523958, by rfl⟩ : syracuseStep 698611 = 1047917) B1047917
theorem B665891 : Blo 413771 665891 := bstep (se 1 (by rfl) ⟨499418, by rfl⟩ : syracuseStep 665891 = 998837) B998837
theorem B469363 : Blo 413771 469363 := bstep (se 1 (by rfl) ⟨352022, by rfl⟩ : syracuseStep 469363 = 704045) B704045
theorem B698753 : Blo 413771 698753 := bstep (se 2 (by rfl) ⟨262032, by rfl⟩ : syracuseStep 698753 = 524065) B524065
theorem B665987 : Blo 413771 665987 := bstep (se 1 (by rfl) ⟨499490, by rfl⟩ : syracuseStep 665987 = 998981) B998981
theorem B2664845 : Blo 413771 2664845 := bstep (se 3 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 2664845 = 999317) B999317
theorem B666019 : Blo 413771 666019 := bstep (se 1 (by rfl) ⟨499514, by rfl⟩ : syracuseStep 666019 = 999029) B999029
theorem B698881 : Blo 413771 698881 := bstep (se 2 (by rfl) ⟨262080, by rfl⟩ : syracuseStep 698881 = 524161) B524161
theorem B469507 : Blo 413771 469507 := bstep (se 1 (by rfl) ⟨352130, by rfl⟩ : syracuseStep 469507 = 704261) B704261
theorem B698915 : Blo 413771 698915 := bstep (se 1 (by rfl) ⟨524186, by rfl⟩ : syracuseStep 698915 = 1048373) B1048373
theorem B2370161 : Blo 413771 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B469651 : Blo 413771 469651 := bstep (se 1 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 469651 = 704477) B704477
theorem B699043 : Blo 413771 699043 := bstep (se 1 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 699043 = 1048565) B1048565
theorem B469795 : Blo 413771 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B699185 : Blo 413771 699185 := bstep (se 2 (by rfl) ⟨262194, by rfl⟩ : syracuseStep 699185 = 524389) B524389
theorem B699313 : Blo 413771 699313 := bstep (se 2 (by rfl) ⟨262242, by rfl⟩ : syracuseStep 699313 = 524485) B524485
theorem B469939 : Blo 413771 469939 := bstep (se 1 (by rfl) ⟨352454, by rfl⟩ : syracuseStep 469939 = 704909) B704909
theorem B699347 : Blo 413771 699347 := bstep (se 1 (by rfl) ⟨524510, by rfl⟩ : syracuseStep 699347 = 1049021) B1049021
theorem B1354733 : Blo 413771 1354733 := bstep (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) B508025
theorem B2108429 : Blo 413771 2108429 := bstep (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) B790661
theorem B699475 : Blo 413771 699475 := bstep (se 1 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 699475 = 1049213) B1049213
theorem B1584269 : Blo 413771 1584269 := bstep (se 3 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 1584269 = 594101) B594101
theorem B699617 : Blo 413771 699617 := bstep (se 2 (by rfl) ⟨262356, by rfl⟩ : syracuseStep 699617 = 524713) B524713
theorem B994531 : Blo 413771 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B666929 : Blo 413771 666929 := bstep (se 2 (by rfl) ⟨250098, by rfl⟩ : syracuseStep 666929 = 500197) B500197
theorem B699745 : Blo 413771 699745 := bstep (se 2 (by rfl) ⟨262404, by rfl⟩ : syracuseStep 699745 = 524809) B524809
theorem B699779 : Blo 413771 699779 := bstep (se 1 (by rfl) ⟨524834, by rfl⟩ : syracuseStep 699779 = 1049669) B1049669
theorem B699907 : Blo 413771 699907 := bstep (se 1 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 699907 = 1049861) B1049861
theorem B1781297 : Blo 413771 1781297 := bstep (se 2 (by rfl) ⟨667986, by rfl⟩ : syracuseStep 1781297 = 1335973) B1335973
theorem B700049 : Blo 413771 700049 := bstep (se 2 (by rfl) ⟨262518, by rfl⟩ : syracuseStep 700049 = 525037) B525037
theorem B1355459 : Blo 413771 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B700177 : Blo 413771 700177 := bstep (se 2 (by rfl) ⟨262566, by rfl⟩ : syracuseStep 700177 = 525133) B525133
theorem B700211 : Blo 413771 700211 := bstep (se 1 (by rfl) ⟨525158, by rfl⟩ : syracuseStep 700211 = 1050317) B1050317
theorem B700339 : Blo 413771 700339 := bstep (se 1 (by rfl) ⟨525254, by rfl⟩ : syracuseStep 700339 = 1050509) B1050509
theorem B2371619 : Blo 413771 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B700481 : Blo 413771 700481 := bstep (se 2 (by rfl) ⟨262680, by rfl⟩ : syracuseStep 700481 = 525361) B525361
theorem B700609 : Blo 413771 700609 := bstep (se 2 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 700609 = 525457) B525457
theorem B700643 : Blo 413771 700643 := bstep (se 1 (by rfl) ⟨525482, by rfl⟩ : syracuseStep 700643 = 1050965) B1050965
theorem B700771 : Blo 413771 700771 := bstep (se 1 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 700771 = 1051157) B1051157
theorem B3977585 : Blo 413771 3977585 := bstep (se 2 (by rfl) ⟨1491594, by rfl⟩ : syracuseStep 3977585 = 2983189) B2983189
theorem B2404721 : Blo 413771 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B700913 : Blo 413771 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B3158513 : Blo 413771 3158513 := bstep (se 2 (by rfl) ⟨1184442, by rfl⟩ : syracuseStep 3158513 = 2368885) B2368885
theorem B668243 : Blo 413771 668243 := bstep (se 1 (by rfl) ⟨501182, by rfl⟩ : syracuseStep 668243 = 1002365) B1002365
theorem B701041 : Blo 413771 701041 := bstep (se 2 (by rfl) ⟨262890, by rfl⟩ : syracuseStep 701041 = 525781) B525781
theorem B701075 : Blo 413771 701075 := bstep (se 1 (by rfl) ⟨525806, by rfl⟩ : syracuseStep 701075 = 1051613) B1051613
theorem B701203 : Blo 413771 701203 := bstep (se 1 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 701203 = 1051805) B1051805
theorem B701345 : Blo 413771 701345 := bstep (se 2 (by rfl) ⟨263004, by rfl⟩ : syracuseStep 701345 = 526009) B526009
theorem B701473 : Blo 413771 701473 := bstep (se 2 (by rfl) ⟨263052, by rfl⟩ : syracuseStep 701473 = 526105) B526105
theorem B701507 : Blo 413771 701507 := bstep (se 1 (by rfl) ⟨526130, by rfl⟩ : syracuseStep 701507 = 1052261) B1052261
theorem B701635 : Blo 413771 701635 := bstep (se 1 (by rfl) ⟨526226, by rfl⟩ : syracuseStep 701635 = 1052453) B1052453
theorem B3880163 : Blo 413771 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B668915 : Blo 413771 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B931121 : Blo 413771 931121 := bstep (se 2 (by rfl) ⟨349170, by rfl⟩ : syracuseStep 931121 = 698341) B698341
theorem B931139 : Blo 413771 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B701777 : Blo 413771 701777 := bstep (se 2 (by rfl) ⟨263166, by rfl⟩ : syracuseStep 701777 = 526333) B526333
theorem B4502897 : Blo 413771 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B701905 : Blo 413771 701905 := bstep (se 2 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 701905 = 526429) B526429
theorem B701939 : Blo 413771 701939 := bstep (se 1 (by rfl) ⟨526454, by rfl⟩ : syracuseStep 701939 = 1052909) B1052909
theorem B3552781 : Blo 413771 3552781 := bstep (se 3 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 3552781 = 1332293) B1332293
theorem B931409 : Blo 413771 931409 := bstep (se 2 (by rfl) ⟨349278, by rfl⟩ : syracuseStep 931409 = 698557) B698557
theorem B931427 : Blo 413771 931427 := bstep (se 1 (by rfl) ⟨698570, by rfl⟩ : syracuseStep 931427 = 1397141) B1397141
theorem B702067 : Blo 413771 702067 := bstep (se 1 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 702067 = 1053101) B1053101
theorem B702209 : Blo 413771 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B2406179 : Blo 413771 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B931697 : Blo 413771 931697 := bstep (se 2 (by rfl) ⟨349386, by rfl⟩ : syracuseStep 931697 = 698773) B698773
theorem B2111345 : Blo 413771 2111345 := bstep (se 2 (by rfl) ⟨791754, by rfl⟩ : syracuseStep 2111345 = 1583509) B1583509
theorem B702337 : Blo 413771 702337 := bstep (se 2 (by rfl) ⟨263376, by rfl⟩ : syracuseStep 702337 = 526753) B526753
theorem B931715 : Blo 413771 931715 := bstep (se 1 (by rfl) ⟨698786, by rfl⟩ : syracuseStep 931715 = 1397573) B1397573
theorem B702371 : Blo 413771 702371 := bstep (se 1 (by rfl) ⟨526778, by rfl⟩ : syracuseStep 702371 = 1053557) B1053557
theorem B702499 : Blo 413771 702499 := bstep (se 1 (by rfl) ⟨526874, by rfl⟩ : syracuseStep 702499 = 1053749) B1053749
theorem B931985 : Blo 413771 931985 := bstep (se 2 (by rfl) ⟨349494, by rfl⟩ : syracuseStep 931985 = 698989) B698989
theorem B932003 : Blo 413771 932003 := bstep (se 1 (by rfl) ⟨699002, by rfl⟩ : syracuseStep 932003 = 1398005) B1398005
theorem B702641 : Blo 413771 702641 := bstep (se 2 (by rfl) ⟨263490, by rfl⟩ : syracuseStep 702641 = 526981) B526981
theorem B571571 : Blo 413771 571571 := bstep (se 1 (by rfl) ⟨428678, by rfl⟩ : syracuseStep 571571 = 857357) B857357
theorem B702769 : Blo 413771 702769 := bstep (se 2 (by rfl) ⟨263538, by rfl⟩ : syracuseStep 702769 = 527077) B527077
theorem B702803 : Blo 413771 702803 := bstep (se 1 (by rfl) ⟨527102, by rfl⟩ : syracuseStep 702803 = 1054205) B1054205
theorem B932273 : Blo 413771 932273 := bstep (se 2 (by rfl) ⟨349602, by rfl⟩ : syracuseStep 932273 = 699205) B699205
theorem B932291 : Blo 413771 932291 := bstep (se 1 (by rfl) ⟨699218, by rfl⟩ : syracuseStep 932291 = 1398437) B1398437
theorem B702931 : Blo 413771 702931 := bstep (se 1 (by rfl) ⟨527198, by rfl⟩ : syracuseStep 702931 = 1054397) B1054397
theorem B703073 : Blo 413771 703073 := bstep (se 2 (by rfl) ⟨263652, by rfl⟩ : syracuseStep 703073 = 527305) B527305
theorem B932561 : Blo 413771 932561 := bstep (se 2 (by rfl) ⟨349710, by rfl⟩ : syracuseStep 932561 = 699421) B699421
theorem B506579 : Blo 413771 506579 := bstep (se 1 (by rfl) ⟨379934, by rfl⟩ : syracuseStep 506579 = 759869) B759869
theorem B703201 : Blo 413771 703201 := bstep (se 2 (by rfl) ⟨263700, by rfl⟩ : syracuseStep 703201 = 527401) B527401
theorem B932579 : Blo 413771 932579 := bstep (se 1 (by rfl) ⟨699434, by rfl⟩ : syracuseStep 932579 = 1398869) B1398869
theorem B703235 : Blo 413771 703235 := bstep (se 1 (by rfl) ⟨527426, by rfl⟩ : syracuseStep 703235 = 1054853) B1054853
theorem B3554117 : Blo 413771 3554117 := bstep (se 4 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 3554117 = 666397) B666397
theorem B4275013 : Blo 413771 4275013 := bstep (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) B801565
theorem B703363 : Blo 413771 703363 := bstep (se 1 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 703363 = 1055045) B1055045
theorem B3259277 : Blo 413771 3259277 := bstep (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) B1222229
theorem B2243555 : Blo 413771 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B932849 : Blo 413771 932849 := bstep (se 2 (by rfl) ⟨349818, by rfl⟩ : syracuseStep 932849 = 699637) B699637
theorem B3783665 : Blo 413771 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B932867 : Blo 413771 932867 := bstep (se 1 (by rfl) ⟨699650, by rfl⟩ : syracuseStep 932867 = 1399301) B1399301
theorem B703505 : Blo 413771 703505 := bstep (se 2 (by rfl) ⟨263814, by rfl⟩ : syracuseStep 703505 = 527629) B527629
theorem B474131 : Blo 413771 474131 := bstep (se 1 (by rfl) ⟨355598, by rfl⟩ : syracuseStep 474131 = 711197) B711197
theorem B703633 : Blo 413771 703633 := bstep (se 2 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 703633 = 527725) B527725
theorem B703667 : Blo 413771 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B933137 : Blo 413771 933137 := bstep (se 2 (by rfl) ⟨349926, by rfl⟩ : syracuseStep 933137 = 699853) B699853
theorem B933155 : Blo 413771 933155 := bstep (se 1 (by rfl) ⟨699866, by rfl⟩ : syracuseStep 933155 = 1399733) B1399733
theorem B2112803 : Blo 413771 2112803 := bstep (se 1 (by rfl) ⟨1584602, by rfl⟩ : syracuseStep 2112803 = 3169205) B3169205
theorem B703795 : Blo 413771 703795 := bstep (se 1 (by rfl) ⟨527846, by rfl⟩ : syracuseStep 703795 = 1055693) B1055693
theorem B703937 : Blo 413771 703937 := bstep (se 2 (by rfl) ⟨263976, by rfl⟩ : syracuseStep 703937 = 527953) B527953
theorem B933425 : Blo 413771 933425 := bstep (se 2 (by rfl) ⟨350034, by rfl⟩ : syracuseStep 933425 = 700069) B700069
theorem B704065 : Blo 413771 704065 := bstep (se 2 (by rfl) ⟨264024, by rfl⟩ : syracuseStep 704065 = 528049) B528049
theorem B933443 : Blo 413771 933443 := bstep (se 1 (by rfl) ⟨700082, by rfl⟩ : syracuseStep 933443 = 1400165) B1400165
theorem B704099 : Blo 413771 704099 := bstep (se 1 (by rfl) ⟨528074, by rfl⟩ : syracuseStep 704099 = 1056149) B1056149
theorem B704227 : Blo 413771 704227 := bstep (se 1 (by rfl) ⟨528170, by rfl⟩ : syracuseStep 704227 = 1056341) B1056341
theorem B442099 : Blo 413771 442099 := bstep (se 1 (by rfl) ⟨331574, by rfl⟩ : syracuseStep 442099 = 663149) B663149
theorem B638707 : Blo 413771 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B933713 : Blo 413771 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B933731 : Blo 413771 933731 := bstep (se 1 (by rfl) ⟨700298, by rfl⟩ : syracuseStep 933731 = 1400597) B1400597
theorem B704369 : Blo 413771 704369 := bstep (se 2 (by rfl) ⟨264138, by rfl⟩ : syracuseStep 704369 = 528277) B528277
theorem B1261453 : Blo 413771 1261453 := bstep (se 3 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 1261453 = 473045) B473045
theorem B1425347 : Blo 413771 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B2670533 : Blo 413771 2670533 := bstep (se 4 (by rfl) ⟨250362, by rfl⟩ : syracuseStep 2670533 = 500725) B500725
theorem B2572273 : Blo 413771 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B704497 : Blo 413771 704497 := bstep (se 2 (by rfl) ⟨264186, by rfl⟩ : syracuseStep 704497 = 528373) B528373
theorem B442355 : Blo 413771 442355 := bstep (se 1 (by rfl) ⟨331766, by rfl⟩ : syracuseStep 442355 = 663533) B663533
theorem B1327117 : Blo 413771 1327117 := bstep (se 3 (by rfl) ⟨248834, by rfl⟩ : syracuseStep 1327117 = 497669) B497669
theorem B704531 : Blo 413771 704531 := bstep (se 1 (by rfl) ⟨528398, by rfl⟩ : syracuseStep 704531 = 1056797) B1056797
theorem B2113613 : Blo 413771 2113613 := bstep (se 3 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 2113613 = 792605) B792605
theorem B1261649 : Blo 413771 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B639073 : Blo 413771 639073 := bstep (se 2 (by rfl) ⟨239652, by rfl⟩ : syracuseStep 639073 = 479305) B479305
theorem B934001 : Blo 413771 934001 := bstep (se 2 (by rfl) ⟨350250, by rfl⟩ : syracuseStep 934001 = 700501) B700501
theorem B934019 : Blo 413771 934019 := bstep (se 1 (by rfl) ⟨700514, by rfl⟩ : syracuseStep 934019 = 1401029) B1401029
theorem B704659 : Blo 413771 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B5062837 : Blo 413771 5062837 := bstep (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) B474641
theorem B8110307 : Blo 413771 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B1065233 : Blo 413771 1065233 := bstep (se 2 (by rfl) ⟨399462, by rfl⟩ : syracuseStep 1065233 = 798925) B798925
theorem B704801 : Blo 413771 704801 := bstep (se 2 (by rfl) ⟨264300, by rfl⟩ : syracuseStep 704801 = 528601) B528601
theorem B2244941 : Blo 413771 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B934289 : Blo 413771 934289 := bstep (se 2 (by rfl) ⟨350358, by rfl⟩ : syracuseStep 934289 = 700717) B700717
theorem B704929 : Blo 413771 704929 := bstep (se 2 (by rfl) ⟨264348, by rfl⟩ : syracuseStep 704929 = 528697) B528697
theorem B934307 : Blo 413771 934307 := bstep (se 1 (by rfl) ⟨700730, by rfl⟩ : syracuseStep 934307 = 1401461) B1401461
theorem B704963 : Blo 413771 704963 := bstep (se 1 (by rfl) ⟨528722, by rfl⟩ : syracuseStep 704963 = 1057445) B1057445
theorem B901649 : Blo 413771 901649 := bstep (se 2 (by rfl) ⟨338118, by rfl⟩ : syracuseStep 901649 = 676237) B676237
theorem B1065521 : Blo 413771 1065521 := bstep (se 2 (by rfl) ⟨399570, by rfl⟩ : syracuseStep 1065521 = 799141) B799141
theorem B934577 : Blo 413771 934577 := bstep (se 2 (by rfl) ⟨350466, by rfl⟩ : syracuseStep 934577 = 700933) B700933
theorem B934595 : Blo 413771 934595 := bstep (se 1 (by rfl) ⟨700946, by rfl⟩ : syracuseStep 934595 = 1401893) B1401893
theorem B803537 : Blo 413771 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B443107 : Blo 413771 443107 := bstep (se 1 (by rfl) ⟨332330, by rfl⟩ : syracuseStep 443107 = 664661) B664661
theorem B4801265 : Blo 413771 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B1000259 : Blo 413771 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B1622897 : Blo 413771 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B1491853 : Blo 413771 1491853 := bstep (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) B559445
theorem B934865 : Blo 413771 934865 := bstep (se 2 (by rfl) ⟨350574, by rfl⟩ : syracuseStep 934865 = 701149) B701149
theorem B934883 : Blo 413771 934883 := bstep (se 1 (by rfl) ⟨701162, by rfl⟩ : syracuseStep 934883 = 1402325) B1402325
theorem B935153 : Blo 413771 935153 := bstep (se 2 (by rfl) ⟨350682, by rfl⟩ : syracuseStep 935153 = 701365) B701365
theorem B935171 : Blo 413771 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B1066321 : Blo 413771 1066321 := bstep (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) B799741
theorem B3982733 : Blo 413771 3982733 := bstep (se 3 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 3982733 = 1493525) B1493525
theorem B935441 : Blo 413771 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B935459 : Blo 413771 935459 := bstep (se 1 (by rfl) ⟨701594, by rfl⟩ : syracuseStep 935459 = 1403189) B1403189
theorem B1328899 : Blo 413771 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B1001219 : Blo 413771 1001219 := bstep (se 1 (by rfl) ⟨750914, by rfl⟩ : syracuseStep 1001219 = 1501829) B1501829
theorem B935729 : Blo 413771 935729 := bstep (se 2 (by rfl) ⟨350898, by rfl⟩ : syracuseStep 935729 = 701797) B701797
theorem B935747 : Blo 413771 935747 := bstep (se 1 (by rfl) ⟨701810, by rfl⟩ : syracuseStep 935747 = 1403621) B1403621
theorem B4474693 : Blo 413771 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B1001297 : Blo 413771 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B5392325 : Blo 413771 5392325 := bstep (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) B1011061
theorem B444371 : Blo 413771 444371 := bstep (se 1 (by rfl) ⟨333278, by rfl⟩ : syracuseStep 444371 = 666557) B666557
theorem B1066979 : Blo 413771 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B936017 : Blo 413771 936017 := bstep (se 2 (by rfl) ⟨351006, by rfl⟩ : syracuseStep 936017 = 702013) B702013
theorem B936035 : Blo 413771 936035 := bstep (se 1 (by rfl) ⟨702026, by rfl⟩ : syracuseStep 936035 = 1404053) B1404053
theorem B8407153 : Blo 413771 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B1427633 : Blo 413771 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B1329347 : Blo 413771 1329347 := bstep (se 1 (by rfl) ⟨997010, by rfl⟩ : syracuseStep 1329347 = 1994021) B1994021
theorem B936305 : Blo 413771 936305 := bstep (se 2 (by rfl) ⟨351114, by rfl⟩ : syracuseStep 936305 = 702229) B702229
theorem B936323 : Blo 413771 936323 := bstep (se 1 (by rfl) ⟨702242, by rfl⟩ : syracuseStep 936323 = 1404485) B1404485
theorem B8997317 : Blo 413771 8997317 := bstep (se 4 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 8997317 = 1686997) B1686997
theorem B1264241 : Blo 413771 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B936593 : Blo 413771 936593 := bstep (se 2 (by rfl) ⟨351222, by rfl⟩ : syracuseStep 936593 = 702445) B702445
theorem B936611 : Blo 413771 936611 := bstep (se 1 (by rfl) ⟨702458, by rfl⟩ : syracuseStep 936611 = 1404917) B1404917
theorem B445123 : Blo 413771 445123 := bstep (se 1 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 445123 = 667685) B667685
theorem B674659 : Blo 413771 674659 := bstep (se 1 (by rfl) ⟨505994, by rfl⟩ : syracuseStep 674659 = 1011989) B1011989
theorem B1493873 : Blo 413771 1493873 := bstep (se 2 (by rfl) ⟨560202, by rfl⟩ : syracuseStep 1493873 = 1120405) B1120405
theorem B936881 : Blo 413771 936881 := bstep (se 2 (by rfl) ⟨351330, by rfl⟩ : syracuseStep 936881 = 702661) B702661
theorem B936899 : Blo 413771 936899 := bstep (se 1 (by rfl) ⟨702674, by rfl⟩ : syracuseStep 936899 = 1405349) B1405349
theorem B937169 : Blo 413771 937169 := bstep (se 2 (by rfl) ⟨351438, by rfl⟩ : syracuseStep 937169 = 702877) B702877
theorem B937187 : Blo 413771 937187 := bstep (se 1 (by rfl) ⟨702890, by rfl⟩ : syracuseStep 937187 = 1405781) B1405781
theorem B1330577 : Blo 413771 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B1002979 : Blo 413771 1002979 := bstep (se 1 (by rfl) ⟨752234, by rfl⟩ : syracuseStep 1002979 = 1504469) B1504469
theorem B937457 : Blo 413771 937457 := bstep (se 2 (by rfl) ⟨351546, by rfl⟩ : syracuseStep 937457 = 703093) B703093
theorem B937475 : Blo 413771 937475 := bstep (se 1 (by rfl) ⟨703106, by rfl⟩ : syracuseStep 937475 = 1406213) B1406213
theorem B3559139 : Blo 413771 3559139 := bstep (se 1 (by rfl) ⟨2669354, by rfl⟩ : syracuseStep 3559139 = 5338709) B5338709
theorem B1396493 : Blo 413771 1396493 := bstep (se 3 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 1396493 = 523685) B523685
theorem B937745 : Blo 413771 937745 := bstep (se 2 (by rfl) ⟨351654, by rfl⟩ : syracuseStep 937745 = 703309) B703309
theorem B937763 : Blo 413771 937763 := bstep (se 1 (by rfl) ⟨703322, by rfl⟩ : syracuseStep 937763 = 1406645) B1406645
theorem B1396547 : Blo 413771 1396547 := bstep (se 1 (by rfl) ⟨1047410, by rfl⟩ : syracuseStep 1396547 = 2094821) B2094821
theorem B642883 : Blo 413771 642883 := bstep (se 1 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 642883 = 964325) B964325
theorem B1003441 : Blo 413771 1003441 := bstep (se 2 (by rfl) ⟨376290, by rfl⟩ : syracuseStep 1003441 = 752581) B752581
theorem B708563 : Blo 413771 708563 := bstep (se 1 (by rfl) ⟨531422, by rfl⟩ : syracuseStep 708563 = 1062845) B1062845
theorem B938033 : Blo 413771 938033 := bstep (se 2 (by rfl) ⟨351762, by rfl⟩ : syracuseStep 938033 = 703525) B703525
theorem B938051 : Blo 413771 938051 := bstep (se 1 (by rfl) ⟨703538, by rfl⟩ : syracuseStep 938051 = 1407077) B1407077
theorem B1396817 : Blo 413771 1396817 := bstep (se 2 (by rfl) ⟨523806, by rfl⟩ : syracuseStep 1396817 = 1047613) B1047613
theorem B413779 : Blo 413771 413779 := bstep (se 1 (by rfl) ⟨310334, by rfl⟩ : syracuseStep 413779 = 620669) B620669
theorem B413795 : Blo 413771 413795 := bstep (se 1 (by rfl) ⟨310346, by rfl⟩ : syracuseStep 413795 = 620693) B620693
theorem B413811 : Blo 413771 413811 := bstep (se 1 (by rfl) ⟨310358, by rfl⟩ : syracuseStep 413811 = 620717) B620717
theorem B413827 : Blo 413771 413827 := bstep (se 1 (by rfl) ⟨310370, by rfl⟩ : syracuseStep 413827 = 620741) B620741
theorem B413843 : Blo 413771 413843 := bstep (se 1 (by rfl) ⟨310382, by rfl⟩ : syracuseStep 413843 = 620765) B620765
theorem B413859 : Blo 413771 413859 := bstep (se 1 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 413859 = 620789) B620789
theorem B413875 : Blo 413771 413875 := bstep (se 1 (by rfl) ⟨310406, by rfl⟩ : syracuseStep 413875 = 620813) B620813
theorem B413891 : Blo 413771 413891 := bstep (se 1 (by rfl) ⟨310418, by rfl⟩ : syracuseStep 413891 = 620837) B620837
theorem B413907 : Blo 413771 413907 := bstep (se 1 (by rfl) ⟨310430, by rfl⟩ : syracuseStep 413907 = 620861) B620861
theorem B413923 : Blo 413771 413923 := bstep (se 1 (by rfl) ⟨310442, by rfl⟩ : syracuseStep 413923 = 620885) B620885
theorem B413939 : Blo 413771 413939 := bstep (se 1 (by rfl) ⟨310454, by rfl⟩ : syracuseStep 413939 = 620909) B620909
theorem B413955 : Blo 413771 413955 := bstep (se 1 (by rfl) ⟨310466, by rfl⟩ : syracuseStep 413955 = 620933) B620933
theorem B1331473 : Blo 413771 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B413971 : Blo 413771 413971 := bstep (se 1 (by rfl) ⟨310478, by rfl⟩ : syracuseStep 413971 = 620957) B620957
theorem B413987 : Blo 413771 413987 := bstep (se 1 (by rfl) ⟨310490, by rfl⟩ : syracuseStep 413987 = 620981) B620981
theorem B414003 : Blo 413771 414003 := bstep (se 1 (by rfl) ⟨310502, by rfl⟩ : syracuseStep 414003 = 621005) B621005
theorem B414019 : Blo 413771 414019 := bstep (se 1 (by rfl) ⟨310514, by rfl⟩ : syracuseStep 414019 = 621029) B621029
theorem B938321 : Blo 413771 938321 := bstep (se 2 (by rfl) ⟨351870, by rfl⟩ : syracuseStep 938321 = 703741) B703741
theorem B414035 : Blo 413771 414035 := bstep (se 1 (by rfl) ⟨310526, by rfl⟩ : syracuseStep 414035 = 621053) B621053
theorem B414051 : Blo 413771 414051 := bstep (se 1 (by rfl) ⟨310538, by rfl⟩ : syracuseStep 414051 = 621077) B621077
theorem B938339 : Blo 413771 938339 := bstep (se 1 (by rfl) ⟨703754, by rfl⟩ : syracuseStep 938339 = 1407509) B1407509
theorem B414067 : Blo 413771 414067 := bstep (se 1 (by rfl) ⟨310550, by rfl⟩ : syracuseStep 414067 = 621101) B621101
theorem B414083 : Blo 413771 414083 := bstep (se 1 (by rfl) ⟨310562, by rfl⟩ : syracuseStep 414083 = 621125) B621125
theorem B414099 : Blo 413771 414099 := bstep (se 1 (by rfl) ⟨310574, by rfl⟩ : syracuseStep 414099 = 621149) B621149
theorem B414115 : Blo 413771 414115 := bstep (se 1 (by rfl) ⟨310586, by rfl⟩ : syracuseStep 414115 = 621173) B621173
theorem B414131 : Blo 413771 414131 := bstep (se 1 (by rfl) ⟨310598, by rfl⟩ : syracuseStep 414131 = 621197) B621197
theorem B414147 : Blo 413771 414147 := bstep (se 1 (by rfl) ⟨310610, by rfl⟩ : syracuseStep 414147 = 621221) B621221
theorem B414163 : Blo 413771 414163 := bstep (se 1 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 414163 = 621245) B621245
theorem B414179 : Blo 413771 414179 := bstep (se 1 (by rfl) ⟨310634, by rfl⟩ : syracuseStep 414179 = 621269) B621269
theorem B414195 : Blo 413771 414195 := bstep (se 1 (by rfl) ⟨310646, by rfl⟩ : syracuseStep 414195 = 621293) B621293
theorem B414211 : Blo 413771 414211 := bstep (se 1 (by rfl) ⟨310658, by rfl⟩ : syracuseStep 414211 = 621317) B621317
theorem B414227 : Blo 413771 414227 := bstep (se 1 (by rfl) ⟨310670, by rfl⟩ : syracuseStep 414227 = 621341) B621341
theorem B414243 : Blo 413771 414243 := bstep (se 1 (by rfl) ⟨310682, by rfl⟩ : syracuseStep 414243 = 621365) B621365
theorem B1495601 : Blo 413771 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B414259 : Blo 413771 414259 := bstep (se 1 (by rfl) ⟨310694, by rfl⟩ : syracuseStep 414259 = 621389) B621389
theorem B414275 : Blo 413771 414275 := bstep (se 1 (by rfl) ⟨310706, by rfl⟩ : syracuseStep 414275 = 621413) B621413
theorem B414291 : Blo 413771 414291 := bstep (se 1 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 414291 = 621437) B621437
theorem B414307 : Blo 413771 414307 := bstep (se 1 (by rfl) ⟨310730, by rfl⟩ : syracuseStep 414307 = 621461) B621461
theorem B1397357 : Blo 413771 1397357 := bstep (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) B524009
theorem B938609 : Blo 413771 938609 := bstep (se 2 (by rfl) ⟨351978, by rfl⟩ : syracuseStep 938609 = 703957) B703957
theorem B414323 : Blo 413771 414323 := bstep (se 1 (by rfl) ⟨310742, by rfl⟩ : syracuseStep 414323 = 621485) B621485
theorem B414339 : Blo 413771 414339 := bstep (se 1 (by rfl) ⟨310754, by rfl⟩ : syracuseStep 414339 = 621509) B621509
theorem B938627 : Blo 413771 938627 := bstep (se 1 (by rfl) ⟨703970, by rfl⟩ : syracuseStep 938627 = 1407941) B1407941
theorem B414355 : Blo 413771 414355 := bstep (se 1 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 414355 = 621533) B621533
theorem B1397411 : Blo 413771 1397411 := bstep (se 1 (by rfl) ⟨1048058, by rfl⟩ : syracuseStep 1397411 = 2096117) B2096117
theorem B414371 : Blo 413771 414371 := bstep (se 1 (by rfl) ⟨310778, by rfl⟩ : syracuseStep 414371 = 621557) B621557
theorem B414387 : Blo 413771 414387 := bstep (se 1 (by rfl) ⟨310790, by rfl⟩ : syracuseStep 414387 = 621581) B621581
theorem B414403 : Blo 413771 414403 := bstep (se 1 (by rfl) ⟨310802, by rfl⟩ : syracuseStep 414403 = 621605) B621605
theorem B3986117 : Blo 413771 3986117 := bstep (se 4 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 3986117 = 747397) B747397
theorem B414419 : Blo 413771 414419 := bstep (se 1 (by rfl) ⟨310814, by rfl⟩ : syracuseStep 414419 = 621629) B621629
theorem B414435 : Blo 413771 414435 := bstep (se 1 (by rfl) ⟨310826, by rfl⟩ : syracuseStep 414435 = 621653) B621653
theorem B414451 : Blo 413771 414451 := bstep (se 1 (by rfl) ⟨310838, by rfl⟩ : syracuseStep 414451 = 621677) B621677
theorem B414467 : Blo 413771 414467 := bstep (se 1 (by rfl) ⟨310850, by rfl⟩ : syracuseStep 414467 = 621701) B621701
theorem B414483 : Blo 413771 414483 := bstep (se 1 (by rfl) ⟨310862, by rfl⟩ : syracuseStep 414483 = 621725) B621725
theorem B414499 : Blo 413771 414499 := bstep (se 1 (by rfl) ⟨310874, by rfl⟩ : syracuseStep 414499 = 621749) B621749
theorem B414515 : Blo 413771 414515 := bstep (se 1 (by rfl) ⟨310886, by rfl⟩ : syracuseStep 414515 = 621773) B621773
theorem B414531 : Blo 413771 414531 := bstep (se 1 (by rfl) ⟨310898, by rfl⟩ : syracuseStep 414531 = 621797) B621797
theorem B414547 : Blo 413771 414547 := bstep (se 1 (by rfl) ⟨310910, by rfl⟩ : syracuseStep 414547 = 621821) B621821
theorem B414563 : Blo 413771 414563 := bstep (se 1 (by rfl) ⟨310922, by rfl⟩ : syracuseStep 414563 = 621845) B621845
theorem B414579 : Blo 413771 414579 := bstep (se 1 (by rfl) ⟨310934, by rfl⟩ : syracuseStep 414579 = 621869) B621869
theorem B414595 : Blo 413771 414595 := bstep (se 1 (by rfl) ⟨310946, by rfl⟩ : syracuseStep 414595 = 621893) B621893
theorem B1069955 : Blo 413771 1069955 := bstep (se 1 (by rfl) ⟨802466, by rfl⟩ : syracuseStep 1069955 = 1604933) B1604933
theorem B938897 : Blo 413771 938897 := bstep (se 2 (by rfl) ⟨352086, by rfl⟩ : syracuseStep 938897 = 704173) B704173
theorem B414611 : Blo 413771 414611 := bstep (se 1 (by rfl) ⟨310958, by rfl⟩ : syracuseStep 414611 = 621917) B621917
theorem B414627 : Blo 413771 414627 := bstep (se 1 (by rfl) ⟨310970, by rfl⟩ : syracuseStep 414627 = 621941) B621941
theorem B938915 : Blo 413771 938915 := bstep (se 1 (by rfl) ⟨704186, by rfl⟩ : syracuseStep 938915 = 1408373) B1408373
theorem B1397681 : Blo 413771 1397681 := bstep (se 2 (by rfl) ⟨524130, by rfl⟩ : syracuseStep 1397681 = 1048261) B1048261
theorem B414643 : Blo 413771 414643 := bstep (se 1 (by rfl) ⟨310982, by rfl⟩ : syracuseStep 414643 = 621965) B621965
theorem B414659 : Blo 413771 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B414675 : Blo 413771 414675 := bstep (se 1 (by rfl) ⟨311006, by rfl⟩ : syracuseStep 414675 = 622013) B622013
theorem B414691 : Blo 413771 414691 := bstep (se 1 (by rfl) ⟨311018, by rfl⟩ : syracuseStep 414691 = 622037) B622037
theorem B414707 : Blo 413771 414707 := bstep (se 1 (by rfl) ⟨311030, by rfl⟩ : syracuseStep 414707 = 622061) B622061
theorem B414723 : Blo 413771 414723 := bstep (se 1 (by rfl) ⟨311042, by rfl⟩ : syracuseStep 414723 = 622085) B622085
theorem B414739 : Blo 413771 414739 := bstep (se 1 (by rfl) ⟨311054, by rfl⟩ : syracuseStep 414739 = 622109) B622109
theorem B414755 : Blo 413771 414755 := bstep (se 1 (by rfl) ⟨311066, by rfl⟩ : syracuseStep 414755 = 622133) B622133
theorem B414771 : Blo 413771 414771 := bstep (se 1 (by rfl) ⟨311078, by rfl⟩ : syracuseStep 414771 = 622157) B622157
theorem B414787 : Blo 413771 414787 := bstep (se 1 (by rfl) ⟨311090, by rfl⟩ : syracuseStep 414787 = 622181) B622181
theorem B414803 : Blo 413771 414803 := bstep (se 1 (by rfl) ⟨311102, by rfl⟩ : syracuseStep 414803 = 622205) B622205
theorem B414819 : Blo 413771 414819 := bstep (se 1 (by rfl) ⟨311114, by rfl⟩ : syracuseStep 414819 = 622229) B622229
theorem B414835 : Blo 413771 414835 := bstep (se 1 (by rfl) ⟨311126, by rfl⟩ : syracuseStep 414835 = 622253) B622253
theorem B414851 : Blo 413771 414851 := bstep (se 1 (by rfl) ⟨311138, by rfl⟩ : syracuseStep 414851 = 622277) B622277
theorem B414867 : Blo 413771 414867 := bstep (se 1 (by rfl) ⟨311150, by rfl⟩ : syracuseStep 414867 = 622301) B622301
theorem B414883 : Blo 413771 414883 := bstep (se 1 (by rfl) ⟨311162, by rfl⟩ : syracuseStep 414883 = 622325) B622325
theorem B939185 : Blo 413771 939185 := bstep (se 2 (by rfl) ⟨352194, by rfl⟩ : syracuseStep 939185 = 704389) B704389
theorem B414899 : Blo 413771 414899 := bstep (se 1 (by rfl) ⟨311174, by rfl⟩ : syracuseStep 414899 = 622349) B622349
theorem B414915 : Blo 413771 414915 := bstep (se 1 (by rfl) ⟨311186, by rfl⟩ : syracuseStep 414915 = 622373) B622373
theorem B939203 : Blo 413771 939203 := bstep (se 1 (by rfl) ⟨704402, by rfl⟩ : syracuseStep 939203 = 1408805) B1408805
theorem B414931 : Blo 413771 414931 := bstep (se 1 (by rfl) ⟨311198, by rfl⟩ : syracuseStep 414931 = 622397) B622397
theorem B414947 : Blo 413771 414947 := bstep (se 1 (by rfl) ⟨311210, by rfl⟩ : syracuseStep 414947 = 622421) B622421
theorem B414963 : Blo 413771 414963 := bstep (se 1 (by rfl) ⟨311222, by rfl⟩ : syracuseStep 414963 = 622445) B622445
theorem B414979 : Blo 413771 414979 := bstep (se 1 (by rfl) ⟨311234, by rfl⟩ : syracuseStep 414979 = 622469) B622469
theorem B414995 : Blo 413771 414995 := bstep (se 1 (by rfl) ⟨311246, by rfl⟩ : syracuseStep 414995 = 622493) B622493
theorem B415011 : Blo 413771 415011 := bstep (se 1 (by rfl) ⟨311258, by rfl⟩ : syracuseStep 415011 = 622517) B622517
theorem B415027 : Blo 413771 415027 := bstep (se 1 (by rfl) ⟨311270, by rfl⟩ : syracuseStep 415027 = 622541) B622541
theorem B415043 : Blo 413771 415043 := bstep (se 1 (by rfl) ⟨311282, by rfl⟩ : syracuseStep 415043 = 622565) B622565
theorem B415059 : Blo 413771 415059 := bstep (se 1 (by rfl) ⟨311294, by rfl⟩ : syracuseStep 415059 = 622589) B622589
theorem B415075 : Blo 413771 415075 := bstep (se 1 (by rfl) ⟨311306, by rfl⟩ : syracuseStep 415075 = 622613) B622613
theorem B415091 : Blo 413771 415091 := bstep (se 1 (by rfl) ⟨311318, by rfl⟩ : syracuseStep 415091 = 622637) B622637
theorem B415107 : Blo 413771 415107 := bstep (se 1 (by rfl) ⟨311330, by rfl⟩ : syracuseStep 415107 = 622661) B622661
theorem B415123 : Blo 413771 415123 := bstep (se 1 (by rfl) ⟨311342, by rfl⟩ : syracuseStep 415123 = 622685) B622685
theorem B415139 : Blo 413771 415139 := bstep (se 1 (by rfl) ⟨311354, by rfl⟩ : syracuseStep 415139 = 622709) B622709
theorem B415155 : Blo 413771 415155 := bstep (se 1 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 415155 = 622733) B622733
theorem B415171 : Blo 413771 415171 := bstep (se 1 (by rfl) ⟨311378, by rfl⟩ : syracuseStep 415171 = 622757) B622757
theorem B1398221 : Blo 413771 1398221 := bstep (se 3 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 1398221 = 524333) B524333
theorem B939473 : Blo 413771 939473 := bstep (se 2 (by rfl) ⟨352302, by rfl⟩ : syracuseStep 939473 = 704605) B704605
theorem B415187 : Blo 413771 415187 := bstep (se 1 (by rfl) ⟨311390, by rfl⟩ : syracuseStep 415187 = 622781) B622781
theorem B415203 : Blo 413771 415203 := bstep (se 1 (by rfl) ⟨311402, by rfl⟩ : syracuseStep 415203 = 622805) B622805
theorem B939491 : Blo 413771 939491 := bstep (se 1 (by rfl) ⟨704618, by rfl⟩ : syracuseStep 939491 = 1409237) B1409237
theorem B415219 : Blo 413771 415219 := bstep (se 1 (by rfl) ⟨311414, by rfl⟩ : syracuseStep 415219 = 622829) B622829
theorem B1398275 : Blo 413771 1398275 := bstep (se 1 (by rfl) ⟨1048706, by rfl⟩ : syracuseStep 1398275 = 2097413) B2097413
theorem B415235 : Blo 413771 415235 := bstep (se 1 (by rfl) ⟨311426, by rfl⟩ : syracuseStep 415235 = 622853) B622853
theorem B415251 : Blo 413771 415251 := bstep (se 1 (by rfl) ⟨311438, by rfl⟩ : syracuseStep 415251 = 622877) B622877
theorem B415267 : Blo 413771 415267 := bstep (se 1 (by rfl) ⟨311450, by rfl⟩ : syracuseStep 415267 = 622901) B622901
theorem B415283 : Blo 413771 415283 := bstep (se 1 (by rfl) ⟨311462, by rfl⟩ : syracuseStep 415283 = 622925) B622925
theorem B415299 : Blo 413771 415299 := bstep (se 1 (by rfl) ⟨311474, by rfl⟩ : syracuseStep 415299 = 622949) B622949
theorem B415315 : Blo 413771 415315 := bstep (se 1 (by rfl) ⟨311486, by rfl⟩ : syracuseStep 415315 = 622973) B622973
theorem B415331 : Blo 413771 415331 := bstep (se 1 (by rfl) ⟨311498, by rfl⟩ : syracuseStep 415331 = 622997) B622997
theorem B415347 : Blo 413771 415347 := bstep (se 1 (by rfl) ⟨311510, by rfl⟩ : syracuseStep 415347 = 623021) B623021
theorem B415363 : Blo 413771 415363 := bstep (se 1 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 415363 = 623045) B623045
theorem B415379 : Blo 413771 415379 := bstep (se 1 (by rfl) ⟨311534, by rfl⟩ : syracuseStep 415379 = 623069) B623069
theorem B415395 : Blo 413771 415395 := bstep (se 1 (by rfl) ⟨311546, by rfl⟩ : syracuseStep 415395 = 623093) B623093
theorem B415411 : Blo 413771 415411 := bstep (se 1 (by rfl) ⟨311558, by rfl⟩ : syracuseStep 415411 = 623117) B623117
theorem B415427 : Blo 413771 415427 := bstep (se 1 (by rfl) ⟨311570, by rfl⟩ : syracuseStep 415427 = 623141) B623141
theorem B415443 : Blo 413771 415443 := bstep (se 1 (by rfl) ⟨311582, by rfl⟩ : syracuseStep 415443 = 623165) B623165
theorem B415459 : Blo 413771 415459 := bstep (se 1 (by rfl) ⟨311594, by rfl⟩ : syracuseStep 415459 = 623189) B623189
theorem B939761 : Blo 413771 939761 := bstep (se 2 (by rfl) ⟨352410, by rfl⟩ : syracuseStep 939761 = 704821) B704821
theorem B415475 : Blo 413771 415475 := bstep (se 1 (by rfl) ⟨311606, by rfl⟩ : syracuseStep 415475 = 623213) B623213
theorem B415491 : Blo 413771 415491 := bstep (se 1 (by rfl) ⟨311618, by rfl⟩ : syracuseStep 415491 = 623237) B623237
theorem B939779 : Blo 413771 939779 := bstep (se 1 (by rfl) ⟨704834, by rfl⟩ : syracuseStep 939779 = 1409669) B1409669
theorem B1398545 : Blo 413771 1398545 := bstep (se 2 (by rfl) ⟨524454, by rfl⟩ : syracuseStep 1398545 = 1048909) B1048909
theorem B415507 : Blo 413771 415507 := bstep (se 1 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 415507 = 623261) B623261
theorem B415523 : Blo 413771 415523 := bstep (se 1 (by rfl) ⟨311642, by rfl⟩ : syracuseStep 415523 = 623285) B623285
theorem B1333037 : Blo 413771 1333037 := bstep (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) B499889
theorem B415539 : Blo 413771 415539 := bstep (se 1 (by rfl) ⟨311654, by rfl⟩ : syracuseStep 415539 = 623309) B623309
theorem B415555 : Blo 413771 415555 := bstep (se 1 (by rfl) ⟨311666, by rfl⟩ : syracuseStep 415555 = 623333) B623333
theorem B415571 : Blo 413771 415571 := bstep (se 1 (by rfl) ⟨311678, by rfl⟩ : syracuseStep 415571 = 623357) B623357
theorem B415587 : Blo 413771 415587 := bstep (se 1 (by rfl) ⟨311690, by rfl⟩ : syracuseStep 415587 = 623381) B623381
theorem B415603 : Blo 413771 415603 := bstep (se 1 (by rfl) ⟨311702, by rfl⟩ : syracuseStep 415603 = 623405) B623405
theorem B415619 : Blo 413771 415619 := bstep (se 1 (by rfl) ⟨311714, by rfl⟩ : syracuseStep 415619 = 623429) B623429
theorem B415635 : Blo 413771 415635 := bstep (se 1 (by rfl) ⟨311726, by rfl⟩ : syracuseStep 415635 = 623453) B623453
theorem B415651 : Blo 413771 415651 := bstep (se 1 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 415651 = 623477) B623477
theorem B415667 : Blo 413771 415667 := bstep (se 1 (by rfl) ⟨311750, by rfl⟩ : syracuseStep 415667 = 623501) B623501
theorem B415683 : Blo 413771 415683 := bstep (se 1 (by rfl) ⟨311762, by rfl⟩ : syracuseStep 415683 = 623525) B623525
theorem B415699 : Blo 413771 415699 := bstep (se 1 (by rfl) ⟨311774, by rfl⟩ : syracuseStep 415699 = 623549) B623549
theorem B841699 : Blo 413771 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B415715 : Blo 413771 415715 := bstep (se 1 (by rfl) ⟨311786, by rfl⟩ : syracuseStep 415715 = 623573) B623573
theorem B415731 : Blo 413771 415731 := bstep (se 1 (by rfl) ⟨311798, by rfl⟩ : syracuseStep 415731 = 623597) B623597
theorem B415747 : Blo 413771 415747 := bstep (se 1 (by rfl) ⟨311810, by rfl⟩ : syracuseStep 415747 = 623621) B623621
theorem B415763 : Blo 413771 415763 := bstep (se 1 (by rfl) ⟨311822, by rfl⟩ : syracuseStep 415763 = 623645) B623645
theorem B415779 : Blo 413771 415779 := bstep (se 1 (by rfl) ⟨311834, by rfl⟩ : syracuseStep 415779 = 623669) B623669
theorem B415795 : Blo 413771 415795 := bstep (se 1 (by rfl) ⟨311846, by rfl⟩ : syracuseStep 415795 = 623693) B623693
theorem B415811 : Blo 413771 415811 := bstep (se 1 (by rfl) ⟨311858, by rfl⟩ : syracuseStep 415811 = 623717) B623717
theorem B415827 : Blo 413771 415827 := bstep (se 1 (by rfl) ⟨311870, by rfl⟩ : syracuseStep 415827 = 623741) B623741
theorem B415843 : Blo 413771 415843 := bstep (se 1 (by rfl) ⟨311882, by rfl⟩ : syracuseStep 415843 = 623765) B623765
theorem B415859 : Blo 413771 415859 := bstep (se 1 (by rfl) ⟨311894, by rfl⟩ : syracuseStep 415859 = 623789) B623789
theorem B415875 : Blo 413771 415875 := bstep (se 1 (by rfl) ⟨311906, by rfl⟩ : syracuseStep 415875 = 623813) B623813
theorem B415891 : Blo 413771 415891 := bstep (se 1 (by rfl) ⟨311918, by rfl⟩ : syracuseStep 415891 = 623837) B623837
theorem B415907 : Blo 413771 415907 := bstep (se 1 (by rfl) ⟨311930, by rfl⟩ : syracuseStep 415907 = 623861) B623861
theorem B2250929 : Blo 413771 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B415923 : Blo 413771 415923 := bstep (se 1 (by rfl) ⟨311942, by rfl⟩ : syracuseStep 415923 = 623885) B623885
theorem B415939 : Blo 413771 415939 := bstep (se 1 (by rfl) ⟨311954, by rfl⟩ : syracuseStep 415939 = 623909) B623909
theorem B415955 : Blo 413771 415955 := bstep (se 1 (by rfl) ⟨311966, by rfl⟩ : syracuseStep 415955 = 623933) B623933
theorem B415971 : Blo 413771 415971 := bstep (se 1 (by rfl) ⟨311978, by rfl⟩ : syracuseStep 415971 = 623957) B623957
theorem B415987 : Blo 413771 415987 := bstep (se 1 (by rfl) ⟨311990, by rfl⟩ : syracuseStep 415987 = 623981) B623981
theorem B416003 : Blo 413771 416003 := bstep (se 1 (by rfl) ⟨312002, by rfl⟩ : syracuseStep 416003 = 624005) B624005
theorem B416019 : Blo 413771 416019 := bstep (se 1 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 416019 = 624029) B624029
theorem B416035 : Blo 413771 416035 := bstep (se 1 (by rfl) ⟨312026, by rfl⟩ : syracuseStep 416035 = 624053) B624053
theorem B1399085 : Blo 413771 1399085 := bstep (se 3 (by rfl) ⟨262328, by rfl⟩ : syracuseStep 1399085 = 524657) B524657
theorem B416051 : Blo 413771 416051 := bstep (se 1 (by rfl) ⟨312038, by rfl⟩ : syracuseStep 416051 = 624077) B624077
theorem B416067 : Blo 413771 416067 := bstep (se 1 (by rfl) ⟨312050, by rfl⟩ : syracuseStep 416067 = 624101) B624101
theorem B1136963 : Blo 413771 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B416083 : Blo 413771 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B1399139 : Blo 413771 1399139 := bstep (se 1 (by rfl) ⟨1049354, by rfl⟩ : syracuseStep 1399139 = 2098709) B2098709
theorem B416099 : Blo 413771 416099 := bstep (se 1 (by rfl) ⟨312074, by rfl⟩ : syracuseStep 416099 = 624149) B624149
theorem B416115 : Blo 413771 416115 := bstep (se 1 (by rfl) ⟨312086, by rfl⟩ : syracuseStep 416115 = 624173) B624173
theorem B416131 : Blo 413771 416131 := bstep (se 1 (by rfl) ⟨312098, by rfl⟩ : syracuseStep 416131 = 624197) B624197
theorem B416147 : Blo 413771 416147 := bstep (se 1 (by rfl) ⟨312110, by rfl⟩ : syracuseStep 416147 = 624221) B624221
theorem B416163 : Blo 413771 416163 := bstep (se 1 (by rfl) ⟨312122, by rfl⟩ : syracuseStep 416163 = 624245) B624245
theorem B1268141 : Blo 413771 1268141 := bstep (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) B475553
theorem B416179 : Blo 413771 416179 := bstep (se 1 (by rfl) ⟨312134, by rfl⟩ : syracuseStep 416179 = 624269) B624269
theorem B416195 : Blo 413771 416195 := bstep (se 1 (by rfl) ⟨312146, by rfl⟩ : syracuseStep 416195 = 624293) B624293
theorem B416211 : Blo 413771 416211 := bstep (se 1 (by rfl) ⟨312158, by rfl⟩ : syracuseStep 416211 = 624317) B624317
theorem B416227 : Blo 413771 416227 := bstep (se 1 (by rfl) ⟨312170, by rfl⟩ : syracuseStep 416227 = 624341) B624341
theorem B9624035 : Blo 413771 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B416243 : Blo 413771 416243 := bstep (se 1 (by rfl) ⟨312182, by rfl⟩ : syracuseStep 416243 = 624365) B624365
theorem B416259 : Blo 413771 416259 := bstep (se 1 (by rfl) ⟨312194, by rfl⟩ : syracuseStep 416259 = 624389) B624389
theorem B416275 : Blo 413771 416275 := bstep (se 1 (by rfl) ⟨312206, by rfl⟩ : syracuseStep 416275 = 624413) B624413
theorem B416291 : Blo 413771 416291 := bstep (se 1 (by rfl) ⟨312218, by rfl⟩ : syracuseStep 416291 = 624437) B624437
theorem B416307 : Blo 413771 416307 := bstep (se 1 (by rfl) ⟨312230, by rfl⟩ : syracuseStep 416307 = 624461) B624461
theorem B416323 : Blo 413771 416323 := bstep (se 1 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 416323 = 624485) B624485
theorem B416339 : Blo 413771 416339 := bstep (se 1 (by rfl) ⟨312254, by rfl⟩ : syracuseStep 416339 = 624509) B624509
theorem B416355 : Blo 413771 416355 := bstep (se 1 (by rfl) ⟨312266, by rfl⟩ : syracuseStep 416355 = 624533) B624533
theorem B1399409 : Blo 413771 1399409 := bstep (se 2 (by rfl) ⟨524778, by rfl⟩ : syracuseStep 1399409 = 1049557) B1049557
theorem B3005041 : Blo 413771 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B416371 : Blo 413771 416371 := bstep (se 1 (by rfl) ⟨312278, by rfl⟩ : syracuseStep 416371 = 624557) B624557
theorem B416387 : Blo 413771 416387 := bstep (se 1 (by rfl) ⟨312290, by rfl⟩ : syracuseStep 416387 = 624581) B624581
theorem B416403 : Blo 413771 416403 := bstep (se 1 (by rfl) ⟨312302, by rfl⟩ : syracuseStep 416403 = 624605) B624605
theorem B416419 : Blo 413771 416419 := bstep (se 1 (by rfl) ⟨312314, by rfl⟩ : syracuseStep 416419 = 624629) B624629
theorem B416435 : Blo 413771 416435 := bstep (se 1 (by rfl) ⟨312326, by rfl⟩ : syracuseStep 416435 = 624653) B624653
theorem B416451 : Blo 413771 416451 := bstep (se 1 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 416451 = 624677) B624677
theorem B416467 : Blo 413771 416467 := bstep (se 1 (by rfl) ⟨312350, by rfl⟩ : syracuseStep 416467 = 624701) B624701
theorem B416483 : Blo 413771 416483 := bstep (se 1 (by rfl) ⟨312362, by rfl⟩ : syracuseStep 416483 = 624725) B624725
theorem B416499 : Blo 413771 416499 := bstep (se 1 (by rfl) ⟨312374, by rfl⟩ : syracuseStep 416499 = 624749) B624749
theorem B416515 : Blo 413771 416515 := bstep (se 1 (by rfl) ⟨312386, by rfl⟩ : syracuseStep 416515 = 624773) B624773
theorem B416531 : Blo 413771 416531 := bstep (se 1 (by rfl) ⟨312398, by rfl⟩ : syracuseStep 416531 = 624797) B624797
theorem B416547 : Blo 413771 416547 := bstep (se 1 (by rfl) ⟨312410, by rfl⟩ : syracuseStep 416547 = 624821) B624821
theorem B416563 : Blo 413771 416563 := bstep (se 1 (by rfl) ⟨312422, by rfl⟩ : syracuseStep 416563 = 624845) B624845
theorem B416579 : Blo 413771 416579 := bstep (se 1 (by rfl) ⟨312434, by rfl⟩ : syracuseStep 416579 = 624869) B624869
theorem B416595 : Blo 413771 416595 := bstep (se 1 (by rfl) ⟨312446, by rfl⟩ : syracuseStep 416595 = 624893) B624893
theorem B416611 : Blo 413771 416611 := bstep (se 1 (by rfl) ⟨312458, by rfl⟩ : syracuseStep 416611 = 624917) B624917
theorem B416627 : Blo 413771 416627 := bstep (se 1 (by rfl) ⟨312470, by rfl⟩ : syracuseStep 416627 = 624941) B624941
theorem B416643 : Blo 413771 416643 := bstep (se 1 (by rfl) ⟨312482, by rfl⟩ : syracuseStep 416643 = 624965) B624965
theorem B416659 : Blo 413771 416659 := bstep (se 1 (by rfl) ⟨312494, by rfl⟩ : syracuseStep 416659 = 624989) B624989
theorem B416675 : Blo 413771 416675 := bstep (se 1 (by rfl) ⟨312506, by rfl⟩ : syracuseStep 416675 = 625013) B625013
theorem B416691 : Blo 413771 416691 := bstep (se 1 (by rfl) ⟨312518, by rfl⟩ : syracuseStep 416691 = 625037) B625037
theorem B416707 : Blo 413771 416707 := bstep (se 1 (by rfl) ⟨312530, by rfl⟩ : syracuseStep 416707 = 625061) B625061
theorem B416723 : Blo 413771 416723 := bstep (se 1 (by rfl) ⟨312542, by rfl⟩ : syracuseStep 416723 = 625085) B625085
theorem B416739 : Blo 413771 416739 := bstep (se 1 (by rfl) ⟨312554, by rfl⟩ : syracuseStep 416739 = 625109) B625109
theorem B416755 : Blo 413771 416755 := bstep (se 1 (by rfl) ⟨312566, by rfl⟩ : syracuseStep 416755 = 625133) B625133
theorem B416771 : Blo 413771 416771 := bstep (se 1 (by rfl) ⟨312578, by rfl⟩ : syracuseStep 416771 = 625157) B625157
theorem B416787 : Blo 413771 416787 := bstep (se 1 (by rfl) ⟨312590, by rfl⟩ : syracuseStep 416787 = 625181) B625181
theorem B416803 : Blo 413771 416803 := bstep (se 1 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 416803 = 625205) B625205
theorem B416819 : Blo 413771 416819 := bstep (se 1 (by rfl) ⟨312614, by rfl⟩ : syracuseStep 416819 = 625229) B625229
theorem B416835 : Blo 413771 416835 := bstep (se 1 (by rfl) ⟨312626, by rfl⟩ : syracuseStep 416835 = 625253) B625253
theorem B416851 : Blo 413771 416851 := bstep (se 1 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 416851 = 625277) B625277
theorem B416867 : Blo 413771 416867 := bstep (se 1 (by rfl) ⟨312650, by rfl⟩ : syracuseStep 416867 = 625301) B625301
theorem B416883 : Blo 413771 416883 := bstep (se 1 (by rfl) ⟨312662, by rfl⟩ : syracuseStep 416883 = 625325) B625325
theorem B416899 : Blo 413771 416899 := bstep (se 1 (by rfl) ⟨312674, by rfl⟩ : syracuseStep 416899 = 625349) B625349
theorem B1399949 : Blo 413771 1399949 := bstep (se 3 (by rfl) ⟨262490, by rfl⟩ : syracuseStep 1399949 = 524981) B524981
theorem B416915 : Blo 413771 416915 := bstep (se 1 (by rfl) ⟨312686, by rfl⟩ : syracuseStep 416915 = 625373) B625373
theorem B416931 : Blo 413771 416931 := bstep (se 1 (by rfl) ⟨312698, by rfl⟩ : syracuseStep 416931 = 625397) B625397
theorem B416947 : Blo 413771 416947 := bstep (se 1 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 416947 = 625421) B625421
theorem B1400003 : Blo 413771 1400003 := bstep (se 1 (by rfl) ⟨1050002, by rfl⟩ : syracuseStep 1400003 = 2100005) B2100005
theorem B416963 : Blo 413771 416963 := bstep (se 1 (by rfl) ⟨312722, by rfl⟩ : syracuseStep 416963 = 625445) B625445
theorem B416979 : Blo 413771 416979 := bstep (se 1 (by rfl) ⟨312734, by rfl⟩ : syracuseStep 416979 = 625469) B625469
theorem B416995 : Blo 413771 416995 := bstep (se 1 (by rfl) ⟨312746, by rfl⟩ : syracuseStep 416995 = 625493) B625493
theorem B417011 : Blo 413771 417011 := bstep (se 1 (by rfl) ⟨312758, by rfl⟩ : syracuseStep 417011 = 625517) B625517
theorem B417027 : Blo 413771 417027 := bstep (se 1 (by rfl) ⟨312770, by rfl⟩ : syracuseStep 417027 = 625541) B625541
theorem B417043 : Blo 413771 417043 := bstep (se 1 (by rfl) ⟨312782, by rfl⟩ : syracuseStep 417043 = 625565) B625565
theorem B417059 : Blo 413771 417059 := bstep (se 1 (by rfl) ⟨312794, by rfl⟩ : syracuseStep 417059 = 625589) B625589
theorem B417075 : Blo 413771 417075 := bstep (se 1 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 417075 = 625613) B625613
theorem B417091 : Blo 413771 417091 := bstep (se 1 (by rfl) ⟨312818, by rfl⟩ : syracuseStep 417091 = 625637) B625637
theorem B417107 : Blo 413771 417107 := bstep (se 1 (by rfl) ⟨312830, by rfl⟩ : syracuseStep 417107 = 625661) B625661
theorem B417123 : Blo 413771 417123 := bstep (se 1 (by rfl) ⟨312842, by rfl⟩ : syracuseStep 417123 = 625685) B625685
theorem B3562865 : Blo 413771 3562865 := bstep (se 2 (by rfl) ⟨1336074, by rfl⟩ : syracuseStep 3562865 = 2672149) B2672149
theorem B417139 : Blo 413771 417139 := bstep (se 1 (by rfl) ⟨312854, by rfl⟩ : syracuseStep 417139 = 625709) B625709
theorem B417155 : Blo 413771 417155 := bstep (se 1 (by rfl) ⟨312866, by rfl⟩ : syracuseStep 417155 = 625733) B625733
theorem B417171 : Blo 413771 417171 := bstep (se 1 (by rfl) ⟨312878, by rfl⟩ : syracuseStep 417171 = 625757) B625757
theorem B417187 : Blo 413771 417187 := bstep (se 1 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 417187 = 625781) B625781
theorem B417203 : Blo 413771 417203 := bstep (se 1 (by rfl) ⟨312902, by rfl⟩ : syracuseStep 417203 = 625805) B625805
theorem B417219 : Blo 413771 417219 := bstep (se 1 (by rfl) ⟨312914, by rfl⟩ : syracuseStep 417219 = 625829) B625829
theorem B1400273 : Blo 413771 1400273 := bstep (se 2 (by rfl) ⟨525102, by rfl⟩ : syracuseStep 1400273 = 1050205) B1050205
theorem B417235 : Blo 413771 417235 := bstep (se 1 (by rfl) ⟨312926, by rfl⟩ : syracuseStep 417235 = 625853) B625853
theorem B417251 : Blo 413771 417251 := bstep (se 1 (by rfl) ⟨312938, by rfl⟩ : syracuseStep 417251 = 625877) B625877
theorem B417267 : Blo 413771 417267 := bstep (se 1 (by rfl) ⟨312950, by rfl⟩ : syracuseStep 417267 = 625901) B625901
theorem B417283 : Blo 413771 417283 := bstep (se 1 (by rfl) ⟨312962, by rfl⟩ : syracuseStep 417283 = 625925) B625925
theorem B417299 : Blo 413771 417299 := bstep (se 1 (by rfl) ⟨312974, by rfl⟩ : syracuseStep 417299 = 625949) B625949
theorem B417315 : Blo 413771 417315 := bstep (se 1 (by rfl) ⟨312986, by rfl⟩ : syracuseStep 417315 = 625973) B625973
theorem B417331 : Blo 413771 417331 := bstep (se 1 (by rfl) ⟨312998, by rfl⟩ : syracuseStep 417331 = 625997) B625997
theorem B417347 : Blo 413771 417347 := bstep (se 1 (by rfl) ⟨313010, by rfl⟩ : syracuseStep 417347 = 626021) B626021
theorem B417363 : Blo 413771 417363 := bstep (se 1 (by rfl) ⟨313022, by rfl⟩ : syracuseStep 417363 = 626045) B626045
theorem B417379 : Blo 413771 417379 := bstep (se 1 (by rfl) ⟨313034, by rfl⟩ : syracuseStep 417379 = 626069) B626069
theorem B417395 : Blo 413771 417395 := bstep (se 1 (by rfl) ⟨313046, by rfl⟩ : syracuseStep 417395 = 626093) B626093
theorem B417411 : Blo 413771 417411 := bstep (se 1 (by rfl) ⟨313058, by rfl⟩ : syracuseStep 417411 = 626117) B626117
theorem B417427 : Blo 413771 417427 := bstep (se 1 (by rfl) ⟨313070, by rfl⟩ : syracuseStep 417427 = 626141) B626141
theorem B417443 : Blo 413771 417443 := bstep (se 1 (by rfl) ⟨313082, by rfl⟩ : syracuseStep 417443 = 626165) B626165
theorem B417459 : Blo 413771 417459 := bstep (se 1 (by rfl) ⟨313094, by rfl⟩ : syracuseStep 417459 = 626189) B626189
theorem B417475 : Blo 413771 417475 := bstep (se 1 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 417475 = 626213) B626213
theorem B417491 : Blo 413771 417491 := bstep (se 1 (by rfl) ⟨313118, by rfl⟩ : syracuseStep 417491 = 626237) B626237
theorem B417507 : Blo 413771 417507 := bstep (se 1 (by rfl) ⟨313130, by rfl⟩ : syracuseStep 417507 = 626261) B626261
theorem B417523 : Blo 413771 417523 := bstep (se 1 (by rfl) ⟨313142, by rfl⟩ : syracuseStep 417523 = 626285) B626285
theorem B417539 : Blo 413771 417539 := bstep (se 1 (by rfl) ⟨313154, by rfl⟩ : syracuseStep 417539 = 626309) B626309
theorem B417555 : Blo 413771 417555 := bstep (se 1 (by rfl) ⟨313166, by rfl⟩ : syracuseStep 417555 = 626333) B626333
theorem B417571 : Blo 413771 417571 := bstep (se 1 (by rfl) ⟨313178, by rfl⟩ : syracuseStep 417571 = 626357) B626357
theorem B417587 : Blo 413771 417587 := bstep (se 1 (by rfl) ⟨313190, by rfl⟩ : syracuseStep 417587 = 626381) B626381
theorem B417603 : Blo 413771 417603 := bstep (se 1 (by rfl) ⟨313202, by rfl⟩ : syracuseStep 417603 = 626405) B626405
theorem B417619 : Blo 413771 417619 := bstep (se 1 (by rfl) ⟨313214, by rfl⟩ : syracuseStep 417619 = 626429) B626429
theorem B417635 : Blo 413771 417635 := bstep (se 1 (by rfl) ⟨313226, by rfl⟩ : syracuseStep 417635 = 626453) B626453
theorem B417651 : Blo 413771 417651 := bstep (se 1 (by rfl) ⟨313238, by rfl⟩ : syracuseStep 417651 = 626477) B626477
theorem B417667 : Blo 413771 417667 := bstep (se 1 (by rfl) ⟨313250, by rfl⟩ : syracuseStep 417667 = 626501) B626501
theorem B417683 : Blo 413771 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B417699 : Blo 413771 417699 := bstep (se 1 (by rfl) ⟨313274, by rfl⟩ : syracuseStep 417699 = 626549) B626549
theorem B417715 : Blo 413771 417715 := bstep (se 1 (by rfl) ⟨313286, by rfl⟩ : syracuseStep 417715 = 626573) B626573
theorem B417731 : Blo 413771 417731 := bstep (se 1 (by rfl) ⟨313298, by rfl⟩ : syracuseStep 417731 = 626597) B626597
theorem B417747 : Blo 413771 417747 := bstep (se 1 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 417747 = 626621) B626621
theorem B417763 : Blo 413771 417763 := bstep (se 1 (by rfl) ⟨313322, by rfl⟩ : syracuseStep 417763 = 626645) B626645
theorem B1400813 : Blo 413771 1400813 := bstep (se 3 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 1400813 = 525305) B525305
theorem B1400867 : Blo 413771 1400867 := bstep (se 1 (by rfl) ⟨1050650, by rfl⟩ : syracuseStep 1400867 = 2101301) B2101301
theorem B2253005 : Blo 413771 2253005 := bstep (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) B844877
theorem B1335523 : Blo 413771 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B1401137 : Blo 413771 1401137 := bstep (se 2 (by rfl) ⟨525426, by rfl⟩ : syracuseStep 1401137 = 1050853) B1050853
theorem B745841 : Blo 413771 745841 := bstep (se 2 (by rfl) ⟨279690, by rfl⟩ : syracuseStep 745841 = 559381) B559381
theorem B1335665 : Blo 413771 1335665 := bstep (se 2 (by rfl) ⟨500874, by rfl⟩ : syracuseStep 1335665 = 1001749) B1001749
theorem B2318725 : Blo 413771 2318725 := bstep (se 4 (by rfl) ⟨217380, by rfl⟩ : syracuseStep 2318725 = 434761) B434761
theorem B1335779 : Blo 413771 1335779 := bstep (se 1 (by rfl) ⟨1001834, by rfl⟩ : syracuseStep 1335779 = 2003669) B2003669
theorem B10641941 : Blo 413771 10641941 := bstep (se 6 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 10641941 = 498841) B498841
theorem B713441 : Blo 413771 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B1401677 : Blo 413771 1401677 := bstep (se 3 (by rfl) ⟨262814, by rfl⟩ : syracuseStep 1401677 = 525629) B525629
theorem B1401731 : Blo 413771 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B1893347 : Blo 413771 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B1402001 : Blo 413771 1402001 := bstep (se 2 (by rfl) ⟨525750, by rfl⟩ : syracuseStep 1402001 = 1051501) B1051501
theorem B746705 : Blo 413771 746705 := bstep (se 2 (by rfl) ⟨280014, by rfl⟩ : syracuseStep 746705 = 560029) B560029
theorem B746929 : Blo 413771 746929 := bstep (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) B560197
theorem B1336753 : Blo 413771 1336753 := bstep (se 2 (by rfl) ⟨501282, by rfl⟩ : syracuseStep 1336753 = 1002565) B1002565
theorem B6809141 : Blo 413771 6809141 := bstep (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) B638357
theorem B1402541 : Blo 413771 1402541 := bstep (se 3 (by rfl) ⟨262976, by rfl⟩ : syracuseStep 1402541 = 525953) B525953
theorem B1402595 : Blo 413771 1402595 := bstep (se 1 (by rfl) ⟨1051946, by rfl⟩ : syracuseStep 1402595 = 2103893) B2103893
theorem B4056803 : Blo 413771 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B2320163 : Blo 413771 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B747427 : Blo 413771 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B1402865 : Blo 413771 1402865 := bstep (se 2 (by rfl) ⟨526074, by rfl⟩ : syracuseStep 1402865 = 1052149) B1052149
theorem B1796195 : Blo 413771 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B944465 : Blo 413771 944465 := bstep (se 2 (by rfl) ⟨354174, by rfl⟩ : syracuseStep 944465 = 708349) B708349
theorem B1894769 : Blo 413771 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B1403405 : Blo 413771 1403405 := bstep (se 3 (by rfl) ⟨263138, by rfl⟩ : syracuseStep 1403405 = 526277) B526277
theorem B1403459 : Blo 413771 1403459 := bstep (se 1 (by rfl) ⟨1052594, by rfl⟩ : syracuseStep 1403459 = 2105189) B2105189
theorem B5335733 : Blo 413771 5335733 := bstep (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) B500225
theorem B1403729 : Blo 413771 1403729 := bstep (se 2 (by rfl) ⟨526398, by rfl⟩ : syracuseStep 1403729 = 1052797) B1052797
theorem B421027 : Blo 413771 421027 := bstep (se 1 (by rfl) ⟨315770, by rfl⟩ : syracuseStep 421027 = 631541) B631541
theorem B1502435 : Blo 413771 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B4713713 : Blo 413771 4713713 := bstep (se 2 (by rfl) ⟨1767642, by rfl⟩ : syracuseStep 4713713 = 3535285) B3535285
theorem B3566861 : Blo 413771 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B1404269 : Blo 413771 1404269 := bstep (se 3 (by rfl) ⟨263300, by rfl⟩ : syracuseStep 1404269 = 526601) B526601
theorem B1404323 : Blo 413771 1404323 := bstep (se 1 (by rfl) ⟨1053242, by rfl⟩ : syracuseStep 1404323 = 2106485) B2106485
theorem B749027 : Blo 413771 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B1404593 : Blo 413771 1404593 := bstep (se 2 (by rfl) ⟨526722, by rfl⟩ : syracuseStep 1404593 = 1053445) B1053445
theorem B749617 : Blo 413771 749617 := bstep (se 2 (by rfl) ⟨281106, by rfl⟩ : syracuseStep 749617 = 562213) B562213
theorem B1405133 : Blo 413771 1405133 := bstep (se 3 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 1405133 = 526925) B526925
theorem B1405187 : Blo 413771 1405187 := bstep (se 1 (by rfl) ⟨1053890, by rfl⟩ : syracuseStep 1405187 = 2107781) B2107781
theorem B5402933 : Blo 413771 5402933 := bstep (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) B506525
theorem B1405457 : Blo 413771 1405457 := bstep (se 2 (by rfl) ⟨527046, by rfl⟩ : syracuseStep 1405457 = 1054093) B1054093
theorem B1012387 : Blo 413771 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B750563 : Blo 413771 750563 := bstep (se 1 (by rfl) ⟨562922, by rfl⟩ : syracuseStep 750563 = 1125845) B1125845
theorem B1405997 : Blo 413771 1405997 := bstep (se 3 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 1405997 = 527249) B527249
theorem B1406051 : Blo 413771 1406051 := bstep (se 1 (by rfl) ⟨1054538, by rfl⟩ : syracuseStep 1406051 = 2109077) B2109077
theorem B7599217 : Blo 413771 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B1537165 : Blo 413771 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B2651363 : Blo 413771 2651363 := bstep (se 1 (by rfl) ⟨1988522, by rfl⟩ : syracuseStep 2651363 = 3977045) B3977045
theorem B1406321 : Blo 413771 1406321 := bstep (se 2 (by rfl) ⟨527370, by rfl⟩ : syracuseStep 1406321 = 1054741) B1054741
theorem B751025 : Blo 413771 751025 := bstep (se 2 (by rfl) ⟨281634, by rfl⟩ : syracuseStep 751025 = 563269) B563269
theorem B2356721 : Blo 413771 2356721 := bstep (se 2 (by rfl) ⟨883770, by rfl⟩ : syracuseStep 2356721 = 1767541) B1767541
theorem B1504817 : Blo 413771 1504817 := bstep (se 2 (by rfl) ⟨564306, by rfl⟩ : syracuseStep 1504817 = 1128613) B1128613
theorem B718625 : Blo 413771 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B1406861 : Blo 413771 1406861 := bstep (se 3 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 1406861 = 527573) B527573
theorem B1898417 : Blo 413771 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B1406915 : Blo 413771 1406915 := bstep (se 1 (by rfl) ⟨1055186, by rfl⟩ : syracuseStep 1406915 = 2110373) B2110373
theorem B620657 : Blo 413771 620657 := bstep (se 2 (by rfl) ⟨232746, by rfl⟩ : syracuseStep 620657 = 465493) B465493
theorem B620675 : Blo 413771 620675 := bstep (se 1 (by rfl) ⟨465506, by rfl⟩ : syracuseStep 620675 = 931013) B931013
theorem B620705 : Blo 413771 620705 := bstep (se 2 (by rfl) ⟨232764, by rfl⟩ : syracuseStep 620705 = 465529) B465529
theorem B620723 : Blo 413771 620723 := bstep (se 1 (by rfl) ⟨465542, by rfl⟩ : syracuseStep 620723 = 931085) B931085
theorem B620753 : Blo 413771 620753 := bstep (se 2 (by rfl) ⟨232782, by rfl⟩ : syracuseStep 620753 = 465565) B465565
theorem B1407185 : Blo 413771 1407185 := bstep (se 2 (by rfl) ⟨527694, by rfl⟩ : syracuseStep 1407185 = 1055389) B1055389
theorem B620771 : Blo 413771 620771 := bstep (se 1 (by rfl) ⟨465578, by rfl⟩ : syracuseStep 620771 = 931157) B931157
theorem B620801 : Blo 413771 620801 := bstep (se 2 (by rfl) ⟨232800, by rfl⟩ : syracuseStep 620801 = 465601) B465601
theorem B620819 : Blo 413771 620819 := bstep (se 1 (by rfl) ⟨465614, by rfl⟩ : syracuseStep 620819 = 931229) B931229
theorem B620849 : Blo 413771 620849 := bstep (se 2 (by rfl) ⟨232818, by rfl⟩ : syracuseStep 620849 = 465637) B465637
theorem B620867 : Blo 413771 620867 := bstep (se 1 (by rfl) ⟨465650, by rfl⟩ : syracuseStep 620867 = 931301) B931301
theorem B620897 : Blo 413771 620897 := bstep (se 2 (by rfl) ⟨232836, by rfl⟩ : syracuseStep 620897 = 465673) B465673
theorem B620915 : Blo 413771 620915 := bstep (se 1 (by rfl) ⟨465686, by rfl⟩ : syracuseStep 620915 = 931373) B931373
theorem B620945 : Blo 413771 620945 := bstep (se 2 (by rfl) ⟨232854, by rfl⟩ : syracuseStep 620945 = 465709) B465709
theorem B620963 : Blo 413771 620963 := bstep (se 1 (by rfl) ⟨465722, by rfl⟩ : syracuseStep 620963 = 931445) B931445
theorem B620993 : Blo 413771 620993 := bstep (se 2 (by rfl) ⟨232872, by rfl⟩ : syracuseStep 620993 = 465745) B465745
theorem B621011 : Blo 413771 621011 := bstep (se 1 (by rfl) ⟨465758, by rfl⟩ : syracuseStep 621011 = 931517) B931517
theorem B621041 : Blo 413771 621041 := bstep (se 2 (by rfl) ⟨232890, by rfl⟩ : syracuseStep 621041 = 465781) B465781
theorem B719347 : Blo 413771 719347 := bstep (se 1 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 719347 = 1079021) B1079021
theorem B621059 : Blo 413771 621059 := bstep (se 1 (by rfl) ⟨465794, by rfl⟩ : syracuseStep 621059 = 931589) B931589
theorem B621089 : Blo 413771 621089 := bstep (se 2 (by rfl) ⟨232908, by rfl⟩ : syracuseStep 621089 = 465817) B465817
theorem B621107 : Blo 413771 621107 := bstep (se 1 (by rfl) ⟨465830, by rfl⟩ : syracuseStep 621107 = 931661) B931661
theorem B2652749 : Blo 413771 2652749 := bstep (se 3 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 2652749 = 994781) B994781
theorem B621137 : Blo 413771 621137 := bstep (se 2 (by rfl) ⟨232926, by rfl⟩ : syracuseStep 621137 = 465853) B465853
theorem B621155 : Blo 413771 621155 := bstep (se 1 (by rfl) ⟨465866, by rfl⟩ : syracuseStep 621155 = 931733) B931733
theorem B621185 : Blo 413771 621185 := bstep (se 2 (by rfl) ⟨232944, by rfl⟩ : syracuseStep 621185 = 465889) B465889
theorem B621203 : Blo 413771 621203 := bstep (se 1 (by rfl) ⟨465902, by rfl⟩ : syracuseStep 621203 = 931805) B931805
theorem B2095793 : Blo 413771 2095793 := bstep (se 2 (by rfl) ⟨785922, by rfl⟩ : syracuseStep 2095793 = 1571845) B1571845
theorem B621233 : Blo 413771 621233 := bstep (se 2 (by rfl) ⟨232962, by rfl⟩ : syracuseStep 621233 = 465925) B465925
theorem B916145 : Blo 413771 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B621251 : Blo 413771 621251 := bstep (se 1 (by rfl) ⟨465938, by rfl⟩ : syracuseStep 621251 = 931877) B931877
theorem B621281 : Blo 413771 621281 := bstep (se 2 (by rfl) ⟨232980, by rfl⟩ : syracuseStep 621281 = 465961) B465961
theorem B3144419 : Blo 413771 3144419 := bstep (se 1 (by rfl) ⟨2358314, by rfl⟩ : syracuseStep 3144419 = 4716629) B4716629
theorem B1407725 : Blo 413771 1407725 := bstep (se 3 (by rfl) ⟨263948, by rfl⟩ : syracuseStep 1407725 = 527897) B527897
theorem B621299 : Blo 413771 621299 := bstep (se 1 (by rfl) ⟨465974, by rfl⟩ : syracuseStep 621299 = 931949) B931949
theorem B621329 : Blo 413771 621329 := bstep (se 2 (by rfl) ⟨232998, by rfl⟩ : syracuseStep 621329 = 465997) B465997
theorem B1407779 : Blo 413771 1407779 := bstep (se 1 (by rfl) ⟨1055834, by rfl⟩ : syracuseStep 1407779 = 2111669) B2111669
theorem B1211171 : Blo 413771 1211171 := bstep (se 1 (by rfl) ⟨908378, by rfl⟩ : syracuseStep 1211171 = 1816757) B1816757
theorem B621347 : Blo 413771 621347 := bstep (se 1 (by rfl) ⟨466010, by rfl⟩ : syracuseStep 621347 = 932021) B932021
theorem B1571633 : Blo 413771 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B621377 : Blo 413771 621377 := bstep (se 2 (by rfl) ⟨233016, by rfl⟩ : syracuseStep 621377 = 466033) B466033
theorem B621395 : Blo 413771 621395 := bstep (se 1 (by rfl) ⟨466046, by rfl⟩ : syracuseStep 621395 = 932093) B932093
theorem B621425 : Blo 413771 621425 := bstep (se 2 (by rfl) ⟨233034, by rfl⟩ : syracuseStep 621425 = 466069) B466069
theorem B621443 : Blo 413771 621443 := bstep (se 1 (by rfl) ⟨466082, by rfl⟩ : syracuseStep 621443 = 932165) B932165
theorem B1178509 : Blo 413771 1178509 := bstep (se 3 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 1178509 = 441941) B441941
theorem B621473 : Blo 413771 621473 := bstep (se 2 (by rfl) ⟨233052, by rfl⟩ : syracuseStep 621473 = 466105) B466105
theorem B2358179 : Blo 413771 2358179 := bstep (se 1 (by rfl) ⟨1768634, by rfl⟩ : syracuseStep 2358179 = 3537269) B3537269
theorem B621491 : Blo 413771 621491 := bstep (se 1 (by rfl) ⟨466118, by rfl⟩ : syracuseStep 621491 = 932237) B932237
theorem B621521 : Blo 413771 621521 := bstep (se 2 (by rfl) ⟨233070, by rfl⟩ : syracuseStep 621521 = 466141) B466141
theorem B621539 : Blo 413771 621539 := bstep (se 1 (by rfl) ⟨466154, by rfl⟩ : syracuseStep 621539 = 932309) B932309
theorem B621569 : Blo 413771 621569 := bstep (se 2 (by rfl) ⟨233088, by rfl⟩ : syracuseStep 621569 = 466177) B466177
theorem B621587 : Blo 413771 621587 := bstep (se 1 (by rfl) ⟨466190, by rfl⟩ : syracuseStep 621587 = 932381) B932381
theorem B621617 : Blo 413771 621617 := bstep (se 2 (by rfl) ⟨233106, by rfl⟩ : syracuseStep 621617 = 466213) B466213
theorem B1408049 : Blo 413771 1408049 := bstep (se 2 (by rfl) ⟨528018, by rfl⟩ : syracuseStep 1408049 = 1056037) B1056037
theorem B621635 : Blo 413771 621635 := bstep (se 1 (by rfl) ⟨466226, by rfl⟩ : syracuseStep 621635 = 932453) B932453
theorem B621665 : Blo 413771 621665 := bstep (se 2 (by rfl) ⟨233124, by rfl⟩ : syracuseStep 621665 = 466249) B466249
theorem B3538019 : Blo 413771 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B621683 : Blo 413771 621683 := bstep (se 1 (by rfl) ⟨466262, by rfl⟩ : syracuseStep 621683 = 932525) B932525
theorem B621713 : Blo 413771 621713 := bstep (se 2 (by rfl) ⟨233142, by rfl⟩ : syracuseStep 621713 = 466285) B466285
theorem B621731 : Blo 413771 621731 := bstep (se 1 (by rfl) ⟨466298, by rfl⟩ : syracuseStep 621731 = 932597) B932597
theorem B621761 : Blo 413771 621761 := bstep (se 2 (by rfl) ⟨233160, by rfl⟩ : syracuseStep 621761 = 466321) B466321
theorem B621779 : Blo 413771 621779 := bstep (se 1 (by rfl) ⟨466334, by rfl⟩ : syracuseStep 621779 = 932669) B932669
theorem B621809 : Blo 413771 621809 := bstep (se 2 (by rfl) ⟨233178, by rfl⟩ : syracuseStep 621809 = 466357) B466357
theorem B621827 : Blo 413771 621827 := bstep (se 1 (by rfl) ⟨466370, by rfl⟩ : syracuseStep 621827 = 932741) B932741
theorem B621857 : Blo 413771 621857 := bstep (se 2 (by rfl) ⟨233196, by rfl⟩ : syracuseStep 621857 = 466393) B466393
theorem B621875 : Blo 413771 621875 := bstep (se 1 (by rfl) ⟨466406, by rfl⟩ : syracuseStep 621875 = 932813) B932813
theorem B621905 : Blo 413771 621905 := bstep (se 2 (by rfl) ⟨233214, by rfl⟩ : syracuseStep 621905 = 466429) B466429
theorem B621923 : Blo 413771 621923 := bstep (se 1 (by rfl) ⟨466442, by rfl⟩ : syracuseStep 621923 = 932885) B932885
theorem B621953 : Blo 413771 621953 := bstep (se 2 (by rfl) ⟨233232, by rfl⟩ : syracuseStep 621953 = 466465) B466465
theorem B621971 : Blo 413771 621971 := bstep (se 1 (by rfl) ⟨466478, by rfl⟩ : syracuseStep 621971 = 932957) B932957
theorem B622001 : Blo 413771 622001 := bstep (se 2 (by rfl) ⟨233250, by rfl⟩ : syracuseStep 622001 = 466501) B466501
theorem B622019 : Blo 413771 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B622049 : Blo 413771 622049 := bstep (se 2 (by rfl) ⟨233268, by rfl⟩ : syracuseStep 622049 = 466537) B466537
theorem B1048049 : Blo 413771 1048049 := bstep (se 2 (by rfl) ⟨393018, by rfl⟩ : syracuseStep 1048049 = 786037) B786037
theorem B622067 : Blo 413771 622067 := bstep (se 1 (by rfl) ⟨466550, by rfl⟩ : syracuseStep 622067 = 933101) B933101
theorem B622097 : Blo 413771 622097 := bstep (se 2 (by rfl) ⟨233286, by rfl⟩ : syracuseStep 622097 = 466573) B466573
theorem B1048099 : Blo 413771 1048099 := bstep (se 1 (by rfl) ⟨786074, by rfl⟩ : syracuseStep 1048099 = 1572149) B1572149
theorem B622115 : Blo 413771 622115 := bstep (se 1 (by rfl) ⟨466586, by rfl⟩ : syracuseStep 622115 = 933173) B933173
theorem B622145 : Blo 413771 622145 := bstep (se 2 (by rfl) ⟨233304, by rfl⟩ : syracuseStep 622145 = 466609) B466609
theorem B1408589 : Blo 413771 1408589 := bstep (se 3 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 1408589 = 528221) B528221
theorem B622163 : Blo 413771 622163 := bstep (se 1 (by rfl) ⟨466622, by rfl⟩ : syracuseStep 622163 = 933245) B933245
theorem B622193 : Blo 413771 622193 := bstep (se 2 (by rfl) ⟨233322, by rfl⟩ : syracuseStep 622193 = 466645) B466645
theorem B622211 : Blo 413771 622211 := bstep (se 1 (by rfl) ⟨466658, by rfl⟩ : syracuseStep 622211 = 933317) B933317
theorem B1408643 : Blo 413771 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B622241 : Blo 413771 622241 := bstep (se 2 (by rfl) ⟨233340, by rfl⟩ : syracuseStep 622241 = 466681) B466681
theorem B1048241 : Blo 413771 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B622259 : Blo 413771 622259 := bstep (se 1 (by rfl) ⟨466694, by rfl⟩ : syracuseStep 622259 = 933389) B933389
theorem B622289 : Blo 413771 622289 := bstep (se 2 (by rfl) ⟨233358, by rfl⟩ : syracuseStep 622289 = 466717) B466717
theorem B622307 : Blo 413771 622307 := bstep (se 1 (by rfl) ⟨466730, by rfl⟩ : syracuseStep 622307 = 933461) B933461
theorem B622337 : Blo 413771 622337 := bstep (se 2 (by rfl) ⟨233376, by rfl⟩ : syracuseStep 622337 = 466753) B466753
theorem B622355 : Blo 413771 622355 := bstep (se 1 (by rfl) ⟨466766, by rfl⟩ : syracuseStep 622355 = 933533) B933533
theorem B622385 : Blo 413771 622385 := bstep (se 2 (by rfl) ⟨233394, by rfl⟩ : syracuseStep 622385 = 466789) B466789
theorem B589619 : Blo 413771 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B622403 : Blo 413771 622403 := bstep (se 1 (by rfl) ⟨466802, by rfl⟩ : syracuseStep 622403 = 933605) B933605
theorem B786257 : Blo 413771 786257 := bstep (se 2 (by rfl) ⟨294846, by rfl⟩ : syracuseStep 786257 = 589693) B589693
theorem B622433 : Blo 413771 622433 := bstep (se 2 (by rfl) ⟨233412, by rfl⟩ : syracuseStep 622433 = 466825) B466825
theorem B622451 : Blo 413771 622451 := bstep (se 1 (by rfl) ⟨466838, by rfl⟩ : syracuseStep 622451 = 933677) B933677
theorem B622481 : Blo 413771 622481 := bstep (se 2 (by rfl) ⟨233430, by rfl⟩ : syracuseStep 622481 = 466861) B466861
theorem B1408913 : Blo 413771 1408913 := bstep (se 2 (by rfl) ⟨528342, by rfl⟩ : syracuseStep 1408913 = 1056685) B1056685
theorem B622499 : Blo 413771 622499 := bstep (se 1 (by rfl) ⟨466874, by rfl⟩ : syracuseStep 622499 = 933749) B933749
theorem B622529 : Blo 413771 622529 := bstep (se 2 (by rfl) ⟨233448, by rfl⟩ : syracuseStep 622529 = 466897) B466897
theorem B524227 : Blo 413771 524227 := bstep (se 1 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 524227 = 786341) B786341
theorem B622547 : Blo 413771 622547 := bstep (se 1 (by rfl) ⟨466910, by rfl⟩ : syracuseStep 622547 = 933821) B933821
theorem B622577 : Blo 413771 622577 := bstep (se 2 (by rfl) ⟨233466, by rfl⟩ : syracuseStep 622577 = 466933) B466933
theorem B1802225 : Blo 413771 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B1769489 : Blo 413771 1769489 := bstep (se 2 (by rfl) ⟨663558, by rfl⟩ : syracuseStep 1769489 = 1327117) B1327117
theorem B1409075 : Blo 413771 1409075 := bstep (se 1 (by rfl) ⟨1056806, by rfl⟩ : syracuseStep 1409075 = 2113613) B2113613
theorem B622667 : Blo 413771 622667 := bstep (se 1 (by rfl) ⟨467000, by rfl⟩ : syracuseStep 622667 = 934001) B934001
theorem B622679 : Blo 413771 622679 := bstep (se 1 (by rfl) ⟨467009, by rfl⟩ : syracuseStep 622679 = 934019) B934019
theorem B1048727 : Blo 413771 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B622745 : Blo 413771 622745 := bstep (se 2 (by rfl) ⟨233529, by rfl⟩ : syracuseStep 622745 = 467059) B467059
theorem B1179841 : Blo 413771 1179841 := bstep (se 2 (by rfl) ⟨442440, by rfl⟩ : syracuseStep 1179841 = 884881) B884881
theorem B6750449 : Blo 413771 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B3997957 : Blo 413771 3997957 := bstep (se 4 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 3997957 = 749617) B749617
theorem B4751621 : Blo 413771 4751621 := bstep (se 4 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 4751621 = 890929) B890929
theorem B622859 : Blo 413771 622859 := bstep (se 1 (by rfl) ⟨467144, by rfl⟩ : syracuseStep 622859 = 934289) B934289
theorem B622871 : Blo 413771 622871 := bstep (se 1 (by rfl) ⟨467153, by rfl⟩ : syracuseStep 622871 = 934307) B934307
theorem B1409345 : Blo 413771 1409345 := bstep (se 2 (by rfl) ⟨528504, by rfl⟩ : syracuseStep 1409345 = 1057009) B1057009
theorem B622937 : Blo 413771 622937 := bstep (se 2 (by rfl) ⟨233601, by rfl⟩ : syracuseStep 622937 = 467203) B467203
theorem B786827 : Blo 413771 786827 := bstep (se 1 (by rfl) ⟨590120, by rfl⟩ : syracuseStep 786827 = 1180241) B1180241
theorem B623051 : Blo 413771 623051 := bstep (se 1 (by rfl) ⟨467288, by rfl⟩ : syracuseStep 623051 = 934577) B934577
theorem B623063 : Blo 413771 623063 := bstep (se 1 (by rfl) ⟨467297, by rfl⟩ : syracuseStep 623063 = 934595) B934595
theorem B3408389 : Blo 413771 3408389 := bstep (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) B639073
theorem B1180183 : Blo 413771 1180183 := bstep (se 1 (by rfl) ⟨885137, by rfl⟩ : syracuseStep 1180183 = 1770275) B1770275
theorem B623129 : Blo 413771 623129 := bstep (se 2 (by rfl) ⟨233673, by rfl⟩ : syracuseStep 623129 = 467347) B467347
theorem B787009 : Blo 413771 787009 := bstep (se 2 (by rfl) ⟨295128, by rfl⟩ : syracuseStep 787009 = 590257) B590257
theorem B524875 : Blo 413771 524875 := bstep (se 1 (by rfl) ⟨393656, by rfl⟩ : syracuseStep 524875 = 787313) B787313
theorem B1081931 : Blo 413771 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B21627485 : Blo 413771 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B623243 : Blo 413771 623243 := bstep (se 1 (by rfl) ⟨467432, by rfl⟩ : syracuseStep 623243 = 934865) B934865
theorem B623255 : Blo 413771 623255 := bstep (se 1 (by rfl) ⟨467441, by rfl⟩ : syracuseStep 623255 = 934883) B934883
theorem B623321 : Blo 413771 623321 := bstep (se 2 (by rfl) ⟨233745, by rfl⟩ : syracuseStep 623321 = 467491) B467491
theorem B1049395 : Blo 413771 1049395 := bstep (se 1 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 1049395 = 1574093) B1574093
theorem B623435 : Blo 413771 623435 := bstep (se 1 (by rfl) ⟨467576, by rfl⟩ : syracuseStep 623435 = 935153) B935153
theorem B525143 : Blo 413771 525143 := bstep (se 1 (by rfl) ⟨393857, by rfl⟩ : syracuseStep 525143 = 787715) B787715
theorem B623447 : Blo 413771 623447 := bstep (se 1 (by rfl) ⟨467585, by rfl⟩ : syracuseStep 623447 = 935171) B935171
theorem B1409885 : Blo 413771 1409885 := bstep (se 3 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 1409885 = 528707) B528707
theorem B623513 : Blo 413771 623513 := bstep (se 2 (by rfl) ⟨233817, by rfl⟩ : syracuseStep 623513 = 467635) B467635
theorem B2655155 : Blo 413771 2655155 := bstep (se 1 (by rfl) ⟨1991366, by rfl⟩ : syracuseStep 2655155 = 3982733) B3982733
theorem B1049537 : Blo 413771 1049537 := bstep (se 2 (by rfl) ⟨393576, by rfl⟩ : syracuseStep 1049537 = 787153) B787153
theorem B590809 : Blo 413771 590809 := bstep (se 2 (by rfl) ⟨221553, by rfl⟩ : syracuseStep 590809 = 443107) B443107
theorem B787457 : Blo 413771 787457 := bstep (se 2 (by rfl) ⟨295296, by rfl⟩ : syracuseStep 787457 = 590593) B590593
theorem B623627 : Blo 413771 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B623639 : Blo 413771 623639 := bstep (se 1 (by rfl) ⟨467729, by rfl⟩ : syracuseStep 623639 = 935459) B935459
theorem B590923 : Blo 413771 590923 := bstep (se 1 (by rfl) ⟨443192, by rfl⟩ : syracuseStep 590923 = 886385) B886385
theorem B623705 : Blo 413771 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B623819 : Blo 413771 623819 := bstep (se 1 (by rfl) ⟨467864, by rfl⟩ : syracuseStep 623819 = 935729) B935729
theorem B623831 : Blo 413771 623831 := bstep (se 1 (by rfl) ⟨467873, by rfl⟩ : syracuseStep 623831 = 935747) B935747
theorem B1180889 : Blo 413771 1180889 := bstep (se 2 (by rfl) ⟨442833, by rfl⟩ : syracuseStep 1180889 = 885667) B885667
theorem B623897 : Blo 413771 623897 := bstep (se 2 (by rfl) ⟨233961, by rfl⟩ : syracuseStep 623897 = 467923) B467923
theorem B787799 : Blo 413771 787799 := bstep (se 1 (by rfl) ⟨590849, by rfl⟩ : syracuseStep 787799 = 1181699) B1181699
theorem B6423907 : Blo 413771 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B886145 : Blo 413771 886145 := bstep (se 2 (by rfl) ⟨332304, by rfl⟩ : syracuseStep 886145 = 664609) B664609
theorem B1574275 : Blo 413771 1574275 := bstep (se 1 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 1574275 = 2361413) B2361413
theorem B624011 : Blo 413771 624011 := bstep (se 1 (by rfl) ⟨468008, by rfl⟩ : syracuseStep 624011 = 936017) B936017
theorem B624023 : Blo 413771 624023 := bstep (se 1 (by rfl) ⟨468017, by rfl⟩ : syracuseStep 624023 = 936035) B936035
theorem B951755 : Blo 413771 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B886231 : Blo 413771 886231 := bstep (se 1 (by rfl) ⟨664673, by rfl⟩ : syracuseStep 886231 = 1329347) B1329347
theorem B624089 : Blo 413771 624089 := bstep (se 2 (by rfl) ⟨234033, by rfl⟩ : syracuseStep 624089 = 468067) B468067
theorem B525847 : Blo 413771 525847 := bstep (se 1 (by rfl) ⟨394385, by rfl⟩ : syracuseStep 525847 = 788771) B788771
theorem B624203 : Blo 413771 624203 := bstep (se 1 (by rfl) ⟨468152, by rfl⟩ : syracuseStep 624203 = 936305) B936305
theorem B624215 : Blo 413771 624215 := bstep (se 1 (by rfl) ⟨468161, by rfl⟩ : syracuseStep 624215 = 936323) B936323
theorem B5998211 : Blo 413771 5998211 := bstep (se 1 (by rfl) ⟨4498658, by rfl⟩ : syracuseStep 5998211 = 8997317) B8997317
theorem B624281 : Blo 413771 624281 := bstep (se 2 (by rfl) ⟨234105, by rfl⟩ : syracuseStep 624281 = 468211) B468211
theorem B1574579 : Blo 413771 1574579 := bstep (se 1 (by rfl) ⟨1180934, by rfl⟩ : syracuseStep 1574579 = 2361869) B2361869
theorem B624395 : Blo 413771 624395 := bstep (se 1 (by rfl) ⟨468296, by rfl⟩ : syracuseStep 624395 = 936593) B936593
theorem B624407 : Blo 413771 624407 := bstep (se 1 (by rfl) ⟨468305, by rfl⟩ : syracuseStep 624407 = 936611) B936611
theorem B624473 : Blo 413771 624473 := bstep (se 2 (by rfl) ⟨234177, by rfl⟩ : syracuseStep 624473 = 468355) B468355
theorem B6096757 : Blo 413771 6096757 := bstep (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) B571571
theorem B624587 : Blo 413771 624587 := bstep (se 1 (by rfl) ⟨468440, by rfl⟩ : syracuseStep 624587 = 936881) B936881
theorem B624599 : Blo 413771 624599 := bstep (se 1 (by rfl) ⟨468449, by rfl⟩ : syracuseStep 624599 = 936899) B936899
theorem B788467 : Blo 413771 788467 := bstep (se 1 (by rfl) ⟨591350, by rfl⟩ : syracuseStep 788467 = 1182701) B1182701
theorem B854039 : Blo 413771 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B624665 : Blo 413771 624665 := bstep (se 2 (by rfl) ⟨234249, by rfl⟩ : syracuseStep 624665 = 468499) B468499
theorem B3147821 : Blo 413771 3147821 := bstep (se 3 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 3147821 = 1180433) B1180433
theorem B624779 : Blo 413771 624779 := bstep (se 1 (by rfl) ⟨468584, by rfl⟩ : syracuseStep 624779 = 937169) B937169
theorem B624791 : Blo 413771 624791 := bstep (se 1 (by rfl) ⟨468593, by rfl⟩ : syracuseStep 624791 = 937187) B937187
theorem B1050803 : Blo 413771 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B624857 : Blo 413771 624857 := bstep (se 2 (by rfl) ⟨234321, by rfl⟩ : syracuseStep 624857 = 468643) B468643
theorem B887051 : Blo 413771 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B1575233 : Blo 413771 1575233 := bstep (se 2 (by rfl) ⟨590712, by rfl⟩ : syracuseStep 1575233 = 1181425) B1181425
theorem B624971 : Blo 413771 624971 := bstep (se 1 (by rfl) ⟨468728, by rfl⟩ : syracuseStep 624971 = 937457) B937457
theorem B624983 : Blo 413771 624983 := bstep (se 1 (by rfl) ⟨468737, by rfl⟩ : syracuseStep 624983 = 937475) B937475
theorem B1771865 : Blo 413771 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B592267 : Blo 413771 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B625049 : Blo 413771 625049 := bstep (se 2 (by rfl) ⟨234393, by rfl⟩ : syracuseStep 625049 = 468787) B468787
theorem B1771949 : Blo 413771 1771949 := bstep (se 3 (by rfl) ⟨332240, by rfl⟩ : syracuseStep 1771949 = 664481) B664481
theorem B5966257 : Blo 413771 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B788915 : Blo 413771 788915 := bstep (se 1 (by rfl) ⟨591686, by rfl⟩ : syracuseStep 788915 = 1183373) B1183373
theorem B788953 : Blo 413771 788953 := bstep (se 2 (by rfl) ⟨295857, by rfl⟩ : syracuseStep 788953 = 591715) B591715
theorem B625163 : Blo 413771 625163 := bstep (se 1 (by rfl) ⟨468872, by rfl⟩ : syracuseStep 625163 = 937745) B937745
theorem B625175 : Blo 413771 625175 := bstep (se 1 (by rfl) ⟨468881, by rfl⟩ : syracuseStep 625175 = 937763) B937763
theorem B625241 : Blo 413771 625241 := bstep (se 2 (by rfl) ⟨234465, by rfl⟩ : syracuseStep 625241 = 468931) B468931
theorem B2099843 : Blo 413771 2099843 := bstep (se 1 (by rfl) ⟨1574882, by rfl⟩ : syracuseStep 2099843 = 3149765) B3149765
theorem B592535 : Blo 413771 592535 := bstep (se 1 (by rfl) ⟨444401, by rfl⟩ : syracuseStep 592535 = 888803) B888803
theorem B1051339 : Blo 413771 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B625355 : Blo 413771 625355 := bstep (se 1 (by rfl) ⟨469016, by rfl⟩ : syracuseStep 625355 = 938033) B938033
theorem B625367 : Blo 413771 625367 := bstep (se 1 (by rfl) ⟨469025, by rfl⟩ : syracuseStep 625367 = 938051) B938051
theorem B625433 : Blo 413771 625433 := bstep (se 2 (by rfl) ⟨234537, by rfl⟩ : syracuseStep 625433 = 469075) B469075
theorem B461611 : Blo 413771 461611 := bstep (se 1 (by rfl) ⟨346208, by rfl⟩ : syracuseStep 461611 = 692417) B692417
theorem B11209537 : Blo 413771 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B1182529 : Blo 413771 1182529 := bstep (se 2 (by rfl) ⟨443448, by rfl⟩ : syracuseStep 1182529 = 886897) B886897
theorem B1051481 : Blo 413771 1051481 := bstep (se 2 (by rfl) ⟨394305, by rfl⟩ : syracuseStep 1051481 = 788611) B788611
theorem B625547 : Blo 413771 625547 := bstep (se 1 (by rfl) ⟨469160, by rfl⟩ : syracuseStep 625547 = 938321) B938321
theorem B625559 : Blo 413771 625559 := bstep (se 1 (by rfl) ⟨469169, by rfl⟩ : syracuseStep 625559 = 938339) B938339
theorem B789401 : Blo 413771 789401 := bstep (se 2 (by rfl) ⟨296025, by rfl⟩ : syracuseStep 789401 = 592051) B592051
theorem B625625 : Blo 413771 625625 := bstep (se 2 (by rfl) ⟨234609, by rfl⟩ : syracuseStep 625625 = 469219) B469219
theorem B625739 : Blo 413771 625739 := bstep (se 1 (by rfl) ⟨469304, by rfl⟩ : syracuseStep 625739 = 938609) B938609
theorem B625751 : Blo 413771 625751 := bstep (se 1 (by rfl) ⟨469313, by rfl⟩ : syracuseStep 625751 = 938627) B938627
theorem B2657411 : Blo 413771 2657411 := bstep (se 1 (by rfl) ⟨1993058, by rfl⟩ : syracuseStep 2657411 = 3986117) B3986117
theorem B625817 : Blo 413771 625817 := bstep (se 2 (by rfl) ⟨234681, by rfl⟩ : syracuseStep 625817 = 469363) B469363
theorem B527563 : Blo 413771 527563 := bstep (se 1 (by rfl) ⟨395672, by rfl⟩ : syracuseStep 527563 = 791345) B791345
theorem B888025 : Blo 413771 888025 := bstep (se 2 (by rfl) ⟨333009, by rfl⟩ : syracuseStep 888025 = 666019) B666019
theorem B625931 : Blo 413771 625931 := bstep (se 1 (by rfl) ⟨469448, by rfl⟩ : syracuseStep 625931 = 938897) B938897
theorem B625943 : Blo 413771 625943 := bstep (se 1 (by rfl) ⟨469457, by rfl⟩ : syracuseStep 625943 = 938915) B938915
theorem B626009 : Blo 413771 626009 := bstep (se 2 (by rfl) ⟨234753, by rfl⟩ : syracuseStep 626009 = 469507) B469507
theorem B626123 : Blo 413771 626123 := bstep (se 1 (by rfl) ⟨469592, by rfl⟩ : syracuseStep 626123 = 939185) B939185
theorem B626135 : Blo 413771 626135 := bstep (se 1 (by rfl) ⟨469601, by rfl⟩ : syracuseStep 626135 = 939203) B939203
theorem B626201 : Blo 413771 626201 := bstep (se 2 (by rfl) ⟨234825, by rfl⟩ : syracuseStep 626201 = 469651) B469651
theorem B1576493 : Blo 413771 1576493 := bstep (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) B591185
theorem B1576523 : Blo 413771 1576523 := bstep (se 1 (by rfl) ⟨1182392, by rfl⟩ : syracuseStep 1576523 = 2364785) B2364785
theorem B593497 : Blo 413771 593497 := bstep (se 2 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 593497 = 445123) B445123
theorem B790145 : Blo 413771 790145 := bstep (se 2 (by rfl) ⟨296304, by rfl⟩ : syracuseStep 790145 = 592609) B592609
theorem B626315 : Blo 413771 626315 := bstep (se 1 (by rfl) ⟨469736, by rfl⟩ : syracuseStep 626315 = 939473) B939473
theorem B1052311 : Blo 413771 1052311 := bstep (se 1 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 1052311 = 1578467) B1578467
theorem B626327 : Blo 413771 626327 := bstep (se 1 (by rfl) ⟨469745, by rfl⟩ : syracuseStep 626327 = 939491) B939491
theorem B626393 : Blo 413771 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B626507 : Blo 413771 626507 := bstep (se 1 (by rfl) ⟨469880, by rfl⟩ : syracuseStep 626507 = 939761) B939761
theorem B626519 : Blo 413771 626519 := bstep (se 1 (by rfl) ⟨469889, by rfl⟩ : syracuseStep 626519 = 939779) B939779
theorem B790411 : Blo 413771 790411 := bstep (se 1 (by rfl) ⟨592808, by rfl⟩ : syracuseStep 790411 = 1185617) B1185617
theorem B626585 : Blo 413771 626585 := bstep (se 2 (by rfl) ⟨234969, by rfl⟩ : syracuseStep 626585 = 469939) B469939
theorem B1052747 : Blo 413771 1052747 := bstep (se 1 (by rfl) ⟨789560, by rfl⟩ : syracuseStep 1052747 = 1579121) B1579121
theorem B18157709 : Blo 413771 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B528535 : Blo 413771 528535 := bstep (se 1 (by rfl) ⟨396401, by rfl⟩ : syracuseStep 528535 = 792803) B792803
theorem B1577177 : Blo 413771 1577177 := bstep (se 2 (by rfl) ⟨591441, by rfl⟩ : syracuseStep 1577177 = 1182883) B1182883
theorem B790859 : Blo 413771 790859 := bstep (se 1 (by rfl) ⟨593144, by rfl⟩ : syracuseStep 790859 = 1186289) B1186289
theorem B1053121 : Blo 413771 1053121 := bstep (se 2 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 1053121 = 789841) B789841
theorem B791041 : Blo 413771 791041 := bstep (se 2 (by rfl) ⟨296640, by rfl⟩ : syracuseStep 791041 = 593281) B593281
theorem B1577495 : Blo 413771 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B5968565 : Blo 413771 5968565 := bstep (se 5 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 5968565 = 559553) B559553
theorem B791383 : Blo 413771 791383 := bstep (se 1 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 791383 = 1187075) B1187075
theorem B1053719 : Blo 413771 1053719 := bstep (se 1 (by rfl) ⟨790289, by rfl⟩ : syracuseStep 1053719 = 1580579) B1580579
theorem B791603 : Blo 413771 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B857177 : Blo 413771 857177 := bstep (se 2 (by rfl) ⟨321441, by rfl⟩ : syracuseStep 857177 = 642883) B642883
theorem B1578163 : Blo 413771 1578163 := bstep (se 1 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 1578163 = 2367245) B2367245
theorem B791831 : Blo 413771 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B1119539 : Blo 413771 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B792089 : Blo 413771 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B497227 : Blo 413771 497227 := bstep (se 1 (by rfl) ⟨372920, by rfl⟩ : syracuseStep 497227 = 745841) B745841
theorem B890443 : Blo 413771 890443 := bstep (se 1 (by rfl) ⟨667832, by rfl⟩ : syracuseStep 890443 = 1335665) B1335665
theorem B4789853 : Blo 413771 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B890519 : Blo 413771 890519 := bstep (se 1 (by rfl) ⟨667889, by rfl⟩ : syracuseStep 890519 = 1335779) B1335779
theorem B1775297 : Blo 413771 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B1054529 : Blo 413771 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B3151709 : Blo 413771 3151709 := bstep (se 3 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 3151709 = 1181891) B1181891
theorem B792499 : Blo 413771 792499 := bstep (se 1 (by rfl) ⟨594374, by rfl⟩ : syracuseStep 792499 = 1188749) B1188749
theorem B8198213 : Blo 413771 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B1349849 : Blo 413771 1349849 := bstep (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) B1012387
theorem B2103569 : Blo 413771 2103569 := bstep (se 2 (by rfl) ⟨788838, by rfl⟩ : syracuseStep 2103569 = 1577677) B1577677
theorem B1055065 : Blo 413771 1055065 := bstep (se 2 (by rfl) ⟨395649, by rfl⟩ : syracuseStep 1055065 = 791299) B791299
theorem B1775965 : Blo 413771 1775965 := bstep (se 3 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 1775965 = 665987) B665987
theorem B1579409 : Blo 413771 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B1120663 : Blo 413771 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B792985 : Blo 413771 792985 := bstep (se 2 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 792985 = 594739) B594739
theorem B2103731 : Blo 413771 2103731 := bstep (se 1 (by rfl) ⟨1577798, by rfl⟩ : syracuseStep 2103731 = 3155597) B3155597
theorem B1186265 : Blo 413771 1186265 := bstep (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) B889699
theorem B2365969 : Blo 413771 2365969 := bstep (se 2 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 2365969 = 1774477) B1774477
theorem B1546775 : Blo 413771 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B465547 : Blo 413771 465547 := bstep (se 1 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 465547 = 698321) B698321
theorem B465655 : Blo 413771 465655 := bstep (se 1 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 465655 = 698483) B698483
theorem B10132289 : Blo 413771 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B465835 : Blo 413771 465835 := bstep (se 1 (by rfl) ⟨349376, by rfl⟩ : syracuseStep 465835 = 698753) B698753
theorem B1776563 : Blo 413771 1776563 := bstep (se 1 (by rfl) ⟨1332422, by rfl⟩ : syracuseStep 1776563 = 2664845) B2664845
theorem B465943 : Blo 413771 465943 := bstep (se 1 (by rfl) ⟨349457, by rfl⟩ : syracuseStep 465943 = 698915) B698915
theorem B1580107 : Blo 413771 1580107 := bstep (se 1 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 1580107 = 2370161) B2370161
theorem B466123 : Blo 413771 466123 := bstep (se 1 (by rfl) ⟨349592, by rfl⟩ : syracuseStep 466123 = 699185) B699185
theorem B1350877 : Blo 413771 1350877 := bstep (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) B506579
theorem B466231 : Blo 413771 466231 := bstep (se 1 (by rfl) ⟨349673, by rfl⟩ : syracuseStep 466231 = 699347) B699347
theorem B1580381 : Blo 413771 1580381 := bstep (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) B592643
theorem B1056179 : Blo 413771 1056179 := bstep (se 1 (by rfl) ⟨792134, by rfl⟩ : syracuseStep 1056179 = 1584269) B1584269
theorem B466411 : Blo 413771 466411 := bstep (se 1 (by rfl) ⟨349808, by rfl⟩ : syracuseStep 466411 = 699617) B699617
theorem B466519 : Blo 413771 466519 := bstep (se 1 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 466519 = 699779) B699779
theorem B1187531 : Blo 413771 1187531 := bstep (se 1 (by rfl) ⟨890648, by rfl⟩ : syracuseStep 1187531 = 1781297) B1781297
theorem B1056473 : Blo 413771 1056473 := bstep (se 2 (by rfl) ⟨396177, by rfl⟩ : syracuseStep 1056473 = 792355) B792355
theorem B466699 : Blo 413771 466699 := bstep (se 1 (by rfl) ⟨350024, by rfl⟩ : syracuseStep 466699 = 700049) B700049
theorem B466807 : Blo 413771 466807 := bstep (se 1 (by rfl) ⟨350105, by rfl⟩ : syracuseStep 466807 = 700211) B700211
theorem B1122265 : Blo 413771 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B1581079 : Blo 413771 1581079 := bstep (se 1 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 1581079 = 2371619) B2371619
theorem B466987 : Blo 413771 466987 := bstep (se 1 (by rfl) ⟨350240, by rfl⟩ : syracuseStep 466987 = 700481) B700481
theorem B467095 : Blo 413771 467095 := bstep (se 1 (by rfl) ⟨350321, by rfl⟩ : syracuseStep 467095 = 700643) B700643
theorem B467275 : Blo 413771 467275 := bstep (se 1 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 467275 = 700913) B700913
theorem B2105675 : Blo 413771 2105675 := bstep (se 1 (by rfl) ⟨1579256, by rfl⟩ : syracuseStep 2105675 = 3158513) B3158513
theorem B467383 : Blo 413771 467383 := bstep (se 1 (by rfl) ⟨350537, by rfl⟩ : syracuseStep 467383 = 701075) B701075
theorem B4006493 : Blo 413771 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B467563 : Blo 413771 467563 := bstep (se 1 (by rfl) ⟨350672, by rfl⟩ : syracuseStep 467563 = 701345) B701345
theorem B500375 : Blo 413771 500375 := bstep (se 1 (by rfl) ⟨375281, by rfl⟩ : syracuseStep 500375 = 750563) B750563
theorem B959129 : Blo 413771 959129 := bstep (se 2 (by rfl) ⟨359673, by rfl⟩ : syracuseStep 959129 = 719347) B719347
theorem B467671 : Blo 413771 467671 := bstep (se 1 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 467671 = 701507) B701507
theorem B1581869 : Blo 413771 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B4006721 : Blo 413771 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B467851 : Blo 413771 467851 := bstep (se 1 (by rfl) ⟨350888, by rfl⟩ : syracuseStep 467851 = 701777) B701777
theorem B500683 : Blo 413771 500683 := bstep (se 1 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 500683 = 751025) B751025
theorem B467959 : Blo 413771 467959 := bstep (se 1 (by rfl) ⟨350969, by rfl⟩ : syracuseStep 467959 = 701939) B701939
theorem B468139 : Blo 413771 468139 := bstep (se 1 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 468139 = 702209) B702209
theorem B468247 : Blo 413771 468247 := bstep (se 1 (by rfl) ⟨351185, by rfl⟩ : syracuseStep 468247 = 702371) B702371
theorem B468427 : Blo 413771 468427 := bstep (se 1 (by rfl) ⟨351320, by rfl⟩ : syracuseStep 468427 = 702641) B702641
theorem B468535 : Blo 413771 468535 := bstep (se 1 (by rfl) ⟨351401, by rfl⟩ : syracuseStep 468535 = 702803) B702803
theorem B468715 : Blo 413771 468715 := bstep (se 1 (by rfl) ⟨351536, by rfl⟩ : syracuseStep 468715 = 703073) B703073
theorem B468823 : Blo 413771 468823 := bstep (se 1 (by rfl) ⟨351617, by rfl⟩ : syracuseStep 468823 = 703235) B703235
theorem B3614557 : Blo 413771 3614557 := bstep (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) B1355459
theorem B2369411 : Blo 413771 2369411 := bstep (se 1 (by rfl) ⟨1777058, by rfl⟩ : syracuseStep 2369411 = 3554117) B3554117
theorem B2172851 : Blo 413771 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B469003 : Blo 413771 469003 := bstep (se 1 (by rfl) ⟨351752, by rfl⟩ : syracuseStep 469003 = 703505) B703505
theorem B2107457 : Blo 413771 2107457 := bstep (se 2 (by rfl) ⟨790296, by rfl⟩ : syracuseStep 2107457 = 1580593) B1580593
theorem B469111 : Blo 413771 469111 := bstep (se 1 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 469111 = 703667) B703667
theorem B1583297 : Blo 413771 1583297 := bstep (se 2 (by rfl) ⟨593736, by rfl⟩ : syracuseStep 1583297 = 1187473) B1187473
theorem B469291 : Blo 413771 469291 := bstep (se 1 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 469291 = 703937) B703937
theorem B698699 : Blo 413771 698699 := bstep (se 1 (by rfl) ⟨524024, by rfl⟩ : syracuseStep 698699 = 1048049) B1048049
theorem B469399 : Blo 413771 469399 := bstep (se 1 (by rfl) ⟨352049, by rfl⟩ : syracuseStep 469399 = 704099) B704099
theorem B698827 : Blo 413771 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B1681937 : Blo 413771 1681937 := bstep (se 2 (by rfl) ⟨630726, by rfl⟩ : syracuseStep 1681937 = 1261453) B1261453
theorem B469579 : Blo 413771 469579 := bstep (se 1 (by rfl) ⟨352184, by rfl⟩ : syracuseStep 469579 = 704369) B704369
theorem B698969 : Blo 413771 698969 := bstep (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) B524227
theorem B1780355 : Blo 413771 1780355 := bstep (se 1 (by rfl) ⟨1335266, by rfl⟩ : syracuseStep 1780355 = 2670533) B2670533
theorem B469687 : Blo 413771 469687 := bstep (se 1 (by rfl) ⟨352265, by rfl⟩ : syracuseStep 469687 = 704531) B704531
theorem B699097 : Blo 413771 699097 := bstep (se 2 (by rfl) ⟨262161, by rfl⟩ : syracuseStep 699097 = 524323) B524323
theorem B2239249 : Blo 413771 2239249 := bstep (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) B1679437
theorem B469867 : Blo 413771 469867 := bstep (se 1 (by rfl) ⟨352400, by rfl⟩ : syracuseStep 469867 = 704801) B704801
theorem B1616843 : Blo 413771 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B469975 : Blo 413771 469975 := bstep (se 1 (by rfl) ⟨352481, by rfl⟩ : syracuseStep 469975 = 704963) B704963
theorem B1780697 : Blo 413771 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B535691 : Blo 413771 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B666839 : Blo 413771 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B699671 : Blo 413771 699671 := bstep (se 1 (by rfl) ⟨524753, by rfl⟩ : syracuseStep 699671 = 1049507) B1049507
theorem B699799 : Blo 413771 699799 := bstep (se 1 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 699799 = 1049699) B1049699
theorem B1584785 : Blo 413771 1584785 := bstep (se 2 (by rfl) ⟨594294, by rfl⟩ : syracuseStep 1584785 = 1188589) B1188589
theorem B896663 : Blo 413771 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B667531 : Blo 413771 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B2109401 : Blo 413771 2109401 := bstep (se 2 (by rfl) ⟨791025, by rfl⟩ : syracuseStep 2109401 = 1582051) B1582051
theorem B700427 : Blo 413771 700427 := bstep (se 1 (by rfl) ⟨525320, by rfl⟩ : syracuseStep 700427 = 1050641) B1050641
theorem B2404397 : Blo 413771 2404397 := bstep (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) B901649
theorem B1585241 : Blo 413771 1585241 := bstep (se 2 (by rfl) ⟨594465, by rfl⟩ : syracuseStep 1585241 = 1188931) B1188931
theorem B1421405 : Blo 413771 1421405 := bstep (se 3 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 1421405 = 533027) B533027
theorem B700555 : Blo 413771 700555 := bstep (se 1 (by rfl) ⟨525416, by rfl⟩ : syracuseStep 700555 = 1050833) B1050833
theorem B2371801 : Blo 413771 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B700697 : Blo 413771 700697 := bstep (se 2 (by rfl) ⟨262761, by rfl⟩ : syracuseStep 700697 = 525523) B525523
theorem B1585453 : Blo 413771 1585453 := bstep (se 3 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 1585453 = 594545) B594545
theorem B700825 : Blo 413771 700825 := bstep (se 2 (by rfl) ⟨262809, by rfl⟩ : syracuseStep 700825 = 525619) B525619
theorem B1421761 : Blo 413771 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B995905 : Blo 413771 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B1782337 : Blo 413771 1782337 := bstep (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) B1336753
theorem B995915 : Blo 413771 995915 := bstep (se 1 (by rfl) ⟨746936, by rfl⟩ : syracuseStep 995915 = 1493873) B1493873
theorem B1585757 : Blo 413771 1585757 := bstep (se 3 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 1585757 = 594659) B594659
theorem B12366533 : Blo 413771 12366533 := bstep (se 4 (by rfl) ⟨1159362, by rfl⟩ : syracuseStep 12366533 = 2318725) B2318725
theorem B668569 : Blo 413771 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B701399 : Blo 413771 701399 := bstep (se 1 (by rfl) ⟨526049, by rfl⟩ : syracuseStep 701399 = 1052099) B1052099
theorem B701527 : Blo 413771 701527 := bstep (se 1 (by rfl) ⟨526145, by rfl⟩ : syracuseStep 701527 = 1052291) B1052291
theorem B2372759 : Blo 413771 2372759 := bstep (se 1 (by rfl) ⟨1779569, by rfl⟩ : syracuseStep 2372759 = 3559139) B3559139
theorem B930995 : Blo 413771 930995 := bstep (se 1 (by rfl) ⟨698246, by rfl⟩ : syracuseStep 930995 = 1396493) B1396493
theorem B931031 : Blo 413771 931031 := bstep (se 1 (by rfl) ⟨698273, by rfl⟩ : syracuseStep 931031 = 1396547) B1396547
theorem B996569 : Blo 413771 996569 := bstep (se 2 (by rfl) ⟨373713, by rfl⟩ : syracuseStep 996569 = 747427) B747427
theorem B472375 : Blo 413771 472375 := bstep (se 1 (by rfl) ⟨354281, by rfl⟩ : syracuseStep 472375 = 708563) B708563
theorem B669017 : Blo 413771 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B931211 : Blo 413771 931211 := bstep (se 1 (by rfl) ⟨698408, by rfl⟩ : syracuseStep 931211 = 1396817) B1396817
theorem B931265 : Blo 413771 931265 := bstep (se 2 (by rfl) ⟨349224, by rfl⟩ : syracuseStep 931265 = 698449) B698449
theorem B2668049 : Blo 413771 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2111021 : Blo 413771 2111021 := bstep (se 3 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 2111021 = 791633) B791633
theorem B931481 : Blo 413771 931481 := bstep (se 2 (by rfl) ⟨349305, by rfl⟩ : syracuseStep 931481 = 698611) B698611
theorem B997067 : Blo 413771 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B702155 : Blo 413771 702155 := bstep (se 1 (by rfl) ⟨526616, by rfl⟩ : syracuseStep 702155 = 1053233) B1053233
theorem B931571 : Blo 413771 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B931607 : Blo 413771 931607 := bstep (se 1 (by rfl) ⟨698705, by rfl⟩ : syracuseStep 931607 = 1397411) B1397411
theorem B702283 : Blo 413771 702283 := bstep (se 1 (by rfl) ⟨526712, by rfl⟩ : syracuseStep 702283 = 1053425) B1053425
theorem B931787 : Blo 413771 931787 := bstep (se 1 (by rfl) ⟨698840, by rfl⟩ : syracuseStep 931787 = 1397681) B1397681
theorem B702425 : Blo 413771 702425 := bstep (se 2 (by rfl) ⟨263409, by rfl⟩ : syracuseStep 702425 = 526819) B526819
theorem B931841 : Blo 413771 931841 := bstep (se 2 (by rfl) ⟨349440, by rfl⟩ : syracuseStep 931841 = 698881) B698881
theorem B702553 : Blo 413771 702553 := bstep (se 2 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 702553 = 526915) B526915
theorem B10074293 : Blo 413771 10074293 := bstep (se 5 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 10074293 = 944465) B944465
theorem B932057 : Blo 413771 932057 := bstep (se 2 (by rfl) ⟨349521, by rfl⟩ : syracuseStep 932057 = 699043) B699043
theorem B932147 : Blo 413771 932147 := bstep (se 1 (by rfl) ⟨699110, by rfl⟩ : syracuseStep 932147 = 1398221) B1398221
theorem B932183 : Blo 413771 932183 := bstep (se 1 (by rfl) ⟨699137, by rfl⟩ : syracuseStep 932183 = 1398275) B1398275
theorem B899545 : Blo 413771 899545 := bstep (se 2 (by rfl) ⟨337329, by rfl⟩ : syracuseStep 899545 = 674659) B674659
theorem B932363 : Blo 413771 932363 := bstep (se 1 (by rfl) ⟨699272, by rfl⟩ : syracuseStep 932363 = 1398545) B1398545
theorem B932417 : Blo 413771 932417 := bstep (se 2 (by rfl) ⟨349656, by rfl⟩ : syracuseStep 932417 = 699313) B699313
theorem B703127 : Blo 413771 703127 := bstep (se 1 (by rfl) ⟨527345, by rfl⟩ : syracuseStep 703127 = 1054691) B1054691
theorem B703255 : Blo 413771 703255 := bstep (se 1 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 703255 = 1054883) B1054883
theorem B932633 : Blo 413771 932633 := bstep (se 2 (by rfl) ⟨349737, by rfl⟩ : syracuseStep 932633 = 699475) B699475
theorem B932723 : Blo 413771 932723 := bstep (se 1 (by rfl) ⟨699542, by rfl⟩ : syracuseStep 932723 = 1399085) B1399085
theorem B932759 : Blo 413771 932759 := bstep (se 1 (by rfl) ⟨699569, by rfl⟩ : syracuseStep 932759 = 1399139) B1399139
theorem B1326041 : Blo 413771 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B932939 : Blo 413771 932939 := bstep (se 1 (by rfl) ⟨699704, by rfl⟩ : syracuseStep 932939 = 1399409) B1399409
theorem B932993 : Blo 413771 932993 := bstep (se 2 (by rfl) ⟨349872, by rfl⟩ : syracuseStep 932993 = 699745) B699745
theorem B6077591 : Blo 413771 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B933209 : Blo 413771 933209 := bstep (se 2 (by rfl) ⟨349953, by rfl⟩ : syracuseStep 933209 = 699907) B699907
theorem B2669917 : Blo 413771 2669917 := bstep (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) B1001219
theorem B703883 : Blo 413771 703883 := bstep (se 1 (by rfl) ⟨527912, by rfl⟩ : syracuseStep 703883 = 1055825) B1055825
theorem B12041621 : Blo 413771 12041621 := bstep (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) B564451
theorem B933299 : Blo 413771 933299 := bstep (se 1 (by rfl) ⟨699974, by rfl⟩ : syracuseStep 933299 = 1399949) B1399949
theorem B3554765 : Blo 413771 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B933335 : Blo 413771 933335 := bstep (se 1 (by rfl) ⟨700001, by rfl⟩ : syracuseStep 933335 = 1400003) B1400003
theorem B704011 : Blo 413771 704011 := bstep (se 1 (by rfl) ⟨528008, by rfl⟩ : syracuseStep 704011 = 1056017) B1056017
theorem B2375243 : Blo 413771 2375243 := bstep (se 1 (by rfl) ⟨1781432, by rfl⟩ : syracuseStep 2375243 = 3562865) B3562865
theorem B933515 : Blo 413771 933515 := bstep (se 1 (by rfl) ⟨700136, by rfl⟩ : syracuseStep 933515 = 1400273) B1400273
theorem B704153 : Blo 413771 704153 := bstep (se 2 (by rfl) ⟨264057, by rfl⟩ : syracuseStep 704153 = 528115) B528115
theorem B933569 : Blo 413771 933569 := bstep (se 2 (by rfl) ⟨350088, by rfl⟩ : syracuseStep 933569 = 700177) B700177
theorem B704281 : Blo 413771 704281 := bstep (se 2 (by rfl) ⟨264105, by rfl⟩ : syracuseStep 704281 = 528211) B528211
theorem B5062445 : Blo 413771 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B933785 : Blo 413771 933785 := bstep (se 2 (by rfl) ⟨350169, by rfl⟩ : syracuseStep 933785 = 700339) B700339
theorem B933875 : Blo 413771 933875 := bstep (se 1 (by rfl) ⟨700406, by rfl⟩ : syracuseStep 933875 = 1400813) B1400813
theorem B933911 : Blo 413771 933911 := bstep (se 1 (by rfl) ⟨700433, by rfl⟩ : syracuseStep 933911 = 1400867) B1400867
theorem B934091 : Blo 413771 934091 := bstep (se 1 (by rfl) ⟨700568, by rfl⟩ : syracuseStep 934091 = 1401137) B1401137
theorem B934145 : Blo 413771 934145 := bstep (se 2 (by rfl) ⟨350304, by rfl⟩ : syracuseStep 934145 = 700609) B700609
theorem B704855 : Blo 413771 704855 := bstep (se 1 (by rfl) ⟨528641, by rfl⟩ : syracuseStep 704855 = 1057283) B1057283
theorem B7094627 : Blo 413771 7094627 := bstep (se 1 (by rfl) ⟨5320970, by rfl⟩ : syracuseStep 7094627 = 10641941) B10641941
theorem B704983 : Blo 413771 704983 := bstep (se 1 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 704983 = 1057475) B1057475
theorem B934361 : Blo 413771 934361 := bstep (se 2 (by rfl) ⟨350385, by rfl⟩ : syracuseStep 934361 = 700771) B700771
theorem B475627 : Blo 413771 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B934451 : Blo 413771 934451 := bstep (se 1 (by rfl) ⟨700838, by rfl⟩ : syracuseStep 934451 = 1401677) B1401677
theorem B934487 : Blo 413771 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B1262231 : Blo 413771 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B2999045 : Blo 413771 2999045 := bstep (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) B562321
theorem B934667 : Blo 413771 934667 := bstep (se 1 (by rfl) ⟨701000, by rfl⟩ : syracuseStep 934667 = 1402001) B1402001
theorem B934721 : Blo 413771 934721 := bstep (se 2 (by rfl) ⟨350520, by rfl⟩ : syracuseStep 934721 = 701041) B701041
theorem B3031901 : Blo 413771 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B2245477 : Blo 413771 2245477 := bstep (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) B421027
theorem B934937 : Blo 413771 934937 := bstep (se 2 (by rfl) ⟨350601, by rfl⟩ : syracuseStep 934937 = 701203) B701203
theorem B1492013 : Blo 413771 1492013 := bstep (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) B559505
theorem B935027 : Blo 413771 935027 := bstep (se 1 (by rfl) ⟨701270, by rfl⟩ : syracuseStep 935027 = 1402541) B1402541
theorem B935063 : Blo 413771 935063 := bstep (se 1 (by rfl) ⟨701297, by rfl⟩ : syracuseStep 935063 = 1402595) B1402595
theorem B2704535 : Blo 413771 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B1688779 : Blo 413771 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B935243 : Blo 413771 935243 := bstep (se 1 (by rfl) ⟨701432, by rfl⟩ : syracuseStep 935243 = 1402865) B1402865
theorem B2114909 : Blo 413771 2114909 := bstep (se 3 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 2114909 = 793091) B793091
theorem B935297 : Blo 413771 935297 := bstep (se 2 (by rfl) ⟨350736, by rfl⟩ : syracuseStep 935297 = 701473) B701473
theorem B443927 : Blo 413771 443927 := bstep (se 1 (by rfl) ⟨332945, by rfl⟩ : syracuseStep 443927 = 665891) B665891
theorem B1263179 : Blo 413771 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B935513 : Blo 413771 935513 := bstep (se 2 (by rfl) ⟨350817, by rfl⟩ : syracuseStep 935513 = 701635) B701635
theorem B8570461 : Blo 413771 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B935603 : Blo 413771 935603 := bstep (se 1 (by rfl) ⟨701702, by rfl⟩ : syracuseStep 935603 = 1403405) B1403405
theorem B935639 : Blo 413771 935639 := bstep (se 1 (by rfl) ⟨701729, by rfl⟩ : syracuseStep 935639 = 1403459) B1403459
theorem B3557155 : Blo 413771 3557155 := bstep (se 1 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 3557155 = 5335733) B5335733
theorem B935819 : Blo 413771 935819 := bstep (se 1 (by rfl) ⟨701864, by rfl⟩ : syracuseStep 935819 = 1403729) B1403729
theorem B935873 : Blo 413771 935873 := bstep (se 2 (by rfl) ⟨350952, by rfl⟩ : syracuseStep 935873 = 701905) B701905
theorem B903155 : Blo 413771 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B4737041 : Blo 413771 4737041 := bstep (se 2 (by rfl) ⟨1776390, by rfl⟩ : syracuseStep 4737041 = 3552781) B3552781
theorem B3229789 : Blo 413771 3229789 := bstep (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) B1211171
theorem B936089 : Blo 413771 936089 := bstep (se 2 (by rfl) ⟨351033, by rfl⟩ : syracuseStep 936089 = 702067) B702067
theorem B2377907 : Blo 413771 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B444619 : Blo 413771 444619 := bstep (se 1 (by rfl) ⟨333464, by rfl⟩ : syracuseStep 444619 = 666929) B666929
theorem B936179 : Blo 413771 936179 := bstep (se 1 (by rfl) ⟨702134, by rfl⟩ : syracuseStep 936179 = 1404269) B1404269
theorem B936215 : Blo 413771 936215 := bstep (se 1 (by rfl) ⟨702161, by rfl⟩ : syracuseStep 936215 = 1404323) B1404323
theorem B1493441 : Blo 413771 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B936395 : Blo 413771 936395 := bstep (se 1 (by rfl) ⟨702296, by rfl⟩ : syracuseStep 936395 = 1404593) B1404593
theorem B936449 : Blo 413771 936449 := bstep (se 2 (by rfl) ⟨351168, by rfl⟩ : syracuseStep 936449 = 702337) B702337
theorem B936665 : Blo 413771 936665 := bstep (se 2 (by rfl) ⟨351249, by rfl⟩ : syracuseStep 936665 = 702499) B702499
theorem B1264349 : Blo 413771 1264349 := bstep (se 3 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 1264349 = 474131) B474131
theorem B936755 : Blo 413771 936755 := bstep (se 1 (by rfl) ⟨702566, by rfl⟩ : syracuseStep 936755 = 1405133) B1405133
theorem B936791 : Blo 413771 936791 := bstep (se 1 (by rfl) ⟨702593, by rfl⟩ : syracuseStep 936791 = 1405187) B1405187
theorem B1330141 : Blo 413771 1330141 := bstep (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) B498803
theorem B936971 : Blo 413771 936971 := bstep (se 1 (by rfl) ⟨702728, by rfl⟩ : syracuseStep 936971 = 1405457) B1405457
theorem B445495 : Blo 413771 445495 := bstep (se 1 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 445495 = 668243) B668243
theorem B937025 : Blo 413771 937025 := bstep (se 2 (by rfl) ⟨351384, by rfl⟩ : syracuseStep 937025 = 702769) B702769
theorem B937241 : Blo 413771 937241 := bstep (se 2 (by rfl) ⟨351465, by rfl⟩ : syracuseStep 937241 = 702931) B702931
theorem B937331 : Blo 413771 937331 := bstep (se 1 (by rfl) ⟨702998, by rfl⟩ : syracuseStep 937331 = 1405997) B1405997
theorem B937367 : Blo 413771 937367 := bstep (se 1 (by rfl) ⟨703025, by rfl⟩ : syracuseStep 937367 = 1406051) B1406051
theorem B445943 : Blo 413771 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B3001931 : Blo 413771 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B937547 : Blo 413771 937547 := bstep (se 1 (by rfl) ⟨703160, by rfl⟩ : syracuseStep 937547 = 1406321) B1406321
theorem B937601 : Blo 413771 937601 := bstep (se 2 (by rfl) ⟨351600, by rfl⟩ : syracuseStep 937601 = 703201) B703201
theorem B1003211 : Blo 413771 1003211 := bstep (se 1 (by rfl) ⟨752408, by rfl⟩ : syracuseStep 1003211 = 1504817) B1504817
theorem B937817 : Blo 413771 937817 := bstep (se 2 (by rfl) ⟨351681, by rfl⟩ : syracuseStep 937817 = 703363) B703363
theorem B479083 : Blo 413771 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B937907 : Blo 413771 937907 := bstep (se 1 (by rfl) ⟨703430, by rfl⟩ : syracuseStep 937907 = 1406861) B1406861
theorem B937943 : Blo 413771 937943 := bstep (se 1 (by rfl) ⟨703457, by rfl⟩ : syracuseStep 937943 = 1406915) B1406915
theorem B413771 : Blo 413771 413771 := bstep (se 1 (by rfl) ⟨310328, by rfl⟩ : syracuseStep 413771 = 620657) B620657
theorem B413783 : Blo 413771 413783 := bstep (se 1 (by rfl) ⟨310337, by rfl⟩ : syracuseStep 413783 = 620675) B620675
theorem B413803 : Blo 413771 413803 := bstep (se 1 (by rfl) ⟨310352, by rfl⟩ : syracuseStep 413803 = 620705) B620705
theorem B413815 : Blo 413771 413815 := bstep (se 1 (by rfl) ⟨310361, by rfl⟩ : syracuseStep 413815 = 620723) B620723
theorem B413835 : Blo 413771 413835 := bstep (se 1 (by rfl) ⟨310376, by rfl⟩ : syracuseStep 413835 = 620753) B620753
theorem B938123 : Blo 413771 938123 := bstep (se 1 (by rfl) ⟨703592, by rfl⟩ : syracuseStep 938123 = 1407185) B1407185
theorem B413847 : Blo 413771 413847 := bstep (se 1 (by rfl) ⟨310385, by rfl⟩ : syracuseStep 413847 = 620771) B620771
theorem B413867 : Blo 413771 413867 := bstep (se 1 (by rfl) ⟨310400, by rfl⟩ : syracuseStep 413867 = 620801) B620801
theorem B413879 : Blo 413771 413879 := bstep (se 1 (by rfl) ⟨310409, by rfl⟩ : syracuseStep 413879 = 620819) B620819
theorem B938177 : Blo 413771 938177 := bstep (se 2 (by rfl) ⟨351816, by rfl⟩ : syracuseStep 938177 = 703633) B703633
theorem B413899 : Blo 413771 413899 := bstep (se 1 (by rfl) ⟨310424, by rfl⟩ : syracuseStep 413899 = 620849) B620849
theorem B413911 : Blo 413771 413911 := bstep (se 1 (by rfl) ⟨310433, by rfl⟩ : syracuseStep 413911 = 620867) B620867
theorem B413931 : Blo 413771 413931 := bstep (se 1 (by rfl) ⟨310448, by rfl⟩ : syracuseStep 413931 = 620897) B620897
theorem B413943 : Blo 413771 413943 := bstep (se 1 (by rfl) ⟨310457, by rfl⟩ : syracuseStep 413943 = 620915) B620915
theorem B413963 : Blo 413771 413963 := bstep (se 1 (by rfl) ⟨310472, by rfl⟩ : syracuseStep 413963 = 620945) B620945
theorem B413975 : Blo 413771 413975 := bstep (se 1 (by rfl) ⟨310481, by rfl⟩ : syracuseStep 413975 = 620963) B620963
theorem B413995 : Blo 413771 413995 := bstep (se 1 (by rfl) ⟨310496, by rfl⟩ : syracuseStep 413995 = 620993) B620993
theorem B414007 : Blo 413771 414007 := bstep (se 1 (by rfl) ⟨310505, by rfl⟩ : syracuseStep 414007 = 621011) B621011
theorem B414027 : Blo 413771 414027 := bstep (se 1 (by rfl) ⟨310520, by rfl⟩ : syracuseStep 414027 = 621041) B621041
theorem B414039 : Blo 413771 414039 := bstep (se 1 (by rfl) ⟨310529, by rfl⟩ : syracuseStep 414039 = 621059) B621059
theorem B414059 : Blo 413771 414059 := bstep (se 1 (by rfl) ⟨310544, by rfl⟩ : syracuseStep 414059 = 621089) B621089
theorem B414071 : Blo 413771 414071 := bstep (se 1 (by rfl) ⟨310553, by rfl⟩ : syracuseStep 414071 = 621107) B621107
theorem B414091 : Blo 413771 414091 := bstep (se 1 (by rfl) ⟨310568, by rfl⟩ : syracuseStep 414091 = 621137) B621137
theorem B414103 : Blo 413771 414103 := bstep (se 1 (by rfl) ⟨310577, by rfl⟩ : syracuseStep 414103 = 621155) B621155
theorem B938393 : Blo 413771 938393 := bstep (se 2 (by rfl) ⟨351897, by rfl⟩ : syracuseStep 938393 = 703795) B703795
theorem B414123 : Blo 413771 414123 := bstep (se 1 (by rfl) ⟨310592, by rfl⟩ : syracuseStep 414123 = 621185) B621185
theorem B414135 : Blo 413771 414135 := bstep (se 1 (by rfl) ⟨310601, by rfl⟩ : syracuseStep 414135 = 621203) B621203
theorem B1397195 : Blo 413771 1397195 := bstep (se 1 (by rfl) ⟨1047896, by rfl⟩ : syracuseStep 1397195 = 2095793) B2095793
theorem B414155 : Blo 413771 414155 := bstep (se 1 (by rfl) ⟨310616, by rfl⟩ : syracuseStep 414155 = 621233) B621233
theorem B610763 : Blo 413771 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B414167 : Blo 413771 414167 := bstep (se 1 (by rfl) ⟨310625, by rfl⟩ : syracuseStep 414167 = 621251) B621251
theorem B414187 : Blo 413771 414187 := bstep (se 1 (by rfl) ⟨310640, by rfl⟩ : syracuseStep 414187 = 621281) B621281
theorem B938483 : Blo 413771 938483 := bstep (se 1 (by rfl) ⟨703862, by rfl⟩ : syracuseStep 938483 = 1407725) B1407725
theorem B414199 : Blo 413771 414199 := bstep (se 1 (by rfl) ⟨310649, by rfl⟩ : syracuseStep 414199 = 621299) B621299
theorem B414219 : Blo 413771 414219 := bstep (se 1 (by rfl) ⟨310664, by rfl⟩ : syracuseStep 414219 = 621329) B621329
theorem B414231 : Blo 413771 414231 := bstep (se 1 (by rfl) ⟨310673, by rfl⟩ : syracuseStep 414231 = 621347) B621347
theorem B938519 : Blo 413771 938519 := bstep (se 1 (by rfl) ⟨703889, by rfl⟩ : syracuseStep 938519 = 1407779) B1407779
theorem B414251 : Blo 413771 414251 := bstep (se 1 (by rfl) ⟨310688, by rfl⟩ : syracuseStep 414251 = 621377) B621377
theorem B414263 : Blo 413771 414263 := bstep (se 1 (by rfl) ⟨310697, by rfl⟩ : syracuseStep 414263 = 621395) B621395
theorem B414283 : Blo 413771 414283 := bstep (se 1 (by rfl) ⟨310712, by rfl⟩ : syracuseStep 414283 = 621425) B621425
theorem B414295 : Blo 413771 414295 := bstep (se 1 (by rfl) ⟨310721, by rfl⟩ : syracuseStep 414295 = 621443) B621443
theorem B414315 : Blo 413771 414315 := bstep (se 1 (by rfl) ⟨310736, by rfl⟩ : syracuseStep 414315 = 621473) B621473
theorem B414327 : Blo 413771 414327 := bstep (se 1 (by rfl) ⟨310745, by rfl⟩ : syracuseStep 414327 = 621491) B621491
theorem B414347 : Blo 413771 414347 := bstep (se 1 (by rfl) ⟨310760, by rfl⟩ : syracuseStep 414347 = 621521) B621521
theorem B414359 : Blo 413771 414359 := bstep (se 1 (by rfl) ⟨310769, by rfl⟩ : syracuseStep 414359 = 621539) B621539
theorem B1495703 : Blo 413771 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B414379 : Blo 413771 414379 := bstep (se 1 (by rfl) ⟨310784, by rfl⟩ : syracuseStep 414379 = 621569) B621569
theorem B414391 : Blo 413771 414391 := bstep (se 1 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 414391 = 621587) B621587
theorem B840385 : Blo 413771 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B414411 : Blo 413771 414411 := bstep (se 1 (by rfl) ⟨310808, by rfl⟩ : syracuseStep 414411 = 621617) B621617
theorem B938699 : Blo 413771 938699 := bstep (se 1 (by rfl) ⟨704024, by rfl⟩ : syracuseStep 938699 = 1408049) B1408049
theorem B414423 : Blo 413771 414423 := bstep (se 1 (by rfl) ⟨310817, by rfl⟩ : syracuseStep 414423 = 621635) B621635
theorem B1397465 : Blo 413771 1397465 := bstep (se 2 (by rfl) ⟨524049, by rfl⟩ : syracuseStep 1397465 = 1048099) B1048099
theorem B414443 : Blo 413771 414443 := bstep (se 1 (by rfl) ⟨310832, by rfl⟩ : syracuseStep 414443 = 621665) B621665
theorem B414455 : Blo 413771 414455 := bstep (se 1 (by rfl) ⟨310841, by rfl⟩ : syracuseStep 414455 = 621683) B621683
theorem B840449 : Blo 413771 840449 := bstep (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) B630337
theorem B938753 : Blo 413771 938753 := bstep (se 2 (by rfl) ⟨352032, by rfl⟩ : syracuseStep 938753 = 704065) B704065
theorem B414475 : Blo 413771 414475 := bstep (se 1 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 414475 = 621713) B621713
theorem B414487 : Blo 413771 414487 := bstep (se 1 (by rfl) ⟨310865, by rfl⟩ : syracuseStep 414487 = 621731) B621731
theorem B414507 : Blo 413771 414507 := bstep (se 1 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 414507 = 621761) B621761
theorem B414519 : Blo 413771 414519 := bstep (se 1 (by rfl) ⟨310889, by rfl⟩ : syracuseStep 414519 = 621779) B621779
theorem B414539 : Blo 413771 414539 := bstep (se 1 (by rfl) ⟨310904, by rfl⟩ : syracuseStep 414539 = 621809) B621809
theorem B414551 : Blo 413771 414551 := bstep (se 1 (by rfl) ⟨310913, by rfl⟩ : syracuseStep 414551 = 621827) B621827
theorem B414571 : Blo 413771 414571 := bstep (se 1 (by rfl) ⟨310928, by rfl⟩ : syracuseStep 414571 = 621857) B621857
theorem B4739957 : Blo 413771 4739957 := bstep (se 5 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 4739957 = 444371) B444371
theorem B414583 : Blo 413771 414583 := bstep (se 1 (by rfl) ⟨310937, by rfl⟩ : syracuseStep 414583 = 621875) B621875
theorem B414603 : Blo 413771 414603 := bstep (se 1 (by rfl) ⟨310952, by rfl⟩ : syracuseStep 414603 = 621905) B621905
theorem B414615 : Blo 413771 414615 := bstep (se 1 (by rfl) ⟨310961, by rfl⟩ : syracuseStep 414615 = 621923) B621923
theorem B414635 : Blo 413771 414635 := bstep (se 1 (by rfl) ⟨310976, by rfl⟩ : syracuseStep 414635 = 621953) B621953
theorem B414647 : Blo 413771 414647 := bstep (se 1 (by rfl) ⟨310985, by rfl⟩ : syracuseStep 414647 = 621971) B621971
theorem B414667 : Blo 413771 414667 := bstep (se 1 (by rfl) ⟨311000, by rfl⟩ : syracuseStep 414667 = 622001) B622001
theorem B414679 : Blo 413771 414679 := bstep (se 1 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 414679 = 622019) B622019
theorem B938969 : Blo 413771 938969 := bstep (se 2 (by rfl) ⟨352113, by rfl⟩ : syracuseStep 938969 = 704227) B704227
theorem B414699 : Blo 413771 414699 := bstep (se 1 (by rfl) ⟨311024, by rfl⟩ : syracuseStep 414699 = 622049) B622049
theorem B414711 : Blo 413771 414711 := bstep (se 1 (by rfl) ⟨311033, by rfl⟩ : syracuseStep 414711 = 622067) B622067
theorem B414731 : Blo 413771 414731 := bstep (se 1 (by rfl) ⟨311048, by rfl⟩ : syracuseStep 414731 = 622097) B622097
theorem B414743 : Blo 413771 414743 := bstep (se 1 (by rfl) ⟨311057, by rfl⟩ : syracuseStep 414743 = 622115) B622115
theorem B414763 : Blo 413771 414763 := bstep (se 1 (by rfl) ⟨311072, by rfl⟩ : syracuseStep 414763 = 622145) B622145
theorem B939059 : Blo 413771 939059 := bstep (se 1 (by rfl) ⟨704294, by rfl⟩ : syracuseStep 939059 = 1408589) B1408589
theorem B414775 : Blo 413771 414775 := bstep (se 1 (by rfl) ⟨311081, by rfl⟩ : syracuseStep 414775 = 622163) B622163
theorem B414795 : Blo 413771 414795 := bstep (se 1 (by rfl) ⟨311096, by rfl⟩ : syracuseStep 414795 = 622193) B622193
theorem B414807 : Blo 413771 414807 := bstep (se 1 (by rfl) ⟨311105, by rfl⟩ : syracuseStep 414807 = 622211) B622211
theorem B939095 : Blo 413771 939095 := bstep (se 1 (by rfl) ⟨704321, by rfl⟩ : syracuseStep 939095 = 1408643) B1408643
theorem B414827 : Blo 413771 414827 := bstep (se 1 (by rfl) ⟨311120, by rfl⟩ : syracuseStep 414827 = 622241) B622241
theorem B414839 : Blo 413771 414839 := bstep (se 1 (by rfl) ⟨311129, by rfl⟩ : syracuseStep 414839 = 622259) B622259
theorem B414859 : Blo 413771 414859 := bstep (se 1 (by rfl) ⟨311144, by rfl⟩ : syracuseStep 414859 = 622289) B622289
theorem B414871 : Blo 413771 414871 := bstep (se 1 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 414871 = 622307) B622307
theorem B414891 : Blo 413771 414891 := bstep (se 1 (by rfl) ⟨311168, by rfl⟩ : syracuseStep 414891 = 622337) B622337
theorem B414903 : Blo 413771 414903 := bstep (se 1 (by rfl) ⟨311177, by rfl⟩ : syracuseStep 414903 = 622355) B622355
theorem B414923 : Blo 413771 414923 := bstep (se 1 (by rfl) ⟨311192, by rfl⟩ : syracuseStep 414923 = 622385) B622385
theorem B414935 : Blo 413771 414935 := bstep (se 1 (by rfl) ⟨311201, by rfl⟩ : syracuseStep 414935 = 622403) B622403
theorem B414955 : Blo 413771 414955 := bstep (se 1 (by rfl) ⟨311216, by rfl⟩ : syracuseStep 414955 = 622433) B622433
theorem B414967 : Blo 413771 414967 := bstep (se 1 (by rfl) ⟨311225, by rfl⟩ : syracuseStep 414967 = 622451) B622451
theorem B414987 : Blo 413771 414987 := bstep (se 1 (by rfl) ⟨311240, by rfl⟩ : syracuseStep 414987 = 622481) B622481
theorem B939275 : Blo 413771 939275 := bstep (se 1 (by rfl) ⟨704456, by rfl⟩ : syracuseStep 939275 = 1408913) B1408913
theorem B414999 : Blo 413771 414999 := bstep (se 1 (by rfl) ⟨311249, by rfl⟩ : syracuseStep 414999 = 622499) B622499
theorem B415019 : Blo 413771 415019 := bstep (se 1 (by rfl) ⟨311264, by rfl⟩ : syracuseStep 415019 = 622529) B622529
theorem B415031 : Blo 413771 415031 := bstep (se 1 (by rfl) ⟨311273, by rfl⟩ : syracuseStep 415031 = 622547) B622547
theorem B3429697 : Blo 413771 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B939329 : Blo 413771 939329 := bstep (se 2 (by rfl) ⟨352248, by rfl⟩ : syracuseStep 939329 = 704497) B704497
theorem B415051 : Blo 413771 415051 := bstep (se 1 (by rfl) ⟨311288, by rfl⟩ : syracuseStep 415051 = 622577) B622577
theorem B1201483 : Blo 413771 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B415063 : Blo 413771 415063 := bstep (se 1 (by rfl) ⟨311297, by rfl⟩ : syracuseStep 415063 = 622595) B622595
theorem B415083 : Blo 413771 415083 := bstep (se 1 (by rfl) ⟨311312, by rfl⟩ : syracuseStep 415083 = 622625) B622625
theorem B415095 : Blo 413771 415095 := bstep (se 1 (by rfl) ⟨311321, by rfl⟩ : syracuseStep 415095 = 622643) B622643
theorem B841099 : Blo 413771 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B415115 : Blo 413771 415115 := bstep (se 1 (by rfl) ⟨311336, by rfl⟩ : syracuseStep 415115 = 622673) B622673
theorem B1398167 : Blo 413771 1398167 := bstep (se 1 (by rfl) ⟨1048625, by rfl⟩ : syracuseStep 1398167 = 2097251) B2097251
theorem B415127 : Blo 413771 415127 := bstep (se 1 (by rfl) ⟨311345, by rfl⟩ : syracuseStep 415127 = 622691) B622691
theorem B415147 : Blo 413771 415147 := bstep (se 1 (by rfl) ⟨311360, by rfl⟩ : syracuseStep 415147 = 622721) B622721
theorem B415159 : Blo 413771 415159 := bstep (se 1 (by rfl) ⟨311369, by rfl⟩ : syracuseStep 415159 = 622739) B622739
theorem B415179 : Blo 413771 415179 := bstep (se 1 (by rfl) ⟨311384, by rfl⟩ : syracuseStep 415179 = 622769) B622769
theorem B415191 : Blo 413771 415191 := bstep (se 1 (by rfl) ⟨311393, by rfl⟩ : syracuseStep 415191 = 622787) B622787
theorem B415211 : Blo 413771 415211 := bstep (se 1 (by rfl) ⟨311408, by rfl⟩ : syracuseStep 415211 = 622817) B622817
theorem B415223 : Blo 413771 415223 := bstep (se 1 (by rfl) ⟨311417, by rfl⟩ : syracuseStep 415223 = 622835) B622835
theorem B710155 : Blo 413771 710155 := bstep (se 1 (by rfl) ⟨532616, by rfl⟩ : syracuseStep 710155 = 1065233) B1065233
theorem B415243 : Blo 413771 415243 := bstep (se 1 (by rfl) ⟨311432, by rfl⟩ : syracuseStep 415243 = 622865) B622865
theorem B415255 : Blo 413771 415255 := bstep (se 1 (by rfl) ⟨311441, by rfl⟩ : syracuseStep 415255 = 622883) B622883
theorem B939545 : Blo 413771 939545 := bstep (se 2 (by rfl) ⟨352329, by rfl⟩ : syracuseStep 939545 = 704659) B704659
theorem B415275 : Blo 413771 415275 := bstep (se 1 (by rfl) ⟨311456, by rfl⟩ : syracuseStep 415275 = 622913) B622913
theorem B1496627 : Blo 413771 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B415287 : Blo 413771 415287 := bstep (se 1 (by rfl) ⟨311465, by rfl⟩ : syracuseStep 415287 = 622931) B622931
theorem B415307 : Blo 413771 415307 := bstep (se 1 (by rfl) ⟨311480, by rfl⟩ : syracuseStep 415307 = 622961) B622961
theorem B415319 : Blo 413771 415319 := bstep (se 1 (by rfl) ⟨311489, by rfl⟩ : syracuseStep 415319 = 622979) B622979
theorem B415339 : Blo 413771 415339 := bstep (se 1 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 415339 = 623009) B623009
theorem B939635 : Blo 413771 939635 := bstep (se 1 (by rfl) ⟨704726, by rfl⟩ : syracuseStep 939635 = 1409453) B1409453
theorem B415351 : Blo 413771 415351 := bstep (se 1 (by rfl) ⟨311513, by rfl⟩ : syracuseStep 415351 = 623027) B623027
theorem B415371 : Blo 413771 415371 := bstep (se 1 (by rfl) ⟨311528, by rfl⟩ : syracuseStep 415371 = 623057) B623057
theorem B415383 : Blo 413771 415383 := bstep (se 1 (by rfl) ⟨311537, by rfl⟩ : syracuseStep 415383 = 623075) B623075
theorem B939671 : Blo 413771 939671 := bstep (se 1 (by rfl) ⟨704753, by rfl⟩ : syracuseStep 939671 = 1409507) B1409507
theorem B415403 : Blo 413771 415403 := bstep (se 1 (by rfl) ⟨311552, by rfl⟩ : syracuseStep 415403 = 623105) B623105
theorem B415415 : Blo 413771 415415 := bstep (se 1 (by rfl) ⟨311561, by rfl⟩ : syracuseStep 415415 = 623123) B623123
theorem B415435 : Blo 413771 415435 := bstep (se 1 (by rfl) ⟨311576, by rfl⟩ : syracuseStep 415435 = 623153) B623153
theorem B415447 : Blo 413771 415447 := bstep (se 1 (by rfl) ⟨311585, by rfl⟩ : syracuseStep 415447 = 623171) B623171
theorem B415467 : Blo 413771 415467 := bstep (se 1 (by rfl) ⟨311600, by rfl⟩ : syracuseStep 415467 = 623201) B623201
theorem B415479 : Blo 413771 415479 := bstep (se 1 (by rfl) ⟨311609, by rfl⟩ : syracuseStep 415479 = 623219) B623219
theorem B415499 : Blo 413771 415499 := bstep (se 1 (by rfl) ⟨311624, by rfl⟩ : syracuseStep 415499 = 623249) B623249
theorem B415511 : Blo 413771 415511 := bstep (se 1 (by rfl) ⟨311633, by rfl⟩ : syracuseStep 415511 = 623267) B623267
theorem B415531 : Blo 413771 415531 := bstep (se 1 (by rfl) ⟨311648, by rfl⟩ : syracuseStep 415531 = 623297) B623297
theorem B415543 : Blo 413771 415543 := bstep (se 1 (by rfl) ⟨311657, by rfl⟩ : syracuseStep 415543 = 623315) B623315
theorem B415563 : Blo 413771 415563 := bstep (se 1 (by rfl) ⟨311672, by rfl⟩ : syracuseStep 415563 = 623345) B623345
theorem B3200843 : Blo 413771 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B939851 : Blo 413771 939851 := bstep (se 1 (by rfl) ⟨704888, by rfl⟩ : syracuseStep 939851 = 1409777) B1409777
theorem B415575 : Blo 413771 415575 := bstep (se 1 (by rfl) ⟨311681, by rfl⟩ : syracuseStep 415575 = 623363) B623363
theorem B415595 : Blo 413771 415595 := bstep (se 1 (by rfl) ⟨311696, by rfl⟩ : syracuseStep 415595 = 623393) B623393
theorem B415607 : Blo 413771 415607 := bstep (se 1 (by rfl) ⟨311705, by rfl⟩ : syracuseStep 415607 = 623411) B623411
theorem B939905 : Blo 413771 939905 := bstep (se 2 (by rfl) ⟨352464, by rfl⟩ : syracuseStep 939905 = 704929) B704929
theorem B415627 : Blo 413771 415627 := bstep (se 1 (by rfl) ⟨311720, by rfl⟩ : syracuseStep 415627 = 623441) B623441
theorem B415639 : Blo 413771 415639 := bstep (se 1 (by rfl) ⟨311729, by rfl⟩ : syracuseStep 415639 = 623459) B623459
theorem B415659 : Blo 413771 415659 := bstep (se 1 (by rfl) ⟨311744, by rfl⟩ : syracuseStep 415659 = 623489) B623489
theorem B1398707 : Blo 413771 1398707 := bstep (se 1 (by rfl) ⟨1049030, by rfl⟩ : syracuseStep 1398707 = 2098061) B2098061
theorem B415671 : Blo 413771 415671 := bstep (se 1 (by rfl) ⟨311753, by rfl⟩ : syracuseStep 415671 = 623507) B623507
theorem B415691 : Blo 413771 415691 := bstep (se 1 (by rfl) ⟨311768, by rfl⟩ : syracuseStep 415691 = 623537) B623537
theorem B415703 : Blo 413771 415703 := bstep (se 1 (by rfl) ⟨311777, by rfl⟩ : syracuseStep 415703 = 623555) B623555
theorem B415723 : Blo 413771 415723 := bstep (se 1 (by rfl) ⟨311792, by rfl⟩ : syracuseStep 415723 = 623585) B623585
theorem B415735 : Blo 413771 415735 := bstep (se 1 (by rfl) ⟨311801, by rfl⟩ : syracuseStep 415735 = 623603) B623603
theorem B415755 : Blo 413771 415755 := bstep (se 1 (by rfl) ⟨311816, by rfl⟩ : syracuseStep 415755 = 623633) B623633
theorem B415767 : Blo 413771 415767 := bstep (se 1 (by rfl) ⟨311825, by rfl⟩ : syracuseStep 415767 = 623651) B623651
theorem B415787 : Blo 413771 415787 := bstep (se 1 (by rfl) ⟨311840, by rfl⟩ : syracuseStep 415787 = 623681) B623681
theorem B415799 : Blo 413771 415799 := bstep (se 1 (by rfl) ⟨311849, by rfl⟩ : syracuseStep 415799 = 623699) B623699
theorem B415819 : Blo 413771 415819 := bstep (se 1 (by rfl) ⟨311864, by rfl⟩ : syracuseStep 415819 = 623729) B623729
theorem B415831 : Blo 413771 415831 := bstep (se 1 (by rfl) ⟨311873, by rfl⟩ : syracuseStep 415831 = 623747) B623747
theorem B415851 : Blo 413771 415851 := bstep (se 1 (by rfl) ⟨311888, by rfl⟩ : syracuseStep 415851 = 623777) B623777
theorem B415863 : Blo 413771 415863 := bstep (se 1 (by rfl) ⟨311897, by rfl⟩ : syracuseStep 415863 = 623795) B623795
theorem B415883 : Blo 413771 415883 := bstep (se 1 (by rfl) ⟨311912, by rfl⟩ : syracuseStep 415883 = 623825) B623825
theorem B415895 : Blo 413771 415895 := bstep (se 1 (by rfl) ⟨311921, by rfl⟩ : syracuseStep 415895 = 623843) B623843
theorem B415915 : Blo 413771 415915 := bstep (se 1 (by rfl) ⟨311936, by rfl⟩ : syracuseStep 415915 = 623873) B623873
theorem B415927 : Blo 413771 415927 := bstep (se 1 (by rfl) ⟨311945, by rfl⟩ : syracuseStep 415927 = 623891) B623891
theorem B1398977 : Blo 413771 1398977 := bstep (se 2 (by rfl) ⟨524616, by rfl⟩ : syracuseStep 1398977 = 1049233) B1049233
theorem B415947 : Blo 413771 415947 := bstep (se 1 (by rfl) ⟨311960, by rfl⟩ : syracuseStep 415947 = 623921) B623921
theorem B415959 : Blo 413771 415959 := bstep (se 1 (by rfl) ⟨311969, by rfl⟩ : syracuseStep 415959 = 623939) B623939
theorem B415979 : Blo 413771 415979 := bstep (se 1 (by rfl) ⟨311984, by rfl⟩ : syracuseStep 415979 = 623969) B623969
theorem B415991 : Blo 413771 415991 := bstep (se 1 (by rfl) ⟨311993, by rfl⟩ : syracuseStep 415991 = 623987) B623987
theorem B416011 : Blo 413771 416011 := bstep (se 1 (by rfl) ⟨312008, by rfl⟩ : syracuseStep 416011 = 624017) B624017
theorem B1497361 : Blo 413771 1497361 := bstep (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) B1123021
theorem B416023 : Blo 413771 416023 := bstep (se 1 (by rfl) ⟨312017, by rfl⟩ : syracuseStep 416023 = 624035) B624035
theorem B416043 : Blo 413771 416043 := bstep (se 1 (by rfl) ⟨312032, by rfl⟩ : syracuseStep 416043 = 624065) B624065
theorem B416055 : Blo 413771 416055 := bstep (se 1 (by rfl) ⟨312041, by rfl⟩ : syracuseStep 416055 = 624083) B624083
theorem B3561803 : Blo 413771 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B416075 : Blo 413771 416075 := bstep (se 1 (by rfl) ⟨312056, by rfl⟩ : syracuseStep 416075 = 624113) B624113
theorem B416087 : Blo 413771 416087 := bstep (se 1 (by rfl) ⟨312065, by rfl⟩ : syracuseStep 416087 = 624131) B624131
theorem B416107 : Blo 413771 416107 := bstep (se 1 (by rfl) ⟨312080, by rfl⟩ : syracuseStep 416107 = 624161) B624161
theorem B416119 : Blo 413771 416119 := bstep (se 1 (by rfl) ⟨312089, by rfl⟩ : syracuseStep 416119 = 624179) B624179
theorem B416139 : Blo 413771 416139 := bstep (se 1 (by rfl) ⟨312104, by rfl⟩ : syracuseStep 416139 = 624209) B624209
theorem B416151 : Blo 413771 416151 := bstep (se 1 (by rfl) ⟨312113, by rfl⟩ : syracuseStep 416151 = 624227) B624227
theorem B416171 : Blo 413771 416171 := bstep (se 1 (by rfl) ⟨312128, by rfl⟩ : syracuseStep 416171 = 624257) B624257
theorem B416183 : Blo 413771 416183 := bstep (se 1 (by rfl) ⟨312137, by rfl⟩ : syracuseStep 416183 = 624275) B624275
theorem B416203 : Blo 413771 416203 := bstep (se 1 (by rfl) ⟨312152, by rfl⟩ : syracuseStep 416203 = 624305) B624305
theorem B416215 : Blo 413771 416215 := bstep (se 1 (by rfl) ⟨312161, by rfl⟩ : syracuseStep 416215 = 624323) B624323
theorem B416235 : Blo 413771 416235 := bstep (se 1 (by rfl) ⟨312176, by rfl⟩ : syracuseStep 416235 = 624353) B624353
theorem B416247 : Blo 413771 416247 := bstep (se 1 (by rfl) ⟨312185, by rfl⟩ : syracuseStep 416247 = 624371) B624371
theorem B416267 : Blo 413771 416267 := bstep (se 1 (by rfl) ⟨312200, by rfl⟩ : syracuseStep 416267 = 624401) B624401
theorem B1989137 : Blo 413771 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B416279 : Blo 413771 416279 := bstep (se 1 (by rfl) ⟨312209, by rfl⟩ : syracuseStep 416279 = 624419) B624419
theorem B416299 : Blo 413771 416299 := bstep (se 1 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 416299 = 624449) B624449
theorem B416311 : Blo 413771 416311 := bstep (se 1 (by rfl) ⟨312233, by rfl⟩ : syracuseStep 416311 = 624467) B624467
theorem B416331 : Blo 413771 416331 := bstep (se 1 (by rfl) ⟨312248, by rfl⟩ : syracuseStep 416331 = 624497) B624497
theorem B416343 : Blo 413771 416343 := bstep (se 1 (by rfl) ⟨312257, by rfl⟩ : syracuseStep 416343 = 624515) B624515
theorem B416363 : Blo 413771 416363 := bstep (se 1 (by rfl) ⟨312272, by rfl⟩ : syracuseStep 416363 = 624545) B624545
theorem B416375 : Blo 413771 416375 := bstep (se 1 (by rfl) ⟨312281, by rfl⟩ : syracuseStep 416375 = 624563) B624563
theorem B3594883 : Blo 413771 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B416395 : Blo 413771 416395 := bstep (se 1 (by rfl) ⟨312296, by rfl⟩ : syracuseStep 416395 = 624593) B624593
theorem B416407 : Blo 413771 416407 := bstep (se 1 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 416407 = 624611) B624611
theorem B416427 : Blo 413771 416427 := bstep (se 1 (by rfl) ⟨312320, by rfl⟩ : syracuseStep 416427 = 624641) B624641
theorem B416439 : Blo 413771 416439 := bstep (se 1 (by rfl) ⟨312329, by rfl⟩ : syracuseStep 416439 = 624659) B624659
theorem B416459 : Blo 413771 416459 := bstep (se 1 (by rfl) ⟨312344, by rfl⟩ : syracuseStep 416459 = 624689) B624689
theorem B416471 : Blo 413771 416471 := bstep (se 1 (by rfl) ⟨312353, by rfl⟩ : syracuseStep 416471 = 624707) B624707
theorem B1399517 : Blo 413771 1399517 := bstep (se 3 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 1399517 = 524819) B524819
theorem B1596125 : Blo 413771 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B416491 : Blo 413771 416491 := bstep (se 1 (by rfl) ⟨312368, by rfl⟩ : syracuseStep 416491 = 624737) B624737
theorem B416503 : Blo 413771 416503 := bstep (se 1 (by rfl) ⟨312377, by rfl⟩ : syracuseStep 416503 = 624755) B624755
theorem B416523 : Blo 413771 416523 := bstep (se 1 (by rfl) ⟨312392, by rfl⟩ : syracuseStep 416523 = 624785) B624785
theorem B416535 : Blo 413771 416535 := bstep (se 1 (by rfl) ⟨312401, by rfl⟩ : syracuseStep 416535 = 624803) B624803
theorem B416555 : Blo 413771 416555 := bstep (se 1 (by rfl) ⟨312416, by rfl⟩ : syracuseStep 416555 = 624833) B624833
theorem B2841389 : Blo 413771 2841389 := bstep (se 3 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 2841389 = 1065521) B1065521
theorem B416567 : Blo 413771 416567 := bstep (se 1 (by rfl) ⟨312425, by rfl⟩ : syracuseStep 416567 = 624851) B624851
theorem B416587 : Blo 413771 416587 := bstep (se 1 (by rfl) ⟨312440, by rfl⟩ : syracuseStep 416587 = 624881) B624881
theorem B416599 : Blo 413771 416599 := bstep (se 1 (by rfl) ⟨312449, by rfl⟩ : syracuseStep 416599 = 624899) B624899
theorem B416619 : Blo 413771 416619 := bstep (se 1 (by rfl) ⟨312464, by rfl⟩ : syracuseStep 416619 = 624929) B624929
theorem B416631 : Blo 413771 416631 := bstep (se 1 (by rfl) ⟨312473, by rfl⟩ : syracuseStep 416631 = 624947) B624947
theorem B416651 : Blo 413771 416651 := bstep (se 1 (by rfl) ⟨312488, by rfl⟩ : syracuseStep 416651 = 624977) B624977
theorem B416663 : Blo 413771 416663 := bstep (se 1 (by rfl) ⟨312497, by rfl⟩ : syracuseStep 416663 = 624995) B624995
theorem B416683 : Blo 413771 416683 := bstep (se 1 (by rfl) ⟨312512, by rfl⟩ : syracuseStep 416683 = 625025) B625025
theorem B416695 : Blo 413771 416695 := bstep (se 1 (by rfl) ⟨312521, by rfl⟩ : syracuseStep 416695 = 625043) B625043
theorem B416715 : Blo 413771 416715 := bstep (se 1 (by rfl) ⟨312536, by rfl⟩ : syracuseStep 416715 = 625073) B625073
theorem B416727 : Blo 413771 416727 := bstep (se 1 (by rfl) ⟨312545, by rfl⟩ : syracuseStep 416727 = 625091) B625091
theorem B416747 : Blo 413771 416747 := bstep (se 1 (by rfl) ⟨312560, by rfl⟩ : syracuseStep 416747 = 625121) B625121
theorem B416759 : Blo 413771 416759 := bstep (se 1 (by rfl) ⟨312569, by rfl⟩ : syracuseStep 416759 = 625139) B625139
theorem B416779 : Blo 413771 416779 := bstep (se 1 (by rfl) ⟨312584, by rfl⟩ : syracuseStep 416779 = 625169) B625169
theorem B416791 : Blo 413771 416791 := bstep (se 1 (by rfl) ⟨312593, by rfl⟩ : syracuseStep 416791 = 625187) B625187
theorem B416811 : Blo 413771 416811 := bstep (se 1 (by rfl) ⟨312608, by rfl⟩ : syracuseStep 416811 = 625217) B625217
theorem B416823 : Blo 413771 416823 := bstep (se 1 (by rfl) ⟨312617, by rfl⟩ : syracuseStep 416823 = 625235) B625235
theorem B842827 : Blo 413771 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B416843 : Blo 413771 416843 := bstep (se 1 (by rfl) ⟨312632, by rfl⟩ : syracuseStep 416843 = 625265) B625265
theorem B416855 : Blo 413771 416855 := bstep (se 1 (by rfl) ⟨312641, by rfl⟩ : syracuseStep 416855 = 625283) B625283
theorem B416875 : Blo 413771 416875 := bstep (se 1 (by rfl) ⟨312656, by rfl⟩ : syracuseStep 416875 = 625313) B625313
theorem B416887 : Blo 413771 416887 := bstep (se 1 (by rfl) ⟨312665, by rfl⟩ : syracuseStep 416887 = 625331) B625331
theorem B7560323 : Blo 413771 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B416907 : Blo 413771 416907 := bstep (se 1 (by rfl) ⟨312680, by rfl⟩ : syracuseStep 416907 = 625361) B625361
theorem B416919 : Blo 413771 416919 := bstep (se 1 (by rfl) ⟨312689, by rfl⟩ : syracuseStep 416919 = 625379) B625379
theorem B416939 : Blo 413771 416939 := bstep (se 1 (by rfl) ⟨312704, by rfl⟩ : syracuseStep 416939 = 625409) B625409
theorem B416951 : Blo 413771 416951 := bstep (se 1 (by rfl) ⟨312713, by rfl⟩ : syracuseStep 416951 = 625427) B625427
theorem B416971 : Blo 413771 416971 := bstep (se 1 (by rfl) ⟨312728, by rfl⟩ : syracuseStep 416971 = 625457) B625457
theorem B416983 : Blo 413771 416983 := bstep (se 1 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 416983 = 625475) B625475
theorem B417003 : Blo 413771 417003 := bstep (se 1 (by rfl) ⟨312752, by rfl⟩ : syracuseStep 417003 = 625505) B625505
theorem B417015 : Blo 413771 417015 := bstep (se 1 (by rfl) ⟨312761, by rfl⟩ : syracuseStep 417015 = 625523) B625523
theorem B417035 : Blo 413771 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B417047 : Blo 413771 417047 := bstep (se 1 (by rfl) ⟨312785, by rfl⟩ : syracuseStep 417047 = 625571) B625571
theorem B417067 : Blo 413771 417067 := bstep (se 1 (by rfl) ⟨312800, by rfl⟩ : syracuseStep 417067 = 625601) B625601
theorem B417079 : Blo 413771 417079 := bstep (se 1 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 417079 = 625619) B625619
theorem B417099 : Blo 413771 417099 := bstep (se 1 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 417099 = 625649) B625649
theorem B417111 : Blo 413771 417111 := bstep (se 1 (by rfl) ⟨312833, by rfl⟩ : syracuseStep 417111 = 625667) B625667
theorem B417131 : Blo 413771 417131 := bstep (se 1 (by rfl) ⟨312848, by rfl⟩ : syracuseStep 417131 = 625697) B625697
theorem B417143 : Blo 413771 417143 := bstep (se 1 (by rfl) ⟨312857, by rfl⟩ : syracuseStep 417143 = 625715) B625715
theorem B417163 : Blo 413771 417163 := bstep (se 1 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 417163 = 625745) B625745
theorem B417175 : Blo 413771 417175 := bstep (se 1 (by rfl) ⟨312881, by rfl⟩ : syracuseStep 417175 = 625763) B625763
theorem B417195 : Blo 413771 417195 := bstep (se 1 (by rfl) ⟨312896, by rfl⟩ : syracuseStep 417195 = 625793) B625793
theorem B417207 : Blo 413771 417207 := bstep (se 1 (by rfl) ⟨312905, by rfl⟩ : syracuseStep 417207 = 625811) B625811
theorem B417227 : Blo 413771 417227 := bstep (se 1 (by rfl) ⟨312920, by rfl⟩ : syracuseStep 417227 = 625841) B625841
theorem B417239 : Blo 413771 417239 := bstep (se 1 (by rfl) ⟨312929, by rfl⟩ : syracuseStep 417239 = 625859) B625859
theorem B417259 : Blo 413771 417259 := bstep (se 1 (by rfl) ⟨312944, by rfl⟩ : syracuseStep 417259 = 625889) B625889
theorem B417271 : Blo 413771 417271 := bstep (se 1 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 417271 = 625907) B625907
theorem B417291 : Blo 413771 417291 := bstep (se 1 (by rfl) ⟨312968, by rfl⟩ : syracuseStep 417291 = 625937) B625937
theorem B417303 : Blo 413771 417303 := bstep (se 1 (by rfl) ⟨312977, by rfl⟩ : syracuseStep 417303 = 625955) B625955
theorem B417323 : Blo 413771 417323 := bstep (se 1 (by rfl) ⟨312992, by rfl⟩ : syracuseStep 417323 = 625985) B625985
theorem B417335 : Blo 413771 417335 := bstep (se 1 (by rfl) ⟨313001, by rfl⟩ : syracuseStep 417335 = 626003) B626003
theorem B417355 : Blo 413771 417355 := bstep (se 1 (by rfl) ⟨313016, by rfl⟩ : syracuseStep 417355 = 626033) B626033
theorem B417367 : Blo 413771 417367 := bstep (se 1 (by rfl) ⟨313025, by rfl⟩ : syracuseStep 417367 = 626051) B626051
theorem B417387 : Blo 413771 417387 := bstep (se 1 (by rfl) ⟨313040, by rfl⟩ : syracuseStep 417387 = 626081) B626081
theorem B417399 : Blo 413771 417399 := bstep (se 1 (by rfl) ⟨313049, by rfl⟩ : syracuseStep 417399 = 626099) B626099
theorem B417419 : Blo 413771 417419 := bstep (se 1 (by rfl) ⟨313064, by rfl⟩ : syracuseStep 417419 = 626129) B626129
theorem B417431 : Blo 413771 417431 := bstep (se 1 (by rfl) ⟨313073, by rfl⟩ : syracuseStep 417431 = 626147) B626147
theorem B417451 : Blo 413771 417451 := bstep (se 1 (by rfl) ⟨313088, by rfl⟩ : syracuseStep 417451 = 626177) B626177
theorem B417463 : Blo 413771 417463 := bstep (se 1 (by rfl) ⟨313097, by rfl⟩ : syracuseStep 417463 = 626195) B626195
theorem B417483 : Blo 413771 417483 := bstep (se 1 (by rfl) ⟨313112, by rfl⟩ : syracuseStep 417483 = 626225) B626225
theorem B417495 : Blo 413771 417495 := bstep (se 1 (by rfl) ⟨313121, by rfl⟩ : syracuseStep 417495 = 626243) B626243
theorem B417515 : Blo 413771 417515 := bstep (se 1 (by rfl) ⟨313136, by rfl⟩ : syracuseStep 417515 = 626273) B626273
theorem B417527 : Blo 413771 417527 := bstep (se 1 (by rfl) ⟨313145, by rfl⟩ : syracuseStep 417527 = 626291) B626291
theorem B417547 : Blo 413771 417547 := bstep (se 1 (by rfl) ⟨313160, by rfl⟩ : syracuseStep 417547 = 626321) B626321
theorem B417559 : Blo 413771 417559 := bstep (se 1 (by rfl) ⟨313169, by rfl⟩ : syracuseStep 417559 = 626339) B626339
theorem B417579 : Blo 413771 417579 := bstep (se 1 (by rfl) ⟨313184, by rfl⟩ : syracuseStep 417579 = 626369) B626369
theorem B417591 : Blo 413771 417591 := bstep (se 1 (by rfl) ⟨313193, by rfl⟩ : syracuseStep 417591 = 626387) B626387
theorem B1400651 : Blo 413771 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B417611 : Blo 413771 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B417623 : Blo 413771 417623 := bstep (se 1 (by rfl) ⟨313217, by rfl⟩ : syracuseStep 417623 = 626435) B626435
theorem B417643 : Blo 413771 417643 := bstep (se 1 (by rfl) ⟨313232, by rfl⟩ : syracuseStep 417643 = 626465) B626465
theorem B417655 : Blo 413771 417655 := bstep (se 1 (by rfl) ⟨313241, by rfl⟩ : syracuseStep 417655 = 626483) B626483
theorem B417675 : Blo 413771 417675 := bstep (se 1 (by rfl) ⟨313256, by rfl⟩ : syracuseStep 417675 = 626513) B626513
theorem B417687 : Blo 413771 417687 := bstep (se 1 (by rfl) ⟨313265, by rfl⟩ : syracuseStep 417687 = 626531) B626531
theorem B417707 : Blo 413771 417707 := bstep (se 1 (by rfl) ⟨313280, by rfl⟩ : syracuseStep 417707 = 626561) B626561
theorem B417719 : Blo 413771 417719 := bstep (se 1 (by rfl) ⟨313289, by rfl⟩ : syracuseStep 417719 = 626579) B626579
theorem B417739 : Blo 413771 417739 := bstep (se 1 (by rfl) ⟨313304, by rfl⟩ : syracuseStep 417739 = 626609) B626609
theorem B417751 : Blo 413771 417751 := bstep (se 1 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 417751 = 626627) B626627
theorem B417771 : Blo 413771 417771 := bstep (se 1 (by rfl) ⟨313328, by rfl⟩ : syracuseStep 417771 = 626657) B626657
theorem B1400921 : Blo 413771 1400921 := bstep (se 2 (by rfl) ⟨525345, by rfl⟩ : syracuseStep 1400921 = 1050691) B1050691
theorem B1335703 : Blo 413771 1335703 := bstep (se 1 (by rfl) ⟨1001777, by rfl⟩ : syracuseStep 1335703 = 2003555) B2003555
theorem B1991213 : Blo 413771 1991213 := bstep (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) B746705
theorem B713303 : Blo 413771 713303 := bstep (se 1 (by rfl) ⟨534977, by rfl⟩ : syracuseStep 713303 = 1069955) B1069955
theorem B1401623 : Blo 413771 1401623 := bstep (se 1 (by rfl) ⟨1051217, by rfl⟩ : syracuseStep 1401623 = 2102435) B2102435
theorem B1336139 : Blo 413771 1336139 := bstep (se 1 (by rfl) ⟨1002104, by rfl⟩ : syracuseStep 1336139 = 2004209) B2004209
theorem B746647 : Blo 413771 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B1402163 : Blo 413771 1402163 := bstep (se 1 (by rfl) ⟨1051622, by rfl⟩ : syracuseStep 1402163 = 2103245) B2103245
theorem B1598899 : Blo 413771 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1500619 : Blo 413771 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B1402433 : Blo 413771 1402433 := bstep (se 2 (by rfl) ⟨525912, by rfl⟩ : syracuseStep 1402433 = 1051825) B1051825
theorem B1336907 : Blo 413771 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B6416023 : Blo 413771 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B13526837 : Blo 413771 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B1337305 : Blo 413771 1337305 := bstep (se 2 (by rfl) ⟨501489, by rfl⟩ : syracuseStep 1337305 = 1002979) B1002979
theorem B1337419 : Blo 413771 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B1402973 : Blo 413771 1402973 := bstep (se 3 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 1402973 = 526115) B526115
theorem B2845003 : Blo 413771 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B1337921 : Blo 413771 1337921 := bstep (se 2 (by rfl) ⟨501720, by rfl⟩ : syracuseStep 1337921 = 1003441) B1003441
theorem B2845277 : Blo 413771 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B1502003 : Blo 413771 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1404107 : Blo 413771 1404107 := bstep (se 1 (by rfl) ⟨1053080, by rfl⟩ : syracuseStep 1404107 = 2106161) B2106161
theorem B1404377 : Blo 413771 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B749387 : Blo 413771 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B1405079 : Blo 413771 1405079 := bstep (se 1 (by rfl) ⟨1053809, by rfl⟩ : syracuseStep 1405079 = 2107619) B2107619
theorem B3371329 : Blo 413771 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B1405619 : Blo 413771 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B3142475 : Blo 413771 3142475 := bstep (se 1 (by rfl) ⟨2356856, by rfl⟩ : syracuseStep 3142475 = 4713713) B4713713
theorem B1405889 : Blo 413771 1405889 := bstep (se 2 (by rfl) ⟨527208, by rfl⟩ : syracuseStep 1405889 = 1054417) B1054417
theorem B2651237 : Blo 413771 2651237 := bstep (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) B497107
theorem B5076269 : Blo 413771 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B1406429 : Blo 413771 1406429 := bstep (se 3 (by rfl) ⟨263705, by rfl⟩ : syracuseStep 1406429 = 527411) B527411
theorem B3601955 : Blo 413771 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B2651723 : Blo 413771 2651723 := bstep (se 1 (by rfl) ⟨1988792, by rfl⟩ : syracuseStep 2651723 = 3977585) B3977585
theorem B1603147 : Blo 413771 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B1767575 : Blo 413771 1767575 := bstep (se 1 (by rfl) ⟨1325681, by rfl⟩ : syracuseStep 1767575 = 2651363) B2651363
theorem B2586775 : Blo 413771 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B620747 : Blo 413771 620747 := bstep (se 1 (by rfl) ⟨465560, by rfl⟩ : syracuseStep 620747 = 931121) B931121
theorem B620759 : Blo 413771 620759 := bstep (se 1 (by rfl) ⟨465569, by rfl⟩ : syracuseStep 620759 = 931139) B931139
theorem B620825 : Blo 413771 620825 := bstep (se 2 (by rfl) ⟨232809, by rfl⟩ : syracuseStep 620825 = 465619) B465619
theorem B1571147 : Blo 413771 1571147 := bstep (se 1 (by rfl) ⟨1178360, by rfl⟩ : syracuseStep 1571147 = 2356721) B2356721
theorem B620939 : Blo 413771 620939 := bstep (se 1 (by rfl) ⟨465704, by rfl⟩ : syracuseStep 620939 = 931409) B931409
theorem B620951 : Blo 413771 620951 := bstep (se 1 (by rfl) ⟨465713, by rfl⟩ : syracuseStep 620951 = 931427) B931427
theorem B5700017 : Blo 413771 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B621017 : Blo 413771 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B1571345 : Blo 413771 1571345 := bstep (se 2 (by rfl) ⟨589254, by rfl⟩ : syracuseStep 1571345 = 1178509) B1178509
theorem B1604119 : Blo 413771 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B621131 : Blo 413771 621131 := bstep (se 1 (by rfl) ⟨465848, by rfl⟩ : syracuseStep 621131 = 931697) B931697
theorem B1407563 : Blo 413771 1407563 := bstep (se 1 (by rfl) ⟨1055672, by rfl⟩ : syracuseStep 1407563 = 2111345) B2111345
theorem B621143 : Blo 413771 621143 := bstep (se 1 (by rfl) ⟨465857, by rfl⟩ : syracuseStep 621143 = 931715) B931715
theorem B1997405 : Blo 413771 1997405 := bstep (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) B749027
theorem B621209 : Blo 413771 621209 := bstep (se 2 (by rfl) ⟨232953, by rfl⟩ : syracuseStep 621209 = 465907) B465907
theorem B621323 : Blo 413771 621323 := bstep (se 1 (by rfl) ⟨465992, by rfl⟩ : syracuseStep 621323 = 931985) B931985
theorem B621335 : Blo 413771 621335 := bstep (se 1 (by rfl) ⟨466001, by rfl⟩ : syracuseStep 621335 = 932003) B932003
theorem B621401 : Blo 413771 621401 := bstep (se 2 (by rfl) ⟨233025, by rfl⟩ : syracuseStep 621401 = 466051) B466051
theorem B1407833 : Blo 413771 1407833 := bstep (se 2 (by rfl) ⟨527937, by rfl⟩ : syracuseStep 1407833 = 1055875) B1055875
theorem B621515 : Blo 413771 621515 := bstep (se 1 (by rfl) ⟨466136, by rfl⟩ : syracuseStep 621515 = 932273) B932273
theorem B621527 : Blo 413771 621527 := bstep (se 1 (by rfl) ⟨466145, by rfl⟩ : syracuseStep 621527 = 932291) B932291
theorem B621593 : Blo 413771 621593 := bstep (se 2 (by rfl) ⟨233097, by rfl⟩ : syracuseStep 621593 = 466195) B466195
theorem B1768499 : Blo 413771 1768499 := bstep (se 1 (by rfl) ⟨1326374, by rfl⟩ : syracuseStep 1768499 = 2652749) B2652749
theorem B621707 : Blo 413771 621707 := bstep (se 1 (by rfl) ⟨466280, by rfl⟩ : syracuseStep 621707 = 932561) B932561
theorem B2096279 : Blo 413771 2096279 := bstep (se 1 (by rfl) ⟨1572209, by rfl⟩ : syracuseStep 2096279 = 3144419) B3144419
theorem B621719 : Blo 413771 621719 := bstep (se 1 (by rfl) ⟨466289, by rfl⟩ : syracuseStep 621719 = 932579) B932579
theorem B1047755 : Blo 413771 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B621785 : Blo 413771 621785 := bstep (se 2 (by rfl) ⟨233169, by rfl⟩ : syracuseStep 621785 = 466339) B466339
theorem B1572119 : Blo 413771 1572119 := bstep (se 1 (by rfl) ⟨1179089, by rfl⟩ : syracuseStep 1572119 = 2358179) B2358179
theorem B883993 : Blo 413771 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B621899 : Blo 413771 621899 := bstep (se 1 (by rfl) ⟨466424, by rfl⟩ : syracuseStep 621899 = 932849) B932849
theorem B2522443 : Blo 413771 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B621911 : Blo 413771 621911 := bstep (se 1 (by rfl) ⟨466433, by rfl⟩ : syracuseStep 621911 = 932867) B932867
theorem B2358679 : Blo 413771 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B621977 : Blo 413771 621977 := bstep (se 2 (by rfl) ⟨233241, by rfl⟩ : syracuseStep 621977 = 466483) B466483
theorem B1572317 : Blo 413771 1572317 := bstep (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) B589619
theorem B622091 : Blo 413771 622091 := bstep (se 1 (by rfl) ⟨466568, by rfl⟩ : syracuseStep 622091 = 933137) B933137
theorem B622103 : Blo 413771 622103 := bstep (se 1 (by rfl) ⟨466577, by rfl⟩ : syracuseStep 622103 = 933155) B933155
theorem B1408535 : Blo 413771 1408535 := bstep (se 1 (by rfl) ⟨1056401, by rfl⟩ : syracuseStep 1408535 = 2112803) B2112803
theorem B622169 : Blo 413771 622169 := bstep (se 2 (by rfl) ⟨233313, by rfl⟩ : syracuseStep 622169 = 466627) B466627
theorem B589465 : Blo 413771 589465 := bstep (se 2 (by rfl) ⟨221049, by rfl⟩ : syracuseStep 589465 = 442099) B442099
theorem B851609 : Blo 413771 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B622283 : Blo 413771 622283 := bstep (se 1 (by rfl) ⟨466712, by rfl⟩ : syracuseStep 622283 = 933425) B933425
theorem B622295 : Blo 413771 622295 := bstep (se 1 (by rfl) ⟨466721, by rfl⟩ : syracuseStep 622295 = 933443) B933443
theorem B622361 : Blo 413771 622361 := bstep (se 2 (by rfl) ⟨233385, by rfl⟩ : syracuseStep 622361 = 466771) B466771
theorem B524171 : Blo 413771 524171 := bstep (se 1 (by rfl) ⟨393128, by rfl⟩ : syracuseStep 524171 = 786257) B786257
theorem B622475 : Blo 413771 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B622487 : Blo 413771 622487 := bstep (se 1 (by rfl) ⟨466865, by rfl⟩ : syracuseStep 622487 = 933731) B933731
theorem B950231 : Blo 413771 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B622553 : Blo 413771 622553 := bstep (se 2 (by rfl) ⟨233457, by rfl⟩ : syracuseStep 622553 = 466915) B466915
theorem B1179613 : Blo 413771 1179613 := bstep (se 3 (by rfl) ⟨221177, by rfl⟩ : syracuseStep 1179613 = 442355) B442355
theorem B1179659 : Blo 413771 1179659 := bstep (se 1 (by rfl) ⟨884744, by rfl⟩ : syracuseStep 1179659 = 1769489) B1769489
theorem B622607 : Blo 413771 622607 := bstep (se 1 (by rfl) ⟨466955, by rfl⟩ : syracuseStep 622607 = 933911) B933911
theorem B622649 : Blo 413771 622649 := bstep (se 2 (by rfl) ⟨233493, by rfl⟩ : syracuseStep 622649 = 466987) B466987
theorem B622727 : Blo 413771 622727 := bstep (se 1 (by rfl) ⟨467045, by rfl⟩ : syracuseStep 622727 = 934091) B934091
theorem B622763 : Blo 413771 622763 := bstep (se 1 (by rfl) ⟨467072, by rfl⟩ : syracuseStep 622763 = 934145) B934145
theorem B622793 : Blo 413771 622793 := bstep (se 2 (by rfl) ⟨233547, by rfl⟩ : syracuseStep 622793 = 467095) B467095
theorem B1573121 : Blo 413771 1573121 := bstep (se 2 (by rfl) ⟨589920, by rfl⟩ : syracuseStep 1573121 = 1179841) B1179841
theorem B524551 : Blo 413771 524551 := bstep (se 1 (by rfl) ⟨393413, by rfl⟩ : syracuseStep 524551 = 786827) B786827
theorem B622907 : Blo 413771 622907 := bstep (se 1 (by rfl) ⟨467180, by rfl⟩ : syracuseStep 622907 = 934361) B934361
theorem B622967 : Blo 413771 622967 := bstep (se 1 (by rfl) ⟨467225, by rfl⟩ : syracuseStep 622967 = 934451) B934451
theorem B622991 : Blo 413771 622991 := bstep (se 1 (by rfl) ⟨467243, by rfl⟩ : syracuseStep 622991 = 934487) B934487
theorem B14418323 : Blo 413771 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B623033 : Blo 413771 623033 := bstep (se 2 (by rfl) ⟨233637, by rfl⟩ : syracuseStep 623033 = 467275) B467275
theorem B1999363 : Blo 413771 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B623111 : Blo 413771 623111 := bstep (se 1 (by rfl) ⟨467333, by rfl⟩ : syracuseStep 623111 = 934667) B934667
theorem B623147 : Blo 413771 623147 := bstep (se 1 (by rfl) ⟨467360, by rfl⟩ : syracuseStep 623147 = 934721) B934721
theorem B623177 : Blo 413771 623177 := bstep (se 2 (by rfl) ⟨233691, by rfl⟩ : syracuseStep 623177 = 467383) B467383
theorem B1770103 : Blo 413771 1770103 := bstep (se 1 (by rfl) ⟨1327577, by rfl⟩ : syracuseStep 1770103 = 2655155) B2655155
theorem B524971 : Blo 413771 524971 := bstep (se 1 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 524971 = 787457) B787457
theorem B623291 : Blo 413771 623291 := bstep (se 1 (by rfl) ⟨467468, by rfl⟩ : syracuseStep 623291 = 934937) B934937
theorem B1573577 : Blo 413771 1573577 := bstep (se 2 (by rfl) ⟨590091, by rfl⟩ : syracuseStep 1573577 = 1180183) B1180183
theorem B623351 : Blo 413771 623351 := bstep (se 1 (by rfl) ⟨467513, by rfl⟩ : syracuseStep 623351 = 935027) B935027
theorem B1049345 : Blo 413771 1049345 := bstep (se 2 (by rfl) ⟨393504, by rfl⟩ : syracuseStep 1049345 = 787009) B787009
theorem B623375 : Blo 413771 623375 := bstep (se 1 (by rfl) ⟨467531, by rfl⟩ : syracuseStep 623375 = 935063) B935063
theorem B1803023 : Blo 413771 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B623417 : Blo 413771 623417 := bstep (se 2 (by rfl) ⟨233781, by rfl⟩ : syracuseStep 623417 = 467563) B467563
theorem B787259 : Blo 413771 787259 := bstep (se 1 (by rfl) ⟨590444, by rfl⟩ : syracuseStep 787259 = 1180889) B1180889
theorem B623495 : Blo 413771 623495 := bstep (se 1 (by rfl) ⟨467621, by rfl⟩ : syracuseStep 623495 = 935243) B935243
theorem B525199 : Blo 413771 525199 := bstep (se 1 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 525199 = 787799) B787799
theorem B1409939 : Blo 413771 1409939 := bstep (se 1 (by rfl) ⟨1057454, by rfl⟩ : syracuseStep 1409939 = 2114909) B2114909
theorem B623531 : Blo 413771 623531 := bstep (se 1 (by rfl) ⟨467648, by rfl⟩ : syracuseStep 623531 = 935297) B935297
theorem B623561 : Blo 413771 623561 := bstep (se 2 (by rfl) ⟨233835, by rfl⟩ : syracuseStep 623561 = 467671) B467671
theorem B623675 : Blo 413771 623675 := bstep (se 1 (by rfl) ⟨467756, by rfl⟩ : syracuseStep 623675 = 935513) B935513
theorem B3998807 : Blo 413771 3998807 := bstep (se 1 (by rfl) ⟨2999105, by rfl⟩ : syracuseStep 3998807 = 5998211) B5998211
theorem B1049719 : Blo 413771 1049719 := bstep (se 1 (by rfl) ⟨787289, by rfl⟩ : syracuseStep 1049719 = 1574579) B1574579
theorem B623735 : Blo 413771 623735 := bstep (se 1 (by rfl) ⟨467801, by rfl⟩ : syracuseStep 623735 = 935603) B935603
theorem B623759 : Blo 413771 623759 := bstep (se 1 (by rfl) ⟨467819, by rfl⟩ : syracuseStep 623759 = 935639) B935639
theorem B623801 : Blo 413771 623801 := bstep (se 2 (by rfl) ⟨233925, by rfl⟩ : syracuseStep 623801 = 467851) B467851
theorem B623879 : Blo 413771 623879 := bstep (se 1 (by rfl) ⟨467909, by rfl⟩ : syracuseStep 623879 = 935819) B935819
theorem B787745 : Blo 413771 787745 := bstep (se 2 (by rfl) ⟨295404, by rfl⟩ : syracuseStep 787745 = 590809) B590809
theorem B623915 : Blo 413771 623915 := bstep (se 1 (by rfl) ⟨467936, by rfl⟩ : syracuseStep 623915 = 935873) B935873
theorem B623945 : Blo 413771 623945 := bstep (se 2 (by rfl) ⟨233979, by rfl⟩ : syracuseStep 623945 = 467959) B467959
theorem B2098547 : Blo 413771 2098547 := bstep (se 1 (by rfl) ⟨1573910, by rfl⟩ : syracuseStep 2098547 = 3147821) B3147821
theorem B787897 : Blo 413771 787897 := bstep (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) B590923
theorem B624059 : Blo 413771 624059 := bstep (se 1 (by rfl) ⟨468044, by rfl⟩ : syracuseStep 624059 = 936089) B936089
theorem B624119 : Blo 413771 624119 := bstep (se 1 (by rfl) ⟨468089, by rfl⟩ : syracuseStep 624119 = 936179) B936179
theorem B624143 : Blo 413771 624143 := bstep (se 1 (by rfl) ⟨468107, by rfl⟩ : syracuseStep 624143 = 936215) B936215
theorem B2885149 : Blo 413771 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B1050155 : Blo 413771 1050155 := bstep (se 1 (by rfl) ⟨787616, by rfl⟩ : syracuseStep 1050155 = 1575233) B1575233
theorem B624185 : Blo 413771 624185 := bstep (se 2 (by rfl) ⟨234069, by rfl⟩ : syracuseStep 624185 = 468139) B468139
theorem B1181243 : Blo 413771 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B1181299 : Blo 413771 1181299 := bstep (se 1 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 1181299 = 1771949) B1771949
theorem B525943 : Blo 413771 525943 := bstep (se 1 (by rfl) ⟨394457, by rfl⟩ : syracuseStep 525943 = 788915) B788915
theorem B624263 : Blo 413771 624263 := bstep (se 1 (by rfl) ⟨468197, by rfl⟩ : syracuseStep 624263 = 936395) B936395
theorem B624299 : Blo 413771 624299 := bstep (se 1 (by rfl) ⟨468224, by rfl⟩ : syracuseStep 624299 = 936449) B936449
theorem B624329 : Blo 413771 624329 := bstep (se 2 (by rfl) ⟨234123, by rfl⟩ : syracuseStep 624329 = 468247) B468247
theorem B624443 : Blo 413771 624443 := bstep (se 1 (by rfl) ⟨468332, by rfl⟩ : syracuseStep 624443 = 936665) B936665
theorem B2099033 : Blo 413771 2099033 := bstep (se 2 (by rfl) ⟨787137, by rfl⟩ : syracuseStep 2099033 = 1574275) B1574275
theorem B624503 : Blo 413771 624503 := bstep (se 1 (by rfl) ⟨468377, by rfl⟩ : syracuseStep 624503 = 936755) B936755
theorem B624527 : Blo 413771 624527 := bstep (se 1 (by rfl) ⟨468395, by rfl⟩ : syracuseStep 624527 = 936791) B936791
theorem B2131865 : Blo 413771 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B2000825 : Blo 413771 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B624569 : Blo 413771 624569 := bstep (se 2 (by rfl) ⟨234213, by rfl⟩ : syracuseStep 624569 = 468427) B468427
theorem B526267 : Blo 413771 526267 := bstep (se 1 (by rfl) ⟨394700, by rfl⟩ : syracuseStep 526267 = 789401) B789401
theorem B1181641 : Blo 413771 1181641 := bstep (se 2 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 1181641 = 886231) B886231
theorem B624647 : Blo 413771 624647 := bstep (se 1 (by rfl) ⟨468485, by rfl⟩ : syracuseStep 624647 = 936971) B936971
theorem B624683 : Blo 413771 624683 := bstep (se 1 (by rfl) ⟨468512, by rfl⟩ : syracuseStep 624683 = 937025) B937025
theorem B624713 : Blo 413771 624713 := bstep (se 2 (by rfl) ⟨234267, by rfl⟩ : syracuseStep 624713 = 468535) B468535
theorem B1771607 : Blo 413771 1771607 := bstep (se 1 (by rfl) ⟨1328705, by rfl⟩ : syracuseStep 1771607 = 2657411) B2657411
theorem B624827 : Blo 413771 624827 := bstep (se 1 (by rfl) ⟨468620, by rfl⟩ : syracuseStep 624827 = 937241) B937241
theorem B8554697 : Blo 413771 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B624887 : Blo 413771 624887 := bstep (se 1 (by rfl) ⟨468665, by rfl⟩ : syracuseStep 624887 = 937331) B937331
theorem B624911 : Blo 413771 624911 := bstep (se 1 (by rfl) ⟨468683, by rfl⟩ : syracuseStep 624911 = 937367) B937367
theorem B624953 : Blo 413771 624953 := bstep (se 2 (by rfl) ⟨234357, by rfl⟩ : syracuseStep 624953 = 468715) B468715
theorem B1050995 : Blo 413771 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B1051015 : Blo 413771 1051015 := bstep (se 1 (by rfl) ⟨788261, by rfl⟩ : syracuseStep 1051015 = 1576523) B1576523
theorem B2001287 : Blo 413771 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B625031 : Blo 413771 625031 := bstep (se 1 (by rfl) ⟨468773, by rfl⟩ : syracuseStep 625031 = 937547) B937547
theorem B526763 : Blo 413771 526763 := bstep (se 1 (by rfl) ⟨395072, by rfl⟩ : syracuseStep 526763 = 790145) B790145
theorem B625067 : Blo 413771 625067 := bstep (se 1 (by rfl) ⟨468800, by rfl⟩ : syracuseStep 625067 = 937601) B937601
theorem B625097 : Blo 413771 625097 := bstep (se 2 (by rfl) ⟨234411, by rfl⟩ : syracuseStep 625097 = 468823) B468823
theorem B4819409 : Blo 413771 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B8129009 : Blo 413771 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B625211 : Blo 413771 625211 := bstep (se 1 (by rfl) ⟨468908, by rfl⟩ : syracuseStep 625211 = 937817) B937817
theorem B625271 : Blo 413771 625271 := bstep (se 1 (by rfl) ⟨468953, by rfl⟩ : syracuseStep 625271 = 937907) B937907
theorem B625295 : Blo 413771 625295 := bstep (se 1 (by rfl) ⟨468971, by rfl⟩ : syracuseStep 625295 = 937943) B937943
theorem B1051289 : Blo 413771 1051289 := bstep (se 2 (by rfl) ⟨394233, by rfl⟩ : syracuseStep 1051289 = 788467) B788467
theorem B625337 : Blo 413771 625337 := bstep (se 2 (by rfl) ⟨234501, by rfl⟩ : syracuseStep 625337 = 469003) B469003
theorem B625415 : Blo 413771 625415 := bstep (se 1 (by rfl) ⟨469061, by rfl⟩ : syracuseStep 625415 = 938123) B938123
theorem B625451 : Blo 413771 625451 := bstep (se 1 (by rfl) ⟨469088, by rfl⟩ : syracuseStep 625451 = 938177) B938177
theorem B1051451 : Blo 413771 1051451 := bstep (se 1 (by rfl) ⟨788588, by rfl⟩ : syracuseStep 1051451 = 1577177) B1577177
theorem B625481 : Blo 413771 625481 := bstep (se 2 (by rfl) ⟨234555, by rfl⟩ : syracuseStep 625481 = 469111) B469111
theorem B527239 : Blo 413771 527239 := bstep (se 1 (by rfl) ⟨395429, by rfl⟩ : syracuseStep 527239 = 790859) B790859
theorem B625595 : Blo 413771 625595 := bstep (se 1 (by rfl) ⟨469196, by rfl⟩ : syracuseStep 625595 = 938393) B938393
theorem B625655 : Blo 413771 625655 := bstep (se 1 (by rfl) ⟨469241, by rfl⟩ : syracuseStep 625655 = 938483) B938483
theorem B5311493 : Blo 413771 5311493 := bstep (se 4 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 5311493 = 995905) B995905
theorem B1051663 : Blo 413771 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B625679 : Blo 413771 625679 := bstep (se 1 (by rfl) ⟨469259, by rfl⟩ : syracuseStep 625679 = 938519) B938519
theorem B625721 : Blo 413771 625721 := bstep (se 2 (by rfl) ⟨234645, by rfl⟩ : syracuseStep 625721 = 469291) B469291
theorem B625799 : Blo 413771 625799 := bstep (se 1 (by rfl) ⟨469349, by rfl⟩ : syracuseStep 625799 = 938699) B938699
theorem B625835 : Blo 413771 625835 := bstep (se 1 (by rfl) ⟨469376, by rfl⟩ : syracuseStep 625835 = 938753) B938753
theorem B789689 : Blo 413771 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B625865 : Blo 413771 625865 := bstep (se 2 (by rfl) ⟨234699, by rfl⟩ : syracuseStep 625865 = 469399) B469399
theorem B1051937 : Blo 413771 1051937 := bstep (se 2 (by rfl) ⟨394476, by rfl⟩ : syracuseStep 1051937 = 788953) B788953
theorem B625979 : Blo 413771 625979 := bstep (se 1 (by rfl) ⟨469484, by rfl⟩ : syracuseStep 625979 = 938969) B938969
theorem B527735 : Blo 413771 527735 := bstep (se 1 (by rfl) ⟨395801, by rfl⟩ : syracuseStep 527735 = 791603) B791603
theorem B626039 : Blo 413771 626039 := bstep (se 1 (by rfl) ⟨469529, by rfl⟩ : syracuseStep 626039 = 939059) B939059
theorem B626063 : Blo 413771 626063 := bstep (se 1 (by rfl) ⟨469547, by rfl⟩ : syracuseStep 626063 = 939095) B939095
theorem B626105 : Blo 413771 626105 := bstep (se 2 (by rfl) ⟨234789, by rfl⟩ : syracuseStep 626105 = 469579) B469579
theorem B2985437 : Blo 413771 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B626183 : Blo 413771 626183 := bstep (se 1 (by rfl) ⟨469637, by rfl⟩ : syracuseStep 626183 = 939275) B939275
theorem B527887 : Blo 413771 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B626219 : Blo 413771 626219 := bstep (se 1 (by rfl) ⟨469664, by rfl⟩ : syracuseStep 626219 = 939329) B939329
theorem B626249 : Blo 413771 626249 := bstep (se 2 (by rfl) ⟨234843, by rfl⟩ : syracuseStep 626249 = 469687) B469687
theorem B2363053 : Blo 413771 2363053 := bstep (se 3 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 2363053 = 886145) B886145
theorem B528059 : Blo 413771 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B626363 : Blo 413771 626363 := bstep (se 1 (by rfl) ⟨469772, by rfl⟩ : syracuseStep 626363 = 939545) B939545
theorem B2985665 : Blo 413771 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B626423 : Blo 413771 626423 := bstep (se 1 (by rfl) ⟨469817, by rfl⟩ : syracuseStep 626423 = 939635) B939635
theorem B14946049 : Blo 413771 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B1576705 : Blo 413771 1576705 := bstep (se 2 (by rfl) ⟨591264, by rfl⟩ : syracuseStep 1576705 = 1182529) B1182529
theorem B626447 : Blo 413771 626447 := bstep (se 1 (by rfl) ⟨469835, by rfl⟩ : syracuseStep 626447 = 939671) B939671
theorem B626489 : Blo 413771 626489 := bstep (se 2 (by rfl) ⟨234933, by rfl⟩ : syracuseStep 626489 = 469867) B469867
theorem B626567 : Blo 413771 626567 := bstep (se 1 (by rfl) ⟨469925, by rfl⟩ : syracuseStep 626567 = 939851) B939851
theorem B2101139 : Blo 413771 2101139 := bstep (se 1 (by rfl) ⟨1575854, by rfl⟩ : syracuseStep 2101139 = 3151709) B3151709
theorem B626603 : Blo 413771 626603 := bstep (se 1 (by rfl) ⟨469952, by rfl⟩ : syracuseStep 626603 = 939905) B939905
theorem B626633 : Blo 413771 626633 := bstep (se 2 (by rfl) ⟨234987, by rfl⟩ : syracuseStep 626633 = 469975) B469975
theorem B1773521 : Blo 413771 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B1183805 : Blo 413771 1183805 := bstep (se 3 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 1183805 = 443927) B443927
theorem B593993 : Blo 413771 593993 := bstep (se 2 (by rfl) ⟨222747, by rfl⟩ : syracuseStep 593993 = 445495) B445495
theorem B9605213 : Blo 413771 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B1052939 : Blo 413771 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B1184033 : Blo 413771 1184033 := bstep (se 2 (by rfl) ⟨444012, by rfl⟩ : syracuseStep 1184033 = 888025) B888025
theorem B2658845 : Blo 413771 2658845 := bstep (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) B997067
theorem B6754859 : Blo 413771 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B1184375 : Blo 413771 1184375 := bstep (se 1 (by rfl) ⟨888281, by rfl⟩ : syracuseStep 1184375 = 1776563) B1776563
theorem B1053587 : Blo 413771 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B791687 : Blo 413771 791687 := bstep (se 1 (by rfl) ⟨593765, by rfl⟩ : syracuseStep 791687 = 1187531) B1187531
theorem B1053881 : Blo 413771 1053881 := bstep (se 2 (by rfl) ⟨395205, by rfl⟩ : syracuseStep 1053881 = 790411) B790411
theorem B890041 : Blo 413771 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B4495105 : Blo 413771 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B1054579 : Blo 413771 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B890759 : Blo 413771 890759 := bstep (se 1 (by rfl) ⟨668069, by rfl⟩ : syracuseStep 890759 = 1336139) B1336139
theorem B1054721 : Blo 413771 1054721 := bstep (se 2 (by rfl) ⟨395520, by rfl⟩ : syracuseStep 1054721 = 791041) B791041
theorem B2365469 : Blo 413771 2365469 := bstep (se 3 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 2365469 = 887051) B887051
theorem B891271 : Blo 413771 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B1055177 : Blo 413771 1055177 := bstep (se 2 (by rfl) ⟨395691, by rfl⟩ : syracuseStep 1055177 = 791383) B791383
theorem B891425 : Blo 413771 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B9017891 : Blo 413771 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B1579607 : Blo 413771 1579607 := bstep (se 1 (by rfl) ⟨1184705, by rfl⟩ : syracuseStep 1579607 = 2369411) B2369411
theorem B1448567 : Blo 413771 1448567 := bstep (se 1 (by rfl) ⟨1086425, by rfl⟩ : syracuseStep 1448567 = 2172851) B2172851
theorem B1055531 : Blo 413771 1055531 := bstep (se 1 (by rfl) ⟨791648, by rfl⟩ : syracuseStep 1055531 = 1583297) B1583297
theorem B465799 : Blo 413771 465799 := bstep (se 1 (by rfl) ⟨349349, by rfl⟩ : syracuseStep 465799 = 698699) B698699
theorem B2104217 : Blo 413771 2104217 := bstep (se 2 (by rfl) ⟨789081, by rfl⟩ : syracuseStep 2104217 = 1578163) B1578163
theorem B1121291 : Blo 413771 1121291 := bstep (se 1 (by rfl) ⟨840968, by rfl⟩ : syracuseStep 1121291 = 1681937) B1681937
theorem B891947 : Blo 413771 891947 := bstep (se 1 (by rfl) ⟨668960, by rfl⟩ : syracuseStep 891947 = 1337921) B1337921
theorem B465979 : Blo 413771 465979 := bstep (se 1 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 465979 = 698969) B698969
theorem B1580093 : Blo 413771 1580093 := bstep (se 3 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 1580093 = 592535) B592535
theorem B1186903 : Blo 413771 1186903 := bstep (se 1 (by rfl) ⟨890177, by rfl⟩ : syracuseStep 1186903 = 1780355) B1780355
theorem B1121465 : Blo 413771 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B1187131 : Blo 413771 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B662969 : Blo 413771 662969 := bstep (se 2 (by rfl) ⟨248613, by rfl⟩ : syracuseStep 662969 = 497227) B497227
theorem B2137529 : Blo 413771 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B1187257 : Blo 413771 1187257 := bstep (se 2 (by rfl) ⟨445221, by rfl⟩ : syracuseStep 1187257 = 890443) B890443
theorem B466447 : Blo 413771 466447 := bstep (se 1 (by rfl) ⟨349835, by rfl⟩ : syracuseStep 466447 = 699671) B699671
theorem B1056523 : Blo 413771 1056523 := bstep (se 1 (by rfl) ⟨792392, by rfl⟩ : syracuseStep 1056523 = 1584785) B1584785
theorem B597775 : Blo 413771 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B499591 : Blo 413771 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B1056665 : Blo 413771 1056665 := bstep (se 2 (by rfl) ⟨396249, by rfl⟩ : syracuseStep 1056665 = 792499) B792499
theorem B466951 : Blo 413771 466951 := bstep (se 1 (by rfl) ⟨350213, by rfl⟩ : syracuseStep 466951 = 700427) B700427
theorem B1056827 : Blo 413771 1056827 := bstep (se 1 (by rfl) ⟨792620, by rfl⟩ : syracuseStep 1056827 = 1585241) B1585241
theorem B467131 : Blo 413771 467131 := bstep (se 1 (by rfl) ⟨350348, by rfl⟩ : syracuseStep 467131 = 700697) B700697
theorem B3449033 : Blo 413771 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B663943 : Blo 413771 663943 := bstep (se 1 (by rfl) ⟨497957, by rfl⟩ : syracuseStep 663943 = 995915) B995915
theorem B1057171 : Blo 413771 1057171 := bstep (se 1 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 1057171 = 1585757) B1585757
theorem B2367953 : Blo 413771 2367953 := bstep (se 2 (by rfl) ⟨887982, by rfl⟩ : syracuseStep 2367953 = 1775965) B1775965
theorem B1057313 : Blo 413771 1057313 := bstep (se 2 (by rfl) ⟨396492, by rfl⟩ : syracuseStep 1057313 = 792985) B792985
theorem B1778237 : Blo 413771 1778237 := bstep (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) B666839
theorem B467599 : Blo 413771 467599 := bstep (se 1 (by rfl) ⟨350699, by rfl⟩ : syracuseStep 467599 = 701399) B701399
theorem B3154625 : Blo 413771 3154625 := bstep (se 2 (by rfl) ⟨1182984, by rfl⟩ : syracuseStep 3154625 = 2365969) B2365969
theorem B2138825 : Blo 413771 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B1581839 : Blo 413771 1581839 := bstep (se 1 (by rfl) ⟨1186379, by rfl⟩ : syracuseStep 1581839 = 2372759) B2372759
theorem B664379 : Blo 413771 664379 := bstep (se 1 (by rfl) ⟨498284, by rfl⟩ : syracuseStep 664379 = 996569) B996569
theorem B4793177 : Blo 413771 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B3384179 : Blo 413771 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B1778699 : Blo 413771 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B468103 : Blo 413771 468103 := bstep (se 1 (by rfl) ⟨351077, by rfl⟩ : syracuseStep 468103 = 702155) B702155
theorem B468283 : Blo 413771 468283 := bstep (se 1 (by rfl) ⟨351212, by rfl⟩ : syracuseStep 468283 = 702425) B702425
theorem B1189181 : Blo 413771 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B1123769 : Blo 413771 1123769 := bstep (se 2 (by rfl) ⟨421413, by rfl⟩ : syracuseStep 1123769 = 842827) B842827
theorem B2106809 : Blo 413771 2106809 := bstep (se 2 (by rfl) ⟨790053, by rfl⟩ : syracuseStep 2106809 = 1580107) B1580107
theorem B468751 : Blo 413771 468751 := bstep (se 1 (by rfl) ⟨351563, by rfl⟩ : syracuseStep 468751 = 703127) B703127
theorem B698503 : Blo 413771 698503 := bstep (se 1 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 698503 = 1047755) B1047755
theorem B469255 : Blo 413771 469255 := bstep (se 1 (by rfl) ⟨351941, by rfl⟩ : syracuseStep 469255 = 703883) B703883
theorem B2369843 : Blo 413771 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B1583495 : Blo 413771 1583495 := bstep (se 1 (by rfl) ⟨1187621, by rfl⟩ : syracuseStep 1583495 = 2375243) B2375243
theorem B567739 : Blo 413771 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B469435 : Blo 413771 469435 := bstep (se 1 (by rfl) ⟨352076, by rfl⟩ : syracuseStep 469435 = 704153) B704153
theorem B2533949 : Blo 413771 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B2108105 : Blo 413771 2108105 := bstep (se 2 (by rfl) ⟨790539, by rfl⟩ : syracuseStep 2108105 = 1581079) B1581079
theorem B699151 : Blo 413771 699151 := bstep (se 1 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 699151 = 1048727) B1048727
theorem B4500299 : Blo 413771 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B469903 : Blo 413771 469903 := bstep (se 1 (by rfl) ⟨352427, by rfl⟩ : syracuseStep 469903 = 704855) B704855
theorem B4729751 : Blo 413771 4729751 := bstep (se 1 (by rfl) ⟨3547313, by rfl⟩ : syracuseStep 4729751 = 7094627) B7094627
theorem B2272259 : Blo 413771 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B1780937 : Blo 413771 1780937 := bstep (se 2 (by rfl) ⟨667851, by rfl⟩ : syracuseStep 1780937 = 1335703) B1335703
theorem B699691 : Blo 413771 699691 := bstep (se 1 (by rfl) ⟨524768, by rfl⟩ : syracuseStep 699691 = 1049537) B1049537
theorem B634169 : Blo 413771 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B994675 : Blo 413771 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B699833 : Blo 413771 699833 := bstep (se 2 (by rfl) ⟨262437, by rfl⟩ : syracuseStep 699833 = 524875) B524875
theorem B2371301 : Blo 413771 2371301 := bstep (se 4 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 2371301 = 444619) B444619
theorem B2993969 : Blo 413771 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B667577 : Blo 413771 667577 := bstep (se 2 (by rfl) ⟨250341, by rfl⟩ : syracuseStep 667577 = 500683) B500683
theorem B3158027 : Blo 413771 3158027 := bstep (se 1 (by rfl) ⟨2368520, by rfl⟩ : syracuseStep 3158027 = 4737041) B4737041
theorem B569359 : Blo 413771 569359 := bstep (se 1 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 569359 = 854039) B854039
theorem B700535 : Blo 413771 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B1585271 : Blo 413771 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B995627 : Blo 413771 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B8565209 : Blo 413771 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B700987 : Blo 413771 700987 := bstep (se 1 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 700987 = 1051481) B1051481
theorem B2241197 : Blo 413771 2241197 := bstep (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) B840449
theorem B701129 : Blo 413771 701129 := bstep (se 2 (by rfl) ⟨262923, by rfl⟩ : syracuseStep 701129 = 525847) B525847
theorem B668807 : Blo 413771 668807 := bstep (se 1 (by rfl) ⟨501605, by rfl⟩ : syracuseStep 668807 = 1003211) B1003211
theorem B1783073 : Blo 413771 1783073 := bstep (se 2 (by rfl) ⟨668652, by rfl⟩ : syracuseStep 1783073 = 1337305) B1337305
theorem B701831 : Blo 413771 701831 := bstep (se 1 (by rfl) ⟨526373, by rfl⟩ : syracuseStep 701831 = 1052747) B1052747
theorem B1783225 : Blo 413771 1783225 := bstep (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) B1337419
theorem B4306385 : Blo 413771 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B931463 : Blo 413771 931463 := bstep (se 1 (by rfl) ⟨698597, by rfl⟩ : syracuseStep 931463 = 1397195) B1397195
theorem B3979043 : Blo 413771 3979043 := bstep (se 1 (by rfl) ⟨2984282, by rfl⟩ : syracuseStep 3979043 = 5968565) B5968565
theorem B931643 : Blo 413771 931643 := bstep (se 1 (by rfl) ⟨698732, by rfl⟩ : syracuseStep 931643 = 1397465) B1397465
theorem B3159971 : Blo 413771 3159971 := bstep (se 1 (by rfl) ⟨2369978, by rfl⟩ : syracuseStep 3159971 = 4739957) B4739957
theorem B931769 : Blo 413771 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B702479 : Blo 413771 702479 := bstep (se 1 (by rfl) ⟨526859, by rfl⟩ : syracuseStep 702479 = 1053719) B1053719
theorem B571451 : Blo 413771 571451 := bstep (se 1 (by rfl) ⟨428588, by rfl⟩ : syracuseStep 571451 = 857177) B857177
theorem B1784045 : Blo 413771 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B932111 : Blo 413771 932111 := bstep (se 1 (by rfl) ⟨699083, by rfl⟩ : syracuseStep 932111 = 1398167) B1398167
theorem B932129 : Blo 413771 932129 := bstep (se 2 (by rfl) ⟨349548, by rfl⟩ : syracuseStep 932129 = 699097) B699097
theorem B997751 : Blo 413771 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B3193235 : Blo 413771 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B703019 : Blo 413771 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B932471 : Blo 413771 932471 := bstep (se 1 (by rfl) ⟨699353, by rfl⟩ : syracuseStep 932471 = 1398707) B1398707
theorem B932651 : Blo 413771 932651 := bstep (se 1 (by rfl) ⟨699488, by rfl⟩ : syracuseStep 932651 = 1398977) B1398977
theorem B2374535 : Blo 413771 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B703417 : Blo 413771 703417 := bstep (se 2 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 703417 = 527563) B527563
theorem B1031183 : Blo 413771 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B2374717 : Blo 413771 2374717 := bstep (se 3 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 2374717 = 890519) B890519
theorem B933011 : Blo 413771 933011 := bstep (se 1 (by rfl) ⟨699758, by rfl⟩ : syracuseStep 933011 = 1399517) B1399517
theorem B1064083 : Blo 413771 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B4734125 : Blo 413771 4734125 := bstep (se 3 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 4734125 = 1775297) B1775297
theorem B933065 : Blo 413771 933065 := bstep (se 2 (by rfl) ⟨349899, by rfl⟩ : syracuseStep 933065 = 699799) B699799
theorem B8535581 : Blo 413771 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B704119 : Blo 413771 704119 := bstep (se 1 (by rfl) ⟨528089, by rfl⟩ : syracuseStep 704119 = 1056179) B1056179
theorem B638777 : Blo 413771 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B704315 : Blo 413771 704315 := bstep (se 1 (by rfl) ⟨528236, by rfl⟩ : syracuseStep 704315 = 1056473) B1056473
theorem B933767 : Blo 413771 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B933947 : Blo 413771 933947 := bstep (se 1 (by rfl) ⟨700460, by rfl⟩ : syracuseStep 933947 = 1400921) B1400921
theorem B934073 : Blo 413771 934073 := bstep (se 2 (by rfl) ⟨350277, by rfl⟩ : syracuseStep 934073 = 700555) B700555
theorem B704713 : Blo 413771 704713 := bstep (se 2 (by rfl) ⟨264267, by rfl⟩ : syracuseStep 704713 = 528535) B528535
theorem B3162401 : Blo 413771 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B1327475 : Blo 413771 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B475535 : Blo 413771 475535 := bstep (se 1 (by rfl) ⟨356651, by rfl⟩ : syracuseStep 475535 = 713303) B713303
theorem B2113937 : Blo 413771 2113937 := bstep (se 2 (by rfl) ⟨792726, by rfl⟩ : syracuseStep 2113937 = 1585453) B1585453
theorem B2670995 : Blo 413771 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B639419 : Blo 413771 639419 := bstep (se 1 (by rfl) ⟨479564, by rfl⟩ : syracuseStep 639419 = 959129) B959129
theorem B934415 : Blo 413771 934415 := bstep (se 1 (by rfl) ⟨700811, by rfl⟩ : syracuseStep 934415 = 1401623) B1401623
theorem B934433 : Blo 413771 934433 := bstep (se 2 (by rfl) ⟨350412, by rfl⟩ : syracuseStep 934433 = 700825) B700825
theorem B2671147 : Blo 413771 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B2376449 : Blo 413771 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B3982117 : Blo 413771 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B934775 : Blo 413771 934775 := bstep (se 1 (by rfl) ⟨701081, by rfl⟩ : syracuseStep 934775 = 1402163) B1402163
theorem B934955 : Blo 413771 934955 := bstep (se 1 (by rfl) ⟨701216, by rfl⟩ : syracuseStep 934955 = 1402433) B1402433
theorem B3163373 : Blo 413771 3163373 := bstep (se 3 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 3163373 = 1186265) B1186265
theorem B935315 : Blo 413771 935315 := bstep (se 1 (by rfl) ⟨701486, by rfl⟩ : syracuseStep 935315 = 1402973) B1402973
theorem B935369 : Blo 413771 935369 := bstep (se 2 (by rfl) ⟨350763, by rfl⟩ : syracuseStep 935369 = 701527) B701527
theorem B6407909 : Blo 413771 6407909 := bstep (se 4 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 6407909 = 1201483) B1201483
theorem B4572929 : Blo 413771 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B1001335 : Blo 413771 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B936071 : Blo 413771 936071 := bstep (se 1 (by rfl) ⟨702053, by rfl⟩ : syracuseStep 936071 = 1404107) B1404107
theorem B936251 : Blo 413771 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B936377 : Blo 413771 936377 := bstep (se 2 (by rfl) ⟨351141, by rfl⟩ : syracuseStep 936377 = 702283) B702283
theorem B936719 : Blo 413771 936719 := bstep (se 1 (by rfl) ⟨702539, by rfl⟩ : syracuseStep 936719 = 1405079) B1405079
theorem B936737 : Blo 413771 936737 := bstep (se 2 (by rfl) ⟨351276, by rfl⟩ : syracuseStep 936737 = 702553) B702553
theorem B1428509 : Blo 413771 1428509 := bstep (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) B535691
theorem B937079 : Blo 413771 937079 := bstep (se 1 (by rfl) ⟨702809, by rfl⟩ : syracuseStep 937079 = 1405619) B1405619
theorem B8244355 : Blo 413771 8244355 := bstep (se 1 (by rfl) ⟨6183266, by rfl⟩ : syracuseStep 8244355 = 12366533) B12366533
theorem B3165317 : Blo 413771 3165317 := bstep (se 4 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 3165317 = 593497) B593497
theorem B1494217 : Blo 413771 1494217 := bstep (se 2 (by rfl) ⟨560331, by rfl⟩ : syracuseStep 1494217 = 1120663) B1120663
theorem B1199393 : Blo 413771 1199393 := bstep (se 2 (by rfl) ⟨449772, by rfl⟩ : syracuseStep 1199393 = 899545) B899545
theorem B937259 : Blo 413771 937259 := bstep (se 1 (by rfl) ⟨702944, by rfl⟩ : syracuseStep 937259 = 1405889) B1405889
theorem B937619 : Blo 413771 937619 := bstep (se 1 (by rfl) ⟨703214, by rfl⟩ : syracuseStep 937619 = 1406429) B1406429
theorem B937673 : Blo 413771 937673 := bstep (se 2 (by rfl) ⟨351627, by rfl⟩ : syracuseStep 937673 = 703255) B703255
theorem B413831 : Blo 413771 413831 := bstep (se 1 (by rfl) ⟨310373, by rfl⟩ : syracuseStep 413831 = 620747) B620747
theorem B413839 : Blo 413771 413839 := bstep (se 1 (by rfl) ⟨310379, by rfl⟩ : syracuseStep 413839 = 620759) B620759
theorem B413883 : Blo 413771 413883 := bstep (se 1 (by rfl) ⟨310412, by rfl⟩ : syracuseStep 413883 = 620825) B620825
theorem B413959 : Blo 413771 413959 := bstep (se 1 (by rfl) ⟨310469, by rfl⟩ : syracuseStep 413959 = 620939) B620939
theorem B413967 : Blo 413771 413967 := bstep (se 1 (by rfl) ⟨310475, by rfl⟩ : syracuseStep 413967 = 620951) B620951
theorem B414011 : Blo 413771 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B414087 : Blo 413771 414087 := bstep (se 1 (by rfl) ⟨310565, by rfl⟩ : syracuseStep 414087 = 621131) B621131
theorem B938375 : Blo 413771 938375 := bstep (se 1 (by rfl) ⟨703781, by rfl⟩ : syracuseStep 938375 = 1407563) B1407563
theorem B414095 : Blo 413771 414095 := bstep (se 1 (by rfl) ⟨310571, by rfl⟩ : syracuseStep 414095 = 621143) B621143
theorem B1331603 : Blo 413771 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B3363257 : Blo 413771 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B414139 : Blo 413771 414139 := bstep (se 1 (by rfl) ⟨310604, by rfl⟩ : syracuseStep 414139 = 621209) B621209
theorem B3559889 : Blo 413771 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B414215 : Blo 413771 414215 := bstep (se 1 (by rfl) ⟨310661, by rfl⟩ : syracuseStep 414215 = 621323) B621323
theorem B414223 : Blo 413771 414223 := bstep (se 1 (by rfl) ⟨310667, by rfl⟩ : syracuseStep 414223 = 621335) B621335
theorem B414267 : Blo 413771 414267 := bstep (se 1 (by rfl) ⟨310700, by rfl⟩ : syracuseStep 414267 = 621401) B621401
theorem B938555 : Blo 413771 938555 := bstep (se 1 (by rfl) ⟨703916, by rfl⟩ : syracuseStep 938555 = 1407833) B1407833
theorem B414343 : Blo 413771 414343 := bstep (se 1 (by rfl) ⟨310757, by rfl⟩ : syracuseStep 414343 = 621515) B621515
theorem B414351 : Blo 413771 414351 := bstep (se 1 (by rfl) ⟨310763, by rfl⟩ : syracuseStep 414351 = 621527) B621527
theorem B938681 : Blo 413771 938681 := bstep (se 2 (by rfl) ⟨352005, by rfl⟩ : syracuseStep 938681 = 704011) B704011
theorem B414395 : Blo 413771 414395 := bstep (se 1 (by rfl) ⟨310796, by rfl⟩ : syracuseStep 414395 = 621593) B621593
theorem B414471 : Blo 413771 414471 := bstep (se 1 (by rfl) ⟨310853, by rfl⟩ : syracuseStep 414471 = 621707) B621707
theorem B1397519 : Blo 413771 1397519 := bstep (se 1 (by rfl) ⟨1048139, by rfl⟩ : syracuseStep 1397519 = 2096279) B2096279
theorem B414479 : Blo 413771 414479 := bstep (se 1 (by rfl) ⟨310859, by rfl⟩ : syracuseStep 414479 = 621719) B621719
theorem B4051727 : Blo 413771 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B414523 : Blo 413771 414523 := bstep (se 1 (by rfl) ⟨310892, by rfl⟩ : syracuseStep 414523 = 621785) B621785
theorem B414599 : Blo 413771 414599 := bstep (se 1 (by rfl) ⟨310949, by rfl⟩ : syracuseStep 414599 = 621899) B621899
theorem B414607 : Blo 413771 414607 := bstep (se 1 (by rfl) ⟨310955, by rfl⟩ : syracuseStep 414607 = 621911) B621911
theorem B414651 : Blo 413771 414651 := bstep (se 1 (by rfl) ⟨310988, by rfl⟩ : syracuseStep 414651 = 621977) B621977
theorem B414727 : Blo 413771 414727 := bstep (se 1 (by rfl) ⟨311045, by rfl⟩ : syracuseStep 414727 = 622091) B622091
theorem B414735 : Blo 413771 414735 := bstep (se 1 (by rfl) ⟨311051, by rfl⟩ : syracuseStep 414735 = 622103) B622103
theorem B939023 : Blo 413771 939023 := bstep (se 1 (by rfl) ⟨704267, by rfl⟩ : syracuseStep 939023 = 1408535) B1408535
theorem B1397789 : Blo 413771 1397789 := bstep (se 3 (by rfl) ⟨262085, by rfl⟩ : syracuseStep 1397789 = 524171) B524171
theorem B939041 : Blo 413771 939041 := bstep (se 2 (by rfl) ⟨352140, by rfl⟩ : syracuseStep 939041 = 704281) B704281
theorem B414779 : Blo 413771 414779 := bstep (se 1 (by rfl) ⟨311084, by rfl⟩ : syracuseStep 414779 = 622169) B622169
theorem B414855 : Blo 413771 414855 := bstep (se 1 (by rfl) ⟨311141, by rfl⟩ : syracuseStep 414855 = 622283) B622283
theorem B414863 : Blo 413771 414863 := bstep (se 1 (by rfl) ⟨311147, by rfl⟩ : syracuseStep 414863 = 622295) B622295
theorem B414907 : Blo 413771 414907 := bstep (se 1 (by rfl) ⟨311180, by rfl⟩ : syracuseStep 414907 = 622361) B622361
theorem B414983 : Blo 413771 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B414991 : Blo 413771 414991 := bstep (se 1 (by rfl) ⟨311243, by rfl⟩ : syracuseStep 414991 = 622487) B622487
theorem B1496353 : Blo 413771 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B415035 : Blo 413771 415035 := bstep (se 1 (by rfl) ⟨311276, by rfl⟩ : syracuseStep 415035 = 622553) B622553
theorem B939383 : Blo 413771 939383 := bstep (se 1 (by rfl) ⟨704537, by rfl⟩ : syracuseStep 939383 = 1409075) B1409075
theorem B415111 : Blo 413771 415111 := bstep (se 1 (by rfl) ⟨311333, by rfl⟩ : syracuseStep 415111 = 622667) B622667
theorem B415119 : Blo 413771 415119 := bstep (se 1 (by rfl) ⟨311339, by rfl⟩ : syracuseStep 415119 = 622679) B622679
theorem B415163 : Blo 413771 415163 := bstep (se 1 (by rfl) ⟨311372, by rfl⟩ : syracuseStep 415163 = 622745) B622745
theorem B3167747 : Blo 413771 3167747 := bstep (se 1 (by rfl) ⟨2375810, by rfl⟩ : syracuseStep 3167747 = 4751621) B4751621
theorem B415239 : Blo 413771 415239 := bstep (se 1 (by rfl) ⟨311429, by rfl⟩ : syracuseStep 415239 = 622859) B622859
theorem B415247 : Blo 413771 415247 := bstep (se 1 (by rfl) ⟨311435, by rfl⟩ : syracuseStep 415247 = 622871) B622871
theorem B939563 : Blo 413771 939563 := bstep (se 1 (by rfl) ⟨704672, by rfl⟩ : syracuseStep 939563 = 1409345) B1409345
theorem B415291 : Blo 413771 415291 := bstep (se 1 (by rfl) ⟨311468, by rfl⟩ : syracuseStep 415291 = 622937) B622937
theorem B415367 : Blo 413771 415367 := bstep (se 1 (by rfl) ⟨311525, by rfl⟩ : syracuseStep 415367 = 623051) B623051
theorem B415375 : Blo 413771 415375 := bstep (se 1 (by rfl) ⟨311531, by rfl⟩ : syracuseStep 415375 = 623063) B623063
theorem B5330609 : Blo 413771 5330609 := bstep (se 2 (by rfl) ⟨1998978, by rfl⟩ : syracuseStep 5330609 = 3997957) B3997957
theorem B415419 : Blo 413771 415419 := bstep (se 1 (by rfl) ⟨311564, by rfl⟩ : syracuseStep 415419 = 623129) B623129
theorem B48420557 : Blo 413771 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B415495 : Blo 413771 415495 := bstep (se 1 (by rfl) ⟨311621, by rfl⟩ : syracuseStep 415495 = 623243) B623243
theorem B841487 : Blo 413771 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B415503 : Blo 413771 415503 := bstep (se 1 (by rfl) ⟨311627, by rfl⟩ : syracuseStep 415503 = 623255) B623255
theorem B415547 : Blo 413771 415547 := bstep (se 1 (by rfl) ⟨311660, by rfl⟩ : syracuseStep 415547 = 623321) B623321
theorem B415623 : Blo 413771 415623 := bstep (se 1 (by rfl) ⟨311717, by rfl⟩ : syracuseStep 415623 = 623435) B623435
theorem B415631 : Blo 413771 415631 := bstep (se 1 (by rfl) ⟨311723, by rfl⟩ : syracuseStep 415631 = 623447) B623447
theorem B2021267 : Blo 413771 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B939923 : Blo 413771 939923 := bstep (se 1 (by rfl) ⟨704942, by rfl⟩ : syracuseStep 939923 = 1409885) B1409885
theorem B415675 : Blo 413771 415675 := bstep (se 1 (by rfl) ⟨311756, by rfl⟩ : syracuseStep 415675 = 623513) B623513
theorem B939977 : Blo 413771 939977 := bstep (se 2 (by rfl) ⟨352491, by rfl⟩ : syracuseStep 939977 = 704983) B704983
theorem B415751 : Blo 413771 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B415759 : Blo 413771 415759 := bstep (se 1 (by rfl) ⟨311819, by rfl⟩ : syracuseStep 415759 = 623639) B623639
theorem B87447605 : Blo 413771 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B415803 : Blo 413771 415803 := bstep (se 1 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 415803 = 623705) B623705
theorem B415879 : Blo 413771 415879 := bstep (se 1 (by rfl) ⟨311909, by rfl⟩ : syracuseStep 415879 = 623819) B623819
theorem B415887 : Blo 413771 415887 := bstep (se 1 (by rfl) ⟨311915, by rfl⟩ : syracuseStep 415887 = 623831) B623831
theorem B415931 : Blo 413771 415931 := bstep (se 1 (by rfl) ⟨311948, by rfl⟩ : syracuseStep 415931 = 623897) B623897
theorem B416007 : Blo 413771 416007 := bstep (se 1 (by rfl) ⟨312005, by rfl⟩ : syracuseStep 416007 = 624011) B624011
theorem B416015 : Blo 413771 416015 := bstep (se 1 (by rfl) ⟨312011, by rfl⟩ : syracuseStep 416015 = 624023) B624023
theorem B416059 : Blo 413771 416059 := bstep (se 1 (by rfl) ⟨312044, by rfl⟩ : syracuseStep 416059 = 624089) B624089
theorem B842119 : Blo 413771 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B416135 : Blo 413771 416135 := bstep (se 1 (by rfl) ⟨312101, by rfl⟩ : syracuseStep 416135 = 624203) B624203
theorem B416143 : Blo 413771 416143 := bstep (se 1 (by rfl) ⟨312107, by rfl⟩ : syracuseStep 416143 = 624215) B624215
theorem B1399193 : Blo 413771 1399193 := bstep (se 2 (by rfl) ⟨524697, by rfl⟩ : syracuseStep 1399193 = 1049395) B1049395
theorem B416187 : Blo 413771 416187 := bstep (se 1 (by rfl) ⟨312140, by rfl⟩ : syracuseStep 416187 = 624281) B624281
theorem B416263 : Blo 413771 416263 := bstep (se 1 (by rfl) ⟨312197, by rfl⟩ : syracuseStep 416263 = 624395) B624395
theorem B416271 : Blo 413771 416271 := bstep (se 1 (by rfl) ⟨312203, by rfl⟩ : syracuseStep 416271 = 624407) B624407
theorem B416315 : Blo 413771 416315 := bstep (se 1 (by rfl) ⟨312236, by rfl⟩ : syracuseStep 416315 = 624473) B624473
theorem B416391 : Blo 413771 416391 := bstep (se 1 (by rfl) ⟨312293, by rfl⟩ : syracuseStep 416391 = 624587) B624587
theorem B416399 : Blo 413771 416399 := bstep (se 1 (by rfl) ⟨312299, by rfl⟩ : syracuseStep 416399 = 624599) B624599
theorem B416443 : Blo 413771 416443 := bstep (se 1 (by rfl) ⟨312332, by rfl⟩ : syracuseStep 416443 = 624665) B624665
theorem B416519 : Blo 413771 416519 := bstep (se 1 (by rfl) ⟨312389, by rfl⟩ : syracuseStep 416519 = 624779) B624779
theorem B416527 : Blo 413771 416527 := bstep (se 1 (by rfl) ⟨312395, by rfl⟩ : syracuseStep 416527 = 624791) B624791
theorem B416571 : Blo 413771 416571 := bstep (se 1 (by rfl) ⟨312428, by rfl⟩ : syracuseStep 416571 = 624857) B624857
theorem B416647 : Blo 413771 416647 := bstep (se 1 (by rfl) ⟨312485, by rfl⟩ : syracuseStep 416647 = 624971) B624971
theorem B416655 : Blo 413771 416655 := bstep (se 1 (by rfl) ⟨312491, by rfl⟩ : syracuseStep 416655 = 624983) B624983
theorem B2251705 : Blo 413771 2251705 := bstep (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) B1688779
theorem B416699 : Blo 413771 416699 := bstep (se 1 (by rfl) ⟨312524, by rfl⟩ : syracuseStep 416699 = 625049) B625049
theorem B416775 : Blo 413771 416775 := bstep (se 1 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 416775 = 625163) B625163
theorem B416783 : Blo 413771 416783 := bstep (se 1 (by rfl) ⟨312587, by rfl⟩ : syracuseStep 416783 = 625175) B625175
theorem B416827 : Blo 413771 416827 := bstep (se 1 (by rfl) ⟨312620, by rfl⟩ : syracuseStep 416827 = 625241) B625241
theorem B3988541 : Blo 413771 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B1334333 : Blo 413771 1334333 := bstep (se 3 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 1334333 = 500375) B500375
theorem B1399895 : Blo 413771 1399895 := bstep (se 1 (by rfl) ⟨1049921, by rfl⟩ : syracuseStep 1399895 = 2099843) B2099843
theorem B416903 : Blo 413771 416903 := bstep (se 1 (by rfl) ⟨312677, by rfl⟩ : syracuseStep 416903 = 625355) B625355
theorem B416911 : Blo 413771 416911 := bstep (se 1 (by rfl) ⟨312683, by rfl⟩ : syracuseStep 416911 = 625367) B625367
theorem B842899 : Blo 413771 842899 := bstep (se 1 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 842899 = 1264349) B1264349
theorem B416955 : Blo 413771 416955 := bstep (se 1 (by rfl) ⟨312716, by rfl⟩ : syracuseStep 416955 = 625433) B625433
theorem B417031 : Blo 413771 417031 := bstep (se 1 (by rfl) ⟨312773, by rfl⟩ : syracuseStep 417031 = 625547) B625547
theorem B417039 : Blo 413771 417039 := bstep (se 1 (by rfl) ⟨312779, by rfl⟩ : syracuseStep 417039 = 625559) B625559
theorem B417083 : Blo 413771 417083 := bstep (se 1 (by rfl) ⟨312812, by rfl⟩ : syracuseStep 417083 = 625625) B625625
theorem B417159 : Blo 413771 417159 := bstep (se 1 (by rfl) ⟨312869, by rfl⟩ : syracuseStep 417159 = 625739) B625739
theorem B417167 : Blo 413771 417167 := bstep (se 1 (by rfl) ⟨312875, by rfl⟩ : syracuseStep 417167 = 625751) B625751
theorem B417211 : Blo 413771 417211 := bstep (se 1 (by rfl) ⟨312908, by rfl⟩ : syracuseStep 417211 = 625817) B625817
theorem B11427281 : Blo 413771 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B417287 : Blo 413771 417287 := bstep (se 1 (by rfl) ⟨312965, by rfl⟩ : syracuseStep 417287 = 625931) B625931
theorem B417295 : Blo 413771 417295 := bstep (se 1 (by rfl) ⟨312971, by rfl⟩ : syracuseStep 417295 = 625943) B625943
theorem B417339 : Blo 413771 417339 := bstep (se 1 (by rfl) ⟨313004, by rfl⟩ : syracuseStep 417339 = 626009) B626009
theorem B1400381 : Blo 413771 1400381 := bstep (se 3 (by rfl) ⟨262571, by rfl⟩ : syracuseStep 1400381 = 525143) B525143
theorem B417415 : Blo 413771 417415 := bstep (se 1 (by rfl) ⟨313061, by rfl⟩ : syracuseStep 417415 = 626123) B626123
theorem B417423 : Blo 413771 417423 := bstep (se 1 (by rfl) ⟨313067, by rfl⟩ : syracuseStep 417423 = 626135) B626135
theorem B417467 : Blo 413771 417467 := bstep (se 1 (by rfl) ⟨313100, by rfl⟩ : syracuseStep 417467 = 626201) B626201
theorem B4742873 : Blo 413771 4742873 := bstep (se 2 (by rfl) ⟨1778577, by rfl⟩ : syracuseStep 4742873 = 3557155) B3557155
theorem B417543 : Blo 413771 417543 := bstep (se 1 (by rfl) ⟨313157, by rfl⟩ : syracuseStep 417543 = 626315) B626315
theorem B417551 : Blo 413771 417551 := bstep (se 1 (by rfl) ⟨313163, by rfl⟩ : syracuseStep 417551 = 626327) B626327
theorem B417595 : Blo 413771 417595 := bstep (se 1 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 417595 = 626393) B626393
theorem B417671 : Blo 413771 417671 := bstep (se 1 (by rfl) ⟨313253, by rfl⟩ : syracuseStep 417671 = 626507) B626507
theorem B417679 : Blo 413771 417679 := bstep (se 1 (by rfl) ⟨313259, by rfl⟩ : syracuseStep 417679 = 626519) B626519
theorem B417723 : Blo 413771 417723 := bstep (se 1 (by rfl) ⟨313292, by rfl⟩ : syracuseStep 417723 = 626585) B626585
theorem B3793337 : Blo 413771 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B7955009 : Blo 413771 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B1401785 : Blo 413771 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B4482053 : Blo 413771 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B615481 : Blo 413771 615481 := bstep (se 2 (by rfl) ⟨230805, by rfl⟩ : syracuseStep 615481 = 461611) B461611
theorem B1402379 : Blo 413771 1402379 := bstep (se 1 (by rfl) ⟨1051784, by rfl⟩ : syracuseStep 1402379 = 2103569) B2103569
theorem B1402487 : Blo 413771 1402487 := bstep (se 1 (by rfl) ⟨1051865, by rfl⟩ : syracuseStep 1402487 = 2103731) B2103731
theorem B1894259 : Blo 413771 1894259 := bstep (se 1 (by rfl) ⟨1420694, by rfl⟩ : syracuseStep 1894259 = 2841389) B2841389
theorem B5040215 : Blo 413771 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B10152053 : Blo 413771 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B6514805 : Blo 413771 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B1403081 : Blo 413771 1403081 := bstep (se 2 (by rfl) ⟨526155, by rfl⟩ : syracuseStep 1403081 = 1052311) B1052311
theorem B1403783 : Blo 413771 1403783 := bstep (se 1 (by rfl) ⟨1052837, by rfl⟩ : syracuseStep 1403783 = 2105675) B2105675
theorem B3599597 : Blo 413771 3599597 := bstep (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) B1349849
theorem B1895681 : Blo 413771 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B1404161 : Blo 413771 1404161 := bstep (se 2 (by rfl) ⟨526560, by rfl⟩ : syracuseStep 1404161 = 1053121) B1053121
theorem B15200045 : Blo 413771 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B1404971 : Blo 413771 1404971 := bstep (se 1 (by rfl) ⟨1053728, by rfl⟩ : syracuseStep 1404971 = 2107457) B2107457
theorem B5304365 : Blo 413771 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B2519333 : Blo 413771 2519333 := bstep (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) B472375
theorem B1896851 : Blo 413771 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B1077895 : Blo 413771 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B946873 : Blo 413771 946873 := bstep (se 2 (by rfl) ⟨355077, by rfl⟩ : syracuseStep 946873 = 710155) B710155
theorem B1406267 : Blo 413771 1406267 := bstep (se 1 (by rfl) ⟨1054700, by rfl⟩ : syracuseStep 1406267 = 2109401) B2109401
theorem B1602931 : Blo 413771 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B947603 : Blo 413771 947603 := bstep (se 1 (by rfl) ⟨710702, by rfl⟩ : syracuseStep 947603 = 1421405) B1421405
theorem B1996481 : Blo 413771 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B1406753 : Blo 413771 1406753 := bstep (se 2 (by rfl) ⟨527532, by rfl⟩ : syracuseStep 1406753 = 1055065) B1055065
theorem B2094983 : Blo 413771 2094983 := bstep (se 1 (by rfl) ⟨1571237, by rfl⟩ : syracuseStep 2094983 = 3142475) B3142475
theorem B1767491 : Blo 413771 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B620663 : Blo 413771 620663 := bstep (se 1 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 620663 = 930995) B930995
theorem B620687 : Blo 413771 620687 := bstep (se 1 (by rfl) ⟨465515, by rfl⟩ : syracuseStep 620687 = 931031) B931031
theorem B620729 : Blo 413771 620729 := bstep (se 2 (by rfl) ⟨232773, by rfl⟩ : syracuseStep 620729 = 465547) B465547
theorem B620807 : Blo 413771 620807 := bstep (se 1 (by rfl) ⟨465605, by rfl⟩ : syracuseStep 620807 = 931211) B931211
theorem B620843 : Blo 413771 620843 := bstep (se 1 (by rfl) ⟨465632, by rfl⟩ : syracuseStep 620843 = 931265) B931265
theorem B620873 : Blo 413771 620873 := bstep (se 2 (by rfl) ⟨232827, by rfl⟩ : syracuseStep 620873 = 465655) B465655
theorem B1407347 : Blo 413771 1407347 := bstep (se 1 (by rfl) ⟨1055510, by rfl⟩ : syracuseStep 1407347 = 2111021) B2111021
theorem B1767815 : Blo 413771 1767815 := bstep (se 1 (by rfl) ⟨1325861, by rfl⟩ : syracuseStep 1767815 = 2651723) B2651723
theorem B620987 : Blo 413771 620987 := bstep (se 1 (by rfl) ⟨465740, by rfl⟩ : syracuseStep 620987 = 931481) B931481
theorem B621047 : Blo 413771 621047 := bstep (se 1 (by rfl) ⟨465785, by rfl⟩ : syracuseStep 621047 = 931571) B931571
theorem B621071 : Blo 413771 621071 := bstep (se 1 (by rfl) ⟨465803, by rfl⟩ : syracuseStep 621071 = 931607) B931607
theorem B621113 : Blo 413771 621113 := bstep (se 2 (by rfl) ⟨232917, by rfl⟩ : syracuseStep 621113 = 465835) B465835
theorem B621191 : Blo 413771 621191 := bstep (se 1 (by rfl) ⟨465893, by rfl⟩ : syracuseStep 621191 = 931787) B931787
theorem B621227 : Blo 413771 621227 := bstep (se 1 (by rfl) ⟨465920, by rfl⟩ : syracuseStep 621227 = 931841) B931841
theorem B621257 : Blo 413771 621257 := bstep (se 2 (by rfl) ⟨232971, by rfl⟩ : syracuseStep 621257 = 465943) B465943
theorem B1178383 : Blo 413771 1178383 := bstep (se 1 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 1178383 = 1767575) B1767575
theorem B6716195 : Blo 413771 6716195 := bstep (se 1 (by rfl) ⟨5037146, by rfl⟩ : syracuseStep 6716195 = 10074293) B10074293
theorem B621371 : Blo 413771 621371 := bstep (se 1 (by rfl) ⟨466028, by rfl⟩ : syracuseStep 621371 = 932057) B932057
theorem B621431 : Blo 413771 621431 := bstep (se 1 (by rfl) ⟨466073, by rfl⟩ : syracuseStep 621431 = 932147) B932147
theorem B1047431 : Blo 413771 1047431 := bstep (se 1 (by rfl) ⟨785573, by rfl⟩ : syracuseStep 1047431 = 1571147) B1571147
theorem B621455 : Blo 413771 621455 := bstep (se 1 (by rfl) ⟨466091, by rfl⟩ : syracuseStep 621455 = 932183) B932183
theorem B621497 : Blo 413771 621497 := bstep (se 2 (by rfl) ⟨233061, by rfl⟩ : syracuseStep 621497 = 466123) B466123
theorem B1801169 : Blo 413771 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B621575 : Blo 413771 621575 := bstep (se 1 (by rfl) ⟨466181, by rfl⟩ : syracuseStep 621575 = 932363) B932363
theorem B1047563 : Blo 413771 1047563 := bstep (se 1 (by rfl) ⟨785672, by rfl⟩ : syracuseStep 1047563 = 1571345) B1571345
theorem B1178657 : Blo 413771 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B621611 : Blo 413771 621611 := bstep (se 1 (by rfl) ⟨466208, by rfl⟩ : syracuseStep 621611 = 932417) B932417
theorem B621641 : Blo 413771 621641 := bstep (se 2 (by rfl) ⟨233115, by rfl⟩ : syracuseStep 621641 = 466231) B466231
theorem B621755 : Blo 413771 621755 := bstep (se 1 (by rfl) ⟨466316, by rfl⟩ : syracuseStep 621755 = 932633) B932633
theorem B3144905 : Blo 413771 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B621815 : Blo 413771 621815 := bstep (se 1 (by rfl) ⟨466361, by rfl⟩ : syracuseStep 621815 = 932723) B932723
theorem B621839 : Blo 413771 621839 := bstep (se 1 (by rfl) ⟨466379, by rfl⟩ : syracuseStep 621839 = 932759) B932759
theorem B621881 : Blo 413771 621881 := bstep (se 2 (by rfl) ⟨233205, by rfl⟩ : syracuseStep 621881 = 466411) B466411
theorem B884027 : Blo 413771 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B1178999 : Blo 413771 1178999 := bstep (se 1 (by rfl) ⟨884249, by rfl⟩ : syracuseStep 1178999 = 1768499) B1768499
theorem B621959 : Blo 413771 621959 := bstep (se 1 (by rfl) ⟨466469, by rfl⟩ : syracuseStep 621959 = 932939) B932939
theorem B621995 : Blo 413771 621995 := bstep (se 1 (by rfl) ⟨466496, by rfl⟩ : syracuseStep 621995 = 932993) B932993
theorem B622025 : Blo 413771 622025 := bstep (se 2 (by rfl) ⟨233259, by rfl⟩ : syracuseStep 622025 = 466519) B466519
theorem B1048079 : Blo 413771 1048079 := bstep (se 1 (by rfl) ⟨786059, by rfl⟩ : syracuseStep 1048079 = 1572119) B1572119
theorem B785953 : Blo 413771 785953 := bstep (se 2 (by rfl) ⟨294732, by rfl⟩ : syracuseStep 785953 = 589465) B589465
theorem B622139 : Blo 413771 622139 := bstep (se 1 (by rfl) ⟨466604, by rfl⟩ : syracuseStep 622139 = 933209) B933209
theorem B8027747 : Blo 413771 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B622199 : Blo 413771 622199 := bstep (se 1 (by rfl) ⟨466649, by rfl⟩ : syracuseStep 622199 = 933299) B933299
theorem B622223 : Blo 413771 622223 := bstep (se 1 (by rfl) ⟨466667, by rfl⟩ : syracuseStep 622223 = 933335) B933335
theorem B1048211 : Blo 413771 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B622265 : Blo 413771 622265 := bstep (se 2 (by rfl) ⟨233349, by rfl⟩ : syracuseStep 622265 = 466699) B466699
theorem B622343 : Blo 413771 622343 := bstep (se 1 (by rfl) ⟨466757, by rfl⟩ : syracuseStep 622343 = 933515) B933515
theorem B622379 : Blo 413771 622379 := bstep (se 1 (by rfl) ⟨466784, by rfl⟩ : syracuseStep 622379 = 933569) B933569
theorem B622409 : Blo 413771 622409 := bstep (se 2 (by rfl) ⟨233403, by rfl⟩ : syracuseStep 622409 = 466807) B466807
theorem B3374963 : Blo 413771 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B9633653 : Blo 413771 9633653 := bstep (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) B903155
theorem B622523 : Blo 413771 622523 := bstep (se 1 (by rfl) ⟨466892, by rfl⟩ : syracuseStep 622523 = 933785) B933785
theorem B1572817 : Blo 413771 1572817 := bstep (se 2 (by rfl) ⟨589806, by rfl⟩ : syracuseStep 1572817 = 1179613) B1179613
theorem B622583 : Blo 413771 622583 := bstep (se 1 (by rfl) ⟨466937, by rfl⟩ : syracuseStep 622583 = 933875) B933875
theorem B786439 : Blo 413771 786439 := bstep (se 1 (by rfl) ⟨589829, by rfl⟩ : syracuseStep 786439 = 1179659) B1179659
theorem B622601 : Blo 413771 622601 := bstep (se 2 (by rfl) ⟨233475, by rfl⟩ : syracuseStep 622601 = 466951) B466951
theorem B622631 : Blo 413771 622631 := bstep (se 1 (by rfl) ⟨466973, by rfl⟩ : syracuseStep 622631 = 933947) B933947
theorem B622715 : Blo 413771 622715 := bstep (se 1 (by rfl) ⟨467036, by rfl⟩ : syracuseStep 622715 = 934073) B934073
theorem B1048747 : Blo 413771 1048747 := bstep (se 1 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 1048747 = 1573121) B1573121
theorem B622841 : Blo 413771 622841 := bstep (se 2 (by rfl) ⟨233565, by rfl⟩ : syracuseStep 622841 = 467131) B467131
theorem B1409291 : Blo 413771 1409291 := bstep (se 1 (by rfl) ⟨1056968, by rfl⟩ : syracuseStep 1409291 = 2113937) B2113937
theorem B622943 : Blo 413771 622943 := bstep (se 1 (by rfl) ⟨467207, by rfl⟩ : syracuseStep 622943 = 934415) B934415
theorem B622955 : Blo 413771 622955 := bstep (se 1 (by rfl) ⟨467216, by rfl⟩ : syracuseStep 622955 = 934433) B934433
theorem B1049051 : Blo 413771 1049051 := bstep (se 1 (by rfl) ⟨786788, by rfl⟩ : syracuseStep 1049051 = 1573577) B1573577
theorem B885257 : Blo 413771 885257 := bstep (se 2 (by rfl) ⟨331971, by rfl⟩ : syracuseStep 885257 = 663943) B663943
theorem B1409561 : Blo 413771 1409561 := bstep (se 2 (by rfl) ⟨528585, by rfl⟩ : syracuseStep 1409561 = 1057171) B1057171
theorem B932774453 : Blo 413771 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B623183 : Blo 413771 623183 := bstep (se 1 (by rfl) ⟨467387, by rfl⟩ : syracuseStep 623183 = 934775) B934775
theorem B6095477 : Blo 413771 6095477 := bstep (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) B571451
theorem B623303 : Blo 413771 623303 := bstep (se 1 (by rfl) ⟨467477, by rfl⟩ : syracuseStep 623303 = 934955) B934955
theorem B2360137 : Blo 413771 2360137 := bstep (se 2 (by rfl) ⟨885051, by rfl⟩ : syracuseStep 2360137 = 1770103) B1770103
theorem B623465 : Blo 413771 623465 := bstep (se 2 (by rfl) ⟨233799, by rfl⟩ : syracuseStep 623465 = 467599) B467599
theorem B623543 : Blo 413771 623543 := bstep (se 1 (by rfl) ⟨467657, by rfl⟩ : syracuseStep 623543 = 935315) B935315
theorem B623579 : Blo 413771 623579 := bstep (se 1 (by rfl) ⟨467684, by rfl⟩ : syracuseStep 623579 = 935369) B935369
theorem B3539933 : Blo 413771 3539933 := bstep (se 3 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 3539933 = 1327475) B1327475
theorem B787495 : Blo 413771 787495 := bstep (se 1 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 787495 = 1181243) B1181243
theorem B5309489 : Blo 413771 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B3048619 : Blo 413771 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B1181071 : Blo 413771 1181071 := bstep (se 1 (by rfl) ⟨885803, by rfl⟩ : syracuseStep 1181071 = 1771607) B1771607
theorem B624047 : Blo 413771 624047 := bstep (se 1 (by rfl) ⟨468035, by rfl⟩ : syracuseStep 624047 = 936071) B936071
theorem B5703131 : Blo 413771 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B624137 : Blo 413771 624137 := bstep (se 2 (by rfl) ⟨234051, by rfl⟩ : syracuseStep 624137 = 468103) B468103
theorem B624167 : Blo 413771 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B624251 : Blo 413771 624251 := bstep (se 1 (by rfl) ⟨468188, by rfl⟩ : syracuseStep 624251 = 936377) B936377
theorem B3212939 : Blo 413771 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B624377 : Blo 413771 624377 := bstep (se 2 (by rfl) ⟨234141, by rfl⟩ : syracuseStep 624377 = 468283) B468283
theorem B624479 : Blo 413771 624479 := bstep (se 1 (by rfl) ⟨468359, by rfl⟩ : syracuseStep 624479 = 936719) B936719
theorem B624491 : Blo 413771 624491 := bstep (se 1 (by rfl) ⟨468368, by rfl⟩ : syracuseStep 624491 = 936737) B936737
theorem B1050529 : Blo 413771 1050529 := bstep (se 2 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 1050529 = 787897) B787897
theorem B3540995 : Blo 413771 3540995 := bstep (se 1 (by rfl) ⟨2655746, by rfl⟩ : syracuseStep 3540995 = 5311493) B5311493
theorem B952339 : Blo 413771 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B4491301 : Blo 413771 4491301 := bstep (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) B842119
theorem B624719 : Blo 413771 624719 := bstep (se 1 (by rfl) ⟨468539, by rfl⟩ : syracuseStep 624719 = 937079) B937079
theorem B1575065 : Blo 413771 1575065 := bstep (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) B1181299
theorem B2099357 : Blo 413771 2099357 := bstep (se 3 (by rfl) ⟨393629, by rfl⟩ : syracuseStep 2099357 = 787259) B787259
theorem B624839 : Blo 413771 624839 := bstep (se 1 (by rfl) ⟨468629, by rfl⟩ : syracuseStep 624839 = 937259) B937259
theorem B625001 : Blo 413771 625001 := bstep (se 2 (by rfl) ⟨234375, by rfl⟩ : syracuseStep 625001 = 468751) B468751
theorem B625079 : Blo 413771 625079 := bstep (se 1 (by rfl) ⟨468809, by rfl⟩ : syracuseStep 625079 = 937619) B937619
theorem B625115 : Blo 413771 625115 := bstep (se 1 (by rfl) ⟨468836, by rfl⟩ : syracuseStep 625115 = 937673) B937673
theorem B1575521 : Blo 413771 1575521 := bstep (se 2 (by rfl) ⟨590820, by rfl⟩ : syracuseStep 1575521 = 1181641) B1181641
theorem B1182347 : Blo 413771 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B789203 : Blo 413771 789203 := bstep (se 1 (by rfl) ⟨591902, by rfl⟩ : syracuseStep 789203 = 1183805) B1183805
theorem B789355 : Blo 413771 789355 := bstep (se 1 (by rfl) ⟨592016, by rfl⟩ : syracuseStep 789355 = 1184033) B1184033
theorem B625583 : Blo 413771 625583 := bstep (se 1 (by rfl) ⟨469187, by rfl⟩ : syracuseStep 625583 = 938375) B938375
theorem B887735 : Blo 413771 887735 := bstep (se 1 (by rfl) ⟨665801, by rfl⟩ : syracuseStep 887735 = 1331603) B1331603
theorem B625673 : Blo 413771 625673 := bstep (se 2 (by rfl) ⟨234627, by rfl⟩ : syracuseStep 625673 = 469255) B469255
theorem B625703 : Blo 413771 625703 := bstep (se 1 (by rfl) ⟨469277, by rfl⟩ : syracuseStep 625703 = 938555) B938555
theorem B789583 : Blo 413771 789583 := bstep (se 1 (by rfl) ⟨592187, by rfl⟩ : syracuseStep 789583 = 1184375) B1184375
theorem B625787 : Blo 413771 625787 := bstep (se 1 (by rfl) ⟨469340, by rfl⟩ : syracuseStep 625787 = 938681) B938681
theorem B756985 : Blo 413771 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B625913 : Blo 413771 625913 := bstep (se 2 (by rfl) ⟨234717, by rfl⟩ : syracuseStep 625913 = 469435) B469435
theorem B626015 : Blo 413771 626015 := bstep (se 1 (by rfl) ⟨469511, by rfl⟩ : syracuseStep 626015 = 939023) B939023
theorem B626027 : Blo 413771 626027 := bstep (se 1 (by rfl) ⟨469520, by rfl⟩ : syracuseStep 626027 = 939041) B939041
theorem B2100653 : Blo 413771 2100653 := bstep (se 3 (by rfl) ⟨393872, by rfl⟩ : syracuseStep 2100653 = 787745) B787745
theorem B527791 : Blo 413771 527791 := bstep (se 1 (by rfl) ⟨395843, by rfl⟩ : syracuseStep 527791 = 791687) B791687
theorem B626255 : Blo 413771 626255 := bstep (se 1 (by rfl) ⟨469691, by rfl⟩ : syracuseStep 626255 = 939383) B939383
theorem B5049989 : Blo 413771 5049989 := bstep (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) B946873
theorem B626375 : Blo 413771 626375 := bstep (se 1 (by rfl) ⟨469781, by rfl⟩ : syracuseStep 626375 = 939563) B939563
theorem B32280371 : Blo 413771 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B626537 : Blo 413771 626537 := bstep (se 2 (by rfl) ⟨234951, by rfl⟩ : syracuseStep 626537 = 469903) B469903
theorem B593839 : Blo 413771 593839 := bstep (se 1 (by rfl) ⟨445379, by rfl⟩ : syracuseStep 593839 = 890759) B890759
theorem B1347511 : Blo 413771 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B626615 : Blo 413771 626615 := bstep (se 1 (by rfl) ⟨469961, by rfl⟩ : syracuseStep 626615 = 939923) B939923
theorem B626651 : Blo 413771 626651 := bstep (se 1 (by rfl) ⟨469988, by rfl⟩ : syracuseStep 626651 = 939977) B939977
theorem B1576979 : Blo 413771 1576979 := bstep (se 1 (by rfl) ⟨1182734, by rfl⟩ : syracuseStep 1576979 = 2365469) B2365469
theorem B1053071 : Blo 413771 1053071 := bstep (se 1 (by rfl) ⟨789803, by rfl⟩ : syracuseStep 1053071 = 1579607) B1579607
theorem B6820469 : Blo 413771 6820469 := bstep (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) B639419
theorem B594631 : Blo 413771 594631 := bstep (se 1 (by rfl) ⟨445973, by rfl⟩ : syracuseStep 594631 = 891947) B891947
theorem B2659027 : Blo 413771 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B1053395 : Blo 413771 1053395 := bstep (se 1 (by rfl) ⟨790046, by rfl⟩ : syracuseStep 1053395 = 1580093) B1580093
theorem B889555 : Blo 413771 889555 := bstep (se 1 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 889555 = 1334333) B1334333
theorem B3150737 : Blo 413771 3150737 := bstep (se 2 (by rfl) ⟨1181526, by rfl⟩ : syracuseStep 3150737 = 2363053) B2363053
theorem B19928065 : Blo 413771 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B2102273 : Blo 413771 2102273 := bstep (se 2 (by rfl) ⟨788352, by rfl⟩ : syracuseStep 2102273 = 1576705) B1576705
theorem B759145 : Blo 413771 759145 := bstep (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) B569359
theorem B2299355 : Blo 413771 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B2528891 : Blo 413771 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B3282565 : Blo 413771 3282565 := bstep (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) B615481
theorem B1578635 : Blo 413771 1578635 := bstep (se 1 (by rfl) ⟨1183976, by rfl⟩ : syracuseStep 1578635 = 2367953) B2367953
theorem B1185491 : Blo 413771 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B2103083 : Blo 413771 2103083 := bstep (se 1 (by rfl) ⟨1577312, by rfl⟩ : syracuseStep 2103083 = 3154625) B3154625
theorem B1054559 : Blo 413771 1054559 := bstep (se 1 (by rfl) ⟨790919, by rfl⟩ : syracuseStep 1054559 = 1581839) B1581839
theorem B4757453 : Blo 413771 4757453 := bstep (se 3 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 4757453 = 1784045) B1784045
theorem B2988035 : Blo 413771 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B1185799 : Blo 413771 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1579895 : Blo 413771 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B1186721 : Blo 413771 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B1055663 : Blo 413771 1055663 := bstep (se 1 (by rfl) ⟨791747, by rfl⟩ : syracuseStep 1055663 = 1583495) B1583495
theorem B2137241 : Blo 413771 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B3153167 : Blo 413771 3153167 := bstep (se 1 (by rfl) ⟨2364875, by rfl⟩ : syracuseStep 3153167 = 4729751) B4729751
theorem B1187291 : Blo 413771 1187291 := bstep (se 1 (by rfl) ⟨890468, by rfl⟩ : syracuseStep 1187291 = 1780937) B1780937
theorem B466555 : Blo 413771 466555 := bstep (se 1 (by rfl) ⟨349916, by rfl⟩ : syracuseStep 466555 = 699833) B699833
theorem B1580867 : Blo 413771 1580867 := bstep (se 1 (by rfl) ⟨1185650, by rfl⟩ : syracuseStep 1580867 = 2371301) B2371301
theorem B10133363 : Blo 413771 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B2105351 : Blo 413771 2105351 := bstep (se 1 (by rfl) ⟨1579013, by rfl⟩ : syracuseStep 2105351 = 3158027) B3158027
theorem B467023 : Blo 413771 467023 := bstep (se 1 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 467023 = 700535) B700535
theorem B1056847 : Blo 413771 1056847 := bstep (se 1 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 1056847 = 1585271) B1585271
theorem B1679555 : Blo 413771 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B663751 : Blo 413771 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B5710139 : Blo 413771 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B467419 : Blo 413771 467419 := bstep (se 1 (by rfl) ⟨350564, by rfl⟩ : syracuseStep 467419 = 701129) B701129
theorem B2105837 : Blo 413771 2105837 := bstep (se 3 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 2105837 = 789689) B789689
theorem B1188361 : Blo 413771 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B5055149 : Blo 413771 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B1188715 : Blo 413771 1188715 := bstep (se 1 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 1188715 = 1783073) B1783073
theorem B467887 : Blo 413771 467887 := bstep (se 1 (by rfl) ⟨350915, by rfl⟩ : syracuseStep 467887 = 701831) B701831
theorem B631735 : Blo 413771 631735 := bstep (se 1 (by rfl) ⟨473801, by rfl⟩ : syracuseStep 631735 = 947603) B947603
theorem B2106647 : Blo 413771 2106647 := bstep (se 1 (by rfl) ⟨1579985, by rfl⟩ : syracuseStep 2106647 = 3159971) B3159971
theorem B468319 : Blo 413771 468319 := bstep (se 1 (by rfl) ⟨351239, by rfl⟩ : syracuseStep 468319 = 702479) B702479
theorem B1582537 : Blo 413771 1582537 := bstep (se 2 (by rfl) ⟨593451, by rfl⟩ : syracuseStep 1582537 = 1186903) B1186903
theorem B1418777 : Blo 413771 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B1123865 : Blo 413771 1123865 := bstep (se 2 (by rfl) ⟨421449, by rfl⟩ : syracuseStep 1123865 = 842899) B842899
theorem B665167 : Blo 413771 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B468679 : Blo 413771 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B1582841 : Blo 413771 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B1583009 : Blo 413771 1583009 := bstep (se 2 (by rfl) ⟨593628, by rfl⟩ : syracuseStep 1583009 = 1187257) B1187257
theorem B698287 : Blo 413771 698287 := bstep (se 1 (by rfl) ⟨523715, by rfl⟩ : syracuseStep 698287 = 1047431) B1047431
theorem B1583023 : Blo 413771 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B698375 : Blo 413771 698375 := bstep (se 1 (by rfl) ⟨523781, by rfl⟩ : syracuseStep 698375 = 1047563) B1047563
theorem B2664485 : Blo 413771 2664485 := bstep (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) B499591
theorem B3156083 : Blo 413771 3156083 := bstep (se 1 (by rfl) ⟨2367062, by rfl⟩ : syracuseStep 3156083 = 4734125) B4734125
theorem B698719 : Blo 413771 698719 := bstep (se 1 (by rfl) ⟨524039, by rfl⟩ : syracuseStep 698719 = 1048079) B1048079
theorem B797033 : Blo 413771 797033 := bstep (se 2 (by rfl) ⟨298887, by rfl⟩ : syracuseStep 797033 = 597775) B597775
theorem B5351831 : Blo 413771 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B698807 : Blo 413771 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B469543 : Blo 413771 469543 := bstep (se 1 (by rfl) ⟨352157, by rfl⟩ : syracuseStep 469543 = 704315) B704315
theorem B2108267 : Blo 413771 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B1583981 : Blo 413771 1583981 := bstep (se 3 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 1583981 = 593993) B593993
theorem B9612215 : Blo 413771 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B1780663 : Blo 413771 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B699401 : Blo 413771 699401 := bstep (se 2 (by rfl) ⟨262275, by rfl⟩ : syracuseStep 699401 = 524551) B524551
theorem B699563 : Blo 413771 699563 := bstep (se 1 (by rfl) ⟨524672, by rfl⟩ : syracuseStep 699563 = 1049345) B1049345
theorem B1584299 : Blo 413771 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B2665817 : Blo 413771 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B2665871 : Blo 413771 2665871 := bstep (se 1 (by rfl) ⟨1999403, by rfl⟩ : syracuseStep 2665871 = 3998807) B3998807
theorem B2108915 : Blo 413771 2108915 := bstep (se 1 (by rfl) ⟨1581686, by rfl⟩ : syracuseStep 2108915 = 3163373) B3163373
theorem B699961 : Blo 413771 699961 := bstep (se 2 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 699961 = 524971) B524971
theorem B700103 : Blo 413771 700103 := bstep (se 1 (by rfl) ⟨525077, by rfl⟩ : syracuseStep 700103 = 1050155) B1050155
theorem B4271939 : Blo 413771 4271939 := bstep (se 1 (by rfl) ⟨3203954, by rfl⟩ : syracuseStep 4271939 = 6407909) B6407909
theorem B700265 : Blo 413771 700265 := bstep (se 2 (by rfl) ⟨262599, by rfl⟩ : syracuseStep 700265 = 525199) B525199
theorem B1421243 : Blo 413771 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B7090253 : Blo 413771 7090253 := bstep (se 3 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 7090253 = 2658845) B2658845
theorem B700663 : Blo 413771 700663 := bstep (se 1 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 700663 = 1050995) B1050995
theorem B700859 : Blo 413771 700859 := bstep (se 1 (by rfl) ⟨525644, by rfl⟩ : syracuseStep 700859 = 1051289) B1051289
theorem B700967 : Blo 413771 700967 := bstep (se 1 (by rfl) ⟨525725, by rfl⟩ : syracuseStep 700967 = 1051451) B1051451
theorem B3846865 : Blo 413771 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B2110211 : Blo 413771 2110211 := bstep (se 1 (by rfl) ⟨1582658, by rfl⟩ : syracuseStep 2110211 = 3165317) B3165317
theorem B701257 : Blo 413771 701257 := bstep (se 2 (by rfl) ⟨262971, by rfl⟩ : syracuseStep 701257 = 525943) B525943
theorem B799595 : Blo 413771 799595 := bstep (se 1 (by rfl) ⟨599696, by rfl⟩ : syracuseStep 799595 = 1199393) B1199393
theorem B701291 : Blo 413771 701291 := bstep (se 1 (by rfl) ⟨525968, by rfl⟩ : syracuseStep 701291 = 1051937) B1051937
theorem B701689 : Blo 413771 701689 := bstep (se 2 (by rfl) ⟨263133, by rfl⟩ : syracuseStep 701689 = 526267) B526267
theorem B6403475 : Blo 413771 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B701959 : Blo 413771 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B931337 : Blo 413771 931337 := bstep (se 2 (by rfl) ⟨349251, by rfl⟩ : syracuseStep 931337 = 698503) B698503
theorem B2242171 : Blo 413771 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B2373259 : Blo 413771 2373259 := bstep (se 1 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 2373259 = 3559889) B3559889
theorem B4503239 : Blo 413771 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B931679 : Blo 413771 931679 := bstep (se 1 (by rfl) ⟨698759, by rfl⟩ : syracuseStep 931679 = 1397519) B1397519
theorem B2701151 : Blo 413771 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B702391 : Blo 413771 702391 := bstep (se 1 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 702391 = 1053587) B1053587
theorem B931859 : Blo 413771 931859 := bstep (se 1 (by rfl) ⟨698894, by rfl⟩ : syracuseStep 931859 = 1397789) B1397789
theorem B702587 : Blo 413771 702587 := bstep (se 1 (by rfl) ⟨526940, by rfl⟩ : syracuseStep 702587 = 1053881) B1053881
theorem B2111831 : Blo 413771 2111831 := bstep (se 1 (by rfl) ⟨1583873, by rfl⟩ : syracuseStep 2111831 = 3167747) B3167747
theorem B932201 : Blo 413771 932201 := bstep (se 2 (by rfl) ⟨349575, by rfl⟩ : syracuseStep 932201 = 699151) B699151
theorem B3553739 : Blo 413771 3553739 := bstep (se 1 (by rfl) ⟨2665304, by rfl⟩ : syracuseStep 3553739 = 5330609) B5330609
theorem B702985 : Blo 413771 702985 := bstep (se 2 (by rfl) ⟨263619, by rfl⟩ : syracuseStep 702985 = 527239) B527239
theorem B703147 : Blo 413771 703147 := bstep (se 1 (by rfl) ⟨527360, by rfl⟩ : syracuseStep 703147 = 1054721) B1054721
theorem B10992473 : Blo 413771 10992473 := bstep (se 2 (by rfl) ⟨4122177, by rfl⟩ : syracuseStep 10992473 = 8244355) B8244355
theorem B932795 : Blo 413771 932795 := bstep (se 1 (by rfl) ⟨699596, by rfl⟩ : syracuseStep 932795 = 1399193) B1399193
theorem B703451 : Blo 413771 703451 := bstep (se 1 (by rfl) ⟨527588, by rfl⟩ : syracuseStep 703451 = 1055177) B1055177
theorem B6011927 : Blo 413771 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B932921 : Blo 413771 932921 := bstep (se 2 (by rfl) ⟨349845, by rfl⟩ : syracuseStep 932921 = 699691) B699691
theorem B965711 : Blo 413771 965711 := bstep (se 1 (by rfl) ⟨724283, by rfl⟩ : syracuseStep 965711 = 1448567) B1448567
theorem B1326233 : Blo 413771 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B703687 : Blo 413771 703687 := bstep (se 1 (by rfl) ⟨527765, by rfl⟩ : syracuseStep 703687 = 1055531) B1055531
theorem B703849 : Blo 413771 703849 := bstep (se 2 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 703849 = 527887) B527887
theorem B2243965 : Blo 413771 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B933263 : Blo 413771 933263 := bstep (se 1 (by rfl) ⟨699947, by rfl⟩ : syracuseStep 933263 = 1399895) B1399895
theorem B441979 : Blo 413771 441979 := bstep (se 1 (by rfl) ⟨331484, by rfl⟩ : syracuseStep 441979 = 662969) B662969
theorem B1425019 : Blo 413771 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B7618187 : Blo 413771 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B933587 : Blo 413771 933587 := bstep (se 1 (by rfl) ⟨700190, by rfl⟩ : syracuseStep 933587 = 1400381) B1400381
theorem B3161915 : Blo 413771 3161915 := bstep (se 1 (by rfl) ⟨2371436, by rfl⟩ : syracuseStep 3161915 = 4742873) B4742873
theorem B704443 : Blo 413771 704443 := bstep (se 1 (by rfl) ⟨528332, by rfl⟩ : syracuseStep 704443 = 1056665) B1056665
theorem B704551 : Blo 413771 704551 := bstep (se 1 (by rfl) ⟨528413, by rfl⟩ : syracuseStep 704551 = 1056827) B1056827
theorem B704875 : Blo 413771 704875 := bstep (se 1 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 704875 = 1057313) B1057313
theorem B1425883 : Blo 413771 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B442919 : Blo 413771 442919 := bstep (se 1 (by rfl) ⟨332189, by rfl⟩ : syracuseStep 442919 = 664379) B664379
theorem B3195451 : Blo 413771 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B934523 : Blo 413771 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B934649 : Blo 413771 934649 := bstep (se 2 (by rfl) ⟨350493, by rfl⟩ : syracuseStep 934649 = 700987) B700987
theorem B934919 : Blo 413771 934919 := bstep (se 1 (by rfl) ⟨701189, by rfl⟩ : syracuseStep 934919 = 1402379) B1402379
theorem B934991 : Blo 413771 934991 := bstep (se 1 (by rfl) ⟨701243, by rfl⟩ : syracuseStep 934991 = 1402487) B1402487
theorem B1262839 : Blo 413771 1262839 := bstep (se 1 (by rfl) ⟨947129, by rfl⟩ : syracuseStep 1262839 = 1894259) B1894259
theorem B21677357 : Blo 413771 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B3360143 : Blo 413771 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B6768035 : Blo 413771 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B4343203 : Blo 413771 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B2377133 : Blo 413771 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B935387 : Blo 413771 935387 := bstep (se 1 (by rfl) ⟨701540, by rfl⟩ : syracuseStep 935387 = 1403081) B1403081
theorem B1689299 : Blo 413771 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B3000199 : Blo 413771 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B2377633 : Blo 413771 2377633 := bstep (se 2 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 2377633 = 1783225) B1783225
theorem B935855 : Blo 413771 935855 := bstep (se 1 (by rfl) ⟨701891, by rfl⟩ : syracuseStep 935855 = 1403783) B1403783
theorem B936107 : Blo 413771 936107 := bstep (se 1 (by rfl) ⟨702080, by rfl⟩ : syracuseStep 936107 = 1404161) B1404161
theorem B445051 : Blo 413771 445051 := bstep (se 1 (by rfl) ⟨333788, by rfl⟩ : syracuseStep 445051 = 667577) B667577
theorem B936647 : Blo 413771 936647 := bstep (se 1 (by rfl) ⟨702485, by rfl⟩ : syracuseStep 936647 = 1404971) B1404971
theorem B1264567 : Blo 413771 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B1494131 : Blo 413771 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B445871 : Blo 413771 445871 := bstep (se 1 (by rfl) ⟨334403, by rfl⟩ : syracuseStep 445871 = 668807) B668807
theorem B1691117 : Blo 413771 1691117 := bstep (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) B634169
theorem B937511 : Blo 413771 937511 := bstep (se 1 (by rfl) ⟨703133, by rfl⟩ : syracuseStep 937511 = 1406267) B1406267
theorem B2870923 : Blo 413771 2870923 := bstep (se 1 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 2870923 = 4306385) B4306385
theorem B1330987 : Blo 413771 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B937835 : Blo 413771 937835 := bstep (se 1 (by rfl) ⟨703376, by rfl⟩ : syracuseStep 937835 = 1406753) B1406753
theorem B3002273 : Blo 413771 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B937889 : Blo 413771 937889 := bstep (se 2 (by rfl) ⟨351708, by rfl⟩ : syracuseStep 937889 = 703417) B703417
theorem B1396655 : Blo 413771 1396655 := bstep (se 1 (by rfl) ⟨1047491, by rfl⟩ : syracuseStep 1396655 = 2094983) B2094983
theorem B23973893 : Blo 413771 23973893 := bstep (se 4 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 23973893 = 4495105) B4495105
theorem B413775 : Blo 413771 413775 := bstep (se 1 (by rfl) ⟨310331, by rfl⟩ : syracuseStep 413775 = 620663) B620663
theorem B3166289 : Blo 413771 3166289 := bstep (se 2 (by rfl) ⟨1187358, by rfl⟩ : syracuseStep 3166289 = 2374717) B2374717
theorem B413791 : Blo 413771 413791 := bstep (se 1 (by rfl) ⟨310343, by rfl⟩ : syracuseStep 413791 = 620687) B620687
theorem B413819 : Blo 413771 413819 := bstep (se 1 (by rfl) ⟨310364, by rfl⟩ : syracuseStep 413819 = 620729) B620729
theorem B413871 : Blo 413771 413871 := bstep (se 1 (by rfl) ⟨310403, by rfl⟩ : syracuseStep 413871 = 620807) B620807
theorem B413895 : Blo 413771 413895 := bstep (se 1 (by rfl) ⟨310421, by rfl⟩ : syracuseStep 413895 = 620843) B620843
theorem B413915 : Blo 413771 413915 := bstep (se 1 (by rfl) ⟨310436, by rfl⟩ : syracuseStep 413915 = 620873) B620873
theorem B938231 : Blo 413771 938231 := bstep (se 1 (by rfl) ⟨703673, by rfl⟩ : syracuseStep 938231 = 1407347) B1407347
theorem B413991 : Blo 413771 413991 := bstep (se 1 (by rfl) ⟨310493, by rfl⟩ : syracuseStep 413991 = 620987) B620987
theorem B414031 : Blo 413771 414031 := bstep (se 1 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 414031 = 621047) B621047
theorem B414047 : Blo 413771 414047 := bstep (se 1 (by rfl) ⟨310535, by rfl⟩ : syracuseStep 414047 = 621071) B621071
theorem B414075 : Blo 413771 414075 := bstep (se 1 (by rfl) ⟨310556, by rfl⟩ : syracuseStep 414075 = 621113) B621113
theorem B414127 : Blo 413771 414127 := bstep (se 1 (by rfl) ⟨310595, by rfl⟩ : syracuseStep 414127 = 621191) B621191
theorem B414151 : Blo 413771 414151 := bstep (se 1 (by rfl) ⟨310613, by rfl⟩ : syracuseStep 414151 = 621227) B621227
theorem B414171 : Blo 413771 414171 := bstep (se 1 (by rfl) ⟨310628, by rfl⟩ : syracuseStep 414171 = 621257) B621257
theorem B4477463 : Blo 413771 4477463 := bstep (se 1 (by rfl) ⟨3358097, by rfl⟩ : syracuseStep 4477463 = 6716195) B6716195
theorem B414247 : Blo 413771 414247 := bstep (se 1 (by rfl) ⟨310685, by rfl⟩ : syracuseStep 414247 = 621371) B621371
theorem B414287 : Blo 413771 414287 := bstep (se 1 (by rfl) ⟨310715, by rfl⟩ : syracuseStep 414287 = 621431) B621431
theorem B414303 : Blo 413771 414303 := bstep (se 1 (by rfl) ⟨310727, by rfl⟩ : syracuseStep 414303 = 621455) B621455
theorem B414331 : Blo 413771 414331 := bstep (se 1 (by rfl) ⟨310748, by rfl⟩ : syracuseStep 414331 = 621497) B621497
theorem B1200779 : Blo 413771 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B414383 : Blo 413771 414383 := bstep (se 1 (by rfl) ⟨310787, by rfl⟩ : syracuseStep 414383 = 621575) B621575
theorem B414407 : Blo 413771 414407 := bstep (se 1 (by rfl) ⟨310805, by rfl⟩ : syracuseStep 414407 = 621611) B621611
theorem B414427 : Blo 413771 414427 := bstep (se 1 (by rfl) ⟨310820, by rfl⟩ : syracuseStep 414427 = 621641) B621641
theorem B414503 : Blo 413771 414503 := bstep (se 1 (by rfl) ⟨310877, by rfl⟩ : syracuseStep 414503 = 621755) B621755
theorem B7983917 : Blo 413771 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B938825 : Blo 413771 938825 := bstep (se 2 (by rfl) ⟨352059, by rfl⟩ : syracuseStep 938825 = 704119) B704119
theorem B414543 : Blo 413771 414543 := bstep (se 1 (by rfl) ⟨310907, by rfl⟩ : syracuseStep 414543 = 621815) B621815
theorem B414559 : Blo 413771 414559 := bstep (se 1 (by rfl) ⟨310919, by rfl⟩ : syracuseStep 414559 = 621839) B621839
theorem B414587 : Blo 413771 414587 := bstep (se 1 (by rfl) ⟨310940, by rfl⟩ : syracuseStep 414587 = 621881) B621881
theorem B414639 : Blo 413771 414639 := bstep (se 1 (by rfl) ⟨310979, by rfl⟩ : syracuseStep 414639 = 621959) B621959
theorem B414663 : Blo 413771 414663 := bstep (se 1 (by rfl) ⟨310997, by rfl⟩ : syracuseStep 414663 = 621995) B621995
theorem B414683 : Blo 413771 414683 := bstep (se 1 (by rfl) ⟨311012, by rfl⟩ : syracuseStep 414683 = 622025) B622025
theorem B5690387 : Blo 413771 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B414759 : Blo 413771 414759 := bstep (se 1 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 414759 = 622139) B622139
theorem B414799 : Blo 413771 414799 := bstep (se 1 (by rfl) ⟨311099, by rfl⟩ : syracuseStep 414799 = 622199) B622199
theorem B414815 : Blo 413771 414815 := bstep (se 1 (by rfl) ⟨311111, by rfl⟩ : syracuseStep 414815 = 622223) B622223
theorem B414843 : Blo 413771 414843 := bstep (se 1 (by rfl) ⟨311132, by rfl⟩ : syracuseStep 414843 = 622265) B622265
theorem B414895 : Blo 413771 414895 := bstep (se 1 (by rfl) ⟨311171, by rfl⟩ : syracuseStep 414895 = 622343) B622343
theorem B414919 : Blo 413771 414919 := bstep (se 1 (by rfl) ⟨311189, by rfl⟩ : syracuseStep 414919 = 622379) B622379
theorem B414939 : Blo 413771 414939 := bstep (se 1 (by rfl) ⟨311204, by rfl⟩ : syracuseStep 414939 = 622409) B622409
theorem B2249975 : Blo 413771 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B415015 : Blo 413771 415015 := bstep (se 1 (by rfl) ⟨311261, by rfl⟩ : syracuseStep 415015 = 622523) B622523
theorem B415055 : Blo 413771 415055 := bstep (se 1 (by rfl) ⟨311291, by rfl⟩ : syracuseStep 415055 = 622583) B622583
theorem B415071 : Blo 413771 415071 := bstep (se 1 (by rfl) ⟨311303, by rfl⟩ : syracuseStep 415071 = 622607) B622607
theorem B415099 : Blo 413771 415099 := bstep (se 1 (by rfl) ⟨311324, by rfl⟩ : syracuseStep 415099 = 622649) B622649
theorem B415151 : Blo 413771 415151 := bstep (se 1 (by rfl) ⟨311363, by rfl⟩ : syracuseStep 415151 = 622727) B622727
theorem B415175 : Blo 413771 415175 := bstep (se 1 (by rfl) ⟨311381, by rfl⟩ : syracuseStep 415175 = 622763) B622763
theorem B415195 : Blo 413771 415195 := bstep (se 1 (by rfl) ⟨311396, by rfl⟩ : syracuseStep 415195 = 622793) B622793
theorem B415271 : Blo 413771 415271 := bstep (se 1 (by rfl) ⟨311453, by rfl⟩ : syracuseStep 415271 = 622907) B622907
theorem B415311 : Blo 413771 415311 := bstep (se 1 (by rfl) ⟨311483, by rfl⟩ : syracuseStep 415311 = 622967) B622967
theorem B415327 : Blo 413771 415327 := bstep (se 1 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 415327 = 622991) B622991
theorem B939617 : Blo 413771 939617 := bstep (se 2 (by rfl) ⟨352356, by rfl⟩ : syracuseStep 939617 = 704713) B704713
theorem B415355 : Blo 413771 415355 := bstep (se 1 (by rfl) ⟨311516, by rfl⟩ : syracuseStep 415355 = 623033) B623033
theorem B415407 : Blo 413771 415407 := bstep (se 1 (by rfl) ⟨311555, by rfl⟩ : syracuseStep 415407 = 623111) B623111
theorem B415431 : Blo 413771 415431 := bstep (se 1 (by rfl) ⟨311573, by rfl⟩ : syracuseStep 415431 = 623147) B623147
theorem B415451 : Blo 413771 415451 := bstep (se 1 (by rfl) ⟨311588, by rfl⟩ : syracuseStep 415451 = 623177) B623177
theorem B415527 : Blo 413771 415527 := bstep (se 1 (by rfl) ⟨311645, by rfl⟩ : syracuseStep 415527 = 623291) B623291
theorem B415567 : Blo 413771 415567 := bstep (se 1 (by rfl) ⟨311675, by rfl⟩ : syracuseStep 415567 = 623351) B623351
theorem B415583 : Blo 413771 415583 := bstep (se 1 (by rfl) ⟨311687, by rfl⟩ : syracuseStep 415583 = 623375) B623375
theorem B1202015 : Blo 413771 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B415611 : Blo 413771 415611 := bstep (se 1 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 415611 = 623417) B623417
theorem B415663 : Blo 413771 415663 := bstep (se 1 (by rfl) ⟨311747, by rfl⟩ : syracuseStep 415663 = 623495) B623495
theorem B939959 : Blo 413771 939959 := bstep (se 1 (by rfl) ⟨704969, by rfl⟩ : syracuseStep 939959 = 1409939) B1409939
theorem B415687 : Blo 413771 415687 := bstep (se 1 (by rfl) ⟨311765, by rfl⟩ : syracuseStep 415687 = 623531) B623531
theorem B415707 : Blo 413771 415707 := bstep (se 1 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 415707 = 623561) B623561
theorem B415783 : Blo 413771 415783 := bstep (se 1 (by rfl) ⟨311837, by rfl⟩ : syracuseStep 415783 = 623675) B623675
theorem B3561529 : Blo 413771 3561529 := bstep (se 2 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 3561529 = 2671147) B2671147
theorem B415823 : Blo 413771 415823 := bstep (se 1 (by rfl) ⟨311867, by rfl⟩ : syracuseStep 415823 = 623735) B623735
theorem B415839 : Blo 413771 415839 := bstep (se 1 (by rfl) ⟨311879, by rfl⟩ : syracuseStep 415839 = 623759) B623759
theorem B415867 : Blo 413771 415867 := bstep (se 1 (by rfl) ⟨311900, by rfl⟩ : syracuseStep 415867 = 623801) B623801
theorem B415919 : Blo 413771 415919 := bstep (se 1 (by rfl) ⟨311939, by rfl⟩ : syracuseStep 415919 = 623879) B623879
theorem B415943 : Blo 413771 415943 := bstep (se 1 (by rfl) ⟨311957, by rfl⟩ : syracuseStep 415943 = 623915) B623915
theorem B415963 : Blo 413771 415963 := bstep (se 1 (by rfl) ⟨311972, by rfl⟩ : syracuseStep 415963 = 623945) B623945
theorem B1399031 : Blo 413771 1399031 := bstep (se 1 (by rfl) ⟨1049273, by rfl⟩ : syracuseStep 1399031 = 2098547) B2098547
theorem B416039 : Blo 413771 416039 := bstep (se 1 (by rfl) ⟨312029, by rfl⟩ : syracuseStep 416039 = 624059) B624059
theorem B416079 : Blo 413771 416079 := bstep (se 1 (by rfl) ⟨312059, by rfl⟩ : syracuseStep 416079 = 624119) B624119
theorem B416095 : Blo 413771 416095 := bstep (se 1 (by rfl) ⟨312071, by rfl⟩ : syracuseStep 416095 = 624143) B624143
theorem B416123 : Blo 413771 416123 := bstep (se 1 (by rfl) ⟨312092, by rfl⟩ : syracuseStep 416123 = 624185) B624185
theorem B1268093 : Blo 413771 1268093 := bstep (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) B475535
theorem B416175 : Blo 413771 416175 := bstep (se 1 (by rfl) ⟨312131, by rfl⟩ : syracuseStep 416175 = 624263) B624263
theorem B416199 : Blo 413771 416199 := bstep (se 1 (by rfl) ⟨312149, by rfl⟩ : syracuseStep 416199 = 624299) B624299
theorem B416219 : Blo 413771 416219 := bstep (se 1 (by rfl) ⟨312164, by rfl⟩ : syracuseStep 416219 = 624329) B624329
theorem B416295 : Blo 413771 416295 := bstep (se 1 (by rfl) ⟨312221, by rfl⟩ : syracuseStep 416295 = 624443) B624443
theorem B1399355 : Blo 413771 1399355 := bstep (se 1 (by rfl) ⟨1049516, by rfl⟩ : syracuseStep 1399355 = 2099033) B2099033
theorem B416335 : Blo 413771 416335 := bstep (se 1 (by rfl) ⟨312251, by rfl⟩ : syracuseStep 416335 = 624503) B624503
theorem B416351 : Blo 413771 416351 := bstep (se 1 (by rfl) ⟨312263, by rfl⟩ : syracuseStep 416351 = 624527) B624527
theorem B1333883 : Blo 413771 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B416379 : Blo 413771 416379 := bstep (se 1 (by rfl) ⟨312284, by rfl⟩ : syracuseStep 416379 = 624569) B624569
theorem B416431 : Blo 413771 416431 := bstep (se 1 (by rfl) ⟨312323, by rfl⟩ : syracuseStep 416431 = 624647) B624647
theorem B416455 : Blo 413771 416455 := bstep (se 1 (by rfl) ⟨312341, by rfl⟩ : syracuseStep 416455 = 624683) B624683
theorem B416475 : Blo 413771 416475 := bstep (se 1 (by rfl) ⟨312356, by rfl⟩ : syracuseStep 416475 = 624713) B624713
theorem B416551 : Blo 413771 416551 := bstep (se 1 (by rfl) ⟨312413, by rfl⟩ : syracuseStep 416551 = 624827) B624827
theorem B1399625 : Blo 413771 1399625 := bstep (se 2 (by rfl) ⟨524859, by rfl⟩ : syracuseStep 1399625 = 1049719) B1049719
theorem B416591 : Blo 413771 416591 := bstep (se 1 (by rfl) ⟨312443, by rfl⟩ : syracuseStep 416591 = 624887) B624887
theorem B416607 : Blo 413771 416607 := bstep (se 1 (by rfl) ⟨312455, by rfl⟩ : syracuseStep 416607 = 624911) B624911
theorem B416635 : Blo 413771 416635 := bstep (se 1 (by rfl) ⟨312476, by rfl⟩ : syracuseStep 416635 = 624953) B624953
theorem B1334191 : Blo 413771 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B416687 : Blo 413771 416687 := bstep (se 1 (by rfl) ⟨312515, by rfl⟩ : syracuseStep 416687 = 625031) B625031
theorem B416711 : Blo 413771 416711 := bstep (se 1 (by rfl) ⟨312533, by rfl⟩ : syracuseStep 416711 = 625067) B625067
theorem B416731 : Blo 413771 416731 := bstep (se 1 (by rfl) ⟨312548, by rfl⟩ : syracuseStep 416731 = 625097) B625097
theorem B416807 : Blo 413771 416807 := bstep (se 1 (by rfl) ⟨312605, by rfl⟩ : syracuseStep 416807 = 625211) B625211
theorem B416847 : Blo 413771 416847 := bstep (se 1 (by rfl) ⟨312635, by rfl⟩ : syracuseStep 416847 = 625271) B625271
theorem B416863 : Blo 413771 416863 := bstep (se 1 (by rfl) ⟨312647, by rfl⟩ : syracuseStep 416863 = 625295) B625295
theorem B416891 : Blo 413771 416891 := bstep (se 1 (by rfl) ⟨312668, by rfl⟩ : syracuseStep 416891 = 625337) B625337
theorem B416943 : Blo 413771 416943 := bstep (se 1 (by rfl) ⟨312707, by rfl⟩ : syracuseStep 416943 = 625415) B625415
theorem B416967 : Blo 413771 416967 := bstep (se 1 (by rfl) ⟨312725, by rfl⟩ : syracuseStep 416967 = 625451) B625451
theorem B416987 : Blo 413771 416987 := bstep (se 1 (by rfl) ⟨312740, by rfl⟩ : syracuseStep 416987 = 625481) B625481
theorem B417063 : Blo 413771 417063 := bstep (se 1 (by rfl) ⟨312797, by rfl⟩ : syracuseStep 417063 = 625595) B625595
theorem B417103 : Blo 413771 417103 := bstep (se 1 (by rfl) ⟨312827, by rfl⟩ : syracuseStep 417103 = 625655) B625655
theorem B417119 : Blo 413771 417119 := bstep (se 1 (by rfl) ⟨312839, by rfl⟩ : syracuseStep 417119 = 625679) B625679
theorem B417147 : Blo 413771 417147 := bstep (se 1 (by rfl) ⟨312860, by rfl⟩ : syracuseStep 417147 = 625721) B625721
theorem B417199 : Blo 413771 417199 := bstep (se 1 (by rfl) ⟨312899, by rfl⟩ : syracuseStep 417199 = 625799) B625799
theorem B417223 : Blo 413771 417223 := bstep (se 1 (by rfl) ⟨312917, by rfl⟩ : syracuseStep 417223 = 625835) B625835
theorem B417243 : Blo 413771 417243 := bstep (se 1 (by rfl) ⟨312932, by rfl⟩ : syracuseStep 417243 = 625865) B625865
theorem B417319 : Blo 413771 417319 := bstep (se 1 (by rfl) ⟨312989, by rfl⟩ : syracuseStep 417319 = 625979) B625979
theorem B417359 : Blo 413771 417359 := bstep (se 1 (by rfl) ⟨313019, by rfl⟩ : syracuseStep 417359 = 626039) B626039
theorem B417375 : Blo 413771 417375 := bstep (se 1 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 417375 = 626063) B626063
theorem B417403 : Blo 413771 417403 := bstep (se 1 (by rfl) ⟨313052, by rfl⟩ : syracuseStep 417403 = 626105) B626105
theorem B1990291 : Blo 413771 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B417455 : Blo 413771 417455 := bstep (se 1 (by rfl) ⟨313091, by rfl⟩ : syracuseStep 417455 = 626183) B626183
theorem B417479 : Blo 413771 417479 := bstep (se 1 (by rfl) ⟨313109, by rfl⟩ : syracuseStep 417479 = 626219) B626219
theorem B417499 : Blo 413771 417499 := bstep (se 1 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 417499 = 626249) B626249
theorem B417575 : Blo 413771 417575 := bstep (se 1 (by rfl) ⟨313181, by rfl⟩ : syracuseStep 417575 = 626363) B626363
theorem B1335113 : Blo 413771 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B417615 : Blo 413771 417615 := bstep (se 1 (by rfl) ⟨313211, by rfl⟩ : syracuseStep 417615 = 626423) B626423
theorem B417631 : Blo 413771 417631 := bstep (se 1 (by rfl) ⟨313223, by rfl⟩ : syracuseStep 417631 = 626447) B626447
theorem B417659 : Blo 413771 417659 := bstep (se 1 (by rfl) ⟨313244, by rfl⟩ : syracuseStep 417659 = 626489) B626489
theorem B417711 : Blo 413771 417711 := bstep (se 1 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 417711 = 626567) B626567
theorem B1400759 : Blo 413771 1400759 := bstep (se 1 (by rfl) ⟨1050569, by rfl⟩ : syracuseStep 1400759 = 2101139) B2101139
theorem B417735 : Blo 413771 417735 := bstep (se 1 (by rfl) ⟨313301, by rfl⟩ : syracuseStep 417735 = 626603) B626603
theorem B417755 : Blo 413771 417755 := bstep (se 1 (by rfl) ⟨313316, by rfl⟩ : syracuseStep 417755 = 626633) B626633
theorem B1401353 : Blo 413771 1401353 := bstep (se 2 (by rfl) ⟨525507, by rfl⟩ : syracuseStep 1401353 = 1051015) B1051015
theorem B3171149 : Blo 413771 3171149 := bstep (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) B1189181
theorem B1402217 : Blo 413771 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B1992289 : Blo 413771 1992289 := bstep (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) B1494217
theorem B1402811 : Blo 413771 1402811 := bstep (se 1 (by rfl) ⟨1052108, by rfl⟩ : syracuseStep 1402811 = 2104217) B2104217
theorem B747527 : Blo 413771 747527 := bstep (se 1 (by rfl) ⟨560645, by rfl⟩ : syracuseStep 747527 = 1121291) B1121291
theorem B747643 : Blo 413771 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B5303339 : Blo 413771 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B2256119 : Blo 413771 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B1437193 : Blo 413771 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B749179 : Blo 413771 749179 := bstep (se 1 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 749179 = 1123769) B1123769
theorem B1404539 : Blo 413771 1404539 := bstep (se 1 (by rfl) ⟨1053404, by rfl⟩ : syracuseStep 1404539 = 2106809) B2106809
theorem B1404701 : Blo 413771 1404701 := bstep (se 3 (by rfl) ⟨263381, by rfl⟩ : syracuseStep 1404701 = 526763) B526763
theorem B1995137 : Blo 413771 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B1405403 : Blo 413771 1405403 := bstep (se 1 (by rfl) ⟨1054052, by rfl⟩ : syracuseStep 1405403 = 2108105) B2108105
theorem B1406105 : Blo 413771 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B6059357 : Blo 413771 6059357 := bstep (se 3 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 6059357 = 2272259) B2272259
theorem B3536243 : Blo 413771 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B9598925 : Blo 413771 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B1407293 : Blo 413771 1407293 := bstep (se 3 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 1407293 = 527735) B527735
theorem B1571177 : Blo 413771 1571177 := bstep (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) B1178383
theorem B620975 : Blo 413771 620975 := bstep (se 1 (by rfl) ⟨465731, by rfl⟩ : syracuseStep 620975 = 931463) B931463
theorem B621065 : Blo 413771 621065 := bstep (se 2 (by rfl) ⟨232899, by rfl⟩ : syracuseStep 621065 = 465799) B465799
theorem B2652695 : Blo 413771 2652695 := bstep (se 1 (by rfl) ⟨1989521, by rfl⟩ : syracuseStep 2652695 = 3979043) B3979043
theorem B621095 : Blo 413771 621095 := bstep (se 1 (by rfl) ⟨465821, by rfl⟩ : syracuseStep 621095 = 931643) B931643
theorem B621179 : Blo 413771 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B1178327 : Blo 413771 1178327 := bstep (se 1 (by rfl) ⟨883745, by rfl⟩ : syracuseStep 1178327 = 1767491) B1767491
theorem B621305 : Blo 413771 621305 := bstep (se 2 (by rfl) ⟨232989, by rfl⟩ : syracuseStep 621305 = 465979) B465979
theorem B621407 : Blo 413771 621407 := bstep (se 1 (by rfl) ⟨466055, by rfl⟩ : syracuseStep 621407 = 932111) B932111
theorem B621419 : Blo 413771 621419 := bstep (se 1 (by rfl) ⟨466064, by rfl⟩ : syracuseStep 621419 = 932129) B932129
theorem B1178543 : Blo 413771 1178543 := bstep (se 1 (by rfl) ⟨883907, by rfl⟩ : syracuseStep 1178543 = 1767815) B1767815
theorem B2128823 : Blo 413771 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B621647 : Blo 413771 621647 := bstep (se 1 (by rfl) ⟨466235, by rfl⟩ : syracuseStep 621647 = 932471) B932471
theorem B1408157 : Blo 413771 1408157 := bstep (se 3 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 1408157 = 528059) B528059
theorem B7961773 : Blo 413771 7961773 := bstep (se 3 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 7961773 = 2985665) B2985665
theorem B621767 : Blo 413771 621767 := bstep (se 1 (by rfl) ⟨466325, by rfl⟩ : syracuseStep 621767 = 932651) B932651
theorem B687455 : Blo 413771 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B621929 : Blo 413771 621929 := bstep (se 2 (by rfl) ⟨233223, by rfl⟩ : syracuseStep 621929 = 466447) B466447
theorem B785771 : Blo 413771 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B1047937 : Blo 413771 1047937 := bstep (se 2 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 1047937 = 785953) B785953
theorem B622007 : Blo 413771 622007 := bstep (se 1 (by rfl) ⟨466505, by rfl⟩ : syracuseStep 622007 = 933011) B933011
theorem B2096603 : Blo 413771 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B622043 : Blo 413771 622043 := bstep (se 1 (by rfl) ⟨466532, by rfl⟩ : syracuseStep 622043 = 933065) B933065
theorem B1703405 : Blo 413771 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B589351 : Blo 413771 589351 := bstep (se 1 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 589351 = 884027) B884027
theorem B785999 : Blo 413771 785999 := bstep (se 1 (by rfl) ⟨589499, by rfl⟩ : syracuseStep 785999 = 1178999) B1178999
theorem B1408697 : Blo 413771 1408697 := bstep (se 2 (by rfl) ⟨528261, by rfl⟩ : syracuseStep 1408697 = 1056523) B1056523
theorem B6422435 : Blo 413771 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B622511 : Blo 413771 622511 := bstep (se 1 (by rfl) ⟨466883, by rfl⟩ : syracuseStep 622511 = 933767) B933767
theorem B2097089 : Blo 413771 2097089 := bstep (se 2 (by rfl) ⟨786408, by rfl⟩ : syracuseStep 2097089 = 1572817) B1572817
theorem B1048585 : Blo 413771 1048585 := bstep (se 2 (by rfl) ⟨393219, by rfl⟩ : syracuseStep 1048585 = 786439) B786439
theorem B622697 : Blo 413771 622697 := bstep (se 2 (by rfl) ⟨233511, by rfl⟩ : syracuseStep 622697 = 467023) B467023
theorem B1409129 : Blo 413771 1409129 := bstep (se 2 (by rfl) ⟨528423, by rfl⟩ : syracuseStep 1409129 = 1056847) B1056847
theorem B885001 : Blo 413771 885001 := bstep (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) B663751
theorem B590171 : Blo 413771 590171 := bstep (se 1 (by rfl) ⟨442628, by rfl⟩ : syracuseStep 590171 = 885257) B885257
theorem B4063651 : Blo 413771 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B623015 : Blo 413771 623015 := bstep (se 1 (by rfl) ⟨467261, by rfl⟩ : syracuseStep 623015 = 934523) B934523
theorem B623099 : Blo 413771 623099 := bstep (se 1 (by rfl) ⟨467324, by rfl⟩ : syracuseStep 623099 = 934649) B934649
theorem B623225 : Blo 413771 623225 := bstep (se 2 (by rfl) ⟨233709, by rfl⟩ : syracuseStep 623225 = 467419) B467419
theorem B1901177 : Blo 413771 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B2359955 : Blo 413771 2359955 := bstep (se 1 (by rfl) ⟨1769966, by rfl⟩ : syracuseStep 2359955 = 3539933) B3539933
theorem B623279 : Blo 413771 623279 := bstep (se 1 (by rfl) ⟨467459, by rfl⟩ : syracuseStep 623279 = 934919) B934919
theorem B3539659 : Blo 413771 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B623327 : Blo 413771 623327 := bstep (se 1 (by rfl) ⟨467495, by rfl⟩ : syracuseStep 623327 = 934991) B934991
theorem B4260601 : Blo 413771 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B14451571 : Blo 413771 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B623591 : Blo 413771 623591 := bstep (se 1 (by rfl) ⟨467693, by rfl⟩ : syracuseStep 623591 = 935387) B935387
theorem B3802087 : Blo 413771 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B3146849 : Blo 413771 3146849 := bstep (se 2 (by rfl) ⟨1180068, by rfl⟩ : syracuseStep 3146849 = 2360137) B2360137
theorem B623849 : Blo 413771 623849 := bstep (se 2 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 623849 = 467887) B467887
theorem B623903 : Blo 413771 623903 := bstep (se 1 (by rfl) ⟨467927, by rfl⟩ : syracuseStep 623903 = 935855) B935855
theorem B2360663 : Blo 413771 2360663 := bstep (se 1 (by rfl) ⟨1770497, by rfl⟩ : syracuseStep 2360663 = 3540995) B3540995
theorem B1049993 : Blo 413771 1049993 := bstep (se 2 (by rfl) ⟨393747, by rfl⟩ : syracuseStep 1049993 = 787495) B787495
theorem B1050043 : Blo 413771 1050043 := bstep (se 1 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 1050043 = 1575065) B1575065
theorem B1181117 : Blo 413771 1181117 := bstep (se 3 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 1181117 = 442919) B442919
theorem B624071 : Blo 413771 624071 := bstep (se 1 (by rfl) ⟨468053, by rfl⟩ : syracuseStep 624071 = 936107) B936107
theorem B4064825 : Blo 413771 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B1050347 : Blo 413771 1050347 := bstep (se 1 (by rfl) ⟨787760, by rfl⟩ : syracuseStep 1050347 = 1575521) B1575521
theorem B788231 : Blo 413771 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B624425 : Blo 413771 624425 := bstep (se 2 (by rfl) ⟨234159, by rfl⟩ : syracuseStep 624425 = 468319) B468319
theorem B624431 : Blo 413771 624431 := bstep (se 1 (by rfl) ⟨468323, by rfl⟩ : syracuseStep 624431 = 936647) B936647
theorem B1574761 : Blo 413771 1574761 := bstep (se 2 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 1574761 = 1181071) B1181071
theorem B591823 : Blo 413771 591823 := bstep (se 1 (by rfl) ⟨443867, by rfl⟩ : syracuseStep 591823 = 887735) B887735
theorem B886889 : Blo 413771 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B2656385 : Blo 413771 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B624905 : Blo 413771 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B625007 : Blo 413771 625007 := bstep (se 1 (by rfl) ⟨468755, by rfl⟩ : syracuseStep 625007 = 937511) B937511
theorem B4000265 : Blo 413771 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B625223 : Blo 413771 625223 := bstep (se 1 (by rfl) ⟨468917, by rfl⟩ : syracuseStep 625223 = 937835) B937835
theorem B2001515 : Blo 413771 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B625259 : Blo 413771 625259 := bstep (se 1 (by rfl) ⟨468944, by rfl⟩ : syracuseStep 625259 = 937889) B937889
theorem B1051319 : Blo 413771 1051319 := bstep (se 1 (by rfl) ⟨788489, by rfl⟩ : syracuseStep 1051319 = 1576979) B1576979
theorem B625487 : Blo 413771 625487 := bstep (se 1 (by rfl) ⟨469115, by rfl⟩ : syracuseStep 625487 = 938231) B938231
theorem B2984975 : Blo 413771 2984975 := bstep (se 1 (by rfl) ⟨2238731, by rfl⟩ : syracuseStep 2984975 = 4477463) B4477463
theorem B625883 : Blo 413771 625883 := bstep (se 1 (by rfl) ⟨469412, by rfl⟩ : syracuseStep 625883 = 938825) B938825
theorem B2100491 : Blo 413771 2100491 := bstep (se 1 (by rfl) ⟨1575368, by rfl⟩ : syracuseStep 2100491 = 3150737) B3150737
theorem B5999933 : Blo 413771 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B626057 : Blo 413771 626057 := bstep (se 2 (by rfl) ⟨234771, by rfl⟩ : syracuseStep 626057 = 469543) B469543
theorem B593401 : Blo 413771 593401 := bstep (se 2 (by rfl) ⟨222525, by rfl⟩ : syracuseStep 593401 = 445051) B445051
theorem B626411 : Blo 413771 626411 := bstep (se 1 (by rfl) ⟨469808, by rfl⟩ : syracuseStep 626411 = 939617) B939617
theorem B1052423 : Blo 413771 1052423 := bstep (se 1 (by rfl) ⟨789317, by rfl⟩ : syracuseStep 1052423 = 1578635) B1578635
theorem B790327 : Blo 413771 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B1052473 : Blo 413771 1052473 := bstep (se 2 (by rfl) ⟨394677, by rfl⟩ : syracuseStep 1052473 = 789355) B789355
theorem B626639 : Blo 413771 626639 := bstep (se 1 (by rfl) ⟨469979, by rfl⟩ : syracuseStep 626639 = 939959) B939959
theorem B1052777 : Blo 413771 1052777 := bstep (se 2 (by rfl) ⟨394791, by rfl⟩ : syracuseStep 1052777 = 789583) B789583
theorem B889255 : Blo 413771 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B1053263 : Blo 413771 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B791147 : Blo 413771 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B2102111 : Blo 413771 2102111 := bstep (se 1 (by rfl) ⟨1576583, by rfl⟩ : syracuseStep 2102111 = 3153167) B3153167
theorem B791527 : Blo 413771 791527 := bstep (se 1 (by rfl) ⟨593645, by rfl⟩ : syracuseStep 791527 = 1187291) B1187291
theorem B1774649 : Blo 413771 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B1053911 : Blo 413771 1053911 := bstep (se 1 (by rfl) ⟨790433, by rfl⟩ : syracuseStep 1053911 = 1580867) B1580867
theorem B890075 : Blo 413771 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B791785 : Blo 413771 791785 := bstep (se 2 (by rfl) ⟨296919, by rfl⟩ : syracuseStep 791785 = 593839) B593839
theorem B6755575 : Blo 413771 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B1119703 : Blo 413771 1119703 := bstep (se 1 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 1119703 = 1679555) B1679555
theorem B3806759 : Blo 413771 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B792841 : Blo 413771 792841 := bstep (se 2 (by rfl) ⟨297315, by rfl⟩ : syracuseStep 792841 = 594631) B594631
theorem B3545369 : Blo 413771 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B1186073 : Blo 413771 1186073 := bstep (se 2 (by rfl) ⟨444777, by rfl⟩ : syracuseStep 1186073 = 889555) B889555
theorem B3381581 : Blo 413771 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B1055227 : Blo 413771 1055227 := bstep (se 1 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 1055227 = 1582841) B1582841
theorem B1055339 : Blo 413771 1055339 := bstep (se 1 (by rfl) ⟨791504, by rfl⟩ : syracuseStep 1055339 = 1583009) B1583009
theorem B465583 : Blo 413771 465583 := bstep (se 1 (by rfl) ⟨349187, by rfl⟩ : syracuseStep 465583 = 698375) B698375
theorem B1776323 : Blo 413771 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B2104055 : Blo 413771 2104055 := bstep (se 1 (by rfl) ⟨1578041, by rfl⟩ : syracuseStep 2104055 = 3156083) B3156083
theorem B531355 : Blo 413771 531355 := bstep (se 1 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 531355 = 797033) B797033
theorem B465871 : Blo 413771 465871 := bstep (se 1 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 465871 = 698807) B698807
theorem B2104541 : Blo 413771 2104541 := bstep (se 3 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 2104541 = 789203) B789203
theorem B1055987 : Blo 413771 1055987 := bstep (se 1 (by rfl) ⟨791990, by rfl⟩ : syracuseStep 1055987 = 1583981) B1583981
theorem B466267 : Blo 413771 466267 := bstep (se 1 (by rfl) ⟨349700, by rfl⟩ : syracuseStep 466267 = 699401) B699401
theorem B466375 : Blo 413771 466375 := bstep (se 1 (by rfl) ⟨349781, by rfl⟩ : syracuseStep 466375 = 699563) B699563
theorem B1056199 : Blo 413771 1056199 := bstep (se 1 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 1056199 = 1584299) B1584299
theorem B2989561 : Blo 413771 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B1777211 : Blo 413771 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B1777247 : Blo 413771 1777247 := bstep (se 1 (by rfl) ⟨1332935, by rfl⟩ : syracuseStep 1777247 = 2665871) B2665871
theorem B466735 : Blo 413771 466735 := bstep (se 1 (by rfl) ⟨350051, by rfl⟩ : syracuseStep 466735 = 700103) B700103
theorem B466843 : Blo 413771 466843 := bstep (se 1 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 466843 = 700265) B700265
theorem B1581065 : Blo 413771 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B4726835 : Blo 413771 4726835 := bstep (se 1 (by rfl) ⟨3545126, by rfl⟩ : syracuseStep 4726835 = 7090253) B7090253
theorem B467239 : Blo 413771 467239 := bstep (se 1 (by rfl) ⟨350429, by rfl⟩ : syracuseStep 467239 = 700859) B700859
theorem B467311 : Blo 413771 467311 := bstep (se 1 (by rfl) ⟨350483, by rfl⟩ : syracuseStep 467311 = 700967) B700967
theorem B533063 : Blo 413771 533063 := bstep (se 1 (by rfl) ⟨399797, by rfl⟩ : syracuseStep 533063 = 799595) B799595
theorem B467527 : Blo 413771 467527 := bstep (se 1 (by rfl) ⟨350645, by rfl⟩ : syracuseStep 467527 = 701291) B701291
theorem B4039571 : Blo 413771 4039571 := bstep (se 1 (by rfl) ⟨3029678, by rfl⟩ : syracuseStep 4039571 = 6059357) B6059357
theorem B4268983 : Blo 413771 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B1188989 : Blo 413771 1188989 := bstep (se 3 (by rfl) ⟨222935, by rfl⟩ : syracuseStep 1188989 = 445871) B445871
theorem B13477013 : Blo 413771 13477013 := bstep (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) B631735
theorem B1778921 : Blo 413771 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B6399283 : Blo 413771 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B468391 : Blo 413771 468391 := bstep (se 1 (by rfl) ⟨351293, by rfl⟩ : syracuseStep 468391 = 702587) B702587
theorem B2369159 : Blo 413771 2369159 := bstep (se 1 (by rfl) ⟨1776869, by rfl⟩ : syracuseStep 2369159 = 3553739) B3553739
theorem B2991953 : Blo 413771 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B1419215 : Blo 413771 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B468967 : Blo 413771 468967 := bstep (se 1 (by rfl) ⟨351725, by rfl⟩ : syracuseStep 468967 = 703451) B703451
theorem B4007951 : Blo 413771 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B2107943 : Blo 413771 2107943 := bstep (se 1 (by rfl) ⟨1580957, by rfl⟩ : syracuseStep 2107943 = 3161915) B3161915
theorem B699367 : Blo 413771 699367 := bstep (se 1 (by rfl) ⟨524525, by rfl⟩ : syracuseStep 699367 = 1049051) B1049051
theorem B621849635 : Blo 413771 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B1584481 : Blo 413771 1584481 := bstep (se 2 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 1584481 = 1188361) B1188361
theorem B1584755 : Blo 413771 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B2141959 : Blo 413771 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B1126199 : Blo 413771 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B1584953 : Blo 413771 1584953 := bstep (se 2 (by rfl) ⟨594357, by rfl⟩ : syracuseStep 1584953 = 1188715) B1188715
theorem B1683785 : Blo 413771 1683785 := bstep (se 2 (by rfl) ⟨631419, by rfl⟩ : syracuseStep 1683785 = 1262839) B1262839
theorem B2110049 : Blo 413771 2110049 := bstep (se 2 (by rfl) ⟨791268, by rfl⟩ : syracuseStep 2110049 = 1582537) B1582537
theorem B1127411 : Blo 413771 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B931049 : Blo 413771 931049 := bstep (se 2 (by rfl) ⟨349143, by rfl⟩ : syracuseStep 931049 = 698287) B698287
theorem B2110697 : Blo 413771 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B931103 : Blo 413771 931103 := bstep (se 1 (by rfl) ⟨698327, by rfl⟩ : syracuseStep 931103 = 1396655) B1396655
theorem B2110859 : Blo 413771 2110859 := bstep (se 1 (by rfl) ⟨1583144, by rfl⟩ : syracuseStep 2110859 = 3166289) B3166289
theorem B996857 : Blo 413771 996857 := bstep (se 2 (by rfl) ⟨373821, by rfl⟩ : syracuseStep 996857 = 747643) B747643
theorem B702047 : Blo 413771 702047 := bstep (se 1 (by rfl) ⟨526535, by rfl⟩ : syracuseStep 702047 = 1053071) B1053071
theorem B800519 : Blo 413771 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B931625 : Blo 413771 931625 := bstep (se 2 (by rfl) ⟨349359, by rfl⟩ : syracuseStep 931625 = 698719) B698719
theorem B702263 : Blo 413771 702263 := bstep (se 1 (by rfl) ⟨526697, by rfl⟩ : syracuseStep 702263 = 1053395) B1053395
theorem B5322611 : Blo 413771 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B8960381 : Blo 413771 8960381 := bstep (se 3 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 8960381 = 3360143) B3360143
theorem B1685927 : Blo 413771 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B801343 : Blo 413771 801343 := bstep (se 1 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 801343 = 1202015) B1202015
theorem B703039 : Blo 413771 703039 := bstep (se 1 (by rfl) ⟨527279, by rfl⟩ : syracuseStep 703039 = 1054559) B1054559
theorem B1686089 : Blo 413771 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B2374217 : Blo 413771 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B932687 : Blo 413771 932687 := bstep (se 1 (by rfl) ⟨699515, by rfl⟩ : syracuseStep 932687 = 1399031) B1399031
theorem B932903 : Blo 413771 932903 := bstep (se 1 (by rfl) ⟨699677, by rfl⟩ : syracuseStep 932903 = 1399355) B1399355
theorem B933083 : Blo 413771 933083 := bstep (se 1 (by rfl) ⟨699812, by rfl⟩ : syracuseStep 933083 = 1399625) B1399625
theorem B703721 : Blo 413771 703721 := bstep (se 2 (by rfl) ⟨263895, by rfl⟩ : syracuseStep 703721 = 527791) B527791
theorem B703775 : Blo 413771 703775 := bstep (se 1 (by rfl) ⟨527831, by rfl⟩ : syracuseStep 703775 = 1055663) B1055663
theorem B1916257 : Blo 413771 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B933281 : Blo 413771 933281 := bstep (se 2 (by rfl) ⟨349980, by rfl⟩ : syracuseStep 933281 = 699961) B699961
theorem B1424827 : Blo 413771 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B998905 : Blo 413771 998905 := bstep (se 2 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 998905 = 749179) B749179
theorem B933839 : Blo 413771 933839 := bstep (se 1 (by rfl) ⟨700379, by rfl⟩ : syracuseStep 933839 = 1400759) B1400759
theorem B934217 : Blo 413771 934217 := bstep (se 2 (by rfl) ⟨350331, by rfl⟩ : syracuseStep 934217 = 700663) B700663
theorem B934235 : Blo 413771 934235 := bstep (se 1 (by rfl) ⟨700676, by rfl⟩ : syracuseStep 934235 = 1401353) B1401353
theorem B2114099 : Blo 413771 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B934811 : Blo 413771 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B5129153 : Blo 413771 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B935009 : Blo 413771 935009 := bstep (se 2 (by rfl) ⟨350628, by rfl⟩ : syracuseStep 935009 = 701257) B701257
theorem B935207 : Blo 413771 935207 := bstep (se 1 (by rfl) ⟨701405, by rfl⟩ : syracuseStep 935207 = 1402811) B1402811
theorem B935585 : Blo 413771 935585 := bstep (se 2 (by rfl) ⟨350844, by rfl⟩ : syracuseStep 935585 = 701689) B701689
theorem B6408143 : Blo 413771 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B935945 : Blo 413771 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B4376753 : Blo 413771 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B3164345 : Blo 413771 3164345 := bstep (se 2 (by rfl) ⟨1186629, by rfl⟩ : syracuseStep 3164345 = 2373259) B2373259
theorem B936359 : Blo 413771 936359 := bstep (se 1 (by rfl) ⟨702269, by rfl⟩ : syracuseStep 936359 = 1404539) B1404539
theorem B936467 : Blo 413771 936467 := bstep (se 1 (by rfl) ⟨702350, by rfl⟩ : syracuseStep 936467 = 1404701) B1404701
theorem B936521 : Blo 413771 936521 := bstep (se 2 (by rfl) ⟨351195, by rfl⟩ : syracuseStep 936521 = 702391) B702391
theorem B1330091 : Blo 413771 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B3984349 : Blo 413771 3984349 := bstep (se 3 (by rfl) ⟨747065, by rfl⟩ : syracuseStep 3984349 = 1494131) B1494131
theorem B936935 : Blo 413771 936935 := bstep (se 1 (by rfl) ⟨702701, by rfl⟩ : syracuseStep 936935 = 1405403) B1405403
theorem B937313 : Blo 413771 937313 := bstep (se 2 (by rfl) ⟨351492, by rfl⟩ : syracuseStep 937313 = 702985) B702985
theorem B937403 : Blo 413771 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B937529 : Blo 413771 937529 := bstep (se 2 (by rfl) ⟨351573, by rfl⟩ : syracuseStep 937529 = 703147) B703147
theorem B3002159 : Blo 413771 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B938195 : Blo 413771 938195 := bstep (se 1 (by rfl) ⟨703646, by rfl⟩ : syracuseStep 938195 = 1407293) B1407293
theorem B938249 : Blo 413771 938249 := bstep (se 2 (by rfl) ⟨351843, by rfl⟩ : syracuseStep 938249 = 703687) B703687
theorem B413983 : Blo 413771 413983 := bstep (se 1 (by rfl) ⟨310487, by rfl⟩ : syracuseStep 413983 = 620975) B620975
theorem B414043 : Blo 413771 414043 := bstep (se 1 (by rfl) ⟨310532, by rfl⟩ : syracuseStep 414043 = 621065) B621065
theorem B414063 : Blo 413771 414063 := bstep (se 1 (by rfl) ⟨310547, by rfl⟩ : syracuseStep 414063 = 621095) B621095
theorem B414119 : Blo 413771 414119 := bstep (se 1 (by rfl) ⟨310589, by rfl⟩ : syracuseStep 414119 = 621179) B621179
theorem B938465 : Blo 413771 938465 := bstep (se 2 (by rfl) ⟨351924, by rfl⟩ : syracuseStep 938465 = 703849) B703849
theorem B414203 : Blo 413771 414203 := bstep (se 1 (by rfl) ⟨310652, by rfl⟩ : syracuseStep 414203 = 621305) B621305
theorem B1397249 : Blo 413771 1397249 := bstep (se 2 (by rfl) ⟨523968, by rfl⟩ : syracuseStep 1397249 = 1047937) B1047937
theorem B7328315 : Blo 413771 7328315 := bstep (se 1 (by rfl) ⟨5496236, by rfl⟩ : syracuseStep 7328315 = 10992473) B10992473
theorem B414271 : Blo 413771 414271 := bstep (se 1 (by rfl) ⟨310703, by rfl⟩ : syracuseStep 414271 = 621407) B621407
theorem B414279 : Blo 413771 414279 := bstep (se 1 (by rfl) ⟨310709, by rfl⟩ : syracuseStep 414279 = 621419) B621419
theorem B414431 : Blo 413771 414431 := bstep (se 1 (by rfl) ⟨310823, by rfl⟩ : syracuseStep 414431 = 621647) B621647
theorem B643807 : Blo 413771 643807 := bstep (se 1 (by rfl) ⟨482855, by rfl⟩ : syracuseStep 643807 = 965711) B965711
theorem B938771 : Blo 413771 938771 := bstep (se 1 (by rfl) ⟨704078, by rfl⟩ : syracuseStep 938771 = 1408157) B1408157
theorem B414511 : Blo 413771 414511 := bstep (se 1 (by rfl) ⟨310883, by rfl⟩ : syracuseStep 414511 = 621767) B621767
theorem B414619 : Blo 413771 414619 := bstep (se 1 (by rfl) ⟨310964, by rfl⟩ : syracuseStep 414619 = 621929) B621929
theorem B414671 : Blo 413771 414671 := bstep (se 1 (by rfl) ⟨311003, by rfl⟩ : syracuseStep 414671 = 622007) B622007
theorem B1397735 : Blo 413771 1397735 := bstep (se 1 (by rfl) ⟨1048301, by rfl⟩ : syracuseStep 1397735 = 2096603) B2096603
theorem B414695 : Blo 413771 414695 := bstep (se 1 (by rfl) ⟨311021, by rfl⟩ : syracuseStep 414695 = 622043) B622043
theorem B1135603 : Blo 413771 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B939131 : Blo 413771 939131 := bstep (se 1 (by rfl) ⟨704348, by rfl⟩ : syracuseStep 939131 = 1408697) B1408697
theorem B939257 : Blo 413771 939257 := bstep (se 2 (by rfl) ⟨352221, by rfl⟩ : syracuseStep 939257 = 704443) B704443
theorem B4281623 : Blo 413771 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B415007 : Blo 413771 415007 := bstep (se 1 (by rfl) ⟨311255, by rfl⟩ : syracuseStep 415007 = 622511) B622511
theorem B1398059 : Blo 413771 1398059 := bstep (se 1 (by rfl) ⟨1048544, by rfl⟩ : syracuseStep 1398059 = 2097089) B2097089
theorem B415067 : Blo 413771 415067 := bstep (se 1 (by rfl) ⟨311300, by rfl⟩ : syracuseStep 415067 = 622601) B622601
theorem B415087 : Blo 413771 415087 := bstep (se 1 (by rfl) ⟨311315, by rfl⟩ : syracuseStep 415087 = 622631) B622631
theorem B939401 : Blo 413771 939401 := bstep (se 2 (by rfl) ⟨352275, by rfl⟩ : syracuseStep 939401 = 704551) B704551
theorem B415143 : Blo 413771 415143 := bstep (se 1 (by rfl) ⟨311357, by rfl⟩ : syracuseStep 415143 = 622715) B622715
theorem B415227 : Blo 413771 415227 := bstep (se 1 (by rfl) ⟨311420, by rfl⟩ : syracuseStep 415227 = 622841) B622841
theorem B939527 : Blo 413771 939527 := bstep (se 1 (by rfl) ⟨704645, by rfl⟩ : syracuseStep 939527 = 1409291) B1409291
theorem B1398329 : Blo 413771 1398329 := bstep (se 2 (by rfl) ⟨524373, by rfl⟩ : syracuseStep 1398329 = 1048747) B1048747
theorem B415295 : Blo 413771 415295 := bstep (se 1 (by rfl) ⟨311471, by rfl⟩ : syracuseStep 415295 = 622943) B622943
theorem B415303 : Blo 413771 415303 := bstep (se 1 (by rfl) ⟨311477, by rfl⟩ : syracuseStep 415303 = 622955) B622955
theorem B939707 : Blo 413771 939707 := bstep (se 1 (by rfl) ⟨704780, by rfl⟩ : syracuseStep 939707 = 1409561) B1409561
theorem B415455 : Blo 413771 415455 := bstep (se 1 (by rfl) ⟨311591, by rfl⟩ : syracuseStep 415455 = 623183) B623183
theorem B415535 : Blo 413771 415535 := bstep (se 1 (by rfl) ⟨311651, by rfl⟩ : syracuseStep 415535 = 623303) B623303
theorem B939833 : Blo 413771 939833 := bstep (se 2 (by rfl) ⟨352437, by rfl⟩ : syracuseStep 939833 = 704875) B704875
theorem B415643 : Blo 413771 415643 := bstep (se 1 (by rfl) ⟨311732, by rfl⟩ : syracuseStep 415643 = 623465) B623465
theorem B415695 : Blo 413771 415695 := bstep (se 1 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 415695 = 623543) B623543
theorem B415719 : Blo 413771 415719 := bstep (se 1 (by rfl) ⟨311789, by rfl⟩ : syracuseStep 415719 = 623579) B623579
theorem B4512023 : Blo 413771 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B416031 : Blo 413771 416031 := bstep (se 1 (by rfl) ⟨312023, by rfl⟩ : syracuseStep 416031 = 624047) B624047
theorem B416091 : Blo 413771 416091 := bstep (se 1 (by rfl) ⟨312068, by rfl⟩ : syracuseStep 416091 = 624137) B624137
theorem B416111 : Blo 413771 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B416167 : Blo 413771 416167 := bstep (se 1 (by rfl) ⟨312125, by rfl⟩ : syracuseStep 416167 = 624251) B624251
theorem B416251 : Blo 413771 416251 := bstep (se 1 (by rfl) ⟨312188, by rfl⟩ : syracuseStep 416251 = 624377) B624377
theorem B416319 : Blo 413771 416319 := bstep (se 1 (by rfl) ⟨312239, by rfl⟩ : syracuseStep 416319 = 624479) B624479
theorem B416327 : Blo 413771 416327 := bstep (se 1 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 416327 = 624491) B624491
theorem B416479 : Blo 413771 416479 := bstep (se 1 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 416479 = 624719) B624719
theorem B1399571 : Blo 413771 1399571 := bstep (se 1 (by rfl) ⟨1049678, by rfl⟩ : syracuseStep 1399571 = 2099357) B2099357
theorem B416559 : Blo 413771 416559 := bstep (se 1 (by rfl) ⟨312419, by rfl⟩ : syracuseStep 416559 = 624839) B624839
theorem B416667 : Blo 413771 416667 := bstep (se 1 (by rfl) ⟨312500, by rfl⟩ : syracuseStep 416667 = 625001) B625001
theorem B416719 : Blo 413771 416719 := bstep (se 1 (by rfl) ⟨312539, by rfl⟩ : syracuseStep 416719 = 625079) B625079
theorem B416743 : Blo 413771 416743 := bstep (se 1 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 416743 = 625115) B625115
theorem B5790937 : Blo 413771 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B417055 : Blo 413771 417055 := bstep (se 1 (by rfl) ⟨312791, by rfl⟩ : syracuseStep 417055 = 625583) B625583
theorem B417115 : Blo 413771 417115 := bstep (se 1 (by rfl) ⟨312836, by rfl⟩ : syracuseStep 417115 = 625673) B625673
theorem B417135 : Blo 413771 417135 := bstep (se 1 (by rfl) ⟨312851, by rfl⟩ : syracuseStep 417135 = 625703) B625703
theorem B417191 : Blo 413771 417191 := bstep (se 1 (by rfl) ⟨312893, by rfl⟩ : syracuseStep 417191 = 625787) B625787
theorem B417275 : Blo 413771 417275 := bstep (se 1 (by rfl) ⟨312956, by rfl⟩ : syracuseStep 417275 = 625913) B625913
theorem B417343 : Blo 413771 417343 := bstep (se 1 (by rfl) ⟨313007, by rfl⟩ : syracuseStep 417343 = 626015) B626015
theorem B417351 : Blo 413771 417351 := bstep (se 1 (by rfl) ⟨313013, by rfl⟩ : syracuseStep 417351 = 626027) B626027
theorem B1400435 : Blo 413771 1400435 := bstep (se 1 (by rfl) ⟨1050326, by rfl⟩ : syracuseStep 1400435 = 2100653) B2100653
theorem B417503 : Blo 413771 417503 := bstep (se 1 (by rfl) ⟨313127, by rfl⟩ : syracuseStep 417503 = 626255) B626255
theorem B3366659 : Blo 413771 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B417583 : Blo 413771 417583 := bstep (se 1 (by rfl) ⟨313187, by rfl⟩ : syracuseStep 417583 = 626375) B626375
theorem B21520247 : Blo 413771 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B1400705 : Blo 413771 1400705 := bstep (se 2 (by rfl) ⟨525264, by rfl⟩ : syracuseStep 1400705 = 1050529) B1050529
theorem B3170177 : Blo 413771 3170177 := bstep (se 2 (by rfl) ⟨1188816, by rfl⟩ : syracuseStep 3170177 = 2377633) B2377633
theorem B417691 : Blo 413771 417691 := bstep (se 1 (by rfl) ⟨313268, by rfl⟩ : syracuseStep 417691 = 626537) B626537
theorem B417743 : Blo 413771 417743 := bstep (se 1 (by rfl) ⟨313307, by rfl⟩ : syracuseStep 417743 = 626615) B626615
theorem B417767 : Blo 413771 417767 := bstep (se 1 (by rfl) ⟨313325, by rfl⟩ : syracuseStep 417767 = 626651) B626651
theorem B15982595 : Blo 413771 15982595 := bstep (se 1 (by rfl) ⟨11986946, by rfl⟩ : syracuseStep 15982595 = 23973893) B23973893
theorem B1269785 : Blo 413771 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B5988401 : Blo 413771 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B4546979 : Blo 413771 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B1401515 : Blo 413771 1401515 := bstep (se 1 (by rfl) ⟨1051136, by rfl⟩ : syracuseStep 1401515 = 2102273) B2102273
theorem B3793591 : Blo 413771 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B1532903 : Blo 413771 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B1402055 : Blo 413771 1402055 := bstep (se 1 (by rfl) ⟨1051541, by rfl⟩ : syracuseStep 1402055 = 2103083) B2103083
theorem B3171635 : Blo 413771 3171635 := bstep (se 1 (by rfl) ⟨2378726, by rfl⟩ : syracuseStep 3171635 = 4757453) B4757453
theorem B1992023 : Blo 413771 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B1009313 : Blo 413771 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B3827897 : Blo 413771 3827897 := bstep (se 2 (by rfl) ⟨1435461, by rfl⟩ : syracuseStep 3827897 = 2870923) B2870923
theorem B1796681 : Blo 413771 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1403567 : Blo 413771 1403567 := bstep (se 1 (by rfl) ⟨1052675, by rfl⟩ : syracuseStep 1403567 = 2105351) B2105351
theorem B1993405 : Blo 413771 1993405 := bstep (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) B747527
theorem B1403891 : Blo 413771 1403891 := bstep (se 1 (by rfl) ⟨1052918, by rfl⟩ : syracuseStep 1403891 = 2105837) B2105837
theorem B3370099 : Blo 413771 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B1404431 : Blo 413771 1404431 := bstep (se 1 (by rfl) ⟨1053323, by rfl⟩ : syracuseStep 1404431 = 2106647) B2106647
theorem B945851 : Blo 413771 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B749243 : Blo 413771 749243 := bstep (se 1 (by rfl) ⟨561932, by rfl⟩ : syracuseStep 749243 = 1123865) B1123865
theorem B26570753 : Blo 413771 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B3567887 : Blo 413771 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B1012193 : Blo 413771 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B1405511 : Blo 413771 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B3535559 : Blo 413771 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B1504079 : Blo 413771 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B1405943 : Blo 413771 1405943 := bstep (se 1 (by rfl) ⟨1054457, by rfl⟩ : syracuseStep 1405943 = 2108915) B2108915
theorem B2847959 : Blo 413771 2847959 := bstep (se 1 (by rfl) ⟨2135969, by rfl⟩ : syracuseStep 2847959 = 4271939) B4271939
theorem B947495 : Blo 413771 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B4748705 : Blo 413771 4748705 := bstep (se 2 (by rfl) ⟨1780764, by rfl⟩ : syracuseStep 4748705 = 3561529) B3561529
theorem B3536621 : Blo 413771 3536621 := bstep (se 3 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 3536621 = 1326233) B1326233
theorem B1406807 : Blo 413771 1406807 := bstep (se 1 (by rfl) ⟨1055105, by rfl⟩ : syracuseStep 1406807 = 2110211) B2110211
theorem B2357221 : Blo 413771 2357221 := bstep (se 4 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 2357221 = 441979) B441979
theorem B2357495 : Blo 413771 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B620891 : Blo 413771 620891 := bstep (se 1 (by rfl) ⟨465668, by rfl⟩ : syracuseStep 620891 = 931337) B931337
theorem B621119 : Blo 413771 621119 := bstep (se 1 (by rfl) ⟨465839, by rfl⟩ : syracuseStep 621119 = 931679) B931679
theorem B1800767 : Blo 413771 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B621239 : Blo 413771 621239 := bstep (se 1 (by rfl) ⟨465929, by rfl⟩ : syracuseStep 621239 = 931859) B931859
theorem B1407887 : Blo 413771 1407887 := bstep (se 1 (by rfl) ⟨1055915, by rfl⟩ : syracuseStep 1407887 = 2111831) B2111831
theorem B10615697 : Blo 413771 10615697 := bstep (se 2 (by rfl) ⟨3980886, by rfl⟩ : syracuseStep 10615697 = 7961773) B7961773
theorem B1047451 : Blo 413771 1047451 := bstep (se 1 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 1047451 = 1571177) B1571177
theorem B621467 : Blo 413771 621467 := bstep (se 1 (by rfl) ⟨466100, by rfl⟩ : syracuseStep 621467 = 932201) B932201
theorem B1768463 : Blo 413771 1768463 := bstep (se 1 (by rfl) ⟨1326347, by rfl⟩ : syracuseStep 1768463 = 2652695) B2652695
theorem B785551 : Blo 413771 785551 := bstep (se 1 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 785551 = 1178327) B1178327
theorem B785695 : Blo 413771 785695 := bstep (se 1 (by rfl) ⟨589271, by rfl⟩ : syracuseStep 785695 = 1178543) B1178543
theorem B621863 : Blo 413771 621863 := bstep (se 1 (by rfl) ⟨466397, by rfl⟩ : syracuseStep 621863 = 932795) B932795
theorem B621947 : Blo 413771 621947 := bstep (se 1 (by rfl) ⟨466460, by rfl⟩ : syracuseStep 621947 = 932921) B932921
theorem B785801 : Blo 413771 785801 := bstep (se 2 (by rfl) ⟨294675, by rfl⟩ : syracuseStep 785801 = 589351) B589351
theorem B622073 : Blo 413771 622073 := bstep (se 2 (by rfl) ⟨233277, by rfl⟩ : syracuseStep 622073 = 466555) B466555
theorem B1900025 : Blo 413771 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B2653721 : Blo 413771 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B458303 : Blo 413771 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B523847 : Blo 413771 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B622175 : Blo 413771 622175 := bstep (se 1 (by rfl) ⟨466631, by rfl⟩ : syracuseStep 622175 = 933263) B933263
theorem B523999 : Blo 413771 523999 := bstep (se 1 (by rfl) ⟨392999, by rfl⟩ : syracuseStep 523999 = 785999) B785999
theorem B5078791 : Blo 413771 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B622391 : Blo 413771 622391 := bstep (se 1 (by rfl) ⟨466793, by rfl⟩ : syracuseStep 622391 = 933587) B933587
theorem B622811 : Blo 413771 622811 := bstep (se 1 (by rfl) ⟨467108, by rfl⟩ : syracuseStep 622811 = 934217) B934217
theorem B622823 : Blo 413771 622823 := bstep (se 1 (by rfl) ⟨467117, by rfl⟩ : syracuseStep 622823 = 934235) B934235
theorem B1180001 : Blo 413771 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B1409399 : Blo 413771 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B622985 : Blo 413771 622985 := bstep (se 2 (by rfl) ⟨233619, by rfl⟩ : syracuseStep 622985 = 467239) B467239
theorem B1573303 : Blo 413771 1573303 := bstep (se 1 (by rfl) ⟨1179977, by rfl⟩ : syracuseStep 1573303 = 2359955) B2359955
theorem B623081 : Blo 413771 623081 := bstep (se 2 (by rfl) ⟨233655, by rfl⟩ : syracuseStep 623081 = 467311) B467311
theorem B623207 : Blo 413771 623207 := bstep (se 1 (by rfl) ⟨467405, by rfl⟩ : syracuseStep 623207 = 934811) B934811
theorem B2097899 : Blo 413771 2097899 := bstep (se 1 (by rfl) ⟨1573424, by rfl⟩ : syracuseStep 2097899 = 3146849) B3146849
theorem B623339 : Blo 413771 623339 := bstep (se 1 (by rfl) ⟨467504, by rfl⟩ : syracuseStep 623339 = 935009) B935009
theorem B623369 : Blo 413771 623369 := bstep (se 2 (by rfl) ⟨233763, by rfl⟩ : syracuseStep 623369 = 467527) B467527
theorem B4490093 : Blo 413771 4490093 := bstep (se 3 (by rfl) ⟨841892, by rfl⟩ : syracuseStep 4490093 = 1683785) B1683785
theorem B623471 : Blo 413771 623471 := bstep (se 1 (by rfl) ⟨467603, by rfl⟩ : syracuseStep 623471 = 935207) B935207
theorem B1573775 : Blo 413771 1573775 := bstep (se 1 (by rfl) ⟨1180331, by rfl⟩ : syracuseStep 1573775 = 2360663) B2360663
theorem B1573789 : Blo 413771 1573789 := bstep (se 3 (by rfl) ⟨295085, by rfl⟩ : syracuseStep 1573789 = 590171) B590171
theorem B4719545 : Blo 413771 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B787411 : Blo 413771 787411 := bstep (se 1 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 787411 = 1181117) B1181117
theorem B623723 : Blo 413771 623723 := bstep (se 1 (by rfl) ⟨467792, by rfl⟩ : syracuseStep 623723 = 935585) B935585
theorem B19268761 : Blo 413771 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B623963 : Blo 413771 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B1770923 : Blo 413771 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B2917835 : Blo 413771 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B624239 : Blo 413771 624239 := bstep (se 1 (by rfl) ⟨468179, by rfl⟩ : syracuseStep 624239 = 936359) B936359
theorem B624311 : Blo 413771 624311 := bstep (se 1 (by rfl) ⟨468233, by rfl⟩ : syracuseStep 624311 = 936467) B936467
theorem B624347 : Blo 413771 624347 := bstep (se 1 (by rfl) ⟨468260, by rfl⟩ : syracuseStep 624347 = 936521) B936521
theorem B624521 : Blo 413771 624521 := bstep (se 2 (by rfl) ⟨234195, by rfl⟩ : syracuseStep 624521 = 468391) B468391
theorem B886727 : Blo 413771 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B624623 : Blo 413771 624623 := bstep (se 1 (by rfl) ⟨468467, by rfl⟩ : syracuseStep 624623 = 936935) B936935
theorem B3999955 : Blo 413771 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B624875 : Blo 413771 624875 := bstep (se 1 (by rfl) ⟨468656, by rfl⟩ : syracuseStep 624875 = 937313) B937313
theorem B624935 : Blo 413771 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B625019 : Blo 413771 625019 := bstep (se 1 (by rfl) ⟨468764, by rfl⟩ : syracuseStep 625019 = 937529) B937529
theorem B2099681 : Blo 413771 2099681 := bstep (se 2 (by rfl) ⟨787380, by rfl⟩ : syracuseStep 2099681 = 1574761) B1574761
theorem B2001439 : Blo 413771 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B789097 : Blo 413771 789097 := bstep (se 2 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 789097 = 591823) B591823
theorem B625289 : Blo 413771 625289 := bstep (se 2 (by rfl) ⟨234483, by rfl⟩ : syracuseStep 625289 = 468967) B468967
theorem B625463 : Blo 413771 625463 := bstep (se 1 (by rfl) ⟨469097, by rfl⟩ : syracuseStep 625463 = 938195) B938195
theorem B625499 : Blo 413771 625499 := bstep (se 1 (by rfl) ⟨469124, by rfl⟩ : syracuseStep 625499 = 938249) B938249
theorem B625643 : Blo 413771 625643 := bstep (se 1 (by rfl) ⟨469232, by rfl⟩ : syracuseStep 625643 = 938465) B938465
theorem B4885543 : Blo 413771 4885543 := bstep (se 1 (by rfl) ⟨3664157, by rfl⟩ : syracuseStep 4885543 = 7328315) B7328315
theorem B625847 : Blo 413771 625847 := bstep (se 1 (by rfl) ⟨469385, by rfl⟩ : syracuseStep 625847 = 938771) B938771
theorem B1183099 : Blo 413771 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B626087 : Blo 413771 626087 := bstep (se 1 (by rfl) ⟨469565, by rfl⟩ : syracuseStep 626087 = 939131) B939131
theorem B2526653 : Blo 413771 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B626171 : Blo 413771 626171 := bstep (se 1 (by rfl) ⟨469628, by rfl⟩ : syracuseStep 626171 = 939257) B939257
theorem B2854415 : Blo 413771 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B2657873 : Blo 413771 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B626267 : Blo 413771 626267 := bstep (se 1 (by rfl) ⟨469700, by rfl⟩ : syracuseStep 626267 = 939401) B939401
theorem B626351 : Blo 413771 626351 := bstep (se 1 (by rfl) ⟨469763, by rfl⟩ : syracuseStep 626351 = 939527) B939527
theorem B626471 : Blo 413771 626471 := bstep (se 1 (by rfl) ⟨469853, by rfl⟩ : syracuseStep 626471 = 939707) B939707
theorem B626555 : Blo 413771 626555 := bstep (se 1 (by rfl) ⟨469916, by rfl⟩ : syracuseStep 626555 = 939833) B939833
theorem B5312465 : Blo 413771 5312465 := bstep (se 2 (by rfl) ⟨1992174, by rfl⟩ : syracuseStep 5312465 = 3984349) B3984349
theorem B4493465 : Blo 413771 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B2363579 : Blo 413771 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B790715 : Blo 413771 790715 := bstep (se 1 (by rfl) ⟨593036, by rfl⟩ : syracuseStep 790715 = 1186073) B1186073
theorem B1184215 : Blo 413771 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B791201 : Blo 413771 791201 := bstep (se 2 (by rfl) ⟨296700, by rfl⟩ : syracuseStep 791201 = 593401) B593401
theorem B2101949 : Blo 413771 2101949 := bstep (se 3 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 2101949 = 788231) B788231
theorem B2134717 : Blo 413771 2134717 := bstep (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) B800519
theorem B2855945 : Blo 413771 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B1184807 : Blo 413771 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B1184831 : Blo 413771 1184831 := bstep (se 1 (by rfl) ⟨888623, by rfl⟩ : syracuseStep 1184831 = 1777247) B1777247
theorem B1053769 : Blo 413771 1053769 := bstep (se 2 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 1053769 = 790327) B790327
theorem B10655063 : Blo 413771 10655063 := bstep (se 1 (by rfl) ⟨7991297, by rfl⟩ : syracuseStep 10655063 = 15982595) B15982595
theorem B1054043 : Blo 413771 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B3151223 : Blo 413771 3151223 := bstep (se 1 (by rfl) ⟨2363417, by rfl⟩ : syracuseStep 3151223 = 4726835) B4726835
theorem B2365037 : Blo 413771 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B1185673 : Blo 413771 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B2693047 : Blo 413771 2693047 := bstep (se 1 (by rfl) ⟨2019785, by rfl⟩ : syracuseStep 2693047 = 4039571) B4039571
theorem B792659 : Blo 413771 792659 := bstep (se 1 (by rfl) ⟨594494, by rfl⟩ : syracuseStep 792659 = 1188989) B1188989
theorem B8984675 : Blo 413771 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B1185947 : Blo 413771 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B1579439 : Blo 413771 1579439 := bstep (se 1 (by rfl) ⟨1184579, by rfl⟩ : syracuseStep 1579439 = 2369159) B2369159
theorem B1055369 : Blo 413771 1055369 := bstep (se 2 (by rfl) ⟨395763, by rfl⟩ : syracuseStep 1055369 = 791527) B791527
theorem B1514137 : Blo 413771 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B1055713 : Blo 413771 1055713 := bstep (se 2 (by rfl) ⟨395892, by rfl⟩ : syracuseStep 1055713 = 791785) B791785
theorem B1056503 : Blo 413771 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B499495 : Blo 413771 499495 := bstep (se 1 (by rfl) ⟨374621, by rfl⟩ : syracuseStep 499495 = 749243) B749243
theorem B1056635 : Blo 413771 1056635 := bstep (se 1 (by rfl) ⟨792476, by rfl⟩ : syracuseStep 1056635 = 1584953) B1584953
theorem B1057121 : Blo 413771 1057121 := bstep (se 2 (by rfl) ⟨396420, by rfl⟩ : syracuseStep 1057121 = 792841) B792841
theorem B664571 : Blo 413771 664571 := bstep (se 1 (by rfl) ⟨498428, by rfl⟩ : syracuseStep 664571 = 996857) B996857
theorem B468031 : Blo 413771 468031 := bstep (se 1 (by rfl) ⟨351023, by rfl⟩ : syracuseStep 468031 = 702047) B702047
theorem B468175 : Blo 413771 468175 := bstep (se 1 (by rfl) ⟨351131, by rfl⟩ : syracuseStep 468175 = 702263) B702263
theorem B3548407 : Blo 413771 3548407 := bstep (se 1 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 3548407 = 5322611) B5322611
theorem B1222141 : Blo 413771 1222141 := bstep (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) B458303
theorem B5973587 : Blo 413771 5973587 := bstep (se 1 (by rfl) ⟨4480190, by rfl⟩ : syracuseStep 5973587 = 8960381) B8960381
theorem B1123951 : Blo 413771 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B1124059 : Blo 413771 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B1582811 : Blo 413771 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B469147 : Blo 413771 469147 := bstep (se 1 (by rfl) ⟨351860, by rfl⟩ : syracuseStep 469147 = 703721) B703721
theorem B469183 : Blo 413771 469183 := bstep (se 1 (by rfl) ⟨351887, by rfl⟩ : syracuseStep 469183 = 703775) B703775
theorem B698665 : Blo 413771 698665 := bstep (se 2 (by rfl) ⟨261999, by rfl⟩ : syracuseStep 698665 = 523999) B523999
theorem B57387325 : Blo 413771 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B3419435 : Blo 413771 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B5058121 : Blo 413771 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B699995 : Blo 413771 699995 := bstep (se 1 (by rfl) ⟨524996, by rfl⟩ : syracuseStep 699995 = 1049993) B1049993
theorem B5680801 : Blo 413771 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B700231 : Blo 413771 700231 := bstep (se 1 (by rfl) ⟨525173, by rfl⟩ : syracuseStep 700231 = 1050347) B1050347
theorem B4272095 : Blo 413771 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B2109563 : Blo 413771 2109563 := bstep (se 1 (by rfl) ⟨1582172, by rfl⟩ : syracuseStep 2109563 = 3164345) B3164345
theorem B1421501 : Blo 413771 1421501 := bstep (se 3 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 1421501 = 533063) B533063
theorem B2109725 : Blo 413771 2109725 := bstep (se 3 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 2109725 = 791147) B791147
theorem B2666843 : Blo 413771 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B8532377 : Blo 413771 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B700879 : Blo 413771 700879 := bstep (se 1 (by rfl) ⟨525659, by rfl⟩ : syracuseStep 700879 = 1051319) B1051319
theorem B21672805 : Blo 413771 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B701615 : Blo 413771 701615 := bstep (se 1 (by rfl) ⟨526211, by rfl⟩ : syracuseStep 701615 = 1052423) B1052423
theorem B701851 : Blo 413771 701851 := bstep (se 1 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 701851 = 1052777) B1052777
theorem B931499 : Blo 413771 931499 := bstep (se 1 (by rfl) ⟨698624, by rfl⟩ : syracuseStep 931499 = 1397249) B1397249
theorem B702175 : Blo 413771 702175 := bstep (se 1 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 702175 = 1053263) B1053263
theorem B2373533 : Blo 413771 2373533 := bstep (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) B890075
theorem B931823 : Blo 413771 931823 := bstep (se 1 (by rfl) ⟨698867, by rfl⟩ : syracuseStep 931823 = 1397735) B1397735
theorem B702607 : Blo 413771 702607 := bstep (se 1 (by rfl) ⟨526955, by rfl⟩ : syracuseStep 702607 = 1053911) B1053911
theorem B932039 : Blo 413771 932039 := bstep (se 1 (by rfl) ⟨699029, by rfl⟩ : syracuseStep 932039 = 1398059) B1398059
theorem B2537839 : Blo 413771 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B932219 : Blo 413771 932219 := bstep (se 1 (by rfl) ⟨699164, by rfl⟩ : syracuseStep 932219 = 1398329) B1398329
theorem B932489 : Blo 413771 932489 := bstep (se 2 (by rfl) ⟨349683, by rfl⟩ : syracuseStep 932489 = 699367) B699367
theorem B703559 : Blo 413771 703559 := bstep (se 1 (by rfl) ⟨527669, by rfl⟩ : syracuseStep 703559 = 1055339) B1055339
theorem B2112641 : Blo 413771 2112641 := bstep (se 2 (by rfl) ⟨792240, by rfl⟩ : syracuseStep 2112641 = 1584481) B1584481
theorem B933047 : Blo 413771 933047 := bstep (se 1 (by rfl) ⟨699785, by rfl⟩ : syracuseStep 933047 = 1399571) B1399571
theorem B703991 : Blo 413771 703991 := bstep (se 1 (by rfl) ⟨527993, by rfl⟩ : syracuseStep 703991 = 1055987) B1055987
theorem B933623 : Blo 413771 933623 := bstep (se 1 (by rfl) ⟨700217, by rfl⟩ : syracuseStep 933623 = 1400435) B1400435
theorem B2244439 : Blo 413771 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B3784573 : Blo 413771 3784573 := bstep (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) B1419215
theorem B933803 : Blo 413771 933803 := bstep (se 1 (by rfl) ⟨700352, by rfl⟩ : syracuseStep 933803 = 1400705) B1400705
theorem B2113451 : Blo 413771 2113451 := bstep (se 1 (by rfl) ⟨1585088, by rfl⟩ : syracuseStep 2113451 = 3170177) B3170177
theorem B3031319 : Blo 413771 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B934343 : Blo 413771 934343 := bstep (se 1 (by rfl) ⟨700757, by rfl⟩ : syracuseStep 934343 = 1401515) B1401515
theorem B934703 : Blo 413771 934703 := bstep (se 1 (by rfl) ⟨701027, by rfl⟩ : syracuseStep 934703 = 1402055) B1402055
theorem B2114423 : Blo 413771 2114423 := bstep (se 1 (by rfl) ⟨1585817, by rfl⟩ : syracuseStep 2114423 = 3171635) B3171635
theorem B1328015 : Blo 413771 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B672875 : Blo 413771 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B2671967 : Blo 413771 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B1197787 : Blo 413771 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B935711 : Blo 413771 935711 := bstep (se 1 (by rfl) ⟨701783, by rfl⟩ : syracuseStep 935711 = 1403567) B1403567
theorem B1492937 : Blo 413771 1492937 := bstep (se 2 (by rfl) ⟨559851, by rfl⟩ : syracuseStep 1492937 = 1119703) B1119703
theorem B935927 : Blo 413771 935927 := bstep (se 1 (by rfl) ⟨701945, by rfl⟩ : syracuseStep 935927 = 1403891) B1403891
theorem B414566423 : Blo 413771 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B936287 : Blo 413771 936287 := bstep (se 1 (by rfl) ⟨702215, by rfl⟩ : syracuseStep 936287 = 1404431) B1404431
theorem B17713835 : Blo 413771 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B2378591 : Blo 413771 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B674795 : Blo 413771 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B937007 : Blo 413771 937007 := bstep (se 1 (by rfl) ⟨702755, by rfl⟩ : syracuseStep 937007 = 1405511) B1405511
theorem B1002719 : Blo 413771 1002719 := bstep (se 1 (by rfl) ⟨752039, by rfl⟩ : syracuseStep 1002719 = 1504079) B1504079
theorem B937295 : Blo 413771 937295 := bstep (se 1 (by rfl) ⟨702971, by rfl⟩ : syracuseStep 937295 = 1405943) B1405943
theorem B1068457 : Blo 413771 1068457 := bstep (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) B801343
theorem B937385 : Blo 413771 937385 := bstep (se 2 (by rfl) ⟨351519, by rfl⟩ : syracuseStep 937385 = 703039) B703039
theorem B3165803 : Blo 413771 3165803 := bstep (se 1 (by rfl) ⟨2374352, by rfl⟩ : syracuseStep 3165803 = 4748705) B4748705
theorem B1396601 : Blo 413771 1396601 := bstep (se 2 (by rfl) ⟨523725, by rfl⟩ : syracuseStep 1396601 = 1047451) B1047451
theorem B708473 : Blo 413771 708473 := bstep (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) B531355
theorem B937871 : Blo 413771 937871 := bstep (se 1 (by rfl) ⟨703403, by rfl⟩ : syracuseStep 937871 = 1406807) B1406807
theorem B27086885 : Blo 413771 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B1396925 : Blo 413771 1396925 := bstep (se 3 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 1396925 = 523847) B523847
theorem B413927 : Blo 413771 413927 := bstep (se 1 (by rfl) ⟨310445, by rfl⟩ : syracuseStep 413927 = 620891) B620891
theorem B7721249 : Blo 413771 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B414079 : Blo 413771 414079 := bstep (se 1 (by rfl) ⟨310559, by rfl⟩ : syracuseStep 414079 = 621119) B621119
theorem B1200511 : Blo 413771 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B414159 : Blo 413771 414159 := bstep (se 1 (by rfl) ⟨310619, by rfl⟩ : syracuseStep 414159 = 621239) B621239
theorem B938591 : Blo 413771 938591 := bstep (se 1 (by rfl) ⟨703943, by rfl⟩ : syracuseStep 938591 = 1407887) B1407887
theorem B414311 : Blo 413771 414311 := bstep (se 1 (by rfl) ⟨310733, by rfl⟩ : syracuseStep 414311 = 621467) B621467
theorem B3986081 : Blo 413771 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B1331873 : Blo 413771 1331873 := bstep (se 2 (by rfl) ⟨499452, by rfl⟩ : syracuseStep 1331873 = 998905) B998905
theorem B414575 : Blo 413771 414575 := bstep (se 1 (by rfl) ⟨310931, by rfl⟩ : syracuseStep 414575 = 621863) B621863
theorem B414631 : Blo 413771 414631 := bstep (se 1 (by rfl) ⟨310973, by rfl⟩ : syracuseStep 414631 = 621947) B621947
theorem B414715 : Blo 413771 414715 := bstep (se 1 (by rfl) ⟨311036, by rfl⟩ : syracuseStep 414715 = 622073) B622073
theorem B1266683 : Blo 413771 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B414783 : Blo 413771 414783 := bstep (se 1 (by rfl) ⟨311087, by rfl⟩ : syracuseStep 414783 = 622175) B622175
theorem B414927 : Blo 413771 414927 := bstep (se 1 (by rfl) ⟨311195, by rfl⟩ : syracuseStep 414927 = 622391) B622391
theorem B1398113 : Blo 413771 1398113 := bstep (se 2 (by rfl) ⟨524292, by rfl⟩ : syracuseStep 1398113 = 1048585) B1048585
theorem B415131 : Blo 413771 415131 := bstep (se 1 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 415131 = 622697) B622697
theorem B939419 : Blo 413771 939419 := bstep (se 1 (by rfl) ⟨704564, by rfl⟩ : syracuseStep 939419 = 1409129) B1409129
theorem B415343 : Blo 413771 415343 := bstep (se 1 (by rfl) ⟨311507, by rfl⟩ : syracuseStep 415343 = 623015) B623015
theorem B415399 : Blo 413771 415399 := bstep (se 1 (by rfl) ⟨311549, by rfl⟩ : syracuseStep 415399 = 623099) B623099
theorem B415483 : Blo 413771 415483 := bstep (se 1 (by rfl) ⟨311612, by rfl⟩ : syracuseStep 415483 = 623225) B623225
theorem B1267451 : Blo 413771 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B415519 : Blo 413771 415519 := bstep (se 1 (by rfl) ⟨311639, by rfl⟩ : syracuseStep 415519 = 623279) B623279
theorem B415551 : Blo 413771 415551 := bstep (se 1 (by rfl) ⟨311663, by rfl⟩ : syracuseStep 415551 = 623327) B623327
theorem B415727 : Blo 413771 415727 := bstep (se 1 (by rfl) ⟨311795, by rfl⟩ : syracuseStep 415727 = 623591) B623591
theorem B415899 : Blo 413771 415899 := bstep (se 1 (by rfl) ⟨311924, by rfl⟩ : syracuseStep 415899 = 623849) B623849
theorem B415935 : Blo 413771 415935 := bstep (se 1 (by rfl) ⟨311951, by rfl⟩ : syracuseStep 415935 = 623903) B623903
theorem B416047 : Blo 413771 416047 := bstep (se 1 (by rfl) ⟨312035, by rfl⟩ : syracuseStep 416047 = 624071) B624071
theorem B2709883 : Blo 413771 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B416283 : Blo 413771 416283 := bstep (se 1 (by rfl) ⟨312212, by rfl⟩ : syracuseStep 416283 = 624425) B624425
theorem B416287 : Blo 413771 416287 := bstep (se 1 (by rfl) ⟨312215, by rfl⟩ : syracuseStep 416287 = 624431) B624431
theorem B5691977 : Blo 413771 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B5069449 : Blo 413771 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B416603 : Blo 413771 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B416671 : Blo 413771 416671 := bstep (se 1 (by rfl) ⟨312503, by rfl⟩ : syracuseStep 416671 = 625007) B625007
theorem B416815 : Blo 413771 416815 := bstep (se 1 (by rfl) ⟨312611, by rfl⟩ : syracuseStep 416815 = 625223) B625223
theorem B416839 : Blo 413771 416839 := bstep (se 1 (by rfl) ⟨312629, by rfl⟩ : syracuseStep 416839 = 625259) B625259
theorem B416991 : Blo 413771 416991 := bstep (se 1 (by rfl) ⟨312743, by rfl⟩ : syracuseStep 416991 = 625487) B625487
theorem B1400057 : Blo 413771 1400057 := bstep (se 2 (by rfl) ⟨525021, by rfl⟩ : syracuseStep 1400057 = 1050043) B1050043
theorem B1989983 : Blo 413771 1989983 := bstep (se 1 (by rfl) ⟨1492487, by rfl⟩ : syracuseStep 1989983 = 2984975) B2984975
theorem B417255 : Blo 413771 417255 := bstep (se 1 (by rfl) ⟨312941, by rfl⟩ : syracuseStep 417255 = 625883) B625883
theorem B1400327 : Blo 413771 1400327 := bstep (se 1 (by rfl) ⟨1050245, by rfl⟩ : syracuseStep 1400327 = 2100491) B2100491
theorem B417371 : Blo 413771 417371 := bstep (se 1 (by rfl) ⟨313028, by rfl⟩ : syracuseStep 417371 = 626057) B626057
theorem B417607 : Blo 413771 417607 := bstep (se 1 (by rfl) ⟨313205, by rfl⟩ : syracuseStep 417607 = 626411) B626411
theorem B4087741 : Blo 413771 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B417759 : Blo 413771 417759 := bstep (se 1 (by rfl) ⟨313319, by rfl⟩ : syracuseStep 417759 = 626639) B626639
theorem B1401407 : Blo 413771 1401407 := bstep (se 1 (by rfl) ⟨1051055, by rfl⟩ : syracuseStep 1401407 = 2102111) B2102111
theorem B3433637 : Blo 413771 3433637 := bstep (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) B643807
theorem B3008015 : Blo 413771 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B2254387 : Blo 413771 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B1402703 : Blo 413771 1402703 := bstep (se 1 (by rfl) ⟨1052027, by rfl⟩ : syracuseStep 1402703 = 2104055) B2104055
theorem B1403027 : Blo 413771 1403027 := bstep (se 1 (by rfl) ⟨1052270, by rfl⟩ : syracuseStep 1403027 = 2104541) B2104541
theorem B1403297 : Blo 413771 1403297 := bstep (se 2 (by rfl) ⟨526236, by rfl⟩ : syracuseStep 1403297 = 1052473) B1052473
theorem B846523 : Blo 413771 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B3992267 : Blo 413771 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B1994635 : Blo 413771 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B2551931 : Blo 413771 2551931 := bstep (se 1 (by rfl) ⟨1913948, by rfl⟩ : syracuseStep 2551931 = 3827897) B3827897
theorem B5337373 : Blo 413771 5337373 := bstep (se 3 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 5337373 = 2001515) B2001515
theorem B9007433 : Blo 413771 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B1405295 : Blo 413771 1405295 := bstep (se 1 (by rfl) ⟨1053971, by rfl⟩ : syracuseStep 1405295 = 2107943) B2107943
theorem B750799 : Blo 413771 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B3142961 : Blo 413771 3142961 := bstep (se 2 (by rfl) ⟨1178610, by rfl⟩ : syracuseStep 3142961 = 2357221) B2357221
theorem B1406699 : Blo 413771 1406699 := bstep (se 1 (by rfl) ⟨1055024, by rfl⟩ : syracuseStep 1406699 = 2110049) B2110049
theorem B2357039 : Blo 413771 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B751607 : Blo 413771 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B1406969 : Blo 413771 1406969 := bstep (se 2 (by rfl) ⟨527613, by rfl⟩ : syracuseStep 1406969 = 1055227) B1055227
theorem B1898639 : Blo 413771 1898639 := bstep (se 1 (by rfl) ⟨1423979, by rfl⟩ : syracuseStep 1898639 = 2847959) B2847959
theorem B620699 : Blo 413771 620699 := bstep (se 1 (by rfl) ⟨465524, by rfl⟩ : syracuseStep 620699 = 931049) B931049
theorem B1407131 : Blo 413771 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B620735 : Blo 413771 620735 := bstep (se 1 (by rfl) ⟨465551, by rfl⟩ : syracuseStep 620735 = 931103) B931103
theorem B620777 : Blo 413771 620777 := bstep (se 2 (by rfl) ⟨232791, by rfl⟩ : syracuseStep 620777 = 465583) B465583
theorem B1407239 : Blo 413771 1407239 := bstep (se 1 (by rfl) ⟨1055429, by rfl⟩ : syracuseStep 1407239 = 2110859) B2110859
theorem B2095469 : Blo 413771 2095469 := bstep (se 3 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 2095469 = 785801) B785801
theorem B2357747 : Blo 413771 2357747 := bstep (se 1 (by rfl) ⟨1768310, by rfl⟩ : syracuseStep 2357747 = 3536621) B3536621
theorem B621083 : Blo 413771 621083 := bstep (se 1 (by rfl) ⟨465812, by rfl⟩ : syracuseStep 621083 = 931625) B931625
theorem B621161 : Blo 413771 621161 := bstep (se 2 (by rfl) ⟨232935, by rfl⟩ : syracuseStep 621161 = 465871) B465871
theorem B1571663 : Blo 413771 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B1047401 : Blo 413771 1047401 := bstep (se 2 (by rfl) ⟨392775, by rfl⟩ : syracuseStep 1047401 = 785551) B785551
theorem B1047593 : Blo 413771 1047593 := bstep (se 2 (by rfl) ⟨392847, by rfl⟩ : syracuseStep 1047593 = 785695) B785695
theorem B621689 : Blo 413771 621689 := bstep (se 2 (by rfl) ⟨233133, by rfl⟩ : syracuseStep 621689 = 466267) B466267
theorem B2555009 : Blo 413771 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B2522269 : Blo 413771 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B621791 : Blo 413771 621791 := bstep (se 1 (by rfl) ⟨466343, by rfl⟩ : syracuseStep 621791 = 932687) B932687
theorem B1899769 : Blo 413771 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B621833 : Blo 413771 621833 := bstep (se 2 (by rfl) ⟨233187, by rfl⟩ : syracuseStep 621833 = 466375) B466375
theorem B1408265 : Blo 413771 1408265 := bstep (se 2 (by rfl) ⟨528099, by rfl⟩ : syracuseStep 1408265 = 1056199) B1056199
theorem B7077131 : Blo 413771 7077131 := bstep (se 1 (by rfl) ⟨5307848, by rfl⟩ : syracuseStep 7077131 = 10615697) B10615697
theorem B1178975 : Blo 413771 1178975 := bstep (se 1 (by rfl) ⟨884231, by rfl⟩ : syracuseStep 1178975 = 1768463) B1768463
theorem B621935 : Blo 413771 621935 := bstep (se 1 (by rfl) ⟨466451, by rfl⟩ : syracuseStep 621935 = 932903) B932903
theorem B622055 : Blo 413771 622055 := bstep (se 1 (by rfl) ⟨466541, by rfl⟩ : syracuseStep 622055 = 933083) B933083
theorem B622187 : Blo 413771 622187 := bstep (se 1 (by rfl) ⟨466640, by rfl⟩ : syracuseStep 622187 = 933281) B933281
theorem B1769147 : Blo 413771 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B622313 : Blo 413771 622313 := bstep (se 2 (by rfl) ⟨233367, by rfl⟩ : syracuseStep 622313 = 466735) B466735
theorem B622457 : Blo 413771 622457 := bstep (se 2 (by rfl) ⟨233421, by rfl⟩ : syracuseStep 622457 = 466843) B466843
theorem B622559 : Blo 413771 622559 := bstep (se 1 (by rfl) ⟨466919, by rfl⟩ : syracuseStep 622559 = 933839) B933839
theorem B786667 : Blo 413771 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B622895 : Blo 413771 622895 := bstep (se 1 (by rfl) ⟨467171, by rfl⟩ : syracuseStep 622895 = 934343) B934343
theorem B623135 : Blo 413771 623135 := bstep (se 1 (by rfl) ⟨467351, by rfl⟩ : syracuseStep 623135 = 934703) B934703
theorem B2097737 : Blo 413771 2097737 := bstep (se 2 (by rfl) ⟨786651, by rfl⟩ : syracuseStep 2097737 = 1573303) B1573303
theorem B1409615 : Blo 413771 1409615 := bstep (se 1 (by rfl) ⟨1057211, by rfl⟩ : syracuseStep 1409615 = 2114423) B2114423
theorem B1049183 : Blo 413771 1049183 := bstep (se 1 (by rfl) ⟨786887, by rfl⟩ : syracuseStep 1049183 = 1573775) B1573775
theorem B885343 : Blo 413771 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B3146363 : Blo 413771 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B623807 : Blo 413771 623807 := bstep (se 1 (by rfl) ⟨467855, by rfl⟩ : syracuseStep 623807 = 935711) B935711
theorem B2098385 : Blo 413771 2098385 := bstep (se 2 (by rfl) ⟨786894, by rfl⟩ : syracuseStep 2098385 = 1573789) B1573789
theorem B1049881 : Blo 413771 1049881 := bstep (se 2 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 1049881 = 787411) B787411
theorem B591151 : Blo 413771 591151 := bstep (se 1 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 591151 = 886727) B886727
theorem B623951 : Blo 413771 623951 := bstep (se 1 (by rfl) ⟨467963, by rfl⟩ : syracuseStep 623951 = 935927) B935927
theorem B624041 : Blo 413771 624041 := bstep (se 2 (by rfl) ⟨234015, by rfl⟩ : syracuseStep 624041 = 468031) B468031
theorem B25691681 : Blo 413771 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B624191 : Blo 413771 624191 := bstep (se 1 (by rfl) ⟨468143, by rfl⟩ : syracuseStep 624191 = 936287) B936287
theorem B624233 : Blo 413771 624233 := bstep (se 2 (by rfl) ⟨234087, by rfl⟩ : syracuseStep 624233 = 468175) B468175
theorem B624671 : Blo 413771 624671 := bstep (se 1 (by rfl) ⟨468503, by rfl⟩ : syracuseStep 624671 = 937007) B937007
theorem B624863 : Blo 413771 624863 := bstep (se 1 (by rfl) ⟨468647, by rfl⟩ : syracuseStep 624863 = 937295) B937295
theorem B624923 : Blo 413771 624923 := bstep (se 1 (by rfl) ⟨468692, by rfl⟩ : syracuseStep 624923 = 937385) B937385
theorem B1902943 : Blo 413771 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B1771915 : Blo 413771 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B625247 : Blo 413771 625247 := bstep (se 1 (by rfl) ⟨468935, by rfl⟩ : syracuseStep 625247 = 937871) B937871
theorem B3541643 : Blo 413771 3541643 := bstep (se 1 (by rfl) ⟨2656232, by rfl⟩ : syracuseStep 3541643 = 5312465) B5312465
theorem B1772189 : Blo 413771 1772189 := bstep (se 3 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 1772189 = 664571) B664571
theorem B3377821 : Blo 413771 3377821 := bstep (se 3 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 3377821 = 1266683) B1266683
theorem B18057923 : Blo 413771 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B1575719 : Blo 413771 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B527143 : Blo 413771 527143 := bstep (se 1 (by rfl) ⟨395357, by rfl⟩ : syracuseStep 527143 = 790715) B790715
theorem B625529 : Blo 413771 625529 := bstep (se 2 (by rfl) ⟨234573, by rfl⟩ : syracuseStep 625529 = 469147) B469147
theorem B625577 : Blo 413771 625577 := bstep (se 2 (by rfl) ⟨234591, by rfl⟩ : syracuseStep 625577 = 469183) B469183
theorem B625727 : Blo 413771 625727 := bstep (se 1 (by rfl) ⟨469295, by rfl⟩ : syracuseStep 625727 = 938591) B938591
theorem B76516433 : Blo 413771 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B2657387 : Blo 413771 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B887915 : Blo 413771 887915 := bstep (se 1 (by rfl) ⟨665936, by rfl⟩ : syracuseStep 887915 = 1331873) B1331873
theorem B527467 : Blo 413771 527467 := bstep (se 1 (by rfl) ⟨395600, by rfl⟩ : syracuseStep 527467 = 791201) B791201
theorem B789887 : Blo 413771 789887 := bstep (se 1 (by rfl) ⟨592415, by rfl⟩ : syracuseStep 789887 = 1184831) B1184831
theorem B27037061 : Blo 413771 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B1052129 : Blo 413771 1052129 := bstep (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) B789097
theorem B2100815 : Blo 413771 2100815 := bstep (se 1 (by rfl) ⟨1575611, by rfl⟩ : syracuseStep 2100815 = 3151223) B3151223
theorem B626279 : Blo 413771 626279 := bstep (se 1 (by rfl) ⟨469709, by rfl⟩ : syracuseStep 626279 = 939419) B939419
theorem B1576691 : Blo 413771 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B4722461 : Blo 413771 4722461 := bstep (se 3 (by rfl) ⟨885461, by rfl⟩ : syracuseStep 4722461 = 1770923) B1770923
theorem B528439 : Blo 413771 528439 := bstep (se 1 (by rfl) ⟨396329, by rfl⟩ : syracuseStep 528439 = 792659) B792659
theorem B790631 : Blo 413771 790631 := bstep (se 1 (by rfl) ⟨592973, by rfl⟩ : syracuseStep 790631 = 1185947) B1185947
theorem B1052959 : Blo 413771 1052959 := bstep (se 1 (by rfl) ⟨789719, by rfl⟩ : syracuseStep 1052959 = 1579439) B1579439
theorem B1577465 : Blo 413771 1577465 := bstep (se 2 (by rfl) ⟨591549, by rfl⟩ : syracuseStep 1577465 = 1183099) B1183099
theorem B7574401 : Blo 413771 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B2659513 : Blo 413771 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B7116497 : Blo 413771 7116497 := bstep (se 2 (by rfl) ⟨2668686, by rfl⟩ : syracuseStep 7116497 = 5337373) B5337373
theorem B1578953 : Blo 413771 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B2005343 : Blo 413771 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B4004261 : Blo 413771 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B1055207 : Blo 413771 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B2661511 : Blo 413771 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B466663 : Blo 413771 466663 := bstep (se 1 (by rfl) ⟨349997, by rfl⟩ : syracuseStep 466663 = 699995) B699995
theorem B1580897 : Blo 413771 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B6004955 : Blo 413771 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B1777895 : Blo 413771 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B3383785 : Blo 413771 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B3613177 : Blo 413771 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B9118493 : Blo 413771 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B467743 : Blo 413771 467743 := bstep (se 1 (by rfl) ⟨350807, by rfl⟩ : syracuseStep 467743 = 701615) B701615
theorem B1582355 : Blo 413771 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B501071 : Blo 413771 501071 := bstep (se 1 (by rfl) ⟨375803, by rfl⟩ : syracuseStep 501071 = 751607) B751607
theorem B2533025 : Blo 413771 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B11970341 : Blo 413771 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B698267 : Blo 413771 698267 := bstep (se 1 (by rfl) ⟨523700, by rfl⟩ : syracuseStep 698267 = 1047401) B1047401
theorem B698395 : Blo 413771 698395 := bstep (se 1 (by rfl) ⟨523796, by rfl⟩ : syracuseStep 698395 = 1047593) B1047593
theorem B469039 : Blo 413771 469039 := bstep (se 1 (by rfl) ⟨351779, by rfl⟩ : syracuseStep 469039 = 703559) B703559
theorem B469327 : Blo 413771 469327 := bstep (se 1 (by rfl) ⟨351995, by rfl⟩ : syracuseStep 469327 = 703991) B703991
theorem B665993 : Blo 413771 665993 := bstep (se 2 (by rfl) ⟨249747, by rfl⟩ : syracuseStep 665993 = 499495) B499495
theorem B5450321 : Blo 413771 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B2993395 : Blo 413771 2993395 := bstep (se 1 (by rfl) ⟨2245046, by rfl⟩ : syracuseStep 2993395 = 4490093) B4490093
theorem B20589997 : Blo 413771 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B1945223 : Blo 413771 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B995291 : Blo 413771 995291 := bstep (se 1 (by rfl) ⟨746468, by rfl⟩ : syracuseStep 995291 = 1492937) B1492937
theorem B276377615 : Blo 413771 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B4731209 : Blo 413771 4731209 := bstep (se 2 (by rfl) ⟨1774203, by rfl⟩ : syracuseStep 4731209 = 3548407) B3548407
theorem B11809223 : Blo 413771 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B1585727 : Blo 413771 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B6402725 : Blo 413771 6402725 := bstep (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) B1200511
theorem B1684435 : Blo 413771 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B2110535 : Blo 413771 2110535 := bstep (se 1 (by rfl) ⟨1582901, by rfl⟩ : syracuseStep 2110535 = 3165803) B3165803
theorem B931067 : Blo 413771 931067 := bstep (se 1 (by rfl) ⟨698300, by rfl⟩ : syracuseStep 931067 = 1396601) B1396601
theorem B7615853 : Blo 413771 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B2995643 : Blo 413771 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B3159485 : Blo 413771 3159485 := bstep (se 3 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 3159485 = 1184807) B1184807
theorem B931283 : Blo 413771 931283 := bstep (se 1 (by rfl) ⟨698462, by rfl⟩ : syracuseStep 931283 = 1396925) B1396925
theorem B931553 : Blo 413771 931553 := bstep (se 2 (by rfl) ⟨349332, by rfl⟩ : syracuseStep 931553 = 698665) B698665
theorem B2668585 : Blo 413771 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B702695 : Blo 413771 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B932075 : Blo 413771 932075 := bstep (se 1 (by rfl) ⟨699056, by rfl⟩ : syracuseStep 932075 = 1398113) B1398113
theorem B1128697 : Blo 413771 1128697 := bstep (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) B846523
theorem B7125245 : Blo 413771 7125245 := bstep (se 3 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 7125245 = 2671967) B2671967
theorem B11385157 : Blo 413771 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B703579 : Blo 413771 703579 := bstep (se 1 (by rfl) ⟨527684, by rfl⟩ : syracuseStep 703579 = 1055369) B1055369
theorem B1424609 : Blo 413771 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B933371 : Blo 413771 933371 := bstep (se 1 (by rfl) ⟨700028, by rfl⟩ : syracuseStep 933371 = 1400057) B1400057
theorem B1326655 : Blo 413771 1326655 := bstep (se 1 (by rfl) ⟨994991, by rfl⟩ : syracuseStep 1326655 = 1989983) B1989983
theorem B933551 : Blo 413771 933551 := bstep (se 1 (by rfl) ⟨700163, by rfl⟩ : syracuseStep 933551 = 1400327) B1400327
theorem B933641 : Blo 413771 933641 := bstep (se 2 (by rfl) ⟨350115, by rfl⟩ : syracuseStep 933641 = 700231) B700231
theorem B704335 : Blo 413771 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B704423 : Blo 413771 704423 := bstep (se 1 (by rfl) ⟨528317, by rfl⟩ : syracuseStep 704423 = 1056635) B1056635
theorem B704747 : Blo 413771 704747 := bstep (se 1 (by rfl) ⟨528560, by rfl⟩ : syracuseStep 704747 = 1057121) B1057121
theorem B934271 : Blo 413771 934271 := bstep (se 1 (by rfl) ⟨700703, by rfl⟩ : syracuseStep 934271 = 1401407) B1401407
theorem B934505 : Blo 413771 934505 := bstep (se 2 (by rfl) ⟨350439, by rfl⟩ : syracuseStep 934505 = 700879) B700879
theorem B13452101 : Blo 413771 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B3982391 : Blo 413771 3982391 := bstep (se 1 (by rfl) ⟨2986793, by rfl⟩ : syracuseStep 3982391 = 5973587) B5973587
theorem B935135 : Blo 413771 935135 := bstep (se 1 (by rfl) ⟨701351, by rfl⟩ : syracuseStep 935135 = 1402703) B1402703
theorem B935351 : Blo 413771 935351 := bstep (se 1 (by rfl) ⟨701513, by rfl⟩ : syracuseStep 935351 = 1403027) B1403027
theorem B935531 : Blo 413771 935531 := bstep (se 1 (by rfl) ⟨701648, by rfl⟩ : syracuseStep 935531 = 1403297) B1403297
theorem B935801 : Blo 413771 935801 := bstep (se 2 (by rfl) ⟨350925, by rfl⟩ : syracuseStep 935801 = 701851) B701851
theorem B936233 : Blo 413771 936233 := bstep (se 2 (by rfl) ⟨351087, by rfl⟩ : syracuseStep 936233 = 702175) B702175
theorem B3590729 : Blo 413771 3590729 := bstep (se 2 (by rfl) ⟨1346523, by rfl⟩ : syracuseStep 3590729 = 2693047) B2693047
theorem B936809 : Blo 413771 936809 := bstep (se 2 (by rfl) ⟨351303, by rfl⟩ : syracuseStep 936809 = 702607) B702607
theorem B936863 : Blo 413771 936863 := bstep (se 1 (by rfl) ⟨702647, by rfl⟩ : syracuseStep 936863 = 1405295) B1405295
theorem B5688251 : Blo 413771 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B2673917 : Blo 413771 2673917 := bstep (se 3 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 2673917 = 1002719) B1002719
theorem B2018849 : Blo 413771 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B937799 : Blo 413771 937799 := bstep (se 1 (by rfl) ⟨703349, by rfl⟩ : syracuseStep 937799 = 1406699) B1406699
theorem B937979 : Blo 413771 937979 := bstep (se 1 (by rfl) ⟨703484, by rfl⟩ : syracuseStep 937979 = 1406969) B1406969
theorem B1265759 : Blo 413771 1265759 := bstep (se 1 (by rfl) ⟨949319, by rfl⟩ : syracuseStep 1265759 = 1898639) B1898639
theorem B413799 : Blo 413771 413799 := bstep (se 1 (by rfl) ⟨310349, by rfl⟩ : syracuseStep 413799 = 620699) B620699
theorem B938087 : Blo 413771 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B413823 : Blo 413771 413823 := bstep (se 1 (by rfl) ⟨310367, by rfl⟩ : syracuseStep 413823 = 620735) B620735
theorem B413851 : Blo 413771 413851 := bstep (se 1 (by rfl) ⟨310388, by rfl⟩ : syracuseStep 413851 = 620777) B620777
theorem B938159 : Blo 413771 938159 := bstep (se 1 (by rfl) ⟨703619, by rfl⟩ : syracuseStep 938159 = 1407239) B1407239
theorem B1396979 : Blo 413771 1396979 := bstep (se 1 (by rfl) ⟨1047734, by rfl⟩ : syracuseStep 1396979 = 2095469) B2095469
theorem B414055 : Blo 413771 414055 := bstep (se 1 (by rfl) ⟨310541, by rfl⟩ : syracuseStep 414055 = 621083) B621083
theorem B414107 : Blo 413771 414107 := bstep (se 1 (by rfl) ⟨310580, by rfl⟩ : syracuseStep 414107 = 621161) B621161
theorem B414459 : Blo 413771 414459 := bstep (se 1 (by rfl) ⟨310844, by rfl⟩ : syracuseStep 414459 = 621689) B621689
theorem B414527 : Blo 413771 414527 := bstep (se 1 (by rfl) ⟨310895, by rfl⟩ : syracuseStep 414527 = 621791) B621791
theorem B414555 : Blo 413771 414555 := bstep (se 1 (by rfl) ⟨310916, by rfl⟩ : syracuseStep 414555 = 621833) B621833
theorem B938843 : Blo 413771 938843 := bstep (se 1 (by rfl) ⟨704132, by rfl⟩ : syracuseStep 938843 = 1408265) B1408265
theorem B414623 : Blo 413771 414623 := bstep (se 1 (by rfl) ⟨310967, by rfl⟩ : syracuseStep 414623 = 621935) B621935
theorem B1889261 : Blo 413771 1889261 := bstep (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) B708473
theorem B414703 : Blo 413771 414703 := bstep (se 1 (by rfl) ⟨311027, by rfl⟩ : syracuseStep 414703 = 622055) B622055
theorem B414791 : Blo 413771 414791 := bstep (se 1 (by rfl) ⟨311093, by rfl⟩ : syracuseStep 414791 = 622187) B622187
theorem B414875 : Blo 413771 414875 := bstep (se 1 (by rfl) ⟨311156, by rfl⟩ : syracuseStep 414875 = 622313) B622313
theorem B414971 : Blo 413771 414971 := bstep (se 1 (by rfl) ⟨311228, by rfl⟩ : syracuseStep 414971 = 622457) B622457
theorem B415039 : Blo 413771 415039 := bstep (se 1 (by rfl) ⟨311279, by rfl⟩ : syracuseStep 415039 = 622559) B622559
theorem B415207 : Blo 413771 415207 := bstep (se 1 (by rfl) ⟨311405, by rfl⟩ : syracuseStep 415207 = 622811) B622811
theorem B415215 : Blo 413771 415215 := bstep (se 1 (by rfl) ⟨311411, by rfl⟩ : syracuseStep 415215 = 622823) B622823
theorem B2020879 : Blo 413771 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B939599 : Blo 413771 939599 := bstep (se 1 (by rfl) ⟨704699, by rfl⟩ : syracuseStep 939599 = 1409399) B1409399
theorem B415323 : Blo 413771 415323 := bstep (se 1 (by rfl) ⟨311492, by rfl⟩ : syracuseStep 415323 = 622985) B622985
theorem B415387 : Blo 413771 415387 := bstep (se 1 (by rfl) ⟨311540, by rfl⟩ : syracuseStep 415387 = 623081) B623081
theorem B415471 : Blo 413771 415471 := bstep (se 1 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 415471 = 623207) B623207
theorem B1398599 : Blo 413771 1398599 := bstep (se 1 (by rfl) ⟨1048949, by rfl⟩ : syracuseStep 1398599 = 2097899) B2097899
theorem B415559 : Blo 413771 415559 := bstep (se 1 (by rfl) ⟨311669, by rfl⟩ : syracuseStep 415559 = 623339) B623339
theorem B415579 : Blo 413771 415579 := bstep (se 1 (by rfl) ⟨311684, by rfl⟩ : syracuseStep 415579 = 623369) B623369
theorem B415647 : Blo 413771 415647 := bstep (se 1 (by rfl) ⟨311735, by rfl⟩ : syracuseStep 415647 = 623471) B623471
theorem B448583 : Blo 413771 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B415815 : Blo 413771 415815 := bstep (se 1 (by rfl) ⟨311861, by rfl⟩ : syracuseStep 415815 = 623723) B623723
theorem B415975 : Blo 413771 415975 := bstep (se 1 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 415975 = 623963) B623963
theorem B416159 : Blo 413771 416159 := bstep (se 1 (by rfl) ⟨312119, by rfl⟩ : syracuseStep 416159 = 624239) B624239
theorem B416207 : Blo 413771 416207 := bstep (se 1 (by rfl) ⟨312155, by rfl⟩ : syracuseStep 416207 = 624311) B624311
theorem B416231 : Blo 413771 416231 := bstep (se 1 (by rfl) ⟨312173, by rfl⟩ : syracuseStep 416231 = 624347) B624347
theorem B416347 : Blo 413771 416347 := bstep (se 1 (by rfl) ⟨312260, by rfl⟩ : syracuseStep 416347 = 624521) B624521
theorem B416415 : Blo 413771 416415 := bstep (se 1 (by rfl) ⟨312311, by rfl⟩ : syracuseStep 416415 = 624623) B624623
theorem B416583 : Blo 413771 416583 := bstep (se 1 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 416583 = 624875) B624875
theorem B416623 : Blo 413771 416623 := bstep (se 1 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 416623 = 624935) B624935
theorem B416679 : Blo 413771 416679 := bstep (se 1 (by rfl) ⟨312509, by rfl⟩ : syracuseStep 416679 = 625019) B625019
theorem B1399787 : Blo 413771 1399787 := bstep (se 1 (by rfl) ⟨1049840, by rfl⟩ : syracuseStep 1399787 = 2099681) B2099681
theorem B416859 : Blo 413771 416859 := bstep (se 1 (by rfl) ⟨312644, by rfl⟩ : syracuseStep 416859 = 625289) B625289
theorem B416975 : Blo 413771 416975 := bstep (se 1 (by rfl) ⟨312731, by rfl⟩ : syracuseStep 416975 = 625463) B625463
theorem B416999 : Blo 413771 416999 := bstep (se 1 (by rfl) ⟨312749, by rfl⟩ : syracuseStep 416999 = 625499) B625499
theorem B15162677 : Blo 413771 15162677 := bstep (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) B1421501
theorem B417095 : Blo 413771 417095 := bstep (se 1 (by rfl) ⟨312821, by rfl⟩ : syracuseStep 417095 = 625643) B625643
theorem B1629521 : Blo 413771 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B3005849 : Blo 413771 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B417231 : Blo 413771 417231 := bstep (se 1 (by rfl) ⟨312923, by rfl⟩ : syracuseStep 417231 = 625847) B625847
theorem B1498601 : Blo 413771 1498601 := bstep (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) B1123951
theorem B417391 : Blo 413771 417391 := bstep (se 1 (by rfl) ⟨313043, by rfl⟩ : syracuseStep 417391 = 626087) B626087
theorem B1597049 : Blo 413771 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B1498745 : Blo 413771 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B417447 : Blo 413771 417447 := bstep (se 1 (by rfl) ⟨313085, by rfl⟩ : syracuseStep 417447 = 626171) B626171
theorem B417511 : Blo 413771 417511 := bstep (se 1 (by rfl) ⟨313133, by rfl⟩ : syracuseStep 417511 = 626267) B626267
theorem B417567 : Blo 413771 417567 := bstep (se 1 (by rfl) ⟨313175, by rfl⟩ : syracuseStep 417567 = 626351) B626351
theorem B417647 : Blo 413771 417647 := bstep (se 1 (by rfl) ⟨313235, by rfl⟩ : syracuseStep 417647 = 626471) B626471
theorem B417703 : Blo 413771 417703 := bstep (se 1 (by rfl) ⟨313277, by rfl⟩ : syracuseStep 417703 = 626555) B626555
theorem B5333273 : Blo 413771 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B1401299 : Blo 413771 1401299 := bstep (se 1 (by rfl) ⟨1050974, by rfl⟩ : syracuseStep 1401299 = 2101949) B2101949
theorem B7103375 : Blo 413771 7103375 := bstep (se 1 (by rfl) ⟨5327531, by rfl⟩ : syracuseStep 7103375 = 10655063) B10655063
theorem B844967 : Blo 413771 844967 := bstep (se 1 (by rfl) ⟨633725, by rfl⟩ : syracuseStep 844967 = 1267451) B1267451
theorem B6514057 : Blo 413771 6514057 := bstep (se 2 (by rfl) ⟨2442771, by rfl⟩ : syracuseStep 6514057 = 4885543) B4885543
theorem B5989783 : Blo 413771 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B3794651 : Blo 413771 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B6744161 : Blo 413771 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B2289091 : Blo 413771 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B28897073 : Blo 413771 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B1405025 : Blo 413771 1405025 := bstep (se 2 (by rfl) ⟨526884, by rfl⟩ : syracuseStep 1405025 = 1053769) B1053769
theorem B1799453 : Blo 413771 1799453 := bstep (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) B674795
theorem B2848063 : Blo 413771 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B1701287 : Blo 413771 1701287 := bstep (se 1 (by rfl) ⟨1275965, by rfl⟩ : syracuseStep 1701287 = 2551931) B2551931
theorem B1406375 : Blo 413771 1406375 := bstep (se 1 (by rfl) ⟨1054781, by rfl⟩ : syracuseStep 1406375 = 2109563) B2109563
theorem B1406483 : Blo 413771 1406483 := bstep (se 1 (by rfl) ⟨1054862, by rfl⟩ : syracuseStep 1406483 = 2109725) B2109725
theorem B2095307 : Blo 413771 2095307 := bstep (se 1 (by rfl) ⟨1571480, by rfl⟩ : syracuseStep 2095307 = 3142961) B3142961
theorem B3143933 : Blo 413771 3143933 := bstep (se 3 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 3143933 = 1178975) B1178975
theorem B620999 : Blo 413771 620999 := bstep (se 1 (by rfl) ⟨465749, by rfl⟩ : syracuseStep 620999 = 931499) B931499
theorem B1571359 : Blo 413771 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B1407617 : Blo 413771 1407617 := bstep (se 2 (by rfl) ⟨527856, by rfl⟩ : syracuseStep 1407617 = 1055713) B1055713
theorem B621215 : Blo 413771 621215 := bstep (se 1 (by rfl) ⟨465911, by rfl⟩ : syracuseStep 621215 = 931823) B931823
theorem B621359 : Blo 413771 621359 := bstep (se 1 (by rfl) ⟨466019, by rfl⟩ : syracuseStep 621359 = 932039) B932039
theorem B621479 : Blo 413771 621479 := bstep (se 1 (by rfl) ⟨466109, by rfl⟩ : syracuseStep 621479 = 932219) B932219
theorem B1571831 : Blo 413771 1571831 := bstep (se 1 (by rfl) ⟨1178873, by rfl⟩ : syracuseStep 1571831 = 2357747) B2357747
theorem B621659 : Blo 413771 621659 := bstep (se 1 (by rfl) ⟨466244, by rfl⟩ : syracuseStep 621659 = 932489) B932489
theorem B1047775 : Blo 413771 1047775 := bstep (se 1 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 1047775 = 1571663) B1571663
theorem B1703339 : Blo 413771 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B1408427 : Blo 413771 1408427 := bstep (se 1 (by rfl) ⟨1056320, by rfl⟩ : syracuseStep 1408427 = 2112641) B2112641
theorem B622031 : Blo 413771 622031 := bstep (se 1 (by rfl) ⟨466523, by rfl⟩ : syracuseStep 622031 = 933047) B933047
theorem B4718087 : Blo 413771 4718087 := bstep (se 1 (by rfl) ⟨3538565, by rfl⟩ : syracuseStep 4718087 = 7077131) B7077131
theorem B1179431 : Blo 413771 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B622415 : Blo 413771 622415 := bstep (se 1 (by rfl) ⟨466811, by rfl⟩ : syracuseStep 622415 = 933623) B933623
theorem B5046097 : Blo 413771 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B622535 : Blo 413771 622535 := bstep (se 1 (by rfl) ⟨466901, by rfl⟩ : syracuseStep 622535 = 933803) B933803
theorem B1408967 : Blo 413771 1408967 := bstep (se 1 (by rfl) ⟨1056725, by rfl⟩ : syracuseStep 1408967 = 2113451) B2113451
theorem B622847 : Blo 413771 622847 := bstep (se 1 (by rfl) ⟨467135, by rfl⟩ : syracuseStep 622847 = 934271) B934271
theorem B1048889 : Blo 413771 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B623003 : Blo 413771 623003 := bstep (se 1 (by rfl) ⟨467252, by rfl⟩ : syracuseStep 623003 = 934505) B934505
theorem B2097575 : Blo 413771 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B4817569 : Blo 413771 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B2654927 : Blo 413771 2654927 := bstep (se 1 (by rfl) ⟨1991195, by rfl⟩ : syracuseStep 2654927 = 3982391) B3982391
theorem B1180457 : Blo 413771 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B623423 : Blo 413771 623423 := bstep (se 1 (by rfl) ⟨467567, by rfl⟩ : syracuseStep 623423 = 935135) B935135
theorem B623567 : Blo 413771 623567 := bstep (se 1 (by rfl) ⟨467675, by rfl⟩ : syracuseStep 623567 = 935351) B935351
theorem B623657 : Blo 413771 623657 := bstep (se 2 (by rfl) ⟨233871, by rfl⟩ : syracuseStep 623657 = 467743) B467743
theorem B623687 : Blo 413771 623687 := bstep (se 1 (by rfl) ⟨467765, by rfl⟩ : syracuseStep 623687 = 935531) B935531
theorem B623867 : Blo 413771 623867 := bstep (se 1 (by rfl) ⟨467900, by rfl⟩ : syracuseStep 623867 = 935801) B935801
theorem B624155 : Blo 413771 624155 := bstep (se 1 (by rfl) ⟨468116, by rfl⟩ : syracuseStep 624155 = 936233) B936233
theorem B2393819 : Blo 413771 2393819 := bstep (se 1 (by rfl) ⟨1795364, by rfl⟩ : syracuseStep 2393819 = 3590729) B3590729
theorem B788201 : Blo 413771 788201 := bstep (se 2 (by rfl) ⟨295575, by rfl⟩ : syracuseStep 788201 = 591151) B591151
theorem B2361095 : Blo 413771 2361095 := bstep (se 1 (by rfl) ⟨1770821, by rfl⟩ : syracuseStep 2361095 = 3541643) B3541643
theorem B1181459 : Blo 413771 1181459 := bstep (se 1 (by rfl) ⟨886094, by rfl⟩ : syracuseStep 1181459 = 1772189) B1772189
theorem B8685409 : Blo 413771 8685409 := bstep (se 2 (by rfl) ⟨3257028, by rfl⟩ : syracuseStep 8685409 = 6514057) B6514057
theorem B1050479 : Blo 413771 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B624539 : Blo 413771 624539 := bstep (se 1 (by rfl) ⟨468404, by rfl⟩ : syracuseStep 624539 = 936809) B936809
theorem B624575 : Blo 413771 624575 := bstep (se 1 (by rfl) ⟨468431, by rfl⟩ : syracuseStep 624575 = 936863) B936863
theorem B1771591 : Blo 413771 1771591 := bstep (se 1 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 1771591 = 2657387) B2657387
theorem B591943 : Blo 413771 591943 := bstep (se 1 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 591943 = 887915) B887915
theorem B526591 : Blo 413771 526591 := bstep (se 1 (by rfl) ⟨394943, by rfl⟩ : syracuseStep 526591 = 789887) B789887
theorem B18024707 : Blo 413771 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B1051127 : Blo 413771 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B3148307 : Blo 413771 3148307 := bstep (se 1 (by rfl) ⟨2361230, by rfl⟩ : syracuseStep 3148307 = 4722461) B4722461
theorem B625199 : Blo 413771 625199 := bstep (se 1 (by rfl) ⟨468899, by rfl⟩ : syracuseStep 625199 = 937799) B937799
theorem B625319 : Blo 413771 625319 := bstep (se 1 (by rfl) ⟨468989, by rfl⟩ : syracuseStep 625319 = 937979) B937979
theorem B625385 : Blo 413771 625385 := bstep (se 2 (by rfl) ⟨234519, by rfl⟩ : syracuseStep 625385 = 469039) B469039
theorem B527087 : Blo 413771 527087 := bstep (se 1 (by rfl) ⟨395315, by rfl⟩ : syracuseStep 527087 = 790631) B790631
theorem B625391 : Blo 413771 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B625439 : Blo 413771 625439 := bstep (se 1 (by rfl) ⟨469079, by rfl⟩ : syracuseStep 625439 = 938159) B938159
theorem B1051643 : Blo 413771 1051643 := bstep (se 1 (by rfl) ⟨788732, by rfl⟩ : syracuseStep 1051643 = 1577465) B1577465
theorem B625769 : Blo 413771 625769 := bstep (se 2 (by rfl) ⟨234663, by rfl⟩ : syracuseStep 625769 = 469327) B469327
theorem B2362553 : Blo 413771 2362553 := bstep (se 2 (by rfl) ⟨885957, by rfl⟩ : syracuseStep 2362553 = 1771915) B1771915
theorem B625895 : Blo 413771 625895 := bstep (se 1 (by rfl) ⟨469421, by rfl⟩ : syracuseStep 625895 = 938843) B938843
theorem B626399 : Blo 413771 626399 := bstep (se 1 (by rfl) ⟨469799, by rfl⟩ : syracuseStep 626399 = 939599) B939599
theorem B1052635 : Blo 413771 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B3052121 : Blo 413771 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B1086347 : Blo 413771 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B1053931 : Blo 413771 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B4003303 : Blo 413771 4003303 := bstep (se 1 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 4003303 = 6004955) B6004955
theorem B1185263 : Blo 413771 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B563311 : Blo 413771 563311 := bstep (se 1 (by rfl) ⟨422483, by rfl⟩ : syracuseStep 563311 = 844967) B844967
theorem B1054903 : Blo 413771 1054903 := bstep (se 1 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 1054903 = 1582355) B1582355
theorem B1775981 : Blo 413771 1775981 := bstep (se 3 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 1775981 = 665993) B665993
theorem B2529767 : Blo 413771 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B10099201 : Blo 413771 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B465511 : Blo 413771 465511 := bstep (se 1 (by rfl) ⟨349133, by rfl⟩ : syracuseStep 465511 = 698267) B698267
theorem B4496107 : Blo 413771 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B3546017 : Blo 413771 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B2694505 : Blo 413771 2694505 := bstep (se 2 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 2694505 = 2020879) B2020879
theorem B663527 : Blo 413771 663527 := bstep (se 1 (by rfl) ⟨497645, by rfl⟩ : syracuseStep 663527 = 995291) B995291
theorem B3154139 : Blo 413771 3154139 := bstep (se 1 (by rfl) ⟨2365604, by rfl⟩ : syracuseStep 3154139 = 4731209) B4731209
theorem B7872815 : Blo 413771 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B1057151 : Blo 413771 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B15180209 : Blo 413771 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B4268483 : Blo 413771 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B2106323 : Blo 413771 2106323 := bstep (se 1 (by rfl) ⟨1579742, by rfl⟩ : syracuseStep 2106323 = 3159485) B3159485
theorem B5383597 : Blo 413771 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B468463 : Blo 413771 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B3548681 : Blo 413771 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B6728129 : Blo 413771 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B469615 : Blo 413771 469615 := bstep (se 1 (by rfl) ⟨352211, by rfl⟩ : syracuseStep 469615 = 704423) B704423
theorem B469831 : Blo 413771 469831 := bstep (se 1 (by rfl) ⟨352373, by rfl⟩ : syracuseStep 469831 = 704747) B704747
theorem B699455 : Blo 413771 699455 := bstep (se 1 (by rfl) ⟨524591, by rfl⟩ : syracuseStep 699455 = 1049183) B1049183
theorem B12038615 : Blo 413771 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B1782611 : Blo 413771 1782611 := bstep (se 1 (by rfl) ⟨1336958, by rfl⟩ : syracuseStep 1782611 = 2673917) B2673917
theorem B701419 : Blo 413771 701419 := bstep (se 1 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 701419 = 1052129) B1052129
theorem B931193 : Blo 413771 931193 := bstep (se 2 (by rfl) ⟨349197, by rfl⟩ : syracuseStep 931193 = 698395) B698395
theorem B931319 : Blo 413771 931319 := bstep (se 1 (by rfl) ⟨698489, by rfl⟩ : syracuseStep 931319 = 1396979) B1396979
theorem B2537257 : Blo 413771 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B1259507 : Blo 413771 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B4798541 : Blo 413771 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B4503761 : Blo 413771 4503761 := bstep (se 2 (by rfl) ⟨1688910, by rfl⟩ : syracuseStep 4503761 = 3377821) B3377821
theorem B702857 : Blo 413771 702857 := bstep (se 2 (by rfl) ⟨263571, by rfl⟩ : syracuseStep 702857 = 527143) B527143
theorem B932399 : Blo 413771 932399 := bstep (se 1 (by rfl) ⟨699299, by rfl⟩ : syracuseStep 932399 = 1398599) B1398599
theorem B703289 : Blo 413771 703289 := bstep (se 2 (by rfl) ⟨263733, by rfl⟩ : syracuseStep 703289 = 527467) B527467
theorem B2669507 : Blo 413771 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B703471 : Blo 413771 703471 := bstep (se 1 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 703471 = 1055207) B1055207
theorem B933191 : Blo 413771 933191 := bstep (se 1 (by rfl) ⟨699893, by rfl⟩ : syracuseStep 933191 = 1399787) B1399787
theorem B10108451 : Blo 413771 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B999067 : Blo 413771 999067 := bstep (se 1 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 999067 = 1498601) B1498601
theorem B1064699 : Blo 413771 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B999163 : Blo 413771 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B704585 : Blo 413771 704585 := bstep (se 2 (by rfl) ⟨264219, by rfl⟩ : syracuseStep 704585 = 528439) B528439
theorem B3555515 : Blo 413771 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B1196221 : Blo 413771 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B934199 : Blo 413771 934199 := bstep (se 1 (by rfl) ⟨700649, by rfl⟩ : syracuseStep 934199 = 1401299) B1401299
theorem B6078995 : Blo 413771 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B4735583 : Blo 413771 4735583 := bstep (se 1 (by rfl) ⟨3551687, by rfl⟩ : syracuseStep 4735583 = 7103375) B7103375
theorem B1688683 : Blo 413771 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B7980227 : Blo 413771 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B2245913 : Blo 413771 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B1296815 : Blo 413771 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B3558113 : Blo 413771 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B936683 : Blo 413771 936683 := bstep (se 1 (by rfl) ⟨702512, by rfl⟩ : syracuseStep 936683 = 1405025) B1405025
theorem B1134191 : Blo 413771 1134191 := bstep (se 1 (by rfl) ⟨850643, by rfl⟩ : syracuseStep 1134191 = 1701287) B1701287
theorem B937583 : Blo 413771 937583 := bstep (se 1 (by rfl) ⟨703187, by rfl⟩ : syracuseStep 937583 = 1406375) B1406375
theorem B937655 : Blo 413771 937655 := bstep (se 1 (by rfl) ⟨703241, by rfl⟩ : syracuseStep 937655 = 1406483) B1406483
theorem B8015597 : Blo 413771 8015597 := bstep (se 3 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 8015597 = 3005849) B3005849
theorem B938105 : Blo 413771 938105 := bstep (se 2 (by rfl) ⟨351789, by rfl⟩ : syracuseStep 938105 = 703579) B703579
theorem B1396871 : Blo 413771 1396871 := bstep (se 1 (by rfl) ⟨1047653, by rfl⟩ : syracuseStep 1396871 = 2095307) B2095307
theorem B1397033 : Blo 413771 1397033 := bstep (se 2 (by rfl) ⟨523887, by rfl⟩ : syracuseStep 1397033 = 1047775) B1047775
theorem B413999 : Blo 413771 413999 := bstep (se 1 (by rfl) ⟨310499, by rfl⟩ : syracuseStep 413999 = 620999) B620999
theorem B938411 : Blo 413771 938411 := bstep (se 1 (by rfl) ⟨703808, by rfl⟩ : syracuseStep 938411 = 1407617) B1407617
theorem B414143 : Blo 413771 414143 := bstep (se 1 (by rfl) ⟨310607, by rfl⟩ : syracuseStep 414143 = 621215) B621215
theorem B414239 : Blo 413771 414239 := bstep (se 1 (by rfl) ⟨310679, by rfl⟩ : syracuseStep 414239 = 621359) B621359
theorem B414319 : Blo 413771 414319 := bstep (se 1 (by rfl) ⟨310739, by rfl⟩ : syracuseStep 414319 = 621479) B621479
theorem B414439 : Blo 413771 414439 := bstep (se 1 (by rfl) ⟨310829, by rfl⟩ : syracuseStep 414439 = 621659) B621659
theorem B1135559 : Blo 413771 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B938951 : Blo 413771 938951 := bstep (se 1 (by rfl) ⟨704213, by rfl⟩ : syracuseStep 938951 = 1408427) B1408427
theorem B414687 : Blo 413771 414687 := bstep (se 1 (by rfl) ⟨311015, by rfl⟩ : syracuseStep 414687 = 622031) B622031
theorem B939113 : Blo 413771 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B414943 : Blo 413771 414943 := bstep (se 1 (by rfl) ⟨311207, by rfl⟩ : syracuseStep 414943 = 622415) B622415
theorem B415023 : Blo 413771 415023 := bstep (se 1 (by rfl) ⟨311267, by rfl⟩ : syracuseStep 415023 = 622535) B622535
theorem B939311 : Blo 413771 939311 := bstep (se 1 (by rfl) ⟨704483, by rfl⟩ : syracuseStep 939311 = 1408967) B1408967
theorem B415263 : Blo 413771 415263 := bstep (se 1 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 415263 = 622895) B622895
theorem B415423 : Blo 413771 415423 := bstep (se 1 (by rfl) ⟨311567, by rfl⟩ : syracuseStep 415423 = 623135) B623135
theorem B1398491 : Blo 413771 1398491 := bstep (se 1 (by rfl) ⟨1048868, by rfl⟩ : syracuseStep 1398491 = 2097737) B2097737
theorem B939743 : Blo 413771 939743 := bstep (se 1 (by rfl) ⟨704807, by rfl⟩ : syracuseStep 939743 = 1409615) B1409615
theorem B8968067 : Blo 413771 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B4511713 : Blo 413771 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B415871 : Blo 413771 415871 := bstep (se 1 (by rfl) ⟨311903, by rfl⟩ : syracuseStep 415871 = 623807) B623807
theorem B1398923 : Blo 413771 1398923 := bstep (se 1 (by rfl) ⟨1049192, by rfl⟩ : syracuseStep 1398923 = 2098385) B2098385
theorem B415967 : Blo 413771 415967 := bstep (se 1 (by rfl) ⟨311975, by rfl⟩ : syracuseStep 415967 = 623951) B623951
theorem B416027 : Blo 413771 416027 := bstep (se 1 (by rfl) ⟨312020, by rfl⟩ : syracuseStep 416027 = 624041) B624041
theorem B17127787 : Blo 413771 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B416127 : Blo 413771 416127 := bstep (se 1 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 416127 = 624191) B624191
theorem B416155 : Blo 413771 416155 := bstep (se 1 (by rfl) ⟨312116, by rfl⟩ : syracuseStep 416155 = 624233) B624233
theorem B6019717 : Blo 413771 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B416447 : Blo 413771 416447 := bstep (se 1 (by rfl) ⟨312335, by rfl⟩ : syracuseStep 416447 = 624671) B624671
theorem B416575 : Blo 413771 416575 := bstep (se 1 (by rfl) ⟨312431, by rfl⟩ : syracuseStep 416575 = 624863) B624863
theorem B416615 : Blo 413771 416615 := bstep (se 1 (by rfl) ⟨312461, by rfl⟩ : syracuseStep 416615 = 624923) B624923
theorem B1399841 : Blo 413771 1399841 := bstep (se 2 (by rfl) ⟨524940, by rfl⟩ : syracuseStep 1399841 = 1049881) B1049881
theorem B416831 : Blo 413771 416831 := bstep (se 1 (by rfl) ⟨312623, by rfl⟩ : syracuseStep 416831 = 625247) B625247
theorem B7986377 : Blo 413771 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B417019 : Blo 413771 417019 := bstep (se 1 (by rfl) ⟨312764, by rfl⟩ : syracuseStep 417019 = 625529) B625529
theorem B417051 : Blo 413771 417051 := bstep (se 1 (by rfl) ⟨312788, by rfl⟩ : syracuseStep 417051 = 625577) B625577
theorem B3792167 : Blo 413771 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B417151 : Blo 413771 417151 := bstep (se 1 (by rfl) ⟨312863, by rfl⟩ : syracuseStep 417151 = 625727) B625727
theorem B51010955 : Blo 413771 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B1400543 : Blo 413771 1400543 := bstep (se 1 (by rfl) ⟨1050407, by rfl⟩ : syracuseStep 1400543 = 2100815) B2100815
theorem B417519 : Blo 413771 417519 := bstep (se 1 (by rfl) ⟨313139, by rfl⟩ : syracuseStep 417519 = 626279) B626279
theorem B843839 : Blo 413771 843839 := bstep (se 1 (by rfl) ⟨632879, by rfl⟩ : syracuseStep 843839 = 1265759) B1265759
theorem B1336189 : Blo 413771 1336189 := bstep (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) B501071
theorem B4744331 : Blo 413771 4744331 := bstep (se 1 (by rfl) ⟨3558248, by rfl⟩ : syracuseStep 4744331 = 7116497) B7116497
theorem B7988381 : Blo 413771 7988381 := bstep (se 3 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 7988381 = 2995643) B2995643
theorem B1336895 : Blo 413771 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B3991193 : Blo 413771 3991193 := bstep (se 2 (by rfl) ⟨1496697, by rfl⟩ : syracuseStep 3991193 = 2993395) B2993395
theorem B27453329 : Blo 413771 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B1403945 : Blo 413771 1403945 := bstep (se 2 (by rfl) ⟨526479, by rfl⟩ : syracuseStep 1403945 = 1052959) B1052959
theorem B3633547 : Blo 413771 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B3797417 : Blo 413771 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B19264715 : Blo 413771 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B184251743 : Blo 413771 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B2095145 : Blo 413771 2095145 := bstep (se 2 (by rfl) ⟨785679, by rfl⟩ : syracuseStep 2095145 = 1571359) B1571359
theorem B1407023 : Blo 413771 1407023 := bstep (se 1 (by rfl) ⟨1055267, by rfl⟩ : syracuseStep 1407023 = 2110535) B2110535
theorem B620711 : Blo 413771 620711 := bstep (se 1 (by rfl) ⟨465533, by rfl⟩ : syracuseStep 620711 = 931067) B931067
theorem B5077235 : Blo 413771 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B620855 : Blo 413771 620855 := bstep (se 1 (by rfl) ⟨465641, by rfl⟩ : syracuseStep 620855 = 931283) B931283
theorem B621035 : Blo 413771 621035 := bstep (se 1 (by rfl) ⟨465776, by rfl⟩ : syracuseStep 621035 = 931553) B931553
theorem B621383 : Blo 413771 621383 := bstep (se 1 (by rfl) ⟨466037, by rfl⟩ : syracuseStep 621383 = 932075) B932075
theorem B2095955 : Blo 413771 2095955 := bstep (se 1 (by rfl) ⟨1571966, by rfl⟩ : syracuseStep 2095955 = 3143933) B3143933
theorem B4750163 : Blo 413771 4750163 := bstep (se 1 (by rfl) ⟨3562622, by rfl⟩ : syracuseStep 4750163 = 7125245) B7125245
theorem B1047887 : Blo 413771 1047887 := bstep (se 1 (by rfl) ⟨785915, by rfl⟩ : syracuseStep 1047887 = 1571831) B1571831
theorem B1768873 : Blo 413771 1768873 := bstep (se 2 (by rfl) ⟨663327, by rfl⟩ : syracuseStep 1768873 = 1326655) B1326655
theorem B949739 : Blo 413771 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B622217 : Blo 413771 622217 := bstep (se 2 (by rfl) ⟨233331, by rfl⟩ : syracuseStep 622217 = 466663) B466663
theorem B622247 : Blo 413771 622247 := bstep (se 1 (by rfl) ⟨466685, by rfl⟩ : syracuseStep 622247 = 933371) B933371
theorem B3145391 : Blo 413771 3145391 := bstep (se 1 (by rfl) ⟨2359043, by rfl⟩ : syracuseStep 3145391 = 4718087) B4718087
theorem B622367 : Blo 413771 622367 := bstep (se 1 (by rfl) ⟨466775, by rfl⟩ : syracuseStep 622367 = 933551) B933551
theorem B622427 : Blo 413771 622427 := bstep (se 1 (by rfl) ⟨466820, by rfl⟩ : syracuseStep 622427 = 933641) B933641
theorem B786287 : Blo 413771 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B622799 : Blo 413771 622799 := bstep (se 1 (by rfl) ⟨467099, by rfl⟩ : syracuseStep 622799 = 934199) B934199
theorem B1769951 : Blo 413771 1769951 := bstep (se 1 (by rfl) ⟨1327463, by rfl⟩ : syracuseStep 1769951 = 2654927) B2654927
theorem B786971 : Blo 413771 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B6423425 : Blo 413771 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B525467 : Blo 413771 525467 := bstep (se 1 (by rfl) ⟨394100, by rfl⟩ : syracuseStep 525467 = 788201) B788201
theorem B1574063 : Blo 413771 1574063 := bstep (se 1 (by rfl) ⟨1180547, by rfl⟩ : syracuseStep 1574063 = 2361095) B2361095
theorem B787639 : Blo 413771 787639 := bstep (se 1 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 787639 = 1181459) B1181459
theorem B2098871 : Blo 413771 2098871 := bstep (se 1 (by rfl) ⟨1574153, by rfl⟩ : syracuseStep 2098871 = 3148307) B3148307
theorem B624455 : Blo 413771 624455 := bstep (se 1 (by rfl) ⟨468341, by rfl⟩ : syracuseStep 624455 = 936683) B936683
theorem B7178129 : Blo 413771 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B624617 : Blo 413771 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B1575035 : Blo 413771 1575035 := bstep (se 1 (by rfl) ⟨1181276, by rfl⟩ : syracuseStep 1575035 = 2362553) B2362553
theorem B756127 : Blo 413771 756127 := bstep (se 1 (by rfl) ⟨567095, by rfl⟩ : syracuseStep 756127 = 1134191) B1134191
theorem B625055 : Blo 413771 625055 := bstep (se 1 (by rfl) ⟨468791, by rfl⟩ : syracuseStep 625055 = 937583) B937583
theorem B625103 : Blo 413771 625103 := bstep (se 1 (by rfl) ⟨468827, by rfl⟩ : syracuseStep 625103 = 937655) B937655
theorem B5343731 : Blo 413771 5343731 := bstep (se 1 (by rfl) ⟨4007798, by rfl⟩ : syracuseStep 5343731 = 8015597) B8015597
theorem B625403 : Blo 413771 625403 := bstep (se 1 (by rfl) ⟨469052, by rfl⟩ : syracuseStep 625403 = 938105) B938105
theorem B2362121 : Blo 413771 2362121 := bstep (se 2 (by rfl) ⟨885795, by rfl⟩ : syracuseStep 2362121 = 1771591) B1771591
theorem B789257 : Blo 413771 789257 := bstep (se 2 (by rfl) ⟨295971, by rfl⟩ : syracuseStep 789257 = 591943) B591943
theorem B625607 : Blo 413771 625607 := bstep (se 1 (by rfl) ⟨469205, by rfl⟩ : syracuseStep 625607 = 938411) B938411
theorem B724231 : Blo 413771 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B625967 : Blo 413771 625967 := bstep (se 1 (by rfl) ⟨469475, by rfl⟩ : syracuseStep 625967 = 938951) B938951
theorem B626075 : Blo 413771 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B626153 : Blo 413771 626153 := bstep (se 2 (by rfl) ⟨234807, by rfl⟩ : syracuseStep 626153 = 469615) B469615
theorem B626207 : Blo 413771 626207 := bstep (se 1 (by rfl) ⟨469655, by rfl⟩ : syracuseStep 626207 = 939311) B939311
theorem B790175 : Blo 413771 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B626441 : Blo 413771 626441 := bstep (se 2 (by rfl) ⟨234915, by rfl⟩ : syracuseStep 626441 = 469831) B469831
theorem B626495 : Blo 413771 626495 := bstep (se 1 (by rfl) ⟨469871, by rfl⟩ : syracuseStep 626495 = 939743) B939743
theorem B1183987 : Blo 413771 1183987 := bstep (se 1 (by rfl) ⟨887990, by rfl⟩ : syracuseStep 1183987 = 1775981) B1775981
theorem B13832693 : Blo 413771 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B2364011 : Blo 413771 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B2528111 : Blo 413771 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B562559 : Blo 413771 562559 := bstep (se 1 (by rfl) ⟨421919, by rfl⟩ : syracuseStep 562559 = 843839) B843839
theorem B2102759 : Blo 413771 2102759 := bstep (se 1 (by rfl) ⟨1577069, by rfl⟩ : syracuseStep 2102759 = 3154139) B3154139
theorem B5248543 : Blo 413771 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B2365787 : Blo 413771 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B891263 : Blo 413771 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B2660795 : Blo 413771 2660795 := bstep (se 1 (by rfl) ⟨1995596, by rfl⟩ : syracuseStep 2660795 = 3991193) B3991193
theorem B466303 : Blo 413771 466303 := bstep (se 1 (by rfl) ⟨349727, by rfl⟩ : syracuseStep 466303 = 699455) B699455
theorem B3383009 : Blo 413771 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B2531611 : Blo 413771 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B1188407 : Blo 413771 1188407 := bstep (se 1 (by rfl) ⟨891305, by rfl⟩ : syracuseStep 1188407 = 1782611) B1782611
theorem B2532637 : Blo 413771 2532637 := bstep (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) B949739
theorem B3384823 : Blo 413771 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B468571 : Blo 413771 468571 := bstep (se 1 (by rfl) ⟨351428, by rfl⟩ : syracuseStep 468571 = 702857) B702857
theorem B468859 : Blo 413771 468859 := bstep (se 1 (by rfl) ⟨351644, by rfl⟩ : syracuseStep 468859 = 703289) B703289
theorem B1779671 : Blo 413771 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B698591 : Blo 413771 698591 := bstep (se 1 (by rfl) ⟨523943, by rfl⟩ : syracuseStep 698591 = 1047887) B1047887
theorem B469723 : Blo 413771 469723 := bstep (se 1 (by rfl) ⟨352292, by rfl⟩ : syracuseStep 469723 = 704585) B704585
theorem B2370343 : Blo 413771 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B699259 : Blo 413771 699259 := bstep (se 1 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 699259 = 1048889) B1048889
theorem B3157055 : Blo 413771 3157055 := bstep (se 1 (by rfl) ⟨2367791, by rfl⟩ : syracuseStep 3157055 = 4735583) B4735583
theorem B5320151 : Blo 413771 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B1781585 : Blo 413771 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B700319 : Blo 413771 700319 := bstep (se 1 (by rfl) ⟨525239, by rfl⟩ : syracuseStep 700319 = 1050479) B1050479
theorem B8138989 : Blo 413771 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B700751 : Blo 413771 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B2372075 : Blo 413771 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B701095 : Blo 413771 701095 := bstep (se 1 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 701095 = 1051643) B1051643
theorem B11580545 : Blo 413771 11580545 := bstep (se 2 (by rfl) ⟨4342704, by rfl⟩ : syracuseStep 11580545 = 8685409) B8685409
theorem B3028157 : Blo 413771 3028157 := bstep (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) B1135559
theorem B931247 : Blo 413771 931247 := bstep (se 1 (by rfl) ⟨698435, by rfl⟩ : syracuseStep 931247 = 1396871) B1396871
theorem B931355 : Blo 413771 931355 := bstep (se 1 (by rfl) ⟨698516, by rfl⟩ : syracuseStep 931355 = 1397033) B1397033
theorem B702121 : Blo 413771 702121 := bstep (se 2 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 702121 = 526591) B526591
theorem B932327 : Blo 413771 932327 := bstep (se 1 (by rfl) ⟨699245, by rfl⟩ : syracuseStep 932327 = 1398491) B1398491
theorem B5978711 : Blo 413771 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B932615 : Blo 413771 932615 := bstep (se 1 (by rfl) ⟨699461, by rfl⟩ : syracuseStep 932615 = 1398923) B1398923
theorem B1686511 : Blo 413771 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B933227 : Blo 413771 933227 := bstep (se 1 (by rfl) ⟨699920, by rfl⟩ : syracuseStep 933227 = 1399841) B1399841
theorem B5324251 : Blo 413771 5324251 := bstep (se 1 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 5324251 = 7986377) B7986377
theorem B933695 : Blo 413771 933695 := bstep (se 1 (by rfl) ⟨700271, by rfl⟩ : syracuseStep 933695 = 1400543) B1400543
theorem B3358685 : Blo 413771 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B442351 : Blo 413771 442351 := bstep (se 1 (by rfl) ⟨331763, by rfl⟩ : syracuseStep 442351 = 663527) B663527
theorem B704767 : Blo 413771 704767 := bstep (se 1 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 704767 = 1057151) B1057151
theorem B3162887 : Blo 413771 3162887 := bstep (se 1 (by rfl) ⟨2372165, by rfl⟩ : syracuseStep 3162887 = 4744331) B4744331
theorem B5325587 : Blo 413771 5325587 := bstep (se 1 (by rfl) ⟨3994190, by rfl⟩ : syracuseStep 5325587 = 7988381) B7988381
theorem B18302219 : Blo 413771 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B935225 : Blo 413771 935225 := bstep (se 2 (by rfl) ⟨350709, by rfl⟩ : syracuseStep 935225 = 701419) B701419
theorem B935963 : Blo 413771 935963 := bstep (se 1 (by rfl) ⟨701972, by rfl⟩ : syracuseStep 935963 = 1403945) B1403945
theorem B6015617 : Blo 413771 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B122834495 : Blo 413771 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B937961 : Blo 413771 937961 := bstep (se 2 (by rfl) ⟨351735, by rfl⟩ : syracuseStep 937961 = 703471) B703471
theorem B1396763 : Blo 413771 1396763 := bstep (se 1 (by rfl) ⟨1047572, by rfl⟩ : syracuseStep 1396763 = 2095145) B2095145
theorem B938015 : Blo 413771 938015 := bstep (se 1 (by rfl) ⟨703511, by rfl⟩ : syracuseStep 938015 = 1407023) B1407023
theorem B3199027 : Blo 413771 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B413807 : Blo 413771 413807 := bstep (se 1 (by rfl) ⟨310355, by rfl⟩ : syracuseStep 413807 = 620711) B620711
theorem B3002507 : Blo 413771 3002507 := bstep (se 1 (by rfl) ⟨2251880, by rfl⟩ : syracuseStep 3002507 = 4503761) B4503761
theorem B413903 : Blo 413771 413903 := bstep (se 1 (by rfl) ⟨310427, by rfl⟩ : syracuseStep 413903 = 620855) B620855
theorem B414023 : Blo 413771 414023 := bstep (se 1 (by rfl) ⟨310517, by rfl⟩ : syracuseStep 414023 = 621035) B621035
theorem B3592673 : Blo 413771 3592673 := bstep (se 2 (by rfl) ⟨1347252, by rfl⟩ : syracuseStep 3592673 = 2694505) B2694505
theorem B414255 : Blo 413771 414255 := bstep (se 1 (by rfl) ⟨310691, by rfl⟩ : syracuseStep 414255 = 621383) B621383
theorem B1397303 : Blo 413771 1397303 := bstep (se 1 (by rfl) ⟨1047977, by rfl⟩ : syracuseStep 1397303 = 2095955) B2095955
theorem B3166775 : Blo 413771 3166775 := bstep (se 1 (by rfl) ⟨2375081, by rfl⟩ : syracuseStep 3166775 = 4750163) B4750163
theorem B1332089 : Blo 413771 1332089 := bstep (se 2 (by rfl) ⟨499533, by rfl⟩ : syracuseStep 1332089 = 999067) B999067
theorem B1332217 : Blo 413771 1332217 := bstep (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) B999163
theorem B6738967 : Blo 413771 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B414811 : Blo 413771 414811 := bstep (se 1 (by rfl) ⟨311108, by rfl⟩ : syracuseStep 414811 = 622217) B622217
theorem B414831 : Blo 413771 414831 := bstep (se 1 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 414831 = 622247) B622247
theorem B709799 : Blo 413771 709799 := bstep (se 1 (by rfl) ⟨532349, by rfl⟩ : syracuseStep 709799 = 1064699) B1064699
theorem B414911 : Blo 413771 414911 := bstep (se 1 (by rfl) ⟨311183, by rfl⟩ : syracuseStep 414911 = 622367) B622367
theorem B414951 : Blo 413771 414951 := bstep (se 1 (by rfl) ⟨311213, by rfl⟩ : syracuseStep 414951 = 622427) B622427
theorem B415231 : Blo 413771 415231 := bstep (se 1 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 415231 = 622847) B622847
theorem B1594961 : Blo 413771 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B415335 : Blo 413771 415335 := bstep (se 1 (by rfl) ⟨311501, by rfl⟩ : syracuseStep 415335 = 623003) B623003
theorem B1398383 : Blo 413771 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B4052663 : Blo 413771 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B415615 : Blo 413771 415615 := bstep (se 1 (by rfl) ⟨311711, by rfl⟩ : syracuseStep 415615 = 623423) B623423
theorem B415711 : Blo 413771 415711 := bstep (se 1 (by rfl) ⟨311783, by rfl⟩ : syracuseStep 415711 = 623567) B623567
theorem B415771 : Blo 413771 415771 := bstep (se 1 (by rfl) ⟨311828, by rfl⟩ : syracuseStep 415771 = 623657) B623657
theorem B415791 : Blo 413771 415791 := bstep (se 1 (by rfl) ⟨311843, by rfl⟩ : syracuseStep 415791 = 623687) B623687
theorem B415911 : Blo 413771 415911 := bstep (se 1 (by rfl) ⟨311933, by rfl⟩ : syracuseStep 415911 = 623867) B623867
theorem B1497275 : Blo 413771 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B416103 : Blo 413771 416103 := bstep (se 1 (by rfl) ⟨312077, by rfl⟩ : syracuseStep 416103 = 624155) B624155
theorem B1595879 : Blo 413771 1595879 := bstep (se 1 (by rfl) ⟨1196909, by rfl⟩ : syracuseStep 1595879 = 2393819) B2393819
theorem B416359 : Blo 413771 416359 := bstep (se 1 (by rfl) ⟨312269, by rfl⟩ : syracuseStep 416359 = 624539) B624539
theorem B416383 : Blo 413771 416383 := bstep (se 1 (by rfl) ⟨312287, by rfl⟩ : syracuseStep 416383 = 624575) B624575
theorem B2251577 : Blo 413771 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B12016471 : Blo 413771 12016471 := bstep (se 1 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 12016471 = 18024707) B18024707
theorem B416799 : Blo 413771 416799 := bstep (se 1 (by rfl) ⟨312599, by rfl⟩ : syracuseStep 416799 = 625199) B625199
theorem B416879 : Blo 413771 416879 := bstep (se 1 (by rfl) ⟨312659, by rfl⟩ : syracuseStep 416879 = 625319) B625319
theorem B416923 : Blo 413771 416923 := bstep (se 1 (by rfl) ⟨312692, by rfl⟩ : syracuseStep 416923 = 625385) B625385
theorem B416927 : Blo 413771 416927 := bstep (se 1 (by rfl) ⟨312695, by rfl⟩ : syracuseStep 416927 = 625391) B625391
theorem B416959 : Blo 413771 416959 := bstep (se 1 (by rfl) ⟨312719, by rfl⟩ : syracuseStep 416959 = 625439) B625439
theorem B417179 : Blo 413771 417179 := bstep (se 1 (by rfl) ⟨312884, by rfl⟩ : syracuseStep 417179 = 625769) B625769
theorem B417263 : Blo 413771 417263 := bstep (se 1 (by rfl) ⟨312947, by rfl⟩ : syracuseStep 417263 = 625895) B625895
theorem B417599 : Blo 413771 417599 := bstep (se 1 (by rfl) ⟨313199, by rfl⟩ : syracuseStep 417599 = 626399) B626399
theorem B34007303 : Blo 413771 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B1403513 : Blo 413771 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B10120139 : Blo 413771 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B2845655 : Blo 413771 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B4844729 : Blo 413771 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B1404215 : Blo 413771 1404215 := bstep (se 1 (by rfl) ⟨1053161, by rfl⟩ : syracuseStep 1404215 = 2106323) B2106323
theorem B4485419 : Blo 413771 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B1405241 : Blo 413771 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B1405565 : Blo 413771 1405565 := bstep (se 3 (by rfl) ⟨263543, by rfl⟩ : syracuseStep 1405565 = 527087) B527087
theorem B5337737 : Blo 413771 5337737 := bstep (se 2 (by rfl) ⟨2001651, by rfl⟩ : syracuseStep 5337737 = 4003303) B4003303
theorem B751081 : Blo 413771 751081 := bstep (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) B563311
theorem B1406537 : Blo 413771 1406537 := bstep (se 2 (by rfl) ⟨527451, by rfl⟩ : syracuseStep 1406537 = 1054903) B1054903
theorem B8025743 : Blo 413771 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B22837049 : Blo 413771 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B13465601 : Blo 413771 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B12843143 : Blo 413771 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B620681 : Blo 413771 620681 := bstep (se 2 (by rfl) ⟨232755, by rfl⟩ : syracuseStep 620681 = 465511) B465511
theorem B8026289 : Blo 413771 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B620795 : Blo 413771 620795 := bstep (se 1 (by rfl) ⟨465596, by rfl⟩ : syracuseStep 620795 = 931193) B931193
theorem B5994809 : Blo 413771 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B620879 : Blo 413771 620879 := bstep (se 1 (by rfl) ⟨465659, by rfl⟩ : syracuseStep 620879 = 931319) B931319
theorem B621599 : Blo 413771 621599 := bstep (se 1 (by rfl) ⟨466199, by rfl⟩ : syracuseStep 621599 = 932399) B932399
theorem B2358497 : Blo 413771 2358497 := bstep (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) B1768873
theorem B622127 : Blo 413771 622127 := bstep (se 1 (by rfl) ⟨466595, by rfl⟩ : syracuseStep 622127 = 933191) B933191
theorem B2096765 : Blo 413771 2096765 := bstep (se 3 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 2096765 = 786287) B786287
theorem B2096927 : Blo 413771 2096927 := bstep (se 1 (by rfl) ⟨1572695, by rfl⟩ : syracuseStep 2096927 = 3145391) B3145391
theorem B1179967 : Blo 413771 1179967 := bstep (se 1 (by rfl) ⟨884975, by rfl⟩ : syracuseStep 1179967 = 1769951) B1769951
theorem B524647 : Blo 413771 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B3375481 : Blo 413771 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B1049375 : Blo 413771 1049375 := bstep (se 1 (by rfl) ⟨787031, by rfl⟩ : syracuseStep 1049375 = 1574063) B1574063
theorem B623483 : Blo 413771 623483 := bstep (se 1 (by rfl) ⟨467612, by rfl⟩ : syracuseStep 623483 = 935225) B935225
theorem B4785419 : Blo 413771 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B623975 : Blo 413771 623975 := bstep (se 1 (by rfl) ⟨467981, by rfl⟩ : syracuseStep 623975 = 935963) B935963
theorem B1050023 : Blo 413771 1050023 := bstep (se 1 (by rfl) ⟨787517, by rfl⟩ : syracuseStep 1050023 = 1575035) B1575035
theorem B1050185 : Blo 413771 1050185 := bstep (se 2 (by rfl) ⟨393819, by rfl⟩ : syracuseStep 1050185 = 787639) B787639
theorem B3376849 : Blo 413771 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B7571189 : Blo 413771 7571189 := bstep (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) B709799
theorem B1574747 : Blo 413771 1574747 := bstep (se 1 (by rfl) ⟨1181060, by rfl⟩ : syracuseStep 1574747 = 2362121) B2362121
theorem B526171 : Blo 413771 526171 := bstep (se 1 (by rfl) ⟨394628, by rfl⟩ : syracuseStep 526171 = 789257) B789257
theorem B624761 : Blo 413771 624761 := bstep (se 2 (by rfl) ⟨234285, by rfl⟩ : syracuseStep 624761 = 468571) B468571
theorem B81889663 : Blo 413771 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B625145 : Blo 413771 625145 := bstep (se 2 (by rfl) ⟨234429, by rfl⟩ : syracuseStep 625145 = 468859) B468859
theorem B625307 : Blo 413771 625307 := bstep (se 1 (by rfl) ⟨468980, by rfl⟩ : syracuseStep 625307 = 937961) B937961
theorem B625343 : Blo 413771 625343 := bstep (se 1 (by rfl) ⟨469007, by rfl⟩ : syracuseStep 625343 = 938015) B938015
theorem B2001671 : Blo 413771 2001671 := bstep (se 1 (by rfl) ⟨1501253, by rfl⟩ : syracuseStep 2001671 = 3002507) B3002507
theorem B2395115 : Blo 413771 2395115 := bstep (se 1 (by rfl) ⟨1796336, by rfl⟩ : syracuseStep 2395115 = 3592673) B3592673
theorem B1576007 : Blo 413771 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B888059 : Blo 413771 888059 := bstep (se 1 (by rfl) ⟨666044, by rfl⟩ : syracuseStep 888059 = 1332089) B1332089
theorem B626297 : Blo 413771 626297 := bstep (se 2 (by rfl) ⟨234861, by rfl⟩ : syracuseStep 626297 = 469723) B469723
theorem B1577191 : Blo 413771 1577191 := bstep (se 1 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 1577191 = 2365787) B2365787
theorem B1773863 : Blo 413771 1773863 := bstep (se 1 (by rfl) ⟨1330397, by rfl⟩ : syracuseStep 1773863 = 2660795) B2660795
theorem B4265369 : Blo 413771 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B10851985 : Blo 413771 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B1578649 : Blo 413771 1578649 := bstep (se 2 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 1578649 = 1183987) B1183987
theorem B792271 : Blo 413771 792271 := bstep (se 1 (by rfl) ⟨594203, by rfl⟩ : syracuseStep 792271 = 1188407) B1188407
theorem B1776289 : Blo 413771 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B8985289 : Blo 413771 8985289 := bstep (se 2 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 8985289 = 6738967) B6738967
theorem B465727 : Blo 413771 465727 := bstep (se 1 (by rfl) ⟨349295, by rfl⟩ : syracuseStep 465727 = 698591) B698591
theorem B2104703 : Blo 413771 2104703 := bstep (se 1 (by rfl) ⟨1578527, by rfl⟩ : syracuseStep 2104703 = 3157055) B3157055
theorem B6004205 : Blo 413771 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B3546767 : Blo 413771 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B1187723 : Blo 413771 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B466879 : Blo 413771 466879 := bstep (se 1 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 466879 = 700319) B700319
theorem B2990279 : Blo 413771 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B467167 : Blo 413771 467167 := bstep (se 1 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 467167 = 700751) B700751
theorem B1581383 : Blo 413771 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B12919277 : Blo 413771 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B5350495 : Blo 413771 5350495 := bstep (se 1 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 5350495 = 8025743) B8025743
theorem B8562095 : Blo 413771 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B5350859 : Blo 413771 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B2107133 : Blo 413771 2107133 := bstep (se 3 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 2107133 = 790175) B790175
theorem B2239123 : Blo 413771 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B2108591 : Blo 413771 2108591 := bstep (se 1 (by rfl) ⟨1581443, by rfl⟩ : syracuseStep 2108591 = 3162887) B3162887
theorem B3550391 : Blo 413771 3550391 := bstep (se 1 (by rfl) ⟨2662793, by rfl⟩ : syracuseStep 3550391 = 5325587) B5325587
theorem B12201479 : Blo 413771 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B4010411 : Blo 413771 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B931175 : Blo 413771 931175 := bstep (se 1 (by rfl) ⟨698381, by rfl⟩ : syracuseStep 931175 = 1396763) B1396763
theorem B9221795 : Blo 413771 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B931535 : Blo 413771 931535 := bstep (se 1 (by rfl) ⟨698651, by rfl⟩ : syracuseStep 931535 = 1397303) B1397303
theorem B2111183 : Blo 413771 2111183 := bstep (se 1 (by rfl) ⟨1583387, by rfl⟩ : syracuseStep 2111183 = 3166775) B3166775
theorem B1685407 : Blo 413771 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B3160457 : Blo 413771 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B1063307 : Blo 413771 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B932255 : Blo 413771 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B2701775 : Blo 413771 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B932345 : Blo 413771 932345 := bstep (se 2 (by rfl) ⟨349629, by rfl⟩ : syracuseStep 932345 = 699259) B699259
theorem B998183 : Blo 413771 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B1063919 : Blo 413771 1063919 := bstep (se 1 (by rfl) ⟨797939, by rfl⟩ : syracuseStep 1063919 = 1595879) B1595879
theorem B965641 : Blo 413771 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B934793 : Blo 413771 934793 := bstep (se 2 (by rfl) ⟨350547, by rfl⟩ : syracuseStep 934793 = 701095) B701095
theorem B2376701 : Blo 413771 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B15943229 : Blo 413771 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B935675 : Blo 413771 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B1001441 : Blo 413771 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B6998057 : Blo 413771 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B936143 : Blo 413771 936143 := bstep (se 1 (by rfl) ⟨702107, by rfl⟩ : syracuseStep 936143 = 1404215) B1404215
theorem B936161 : Blo 413771 936161 := bstep (se 2 (by rfl) ⟨351060, by rfl⟩ : syracuseStep 936161 = 702121) B702121
theorem B936827 : Blo 413771 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B937043 : Blo 413771 937043 := bstep (se 1 (by rfl) ⟨702782, by rfl⟩ : syracuseStep 937043 = 1405565) B1405565
theorem B3558491 : Blo 413771 3558491 := bstep (se 1 (by rfl) ⟨2668868, by rfl⟩ : syracuseStep 3558491 = 5337737) B5337737
theorem B7720363 : Blo 413771 7720363 := bstep (se 1 (by rfl) ⟨5790272, by rfl⟩ : syracuseStep 7720363 = 11580545) B11580545
theorem B2018771 : Blo 413771 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B937691 : Blo 413771 937691 := bstep (se 1 (by rfl) ⟨703268, by rfl⟩ : syracuseStep 937691 = 1406537) B1406537
theorem B15224699 : Blo 413771 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B2248681 : Blo 413771 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B413787 : Blo 413771 413787 := bstep (se 1 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 413787 = 620681) B620681
theorem B413863 : Blo 413771 413863 := bstep (se 1 (by rfl) ⟨310397, by rfl⟩ : syracuseStep 413863 = 620795) B620795
theorem B413919 : Blo 413771 413919 := bstep (se 1 (by rfl) ⟨310439, by rfl⟩ : syracuseStep 413919 = 620879) B620879
theorem B7099001 : Blo 413771 7099001 := bstep (se 2 (by rfl) ⟨2662125, by rfl⟩ : syracuseStep 7099001 = 5324251) B5324251
theorem B414399 : Blo 413771 414399 := bstep (se 1 (by rfl) ⟨310799, by rfl⟩ : syracuseStep 414399 = 621599) B621599
theorem B414751 : Blo 413771 414751 := bstep (se 1 (by rfl) ⟨311063, by rfl⟩ : syracuseStep 414751 = 622127) B622127
theorem B1397843 : Blo 413771 1397843 := bstep (se 1 (by rfl) ⟨1048382, by rfl⟩ : syracuseStep 1397843 = 2096765) B2096765
theorem B1397951 : Blo 413771 1397951 := bstep (se 1 (by rfl) ⟨1048463, by rfl⟩ : syracuseStep 1397951 = 2096927) B2096927
theorem B415199 : Blo 413771 415199 := bstep (se 1 (by rfl) ⟨311399, by rfl⟩ : syracuseStep 415199 = 622799) B622799
theorem B939689 : Blo 413771 939689 := bstep (se 2 (by rfl) ⟨352383, by rfl⟩ : syracuseStep 939689 = 704767) B704767
theorem B4282283 : Blo 413771 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1399247 : Blo 413771 1399247 := bstep (se 1 (by rfl) ⟨1049435, by rfl⟩ : syracuseStep 1399247 = 2098871) B2098871
theorem B416303 : Blo 413771 416303 := bstep (se 1 (by rfl) ⟨312227, by rfl⟩ : syracuseStep 416303 = 624455) B624455
theorem B416411 : Blo 413771 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B416703 : Blo 413771 416703 := bstep (se 1 (by rfl) ⟨312527, by rfl⟩ : syracuseStep 416703 = 625055) B625055
theorem B416735 : Blo 413771 416735 := bstep (se 1 (by rfl) ⟨312551, by rfl⟩ : syracuseStep 416735 = 625103) B625103
theorem B3562487 : Blo 413771 3562487 := bstep (se 1 (by rfl) ⟨2671865, by rfl⟩ : syracuseStep 3562487 = 5343731) B5343731
theorem B416935 : Blo 413771 416935 := bstep (se 1 (by rfl) ⟨312701, by rfl⟩ : syracuseStep 416935 = 625403) B625403
theorem B417071 : Blo 413771 417071 := bstep (se 1 (by rfl) ⟨312803, by rfl⟩ : syracuseStep 417071 = 625607) B625607
theorem B4513097 : Blo 413771 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B417311 : Blo 413771 417311 := bstep (se 1 (by rfl) ⟨312983, by rfl⟩ : syracuseStep 417311 = 625967) B625967
theorem B417383 : Blo 413771 417383 := bstep (se 1 (by rfl) ⟨313037, by rfl⟩ : syracuseStep 417383 = 626075) B626075
theorem B417435 : Blo 413771 417435 := bstep (se 1 (by rfl) ⟨313076, by rfl⟩ : syracuseStep 417435 = 626153) B626153
theorem B417471 : Blo 413771 417471 := bstep (se 1 (by rfl) ⟨313103, by rfl⟩ : syracuseStep 417471 = 626207) B626207
theorem B417627 : Blo 413771 417627 := bstep (se 1 (by rfl) ⟨313220, by rfl⟩ : syracuseStep 417627 = 626441) B626441
theorem B417663 : Blo 413771 417663 := bstep (se 1 (by rfl) ⟨313247, by rfl⟩ : syracuseStep 417663 = 626495) B626495
theorem B1401245 : Blo 413771 1401245 := bstep (se 3 (by rfl) ⟨262733, by rfl⟩ : syracuseStep 1401245 = 525467) B525467
theorem B1008169 : Blo 413771 1008169 := bstep (se 2 (by rfl) ⟨378063, by rfl⟩ : syracuseStep 1008169 = 756127) B756127
theorem B1401839 : Blo 413771 1401839 := bstep (se 1 (by rfl) ⟨1051379, by rfl⟩ : syracuseStep 1401839 = 2102759) B2102759
theorem B1500157 : Blo 413771 1500157 := bstep (se 3 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 1500157 = 562559) B562559
theorem B2255339 : Blo 413771 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B4745789 : Blo 413771 4745789 := bstep (se 3 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 4745789 = 1779671) B1779671
theorem B22671535 : Blo 413771 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B6746759 : Blo 413771 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B1897103 : Blo 413771 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B620831 : Blo 413771 620831 := bstep (se 1 (by rfl) ⟨465623, by rfl⟩ : syracuseStep 620831 = 931247) B931247
theorem B620903 : Blo 413771 620903 := bstep (se 1 (by rfl) ⟨465677, by rfl⟩ : syracuseStep 620903 = 931355) B931355
theorem B16021961 : Blo 413771 16021961 := bstep (se 2 (by rfl) ⟨6008235, by rfl⟩ : syracuseStep 16021961 = 12016471) B12016471
theorem B8977067 : Blo 413771 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B3996539 : Blo 413771 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B621551 : Blo 413771 621551 := bstep (se 1 (by rfl) ⟨466163, by rfl⟩ : syracuseStep 621551 = 932327) B932327
theorem B621737 : Blo 413771 621737 := bstep (se 2 (by rfl) ⟨233151, by rfl⟩ : syracuseStep 621737 = 466303) B466303
theorem B621743 : Blo 413771 621743 := bstep (se 1 (by rfl) ⟨466307, by rfl⟩ : syracuseStep 621743 = 932615) B932615
theorem B1572331 : Blo 413771 1572331 := bstep (se 1 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 1572331 = 2358497) B2358497
theorem B622151 : Blo 413771 622151 := bstep (se 1 (by rfl) ⟨466613, by rfl⟩ : syracuseStep 622151 = 933227) B933227
theorem B622463 : Blo 413771 622463 := bstep (se 1 (by rfl) ⟨466847, by rfl⟩ : syracuseStep 622463 = 933695) B933695
theorem B2359205 : Blo 413771 2359205 := bstep (se 4 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 2359205 = 442351) B442351
theorem B622889 : Blo 413771 622889 := bstep (se 2 (by rfl) ⟨233583, by rfl⟩ : syracuseStep 622889 = 467167) B467167
theorem B1573289 : Blo 413771 1573289 := bstep (se 2 (by rfl) ⟨589983, by rfl⟩ : syracuseStep 1573289 = 1179967) B1179967
theorem B623195 : Blo 413771 623195 := bstep (se 1 (by rfl) ⟨467396, by rfl⟩ : syracuseStep 623195 = 934793) B934793
theorem B623783 : Blo 413771 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B1049831 : Blo 413771 1049831 := bstep (se 1 (by rfl) ⟨787373, by rfl⟩ : syracuseStep 1049831 = 1574747) B1574747
theorem B2000209 : Blo 413771 2000209 := bstep (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) B1500157
theorem B624095 : Blo 413771 624095 := bstep (se 1 (by rfl) ⟨468071, by rfl⟩ : syracuseStep 624095 = 936143) B936143
theorem B624107 : Blo 413771 624107 := bstep (se 1 (by rfl) ⟨468080, by rfl⟩ : syracuseStep 624107 = 936161) B936161
theorem B624551 : Blo 413771 624551 := bstep (se 1 (by rfl) ⟨468413, by rfl⟩ : syracuseStep 624551 = 936827) B936827
theorem B1050671 : Blo 413771 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B624695 : Blo 413771 624695 := bstep (se 1 (by rfl) ⟨468521, by rfl⟩ : syracuseStep 624695 = 937043) B937043
theorem B592039 : Blo 413771 592039 := bstep (se 1 (by rfl) ⟨444029, by rfl⟩ : syracuseStep 592039 = 888059) B888059
theorem B1345847 : Blo 413771 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B625127 : Blo 413771 625127 := bstep (se 1 (by rfl) ⟨468845, by rfl⟩ : syracuseStep 625127 = 937691) B937691
theorem B1182575 : Blo 413771 1182575 := bstep (se 1 (by rfl) ⟨886931, by rfl⟩ : syracuseStep 1182575 = 1773863) B1773863
theorem B5376901 : Blo 413771 5376901 := bstep (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) B1008169
theorem B109186217 : Blo 413771 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B2985497 : Blo 413771 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B626459 : Blo 413771 626459 := bstep (se 1 (by rfl) ⟨469844, by rfl⟩ : syracuseStep 626459 = 939689) B939689
theorem B2854855 : Blo 413771 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B10293817 : Blo 413771 10293817 := bstep (se 2 (by rfl) ⟨3860181, by rfl⟩ : syracuseStep 10293817 = 7720363) B7720363
theorem B20189837 : Blo 413771 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B4002803 : Blo 413771 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B2364511 : Blo 413771 2364511 := bstep (se 1 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 2364511 = 3546767) B3546767
theorem B1054255 : Blo 413771 1054255 := bstep (se 1 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 1054255 = 1581383) B1581383
theorem B2102921 : Blo 413771 2102921 := bstep (se 2 (by rfl) ⟨788595, by rfl⟩ : syracuseStep 2102921 = 1577191) B1577191
theorem B5708063 : Blo 413771 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B2661821 : Blo 413771 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B2366927 : Blo 413771 2366927 := bstep (se 1 (by rfl) ⟨1775195, by rfl⟩ : syracuseStep 2366927 = 3550391) B3550391
theorem B2104865 : Blo 413771 2104865 := bstep (se 2 (by rfl) ⟨789324, by rfl⟩ : syracuseStep 2104865 = 1578649) B1578649
theorem B1056361 : Blo 413771 1056361 := bstep (se 2 (by rfl) ⟨396135, by rfl⟩ : syracuseStep 1056361 = 792271) B792271
theorem B8134319 : Blo 413771 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B4497839 : Blo 413771 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B12034925 : Blo 413771 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B2368385 : Blo 413771 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B1287521 : Blo 413771 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B2106971 : Blo 413771 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B2664359 : Blo 413771 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B699529 : Blo 413771 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B4500641 : Blo 413771 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B699583 : Blo 413771 699583 := bstep (se 1 (by rfl) ⟨524687, by rfl⟩ : syracuseStep 699583 = 1049375) B1049375
theorem B1584467 : Blo 413771 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B3190279 : Blo 413771 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B700015 : Blo 413771 700015 := bstep (se 1 (by rfl) ⟨525011, by rfl⟩ : syracuseStep 700015 = 1050023) B1050023
theorem B10628819 : Blo 413771 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B700123 : Blo 413771 700123 := bstep (se 1 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 700123 = 1050185) B1050185
theorem B10694429 : Blo 413771 10694429 := bstep (se 3 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 10694429 = 4010411) B4010411
theorem B4665371 : Blo 413771 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B5058941 : Blo 413771 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B2372327 : Blo 413771 2372327 := bstep (se 1 (by rfl) ⟨1779245, by rfl⟩ : syracuseStep 2372327 = 3558491) B3558491
theorem B4502465 : Blo 413771 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B701561 : Blo 413771 701561 := bstep (se 2 (by rfl) ⟨263085, by rfl⟩ : syracuseStep 701561 = 526171) B526171
theorem B4732667 : Blo 413771 4732667 := bstep (se 1 (by rfl) ⟨3549500, by rfl⟩ : syracuseStep 4732667 = 7099001) B7099001
theorem B931895 : Blo 413771 931895 := bstep (se 1 (by rfl) ⟨698921, by rfl⟩ : syracuseStep 931895 = 1397843) B1397843
theorem B931967 : Blo 413771 931967 := bstep (se 1 (by rfl) ⟨698975, by rfl⟩ : syracuseStep 931967 = 1397951) B1397951
theorem B932831 : Blo 413771 932831 := bstep (se 1 (by rfl) ⟨699623, by rfl⟩ : syracuseStep 932831 = 1399247) B1399247
theorem B2374991 : Blo 413771 2374991 := bstep (se 1 (by rfl) ⟨1781243, by rfl⟩ : syracuseStep 2374991 = 3562487) B3562487
theorem B2670509 : Blo 413771 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B2998241 : Blo 413771 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B30228713 : Blo 413771 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B934163 : Blo 413771 934163 := bstep (se 1 (by rfl) ⟨700622, by rfl⟩ : syracuseStep 934163 = 1401245) B1401245
theorem B934559 : Blo 413771 934559 := bstep (se 1 (by rfl) ⟨700919, by rfl⟩ : syracuseStep 934559 = 1401839) B1401839
theorem B3163859 : Blo 413771 3163859 := bstep (se 1 (by rfl) ⟨2372894, by rfl⟩ : syracuseStep 3163859 = 4745789) B4745789
theorem B14469313 : Blo 413771 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B2247209 : Blo 413771 2247209 := bstep (se 2 (by rfl) ⟨842703, by rfl⟩ : syracuseStep 2247209 = 1685407) B1685407
theorem B11980385 : Blo 413771 11980385 := bstep (se 2 (by rfl) ⟨4492644, by rfl⟩ : syracuseStep 11980385 = 8985289) B8985289
theorem B6147863 : Blo 413771 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B413887 : Blo 413771 413887 := bstep (se 1 (by rfl) ⟨310415, by rfl⟩ : syracuseStep 413887 = 620831) B620831
theorem B413935 : Blo 413771 413935 := bstep (se 1 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 413935 = 620903) B620903
theorem B708871 : Blo 413771 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B5984711 : Blo 413771 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B414367 : Blo 413771 414367 := bstep (se 1 (by rfl) ⟨310775, by rfl⟩ : syracuseStep 414367 = 621551) B621551
theorem B709279 : Blo 413771 709279 := bstep (se 1 (by rfl) ⟨531959, by rfl⟩ : syracuseStep 709279 = 1063919) B1063919
theorem B414491 : Blo 413771 414491 := bstep (se 1 (by rfl) ⟨310868, by rfl⟩ : syracuseStep 414491 = 621737) B621737
theorem B414495 : Blo 413771 414495 := bstep (se 1 (by rfl) ⟨310871, by rfl⟩ : syracuseStep 414495 = 621743) B621743
theorem B3167261 : Blo 413771 3167261 := bstep (se 3 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 3167261 = 1187723) B1187723
theorem B414767 : Blo 413771 414767 := bstep (se 1 (by rfl) ⟨311075, by rfl⟩ : syracuseStep 414767 = 622151) B622151
theorem B414975 : Blo 413771 414975 := bstep (se 1 (by rfl) ⟨311231, by rfl⟩ : syracuseStep 414975 = 622463) B622463
theorem B415655 : Blo 413771 415655 := bstep (se 1 (by rfl) ⟨311741, by rfl⟩ : syracuseStep 415655 = 623483) B623483
theorem B415983 : Blo 413771 415983 := bstep (se 1 (by rfl) ⟨311987, by rfl⟩ : syracuseStep 415983 = 623975) B623975
theorem B416507 : Blo 413771 416507 := bstep (se 1 (by rfl) ⟨312380, by rfl⟩ : syracuseStep 416507 = 624761) B624761
theorem B7133993 : Blo 413771 7133993 := bstep (se 2 (by rfl) ⟨2675247, by rfl⟩ : syracuseStep 7133993 = 5350495) B5350495
theorem B416763 : Blo 413771 416763 := bstep (se 1 (by rfl) ⟨312572, by rfl⟩ : syracuseStep 416763 = 625145) B625145
theorem B416871 : Blo 413771 416871 := bstep (se 1 (by rfl) ⟨312653, by rfl⟩ : syracuseStep 416871 = 625307) B625307
theorem B416895 : Blo 413771 416895 := bstep (se 1 (by rfl) ⟨312671, by rfl⟩ : syracuseStep 416895 = 625343) B625343
theorem B1334447 : Blo 413771 1334447 := bstep (se 1 (by rfl) ⟨1000835, by rfl⟩ : syracuseStep 1334447 = 2001671) B2001671
theorem B1596743 : Blo 413771 1596743 := bstep (se 1 (by rfl) ⟨1197557, by rfl⟩ : syracuseStep 1596743 = 2395115) B2395115
theorem B417531 : Blo 413771 417531 := bstep (se 1 (by rfl) ⟨313148, by rfl⟩ : syracuseStep 417531 = 626297) B626297
theorem B10149799 : Blo 413771 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B2843579 : Blo 413771 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B1403135 : Blo 413771 1403135 := bstep (se 1 (by rfl) ⟨1052351, by rfl⟩ : syracuseStep 1403135 = 2104703) B2104703
theorem B1993519 : Blo 413771 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B8612851 : Blo 413771 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B3567239 : Blo 413771 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B1404755 : Blo 413771 1404755 := bstep (se 1 (by rfl) ⟨1053566, by rfl⟩ : syracuseStep 1404755 = 2107133) B2107133
theorem B1503559 : Blo 413771 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B1405727 : Blo 413771 1405727 := bstep (se 1 (by rfl) ⟨1054295, by rfl⟩ : syracuseStep 1405727 = 2108591) B2108591
theorem B620783 : Blo 413771 620783 := bstep (se 1 (by rfl) ⟨465587, by rfl⟩ : syracuseStep 620783 = 931175) B931175
theorem B620969 : Blo 413771 620969 := bstep (se 2 (by rfl) ⟨232863, by rfl⟩ : syracuseStep 620969 = 465727) B465727
theorem B621023 : Blo 413771 621023 := bstep (se 1 (by rfl) ⟨465767, by rfl⟩ : syracuseStep 621023 = 931535) B931535
theorem B1407455 : Blo 413771 1407455 := bstep (se 1 (by rfl) ⟨1055591, by rfl⟩ : syracuseStep 1407455 = 2111183) B2111183
theorem B621503 : Blo 413771 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B10681307 : Blo 413771 10681307 := bstep (se 1 (by rfl) ⟨8010980, by rfl⟩ : syracuseStep 10681307 = 16021961) B16021961
theorem B1801183 : Blo 413771 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B621563 : Blo 413771 621563 := bstep (se 1 (by rfl) ⟨466172, by rfl⟩ : syracuseStep 621563 = 932345) B932345
theorem B2096441 : Blo 413771 2096441 := bstep (se 2 (by rfl) ⟨786165, by rfl⟩ : syracuseStep 2096441 = 1572331) B1572331
theorem B622505 : Blo 413771 622505 := bstep (se 2 (by rfl) ⟨233439, by rfl⟩ : syracuseStep 622505 = 466879) B466879
theorem B1572803 : Blo 413771 1572803 := bstep (se 1 (by rfl) ⟨1179602, by rfl⟩ : syracuseStep 1572803 = 2359205) B2359205
theorem B20152475 : Blo 413771 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B622775 : Blo 413771 622775 := bstep (se 1 (by rfl) ⟨467081, by rfl⟩ : syracuseStep 622775 = 934163) B934163
theorem B1048859 : Blo 413771 1048859 := bstep (se 1 (by rfl) ⟨786644, by rfl⟩ : syracuseStep 1048859 = 1573289) B1573289
theorem B623039 : Blo 413771 623039 := bstep (se 1 (by rfl) ⟨467279, by rfl⟩ : syracuseStep 623039 = 934559) B934559
theorem B788383 : Blo 413771 788383 := bstep (se 1 (by rfl) ⟨591287, by rfl⟩ : syracuseStep 788383 = 1182575) B1182575
theorem B4098575 : Blo 413771 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B14355701 : Blo 413771 14355701 := bstep (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) B1345847
theorem B2658025 : Blo 413771 2658025 := bstep (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) B1993519
theorem B3805375 : Blo 413771 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B4755995 : Blo 413771 4755995 := bstep (se 1 (by rfl) ⟨3566996, by rfl⟩ : syracuseStep 4755995 = 7133993) B7133993
theorem B889631 : Blo 413771 889631 := bstep (se 1 (by rfl) ⟨667223, by rfl⟩ : syracuseStep 889631 = 1334447) B1334447
theorem B1774547 : Blo 413771 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B1577951 : Blo 413771 1577951 := bstep (se 1 (by rfl) ⟨1183463, by rfl⟩ : syracuseStep 1577951 = 2366927) B2366927
theorem B3806473 : Blo 413771 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B2004745 : Blo 413771 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B1578923 : Blo 413771 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B858347 : Blo 413771 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B1776239 : Blo 413771 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B3152681 : Blo 413771 3152681 := bstep (se 2 (by rfl) ⟨1182255, by rfl⟩ : syracuseStep 3152681 = 2364511) B2364511
theorem B1056311 : Blo 413771 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B7085879 : Blo 413771 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B12001709 : Blo 413771 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B1581551 : Blo 413771 1581551 := bstep (se 1 (by rfl) ⟨1186163, by rfl⟩ : syracuseStep 1581551 = 2372327) B2372327
theorem B467707 : Blo 413771 467707 := bstep (se 1 (by rfl) ⟨350780, by rfl⟩ : syracuseStep 467707 = 701561) B701561
theorem B3155111 : Blo 413771 3155111 := bstep (se 1 (by rfl) ⟨2366333, by rfl⟩ : syracuseStep 3155111 = 4732667) B4732667
theorem B2401577 : Blo 413771 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B7120871 : Blo 413771 7120871 := bstep (se 1 (by rfl) ⟨5340653, by rfl⟩ : syracuseStep 7120871 = 10681307) B10681307
theorem B1583327 : Blo 413771 1583327 := bstep (se 1 (by rfl) ⟨1187495, by rfl⟩ : syracuseStep 1583327 = 2374991) B2374991
theorem B1780339 : Blo 413771 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B699887 : Blo 413771 699887 := bstep (se 1 (by rfl) ⟨524915, by rfl⟩ : syracuseStep 699887 = 1049831) B1049831
theorem B3157541 : Blo 413771 3157541 := bstep (se 4 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 3157541 = 592039) B592039
theorem B2109239 : Blo 413771 2109239 := bstep (se 1 (by rfl) ⟨1581929, by rfl⟩ : syracuseStep 2109239 = 3163859) B3163859
theorem B700447 : Blo 413771 700447 := bstep (se 1 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 700447 = 1050671) B1050671
theorem B2666945 : Blo 413771 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B72790811 : Blo 413771 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B2668535 : Blo 413771 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B2111507 : Blo 413771 2111507 := bstep (se 1 (by rfl) ⟨1583630, by rfl⟩ : syracuseStep 2111507 = 3167261) B3167261
theorem B11483801 : Blo 413771 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B932705 : Blo 413771 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B932777 : Blo 413771 932777 := bstep (se 2 (by rfl) ⟨349791, by rfl⟩ : syracuseStep 932777 = 699583) B699583
theorem B933353 : Blo 413771 933353 := bstep (se 2 (by rfl) ⟨350007, by rfl⟩ : syracuseStep 933353 = 700015) B700015
theorem B1064495 : Blo 413771 1064495 := bstep (se 1 (by rfl) ⟨798371, by rfl⟩ : syracuseStep 1064495 = 1596743) B1596743
theorem B933497 : Blo 413771 933497 := bstep (se 2 (by rfl) ⟨350061, by rfl⟩ : syracuseStep 933497 = 700123) B700123
theorem B5422879 : Blo 413771 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B2998559 : Blo 413771 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B935423 : Blo 413771 935423 := bstep (se 1 (by rfl) ⟨701567, by rfl⟩ : syracuseStep 935423 = 1403135) B1403135
theorem B2378159 : Blo 413771 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B7129619 : Blo 413771 7129619 := bstep (se 1 (by rfl) ⟨5347214, by rfl⟩ : syracuseStep 7129619 = 10694429) B10694429
theorem B936503 : Blo 413771 936503 := bstep (se 1 (by rfl) ⟨702377, by rfl⟩ : syracuseStep 936503 = 1404755) B1404755
theorem B937151 : Blo 413771 937151 := bstep (se 1 (by rfl) ⟨702863, by rfl⟩ : syracuseStep 937151 = 1405727) B1405727
theorem B3001643 : Blo 413771 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B413855 : Blo 413771 413855 := bstep (se 1 (by rfl) ⟨310391, by rfl⟩ : syracuseStep 413855 = 620783) B620783
theorem B413979 : Blo 413771 413979 := bstep (se 1 (by rfl) ⟨310484, by rfl⟩ : syracuseStep 413979 = 620969) B620969
theorem B414015 : Blo 413771 414015 := bstep (se 1 (by rfl) ⟨310511, by rfl⟩ : syracuseStep 414015 = 621023) B621023
theorem B938303 : Blo 413771 938303 := bstep (se 1 (by rfl) ⟨703727, by rfl⟩ : syracuseStep 938303 = 1407455) B1407455
theorem B414335 : Blo 413771 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B414375 : Blo 413771 414375 := bstep (se 1 (by rfl) ⟨310781, by rfl⟩ : syracuseStep 414375 = 621563) B621563
theorem B1397627 : Blo 413771 1397627 := bstep (se 1 (by rfl) ⟨1048220, by rfl⟩ : syracuseStep 1397627 = 2096441) B2096441
theorem B415003 : Blo 413771 415003 := bstep (se 1 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 415003 = 622505) B622505
theorem B12440989 : Blo 413771 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B415259 : Blo 413771 415259 := bstep (se 1 (by rfl) ⟨311444, by rfl⟩ : syracuseStep 415259 = 622889) B622889
theorem B415463 : Blo 413771 415463 := bstep (se 1 (by rfl) ⟨311597, by rfl⟩ : syracuseStep 415463 = 623195) B623195
theorem B415855 : Blo 413771 415855 := bstep (se 1 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 415855 = 623783) B623783
theorem B416063 : Blo 413771 416063 := bstep (se 1 (by rfl) ⟨312047, by rfl⟩ : syracuseStep 416063 = 624095) B624095
theorem B416071 : Blo 413771 416071 := bstep (se 1 (by rfl) ⟨312053, by rfl⟩ : syracuseStep 416071 = 624107) B624107
theorem B13490509 : Blo 413771 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B416367 : Blo 413771 416367 := bstep (se 1 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 416367 = 624551) B624551
theorem B416463 : Blo 413771 416463 := bstep (se 1 (by rfl) ⟨312347, by rfl⟩ : syracuseStep 416463 = 624695) B624695
theorem B416751 : Blo 413771 416751 := bstep (se 1 (by rfl) ⟨312563, by rfl⟩ : syracuseStep 416751 = 625127) B625127
theorem B1498139 : Blo 413771 1498139 := bstep (se 1 (by rfl) ⟨1123604, by rfl⟩ : syracuseStep 1498139 = 2247209) B2247209
theorem B1990331 : Blo 413771 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B7986923 : Blo 413771 7986923 := bstep (se 1 (by rfl) ⟨5990192, by rfl⟩ : syracuseStep 7986923 = 11980385) B11980385
theorem B417639 : Blo 413771 417639 := bstep (se 1 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 417639 = 626459) B626459
theorem B19292417 : Blo 413771 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B3989807 : Blo 413771 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B13459891 : Blo 413771 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B15131285 : Blo 413771 15131285 := bstep (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) B709279
theorem B1401947 : Blo 413771 1401947 := bstep (se 1 (by rfl) ⟨1051460, by rfl⟩ : syracuseStep 1401947 = 2102921) B2102921
theorem B7169201 : Blo 413771 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B4253705 : Blo 413771 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B1403243 : Blo 413771 1403243 := bstep (se 1 (by rfl) ⟨1052432, by rfl⟩ : syracuseStep 1403243 = 2104865) B2104865
theorem B945161 : Blo 413771 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B8023283 : Blo 413771 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B1895719 : Blo 413771 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B13725089 : Blo 413771 13725089 := bstep (se 2 (by rfl) ⟨5146908, by rfl⟩ : syracuseStep 13725089 = 10293817) B10293817
theorem B1404647 : Blo 413771 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B1405673 : Blo 413771 1405673 := bstep (se 2 (by rfl) ⟨527127, by rfl⟩ : syracuseStep 1405673 = 1054255) B1054255
theorem B621263 : Blo 413771 621263 := bstep (se 1 (by rfl) ⟨465947, by rfl⟩ : syracuseStep 621263 = 931895) B931895
theorem B621311 : Blo 413771 621311 := bstep (se 1 (by rfl) ⟨465983, by rfl⟩ : syracuseStep 621311 = 931967) B931967
theorem B621887 : Blo 413771 621887 := bstep (se 1 (by rfl) ⟨466415, by rfl⟩ : syracuseStep 621887 = 932831) B932831
theorem B1408481 : Blo 413771 1408481 := bstep (se 2 (by rfl) ⟨528180, by rfl⟩ : syracuseStep 1408481 = 1056361) B1056361
theorem B13533065 : Blo 413771 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B1048535 : Blo 413771 1048535 := bstep (se 1 (by rfl) ⟨786401, by rfl⟩ : syracuseStep 1048535 = 1572803) B1572803
theorem B1998827 : Blo 413771 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B13434983 : Blo 413771 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B1999039 : Blo 413771 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B623609 : Blo 413771 623609 := bstep (se 2 (by rfl) ⟨233853, by rfl⟩ : syracuseStep 623609 = 467707) B467707
theorem B623615 : Blo 413771 623615 := bstep (se 1 (by rfl) ⟨467711, by rfl⟩ : syracuseStep 623615 = 935423) B935423
theorem B4753079 : Blo 413771 4753079 := bstep (se 1 (by rfl) ⟨3564809, by rfl⟩ : syracuseStep 4753079 = 7129619) B7129619
theorem B624335 : Blo 413771 624335 := bstep (se 1 (by rfl) ⟨468251, by rfl⟩ : syracuseStep 624335 = 936503) B936503
theorem B624767 : Blo 413771 624767 := bstep (se 1 (by rfl) ⟨468575, by rfl⟩ : syracuseStep 624767 = 937151) B937151
theorem B9570467 : Blo 413771 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B2001095 : Blo 413771 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B1051177 : Blo 413771 1051177 := bstep (se 2 (by rfl) ⟨394191, by rfl⟩ : syracuseStep 1051177 = 788383) B788383
theorem B625535 : Blo 413771 625535 := bstep (se 1 (by rfl) ⟨469151, by rfl⟩ : syracuseStep 625535 = 938303) B938303
theorem B593087 : Blo 413771 593087 := bstep (se 1 (by rfl) ⟨444815, by rfl⟩ : syracuseStep 593087 = 889631) B889631
theorem B1183031 : Blo 413771 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B1051967 : Blo 413771 1051967 := bstep (se 1 (by rfl) ⟨788975, by rfl⟩ : syracuseStep 1051967 = 1577951) B1577951
theorem B1052615 : Blo 413771 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B2527625 : Blo 413771 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B1184159 : Blo 413771 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B2101787 : Blo 413771 2101787 := bstep (se 1 (by rfl) ⟨1576340, by rfl⟩ : syracuseStep 2101787 = 3152681) B3152681
theorem B3544033 : Blo 413771 3544033 := bstep (se 2 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 3544033 = 2658025) B2658025
theorem B4723919 : Blo 413771 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B2659871 : Blo 413771 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B8001139 : Blo 413771 8001139 := bstep (se 1 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 8001139 = 12001709) B12001709
theorem B1054367 : Blo 413771 1054367 := bstep (se 1 (by rfl) ⟨790775, by rfl⟩ : syracuseStep 1054367 = 1581551) B1581551
theorem B2103407 : Blo 413771 2103407 := bstep (se 1 (by rfl) ⟨1577555, by rfl⟩ : syracuseStep 2103407 = 3155111) B3155111
theorem B1055551 : Blo 413771 1055551 := bstep (se 1 (by rfl) ⟨791663, by rfl⟩ : syracuseStep 1055551 = 1583327) B1583327
theorem B16587985 : Blo 413771 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B630107 : Blo 413771 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B5348855 : Blo 413771 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B9150059 : Blo 413771 9150059 := bstep (se 1 (by rfl) ⟨6862544, by rfl⟩ : syracuseStep 9150059 = 13725089) B13725089
theorem B466591 : Blo 413771 466591 := bstep (se 1 (by rfl) ⟨349943, by rfl⟩ : syracuseStep 466591 = 699887) B699887
theorem B2105027 : Blo 413771 2105027 := bstep (se 1 (by rfl) ⟨1578770, by rfl⟩ : syracuseStep 2105027 = 3157541) B3157541
theorem B1777963 : Blo 413771 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B1779023 : Blo 413771 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B9022043 : Blo 413771 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B699023 : Blo 413771 699023 := bstep (se 1 (by rfl) ⟨524267, by rfl⟩ : syracuseStep 699023 = 1048535) B1048535
theorem B699239 : Blo 413771 699239 := bstep (se 1 (by rfl) ⟨524429, by rfl⟩ : syracuseStep 699239 = 1048859) B1048859
theorem B1585439 : Blo 413771 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B2732383 : Blo 413771 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B931751 : Blo 413771 931751 := bstep (se 1 (by rfl) ⟨698813, by rfl⟩ : syracuseStep 931751 = 1397627) B1397627
theorem B2373785 : Blo 413771 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B572231 : Blo 413771 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B998759 : Blo 413771 998759 := bstep (se 1 (by rfl) ⟨749069, by rfl⟩ : syracuseStep 998759 = 1498139) B1498139
theorem B704207 : Blo 413771 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B1326887 : Blo 413771 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B5324615 : Blo 413771 5324615 := bstep (se 1 (by rfl) ⟨3993461, by rfl⟩ : syracuseStep 5324615 = 7986923) B7986923
theorem B933929 : Blo 413771 933929 := bstep (se 2 (by rfl) ⟨350223, by rfl⟩ : syracuseStep 933929 = 700447) B700447
theorem B12861611 : Blo 413771 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B934631 : Blo 413771 934631 := bstep (se 1 (by rfl) ⟨700973, by rfl⟩ : syracuseStep 934631 = 1401947) B1401947
theorem B2835803 : Blo 413771 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B935495 : Blo 413771 935495 := bstep (se 1 (by rfl) ⟨701621, by rfl⟩ : syracuseStep 935495 = 1403243) B1403243
theorem B2672993 : Blo 413771 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B936431 : Blo 413771 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B937115 : Blo 413771 937115 := bstep (se 1 (by rfl) ⟨702836, by rfl⟩ : syracuseStep 937115 = 1405673) B1405673
theorem B7655867 : Blo 413771 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B414175 : Blo 413771 414175 := bstep (se 1 (by rfl) ⟨310631, by rfl⟩ : syracuseStep 414175 = 621263) B621263
theorem B414207 : Blo 413771 414207 := bstep (se 1 (by rfl) ⟨310655, by rfl⟩ : syracuseStep 414207 = 621311) B621311
theorem B414591 : Blo 413771 414591 := bstep (se 1 (by rfl) ⟨310943, by rfl⟩ : syracuseStep 414591 = 621887) B621887
theorem B938987 : Blo 413771 938987 := bstep (se 1 (by rfl) ⟨704240, by rfl⟩ : syracuseStep 938987 = 1408481) B1408481
theorem B709663 : Blo 413771 709663 := bstep (se 1 (by rfl) ⟨532247, by rfl⟩ : syracuseStep 709663 = 1064495) B1064495
theorem B7230505 : Blo 413771 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1332551 : Blo 413771 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B415183 : Blo 413771 415183 := bstep (se 1 (by rfl) ⟨311387, by rfl⟩ : syracuseStep 415183 = 622775) B622775
theorem B415359 : Blo 413771 415359 := bstep (se 1 (by rfl) ⟨311519, by rfl⟩ : syracuseStep 415359 = 623039) B623039
theorem B17946521 : Blo 413771 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B3170663 : Blo 413771 3170663 := bstep (se 1 (by rfl) ⟨2377997, by rfl⟩ : syracuseStep 3170663 = 4755995) B4755995
theorem B5073833 : Blo 413771 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B10087523 : Blo 413771 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B4779467 : Blo 413771 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B1601051 : Blo 413771 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B4747247 : Blo 413771 4747247 := bstep (se 1 (by rfl) ⟨3560435, by rfl⟩ : syracuseStep 4747247 = 7120871) B7120871
theorem B5075297 : Blo 413771 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B1406159 : Blo 413771 1406159 := bstep (se 1 (by rfl) ⟨1054619, by rfl⟩ : syracuseStep 1406159 = 2109239) B2109239
theorem B17987345 : Blo 413771 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B48527207 : Blo 413771 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B1407671 : Blo 413771 1407671 := bstep (se 1 (by rfl) ⟨1055753, by rfl⟩ : syracuseStep 1407671 = 2111507) B2111507
theorem B621803 : Blo 413771 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B621851 : Blo 413771 621851 := bstep (se 1 (by rfl) ⟨466388, by rfl⟩ : syracuseStep 621851 = 932777) B932777
theorem B622235 : Blo 413771 622235 := bstep (se 1 (by rfl) ⟨466676, by rfl⟩ : syracuseStep 622235 = 933353) B933353
theorem B622331 : Blo 413771 622331 := bstep (se 1 (by rfl) ⟨466748, by rfl⟩ : syracuseStep 622331 = 933497) B933497
theorem B622619 : Blo 413771 622619 := bstep (se 1 (by rfl) ⟨466964, by rfl⟩ : syracuseStep 622619 = 933929) B933929
theorem B623087 : Blo 413771 623087 := bstep (se 1 (by rfl) ⟨467315, by rfl⟩ : syracuseStep 623087 = 934631) B934631
theorem B623663 : Blo 413771 623663 := bstep (se 1 (by rfl) ⟨467747, by rfl⟩ : syracuseStep 623663 = 935495) B935495
theorem B624287 : Blo 413771 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B624743 : Blo 413771 624743 := bstep (se 1 (by rfl) ⟨468557, by rfl⟩ : syracuseStep 624743 = 937115) B937115
theorem B788687 : Blo 413771 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B789439 : Blo 413771 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B625991 : Blo 413771 625991 := bstep (se 1 (by rfl) ⟨469493, by rfl⟩ : syracuseStep 625991 = 938987) B938987
theorem B3149279 : Blo 413771 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B888367 : Blo 413771 888367 := bstep (se 1 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 888367 = 1332551) B1332551
theorem B1773247 : Blo 413771 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B11964347 : Blo 413771 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B6100039 : Blo 413771 6100039 := bstep (se 1 (by rfl) ⟨4575029, by rfl⟩ : syracuseStep 6100039 = 9150059) B9150059
theorem B3643177 : Blo 413771 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B1186015 : Blo 413771 1186015 := bstep (se 1 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 1186015 = 1779023) B1779023
theorem B4725377 : Blo 413771 4725377 := bstep (se 2 (by rfl) ⟨1772016, by rfl⟩ : syracuseStep 4725377 = 3544033) B3544033
theorem B9640673 : Blo 413771 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B466015 : Blo 413771 466015 := bstep (se 1 (by rfl) ⟨349511, by rfl⟩ : syracuseStep 466015 = 699023) B699023
theorem B466159 : Blo 413771 466159 := bstep (se 1 (by rfl) ⟨349619, by rfl⟩ : syracuseStep 466159 = 699239) B699239
theorem B3382555 : Blo 413771 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B6725015 : Blo 413771 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B3186311 : Blo 413771 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B1056959 : Blo 413771 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B3383531 : Blo 413771 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B1581565 : Blo 413771 1581565 := bstep (se 3 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 1581565 = 593087) B593087
theorem B32351471 : Blo 413771 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B4269469 : Blo 413771 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B1582523 : Blo 413771 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B665839 : Blo 413771 665839 := bstep (se 1 (by rfl) ⟨499379, by rfl⟩ : syracuseStep 665839 = 998759) B998759
theorem B469471 : Blo 413771 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B3549743 : Blo 413771 3549743 := bstep (se 1 (by rfl) ⟨2662307, by rfl⟩ : syracuseStep 3549743 = 5324615) B5324615
theorem B8956655 : Blo 413771 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B2665385 : Blo 413771 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B2370617 : Blo 413771 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B1781995 : Blo 413771 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B701311 : Blo 413771 701311 := bstep (se 1 (by rfl) ⟨525983, by rfl⟩ : syracuseStep 701311 = 1051967) B1051967
theorem B701743 : Blo 413771 701743 := bstep (se 1 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 701743 = 1052615) B1052615
theorem B702911 : Blo 413771 702911 := bstep (se 1 (by rfl) ⟨527183, by rfl⟩ : syracuseStep 702911 = 1054367) B1054367
theorem B2113775 : Blo 413771 2113775 := bstep (se 1 (by rfl) ⟨1585331, by rfl⟩ : syracuseStep 2113775 = 3170663) B3170663
theorem B6014695 : Blo 413771 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B10668185 : Blo 413771 10668185 := bstep (se 2 (by rfl) ⟨4000569, by rfl⟩ : syracuseStep 10668185 = 8001139) B8001139
theorem B1525949 : Blo 413771 1525949 := bstep (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) B572231
theorem B3164831 : Blo 413771 3164831 := bstep (se 1 (by rfl) ⟨2373623, by rfl⟩ : syracuseStep 3164831 = 4747247) B4747247
theorem B937439 : Blo 413771 937439 := bstep (se 1 (by rfl) ⟨703079, by rfl⟩ : syracuseStep 937439 = 1406159) B1406159
theorem B938447 : Blo 413771 938447 := bstep (se 1 (by rfl) ⟨703835, by rfl⟩ : syracuseStep 938447 = 1407671) B1407671
theorem B414535 : Blo 413771 414535 := bstep (se 1 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 414535 = 621803) B621803
theorem B414567 : Blo 413771 414567 := bstep (se 1 (by rfl) ⟨310925, by rfl⟩ : syracuseStep 414567 = 621851) B621851
theorem B414823 : Blo 413771 414823 := bstep (se 1 (by rfl) ⟨311117, by rfl⟩ : syracuseStep 414823 = 622235) B622235
theorem B414887 : Blo 413771 414887 := bstep (se 1 (by rfl) ⟨311165, by rfl⟩ : syracuseStep 414887 = 622331) B622331
theorem B8574407 : Blo 413771 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B415739 : Blo 413771 415739 := bstep (se 1 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 415739 = 623609) B623609
theorem B415743 : Blo 413771 415743 := bstep (se 1 (by rfl) ⟨311807, by rfl⟩ : syracuseStep 415743 = 623615) B623615
theorem B1890535 : Blo 413771 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B6740333 : Blo 413771 6740333 := bstep (se 3 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 6740333 = 2527625) B2527625
theorem B3168719 : Blo 413771 3168719 := bstep (se 1 (by rfl) ⟨2376539, by rfl⟩ : syracuseStep 3168719 = 4753079) B4753079
theorem B416223 : Blo 413771 416223 := bstep (se 1 (by rfl) ⟨312167, by rfl⟩ : syracuseStep 416223 = 624335) B624335
theorem B416511 : Blo 413771 416511 := bstep (se 1 (by rfl) ⟨312383, by rfl⟩ : syracuseStep 416511 = 624767) B624767
theorem B6380311 : Blo 413771 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B1334063 : Blo 413771 1334063 := bstep (se 1 (by rfl) ⟨1000547, by rfl⟩ : syracuseStep 1334063 = 2001095) B2001095
theorem B417023 : Blo 413771 417023 := bstep (se 1 (by rfl) ⟨312767, by rfl⟩ : syracuseStep 417023 = 625535) B625535
theorem B5103911 : Blo 413771 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B1401191 : Blo 413771 1401191 := bstep (se 1 (by rfl) ⟨1050893, by rfl⟩ : syracuseStep 1401191 = 2101787) B2101787
theorem B1401569 : Blo 413771 1401569 := bstep (se 2 (by rfl) ⟨525588, by rfl⟩ : syracuseStep 1401569 = 1051177) B1051177
theorem B1402271 : Blo 413771 1402271 := bstep (se 1 (by rfl) ⟨1051703, by rfl⟩ : syracuseStep 1402271 = 2103407) B2103407
theorem B420071 : Blo 413771 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B3565903 : Blo 413771 3565903 := bstep (se 1 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 3565903 = 5348855) B5348855
theorem B1403351 : Blo 413771 1403351 := bstep (se 1 (by rfl) ⟨1052513, by rfl⟩ : syracuseStep 1403351 = 2105027) B2105027
theorem B946217 : Blo 413771 946217 := bstep (se 2 (by rfl) ⟨354831, by rfl⟩ : syracuseStep 946217 = 709663) B709663
theorem B1407401 : Blo 413771 1407401 := bstep (se 2 (by rfl) ⟨527775, by rfl⟩ : syracuseStep 1407401 = 1055551) B1055551
theorem B11991563 : Blo 413771 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B621167 : Blo 413771 621167 := bstep (se 1 (by rfl) ⟨465875, by rfl⟩ : syracuseStep 621167 = 931751) B931751
theorem B22117313 : Blo 413771 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B622121 : Blo 413771 622121 := bstep (se 2 (by rfl) ⟨233295, by rfl⟩ : syracuseStep 622121 = 466591) B466591
theorem B884591 : Blo 413771 884591 := bstep (se 1 (by rfl) ⟨663443, by rfl⟩ : syracuseStep 884591 = 1326887) B1326887
theorem B1409183 : Blo 413771 1409183 := bstep (se 1 (by rfl) ⟨1056887, by rfl⟩ : syracuseStep 1409183 = 2113775) B2113775
theorem B7112123 : Blo 413771 7112123 := bstep (se 1 (by rfl) ⟨5334092, by rfl⟩ : syracuseStep 7112123 = 10668185) B10668185
theorem B1017299 : Blo 413771 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B525791 : Blo 413771 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B2099519 : Blo 413771 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B624959 : Blo 413771 624959 := bstep (se 1 (by rfl) ⟨468719, by rfl⟩ : syracuseStep 624959 = 937439) B937439
theorem B625631 : Blo 413771 625631 := bstep (se 1 (by rfl) ⟨469223, by rfl⟩ : syracuseStep 625631 = 938447) B938447
theorem B4754537 : Blo 413771 4754537 := bstep (se 2 (by rfl) ⟨1782951, by rfl⟩ : syracuseStep 4754537 = 3565903) B3565903
theorem B625961 : Blo 413771 625961 := bstep (se 2 (by rfl) ⟨234735, by rfl⟩ : syracuseStep 625961 = 469471) B469471
theorem B1052585 : Blo 413771 1052585 := bstep (se 2 (by rfl) ⟨394719, by rfl⟩ : syracuseStep 1052585 = 789439) B789439
theorem B4493555 : Blo 413771 4493555 := bstep (se 1 (by rfl) ⟨3370166, by rfl⟩ : syracuseStep 4493555 = 6740333) B6740333
theorem B3150251 : Blo 413771 3150251 := bstep (se 1 (by rfl) ⟨2362688, by rfl⟩ : syracuseStep 3150251 = 4725377) B4725377
theorem B6427115 : Blo 413771 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B889375 : Blo 413771 889375 := bstep (se 1 (by rfl) ⟨667031, by rfl⟩ : syracuseStep 889375 = 1334063) B1334063
theorem B1184489 : Blo 413771 1184489 := bstep (se 2 (by rfl) ⟨444183, by rfl⟩ : syracuseStep 1184489 = 888367) B888367
theorem B2364329 : Blo 413771 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B1120189 : Blo 413771 1120189 := bstep (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) B420071
theorem B21567647 : Blo 413771 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B1055015 : Blo 413771 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B8133385 : Blo 413771 8133385 := bstep (se 2 (by rfl) ⟨3050019, by rfl⟩ : syracuseStep 8133385 = 6100039) B6100039
theorem B2366495 : Blo 413771 2366495 := bstep (se 1 (by rfl) ⟨1774871, by rfl⟩ : syracuseStep 2366495 = 3549743) B3549743
theorem B5971103 : Blo 413771 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B1776923 : Blo 413771 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B1580411 : Blo 413771 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B4857569 : Blo 413771 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B630811 : Blo 413771 630811 := bstep (se 1 (by rfl) ⟨473108, by rfl⟩ : syracuseStep 630811 = 946217) B946217
theorem B1581353 : Blo 413771 1581353 := bstep (se 2 (by rfl) ⟨593007, by rfl⟩ : syracuseStep 1581353 = 1186015) B1186015
theorem B468607 : Blo 413771 468607 := bstep (se 1 (by rfl) ⟨351455, by rfl⟩ : syracuseStep 468607 = 702911) B702911
theorem B8496829 : Blo 413771 8496829 := bstep (se 3 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 8496829 = 3186311) B3186311
theorem B2108753 : Blo 413771 2108753 := bstep (se 2 (by rfl) ⟨790782, by rfl⟩ : syracuseStep 2108753 = 1581565) B1581565
theorem B3551141 : Blo 413771 3551141 := bstep (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) B665839
theorem B2109887 : Blo 413771 2109887 := bstep (se 1 (by rfl) ⟨1582415, by rfl⟩ : syracuseStep 2109887 = 3164831) B3164831
theorem B7976231 : Blo 413771 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B5716271 : Blo 413771 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B2112479 : Blo 413771 2112479 := bstep (se 1 (by rfl) ⟨1584359, by rfl⟩ : syracuseStep 2112479 = 3168719) B3168719
theorem B704639 : Blo 413771 704639 := bstep (se 1 (by rfl) ⟨528479, by rfl⟩ : syracuseStep 704639 = 1056959) B1056959
theorem B934127 : Blo 413771 934127 := bstep (se 1 (by rfl) ⟨700595, by rfl⟩ : syracuseStep 934127 = 1401191) B1401191
theorem B2375993 : Blo 413771 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B934379 : Blo 413771 934379 := bstep (se 1 (by rfl) ⟨700784, by rfl⟩ : syracuseStep 934379 = 1401569) B1401569
theorem B934847 : Blo 413771 934847 := bstep (se 1 (by rfl) ⟨701135, by rfl⟩ : syracuseStep 934847 = 1402271) B1402271
theorem B935081 : Blo 413771 935081 := bstep (se 2 (by rfl) ⟨350655, by rfl⟩ : syracuseStep 935081 = 701311) B701311
theorem B935567 : Blo 413771 935567 := bstep (se 1 (by rfl) ⟨701675, by rfl⟩ : syracuseStep 935567 = 1403351) B1403351
theorem B935657 : Blo 413771 935657 := bstep (se 2 (by rfl) ⟨350871, by rfl⟩ : syracuseStep 935657 = 701743) B701743
theorem B8507081 : Blo 413771 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B938267 : Blo 413771 938267 := bstep (se 1 (by rfl) ⟨703700, by rfl⟩ : syracuseStep 938267 = 1407401) B1407401
theorem B4510073 : Blo 413771 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B414111 : Blo 413771 414111 := bstep (se 1 (by rfl) ⟨310583, by rfl⟩ : syracuseStep 414111 = 621167) B621167
theorem B414747 : Blo 413771 414747 := bstep (se 1 (by rfl) ⟨311060, by rfl⟩ : syracuseStep 414747 = 622121) B622121
theorem B415079 : Blo 413771 415079 := bstep (se 1 (by rfl) ⟨311309, by rfl⟩ : syracuseStep 415079 = 622619) B622619
theorem B415391 : Blo 413771 415391 := bstep (se 1 (by rfl) ⟨311543, by rfl⟩ : syracuseStep 415391 = 623087) B623087
theorem B415775 : Blo 413771 415775 := bstep (se 1 (by rfl) ⟨311831, by rfl⟩ : syracuseStep 415775 = 623663) B623663
theorem B416191 : Blo 413771 416191 := bstep (se 1 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 416191 = 624287) B624287
theorem B416495 : Blo 413771 416495 := bstep (se 1 (by rfl) ⟨312371, by rfl⟩ : syracuseStep 416495 = 624743) B624743
theorem B5692625 : Blo 413771 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B417327 : Blo 413771 417327 := bstep (se 1 (by rfl) ⟨312995, by rfl⟩ : syracuseStep 417327 = 625991) B625991
theorem B8019593 : Blo 413771 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B4483343 : Blo 413771 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B2255687 : Blo 413771 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B3402607 : Blo 413771 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B2520713 : Blo 413771 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B621353 : Blo 413771 621353 := bstep (se 2 (by rfl) ⟨233007, by rfl⟩ : syracuseStep 621353 = 466015) B466015
theorem B621545 : Blo 413771 621545 := bstep (se 2 (by rfl) ⟨233079, by rfl⟩ : syracuseStep 621545 = 466159) B466159
theorem B7994375 : Blo 413771 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B14744875 : Blo 413771 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B589727 : Blo 413771 589727 := bstep (se 1 (by rfl) ⟨442295, by rfl⟩ : syracuseStep 589727 = 884591) B884591
theorem B622751 : Blo 413771 622751 := bstep (se 1 (by rfl) ⟨467063, by rfl⟩ : syracuseStep 622751 = 934127) B934127
theorem B622919 : Blo 413771 622919 := bstep (se 1 (by rfl) ⟨467189, by rfl⟩ : syracuseStep 622919 = 934379) B934379
theorem B623231 : Blo 413771 623231 := bstep (se 1 (by rfl) ⟨467423, by rfl⟩ : syracuseStep 623231 = 934847) B934847
theorem B623387 : Blo 413771 623387 := bstep (se 1 (by rfl) ⟨467540, by rfl⟩ : syracuseStep 623387 = 935081) B935081
theorem B623711 : Blo 413771 623711 := bstep (se 1 (by rfl) ⟨467783, by rfl⟩ : syracuseStep 623711 = 935567) B935567
theorem B623771 : Blo 413771 623771 := bstep (se 1 (by rfl) ⟨467828, by rfl⟩ : syracuseStep 623771 = 935657) B935657
theorem B624809 : Blo 413771 624809 := bstep (se 2 (by rfl) ⟨234303, by rfl⟩ : syracuseStep 624809 = 468607) B468607
theorem B5671387 : Blo 413771 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B625511 : Blo 413771 625511 := bstep (se 1 (by rfl) ⟨469133, by rfl⟩ : syracuseStep 625511 = 938267) B938267
theorem B2100167 : Blo 413771 2100167 := bstep (se 1 (by rfl) ⟨1575125, by rfl⟩ : syracuseStep 2100167 = 3150251) B3150251
theorem B789659 : Blo 413771 789659 := bstep (se 1 (by rfl) ⟨592244, by rfl⟩ : syracuseStep 789659 = 1184489) B1184489
theorem B1576219 : Blo 413771 1576219 := bstep (se 1 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 1576219 = 2364329) B2364329
theorem B1577663 : Blo 413771 1577663 := bstep (se 1 (by rfl) ⟨1183247, by rfl⟩ : syracuseStep 1577663 = 2366495) B2366495
theorem B1184615 : Blo 413771 1184615 := bstep (se 1 (by rfl) ⟨888461, by rfl⟩ : syracuseStep 1184615 = 1776923) B1776923
theorem B1053607 : Blo 413771 1053607 := bstep (se 1 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 1053607 = 1580411) B1580411
theorem B5346395 : Blo 413771 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B1054235 : Blo 413771 1054235 := bstep (se 1 (by rfl) ⟨790676, by rfl⟩ : syracuseStep 1054235 = 1581353) B1581353
theorem B57513725 : Blo 413771 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B1185833 : Blo 413771 1185833 := bstep (se 2 (by rfl) ⟨444687, by rfl⟩ : syracuseStep 1185833 = 889375) B889375
theorem B15243389 : Blo 413771 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B2988895 : Blo 413771 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B2367427 : Blo 413771 2367427 := bstep (se 1 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 2367427 = 3551141) B3551141
theorem B5317487 : Blo 413771 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B1680475 : Blo 413771 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B469759 : Blo 413771 469759 := bstep (se 1 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 469759 = 704639) B704639
theorem B1583995 : Blo 413771 1583995 := bstep (se 1 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 1583995 = 2375993) B2375993
theorem B701723 : Blo 413771 701723 := bstep (se 1 (by rfl) ⟨526292, by rfl⟩ : syracuseStep 701723 = 1052585) B1052585
theorem B2995703 : Blo 413771 2995703 := bstep (se 1 (by rfl) ⟨2246777, by rfl⟩ : syracuseStep 2995703 = 4493555) B4493555
theorem B4536809 : Blo 413771 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B703343 : Blo 413771 703343 := bstep (se 1 (by rfl) ⟨527507, by rfl⟩ : syracuseStep 703343 = 1055015) B1055015
theorem B3980735 : Blo 413771 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B1493585 : Blo 413771 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B414235 : Blo 413771 414235 := bstep (se 1 (by rfl) ⟨310676, by rfl⟩ : syracuseStep 414235 = 621353) B621353
theorem B414363 : Blo 413771 414363 := bstep (se 1 (by rfl) ⟨310772, by rfl⟩ : syracuseStep 414363 = 621545) B621545
theorem B5329583 : Blo 413771 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B939455 : Blo 413771 939455 := bstep (se 1 (by rfl) ⟨704591, by rfl⟩ : syracuseStep 939455 = 1409183) B1409183
theorem B3364325 : Blo 413771 3364325 := bstep (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) B630811
theorem B4741415 : Blo 413771 4741415 := bstep (se 1 (by rfl) ⟨3556061, by rfl⟩ : syracuseStep 4741415 = 7112123) B7112123
theorem B1399679 : Blo 413771 1399679 := bstep (se 1 (by rfl) ⟨1049759, by rfl⟩ : syracuseStep 1399679 = 2099519) B2099519
theorem B416639 : Blo 413771 416639 := bstep (se 1 (by rfl) ⟨312479, by rfl⟩ : syracuseStep 416639 = 624959) B624959
theorem B417087 : Blo 413771 417087 := bstep (se 1 (by rfl) ⟨312815, by rfl⟩ : syracuseStep 417087 = 625631) B625631
theorem B3169691 : Blo 413771 3169691 := bstep (se 1 (by rfl) ⟨2377268, by rfl⟩ : syracuseStep 3169691 = 4754537) B4754537
theorem B417307 : Blo 413771 417307 := bstep (se 1 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 417307 = 625961) B625961
theorem B11329105 : Blo 413771 11329105 := bstep (se 2 (by rfl) ⟨4248414, by rfl⟩ : syracuseStep 11329105 = 8496829) B8496829
theorem B3006715 : Blo 413771 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B4284743 : Blo 413771 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B2712797 : Blo 413771 2712797 := bstep (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) B1017299
theorem B1402109 : Blo 413771 1402109 := bstep (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) B525791
theorem B3795083 : Blo 413771 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B3238379 : Blo 413771 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B1503791 : Blo 413771 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B1405835 : Blo 413771 1405835 := bstep (se 1 (by rfl) ⟨1054376, by rfl⟩ : syracuseStep 1405835 = 2108753) B2108753
theorem B1406591 : Blo 413771 1406591 := bstep (se 1 (by rfl) ⟨1054943, by rfl⟩ : syracuseStep 1406591 = 2109887) B2109887
theorem B10844513 : Blo 413771 10844513 := bstep (se 2 (by rfl) ⟨4066692, by rfl⟩ : syracuseStep 10844513 = 8133385) B8133385
theorem B19659833 : Blo 413771 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B1408319 : Blo 413771 1408319 := bstep (se 1 (by rfl) ⟨1056239, by rfl⟩ : syracuseStep 1408319 = 2112479) B2112479
theorem B1572605 : Blo 413771 1572605 := bstep (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) B589727
theorem B526439 : Blo 413771 526439 := bstep (se 1 (by rfl) ⟨394829, by rfl⟩ : syracuseStep 526439 = 789659) B789659
theorem B1051775 : Blo 413771 1051775 := bstep (se 1 (by rfl) ⟨788831, by rfl⟩ : syracuseStep 1051775 = 1577663) B1577663
theorem B789743 : Blo 413771 789743 := bstep (se 1 (by rfl) ⟨592307, by rfl⟩ : syracuseStep 789743 = 1184615) B1184615
theorem B626303 : Blo 413771 626303 := bstep (se 1 (by rfl) ⟨469727, by rfl⟩ : syracuseStep 626303 = 939455) B939455
theorem B626345 : Blo 413771 626345 := bstep (se 2 (by rfl) ⟨234879, by rfl⟩ : syracuseStep 626345 = 469759) B469759
theorem B38342483 : Blo 413771 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B790555 : Blo 413771 790555 := bstep (se 1 (by rfl) ⟨592916, by rfl⟩ : syracuseStep 790555 = 1185833) B1185833
theorem B10162259 : Blo 413771 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B2101625 : Blo 413771 2101625 := bstep (se 2 (by rfl) ⟨788109, by rfl⟩ : syracuseStep 2101625 = 1576219) B1576219
theorem B3544991 : Blo 413771 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B1808531 : Blo 413771 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B2530055 : Blo 413771 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B467815 : Blo 413771 467815 := bstep (se 1 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 467815 = 701723) B701723
theorem B3024539 : Blo 413771 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B468895 : Blo 413771 468895 := bstep (se 1 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 468895 = 703343) B703343
theorem B3156569 : Blo 413771 3156569 := bstep (se 2 (by rfl) ⟨1183713, by rfl⟩ : syracuseStep 3156569 = 2367427) B2367427
theorem B4008953 : Blo 413771 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B2240633 : Blo 413771 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B995723 : Blo 413771 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B3553055 : Blo 413771 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B2242883 : Blo 413771 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B702823 : Blo 413771 702823 := bstep (se 1 (by rfl) ⟨527117, by rfl⟩ : syracuseStep 702823 = 1054235) B1054235
theorem B2111993 : Blo 413771 2111993 := bstep (se 2 (by rfl) ⟨791997, by rfl⟩ : syracuseStep 2111993 = 1583995) B1583995
theorem B3160943 : Blo 413771 3160943 := bstep (se 1 (by rfl) ⟨2370707, by rfl⟩ : syracuseStep 3160943 = 4741415) B4741415
theorem B933119 : Blo 413771 933119 := bstep (se 1 (by rfl) ⟨699839, by rfl⟩ : syracuseStep 933119 = 1399679) B1399679
theorem B2113127 : Blo 413771 2113127 := bstep (se 1 (by rfl) ⟨1584845, by rfl⟩ : syracuseStep 2113127 = 3169691) B3169691
theorem B934739 : Blo 413771 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B1002527 : Blo 413771 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B937223 : Blo 413771 937223 := bstep (se 1 (by rfl) ⟨702917, by rfl⟩ : syracuseStep 937223 = 1405835) B1405835
theorem B937727 : Blo 413771 937727 := bstep (se 1 (by rfl) ⟨703295, by rfl⟩ : syracuseStep 937727 = 1406591) B1406591
theorem B3985193 : Blo 413771 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B7229675 : Blo 413771 7229675 := bstep (se 1 (by rfl) ⟨5422256, by rfl⟩ : syracuseStep 7229675 = 10844513) B10844513
theorem B938879 : Blo 413771 938879 := bstep (se 1 (by rfl) ⟨704159, by rfl⟩ : syracuseStep 938879 = 1408319) B1408319
theorem B415167 : Blo 413771 415167 := bstep (se 1 (by rfl) ⟨311375, by rfl⟩ : syracuseStep 415167 = 622751) B622751
theorem B415279 : Blo 413771 415279 := bstep (se 1 (by rfl) ⟨311459, by rfl⟩ : syracuseStep 415279 = 622919) B622919
theorem B415487 : Blo 413771 415487 := bstep (se 1 (by rfl) ⟨311615, by rfl⟩ : syracuseStep 415487 = 623231) B623231
theorem B415591 : Blo 413771 415591 := bstep (se 1 (by rfl) ⟨311693, by rfl⟩ : syracuseStep 415591 = 623387) B623387
theorem B415807 : Blo 413771 415807 := bstep (se 1 (by rfl) ⟨311855, by rfl⟩ : syracuseStep 415807 = 623711) B623711
theorem B415847 : Blo 413771 415847 := bstep (se 1 (by rfl) ⟨311885, by rfl⟩ : syracuseStep 415847 = 623771) B623771
theorem B416539 : Blo 413771 416539 := bstep (se 1 (by rfl) ⟨312404, by rfl⟩ : syracuseStep 416539 = 624809) B624809
theorem B417007 : Blo 413771 417007 := bstep (se 1 (by rfl) ⟨312755, by rfl⟩ : syracuseStep 417007 = 625511) B625511
theorem B1400111 : Blo 413771 1400111 := bstep (se 1 (by rfl) ⟨1050083, by rfl⟩ : syracuseStep 1400111 = 2100167) B2100167
theorem B7561849 : Blo 413771 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B3564263 : Blo 413771 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B45703925 : Blo 413771 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B1404809 : Blo 413771 1404809 := bstep (se 2 (by rfl) ⟨526803, by rfl⟩ : syracuseStep 1404809 = 1053607) B1053607
theorem B2158919 : Blo 413771 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B1997135 : Blo 413771 1997135 := bstep (se 1 (by rfl) ⟨1497851, by rfl⟩ : syracuseStep 1997135 = 2995703) B2995703
theorem B13106555 : Blo 413771 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B15105473 : Blo 413771 15105473 := bstep (se 2 (by rfl) ⟨5664552, by rfl⟩ : syracuseStep 15105473 = 11329105) B11329105
theorem B2653823 : Blo 413771 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B1048403 : Blo 413771 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B623159 : Blo 413771 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B623753 : Blo 413771 623753 := bstep (se 2 (by rfl) ⟨233907, by rfl⟩ : syracuseStep 623753 = 467815) B467815
theorem B526495 : Blo 413771 526495 := bstep (se 1 (by rfl) ⟨394871, by rfl⟩ : syracuseStep 526495 = 789743) B789743
theorem B624815 : Blo 413771 624815 := bstep (se 1 (by rfl) ⟨468611, by rfl⟩ : syracuseStep 624815 = 937223) B937223
theorem B625151 : Blo 413771 625151 := bstep (se 1 (by rfl) ⟨468863, by rfl⟩ : syracuseStep 625151 = 937727) B937727
theorem B2656795 : Blo 413771 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B625193 : Blo 413771 625193 := bstep (se 2 (by rfl) ⟨234447, by rfl⟩ : syracuseStep 625193 = 468895) B468895
theorem B25561655 : Blo 413771 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B4819783 : Blo 413771 4819783 := bstep (se 1 (by rfl) ⟨3614837, by rfl⟩ : syracuseStep 4819783 = 7229675) B7229675
theorem B625919 : Blo 413771 625919 := bstep (se 1 (by rfl) ⟨469439, by rfl⟩ : syracuseStep 625919 = 938879) B938879
theorem B2363327 : Blo 413771 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B1054073 : Blo 413771 1054073 := bstep (se 2 (by rfl) ⟨395277, by rfl⟩ : syracuseStep 1054073 = 790555) B790555
theorem B2104379 : Blo 413771 2104379 := bstep (se 1 (by rfl) ⟨1578284, by rfl⟩ : syracuseStep 2104379 = 3156569) B3156569
theorem B663815 : Blo 413771 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B2368703 : Blo 413771 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B2107295 : Blo 413771 2107295 := bstep (se 1 (by rfl) ⟨1580471, by rfl⟩ : syracuseStep 2107295 = 3160943) B3160943
theorem B10070315 : Blo 413771 10070315 := bstep (se 1 (by rfl) ⟨7552736, by rfl⟩ : syracuseStep 10070315 = 15105473) B15105473
theorem B698935 : Blo 413771 698935 := bstep (se 1 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 698935 = 1048403) B1048403
theorem B5975021 : Blo 413771 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B668351 : Blo 413771 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B701183 : Blo 413771 701183 := bstep (se 1 (by rfl) ⟨525887, by rfl⟩ : syracuseStep 701183 = 1051775) B1051775
theorem B933407 : Blo 413771 933407 := bstep (se 1 (by rfl) ⟨700055, by rfl⟩ : syracuseStep 933407 = 1400111) B1400111
theorem B2376175 : Blo 413771 2376175 := bstep (se 1 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 2376175 = 3564263) B3564263
theorem B2016359 : Blo 413771 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B2672635 : Blo 413771 2672635 := bstep (se 1 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 2672635 = 4008953) B4008953
theorem B936539 : Blo 413771 936539 := bstep (se 1 (by rfl) ⟨702404, by rfl⟩ : syracuseStep 936539 = 1404809) B1404809
theorem B937097 : Blo 413771 937097 := bstep (se 2 (by rfl) ⟨351411, by rfl⟩ : syracuseStep 937097 = 702823) B702823
theorem B1495255 : Blo 413771 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1331423 : Blo 413771 1331423 := bstep (se 1 (by rfl) ⟨998567, by rfl⟩ : syracuseStep 1331423 = 1997135) B1997135
theorem B8737703 : Blo 413771 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B10082465 : Blo 413771 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B417535 : Blo 413771 417535 := bstep (se 1 (by rfl) ⟨313151, by rfl⟩ : syracuseStep 417535 = 626303) B626303
theorem B417563 : Blo 413771 417563 := bstep (se 1 (by rfl) ⟨313172, by rfl⟩ : syracuseStep 417563 = 626345) B626345
theorem B6774839 : Blo 413771 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B1401083 : Blo 413771 1401083 := bstep (se 1 (by rfl) ⟨1050812, by rfl⟩ : syracuseStep 1401083 = 2101625) B2101625
theorem B1205687 : Blo 413771 1205687 := bstep (se 1 (by rfl) ⟨904265, by rfl⟩ : syracuseStep 1205687 = 1808531) B1808531
theorem B1403837 : Blo 413771 1403837 := bstep (se 3 (by rfl) ⟨263219, by rfl⟩ : syracuseStep 1403837 = 526439) B526439
theorem B30469283 : Blo 413771 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B6746813 : Blo 413771 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B1439279 : Blo 413771 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B1407995 : Blo 413771 1407995 := bstep (se 1 (by rfl) ⟨1055996, by rfl⟩ : syracuseStep 1407995 = 2111993) B2111993
theorem B622079 : Blo 413771 622079 := bstep (se 1 (by rfl) ⟨466559, by rfl⟩ : syracuseStep 622079 = 933119) B933119
theorem B1408751 : Blo 413771 1408751 := bstep (se 1 (by rfl) ⟨1056563, by rfl⟩ : syracuseStep 1408751 = 2113127) B2113127
theorem B1769215 : Blo 413771 1769215 := bstep (se 1 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 1769215 = 2653823) B2653823
theorem B1770173 : Blo 413771 1770173 := bstep (se 3 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 1770173 = 663815) B663815
theorem B1344239 : Blo 413771 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B17041103 : Blo 413771 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B624359 : Blo 413771 624359 := bstep (se 1 (by rfl) ⟨468269, by rfl⟩ : syracuseStep 624359 = 936539) B936539
theorem B624731 : Blo 413771 624731 := bstep (se 1 (by rfl) ⟨468548, by rfl⟩ : syracuseStep 624731 = 937097) B937097
theorem B1575551 : Blo 413771 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B887615 : Blo 413771 887615 := bstep (se 1 (by rfl) ⟨665711, by rfl⟩ : syracuseStep 887615 = 1331423) B1331423
theorem B3542393 : Blo 413771 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B6426377 : Blo 413771 6426377 := bstep (se 2 (by rfl) ⟨2409891, by rfl⟩ : syracuseStep 6426377 = 4819783) B4819783
theorem B6721643 : Blo 413771 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B1579135 : Blo 413771 1579135 := bstep (se 1 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 1579135 = 2368703) B2368703
theorem B4497875 : Blo 413771 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B467455 : Blo 413771 467455 := bstep (se 1 (by rfl) ⟨350591, by rfl⟩ : syracuseStep 467455 = 701183) B701183
theorem B959519 : Blo 413771 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B1782269 : Blo 413771 1782269 := bstep (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) B668351
theorem B701993 : Blo 413771 701993 := bstep (se 2 (by rfl) ⟨263247, by rfl⟩ : syracuseStep 701993 = 526495) B526495
theorem B931913 : Blo 413771 931913 := bstep (se 2 (by rfl) ⟨349467, by rfl⟩ : syracuseStep 931913 = 698935) B698935
theorem B702715 : Blo 413771 702715 := bstep (se 1 (by rfl) ⟨527036, by rfl⟩ : syracuseStep 702715 = 1054073) B1054073
theorem B934055 : Blo 413771 934055 := bstep (se 1 (by rfl) ⟨700541, by rfl⟩ : syracuseStep 934055 = 1401083) B1401083
theorem B803791 : Blo 413771 803791 := bstep (se 1 (by rfl) ⟨602843, by rfl⟩ : syracuseStep 803791 = 1205687) B1205687
theorem B935891 : Blo 413771 935891 := bstep (se 1 (by rfl) ⟨701918, by rfl⟩ : syracuseStep 935891 = 1403837) B1403837
theorem B3983347 : Blo 413771 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B938663 : Blo 413771 938663 := bstep (se 1 (by rfl) ⟨703997, by rfl⟩ : syracuseStep 938663 = 1407995) B1407995
theorem B414719 : Blo 413771 414719 := bstep (se 1 (by rfl) ⟨311039, by rfl⟩ : syracuseStep 414719 = 622079) B622079
theorem B939167 : Blo 413771 939167 := bstep (se 1 (by rfl) ⟨704375, by rfl⟩ : syracuseStep 939167 = 1408751) B1408751
theorem B415439 : Blo 413771 415439 := bstep (se 1 (by rfl) ⟨311579, by rfl⟩ : syracuseStep 415439 = 623159) B623159
theorem B3168233 : Blo 413771 3168233 := bstep (se 2 (by rfl) ⟨1188087, by rfl⟩ : syracuseStep 3168233 = 2376175) B2376175
theorem B415835 : Blo 413771 415835 := bstep (se 1 (by rfl) ⟨311876, by rfl⟩ : syracuseStep 415835 = 623753) B623753
theorem B416543 : Blo 413771 416543 := bstep (se 1 (by rfl) ⟨312407, by rfl⟩ : syracuseStep 416543 = 624815) B624815
theorem B416767 : Blo 413771 416767 := bstep (se 1 (by rfl) ⟨312575, by rfl⟩ : syracuseStep 416767 = 625151) B625151
theorem B416795 : Blo 413771 416795 := bstep (se 1 (by rfl) ⟨312596, by rfl⟩ : syracuseStep 416795 = 625193) B625193
theorem B417279 : Blo 413771 417279 := bstep (se 1 (by rfl) ⟨312959, by rfl⟩ : syracuseStep 417279 = 625919) B625919
theorem B3563513 : Blo 413771 3563513 := bstep (se 2 (by rfl) ⟨1336317, by rfl⟩ : syracuseStep 3563513 = 2672635) B2672635
theorem B5825135 : Blo 413771 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B1402919 : Blo 413771 1402919 := bstep (se 1 (by rfl) ⟨1052189, by rfl⟩ : syracuseStep 1402919 = 2104379) B2104379
theorem B4516559 : Blo 413771 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B1993673 : Blo 413771 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B1404863 : Blo 413771 1404863 := bstep (se 1 (by rfl) ⟨1053647, by rfl⟩ : syracuseStep 1404863 = 2107295) B2107295
theorem B6713543 : Blo 413771 6713543 := bstep (se 1 (by rfl) ⟨5035157, by rfl⟩ : syracuseStep 6713543 = 10070315) B10070315
theorem B20312855 : Blo 413771 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B2358953 : Blo 413771 2358953 := bstep (se 2 (by rfl) ⟨884607, by rfl⟩ : syracuseStep 2358953 = 1769215) B1769215
theorem B622271 : Blo 413771 622271 := bstep (se 1 (by rfl) ⟨466703, by rfl⟩ : syracuseStep 622271 = 933407) B933407
theorem B622703 : Blo 413771 622703 := bstep (se 1 (by rfl) ⟨467027, by rfl⟩ : syracuseStep 622703 = 934055) B934055
theorem B1180115 : Blo 413771 1180115 := bstep (se 1 (by rfl) ⟨885086, by rfl⟩ : syracuseStep 1180115 = 1770173) B1770173
theorem B623273 : Blo 413771 623273 := bstep (se 2 (by rfl) ⟨233727, by rfl⟩ : syracuseStep 623273 = 467455) B467455
theorem B623927 : Blo 413771 623927 := bstep (se 1 (by rfl) ⟨467945, by rfl⟩ : syracuseStep 623927 = 935891) B935891
theorem B15533693 : Blo 413771 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B1050367 : Blo 413771 1050367 := bstep (se 1 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 1050367 = 1575551) B1575551
theorem B591743 : Blo 413771 591743 := bstep (se 1 (by rfl) ⟨443807, by rfl⟩ : syracuseStep 591743 = 887615) B887615
theorem B2361595 : Blo 413771 2361595 := bstep (se 1 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 2361595 = 3542393) B3542393
theorem B5311129 : Blo 413771 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B625775 : Blo 413771 625775 := bstep (se 1 (by rfl) ⟨469331, by rfl⟩ : syracuseStep 625775 = 938663) B938663
theorem B626111 : Blo 413771 626111 := bstep (se 1 (by rfl) ⟨469583, by rfl⟩ : syracuseStep 626111 = 939167) B939167
theorem B5316461 : Blo 413771 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B2105513 : Blo 413771 2105513 := bstep (se 2 (by rfl) ⟨789567, by rfl⟩ : syracuseStep 2105513 = 1579135) B1579135
theorem B1188179 : Blo 413771 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B13541903 : Blo 413771 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B467995 : Blo 413771 467995 := bstep (se 1 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 467995 = 701993) B701993
theorem B896159 : Blo 413771 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B2112155 : Blo 413771 2112155 := bstep (se 1 (by rfl) ⟨1584116, by rfl⟩ : syracuseStep 2112155 = 3168233) B3168233
theorem B2375675 : Blo 413771 2375675 := bstep (se 1 (by rfl) ⟨1781756, by rfl⟩ : syracuseStep 2375675 = 3563513) B3563513
theorem B2998583 : Blo 413771 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B639679 : Blo 413771 639679 := bstep (se 1 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 639679 = 959519) B959519
theorem B935279 : Blo 413771 935279 := bstep (se 1 (by rfl) ⟨701459, by rfl⟩ : syracuseStep 935279 = 1402919) B1402919
theorem B936575 : Blo 413771 936575 := bstep (se 1 (by rfl) ⟨702431, by rfl⟩ : syracuseStep 936575 = 1404863) B1404863
theorem B4475695 : Blo 413771 4475695 := bstep (se 1 (by rfl) ⟨3356771, by rfl⟩ : syracuseStep 4475695 = 6713543) B6713543
theorem B936953 : Blo 413771 936953 := bstep (se 2 (by rfl) ⟨351357, by rfl⟩ : syracuseStep 936953 = 702715) B702715
theorem B414847 : Blo 413771 414847 := bstep (se 1 (by rfl) ⟨311135, by rfl⟩ : syracuseStep 414847 = 622271) B622271
theorem B11360735 : Blo 413771 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B416239 : Blo 413771 416239 := bstep (se 1 (by rfl) ⟨312179, by rfl⟩ : syracuseStep 416239 = 624359) B624359
theorem B1071721 : Blo 413771 1071721 := bstep (se 2 (by rfl) ⟨401895, by rfl⟩ : syracuseStep 1071721 = 803791) B803791
theorem B416487 : Blo 413771 416487 := bstep (se 1 (by rfl) ⟨312365, by rfl⟩ : syracuseStep 416487 = 624731) B624731
theorem B4284251 : Blo 413771 4284251 := bstep (se 1 (by rfl) ⟨3213188, by rfl⟩ : syracuseStep 4284251 = 6426377) B6426377
theorem B4481095 : Blo 413771 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B3011039 : Blo 413771 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B621275 : Blo 413771 621275 := bstep (se 1 (by rfl) ⟨465956, by rfl⟩ : syracuseStep 621275 = 931913) B931913
theorem B1572635 : Blo 413771 1572635 := bstep (se 1 (by rfl) ⟨1179476, by rfl⟩ : syracuseStep 1572635 = 2358953) B2358953
theorem B1999055 : Blo 413771 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B786743 : Blo 413771 786743 := bstep (se 1 (by rfl) ⟨590057, by rfl⟩ : syracuseStep 786743 = 1180115) B1180115
theorem B623519 : Blo 413771 623519 := bstep (se 1 (by rfl) ⟨467639, by rfl⟩ : syracuseStep 623519 = 935279) B935279
theorem B852905 : Blo 413771 852905 := bstep (se 2 (by rfl) ⟨319839, by rfl⟩ : syracuseStep 852905 = 639679) B639679
theorem B10355795 : Blo 413771 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B623993 : Blo 413771 623993 := bstep (se 2 (by rfl) ⟨233997, by rfl⟩ : syracuseStep 623993 = 467995) B467995
theorem B624383 : Blo 413771 624383 := bstep (se 1 (by rfl) ⟨468287, by rfl⟩ : syracuseStep 624383 = 936575) B936575
theorem B624635 : Blo 413771 624635 := bstep (se 1 (by rfl) ⟨468476, by rfl⟩ : syracuseStep 624635 = 936953) B936953
theorem B3148793 : Blo 413771 3148793 := bstep (se 2 (by rfl) ⟨1180797, by rfl⟩ : syracuseStep 3148793 = 2361595) B2361595
theorem B7081505 : Blo 413771 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B5967593 : Blo 413771 5967593 := bstep (se 2 (by rfl) ⟨2237847, by rfl⟩ : syracuseStep 5967593 = 4475695) B4475695
theorem B7573823 : Blo 413771 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B1577981 : Blo 413771 1577981 := bstep (se 3 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 1577981 = 591743) B591743
theorem B2856167 : Blo 413771 2856167 := bstep (se 1 (by rfl) ⟨2142125, by rfl⟩ : syracuseStep 2856167 = 4284251) B4284251
theorem B3544307 : Blo 413771 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B792119 : Blo 413771 792119 := bstep (se 1 (by rfl) ⟨594089, by rfl⟩ : syracuseStep 792119 = 1188179) B1188179
theorem B597439 : Blo 413771 597439 := bstep (se 1 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 597439 = 896159) B896159
theorem B2007359 : Blo 413771 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B1583783 : Blo 413771 1583783 := bstep (se 1 (by rfl) ⟨1187837, by rfl⟩ : syracuseStep 1583783 = 2375675) B2375675
theorem B5974793 : Blo 413771 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B9027935 : Blo 413771 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B1428961 : Blo 413771 1428961 := bstep (se 2 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 1428961 = 1071721) B1071721
theorem B414183 : Blo 413771 414183 := bstep (se 1 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 414183 = 621275) B621275
theorem B415135 : Blo 413771 415135 := bstep (se 1 (by rfl) ⟨311351, by rfl⟩ : syracuseStep 415135 = 622703) B622703
theorem B415515 : Blo 413771 415515 := bstep (se 1 (by rfl) ⟨311636, by rfl⟩ : syracuseStep 415515 = 623273) B623273
theorem B415951 : Blo 413771 415951 := bstep (se 1 (by rfl) ⟨311963, by rfl⟩ : syracuseStep 415951 = 623927) B623927
theorem B417183 : Blo 413771 417183 := bstep (se 1 (by rfl) ⟨312887, by rfl⟩ : syracuseStep 417183 = 625775) B625775
theorem B417407 : Blo 413771 417407 := bstep (se 1 (by rfl) ⟨313055, by rfl⟩ : syracuseStep 417407 = 626111) B626111
theorem B1400489 : Blo 413771 1400489 := bstep (se 2 (by rfl) ⟨525183, by rfl⟩ : syracuseStep 1400489 = 1050367) B1050367
theorem B1403675 : Blo 413771 1403675 := bstep (se 1 (by rfl) ⟨1052756, by rfl⟩ : syracuseStep 1403675 = 2105513) B2105513
theorem B1408103 : Blo 413771 1408103 := bstep (se 1 (by rfl) ⟨1056077, by rfl⟩ : syracuseStep 1408103 = 2112155) B2112155
theorem B1048423 : Blo 413771 1048423 := bstep (se 1 (by rfl) ⟨786317, by rfl⟩ : syracuseStep 1048423 = 1572635) B1572635
theorem B524495 : Blo 413771 524495 := bstep (se 1 (by rfl) ⟨393371, by rfl⟩ : syracuseStep 524495 = 786743) B786743
theorem B2099195 : Blo 413771 2099195 := bstep (se 1 (by rfl) ⟨1574396, by rfl⟩ : syracuseStep 2099195 = 3148793) B3148793
theorem B4721003 : Blo 413771 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B5049215 : Blo 413771 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B1051987 : Blo 413771 1051987 := bstep (se 1 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 1051987 = 1577981) B1577981
theorem B1904111 : Blo 413771 1904111 := bstep (se 1 (by rfl) ⟨1428083, by rfl⟩ : syracuseStep 1904111 = 2856167) B2856167
theorem B2362871 : Blo 413771 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B1905281 : Blo 413771 1905281 := bstep (se 2 (by rfl) ⟨714480, by rfl⟩ : syracuseStep 1905281 = 1428961) B1428961
theorem B1055855 : Blo 413771 1055855 := bstep (se 1 (by rfl) ⟨791891, by rfl⟩ : syracuseStep 1055855 = 1583783) B1583783
theorem B3186341 : Blo 413771 3186341 := bstep (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) B597439
theorem B568603 : Blo 413771 568603 := bstep (se 1 (by rfl) ⟨426452, by rfl⟩ : syracuseStep 568603 = 852905) B852905
theorem B3978395 : Blo 413771 3978395 := bstep (se 1 (by rfl) ⟨2983796, by rfl⟩ : syracuseStep 3978395 = 5967593) B5967593
theorem B2112317 : Blo 413771 2112317 := bstep (se 3 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 2112317 = 792119) B792119
theorem B933659 : Blo 413771 933659 := bstep (se 1 (by rfl) ⟨700244, by rfl⟩ : syracuseStep 933659 = 1400489) B1400489
theorem B3983195 : Blo 413771 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B935783 : Blo 413771 935783 := bstep (se 1 (by rfl) ⟨701837, by rfl⟩ : syracuseStep 935783 = 1403675) B1403675
theorem B938735 : Blo 413771 938735 := bstep (se 1 (by rfl) ⟨704051, by rfl⟩ : syracuseStep 938735 = 1408103) B1408103
theorem B1397897 : Blo 413771 1397897 := bstep (se 2 (by rfl) ⟨524211, by rfl⟩ : syracuseStep 1397897 = 1048423) B1048423
theorem B1332703 : Blo 413771 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B6018623 : Blo 413771 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B415679 : Blo 413771 415679 := bstep (se 1 (by rfl) ⟨311759, by rfl⟩ : syracuseStep 415679 = 623519) B623519
theorem B6903863 : Blo 413771 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B415995 : Blo 413771 415995 := bstep (se 1 (by rfl) ⟨311996, by rfl⟩ : syracuseStep 415995 = 623993) B623993
theorem B416255 : Blo 413771 416255 := bstep (se 1 (by rfl) ⟨312191, by rfl⟩ : syracuseStep 416255 = 624383) B624383
theorem B416423 : Blo 413771 416423 := bstep (se 1 (by rfl) ⟨312317, by rfl⟩ : syracuseStep 416423 = 624635) B624635
theorem B1338239 : Blo 413771 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B2655463 : Blo 413771 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B623855 : Blo 413771 623855 := bstep (se 1 (by rfl) ⟨467891, by rfl⟩ : syracuseStep 623855 = 935783) B935783
theorem B3147335 : Blo 413771 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B1575247 : Blo 413771 1575247 := bstep (se 1 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 1575247 = 2362871) B2362871
theorem B625823 : Blo 413771 625823 := bstep (se 1 (by rfl) ⟨469367, by rfl⟩ : syracuseStep 625823 = 938735) B938735
theorem B931931 : Blo 413771 931931 := bstep (se 1 (by rfl) ⟨698948, by rfl⟩ : syracuseStep 931931 = 1397897) B1397897
theorem B4012415 : Blo 413771 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B4602575 : Blo 413771 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B703903 : Blo 413771 703903 := bstep (se 1 (by rfl) ⟨527927, by rfl⟩ : syracuseStep 703903 = 1055855) B1055855
theorem B3032549 : Blo 413771 3032549 := bstep (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) B568603
theorem B1398653 : Blo 413771 1398653 := bstep (se 3 (by rfl) ⟨262247, by rfl⟩ : syracuseStep 1398653 = 524495) B524495
theorem B1399463 : Blo 413771 1399463 := bstep (se 1 (by rfl) ⟨1049597, by rfl⟩ : syracuseStep 1399463 = 2099195) B2099195
theorem B3366143 : Blo 413771 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B1269407 : Blo 413771 1269407 := bstep (se 1 (by rfl) ⟨952055, by rfl⟩ : syracuseStep 1269407 = 1904111) B1904111
theorem B1270187 : Blo 413771 1270187 := bstep (se 1 (by rfl) ⟨952640, by rfl⟩ : syracuseStep 1270187 = 1905281) B1905281
theorem B1402649 : Blo 413771 1402649 := bstep (se 2 (by rfl) ⟨525993, by rfl⟩ : syracuseStep 1402649 = 1051987) B1051987
theorem B2124227 : Blo 413771 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B3568637 : Blo 413771 3568637 := bstep (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) B1338239
theorem B7107749 : Blo 413771 7107749 := bstep (se 4 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 7107749 = 1332703) B1332703
theorem B2652263 : Blo 413771 2652263 := bstep (se 1 (by rfl) ⟨1989197, by rfl⟩ : syracuseStep 2652263 = 3978395) B3978395
theorem B1408211 : Blo 413771 1408211 := bstep (se 1 (by rfl) ⟨1056158, by rfl⟩ : syracuseStep 1408211 = 2112317) B2112317
theorem B622439 : Blo 413771 622439 := bstep (se 1 (by rfl) ⟨466829, by rfl⟩ : syracuseStep 622439 = 933659) B933659
theorem B2098223 : Blo 413771 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B3540617 : Blo 413771 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B2100329 : Blo 413771 2100329 := bstep (se 2 (by rfl) ⟨787623, by rfl⟩ : syracuseStep 2100329 = 1575247) B1575247
theorem B1416151 : Blo 413771 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B932435 : Blo 413771 932435 := bstep (se 1 (by rfl) ⟨699326, by rfl⟩ : syracuseStep 932435 = 1398653) B1398653
theorem B932975 : Blo 413771 932975 := bstep (se 1 (by rfl) ⟨699731, by rfl⟩ : syracuseStep 932975 = 1399463) B1399463
theorem B2244095 : Blo 413771 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B935099 : Blo 413771 935099 := bstep (se 1 (by rfl) ⟨701324, by rfl⟩ : syracuseStep 935099 = 1402649) B1402649
theorem B2379091 : Blo 413771 2379091 := bstep (se 1 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 2379091 = 3568637) B3568637
theorem B4738499 : Blo 413771 4738499 := bstep (se 1 (by rfl) ⟨3553874, by rfl⟩ : syracuseStep 4738499 = 7107749) B7107749
theorem B2674943 : Blo 413771 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B3068383 : Blo 413771 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B938537 : Blo 413771 938537 := bstep (se 2 (by rfl) ⟨351951, by rfl⟩ : syracuseStep 938537 = 703903) B703903
theorem B938807 : Blo 413771 938807 := bstep (se 1 (by rfl) ⟨704105, by rfl⟩ : syracuseStep 938807 = 1408211) B1408211
theorem B414959 : Blo 413771 414959 := bstep (se 1 (by rfl) ⟨311219, by rfl⟩ : syracuseStep 414959 = 622439) B622439
theorem B415903 : Blo 413771 415903 := bstep (se 1 (by rfl) ⟨311927, by rfl⟩ : syracuseStep 415903 = 623855) B623855
theorem B2021699 : Blo 413771 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B417215 : Blo 413771 417215 := bstep (se 1 (by rfl) ⟨312911, by rfl⟩ : syracuseStep 417215 = 625823) B625823
theorem B846271 : Blo 413771 846271 := bstep (se 1 (by rfl) ⟨634703, by rfl⟩ : syracuseStep 846271 = 1269407) B1269407
theorem B846791 : Blo 413771 846791 := bstep (se 1 (by rfl) ⟨635093, by rfl⟩ : syracuseStep 846791 = 1270187) B1270187
theorem B621287 : Blo 413771 621287 := bstep (se 1 (by rfl) ⟨465965, by rfl⟩ : syracuseStep 621287 = 931931) B931931
theorem B1768175 : Blo 413771 1768175 := bstep (se 1 (by rfl) ⟨1326131, by rfl⟩ : syracuseStep 1768175 = 2652263) B2652263
theorem B623399 : Blo 413771 623399 := bstep (se 1 (by rfl) ⟨467549, by rfl⟩ : syracuseStep 623399 = 935099) B935099
theorem B2360411 : Blo 413771 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B625691 : Blo 413771 625691 := bstep (se 1 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 625691 = 938537) B938537
theorem B625871 : Blo 413771 625871 := bstep (se 1 (by rfl) ⟨469403, by rfl⟩ : syracuseStep 625871 = 938807) B938807
theorem B564527 : Blo 413771 564527 := bstep (se 1 (by rfl) ⟨423395, by rfl⟩ : syracuseStep 564527 = 846791) B846791
theorem B3158999 : Blo 413771 3158999 := bstep (se 1 (by rfl) ⟨2369249, by rfl⟩ : syracuseStep 3158999 = 4738499) B4738499
theorem B1783295 : Blo 413771 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B5391197 : Blo 413771 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B1888201 : Blo 413771 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B414191 : Blo 413771 414191 := bstep (se 1 (by rfl) ⟨310643, by rfl⟩ : syracuseStep 414191 = 621287) B621287
theorem B1496063 : Blo 413771 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B1398815 : Blo 413771 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B1400219 : Blo 413771 1400219 := bstep (se 1 (by rfl) ⟨1050164, by rfl⟩ : syracuseStep 1400219 = 2100329) B2100329
theorem B4513445 : Blo 413771 4513445 := bstep (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) B846271
theorem B3172121 : Blo 413771 3172121 := bstep (se 2 (by rfl) ⟨1189545, by rfl⟩ : syracuseStep 3172121 = 2379091) B2379091
theorem B4091177 : Blo 413771 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B621623 : Blo 413771 621623 := bstep (se 1 (by rfl) ⟨466217, by rfl⟩ : syracuseStep 621623 = 932435) B932435
theorem B1178783 : Blo 413771 1178783 := bstep (se 1 (by rfl) ⟨884087, by rfl⟩ : syracuseStep 1178783 = 1768175) B1768175
theorem B621983 : Blo 413771 621983 := bstep (se 1 (by rfl) ⟨466487, by rfl⟩ : syracuseStep 621983 = 932975) B932975
theorem B1573607 : Blo 413771 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B2727451 : Blo 413771 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B2105999 : Blo 413771 2105999 := bstep (se 1 (by rfl) ⟨1579499, by rfl⟩ : syracuseStep 2105999 = 3158999) B3158999
theorem B1188863 : Blo 413771 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B997375 : Blo 413771 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B932543 : Blo 413771 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B933479 : Blo 413771 933479 := bstep (se 1 (by rfl) ⟨700109, by rfl⟩ : syracuseStep 933479 = 1400219) B1400219
theorem B2114747 : Blo 413771 2114747 := bstep (se 1 (by rfl) ⟨1586060, by rfl⟩ : syracuseStep 2114747 = 3172121) B3172121
theorem B414415 : Blo 413771 414415 := bstep (se 1 (by rfl) ⟨310811, by rfl⟩ : syracuseStep 414415 = 621623) B621623
theorem B414655 : Blo 413771 414655 := bstep (se 1 (by rfl) ⟨310991, by rfl⟩ : syracuseStep 414655 = 621983) B621983
theorem B415599 : Blo 413771 415599 := bstep (se 1 (by rfl) ⟨311699, by rfl⟩ : syracuseStep 415599 = 623399) B623399
theorem B3594131 : Blo 413771 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B417127 : Blo 413771 417127 := bstep (se 1 (by rfl) ⟨312845, by rfl⟩ : syracuseStep 417127 = 625691) B625691
theorem B417247 : Blo 413771 417247 := bstep (se 1 (by rfl) ⟨312935, by rfl⟩ : syracuseStep 417247 = 625871) B625871
theorem B3008963 : Blo 413771 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B2517601 : Blo 413771 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B1505405 : Blo 413771 1505405 := bstep (se 3 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 1505405 = 564527) B564527
theorem B785855 : Blo 413771 785855 := bstep (se 1 (by rfl) ⟨589391, by rfl⟩ : syracuseStep 785855 = 1178783) B1178783
theorem B1049071 : Blo 413771 1049071 := bstep (se 1 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 1049071 = 1573607) B1573607
theorem B1409831 : Blo 413771 1409831 := bstep (se 1 (by rfl) ⟨1057373, by rfl⟩ : syracuseStep 1409831 = 2114747) B2114747
theorem B2396087 : Blo 413771 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B792575 : Blo 413771 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B2005975 : Blo 413771 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B3356801 : Blo 413771 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B1329833 : Blo 413771 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B1003603 : Blo 413771 1003603 := bstep (se 1 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 1003603 = 1505405) B1505405
theorem B1403999 : Blo 413771 1403999 := bstep (se 1 (by rfl) ⟨1052999, by rfl⟩ : syracuseStep 1403999 = 2105999) B2105999
theorem B14546405 : Blo 413771 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B621695 : Blo 413771 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B523903 : Blo 413771 523903 := bstep (se 1 (by rfl) ⟨392927, by rfl⟩ : syracuseStep 523903 = 785855) B785855
theorem B622319 : Blo 413771 622319 := bstep (se 1 (by rfl) ⟨466739, by rfl⟩ : syracuseStep 622319 = 933479) B933479
theorem B886555 : Blo 413771 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B528383 : Blo 413771 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B2237867 : Blo 413771 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B698537 : Blo 413771 698537 := bstep (se 2 (by rfl) ⟨261951, by rfl⟩ : syracuseStep 698537 = 523903) B523903
theorem B935999 : Blo 413771 935999 := bstep (se 1 (by rfl) ⟨701999, by rfl⟩ : syracuseStep 935999 = 1403999) B1403999
theorem B2674633 : Blo 413771 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B414463 : Blo 413771 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B414879 : Blo 413771 414879 := bstep (se 1 (by rfl) ⟨311159, by rfl⟩ : syracuseStep 414879 = 622319) B622319
theorem B939887 : Blo 413771 939887 := bstep (se 1 (by rfl) ⟨704915, by rfl⟩ : syracuseStep 939887 = 1409831) B1409831
theorem B1398761 : Blo 413771 1398761 := bstep (se 2 (by rfl) ⟨524535, by rfl⟩ : syracuseStep 1398761 = 1049071) B1049071
theorem B1597391 : Blo 413771 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B1338137 : Blo 413771 1338137 := bstep (se 2 (by rfl) ⟨501801, by rfl⟩ : syracuseStep 1338137 = 1003603) B1003603
theorem B9697603 : Blo 413771 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B623999 : Blo 413771 623999 := bstep (se 1 (by rfl) ⟨467999, by rfl⟩ : syracuseStep 623999 = 935999) B935999
theorem B626591 : Blo 413771 626591 := bstep (se 1 (by rfl) ⟨469943, by rfl⟩ : syracuseStep 626591 = 939887) B939887
theorem B465691 : Blo 413771 465691 := bstep (se 1 (by rfl) ⟨349268, by rfl⟩ : syracuseStep 465691 = 698537) B698537
theorem B892091 : Blo 413771 892091 := bstep (se 1 (by rfl) ⟨669068, by rfl⟩ : syracuseStep 892091 = 1338137) B1338137
theorem B4728293 : Blo 413771 4728293 := bstep (se 4 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 4728293 = 886555) B886555
theorem B1409021 : Blo 413771 1409021 := bstep (se 3 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 1409021 = 528383) B528383
theorem B932507 : Blo 413771 932507 := bstep (se 1 (by rfl) ⟨699380, by rfl⟩ : syracuseStep 932507 = 1398761) B1398761
theorem B1064927 : Blo 413771 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B1491911 : Blo 413771 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B12930137 : Blo 413771 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B3566177 : Blo 413771 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B8620091 : Blo 413771 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B3152195 : Blo 413771 3152195 := bstep (se 1 (by rfl) ⟨2364146, by rfl⟩ : syracuseStep 3152195 = 4728293) B4728293
theorem B994607 : Blo 413771 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B2377451 : Blo 413771 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B2378909 : Blo 413771 2378909 := bstep (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) B892091
theorem B2839805 : Blo 413771 2839805 := bstep (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) B1064927
theorem B939347 : Blo 413771 939347 := bstep (se 1 (by rfl) ⟨704510, by rfl⟩ : syracuseStep 939347 = 1409021) B1409021
theorem B415999 : Blo 413771 415999 := bstep (se 1 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 415999 = 623999) B623999
theorem B417727 : Blo 413771 417727 := bstep (se 1 (by rfl) ⟨313295, by rfl⟩ : syracuseStep 417727 = 626591) B626591
theorem B620921 : Blo 413771 620921 := bstep (se 2 (by rfl) ⟨232845, by rfl⟩ : syracuseStep 620921 = 465691) B465691
theorem B621671 : Blo 413771 621671 := bstep (se 1 (by rfl) ⟨466253, by rfl⟩ : syracuseStep 621671 = 932507) B932507
theorem B626231 : Blo 413771 626231 := bstep (se 1 (by rfl) ⟨469673, by rfl⟩ : syracuseStep 626231 = 939347) B939347
theorem B2101463 : Blo 413771 2101463 := bstep (se 1 (by rfl) ⟨1576097, by rfl⟩ : syracuseStep 2101463 = 3152195) B3152195
theorem B663071 : Blo 413771 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B1584967 : Blo 413771 1584967 := bstep (se 1 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 1584967 = 2377451) B2377451
theorem B5746727 : Blo 413771 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B1585939 : Blo 413771 1585939 := bstep (se 1 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 1585939 = 2378909) B2378909
theorem B413947 : Blo 413771 413947 := bstep (se 1 (by rfl) ⟨310460, by rfl⟩ : syracuseStep 413947 = 620921) B620921
theorem B414447 : Blo 413771 414447 := bstep (se 1 (by rfl) ⟨310835, by rfl⟩ : syracuseStep 414447 = 621671) B621671
theorem B1893203 : Blo 413771 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B2113289 : Blo 413771 2113289 := bstep (se 2 (by rfl) ⟨792483, by rfl⟩ : syracuseStep 2113289 = 1584967) B1584967
theorem B1262135 : Blo 413771 1262135 := bstep (se 1 (by rfl) ⟨946601, by rfl⟩ : syracuseStep 1262135 = 1893203) B1893203
theorem B2114585 : Blo 413771 2114585 := bstep (se 2 (by rfl) ⟨792969, by rfl⟩ : syracuseStep 2114585 = 1585939) B1585939
theorem B417487 : Blo 413771 417487 := bstep (se 1 (by rfl) ⟨313115, by rfl⟩ : syracuseStep 417487 = 626231) B626231
theorem B1400975 : Blo 413771 1400975 := bstep (se 1 (by rfl) ⟨1050731, by rfl⟩ : syracuseStep 1400975 = 2101463) B2101463
theorem B7072757 : Blo 413771 7072757 := bstep (se 5 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 7072757 = 663071) B663071
theorem B3831151 : Blo 413771 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B1409723 : Blo 413771 1409723 := bstep (se 1 (by rfl) ⟨1057292, by rfl⟩ : syracuseStep 1409723 = 2114585) B2114585
theorem B933983 : Blo 413771 933983 := bstep (se 1 (by rfl) ⟨700487, by rfl⟩ : syracuseStep 933983 = 1400975) B1400975
theorem B841423 : Blo 413771 841423 := bstep (se 1 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 841423 = 1262135) B1262135
theorem B5108201 : Blo 413771 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B4715171 : Blo 413771 4715171 := bstep (se 1 (by rfl) ⟨3536378, by rfl⟩ : syracuseStep 4715171 = 7072757) B7072757
theorem B1408859 : Blo 413771 1408859 := bstep (se 1 (by rfl) ⟨1056644, by rfl⟩ : syracuseStep 1408859 = 2113289) B2113289
theorem B622655 : Blo 413771 622655 := bstep (se 1 (by rfl) ⟨466991, by rfl⟩ : syracuseStep 622655 = 933983) B933983
theorem B1121897 : Blo 413771 1121897 := bstep (se 2 (by rfl) ⟨420711, by rfl⟩ : syracuseStep 1121897 = 841423) B841423
theorem B939239 : Blo 413771 939239 := bstep (se 1 (by rfl) ⟨704429, by rfl⟩ : syracuseStep 939239 = 1408859) B1408859
theorem B939815 : Blo 413771 939815 := bstep (se 1 (by rfl) ⟨704861, by rfl⟩ : syracuseStep 939815 = 1409723) B1409723
theorem B3405467 : Blo 413771 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B3143447 : Blo 413771 3143447 := bstep (se 1 (by rfl) ⟨2357585, by rfl⟩ : syracuseStep 3143447 = 4715171) B4715171
theorem B626159 : Blo 413771 626159 := bstep (se 1 (by rfl) ⟨469619, by rfl⟩ : syracuseStep 626159 = 939239) B939239
theorem B626543 : Blo 413771 626543 := bstep (se 1 (by rfl) ⟨469907, by rfl⟩ : syracuseStep 626543 = 939815) B939815
theorem B2270311 : Blo 413771 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B2991725 : Blo 413771 2991725 := bstep (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) B1121897
theorem B415103 : Blo 413771 415103 := bstep (se 1 (by rfl) ⟨311327, by rfl⟩ : syracuseStep 415103 = 622655) B622655
theorem B2095631 : Blo 413771 2095631 := bstep (se 1 (by rfl) ⟨1571723, by rfl⟩ : syracuseStep 2095631 = 3143447) B3143447
theorem B12108325 : Blo 413771 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B1397087 : Blo 413771 1397087 := bstep (se 1 (by rfl) ⟨1047815, by rfl⟩ : syracuseStep 1397087 = 2095631) B2095631
theorem B417439 : Blo 413771 417439 := bstep (se 1 (by rfl) ⟨313079, by rfl⟩ : syracuseStep 417439 = 626159) B626159
theorem B417695 : Blo 413771 417695 := bstep (se 1 (by rfl) ⟨313271, by rfl⟩ : syracuseStep 417695 = 626543) B626543
theorem B1994483 : Blo 413771 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B931391 : Blo 413771 931391 := bstep (se 1 (by rfl) ⟨698543, by rfl⟩ : syracuseStep 931391 = 1397087) B1397087
theorem B1329655 : Blo 413771 1329655 := bstep (se 1 (by rfl) ⟨997241, by rfl⟩ : syracuseStep 1329655 = 1994483) B1994483
theorem B16144433 : Blo 413771 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B1772873 : Blo 413771 1772873 := bstep (se 2 (by rfl) ⟨664827, by rfl⟩ : syracuseStep 1772873 = 1329655) B1329655
theorem B10762955 : Blo 413771 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B620927 : Blo 413771 620927 := bstep (se 1 (by rfl) ⟨465695, by rfl⟩ : syracuseStep 620927 = 931391) B931391
theorem B1181915 : Blo 413771 1181915 := bstep (se 1 (by rfl) ⟨886436, by rfl⟩ : syracuseStep 1181915 = 1772873) B1772873
theorem B413951 : Blo 413771 413951 := bstep (se 1 (by rfl) ⟨310463, by rfl⟩ : syracuseStep 413951 = 620927) B620927
theorem B7175303 : Blo 413771 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B787943 : Blo 413771 787943 := bstep (se 1 (by rfl) ⟨590957, by rfl⟩ : syracuseStep 787943 = 1181915) B1181915
theorem B4783535 : Blo 413771 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B525295 : Blo 413771 525295 := bstep (se 1 (by rfl) ⟨393971, by rfl⟩ : syracuseStep 525295 = 787943) B787943
theorem B3189023 : Blo 413771 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B700393 : Blo 413771 700393 := bstep (se 2 (by rfl) ⟨262647, by rfl⟩ : syracuseStep 700393 = 525295) B525295
theorem B2126015 : Blo 413771 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B1417343 : Blo 413771 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B933857 : Blo 413771 933857 := bstep (se 2 (by rfl) ⟨350196, by rfl⟩ : syracuseStep 933857 = 700393) B700393
theorem B3779581 : Blo 413771 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B622571 : Blo 413771 622571 := bstep (se 1 (by rfl) ⟨466928, by rfl⟩ : syracuseStep 622571 = 933857) B933857
theorem B415047 : Blo 413771 415047 := bstep (se 1 (by rfl) ⟨311285, by rfl⟩ : syracuseStep 415047 = 622571) B622571
theorem B5039441 : Blo 413771 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B3359627 : Blo 413771 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B2239751 : Blo 413771 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B1493167 : Blo 413771 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B1990889 : Blo 413771 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B1327259 : Blo 413771 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889
theorem B884839 : Blo 413771 884839 := bstep (se 1 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 884839 = 1327259) B1327259
theorem B1179785 : Blo 413771 1179785 := bstep (se 2 (by rfl) ⟨442419, by rfl⟩ : syracuseStep 1179785 = 884839) B884839
theorem B786523 : Blo 413771 786523 := bstep (se 1 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 786523 = 1179785) B1179785
theorem B1048697 : Blo 413771 1048697 := bstep (se 2 (by rfl) ⟨393261, by rfl⟩ : syracuseStep 1048697 = 786523) B786523
theorem B699131 : Blo 413771 699131 := bstep (se 1 (by rfl) ⟨524348, by rfl⟩ : syracuseStep 699131 = 1048697) B1048697
theorem B466087 : Blo 413771 466087 := bstep (se 1 (by rfl) ⟨349565, by rfl⟩ : syracuseStep 466087 = 699131) B699131
theorem B621449 : Blo 413771 621449 := bstep (se 2 (by rfl) ⟨233043, by rfl⟩ : syracuseStep 621449 = 466087) B466087
theorem B414299 : Blo 413771 414299 := bstep (se 1 (by rfl) ⟨310724, by rfl⟩ : syracuseStep 414299 = 621449) B621449

theorem C0 (j : ℕ) (h1 : 103442 ≤ j) (h2 : j ≤ 104141) : Blo 413771 (4 * j + 3) := by
  interval_cases j
  · exact B413771
  · exact B413775
  · exact B413779
  · exact B413783
  · exact B413787
  · exact B413791
  · exact B413795
  · exact B413799
  · exact B413803
  · exact B413807
  · exact B413811
  · exact B413815
  · exact B413819
  · exact B413823
  · exact B413827
  · exact B413831
  · exact B413835
  · exact B413839
  · exact B413843
  · exact B413847
  · exact B413851
  · exact B413855
  · exact B413859
  · exact B413863
  · exact B413867
  · exact B413871
  · exact B413875
  · exact B413879
  · exact B413883
  · exact B413887
  · exact B413891
  · exact B413895
  · exact B413899
  · exact B413903
  · exact B413907
  · exact B413911
  · exact B413915
  · exact B413919
  · exact B413923
  · exact B413927
  · exact B413931
  · exact B413935
  · exact B413939
  · exact B413943
  · exact B413947
  · exact B413951
  · exact B413955
  · exact B413959
  · exact B413963
  · exact B413967
  · exact B413971
  · exact B413975
  · exact B413979
  · exact B413983
  · exact B413987
  · exact B413991
  · exact B413995
  · exact B413999
  · exact B414003
  · exact B414007
  · exact B414011
  · exact B414015
  · exact B414019
  · exact B414023
  · exact B414027
  · exact B414031
  · exact B414035
  · exact B414039
  · exact B414043
  · exact B414047
  · exact B414051
  · exact B414055
  · exact B414059
  · exact B414063
  · exact B414067
  · exact B414071
  · exact B414075
  · exact B414079
  · exact B414083
  · exact B414087
  · exact B414091
  · exact B414095
  · exact B414099
  · exact B414103
  · exact B414107
  · exact B414111
  · exact B414115
  · exact B414119
  · exact B414123
  · exact B414127
  · exact B414131
  · exact B414135
  · exact B414139
  · exact B414143
  · exact B414147
  · exact B414151
  · exact B414155
  · exact B414159
  · exact B414163
  · exact B414167
  · exact B414171
  · exact B414175
  · exact B414179
  · exact B414183
  · exact B414187
  · exact B414191
  · exact B414195
  · exact B414199
  · exact B414203
  · exact B414207
  · exact B414211
  · exact B414215
  · exact B414219
  · exact B414223
  · exact B414227
  · exact B414231
  · exact B414235
  · exact B414239
  · exact B414243
  · exact B414247
  · exact B414251
  · exact B414255
  · exact B414259
  · exact B414263
  · exact B414267
  · exact B414271
  · exact B414275
  · exact B414279
  · exact B414283
  · exact B414287
  · exact B414291
  · exact B414295
  · exact B414299
  · exact B414303
  · exact B414307
  · exact B414311
  · exact B414315
  · exact B414319
  · exact B414323
  · exact B414327
  · exact B414331
  · exact B414335
  · exact B414339
  · exact B414343
  · exact B414347
  · exact B414351
  · exact B414355
  · exact B414359
  · exact B414363
  · exact B414367
  · exact B414371
  · exact B414375
  · exact B414379
  · exact B414383
  · exact B414387
  · exact B414391
  · exact B414395
  · exact B414399
  · exact B414403
  · exact B414407
  · exact B414411
  · exact B414415
  · exact B414419
  · exact B414423
  · exact B414427
  · exact B414431
  · exact B414435
  · exact B414439
  · exact B414443
  · exact B414447
  · exact B414451
  · exact B414455
  · exact B414459
  · exact B414463
  · exact B414467
  · exact B414471
  · exact B414475
  · exact B414479
  · exact B414483
  · exact B414487
  · exact B414491
  · exact B414495
  · exact B414499
  · exact B414503
  · exact B414507
  · exact B414511
  · exact B414515
  · exact B414519
  · exact B414523
  · exact B414527
  · exact B414531
  · exact B414535
  · exact B414539
  · exact B414543
  · exact B414547
  · exact B414551
  · exact B414555
  · exact B414559
  · exact B414563
  · exact B414567
  · exact B414571
  · exact B414575
  · exact B414579
  · exact B414583
  · exact B414587
  · exact B414591
  · exact B414595
  · exact B414599
  · exact B414603
  · exact B414607
  · exact B414611
  · exact B414615
  · exact B414619
  · exact B414623
  · exact B414627
  · exact B414631
  · exact B414635
  · exact B414639
  · exact B414643
  · exact B414647
  · exact B414651
  · exact B414655
  · exact B414659
  · exact B414663
  · exact B414667
  · exact B414671
  · exact B414675
  · exact B414679
  · exact B414683
  · exact B414687
  · exact B414691
  · exact B414695
  · exact B414699
  · exact B414703
  · exact B414707
  · exact B414711
  · exact B414715
  · exact B414719
  · exact B414723
  · exact B414727
  · exact B414731
  · exact B414735
  · exact B414739
  · exact B414743
  · exact B414747
  · exact B414751
  · exact B414755
  · exact B414759
  · exact B414763
  · exact B414767
  · exact B414771
  · exact B414775
  · exact B414779
  · exact B414783
  · exact B414787
  · exact B414791
  · exact B414795
  · exact B414799
  · exact B414803
  · exact B414807
  · exact B414811
  · exact B414815
  · exact B414819
  · exact B414823
  · exact B414827
  · exact B414831
  · exact B414835
  · exact B414839
  · exact B414843
  · exact B414847
  · exact B414851
  · exact B414855
  · exact B414859
  · exact B414863
  · exact B414867
  · exact B414871
  · exact B414875
  · exact B414879
  · exact B414883
  · exact B414887
  · exact B414891
  · exact B414895
  · exact B414899
  · exact B414903
  · exact B414907
  · exact B414911
  · exact B414915
  · exact B414919
  · exact B414923
  · exact B414927
  · exact B414931
  · exact B414935
  · exact B414939
  · exact B414943
  · exact B414947
  · exact B414951
  · exact B414955
  · exact B414959
  · exact B414963
  · exact B414967
  · exact B414971
  · exact B414975
  · exact B414979
  · exact B414983
  · exact B414987
  · exact B414991
  · exact B414995
  · exact B414999
  · exact B415003
  · exact B415007
  · exact B415011
  · exact B415015
  · exact B415019
  · exact B415023
  · exact B415027
  · exact B415031
  · exact B415035
  · exact B415039
  · exact B415043
  · exact B415047
  · exact B415051
  · exact B415055
  · exact B415059
  · exact B415063
  · exact B415067
  · exact B415071
  · exact B415075
  · exact B415079
  · exact B415083
  · exact B415087
  · exact B415091
  · exact B415095
  · exact B415099
  · exact B415103
  · exact B415107
  · exact B415111
  · exact B415115
  · exact B415119
  · exact B415123
  · exact B415127
  · exact B415131
  · exact B415135
  · exact B415139
  · exact B415143
  · exact B415147
  · exact B415151
  · exact B415155
  · exact B415159
  · exact B415163
  · exact B415167
  · exact B415171
  · exact B415175
  · exact B415179
  · exact B415183
  · exact B415187
  · exact B415191
  · exact B415195
  · exact B415199
  · exact B415203
  · exact B415207
  · exact B415211
  · exact B415215
  · exact B415219
  · exact B415223
  · exact B415227
  · exact B415231
  · exact B415235
  · exact B415239
  · exact B415243
  · exact B415247
  · exact B415251
  · exact B415255
  · exact B415259
  · exact B415263
  · exact B415267
  · exact B415271
  · exact B415275
  · exact B415279
  · exact B415283
  · exact B415287
  · exact B415291
  · exact B415295
  · exact B415299
  · exact B415303
  · exact B415307
  · exact B415311
  · exact B415315
  · exact B415319
  · exact B415323
  · exact B415327
  · exact B415331
  · exact B415335
  · exact B415339
  · exact B415343
  · exact B415347
  · exact B415351
  · exact B415355
  · exact B415359
  · exact B415363
  · exact B415367
  · exact B415371
  · exact B415375
  · exact B415379
  · exact B415383
  · exact B415387
  · exact B415391
  · exact B415395
  · exact B415399
  · exact B415403
  · exact B415407
  · exact B415411
  · exact B415415
  · exact B415419
  · exact B415423
  · exact B415427
  · exact B415431
  · exact B415435
  · exact B415439
  · exact B415443
  · exact B415447
  · exact B415451
  · exact B415455
  · exact B415459
  · exact B415463
  · exact B415467
  · exact B415471
  · exact B415475
  · exact B415479
  · exact B415483
  · exact B415487
  · exact B415491
  · exact B415495
  · exact B415499
  · exact B415503
  · exact B415507
  · exact B415511
  · exact B415515
  · exact B415519
  · exact B415523
  · exact B415527
  · exact B415531
  · exact B415535
  · exact B415539
  · exact B415543
  · exact B415547
  · exact B415551
  · exact B415555
  · exact B415559
  · exact B415563
  · exact B415567
  · exact B415571
  · exact B415575
  · exact B415579
  · exact B415583
  · exact B415587
  · exact B415591
  · exact B415595
  · exact B415599
  · exact B415603
  · exact B415607
  · exact B415611
  · exact B415615
  · exact B415619
  · exact B415623
  · exact B415627
  · exact B415631
  · exact B415635
  · exact B415639
  · exact B415643
  · exact B415647
  · exact B415651
  · exact B415655
  · exact B415659
  · exact B415663
  · exact B415667
  · exact B415671
  · exact B415675
  · exact B415679
  · exact B415683
  · exact B415687
  · exact B415691
  · exact B415695
  · exact B415699
  · exact B415703
  · exact B415707
  · exact B415711
  · exact B415715
  · exact B415719
  · exact B415723
  · exact B415727
  · exact B415731
  · exact B415735
  · exact B415739
  · exact B415743
  · exact B415747
  · exact B415751
  · exact B415755
  · exact B415759
  · exact B415763
  · exact B415767
  · exact B415771
  · exact B415775
  · exact B415779
  · exact B415783
  · exact B415787
  · exact B415791
  · exact B415795
  · exact B415799
  · exact B415803
  · exact B415807
  · exact B415811
  · exact B415815
  · exact B415819
  · exact B415823
  · exact B415827
  · exact B415831
  · exact B415835
  · exact B415839
  · exact B415843
  · exact B415847
  · exact B415851
  · exact B415855
  · exact B415859
  · exact B415863
  · exact B415867
  · exact B415871
  · exact B415875
  · exact B415879
  · exact B415883
  · exact B415887
  · exact B415891
  · exact B415895
  · exact B415899
  · exact B415903
  · exact B415907
  · exact B415911
  · exact B415915
  · exact B415919
  · exact B415923
  · exact B415927
  · exact B415931
  · exact B415935
  · exact B415939
  · exact B415943
  · exact B415947
  · exact B415951
  · exact B415955
  · exact B415959
  · exact B415963
  · exact B415967
  · exact B415971
  · exact B415975
  · exact B415979
  · exact B415983
  · exact B415987
  · exact B415991
  · exact B415995
  · exact B415999
  · exact B416003
  · exact B416007
  · exact B416011
  · exact B416015
  · exact B416019
  · exact B416023
  · exact B416027
  · exact B416031
  · exact B416035
  · exact B416039
  · exact B416043
  · exact B416047
  · exact B416051
  · exact B416055
  · exact B416059
  · exact B416063
  · exact B416067
  · exact B416071
  · exact B416075
  · exact B416079
  · exact B416083
  · exact B416087
  · exact B416091
  · exact B416095
  · exact B416099
  · exact B416103
  · exact B416107
  · exact B416111
  · exact B416115
  · exact B416119
  · exact B416123
  · exact B416127
  · exact B416131
  · exact B416135
  · exact B416139
  · exact B416143
  · exact B416147
  · exact B416151
  · exact B416155
  · exact B416159
  · exact B416163
  · exact B416167
  · exact B416171
  · exact B416175
  · exact B416179
  · exact B416183
  · exact B416187
  · exact B416191
  · exact B416195
  · exact B416199
  · exact B416203
  · exact B416207
  · exact B416211
  · exact B416215
  · exact B416219
  · exact B416223
  · exact B416227
  · exact B416231
  · exact B416235
  · exact B416239
  · exact B416243
  · exact B416247
  · exact B416251
  · exact B416255
  · exact B416259
  · exact B416263
  · exact B416267
  · exact B416271
  · exact B416275
  · exact B416279
  · exact B416283
  · exact B416287
  · exact B416291
  · exact B416295
  · exact B416299
  · exact B416303
  · exact B416307
  · exact B416311
  · exact B416315
  · exact B416319
  · exact B416323
  · exact B416327
  · exact B416331
  · exact B416335
  · exact B416339
  · exact B416343
  · exact B416347
  · exact B416351
  · exact B416355
  · exact B416359
  · exact B416363
  · exact B416367
  · exact B416371
  · exact B416375
  · exact B416379
  · exact B416383
  · exact B416387
  · exact B416391
  · exact B416395
  · exact B416399
  · exact B416403
  · exact B416407
  · exact B416411
  · exact B416415
  · exact B416419
  · exact B416423
  · exact B416427
  · exact B416431
  · exact B416435
  · exact B416439
  · exact B416443
  · exact B416447
  · exact B416451
  · exact B416455
  · exact B416459
  · exact B416463
  · exact B416467
  · exact B416471
  · exact B416475
  · exact B416479
  · exact B416483
  · exact B416487
  · exact B416491
  · exact B416495
  · exact B416499
  · exact B416503
  · exact B416507
  · exact B416511
  · exact B416515
  · exact B416519
  · exact B416523
  · exact B416527
  · exact B416531
  · exact B416535
  · exact B416539
  · exact B416543
  · exact B416547
  · exact B416551
  · exact B416555
  · exact B416559
  · exact B416563
  · exact B416567

theorem C1 (j : ℕ) (h1 : 104142 ≤ j) (h2 : j ≤ 104442) : Blo 413771 (4 * j + 3) := by
  interval_cases j
  · exact B416571
  · exact B416575
  · exact B416579
  · exact B416583
  · exact B416587
  · exact B416591
  · exact B416595
  · exact B416599
  · exact B416603
  · exact B416607
  · exact B416611
  · exact B416615
  · exact B416619
  · exact B416623
  · exact B416627
  · exact B416631
  · exact B416635
  · exact B416639
  · exact B416643
  · exact B416647
  · exact B416651
  · exact B416655
  · exact B416659
  · exact B416663
  · exact B416667
  · exact B416671
  · exact B416675
  · exact B416679
  · exact B416683
  · exact B416687
  · exact B416691
  · exact B416695
  · exact B416699
  · exact B416703
  · exact B416707
  · exact B416711
  · exact B416715
  · exact B416719
  · exact B416723
  · exact B416727
  · exact B416731
  · exact B416735
  · exact B416739
  · exact B416743
  · exact B416747
  · exact B416751
  · exact B416755
  · exact B416759
  · exact B416763
  · exact B416767
  · exact B416771
  · exact B416775
  · exact B416779
  · exact B416783
  · exact B416787
  · exact B416791
  · exact B416795
  · exact B416799
  · exact B416803
  · exact B416807
  · exact B416811
  · exact B416815
  · exact B416819
  · exact B416823
  · exact B416827
  · exact B416831
  · exact B416835
  · exact B416839
  · exact B416843
  · exact B416847
  · exact B416851
  · exact B416855
  · exact B416859
  · exact B416863
  · exact B416867
  · exact B416871
  · exact B416875
  · exact B416879
  · exact B416883
  · exact B416887
  · exact B416891
  · exact B416895
  · exact B416899
  · exact B416903
  · exact B416907
  · exact B416911
  · exact B416915
  · exact B416919
  · exact B416923
  · exact B416927
  · exact B416931
  · exact B416935
  · exact B416939
  · exact B416943
  · exact B416947
  · exact B416951
  · exact B416955
  · exact B416959
  · exact B416963
  · exact B416967
  · exact B416971
  · exact B416975
  · exact B416979
  · exact B416983
  · exact B416987
  · exact B416991
  · exact B416995
  · exact B416999
  · exact B417003
  · exact B417007
  · exact B417011
  · exact B417015
  · exact B417019
  · exact B417023
  · exact B417027
  · exact B417031
  · exact B417035
  · exact B417039
  · exact B417043
  · exact B417047
  · exact B417051
  · exact B417055
  · exact B417059
  · exact B417063
  · exact B417067
  · exact B417071
  · exact B417075
  · exact B417079
  · exact B417083
  · exact B417087
  · exact B417091
  · exact B417095
  · exact B417099
  · exact B417103
  · exact B417107
  · exact B417111
  · exact B417115
  · exact B417119
  · exact B417123
  · exact B417127
  · exact B417131
  · exact B417135
  · exact B417139
  · exact B417143
  · exact B417147
  · exact B417151
  · exact B417155
  · exact B417159
  · exact B417163
  · exact B417167
  · exact B417171
  · exact B417175
  · exact B417179
  · exact B417183
  · exact B417187
  · exact B417191
  · exact B417195
  · exact B417199
  · exact B417203
  · exact B417207
  · exact B417211
  · exact B417215
  · exact B417219
  · exact B417223
  · exact B417227
  · exact B417231
  · exact B417235
  · exact B417239
  · exact B417243
  · exact B417247
  · exact B417251
  · exact B417255
  · exact B417259
  · exact B417263
  · exact B417267
  · exact B417271
  · exact B417275
  · exact B417279
  · exact B417283
  · exact B417287
  · exact B417291
  · exact B417295
  · exact B417299
  · exact B417303
  · exact B417307
  · exact B417311
  · exact B417315
  · exact B417319
  · exact B417323
  · exact B417327
  · exact B417331
  · exact B417335
  · exact B417339
  · exact B417343
  · exact B417347
  · exact B417351
  · exact B417355
  · exact B417359
  · exact B417363
  · exact B417367
  · exact B417371
  · exact B417375
  · exact B417379
  · exact B417383
  · exact B417387
  · exact B417391
  · exact B417395
  · exact B417399
  · exact B417403
  · exact B417407
  · exact B417411
  · exact B417415
  · exact B417419
  · exact B417423
  · exact B417427
  · exact B417431
  · exact B417435
  · exact B417439
  · exact B417443
  · exact B417447
  · exact B417451
  · exact B417455
  · exact B417459
  · exact B417463
  · exact B417467
  · exact B417471
  · exact B417475
  · exact B417479
  · exact B417483
  · exact B417487
  · exact B417491
  · exact B417495
  · exact B417499
  · exact B417503
  · exact B417507
  · exact B417511
  · exact B417515
  · exact B417519
  · exact B417523
  · exact B417527
  · exact B417531
  · exact B417535
  · exact B417539
  · exact B417543
  · exact B417547
  · exact B417551
  · exact B417555
  · exact B417559
  · exact B417563
  · exact B417567
  · exact B417571
  · exact B417575
  · exact B417579
  · exact B417583
  · exact B417587
  · exact B417591
  · exact B417595
  · exact B417599
  · exact B417603
  · exact B417607
  · exact B417611
  · exact B417615
  · exact B417619
  · exact B417623
  · exact B417627
  · exact B417631
  · exact B417635
  · exact B417639
  · exact B417643
  · exact B417647
  · exact B417651
  · exact B417655
  · exact B417659
  · exact B417663
  · exact B417667
  · exact B417671
  · exact B417675
  · exact B417679
  · exact B417683
  · exact B417687
  · exact B417691
  · exact B417695
  · exact B417699
  · exact B417703
  · exact B417707
  · exact B417711
  · exact B417715
  · exact B417719
  · exact B417723
  · exact B417727
  · exact B417731
  · exact B417735
  · exact B417739
  · exact B417743
  · exact B417747
  · exact B417751
  · exact B417755
  · exact B417759
  · exact B417763
  · exact B417767
  · exact B417771

theorem solution (m : ℕ) (hlo : 413771 ≤ m) (hhi : m ≤ 417771) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 103442 ≤ j := by omega
    have hj2 : j ≤ 104442 := by omega
    have hb : Blo 413771 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 104142 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
