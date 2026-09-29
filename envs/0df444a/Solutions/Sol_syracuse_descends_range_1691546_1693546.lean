-- Prove2me | solution 1 for syracuse_descends_range_1691546_1693546
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:24:15.373688+00:00
-- url     : https://prove2.me/submissions/5ecc0dde-b56b-4f68-ad61-ed3b07d0fe5c

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


theorem B3809285 : Blo 1691546 3809285 := bbase (se 4 (by rfl) ⟨357120, by rfl⟩ : syracuseStep 3809285 = 714241) (by norm_num)
theorem B16482325 : Blo 1691546 16482325 := bbase (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) (by norm_num)
theorem B2539541 : Blo 1691546 2539541 := bbase (se 6 (by rfl) ⟨59520, by rfl⟩ : syracuseStep 2539541 = 119041) (by norm_num)
theorem B2539565 : Blo 1691546 2539565 := bbase (se 3 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 2539565 = 952337) (by norm_num)
theorem B6422597 : Blo 1691546 6422597 := bbase (se 4 (by rfl) ⟨602118, by rfl⟩ : syracuseStep 6422597 = 1204237) (by norm_num)
theorem B4284485 : Blo 1691546 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B2539589 : Blo 1691546 2539589 := bbase (se 4 (by rfl) ⟨238086, by rfl⟩ : syracuseStep 2539589 = 476173) (by norm_num)
theorem B3809357 : Blo 1691546 3809357 := bbase (se 3 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 3809357 = 1428509) (by norm_num)
theorem B4341845 : Blo 1691546 4341845 := bbase (se 8 (by rfl) ⟨25440, by rfl⟩ : syracuseStep 4341845 = 50881) (by norm_num)
theorem B2539613 : Blo 1691546 2539613 := bbase (se 3 (by rfl) ⟨476177, by rfl⟩ : syracuseStep 2539613 = 952355) (by norm_num)
theorem B13721717 : Blo 1691546 13721717 := bbase (se 5 (by rfl) ⟨643205, by rfl⟩ : syracuseStep 13721717 = 1286411) (by norm_num)
theorem B2539637 : Blo 1691546 2539637 := bbase (se 5 (by rfl) ⟨119045, by rfl⟩ : syracuseStep 2539637 = 238091) (by norm_num)
theorem B3211397 : Blo 1691546 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B2711693 : Blo 1691546 2711693 := bbase (se 3 (by rfl) ⟨508442, by rfl⟩ : syracuseStep 2711693 = 1016885) (by norm_num)
theorem B2539661 : Blo 1691546 2539661 := bbase (se 3 (by rfl) ⟨476186, by rfl⟩ : syracuseStep 2539661 = 952373) (by norm_num)
theorem B3809429 : Blo 1691546 3809429 := bbase (se 6 (by rfl) ⟨89283, by rfl⟩ : syracuseStep 3809429 = 178567) (by norm_num)
theorem B2539685 : Blo 1691546 2539685 := bbase (se 4 (by rfl) ⟨238095, by rfl⟩ : syracuseStep 2539685 = 476191) (by norm_num)
theorem B2539709 : Blo 1691546 2539709 := bbase (se 3 (by rfl) ⟨476195, by rfl⟩ : syracuseStep 2539709 = 952391) (by norm_num)
theorem B2539733 : Blo 1691546 2539733 := bbase (se 7 (by rfl) ⟨29762, by rfl⟩ : syracuseStep 2539733 = 59525) (by norm_num)
theorem B3809501 : Blo 1691546 3809501 := bbase (se 3 (by rfl) ⟨714281, by rfl⟩ : syracuseStep 3809501 = 1428563) (by norm_num)
theorem B2539757 : Blo 1691546 2539757 := bbase (se 3 (by rfl) ⟨476204, by rfl⟩ : syracuseStep 2539757 = 952409) (by norm_num)
theorem B4817141 : Blo 1691546 4817141 := bbase (se 5 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 4817141 = 451607) (by norm_num)
theorem B3612917 : Blo 1691546 3612917 := bbase (se 5 (by rfl) ⟨169355, by rfl⟩ : syracuseStep 3612917 = 338711) (by norm_num)
theorem B4284677 : Blo 1691546 4284677 := bbase (se 4 (by rfl) ⟨401688, by rfl⟩ : syracuseStep 4284677 = 803377) (by norm_num)
theorem B2539781 : Blo 1691546 2539781 := bbase (se 4 (by rfl) ⟨238104, by rfl⟩ : syracuseStep 2539781 = 476209) (by norm_num)
theorem B2711821 : Blo 1691546 2711821 := bbase (se 3 (by rfl) ⟨508466, by rfl⟩ : syracuseStep 2711821 = 1016933) (by norm_num)
theorem B2539805 : Blo 1691546 2539805 := bbase (se 3 (by rfl) ⟨476213, by rfl⟩ : syracuseStep 2539805 = 952427) (by norm_num)
theorem B3809573 : Blo 1691546 3809573 := bbase (se 4 (by rfl) ⟨357147, by rfl⟩ : syracuseStep 3809573 = 714295) (by norm_num)
theorem B2539829 : Blo 1691546 2539829 := bbase (se 5 (by rfl) ⟨119054, by rfl⟩ : syracuseStep 2539829 = 238109) (by norm_num)
theorem B2539853 : Blo 1691546 2539853 := bbase (se 3 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 2539853 = 952445) (by norm_num)
theorem B6422885 : Blo 1691546 6422885 := bbase (se 4 (by rfl) ⟨602145, by rfl⟩ : syracuseStep 6422885 = 1204291) (by norm_num)
theorem B2539877 : Blo 1691546 2539877 := bbase (se 4 (by rfl) ⟨238113, by rfl⟩ : syracuseStep 2539877 = 476227) (by norm_num)
theorem B3809645 : Blo 1691546 3809645 := bbase (se 3 (by rfl) ⟨714308, by rfl⟩ : syracuseStep 3809645 = 1428617) (by norm_num)
theorem B2539901 : Blo 1691546 2539901 := bbase (se 3 (by rfl) ⟨476231, by rfl⟩ : syracuseStep 2539901 = 952463) (by norm_num)
theorem B3432829 : Blo 1691546 3432829 := bbase (se 3 (by rfl) ⟨643655, by rfl⟩ : syracuseStep 3432829 = 1287311) (by norm_num)
theorem B3613061 : Blo 1691546 3613061 := bbase (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) (by norm_num)
theorem B2318725 : Blo 1691546 2318725 := bbase (se 4 (by rfl) ⟨217380, by rfl⟩ : syracuseStep 2318725 = 434761) (by norm_num)
theorem B5710229 : Blo 1691546 5710229 := bbase (se 6 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 5710229 = 267667) (by norm_num)
theorem B2539925 : Blo 1691546 2539925 := bbase (se 6 (by rfl) ⟨59529, by rfl⟩ : syracuseStep 2539925 = 119059) (by norm_num)
theorem B2539949 : Blo 1691546 2539949 := bbase (se 3 (by rfl) ⟨476240, by rfl⟩ : syracuseStep 2539949 = 952481) (by norm_num)
theorem B7717301 : Blo 1691546 7717301 := bbase (se 5 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 7717301 = 723497) (by norm_num)
theorem B3809717 : Blo 1691546 3809717 := bbase (se 5 (by rfl) ⟨178580, by rfl⟩ : syracuseStep 3809717 = 357161) (by norm_num)
theorem B2539973 : Blo 1691546 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B2539997 : Blo 1691546 2539997 := bbase (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) (by norm_num)
theorem B2540021 : Blo 1691546 2540021 := bbase (se 5 (by rfl) ⟨119063, by rfl⟩ : syracuseStep 2540021 = 238127) (by norm_num)
theorem B3809789 : Blo 1691546 3809789 := bbase (se 3 (by rfl) ⟨714335, by rfl⟩ : syracuseStep 3809789 = 1428671) (by norm_num)
theorem B2540045 : Blo 1691546 2540045 := bbase (se 3 (by rfl) ⟨476258, by rfl⟩ : syracuseStep 2540045 = 952517) (by norm_num)
theorem B2032165 : Blo 1691546 2032165 := bbase (se 4 (by rfl) ⟨190515, by rfl⟩ : syracuseStep 2032165 = 381031) (by norm_num)
theorem B2540069 : Blo 1691546 2540069 := bbase (se 4 (by rfl) ⟨238131, by rfl⟩ : syracuseStep 2540069 = 476263) (by norm_num)
theorem B2540093 : Blo 1691546 2540093 := bbase (se 3 (by rfl) ⟨476267, by rfl⟩ : syracuseStep 2540093 = 952535) (by norm_num)
theorem B2032193 : Blo 1691546 2032193 := bbase (se 2 (by rfl) ⟨762072, by rfl⟩ : syracuseStep 2032193 = 1524145) (by norm_num)
theorem B5145157 : Blo 1691546 5145157 := bbase (se 4 (by rfl) ⟨482358, by rfl⟩ : syracuseStep 5145157 = 964717) (by norm_num)
theorem B3809861 : Blo 1691546 3809861 := bbase (se 4 (by rfl) ⟨357174, by rfl⟩ : syracuseStep 3809861 = 714349) (by norm_num)
theorem B2540117 : Blo 1691546 2540117 := bbase (se 8 (by rfl) ⟨14883, by rfl⟩ : syracuseStep 2540117 = 29767) (by norm_num)
theorem B4285021 : Blo 1691546 4285021 := bbase (se 3 (by rfl) ⟨803441, by rfl⟩ : syracuseStep 4285021 = 1606883) (by norm_num)
theorem B2540141 : Blo 1691546 2540141 := bbase (se 3 (by rfl) ⟨476276, by rfl⟩ : syracuseStep 2540141 = 952553) (by norm_num)
theorem B2540165 : Blo 1691546 2540165 := bbase (se 4 (by rfl) ⟨238140, by rfl⟩ : syracuseStep 2540165 = 476281) (by norm_num)
theorem B2712205 : Blo 1691546 2712205 := bbase (se 3 (by rfl) ⟨508538, by rfl⟩ : syracuseStep 2712205 = 1017077) (by norm_num)
theorem B3809933 : Blo 1691546 3809933 := bbase (se 3 (by rfl) ⟨714362, by rfl⟩ : syracuseStep 3809933 = 1428725) (by norm_num)
theorem B2540189 : Blo 1691546 2540189 := bbase (se 3 (by rfl) ⟨476285, by rfl⟩ : syracuseStep 2540189 = 952571) (by norm_num)
theorem B2540213 : Blo 1691546 2540213 := bbase (se 5 (by rfl) ⟨119072, by rfl⟩ : syracuseStep 2540213 = 238145) (by norm_num)
theorem B4285133 : Blo 1691546 4285133 := bbase (se 3 (by rfl) ⟨803462, by rfl⟩ : syracuseStep 4285133 = 1606925) (by norm_num)
theorem B2540237 : Blo 1691546 2540237 := bbase (se 3 (by rfl) ⟨476294, by rfl⟩ : syracuseStep 2540237 = 952589) (by norm_num)
theorem B3810005 : Blo 1691546 3810005 := bbase (se 7 (by rfl) ⟨44648, by rfl⟩ : syracuseStep 3810005 = 89297) (by norm_num)
theorem B2540261 : Blo 1691546 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B2032381 : Blo 1691546 2032381 := bbase (se 3 (by rfl) ⟨381071, by rfl⟩ : syracuseStep 2032381 = 762143) (by norm_num)
theorem B2540285 : Blo 1691546 2540285 := bbase (se 3 (by rfl) ⟨476303, by rfl⟩ : syracuseStep 2540285 = 952607) (by norm_num)
theorem B2540309 : Blo 1691546 2540309 := bbase (se 6 (by rfl) ⟨59538, by rfl⟩ : syracuseStep 2540309 = 119077) (by norm_num)
theorem B3810077 : Blo 1691546 3810077 := bbase (se 3 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 3810077 = 1428779) (by norm_num)
theorem B8569637 : Blo 1691546 8569637 := bbase (se 4 (by rfl) ⟨803403, by rfl⟩ : syracuseStep 8569637 = 1606807) (by norm_num)
theorem B2409277 : Blo 1691546 2409277 := bbase (se 3 (by rfl) ⟨451739, by rfl⟩ : syracuseStep 2409277 = 903479) (by norm_num)
theorem B5710661 : Blo 1691546 5710661 := bbase (se 4 (by rfl) ⟨535374, by rfl⟩ : syracuseStep 5710661 = 1070749) (by norm_num)
theorem B3810149 : Blo 1691546 3810149 := bbase (se 4 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 3810149 = 714403) (by norm_num)
theorem B2032501 : Blo 1691546 2032501 := bbase (se 5 (by rfl) ⟨95273, by rfl⟩ : syracuseStep 2032501 = 190547) (by norm_num)
theorem B3212149 : Blo 1691546 3212149 := bbase (se 5 (by rfl) ⟨150569, by rfl⟩ : syracuseStep 3212149 = 301139) (by norm_num)
theorem B4285325 : Blo 1691546 4285325 := bbase (se 3 (by rfl) ⟨803498, by rfl⟩ : syracuseStep 4285325 = 1606997) (by norm_num)
theorem B2712461 : Blo 1691546 2712461 := bbase (se 3 (by rfl) ⟨508586, by rfl⟩ : syracuseStep 2712461 = 1017173) (by norm_num)
theorem B3810221 : Blo 1691546 3810221 := bbase (se 3 (by rfl) ⟨714416, by rfl⟩ : syracuseStep 3810221 = 1428833) (by norm_num)
theorem B7226293 : Blo 1691546 7226293 := bbase (se 5 (by rfl) ⟨338732, by rfl⟩ : syracuseStep 7226293 = 677465) (by norm_num)
theorem B2171845 : Blo 1691546 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B54887381 : Blo 1691546 54887381 := bbase (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) (by norm_num)
theorem B4817893 : Blo 1691546 4817893 := bbase (se 4 (by rfl) ⟨451677, by rfl⟩ : syracuseStep 4817893 = 903355) (by norm_num)
theorem B3810293 : Blo 1691546 3810293 := bbase (se 5 (by rfl) ⟨178607, by rfl⟩ : syracuseStep 3810293 = 357215) (by norm_num)
theorem B3212293 : Blo 1691546 3212293 := bbase (se 4 (by rfl) ⟨301152, by rfl⟩ : syracuseStep 3212293 = 602305) (by norm_num)
theorem B3810365 : Blo 1691546 3810365 := bbase (se 3 (by rfl) ⟨714443, by rfl⟩ : syracuseStep 3810365 = 1428887) (by norm_num)
theorem B3613805 : Blo 1691546 3613805 := bbase (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) (by norm_num)
theorem B3810437 : Blo 1691546 3810437 := bbase (se 4 (by rfl) ⟨357228, by rfl⟩ : syracuseStep 3810437 = 714457) (by norm_num)
theorem B3212453 : Blo 1691546 3212453 := bbase (se 4 (by rfl) ⟨301167, by rfl⟩ : syracuseStep 3212453 = 602335) (by norm_num)
theorem B3302621 : Blo 1691546 3302621 := bbase (se 3 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 3302621 = 1238483) (by norm_num)
theorem B4285669 : Blo 1691546 4285669 := bbase (se 4 (by rfl) ⟨401781, by rfl⟩ : syracuseStep 4285669 = 803563) (by norm_num)
theorem B5711093 : Blo 1691546 5711093 := bbase (se 5 (by rfl) ⟨267707, by rfl⟩ : syracuseStep 5711093 = 535415) (by norm_num)
theorem B12363029 : Blo 1691546 12363029 := bbase (se 6 (by rfl) ⟨289758, by rfl⟩ : syracuseStep 12363029 = 579517) (by norm_num)
theorem B3212597 : Blo 1691546 3212597 := bbase (se 5 (by rfl) ⟨150590, by rfl⟩ : syracuseStep 3212597 = 301181) (by norm_num)
theorem B3048781 : Blo 1691546 3048781 := bbase (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) (by norm_num)
theorem B4285781 : Blo 1691546 4285781 := bbase (se 12 (by rfl) ⟨1569, by rfl⟩ : syracuseStep 4285781 = 3139) (by norm_num)
theorem B3859853 : Blo 1691546 3859853 := bbase (se 3 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 3859853 = 1447445) (by norm_num)
theorem B2409869 : Blo 1691546 2409869 := bbase (se 3 (by rfl) ⟨451850, by rfl⟩ : syracuseStep 2409869 = 903701) (by norm_num)
theorem B37094869 : Blo 1691546 37094869 := bbase (se 7 (by rfl) ⟨434705, by rfl⟩ : syracuseStep 37094869 = 869411) (by norm_num)
theorem B2409949 : Blo 1691546 2409949 := bbase (se 3 (by rfl) ⟨451865, by rfl⟩ : syracuseStep 2409949 = 903731) (by norm_num)
theorem B6424069 : Blo 1691546 6424069 := bbase (se 4 (by rfl) ⟨602256, by rfl⟩ : syracuseStep 6424069 = 1204513) (by norm_num)
theorem B4285973 : Blo 1691546 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B3663389 : Blo 1691546 3663389 := bbase (se 3 (by rfl) ⟨686885, by rfl⟩ : syracuseStep 3663389 = 1373771) (by norm_num)
theorem B3048997 : Blo 1691546 3048997 := bbase (se 4 (by rfl) ⟨285843, by rfl⟩ : syracuseStep 3048997 = 571687) (by norm_num)
theorem B3212885 : Blo 1691546 3212885 := bbase (se 8 (by rfl) ⟨18825, by rfl⟩ : syracuseStep 3212885 = 37651) (by norm_num)
theorem B2410069 : Blo 1691546 2410069 := bbase (se 8 (by rfl) ⟨14121, by rfl⟩ : syracuseStep 2410069 = 28243) (by norm_num)
theorem B5711525 : Blo 1691546 5711525 := bbase (se 4 (by rfl) ⟨535455, by rfl⟩ : syracuseStep 5711525 = 1070911) (by norm_num)
theorem B2410165 : Blo 1691546 2410165 := bbase (se 5 (by rfl) ⟨112976, by rfl⟩ : syracuseStep 2410165 = 225953) (by norm_num)
theorem B5146325 : Blo 1691546 5146325 := bbase (se 7 (by rfl) ⟨60308, by rfl⟩ : syracuseStep 5146325 = 120617) (by norm_num)
theorem B3213037 : Blo 1691546 3213037 := bbase (se 3 (by rfl) ⟨602444, by rfl⟩ : syracuseStep 3213037 = 1204889) (by norm_num)
theorem B6424373 : Blo 1691546 6424373 := bbase (se 5 (by rfl) ⟨301142, by rfl⟩ : syracuseStep 6424373 = 602285) (by norm_num)
theorem B87934805 : Blo 1691546 87934805 := bbase (se 9 (by rfl) ⟨257621, by rfl⟩ : syracuseStep 87934805 = 515243) (by norm_num)
theorem B3614557 : Blo 1691546 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B4286317 : Blo 1691546 4286317 := bbase (se 3 (by rfl) ⟨803684, by rfl⟩ : syracuseStep 4286317 = 1607369) (by norm_num)
theorem B2574197 : Blo 1691546 2574197 := bbase (se 5 (by rfl) ⟨120665, by rfl⟩ : syracuseStep 2574197 = 241331) (by norm_num)
theorem B2443141 : Blo 1691546 2443141 := bbase (se 4 (by rfl) ⟨229044, by rfl⟩ : syracuseStep 2443141 = 458089) (by norm_num)
theorem B4286429 : Blo 1691546 4286429 := bbase (se 3 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 4286429 = 1607411) (by norm_num)
theorem B3614701 : Blo 1691546 3614701 := bbase (se 3 (by rfl) ⟨677756, by rfl⟩ : syracuseStep 3614701 = 1355513) (by norm_num)
theorem B3213341 : Blo 1691546 3213341 := bbase (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) (by norm_num)
theorem B14452789 : Blo 1691546 14452789 := bbase (se 5 (by rfl) ⟨677474, by rfl⟩ : syracuseStep 14452789 = 1354949) (by norm_num)
theorem B8570933 : Blo 1691546 8570933 := bbase (se 5 (by rfl) ⟨401762, by rfl⟩ : syracuseStep 8570933 = 803525) (by norm_num)
theorem B5711957 : Blo 1691546 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B4286621 : Blo 1691546 4286621 := bbase (se 3 (by rfl) ⟨803741, by rfl⟩ : syracuseStep 4286621 = 1607483) (by norm_num)
theorem B2410661 : Blo 1691546 2410661 := bbase (se 4 (by rfl) ⟨225999, by rfl⟩ : syracuseStep 2410661 = 451999) (by norm_num)
theorem B2287813 : Blo 1691546 2287813 := bbase (se 4 (by rfl) ⟨214482, by rfl⟩ : syracuseStep 2287813 = 428965) (by norm_num)
theorem B3615077 : Blo 1691546 3615077 := bbase (se 4 (by rfl) ⟨338913, by rfl⟩ : syracuseStep 3615077 = 677827) (by norm_num)
theorem B2034077 : Blo 1691546 2034077 := bbase (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) (by norm_num)
theorem B1903009 : Blo 1691546 1903009 := bbase (se 2 (by rfl) ⟨713628, by rfl⟩ : syracuseStep 1903009 = 1427257) (by norm_num)
theorem B1903045 : Blo 1691546 1903045 := bbase (se 4 (by rfl) ⟨178410, by rfl⟩ : syracuseStep 1903045 = 356821) (by norm_num)
theorem B1903081 : Blo 1691546 1903081 := bbase (se 2 (by rfl) ⟨713655, by rfl⟩ : syracuseStep 1903081 = 1427311) (by norm_num)
theorem B5712389 : Blo 1691546 5712389 := bbase (se 4 (by rfl) ⟨535536, by rfl⟩ : syracuseStep 5712389 = 1071073) (by norm_num)
theorem B1903117 : Blo 1691546 1903117 := bbase (se 3 (by rfl) ⟨356834, by rfl⟩ : syracuseStep 1903117 = 713669) (by norm_num)
theorem B1903153 : Blo 1691546 1903153 := bbase (se 2 (by rfl) ⟨713682, by rfl⟩ : syracuseStep 1903153 = 1427365) (by norm_num)
theorem B1903189 : Blo 1691546 1903189 := bbase (se 8 (by rfl) ⟨11151, by rfl⟩ : syracuseStep 1903189 = 22303) (by norm_num)
theorem B1903225 : Blo 1691546 1903225 := bbase (se 2 (by rfl) ⟨713709, by rfl⟩ : syracuseStep 1903225 = 1427419) (by norm_num)
theorem B1903261 : Blo 1691546 1903261 := bbase (se 3 (by rfl) ⟨356861, by rfl⟩ : syracuseStep 1903261 = 713723) (by norm_num)
theorem B2288293 : Blo 1691546 2288293 := bbase (se 4 (by rfl) ⟨214527, by rfl⟩ : syracuseStep 2288293 = 429055) (by norm_num)
theorem B1903297 : Blo 1691546 1903297 := bbase (se 2 (by rfl) ⟨713736, by rfl⟩ : syracuseStep 1903297 = 1427473) (by norm_num)
theorem B2411213 : Blo 1691546 2411213 := bbase (se 3 (by rfl) ⟨452102, by rfl⟩ : syracuseStep 2411213 = 904205) (by norm_num)
theorem B3615445 : Blo 1691546 3615445 := bbase (se 7 (by rfl) ⟨42368, by rfl⟩ : syracuseStep 3615445 = 84737) (by norm_num)
theorem B1903333 : Blo 1691546 1903333 := bbase (se 4 (by rfl) ⟨178437, by rfl⟩ : syracuseStep 1903333 = 356875) (by norm_num)
theorem B2140921 : Blo 1691546 2140921 := bbase (se 2 (by rfl) ⟨802845, by rfl⟩ : syracuseStep 2140921 = 1605691) (by norm_num)
theorem B4639493 : Blo 1691546 4639493 := bbase (se 4 (by rfl) ⟨434952, by rfl⟩ : syracuseStep 4639493 = 869905) (by norm_num)
theorem B1903369 : Blo 1691546 1903369 := bbase (se 2 (by rfl) ⟨713763, by rfl⟩ : syracuseStep 1903369 = 1427527) (by norm_num)
theorem B3214093 : Blo 1691546 3214093 := bbase (se 3 (by rfl) ⟨602642, by rfl⟩ : syracuseStep 3214093 = 1205285) (by norm_num)
theorem B1903405 : Blo 1691546 1903405 := bbase (se 3 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 1903405 = 713777) (by norm_num)
theorem B6097733 : Blo 1691546 6097733 := bbase (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) (by norm_num)
theorem B1903441 : Blo 1691546 1903441 := bbase (se 2 (by rfl) ⟨713790, by rfl⟩ : syracuseStep 1903441 = 1427581) (by norm_num)
theorem B1903477 : Blo 1691546 1903477 := bbase (se 5 (by rfl) ⟨89225, by rfl⟩ : syracuseStep 1903477 = 178451) (by norm_num)
theorem B8129429 : Blo 1691546 8129429 := bbase (se 6 (by rfl) ⟨190533, by rfl⟩ : syracuseStep 8129429 = 381067) (by norm_num)
theorem B1903513 : Blo 1691546 1903513 := bbase (se 2 (by rfl) ⟨713817, by rfl⟩ : syracuseStep 1903513 = 1427635) (by norm_num)
theorem B3214237 : Blo 1691546 3214237 := bbase (se 3 (by rfl) ⟨602669, by rfl⟩ : syracuseStep 3214237 = 1205339) (by norm_num)
theorem B2141093 : Blo 1691546 2141093 := bbase (se 4 (by rfl) ⟨200727, by rfl⟩ : syracuseStep 2141093 = 401455) (by norm_num)
theorem B5712821 : Blo 1691546 5712821 := bbase (se 5 (by rfl) ⟨267788, by rfl⟩ : syracuseStep 5712821 = 535577) (by norm_num)
theorem B1903549 : Blo 1691546 1903549 := bbase (se 3 (by rfl) ⟨356915, by rfl⟩ : syracuseStep 1903549 = 713831) (by norm_num)
theorem B3050453 : Blo 1691546 3050453 := bbase (se 7 (by rfl) ⟨35747, by rfl⟩ : syracuseStep 3050453 = 71495) (by norm_num)
theorem B2141149 : Blo 1691546 2141149 := bbase (se 3 (by rfl) ⟨401465, by rfl⟩ : syracuseStep 2141149 = 802931) (by norm_num)
theorem B1903585 : Blo 1691546 1903585 := bbase (se 2 (by rfl) ⟨713844, by rfl⟩ : syracuseStep 1903585 = 1427689) (by norm_num)
theorem B3476477 : Blo 1691546 3476477 := bbase (se 3 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 3476477 = 1303679) (by norm_num)
theorem B1903621 : Blo 1691546 1903621 := bbase (se 4 (by rfl) ⟨178464, by rfl⟩ : syracuseStep 1903621 = 356929) (by norm_num)
theorem B1903657 : Blo 1691546 1903657 := bbase (se 2 (by rfl) ⟨713871, by rfl⟩ : syracuseStep 1903657 = 1427743) (by norm_num)
theorem B2141245 : Blo 1691546 2141245 := bbase (se 3 (by rfl) ⟨401483, by rfl⟩ : syracuseStep 2141245 = 802967) (by norm_num)
theorem B3214397 : Blo 1691546 3214397 := bbase (se 3 (by rfl) ⟨602699, by rfl⟩ : syracuseStep 3214397 = 1205399) (by norm_num)
theorem B1903693 : Blo 1691546 1903693 := bbase (se 3 (by rfl) ⟨356942, by rfl⟩ : syracuseStep 1903693 = 713885) (by norm_num)
theorem B3050597 : Blo 1691546 3050597 := bbase (se 4 (by rfl) ⟨285993, by rfl⟩ : syracuseStep 3050597 = 571987) (by norm_num)
theorem B1903729 : Blo 1691546 1903729 := bbase (se 2 (by rfl) ⟨713898, by rfl⟩ : syracuseStep 1903729 = 1427797) (by norm_num)
theorem B16264309 : Blo 1691546 16264309 := bbase (se 5 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 16264309 = 1524779) (by norm_num)
theorem B1715341 : Blo 1691546 1715341 := bbase (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) (by norm_num)
theorem B1903765 : Blo 1691546 1903765 := bbase (se 6 (by rfl) ⟨44619, by rfl⟩ : syracuseStep 1903765 = 89239) (by norm_num)
theorem B4066453 : Blo 1691546 4066453 := bbase (se 6 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 4066453 = 190615) (by norm_num)
theorem B3050669 : Blo 1691546 3050669 := bbase (se 3 (by rfl) ⟨572000, by rfl⟩ : syracuseStep 3050669 = 1144001) (by norm_num)
theorem B1903801 : Blo 1691546 1903801 := bbase (se 2 (by rfl) ⟨713925, by rfl⟩ : syracuseStep 1903801 = 1427851) (by norm_num)
theorem B4123853 : Blo 1691546 4123853 := bbase (se 3 (by rfl) ⟨773222, by rfl⟩ : syracuseStep 4123853 = 1546445) (by norm_num)
theorem B3214541 : Blo 1691546 3214541 := bbase (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) (by norm_num)
theorem B27446485 : Blo 1691546 27446485 := bbase (se 7 (by rfl) ⟨321638, by rfl⟩ : syracuseStep 27446485 = 643277) (by norm_num)
theorem B1903837 : Blo 1691546 1903837 := bbase (se 3 (by rfl) ⟨356969, by rfl⟩ : syracuseStep 1903837 = 713939) (by norm_num)
theorem B2141417 : Blo 1691546 2141417 := bbase (se 2 (by rfl) ⟨803031, by rfl⟩ : syracuseStep 2141417 = 1606063) (by norm_num)
theorem B12201205 : Blo 1691546 12201205 := bbase (se 5 (by rfl) ⟨571931, by rfl⟩ : syracuseStep 12201205 = 1143863) (by norm_num)
theorem B1903873 : Blo 1691546 1903873 := bbase (se 2 (by rfl) ⟨713952, by rfl⟩ : syracuseStep 1903873 = 1427905) (by norm_num)
theorem B10439957 : Blo 1691546 10439957 := bbase (se 6 (by rfl) ⟨244686, by rfl⟩ : syracuseStep 10439957 = 489373) (by norm_num)
theorem B2141473 : Blo 1691546 2141473 := bbase (se 2 (by rfl) ⟨803052, by rfl⟩ : syracuseStep 2141473 = 1606105) (by norm_num)
theorem B1903909 : Blo 1691546 1903909 := bbase (se 4 (by rfl) ⟨178491, by rfl⟩ : syracuseStep 1903909 = 356983) (by norm_num)
theorem B8572229 : Blo 1691546 8572229 := bbase (se 4 (by rfl) ⟨803646, by rfl⟩ : syracuseStep 8572229 = 1607293) (by norm_num)
theorem B1903945 : Blo 1691546 1903945 := bbase (se 2 (by rfl) ⟨713979, by rfl⟩ : syracuseStep 1903945 = 1427959) (by norm_num)
theorem B5713253 : Blo 1691546 5713253 := bbase (se 4 (by rfl) ⟨535617, by rfl⟩ : syracuseStep 5713253 = 1071235) (by norm_num)
theorem B1903981 : Blo 1691546 1903981 := bbase (se 3 (by rfl) ⟨356996, by rfl⟩ : syracuseStep 1903981 = 713993) (by norm_num)
theorem B2141569 : Blo 1691546 2141569 := bbase (se 2 (by rfl) ⟨803088, by rfl⟩ : syracuseStep 2141569 = 1606177) (by norm_num)
theorem B1904017 : Blo 1691546 1904017 := bbase (se 2 (by rfl) ⟨714006, by rfl⟩ : syracuseStep 1904017 = 1428013) (by norm_num)
theorem B1904053 : Blo 1691546 1904053 := bbase (se 5 (by rfl) ⟨89252, by rfl⟩ : syracuseStep 1904053 = 178505) (by norm_num)
theorem B1904089 : Blo 1691546 1904089 := bbase (se 2 (by rfl) ⟨714033, by rfl⟩ : syracuseStep 1904089 = 1428067) (by norm_num)
theorem B3214829 : Blo 1691546 3214829 := bbase (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) (by norm_num)
theorem B1904125 : Blo 1691546 1904125 := bbase (se 3 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 1904125 = 714047) (by norm_num)
theorem B1904161 : Blo 1691546 1904161 := bbase (se 2 (by rfl) ⟨714060, by rfl⟩ : syracuseStep 1904161 = 1428121) (by norm_num)
theorem B2141741 : Blo 1691546 2141741 := bbase (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) (by norm_num)
theorem B1904197 : Blo 1691546 1904197 := bbase (se 4 (by rfl) ⟨178518, by rfl⟩ : syracuseStep 1904197 = 357037) (by norm_num)
theorem B2141797 : Blo 1691546 2141797 := bbase (se 4 (by rfl) ⟨200793, by rfl⟩ : syracuseStep 2141797 = 401587) (by norm_num)
theorem B3862117 : Blo 1691546 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B1904233 : Blo 1691546 1904233 := bbase (se 2 (by rfl) ⟨714087, by rfl⟩ : syracuseStep 1904233 = 1428175) (by norm_num)
theorem B3214981 : Blo 1691546 3214981 := bbase (se 4 (by rfl) ⟨301404, by rfl⟩ : syracuseStep 3214981 = 602809) (by norm_num)
theorem B2854541 : Blo 1691546 2854541 := bbase (se 3 (by rfl) ⟨535226, by rfl⟩ : syracuseStep 2854541 = 1070453) (by norm_num)
theorem B1904269 : Blo 1691546 1904269 := bbase (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) (by norm_num)
theorem B3051173 : Blo 1691546 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B1904305 : Blo 1691546 1904305 := bbase (se 2 (by rfl) ⟨714114, by rfl⟩ : syracuseStep 1904305 = 1428229) (by norm_num)
theorem B2141893 : Blo 1691546 2141893 := bbase (se 4 (by rfl) ⟨200802, by rfl⟩ : syracuseStep 2141893 = 401605) (by norm_num)
theorem B1904341 : Blo 1691546 1904341 := bbase (se 7 (by rfl) ⟨22316, by rfl⟩ : syracuseStep 1904341 = 44633) (by norm_num)
theorem B2059997 : Blo 1691546 2059997 := bbase (se 3 (by rfl) ⟨386249, by rfl⟩ : syracuseStep 2059997 = 772499) (by norm_num)
theorem B8564453 : Blo 1691546 8564453 := bbase (se 4 (by rfl) ⟨802917, by rfl⟩ : syracuseStep 8564453 = 1605835) (by norm_num)
theorem B4574965 : Blo 1691546 4574965 := bbase (se 5 (by rfl) ⟨214451, by rfl⟩ : syracuseStep 4574965 = 428903) (by norm_num)
theorem B1904377 : Blo 1691546 1904377 := bbase (se 2 (by rfl) ⟨714141, by rfl⟩ : syracuseStep 1904377 = 1428283) (by norm_num)
theorem B4820741 : Blo 1691546 4820741 := bbase (se 4 (by rfl) ⟨451944, by rfl⟩ : syracuseStep 4820741 = 903889) (by norm_num)
theorem B2854669 : Blo 1691546 2854669 := bbase (se 3 (by rfl) ⟨535250, by rfl⟩ : syracuseStep 2854669 = 1070501) (by norm_num)
theorem B5713685 : Blo 1691546 5713685 := bbase (se 6 (by rfl) ⟨133914, by rfl⟩ : syracuseStep 5713685 = 267829) (by norm_num)
theorem B1904413 : Blo 1691546 1904413 := bbase (se 3 (by rfl) ⟨357077, by rfl⟩ : syracuseStep 1904413 = 714155) (by norm_num)
theorem B4067117 : Blo 1691546 4067117 := bbase (se 3 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 4067117 = 1525169) (by norm_num)
theorem B1904449 : Blo 1691546 1904449 := bbase (se 2 (by rfl) ⟨714168, by rfl⟩ : syracuseStep 1904449 = 1428337) (by norm_num)
theorem B2854757 : Blo 1691546 2854757 := bbase (se 4 (by rfl) ⟨267633, by rfl⟩ : syracuseStep 2854757 = 535267) (by norm_num)
theorem B1904485 : Blo 1691546 1904485 := bbase (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) (by norm_num)
theorem B2142065 : Blo 1691546 2142065 := bbase (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) (by norm_num)
theorem B6426485 : Blo 1691546 6426485 := bbase (se 5 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 6426485 = 602483) (by norm_num)
theorem B1904521 : Blo 1691546 1904521 := bbase (se 2 (by rfl) ⟨714195, by rfl⟩ : syracuseStep 1904521 = 1428391) (by norm_num)
theorem B2142121 : Blo 1691546 2142121 := bbase (se 2 (by rfl) ⟨803295, by rfl⟩ : syracuseStep 2142121 = 1606591) (by norm_num)
theorem B1904557 : Blo 1691546 1904557 := bbase (se 3 (by rfl) ⟨357104, by rfl⟩ : syracuseStep 1904557 = 714209) (by norm_num)
theorem B1904593 : Blo 1691546 1904593 := bbase (se 2 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 1904593 = 1428445) (by norm_num)
theorem B2854885 : Blo 1691546 2854885 := bbase (se 4 (by rfl) ⟨267645, by rfl⟩ : syracuseStep 2854885 = 535291) (by norm_num)
theorem B14454773 : Blo 1691546 14454773 := bbase (se 5 (by rfl) ⟨677567, by rfl⟩ : syracuseStep 14454773 = 1355135) (by norm_num)
theorem B1904629 : Blo 1691546 1904629 := bbase (se 5 (by rfl) ⟨89279, by rfl⟩ : syracuseStep 1904629 = 178559) (by norm_num)
theorem B2142217 : Blo 1691546 2142217 := bbase (se 2 (by rfl) ⟨803331, by rfl⟩ : syracuseStep 2142217 = 1606663) (by norm_num)
theorem B1904665 : Blo 1691546 1904665 := bbase (se 2 (by rfl) ⟨714249, by rfl⟩ : syracuseStep 1904665 = 1428499) (by norm_num)
theorem B2895917 : Blo 1691546 2895917 := bbase (se 3 (by rfl) ⟨542984, by rfl⟩ : syracuseStep 2895917 = 1085969) (by norm_num)
theorem B2854973 : Blo 1691546 2854973 := bbase (se 3 (by rfl) ⟨535307, by rfl⟩ : syracuseStep 2854973 = 1070615) (by norm_num)
theorem B1904701 : Blo 1691546 1904701 := bbase (se 3 (by rfl) ⟨357131, by rfl⟩ : syracuseStep 1904701 = 714263) (by norm_num)
theorem B4067405 : Blo 1691546 4067405 := bbase (se 3 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 4067405 = 1525277) (by norm_num)
theorem B9637973 : Blo 1691546 9637973 := bbase (se 8 (by rfl) ⟨56472, by rfl⟩ : syracuseStep 9637973 = 112945) (by norm_num)
theorem B1904737 : Blo 1691546 1904737 := bbase (se 2 (by rfl) ⟨714276, by rfl⟩ : syracuseStep 1904737 = 1428553) (by norm_num)
theorem B1806445 : Blo 1691546 1806445 := bbase (se 3 (by rfl) ⟨338708, by rfl⟩ : syracuseStep 1806445 = 677417) (by norm_num)
theorem B1904773 : Blo 1691546 1904773 := bbase (se 4 (by rfl) ⟨178572, by rfl⟩ : syracuseStep 1904773 = 357145) (by norm_num)
theorem B2896013 : Blo 1691546 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B6426773 : Blo 1691546 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B1904809 : Blo 1691546 1904809 := bbase (se 2 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 1904809 = 1428607) (by norm_num)
theorem B2142389 : Blo 1691546 2142389 := bbase (se 5 (by rfl) ⟨100424, by rfl⟩ : syracuseStep 2142389 = 200849) (by norm_num)
theorem B3616949 : Blo 1691546 3616949 := bbase (se 5 (by rfl) ⟨169544, by rfl⟩ : syracuseStep 3616949 = 339089) (by norm_num)
theorem B2855101 : Blo 1691546 2855101 := bbase (se 3 (by rfl) ⟨535331, by rfl⟩ : syracuseStep 2855101 = 1070663) (by norm_num)
theorem B5714117 : Blo 1691546 5714117 := bbase (se 4 (by rfl) ⟨535698, by rfl⟩ : syracuseStep 5714117 = 1071397) (by norm_num)
theorem B1904845 : Blo 1691546 1904845 := bbase (se 3 (by rfl) ⟨357158, by rfl⟩ : syracuseStep 1904845 = 714317) (by norm_num)
theorem B2142445 : Blo 1691546 2142445 := bbase (se 3 (by rfl) ⟨401708, by rfl⟩ : syracuseStep 2142445 = 803417) (by norm_num)
theorem B1904881 : Blo 1691546 1904881 := bbase (se 2 (by rfl) ⟨714330, by rfl⟩ : syracuseStep 1904881 = 1428661) (by norm_num)
theorem B2855189 : Blo 1691546 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B11579669 : Blo 1691546 11579669 := bbase (se 6 (by rfl) ⟨271398, by rfl⟩ : syracuseStep 11579669 = 542797) (by norm_num)
theorem B1904917 : Blo 1691546 1904917 := bbase (se 6 (by rfl) ⟨44646, by rfl⟩ : syracuseStep 1904917 = 89293) (by norm_num)
theorem B1806629 : Blo 1691546 1806629 := bbase (se 4 (by rfl) ⟨169371, by rfl⟩ : syracuseStep 1806629 = 338743) (by norm_num)
theorem B1904953 : Blo 1691546 1904953 := bbase (se 2 (by rfl) ⟨714357, by rfl⟩ : syracuseStep 1904953 = 1428715) (by norm_num)
theorem B2142541 : Blo 1691546 2142541 := bbase (se 3 (by rfl) ⟨401726, by rfl⟩ : syracuseStep 2142541 = 803453) (by norm_num)
theorem B1904989 : Blo 1691546 1904989 := bbase (se 3 (by rfl) ⟨357185, by rfl⟩ : syracuseStep 1904989 = 714371) (by norm_num)
theorem B1905025 : Blo 1691546 1905025 := bbase (se 2 (by rfl) ⟨714384, by rfl⟩ : syracuseStep 1905025 = 1428769) (by norm_num)
theorem B2855317 : Blo 1691546 2855317 := bbase (se 6 (by rfl) ⟨66921, by rfl⟩ : syracuseStep 2855317 = 133843) (by norm_num)
theorem B1905061 : Blo 1691546 1905061 := bbase (se 4 (by rfl) ⟨178599, by rfl⟩ : syracuseStep 1905061 = 357199) (by norm_num)
theorem B1905097 : Blo 1691546 1905097 := bbase (se 2 (by rfl) ⟨714411, by rfl⟩ : syracuseStep 1905097 = 1428823) (by norm_num)
theorem B5419477 : Blo 1691546 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B2855405 : Blo 1691546 2855405 := bbase (se 3 (by rfl) ⟨535388, by rfl⟩ : syracuseStep 2855405 = 1070777) (by norm_num)
theorem B1905133 : Blo 1691546 1905133 := bbase (se 3 (by rfl) ⟨357212, by rfl⟩ : syracuseStep 1905133 = 714425) (by norm_num)
theorem B2142713 : Blo 1691546 2142713 := bbase (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) (by norm_num)
theorem B1905169 : Blo 1691546 1905169 := bbase (se 2 (by rfl) ⟨714438, by rfl⟩ : syracuseStep 1905169 = 1428877) (by norm_num)
theorem B5419541 : Blo 1691546 5419541 := bbase (se 6 (by rfl) ⟨127020, by rfl⟩ : syracuseStep 5419541 = 254041) (by norm_num)
theorem B5788181 : Blo 1691546 5788181 := bbase (se 6 (by rfl) ⟨135660, by rfl⟩ : syracuseStep 5788181 = 271321) (by norm_num)
theorem B2142769 : Blo 1691546 2142769 := bbase (se 2 (by rfl) ⟨803538, by rfl⟩ : syracuseStep 2142769 = 1607077) (by norm_num)
theorem B1905205 : Blo 1691546 1905205 := bbase (se 5 (by rfl) ⟨89306, by rfl⟩ : syracuseStep 1905205 = 178613) (by norm_num)
theorem B8573525 : Blo 1691546 8573525 := bbase (se 8 (by rfl) ⟨50235, by rfl⟩ : syracuseStep 8573525 = 100471) (by norm_num)
theorem B2855533 : Blo 1691546 2855533 := bbase (se 3 (by rfl) ⟨535412, by rfl⟩ : syracuseStep 2855533 = 1070825) (by norm_num)
theorem B5714549 : Blo 1691546 5714549 := bbase (se 5 (by rfl) ⟨267869, by rfl⟩ : syracuseStep 5714549 = 535739) (by norm_num)
theorem B2142865 : Blo 1691546 2142865 := bbase (se 2 (by rfl) ⟨803574, by rfl⟩ : syracuseStep 2142865 = 1607149) (by norm_num)
theorem B2855621 : Blo 1691546 2855621 := bbase (se 4 (by rfl) ⟨267714, by rfl⟩ : syracuseStep 2855621 = 535429) (by norm_num)
theorem B12858101 : Blo 1691546 12858101 := bbase (se 5 (by rfl) ⟨602723, by rfl⟩ : syracuseStep 12858101 = 1205447) (by norm_num)
theorem B12530485 : Blo 1691546 12530485 := bbase (se 5 (by rfl) ⟨587366, by rfl⟩ : syracuseStep 12530485 = 1174733) (by norm_num)
theorem B2143037 : Blo 1691546 2143037 := bbase (se 3 (by rfl) ⟨401819, by rfl⟩ : syracuseStep 2143037 = 803639) (by norm_num)
theorem B2855749 : Blo 1691546 2855749 := bbase (se 4 (by rfl) ⟨267726, by rfl⟩ : syracuseStep 2855749 = 535453) (by norm_num)
theorem B3806045 : Blo 1691546 3806045 := bbase (se 3 (by rfl) ⟨713633, by rfl⟩ : syracuseStep 3806045 = 1427267) (by norm_num)
theorem B2143093 : Blo 1691546 2143093 := bbase (se 5 (by rfl) ⟨100457, by rfl⟩ : syracuseStep 2143093 = 200915) (by norm_num)
theorem B2855837 : Blo 1691546 2855837 := bbase (se 3 (by rfl) ⟨535469, by rfl⟩ : syracuseStep 2855837 = 1070939) (by norm_num)
theorem B3806117 : Blo 1691546 3806117 := bbase (se 4 (by rfl) ⟨356823, by rfl⟩ : syracuseStep 3806117 = 713647) (by norm_num)
theorem B4821925 : Blo 1691546 4821925 := bbase (se 4 (by rfl) ⟨452055, by rfl⟩ : syracuseStep 4821925 = 904111) (by norm_num)
theorem B1831889 : Blo 1691546 1831889 := bbase (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) (by norm_num)
theorem B2143189 : Blo 1691546 2143189 := bbase (se 7 (by rfl) ⟨25115, by rfl⟩ : syracuseStep 2143189 = 50231) (by norm_num)
theorem B3806189 : Blo 1691546 3806189 := bbase (se 3 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 3806189 = 1427321) (by norm_num)
theorem B8565749 : Blo 1691546 8565749 := bbase (se 5 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 8565749 = 803039) (by norm_num)
theorem B1807381 : Blo 1691546 1807381 := bbase (se 6 (by rfl) ⟨42360, by rfl⟩ : syracuseStep 1807381 = 84721) (by norm_num)
theorem B2855965 : Blo 1691546 2855965 := bbase (se 3 (by rfl) ⟨535493, by rfl⟩ : syracuseStep 2855965 = 1070987) (by norm_num)
theorem B7935013 : Blo 1691546 7935013 := bbase (se 4 (by rfl) ⟨743907, by rfl⟩ : syracuseStep 7935013 = 1487815) (by norm_num)
theorem B5714981 : Blo 1691546 5714981 := bbase (se 4 (by rfl) ⟨535779, by rfl⟩ : syracuseStep 5714981 = 1071559) (by norm_num)
theorem B3806261 : Blo 1691546 3806261 := bbase (se 5 (by rfl) ⟨178418, by rfl⟩ : syracuseStep 3806261 = 356837) (by norm_num)
theorem B4822085 : Blo 1691546 4822085 := bbase (se 4 (by rfl) ⟨452070, by rfl⟩ : syracuseStep 4822085 = 904141) (by norm_num)
theorem B1807453 : Blo 1691546 1807453 := bbase (se 3 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 1807453 = 677795) (by norm_num)
theorem B2856053 : Blo 1691546 2856053 := bbase (se 5 (by rfl) ⟨133877, by rfl⟩ : syracuseStep 2856053 = 267755) (by norm_num)
theorem B3806333 : Blo 1691546 3806333 := bbase (se 3 (by rfl) ⟨713687, by rfl⟩ : syracuseStep 3806333 = 1427375) (by norm_num)
theorem B2143361 : Blo 1691546 2143361 := bbase (se 2 (by rfl) ⟨803760, by rfl⟩ : syracuseStep 2143361 = 1607521) (by norm_num)
theorem B25801877 : Blo 1691546 25801877 := bbase (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) (by norm_num)
theorem B12850325 : Blo 1691546 12850325 := bbase (se 6 (by rfl) ⟨301179, by rfl⟩ : syracuseStep 12850325 = 602359) (by norm_num)
theorem B3806405 : Blo 1691546 3806405 := bbase (se 4 (by rfl) ⟨356850, by rfl⟩ : syracuseStep 3806405 = 713701) (by norm_num)
theorem B2856181 : Blo 1691546 2856181 := bbase (se 5 (by rfl) ⟨133883, by rfl⟩ : syracuseStep 2856181 = 267767) (by norm_num)
theorem B3806477 : Blo 1691546 3806477 := bbase (se 3 (by rfl) ⟨713714, by rfl⟩ : syracuseStep 3806477 = 1427429) (by norm_num)
theorem B1807633 : Blo 1691546 1807633 := bbase (se 2 (by rfl) ⟨677862, by rfl⟩ : syracuseStep 1807633 = 1355725) (by norm_num)
theorem B6427957 : Blo 1691546 6427957 := bbase (se 5 (by rfl) ⟨301310, by rfl⟩ : syracuseStep 6427957 = 602621) (by norm_num)
theorem B4822325 : Blo 1691546 4822325 := bbase (se 5 (by rfl) ⟨226046, by rfl⟩ : syracuseStep 4822325 = 452093) (by norm_num)
theorem B2856269 : Blo 1691546 2856269 := bbase (se 3 (by rfl) ⟨535550, by rfl⟩ : syracuseStep 2856269 = 1071101) (by norm_num)
theorem B3806549 : Blo 1691546 3806549 := bbase (se 14 (by rfl) ⟨348, by rfl⟩ : syracuseStep 3806549 = 697) (by norm_num)
theorem B11744597 : Blo 1691546 11744597 := bbase (se 13 (by rfl) ⟨2150, by rfl⟩ : syracuseStep 11744597 = 4301) (by norm_num)
theorem B10843541 : Blo 1691546 10843541 := bbase (se 6 (by rfl) ⟨254145, by rfl⟩ : syracuseStep 10843541 = 508291) (by norm_num)
theorem B3806621 : Blo 1691546 3806621 := bbase (se 3 (by rfl) ⟨713741, by rfl⟩ : syracuseStep 3806621 = 1427483) (by norm_num)
theorem B3429797 : Blo 1691546 3429797 := bbase (se 4 (by rfl) ⟨321543, by rfl⟩ : syracuseStep 3429797 = 643087) (by norm_num)
theorem B4281781 : Blo 1691546 4281781 := bbase (se 5 (by rfl) ⟨200708, by rfl⟩ : syracuseStep 4281781 = 401417) (by norm_num)
theorem B2856397 : Blo 1691546 2856397 := bbase (se 3 (by rfl) ⟨535574, by rfl⟩ : syracuseStep 2856397 = 1071149) (by norm_num)
theorem B5715413 : Blo 1691546 5715413 := bbase (se 7 (by rfl) ⟨66977, by rfl⟩ : syracuseStep 5715413 = 133955) (by norm_num)
theorem B3806693 : Blo 1691546 3806693 := bbase (se 4 (by rfl) ⟨356877, by rfl⟩ : syracuseStep 3806693 = 713755) (by norm_num)
theorem B4822517 : Blo 1691546 4822517 := bbase (se 5 (by rfl) ⟨226055, by rfl⟩ : syracuseStep 4822517 = 452111) (by norm_num)
theorem B4281893 : Blo 1691546 4281893 := bbase (se 4 (by rfl) ⟨401427, by rfl⟩ : syracuseStep 4281893 = 802855) (by norm_num)
theorem B2856485 : Blo 1691546 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B3806765 : Blo 1691546 3806765 := bbase (se 3 (by rfl) ⟨713768, by rfl⟩ : syracuseStep 3806765 = 1427537) (by norm_num)
theorem B2823725 : Blo 1691546 2823725 := bbase (se 3 (by rfl) ⟨529448, by rfl⟩ : syracuseStep 2823725 = 1058897) (by norm_num)
theorem B4576837 : Blo 1691546 4576837 := bbase (se 4 (by rfl) ⟨429078, by rfl⟩ : syracuseStep 4576837 = 858157) (by norm_num)
theorem B19273301 : Blo 1691546 19273301 := bbase (se 8 (by rfl) ⟨112929, by rfl⟩ : syracuseStep 19273301 = 225859) (by norm_num)
theorem B6428261 : Blo 1691546 6428261 := bbase (se 4 (by rfl) ⟨602649, by rfl⟩ : syracuseStep 6428261 = 1205299) (by norm_num)
theorem B3806837 : Blo 1691546 3806837 := bbase (se 5 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 3806837 = 356891) (by norm_num)
theorem B2856613 : Blo 1691546 2856613 := bbase (se 4 (by rfl) ⟨267807, by rfl⟩ : syracuseStep 2856613 = 535615) (by norm_num)
theorem B3806909 : Blo 1691546 3806909 := bbase (se 3 (by rfl) ⟨713795, by rfl⟩ : syracuseStep 3806909 = 1427591) (by norm_num)
theorem B1808077 : Blo 1691546 1808077 := bbase (se 3 (by rfl) ⟨339014, by rfl⟩ : syracuseStep 1808077 = 678029) (by norm_num)
theorem B8132309 : Blo 1691546 8132309 := bbase (se 7 (by rfl) ⟨95300, by rfl⟩ : syracuseStep 8132309 = 190601) (by norm_num)
theorem B4282085 : Blo 1691546 4282085 := bbase (se 4 (by rfl) ⟨401445, by rfl⟩ : syracuseStep 4282085 = 802891) (by norm_num)
theorem B2856701 : Blo 1691546 2856701 := bbase (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) (by norm_num)
theorem B3806981 : Blo 1691546 3806981 := bbase (se 4 (by rfl) ⟨356904, by rfl⟩ : syracuseStep 3806981 = 713809) (by norm_num)
theorem B7231301 : Blo 1691546 7231301 := bbase (se 4 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 7231301 = 1355869) (by norm_num)
theorem B1808201 : Blo 1691546 1808201 := bbase (se 2 (by rfl) ⟨678075, by rfl⟩ : syracuseStep 1808201 = 1356151) (by norm_num)
theorem B3807053 : Blo 1691546 3807053 := bbase (se 3 (by rfl) ⟨713822, by rfl⟩ : syracuseStep 3807053 = 1427645) (by norm_num)
theorem B2537333 : Blo 1691546 2537333 := bbase (se 5 (by rfl) ⟨118937, by rfl⟩ : syracuseStep 2537333 = 237875) (by norm_num)
theorem B2856829 : Blo 1691546 2856829 := bbase (se 3 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 2856829 = 1071311) (by norm_num)
theorem B2537357 : Blo 1691546 2537357 := bbase (se 3 (by rfl) ⟨475754, by rfl⟩ : syracuseStep 2537357 = 951509) (by norm_num)
theorem B3807125 : Blo 1691546 3807125 := bbase (se 6 (by rfl) ⟨89229, by rfl⟩ : syracuseStep 3807125 = 178459) (by norm_num)
theorem B2537381 : Blo 1691546 2537381 := bbase (se 4 (by rfl) ⟨237879, by rfl⟩ : syracuseStep 2537381 = 475759) (by norm_num)
theorem B2537405 : Blo 1691546 2537405 := bbase (se 3 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 2537405 = 951527) (by norm_num)
theorem B2537429 : Blo 1691546 2537429 := bbase (se 7 (by rfl) ⟨29735, by rfl⟩ : syracuseStep 2537429 = 59471) (by norm_num)
theorem B2856917 : Blo 1691546 2856917 := bbase (se 7 (by rfl) ⟨33479, by rfl⟩ : syracuseStep 2856917 = 66959) (by norm_num)
theorem B3807197 : Blo 1691546 3807197 := bbase (se 3 (by rfl) ⟨713849, by rfl⟩ : syracuseStep 3807197 = 1427699) (by norm_num)
theorem B2537453 : Blo 1691546 2537453 := bbase (se 3 (by rfl) ⟨475772, by rfl⟩ : syracuseStep 2537453 = 951545) (by norm_num)
theorem B2537477 : Blo 1691546 2537477 := bbase (se 4 (by rfl) ⟨237888, by rfl⟩ : syracuseStep 2537477 = 475777) (by norm_num)
theorem B2537501 : Blo 1691546 2537501 := bbase (se 3 (by rfl) ⟨475781, by rfl⟩ : syracuseStep 2537501 = 951563) (by norm_num)
theorem B3807269 : Blo 1691546 3807269 := bbase (se 4 (by rfl) ⟨356931, by rfl⟩ : syracuseStep 3807269 = 713863) (by norm_num)
theorem B2537525 : Blo 1691546 2537525 := bbase (se 5 (by rfl) ⟨118946, by rfl⟩ : syracuseStep 2537525 = 237893) (by norm_num)
theorem B4282429 : Blo 1691546 4282429 := bbase (se 3 (by rfl) ⟨802955, by rfl⟩ : syracuseStep 4282429 = 1605911) (by norm_num)
theorem B1808453 : Blo 1691546 1808453 := bbase (se 4 (by rfl) ⟨169542, by rfl⟩ : syracuseStep 1808453 = 339085) (by norm_num)
theorem B2537549 : Blo 1691546 2537549 := bbase (se 3 (by rfl) ⟨475790, by rfl⟩ : syracuseStep 2537549 = 951581) (by norm_num)
theorem B6101077 : Blo 1691546 6101077 := bbase (se 8 (by rfl) ⟨35748, by rfl⟩ : syracuseStep 6101077 = 71497) (by norm_num)
theorem B2857045 : Blo 1691546 2857045 := bbase (se 8 (by rfl) ⟨16740, by rfl⟩ : syracuseStep 2857045 = 33481) (by norm_num)
theorem B2537573 : Blo 1691546 2537573 := bbase (se 4 (by rfl) ⟨237897, by rfl⟩ : syracuseStep 2537573 = 475795) (by norm_num)
theorem B7231589 : Blo 1691546 7231589 := bbase (se 4 (by rfl) ⟨677961, by rfl⟩ : syracuseStep 7231589 = 1355923) (by norm_num)
theorem B3807341 : Blo 1691546 3807341 := bbase (se 3 (by rfl) ⟨713876, by rfl⟩ : syracuseStep 3807341 = 1427753) (by norm_num)
theorem B2537597 : Blo 1691546 2537597 := bbase (se 3 (by rfl) ⟨475799, by rfl⟩ : syracuseStep 2537597 = 951599) (by norm_num)
theorem B2537621 : Blo 1691546 2537621 := bbase (se 6 (by rfl) ⟨59475, by rfl⟩ : syracuseStep 2537621 = 118951) (by norm_num)
theorem B2537645 : Blo 1691546 2537645 := bbase (se 3 (by rfl) ⟨475808, by rfl⟩ : syracuseStep 2537645 = 951617) (by norm_num)
theorem B4282541 : Blo 1691546 4282541 := bbase (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) (by norm_num)
theorem B2857133 : Blo 1691546 2857133 := bbase (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) (by norm_num)
theorem B3807413 : Blo 1691546 3807413 := bbase (se 5 (by rfl) ⟨178472, by rfl⟩ : syracuseStep 3807413 = 356945) (by norm_num)
theorem B2537669 : Blo 1691546 2537669 := bbase (se 4 (by rfl) ⟨237906, by rfl⟩ : syracuseStep 2537669 = 475813) (by norm_num)
theorem B1833161 : Blo 1691546 1833161 := bbase (se 2 (by rfl) ⟨687435, by rfl⟩ : syracuseStep 1833161 = 1374871) (by norm_num)
theorem B7936213 : Blo 1691546 7936213 := bbase (se 7 (by rfl) ⟨93002, by rfl⟩ : syracuseStep 7936213 = 186005) (by norm_num)
theorem B2537693 : Blo 1691546 2537693 := bbase (se 3 (by rfl) ⟨475817, by rfl⟩ : syracuseStep 2537693 = 951635) (by norm_num)
theorem B2537717 : Blo 1691546 2537717 := bbase (se 5 (by rfl) ⟨118955, by rfl⟩ : syracuseStep 2537717 = 237911) (by norm_num)
theorem B3807485 : Blo 1691546 3807485 := bbase (se 3 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 3807485 = 1427807) (by norm_num)
theorem B8567045 : Blo 1691546 8567045 := bbase (se 4 (by rfl) ⟨803160, by rfl⟩ : syracuseStep 8567045 = 1606321) (by norm_num)
theorem B2537741 : Blo 1691546 2537741 := bbase (se 3 (by rfl) ⟨475826, by rfl⟩ : syracuseStep 2537741 = 951653) (by norm_num)
theorem B2537765 : Blo 1691546 2537765 := bbase (se 4 (by rfl) ⟨237915, by rfl⟩ : syracuseStep 2537765 = 475831) (by norm_num)
theorem B2857261 : Blo 1691546 2857261 := bbase (se 3 (by rfl) ⟨535736, by rfl⟩ : syracuseStep 2857261 = 1071473) (by norm_num)
theorem B2537789 : Blo 1691546 2537789 := bbase (se 3 (by rfl) ⟨475835, by rfl⟩ : syracuseStep 2537789 = 951671) (by norm_num)
theorem B3807557 : Blo 1691546 3807557 := bbase (se 4 (by rfl) ⟨356958, by rfl⟩ : syracuseStep 3807557 = 713917) (by norm_num)
theorem B2537813 : Blo 1691546 2537813 := bbase (se 10 (by rfl) ⟨3717, by rfl⟩ : syracuseStep 2537813 = 7435) (by norm_num)
theorem B46332245 : Blo 1691546 46332245 := bbase (se 10 (by rfl) ⟨67869, by rfl⟩ : syracuseStep 46332245 = 135739) (by norm_num)
theorem B8690005 : Blo 1691546 8690005 := bbase (se 10 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 8690005 = 25459) (by norm_num)
theorem B2537837 : Blo 1691546 2537837 := bbase (se 3 (by rfl) ⟨475844, by rfl⟩ : syracuseStep 2537837 = 951689) (by norm_num)
theorem B4282733 : Blo 1691546 4282733 := bbase (se 3 (by rfl) ⟨803012, by rfl⟩ : syracuseStep 4282733 = 1606025) (by norm_num)
theorem B2537861 : Blo 1691546 2537861 := bbase (se 4 (by rfl) ⟨237924, by rfl⟩ : syracuseStep 2537861 = 475849) (by norm_num)
theorem B2857349 : Blo 1691546 2857349 := bbase (se 4 (by rfl) ⟨267876, by rfl⟩ : syracuseStep 2857349 = 535753) (by norm_num)
theorem B3807629 : Blo 1691546 3807629 := bbase (se 3 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 3807629 = 1427861) (by norm_num)
theorem B2537885 : Blo 1691546 2537885 := bbase (se 3 (by rfl) ⟨475853, by rfl⟩ : syracuseStep 2537885 = 951707) (by norm_num)
theorem B2537909 : Blo 1691546 2537909 := bbase (se 5 (by rfl) ⟨118964, by rfl⟩ : syracuseStep 2537909 = 237929) (by norm_num)
theorem B2537933 : Blo 1691546 2537933 := bbase (se 3 (by rfl) ⟨475862, by rfl⟩ : syracuseStep 2537933 = 951725) (by norm_num)
theorem B3807701 : Blo 1691546 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B2537957 : Blo 1691546 2537957 := bbase (se 4 (by rfl) ⟨237933, by rfl⟩ : syracuseStep 2537957 = 475867) (by norm_num)
theorem B2537981 : Blo 1691546 2537981 := bbase (se 3 (by rfl) ⟨475871, by rfl⟩ : syracuseStep 2537981 = 951743) (by norm_num)
theorem B2857477 : Blo 1691546 2857477 := bbase (se 4 (by rfl) ⟨267888, by rfl⟩ : syracuseStep 2857477 = 535777) (by norm_num)
theorem B2538005 : Blo 1691546 2538005 := bbase (se 6 (by rfl) ⟨59484, by rfl⟩ : syracuseStep 2538005 = 118969) (by norm_num)
theorem B6101525 : Blo 1691546 6101525 := bbase (se 6 (by rfl) ⟨143004, by rfl⟩ : syracuseStep 6101525 = 286009) (by norm_num)
theorem B3807773 : Blo 1691546 3807773 := bbase (se 3 (by rfl) ⟨713957, by rfl⟩ : syracuseStep 3807773 = 1427915) (by norm_num)
theorem B2538029 : Blo 1691546 2538029 := bbase (se 3 (by rfl) ⟨475880, by rfl⟩ : syracuseStep 2538029 = 951761) (by norm_num)
theorem B2538053 : Blo 1691546 2538053 := bbase (se 4 (by rfl) ⟨237942, by rfl⟩ : syracuseStep 2538053 = 475885) (by norm_num)
theorem B2538077 : Blo 1691546 2538077 := bbase (se 3 (by rfl) ⟨475889, by rfl⟩ : syracuseStep 2538077 = 951779) (by norm_num)
theorem B2857565 : Blo 1691546 2857565 := bbase (se 3 (by rfl) ⟨535793, by rfl⟩ : syracuseStep 2857565 = 1071587) (by norm_num)
theorem B3807845 : Blo 1691546 3807845 := bbase (se 4 (by rfl) ⟨356985, by rfl⟩ : syracuseStep 3807845 = 713971) (by norm_num)
theorem B2538101 : Blo 1691546 2538101 := bbase (se 5 (by rfl) ⟨118973, by rfl⟩ : syracuseStep 2538101 = 237947) (by norm_num)
theorem B2538125 : Blo 1691546 2538125 := bbase (se 3 (by rfl) ⟨475898, by rfl⟩ : syracuseStep 2538125 = 951797) (by norm_num)
theorem B2710181 : Blo 1691546 2710181 := bbase (se 4 (by rfl) ⟨254079, by rfl⟩ : syracuseStep 2710181 = 508159) (by norm_num)
theorem B2538149 : Blo 1691546 2538149 := bbase (se 4 (by rfl) ⟨237951, by rfl⟩ : syracuseStep 2538149 = 475903) (by norm_num)
theorem B3807917 : Blo 1691546 3807917 := bbase (se 3 (by rfl) ⟨713984, by rfl⟩ : syracuseStep 3807917 = 1427969) (by norm_num)
theorem B2538173 : Blo 1691546 2538173 := bbase (se 3 (by rfl) ⟨475907, by rfl⟩ : syracuseStep 2538173 = 951815) (by norm_num)
theorem B4283077 : Blo 1691546 4283077 := bbase (se 4 (by rfl) ⟨401538, by rfl⟩ : syracuseStep 4283077 = 803077) (by norm_num)
theorem B2538197 : Blo 1691546 2538197 := bbase (se 7 (by rfl) ⟨29744, by rfl⟩ : syracuseStep 2538197 = 59489) (by norm_num)
theorem B2857693 : Blo 1691546 2857693 := bbase (se 3 (by rfl) ⟨535817, by rfl⟩ : syracuseStep 2857693 = 1071635) (by norm_num)
theorem B2538221 : Blo 1691546 2538221 := bbase (se 3 (by rfl) ⟨475916, by rfl⟩ : syracuseStep 2538221 = 951833) (by norm_num)
theorem B3807989 : Blo 1691546 3807989 := bbase (se 5 (by rfl) ⟨178499, by rfl⟩ : syracuseStep 3807989 = 356999) (by norm_num)
theorem B2538245 : Blo 1691546 2538245 := bbase (se 4 (by rfl) ⟨237960, by rfl⟩ : syracuseStep 2538245 = 475921) (by norm_num)
theorem B2538269 : Blo 1691546 2538269 := bbase (se 3 (by rfl) ⟨475925, by rfl⟩ : syracuseStep 2538269 = 951851) (by norm_num)
theorem B4283189 : Blo 1691546 4283189 := bbase (se 5 (by rfl) ⟨200774, by rfl⟩ : syracuseStep 4283189 = 401549) (by norm_num)
theorem B2538293 : Blo 1691546 2538293 := bbase (se 5 (by rfl) ⟨118982, by rfl⟩ : syracuseStep 2538293 = 237965) (by norm_num)
theorem B2857781 : Blo 1691546 2857781 := bbase (se 5 (by rfl) ⟨133958, by rfl⟩ : syracuseStep 2857781 = 267917) (by norm_num)
theorem B3808061 : Blo 1691546 3808061 := bbase (se 3 (by rfl) ⟨714011, by rfl⟩ : syracuseStep 3808061 = 1428023) (by norm_num)
theorem B2538317 : Blo 1691546 2538317 := bbase (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) (by norm_num)
theorem B11139925 : Blo 1691546 11139925 := bbase (se 9 (by rfl) ⟨32636, by rfl⟩ : syracuseStep 11139925 = 65273) (by norm_num)
theorem B7232341 : Blo 1691546 7232341 := bbase (se 9 (by rfl) ⟨21188, by rfl⟩ : syracuseStep 7232341 = 42377) (by norm_num)
theorem B2538341 : Blo 1691546 2538341 := bbase (se 4 (by rfl) ⟨237969, by rfl⟩ : syracuseStep 2538341 = 475939) (by norm_num)
theorem B2538365 : Blo 1691546 2538365 := bbase (se 3 (by rfl) ⟨475943, by rfl⟩ : syracuseStep 2538365 = 951887) (by norm_num)
theorem B3808133 : Blo 1691546 3808133 := bbase (se 4 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 3808133 = 714025) (by norm_num)
theorem B2538389 : Blo 1691546 2538389 := bbase (se 6 (by rfl) ⟨59493, by rfl⟩ : syracuseStep 2538389 = 118987) (by norm_num)
theorem B2538413 : Blo 1691546 2538413 := bbase (se 3 (by rfl) ⟨475952, by rfl⟩ : syracuseStep 2538413 = 951905) (by norm_num)
theorem B2538437 : Blo 1691546 2538437 := bbase (se 4 (by rfl) ⟨237978, by rfl⟩ : syracuseStep 2538437 = 475957) (by norm_num)
theorem B3808205 : Blo 1691546 3808205 := bbase (se 3 (by rfl) ⟨714038, by rfl⟩ : syracuseStep 3808205 = 1428077) (by norm_num)
theorem B2538461 : Blo 1691546 2538461 := bbase (se 3 (by rfl) ⟨475961, by rfl⟩ : syracuseStep 2538461 = 951923) (by norm_num)
theorem B4283381 : Blo 1691546 4283381 := bbase (se 5 (by rfl) ⟨200783, by rfl⟩ : syracuseStep 4283381 = 401567) (by norm_num)
theorem B2538485 : Blo 1691546 2538485 := bbase (se 5 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 2538485 = 237983) (by norm_num)
theorem B5790709 : Blo 1691546 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B2538509 : Blo 1691546 2538509 := bbase (se 3 (by rfl) ⟨475970, by rfl⟩ : syracuseStep 2538509 = 951941) (by norm_num)
theorem B3808277 : Blo 1691546 3808277 := bbase (se 6 (by rfl) ⟨89256, by rfl⟩ : syracuseStep 3808277 = 178513) (by norm_num)
theorem B16268309 : Blo 1691546 16268309 := bbase (se 6 (by rfl) ⟨381288, by rfl⟩ : syracuseStep 16268309 = 762577) (by norm_num)
theorem B2710565 : Blo 1691546 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B2538533 : Blo 1691546 2538533 := bbase (se 4 (by rfl) ⟨237987, by rfl⟩ : syracuseStep 2538533 = 475975) (by norm_num)
theorem B2538557 : Blo 1691546 2538557 := bbase (se 3 (by rfl) ⟨475979, by rfl⟩ : syracuseStep 2538557 = 951959) (by norm_num)
theorem B21683285 : Blo 1691546 21683285 := bbase (se 8 (by rfl) ⟨127050, by rfl⟩ : syracuseStep 21683285 = 254101) (by norm_num)
theorem B2538581 : Blo 1691546 2538581 := bbase (se 8 (by rfl) ⟨14874, by rfl⟩ : syracuseStep 2538581 = 29749) (by norm_num)
theorem B3808349 : Blo 1691546 3808349 := bbase (se 3 (by rfl) ⟨714065, by rfl⟩ : syracuseStep 3808349 = 1428131) (by norm_num)
theorem B2538605 : Blo 1691546 2538605 := bbase (se 3 (by rfl) ⟨475988, by rfl⟩ : syracuseStep 2538605 = 951977) (by norm_num)
theorem B2538629 : Blo 1691546 2538629 := bbase (se 4 (by rfl) ⟨237996, by rfl⟩ : syracuseStep 2538629 = 475993) (by norm_num)
theorem B2538653 : Blo 1691546 2538653 := bbase (se 3 (by rfl) ⟨475997, by rfl⟩ : syracuseStep 2538653 = 951995) (by norm_num)
theorem B2710693 : Blo 1691546 2710693 := bbase (se 4 (by rfl) ⟨254127, by rfl⟩ : syracuseStep 2710693 = 508255) (by norm_num)
theorem B3808421 : Blo 1691546 3808421 := bbase (se 4 (by rfl) ⟨357039, by rfl⟩ : syracuseStep 3808421 = 714079) (by norm_num)
theorem B2538677 : Blo 1691546 2538677 := bbase (se 5 (by rfl) ⟨119000, by rfl⟩ : syracuseStep 2538677 = 238001) (by norm_num)
theorem B2538701 : Blo 1691546 2538701 := bbase (se 3 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 2538701 = 952013) (by norm_num)
theorem B31284437 : Blo 1691546 31284437 := bbase (se 7 (by rfl) ⟨366614, by rfl⟩ : syracuseStep 31284437 = 733229) (by norm_num)
theorem B2538725 : Blo 1691546 2538725 := bbase (se 4 (by rfl) ⟨238005, by rfl⟩ : syracuseStep 2538725 = 476011) (by norm_num)
theorem B3808493 : Blo 1691546 3808493 := bbase (se 3 (by rfl) ⟨714092, by rfl⟩ : syracuseStep 3808493 = 1428185) (by norm_num)
theorem B2538749 : Blo 1691546 2538749 := bbase (se 3 (by rfl) ⟨476015, by rfl⟩ : syracuseStep 2538749 = 952031) (by norm_num)
theorem B12197141 : Blo 1691546 12197141 := bbase (se 6 (by rfl) ⟨285870, by rfl⟩ : syracuseStep 12197141 = 571741) (by norm_num)
theorem B2538773 : Blo 1691546 2538773 := bbase (se 6 (by rfl) ⟨59502, by rfl⟩ : syracuseStep 2538773 = 119005) (by norm_num)
theorem B2538797 : Blo 1691546 2538797 := bbase (se 3 (by rfl) ⟨476024, by rfl⟩ : syracuseStep 2538797 = 952049) (by norm_num)
theorem B3808565 : Blo 1691546 3808565 := bbase (se 5 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 3808565 = 357053) (by norm_num)
theorem B2538821 : Blo 1691546 2538821 := bbase (se 4 (by rfl) ⟨238014, by rfl⟩ : syracuseStep 2538821 = 476029) (by norm_num)
theorem B4283725 : Blo 1691546 4283725 := bbase (se 3 (by rfl) ⟨803198, by rfl⟩ : syracuseStep 4283725 = 1606397) (by norm_num)
theorem B2538845 : Blo 1691546 2538845 := bbase (se 3 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 2538845 = 952067) (by norm_num)
theorem B2538869 : Blo 1691546 2538869 := bbase (se 5 (by rfl) ⟨119009, by rfl⟩ : syracuseStep 2538869 = 238019) (by norm_num)
theorem B3808637 : Blo 1691546 3808637 := bbase (se 3 (by rfl) ⟨714119, by rfl⟩ : syracuseStep 3808637 = 1428239) (by norm_num)
theorem B2538893 : Blo 1691546 2538893 := bbase (se 3 (by rfl) ⟨476042, by rfl⟩ : syracuseStep 2538893 = 952085) (by norm_num)
theorem B2538917 : Blo 1691546 2538917 := bbase (se 4 (by rfl) ⟨238023, by rfl⟩ : syracuseStep 2538917 = 476047) (by norm_num)
theorem B10288565 : Blo 1691546 10288565 := bbase (se 5 (by rfl) ⟨482276, by rfl⟩ : syracuseStep 10288565 = 964553) (by norm_num)
theorem B4283837 : Blo 1691546 4283837 := bbase (se 3 (by rfl) ⟨803219, by rfl⟩ : syracuseStep 4283837 = 1606439) (by norm_num)
theorem B2538941 : Blo 1691546 2538941 := bbase (se 3 (by rfl) ⟨476051, by rfl⟩ : syracuseStep 2538941 = 952103) (by norm_num)
theorem B3808709 : Blo 1691546 3808709 := bbase (se 4 (by rfl) ⟨357066, by rfl⟩ : syracuseStep 3808709 = 714133) (by norm_num)
theorem B2538965 : Blo 1691546 2538965 := bbase (se 7 (by rfl) ⟨29753, by rfl⟩ : syracuseStep 2538965 = 59507) (by norm_num)
theorem B5422565 : Blo 1691546 5422565 := bbase (se 4 (by rfl) ⟨508365, by rfl⟩ : syracuseStep 5422565 = 1016731) (by norm_num)
theorem B2538989 : Blo 1691546 2538989 := bbase (se 3 (by rfl) ⟨476060, by rfl⟩ : syracuseStep 2538989 = 952121) (by norm_num)
theorem B2539013 : Blo 1691546 2539013 := bbase (se 4 (by rfl) ⟨238032, by rfl⟩ : syracuseStep 2539013 = 476065) (by norm_num)
theorem B3808781 : Blo 1691546 3808781 := bbase (se 3 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 3808781 = 1428293) (by norm_num)
theorem B8568341 : Blo 1691546 8568341 := bbase (se 6 (by rfl) ⟨200820, by rfl⟩ : syracuseStep 8568341 = 401641) (by norm_num)
theorem B2539037 : Blo 1691546 2539037 := bbase (se 3 (by rfl) ⟨476069, by rfl⟩ : syracuseStep 2539037 = 952139) (by norm_num)
theorem B5709365 : Blo 1691546 5709365 := bbase (se 5 (by rfl) ⟨267626, by rfl⟩ : syracuseStep 5709365 = 535253) (by norm_num)
theorem B2539061 : Blo 1691546 2539061 := bbase (se 5 (by rfl) ⟨119018, by rfl⟩ : syracuseStep 2539061 = 238037) (by norm_num)
theorem B7233077 : Blo 1691546 7233077 := bbase (se 5 (by rfl) ⟨339050, by rfl⟩ : syracuseStep 7233077 = 678101) (by norm_num)
theorem B2539085 : Blo 1691546 2539085 := bbase (se 3 (by rfl) ⟨476078, by rfl⟩ : syracuseStep 2539085 = 952157) (by norm_num)
theorem B3808853 : Blo 1691546 3808853 := bbase (se 8 (by rfl) ⟨22317, by rfl⟩ : syracuseStep 3808853 = 44635) (by norm_num)
theorem B2539109 : Blo 1691546 2539109 := bbase (se 4 (by rfl) ⟨238041, by rfl⟩ : syracuseStep 2539109 = 476083) (by norm_num)
theorem B4284029 : Blo 1691546 4284029 := bbase (se 3 (by rfl) ⟨803255, by rfl⟩ : syracuseStep 4284029 = 1606511) (by norm_num)
theorem B2539133 : Blo 1691546 2539133 := bbase (se 3 (by rfl) ⟨476087, by rfl⟩ : syracuseStep 2539133 = 952175) (by norm_num)
theorem B2539157 : Blo 1691546 2539157 := bbase (se 6 (by rfl) ⟨59511, by rfl⟩ : syracuseStep 2539157 = 119023) (by norm_num)
theorem B3808925 : Blo 1691546 3808925 := bbase (se 3 (by rfl) ⟨714173, by rfl⟩ : syracuseStep 3808925 = 1428347) (by norm_num)
theorem B2539181 : Blo 1691546 2539181 := bbase (se 3 (by rfl) ⟨476096, by rfl⟩ : syracuseStep 2539181 = 952193) (by norm_num)
theorem B2539205 : Blo 1691546 2539205 := bbase (se 4 (by rfl) ⟨238050, by rfl⟩ : syracuseStep 2539205 = 476101) (by norm_num)
theorem B2539229 : Blo 1691546 2539229 := bbase (se 3 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 2539229 = 952211) (by norm_num)
theorem B3808997 : Blo 1691546 3808997 := bbase (se 4 (by rfl) ⟨357093, by rfl⟩ : syracuseStep 3808997 = 714187) (by norm_num)
theorem B2539253 : Blo 1691546 2539253 := bbase (se 5 (by rfl) ⟨119027, by rfl⟩ : syracuseStep 2539253 = 238055) (by norm_num)
theorem B2539277 : Blo 1691546 2539277 := bbase (se 3 (by rfl) ⟨476114, by rfl⟩ : syracuseStep 2539277 = 952229) (by norm_num)
theorem B2539301 : Blo 1691546 2539301 := bbase (se 4 (by rfl) ⟨238059, by rfl⟩ : syracuseStep 2539301 = 476119) (by norm_num)
theorem B3809069 : Blo 1691546 3809069 := bbase (se 3 (by rfl) ⟨714200, by rfl⟩ : syracuseStep 3809069 = 1428401) (by norm_num)
theorem B14466869 : Blo 1691546 14466869 := bbase (se 5 (by rfl) ⟨678134, by rfl⟩ : syracuseStep 14466869 = 1356269) (by norm_num)
theorem B2539325 : Blo 1691546 2539325 := bbase (se 3 (by rfl) ⟨476123, by rfl⟩ : syracuseStep 2539325 = 952247) (by norm_num)
theorem B2539349 : Blo 1691546 2539349 := bbase (se 9 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 2539349 = 14879) (by norm_num)
theorem B8134501 : Blo 1691546 8134501 := bbase (se 4 (by rfl) ⟨762609, by rfl⟩ : syracuseStep 8134501 = 1525219) (by norm_num)
theorem B2539373 : Blo 1691546 2539373 := bbase (se 3 (by rfl) ⟨476132, by rfl⟩ : syracuseStep 2539373 = 952265) (by norm_num)
theorem B3809141 : Blo 1691546 3809141 := bbase (se 5 (by rfl) ⟨178553, by rfl⟩ : syracuseStep 3809141 = 357107) (by norm_num)
theorem B2539397 : Blo 1691546 2539397 := bbase (se 4 (by rfl) ⟨238068, by rfl⟩ : syracuseStep 2539397 = 476137) (by norm_num)
theorem B2539421 : Blo 1691546 2539421 := bbase (se 3 (by rfl) ⟨476141, by rfl⟩ : syracuseStep 2539421 = 952283) (by norm_num)
theorem B13205429 : Blo 1691546 13205429 := bbase (se 5 (by rfl) ⟨619004, by rfl⟩ : syracuseStep 13205429 = 1238009) (by norm_num)
theorem B2539445 : Blo 1691546 2539445 := bbase (se 5 (by rfl) ⟨119036, by rfl⟩ : syracuseStep 2539445 = 238073) (by norm_num)
theorem B3809213 : Blo 1691546 3809213 := bbase (se 3 (by rfl) ⟨714227, by rfl⟩ : syracuseStep 3809213 = 1428455) (by norm_num)
theorem B2539469 : Blo 1691546 2539469 := bbase (se 3 (by rfl) ⟨476150, by rfl⟩ : syracuseStep 2539469 = 952301) (by norm_num)
theorem B4284373 : Blo 1691546 4284373 := bbase (se 7 (by rfl) ⟨50207, by rfl⟩ : syracuseStep 4284373 = 100415) (by norm_num)
theorem B5709797 : Blo 1691546 5709797 := bbase (se 4 (by rfl) ⟨535293, by rfl⟩ : syracuseStep 5709797 = 1070587) (by norm_num)
theorem B2539493 : Blo 1691546 2539493 := bbase (se 4 (by rfl) ⟨238077, by rfl⟩ : syracuseStep 2539493 = 476155) (by norm_num)
theorem B2539517 : Blo 1691546 2539517 := bbase (se 3 (by rfl) ⟨476159, by rfl⟩ : syracuseStep 2539517 = 952319) (by norm_num)
theorem B2539523 : Blo 1691546 2539523 := bstep (se 1 (by rfl) ⟨1904642, by rfl⟩ : syracuseStep 2539523 = 3809285) B3809285
theorem B2539553 : Blo 1691546 2539553 := bstep (se 2 (by rfl) ⟨952332, by rfl⟩ : syracuseStep 2539553 = 1904665) B1904665
theorem B2711603 : Blo 1691546 2711603 := bstep (se 1 (by rfl) ⟨2033702, by rfl⟩ : syracuseStep 2711603 = 4067405) B4067405
theorem B2539571 : Blo 1691546 2539571 := bstep (se 1 (by rfl) ⟨1904678, by rfl⟩ : syracuseStep 2539571 = 3809357) B3809357
theorem B5709905 : Blo 1691546 5709905 := bstep (se 2 (by rfl) ⟨2141214, by rfl⟩ : syracuseStep 5709905 = 4282429) B4282429
theorem B2539601 : Blo 1691546 2539601 := bstep (se 2 (by rfl) ⟨952350, by rfl⟩ : syracuseStep 2539601 = 1904701) B1904701
theorem B4284515 : Blo 1691546 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B2539619 : Blo 1691546 2539619 := bstep (se 1 (by rfl) ⟨1904714, by rfl⟩ : syracuseStep 2539619 = 3809429) B3809429
theorem B8134769 : Blo 1691546 8134769 := bstep (se 2 (by rfl) ⟨3050538, by rfl⟩ : syracuseStep 8134769 = 6101077) B6101077
theorem B3809393 : Blo 1691546 3809393 := bstep (se 2 (by rfl) ⟨1428522, by rfl⟩ : syracuseStep 3809393 = 2857045) B2857045
theorem B2539649 : Blo 1691546 2539649 := bstep (se 2 (by rfl) ⟨952368, by rfl⟩ : syracuseStep 2539649 = 1904737) B1904737
theorem B3809411 : Blo 1691546 3809411 := bstep (se 1 (by rfl) ⟨2857058, by rfl⟩ : syracuseStep 3809411 = 5714117) B5714117
theorem B2539667 : Blo 1691546 2539667 := bstep (se 1 (by rfl) ⟨1904750, by rfl⟩ : syracuseStep 2539667 = 3809501) B3809501
theorem B3211427 : Blo 1691546 3211427 := bstep (se 1 (by rfl) ⟨2408570, by rfl⟩ : syracuseStep 3211427 = 4817141) B4817141
theorem B2408611 : Blo 1691546 2408611 := bstep (se 1 (by rfl) ⟨1806458, by rfl⟩ : syracuseStep 2408611 = 3612917) B3612917
theorem B2539697 : Blo 1691546 2539697 := bstep (se 2 (by rfl) ⟨952386, by rfl⟩ : syracuseStep 2539697 = 1904773) B1904773
theorem B2539715 : Blo 1691546 2539715 := bstep (se 1 (by rfl) ⟨1904786, by rfl⟩ : syracuseStep 2539715 = 3809573) B3809573
theorem B42320069 : Blo 1691546 42320069 := bstep (se 4 (by rfl) ⟨3967506, by rfl⟩ : syracuseStep 42320069 = 7935013) B7935013
theorem B2539745 : Blo 1691546 2539745 := bstep (se 2 (by rfl) ⟨952404, by rfl⟩ : syracuseStep 2539745 = 1904809) B1904809
theorem B2539763 : Blo 1691546 2539763 := bstep (se 1 (by rfl) ⟨1904822, by rfl⟩ : syracuseStep 2539763 = 3809645) B3809645
theorem B2408707 : Blo 1691546 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B2539793 : Blo 1691546 2539793 := bstep (se 2 (by rfl) ⟨952422, by rfl⟩ : syracuseStep 2539793 = 1904845) B1904845
theorem B5144867 : Blo 1691546 5144867 := bstep (se 1 (by rfl) ⟨3858650, by rfl⟩ : syracuseStep 5144867 = 7717301) B7717301
theorem B2539811 : Blo 1691546 2539811 := bstep (se 1 (by rfl) ⟨1904858, by rfl⟩ : syracuseStep 2539811 = 3809717) B3809717
theorem B2539841 : Blo 1691546 2539841 := bstep (se 2 (by rfl) ⟨952440, by rfl⟩ : syracuseStep 2539841 = 1904881) B1904881
theorem B2539859 : Blo 1691546 2539859 := bstep (se 1 (by rfl) ⟨1904894, by rfl⟩ : syracuseStep 2539859 = 3809789) B3809789
theorem B3613027 : Blo 1691546 3613027 := bstep (se 1 (by rfl) ⟨2709770, by rfl⟩ : syracuseStep 3613027 = 5419541) B5419541
theorem B3858787 : Blo 1691546 3858787 := bstep (se 1 (by rfl) ⟨2894090, by rfl⟩ : syracuseStep 3858787 = 5788181) B5788181
theorem B2539889 : Blo 1691546 2539889 := bstep (se 2 (by rfl) ⟨952458, by rfl⟩ : syracuseStep 2539889 = 1904917) B1904917
theorem B2539907 : Blo 1691546 2539907 := bstep (se 1 (by rfl) ⟨1904930, by rfl⟩ : syracuseStep 2539907 = 3809861) B3809861
theorem B3809681 : Blo 1691546 3809681 := bstep (se 2 (by rfl) ⟨1428630, by rfl⟩ : syracuseStep 3809681 = 2857261) B2857261
theorem B2539937 : Blo 1691546 2539937 := bstep (se 2 (by rfl) ⟨952476, by rfl⟩ : syracuseStep 2539937 = 1904953) B1904953
theorem B3809699 : Blo 1691546 3809699 := bstep (se 1 (by rfl) ⟨2857274, by rfl⟩ : syracuseStep 3809699 = 5714549) B5714549
theorem B2539955 : Blo 1691546 2539955 := bstep (se 1 (by rfl) ⟨1904966, by rfl⟩ : syracuseStep 2539955 = 3809933) B3809933
theorem B8135117 : Blo 1691546 8135117 := bstep (se 3 (by rfl) ⟨1525334, by rfl⟩ : syracuseStep 8135117 = 3050669) B3050669
theorem B2539985 : Blo 1691546 2539985 := bstep (se 2 (by rfl) ⟨952494, by rfl⟩ : syracuseStep 2539985 = 1904989) B1904989
theorem B2540003 : Blo 1691546 2540003 := bstep (se 1 (by rfl) ⟨1905002, by rfl⟩ : syracuseStep 2540003 = 3810005) B3810005
theorem B2540033 : Blo 1691546 2540033 := bstep (se 2 (by rfl) ⟨952512, by rfl⟩ : syracuseStep 2540033 = 1905025) B1905025
theorem B2540051 : Blo 1691546 2540051 := bstep (se 1 (by rfl) ⟨1905038, by rfl⟩ : syracuseStep 2540051 = 3810077) B3810077
theorem B2540081 : Blo 1691546 2540081 := bstep (se 2 (by rfl) ⟨952530, by rfl⟩ : syracuseStep 2540081 = 1905061) B1905061
theorem B2540099 : Blo 1691546 2540099 := bstep (se 1 (by rfl) ⟨1905074, by rfl⟩ : syracuseStep 2540099 = 3810149) B3810149
theorem B9634373 : Blo 1691546 9634373 := bstep (se 4 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 9634373 = 1806445) B1806445
theorem B2540129 : Blo 1691546 2540129 := bstep (se 2 (by rfl) ⟨952548, by rfl⟩ : syracuseStep 2540129 = 1905097) B1905097
theorem B5710445 : Blo 1691546 5710445 := bstep (se 3 (by rfl) ⟨1070708, by rfl⟩ : syracuseStep 5710445 = 2141417) B2141417
theorem B7225969 : Blo 1691546 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B2540147 : Blo 1691546 2540147 := bstep (se 1 (by rfl) ⟨1905110, by rfl⟩ : syracuseStep 2540147 = 3810221) B3810221
theorem B2540177 : Blo 1691546 2540177 := bstep (se 2 (by rfl) ⟨952566, by rfl⟩ : syracuseStep 2540177 = 1905133) B1905133
theorem B5710499 : Blo 1691546 5710499 := bstep (se 1 (by rfl) ⟨4282874, by rfl⟩ : syracuseStep 5710499 = 8565749) B8565749
theorem B2540195 : Blo 1691546 2540195 := bstep (se 1 (by rfl) ⟨1905146, by rfl⟩ : syracuseStep 2540195 = 3810293) B3810293
theorem B3809969 : Blo 1691546 3809969 := bstep (se 2 (by rfl) ⟨1428738, by rfl⟩ : syracuseStep 3809969 = 2857477) B2857477
theorem B2540225 : Blo 1691546 2540225 := bstep (se 2 (by rfl) ⟨952584, by rfl⟩ : syracuseStep 2540225 = 1905169) B1905169
theorem B3809987 : Blo 1691546 3809987 := bstep (se 1 (by rfl) ⟨2857490, by rfl⟩ : syracuseStep 3809987 = 5714981) B5714981
theorem B2540243 : Blo 1691546 2540243 := bstep (se 1 (by rfl) ⟨1905182, by rfl⟩ : syracuseStep 2540243 = 3810365) B3810365
theorem B2540273 : Blo 1691546 2540273 := bstep (se 2 (by rfl) ⟨952602, by rfl⟩ : syracuseStep 2540273 = 1905205) B1905205
theorem B2409203 : Blo 1691546 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B2540291 : Blo 1691546 2540291 := bstep (se 1 (by rfl) ⟨1905218, by rfl⟩ : syracuseStep 2540291 = 3810437) B3810437
theorem B4817677 : Blo 1691546 4817677 := bstep (se 3 (by rfl) ⟨903314, by rfl⟩ : syracuseStep 4817677 = 1806629) B1806629
theorem B48816917 : Blo 1691546 48816917 := bstep (se 6 (by rfl) ⟨1144146, by rfl⟩ : syracuseStep 48816917 = 2288293) B2288293
theorem B8242019 : Blo 1691546 8242019 := bstep (se 1 (by rfl) ⟨6181514, by rfl⟩ : syracuseStep 8242019 = 12363029) B12363029
theorem B5710769 : Blo 1691546 5710769 := bstep (se 2 (by rfl) ⟨2141538, by rfl⟩ : syracuseStep 5710769 = 4283077) B4283077
theorem B12854213 : Blo 1691546 12854213 := bstep (se 4 (by rfl) ⟨1205082, by rfl⟩ : syracuseStep 12854213 = 2410165) B2410165
theorem B3810257 : Blo 1691546 3810257 := bstep (se 2 (by rfl) ⟨1428846, by rfl⟩ : syracuseStep 3810257 = 2857693) B2857693
theorem B3810275 : Blo 1691546 3810275 := bstep (se 1 (by rfl) ⟨2857706, by rfl⟩ : syracuseStep 3810275 = 5715413) B5715413
theorem B4285457 : Blo 1691546 4285457 := bstep (se 2 (by rfl) ⟨1607046, by rfl⟩ : syracuseStep 4285457 = 3214093) B3214093
theorem B2442259 : Blo 1691546 2442259 := bstep (se 1 (by rfl) ⟨1831694, by rfl⟩ : syracuseStep 2442259 = 3663389) B3663389
theorem B4285507 : Blo 1691546 4285507 := bstep (se 1 (by rfl) ⟨3214130, by rfl⟩ : syracuseStep 4285507 = 6428261) B6428261
theorem B5424205 : Blo 1691546 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B3212369 : Blo 1691546 3212369 := bstep (se 2 (by rfl) ⟨1204638, by rfl⟩ : syracuseStep 3212369 = 2409277) B2409277
theorem B14853233 : Blo 1691546 14853233 := bstep (se 2 (by rfl) ⟨5569962, by rfl⟩ : syracuseStep 14853233 = 11139925) B11139925
theorem B9643121 : Blo 1691546 9643121 := bstep (se 2 (by rfl) ⟨3616170, by rfl⟩ : syracuseStep 9643121 = 7232341) B7232341
theorem B4285649 : Blo 1691546 4285649 := bstep (se 2 (by rfl) ⟨1607118, by rfl⟩ : syracuseStep 4285649 = 3214237) B3214237
theorem B58623203 : Blo 1691546 58623203 := bstep (se 1 (by rfl) ⟨43967402, by rfl⟩ : syracuseStep 58623203 = 87934805) B87934805
theorem B9635057 : Blo 1691546 9635057 := bstep (se 2 (by rfl) ⟨3613146, by rfl⟩ : syracuseStep 9635057 = 7226293) B7226293
theorem B6423857 : Blo 1691546 6423857 := bstep (se 2 (by rfl) ⟨2408946, by rfl⟩ : syracuseStep 6423857 = 4817893) B4817893
theorem B10839365 : Blo 1691546 10839365 := bstep (se 4 (by rfl) ⟨1016190, by rfl⟩ : syracuseStep 10839365 = 2032381) B2032381
theorem B2409841 : Blo 1691546 2409841 := bstep (se 2 (by rfl) ⟨903690, by rfl⟩ : syracuseStep 2409841 = 1807381) B1807381
theorem B16270733 : Blo 1691546 16270733 := bstep (se 3 (by rfl) ⟨3050762, by rfl⟩ : syracuseStep 16270733 = 6101525) B6101525
theorem B5711309 : Blo 1691546 5711309 := bstep (se 3 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 5711309 = 2141741) B2141741
theorem B21685745 : Blo 1691546 21685745 := bstep (se 2 (by rfl) ⟨8132154, by rfl⟩ : syracuseStep 21685745 = 16264309) B16264309
theorem B5711363 : Blo 1691546 5711363 := bstep (se 1 (by rfl) ⟨4283522, by rfl⟩ : syracuseStep 5711363 = 8567045) B8567045
theorem B2287121 : Blo 1691546 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B3614257 : Blo 1691546 3614257 := bstep (se 2 (by rfl) ⟨1355346, by rfl⟩ : syracuseStep 3614257 = 2710693) B2710693
theorem B36595313 : Blo 1691546 36595313 := bstep (se 2 (by rfl) ⟨13723242, by rfl⟩ : syracuseStep 36595313 = 27446485) B27446485
theorem B2410177 : Blo 1691546 2410177 := bstep (se 2 (by rfl) ⟨903816, by rfl⟩ : syracuseStep 2410177 = 1807633) B1807633
theorem B8570609 : Blo 1691546 8570609 := bstep (se 2 (by rfl) ⟨3213978, by rfl⟩ : syracuseStep 8570609 = 6427957) B6427957
theorem B4065041 : Blo 1691546 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B5711633 : Blo 1691546 5711633 := bstep (se 2 (by rfl) ⟨2141862, by rfl⟩ : syracuseStep 5711633 = 4283725) B4283725
theorem B4065155 : Blo 1691546 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B3213265 : Blo 1691546 3213265 := bstep (se 2 (by rfl) ⟨1204974, by rfl⟩ : syracuseStep 3213265 = 2409949) B2409949
theorem B2033635 : Blo 1691546 2033635 := bstep (se 1 (by rfl) ⟨1525226, by rfl⟩ : syracuseStep 2033635 = 3050453) B3050453
theorem B4065329 : Blo 1691546 4065329 := bstep (se 2 (by rfl) ⟨1524498, by rfl⟩ : syracuseStep 4065329 = 3048997) B3048997
theorem B2033731 : Blo 1691546 2033731 := bstep (se 1 (by rfl) ⟨1525298, by rfl⟩ : syracuseStep 2033731 = 3050597) B3050597
theorem B3213425 : Blo 1691546 3213425 := bstep (se 2 (by rfl) ⟨1205034, by rfl⟩ : syracuseStep 3213425 = 2410069) B2410069
theorem B4286641 : Blo 1691546 4286641 := bstep (se 2 (by rfl) ⟨1607490, by rfl⟩ : syracuseStep 4286641 = 3214981) B3214981
theorem B2410769 : Blo 1691546 2410769 := bstep (se 2 (by rfl) ⟨904038, by rfl⟩ : syracuseStep 2410769 = 1808077) B1808077
theorem B6859043 : Blo 1691546 6859043 := bstep (se 1 (by rfl) ⟨5144282, by rfl⟩ : syracuseStep 6859043 = 10288565) B10288565
theorem B5712173 : Blo 1691546 5712173 := bstep (se 3 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 5712173 = 2142065) B2142065
theorem B35227957 : Blo 1691546 35227957 := bstep (se 5 (by rfl) ⟨1651310, by rfl⟩ : syracuseStep 35227957 = 3302621) B3302621
theorem B3615043 : Blo 1691546 3615043 := bstep (se 1 (by rfl) ⟨2711282, by rfl⟩ : syracuseStep 3615043 = 5422565) B5422565
theorem B5712227 : Blo 1691546 5712227 := bstep (se 1 (by rfl) ⟨4284170, by rfl⟩ : syracuseStep 5712227 = 8568341) B8568341
theorem B1903027 : Blo 1691546 1903027 := bstep (se 1 (by rfl) ⟨1427270, by rfl⟩ : syracuseStep 1903027 = 2854541) B2854541
theorem B2034115 : Blo 1691546 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B4819409 : Blo 1691546 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B3213827 : Blo 1691546 3213827 := bstep (se 1 (by rfl) ⟨2410370, by rfl⟩ : syracuseStep 3213827 = 4820741) B4820741
theorem B9644579 : Blo 1691546 9644579 := bstep (se 1 (by rfl) ⟨7233434, by rfl⟩ : syracuseStep 9644579 = 14466869) B14466869
theorem B4885037 : Blo 1691546 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B1903171 : Blo 1691546 1903171 := bstep (se 1 (by rfl) ⟨1427378, by rfl⟩ : syracuseStep 1903171 = 2854757) B2854757
theorem B5712497 : Blo 1691546 5712497 := bstep (se 2 (by rfl) ⟨2142186, by rfl⟩ : syracuseStep 5712497 = 4284373) B4284373
theorem B4819601 : Blo 1691546 4819601 := bstep (se 2 (by rfl) ⟨1807350, by rfl⟩ : syracuseStep 4819601 = 3614701) B3614701
theorem B9636515 : Blo 1691546 9636515 := bstep (se 1 (by rfl) ⟨7227386, by rfl⟩ : syracuseStep 9636515 = 14454773) B14454773
theorem B1903315 : Blo 1691546 1903315 := bstep (se 1 (by rfl) ⟨1427486, by rfl⟩ : syracuseStep 1903315 = 2854973) B2854973
theorem B2894563 : Blo 1691546 2894563 := bstep (se 1 (by rfl) ⟨2170922, by rfl⟩ : syracuseStep 2894563 = 4341845) B4341845
theorem B6425315 : Blo 1691546 6425315 := bstep (se 1 (by rfl) ⟨4818986, by rfl⟩ : syracuseStep 6425315 = 9637973) B9637973
theorem B19270385 : Blo 1691546 19270385 := bstep (se 2 (by rfl) ⟨7226394, by rfl⟩ : syracuseStep 19270385 = 14452789) B14452789
theorem B2140931 : Blo 1691546 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B2411299 : Blo 1691546 2411299 := bstep (se 1 (by rfl) ⟨1808474, by rfl⟩ : syracuseStep 2411299 = 3616949) B3616949
theorem B1903459 : Blo 1691546 1903459 := bstep (se 1 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 1903459 = 2855189) B2855189
theorem B7719779 : Blo 1691546 7719779 := bstep (se 1 (by rfl) ⟨5789834, by rfl⟩ : syracuseStep 7719779 = 11579669) B11579669
theorem B3050417 : Blo 1691546 3050417 := bstep (se 2 (by rfl) ⟨1143906, by rfl⟩ : syracuseStep 3050417 = 2287813) B2287813
theorem B1903603 : Blo 1691546 1903603 := bstep (se 1 (by rfl) ⟨1427702, by rfl⟩ : syracuseStep 1903603 = 2855405) B2855405
theorem B3615761 : Blo 1691546 3615761 := bstep (se 2 (by rfl) ⟨1355910, by rfl⟩ : syracuseStep 3615761 = 2711821) B2711821
theorem B11586673 : Blo 1691546 11586673 := bstep (se 2 (by rfl) ⟨4345002, by rfl⟩ : syracuseStep 11586673 = 8690005) B8690005
theorem B1903747 : Blo 1691546 1903747 := bstep (se 1 (by rfl) ⟨1427810, by rfl⟩ : syracuseStep 1903747 = 2855621) B2855621
theorem B5713037 : Blo 1691546 5713037 := bstep (se 3 (by rfl) ⟨1071194, by rfl⟩ : syracuseStep 5713037 = 2142389) B2142389
theorem B8572067 : Blo 1691546 8572067 := bstep (se 1 (by rfl) ⟨6429050, by rfl⟩ : syracuseStep 8572067 = 12858101) B12858101
theorem B5713091 : Blo 1691546 5713091 := bstep (se 1 (by rfl) ⟨4284818, by rfl⟩ : syracuseStep 5713091 = 8569637) B8569637
theorem B1903891 : Blo 1691546 1903891 := bstep (se 1 (by rfl) ⟨1427918, by rfl⟩ : syracuseStep 1903891 = 2855837) B2855837
theorem B3214723 : Blo 1691546 3214723 := bstep (se 1 (by rfl) ⟨2411042, by rfl⟩ : syracuseStep 3214723 = 4822085) B4822085
theorem B1904035 : Blo 1691546 1904035 := bstep (se 1 (by rfl) ⟨1428026, by rfl⟩ : syracuseStep 1904035 = 2856053) B2856053
theorem B6860209 : Blo 1691546 6860209 := bstep (se 2 (by rfl) ⟨2572578, by rfl⟩ : syracuseStep 6860209 = 5145157) B5145157
theorem B2141635 : Blo 1691546 2141635 := bstep (se 1 (by rfl) ⟨1606226, by rfl⟩ : syracuseStep 2141635 = 3212453) B3212453
theorem B21687749 : Blo 1691546 21687749 := bstep (se 4 (by rfl) ⟨2033226, by rfl⟩ : syracuseStep 21687749 = 4066453) B4066453
theorem B5713361 : Blo 1691546 5713361 := bstep (se 2 (by rfl) ⟨2142510, by rfl⟩ : syracuseStep 5713361 = 4285021) B4285021
theorem B3616273 : Blo 1691546 3616273 := bstep (se 2 (by rfl) ⟨1356102, by rfl⟩ : syracuseStep 3616273 = 2712205) B2712205
theorem B2141731 : Blo 1691546 2141731 := bstep (se 1 (by rfl) ⟨1606298, by rfl⟩ : syracuseStep 2141731 = 3212597) B3212597
theorem B3214883 : Blo 1691546 3214883 := bstep (se 1 (by rfl) ⟨2411162, by rfl⟩ : syracuseStep 3214883 = 4822325) B4822325
theorem B1904179 : Blo 1691546 1904179 := bstep (se 1 (by rfl) ⟨1428134, by rfl⟩ : syracuseStep 1904179 = 2856269) B2856269
theorem B7229027 : Blo 1691546 7229027 := bstep (se 1 (by rfl) ⟨5421770, by rfl⟩ : syracuseStep 7229027 = 10843541) B10843541
theorem B4820593 : Blo 1691546 4820593 := bstep (se 2 (by rfl) ⟨1807722, by rfl⟩ : syracuseStep 4820593 = 3615445) B3615445
theorem B2854561 : Blo 1691546 2854561 := bstep (se 2 (by rfl) ⟨1070460, by rfl⟩ : syracuseStep 2854561 = 2140921) B2140921
theorem B2854595 : Blo 1691546 2854595 := bstep (se 1 (by rfl) ⟨2140946, by rfl⟩ : syracuseStep 2854595 = 4281893) B4281893
theorem B1904323 : Blo 1691546 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B10292941 : Blo 1691546 10292941 := bstep (se 3 (by rfl) ⟨1929926, by rfl⟩ : syracuseStep 10292941 = 3859853) B3859853
theorem B6426317 : Blo 1691546 6426317 := bstep (se 3 (by rfl) ⟨1204934, by rfl⟩ : syracuseStep 6426317 = 2409869) B2409869
theorem B12848867 : Blo 1691546 12848867 := bstep (se 1 (by rfl) ⟨9636650, by rfl⟩ : syracuseStep 12848867 = 19273301) B19273301
theorem B16707313 : Blo 1691546 16707313 := bstep (se 2 (by rfl) ⟨6265242, by rfl⟩ : syracuseStep 16707313 = 12530485) B12530485
theorem B9146125 : Blo 1691546 9146125 := bstep (se 3 (by rfl) ⟨1714898, by rfl⟩ : syracuseStep 9146125 = 3429797) B3429797
theorem B2854723 : Blo 1691546 2854723 := bstep (se 1 (by rfl) ⟨2141042, by rfl⟩ : syracuseStep 2854723 = 4282085) B4282085
theorem B1904467 : Blo 1691546 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B4820867 : Blo 1691546 4820867 := bstep (se 1 (by rfl) ⟨3615650, by rfl⟩ : syracuseStep 4820867 = 7231301) B7231301
theorem B1691555 : Blo 1691546 1691555 := bstep (se 1 (by rfl) ⟨1268666, by rfl⟩ : syracuseStep 1691555 = 2537333) B2537333
theorem B1716131 : Blo 1691546 1716131 := bstep (se 1 (by rfl) ⟨1287098, by rfl⟩ : syracuseStep 1716131 = 2574197) B2574197
theorem B2895793 : Blo 1691546 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B1691571 : Blo 1691546 1691571 := bstep (se 1 (by rfl) ⟨1268678, by rfl⟩ : syracuseStep 1691571 = 2537357) B2537357
theorem B1691587 : Blo 1691546 1691587 := bstep (se 1 (by rfl) ⟨1268690, by rfl⟩ : syracuseStep 1691587 = 2537381) B2537381
theorem B8572877 : Blo 1691546 8572877 := bstep (se 3 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 8572877 = 3214829) B3214829
theorem B2854865 : Blo 1691546 2854865 := bstep (se 2 (by rfl) ⟨1070574, by rfl⟩ : syracuseStep 2854865 = 2141149) B2141149
theorem B1691603 : Blo 1691546 1691603 := bstep (se 1 (by rfl) ⟨1268702, by rfl⟩ : syracuseStep 1691603 = 2537405) B2537405
theorem B1691619 : Blo 1691546 1691619 := bstep (se 1 (by rfl) ⟨1268714, by rfl⟩ : syracuseStep 1691619 = 2537429) B2537429
theorem B1904611 : Blo 1691546 1904611 := bstep (se 1 (by rfl) ⟨1428458, by rfl⟩ : syracuseStep 1904611 = 2856917) B2856917
theorem B5713901 : Blo 1691546 5713901 := bstep (se 3 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 5713901 = 2142713) B2142713
theorem B1691635 : Blo 1691546 1691635 := bstep (se 1 (by rfl) ⟨1268726, by rfl⟩ : syracuseStep 1691635 = 2537453) B2537453
theorem B1691651 : Blo 1691546 1691651 := bstep (se 1 (by rfl) ⟨1268738, by rfl⟩ : syracuseStep 1691651 = 2537477) B2537477
theorem B1691667 : Blo 1691546 1691667 := bstep (se 1 (by rfl) ⟨1268750, by rfl⟩ : syracuseStep 1691667 = 2537501) B2537501
theorem B2142227 : Blo 1691546 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B1691683 : Blo 1691546 1691683 := bstep (se 1 (by rfl) ⟨1268762, by rfl⟩ : syracuseStep 1691683 = 2537525) B2537525
theorem B5713955 : Blo 1691546 5713955 := bstep (se 1 (by rfl) ⟨4285466, by rfl⟩ : syracuseStep 5713955 = 8570933) B8570933
theorem B1691699 : Blo 1691546 1691699 := bstep (se 1 (by rfl) ⟨1268774, by rfl⟩ : syracuseStep 1691699 = 2537549) B2537549
theorem B1691715 : Blo 1691546 1691715 := bstep (se 1 (by rfl) ⟨1268786, by rfl⟩ : syracuseStep 1691715 = 2537573) B2537573
theorem B4821059 : Blo 1691546 4821059 := bstep (se 1 (by rfl) ⟨3615794, by rfl⟩ : syracuseStep 4821059 = 7231589) B7231589
theorem B2854993 : Blo 1691546 2854993 := bstep (se 2 (by rfl) ⟨1070622, by rfl⟩ : syracuseStep 2854993 = 2141245) B2141245
theorem B1691731 : Blo 1691546 1691731 := bstep (se 1 (by rfl) ⟨1268798, by rfl⟩ : syracuseStep 1691731 = 2537597) B2537597
theorem B1691747 : Blo 1691546 1691747 := bstep (se 1 (by rfl) ⟨1268810, by rfl⟩ : syracuseStep 1691747 = 2537621) B2537621
theorem B1691763 : Blo 1691546 1691763 := bstep (se 1 (by rfl) ⟨1268822, by rfl⟩ : syracuseStep 1691763 = 2537645) B2537645
theorem B2855027 : Blo 1691546 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B1904755 : Blo 1691546 1904755 := bstep (se 1 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 1904755 = 2857133) B2857133
theorem B1691779 : Blo 1691546 1691779 := bstep (se 1 (by rfl) ⟨1268834, by rfl⟩ : syracuseStep 1691779 = 2537669) B2537669
theorem B1691795 : Blo 1691546 1691795 := bstep (se 1 (by rfl) ⟨1268846, by rfl⟩ : syracuseStep 1691795 = 2537693) B2537693
theorem B1691811 : Blo 1691546 1691811 := bstep (se 1 (by rfl) ⟨1268858, by rfl⟩ : syracuseStep 1691811 = 2537717) B2537717
theorem B5419181 : Blo 1691546 5419181 := bstep (se 3 (by rfl) ⟨1016096, by rfl⟩ : syracuseStep 5419181 = 2032193) B2032193
theorem B1691827 : Blo 1691546 1691827 := bstep (se 1 (by rfl) ⟨1268870, by rfl⟩ : syracuseStep 1691827 = 2537741) B2537741
theorem B1691843 : Blo 1691546 1691843 := bstep (se 1 (by rfl) ⟨1268882, by rfl⟩ : syracuseStep 1691843 = 2537765) B2537765
theorem B1691859 : Blo 1691546 1691859 := bstep (se 1 (by rfl) ⟨1268894, by rfl⟩ : syracuseStep 1691859 = 2537789) B2537789
theorem B1691875 : Blo 1691546 1691875 := bstep (se 1 (by rfl) ⟨1268906, by rfl⟩ : syracuseStep 1691875 = 2537813) B2537813
theorem B30888163 : Blo 1691546 30888163 := bstep (se 1 (by rfl) ⟨23166122, by rfl⟩ : syracuseStep 30888163 = 46332245) B46332245
theorem B1691891 : Blo 1691546 1691891 := bstep (se 1 (by rfl) ⟨1268918, by rfl⟩ : syracuseStep 1691891 = 2537837) B2537837
theorem B2855155 : Blo 1691546 2855155 := bstep (se 1 (by rfl) ⟨2141366, by rfl⟩ : syracuseStep 2855155 = 4282733) B4282733
theorem B1691907 : Blo 1691546 1691907 := bstep (se 1 (by rfl) ⟨1268930, by rfl⟩ : syracuseStep 1691907 = 2537861) B2537861
theorem B1904899 : Blo 1691546 1904899 := bstep (se 1 (by rfl) ⟨1428674, by rfl⟩ : syracuseStep 1904899 = 2857349) B2857349
theorem B1691923 : Blo 1691546 1691923 := bstep (se 1 (by rfl) ⟨1268942, by rfl⟩ : syracuseStep 1691923 = 2537885) B2537885
theorem B1691939 : Blo 1691546 1691939 := bstep (se 1 (by rfl) ⟨1268954, by rfl⟩ : syracuseStep 1691939 = 2537909) B2537909
theorem B5714225 : Blo 1691546 5714225 := bstep (se 2 (by rfl) ⟨2142834, by rfl⟩ : syracuseStep 5714225 = 4285669) B4285669
theorem B1691955 : Blo 1691546 1691955 := bstep (se 1 (by rfl) ⟨1268966, by rfl⟩ : syracuseStep 1691955 = 2537933) B2537933
theorem B1691971 : Blo 1691546 1691971 := bstep (se 1 (by rfl) ⟨1268978, by rfl⟩ : syracuseStep 1691971 = 2537957) B2537957
theorem B1691987 : Blo 1691546 1691987 := bstep (se 1 (by rfl) ⟨1268990, by rfl⟩ : syracuseStep 1691987 = 2537981) B2537981
theorem B1692003 : Blo 1691546 1692003 := bstep (se 1 (by rfl) ⟨1269002, by rfl⟩ : syracuseStep 1692003 = 2538005) B2538005
theorem B1692019 : Blo 1691546 1692019 := bstep (se 1 (by rfl) ⟨1269014, by rfl⟩ : syracuseStep 1692019 = 2538029) B2538029
theorem B2855297 : Blo 1691546 2855297 := bstep (se 2 (by rfl) ⟨1070736, by rfl⟩ : syracuseStep 2855297 = 2141473) B2141473
theorem B1692035 : Blo 1691546 1692035 := bstep (se 1 (by rfl) ⟨1269026, by rfl⟩ : syracuseStep 1692035 = 2538053) B2538053
theorem B1692051 : Blo 1691546 1692051 := bstep (se 1 (by rfl) ⟨1269038, by rfl⟩ : syracuseStep 1692051 = 2538077) B2538077
theorem B1905043 : Blo 1691546 1905043 := bstep (se 1 (by rfl) ⟨1428782, by rfl⟩ : syracuseStep 1905043 = 2857565) B2857565
theorem B1692067 : Blo 1691546 1692067 := bstep (se 1 (by rfl) ⟨1269050, by rfl⟩ : syracuseStep 1692067 = 2538101) B2538101
theorem B1692083 : Blo 1691546 1692083 := bstep (se 1 (by rfl) ⟨1269062, by rfl⟩ : syracuseStep 1692083 = 2538125) B2538125
theorem B1806787 : Blo 1691546 1806787 := bstep (se 1 (by rfl) ⟨1355090, by rfl⟩ : syracuseStep 1806787 = 2710181) B2710181
theorem B1692099 : Blo 1691546 1692099 := bstep (se 1 (by rfl) ⟨1269074, by rfl⟩ : syracuseStep 1692099 = 2538149) B2538149
theorem B1692115 : Blo 1691546 1692115 := bstep (se 1 (by rfl) ⟨1269086, by rfl⟩ : syracuseStep 1692115 = 2538173) B2538173
theorem B1692131 : Blo 1691546 1692131 := bstep (se 1 (by rfl) ⟨1269098, by rfl⟩ : syracuseStep 1692131 = 2538197) B2538197
theorem B1692147 : Blo 1691546 1692147 := bstep (se 1 (by rfl) ⟨1269110, by rfl⟩ : syracuseStep 1692147 = 2538221) B2538221
theorem B2855425 : Blo 1691546 2855425 := bstep (se 2 (by rfl) ⟨1070784, by rfl⟩ : syracuseStep 2855425 = 2141569) B2141569
theorem B1692163 : Blo 1691546 1692163 := bstep (se 1 (by rfl) ⟨1269122, by rfl⟩ : syracuseStep 1692163 = 2538245) B2538245
theorem B3092995 : Blo 1691546 3092995 := bstep (se 1 (by rfl) ⟨2319746, by rfl⟩ : syracuseStep 3092995 = 4639493) B4639493
theorem B1692179 : Blo 1691546 1692179 := bstep (se 1 (by rfl) ⟨1269134, by rfl⟩ : syracuseStep 1692179 = 2538269) B2538269
theorem B2855459 : Blo 1691546 2855459 := bstep (se 1 (by rfl) ⟨2141594, by rfl⟩ : syracuseStep 2855459 = 4283189) B4283189
theorem B1692195 : Blo 1691546 1692195 := bstep (se 1 (by rfl) ⟨1269146, by rfl⟩ : syracuseStep 1692195 = 2538293) B2538293
theorem B1905187 : Blo 1691546 1905187 := bstep (se 1 (by rfl) ⟨1428890, by rfl⟩ : syracuseStep 1905187 = 2857781) B2857781
theorem B1692211 : Blo 1691546 1692211 := bstep (se 1 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 1692211 = 2538317) B2538317
theorem B1692227 : Blo 1691546 1692227 := bstep (se 1 (by rfl) ⟨1269170, by rfl⟩ : syracuseStep 1692227 = 2538341) B2538341
theorem B5493325 : Blo 1691546 5493325 := bstep (se 3 (by rfl) ⟨1029998, by rfl⟩ : syracuseStep 5493325 = 2059997) B2059997
theorem B1692243 : Blo 1691546 1692243 := bstep (se 1 (by rfl) ⟨1269182, by rfl⟩ : syracuseStep 1692243 = 2538365) B2538365
theorem B5419619 : Blo 1691546 5419619 := bstep (se 1 (by rfl) ⟨4064714, by rfl⟩ : syracuseStep 5419619 = 8129429) B8129429
theorem B1692259 : Blo 1691546 1692259 := bstep (se 1 (by rfl) ⟨1269194, by rfl⟩ : syracuseStep 1692259 = 2538389) B2538389
theorem B49459825 : Blo 1691546 49459825 := bstep (se 2 (by rfl) ⟨18547434, by rfl⟩ : syracuseStep 49459825 = 37094869) B37094869
theorem B1692275 : Blo 1691546 1692275 := bstep (se 1 (by rfl) ⟨1269206, by rfl⟩ : syracuseStep 1692275 = 2538413) B2538413
theorem B1692291 : Blo 1691546 1692291 := bstep (se 1 (by rfl) ⟨1269218, by rfl⟩ : syracuseStep 1692291 = 2538437) B2538437
theorem B1692307 : Blo 1691546 1692307 := bstep (se 1 (by rfl) ⟨1269230, by rfl⟩ : syracuseStep 1692307 = 2538461) B2538461
theorem B2855587 : Blo 1691546 2855587 := bstep (se 1 (by rfl) ⟨2141690, by rfl⟩ : syracuseStep 2855587 = 4283381) B4283381
theorem B1692323 : Blo 1691546 1692323 := bstep (se 1 (by rfl) ⟨1269242, by rfl⟩ : syracuseStep 1692323 = 2538485) B2538485
theorem B8565425 : Blo 1691546 8565425 := bstep (se 2 (by rfl) ⟨3212034, by rfl⟩ : syracuseStep 8565425 = 6424069) B6424069
theorem B1692339 : Blo 1691546 1692339 := bstep (se 1 (by rfl) ⟨1269254, by rfl⟩ : syracuseStep 1692339 = 2538509) B2538509
theorem B1807043 : Blo 1691546 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B1692355 : Blo 1691546 1692355 := bstep (se 1 (by rfl) ⟨1269266, by rfl⟩ : syracuseStep 1692355 = 2538533) B2538533
theorem B12366533 : Blo 1691546 12366533 := bstep (se 4 (by rfl) ⟨1159362, by rfl⟩ : syracuseStep 12366533 = 2318725) B2318725
theorem B13030085 : Blo 1691546 13030085 := bstep (se 4 (by rfl) ⟨1221570, by rfl⟩ : syracuseStep 13030085 = 2443141) B2443141
theorem B1692371 : Blo 1691546 1692371 := bstep (se 1 (by rfl) ⟨1269278, by rfl⟩ : syracuseStep 1692371 = 2538557) B2538557
theorem B2142931 : Blo 1691546 2142931 := bstep (se 1 (by rfl) ⟨1607198, by rfl⟩ : syracuseStep 2142931 = 3214397) B3214397
theorem B14455523 : Blo 1691546 14455523 := bstep (se 1 (by rfl) ⟨10841642, by rfl⟩ : syracuseStep 14455523 = 21683285) B21683285
theorem B1692387 : Blo 1691546 1692387 := bstep (se 1 (by rfl) ⟨1269290, by rfl⟩ : syracuseStep 1692387 = 2538581) B2538581
theorem B1692403 : Blo 1691546 1692403 := bstep (se 1 (by rfl) ⟨1269302, by rfl⟩ : syracuseStep 1692403 = 2538605) B2538605
theorem B1692419 : Blo 1691546 1692419 := bstep (se 1 (by rfl) ⟨1269314, by rfl⟩ : syracuseStep 1692419 = 2538629) B2538629
theorem B1692435 : Blo 1691546 1692435 := bstep (se 1 (by rfl) ⟨1269326, by rfl⟩ : syracuseStep 1692435 = 2538653) B2538653
theorem B1692451 : Blo 1691546 1692451 := bstep (se 1 (by rfl) ⟨1269338, by rfl⟩ : syracuseStep 1692451 = 2538677) B2538677
theorem B2855729 : Blo 1691546 2855729 := bstep (se 2 (by rfl) ⟨1070898, by rfl⟩ : syracuseStep 2855729 = 2141797) B2141797
theorem B5149489 : Blo 1691546 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B1692467 : Blo 1691546 1692467 := bstep (se 1 (by rfl) ⟨1269350, by rfl⟩ : syracuseStep 1692467 = 2538701) B2538701
theorem B2749235 : Blo 1691546 2749235 := bstep (se 1 (by rfl) ⟨2061926, by rfl⟩ : syracuseStep 2749235 = 4123853) B4123853
theorem B2143027 : Blo 1691546 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B1692483 : Blo 1691546 1692483 := bstep (se 1 (by rfl) ⟨1269362, by rfl⟩ : syracuseStep 1692483 = 2538725) B2538725
theorem B5714765 : Blo 1691546 5714765 := bstep (se 3 (by rfl) ⟨1071518, by rfl⟩ : syracuseStep 5714765 = 2143037) B2143037
theorem B1692499 : Blo 1691546 1692499 := bstep (se 1 (by rfl) ⟨1269374, by rfl⟩ : syracuseStep 1692499 = 2538749) B2538749
theorem B8131427 : Blo 1691546 8131427 := bstep (se 1 (by rfl) ⟨6098570, by rfl⟩ : syracuseStep 8131427 = 12197141) B12197141
theorem B1692515 : Blo 1691546 1692515 := bstep (se 1 (by rfl) ⟨1269386, by rfl⟩ : syracuseStep 1692515 = 2538773) B2538773
theorem B6959971 : Blo 1691546 6959971 := bstep (se 1 (by rfl) ⟨5219978, by rfl⟩ : syracuseStep 6959971 = 10439957) B10439957
theorem B4821869 : Blo 1691546 4821869 := bstep (se 3 (by rfl) ⟨904100, by rfl⟩ : syracuseStep 4821869 = 1808201) B1808201
theorem B1692531 : Blo 1691546 1692531 := bstep (se 1 (by rfl) ⟨1269398, by rfl⟩ : syracuseStep 1692531 = 2538797) B2538797
theorem B1692547 : Blo 1691546 1692547 := bstep (se 1 (by rfl) ⟨1269410, by rfl⟩ : syracuseStep 1692547 = 2538821) B2538821
theorem B5714819 : Blo 1691546 5714819 := bstep (se 1 (by rfl) ⟨4286114, by rfl⟩ : syracuseStep 5714819 = 8572229) B8572229
theorem B1692563 : Blo 1691546 1692563 := bstep (se 1 (by rfl) ⟨1269422, by rfl⟩ : syracuseStep 1692563 = 2538845) B2538845
theorem B1692579 : Blo 1691546 1692579 := bstep (se 1 (by rfl) ⟨1269434, by rfl⟩ : syracuseStep 1692579 = 2538869) B2538869
theorem B2855857 : Blo 1691546 2855857 := bstep (se 2 (by rfl) ⟨1070946, by rfl⟩ : syracuseStep 2855857 = 2141893) B2141893
theorem B1692595 : Blo 1691546 1692595 := bstep (se 1 (by rfl) ⟨1269446, by rfl⟩ : syracuseStep 1692595 = 2538893) B2538893
theorem B1692611 : Blo 1691546 1692611 := bstep (se 1 (by rfl) ⟨1269458, by rfl⟩ : syracuseStep 1692611 = 2538917) B2538917
theorem B2855891 : Blo 1691546 2855891 := bstep (se 1 (by rfl) ⟨2141918, by rfl⟩ : syracuseStep 2855891 = 4283837) B4283837
theorem B1692627 : Blo 1691546 1692627 := bstep (se 1 (by rfl) ⟨1269470, by rfl⟩ : syracuseStep 1692627 = 2538941) B2538941
theorem B1692643 : Blo 1691546 1692643 := bstep (se 1 (by rfl) ⟨1269482, by rfl⟩ : syracuseStep 1692643 = 2538965) B2538965
theorem B6099953 : Blo 1691546 6099953 := bstep (se 2 (by rfl) ⟨2287482, by rfl⟩ : syracuseStep 6099953 = 4574965) B4574965
theorem B1692659 : Blo 1691546 1692659 := bstep (se 1 (by rfl) ⟨1269494, by rfl⟩ : syracuseStep 1692659 = 2538989) B2538989
theorem B1692675 : Blo 1691546 1692675 := bstep (se 1 (by rfl) ⟨1269506, by rfl⟩ : syracuseStep 1692675 = 2539013) B2539013
theorem B3806225 : Blo 1691546 3806225 := bstep (se 2 (by rfl) ⟨1427334, by rfl⟩ : syracuseStep 3806225 = 2854669) B2854669
theorem B1692691 : Blo 1691546 1692691 := bstep (se 1 (by rfl) ⟨1269518, by rfl⟩ : syracuseStep 1692691 = 2539037) B2539037
theorem B3806243 : Blo 1691546 3806243 := bstep (se 1 (by rfl) ⟨2854682, by rfl⟩ : syracuseStep 3806243 = 5709365) B5709365
theorem B1692707 : Blo 1691546 1692707 := bstep (se 1 (by rfl) ⟨1269530, by rfl⟩ : syracuseStep 1692707 = 2539061) B2539061
theorem B4822051 : Blo 1691546 4822051 := bstep (se 1 (by rfl) ⟨3616538, by rfl⟩ : syracuseStep 4822051 = 7233077) B7233077
theorem B1692723 : Blo 1691546 1692723 := bstep (se 1 (by rfl) ⟨1269542, by rfl⟩ : syracuseStep 1692723 = 2539085) B2539085
theorem B1692739 : Blo 1691546 1692739 := bstep (se 1 (by rfl) ⟨1269554, by rfl⟩ : syracuseStep 1692739 = 2539109) B2539109
theorem B2856019 : Blo 1691546 2856019 := bstep (se 1 (by rfl) ⟨2142014, by rfl⟩ : syracuseStep 2856019 = 4284029) B4284029
theorem B1692755 : Blo 1691546 1692755 := bstep (se 1 (by rfl) ⟨1269566, by rfl⟩ : syracuseStep 1692755 = 2539133) B2539133
theorem B1692771 : Blo 1691546 1692771 := bstep (se 1 (by rfl) ⟨1269578, by rfl⟩ : syracuseStep 1692771 = 2539157) B2539157
theorem B1692787 : Blo 1691546 1692787 := bstep (se 1 (by rfl) ⟨1269590, by rfl⟩ : syracuseStep 1692787 = 2539181) B2539181
theorem B1692803 : Blo 1691546 1692803 := bstep (se 1 (by rfl) ⟨1269602, by rfl⟩ : syracuseStep 1692803 = 2539205) B2539205
theorem B5715089 : Blo 1691546 5715089 := bstep (se 2 (by rfl) ⟨2143158, by rfl⟩ : syracuseStep 5715089 = 4286317) B4286317
theorem B1692819 : Blo 1691546 1692819 := bstep (se 1 (by rfl) ⟨1269614, by rfl⟩ : syracuseStep 1692819 = 2539229) B2539229
theorem B1692835 : Blo 1691546 1692835 := bstep (se 1 (by rfl) ⟨1269626, by rfl⟩ : syracuseStep 1692835 = 2539253) B2539253
theorem B1692851 : Blo 1691546 1692851 := bstep (se 1 (by rfl) ⟨1269638, by rfl⟩ : syracuseStep 1692851 = 2539277) B2539277
theorem B1692867 : Blo 1691546 1692867 := bstep (se 1 (by rfl) ⟨1269650, by rfl⟩ : syracuseStep 1692867 = 2539301) B2539301
theorem B1692883 : Blo 1691546 1692883 := bstep (se 1 (by rfl) ⟨1269662, by rfl⟩ : syracuseStep 1692883 = 2539325) B2539325
theorem B2856161 : Blo 1691546 2856161 := bstep (se 2 (by rfl) ⟨1071060, by rfl⟩ : syracuseStep 2856161 = 2142121) B2142121
theorem B1692899 : Blo 1691546 1692899 := bstep (se 1 (by rfl) ⟨1269674, by rfl⟩ : syracuseStep 1692899 = 2539349) B2539349
theorem B1692915 : Blo 1691546 1692915 := bstep (se 1 (by rfl) ⟨1269686, by rfl⟩ : syracuseStep 1692915 = 2539373) B2539373
theorem B1692931 : Blo 1691546 1692931 := bstep (se 1 (by rfl) ⟨1269698, by rfl⟩ : syracuseStep 1692931 = 2539397) B2539397
theorem B1692947 : Blo 1691546 1692947 := bstep (se 1 (by rfl) ⟨1269710, by rfl⟩ : syracuseStep 1692947 = 2539421) B2539421
theorem B8803619 : Blo 1691546 8803619 := bstep (se 1 (by rfl) ⟨6602714, by rfl⟩ : syracuseStep 8803619 = 13205429) B13205429
theorem B1692963 : Blo 1691546 1692963 := bstep (se 1 (by rfl) ⟨1269722, by rfl⟩ : syracuseStep 1692963 = 2539445) B2539445
theorem B3806513 : Blo 1691546 3806513 := bstep (se 2 (by rfl) ⟨1427442, by rfl⟩ : syracuseStep 3806513 = 2854885) B2854885
theorem B1692979 : Blo 1691546 1692979 := bstep (se 1 (by rfl) ⟨1269734, by rfl⟩ : syracuseStep 1692979 = 2539469) B2539469
theorem B3806531 : Blo 1691546 3806531 := bstep (se 1 (by rfl) ⟨2854898, by rfl⟩ : syracuseStep 3806531 = 5709797) B5709797
theorem B1692995 : Blo 1691546 1692995 := bstep (se 1 (by rfl) ⟨1269746, by rfl⟩ : syracuseStep 1692995 = 2539493) B2539493
theorem B9270605 : Blo 1691546 9270605 := bstep (se 3 (by rfl) ⟨1738238, by rfl⟩ : syracuseStep 9270605 = 3476477) B3476477
theorem B1693011 : Blo 1691546 1693011 := bstep (se 1 (by rfl) ⟨1269758, by rfl⟩ : syracuseStep 1693011 = 2539517) B2539517
theorem B2856289 : Blo 1691546 2856289 := bstep (se 2 (by rfl) ⟨1071108, by rfl⟩ : syracuseStep 2856289 = 2142217) B2142217
theorem B1693027 : Blo 1691546 1693027 := bstep (se 1 (by rfl) ⟨1269770, by rfl⟩ : syracuseStep 1693027 = 2539541) B2539541
theorem B21976433 : Blo 1691546 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B1693043 : Blo 1691546 1693043 := bstep (se 1 (by rfl) ⟨1269782, by rfl⟩ : syracuseStep 1693043 = 2539565) B2539565
theorem B4281731 : Blo 1691546 4281731 := bstep (se 1 (by rfl) ⟨3211298, by rfl⟩ : syracuseStep 4281731 = 6422597) B6422597
theorem B2856323 : Blo 1691546 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B1693059 : Blo 1691546 1693059 := bstep (se 1 (by rfl) ⟨1269794, by rfl⟩ : syracuseStep 1693059 = 2539589) B2539589
theorem B1693075 : Blo 1691546 1693075 := bstep (se 1 (by rfl) ⟨1269806, by rfl⟩ : syracuseStep 1693075 = 2539613) B2539613
theorem B9147811 : Blo 1691546 9147811 := bstep (se 1 (by rfl) ⟨6860858, by rfl⟩ : syracuseStep 9147811 = 13721717) B13721717
theorem B1693091 : Blo 1691546 1693091 := bstep (se 1 (by rfl) ⟨1269818, by rfl⟩ : syracuseStep 1693091 = 2539637) B2539637
theorem B1807795 : Blo 1691546 1807795 := bstep (se 1 (by rfl) ⟨1355846, by rfl⟩ : syracuseStep 1807795 = 2711693) B2711693
theorem B1693107 : Blo 1691546 1693107 := bstep (se 1 (by rfl) ⟨1269830, by rfl⟩ : syracuseStep 1693107 = 2539661) B2539661
theorem B1693123 : Blo 1691546 1693123 := bstep (se 1 (by rfl) ⟨1269842, by rfl⟩ : syracuseStep 1693123 = 2539685) B2539685
theorem B1693139 : Blo 1691546 1693139 := bstep (se 1 (by rfl) ⟨1269854, by rfl⟩ : syracuseStep 1693139 = 2539709) B2539709
theorem B1693155 : Blo 1691546 1693155 := bstep (se 1 (by rfl) ⟨1269866, by rfl⟩ : syracuseStep 1693155 = 2539733) B2539733
theorem B1693171 : Blo 1691546 1693171 := bstep (se 1 (by rfl) ⟨1269878, by rfl⟩ : syracuseStep 1693171 = 2539757) B2539757
theorem B2856451 : Blo 1691546 2856451 := bstep (se 1 (by rfl) ⟨2142338, by rfl⟩ : syracuseStep 2856451 = 4284677) B4284677
theorem B1693187 : Blo 1691546 1693187 := bstep (se 1 (by rfl) ⟨1269890, by rfl⟩ : syracuseStep 1693187 = 2539781) B2539781
theorem B4822541 : Blo 1691546 4822541 := bstep (se 3 (by rfl) ⟨904226, by rfl⟩ : syracuseStep 4822541 = 1808453) B1808453
theorem B1693203 : Blo 1691546 1693203 := bstep (se 1 (by rfl) ⟨1269902, by rfl⟩ : syracuseStep 1693203 = 2539805) B2539805
theorem B1693219 : Blo 1691546 1693219 := bstep (se 1 (by rfl) ⟨1269914, by rfl⟩ : syracuseStep 1693219 = 2539829) B2539829
theorem B1693235 : Blo 1691546 1693235 := bstep (se 1 (by rfl) ⟨1269926, by rfl⟩ : syracuseStep 1693235 = 2539853) B2539853
theorem B4281923 : Blo 1691546 4281923 := bstep (se 1 (by rfl) ⟨3211442, by rfl⟩ : syracuseStep 4281923 = 6422885) B6422885
theorem B1693251 : Blo 1691546 1693251 := bstep (se 1 (by rfl) ⟨1269938, by rfl⟩ : syracuseStep 1693251 = 2539877) B2539877
theorem B3806801 : Blo 1691546 3806801 := bstep (se 2 (by rfl) ⟨1427550, by rfl⟩ : syracuseStep 3806801 = 2855101) B2855101
theorem B1693267 : Blo 1691546 1693267 := bstep (se 1 (by rfl) ⟨1269950, by rfl⟩ : syracuseStep 1693267 = 2539901) B2539901
theorem B3806819 : Blo 1691546 3806819 := bstep (se 1 (by rfl) ⟨2855114, by rfl⟩ : syracuseStep 3806819 = 5710229) B5710229
theorem B1693283 : Blo 1691546 1693283 := bstep (se 1 (by rfl) ⟨1269962, by rfl⟩ : syracuseStep 1693283 = 2539925) B2539925
theorem B10581617 : Blo 1691546 10581617 := bstep (se 2 (by rfl) ⟨3968106, by rfl⟩ : syracuseStep 10581617 = 7936213) B7936213
theorem B1693299 : Blo 1691546 1693299 := bstep (se 1 (by rfl) ⟨1269974, by rfl⟩ : syracuseStep 1693299 = 2539949) B2539949
theorem B1693315 : Blo 1691546 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B2856593 : Blo 1691546 2856593 := bstep (se 2 (by rfl) ⟨1071222, by rfl⟩ : syracuseStep 2856593 = 2142445) B2142445
theorem B1693331 : Blo 1691546 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B1693347 : Blo 1691546 1693347 := bstep (se 1 (by rfl) ⟨1270010, by rfl⟩ : syracuseStep 1693347 = 2540021) B2540021
theorem B5715629 : Blo 1691546 5715629 := bstep (se 3 (by rfl) ⟨1071680, by rfl⟩ : syracuseStep 5715629 = 2143361) B2143361
theorem B1693363 : Blo 1691546 1693363 := bstep (se 1 (by rfl) ⟨1270022, by rfl⟩ : syracuseStep 1693363 = 2540045) B2540045
theorem B1693379 : Blo 1691546 1693379 := bstep (se 1 (by rfl) ⟨1270034, by rfl⟩ : syracuseStep 1693379 = 2540069) B2540069
theorem B7722701 : Blo 1691546 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B1693395 : Blo 1691546 1693395 := bstep (se 1 (by rfl) ⟨1270046, by rfl⟩ : syracuseStep 1693395 = 2540093) B2540093
theorem B1693411 : Blo 1691546 1693411 := bstep (se 1 (by rfl) ⟨1270058, by rfl⟩ : syracuseStep 1693411 = 2540117) B2540117
theorem B5715683 : Blo 1691546 5715683 := bstep (se 1 (by rfl) ⟨4286762, by rfl⟩ : syracuseStep 5715683 = 8573525) B8573525
theorem B1693427 : Blo 1691546 1693427 := bstep (se 1 (by rfl) ⟨1270070, by rfl⟩ : syracuseStep 1693427 = 2540141) B2540141
theorem B1693443 : Blo 1691546 1693443 := bstep (se 1 (by rfl) ⟨1270082, by rfl⟩ : syracuseStep 1693443 = 2540165) B2540165
theorem B6428429 : Blo 1691546 6428429 := bstep (se 3 (by rfl) ⟨1205330, by rfl⟩ : syracuseStep 6428429 = 2410661) B2410661
theorem B2856721 : Blo 1691546 2856721 := bstep (se 2 (by rfl) ⟨1071270, by rfl⟩ : syracuseStep 2856721 = 2142541) B2142541
theorem B1693459 : Blo 1691546 1693459 := bstep (se 1 (by rfl) ⟨1270094, by rfl⟩ : syracuseStep 1693459 = 2540189) B2540189
theorem B1693475 : Blo 1691546 1693475 := bstep (se 1 (by rfl) ⟨1270106, by rfl⟩ : syracuseStep 1693475 = 2540213) B2540213
theorem B2856755 : Blo 1691546 2856755 := bstep (se 1 (by rfl) ⟨2142566, by rfl⟩ : syracuseStep 2856755 = 4285133) B4285133
theorem B1693491 : Blo 1691546 1693491 := bstep (se 1 (by rfl) ⟨1270118, by rfl⟩ : syracuseStep 1693491 = 2540237) B2540237
theorem B30889781 : Blo 1691546 30889781 := bstep (se 5 (by rfl) ⟨1447958, by rfl⟩ : syracuseStep 30889781 = 2895917) B2895917
theorem B1693507 : Blo 1691546 1693507 := bstep (se 1 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 1693507 = 2540261) B2540261
theorem B9639749 : Blo 1691546 9639749 := bstep (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) B1807453
theorem B4577105 : Blo 1691546 4577105 := bstep (se 2 (by rfl) ⟨1716414, by rfl⟩ : syracuseStep 4577105 = 3432829) B3432829
theorem B1693523 : Blo 1691546 1693523 := bstep (se 1 (by rfl) ⟨1270142, by rfl⟩ : syracuseStep 1693523 = 2540285) B2540285
theorem B1693539 : Blo 1691546 1693539 := bstep (se 1 (by rfl) ⟨1270154, by rfl⟩ : syracuseStep 1693539 = 2540309) B2540309
theorem B3807089 : Blo 1691546 3807089 := bstep (se 2 (by rfl) ⟨1427658, by rfl⟩ : syracuseStep 3807089 = 2855317) B2855317
theorem B2537345 : Blo 1691546 2537345 := bstep (se 2 (by rfl) ⟨951504, by rfl⟩ : syracuseStep 2537345 = 1903009) B1903009
theorem B3807107 : Blo 1691546 3807107 := bstep (se 1 (by rfl) ⟨2855330, by rfl⟩ : syracuseStep 3807107 = 5710661) B5710661
theorem B2537363 : Blo 1691546 2537363 := bstep (se 1 (by rfl) ⟨1903022, by rfl⟩ : syracuseStep 2537363 = 3806045) B3806045
theorem B2537393 : Blo 1691546 2537393 := bstep (se 2 (by rfl) ⟨951522, by rfl⟩ : syracuseStep 2537393 = 1903045) B1903045
theorem B2856883 : Blo 1691546 2856883 := bstep (se 1 (by rfl) ⟨2142662, by rfl⟩ : syracuseStep 2856883 = 4285325) B4285325
theorem B2537411 : Blo 1691546 2537411 := bstep (se 1 (by rfl) ⟨1903058, by rfl⟩ : syracuseStep 2537411 = 3806117) B3806117
theorem B2537441 : Blo 1691546 2537441 := bstep (se 2 (by rfl) ⟨951540, by rfl⟩ : syracuseStep 2537441 = 1903081) B1903081
theorem B36591587 : Blo 1691546 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B2537459 : Blo 1691546 2537459 := bstep (se 1 (by rfl) ⟨1903094, by rfl⟩ : syracuseStep 2537459 = 3806189) B3806189
theorem B2537489 : Blo 1691546 2537489 := bstep (se 2 (by rfl) ⟨951558, by rfl⟩ : syracuseStep 2537489 = 1903117) B1903117
theorem B2537507 : Blo 1691546 2537507 := bstep (se 1 (by rfl) ⟨1903130, by rfl⟩ : syracuseStep 2537507 = 3806261) B3806261
theorem B2709553 : Blo 1691546 2709553 := bstep (se 2 (by rfl) ⟨1016082, by rfl⟩ : syracuseStep 2709553 = 2032165) B2032165
theorem B2537537 : Blo 1691546 2537537 := bstep (se 2 (by rfl) ⟨951576, by rfl⟩ : syracuseStep 2537537 = 1903153) B1903153
theorem B2857025 : Blo 1691546 2857025 := bstep (se 2 (by rfl) ⟨1071384, by rfl⟩ : syracuseStep 2857025 = 2142769) B2142769
theorem B2537555 : Blo 1691546 2537555 := bstep (se 1 (by rfl) ⟨1903166, by rfl⟩ : syracuseStep 2537555 = 3806333) B3806333
theorem B17201251 : Blo 1691546 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B8566883 : Blo 1691546 8566883 := bstep (se 1 (by rfl) ⟨6425162, by rfl⟩ : syracuseStep 8566883 = 12850325) B12850325
theorem B2537585 : Blo 1691546 2537585 := bstep (se 2 (by rfl) ⟨951594, by rfl⟩ : syracuseStep 2537585 = 1903189) B1903189
theorem B2537603 : Blo 1691546 2537603 := bstep (se 1 (by rfl) ⟨1903202, by rfl⟩ : syracuseStep 2537603 = 3806405) B3806405
theorem B3807377 : Blo 1691546 3807377 := bstep (se 2 (by rfl) ⟨1427766, by rfl⟩ : syracuseStep 3807377 = 2855533) B2855533
theorem B2537633 : Blo 1691546 2537633 := bstep (se 2 (by rfl) ⟨951612, by rfl⟩ : syracuseStep 2537633 = 1903225) B1903225
theorem B3807395 : Blo 1691546 3807395 := bstep (se 1 (by rfl) ⟨2855546, by rfl⟩ : syracuseStep 3807395 = 5711093) B5711093
theorem B2537651 : Blo 1691546 2537651 := bstep (se 1 (by rfl) ⟨1903238, by rfl⟩ : syracuseStep 2537651 = 3806477) B3806477
theorem B2857153 : Blo 1691546 2857153 := bstep (se 2 (by rfl) ⟨1071432, by rfl⟩ : syracuseStep 2857153 = 2142865) B2142865
theorem B2537681 : Blo 1691546 2537681 := bstep (se 2 (by rfl) ⟨951630, by rfl⟩ : syracuseStep 2537681 = 1903261) B1903261
theorem B2537699 : Blo 1691546 2537699 := bstep (se 1 (by rfl) ⟨1903274, by rfl⟩ : syracuseStep 2537699 = 3806549) B3806549
theorem B2857187 : Blo 1691546 2857187 := bstep (se 1 (by rfl) ⟨2142890, by rfl⟩ : syracuseStep 2857187 = 4285781) B4285781
theorem B7829731 : Blo 1691546 7829731 := bstep (se 1 (by rfl) ⟨5872298, by rfl⟩ : syracuseStep 7829731 = 11744597) B11744597
theorem B2537729 : Blo 1691546 2537729 := bstep (se 2 (by rfl) ⟨951648, by rfl⟩ : syracuseStep 2537729 = 1903297) B1903297
theorem B9640205 : Blo 1691546 9640205 := bstep (se 3 (by rfl) ⟨1807538, by rfl⟩ : syracuseStep 9640205 = 3615077) B3615077
theorem B2537747 : Blo 1691546 2537747 := bstep (se 1 (by rfl) ⟨1903310, by rfl⟩ : syracuseStep 2537747 = 3806621) B3806621
theorem B2537777 : Blo 1691546 2537777 := bstep (se 2 (by rfl) ⟨951666, by rfl⟩ : syracuseStep 2537777 = 1903333) B1903333
theorem B2537795 : Blo 1691546 2537795 := bstep (se 1 (by rfl) ⟨1903346, by rfl⟩ : syracuseStep 2537795 = 3806693) B3806693
theorem B2537825 : Blo 1691546 2537825 := bstep (se 2 (by rfl) ⟨951684, by rfl⟩ : syracuseStep 2537825 = 1903369) B1903369
theorem B2857315 : Blo 1691546 2857315 := bstep (se 1 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 2857315 = 4285973) B4285973
theorem B2537843 : Blo 1691546 2537843 := bstep (se 1 (by rfl) ⟨1903382, by rfl⟩ : syracuseStep 2537843 = 3806765) B3806765
theorem B1882483 : Blo 1691546 1882483 := bstep (se 1 (by rfl) ⟨1411862, by rfl⟩ : syracuseStep 1882483 = 2823725) B2823725
theorem B2537873 : Blo 1691546 2537873 := bstep (se 2 (by rfl) ⟨951702, by rfl⟩ : syracuseStep 2537873 = 1903405) B1903405
theorem B2537891 : Blo 1691546 2537891 := bstep (se 1 (by rfl) ⟨1903418, by rfl⟩ : syracuseStep 2537891 = 3806837) B3806837
theorem B3807665 : Blo 1691546 3807665 := bstep (se 2 (by rfl) ⟨1427874, by rfl⟩ : syracuseStep 3807665 = 2855749) B2855749
theorem B2537921 : Blo 1691546 2537921 := bstep (se 2 (by rfl) ⟨951720, by rfl⟩ : syracuseStep 2537921 = 1903441) B1903441
theorem B3807683 : Blo 1691546 3807683 := bstep (se 1 (by rfl) ⟨2855762, by rfl⟩ : syracuseStep 3807683 = 5711525) B5711525
theorem B2537939 : Blo 1691546 2537939 := bstep (se 1 (by rfl) ⟨1903454, by rfl⟩ : syracuseStep 2537939 = 3806909) B3806909
theorem B5421539 : Blo 1691546 5421539 := bstep (se 1 (by rfl) ⟨4066154, by rfl⟩ : syracuseStep 5421539 = 8132309) B8132309
theorem B3430883 : Blo 1691546 3430883 := bstep (se 1 (by rfl) ⟨2573162, by rfl⟩ : syracuseStep 3430883 = 5146325) B5146325
theorem B2710001 : Blo 1691546 2710001 := bstep (se 2 (by rfl) ⟨1016250, by rfl⟩ : syracuseStep 2710001 = 2032501) B2032501
theorem B2537969 : Blo 1691546 2537969 := bstep (se 2 (by rfl) ⟨951738, by rfl⟩ : syracuseStep 2537969 = 1903477) B1903477
theorem B4282865 : Blo 1691546 4282865 := bstep (se 2 (by rfl) ⟨1606074, by rfl⟩ : syracuseStep 4282865 = 3212149) B3212149
theorem B2857457 : Blo 1691546 2857457 := bstep (se 2 (by rfl) ⟨1071546, by rfl⟩ : syracuseStep 2857457 = 2143093) B2143093
theorem B2537987 : Blo 1691546 2537987 := bstep (se 1 (by rfl) ⟨1903490, by rfl⟩ : syracuseStep 2537987 = 3806981) B3806981
theorem B2538017 : Blo 1691546 2538017 := bstep (se 2 (by rfl) ⟨951756, by rfl⟩ : syracuseStep 2538017 = 1903513) B1903513
theorem B4282915 : Blo 1691546 4282915 := bstep (se 1 (by rfl) ⟨3212186, by rfl⟩ : syracuseStep 4282915 = 6424373) B6424373
theorem B6429233 : Blo 1691546 6429233 := bstep (se 2 (by rfl) ⟨2410962, by rfl⟩ : syracuseStep 6429233 = 4821925) B4821925
theorem B2538035 : Blo 1691546 2538035 := bstep (se 1 (by rfl) ⟨1903526, by rfl⟩ : syracuseStep 2538035 = 3807053) B3807053
theorem B2538065 : Blo 1691546 2538065 := bstep (se 2 (by rfl) ⟨951774, by rfl⟩ : syracuseStep 2538065 = 1903549) B1903549
theorem B2538083 : Blo 1691546 2538083 := bstep (se 1 (by rfl) ⟨1903562, by rfl⟩ : syracuseStep 2538083 = 3807125) B3807125
theorem B2857585 : Blo 1691546 2857585 := bstep (se 2 (by rfl) ⟨1071594, by rfl⟩ : syracuseStep 2857585 = 2143189) B2143189
theorem B2538113 : Blo 1691546 2538113 := bstep (se 2 (by rfl) ⟨951792, by rfl⟩ : syracuseStep 2538113 = 1903585) B1903585
theorem B12860045 : Blo 1691546 12860045 := bstep (se 3 (by rfl) ⟨2411258, by rfl⟩ : syracuseStep 12860045 = 4822517) B4822517
theorem B2538131 : Blo 1691546 2538131 := bstep (se 1 (by rfl) ⟨1903598, by rfl⟩ : syracuseStep 2538131 = 3807197) B3807197
theorem B2857619 : Blo 1691546 2857619 := bstep (se 1 (by rfl) ⟨2143214, by rfl⟩ : syracuseStep 2857619 = 4286429) B4286429
theorem B4283057 : Blo 1691546 4283057 := bstep (se 2 (by rfl) ⟨1606146, by rfl⟩ : syracuseStep 4283057 = 3212293) B3212293
theorem B2538161 : Blo 1691546 2538161 := bstep (se 2 (by rfl) ⟨951810, by rfl⟩ : syracuseStep 2538161 = 1903621) B1903621
theorem B2538179 : Blo 1691546 2538179 := bstep (se 1 (by rfl) ⟨1903634, by rfl⟩ : syracuseStep 2538179 = 3807269) B3807269
theorem B3807953 : Blo 1691546 3807953 := bstep (se 2 (by rfl) ⟨1427982, by rfl⟩ : syracuseStep 3807953 = 2855965) B2855965
theorem B2538209 : Blo 1691546 2538209 := bstep (se 2 (by rfl) ⟨951828, by rfl⟩ : syracuseStep 2538209 = 1903657) B1903657
theorem B3807971 : Blo 1691546 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B2538227 : Blo 1691546 2538227 := bstep (se 1 (by rfl) ⟨1903670, by rfl⟩ : syracuseStep 2538227 = 3807341) B3807341
theorem B2538257 : Blo 1691546 2538257 := bstep (se 2 (by rfl) ⟨951846, by rfl⟩ : syracuseStep 2538257 = 1903693) B1903693
theorem B2857747 : Blo 1691546 2857747 := bstep (se 1 (by rfl) ⟨2143310, by rfl⟩ : syracuseStep 2857747 = 4286621) B4286621
theorem B2538275 : Blo 1691546 2538275 := bstep (se 1 (by rfl) ⟨1903706, by rfl⟩ : syracuseStep 2538275 = 3807413) B3807413
theorem B2538305 : Blo 1691546 2538305 := bstep (se 2 (by rfl) ⟨951864, by rfl⟩ : syracuseStep 2538305 = 1903729) B1903729
theorem B2538323 : Blo 1691546 2538323 := bstep (se 1 (by rfl) ⟨1903742, by rfl⟩ : syracuseStep 2538323 = 3807485) B3807485
theorem B2538353 : Blo 1691546 2538353 := bstep (se 2 (by rfl) ⟨951882, by rfl⟩ : syracuseStep 2538353 = 1903765) B1903765
theorem B2538371 : Blo 1691546 2538371 := bstep (se 1 (by rfl) ⟨1903778, by rfl⟩ : syracuseStep 2538371 = 3807557) B3807557
theorem B8567693 : Blo 1691546 8567693 := bstep (se 3 (by rfl) ⟨1606442, by rfl⟩ : syracuseStep 8567693 = 3212885) B3212885
theorem B2538401 : Blo 1691546 2538401 := bstep (se 2 (by rfl) ⟨951900, by rfl⟩ : syracuseStep 2538401 = 1903801) B1903801
theorem B2538419 : Blo 1691546 2538419 := bstep (se 1 (by rfl) ⟨1903814, by rfl⟩ : syracuseStep 2538419 = 3807629) B3807629
theorem B2538449 : Blo 1691546 2538449 := bstep (se 2 (by rfl) ⟨951918, by rfl⟩ : syracuseStep 2538449 = 1903837) B1903837
theorem B2538467 : Blo 1691546 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B3808241 : Blo 1691546 3808241 := bstep (se 2 (by rfl) ⟨1428090, by rfl⟩ : syracuseStep 3808241 = 2856181) B2856181
theorem B16268273 : Blo 1691546 16268273 := bstep (se 2 (by rfl) ⟨6100602, by rfl⟩ : syracuseStep 16268273 = 12201205) B12201205
theorem B2538497 : Blo 1691546 2538497 := bstep (se 2 (by rfl) ⟨951936, by rfl⟩ : syracuseStep 2538497 = 1903873) B1903873
theorem B3808259 : Blo 1691546 3808259 := bstep (se 1 (by rfl) ⟨2856194, by rfl⟩ : syracuseStep 3808259 = 5712389) B5712389
theorem B2538515 : Blo 1691546 2538515 := bstep (se 1 (by rfl) ⟨1903886, by rfl⟩ : syracuseStep 2538515 = 3807773) B3807773
theorem B2538545 : Blo 1691546 2538545 := bstep (se 2 (by rfl) ⟨951954, by rfl⟩ : syracuseStep 2538545 = 1903909) B1903909
theorem B2538563 : Blo 1691546 2538563 := bstep (se 1 (by rfl) ⟨1903922, by rfl⟩ : syracuseStep 2538563 = 3807845) B3807845
theorem B2538593 : Blo 1691546 2538593 := bstep (se 2 (by rfl) ⟨951972, by rfl⟩ : syracuseStep 2538593 = 1903945) B1903945
theorem B2538611 : Blo 1691546 2538611 := bstep (se 1 (by rfl) ⟨1903958, by rfl⟩ : syracuseStep 2538611 = 3807917) B3807917
theorem B2538641 : Blo 1691546 2538641 := bstep (se 2 (by rfl) ⟨951990, by rfl⟩ : syracuseStep 2538641 = 1903981) B1903981
theorem B2538659 : Blo 1691546 2538659 := bstep (se 1 (by rfl) ⟨1903994, by rfl⟩ : syracuseStep 2538659 = 3807989) B3807989
theorem B2538689 : Blo 1691546 2538689 := bstep (se 2 (by rfl) ⟨952008, by rfl⟩ : syracuseStep 2538689 = 1904017) B1904017
theorem B6429901 : Blo 1691546 6429901 := bstep (se 3 (by rfl) ⟨1205606, by rfl⟩ : syracuseStep 6429901 = 2411213) B2411213
theorem B2538707 : Blo 1691546 2538707 := bstep (se 1 (by rfl) ⟨1904030, by rfl⟩ : syracuseStep 2538707 = 3808061) B3808061
theorem B5709041 : Blo 1691546 5709041 := bstep (se 2 (by rfl) ⟨2140890, by rfl⟩ : syracuseStep 5709041 = 4281781) B4281781
theorem B2538737 : Blo 1691546 2538737 := bstep (se 2 (by rfl) ⟨952026, by rfl⟩ : syracuseStep 2538737 = 1904053) B1904053
theorem B2538755 : Blo 1691546 2538755 := bstep (se 1 (by rfl) ⟨1904066, by rfl⟩ : syracuseStep 2538755 = 3808133) B3808133
theorem B3808529 : Blo 1691546 3808529 := bstep (se 2 (by rfl) ⟨1428198, by rfl⟩ : syracuseStep 3808529 = 2856397) B2856397
theorem B2538785 : Blo 1691546 2538785 := bstep (se 2 (by rfl) ⟨952044, by rfl⟩ : syracuseStep 2538785 = 1904089) B1904089
theorem B3808547 : Blo 1691546 3808547 := bstep (se 1 (by rfl) ⟨2856410, by rfl⟩ : syracuseStep 3808547 = 5712821) B5712821
theorem B2538803 : Blo 1691546 2538803 := bstep (se 1 (by rfl) ⟨1904102, by rfl⟩ : syracuseStep 2538803 = 3808205) B3808205
theorem B2538833 : Blo 1691546 2538833 := bstep (se 2 (by rfl) ⟨952062, by rfl⟩ : syracuseStep 2538833 = 1904125) B1904125
theorem B2538851 : Blo 1691546 2538851 := bstep (se 1 (by rfl) ⟨1904138, by rfl⟩ : syracuseStep 2538851 = 3808277) B3808277
theorem B10845539 : Blo 1691546 10845539 := bstep (se 1 (by rfl) ⟨8134154, by rfl⟩ : syracuseStep 10845539 = 16268309) B16268309
theorem B2538881 : Blo 1691546 2538881 := bstep (se 2 (by rfl) ⟨952080, by rfl⟩ : syracuseStep 2538881 = 1904161) B1904161
theorem B2538899 : Blo 1691546 2538899 := bstep (se 1 (by rfl) ⟨1904174, by rfl⟩ : syracuseStep 2538899 = 3808349) B3808349
theorem B2538929 : Blo 1691546 2538929 := bstep (se 2 (by rfl) ⟨952098, by rfl⟩ : syracuseStep 2538929 = 1904197) B1904197
theorem B6102449 : Blo 1691546 6102449 := bstep (se 2 (by rfl) ⟨2288418, by rfl⟩ : syracuseStep 6102449 = 4576837) B4576837
theorem B19553717 : Blo 1691546 19553717 := bstep (se 5 (by rfl) ⟨916580, by rfl⟩ : syracuseStep 19553717 = 1833161) B1833161
theorem B2538947 : Blo 1691546 2538947 := bstep (se 1 (by rfl) ⟨1904210, by rfl⟩ : syracuseStep 2538947 = 3808421) B3808421
theorem B2538977 : Blo 1691546 2538977 := bstep (se 2 (by rfl) ⟨952116, by rfl⟩ : syracuseStep 2538977 = 1904233) B1904233
theorem B2538995 : Blo 1691546 2538995 := bstep (se 1 (by rfl) ⟨1904246, by rfl⟩ : syracuseStep 2538995 = 3808493) B3808493
theorem B2539025 : Blo 1691546 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B2539043 : Blo 1691546 2539043 := bstep (se 1 (by rfl) ⟨1904282, by rfl⟩ : syracuseStep 2539043 = 3808565) B3808565
theorem B3808817 : Blo 1691546 3808817 := bstep (se 2 (by rfl) ⟨1428306, by rfl⟩ : syracuseStep 3808817 = 2856613) B2856613
theorem B333700661 : Blo 1691546 333700661 := bstep (se 5 (by rfl) ⟨15642218, by rfl⟩ : syracuseStep 333700661 = 31284437) B31284437
theorem B2539073 : Blo 1691546 2539073 := bstep (se 2 (by rfl) ⟨952152, by rfl⟩ : syracuseStep 2539073 = 1904305) B1904305
theorem B3808835 : Blo 1691546 3808835 := bstep (se 1 (by rfl) ⟨2856626, by rfl⟩ : syracuseStep 3808835 = 5713253) B5713253
theorem B2539091 : Blo 1691546 2539091 := bstep (se 1 (by rfl) ⟨1904318, by rfl⟩ : syracuseStep 2539091 = 3808637) B3808637
theorem B2539121 : Blo 1691546 2539121 := bstep (se 2 (by rfl) ⟨952170, by rfl⟩ : syracuseStep 2539121 = 1904341) B1904341
theorem B2539139 : Blo 1691546 2539139 := bstep (se 1 (by rfl) ⟨1904354, by rfl⟩ : syracuseStep 2539139 = 3808709) B3808709
theorem B4284049 : Blo 1691546 4284049 := bstep (se 2 (by rfl) ⟨1606518, by rfl⟩ : syracuseStep 4284049 = 3213037) B3213037
theorem B2539169 : Blo 1691546 2539169 := bstep (se 2 (by rfl) ⟨952188, by rfl⟩ : syracuseStep 2539169 = 1904377) B1904377
theorem B2539187 : Blo 1691546 2539187 := bstep (se 1 (by rfl) ⟨1904390, by rfl⟩ : syracuseStep 2539187 = 3808781) B3808781
theorem B7233229 : Blo 1691546 7233229 := bstep (se 3 (by rfl) ⟨1356230, by rfl⟩ : syracuseStep 7233229 = 2712461) B2712461
theorem B2539217 : Blo 1691546 2539217 := bstep (se 2 (by rfl) ⟨952206, by rfl⟩ : syracuseStep 2539217 = 1904413) B1904413
theorem B2539235 : Blo 1691546 2539235 := bstep (se 1 (by rfl) ⟨1904426, by rfl⟩ : syracuseStep 2539235 = 3808853) B3808853
theorem B2539265 : Blo 1691546 2539265 := bstep (se 2 (by rfl) ⟨952224, by rfl⟩ : syracuseStep 2539265 = 1904449) B1904449
theorem B5709581 : Blo 1691546 5709581 := bstep (se 3 (by rfl) ⟨1070546, by rfl⟩ : syracuseStep 5709581 = 2141093) B2141093
theorem B2539283 : Blo 1691546 2539283 := bstep (se 1 (by rfl) ⟨1904462, by rfl⟩ : syracuseStep 2539283 = 3808925) B3808925
theorem B10846001 : Blo 1691546 10846001 := bstep (se 2 (by rfl) ⟨4067250, by rfl⟩ : syracuseStep 10846001 = 8134501) B8134501
theorem B2539313 : Blo 1691546 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B5709635 : Blo 1691546 5709635 := bstep (se 1 (by rfl) ⟨4282226, by rfl⟩ : syracuseStep 5709635 = 8564453) B8564453
theorem B2539331 : Blo 1691546 2539331 := bstep (se 1 (by rfl) ⟨1904498, by rfl⟩ : syracuseStep 2539331 = 3808997) B3808997
theorem B3809105 : Blo 1691546 3809105 := bstep (se 2 (by rfl) ⟨1428414, by rfl⟩ : syracuseStep 3809105 = 2856829) B2856829
theorem B2539361 : Blo 1691546 2539361 := bstep (se 2 (by rfl) ⟨952260, by rfl⟩ : syracuseStep 2539361 = 1904521) B1904521
theorem B3809123 : Blo 1691546 3809123 := bstep (se 1 (by rfl) ⟨2856842, by rfl⟩ : syracuseStep 3809123 = 5713685) B5713685
theorem B2711411 : Blo 1691546 2711411 := bstep (se 1 (by rfl) ⟨2033558, by rfl⟩ : syracuseStep 2711411 = 4067117) B4067117
theorem B2539379 : Blo 1691546 2539379 := bstep (se 1 (by rfl) ⟨1904534, by rfl⟩ : syracuseStep 2539379 = 3809069) B3809069
theorem B2539409 : Blo 1691546 2539409 := bstep (se 2 (by rfl) ⟨952278, by rfl⟩ : syracuseStep 2539409 = 1904557) B1904557
theorem B4284323 : Blo 1691546 4284323 := bstep (se 1 (by rfl) ⟨3213242, by rfl⟩ : syracuseStep 4284323 = 6426485) B6426485
theorem B2539427 : Blo 1691546 2539427 := bstep (se 1 (by rfl) ⟨1904570, by rfl⟩ : syracuseStep 2539427 = 3809141) B3809141
theorem B2539457 : Blo 1691546 2539457 := bstep (se 2 (by rfl) ⟨952296, by rfl⟩ : syracuseStep 2539457 = 1904593) B1904593
theorem B30883781 : Blo 1691546 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B2539475 : Blo 1691546 2539475 := bstep (se 1 (by rfl) ⟨1904606, by rfl⟩ : syracuseStep 2539475 = 3809213) B3809213
theorem B2539505 : Blo 1691546 2539505 := bstep (se 2 (by rfl) ⟨952314, by rfl⟩ : syracuseStep 2539505 = 1904629) B1904629
theorem B3809303 : Blo 1691546 3809303 := bstep (se 1 (by rfl) ⟨2856977, by rfl⟩ : syracuseStep 3809303 = 5713955) B5713955
theorem B3612737 : Blo 1691546 3612737 := bstep (se 2 (by rfl) ⟨1354776, by rfl⟩ : syracuseStep 3612737 = 2709553) B2709553
theorem B2539595 : Blo 1691546 2539595 := bstep (se 1 (by rfl) ⟨1904696, by rfl⟩ : syracuseStep 2539595 = 3809393) B3809393
theorem B2539607 : Blo 1691546 2539607 := bstep (se 1 (by rfl) ⟨1904705, by rfl⟩ : syracuseStep 2539607 = 3809411) B3809411
theorem B2711641 : Blo 1691546 2711641 := bstep (se 2 (by rfl) ⟨1016865, by rfl⟩ : syracuseStep 2711641 = 2033731) B2033731
theorem B28213379 : Blo 1691546 28213379 := bstep (se 1 (by rfl) ⟨21160034, by rfl⟩ : syracuseStep 28213379 = 42320069) B42320069
theorem B2539673 : Blo 1691546 2539673 := bstep (se 2 (by rfl) ⟨952377, by rfl⟩ : syracuseStep 2539673 = 1904755) B1904755
theorem B3809483 : Blo 1691546 3809483 := bstep (se 1 (by rfl) ⟨2857112, by rfl⟩ : syracuseStep 3809483 = 5714225) B5714225
theorem B3211481 : Blo 1691546 3211481 := bstep (se 2 (by rfl) ⟨1204305, by rfl⟩ : syracuseStep 3211481 = 2408611) B2408611
theorem B3809537 : Blo 1691546 3809537 := bstep (se 2 (by rfl) ⟨1428576, by rfl⟩ : syracuseStep 3809537 = 2857153) B2857153
theorem B2539787 : Blo 1691546 2539787 := bstep (se 1 (by rfl) ⟨1904840, by rfl⟩ : syracuseStep 2539787 = 3809681) B3809681
theorem B2539799 : Blo 1691546 2539799 := bstep (se 1 (by rfl) ⟨1904849, by rfl⟩ : syracuseStep 2539799 = 3809699) B3809699
theorem B39608621 : Blo 1691546 39608621 := bstep (se 3 (by rfl) ⟨7426616, by rfl⟩ : syracuseStep 39608621 = 14853233) B14853233
theorem B21692717 : Blo 1691546 21692717 := bstep (se 3 (by rfl) ⟨4067384, by rfl⟩ : syracuseStep 21692717 = 8134769) B8134769
theorem B5423411 : Blo 1691546 5423411 := bstep (se 1 (by rfl) ⟨4067558, by rfl⟩ : syracuseStep 5423411 = 8135117) B8135117
theorem B2539865 : Blo 1691546 2539865 := bstep (se 2 (by rfl) ⟨952449, by rfl⟩ : syracuseStep 2539865 = 1904899) B1904899
theorem B6422915 : Blo 1691546 6422915 := bstep (se 1 (by rfl) ⟨4817186, by rfl⟩ : syracuseStep 6422915 = 9634373) B9634373
theorem B3613079 : Blo 1691546 3613079 := bstep (se 1 (by rfl) ⟨2709809, by rfl⟩ : syracuseStep 3613079 = 5419619) B5419619
theorem B5710283 : Blo 1691546 5710283 := bstep (se 1 (by rfl) ⟨4282712, by rfl⟩ : syracuseStep 5710283 = 8565425) B8565425
theorem B2539979 : Blo 1691546 2539979 := bstep (se 1 (by rfl) ⟨1904984, by rfl⟩ : syracuseStep 2539979 = 3809969) B3809969
theorem B14451149 : Blo 1691546 14451149 := bstep (se 3 (by rfl) ⟨2709590, by rfl⟩ : syracuseStep 14451149 = 5419181) B5419181
theorem B2539991 : Blo 1691546 2539991 := bstep (se 1 (by rfl) ⟨1904993, by rfl⟩ : syracuseStep 2539991 = 3809987) B3809987
theorem B4817369 : Blo 1691546 4817369 := bstep (se 2 (by rfl) ⟨1806513, by rfl⟩ : syracuseStep 4817369 = 3613027) B3613027
theorem B5145049 : Blo 1691546 5145049 := bstep (se 2 (by rfl) ⟨1929393, by rfl⟩ : syracuseStep 5145049 = 3858787) B3858787
theorem B3809753 : Blo 1691546 3809753 := bstep (se 2 (by rfl) ⟨1428657, by rfl⟩ : syracuseStep 3809753 = 2857315) B2857315
theorem B2540057 : Blo 1691546 2540057 := bstep (se 2 (by rfl) ⟨952521, by rfl⟩ : syracuseStep 2540057 = 1905043) B1905043
theorem B3809843 : Blo 1691546 3809843 := bstep (se 1 (by rfl) ⟨2857382, by rfl⟩ : syracuseStep 3809843 = 5714765) B5714765
theorem B3809879 : Blo 1691546 3809879 := bstep (se 1 (by rfl) ⟨2857409, by rfl⟩ : syracuseStep 3809879 = 5714819) B5714819
theorem B2409049 : Blo 1691546 2409049 := bstep (se 2 (by rfl) ⟨903393, by rfl⟩ : syracuseStep 2409049 = 1806787) B1806787
theorem B8569475 : Blo 1691546 8569475 := bstep (se 1 (by rfl) ⟨6427106, by rfl⟩ : syracuseStep 8569475 = 12854213) B12854213
theorem B2540171 : Blo 1691546 2540171 := bstep (se 1 (by rfl) ⟨1905128, by rfl⟩ : syracuseStep 2540171 = 3810257) B3810257
theorem B2540183 : Blo 1691546 2540183 := bstep (se 1 (by rfl) ⟨1905137, by rfl⟩ : syracuseStep 2540183 = 3810275) B3810275
theorem B5710553 : Blo 1691546 5710553 := bstep (se 2 (by rfl) ⟨2141457, by rfl⟩ : syracuseStep 5710553 = 4282915) B4282915
theorem B2540249 : Blo 1691546 2540249 := bstep (se 2 (by rfl) ⟨952593, by rfl⟩ : syracuseStep 2540249 = 1905187) B1905187
theorem B3810059 : Blo 1691546 3810059 := bstep (se 1 (by rfl) ⟨2857544, by rfl⟩ : syracuseStep 3810059 = 5715089) B5715089
theorem B7324433 : Blo 1691546 7324433 := bstep (se 2 (by rfl) ⟨2746662, by rfl⟩ : syracuseStep 7324433 = 5493325) B5493325
theorem B9634625 : Blo 1691546 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B65946433 : Blo 1691546 65946433 := bstep (se 2 (by rfl) ⟨24729912, by rfl⟩ : syracuseStep 65946433 = 49459825) B49459825
theorem B3810113 : Blo 1691546 3810113 := bstep (se 2 (by rfl) ⟨1428792, by rfl⟩ : syracuseStep 3810113 = 2857585) B2857585
theorem B6423371 : Blo 1691546 6423371 := bstep (se 1 (by rfl) ⟨4817528, by rfl⟩ : syracuseStep 6423371 = 9635057) B9635057
theorem B7226243 : Blo 1691546 7226243 := bstep (se 1 (by rfl) ⟨5419682, by rfl⟩ : syracuseStep 7226243 = 10839365) B10839365
theorem B10847155 : Blo 1691546 10847155 := bstep (se 1 (by rfl) ⟨8135366, by rfl⟩ : syracuseStep 10847155 = 16270733) B16270733
theorem B3859417 : Blo 1691546 3859417 := bstep (se 2 (by rfl) ⟨1447281, by rfl⟩ : syracuseStep 3859417 = 2894563) B2894563
theorem B6423569 : Blo 1691546 6423569 := bstep (se 2 (by rfl) ⟨2408838, by rfl⟩ : syracuseStep 6423569 = 4817677) B4817677
theorem B3810329 : Blo 1691546 3810329 := bstep (se 2 (by rfl) ⟨1428873, by rfl⟩ : syracuseStep 3810329 = 2857747) B2857747
theorem B6865985 : Blo 1691546 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B24396875 : Blo 1691546 24396875 := bstep (se 1 (by rfl) ⟨18297656, by rfl⟩ : syracuseStep 24396875 = 36595313) B36595313
theorem B7054411 : Blo 1691546 7054411 := bstep (se 1 (by rfl) ⟨5290808, by rfl⟩ : syracuseStep 7054411 = 10581617) B10581617
theorem B3810419 : Blo 1691546 3810419 := bstep (se 1 (by rfl) ⟨2857814, by rfl⟩ : syracuseStep 3810419 = 5715629) B5715629
theorem B3810455 : Blo 1691546 3810455 := bstep (se 1 (by rfl) ⟨2857841, by rfl⟩ : syracuseStep 3810455 = 5715683) B5715683
theorem B4285619 : Blo 1691546 4285619 := bstep (se 1 (by rfl) ⟨3214214, by rfl⟩ : syracuseStep 4285619 = 6428429) B6428429
theorem B89105669 : Blo 1691546 89105669 := bstep (se 4 (by rfl) ⟨8353656, by rfl⟩ : syracuseStep 89105669 = 16707313) B16707313
theorem B12846437 : Blo 1691546 12846437 := bstep (se 4 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 12846437 = 2408707) B2408707
theorem B43394453 : Blo 1691546 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B5711255 : Blo 1691546 5711255 := bstep (se 1 (by rfl) ⟨4283441, by rfl⟩ : syracuseStep 5711255 = 8566883) B8566883
theorem B4572695 : Blo 1691546 4572695 := bstep (se 1 (by rfl) ⟨3429521, by rfl⟩ : syracuseStep 4572695 = 6859043) B6859043
theorem B3212939 : Blo 1691546 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B4286155 : Blo 1691546 4286155 := bstep (se 1 (by rfl) ⟨3214616, by rfl⟩ : syracuseStep 4286155 = 6429233) B6429233
theorem B6424343 : Blo 1691546 6424343 := bstep (se 1 (by rfl) ⟨4818257, by rfl⟩ : syracuseStep 6424343 = 9636515) B9636515
theorem B3213121 : Blo 1691546 3213121 := bstep (se 2 (by rfl) ⟨1204920, by rfl⟩ : syracuseStep 3213121 = 2409841) B2409841
theorem B12846923 : Blo 1691546 12846923 := bstep (se 1 (by rfl) ⟨9635192, by rfl⟩ : syracuseStep 12846923 = 19270385) B19270385
theorem B4286297 : Blo 1691546 4286297 := bstep (se 2 (by rfl) ⟨1607361, by rfl⟩ : syracuseStep 4286297 = 3214723) B3214723
theorem B4818781 : Blo 1691546 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B37119845 : Blo 1691546 37119845 := bstep (se 4 (by rfl) ⟨3479985, by rfl⟩ : syracuseStep 37119845 = 6959971) B6959971
theorem B5146519 : Blo 1691546 5146519 := bstep (se 1 (by rfl) ⟨3859889, by rfl⟩ : syracuseStep 5146519 = 7719779) B7719779
theorem B2410393 : Blo 1691546 2410393 := bstep (se 2 (by rfl) ⟨903897, by rfl⟩ : syracuseStep 2410393 = 1807795) B1807795
theorem B5711795 : Blo 1691546 5711795 := bstep (se 1 (by rfl) ⟨4283846, by rfl⟩ : syracuseStep 5711795 = 8567693) B8567693
theorem B6424541 : Blo 1691546 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B2410507 : Blo 1691546 2410507 := bstep (se 1 (by rfl) ⟨1807880, by rfl⟩ : syracuseStep 2410507 = 3615761) B3615761
theorem B4819009 : Blo 1691546 4819009 := bstep (se 2 (by rfl) ⟨1807128, by rfl⟩ : syracuseStep 4819009 = 3614257) B3614257
theorem B5712065 : Blo 1691546 5712065 := bstep (se 2 (by rfl) ⟨2142024, by rfl⟩ : syracuseStep 5712065 = 4284049) B4284049
theorem B3213569 : Blo 1691546 3213569 := bstep (se 2 (by rfl) ⟨1205088, by rfl⟩ : syracuseStep 3213569 = 2410177) B2410177
theorem B15444229 : Blo 1691546 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B13723921 : Blo 1691546 13723921 := bstep (se 2 (by rfl) ⟨5146470, by rfl⟩ : syracuseStep 13723921 = 10292941) B10292941
theorem B9644305 : Blo 1691546 9644305 := bstep (se 2 (by rfl) ⟨3616614, by rfl⟩ : syracuseStep 9644305 = 7233229) B7233229
theorem B13035811 : Blo 1691546 13035811 := bstep (se 1 (by rfl) ⟨9776858, by rfl⟩ : syracuseStep 13035811 = 19553717) B19553717
theorem B4819351 : Blo 1691546 4819351 := bstep (se 1 (by rfl) ⟨3614513, by rfl⟩ : syracuseStep 4819351 = 7229027) B7229027
theorem B1903063 : Blo 1691546 1903063 := bstep (se 1 (by rfl) ⟨1427297, by rfl⟩ : syracuseStep 1903063 = 2854595) B2854595
theorem B82356749 : Blo 1691546 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B3213911 : Blo 1691546 3213911 := bstep (se 1 (by rfl) ⟨2410433, by rfl⟩ : syracuseStep 3213911 = 4820867) B4820867
theorem B1903243 : Blo 1691546 1903243 := bstep (se 1 (by rfl) ⟨1427432, by rfl⟩ : syracuseStep 1903243 = 2854865) B2854865
theorem B5712605 : Blo 1691546 5712605 := bstep (se 3 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 5712605 = 2142227) B2142227
theorem B1903351 : Blo 1691546 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B10840877 : Blo 1691546 10840877 := bstep (se 3 (by rfl) ⟨2032664, by rfl⟩ : syracuseStep 10840877 = 4065329) B4065329
theorem B12856157 : Blo 1691546 12856157 := bstep (se 3 (by rfl) ⟨2410529, by rfl⟩ : syracuseStep 12856157 = 4821059) B4821059
theorem B1903531 : Blo 1691546 1903531 := bstep (se 1 (by rfl) ⟨1427648, by rfl⟩ : syracuseStep 1903531 = 2855297) B2855297
theorem B41184217 : Blo 1691546 41184217 := bstep (se 2 (by rfl) ⟨15444081, by rfl⟩ : syracuseStep 41184217 = 30888163) B30888163
theorem B10439641 : Blo 1691546 10439641 := bstep (se 2 (by rfl) ⟨3914865, by rfl⟩ : syracuseStep 10439641 = 7829731) B7829731
theorem B1903639 : Blo 1691546 1903639 := bstep (se 1 (by rfl) ⟨1427729, by rfl⟩ : syracuseStep 1903639 = 2855459) B2855459
theorem B4820057 : Blo 1691546 4820057 := bstep (se 2 (by rfl) ⟨1807521, by rfl⟩ : syracuseStep 4820057 = 3615043) B3615043
theorem B8563805 : Blo 1691546 8563805 := bstep (se 3 (by rfl) ⟨1605713, by rfl⟩ : syracuseStep 8563805 = 3211427) B3211427
theorem B8244355 : Blo 1691546 8244355 := bstep (se 1 (by rfl) ⟨6183266, by rfl⟩ : syracuseStep 8244355 = 12366533) B12366533
theorem B8686723 : Blo 1691546 8686723 := bstep (se 1 (by rfl) ⟨6515042, by rfl⟩ : syracuseStep 8686723 = 13030085) B13030085
theorem B9637015 : Blo 1691546 9637015 := bstep (se 1 (by rfl) ⟨7227761, by rfl⟩ : syracuseStep 9637015 = 14455523) B14455523
theorem B1903819 : Blo 1691546 1903819 := bstep (se 1 (by rfl) ⟨1427864, by rfl⟩ : syracuseStep 1903819 = 2855729) B2855729
theorem B3214579 : Blo 1691546 3214579 := bstep (se 1 (by rfl) ⟨2410934, by rfl⟩ : syracuseStep 3214579 = 4821869) B4821869
theorem B1903927 : Blo 1691546 1903927 := bstep (se 1 (by rfl) ⟨1427945, by rfl⟩ : syracuseStep 1903927 = 2855891) B2855891
theorem B2141579 : Blo 1691546 2141579 := bstep (se 1 (by rfl) ⟨1606184, by rfl⟩ : syracuseStep 2141579 = 3212369) B3212369
theorem B1904107 : Blo 1691546 1904107 := bstep (se 1 (by rfl) ⟨1428080, by rfl⟩ : syracuseStep 1904107 = 2856161) B2856161
theorem B5869079 : Blo 1691546 5869079 := bstep (se 1 (by rfl) ⟨4401809, by rfl⟩ : syracuseStep 5869079 = 8803619) B8803619
theorem B6180403 : Blo 1691546 6180403 := bstep (se 1 (by rfl) ⟨4635302, by rfl⟩ : syracuseStep 6180403 = 9270605) B9270605
theorem B14650955 : Blo 1691546 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B2854487 : Blo 1691546 2854487 := bstep (se 1 (by rfl) ⟨2140865, by rfl⟩ : syracuseStep 2854487 = 4281731) B4281731
theorem B1904215 : Blo 1691546 1904215 := bstep (se 1 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 1904215 = 2856323) B2856323
theorem B3215027 : Blo 1691546 3215027 := bstep (se 1 (by rfl) ⟨2411270, by rfl⟩ : syracuseStep 3215027 = 4822541) B4822541
theorem B2854615 : Blo 1691546 2854615 := bstep (se 1 (by rfl) ⟨2140961, by rfl⟩ : syracuseStep 2854615 = 4281923) B4281923
theorem B3215065 : Blo 1691546 3215065 := bstep (se 2 (by rfl) ⟨1205649, by rfl⟩ : syracuseStep 3215065 = 2411299) B2411299
theorem B1904395 : Blo 1691546 1904395 := bstep (se 1 (by rfl) ⟨1428296, by rfl⟩ : syracuseStep 1904395 = 2856593) B2856593
theorem B5148467 : Blo 1691546 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B5713739 : Blo 1691546 5713739 := bstep (se 1 (by rfl) ⟨4285304, by rfl⟩ : syracuseStep 5713739 = 8570609) B8570609
theorem B1904503 : Blo 1691546 1904503 := bstep (se 1 (by rfl) ⟨1428377, by rfl⟩ : syracuseStep 1904503 = 2856755) B2856755
theorem B6426499 : Blo 1691546 6426499 := bstep (se 1 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 6426499 = 9639749) B9639749
theorem B1691563 : Blo 1691546 1691563 := bstep (se 1 (by rfl) ⟨1268672, by rfl⟩ : syracuseStep 1691563 = 2537345) B2537345
theorem B1691575 : Blo 1691546 1691575 := bstep (se 1 (by rfl) ⟨1268681, by rfl⟩ : syracuseStep 1691575 = 2537363) B2537363
theorem B1691595 : Blo 1691546 1691595 := bstep (se 1 (by rfl) ⟨1268696, by rfl⟩ : syracuseStep 1691595 = 2537393) B2537393
theorem B1691607 : Blo 1691546 1691607 := bstep (se 1 (by rfl) ⟨1268705, by rfl⟩ : syracuseStep 1691607 = 2537411) B2537411
theorem B1691627 : Blo 1691546 1691627 := bstep (se 1 (by rfl) ⟨1268720, by rfl⟩ : syracuseStep 1691627 = 2537441) B2537441
theorem B1691639 : Blo 1691546 1691639 := bstep (se 1 (by rfl) ⟨1268729, by rfl⟩ : syracuseStep 1691639 = 2537459) B2537459
theorem B1691659 : Blo 1691546 1691659 := bstep (se 1 (by rfl) ⟨1268744, by rfl⟩ : syracuseStep 1691659 = 2537489) B2537489
theorem B1691671 : Blo 1691546 1691671 := bstep (se 1 (by rfl) ⟨1268753, by rfl⟩ : syracuseStep 1691671 = 2537507) B2537507
theorem B3256345 : Blo 1691546 3256345 := bstep (se 2 (by rfl) ⟨1221129, by rfl⟩ : syracuseStep 3256345 = 2442259) B2442259
theorem B1691691 : Blo 1691546 1691691 := bstep (se 1 (by rfl) ⟨1268768, by rfl⟩ : syracuseStep 1691691 = 2537537) B2537537
theorem B1904683 : Blo 1691546 1904683 := bstep (se 1 (by rfl) ⟨1428512, by rfl⟩ : syracuseStep 1904683 = 2857025) B2857025
theorem B6098989 : Blo 1691546 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B1691703 : Blo 1691546 1691703 := bstep (se 1 (by rfl) ⟨1268777, by rfl⟩ : syracuseStep 1691703 = 2537555) B2537555
theorem B1691723 : Blo 1691546 1691723 := bstep (se 1 (by rfl) ⟨1268792, by rfl⟩ : syracuseStep 1691723 = 2537585) B2537585
theorem B2142283 : Blo 1691546 2142283 := bstep (se 1 (by rfl) ⟨1606712, by rfl⟩ : syracuseStep 2142283 = 3213425) B3213425
theorem B1691735 : Blo 1691546 1691735 := bstep (se 1 (by rfl) ⟨1268801, by rfl⟩ : syracuseStep 1691735 = 2537603) B2537603
theorem B5714009 : Blo 1691546 5714009 := bstep (se 2 (by rfl) ⟨2142753, by rfl⟩ : syracuseStep 5714009 = 4285507) B4285507
theorem B1691755 : Blo 1691546 1691755 := bstep (se 1 (by rfl) ⟨1268816, by rfl⟩ : syracuseStep 1691755 = 2537633) B2537633
theorem B1691767 : Blo 1691546 1691767 := bstep (se 1 (by rfl) ⟨1268825, by rfl⟩ : syracuseStep 1691767 = 2537651) B2537651
theorem B1691787 : Blo 1691546 1691787 := bstep (se 1 (by rfl) ⟨1268840, by rfl⟩ : syracuseStep 1691787 = 2537681) B2537681
theorem B1691799 : Blo 1691546 1691799 := bstep (se 1 (by rfl) ⟨1268849, by rfl⟩ : syracuseStep 1691799 = 2537699) B2537699
theorem B1904791 : Blo 1691546 1904791 := bstep (se 1 (by rfl) ⟨1428593, by rfl⟩ : syracuseStep 1904791 = 2857187) B2857187
theorem B1691819 : Blo 1691546 1691819 := bstep (se 1 (by rfl) ⟨1268864, by rfl⟩ : syracuseStep 1691819 = 2537729) B2537729
theorem B6426803 : Blo 1691546 6426803 := bstep (se 1 (by rfl) ⟨4820102, by rfl⟩ : syracuseStep 6426803 = 9640205) B9640205
theorem B1691831 : Blo 1691546 1691831 := bstep (se 1 (by rfl) ⟨1268873, by rfl⟩ : syracuseStep 1691831 = 2537747) B2537747
theorem B1691851 : Blo 1691546 1691851 := bstep (se 1 (by rfl) ⟨1268888, by rfl⟩ : syracuseStep 1691851 = 2537777) B2537777
theorem B1691863 : Blo 1691546 1691863 := bstep (se 1 (by rfl) ⟨1268897, by rfl⟩ : syracuseStep 1691863 = 2537795) B2537795
theorem B1691883 : Blo 1691546 1691883 := bstep (se 1 (by rfl) ⟨1268912, by rfl⟩ : syracuseStep 1691883 = 2537825) B2537825
theorem B1691895 : Blo 1691546 1691895 := bstep (se 1 (by rfl) ⟨1268921, by rfl⟩ : syracuseStep 1691895 = 2537843) B2537843
theorem B1691915 : Blo 1691546 1691915 := bstep (se 1 (by rfl) ⟨1268936, by rfl⟩ : syracuseStep 1691915 = 2537873) B2537873
theorem B8573201 : Blo 1691546 8573201 := bstep (se 2 (by rfl) ⟨3214950, by rfl⟩ : syracuseStep 8573201 = 6429901) B6429901
theorem B1691927 : Blo 1691546 1691927 := bstep (se 1 (by rfl) ⟨1268945, by rfl⟩ : syracuseStep 1691927 = 2537891) B2537891
theorem B1691947 : Blo 1691546 1691947 := bstep (se 1 (by rfl) ⟨1268960, by rfl⟩ : syracuseStep 1691947 = 2537921) B2537921
theorem B1691959 : Blo 1691546 1691959 := bstep (se 1 (by rfl) ⟨1268969, by rfl⟩ : syracuseStep 1691959 = 2537939) B2537939
theorem B1806667 : Blo 1691546 1806667 := bstep (se 1 (by rfl) ⟨1355000, by rfl⟩ : syracuseStep 1806667 = 2710001) B2710001
theorem B1691979 : Blo 1691546 1691979 := bstep (se 1 (by rfl) ⟨1268984, by rfl⟩ : syracuseStep 1691979 = 2537969) B2537969
theorem B2855243 : Blo 1691546 2855243 := bstep (se 1 (by rfl) ⟨2141432, by rfl⟩ : syracuseStep 2855243 = 4282865) B4282865
theorem B1904971 : Blo 1691546 1904971 := bstep (se 1 (by rfl) ⟨1428728, by rfl⟩ : syracuseStep 1904971 = 2857457) B2857457
theorem B1691991 : Blo 1691546 1691991 := bstep (se 1 (by rfl) ⟨1268993, by rfl⟩ : syracuseStep 1691991 = 2537987) B2537987
theorem B2142551 : Blo 1691546 2142551 := bstep (se 1 (by rfl) ⟨1606913, by rfl⟩ : syracuseStep 2142551 = 3213827) B3213827
theorem B1692011 : Blo 1691546 1692011 := bstep (se 1 (by rfl) ⟨1269008, by rfl⟩ : syracuseStep 1692011 = 2538017) B2538017
theorem B3256691 : Blo 1691546 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B1692023 : Blo 1691546 1692023 := bstep (se 1 (by rfl) ⟨1269017, by rfl⟩ : syracuseStep 1692023 = 2538035) B2538035
theorem B1692043 : Blo 1691546 1692043 := bstep (se 1 (by rfl) ⟨1269032, by rfl⟩ : syracuseStep 1692043 = 2538065) B2538065
theorem B1692055 : Blo 1691546 1692055 := bstep (se 1 (by rfl) ⟨1269041, by rfl⟩ : syracuseStep 1692055 = 2538083) B2538083
theorem B1692075 : Blo 1691546 1692075 := bstep (se 1 (by rfl) ⟨1269056, by rfl⟩ : syracuseStep 1692075 = 2538113) B2538113
theorem B8573363 : Blo 1691546 8573363 := bstep (se 1 (by rfl) ⟨6430022, by rfl⟩ : syracuseStep 8573363 = 12860045) B12860045
theorem B1692087 : Blo 1691546 1692087 := bstep (se 1 (by rfl) ⟨1269065, by rfl⟩ : syracuseStep 1692087 = 2538131) B2538131
theorem B1905079 : Blo 1691546 1905079 := bstep (se 1 (by rfl) ⟨1428809, by rfl⟩ : syracuseStep 1905079 = 2857619) B2857619
theorem B2855371 : Blo 1691546 2855371 := bstep (se 1 (by rfl) ⟨2141528, by rfl⟩ : syracuseStep 2855371 = 4283057) B4283057
theorem B1692107 : Blo 1691546 1692107 := bstep (se 1 (by rfl) ⟨1269080, by rfl⟩ : syracuseStep 1692107 = 2538161) B2538161
theorem B1692119 : Blo 1691546 1692119 := bstep (se 1 (by rfl) ⟨1269089, by rfl⟩ : syracuseStep 1692119 = 2538179) B2538179
theorem B1692139 : Blo 1691546 1692139 := bstep (se 1 (by rfl) ⟨1269104, by rfl⟩ : syracuseStep 1692139 = 2538209) B2538209
theorem B1692151 : Blo 1691546 1692151 := bstep (se 1 (by rfl) ⟨1269113, by rfl⟩ : syracuseStep 1692151 = 2538227) B2538227
theorem B1692171 : Blo 1691546 1692171 := bstep (se 1 (by rfl) ⟨1269128, by rfl⟩ : syracuseStep 1692171 = 2538257) B2538257
theorem B1692183 : Blo 1691546 1692183 := bstep (se 1 (by rfl) ⟨1269137, by rfl⟩ : syracuseStep 1692183 = 2538275) B2538275
theorem B1692203 : Blo 1691546 1692203 := bstep (se 1 (by rfl) ⟨1269152, by rfl⟩ : syracuseStep 1692203 = 2538305) B2538305
theorem B1692215 : Blo 1691546 1692215 := bstep (se 1 (by rfl) ⟨1269161, by rfl⟩ : syracuseStep 1692215 = 2538323) B2538323
theorem B9146945 : Blo 1691546 9146945 := bstep (se 2 (by rfl) ⟨3430104, by rfl⟩ : syracuseStep 9146945 = 6860209) B6860209
theorem B1692235 : Blo 1691546 1692235 := bstep (se 1 (by rfl) ⟨1269176, by rfl⟩ : syracuseStep 1692235 = 2538353) B2538353
theorem B1692247 : Blo 1691546 1692247 := bstep (se 1 (by rfl) ⟨1269185, by rfl⟩ : syracuseStep 1692247 = 2538371) B2538371
theorem B2855513 : Blo 1691546 2855513 := bstep (se 2 (by rfl) ⟨1070817, by rfl⟩ : syracuseStep 2855513 = 2141635) B2141635
theorem B10039909 : Blo 1691546 10039909 := bstep (se 4 (by rfl) ⟨941241, by rfl⟩ : syracuseStep 10039909 = 1882483) B1882483
theorem B1692267 : Blo 1691546 1692267 := bstep (se 1 (by rfl) ⟨1269200, by rfl⟩ : syracuseStep 1692267 = 2538401) B2538401
theorem B1692279 : Blo 1691546 1692279 := bstep (se 1 (by rfl) ⟨1269209, by rfl⟩ : syracuseStep 1692279 = 2538419) B2538419
theorem B1692299 : Blo 1691546 1692299 := bstep (se 1 (by rfl) ⟨1269224, by rfl⟩ : syracuseStep 1692299 = 2538449) B2538449
theorem B1692311 : Blo 1691546 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B1692331 : Blo 1691546 1692331 := bstep (se 1 (by rfl) ⟨1269248, by rfl⟩ : syracuseStep 1692331 = 2538497) B2538497
theorem B1692343 : Blo 1691546 1692343 := bstep (se 1 (by rfl) ⟨1269257, by rfl⟩ : syracuseStep 1692343 = 2538515) B2538515
theorem B4821697 : Blo 1691546 4821697 := bstep (se 2 (by rfl) ⟨1808136, by rfl⟩ : syracuseStep 4821697 = 3616273) B3616273
theorem B1692363 : Blo 1691546 1692363 := bstep (se 1 (by rfl) ⟨1269272, by rfl⟩ : syracuseStep 1692363 = 2538545) B2538545
theorem B1692375 : Blo 1691546 1692375 := bstep (se 1 (by rfl) ⟨1269281, by rfl⟩ : syracuseStep 1692375 = 2538563) B2538563
theorem B2855641 : Blo 1691546 2855641 := bstep (se 2 (by rfl) ⟨1070865, by rfl⟩ : syracuseStep 2855641 = 2141731) B2141731
theorem B1692395 : Blo 1691546 1692395 := bstep (se 1 (by rfl) ⟨1269296, by rfl⟩ : syracuseStep 1692395 = 2538593) B2538593
theorem B1692407 : Blo 1691546 1692407 := bstep (se 1 (by rfl) ⟨1269305, by rfl⟩ : syracuseStep 1692407 = 2538611) B2538611
theorem B1692427 : Blo 1691546 1692427 := bstep (se 1 (by rfl) ⟨1269320, by rfl⟩ : syracuseStep 1692427 = 2538641) B2538641
theorem B1692439 : Blo 1691546 1692439 := bstep (se 1 (by rfl) ⟨1269329, by rfl⟩ : syracuseStep 1692439 = 2538659) B2538659
theorem B5714711 : Blo 1691546 5714711 := bstep (se 1 (by rfl) ⟨4286033, by rfl⟩ : syracuseStep 5714711 = 8572067) B8572067
theorem B1692459 : Blo 1691546 1692459 := bstep (se 1 (by rfl) ⟨1269344, by rfl⟩ : syracuseStep 1692459 = 2538689) B2538689
theorem B1692471 : Blo 1691546 1692471 := bstep (se 1 (by rfl) ⟨1269353, by rfl⟩ : syracuseStep 1692471 = 2538707) B2538707
theorem B6427457 : Blo 1691546 6427457 := bstep (se 2 (by rfl) ⟨2410296, by rfl⟩ : syracuseStep 6427457 = 4820593) B4820593
theorem B3806027 : Blo 1691546 3806027 := bstep (se 1 (by rfl) ⟨2854520, by rfl⟩ : syracuseStep 3806027 = 5709041) B5709041
theorem B1692491 : Blo 1691546 1692491 := bstep (se 1 (by rfl) ⟨1269368, by rfl⟩ : syracuseStep 1692491 = 2538737) B2538737
theorem B1692503 : Blo 1691546 1692503 := bstep (se 1 (by rfl) ⟨1269377, by rfl⟩ : syracuseStep 1692503 = 2538755) B2538755
theorem B1692523 : Blo 1691546 1692523 := bstep (se 1 (by rfl) ⟨1269392, by rfl⟩ : syracuseStep 1692523 = 2538785) B2538785
theorem B1692535 : Blo 1691546 1692535 := bstep (se 1 (by rfl) ⟨1269401, by rfl⟩ : syracuseStep 1692535 = 2538803) B2538803
theorem B3806081 : Blo 1691546 3806081 := bstep (se 2 (by rfl) ⟨1427280, by rfl⟩ : syracuseStep 3806081 = 2854561) B2854561
theorem B1692555 : Blo 1691546 1692555 := bstep (se 1 (by rfl) ⟨1269416, by rfl⟩ : syracuseStep 1692555 = 2538833) B2538833
theorem B1692567 : Blo 1691546 1692567 := bstep (se 1 (by rfl) ⟨1269425, by rfl⟩ : syracuseStep 1692567 = 2538851) B2538851
theorem B7230359 : Blo 1691546 7230359 := bstep (se 1 (by rfl) ⟨5422769, by rfl⟩ : syracuseStep 7230359 = 10845539) B10845539
theorem B1692587 : Blo 1691546 1692587 := bstep (se 1 (by rfl) ⟨1269440, by rfl⟩ : syracuseStep 1692587 = 2538881) B2538881
theorem B1692599 : Blo 1691546 1692599 := bstep (se 1 (by rfl) ⟨1269449, by rfl⟩ : syracuseStep 1692599 = 2538899) B2538899
theorem B1692619 : Blo 1691546 1692619 := bstep (se 1 (by rfl) ⟨1269464, by rfl⟩ : syracuseStep 1692619 = 2538929) B2538929
theorem B4068299 : Blo 1691546 4068299 := bstep (se 1 (by rfl) ⟨3051224, by rfl⟩ : syracuseStep 4068299 = 6102449) B6102449
theorem B1692631 : Blo 1691546 1692631 := bstep (se 1 (by rfl) ⟨1269473, by rfl⟩ : syracuseStep 1692631 = 2538947) B2538947
theorem B1692651 : Blo 1691546 1692651 := bstep (se 1 (by rfl) ⟨1269488, by rfl⟩ : syracuseStep 1692651 = 2538977) B2538977
theorem B1692663 : Blo 1691546 1692663 := bstep (se 1 (by rfl) ⟨1269497, by rfl⟩ : syracuseStep 1692663 = 2538995) B2538995
theorem B1692683 : Blo 1691546 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B12194833 : Blo 1691546 12194833 := bstep (se 2 (by rfl) ⟨4573062, by rfl⟩ : syracuseStep 12194833 = 9146125) B9146125
theorem B1692695 : Blo 1691546 1692695 := bstep (se 1 (by rfl) ⟨1269521, by rfl⟩ : syracuseStep 1692695 = 2539043) B2539043
theorem B2143255 : Blo 1691546 2143255 := bstep (se 1 (by rfl) ⟨1607441, by rfl⟩ : syracuseStep 2143255 = 3214883) B3214883
theorem B222467107 : Blo 1691546 222467107 := bstep (se 1 (by rfl) ⟨166850330, by rfl⟩ : syracuseStep 222467107 = 333700661) B333700661
theorem B1692715 : Blo 1691546 1692715 := bstep (se 1 (by rfl) ⟨1269536, by rfl⟩ : syracuseStep 1692715 = 2539073) B2539073
theorem B1692727 : Blo 1691546 1692727 := bstep (se 1 (by rfl) ⟨1269545, by rfl⟩ : syracuseStep 1692727 = 2539091) B2539091
theorem B1692747 : Blo 1691546 1692747 := bstep (se 1 (by rfl) ⟨1269560, by rfl⟩ : syracuseStep 1692747 = 2539121) B2539121
theorem B1692759 : Blo 1691546 1692759 := bstep (se 1 (by rfl) ⟨1269569, by rfl⟩ : syracuseStep 1692759 = 2539139) B2539139
theorem B3806297 : Blo 1691546 3806297 := bstep (se 2 (by rfl) ⟨1427361, by rfl⟩ : syracuseStep 3806297 = 2854723) B2854723
theorem B4576349 : Blo 1691546 4576349 := bstep (se 3 (by rfl) ⟨858065, by rfl⟩ : syracuseStep 4576349 = 1716131) B1716131
theorem B1692779 : Blo 1691546 1692779 := bstep (se 1 (by rfl) ⟨1269584, by rfl⟩ : syracuseStep 1692779 = 2539169) B2539169
theorem B1692791 : Blo 1691546 1692791 := bstep (se 1 (by rfl) ⟨1269593, by rfl⟩ : syracuseStep 1692791 = 2539187) B2539187
theorem B1692811 : Blo 1691546 1692811 := bstep (se 1 (by rfl) ⟨1269608, by rfl⟩ : syracuseStep 1692811 = 2539217) B2539217
theorem B8565911 : Blo 1691546 8565911 := bstep (se 1 (by rfl) ⟨6424433, by rfl⟩ : syracuseStep 8565911 = 12848867) B12848867
theorem B1692823 : Blo 1691546 1692823 := bstep (se 1 (by rfl) ⟨1269617, by rfl⟩ : syracuseStep 1692823 = 2539235) B2539235
theorem B1692843 : Blo 1691546 1692843 := bstep (se 1 (by rfl) ⟨1269632, by rfl⟩ : syracuseStep 1692843 = 2539265) B2539265
theorem B3806387 : Blo 1691546 3806387 := bstep (se 1 (by rfl) ⟨2854790, by rfl⟩ : syracuseStep 3806387 = 5709581) B5709581
theorem B1692855 : Blo 1691546 1692855 := bstep (se 1 (by rfl) ⟨1269641, by rfl⟩ : syracuseStep 1692855 = 2539283) B2539283
theorem B7230667 : Blo 1691546 7230667 := bstep (se 1 (by rfl) ⟨5423000, by rfl⟩ : syracuseStep 7230667 = 10846001) B10846001
theorem B1692875 : Blo 1691546 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B3806423 : Blo 1691546 3806423 := bstep (se 1 (by rfl) ⟨2854817, by rfl⟩ : syracuseStep 3806423 = 5709635) B5709635
theorem B1692887 : Blo 1691546 1692887 := bstep (se 1 (by rfl) ⟨1269665, by rfl⟩ : syracuseStep 1692887 = 2539331) B2539331
theorem B1692907 : Blo 1691546 1692907 := bstep (se 1 (by rfl) ⟨1269680, by rfl⟩ : syracuseStep 1692907 = 2539361) B2539361
theorem B1807607 : Blo 1691546 1807607 := bstep (se 1 (by rfl) ⟨1355705, by rfl⟩ : syracuseStep 1807607 = 2711411) B2711411
theorem B1692919 : Blo 1691546 1692919 := bstep (se 1 (by rfl) ⟨1269689, by rfl⟩ : syracuseStep 1692919 = 2539379) B2539379
theorem B1692939 : Blo 1691546 1692939 := bstep (se 1 (by rfl) ⟨1269704, by rfl⟩ : syracuseStep 1692939 = 2539409) B2539409
theorem B2856215 : Blo 1691546 2856215 := bstep (se 1 (by rfl) ⟨2142161, by rfl⟩ : syracuseStep 2856215 = 4284323) B4284323
theorem B1692951 : Blo 1691546 1692951 := bstep (se 1 (by rfl) ⟨1269713, by rfl⟩ : syracuseStep 1692951 = 2539427) B2539427
theorem B1692971 : Blo 1691546 1692971 := bstep (se 1 (by rfl) ⟨1269728, by rfl⟩ : syracuseStep 1692971 = 2539457) B2539457
theorem B16266541 : Blo 1691546 16266541 := bstep (se 3 (by rfl) ⟨3049976, by rfl⟩ : syracuseStep 16266541 = 6099953) B6099953
theorem B5715251 : Blo 1691546 5715251 := bstep (se 1 (by rfl) ⟨4286438, by rfl⟩ : syracuseStep 5715251 = 8572877) B8572877
theorem B1692983 : Blo 1691546 1692983 := bstep (se 1 (by rfl) ⟨1269737, by rfl⟩ : syracuseStep 1692983 = 2539475) B2539475
theorem B1693003 : Blo 1691546 1693003 := bstep (se 1 (by rfl) ⟨1269752, by rfl⟩ : syracuseStep 1693003 = 2539505) B2539505
theorem B1693015 : Blo 1691546 1693015 := bstep (se 1 (by rfl) ⟨1269761, by rfl⟩ : syracuseStep 1693015 = 2539523) B2539523
theorem B16495973 : Blo 1691546 16495973 := bstep (se 4 (by rfl) ⟨1546497, by rfl⟩ : syracuseStep 16495973 = 3092995) B3092995
theorem B1693035 : Blo 1691546 1693035 := bstep (se 1 (by rfl) ⟨1269776, by rfl⟩ : syracuseStep 1693035 = 2539553) B2539553
theorem B1693047 : Blo 1691546 1693047 := bstep (se 1 (by rfl) ⟨1269785, by rfl⟩ : syracuseStep 1693047 = 2539571) B2539571
theorem B3806603 : Blo 1691546 3806603 := bstep (se 1 (by rfl) ⟨2854952, by rfl⟩ : syracuseStep 3806603 = 5709905) B5709905
theorem B1693067 : Blo 1691546 1693067 := bstep (se 1 (by rfl) ⟨1269800, by rfl⟩ : syracuseStep 1693067 = 2539601) B2539601
theorem B2856343 : Blo 1691546 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B1693079 : Blo 1691546 1693079 := bstep (se 1 (by rfl) ⟨1269809, by rfl⟩ : syracuseStep 1693079 = 2539619) B2539619
theorem B1693099 : Blo 1691546 1693099 := bstep (se 1 (by rfl) ⟨1269824, by rfl⟩ : syracuseStep 1693099 = 2539649) B2539649
theorem B1693111 : Blo 1691546 1693111 := bstep (se 1 (by rfl) ⟨1269833, by rfl⟩ : syracuseStep 1693111 = 2539667) B2539667
theorem B3806657 : Blo 1691546 3806657 := bstep (se 2 (by rfl) ⟨1427496, by rfl⟩ : syracuseStep 3806657 = 2854993) B2854993
theorem B1693131 : Blo 1691546 1693131 := bstep (se 1 (by rfl) ⟨1269848, by rfl⟩ : syracuseStep 1693131 = 2539697) B2539697
theorem B1693143 : Blo 1691546 1693143 := bstep (se 1 (by rfl) ⟨1269857, by rfl⟩ : syracuseStep 1693143 = 2539715) B2539715
theorem B22935001 : Blo 1691546 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B7230941 : Blo 1691546 7230941 := bstep (se 3 (by rfl) ⟨1355801, by rfl⟩ : syracuseStep 7230941 = 2711603) B2711603
theorem B1693163 : Blo 1691546 1693163 := bstep (se 1 (by rfl) ⟨1269872, by rfl⟩ : syracuseStep 1693163 = 2539745) B2539745
theorem B1693175 : Blo 1691546 1693175 := bstep (se 1 (by rfl) ⟨1269881, by rfl⟩ : syracuseStep 1693175 = 2539763) B2539763
theorem B1693195 : Blo 1691546 1693195 := bstep (se 1 (by rfl) ⟨1269896, by rfl⟩ : syracuseStep 1693195 = 2539793) B2539793
theorem B3429911 : Blo 1691546 3429911 := bstep (se 1 (by rfl) ⟨2572433, by rfl⟩ : syracuseStep 3429911 = 5144867) B5144867
theorem B1693207 : Blo 1691546 1693207 := bstep (se 1 (by rfl) ⟨1269905, by rfl⟩ : syracuseStep 1693207 = 2539811) B2539811
theorem B1693227 : Blo 1691546 1693227 := bstep (se 1 (by rfl) ⟨1269920, by rfl⟩ : syracuseStep 1693227 = 2539841) B2539841
theorem B1693239 : Blo 1691546 1693239 := bstep (se 1 (by rfl) ⟨1269929, by rfl⟩ : syracuseStep 1693239 = 2539859) B2539859
theorem B5715521 : Blo 1691546 5715521 := bstep (se 2 (by rfl) ⟨2143320, by rfl⟩ : syracuseStep 5715521 = 4286641) B4286641
theorem B1693259 : Blo 1691546 1693259 := bstep (se 1 (by rfl) ⟨1269944, by rfl⟩ : syracuseStep 1693259 = 2539889) B2539889
theorem B1693271 : Blo 1691546 1693271 := bstep (se 1 (by rfl) ⟨1269953, by rfl⟩ : syracuseStep 1693271 = 2539907) B2539907
theorem B1693291 : Blo 1691546 1693291 := bstep (se 1 (by rfl) ⟨1269968, by rfl⟩ : syracuseStep 1693291 = 2539937) B2539937
theorem B1693303 : Blo 1691546 1693303 := bstep (se 1 (by rfl) ⟨1269977, by rfl⟩ : syracuseStep 1693303 = 2539955) B2539955
theorem B1693323 : Blo 1691546 1693323 := bstep (se 1 (by rfl) ⟨1269992, by rfl⟩ : syracuseStep 1693323 = 2539985) B2539985
theorem B1693335 : Blo 1691546 1693335 := bstep (se 1 (by rfl) ⟨1270001, by rfl⟩ : syracuseStep 1693335 = 2540003) B2540003
theorem B3806873 : Blo 1691546 3806873 := bstep (se 2 (by rfl) ⟨1427577, by rfl⟩ : syracuseStep 3806873 = 2855155) B2855155
theorem B1693355 : Blo 1691546 1693355 := bstep (se 1 (by rfl) ⟨1270016, by rfl⟩ : syracuseStep 1693355 = 2540033) B2540033
theorem B1693367 : Blo 1691546 1693367 := bstep (se 1 (by rfl) ⟨1270025, by rfl⟩ : syracuseStep 1693367 = 2540051) B2540051
theorem B1693387 : Blo 1691546 1693387 := bstep (se 1 (by rfl) ⟨1270040, by rfl⟩ : syracuseStep 1693387 = 2540081) B2540081
theorem B1693399 : Blo 1691546 1693399 := bstep (se 1 (by rfl) ⟨1270049, by rfl⟩ : syracuseStep 1693399 = 2540099) B2540099
theorem B1693419 : Blo 1691546 1693419 := bstep (se 1 (by rfl) ⟨1270064, by rfl⟩ : syracuseStep 1693419 = 2540129) B2540129
theorem B46970609 : Blo 1691546 46970609 := bstep (se 2 (by rfl) ⟨17613978, by rfl⟩ : syracuseStep 46970609 = 35227957) B35227957
theorem B3806963 : Blo 1691546 3806963 := bstep (se 1 (by rfl) ⟨2855222, by rfl⟩ : syracuseStep 3806963 = 5710445) B5710445
theorem B1693431 : Blo 1691546 1693431 := bstep (se 1 (by rfl) ⟨1270073, by rfl⟩ : syracuseStep 1693431 = 2540147) B2540147
theorem B1693451 : Blo 1691546 1693451 := bstep (se 1 (by rfl) ⟨1270088, by rfl⟩ : syracuseStep 1693451 = 2540177) B2540177
theorem B3806999 : Blo 1691546 3806999 := bstep (se 1 (by rfl) ⟨2855249, by rfl⟩ : syracuseStep 3806999 = 5710499) B5710499
theorem B1693463 : Blo 1691546 1693463 := bstep (se 1 (by rfl) ⟨1270097, by rfl⟩ : syracuseStep 1693463 = 2540195) B2540195
theorem B1693483 : Blo 1691546 1693483 := bstep (se 1 (by rfl) ⟨1270112, by rfl⟩ : syracuseStep 1693483 = 2540225) B2540225
theorem B1693495 : Blo 1691546 1693495 := bstep (se 1 (by rfl) ⟨1270121, by rfl⟩ : syracuseStep 1693495 = 2540243) B2540243
theorem B1693515 : Blo 1691546 1693515 := bstep (se 1 (by rfl) ⟨1270136, by rfl⟩ : syracuseStep 1693515 = 2540273) B2540273
theorem B1693527 : Blo 1691546 1693527 := bstep (se 1 (by rfl) ⟨1270145, by rfl⟩ : syracuseStep 1693527 = 2540291) B2540291
theorem B32544611 : Blo 1691546 32544611 := bstep (se 1 (by rfl) ⟨24408458, by rfl⟩ : syracuseStep 32544611 = 48816917) B48816917
theorem B5494679 : Blo 1691546 5494679 := bstep (se 1 (by rfl) ⟨4121009, by rfl⟩ : syracuseStep 5494679 = 8242019) B8242019
theorem B5420951 : Blo 1691546 5420951 := bstep (se 1 (by rfl) ⟨4065713, by rfl⟩ : syracuseStep 5420951 = 8131427) B8131427
theorem B2537369 : Blo 1691546 2537369 := bstep (se 2 (by rfl) ⟨951513, by rfl⟩ : syracuseStep 2537369 = 1903027) B1903027
theorem B3807179 : Blo 1691546 3807179 := bstep (se 1 (by rfl) ⟨2855384, by rfl⟩ : syracuseStep 3807179 = 5710769) B5710769
theorem B3807233 : Blo 1691546 3807233 := bstep (se 2 (by rfl) ⟨1427712, by rfl⟩ : syracuseStep 3807233 = 2855425) B2855425
theorem B2537483 : Blo 1691546 2537483 := bstep (se 1 (by rfl) ⟨1903112, by rfl⟩ : syracuseStep 2537483 = 3806225) B3806225
theorem B2856971 : Blo 1691546 2856971 := bstep (se 1 (by rfl) ⟨2142728, by rfl⟩ : syracuseStep 2856971 = 4285457) B4285457
theorem B2537495 : Blo 1691546 2537495 := bstep (se 1 (by rfl) ⟨1903121, by rfl⟩ : syracuseStep 2537495 = 3806243) B3806243
theorem B6428717 : Blo 1691546 6428717 := bstep (se 3 (by rfl) ⟨1205384, by rfl⟩ : syracuseStep 6428717 = 2410769) B2410769
theorem B6428747 : Blo 1691546 6428747 := bstep (se 1 (by rfl) ⟨4821560, by rfl⟩ : syracuseStep 6428747 = 9643121) B9643121
theorem B2537561 : Blo 1691546 2537561 := bstep (se 2 (by rfl) ⟨951585, by rfl⟩ : syracuseStep 2537561 = 1903171) B1903171
theorem B2857099 : Blo 1691546 2857099 := bstep (se 1 (by rfl) ⟨2142824, by rfl⟩ : syracuseStep 2857099 = 4285649) B4285649
theorem B39082135 : Blo 1691546 39082135 := bstep (se 1 (by rfl) ⟨29311601, by rfl⟩ : syracuseStep 39082135 = 58623203) B58623203
theorem B2537675 : Blo 1691546 2537675 := bstep (se 1 (by rfl) ⟨1903256, by rfl⟩ : syracuseStep 2537675 = 3806513) B3806513
theorem B4282571 : Blo 1691546 4282571 := bstep (se 1 (by rfl) ⟨3211928, by rfl⟩ : syracuseStep 4282571 = 6423857) B6423857
theorem B2537687 : Blo 1691546 2537687 := bstep (se 1 (by rfl) ⟨1903265, by rfl⟩ : syracuseStep 2537687 = 3806531) B3806531
theorem B3807449 : Blo 1691546 3807449 := bstep (se 2 (by rfl) ⟨1427793, by rfl⟩ : syracuseStep 3807449 = 2855587) B2855587
theorem B2537753 : Blo 1691546 2537753 := bstep (se 2 (by rfl) ⟨951657, by rfl⟩ : syracuseStep 2537753 = 1903315) B1903315
theorem B2857241 : Blo 1691546 2857241 := bstep (se 2 (by rfl) ⟨1071465, by rfl⟩ : syracuseStep 2857241 = 2142931) B2142931
theorem B3807539 : Blo 1691546 3807539 := bstep (se 1 (by rfl) ⟨2855654, by rfl⟩ : syracuseStep 3807539 = 5711309) B5711309
theorem B14457163 : Blo 1691546 14457163 := bstep (se 1 (by rfl) ⟨10842872, by rfl⟩ : syracuseStep 14457163 = 21685745) B21685745
theorem B3807575 : Blo 1691546 3807575 := bstep (se 1 (by rfl) ⟨2855681, by rfl⟩ : syracuseStep 3807575 = 5711363) B5711363
theorem B2537867 : Blo 1691546 2537867 := bstep (se 1 (by rfl) ⟨1903400, by rfl⟩ : syracuseStep 2537867 = 3806801) B3806801
theorem B2537879 : Blo 1691546 2537879 := bstep (se 1 (by rfl) ⟨1903409, by rfl⟩ : syracuseStep 2537879 = 3806819) B3806819
theorem B2857369 : Blo 1691546 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B2537945 : Blo 1691546 2537945 := bstep (se 2 (by rfl) ⟨951729, by rfl⟩ : syracuseStep 2537945 = 1903459) B1903459
theorem B2710027 : Blo 1691546 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B3807755 : Blo 1691546 3807755 := bstep (se 1 (by rfl) ⟨2855816, by rfl⟩ : syracuseStep 3807755 = 5711633) B5711633
theorem B20593187 : Blo 1691546 20593187 := bstep (se 1 (by rfl) ⟨15444890, by rfl⟩ : syracuseStep 20593187 = 30889781) B30889781
theorem B3807809 : Blo 1691546 3807809 := bstep (se 2 (by rfl) ⟨1427928, by rfl⟩ : syracuseStep 3807809 = 2855857) B2855857
theorem B2538059 : Blo 1691546 2538059 := bstep (se 1 (by rfl) ⟨1903544, by rfl⟩ : syracuseStep 2538059 = 3807089) B3807089
theorem B2710103 : Blo 1691546 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B2538071 : Blo 1691546 2538071 := bstep (se 1 (by rfl) ⟨1903553, by rfl⟩ : syracuseStep 2538071 = 3807107) B3807107
theorem B14457437 : Blo 1691546 14457437 := bstep (se 3 (by rfl) ⟨2710769, by rfl⟩ : syracuseStep 14457437 = 5421539) B5421539
theorem B9149021 : Blo 1691546 9149021 := bstep (se 3 (by rfl) ⟨1715441, by rfl⟩ : syracuseStep 9149021 = 3430883) B3430883
theorem B24394391 : Blo 1691546 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B2538137 : Blo 1691546 2538137 := bstep (se 2 (by rfl) ⟨951801, by rfl⟩ : syracuseStep 2538137 = 1903603) B1903603
theorem B6429401 : Blo 1691546 6429401 := bstep (se 2 (by rfl) ⟨2411025, by rfl⟩ : syracuseStep 6429401 = 4822051) B4822051
theorem B2538251 : Blo 1691546 2538251 := bstep (se 1 (by rfl) ⟨1903688, by rfl⟩ : syracuseStep 2538251 = 3807377) B3807377
theorem B7232273 : Blo 1691546 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B2538263 : Blo 1691546 2538263 := bstep (se 1 (by rfl) ⟨1903697, by rfl⟩ : syracuseStep 2538263 = 3807395) B3807395
theorem B3808025 : Blo 1691546 3808025 := bstep (se 2 (by rfl) ⟨1428009, by rfl⟩ : syracuseStep 3808025 = 2856019) B2856019
theorem B15448897 : Blo 1691546 15448897 := bstep (se 2 (by rfl) ⟨5793336, by rfl⟩ : syracuseStep 15448897 = 11586673) B11586673
theorem B2538329 : Blo 1691546 2538329 := bstep (se 2 (by rfl) ⟨951873, by rfl⟩ : syracuseStep 2538329 = 1903747) B1903747
theorem B3808115 : Blo 1691546 3808115 := bstep (se 1 (by rfl) ⟨2856086, by rfl⟩ : syracuseStep 3808115 = 5712173) B5712173
theorem B3808151 : Blo 1691546 3808151 := bstep (se 1 (by rfl) ⟨2856113, by rfl⟩ : syracuseStep 3808151 = 5712227) B5712227
theorem B2538443 : Blo 1691546 2538443 := bstep (se 1 (by rfl) ⟨1903832, by rfl⟩ : syracuseStep 2538443 = 3807665) B3807665
theorem B2538455 : Blo 1691546 2538455 := bstep (se 1 (by rfl) ⟨1903841, by rfl⟩ : syracuseStep 2538455 = 3807683) B3807683
theorem B6429719 : Blo 1691546 6429719 := bstep (se 1 (by rfl) ⟨4822289, by rfl⟩ : syracuseStep 6429719 = 9644579) B9644579
theorem B2538521 : Blo 1691546 2538521 := bstep (se 2 (by rfl) ⟨951945, by rfl⟩ : syracuseStep 2538521 = 1903891) B1903891
theorem B12852269 : Blo 1691546 12852269 := bstep (se 3 (by rfl) ⟨2409800, by rfl⟩ : syracuseStep 12852269 = 4819601) B4819601
theorem B3808331 : Blo 1691546 3808331 := bstep (se 1 (by rfl) ⟨2856248, by rfl⟩ : syracuseStep 3808331 = 5712497) B5712497
theorem B3808385 : Blo 1691546 3808385 := bstep (se 2 (by rfl) ⟨1428144, by rfl⟩ : syracuseStep 3808385 = 2856289) B2856289
theorem B2538635 : Blo 1691546 2538635 := bstep (se 1 (by rfl) ⟨1903976, by rfl⟩ : syracuseStep 2538635 = 3807953) B3807953
theorem B4283543 : Blo 1691546 4283543 := bstep (se 1 (by rfl) ⟨3212657, by rfl⟩ : syracuseStep 4283543 = 6425315) B6425315
theorem B2538647 : Blo 1691546 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B12197081 : Blo 1691546 12197081 := bstep (se 2 (by rfl) ⟨4573905, by rfl⟩ : syracuseStep 12197081 = 9147811) B9147811
theorem B2538713 : Blo 1691546 2538713 := bstep (se 2 (by rfl) ⟨952017, by rfl⟩ : syracuseStep 2538713 = 1904035) B1904035
theorem B2538827 : Blo 1691546 2538827 := bstep (se 1 (by rfl) ⟨1904120, by rfl⟩ : syracuseStep 2538827 = 3808241) B3808241
theorem B10845515 : Blo 1691546 10845515 := bstep (se 1 (by rfl) ⟨8134136, by rfl⟩ : syracuseStep 10845515 = 16268273) B16268273
theorem B2538839 : Blo 1691546 2538839 := bstep (se 1 (by rfl) ⟨1904129, by rfl⟩ : syracuseStep 2538839 = 3808259) B3808259
theorem B3808601 : Blo 1691546 3808601 := bstep (se 2 (by rfl) ⟨1428225, by rfl⟩ : syracuseStep 3808601 = 2856451) B2856451
theorem B5709149 : Blo 1691546 5709149 := bstep (se 3 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 5709149 = 2140931) B2140931
theorem B2538905 : Blo 1691546 2538905 := bstep (se 2 (by rfl) ⟨952089, by rfl⟩ : syracuseStep 2538905 = 1904179) B1904179
theorem B3808691 : Blo 1691546 3808691 := bstep (se 1 (by rfl) ⟨2856518, by rfl⟩ : syracuseStep 3808691 = 5713037) B5713037
theorem B3808727 : Blo 1691546 3808727 := bstep (se 1 (by rfl) ⟨2856545, by rfl⟩ : syracuseStep 3808727 = 5713091) B5713091
theorem B7331293 : Blo 1691546 7331293 := bstep (se 3 (by rfl) ⟨1374617, by rfl⟩ : syracuseStep 7331293 = 2749235) B2749235
theorem B2539019 : Blo 1691546 2539019 := bstep (se 1 (by rfl) ⟨1904264, by rfl⟩ : syracuseStep 2539019 = 3808529) B3808529
theorem B2539031 : Blo 1691546 2539031 := bstep (se 1 (by rfl) ⟨1904273, by rfl⟩ : syracuseStep 2539031 = 3808547) B3808547
theorem B12205613 : Blo 1691546 12205613 := bstep (se 3 (by rfl) ⟨2288552, by rfl⟩ : syracuseStep 12205613 = 4577105) B4577105
theorem B2539097 : Blo 1691546 2539097 := bstep (se 2 (by rfl) ⟨952161, by rfl⟩ : syracuseStep 2539097 = 1904323) B1904323
theorem B14458499 : Blo 1691546 14458499 := bstep (se 1 (by rfl) ⟨10843874, by rfl⟩ : syracuseStep 14458499 = 21687749) B21687749
theorem B3808907 : Blo 1691546 3808907 := bstep (se 1 (by rfl) ⟨2856680, by rfl⟩ : syracuseStep 3808907 = 5713361) B5713361
theorem B3808961 : Blo 1691546 3808961 := bstep (se 2 (by rfl) ⟨1428360, by rfl⟩ : syracuseStep 3808961 = 2856721) B2856721
theorem B2539211 : Blo 1691546 2539211 := bstep (se 1 (by rfl) ⟨1904408, by rfl⟩ : syracuseStep 2539211 = 3808817) B3808817
theorem B2539223 : Blo 1691546 2539223 := bstep (se 1 (by rfl) ⟨1904417, by rfl⟩ : syracuseStep 2539223 = 3808835) B3808835
theorem B2539289 : Blo 1691546 2539289 := bstep (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) B1904467
theorem B8134445 : Blo 1691546 8134445 := bstep (se 3 (by rfl) ⟨1525208, by rfl⟩ : syracuseStep 8134445 = 3050417) B3050417
theorem B4284211 : Blo 1691546 4284211 := bstep (se 1 (by rfl) ⟨3213158, by rfl⟩ : syracuseStep 4284211 = 6426317) B6426317
theorem B2539403 : Blo 1691546 2539403 := bstep (se 1 (by rfl) ⟨1904552, by rfl⟩ : syracuseStep 2539403 = 3809105) B3809105
theorem B2539415 : Blo 1691546 2539415 := bstep (se 1 (by rfl) ⟨1904561, by rfl⟩ : syracuseStep 2539415 = 3809123) B3809123
theorem B3809177 : Blo 1691546 3809177 := bstep (se 2 (by rfl) ⟨1428441, by rfl⟩ : syracuseStep 3809177 = 2856883) B2856883
theorem B4284353 : Blo 1691546 4284353 := bstep (se 2 (by rfl) ⟨1606632, by rfl⟩ : syracuseStep 4284353 = 3213265) B3213265
theorem B2711513 : Blo 1691546 2711513 := bstep (se 2 (by rfl) ⟨1016817, by rfl⟩ : syracuseStep 2711513 = 2033635) B2033635
theorem B2539481 : Blo 1691546 2539481 := bstep (se 2 (by rfl) ⟨952305, by rfl⟩ : syracuseStep 2539481 = 1904611) B1904611
theorem B3809267 : Blo 1691546 3809267 := bstep (se 1 (by rfl) ⟨2856950, by rfl⟩ : syracuseStep 3809267 = 5713901) B5713901
theorem B2539535 : Blo 1691546 2539535 := bstep (se 1 (by rfl) ⟨1904651, by rfl⟩ : syracuseStep 2539535 = 3809303) B3809303
theorem B2408491 : Blo 1691546 2408491 := bstep (se 1 (by rfl) ⟨1806368, by rfl⟩ : syracuseStep 2408491 = 3612737) B3612737
theorem B2539577 : Blo 1691546 2539577 := bstep (se 2 (by rfl) ⟨952341, by rfl⟩ : syracuseStep 2539577 = 1904683) B1904683
theorem B3809339 : Blo 1691546 3809339 := bstep (se 1 (by rfl) ⟨2857004, by rfl⟩ : syracuseStep 3809339 = 5714009) B5714009
theorem B18808919 : Blo 1691546 18808919 := bstep (se 1 (by rfl) ⟨14106689, by rfl⟩ : syracuseStep 18808919 = 28213379) B28213379
theorem B4284535 : Blo 1691546 4284535 := bstep (se 1 (by rfl) ⟨3213401, by rfl⟩ : syracuseStep 4284535 = 6426803) B6426803
theorem B17367173 : Blo 1691546 17367173 := bstep (se 4 (by rfl) ⟨1628172, by rfl⟩ : syracuseStep 17367173 = 3256345) B3256345
theorem B2539655 : Blo 1691546 2539655 := bstep (se 1 (by rfl) ⟨1904741, by rfl⟩ : syracuseStep 2539655 = 3809483) B3809483
theorem B2539691 : Blo 1691546 2539691 := bstep (se 1 (by rfl) ⟨1904768, by rfl⟩ : syracuseStep 2539691 = 3809537) B3809537
theorem B3809465 : Blo 1691546 3809465 := bstep (se 2 (by rfl) ⟨1428549, by rfl⟩ : syracuseStep 3809465 = 2857099) B2857099
theorem B52109513 : Blo 1691546 52109513 := bstep (se 2 (by rfl) ⟨19541067, by rfl⟩ : syracuseStep 52109513 = 39082135) B39082135
theorem B2539721 : Blo 1691546 2539721 := bstep (se 2 (by rfl) ⟨952395, by rfl⟩ : syracuseStep 2539721 = 1904791) B1904791
theorem B2408719 : Blo 1691546 2408719 := bstep (se 1 (by rfl) ⟨1806539, by rfl⟩ : syracuseStep 2408719 = 3613079) B3613079
theorem B9634099 : Blo 1691546 9634099 := bstep (se 1 (by rfl) ⟨7225574, by rfl⟩ : syracuseStep 9634099 = 14451149) B14451149
theorem B3211579 : Blo 1691546 3211579 := bstep (se 1 (by rfl) ⟨2408684, by rfl⟩ : syracuseStep 3211579 = 4817369) B4817369
theorem B2539835 : Blo 1691546 2539835 := bstep (se 1 (by rfl) ⟨1904876, by rfl⟩ : syracuseStep 2539835 = 3809753) B3809753
theorem B2539895 : Blo 1691546 2539895 := bstep (se 1 (by rfl) ⟨1904921, by rfl⟩ : syracuseStep 2539895 = 3809843) B3809843
theorem B2539919 : Blo 1691546 2539919 := bstep (se 1 (by rfl) ⟨1904939, by rfl⟩ : syracuseStep 2539919 = 3809879) B3809879
theorem B19276217 : Blo 1691546 19276217 := bstep (se 2 (by rfl) ⟨7228581, by rfl⟩ : syracuseStep 19276217 = 14457163) B14457163
theorem B2539961 : Blo 1691546 2539961 := bstep (se 2 (by rfl) ⟨952485, by rfl⟩ : syracuseStep 2539961 = 1904971) B1904971
theorem B2540039 : Blo 1691546 2540039 := bstep (se 1 (by rfl) ⟨1905029, by rfl⟩ : syracuseStep 2540039 = 3810059) B3810059
theorem B4882955 : Blo 1691546 4882955 := bstep (se 1 (by rfl) ⟨3662216, by rfl⟩ : syracuseStep 4882955 = 7324433) B7324433
theorem B3809807 : Blo 1691546 3809807 := bstep (se 1 (by rfl) ⟨2857355, by rfl⟩ : syracuseStep 3809807 = 5714711) B5714711
theorem B3809825 : Blo 1691546 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B6423083 : Blo 1691546 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B4284971 : Blo 1691546 4284971 := bstep (se 1 (by rfl) ⟨3213728, by rfl⟩ : syracuseStep 4284971 = 6427457) B6427457
theorem B2540075 : Blo 1691546 2540075 := bstep (se 1 (by rfl) ⟨1905056, by rfl⟩ : syracuseStep 2540075 = 3810113) B3810113
theorem B2540105 : Blo 1691546 2540105 := bstep (se 2 (by rfl) ⟨952539, by rfl⟩ : syracuseStep 2540105 = 1905079) B1905079
theorem B4817495 : Blo 1691546 4817495 := bstep (se 1 (by rfl) ⟨3613121, by rfl⟩ : syracuseStep 4817495 = 7226243) B7226243
theorem B2712199 : Blo 1691546 2712199 := bstep (se 1 (by rfl) ⟨2034149, by rfl⟩ : syracuseStep 2712199 = 4068299) B4068299
theorem B3613369 : Blo 1691546 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B2540219 : Blo 1691546 2540219 := bstep (se 1 (by rfl) ⟨1905164, by rfl⟩ : syracuseStep 2540219 = 3810329) B3810329
theorem B2540279 : Blo 1691546 2540279 := bstep (se 1 (by rfl) ⟨1905209, by rfl⟩ : syracuseStep 2540279 = 3810419) B3810419
theorem B5710607 : Blo 1691546 5710607 := bstep (se 1 (by rfl) ⟨4282955, by rfl⟩ : syracuseStep 5710607 = 8565911) B8565911
theorem B2540303 : Blo 1691546 2540303 := bstep (se 1 (by rfl) ⟨1905227, by rfl⟩ : syracuseStep 2540303 = 3810455) B3810455
theorem B3212065 : Blo 1691546 3212065 := bstep (se 2 (by rfl) ⟨1204524, by rfl⟩ : syracuseStep 3212065 = 2409049) B2409049
theorem B13386545 : Blo 1691546 13386545 := bstep (se 2 (by rfl) ⟨5019954, by rfl⟩ : syracuseStep 13386545 = 10039909) B10039909
theorem B3810167 : Blo 1691546 3810167 := bstep (se 1 (by rfl) ⟨2857625, by rfl⟩ : syracuseStep 3810167 = 5715251) B5715251
theorem B8684509 : Blo 1691546 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B3048463 : Blo 1691546 3048463 := bstep (se 1 (by rfl) ⟨2286347, by rfl⟩ : syracuseStep 3048463 = 4572695) B4572695
theorem B5710877 : Blo 1691546 5710877 := bstep (se 3 (by rfl) ⟨1070789, by rfl⟩ : syracuseStep 5710877 = 2141579) B2141579
theorem B3810347 : Blo 1691546 3810347 := bstep (se 1 (by rfl) ⟨2857760, by rfl⟩ : syracuseStep 3810347 = 5715521) B5715521
theorem B3663119 : Blo 1691546 3663119 := bstep (se 1 (by rfl) ⟨2747339, by rfl⟩ : syracuseStep 3663119 = 5494679) B5494679
theorem B3613967 : Blo 1691546 3613967 := bstep (se 1 (by rfl) ⟨2710475, by rfl⟩ : syracuseStep 3613967 = 5420951) B5420951
theorem B5145889 : Blo 1691546 5145889 := bstep (se 2 (by rfl) ⟨1929708, by rfl⟩ : syracuseStep 5145889 = 3859417) B3859417
theorem B54912289 : Blo 1691546 54912289 := bstep (se 2 (by rfl) ⟨20592108, by rfl⟩ : syracuseStep 54912289 = 41184217) B41184217
theorem B13919521 : Blo 1691546 13919521 := bstep (se 2 (by rfl) ⟨5219820, by rfl⟩ : syracuseStep 13919521 = 10439641) B10439641
theorem B4285811 : Blo 1691546 4285811 := bstep (se 1 (by rfl) ⟨3214358, by rfl⟩ : syracuseStep 4285811 = 6428717) B6428717
theorem B4285831 : Blo 1691546 4285831 := bstep (se 1 (by rfl) ⟨3214373, by rfl⟩ : syracuseStep 4285831 = 6428747) B6428747
theorem B9405881 : Blo 1691546 9405881 := bstep (se 2 (by rfl) ⟨3527205, by rfl⟩ : syracuseStep 9405881 = 7054411) B7054411
theorem B32548301 : Blo 1691546 32548301 := bstep (se 3 (by rfl) ⟨6102806, by rfl⟩ : syracuseStep 32548301 = 12205613) B12205613
theorem B4286105 : Blo 1691546 4286105 := bstep (se 2 (by rfl) ⟨1607289, by rfl⟩ : syracuseStep 4286105 = 3214579) B3214579
theorem B54904499 : Blo 1691546 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B9635557 : Blo 1691546 9635557 := bstep (se 4 (by rfl) ⟨903333, by rfl⟩ : syracuseStep 9635557 = 1806667) B1806667
theorem B16262927 : Blo 1691546 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B4286267 : Blo 1691546 4286267 := bstep (se 1 (by rfl) ⟨3214700, by rfl⟩ : syracuseStep 4286267 = 6429401) B6429401
theorem B7227251 : Blo 1691546 7227251 := bstep (se 1 (by rfl) ⟨5420438, by rfl⟩ : syracuseStep 7227251 = 10840877) B10840877
theorem B8570771 : Blo 1691546 8570771 := bstep (se 1 (by rfl) ⟨6428078, by rfl⟩ : syracuseStep 8570771 = 12856157) B12856157
theorem B4286479 : Blo 1691546 4286479 := bstep (se 1 (by rfl) ⟨3214859, by rfl⟩ : syracuseStep 4286479 = 6429719) B6429719
theorem B3213371 : Blo 1691546 3213371 := bstep (se 1 (by rfl) ⟨2410028, by rfl⟩ : syracuseStep 3213371 = 4820057) B4820057
theorem B4286753 : Blo 1691546 4286753 := bstep (se 2 (by rfl) ⟨1607532, by rfl⟩ : syracuseStep 4286753 = 3215065) B3215065
theorem B9767303 : Blo 1691546 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B1902991 : Blo 1691546 1902991 := bstep (se 1 (by rfl) ⟨1427243, by rfl⟩ : syracuseStep 1902991 = 2854487) B2854487
theorem B5712281 : Blo 1691546 5712281 := bstep (se 2 (by rfl) ⟨2142105, by rfl⟩ : syracuseStep 5712281 = 4284211) B4284211
theorem B6425041 : Blo 1691546 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B3213857 : Blo 1691546 3213857 := bstep (se 2 (by rfl) ⟨1205196, by rfl⟩ : syracuseStep 3213857 = 2410393) B2410393
theorem B3214009 : Blo 1691546 3214009 := bstep (se 2 (by rfl) ⟨1205253, by rfl⟩ : syracuseStep 3214009 = 2410507) B2410507
theorem B6425345 : Blo 1691546 6425345 := bstep (se 2 (by rfl) ⟨2409504, by rfl⟩ : syracuseStep 6425345 = 4819009) B4819009
theorem B3615521 : Blo 1691546 3615521 := bstep (se 2 (by rfl) ⟨1355820, by rfl⟩ : syracuseStep 3615521 = 2711641) B2711641
theorem B2140987 : Blo 1691546 2140987 := bstep (se 1 (by rfl) ⟨1605740, by rfl⟩ : syracuseStep 2140987 = 3211481) B3211481
theorem B26405747 : Blo 1691546 26405747 := bstep (se 1 (by rfl) ⟨19804310, by rfl⟩ : syracuseStep 26405747 = 39608621) B39608621
theorem B14461811 : Blo 1691546 14461811 := bstep (se 1 (by rfl) ⟨10846358, by rfl⟩ : syracuseStep 14461811 = 21692717) B21692717
theorem B3615607 : Blo 1691546 3615607 := bstep (se 1 (by rfl) ⟨2711705, by rfl⟩ : syracuseStep 3615607 = 5423411) B5423411
theorem B1903495 : Blo 1691546 1903495 := bstep (se 1 (by rfl) ⟨1427621, by rfl⟩ : syracuseStep 1903495 = 2855243) B2855243
theorem B1903675 : Blo 1691546 1903675 := bstep (se 1 (by rfl) ⟨1427756, by rfl⟩ : syracuseStep 1903675 = 2855513) B2855513
theorem B5712983 : Blo 1691546 5712983 := bstep (se 1 (by rfl) ⟨4284737, by rfl⟩ : syracuseStep 5712983 = 8569475) B8569475
theorem B6425801 : Blo 1691546 6425801 := bstep (se 2 (by rfl) ⟨2409675, by rfl⟩ : syracuseStep 6425801 = 4819351) B4819351
theorem B4820239 : Blo 1691546 4820239 := bstep (se 1 (by rfl) ⟨3615179, by rfl⟩ : syracuseStep 4820239 = 7230359) B7230359
theorem B6860065 : Blo 1691546 6860065 := bstep (se 2 (by rfl) ⟨2572524, by rfl⟩ : syracuseStep 6860065 = 5145049) B5145049
theorem B4820285 : Blo 1691546 4820285 := bstep (se 3 (by rfl) ⟨903803, by rfl⟩ : syracuseStep 4820285 = 1807607) B1807607
theorem B16264583 : Blo 1691546 16264583 := bstep (se 1 (by rfl) ⟨12198437, by rfl⟩ : syracuseStep 16264583 = 24396875) B24396875
theorem B59403779 : Blo 1691546 59403779 := bstep (se 1 (by rfl) ⟨44552834, by rfl⟩ : syracuseStep 59403779 = 89105669) B89105669
theorem B1904143 : Blo 1691546 1904143 := bstep (se 1 (by rfl) ⟨1428107, by rfl⟩ : syracuseStep 1904143 = 2856215) B2856215
theorem B5713469 : Blo 1691546 5713469 := bstep (se 3 (by rfl) ⟨1071275, by rfl⟩ : syracuseStep 5713469 = 2142551) B2142551
theorem B8564291 : Blo 1691546 8564291 := bstep (se 1 (by rfl) ⟨6423218, by rfl⟩ : syracuseStep 8564291 = 12846437) B12846437
theorem B10997315 : Blo 1691546 10997315 := bstep (se 1 (by rfl) ⟨8247986, by rfl⟩ : syracuseStep 10997315 = 16495973) B16495973
theorem B28929635 : Blo 1691546 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B4820627 : Blo 1691546 4820627 := bstep (se 1 (by rfl) ⟨3615470, by rfl⟩ : syracuseStep 4820627 = 7230941) B7230941
theorem B87928577 : Blo 1691546 87928577 := bstep (se 2 (by rfl) ⟨32973216, by rfl⟩ : syracuseStep 87928577 = 65946433) B65946433
theorem B2141959 : Blo 1691546 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B8564615 : Blo 1691546 8564615 := bstep (se 1 (by rfl) ⟨6423461, by rfl⟩ : syracuseStep 8564615 = 12846923) B12846923
theorem B21696407 : Blo 1691546 21696407 := bstep (se 1 (by rfl) ⟨16272305, by rfl⟩ : syracuseStep 21696407 = 32544611) B32544611
theorem B14462873 : Blo 1691546 14462873 := bstep (se 2 (by rfl) ⟨5423577, by rfl⟩ : syracuseStep 14462873 = 10847155) B10847155
theorem B1691579 : Blo 1691546 1691579 := bstep (se 1 (by rfl) ⟨1268684, by rfl⟩ : syracuseStep 1691579 = 2537369) B2537369
theorem B1691655 : Blo 1691546 1691655 := bstep (se 1 (by rfl) ⟨1268741, by rfl⟩ : syracuseStep 1691655 = 2537483) B2537483
theorem B1904647 : Blo 1691546 1904647 := bstep (se 1 (by rfl) ⟨1428485, by rfl⟩ : syracuseStep 1904647 = 2856971) B2856971
theorem B1691663 : Blo 1691546 1691663 := bstep (se 1 (by rfl) ⟨1268747, by rfl⟩ : syracuseStep 1691663 = 2537495) B2537495
theorem B1691707 : Blo 1691546 1691707 := bstep (se 1 (by rfl) ⟨1268780, by rfl⟩ : syracuseStep 1691707 = 2537561) B2537561
theorem B9146429 : Blo 1691546 9146429 := bstep (se 3 (by rfl) ⟨1714955, by rfl⟩ : syracuseStep 9146429 = 3429911) B3429911
theorem B1691783 : Blo 1691546 1691783 := bstep (se 1 (by rfl) ⟨1268837, by rfl⟩ : syracuseStep 1691783 = 2537675) B2537675
theorem B2855047 : Blo 1691546 2855047 := bstep (se 1 (by rfl) ⟨2141285, by rfl⟩ : syracuseStep 2855047 = 4282571) B4282571
theorem B1691791 : Blo 1691546 1691791 := bstep (se 1 (by rfl) ⟨1268843, by rfl⟩ : syracuseStep 1691791 = 2537687) B2537687
theorem B24391853 : Blo 1691546 24391853 := bstep (se 3 (by rfl) ⟨4573472, by rfl⟩ : syracuseStep 24391853 = 9146945) B9146945
theorem B2142379 : Blo 1691546 2142379 := bstep (se 1 (by rfl) ⟨1606784, by rfl⟩ : syracuseStep 2142379 = 3213569) B3213569
theorem B1691835 : Blo 1691546 1691835 := bstep (se 1 (by rfl) ⟨1268876, by rfl⟩ : syracuseStep 1691835 = 2537753) B2537753
theorem B1904827 : Blo 1691546 1904827 := bstep (se 1 (by rfl) ⟨1428620, by rfl⟩ : syracuseStep 1904827 = 2857241) B2857241
theorem B12849353 : Blo 1691546 12849353 := bstep (se 2 (by rfl) ⟨4818507, by rfl⟩ : syracuseStep 12849353 = 9637015) B9637015
theorem B1691911 : Blo 1691546 1691911 := bstep (se 1 (by rfl) ⟨1268933, by rfl⟩ : syracuseStep 1691911 = 2537867) B2537867
theorem B1691919 : Blo 1691546 1691919 := bstep (se 1 (by rfl) ⟨1268939, by rfl⟩ : syracuseStep 1691919 = 2537879) B2537879
theorem B1691963 : Blo 1691546 1691963 := bstep (se 1 (by rfl) ⟨1268972, by rfl⟩ : syracuseStep 1691963 = 2537945) B2537945
theorem B1692039 : Blo 1691546 1692039 := bstep (se 1 (by rfl) ⟨1269029, by rfl⟩ : syracuseStep 1692039 = 2538059) B2538059
theorem B1692047 : Blo 1691546 1692047 := bstep (se 1 (by rfl) ⟨1269035, by rfl⟩ : syracuseStep 1692047 = 2538071) B2538071
theorem B2142607 : Blo 1691546 2142607 := bstep (se 1 (by rfl) ⟨1606955, by rfl⟩ : syracuseStep 2142607 = 3213911) B3213911
theorem B21688721 : Blo 1691546 21688721 := bstep (se 2 (by rfl) ⟨8133270, by rfl⟩ : syracuseStep 21688721 = 16266541) B16266541
theorem B9638291 : Blo 1691546 9638291 := bstep (se 1 (by rfl) ⟨7228718, by rfl⟩ : syracuseStep 9638291 = 14457437) B14457437
theorem B6099347 : Blo 1691546 6099347 := bstep (se 1 (by rfl) ⟨4574510, by rfl⟩ : syracuseStep 6099347 = 9149021) B9149021
theorem B1692091 : Blo 1691546 1692091 := bstep (se 1 (by rfl) ⟨1269068, by rfl⟩ : syracuseStep 1692091 = 2538137) B2538137
theorem B1692167 : Blo 1691546 1692167 := bstep (se 1 (by rfl) ⟨1269125, by rfl⟩ : syracuseStep 1692167 = 2538251) B2538251
theorem B4821515 : Blo 1691546 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B1692175 : Blo 1691546 1692175 := bstep (se 1 (by rfl) ⟨1269131, by rfl⟩ : syracuseStep 1692175 = 2538263) B2538263
theorem B1692219 : Blo 1691546 1692219 := bstep (se 1 (by rfl) ⟨1269164, by rfl⟩ : syracuseStep 1692219 = 2538329) B2538329
theorem B1692295 : Blo 1691546 1692295 := bstep (se 1 (by rfl) ⟨1269221, by rfl⟩ : syracuseStep 1692295 = 2538443) B2538443
theorem B1692303 : Blo 1691546 1692303 := bstep (se 1 (by rfl) ⟨1269227, by rfl⟩ : syracuseStep 1692303 = 2538455) B2538455
theorem B1692347 : Blo 1691546 1692347 := bstep (se 1 (by rfl) ⟨1269260, by rfl⟩ : syracuseStep 1692347 = 2538521) B2538521
theorem B1692423 : Blo 1691546 1692423 := bstep (se 1 (by rfl) ⟨1269317, by rfl⟩ : syracuseStep 1692423 = 2538635) B2538635
theorem B2855695 : Blo 1691546 2855695 := bstep (se 1 (by rfl) ⟨2141771, by rfl⟩ : syracuseStep 2855695 = 4283543) B4283543
theorem B1692431 : Blo 1691546 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B8131387 : Blo 1691546 8131387 := bstep (se 1 (by rfl) ⟨6098540, by rfl⟩ : syracuseStep 8131387 = 12197081) B12197081
theorem B1692475 : Blo 1691546 1692475 := bstep (se 1 (by rfl) ⟨1269356, by rfl⟩ : syracuseStep 1692475 = 2538713) B2538713
theorem B1692551 : Blo 1691546 1692551 := bstep (se 1 (by rfl) ⟨1269413, by rfl⟩ : syracuseStep 1692551 = 2538827) B2538827
theorem B7230343 : Blo 1691546 7230343 := bstep (se 1 (by rfl) ⟨5422757, by rfl⟩ : syracuseStep 7230343 = 10845515) B10845515
theorem B1692559 : Blo 1691546 1692559 := bstep (se 1 (by rfl) ⟨1269419, by rfl⟩ : syracuseStep 1692559 = 2538839) B2538839
theorem B3806099 : Blo 1691546 3806099 := bstep (se 1 (by rfl) ⟨2854574, by rfl⟩ : syracuseStep 3806099 = 5709149) B5709149
theorem B5714873 : Blo 1691546 5714873 := bstep (se 2 (by rfl) ⟨2143077, by rfl⟩ : syracuseStep 5714873 = 4286155) B4286155
theorem B1692603 : Blo 1691546 1692603 := bstep (se 1 (by rfl) ⟨1269452, by rfl⟩ : syracuseStep 1692603 = 2538905) B2538905
theorem B3806153 : Blo 1691546 3806153 := bstep (se 2 (by rfl) ⟨1427307, by rfl⟩ : syracuseStep 3806153 = 2854615) B2854615
theorem B1692679 : Blo 1691546 1692679 := bstep (se 1 (by rfl) ⟨1269509, by rfl⟩ : syracuseStep 1692679 = 2539019) B2539019
theorem B3912719 : Blo 1691546 3912719 := bstep (se 1 (by rfl) ⟨2934539, by rfl⟩ : syracuseStep 3912719 = 5869079) B5869079
theorem B1692687 : Blo 1691546 1692687 := bstep (se 1 (by rfl) ⟨1269515, by rfl⟩ : syracuseStep 1692687 = 2539031) B2539031
theorem B1692731 : Blo 1691546 1692731 := bstep (se 1 (by rfl) ⟨1269548, by rfl⟩ : syracuseStep 1692731 = 2539097) B2539097
theorem B9638999 : Blo 1691546 9638999 := bstep (se 1 (by rfl) ⟨7229249, by rfl⟩ : syracuseStep 9638999 = 14458499) B14458499
theorem B2143351 : Blo 1691546 2143351 := bstep (se 1 (by rfl) ⟨1607513, by rfl⟩ : syracuseStep 2143351 = 3215027) B3215027
theorem B1692807 : Blo 1691546 1692807 := bstep (se 1 (by rfl) ⟨1269605, by rfl⟩ : syracuseStep 1692807 = 2539211) B2539211
theorem B1692815 : Blo 1691546 1692815 := bstep (se 1 (by rfl) ⟨1269611, by rfl⟩ : syracuseStep 1692815 = 2539223) B2539223
theorem B1692859 : Blo 1691546 1692859 := bstep (se 1 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 1692859 = 2539289) B2539289
theorem B6862025 : Blo 1691546 6862025 := bstep (se 2 (by rfl) ⟨2573259, by rfl⟩ : syracuseStep 6862025 = 5146519) B5146519
theorem B7230701 : Blo 1691546 7230701 := bstep (se 3 (by rfl) ⟨1355756, by rfl⟩ : syracuseStep 7230701 = 2711513) B2711513
theorem B1692935 : Blo 1691546 1692935 := bstep (se 1 (by rfl) ⟨1269701, by rfl⟩ : syracuseStep 1692935 = 2539403) B2539403
theorem B1692943 : Blo 1691546 1692943 := bstep (se 1 (by rfl) ⟨1269707, by rfl⟩ : syracuseStep 1692943 = 2539415) B2539415
theorem B2856235 : Blo 1691546 2856235 := bstep (se 1 (by rfl) ⟨2142176, by rfl⟩ : syracuseStep 2856235 = 4284353) B4284353
theorem B1692987 : Blo 1691546 1692987 := bstep (se 1 (by rfl) ⟨1269740, by rfl⟩ : syracuseStep 1692987 = 2539481) B2539481
theorem B1693063 : Blo 1691546 1693063 := bstep (se 1 (by rfl) ⟨1269797, by rfl⟩ : syracuseStep 1693063 = 2539595) B2539595
theorem B1693071 : Blo 1691546 1693071 := bstep (se 1 (by rfl) ⟨1269803, by rfl⟩ : syracuseStep 1693071 = 2539607) B2539607
theorem B8131985 : Blo 1691546 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B2856377 : Blo 1691546 2856377 := bstep (se 2 (by rfl) ⟨1071141, by rfl⟩ : syracuseStep 2856377 = 2142283) B2142283
theorem B1693115 : Blo 1691546 1693115 := bstep (se 1 (by rfl) ⟨1269836, by rfl⟩ : syracuseStep 1693115 = 2539673) B2539673
theorem B1693191 : Blo 1691546 1693191 := bstep (se 1 (by rfl) ⟨1269893, by rfl⟩ : syracuseStep 1693191 = 2539787) B2539787
theorem B5715467 : Blo 1691546 5715467 := bstep (se 1 (by rfl) ⟨4286600, by rfl⟩ : syracuseStep 5715467 = 8573201) B8573201
theorem B1693199 : Blo 1691546 1693199 := bstep (se 1 (by rfl) ⟨1269899, by rfl⟩ : syracuseStep 1693199 = 2539799) B2539799
theorem B1693243 : Blo 1691546 1693243 := bstep (se 1 (by rfl) ⟨1269932, by rfl⟩ : syracuseStep 1693243 = 2539865) B2539865
theorem B12203597 : Blo 1691546 12203597 := bstep (se 3 (by rfl) ⟨2288174, by rfl⟩ : syracuseStep 12203597 = 4576349) B4576349
theorem B4281943 : Blo 1691546 4281943 := bstep (se 1 (by rfl) ⟨3211457, by rfl⟩ : syracuseStep 4281943 = 6422915) B6422915
theorem B5715575 : Blo 1691546 5715575 := bstep (se 1 (by rfl) ⟨4286681, by rfl⟩ : syracuseStep 5715575 = 8573363) B8573363
theorem B3806855 : Blo 1691546 3806855 := bstep (se 1 (by rfl) ⟨2855141, by rfl⟩ : syracuseStep 3806855 = 5710283) B5710283
theorem B1693319 : Blo 1691546 1693319 := bstep (se 1 (by rfl) ⟨1269989, by rfl⟩ : syracuseStep 1693319 = 2539979) B2539979
theorem B1693327 : Blo 1691546 1693327 := bstep (se 1 (by rfl) ⟨1269995, by rfl⟩ : syracuseStep 1693327 = 2539991) B2539991
theorem B20592305 : Blo 1691546 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B1693371 : Blo 1691546 1693371 := bstep (se 1 (by rfl) ⟨1270028, by rfl⟩ : syracuseStep 1693371 = 2540057) B2540057
theorem B18298561 : Blo 1691546 18298561 := bstep (se 2 (by rfl) ⟨6861960, by rfl⟩ : syracuseStep 18298561 = 13723921) B13723921
theorem B12859073 : Blo 1691546 12859073 := bstep (se 2 (by rfl) ⟨4822152, by rfl⟩ : syracuseStep 12859073 = 9644305) B9644305
theorem B17381081 : Blo 1691546 17381081 := bstep (se 2 (by rfl) ⟨6517905, by rfl⟩ : syracuseStep 17381081 = 13035811) B13035811
theorem B1693447 : Blo 1691546 1693447 := bstep (se 1 (by rfl) ⟨1270085, by rfl⟩ : syracuseStep 1693447 = 2540171) B2540171
theorem B1693455 : Blo 1691546 1693455 := bstep (se 1 (by rfl) ⟨1270091, by rfl⟩ : syracuseStep 1693455 = 2540183) B2540183
theorem B3807035 : Blo 1691546 3807035 := bstep (se 1 (by rfl) ⟨2855276, by rfl⟩ : syracuseStep 3807035 = 5710553) B5710553
theorem B1693499 : Blo 1691546 1693499 := bstep (se 1 (by rfl) ⟨1270124, by rfl⟩ : syracuseStep 1693499 = 2540249) B2540249
theorem B2537351 : Blo 1691546 2537351 := bstep (se 1 (by rfl) ⟨1903013, by rfl⟩ : syracuseStep 2537351 = 3806027) B3806027
theorem B4282247 : Blo 1691546 4282247 := bstep (se 1 (by rfl) ⟨3211685, by rfl⟩ : syracuseStep 4282247 = 6423371) B6423371
theorem B2537387 : Blo 1691546 2537387 := bstep (se 1 (by rfl) ⟨1903040, by rfl⟩ : syracuseStep 2537387 = 3806081) B3806081
theorem B3807161 : Blo 1691546 3807161 := bstep (se 2 (by rfl) ⟨1427685, by rfl⟩ : syracuseStep 3807161 = 2855371) B2855371
theorem B2537417 : Blo 1691546 2537417 := bstep (se 2 (by rfl) ⟨951531, by rfl⟩ : syracuseStep 2537417 = 1903063) B1903063
theorem B4282379 : Blo 1691546 4282379 := bstep (se 1 (by rfl) ⟨3211784, by rfl⟩ : syracuseStep 4282379 = 6423569) B6423569
theorem B4577323 : Blo 1691546 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B2537531 : Blo 1691546 2537531 := bstep (se 1 (by rfl) ⟨1903148, by rfl⟩ : syracuseStep 2537531 = 3806297) B3806297
theorem B2537591 : Blo 1691546 2537591 := bstep (se 1 (by rfl) ⟨1903193, by rfl⟩ : syracuseStep 2537591 = 3806387) B3806387
theorem B2857079 : Blo 1691546 2857079 := bstep (se 1 (by rfl) ⟨2142809, by rfl⟩ : syracuseStep 2857079 = 4285619) B4285619
theorem B2537615 : Blo 1691546 2537615 := bstep (se 1 (by rfl) ⟨1903211, by rfl⟩ : syracuseStep 2537615 = 3806423) B3806423
theorem B2537657 : Blo 1691546 2537657 := bstep (se 2 (by rfl) ⟨951621, by rfl⟩ : syracuseStep 2537657 = 1903243) B1903243
theorem B28907765 : Blo 1691546 28907765 := bstep (se 5 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 28907765 = 2710103) B2710103
theorem B6428929 : Blo 1691546 6428929 := bstep (se 2 (by rfl) ⟨2410848, by rfl⟩ : syracuseStep 6428929 = 4821697) B4821697
theorem B2537735 : Blo 1691546 2537735 := bstep (se 1 (by rfl) ⟨1903301, by rfl⟩ : syracuseStep 2537735 = 3806603) B3806603
theorem B3807503 : Blo 1691546 3807503 := bstep (se 1 (by rfl) ⟨2855627, by rfl⟩ : syracuseStep 3807503 = 5711255) B5711255
theorem B3807521 : Blo 1691546 3807521 := bstep (se 2 (by rfl) ⟨1427820, by rfl⟩ : syracuseStep 3807521 = 2855641) B2855641
theorem B2537771 : Blo 1691546 2537771 := bstep (se 1 (by rfl) ⟨1903328, by rfl⟩ : syracuseStep 2537771 = 3806657) B3806657
theorem B2537801 : Blo 1691546 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B2537915 : Blo 1691546 2537915 := bstep (se 1 (by rfl) ⟨1903436, by rfl⟩ : syracuseStep 2537915 = 3806873) B3806873
theorem B2537975 : Blo 1691546 2537975 := bstep (se 1 (by rfl) ⟨1903481, by rfl⟩ : syracuseStep 2537975 = 3806963) B3806963
theorem B2537999 : Blo 1691546 2537999 := bstep (se 1 (by rfl) ⟨1903499, by rfl⟩ : syracuseStep 2537999 = 3806999) B3806999
theorem B4282895 : Blo 1691546 4282895 := bstep (se 1 (by rfl) ⟨3212171, by rfl⟩ : syracuseStep 4282895 = 6424343) B6424343
theorem B2538041 : Blo 1691546 2538041 := bstep (se 2 (by rfl) ⟨951765, by rfl⟩ : syracuseStep 2538041 = 1903531) B1903531
theorem B2857531 : Blo 1691546 2857531 := bstep (se 1 (by rfl) ⟨2143148, by rfl⟩ : syracuseStep 2857531 = 4286297) B4286297
theorem B24746563 : Blo 1691546 24746563 := bstep (se 1 (by rfl) ⟨18559922, by rfl⟩ : syracuseStep 24746563 = 37119845) B37119845
theorem B3807863 : Blo 1691546 3807863 := bstep (se 1 (by rfl) ⟨2855897, by rfl⟩ : syracuseStep 3807863 = 5711795) B5711795
theorem B2538119 : Blo 1691546 2538119 := bstep (se 1 (by rfl) ⟨1903589, by rfl⟩ : syracuseStep 2538119 = 3807179) B3807179
theorem B4283027 : Blo 1691546 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B2538155 : Blo 1691546 2538155 := bstep (se 1 (by rfl) ⟨1903616, by rfl⟩ : syracuseStep 2538155 = 3807233) B3807233
theorem B16259777 : Blo 1691546 16259777 := bstep (se 2 (by rfl) ⟨6097416, by rfl⟩ : syracuseStep 16259777 = 12194833) B12194833
theorem B2538185 : Blo 1691546 2538185 := bstep (se 2 (by rfl) ⟨951819, by rfl⟩ : syracuseStep 2538185 = 1903639) B1903639
theorem B2857673 : Blo 1691546 2857673 := bstep (se 2 (by rfl) ⟨1071627, by rfl⟩ : syracuseStep 2857673 = 2143255) B2143255
theorem B296622809 : Blo 1691546 296622809 := bstep (se 2 (by rfl) ⟨111233553, by rfl⟩ : syracuseStep 296622809 = 222467107) B222467107
theorem B3808043 : Blo 1691546 3808043 := bstep (se 1 (by rfl) ⟨2856032, by rfl⟩ : syracuseStep 3808043 = 5712065) B5712065
theorem B2538299 : Blo 1691546 2538299 := bstep (se 1 (by rfl) ⟨1903724, by rfl⟩ : syracuseStep 2538299 = 3807449) B3807449
theorem B10992473 : Blo 1691546 10992473 := bstep (se 2 (by rfl) ⟨4122177, by rfl⟩ : syracuseStep 10992473 = 8244355) B8244355
theorem B11582297 : Blo 1691546 11582297 := bstep (se 2 (by rfl) ⟨4343361, by rfl⟩ : syracuseStep 11582297 = 8686723) B8686723
theorem B2538359 : Blo 1691546 2538359 := bstep (se 1 (by rfl) ⟨1903769, by rfl⟩ : syracuseStep 2538359 = 3807539) B3807539
theorem B2538383 : Blo 1691546 2538383 := bstep (se 1 (by rfl) ⟨1903787, by rfl⟩ : syracuseStep 2538383 = 3807575) B3807575
theorem B2538425 : Blo 1691546 2538425 := bstep (se 2 (by rfl) ⟨951909, by rfl⟩ : syracuseStep 2538425 = 1903819) B1903819
theorem B9640889 : Blo 1691546 9640889 := bstep (se 2 (by rfl) ⟨3615333, by rfl⟩ : syracuseStep 9640889 = 7230667) B7230667
theorem B82394117 : Blo 1691546 82394117 := bstep (se 4 (by rfl) ⟨7724448, by rfl⟩ : syracuseStep 82394117 = 15448897) B15448897
theorem B2538503 : Blo 1691546 2538503 := bstep (se 1 (by rfl) ⟨1903877, by rfl⟩ : syracuseStep 2538503 = 3807755) B3807755
theorem B13728791 : Blo 1691546 13728791 := bstep (se 1 (by rfl) ⟨10296593, by rfl⟩ : syracuseStep 13728791 = 20593187) B20593187
theorem B2538539 : Blo 1691546 2538539 := bstep (se 1 (by rfl) ⟨1903904, by rfl⟩ : syracuseStep 2538539 = 3807809) B3807809
theorem B2538569 : Blo 1691546 2538569 := bstep (se 2 (by rfl) ⟨951963, by rfl⟩ : syracuseStep 2538569 = 1903927) B1903927
theorem B3808403 : Blo 1691546 3808403 := bstep (se 1 (by rfl) ⟨2856302, by rfl⟩ : syracuseStep 3808403 = 5712605) B5712605
theorem B2538683 : Blo 1691546 2538683 := bstep (se 1 (by rfl) ⟨1904012, by rfl⟩ : syracuseStep 2538683 = 3808025) B3808025
theorem B3808457 : Blo 1691546 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B2538743 : Blo 1691546 2538743 := bstep (se 1 (by rfl) ⟨1904057, by rfl⟩ : syracuseStep 2538743 = 3808115) B3808115
theorem B2538767 : Blo 1691546 2538767 := bstep (se 1 (by rfl) ⟨1904075, by rfl⟩ : syracuseStep 2538767 = 3808151) B3808151
theorem B30580001 : Blo 1691546 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B125254957 : Blo 1691546 125254957 := bstep (se 3 (by rfl) ⟨23485304, by rfl⟩ : syracuseStep 125254957 = 46970609) B46970609
theorem B2538809 : Blo 1691546 2538809 := bstep (se 2 (by rfl) ⟨952053, by rfl⟩ : syracuseStep 2538809 = 1904107) B1904107
theorem B8568179 : Blo 1691546 8568179 := bstep (se 1 (by rfl) ⟨6426134, by rfl⟩ : syracuseStep 8568179 = 12852269) B12852269
theorem B2538887 : Blo 1691546 2538887 := bstep (se 1 (by rfl) ⟨1904165, by rfl⟩ : syracuseStep 2538887 = 3808331) B3808331
theorem B5709203 : Blo 1691546 5709203 := bstep (se 1 (by rfl) ⟨4281902, by rfl⟩ : syracuseStep 5709203 = 8563805) B8563805
theorem B8240537 : Blo 1691546 8240537 := bstep (se 2 (by rfl) ⟨3090201, by rfl⟩ : syracuseStep 8240537 = 6180403) B6180403
theorem B2538923 : Blo 1691546 2538923 := bstep (se 1 (by rfl) ⟨1904192, by rfl⟩ : syracuseStep 2538923 = 3808385) B3808385
theorem B2538953 : Blo 1691546 2538953 := bstep (se 2 (by rfl) ⟨952107, by rfl⟩ : syracuseStep 2538953 = 1904215) B1904215
theorem B2539067 : Blo 1691546 2539067 := bstep (se 1 (by rfl) ⟨1904300, by rfl⟩ : syracuseStep 2539067 = 3808601) B3808601
theorem B2539127 : Blo 1691546 2539127 := bstep (se 1 (by rfl) ⟨1904345, by rfl⟩ : syracuseStep 2539127 = 3808691) B3808691
theorem B2539151 : Blo 1691546 2539151 := bstep (se 1 (by rfl) ⟨1904363, by rfl⟩ : syracuseStep 2539151 = 3808727) B3808727
theorem B2539193 : Blo 1691546 2539193 := bstep (se 2 (by rfl) ⟨952197, by rfl⟩ : syracuseStep 2539193 = 1904395) B1904395
theorem B4284161 : Blo 1691546 4284161 := bstep (se 2 (by rfl) ⟨1606560, by rfl⟩ : syracuseStep 4284161 = 3213121) B3213121
theorem B2539271 : Blo 1691546 2539271 := bstep (se 1 (by rfl) ⟨1904453, by rfl⟩ : syracuseStep 2539271 = 3808907) B3808907
theorem B2539307 : Blo 1691546 2539307 := bstep (se 1 (by rfl) ⟨1904480, by rfl⟩ : syracuseStep 2539307 = 3808961) B3808961
theorem B39100229 : Blo 1691546 39100229 := bstep (se 4 (by rfl) ⟨3665646, by rfl⟩ : syracuseStep 39100229 = 7331293) B7331293
theorem B2539337 : Blo 1691546 2539337 := bstep (se 2 (by rfl) ⟨952251, by rfl⟩ : syracuseStep 2539337 = 1904503) B1904503
theorem B8568665 : Blo 1691546 8568665 := bstep (se 2 (by rfl) ⟨3213249, by rfl⟩ : syracuseStep 8568665 = 6426499) B6426499
theorem B5422963 : Blo 1691546 5422963 := bstep (se 1 (by rfl) ⟨4067222, by rfl⟩ : syracuseStep 5422963 = 8134445) B8134445
theorem B3432311 : Blo 1691546 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B3809159 : Blo 1691546 3809159 := bstep (se 1 (by rfl) ⟨2856869, by rfl⟩ : syracuseStep 3809159 = 5713739) B5713739
theorem B2539451 : Blo 1691546 2539451 := bstep (se 1 (by rfl) ⟨1904588, by rfl⟩ : syracuseStep 2539451 = 3809177) B3809177
theorem B2539511 : Blo 1691546 2539511 := bstep (se 1 (by rfl) ⟨1904633, by rfl⟩ : syracuseStep 2539511 = 3809267) B3809267
theorem B2539529 : Blo 1691546 2539529 := bstep (se 2 (by rfl) ⟨952323, by rfl⟩ : syracuseStep 2539529 = 1904647) B1904647
theorem B2539559 : Blo 1691546 2539559 := bstep (se 1 (by rfl) ⟨1904669, by rfl⟩ : syracuseStep 2539559 = 3809339) B3809339
theorem B3211321 : Blo 1691546 3211321 := bstep (se 2 (by rfl) ⟨1204245, by rfl⟩ : syracuseStep 3211321 = 2408491) B2408491
theorem B6103097 : Blo 1691546 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B16261235 : Blo 1691546 16261235 := bstep (se 1 (by rfl) ⟨12195926, by rfl⟩ : syracuseStep 16261235 = 24391853) B24391853
theorem B52084853 : Blo 1691546 52084853 := bstep (se 5 (by rfl) ⟨2441477, by rfl⟩ : syracuseStep 52084853 = 4882955) B4882955
theorem B2539643 : Blo 1691546 2539643 := bstep (se 1 (by rfl) ⟨1904732, by rfl⟩ : syracuseStep 2539643 = 3809465) B3809465
theorem B8568989 : Blo 1691546 8568989 := bstep (se 3 (by rfl) ⟨1606685, by rfl⟩ : syracuseStep 8568989 = 3213371) B3213371
theorem B2539769 : Blo 1691546 2539769 := bstep (se 2 (by rfl) ⟨952413, by rfl⟩ : syracuseStep 2539769 = 1904827) B1904827
theorem B14459147 : Blo 1691546 14459147 := bstep (se 1 (by rfl) ⟨10844360, by rfl⟩ : syracuseStep 14459147 = 21688721) B21688721
theorem B2539871 : Blo 1691546 2539871 := bstep (se 1 (by rfl) ⟨1904903, by rfl⟩ : syracuseStep 2539871 = 3809807) B3809807
theorem B131981669 : Blo 1691546 131981669 := bstep (se 4 (by rfl) ⟨12373281, by rfl⟩ : syracuseStep 131981669 = 24746563) B24746563
theorem B3211625 : Blo 1691546 3211625 := bstep (se 2 (by rfl) ⟨1204359, by rfl⟩ : syracuseStep 3211625 = 2408719) B2408719
theorem B2539883 : Blo 1691546 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B3211663 : Blo 1691546 3211663 := bstep (se 1 (by rfl) ⟨2408747, by rfl⟩ : syracuseStep 3211663 = 4817495) B4817495
theorem B12845465 : Blo 1691546 12845465 := bstep (se 2 (by rfl) ⟨4817049, by rfl⟩ : syracuseStep 12845465 = 9634099) B9634099
theorem B2540111 : Blo 1691546 2540111 := bstep (se 1 (by rfl) ⟨1905083, by rfl⟩ : syracuseStep 2540111 = 3810167) B3810167
theorem B3809915 : Blo 1691546 3809915 := bstep (se 1 (by rfl) ⟨2857436, by rfl⟩ : syracuseStep 3809915 = 5714873) B5714873
theorem B2540231 : Blo 1691546 2540231 := bstep (se 1 (by rfl) ⟨1905173, by rfl⟩ : syracuseStep 2540231 = 3810347) B3810347
theorem B3810041 : Blo 1691546 3810041 := bstep (se 2 (by rfl) ⟨1428765, by rfl⟩ : syracuseStep 3810041 = 2857531) B2857531
theorem B2442079 : Blo 1691546 2442079 := bstep (se 1 (by rfl) ⟨1831559, by rfl⟩ : syracuseStep 2442079 = 3663119) B3663119
theorem B2409311 : Blo 1691546 2409311 := bstep (se 1 (by rfl) ⟨1806983, by rfl⟩ : syracuseStep 2409311 = 3613967) B3613967
theorem B4817825 : Blo 1691546 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B4285345 : Blo 1691546 4285345 := bstep (se 2 (by rfl) ⟨1607004, by rfl⟩ : syracuseStep 4285345 = 3214009) B3214009
theorem B3810311 : Blo 1691546 3810311 := bstep (se 1 (by rfl) ⟨2857733, by rfl⟩ : syracuseStep 3810311 = 5715467) B5715467
theorem B8135731 : Blo 1691546 8135731 := bstep (se 1 (by rfl) ⟨6101798, by rfl⟩ : syracuseStep 8135731 = 12203597) B12203597
theorem B3810383 : Blo 1691546 3810383 := bstep (se 1 (by rfl) ⟨2857787, by rfl⟩ : syracuseStep 3810383 = 5715575) B5715575
theorem B36602999 : Blo 1691546 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B4818167 : Blo 1691546 4818167 := bstep (se 1 (by rfl) ⟨3613625, by rfl⟩ : syracuseStep 4818167 = 7227251) B7227251
theorem B4064617 : Blo 1691546 4064617 := bstep (se 2 (by rfl) ⟨1524231, by rfl⟩ : syracuseStep 4064617 = 3048463) B3048463
theorem B8570285 : Blo 1691546 8570285 := bstep (se 3 (by rfl) ⟨1606928, by rfl⟩ : syracuseStep 8570285 = 3213857) B3213857
theorem B10839851 : Blo 1691546 10839851 := bstep (se 1 (by rfl) ⟨8129888, by rfl⟩ : syracuseStep 10839851 = 16259777) B16259777
theorem B197748539 : Blo 1691546 197748539 := bstep (se 1 (by rfl) ⟨148311404, by rfl⟩ : syracuseStep 197748539 = 296622809) B296622809
theorem B54929411 : Blo 1691546 54929411 := bstep (se 1 (by rfl) ⟨41197058, by rfl⟩ : syracuseStep 54929411 = 82394117) B82394117
theorem B9152527 : Blo 1691546 9152527 := bstep (se 1 (by rfl) ⟨6864395, by rfl⟩ : syracuseStep 9152527 = 13728791) B13728791
theorem B3213523 : Blo 1691546 3213523 := bstep (se 1 (by rfl) ⟨2410142, by rfl⟩ : syracuseStep 3213523 = 4820285) B4820285
theorem B5712119 : Blo 1691546 5712119 := bstep (se 1 (by rfl) ⟨4284089, by rfl⟩ : syracuseStep 5712119 = 8568179) B8568179
theorem B24398081 : Blo 1691546 24398081 := bstep (se 2 (by rfl) ⟨9149280, by rfl⟩ : syracuseStep 24398081 = 18298561) B18298561
theorem B12847409 : Blo 1691546 12847409 := bstep (se 2 (by rfl) ⟨4817778, by rfl⟩ : syracuseStep 12847409 = 9635557) B9635557
theorem B39602519 : Blo 1691546 39602519 := bstep (se 1 (by rfl) ⟨29701889, by rfl⟩ : syracuseStep 39602519 = 59403779) B59403779
theorem B19286423 : Blo 1691546 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B3213751 : Blo 1691546 3213751 := bstep (se 1 (by rfl) ⟨2410313, by rfl⟩ : syracuseStep 3213751 = 4820627) B4820627
theorem B5712443 : Blo 1691546 5712443 := bstep (se 1 (by rfl) ⟨4284332, by rfl⟩ : syracuseStep 5712443 = 8568665) B8568665
theorem B2288207 : Blo 1691546 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B6097619 : Blo 1691546 6097619 := bstep (se 1 (by rfl) ⟨4573214, by rfl⟩ : syracuseStep 6097619 = 9146429) B9146429
theorem B11578115 : Blo 1691546 11578115 := bstep (se 1 (by rfl) ⟨8683586, by rfl⟩ : syracuseStep 11578115 = 17367173) B17367173
theorem B5712713 : Blo 1691546 5712713 := bstep (se 2 (by rfl) ⟨2142267, by rfl⟩ : syracuseStep 5712713 = 4284535) B4284535
theorem B6425527 : Blo 1691546 6425527 := bstep (se 1 (by rfl) ⟨4819145, by rfl⟩ : syracuseStep 6425527 = 9638291) B9638291
theorem B8571905 : Blo 1691546 8571905 := bstep (se 2 (by rfl) ⟨3214464, by rfl⟩ : syracuseStep 8571905 = 6428929) B6428929
theorem B3214343 : Blo 1691546 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B8924363 : Blo 1691546 8924363 := bstep (se 1 (by rfl) ⟨6693272, by rfl⟩ : syracuseStep 8924363 = 13386545) B13386545
theorem B6425999 : Blo 1691546 6425999 := bstep (se 1 (by rfl) ⟨4819499, by rfl⟩ : syracuseStep 6425999 = 9638999) B9638999
theorem B4574683 : Blo 1691546 4574683 := bstep (se 1 (by rfl) ⟨3431012, by rfl⟩ : syracuseStep 4574683 = 6862025) B6862025
theorem B4820467 : Blo 1691546 4820467 := bstep (se 1 (by rfl) ⟨3615350, by rfl⟩ : syracuseStep 4820467 = 7230701) B7230701
theorem B3616265 : Blo 1691546 3616265 := bstep (se 2 (by rfl) ⟨1356099, by rfl⟩ : syracuseStep 3616265 = 2712199) B2712199
theorem B1904251 : Blo 1691546 1904251 := bstep (se 1 (by rfl) ⟨1428188, by rfl⟩ : syracuseStep 1904251 = 2856377) B2856377
theorem B6270587 : Blo 1691546 6270587 := bstep (se 1 (by rfl) ⟨4702940, by rfl⟩ : syracuseStep 6270587 = 9405881) B9405881
theorem B16264925 : Blo 1691546 16264925 := bstep (se 3 (by rfl) ⟨3049673, by rfl⟩ : syracuseStep 16264925 = 6099347) B6099347
theorem B2854649 : Blo 1691546 2854649 := bstep (se 2 (by rfl) ⟨1070493, by rfl⟩ : syracuseStep 2854649 = 2140987) B2140987
theorem B10841849 : Blo 1691546 10841849 := bstep (se 2 (by rfl) ⟨4065693, by rfl⟩ : syracuseStep 10841849 = 8131387) B8131387
theorem B8572715 : Blo 1691546 8572715 := bstep (se 1 (by rfl) ⟨6429536, by rfl⟩ : syracuseStep 8572715 = 12859073) B12859073
theorem B11587387 : Blo 1691546 11587387 := bstep (se 1 (by rfl) ⟨8690540, by rfl⟩ : syracuseStep 11587387 = 17381081) B17381081
theorem B4820809 : Blo 1691546 4820809 := bstep (se 2 (by rfl) ⟨1807803, by rfl⟩ : syracuseStep 4820809 = 3615607) B3615607
theorem B10841951 : Blo 1691546 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B1691567 : Blo 1691546 1691567 := bstep (se 1 (by rfl) ⟨1268675, by rfl⟩ : syracuseStep 1691567 = 2537351) B2537351
theorem B2854831 : Blo 1691546 2854831 := bstep (se 1 (by rfl) ⟨2141123, by rfl⟩ : syracuseStep 2854831 = 4282247) B4282247
theorem B5713847 : Blo 1691546 5713847 := bstep (se 1 (by rfl) ⟨4285385, by rfl⟩ : syracuseStep 5713847 = 8570771) B8570771
theorem B1691591 : Blo 1691546 1691591 := bstep (se 1 (by rfl) ⟨1268693, by rfl⟩ : syracuseStep 1691591 = 2537387) B2537387
theorem B11579345 : Blo 1691546 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B1691611 : Blo 1691546 1691611 := bstep (se 1 (by rfl) ⟨1268708, by rfl⟩ : syracuseStep 1691611 = 2537417) B2537417
theorem B2854919 : Blo 1691546 2854919 := bstep (se 1 (by rfl) ⟨2141189, by rfl⟩ : syracuseStep 2854919 = 4282379) B4282379
theorem B1691687 : Blo 1691546 1691687 := bstep (se 1 (by rfl) ⟨1268765, by rfl⟩ : syracuseStep 1691687 = 2537531) B2537531
theorem B1691727 : Blo 1691546 1691727 := bstep (se 1 (by rfl) ⟨1268795, by rfl⟩ : syracuseStep 1691727 = 2537591) B2537591
theorem B1904719 : Blo 1691546 1904719 := bstep (se 1 (by rfl) ⟨1428539, by rfl⟩ : syracuseStep 1904719 = 2857079) B2857079
theorem B1691743 : Blo 1691546 1691743 := bstep (se 1 (by rfl) ⟨1268807, by rfl⟩ : syracuseStep 1691743 = 2537615) B2537615
theorem B1691771 : Blo 1691546 1691771 := bstep (se 1 (by rfl) ⟨1268828, by rfl⟩ : syracuseStep 1691771 = 2537657) B2537657
theorem B19271843 : Blo 1691546 19271843 := bstep (se 1 (by rfl) ⟨14453882, by rfl⟩ : syracuseStep 19271843 = 28907765) B28907765
theorem B1691823 : Blo 1691546 1691823 := bstep (se 1 (by rfl) ⟨1268867, by rfl⟩ : syracuseStep 1691823 = 2537735) B2537735
theorem B1691847 : Blo 1691546 1691847 := bstep (se 1 (by rfl) ⟨1268885, by rfl⟩ : syracuseStep 1691847 = 2537771) B2537771
theorem B1691867 : Blo 1691546 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B1691943 : Blo 1691546 1691943 := bstep (se 1 (by rfl) ⟨1268957, by rfl⟩ : syracuseStep 1691943 = 2537915) B2537915
theorem B1691983 : Blo 1691546 1691983 := bstep (se 1 (by rfl) ⟨1268987, by rfl⟩ : syracuseStep 1691983 = 2537975) B2537975
theorem B1691999 : Blo 1691546 1691999 := bstep (se 1 (by rfl) ⟨1268999, by rfl⟩ : syracuseStep 1691999 = 2537999) B2537999
theorem B2855263 : Blo 1691546 2855263 := bstep (se 1 (by rfl) ⟨2141447, by rfl⟩ : syracuseStep 2855263 = 4282895) B4282895
theorem B6426985 : Blo 1691546 6426985 := bstep (se 2 (by rfl) ⟨2410119, by rfl⟩ : syracuseStep 6426985 = 4820239) B4820239
theorem B1692027 : Blo 1691546 1692027 := bstep (se 1 (by rfl) ⟨1269020, by rfl⟩ : syracuseStep 1692027 = 2538041) B2538041
theorem B9146753 : Blo 1691546 9146753 := bstep (se 2 (by rfl) ⟨3430032, by rfl⟩ : syracuseStep 9146753 = 6860065) B6860065
theorem B6861185 : Blo 1691546 6861185 := bstep (se 2 (by rfl) ⟨2572944, by rfl⟩ : syracuseStep 6861185 = 5145889) B5145889
theorem B73216385 : Blo 1691546 73216385 := bstep (se 2 (by rfl) ⟨27456144, by rfl⟩ : syracuseStep 73216385 = 54912289) B54912289
theorem B18559361 : Blo 1691546 18559361 := bstep (se 2 (by rfl) ⟨6959760, by rfl⟩ : syracuseStep 18559361 = 13919521) B13919521
theorem B167006609 : Blo 1691546 167006609 := bstep (se 2 (by rfl) ⟨62627478, by rfl⟩ : syracuseStep 167006609 = 125254957) B125254957
theorem B1692079 : Blo 1691546 1692079 := bstep (se 1 (by rfl) ⟨1269059, by rfl⟩ : syracuseStep 1692079 = 2538119) B2538119
theorem B2855351 : Blo 1691546 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B1692103 : Blo 1691546 1692103 := bstep (se 1 (by rfl) ⟨1269077, by rfl⟩ : syracuseStep 1692103 = 2538155) B2538155
theorem B1692123 : Blo 1691546 1692123 := bstep (se 1 (by rfl) ⟨1269092, by rfl⟩ : syracuseStep 1692123 = 2538185) B2538185
theorem B1905115 : Blo 1691546 1905115 := bstep (se 1 (by rfl) ⟨1428836, by rfl⟩ : syracuseStep 1905115 = 2857673) B2857673
theorem B5714441 : Blo 1691546 5714441 := bstep (se 2 (by rfl) ⟨2142915, by rfl⟩ : syracuseStep 5714441 = 4285831) B4285831
theorem B1692199 : Blo 1691546 1692199 := bstep (se 1 (by rfl) ⟨1269149, by rfl⟩ : syracuseStep 1692199 = 2538299) B2538299
theorem B7328315 : Blo 1691546 7328315 := bstep (se 1 (by rfl) ⟨5496236, by rfl⟩ : syracuseStep 7328315 = 10992473) B10992473
theorem B7721531 : Blo 1691546 7721531 := bstep (se 1 (by rfl) ⟨5791148, by rfl⟩ : syracuseStep 7721531 = 11582297) B11582297
theorem B1692239 : Blo 1691546 1692239 := bstep (se 1 (by rfl) ⟨1269179, by rfl⟩ : syracuseStep 1692239 = 2538359) B2538359
theorem B1692255 : Blo 1691546 1692255 := bstep (se 1 (by rfl) ⟨1269191, by rfl⟩ : syracuseStep 1692255 = 2538383) B2538383
theorem B1692283 : Blo 1691546 1692283 := bstep (se 1 (by rfl) ⟨1269212, by rfl⟩ : syracuseStep 1692283 = 2538425) B2538425
theorem B6427259 : Blo 1691546 6427259 := bstep (se 1 (by rfl) ⟨4820444, by rfl⟩ : syracuseStep 6427259 = 9640889) B9640889
theorem B1692335 : Blo 1691546 1692335 := bstep (se 1 (by rfl) ⟨1269251, by rfl⟩ : syracuseStep 1692335 = 2538503) B2538503
theorem B1692359 : Blo 1691546 1692359 := bstep (se 1 (by rfl) ⟨1269269, by rfl⟩ : syracuseStep 1692359 = 2538539) B2538539
theorem B1692379 : Blo 1691546 1692379 := bstep (se 1 (by rfl) ⟨1269284, by rfl⟩ : syracuseStep 1692379 = 2538569) B2538569
theorem B1692455 : Blo 1691546 1692455 := bstep (se 1 (by rfl) ⟨1269341, by rfl⟩ : syracuseStep 1692455 = 2538683) B2538683
theorem B1692495 : Blo 1691546 1692495 := bstep (se 1 (by rfl) ⟨1269371, by rfl⟩ : syracuseStep 1692495 = 2538743) B2538743
theorem B1692511 : Blo 1691546 1692511 := bstep (se 1 (by rfl) ⟨1269383, by rfl⟩ : syracuseStep 1692511 = 2538767) B2538767
theorem B20386667 : Blo 1691546 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B1692539 : Blo 1691546 1692539 := bstep (se 1 (by rfl) ⟨1269404, by rfl⟩ : syracuseStep 1692539 = 2538809) B2538809
theorem B10843055 : Blo 1691546 10843055 := bstep (se 1 (by rfl) ⟨8132291, by rfl⟩ : syracuseStep 10843055 = 16264583) B16264583
theorem B1692591 : Blo 1691546 1692591 := bstep (se 1 (by rfl) ⟨1269443, by rfl⟩ : syracuseStep 1692591 = 2538887) B2538887
theorem B3806135 : Blo 1691546 3806135 := bstep (se 1 (by rfl) ⟨2854601, by rfl⟩ : syracuseStep 3806135 = 5709203) B5709203
theorem B5493691 : Blo 1691546 5493691 := bstep (se 1 (by rfl) ⟨4120268, by rfl⟩ : syracuseStep 5493691 = 8240537) B8240537
theorem B1692615 : Blo 1691546 1692615 := bstep (se 1 (by rfl) ⟨1269461, by rfl⟩ : syracuseStep 1692615 = 2538923) B2538923
theorem B1692635 : Blo 1691546 1692635 := bstep (se 1 (by rfl) ⟨1269476, by rfl⟩ : syracuseStep 1692635 = 2538953) B2538953
theorem B2855945 : Blo 1691546 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B1692711 : Blo 1691546 1692711 := bstep (se 1 (by rfl) ⟨1269533, by rfl⟩ : syracuseStep 1692711 = 2539067) B2539067
theorem B1692751 : Blo 1691546 1692751 := bstep (se 1 (by rfl) ⟨1269563, by rfl⟩ : syracuseStep 1692751 = 2539127) B2539127
theorem B1692767 : Blo 1691546 1692767 := bstep (se 1 (by rfl) ⟨1269575, by rfl⟩ : syracuseStep 1692767 = 2539151) B2539151
theorem B1692795 : Blo 1691546 1692795 := bstep (se 1 (by rfl) ⟨1269596, by rfl⟩ : syracuseStep 1692795 = 2539193) B2539193
theorem B7230617 : Blo 1691546 7230617 := bstep (se 2 (by rfl) ⟨2711481, by rfl⟩ : syracuseStep 7230617 = 5422963) B5422963
theorem B58619051 : Blo 1691546 58619051 := bstep (se 1 (by rfl) ⟨43964288, by rfl⟩ : syracuseStep 58619051 = 87928577) B87928577
theorem B2856107 : Blo 1691546 2856107 := bstep (se 1 (by rfl) ⟨2142080, by rfl⟩ : syracuseStep 2856107 = 4284161) B4284161
theorem B1692847 : Blo 1691546 1692847 := bstep (se 1 (by rfl) ⟨1269635, by rfl⟩ : syracuseStep 1692847 = 2539271) B2539271
theorem B1692871 : Blo 1691546 1692871 := bstep (se 1 (by rfl) ⟨1269653, by rfl⟩ : syracuseStep 1692871 = 2539307) B2539307
theorem B1692891 : Blo 1691546 1692891 := bstep (se 1 (by rfl) ⟨1269668, by rfl⟩ : syracuseStep 1692891 = 2539337) B2539337
theorem B14464271 : Blo 1691546 14464271 := bstep (se 1 (by rfl) ⟨10848203, by rfl⟩ : syracuseStep 14464271 = 21696407) B21696407
theorem B1692967 : Blo 1691546 1692967 := bstep (se 1 (by rfl) ⟨1269725, by rfl⟩ : syracuseStep 1692967 = 2539451) B2539451
theorem B1693007 : Blo 1691546 1693007 := bstep (se 1 (by rfl) ⟨1269755, by rfl⟩ : syracuseStep 1693007 = 2539511) B2539511
theorem B1693023 : Blo 1691546 1693023 := bstep (se 1 (by rfl) ⟨1269767, by rfl⟩ : syracuseStep 1693023 = 2539535) B2539535
theorem B5715305 : Blo 1691546 5715305 := bstep (se 2 (by rfl) ⟨2143239, by rfl⟩ : syracuseStep 5715305 = 4286479) B4286479
theorem B1693051 : Blo 1691546 1693051 := bstep (se 1 (by rfl) ⟨1269788, by rfl⟩ : syracuseStep 1693051 = 2539577) B2539577
theorem B10433917 : Blo 1691546 10433917 := bstep (se 3 (by rfl) ⟨1956359, by rfl⟩ : syracuseStep 10433917 = 3912719) B3912719
theorem B12539279 : Blo 1691546 12539279 := bstep (se 1 (by rfl) ⟨9404459, by rfl⟩ : syracuseStep 12539279 = 18808919) B18808919
theorem B1693103 : Blo 1691546 1693103 := bstep (se 1 (by rfl) ⟨1269827, by rfl⟩ : syracuseStep 1693103 = 2539655) B2539655
theorem B1693127 : Blo 1691546 1693127 := bstep (se 1 (by rfl) ⟨1269845, by rfl⟩ : syracuseStep 1693127 = 2539691) B2539691
theorem B8566235 : Blo 1691546 8566235 := bstep (se 1 (by rfl) ⟨6424676, by rfl⟩ : syracuseStep 8566235 = 12849353) B12849353
theorem B34739675 : Blo 1691546 34739675 := bstep (se 1 (by rfl) ⟨26054756, by rfl⟩ : syracuseStep 34739675 = 52109513) B52109513
theorem B1693147 : Blo 1691546 1693147 := bstep (se 1 (by rfl) ⟨1269860, by rfl⟩ : syracuseStep 1693147 = 2539721) B2539721
theorem B3806729 : Blo 1691546 3806729 := bstep (se 2 (by rfl) ⟨1427523, by rfl⟩ : syracuseStep 3806729 = 2855047) B2855047
theorem B1693223 : Blo 1691546 1693223 := bstep (se 1 (by rfl) ⟨1269917, by rfl⟩ : syracuseStep 1693223 = 2539835) B2539835
theorem B2856505 : Blo 1691546 2856505 := bstep (se 2 (by rfl) ⟨1071189, by rfl⟩ : syracuseStep 2856505 = 2142379) B2142379
theorem B1693263 : Blo 1691546 1693263 := bstep (se 1 (by rfl) ⟨1269947, by rfl⟩ : syracuseStep 1693263 = 2539895) B2539895
theorem B1693279 : Blo 1691546 1693279 := bstep (se 1 (by rfl) ⟨1269959, by rfl⟩ : syracuseStep 1693279 = 2539919) B2539919
theorem B12850811 : Blo 1691546 12850811 := bstep (se 1 (by rfl) ⟨9638108, by rfl⟩ : syracuseStep 12850811 = 19276217) B19276217
theorem B1693307 : Blo 1691546 1693307 := bstep (se 1 (by rfl) ⟨1269980, by rfl⟩ : syracuseStep 1693307 = 2539961) B2539961
theorem B1693359 : Blo 1691546 1693359 := bstep (se 1 (by rfl) ⟨1270019, by rfl⟩ : syracuseStep 1693359 = 2540039) B2540039
theorem B4282055 : Blo 1691546 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B2856647 : Blo 1691546 2856647 := bstep (se 1 (by rfl) ⟨2142485, by rfl⟩ : syracuseStep 2856647 = 4284971) B4284971
theorem B1693383 : Blo 1691546 1693383 := bstep (se 1 (by rfl) ⟨1270037, by rfl⟩ : syracuseStep 1693383 = 2540075) B2540075
theorem B1693403 : Blo 1691546 1693403 := bstep (se 1 (by rfl) ⟨1270052, by rfl⟩ : syracuseStep 1693403 = 2540105) B2540105
theorem B4282105 : Blo 1691546 4282105 := bstep (se 2 (by rfl) ⟨1605789, by rfl⟩ : syracuseStep 4282105 = 3211579) B3211579
theorem B1693479 : Blo 1691546 1693479 := bstep (se 1 (by rfl) ⟨1270109, by rfl⟩ : syracuseStep 1693479 = 2540219) B2540219
theorem B1693519 : Blo 1691546 1693519 := bstep (se 1 (by rfl) ⟨1270139, by rfl⟩ : syracuseStep 1693519 = 2540279) B2540279
theorem B3807071 : Blo 1691546 3807071 := bstep (se 1 (by rfl) ⟨2855303, by rfl⟩ : syracuseStep 3807071 = 5710607) B5710607
theorem B1693535 : Blo 1691546 1693535 := bstep (se 1 (by rfl) ⟨1270151, by rfl⟩ : syracuseStep 1693535 = 2540303) B2540303
theorem B2537321 : Blo 1691546 2537321 := bstep (se 2 (by rfl) ⟨951495, by rfl⟩ : syracuseStep 2537321 = 1902991) B1902991
theorem B2856809 : Blo 1691546 2856809 := bstep (se 2 (by rfl) ⟨1071303, by rfl⟩ : syracuseStep 2856809 = 2142607) B2142607
theorem B2537399 : Blo 1691546 2537399 := bstep (se 1 (by rfl) ⟨1903049, by rfl⟩ : syracuseStep 2537399 = 3806099) B3806099
theorem B8566721 : Blo 1691546 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B2537435 : Blo 1691546 2537435 := bstep (se 1 (by rfl) ⟨1903076, by rfl⟩ : syracuseStep 2537435 = 3806153) B3806153
theorem B3807251 : Blo 1691546 3807251 := bstep (se 1 (by rfl) ⟨2855438, by rfl⟩ : syracuseStep 3807251 = 5710877) B5710877
theorem B2857207 : Blo 1691546 2857207 := bstep (se 1 (by rfl) ⟨2142905, by rfl⟩ : syracuseStep 2857207 = 4285811) B4285811
theorem B5421323 : Blo 1691546 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B21698867 : Blo 1691546 21698867 := bstep (se 1 (by rfl) ⟨16274150, by rfl⟩ : syracuseStep 21698867 = 32548301) B32548301
theorem B3807593 : Blo 1691546 3807593 := bstep (se 2 (by rfl) ⟨1427847, by rfl⟩ : syracuseStep 3807593 = 2855695) B2855695
theorem B4282753 : Blo 1691546 4282753 := bstep (se 2 (by rfl) ⟨1606032, by rfl⟩ : syracuseStep 4282753 = 3212065) B3212065
theorem B2537903 : Blo 1691546 2537903 := bstep (se 1 (by rfl) ⟨1903427, by rfl⟩ : syracuseStep 2537903 = 3806855) B3806855
theorem B2857403 : Blo 1691546 2857403 := bstep (se 1 (by rfl) ⟨2143052, by rfl⟩ : syracuseStep 2857403 = 4286105) B4286105
theorem B13728203 : Blo 1691546 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B2537993 : Blo 1691546 2537993 := bstep (se 2 (by rfl) ⟨951747, by rfl⟩ : syracuseStep 2537993 = 1903495) B1903495
theorem B9640457 : Blo 1691546 9640457 := bstep (se 2 (by rfl) ⟨3615171, by rfl⟩ : syracuseStep 9640457 = 7230343) B7230343
theorem B2538023 : Blo 1691546 2538023 := bstep (se 1 (by rfl) ⟨1903517, by rfl⟩ : syracuseStep 2538023 = 3807035) B3807035
theorem B2857511 : Blo 1691546 2857511 := bstep (se 1 (by rfl) ⟨2143133, by rfl⟩ : syracuseStep 2857511 = 4286267) B4286267
theorem B2538107 : Blo 1691546 2538107 := bstep (se 1 (by rfl) ⟨1903580, by rfl⟩ : syracuseStep 2538107 = 3807161) B3807161
theorem B2538233 : Blo 1691546 2538233 := bstep (se 2 (by rfl) ⟨951837, by rfl⟩ : syracuseStep 2538233 = 1903675) B1903675
theorem B2857801 : Blo 1691546 2857801 := bstep (se 2 (by rfl) ⟨1071675, by rfl⟩ : syracuseStep 2857801 = 2143351) B2143351
theorem B2538335 : Blo 1691546 2538335 := bstep (se 1 (by rfl) ⟨1903751, by rfl⟩ : syracuseStep 2538335 = 3807503) B3807503
theorem B2538347 : Blo 1691546 2538347 := bstep (se 1 (by rfl) ⟨1903760, by rfl⟩ : syracuseStep 2538347 = 3807521) B3807521
theorem B2857835 : Blo 1691546 2857835 := bstep (se 1 (by rfl) ⟨2143376, by rfl⟩ : syracuseStep 2857835 = 4286753) B4286753
theorem B6511535 : Blo 1691546 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B3808187 : Blo 1691546 3808187 := bstep (se 1 (by rfl) ⟨2856140, by rfl⟩ : syracuseStep 3808187 = 5712281) B5712281
theorem B3808313 : Blo 1691546 3808313 := bstep (se 2 (by rfl) ⟨1428117, by rfl⟩ : syracuseStep 3808313 = 2856235) B2856235
theorem B2538575 : Blo 1691546 2538575 := bstep (se 1 (by rfl) ⟨1903931, by rfl⟩ : syracuseStep 2538575 = 3807863) B3807863
theorem B4283563 : Blo 1691546 4283563 := bstep (se 1 (by rfl) ⟨3212672, by rfl⟩ : syracuseStep 4283563 = 6425345) B6425345
theorem B2538695 : Blo 1691546 2538695 := bstep (se 1 (by rfl) ⟨1904021, by rfl⟩ : syracuseStep 2538695 = 3808043) B3808043
theorem B17603831 : Blo 1691546 17603831 := bstep (se 1 (by rfl) ⟨13202873, by rfl⟩ : syracuseStep 17603831 = 26405747) B26405747
theorem B9641207 : Blo 1691546 9641207 := bstep (se 1 (by rfl) ⟨7230905, by rfl⟩ : syracuseStep 9641207 = 14461811) B14461811
theorem B2538857 : Blo 1691546 2538857 := bstep (se 2 (by rfl) ⟨952071, by rfl⟩ : syracuseStep 2538857 = 1904143) B1904143
theorem B3808655 : Blo 1691546 3808655 := bstep (se 1 (by rfl) ⟨2856491, by rfl⟩ : syracuseStep 3808655 = 5712983) B5712983
theorem B9641389 : Blo 1691546 9641389 := bstep (se 3 (by rfl) ⟨1807760, by rfl⟩ : syracuseStep 9641389 = 3615521) B3615521
theorem B2538935 : Blo 1691546 2538935 := bstep (se 1 (by rfl) ⟨1904201, by rfl⟩ : syracuseStep 2538935 = 3808403) B3808403
theorem B5709257 : Blo 1691546 5709257 := bstep (se 2 (by rfl) ⟨2140971, by rfl⟩ : syracuseStep 5709257 = 4281943) B4281943
theorem B4283867 : Blo 1691546 4283867 := bstep (se 1 (by rfl) ⟨3212900, by rfl⟩ : syracuseStep 4283867 = 6425801) B6425801
theorem B2538971 : Blo 1691546 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B3808979 : Blo 1691546 3808979 := bstep (se 1 (by rfl) ⟨2856734, by rfl⟩ : syracuseStep 3808979 = 5713469) B5713469
theorem B5709527 : Blo 1691546 5709527 := bstep (se 1 (by rfl) ⟨4282145, by rfl⟩ : syracuseStep 5709527 = 8564291) B8564291
theorem B7331543 : Blo 1691546 7331543 := bstep (se 1 (by rfl) ⟨5498657, by rfl⟩ : syracuseStep 7331543 = 10997315) B10997315
theorem B26066819 : Blo 1691546 26066819 := bstep (se 1 (by rfl) ⟨19550114, by rfl⟩ : syracuseStep 26066819 = 39100229) B39100229
theorem B5709743 : Blo 1691546 5709743 := bstep (se 1 (by rfl) ⟨4282307, by rfl⟩ : syracuseStep 5709743 = 8564615) B8564615
theorem B2539439 : Blo 1691546 2539439 := bstep (se 1 (by rfl) ⟨1904579, by rfl⟩ : syracuseStep 2539439 = 3809159) B3809159
theorem B9641915 : Blo 1691546 9641915 := bstep (se 1 (by rfl) ⟨7231436, by rfl⟩ : syracuseStep 9641915 = 14462873) B14462873
theorem B2539625 : Blo 1691546 2539625 := bstep (se 2 (by rfl) ⟨952359, by rfl⟩ : syracuseStep 2539625 = 1904719) B1904719
theorem B111337739 : Blo 1691546 111337739 := bstep (se 1 (by rfl) ⟨83503304, by rfl⟩ : syracuseStep 111337739 = 167006609) B167006609
theorem B4284697 : Blo 1691546 4284697 := bstep (se 2 (by rfl) ⟨1606761, by rfl⟩ : syracuseStep 4284697 = 3213523) B3213523
theorem B3809609 : Blo 1691546 3809609 := bstep (se 2 (by rfl) ⟨1428603, by rfl⟩ : syracuseStep 3809609 = 2857207) B2857207
theorem B3809627 : Blo 1691546 3809627 := bstep (se 1 (by rfl) ⟨2857220, by rfl⟩ : syracuseStep 3809627 = 5714441) B5714441
theorem B4284839 : Blo 1691546 4284839 := bstep (se 1 (by rfl) ⟨3213629, by rfl⟩ : syracuseStep 4284839 = 6427259) B6427259
theorem B2539943 : Blo 1691546 2539943 := bstep (se 1 (by rfl) ⟨1904957, by rfl⟩ : syracuseStep 2539943 = 3809915) B3809915
theorem B8569313 : Blo 1691546 8569313 := bstep (se 2 (by rfl) ⟨3213492, by rfl⟩ : syracuseStep 8569313 = 6426985) B6426985
theorem B2540027 : Blo 1691546 2540027 := bstep (se 1 (by rfl) ⟨1905020, by rfl⟩ : syracuseStep 2540027 = 3810041) B3810041
theorem B5710337 : Blo 1691546 5710337 := bstep (se 2 (by rfl) ⟨2141376, by rfl⟩ : syracuseStep 5710337 = 4282753) B4282753
theorem B4285001 : Blo 1691546 4285001 := bstep (se 2 (by rfl) ⟨1606875, by rfl⟩ : syracuseStep 4285001 = 3213751) B3213751
theorem B3211883 : Blo 1691546 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B2540153 : Blo 1691546 2540153 := bstep (se 2 (by rfl) ⟨952557, by rfl⟩ : syracuseStep 2540153 = 1905115) B1905115
theorem B2540207 : Blo 1691546 2540207 := bstep (se 1 (by rfl) ⟨1905155, by rfl⟩ : syracuseStep 2540207 = 3810311) B3810311
theorem B2540255 : Blo 1691546 2540255 := bstep (se 1 (by rfl) ⟨1905191, by rfl⟩ : syracuseStep 2540255 = 3810383) B3810383
theorem B3212111 : Blo 1691546 3212111 := bstep (se 1 (by rfl) ⟨2409083, by rfl⟩ : syracuseStep 3212111 = 4818167) B4818167
theorem B9642847 : Blo 1691546 9642847 := bstep (se 1 (by rfl) ⟨7232135, by rfl⟩ : syracuseStep 9642847 = 14464271) B14464271
theorem B3810203 : Blo 1691546 3810203 := bstep (se 1 (by rfl) ⟨2857652, by rfl⟩ : syracuseStep 3810203 = 5715305) B5715305
theorem B5710823 : Blo 1691546 5710823 := bstep (se 1 (by rfl) ⟨4283117, by rfl⟩ : syracuseStep 5710823 = 8566235) B8566235
theorem B23159783 : Blo 1691546 23159783 := bstep (se 1 (by rfl) ⟨17369837, by rfl⟩ : syracuseStep 23159783 = 34739675) B34739675
theorem B3810401 : Blo 1691546 3810401 := bstep (se 2 (by rfl) ⟨1428900, by rfl⟩ : syracuseStep 3810401 = 2857801) B2857801
theorem B7226567 : Blo 1691546 7226567 := bstep (se 1 (by rfl) ⟨5419925, by rfl⟩ : syracuseStep 7226567 = 10839851) B10839851
theorem B7324921 : Blo 1691546 7324921 := bstep (se 2 (by rfl) ⟨2746845, by rfl⟩ : syracuseStep 7324921 = 5493691) B5493691
theorem B5711147 : Blo 1691546 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B36619607 : Blo 1691546 36619607 := bstep (se 1 (by rfl) ⟨27464705, by rfl⟩ : syracuseStep 36619607 = 54929411) B54929411
theorem B9643373 : Blo 1691546 9643373 := bstep (se 3 (by rfl) ⟨1808132, by rfl⟩ : syracuseStep 9643373 = 3616265) B3616265
theorem B10847641 : Blo 1691546 10847641 := bstep (se 2 (by rfl) ⟨4067865, by rfl⟩ : syracuseStep 10847641 = 8135731) B8135731
theorem B3614215 : Blo 1691546 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B5711417 : Blo 1691546 5711417 := bstep (se 2 (by rfl) ⟨2141781, by rfl⟩ : syracuseStep 5711417 = 4283563) B4283563
theorem B9152135 : Blo 1691546 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B4065079 : Blo 1691546 4065079 := bstep (se 1 (by rfl) ⟨3048809, by rfl⟩ : syracuseStep 4065079 = 6097619) B6097619
theorem B7718743 : Blo 1691546 7718743 := bstep (se 1 (by rfl) ⟨5789057, by rfl⟩ : syracuseStep 7718743 = 11578115) B11578115
theorem B12855185 : Blo 1691546 12855185 := bstep (se 2 (by rfl) ⟨4820694, by rfl⟩ : syracuseStep 12855185 = 9641389) B9641389
theorem B5949575 : Blo 1691546 5949575 := bstep (se 1 (by rfl) ⟨4462181, by rfl⟩ : syracuseStep 5949575 = 8924363) B8924363
theorem B6424829 : Blo 1691546 6424829 := bstep (se 3 (by rfl) ⟨1204655, by rfl⟩ : syracuseStep 6424829 = 2409311) B2409311
theorem B54364445 : Blo 1691546 54364445 := bstep (se 3 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 54364445 = 20386667) B20386667
theorem B69511517 : Blo 1691546 69511517 := bstep (se 3 (by rfl) ⟨13033409, by rfl⟩ : syracuseStep 69511517 = 26066819) B26066819
theorem B4180391 : Blo 1691546 4180391 := bstep (se 1 (by rfl) ⟨3135293, by rfl⟩ : syracuseStep 4180391 = 6270587) B6270587
theorem B24398309 : Blo 1691546 24398309 := bstep (se 4 (by rfl) ⟨2287341, by rfl⟩ : syracuseStep 24398309 = 4574683) B4574683
theorem B1903099 : Blo 1691546 1903099 := bstep (se 1 (by rfl) ⟨1427324, by rfl⟩ : syracuseStep 1903099 = 2854649) B2854649
theorem B7227899 : Blo 1691546 7227899 := bstep (se 1 (by rfl) ⟨5420924, by rfl⟩ : syracuseStep 7227899 = 10841849) B10841849
theorem B7227967 : Blo 1691546 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B7719563 : Blo 1691546 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B1903279 : Blo 1691546 1903279 := bstep (se 1 (by rfl) ⟨1427459, by rfl⟩ : syracuseStep 1903279 = 2854919) B2854919
theorem B8571581 : Blo 1691546 8571581 := bstep (se 3 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 8571581 = 3214343) B3214343
theorem B10840823 : Blo 1691546 10840823 := bstep (se 1 (by rfl) ⟨8130617, by rfl⟩ : syracuseStep 10840823 = 16261235) B16261235
theorem B5712659 : Blo 1691546 5712659 := bstep (se 1 (by rfl) ⟨4284494, by rfl⟩ : syracuseStep 5712659 = 8568989) B8568989
theorem B12847895 : Blo 1691546 12847895 := bstep (se 1 (by rfl) ⟨9635921, by rfl⟩ : syracuseStep 12847895 = 19271843) B19271843
theorem B2141083 : Blo 1691546 2141083 := bstep (se 1 (by rfl) ⟨1605812, by rfl⟩ : syracuseStep 2141083 = 3211625) B3211625
theorem B6097835 : Blo 1691546 6097835 := bstep (se 1 (by rfl) ⟨4573376, by rfl⟩ : syracuseStep 6097835 = 9146753) B9146753
theorem B4574123 : Blo 1691546 4574123 := bstep (se 1 (by rfl) ⟨3430592, by rfl⟩ : syracuseStep 4574123 = 6861185) B6861185
theorem B48810923 : Blo 1691546 48810923 := bstep (se 1 (by rfl) ⟨36608192, by rfl⟩ : syracuseStep 48810923 = 73216385) B73216385
theorem B12372907 : Blo 1691546 12372907 := bstep (se 1 (by rfl) ⟨9279680, by rfl⟩ : syracuseStep 12372907 = 18559361) B18559361
theorem B8563643 : Blo 1691546 8563643 := bstep (se 1 (by rfl) ⟨6422732, by rfl⟩ : syracuseStep 8563643 = 12845465) B12845465
theorem B1903567 : Blo 1691546 1903567 := bstep (se 1 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 1903567 = 2855351) B2855351
theorem B4885543 : Blo 1691546 4885543 := bstep (se 1 (by rfl) ⟨3664157, by rfl⟩ : syracuseStep 4885543 = 7328315) B7328315
theorem B5147687 : Blo 1691546 5147687 := bstep (se 1 (by rfl) ⟨3860765, by rfl⟩ : syracuseStep 5147687 = 7721531) B7721531
theorem B7228703 : Blo 1691546 7228703 := bstep (se 1 (by rfl) ⟨5421527, by rfl⟩ : syracuseStep 7228703 = 10843055) B10843055
theorem B1903963 : Blo 1691546 1903963 := bstep (se 1 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 1903963 = 2855945) B2855945
theorem B4820411 : Blo 1691546 4820411 := bstep (se 1 (by rfl) ⟨3615308, by rfl⟩ : syracuseStep 4820411 = 7230617) B7230617
theorem B39079367 : Blo 1691546 39079367 := bstep (se 1 (by rfl) ⟨29309525, by rfl⟩ : syracuseStep 39079367 = 58619051) B58619051
theorem B1904071 : Blo 1691546 1904071 := bstep (se 1 (by rfl) ⟨1428053, by rfl⟩ : syracuseStep 1904071 = 2856107) B2856107
theorem B8359519 : Blo 1691546 8359519 := bstep (se 1 (by rfl) ⟨6269639, by rfl⟩ : syracuseStep 8359519 = 12539279) B12539279
theorem B5713523 : Blo 1691546 5713523 := bstep (se 1 (by rfl) ⟨4285142, by rfl⟩ : syracuseStep 5713523 = 8570285) B8570285
theorem B2854703 : Blo 1691546 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B1904431 : Blo 1691546 1904431 := bstep (se 1 (by rfl) ⟨1428323, by rfl⟩ : syracuseStep 1904431 = 2856647) B2856647
theorem B5713793 : Blo 1691546 5713793 := bstep (se 2 (by rfl) ⟨2142672, by rfl⟩ : syracuseStep 5713793 = 4285345) B4285345
theorem B1691547 : Blo 1691546 1691547 := bstep (se 1 (by rfl) ⟨1268660, by rfl⟩ : syracuseStep 1691547 = 2537321) B2537321
theorem B1904539 : Blo 1691546 1904539 := bstep (se 1 (by rfl) ⟨1428404, by rfl⟩ : syracuseStep 1904539 = 2856809) B2856809
theorem B1691599 : Blo 1691546 1691599 := bstep (se 1 (by rfl) ⟨1268699, by rfl⟩ : syracuseStep 1691599 = 2537399) B2537399
theorem B1691623 : Blo 1691546 1691623 := bstep (se 1 (by rfl) ⟨1268717, by rfl⟩ : syracuseStep 1691623 = 2537435) B2537435
theorem B16265387 : Blo 1691546 16265387 := bstep (se 1 (by rfl) ⟨12199040, by rfl⟩ : syracuseStep 16265387 = 24398081) B24398081
theorem B8564939 : Blo 1691546 8564939 := bstep (se 1 (by rfl) ⟨6423704, by rfl⟩ : syracuseStep 8564939 = 12847409) B12847409
theorem B12857615 : Blo 1691546 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B1691935 : Blo 1691546 1691935 := bstep (se 1 (by rfl) ⟨1268951, by rfl⟩ : syracuseStep 1691935 = 2537903) B2537903
theorem B1904935 : Blo 1691546 1904935 := bstep (se 1 (by rfl) ⟨1428701, by rfl⟩ : syracuseStep 1904935 = 2857403) B2857403
theorem B1691995 : Blo 1691546 1691995 := bstep (se 1 (by rfl) ⟨1268996, by rfl⟩ : syracuseStep 1691995 = 2537993) B2537993
theorem B6426971 : Blo 1691546 6426971 := bstep (se 1 (by rfl) ⟨4820228, by rfl⟩ : syracuseStep 6426971 = 9640457) B9640457
theorem B1692015 : Blo 1691546 1692015 := bstep (se 1 (by rfl) ⟨1269011, by rfl⟩ : syracuseStep 1692015 = 2538023) B2538023
theorem B1905007 : Blo 1691546 1905007 := bstep (se 1 (by rfl) ⟨1428755, by rfl⟩ : syracuseStep 1905007 = 2857511) B2857511
theorem B1692071 : Blo 1691546 1692071 := bstep (se 1 (by rfl) ⟨1269053, by rfl⟩ : syracuseStep 1692071 = 2538107) B2538107
theorem B5419489 : Blo 1691546 5419489 := bstep (se 2 (by rfl) ⟨2032308, by rfl⟩ : syracuseStep 5419489 = 4064617) B4064617
theorem B1692155 : Blo 1691546 1692155 := bstep (se 1 (by rfl) ⟨1269116, by rfl⟩ : syracuseStep 1692155 = 2538233) B2538233
theorem B1692223 : Blo 1691546 1692223 := bstep (se 1 (by rfl) ⟨1269167, by rfl⟩ : syracuseStep 1692223 = 2538335) B2538335
theorem B1692231 : Blo 1691546 1692231 := bstep (se 1 (by rfl) ⟨1269173, by rfl⟩ : syracuseStep 1692231 = 2538347) B2538347
theorem B1905223 : Blo 1691546 1905223 := bstep (se 1 (by rfl) ⟨1428917, by rfl⟩ : syracuseStep 1905223 = 2857835) B2857835
theorem B6427289 : Blo 1691546 6427289 := bstep (se 2 (by rfl) ⟨2410233, by rfl⟩ : syracuseStep 6427289 = 4820467) B4820467
theorem B5714603 : Blo 1691546 5714603 := bstep (se 1 (by rfl) ⟨4285952, by rfl⟩ : syracuseStep 5714603 = 8571905) B8571905
theorem B1692383 : Blo 1691546 1692383 := bstep (se 1 (by rfl) ⟨1269287, by rfl⟩ : syracuseStep 1692383 = 2538575) B2538575
theorem B1692463 : Blo 1691546 1692463 := bstep (se 1 (by rfl) ⟨1269347, by rfl⟩ : syracuseStep 1692463 = 2538695) B2538695
theorem B11735887 : Blo 1691546 11735887 := bstep (se 1 (by rfl) ⟨8801915, by rfl⟩ : syracuseStep 11735887 = 17603831) B17603831
theorem B6427471 : Blo 1691546 6427471 := bstep (se 1 (by rfl) ⟨4820603, by rfl⟩ : syracuseStep 6427471 = 9641207) B9641207
theorem B1692571 : Blo 1691546 1692571 := bstep (se 1 (by rfl) ⟨1269428, by rfl⟩ : syracuseStep 1692571 = 2538857) B2538857
theorem B1692623 : Blo 1691546 1692623 := bstep (se 1 (by rfl) ⟨1269467, by rfl⟩ : syracuseStep 1692623 = 2538935) B2538935
theorem B3806171 : Blo 1691546 3806171 := bstep (se 1 (by rfl) ⟨2854628, by rfl⟩ : syracuseStep 3806171 = 5709257) B5709257
theorem B2855911 : Blo 1691546 2855911 := bstep (se 1 (by rfl) ⟨2141933, by rfl⟩ : syracuseStep 2855911 = 4283867) B4283867
theorem B1692647 : Blo 1691546 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B6427745 : Blo 1691546 6427745 := bstep (se 2 (by rfl) ⟨2410404, by rfl⟩ : syracuseStep 6427745 = 4820809) B4820809
theorem B3806351 : Blo 1691546 3806351 := bstep (se 1 (by rfl) ⟨2854763, by rfl⟩ : syracuseStep 3806351 = 5709527) B5709527
theorem B4887695 : Blo 1691546 4887695 := bstep (se 1 (by rfl) ⟨3665771, by rfl⟩ : syracuseStep 4887695 = 7331543) B7331543
theorem B10843283 : Blo 1691546 10843283 := bstep (se 1 (by rfl) ⟨8132462, by rfl⟩ : syracuseStep 10843283 = 16264925) B16264925
theorem B5715143 : Blo 1691546 5715143 := bstep (se 1 (by rfl) ⟨4286357, by rfl⟩ : syracuseStep 5715143 = 8572715) B8572715
theorem B3806441 : Blo 1691546 3806441 := bstep (se 2 (by rfl) ⟨1427415, by rfl⟩ : syracuseStep 3806441 = 2854831) B2854831
theorem B3806495 : Blo 1691546 3806495 := bstep (se 1 (by rfl) ⟨2854871, by rfl⟩ : syracuseStep 3806495 = 5709743) B5709743
theorem B1692959 : Blo 1691546 1692959 := bstep (se 1 (by rfl) ⟨1269719, by rfl⟩ : syracuseStep 1692959 = 2539439) B2539439
theorem B6427943 : Blo 1691546 6427943 := bstep (se 1 (by rfl) ⟨4820957, by rfl⟩ : syracuseStep 6427943 = 9641915) B9641915
theorem B1693019 : Blo 1691546 1693019 := bstep (se 1 (by rfl) ⟨1269764, by rfl⟩ : syracuseStep 1693019 = 2539529) B2539529
theorem B12203369 : Blo 1691546 12203369 := bstep (se 2 (by rfl) ⟨4576263, by rfl⟩ : syracuseStep 12203369 = 9152527) B9152527
theorem B1693039 : Blo 1691546 1693039 := bstep (se 1 (by rfl) ⟨1269779, by rfl⟩ : syracuseStep 1693039 = 2539559) B2539559
theorem B4068731 : Blo 1691546 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B4281761 : Blo 1691546 4281761 := bstep (se 2 (by rfl) ⟨1605660, by rfl⟩ : syracuseStep 4281761 = 3211321) B3211321
theorem B34723235 : Blo 1691546 34723235 := bstep (se 1 (by rfl) ⟨26042426, by rfl⟩ : syracuseStep 34723235 = 52084853) B52084853
theorem B1693095 : Blo 1691546 1693095 := bstep (se 1 (by rfl) ⟨1269821, by rfl⟩ : syracuseStep 1693095 = 2539643) B2539643
theorem B1693179 : Blo 1691546 1693179 := bstep (se 1 (by rfl) ⟨1269884, by rfl⟩ : syracuseStep 1693179 = 2539769) B2539769
theorem B9639431 : Blo 1691546 9639431 := bstep (se 1 (by rfl) ⟨7229573, by rfl⟩ : syracuseStep 9639431 = 14459147) B14459147
theorem B1693247 : Blo 1691546 1693247 := bstep (se 1 (by rfl) ⟨1269935, by rfl⟩ : syracuseStep 1693247 = 2539871) B2539871
theorem B87987779 : Blo 1691546 87987779 := bstep (se 1 (by rfl) ⟨65990834, by rfl⟩ : syracuseStep 87987779 = 131981669) B131981669
theorem B1693255 : Blo 1691546 1693255 := bstep (se 1 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 1693255 = 2539883) B2539883
theorem B1693407 : Blo 1691546 1693407 := bstep (se 1 (by rfl) ⟨1270055, by rfl⟩ : syracuseStep 1693407 = 2540111) B2540111
theorem B3807017 : Blo 1691546 3807017 := bstep (se 2 (by rfl) ⟨1427631, by rfl⟩ : syracuseStep 3807017 = 2855263) B2855263
theorem B1693487 : Blo 1691546 1693487 := bstep (se 1 (by rfl) ⟨1270115, by rfl⟩ : syracuseStep 1693487 = 2540231) B2540231
theorem B4282217 : Blo 1691546 4282217 := bstep (se 2 (by rfl) ⟨1605831, by rfl⟩ : syracuseStep 4282217 = 3211663) B3211663
theorem B2537423 : Blo 1691546 2537423 := bstep (se 1 (by rfl) ⟨1903067, by rfl⟩ : syracuseStep 2537423 = 3806135) B3806135
theorem B24401999 : Blo 1691546 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B2537819 : Blo 1691546 2537819 := bstep (se 1 (by rfl) ⟨1903364, by rfl⟩ : syracuseStep 2537819 = 3806729) B3806729
theorem B8567207 : Blo 1691546 8567207 := bstep (se 1 (by rfl) ⟨6425405, by rfl⟩ : syracuseStep 8567207 = 12850811) B12850811
theorem B131832359 : Blo 1691546 131832359 := bstep (se 1 (by rfl) ⟨98874269, by rfl⟩ : syracuseStep 131832359 = 197748539) B197748539
theorem B2538047 : Blo 1691546 2538047 := bstep (se 1 (by rfl) ⟨1903535, by rfl⟩ : syracuseStep 2538047 = 3807071) B3807071
theorem B8567369 : Blo 1691546 8567369 := bstep (se 2 (by rfl) ⟨3212763, by rfl⟩ : syracuseStep 8567369 = 6425527) B6425527
theorem B2538167 : Blo 1691546 2538167 := bstep (se 1 (by rfl) ⟨1903625, by rfl⟩ : syracuseStep 2538167 = 3807251) B3807251
theorem B3808079 : Blo 1691546 3808079 := bstep (se 1 (by rfl) ⟨2856059, by rfl⟩ : syracuseStep 3808079 = 5712119) B5712119
theorem B14465911 : Blo 1691546 14465911 := bstep (se 1 (by rfl) ⟨10849433, by rfl⟩ : syracuseStep 14465911 = 21698867) B21698867
theorem B6101885 : Blo 1691546 6101885 := bstep (se 3 (by rfl) ⟨1144103, by rfl⟩ : syracuseStep 6101885 = 2288207) B2288207
theorem B26401679 : Blo 1691546 26401679 := bstep (se 1 (by rfl) ⟨19801259, by rfl⟩ : syracuseStep 26401679 = 39602519) B39602519
theorem B2538395 : Blo 1691546 2538395 := bstep (se 1 (by rfl) ⟨1903796, by rfl⟩ : syracuseStep 2538395 = 3807593) B3807593
theorem B3808295 : Blo 1691546 3808295 := bstep (se 1 (by rfl) ⟨2856221, by rfl⟩ : syracuseStep 3808295 = 5712443) B5712443
theorem B13024421 : Blo 1691546 13024421 := bstep (se 4 (by rfl) ⟨1221039, by rfl⟩ : syracuseStep 13024421 = 2442079) B2442079
theorem B3808475 : Blo 1691546 3808475 := bstep (se 1 (by rfl) ⟨2856356, by rfl⟩ : syracuseStep 3808475 = 5712713) B5712713
theorem B4341023 : Blo 1691546 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B2538791 : Blo 1691546 2538791 := bstep (se 1 (by rfl) ⟨1904093, by rfl⟩ : syracuseStep 2538791 = 3808187) B3808187
theorem B55647557 : Blo 1691546 55647557 := bstep (se 4 (by rfl) ⟨5216958, by rfl⟩ : syracuseStep 55647557 = 10433917) B10433917
theorem B2538875 : Blo 1691546 2538875 := bstep (se 1 (by rfl) ⟨1904156, by rfl⟩ : syracuseStep 2538875 = 3808313) B3808313
theorem B3808673 : Blo 1691546 3808673 := bstep (se 2 (by rfl) ⟨1428252, by rfl⟩ : syracuseStep 3808673 = 2856505) B2856505
theorem B2539001 : Blo 1691546 2539001 := bstep (se 2 (by rfl) ⟨952125, by rfl⟩ : syracuseStep 2539001 = 1904251) B1904251
theorem B4283999 : Blo 1691546 4283999 := bstep (se 1 (by rfl) ⟨3212999, by rfl⟩ : syracuseStep 4283999 = 6425999) B6425999
theorem B2539103 : Blo 1691546 2539103 := bstep (se 1 (by rfl) ⟨1904327, by rfl⟩ : syracuseStep 2539103 = 3808655) B3808655
theorem B5709473 : Blo 1691546 5709473 := bstep (se 2 (by rfl) ⟨2141052, by rfl⟩ : syracuseStep 5709473 = 4282105) B4282105
theorem B15449849 : Blo 1691546 15449849 := bstep (se 2 (by rfl) ⟨5793693, by rfl⟩ : syracuseStep 15449849 = 11587387) B11587387
theorem B2539319 : Blo 1691546 2539319 := bstep (se 1 (by rfl) ⟨1904489, by rfl⟩ : syracuseStep 2539319 = 3808979) B3808979
theorem B3809231 : Blo 1691546 3809231 := bstep (se 1 (by rfl) ⟨2856923, by rfl⟩ : syracuseStep 3809231 = 5713847) B5713847
theorem B5709959 : Blo 1691546 5709959 := bstep (se 1 (by rfl) ⟨4282469, by rfl⟩ : syracuseStep 5709959 = 8564939) B8564939
theorem B2539739 : Blo 1691546 2539739 := bstep (se 1 (by rfl) ⟨1904804, by rfl⟩ : syracuseStep 2539739 = 3809609) B3809609
theorem B4284647 : Blo 1691546 4284647 := bstep (se 1 (by rfl) ⟨3213485, by rfl⟩ : syracuseStep 4284647 = 6426971) B6426971
theorem B2539751 : Blo 1691546 2539751 := bstep (se 1 (by rfl) ⟨1904813, by rfl⟩ : syracuseStep 2539751 = 3809627) B3809627
theorem B2539913 : Blo 1691546 2539913 := bstep (se 2 (by rfl) ⟨952467, by rfl⟩ : syracuseStep 2539913 = 1904935) B1904935
theorem B4284859 : Blo 1691546 4284859 := bstep (se 1 (by rfl) ⟨3213644, by rfl⟩ : syracuseStep 4284859 = 6427289) B6427289
theorem B3809735 : Blo 1691546 3809735 := bstep (se 1 (by rfl) ⟨2857301, by rfl⟩ : syracuseStep 3809735 = 5714603) B5714603
theorem B2540009 : Blo 1691546 2540009 := bstep (se 2 (by rfl) ⟨952503, by rfl⟩ : syracuseStep 2540009 = 1905007) B1905007
theorem B2540135 : Blo 1691546 2540135 := bstep (se 1 (by rfl) ⟨1905101, by rfl⟩ : syracuseStep 2540135 = 3810203) B3810203
theorem B7225985 : Blo 1691546 7225985 := bstep (se 2 (by rfl) ⟨2709744, by rfl⟩ : syracuseStep 7225985 = 5419489) B5419489
theorem B4285163 : Blo 1691546 4285163 := bstep (se 1 (by rfl) ⟨3213872, by rfl⟩ : syracuseStep 4285163 = 6427745) B6427745
theorem B2540267 : Blo 1691546 2540267 := bstep (se 1 (by rfl) ⟨1905200, by rfl⟩ : syracuseStep 2540267 = 3810401) B3810401
theorem B2540297 : Blo 1691546 2540297 := bstep (se 2 (by rfl) ⟨952611, by rfl⟩ : syracuseStep 2540297 = 1905223) B1905223
theorem B4817711 : Blo 1691546 4817711 := bstep (se 1 (by rfl) ⟨3613283, by rfl⟩ : syracuseStep 4817711 = 7226567) B7226567
theorem B3810095 : Blo 1691546 3810095 := bstep (se 1 (by rfl) ⟨2857571, by rfl⟩ : syracuseStep 3810095 = 5715143) B5715143
theorem B4285295 : Blo 1691546 4285295 := bstep (se 1 (by rfl) ⟨3213971, by rfl⟩ : syracuseStep 4285295 = 6427943) B6427943
theorem B24413071 : Blo 1691546 24413071 := bstep (se 1 (by rfl) ⟨18309803, by rfl⟩ : syracuseStep 24413071 = 36619607) B36619607
theorem B8135579 : Blo 1691546 8135579 := bstep (se 1 (by rfl) ⟨6101684, by rfl⟩ : syracuseStep 8135579 = 12203369) B12203369
theorem B15647849 : Blo 1691546 15647849 := bstep (se 2 (by rfl) ⟨5867943, by rfl⟩ : syracuseStep 15647849 = 11735887) B11735887
theorem B8569961 : Blo 1691546 8569961 := bstep (se 2 (by rfl) ⟨3213735, by rfl⟩ : syracuseStep 8569961 = 6427471) B6427471
theorem B8570123 : Blo 1691546 8570123 := bstep (se 1 (by rfl) ⟨6427592, by rfl⟩ : syracuseStep 8570123 = 12855185) B12855185
theorem B6514057 : Blo 1691546 6514057 := bstep (se 2 (by rfl) ⟨2442771, by rfl⟩ : syracuseStep 6514057 = 4885543) B4885543
theorem B3966383 : Blo 1691546 3966383 := bstep (se 1 (by rfl) ⟨2974787, by rfl⟩ : syracuseStep 3966383 = 5949575) B5949575
theorem B36242963 : Blo 1691546 36242963 := bstep (se 1 (by rfl) ⟨27182222, by rfl⟩ : syracuseStep 36242963 = 54364445) B54364445
theorem B5711471 : Blo 1691546 5711471 := bstep (se 1 (by rfl) ⟨4283603, by rfl⟩ : syracuseStep 5711471 = 8567207) B8567207
theorem B4818599 : Blo 1691546 4818599 := bstep (se 1 (by rfl) ⟨3613949, by rfl⟩ : syracuseStep 4818599 = 7227899) B7227899
theorem B5711579 : Blo 1691546 5711579 := bstep (se 1 (by rfl) ⟨4283684, by rfl⟩ : syracuseStep 5711579 = 8567369) B8567369
theorem B7227215 : Blo 1691546 7227215 := bstep (se 1 (by rfl) ⟨5420411, by rfl⟩ : syracuseStep 7227215 = 10840823) B10840823
theorem B4065223 : Blo 1691546 4065223 := bstep (se 1 (by rfl) ⟨3048917, by rfl⟩ : syracuseStep 4065223 = 6097835) B6097835
theorem B3049415 : Blo 1691546 3049415 := bstep (se 1 (by rfl) ⟨2287061, by rfl⟩ : syracuseStep 3049415 = 4574123) B4574123
theorem B32540615 : Blo 1691546 32540615 := bstep (se 1 (by rfl) ⟨24405461, by rfl⟩ : syracuseStep 32540615 = 48810923) B48810923
theorem B4818953 : Blo 1691546 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B2894015 : Blo 1691546 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B4819135 : Blo 1691546 4819135 := bstep (se 1 (by rfl) ⟨3614351, by rfl⟩ : syracuseStep 4819135 = 7228703) B7228703
theorem B3213607 : Blo 1691546 3213607 := bstep (se 1 (by rfl) ⟨2410205, by rfl⟩ : syracuseStep 3213607 = 4820411) B4820411
theorem B26052911 : Blo 1691546 26052911 := bstep (se 1 (by rfl) ⟨19539683, by rfl⟩ : syracuseStep 26052911 = 39079367) B39079367
theorem B10291657 : Blo 1691546 10291657 := bstep (se 2 (by rfl) ⟨3859371, by rfl⟩ : syracuseStep 10291657 = 7718743) B7718743
theorem B10299899 : Blo 1691546 10299899 := bstep (se 1 (by rfl) ⟨7724924, by rfl⟩ : syracuseStep 10299899 = 15449849) B15449849
theorem B1903135 : Blo 1691546 1903135 := bstep (se 1 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 1903135 = 2854703) B2854703
theorem B8571743 : Blo 1691546 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B65071997 : Blo 1691546 65071997 := bstep (se 3 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 65071997 = 24401999) B24401999
theorem B5712875 : Blo 1691546 5712875 := bstep (se 1 (by rfl) ⟨4284656, by rfl⟩ : syracuseStep 5712875 = 8569313) B8569313
theorem B5712929 : Blo 1691546 5712929 := bstep (se 2 (by rfl) ⟨2142348, by rfl⟩ : syracuseStep 5712929 = 4284697) B4284697
theorem B2141255 : Blo 1691546 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B2141407 : Blo 1691546 2141407 := bstep (se 1 (by rfl) ⟨1606055, by rfl⟩ : syracuseStep 2141407 = 3212111) B3212111
theorem B9637289 : Blo 1691546 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B7228855 : Blo 1691546 7228855 := bstep (se 1 (by rfl) ⟨5421641, by rfl⟩ : syracuseStep 7228855 = 10843283) B10843283
theorem B2854507 : Blo 1691546 2854507 := bstep (se 1 (by rfl) ⟨2140880, by rfl⟩ : syracuseStep 2854507 = 4281761) B4281761
theorem B10849949 : Blo 1691546 10849949 := bstep (se 3 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 10849949 = 4068731) B4068731
theorem B6426287 : Blo 1691546 6426287 := bstep (se 1 (by rfl) ⟨4819715, by rfl⟩ : syracuseStep 6426287 = 9639431) B9639431
theorem B58658519 : Blo 1691546 58658519 := bstep (se 1 (by rfl) ⟨43993889, by rfl⟩ : syracuseStep 58658519 = 87987779) B87987779
theorem B12857129 : Blo 1691546 12857129 := bstep (se 2 (by rfl) ⟨4821423, by rfl⟩ : syracuseStep 12857129 = 9642847) B9642847
theorem B19287881 : Blo 1691546 19287881 := bstep (se 2 (by rfl) ⟨7232955, by rfl⟩ : syracuseStep 19287881 = 14465911) B14465911
theorem B2854777 : Blo 1691546 2854777 := bstep (se 2 (by rfl) ⟨1070541, by rfl⟩ : syracuseStep 2854777 = 2141083) B2141083
theorem B2854811 : Blo 1691546 2854811 := bstep (se 1 (by rfl) ⟨2141108, by rfl⟩ : syracuseStep 2854811 = 4282217) B4282217
theorem B1691615 : Blo 1691546 1691615 := bstep (se 1 (by rfl) ⟨1268711, by rfl⟩ : syracuseStep 1691615 = 2537423) B2537423
theorem B1691879 : Blo 1691546 1691879 := bstep (se 1 (by rfl) ⟨1268909, by rfl⟩ : syracuseStep 1691879 = 2537819) B2537819
theorem B16265539 : Blo 1691546 16265539 := bstep (se 1 (by rfl) ⟨12199154, by rfl⟩ : syracuseStep 16265539 = 24398309) B24398309
theorem B87888239 : Blo 1691546 87888239 := bstep (se 1 (by rfl) ⟨65916179, by rfl⟩ : syracuseStep 87888239 = 131832359) B131832359
theorem B1692031 : Blo 1691546 1692031 := bstep (se 1 (by rfl) ⟨1269023, by rfl⟩ : syracuseStep 1692031 = 2538047) B2538047
theorem B1692111 : Blo 1691546 1692111 := bstep (se 1 (by rfl) ⟨1269083, by rfl⟩ : syracuseStep 1692111 = 2538167) B2538167
theorem B5714387 : Blo 1691546 5714387 := bstep (se 1 (by rfl) ⟨4285790, by rfl⟩ : syracuseStep 5714387 = 8571581) B8571581
theorem B8565263 : Blo 1691546 8565263 := bstep (se 1 (by rfl) ⟨6423947, by rfl⟩ : syracuseStep 8565263 = 12847895) B12847895
theorem B14463521 : Blo 1691546 14463521 := bstep (se 2 (by rfl) ⟨5423820, by rfl⟩ : syracuseStep 14463521 = 10847641) B10847641
theorem B4067923 : Blo 1691546 4067923 := bstep (se 1 (by rfl) ⟨3050942, by rfl⟩ : syracuseStep 4067923 = 6101885) B6101885
theorem B17601119 : Blo 1691546 17601119 := bstep (se 1 (by rfl) ⟨13200839, by rfl⟩ : syracuseStep 17601119 = 26401679) B26401679
theorem B1692263 : Blo 1691546 1692263 := bstep (se 1 (by rfl) ⟨1269197, by rfl⟩ : syracuseStep 1692263 = 2538395) B2538395
theorem B11146025 : Blo 1691546 11146025 := bstep (se 2 (by rfl) ⟨4179759, by rfl⟩ : syracuseStep 11146025 = 8359519) B8359519
theorem B1692527 : Blo 1691546 1692527 := bstep (se 1 (by rfl) ⟨1269395, by rfl⟩ : syracuseStep 1692527 = 2538791) B2538791
theorem B37098371 : Blo 1691546 37098371 := bstep (se 1 (by rfl) ⟨27823778, by rfl⟩ : syracuseStep 37098371 = 55647557) B55647557
theorem B1692583 : Blo 1691546 1692583 := bstep (se 1 (by rfl) ⟨1269437, by rfl⟩ : syracuseStep 1692583 = 2538875) B2538875
theorem B1692667 : Blo 1691546 1692667 := bstep (se 1 (by rfl) ⟨1269500, by rfl⟩ : syracuseStep 1692667 = 2539001) B2539001
theorem B2855999 : Blo 1691546 2855999 := bstep (se 1 (by rfl) ⟨2141999, by rfl⟩ : syracuseStep 2855999 = 4283999) B4283999
theorem B1692735 : Blo 1691546 1692735 := bstep (se 1 (by rfl) ⟨1269551, by rfl⟩ : syracuseStep 1692735 = 2539103) B2539103
theorem B5420105 : Blo 1691546 5420105 := bstep (se 2 (by rfl) ⟨2032539, by rfl⟩ : syracuseStep 5420105 = 4065079) B4065079
theorem B3806315 : Blo 1691546 3806315 := bstep (se 1 (by rfl) ⟨2854736, by rfl⟩ : syracuseStep 3806315 = 5709473) B5709473
theorem B1692879 : Blo 1691546 1692879 := bstep (se 1 (by rfl) ⟨1269659, by rfl⟩ : syracuseStep 1692879 = 2539319) B2539319
theorem B1693083 : Blo 1691546 1693083 := bstep (se 1 (by rfl) ⟨1269812, by rfl⟩ : syracuseStep 1693083 = 2539625) B2539625
theorem B10843591 : Blo 1691546 10843591 := bstep (se 1 (by rfl) ⟨8132693, by rfl⟩ : syracuseStep 10843591 = 16265387) B16265387
theorem B74225159 : Blo 1691546 74225159 := bstep (se 1 (by rfl) ⟨55668869, by rfl⟩ : syracuseStep 74225159 = 111337739) B111337739
theorem B2856559 : Blo 1691546 2856559 := bstep (se 1 (by rfl) ⟨2142419, by rfl⟩ : syracuseStep 2856559 = 4284839) B4284839
theorem B1693295 : Blo 1691546 1693295 := bstep (se 1 (by rfl) ⟨1269971, by rfl⟩ : syracuseStep 1693295 = 2539943) B2539943
theorem B1693351 : Blo 1691546 1693351 := bstep (se 1 (by rfl) ⟨1270013, by rfl⟩ : syracuseStep 1693351 = 2540027) B2540027
theorem B3806891 : Blo 1691546 3806891 := bstep (se 1 (by rfl) ⟨2855168, by rfl⟩ : syracuseStep 3806891 = 5710337) B5710337
theorem B2856667 : Blo 1691546 2856667 := bstep (se 1 (by rfl) ⟨2142500, by rfl⟩ : syracuseStep 2856667 = 4285001) B4285001
theorem B1693435 : Blo 1691546 1693435 := bstep (se 1 (by rfl) ⟨1270076, by rfl⟩ : syracuseStep 1693435 = 2540153) B2540153
theorem B1693471 : Blo 1691546 1693471 := bstep (se 1 (by rfl) ⟨1270103, by rfl⟩ : syracuseStep 1693471 = 2540207) B2540207
theorem B1693503 : Blo 1691546 1693503 := bstep (se 1 (by rfl) ⟨1270127, by rfl⟩ : syracuseStep 1693503 = 2540255) B2540255
theorem B2537447 : Blo 1691546 2537447 := bstep (se 1 (by rfl) ⟨1903085, by rfl⟩ : syracuseStep 2537447 = 3806171) B3806171
theorem B3807215 : Blo 1691546 3807215 := bstep (se 1 (by rfl) ⟨2855411, by rfl⟩ : syracuseStep 3807215 = 5710823) B5710823
theorem B15439855 : Blo 1691546 15439855 := bstep (se 1 (by rfl) ⟨11579891, by rfl⟩ : syracuseStep 15439855 = 23159783) B23159783
theorem B2537465 : Blo 1691546 2537465 := bstep (se 2 (by rfl) ⟨951549, by rfl⟩ : syracuseStep 2537465 = 1903099) B1903099
theorem B2537567 : Blo 1691546 2537567 := bstep (se 1 (by rfl) ⟨1903175, by rfl⟩ : syracuseStep 2537567 = 3806351) B3806351
theorem B3258463 : Blo 1691546 3258463 := bstep (se 1 (by rfl) ⟨2443847, by rfl⟩ : syracuseStep 3258463 = 4887695) B4887695
theorem B2537627 : Blo 1691546 2537627 := bstep (se 1 (by rfl) ⟨1903220, by rfl⟩ : syracuseStep 2537627 = 3806441) B3806441
theorem B2537663 : Blo 1691546 2537663 := bstep (se 1 (by rfl) ⟨1903247, by rfl⟩ : syracuseStep 2537663 = 3806495) B3806495
theorem B3807431 : Blo 1691546 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B2537705 : Blo 1691546 2537705 := bstep (se 2 (by rfl) ⟨951639, by rfl⟩ : syracuseStep 2537705 = 1903279) B1903279
theorem B6428915 : Blo 1691546 6428915 := bstep (se 1 (by rfl) ⟨4821686, by rfl⟩ : syracuseStep 6428915 = 9643373) B9643373
theorem B23148823 : Blo 1691546 23148823 := bstep (se 1 (by rfl) ⟨17361617, by rfl⟩ : syracuseStep 23148823 = 34723235) B34723235
theorem B3807611 : Blo 1691546 3807611 := bstep (se 1 (by rfl) ⟨2855708, by rfl⟩ : syracuseStep 3807611 = 5711417) B5711417
theorem B6101423 : Blo 1691546 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B2538011 : Blo 1691546 2538011 := bstep (se 1 (by rfl) ⟨1903508, by rfl⟩ : syracuseStep 2538011 = 3807017) B3807017
theorem B16497209 : Blo 1691546 16497209 := bstep (se 2 (by rfl) ⟨6186453, by rfl⟩ : syracuseStep 16497209 = 12372907) B12372907
theorem B2538089 : Blo 1691546 2538089 := bstep (se 2 (by rfl) ⟨951783, by rfl⟩ : syracuseStep 2538089 = 1903567) B1903567
theorem B39066245 : Blo 1691546 39066245 := bstep (se 4 (by rfl) ⟨3662460, by rfl⟩ : syracuseStep 39066245 = 7324921) B7324921
theorem B3807881 : Blo 1691546 3807881 := bstep (se 2 (by rfl) ⟨1427955, by rfl⟩ : syracuseStep 3807881 = 2855911) B2855911
theorem B4283219 : Blo 1691546 4283219 := bstep (se 1 (by rfl) ⟨3212414, by rfl⟩ : syracuseStep 4283219 = 6424829) B6424829
theorem B46341011 : Blo 1691546 46341011 := bstep (se 1 (by rfl) ⟨34755758, by rfl⟩ : syracuseStep 46341011 = 69511517) B69511517
theorem B178363349 : Blo 1691546 178363349 := bstep (se 7 (by rfl) ⟨2090195, by rfl⟩ : syracuseStep 178363349 = 4180391) B4180391
theorem B20585501 : Blo 1691546 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B2538617 : Blo 1691546 2538617 := bstep (se 2 (by rfl) ⟨951981, by rfl⟩ : syracuseStep 2538617 = 1903963) B1903963
theorem B3808439 : Blo 1691546 3808439 := bstep (se 1 (by rfl) ⟨2856329, by rfl⟩ : syracuseStep 3808439 = 5712659) B5712659
theorem B2538719 : Blo 1691546 2538719 := bstep (se 1 (by rfl) ⟨1904039, by rfl⟩ : syracuseStep 2538719 = 3808079) B3808079
theorem B2538761 : Blo 1691546 2538761 := bstep (se 2 (by rfl) ⟨952035, by rfl⟩ : syracuseStep 2538761 = 1904071) B1904071
theorem B5709095 : Blo 1691546 5709095 := bstep (se 1 (by rfl) ⟨4281821, by rfl⟩ : syracuseStep 5709095 = 8563643) B8563643
theorem B2538863 : Blo 1691546 2538863 := bstep (se 1 (by rfl) ⟨1904147, by rfl⟩ : syracuseStep 2538863 = 3808295) B3808295
theorem B3431791 : Blo 1691546 3431791 := bstep (se 1 (by rfl) ⟨2573843, by rfl⟩ : syracuseStep 3431791 = 5147687) B5147687
theorem B8682947 : Blo 1691546 8682947 := bstep (se 1 (by rfl) ⟨6512210, by rfl⟩ : syracuseStep 8682947 = 13024421) B13024421
theorem B2538983 : Blo 1691546 2538983 := bstep (se 1 (by rfl) ⟨1904237, by rfl⟩ : syracuseStep 2538983 = 3808475) B3808475
theorem B2539115 : Blo 1691546 2539115 := bstep (se 1 (by rfl) ⟨1904336, by rfl⟩ : syracuseStep 2539115 = 3808673) B3808673
theorem B2539241 : Blo 1691546 2539241 := bstep (se 2 (by rfl) ⟨952215, by rfl⟩ : syracuseStep 2539241 = 1904431) B1904431
theorem B3809015 : Blo 1691546 3809015 := bstep (se 1 (by rfl) ⟨2856761, by rfl⟩ : syracuseStep 3809015 = 5713523) B5713523
theorem B2539385 : Blo 1691546 2539385 := bstep (se 2 (by rfl) ⟨952269, by rfl⟩ : syracuseStep 2539385 = 1904539) B1904539
theorem B3809195 : Blo 1691546 3809195 := bstep (se 1 (by rfl) ⟨2856896, by rfl⟩ : syracuseStep 3809195 = 5713793) B5713793
theorem B2539487 : Blo 1691546 2539487 := bstep (se 1 (by rfl) ⟨1904615, by rfl⟩ : syracuseStep 2539487 = 3809231) B3809231
theorem B5710013 : Blo 1691546 5710013 := bstep (se 3 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 5710013 = 2141255) B2141255
theorem B2539823 : Blo 1691546 2539823 := bstep (se 1 (by rfl) ⟨1904867, by rfl⟩ : syracuseStep 2539823 = 3809735) B3809735
theorem B3809591 : Blo 1691546 3809591 := bstep (se 1 (by rfl) ⟨2857193, by rfl⟩ : syracuseStep 3809591 = 5714387) B5714387
theorem B5710175 : Blo 1691546 5710175 := bstep (se 1 (by rfl) ⟨4282631, by rfl⟩ : syracuseStep 5710175 = 8565263) B8565263
theorem B9642347 : Blo 1691546 9642347 := bstep (se 1 (by rfl) ⟨7231760, by rfl⟩ : syracuseStep 9642347 = 14463521) B14463521
theorem B4284809 : Blo 1691546 4284809 := bstep (se 2 (by rfl) ⟨1606803, by rfl⟩ : syracuseStep 4284809 = 3213607) B3213607
theorem B4817323 : Blo 1691546 4817323 := bstep (se 1 (by rfl) ⟨3612992, by rfl⟩ : syracuseStep 4817323 = 7225985) B7225985
theorem B7430683 : Blo 1691546 7430683 := bstep (se 1 (by rfl) ⟨5573012, by rfl⟩ : syracuseStep 7430683 = 11146025) B11146025
theorem B3211807 : Blo 1691546 3211807 := bstep (se 1 (by rfl) ⟨2408855, by rfl⟩ : syracuseStep 3211807 = 4817711) B4817711
theorem B2540063 : Blo 1691546 2540063 := bstep (se 1 (by rfl) ⟨1905047, by rfl⟩ : syracuseStep 2540063 = 3810095) B3810095
theorem B13722209 : Blo 1691546 13722209 := bstep (se 2 (by rfl) ⟨5145828, by rfl⟩ : syracuseStep 13722209 = 10291657) B10291657
theorem B5423719 : Blo 1691546 5423719 := bstep (se 1 (by rfl) ⟨4067789, by rfl⟩ : syracuseStep 5423719 = 8135579) B8135579
theorem B3613403 : Blo 1691546 3613403 := bstep (se 1 (by rfl) ⟨2710052, by rfl⟩ : syracuseStep 3613403 = 5420105) B5420105
theorem B5423897 : Blo 1691546 5423897 := bstep (se 2 (by rfl) ⟨2033961, by rfl⟩ : syracuseStep 5423897 = 4067923) B4067923
theorem B3212399 : Blo 1691546 3212399 := bstep (se 1 (by rfl) ⟨2409299, by rfl⟩ : syracuseStep 3212399 = 4818599) B4818599
theorem B4818143 : Blo 1691546 4818143 := bstep (se 1 (by rfl) ⟨3613607, by rfl⟩ : syracuseStep 4818143 = 7227215) B7227215
theorem B2032943 : Blo 1691546 2032943 := bstep (se 1 (by rfl) ⟨1524707, by rfl⟩ : syracuseStep 2032943 = 3049415) B3049415
theorem B21693743 : Blo 1691546 21693743 := bstep (se 1 (by rfl) ⟨16270307, by rfl⟩ : syracuseStep 21693743 = 32540615) B32540615
theorem B3212635 : Blo 1691546 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B4285943 : Blo 1691546 4285943 := bstep (se 1 (by rfl) ⟨3214457, by rfl⟩ : syracuseStep 4285943 = 6428915) B6428915
theorem B17368607 : Blo 1691546 17368607 := bstep (se 1 (by rfl) ⟨13026455, by rfl⟩ : syracuseStep 17368607 = 26052911) B26052911
theorem B26044163 : Blo 1691546 26044163 := bstep (se 1 (by rfl) ⟨19533122, by rfl⟩ : syracuseStep 26044163 = 39066245) B39066245
theorem B8685409 : Blo 1691546 8685409 := bstep (se 2 (by rfl) ⟨3257028, by rfl⟩ : syracuseStep 8685409 = 6514057) B6514057
theorem B18302885 : Blo 1691546 18302885 := bstep (se 4 (by rfl) ⟨1715895, by rfl⟩ : syracuseStep 18302885 = 3431791) B3431791
theorem B30894007 : Blo 1691546 30894007 := bstep (se 1 (by rfl) ⟨23170505, by rfl⟩ : syracuseStep 30894007 = 46341011) B46341011
theorem B118908899 : Blo 1691546 118908899 := bstep (se 1 (by rfl) ⟨89181674, by rfl⟩ : syracuseStep 118908899 = 178363349) B178363349
theorem B13723667 : Blo 1691546 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B6424859 : Blo 1691546 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B98928989 : Blo 1691546 98928989 := bstep (se 3 (by rfl) ⟨18549185, by rfl⟩ : syracuseStep 98928989 = 37098371) B37098371
theorem B8571419 : Blo 1691546 8571419 := bstep (se 1 (by rfl) ⟨6428564, by rfl⟩ : syracuseStep 8571419 = 12857129) B12857129
theorem B1903207 : Blo 1691546 1903207 := bstep (se 1 (by rfl) ⟨1427405, by rfl⟩ : syracuseStep 1903207 = 2854811) B2854811
theorem B4344617 : Blo 1691546 4344617 := bstep (se 2 (by rfl) ⟨1629231, by rfl⟩ : syracuseStep 4344617 = 3258463) B3258463
theorem B58592159 : Blo 1691546 58592159 := bstep (se 1 (by rfl) ⟨43944119, by rfl⟩ : syracuseStep 58592159 = 87888239) B87888239
theorem B6425513 : Blo 1691546 6425513 := bstep (se 2 (by rfl) ⟨2409567, by rfl⟩ : syracuseStep 6425513 = 4819135) B4819135
theorem B11734079 : Blo 1691546 11734079 := bstep (se 1 (by rfl) ⟨8800559, by rfl⟩ : syracuseStep 11734079 = 17601119) B17601119
theorem B21687385 : Blo 1691546 21687385 := bstep (se 2 (by rfl) ⟨8132769, by rfl⟩ : syracuseStep 21687385 = 16265539) B16265539
theorem B39105679 : Blo 1691546 39105679 := bstep (se 1 (by rfl) ⟨29329259, by rfl⟩ : syracuseStep 39105679 = 58658519) B58658519
theorem B5713145 : Blo 1691546 5713145 := bstep (se 2 (by rfl) ⟨2142429, by rfl⟩ : syracuseStep 5713145 = 4284859) B4284859
theorem B1903999 : Blo 1691546 1903999 := bstep (se 1 (by rfl) ⟨1427999, by rfl⟩ : syracuseStep 1903999 = 2855999) B2855999
theorem B10431899 : Blo 1691546 10431899 := bstep (se 1 (by rfl) ⟨7823924, by rfl⟩ : syracuseStep 10431899 = 15647849) B15647849
theorem B5713307 : Blo 1691546 5713307 := bstep (se 1 (by rfl) ⟨4284980, by rfl⟩ : syracuseStep 5713307 = 8569961) B8569961
theorem B5713415 : Blo 1691546 5713415 := bstep (se 1 (by rfl) ⟨4285061, by rfl⟩ : syracuseStep 5713415 = 8570123) B8570123
theorem B49483439 : Blo 1691546 49483439 := bstep (se 1 (by rfl) ⟨37112579, by rfl⟩ : syracuseStep 49483439 = 74225159) B74225159
theorem B24161975 : Blo 1691546 24161975 := bstep (se 1 (by rfl) ⟨18121481, by rfl⟩ : syracuseStep 24161975 = 36242963) B36242963
theorem B32550761 : Blo 1691546 32550761 := bstep (se 2 (by rfl) ⟨12206535, by rfl⟩ : syracuseStep 32550761 = 24413071) B24413071
theorem B1691631 : Blo 1691546 1691631 := bstep (se 1 (by rfl) ⟨1268723, by rfl⟩ : syracuseStep 1691631 = 2537447) B2537447
theorem B1691643 : Blo 1691546 1691643 := bstep (se 1 (by rfl) ⟨1268732, by rfl⟩ : syracuseStep 1691643 = 2537465) B2537465
theorem B1691711 : Blo 1691546 1691711 := bstep (se 1 (by rfl) ⟨1268783, by rfl⟩ : syracuseStep 1691711 = 2537567) B2537567
theorem B1691751 : Blo 1691546 1691751 := bstep (se 1 (by rfl) ⟨1268813, by rfl⟩ : syracuseStep 1691751 = 2537627) B2537627
theorem B1691775 : Blo 1691546 1691775 := bstep (se 1 (by rfl) ⟨1268831, by rfl⟩ : syracuseStep 1691775 = 2537663) B2537663
theorem B1929343 : Blo 1691546 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B1691803 : Blo 1691546 1691803 := bstep (se 1 (by rfl) ⟨1268852, by rfl⟩ : syracuseStep 1691803 = 2537705) B2537705
theorem B4067615 : Blo 1691546 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B2855209 : Blo 1691546 2855209 := bstep (se 2 (by rfl) ⟨1070703, by rfl⟩ : syracuseStep 2855209 = 2141407) B2141407
theorem B1692007 : Blo 1691546 1692007 := bstep (se 1 (by rfl) ⟨1269005, by rfl⟩ : syracuseStep 1692007 = 2538011) B2538011
theorem B10998139 : Blo 1691546 10998139 := bstep (se 1 (by rfl) ⟨8248604, by rfl⟩ : syracuseStep 10998139 = 16497209) B16497209
theorem B1692059 : Blo 1691546 1692059 := bstep (se 1 (by rfl) ⟨1269044, by rfl⟩ : syracuseStep 1692059 = 2538089) B2538089
theorem B2855479 : Blo 1691546 2855479 := bstep (se 1 (by rfl) ⟨2141609, by rfl⟩ : syracuseStep 2855479 = 4283219) B4283219
theorem B5714495 : Blo 1691546 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B9638473 : Blo 1691546 9638473 := bstep (se 2 (by rfl) ⟨3614427, by rfl⟩ : syracuseStep 9638473 = 7228855) B7228855
theorem B43381331 : Blo 1691546 43381331 := bstep (se 1 (by rfl) ⟨32535998, by rfl⟩ : syracuseStep 43381331 = 65071997) B65071997
theorem B1692411 : Blo 1691546 1692411 := bstep (se 1 (by rfl) ⟨1269308, by rfl⟩ : syracuseStep 1692411 = 2538617) B2538617
theorem B3806009 : Blo 1691546 3806009 := bstep (se 2 (by rfl) ⟨1427253, by rfl⟩ : syracuseStep 3806009 = 2854507) B2854507
theorem B1692479 : Blo 1691546 1692479 := bstep (se 1 (by rfl) ⟨1269359, by rfl⟩ : syracuseStep 1692479 = 2538719) B2538719
theorem B1692507 : Blo 1691546 1692507 := bstep (se 1 (by rfl) ⟨1269380, by rfl⟩ : syracuseStep 1692507 = 2538761) B2538761
theorem B3806063 : Blo 1691546 3806063 := bstep (se 1 (by rfl) ⟨2854547, by rfl⟩ : syracuseStep 3806063 = 5709095) B5709095
theorem B1692575 : Blo 1691546 1692575 := bstep (se 1 (by rfl) ⟨1269431, by rfl⟩ : syracuseStep 1692575 = 2538863) B2538863
theorem B5788631 : Blo 1691546 5788631 := bstep (se 1 (by rfl) ⟨4341473, by rfl⟩ : syracuseStep 5788631 = 8682947) B8682947
theorem B1692655 : Blo 1691546 1692655 := bstep (se 1 (by rfl) ⟨1269491, by rfl⟩ : syracuseStep 1692655 = 2538983) B2538983
theorem B1692743 : Blo 1691546 1692743 := bstep (se 1 (by rfl) ⟨1269557, by rfl⟩ : syracuseStep 1692743 = 2539115) B2539115
theorem B1692827 : Blo 1691546 1692827 := bstep (se 1 (by rfl) ⟨1269620, by rfl⟩ : syracuseStep 1692827 = 2539241) B2539241
theorem B3806369 : Blo 1691546 3806369 := bstep (se 2 (by rfl) ⟨1427388, by rfl⟩ : syracuseStep 3806369 = 2854777) B2854777
theorem B12858587 : Blo 1691546 12858587 := bstep (se 1 (by rfl) ⟨9643940, by rfl⟩ : syracuseStep 12858587 = 19287881) B19287881
theorem B1692923 : Blo 1691546 1692923 := bstep (se 1 (by rfl) ⟨1269692, by rfl⟩ : syracuseStep 1692923 = 2539385) B2539385
theorem B5420297 : Blo 1691546 5420297 := bstep (se 2 (by rfl) ⟨2032611, by rfl⟩ : syracuseStep 5420297 = 4065223) B4065223
theorem B1692991 : Blo 1691546 1692991 := bstep (se 1 (by rfl) ⟨1269743, by rfl⟩ : syracuseStep 1692991 = 2539487) B2539487
theorem B3806639 : Blo 1691546 3806639 := bstep (se 1 (by rfl) ⟨2854979, by rfl⟩ : syracuseStep 3806639 = 5709959) B5709959
theorem B1693159 : Blo 1691546 1693159 := bstep (se 1 (by rfl) ⟨1269869, by rfl⟩ : syracuseStep 1693159 = 2539739) B2539739
theorem B2856431 : Blo 1691546 2856431 := bstep (se 1 (by rfl) ⟨2142323, by rfl⟩ : syracuseStep 2856431 = 4284647) B4284647
theorem B1693167 : Blo 1691546 1693167 := bstep (se 1 (by rfl) ⟨1269875, by rfl⟩ : syracuseStep 1693167 = 2539751) B2539751
theorem B1693275 : Blo 1691546 1693275 := bstep (se 1 (by rfl) ⟨1269956, by rfl⟩ : syracuseStep 1693275 = 2539913) B2539913
theorem B1693339 : Blo 1691546 1693339 := bstep (se 1 (by rfl) ⟨1270004, by rfl⟩ : syracuseStep 1693339 = 2540009) B2540009
theorem B30865097 : Blo 1691546 30865097 := bstep (se 2 (by rfl) ⟨11574411, by rfl⟩ : syracuseStep 30865097 = 23148823) B23148823
theorem B1693423 : Blo 1691546 1693423 := bstep (se 1 (by rfl) ⟨1270067, by rfl⟩ : syracuseStep 1693423 = 2540135) B2540135
theorem B2856775 : Blo 1691546 2856775 := bstep (se 1 (by rfl) ⟨2142581, by rfl⟩ : syracuseStep 2856775 = 4285163) B4285163
theorem B1693511 : Blo 1691546 1693511 := bstep (se 1 (by rfl) ⟨1270133, by rfl⟩ : syracuseStep 1693511 = 2540267) B2540267
theorem B1693531 : Blo 1691546 1693531 := bstep (se 1 (by rfl) ⟨1270148, by rfl⟩ : syracuseStep 1693531 = 2540297) B2540297
theorem B2856863 : Blo 1691546 2856863 := bstep (se 1 (by rfl) ⟨2142647, by rfl⟩ : syracuseStep 2856863 = 4285295) B4285295
theorem B2537513 : Blo 1691546 2537513 := bstep (se 2 (by rfl) ⟨951567, by rfl⟩ : syracuseStep 2537513 = 1903135) B1903135
theorem B2537543 : Blo 1691546 2537543 := bstep (se 1 (by rfl) ⟨1903157, by rfl⟩ : syracuseStep 2537543 = 3806315) B3806315
theorem B2644255 : Blo 1691546 2644255 := bstep (se 1 (by rfl) ⟨1983191, by rfl⟩ : syracuseStep 2644255 = 3966383) B3966383
theorem B3807647 : Blo 1691546 3807647 := bstep (se 1 (by rfl) ⟨2855735, by rfl⟩ : syracuseStep 3807647 = 5711471) B5711471
theorem B2537927 : Blo 1691546 2537927 := bstep (se 1 (by rfl) ⟨1903445, by rfl⟩ : syracuseStep 2537927 = 3806891) B3806891
theorem B3807719 : Blo 1691546 3807719 := bstep (se 1 (by rfl) ⟨2855789, by rfl⟩ : syracuseStep 3807719 = 5711579) B5711579
theorem B27466397 : Blo 1691546 27466397 := bstep (se 3 (by rfl) ⟨5149949, by rfl⟩ : syracuseStep 27466397 = 10299899) B10299899
theorem B2538143 : Blo 1691546 2538143 := bstep (se 1 (by rfl) ⟨1903607, by rfl⟩ : syracuseStep 2538143 = 3807215) B3807215
theorem B2538287 : Blo 1691546 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B2538407 : Blo 1691546 2538407 := bstep (se 1 (by rfl) ⟨1903805, by rfl⟩ : syracuseStep 2538407 = 3807611) B3807611
theorem B2538587 : Blo 1691546 2538587 := bstep (se 1 (by rfl) ⟨1903940, by rfl⟩ : syracuseStep 2538587 = 3807881) B3807881
theorem B14458121 : Blo 1691546 14458121 := bstep (se 2 (by rfl) ⟨5421795, by rfl⟩ : syracuseStep 14458121 = 10843591) B10843591
theorem B3808583 : Blo 1691546 3808583 := bstep (se 1 (by rfl) ⟨2856437, by rfl⟩ : syracuseStep 3808583 = 5712875) B5712875
theorem B3808619 : Blo 1691546 3808619 := bstep (se 1 (by rfl) ⟨2856464, by rfl⟩ : syracuseStep 3808619 = 5712929) B5712929
theorem B2538959 : Blo 1691546 2538959 := bstep (se 1 (by rfl) ⟨1904219, by rfl⟩ : syracuseStep 2538959 = 3808439) B3808439
theorem B3808745 : Blo 1691546 3808745 := bstep (se 2 (by rfl) ⟨1428279, by rfl⟩ : syracuseStep 3808745 = 2856559) B2856559
theorem B3808889 : Blo 1691546 3808889 := bstep (se 2 (by rfl) ⟨1428333, by rfl⟩ : syracuseStep 3808889 = 2856667) B2856667
theorem B7233299 : Blo 1691546 7233299 := bstep (se 1 (by rfl) ⟨5424974, by rfl⟩ : syracuseStep 7233299 = 10849949) B10849949
theorem B4284191 : Blo 1691546 4284191 := bstep (se 1 (by rfl) ⟨3213143, by rfl⟩ : syracuseStep 4284191 = 6426287) B6426287
theorem B2539343 : Blo 1691546 2539343 := bstep (se 1 (by rfl) ⟨1904507, by rfl⟩ : syracuseStep 2539343 = 3809015) B3809015
theorem B2539463 : Blo 1691546 2539463 := bstep (se 1 (by rfl) ⟨1904597, by rfl⟩ : syracuseStep 2539463 = 3809195) B3809195
theorem B20586473 : Blo 1691546 20586473 := bstep (se 2 (by rfl) ⟨7719927, by rfl⟩ : syracuseStep 20586473 = 15439855) B15439855
theorem B2572457 : Blo 1691546 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B2539727 : Blo 1691546 2539727 := bstep (se 1 (by rfl) ⟨1904795, by rfl⟩ : syracuseStep 2539727 = 3809591) B3809591
theorem B3809663 : Blo 1691546 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B2408935 : Blo 1691546 2408935 := bstep (se 1 (by rfl) ⟨1806701, by rfl⟩ : syracuseStep 2408935 = 3613403) B3613403
theorem B14664185 : Blo 1691546 14664185 := bstep (se 2 (by rfl) ⟨5499069, by rfl⟩ : syracuseStep 14664185 = 10998139) B10998139
theorem B6423097 : Blo 1691546 6423097 := bstep (se 2 (by rfl) ⟨2408661, by rfl⟩ : syracuseStep 6423097 = 4817323) B4817323
theorem B3859087 : Blo 1691546 3859087 := bstep (se 1 (by rfl) ⟨2894315, by rfl⟩ : syracuseStep 3859087 = 5788631) B5788631
theorem B10846973 : Blo 1691546 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B18310931 : Blo 1691546 18310931 := bstep (se 1 (by rfl) ⟨13733198, by rfl⟩ : syracuseStep 18310931 = 27466397) B27466397
theorem B82306925 : Blo 1691546 82306925 := bstep (se 3 (by rfl) ⟨15432548, by rfl⟩ : syracuseStep 82306925 = 30865097) B30865097
theorem B39061439 : Blo 1691546 39061439 := bstep (se 1 (by rfl) ⟨29296079, by rfl⟩ : syracuseStep 39061439 = 58592159) B58592159
theorem B16107983 : Blo 1691546 16107983 := bstep (se 1 (by rfl) ⟨12080987, by rfl⟩ : syracuseStep 16107983 = 24161975) B24161975
theorem B41192009 : Blo 1691546 41192009 := bstep (se 2 (by rfl) ⟨15447003, by rfl⟩ : syracuseStep 41192009 = 30894007) B30894007
theorem B13724315 : Blo 1691546 13724315 := bstep (se 1 (by rfl) ⟨10293236, by rfl⟩ : syracuseStep 13724315 = 20586473) B20586473
theorem B28920887 : Blo 1691546 28920887 := bstep (se 1 (by rfl) ⟨21690665, by rfl⟩ : syracuseStep 28920887 = 43381331) B43381331
theorem B3615931 : Blo 1691546 3615931 := bstep (se 1 (by rfl) ⟨2711948, by rfl⟩ : syracuseStep 3615931 = 5423897) B5423897
theorem B12848381 : Blo 1691546 12848381 := bstep (se 3 (by rfl) ⟨2409071, by rfl⟩ : syracuseStep 12848381 = 4818143) B4818143
theorem B14454125 : Blo 1691546 14454125 := bstep (se 3 (by rfl) ⟨2710148, by rfl⟩ : syracuseStep 14454125 = 5420297) B5420297
theorem B9907577 : Blo 1691546 9907577 := bstep (se 2 (by rfl) ⟨3715341, by rfl⟩ : syracuseStep 9907577 = 7430683) B7430683
theorem B8572391 : Blo 1691546 8572391 := bstep (se 1 (by rfl) ⟨6429293, by rfl⟩ : syracuseStep 8572391 = 12858587) B12858587
theorem B14462495 : Blo 1691546 14462495 := bstep (se 1 (by rfl) ⟨10846871, by rfl⟩ : syracuseStep 14462495 = 21693743) B21693743
theorem B1904287 : Blo 1691546 1904287 := bstep (se 1 (by rfl) ⟨1428215, by rfl⟩ : syracuseStep 1904287 = 2856431) B2856431
theorem B17362775 : Blo 1691546 17362775 := bstep (se 1 (by rfl) ⟨13022081, by rfl⟩ : syracuseStep 17362775 = 26044163) B26044163
theorem B1904575 : Blo 1691546 1904575 := bstep (se 1 (by rfl) ⟨1428431, by rfl⟩ : syracuseStep 1904575 = 2856863) B2856863
theorem B12201923 : Blo 1691546 12201923 := bstep (se 1 (by rfl) ⟨9151442, by rfl⟩ : syracuseStep 12201923 = 18302885) B18302885
theorem B1691675 : Blo 1691546 1691675 := bstep (se 1 (by rfl) ⟨1268756, by rfl⟩ : syracuseStep 1691675 = 2537513) B2537513
theorem B1691695 : Blo 1691546 1691695 := bstep (se 1 (by rfl) ⟨1268771, by rfl⟩ : syracuseStep 1691695 = 2537543) B2537543
theorem B14102693 : Blo 1691546 14102693 := bstep (se 4 (by rfl) ⟨1322127, by rfl⟩ : syracuseStep 14102693 = 2644255) B2644255
theorem B1691951 : Blo 1691546 1691951 := bstep (se 1 (by rfl) ⟨1268963, by rfl⟩ : syracuseStep 1691951 = 2537927) B2537927
theorem B5714279 : Blo 1691546 5714279 := bstep (se 1 (by rfl) ⟨4285709, by rfl⟩ : syracuseStep 5714279 = 8571419) B8571419
theorem B1692095 : Blo 1691546 1692095 := bstep (se 1 (by rfl) ⟨1269071, by rfl⟩ : syracuseStep 1692095 = 2538143) B2538143
theorem B2896411 : Blo 1691546 2896411 := bstep (se 1 (by rfl) ⟨2172308, by rfl⟩ : syracuseStep 2896411 = 4344617) B4344617
theorem B1692191 : Blo 1691546 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1692271 : Blo 1691546 1692271 := bstep (se 1 (by rfl) ⟨1269203, by rfl⟩ : syracuseStep 1692271 = 2538407) B2538407
theorem B1692391 : Blo 1691546 1692391 := bstep (se 1 (by rfl) ⟨1269293, by rfl⟩ : syracuseStep 1692391 = 2538587) B2538587
theorem B9638747 : Blo 1691546 9638747 := bstep (se 1 (by rfl) ⟨7229060, by rfl⟩ : syracuseStep 9638747 = 14458121) B14458121
theorem B1692639 : Blo 1691546 1692639 := bstep (se 1 (by rfl) ⟨1269479, by rfl⟩ : syracuseStep 1692639 = 2538959) B2538959
theorem B11580545 : Blo 1691546 11580545 := bstep (se 2 (by rfl) ⟨4342704, by rfl⟩ : syracuseStep 11580545 = 8685409) B8685409
theorem B4822199 : Blo 1691546 4822199 := bstep (se 1 (by rfl) ⟨3616649, by rfl⟩ : syracuseStep 4822199 = 7233299) B7233299
theorem B2856127 : Blo 1691546 2856127 := bstep (se 1 (by rfl) ⟨2142095, by rfl⟩ : syracuseStep 2856127 = 4284191) B4284191
theorem B1692895 : Blo 1691546 1692895 := bstep (se 1 (by rfl) ⟨1269671, by rfl⟩ : syracuseStep 1692895 = 2539343) B2539343
theorem B1692975 : Blo 1691546 1692975 := bstep (se 1 (by rfl) ⟨1269731, by rfl⟩ : syracuseStep 1692975 = 2539463) B2539463
theorem B3806675 : Blo 1691546 3806675 := bstep (se 1 (by rfl) ⟨2855006, by rfl⟩ : syracuseStep 3806675 = 5710013) B5710013
theorem B31290877 : Blo 1691546 31290877 := bstep (se 3 (by rfl) ⟨5867039, by rfl⟩ : syracuseStep 31290877 = 11734079) B11734079
theorem B1693215 : Blo 1691546 1693215 := bstep (se 1 (by rfl) ⟨1269911, by rfl⟩ : syracuseStep 1693215 = 2539823) B2539823
theorem B3806783 : Blo 1691546 3806783 := bstep (se 1 (by rfl) ⟨2855087, by rfl⟩ : syracuseStep 3806783 = 5710175) B5710175
theorem B6428231 : Blo 1691546 6428231 := bstep (se 1 (by rfl) ⟨4821173, by rfl⟩ : syracuseStep 6428231 = 9642347) B9642347
theorem B2856539 : Blo 1691546 2856539 := bstep (se 1 (by rfl) ⟨2142404, by rfl⟩ : syracuseStep 2856539 = 4284809) B4284809
theorem B8566397 : Blo 1691546 8566397 := bstep (se 3 (by rfl) ⟨1606199, by rfl⟩ : syracuseStep 8566397 = 3212399) B3212399
theorem B1693375 : Blo 1691546 1693375 := bstep (se 1 (by rfl) ⟨1270031, by rfl⟩ : syracuseStep 1693375 = 2540063) B2540063
theorem B3806945 : Blo 1691546 3806945 := bstep (se 2 (by rfl) ⟨1427604, by rfl⟩ : syracuseStep 3806945 = 2855209) B2855209
theorem B9148139 : Blo 1691546 9148139 := bstep (se 1 (by rfl) ⟨6861104, by rfl⟩ : syracuseStep 9148139 = 13722209) B13722209
theorem B2537339 : Blo 1691546 2537339 := bstep (se 1 (by rfl) ⟨1903004, by rfl⟩ : syracuseStep 2537339 = 3806009) B3806009
theorem B2537375 : Blo 1691546 2537375 := bstep (se 1 (by rfl) ⟨1903031, by rfl⟩ : syracuseStep 2537375 = 3806063) B3806063
theorem B4282409 : Blo 1691546 4282409 := bstep (se 2 (by rfl) ⟨1605903, by rfl⟩ : syracuseStep 4282409 = 3211807) B3211807
theorem B3807305 : Blo 1691546 3807305 := bstep (se 2 (by rfl) ⟨1427739, by rfl⟩ : syracuseStep 3807305 = 2855479) B2855479
theorem B12851297 : Blo 1691546 12851297 := bstep (se 2 (by rfl) ⟨4819236, by rfl⟩ : syracuseStep 12851297 = 9638473) B9638473
theorem B2537579 : Blo 1691546 2537579 := bstep (se 1 (by rfl) ⟨1903184, by rfl⟩ : syracuseStep 2537579 = 3806369) B3806369
theorem B5421181 : Blo 1691546 5421181 := bstep (se 3 (by rfl) ⟨1016471, by rfl⟩ : syracuseStep 5421181 = 2032943) B2032943
theorem B2537609 : Blo 1691546 2537609 := bstep (se 2 (by rfl) ⟨951603, by rfl⟩ : syracuseStep 2537609 = 1903207) B1903207
theorem B7231625 : Blo 1691546 7231625 := bstep (se 2 (by rfl) ⟨2711859, by rfl⟩ : syracuseStep 7231625 = 5423719) B5423719
theorem B2537759 : Blo 1691546 2537759 := bstep (se 1 (by rfl) ⟨1903319, by rfl⟩ : syracuseStep 2537759 = 3806639) B3806639
theorem B2857295 : Blo 1691546 2857295 := bstep (se 1 (by rfl) ⟨2142971, by rfl⟩ : syracuseStep 2857295 = 4285943) B4285943
theorem B79272599 : Blo 1691546 79272599 := bstep (se 1 (by rfl) ⟨59454449, by rfl⟩ : syracuseStep 79272599 = 118908899) B118908899
theorem B9149111 : Blo 1691546 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B46316285 : Blo 1691546 46316285 := bstep (se 3 (by rfl) ⟨8684303, by rfl⟩ : syracuseStep 46316285 = 17368607) B17368607
theorem B28916513 : Blo 1691546 28916513 := bstep (se 2 (by rfl) ⟨10843692, by rfl⟩ : syracuseStep 28916513 = 21687385) B21687385
theorem B4283239 : Blo 1691546 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B52140905 : Blo 1691546 52140905 := bstep (se 2 (by rfl) ⟨19552839, by rfl⟩ : syracuseStep 52140905 = 39105679) B39105679
theorem B65952659 : Blo 1691546 65952659 := bstep (se 1 (by rfl) ⟨49464494, by rfl⟩ : syracuseStep 65952659 = 98928989) B98928989
theorem B2538431 : Blo 1691546 2538431 := bstep (se 1 (by rfl) ⟨1903823, by rfl⟩ : syracuseStep 2538431 = 3807647) B3807647
theorem B2538479 : Blo 1691546 2538479 := bstep (se 1 (by rfl) ⟨1903859, by rfl⟩ : syracuseStep 2538479 = 3807719) B3807719
theorem B4283513 : Blo 1691546 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B2538665 : Blo 1691546 2538665 := bstep (se 2 (by rfl) ⟨951999, by rfl⟩ : syracuseStep 2538665 = 1903999) B1903999
theorem B4283675 : Blo 1691546 4283675 := bstep (se 1 (by rfl) ⟨3212756, by rfl⟩ : syracuseStep 4283675 = 6425513) B6425513
theorem B3808763 : Blo 1691546 3808763 := bstep (se 1 (by rfl) ⟨2856572, by rfl⟩ : syracuseStep 3808763 = 5713145) B5713145
theorem B2539055 : Blo 1691546 2539055 := bstep (se 1 (by rfl) ⟨1904291, by rfl⟩ : syracuseStep 2539055 = 3808583) B3808583
theorem B2539079 : Blo 1691546 2539079 := bstep (se 1 (by rfl) ⟨1904309, by rfl⟩ : syracuseStep 2539079 = 3808619) B3808619
theorem B6954599 : Blo 1691546 6954599 := bstep (se 1 (by rfl) ⟨5215949, by rfl⟩ : syracuseStep 6954599 = 10431899) B10431899
theorem B3808871 : Blo 1691546 3808871 := bstep (se 1 (by rfl) ⟨2856653, by rfl⟩ : syracuseStep 3808871 = 5713307) B5713307
theorem B2539163 : Blo 1691546 2539163 := bstep (se 1 (by rfl) ⟨1904372, by rfl⟩ : syracuseStep 2539163 = 3808745) B3808745
theorem B3808943 : Blo 1691546 3808943 := bstep (se 1 (by rfl) ⟨2856707, by rfl⟩ : syracuseStep 3808943 = 5713415) B5713415
theorem B2539259 : Blo 1691546 2539259 := bstep (se 1 (by rfl) ⟨1904444, by rfl⟩ : syracuseStep 2539259 = 3808889) B3808889
theorem B3809033 : Blo 1691546 3809033 := bstep (se 2 (by rfl) ⟨1428387, by rfl⟩ : syracuseStep 3809033 = 2856775) B2856775
theorem B32988959 : Blo 1691546 32988959 := bstep (se 1 (by rfl) ⟨24741719, by rfl⟩ : syracuseStep 32988959 = 49483439) B49483439
theorem B21700507 : Blo 1691546 21700507 := bstep (se 1 (by rfl) ⟨16275380, by rfl⟩ : syracuseStep 21700507 = 32550761) B32550761
theorem B3809519 : Blo 1691546 3809519 := bstep (se 1 (by rfl) ⟨2857139, by rfl⟩ : syracuseStep 3809519 = 5714279) B5714279
theorem B2539775 : Blo 1691546 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B3211913 : Blo 1691546 3211913 := bstep (se 2 (by rfl) ⟨1204467, by rfl⟩ : syracuseStep 3211913 = 2408935) B2408935
theorem B5145449 : Blo 1691546 5145449 := bstep (se 2 (by rfl) ⟨1929543, by rfl⟩ : syracuseStep 5145449 = 3859087) B3859087
theorem B19284965 : Blo 1691546 19284965 := bstep (se 4 (by rfl) ⟨1807965, by rfl⟩ : syracuseStep 19284965 = 3615931) B3615931
theorem B4285487 : Blo 1691546 4285487 := bstep (se 1 (by rfl) ⟨3214115, by rfl⟩ : syracuseStep 4285487 = 6428231) B6428231
theorem B5710931 : Blo 1691546 5710931 := bstep (se 1 (by rfl) ⟨4283198, by rfl⟩ : syracuseStep 5710931 = 8566397) B8566397
theorem B5710985 : Blo 1691546 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B12207287 : Blo 1691546 12207287 := bstep (se 1 (by rfl) ⟨9155465, by rfl⟩ : syracuseStep 12207287 = 18310931) B18310931
theorem B54871283 : Blo 1691546 54871283 := bstep (se 1 (by rfl) ⟨41153462, by rfl⟩ : syracuseStep 54871283 = 82306925) B82306925
theorem B27461339 : Blo 1691546 27461339 := bstep (se 1 (by rfl) ⟨20596004, by rfl⟩ : syracuseStep 27461339 = 41192009) B41192009
theorem B30877523 : Blo 1691546 30877523 := bstep (se 1 (by rfl) ⟨23158142, by rfl⟩ : syracuseStep 30877523 = 46316285) B46316285
theorem B19277675 : Blo 1691546 19277675 := bstep (se 1 (by rfl) ⟨14458256, by rfl⟩ : syracuseStep 19277675 = 28916513) B28916513
theorem B34760603 : Blo 1691546 34760603 := bstep (se 1 (by rfl) ⟨26070452, by rfl⟩ : syracuseStep 34760603 = 52140905) B52140905
theorem B43968439 : Blo 1691546 43968439 := bstep (se 1 (by rfl) ⟨32976329, by rfl⟩ : syracuseStep 43968439 = 65952659) B65952659
theorem B9636083 : Blo 1691546 9636083 := bstep (se 1 (by rfl) ⟨7227062, by rfl⟩ : syracuseStep 9636083 = 14454125) B14454125
theorem B7228241 : Blo 1691546 7228241 := bstep (se 2 (by rfl) ⟨2710590, by rfl⟩ : syracuseStep 7228241 = 5421181) B5421181
theorem B9776123 : Blo 1691546 9776123 := bstep (se 1 (by rfl) ⟨7332092, by rfl⟩ : syracuseStep 9776123 = 14664185) B14664185
theorem B6859885 : Blo 1691546 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B6425831 : Blo 1691546 6425831 := bstep (se 1 (by rfl) ⟨4819373, by rfl⟩ : syracuseStep 6425831 = 9638747) B9638747
theorem B3861881 : Blo 1691546 3861881 := bstep (se 2 (by rfl) ⟨1448205, by rfl⟩ : syracuseStep 3861881 = 2896411) B2896411
theorem B8564129 : Blo 1691546 8564129 := bstep (se 2 (by rfl) ⟨3211548, by rfl⟩ : syracuseStep 8564129 = 6423097) B6423097
theorem B7720363 : Blo 1691546 7720363 := bstep (se 1 (by rfl) ⟨5790272, by rfl⟩ : syracuseStep 7720363 = 11580545) B11580545
theorem B3214799 : Blo 1691546 3214799 := bstep (se 1 (by rfl) ⟨2411099, by rfl⟩ : syracuseStep 3214799 = 4822199) B4822199
theorem B1904359 : Blo 1691546 1904359 := bstep (se 1 (by rfl) ⟨1428269, by rfl⟩ : syracuseStep 1904359 = 2856539) B2856539
theorem B6098759 : Blo 1691546 6098759 := bstep (se 1 (by rfl) ⟨4574069, by rfl⟩ : syracuseStep 6098759 = 9148139) B9148139
theorem B1691559 : Blo 1691546 1691559 := bstep (se 1 (by rfl) ⟨1268669, by rfl⟩ : syracuseStep 1691559 = 2537339) B2537339
theorem B1691583 : Blo 1691546 1691583 := bstep (se 1 (by rfl) ⟨1268687, by rfl⟩ : syracuseStep 1691583 = 2537375) B2537375
theorem B2854939 : Blo 1691546 2854939 := bstep (se 1 (by rfl) ⟨2141204, by rfl⟩ : syracuseStep 2854939 = 4282409) B4282409
theorem B1691719 : Blo 1691546 1691719 := bstep (se 1 (by rfl) ⟨1268789, by rfl⟩ : syracuseStep 1691719 = 2537579) B2537579
theorem B1691739 : Blo 1691546 1691739 := bstep (se 1 (by rfl) ⟨1268804, by rfl⟩ : syracuseStep 1691739 = 2537609) B2537609
theorem B4821083 : Blo 1691546 4821083 := bstep (se 1 (by rfl) ⟨3615812, by rfl⟩ : syracuseStep 4821083 = 7231625) B7231625
theorem B1691839 : Blo 1691546 1691839 := bstep (se 1 (by rfl) ⟨1268879, by rfl⟩ : syracuseStep 1691839 = 2537759) B2537759
theorem B1904863 : Blo 1691546 1904863 := bstep (se 1 (by rfl) ⟨1428647, by rfl⟩ : syracuseStep 1904863 = 2857295) B2857295
theorem B6099407 : Blo 1691546 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B1692287 : Blo 1691546 1692287 := bstep (se 1 (by rfl) ⟨1269215, by rfl⟩ : syracuseStep 1692287 = 2538431) B2538431
theorem B1692319 : Blo 1691546 1692319 := bstep (se 1 (by rfl) ⟨1269239, by rfl⟩ : syracuseStep 1692319 = 2538479) B2538479
theorem B19280591 : Blo 1691546 19280591 := bstep (se 1 (by rfl) ⟨14460443, by rfl⟩ : syracuseStep 19280591 = 28920887) B28920887
theorem B2855675 : Blo 1691546 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B1692443 : Blo 1691546 1692443 := bstep (se 1 (by rfl) ⟨1269332, by rfl⟩ : syracuseStep 1692443 = 2538665) B2538665
theorem B8565587 : Blo 1691546 8565587 := bstep (se 1 (by rfl) ⟨6424190, by rfl⟩ : syracuseStep 8565587 = 12848381) B12848381
theorem B2855783 : Blo 1691546 2855783 := bstep (se 1 (by rfl) ⟨2141837, by rfl⟩ : syracuseStep 2855783 = 4283675) B4283675
theorem B5714927 : Blo 1691546 5714927 := bstep (se 1 (by rfl) ⟨4286195, by rfl⟩ : syracuseStep 5714927 = 8572391) B8572391
theorem B1692703 : Blo 1691546 1692703 := bstep (se 1 (by rfl) ⟨1269527, by rfl⟩ : syracuseStep 1692703 = 2539055) B2539055
theorem B1692719 : Blo 1691546 1692719 := bstep (se 1 (by rfl) ⟨1269539, by rfl⟩ : syracuseStep 1692719 = 2539079) B2539079
theorem B1692775 : Blo 1691546 1692775 := bstep (se 1 (by rfl) ⟨1269581, by rfl⟩ : syracuseStep 1692775 = 2539163) B2539163
theorem B1692839 : Blo 1691546 1692839 := bstep (se 1 (by rfl) ⟨1269629, by rfl⟩ : syracuseStep 1692839 = 2539259) B2539259
theorem B21992639 : Blo 1691546 21992639 := bstep (se 1 (by rfl) ⟨16494479, by rfl⟩ : syracuseStep 21992639 = 32988959) B32988959
theorem B9401795 : Blo 1691546 9401795 := bstep (se 1 (by rfl) ⟨7051346, by rfl⟩ : syracuseStep 9401795 = 14102693) B14102693
theorem B1693151 : Blo 1691546 1693151 := bstep (se 1 (by rfl) ⟨1269863, by rfl⟩ : syracuseStep 1693151 = 2539727) B2539727
theorem B2537783 : Blo 1691546 2537783 := bstep (se 1 (by rfl) ⟨1903337, by rfl⟩ : syracuseStep 2537783 = 3806675) B3806675
theorem B2537855 : Blo 1691546 2537855 := bstep (se 1 (by rfl) ⟨1903391, by rfl⟩ : syracuseStep 2537855 = 3806783) B3806783
theorem B2537963 : Blo 1691546 2537963 := bstep (se 1 (by rfl) ⟨1903472, by rfl⟩ : syracuseStep 2537963 = 3806945) B3806945
theorem B26040959 : Blo 1691546 26040959 := bstep (se 1 (by rfl) ⟨19530719, by rfl⟩ : syracuseStep 26040959 = 39061439) B39061439
theorem B2538203 : Blo 1691546 2538203 := bstep (se 1 (by rfl) ⟨1903652, by rfl⟩ : syracuseStep 2538203 = 3807305) B3807305
theorem B8567531 : Blo 1691546 8567531 := bstep (se 1 (by rfl) ⟨6425648, by rfl⟩ : syracuseStep 8567531 = 12851297) B12851297
theorem B3808169 : Blo 1691546 3808169 := bstep (se 2 (by rfl) ⟨1428063, by rfl⟩ : syracuseStep 3808169 = 2856127) B2856127
theorem B10738655 : Blo 1691546 10738655 := bstep (se 1 (by rfl) ⟨8053991, by rfl⟩ : syracuseStep 10738655 = 16107983) B16107983
theorem B211393597 : Blo 1691546 211393597 := bstep (se 3 (by rfl) ⟨39636299, by rfl⟩ : syracuseStep 211393597 = 79272599) B79272599
theorem B9149543 : Blo 1691546 9149543 := bstep (se 1 (by rfl) ⟨6862157, by rfl⟩ : syracuseStep 9149543 = 13724315) B13724315
theorem B28925261 : Blo 1691546 28925261 := bstep (se 3 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 28925261 = 10846973) B10846973
theorem B41721169 : Blo 1691546 41721169 := bstep (se 2 (by rfl) ⟨15645438, by rfl⟩ : syracuseStep 41721169 = 31290877) B31290877
theorem B2539049 : Blo 1691546 2539049 := bstep (se 2 (by rfl) ⟨952143, by rfl⟩ : syracuseStep 2539049 = 1904287) B1904287
theorem B2539175 : Blo 1691546 2539175 := bstep (se 1 (by rfl) ⟨1904381, by rfl⟩ : syracuseStep 2539175 = 3808763) B3808763
theorem B9641663 : Blo 1691546 9641663 := bstep (se 1 (by rfl) ⟨7231247, by rfl⟩ : syracuseStep 9641663 = 14462495) B14462495
theorem B422723285 : Blo 1691546 422723285 := bstep (se 7 (by rfl) ⟨4953788, by rfl⟩ : syracuseStep 422723285 = 9907577) B9907577
theorem B4636399 : Blo 1691546 4636399 := bstep (se 1 (by rfl) ⟨3477299, by rfl⟩ : syracuseStep 4636399 = 6954599) B6954599
theorem B2539247 : Blo 1691546 2539247 := bstep (se 1 (by rfl) ⟨1904435, by rfl⟩ : syracuseStep 2539247 = 3808871) B3808871
theorem B2539295 : Blo 1691546 2539295 := bstep (se 1 (by rfl) ⟨1904471, by rfl⟩ : syracuseStep 2539295 = 3808943) B3808943
theorem B2539355 : Blo 1691546 2539355 := bstep (se 1 (by rfl) ⟨1904516, by rfl⟩ : syracuseStep 2539355 = 3809033) B3809033
theorem B28934009 : Blo 1691546 28934009 := bstep (se 2 (by rfl) ⟨10850253, by rfl⟩ : syracuseStep 28934009 = 21700507) B21700507
theorem B11575183 : Blo 1691546 11575183 := bstep (se 1 (by rfl) ⟨8681387, by rfl⟩ : syracuseStep 11575183 = 17362775) B17362775
theorem B2539433 : Blo 1691546 2539433 := bstep (se 2 (by rfl) ⟨952287, by rfl⟩ : syracuseStep 2539433 = 1904575) B1904575
theorem B8134615 : Blo 1691546 8134615 := bstep (se 1 (by rfl) ⟨6100961, by rfl⟩ : syracuseStep 8134615 = 12201923) B12201923
theorem B2539679 : Blo 1691546 2539679 := bstep (se 1 (by rfl) ⟨1904759, by rfl⟩ : syracuseStep 2539679 = 3809519) B3809519
theorem B2539817 : Blo 1691546 2539817 := bstep (se 2 (by rfl) ⟨952431, by rfl⟩ : syracuseStep 2539817 = 1904863) B1904863
theorem B12853727 : Blo 1691546 12853727 := bstep (se 1 (by rfl) ⟨9640295, by rfl⟩ : syracuseStep 12853727 = 19280591) B19280591
theorem B58647037 : Blo 1691546 58647037 := bstep (se 3 (by rfl) ⟨10996319, by rfl⟩ : syracuseStep 58647037 = 21992639) B21992639
theorem B5710391 : Blo 1691546 5710391 := bstep (se 1 (by rfl) ⟨4282793, by rfl⟩ : syracuseStep 5710391 = 8565587) B8565587
theorem B3809951 : Blo 1691546 3809951 := bstep (se 1 (by rfl) ⟨2857463, by rfl⟩ : syracuseStep 3809951 = 5714927) B5714927
theorem B6267863 : Blo 1691546 6267863 := bstep (se 1 (by rfl) ⟨4700897, by rfl⟩ : syracuseStep 6267863 = 9401795) B9401795
theorem B6424055 : Blo 1691546 6424055 := bstep (se 1 (by rfl) ⟨4818041, by rfl⟩ : syracuseStep 6424055 = 9636083) B9636083
theorem B17360639 : Blo 1691546 17360639 := bstep (se 1 (by rfl) ⟨13020479, by rfl⟩ : syracuseStep 17360639 = 26040959) B26040959
theorem B5711687 : Blo 1691546 5711687 := bstep (se 1 (by rfl) ⟨4283765, by rfl⟩ : syracuseStep 5711687 = 8567531) B8567531
theorem B4818827 : Blo 1691546 4818827 := bstep (se 1 (by rfl) ⟨3614120, by rfl⟩ : syracuseStep 4818827 = 7228241) B7228241
theorem B2574587 : Blo 1691546 2574587 := bstep (se 1 (by rfl) ⟨1930940, by rfl⟩ : syracuseStep 2574587 = 3861881) B3861881
theorem B234498341 : Blo 1691546 234498341 := bstep (se 4 (by rfl) ⟨21984219, by rfl⟩ : syracuseStep 234498341 = 43968439) B43968439
theorem B281815523 : Blo 1691546 281815523 := bstep (se 1 (by rfl) ⟨211361642, by rfl⟩ : syracuseStep 281815523 = 422723285) B422723285
theorem B4065839 : Blo 1691546 4065839 := bstep (se 1 (by rfl) ⟨3049379, by rfl⟩ : syracuseStep 4065839 = 6098759) B6098759
theorem B3214055 : Blo 1691546 3214055 := bstep (se 1 (by rfl) ⟨2410541, by rfl⟩ : syracuseStep 3214055 = 4821083) B4821083
theorem B4066271 : Blo 1691546 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B1903783 : Blo 1691546 1903783 := bstep (se 1 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 1903783 = 2855675) B2855675
theorem B1903855 : Blo 1691546 1903855 := bstep (se 1 (by rfl) ⟨1427891, by rfl⟩ : syracuseStep 1903855 = 2855783) B2855783
theorem B12856643 : Blo 1691546 12856643 := bstep (se 1 (by rfl) ⟨9642482, by rfl⟩ : syracuseStep 12856643 = 19284965) B19284965
theorem B281858129 : Blo 1691546 281858129 := bstep (se 2 (by rfl) ⟨105696798, by rfl⟩ : syracuseStep 281858129 = 211393597) B211393597
theorem B9146513 : Blo 1691546 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B1691855 : Blo 1691546 1691855 := bstep (se 1 (by rfl) ⟨1268891, by rfl⟩ : syracuseStep 1691855 = 2537783) B2537783
theorem B1691903 : Blo 1691546 1691903 := bstep (se 1 (by rfl) ⟨1268927, by rfl⟩ : syracuseStep 1691903 = 2537855) B2537855
theorem B1691975 : Blo 1691546 1691975 := bstep (se 1 (by rfl) ⟨1268981, by rfl⟩ : syracuseStep 1691975 = 2537963) B2537963
theorem B8565101 : Blo 1691546 8565101 := bstep (se 3 (by rfl) ⟨1605956, by rfl⟩ : syracuseStep 8565101 = 3211913) B3211913
theorem B55628225 : Blo 1691546 55628225 := bstep (se 2 (by rfl) ⟨20860584, by rfl⟩ : syracuseStep 55628225 = 41721169) B41721169
theorem B1692135 : Blo 1691546 1692135 := bstep (se 1 (by rfl) ⟨1269101, by rfl⟩ : syracuseStep 1692135 = 2538203) B2538203
theorem B10293817 : Blo 1691546 10293817 := bstep (se 2 (by rfl) ⟨3860181, by rfl⟩ : syracuseStep 10293817 = 7720363) B7720363
theorem B6517415 : Blo 1691546 6517415 := bstep (se 1 (by rfl) ⟨4888061, by rfl⟩ : syracuseStep 6517415 = 9776123) B9776123
theorem B6099695 : Blo 1691546 6099695 := bstep (se 1 (by rfl) ⟨4574771, by rfl⟩ : syracuseStep 6099695 = 9149543) B9149543
theorem B2143199 : Blo 1691546 2143199 := bstep (se 1 (by rfl) ⟨1607399, by rfl⟩ : syracuseStep 2143199 = 3214799) B3214799
theorem B6181865 : Blo 1691546 6181865 := bstep (se 2 (by rfl) ⟨2318199, by rfl⟩ : syracuseStep 6181865 = 4636399) B4636399
theorem B1692699 : Blo 1691546 1692699 := bstep (se 1 (by rfl) ⟨1269524, by rfl⟩ : syracuseStep 1692699 = 2539049) B2539049
theorem B1692783 : Blo 1691546 1692783 := bstep (se 1 (by rfl) ⟨1269587, by rfl⟩ : syracuseStep 1692783 = 2539175) B2539175
theorem B6427775 : Blo 1691546 6427775 := bstep (se 1 (by rfl) ⟨4820831, by rfl⟩ : syracuseStep 6427775 = 9641663) B9641663
theorem B1692831 : Blo 1691546 1692831 := bstep (se 1 (by rfl) ⟨1269623, by rfl⟩ : syracuseStep 1692831 = 2539247) B2539247
theorem B1692863 : Blo 1691546 1692863 := bstep (se 1 (by rfl) ⟨1269647, by rfl⟩ : syracuseStep 1692863 = 2539295) B2539295
theorem B1692903 : Blo 1691546 1692903 := bstep (se 1 (by rfl) ⟨1269677, by rfl⟩ : syracuseStep 1692903 = 2539355) B2539355
theorem B19289339 : Blo 1691546 19289339 := bstep (se 1 (by rfl) ⟨14467004, by rfl⟩ : syracuseStep 19289339 = 28934009) B28934009
theorem B1692955 : Blo 1691546 1692955 := bstep (se 1 (by rfl) ⟨1269716, by rfl⟩ : syracuseStep 1692955 = 2539433) B2539433
theorem B3806585 : Blo 1691546 3806585 := bstep (se 2 (by rfl) ⟨1427469, by rfl⟩ : syracuseStep 3806585 = 2854939) B2854939
theorem B1693183 : Blo 1691546 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B32552765 : Blo 1691546 32552765 := bstep (se 3 (by rfl) ⟨6103643, by rfl⟩ : syracuseStep 32552765 = 12207287) B12207287
theorem B146323421 : Blo 1691546 146323421 := bstep (se 3 (by rfl) ⟨27435641, by rfl⟩ : syracuseStep 146323421 = 54871283) B54871283
theorem B2856991 : Blo 1691546 2856991 := bstep (se 1 (by rfl) ⟨2142743, by rfl⟩ : syracuseStep 2856991 = 4285487) B4285487
theorem B3807287 : Blo 1691546 3807287 := bstep (se 1 (by rfl) ⟨2855465, by rfl⟩ : syracuseStep 3807287 = 5710931) B5710931
theorem B3807323 : Blo 1691546 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B18307559 : Blo 1691546 18307559 := bstep (se 1 (by rfl) ⟨13730669, by rfl⟩ : syracuseStep 18307559 = 27461339) B27461339
theorem B20585015 : Blo 1691546 20585015 := bstep (se 1 (by rfl) ⟨15438761, by rfl⟩ : syracuseStep 20585015 = 30877523) B30877523
theorem B12851783 : Blo 1691546 12851783 := bstep (se 1 (by rfl) ⟨9638837, by rfl⟩ : syracuseStep 12851783 = 19277675) B19277675
theorem B23173735 : Blo 1691546 23173735 := bstep (se 1 (by rfl) ⟨17380301, by rfl⟩ : syracuseStep 23173735 = 34760603) B34760603
theorem B2538779 : Blo 1691546 2538779 := bstep (se 1 (by rfl) ⟨1904084, by rfl⟩ : syracuseStep 2538779 = 3808169) B3808169
theorem B7159103 : Blo 1691546 7159103 := bstep (se 1 (by rfl) ⟨5369327, by rfl⟩ : syracuseStep 7159103 = 10738655) B10738655
theorem B4283887 : Blo 1691546 4283887 := bstep (se 1 (by rfl) ⟨3212915, by rfl⟩ : syracuseStep 4283887 = 6425831) B6425831
theorem B19283507 : Blo 1691546 19283507 := bstep (se 1 (by rfl) ⟨14462630, by rfl⟩ : syracuseStep 19283507 = 28925261) B28925261
theorem B5709419 : Blo 1691546 5709419 := bstep (se 1 (by rfl) ⟨4282064, by rfl⟩ : syracuseStep 5709419 = 8564129) B8564129
theorem B13721197 : Blo 1691546 13721197 := bstep (se 3 (by rfl) ⟨2572724, by rfl⟩ : syracuseStep 13721197 = 5145449) B5145449
theorem B2539145 : Blo 1691546 2539145 := bstep (se 2 (by rfl) ⟨952179, by rfl⟩ : syracuseStep 2539145 = 1904359) B1904359
theorem B15433577 : Blo 1691546 15433577 := bstep (se 2 (by rfl) ⟨5787591, by rfl⟩ : syracuseStep 15433577 = 11575183) B11575183
theorem B10846153 : Blo 1691546 10846153 := bstep (se 2 (by rfl) ⟨4067307, by rfl⟩ : syracuseStep 10846153 = 8134615) B8134615
theorem B3809321 : Blo 1691546 3809321 := bstep (se 2 (by rfl) ⟨1428495, by rfl⟩ : syracuseStep 3809321 = 2856991) B2856991
theorem B5710067 : Blo 1691546 5710067 := bstep (se 1 (by rfl) ⟨4282550, by rfl⟩ : syracuseStep 5710067 = 8565101) B8565101
theorem B37085483 : Blo 1691546 37085483 := bstep (se 1 (by rfl) ⟨27814112, by rfl⟩ : syracuseStep 37085483 = 55628225) B55628225
theorem B8569151 : Blo 1691546 8569151 := bstep (se 1 (by rfl) ⟨6426863, by rfl⟩ : syracuseStep 8569151 = 12853727) B12853727
theorem B2539967 : Blo 1691546 2539967 := bstep (se 1 (by rfl) ⟨1904975, by rfl⟩ : syracuseStep 2539967 = 3809951) B3809951
theorem B4178575 : Blo 1691546 4178575 := bstep (se 1 (by rfl) ⟨3133931, by rfl⟩ : syracuseStep 4178575 = 6267863) B6267863
theorem B4121243 : Blo 1691546 4121243 := bstep (se 1 (by rfl) ⟨3090932, by rfl⟩ : syracuseStep 4121243 = 6181865) B6181865
theorem B4285183 : Blo 1691546 4285183 := bstep (se 1 (by rfl) ⟨3213887, by rfl⟩ : syracuseStep 4285183 = 6427775) B6427775
theorem B21701843 : Blo 1691546 21701843 := bstep (se 1 (by rfl) ⟨16276382, by rfl⟩ : syracuseStep 21701843 = 32552765) B32552765
theorem B3212551 : Blo 1691546 3212551 := bstep (se 1 (by rfl) ⟨2409413, by rfl⟩ : syracuseStep 3212551 = 4818827) B4818827
theorem B187877015 : Blo 1691546 187877015 := bstep (se 1 (by rfl) ⟨140907761, by rfl⟩ : syracuseStep 187877015 = 281815523) B281815523
theorem B13723343 : Blo 1691546 13723343 := bstep (se 1 (by rfl) ⟨10292507, by rfl⟩ : syracuseStep 13723343 = 20585015) B20585015
theorem B5711849 : Blo 1691546 5711849 := bstep (se 2 (by rfl) ⟨2141943, by rfl⟩ : syracuseStep 5711849 = 4283887) B4283887
theorem B18294929 : Blo 1691546 18294929 := bstep (se 2 (by rfl) ⟨6860598, by rfl⟩ : syracuseStep 18294929 = 13721197) B13721197
theorem B8571095 : Blo 1691546 8571095 := bstep (se 1 (by rfl) ⟨6428321, by rfl⟩ : syracuseStep 8571095 = 12856643) B12856643
theorem B12855671 : Blo 1691546 12855671 := bstep (se 1 (by rfl) ⟨9641753, by rfl⟩ : syracuseStep 12855671 = 19283507) B19283507
theorem B14461537 : Blo 1691546 14461537 := bstep (se 2 (by rfl) ⟨5423076, by rfl⟩ : syracuseStep 14461537 = 10846153) B10846153
theorem B6097675 : Blo 1691546 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B4344943 : Blo 1691546 4344943 := bstep (se 1 (by rfl) ⟨3258707, by rfl⟩ : syracuseStep 4344943 = 6517415) B6517415
theorem B4066463 : Blo 1691546 4066463 := bstep (se 1 (by rfl) ⟨3049847, by rfl⟩ : syracuseStep 4066463 = 6099695) B6099695
theorem B78196049 : Blo 1691546 78196049 := bstep (se 2 (by rfl) ⟨29323518, by rfl⟩ : syracuseStep 78196049 = 58647037) B58647037
theorem B13725089 : Blo 1691546 13725089 := bstep (se 2 (by rfl) ⟨5146908, by rfl⟩ : syracuseStep 13725089 = 10293817) B10293817
theorem B1716391 : Blo 1691546 1716391 := bstep (se 1 (by rfl) ⟨1287293, by rfl⟩ : syracuseStep 1716391 = 2574587) B2574587
theorem B156332227 : Blo 1691546 156332227 := bstep (se 1 (by rfl) ⟨117249170, by rfl⟩ : syracuseStep 156332227 = 234498341) B234498341
theorem B2142703 : Blo 1691546 2142703 := bstep (se 1 (by rfl) ⟨1607027, by rfl⟩ : syracuseStep 2142703 = 3214055) B3214055
theorem B1692519 : Blo 1691546 1692519 := bstep (se 1 (by rfl) ⟨1269389, by rfl⟩ : syracuseStep 1692519 = 2538779) B2538779
theorem B4772735 : Blo 1691546 4772735 := bstep (se 1 (by rfl) ⟨3579551, by rfl⟩ : syracuseStep 4772735 = 7159103) B7159103
theorem B3806279 : Blo 1691546 3806279 := bstep (se 1 (by rfl) ⟨2854709, by rfl⟩ : syracuseStep 3806279 = 5709419) B5709419
theorem B1692763 : Blo 1691546 1692763 := bstep (se 1 (by rfl) ⟨1269572, by rfl⟩ : syracuseStep 1692763 = 2539145) B2539145
theorem B5715197 : Blo 1691546 5715197 := bstep (se 3 (by rfl) ⟨1071599, by rfl⟩ : syracuseStep 5715197 = 2143199) B2143199
theorem B187905419 : Blo 1691546 187905419 := bstep (se 1 (by rfl) ⟨140929064, by rfl⟩ : syracuseStep 187905419 = 281858129) B281858129
theorem B1693119 : Blo 1691546 1693119 := bstep (se 1 (by rfl) ⟨1269839, by rfl⟩ : syracuseStep 1693119 = 2539679) B2539679
theorem B1693211 : Blo 1691546 1693211 := bstep (se 1 (by rfl) ⟨1269908, by rfl⟩ : syracuseStep 1693211 = 2539817) B2539817
theorem B3806927 : Blo 1691546 3806927 := bstep (se 1 (by rfl) ⟨2855195, by rfl⟩ : syracuseStep 3806927 = 5710391) B5710391
theorem B30898313 : Blo 1691546 30898313 := bstep (se 2 (by rfl) ⟨11586867, by rfl⟩ : syracuseStep 30898313 = 23173735) B23173735
theorem B12859559 : Blo 1691546 12859559 := bstep (se 1 (by rfl) ⟨9644669, by rfl⟩ : syracuseStep 12859559 = 19289339) B19289339
theorem B2537723 : Blo 1691546 2537723 := bstep (se 1 (by rfl) ⟨1903292, by rfl⟩ : syracuseStep 2537723 = 3806585) B3806585
theorem B4282703 : Blo 1691546 4282703 := bstep (se 1 (by rfl) ⟨3212027, by rfl⟩ : syracuseStep 4282703 = 6424055) B6424055
theorem B11573759 : Blo 1691546 11573759 := bstep (se 1 (by rfl) ⟨8680319, by rfl⟩ : syracuseStep 11573759 = 17360639) B17360639
theorem B3807791 : Blo 1691546 3807791 := bstep (se 1 (by rfl) ⟨2855843, by rfl⟩ : syracuseStep 3807791 = 5711687) B5711687
theorem B97548947 : Blo 1691546 97548947 := bstep (se 1 (by rfl) ⟨73161710, by rfl⟩ : syracuseStep 97548947 = 146323421) B146323421
theorem B2538191 : Blo 1691546 2538191 := bstep (se 1 (by rfl) ⟨1903643, by rfl⟩ : syracuseStep 2538191 = 3807287) B3807287
theorem B2538215 : Blo 1691546 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B2538377 : Blo 1691546 2538377 := bstep (se 2 (by rfl) ⟨951891, by rfl⟩ : syracuseStep 2538377 = 1903783) B1903783
theorem B2538473 : Blo 1691546 2538473 := bstep (se 2 (by rfl) ⟨951927, by rfl⟩ : syracuseStep 2538473 = 1903855) B1903855
theorem B12205039 : Blo 1691546 12205039 := bstep (se 1 (by rfl) ⟨9153779, by rfl⟩ : syracuseStep 12205039 = 18307559) B18307559
theorem B2710559 : Blo 1691546 2710559 := bstep (se 1 (by rfl) ⟨2032919, by rfl⟩ : syracuseStep 2710559 = 4065839) B4065839
theorem B8567855 : Blo 1691546 8567855 := bstep (se 1 (by rfl) ⟨6425891, by rfl⟩ : syracuseStep 8567855 = 12851783) B12851783
theorem B2710847 : Blo 1691546 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B10289051 : Blo 1691546 10289051 := bstep (se 1 (by rfl) ⟨7716788, by rfl⟩ : syracuseStep 10289051 = 15433577) B15433577
theorem B2539547 : Blo 1691546 2539547 := bstep (se 1 (by rfl) ⟨1904660, by rfl⟩ : syracuseStep 2539547 = 3809321) B3809321
theorem B98894621 : Blo 1691546 98894621 := bstep (se 3 (by rfl) ⟨18542741, by rfl⟩ : syracuseStep 98894621 = 37085483) B37085483
theorem B14467895 : Blo 1691546 14467895 := bstep (se 1 (by rfl) ⟨10850921, by rfl⟩ : syracuseStep 14467895 = 21701843) B21701843
theorem B3810131 : Blo 1691546 3810131 := bstep (se 1 (by rfl) ⟨2857598, by rfl⟩ : syracuseStep 3810131 = 5715197) B5715197
theorem B5571433 : Blo 1691546 5571433 := bstep (se 2 (by rfl) ⟨2089287, by rfl⟩ : syracuseStep 5571433 = 4178575) B4178575
theorem B5793257 : Blo 1691546 5793257 := bstep (se 2 (by rfl) ⟨2172471, by rfl⟩ : syracuseStep 5793257 = 4344943) B4344943
theorem B8570447 : Blo 1691546 8570447 := bstep (se 1 (by rfl) ⟨6427835, by rfl⟩ : syracuseStep 8570447 = 12855671) B12855671
theorem B5711903 : Blo 1691546 5711903 := bstep (se 1 (by rfl) ⟨4283927, by rfl⟩ : syracuseStep 5711903 = 8567855) B8567855
theorem B6859367 : Blo 1691546 6859367 := bstep (se 1 (by rfl) ⟨5144525, by rfl⟩ : syracuseStep 6859367 = 10289051) B10289051
theorem B5712767 : Blo 1691546 5712767 := bstep (se 1 (by rfl) ⟨4284575, by rfl⟩ : syracuseStep 5712767 = 8569151) B8569151
theorem B2288521 : Blo 1691546 2288521 := bstep (se 2 (by rfl) ⟨858195, by rfl⟩ : syracuseStep 2288521 = 1716391) B1716391
theorem B2747495 : Blo 1691546 2747495 := bstep (se 1 (by rfl) ⟨2060621, by rfl⟩ : syracuseStep 2747495 = 4121243) B4121243
theorem B7228925 : Blo 1691546 7228925 := bstep (se 3 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 7228925 = 2710847) B2710847
theorem B5713577 : Blo 1691546 5713577 := bstep (se 2 (by rfl) ⟨2142591, by rfl⟩ : syracuseStep 5713577 = 4285183) B4285183
theorem B8130233 : Blo 1691546 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B125251343 : Blo 1691546 125251343 := bstep (se 1 (by rfl) ⟨93938507, by rfl⟩ : syracuseStep 125251343 = 187877015) B187877015
theorem B16273385 : Blo 1691546 16273385 := bstep (se 2 (by rfl) ⟨6102519, by rfl⟩ : syracuseStep 16273385 = 12205039) B12205039
theorem B20598875 : Blo 1691546 20598875 := bstep (se 1 (by rfl) ⟨15449156, by rfl⟩ : syracuseStep 20598875 = 30898313) B30898313
theorem B8573039 : Blo 1691546 8573039 := bstep (se 1 (by rfl) ⟨6429779, by rfl⟩ : syracuseStep 8573039 = 12859559) B12859559
theorem B5714063 : Blo 1691546 5714063 := bstep (se 1 (by rfl) ⟨4285547, by rfl⟩ : syracuseStep 5714063 = 8571095) B8571095
theorem B1691815 : Blo 1691546 1691815 := bstep (se 1 (by rfl) ⟨1268861, by rfl⟩ : syracuseStep 1691815 = 2537723) B2537723
theorem B2855135 : Blo 1691546 2855135 := bstep (se 1 (by rfl) ⟨2141351, by rfl⟩ : syracuseStep 2855135 = 4282703) B4282703
theorem B65032631 : Blo 1691546 65032631 := bstep (se 1 (by rfl) ⟨48774473, by rfl⟩ : syracuseStep 65032631 = 97548947) B97548947
theorem B1692127 : Blo 1691546 1692127 := bstep (se 1 (by rfl) ⟨1269095, by rfl⟩ : syracuseStep 1692127 = 2538191) B2538191
theorem B1692143 : Blo 1691546 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B1692251 : Blo 1691546 1692251 := bstep (se 1 (by rfl) ⟨1269188, by rfl⟩ : syracuseStep 1692251 = 2538377) B2538377
theorem B1692315 : Blo 1691546 1692315 := bstep (se 1 (by rfl) ⟨1269236, by rfl⟩ : syracuseStep 1692315 = 2538473) B2538473
theorem B1807039 : Blo 1691546 1807039 := bstep (se 1 (by rfl) ⟨1355279, by rfl⟩ : syracuseStep 1807039 = 2710559) B2710559
theorem B52130699 : Blo 1691546 52130699 := bstep (se 1 (by rfl) ⟨39098024, by rfl⟩ : syracuseStep 52130699 = 78196049) B78196049
theorem B3806711 : Blo 1691546 3806711 := bstep (se 1 (by rfl) ⟨2855033, by rfl⟩ : syracuseStep 3806711 = 5710067) B5710067
theorem B208442969 : Blo 1691546 208442969 := bstep (se 2 (by rfl) ⟨78166113, by rfl⟩ : syracuseStep 208442969 = 156332227) B156332227
theorem B1693311 : Blo 1691546 1693311 := bstep (se 1 (by rfl) ⟨1269983, by rfl⟩ : syracuseStep 1693311 = 2539967) B2539967
theorem B2856937 : Blo 1691546 2856937 := bstep (se 2 (by rfl) ⟨1071351, by rfl⟩ : syracuseStep 2856937 = 2142703) B2142703
theorem B2537519 : Blo 1691546 2537519 := bstep (se 1 (by rfl) ⟨1903139, by rfl⟩ : syracuseStep 2537519 = 3806279) B3806279
theorem B19282049 : Blo 1691546 19282049 := bstep (se 2 (by rfl) ⟨7230768, by rfl⟩ : syracuseStep 19282049 = 14461537) B14461537
theorem B125270279 : Blo 1691546 125270279 := bstep (se 1 (by rfl) ⟨93952709, by rfl⟩ : syracuseStep 125270279 = 187905419) B187905419
theorem B2537951 : Blo 1691546 2537951 := bstep (se 1 (by rfl) ⟨1903463, by rfl⟩ : syracuseStep 2537951 = 3806927) B3806927
theorem B9148895 : Blo 1691546 9148895 := bstep (se 1 (by rfl) ⟨6861671, by rfl⟩ : syracuseStep 9148895 = 13723343) B13723343
theorem B3807899 : Blo 1691546 3807899 := bstep (se 1 (by rfl) ⟨2855924, by rfl⟩ : syracuseStep 3807899 = 5711849) B5711849
theorem B12196619 : Blo 1691546 12196619 := bstep (se 1 (by rfl) ⟨9147464, by rfl⟩ : syracuseStep 12196619 = 18294929) B18294929
theorem B7715839 : Blo 1691546 7715839 := bstep (se 1 (by rfl) ⟨5786879, by rfl⟩ : syracuseStep 7715839 = 11573759) B11573759
theorem B4283401 : Blo 1691546 4283401 := bstep (se 2 (by rfl) ⟨1606275, by rfl⟩ : syracuseStep 4283401 = 3212551) B3212551
theorem B2538527 : Blo 1691546 2538527 := bstep (se 1 (by rfl) ⟨1903895, by rfl⟩ : syracuseStep 2538527 = 3807791) B3807791
theorem B2710975 : Blo 1691546 2710975 := bstep (se 1 (by rfl) ⟨2033231, by rfl⟩ : syracuseStep 2710975 = 4066463) B4066463
theorem B9150059 : Blo 1691546 9150059 := bstep (se 1 (by rfl) ⟨6862544, by rfl⟩ : syracuseStep 9150059 = 13725089) B13725089
theorem B203636693 : Blo 1691546 203636693 := bstep (se 7 (by rfl) ⟨2386367, by rfl⟩ : syracuseStep 203636693 = 4772735) B4772735
theorem B3809375 : Blo 1691546 3809375 := bstep (se 1 (by rfl) ⟨2857031, by rfl⟩ : syracuseStep 3809375 = 5714063) B5714063
theorem B65929747 : Blo 1691546 65929747 := bstep (se 1 (by rfl) ⟨49447310, by rfl⟩ : syracuseStep 65929747 = 98894621) B98894621
theorem B2540087 : Blo 1691546 2540087 := bstep (se 1 (by rfl) ⟨1905065, by rfl⟩ : syracuseStep 2540087 = 3810131) B3810131
theorem B138961979 : Blo 1691546 138961979 := bstep (se 1 (by rfl) ⟨104221484, by rfl⟩ : syracuseStep 138961979 = 208442969) B208442969
theorem B5711201 : Blo 1691546 5711201 := bstep (se 2 (by rfl) ⟨2141700, by rfl⟩ : syracuseStep 5711201 = 4283401) B4283401
theorem B12854699 : Blo 1691546 12854699 := bstep (se 1 (by rfl) ⟨9641024, by rfl⟩ : syracuseStep 12854699 = 19282049) B19282049
theorem B4572911 : Blo 1691546 4572911 := bstep (se 1 (by rfl) ⟨3429683, by rfl⟩ : syracuseStep 4572911 = 6859367) B6859367
theorem B29714309 : Blo 1691546 29714309 := bstep (se 4 (by rfl) ⟨2785716, by rfl⟩ : syracuseStep 29714309 = 5571433) B5571433
theorem B3614633 : Blo 1691546 3614633 := bstep (se 2 (by rfl) ⟨1355487, by rfl⟩ : syracuseStep 3614633 = 2710975) B2710975
theorem B4819283 : Blo 1691546 4819283 := bstep (se 1 (by rfl) ⟨3614462, by rfl⟩ : syracuseStep 4819283 = 7228925) B7228925
theorem B10848923 : Blo 1691546 10848923 := bstep (se 1 (by rfl) ⟨8136692, by rfl⟩ : syracuseStep 10848923 = 16273385) B16273385
theorem B13732583 : Blo 1691546 13732583 := bstep (se 1 (by rfl) ⟨10299437, by rfl⟩ : syracuseStep 13732583 = 20598875) B20598875
theorem B1903423 : Blo 1691546 1903423 := bstep (se 1 (by rfl) ⟨1427567, by rfl⟩ : syracuseStep 1903423 = 2855135) B2855135
theorem B43355087 : Blo 1691546 43355087 := bstep (se 1 (by rfl) ⟨32516315, by rfl⟩ : syracuseStep 43355087 = 65032631) B65032631
theorem B9645263 : Blo 1691546 9645263 := bstep (se 1 (by rfl) ⟨7233947, by rfl⟩ : syracuseStep 9645263 = 14467895) B14467895
theorem B34753799 : Blo 1691546 34753799 := bstep (se 1 (by rfl) ⟨26065349, by rfl⟩ : syracuseStep 34753799 = 52130699) B52130699
theorem B3862171 : Blo 1691546 3862171 := bstep (se 1 (by rfl) ⟨2896628, by rfl⟩ : syracuseStep 3862171 = 5793257) B5793257
theorem B9637541 : Blo 1691546 9637541 := bstep (se 4 (by rfl) ⟨903519, by rfl⟩ : syracuseStep 9637541 = 1807039) B1807039
theorem B5713631 : Blo 1691546 5713631 := bstep (se 1 (by rfl) ⟨4285223, by rfl⟩ : syracuseStep 5713631 = 8570447) B8570447
theorem B3051361 : Blo 1691546 3051361 := bstep (se 2 (by rfl) ⟨1144260, by rfl⟩ : syracuseStep 3051361 = 2288521) B2288521
theorem B1691679 : Blo 1691546 1691679 := bstep (se 1 (by rfl) ⟨1268759, by rfl⟩ : syracuseStep 1691679 = 2537519) B2537519
theorem B83513519 : Blo 1691546 83513519 := bstep (se 1 (by rfl) ⟨62635139, by rfl⟩ : syracuseStep 83513519 = 125270279) B125270279
theorem B1691967 : Blo 1691546 1691967 := bstep (se 1 (by rfl) ⟨1268975, by rfl⟩ : syracuseStep 1691967 = 2537951) B2537951
theorem B6099263 : Blo 1691546 6099263 := bstep (se 1 (by rfl) ⟨4574447, by rfl⟩ : syracuseStep 6099263 = 9148895) B9148895
theorem B21680621 : Blo 1691546 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B8131079 : Blo 1691546 8131079 := bstep (se 1 (by rfl) ⟨6098309, by rfl⟩ : syracuseStep 8131079 = 12196619) B12196619
theorem B1692351 : Blo 1691546 1692351 := bstep (se 1 (by rfl) ⟨1269263, by rfl⟩ : syracuseStep 1692351 = 2538527) B2538527
theorem B1831663 : Blo 1691546 1831663 := bstep (se 1 (by rfl) ⟨1373747, by rfl⟩ : syracuseStep 1831663 = 2747495) B2747495
theorem B6100039 : Blo 1691546 6100039 := bstep (se 1 (by rfl) ⟨4575029, by rfl⟩ : syracuseStep 6100039 = 9150059) B9150059
theorem B1693031 : Blo 1691546 1693031 := bstep (se 1 (by rfl) ⟨1269773, by rfl⟩ : syracuseStep 1693031 = 2539547) B2539547
theorem B5715359 : Blo 1691546 5715359 := bstep (se 1 (by rfl) ⟨4286519, by rfl⟩ : syracuseStep 5715359 = 8573039) B8573039
theorem B2537807 : Blo 1691546 2537807 := bstep (se 1 (by rfl) ⟨1903355, by rfl⟩ : syracuseStep 2537807 = 3806711) B3806711
theorem B10287785 : Blo 1691546 10287785 := bstep (se 2 (by rfl) ⟨3857919, by rfl⟩ : syracuseStep 10287785 = 7715839) B7715839
theorem B3807935 : Blo 1691546 3807935 := bstep (se 1 (by rfl) ⟨2855951, by rfl⟩ : syracuseStep 3807935 = 5711903) B5711903
theorem B2538599 : Blo 1691546 2538599 := bstep (se 1 (by rfl) ⟨1903949, by rfl⟩ : syracuseStep 2538599 = 3807899) B3807899
theorem B3808511 : Blo 1691546 3808511 := bstep (se 1 (by rfl) ⟨2856383, by rfl⟩ : syracuseStep 3808511 = 5712767) B5712767
theorem B3809051 : Blo 1691546 3809051 := bstep (se 1 (by rfl) ⟨2856788, by rfl⟩ : syracuseStep 3809051 = 5713577) B5713577
theorem B83500895 : Blo 1691546 83500895 := bstep (se 1 (by rfl) ⟨62625671, by rfl⟩ : syracuseStep 83500895 = 125251343) B125251343
theorem B3809249 : Blo 1691546 3809249 := bstep (se 2 (by rfl) ⟨1428468, by rfl⟩ : syracuseStep 3809249 = 2856937) B2856937
theorem B135757795 : Blo 1691546 135757795 := bstep (se 1 (by rfl) ⟨101818346, by rfl⟩ : syracuseStep 135757795 = 203636693) B203636693
theorem B2539583 : Blo 1691546 2539583 := bstep (se 1 (by rfl) ⟨1904687, by rfl⟩ : syracuseStep 2539583 = 3809375) B3809375
theorem B3810239 : Blo 1691546 3810239 := bstep (se 1 (by rfl) ⟨2857679, by rfl⟩ : syracuseStep 3810239 = 5715359) B5715359
theorem B8569799 : Blo 1691546 8569799 := bstep (se 1 (by rfl) ⟨6427349, by rfl⟩ : syracuseStep 8569799 = 12854699) B12854699
theorem B3048607 : Blo 1691546 3048607 := bstep (se 1 (by rfl) ⟨2286455, by rfl⟩ : syracuseStep 3048607 = 4572911) B4572911
theorem B19809539 : Blo 1691546 19809539 := bstep (se 1 (by rfl) ⟨14857154, by rfl⟩ : syracuseStep 19809539 = 29714309) B29714309
theorem B2409755 : Blo 1691546 2409755 := bstep (se 1 (by rfl) ⟨1807316, by rfl⟩ : syracuseStep 2409755 = 3614633) B3614633
theorem B3212855 : Blo 1691546 3212855 := bstep (se 1 (by rfl) ⟨2409641, by rfl⟩ : syracuseStep 3212855 = 4819283) B4819283
theorem B6858523 : Blo 1691546 6858523 := bstep (se 1 (by rfl) ⟨5143892, by rfl⟩ : syracuseStep 6858523 = 10287785) B10287785
theorem B36620221 : Blo 1691546 36620221 := bstep (se 3 (by rfl) ⟨6866291, by rfl⟩ : syracuseStep 36620221 = 13732583) B13732583
theorem B28903391 : Blo 1691546 28903391 := bstep (se 1 (by rfl) ⟨21677543, by rfl⟩ : syracuseStep 28903391 = 43355087) B43355087
theorem B23169199 : Blo 1691546 23169199 := bstep (se 1 (by rfl) ⟨17376899, by rfl⟩ : syracuseStep 23169199 = 34753799) B34753799
theorem B6425027 : Blo 1691546 6425027 := bstep (se 1 (by rfl) ⟨4818770, by rfl⟩ : syracuseStep 6425027 = 9637541) B9637541
theorem B55667263 : Blo 1691546 55667263 := bstep (se 1 (by rfl) ⟨41750447, by rfl⟩ : syracuseStep 55667263 = 83500895) B83500895
theorem B55675679 : Blo 1691546 55675679 := bstep (se 1 (by rfl) ⟨41756759, by rfl⟩ : syracuseStep 55675679 = 83513519) B83513519
theorem B4066175 : Blo 1691546 4066175 := bstep (se 1 (by rfl) ⟨3049631, by rfl⟩ : syracuseStep 4066175 = 6099263) B6099263
theorem B14453747 : Blo 1691546 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B20598245 : Blo 1691546 20598245 := bstep (se 4 (by rfl) ⟨1931085, by rfl⟩ : syracuseStep 20598245 = 3862171) B3862171
theorem B9768869 : Blo 1691546 9768869 := bstep (se 4 (by rfl) ⟨915831, by rfl⟩ : syracuseStep 9768869 = 1831663) B1831663
theorem B1691871 : Blo 1691546 1691871 := bstep (se 1 (by rfl) ⟨1268903, by rfl⟩ : syracuseStep 1691871 = 2537807) B2537807
theorem B1692399 : Blo 1691546 1692399 := bstep (se 1 (by rfl) ⟨1269299, by rfl⟩ : syracuseStep 1692399 = 2538599) B2538599
theorem B4068481 : Blo 1691546 4068481 := bstep (se 2 (by rfl) ⟨1525680, by rfl⟩ : syracuseStep 4068481 = 3051361) B3051361
theorem B5420719 : Blo 1691546 5420719 := bstep (se 1 (by rfl) ⟨4065539, by rfl⟩ : syracuseStep 5420719 = 8131079) B8131079
theorem B1693391 : Blo 1691546 1693391 := bstep (se 1 (by rfl) ⟨1270043, by rfl⟩ : syracuseStep 1693391 = 2540087) B2540087
theorem B87906329 : Blo 1691546 87906329 := bstep (se 2 (by rfl) ⟨32964873, by rfl⟩ : syracuseStep 87906329 = 65929747) B65929747
theorem B92641319 : Blo 1691546 92641319 := bstep (se 1 (by rfl) ⟨69480989, by rfl⟩ : syracuseStep 92641319 = 138961979) B138961979
theorem B3807467 : Blo 1691546 3807467 := bstep (se 1 (by rfl) ⟨2855600, by rfl⟩ : syracuseStep 3807467 = 5711201) B5711201
theorem B2537897 : Blo 1691546 2537897 := bstep (se 2 (by rfl) ⟨951711, by rfl⟩ : syracuseStep 2537897 = 1903423) B1903423
theorem B8133385 : Blo 1691546 8133385 := bstep (se 2 (by rfl) ⟨3050019, by rfl⟩ : syracuseStep 8133385 = 6100039) B6100039
theorem B7232615 : Blo 1691546 7232615 := bstep (se 1 (by rfl) ⟨5424461, by rfl⟩ : syracuseStep 7232615 = 10848923) B10848923
theorem B2538623 : Blo 1691546 2538623 := bstep (se 1 (by rfl) ⟨1903967, by rfl⟩ : syracuseStep 2538623 = 3807935) B3807935
theorem B6430175 : Blo 1691546 6430175 := bstep (se 1 (by rfl) ⟨4822631, by rfl⟩ : syracuseStep 6430175 = 9645263) B9645263
theorem B2539007 : Blo 1691546 2539007 := bstep (se 1 (by rfl) ⟨1904255, by rfl⟩ : syracuseStep 2539007 = 3808511) B3808511
theorem B3809087 : Blo 1691546 3809087 := bstep (se 1 (by rfl) ⟨2856815, by rfl⟩ : syracuseStep 3809087 = 5713631) B5713631
theorem B2539367 : Blo 1691546 2539367 := bstep (se 1 (by rfl) ⟨1904525, by rfl⟩ : syracuseStep 2539367 = 3809051) B3809051
theorem B181010393 : Blo 1691546 181010393 := bstep (se 2 (by rfl) ⟨67878897, by rfl⟩ : syracuseStep 181010393 = 135757795) B135757795
theorem B2539499 : Blo 1691546 2539499 := bstep (se 1 (by rfl) ⟨1904624, by rfl⟩ : syracuseStep 2539499 = 3809249) B3809249
theorem B30892265 : Blo 1691546 30892265 := bstep (se 2 (by rfl) ⟨11584599, by rfl⟩ : syracuseStep 30892265 = 23169199) B23169199
theorem B2540159 : Blo 1691546 2540159 := bstep (se 1 (by rfl) ⟨1905119, by rfl⟩ : syracuseStep 2540159 = 3810239) B3810239
theorem B13206359 : Blo 1691546 13206359 := bstep (se 1 (by rfl) ⟨9904769, by rfl⟩ : syracuseStep 13206359 = 19809539) B19809539
theorem B19268927 : Blo 1691546 19268927 := bstep (se 1 (by rfl) ⟨14451695, by rfl⟩ : syracuseStep 19268927 = 28903391) B28903391
theorem B61760879 : Blo 1691546 61760879 := bstep (se 1 (by rfl) ⟨46320659, by rfl⟩ : syracuseStep 61760879 = 92641319) B92641319
theorem B5424641 : Blo 1691546 5424641 := bstep (se 2 (by rfl) ⟨2034240, by rfl⟩ : syracuseStep 5424641 = 4068481) B4068481
theorem B9635831 : Blo 1691546 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B7227625 : Blo 1691546 7227625 := bstep (se 2 (by rfl) ⟨2710359, by rfl⟩ : syracuseStep 7227625 = 5420719) B5420719
theorem B4286783 : Blo 1691546 4286783 := bstep (se 1 (by rfl) ⟨3215087, by rfl⟩ : syracuseStep 4286783 = 6430175) B6430175
theorem B13732163 : Blo 1691546 13732163 := bstep (se 1 (by rfl) ⟨10299122, by rfl⟩ : syracuseStep 13732163 = 20598245) B20598245
theorem B9144697 : Blo 1691546 9144697 := bstep (se 2 (by rfl) ⟨3429261, by rfl⟩ : syracuseStep 9144697 = 6858523) B6858523
theorem B48826961 : Blo 1691546 48826961 := bstep (se 2 (by rfl) ⟨18310110, by rfl⟩ : syracuseStep 48826961 = 36620221) B36620221
theorem B5713199 : Blo 1691546 5713199 := bstep (se 1 (by rfl) ⟨4284899, by rfl⟩ : syracuseStep 5713199 = 8569799) B8569799
theorem B6426013 : Blo 1691546 6426013 := bstep (se 3 (by rfl) ⟨1204877, by rfl⟩ : syracuseStep 6426013 = 2409755) B2409755
theorem B74223017 : Blo 1691546 74223017 := bstep (se 2 (by rfl) ⟨27833631, by rfl⟩ : syracuseStep 74223017 = 55667263) B55667263
theorem B2141903 : Blo 1691546 2141903 := bstep (se 1 (by rfl) ⟨1606427, by rfl⟩ : syracuseStep 2141903 = 3212855) B3212855
theorem B1691931 : Blo 1691546 1691931 := bstep (se 1 (by rfl) ⟨1268948, by rfl⟩ : syracuseStep 1691931 = 2537897) B2537897
theorem B4821743 : Blo 1691546 4821743 := bstep (se 1 (by rfl) ⟨3616307, by rfl⟩ : syracuseStep 4821743 = 7232615) B7232615
theorem B148468477 : Blo 1691546 148468477 := bstep (se 3 (by rfl) ⟨27837839, by rfl⟩ : syracuseStep 148468477 = 55675679) B55675679
theorem B1692415 : Blo 1691546 1692415 := bstep (se 1 (by rfl) ⟨1269311, by rfl⟩ : syracuseStep 1692415 = 2538623) B2538623
theorem B1692671 : Blo 1691546 1692671 := bstep (se 1 (by rfl) ⟨1269503, by rfl⟩ : syracuseStep 1692671 = 2539007) B2539007
theorem B1692911 : Blo 1691546 1692911 := bstep (se 1 (by rfl) ⟨1269683, by rfl⟩ : syracuseStep 1692911 = 2539367) B2539367
theorem B120673595 : Blo 1691546 120673595 := bstep (se 1 (by rfl) ⟨90505196, by rfl⟩ : syracuseStep 120673595 = 181010393) B181010393
theorem B1692999 : Blo 1691546 1692999 := bstep (se 1 (by rfl) ⟨1269749, by rfl⟩ : syracuseStep 1692999 = 2539499) B2539499
theorem B1693055 : Blo 1691546 1693055 := bstep (se 1 (by rfl) ⟨1269791, by rfl⟩ : syracuseStep 1693055 = 2539583) B2539583
theorem B16259237 : Blo 1691546 16259237 := bstep (se 4 (by rfl) ⟨1524303, by rfl⟩ : syracuseStep 16259237 = 3048607) B3048607
theorem B10844513 : Blo 1691546 10844513 := bstep (se 2 (by rfl) ⟨4066692, by rfl⟩ : syracuseStep 10844513 = 8133385) B8133385
theorem B58604219 : Blo 1691546 58604219 := bstep (se 1 (by rfl) ⟨43953164, by rfl⟩ : syracuseStep 58604219 = 87906329) B87906329
theorem B2538311 : Blo 1691546 2538311 := bstep (se 1 (by rfl) ⟨1903733, by rfl⟩ : syracuseStep 2538311 = 3807467) B3807467
theorem B4283351 : Blo 1691546 4283351 := bstep (se 1 (by rfl) ⟨3212513, by rfl⟩ : syracuseStep 4283351 = 6425027) B6425027
theorem B2710783 : Blo 1691546 2710783 := bstep (se 1 (by rfl) ⟨2033087, by rfl⟩ : syracuseStep 2710783 = 4066175) B4066175
theorem B2539391 : Blo 1691546 2539391 := bstep (se 1 (by rfl) ⟨1904543, by rfl⟩ : syracuseStep 2539391 = 3809087) B3809087
theorem B6512579 : Blo 1691546 6512579 := bstep (se 1 (by rfl) ⟨4884434, by rfl⟩ : syracuseStep 6512579 = 9768869) B9768869
theorem B20594843 : Blo 1691546 20594843 := bstep (se 1 (by rfl) ⟨15446132, by rfl⟩ : syracuseStep 20594843 = 30892265) B30892265
theorem B12845951 : Blo 1691546 12845951 := bstep (se 1 (by rfl) ⟨9634463, by rfl⟩ : syracuseStep 12845951 = 19268927) B19268927
theorem B41173919 : Blo 1691546 41173919 := bstep (se 1 (by rfl) ⟨30880439, by rfl⟩ : syracuseStep 41173919 = 61760879) B61760879
theorem B6423887 : Blo 1691546 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B10839491 : Blo 1691546 10839491 := bstep (se 1 (by rfl) ⟨8129618, by rfl⟩ : syracuseStep 10839491 = 16259237) B16259237
theorem B3614377 : Blo 1691546 3614377 := bstep (se 2 (by rfl) ⟨1355391, by rfl⟩ : syracuseStep 3614377 = 2710783) B2710783
theorem B39069479 : Blo 1691546 39069479 := bstep (se 1 (by rfl) ⟨29302109, by rfl⟩ : syracuseStep 39069479 = 58604219) B58604219
theorem B5711741 : Blo 1691546 5711741 := bstep (se 3 (by rfl) ⟨1070951, by rfl⟩ : syracuseStep 5711741 = 2141903) B2141903
theorem B49482011 : Blo 1691546 49482011 := bstep (se 1 (by rfl) ⟨37111508, by rfl⟩ : syracuseStep 49482011 = 74223017) B74223017
theorem B9636833 : Blo 1691546 9636833 := bstep (se 2 (by rfl) ⟨3613812, by rfl⟩ : syracuseStep 9636833 = 7227625) B7227625
theorem B12192929 : Blo 1691546 12192929 := bstep (se 2 (by rfl) ⟨4572348, by rfl⟩ : syracuseStep 12192929 = 9144697) B9144697
theorem B3214495 : Blo 1691546 3214495 := bstep (se 1 (by rfl) ⟨2410871, by rfl⟩ : syracuseStep 3214495 = 4821743) B4821743
theorem B3616427 : Blo 1691546 3616427 := bstep (se 1 (by rfl) ⟨2712320, by rfl⟩ : syracuseStep 3616427 = 5424641) B5424641
theorem B9154775 : Blo 1691546 9154775 := bstep (se 1 (by rfl) ⟨6866081, by rfl⟩ : syracuseStep 9154775 = 13732163) B13732163
theorem B7229675 : Blo 1691546 7229675 := bstep (se 1 (by rfl) ⟨5422256, by rfl⟩ : syracuseStep 7229675 = 10844513) B10844513
theorem B32551307 : Blo 1691546 32551307 := bstep (se 1 (by rfl) ⟨24413480, by rfl⟩ : syracuseStep 32551307 = 48826961) B48826961
theorem B1692207 : Blo 1691546 1692207 := bstep (se 1 (by rfl) ⟨1269155, by rfl⟩ : syracuseStep 1692207 = 2538311) B2538311
theorem B2855567 : Blo 1691546 2855567 := bstep (se 1 (by rfl) ⟨2141675, by rfl⟩ : syracuseStep 2855567 = 4283351) B4283351
theorem B1692927 : Blo 1691546 1692927 := bstep (se 1 (by rfl) ⟨1269695, by rfl⟩ : syracuseStep 1692927 = 2539391) B2539391
theorem B1693439 : Blo 1691546 1693439 := bstep (se 1 (by rfl) ⟨1270079, by rfl⟩ : syracuseStep 1693439 = 2540159) B2540159
theorem B321796253 : Blo 1691546 321796253 := bstep (se 3 (by rfl) ⟨60336797, by rfl⟩ : syracuseStep 321796253 = 120673595) B120673595
theorem B197957969 : Blo 1691546 197957969 := bstep (se 2 (by rfl) ⟨74234238, by rfl⟩ : syracuseStep 197957969 = 148468477) B148468477
theorem B2857855 : Blo 1691546 2857855 := bstep (se 1 (by rfl) ⟨2143391, by rfl⟩ : syracuseStep 2857855 = 4286783) B4286783
theorem B8568017 : Blo 1691546 8568017 := bstep (se 2 (by rfl) ⟨3213006, by rfl⟩ : syracuseStep 8568017 = 6426013) B6426013
theorem B3808799 : Blo 1691546 3808799 := bstep (se 1 (by rfl) ⟨2856599, by rfl⟩ : syracuseStep 3808799 = 5713199) B5713199
theorem B35216957 : Blo 1691546 35216957 := bstep (se 3 (by rfl) ⟨6603179, by rfl⟩ : syracuseStep 35216957 = 13206359) B13206359
theorem B4341719 : Blo 1691546 4341719 := bstep (se 1 (by rfl) ⟨3256289, by rfl⟩ : syracuseStep 4341719 = 6512579) B6512579
theorem B13729895 : Blo 1691546 13729895 := bstep (se 1 (by rfl) ⟨10297421, by rfl⟩ : syracuseStep 13729895 = 20594843) B20594843
theorem B6103183 : Blo 1691546 6103183 := bstep (se 1 (by rfl) ⟨4577387, by rfl⟩ : syracuseStep 6103183 = 9154775) B9154775
theorem B21700871 : Blo 1691546 21700871 := bstep (se 1 (by rfl) ⟨16275653, by rfl⟩ : syracuseStep 21700871 = 32551307) B32551307
theorem B7226327 : Blo 1691546 7226327 := bstep (se 1 (by rfl) ⟨5419745, by rfl⟩ : syracuseStep 7226327 = 10839491) B10839491
theorem B3810473 : Blo 1691546 3810473 := bstep (se 2 (by rfl) ⟨1428927, by rfl⟩ : syracuseStep 3810473 = 2857855) B2857855
theorem B4285993 : Blo 1691546 4285993 := bstep (se 2 (by rfl) ⟨1607247, by rfl⟩ : syracuseStep 4285993 = 3214495) B3214495
theorem B9643805 : Blo 1691546 9643805 := bstep (se 3 (by rfl) ⟨1808213, by rfl⟩ : syracuseStep 9643805 = 3616427) B3616427
theorem B6424555 : Blo 1691546 6424555 := bstep (se 1 (by rfl) ⟨4818416, by rfl⟩ : syracuseStep 6424555 = 9636833) B9636833
theorem B8128619 : Blo 1691546 8128619 := bstep (se 1 (by rfl) ⟨6096464, by rfl⟩ : syracuseStep 8128619 = 12192929) B12192929
theorem B5712011 : Blo 1691546 5712011 := bstep (se 1 (by rfl) ⟨4284008, by rfl⟩ : syracuseStep 5712011 = 8568017) B8568017
theorem B4819169 : Blo 1691546 4819169 := bstep (se 2 (by rfl) ⟨1807188, by rfl⟩ : syracuseStep 4819169 = 3614377) B3614377
theorem B11577917 : Blo 1691546 11577917 := bstep (se 3 (by rfl) ⟨2170859, by rfl⟩ : syracuseStep 11577917 = 4341719) B4341719
theorem B858123341 : Blo 1691546 858123341 := bstep (se 3 (by rfl) ⟨160898126, by rfl⟩ : syracuseStep 858123341 = 321796253) B321796253
theorem B1903711 : Blo 1691546 1903711 := bstep (se 1 (by rfl) ⟨1427783, by rfl⟩ : syracuseStep 1903711 = 2855567) B2855567
theorem B8563967 : Blo 1691546 8563967 := bstep (se 1 (by rfl) ⟨6422975, by rfl⟩ : syracuseStep 8563967 = 12845951) B12845951
theorem B19279133 : Blo 1691546 19279133 := bstep (se 3 (by rfl) ⟨3614837, by rfl⟩ : syracuseStep 19279133 = 7229675) B7229675
theorem B27449279 : Blo 1691546 27449279 := bstep (se 1 (by rfl) ⟨20586959, by rfl⟩ : syracuseStep 27449279 = 41173919) B41173919
theorem B4282591 : Blo 1691546 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B3807827 : Blo 1691546 3807827 := bstep (se 1 (by rfl) ⟨2855870, by rfl⟩ : syracuseStep 3807827 = 5711741) B5711741
theorem B93911885 : Blo 1691546 93911885 := bstep (se 3 (by rfl) ⟨17608478, by rfl⟩ : syracuseStep 93911885 = 35216957) B35216957
theorem B32988007 : Blo 1691546 32988007 := bstep (se 1 (by rfl) ⟨24741005, by rfl⟩ : syracuseStep 32988007 = 49482011) B49482011
theorem B131971979 : Blo 1691546 131971979 := bstep (se 1 (by rfl) ⟨98978984, by rfl⟩ : syracuseStep 131971979 = 197957969) B197957969
theorem B104185277 : Blo 1691546 104185277 := bstep (se 3 (by rfl) ⟨19534739, by rfl⟩ : syracuseStep 104185277 = 39069479) B39069479
theorem B2539199 : Blo 1691546 2539199 := bstep (se 1 (by rfl) ⟨1904399, by rfl⟩ : syracuseStep 2539199 = 3808799) B3808799
theorem B14467247 : Blo 1691546 14467247 := bstep (se 1 (by rfl) ⟨10850435, by rfl⟩ : syracuseStep 14467247 = 21700871) B21700871
theorem B5710121 : Blo 1691546 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B4817551 : Blo 1691546 4817551 := bstep (se 1 (by rfl) ⟨3613163, by rfl⟩ : syracuseStep 4817551 = 7226327) B7226327
theorem B2540315 : Blo 1691546 2540315 := bstep (se 1 (by rfl) ⟨1905236, by rfl⟩ : syracuseStep 2540315 = 3810473) B3810473
theorem B43984009 : Blo 1691546 43984009 := bstep (se 2 (by rfl) ⟨16494003, by rfl⟩ : syracuseStep 43984009 = 32988007) B32988007
theorem B3212779 : Blo 1691546 3212779 := bstep (se 1 (by rfl) ⟨2409584, by rfl⟩ : syracuseStep 3212779 = 4819169) B4819169
theorem B7718611 : Blo 1691546 7718611 := bstep (se 1 (by rfl) ⟨5788958, by rfl⟩ : syracuseStep 7718611 = 11577917) B11577917
theorem B572082227 : Blo 1691546 572082227 := bstep (se 1 (by rfl) ⟨429061670, by rfl⟩ : syracuseStep 572082227 = 858123341) B858123341
theorem B9153263 : Blo 1691546 9153263 := bstep (se 1 (by rfl) ⟨6864947, by rfl⟩ : syracuseStep 9153263 = 13729895) B13729895
theorem B8137577 : Blo 1691546 8137577 := bstep (se 2 (by rfl) ⟨3051591, by rfl⟩ : syracuseStep 8137577 = 6103183) B6103183
theorem B5419079 : Blo 1691546 5419079 := bstep (se 1 (by rfl) ⟨4064309, by rfl⟩ : syracuseStep 5419079 = 8128619) B8128619
theorem B62607923 : Blo 1691546 62607923 := bstep (se 1 (by rfl) ⟨46955942, by rfl⟩ : syracuseStep 62607923 = 93911885) B93911885
theorem B5714657 : Blo 1691546 5714657 := bstep (se 2 (by rfl) ⟨2142996, by rfl⟩ : syracuseStep 5714657 = 4285993) B4285993
theorem B69456851 : Blo 1691546 69456851 := bstep (se 1 (by rfl) ⟨52092638, by rfl⟩ : syracuseStep 69456851 = 104185277) B104185277
theorem B1692799 : Blo 1691546 1692799 := bstep (se 1 (by rfl) ⟨1269599, by rfl⟩ : syracuseStep 1692799 = 2539199) B2539199
theorem B8566073 : Blo 1691546 8566073 := bstep (se 2 (by rfl) ⟨3212277, by rfl⟩ : syracuseStep 8566073 = 6424555) B6424555
theorem B6429203 : Blo 1691546 6429203 := bstep (se 1 (by rfl) ⟨4821902, by rfl⟩ : syracuseStep 6429203 = 9643805) B9643805
theorem B18299519 : Blo 1691546 18299519 := bstep (se 1 (by rfl) ⟨13724639, by rfl⟩ : syracuseStep 18299519 = 27449279) B27449279
theorem B3808007 : Blo 1691546 3808007 := bstep (se 1 (by rfl) ⟨2856005, by rfl⟩ : syracuseStep 3808007 = 5712011) B5712011
theorem B2538281 : Blo 1691546 2538281 := bstep (se 2 (by rfl) ⟨951855, by rfl⟩ : syracuseStep 2538281 = 1903711) B1903711
theorem B2538551 : Blo 1691546 2538551 := bstep (se 1 (by rfl) ⟨1903913, by rfl⟩ : syracuseStep 2538551 = 3807827) B3807827
theorem B87981319 : Blo 1691546 87981319 := bstep (se 1 (by rfl) ⟨65985989, by rfl⟩ : syracuseStep 87981319 = 131971979) B131971979
theorem B5709311 : Blo 1691546 5709311 := bstep (se 1 (by rfl) ⟨4281983, by rfl⟩ : syracuseStep 5709311 = 8563967) B8563967
theorem B12852755 : Blo 1691546 12852755 := bstep (se 1 (by rfl) ⟨9639566, by rfl⟩ : syracuseStep 12852755 = 19279133) B19279133
theorem B3612719 : Blo 1691546 3612719 := bstep (se 1 (by rfl) ⟨2709539, by rfl⟩ : syracuseStep 3612719 = 5419079) B5419079
theorem B41738615 : Blo 1691546 41738615 := bstep (se 1 (by rfl) ⟨31303961, by rfl⟩ : syracuseStep 41738615 = 62607923) B62607923
theorem B3809771 : Blo 1691546 3809771 := bstep (se 1 (by rfl) ⟨2857328, by rfl⟩ : syracuseStep 3809771 = 5714657) B5714657
theorem B6423401 : Blo 1691546 6423401 := bstep (se 2 (by rfl) ⟨2408775, by rfl⟩ : syracuseStep 6423401 = 4817551) B4817551
theorem B5710715 : Blo 1691546 5710715 := bstep (se 1 (by rfl) ⟨4283036, by rfl⟩ : syracuseStep 5710715 = 8566073) B8566073
theorem B381388151 : Blo 1691546 381388151 := bstep (se 1 (by rfl) ⟨286041113, by rfl⟩ : syracuseStep 381388151 = 572082227) B572082227
theorem B4286135 : Blo 1691546 4286135 := bstep (se 1 (by rfl) ⟨3214601, by rfl⟩ : syracuseStep 4286135 = 6429203) B6429203
theorem B12199679 : Blo 1691546 12199679 := bstep (se 1 (by rfl) ⟨9149759, by rfl⟩ : syracuseStep 12199679 = 18299519) B18299519
theorem B5425051 : Blo 1691546 5425051 := bstep (se 1 (by rfl) ⟨4068788, by rfl⟩ : syracuseStep 5425051 = 8137577) B8137577
theorem B10291481 : Blo 1691546 10291481 := bstep (se 2 (by rfl) ⟨3859305, by rfl⟩ : syracuseStep 10291481 = 7718611) B7718611
theorem B9644831 : Blo 1691546 9644831 := bstep (se 1 (by rfl) ⟨7233623, by rfl⟩ : syracuseStep 9644831 = 14467247) B14467247
theorem B46304567 : Blo 1691546 46304567 := bstep (se 1 (by rfl) ⟨34728425, by rfl⟩ : syracuseStep 46304567 = 69456851) B69456851
theorem B1692187 : Blo 1691546 1692187 := bstep (se 1 (by rfl) ⟨1269140, by rfl⟩ : syracuseStep 1692187 = 2538281) B2538281
theorem B1692367 : Blo 1691546 1692367 := bstep (se 1 (by rfl) ⟨1269275, by rfl⟩ : syracuseStep 1692367 = 2538551) B2538551
theorem B3806207 : Blo 1691546 3806207 := bstep (se 1 (by rfl) ⟨2854655, by rfl⟩ : syracuseStep 3806207 = 5709311) B5709311
theorem B3806747 : Blo 1691546 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B1693543 : Blo 1691546 1693543 := bstep (se 1 (by rfl) ⟨1270157, by rfl⟩ : syracuseStep 1693543 = 2540315) B2540315
theorem B58645345 : Blo 1691546 58645345 := bstep (se 2 (by rfl) ⟨21992004, by rfl⟩ : syracuseStep 58645345 = 43984009) B43984009
theorem B117308425 : Blo 1691546 117308425 := bstep (se 2 (by rfl) ⟨43990659, by rfl⟩ : syracuseStep 117308425 = 87981319) B87981319
theorem B6102175 : Blo 1691546 6102175 := bstep (se 1 (by rfl) ⟨4576631, by rfl⟩ : syracuseStep 6102175 = 9153263) B9153263
theorem B2538671 : Blo 1691546 2538671 := bstep (se 1 (by rfl) ⟨1904003, by rfl⟩ : syracuseStep 2538671 = 3808007) B3808007
theorem B4283705 : Blo 1691546 4283705 := bstep (se 2 (by rfl) ⟨1606389, by rfl⟩ : syracuseStep 4283705 = 3212779) B3212779
theorem B8568503 : Blo 1691546 8568503 := bstep (se 1 (by rfl) ⟨6426377, by rfl⟩ : syracuseStep 8568503 = 12852755) B12852755
theorem B9633917 : Blo 1691546 9633917 := bstep (se 3 (by rfl) ⟨1806359, by rfl⟩ : syracuseStep 9633917 = 3612719) B3612719
theorem B2539847 : Blo 1691546 2539847 := bstep (se 1 (by rfl) ⟨1904885, by rfl⟩ : syracuseStep 2539847 = 3809771) B3809771
theorem B78193793 : Blo 1691546 78193793 := bstep (se 2 (by rfl) ⟨29322672, by rfl⟩ : syracuseStep 78193793 = 58645345) B58645345
theorem B156411233 : Blo 1691546 156411233 := bstep (se 2 (by rfl) ⟨58654212, by rfl⟩ : syracuseStep 156411233 = 117308425) B117308425
theorem B8136233 : Blo 1691546 8136233 := bstep (se 2 (by rfl) ⟨3051087, by rfl⟩ : syracuseStep 8136233 = 6102175) B6102175
theorem B30869711 : Blo 1691546 30869711 := bstep (se 1 (by rfl) ⟨23152283, by rfl⟩ : syracuseStep 30869711 = 46304567) B46304567
theorem B5712335 : Blo 1691546 5712335 := bstep (se 1 (by rfl) ⟨4284251, by rfl⟩ : syracuseStep 5712335 = 8568503) B8568503
theorem B254258767 : Blo 1691546 254258767 := bstep (se 1 (by rfl) ⟨190694075, by rfl⟩ : syracuseStep 254258767 = 381388151) B381388151
theorem B6860987 : Blo 1691546 6860987 := bstep (se 1 (by rfl) ⟨5145740, by rfl⟩ : syracuseStep 6860987 = 10291481) B10291481
theorem B1692447 : Blo 1691546 1692447 := bstep (se 1 (by rfl) ⟨1269335, by rfl⟩ : syracuseStep 1692447 = 2538671) B2538671
theorem B2855803 : Blo 1691546 2855803 := bstep (se 1 (by rfl) ⟨2141852, by rfl⟩ : syracuseStep 2855803 = 4283705) B4283705
theorem B27825743 : Blo 1691546 27825743 := bstep (se 1 (by rfl) ⟨20869307, by rfl⟩ : syracuseStep 27825743 = 41738615) B41738615
theorem B4282267 : Blo 1691546 4282267 := bstep (se 1 (by rfl) ⟨3211700, by rfl⟩ : syracuseStep 4282267 = 6423401) B6423401
theorem B3807143 : Blo 1691546 3807143 := bstep (se 1 (by rfl) ⟨2855357, by rfl⟩ : syracuseStep 3807143 = 5710715) B5710715
theorem B2537471 : Blo 1691546 2537471 := bstep (se 1 (by rfl) ⟨1903103, by rfl⟩ : syracuseStep 2537471 = 3806207) B3806207
theorem B2537831 : Blo 1691546 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B2857423 : Blo 1691546 2857423 := bstep (se 1 (by rfl) ⟨2143067, by rfl⟩ : syracuseStep 2857423 = 4286135) B4286135
theorem B8133119 : Blo 1691546 8133119 := bstep (se 1 (by rfl) ⟨6099839, by rfl⟩ : syracuseStep 8133119 = 12199679) B12199679
theorem B6429887 : Blo 1691546 6429887 := bstep (se 1 (by rfl) ⟨4822415, by rfl⟩ : syracuseStep 6429887 = 9644831) B9644831
theorem B7233401 : Blo 1691546 7233401 := bstep (se 2 (by rfl) ⟨2712525, by rfl⟩ : syracuseStep 7233401 = 5425051) B5425051
theorem B6422611 : Blo 1691546 6422611 := bstep (se 1 (by rfl) ⟨4816958, by rfl⟩ : syracuseStep 6422611 = 9633917) B9633917
theorem B3809897 : Blo 1691546 3809897 := bstep (se 2 (by rfl) ⟨1428711, by rfl⟩ : syracuseStep 3809897 = 2857423) B2857423
theorem B5424155 : Blo 1691546 5424155 := bstep (se 1 (by rfl) ⟨4068116, by rfl⟩ : syracuseStep 5424155 = 8136233) B8136233
theorem B20579807 : Blo 1691546 20579807 := bstep (se 1 (by rfl) ⟨15434855, by rfl⟩ : syracuseStep 20579807 = 30869711) B30869711
theorem B339011689 : Blo 1691546 339011689 := bstep (se 2 (by rfl) ⟨127129383, by rfl⟩ : syracuseStep 339011689 = 254258767) B254258767
theorem B4286591 : Blo 1691546 4286591 := bstep (se 1 (by rfl) ⟨3214943, by rfl⟩ : syracuseStep 4286591 = 6429887) B6429887
theorem B4573991 : Blo 1691546 4573991 := bstep (se 1 (by rfl) ⟨3430493, by rfl⟩ : syracuseStep 4573991 = 6860987) B6860987
theorem B18550495 : Blo 1691546 18550495 := bstep (se 1 (by rfl) ⟨13912871, by rfl⟩ : syracuseStep 18550495 = 27825743) B27825743
theorem B1691647 : Blo 1691546 1691647 := bstep (se 1 (by rfl) ⟨1268735, by rfl⟩ : syracuseStep 1691647 = 2537471) B2537471
theorem B1691887 : Blo 1691546 1691887 := bstep (se 1 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 1691887 = 2537831) B2537831
theorem B4822267 : Blo 1691546 4822267 := bstep (se 1 (by rfl) ⟨3616700, by rfl⟩ : syracuseStep 4822267 = 7233401) B7233401
theorem B1693231 : Blo 1691546 1693231 := bstep (se 1 (by rfl) ⟨1269923, by rfl⟩ : syracuseStep 1693231 = 2539847) B2539847
theorem B208516781 : Blo 1691546 208516781 := bstep (se 3 (by rfl) ⟨39096896, by rfl⟩ : syracuseStep 208516781 = 78193793) B78193793
theorem B104274155 : Blo 1691546 104274155 := bstep (se 1 (by rfl) ⟨78205616, by rfl⟩ : syracuseStep 104274155 = 156411233) B156411233
theorem B3807737 : Blo 1691546 3807737 := bstep (se 2 (by rfl) ⟨1427901, by rfl⟩ : syracuseStep 3807737 = 2855803) B2855803
theorem B2538095 : Blo 1691546 2538095 := bstep (se 1 (by rfl) ⟨1903571, by rfl⟩ : syracuseStep 2538095 = 3807143) B3807143
theorem B3808223 : Blo 1691546 3808223 := bstep (se 1 (by rfl) ⟨2856167, by rfl⟩ : syracuseStep 3808223 = 5712335) B5712335
theorem B5422079 : Blo 1691546 5422079 := bstep (se 1 (by rfl) ⟨4066559, by rfl⟩ : syracuseStep 5422079 = 8133119) B8133119
theorem B5709689 : Blo 1691546 5709689 := bstep (se 2 (by rfl) ⟨2141133, by rfl⟩ : syracuseStep 5709689 = 4282267) B4282267
theorem B2539931 : Blo 1691546 2539931 := bstep (se 1 (by rfl) ⟨1904948, by rfl⟩ : syracuseStep 2539931 = 3809897) B3809897
theorem B139011187 : Blo 1691546 139011187 := bstep (se 1 (by rfl) ⟨104258390, by rfl⟩ : syracuseStep 139011187 = 208516781) B208516781
theorem B3614719 : Blo 1691546 3614719 := bstep (se 1 (by rfl) ⟨2711039, by rfl⟩ : syracuseStep 3614719 = 5422079) B5422079
theorem B24733993 : Blo 1691546 24733993 := bstep (se 2 (by rfl) ⟨9275247, by rfl⟩ : syracuseStep 24733993 = 18550495) B18550495
theorem B8563481 : Blo 1691546 8563481 := bstep (se 2 (by rfl) ⟨3211305, by rfl⟩ : syracuseStep 8563481 = 6422611) B6422611
theorem B3616103 : Blo 1691546 3616103 := bstep (se 1 (by rfl) ⟨2712077, by rfl⟩ : syracuseStep 3616103 = 5424155) B5424155
theorem B1692063 : Blo 1691546 1692063 := bstep (se 1 (by rfl) ⟨1269047, by rfl⟩ : syracuseStep 1692063 = 2538095) B2538095
theorem B3806459 : Blo 1691546 3806459 := bstep (se 1 (by rfl) ⟨2854844, by rfl⟩ : syracuseStep 3806459 = 5709689) B5709689
theorem B452015585 : Blo 1691546 452015585 := bstep (se 2 (by rfl) ⟨169505844, by rfl⟩ : syracuseStep 452015585 = 339011689) B339011689
theorem B13719871 : Blo 1691546 13719871 := bstep (se 1 (by rfl) ⟨10289903, by rfl⟩ : syracuseStep 13719871 = 20579807) B20579807
theorem B2857727 : Blo 1691546 2857727 := bstep (se 1 (by rfl) ⟨2143295, by rfl⟩ : syracuseStep 2857727 = 4286591) B4286591
theorem B69516103 : Blo 1691546 69516103 := bstep (se 1 (by rfl) ⟨52137077, by rfl⟩ : syracuseStep 69516103 = 104274155) B104274155
theorem B6429689 : Blo 1691546 6429689 := bstep (se 2 (by rfl) ⟨2411133, by rfl⟩ : syracuseStep 6429689 = 4822267) B4822267
theorem B2538491 : Blo 1691546 2538491 := bstep (se 1 (by rfl) ⟨1903868, by rfl⟩ : syracuseStep 2538491 = 3807737) B3807737
theorem B2538815 : Blo 1691546 2538815 := bstep (se 1 (by rfl) ⟨1904111, by rfl⟩ : syracuseStep 2538815 = 3808223) B3808223
theorem B12197309 : Blo 1691546 12197309 := bstep (se 3 (by rfl) ⟨2286995, by rfl⟩ : syracuseStep 12197309 = 4573991) B4573991
theorem B18293161 : Blo 1691546 18293161 := bstep (se 2 (by rfl) ⟨6859935, by rfl⟩ : syracuseStep 18293161 = 13719871) B13719871
theorem B301343723 : Blo 1691546 301343723 := bstep (se 1 (by rfl) ⟨226007792, by rfl⟩ : syracuseStep 301343723 = 452015585) B452015585
theorem B4286459 : Blo 1691546 4286459 := bstep (se 1 (by rfl) ⟨3214844, by rfl⟩ : syracuseStep 4286459 = 6429689) B6429689
theorem B2410735 : Blo 1691546 2410735 := bstep (se 1 (by rfl) ⟨1808051, by rfl⟩ : syracuseStep 2410735 = 3616103) B3616103
theorem B4819625 : Blo 1691546 4819625 := bstep (se 2 (by rfl) ⟨1807359, by rfl⟩ : syracuseStep 4819625 = 3614719) B3614719
theorem B92688137 : Blo 1691546 92688137 := bstep (se 2 (by rfl) ⟨34758051, by rfl⟩ : syracuseStep 92688137 = 69516103) B69516103
theorem B32526157 : Blo 1691546 32526157 := bstep (se 3 (by rfl) ⟨6098654, by rfl⟩ : syracuseStep 32526157 = 12197309) B12197309
theorem B185348249 : Blo 1691546 185348249 := bstep (se 2 (by rfl) ⟨69505593, by rfl⟩ : syracuseStep 185348249 = 139011187) B139011187
theorem B1905151 : Blo 1691546 1905151 := bstep (se 1 (by rfl) ⟨1428863, by rfl⟩ : syracuseStep 1905151 = 2857727) B2857727
theorem B1692327 : Blo 1691546 1692327 := bstep (se 1 (by rfl) ⟨1269245, by rfl⟩ : syracuseStep 1692327 = 2538491) B2538491
theorem B1692543 : Blo 1691546 1692543 := bstep (se 1 (by rfl) ⟨1269407, by rfl⟩ : syracuseStep 1692543 = 2538815) B2538815
theorem B1693287 : Blo 1691546 1693287 := bstep (se 1 (by rfl) ⟨1269965, by rfl⟩ : syracuseStep 1693287 = 2539931) B2539931
theorem B32978657 : Blo 1691546 32978657 := bstep (se 2 (by rfl) ⟨12366996, by rfl⟩ : syracuseStep 32978657 = 24733993) B24733993
theorem B2537639 : Blo 1691546 2537639 := bstep (se 1 (by rfl) ⟨1903229, by rfl⟩ : syracuseStep 2537639 = 3806459) B3806459
theorem B5708987 : Blo 1691546 5708987 := bstep (se 1 (by rfl) ⟨4281740, by rfl⟩ : syracuseStep 5708987 = 8563481) B8563481
theorem B2540201 : Blo 1691546 2540201 := bstep (se 2 (by rfl) ⟨952575, by rfl⟩ : syracuseStep 2540201 = 1905151) B1905151
theorem B3213083 : Blo 1691546 3213083 := bstep (se 1 (by rfl) ⟨2409812, by rfl⟩ : syracuseStep 3213083 = 4819625) B4819625
theorem B3214313 : Blo 1691546 3214313 := bstep (se 2 (by rfl) ⟨1205367, by rfl⟩ : syracuseStep 3214313 = 2410735) B2410735
theorem B24390881 : Blo 1691546 24390881 := bstep (se 2 (by rfl) ⟨9146580, by rfl⟩ : syracuseStep 24390881 = 18293161) B18293161
theorem B200895815 : Blo 1691546 200895815 := bstep (se 1 (by rfl) ⟨150671861, by rfl⟩ : syracuseStep 200895815 = 301343723) B301343723
theorem B1691759 : Blo 1691546 1691759 := bstep (se 1 (by rfl) ⟨1268819, by rfl⟩ : syracuseStep 1691759 = 2537639) B2537639
theorem B3805991 : Blo 1691546 3805991 := bstep (se 1 (by rfl) ⟨2854493, by rfl⟩ : syracuseStep 3805991 = 5708987) B5708987
theorem B123565499 : Blo 1691546 123565499 := bstep (se 1 (by rfl) ⟨92674124, by rfl⟩ : syracuseStep 123565499 = 185348249) B185348249
theorem B21985771 : Blo 1691546 21985771 := bstep (se 1 (by rfl) ⟨16489328, by rfl⟩ : syracuseStep 21985771 = 32978657) B32978657
theorem B2857639 : Blo 1691546 2857639 := bstep (se 1 (by rfl) ⟨2143229, by rfl⟩ : syracuseStep 2857639 = 4286459) B4286459
theorem B43368209 : Blo 1691546 43368209 := bstep (se 2 (by rfl) ⟨16263078, by rfl⟩ : syracuseStep 43368209 = 32526157) B32526157
theorem B61792091 : Blo 1691546 61792091 := bstep (se 1 (by rfl) ⟨46344068, by rfl⟩ : syracuseStep 61792091 = 92688137) B92688137
theorem B3810185 : Blo 1691546 3810185 := bstep (se 2 (by rfl) ⟨1428819, by rfl⟩ : syracuseStep 3810185 = 2857639) B2857639
theorem B28912139 : Blo 1691546 28912139 := bstep (se 1 (by rfl) ⟨21684104, by rfl⟩ : syracuseStep 28912139 = 43368209) B43368209
theorem B29314361 : Blo 1691546 29314361 := bstep (se 2 (by rfl) ⟨10992885, by rfl⟩ : syracuseStep 29314361 = 21985771) B21985771
theorem B2142055 : Blo 1691546 2142055 := bstep (se 1 (by rfl) ⟨1606541, by rfl⟩ : syracuseStep 2142055 = 3213083) B3213083
theorem B2142875 : Blo 1691546 2142875 := bstep (se 1 (by rfl) ⟨1607156, by rfl⟩ : syracuseStep 2142875 = 3214313) B3214313
theorem B41194727 : Blo 1691546 41194727 := bstep (se 1 (by rfl) ⟨30896045, by rfl⟩ : syracuseStep 41194727 = 61792091) B61792091
theorem B1693467 : Blo 1691546 1693467 := bstep (se 1 (by rfl) ⟨1270100, by rfl⟩ : syracuseStep 1693467 = 2540201) B2540201
theorem B2537327 : Blo 1691546 2537327 := bstep (se 1 (by rfl) ⟨1902995, by rfl⟩ : syracuseStep 2537327 = 3805991) B3805991
theorem B82376999 : Blo 1691546 82376999 := bstep (se 1 (by rfl) ⟨61782749, by rfl⟩ : syracuseStep 82376999 = 123565499) B123565499
theorem B16260587 : Blo 1691546 16260587 := bstep (se 1 (by rfl) ⟨12195440, by rfl⟩ : syracuseStep 16260587 = 24390881) B24390881
theorem B133930543 : Blo 1691546 133930543 := bstep (se 1 (by rfl) ⟨100447907, by rfl⟩ : syracuseStep 133930543 = 200895815) B200895815
theorem B2540123 : Blo 1691546 2540123 := bstep (se 1 (by rfl) ⟨1905092, by rfl⟩ : syracuseStep 2540123 = 3810185) B3810185
theorem B10840391 : Blo 1691546 10840391 := bstep (se 1 (by rfl) ⟨8130293, by rfl⟩ : syracuseStep 10840391 = 16260587) B16260587
theorem B27463151 : Blo 1691546 27463151 := bstep (se 1 (by rfl) ⟨20597363, by rfl⟩ : syracuseStep 27463151 = 41194727) B41194727
theorem B1691551 : Blo 1691546 1691551 := bstep (se 1 (by rfl) ⟨1268663, by rfl⟩ : syracuseStep 1691551 = 2537327) B2537327
theorem B5714333 : Blo 1691546 5714333 := bstep (se 3 (by rfl) ⟨1071437, by rfl⟩ : syracuseStep 5714333 = 2142875) B2142875
theorem B178574057 : Blo 1691546 178574057 := bstep (se 2 (by rfl) ⟨66965271, by rfl⟩ : syracuseStep 178574057 = 133930543) B133930543
theorem B19542907 : Blo 1691546 19542907 := bstep (se 1 (by rfl) ⟨14657180, by rfl⟩ : syracuseStep 19542907 = 29314361) B29314361
theorem B2856073 : Blo 1691546 2856073 := bstep (se 2 (by rfl) ⟨1071027, by rfl⟩ : syracuseStep 2856073 = 2142055) B2142055
theorem B54917999 : Blo 1691546 54917999 := bstep (se 1 (by rfl) ⟨41188499, by rfl⟩ : syracuseStep 54917999 = 82376999) B82376999
theorem B19274759 : Blo 1691546 19274759 := bstep (se 1 (by rfl) ⟨14456069, by rfl⟩ : syracuseStep 19274759 = 28912139) B28912139
theorem B3809555 : Blo 1691546 3809555 := bstep (se 1 (by rfl) ⟨2857166, by rfl⟩ : syracuseStep 3809555 = 5714333) B5714333
theorem B7226927 : Blo 1691546 7226927 := bstep (se 1 (by rfl) ⟨5420195, by rfl⟩ : syracuseStep 7226927 = 10840391) B10840391
theorem B36611999 : Blo 1691546 36611999 := bstep (se 1 (by rfl) ⟨27458999, by rfl⟩ : syracuseStep 36611999 = 54917999) B54917999
theorem B119049371 : Blo 1691546 119049371 := bstep (se 1 (by rfl) ⟨89287028, by rfl⟩ : syracuseStep 119049371 = 178574057) B178574057
theorem B12849839 : Blo 1691546 12849839 := bstep (se 1 (by rfl) ⟨9637379, by rfl⟩ : syracuseStep 12849839 = 19274759) B19274759
theorem B1693415 : Blo 1691546 1693415 := bstep (se 1 (by rfl) ⟨1270061, by rfl⟩ : syracuseStep 1693415 = 2540123) B2540123
theorem B26057209 : Blo 1691546 26057209 := bstep (se 2 (by rfl) ⟨9771453, by rfl⟩ : syracuseStep 26057209 = 19542907) B19542907
theorem B3808097 : Blo 1691546 3808097 := bstep (se 2 (by rfl) ⟨1428036, by rfl⟩ : syracuseStep 3808097 = 2856073) B2856073
theorem B18308767 : Blo 1691546 18308767 := bstep (se 1 (by rfl) ⟨13731575, by rfl⟩ : syracuseStep 18308767 = 27463151) B27463151
theorem B2539703 : Blo 1691546 2539703 := bstep (se 1 (by rfl) ⟨1904777, by rfl⟩ : syracuseStep 2539703 = 3809555) B3809555
theorem B34742945 : Blo 1691546 34742945 := bstep (se 2 (by rfl) ⟨13028604, by rfl⟩ : syracuseStep 34742945 = 26057209) B26057209
theorem B4817951 : Blo 1691546 4817951 := bstep (se 1 (by rfl) ⟨3613463, by rfl⟩ : syracuseStep 4817951 = 7226927) B7226927
theorem B79366247 : Blo 1691546 79366247 := bstep (se 1 (by rfl) ⟨59524685, by rfl⟩ : syracuseStep 79366247 = 119049371) B119049371
theorem B24407999 : Blo 1691546 24407999 := bstep (se 1 (by rfl) ⟨18305999, by rfl⟩ : syracuseStep 24407999 = 36611999) B36611999
theorem B8566559 : Blo 1691546 8566559 := bstep (se 1 (by rfl) ⟨6424919, by rfl⟩ : syracuseStep 8566559 = 12849839) B12849839
theorem B2538731 : Blo 1691546 2538731 := bstep (se 1 (by rfl) ⟨1904048, by rfl⟩ : syracuseStep 2538731 = 3808097) B3808097
theorem B24411689 : Blo 1691546 24411689 := bstep (se 2 (by rfl) ⟨9154383, by rfl⟩ : syracuseStep 24411689 = 18308767) B18308767
theorem B3211967 : Blo 1691546 3211967 := bstep (se 1 (by rfl) ⟨2408975, by rfl⟩ : syracuseStep 3211967 = 4817951) B4817951
theorem B5711039 : Blo 1691546 5711039 := bstep (se 1 (by rfl) ⟨4283279, by rfl⟩ : syracuseStep 5711039 = 8566559) B8566559
theorem B16271999 : Blo 1691546 16271999 := bstep (se 1 (by rfl) ⟨12203999, by rfl⟩ : syracuseStep 16271999 = 24407999) B24407999
theorem B23161963 : Blo 1691546 23161963 := bstep (se 1 (by rfl) ⟨17371472, by rfl⟩ : syracuseStep 23161963 = 34742945) B34742945
theorem B846573301 : Blo 1691546 846573301 := bstep (se 5 (by rfl) ⟨39683123, by rfl⟩ : syracuseStep 846573301 = 79366247) B79366247
theorem B1692487 : Blo 1691546 1692487 := bstep (se 1 (by rfl) ⟨1269365, by rfl⟩ : syracuseStep 1692487 = 2538731) B2538731
theorem B16274459 : Blo 1691546 16274459 := bstep (se 1 (by rfl) ⟨12205844, by rfl⟩ : syracuseStep 16274459 = 24411689) B24411689
theorem B1693135 : Blo 1691546 1693135 := bstep (se 1 (by rfl) ⟨1269851, by rfl⟩ : syracuseStep 1693135 = 2539703) B2539703
theorem B10847999 : Blo 1691546 10847999 := bstep (se 1 (by rfl) ⟨8135999, by rfl⟩ : syracuseStep 10847999 = 16271999) B16271999
theorem B2141311 : Blo 1691546 2141311 := bstep (se 1 (by rfl) ⟨1605983, by rfl⟩ : syracuseStep 2141311 = 3211967) B3211967
theorem B10849639 : Blo 1691546 10849639 := bstep (se 1 (by rfl) ⟨8137229, by rfl⟩ : syracuseStep 10849639 = 16274459) B16274459
theorem B4515057605 : Blo 1691546 4515057605 := bstep (se 4 (by rfl) ⟨423286650, by rfl⟩ : syracuseStep 4515057605 = 846573301) B846573301
theorem B3807359 : Blo 1691546 3807359 := bstep (se 1 (by rfl) ⟨2855519, by rfl⟩ : syracuseStep 3807359 = 5711039) B5711039
theorem B30882617 : Blo 1691546 30882617 := bstep (se 2 (by rfl) ⟨11580981, by rfl⟩ : syracuseStep 30882617 = 23161963) B23161963
theorem B20588411 : Blo 1691546 20588411 := bstep (se 1 (by rfl) ⟨15441308, by rfl⟩ : syracuseStep 20588411 = 30882617) B30882617
theorem B3010038403 : Blo 1691546 3010038403 := bstep (se 1 (by rfl) ⟨2257528802, by rfl⟩ : syracuseStep 3010038403 = 4515057605) B4515057605
theorem B2855081 : Blo 1691546 2855081 := bstep (se 2 (by rfl) ⟨1070655, by rfl⟩ : syracuseStep 2855081 = 2141311) B2141311
theorem B7231999 : Blo 1691546 7231999 := bstep (se 1 (by rfl) ⟨5423999, by rfl⟩ : syracuseStep 7231999 = 10847999) B10847999
theorem B2538239 : Blo 1691546 2538239 := bstep (se 1 (by rfl) ⟨1903679, by rfl⟩ : syracuseStep 2538239 = 3807359) B3807359
theorem B14466185 : Blo 1691546 14466185 := bstep (se 2 (by rfl) ⟨5424819, by rfl⟩ : syracuseStep 14466185 = 10849639) B10849639
theorem B9642665 : Blo 1691546 9642665 := bstep (se 2 (by rfl) ⟨3615999, by rfl⟩ : syracuseStep 9642665 = 7231999) B7231999
theorem B4013384537 : Blo 1691546 4013384537 := bstep (se 2 (by rfl) ⟨1505019201, by rfl⟩ : syracuseStep 4013384537 = 3010038403) B3010038403
theorem B9644123 : Blo 1691546 9644123 := bstep (se 1 (by rfl) ⟨7233092, by rfl⟩ : syracuseStep 9644123 = 14466185) B14466185
theorem B1903387 : Blo 1691546 1903387 := bstep (se 1 (by rfl) ⟨1427540, by rfl⟩ : syracuseStep 1903387 = 2855081) B2855081
theorem B13725607 : Blo 1691546 13725607 := bstep (se 1 (by rfl) ⟨10294205, by rfl⟩ : syracuseStep 13725607 = 20588411) B20588411
theorem B1692159 : Blo 1691546 1692159 := bstep (se 1 (by rfl) ⟨1269119, by rfl⟩ : syracuseStep 1692159 = 2538239) B2538239
theorem B10702358765 : Blo 1691546 10702358765 := bstep (se 3 (by rfl) ⟨2006692268, by rfl⟩ : syracuseStep 10702358765 = 4013384537) B4013384537
theorem B6428443 : Blo 1691546 6428443 := bstep (se 1 (by rfl) ⟨4821332, by rfl⟩ : syracuseStep 6428443 = 9642665) B9642665
theorem B2537849 : Blo 1691546 2537849 := bstep (se 2 (by rfl) ⟨951693, by rfl⟩ : syracuseStep 2537849 = 1903387) B1903387
theorem B6429415 : Blo 1691546 6429415 := bstep (se 1 (by rfl) ⟨4822061, by rfl⟩ : syracuseStep 6429415 = 9644123) B9644123
theorem B18300809 : Blo 1691546 18300809 := bstep (se 2 (by rfl) ⟨6862803, by rfl⟩ : syracuseStep 18300809 = 13725607) B13725607
theorem B7134905843 : Blo 1691546 7134905843 := bstep (se 1 (by rfl) ⟨5351179382, by rfl⟩ : syracuseStep 7134905843 = 10702358765) B10702358765
theorem B8571257 : Blo 1691546 8571257 := bstep (se 2 (by rfl) ⟨3214221, by rfl⟩ : syracuseStep 8571257 = 6428443) B6428443
theorem B12200539 : Blo 1691546 12200539 := bstep (se 1 (by rfl) ⟨9150404, by rfl⟩ : syracuseStep 12200539 = 18300809) B18300809
theorem B8572553 : Blo 1691546 8572553 := bstep (se 2 (by rfl) ⟨3214707, by rfl⟩ : syracuseStep 8572553 = 6429415) B6429415
theorem B1691899 : Blo 1691546 1691899 := bstep (se 1 (by rfl) ⟨1268924, by rfl⟩ : syracuseStep 1691899 = 2537849) B2537849
theorem B4756603895 : Blo 1691546 4756603895 := bstep (se 1 (by rfl) ⟨3567452921, by rfl⟩ : syracuseStep 4756603895 = 7134905843) B7134905843
theorem B5714171 : Blo 1691546 5714171 := bstep (se 1 (by rfl) ⟨4285628, by rfl⟩ : syracuseStep 5714171 = 8571257) B8571257
theorem B5715035 : Blo 1691546 5715035 := bstep (se 1 (by rfl) ⟨4286276, by rfl⟩ : syracuseStep 5715035 = 8572553) B8572553
theorem B16267385 : Blo 1691546 16267385 := bstep (se 2 (by rfl) ⟨6100269, by rfl⟩ : syracuseStep 16267385 = 12200539) B12200539
theorem B3809447 : Blo 1691546 3809447 := bstep (se 1 (by rfl) ⟨2857085, by rfl⟩ : syracuseStep 3809447 = 5714171) B5714171
theorem B3810023 : Blo 1691546 3810023 := bstep (se 1 (by rfl) ⟨2857517, by rfl⟩ : syracuseStep 3810023 = 5715035) B5715035
theorem B3171069263 : Blo 1691546 3171069263 := bstep (se 1 (by rfl) ⟨2378301947, by rfl⟩ : syracuseStep 3171069263 = 4756603895) B4756603895
theorem B10844923 : Blo 1691546 10844923 := bstep (se 1 (by rfl) ⟨8133692, by rfl⟩ : syracuseStep 10844923 = 16267385) B16267385
theorem B2539631 : Blo 1691546 2539631 := bstep (se 1 (by rfl) ⟨1904723, by rfl⟩ : syracuseStep 2539631 = 3809447) B3809447
theorem B2540015 : Blo 1691546 2540015 := bstep (se 1 (by rfl) ⟨1905011, by rfl⟩ : syracuseStep 2540015 = 3810023) B3810023
theorem B14459897 : Blo 1691546 14459897 := bstep (se 2 (by rfl) ⟨5422461, by rfl⟩ : syracuseStep 14459897 = 10844923) B10844923
theorem B2114046175 : Blo 1691546 2114046175 := bstep (se 1 (by rfl) ⟨1585534631, by rfl⟩ : syracuseStep 2114046175 = 3171069263) B3171069263
theorem B2818728233 : Blo 1691546 2818728233 := bstep (se 2 (by rfl) ⟨1057023087, by rfl⟩ : syracuseStep 2818728233 = 2114046175) B2114046175
theorem B1693087 : Blo 1691546 1693087 := bstep (se 1 (by rfl) ⟨1269815, by rfl⟩ : syracuseStep 1693087 = 2539631) B2539631
theorem B1693343 : Blo 1691546 1693343 := bstep (se 1 (by rfl) ⟨1270007, by rfl⟩ : syracuseStep 1693343 = 2540015) B2540015
theorem B9639931 : Blo 1691546 9639931 := bstep (se 1 (by rfl) ⟨7229948, by rfl⟩ : syracuseStep 9639931 = 14459897) B14459897
theorem B1879152155 : Blo 1691546 1879152155 := bstep (se 1 (by rfl) ⟨1409364116, by rfl⟩ : syracuseStep 1879152155 = 2818728233) B2818728233
theorem B12853241 : Blo 1691546 12853241 := bstep (se 2 (by rfl) ⟨4819965, by rfl⟩ : syracuseStep 12853241 = 9639931) B9639931
theorem B1252768103 : Blo 1691546 1252768103 := bstep (se 1 (by rfl) ⟨939576077, by rfl⟩ : syracuseStep 1252768103 = 1879152155) B1879152155
theorem B8568827 : Blo 1691546 8568827 := bstep (se 1 (by rfl) ⟨6426620, by rfl⟩ : syracuseStep 8568827 = 12853241) B12853241
theorem B5712551 : Blo 1691546 5712551 := bstep (se 1 (by rfl) ⟨4284413, by rfl⟩ : syracuseStep 5712551 = 8568827) B8568827
theorem B835178735 : Blo 1691546 835178735 := bstep (se 1 (by rfl) ⟨626384051, by rfl⟩ : syracuseStep 835178735 = 1252768103) B1252768103
theorem B556785823 : Blo 1691546 556785823 := bstep (se 1 (by rfl) ⟨417589367, by rfl⟩ : syracuseStep 556785823 = 835178735) B835178735
theorem B3808367 : Blo 1691546 3808367 := bstep (se 1 (by rfl) ⟨2856275, by rfl⟩ : syracuseStep 3808367 = 5712551) B5712551
theorem B742381097 : Blo 1691546 742381097 := bstep (se 2 (by rfl) ⟨278392911, by rfl⟩ : syracuseStep 742381097 = 556785823) B556785823
theorem B2538911 : Blo 1691546 2538911 := bstep (se 1 (by rfl) ⟨1904183, by rfl⟩ : syracuseStep 2538911 = 3808367) B3808367
theorem B1979682925 : Blo 1691546 1979682925 := bstep (se 3 (by rfl) ⟨371190548, by rfl⟩ : syracuseStep 1979682925 = 742381097) B742381097
theorem B1692607 : Blo 1691546 1692607 := bstep (se 1 (by rfl) ⟨1269455, by rfl⟩ : syracuseStep 1692607 = 2538911) B2538911
theorem B2639577233 : Blo 1691546 2639577233 := bstep (se 2 (by rfl) ⟨989841462, by rfl⟩ : syracuseStep 2639577233 = 1979682925) B1979682925
theorem B7038872621 : Blo 1691546 7038872621 := bstep (se 3 (by rfl) ⟨1319788616, by rfl⟩ : syracuseStep 7038872621 = 2639577233) B2639577233
theorem B4692581747 : Blo 1691546 4692581747 := bstep (se 1 (by rfl) ⟨3519436310, by rfl⟩ : syracuseStep 4692581747 = 7038872621) B7038872621
theorem B3128387831 : Blo 1691546 3128387831 := bstep (se 1 (by rfl) ⟨2346290873, by rfl⟩ : syracuseStep 3128387831 = 4692581747) B4692581747
theorem B2085591887 : Blo 1691546 2085591887 := bstep (se 1 (by rfl) ⟨1564193915, by rfl⟩ : syracuseStep 2085591887 = 3128387831) B3128387831
theorem B1390394591 : Blo 1691546 1390394591 := bstep (se 1 (by rfl) ⟨1042795943, by rfl⟩ : syracuseStep 1390394591 = 2085591887) B2085591887
theorem B926929727 : Blo 1691546 926929727 := bstep (se 1 (by rfl) ⟨695197295, by rfl⟩ : syracuseStep 926929727 = 1390394591) B1390394591
theorem B617953151 : Blo 1691546 617953151 := bstep (se 1 (by rfl) ⟨463464863, by rfl⟩ : syracuseStep 617953151 = 926929727) B926929727
theorem B411968767 : Blo 1691546 411968767 := bstep (se 1 (by rfl) ⟨308976575, by rfl⟩ : syracuseStep 411968767 = 617953151) B617953151
theorem B549291689 : Blo 1691546 549291689 := bstep (se 2 (by rfl) ⟨205984383, by rfl⟩ : syracuseStep 549291689 = 411968767) B411968767
theorem B366194459 : Blo 1691546 366194459 := bstep (se 1 (by rfl) ⟨274645844, by rfl⟩ : syracuseStep 366194459 = 549291689) B549291689
theorem B244129639 : Blo 1691546 244129639 := bstep (se 1 (by rfl) ⟨183097229, by rfl⟩ : syracuseStep 244129639 = 366194459) B366194459
theorem B325506185 : Blo 1691546 325506185 := bstep (se 2 (by rfl) ⟨122064819, by rfl⟩ : syracuseStep 325506185 = 244129639) B244129639
theorem B217004123 : Blo 1691546 217004123 := bstep (se 1 (by rfl) ⟨162753092, by rfl⟩ : syracuseStep 217004123 = 325506185) B325506185
theorem B144669415 : Blo 1691546 144669415 := bstep (se 1 (by rfl) ⟨108502061, by rfl⟩ : syracuseStep 144669415 = 217004123) B217004123
theorem B192892553 : Blo 1691546 192892553 := bstep (se 2 (by rfl) ⟨72334707, by rfl⟩ : syracuseStep 192892553 = 144669415) B144669415
theorem B128595035 : Blo 1691546 128595035 := bstep (se 1 (by rfl) ⟨96446276, by rfl⟩ : syracuseStep 128595035 = 192892553) B192892553
theorem B85730023 : Blo 1691546 85730023 := bstep (se 1 (by rfl) ⟨64297517, by rfl⟩ : syracuseStep 85730023 = 128595035) B128595035
theorem B114306697 : Blo 1691546 114306697 := bstep (se 2 (by rfl) ⟨42865011, by rfl⟩ : syracuseStep 114306697 = 85730023) B85730023
theorem B609635717 : Blo 1691546 609635717 := bstep (se 4 (by rfl) ⟨57153348, by rfl⟩ : syracuseStep 609635717 = 114306697) B114306697
theorem B406423811 : Blo 1691546 406423811 := bstep (se 1 (by rfl) ⟨304817858, by rfl⟩ : syracuseStep 406423811 = 609635717) B609635717
theorem B270949207 : Blo 1691546 270949207 := bstep (se 1 (by rfl) ⟨203211905, by rfl⟩ : syracuseStep 270949207 = 406423811) B406423811
theorem B361265609 : Blo 1691546 361265609 := bstep (se 2 (by rfl) ⟨135474603, by rfl⟩ : syracuseStep 361265609 = 270949207) B270949207
theorem B963374957 : Blo 1691546 963374957 := bstep (se 3 (by rfl) ⟨180632804, by rfl⟩ : syracuseStep 963374957 = 361265609) B361265609
theorem B642249971 : Blo 1691546 642249971 := bstep (se 1 (by rfl) ⟨481687478, by rfl⟩ : syracuseStep 642249971 = 963374957) B963374957
theorem B428166647 : Blo 1691546 428166647 := bstep (se 1 (by rfl) ⟨321124985, by rfl⟩ : syracuseStep 428166647 = 642249971) B642249971
theorem B285444431 : Blo 1691546 285444431 := bstep (se 1 (by rfl) ⟨214083323, by rfl⟩ : syracuseStep 285444431 = 428166647) B428166647
theorem B190296287 : Blo 1691546 190296287 := bstep (se 1 (by rfl) ⟨142722215, by rfl⟩ : syracuseStep 190296287 = 285444431) B285444431
theorem B126864191 : Blo 1691546 126864191 := bstep (se 1 (by rfl) ⟨95148143, by rfl⟩ : syracuseStep 126864191 = 190296287) B190296287
theorem B338304509 : Blo 1691546 338304509 := bstep (se 3 (by rfl) ⟨63432095, by rfl⟩ : syracuseStep 338304509 = 126864191) B126864191
theorem B225536339 : Blo 1691546 225536339 := bstep (se 1 (by rfl) ⟨169152254, by rfl⟩ : syracuseStep 225536339 = 338304509) B338304509
theorem B150357559 : Blo 1691546 150357559 := bstep (se 1 (by rfl) ⟨112768169, by rfl⟩ : syracuseStep 150357559 = 225536339) B225536339
theorem B200476745 : Blo 1691546 200476745 := bstep (se 2 (by rfl) ⟨75178779, by rfl⟩ : syracuseStep 200476745 = 150357559) B150357559
theorem B133651163 : Blo 1691546 133651163 := bstep (se 1 (by rfl) ⟨100238372, by rfl⟩ : syracuseStep 133651163 = 200476745) B200476745
theorem B89100775 : Blo 1691546 89100775 := bstep (se 1 (by rfl) ⟨66825581, by rfl⟩ : syracuseStep 89100775 = 133651163) B133651163
theorem B475204133 : Blo 1691546 475204133 := bstep (se 4 (by rfl) ⟨44550387, by rfl⟩ : syracuseStep 475204133 = 89100775) B89100775
theorem B316802755 : Blo 1691546 316802755 := bstep (se 1 (by rfl) ⟨237602066, by rfl⟩ : syracuseStep 316802755 = 475204133) B475204133
theorem B422403673 : Blo 1691546 422403673 := bstep (se 2 (by rfl) ⟨158401377, by rfl⟩ : syracuseStep 422403673 = 316802755) B316802755
theorem B563204897 : Blo 1691546 563204897 := bstep (se 2 (by rfl) ⟨211201836, by rfl⟩ : syracuseStep 563204897 = 422403673) B422403673
theorem B375469931 : Blo 1691546 375469931 := bstep (se 1 (by rfl) ⟨281602448, by rfl⟩ : syracuseStep 375469931 = 563204897) B563204897
theorem B250313287 : Blo 1691546 250313287 := bstep (se 1 (by rfl) ⟨187734965, by rfl⟩ : syracuseStep 250313287 = 375469931) B375469931
theorem B333751049 : Blo 1691546 333751049 := bstep (se 2 (by rfl) ⟨125156643, by rfl⟩ : syracuseStep 333751049 = 250313287) B250313287
theorem B222500699 : Blo 1691546 222500699 := bstep (se 1 (by rfl) ⟨166875524, by rfl⟩ : syracuseStep 222500699 = 333751049) B333751049
theorem B148333799 : Blo 1691546 148333799 := bstep (se 1 (by rfl) ⟨111250349, by rfl⟩ : syracuseStep 148333799 = 222500699) B222500699
theorem B395556797 : Blo 1691546 395556797 := bstep (se 3 (by rfl) ⟨74166899, by rfl⟩ : syracuseStep 395556797 = 148333799) B148333799
theorem B263704531 : Blo 1691546 263704531 := bstep (se 1 (by rfl) ⟨197778398, by rfl⟩ : syracuseStep 263704531 = 395556797) B395556797
theorem B351606041 : Blo 1691546 351606041 := bstep (se 2 (by rfl) ⟨131852265, by rfl⟩ : syracuseStep 351606041 = 263704531) B263704531
theorem B234404027 : Blo 1691546 234404027 := bstep (se 1 (by rfl) ⟨175803020, by rfl⟩ : syracuseStep 234404027 = 351606041) B351606041
theorem B156269351 : Blo 1691546 156269351 := bstep (se 1 (by rfl) ⟨117202013, by rfl⟩ : syracuseStep 156269351 = 234404027) B234404027
theorem B104179567 : Blo 1691546 104179567 := bstep (se 1 (by rfl) ⟨78134675, by rfl⟩ : syracuseStep 104179567 = 156269351) B156269351
theorem B138906089 : Blo 1691546 138906089 := bstep (se 2 (by rfl) ⟨52089783, by rfl⟩ : syracuseStep 138906089 = 104179567) B104179567
theorem B92604059 : Blo 1691546 92604059 := bstep (se 1 (by rfl) ⟨69453044, by rfl⟩ : syracuseStep 92604059 = 138906089) B138906089
theorem B61736039 : Blo 1691546 61736039 := bstep (se 1 (by rfl) ⟨46302029, by rfl⟩ : syracuseStep 61736039 = 92604059) B92604059
theorem B41157359 : Blo 1691546 41157359 := bstep (se 1 (by rfl) ⟨30868019, by rfl⟩ : syracuseStep 41157359 = 61736039) B61736039
theorem B27438239 : Blo 1691546 27438239 := bstep (se 1 (by rfl) ⟨20578679, by rfl⟩ : syracuseStep 27438239 = 41157359) B41157359
theorem B18292159 : Blo 1691546 18292159 := bstep (se 1 (by rfl) ⟨13719119, by rfl⟩ : syracuseStep 18292159 = 27438239) B27438239
theorem B24389545 : Blo 1691546 24389545 := bstep (se 2 (by rfl) ⟨9146079, by rfl⟩ : syracuseStep 24389545 = 18292159) B18292159
theorem B32519393 : Blo 1691546 32519393 := bstep (se 2 (by rfl) ⟨12194772, by rfl⟩ : syracuseStep 32519393 = 24389545) B24389545
theorem B21679595 : Blo 1691546 21679595 := bstep (se 1 (by rfl) ⟨16259696, by rfl⟩ : syracuseStep 21679595 = 32519393) B32519393
theorem B14453063 : Blo 1691546 14453063 := bstep (se 1 (by rfl) ⟨10839797, by rfl⟩ : syracuseStep 14453063 = 21679595) B21679595
theorem B9635375 : Blo 1691546 9635375 := bstep (se 1 (by rfl) ⟨7226531, by rfl⟩ : syracuseStep 9635375 = 14453063) B14453063
theorem B6423583 : Blo 1691546 6423583 := bstep (se 1 (by rfl) ⟨4817687, by rfl⟩ : syracuseStep 6423583 = 9635375) B9635375
theorem B8564777 : Blo 1691546 8564777 := bstep (se 2 (by rfl) ⟨3211791, by rfl⟩ : syracuseStep 8564777 = 6423583) B6423583
theorem B5709851 : Blo 1691546 5709851 := bstep (se 1 (by rfl) ⟨4282388, by rfl⟩ : syracuseStep 5709851 = 8564777) B8564777
theorem B3806567 : Blo 1691546 3806567 := bstep (se 1 (by rfl) ⟨2854925, by rfl⟩ : syracuseStep 3806567 = 5709851) B5709851
theorem B2537711 : Blo 1691546 2537711 := bstep (se 1 (by rfl) ⟨1903283, by rfl⟩ : syracuseStep 2537711 = 3806567) B3806567
theorem B1691807 : Blo 1691546 1691807 := bstep (se 1 (by rfl) ⟨1268855, by rfl⟩ : syracuseStep 1691807 = 2537711) B2537711

theorem C0 (j : ℕ) (h1 : 422886 ≤ j) (h2 : j ≤ 423385) : Blo 1691546 (4 * j + 3) := by
  interval_cases j
  · exact B1691547
  · exact B1691551
  · exact B1691555
  · exact B1691559
  · exact B1691563
  · exact B1691567
  · exact B1691571
  · exact B1691575
  · exact B1691579
  · exact B1691583
  · exact B1691587
  · exact B1691591
  · exact B1691595
  · exact B1691599
  · exact B1691603
  · exact B1691607
  · exact B1691611
  · exact B1691615
  · exact B1691619
  · exact B1691623
  · exact B1691627
  · exact B1691631
  · exact B1691635
  · exact B1691639
  · exact B1691643
  · exact B1691647
  · exact B1691651
  · exact B1691655
  · exact B1691659
  · exact B1691663
  · exact B1691667
  · exact B1691671
  · exact B1691675
  · exact B1691679
  · exact B1691683
  · exact B1691687
  · exact B1691691
  · exact B1691695
  · exact B1691699
  · exact B1691703
  · exact B1691707
  · exact B1691711
  · exact B1691715
  · exact B1691719
  · exact B1691723
  · exact B1691727
  · exact B1691731
  · exact B1691735
  · exact B1691739
  · exact B1691743
  · exact B1691747
  · exact B1691751
  · exact B1691755
  · exact B1691759
  · exact B1691763
  · exact B1691767
  · exact B1691771
  · exact B1691775
  · exact B1691779
  · exact B1691783
  · exact B1691787
  · exact B1691791
  · exact B1691795
  · exact B1691799
  · exact B1691803
  · exact B1691807
  · exact B1691811
  · exact B1691815
  · exact B1691819
  · exact B1691823
  · exact B1691827
  · exact B1691831
  · exact B1691835
  · exact B1691839
  · exact B1691843
  · exact B1691847
  · exact B1691851
  · exact B1691855
  · exact B1691859
  · exact B1691863
  · exact B1691867
  · exact B1691871
  · exact B1691875
  · exact B1691879
  · exact B1691883
  · exact B1691887
  · exact B1691891
  · exact B1691895
  · exact B1691899
  · exact B1691903
  · exact B1691907
  · exact B1691911
  · exact B1691915
  · exact B1691919
  · exact B1691923
  · exact B1691927
  · exact B1691931
  · exact B1691935
  · exact B1691939
  · exact B1691943
  · exact B1691947
  · exact B1691951
  · exact B1691955
  · exact B1691959
  · exact B1691963
  · exact B1691967
  · exact B1691971
  · exact B1691975
  · exact B1691979
  · exact B1691983
  · exact B1691987
  · exact B1691991
  · exact B1691995
  · exact B1691999
  · exact B1692003
  · exact B1692007
  · exact B1692011
  · exact B1692015
  · exact B1692019
  · exact B1692023
  · exact B1692027
  · exact B1692031
  · exact B1692035
  · exact B1692039
  · exact B1692043
  · exact B1692047
  · exact B1692051
  · exact B1692055
  · exact B1692059
  · exact B1692063
  · exact B1692067
  · exact B1692071
  · exact B1692075
  · exact B1692079
  · exact B1692083
  · exact B1692087
  · exact B1692091
  · exact B1692095
  · exact B1692099
  · exact B1692103
  · exact B1692107
  · exact B1692111
  · exact B1692115
  · exact B1692119
  · exact B1692123
  · exact B1692127
  · exact B1692131
  · exact B1692135
  · exact B1692139
  · exact B1692143
  · exact B1692147
  · exact B1692151
  · exact B1692155
  · exact B1692159
  · exact B1692163
  · exact B1692167
  · exact B1692171
  · exact B1692175
  · exact B1692179
  · exact B1692183
  · exact B1692187
  · exact B1692191
  · exact B1692195
  · exact B1692199
  · exact B1692203
  · exact B1692207
  · exact B1692211
  · exact B1692215
  · exact B1692219
  · exact B1692223
  · exact B1692227
  · exact B1692231
  · exact B1692235
  · exact B1692239
  · exact B1692243
  · exact B1692247
  · exact B1692251
  · exact B1692255
  · exact B1692259
  · exact B1692263
  · exact B1692267
  · exact B1692271
  · exact B1692275
  · exact B1692279
  · exact B1692283
  · exact B1692287
  · exact B1692291
  · exact B1692295
  · exact B1692299
  · exact B1692303
  · exact B1692307
  · exact B1692311
  · exact B1692315
  · exact B1692319
  · exact B1692323
  · exact B1692327
  · exact B1692331
  · exact B1692335
  · exact B1692339
  · exact B1692343
  · exact B1692347
  · exact B1692351
  · exact B1692355
  · exact B1692359
  · exact B1692363
  · exact B1692367
  · exact B1692371
  · exact B1692375
  · exact B1692379
  · exact B1692383
  · exact B1692387
  · exact B1692391
  · exact B1692395
  · exact B1692399
  · exact B1692403
  · exact B1692407
  · exact B1692411
  · exact B1692415
  · exact B1692419
  · exact B1692423
  · exact B1692427
  · exact B1692431
  · exact B1692435
  · exact B1692439
  · exact B1692443
  · exact B1692447
  · exact B1692451
  · exact B1692455
  · exact B1692459
  · exact B1692463
  · exact B1692467
  · exact B1692471
  · exact B1692475
  · exact B1692479
  · exact B1692483
  · exact B1692487
  · exact B1692491
  · exact B1692495
  · exact B1692499
  · exact B1692503
  · exact B1692507
  · exact B1692511
  · exact B1692515
  · exact B1692519
  · exact B1692523
  · exact B1692527
  · exact B1692531
  · exact B1692535
  · exact B1692539
  · exact B1692543
  · exact B1692547
  · exact B1692551
  · exact B1692555
  · exact B1692559
  · exact B1692563
  · exact B1692567
  · exact B1692571
  · exact B1692575
  · exact B1692579
  · exact B1692583
  · exact B1692587
  · exact B1692591
  · exact B1692595
  · exact B1692599
  · exact B1692603
  · exact B1692607
  · exact B1692611
  · exact B1692615
  · exact B1692619
  · exact B1692623
  · exact B1692627
  · exact B1692631
  · exact B1692635
  · exact B1692639
  · exact B1692643
  · exact B1692647
  · exact B1692651
  · exact B1692655
  · exact B1692659
  · exact B1692663
  · exact B1692667
  · exact B1692671
  · exact B1692675
  · exact B1692679
  · exact B1692683
  · exact B1692687
  · exact B1692691
  · exact B1692695
  · exact B1692699
  · exact B1692703
  · exact B1692707
  · exact B1692711
  · exact B1692715
  · exact B1692719
  · exact B1692723
  · exact B1692727
  · exact B1692731
  · exact B1692735
  · exact B1692739
  · exact B1692743
  · exact B1692747
  · exact B1692751
  · exact B1692755
  · exact B1692759
  · exact B1692763
  · exact B1692767
  · exact B1692771
  · exact B1692775
  · exact B1692779
  · exact B1692783
  · exact B1692787
  · exact B1692791
  · exact B1692795
  · exact B1692799
  · exact B1692803
  · exact B1692807
  · exact B1692811
  · exact B1692815
  · exact B1692819
  · exact B1692823
  · exact B1692827
  · exact B1692831
  · exact B1692835
  · exact B1692839
  · exact B1692843
  · exact B1692847
  · exact B1692851
  · exact B1692855
  · exact B1692859
  · exact B1692863
  · exact B1692867
  · exact B1692871
  · exact B1692875
  · exact B1692879
  · exact B1692883
  · exact B1692887
  · exact B1692891
  · exact B1692895
  · exact B1692899
  · exact B1692903
  · exact B1692907
  · exact B1692911
  · exact B1692915
  · exact B1692919
  · exact B1692923
  · exact B1692927
  · exact B1692931
  · exact B1692935
  · exact B1692939
  · exact B1692943
  · exact B1692947
  · exact B1692951
  · exact B1692955
  · exact B1692959
  · exact B1692963
  · exact B1692967
  · exact B1692971
  · exact B1692975
  · exact B1692979
  · exact B1692983
  · exact B1692987
  · exact B1692991
  · exact B1692995
  · exact B1692999
  · exact B1693003
  · exact B1693007
  · exact B1693011
  · exact B1693015
  · exact B1693019
  · exact B1693023
  · exact B1693027
  · exact B1693031
  · exact B1693035
  · exact B1693039
  · exact B1693043
  · exact B1693047
  · exact B1693051
  · exact B1693055
  · exact B1693059
  · exact B1693063
  · exact B1693067
  · exact B1693071
  · exact B1693075
  · exact B1693079
  · exact B1693083
  · exact B1693087
  · exact B1693091
  · exact B1693095
  · exact B1693099
  · exact B1693103
  · exact B1693107
  · exact B1693111
  · exact B1693115
  · exact B1693119
  · exact B1693123
  · exact B1693127
  · exact B1693131
  · exact B1693135
  · exact B1693139
  · exact B1693143
  · exact B1693147
  · exact B1693151
  · exact B1693155
  · exact B1693159
  · exact B1693163
  · exact B1693167
  · exact B1693171
  · exact B1693175
  · exact B1693179
  · exact B1693183
  · exact B1693187
  · exact B1693191
  · exact B1693195
  · exact B1693199
  · exact B1693203
  · exact B1693207
  · exact B1693211
  · exact B1693215
  · exact B1693219
  · exact B1693223
  · exact B1693227
  · exact B1693231
  · exact B1693235
  · exact B1693239
  · exact B1693243
  · exact B1693247
  · exact B1693251
  · exact B1693255
  · exact B1693259
  · exact B1693263
  · exact B1693267
  · exact B1693271
  · exact B1693275
  · exact B1693279
  · exact B1693283
  · exact B1693287
  · exact B1693291
  · exact B1693295
  · exact B1693299
  · exact B1693303
  · exact B1693307
  · exact B1693311
  · exact B1693315
  · exact B1693319
  · exact B1693323
  · exact B1693327
  · exact B1693331
  · exact B1693335
  · exact B1693339
  · exact B1693343
  · exact B1693347
  · exact B1693351
  · exact B1693355
  · exact B1693359
  · exact B1693363
  · exact B1693367
  · exact B1693371
  · exact B1693375
  · exact B1693379
  · exact B1693383
  · exact B1693387
  · exact B1693391
  · exact B1693395
  · exact B1693399
  · exact B1693403
  · exact B1693407
  · exact B1693411
  · exact B1693415
  · exact B1693419
  · exact B1693423
  · exact B1693427
  · exact B1693431
  · exact B1693435
  · exact B1693439
  · exact B1693443
  · exact B1693447
  · exact B1693451
  · exact B1693455
  · exact B1693459
  · exact B1693463
  · exact B1693467
  · exact B1693471
  · exact B1693475
  · exact B1693479
  · exact B1693483
  · exact B1693487
  · exact B1693491
  · exact B1693495
  · exact B1693499
  · exact B1693503
  · exact B1693507
  · exact B1693511
  · exact B1693515
  · exact B1693519
  · exact B1693523
  · exact B1693527
  · exact B1693531
  · exact B1693535
  · exact B1693539
  · exact B1693543

theorem solution (m : ℕ) (hlo : 1691546 ≤ m) (hhi : m ≤ 1693546) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 422886 ≤ j := by omega
    have hj2 : j ≤ 423385 := by omega
    have hb : Blo 1691546 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
