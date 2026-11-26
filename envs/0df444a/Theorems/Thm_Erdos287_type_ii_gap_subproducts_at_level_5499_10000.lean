-- Prove2me | Theorems.Thm_Erdos287_type_ii_gap_subproducts_at_level_5499_10000
-- name    : Erdos287.type_ii_gap_subproducts_at_level_5499_10000
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T21:31:24.870198+00:00
-- url     : https://prove2.me/theorems/65e62fa3-6db7-56f1-a428-a02173fba655
-- title:
--   Type II subproducts across an exponent gap at level 0.5499
-- statement:
--   Let the nonnegative exponents in a finite box sum to one, with each nonsmooth exponent at most 0.3. A smooth exponent is at least 0.325 or a subproduct exponent lies in [0.01,0.10016] or [0.125,0.30004]. The stated Type I, short Type II, and regular Type II arithmetic size tests at sieve level 0.5499 hold in these three respective cases. The nominal coefficient 2/0.5499 is less than 3.64.
-- source:
--   Erdős #287, mixed-residue sieve and Fouvry (C.4).

import Mathlib

theorem Erdos287.type_ii_gap_subproducts_at_level_5499_10000 {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 3 / 10)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 10000000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 13 / 40 ≤ x i) ∨
      ∃ J ⊆ I, (1 / 100 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 313 / 3125) ∨
        (1 / 8 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 7501 / 25000)) ∧
    (∀ m r s : ℝ, 13 / 40 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ 5499 / 10000 - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧ r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν q r s : ℝ, 1 / 100 ≤ ν → ν ≤ 313 / 3125 → 0 ≤ q → q ≤ ε →
      0 ≤ r → r ≤ 2813 / 6250 + ε → 0 ≤ s → s ≤ 4991 / 50000 + ε →
      2 * (r + q) + s ≤ 1 - ε ∧
      5 * ν / 2 + (r + q) + 5 * s / 2 ≤ 1 - ε ∧
      5 * ν / 4 + 3 * (r + q) / 2 + 2 * s ≤ 1 - ε ∧
      5 * ν + 4 * (r + q) + 5 * s - 1 ≤ 6 * ν + 2 * (r + q) + 5 * s) ∧
    (∀ ν r s : ℝ, 1 / 8 ≤ ν → ν ≤ 7501 / 25000 → 0 ≤ r → 0 ≤ s →
      r ≤ 5499 / 10000 - ν + 2 * ε → s ≤ ν - ε →
      2 * r + ν ≤ 1 - ε ∧ r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧ r + 3 * ν / 2 ≤ 1 - ε ∧
      (r - s / 2 + ν ≤ 1 / 2 - ε ∨
        r + s / 2 ≤ 1 / 2 - ε ∧ 7 * r / 4 + 5 * ν / 4 + s ≤ 1 - ε)) ∧
    2 / (5499 / 10000 : ℝ) < 91 / 25 := by sorry
