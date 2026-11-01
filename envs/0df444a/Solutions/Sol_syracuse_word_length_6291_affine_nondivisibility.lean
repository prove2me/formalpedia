-- Prove2me | solution 1 for syracuse_word_length_6291_affine_nondivisibility
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T15:11:40.585558+00:00
-- url     : https://prove2.me/submissions/36599633-af71-473b-8d43-3ae890e66f81

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_affine_constant_some_rotation_le_mechanical_bound
import Theorems.Thm_syracuse_mechanical_numerator_6291_9971_strict_baseline_bounds
import Theorems.Thm_syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502

set_option autoImplicit false

open scoped BigOperators

private theorem two_pow_9970_le_three_pow_6291 : (2 : ℕ) ^ 9970 ≤ 3 ^ 6291 := by
  decide +kernel

theorem solution (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : w.length = 6291)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlowSharp : 306 * w.sum < 485 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  have hsum_le : w.sum ≤ 9971 := by omega
  have hsum_ge : 9971 ≤ w.sum := by
    by_contra hlt
    have hle9970 : w.sum ≤ 9970 := by omega
    have hpow_le : (2 : ℕ) ^ w.sum ≤ 2 ^ 9970 :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hle9970
    have hgap' : (3 : ℕ) ^ 6291 < 2 ^ w.sum := by
      simpa only [hlength] using hgap
    have hcontra : (3 : ℕ) ^ 6291 < 3 ^ 6291 :=
      lt_of_lt_of_le hgap' (le_trans hpow_le two_pow_9970_le_three_pow_6291)
    exact Nat.lt_irrefl _ hcontra
  have hsum : w.sum = 9971 := by omega
  obtain ⟨d, hd, hmech⟩ :=
    syracuse_affine_constant_some_rotation_le_mechanical_bound w (by omega)
  have hmech_6291 :
      syracuseAffineConstant (w.rotate d) ≤
        ∑ j ∈ Finset.range 6291,
          (3 : ℕ) ^ (6291 - 1 - j) * 2 ^ ((9971 * j) / 6291) := by
    simpa only [hlength, hsum] using hmech
  have hstrict := syracuse_mechanical_numerator_6291_9971_strict_baseline_bounds.2.2
  have hlt_2403661 :
      syracuseAffineConstant (w.rotate d) <
        2403661 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) :=
    lt_of_le_of_lt hmech_6291 hstrict
  have hle_2786502 :
      2403661 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) ≤
        2786502 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) :=
    Nat.mul_le_mul_right _ (by decide : 2403661 ≤ 2786502)
  have hsmall :
      syracuseAffineConstant (w.rotate d) <
        2786502 * (2 ^ w.sum - 3 ^ w.length) := by
    simpa only [hlength, hsum] using lt_of_lt_of_le hlt_2403661 hle_2786502
  exact syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502
    w hpositive hgap hlowSharp ⟨d, hd, hsmall⟩
