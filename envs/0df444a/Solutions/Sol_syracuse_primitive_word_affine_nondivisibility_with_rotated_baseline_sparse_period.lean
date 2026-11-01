-- Prove2me | solution 1 for syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline_sparse_period
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T15:12:58.470127+00:00
-- url     : https://prove2.me/submissions/4c9f5eee-64b6-4532-a0e6-c50dce3554c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_word_length_6291_affine_nondivisibility
import Theorems.Thm_syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502
import Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502

set_option autoImplicit false

theorem solution (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6291 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2310000 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d))
    (hsparsePeriod : w.length = 6291 ∨ 6956 ≤ w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  rcases hsparsePeriod with h6291 | h6956
  · exact syracuse_word_length_6291_affine_nondivisibility
      w hpositive h6291 hgap hlowSharp
  · by_cases hrot2786502 : ∀ d : ℕ, d < w.length →
        (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
          syracuseAffineConstant (w.rotate d)
    · exact syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502
        w hpositive h6956 hprimitive hgap hlow hlowSharp hbaselineBudget hrot2786502
    · push_neg at hrot2786502
      exact syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502
        w hpositive hgap hlowSharp hrot2786502
