-- Prove2me | solution 1 for syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T13:48:47.527509+00:00
-- url     : https://prove2.me/submissions/08b7050f-d577-4df3-8a67-ebfcb321a21e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_word_length_6956_to_7620_affine_nondivisibility
import Theorems.Thm_syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463
import Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_ge_7621_with_rotated_baseline_2887463

set_option autoImplicit false

theorem solution (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6956 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  by_cases hlt : w.length < 7621
  · exact syracuse_word_length_6956_to_7620_affine_nondivisibility
      w hpositive hlength hlt hgap hlowSharp hbaselineBudget
  · have hge7621 : 7621 ≤ w.length := by omega
    by_cases hrot2887463 : ∀ d : ℕ, d < w.length →
        (2887463 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
          syracuseAffineConstant (w.rotate d)
    · exact syracuse_primitive_word_affine_nondivisibility_ge_7621_with_rotated_baseline_2887463
        w hpositive hge7621 hprimitive hgap hlow hlowSharp hbaselineBudget hrot2887463
    · push_neg at hrot2887463
      exact syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463
        w hpositive hgap hlowSharp hrot2887463
