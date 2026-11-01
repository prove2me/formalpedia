-- Prove2me | solution 1 for syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:59:52.487899+00:00
-- url     : https://prove2.me/submissions/a9022889-fd55-4145-a6e1-f58dbcf8c02a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_power_gap_baseline_budget_period_sparse_6291
import Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline_sparse_period

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
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  have hsparse : w.length = 6291 ∨ 6956 ≤ w.length :=
    syracuse_power_gap_baseline_budget_period_sparse_6291
      w.length w.sum hlength hgap hbaselineBudget
  exact syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline_sparse_period
    w hpositive hlength hprimitive hgap hlow hlowSharp hbaselineBudget hrotatedBaseline hsparse
