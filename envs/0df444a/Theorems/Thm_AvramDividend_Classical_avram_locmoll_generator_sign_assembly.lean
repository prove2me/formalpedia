-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_generator_sign_assembly
-- name    : AvramDividend.Classical.avram_locmoll_generator_sign_assembly
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:23:00.605081+00:00
-- url     : https://prove2.me/theorems/132976a4-7d51-591f-bcdb-69c7f89c4996
-- title:
--   Integrating a nonpositive linear generator residual preserves its sign
-- statement:
--   Integrating a nonpositive linear generator residual preserves its sign
-- source:
--   Avram Proposition 4(i), exact decomposition of 4ce72d47-4d5a-479e-bf24-f651ec5f67ec

import Mathlib
open MeasureTheory Filter
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_generator_sign_assembly
    (a b q : ℝ) (A B J W : ℝ → ℝ)
    (hA : Integrable A) (hB : Integrable B)
    (hJ : Integrable J) (hW : Integrable W)
    (hsign : ∀ᵐ r ∂volume, a * A r + b * B r + J r - q * W r ≤ 0) :
    a * (∫ r, A r) + b * (∫ r, B r) + (∫ r, J r) -
      q * (∫ r, W r) ≤ 0 := by sorry
