-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_negative_jump_generator_kernel_lower
-- name    : AvramDividend.Classical.avram_mix_fin26_negative_jump_generator_kernel_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:12:28.701203+00:00
-- url     : https://prove2.me/theorems/3c693b1c-6116-4101-85cf-0a11b7af2b63
-- title:
--   Original finite-mixed generator negative-mark kernel is bounded below by minus the current reward
-- statement:
--   For the original spectrally negative Lévy generator, if a negative jump lands at a nonnegative reward and the derivative at the pre-jump reserve is nonnegative, its compensated jump kernel is at least minus the pre-jump reward. The compensation term for negative jumps is nonnegative. This pointwise estimate will be integrated under finite jump intensity to bound the original jump generator without large-mark first moments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_negative_jump_generator_kernel_lower
    (w : ℝ → ℝ) (y z : ℝ) (hz : z < 0)
    (hwyz : 0 ≤ w (y + z)) (hDeriv : 0 ≤ deriv w y) :
    -w y ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by sorry
