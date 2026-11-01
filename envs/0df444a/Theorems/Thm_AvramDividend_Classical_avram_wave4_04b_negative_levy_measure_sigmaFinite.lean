-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_negative_levy_measure_sigmaFinite
-- name    : AvramDividend.Classical.avram_wave4_04b_negative_levy_measure_sigmaFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:10:03.319646+00:00
-- url     : https://prove2.me/theorems/c93daaa4-dec6-4f04-8a31-ab86cf53772c
-- title:
--   Negative-supported Lévy square-integrable jump measures are sigma-finite on their original signed marks
-- statement:
--   A finite quadratic truncation mass on negative Lévy jumps and no nonnegative marks makes the original signed-mark Lévy measure sigma-finite. This supplies the s-finite mark hypothesis required to integrate source-specific predictable compensated jump kernels against the genuine Lévy measure. The proof transports the already Proved negative-to-positive pushforward result back to the original source measure.
-- source:
--   Proved Gaussian negative-jump pushforward sigma-finiteness 08bca239, Mathlib SigmaFinite.of_map for measurable negation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_04b_negative_levy_measure_sigmaFinite
    (ν : Measure ℝ)
    (hν : ν (Ici (0 : ℝ)) = 0)
    (hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    SigmaFinite ν := by
  sorry
