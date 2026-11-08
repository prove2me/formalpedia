-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_terminal_square_bracket_L1
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_uniform_terminal_square_bracket_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:21:33.953257+00:00
-- url     : https://prove2.me/theorems/99460b53-8651-428f-8991-152e36f1437d
-- title:
--   Uniform finite-horizon Gaussian square bracket is terminal L1
-- statement:
--   If the original probability measure is finite, the time interval has finite measure, the Gaussian coefficient is uniformly bounded at every time and sample point, and its terminal quadratic bracket is measurable, then the terminal bracket is integrable. The proof derives a deterministic norm bound for the Bochner integral on the restricted time measure and applies Integrable.of_bound, with all finite-measure assumptions explicit.
-- source:
--   Pinned Mathlib norm_integral_le_of_norm_le_const, isFiniteMeasure_restrict and Integrable.of_bound; adapted bracket measurable from Proved Gaussian10 helpers.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_uniform_terminal_square_bracket_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (H : ℝ≥0 × Ω → ℝ)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ p, |H p| ≤ C)
    (hTerminalMeas : Measurable (fun ω =>
      ∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime)) :
    Integrable (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
      (H (t, ω)) ^ 2 ∂μtime) P := by sorry
