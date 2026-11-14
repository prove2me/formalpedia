-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_nnreal_window_measure_finite_atomless
-- name    : AvramDividend.Classical.avram_chat24_nnreal_window_measure_finite_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:34:26.713225+00:00
-- url     : https://prove2.me/theorems/13b37c4d-9d22-4480-a8f3-41717a34fa67
-- title:
--   Finite atomless physical measure after nonnegative time conversion
-- statement:
--   The image under Real.toNNReal of Lebesgue measure restricted to Icc 0 T is finite and atomless. On the restricted interval, the preimage of {t} is contained in the singleton of the real coercion of t. This includes t=0 and T<0. It supplies the measure hypotheses for the AE moving-chord limit in parent 7b52eba8-6fe9-40c9-89f7-a341ca70210b.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_nnreal_window_measure_finite_atomless (T : ℝ) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    IsFiniteMeasure μ ∧ ∀ t : ℝ≥0, μ {t} = 0 := by sorry
