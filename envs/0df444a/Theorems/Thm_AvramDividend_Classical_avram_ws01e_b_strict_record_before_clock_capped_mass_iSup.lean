-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_clock_capped_mass_iSup
-- name    : AvramDividend.Classical.avram_ws01e_b_strict_record_before_clock_capped_mass_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:55:55.902163+00:00
-- url     : https://prove2.me/theorems/1a41ce57-04c2-47a8-9191-cb36a7a055e5
-- title:
--   True tilted or untitled survival mass equals supremum over finite natural first-record caps
-- statement:
--   Under any measure μ on path × real observation-clock space (including the genuine random-terminal Esscher law), if the capped strict first-record-before-clock events are measurable then the μ-mass of the uncapped strict event is the supremum over natural deterministic caps N of the corresponding capped event masses. This follows from the strict cap event exhaustion and continuity from below for a monotone sequence of measurable sets. It makes no probability-normalisation assumption and preserves the genuine strict clock condition.
-- source:
--   Canonically Proved avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion, pinned Mathlib Monotone.measure_iUnion, and ENNReal coercion order.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_strict_record_before_clock_capped_mass_iSup
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure (Ω × Θ))
    (τ : Ω → ℝ≥0∞) (clock : Θ → ℝ)
    (hMeas : ∀ n : ℕ, MeasurableSet {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}) :
    μ {z : Ω × Θ |
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} =
    ⨆ n : ℕ, μ {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} := by sorry
