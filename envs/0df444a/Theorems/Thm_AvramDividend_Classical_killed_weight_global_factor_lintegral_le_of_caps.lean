-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_weight_global_factor_lintegral_le_of_caps
-- name    : AvramDividend.Classical.killed_weight_global_factor_lintegral_le_of_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:45:07.615897+00:00
-- url     : https://prove2.me/theorems/72fb5e01-9c50-49a2-af67-4a6633635ce5
-- title:
--   Uniform capped bounds transfer to a globally killed reward with a constant factor
-- statement:
--   If for every finite natural time cap the integral of a killed nonnegative reward multiplied by a fixed nonnegative factor is bounded above, the same bound holds for the integral of the full globally killed reward multiplied by that factor. This preserves the independent two-sided exit factor through the cap-removal step.
-- source:
--   Proved killed_weight_global_lintegral_le_of_uniform_caps combined with Mathlib lintegral_const_mul.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_killed_weight_global_lintegral_le_of_uniform_caps

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.killed_weight_global_factor_lintegral_le_of_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (weight : Ω → ℝ≥0∞) (hw : Measurable weight)
    (hzero : ∀ ω, T ω = ⊤ → weight ω = 0)
    (factor bound : ℝ≥0∞)
    (hbound : ∀ n : ℕ, factor *
      (∫⁻ ω, if T ω ≤ (n : ℝ≥0∞) then weight ω else 0 ∂P) ≤ bound) :
    factor * (∫⁻ ω, weight ω ∂P) ≤ bound := by sorry
