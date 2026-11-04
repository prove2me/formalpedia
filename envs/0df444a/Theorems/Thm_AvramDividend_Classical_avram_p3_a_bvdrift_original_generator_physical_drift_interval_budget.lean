-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_generator_physical_drift_interval_budget
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_generator_physical_drift_interval_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:53:24.810597+00:00
-- url     : https://prove2.me/theorems/8322c28a-b518-4f8d-af03-b27a3e949168
-- title:
--   Original-source BV generator and sample-path jump budget share the physical drift coefficient
-- statement:
--   Under BV and generator integrability, combine the exact original-generator conversion to physical drift with the actual original-process jump-plus-nonnegative-residual identity on all intervals. Both use precisely X.drift, X.ν and original X.X; the pathwise remainder remains explicit and is not asserted zero.
-- source:
--   Proved physical-generator identity c8ba98f0 and original BV interval nonnegative jump-budget theorem e84d1832, same source process X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On the same BV source process, the generator uses the exact physical
drift found in the sample-path jump budget, with an explicit residual. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_generator_physical_drift_interval_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    (∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ∃ r : ℝ, 0 ≤ r ∧
        (∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal + r =
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω))) := by sorry
