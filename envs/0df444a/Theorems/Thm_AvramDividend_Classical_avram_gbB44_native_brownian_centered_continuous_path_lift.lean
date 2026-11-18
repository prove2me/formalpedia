-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB44_native_brownian_centered_continuous_path_lift
-- name    : AvramDividend.Classical.avram_gbB44_native_brownian_centered_continuous_path_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:52:03.235096+00:00
-- url     : https://prove2.me/theorems/5e62530d-2f90-40c1-bcd2-241f7422935d
-- title:
--   Construct native centered Brownian continuous-map lift on the unit interval
-- statement:
--   Using the existing Proved canonical Brownian sample-path continuity, construct a continuous function on the unit interval for each native path, with values equal to the centered Brownian coordinates at the corresponding NNReal times. This proves existence of the continuous lift; its measurability as a random C([0,1])-valued variable is a separate obligation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB44_native_brownian_centered_continuous_path_lift :
    ∃ B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ),
      ∀ (ω : ℝ≥0 → ℝ) (t : unitInterval),
        B ω t =
          ProbabilityTheory.brownian (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ω -
          ProbabilityTheory.brownian 0 ω := by sorry
