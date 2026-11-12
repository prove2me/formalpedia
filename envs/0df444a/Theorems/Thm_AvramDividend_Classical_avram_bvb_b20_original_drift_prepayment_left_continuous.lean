-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_drift_prepayment_left_continuous
-- name    : AvramDividend.Classical.avram_bvb_b20_original_drift_prepayment_left_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:02:20.049017+00:00
-- url     : https://prove2.me/theorems/1e10f846-2ab9-42db-bbb3-cffb0e00e90b
-- title:
--   Original bounded-variation drift-minus-dividend prepayment reserve is left-continuous
-- statement:
--   For every original admissible strategy and every outcome, the drift reserve net of the dividend left limit is continuous when approached from the left at each nonnegative time. This preserves the exact prepayment side of jump-compensation quadrature.
-- source:
--   BV-B20 original-path analytic prerequisite for phys95, from admissible monotone dividend paths and Mathlib left-limit continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_original_drift_prepayment_left_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => x + (s : ℝ) * X.drift -
        Function.leftLim (fun r : ℝ≥0 => D r ω) s)
      (Iic t) t := by sorry
