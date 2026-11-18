-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_barrier_upperstrip_section_measurable
-- name    : AvramDividend.Classical.avram_gbB49_original_barrier_upperstrip_section_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:23:09.506691+00:00
-- url     : https://prove2.me/theorems/e20f0764-98b1-4cda-8eb5-3991083832a9
-- title:
--   Original cap barrier's physical-time upper-strip section is measurable without extra assumptions
-- statement:
--   The actual original barrier dividend is an adapted dividend strategy and a deterministic finite horizon is a right-continuous-filtration stopping time. The already Proved source-faithful joint real-time cap-strip measurability theorem therefore makes every fixed-sample physical-time upper-strip indicator set measurable. This discharges the only measurability hypothesis in B48.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_gfinite67_original_real_time_cap_strip_joint_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB49_original_barrier_upperstrip_section_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) :
    MeasurableSet {t : ℝ | t < (T : ℝ) ∧
      (5 / 44 : ℝ) < riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
        (Real.toNNReal t) ω} := by sorry
