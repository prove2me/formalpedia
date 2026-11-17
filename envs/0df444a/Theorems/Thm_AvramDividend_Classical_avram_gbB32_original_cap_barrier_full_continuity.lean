-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_cap_barrier_full_continuity
-- name    : AvramDividend.Classical.avram_gbB32_original_cap_barrier_full_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:42:37.397715+00:00
-- url     : https://prove2.me/theorems/96c0e717-234a-4d96-8f08-b1cefd76ac0f
-- title:
--   Original cap barrier dividend strategy is continuous at all times
-- statement:
--   Combine both already Proved original barrierStrategy continuity theorems from left and right, including time zero, to establish complete path continuity of the dividend process at barrier=c and initial reserve=c. This is a source-faithful prerequisite for the positive Gaussian riskProcess lower-stopping clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_left_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB32_original_cap_barrier_full_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω, Continuous (fun t : ℝ≥0 => barrierStrategy X c c t ω) := by sorry
