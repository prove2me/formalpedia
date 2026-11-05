-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_ruin_extension_value_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:36:18.714564+00:00
-- url     : https://prove2.me/theorems/f8376baa-6772-4161-9b42-50f77da12c7d
-- title:
--   Original ruin-extended dividend value is Borel measurable across reserve zero
-- statement:
--   The original dividend verification value is continuous on the nonnegative reserve half-line and vanishes at every negative reserve. These hypotheses imply global Borel measurability even if the value has a genuine jump at zero, by constructing a continuous max-zero extension and a measurable negative-halfline split.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_ruin_extension_value_measurable
(w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y < 0, w y = 0) :
Measurable w := by sorry
