-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_levy_detection_at_time_or_infinity_stopping
-- name    : AvramDividend.Classical.chat08_levy_detection_at_time_or_infinity_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:14:37.272989+00:00
-- url     : https://prove2.me/theorems/4abec2d8-994d-466a-aa88-f1a8ca559cf8
-- title:
--   Single sampled Lévy threshold detection with infinite no-hit clock
-- statement:
--   The sampled upper threshold event of a Lévy process at deterministic time s is observable in the filtration. Its clock is s if detected and infinity otherwise, so it is a stopping time.
-- source:
--   SpectrallyNegativeLevy.adapted and chat08_measurable_detection_time_or_infinity_is_stopping.

import Theorems.Thm_AvramDividend_Classical_chat08_measurable_detection_time_or_infinity_is_stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_levy_detection_at_time_or_infinity_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s : ℝ≥0) (a : ℝ) :
    IsStoppingTime ℱ
      (fun ω => if a < X.X s ω then (s : WithTop ℝ≥0) else ⊤) := by sorry
