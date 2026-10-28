-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_two_grid_levy_upcrossing_clock_is_stopping
-- name    : AvramDividend.Classical.chat08_two_grid_levy_upcrossing_clock_is_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:39:07.233444+00:00
-- url     : https://prove2.me/theorems/58317a38-7847-48ba-93ed-8d5643b46f7c
-- title:
--   First threshold hit on a two-observation grid is a stopping time
-- statement:
--   An adapted Lévy path is inspected first at s and then at t, stopping at the first strict threshold hit and otherwise at a terminal time u. For s≤t≤u this is a stopping time, using the observed-event switching rule inductively.
-- source:
--   chat08_stopping_time_early_observed_switch and chat08_two_level_levy_upcrossing_clock_stopping_time.

import Theorems.Thm_AvramDividend_Classical_chat08_stopping_time_early_observed_switch
import Theorems.Thm_AvramDividend_Classical_chat08_two_level_levy_upcrossing_clock_stopping_time
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_two_grid_levy_upcrossing_clock_is_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (a : ℝ) :
    IsStoppingTime ℱ
      (fun ω => if a < X.X s ω then (s : WithTop ℝ≥0)
        else if a < X.X t ω then (t : WithTop ℝ≥0)
        else (u : WithTop ℝ≥0)) := by sorry
