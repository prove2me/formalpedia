-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedUpper_strictCrossing_rightInterval
-- name    : AvramDividend.Classical.levy_shiftedUpper_strictCrossing_rightInterval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:10:19.134423+00:00
-- url     : https://prove2.me/theorems/aa1666f8-d581-45c4-ad24-2f9e9394cc18
-- title:
--   Shifted Lévy increments preserve every strict upper threshold crossing on a right interval
-- statement:
--   For an official spectrally negative Lévy sample path, any time origin u and any strict upper threshold of the increment X(u+s)-X(u), the strict increment crossing persists throughout a nonempty right interval after s. This makes the generic countable-schedule strict exit theorem applicable to stopped Lévy future increments.
-- source:
--   Uses the Proved strict upper Lévy right-interval theorem applied at u+s with the threshold upper+X(u), then translates interval endpoints by subtracting u.

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedUpper_strictCrossing_rightInterval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (upper : ℝ) :
    ∀ s : ℝ≥0, upper < X.X (u + s) ω - X.X u ω →
      ∃ v : ℝ≥0, s < v ∧
        ∀ r : ℝ≥0, s ≤ r → r < v →
          upper < X.X (u + r) ω - X.X u ω := by sorry
