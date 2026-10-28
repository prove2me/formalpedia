-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedLower_strictCrossing_rightInterval
-- name    : AvramDividend.Classical.levy_shiftedLower_strictCrossing_rightInterval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:11:09.715642+00:00
-- url     : https://prove2.me/theorems/c319d3c1-fd81-476c-b6ee-cd651e93c404
-- title:
--   Shifted Lévy increments preserve every strict lower threshold crossing on a right interval
-- statement:
--   For each Lévy sample path, any nonnegative time shift u and a strict downward crossing of the increment X(u+s)-X(u), the crossing remains strict over a nonempty interval to the right of s. This supplies the hypothesis for the generic exact lower first-passage clock on shifted paths.
-- source:
--   Apply the Proved ordinary strict lower right-interval theorem at time u+s and threshold lower+X(u); subtract u from the interval endpoint.

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedLower_strictCrossing_rightInterval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (lower : ℝ) :
    ∀ s : ℝ≥0, X.X (u + s) ω - X.X u ω < lower →
      ∃ v : ℝ≥0, s < v ∧
        ∀ r : ℝ≥0, s ≤ r → r < v →
          X.X (u + r) ω - X.X u ω < lower := by sorry
