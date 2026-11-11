-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_all_BV_two_clock_source_increment_ae
-- name    : AvramDividend.Classical.avram_bva22_original_all_BV_two_clock_source_increment_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:08:19.72414+00:00
-- url     : https://prove2.me/theorems/ab16704d-ed99-4180-a81b-14a9db944cf9
-- title:
--   Original standing BV source-drift increment ledger at all pairs of physical clocks
-- statement:
--   On one probability-one event for the original spectrally negative Levy process with Standing and bounded variation, its increments between any two nonnegative clocks equal physical drift increment minus the change of its genuine cumulative negative-jump sum. No finite activity, truncation, independent process, auxiliary filtration, or chosen time horizon is needed. This shared source increment certificate feeds both finite and infinite activity BV Stieltjes/compensation branches.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_all_BV_two_clock_source_increment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0,
      X.X b ω - X.X a ω =
        ((b : ℝ) - (a : ℝ)) * X.drift -
          ((∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
           (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by sorry
