-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_finiteactivity_standing_two_clock_source_ledger
-- name    : AvramDividend.Classical.avram_bva22_original_finiteactivity_standing_two_clock_source_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:56:28.273199+00:00
-- url     : https://prove2.me/theorems/43789790-42b7-421e-9945-92cc17bd7f46
-- title:
--   Original finite-activity BV source increment identity between any two deterministic clocks
-- statement:
--   For the same original probability space and stopped BV Levy source with Standing and finite negative jump intensity, each pair of clocks up to a positive finite horizon obeys the exact drift-minus-original-source-jump increment ledger on a common almost-everywhere event. This is the deterministic grid increment needed in the finite-activity physical Stieltjes cash argument; no auxiliary process or independent copy is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_finiteactivity_standing_two_clock_source_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      X.X b ω - X.X a ω =
        ((b : ℝ) - (a : ℝ)) * X.drift -
          ((∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
           (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by sorry
