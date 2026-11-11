-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_finiteactivity_nojump_source_clock_drift
-- name    : AvramDividend.Classical.avram_bva22_original_finiteactivity_nojump_source_clock_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:02:51.203525+00:00
-- url     : https://prove2.me/theorems/e7acab65-8c64-4f37-9279-3f9090cf8a2e
-- title:
--   Original finite-activity BV physical drift on any no-source-jump clock interval
-- statement:
--   On one original standing finite-activity BV probability-one event, whenever the physical cumulative negative-jump source has equal values at two ordered clocks within a finite horizon, the actual original process increment equals the physical drift times the interval length. This is a source-specific no-jump prefix needed to account for zero-reserve contact and continuous Stieltjes cash between jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_finiteactivity_nojump_source_clock_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) →
      X.X b ω - X.X a ω = ((b : ℝ) - (a : ℝ)) * X.drift := by sorry
