-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_finite_activity_standing_exact_drift_jump_path
-- name    : AvramDividend.Classical.avram_bva22_original_finite_activity_standing_exact_drift_jump_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:42:05.831896+00:00
-- url     : https://prove2.me/theorems/dcda0213-3cd9-45c6-a14c-b1fa3026d85d
-- title:
--   Original standing BV finite-activity path equals drift minus actual negative jump sum
-- statement:
--   On the exact original probability space under Standing and bounded variation, the finite negative jump intensity branch has a single almost-everywhere path identity through each bounded horizon: the risk input X equals physical drift minus the cumulative genuine negative jump magnitudes. This source-specific corollary is used in the finite-activity cash ledger and preserves the distinction from the stronger hX-free Open lemma 69dc5e14.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_finite_activity_standing_exact_drift_jump_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
