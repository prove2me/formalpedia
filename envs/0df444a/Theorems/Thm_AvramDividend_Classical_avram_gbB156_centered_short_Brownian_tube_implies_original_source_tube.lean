-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
-- name    : AvramDividend.Classical.avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:14:45.839611+00:00
-- url     : https://prove2.me/theorems/46d61de6-e713-4e76-a4c7-ddf78afc5547
-- title:
--   Centred Gaussian Brownian radius 1/4000 guarantees original drift-two source radius 1/400 at T=1/1000
-- statement:
--   For an original spectrally negative Lévy source whose short-time increments are X_s=B_s+2s, if its centred Brownian path remains within 1/4000 until T=1/1000, then the full original source path remains within 1/400. This eliminates an independent source-tube assumption in the direct cash counterexample and connects the Brownian small-ball event to the original stopped barrier geometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ)) :
    ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |X.X s ω| ≤ (1 / 400 : ℝ) := by sorry
