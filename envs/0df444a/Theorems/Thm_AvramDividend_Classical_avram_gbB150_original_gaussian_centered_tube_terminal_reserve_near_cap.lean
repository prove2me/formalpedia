-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
-- name    : AvramDividend.Classical.avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:05:48.620058+00:00
-- url     : https://prove2.me/theorems/b3f75e94-a71c-4f87-a6ea-95e05ee16d52
-- title:
--   Original reflected positive-drift Gaussian terminal reserve stays within 1/2000 below cap on centred Brownian tube
-- statement:
--   For an original reflected upper-cap reserve driven by the path X_s=2s+B_s, if the centred Brownian path stays within 1/4000 up to T, the regulator at T differs from the current source value by at most 1/2000. Consequently the terminal reserve Y_T remains at least C-1/2000. This sharpens the generic tube floor sufficiently for a direct discounted cash lower-bound counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ T →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ T →
      |B s| ≤ (1 / 4000 : ℝ)) :
    (1 / 8 : ℝ) - (1 / 2000 : ℝ) ≤
      riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω := by sorry
