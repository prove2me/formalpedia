-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
-- name    : AvramDividend.Classical.avram_redux11_original_BV_raw_removed_residual_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:02:37.563019+00:00
-- url     : https://prove2.me/theorems/79a63ca0-322e-49b7-bd9b-2fcd3db555c5
-- title:
--   Original BV Lévy drift-minus-actual-negative-jumps residual vanishes almost surely
-- statement:
--   For the original same-probability-space bounded-variation spectrally negative Lévy process, the physical drift-minus-path-minus-actual-jump-sum remainder vanishes simultaneously at every nonnegative time on one probability-one event. No independent Lévy copy or grid-specific assumptions are introduced. The proof requires the full original BV path Lévy–Itô decomposition, eliminating any residual continuous component.
-- source:
--   Exact original BV source-process path identity needed to resolve the weighted raw-removed uniform-grid residual integrability branch d001f11f. The existing proved original global path theorem 45236e85 supplies the conditional Laplace route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux11_original_BV_raw_removed_residual_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0 := by sorry
