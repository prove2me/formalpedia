-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_frozen_preruin_source_cell_nonnegative
-- name    : AvramDividend.Classical.avram_p3_bv_original_frozen_preruin_source_cell_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:13:01.614599+00:00
-- url     : https://prove2.me/theorems/a9e0006d-b2e7-4e0c-857f-0fcc370ac525
-- title:
--   Actual frozen dividend reserve nonnegative at every original zero or strict pre-ruin physical source endpoint
-- statement:
--   For the actual spectrally negative Levy reserve and admissible original dividend strategy, an ordered physical grid cell whose right endpoint is zero or strictly before ruin has nonnegative source-frozen reserve evaluated using dividends immediately after the earlier grid time.
-- source:
--   Source-exact application of Proved d6323bfa original postpayment reserve nonnegativity and f7eef805 original dividend right-limit monotonicity; discharges the stopping/cap positivity input of source-chain grid integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Actual admissibility makes every physical frozen-dividend source endpoint
   nonnegative up to the inclusive initial/strict pre-ruin clock. -/

theorem AvramDividend.Classical.avram_p3_bv_original_frozen_preruin_source_cell_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (i : ℕ)
    (hui : u i ≤ u (i + 1))
    (hLive : u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u i) ω := by sorry
