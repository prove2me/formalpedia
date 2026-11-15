-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b248_original_positive_ruinclipped_clock_implies_ruin_strictly_after_zero_20261114
-- name    : AvramDividend.Classical.avram_b248_original_positive_ruinclipped_clock_implies_ruin_strictly_after_zero_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:39:53.448927+00:00
-- url     : https://prove2.me/theorems/a154bb94-ed9c-409b-aaf9-5c6adcaf386c
-- title:
--   Original positive ruin-clipped physical stopping clock excludes immediate ruin
-- statement:
--   For the actual spectrally negative Lévy process and dividend strategy, a positive physical stopping time bounded by the true clipped ruin clock implies ruin did not occur at time zero. The argument uses the exact finite ruin-time truncation, without changing the sample space or defining any post-ruin process. This is a guard for the positive-clock original physical Itô-Meyer ledger.
-- source:
--   Elementary order argument for the exact min(ruinTime, horizon).toNNReal clock supplied in B24 main source. Uses no stochastic distribution assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b248_original_positive_ruinclipped_clock_implies_ruin_strictly_after_zero_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ω : Ω) (hσpositive : 0 < σ ω) :
    0 < ruinTime X x D ω := by sorry
