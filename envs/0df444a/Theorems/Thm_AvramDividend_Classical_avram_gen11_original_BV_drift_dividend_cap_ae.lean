-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen11_original_BV_drift_dividend_cap_ae
-- name    : AvramDividend.Classical.avram_gen11_original_BV_drift_dividend_cap_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:26:54.787422+00:00
-- url     : https://prove2.me/theorems/437132c7-6c8c-402d-8ca2-83867273c4d3
-- title:
--   Actual original BV Lévy drift yields an almost-sure all-time cap after right and continuous dividends
-- statement:
--   For an actual source bounded-variation spectrally negative Lévy process with nonnegative physical drift, a nonnegative right-dividend and subsequent continuous drift-cancelling dividend keep the controlled reserve below initial reserve plus drift through the horizon, for every time on a single probability-one event.
-- source:
--   Source-exact original-process bridge for Avram A19 countermodel. Uses canonical original BV drift upper theorem c1de9f71 and Proved drift-cancelling payout cap 9da98a2d. Does not assert the existence of a particular levy triplet, adapted strategy, or the disproof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_all_times
import Theorems.Thm_AvramDividend_Classical_avram_gen10_drift_cancelled_dividend_cap_bound
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen11_original_BV_drift_dividend_cap_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hb : 0 ≤ X.drift) (x T : ℝ)
    (s : Ω → ℝ≥0) (A : Ω → ℝ) (hA : ∀ ω, 0 ≤ A ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      x + X.X t ω -
        ((if s ω < t then A ω else 0) +
          X.drift * max ((t : ℝ) - T) 0) ≤ x + X.drift * T := by sorry
