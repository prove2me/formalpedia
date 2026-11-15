-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb26_standing_original_BV_HJB_strict_positive_origin
-- name    : AvramDividend.Classical.avram_bvb26_standing_original_BV_HJB_strict_positive_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:52:08.11513+00:00
-- url     : https://prove2.me/theorems/786bca56-800c-4283-8dfd-8d9383649e94
-- title:
--   Strictly positive origin payoff from original Standing BV HJB hypotheses
-- statement:
--   For the same original Standing spectrally negative BV Levy process X with positive drift and any candidate w satisfying the finite-cap or top-cap generator and slope HJB assumptions, show w(0)>0. This eliminates the degenerate zero-boundary-payoff case and assists stopped dividend contact analysis. Derive from the existing Proved standing-positive-drift and origin-value-positive theorems.
-- source:
--   Original Standing BV drift theorem 0432f641 Proved; original BV HJB positive origin theorem 92e61d41 Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb26_standing_original_BV_HJB_strict_positive_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    : 0 < w 0 := by sorry
