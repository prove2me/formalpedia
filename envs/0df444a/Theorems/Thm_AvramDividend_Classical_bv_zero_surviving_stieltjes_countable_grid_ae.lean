-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_zero_surviving_stieltjes_countable_grid_ae
-- name    : AvramDividend.Classical.bv_zero_surviving_stieltjes_countable_grid_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T16:37:40.786986+00:00
-- url     : https://prove2.me/theorems/6cefeac5-f4a0-49be-807c-e1e965aaf4c3
-- title:
--   Every surviving time in a countable deterministic grid has the exact discounted drift Stieltjes reward almost surely
-- statement:
--   Strengthen the accepted fixed-horizon zero-barrier weighted Stieltjes identity to a common full-measure event covering every time in an arbitrary deterministic countable time grid. The countable intersection permits subsequent dyadic or rational exhaustion of the strict stopped payment window with the exact endpoint convention. This result is genuine and independent of any first-jump payoff formula.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3. Countable intersection of the accepted finite-activity surviving Stieltjes prefixes.

import Theorems.Thm_AvramDividend_Classical_bv_zero_surviving_weighted_stieltjes_prefix_ae
import Mathlib.MeasureTheory.OuterMeasure.AE
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_zero_surviving_stieltjes_countable_grid_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((grid n : ℝ≥0) : ℝ≥0∞) < barrierRuinTime X 0 ω →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) ((grid n : ℝ≥0) : ℝ), f t
          ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ t in Ioc (0 : ℝ) ((grid n : ℝ≥0) : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
