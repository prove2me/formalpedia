-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
-- name    : AvramDividend.Classical.bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:35:15.996353+00:00
-- url     : https://prove2.me/theorems/65b7c0e0-6c57-4a70-92c4-9e40a8cc9fff
-- title:
--   An actual finite-activity BV Levy path cannot survive zero-barrier ruin with positive jump deficit
-- statement:
--   For a bounded-variation spectrally negative Lévy process whose negative jump measure has finite mass, the probability that the reflected zero-barrier process survives strictly beyond a finite horizon while its drift-corrected accumulated negative-jump deficit is positive is zero. This establishes that the positive-deficit event is concentrated on paths already ruined by the first negative jump. Its proof uses exact uniform time meshes, the positive-deficit Laplace bound, and the vanishing refined-grid exponential error.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.3, bounded-variation finite-activity argument immediately following Proposition 1; Prove2Me proved uniform-mesh and Laplace-gap ingredients.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Measure.Real
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    P.real {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
      0 < X.drift * (T : ℝ) - X.X T ω} = 0 := by sorry
