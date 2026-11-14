-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB272_original_gaussian_fixed_level_product_measure_null
-- name    : AvramDividend.Classical.avram_gbB272_original_gaussian_fixed_level_product_measure_null
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:41:02.164763+00:00
-- url     : https://prove2.me/theorems/a573d733-800a-4d5e-b7dc-89ab7eebdbf7
-- title:
--   Original Gaussian controlled reserve fixed-level event has zero product probability-time measure
-- statement:
--   For a genuinely original unbounded-variation zero-jump spectrally negative Lévy process and any original adapted dividend strategy, the product measure of original probability and Lebesgue real physical time assigns zero mass to the prescribed fixed-level postpayment reserve event on every deterministic finite time horizon. This is the integrated Tonelli-occupation statement targeted directly by the fourth-power time-grid estimates. It implies the original almost-everywhere zero occupation B100 by Fubini and restriction to any arbitrary finite ruin horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB272_original_gaussian_fixed_level_product_measure_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) :
    (P.prod volume)
      {z : Ω × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b} = 0 := by sorry
