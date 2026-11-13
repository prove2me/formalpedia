-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a47_original_small_source_increment_enlarged_compact_band
-- name    : AvramDividend.Classical.avram_ga_a47_original_small_source_increment_enlarged_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:56:47.725199+00:00
-- url     : https://prove2.me/theorems/83d956af-7ef6-46bd-9e38-28f988886ef9
-- title:
--   Original source small-increment postpayment spatial Taylor endpoint stays in enlarged positive compact band
-- statement:
--   On the original source X and dividend D, a starting postpayment reserve in a positive compact band and a sufficiently small raw Gaussian source displacement guarantee that the actual spatial Taylor endpoint stays in the enlarged positive compact band.
-- source:
--   Direct original safe-cell positive-only C2 spatial Taylor compact band input for b0d9951c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_a47_original_small_source_increment_enlarged_compact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0)
    (a b δ : ℝ) (ha : 0 < a) (hδ : 0 ≤ δ)
    (hδa : δ ≤ a / 2)
    (hBand : a ≤ x + X.X s ω - rightLimit D s ω ∧
      x + X.X s ω - rightLimit D s ω ≤ b)
    (hInc : |X.X t ω - X.X s ω| ≤ δ) :
    a / 2 ≤ x + X.X t ω - rightLimit D s ω ∧
      x + X.X t ω - rightLimit D s ω ≤ b + a / 2 := by sorry
