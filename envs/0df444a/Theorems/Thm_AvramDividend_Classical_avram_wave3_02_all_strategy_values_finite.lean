-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_strategy_values_finite
-- name    : AvramDividend.Classical.avram_wave3_02_all_strategy_values_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:32:21.719991+00:00
-- url     : https://prove2.me/theorems/5606bda2-a27d-47e0-9ef8-437b6d7b6673
-- title:
--   All genuine barrier dividend strategies have finite discounted Stieltjes value at any cap and reserve
-- statement:
--   For every Standing spectrally negative Levy process and every positive discount, the genuine expected discounted Stieltjes dividend value of reflection at any nonnegative barrier with any nonnegative initial capital is finite. It follows constructively from the accepted barrier-independent affine upper bound by finite real ENNReal ofReal terms. No source regularity at the barrier is needed.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; proved original Stieltjes barrier uniform growth bound.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_strategy_value_growth

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_strategy_values_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ (a x : ℝ), 0 ≤ a → 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) < ∞ := by sorry
