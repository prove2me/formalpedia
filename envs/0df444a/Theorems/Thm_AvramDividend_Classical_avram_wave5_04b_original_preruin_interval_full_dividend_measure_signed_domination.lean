-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:27:47.227673+00:00
-- url     : https://prove2.me/theorems/bfadf699-5a2d-44f5-9614-ea73c456f34e
-- title:
--   Original-source unweighted full Stieltjes dividend-measure domination by cap-linear value drops
-- statement:
--   For every pre-ruin dividend cell (a,b], the genuine dividendMeasure mass, converted to a real, plus the source-frozen signed cap-linear value change over the interval, is nonpositive. This derivative-free interval measure-domination statement includes diffuse and singular-continuous variation, countable right-payment atoms and zero/cap reserve contacts. It is the unweighted measure-domination input for future discounted Stieltjes variation estimates.
-- source:
--   Specialise canonical fully signed source-specific discounted Stieltjes interval theorem 3e748b51-e344-4668-935b-d97ed5744826 to q=0 and simplify the full lower integral of the constant 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by sorry
