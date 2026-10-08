-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_compensated_jump_integrable_levy
-- name    : AvramDividend.Classical.exp_compensated_jump_integrable_levy
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:29:37.211423+00:00
-- url     : https://prove2.me/theorems/7850173e-657e-45f3-87a6-05ea4d2264ce
-- title:
--   The full compensated exponential kernel is integrable against a spectrally negative Lévy measure
-- statement:
--   Let X be any spectrally negative Lévy process with the standard ν-integrable min(1,y²) moment. For every θ≥0 the complete negative-jump exponential compensation exp(θy)−1−θy1_{(-1,1)}(y) is ν-integrable on (-∞,0). The proven quadratic domination theorem bounds its absolute value by C min(1,y²), and the Lévy moment condition makes this majorant integrable. The kernel is measurable by continuity of the exponential and measurability of the truncation indicator. This gives a rigorous, unsplit jump integral as required by the Lévy–Khintchine exponent and the scale-function generator's Laplace calculation.
-- source:
--   Absolute integrability of the spectrally negative Lévy–Khintchine exponent's compensated jump kernel, an essential Fubini component of the optimal dividend generator proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem exp_compensated_jump_integrable_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
      (Iio 0) X.ν := by sorry
end AvramDividend.Classical
