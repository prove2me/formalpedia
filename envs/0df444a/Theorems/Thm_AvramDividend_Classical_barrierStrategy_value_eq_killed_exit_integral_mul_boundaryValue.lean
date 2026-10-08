-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
-- name    : AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:53:38.423686+00:00
-- url     : https://prove2.me/theorems/2f4d50d7-b08b-4db7-a7e6-3fef6281ade5
-- title:
--   Barrier value factors at first successful upcrossing through the killed exit integral
-- statement:
--   For 0≤x≤a with a>0, the barrier strategy pays no dividends before the reserve first reaches the barrier. If ruin occurs first, the contribution is zero. On successful upward passage, spectral negativity gives no upward overshoot and the strong Markov property restarts the same barrier strategy from reserve a. Hence the value from x is the killed discounted probability of upward passage before ruin multiplied by the barrier value started at a. The displayed integral is written explicitly so this theorem does not depend on any still-Open exit-law theorem merely for a helper definition.
-- source:
--   Avram, Palmowski and Pistorius (2007), strong-Markov/first-passage step underlying the barrier identity preceding equation (5.1), together with the two-sided exit event of equation (3.6). This theorem isolates the stochastic restart step from the separate scale-function evaluation of the killed exit integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) *
        dividendValue X q a (barrierStrategy X a a) := by sorry
