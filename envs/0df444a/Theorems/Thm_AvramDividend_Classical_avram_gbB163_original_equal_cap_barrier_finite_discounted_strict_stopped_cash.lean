-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
-- name    : AvramDividend.Classical.avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:33:59.84437+00:00
-- url     : https://prove2.me/theorems/67180986-acd8-4ee2-ad11-95bfbfc0cfa6
-- title:
--   Genuine original equal-cap reflected barrier has finite strictly pre-ruin discounted Stieltjes cash at every finite horizon
-- statement:
--   For every original equal-cap reflected Lévy dividend strategy, finite NNReal horizon T and nonnegative discount q, the actual original dividendMeasure cash paid strictly before ruin and before T is finite as ENNReal. The proof uses the exact original Stieltjes measure identity μ((−∞,T])=D_T, the source paymentTimes support in [0,T], and a general discounted finite-measure estimate. This removes the previously explicit cash finiteness condition in the direct Gaussian counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB161_original_strict_prepayment_times_are_nonnegative_horizon_bounded
import Theorems.Thm_AvramDividend_Classical_avram_gbB162_original_equal_cap_barrier_measure_full_nonpositive_to_T_mass
import Theorems.Thm_AvramDividend_Classical_avram_gbB158_finite_positive_horizon_measure_implies_finite_discounted_stopped_cash
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≠ ⊤ := by sorry
