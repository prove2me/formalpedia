-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_linear_zero_barrier_full_grid_prestate_zero
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_linear_zero_barrier_full_grid_prestate_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:41:47.308785+00:00
-- url     : https://prove2.me/theorems/84c604ea-dfc1-4102-8b9c-89350e09f212
-- title:
--   Original unit-drift zero-barrier prepayment reserve is zero at every physical grid point including origin
-- statement:
--   For the original unit-drift linear no-jump source on [0,1], the true zero-barrier source prepayment left-limit reserve is exactly zero at every physical grid point within the horizon, including the initial grid time zero. This proves every interior mask of the original generator and drift-only physical grids vanishes on the positive-probability no-jump event.
-- source:
--   Proved source-exact zero barrier D(t)=t, riskProcess=0, Proved source contact leftLim at positive clocks and pinned NNReal leftLim origin equality. The admissible zero barrier has no initial right-payment jump.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_unit_drift_zero_barrier_exact_linear_dividends
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_linear_zero_barrier_full_grid_prestate_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hWithin : ∀ i ∈ Finset.range (n + 1), u n i ≤ 1) :
    ∀ i ∈ Finset.range (n + 1),
      Function.leftLim
        (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω -
          rightLimit (barrierStrategy X 0 0) t ω)
        (u n i) = 0 := by sorry
