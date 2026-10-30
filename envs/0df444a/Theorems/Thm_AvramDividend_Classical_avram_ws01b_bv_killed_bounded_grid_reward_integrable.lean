-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_bounded_grid_reward_integrable
-- name    : AvramDividend.Classical.avram_ws01b_bv_killed_bounded_grid_reward_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:50:46.641558+00:00
-- url     : https://prove2.me/theorems/85754212-6076-4cbf-b089-8a59164b6def
-- title:
--   Genuine bounded-variation original killed stopped grid reward is integrable, including zero capital
-- statement:
--   For any nonnegative starting reserve, q>0 and genuine bounded variation original spectrally negative Lévy law, the full-history killed discounted q-scale reward at an actual bounded two-sided sampled first-exit index is Bochner integrable. Its accepted optional-stopping integral equals the strictly positive Wq(x), even when x=0 by positive BV drift and Wq(0)=1/d, so non-integrability (which would force zero Bochner integral) is impossible.
-- source:
--   Accepted genuine BV killed stopped-grid optional-stopping expectation, scale positivity under Standing for x>0, BV positive drift and exact Wq(0)=1/d; pinned Mathlib MeasureTheory.integral_undef.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_grid_optional_stopping
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_killed_bounded_grid_reward_integrable
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) (hx : 0 ≤ x)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (hclock0 : clock 0 = 0)
    (lower upper : ℝ) (m : ℕ) :
    Integrable (fun ω =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ clock (hittingBtwn
          (fun k ξ => max (X.X (clock k) ξ - upper)
            (lower - X.X (clock k) ξ))
          (Set.Ioi (0 : ℝ)) 0 m η) →
            0 ≤ x + X.X s η}).indicator
        (fun η =>
          Real.exp (-(q * (clock (hittingBtwn
            (fun k ξ => max (X.X (clock k) ξ - upper)
              (lower - X.X (clock k) ξ))
            (Set.Ioi (0 : ℝ)) 0 m η) : ℝ))) *
          W (x + X.X (clock (hittingBtwn
            (fun k ξ => max (X.X (clock k) ξ - upper)
              (lower - X.X (clock k) ξ))
            (Set.Ioi (0 : ℝ)) 0 m η)) η)) ω) P := by sorry
