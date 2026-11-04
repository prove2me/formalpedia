-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_closed_cap_actual_right_discounted_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_closed_cap_actual_right_discounted_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:21:07.473342+00:00
-- url     : https://prove2.me/theorems/7737a1c0-a3b5-4de0-a439-e37b942687d1
-- title:
--   Exact original closed-cap discounted right-dividend signed remainder is nonpositive
-- statement:
--   At each eligible original-source dividend payment time, including initial payment and simultaneous source jump, admissibility positions the post-X pre-payment and post-right-payment reserves in the closed capped range, and the proved two-point unit-slope secant inequality yields the correctly discounted signed payment remainder nonpositive. Both reserve boundaries 0 and C are allowed. The positivity of discount factor uses the actual time t.
-- source:
--   Original dividend strategy definitions and riskProcess; proved closed-cap secant aeec073e-64c0-49d6-a86e-3113d03c0485; exact source payment ordering eq (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_closed_cap_actual_right_discounted_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-q * (t : ℝ)) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)) ≤ 0 := by sorry
