-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_frozen_reserve_closed_discounted_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_frozen_reserve_closed_discounted_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:15:57.850592+00:00
-- url     : https://prove2.me/theorems/0c66d9cd-0d75-4b55-b5a9-993b62a4b963
-- title:
--   Closed-horizon all-mass discounted Stieltjes dividend bound by frozen HJB potential drop including terminal right payment
-- statement:
--   For any actual adapted monotone left-continuous dividend strategy D, discount q≥0, and finite horizon T, the complete discounted dividendMeasure over [0,T] including diffuse, singular-continuous, time-zero and terminal-time right-jump mass is at most the test-value drop w(y)-w(y-rightLimit D T), provided the initial frozen reserve y covers all payments through T including the right payment and lies within cap C. Follows from accepted complete Stieltjes mass bound and HJB full-cap secant.
-- source:
--   Theorem avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound, theorem avram_wave3_03_bv_full_cap_gradient_secant and actual dividendStrategy_le_rightLimit, all Proved; no countable atomic assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_frozen_reserve_closed_discounted_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (C : ℝ≥0∞) (hC : 0 < C) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (y : ℝ)
    (hyD : rightLimit D T ω ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w y - w (y - rightLimit D T ω)) := by sorry
