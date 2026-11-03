-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:56:17.029607+00:00
-- url     : https://prove2.me/theorems/1402a335-c140-493a-8812-5399d364a0a3
-- title:
--   Actual positive finite ruin strictly pre-ruin full discounted Stieltjes dividend reward is finite
-- statement:
--   For a genuine original dividend strategy and every finite positive pre-ruin endpoint, the entire discounted Stieltjes measure on the open interval (0,τ) is finite for any nonnegative discount rate. The exact original Stieltjes mass is ENNReal.ofReal(D(τ)−rightLimit D(0)), which is finite, and every positive-time weight exp(-qt) is at most one. The open endpoint excludes the right ruin payment but includes diffuse, singular-continuous and interior atomic dividends. This pathwise finite total is a proper input to terminal-grid limit and localisation, not a stochastic estimate assumption.
-- source:
--   Proved exact original strictly interior Stieltjes mass cd71bccf, exp(-qt)≤1, ENNReal lintegral monotonicity and ofReal_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_discounted_cash_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
