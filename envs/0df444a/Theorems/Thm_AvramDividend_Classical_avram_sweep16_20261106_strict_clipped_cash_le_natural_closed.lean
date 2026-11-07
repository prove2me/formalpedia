-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_strict_clipped_cash_le_natural_closed
-- name    : AvramDividend.Classical.avram_sweep16_20261106_strict_clipped_cash_le_natural_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:39:20.619187+00:00
-- url     : https://prove2.me/theorems/201226c7-4f36-4bc2-8d5b-7bdb73a3c386
-- title:
--   Generic physical-payment clipped-cash integral is bounded by natural stopped-clock closed cash
-- statement:
--   For each original path, the nonnegative Stieltjes cash measured on paymentTimes(min(σ,n)) up to any arbitrary real T is bounded by cash measured on paymentTimes(σ) and the closed true natural stopped-clock horizon. The inequality is uniform under all measures, all nonnegative integrands, all sample spaces and any horizon. It follows from an exact set-inclusion reduction and monotonicity of both inner and outer lintegrals.
-- source:
--   Direct reduction for original UBV 429e17ca from previously Proved localised natural stopped-clock budgets 3b8e6210 and full-horizon bridge 196220b2. Depends on child theorem AvramDividend.Classical.avram_sweep16_20261106_strict_clipped_times_subset_natural_closed, and only the valid MeasureTheory.lintegral_mono_set/lintegral_mono. Retains the time-zero atom; additional right-boundary atom on RHS is harmless. Original X/P/filtration/discount can be substituted into the universally quantified measures and integrands.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_strict_clipped_cash_le_natural_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (σ : Ω → ℝ≥0∞) (μ : Ω → Measure ℝ) (f : Ω → ℝ → ℝ≥0∞)
    (n : ℕ) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (σ ω) (n : ℝ≥0∞)) ∩ Iic T,
      f ω t ∂(μ ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩
      Iic (((min (σ ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
      f ω t ∂(μ ω) ∂P) := by sorry
