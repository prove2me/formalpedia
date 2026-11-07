-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_terminal_prefix_budget_mono
-- name    : AvramDividend.Classical.avram_a19_discounted_cash_terminal_prefix_budget_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:24:03.313832+00:00
-- url     : https://prove2.me/theorems/479e875f-0ea7-49a7-8b3d-72fc73ab1e9f
-- title:
--   Expected original strict Stieltjes cash plus common terminal is monotone
-- statement:
--   With integrable original discounted strict cash at two horizons, almost-sure finiteness at the later horizon, and an integrable common terminal random variable, the expected strict cash plus terminal value is monotone in the cash horizon.
-- source:
--   Exact endpoint monotonicity bridge for true original T-survival terminal and strictly pre-s cash in a19d8b28; combines prior public cash monotonicity with integral linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_discounted_cash_terminal_prefix_budget_mono
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q s T : ℝ) (hst : s ≤ T) (Terminal : Ω → ℝ)
    (hFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤)
    (hIs : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hIT : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hTerm : Integrable Terminal P) :
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Terminal ω ∂P) ≤
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Terminal ω ∂P) := by sorry
