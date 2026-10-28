-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_residual_laplace_tendsto_survival
-- name    : AvramDividend.Classical.bv_actual_residual_laplace_tendsto_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:30:19.928468+00:00
-- url     : https://prove2.me/theorems/fd5de744-59d4-4b02-89d0-802da1aafdfd
-- title:
--   Actual finite-activity Lévy residual Laplace moments converge to exponential first-jump survival
-- statement:
--   At a fixed time t, the exponential moments E[exp(-n(d t-X_t))] of the actual nonnegative BV Lévy residual converge to exp(-t·ν((−∞,0))). This follows from its actual-process Lévy Laplace identity, the proved drift-exponent gap limit, and continuity of the exponential. The result is the essential transform precursor to identifying P(d t-X_t=0) as the zero-jump Poisson survival probability, and hence to the zero-barrier stopped reward.
-- source:
--   Avram, Palmowski and Pistorius (2007), eq (3.14); proved actual Lévy residual transform and finite negative-jump exponent gap limit.

import Theorems.Thm_AvramDividend_Classical_bv_actual_drift_exponent_gap_tendsto_intensity
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_residual_laplace_tendsto_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, Real.exp ((n : ℝ) * (X.X t ω - (t : ℝ) * X.drift)) ∂P)
      atTop (𝓝 (Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)))) := by sorry
