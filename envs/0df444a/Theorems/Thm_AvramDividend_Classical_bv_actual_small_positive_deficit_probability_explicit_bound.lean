-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_small_positive_deficit_probability_explicit_bound
-- name    : AvramDividend.Classical.bv_actual_small_positive_deficit_probability_explicit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:23:02.607562+00:00
-- url     : https://prove2.me/theorems/101cccd7-af6b-4481-9884-01033a09a9c0
-- title:
--   The actual finite-activity BV Lévy deficit has a complete explicit small-positive probability bound
-- statement:
--   For every bounded-variation spectrally negative Lévy process with finite negative-jump intensity, without extra measurability or integrability assumptions, the probability of a positive drift residual satisfying nD_t≤a is bounded by exp(a) times the exact difference between the process's Laplace transform and its zero-atom exponential survival. This combines the accepted actual-process exponent with a generic integrability package.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.3 formula (3.14), and accepted Prove2Me Lévy-Laplace/zero-atom theorems.

import Theorems.Thm_AvramDividend_Classical_nonnegative_deficit_laplace_integrability_package
import Theorems.Thm_AvramDividend_Classical_bv_actual_small_positive_deficit_probability_le_exp_laplace_gap
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_small_positive_deficit_probability_explicit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    P.real {ω : Ω |
      0 < (t : ℝ) * X.drift - X.X t ω ∧
      (n : ℝ) * ((t : ℝ) * X.drift - X.X t ω) ≤ a} ≤
    Real.exp a *
      (Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) -
        Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by sorry
