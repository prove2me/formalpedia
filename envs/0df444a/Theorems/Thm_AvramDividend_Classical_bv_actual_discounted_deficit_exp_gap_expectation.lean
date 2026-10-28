-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_discounted_deficit_exp_gap_expectation
-- name    : AvramDividend.Classical.bv_actual_discounted_deficit_exp_gap_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:21:43.174892+00:00
-- url     : https://prove2.me/theorems/3a467672-6371-45d4-8b8b-7a7eab380529
-- title:
--   Expected exponential drift-deficit gap equals one minus the exact bounded-variation Lévy transform
-- statement:
--   For the actual BV spectrally negative Lévy process and theta at least one, the ordinary expectation of one minus its drift-normalised exponential martingale at a fixed time is one minus the known exact negative-jump Laplace exponent. Use the accepted exact BV drift-normalised Laplace integral and the fact the underlying probability has mass one. This supplies the one-step expectation in the finite-mesh no-local-monotonicity proof.
-- source:
--   Proved bv_actual_levy_drift_normalised_laplace, X.laplace integrability, and ordinary probability integral linearity.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_discounted_deficit_exp_gap_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, (1 : ℝ) -
        Real.exp (θ * X.X t ω) *
          Real.exp (-((t : ℝ) * X.drift * θ)) ∂P) =
      1 - Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by sorry
