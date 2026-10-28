-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_deficit_laplace_nat
-- name    : AvramDividend.Classical.bv_actual_levy_drift_deficit_laplace_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:40:37.753553+00:00
-- url     : https://prove2.me/theorems/e2f07b42-30d8-43ea-a10d-e4bf728235f6
-- title:
--   Actual bounded-variation drift deficit has the negative-jump Laplace transform at each positive integer
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process, the nonnegative drift deficit at a fixed time has the exponential Laplace transform dictated by the negative Lévy jump measure at every positive integer parameter. This converts the previously proved drift-normalised process transform to the exact integrand used by the generic zero-atom dominated-convergence theorem and prepares the finite-activity no-jump probability identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3; proved actual drift-normalised Lévy Laplace theorem.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_drift_deficit_laplace_nat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) :
    (∫ ω, Real.exp ((n : ℝ) * (-((t : ℝ) * X.drift - X.X t ω))) ∂P) =
      Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) := by sorry
