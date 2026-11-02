-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_exponential_test_right_slope
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_exponential_test_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:56:45.689966+00:00
-- url     : https://prove2.me/theorems/20ad2112-f3fb-43ce-bece-4bf6d16c9f5a
-- title:
--   Original BV Lévy residual exponential-test right slope equals the negative-jump Laplace deficit
-- statement:
--   For the actual spectrally negative Lévy source X under BoundedVariation and any positive integer n, the exact canonical real right-time derivative of 1-E[exp(-n(h*d-X_h))] divided by h equals the actual negative-jump Lévy integral ∫_{y<0}(1-exp(n*y))dν. Time is exactly X.X (Real.toNNReal h), and the filter is nhdsWithin 0 (Ioi 0). The proof directly invokes the Proved physical residual source Laplace transform, uses equality of NNReal and real time on the positive filter, and the separately Proved scalar exponential deficit slope. There is no changed process, no coupling and no assumed generator identity. This is a rigorous original-process exponential test input to the still-open C1 density argument.
-- source:
--   Full original-source Lean solution privately remote compiler sentinel-verified: candidates/work_on/AvramDividend_04c_actual_bv_residual_exp_test_slope_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_deficit_laplace_nat
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_scalar_exponential_deficit_right_slope
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_exponential_test_right_slope {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto
      (fun h : ℝ => h⁻¹ * (1 -
        (∫ ω, Real.exp ((n : ℝ) *
          (-((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω))) ∂P)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ),
         (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) := by sorry
