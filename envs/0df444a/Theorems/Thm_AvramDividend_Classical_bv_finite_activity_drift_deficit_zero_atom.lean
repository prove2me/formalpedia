-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_drift_deficit_zero_atom
-- name    : AvramDividend.Classical.bv_finite_activity_drift_deficit_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:45:52.120607+00:00
-- url     : https://prove2.me/theorems/957b07a4-c041-4b38-872f-d4aa2f00714a
-- title:
--   No drift deficit at fixed time has the finite negative-jump exponential survival probability
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process with finite negative-jump intensity and measurable fixed-time capital, the probability (expressed as the real integral of an event indicator) that the drift deficit is still zero at t is exp(-lambda*t). This is the genuine no-jump event law without inventing a compound-Poisson auxiliary process. Apply the already proved nonnegative Laplace atom limit to the drift deficit, the actual drift-deficit Laplace transform and the finite-jump exponential-deficit limit; identify the two sequence limits in a Hausdorff space.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 first-jump argument after Proposition 1.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_deficit_laplace_nat
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_limit_nat
import Mathlib.Topology.Separation.Hausdorff
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_drift_deficit_zero_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (t : ℝ≥0)
    (hMeas : Measurable (fun ω => X.X t ω)) :
    (∫ ω, if (t : ℝ) * X.drift - X.X t ω = 0 then (1 : ℝ) else 0 ∂P) =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
