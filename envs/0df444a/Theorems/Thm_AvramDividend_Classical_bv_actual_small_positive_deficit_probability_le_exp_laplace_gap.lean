-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_small_positive_deficit_probability_le_exp_laplace_gap
-- name    : AvramDividend.Classical.bv_actual_small_positive_deficit_probability_le_exp_laplace_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:01:53.036653+00:00
-- url     : https://prove2.me/theorems/4dcbcea3-e3f8-47a0-bc9c-46c36b115b6f
-- title:
--   Actual BV Lévy small-positive drift deficit is bounded by its exact Laplace/zero-atom gap
-- statement:
--   Under explicit measurability and integrability conditions, identify the actual compensated-drift deficit's small-positive probability upper bound from the exact Lévy Laplace transform and its zero atom. This is the process-level connection required to estimate each equal-length grid cell in the finite-activity zero-barrier first-jump proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.3, equation (3.14); accepted Prove2Me actual Lévy transform and zero-atom theorems.

import Theorems.Thm_AvramDividend_Classical_small_positive_deficit_measureReal_le_laplace_gap
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_deficit_laplace_nat
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.MeasureTheory.Integral.Bochner.Set
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_small_positive_deficit_probability_le_exp_laplace_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) (a : ℝ)
    (D : Ω → ℝ)
    (hD : D = fun ω => (t : ℝ) * X.drift - X.X t ω)
    (hSmallMeas : MeasurableSet {ω : Ω | 0 < D ω ∧ (n : ℝ) * D ω ≤ a})
    (hZeroMeas : MeasurableSet {ω : Ω | D ω = 0})
    (hLeft : Integrable
      (fun ω => if 0 < D ω ∧ (n : ℝ) * D ω ≤ a then (1 : ℝ) else 0) P)
    (hRight : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-((n : ℝ) * D ω))) P)
    (hZero : Integrable
      (fun ω => if D ω = 0 then (1 : ℝ) else 0) P) :
    P.real {ω : Ω | 0 < D ω ∧ (n : ℝ) * D ω ≤ a} ≤
      Real.exp a *
        (Real.exp (-((t : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) -
          Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by sorry
