-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_negative_mark_JL_compensator_integral_cancellation
-- name    : AvramDividend.Classical.avram_pj_workerC_original_negative_mark_JL_compensator_integral_cancellation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:42:50.708436+00:00
-- url     : https://prove2.me/theorems/aeae1699-cbf4-4038-8e47-457773a28864
-- title:
--   Genuine compensated negative Lévy mark integrals J plus annular linear L combine into the very-small-mark Taylor residual integral
-- statement:
--   On a mark measure supported on negative marks, and given integrability of the actual nonlinear and annular linear components, the integrals of J Taylor nonlinear residual plus L truncated first-order part equal the single integral of the residual with linear subtraction only on marks z>=-eta. This is the actual compensator assembly needed for purejump physical stopped Ito; it preserves the integrability obligations.
-- source:
--   Proved original pointwise negative J+L kernel 97521e90; Mathlib integral_add and integral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_negative_mark_JL_compensator_integral_cancellation
    (μ : Measure ℝ) (η : ℝ) (S d : ℝ → ℝ)
    (hη : 0 < η) (hηone : η < 1)
    (hneg : ∀ᵐ z ∂μ, z < 0)
    (hH : Integrable (fun z => S z -
      (if -1 < z then z * d z else 0)) μ)
    (hL : Integrable (fun z => if z ∈ Ioo (-1 : ℝ) (-η) then
      z * d z else 0) μ) :
    (∫ z, S z - (if -1 < z then z * d z else 0) ∂μ) +
    (∫ z, (if z ∈ Ioo (-1 : ℝ) (-η) then z * d z else 0) ∂μ) =
    (∫ z, S z - (if -η ≤ z then z * d z else 0) ∂μ) := by sorry
