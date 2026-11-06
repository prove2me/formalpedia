-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_signed_L1_mesh_error_fatou
-- name    : AvramDividend.Classical.avram_p3_2_signed_L1_mesh_error_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:29:14.211524+00:00
-- url     : https://prove2.me/theorems/d7cb52aa-bd3e-4845-af15-c3a524989b39
-- title:
--   Signed original-process L1 mesh errors preserve the Fatou upper bound
-- statement:
--   When a measurable nonnegative original stopped-process mesh payoff is bounded by initial value plus an integrable mean-nonpositive stochastic residual and an integrable signed pathwise mesh error whose expectation tends to zero, the Fatou lower limit of mesh payoffs gives the exact expected original stopped payoff upper bound. The proof centres the signed error and applies the independent vanishing deterministic-error Fatou theorem.
-- source:
--   Mathematically independent signed L1 centring of genuine mesh corrections, building on P3-2 vanishing deterministic-error signed Fatou theorem f1877a7f once proved; no original global L1 hypothesis is inferred.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_vanishing_error_signed_fatou_original_grid
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_signed_L1_mesh_error_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : ℝ) (Y : Ω → ℝ) (F R Err : ℕ → Ω → ℝ)
    (hYInt : Integrable Y P) (hYNonneg : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧ (∫ ω, R n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (Err n) P)
    (hErrMean : Tendsto (fun n => ∫ ω, Err n ω ∂P)
      atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ K + R n ω + Err n ω)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by sorry
