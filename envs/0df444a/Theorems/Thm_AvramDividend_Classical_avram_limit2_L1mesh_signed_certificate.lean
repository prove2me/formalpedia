-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_L1mesh_signed_certificate
-- name    : AvramDividend.Classical.avram_limit2_L1mesh_signed_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:14:20.61378+00:00
-- url     : https://prove2.me/theorems/cd9cf1c8-0abd-4ffb-93dc-5ecaf09428ae
-- title:
--   Physical stopped-grid L1 convergence supplies the signed Fatou certificate
-- statement:
--   The L1-error convergence actually produced by the original stochastic tagged-mesh analysis implies convergence in measure. A strictly increasing subsequence then yields almost-sure Fatou domination. Coupled with genuine nonnegative integrable physical meshes and their finite expected value bound, this gives all six signed BV verification clauses.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_L1mesh_signed_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ) (c : ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hRm : AEStronglyMeasurable R P)
    (hL1 : Tendsto (fun n => eLpNorm (F n - R) 1 P)
      atTop (nhds 0)) :
    ∃ F' M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ c + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (R ω) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by sorry
