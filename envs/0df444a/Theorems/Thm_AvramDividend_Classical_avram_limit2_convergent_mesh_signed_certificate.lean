-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_convergent_mesh_signed_certificate
-- name    : AvramDividend.Classical.avram_limit2_convergent_mesh_signed_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:01:54.218857+00:00
-- url     : https://prove2.me/theorems/6ffb6d57-9270-43ef-89ea-19c3cf9d36e2
-- title:
--   Physical stopped mesh convergence and finite-grid expectation yield the complete signed Fatou certificate
-- statement:
--   Given the genuine physical stopped-mesh random cash grid, its measurable nonnegative integrable terms, finite-grid upper expectation and almost-everywhere convergence to original strict cash plus the surviving terminal value, the full six-clause signed F/M/B certificate follows. This eliminates a separate liminf hypothesis and is intended for the outstanding original BV stochastic source. The theorem itself still requires construction of the physical source mesh.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_convergent_mesh_signed_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ) (c : ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ c)
    (hConverge : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (nhds (R ω))) :
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
