-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB85_integral_expected_finite_step_kernel
-- name    : AvramDividend.Classical.avram_gbB85_integral_expected_finite_step_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:54:21.411738+00:00
-- url     : https://prove2.me/theorems/678ac360-2f79-4fea-9419-9dda52840b3e
-- title:
--   Finite expected step kernel integrates to cell width times coefficient sum
-- statement:
--   Integrating the expectation of a finite, disjoint half-open step kernel across the positive horizon gives exactly the step width times the finite sum of expected coefficients. Each coefficient is integrable, so finite-sum interchange and scalar indicator interval integration are valid.
-- source:
--   Lebesgue integration child of original two-grid step time-integral B78; independent of any stochastic process.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB85_integral_expected_finite_step_kernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (F : ℕ → Ω → ℝ) (hF : ∀ r, Integrable (F r) P) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then F r ω else 0) ∂P) ∂volume) =
      δ * (Finset.range N).sum (fun r => ∫ ω, F r ω ∂P) := by sorry
