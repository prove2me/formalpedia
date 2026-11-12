-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB88_finite_step_expectation_time_sum_interchange
-- name    : AvramDividend.Classical.avram_gbB88_finite_step_expectation_time_sum_interchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:14:15.472325+00:00
-- url     : https://prove2.me/theorems/cf084ee4-bd57-44c1-a7ce-78698d076bbf
-- title:
--   Expected finite-step kernel interchanges both finite sums and time integration
-- statement:
--   For finitely many integrable real random coefficients, the expectation of a finite grid-indicator sum can be exchanged with the sum, and the time integral over the finite horizon can then be exchanged with the same finite sum. This isolates Bochner integrability and finite linearity from the interval geometry.
-- source:
--   Finite-sum linearity child for original exact expected finite-step kernel B85.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB88_finite_step_expectation_time_sum_interchange
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (F : ℕ → Ω → ℝ) (hF : ∀ r, Integrable (F r) P) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then F r ω else 0) ∂P) ∂volume) =
      (Finset.range N).sum (fun r =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then (∫ ω, F r ω ∂P) else 0 ∂volume) := by sorry
