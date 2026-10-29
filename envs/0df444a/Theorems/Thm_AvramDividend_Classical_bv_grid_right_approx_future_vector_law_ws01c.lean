-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_grid_right_approx_future_vector_law_ws01c
-- name    : AvramDividend.Classical.bv_grid_right_approx_future_vector_law_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:14:32.344168+00:00
-- url     : https://prove2.me/theorems/0ed24cbc-0c8a-4d78-94bf-b7f91cda453b
-- title:
--   Right-approximated Lévy stopping clocks preserve finite-dimensional future-increment laws
-- statement:
--   For a spectrally negative Lévy process, finite clocks converging from above yield almost-sure convergence of finite future-increment vectors by right continuity. The unchanged finite-dimensional law passes to the limit using the now-Proved common-law convergence lemma; no uncountable product weak-convergence assertion is made.
-- source:
--   Cause-linked re-publication of terminal job 99a6805c-7449-47e3-a0d7-6364671ac54c, which failed only because bv_finite_vector_common_law_limit_ws01c had status Open then. That same necessary helper is now Proved UUID a5f95c47-c16f-4f7a-9cff-6692e2daf656, accepted candidate 17637. The exact formal statement and preamble are unchanged; original complete 43-line solution retained at work/avram_ws01c_grid_right_approx_future_vector_solution_direct.lean.

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation
import Theorems.Thm_AvramDividend_Classical_bv_finite_vector_common_law_limit_ws01c

open Filter MeasureTheory Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_grid_right_approx_future_vector_law_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (J : Finset ℝ≥0)
    (grid : ℕ → Ω → ℝ≥0) (raw : Ω → ℝ≥0)
    (hGridTends : ∀ ω, Tendsto (fun n => grid n ω) atTop (𝓝 (raw ω)))
    (hGridAbove : ∀ ω n, raw ω ≤ grid n ω)
    (hGridMeas : ∀ n, Measurable (fun ω : Ω =>
      fun j : J => X.X (grid n ω + j.1) ω - X.X (grid n ω) ω))
    (hRawMeas : Measurable (fun ω : Ω =>
      fun j : J => X.X (raw ω + j.1) ω - X.X (raw ω) ω))
    (hOrigMeas : Measurable (fun ω : Ω =>
      fun j : J => X.X j.1 ω))
    (hGridLaw : ∀ n,
      Measure.map (fun ω : Ω =>
        fun j : J => X.X (grid n ω + j.1) ω - X.X (grid n ω) ω) P =
      Measure.map (fun ω : Ω => fun j : J => X.X j.1 ω) P) :
    Measure.map (fun ω : Ω =>
      fun j : J => X.X (raw ω + j.1) ω - X.X (raw ω) ω) P =
    Measure.map (fun ω : Ω => fun j : J => X.X j.1 ω) P := by sorry
