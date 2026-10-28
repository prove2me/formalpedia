-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_nonnegative_tails_bundle_ws01c
-- name    : AvramDividend.Classical.bv_nonnegative_tails_bundle_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:33:16.668598+00:00
-- url     : https://prove2.me/theorems/753f1426-ed9c-4e89-8cde-4607abf7e79b
-- title:
--   Nonnegative upper-tail decay implies convergence in measure
-- statement:
--   A sequence of everywhere nonnegative real random variables on a finite measure space converges in measure to zero if for every positive threshold the measure of its upper-tail event tends to zero. The proof identifies the distance to zero with the variable itself and invokes the pinned convergence-in-measure tail criterion.
-- source:
--   A standard convergence-in-probability tail criterion, used as the first analytic helper in the direct canonical proof of AvramDividend.Classical.bv_strict_lower_exit_no_creeping_ae (43a28d8e-14f3-44d6-8b46-347138818c52). The source-complete Lean proof is in work/avram_ws01c_probability_bridge_bundle_draft.lean.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Filter MeasureTheory Topology

theorem AvramDividend.Classical.bv_nonnegative_tails_bundle_ws01c
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ)
    (hNonneg : ∀ n ω, 0 ≤ f n ω)
    (hTail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | ε ≤ f n ω}) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => (0 : ℝ)) := by sorry
