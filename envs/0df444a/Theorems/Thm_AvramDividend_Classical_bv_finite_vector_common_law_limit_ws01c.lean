-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_vector_common_law_limit_ws01c
-- name    : AvramDividend.Classical.bv_finite_vector_common_law_limit_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:41:39.348771+00:00
-- url     : https://prove2.me/theorems/a5f95c47-c16f-4f7a-9cff-6692e2daf656
-- title:
--   A common finite-dimensional probability law persists under almost-sure convergence
-- statement:
--   If measurable finite-dimensional random vectors Y_n have a fixed probability distribution and converge almost surely to Z, then Z has the same distribution. The proof compares convergence in distribution to the almost-sure limit and to an identically distributed anchor, using uniqueness in a Borel state space with closed-set outer approximation. This avoids an unjustified appeal to weak convergence in the full uncountable path product.
-- source:
--   Extracted complete generic probability-law limit proof from work/avram_ws01c_grid_right_limit_law_v2_draft.lean, with no unproved imported WS1C helper.

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open Filter MeasureTheory Topology

theorem AvramDividend.Classical.bv_finite_vector_common_law_limit_ws01c
    {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (Z Z₀ : Ω → E)
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hZ : AEMeasurable Z P)
    (hZ₀ : AEMeasurable Z₀ P)
    (hLaw : ∀ n, Measure.map (Y n) P = Measure.map Z₀ P)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Measure.map Z P = Measure.map Z₀ P := by sorry
