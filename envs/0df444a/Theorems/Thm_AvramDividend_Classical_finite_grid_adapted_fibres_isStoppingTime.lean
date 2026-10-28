-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
-- name    : AvramDividend.Classical.finite_grid_adapted_fibres_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:03:29.474155+00:00
-- url     : https://prove2.me/theorems/aa6185a1-757c-4916-92dc-b2766a0aede9
-- title:
--   Finite adapted stopping-time grid fibres imply a genuine stopping time
-- statement:
--   If a random nonnegative time takes all of its values in a finite grid, and each exact time fibre belongs to the filtration at that time, the random time satisfies the actual Mathlib IsStoppingTime condition. For each t, the event τ≤t is the finite union of fibres whose grid values are at most t. This is the reusable bridge between finite-grid Esscher factorisation and measurability of stopped future paths.
-- source:
--   Finite adapted stopping-time construction; pinned Mathlib Finset.measurableSet_biUnion, Filtration.mono and accepted AvramDividend.Classical.isStoppingTime_withTop_of_le_events (7851293c-fd3e-4bc8-b3cb-9653ccf13cf3).

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Adapted measurable fibres on a finite time grid certify a stopping time. -/

theorem AvramDividend.Classical.finite_grid_adapted_fibres_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s}) :
    IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) := by sorry
