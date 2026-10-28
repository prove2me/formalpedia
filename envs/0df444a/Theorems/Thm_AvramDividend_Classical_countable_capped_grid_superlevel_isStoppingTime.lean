-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_capped_grid_superlevel_isStoppingTime
-- name    : AvramDividend.Classical.countable_capped_grid_superlevel_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:30:09.555709+00:00
-- url     : https://prove2.me/theorems/4d7621b1-27c5-477b-bdf8-d10159caf57e
-- title:
--   First sampled superlevel arrival, capped at a deterministic horizon, is a stopping time under a right-continuous filtration
-- statement:
--   For an adapted real-valued process on an arbitrary right-continuous filtration, and any countable observation schedule with observation times ≤H, define the capped first observed superlevel crossing time as the infimum over indices n of clock(n) if u(clock(n))≥x and H otherwise. This is a stopping time. Each individual sampled-or-H clock is a stopping time by the measurable-at-observation-time event and the pinned Mathlib piecewise-constant stopping-time lemma. Countable infima of stopping times are stopping times in right-continuous filtrations. The right-continuity assumption is explicit and mathematically indispensable for the generic countable-inf route. Applies to the actual reflected Lévy path once its adaptedness is available.
-- source:
--   Pinned Mathlib.Probability.Process.Stopping, isStoppingTime_piecewise_const and IsStoppingTime.iInf; excursion first-passage time finite-grid approximations.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.countable_capped_grid_superlevel_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (u : ℝ≥0 → Ω → ℝ) (hu : Adapted 𝓕 u)
    (clock : ℕ → ℝ≥0) (H : ℝ≥0)
    (hclock : ∀ n : ℕ, clock n ≤ H) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨅ n : ℕ, if x ≤ u (clock n) ω
        then (clock n : WithTop ℝ≥0) else (H : WithTop ℝ≥0)) := by sorry
