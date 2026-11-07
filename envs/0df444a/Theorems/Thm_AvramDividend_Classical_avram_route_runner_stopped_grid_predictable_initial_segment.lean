-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_stopped_grid_predictable_initial_segment
-- name    : AvramDividend.Classical.avram_route_runner_stopped_grid_predictable_initial_segment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:34:52.470859+00:00
-- url     : https://prove2.me/theorems/0ae52c11-12ab-403e-b3c6-0b69921562dc
-- title:
--   Stopped monotone-grid prefix selector yields predictable selected-cell events
-- statement:
--   For the original stopped Lévy filtration and a finite monotone physical clock grid, construct a bounded first-crossing index whose selected cells form an initial segment and whose selected-prefix events are measurable in the respective right-continuous σ-algebras. This composes the deterministic selector and accepted original stopping-time mask measurability without assuming zero overshoot or fabricated source processes. Measurability of the whole Nat-valued index will be a subsequent obligation for the bounded-prefix martingale theorem.
-- source:
--   Original process predictable stopped source grid: exact Proved mask 5319a1cb-c412-4ada-bbb3-e490e66cb669 plus new source-exact pointwise selector 204f43a5-a2c4-4b1f-807f-6f1aa82b427e, providing bounded-prefix events for Proved source budget 2b993cd3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_stopped_grid_predictable_initial_segment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    ∃ k : Ω → ℕ,
      (∀ ω, k ω ≤ m) ∧
      (∀ ω i, i < m →
        ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω)) ∧
      (∀ i, MeasurableSet[𝓕.rightCont (u i)]
        {ω : Ω | i < k ω}) := by sorry
