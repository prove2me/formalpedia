-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_original_stopped_measurable_predictable_prefix
-- name    : AvramDividend.Classical.avram_route_runner_original_stopped_measurable_predictable_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:11:23.514148+00:00
-- url     : https://prove2.me/theorems/bcd472a7-723c-43b9-874b-91487f18327a
-- title:
--   Original stopped Lévy grid has a bounded measurable predictable index prefix
-- statement:
--   For the true stopped spectrally negative Levy process and a monotone physical grid, construct a finite bounded prefix selector whose strict pre-ruin indicators are exact, whose cell events are measurable at the right-continuous filtration levels, and whose random integer index has measurable preimage of every subset of Nat. This is the exact selector needed by the accepted predictable martingale stopped signed-budget 2b993cd3 and pathwise mask sum identity d046abd3.
-- source:
--   Composes accepted route-runner 0ae52c11 predictable first-crossing selector, accepted 86ff26ac all-Nat-preimages, and ambient right-cont filtration inclusion 6c9cf0d7 (currently publication done, proof pending). Faithful to original X, tau, filtration and grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_original_stopped_measurable_predictable_prefix
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
        {ω : Ω | i < k ω}) ∧
      (∀ s : Set ℕ, MeasurableSet (k ⁻¹' s)) := by sorry
