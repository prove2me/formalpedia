-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_discrete_stopping_time_inclusive_predictable_mask
-- name    : AvramDividend.Classical.avram_wave4_p1_discrete_stopping_time_inclusive_predictable_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:41:07.516141+00:00
-- url     : https://prove2.me/theorems/c1f65a27-80d4-4b9c-b25f-72f14ba0b98c
-- title:
--   Inclusive stopped survival indicator is predictable for the original discrete filtration
-- statement:
--   On the actual sample space and its filtration, prove that the inclusive stopped mask (n,omega)↦1_{n≤τ(omega)} belongs to the predictable sigma algebra for every genuinely adapted discrete stopping time τ. At n=0 it is the initial measurable atom; at n+1 survival is complement of {τ≤n}, which is F_n measurable by the stopping-time property and hence belongs to the pinned predictable singleton-step generator. A countable union of these singleton slices gives the full mask. This establishes stopped nonanticipativity for finite Poisson-grid integration; it does not assume martingale, compensation or source Lévy jump intensity. Does not claim the general real-time stopping mask.
-- source:
--   Pinned Mathlib Probability.Process.Stopping IsStoppingTime, Probability.Process.Predictable measurableSet_predictable_singleton_bot_prod and singleton_prod; countable measurable union.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave4_p1_discrete_stopping_time_inclusive_predictable_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℕ mΩ) (τ : Ω → ℕ)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) :
    MeasurableSet[𝓕.predictable]
      {p : ℕ × Ω | p.1 ≤ τ p.2} := by sorry
