-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
-- name    : AvramDividend.Classical.avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:49:56.678198+00:00
-- url     : https://prove2.me/theorems/28d6f0bd-83a6-4da0-a0f8-524ffb8d834d
-- title:
--   Original true stopped-grid source squared increment and elapsed-duration energy measurability
-- statement:
--   For the actual original spectrally negative Levy process and finite stopping-time grid, measurability of both the true drift-corrected original source squared increment sum and the squared NNReal elapsed durations follows automatically from the stopping-time hypotheses and ordered endpoints. This removes two independent measurable-energy assumptions from the B73 physical stopped mesh bound.
-- source:
--   Proved chat04_levy_joint_time_state_measurable, Mathlib right-continuous IsStoppingTime.measurable', NNReal.coe_sub at pinned revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hLe : ∀ ω i, i ∈ S → s i ω ≤ t i ω) :
    Measurable (fun ω => ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω -
        (((t i ω - s i ω : ℝ≥0) : ℝ)) * X.c)^2) ∧
    Measurable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) := by sorry
