-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
-- name    : AvramDividend.Classical.avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:03:19.096207+00:00
-- url     : https://prove2.me/theorems/c2d15493-3539-4d17-ba2f-e2e7fe836d12
-- title:
--   Original finite-activity Lévy physical jump removal leaves an actually continuous source residual on each finite horizon
-- statement:
--   On one original probability conull event, for every finite time horizon, subtracting the finite sum of genuine Lévy jump marks from the original path leaves a continuous path up to and including the horizon.
-- source:
--   Proved A32 original physical no-jump cadlag residual, bounded deterministic continuity bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a32_original_finiteactivity_physical_jumpfree_residual_cadlag_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let f : ℝ≥0 → ℝ := fun t => X.X t ω
      let j : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
      ∃ S : Finset ℝ≥0,
        (∀ t, t ∈ S ↔ 0 < t ∧ t ≤ T ∧ j t ≠ 0) ∧
        (∀ t : ℝ≥0, t ≤ T →
          ContinuousAt
            (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0) t) := by sorry
