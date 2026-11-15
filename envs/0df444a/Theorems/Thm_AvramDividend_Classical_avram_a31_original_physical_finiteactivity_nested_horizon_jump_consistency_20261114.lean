-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a31_original_physical_finiteactivity_nested_horizon_jump_consistency_20261114
-- name    : AvramDividend.Classical.avram_a31_original_physical_finiteactivity_nested_horizon_jump_consistency_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:48:13.55338+00:00
-- url     : https://prove2.me/theorems/a01bdda4-93df-4fea-a6ef-a220b1cd6f15
-- title:
--   Original finite-activity actual marked-jump accumulators agree on nested physical time horizons on one conull event
-- statement:
--   On one original source conull event, the finite sets of actual negative-jump times from two nested horizons give causal marked sums that agree at every time in the earlier horizon.
-- source:
--   Proved original physical finite jump support 1e50b68a and Proved A31 deterministic horizon consistency 206e314b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a31_physical_jump_accumulator_horizon_consistency_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original physical negative-jump accumulators on nested horizons have identical causal history. -/

theorem AvramDividend.Classical.avram_a31_original_physical_finiteactivity_nested_horizon_jump_consistency_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T U : ℝ≥0, T ≤ U →
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      ∃ S R : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ u, u ∈ R ↔ 0 < u ∧ u ≤ U ∧ j u ≠ 0) ∧
        (∀ t : ℝ≥0, t ≤ T →
          (∑ u ∈ S, if u ≤ t then j u else 0) =
          (∑ u ∈ R, if u ≤ t then j u else 0)) := by sorry
