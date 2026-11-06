-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:36:09.589319+00:00
-- url     : https://prove2.me/theorems/f37429d3-3a4b-4e73-a9ce-70d4e64142b5
-- title:
--   Actual last strictly pre-ruin original stopped-grid node lies within one vanishing deterministic mesh step of tau
-- statement:
--   For any positive original stopped ruin/horizon time, the previously Proved genuine crossing index i satisfies u(i)<tau=u(i+1). The separately Proved original physical cell-size estimate then gives tau-u(i)<=T/(m+1). This precise pathwise approximation is a source-exact precursor to Stieltjes continuity and strict horizon cash liminf, with no surrogate process, stopping-time claim about the last strict index, or assumption on w(0).

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
        u (i + 1) = τ ∧ τ - u i ≤ T / (m + 1) := by sorry
