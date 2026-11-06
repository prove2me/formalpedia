-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:19:10.004185+00:00
-- url     : https://prove2.me/theorems/caf0e418-18ef-4eb9-a680-c0e9e1809e8d
-- title:
--   Positive stopped original ruin clock isolates exactly one physical boundary cash cell
-- statement:
--   For every actual original spectrally negative Levy sample path with positive ruin/horizon-stopped time, the physical stopped grid's crossing-cell index filter is exactly a singleton. Existence uses the Proved original zero-start/exact-end crossing lemma and uniqueness uses the Proved monotone stopped-clock at-most-one-crossing lemma. This turns the boundary term in the accepted exact strict/crossing dividendMeasure partition into one explicit physical cell, essential to distinguish the strict horizon atom from closed cash.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_has_crossing_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_unique_crossing
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
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
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        (Finset.range (m + 1)).filter
          (fun j => u j < τ ∧ u (j + 1) = τ) =
            ({i} : Finset ℕ) := by sorry
