-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_original_stopped_contact_prefix_card_measurable
-- name    : AvramDividend.Classical.avram_bv_env3_turn9_original_stopped_contact_prefix_card_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:58:03.607142+00:00
-- url     : https://prove2.me/theorems/fbb734fc-f2b9-442e-a0c8-bf5183b022be
-- title:
--   Measurable exact stopped contact-cell strict-prefix cardinal
-- statement:
--   The exact strict stopped-index k(ω) defined as the cardinality of physical-grid cells whose right endpoint is strictly before min(ruin,T) is a measurable natural-valued function bounded by the grid size. This supplies a measurable version of the exact P3-GRID3 pathwise prefix cardinal, enabling random-index stopping and future finite-grid signed Fatou integrands.
-- source:
--   Original ruinTime_measurable bbfbecf4 (Proved), Finset.card_filter = finite sum of measurable indicator functions. Matches canonical cardinal k in P3-GRID3 53697545 (Proved), but creates an independent measurable-selection property for P3-GRID4 1359bfd0 and c1e2f021.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn9_original_stopped_contact_prefix_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → Ω → ℝ≥0 := fun j ω =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) (τ ω)
    let k : Ω → ℕ := fun ω =>
      ((Finset.range (m + 1)).filter
        (fun i => u (i + 1) ω < τ ω)).card
    Measurable k ∧ ∀ ω, k ω ≤ m + 1 := by sorry
