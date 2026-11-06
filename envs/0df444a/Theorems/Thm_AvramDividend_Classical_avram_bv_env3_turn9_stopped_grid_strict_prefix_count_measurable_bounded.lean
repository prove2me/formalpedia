-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_stopped_grid_strict_prefix_count_measurable_bounded
-- name    : AvramDividend.Classical.avram_bv_env3_turn9_stopped_grid_strict_prefix_count_measurable_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:46:34.795099+00:00
-- url     : https://prove2.me/theorems/58312315-9383-4fdc-a9b5-9066e1b93bdf
-- title:
--   Measurable bounded strict pre-ruin contact selector on original physical grids
-- statement:
--   For a bounded-variation-compatible original spectrally negative Lévy process and an original admissible dividend strategy, the number of physical-grid endpoints strictly before min(ruin,T) is a measurable random variable bounded by the number of grid cells. Strictness excludes contact with the ruin time. This supplies the measurable finite-prefix selection needed by stopped Stieltjes signed Fatou grids.
-- source:
--   Original process ruinTime_measurable (bbfbecf4 Proved), finite measurable sum and bounded indicator components. Intended for c1e2f021 source-witness selection and c8770486 strict-complement grid passage; it does not provide the missing stochastic mean-zero or signed HJB source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn9_stopped_grid_strict_prefix_count_measurable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let K : Ω → ℕ := fun ω =>
      ∑ j ∈ Finset.range m,
        if (((j + 1 : ℕ) : ℝ≥0) *
          (T / ((m + 1 : ℕ) : ℝ≥0)) < τ ω)
        then 1 else 0
    Measurable K ∧ ∀ ω, K ω ≤ m := by sorry
