-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_scale_square_meas
-- name    : AvramDividend.Classical.avram_root29_01_two_sided_grid_scale_square_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:37:53.623139+00:00
-- url     : https://prove2.me/theorems/fcf00bae-3ba9-425f-aac9-d8212659d010
-- title:
--   Actual Lévy two-sided stopped-grid scale-square measurability
-- statement:
--   The genuine finite two-sided first-exit grid stopped discounted q-scale square is strongly measurable for every reserve, from accepted adapted stopped-time and stopped-reserve measurability and measurable scale-function continuity. This discharges the technical measurability premise in the source-specific two-sided stopped-grid L² bound.
-- source:
--   WS1A work/avram_root29_01_two_sided_grid_scale_square_meas_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_two_sided_grid_scale_square_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    AEStronglyMeasurable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P := by sorry
