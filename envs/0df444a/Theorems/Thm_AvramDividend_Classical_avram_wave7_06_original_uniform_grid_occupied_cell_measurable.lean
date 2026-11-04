-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_uniform_grid_occupied_cell_measurable
-- name    : AvramDividend.Classical.avram_wave7_06_original_uniform_grid_occupied_cell_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:23:37.922333+00:00
-- url     : https://prove2.me/theorems/b42e2852-1053-4a2d-8528-a41da07b9aed
-- title:
--   All genuine negative-band uniform-grid cell indicators measurable from original X
-- statement:
--   For the exact source Lévy jump measure NX, every equal-width shifted cutoff-cell occupancy indicator is measurable on original Ω. Follows cellwise from the source occupied-cell measurability theorem, discharging the grid assembly hypothesis.
-- source:
--   W7-06 genuine original-filtration source uniform-grid measurability bridge. Imports only the exact predecessor original-cell measurable theorem bc862522, itself submitted and unconfirmed at authoring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_uniform_grid_occupied_cell_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (δ : ℝ≥0) (n m : ℕ) :
    ∀ i ∈ Finset.range m, Measurable
      (fun ω : Ω =>
        ({ω : Ω | NX ω
          (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
            Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
          (fun _ => (1 : ENNReal)) ω) := by sorry
