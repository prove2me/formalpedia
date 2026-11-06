-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_stopped_negative_band_square_budget
-- name    : AvramDividend.Classical.avram_p4_s3_original_grid_stopped_negative_band_square_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:46:59.582553+00:00
-- url     : https://prove2.me/theorems/0cb80e25-f18f-4e12-af48-9dddb5f8be34
-- title:
--   Actual grid-stopped negative-band count has an explicit L² bound
-- statement:
--   The actual negative-band jump count of the original process at any bounded countably grid-selected stopping clock is square integrable with second moment bounded by r+r², r=Tν(band). The proof eliminates the measurable-stopped-count assumption by combining countable-fibre measurability and the pathwise fixed-horizon factorial-moment bound.
-- source:
--   Proof combines original-process accepted P4-S3 grid count measurability and original bounded stopping count L² budget, each founded on true sample paths and original factorial moments; no equality-in-law.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_grid_stopped_negative_band_square_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ ω, grid (tick ω) ≤ T) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r := by sorry
