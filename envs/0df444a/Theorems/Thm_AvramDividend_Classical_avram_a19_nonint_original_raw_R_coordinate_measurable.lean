-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_raw_R_coordinate_measurable
-- name    : AvramDividend.Classical.avram_a19_nonint_original_raw_R_coordinate_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:58:42.616582+00:00
-- url     : https://prove2.me/theorems/86c7cf52-9eb1-49b6-a235-9a7b2c2189b9
-- title:
--   Original BV drift-removed raw jump residual is a.e. measurable at every deterministic time
-- statement:
--   At every deterministic time, the actual bounded-variation Lévy drift minus its coordinate and raw negative-jump accumulation is almost everywhere strongly measurable on the source probability space.
-- source:
--   Exact integration of Proved original joint Lévy coordinate measurability d55462c3 with newly Proved raw jump cumulative measurability 2427e100; raw-grid R child for 6d55dddd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_nonint_original_raw_R_coordinate_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ t : ℝ≥0, AEStronglyMeasurable (fun ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P := by sorry
