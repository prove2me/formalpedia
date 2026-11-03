-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:22:53.77483+00:00
-- url     : https://prove2.me/theorems/8b9eb23c-245d-4e22-976b-8f584e3fdc1a
-- title:
--   Actual Lévy shifted future-increment path is coordinate-product measurable
-- statement:
--   For the exact original spectrally negative Lévy sample space, probability, filtration and process, the shifted future-increment path ω↦(t↦X(s+t,ω)−X(s,ω)) is measurable as a function into the real-valued coordinate product measurable space. This is needed to compose independent future-path extractors with original-process trajectories. No jump intensity or finite activity is asserted.
-- source:
--   The adapted original coordinates X.X t are globally measurable by filtration monotonicity. Subtraction of two original coordinates and measurable_pi_lambda give coordinate-product measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) := by sorry
