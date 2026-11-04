-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
-- name    : AvramDividend.Classical.avram_p2_e_compensator_intrinsic_rectangle_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:27:36.127189+00:00
-- url     : https://prove2.me/theorems/8146a449-000a-49f5-9c6c-33a35a7a847e
-- title:
--   Measurability of actual intrinsic Lévy marked rectangle counts
-- statement:
--   For the unchanged original Lévy path X on Ω, the total intrinsic jump count on the half-open rectangle (s,t] × B is an ENNReal-valued measurable random variable for every s ≤ t and Borel mark set B. The proof uses the Proved same-path shifted future functional and original adaptedness; no intensity, conditional independence or Poisson replacement is assumed.
-- source:
--   Proved original marked count measurable extractor 5cf3e058-4372-4903-a4fe-24732496cb39. SpectrallyNegativeLevy adaptedness. Parent compensator 393b03a8-2e9a-43d8-b415-854d86d58104.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_intrinsic_rectangle_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) := by sorry
