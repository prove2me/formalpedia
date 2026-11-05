-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_separated_negative_borel_levy_rate
-- name    : AvramDividend.Classical.avram_integration_original_unit_separated_negative_borel_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:50:50.638208+00:00
-- url     : https://prove2.me/theorems/57f57f42-8f99-4af8-81d5-555f54ff14c1
-- title:
--   Original intrinsic unit-horizon separated negative Borel Lévy rate
-- statement:
--   For the same original spectrally negative Lévy process and genuine intrinsic jump-count measure, the expected number of marks in a Borel set separated from zero during (0,1] equals the original triplet Lévy measure of that set. This is the unit-time determining-class rate identification, independent of all-horizon time scaling; it requires genuine compact-test-to-Borel identification and is not yet proved.
-- source:
--   Reduction target for canonical 34dbea70. Proved unconditional original time-scaling 5c2e21c1; Proved genuine original compact-negative test identity 2e2ebbae and original intrinsic marginal compact-test first moment c3a1882e. Remaining missing edge is measure identification for separated Borel bands.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_integration_original_unit_separated_negative_borel_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B := by sorry
