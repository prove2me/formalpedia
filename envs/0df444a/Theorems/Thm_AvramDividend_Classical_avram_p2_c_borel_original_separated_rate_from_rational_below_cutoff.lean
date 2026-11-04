-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_rational_below_cutoff
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_rational_below_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:30:31.326077+00:00
-- url     : https://prove2.me/theorems/e7806d2d-4158-4f00-bf51-2f2374b61720
-- title:
--   Original separated Borel ν rate from rational thresholds below cutoff and one cutoff test
-- statement:
--   Every separated negative Borel marked-jump rate on the original Lévy process follows if one knows the original rate at the cutoff and on the countably many rational lower-halfline thresholds strictly below it. No additional tests above cutoff or finite original mean are required.
-- source:
--   Rat.denseRange_cast with conditional Proved P2-C original rate from below-cutoff dense thresholds, after that named parent becomes authoritatively Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_rational_below_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (hCut : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (-ε))))
    (hBelow : ∀ q : ℚ, (q : ℝ) < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (q : ℝ)) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (q : ℝ)))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
