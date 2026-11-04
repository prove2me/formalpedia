-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_rational_truncated_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_rational_truncated_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:09:37.070849+00:00
-- url     : https://prove2.me/theorems/e271a938-4d63-4e9f-8ce7-5ea0c0af97b7
-- title:
--   Separated original marked ν rate from rational cutoff-truncated halfline tests
-- statement:
--   For a fixed strictly negative mark cutoff and any original Lévy time interval, exact ν rates on the countable family Iic(q)∩Iic(-ε), q rational, suffice to prove exact original intrinsic jump intensity on every Borel mark set below the cutoff.
-- source:
--   P2-C original separated dense threshold extension f5b475db plus pinned Mathlib Rat.denseRange_cast, with no assumption of the unrestricted source rate or a compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_dense_tests

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_rational_truncated_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (hTests : ∀ q : ℚ,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic (q : ℝ) ∩ Iic (-ε))) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (q : ℝ) ∩ Iic (-ε)))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
