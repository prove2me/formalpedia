-- Prove2me | Theorems.Thm_AvramDividend_Classical_standing_levy_regular_cases
-- name    : AvramDividend.Classical.standing_levy_regular_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T18:38:52.91142+00:00
-- url     : https://prove2.me/theorems/f5ce6b06-5f8c-4d02-a8d6-9930dcabd1a7
-- title:
--   Standing Lévy assumptions give the bounded-variation or unbounded-variation regularity split
-- statement:
--   Under Standing, either the process has bounded variation with strictly positive drift and absolutely continuous Lévy jump measure, or it has a strictly positive Gaussian component or infinitely many small jumps in total variation. The result is the exact case split needed for proving scale-function positivity and C1 regularity, directly from the mission's triplet assumptions.
-- source:
--   Avram, Palmowski and Pistorius, condition (3.3) and assumptions; Kuznetsov, Kyprianou and Rivero, scale function regularity case split

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The standing assumptions split the regularity analysis into
a positive-drift bounded-variation process with atomless jumps,
or Gaussian/infinite-small-jump variation. -/
theorem standing_levy_regular_cases {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    (X.BoundedVariation ∧ 0 < X.drift ∧ X.ν ≪ (volume : Measure ℝ)) ∨
      (0 < X.σ ∨
        (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) := by
  sorry

end AvramDividend.Classical
