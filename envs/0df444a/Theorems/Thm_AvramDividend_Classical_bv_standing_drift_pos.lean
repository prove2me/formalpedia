-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
-- name    : AvramDividend.Classical.bv_standing_drift_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:50:59.651497+00:00
-- url     : https://prove2.me/theorems/0432f641-b22a-4ba0-b92e-6972ea7a1908
-- title:
--   Positive drift under bounded variation and nonmonotone path standing assumptions
-- statement:
--   Under the exact Avram standing assumption excluding processes with monotone paths, a bounded-variation spectrally negative Lévy process must have strictly positive drift and nonzero Lévy measure. This isolates a purely logical consequence needed in the bounded-variation branch of the scale-function positivity proof.
-- source:
--   Exact definitions Standing := not HasMonotonePaths and HasMonotonePaths := BoundedVariation and (drift≤0 or ν=0). Uses excluded-middle linear order only; no stochastic theorem or unproved process asymptotics.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem bv_standing_drift_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hstanding : X.Standing) (hBV : X.BoundedVariation) :
    0 < X.drift ∧ X.ν ≠ 0 := by
  sorry
end AvramDividend.Classical
