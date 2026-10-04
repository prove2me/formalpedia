-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_measure_ac_on_positive
-- name    : AvramDividend.Classical.renewal_measure_ac_on_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:03:39.030591+00:00
-- url     : https://prove2.me/theorems/563ee480-72e9-405a-ac26-09db3ed399b7
-- title:
--   Renewal measure is absolutely continuous away from its atom at zero
-- statement:
--   Let κ and R be s-finite measures on the real line. Suppose κ is absolutely continuous with respect to Lebesgue measure and the renewal equation R=aδ0+b(R*κ) holds for nonnegative scalar coefficients a,b. Then the restriction of R to (0,∞) is absolutely continuous with respect to Lebesgue measure. This supplies the crucial density existence needed to establish positivity of the exponentially tilted BV scale-function renewal candidate, without first requiring C1 differentiability.
-- source:
--   Pinned Mathlib MeasureTheory.Group.Convolution theorem Measure.conv_absolutelyContinuous; measure restriction and absolutely continuous null-set formalism

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Any positive renewal measure with an absolutely continuous convolution
kernel has an absolutely continuous restriction away from its initial atom. -/
theorem renewal_measure_ac_on_positive (κ R : Measure ℝ) [SFinite κ] [SFinite R]
    (hκ : κ ≪ (volume : Measure ℝ))
    (a b : ℝ≥0∞)
    (hR : R = a • (Measure.dirac (0 : ℝ)) + b • (R ∗ κ)) :
    R.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) := by
  sorry

end AvramDividend.Classical
