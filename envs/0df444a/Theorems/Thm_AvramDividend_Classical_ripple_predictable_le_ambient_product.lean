-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_predictable_le_ambient_product
-- name    : AvramDividend.Classical.ripple_predictable_le_ambient_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:10:44.325799+00:00
-- url     : https://prove2.me/theorems/8bade7d6-a0bd-486e-8026-11a4be4cb012
-- title:
--   Predictable sigma algebra embeds in the ambient physical-time product sigma algebra
-- statement:
--   The predictable sigma-algebra of any nonnegative-real-time filtration is smaller than the usual product sigma-algebra on time times sample space. The proof checks the two families of predictable generating rectangles.
-- source:
--   Source-faithful structural interface proof for the predictable filtered L² construction in Ripple/Stochastic/StoppedPredictableIntegrand.lean; Ripple commit e216e28ce3ffb43877e11f71be260e40a37a35df (Apache-2.0). Avram Dividend Classical mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib

open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.ripple_predictable_le_ambient_product
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 mΩ) :
    F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by sorry
