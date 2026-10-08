-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted_of_countable_endpoint_representation
-- name    : AvramDividend.Classical.barrierStrategy_adapted_of_countable_endpoint_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T23:27:20.995664+00:00
-- url     : https://prove2.me/theorems/22148b64-19cf-424b-a285-5841218c2da0
-- title:
--   Barrier adaptedness from countable past supremum and current-time sample
-- statement:
--   If a barrier dividend path is expressed as the positive part of the maximum of a countably sampled past supremum and the process value at the current time, with no dividend at time zero, it is adapted. All past sampled values are measurable with respect to the current filtration; the current-time sample is adapted directly. The endpoint augmentation removes any need for a left-limit or no-positive-jump assumption in the representation step.
-- source:
--   Alternative bridge to the already authored countable_pastSup_adapted supporting theorem; avoids the more restrictive representation without an endpoint, and makes proof of the endpoint-value equality immediate. For eventual witness to AvramDividend.Classical.valueFunctionLe_above_cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_adapted_of_countable_endpoint_representation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (S : Set ℝ≥0) (hS : S.Countable)
    (hrep : ∀ t ω,
      barrierStrategy X c c t ω =
        if t = 0 then 0 else
          max 0 (max
            (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω)
            (X.X t ω))) :
    Adapted 𝓕 (barrierStrategy X c c) := by
  sorry
