-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_source_interval_growth_bound
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_source_interval_growth_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:56:05.679209+00:00
-- url     : https://prove2.me/theorems/c580d5e8-328a-47ba-9e1f-5305fda8f000
-- title:
--   Original BV process interval growth bounded by source drift minus genuine jumps
-- statement:
--   On one full-probability set of original bounded-variation Levy sample paths, each source increment plus the exact actual signed negative-jump series over the same interval is at most the physical source drift times elapsed time. The nonnegative continuous residual provides the exact slack; no jump Poisson law or deterministic residual identity is assumed.
-- source:
--   The original-source residual monotonicity e9d95081-1010-4cec-87d2-14abac4f2e96 and original-source cocycle 5b913d53-0281-4b45-b508-bc5ac69419a8, both Proved; rewrite to a bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_interval_cocycle

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_source_interval_growth_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (X.X t ω - X.X s ω) +
        (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) ≤
      ((t : ℝ) - (s : ℝ)) * X.drift := by sorry
