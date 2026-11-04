-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_canonical_residual_zero_at_origin
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_zero_at_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:29:51.004085+00:00
-- url     : https://prove2.me/theorems/63f6215d-7deb-4535-83f5-a794ad532c9c
-- title:
--   Original Levy drift-minus-jump residual starts at zero without extra process hypotheses
-- statement:
--   The original-source residual t*X.drift-X_t minus the actual downward jump total over (0,t] vanishes exactly at t=0, pathwise, relying on the source X_0=0 axiom and the empty time interval. No BV assumption, Poisson model, or compensator required.
-- source:
--   Source SpectrallyNegativeLevy.X_zero and simplification of empty interval 0<u≤0; original paths and drift coefficient, no helper representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original source residual is zero at the initial time. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_zero_at_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ((0 : ℝ) * X.drift - X.X 0 ω) -
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ (0 : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal = 0 := by sorry
