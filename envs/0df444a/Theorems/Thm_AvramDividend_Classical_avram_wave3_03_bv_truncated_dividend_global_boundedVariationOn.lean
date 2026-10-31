-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_truncated_dividend_global_boundedVariationOn
-- name    : AvramDividend.Classical.avram_wave3_03_bv_truncated_dividend_global_boundedVariationOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:49:53.646156+00:00
-- url     : https://prove2.me/theorems/396e09d1-acd0-4a4d-b71f-a4043be227ac
-- title:
--   Actual dividend path clipped after any finite horizon has global bounded variation, including continuous Stieltjes mass and initial right jump
-- statement:
--   Every path of the actual admissible left-continuous monotone cumulative dividend control, viewed on the entire real line through Real.toNNReal and frozen at horizon T, is globally bounded-variation. It is bounded between D(0)=0 and D(T) and monotone. This provides the global BV input for Mathlib's finite signed vector Stieltjes measure and integration by parts, retaining both non-atomic payment mass and the right payment at zero; no Poisson or countable-atoms hypothesis is used.
-- source:
--   Use IsDividendStrategy monotonicity and D 0=0, Real.toNNReal_mono, min_le_min, MonotoneOn.boundedVariationOn with |D(min(t.toNNReal,T))|≤D T. Pinned Mathlib.Topology.EMetricSpace.BoundedVariation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_truncated_dividend_global_boundedVariationOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    BoundedVariationOn
      (fun t : ℝ => D (min t.toNNReal T) ω) Set.univ := by sorry
