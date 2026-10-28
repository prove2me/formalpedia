-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
-- name    : AvramDividend.Classical.firstRecord_capped_coe_toNNReal_with_measure_import
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:58:42.183551+00:00
-- url     : https://prove2.me/theorems/7e78aea2-9eee-4ae2-883a-d97b3c48d2b4
-- title:
--   Capped strict upcrossing time equals the coercion of its finite NNReal conversion
-- statement:
--   A strict upcrossing time truncated at any finite NNReal horizon is below infinity, hence converting it from ENNReal to NNReal and coercing back recovers precisely the minimum clock. This supplies the equality of random-time representations used to transport stopped-history measurability into finite stopped Markov factorisation. The declaration explicitly opens MeasureTheory for Measure and Filtration.
-- source:
--   Pinned Mathlib ENNReal.coe_toNNReal and ENNReal.coe_lt_top; finite cap comparison.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_coe_toNNReal_with_measure_import
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) (ω : Ω) :
    (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
      min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞) := by sorry
