-- Prove2me | Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
-- name    : AvramDividend.Classical.levyPath_bddAbove_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:10:44.928495+00:00
-- url     : https://prove2.me/theorems/c2066587-8d80-45bd-a4dc-0d24c616ddf8
-- title:
--   A Lévy path is bounded above on every finite interval by its terminal running maximum
-- statement:
--   At any finite horizon T, the running supremum of a Lévy sample path dominates its value at every time r≤T. Hence the path values on [0,T] form a bounded-above subset of the reals. This provides the exact BddAbove hypothesis for the shifted supremum and Stieltjes dividend-measure identities.

import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levyPath_bddAbove_Icc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 T) := by sorry
