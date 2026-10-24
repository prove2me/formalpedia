-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_exit_ratio_continuousAt_upper_barrier
-- name    : AvramDividend.Classical.chat04_scale_exit_ratio_continuousAt_upper_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:42:49.878514+00:00
-- url     : https://prove2.me/theorems/b8b7294b-e3a7-4d83-82d3-06cb40545a8b
-- title:
--   Scale-function exit ratio is continuous in the positive upper barrier
-- statement:
--   For a strictly positive upper barrier a, the q-scale exit factor W(x)/W(b) varies continuously with the barrier level b at a. The numerator is constant; scale continuity holds away from zero, and strict q-scale positivity under Standing makes the denominator nonvanishing. This is a barrier perturbation lemma for valuation and scale comparison, independent of the unproved stochastic exit identity.
-- source:
--   Proved continuity of W away from zero and strict positivity of W on the positive axis, combined with continuity of division.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_exit_ratio_continuousAt_upper_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a : ℝ) (ha : 0 < a) :
    ContinuousAt (fun b : ℝ => W x / W b) a := by sorry
