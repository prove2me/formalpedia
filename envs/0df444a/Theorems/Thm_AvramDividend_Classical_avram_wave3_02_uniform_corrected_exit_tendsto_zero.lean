-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_corrected_exit_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_corrected_exit_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:02:33.672597+00:00
-- url     : https://prove2.me/theorems/97f4b12f-c472-4d37-931c-bb8ab8a7e7c8
-- title:
--   Original discounted upper-exit reward before ruin vanishes uniformly on every bounded reserve range
-- statement:
--   For the original Standing spectrally negative Levy process at q>0, the genuine corrected discounted two-sided upward first exit before ruin converges uniformly to zero as the upper barrier tends to infinity, simultaneously across every nonnegative starting capital bounded by an arbitrary fixed R≥0, including x=0. The canonically Proved uniform exponential source exit bound provides an upper envelope exp(-φ(a-R-1)), which tends to zero under the order topology and continuous ENNReal.ofReal, and the original exit reward is always nonnegative. This is a stochastic source limit with no C1 and no false surrogate stopped time.
-- source:
--   Avram Palmowski Pistorius (2007), true two-sided discounted first exit; canonical uniform Esscher source exit upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_corrected_exit_exp_bound

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_corrected_exit_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun a : ℝ =>
      ⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        twoSidedExitExpectationCorrected X q a x)
      atTop (𝓝 (0 : ENNReal)) := by sorry
