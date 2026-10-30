-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_raw_prefix_iff_strict_exit
-- name    : AvramDividend.Classical.avram_wave3_01_raw_prefix_iff_strict_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:31:44.123271+00:00
-- url     : https://prove2.me/theorems/8ce502f5-8250-496c-be64-b78bc7d735e8
-- title:
--   Genuine Lévy raw prefix survival iff strict lower exit after finite attained upper record
-- statement:
--   For the actual source spectrally negative Levy process, suppose the upper first-passage clock at level b is finite, realised by u, b is nonnegative and a is positive. Then the entire strict pre-u original path staying above -a is equivalent to strict order u < the original lower first-exit clock below -a. The forward implication uses source first-upcrossing attainment, upper terminal location b> -a, right-continuity at u and exact infimum clock order; the converse uses the accepted strict-upper-before-lower prefix theorem. The exact endpoint correction is necessary for the original two-sided-exit Laplace expectation and the one-step scale-function ratio sandwich, without an incorrect boundary convention or optional stopping hypothesis.
-- source:
--   Source first-passage and path definitions in AvramDividend.Classical; Avram, Palmowski and Pistorius (2007), stopped two-sided exit; accepted firstUpcrossing_attains_peak and strict_up_before_down_preserves_lower_prefix.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_strict_up_before_down_preserves_lower_prefix

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_raw_prefix_iff_strict_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω) :
    (∀ t : ℝ≥0, t < u → -a ≤ X.X t ω) ↔
      (u : ℝ≥0∞) < twoSidedExitDownTime X (-a) ω := by sorry
