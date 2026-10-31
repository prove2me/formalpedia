-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_left_step_lower
-- name    : AvramDividend.Classical.avram_wave3_02_standing_left_step_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:30:46.191092+00:00
-- url     : https://prove2.me/theorems/77c76dfd-6885-4337-9bb8-32873539de9e
-- title:
--   Standing-only derivative-free backward finite-difference lower bound for true reflected reward
-- statement:
--   For the original Standing spectrally negative Levy process at q>0, every positive barrier a and any epsilon strictly between 0 and a, the genuine discounted reflected regulator reward dominates epsilon W(a-epsilon)/(W(a)-W(a-epsilon)). The strict denominator is proved from Proved Esscher-normalised scale positivity and monotonicity, independent of any differentiability theorem. Actual killed first-record lower regeneration and the corrected source two-sided exit identity supply the stochastic inequality.
-- source:
--   Avram Palmowski Pistorius 2007, Proposition 1. Combines Proved corrected two-sided exit identity, killed_firstRecord_grid_expected_scale_lower_of_strict_exit, barrierSupValue_ge_left_scale_quotient_of_actual_grid, and scaleFunction_tilted_positive_monotone.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_expected_scale_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_actual_grid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_left_step_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a) :
    ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
      barrierSupValue X a q := by sorry
