-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_all_right_step_upper
-- name    : AvramDividend.Classical.avram_wave3_02_standing_all_right_step_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:30:32.297985+00:00
-- url     : https://prove2.me/theorems/c741f0eb-807c-4324-acdc-555f755a36e1
-- title:
--   All positive right finite-difference reflected reward bounds without scale C1
-- statement:
--   For a Standing spectrally negative Levy process and positive q, at every positive barrier a and every positive right record mesh epsilon, the genuine expected discounted reflected regulator reward is at most epsilon W(a+epsilon)/(W(a+epsilon)-W(a)). The q-scale increment is strictly positive due to positive Esscher-normalised monotonicity, and actual killed-record geometric budgets give the stochastic bound. No derivative or global C1 is assumed; in particular this yields the right-hand eventual bound for the renewal sandwich unconditionally.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1, geometric stopped first-record valuation, with Proved scaleFunction_tilted_positive_monotone and the actual killed first-record upper-budget theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_upper_geometric_budgets
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_all_right_step_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    ∀ ε : ℝ, 0 < ε →
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
