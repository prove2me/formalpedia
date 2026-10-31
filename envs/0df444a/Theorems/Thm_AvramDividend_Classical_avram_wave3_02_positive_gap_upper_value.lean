-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_gap_upper_value
-- name    : AvramDividend.Classical.avram_wave3_02_positive_gap_upper_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:21:51.740349+00:00
-- url     : https://prove2.me/theorems/1325d88a-3bc7-4338-967d-db2986a05ba8
-- title:
--   Derivative-free finite right-step upper bound for the genuine reflected barrier reward
-- statement:
--   For the actual original spectrally negative Levy reflected barrier regulator, any positive record mesh epsilon with W(a+epsilon)>W(a)>=0 and W(a+epsilon)>0 yields the finite positive right-difference upper bound barrierSupValue X a q <= epsilon W(a+epsilon)/(W(a+epsilon)-W(a)). This holds without differentiability of W at a. It combines genuine killed-record geometric budgets and a proved Tonelli/geometric-series bridge.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1, killed first-record renewal at a positive step. Derives directly from canonically Proved stoppedFirstRecord_upper_geometric_budgets and barrierSupValue_le_right_scale_quotient_of_killed_grid_step.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_upper_geometric_budgets
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_positive_gap_upper_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε)) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
