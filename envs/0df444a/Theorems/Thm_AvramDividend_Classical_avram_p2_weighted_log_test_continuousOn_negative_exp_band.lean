-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_weighted_log_test_continuousOn_negative_exp_band
-- name    : AvramDividend.Classical.avram_p2_weighted_log_test_continuousOn_negative_exp_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:53:24.797106+00:00
-- url     : https://prove2.me/theorems/2925903e-ce15-4d9b-a6a9-b2cfa348eeeb
-- title:
--   Continuity of the weighted logarithmic test transform on the strict negative-jump exponential band
-- statement:
--   For any continuous real test f, the inverse exponential coordinate transform z↦f(log z)/(z−1)^4 is continuous on the open interval (0,1). This gives the interior continuity needed to transfer weak convergence of the actual original process's fourth-weighted exponential pushforward to continuous tests on strictly negative original marks. Only the strict interior is asserted; endpoint extension still requires compact support separated from zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_weighted_log_test_continuousOn_negative_exp_band
    (f : ℝ → ℝ) (hf : Continuous f) :
    ContinuousOn
      (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4)
      (Ioo (0 : ℝ) 1) := by sorry
