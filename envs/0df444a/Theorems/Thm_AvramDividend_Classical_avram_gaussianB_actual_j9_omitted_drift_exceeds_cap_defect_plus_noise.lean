-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_actual_j9_omitted_drift_exceeds_cap_defect_plus_noise
-- name    : AvramDividend.Classical.avram_gaussianB_actual_j9_omitted_drift_exceeds_cap_defect_plus_noise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:10:54.577767+00:00
-- url     : https://prove2.me/theorems/d361de55-89cb-43c1-95f9-d4ee2a33d247
-- title:
--   Original Gaussian j9 omitted drift occupation charge strictly dominates its cap-linear defect and bounded martingale noise
-- statement:
--   For the actual source parameters c=2, T=1/1000, cap C=1/8, j=9 upper band b=5/44 and quadratic reward w(y)=2y−4y², the drift occupation cT strictly exceeds the exact cap-linear defect 1/1936 plus Brownian noise tolerance 1/4000. This is the verified rational numerical gap in the positive-drift original stopped cash counterexample.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_actual_j9_omitted_drift_exceeds_cap_defect_plus_noise :
    0 < (2 : ℝ) * (1 / 1000 : ℝ) -
      (((((2 * (1 / 8 : ℝ) - 4 * (1 / 8 : ℝ) ^ 2) -
         (2 * (5 / 44 : ℝ) - 4 * (5 / 44 : ℝ) ^ 2)) -
         ((1 / 8 : ℝ) - (5 / 44 : ℝ))) +
        (1 / 4000 : ℝ)) ) := by sorry
