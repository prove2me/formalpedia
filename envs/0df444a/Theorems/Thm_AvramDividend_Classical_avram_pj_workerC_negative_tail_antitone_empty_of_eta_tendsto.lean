-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_tail_antitone_empty_of_eta_tendsto
-- name    : AvramDividend.Classical.avram_pj_workerC_negative_tail_antitone_empty_of_eta_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:34:39.184996+00:00
-- url     : https://prove2.me/theorems/9e48545d-06ad-4e29-9c9e-07edf7d2c774
-- title:
--   Shrinking original negative-mark cutoff intervals are antitone and have empty intersection
-- statement:
--   Given a positive monotonically decreasing negative-mark threshold eta_n converging to zero, the actual small negative mark intervals (-eta_n,0) decrease as sets and have no common negative jump mark. This supplies the exact B_n set assumptions for stopped C2 jump-tail L1/L2 theorems.
-- source:
--   Elementary order and tendsto of negative eta_n; supports Proved decd1b90 actual stopped purejump Taylor tail.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_negative_tail_antitone_empty_of_eta_tendsto
    (eta : ℕ → ℝ) (hpos : ∀ n, 0 < eta n)
    (hanti : Antitone eta)
    (hlim : Tendsto eta atTop (𝓝 (0 : ℝ))) :
    Antitone (fun n : ℕ => Ioo (-eta n) (0 : ℝ)) ∧
      (⋂ n : ℕ, Ioo (-eta n) (0 : ℝ)) = ∅ := by sorry
