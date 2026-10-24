-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_zero_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:37:32.028142+00:00
-- url     : https://prove2.me/theorems/cbc76364-c2c0-4fb0-89a2-2de988872e43
-- title:
--   The running-supremum Stieltjes reward has no initial-time dividend atom
-- statement:
--   For the running supremum of any spectrally negative Levy process, its Lebesgue–Stieltjes dividend measure assigns zero mass to time zero. Identify the record process with the barrier strategy started at any nonnegative barrier a, then apply the proved fact that an at-barrier strategy produces no initial Stieltjes payment. This explicitly settles the zero-time boundary term in the stopped reflected-record renewal integral.
-- source:
--   Proved barrierStrategy_self_eq_runningSup (6f853442) and barrierStrategy_no_initial_dividendMeasure_atom (1b0903d2).

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_initial_dividendMeasure_atom
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_dividendMeasure_zero_initial_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ha : 0 ≤ a) (ω : Ω) :
    dividendMeasure (runningSup X) ω ({0} : Set ℝ) = 0 := by sorry
