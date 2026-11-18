-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB47_upper_strip_occupation_exact_on_floor_path
-- name    : AvramDividend.Classical.avram_gbB47_upper_strip_occupation_exact_on_floor_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:21:05.583457+00:00
-- url     : https://prove2.me/theorems/11b492f8-7666-45c7-a191-57177b650014
-- title:
--   Positive upper-strip occupation is exactly the stopped horizon on a floor-preserving path
-- statement:
--   If the original reserve path is strictly above the band cutoff at every positive physical time before stopped horizon T, and T lies within the bounded observation horizon n, the actual real Lebesgue occupation indicator integrated over (0,n) is exactly T, provided the strip set is measurable. This gives the positive occupation term omitted by the disputed fixed-j original caplinear cash inequality.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB47_upper_strip_occupation_exact_on_floor_path
    (n T b : ℝ) (hT : 0 < T) (hTn : T ≤ n)
    (Y : ℝ → ℝ)
    (hY : ∀ t : ℝ, 0 < t → t < T → b < Y t)
    (hMeas : MeasurableSet {t : ℝ | t < T ∧ b < Y t}) :
    (∫ t in Ioo (0 : ℝ) n,
        if t < T ∧ b < Y t then (1 : ℝ) else 0 ∂volume) = T := by sorry
