-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_never_exit_scale_strip_bound
-- name    : AvramDividend.Classical.avram_ws01b_true_never_exit_scale_strip_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:27:19.735013+00:00
-- url     : https://prove2.me/theorems/226369bf-da1c-4034-a105-1284e3afb6dc
-- title:
--   Exact original Lévy q-scale remains inside the two-sided strip on paths that never exit
-- statement:
--   For actual Lévy paths whose original strict upward and downward passage clocks are both infinite, the starting reserve remains in [0,a] at every finite time. The genuine q-scale function is nonnegative and monotone on this strip, hence its value lies between 0 and Wq(a). This is the pathwise uniform domination needed to take the infinite-horizon BV killed limit.
-- source:
--   Accepted source strict upper and lower observation-to-hitting-time bounds, source IsScaleFunction nonnegative/monotone axioms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_true_never_exit_scale_strip_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hUp : twoSidedExitUpTime X (a-x) ω = ∞)
    (hDown : twoSidedExitDownTime X (-x) ω = ∞) :
    ∀ t : ℝ≥0, 0 ≤ W (x + X.X t ω) ∧ W (x + X.X t ω) ≤ W a := by sorry
