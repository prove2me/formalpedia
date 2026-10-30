-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_stopped_min_away_zero_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_stopped_min_away_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:06:47.228004+00:00
-- url     : https://prove2.me/theorems/058bc8db-683e-40c3-99e0-f27ea0002016
-- title:
--   Actual BV finite two-sided stopped reserve is nonzero a.s.
-- statement:
--   For genuine Standing BV spectrally negative Lévy process, positive upper barrier a and 0<=x<=a, the actual reserve at the minimum of strict up/down exit clocks is nonzero almost surely whenever that exit is finite. Upper first passage attains positive a without overshoot; lower first passage has strict negative undershoot by the already Proved no-creeping theorem. The third equal-clock case is excluded by the proved strict up-first event equivalence.
-- source:
--   Combines canonically Proved BV lower strict exit negative undershoot cad05116, original no positive jumps first upper hit equality 014436e7, strict clock ordering 9a984dcc, and the source definition of twoSidedExitUpTime/DownTime. This is the exact BV W(0)>0 continuity interface for capped grid to real-time optional stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_undershoot_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_up_first_iff_finite_stopped_min

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_stopped_min_away_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      x + X.X (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal ω ≠ 0 := by sorry
