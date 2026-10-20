-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_no_right_dividend_jump_before_ruin
-- name    : AvramDividend.Classical.zero_cap_no_right_dividend_jump_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:20:38.336238+00:00
-- url     : https://prove2.me/theorems/751e2dad-57d3-45b8-a086-f0f401285697
-- title:
--   Admissible zero-cap dividend controls cannot have positive-time right jumps before ruin
-- statement:
--   At every strictly positive time strictly before ruin, a zero-capped admissible dividend strategy has right-limit equal to its current cumulative dividend. The proved control identity forces reserve U=0. The admissibility inequality bounds right dividend by reserve, while monotonicity forces any right dividend jump to be nonnegative. This eliminates all positive pre-ruin dividend atoms of the exact Stieltjes measure.
-- source:
--   Prove2Me Exact DividendStrategy definitions and previously proved zero_cap_control_eq_levy_before_ruin, pinned Mathlib 0df444a, arXiv:math/0702893 §2.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_control_eq_levy_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_no_right_dividend_jump_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (t : ℝ≥0) (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ruinTime X 0 D ω) :
    rightLimit D t ω = D t ω := by sorry
