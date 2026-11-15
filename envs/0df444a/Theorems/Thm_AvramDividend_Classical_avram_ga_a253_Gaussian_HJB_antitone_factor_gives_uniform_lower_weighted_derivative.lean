-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a253_Gaussian_HJB_antitone_factor_gives_uniform_lower_weighted_derivative
-- name    : AvramDividend.Classical.avram_ga_a253_Gaussian_HJB_antitone_factor_gives_uniform_lower_weighted_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:48:36.025581+00:00
-- url     : https://prove2.me/theorems/dfd276b2-8e97-4c97-b548-72515e08f187
-- title:
--   Gaussian characteristic-root weighted antitone factor bounded below uniformly by negative fixed interior factor
-- statement:
--   For Gaussian HJB characteristic roots ordered lambdaMinus≤lambdaPlus and a positive reserve y≥0, the exponential multiplier exp((lambdaMinus-lambdaPlus)y) lies between zero and one. If the first-order HJB factor at y is no less than its fixed value gAtA at a, the weighted value is bounded below uniformly by minus the absolute value of gAtA. Combined with factor antitonicity a250 and the exact transformed derivative identity this gives an original Gaussian scalar upper bound near zero via a251, without evaluating the dividend candidate at zero.
-- source:
--   Positive-root ordering, exponential monotonicity, original Gaussian a250 antitone HJB factor and a251 uniform derivative-to-value bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a253_Gaussian_HJB_antitone_factor_gives_uniform_lower_weighted_derivative
    (lambdaPlus lambdaMinus y gAtA gAtY : ℝ)
    (hOrder : lambdaMinus ≤ lambdaPlus)
    (hy : 0 ≤ y)
    (hAnti : gAtA ≤ gAtY) :
    -|gAtA| ≤ Real.exp ((lambdaMinus-lambdaPlus)*y)*gAtY := by sorry
