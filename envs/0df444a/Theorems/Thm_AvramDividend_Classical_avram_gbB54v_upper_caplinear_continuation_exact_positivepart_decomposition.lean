-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54v_upper_caplinear_continuation_exact_positivepart_decomposition
-- name    : AvramDividend.Classical.avram_gbB54v_upper_caplinear_continuation_exact_positivepart_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:32:26.634119+00:00
-- url     : https://prove2.me/theorems/46bba94d-65bb-4157-bdf2-a513f64b4946
-- title:
--   Finite-cap slope-one extension equals slope-alpha continuation minus an exact positive-part kink
-- statement:
--   For any verification payoff w, cap b and real slope alpha, the upper affine slope-one extension equals the slope-alpha continuation minus (alpha-1) times the positive part of the distance above b. This is an exact algebraic decomposition without smoothness assumptions and isolates the sole downward-kink contribution for the original stopped Gaussian Itô-Tanaka source ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_gbB54v_upper_caplinear_continuation_exact_positivepart_decomposition
    (w : ℝ → ℝ) (b α z : ℝ) :
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let U : ℝ → ℝ := fun y => if y ≤ b then w y else w b + α * (y - b)
    V z = U z - (α - 1) * max (z - b) 0 := by sorry
