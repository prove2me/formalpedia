-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_compensated_jump_zero_of_stays_above_cstar
-- name    : AvramDividend.Classical.vcstar_compensated_jump_zero_of_stays_above_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:29:16.503987+00:00
-- url     : https://prove2.me/theorems/06b53a89-4eae-4c7e-a395-19f6cb7b6673
-- title:
--   Compensated Lévy jump contribution vanishes above the optimal barrier unless the jump crosses it
-- statement:
--   For a reserve x strictly above the optimal dividend barrier cstar, the candidate dividend value is affine with unit slope. Consequently, any jump z whose endpoint x+z also remains strictly above cstar contributes exactly zero to the compensated Lévy generator integrand. This identity isolates the stochastic generator difficulty to jumps crossing the barrier and can simplify integrability and generator residual estimates without requiring global scale-function smoothness.
-- source:
--   Canonical proved affine continuation ee11c526-1dfc-4622-86fb-5de4518a7c45 and affine derivative 4098a584-9c09-4437-b71f-5590221db9ab.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_compensated_jump_zero_of_stays_above_cstar
    (W : ℝ → ℝ) (x z : ℝ)
    (hx : (cstar W).toReal < x)
    (hstay : (cstar W).toReal < x + z) :
    vcstar W (x + z) - vcstar W x -
      z * deriv (vcstar W) x = 0 := by sorry
