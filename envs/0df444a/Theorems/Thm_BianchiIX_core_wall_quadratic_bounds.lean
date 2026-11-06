-- Prove2me | Theorems.Thm_BianchiIX_core_wall_quadratic_bounds
-- name    : BianchiIX.core_wall_quadratic_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:26:39.949705+00:00
-- url     : https://prove2.me/theorems/9f458946-c22b-4b00-b7ea-dd7ee0df0604
-- title:
--   Quadratic wall products retain the strong amplitude and weak square
-- statement:
--   For real $\mu,u,w$ with $0\leq u,w\leq\mu$,
--   $$|u-w|\,|u-2w|\leq4\mu u+2w^2,$$
--   $$|u-w|\,|3w-u|\leq5\mu u+3w^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreAmplitudeCoefficients.lean#L7-L28

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.core_wall_quadratic_bounds {m u w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m) :
    |u - w| * |u - 2 * w| ≤ 4 * m * u + 2 * w ^ 2 ∧
    |u - w| * |3 * w - u| ≤ 5 * m * u + 3 * w ^ 2 := by sorry
