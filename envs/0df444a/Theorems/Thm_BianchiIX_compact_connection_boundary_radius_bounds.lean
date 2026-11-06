-- Prove2me | Theorems.Thm_BianchiIX_compact_connection_boundary_radius_bounds
-- name    : BianchiIX.compact_connection_boundary_radius_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T05:39:29.188538+00:00
-- url     : https://prove2.me/theorems/fdcc487a-a729-4024-b547-ef990f1b3192
-- title:
--   The reflected boundary radius lies in an explicit overlap interval
-- statement:
--   If $31/8\leq K\leq6$ and $0<\eta\leq1/8$, then
--   $$15/8-8\eta^2/31\leq\sqrt{K^2-\eta^2}-2\leq4-\eta^2/12.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CompactConnectionRadius.lean#L7-L31

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.compact_connection_boundary_radius_bounds {K η : ℝ}
    (hK : 31 / 8 ≤ K ∧ K ≤ 6) (hη : 0 < η ∧ η ≤ 1 / 8) :
    15 / 8 - 8 * η ^ 2 / 31 ≤ Real.sqrt (K ^ 2 - η ^ 2) - 2 ∧
      Real.sqrt (K ^ 2 - η ^ 2) - 2 ≤ 4 - η ^ 2 / 12 := by sorry
