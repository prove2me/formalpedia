-- Prove2me | Theorems.Thm_BianchiIX_reciprocal_small_phase_bounds
-- name    : BianchiIX.reciprocal_small_phase_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:50:58.323195+00:00
-- url     : https://prove2.me/theorems/8846a090-e5b3-4f4d-8469-fbeb4cbd6984
-- title:
--   Inversion of a small positive phase has explicit value and radial-error bounds
-- statement:
--   Let $0<\alpha\leq1$, $A,b\geq0$, and $Ab\leq\alpha/4$.
--   If $|x-\alpha|+|p-1/2|\leq Ab$, then
--   $$x>0,\qquad x^{-2}\leq4\alpha^{-2},\qquad
--   |2/x-2/\alpha|\leq4Ab/\alpha^2,$$
--   $$|-2p/x^2+1/\alpha^2|\leq20Ab/\alpha^3.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ReciprocalPhaseStatistics.lean#L27-L75

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Notation

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.reciprocal_small_phase_bounds {α x p A b : ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hsmall : A * b ≤ α / 4) (herr : |x - α| + |p - 1 / 2| ≤ A * b) :
    0 < x ∧ 1 / x ^ 2 ≤ 4 / α ^ 2 ∧
      |2 / x - 2 / α| ≤ 4 * A * b / α ^ 2 ∧
      |-2 * p / x ^ 2 + 1 / α ^ 2| ≤ 20 * A * b / α ^ 3 := by sorry
