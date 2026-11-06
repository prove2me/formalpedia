-- Prove2me | Theorems.Thm_BianchiIX_partial_core_connection_wall_budget
-- name    : BianchiIX.partial_core_connection_wall_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:27:26.782056+00:00
-- url     : https://prove2.me/theorems/3f48e4f4-e2dd-4d66-a4ed-0dc8b991e5fc
-- title:
--   Absorbing logarithmic radial losses with strong-wall decay
-- statement:
--   Suppose $r>0$, $K\geq0$, $k\geq6$,
--   $1/k\leq Kr$, $k\leq K/r$, $A,B,U,u,w\geq0$,
--   $u\leq Ue^{-k/12}$, $w\leq P$, and
--   $$|du|\leq u[K/r+A\log(4k)/r^2],\quad
--   |dw|\leq w[K/r+B\log(4k)].$$
--   Then
--   $$u\leq U,\quad r|du|\leq K(1+576A)U,\quad
--   r|dw|\leq K(1+B)P.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/PartialCoreConnectionBudget.lean#L7-L56

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.partial_core_connection_wall_budget {r K k A B U P u w du dw : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hk : 6 ≤ k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (_hu : 0 ≤ u) (hw : 0 ≤ w)
    (hdec : u ≤ U * Real.exp (-k / 12)) (hweak : w ≤ P)
    (hdu : |du| ≤ u * (K / r + A * Real.log (4 * k) / r ^ 2))
    (hdw : |dw| ≤ w * (K / r + B * Real.log (4 * k))) :
    u ≤ U ∧ r * |du| ≤ K * (1 + 576 * A) * U ∧
      r * |dw| ≤ K * (1 + B) * P := by sorry
