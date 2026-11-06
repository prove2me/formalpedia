-- Prove2me | Theorems.Thm_BianchiIX_core_cone_radius_size
-- name    : BianchiIX.core_cone_radius_size
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T03:27:20.732552+00:00
-- url     : https://prove2.me/theorems/a123b9cb-d788-4f89-b749-a173347e941c
-- title:
--   The radial cone error retains the actual incoming wall sum
-- statement:
--   Suppose $k\geq6$, $0\leq\varepsilon\leq1$,
--   $0\leq u,w\leq\varepsilon/k$, $|a|\leq\sqrt u$, and
--   $|b|\leq\sqrt w$. Then
--   $$\sqrt u+(u+w)(1+k|a|+|b|)\leq5\sqrt{u+w}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreConeRefinement.lean#L49-L79

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.core_cone_radius_size {k ε u w a b : ℝ} (hk : 6 ≤ k)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (ha : |a| ≤ Real.sqrt u) (hb : |b| ≤ Real.sqrt w) :
    Real.sqrt u + (u + w) * (1 + k * |a| + |b|) ≤ 5 * Real.sqrt (u + w) := by sorry
