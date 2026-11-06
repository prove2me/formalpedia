-- Prove2me | Theorems.Thm_BianchiIX_core_cone_weighted_size
-- name    : BianchiIX.core_cone_weighted_size
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T03:27:20.47268+00:00
-- url     : https://prove2.me/theorems/e760add5-2ff3-4e09-8c34-cf313f706f27
-- title:
--   Small walls control the weighted size of square-root cone directions
-- statement:
--   Let $k\geq6$, $0\leq\varepsilon\leq1$,
--   $0\leq u,w\leq\varepsilon/k$, $|a|\leq\sqrt u$, and
--   $|b|\leq\sqrt w$. Set $Q=1+k|a|+|b|$. Then
--   $$\sqrt u\,Q\leq3\sqrt\varepsilon,\qquad
--   \sqrt w\,Q\leq3\sqrt\varepsilon,\qquad
--   \sqrt u+(u+w)Q\leq7\sqrt\varepsilon.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreConeSize.lean#L8-L67

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

theorem BianchiIX.core_cone_weighted_size {k ε u w a b : ℝ} (hk : 6 ≤ k)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (ha : |a| ≤ Real.sqrt u) (hb : |b| ≤ Real.sqrt w) :
    let Q := 1 + k * |a| + |b|
    Real.sqrt u * Q ≤ 3 * Real.sqrt ε ∧ Real.sqrt w * Q ≤ 3 * Real.sqrt ε ∧
      Real.sqrt u + (u + w) * Q ≤ 7 * Real.sqrt ε := by sorry
