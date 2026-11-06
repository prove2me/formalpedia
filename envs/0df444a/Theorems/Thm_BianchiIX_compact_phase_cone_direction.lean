-- Prove2me | Theorems.Thm_BianchiIX_compact_phase_cone_direction
-- name    : BianchiIX.compact_phase_cone_direction
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:51:18.269582+00:00
-- url     : https://prove2.me/theorems/719bc6f7-6045-472b-9bb6-3260a3b5eac0
-- title:
--   Compact phase derivative bounds control every square-root cone direction
-- statement:
--   Let $J:\mathbb R^3\to\mathbb R$ be linear, $C\geq0$,
--   $k\geq2$, and $0\leq x,y\leq1$. Suppose
--   $$|Je_0-1|\leq C(x+y^2),\qquad |Je_1+2/k|+|Je_2|\leq C(x+y).$$
--   For every $v$ with $v_0=1$, $|v_1|\leq\sqrt x$, and $|v_2|\leq\sqrt y$,
--   $$|Jv-1|\leq(4C+1)(\sqrt x+y\sqrt y).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactPhaseCone.lean#L10-L57

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.compact_phase_cone_direction (J : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ)
    {C k x y : ℝ} (hC : 0 ≤ C) (hk : 2 ≤ k)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hv0 : v 0 = 1) (hv1 : |v 1| ≤ Real.sqrt x) (hv2 : |v 2| ≤ Real.sqrt y)
    (hJ0 : |J (Pi.single 0 1) - 1| ≤ C * (x + y ^ 2))
    (hJ12 : |J (Pi.single 1 1) + 2 / k| + |J (Pi.single 2 1)| ≤ C * (x + y)) :
    |J v - 1| ≤ (4 * C + 1) * (Real.sqrt x + y * Real.sqrt y) := by sorry
