-- Prove2me | Theorems.Thm_BianchiIX_connection_phase_radial_budget
-- name    : BianchiIX.connection_phase_radial_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:55:04.237173+00:00
-- url     : https://prove2.me/theorems/836e157f-cbc3-4367-be1e-567f29316fa7
-- title:
--   Connection phase columns preserve the radial wall amplitude budget
-- statement:
--   Let $r,\mu>0$, $K,M,A,B,U\geq0$, $0\leq P\leq1$,
--   $1/\mu\leq Kr$, $0\leq u\leq U$, and $0\leq w\leq P$. If
--   $$|v_0|\leq M/r^2,\qquad r|v_1|\leq AU,\qquad r|v_2|\leq BP,$$
--   then
--   $$\frac{50000|v_0|(u+w^2)}{\mu^2}
--   +\frac{50000|v_1|}{\mu}+\frac{50000|v_2|(u+w)}{\mu}
--   \leq50000(K^2M+KA+KB)(U+P^2).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/PartialCoreConnectionBudget.lean#L58-L95

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

theorem BianchiIX.connection_phase_radial_budget {r K M A B μ U P u w v0 v1 v2 : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : 0 < μ) (hi : 1 / μ ≤ K * r) (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ U) (hw : 0 ≤ w ∧ w ≤ P)
    (hv0 : |v0| ≤ M / r ^ 2) (hv1 : r * |v1| ≤ A * U) (hv2 : r * |v2| ≤ B * P) :
    |v0| * (50000 * (u + w ^ 2) / μ ^ 2) + |v1| * (50000 / μ) +
      |v2| * (50000 * (u + w) / μ) ≤
        50000 * (K ^ 2 * M + K * A + K * B) * (U + P ^ 2) := by sorry
