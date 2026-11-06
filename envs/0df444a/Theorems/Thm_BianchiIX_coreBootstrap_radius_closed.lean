-- Prove2me | Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
-- name    : BianchiIX.coreBootstrap_radius_closed
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:31:48.952494+00:00
-- url     : https://prove2.me/theorems/75b29a39-9bab-4f49-b42f-691ca666ee11
-- title:
--   The closed energy band controls the core radius
-- statement:
--   If $k\geq6$, $r\geq0$, and $|r^2-k^2|\leq1/8$, then
--   $$99k/100\leq r\leq101k/100.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreRadialBounds.lean#L7-L16

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

theorem BianchiIX.coreBootstrap_radius_closed {k r : ℝ} (hk : 6 ≤ k) (hr : 0 ≤ r)
    (he : |r ^ 2 - k ^ 2| ≤ 1 / 8) : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k := by sorry
