-- Prove2me | Theorems.Thm_BianchiIX_core_radius_budget
-- name    : BianchiIX.core_radius_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:32:03.928084+00:00
-- url     : https://prove2.me/theorems/168bd72b-c2f3-4b09-aa38-92c3de1ccf26
-- title:
--   The integrated radial contributions fit a uniform budget
-- statement:
--   Suppose $k\geq6$ and $0\leq u,w\leq1/(10000k)$. Then
--   $$\frac{14u/k+4uw/k+3u^2/k^2+4w^2/k}{999/1000}
--   \leq\frac{16}{k}(u+w^2).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreRadialBounds.lean#L51-L66

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

theorem BianchiIX.core_radius_budget {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (14 * u / k + 4 * u * w / k + 3 * u ^ 2 / k ^ 2 + 4 * w ^ 2 / k) / (999 / 1000) ≤
      16 / k * (u + w ^ 2) := by sorry
