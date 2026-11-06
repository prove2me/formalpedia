-- Prove2me | Theorems.Thm_BianchiIX_core_radius_energy_improvement
-- name    : BianchiIX.core_radius_energy_improvement
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:31:50.884817+00:00
-- url     : https://prove2.me/theorems/bd83c2b6-d626-47d1-967e-5f8b0f6b4f58
-- title:
--   A small radial drift strictly improves the energy band
-- statement:
--   Assume $k\geq6$, $0\leq r\leq101k/100$,
--   $0\leq u,w\leq1/(10000k)$, and
--   $|r-k|\leq16(u+w^2)/k$. Then
--   $$|r^2-k^2|<1/16.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreRadialBounds.lean#L68-L84

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

theorem BianchiIX.core_radius_energy_improvement {k r u w : ℝ} (hk : 6 ≤ k)
    (hr : 0 ≤ r) (hrhi : r ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (hR : |r - k| ≤ 16 / k * (u + w ^ 2)) : |r ^ 2 - k ^ 2| < 1 / 16 := by sorry
