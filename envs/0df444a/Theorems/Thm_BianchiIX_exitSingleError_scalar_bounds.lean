-- Prove2me | Theorems.Thm_BianchiIX_exitSingleError_scalar_bounds
-- name    : BianchiIX.exitSingleError_scalar_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:50:50.929019+00:00
-- url     : https://prove2.me/theorems/26d7c902-b2a7-4af8-9748-a91f3b4b5b9e
-- title:
--   Single exit perturbations satisfy value and radial coefficient bounds
-- statement:
--   Let $0<\alpha\leq1$, $0\leq R\leq5$, $H\geq\alpha^2$,
--   $|T|\leq\alpha^2/1000$, $|R^2-4+T|\leq22\alpha$,
--   $|L|\leq20\alpha$, and $|T|\leq K$. Then
--   $$|T(1+(R^2-4+T)/H)|\leq23K/\alpha,$$
--   $$|T(1+(R^2-4+T)/H)|\leq23\alpha/1000,$$
--   $$|T(2R/H-(R^2-4+T)L/H^2)|\leq450K/\alpha^2,$$
--   $$|1+(R^2-4+2T)/H|\leq24/\alpha.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/ExitSinglePhaseBounds.lean#L69-L126

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.exitSingleError_scalar_bounds {α R H T L K : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hR : 0 ≤ R ∧ R ≤ 5) (hH : α ^ 2 ≤ H) (hT : |T| ≤ α ^ 2 / 1000)
    (hN : |R ^ 2 - 4 + T| ≤ 22 * α) (hL : |L| ≤ 20 * α)
    (hK : |T| ≤ K) :
    |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ 23 * K / α ∧
      |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ 23 * α / 1000 ∧
      |T * (2 * R / H - (R ^ 2 - 4 + T) * L / H ^ 2)| ≤ 450 * K / α ^ 2 ∧
      |1 + (R ^ 2 - 4 + 2 * T) / H| ≤ 24 / α := by sorry
