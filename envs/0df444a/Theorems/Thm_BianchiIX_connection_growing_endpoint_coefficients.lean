-- Prove2me | Theorems.Thm_BianchiIX_connection_growing_endpoint_coefficients
-- name    : BianchiIX.connection_growing_endpoint_coefficients
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:58:59.299429+00:00
-- url     : https://prove2.me/theorems/0e0cab57-6f04-4178-95aa-e12576b3bcab
-- title:
--   Growing endpoint coefficients satisfy explicit reciprocal wall bounds
-- statement:
--   Suppose $\mu\geq4$, $0\leq u\leq1/(10000\mu)$,
--   $0<w\leq1/10000$, and $wL\leq1$. Then
--   $$32+12800u+\frac{96}{\mu w}+\frac{1024000L(u+w)}\mu\leq\frac{16\mu}w,$$
--   $$\frac{12800u+64/(\mu w)+1024000L(u+w)/\mu}{\mu^2}
--   \leq\frac{200}{\mu^3w}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionReturnBounds.lean#L14-L46

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.connection_growing_endpoint_coefficients {μ u w L : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000)
    (hL : w * L ≤ 1) :
    32 + 12800 * u + 96 / (μ * w) + 1024000 * L * (u + w) / μ ≤ 16 * μ / w ∧
    (12800 * u + 64 / (μ * w) + 1024000 * L * (u + w) / μ) / μ ^ 2 ≤
      200 / (μ ^ 3 * w) := by sorry
