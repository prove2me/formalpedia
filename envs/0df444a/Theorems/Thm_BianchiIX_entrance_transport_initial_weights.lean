-- Prove2me | Theorems.Thm_BianchiIX_entrance_transport_initial_weights
-- name    : BianchiIX.entrance_transport_initial_weights
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:59:27.047199+00:00
-- url     : https://prove2.me/theorems/32bba5f9-0954-447a-a827-c4b6180b6194
-- title:
--   Initial logarithmic rates preserve the weighted entrance amplitude budget
-- statement:
--   Let $u,v,\theta\geq0$, $0\leq w\leq1$, $k\geq1$,
--   $|\beta_U|\leq12k$, and $|\beta_W|\leq9$. Then
--   $$|u\beta_U|+|w\beta_W|\leq12ku+9w,$$
--   $$\frac{v|u\beta_U|+(uv+\theta v^2w)|w\beta_W|}{k}
--   \leq21\bigl(uv+\theta(vw)^2\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/EntranceTransportWeights.lean#L32-L63

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

theorem BianchiIX.entrance_transport_initial_weights {u v w θ k βU βW : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w ∧ w ≤ 1) (hθ : 0 ≤ θ)
    (hk : 1 ≤ k) (hU : |βU| ≤ 12 * k) (hW : |βW| ≤ 9) :
    |u * βU| + |w * βW| ≤ 12 * k * u + 9 * w ∧
      (v * |u * βU| + (u * v + θ * v ^ 2 * w) * |w * βW|) / k ≤
        21 * (u * v + θ * (v * w) ^ 2) := by sorry
