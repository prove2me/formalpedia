-- Prove2me | Theorems.Thm_BianchiIX_entrance_terminal_wall_forms
-- name    : BianchiIX.entrance_terminal_wall_forms
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:24.426476+00:00
-- url     : https://prove2.me/theorems/5f5970c5-1bde-44ae-93d6-eed5c30796ba
-- title:
--   Terminal products control all three entrance logarithmic columns
-- statement:
--   Let $A\geq0$, $k\geq1$, $0<u,v,w\leq1$,
--   $U,W,\theta\geq0$, and $0\leq\omega\leq1$. Put
--   $b=U+W$, $J=uv+v^2w(\theta+\omega)$, $K=u+vw^2$. Suppose
--   $$b^2\leq2(uv+v^2w^2\omega),\quad bU\leq2uv,\quad
--   bW\leq w(uv+v^2w\omega),\quad b\leq2v.$$
--   Then
--   $$b^2/k^2\leq4,$$
--   $$\frac b k\bigl(U(1/u+A)+WA/k^2\bigr)\leq(2+4A)v/k,$$
--   $$\frac b k\bigl(UA+W(1/w+A/k^2)\bigr)\leq(2+4A)J/k,$$
--   $$\frac b k\bigl(UAk/v+WA/v\bigr)\leq(2+4A)K.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/EntranceWallTerminalCorrection.lean#L19-L87

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
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.entrance_terminal_wall_forms {A k u v w U W θ ω : ℝ}
    (hA : 0 ≤ A) (hk : 1 ≤ k) (hu : 0 < u ∧ u ≤ 1) (hv : 0 < v ∧ v ≤ 1)
    (hw : 0 < w ∧ w ≤ 1) (hU : 0 ≤ U) (hW : 0 ≤ W) (hθ : 0 ≤ θ) (hω : 0 ≤ ω ∧ ω ≤ 1)
    (hsq : (U + W) ^ 2 ≤ 2 * (u * v + v ^ 2 * w ^ 2 * ω))
    (hfast : (U + W) * U ≤ 2 * u * v)
    (hslow : (U + W) * W ≤ w * (u * v + v ^ 2 * w * ω))
    (hsum : U + W ≤ 2 * v) :
    let b := U + W
    let J := u * v + v ^ 2 * w * (θ + ω)
    let K := u + v * w ^ 2
    b ^ 2 / k ^ 2 ≤ 4 ∧
    b / k * (U * (1 / u + A) + W * (A / k ^ 2)) ≤ (2 + 4 * A) * (v / k) ∧
    b / k * (U * A + W * (1 / w + A / k ^ 2)) ≤ (2 + 4 * A) * (J / k) ∧
    b / k * (U * (A * k / v) + W * (A / v)) ≤ (2 + 4 * A) * K := by sorry
