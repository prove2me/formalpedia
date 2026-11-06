-- Prove2me | Theorems.Thm_BianchiIX_entrance_terminal_wall_weights
-- name    : BianchiIX.entrance_terminal_wall_weights
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:51:01.157951+00:00
-- url     : https://prove2.me/theorems/6b3b9a35-cf8b-41b8-9b66-5ff7e4354bdf
-- title:
--   Terminal wall weights absorb the strong waiting time and retain weak decay
-- statement:
--   Let $k\geq1$, $L\geq0$, $u,v,w,a,c\in[0,1]$,
--   and $U,W\geq0$. Suppose $La\leq3/k$, $U\leq uva$, and $W\leq wvc$.
--   Writing $b=U+W$ and $R=v^2w^2c^2$, one has
--   $$b^2\leq2(uv+R),\qquad kLbU\leq6uv,\qquad
--   (L/k)bW\leq3uv+(L/k)R,$$
--   $$bU\leq2uv,\qquad bW\leq w(uv+v^2wc^2),\qquad b\leq2v.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/EntranceTerminalWeights.lean#L7-L57

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

theorem BianchiIX.entrance_terminal_wall_weights {k L u v w U W a c : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hu : 0 ≤ u ∧ u ≤ 1)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hU0 : 0 ≤ U) (hW0 : 0 ≤ W) (ha : 0 ≤ a ∧ a ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hLa : L * a ≤ 3 / k) (hU : U ≤ u * v * a) (hW : W ≤ w * v * c) :
    (U + W) ^ 2 ≤ 2 * (u * v + v ^ 2 * w ^ 2 * c ^ 2) ∧
    k * L * (U + W) * U ≤ 6 * u * v ∧
    (L / k) * (U + W) * W ≤ 3 * u * v + (L / k) * (v ^ 2 * w ^ 2 * c ^ 2) ∧
    (U + W) * U ≤ 2 * u * v ∧
    (U + W) * W ≤ w * (u * v + v ^ 2 * w * c ^ 2) ∧
    U + W ≤ 2 * v := by sorry
