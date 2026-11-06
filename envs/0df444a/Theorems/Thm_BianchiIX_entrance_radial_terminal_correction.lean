-- Prove2me | Theorems.Thm_BianchiIX_entrance_radial_terminal_correction
-- name    : BianchiIX.entrance_radial_terminal_correction
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:58:55.188967+00:00
-- url     : https://prove2.me/theorems/5c4732c8-8c39-4043-a93b-ea73eef04222
-- title:
--   The entrance radial endpoint correction obeys a weighted terminal budget
-- statement:
--   Let $A,T,L,S,U,W\geq0$ and $k>0$, and put $b=U+W$.
--   Assume
--   $$b^2\leq2(P+S),\quad kLbU\leq6P,\quad (L/k)bW\leq3P+(L/k)S,$$
--   $$X\leq1+2A,\quad X_U\leq AL,\quad X_W\leq AL/k^2,$$
--   $$E\leq T\bigl(b^2X/k^2+(b/k)(UX_U+WX_W)\bigr).$$
--   Then
--   $$E\leq\frac{T(2+13A)}{k^2}\bigl(P+(1+L/k)S\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/EntranceRadialTerminalCorrection.lean#L7-L41

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

theorem BianchiIX.entrance_radial_terminal_correction {A T k L P S U W X XU XW E : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hk : 0 < k) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hsq : (U + W) ^ 2 ≤ 2 * (P + S))
    (hfast : k * L * (U + W) * U ≤ 6 * P)
    (hslow : (L / k) * (U + W) * W ≤ 3 * P + (L / k) * S)
    (hX : X ≤ 1 + 2 * A) (hXU : XU ≤ A * L) (hXW : XW ≤ A * L / k ^ 2)
    (hE : E ≤ T * ((U + W) ^ 2 / k ^ 2 * X + (U + W) / k * (U * XU + W * XW))) :
    E ≤ T * (2 + 13 * A) * (P + (1 + L / k) * S) / k ^ 2 := by sorry
