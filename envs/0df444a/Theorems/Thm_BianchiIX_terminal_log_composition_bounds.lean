-- Prove2me | Theorems.Thm_BianchiIX_terminal_log_composition_bounds
-- name    : BianchiIX.terminal_log_composition_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:14.002414+00:00
-- url     : https://prove2.me/theorems/e4d3bfe1-e417-4281-832f-1d56b1e895e8
-- title:
--   Terminal logarithmic rows retain their distinct radial scales under composition
-- statement:
--   Let $M:\mathbb R^4\to\mathbb R^2$ be linear, with matrix
--   $M_{ij}=(Me_j)_i$, and let $d\in\mathbb R^4$. Suppose $A,B\geq1$,
--   $0<\alpha\leq1$, $1/\alpha\leq k\leq3/\alpha$, $0<u,w\leq1$,
--   $v>0$, and $L,s,t\geq0$, with $wt\leq B/\alpha^2$. Assume
--   $$|d_0|\leq B/\alpha^2,\quad |d_1|\leq uB/\alpha,\quad
--   |d_2|\leq v(B/\alpha+s),\quad |d_3|\leq w(B/\alpha+t),$$
--   $$|M_{00}|\leq AL,\quad |M_{01}-1/u|\leq A,\quad
--   |M_{02}|\leq Ak/v,\quad |M_{03}|\leq A,$$
--   $$|M_{10}|\leq AL/k^2,\quad |M_{11}|\leq A/k^2,\quad
--   |M_{12}|\leq A/v,\quad |M_{13}-1/w|\leq A/k^2.$$
--   Then
--   $$|(Md)_0|\leq8AB((1+L)/\alpha^2+s/\alpha),\qquad
--   |(Md)_1|\leq8AB(L+1/\alpha+s+t).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/TerminalLogComposition.lean#L7-L125

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.terminal_log_composition_bounds
    (M : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (d : Fin 4 → ℝ)
    {A B α k u v w L s t : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hα : 0 < α ∧ α ≤ 1) (hk : 1 / α ≤ k ∧ k ≤ 3 / α)
    (hu : 0 < u ∧ u ≤ 1) (hv : 0 < v) (hw : 0 < w ∧ w ≤ 1)
    (hL : 0 ≤ L) (hs : 0 ≤ s) (ht : 0 ≤ t) (hwt : w * t ≤ B / α ^ 2)
    (hd0 : |d 0| ≤ B / α ^ 2) (hd1 : |d 1| ≤ u * (B / α))
    (hd2 : |d 2| ≤ v * (B / α + s)) (hd3 : |d 3| ≤ w * (B / α + t))
    (hUr : |M (Pi.single 0 1) 0| ≤ A * L)
    (hUu : |M (Pi.single 1 1) 0 - 1 / u| ≤ A)
    (hUv : |M (Pi.single 2 1) 0| ≤ A * k / v)
    (hUw : |M (Pi.single 3 1) 0| ≤ A)
    (hWr : |M (Pi.single 0 1) 1| ≤ A * L / k ^ 2)
    (hWu : |M (Pi.single 1 1) 1| ≤ A / k ^ 2)
    (hWv : |M (Pi.single 2 1) 1| ≤ A / v)
    (hWw : |M (Pi.single 3 1) 1 - 1 / w| ≤ A / k ^ 2) :
    |M d 0| ≤ 8 * A * B * ((1 + L) / α ^ 2 + s / α) ∧
      |M d 1| ≤ 8 * A * B * (L + 1 / α + s + t) := by sorry
