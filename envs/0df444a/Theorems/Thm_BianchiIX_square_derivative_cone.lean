-- Prove2me | Theorems.Thm_BianchiIX_square_derivative_cone
-- name    : BianchiIX.square_derivative_cone
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:29:51.893192+00:00
-- url     : https://prove2.me/theorems/b1a7e145-1967-4755-a8eb-c1f93385866a
-- title:
--   A square-root cone bound for the square of a positive function
-- statement:
--   If $f'(x)=d$, $f(x)>0$, and $|d|\leq\theta/2$, then
--   $$|(f^2)'(x)|\leq\theta\sqrt{f(x)^2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L144-L155

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section

theorem BianchiIX.square_derivative_cone {f : ℝ → ℝ} {d x θ : ℝ} (hf : HasDerivAt f d x)
    (hpos : 0 < f x) (hd : |d| ≤ θ / 2) :
    |deriv (fun z => f z ^ 2) x| ≤ θ * Real.sqrt (f x ^ 2) := by sorry
