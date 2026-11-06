-- Prove2me | Theorems.Thm_BianchiIX_rootExtension_derivative_bound
-- name    : BianchiIX.rootExtension_derivative_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:36:23.289531+00:00
-- url     : https://prove2.me/theorems/1feeaf3f-27d3-47f0-bff6-00ce844c6332
-- title:
--   A bound for the outward derivative formula
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   If $s>0$, $ex\geq0$, and $|d|\leq\theta/2$,
--   then $|d\chi(ex/s)|\leq\theta/2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L128-L132

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

theorem BianchiIX.rootExtension_derivative_bound {s d e x θ : ℝ} (hs : 0 < s)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) : |d * rootCutoff (e * x / s)| ≤ θ / 2 := by sorry
