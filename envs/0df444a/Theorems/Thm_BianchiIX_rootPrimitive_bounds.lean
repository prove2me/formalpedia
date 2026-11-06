-- Prove2me | Theorems.Thm_BianchiIX_rootPrimitive_bounds
-- name    : BianchiIX.rootPrimitive_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:39:29.495483+00:00
-- url     : https://prove2.me/theorems/d0a455c2-d1cc-44b4-be68-c453316989cc
-- title:
--   Bounds for the root primitive on the nonnegative half-line
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   For $t\geq0$, $0\leq P(t)\leq1/2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L66-L72

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

theorem BianchiIX.rootPrimitive_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ rootPrimitive t ∧ rootPrimitive t ≤ 1 / 2 := by sorry
