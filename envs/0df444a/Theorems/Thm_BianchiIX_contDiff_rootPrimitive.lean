-- Prove2me | Theorems.Thm_BianchiIX_contDiff_rootPrimitive
-- name    : BianchiIX.contDiff_rootPrimitive
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:38:25.159474+00:00
-- url     : https://prove2.me/theorems/578c7e6b-83e3-4742-a2d9-988821a20c9f
-- title:
--   Continuous differentiability of the root primitive
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   The function $P$ is of class $C^1$ on $\mathbb R$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L31-L34

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

theorem BianchiIX.contDiff_rootPrimitive : ContDiff ℝ 1 rootPrimitive := by sorry
