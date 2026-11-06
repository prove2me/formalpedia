-- Prove2me | Theorems.Thm_BianchiIX_rootPrimitive_after_one
-- name    : BianchiIX.rootPrimitive_after_one
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:35:59.723265+00:00
-- url     : https://prove2.me/theorems/28a05a4a-9b30-47a5-8d24-1314bee8b167
-- title:
--   The constant tail of the root primitive
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   For $t\geq1$, $P(t)=1/2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L50-L64

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

theorem BianchiIX.rootPrimitive_after_one {t : ℝ} (ht : 1 ≤ t) : rootPrimitive t = 1 / 2 := by sorry
