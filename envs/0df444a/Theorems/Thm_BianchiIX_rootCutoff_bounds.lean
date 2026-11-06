-- Prove2me | Theorems.Thm_BianchiIX_rootCutoff_bounds
-- name    : BianchiIX.rootCutoff_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:28:45.031049+00:00
-- url     : https://prove2.me/theorems/8c74cb6d-4b3f-44da-94a2-df1b53fa0793
-- title:
--   Bounds for the root cutoff
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   For $t\geq0$, $0\leq\chi(t)\leq1$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L74-L75

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

theorem BianchiIX.rootCutoff_bounds {t : ℝ} (ht : 0 ≤ t) : 0 ≤ rootCutoff t ∧ rootCutoff t ≤ 1 := by sorry
