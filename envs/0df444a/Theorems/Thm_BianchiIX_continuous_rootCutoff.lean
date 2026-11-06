-- Prove2me | Theorems.Thm_BianchiIX_continuous_rootCutoff
-- name    : BianchiIX.continuous_rootCutoff
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:28:44.792204+00:00
-- url     : https://prove2.me/theorems/657ddf5f-0b04-4af8-8512-fe327bf20289
-- title:
--   Continuity of the root cutoff
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   The function $\chi$ is continuous on $\mathbb R$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L23-L24

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

theorem BianchiIX.continuous_rootCutoff : Continuous rootCutoff := by sorry
