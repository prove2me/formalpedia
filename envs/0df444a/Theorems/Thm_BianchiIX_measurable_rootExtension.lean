-- Prove2me | Theorems.Thm_BianchiIX_measurable_rootExtension
-- name    : BianchiIX.measurable_rootExtension
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:40:55.896697+00:00
-- url     : https://prove2.me/theorems/4c8544be-f075-441d-94d6-472f00995901
-- title:
--   Measurability of a parametrized root extension
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   If $s,d,e,x:X\to\mathbb R$ are measurable
--   on a measurable space $X$, then
--   $q\mapsto\mathcal R_{s(q),d(q),e(q)}(x(q))$ is measurable.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L170-L173

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

theorem BianchiIX.measurable_rootExtension {X : Type*} [MeasurableSpace X] {s d e x : X → ℝ}
    (hs : Measurable s) (hd : Measurable d) (he : Measurable e) (hx : Measurable x) :
    Measurable (fun q => rootExtension (s q) (d q) (e q) (x q)) := by sorry
