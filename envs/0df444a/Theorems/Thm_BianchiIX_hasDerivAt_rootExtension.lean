-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_rootExtension
-- name    : BianchiIX.hasDerivAt_rootExtension
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:39:09.259287+00:00
-- url     : https://prove2.me/theorems/9b1018a3-42cf-4934-ba00-9da7e334bbf3
-- title:
--   The derivative of a root extension
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   If $s>0$ and $|e|=1$, then
--   $$\mathcal R_{s,d,e}'(x)=d\chi(ex/s)$$
--   for every real $d,x$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L83-L91

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

theorem BianchiIX.hasDerivAt_rootExtension {s e : ℝ} (hs : 0 < s) (he : |e| = 1) (d x : ℝ) :
    HasDerivAt (rootExtension s d e) (d * rootCutoff (e * x / s)) x := by sorry
