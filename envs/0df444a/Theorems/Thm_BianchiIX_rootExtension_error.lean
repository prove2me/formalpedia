-- Prove2me | Theorems.Thm_BianchiIX_rootExtension_error
-- name    : BianchiIX.rootExtension_error
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:42:31.220356+00:00
-- url     : https://prove2.me/theorems/16e811f4-988c-45ae-b14c-5f1f5889e94a
-- title:
--   The relative error of an outward root extension
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   Suppose $s>0$, $|e|=1$, $ex\geq0$, and
--   $|d|\leq\theta/2$. Then
--   $$|\mathcal R_{s,d,e}(x)-s|\leq\theta s/4.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L104-L113

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

theorem BianchiIX.rootExtension_error {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) :
    |rootExtension s d e x - s| ≤ θ * s / 4 := by sorry
