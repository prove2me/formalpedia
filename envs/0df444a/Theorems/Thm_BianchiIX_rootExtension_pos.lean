-- Prove2me | Theorems.Thm_BianchiIX_rootExtension_pos
-- name    : BianchiIX.rootExtension_pos
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:46:53.457412+00:00
-- url     : https://prove2.me/theorems/f5b46e7a-f1a3-487e-b6b4-671824a6b7dc
-- title:
--   Positivity of an outward root extension
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   If $s>0$, $|e|=1$, $ex\geq0$,
--   $|d|\leq\theta/2$, and $\theta\leq1$, then $\mathcal R_{s,d,e}(x)>0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L122-L126

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

theorem BianchiIX.rootExtension_pos {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) (hθ : θ ≤ 1) : 0 < rootExtension s d e x := by sorry
