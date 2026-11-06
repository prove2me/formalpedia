-- Prove2me | Theorems.Thm_BianchiIX_rootExtension_pair_bound
-- name    : BianchiIX.rootExtension_pair_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:48:21.557946+00:00
-- url     : https://prove2.me/theorems/2842d453-0f87-48fb-993e-5f5edf804eb6
-- title:
--   A joint bound for two outward root extensions
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   Suppose $s,t>0$, $|e|=1$, $ex\geq0$,
--   $|d|,|c|\leq\theta/2$, $\theta\leq1$, and $s^2+t^2\leq B$. Then
--   $$\mathcal R_{s,d,e}(x)^2+\mathcal R_{t,c,e}(x)^2
--   \leq(1+\theta/4)^2B.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L157-L168

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

theorem BianchiIX.rootExtension_pair_bound {s t d c e x θ B : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : |e| = 1) (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) (hc : |c| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : s ^ 2 + t ^ 2 ≤ B) :
    rootExtension s d e x ^ 2 + rootExtension t c e x ^ 2 ≤ (1 + θ / 4) ^ 2 * B := by sorry
