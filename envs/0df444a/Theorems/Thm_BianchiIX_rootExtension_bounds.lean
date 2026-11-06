-- Prove2me | Theorems.Thm_BianchiIX_rootExtension_bounds
-- name    : BianchiIX.rootExtension_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:44:52.440109+00:00
-- url     : https://prove2.me/theorems/952c7ea1-0910-4071-9c2e-00a8a6e78820
-- title:
--   Two-sided bounds for an outward root extension
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--   Under $s>0$, $|e|=1$, $ex\geq0$, and
--   $|d|\leq\theta/2$,
--   $$(1-\theta/4)s\leq\mathcal R_{s,d,e}(x)\leq(1+\theta/4)s.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean#L115-L120

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

theorem BianchiIX.rootExtension_bounds {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) :
    (1 - θ / 4) * s ≤ rootExtension s d e x ∧
      rootExtension s d e x ≤ (1 + θ / 4) * s := by sorry
