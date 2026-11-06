-- Prove2me | Theorems.Thm_BianchiIX_rootCurveExtension_right
-- name    : BianchiIX.rootCurveExtension_right
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:36:53.771453+00:00
-- url     : https://prove2.me/theorems/df1b696e-6eff-4e26-836d-828f8746fb88
-- title:
--   The right root-extension formula including the endpoint
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--
--   For real functions $f,d_f$ and real endpoints $l,r$, define $F$ and $V$ by
--   $$F(x)=\begin{cases}
--   \mathcal R_{f(l),d_f(l),-1}(x-l),&x<l,\\
--   \mathcal R_{f(r),d_f(r),1}(x-r),&x\geq l,\ r<x,\\
--   f(x),&\text{otherwise},
--   \end{cases}$$
--   $$V(x)=\begin{cases}
--   d_f(l)\chi(-(x-l)/f(l)),&x<l,\\
--   d_f(r)\chi((x-r)/f(r)),&x\geq l,\ r<x,\\
--   d_f(x),&\text{otherwise}.
--   \end{cases}$$
--   Write $F_f,V_f$ when comparing several pairs of input functions.
--   If $l\leq r$ and $r\leq x$, then
--   $$F(x)=\mathcal R_{f(r),d_f(r),1}(x-r),\qquad
--   V(x)=d_f(r)\chi((x-r)/f(r)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootCurveExtension.lean#L31-L36

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
open BianchiIX
noncomputable section

theorem BianchiIX.rootCurveExtension_right {l r x : ℝ} (f df : ℝ → ℝ) (hlr : l ≤ r) (hx : r ≤ x) :
    rootCurveExtension l r f df x = rootExtension (f r) (df r) 1 (x - r) ∧
      rootCurveDerivative l r f df x = df r * rootCutoff ((x - r) / f r) := by sorry
