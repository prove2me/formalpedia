-- Prove2me | Theorems.Thm_BianchiIX_rootCurveExtension_pos
-- name    : BianchiIX.rootCurveExtension_pos
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:48:25.20394+00:00
-- url     : https://prove2.me/theorems/c176ed94-4310-4ed9-85a2-65a8f8fe44b3
-- title:
--   Positivity of the joined root curve
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
--   Suppose $l\leq r$, $f>0$ on $[l,r]$,
--   $|d_f|\leq\theta/2$ there, and $\theta\leq1$. Then $F(x)>0$ for every $x$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootCurveExtension.lean#L141-L154

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

theorem BianchiIX.rootCurveExtension_pos {l r θ : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2)
    (hθ : θ ≤ 1) (x : ℝ) : 0 < rootCurveExtension l r f df x := by sorry
