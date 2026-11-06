-- Prove2me | Theorems.Thm_BianchiIX_rootCurveDerivative_bound
-- name    : BianchiIX.rootCurveDerivative_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:40:37.189637+00:00
-- url     : https://prove2.me/theorems/65a5da13-8a3f-4a92-9a77-b5e92d6f7fb9
-- title:
--   Preservation of the derivative bound under root-curve extension
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
--   Suppose $l\leq r$, $f>0$ on $[l,r]$, and
--   $|d_f|\leq\theta/2$ there. Then $|V(x)|\leq\theta/2$ for every $x$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootCurveExtension.lean#L156-L171

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

theorem BianchiIX.rootCurveDerivative_bound {l r θ : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2)
    (x : ℝ) : |rootCurveDerivative l r f df x| ≤ θ / 2 := by sorry
