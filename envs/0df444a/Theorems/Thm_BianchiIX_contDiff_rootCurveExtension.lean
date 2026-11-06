-- Prove2me | Theorems.Thm_BianchiIX_contDiff_rootCurveExtension
-- name    : BianchiIX.contDiff_rootCurveExtension
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:44:04.83561+00:00
-- url     : https://prove2.me/theorems/478c3704-145d-4c69-87ca-07561fa24b11
-- title:
--   Continuous differentiability of the joined root curve
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
--
--   Assume $l<r$, $f(l)>0$, $f(r)>0$, and that $f$ has derivative $d_f(x)$
--   within $[l,r]$ at every $x\in[l,r]$.
--   If also $d_f$ is continuous on $[l,r]$,
--   then $F$ is of class $C^1$ on $\mathbb R$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootCurveExtension.lean#L132-L139

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

theorem BianchiIX.contDiff_rootCurveExtension {l r : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hfl : 0 < f l) (hfr : 0 < f r)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x)
    (hdf : ContinuousOn df (Icc l r)) : ContDiff ℝ 1 (rootCurveExtension l r f df) := by sorry
