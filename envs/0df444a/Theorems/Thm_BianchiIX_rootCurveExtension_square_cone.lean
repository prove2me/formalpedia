-- Prove2me | Theorems.Thm_BianchiIX_rootCurveExtension_square_cone
-- name    : BianchiIX.rootCurveExtension_square_cone
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:49:45.361897+00:00
-- url     : https://prove2.me/theorems/b01667a0-f9b6-48a1-a1ae-51d5b647e2d1
-- title:
--   A global square-root cone bound for a squared root curve
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
--   Assume also $f>0$ on $[l,r]$,
--   $|d_f|\leq\theta/2$ there, and $\theta\leq1$. Then
--   $$|(F^2)'(x)|\leq\theta\sqrt{F(x)^2}\quad(x\in\mathbb R).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootCurveExtension.lean#L173-L180

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

theorem BianchiIX.rootCurveExtension_square_cone {l r θ : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hθ : θ ≤ 1)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x) (x : ℝ) :
    |deriv (fun z => rootCurveExtension l r f df z ^ 2) x| ≤
      θ * Real.sqrt (rootCurveExtension l r f df x ^ 2) := by sorry
