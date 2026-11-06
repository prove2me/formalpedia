-- Prove2me | Theorems.Thm_BianchiIX_rootCurveExtension_pair_bound
-- name    : BianchiIX.rootCurveExtension_pair_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:50:25.833149+00:00
-- url     : https://prove2.me/theorems/a1491d99-91ee-43ff-b3f9-d4d674d59b66
-- title:
--   A uniform joint bound for two extended root curves
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
--   For a second pair $g,d_g$, form $F_g,V_g$ by the same construction.
--   Assume $l\leq r$, $f,g>0$ on $[l,r]$, and
--   $|d_f(x)|,|d_g(x)|\leq\theta/2$ there, with $\theta\leq1$.
--   If $f(x)^2+g(x)^2\leq B$ on $[l,r]$, then
--   $$F_f(x)^2+F_g(x)^2\leq\tfrac{25}{16}B
--   \quad(x\in\mathbb R).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootCurveExtension.lean#L203-L213

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

theorem BianchiIX.rootCurveExtension_pair_bound {l r θ B : ℝ} (hlr : l ≤ r) {f g df dg : ℝ → ℝ}
    (hf : ∀ x ∈ Icc l r, 0 < f x) (hg : ∀ x ∈ Icc l r, 0 < g x)
    (hdf : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hdg : ∀ x ∈ Icc l r, |dg x| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, f x ^ 2 + g x ^ 2 ≤ B) (x : ℝ) :
    rootCurveExtension l r f df x ^ 2 + rootCurveExtension l r g dg x ^ 2 ≤ (25 / 16) * B := by sorry
