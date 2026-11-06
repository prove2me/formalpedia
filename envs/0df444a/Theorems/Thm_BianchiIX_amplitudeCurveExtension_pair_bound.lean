-- Prove2me | Theorems.Thm_BianchiIX_amplitudeCurveExtension_pair_bound
-- name    : BianchiIX.amplitudeCurveExtension_pair_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:51:42.985037+00:00
-- url     : https://prove2.me/theorems/8be3f3b5-7c38-458b-977a-531896124351
-- title:
--   A uniform total-amplitude bound after extension
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
--   For real functions $U,d_U$, set
--   $$r_U(x)=\sqrt{U(x)},\qquad b_U(x)=\frac{d_U(x)}{2\sqrt{U(x)}}.$$
--   Let $F_U,V_U$ be the root-curve construction applied to $(r_U,b_U)$, and set
--   $$\widetilde U(x)=F_U(x)^2.$$
--   For another pair $W,d_W$, use the analogous notation.
--
--   Assume $l\leq r$, $U,W>0$ on $[l,r]$, and
--   $$|d_U(x)|\leq\theta\sqrt{U(x)},\qquad
--   |d_W(x)|\leq\theta\sqrt{W(x)}\quad(x\in[l,r]),\qquad \theta\leq1.$$
--   If $U(x)+W(x)\leq B$ on $[l,r]$, then
--   $$\widetilde U(x)+\widetilde W(x)\leq\tfrac{25}{16}B
--   \quad(x\in\mathbb R).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeExtension.lean#L107-L120

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.amplitudeCurveExtension_pair_bound {l r θ B : ℝ} (hlr : l ≤ r)
    {U W dU dW : ℝ → ℝ}
    (hU : ∀ x ∈ Icc l r, 0 < U x) (hW : ∀ x ∈ Icc l r, 0 < W x)
    (hdU : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x))
    (hdW : ∀ x ∈ Icc l r, |dW x| ≤ θ * Real.sqrt (W x))
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, U x + W x ≤ B) (x : ℝ) :
    amplitudeCurveExtension l r U dU x + amplitudeCurveExtension l r W dW x ≤
      (25 / 16) * B := by sorry
