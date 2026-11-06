-- Prove2me | Theorems.Thm_BianchiIX_amplitudeCurveExtension_deriv_middle
-- name    : BianchiIX.amplitudeCurveExtension_deriv_middle
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:46:27.772298+00:00
-- url     : https://prove2.me/theorems/5da18462-7f0e-4e44-9d80-d2f2083d8d8d
-- title:
--   Preservation of the amplitude derivative on its interval
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
--   Assume $l<r$, $U>0$ on $[l,r]$, and that $U$ has derivative $d_U(x)$
--   within $[l,r]$ at every $x\in[l,r]$.
--   For $x\in[l,r]$,
--   $\widetilde U'(x)=d_U(x)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeExtension.lean#L55-L62

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

theorem BianchiIX.amplitudeCurveExtension_deriv_middle {l r x : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ y ∈ Icc l r, 0 < U y)
    (hU : ∀ y ∈ Icc l r, HasDerivWithinAt U (dU y) (Icc l r) y) (hx : x ∈ Icc l r) :
    deriv (amplitudeCurveExtension l r U dU) x = dU x := by sorry
