-- Prove2me | Theorems.Thm_BianchiIX_jointly_measurable_amplitudeCurve
-- name    : BianchiIX.jointly_measurable_amplitudeCurve
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:47:47.078203+00:00
-- url     : https://prove2.me/theorems/e92db6d7-f591-4b66-b346-9e24a7508dc7
-- title:
--   Joint measurability of extended amplitudes and their derivatives
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
--   Let $X$ be a measurable space and
--   $l,r:X\to\mathbb R$ be measurable with $l(q)<r(q)$. Assume
--   $U_q>0$ on $[l(q),r(q)]$, with within-derivative $d_q$ there, and assume
--   the interior function $(q,x)\mapsto U_q(x)\mathbf1_{\{l(q)<x<r(q)\}}$
--   is measurable. Then both
--   $$(q,x)\mapsto\widetilde U_q(x),\qquad
--   (q,x)\mapsto\widetilde U_q'(x)$$
--   are measurable.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeExtension.lean#L134-L155

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

theorem BianchiIX.jointly_measurable_amplitudeCurve {X : Type*} [MeasurableSpace X]
    {l r : X → ℝ} {U dU : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hpos : ∀ q x, x ∈ Icc (l q) (r q) → 0 < U q x)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then U p.1 p.2 else 0))
    (hU : ∀ q x, x ∈ Icc (l q) (r q) →
      HasDerivWithinAt (U q) (dU q x) (Icc (l q) (r q)) x) :
    Measurable (fun p : X × ℝ => amplitudeCurveExtension (l p.1) (r p.1) (U p.1) (dU p.1) p.2) ∧
      Measurable (fun p : X × ℝ => deriv (amplitudeCurveExtension (l p.1) (r p.1) (U p.1) (dU p.1)) p.2) := by sorry
