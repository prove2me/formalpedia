-- Prove2me | Theorems.Thm_BianchiIX_jointly_measurable_rootCurve_of_interior
-- name    : BianchiIX.jointly_measurable_rootCurve_of_interior
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:45:28.017806+00:00
-- url     : https://prove2.me/theorems/79e3d111-07a9-4510-ab2d-ca98606bdea5
-- title:
--   Joint measurability of root curves and their derivative data
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
--   Let $X$ be a measurable space. Let $l,r:X\to\mathbb R$ be measurable,
--   with $l(q)<r(q)$ for every $q$. For functions $f_q,d_q:\mathbb R\to\mathbb R$,
--   assume that $f_q$ has derivative $d_q(x)$ within $[l(q),r(q)]$ at every
--   point of that interval, and that
--   $$(q,x)\longmapsto
--   \begin{cases}f_q(x),&l(q)<x<r(q),\\0,&\text{otherwise}\end{cases}$$
--   is measurable on $X\times\mathbb R$. Let $F_q,V_q$ be their root-curve
--   extensions with these endpoints.
--   Both maps $(q,x)\mapsto F_q(x)$ and
--   $(q,x)\mapsto V_q(x)$ are measurable on $X\times\mathbb R$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CurveMeasurability.lean#L179-L191

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
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

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

theorem BianchiIX.jointly_measurable_rootCurve_of_interior {X : Type*} [MeasurableSpace X]
    {l r : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun p : X × ℝ => rootCurveExtension (l p.1) (r p.1) (f p.1) (df p.1) p.2) ∧
      Measurable (fun p : X × ℝ => rootCurveDerivative (l p.1) (r p.1) (f p.1) (df p.1) p.2) := by sorry
