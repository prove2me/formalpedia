-- Prove2me | Theorems.Thm_BianchiIX_measurable_curveSampleStep
-- name    : BianchiIX.measurable_curveSampleStep
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:31:54.103404+00:00
-- url     : https://prove2.me/theorems/3ef0a0b5-416c-4a04-8e91-9261a977ca81
-- title:
--   Measurability of a parametrized sampling step
-- statement:
--   For real $l,r,x$ and $n\in\mathbb N$, define
--   $$h_n(l,r,x)=
--   \frac{\begin{cases}r-x,&x<r,\\l-x,&x\geq r\end{cases}}{3(n+1)}.$$
--   If $l,r,x:X\to\mathbb R$ are measurable,
--   then $q\mapsto h_n(l(q),r(q),x(q))$ is measurable for each $n$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CurveMeasurability.lean#L76-L79

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

theorem BianchiIX.measurable_curveSampleStep {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} (hl : Measurable l) (hr : Measurable r) (hx : Measurable x) (n : ℕ) :
    Measurable (fun q => curveSampleStep (l q) (r q) (x q) n) := by sorry
