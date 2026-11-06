-- Prove2me | Theorems.Thm_BianchiIX_curveSampleStep_samples
-- name    : BianchiIX.curveSampleStep_samples
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:31:02.391576+00:00
-- url     : https://prove2.me/theorems/72fb258c-d7a1-4fb7-960b-0895347f0c5f
-- title:
--   Two nontrivial interior samples from every closed-interval point
-- statement:
--   For real $l,r,x$ and $n\in\mathbb N$, define
--   $$h_n(l,r,x)=
--   \frac{\begin{cases}r-x,&x<r,\\l-x,&x\geq r\end{cases}}{3(n+1)}.$$
--   If $l<r$ and $x\in[l,r]$, then for every $n$,
--   $$h_n(l,r,x)\ne0,\qquad x+h_n(l,r,x),\ x+2h_n(l,r,x)\in(l,r).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CurveMeasurability.lean#L44-L67

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

theorem BianchiIX.curveSampleStep_samples {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r) (n : ℕ) :
    curveSampleStep l r x n ≠ 0 ∧
      x + curveSampleStep l r x n ∈ Ioo l r ∧
      x + 2 * curveSampleStep l r x n ∈ Ioo l r := by sorry
