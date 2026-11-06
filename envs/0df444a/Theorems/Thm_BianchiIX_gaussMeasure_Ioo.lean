-- Prove2me | Theorems.Thm_BianchiIX_gaussMeasure_Ioo
-- name    : BianchiIX.gaussMeasure_Ioo
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:21:37.375847+00:00
-- url     : https://prove2.me/theorems/548254a1-a8c6-43af-a3e9-a11343e03fa3
-- title:
--   Gauss measure of a subinterval
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--   For $0\leq a\leq b\leq1$,
--   $$\mu_G((a,b))=\frac{\log(1+b)-\log(1+a)}{\log2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussMeasure.lean#L64-L69

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity

open Set MeasureTheory
open scoped ENNReal
open BianchiIX
noncomputable section

theorem BianchiIX.gaussMeasure_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    gaussMeasure (Ioo a b) = ENNReal.ofReal ((Real.log (1 + b) - Real.log (1 + a)) / Real.log 2) := by sorry
