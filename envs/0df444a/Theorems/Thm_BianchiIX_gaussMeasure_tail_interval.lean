-- Prove2me | Theorems.Thm_BianchiIX_gaussMeasure_tail_interval
-- name    : BianchiIX.gaussMeasure_tail_interval
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:25:34.579262+00:00
-- url     : https://prove2.me/theorems/cbfd58db-a618-4296-828c-0884ba05041a
-- title:
--   Gauss measure of a digit tail interval
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--   For every positive integer $k$,
--   $$\mu_G((0,1/k))=\frac{\log(1+1/k)}{\log2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussMeasure.lean#L133-L138

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

theorem BianchiIX.gaussMeasure_tail_interval (k : ℕ+) :
    gaussMeasure (Ioo 0 (1 / (k : ℝ))) = ENNReal.ofReal (Real.log (1 + 1 / (k : ℝ)) / Real.log 2) := by sorry
