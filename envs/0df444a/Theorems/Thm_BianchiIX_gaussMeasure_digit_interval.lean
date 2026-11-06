-- Prove2me | Theorems.Thm_BianchiIX_gaussMeasure_digit_interval
-- name    : BianchiIX.gaussMeasure_digit_interval
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:25:50.33551+00:00
-- url     : https://prove2.me/theorems/3b9b3eb6-1718-4c08-9345-b36f4110e662
-- title:
--   Gauss measure of an individual digit interval
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--   For every positive integer $k$,
--   $$\mu_G((1/(k+1),1/k))=\frac{\log((k+1)^2/(k(k+2)))}{\log2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussMeasure.lean#L140-L153

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

theorem BianchiIX.gaussMeasure_digit_interval (k : ℕ+) :
    gaussMeasure (Ioo (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))) =
      ENNReal.ofReal (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2) := by sorry
